theory IsaSAT_Restart_Inprocessing
  imports IsaSAT_Restart
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
begin
thm simplify_clause_with_unit_def

definition simplify_clause_with_unit2_pre where
  \<open>simplify_clause_with_unit2_pre C M N \<longleftrightarrow>
     C \<in># dom_m N \<and> no_dup M\<close>

definition simplify_clause_with_unit2 where
  \<open>simplify_clause_with_unit2 C M N\<^sub>0 = do {
      ASSERT(C \<in># dom_m N\<^sub>0);
        let l = length (N\<^sub>0 \<propto> C);
        (i, j, N, del, is_true) \<leftarrow> WHILE\<^sub>T\<^bsup>(\<lambda>(i, j, N, del, b). C \<in># dom_m N)\<^esup>
        (\<lambda>(i, j, N, del, b). \<not>b \<and> j < l)
        (\<lambda>(i, j, N, del, is_true). do {
           ASSERT(i < length (N \<propto> C) \<and> j < length (N \<propto> C) \<and> C \<in># dom_m N);
           let L = N \<propto> C ! j;
           ASSERT(L \<in> set (N\<^sub>0 \<propto> C));
           let val = polarity M L;
           if val = Some True then RETURN (i, j+1, N, add_mset L del, True)
           else if val = Some False
           then RETURN (i, j+1, N, add_mset L del, False)
           else RETURN (i+1, j+1, N(C \<hookrightarrow> ((N \<propto> C)[i := L])), del, False)
        })
         (0, 0, N\<^sub>0, {#}, False);
    ASSERT(C \<in># dom_m N \<and> i \<le> length (N \<propto> C));
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (fmdrop C N, L, is_true, i)
    else do {
      RETURN (N(C \<hookrightarrow> (take i (N \<propto> C))), L, is_true, i)
    }
  }\<close>


lemma RES_RETURN_RES3':
  \<open>RES \<Phi> \<bind> (\<lambda>(T, T', T''). RETURN (f T T' T'')) = RES ((\<lambda>(a, b, c). f a b c) ` \<Phi>)\<close>
  apply (subst RES_SPEC_conv)
  apply (subst RES_RETURN_RES3)
  by auto

lemma RETURN_le_RES_no_return3:
  \<open>f \<le> SPEC (\<lambda>(S,T,U). g S T U \<in> \<Phi>) \<Longrightarrow> do {(S, T, U) \<leftarrow> f; RETURN (g S T U)} \<le> RES \<Phi>\<close>
  by (cases f)
   (auto simp: RES_RETURN_RES3')

lemma RES_RETURN_RES4':
  \<open>RES \<Phi> \<bind> (\<lambda>(T, T', T'', T'''). RETURN (f T T' T'' T''')) = RES ((\<lambda>(a, b, c, d). f a b c d) ` \<Phi>)\<close>
  apply (subst RES_SPEC_conv)
  apply (subst RES_RETURN_RES4)
  by auto

lemma RETURN_le_RES_no_return4:
  \<open>f \<le> SPEC (\<lambda>(S,T,U,V). g S T U V \<in> \<Phi>) \<Longrightarrow> do {(S, T, U, V) \<leftarrow> f; RETURN (g S T U V)} \<le> RES \<Phi>\<close>
  by (cases f)
    (auto simp: RES_RETURN_RES4')

lemma RES_RETURN_RES5':
  \<open>RES \<Phi> \<bind> (\<lambda>(T, T', T'', T''', T''''). RETURN (f T T' T'' T''' T'''')) =
    RES ((\<lambda>(a, b, c, d, e). f a b c d e) ` \<Phi>)\<close>
  apply (subst RES_SPEC_conv)
  apply (subst RES_RETURN_RES5)
  by auto

lemma RETURN_le_RES_no_return5:
  \<open>f \<le> SPEC (\<lambda>(S,T,U,V, W). g S T U V W \<in> \<Phi>) \<Longrightarrow> do {(S, T, U, V, W) \<leftarrow> f; RETURN (g S T U V W)} \<le> RES \<Phi>\<close>
  by (cases f)
    (auto simp: RES_RETURN_RES5')



lemma mset_remove_filtered: \<open>C - {#x \<in># C. P x#} = {#x \<in># C. \<not>P x#}\<close>
  by (metis add_implies_diff union_filter_mset_complement)

lemma simplify_clause_with_unit2_simplify_clause_with_unit:
  fixes N :: \<open>'v clauses_l\<close>
  assumes \<open>C \<in># dom_m N\<close> \<open>no_dup M\<close> and
    st: \<open>(M,M') \<in> Id\<close> \<open>(C,C') \<in> Id\<close> \<open>(N,N')\<in> Id\<close>
  shows
  \<open>simplify_clause_with_unit2 C M N \<le> \<Down> {((N, L, b, i), (b', N')).
  (C \<in># dom_m N \<longrightarrow> N' = N) \<and>
  (C \<notin># dom_m N \<longrightarrow> fmdrop C N' = N) \<and>
  (\<not>b \<longrightarrow> length (N' \<propto> C) = 1 \<longrightarrow> C \<notin>#dom_m N \<and> N' \<propto> C = [L]) \<and>
  (if b \<or> i \<le> 1 then C \<notin># dom_m N else C \<in>#dom_m N) \<and>
  (b=b') \<and>
  (\<not>b \<longrightarrow> i = size (N' \<propto> C))}
  (simplify_clause_with_unit C' M' N')\<close>
proof -
  have simplify_clause_with_unit_alt_def:
    \<open>simplify_clause_with_unit = (\<lambda>C M N. do {
    (b, N') \<leftarrow>
      SPEC(\<lambda>(b, N'). fmdrop C N = fmdrop C N' \<and> mset (N' \<propto> C) \<subseteq># mset (N \<propto> C) \<and> C \<in># dom_m N' \<and>
        (\<not>b \<longrightarrow> (\<forall>L \<in># mset (N' \<propto> C). undefined_lit M L)) \<and>
        (\<forall>L \<in># mset (N \<propto> C) - mset (N' \<propto> C). defined_lit M L) \<and>
       (irred N C = irred N' C) \<and>
       (b \<longleftrightarrow> (\<exists>L. L \<in># mset (N \<propto> C) \<and> L \<in> lits_of_l M)));
    RETURN (b, N')
    })\<close> (is \<open>_ = (\<lambda>C M N. do {
    (_, _) \<leftarrow> SPEC (?P C M N);
      RETURN _})\<close>)
    unfolding simplify_clause_with_unit_def by auto
  have st: \<open>M' = M\<close> \<open>C'=C\<close> \<open>N'=N\<close>
    using st by auto
  let ?R = \<open>measure (\<lambda>(i, j, N', is_true). Suc (length (N \<propto> C)) - j)\<close>
  define I where
    \<open>I = (\<lambda>(i::nat, j::nat, N' :: 'v clauses_l, del:: 'v clause, is_true). i \<le> j \<and>
    j \<le> length (N \<propto> C) \<and>
    C \<in># dom_m N' \<and>
    (
      (\<forall>L\<in>set (take i (N' \<propto> C)). undefined_lit M L) \<and>
      (\<forall>L\<in># del. defined_lit M L) \<and>
      drop j (N' \<propto> C) = drop j (N \<propto> C) \<and>
      length (N' \<propto> C) = length (N \<propto> C) \<and>
      mset (take j (N \<propto> C)) = del + mset (take i (N' \<propto> C))) \<and>
    fmdrop C N' = fmdrop C N \<and>
    (irred N' C = irred N C) \<and>
    (is_true \<longleftrightarrow>  (\<exists>L \<in> set (take j (N \<propto> C)). L \<in> lits_of_l M)))\<close>
  have I0: \<open>I (0, 0, N, {#}, False)\<close>
    using assms unfolding I_def
    by auto
  have H: \<open>(if b then RETURN P else RETURN Q) = RETURN (if b then P else Q)\<close> for b P Q
    by auto
  have I_Suc: \<open>I (if polarity M (ab \<propto> C ! aa) = Some True
    then (a, aa + 1, ab, add_mset (ab \<propto> C ! aa) del,True)
    else if polarity M (ab \<propto> C ! aa) = Some False
    then (a, aa + 1, ab, add_mset (ab \<propto> C ! aa) del, False)
    else (a + 1, aa + 1, ab(C \<hookrightarrow> (ab \<propto> C)[a := ab \<propto> C ! aa]), del, False))\<close>
    if 
      I: \<open>I s\<close> and
      \<open>case s of (i, j, _, _, b) \<Rightarrow> \<not> b \<and> j < length (N \<propto> C)\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>b = (aa, ba)\<close>
        \<open>ba = (ab, bdel)\<close>
      \<open>bdel = (del, bb)\<close> and
      le: \<open>a < length (ab \<propto> C) \<and> aa < length (ab \<propto> C) \<and> C \<in># dom_m ab\<close>
    for s a b aa ba ab bb el del bdel
  proof -
    have[simp]: \<open>C \<notin># remove1_mset C (dom_m N)\<close>
      using assms distinct_mset_dom[of N]
      by (auto dest!: multi_member_split)
    have [simp]: \<open>(take a (ab \<propto> C) @ [ab \<propto> C ! a])[a := N \<propto> C ! aa] =
      take a (ab \<propto> C) @ [N \<propto> C ! aa]\<close>
      using I le unfolding I_def st
      by (auto simp: list_update_append)

    consider
        \<open>polarity M (ab \<propto> C ! aa) = Some True\<close> |
        \<open>polarity M (ab \<propto> C ! aa) = Some False\<close> |
        \<open>polarity M (ab \<propto> C ! aa) = None\<close>
      by (cases \<open>polarity M (ab \<propto> C ! aa)\<close>) auto
    then show ?thesis
      using that
      apply cases
      subgoal
        by (auto simp: I_def take_Suc_conv_app_nth fmdrop_fmupd_same
          polarity_spec' assms
          simp flip: Cons_nth_drop_Suc
          dest: in_lits_of_l_defined_litD)
      subgoal
        by (auto simp: I_def take_Suc_conv_app_nth fmdrop_fmupd_same
            polarity_spec' assms
            dest: uminus_lits_of_l_definedD
          simp flip: Cons_nth_drop_Suc)
      subgoal
        by (simp add: I_def take_Suc_conv_app_nth polarity_spec' assms(2)
          fmdrop_fmupd_same
          flip: Cons_nth_drop_Suc)
           (clarsimp simp only: Decided_Propagated_in_iff_in_lits_of_l
            simp_thms)
      done
  qed
  have [simp]: \<open>C \<notin># remove1_mset C (dom_m x1b)\<close> for x1b
    using distinct_mset_dom[of x1b]
    by (cases \<open>C \<in># dom_m x1b\<close>) (auto dest!: multi_member_split)
  have H0: \<open>C = [c] \<longleftrightarrow> mset C = {#c#}\<close> for C c
    by auto
  have filt: \<open>(\<And>x. x \<in># C \<Longrightarrow> P x) \<Longrightarrow> filter_mset P C = C\<close>
    \<open>(\<And>x. x \<in># C \<Longrightarrow> \<not>P x) \<Longrightarrow> filter_mset P C = {#}\<close>
    \<open>filter P D = [] \<longleftrightarrow> (\<forall>L\<in>#mset D. \<not>P L)\<close>for C P D
    by (simp_all add: filter_mset_eq_conv filter_empty_conv)
  have [simp]: \<open>take (Suc 0) C = [C!0] \<longleftrightarrow> C \<noteq> []\<close> for C
    by (cases C) auto
  have in_set_dropp_begin:
    \<open>drop n xs = drop n ys \<Longrightarrow> n < length xs \<Longrightarrow> xs ! n \<in> set ys\<close> for n xs ys
    by (metis in_set_dropI nat_le_eq_or_lt set_drop_subset subset_code(1))+

      term \<open>?P C M N (b, N'')\<close>
      term I
  let ?Q = \<open>\<lambda>(i::nat, j::nat, N', del, is_true) (b, N'').
    (let P = (if is_true
      then N'(C \<hookrightarrow> filter (Not o defined_lit M) (N \<propto> C))
    else N'(C \<hookrightarrow> take i (N' \<propto> C)))in
        (P, N'') \<in> Id \<and> ?P C M N (b, N''))\<close>
   have H3: \<open>\<forall>x\<in>#ab. defined_lit M x \<Longrightarrow>
        undefined_lit M a \<Longrightarrow>
        mset (N \<propto> C) = add_mset a ab \<Longrightarrow>
        filter (undefined_lit M) (N \<propto> C) = [a]\<close> for a ab
     by (simp add: H0 filt)
  show ?thesis
    unfolding simplify_clause_with_unit_alt_def simplify_clause_with_unit2_def
      Let_def H conc_fun_RES st
    apply (rule ASSERT_leI)
    subgoal using assms by auto
    apply (refine_vcg WHILEIT_rule_stronger_inv_RES'[where I'=I and R = \<open>?R\<close> and
      H = \<open>{(a, b). I a \<and> ?Q a (b) \<and>  (fst b \<longleftrightarrow>  ((snd o snd o snd o snd) a))}\<close>])
    subgoal by auto
    subgoal by (auto simp: I_def)
    subgoal by (rule I0)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def intro: in_set_dropp_begin)
    subgoal by (auto simp: I_def split: if_splits)
    subgoal by (rule I_Suc)
    subgoal by (auto simp: I_def)
      find_theorems "do {ASSERT _; _} \<le> (SPEC _)"
    subgoal for s
      supply [[goals_limit=1]]
      using assms(2)
      unfolding mem_Collect_eq RETURN_RES_refine_iff case_prod_beta
      apply (auto simp: I_def fmdrop_fmupd_same mset_remove_filtered comp_def
        intro: in_lits_of_l_defined_litD)
      apply (auto dest: in_set_takeD)[4]
      apply (intro conjI impI exI[of _ \<open>if (snd o snd o snd o snd) s
    then (fst (snd (snd s)))(C \<hookrightarrow> filter (Not o defined_lit M) (N \<propto> C))
      else (fst (snd (snd s)))(C \<hookrightarrow> take (fst s) ((fst (snd (snd s))) \<propto> C))\<close>])
      apply (auto simp: I_def fmdrop_fmupd_same mset_remove_filtered comp_def
          intro: in_lits_of_l_defined_litD dest: )
        apply (auto simp add: I_def filt H0)
        apply (simp only: size_mset[symmetric] mset_filter filter_union_mset)
        apply (subst filt(1), simp, simp)
        apply (metis (no_types, lifting) diff_union_cancelR filt(1) set_mset_mset)
        apply (simp only: size_mset[symmetric] mset_filter filter_union_mset)
        apply (intro conjI impI exI[of _ \<open>if (snd o snd o snd o snd) s  \<or> fst s \<le> 1
      then (fst (snd (snd s)))(C \<hookrightarrow> filter (Not o defined_lit M) (N \<propto> C))
        else  (fst (snd (snd s)))(C \<hookrightarrow> take (fst s) ((fst (snd (snd s))) \<propto> C))\<close>])
        apply (auto simp: I_def fmdrop_fmupd_same mset_remove_filtered comp_def
          intro: in_lits_of_l_defined_litD)
        apply (auto simp add: I_def filt H0 H3)
        apply (subst filt(1), simp, simp)
        apply (metis (no_types, lifting) diff_union_cancelR filt(1) set_mset_mset)
        apply (subst filt(1), simp, simp)
        apply (metis (no_types, lifting) diff_union_cancelR filt(1) set_mset_mset)
        apply (case_tac x; case_tac \<open>aa \<propto> C\<close>)
        apply (auto simp: H3)
        done
     subgoal for s x1 x2 x1a x2a x1b x2b x1c x2c
        by (auto simp add: I_def)
    subgoal for s x1 x2 x1a x2a x1b x2b x1c x2c
      by (auto simp add: I_def)
    subgoal for s x1 x2 x1a x2a x1b x2b x1c x2c
      by (auto simp add: I_def split: if_splits)
    done
qed

definition simplify_clause_with_unit_st2 where
  \<open>simplify_clause_with_unit_st2 =  (\<lambda>C (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, WS, Q). do {
    ASSERT (simplify_clause_with_unit_st_pre C (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, WS, Q));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None \<and> WS = {#});
    if C \<in> set (get_all_mark_of_propagated M)
    then RETURN (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, WS, Q)
    else do {
      let E = mset (N\<^sub>0 \<propto> C);
      let irr = irred N\<^sub>0 C;
      (N, L, b, i) \<leftarrow> simplify_clause_with_unit2 C M N\<^sub>0;
      if b then
        RETURN (M, N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, WS, Q)
      else if i = 1
      then do {
        RETURN (Propagated L 0 # M, N, D, (if irr then add_mset {#L#} else id) NE, (if \<not>irr then add_mset {#L#} else id)UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, WS, add_mset (-L) Q)}
      else if i = 0
        then RETURN (M, N, Some {#}, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, WS, {#})
      else
          RETURN (M, N, D, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, WS, Q)
    }
     })\<close>

lemma simplify_clause_with_unit_st2_simplify_clause_with_unit_st:
  assumes \<open>(C,C')\<in>Id\<close> \<open>(S,S')\<in>Id\<close>
  shows
    \<open>simplify_clause_with_unit_st2 C S \<le> \<Down>Id (simplify_clause_with_unit_st C' S')\<close>
  using assms
  unfolding simplify_clause_with_unit_st2_def simplify_clause_with_unit_st_def
  supply [[goals_limit=1]]
  apply (refine_rcg simplify_clause_with_unit2_simplify_clause_with_unit)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply (simp only: mem_Collect_eq pair_in_Id_conv)
    apply (subst (asm)  prod.simps eq_commute[of _ \<open>length _\<close>])+
    by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition simplify_clauses_with_unit_st2 :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close>  where
  \<open>simplify_clauses_with_unit_st2 S =
  do {
  ASSERT(simplify_clauses_with_unit_st_pre S);
  xs \<leftarrow> SPEC(\<lambda>xs. xs \<subseteq>set_mset (dom_m (get_clauses_l S)));
  T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_inv S it T)
  (xs)
  (\<lambda>S. get_conflict_l S = None)
  (\<lambda>i S. simplify_clause_with_unit_st2 i S)
  S;
  ASSERT(set_mset (all_learned_lits_of_l T) \<subseteq> set_mset (all_learned_lits_of_l S));
  ASSERT(set_mset (all_init_lits_of_l T) = set_mset (all_init_lits_of_l S));
  RETURN T
  }\<close>

lemma simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st:
  assumes \<open>(S,S')\<in>Id\<close>
  shows
    \<open>simplify_clauses_with_unit_st2 S \<le> \<Down>Id (simplify_clauses_with_unit_st S')\<close>
proof -
  have inj: \<open>inj_on id x\<close> for x
    by auto
  show ?thesis
    using assms
    unfolding simplify_clauses_with_unit_st2_def simplify_clauses_with_unit_st_def
    by (refine_vcg simplify_clause_with_unit_st2_simplify_clause_with_unit_st inj)
      auto
qed

definition arena_shorten :: \<open>nat \<Rightarrow> nat \<Rightarrow> arena \<Rightarrow> arena\<close> where
  \<open>arena_shorten C j N =
  (if j > MAX_LENGTH_SHORT_CLAUSE then  N[C - SIZE_SHIFT := ASize (j-2), C - POS_SHIFT := APos 0]
  else N[C - SIZE_SHIFT := ASize (j-2)])\<close>


definition arena_shorten_pre where
    \<open>arena_shorten_pre C j arena \<longleftrightarrow> j \<ge> 2 \<and> arena_is_valid_clause_idx arena C \<and>
      j \<le> arena_length arena C\<close>

definition mop_arena_shorten where
  \<open>mop_arena_shorten C j arena = do {
    ASSERT(arena_shorten_pre C j arena);
    RETURN (arena_shorten C j arena)
  }\<close>

lemma valid_arena_arena_shorten:
  assumes C: \<open>C \<in># dom_m N\<close> and
    j: \<open>j \<le> arena_length arena C\<close> and
    valid: \<open>valid_arena arena N vdom\<close> and
    j2: \<open>j \<ge> 2\<close>
  shows \<open>valid_arena (arena_shorten C j arena) (N(C \<hookrightarrow> take j (N \<propto> C))) vdom\<close>
proof -
  let ?N = \<open>N(C \<hookrightarrow> take j (N \<propto> C))\<close>
  have header: \<open>header_size (take j (N \<propto> C)) \<le> header_size (N \<propto> C)\<close>
    by (auto simp: header_size_def)
  let ?arena = \<open>(if j > MAX_LENGTH_SHORT_CLAUSE then
       arena[C - SIZE_SHIFT := ASize (j-2), C - POS_SHIFT := APos 0]
    else arena[C - SIZE_SHIFT := ASize (j-2)])\<close>
  have dead_clause: \<open>arena_dead_clause (Misc.slice (i - 2) i ?arena) \<longleftrightarrow>
    arena_dead_clause (Misc.slice (i - 2) i arena)\<close>
    if i: \<open>i \<in> vdom\<close> \<open>i \<notin># dom_m N\<close>
    for i
  proof -
    have [simp]: \<open>Misc.slice (i - 2) i (arena[C - Suc 0 := ASize (j - 2)]) =
      Misc.slice (i - 2) i (arena)\<close>
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j
        valid_arena_in_vdom_le_arena[OF valid, of i]
      apply -
      apply (subst slice_irrelevant(3))
      apply auto
      by (metis One_nat_def SIZE_SHIFT_def Suc_le_lessD Suc_pred \<open>\<lbrakk>i \<notin># dom_m N; C \<le> i; i \<in> vdom\<rbrakk> \<Longrightarrow> length (N \<propto> C) + 2 \<le> i - C\<close> add_leD2 diff_diff_cancel diff_le_self le_diff_iff' nat_le_Suc_less_imp that(1) that(2) verit_comp_simplify1(3)) 

    have [simp]:
      \<open>Misc.slice (i - 2) i (arena[C - SIZE_SHIFT := ASize (j - 2), C - POS_SHIFT := APos 0]) =
      Misc.slice (i - 2) i arena\<close> if j5: \<open>j > MAX_LENGTH_SHORT_CLAUSE\<close>
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j that i
        valid_arena_in_vdom_le_arena[OF valid, of i] j
      apply -
      apply (subst slice_irrelevant(3))
      apply (auto simp: SHIFTS_def not_less_eq header_size_def linorder_class.not_le
        split: if_splits)
      by (metis diff_diff_cancel diff_le_self le_diff_iff' less_or_eq_imp_le numeral_3_eq_3 verit_comp_simplify1(3))
    show ?thesis
      using that
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j 
        valid_arena_in_vdom_le_arena[OF valid, of i]
      apply -
      apply (simp split: if_splits, intro conjI impI)
      subgoal
        apply (subst slice_irrelevant(3))
        apply (cases \<open>C < i\<close>)
        apply (auto simp: arena_dead_clause_def not_less_eq
          SHIFTS_def header_size_def)
        by (metis less_Suc_eq nat_le_Suc_less_imp)
     done
   qed
  have other_active: \<open>i \<noteq> C \<Longrightarrow>
    i \<in># dom_m N \<Longrightarrow>
    xarena_active_clause (clause_slice (?arena) N i)
    (the (fmlookup N i)) \<longleftrightarrow>
    xarena_active_clause (clause_slice (arena) N i)
    (the (fmlookup N i))\<close> for i
    using 
      arena_lifting(1,4,15,18)[OF valid C] j
      arena_lifting(18)[OF valid, of i]
      valid_minimal_difference_between_valid_index[OF valid C, of i]
      valid_minimal_difference_between_valid_index[OF valid _ C, of i]
    apply -
    apply (simp split: if_splits, intro conjI impI)
    apply (subst slice_irrelevant(3))
    subgoal
      by (cases \<open>C < i\<close>)
       (auto simp: arena_dead_clause_def arena_lifting SHIFTS_def not_less_eq
        header_size_def split: if_splits)
    subgoal
      by (cases \<open>C < i\<close>)
        (auto simp: arena_dead_clause_def arena_lifting SHIFTS_def not_less_eq
        header_size_def split: if_splits)
    subgoal
      by (cases \<open>C < i\<close>)
        (auto simp: arena_dead_clause_def arena_lifting SHIFTS_def not_less_eq
        header_size_def split: if_splits)
   done
 have [simp]:
   \<open>Misc.slice C (C + arena_length arena C) arena = map ALit (N \<propto> C) \<Longrightarrow> Misc.slice C (C + j) arena = map ALit (take j (N \<propto> C))\<close>
   by (drule arg_cong[of _ _ \<open>take j\<close>])
    (use j j2 arena_lifting[OF valid C] in \<open>auto simp: Misc.slice_def take_map\<close>)

  have arena2: \<open>xarena_active_clause (clause_slice arena N C) (the (fmlookup N C)) \<Longrightarrow>
    xarena_active_clause (clause_slice ?arena ?N C)
    (take j (N \<propto> C), irred N C)\<close>
    using j j2 arena_lifting[OF valid C] header
    apply (subst (asm) xarena_active_clause_alt_def)
    apply (subst xarena_active_clause_def)
    apply simp
    apply (intro conjI impI)
    apply (simp add: slice_head SHIFTS_def header_size_def
      slice_len_min_If slice_nth; fail)+
    done

  show ?thesis
    using assms header distinct_mset_dom[of N] arena2 other_active dead_clause
    unfolding valid_arena_def arena_shorten_def
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
qed

lemma mop_arena_shorten_spec:
  assumes C: \<open>C \<in># dom_m N\<close> and
    j: \<open>j \<le> arena_length arena C\<close> and
    valid: \<open>valid_arena arena N vdom\<close> and
    j2: \<open>j \<ge> 2\<close> and
    \<open>(C,C')\<in>nat_rel\<close> \<open>(j,j')\<in>nat_rel\<close>
  shows \<open>mop_arena_shorten C j arena \<le> SPEC(\<lambda>c. (c, N(C' \<hookrightarrow> take j' (N \<propto> C'))) \<in>
       {(arena, N). valid_arena arena N vdom})\<close>
  unfolding mop_arena_shorten_def
  apply refine_vcg
  subgoal
    using assms
    unfolding arena_shorten_pre_def arena_is_valid_clause_idx_def by auto
  subgoal
    using assms
    by (auto intro!: valid_arena_arena_shorten)
  done

definition arenap_update_lit :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> arena \<Rightarrow> arena\<close> where
  \<open>arenap_update_lit C j L N = N[C + j := ALit L]\<close>

lemma length_arenap_update_lit[simp]: \<open>length (arenap_update_lit C j L arena) = length arena\<close>
  by (auto simp: arenap_update_lit_def)

lemma valid_arena_arenap_update_lit:
  assumes C: \<open>C \<in># dom_m N\<close> and
    j: \<open>j < arena_length arena C\<close> and
    valid: \<open>valid_arena arena N vdom\<close>
  shows \<open>valid_arena (arenap_update_lit C j  L arena) (N(C \<hookrightarrow> (N \<propto> C)[j := L])) vdom\<close>
proof -
  let ?N = \<open>N(C \<hookrightarrow> (N \<propto> C)[j := L])\<close>
  have header[simp]: \<open>header_size (?N \<propto> C) = header_size (N \<propto> C)\<close>
    by (auto simp: header_size_def)
  let ?arena = \<open>arenap_update_lit C j L arena\<close>
  have dead_clause: \<open>arena_dead_clause (Misc.slice (i - 2) i ?arena) \<longleftrightarrow>
    arena_dead_clause (Misc.slice (i - 2) i arena)\<close>
    if i: \<open>i \<in> vdom\<close> \<open>i \<notin># dom_m N\<close>
    for i
  proof -
    have [simp]: \<open>Misc.slice (i - 2) i (arena[C - Suc 0 := ASize (j - 2)]) =
      Misc.slice (i - 2) i (arena)\<close>
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j
        valid_arena_in_vdom_le_arena[OF valid, of i]
      apply -
      apply (subst slice_irrelevant(3))
      apply auto
      by (metis One_nat_def SIZE_SHIFT_def Suc_le_lessD Suc_pred \<open>\<lbrakk>i \<notin># dom_m N; C \<le> i; i \<in> vdom\<rbrakk> \<Longrightarrow> length (N \<propto> C) + 2 \<le> i - C\<close> add_leD2 diff_diff_cancel diff_le_self le_diff_iff' nat_le_Suc_less_imp that(1) that(2) verit_comp_simplify1(3)) 

    have [simp]:
      \<open>Misc.slice (i - 2) i ?arena =
      Misc.slice (i - 2) i arena\<close>
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j that i
        valid_arena_in_vdom_le_arena[OF valid, of i] j
      unfolding arenap_update_lit_def
      apply -
      apply (subst slice_irrelevant(3))
      apply (auto simp: SHIFTS_def not_less_eq header_size_def linorder_class.not_le
        split: if_splits)
      apply linarith
      apply linarith
      done
    show ?thesis
      using that
      using minimal_difference_between_invalid_index[OF valid C, of i]
        minimal_difference_between_invalid_index2[OF valid C, of i]
        arena_lifting(1,4,15,18)[OF valid C] j 
        valid_arena_in_vdom_le_arena[OF valid, of i]
      unfolding arenap_update_lit_def
      apply -
      apply (subst slice_irrelevant(3))
      apply (cases \<open>C < i\<close>)
      apply (auto simp: arena_dead_clause_def not_less_eq
        SHIFTS_def header_size_def)
     done
  qed
  have other_active: \<open>i \<noteq> C \<Longrightarrow>
    i \<in># dom_m N \<Longrightarrow>
    xarena_active_clause (clause_slice (?arena) N i)
    (the (fmlookup N i)) \<longleftrightarrow>
    xarena_active_clause (clause_slice (arena) N i)
    (the (fmlookup N i))\<close> for i
    using 
      arena_lifting(1,4,15,18)[OF valid C] j
      arena_lifting(18)[OF valid, of i]
      valid_minimal_difference_between_valid_index[OF valid C, of i]
      valid_minimal_difference_between_valid_index[OF valid _ C, of i]
    unfolding arenap_update_lit_def
    apply -
    apply (subst slice_irrelevant(3))
    subgoal
      by (cases \<open>C < i\<close>)
       (auto simp: arena_dead_clause_def arena_lifting SHIFTS_def not_less_eq
        header_size_def split: if_splits)
    subgoal
      by (cases \<open>C < i\<close>)
        (auto simp: arena_dead_clause_def arena_lifting SHIFTS_def not_less_eq
        header_size_def split: if_splits)
   done
 have [simp]: \<open>header_size ((N \<propto> C)[j := L]) = header_size (N \<propto> C)\<close>
   by (auto simp: header_size_def)
 have [simp]:
   \<open>Misc.slice C (C + arena_length arena C) arena = map ALit (N \<propto> C) \<Longrightarrow>
   drop (header_size (N \<propto> C)) ((Misc.slice (C - header_size (N \<propto> C)) (C + arena_length arena C) arena)[j + header_size (N \<propto> C) := ALit L]) =
   map ALit ((N \<propto> C)[j := L])\<close>
   by (drule arg_cong[of _ _ \<open> \<lambda>xs. xs [j := ALit L]\<close>])
      (use j arena_lifting(1-4)[OF valid C] in \<open>auto simp: drop_update_swap map_update\<close>)

  have arena2: \<open>xarena_active_clause (clause_slice arena N C) (the (fmlookup N C)) \<Longrightarrow>
    xarena_active_clause (clause_slice ?arena ?N C)
    ((?N \<propto> C), irred N C)\<close>
    using j arena_lifting[OF valid C] header
    unfolding arenap_update_lit_def
    apply (subst (asm) xarena_active_clause_alt_def)
    apply (subst xarena_active_clause_def)
    apply (subst prod.simps)
    apply simp
    apply (intro conjI impI)
    apply (simp add: slice_head SHIFTS_def header_size_def
      slice_len_min_If slice_nth; fail)+
    done
  show ?thesis
    using assms distinct_mset_dom[of N] arena2 other_active dead_clause
    unfolding valid_arena_def arena_shorten_def
    by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
qed

definition mop_arena_update_lit :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> arena \<Rightarrow> arena nres\<close> where
  \<open>mop_arena_update_lit C j L arena = do {
    ASSERT(arena_lit_pre2 arena C j);
    RETURN (arenap_update_lit C j L arena)
  }\<close>

lemma mop_arena_update_lit_spec:
  assumes C: \<open>C \<in># dom_m N\<close> and
    j: \<open>j < arena_length arena C\<close> and
    valid: \<open>valid_arena arena N vdom\<close> and
    \<open>(j,j') \<in> nat_rel\<close> and
    \<open>(C,C') \<in> nat_rel\<close> and
    \<open>(L,L') \<in> nat_lit_lit_rel\<close>
  shows
    \<open>mop_arena_update_lit C j L arena \<le> SPEC (\<lambda>c. (c, (N(C' \<hookrightarrow> (N \<propto> C')[j' := L']))) \<in>
    {(arena, N). valid_arena arena N vdom})\<close>
  unfolding mop_arena_update_lit_def
  apply refine_vcg
  subgoal using assms unfolding arena_lit_pre2_def
    by (auto simp: arena_lifting)
  subgoal using assms by (auto intro!: valid_arena_arenap_update_lit)
  done



definition isa_simplify_clause_with_unit2 where
  \<open>isa_simplify_clause_with_unit2 C M N = do {
    let l = arena_length N C;
    (i, j, N::arena, is_true) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, j, N::arena, b). \<not>b \<and> j < l)
    (\<lambda>(i, j, N, is_true). do {
      L \<leftarrow> mop_arena_lit2 N C j;
      val \<leftarrow> mop_polarity_pol M L;
      if val = Some True then RETURN (i, j+1, N,True)
      else if val = Some False
      then RETURN (i, j+1, N,  False)
        else do {
        N \<leftarrow> mop_arena_update_lit C i L N;
        RETURN (i+1, j+1, N, False)}
    })
      (0, 0, N, False);
   L \<leftarrow> mop_arena_lit2 N C 0;
   if is_true \<or> i \<le> 1
   then RETURN (extra_information_mark_to_delete N C, L, is_true, i)
   else do {
      N \<leftarrow> mop_arena_shorten C i N;
      RETURN (N, L, is_true, i)}
    }\<close>
 
lemma simplify_clause_with_unit2_alt_def:
  \<open>simplify_clause_with_unit2 C M N\<^sub>0 = do {
      ASSERT(C \<in># dom_m N\<^sub>0);
      let l = length (N\<^sub>0 \<propto> C);
        (i, j, N, del, is_true) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, j, N, del, b). C \<in># dom_m N\<^esup>
        (\<lambda>(i, j, N, del, b). \<not>b \<and> j < l)
        (\<lambda>(i, j, N, del, is_true). do {
           ASSERT(i < length (N \<propto> C) \<and> j < length (N \<propto> C) \<and> C \<in># dom_m N);
           let L = N \<propto> C ! j;
           ASSERT(L \<in> set (N\<^sub>0 \<propto> C));
           let val = polarity M L;
           if val = Some True then RETURN (i, j+1, N, add_mset L del, True)
           else if val = Some False
         then RETURN (i, j+1, N, add_mset L del, False)
           else let N = N(C \<hookrightarrow> ((N \<propto> C)[i := L])) in RETURN (i+1, j+1, N, del, False)
        })
        (0, 0, N\<^sub>0, {#}, False);
    ASSERT (C \<in># dom_m N \<and> i \<le> length (N \<propto> C));
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (fmdrop C N, L, is_true, i)
      else do {
      let N = N(C \<hookrightarrow> (take i (N \<propto> C))) in RETURN (N, L, is_true, i)}
  }\<close>
   unfolding Let_def simplify_clause_with_unit2_def
   by simp

lemma isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit:
  assumes \<open>valid_arena arena N vdom\<close> and
    trail: \<open>(M, M') \<in> trail_pol \<A>\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close>
  shows \<open>isa_simplify_clause_with_unit2 C M arena \<le> \<Down>
    ({(arena, N). valid_arena arena N vdom} \<times>\<^sub>r
    Id \<times>\<^sub>r bool_rel \<times>\<^sub>r nat_rel)
    (simplify_clause_with_unit2 C M' N)\<close>
proof -
  have [refine0]: \<open>C \<in># dom_m N \<Longrightarrow>
  ((0, 0, arena, False), 0, 0, N, {#}, False) \<in> {((i, j, N, is_true),
    (i', j', N', del', is_true')).
    ((i, j, N, is_true), (i', j', N', is_true')) \<in>
    nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(arena, N). valid_arena arena N vdom \<and> C \<in># dom_m N} \<times>\<^sub>r
    bool_rel}\<close>
    using assms by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_simplify_clause_with_unit2_def simplify_clause_with_unit2_alt_def
      mop_polarity_pol_def nres_monad3
    apply (refine_rcg mop_arena_lit[where vdom=vdom]
      polarity_pol_pre[OF trail]
      polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp,
        THEN fref_to_Down_unRET_uncurry]
       mop_arena_shorten_spec[where vdom=vdom]
     )
    subgoal using assms by (auto simp add: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      using lits
      by (auto simp:
      all_lits_of_mm_def ran_m_def dest!: multi_member_split
      dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_msetD)
    subgoal
      using lits
      by (auto simp:
        all_lits_of_mm_def ran_m_def dest!: multi_member_split
        dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_mm_add_msetD)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule_tac mop_arena_update_lit_spec[where vdom=vdom])
    subgoal by auto
    subgoal by (auto simp: arena_lifting)
    subgoal by (auto simp: arena_lifting)
    subgoal by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
      using arena_lifting(4,19)[of x1f x1b vdom C] by auto
    subgoal by auto
    subgoal by (auto intro!: valid_arena_extra_information_mark_to_delete')
    subgoal by auto
    subgoal by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed
end