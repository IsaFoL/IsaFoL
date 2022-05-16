theory IsaSAT_Simplify_Units
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart (*line 691 in auto TODO: which simp rule should be moved?*)
begin

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
           ASSERT(i < length (N \<propto> C) \<and> j < length (N \<propto> C) \<and> C \<in># dom_m N \<and> i \<le> j);
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
    ASSERT(is_true \<or> j = l);
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (False, fmdrop C N, L, is_true, i)
    else if i = j \<and> \<not>is_true then RETURN (True, N, L, is_true, i)
    else do {
      RETURN (False, N(C \<hookrightarrow> (take i (N \<propto> C))), L, is_true, i)
    }
  }\<close>

(*TODO Move*)
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
(*end move*)

text \<open>Makes the simplifier loop...\<close>
definition simplify_clause_with_unit2_rel_simp_wo where
  \<open>simplify_clause_with_unit2_rel_simp_wo unc N N\<^sub>0 N' \<longleftrightarrow>
  (unc \<longrightarrow> N = N\<^sub>0 \<and> N' = N\<^sub>0)\<close>

lemma simplify_clause_with_unit2_rel_simp_wo[iff]:
  \<open>simplify_clause_with_unit2_rel_simp_wo True N N\<^sub>0 N' \<longleftrightarrow>
  (N = N\<^sub>0 \<and> N' = N\<^sub>0)\<close>
  \<open>simplify_clause_with_unit2_rel_simp_wo False N N\<^sub>0 N'\<close>
 unfolding simplify_clause_with_unit2_rel_simp_wo_def by auto

definition simplify_clause_with_unit2_rel where
  \<open>simplify_clause_with_unit2_rel N\<^sub>0 C=
  {((unc, N, L, b, i), (unc', b', N')).
  (C \<in># dom_m N \<longrightarrow> N' = N) \<and>
  (C \<notin># dom_m N \<longrightarrow> fmdrop C N' = N) \<and>
  (\<not>b \<longrightarrow> length (N' \<propto> C) = 1 \<longrightarrow> C \<notin>#dom_m N \<and> N' \<propto> C = [L]) \<and>
  (if b \<or> i \<le> 1 then C \<notin># dom_m N else C \<in>#dom_m N) \<and>
  (b=b') \<and>
  (\<not>b \<longrightarrow> i = size (N' \<propto> C)) \<and>
  C \<in># dom_m N' \<and>
    (b \<or> i \<le> 1 \<longrightarrow> size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irred N\<^sub>0 C then 0 else 1))\<and>
    (\<not>(b \<or> i \<le> 1) \<longrightarrow> size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0)) \<and>
    (C \<in># dom_m N \<longrightarrow> dom_m N = dom_m N\<^sub>0) \<and>
    (C \<in># dom_m N \<longrightarrow> irred N C = irred N\<^sub>0 C \<and> irred N C = irred N' C) \<and>
    (C \<notin># dom_m N \<longrightarrow> dom_m N = remove1_mset C (dom_m N\<^sub>0)) \<and>
    unc=unc' \<and>
  simplify_clause_with_unit2_rel_simp_wo unc N N\<^sub>0 N'}\<close>
 
lemma simplify_clause_with_unit2_simplify_clause_with_unit:
  fixes N N\<^sub>0 :: \<open>'v clauses_l\<close> and N' :: \<open>'a\<close>
  assumes \<open>C \<in># dom_m N\<close> \<open>no_dup M\<close> and
    st: \<open>(M,M') \<in> Id\<close> \<open>(C,C') \<in> Id\<close> \<open>(N,N\<^sub>0)\<in> Id\<close>
  shows
  \<open>simplify_clause_with_unit2 C M N \<le> \<Down> (simplify_clause_with_unit2_rel N\<^sub>0 C)
  (simplify_clause_with_unit C' M' N\<^sub>0)\<close>
proof -
  have simplify_clause_with_unit_alt_def:
    \<open>simplify_clause_with_unit = (\<lambda>C M N. do {
    (unc, b, N') \<leftarrow>
      SPEC(\<lambda>(unc, b, N'). fmdrop C N = fmdrop C N' \<and> mset (N' \<propto> C) \<subseteq># mset (N \<propto> C) \<and> C \<in># dom_m N' \<and>
        (\<not>b \<longrightarrow> (\<forall>L \<in># mset (N' \<propto> C). undefined_lit M L)) \<and>
        (\<forall>L \<in># mset (N \<propto> C) - mset (N' \<propto> C). defined_lit M L) \<and>
       (irred N C = irred N' C) \<and>
        (b \<longleftrightarrow> (\<exists>L. L \<in># mset (N \<propto> C) \<and> L \<in> lits_of_l M)) \<and>
       (unc \<longrightarrow> N = N' \<and> \<not>b));
    RETURN (unc, b, N')
    })\<close> (is \<open>_ = (\<lambda>C M N. do {
    (_, _, _) \<leftarrow> SPEC (?P C M N);
      RETURN _})\<close>)
    unfolding simplify_clause_with_unit_def by auto
  have st: \<open>M' = M\<close> \<open>C'=C\<close> \<open>N\<^sub>0=N\<close>
    using st by auto
  let ?R = \<open>measure (\<lambda>(i, j, N', is_true). Suc (length (N \<propto> C)) - j)\<close>
  define I where
    \<open>I = (\<lambda>(i::nat, j::nat, N' :: 'v clauses_l, del:: 'v clause, is_true). i \<le> j \<and>
    j \<le> length (N \<propto> C) \<and>
    C \<in># dom_m N' \<and>
    dom_m N' = dom_m N \<and>
    (
      (\<forall>L\<in>set (take i (N' \<propto> C)). undefined_lit M L) \<and>
      (\<forall>L\<in># del. defined_lit M L) \<and>
      drop j (N' \<propto> C) = drop j (N \<propto> C) \<and>
      length (N' \<propto> C) = length (N \<propto> C) \<and>
      mset (take j (N \<propto> C)) = del + mset (take i (N' \<propto> C))) \<and>
    fmdrop C N' = fmdrop C N \<and>
    (irred N' C = irred N C) \<and>
    (is_true \<longleftrightarrow>  (\<exists>L \<in> set (take j (N \<propto> C)). L \<in> lits_of_l M)) \<and>
    (i = j \<longrightarrow> take i (N' \<propto> C) = take j (N \<propto> C)))\<close>
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
      le: \<open>a < length (ab \<propto> C) \<and> aa < length (ab \<propto> C) \<and> C \<in># dom_m ab \<and> a \<le> aa\<close>
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
          fmdrop_fmupd_same nth_append list_update_append
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
    by (metis in_set_dropD in_set_dropI le_cases)

  let ?Q = \<open>\<lambda>(i::nat, j::nat, N', del, is_true) (unc, b, N'').
    (let P = (if is_true
      then N'(C \<hookrightarrow> filter (Not o defined_lit M) (N \<propto> C))
    else N'(C \<hookrightarrow> take i (N' \<propto> C)))in
        (P, N'') \<in> Id \<and> ?P C M N (unc, b, N'') \<and>
        (is_true \<or> j = length (N \<propto> C)) \<and>
        (unc \<longleftrightarrow> \<not>is_true \<and> i = j \<and> i > 1))\<close>
   have H3: \<open>\<forall>x\<in>#ab. defined_lit M x \<Longrightarrow>
        undefined_lit M a \<Longrightarrow>
        mset (N \<propto> C) = add_mset a ab \<Longrightarrow>
        filter (undefined_lit M) (N \<propto> C) = [a]\<close> for a ab
     by (simp add: H0 filt)
   have H4: \<open>fmdrop C N = fmdrop C x1a \<Longrightarrow> C \<in># dom_m x1a \<Longrightarrow>
     size (learned_clss_l x1a) = size (learned_clss_l N) \<longleftrightarrow>
     (irred x1a C \<longleftrightarrow> irred N C)\<close> for x1a
     using assms(1)
     apply (auto simp: ran_m_def dest!: multi_member_split split: if_splits
       intro!: filter_mset_cong2)
     apply (smt (verit, best) \<open>\<And>x1b. C \<notin># remove1_mset C (dom_m x1b)\<close> add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq fmupd_lookup image_mset_cong2 n_not_Suc_n union_single_eq_member)
     apply (smt (verit, best) \<open>\<And>x1b. C \<notin># remove1_mset C (dom_m x1b)\<close> add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq fmupd_lookup image_mset_cong2 n_not_Suc_n union_single_eq_member)
     apply (smt (verit, best) \<open>\<And>x1b. C \<notin># remove1_mset C (dom_m x1b)\<close> add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq fmupd_lookup image_mset_cong2 union_single_eq_member)
     by (smt (verit, ccfv_SIG) \<open>\<And>x1b. C \<notin># remove1_mset C (dom_m x1b)\<close> add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq fmupd_lookup image_mset_cong2 union_single_eq_member)
   have H5: \<open>irred x2c C \<Longrightarrow>
     size (learned_clss_l (fmupd C (x, True) x2c)) =
     size (learned_clss_l x2c)\<close> for x x2c
    using distinct_mset_dom[of x2c]
    by (cases \<open>C \<in># dom_m x2c\<close>)
     (force dest!: multi_member_split simp: ran_m_def
      intro: filter_mset_cong2 image_mset_cong2
      intro: multiset.map_cong multiset.map_cong0
      intro!: arg_cong[of _ _ size])+
  have H6: \<open>\<not>irred x2c C \<Longrightarrow> C \<in># dom_m x2c \<Longrightarrow>
    size (learned_clss_l (fmupd C (x, False) x2c)) =
    (size (learned_clss_l x2c))\<close> for x x2c
    using distinct_mset_dom[of x2c]
    apply (cases \<open>C \<in># dom_m x2c\<close>)
    by (force dest!: multi_member_split simp: ran_m_def
      intro: filter_mset_cong2 image_mset_cong2
      intro: multiset.map_cong multiset.map_cong0
      intro: arg_cong[of _ _ size])+
  have H7: \<open>\<not>irred x1a C \<Longrightarrow> C \<in># dom_m x1a \<Longrightarrow>
    size (remove1_mset (the (fmlookup x1a C)) (learned_clss_l x1a)) =
    size (learned_clss_l x1a) - Suc 0 \<close> for x1a
    by (auto simp: ran_m_def dest!: multi_member_split)
  have H8: \<open>fmdrop C x1a = fmdrop C N \<Longrightarrow> C \<in># dom_m x1a \<Longrightarrow>
    irred x1a C = irred N C \<Longrightarrow> size (learned_clss_l x1a) - Suc 0 = size (learned_clss_l N) - Suc 0
\<close> for x1a
    using assms(1) distinct_mset_dom[of x1a]
    apply (auto dest!: multi_member_split simp: ran_m_def)
    apply (smt (verit, best) \<open>\<And>x1b. C \<notin># remove1_mset C (dom_m x1b)\<close> add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq2 fmupd_lookup image_mset_cong2 union_single_eq_member)
    by (metis (no_types, lifting) add_mset_remove_trivial dom_m_fmdrop fmdrop_eq_update_eq fmupd_lookup image_mset_cong2 union_single_eq_member)

  have H9: \<open>fmdrop C N = fmdrop C x1a \<Longrightarrow> remove1_mset C (dom_m x1a) = remove1_mset C (dom_m N)\<close> for x1a
    by (metis dom_m_fmdrop)
  have eq_upd_same: \<open>fmdrop C aa = fmdrop C N \<Longrightarrow> b= irred N C \<Longrightarrow>
    N = fmupd C (filter (undefined_lit M) (N \<propto> C), b) aa \<longleftrightarrow>
    (\<forall>x \<in> set (N \<propto> C). undefined_lit M x)\<close> for aa b
    apply (rule iffI)
    subgoal
      by (subst arg_cong[of \<open>N\<close> \<open>fmupd C (filter (undefined_lit M) (N \<propto> C), b) aa\<close>
        \<open>\<lambda>N. N \<propto> C\<close>, unfolded fmupd_lookup])
       simp_all
    subgoal
      apply (subst fmap.fmlookup_inject[symmetric])
      apply (cases \<open>the (fmlookup N C)\<close>; cases \<open>fmlookup N C\<close>)
      using fmupd_same[OF assms(1)] assms(1)
        arg_cong[of \<open>fmdrop C aa\<close> \<open>fmdrop C N\<close> \<open>\<lambda>N. fmlookup N x\<close> for x, unfolded fmlookup_drop]
      apply (auto intro!: ext split: if_splits)
      by metis
    done
  have H11: \<open>\<not> irred N C \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
    size (learned_clss_l (fmdrop C N)) = size (learned_clss_l N) - Suc 0\<close> for N
    using distinct_mset_dom[of N]
    by (auto simp: learned_clss_l_l_fmdrop ran_m_def dest!: multi_member_split
      intro!: arg_cong[of _ _ size] image_mset_cong2 filter_mset_cong2)

  have fmdrop_eq_update_eq': \<open>fmdrop C aa = fmdrop C N \<Longrightarrow> b = irred N C \<Longrightarrow>  N = fmupd C (N \<propto> C, b) aa\<close> for aa b
    using assms(1) fmdrop_eq_update_eq by blast
  have [simp]: \<open>fmupd C (D) aa = fmupd C (E) aa \<longleftrightarrow> D = E\<close> for aa D E
    apply auto
    by (metis fmupd_lookup option.sel)
  have [simp]: \<open>(\<forall>a. a) \<longleftrightarrow> False\<close>
    by blast
  define simp_work_around where \<open>simp_work_around unc b b' \<equiv> unc \<longrightarrow> N = b \<and> \<not>b'\<close> for unc b b'
  have simp_work_around_simp[simp]: \<open>simp_work_around True b b' \<longleftrightarrow> b = N \<and> \<not>b'\<close> for b b'
    unfolding simp_work_around_def by auto
    term  \<open>{(a, b). I a \<and> ?Q a (b) \<and>  (fst b \<longleftrightarrow>  ((snd o snd o snd o snd) a))}\<close>
  have hd_nth_take: \<open>length C > 0 \<Longrightarrow> [C!0] = take (Suc 0) C\<close> for C
    by (cases C; auto)
  show ?thesis
    unfolding simplify_clause_with_unit_alt_def simplify_clause_with_unit2_def
      Let_def H conc_fun_RES st simplify_clause_with_unit2_rel_def
    apply (rule ASSERT_leI)
    subgoal using assms by auto
    apply (refine_vcg WHILEIT_rule_stronger_inv_RES'[where I'=I and R = \<open>?R\<close> and
      H = \<open>{(a, b). I a \<and> ?Q a b \<and>  (fst (snd b) \<longleftrightarrow>  ((snd o snd o snd o snd) a))}\<close>])
    subgoal by auto
    subgoal by (auto simp: I_def)
    subgoal by (rule I0)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def intro: in_set_dropp_begin)
    subgoal by (auto simp: I_def split: if_splits)
    subgoal by (rule I_Suc)
    subgoal by (auto simp: I_def)
    subgoal for s
      apply (cases s)
      apply (clarsimp intro!: RETURN_SPEC_refine)
      apply (intro conjI)
      subgoal
        apply (intro impI)
        apply (clarsimp simp add: I_def fmdrop_fmupd_same)
        apply (auto simp add: I_def mset_remove_filtered
          dest: in_set_takeD)
        done
      subgoal
        by (intro impI)
         (auto simp add: I_def fmdrop_fmupd_same
          intro!: fmdrop_eq_update_eq')
      done
    subgoal
      unfolding I_def simp_work_around_def[symmetric]
      by simp
    subgoal
      unfolding I_def simp_work_around_def[symmetric]
      by simp
    subgoal
      unfolding I_def simp_work_around_def[symmetric]
      by clarsimp
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
      unfolding I_def simp_work_around_def[symmetric]
      apply (cases \<open>x2e \<or> x1b \<le> 1\<close>)
      apply (simp only: if_True split: )
      subgoal
        apply (simp add: hd_nth_take learned_clss_l_l_fmdrop_irrelev H5 H4 H9[of x2a] H11
            ;
          (subst (asm) eq_commute[of \<open>If _ (fmupd C (_, _) _) _\<close> x2a])?)
        apply (intro conjI impI allI)
        apply (simp add: hd_nth_take)
        apply (clarsimp simp only:)
        apply (simp add: )
        apply (clarsimp simp only:)
        apply (clarsimp simp only:)
        apply (simp add: )
        apply (metis length_0_conv)
        apply (clarsimp simp only:; fail)+
        apply (simp add: )
        apply (clarsimp simp only: if_True if_False H11 H8[of \<open>fmupd _ _ x1d\<close>])
        apply (clarsimp simp only: if_True if_False H11 H8[of \<open>fmupd _ _ x1d\<close>] refl
          split: if_splits)
          apply (metis (no_types, lifting) H8)
          apply (metis (no_types, lifting) H8)
        apply (clarsimp simp only: if_True if_False H11 H8[of x1d])
          apply (metis (no_types, lifting))
        apply (clarsimp simp only: if_True if_False H11 H8[of x1d])
        done
      apply (cases \<open>x1b = x1c \<and> \<not> x2e\<close>)
      subgoal
        using fmupd_same[of C x1d]
        apply (cases \<open>the (fmlookup x1d C)\<close>)
        apply (simp only: if_True if_False simp_thms mem_Collect_eq prod.case
          Let_def linorder_class.not_le[symmetric] simp_work_around_simp
          take_all[OF order.refl] fmupd_lookup refl if_True simp_thms
          option.sel fst_conv simp_work_around_simp eq_commute[of \<open>fmupd _ _ _\<close> N]
          eq_commute [of x2a N]
          fst_conv snd_conv)
        apply (intro conjI impI allI)
        apply (clarsimp simp :; fail)+
        done
     subgoal
        using fmupd_same[of C x1d]
        apply (cases \<open>the (fmlookup x1d C)\<close>)
        apply (cases \<open>irred x2a C\<close>)
        apply (simp_all only: if_True if_False simp_thms mem_Collect_eq prod.case
          Let_def linorder_class.not_le[symmetric] simp_work_around_simp
          take_all[OF order.refl] fmupd_lookup refl if_True simp_thms H4 H5
          option.sel fst_conv simp_work_around_simp eq_commute[of \<open>fmupd _ _ _\<close> x2a]
          eq_commute [of x2a N] H4 H5
          fst_conv snd_conv;
          intro conjI impI allI)
        apply (clarsimp simp :; fail)+
        apply (clarsimp simp add: eq_commute[of \<open>fmupd _ _ _\<close> x2a])
        apply (metis set_mset_mset union_iff)
        apply (clarsimp simp: H4 H5; fail)+
        done
      done
    done
qed


definition simplify_clause_with_unit_st2 :: \<open>nat \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>simplify_clause_with_unit_st2 =  (\<lambda>C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(simplify_clause_with_unit_st_wl_pre C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None);
    let S =  (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
    let E = mset (N\<^sub>0 \<propto> C);
    let irr = irred N\<^sub>0 C;
    (unc, N, L, b, i) \<leftarrow> simplify_clause_with_unit2 C M N\<^sub>0;
    ASSERT(dom_m N \<subseteq># dom_m N\<^sub>0);
      if unc then do {
      ASSERT(N = N\<^sub>0);
      let T = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
      RETURN T
    }
    else if b then do {
       let T = (M, N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NEk, UEk, NS, US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else if i = 1
    then do {
      ASSERT (undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S));
      M \<leftarrow> cons_trail_propagate_l L 0 M;
      let T = (M, N, D, NE, UE, (if irr then add_mset {#L#} else id) NEk, (if \<not>irr then add_mset {#L#} else id)UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
   }
    else if i = 0
    then do {
      let j = length M;
      let T = (M, N, Some {#}, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else do {
      let T = (M, N, D, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0));
      ASSERT (C \<in># dom_m N);
      RETURN T
    }
        })\<close>

lemma all_learned_all_lits_all_atms_st:
  \<open>set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S) \<Longrightarrow>
  set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S) \<Longrightarrow>
  set_mset (all_atms_st T) = set_mset (all_atms_st S)\<close>
  by (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms
    all_lits_st_init_learned
    atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset)

lemma simplify_clause_with_unit_st2_simplify_clause_with_unit_st:
  fixes S :: \<open>nat twl_st_wl\<close>
  assumes \<open>(C,C')\<in>Id\<close> \<open>(S,S')\<in>Id\<close>
  shows
    \<open>simplify_clause_with_unit_st2 C S \<le> \<Down>Id (simplify_clause_with_unit_st_wl C' S')\<close>
proof -
  show ?thesis
    using assms
    unfolding simplify_clause_with_unit_st2_def simplify_clause_with_unit_st_wl_def
      if_False Let_def cons_trail_propagate_l_def nres_monad3 bind_to_let_conv
    supply [[goals_limit=1]]
    apply (refine_rcg simplify_clause_with_unit2_simplify_clause_with_unit[unfolded simplify_clause_with_unit2_rel_def])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j
      x2j x1k x2k x1l x2l x1m x2m x1n _ _ _ _
      x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x x' x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y
      by (cases \<open>C' \<notin># dom_m x1y\<close>)
        (simp_all add: eq_commute[of \<open>remove1_mset _ _\<close> \<open>dom_m _\<close>])
    subgoal by auto
    subgoal
      by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case)
    subgoal by auto
    subgoal by auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (rule all_learned_all_lits_all_atms_st)
    subgoal by (clarsimp simp add: learned_clss_l_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      learned_clss_l_fmdrop_if)
    subgoal by (clarsimp simp add: ran_m_def dest!: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (simp flip: all_lits_of_all_atms_of add: all_atms_st_def all_lits_st_def)
    subgoal by auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (rule all_learned_all_lits_all_atms_st)
    subgoal by (clarsimp simp add: learned_clss_l_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      learned_clss_l_fmdrop_if)
    subgoal by (clarsimp simp add: ran_m_def dest!: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case) auto
    subgoal by (rule all_learned_all_lits_all_atms_st)
    subgoal by (clarsimp simp add: learned_clss_l_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      learned_clss_l_fmdrop_if)
    subgoal by (clarsimp simp add: ran_m_def dest!: multi_member_split)
    subgoal by auto
    subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case
      disj.left_neutral)
      subgoal by (clarsimp simp only: pair_in_Id_conv prod.inject mem_Collect_eq prod.case
        disj.left_neutral)
    subgoal by (rule all_learned_all_lits_all_atms_st)
    subgoal by (clarsimp simp add: learned_clss_l_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      learned_clss_l_fmdrop_if)
    subgoal by auto
    subgoal by auto
    done
qed

definition simplify_clauses_with_unit_st2 :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>  where
  \<open>simplify_clauses_with_unit_st2 S =
  do {
  ASSERT (simplify_clauses_with_unit_st_wl_pre S);
  xs \<leftarrow> SPEC(\<lambda>xs. finite xs);
  T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
  (xs)
  (\<lambda>S. get_conflict_wl S = None)
  (\<lambda>i S. if i \<in># dom_m (get_clauses_wl S)
            then simplify_clause_with_unit_st2 i S else RETURN S)
  S;
  ASSERT(set_mset (all_learned_lits_of_wl T) \<subseteq> set_mset (all_learned_lits_of_wl S));
  ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
  RETURN T
  }\<close>

lemma simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st:
  assumes \<open>(S,S')\<in>Id\<close>
  shows
    \<open>simplify_clauses_with_unit_st2 S \<le> \<Down>Id (simplify_clauses_with_unit_st_wl S')\<close>
proof -
  have inj: \<open>inj_on id x\<close> for x
    by auto
  show ?thesis
    using assms
    unfolding simplify_clauses_with_unit_st2_def simplify_clauses_with_unit_st_wl_def
    by (refine_vcg simplify_clause_with_unit_st2_simplify_clause_with_unit_st inj)
      auto
qed

definition isa_simplify_clause_with_unit2 where
  \<open>isa_simplify_clause_with_unit2 C M N = do {
     l \<leftarrow> mop_arena_length N C;
    ASSERT(l < length N \<and> l \<le> Suc (uint32_max div 2));
    (i, j, N::arena, is_true) \<leftarrow> WHILE\<^sub>T(\<lambda>(i, j, N::arena, b). \<not>b \<and> j < l)
    (\<lambda>(i, j, N, is_true). do {
      ASSERT(i \<le> j \<and> j < l);
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
   then do {
     ASSERT(mark_garbage_pre (N, C));
     RETURN (False, extra_information_mark_to_delete N C, L, is_true, i)}
   else if i = j then RETURN (True, N, L, is_true, i)
   else do {
      N \<leftarrow> mop_arena_shorten C i N;
      RETURN (False, N, L, is_true, i)}
    }\<close>
 
lemma simplify_clause_with_unit2_alt_def:
  \<open>simplify_clause_with_unit2 C M N\<^sub>0 = do {
      ASSERT(C \<in># dom_m N\<^sub>0);
      let l = length (N\<^sub>0 \<propto> C);
        (i, j, N, del, is_true) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, j, N, del, b). C \<in># dom_m N\<^esup>
        (\<lambda>(i, j, N, del, b). \<not>b \<and> j < l)
        (\<lambda>(i, j, N, del, is_true). do {
           ASSERT(i < length (N \<propto> C) \<and> j < length (N \<propto> C) \<and> C \<in># dom_m N \<and> i \<le> j);
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
    ASSERT (is_true \<or> j = length (N\<^sub>0 \<propto> C));
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (False, fmdrop C N, L, is_true, i)
    else if i=j \<and> \<not> is_true then RETURN (True, N, L, is_true, i)
      else do {
      let N = N(C \<hookrightarrow> (take i (N \<propto> C))) in RETURN (False, N, L, is_true, i)}
  }\<close>
   unfolding Let_def simplify_clause_with_unit2_def
   by (auto intro!: bind_cong[OF refl])

(*TODO: WTF*)
lemma normalize_down_return_spec: \<open>\<Down>A ((RETURN o f) c) = SPEC (\<lambda>a. (a, f c) \<in> {(a,b). (a,b) \<in> A \<and> b = f c})\<close>
  by (auto simp: conc_fun_RES RETURN_def)
(*TODO Move*)
lemma arena_length_le_length_arena:
  \<open>C' \<in># dom_m N \<Longrightarrow>
    valid_arena arena N vdom \<Longrightarrow>
    arena_length arena C' < length arena\<close>
  by (smt (verit, best) Nat.le_diff_conv2 STATUS_SHIFT_def Suc_le_lessD arena_lifting(10) arena_lifting(16) arena_lifting(4) diff_self_eq_0 le_trans less_Suc_eq not_less_eq not_less_eq_eq numeral_2_eq_2)

lemma simplify_clause_with_unit_st_wl_preD:
  assumes \<open>simplify_clause_with_unit_st_wl_pre C S\<close>
  shows
    simplify_clause_with_unit_st_wl_pre_all_init_atms_all_atms:
      \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close> and
    \<open>isasat_input_bounded (all_init_atms_st S) \<Longrightarrow> length (get_clauses_wl S \<propto> C) \<le> Suc (uint32_max div 2)\<close>
proof -
  obtain x xa where
    Sx: \<open>(S, x) \<in> state_wl_l None\<close> and
    C: \<open>C \<in># dom_m (get_clauses_l x)\<close> and
    \<open>count_decided (get_trail_l x) = 0\<close> and
    \<open>get_conflict_l x = None\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    \<open>twl_st_inv xa\<close> and
    \<open>valid_enqueued xa\<close> and
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (state\<^sub>W_of xa)\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of xa)\<close> and
    \<open>entailed_clss_inv (pstate\<^sub>W_of xa)\<close> and
    \<open>twl_st_exception_inv xa\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of xa)\<close> and
    \<open>psubsumed_invs (pstate\<^sub>W_of xa)\<close> and
    \<open>clauses0_inv (pstate\<^sub>W_of xa)\<close> and
    \<open>no_duplicate_queued xa\<close> and
    \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of xa). \<not> tautology s\<close> and
    \<open>distinct_queued xa\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of xa)\<close> and
    \<open>confl_cands_enqueued xa\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of xa)\<close> and
    \<open>propa_cands_enqueued xa\<close> and
    \<open>all_decomposition_implies_m (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of xa))
    (get_all_ann_decomposition (trail (state\<^sub>W_of xa)))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of xa)\<close> and
    \<open>get_conflict xa \<noteq> None \<longrightarrow> clauses_to_update xa = {#} \<and> literals_to_update xa = {#}\<close> and
    \<open>clauses_to_update_inv xa\<close> and
    \<open>past_invs xa\<close> and
    list: \<open>twl_list_invs x\<close>
    using assms
    unfolding simplify_clause_with_unit_st_wl_pre_def twl_struct_invs_def
      simplify_clause_with_unit_st_pre_def pcdcl_all_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      state\<^sub>W_of_def[symmetric] apply -
    by blast

  show H: \<open>set_mset (all_init_atms_st S) = set_mset (all_atms_st S)\<close>
    using Sx xxa alien
    unfolding all_init_atms_def all_init_atms_st_def all_atms_st_def all_init_lits_def
      all_lits_of_mm_union image_mset_union get_unit_clauses_wl_alt_def all_atms_def all_lits_def
      set_mset_union atm_of_all_lits_of_mm cdcl\<^sub>W_restart_mset.no_strange_atm_def
    apply (subst (2)all_clss_l_ran_m[symmetric])
    apply (subst all_clss_l_ran_m[symmetric])
    unfolding image_mset_union filter_union_mset atms_of_ms_union set_mset_union
    by auto
  have \<open>distinct_mset (mset (get_clauses_wl S \<propto> C))\<close>
    using Sx xxa dist C
    by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def ran_m_def conj_disj_distribR image_Un
      Collect_disj_eq Collect_conv_if split: if_splits
      dest!: multi_member_split)
  moreover have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (all_init_atms_st S) (mset (get_clauses_wl S \<propto> C))\<close>
    using C Sx xxa unfolding H  literals_are_in_\<L>\<^sub>i\<^sub>n_def \<L>\<^sub>a\<^sub>l\<^sub>l_cong[OF H]
    by (auto simp:all_atms_st_def ran_m_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
      all_lits_of_mm_add_mset all_lits_def
      all_atms_def all_init_lits_def dest!: multi_member_split
      simp del: all_atms_def[symmetric])
  moreover have \<open>\<not>tautology (mset (get_clauses_wl S \<propto> C))\<close>
    using list C Sx unfolding twl_list_invs_def
    by auto
  ultimately show \<open>length (get_clauses_wl S \<propto> C) \<le> Suc (uint32_max div 2)\<close>
    if \<open>isasat_input_bounded (all_init_atms_st S)\<close>
    using simple_clss_size_upper_div2[OF that, of \<open>mset (get_clauses_wl S \<propto> C)\<close>] by auto
qed

lemma isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit:
  assumes \<open>valid_arena arena N vdom\<close> and
    trail: \<open>(M, M') \<in> trail_pol \<A>\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    C: \<open>(C,C')\<in>Id\<close> and
    le: \<open>length (N \<propto> C) \<le> Suc (uint32_max div 2)\<close>
  shows \<open>isa_simplify_clause_with_unit2 C M arena \<le> \<Down>
    (bool_rel \<times>\<^sub>r {(arena', N). valid_arena arena' N vdom \<and> length arena' = length arena} \<times>\<^sub>r
    Id \<times>\<^sub>r bool_rel \<times>\<^sub>r nat_rel)
    (simplify_clause_with_unit2 C' M' N)\<close>
proof -
  have C: \<open>C'=C\<close>
    using C by auto

  have [refine0]: \<open>C \<in># dom_m N \<Longrightarrow>
  ((0, 0, arena, False), 0, 0, N, {#}, False) \<in> {((i, j, N, is_true),
    (i', j', N', del', is_true')).
    ((i, j, N, is_true), (i', j', N', is_true')) \<in>
    nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r {(arena', N). valid_arena arena' N vdom \<and> length arena' = length arena \<and> C \<in># dom_m N} \<times>\<^sub>r
    bool_rel}\<close>
    using assms by auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding isa_simplify_clause_with_unit2_def simplify_clause_with_unit2_alt_def
      mop_polarity_pol_def nres_monad3 C
    apply (refine_rcg mop_arena_lit[where vdom=vdom]
      polarity_pol_pre[OF trail]
      polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp,
        THEN fref_to_Down_unRET_uncurry]
      mop_arena_shorten_spec[where vdom=vdom]
      mop_arena_length[THEN fref_to_Down_curry, of N C _ _ vdom, unfolded normalize_down_return_spec]
     )
    subgoal using assms by (auto simp add: arena_lifting)
    subgoal using assms by (auto simp add: arena_lifting)
    subgoal
      using assms by (auto simp add: arena_lifting arena_length_le_length_arena)

    subgoal using le by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
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
    subgoal for _ x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
      using arena_lifting(4,19)[of x1f x1b vdom C] by auto
    subgoal by auto
    subgoal by (auto simp: mark_garbage_pre_def arena_is_valid_clause_idx_def)
    subgoal by (auto intro!: valid_arena_extra_information_mark_to_delete')
    subgoal by auto
    subgoal by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition set_conflict_to_false :: \<open>conflict_option_rel \<Rightarrow> conflict_option_rel\<close> where
  \<open>set_conflict_to_false = (\<lambda>(b, n, xs). (False, 0, xs))\<close>

text \<open>We butcher our statistics here, but the clauses are deleted later anyway.\<close>
definition isa_simplify_clause_with_unit_st2 :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_simplify_clause_with_unit_st2 =  (\<lambda>C S. do {
   let lcount = get_learned_count S; let N = get_clauses_wl_heur S; let M = get_trail_wl_heur S;
   E \<leftarrow> mop_arena_status N C;
   ASSERT(E = LEARNED \<longrightarrow> 1 \<le> clss_size_lcount lcount);
   (unc, N, L, b, i) \<leftarrow> isa_simplify_clause_with_unit2 C M N;
   ASSERT (length N \<le> length (get_clauses_wl_heur S));
   if unc then RETURN (set_clauses_wl_heur N S)
   else if b then
   RETURN  (set_clauses_wl_heur N
     (set_stats_wl_heur (if E=LEARNED then (get_stats_heur S) else (decr_irred_clss (get_stats_heur S)))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount (lcount) else lcount)
     S)))
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
     RETURN (set_clauses_wl_heur N
     (set_trail_wl_heur M
     (set_stats_wl_heur (if E=LEARNED then incr_uset (get_stats_heur S) else incr_uset (decr_irred_clss (get_stats_heur S)))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUEk lcount) else lcount)
     S)))) }
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
     RETURN (set_clauses_wl_heur N
     (set_conflict_wl_heur (set_conflict_to_false (get_conflict_wl_heur S))
     (set_count_max_wl_heur 0
     (set_literals_to_update_wl_heur j
     (set_stats_wl_heur (if E=LEARNED then get_stats_heur S else decr_irred_clss (get_stats_heur S))
     (set_learned_count_wl_heur (if E = LEARNED then clss_size_decr_lcount lcount else lcount)
     S))))))
   }
   else do {
       let S = (set_clauses_wl_heur N S);
       _ \<leftarrow> log_new_clause_heur S C;
       RETURN S
     }
   })\<close>

lemma literals_are_in_mm_clauses:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (all_atms_st T) (mset `# ran_mf (get_clauses_wl T))\<close>
  unfolding all_atms_st_def all_atms_def all_lits_def
  by (auto simp: all_lits_of_mm_union
    literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)

(* TODO Move to IsaSAT_Arena *)
lemma mop_arena_status:
  assumes \<open>C \<in># dom_m N\<close> and \<open>(C,C')\<in>nat_rel\<close>
    \<open>valid_arena arena N vdom\<close>
  shows
    \<open>mop_arena_status arena C
    \<le> SPEC
    (\<lambda>c. (c, irred N C')
    \<in> {(a,b). (a = IRRED \<longleftrightarrow> b) \<and> (a = LEARNED \<longleftrightarrow> \<not>b) \<and>  (irred N C' = b)})\<close>
   using assms unfolding mop_arena_status_def
   by (auto intro!: ASSERT_leI simp: arena_is_valid_clause_vdom_def
     arena_lifting)

lemma twl_st_heur_restart_alt_def[unfolded Let_def]:
  \<open>twl_st_heur_restart =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    let \<A> = all_init_atms_st (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) in
    (M', M) \<in> trail_pol \<A>  \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel \<A> \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A> ) \<and>
    vm \<in> isa_vmtf \<A>  M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty \<A>  cach \<and>
    out_learned M D outl \<and>
    clss_size_corr_restart N NE {#} NEk UEk NS {#} N0 {#} lcount \<and>
    vdom_m \<A>  W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded \<A>  \<and>
    isasat_input_nempty \<A>  \<and>
    old_arena = [] \<and>
    heuristic_rel \<A>  heur
    }\<close>
    unfolding twl_st_heur_restart_def all_init_atms_st_def Let_def by auto


(*TODO Move*)
lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_cong:
  \<open>set_mset A = set_mset B \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_mm A = literals_are_in_\<L>\<^sub>i\<^sub>n_mm B\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def \<L>\<^sub>a\<^sub>l\<^sub>l_cong by force

lemma aivdom_inv_mono:
  \<open>B \<subseteq># A \<Longrightarrow> aivdom_inv (v, x1y, x2aa, tvdom) A \<Longrightarrow> aivdom_inv (v, x1y, x2aa, tvdom) B\<close>
  using distinct_mset_mono[of B A]
  by (auto simp: aivdom_inv_alt_def)

lemma aivdom_inv_dec_mono:
  \<open>B \<subseteq># A \<Longrightarrow> aivdom_inv_dec vdom A \<Longrightarrow> aivdom_inv_dec vdom B\<close>
  using aivdom_inv_mono[of B A \<open>get_vdom_aivdom vdom\<close> \<open>get_avdom_aivdom vdom\<close> \<open>get_ivdom_aivdom vdom\<close>
    \<open>get_tvdom_aivdom vdom\<close>]
  by (cases vdom) (auto simp: aivdom_inv_dec_def)

lemma simplify_clause_with_unit_st2_alt_def:
  \<open>simplify_clause_with_unit_st2 =  (\<lambda>C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). do {
    ASSERT(simplify_clause_with_unit_st_wl_pre C (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W));
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None);
    let S =  (M, N\<^sub>0, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
    let E = mset (N\<^sub>0 \<propto> C);
    let irr = irred N\<^sub>0 C;
    (unc, N, L, b, i) \<leftarrow> simplify_clause_with_unit2 C M N\<^sub>0;
    ASSERT(dom_m N \<subseteq># dom_m N\<^sub>0);
      if unc then do {
      ASSERT(N = N\<^sub>0);
      let T = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W);
      RETURN T
    }
    else if b then do {
       let T = (M, N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NEk, UEk, NS, US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else if i = 1
    then do {
      ASSERT (undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S));
      M \<leftarrow> cons_trail_propagate_l L 0 M;
      let T = (M, N, D, NE, UE, (if irr then add_mset {#L#} else id) NEk, (if \<not>irr then add_mset {#L#} else id)UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
   }
    else if i = 0
    then do {
      let j = length M;
      let T = (M, N, Some {#}, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else do {
      let T = (M, N, D, NE, UE, NEk, UEk, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0));
      ASSERT (C \<in># dom_m N);
      let _ = log_clause T C;
      RETURN T
    }
        })\<close>
  by (auto simp: simplify_clause_with_unit_st2_def log_clause_def intro!: ext Let_def cong: if_cong)

lemma isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2:
  assumes \<open>(S, S') \<in> {(a,b). (a,b) \<in> twl_st_heur_restart \<and> get_avdom a = u\<and> get_vdom a = v\<and>
    get_ivdom a = x \<and>length (get_clauses_wl_heur a) = r \<and>
    learned_clss_count a \<le> w \<and> get_vmtf_heur a = vm  \<and>
    length (get_watched_wl_heur a) = lw}\<close>
    \<open>(C,C')\<in> nat_rel\<close>
  shows \<open>isa_simplify_clause_with_unit_st2 C S \<le>
    \<Down>{(a,b). (a,b) \<in> twl_st_heur_restart \<and> get_avdom a = u\<and> get_vdom a = v\<and> get_ivdom a = x \<and>
    length (get_clauses_wl_heur a) = r\<and>
    learned_clss_count a \<le> w \<and> get_vmtf_heur a = vm \<and>
    learned_clss_count a \<le> learned_clss_count S \<and>
    length (get_watched_wl_heur a) = lw} (simplify_clause_with_unit_st2 C' S')\<close> (is \<open>_ \<le> \<Down>?A _\<close>)
proof -
  have H: \<open>A = B \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B\<close> for A B x
    by auto
  have H': \<open>A = B \<Longrightarrow> A x \<Longrightarrow> B x\<close> for A B x
    by auto
  have H'': \<open>A = B \<Longrightarrow> A \<subseteq> c \<Longrightarrow> B \<subseteq> c\<close> for A B c
    by auto

  have vdom_m_cong2: \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> vdom_m \<A> W N \<subseteq> vd \<Longrightarrow> dom_m N' \<subseteq># dom_m N \<Longrightarrow>
    vdom_m \<B> W N' \<subseteq> vd\<close>
    for \<A> W N N' vd \<B>
    by (subst vdom_m_cong[of \<B> \<A>])
      (auto simp: vdom_m_def)
  note cong =  trail_pol_cong heuristic_rel_cong
    option_lookup_clause_rel_cong isa_vmtf_cong
    vdom_m_cong[THEN H] isasat_input_nempty_cong[THEN iffD1]
    isasat_input_bounded_cong[THEN iffD1]
    cach_refinement_empty_cong[THEN H']
    phase_saving_cong[THEN H']
    \<L>\<^sub>a\<^sub>l\<^sub>l_cong[THEN H]
    D\<^sub>0_cong[THEN H]
    D\<^sub>0_cong[OF sym]
    vdom_m_cong[THEN H'']
    vdom_m_cong2
  have set_conflict_to_false: \<open>(a, None) \<in> option_lookup_clause_rel \<A> \<Longrightarrow>
    (set_conflict_to_false a, Some {#}) \<in> option_lookup_clause_rel \<A>\<close> for a \<A>
    by (auto simp: option_lookup_clause_rel_def set_conflict_to_false_def
      lookup_clause_rel_def)
  have outl: \<open>out_learned x1 None x1s \<Longrightarrow> out_learned x1 (Some {#}) (x1s)\<close>
    \<open>0 \<in> counts_maximum_level x1 (Some {#})\<close> for x1 x1s
    by (cases x1s, auto simp: out_learned_def counts_maximum_level_def)
  have all_init_lits_of_wl:
    \<open>set_mset (all_init_lits_of_wl a) = set_mset (all_init_lits_of_wl b) \<longleftrightarrow>
    set_mset (all_init_atms_st a) = set_mset (all_init_atms_st b)\<close> for a b
    by (metis \<L>\<^sub>a\<^sub>l\<^sub>l_all_init_atms(2) \<L>\<^sub>a\<^sub>l\<^sub>l_cong atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n atms_of_cong_set_mset)
  have log_clause[refine0]: \<open>y' \<in># dom_m (get_clauses_wl x') \<Longrightarrow> (x, x')\<in> ?A \<Longrightarrow> (y,y')\<in> nat_rel \<Longrightarrow>
    log_new_clause_heur x y \<le> SPEC(\<lambda>c. (c, log_clause x' y') \<in> unit_rel)\<close> for x x' y y'
    unfolding log_new_clause_heur_alt_def
    apply (rule log_clause_heur_log_clause2_ana[THEN order_trans])
    apply (auto simp add: twl_st_heur_restart_ana_def)
  by (rule log_clause2_log_clause[THEN fref_to_Down_curry, unfolded prod.simps, THEN order_trans])
   auto

  note accessors_def = get_trail_wl.simps get_clauses_wl.simps get_conflict_wl.simps literals_to_update_wl.simps
        get_watched_wl.simps get_init_clauses0_wl.simps get_learned_clauses0_wl.simps
        get_subsumed_init_clauses_wl.simps get_subsumed_learned_clauses_wl.simps
        get_kept_unit_init_clss_wl.simps get_kept_unit_learned_clss_wl.simps isasat_state_simp
        get_unkept_unit_init_clss_wl.simps get_unkept_unit_learned_clss_wl.simps
  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding isa_simplify_clause_with_unit_st2_def
      simplify_clause_with_unit_st2_alt_def Let_def[of "(_,_)"] Let_def[of \<open>mset _\<close>]
      all_init_lits_of_wl
    apply (rewrite at \<open>let _ = set_clauses_wl_heur _ _ in _\<close> Let_def)
    apply (refine_rcg isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit[where
      vdom=\<open>set (get_vdom S)\<close> and \<A> = \<open>all_init_atms_st S'\<close>]
      mop_arena_status[where vdom = \<open>set (get_vdom S)\<close>]
      cons_trail_Propagated_tr2[where \<A> = \<open>all_init_atms_st S'\<close>]
      mop_isa_length_trail_length_u[of \<open>all_init_atms_st (S')\<close>, THEN fref_to_Down_Id_keep,
      unfolded length_uint32_nat_def comp_def])
    subgoal by auto
    subgoal by (auto simp: twl_st_heur_restart_def)
    subgoal by (auto simp: twl_st_heur_restart_def clss_size_corr_def ran_m_def
        clss_size_def
      dest!: multi_member_split clss_size_corr_restart_rew)
    subgoal
      by (auto simp: twl_st_heur_restart_def)
    subgoal
      by (auto simp: twl_st_heur_restart_def all_init_atms_st_def)
    subgoal
      using literals_are_in_mm_clauses[of S']
        simplify_clause_with_unit_st_wl_pre_all_init_atms_all_atms[of C' S',
    THEN literals_are_in_\<L>\<^sub>i\<^sub>n_mm_cong]
      by (auto simp: twl_st_heur_restart_def)
    subgoal
      by (drule simplify_clause_with_unit_st_wl_preD(2)[of C'])
       (auto dest!: simp: twl_st_heur_restart_def all_init_atms_st_def
        simp del: isasat_input_bounded_def)
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_restart_def learned_clss_count_def)
    subgoal
      by (auto simp: twl_st_heur_restart_def)
    subgoal
      by (auto simp: twl_st_heur_restart_def)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n
      x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u
      by (clarsimp simp only: twl_st_heur_restart_alt_def in_pair_collect_simp prod.simps
         prod_rel_iff TrueI refl
        cong[of \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
        \<open>all_init_atms_st (_, _, _, (If _ _ _) _, _)\<close>] clss_size_corr_restart_def isasat_state_simp
        clss_size_def clss_size_incr_lcountUE_def learned_clss_count_def aivdom_inv_dec_mono
        clss_size_decr_lcount_def accessors_def)
       (auto split: if_splits intro: aivdom_inv_dec_mono simp:
        clss_size_decr_lcount_def clss_size_lcount_def clss_size_lcountUS_def
        clss_size_lcountU0_def clss_size_lcountUE_def clss_size_lcountUEk_def)
   subgoal by simp
   subgoal by (auto simp: twl_st_heur_restart_def all_init_atms_st_def)
   subgoal
     using simplify_clause_with_unit_st_wl_pre_all_init_atms_all_atms[of C' S', THEN \<L>\<^sub>a\<^sub>l\<^sub>l_cong]
     by auto
   subgoal by (auto simp: DECISION_REASON_def)
   subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v
     by (clarsimp simp only: twl_st_heur_restart_alt_def in_pair_collect_simp prod.simps
         prod_rel_iff TrueI refl accessors_def
       cong[of \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
       \<open>all_init_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2 clss_size_corr_restart_def
        clss_size_def clss_size_incr_lcountUEk_def learned_clss_count_def aivdom_inv_dec_mono
        clss_size_decr_lcount_def)
       (auto split: if_splits intro: aivdom_inv_dec_mono simp:
        clss_size_decr_lcount_def clss_size_lcount_def clss_size_lcountUS_def
        clss_size_lcountU0_def clss_size_lcountUE_def clss_size_lcountUEk_def)
   subgoal by simp
   subgoal by simp
   subgoal by (auto simp add: twl_st_heur_restart_def all_init_atms_st_def)
   subgoal  for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u
     by (clarsimp simp only: twl_st_heur_restart_alt_def in_pair_collect_simp prod.simps
       isasat_state_simp prod_rel_iff TrueI refl accessors_def
       cong[of \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
       \<open>all_init_atms_st (_, _, _, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def
       clss_size_decr_lcount_def clss_size_corr_restart_def
       option_lookup_clause_rel_cong[of
       \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
       \<open>all_init_atms_st (_, _, _, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false aivdom_inv_dec_mono
        clss_size_def clss_size_incr_lcountUE_def learned_clss_count_def
        clss_size_decr_lcount_def)
       (auto split: if_splits simp:
        clss_size_decr_lcount_def clss_size_lcount_def clss_size_lcountUS_def
       clss_size_lcountU0_def clss_size_lcountUE_def clss_size_lcountUEk_def)
   subgoal by simp
   subgoal state_conv for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u
     apply (clarsimp simp only: twl_st_heur_restart_alt_def in_pair_collect_simp prod.simps
       prod_rel_iff TrueI refl accessors_def isasat_state_simp
       cong[of \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
       \<open>all_init_atms_st (_, _, _, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def aivdom_inv_dec_mono
       clss_size_decr_lcount_def clss_size_corr_restart_def
       option_lookup_clause_rel_cong[of \<open>all_init_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
         x1i, x1j, uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev x1)), x2k)\<close>
       \<open>all_init_atms_st (_, _, _, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false)
     apply (auto split: if_splits)
     done
   subgoal premises p
       by (rule state_conv[OF p(1-43)])
   done
qed

definition isa_simplify_clauses_with_unit_st2 :: \<open>isasat \<Rightarrow> isasat nres\<close>  where
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
     xs \<leftarrow> RETURN (get_avdom S @ get_ivdom S);
    ASSERT(length xs \<le> length (get_vdom S) \<and> length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
           ASSERT((i < length (get_avdom T) \<longrightarrow> access_avdom_at_pre T i) \<and>
           (i \<ge> length (get_avdom T) \<longrightarrow> access_ivdom_at_pre T (i - length_avdom S)) \<and>
           length_avdom T = length_avdom S \<and>
           length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
            learned_clss_count T \<le> learned_clss_count S);
          let C = (if i < length (get_avdom S) then access_avdom_at T i else access_ivdom_at T (i - length_avdom S));
          E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
          if E \<noteq> DELETED then do {
          T \<leftarrow> isa_simplify_clause_with_unit_st2 C T;
          ASSERT(i < length xs);
          RETURN (i+1, T)
        }
        else do {ASSERT(i < length xs); RETURN (i+1,T)}
      })
     (0, S);
    RETURN (reset_units_since_last_GC_st T)
  }\<close>


lemma learned_clss_count_reset_units_since_last_GC_st[simp]:
  \<open>learned_clss_count (reset_units_since_last_GC_st T) =
  learned_clss_count T\<close>
  \<open>(reset_units_since_last_GC_st T, Ta) \<in> twl_st_heur_restart \<longleftrightarrow>
  (T, Ta) \<in> twl_st_heur_restart\<close>
  \<open>get_clauses_wl_heur (reset_units_since_last_GC_st T) = get_clauses_wl_heur T\<close>
  by (cases Ta; auto simp: reset_units_since_last_GC_st_def twl_st_heur_restart_def; fail)+

lemma isa_simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st2:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_simplify_clauses_with_unit_st2 S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (simplify_clauses_with_unit_st2 S')\<close>
proof -
  have isa_simplify_clauses_with_unit_st2_def: \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    xs \<leftarrow> RETURN (get_avdom S @ get_ivdom S);
    ASSERT(length xs \<le> length (get_vdom S) \<and> length (get_vdom S) \<le> length (get_clauses_wl_heur S));
    T \<leftarrow> do {
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
      (T) \<leftarrow>
        do {
           ASSERT((i < length (get_avdom T) \<longrightarrow> access_avdom_at_pre T i) \<and>
             (i \<ge> length (get_avdom T) \<longrightarrow> access_ivdom_at_pre T (i - length_avdom S)) \<and>
             length_avdom T = length_avdom S \<and>
             length (get_clauses_wl_heur T) = length (get_clauses_wl_heur S) \<and>
            learned_clss_count T \<le> learned_clss_count S);
           C \<leftarrow> RETURN (if i < length (get_avdom S) then access_avdom_at T i else access_ivdom_at T (i - length_avdom S));
           E \<leftarrow> mop_arena_status (get_clauses_wl_heur T) C;
          if E \<noteq> DELETED then do {
            isa_simplify_clause_with_unit_st2 C T
         }
         else RETURN (T)
            };
     ASSERT(i < length xs);
     RETURN (i+1, T)})
     (0, S);
    RETURN T
    };
    RETURN (reset_units_since_last_GC_st T)
    }\<close>
    unfolding isa_simplify_clauses_with_unit_st2_def Let_def
    by (auto simp: intro!: bind_cong[OF refl] cong: if_cong)
  have simplify_clauses_with_unit_st2_def:
      \<open>simplify_clauses_with_unit_st2 S =
      do {
        ASSERT (simplify_clauses_with_unit_st_wl_pre S);
        xs \<leftarrow> SPEC(\<lambda>xs. finite xs);
        T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
        (xs)
        (\<lambda>S. get_conflict_wl S = None)
          (\<lambda>i S. let _ =i; b = i \<in># dom_m (get_clauses_wl S) in
          if b then simplify_clause_with_unit_st2 i S else RETURN S)
        S;
        ASSERT(set_mset (all_learned_lits_of_wl T) \<subseteq> set_mset (all_learned_lits_of_wl S));
        ASSERT(set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
        RETURN T
      }\<close> for S
    unfolding simplify_clauses_with_unit_st2_def by (auto simp: Let_def)
  have dist_vdom: \<open>distinct (get_vdom S)\<close> and
      valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl S') (set (get_vdom S))\<close>
    using assms by (auto simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def aivdom_inv_dec_alt_def)


  have vdom_incl: \<open>set (get_vdom S) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur S)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have le_vdom_arena: \<open>length (get_vdom S) \<le> length (get_clauses_wl_heur S)\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)

  have [refine]: \<open>RETURN (get_avdom S@ get_ivdom S) \<le> \<Down> {(xs, a). a = set xs \<and> distinct xs \<and> set xs \<subseteq> set (get_vdom S) \<and>
       xs = get_avdom S@ get_ivdom S} (SPEC (\<lambda>xs. finite xs))\<close>
    (is \<open>_ \<le> \<Down>?A _\<close>)
    using assms distinct_mset_mono[of \<open>mset (get_avdom S)\<close> \<open>mset (get_vdom S)\<close>]
    distinct_mset_mono[of \<open>mset (get_ivdom S)\<close> \<open>mset (get_vdom S)\<close>] apply -
    by (rule RETURN_RES_refine)
      (auto intro!:  simp: twl_st_heur_restart_def twl_st_heur_restart_ana_def aivdom_inv_dec_alt_def)
  let ?R = \<open>{(a, b). (a, b) \<in> twl_st_heur_restart \<and> get_avdom a = get_avdom S \<and> get_vdom a = get_vdom S\<and>
     get_ivdom a = get_ivdom S \<and>
    length (get_clauses_wl_heur a) = r \<and> learned_clss_count a \<le> u \<and>
            learned_clss_count a \<le> learned_clss_count S}\<close>
   have [refine]: \<open>(xs, xsa) \<in> ?A \<Longrightarrow>
      xsa \<in> {xs:: nat set. finite xs} \<Longrightarrow>
     ([0..<length xs], xsa) \<in> \<langle>{(i, a). xs ! i =a \<and> i < length xs}\<rangle>list_set_rel\<close>
     (is \<open>_ \<Longrightarrow> _ \<Longrightarrow> _ \<in> \<langle>?B\<rangle>list_set_rel\<close>)  for xs xsa
      by (auto simp: list_set_rel_def br_def
        intro!: relcompI[of _ xs])
       (auto simp: list_rel_def intro!: list_all2_all_nthI)

   have H: \<open>(xi, x) \<in> ?B xs \<Longrightarrow>
    (xi, x) \<in> {(i, a). xs ! i = a}\<close> for xi x xs
     by auto
  have H2: \<open>(si, s) \<in> ?R \<Longrightarrow>
    valid_arena (get_clauses_wl_heur si) (get_clauses_wl s) (set (get_vdom S))\<close> for si s
    by (auto simp: twl_st_heur_restart_def)
  have H3: \<open>(if xi < length (get_avdom S) then access_avdom_at si xi else access_ivdom_at si (xi - length_avdom S), x)
   \<in> {(C,C'). (C,C')\<in> nat_rel \<and> C \<in> set (get_vdom S)}\<close> (is \<open>_ \<in> ?access\<close>)
     if 
       \<open>(xs, xsa)
     \<in> {(xs, a). a = set xs \<and> distinct xs \<and> set xs \<subseteq> set (get_vdom S) \<and> xs = get_avdom S @ get_ivdom S}\<close> and
       \<open>(xi, x) \<in> {(i, a). xs ! i = a \<and> i < length xs}\<close> and
       \<open>(si, s) \<in> ?R\<close>
     for xs xsa x xi s si
     using that by (auto simp: access_ivdom_at_def access_avdom_at_def nth_append length_avdom_def)
  have H5: \<open>(s,si)\<in> ?R \<Longrightarrow> (xi, x) \<in> ?B xs \<Longrightarrow> (xs, xsa) \<in> ?A \<Longrightarrow> (C,C') \<in> ?access \<Longrightarrow>
    (xa, C \<in># dom_m (get_clauses_wl si))
    \<in> {(a, b).
    (b \<longrightarrow>
     (a = IRRED) = irred (get_clauses_wl si) (C) \<and>
     (a = LEARNED) = (\<not> irred (get_clauses_wl si) C)) \<and>
    (a = DELETED) = (\<not> b)} \<Longrightarrow>
    (xa, C' \<in># dom_m (get_clauses_wl si)) \<in> {(a, b).
    (b \<longrightarrow>
     (a = IRRED) = irred (get_clauses_wl si) C' \<and>
     (a = LEARNED) = (\<not> irred (get_clauses_wl si) C')) \<and>
    (a = DELETED) = (\<not> b)}\<close> for xi xs x s xa si xsa C C'
    by (auto simp: access_avdom_at_def)
  have H4: \<open>(C,C')\<in>?access \<Longrightarrow> (C,C')\<in> nat_rel\<close> for C C' by auto
  show ?thesis
    unfolding isa_simplify_clauses_with_unit_st2_def simplify_clauses_with_unit_st2_def
      nfoldli_upt_by_while[symmetric]
    unfolding nres_monad3
    apply (refine_vcg
      LFOci_refine[where R= ?R]
      mop_arena_status2[where vdom = \<open>set (get_vdom S)\<close>])
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def twl_st_heur_restart_def card_Un_Int
         aivdom_inv_dec_alt_def
      simp flip: distinct_card intro!: card_mono)
    subgoal using le_vdom_arena by auto
    subgoal
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_restart[THEN fref_to_Down_unRET_Id])
        (auto simp: get_conflict_wl_is_None_def)
    subgoal by (auto simp: access_avdom_at_pre_def)
    subgoal by (auto simp: access_ivdom_at_pre_def length_avdom_def less_diff_conv2)
    subgoal by (auto simp: length_avdom_def)
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by auto
    apply (rule H3; assumption)
    apply (rule H4; assumption)
    subgoal by auto
    apply (rule H2; assumption)
    apply (rule H5; assumption)
    subgoal by auto
    apply (rule isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2[where
      u = \<open>(get_avdom S)\<close> and v = \<open>(get_vdom S)\<close> and x = \<open>(get_ivdom S)\<close> and r=r, THEN order_trans]; assumption?)
    apply (auto; fail)[]
    apply (auto; fail)[]
    subgoal
      by (clarsimp intro!: conc_fun_R_mono)
   subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
   subgoal by (auto simp: twl_st_heur_restart_ana_def reset_units_since_last_GC_def)
   done
qed

definition simplify_clauses_with_units_st_wl2 :: \<open>_\<close> where
  \<open>simplify_clauses_with_units_st_wl2 S = do {
  b \<leftarrow> SPEC(\<lambda>b::bool. b \<longrightarrow> get_conflict_wl S =None);
  if b then simplify_clauses_with_unit_st2 S else RETURN S
  }\<close>

lemma simplify_clauses_with_units_st_wl2_simplify_clauses_with_units_st_wl:
  \<open>(S, S') \<in> Id \<Longrightarrow> simplify_clauses_with_units_st_wl2 S \<le> \<Down>Id (simplify_clauses_with_units_st_wl S)\<close>
  unfolding simplify_clauses_with_units_st_wl2_def simplify_clauses_with_units_st_wl_def
  by (refine_vcg simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st) auto

definition isa_simplify_clauses_with_units_st_wl2 :: \<open>_\<close> where
  \<open>isa_simplify_clauses_with_units_st_wl2 S = do {
  b \<leftarrow> RETURN (get_conflict_wl_is_None_heur S \<and> units_since_last_GC_st S > 0);
  if b then isa_simplify_clauses_with_unit_st2 S else RETURN S
  }\<close>

lemma isa_simplify_clauses_with_units_st2_simplify_clauses_with_units_st2:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_simplify_clauses_with_units_st_wl2 S \<le>
    \<Down>(twl_st_heur_restart_ana' r u) (simplify_clauses_with_units_st_wl2 S')\<close>
  unfolding isa_simplify_clauses_with_units_st_wl2_def simplify_clauses_with_units_st_wl2_def
  by (refine_vcg isa_simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st2)
   (use assms in \<open>auto simp: get_conflict_wl_is_None_def
      get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id]\<close>)

end