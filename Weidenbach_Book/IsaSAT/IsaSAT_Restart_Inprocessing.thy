(*TODO Rename to IsaSAT_Inprocessing*)
theory IsaSAT_Restart_Inprocessing
  imports IsaSAT_Setup
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
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
    ASSERT(is_true \<or> j = l);
    let L = N \<propto> C ! 0;
    if is_true \<or> i \<le> 1
    then RETURN (False, fmdrop C N, L, is_true, i)
    else if i = j \<and> \<not>is_true then RETURN (True, N, L, is_true, i)
    else do {
      RETURN (False, N(C \<hookrightarrow> (take i (N \<propto> C))), L, is_true, i)
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
       (unc \<longrightarrow> N = N'));
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

  term \<open>?P C M N (unc, b, N'')\<close>
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
    apply (cases \<open>C \<in># dom_m x2c\<close>)
    apply (auto 6 3 dest!: multi_member_split simp: ran_m_def
      intro: filter_mset_cong2 image_mset_cong2
      intro: multiset.map_cong multiset.map_cong0
      intro!: arg_cong[of _ _ size])
    by (smt (verit, best) multiset.map_cong)
  have H6: \<open>\<not>irred x2c C \<Longrightarrow> C \<in># dom_m x2c \<Longrightarrow>
    size (learned_clss_l (fmupd C (x, False) x2c)) =
    (size (learned_clss_l x2c))\<close> for x x2c
    using distinct_mset_dom[of x2c]
    apply (cases \<open>C \<in># dom_m x2c\<close>)
    apply (auto 6 3 dest!: multi_member_split simp: ran_m_def
      intro: filter_mset_cong2 image_mset_cong2
      intro: multiset.map_cong multiset.map_cong0
      intro: arg_cong[of _ _ size])
    by (smt (verit, best) multiset.map_cong)
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
  define simp_work_around where \<open>simp_work_around unc b \<equiv> unc \<longrightarrow> N = b\<close> for unc b
  have simp_work_around_simp[simp]: \<open>simp_work_around True b \<longleftrightarrow> b = N\<close> for b
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
  \<open>simplify_clause_with_unit_st2 =  (\<lambda>C (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, W). do {
    ASSERT (C \<in># dom_m N\<^sub>0 \<and> count_decided M = 0 \<and> D = None);
    let S =  (M, N\<^sub>0, D, NE, UE, NS, US, N0, U0, Q, W);
    let E = mset (N\<^sub>0 \<propto> C);
    let irr = irred N\<^sub>0 C;
    (unc, N, L, b, i) \<leftarrow> simplify_clause_with_unit2 C M N\<^sub>0;
    ASSERT(dom_m N \<subseteq># dom_m N\<^sub>0);
      if unc then do {
      ASSERT(N = N\<^sub>0);
      let T = (M, N, D, NE, UE, NS, US, N0, U0, Q, W);
      RETURN T
    }
    else if b then do {
       let T = (M, N, D, (if irr then add_mset E else id) NE, (if \<not>irr then add_mset E else id) UE, NS, US, N0, U0, Q, W);
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
      let T = (M, N, D, (if irr then add_mset {#L#} else id) NE, (if \<not>irr then add_mset {#L#} else id)UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id)US, N0, U0, add_mset (-L) Q, W);
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
      let T = (M, N, Some {#}, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, (if irr then add_mset {#} else id) N0, (if \<not>irr then add_mset {#} else id)U0, {#}, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0) - (if irr then 0 else 1));
      ASSERT(\<not>irr \<longrightarrow> size (learned_clss_lf N\<^sub>0) \<ge> 1);
      RETURN T
    }
    else do {
      let T = (M, N, D, NE, UE, (if irr then add_mset E else id) NS, (if \<not>irr then add_mset E else id) US, N0, U0, Q, W);
      ASSERT (set_mset (all_learned_lits_of_wl T) = set_mset (all_learned_lits_of_wl S));
      ASSERT (set_mset (all_init_lits_of_wl T) = set_mset (all_init_lits_of_wl S));
      ASSERT (set_mset (all_atms_st T) = set_mset (all_atms_st S));
      ASSERT (size (learned_clss_lf N) = size (learned_clss_lf N\<^sub>0));
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
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n
      x2n x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x x' x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y
      by (cases \<open>C' \<notin># dom_m x1w\<close>)
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
    subgoal by auto
    subgoal by auto
    subgoal by (rule all_learned_all_lits_all_atms_st)
    subgoal by (clarsimp simp add: learned_clss_l_l_fmdrop_irrelev learned_clss_l_l_fmdrop
      learned_clss_l_fmdrop_if)
    subgoal by auto
    done
qed

definition simplify_clauses_with_unit_st2 :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>  where
  \<open>simplify_clauses_with_unit_st2 S =
  do {
  xs \<leftarrow> SPEC(\<lambda>xs. xs \<subseteq>set_mset (dom_m (get_clauses_wl S)));
  T \<leftarrow> FOREACHci(\<lambda>it T. simplify_clauses_with_unit_st_wl_inv S it T)
  (xs)
  (\<lambda>S. get_conflict_wl S = None)
  (\<lambda>i S. simplify_clause_with_unit_st2 i S)
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

lemma length_arena_shorten[simp]:
  \<open>length (arena_shorten C' j' arena) = length arena\<close>
  by (auto simp: arena_shorten_def)

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
       {(arena', N). valid_arena arena' N vdom \<and> length arena = length arena'})\<close>
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
    {(arena', N). valid_arena arena' N vdom \<and> length arena' = length arena})\<close>
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
   then RETURN (False, extra_information_mark_to_delete N C, L, is_true, i)
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

lemma isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit:
  assumes \<open>valid_arena arena N vdom\<close> and
    trail: \<open>(M, M') \<in> trail_pol \<A>\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    C: \<open>(C,C')\<in>Id\<close>
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

definition isa_simplify_clause_with_unit_st2 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>isa_simplify_clause_with_unit_st2 =  (\<lambda>C (M, N, D, j, W, vm, clvls, cach, lbd, outl, stats, heur,
      vdom, avdom, lcount, opts, old_arena). do {
   E \<leftarrow> mop_arena_status N C;
  (unc, N, L, b, i) \<leftarrow> isa_simplify_clause_with_unit2 C M N;
   if unc then RETURN (M, N, D, j, W, vm, clvls, cach, lbd, outl, stats, heur,
      vdom, avdom, lcount, opts, old_arena)
   else if b then
   RETURN  (M, N, D, j, W, vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom,
     if E = LEARNED then clss_size_decr_lcount (clss_size_incr_lcountUE lcount) else lcount,
     opts, old_arena)
   else if i = 1
   then do {
     M \<leftarrow> cons_trail_Propagated_tr L 0 M;
     RETURN  (M, N, D, j, W, vm, clvls, cach, lbd, outl, stats, heur,
     vdom, avdom, if E = LEARNED
       then clss_size_decr_lcount (clss_size_incr_lcountUE (clss_size_incr_lcountUS lcount))
       else lcount, opts, old_arena)}
   else if i = 0
   then do {
     j \<leftarrow> mop_isa_length_trail M;
     RETURN  (M, N, set_conflict_to_false D, j, W, vm, 0, cach, lbd, outl, stats, heur,
     vdom, avdom,
     if E = LEARNED
     then clss_size_decr_lcount (clss_size_incr_lcountUS (clss_size_incr_lcountU0 lcount)) else lcount,
     opts, old_arena)
   }
   else
     RETURN  (M, N, D, j, W, vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom,
     if E = LEARNED
     then (clss_size_incr_lcountUS lcount) else lcount, opts, old_arena)
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

lemma isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2:
  assumes \<open>(S, S') \<in> twl_st_heur\<close> and \<open>(C,C')\<in> nat_rel\<close>
  shows \<open>isa_simplify_clause_with_unit_st2 C S \<le>
    \<Down>twl_st_heur (simplify_clause_with_unit_st2 C' S')\<close>
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

  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding isa_simplify_clause_with_unit_st2_def
      simplify_clause_with_unit_st2_def Let_def[of "(_,_)"] Let_def[of \<open>mset _\<close>]
    apply (refine_rcg isa_simplify_clause_with_unit2_isa_simplify_clause_with_unit[where
      vdom=\<open>set (get_vdom S)\<close> and \<A> = \<open>all_atms_st S'\<close>]
      mop_arena_status[where vdom = \<open>set (get_vdom S)\<close>]
      cons_trail_Propagated_tr2[where \<A> = \<open>all_atms_st S'\<close>]
      mop_isa_length_trail_length_u[of \<open>all_atms_st (S')\<close>, THEN fref_to_Down_Id_keep,
      unfolded length_uint32_nat_def comp_def])
    subgoal by auto
    subgoal by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      using literals_are_in_mm_clauses[of S']
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal
      by (auto simp: twl_st_heur_def)
    subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n
      x1o x2o x1p x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y x x' x1z x2z x1aa x2aa x1ab
      x2ab x1ac x2ac x1ad x2ad x1ae x2ae
      apply (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
        get_vdom.simps prod_rel_iff TrueI refl
        cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
        uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
        \<open>all_atms_st (_, _, _, (If _ _ _) _, _)\<close>]
        clss_size_def clss_size_incr_lcountUE_def
        clss_size_decr_lcount_def)
     apply (clarsimp split: if_splits)
     done
   subgoal by simp
   subgoal by (auto simp: twl_st_heur_def)
   subgoal by auto
   subgoal by (auto simp: DECISION_REASON_def)
   subgoal for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae M Ma
     apply (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_decr_lcount_def)
     apply (clarsimp split: if_splits)
     done
   subgoal by simp
   subgoal by simp
   subgoal by (auto simp add: twl_st_heur_def)
   subgoal  for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae
     apply (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def
       clss_size_decr_lcount_def
       option_lookup_clause_rel_cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false)
     apply (clarsimp split: if_splits)
     done
   subgoal  for x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p
     x2p x1q x2q x1r x2r x1s x2s x1t x2t x1u x2u x1v x2v x1w x2w x1x x2x x1y x2y E x x' x1z x2z x1aa x2aa x1ab x2ab x1ac x2ac x1ad
     x2ad x1ae x2ae
     apply (clarsimp simp only: twl_st_heur_def in_pair_collect_simp prod.simps
       get_vdom.simps prod_rel_iff TrueI refl
       cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>] isa_vmtf_consD2
       clss_size_def clss_size_incr_lcountUE_def clss_size_incr_lcountUS_def
       clss_size_incr_lcountU0_def
       clss_size_decr_lcount_def
       option_lookup_clause_rel_cong[of \<open>all_atms_st (x1, x1a, None, x1c, x1d, x1e, x1f, x1g, x1h,
       uminus `# lit_of `# mset (drop x1m (rev x1)), x2i)\<close>
       \<open>all_atms_st (_, _, _, _, _, (If _ _ _) _, _)\<close>, OF sym] outl
       set_conflict_to_false)
     apply (clarsimp split: if_splits)
     done
   done
qed

definition isa_simplify_clauses_with_unit_st2 :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>  where
  \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    xs \<leftarrow> RETURN [];
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
        T \<leftarrow> isa_simplify_clause_with_unit_st2 (xs!i) T;
        ASSERT(i < length xs);
        RETURN (i+1, T)
      })
     (0, S);
    RETURN T
  }\<close>

lemma isa_simplify_clauses_with_unit_st2_simplify_clauses_with_unit_st2:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows \<open>isa_simplify_clauses_with_unit_st2 S \<le>
    \<Down>twl_st_heur (simplify_clauses_with_unit_st2 S')\<close>
proof -
  have isa_simplify_clauses_with_unit_st2_def: \<open>isa_simplify_clauses_with_unit_st2 S =
  do {
    xs \<leftarrow> RETURN [];
    T \<leftarrow> do {
    (_, T) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, T). i < length xs \<and> get_conflict_wl_is_None_heur T)
      (\<lambda>(i,T). do {
        T \<leftarrow> isa_simplify_clause_with_unit_st2 (xs!i) T;
        ASSERT(i < length xs);
        RETURN (i+1, T)
      })
     (0, S);
    RETURN T
    };
    RETURN T
    }\<close>
    unfolding isa_simplify_clauses_with_unit_st2_def by auto

  have [refine]: \<open>RETURN [] \<le> \<Down> {(xs, a). a = set xs \<and> distinct xs} (SPEC (\<lambda>xs. xs \<subseteq> set_mset (dom_m (get_clauses_wl S'))))\<close>
    by (auto simp: RETURN_RES_refine)

    have [refine]: \<open>(xs, xsa) \<in> {(xs, a). a = set xs \<and> distinct xs} \<Longrightarrow>
      xsa \<in> {xs. xs \<subseteq> set_mset (dom_m (get_clauses_wl S'))} \<Longrightarrow>
      ([0..<length xs], xsa) \<in> \<langle>{(i, a). xs ! i =a}\<rangle>list_set_rel\<close> for xs xsa
      by (auto simp: list_set_rel_def br_def
        intro!: relcompI[of _ xs])
       (auto simp: list_rel_def intro!: list_all2_all_nthI)
  show ?thesis
    unfolding isa_simplify_clauses_with_unit_st2_def simplify_clauses_with_unit_st2_def
      nfoldli_upt_by_while[symmetric]  nres_monad3
    apply (refine_vcg isa_simplify_clause_with_unit_st2_simplify_clause_with_unit_st2
      LFOci_refine)
    subgoal by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id]
      assms get_conflict_wl_is_None_def)
    subgoal by auto
    subgoal using assms by auto
    done
qed

text \<open>This is a temporary work-around to make IsaSAT compile again before properly implementing the
  function.\<close>
lemma isa_simplify_clauses_with_unit_st2_alt_def:
  \<open>isa_simplify_clauses_with_unit_st2 S = RETURN S\<close>
  unfolding isa_simplify_clauses_with_unit_st2_def
  apply (subst WHILET_unfold)
  apply simp
  done

end