theory Watched_Literals_List_Restart
  imports Watched_Literals_List Watched_Literals_Algorithm_Restart
begin

definition mapping_old_new_clauses where
  \<open>mapping_old_new_clauses N N' NE NE' \<longleftrightarrow>
    (init_clss_lf N' = init_clss_lf N \<and>
    learned_clss_lf N' \<subseteq># learned_clss_lf N \<and>
    0 \<notin># dom_m N' \<and>
    NE' = NE)\<close>

definition derive_literals_and_clauses
  :: \<open>('v, nat) ann_lits \<Rightarrow> ('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clauses_l \<Rightarrow>
        'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
 \<open>derive_literals_and_clauses M M' N N' NE NE' \<longleftrightarrow>
    mapping_old_new_clauses N N' NE NE' \<and>
    (\<forall>L C C'. Propagated L C \<in> set M \<longrightarrow> Propagated L C \<in> set M' \<longrightarrow> N \<propto> C = N' \<propto> C')\<close>

definition restart_prog_clss_list :: \<open>'v twl_st_l \<Rightarrow> 'v twl_st_l nres\<close> where
  \<open>restart_prog_clss_list = (\<lambda>(M, N, D, NE, UE, WS, Q). do {
     (M', N', NE') \<leftarrow> SPEC(\<lambda>(M', N', NE'). derive_literals_and_clauses M M' N N' NE NE');
     RETURN (M', N', D, NE', UE, WS, Q)
  })\<close>

definition cdcl_twl_restart_only:: \<open>'v twl_st \<Rightarrow> ('v twl_st) nres\<close>  where
  \<open>cdcl_twl_restart_only = (\<lambda>S. SPEC(\<lambda>T. cdcl_twl_restart S T))\<close>

context twl_restart
begin

definition restart_required_l :: "'v twl_st_l \<times> nat \<Rightarrow> bool nres" where
  \<open>restart_required_l S = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clauses_l (fst S)) > f (snd S))\<close>

definition restart_prog_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat) nres" where
  \<open>restart_prog_l S n brk = do {
     b \<leftarrow> restart_required_l (S, n);
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>



lemma cdcl_twl_o_prog_l_spec:
  \<open>(restart_prog_clss_list, cdcl_twl_restart_only) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None \<and> literals_to_update_l S = {#} \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S \<and>
       get_conflict S' = None} \<rightarrow>
    \<langle>{(T, T'). (T, T') \<in> twl_st_l None \<and> twl_list_invs T}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have \<open>RETURN (M'', N', D, NE', UE, WS, Q)
      \<le> \<Down> {(T, T'). (T, T') \<in> twl_st_l None \<and>
            twl_list_invs T \<and> clauses_to_update_l T = {#} \<and> twl_struct_invs T' \<and> twl_stgy_invs T'}
          (SPEC (cdcl_twl_restart S''))\<close>
    if
      \<open>(S, S'') \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and>
         literals_to_update_l S = {#} \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S \<and>
         get_conflict S' = None}\<close> and
      \<open>SUE = (WS, Q)\<close> and
      \<open>SNE = (UE, SUE)\<close> and
      \<open>SD = (NE, SNE)\<close> and
      \<open>SN = (D, SD)\<close> and
      \<open>SM = (N, SN)\<close> and
      \<open>S = (M, SM)\<close> and
      \<open>x \<in> {(M', N', y). derive_literals_and_clauses M M' N N' NE y}\<close> and
      \<open>SM'' = (N', NE')\<close> and
      \<open>x = (M'', SM'')\<close>
    for S and SM and SN and D and SD and NE and SNE and UE and SUE and WS and Q and
      M'' and SM'' and N' and NE' and S'' and x and M and N
  proof -
    have [simp]: \<open>clause (twl_clause_of x) = mset x\<close> for x
      by (cases x) (auto simp: mset_append[symmetric] simp del: mset_append)

    obtain M' N'' U' D' NE'' UE' WS' Q' where
      S'': \<open>S'' = (M', N'', U', D', NE'', UE', WS', Q')\<close>
      by (cases S'')
    have [simp]: \<open>{#twl_clause_of (fst x). x \<in># init_clss_l N'#} = {#twl_clause_of (fst x). x \<in># init_clss_l N#}\<close>
      if \<open>init_clss_lf N' = init_clss_lf N\<close>
    proof -
      have \<open>{#twl_clause_of (fst x). x \<in># init_clss_l N'#} = {#twl_clause_of x. x \<in># init_clss_lf N'#}\<close>
        by auto
      also have \<open>\<dots> = {#twl_clause_of x. x \<in># init_clss_lf N#}\<close>
        unfolding that ..
      finally show ?thesis by simp
    qed
    have [simp]: \<open>{#twl_clause_of (fst x). x \<in># learned_clss_l N'#} \<subseteq># {#twl_clause_of (fst x). x \<in># learned_clss_l N#}\<close>
      if \<open>learned_clss_lf N' \<subseteq># learned_clss_lf N\<close>
    proof -
      have \<open>{#twl_clause_of (fst x). x \<in># learned_clss_l N'#} = {#twl_clause_of x. x \<in># learned_clss_lf N'#}\<close>
        by auto
      also have \<open>\<dots> \<subseteq>#  {#twl_clause_of x. x \<in># learned_clss_lf N#}\<close>
        using image_mset_subseteq_mono[OF that] .
      finally show ?thesis by simp
    qed
    show ?thesis
    apply (subst RETURN_RES_refine_iff)
    using that unfolding S''
    apply (auto simp: twl_st_l_def derive_literals_and_clauses_def mapping_old_new_clauses_def
        (* intro: *) cdcl_twl_restart.simps simp del: twl_clause_of.simps)
    sorry
qed
  show ?thesis
    unfolding restart_prog_clss_list_def cdcl_twl_restart_only_def
    apply (refine_vcg)
    explore_have
    apply assumption
    sorry

  show ?thesis
    unfolding restart_prog_clss_list_def cdcl_twl_restart_only_def
    by (refine_vcg corr; remove_dummy_vars)
  oops

end

end
