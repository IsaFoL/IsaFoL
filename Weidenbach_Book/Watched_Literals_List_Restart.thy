theory Watched_Literals_List_Restart
  imports Watched_Literals_List Watched_Literals_Algorithm_Restart
begin

definition mapping_old_new_clauses where
  \<open>mapping_old_new_clauses N N' NE NE' \<longleftrightarrow>
    (mset `# (init_clss_lf N') + NE = mset `# (init_clss_lf N) + NE' \<and>
    learned_clss_lf N' \<subseteq># learned_clss_lf N \<and>
    0 \<notin># dom_m N')\<close>

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

lemma cdcl_twl_o_prog_l_spec:
  \<open>(restart_prog_clss_list, cdcl_twl_restart_only) \<in>
    {(S, S'). (S, S') \<in> twl_st_l None \<and> literals_to_update_l S = {#} \<and>
       twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S} \<rightarrow>
    \<langle>{(T, T'). (T, T') \<in> twl_st_l None  \<and> twl_list_invs T \<and> clauses_to_update_l T = {#} \<and>
       twl_struct_invs T' \<and> twl_stgy_invs T'}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have \<open>RETURN (M'', N', D, NE', UE, WS, Q)
      \<le> \<Down> {(T, T').
            (T, T') \<in> twl_st_l None \<and>
            twl_list_invs T \<and> clauses_to_update_l T = {#} \<and> twl_struct_invs T' \<and> twl_stgy_invs T'}
          (SPEC (cdcl_twl_restart S''))\<close>
    if 
      \<open>(S, S'')
     \<in> {(S, S').
         (S, S') \<in> twl_st_l None \<and>
         literals_to_update_l S = {#} \<and> twl_struct_invs S' \<and> twl_stgy_invs S' \<and> twl_list_invs S}\<close> and
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
  obtain M' N'' U' D' NE'' UE' WS' Q' where
    S'': \<open>S'' = (M', N'', U', D', NE'', UE', WS', Q')\<close>
    by (cases S'')
  show ?thesis
    apply (subst RETURN_RES_refine_iff)
    using that unfolding S''
    apply (auto)
    sorry
qed
  show ?thesis
    unfolding restart_prog_clss_list_def cdcl_twl_restart_only_def
    apply (refine_vcg)
    explore_have
    apply assumption
    sorry
  have corr:
    \<open>RETURN (map_proped_lits (the \<circ> new_pos) M, N', u, D, NE, UE, WS, Q)
      \<le> \<Down> {(T, T').
            T' = twl_st_of None T \<and>
            twl_list_invs T \<and>
            clauses_to_update_l T = {#} \<and>
            twl_struct_invs (twl_st_of None T) \<and>
            twl_stgy_invs (twl_st_of None T)}
          (SPEC (cdcl_twl_restart S))\<close>
    if
      \<open>((M, N, u, D, NE, UE, WS, Q), S) \<in> {(S, S').
         S' = twl_st_of None S \<and>
         literals_to_update_l S = {#} \<and>
         twl_struct_invs (twl_st_of None S) \<and>
         twl_stgy_invs (twl_st_of None S) \<and> twl_list_invs S}\<close> and
      \<open>(N', new_pos) \<in> {(x, y). derive_literals_and_clauses M N u x y}\<close>
    for S M N u D NE UE WS Q N' new_pos
  proof -
    obtain M' N'' U' D' NE' UE' WS' Q' where
      S: \<open>S = (M', N'', U', D', NE', UE', WS', Q')\<close>
      by (cases S)
    have
      S_twl: \<open>S = twl_st_of None (M, N, u, D, NE, UE, WS, Q)\<close> and
      \<open>literals_to_update_l (M, N, u, D, NE, UE, WS, Q) = {#}\<close> and
      \<open>twl_struct_invs (twl_st_of None (M, N, u, D, NE, UE, WS, Q))\<close> and
      \<open>twl_stgy_invs (twl_st_of None (M, N, u, D, NE, UE, WS, Q))\<close> and
      list_invs: \<open>twl_list_invs (M, N, u, D, NE, UE, WS, Q)\<close> and
      derive: \<open>derive_literals_and_clauses M N u N' new_pos\<close>
      using that by fast+
    have
      H: \<open>\<And>i. i\<in>{1..<length N} \<Longrightarrow> new_pos i \<noteq> None \<Longrightarrow>
        the (new_pos i) < length N' \<and> N' ! the (new_pos i) = N ! i\<close> and
      \<open>mset (tl N') \<subseteq># mset (tl N)\<close> and
      trail_kept: \<open>\<And>L C. Propagated L C \<in> set M \<Longrightarrow> new_pos C \<noteq> None\<close> and
      [simp]: \<open>new_pos 0 = Some 0\<close> and
      new_pos_0[iff]: \<open>\<And>i. new_pos i = Some 0 \<longleftrightarrow> i = 0\<close> and
      init_at_beginning: \<open>\<And>j. j < u \<longrightarrow> new_pos j \<noteq> None \<and> the (new_pos j) < u\<close>
      using derive unfolding derive_literals_and_clauses_def
      by fast+
    have
      M'_M: \<open>M' = convert_lits_l N M\<close> and
      \<open>N'' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)).
          x \<in># mset (take u (tl N))#}\<close> and
      \<open>U' = {#TWL_Clause (mset (watched_l x)) (mset (unwatched_l x)).
          x \<in># mset (drop (Suc u) N)#}\<close> and
      [simp]: \<open>D' = D\<close> and
      [simp]: \<open>NE' = NE\<close> and
      [simp]: \<open>UE' = UE\<close> and
      [simp]: \<open>WS' = {#}\<close> and
      [simp]: \<open>Q' = Q\<close>
      using S_twl unfolding S
      by auto
    have \<open>convert_lit N x = convert_lit N' (map_annotated_lit id id (the \<circ> new_pos) x)\<close>
      if \<open>x \<in> set M\<close> for x
    proof -
      show ?thesis
      proof (cases x)
        case (Decided x1)
        then show ?thesis by auto
      next
        case x: (Propagated L C)
        have \<open>C < length N\<close>
          using list_invs \<open>x \<in> set M\<close> unfolding twl_list_invs_def x by auto
        show ?thesis
          using that trail_kept[of L C] H[of \<open>mark_of x\<close>] \<open>C < length N\<close>
          by (auto simp: x)
      qed
    qed
    then have trail_S: \<open>get_trail S = convert_lits_l N' (map_proped_lits (the \<circ> new_pos) M)\<close>
      unfolding S M'_M convert_lits_l_def by auto
    have \<open>mset (take u (tl N')) = mset (take u (tl N))\<close>
      using init_at_beginning

      sorry
    show ?thesis
      apply (subst RETURN_RES_refine_iff)
      apply (auto intro!: cdcl_twl_restart.intros(2)
          simp: trail_S[symmetric])
      sorry
  qed
  show ?thesis
    unfolding restart_prog_clss_list_def cdcl_twl_restart_only_def
    by (refine_vcg corr; remove_dummy_vars)
  oops

end

end
