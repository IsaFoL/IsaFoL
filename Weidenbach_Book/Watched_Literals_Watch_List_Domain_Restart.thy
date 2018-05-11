theory Watched_Literals_Watch_List_Domain_Restart
  imports Watched_Literals_Watch_List_Domain Watched_Literals_Watch_List_Restart
begin

locale isasat_restart_ops =
  twl_restart + isasat_input_bounded

context isasat_restart_ops
begin

definition restart_prog_wl_D_pre :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>restart_prog_wl_D_pre S \<longleftrightarrow> literals_are_\<L>\<^sub>i\<^sub>n S \<and> restart_prog_wl_pre S\<close>

lemma cdcl_twl_restart_wl_literals_are_\<L>\<^sub>i\<^sub>n:
  assumes
     \<open>cdcl_twl_restart_wl S T\<close> and
    \<A>\<^sub>i\<^sub>n: \<open>restart_prog_wl_D_pre S\<close>
  shows \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close>
  using assms
proof (induction)
  case (restart_trail M M' N N' NE' UE' NE UE Q Q' W' W) note init_clss = this(2) and
   learned = this(3) and pre = this(11)
  obtain T U where
    lits_in: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, None, NE, UE, Q, W)\<close> and
    ST: \<open>((M, N, None, NE, UE, Q, W), T) \<in> state_wl_l None\<close> and
    \<open>correct_watching (M, N, None, NE, UE, Q, W)\<close> and
    TU: \<open>(T, U) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs T\<close> and
    struct_invs: \<open>twl_struct_invs U\<close> and
    \<open>twl_stgy_invs U\<close>
    using pre unfolding restart_prog_wl_D_pre_def restart_prog_wl_pre_def
      restart_prog_l_pre_def restart_prog_pre_def
    by blast
  define S' T' :: \<open>nat twl_st_wl\<close> where
     \<open>S' \<equiv> (M, N, None, NE, UE, Q, W)\<close> and
     \<open>T' \<equiv> (M', N', None, NE + mset `# NE', UE + mset `# UE', Q', W')\<close>
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of U)\<close>
    using struct_invs unfolding twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  obtain NN where NN: \<open>learned_clss_lf N = learned_clss_lf N' + UE' + NN\<close>
    using learned[unfolded mset_subset_eq_exists_conv] ..
  have \<open>atms_of_mm (mset `# ran_mf (get_clauses_wl T') + get_unit_clauses_wl T') =
     atms_of_mm (mset `# init_clss_lf (get_clauses_wl T') + get_unit_init_clss_wl T') \<union>
     atms_of_mm (mset `# learned_clss_lf (get_clauses_wl T') + get_unit_learned_clss_wl T')\<close>
    unfolding all_clss_lf_ran_m[symmetric] image_mset_union
    by (cases T') (auto simp:)
  moreover have \<open>atms_of_mm (mset `# init_clss_lf (get_clauses_wl T') + get_unit_init_clss_wl T') =
     atms_of_mm (mset `# init_clss_lf (get_clauses_wl S') + get_unit_init_clss_wl S')\<close>
    using init_clss unfolding S'_def T'_def
    by auto
  moreover have \<open>atms_of_mm (mset `# learned_clss_lf (get_clauses_wl T') + get_unit_learned_clss_wl T') \<subseteq>
     atms_of_mm (mset `# learned_clss_lf (get_clauses_wl S') + get_unit_learned_clss_wl S')\<close>
    unfolding S'_def T'_def NN get_clauses_wl.simps
    by auto
  moreover have \<open>atms_of_mm (mset `# init_clss_lf (get_clauses_wl S') + get_unit_init_clss_wl S') \<supseteq>
     atms_of_mm (mset `# learned_clss_lf (get_clauses_wl S') + get_unit_learned_clss_wl S')\<close>
    using ST TU alien
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def cdcl\<^sub>W_restart_mset.no_strange_atm_def S'_def T'_def
    by (auto simp: state_wl_l_def twl_st_l_def cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
  ultimately have H: \<open>atms_of_mm ({#mset (fst C). C \<in># ran_m (get_clauses_wl T')#} + get_unit_clauses_wl T') =
     atms_of_mm (mset `# init_clss_lf (get_clauses_wl S') + get_unit_init_clss_wl S') \<union>
     atms_of_mm (mset `# learned_clss_lf (get_clauses_wl S') + get_unit_learned_clss_wl S')\<close>
    by auto
  moreover have \<open>atms_of_mm (mset `# ran_mf (get_clauses_wl S') + get_unit_clauses_wl S') =
     atms_of_mm (mset `# init_clss_lf (get_clauses_wl S') + get_unit_init_clss_wl S') \<union>
     atms_of_mm (mset `# learned_clss_lf (get_clauses_wl S') + get_unit_learned_clss_wl S')\<close>
    unfolding all_clss_lf_ran_m[symmetric] image_mset_union
    by (cases S') (auto simp:)
  ultimately have H:  \<open>atms_of_mm ({#mset (fst C). C \<in># ran_m (get_clauses_wl T')#} + get_unit_clauses_wl T') =
     atms_of_mm ({#mset (fst C). C \<in># ran_m (get_clauses_wl S')#} + get_unit_clauses_wl S')\<close>
    by auto
  show ?case
    using lits_in
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def S'_def[symmetric] T'_def[symmetric] H
    .
qed


lemma cdcl_twl_restart_wl_cdcl_twl_restart_wl:
  assumes
    \<A>\<^sub>i\<^sub>n: \<open>restart_prog_wl_D_pre S\<close>
  shows \<open>SPEC (cdcl_twl_restart_wl S) \<le> \<Down> {(S, S'). (S, S') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}
          (SPEC (cdcl_twl_restart_wl S))\<close>
  using cdcl_twl_restart_wl_literals_are_\<L>\<^sub>i\<^sub>n[OF _ assms]
  by (auto intro!: RES_refine)

definition restart_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (nat twl_st_wl \<times> nat) nres" where
  \<open>restart_prog_wl_D S n brk = do {
     ASSERT(restart_prog_wl_D_pre S);
     b \<leftarrow> restart_required_wl S n;
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_wl S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>


lemma restart_prog_wl_D_restart_prog_wl:
  assumes
     \<open>((S, n, brk), (S', n', brk')) \<in> {((S, m), (S', m')). S = S' \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and> m = m' \<and>
       brk = brk'}\<close>
  shows \<open>restart_prog_wl_D S n brk \<le> \<Down>{((S, m), (S', m')). S = S' \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and> m = m'}
      (restart_prog_wl S' n' brk')\<close>
proof -
  have 1: \<open>restart_required_wl S n \<le> \<Down> bool_rel (restart_required_wl S' n')\<close>
    using assms by (auto simp: restart_required_wl_def)
  show ?thesis
    using assms
    unfolding restart_prog_wl_def restart_prog_wl_D_def
    apply (refine_vcg 1 )
    subgoal unfolding restart_prog_wl_D_pre_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro: cdcl_twl_restart_wl_literals_are_\<L>\<^sub>i\<^sub>n)
    subgoal by auto
    done
qed


definition cdcl_twl_stgy_restart_prog_wl_D_inv where
  \<open>cdcl_twl_stgy_restart_prog_wl_D_inv S\<^sub>0 brk T n \<equiv>
    (cdcl_twl_stgy_restart_prog_wl_inv S\<^sub>0 brk T n \<and>
       literals_are_\<L>\<^sub>i\<^sub>n T)\<close>

definition cdcl_twl_stgy_restart_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>cdcl_twl_stgy_restart_prog_wl_D S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_wl_D_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_wl_D S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_wl_D T;
        (T, n) \<leftarrow> restart_prog_wl_D T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma cdcl_twl_stgy_restart_prog_wl_D_cdcl_twl_stgy_restart_prog_wl:
  \<open>(cdcl_twl_stgy_restart_prog_wl_D, cdcl_twl_stgy_restart_prog_wl) \<in>
     {(S, S'). (S, S') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S}\<rangle> nres_rel\<close>
proof -
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast

  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_\<L>\<^sub>i\<^sub>n T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_wl_D_def cdcl_twl_stgy_restart_prog_wl_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg 2 3 WHILEIT_refine[where R = \<open>{((brk :: bool, S, n :: nat), (brk', S', n')).
        (S, S') \<in> Id \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and> brk = brk' \<and> n = n'}\<close>]
        unit_propagation_outer_loop_wl_D_spec
        cdcl_twl_o_prog_wl_D_spec
        restart_prog_wl_D_restart_prog_wl)
    subgoal by auto
    subgoal for x y xa x' x1 x2 x1a x2a
      unfolding cdcl_twl_stgy_restart_prog_wl_D_inv_def
      by auto
    subgoal by fast
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_wl_inv_def
        cdcl_twl_stgy_restart_prog_wl_D_inv_def
      apply (simp only: prod.case)
      apply (normalize_goal)+
      by (simp add: twl_st_l twl_st twl_st_wl)
    subgoal by (auto simp: twl_st_l twl_st)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end

end