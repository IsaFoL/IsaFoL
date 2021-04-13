theory Watched_Literals_List_Simp
  imports
    Watched_Literals_List_Reduce
    Watched_Literals_List_Inprocessing
begin
lemma cdcl_twl_inprocessing_l_count_dec:
  \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close>
  by (induction rule: cdcl_twl_inprocessing_l.induct)
   (auto simp: cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
    cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
 
lemma rtranclp_cdcl_twl_inprocessing_l_count_dec:
  \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<Longrightarrow> count_decided (get_trail_l T) = count_decided (get_trail_l S)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: cdcl_twl_inprocessing_l_count_dec)
    
inductive cdcl_twl_restart_l_inp for S T where
  \<open>cdcl_twl_restart_l S T \<Longrightarrow> cdcl_twl_restart_l_inp S T\<close> |
  \<open>cdcl_twl_inprocessing_l S T \<Longrightarrow> cdcl_twl_restart_l_inp S T\<close>

lemma cdcl_twl_restart_l_inp_twl_list_invs:
  \<open>cdcl_twl_restart_l_inp S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  apply (induction rule: cdcl_twl_restart_l_inp.induct)
    using cdcl_twl_restart_l_list_invs apply blast
  using cdcl_twl_inprocessing_l_twl_list_invs by blast

lemma rtranclp_cdcl_twl_restart_l_inp_twl_list_invs:
  \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<Longrightarrow> twl_list_invs S \<Longrightarrow> twl_list_invs T\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl_twl_restart_l_inp_twl_list_invs)

lemma rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l:
  \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* xa V\<Longrightarrow> clauses_to_update_l xa = {#} \<Longrightarrow>
  clauses_to_update_l V = {#}\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal premises p
    using p(2)
    by (auto simp: cdcl_twl_restart_l_inp.simps
      cdcl_twl_restart_l.simps cdcl_twl_inprocessing_l.simps
      cdcl_twl_unitres_l.simps cdcl_twl_unitres_true_l.simps
      cdcl_twl_subsumed_l.simps cdcl_twl_subresolution_l.simps)
  done

lemma rtranclp_cdcl_twl_inprocessing_l_cdcl_twl_l_inp:
  \<open>cdcl_twl_inprocessing_l\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: cdcl_twl_restart_l_inp.intros)

lemma cdcl_twl_restart_l_inp_cdcl_twl_restart_inp:
  assumes
    \<open>cdcl_twl_restart_l_inp S U\<close>
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>twl_struct_invs T\<close>
  obtains V where
    \<open>(U, V) \<in> twl_st_l None\<close>
    \<open>cdcl_twl_inp T V\<close>
  using assms
  apply (induction rule: cdcl_twl_restart_l_inp.induct)
  subgoal premises p
    using p apply -
    apply (drule cdcl_twl_restart_l_invs[OF assms(2,3,4), of U])
    apply normalize_goal+
    apply (rule p(2))
    apply assumption
    by (auto dest!: cdcl_twl_inp.intros)
  subgoal
    apply (cases rule: cdcl_twl_inprocessing_l.cases, assumption)
    using cdcl_twl_inp.intros(3) cdcl_twl_unitres_l_cdcl_twl_unitres apply blast
    apply (meson cdcl_twl_inp.simps cdcl_twl_unitres_true_l_cdcl_twl_unitres_true)
    apply (meson cdcl_twl_inp.intros(1) cdcl_twl_inp.intros(2) cdcl_twl_inp.intros(3) cdcl_twl_inp.intros(4) cdcl_twl_inprocessing_l_twl_st_l0)
    by (meson cdcl_twl_inp.simps cdcl_twl_subresolution_l_cdcl_twl_subresolution)
    done

lemma rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp:
  assumes
    \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S U\<close>
    \<open>(S, T) \<in> twl_st_l None\<close> and
    \<open>twl_list_invs S\<close> and
    \<open>twl_struct_invs T\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
  obtains V where
    \<open>(U, V) \<in> twl_st_l None\<close>  and
    \<open>cdcl_twl_inp\<^sup>*\<^sup>* T V\<close>
proof -
  have \<open>\<exists>V. (U, V) \<in> twl_st_l None \<and> cdcl_twl_inp\<^sup>*\<^sup>* T V\<close>
    using assms(1)
    apply (induction arbitrary: rule: rtranclp_induct)
    subgoal
      by (rule exI[of _ T]) (use assms in auto)
    subgoal for x y
      apply normalize_goal+
      apply (rule cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[of ], assumption+)
      apply (smt (verit, ccfv_threshold) assms(3) rtranclp_cdcl_twl_restart_l_inp_twl_list_invs)
      using assms(4) assms(5) rtranclp_cdcl_twl_inp_invs(1) apply blast
      by force
    done
  then show ?thesis
    using that by blast
qed

definition cdcl_twl_full_restart_l_prog where
  \<open>cdcl_twl_full_restart_l_prog S = do {
  ASSERT(mark_to_delete_clauses_l_pre S);
  T \<leftarrow> mark_to_delete_clauses_l S;
  ASSERT (mark_to_delete_clauses_l_post S T);
  RETURN T
  }\<close>

definition cdcl_twl_full_restart_inprocess_l where
  \<open>cdcl_twl_full_restart_inprocess_l S = do {
  ASSERT(cdcl_twl_full_restart_l_GC_prog_pre S);
  S' \<leftarrow> cdcl_twl_local_restart_l_spec0 S;
  S' \<leftarrow> simplify_clauses_with_unit_st S';
  if (get_conflict_l S' \<noteq> None) then
    RETURN S'
  else do {
      T \<leftarrow> remove_one_annot_true_clause_imp S';
      ASSERT(mark_to_delete_clauses_l_pre T);
      U \<leftarrow> mark_to_delete_clauses_l T;
      V \<leftarrow> cdcl_GC_clauses U;
      ASSERT(cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S V);
      RETURN V
    }
  }\<close>

definition cdcl_twl_full_restart_l_GC_prog where
  \<open>cdcl_twl_full_restart_l_GC_prog S = do {
    ASSERT(cdcl_twl_full_restart_l_GC_prog_pre S);
    S' \<leftarrow> cdcl_twl_local_restart_l_spec0 S;
    T \<leftarrow> remove_one_annot_true_clause_imp S';
    ASSERT(mark_to_delete_clauses_l_pre T);
    U \<leftarrow> mark_to_delete_clauses_l T;
    V \<leftarrow> cdcl_GC_clauses U;
    ASSERT(cdcl_twl_restart_l S V);
    RETURN V
  }\<close>


context twl_restart_ops
begin

lemma cdcl_twl_full_restart_l_prog_spec:
  assumes
    ST: \<open>(S, T) \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs T\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close>
  shows \<open>cdcl_twl_full_restart_l_prog S \<le> \<Down> Id (SPEC(remove_one_annot_true_clause\<^sup>+\<^sup>+ S))\<close>
proof -
  have mark_to_delete_clauses_l:
    \<open>mark_to_delete_clauses_l x \<le> SPEC (\<lambda>T. ASSERT (mark_to_delete_clauses_l_post U T) \<bind>
             (\<lambda>_. RETURN T)
             \<le> SPEC (remove_one_annot_true_clause\<^sup>+\<^sup>+ U))\<close>
    if
      Ux: \<open>(x, U) \<in> Id\<close> and
      U: \<open>U \<in> Collect (remove_one_annot_true_clause\<^sup>*\<^sup>* S)\<close>
      for x U
  proof -
    from U have SU: \<open>remove_one_annot_true_clause\<^sup>*\<^sup>* S U\<close> by simp
    have x: \<open>x = U\<close>
      using Ux by auto
    obtain V where
      SU': \<open>cdcl_twl_restart_l\<^sup>*\<^sup>* S U\<close> and
      UV: \<open>(U, V) \<in> twl_st_l None\<close> and
      TV: \<open>cdcl_twl_restart\<^sup>*\<^sup>* T V\<close> and
      struct_invs_V: \<open>twl_struct_invs V\<close>
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[OF SU list_invs
        confl upd ST struct_invs]
      by auto
    have
      confl_U: \<open>get_conflict_l U = None\<close> and
      upd_U: \<open>clauses_to_update_l U = {#}\<close>
      using rtranclp_remove_one_annot_true_clause_get_conflict_l[OF SU]
         rtranclp_remove_one_annot_true_clause_clauses_to_update_l[OF SU] confl upd
      by auto
    have list_U: \<open>twl_list_invs U\<close>
      using SU' list_invs rtranclp_cdcl_twl_restart_l_list_invs by blast
     have [simp]:
      \<open>remove_one_annot_true_clause\<^sup>+\<^sup>+ U V' \<Longrightarrow>  mark_to_delete_clauses_l_post U V'\<close> for V'
      unfolding mark_to_delete_clauses_l_post_def
      using UV struct_invs_V list_U confl_U upd_U
      by (blast dest: tranclp_into_rtranclp)
    show ?thesis
      unfolding x
      by (rule mark_to_delete_clauses_l_spec[OF UV list_U struct_invs_V confl_U upd_U,
         THEN order_trans])
       (auto intro: RES_refine)
  qed
  have 1: \<open>SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* S) = do {
       T \<leftarrow> SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* S);
       SPEC (remove_one_annot_true_clause\<^sup>*\<^sup>* T)
    }\<close>
  by (auto simp: RES_RES_RETURN_RES)
  have H: \<open>mark_to_delete_clauses_l_pre T\<close>
    if
      \<open>(T, U) \<in> Id\<close> and
      \<open>U \<in> Collect (remove_one_annot_true_clause\<^sup>*\<^sup>* S)\<close>
    for T U
  proof -
    show ?thesis
      using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[of S U,
          OF _ list_invs confl upd ST struct_invs] that list_invs
      unfolding mark_to_delete_clauses_l_pre_def
      by (force intro: rtranclp_cdcl_twl_restart_l_list_invs)
  qed
  show ?thesis
    unfolding cdcl_twl_full_restart_l_prog_def
    apply (refine_vcg mark_to_delete_clauses_l)
    subgoal
      using assms
      unfolding mark_to_delete_clauses_l_pre_def
      by blast
    subgoal by auto
    subgoal by (auto simp: assert_bind_spec_conv)
    done
qed

definition GC_required_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>GC_required_l S m n = do {
     ASSERT(size (get_all_learned_clss_l S) \<ge> m);
     SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss_l S) - m > f n)
  }\<close>

definition restart_required_l :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_l S m n =  do {
     ASSERT(size (get_all_learned_clss_l S) \<ge> m);
     SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss_l S) > m)
   }\<close>

definition inprocessing_required_l :: "'v twl_st_l \<Rightarrow> bool nres" where
  \<open>inprocessing_required_l S = do {
  SPEC (\<lambda>b. True)
  }\<close>

lemma inprocessing_required_l_inprocessing_required:
  \<open>(inprocessing_required_l, inprocessing_required) \<in> twl_st_l None \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: inprocessing_required_l_def inprocessing_required_def)

definition restart_abs_l
  :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat \<times> nat \<times> nat) nres"
where
  \<open>restart_abs_l S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_l_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required_l S last_GC n;
     b2 \<leftarrow> restart_required_l S last_Restart n;
     if b2 \<and>  \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only_l S T);
       RETURN (T, last_GC, size (get_all_learned_clss_l T), n)
     }
     else
     if b \<and> \<not>brk then do {
       b \<leftarrow> inprocessing_required_l S;
       if \<not>b then do {
         T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l S T);
         RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       } else do {
         T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail_l T) = 0);
         if get_conflict_l T = None
         then do {
           T \<leftarrow> SPEC(cdcl_twl_restart_l T);
           T \<leftarrow> RETURN T;
           RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
         } else
           RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
     }
     else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>


lemma (in -)[twl_st_l]:
  \<open>(S, S') \<in> twl_st_l None \<Longrightarrow> get_learned_clss S' = twl_clause_of `# (get_learned_clss_l S)\<close>
  by (auto simp: get_learned_clss_l_def twl_st_l_def)

lemma restart_required_l_restart_required:
  \<open>(uncurry2 restart_required_l, uncurry2 restart_required) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S} \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f
    \<langle>bool_rel\<rangle> nres_rel\<close>
  unfolding restart_required_l_def restart_required_def uncurry_def
  by (intro frefI nres_relI) (refine_rcg, auto simp: twl_st_l_def get_learned_clss_l_def)

lemma GC_required_l_GC_required:
  \<open>(uncurry2 GC_required_l, uncurry2 GC_required) \<in>
     {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S} \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f
    \<langle>bool_rel\<rangle> nres_rel\<close>
  unfolding GC_required_l_def GC_required_def uncurry_def
  by (intro frefI nres_relI) (refine_rcg, auto simp: twl_st_l_def get_learned_clss_l_def)

lemma \<open>size (get_learned_clss_l T) = size (learned_clss_l (get_clauses_l T))\<close>
  by (auto simp: get_learned_clss_l_def)

lemma restart_abs_l_restart_prog:
  \<open>(uncurry4 restart_abs_l, uncurry4 restart_prog) \<in>
  {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel
  \<rightarrow>\<^sub>f
    \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<rangle> nres_rel\<close>
proof -
  have [refine]: \<open>RETURN T
    \<le> \<Down> ({(S, T). (S, T) \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S = {#} \<and> get_conflict_l S = None})
       (SPEC
         (\<lambda>U. cdcl_twl_stgy\<^sup>*\<^sup>* Ta U \<and>
    clauses_to_update U = {#} \<and> get_conflict U = None))\<close>
    if \<open>(T, Ta) \<in> twl_st_l None\<close> \<open>clauses_to_update_l T = {#}\<close>
      \<open>get_conflict_l T = None\<close> \<open>twl_list_invs T\<close>
    for T Ta
    using that apply -
    apply (rule RETURN_RES_refine)
    apply (rule_tac x=Ta in exI)
    apply (auto intro!: RETURN_RES_refine)
    done
  have [refine0]: \<open>RETURN False \<le> \<Down> {(a,b). \<not>a \<and> \<not>b} (inprocessing_required S)\<close> for S
    by (auto simp: inprocessing_required_def intro!: RETURN_RES_refine)
  have cdcl_twl_restart_l_inp: \<open>(x, y)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<times>\<^sub>f nat_rel \<times>\<^sub>f
    nat_rel \<times>\<^sub>f
    nat_rel \<times>\<^sub>f
    bool_rel \<Longrightarrow>
    x1b = (x1c, x2) \<Longrightarrow>
    x1a = (x1b, x2a) \<Longrightarrow>
    x1 = (x1a, x2b) \<Longrightarrow>
    y = (x1, x2c) \<Longrightarrow>
    x1f = (x1g, x2d) \<Longrightarrow>
    x1e = (x1f, x2e) \<Longrightarrow>
    x1d = (x1e, x2f) \<Longrightarrow>
    x = (x1d, x2g) \<Longrightarrow>
    restart_prog_pre x1c x2 x2a x2c \<Longrightarrow>
    restart_abs_l_pre x1g x2d x2e x2g \<Longrightarrow>
    SPEC (cdcl_twl_restart_l_inp\<^sup>*\<^sup>* x1g)
    \<le> \<Down>{(S, T). (S, T) \<in> twl_st_l None \<and> twl_list_invs S \<and>
    clauses_to_update_l S = {#}}
    (SPEC (cdcl_twl_inp\<^sup>*\<^sup>* x1c))\<close>
    for x y x1 x1a x1b x1c x2 x2a x2b x2c x1d x1e x1f x1g x2d x2e x2f x2g b ba
      b2 b2a bb bc
    supply [[goals_limit=1]]
    apply (rule RES_refine)
    apply (simp only: mem_Collect_eq prod.simps prod_rel_iff
      restart_abs_l_pre_def restart_prog_pre_def)
    apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp)
    apply assumption+
    apply normalize_goal+
    apply assumption+
    apply normalize_goal+
    apply assumption+
    apply normalize_goal+
    apply assumption+
    apply normalize_goal+
    apply assumption+
     apply (rule_tac x=V in bexI)
       apply simp
       apply (intro conjI)
       apply (meson rtranclp_cdcl_twl_restart_l_inp_twl_list_invs) 
       apply (meson rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l)
       apply simp
     done
  have inprocess_refine:
    \<open>SPEC (\<lambda>T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* x1g T \<and> count_decided (get_trail_l T) = 0)
    \<le> \<Down> {(x,y). (x,y) \<in> twl_st_l None \<and> twl_list_invs x \<and> twl_struct_invs y}
        (SPEC (\<lambda>T. cdcl_twl_inp\<^sup>*\<^sup>* x1c T \<and> count_decided (get_trail T) = 0))\<close>
    if 
      True and
      \<open>(x, y)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<times>\<^sub>f nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      nat_rel \<times>\<^sub>f
      bool_rel\<close> and
      \<open>x1b = (x1c, x2)\<close> and
      \<open>x1a = (x1b, x2a)\<close> and
      \<open>x1 = (x1a, x2b)\<close> and
      \<open>y = (x1, x2c)\<close> and
      \<open>x1f = (x1g, x2d)\<close> and
      \<open>x1e = (x1f, x2e)\<close> and
      \<open>x1d = (x1e, x2f)\<close> and
      \<open>x = (x1d, x2g)\<close> and
      \<open>restart_prog_pre x1c x2 x2a x2c\<close> and
      \<open>restart_abs_l_pre x1g x2d x2e x2g\<close>
    for x y x1 x1a x1b x1c x2 x2a x2b x2c x1d x1e x1f x1g x2d x2e x2f x2g b ba b2 b2a bb bc
    using that 
    apply (simp only: in_pair_collect_simp prod_rel_iff restart_prog_pre_def)
    apply (rule RES_refine)
    unfolding mem_Collect_eq
    apply normalize_goal+
    apply (rule rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp)
    apply assumption+
    apply (rule_tac x=V in bexI)
    apply (auto intro: rtranclp_cdcl_twl_restart_l_inp_twl_list_invs
      rtranclp_cdcl_twl_inp_twl_struct_invs)
    done
  show ?thesis
   supply [[goals_limit=1]]
    unfolding restart_abs_l_def restart_prog_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      restart_required_l_restart_required[THEN fref_to_Down_curry2]
      GC_required_l_GC_required[THEN fref_to_Down_curry2]
      cdcl_twl_restart_only_l_cdcl_twl_restart_only
      cdcl_twl_restart_l_cdcl_twl_restart
      cdcl_twl_restart_only_l_cdcl_twl_restart_only_spec
      cdcl_twl_restart_l_inp
      inprocessing_required_l_inprocessing_required[THEN fref_to_Down]
      )
    subgoal for Snb Snb'
      unfolding restart_abs_l_pre_def
      by (rule exI[of _ \<open>fst (fst (fst (fst (Snb'))))\<close>])
         simp
    subgoal by auto
    subgoal by auto
    subgoal by auto  \<comment> \<open>If condition\<close>
    subgoal by simp
    subgoal unfolding restart_prog_pre_def by auto
    subgoal by (auto simp: get_learned_clss_l_def)
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x1a x1b x1c x2 x2a x2b x2c x1d x1e x1f x1g x2d x2e x2f x2g b ba
      b2 b2a bb bc
      by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding restart_prog_pre_def by auto
    subgoal by (auto simp: get_learned_clss_l_def)
      apply (rule inprocess_refine; assumption)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: get_learned_clss_l_def)
    subgoal by auto
    done
qed


definition cdcl_twl_stgy_restart_abs_l_inv :: \<open>'v twl_st_l \<Rightarrow> bool \<times> 'v twl_st_l \<times> nat \<times> nat \<times> nat \<Rightarrow> bool\<close> where
  \<open>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 \<equiv> (\<lambda>(brk, T, last_GC, last_Restart, n).
    (\<exists>S\<^sub>0' T' n'.
       (T, T') \<in> twl_st_l None \<and>
       (S\<^sub>0, S\<^sub>0') \<in> twl_st_l None \<and>
       cdcl_twl_stgy_restart_prog_inv (S\<^sub>0', n') (brk, T', last_GC, last_Restart, n) \<and>
       clauses_to_update_l T = {#} \<and>
       twl_list_invs T))\<close>

definition cdcl_twl_stgy_restart_abs_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_abs_l S\<^sub>0 =
  do {
    (brk, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, m, p, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, m, p, n) \<leftarrow> restart_abs_l T m p n brk;
        RETURN (brk \<or> get_conflict_l T \<noteq> None, T, m, p, n)
      })
      (False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    RETURN T
  }\<close>

(* TODO Move *)
lemma (in -)prod_rel_fst_snd_iff: \<open>(x, y) \<in> A \<times>\<^sub>r B \<longleftrightarrow> (fst x, fst y) \<in> A \<and> (snd x, snd y) \<in> B\<close>
  by (cases x; cases y) auto

lemma cdcl_twl_stgy_restart_abs_l_cdcl_twl_stgy_restart_abs_l:
  \<open>(cdcl_twl_stgy_restart_abs_l, cdcl_twl_stgy_restart_prog) \<in>
     {(S :: 'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_abs_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg WHILEIT_refine[where R =
     \<open>bool_rel \<times>\<^sub>r {(S :: 'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_abs_l_restart_prog[THEN fref_to_Down_curry4])
  subgoal by (auto simp add: get_learned_clss_l_def)
  subgoal for x y xa x'
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def case_prod_beta
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd x')\<close> in exI)
    apply (rule_tac x=0 in exI)
    by (auto simp: prod_rel_fst_snd_iff)
  subgoal by auto
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by auto
  done

end


lemma cdcl_twl_full_restart_l_GC_prog_cdcl_twl_restart_l:
  assumes
    ST: \<open>(S, S') \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    stgy_invs: \<open>twl_stgy_invs S'\<close> and
    abs_pre: \<open>restart_prog_pre S' last_GC last_Restart brk\<close>
  shows \<open>cdcl_twl_full_restart_l_GC_prog S \<le> \<Down> Id (SPEC (\<lambda>T. cdcl_twl_restart_l S T))\<close>
proof -
  let ?f = \<open>(\<lambda>S T. cdcl_twl_restart_l S T)\<close>
  let ?f1 = \<open>\<lambda>S S'. (?f S S' \<or> S = S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?f1' = \<open>\<lambda>S S'. (?f S S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?f2 = \<open>\<lambda>S S'. ?f S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  let ?f3 = \<open>\<lambda>S S'. ?f1 S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using struct_invs ST unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: twl_st)
  then have alt_def: \<open>SPEC (\<lambda>T. cdcl_twl_restart_l S T) \<ge> do {
    S' \<leftarrow> SPEC (\<lambda>S'. ?f1 S S');
    T \<leftarrow> SPEC (?f2 S');
    U \<leftarrow> SPEC (?f3 T);
    V \<leftarrow> SPEC (\<lambda>V. ?f3 U V);
    RETURN V
    }\<close>
    unfolding RETURN_def RES_RES_RETURN_RES apply -
    apply (rule RES_rule)
    unfolding UN_iff
    apply (elim bexE)+
    unfolding mem_Collect_eq
    by (metis (full_types) cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l singletonD)

  have 1: \<open>remove_one_annot_true_clause_imp T \<le> SPEC (\<lambda>V. ?f2 U V)\<close>
    if
      \<open>(T, U) \<in> Id\<close> and
      \<open>U \<in> Collect (\<lambda>S'. ?f1 S S')\<close>
    for T U
  proof -
    have \<open>T = U\<close> and \<open>?f S T \<or> S = T\<close> and count_0: \<open>count_decided (get_trail_l T) = 0\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T' where
      TT': \<open>(T, T') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T\<close> and
      struct_invs: \<open>twl_struct_invs T'\<close> and
      clss_upd: \<open>clauses_to_update_l T = {#}\<close> and
      \<open>cdcl_twl_restart S' T' \<or> S' = T'\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close>
      by blast
   show ?thesis
      unfolding \<open>T = U\<close>[symmetric]
      by (rule remove_one_annot_true_clause_imp_spec_lev0[OF TT' list_invs struct_invs confl
          clss_upd, THEN order_trans])
       (use count_0 remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF TT' list_invs struct_invs
           confl clss_upd] n_d \<open>?f S T \<or> S = T\<close>
           remove_one_annot_true_clause_map_mark_of_same_or_0[of T] in
         \<open>auto dest: cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
           simp: rtranclp_remove_one_annot_true_clause_count_dec\<close>)
  qed

  have mark_to_delete_clauses_l_pre: \<open>mark_to_delete_clauses_l_pre U\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close>
    for T T' U U'
  proof -
    have \<open>T = T'\<close> \<open>U = U'\<close> and \<open>?f T U\<close> and \<open>?f S T \<or> S = T\<close>
      using that by auto
    then have \<open>?f S U \<or> S = U\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast
    have confl: \<open>get_conflict_l U = None\<close>
      using \<open>?f T U\<close> \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain U' where
      TT': \<open>(U, U') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs U\<close> and
      struct_invs: \<open>twl_struct_invs U'\<close> and
      clss_upd: \<open>clauses_to_update_l U = {#}\<close> and
      \<open>cdcl_twl_restart S' U' \<or> S' = U'\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of U] \<open>?f S U \<or> S = U\<close> assms that[of S']
      by blast
    then show ?thesis
      unfolding mark_to_delete_clauses_l_pre_def
      by blast
  qed
  have 2: \<open>mark_to_delete_clauses_l U \<le> SPEC (\<lambda>V. ?f3 U' V)\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      UU': \<open>(U, U') \<in> Id\<close> and
      U: \<open>U' \<in> Collect (?f2 T')\<close> and
      pre: \<open>mark_to_delete_clauses_l_pre U\<close>
    for T T' U U'
  proof -
    have \<open>T = T'\<close> \<open>U = U'\<close> and \<open>?f T U\<close> and \<open>?f S T \<or> S = T\<close>
      using that by auto
    then have SU: \<open>?f S U\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast
    obtain V where
      TV: \<open>(U, V) \<in> twl_st_l None\<close> and
      struct: \<open>twl_struct_invs V\<close> and
      list_invs: \<open>twl_list_invs U\<close>
      using pre unfolding mark_to_delete_clauses_l_pre_def
      by auto
    have confl: \<open>get_conflict_l U = None\<close> and upd: \<open>clauses_to_update_l U = {#}\<close> and UU[simp]: \<open>U' = U\<close>
      using U UU' \<open>?f T U\<close> confl  \<open>?f S T \<or> S = T\<close> assms
      by (auto simp: cdcl_twl_restart_l.simps)
    show ?thesis
      by (rule mark_to_delete_clauses_l_spec[OF TV list_invs struct confl upd, THEN order_trans],
         subst Down_id_eq)
       (use remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF TV list_invs struct confl upd]
          cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of T] that
          ST in \<open>auto dest!: cdcl_twl_restart_l_count_dec\<close>)
  qed
  have 3: \<open>cdcl_GC_clauses V \<le> SPEC (?f3 V')\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close> and
      \<open>mark_to_delete_clauses_l_pre U\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>V' \<in> Collect (?f3 U')\<close>
    for T T' U U' V V'
  proof -
    have eq: \<open>U' = U\<close>
      using that by auto
    have st: \<open>T = T'\<close> \<open>U = U'\<close> \<open>V = V'\<close> and \<open>?f S T \<or> S = T\<close> and \<open>?f T U\<close> and
       \<open>?f U V \<or> U = V\<close> and
      le_UV: \<open>length (get_trail_l U) = length (get_trail_l V)\<close> and
      mark0: \<open>\<forall>L\<in>set (get_trail_l V'). mark_of L = 0\<close> and
      count_dec: \<open>count_decided (get_trail_l V') = 0\<close>
      using that by (auto dest!: cdcl_twl_restart_l_count_dec)
    then have \<open>?f S V\<close>
      using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
      by blast
    have mark: \<open>mark_of (get_trail_l V ! i) = 0\<close> if \<open>i < length (get_trail_l V)\<close> for i
      using that
      by (use st that le_UV count_dec mark0 in
        \<open>auto simp: count_decided_0_iff is_decided_no_proped_iff\<close>)
    then have count_dec: \<open>count_decided (get_trail_l V') = 0\<close> and
      mark: \<open>\<And>L. L \<in> set (get_trail_l V') \<Longrightarrow> mark_of L = 0\<close>
      using cdcl_twl_restart_l_count_dec[of U V] that \<open>?f U V \<or> U = V\<close>
      by (auto dest!: cdcl_twl_restart_l_count_dec)
    obtain W where
      UV: \<open>(V, W) \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs V\<close> and
      clss: \<open>clauses_to_update_l V = {#}\<close> and
      \<open>cdcl_twl_restart S' W\<close> and
      struct: \<open>twl_struct_invs W\<close>
      using cdcl_twl_restart_l_invs[OF assms(1,2,3) \<open>?f S V\<close>] unfolding eq by blast
    have confl: \<open>get_conflict_l V = None\<close>
      using \<open>?f S V\<close> unfolding eq
      by (auto simp: cdcl_twl_restart_l.simps)
    show ?thesis
      unfolding eq
      by (rule cdcl_GC_clauses_cdcl_twl_restart_l[OF UV list_invs struct confl clss, THEN order_trans])
       (use count_dec cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of U']
         \<open>?f S V\<close> eq mark in \<open>auto simp: \<open>V = V'\<close>\<close>)
  qed
  have cdcl_twl_restart_l: \<open>cdcl_twl_restart_l S W\<close>
    if
      \<open>(T, T') \<in> Id\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>U' \<in> Collect (?f2 T')\<close> and
      \<open>mark_to_delete_clauses_l_pre U\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>V' \<in> Collect (?f3 U')\<close> and
      \<open>(W, W') \<in> Id\<close> and
      \<open>W' \<in> Collect (?f3 V')\<close>
    for T T' U U' V V' W W'
    using n_d cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S T U]
      cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S U V]
      cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[of S V W] that
    by fast
  have abs_pre: \<open>restart_abs_l_pre S last_GC last_Restart False\<close>
    using assms unfolding cdcl_twl_full_restart_l_GC_prog_pre_def restart_abs_l_pre_def
      restart_prog_pre_def apply -
    apply (rule exI[of _ S'])
    by auto

  show ?thesis
    unfolding cdcl_twl_full_restart_l_GC_prog_def
    apply (rule order_trans)
    prefer 2 apply (rule ref_two_step')
    apply (rule alt_def)
    apply refine_rcg
    subgoal
      using assms unfolding cdcl_twl_full_restart_l_GC_prog_pre_def restart_prog_pre_def
      by fastforce
    subgoal
      by (rule cdcl_twl_local_restart_l_spec0_cdcl_twl_restart_l[THEN order_trans, OF abs_pre])
        auto
    subgoal
      by (rule 1)
    subgoal for  T T' U U'
      by (rule mark_to_delete_clauses_l_pre)
    subgoal for T T' U U'
      by (rule 2)
    subgoal for T T' U U' V V'
      by (rule 3)
    subgoal for T T' U U' V V' W W'
      by (rule cdcl_twl_restart_l)
    done
qed


lemma cdcl_twl_full_restart_inprocess_l_cdcl_twl_restart_l:
  assumes
    ST: \<open>(S, S') \<in> twl_st_l None\<close> and
    list_invs: \<open>twl_list_invs S\<close> and
    struct_invs: \<open>twl_struct_invs S'\<close> and
    confl: \<open>get_conflict_l S = None\<close> and
    upd: \<open>clauses_to_update_l S = {#}\<close> and
    stgy_invs: \<open>twl_stgy_invs S'\<close> and
    abs_pre: \<open>restart_prog_pre S' last_GC last_Restart brk\<close>
  shows \<open>cdcl_twl_full_restart_inprocess_l S \<le> \<Down> Id (SPEC (\<lambda>T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail_l T) = 0))\<close> (is \<open>_ \<le> \<Down> _ ?P\<close>)
proof -
  let ?f = \<open>(\<lambda>S T. cdcl_twl_restart_l S T)\<close>
  let ?f1 = \<open>\<lambda>S S'. (?f S S' \<or> S = S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?f1' = \<open>\<lambda>S S'. (?f S S') \<and> count_decided (get_trail_l S') = 0\<close>
  let ?finp = \<open>\<lambda>S S'. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S S' \<and>  count_decided (get_trail_l S') = 0\<close>
  let ?f2 = \<open>\<lambda>S S'. ?f S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  let ?f3 = \<open>\<lambda>S S'. ?f1 S S' \<and> (\<forall>L \<in> set (get_trail_l S'). mark_of L = 0) \<and>
    length (get_trail_l S) = length (get_trail_l S')\<close>
  have n_d: \<open>no_dup (get_trail_l S)\<close>
    using struct_invs ST unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def pcdcl_all_struct_invs_def
    by (simp add: twl_st)
  then have alt_def: \<open>?P \<ge> do {
    S' \<leftarrow> SPEC (?f1 S);
    T \<leftarrow> SPEC (?finp S');
    if(get_conflict_l T \<noteq> None) then
      RETURN T
    else do {
        T \<leftarrow> SPEC (?f2 T);
        U \<leftarrow> SPEC (?f3 T);
        V \<leftarrow> SPEC (\<lambda>V. ?f3 U V);
        RETURN V
      }
    }\<close>
    unfolding RETURN_def RES_RES_RETURN_RES apply -
    apply refine_vcg
    apply (metis (no_types, hide_lams) cdcl_twl_restart_l_inp.intros(1) converse_rtranclp_into_rtranclp empty_iff insert_iff)
    apply simp
      apply (elim UN_E)+
      unfolding mem_Collect_eq
      apply (smt (z3) cdcl_twl_restart_l_inp.intros(1) converse_rtranclp_into_rtranclp rtranclp.rtrancl_into_rtrancl singletonD)
      apply (elim UN_E)+
      unfolding mem_Collect_eq
      apply (metis (no_types, hide_lams) singletonD)
    done

  have 1: \<open>remove_one_annot_true_clause_imp U \<le> SPEC (?f2 U')\<close>
    if 
      \<open>cdcl_twl_full_restart_l_GC_prog_pre S\<close> and
      \<open>T' \<in> Collect (?f1 S)\<close>  and
      \<open>U' \<in> Collect (?finp T')\<close> and
      confl_U': \<open>\<not>get_conflict_l U' \<noteq> None\<close> and
      \<open>(T, T') \<in> Id\<close> and
      \<open>(U, U') \<in> Id\<close>
      for T T' U U'
  proof -
    have \<open>T = T'\<close> \<open>U=U'\<close> and \<open>?f S T \<or> S = T\<close> and
      count_0: \<open>count_decided (get_trail_l T) = 0\<close> and
      T'U': \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* T' U'\<close> and
      count_0_U: \<open>count_decided (get_trail_l U') = 0\<close> and
      confl_U': \<open>get_conflict_l U' = None\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T'' where
      TT': \<open>(T', T'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T'\<close> and
      struct_invs: \<open>twl_struct_invs T''\<close> and
      clss_upd: \<open>clauses_to_update_l T' = {#}\<close> and
      \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close> unfolding  \<open>T = T'\<close>
      by blast

    have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T'')\<close>
      using \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close> abs_pre cdcl_twl_inp.intros(5)
        cdcl_twl_inp_invs(3) restart_prog_pre_def by blast
    obtain U'' where
      U'U'': \<open>(U', U'') \<in> twl_st_l None\<close> and
      \<open>cdcl_twl_inp\<^sup>*\<^sup>* T'' U''\<close>
      using rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[OF T'U' TT' list_invs struct_invs
        ent] by blast
    then have
      list_invs: \<open>twl_list_invs U'\<close> and
      struct_invs: \<open>twl_struct_invs U''\<close> and
      clss_upd: \<open>clauses_to_update_l U' = {#}\<close>
      using T'U' ent
      by (auto intro:  list_invs rtranclp_cdcl_twl_restart_l_inp_twl_list_invs
          rtranclp_cdcl_twl_inp_invs struct_invs
        clss_upd rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l
       simp: \<open>U = U'\<close>)

   show ?thesis
     unfolding \<open>T = T'\<close>[symmetric] \<open>U=U'\<close>
      by (rule remove_one_annot_true_clause_imp_spec_lev0[OF U'U'' list_invs struct_invs confl_U'
        clss_upd, THEN order_trans])
       (use count_0 remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF U'U'' list_invs
          struct_invs confl_U' clss_upd] n_d \<open>?f S T \<or> S = T\<close> count_0_U
           remove_one_annot_true_clause_map_mark_of_same_or_0[of T] in
         \<open>auto dest: cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l
           simp: rtranclp_remove_one_annot_true_clause_count_dec\<close>)
  qed

  have mark_to_delete_clauses_l_pre: \<open>mark_to_delete_clauses_l_pre V\<close>
    if
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>U' \<in> Collect (?finp T')\<close> and
      confl_U': \<open>\<not>get_conflict_l U' \<noteq> None\<close> and
      \<open>V' \<in> Collect (?f2 U')\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>(T, T') \<in> Id\<close> and
      \<open>(U, U') \<in> Id\<close>
    for T T' U U' V V'
  proof -
    have \<open>T = T'\<close> \<open>U=U'\<close> \<open>V'=V\<close> and \<open>?f S T \<or> S = T\<close> and
      count_0: \<open>count_decided (get_trail_l T) = 0\<close> and
      T'U': \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* T' U'\<close> and
      count_0_U: \<open>count_decided (get_trail_l U') = 0\<close> and
      confl_U': \<open>get_conflict_l U' = None\<close> and
      UV: \<open>cdcl_twl_restart_l U' V\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T'' where
      TT': \<open>(T', T'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T'\<close> and
      struct_invs: \<open>twl_struct_invs T''\<close> and
      clss_upd: \<open>clauses_to_update_l T' = {#}\<close> and
      \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close> unfolding  \<open>T = T'\<close>
      by blast

    have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T'')\<close>
      using \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close> abs_pre cdcl_twl_inp.intros(5)
        cdcl_twl_inp_invs(3) restart_prog_pre_def by blast
    obtain U'' where
      U'U'': \<open>(U', U'') \<in> twl_st_l None\<close> and
      \<open>cdcl_twl_inp\<^sup>*\<^sup>* T'' U''\<close>
      using rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[OF T'U' TT' list_invs struct_invs
        ent] by blast
    then have
      list_invs: \<open>twl_list_invs U'\<close> and
      struct_invs: \<open>twl_struct_invs U''\<close> and
      clss_upd: \<open>clauses_to_update_l U' = {#}\<close>
      using T'U' ent
      by (auto intro:  list_invs rtranclp_cdcl_twl_restart_l_inp_twl_list_invs
          rtranclp_cdcl_twl_inp_invs struct_invs
        clss_upd rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l
       simp: \<open>U = U'\<close>)
    obtain V'' where
      \<open>(V, V'') \<in> twl_st_l None\<close>
      \<open>twl_list_invs V\<close>
      \<open>clauses_to_update_l V = {#}\<close>
      \<open>cdcl_twl_restart U'' V''\<close>
      \<open>twl_struct_invs V''\<close>
      using cdcl_twl_restart_l_invs[OF U'U'' list_invs struct_invs UV]
      by blast
    then show ?thesis
      unfolding mark_to_delete_clauses_l_pre_def  \<open>U=U'\<close>
      by blast
  qed

  
  have 2:  \<open>mark_to_delete_clauses_l V \<le> SPEC (?f3 V')\<close>
    if
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>U' \<in> Collect (?finp T')\<close> and
      confl_U': \<open>\<not>get_conflict_l U' \<noteq> None\<close> and
      \<open>V' \<in> Collect (?f2 U')\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>(T, T') \<in> Id\<close> and
      \<open>(U, U') \<in> Id\<close>
    for T T' U U' V V'
  proof -
    have \<open>T = T'\<close> \<open>U=U'\<close> \<open>V'=V\<close> and \<open>?f S T \<or> S = T\<close> and
      count_0: \<open>count_decided (get_trail_l T) = 0\<close> and
      T'U': \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* T' U'\<close> and
      count_0_U: \<open>count_decided (get_trail_l U') = 0\<close> and
      confl_U': \<open>get_conflict_l U' = None\<close> and
      UV: \<open>cdcl_twl_restart_l U' V\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T'' where
      TT': \<open>(T', T'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T'\<close> and
      struct_invs: \<open>twl_struct_invs T''\<close> and
      clss_upd: \<open>clauses_to_update_l T' = {#}\<close> and
      \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close> unfolding  \<open>T = T'\<close>
      by blast

    have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T'')\<close>
      using \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close> abs_pre cdcl_twl_inp.intros(5)
        cdcl_twl_inp_invs(3) restart_prog_pre_def by blast
    obtain U'' where
      U'U'': \<open>(U', U'') \<in> twl_st_l None\<close> and
      \<open>cdcl_twl_inp\<^sup>*\<^sup>* T'' U''\<close>
      using rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[OF T'U' TT' list_invs struct_invs
        ent] by blast
    then have
      list_invs: \<open>twl_list_invs U'\<close> and
      struct_invs: \<open>twl_struct_invs U''\<close> and
      clss_upd: \<open>clauses_to_update_l U' = {#}\<close>
      using T'U' ent
      by (auto intro:  list_invs rtranclp_cdcl_twl_restart_l_inp_twl_list_invs
          rtranclp_cdcl_twl_inp_invs struct_invs
        clss_upd rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l
       simp: \<open>U = U'\<close>)
    obtain V'' where
      VV'': \<open>(V, V'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs V\<close> and
      upd: \<open>clauses_to_update_l V = {#}\<close> and
      U''V'': \<open>cdcl_twl_restart U'' V''\<close> and
      struct_invs: \<open>twl_struct_invs V''\<close>
      using cdcl_twl_restart_l_invs[OF U'U'' list_invs struct_invs UV]
      by blast
    have confl: \<open>get_conflict_l V = None\<close>
      using U''V'' VV'' confl_U' U'U''
      by (auto simp: cdcl_twl_restart.simps  \<open>U=U'\<close> \<open>V'=V\<close>
          twl_st_l_def)
    show ?thesis
      by (rule mark_to_delete_clauses_l_spec[OF VV'' list_invs struct_invs confl upd,
    THEN order_trans],
        subst Down_id_eq)
       (use confl remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF VV'' list_invs struct_invs _ upd]
        cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of T] that
        ST in \<open>auto dest!: cdcl_twl_restart_l_count_dec\<close>)
  qed

  have 3: \<open>cdcl_GC_clauses W \<le> SPEC (?f3 W')\<close>
    if
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>U' \<in> Collect (?finp T')\<close> and
      confl_U': \<open>\<not>get_conflict_l U' \<noteq> None\<close> and
      V': \<open>V' \<in> Collect (?f2 U')\<close> and
      \<open>W' \<in> Collect (?f3 V')\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>(T, T') \<in> Id\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>(W, W') \<in> Id\<close>
    for T T' U U' V V' W W'
  proof -
    have eq: \<open>T = T'\<close> \<open>U=U'\<close> \<open>V'=V\<close> \<open>W=W'\<close> and
      \<open>?f S T \<or> S = T\<close> and
      count_0: \<open>count_decided (get_trail_l T) = 0\<close> and
      T'U': \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* T' U'\<close> and
      count_0_U: \<open>count_decided (get_trail_l U') = 0\<close> and
      confl_U': \<open>get_conflict_l U' = None\<close> and
      UV: \<open>cdcl_twl_restart_l U' V\<close> and
      VW: \<open>?f V W' \<or> V = W'\<close> and
      mark: \<open>\<forall>L\<in>set (get_trail_l W'). mark_of L = 0\<close>
      using that by auto
    have confl: \<open>get_conflict_l T = None\<close>
      using \<open>?f S T \<or> S = T\<close> confl
      by (auto simp: cdcl_twl_restart_l.simps)
    obtain T'' where
      TT': \<open>(T', T'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs T'\<close> and
      struct_invs: \<open>twl_struct_invs T''\<close> and
      clss_upd: \<open>clauses_to_update_l T' = {#}\<close> and
      \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close>
      using cdcl_twl_restart_l_invs[OF assms(1-3), of T] assms
        \<open>?f S T \<or> S = T\<close> unfolding  \<open>T = T'\<close>
      by blast

    have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T'')\<close>
      using \<open>cdcl_twl_restart S' T'' \<or> S' = T''\<close> abs_pre cdcl_twl_inp.intros(5)
        cdcl_twl_inp_invs(3) restart_prog_pre_def by blast
    obtain U'' where
      U'U'': \<open>(U', U'') \<in> twl_st_l None\<close> and
      \<open>cdcl_twl_inp\<^sup>*\<^sup>* T'' U''\<close>
      using rtranclp_cdcl_twl_restart_l_inp_cdcl_twl_restart_inp[OF T'U' TT' list_invs struct_invs
        ent] by blast
    then have
      list_invs: \<open>twl_list_invs U'\<close> and
      struct_invs: \<open>twl_struct_invs U''\<close> and
      clss_upd: \<open>clauses_to_update_l U' = {#}\<close>
      using T'U' ent
      by (auto intro:  list_invs rtranclp_cdcl_twl_restart_l_inp_twl_list_invs
          rtranclp_cdcl_twl_inp_invs struct_invs
        clss_upd rtranclp_cdcl_twl_restart_l_inp_clauses_to_update_l
       simp: \<open>U = U'\<close>)
    obtain V'' where
      VV'': \<open>(V, V'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs V\<close> and
      upd: \<open>clauses_to_update_l V = {#}\<close> and
      U''V'': \<open>cdcl_twl_restart U'' V''\<close> and
      struct_invs: \<open>twl_struct_invs V''\<close>
      using cdcl_twl_restart_l_invs[OF U'U'' list_invs struct_invs UV]
      by blast
    have confl: \<open>get_conflict_l V = None\<close>
      using U''V'' VV'' confl_U' U'U''
     by (auto simp: cdcl_twl_restart.simps  \<open>U=U'\<close> \<open>V'=V\<close>
          twl_st_l_def)
    have count_0_V: \<open>count_decided (get_trail_l V) = 0\<close>
      using count_0_U V' U'U'' unfolding eq
      by (auto dest!: cdcl_twl_restart_l_count_dec)
    obtain W'' where
      VW'': \<open>(W, W'') \<in> twl_st_l None\<close> and
      list_invs: \<open>twl_list_invs W\<close> and
      upd: \<open>clauses_to_update_l W = {#}\<close> and
      U''W'': \<open>cdcl_twl_restart V'' W'' \<or> V = W\<close> and
      struct_invs: \<open>twl_struct_invs W''\<close>
      using cdcl_twl_restart_l_invs[OF VV'' list_invs struct_invs, of W]
        list_invs struct_invs upd VV''
        VW unfolding eq
      by blast
    have confl_W: \<open>get_conflict_l W = None\<close> and
      count_0_W: \<open>count_decided (get_trail_l W) = 0\<close>
      by (use confl U''W'' VW'' VV'' count_0_V in
        \<open>auto simp: eq twl_st_l_def cdcl_twl_restart.simps\<close>)[]
       (use VW VV'' VW'' count_0_V in \<open>auto dest!: cdcl_twl_restart_l_count_dec simp: eq\<close>)

    show ?thesis
      unfolding eq[symmetric]
      by (rule cdcl_GC_clauses_cdcl_twl_restart_l[OF VW'' list_invs struct_invs confl_W upd,
           THEN order_trans])
       (use count_0_W mark
        cdcl_twl_restart_l_cdcl_twl_restart_l_is_cdcl_twl_restart_l[OF _ _ n_d, of U']
       eq  in \<open>auto simp: \<open>V = V'\<close>\<close>)
  qed
    
  have cdcl_twl_restart_l: \<open>cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S X\<close>
    if
      \<open>T' \<in> Collect (?f1 S)\<close> and
      \<open>U' \<in> Collect (?finp T')\<close> and
      confl_U': \<open>\<not>get_conflict_l U' \<noteq> None\<close> and
      V': \<open>V' \<in> Collect (?f2 U')\<close> and
      \<open>W' \<in> Collect (?f3 V')\<close> and
      \<open>X' \<in> Collect (?f3 W')\<close> and
      \<open>(V, V') \<in> Id\<close> and
      \<open>(T, T') \<in> Id\<close> and
      \<open>(U, U') \<in> Id\<close> and
      \<open>(W, W') \<in> Id\<close> and
      \<open>(X,X') \<in> Id\<close>
    for T T' U U' V V' W W' X X'
    using that unfolding mem_Collect_eq
    by (auto dest!: cdcl_twl_restart_l_inp.intros)

  have abs_l_pre: \<open>restart_abs_l_pre S last_GC last_Restart False\<close>
    using assms unfolding restart_abs_l_pre_def
      restart_prog_pre_def apply -
    apply (rule exI[of _ S'])
    by auto

  have simplify_clauses_with_unit_st:
    \<open>simplify_clauses_with_unit_st T \<le> SPEC (?finp U)\<close>
    if 
      pre: \<open>cdcl_twl_full_restart_l_GC_prog_pre S\<close> and
      \<open>(T, U) \<in> Id\<close> and
      \<open>U \<in> Collect (?f1 S)\<close>
   for T U
 proof -
   have st: \<open>T = U\<close> and
     SU: \<open>S=U \<or> cdcl_twl_restart_l S U\<close> and
     lev0: \<open>count_decided (get_trail_l U) = 0\<close>
     using that by (auto dest!: cdcl_twl_restart_l_count_dec)

   have confl: \<open>get_conflict_l U = None \<close>and
     clss: \<open>clauses_to_update_l U = {#}\<close>
     using pre SU upd
     using confl SU upd by (auto simp add: cdcl_twl_full_restart_l_GC_prog_pre_def
       cdcl_twl_restart_l.simps)

   obtain V where
     UV: \<open>(U, V) \<in> twl_st_l None\<close> and
     struct: \<open>twl_struct_invs V\<close> and
     list_invs: \<open>twl_list_invs U\<close> and
     SUV: \<open>S = U \<or> cdcl_twl_restart S' V\<close>
     using ST cdcl_twl_restart_l_invs[OF ST list_invs struct_invs] list_invs SU struct_invs
       assms by blast

   have ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S')\<close>
      using assms(7) unfolding restart_prog_pre_def by blast
   have 
     ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of V)\<close>
     using cdcl_twl_restart_entailed_init[unfolded state\<^sub>W_of_def[symmetric], of S' V]
       ent SUV UV ST by (auto simp: twl_st_l_def
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)

    show ?thesis
      apply (rule simplify_clauses_with_unit_st_spec[THEN order_trans, of _ V])
      apply (use lev0 UV struct list_invs st confl clss ent in auto)[7]
      apply (auto dest: rtranclp_cdcl_twl_inprocessing_l_cdcl_twl_l_inp
          rtranclp_cdcl_twl_inprocessing_l_count_dec simp: st lev0)
      done
  qed
  show ?thesis
    unfolding cdcl_twl_full_restart_inprocess_l_def
    apply (rule order_trans)
    prefer 2 apply (rule ref_two_step')
    apply (rule alt_def)
    apply refine_rcg
    subgoal
      using assms unfolding cdcl_twl_full_restart_l_GC_prog_pre_def restart_prog_pre_def
      by fastforce
    subgoal
      by (rule cdcl_twl_local_restart_l_spec0_cdcl_twl_restart_l[THEN order_trans, OF abs_l_pre])
        auto
    subgoal for T U
      by (rule simplify_clauses_with_unit_st)
    subgoal by auto 
    subgoal for T T' U U'
      by (rule 1)
    subgoal for T T' U U' V V'
      by (rule mark_to_delete_clauses_l_pre)
    subgoal for U U'
      by (rule 2)
    subgoal for U U' V V'
      by (rule 3)
    subgoal for U U' V V' W W'
      by (rule cdcl_twl_restart_l)
    done
qed


context twl_restart_ops
begin

definition restart_prog_l
  :: "'v twl_st_l \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st_l \<times> nat \<times> nat \<times> nat) nres"
where
  \<open>restart_prog_l S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_l_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required_l S last_GC n;
     b2 \<leftarrow> restart_required_l S last_Restart n;
     if b2 \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_l_prog S;
       RETURN (T, last_GC, size (get_all_learned_clss_l T), n)
     }
     else if b \<and> \<not>brk then do {
       inp \<leftarrow> inprocessing_required_l S;
       if \<not>inp then do {
         b \<leftarrow> SPEC(\<lambda>_. True);
         T \<leftarrow> (if b then cdcl_twl_full_restart_l_prog S else cdcl_twl_full_restart_l_GC_prog S);
         RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
       else do {
         T \<leftarrow> cdcl_twl_full_restart_inprocess_l S;
         RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
     }
     else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>

lemma restart_prog_l_alt_def:
     \<open>restart_prog_l S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_l_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required_l S last_GC n;
     b2 \<leftarrow> restart_required_l S last_Restart n;
     if b2 \<and> \<not>brk then do {
       T \<leftarrow> cdcl_twl_restart_l_prog S;
       RETURN (T, last_GC, size (get_all_learned_clss_l T), n)
     }
     else if b \<and> \<not>brk then do {
       inp \<leftarrow> inprocessing_required_l S;
       if \<not>inp then do {
         b \<leftarrow> SPEC(\<lambda>_. True);
         T \<leftarrow> (if b then cdcl_twl_full_restart_l_prog S else cdcl_twl_full_restart_l_GC_prog S);
         RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
       else do {
         T \<leftarrow> cdcl_twl_full_restart_inprocess_l S;
         T \<leftarrow> RETURN T;
         RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
     }
     else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>
   by (auto simp: restart_prog_l_def cong: if_cong)

lemma restart_prog_l_restart_abs_l:
  \<open>(uncurry4 restart_prog_l, uncurry4 restart_abs_l)
  \<in> {(S:: 'v twl_st_l, S'). (S, S') \<in> Id \<and> twl_list_invs S \<and> clauses_to_update_l S  = {#}}  \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
    \<langle>{(S:: 'v twl_st_l, S'). (S, S') \<in> Id \<and> twl_list_invs S \<and> clauses_to_update_l S  = {#}}  \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close> (is \<open>_ \<in> ?R  \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f _\<close>)
proof -
  have cdcl_twl_full_restart_l_prog:
    \<open>cdcl_twl_full_restart_l_prog S \<le> SPEC (\<lambda>T. cdcl_twl_restart_l S T)\<close>
    if
      inv: \<open>restart_abs_l_pre S last_GC last_Restart brk\<close> and
      \<open>(b, ba) \<in> bool_rel\<close> and
      \<open>b \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      \<open>ba \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      brk: \<open>\<not>brk\<close>
    for b ba S brk n last_GC last_Restart
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      using cdcl_twl_full_restart_l_prog_spec[OF ST list_invs struct_invs
         confl upd]
        remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF ST list_invs struct_invs
         confl upd]
      by (rule conc_trans_additional)
  qed
  have cdcl_twl_full_restart_l_GC_prog:
    \<open>cdcl_twl_full_restart_l_GC_prog S \<le> SPEC (cdcl_twl_restart_l S)\<close>
    if
      inv: \<open>restart_abs_l_pre S last_GC last_Restart brk\<close> and
      brk: \<open>ba \<and> b2a \<and> \<not> brk\<close>
    for ba b2a brk S last_GC last_Restart
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close> and
      inv2: \<open>restart_prog_pre T last_GC last_Restart brk\<close> and
      ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      by (rule cdcl_twl_full_restart_l_GC_prog_cdcl_twl_restart_l[unfolded Down_id_eq, OF ST list_invs
        struct_invs confl upd stgy_invs inv2])
  qed

  have restart_abs_l_alt_def:
  \<open>restart_abs_l S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_l_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required_l S last_GC n;
     b2 \<leftarrow> restart_required_l S last_Restart n;
     if b2 \<and>  \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only_l S T);
       RETURN (T, last_GC, size (get_all_learned_clss_l T), n)
     }
     else
     if b \<and> \<not>brk then do {
       inp \<leftarrow> inprocessing_required_l S;
     if \<not>inp then do {
       _ \<leftarrow> SPEC(\<lambda>_::bool. True);
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l S T);
       RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
       else do {
       T \<leftarrow> SPEC (\<lambda>T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail_l T) = 0);
       T \<leftarrow> SPEC(cdcl_twl_restart_l T);
       RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
       }
     }
     else
       RETURN (S, last_GC, last_Restart, n)
       }\<close> for  S last_GC last_Restart n brk
     unfolding restart_abs_l_def
     by (auto cong: if_cong)
   have cdcl_twl_full_restart_inprocess_l:
     \<open>cdcl_twl_full_restart_inprocess_l S \<le> SPEC (\<lambda>T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail_l T) = 0)\<close>
     if
       inv: \<open>restart_abs_l_pre S last_GC last_Restart brk\<close> and
       brk: \<open>ba \<and> b2a \<and> \<not> brk\<close>
     for ba b2a brk S last_GC last_Restart
   proof -
     obtain T where
       ST: \<open>(S, T) \<in> twl_st_l None\<close> and
       struct_invs: \<open>twl_struct_invs T\<close> and
       list_invs: \<open>twl_list_invs S\<close> and
       upd: \<open>clauses_to_update_l S = {#}\<close> and
       stgy_invs: \<open>twl_stgy_invs T\<close> and
       confl: \<open>get_conflict_l S = None\<close> and
       inv2: \<open>restart_prog_pre T last_GC last_Restart brk\<close> and
       ent_init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
       using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
       apply - apply normalize_goal+
       by (auto simp: twl_st)
     show ?thesis
       by (rule cdcl_twl_full_restart_inprocess_l_cdcl_twl_restart_l[THEN order_trans,
         OF ST list_invs struct_invs confl upd stgy_invs inv2])
         auto
    qed

   have [simp]: \<open>cdcl_twl_restart_only_l S Ta \<Longrightarrow>clauses_to_update_l Ta = {#}\<close> for S Ta
     by (auto simp: cdcl_twl_restart_only_l.simps)
   have [simp]: \<open>cdcl_twl_restart_l S Ta \<Longrightarrow>clauses_to_update_l Ta = {#}\<close> for S Ta
     by (auto simp: cdcl_twl_restart_l.simps)
   have \<open>(get_conflict_l T \<noteq> None) \<or> cdcl_twl_restart_l T' T\<close>
     if 
       \<open>restart_abs_l_pre S p m brk\<close> and
       \<open>restart_abs_l_pre S p m brk\<close> and
       \<open>(b, ba) \<in> bool_rel\<close> and
       \<open>(b2, b2a) \<in> bool_rel\<close> and
       \<open>\<not> (b2 \<and> \<not> brk)\<close> and
       \<open>\<not> (b2a \<and> \<not> brk)\<close> and
       \<open>b \<and> \<not> brk\<close> and
       \<open>ba \<and> \<not> brk\<close> and
       \<open>(inp, inp') \<in> bool_rel\<close> and
       \<open>\<not> \<not> inp\<close> and
       \<open>\<not> \<not> inp'\<close> and
       TT': \<open>(T, T') \<in> Id\<close> and
       T': \<open>T' \<in> {T. cdcl_twl_restart_l_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail_l T) = 0}\<close>
     for b ba b2 b2a inp inp' T T' S p m brk
   proof -
     have eq: \<open>T = T'\<close>
       using TT' by auto
         find_theorems "?a \<or> _" "\<not>?a"
     show ?thesis
       unfolding eq
       apply (subst imp_conv_disj[symmetric], rule impI)
       apply (rule cdcl_twl_restart_l_refl)
         using T' apply auto
       sorry
   qed
   have \<open>restart_prog_l S p m n brk \<le> \<Down> (?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel)
       (restart_abs_l S p m n brk)\<close> for S n brk p m
    unfolding restart_prog_l_alt_def restart_abs_l_alt_def restart_required_l_def cdcl_twl_restart_l_prog_def
    apply (refine_vcg)
    subgoal by auto
    subgoal
      by (rule cdcl_twl_local_restart_l_spec_cdcl_twl_restart_l[THEN order_trans])
        (auto simp: conc_fun_RES)
    subgoal by (auto intro: cdcl_twl_restart_only_l_list_invs
      simp: restart_abs_l_pre_def)
    subgoal by auto
    subgoal by auto
    subgoal by (rule cdcl_twl_full_restart_l_prog) auto
    subgoal by (rule cdcl_twl_full_restart_l_GC_prog) auto
    subgoal by (auto simp: cdcl_twl_restart_l_list_invs
      simp: restart_abs_l_pre_def)
    subgoal by (rule cdcl_twl_full_restart_inprocess_l, assumption, auto)
    subgoal for b ba b2 b2a inp inp' T T'
      explore_have
      sorry
    subgoal by (auto simp: cdcl_twl_restart_l_list_invs
      simp: restart_abs_l_pre_def)
    done
  then show ?thesis
    apply -
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    by force
qed


lemma restart_prog_l_restart_abs_l2:
  \<open>(uncurry4 restart_prog_l, uncurry4 restart_abs_l)
  \<in> Id  \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<rightarrow>\<^sub>f
    \<langle>Id  \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close> (is \<open>_ \<in> ?R  \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel\<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f _\<close>)
proof -
  have cdcl_twl_full_restart_l_prog:
    \<open>cdcl_twl_full_restart_l_prog S \<le> SPEC (\<lambda>T. cdcl_twl_restart_l S T)\<close>
    if
      inv: \<open>restart_abs_l_pre S last_GC last_Restart brk\<close> and
      \<open>(b, ba) \<in> bool_rel\<close> and
      \<open>b \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      \<open>ba \<in> {b. b \<longrightarrow> f n < size ( S)}\<close> and
      brk: \<open>\<not>brk\<close>
    for b ba S brk n last_GC last_Restart
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      using cdcl_twl_full_restart_l_prog_spec[OF ST list_invs struct_invs
         confl upd]
        remove_one_annot_true_clause_cdcl_twl_restart_l_spec[OF ST list_invs struct_invs
         confl upd]
      by (rule conc_trans_additional)
  qed
  have cdcl_twl_full_restart_l_GC_prog:
    \<open>cdcl_twl_full_restart_l_GC_prog S \<le> SPEC (cdcl_twl_restart_l S)\<close>
    if
      inv: \<open>restart_abs_l_pre S last_GC last_Restart brk\<close> and
      brk: \<open>ba \<and> b2a \<and> \<not> brk\<close>
    for ba b2a brk S last_GC last_Restart
  proof -
    obtain T where
      ST: \<open>(S, T) \<in> twl_st_l None\<close> and
      struct_invs: \<open>twl_struct_invs T\<close> and
      list_invs: \<open>twl_list_invs S\<close> and
      upd: \<open>clauses_to_update_l S = {#}\<close> and
      stgy_invs: \<open>twl_stgy_invs T\<close> and
      confl: \<open>get_conflict_l S = None\<close> and
      inv2: \<open>restart_prog_pre T last_GC last_Restart brk\<close>
      using inv brk unfolding restart_abs_l_pre_def restart_prog_pre_def
      apply - apply normalize_goal+
      by (auto simp: twl_st)
    show ?thesis
      by (rule cdcl_twl_full_restart_l_GC_prog_cdcl_twl_restart_l[unfolded Down_id_eq, OF ST list_invs
        struct_invs confl upd stgy_invs inv2])
  qed

  have restart_abs_l_alt_def:
  \<open>restart_abs_l S last_GC last_Restart n brk = do {
     ASSERT(restart_abs_l_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required_l S last_GC n;
     b2 \<leftarrow> restart_required_l S last_Restart n;
     if b2 \<and>  \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only_l S T);
       RETURN (T, last_GC, size (get_all_learned_clss_l T), n)
     }
     else
     if b \<and> \<not>brk then do {
       _ \<leftarrow> SPEC(\<lambda>b :: bool. True);
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_l S T);
       RETURN (T, size (get_all_learned_clss_l T), size (get_all_learned_clss_l T), n + 1)
     }
     else
       RETURN (S, last_GC, last_Restart, n)
       }\<close> for  S last_GC last_Restart n brk
     unfolding restart_abs_l_def
     by (auto cong: if_cong)

   have [simp]: \<open>cdcl_twl_restart_only_l S Ta \<Longrightarrow>clauses_to_update_l Ta = {#}\<close> for S Ta
     by (auto simp: cdcl_twl_restart_only_l.simps)
   have [simp]: \<open>cdcl_twl_restart_l S Ta \<Longrightarrow>clauses_to_update_l Ta = {#}\<close> for S Ta
     by (auto simp: cdcl_twl_restart_l.simps)
   have \<open>restart_prog_l S p m n brk \<le> \<Down> (?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel)
       (restart_abs_l S p m n brk)\<close> for S n brk p m
    unfolding restart_prog_l_def restart_abs_l_alt_def restart_required_l_def cdcl_twl_restart_l_prog_def
    apply (refine_vcg)
    subgoal by auto
    subgoal
      by (rule cdcl_twl_local_restart_l_spec_cdcl_twl_restart_l[THEN order_trans])
        (auto simp: conc_fun_RES)
    subgoal by (auto intro: cdcl_twl_restart_only_l_list_invs
      simp: restart_abs_l_pre_def)
    subgoal by auto
    subgoal by (rule cdcl_twl_full_restart_l_prog) auto
    subgoal by (rule cdcl_twl_full_restart_l_GC_prog) auto
    subgoal by (auto simp: cdcl_twl_restart_l_list_invs
      simp: restart_abs_l_pre_def)
    subgoal by (auto simp: cdcl_twl_restart_l_list_invs
      simp: restart_abs_l_pre_def)
    done
  then show ?thesis
    apply -
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    by force
qed

definition cdcl_twl_stgy_restart_abs_early_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_abs_early_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (_, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, last_GC, last_Restart,n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, last_GC, last_Restart,n) \<leftarrow> restart_abs_l T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart,n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    if \<not>brk then do {
      (brk, T, last_GC, last_Restart, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv T\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, last_GC, last_Restart,n) \<leftarrow> restart_abs_l T last_GC last_Restart n brk;
        RETURN (brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (False, T, last_GC, last_Restart, n);
      RETURN T
    } else RETURN T
  }\<close>

definition cdcl_twl_stgy_restart_abs_bounded_l :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_stgy_restart_abs_bounded_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(_, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_abs_l T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    RETURN (ebrk, T)
  }\<close>

definition cdcl_twl_stgy_restart_prog_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_prog_l S\<^sub>0 =
  do {
    (brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, last_GC, last_Restart, n).
      do {
	T \<leftarrow> unit_propagation_outer_loop_l S;
	(brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
	(T, last_GC, last_Restart, n) \<leftarrow> restart_prog_l T last_GC last_Restart n brk;
	RETURN (brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    RETURN T
  }\<close>


definition cdcl_twl_stgy_restart_prog_early_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_restart_prog_early_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, n) \<leftarrow> restart_prog_l T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_l T \<noteq> None, T, n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    if \<not>brk then do {
      (brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv T\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, S, last_GC, last_Restart, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop_l S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
	  (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_l T last_GC last_Restart n brk;
	  RETURN (brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart, n)
	})
	(False, T, last_GC, last_Restart, n);
      RETURN T
    }
    else RETURN T
  }\<close>


lemma cdcl_twl_stgy_restart_prog_early_l_cdcl_twl_stgy_restart_abs_early_l:
  \<open>(cdcl_twl_stgy_restart_prog_early_l, cdcl_twl_stgy_restart_abs_early_l) \<in> {(S, S').
   (S, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((False, S, 0), (False, T , 0)) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close>
    for S T
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_early_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
	WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close> ]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_abs_l_restart_prog[THEN fref_to_Down_curry2]
        restart_prog_l_restart_abs_l2[THEN fref_to_Down_curry4])
    subgoal by auto
    subgoal by auto
    subgoal for x y xa x' x1 x2 x1a x2a
      by fastforce
    subgoal by auto
    subgoal
      by (simp add: twl_st)
    subgoal by (auto simp: twl_st)
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_abs_l:
  \<open>(cdcl_twl_stgy_restart_prog_l, cdcl_twl_stgy_restart_abs_l) \<in> {(S, S').
   (S, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S =  {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((False, S, 0), (False, T , 0)) \<in> bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close>
    for S T
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_abs_l_restart_prog[THEN fref_to_Down_curry4]
        restart_prog_l_restart_abs_l2[THEN fref_to_Down_curry4])
    subgoal by auto
    subgoal
      unfolding cdcl_twl_stgy_restart_abs_l_inv_def
      by (fastforce simp: prod_rel_fst_snd_iff)
    subgoal for x y xa x' x1 x2 x1a x2a
      by fastforce
    subgoal by auto
    subgoal
      by (auto simp add: twl_st)
    subgoal by (auto simp: twl_st)
    subgoal
       unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_abs_l_inv_def
       by (auto simp: twl_st)
    done
qed

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_prog:
  \<open>(cdcl_twl_stgy_restart_prog_l, cdcl_twl_stgy_restart_prog)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
      \<langle>{(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans)
  defer
  apply (rule cdcl_twl_stgy_restart_abs_l_cdcl_twl_stgy_restart_abs_l[THEN fref_to_Down])
    apply fast
    apply assumption
  apply (rule cdcl_twl_stgy_restart_prog_l_cdcl_twl_stgy_restart_abs_l[THEN fref_to_Down,
    simplified])
  apply simp
  done


definition cdcl_twl_stgy_restart_prog_bounded_l :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_stgy_restart_prog_bounded_l S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_abs_l_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop_l S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog_l T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog_l T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict_l T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss_l S\<^sub>0), size (get_all_learned_clss_l S\<^sub>0), 0);
    RETURN (ebrk, T)
  }\<close>

lemma (in -) [simp]:
  \<open>(S, T) \<in> twl_st_l b \<Longrightarrow> size (get_learned_clss T) = size (get_learned_clss_l S)\<close>
  \<open>(S, T) \<in> twl_st_l b \<Longrightarrow> (get_init_learned_clss T) = (get_unit_learned_clss_l S)\<close>
  by (auto simp: twl_st_l_def get_learned_clss_l_def)

lemma (in -) get_all_learned_clss_alt_def:
  \<open>get_all_learned_clss S = clauses (get_learned_clss S) + get_init_learned_clss S +
         subsumed_learned_clauses S + get_learned_clauses0 S\<close>
  by (cases S) auto

lemma cdcl_twl_stgy_restart_abs_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l:
  \<open>(cdcl_twl_stgy_restart_abs_bounded_l, cdcl_twl_stgy_restart_prog_bounded) \<in>
     {(S :: 'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle> nres_rel\<close>
  unfolding cdcl_twl_stgy_restart_abs_bounded_l_def cdcl_twl_stgy_restart_prog_bounded_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
	WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S  = {#}} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
      unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
      cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
      restart_abs_l_restart_prog[THEN fref_to_Down_curry4])
  subgoal by (auto simp add: get_all_learned_clss_alt_def)
  subgoal for x y ebrk ebrka xa x'
    unfolding cdcl_twl_stgy_restart_abs_l_inv_def comp_def case_prod_beta
    apply (rule_tac x=y in exI)
    apply (rule_tac x=\<open>fst (snd (snd x'))\<close> in exI)
    by (auto simp: prod_rel_fst_snd_iff)
  subgoal by (auto simp: prod_rel_fst_snd_iff)
  subgoal
    unfolding cdcl_twl_stgy_restart_prog_inv_def
      cdcl_twl_stgy_restart_abs_l_inv_def
    apply (simp only: prod.case)
    apply (normalize_goal)+
    by (simp add: twl_st_l twl_st)
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by auto
  subgoal by (auto simp: twl_st_l twl_st)
  subgoal by (auto simp: prod_rel_fst_snd_iff)
  done


lemma cdcl_twl_stgy_restart_abs_early_l_cdcl_twl_stgy_restart_abs_early:
  \<open>(cdcl_twl_stgy_restart_abs_early_l, cdcl_twl_stgy_restart_prog_early)
  \<in> {(S :: 'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
       clauses_to_update_l S  = {#}} \<rightarrow>\<^sub>f \<langle>twl_st_l None\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_abs_early_l_def cdcl_twl_stgy_restart_prog_early_def
    apply (intro frefI nres_relI)
    apply (refine_rcg
      WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and>
           twl_list_invs S \<and> clauses_to_update_l S  = {#}} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
         restart_abs_l_restart_prog[THEN fref_to_Down_curry4]
     WHILEIT_refine[where R =
       \<open>bool_rel \<times>\<^sub>r {(S :: 'v twl_st_l, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and>
         clauses_to_update_l S  = {#}} \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>])
    subgoal by (auto simp add: get_all_learned_clss_alt_def)
    subgoal for x y ebrk ebrka xa x'
      unfolding cdcl_twl_stgy_restart_abs_l_inv_def comp_def case_prod_beta
      apply (rule_tac x=y in exI)
      apply (rule_tac x=\<open>fst (snd (snd x'))\<close> in exI)
      by (auto simp: prod_rel_fst_snd_iff)
    subgoal by (auto simp: prod_rel_fst_snd_iff)
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def
        cdcl_twl_stgy_restart_abs_l_inv_def
      apply (simp only: prod.case)
      apply (normalize_goal)+
      by (simp add: twl_st_l twl_st)
    subgoal by (auto simp: twl_st_l twl_st)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y ebrk ebrka xa x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
         x1g x2g x1h x2h x1i x2i xb x'a
      unfolding cdcl_twl_stgy_restart_abs_l_inv_def comp_def case_prod_beta
      apply (rule_tac x= \<open>x1b\<close> in exI)
      apply (rule_tac x=\<open>fst (snd x'a)\<close> in exI)
      apply (rule_tac x= \<open>x2d\<close> in exI)
      by (auto simp: prod_rel_fst_snd_iff)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_l, cdcl_twl_stgy_restart_abs_bounded_l) \<in> {(S, S').
   (S:: 'v twl_st_l, S') \<in> Id \<and>  twl_list_invs S \<and>  clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
   (is \<open>_ \<in> ?R \<rightarrow>\<^sub>f _\<close>)
proof -
  have [refine0]: \<open>((ebrk, False, S, size (get_all_learned_clss_l S),
      size (get_all_learned_clss_l S), 0::nat),
     ebrka, False, T, size (get_all_learned_clss_l T),
     size (get_all_learned_clss_l T), 0::nat) \<in> bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r ?R \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>
    if \<open>(S, T) \<in> ?R\<close> \<open>(ebrk, ebrka) \<in> bool_rel\<close>
    for S T ebrk ebrka
    using that by auto
  have [refine0]: \<open>unit_propagation_outer_loop_l x1c  \<le> \<Down> Id (unit_propagation_outer_loop_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  have [refine0]: \<open>cdcl_twl_o_prog_l x1c  \<le> \<Down> Id (cdcl_twl_o_prog_l x1a)\<close>
    if \<open>(x1c, x1a) \<in> Id\<close>
    for x1c x1a
    using that by auto
  show ?thesis
    supply [simp] = prod_rel_fst_snd_iff
    unfolding cdcl_twl_stgy_restart_prog_bounded_l_def cdcl_twl_stgy_restart_prog_def uncurry_def
      cdcl_twl_stgy_restart_abs_bounded_l_def
    apply (intro frefI nres_relI)
    apply (refine_rcg WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close>]
	WHILEIT_refine[where R = \<open>bool_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel\<close> ]
        unit_propagation_outer_loop_l_spec[THEN fref_to_Down]
        cdcl_twl_o_prog_l_spec[THEN fref_to_Down]
        restart_prog_l_restart_abs_l2[THEN fref_to_Down_curry4])
    subgoal
      by  auto
    subgoal
      by fastforce
    subgoal by auto
    subgoal
      by (simp add: twl_st)
    subgoal
       by (auto simp: twl_st)
    subgoal by auto
    subgoal by auto
    done
qed

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_prog_bounded:
  \<open>(cdcl_twl_stgy_restart_prog_bounded_l, cdcl_twl_stgy_restart_prog_bounded)
    \<in> {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S \<and> clauses_to_update_l S = {#}} \<rightarrow>\<^sub>f
      \<langle>bool_rel \<times>\<^sub>r {(S, S'). (S, S') \<in> twl_st_l None \<and> twl_list_invs S}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rule order_trans)
  defer
  apply (rule cdcl_twl_stgy_restart_abs_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l[THEN fref_to_Down])
    apply fast
    apply assumption
  apply (rule cdcl_twl_stgy_restart_prog_bounded_l_cdcl_twl_stgy_restart_abs_bounded_l[THEN fref_to_Down,
    simplified])
  apply simp
  done


end

end