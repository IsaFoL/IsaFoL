theory Watched_Literals_Algorithm_Reduce
imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Simp
  Watched_Literals_Transition_System_Reduce
  Weidenbach_Book_Base.Explorer
begin

context twl_restart_ops
begin

text \<open>
  We refine in two steps. In the first, we refine the transition system directly. Then we simplify
  the stat and remove the unnecessary state and replace them by the counts we need.
\<close>
text \<open>Restarts are never necessary\<close>
definition GC_required :: "'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>GC_required S last_GC_learnt_clss n = do {
     ASSERT(size (get_all_learned_clss S) \<ge> last_GC_learnt_clss);
     SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss S) - last_GC_learnt_clss > f n)}\<close>

definition restart_required :: "'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required S last_Restart_learnt_clss n = do {
    ASSERT(size (get_all_learned_clss S) \<ge> last_Restart_learnt_clss);
    SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss S) > last_Restart_learnt_clss)
  }\<close>

definition inprocessing_required :: "'v twl_st \<Rightarrow> bool nres" where
  \<open>inprocessing_required S = do {
    SPEC (\<lambda>b. True)
  }\<close>

definition (in -) restart_prog_pre_int :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_prog_pre_int last_GC last_Restart S brk \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
    (\<not>brk \<longrightarrow> get_conflict S = None) \<and>
    size (get_all_learned_clss S) \<ge> size (get_all_learned_clss last_Restart) \<and>
    size (get_all_learned_clss S) \<ge> size (get_all_learned_clss last_GC) \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>

definition restart_prog_int
  :: \<open>'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st \<times> 'v twl_st \<times> 'v twl_st \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog_int last_GC last_Restart S m n brk = do {
     ASSERT(restart_prog_pre_int last_GC last_Restart S brk);
     b \<leftarrow> GC_required S (size (get_all_learned_clss last_GC)) n;
     b2 \<leftarrow> restart_required S  (size (get_all_learned_clss last_Restart))  n;
     if b2 \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only S T);
       RETURN (last_GC, T, T, Suc m, n)
     }
     else if b \<and> \<not>brk then do {
       b \<leftarrow> inprocessing_required S;
       if \<not>b then do {
         T  \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
         RETURN (T, T, T, m, Suc n)
      }
      else do {
         T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail T) = 0);
         U \<leftarrow> SPEC(\<lambda>U. cdcl_twl_restart T U);
         V \<leftarrow> SPEC(\<lambda>V. cdcl_twl_stgy\<^sup>*\<^sup>* U V \<and> clauses_to_update V = {#} \<and>
            (get_conflict V \<noteq> None \<longrightarrow> count_decided (get_trail V) = 0));
         RETURN (V, V, V, m, Suc n)
      }
    }
    else
      RETURN (last_GC, last_Restart, S, m, n)
  }\<close>

fun cdcl_twl_stgy_restart_prog_int_inv where
  \<open>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0) (brk, R, S, T, m, n) \<longleftrightarrow>
    twl_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) \<and>
    twl_stgy_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R, S, T, m, n, \<not>brk) \<and>
    clauses_to_update T = {#} \<and> (\<not>brk \<longrightarrow> get_conflict T = None)\<close>

lemmas cdcl_twl_stgy_restart_prog_int_inv_def[simp del] =
  cdcl_twl_stgy_restart_prog_int_inv.simps

lemma cdcl_twl_stgy_restart_prog_int_inv_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0) (brk, R, S, T, m, n) \<longleftrightarrow>
    twl_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) \<and>
    twl_stgy_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) \<and>
    twl_stgy_restart_inv (R, S, T, m, n, \<not>brk) \<and>
    twl_restart_inv (R, S, T, m, n, \<not>brk) \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R, S, T, m, n, \<not>brk) \<and>
  clauses_to_update T = {#} \<and> (\<not>brk \<longrightarrow> get_conflict T = None)\<close>
  unfolding cdcl_twl_stgy_restart_prog_int_inv_def
  by (auto dest: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv
    rtranclp_cdcl_twl_stgy_restart_twl_stgy_restart_inv)


text \<open>
  In the main loop, and purely to simplify the proof, we remember the state obtained after the last
  restart in order to relate it to the number of clauses. In a first proof attempt, we try to make
  do without it by only assuming its existence, but we could no prove that the loop terminates,
  because the state can change each time.

  This state is not needed at all in the execution and will be removed in the next refinement step.
\<close>
definition cdcl_twl_stgy_restart_prog_intg
  :: "nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow>'v twl_st \<Rightarrow>'v twl_st \<Rightarrow> 'v twl_st nres"
where
  \<open>cdcl_twl_stgy_restart_prog_intg m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 =
  do {
    (brk, _, _, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0)\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, S', S'', m,  n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S'';
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (S, S', T, m', n') \<leftarrow> restart_prog_int S S' T m n brk;
        RETURN (brk \<or> get_conflict T \<noteq> None, S, S', T, m', n')
      })
      (False, S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0);
    RETURN T
  }\<close>

abbreviation cdcl_twl_stgy_restart_prog_int where
  \<open>cdcl_twl_stgy_restart_prog_int S \<equiv> cdcl_twl_stgy_restart_prog_intg 0 0 S S S\<close>

lemmas cdcl_twl_stgy_restart_prog_int_def = cdcl_twl_stgy_restart_prog_intg_def

abbreviation cdcl_algo_termination_early_rel
  :: \<open>((bool \<times> bool \<times> 'v twl_st \<times> 'v twl_st \<times>  'v twl_st \<times> nat \<times> nat) \<times> _) set\<close>
where
  \<open>cdcl_algo_termination_early_rel \<equiv>
  {((ebrkT :: bool, brkT :: bool, R' :: 'v twl_st, S' :: 'v twl_st, T' :: 'v twl_st, m' :: nat, n' :: nat),
       (ebrkS, brkS, R :: 'v twl_st, S :: 'v twl_st, T :: 'v twl_st, m :: nat, n :: nat)).
     twl_restart_inv (R, S, T, m, n, \<not>brkS) \<and> \<not>brkS \<and>
     cdcl_twl_stgy_restart\<^sup>+\<^sup>+ (R, S, T, m, n, \<not>brkS) (R', S', T', m', n', \<not>brkT)} \<union>
  {((ebrkT :: bool, brkT :: bool, R' :: 'v twl_st, S' :: 'v twl_st, T' :: 'v twl_st, m' :: nat, n' :: nat),
  (ebrkS, brkS, R :: 'v twl_st, S :: 'v twl_st, T :: 'v twl_st, m :: nat, n :: nat)).
  \<not>brkS \<and> brkT}\<close>

end


context twl_restart
begin

lemma cdcl_twl_stgy_restart_tranclpI:
  \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<Longrightarrow> cdcl_twl_stgy_restart\<^sup>+\<^sup>+ (R, S, T, m, n, True) (R, S, U, m, n, True)\<close>
  by (induction rule: tranclp_induct)
    (auto dest!: cdcl_twl_stgy_restart.intros(1)[of _ _ R S m n])

lemma cdcl_twl_stgy_restart_rtranclpI:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U \<Longrightarrow> cdcl_twl_stgy_restart\<^sup>*\<^sup>* (R, S, T, m, n, True) (R, S, U, m, n, True)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: cdcl_twl_stgy_restart.intros(1)[of _ _ R S m n])

lemma  wf_cdcl_algo_termination_early_rel: \<open>wf cdcl_algo_termination_early_rel\<close> (is \<open>wf (?C \<union> ?D)\<close>)
proof -
  have A: \<open>{(T, S :: 'v twl_st_restart). twl_restart_inv S \<and> cdcl_twl_stgy_restart S T}\<^sup>+ =
    {(T, S :: 'v twl_st_restart). twl_restart_inv S \<and> cdcl_twl_stgy_restart\<^sup>+\<^sup>+ S T}\<close> (is \<open>?A = ?B\<close>)
  proof -
    have \<open>(x, y) \<in> ?A \<Longrightarrow> (x, y) \<in> ?B\<close> for x y
      by (induction rule: trancl_induct)
        auto
    moreover have \<open>cdcl_twl_stgy_restart\<^sup>+\<^sup>+ S T \<Longrightarrow> twl_restart_inv S \<Longrightarrow> (T, S) \<in> ?A\<close> for S T
      apply (induction rule: tranclp_induct)
      subgoal by auto
      subgoal for T U
        by (rule trancl_into_trancl2[of _ T])
          (use rtranclp_cdcl_twl_stgy_restart_twl_restart_inv[of S T] in \<open>simp_all add: tranclp_into_rtranclp\<close>)
      done
    ultimately show ?thesis
      by blast
  qed
  have \<open>wf ?D\<close>
    by (rule wf_no_loop) auto
  moreover have \<open>wf ?C\<close>
    by (rule wf_if_measure_in_wf[OF wf_trancl[OF wf_cdcl_twl_stgy_restart, unfolded A],
        of _  \<open>\<lambda>(_, brkT, R, S, T, n, n'). (R, S, T, n, n', \<not>brkT)\<close>])
      auto
  moreover have \<open>?D O ?C \<subseteq> ?D\<close>
    by auto
  ultimately show ?thesis
    apply (subst Un_commute)
    by (rule wf_union_compatible)
qed

definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_bounded_intg
     :: "nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres"
where
  \<open>cdcl_twl_stgy_restart_prog_bounded_intg m n S\<^sub>0 T\<^sub>0 U\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, _, _, _, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m, n) o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, Q, R, S, m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (Q, R, T, m, n) \<leftarrow> restart_prog_int Q R T m n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict T \<noteq> None, Q, R, T, m, n)
      })
      (ebrk, False, S\<^sub>0, T\<^sub>0, U\<^sub>0, m, n);
    RETURN (ebrk, T)
  }\<close>

abbreviation (in twl_restart_ops) cdcl_twl_stgy_restart_prog_bounded_int where
  \<open>cdcl_twl_stgy_restart_prog_bounded_int S \<equiv> cdcl_twl_stgy_restart_prog_bounded_intg 0 0 S S S\<close>

lemmas cdcl_twl_stgy_restart_prog_bounded_int_def = cdcl_twl_stgy_restart_prog_bounded_intg_def

lemma pcdcl_core_stgy_get_all_learned_clss:
  \<open>pcdcl_core_stgy T U \<Longrightarrow>
  size (pget_all_learned_clss T) \<le> size (pget_all_learned_clss U)\<close>
  by (induction rule: pcdcl_core_stgy.induct)
   (cases T; cases U; auto simp: cdcl_conflict.simps cdcl_propagate.simps cdcl_decide.simps
    cdcl_skip.simps cdcl_resolve.simps cdcl_backtrack.simps
    dest!: arg_cong[of \<open>clauses _\<close> \<open>_\<close> size])+

lemma cdcl_twl_cp_get_all_learned_clss:
  \<open>cdcl_twl_cp T U \<Longrightarrow>
    size (get_all_learned_clss T) = size (get_all_learned_clss U)\<close>
  by (induction rule: cdcl_twl_cp.induct)
   (auto simp: update_clauses.simps dest!: multi_member_split)

lemma rtranclp_cdcl_twl_cp_get_all_learned_clss:
  \<open>cdcl_twl_cp\<^sup>*\<^sup>* T U \<Longrightarrow>
    size (get_all_learned_clss T) = size (get_all_learned_clss U)\<close>
  by (induction rule:rtranclp_induct)
   (auto  dest: cdcl_twl_cp_get_all_learned_clss)

lemma cdcl_twl_o_get_all_learned_clss:
  \<open>cdcl_twl_o T U \<Longrightarrow>
    size (get_all_learned_clss T) \<le> size (get_all_learned_clss U)\<close>
  by (induction rule: cdcl_twl_o.induct)
   (auto simp: update_clauses.simps dest!: multi_member_split)

lemma rtranclp_cdcl_twl_o_get_all_learned_clss:
  \<open>cdcl_twl_o\<^sup>*\<^sup>* T U \<Longrightarrow>
    size (get_all_learned_clss T) \<le> size (get_all_learned_clss U)\<close>
  by (induction rule:rtranclp_induct)
   (auto  dest: cdcl_twl_o_get_all_learned_clss)

lemma rtranclp_pcdcl_stgy_only_restart_pget_all_learned_clss_mono:
  \<open>pcdcl_stgy_only_restart\<^sup>*\<^sup>* S T \<Longrightarrow>
    size (pget_all_learned_clss S) \<le> size (pget_all_learned_clss T)\<close>
  by (induction rule:rtranclp_induct)
   (auto  dest: pcdcl_stgy_only_restart_pget_all_learned_clss_mono)

lemma restart_prog_bounded_spec:
  assumes
    \<open>iebrk \<in> UNIV\<close> and
    inv: \<open>(cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0) \<circ> snd) (ebrk, brk, S, T, U, m, n)\<close> and
    cond: \<open>case (ebrk, brk, S, T, U, m, n) of
     (ebrk, brk, uu_) \<Rightarrow> \<not> brk \<and> \<not> ebrk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec V (brkW, W)\<close> and
    \<open>twl_struct_invs V\<close> and
    \<open>cdcl_twl_cp\<^sup>*\<^sup>* U V\<close> and
    \<open>literals_to_update V = {#}\<close> and
    \<open>\<forall>S'. \<not> cdcl_twl_cp V S'\<close> and
    \<open>twl_stgy_invs V\<close>
  shows \<open>restart_prog_int S T W m n brkW
         \<le> SPEC
            (\<lambda>x. (case x of (Q, R, T, m, n) \<Rightarrow> do {
                                ebrk \<leftarrow> RES UNIV;
                                RETURN (ebrk, brkW \<or> get_conflict T \<noteq> None, Q, R, T, m, n)
                              })
                 \<le> SPEC
                    (\<lambda>s'. (cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0) \<circ> snd) s' \<and>
                          (s', ebrk, brk, S, T, U, m, n)
                          \<in> cdcl_algo_termination_early_rel))\<close>
    (is \<open>_ \<le> SPEC (\<lambda>x. _ \<le> SPEC(\<lambda>s. ?I s \<and> _ \<in> ?term))\<close>)
proof -

  have [simp]: \<open>\<not>brk\<close> \<open>\<not>ebrk\<close>
    using cond by auto
  have struct_invs': \<open>cdcl_twl_restart W T' \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* T' V' \<Longrightarrow> twl_struct_invs V'\<close> for T' V'
    using assms(3) cdcl_twl_restart_twl_struct_invs
      by (metis (no_types, lifting) assms(4) case_prodD rtranclp_cdcl_twl_stgy_twl_struct_invs)
  have stgy_invs: \<open>cdcl_twl_restart W V' \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V' W' \<Longrightarrow> twl_stgy_invs W'\<close> for V' W'
    using assms(3) cdcl_twl_restart_twl_stgy_invs
    by (metis (no_types, lifting) assms(4) case_prodD cdcl_twl_restart_twl_struct_invs
      rtranclp_cdcl_twl_stgy_twl_stgy_invs)

  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_S0: \<open>twl_struct_invs S\<^sub>0\<close> \<open>twl_struct_invs T\<^sub>0\<close> \<open>twl_struct_invs U\<^sub>0\<close> and
    struct_invs_S: \<open>twl_struct_invs S\<close> and
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    struct_invs_U: \<open>twl_struct_invs U\<close> and
    twl_stgy_invs_S0: \<open>twl_stgy_invs S\<^sub>0\<close>\<open>twl_stgy_invs T\<^sub>0\<close>\<open>twl_stgy_invs U\<^sub>0\<close> and
    twl_stgy_invs_S: \<open>twl_stgy_invs S\<close> and
    twl_stgy_invs_T: \<open>twl_stgy_invs T\<close> and
    twl_stgy_invs_U: \<open>twl_stgy_invs U\<close> and
    \<open>brk \<longrightarrow> final_twl_state U\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (S, T, U, m, n, \<not> brk)\<close> and
    clss_T: \<open>clauses_to_update U = {#}\<close> and
    confl: \<open>\<not> brk \<longrightarrow> get_conflict U = None\<close> and
    STU_inv: \<open>pcdcl_stgy_restart_inv (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, \<not> brk)\<close> and
    [simp]: \<open>twl_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True)\<close>
    \<open>twl_stgy_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True)\<close> and
    init: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
       \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of T)\<close>
       \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of U)\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_int_inv_alt_def prod.case comp_def snd_conv
      twl_restart_inv_def twl_stgy_restart_inv_def by fast+

  have
    cdcl_o: \<open>cdcl_twl_o\<^sup>*\<^sup>* V W\<close> and
    conflict_W: \<open>get_conflict W \<noteq> None \<Longrightarrow> count_decided (get_trail W) = 0\<close> and
    brk'_no_step: \<open>brkW \<Longrightarrow> final_twl_state W\<close> and
    struct_invs_W: \<open>twl_struct_invs W\<close> and
    stgy_invs_W: \<open>twl_stgy_invs W\<close> and
    clss_to_upd_W: \<open>clauses_to_update W = {#}\<close> and
    lits_to_upd_W: \<open>\<not> brkW \<longrightarrow> literals_to_update W \<noteq> {#}\<close> and
    confl_W: \<open>\<not> brkW \<longrightarrow> get_conflict W = None\<close> and
    ent: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of V)\<close>
    using other_inv unfolding final_twl_state_def by fast+
  have ent_W: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of W)\<close>
    using assms(5) rtranclp_cdcl_twl_o_stgyD[OF cdcl_o] ent
      rtranclp_cdcl_twl_stgy_entailed_by_init by blast
  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close>
    by (meson cdcl_o assms(5) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD
      rtranclp_trans)

  have \<open>size (get_all_learned_clss T) \<le> size (get_all_learned_clss W)\<close>
     \<open>size (get_all_learned_clss S) \<le> size (get_all_learned_clss W)\<close>
    using STU_inv assms(6) cdcl_o unfolding pcdcl_stgy_restart_inv_def
    by (auto dest!: rtranclp_pcdcl_tcore_stgy_pget_all_learned_clss_mono
      rtranclp_cdcl_twl_cp_get_all_learned_clss rtranclp_cdcl_twl_o_get_all_learned_clss
      rtranclp_pcdcl_stgy_only_restart_pget_all_learned_clss_mono)
  then have restart_W: \<open>restart_prog_pre_int S T W brkW\<close>
    using struct_invs_W stgy_invs_W confl_W ent_W unfolding restart_prog_pre_int_def by auto

  have UW: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, T, U, m, n, True) (S, T, W, m, n, True)\<close>
    apply (rule cdcl_twl_stgy_restart_rtranclpI)
    by (meson \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> assms(6) rtranclp_cdcl_twl_cp_stgyD rtranclp_trans)
  have restart_only: \<open>?I (ebrk', False \<or> get_conflict X \<noteq> None, S, X, X, Suc m, n)\<close> (is ?A) and
    restart_only_term: \<open>((ebrk', False \<or> get_conflict X \<noteq> None, S, X, X, Suc m, n), ebrk, brk, S, T, U, m, n) \<in> ?term\<close> (is ?B)
    if 
      \<open>restart_prog_pre_int S T W False\<close> and
      less: \<open>True \<longrightarrow>
      size (get_all_learned_clss T) < size (get_all_learned_clss W)\<close> and
      WX: \<open>cdcl_twl_restart_only W X\<close> and
      \<open>ebrk' \<in> UNIV\<close> and
      y and
      x
     for x y X ebrk'
  proof -
    have WX': \<open>cdcl_twl_stgy_restart (S, T, W, m, n, True) (S, X, X, Suc m, n, True)\<close>
      by (rule cdcl_twl_stgy_restart.intros)
        (use less WX in auto)
    show ?A
      using UW WX twl_res WX' clss_to_upd_W
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def cdcl_twl_restart_only.simps)
    show ?B
      using STU_inv UW WX' init
        by (auto simp: twl_restart_inv_def struct_invs_S struct_invs_T struct_invs_U)
  qed
  have GC: \<open>?I (ebrk', False \<or> get_conflict Y \<noteq> None, Y, Y, Y, m, Suc n)\<close> (is ?A) and
    GC_term: \<open>((ebrk', False \<or> get_conflict Y \<noteq> None, Y, Y, Y, m, Suc n), ebrk, brk, S, T, U, m, n) \<in> ?term\<close> (is ?B)
    if 
      \<open>restart_prog_pre_int S T W False\<close> and
      less: \<open>True \<longrightarrow> f n < size (get_all_learned_clss W) - size (get_all_learned_clss S)\<close> and
      WX: \<open>cdcl_twl_subsumption_inp\<^sup>*\<^sup>* W W'\<close>
        \<open>count_decided (get_trail W') = 0\<close>
        \<open>cdcl_twl_restart W' X\<close> and
      \<open>ebrk' \<in> UNIV\<close> and
      \<open>\<not> brkW\<close> and
      XY: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* X Y\<close>
        \<open>clauses_to_update Y = {#}\<close>
        \<open>get_conflict Y \<noteq> None \<longrightarrow> count_decided (get_trail Y) = 0\<close>
    for x X Y ebrk' W'
  proof -
    have WX': \<open>cdcl_twl_stgy_restart (S, T, W, m, n, True) (Y, Y, Y, m, Suc n, True)\<close>
      by (rule cdcl_twl_stgy_restart.intros(2)[of _ _ _ W'])
       (use less WX XY in auto)
    have \<open>count_decided (get_trail Y) = 0 \<Longrightarrow> get_conflict Y \<noteq> None \<Longrightarrow> final_twl_state Y\<close>
      by (auto simp: final_twl_state_def)
    moreover have \<open>count_decided (get_trail Y) = 0 \<Longrightarrow> get_conflict Y \<noteq> None \<Longrightarrow>
      cdcl_twl_stgy_restart (Y, Y, Y, m, Suc n, True) (Y, Y, Y, m, Suc n, False)\<close>
      by (rule cdcl_twl_stgy_restart.intros)
        (auto simp: pcdcl_twl_final_state_def)
    ultimately show ?A
      using UW WX twl_res WX' XY
      by (cases \<open>get_conflict Y = None\<close>) (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def)
    show ?B
      using STU_inv UW WX' init
      by (auto simp: twl_restart_inv_def struct_invs_S struct_invs_T struct_invs_U)
  qed
  have continue: \<open>?I (ebrk', brkW \<or> get_conflict W \<noteq> None, S, T, W, m, n)\<close> (is ?A) and
    continue_term: \<open>((ebrk', brkW \<or> get_conflict W \<noteq> None, S, T, W, m, n), ebrk, brk, S, T, U, m, n) \<in> ?term\<close> (is ?B) for ebrk'
  proof -
    show ?A
      using brk'_no_step confl_W clss_to_upd_W UW twl_res
        cdcl_twl_stgy_restart.intros(4)[of W S T m n]
      apply (cases \<open>get_conflict W = None\<close>; cases brkW)
      apply (auto simp add: cdcl_twl_stgy_restart_prog_int_inv_def)
      apply (metis (no_types, lifting) final_twl_state_def pcdcl_twl_final_state_def rtranclp.simps rtranclp_trans)+
      done
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ V W\<close> if \<open>\<not>brkW\<close>
      using  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W that assms(7) unfolding rtranclp_unfold
      by auto
    then have [simp]: \<open>cdcl_twl_stgy_restart\<^sup>+\<^sup>+ (S, T, U, m, n, True) (S, T, W, m, n, True)\<close> if \<open>\<not>brkW\<close>
      by (meson assms(6) cdcl_twl_stgy_restart_tranclpI
        rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp that)

    show ?B
      using STU_inv brk'_no_step init
      apply (cases \<open>get_conflict W = None\<close>; cases brkW)
      by (auto simp: twl_restart_inv_def struct_invs_S struct_invs_T struct_invs_U)
  qed
  have noinp_continue: \<open>?I (xd, False \<or> get_conflict ab \<noteq> None, ab, ab, ab, m, Suc n)\<close> (is ?A) and
    noinp_term: \<open>((xd, False \<or> get_conflict ab \<noteq> None, ab, ab, ab, m, Suc n), ebrk, brk, S, T, U, m, n) \<in> ?term\<close>
      (is ?B)
    if
      \<open>restart_prog_pre_int S T W False\<close> and
      \<open>size (get_all_learned_clss S) \<le> size (get_all_learned_clss W)\<close> and
      less: \<open>True \<longrightarrow>
       f n < size (get_all_learned_clss W) - size (get_all_learned_clss S)\<close> and
      \<open>size (get_all_learned_clss T) \<le> size (get_all_learned_clss W)\<close> and
      \<open>xa \<longrightarrow> size (get_all_learned_clss T) < size (get_all_learned_clss W)\<close> and
      \<open>\<not> (xa \<and> \<not> False)\<close> and
      WX: \<open>cdcl_twl_restart W ab\<close> and
      \<open>xd \<in> UNIV\<close> and
      [simp]: x \<open>\<not> brkW\<close> \<open>\<not> xb\<close>
      for x xa xb ab xd
  proof -
    have [simp]: \<open>get_conflict W = None\<close> \<open>get_conflict ab = None\<close> \<open>clauses_to_update ab = {#}\<close>
      using that(1) WX
      by (auto simp: restart_prog_pre_int_def cdcl_twl_restart.simps)
    have WX': \<open>cdcl_twl_stgy_restart (S, T, W, m, n, True) (ab, ab, ab, m, Suc n, True)\<close>
      by (rule cdcl_twl_stgy_restart.intros(2)[of _ _ _ W]) (use less WX in auto)
    then show ?A
      using UW twl_res by (auto simp add: cdcl_twl_stgy_restart_prog_int_inv_def)
    show ?B
      using UW twl_res WX' \<open>twl_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True)\<close> by (auto
        dest: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv)
  qed

  show ?thesis
    unfolding restart_prog_int_def restart_required_def GC_required_def inprocessing_required_def
    apply (refine_vcg lhs_step_If; remove_dummy_vars)
    subgoal by (rule restart_W)
    subgoal by (auto simp: restart_prog_pre_int_def)
    subgoal by (auto simp: restart_prog_pre_int_def)
    subgoal by (rule restart_only)
    subgoal by (rule restart_only_term)
    subgoal by (rule noinp_continue)
    subgoal by (rule noinp_term)
    subgoal by (rule GC)
    subgoal by (rule GC_term)
    subgoal by (rule continue)
    subgoal by (rule continue_term)
    done
qed


lemma (in twl_restart) cdcl_twl_stgy_prog_bounded_int_spec:
  fixes n :: nat
  assumes \<open>twl_restart_inv (S, T, U, m, n, False)\<close> and
    \<open>twl_stgy_restart_inv (S, T, U, m, n, False)\<close> and
    \<open>clauses_to_update U = {#}\<close> and
    \<open>get_conflict U = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_bounded_intg m n S T U \<le> partial_conclusive_TWL_run2 m n S T U\<close>
  supply RETURN_as_SPEC_refine[refine2 del]
  unfolding cdcl_twl_stgy_restart_prog_bounded_intg_def full_def partial_conclusive_TWL_run2_def
  apply (refine_vcg
    WHILEIT_rule[where
    R = \<open>cdcl_algo_termination_early_rel\<close>];
    remove_dummy_vars)
  subgoal
    by (rule wf_cdcl_algo_termination_early_rel)
  subgoal
    using assms by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_restart_inv_def
      twl_struct_invs_def pcdcl_stgy_restart_inv_def twl_stgy_restart_inv_def)
  subgoal
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
      twl_restart_inv_def
      dest!: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv)
  subgoal
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def)
  subgoal
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def)
  subgoal
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
      twl_restart_inv_def
      dest: rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs)
  subgoal
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
      twl_restart_inv_def no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp
      dest: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv)
  subgoal by fast
  subgoal for x a aa ab ac ad ae be xa
    using assms
    using
      rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of \<open>(S, T, U, m, n, True)\<close>
      \<open>(ab, ac, ad, ae, be, True)\<close>]
    by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def
       twl_restart_inv_def
      intro: rtranclp_cdcl_twl_stgy_entailed_by_init
      dest!: rtranclp_cdcl_twl_cp_stgyD
      simp flip:  state\<^sub>W_of_def)
  subgoal
    by (rule restart_prog_bounded_spec)
  subgoal for x brk T U m n ebrk V
    apply (rule_tac x=T in exI)
    apply (rule_tac x=U in exI)
    apply (rule_tac x= \<open>(m, n, \<not>brk)\<close> in exI)
    by (auto simp add: cdcl_twl_stgy_restart_prog_int_inv_def)
  done


lemma cdcl_twl_stgy_restart_prog_int_spec:
  fixes S\<^sub>0 :: \<open>'v twl_st\<close>
  assumes \<open>twl_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, False)\<close> and
    \<open>twl_stgy_restart_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, False)\<close> and
    \<open>clauses_to_update U\<^sub>0 = {#}\<close> and
    \<open>get_conflict U\<^sub>0 = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_intg m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 \<le> conclusive_TWL_run2 m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0\<close>
proof -
  define RETURN_FALSE where \<open>RETURN_FALSE = RETURN False\<close>
  have cdcl_twl_stgy_restart_prog_alt_def:
    \<open>cdcl_twl_stgy_restart_prog_intg m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 =
    do {
    _ \<leftarrow> RETURN False;
    (brk, _, _, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0)\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, S', S'', m,  n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S'';
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (S, S', T, m', n') \<leftarrow> restart_prog_int S S' T m n brk;
        _ \<leftarrow> RETURN_FALSE;
        RETURN (brk \<or> get_conflict T \<noteq> None, S, S', T, m', n')
      })
      (False, S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0);
    RETURN T
    }\<close>
    unfolding cdcl_twl_stgy_restart_prog_int_def RETURN_FALSE_def
    by auto

  have [refine]: \<open>RETURN False \<le> \<Down> {(b, b'). (b = b') \<and> \<not>b} (RES UNIV)\<close>
     \<open>RETURN_FALSE \<le> \<Down> {(b, b'). (b = b') \<and> \<not>b} (RES UNIV)\<close>
    by (auto intro!: RETURN_RES_refine simp: RETURN_FALSE_def)
   have [refine]: \<open>((False, S\<^sub>0, T\<^sub>0, U\<^sub>0, (m\<^sub>0::nat), (n\<^sub>0 :: nat)), ebrk, False, S\<^sub>0, T\<^sub>0, U\<^sub>0,
      m\<^sub>0, n\<^sub>0) \<in> {(T, (b, S)). S = T \<and> \<not>b}\<close>
     if \<open>(u, ebrk) \<in> {(b, b'). (b = b') \<and> \<not>b}\<close> for ebrk u
     using that
     by auto
   have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close>
     for x x'
     using that by auto

  have ref_early: \<open>cdcl_twl_stgy_restart_prog_intg m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 \<le> \<Down>{((S), (ebrk, T)). S = T \<and> \<not>ebrk}
       (cdcl_twl_stgy_restart_prog_bounded_intg m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0)\<close>
    unfolding cdcl_twl_stgy_restart_prog_alt_def cdcl_twl_stgy_restart_prog_bounded_intg_def
    apply refine_rcg
    apply assumption
    subgoal by auto
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done

  show ?thesis
    apply (rule order_trans[OF ref_early])
    apply (rule order_trans[OF ref_two_step'])
    apply (rule cdcl_twl_stgy_prog_bounded_int_spec[OF assms])
    unfolding conc_fun_RES partial_conclusive_TWL_run2_def conclusive_TWL_run2_def by fastforce
qed

end

context twl_restart_ops
begin

definition (in -) restart_prog_pre :: \<open>'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_prog_pre S last_GC last_Restart  brk \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
    (\<not>brk \<longrightarrow> get_conflict S = None) \<and>
    size (get_all_learned_clss S) \<ge> last_Restart \<and>
    size (get_all_learned_clss S) \<ge> last_GC \<and>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>

definition restart_prog
  :: \<open>'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st \<times> nat \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog S last_GC last_Restart n brk = do {
     ASSERT(restart_prog_pre S last_GC last_Restart brk);
     b \<leftarrow> GC_required S last_GC  n;
     b2 \<leftarrow> restart_required S last_Restart  n;
     if b2 \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only S T);
       RETURN (T, last_GC, (size (get_all_learned_clss T)), n)
     }
     else
     if b \<and> \<not>brk then do {
         b \<leftarrow> inprocessing_required S;
         if \<not>b then  do {
           V \<leftarrow> SPEC(\<lambda>U. cdcl_twl_restart S U);
           RETURN (V, (size (get_all_learned_clss V)), (size (get_all_learned_clss V)), Suc n)
       } else do {
           T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_subsumption_inp\<^sup>*\<^sup>* S T \<and> count_decided (get_trail T) = 0);
           U \<leftarrow> SPEC(\<lambda>U. cdcl_twl_restart T U);
           V \<leftarrow> SPEC(\<lambda>V. cdcl_twl_stgy\<^sup>*\<^sup>* U V \<and> clauses_to_update V = {#} \<and> get_conflict V = None);
           RETURN (V, (size (get_all_learned_clss V)), (size (get_all_learned_clss V)), Suc n)
        }
     }
     else
       RETURN (S, last_GC, last_Restart, n)
   }\<close>

lemma restart_prog_spec:
  \<open>(uncurry4 restart_prog, uncurry5 restart_prog_int) \<in>
  {(((((S, last_GC), last_Restart), n), brk),
  (((((last_GC', last_Restart'), S'), m'), n'), brk')).
  S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
  last_Restart = size (get_all_learned_clss last_Restart') \<and>
  n = n' \<and> brk = brk'} \<rightarrow>\<^sub>f
  \<langle>{((S, last_GC, last_Restart, n),
   (last_GC', last_Restart', S', m', n')).
  S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
  last_Restart = size (get_all_learned_clss last_Restart') \<and>
  n = n'}\<rangle>nres_rel\<close>
proof -
  have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close> for x x'
    using that by auto
  show ?thesis
    unfolding restart_prog_def restart_prog_int_def uncurry_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    subgoal
      by (auto simp: restart_prog_pre_def restart_prog_pre_int_def)
    apply (rule this_is_the_identity)
    subgoal
      by auto
    apply (rule this_is_the_identity)
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
    apply (rule this_is_the_identity)
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
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    done
qed

fun cdcl_twl_stgy_restart_prog_inv:: "'v twl_st \<times> nat \<Rightarrow> (bool \<times> 'v twl_st \<times> nat \<times> nat \<times>nat) \<Rightarrow> bool" where
 [simp del]: \<open>cdcl_twl_stgy_restart_prog_inv (S\<^sub>0, n\<^sub>0)(brk, T, last_GC, last_Restart, n) \<longleftrightarrow>
    (\<exists>last_GC' last_Restart' m m\<^sub>0 T\<^sub>0 U\<^sub>0. last_GC = size (get_all_learned_clss last_GC') \<and>
      last_Restart = size (get_all_learned_clss last_Restart') \<and>
     cdcl_twl_stgy_restart_prog_int_inv (T\<^sub>0, U\<^sub>0, S\<^sub>0, m\<^sub>0, n\<^sub>0) (brk, last_GC', last_Restart', T, m, n))\<close>

lemma cdcl_twl_stgy_restart_prog_inv_def:
  \<open>cdcl_twl_stgy_restart_prog_inv= (\<lambda>(S\<^sub>0, n\<^sub>0) (brk, T, last_GC, last_Restart, n).
    (\<exists>last_GC' last_Restart' m m\<^sub>0 T\<^sub>0 U\<^sub>0. last_GC = size (get_all_learned_clss last_GC') \<and>
      last_Restart = size (get_all_learned_clss last_Restart') \<and>
  cdcl_twl_stgy_restart_prog_int_inv (T\<^sub>0, U\<^sub>0, S\<^sub>0, m\<^sub>0, n\<^sub>0) (brk, last_GC', last_Restart', T, m, n)))\<close>
  by (force intro!: ext simp: cdcl_twl_stgy_restart_prog_inv.simps)

definition cdcl_twl_stgy_restart_progg
  :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres"
where
  \<open>cdcl_twl_stgy_restart_progg n\<^sub>0 last_GC last_Restart S\<^sub>0 =
  do {
    (brk, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv (S\<^sub>0, n\<^sub>0)\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S'', S, S', n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S'';
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, S, S', n') \<leftarrow> restart_prog T S S' n brk;
        RETURN (brk \<or> get_conflict T \<noteq> None, T, S, S', n')
      })
      (False, S\<^sub>0, last_GC, last_Restart, n\<^sub>0);
    RETURN T
  }\<close>

abbreviation cdcl_twl_stgy_restart_prog where
  \<open>cdcl_twl_stgy_restart_prog S \<equiv>
     cdcl_twl_stgy_restart_progg 0 (size (get_all_learned_clss S)) (size (get_all_learned_clss S)) S\<close>

lemmas cdcl_twl_stgy_restart_prog_def = cdcl_twl_stgy_restart_progg_def

lemma (in -) fref_to_Down_curry4_5:
  \<open>(uncurry4 f, uncurry5 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z' a a' b b' c'. P (((((x', y'), z'), a'), b'), c') \<Longrightarrow>
        (((((x, y), z), a), b), (((((x', y'), z'), a'), b'), c')) \<in> A \<Longrightarrow>
         f x y z a b \<le> \<Down> B (g x' y' z' a' b' c'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma cdcl_twl_stgy_restart_progg_cdcl_twl_stgy_restart_prog_intg:
  \<open>cdcl_twl_stgy_restart_progg n\<^sub>0 (size (get_all_learned_clss T)) (size (get_all_learned_clss U)) S \<le> \<Down>Id (cdcl_twl_stgy_restart_prog_intg m\<^sub>0 n\<^sub>0 T U S)\<close>
proof -
  have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close> for x x'
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_def cdcl_twl_stgy_restart_prog_int_def uncurry_def
    apply (refine_rcg
      WHILEIT_refine[where R = \<open>{((brk :: bool,  S :: 'v twl_st, last_GC, last_Restart, n),
     (brk', last_GC', last_Restart', S', m', n')).
    S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
    last_Restart = size (get_all_learned_clss last_Restart') \<and>
      n = n' \<and> brk = brk'}\<close>]
      restart_prog_spec[THEN fref_to_Down_curry4_5])
    subgoal
      by auto
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def by blast
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    done
qed

lemma cdcl_twl_stgy_restart_prog_cdcl_twl_stgy_restart_prog_int:
  \<open>(cdcl_twl_stgy_restart_prog, cdcl_twl_stgy_restart_prog_int) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding uncurry_def Down_id_eq
    apply (intro frefI nres_relI)
    apply (rule order_trans[OF cdcl_twl_stgy_restart_progg_cdcl_twl_stgy_restart_prog_intg])
    apply auto
    done
qed


lemma (in twl_restart) cdcl_twl_stgy_restart_prog_specg:
  fixes S\<^sub>0 :: \<open>'v twl_st\<close>
  assumes \<open>twl_restart_inv (T\<^sub>0, U\<^sub>0, S\<^sub>0, m\<^sub>0, n\<^sub>0, False)\<close> and
    \<open>twl_stgy_restart_inv (T\<^sub>0, U\<^sub>0, S\<^sub>0,  m\<^sub>0, n\<^sub>0, False)\<close> and
    \<open>clauses_to_update S\<^sub>0 = {#}\<close> and
    \<open>get_conflict S\<^sub>0 = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_progg n\<^sub>0 (size (get_all_learned_clss T\<^sub>0)) (size (get_all_learned_clss U\<^sub>0)) S\<^sub>0 \<le> conclusive_TWL_run2 m\<^sub>0 n\<^sub>0 T\<^sub>0 U\<^sub>0 S\<^sub>0\<close>
  apply (rule order_trans)
  apply (rule cdcl_twl_stgy_restart_progg_cdcl_twl_stgy_restart_prog_intg[of _ _ _ _ m\<^sub>0])
  apply simp
  apply (rule cdcl_twl_stgy_restart_prog_int_spec[OF assms])
  done

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_spec:
  fixes S :: \<open>'v twl_st\<close>
  assumes
    \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog S \<le> conclusive_TWL_run S\<close>
  by (rule order_trans[OF cdcl_twl_stgy_restart_prog_specg[of _ _ _ 0]])
   (use assms in \<open>force simp: twl_restart_inv_def pcdcl_stgy_restart_inv_def
      twl_struct_invs_def twl_stgy_restart_inv_def conclusive_TWL_run2_def
      conclusive_TWL_run_def\<close>)+


definition (in twl_restart_ops) cdcl_twl_stgy_restart_prog_boundedg
   :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres"
where
  \<open>cdcl_twl_stgy_restart_prog_boundedg n\<^sub>0 last_GC last_Restart S\<^sub>0=
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, _, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv (S\<^sub>0, n\<^sub>0) o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0, last_GC, last_Restart, n\<^sub>0);
    RETURN (ebrk, T)
  }\<close>

abbreviation cdcl_twl_stgy_restart_prog_bounded where
 \<open>cdcl_twl_stgy_restart_prog_bounded S \<equiv> cdcl_twl_stgy_restart_prog_boundedg 0 (size (get_all_learned_clss S))
      (size (get_all_learned_clss S)) S\<close>

lemmas cdcl_twl_stgy_restart_prog_bounded_def =
  cdcl_twl_stgy_restart_prog_boundedg_def

lemma cdcl_twl_stgy_restart_prog_boundedg_cdcl_twl_stgy_restart_prog_bounded_intg:
  \<open>cdcl_twl_stgy_restart_prog_boundedg n\<^sub>0 (size (get_all_learned_clss T\<^sub>0))
      (size (get_all_learned_clss U\<^sub>0)) S \<le> \<Down>Id (cdcl_twl_stgy_restart_prog_bounded_intg m\<^sub>0 n\<^sub>0 T\<^sub>0 U\<^sub>0 S)\<close>
proof -
  have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close> for x x'
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_bounded_def cdcl_twl_stgy_restart_prog_bounded_intg_def
      uncurry_def
    apply (refine_rcg
      WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool,  S :: 'v twl_st, last_GC, last_Restart, n),
     (ebrk', brk', last_GC', last_Restart', S', m', n')).
    S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
    last_Restart = size (get_all_learned_clss last_Restart') \<and>
      n = n' \<and> brk = brk' \<and> ebrk = ebrk'}\<close>]
      restart_prog_spec[THEN fref_to_Down_curry4_5])
    subgoal
      by auto
    subgoal for ebrk ebrka x x'
      unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case case_prod_beta comp_def
      apply (rule exI[of _ \<open>fst (snd (snd ((x'))))\<close>])
      apply (rule exI[of _ \<open>fst (snd (snd (snd ((x')))))\<close>])
      apply (rule_tac exI[of _ \<open>fst (snd (snd (snd (snd (snd (x'))))))\<close>])
      apply (rule_tac exI[of _ m\<^sub>0])
      apply (rule_tac exI[of _ T\<^sub>0])
      apply (rule_tac exI[of _ U\<^sub>0])
      by simp
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    done
qed

lemma cdcl_twl_stgy_restart_prog_bounded_cdcl_twl_stgy_restart_prog_bounded_int:
  \<open>(cdcl_twl_stgy_restart_prog_bounded, cdcl_twl_stgy_restart_prog_bounded_int) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close> for x x'
    using that by auto
  show ?thesis
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    apply (rule order_trans[OF cdcl_twl_stgy_restart_prog_boundedg_cdcl_twl_stgy_restart_prog_bounded_intg])
    apply (auto simp add: )
    done
qed
thm twl_restart_inv_def
lemma (in twl_restart) cdcl_twl_stgy_prog_bounded_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_bounded S \<le> partial_conclusive_TWL_run S\<close>
  apply (rule order_trans)
  apply (rule cdcl_twl_stgy_restart_prog_bounded_cdcl_twl_stgy_restart_prog_bounded_int[THEN fref_to_Down, of _ S])
  apply simp
  apply simp
  apply (rule order_trans[OF ref_two_step'])
  apply (rule cdcl_twl_stgy_prog_bounded_int_spec)
  apply ((use assms in \<open>auto simp: twl_restart_inv_def pcdcl_stgy_restart_inv_def
    twl_struct_invs_def twl_stgy_restart_inv_def partial_conclusive_TWL_run2_def
    partial_conclusive_TWL_run_def\<close>)+)[4]
  unfolding partial_conclusive_TWL_run2_def partial_conclusive_TWL_run_def
  by fastforce


definition cdcl_twl_stgy_restart_prog_early_intg
  :: "'v twl_st \<Rightarrow>'v twl_st \<Rightarrow>'v twl_st \<Rightarrow> 'v twl_st nres"
where
  \<open>cdcl_twl_stgy_restart_prog_early_intg S\<^sub>0 T\<^sub>0 U\<^sub>0=
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, last_GC, last_Restart, T,m, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, 0, 0) o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, last_GC, last_Restart, S, m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (last_GC, last_Restart, T, m, n) \<leftarrow> restart_prog_int last_GC last_Restart T m n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict T \<noteq> None, last_GC, last_Restart, T, m, n)
      })
      (ebrk, False, S\<^sub>0, T\<^sub>0, U\<^sub>0, 0, 0);
    if \<not>brk then do {
      (brk, last_GC, last_Restart, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (last_GC, last_Restart, T, m, n)\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, last_GC, last_Restart, S, m, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog T;
	  (last_GC, last_Restart, T, m, n) \<leftarrow> restart_prog_int last_GC last_Restart T m n brk;
	  RETURN (brk \<or> get_conflict T \<noteq> None, last_GC, last_Restart, T, m, n)
	})
	(False, last_GC, last_Restart, T, m, n);
      RETURN T
    }
    else RETURN T
  }\<close>

lemmas cdcl_twl_stgy_restart_prog_early_int_def =
  cdcl_twl_stgy_restart_prog_early_intg_def

lemma cdcl_twl_stgy_restart_prog_early_intg_alt_def:
  \<open>cdcl_twl_stgy_restart_prog_early_intg S\<^sub>0  T\<^sub>0 U\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, last_GC, last_Restart, T,m, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_int_inv (S\<^sub>0, T\<^sub>0, U\<^sub>0, 0, 0) o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, last_GC, last_Restart, S, m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (last_GC, last_Restart, T, m, n) \<leftarrow> restart_prog_int last_GC last_Restart T m n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict T \<noteq> None, last_GC, last_Restart, T, m, n)
      })
      (ebrk, False, S\<^sub>0, T\<^sub>0, U\<^sub>0, 0, 0);
    if \<not>brk then do {
        cdcl_twl_stgy_restart_prog_intg m n last_GC last_Restart T
      } else RETURN T
  }\<close>
   unfolding cdcl_twl_stgy_restart_prog_intg_def cdcl_twl_stgy_restart_prog_early_intg_def
   by (auto intro!: bind_cong[OF refl])

definition cdcl_twl_stgy_restart_prog_early :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_restart_prog_early S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, last_GC, last_Restart, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv (S\<^sub>0, 0) o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, last_GC, last_Restart, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, last_GC, last_Restart, n) \<leftarrow> restart_prog T last_GC last_Restart n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk \<or> get_conflict T \<noteq> None, T, last_GC, last_Restart, n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), size (get_all_learned_clss S\<^sub>0), 0);
    if \<not>brk then do {
      (brk, T, last_GC, last_Restart, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv (T, n)\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, S, last_GC, last_Restart, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog T;
	  (T, last_GC, last_Restart, n) \<leftarrow> restart_prog T last_GC last_Restart n brk;
	  RETURN (brk \<or> get_conflict T \<noteq> None, T, last_GC, last_Restart, n)
	})
	(False, T, last_GC, last_Restart, n);
      RETURN T
    }
    else RETURN T
  }\<close>

abbreviation cdcl_twl_stgy_restart_prog_early_int where
  \<open>cdcl_twl_stgy_restart_prog_early_int S \<equiv> cdcl_twl_stgy_restart_prog_early_intg S S S\<close>


lemma (in twl_restart) cdcl_twl_stgy_prog_early_int_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_early_int S \<le> conclusive_TWL_run S\<close>
proof -
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_intg_alt_def conclusive_TWL_run_def
    apply (refine_vcg
      cdcl_twl_stgy_restart_prog_int_spec[THEN order_trans]
      WHILEIT_rule[where
      R = \<open>cdcl_algo_termination_early_rel\<close>];
      remove_dummy_vars)
    subgoal
      by (rule wf_cdcl_algo_termination_early_rel)
    subgoal
      using assms by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_restart_inv_def
        twl_struct_invs_def pcdcl_stgy_restart_inv_def twl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
        twl_restart_inv_def
        dest!: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
        twl_restart_inv_def
        dest: rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def twl_stgy_restart_inv_def
        twl_restart_inv_def no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp
        dest: rtranclp_cdcl_twl_stgy_restart_twl_restart_inv)
    subgoal by fast
    subgoal for x a aa ab ac ad ae be xa
      using assms
      using
        rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[of \<open>(S, S, S, 0, 0, True)\<close>
        \<open>(ab, ac, ad, ae, be, True)\<close>]
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_def
         twl_restart_inv_def
        intro: rtranclp_cdcl_twl_stgy_entailed_by_init
        dest!: rtranclp_cdcl_twl_cp_stgyD
        simp flip:  state\<^sub>W_of_def)
    subgoal
      by (rule restart_prog_bounded_spec)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_alt_def twl_restart_inv_def
        twl_stgy_restart_inv_def pcdcl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_alt_def twl_restart_inv_def
        twl_stgy_restart_inv_def pcdcl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_alt_def twl_restart_inv_def
        twl_stgy_restart_inv_def pcdcl_stgy_restart_inv_def)
    subgoal
      by (auto simp: cdcl_twl_stgy_restart_prog_int_inv_alt_def twl_restart_inv_def
        twl_stgy_restart_inv_def pcdcl_stgy_restart_inv_def)
    subgoal for x a aa ab ac ad ae be
      unfolding conclusive_TWL_run2_def cdcl_twl_stgy_restart_prog_int_inv_def
        cdcl_twl_stgy_restart_prog_int_inv_alt_def comp_def snd_conv
      apply (rule SPEC_rule)
      apply normalize_goal+
      apply (rule_tac x=xb in exI)
      apply (rule_tac x=xc in exI)
      apply (rule_tac x=xd in exI)
      apply (rule_tac x=0 in exI)
      apply (rule_tac x=0 in exI)
      apply auto
      done
    subgoal for x a aa ab ac ad ae be
      unfolding conclusive_TWL_run2_def cdcl_twl_stgy_restart_prog_int_inv_def
        cdcl_twl_stgy_restart_prog_int_inv_alt_def comp_def snd_conv
      apply normalize_goal+
      apply (rule_tac x=ab in exI)
      apply (rule_tac x=ac in exI)
      apply (rule_tac x= \<open>(ae, be, \<not>aa)\<close> in exI)
      apply (rule_tac x=0 in exI)
      apply (rule_tac x=0 in exI)
      apply auto
      done
    done
qed

lemma cdcl_twl_stgy_restart_prog_early_cdcl_twl_stgy_restart_prog_early:
  \<open>cdcl_twl_stgy_restart_prog_early S \<le> \<Down>Id (cdcl_twl_stgy_restart_prog_early_int S)\<close>
proof -
  have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close> for x x'
    using that by auto
  show ?thesis
    unfolding cdcl_twl_stgy_restart_prog_early_def cdcl_twl_stgy_restart_prog_early_int_def
      uncurry_def
    apply (refine_rcg
      WHILEIT_refine[where R = \<open>{((ebrk :: bool, brk :: bool,  S :: 'v twl_st, last_GC, last_Restart, n),
     (ebrk', brk', last_GC', last_Restart', S', m', n')).
    S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
    last_Restart = size (get_all_learned_clss last_Restart') \<and>
      n = n' \<and> brk = brk' \<and> ebrk = ebrk'}\<close>]
      WHILEIT_refine[where R = \<open>{((brk :: bool,  S :: 'v twl_st, last_GC, last_Restart, n),
     (brk', last_GC', last_Restart', S', m', n')).
    S = S' \<and> last_GC = size (get_all_learned_clss last_GC') \<and>
    last_Restart = size (get_all_learned_clss last_Restart') \<and>
      n = n' \<and> brk = brk'}\<close>]
      restart_prog_spec[THEN fref_to_Down_curry4_5])
    subgoal
      by auto
    subgoal for ebrk ebrka x x'
      unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case case_prod_beta comp_def
      apply (rule exI[of _ \<open>fst (snd (snd ((x'))))\<close>])
      apply (rule exI[of _ \<open>fst (snd (snd (snd ((x')))))\<close>])
      apply (rule_tac exI[of _ \<open>fst (snd (snd (snd (snd (snd (x'))))))\<close>])
      apply (rule_tac exI[of _ 0])
      apply (rule_tac exI[of _ S])
      apply (rule_tac exI[of _ S])
      by simp
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by auto
    subgoal for ebrk ebrka x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h
      x2h x1i x2i x1j x2j xa x'a
      unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case case_prod_beta comp_def
      apply (rule exI[of _ \<open>fst (snd (((x'a))))\<close>])
      apply (rule exI[of _ \<open>fst (snd (snd (((x'a)))))\<close>])
      apply (rule_tac exI[of _ \<open>fst ((snd (snd (snd (snd (x'a))))))\<close>])
      apply (rule_tac exI[of _ x1e])
      apply (rule_tac exI[of _ x1b])
      apply (rule_tac exI[of _ x1c])
      apply (cases x'a)
      by simp
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    apply (rule this_is_the_identity)
    subgoal
      by auto
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    done
qed

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_early_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close> \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init (state\<^sub>W_of S)\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_early S \<le> conclusive_TWL_run S\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_restart_prog_early_cdcl_twl_stgy_restart_prog_early])
  apply (subst Down_id_eq)
  apply (rule cdcl_twl_stgy_prog_early_int_spec[OF assms])
  done

end

end
