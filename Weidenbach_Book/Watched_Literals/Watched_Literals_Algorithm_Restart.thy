theory Watched_Literals_Algorithm_Restart
imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Restart
begin

context twl_restart_ops
begin

text \<open>
  In the transition system we need to talk about the intermediate state from which we have
  to remember of learned clauses. Therefore, we have introduce an intermediate function that
  stores the state in order to be able to relate it to the function. We initially tried to keep
  it existentially, but this would allow to change the intermediate state each time and we did
  not manage to write the proof.
\<close>
text \<open>Restarts are never necessary\<close>
definition restart_required :: "'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required S m n = SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss S) - m > f n)\<close>

definition (in -) restart_prog_pre :: \<open>'v twl_st \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_prog_pre S brk \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
    (\<not>brk \<longrightarrow> get_conflict S = None)\<close>

definition restart_prog
  :: \<open>'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (bool \<times> 'v twl_st \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog S m n brk = do {
     ASSERT(restart_prog_pre S brk);
     b \<leftarrow> restart_required S m n;
     b2 \<leftarrow> SPEC(\<lambda>_. b \<longrightarrow> size (get_all_learned_clss S) > m);
     if b2 \<and> b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only S T);
       RETURN (True, T, size (get_all_learned_clss T), n)
     }
     else
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
       U \<leftarrow> SPEC(\<lambda>U. cdcl_twl_stgy\<^sup>*\<^sup>* T U \<and> clauses_to_update U = {#} \<and>
          get_conflict U = None);
       RETURN (True, U, size (get_all_learned_clss U), n + 1)
     }
     else
       RETURN (False, S, m, n)
   }\<close>

fun cdcl_twl_stgy_restart_prog_inv where
  \<open>cdcl_twl_stgy_restart_prog_inv S\<^sub>0 (brk, S, T, m, n) \<longleftrightarrow>
    twl_struct_invs S\<^sub>0 \<and>
    twl_struct_invs T \<and> twl_stgy_invs T \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart_with_leftovers (S\<^sub>0, 0, True) m S (T, n, True) \<and>
    clauses_to_update T = {#} \<and> (\<not>brk \<longrightarrow> get_conflict T = None)\<close>

lemmas cdcl_twl_stgy_restart_prog_inv_def[simp del] =
  cdcl_twl_stgy_restart_prog_inv.simps

text \<open>
  In the main loop, and purely to simplify the proof, we remember the state obtained after the last
  restart in order to relate it to the number of clauses. In a first proof attempt, we try to make
  do without it by only assuming its existence, but we could no prove that the loop terminates,
  because the state can change each time.

  This state is not needed at all in the execution and will be removed in the next refinement step.
\<close>
definition cdcl_twl_stgy_restart_prog :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_restart_prog S\<^sub>0 =
  do {
    (brk, _, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, S', m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S';
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (b, T, m', n') \<leftarrow> restart_prog T m n brk;
        RETURN (brk, if b then T else S, T, m', n')
      })
      (False, S\<^sub>0, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), 0);
    RETURN T
  }\<close>

abbreviation cdcl_algo_termination_rel :: \<open>((bool \<times> 'v twl_st \<times> 'v twl_st \<times> nat \<times> nat) \<times> _) set\<close> where
  \<open>cdcl_algo_termination_rel \<equiv>
    {((brkT, T, T', n, n'), brkS, S, _, m, m').
                              twl_struct_invs S \<and>
                              \<not> brkS \<and>
                              cdcl_twl_stgy_restart_with_leftovers1
                             (S, m', \<not>brkS) (T, n', \<not>brkT)} \<union>
                           {((brkT, T, T', n, n'), (brkS, S, S', m, m')). S = T \<and> \<not> brkS \<and> n' = m' \<and>
                             twl_struct_invs S' \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S' T'} \<union>
                           {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>

abbreviation cdcl_algo_termination_early_rel
  :: \<open>((bool \<times> bool \<times> 'v twl_st \<times> 'v twl_st \<times> nat \<times> nat) \<times> _) set\<close>
where
  \<open>cdcl_algo_termination_early_rel \<equiv>
    {((ebrkT, brkT, T, T', n, n'), ebrkS, brkS, S, _, m, m').
                              twl_struct_invs S \<and>
                              \<not> brkS \<and>
                              cdcl_twl_stgy_restart_with_leftovers1
                             (S, m', \<not>brkS) (T, n', \<not>brkT)} \<union>
    {((ebrkT, brkT, T, T', n, n'), (ebrkS, brkS, S, S', m, m')). S = T \<and> \<not> brkS\<and> \<not> ebrkS \<and> n' = m' \<and>
                             twl_struct_invs S' \<and> cdcl_twl_stgy\<^sup>+\<^sup>+ S' T'} \<union>
    {((ebrkT, brkT, T), ebrkS, brkS, S). S = T \<and> (ebrkT \<or> brkT) \<and> \<not> brkS \<and> brkT}\<close>
end


context twl_restart
begin

lemma  wf_cdcl_algo_termination_early_rel: \<open>wf cdcl_algo_termination_early_rel\<close>
  apply (rule wf_union_compatible)
  apply (rule wf_union_compatible)
  subgoal
    by (rule wf_if_measure_in_wf[OF wf_cdcl_twl_stgy_restart_with_leftovers1,
        of _  \<open>\<lambda>(_, brkT, T, T', n, n'). (T, n', \<not>brkT)\<close>])
      auto
  subgoal
    by (rule wf_if_measure_in_wf[OF tranclp_wf_cdcl_twl_stgy,
        of _  \<open>\<lambda>(_, brkT, T, T', n, n'). T'\<close>])
      auto
  subgoal
    by auto
  subgoal
    by (rule wf_no_loop) auto
  subgoal
    by auto
  done

lemma  wf_cdcl_algo_termination_rel: \<open>wf cdcl_algo_termination_rel\<close>
  by (rule wf_if_measure_in_wf[OF wf_cdcl_algo_termination_early_rel,
      of _  \<open>\<lambda>(brkT, T, T', n, n'). (False, brkT, T, T', n, n')\<close>])
    auto

lemma restart_prog_spec:
  assumes
    inv: \<open>(cdcl_twl_stgy_restart_prog_inv S o snd) (ebrkU, brkU, T, U, m, n)\<close> and
    cond: \<open>case (ebrkU, brkU, T, U, m, n) of (ebrk, brk, uu_) \<Rightarrow> \<not> brk \<and> \<not>ebrk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec V (brkT, W)\<close> and
    struct_invs_V: \<open>twl_struct_invs V\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* U V\<close> and
    lits_to_update: \<open>literals_to_update V = {#}\<close> and
    \<open>\<forall>S'. \<not> cdcl_twl_cp V S'\<close> and
    \<open>twl_stgy_invs V\<close>
  shows \<open>restart_prog W m n brkT
         \<le> SPEC
            (\<lambda>x. (case x of
                  (b, Ta, m', n') \<Rightarrow> do {
                    ebrk \<leftarrow> RES UNIV;
                    RETURN (ebrk, brkT, (if b then Ta else T), Ta, m', n')})
                 \<le> SPEC
                    (\<lambda>s'. (cdcl_twl_stgy_restart_prog_inv S o snd) s' \<and>
                          (s', ebrkU, brkU, T, U, m, n)
                          \<in> cdcl_algo_termination_early_rel))\<close>
    (is \<open>_ \<le> SPEC (\<lambda>x. _ \<le> SPEC(\<lambda>s. ?I s \<and> _ \<in> ?term))\<close>)
proof -
  have [simp]: \<open>\<not>brkU\<close> \<open>\<not>ebrkU\<close>
    using cond by auto
  have struct_invs': \<open>cdcl_twl_restart W T' \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* T' V' \<Longrightarrow> twl_struct_invs V'\<close> for T' V'
    using assms(3) cdcl_twl_restart_twl_struct_invs
    by (metis (no_types, lifting) case_prodD rtranclp_cdcl_twl_stgy_twl_struct_invs)
  have stgy_invs: \<open>cdcl_twl_restart W V' \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V' W' \<Longrightarrow> twl_stgy_invs W'\<close> for V' W'
    using assms(3) cdcl_twl_restart_twl_stgy_invs
    by (metis (no_types, lifting) case_prodD cdcl_twl_restart_twl_struct_invs
      rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_S: \<open>twl_struct_invs S\<close> and
    struct_invs_U: \<open>twl_struct_invs U\<close> and
    twl_stgy_invs_U: \<open>twl_stgy_invs U\<close> and
    \<open>brkU \<longrightarrow> final_twl_state U\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m T (U, n, True)\<close> and
    clss_T: \<open>clauses_to_update U = {#}\<close> and
    confl: \<open>\<not> brkU \<longrightarrow> get_conflict U = None\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case comp_def snd_conv by fast+

  have
    cdcl_o: \<open>cdcl_twl_o\<^sup>*\<^sup>* V W\<close> and
    conflict_W: \<open>get_conflict W \<noteq> None \<Longrightarrow> count_decided (get_trail W) = 0\<close> and
    brk'_no_step: \<open>brkT \<Longrightarrow> final_twl_state W\<close> and
    struct_invs_W: \<open>twl_struct_invs W\<close> and
    stgy_invs_W: \<open>twl_stgy_invs W\<close> and
    clss_to_upd_W: \<open>clauses_to_update W = {#}\<close> and
    lits_to_upd_W: \<open>\<not> brkT \<longrightarrow> literals_to_update W \<noteq> {#}\<close> and
    confl_W: \<open>\<not> brkT \<longrightarrow> get_conflict W = None\<close>
    using other_inv unfolding final_twl_state_def by fast+

  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close>
    by (meson cdcl_o assms(5) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD
        rtranclp_trans)
  from twl_res have
    STa: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (T, n, True)\<close> and
    TaT: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> and
    m: \<open>m = size (get_all_learned_clss T)\<close>
    unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case snd_conv fst_conv
    by blast+
  have struct_invs_T: \<open>twl_struct_invs T\<close>
    using STa rtranclp_cdcl_twl_stgy_restart_twl_struct_invs struct_invs_S by fastforce
  have restart_prog_pre_W: \<open>restart_prog_pre W brkT\<close>
    using confl_W stgy_invs_W struct_invs_W
    unfolding restart_prog_pre_def
    by fast

  have UW: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* U W\<close>
    by (meson \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_trans)
    have TW: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T W\<close>
      by (metis (no_types) TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> local.cp
        rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp rtranclp_unfold)
  have only_restart: \<open>?I (ebrk, False, if True then Y else T, Y, size (get_all_learned_clss Y), n)\<close> (is ?A) and
     only_restart_term: \<open>((ebrk, False, (if True then Y else T), Y, size (get_all_learned_clss Y), n),
        ebrkU, brkU, T, U, m, n)
        \<in> ?term\<close> (is ?B)
    if
      \<open>True \<longrightarrow> f n < size (get_all_learned_clss W) - m\<close> and
      m_size_W: \<open>True \<longrightarrow> m < size (get_all_learned_clss W)\<close> and
      WY: \<open>cdcl_twl_restart_only W Y\<close> and
      brkX and
      X and
      \<open>\<not> brkT\<close>
    for X brkX Y ebrk
  proof -
    have \<open>size (get_all_learned_clss T) \<le> size (get_all_learned_clss U)\<close>
      using rtranclp_cdcl_twl_stgy_size_get_all_learned[of T U] TaT
      by auto
    have TW: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T W\<close>
      by (metis (no_types) TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W lits_to_update local.cp
        rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp rtranclp_unfold that(6))
    have UW: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ U W\<close>
      by (metis (mono_tags) Nitpick.rtranclp_unfold \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W
        lits_to_update local.cp that(6) tranclp_cdcl_twl_cp_stgyD tranclp_rtranclp_tranclp)
    have \<open>twl_struct_invs Y\<close>
      using WY cdcl_twl_restart_only_twl_struct_invs struct_invs_W by blast
    moreover have \<open>twl_stgy_invs Y\<close>
      using WY cdcl_twl_stgy_restart_only_twl_stgy_invs stgy_invs_W by blast
    moreover have \<open>clauses_to_update Y = {#}\<close> \<open>get_conflict Y = None\<close>
      using WY by (auto simp: cdcl_twl_restart_only.simps)
    moreover {
      have \<open>cdcl_twl_stgy_restart (T, n, True) (Y, n, True)\<close>
        by (rule restart_noGC[OF _ _ WY])
         (auto simp: m_size_W UW TW  m[symmetric])
      then have \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True)
        (size (get_all_learned_clss Y)) Y (Y, n, True)\<close>
        using STa
        unfolding cdcl_twl_stgy_restart_with_leftovers_def
        by auto
    }
    ultimately show ?A
      using struct_invs_S
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def)
    have \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (Y, n, True)\<close>
      using m_size_W
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def m
      by (auto intro!: cdcl_twl_stgy_restart.intros(2)[of _ W] simp: WY TW UW)
    then show ?B by (auto simp: struct_invs_T m)
  qed
  have full_restart: \<open>?I (ebrk, False, if True then Z else T, Z, size (get_all_learned_clss Z), n + 1)\<close> (is ?A)and
    full_restart_term:
      \<open>((ebrk, False, if True then Z else T, Z, size (get_all_learned_clss Z), n + 1), ebrkU, brkU, T, U, m, n)
    \<in> ?term\<close> (is ?B)
    if
      \<open>restart_prog_pre W False\<close> and
      m_size: \<open>True \<longrightarrow> f n < size (get_all_learned_clss W) - m\<close> and
      \<open>True \<longrightarrow> m < size (get_all_learned_clss W)\<close> and
      \<open>\<not> (brkX \<and> True \<and> \<not> False)\<close> and
      WY: \<open>cdcl_twl_restart W Y\<close> and
      X and
      \<open>\<not> brkT\<close> and
      YZ: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Y Z\<close> and
      clss_Z: \<open>clauses_to_update Z = {#}\<close> and
      confl_Z: \<open>get_conflict Z = None\<close>
    for X brkX Y Z ebrk
  proof -
    have TW: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T W\<close>
      by (metis (no_types) TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W lits_to_update local.cp
        rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp rtranclp_unfold that(7))
    have UW: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ U W\<close>
      by (metis (mono_tags) Nitpick.rtranclp_unfold \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W
        lits_to_update local.cp that(7) tranclp_cdcl_twl_cp_stgyD tranclp_rtranclp_tranclp)
    have UZ: \<open>cdcl_twl_stgy_restart (T, n, True) (Z, Suc n, True)\<close>
      apply (rule restart_step[OF TW _ WY YZ])
      using m_size
      unfolding m[symmetric]
      by (auto simp: m UW clss_Z confl_Z)
    have \<open>twl_struct_invs Z\<close>
      using struct_invs' WY YZ by blast
    moreover have \<open>twl_stgy_invs Z\<close>
      using WY YZ stgy_invs by blast
    moreover have \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True)
        (size (get_all_learned_clss Z)) Z (Z, Suc n, True)\<close>
        using STa UZ
        by (auto simp: cdcl_twl_stgy_restart_with_leftovers_def)
    ultimately show ?A
      using struct_invs_S YZ WY clss_Z confl_Z
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def)
    have \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (Z, Suc n, True)\<close>
      using UZ by (auto simp: cdcl_twl_stgy_restart_with_leftovers1_def)
    then show ?B
      by (auto simp: struct_invs_T)
  qed
  have no_restart: \<open>?I (ebrk, brkT, if False then W else T, W, m, n)\<close>
    for ebrk :: bool
    using struct_invs_S STa TW
    by (auto simp: struct_invs_S struct_invs_W stgy_invs_W clss_to_upd_W confl_W
      cdcl_twl_stgy_restart_with_leftovers_def m brk'_no_step cdcl_twl_stgy_restart_prog_inv_def)

  have no_restart_term: \<open>cdcl_twl_stgy_restart_with_leftovers1 (U, n, True) (W, n, \<not> brkT)\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ U W\<close> if \<open>\<not> cdcl_twl_stgy_restart (U, n, True) (W, n, \<not> brkT)\<close>
    proof -
      have "(\<not> brkT \<or> \<not> cdcl_twl_stgy\<^sup>*\<^sup>* U W) \<or> \<not> pcdcl_twl_final_state W"
        using twl_restart_ops.cdcl_twl_stgy_restart.restart_full that by fastforce
      then show "cdcl_twl_stgy\<^sup>+\<^sup>+ U W"
        by (metis (no_types) Nitpick.rtranclp_unfold \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> brk'_no_step
          final_twl_state_def lits_to_upd_W lits_to_update local.cp pcdcl_twl_final_state_def
          rtranclp_cdcl_twl_cp_stgyD tranclp_rtranclp_tranclp)
    qed
    moreover have False if \<open>\<not>cdcl_twl_stgy_restart (U, n, True) (W, n, False)\<close> and brkT
      using UW brk'_no_step final_twl_state_def pcdcl_twl_final_state_def that
        twl_restart_ops.cdcl_twl_stgy_restart.restart_full by blast
    ultimately show ?thesis
      by (auto simp: cdcl_twl_stgy_restart_with_leftovers1_def)
  qed
  have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ U W \<or> U = W\<close>
    by (meson UW rtranclp_unfold)
  then have no_restart_term: \<open>((ebrk, brkT, if False then W else T, W, m, n), ebrkU, brkU, T, U, m, n)
    \<in> ?term\<close> for ebrk
    using no_restart_term
    apply (auto simp: struct_invs_T struct_invs_U)
    by (metis (no_types, lifting) \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W lits_to_update local.cp
      rtranclp_cdcl_twl_cp_stgyD rtranclp_into_tranclp1 rtranclp_unfold tranclp_idemp)+

  show ?thesis
    unfolding restart_prog_def restart_required_def
    apply (refine_vcg; remove_dummy_vars)
    subgoal by (rule restart_prog_pre_W)
    subgoal for X brkX Y
      by (rule only_restart)
    subgoal for X brkX Y
      by (rule only_restart_term)
    subgoal for X brkX Y Z
      by (rule full_restart)
    subgoal for X brkX Y Z
      by (rule full_restart_term)
    subgoal for brk brk'
      by (rule no_restart)
    subgoal for brk brk'
      by (rule no_restart_term)
    done
qed

definition cdcl_twl_stgy_restart_prog_bounded :: "'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres" where
  \<open>cdcl_twl_stgy_restart_prog_bounded S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, _, _, T, _, n) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv S\<^sub>0 o snd\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S', S, m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (b, T, m, n) \<leftarrow> restart_prog T m n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, if b then T else S', T, m, n)
      })
      (ebrk, False, S\<^sub>0, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), 0);
    RETURN (ebrk, T)
  }\<close>

lemma (in twl_restart) cdcl_twl_stgy_prog_bounded_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_bounded S \<le> SPEC(\<lambda>(brk, T). \<exists> S' m n. (cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m S' (T, n, True) \<and>
        (\<not>brk \<longrightarrow> final_twl_state T)))\<close>
    (is \<open>_ \<le> SPEC ?P\<close>)
proof -
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding cdcl_twl_stgy_restart_prog_bounded_def full_def
    apply (refine_vcg
        WHILEIT_rule[where
           R = \<open>cdcl_algo_termination_early_rel\<close>];
        remove_dummy_vars)
    subgoal
      by (rule wf_cdcl_algo_termination_early_rel)
    subgoal using assms
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def)
    subgoal using assms
      by (auto dest: rtranclp_cdcl_twl_stgy_restart_twl_struct_invs
        simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def)
    subgoal using assms
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
        dest!: rtranclp_cdcl_twl_stgy_restart_clauses_to_update)
    subgoal using assms
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
        dest!: rtranclp_cdcl_twl_stgy_restart_get_conflict)
    subgoal
      using assms
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
        dest: rtranclp_cdcl_twl_stgy_restart_twl_stgy_invs)
    subgoal
      using assms
      by (auto simp: cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
        no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal for brkU U T m n V brkT W
      by (rule restart_prog_spec)
    subgoal for init_ebrk brkT T' m n ebrk T
      by (rule_tac x=T' in exI) (auto simp: cdcl_twl_stgy_restart_prog_inv_def)
    done
qed


lemma cdcl_twl_stgy_restart_prog_spec:
  fixes S :: \<open>'v twl_st\<close>
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog S \<le> SPEC(\<lambda>T.
       \<exists>S' m n. cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m S' (T, n, True) \<and>
        final_twl_state T)\<close>
    (is \<open>_ \<le> SPEC(\<lambda>T. ?P T)\<close>)
proof -
  have cdcl_twl_stgy_restart_prog_alt_def:
    \<open>cdcl_twl_stgy_restart_prog S\<^sub>0 =
    do {
    _ \<leftarrow> RETURN False;
    (brk, _, T, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, S', m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S';
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (b, T, m', n') \<leftarrow> restart_prog T m n brk;
        _ \<leftarrow> RETURN False;
        RETURN (brk, if b then T else S, T, m', n')
      })
      (False, S\<^sub>0, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), 0);
    RETURN T
    }\<close> for S\<^sub>0 :: \<open>'v twl_st\<close>
    unfolding cdcl_twl_stgy_restart_prog_def
    by auto
  have [refine]: \<open>RETURN False \<le> \<Down> {(b, b'). (b = b') \<and> \<not>b} (RES UNIV)\<close>
    by (auto intro!: RETURN_RES_refine)
   have [refine]: \<open>((False, S, S, size (get_all_learned_clss S), (0 :: nat)), ebrk, False, S, S,
     size (get_all_learned_clss S), 0) \<in> {(T, (b, S)). S = T \<and> \<not>b}\<close>
     if \<open>(u, ebrk) \<in> {(b, b'). (b = b') \<and> \<not>b}\<close> for ebrk u
     using that
     by auto
   have this_is_the_identity: \<open>x \<le> \<Down>Id (x')\<close> if \<open>x = x'\<close>
     for x x'
     using that by auto

  have ref_early: \<open>cdcl_twl_stgy_restart_prog S \<le> \<Down>{((S), (ebrk, T)). S = T \<and> \<not>ebrk} (cdcl_twl_stgy_restart_prog_bounded S)\<close>
    unfolding cdcl_twl_stgy_restart_prog_alt_def cdcl_twl_stgy_restart_prog_bounded_def
    apply refine_rcg
    apply assumption
    subgoal by auto
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by auto
    apply (rule this_is_the_identity)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done

  show ?thesis
    apply (rule order_trans[OF ref_early])
    apply (rule order_trans[OF ref_two_step'])
    apply (rule cdcl_twl_stgy_prog_bounded_spec[OF assms])
    unfolding conc_fun_RES by fastforce
qed

end

end
