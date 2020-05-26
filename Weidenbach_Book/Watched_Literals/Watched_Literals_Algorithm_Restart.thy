theory Watched_Literals_Algorithm_Restart
imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Restart
  "../../lib/Explorer"
begin

context twl_restart_ops
begin

text \<open>Restarts are never necessary\<close>
definition restart_required :: "'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required S m n = SPEC (\<lambda>b. b \<longrightarrow> size (get_all_learned_clss S) - m > f n)\<close>

definition (in -) restart_prog_pre :: \<open>'v twl_st \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_prog_pre S brk \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
    (\<not>brk \<longrightarrow> get_conflict S = None)\<close>

definition restart_prog
  :: \<open>'v twl_st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st \<times> nat \<times> nat) nres\<close>
where
  \<open>restart_prog S m n brk = do {
     ASSERT(restart_prog_pre S brk);
     b \<leftarrow> restart_required S m n;
     b2 \<leftarrow> SPEC(\<lambda>_. b \<longrightarrow> size (get_all_learned_clss S) > m);
     if b2 \<and> b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart_only S T);
       RETURN (T, size (get_all_learned_clss T), n)
     }
     else
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
       U \<leftarrow> SPEC(\<lambda>U. cdcl_twl_stgy\<^sup>*\<^sup>* T U \<and> clauses_to_update U = {#} \<and>
          get_conflict U = None);
       RETURN (U, size (get_all_learned_clss U), n + 1)
     }
     else
       RETURN (S, m, n)
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

definition cdcl_twl_stgy_restart_prog :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_restart_prog S\<^sub>0 =
  do {
    (brk, T, _, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>cdcl_twl_stgy_restart_prog_inv S\<^sub>0\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, S', m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, m', n') \<leftarrow> restart_prog T m n brk;
        RETURN (brk, T, T, m', n')
      })
      (False, S\<^sub>0, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), 0);
    RETURN T
  }\<close>
end

context twl_restart
begin


lemma restart_prog_spec:
  assumes
    inv: \<open>cdcl_twl_stgy_restart_prog_inv S (brkU, U, T, m, n)\<close> and
    cond: \<open>case (brkU, U, T, m, n) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec V (brkT, W)\<close> and
    struct_invs_V: \<open>twl_struct_invs V\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* U V\<close> and
    lits_to_update: \<open>literals_to_update V = {#}\<close> and
    \<open>\<forall>S'. \<not> cdcl_twl_cp V S'\<close> and
    \<open>twl_stgy_invs V\<close>
  shows \<open>restart_prog W m n brkT
         \<le> SPEC
            (\<lambda>x. (case x of
                  (Ta, m', n') \<Rightarrow>
                    RETURN (brkT, Ta, Ta, m', n'))
                 \<le> SPEC
                    (\<lambda>s'. cdcl_twl_stgy_restart_prog_inv S s' \<and>
                          (s', brkU, U, T, m, n)
                          \<in> {((brkT, T, T', n, n'), brkS, S, S', m, m').
                             twl_struct_invs S \<and>
                             \<not> brkS \<and>
                             cdcl_twl_stgy_restart_with_leftovers1
                              (S, m', \<not>brkS) (T, n', \<not>brkT)} \<union>
                            {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}))\<close>
proof -
  have [simp]: \<open>\<not>brkU\<close>
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
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    twl_stgy_invs_T: \<open>twl_stgy_invs T\<close> and
    \<open>brkU \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m U (T, n, True)\<close> and
    clss_T: \<open>clauses_to_update T = {#}\<close> and
    confl: \<open>\<not> brkU \<longrightarrow> get_conflict T = None\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case by fast+
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
    STa: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (U, n, True)\<close> and
    TaT: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* U T\<close> and
    m: \<open>m = size (get_all_learned_clss U)\<close>
    unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case snd_conv fst_conv
    by blast+

  have restart_prog_pre_W: \<open>restart_prog_pre W brkT\<close>
    using confl_W stgy_invs_W struct_invs_W
    unfolding restart_prog_pre_def
    by fast
  have struct_invs_U: \<open>twl_struct_invs U\<close>
    using rtranclp_cdcl_twl_stgy_restart_twl_struct_invs[OF STa] struct_invs_S
    by simp

  have UW: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* U W\<close>
    by (meson \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_trans)
  have only_restart: \<open>cdcl_twl_stgy_restart_prog_inv S
       (False, Y, Y, size (get_all_learned_clss Y), n)\<close> (is ?A) and
     only_restart_term: \<open>((False, Y, Y, size (get_all_learned_clss Y), n),
        brkU, U, T, m, n)
        \<in> {((brkT, T, T', n, n'), brkS, S, S', m, m').
        twl_struct_invs S \<and>
        \<not> brkS \<and>
        cdcl_twl_stgy_restart_with_leftovers1 (S, m', \<not>brkS) (T, n', \<not>brkT)} \<union>
        {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close> (is ?B)
    if
      \<open>True \<longrightarrow> f n < size (get_all_learned_clss W) - m\<close> and
      m_size_W: \<open>True \<longrightarrow> m < size (get_all_learned_clss W)\<close> and
      WY: \<open>cdcl_twl_restart_only W Y\<close> and
      brkX and
      X and
      \<open>\<not> brkT\<close>
    for X brkX Y
  proof -
    have \<open>twl_struct_invs Y\<close>
      using WY cdcl_twl_restart_only_twl_struct_invs struct_invs_W by blast
    moreover have \<open>twl_stgy_invs Y\<close>
      using WY cdcl_twl_stgy_restart_only_twl_stgy_invs stgy_invs_W by blast
    moreover have \<open>clauses_to_update Y = {#}\<close> \<open>get_conflict Y = None\<close>
      using WY by (auto simp: cdcl_twl_restart_only.simps)
    moreover {
      have \<open>cdcl_twl_stgy_restart (U, n, True) (Y, n, True)\<close>
        apply (rule restart_noGC[OF _ _ WY])
        unfolding m[symmetric]
        defer
        apply (auto simp: m_size_W UW)[]
        by (metis (mono_tags, hide_lams) Nitpick.rtranclp_unfold \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> UW lits_to_upd_W
          lits_to_update local.cp that(6) tranclp_cdcl_twl_cp_stgyD tranclp_rtranclp_tranclp)
      then have \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True)
        (size (get_all_learned_clss Y)) Y (Y, n, True)\<close>
        using STa
        unfolding cdcl_twl_stgy_restart_with_leftovers_def
        by auto
    }
    ultimately show ?A
      using struct_invs_S
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      by auto
    have \<open>cdcl_twl_stgy_restart_with_leftovers1 (U, n, True) (Y, n, True)\<close>
      using m_size_W
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def m
      apply (auto intro!: cdcl_twl_stgy_restart.intros(2)[of _ W] simp: WY)[]
      by (metis Nitpick.rtranclp_unfold UW nat_neq_iff)
    then show ?B by (auto simp: struct_invs_U m)
  qed
  have full_restart: \<open>cdcl_twl_stgy_restart_prog_inv S (False, Z, Z, size (get_all_learned_clss Z), n + 1)\<close> (is ?A)and
    full_restart_term:
      \<open>((False, Z, Z, size (get_all_learned_clss Z), n + 1), brkU, U, T, m, n)
    \<in> {((brkT, T, T', n, n'), brkS, S, S', m, m').
       twl_struct_invs S \<and>
       \<not> brkS \<and>
       cdcl_twl_stgy_restart_with_leftovers1 (S, m', \<not> brkS)
        (T, n', \<not> brkT)} \<union>
      {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close> (is ?B)
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
    for X brkX Y Z
  proof -
    have UW: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ U W\<close>
      by (metis (mono_tags) Nitpick.rtranclp_unfold \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> lits_to_upd_W
        lits_to_update local.cp that(7) tranclp_cdcl_twl_cp_stgyD tranclp_rtranclp_tranclp)
    have UZ: \<open>cdcl_twl_stgy_restart (U, n, True) (Z, Suc n, True)\<close>
      apply (rule restart_step[OF UW _ WY YZ])
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
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      by auto
    have \<open>cdcl_twl_stgy_restart_with_leftovers1 (U, n, True) (Z, Suc n, True)\<close>
      using UZ by (auto simp: cdcl_twl_stgy_restart_with_leftovers1_def)
    then show ?B
      by (auto simp: struct_invs_U)
  qed
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
    subgoal for X brkX
        
qed

lemma (in twl_restart)
  assumes
    inv: \<open>case (brk, T, m, n) of  (brk, T, m, n) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m n\<close> and
    cond: \<open>case (brk, T, m, n) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec S' (brk', U)\<close> and
    struct_invs_S: \<open>twl_struct_invs S'\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T S'\<close> and
    lits_to_update: \<open>literals_to_update S' = {#}\<close> and
    \<open>\<forall>S'a. \<not> cdcl_twl_cp S' S'a\<close> and
    \<open>twl_stgy_invs S'\<close> and
    brk: \<open>(brk', brk) \<in> bool_rel\<close>
  shows restart_prog_spec:
    \<open>restart_prog U m n brk'
         \<le> SPEC
             (\<lambda>x. (case x of
                   (T, m, na) \<Rightarrow> RETURN (brk', T, m, na))
                  \<le> SPEC
                      (\<lambda>s'. (case s' of
  (brk, T, m, n'') \<Rightarrow>
    twl_struct_invs T \<and>
    twl_stgy_invs T \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>brk) m S (T, n'', \<not>brk) \<and>
    clauses_to_update T = {#} \<and>
    (\<not> brk \<longrightarrow> get_conflict T = None)) \<and>
 (s', brk, T, n)
 \<in> {((brkT, T, m, n'), brkS, S, _).
     twl_struct_invs S \<and>
     cdcl_twl_stgy_restart_with_leftovers1 (S, n, \<not>brkS) (T, n', \<not>brkS)} \<union>
    {((brkT, T, _, _), brkS, S, _). S = T \<and> brkT \<and> \<not> brkS}))\<close> (is ?A)
proof -
  have brk[simp]: \<open>brk' = brk\<close>
    using brk by auto
  have struct_invs': \<open>cdcl_twl_restart U T \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* T V \<Longrightarrow> twl_struct_invs V\<close> for T V
    using assms(3) cdcl_twl_restart_twl_struct_invs
    by (metis (no_types, lifting) case_prodD rtranclp_cdcl_twl_stgy_twl_struct_invs)
  have stgy_invs: \<open>cdcl_twl_restart U V \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<Longrightarrow> twl_stgy_invs W\<close> for V W
    using assms(3) cdcl_twl_restart_twl_stgy_invs
    by (metis (no_types, lifting) case_prodD cdcl_twl_restart_twl_struct_invs
      rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close> and
    \<open>brk \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (T, n, True)\<close> and
    \<open>clauses_to_update T = {#}\<close> and
    confl: \<open>\<not> brk \<longrightarrow> get_conflict T = None\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case by fast+
  have
    cdcl_o: \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> and
    conflict_U: \<open>get_conflict U \<noteq> None \<Longrightarrow> count_decided (get_trail U) = 0\<close> and
    brk'_no_step: \<open>brk' \<Longrightarrow> final_twl_state U\<close> and
    struct_invs_U: \<open>twl_struct_invs U\<close> and
    stgy_invs_U: \<open>twl_stgy_invs U\<close> and
    clss_to_upd_U: \<open>clauses_to_update U = {#}\<close> and
    lits_to_upd_U: \<open>\<not> brk' \<longrightarrow> literals_to_update U \<noteq> {#}\<close> and
    confl_U: \<open>\<not> brk' \<longrightarrow> get_conflict U = None\<close>
    using other_inv unfolding final_twl_state_def by fast+

  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
    by (meson \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> assms(5) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD
        rtranclp_trans)
  from twl_res obtain Ta where
    STa: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (Ta, n, True)\<close> and
    TaT: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta T\<close> and
    m: \<open>m = size (get_all_learned_clss Ta)\<close>
    unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case snd_conv fst_conv
    by blast
  have
    twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close> and
    rtranclp_twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (W, n + 1, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (size (get_all_learned_clss W))
        (W, n + 1, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
    \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (size (get_all_learned_clss W))
         (W, Suc n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
    if
      f: \<open>True \<longrightarrow> f (snd (U, n)) < size (get_all_learned_clss (fst (U, n))) - m\<close> and
      res: \<open>cdcl_twl_restart U V\<close> and
      pre: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V W
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)

    show twl_res_T_V[unfolded not_False_eq_True]:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
      unfolding not_False_eq_True
      apply (rule cdcl_twl_stgy_restart.restart_step[of _ U _ V])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      subgoal using pre by simp
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False)
        (size (get_all_learned_clss W)) (W, Suc n, \<not>False)\<close>
      unfolding not_False_eq_True cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>W\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (W, n + 1, \<not>False)\<close>
      using twl_res twl_res_T_V STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (auto dest: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart)
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (size (get_all_learned_clss W))
        (W, n + 1, \<not>False)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ W]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def not_False_eq_True
      by fast
  qed
  let ?m = \<open>\<lambda>W. (size (get_all_learned_clss W))\<close>
  have
    twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close> and
    rtranclp_twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_only:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart_only:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
    if
      f: \<open>True \<longrightarrow> m < size (get_all_learned_clss U)\<close> and
      res: \<open>cdcl_twl_restart_only U V\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close> and st2: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)+

    show twl_res_T_V[unfolded not_False_eq_True]:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True
      apply (rule cdcl_twl_stgy_restart.restart_noGC[of _ U])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>V\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close>
      using twl_res twl_res_T_V TaT STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by auto
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ V]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def not_False_eq_True
      by fast
  qed

  have
    rtranclp_twl_restart_after_restart_S_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close> and
    rtranclp_twl_restart_after_restart_T_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
  proof -
    have TaU: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (U, n))\<close>
      using TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> by auto
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
      using STa m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> TaU m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
  qed
  have
    rtranclp_twl_restart_after_restart_brk:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    if
      [simp]: \<open>brk = True\<close>
  proof -
    have \<open>full cdcl_twl_stgy T U \<or> get_conflict U \<noteq> None\<close>
      using brk'_no_step \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      unfolding rtranclp_unfold full_def final_twl_state_def by auto
    then have \<open>(cdcl_twl_stgy\<^sup>*\<^sup>* T U \<and> pcdcl_twl_final_state U) \<or> get_conflict U \<noteq> None\<close>
      unfolding full_def pcdcl_twl_final_state_def
      by auto
    then consider
        (step) \<open>cdcl_twl_stgy_restart (T, n, True) (U, n, False)\<close> |
        (final) \<open>get_conflict U \<noteq> None\<close>
      using cdcl_twl_stgy_restart.intros(3)[of T U]
      by (auto dest!: cdcl_twl_stgy_restart.intros)
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    proof cases
      case step
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T n True U] apply -
        by fastforce
    next
      case final
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>  unfolding cdcl_twl_stgy_restart_with_leftovers_def
        by fastforce
    qed
  qed
  have cdcl_twl_stgy_restart_with_leftovers1_T_U:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<longleftrightarrow> T \<noteq> U\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<or> T = U\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding rtranclp_unfold by auto
    then show ?thesis
      using wf_not_refl[OF wf_cdcl_twl_stgy_restart, of \<open>(U, n, True)\<close>]
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of \<open>U\<close>]
        struct_invs_U
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def by auto
  qed
  have brk'_eq: \<open>\<not>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<Longrightarrow> brk'\<close>
    using cdcl_o lits_to_upd_U lits_to_update local.cp
    unfolding cdcl_twl_stgy_restart_with_leftovers1_def
    unfolding rtranclp_unfold
    by (auto dest!: tranclp_cdcl_twl_o_stgyD tranclp_cdcl_twl_cp_stgyD
        simp: rtranclp_unfold
        dest: rtranclp_tranclp_tranclp tranclp_trans)

  have [simp]: \<open>brk = False\<close>
    using cond by auto
  show ?A
    unfolding restart_prog_def restart_required_def
    apply (refine_vcg; remove_dummy_vars)
    subgoal using struct_invs_U stgy_invs_U confl_U unfolding restart_prog_pre_def by fast
    subgoal using cdcl_twl_restart_only_twl_struct_invs struct_invs_U by blast
    subgoal using cdcl_twl_stgy_restart_only_twl_stgy_invs stgy_invs_U by blast
    subgoal by simp
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart_only)
    subgoal by (auto simp add: cdcl_twl_restart_only.simps)
    subgoal by (auto simp add: cdcl_twl_restart_only.simps)
    subgoal apply (auto intro!: struct_invs_S struct_invs_T
      cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True])
thm 
  cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True]

      apply (rule 
        cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True])
      sorry
    subgoal by (rule struct_invs')
    subgoal by (rule stgy_invs)
    subgoal by simp
    subgoal
      by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart, simp)
    subgoal
      using rtranclp_twl_restart_after_restart_T_U
      by (auto intro!: struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers1_after_restart[unfolded not_False_eq_True])
    subgoal by (rule struct_invs_U)
    subgoal by (rule stgy_invs_U)
    subgoal by (rule brk'_no_step) simp
    subgoal
      by (auto intro: rtranclp_twl_restart_after_restart_brk
        rtranclp_twl_restart_after_restart_S_U)
    subgoal by (rule clss_to_upd_U)
    subgoal using struct_invs_U conflict_U lits_to_upd_U
      by (cases \<open>get_conflict U\<close>)(auto simp: twl_struct_invs_def)
    subgoal
      using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
      by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V struct_invs_U
        rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
        cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    done
qed

lemma (in twl_restart) cdcl_twl_stgy_restart_prog_spec:
  fixes S :: \<open>'v twl_st\<close>
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog S \<le> SPEC(\<lambda>T.
       \<exists>S' m n. cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m S' (T, n, True) \<and>
        final_twl_state T)\<close>
    (is \<open>_ \<le> SPEC(\<lambda>T. ?P T)\<close>)
proof -
  
  (* have final_prop: \<open>?P T\<close>
   *   if
   *    inv: \<open>case (brk, T, n) of  (brk, T, m, n) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m n\<close> and
   *     \<open>\<not> (case (brk, T, n) of (brk, uu_) \<Rightarrow> \<not> brk)\<close>
   *   for brk T n
   * proof -
   *   have
   *     \<open>brk\<close> and
   *     \<open>twl_struct_invs T\<close> and
   *     \<open>twl_stgy_invs T\<close> and
   *     ns: \<open>final_twl_state T\<close> and
   *     twl_left_overs: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n)\<close> and
   *     \<open>clauses_to_update T = {#}\<close>
   *     using that unfolding cdcl_twl_stgy_restart_prog_inv_def by auto
   *   obtain S' where
   *      st: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (S', n)\<close> and
   *      S'_T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
   *     using twl_left_overs unfolding cdcl_twl_stgy_restart_with_leftovers_def by auto
   *   then show ?thesis
   *     using ns unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
   *     apply (rule_tac x=n in exI)
   *     apply (rule conjI)
   *     subgoal by (rule_tac x=S' in exI) auto
   *     subgoal by auto
   *     done
  * qed *)
  let ?R = \<open>{((brkT :: bool, T :: 'v twl_st, T' :: 'v twl_st, n :: nat, n' :: nat),
      brkS, S, S' :: 'v twl_st, m :: nat, m' :: nat).
    twl_struct_invs S \<and> \<not> brkS \<and>
    cdcl_twl_stgy_restart_with_leftovers1 (S, m, brkS) (T, n, brkT)} \<union>
    {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}\<close>

  have wf: \<open>wf ?R\<close>
    apply (rule wf_union_compatible)
    subgoal
      by (rule wf_if_measure_in_wf[OF wf_cdcl_twl_stgy_restart_with_leftovers1,
          of _  \<open>\<lambda>(brkT, T, T', n, n'). (T, n, brkT)\<close>])
        auto
    subgoal
      by (rule wf_no_loop) auto
    subgoal
      by auto
    done
   term cdcl_twl_stgy_restart

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding cdcl_twl_stgy_restart_prog_def full_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>?R\<close>];
      remove_dummy_vars)
    subgoal by (rule wf)
    subgoal using assms unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
      by auto
    subgoal using assms unfolding cdcl_twl_stgy_restart_prog_inv_def cdcl_twl_stgy_restart_with_leftovers_def
      by (auto dest: rtranclp_cdcl_twl_stgy_restart_twl_struct_invs)
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
      explore_lemma
      sorry

    subgoal by (rule wf_cdcl_twl_stgy_restart_measure)
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_refl)
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal by (rule final_prop[unfolded cdcl_twl_stgy_restart_prog_inv_def])
    done
qed
lemma (in twl_restart)
  assumes
    inv: \<open>case (brk, T, m, n) of  (brk, T, m, n) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m n\<close> and
    cond: \<open>case (brk, T, m, n) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec S' (brk', U)\<close> and
    struct_invs_S: \<open>twl_struct_invs S'\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T S'\<close> and
    lits_to_update: \<open>literals_to_update S' = {#}\<close> and
    \<open>\<forall>S'a. \<not> cdcl_twl_cp S' S'a\<close> and
    \<open>twl_stgy_invs S'\<close> and
    brk: \<open>(brk', brk) \<in> bool_rel\<close>
  shows restart_prog_spec:
    \<open>restart_prog U m n brk'
         \<le> SPEC
             (\<lambda>x. (case x of
                   (T, m, na) \<Rightarrow> RETURN (brk', T, m, na))
                  \<le> SPEC
                      (\<lambda>s'. (case s' of
  (brk, T, m, n'') \<Rightarrow>
    twl_struct_invs T \<and>
    twl_stgy_invs T \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>brk) m S (T, n'', \<not>brk) \<and>
    clauses_to_update T = {#} \<and>
    (\<not> brk \<longrightarrow> get_conflict T = None)) \<and>
 (s', brk, T, n)
 \<in> {((brkT, T, m, n'), brkS, S, _).
     twl_struct_invs S \<and>
     cdcl_twl_stgy_restart_with_leftovers1 (S, n, \<not>brkS) (T, n', \<not>brkS)} \<union>
    {((brkT, T, _, _), brkS, S, _). S = T \<and> brkT \<and> \<not> brkS}))\<close> (is ?A)
proof -
  have brk[simp]: \<open>brk' = brk\<close>
    using brk by auto
  have struct_invs': \<open>cdcl_twl_restart U T \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* T V \<Longrightarrow> twl_struct_invs V\<close> for T V
    using assms(3) cdcl_twl_restart_twl_struct_invs
    by (metis (no_types, lifting) case_prodD rtranclp_cdcl_twl_stgy_twl_struct_invs)
  have stgy_invs: \<open>cdcl_twl_restart U V \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<Longrightarrow> twl_stgy_invs W\<close> for V W
    using assms(3) cdcl_twl_restart_twl_stgy_invs
    by (metis (no_types, lifting) case_prodD cdcl_twl_restart_twl_struct_invs
      rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close> and
    \<open>brk \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (T, n, True)\<close> and
    \<open>clauses_to_update T = {#}\<close> and
    confl: \<open>\<not> brk \<longrightarrow> get_conflict T = None\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case by fast+
  have
    cdcl_o: \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> and
    conflict_U: \<open>get_conflict U \<noteq> None \<Longrightarrow> count_decided (get_trail U) = 0\<close> and
    brk'_no_step: \<open>brk' \<Longrightarrow> final_twl_state U\<close> and
    struct_invs_U: \<open>twl_struct_invs U\<close> and
    stgy_invs_U: \<open>twl_stgy_invs U\<close> and
    clss_to_upd_U: \<open>clauses_to_update U = {#}\<close> and
    lits_to_upd_U: \<open>\<not> brk' \<longrightarrow> literals_to_update U \<noteq> {#}\<close> and
    confl_U: \<open>\<not> brk' \<longrightarrow> get_conflict U = None\<close>
    using other_inv unfolding final_twl_state_def by fast+

  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
    by (meson \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> assms(5) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD
        rtranclp_trans)
  from twl_res obtain Ta where
    STa: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (Ta, n, True)\<close> and
    TaT: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta T\<close> and
    m: \<open>m = size (get_all_learned_clss Ta)\<close>
    unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case snd_conv fst_conv
    by blast
  have
    twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close> and
    rtranclp_twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (W, n + 1, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (size (get_all_learned_clss W))
        (W, n + 1, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
    \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (size (get_all_learned_clss W))
         (W, Suc n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
    if
      f: \<open>True \<longrightarrow> f (snd (U, n)) < size (get_all_learned_clss (fst (U, n))) - m\<close> and
      res: \<open>cdcl_twl_restart U V\<close> and
      pre: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V W
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)

    show twl_res_T_V[unfolded not_False_eq_True]:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
      unfolding not_False_eq_True
      apply (rule cdcl_twl_stgy_restart.restart_step[of _ U _ V])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      subgoal using pre by simp
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False)
        (size (get_all_learned_clss W)) (W, Suc n, \<not>False)\<close>
      unfolding not_False_eq_True cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>W\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (W, n + 1, \<not>False)\<close>
      using twl_res twl_res_T_V STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (auto dest: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart)
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (size (get_all_learned_clss W))
        (W, n + 1, \<not>False)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ W]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (W, Suc n, \<not>False)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def not_False_eq_True
      by fast
  qed
  let ?m = \<open>\<lambda>W. (size (get_all_learned_clss W))\<close>
  have
    twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close> and
    rtranclp_twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_only:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart_only:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
    if
      f: \<open>True \<longrightarrow> m < size (get_all_learned_clss U)\<close> and
      res: \<open>cdcl_twl_restart_only U V\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close> and st2: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)+

    show twl_res_T_V[unfolded not_False_eq_True]:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True
      apply (rule cdcl_twl_stgy_restart.restart_noGC[of _ U])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>V\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close>
      using twl_res twl_res_T_V TaT STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by auto
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ V]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def not_False_eq_True
      by fast
  qed

  have
    rtranclp_twl_restart_after_restart_S_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close> and
    rtranclp_twl_restart_after_restart_T_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
  proof -
    have TaU: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (U, n))\<close>
      using TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> by auto
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
      using STa m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> TaU m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
  qed
  have
    rtranclp_twl_restart_after_restart_brk:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    if
      [simp]: \<open>brk = True\<close>
  proof -
    have \<open>full cdcl_twl_stgy T U \<or> get_conflict U \<noteq> None\<close>
      using brk'_no_step \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      unfolding rtranclp_unfold full_def final_twl_state_def by auto
    then have \<open>(cdcl_twl_stgy\<^sup>*\<^sup>* T U \<and> pcdcl_twl_final_state U) \<or> get_conflict U \<noteq> None\<close>
      unfolding full_def pcdcl_twl_final_state_def
      by auto
    then consider
        (step) \<open>cdcl_twl_stgy_restart (T, n, True) (U, n, False)\<close> |
        (final) \<open>get_conflict U \<noteq> None\<close>
      using cdcl_twl_stgy_restart.intros(3)[of T U]
      by (auto dest!: cdcl_twl_stgy_restart.intros)
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    proof cases
      case step
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T n True U] apply -
        by fastforce
    next
      case final
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>  unfolding cdcl_twl_stgy_restart_with_leftovers_def
        by fastforce
    qed
  qed
  have cdcl_twl_stgy_restart_with_leftovers1_T_U:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<longleftrightarrow> T \<noteq> U\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<or> T = U\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding rtranclp_unfold by auto
    then show ?thesis
      using wf_not_refl[OF wf_cdcl_twl_stgy_restart, of \<open>(U, n, True)\<close>]
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of \<open>U\<close>]
        struct_invs_U
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def by auto
  qed
  have brk'_eq: \<open>\<not>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<Longrightarrow> brk'\<close>
    using cdcl_o lits_to_upd_U lits_to_update local.cp
    unfolding cdcl_twl_stgy_restart_with_leftovers1_def
    unfolding rtranclp_unfold
    by (auto dest!: tranclp_cdcl_twl_o_stgyD tranclp_cdcl_twl_cp_stgyD
        simp: rtranclp_unfold
        dest: rtranclp_tranclp_tranclp tranclp_trans)

  have [simp]: \<open>brk = False\<close>
    using cond by auto
  show ?A
    unfolding restart_prog_def restart_required_def
    apply (refine_vcg; remove_dummy_vars)
    subgoal using struct_invs_U stgy_invs_U confl_U unfolding restart_prog_pre_def by fast
    subgoal using cdcl_twl_restart_only_twl_struct_invs struct_invs_U by blast
    subgoal using cdcl_twl_stgy_restart_only_twl_stgy_invs stgy_invs_U by blast
    subgoal by simp
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart_only)
    subgoal by (auto simp add: cdcl_twl_restart_only.simps)
    subgoal by (auto simp add: cdcl_twl_restart_only.simps)
    subgoal apply (auto intro!: struct_invs_S struct_invs_T
      cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True])
thm 
  cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True]

      apply (rule 
        cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True])
      sorry
    subgoal by (rule struct_invs')
    subgoal by (rule stgy_invs)
    subgoal by simp
    subgoal
      by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart, simp)
    subgoal
      using rtranclp_twl_restart_after_restart_T_U
      by (auto intro!: struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers1_after_restart[unfolded not_False_eq_True])
    subgoal by (rule struct_invs_U)
    subgoal by (rule stgy_invs_U)
    subgoal by (rule brk'_no_step) simp
    subgoal
      by (auto intro: rtranclp_twl_restart_after_restart_brk
        rtranclp_twl_restart_after_restart_S_U)
    subgoal by (rule clss_to_upd_U)
    subgoal using struct_invs_U conflict_U lits_to_upd_U
      by (cases \<open>get_conflict U\<close>)(auto simp: twl_struct_invs_def)
    subgoal
      using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
      by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V struct_invs_U
        rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
        cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    done
qed

lemma (in twl_restart)
  assumes
    inv: \<open>case (ebrk, brk, T, m, n) of  (ebrk, brk, T, m, n) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m n\<close> and
    cond: \<open>case (ebrk, brk, T, m, n) of (ebrk, brk, _) \<Rightarrow> \<not> brk \<and> \<not>ebrk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec S' (brk', U)\<close> and
    struct_invs_S: \<open>twl_struct_invs S'\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T S'\<close> and
    lits_to_update: \<open>literals_to_update S' = {#}\<close> and
    \<open>\<forall>S'a. \<not> cdcl_twl_cp S' S'a\<close> and
    \<open>twl_stgy_invs S'\<close> and
    brk: \<open>(brk', brk) \<in> bool_rel\<close>
  shows restart_prog_early_spec:
   \<open>restart_prog U m n brk'
    \<le> SPEC (\<lambda>x. (case x of (T, m, n) \<Rightarrow> RES UNIV \<bind> (\<lambda>ebrk. RETURN (ebrk, brk', T, m, n)))
            \<le> SPEC
               (\<lambda>s'. (case s' of (ebrk, brk, x, xb, xc) \<Rightarrow>
                        cdcl_twl_stgy_restart_prog_inv S brk x xb xc) \<and>
                     (s', ebrk, brk, T, n)
                     \<in> {((ebrk, brkT, T, m, n'), ebrk, brkS, S, _).
                        twl_struct_invs S \<and>
                        cdcl_twl_stgy_restart_with_leftovers1 (S, n, \<not>brkT) (T, n', \<not>brkS)} \<union>
                       {((ebrkT, brkT, T, m), ebrkS, brkS, S, n).
                           S = T \<and> (ebrkT \<or> brkT) \<and> \<not> brkS \<and> \<not> ebrkS}))\<close>  (is \<open>?B\<close>)
proof -
  have brk[simp]: \<open>brk' = brk\<close>
    using brk by auto
  have struct_invs': \<open>cdcl_twl_restart U T \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* T V \<Longrightarrow> twl_struct_invs V\<close> for T V
    using assms(3) cdcl_twl_restart_twl_struct_invs
    by (metis (no_types, lifting) case_prodD rtranclp_cdcl_twl_stgy_twl_struct_invs)
  have stgy_invs: \<open>cdcl_twl_restart U V \<Longrightarrow> cdcl_twl_stgy\<^sup>*\<^sup>* V W \<Longrightarrow> twl_stgy_invs W\<close> for V W
    using assms(3) cdcl_twl_restart_twl_stgy_invs
    by (metis (no_types, lifting) case_prodD cdcl_twl_restart_twl_struct_invs
      rtranclp_cdcl_twl_stgy_twl_stgy_invs)
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close> and
    \<open>brk \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (T, n, True)\<close> and
    \<open>clauses_to_update T = {#}\<close> and
    confl: \<open>\<not> brk \<longrightarrow> get_conflict T = None\<close>
    using inv unfolding cdcl_twl_stgy_restart_prog_inv_def by fast+

  have
    cdcl_o: \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> and
    conflict_U: \<open>get_conflict U \<noteq> None \<Longrightarrow> count_decided (get_trail U) = 0\<close> and
    brk'_no_step: \<open>brk' \<Longrightarrow> final_twl_state U\<close> and
    struct_invs_U: \<open>twl_struct_invs U\<close> and
    stgy_invs_U: \<open>twl_stgy_invs U\<close> and
    clss_to_upd_U: \<open>clauses_to_update U = {#}\<close> and
    lits_to_upd_U: \<open>\<not> brk' \<longrightarrow> literals_to_update U \<noteq> {#}\<close> and
    confl_U: \<open>\<not> brk' \<longrightarrow> get_conflict U = None\<close>
    using other_inv unfolding final_twl_state_def by fast+

  have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
    by (meson \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> assms(5) rtranclp_cdcl_twl_cp_stgyD rtranclp_cdcl_twl_o_stgyD
        rtranclp_trans)
  from twl_res obtain Ta where
    STa: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (Ta, n, True)\<close> and
    TaT: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta T\<close> and
    m: \<open>m = size (get_all_learned_clss Ta)\<close>
    unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case snd_conv fst_conv
    by blast

  let ?m = \<open>\<lambda>W. (size (get_all_learned_clss W))\<close>
  have
    twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart (Ta, n, True) (W, Suc n, True)\<close> and
    rtranclp_twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (W, n + 1, True)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) (?m W) (W, n + 1, True)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_W:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) (?m W) (W, Suc n, True)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, True) (W, Suc n, True)\<close>
    if
      f: \<open>True \<longrightarrow> f (snd (U, n)) < size (get_all_learned_clss (fst (U, n))) - m\<close> and
      res: \<open>cdcl_twl_restart U V\<close> and
      inp: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* V W\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V W
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close> and st': \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)+

    show twl_res_T_V: \<open>cdcl_twl_stgy_restart (Ta, n, True) (W, Suc n, True)\<close>
      apply (rule cdcl_twl_stgy_restart.restart_step[of _ U _ V])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      subgoal by (rule inp)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) (?m W) (W, Suc n, True)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>W\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, True) (W, n + 1, True)\<close>
      using twl_res twl_res_T_V STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (auto dest: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart)
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) (?m W) (W, n + 1, True)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ W]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, True) (W, Suc n, True)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def
      by fast
  qed
  have
    twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close> and
    rtranclp_twl_restart_after_restart_only:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_only:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart_only:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
    if
      f: \<open>True \<longrightarrow> m < size (get_all_learned_clss U)\<close> and
      res: \<open>cdcl_twl_restart_only U V\<close> and
      [unfolded brk, simp]: \<open>brk' = False\<close>
    for V
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ Ta U\<close> and st2: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      using TaT
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)+

    show twl_res_T_V[unfolded not_False_eq_True]:
      \<open>cdcl_twl_stgy_restart (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True
      apply (rule cdcl_twl_stgy_restart.restart_noGC[of _ U])
      subgoal by (rule st)
      subgoal using f unfolding m by simp
      subgoal by (rule res)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding not_False_eq_True cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>V\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0, \<not>False) (V, n, \<not>False)\<close>
      using twl_res twl_res_T_V TaT STa
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by auto
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, \<not>False) (?m V) (V, n, \<not>False)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ V]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (Ta, n, \<not>False) (V, n, \<not>False)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def not_False_eq_True
      by fast
  qed
  have
    rtranclp_twl_restart_after_restart_S_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close> and
    rtranclp_twl_restart_after_restart_T_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
  proof -
    have TaU: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (U, n))\<close>
      using TaT \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> by auto
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
      using STa m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
    show \<open>cdcl_twl_stgy_restart_with_leftovers (Ta, n, True) m (U, n, True)\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> TaU m unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
  qed
  have
    rtranclp_twl_restart_after_restart_brk:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    if
      [simp]: \<open>brk = True\<close>
  proof -
    have \<open>full cdcl_twl_stgy T U \<or> get_conflict U \<noteq> None\<close>
      using brk'_no_step \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      unfolding rtranclp_unfold full_def final_twl_state_def by auto
    then have \<open>(cdcl_twl_stgy\<^sup>*\<^sup>* T U \<and> pcdcl_twl_final_state U) \<or> get_conflict U \<noteq> None\<close>
      unfolding full_def pcdcl_twl_final_state_def
      by auto
    then consider
        (step) \<open>cdcl_twl_stgy_restart (T, n, True) (U, n, False)\<close> |
        (final) \<open>get_conflict U \<noteq> None\<close>
      using cdcl_twl_stgy_restart.intros(3)[of T U]
      by (auto dest!: cdcl_twl_stgy_restart.intros)
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (U, n, True)\<close>
    proof cases
      case step
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T n True U] apply -
        by fastforce
    next
      case final
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>  unfolding cdcl_twl_stgy_restart_with_leftovers_def
        by fastforce
    qed
  qed
  have cdcl_twl_stgy_restart_with_leftovers1_T_U:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<longleftrightarrow> T \<noteq> U\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<or> T = U\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding rtranclp_unfold by auto
    then show ?thesis
      using wf_not_refl[OF wf_cdcl_twl_stgy_restart, of \<open>(U, n, True)\<close>]
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of \<open>U\<close>]
        struct_invs_U
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def by auto
  qed
  have brk'_eq: \<open>\<not>cdcl_twl_stgy_restart_with_leftovers1 (T, n, True) (U, n, True) \<Longrightarrow> brk'\<close>
    using cdcl_o lits_to_upd_U lits_to_update local.cp
    unfolding cdcl_twl_stgy_restart_with_leftovers1_def
    unfolding rtranclp_unfold
    by (auto dest!: tranclp_cdcl_twl_o_stgyD tranclp_cdcl_twl_cp_stgyD
        simp: rtranclp_unfold
        dest: rtranclp_tranclp_tranclp tranclp_trans)

  have H[simp]: \<open>brk = False\<close>
    using cond by auto
  show ?B
    unfolding restart_prog_def restart_required_def
    apply (refine_vcg; remove_dummy_vars)
    subgoal using struct_invs_U stgy_invs_U confl_U unfolding restart_prog_pre_def by fast
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      apply (intro conjI)
      subgoal using cdcl_twl_restart_only_twl_struct_invs struct_invs_U by blast
      subgoal using cdcl_twl_stgy_restart_only_twl_stgy_invs stgy_invs_U by blast
      subgoal by simp
      subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart_only[unfolded not_False_eq_True]) simp_all
      subgoal by (auto simp: cdcl_twl_restart_only.simps)
      subgoal by (auto simp: cdcl_twl_restart_only.simps)
      done
    subgoal
      using rtranclp_twl_restart_after_restart_T_U
      by (auto intro!: struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers1_after_restart_only[unfolded not_False_eq_True])
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      apply (intro conjI)
      subgoal by (rule struct_invs')
      subgoal by (rule stgy_invs)
      subgoal unfolding H by fast
      subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart) simp_all
      subgoal by simp
      subgoal by (simp add: res_no_confl)
      done
    subgoal
      using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
      by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
        cdcl_twl_stgy_restart_with_leftovers_after_restart_T_W struct_invs_U
        rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
        cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    subgoal
      using inv
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (simp add: struct_invs_U stgy_invs_U clss_to_upd_U lits_to_upd_U
        confl_U rtranclp_twl_restart_after_restart_S_U)
    subgoal
      using inv cdcl_twl_stgy_restart_with_leftovers1_T_U H brk brk'_eq
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      apply (simp add: struct_invs_U stgy_invs_U clss_to_upd_U lits_to_upd_U
        confl_U rtranclp_twl_restart_after_restart_S_U)
      by auto
    done
qed

lemma cdcl_twl_stgy_restart_with_leftovers_refl:
  \<open>cdcl_twl_stgy_restart_with_leftovers (S, a) (size (get_all_learned_clss S)) (S, a)\<close>
  unfolding cdcl_twl_stgy_restart_with_leftovers_def
  by (rule exI[of _ \<open>S\<close>]) auto

(* declare restart_prog_spec[THEN order_trans, refine_vcg] 
lemma (in twl_restart) cdcl_twl_stgy_restart_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog S \<le> SPEC(\<lambda>T.
       \<exists>m n. cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (T, n, True) \<and>
        final_twl_state T)\<close>
    (is \<open>_ \<le> SPEC(\<lambda>T. ?P T)\<close>)
proof -
  have final_prop: \<open>?P T\<close>
    if
     inv: \<open>case (brk, T, n) of  (brk, T, m, n) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m n\<close> and
      \<open>\<not> (case (brk, T, n) of (brk, uu_) \<Rightarrow> \<not> brk)\<close>
    for brk T n
  proof -
    have
      \<open>brk\<close> and
      \<open>twl_struct_invs T\<close> and
      \<open>twl_stgy_invs T\<close> and
      ns: \<open>final_twl_state T\<close> and
      twl_left_overs: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n)\<close> and
      \<open>clauses_to_update T = {#}\<close>
      using that unfolding cdcl_twl_stgy_restart_prog_inv_def by auto
    obtain S' where
       st: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (S', n)\<close> and
       S'_T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
      using twl_left_overs unfolding cdcl_twl_stgy_restart_with_leftovers_def by auto
    then show ?thesis
      using ns unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      apply (rule_tac x=n in exI)
      apply (rule conjI)
      subgoal by (rule_tac x=S' in exI) auto
      subgoal by auto
      done
  qed
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding cdcl_twl_stgy_restart_prog_def full_def cdcl_twl_stgy_restart_prog_inv_def
    apply (refine_vcg WHILEIT_rule[where
           R = \<open>{((brkT, T, n), (brkS, S, m)).
                     twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
                {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS}\<close>];
        remove_dummy_vars)
    subgoal by (rule wf_cdcl_twl_stgy_restart_measure)
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_refl)
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal by (rule restart_prog_spec[unfolded cdcl_twl_stgy_restart_prog_inv_def])
    subgoal by (rule final_prop[unfolded cdcl_twl_stgy_restart_prog_inv_def])
    done
qed
definition cdcl_twl_stgy_restart_prog_early :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_restart_prog_early S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, m, n). cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T m n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, n) \<leftarrow> restart_prog T n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, n)
      })
      (ebrk, False, S\<^sub>0, 0);
    if \<not>brk then do {
      (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T n\<^esup>
	(\<lambda>(brk, _). \<not>brk)
	(\<lambda>(brk, S, n).
	do {
	  T \<leftarrow> unit_propagation_outer_loop S;
	  (brk, T) \<leftarrow> cdcl_twl_o_prog T;
	  (T, n) \<leftarrow> restart_prog T n brk;
	  RETURN (brk, T, n)
	})
	(False, T, n);
      RETURN T
    }
    else RETURN T
  }\<close>

lemma (in twl_restart) cdcl_twl_stgy_prog_early_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_early S \<le> SPEC(\<lambda>T. \<exists>n. cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n) \<and>
        final_twl_state T)\<close>
    (is \<open>_ \<le> SPEC(\<lambda>T. ?P T)\<close>)
proof -
  have final_prop: \<open>?P T\<close>
    if
     inv: \<open>case (brk, T, n) of  (brk, T, m) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m\<close> and
      \<open>\<not> (case (brk, T, n) of (brk, uu_) \<Rightarrow> \<not> brk)\<close>
    for brk T n
  proof -
    have
      \<open>brk\<close> and
      \<open>twl_struct_invs T\<close> and
      \<open>twl_stgy_invs T\<close> and
      ns: \<open>final_twl_state T\<close> and
      twl_left_overs: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n)\<close> and
      \<open>clauses_to_update T = {#}\<close>
      using that unfolding cdcl_twl_stgy_restart_prog_inv_def by auto
    obtain S' where
       st: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (S', n)\<close> and
       S'_T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
      using twl_left_overs unfolding cdcl_twl_stgy_restart_with_leftovers_def by auto
    then show ?thesis
      using ns unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      apply (rule_tac x=n in exI)
      apply (rule conjI)
      subgoal by (rule_tac x=S' in exI) auto
      subgoal by auto
      done
  qed
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding cdcl_twl_stgy_restart_prog_early_def full_def
    apply (refine_vcg
        WHILEIT_rule[where
           R = \<open>{((ebrk, brkT, T, n), (ebrk, brkS, S, m)).
                     twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
                {((ebrkT, brkT, T), (ebrkS, brkS, S)). S = T \<and> (ebrkT \<or> brkT) \<and> (\<not>brkS \<and> \<not>ebrkS)}\<close>]
       WHILEIT_rule[where
           R = \<open>{((brkT, T, n), (brkS, S, m)).
                     twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
                {((brkT, T), (brkS, S)). S = T \<and> brkT \<and> \<not>brkS}\<close>];
        remove_dummy_vars)
    subgoal by (rule wf_cdcl_twl_stgy_restart_measure_early)
    subgoal using assms unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (fast intro: cdcl_twl_stgy_restart_with_leftovers_refl)
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal for ebrk brk T m x ac bc
      by (rule restart_prog_early_spec)
    subgoal by (rule wf_cdcl_twl_stgy_restart_measure)
    subgoal by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (rule restart_prog_spec[unfolded cdcl_twl_stgy_restart_prog_inv_def])
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (rule final_prop[unfolded cdcl_twl_stgy_restart_prog_inv_def])
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by auto
    done
qed

*)
definition cdcl_twl_stgy_restart_prog_bounded :: "'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres" where
  \<open>cdcl_twl_stgy_restart_prog_bounded S\<^sub>0 =
  do {
    ebrk \<leftarrow> RES UNIV;
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, m, n). cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T m n\<^esup>
      (\<lambda>(ebrk, brk, _). \<not>brk \<and> \<not>ebrk)
      (\<lambda>(ebrk, brk, S, m, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, m, n) \<leftarrow> restart_prog T m n brk;
	ebrk \<leftarrow> RES UNIV;
        RETURN (ebrk, brk, T, m, n)
      })
      (ebrk, False, S\<^sub>0, size (get_all_learned_clss S\<^sub>0), 0);
    RETURN (brk, T)
  }\<close>

lemma (in twl_restart) cdcl_twl_stgy_prog_bounded_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog_bounded S \<le> SPEC(\<lambda>(brk, T). \<exists>m n. cdcl_twl_stgy_restart_with_leftovers (S, 0, True) m (T, n) \<and>
        (brk \<longrightarrow> final_twl_state T))\<close>
    (is \<open>_ \<le> SPEC ?P\<close>)
proof -
(*
  have final_prop: \<open>?P (brk, T)\<close>
    if
     inv: \<open>case (brk, T, n) of  (brk, T, m) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m\<close>
    for brk T n
  proof -
    have
      \<open>twl_struct_invs T\<close> and
      \<open>twl_stgy_invs T\<close> and
      ns: \<open>brk \<longrightarrow> final_twl_state T\<close> and
      twl_left_overs: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n)\<close> and
      \<open>clauses_to_update T = {#}\<close>
      using that unfolding cdcl_twl_stgy_restart_prog_inv_def by auto
    obtain S' where
       st: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (S', n)\<close> and
       S'_T: \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S' T\<close>
      using twl_left_overs unfolding cdcl_twl_stgy_restart_with_leftovers_def by auto
    then show ?thesis
      using ns unfolding cdcl_twl_stgy_restart_with_leftovers_def prod.case apply -
      apply (rule_tac x=n in exI)
      apply (rule conjI)
      subgoal by (rule_tac x=S' in exI) auto
      subgoal by auto
      done
  qed*)
thm cdcl_twl_stgy_restart_prog_inv_def
thm wf_cdcl_twl_stgy_restart_measure_early
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding cdcl_twl_stgy_restart_prog_bounded_def full_def
    apply (refine_vcg
        WHILEIT_rule[where
           R = \<open>{((ebrk, brkT, T, n, n'), (ebrk, brkS, S, m, m')).
                  twl_struct_invs S \<and> cdcl_twl_stgy_restart_with_leftovers1 (S, m, brkS)
                  (T, n, brkT)} \<union>
                {((ebrkT, brkT, T), (ebrkS, brkS, S)). S = T \<and> (ebrkT \<or> brkT) \<and> (\<not>brkS \<and> \<not>ebrkS)}\<close>];
        remove_dummy_vars)
    subgoal
      by (rule wf_cdcl_twl_stgy_restart_measure_early)
    subgoal using assms unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (auto intro: cdcl_twl_stgy_restart_with_leftovers_refl)
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def by fast
    subgoal unfolding cdcl_twl_stgy_restart_prog_inv_def
      by (simp add: no_step_cdcl_twl_cp_no_step_cdcl\<^sub>W_cp)
    subgoal by fast
    subgoal for ebrk brk T m x ac bc ad bd
      by (rule restart_prog_early_spec)
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def prod.case
      by (rule final_prop[unfolded prod.case cdcl_twl_stgy_restart_prog_inv_def])
    done
qed
end

end
