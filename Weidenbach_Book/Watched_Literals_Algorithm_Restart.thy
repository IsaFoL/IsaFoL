theory Watched_Literals_Algorithm_Restart
  imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Restart
begin

context twl_restart_ops
begin

text \<open>Restarts are never necessary\<close>
definition restart_required :: "'v twl_st \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required S n = SPEC (\<lambda>b. b \<longrightarrow> size (get_learned_clss S) > f n)\<close>

definition (in -) restart_prog_pre :: \<open>'v twl_st \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_prog_pre S brk \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S \<and>
    (\<not>brk \<longrightarrow> get_conflict S = None)\<close>

definition restart_prog
  :: "'v twl_st \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> ('v twl_st \<times> nat) nres"
where
  \<open>restart_prog S n brk = do {
     ASSERT(restart_prog_pre S brk);
     b \<leftarrow> restart_required S n;
     b2 \<leftarrow> SPEC(\<lambda>_. True);
     if b2 \<and> b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
       RETURN (T, n + 1)
     }
     else
     if b \<and> \<not>brk then do {
       T \<leftarrow> SPEC(\<lambda>T. cdcl_twl_restart S T);
       RETURN (T, n + 1)
     }
     else
       RETURN (S, n)
   }\<close>

definition cdcl_twl_stgy_restart_prog_inv where
  \<open>cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T n \<equiv> twl_struct_invs T \<and> twl_stgy_invs T \<and>
      (brk \<longrightarrow> final_twl_state T) \<and> cdcl_twl_stgy_restart_with_leftovers (S\<^sub>0, 0) (T, n) \<and>
         clauses_to_update T = {#} \<and> (\<not>brk \<longrightarrow> get_conflict T = None)\<close>

definition cdcl_twl_stgy_restart_prog :: "'v twl_st \<Rightarrow> 'v twl_st nres" where
  \<open>cdcl_twl_stgy_restart_prog S\<^sub>0 =
  do {
    (brk, T, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T, n). cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T n\<^esup>
      (\<lambda>(brk, _). \<not>brk)
      (\<lambda>(brk, S, n).
      do {
        T \<leftarrow> unit_propagation_outer_loop S;
        (brk, T) \<leftarrow> cdcl_twl_o_prog T;
        (T, n) \<leftarrow> restart_prog T n brk;
        RETURN (brk, T, n)
      })
      (False, S\<^sub>0, 0);
    RETURN T
  }\<close>

lemma (in twl_restart)
  assumes
    inv: \<open>case (brk, T, m) of  (brk, T, m) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m\<close> and
    cond: \<open>case (brk, T, m) of (brk, uu_) \<Rightarrow> \<not> brk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec S' (brk', U)\<close> and
    struct_invs_S: \<open>twl_struct_invs S'\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T S'\<close> and
    lits_to_update: \<open>literals_to_update S' = {#}\<close> and
    \<open>\<forall>S'a. \<not> cdcl_twl_cp S' S'a\<close> and
    \<open>twl_stgy_invs S'\<close>
  shows restart_prog_spec:
    \<open>restart_prog U m brk'
         \<le> SPEC
             (\<lambda>x. (case x of
                   (T, na) \<Rightarrow> RETURN (brk', T, na))
                  \<le> SPEC
                      (\<lambda>s'. (case s' of
  (brk, T, n) \<Rightarrow>
    twl_struct_invs T \<and>
    twl_stgy_invs T \<and>
    (brk \<longrightarrow> final_twl_state T) \<and>
    cdcl_twl_stgy_restart_with_leftovers (S, 0)
     (T, n) \<and>
    clauses_to_update T = {#} \<and>
    (\<not> brk \<longrightarrow> get_conflict T = None)) \<and>
 (s', brk, T, m)
 \<in> {((brkT, T, n), brkS, S, m).
     twl_struct_invs S \<and>
     cdcl_twl_stgy_restart_with_leftovers1 (S, m)
      (T, n)} \<union>
    {((brkT, T), brkS, S). S = T \<and> brkT \<and> \<not> brkS}))\<close> (is ?A)
proof -
  have struct_invs': \<open>cdcl_twl_restart U T \<Longrightarrow> twl_struct_invs T\<close> for T
    using assms(3) cdcl_twl_restart_twl_struct_invs by blast
  have stgy_invs: \<open>cdcl_twl_restart U V \<Longrightarrow>twl_stgy_invs V\<close> for V
    using assms(3) cdcl_twl_restart_twl_stgy_invs by blast
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close> and
    \<open>brk \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, m)\<close> and
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
  have
    twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart (T, m) (V, Suc m)\<close> and
    rtranclp_twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (V, m + 1)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (V, m + 1)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
      \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (V, Suc m)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (V, Suc m)\<close>
    if
      f: \<open>True \<longrightarrow> f (snd (U, m)) < size (get_learned_clss (fst (U, m)))\<close> and
      res: \<open>cdcl_twl_restart U V\<close> and
      [simp]: \<open>brk' = False\<close>
    for V
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)

    show twl_res_T_V: \<open>cdcl_twl_stgy_restart (T, m) (V, Suc m)\<close>
      apply (rule cdcl_twl_stgy_restart.restart_step[of _ U])
      subgoal by (rule st)
      subgoal using f by simp
      subgoal by (rule res)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (V, Suc m)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>V\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (V, m + 1)\<close>
      using twl_res twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by (auto dest: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart)
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (V, m + 1)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ V]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (V, Suc m)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def
      by fast
  qed
  have
    rtranclp_twl_restart_after_restart_S_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close> and
    rtranclp_twl_restart_after_restart_T_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (U, m)\<close>
  proof -
    obtain Ta where
      S_Ta: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (Ta, snd (T, m))\<close>
      \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (T, m))\<close>
      using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by auto
    then have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (U, m))\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> by auto
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
      using S_Ta unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
    show \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (U, m)\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
  qed
  have
    rtranclp_twl_restart_after_restart_brk:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
    if
      [simp]: \<open>brk' = True\<close>
  proof -
    have \<open>full1 cdcl_twl_stgy T U \<or> T = U \<or> get_conflict U \<noteq> None\<close>
      using brk'_no_step \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      unfolding rtranclp_unfold full1_def final_twl_state_def by auto
    then consider
        (step) \<open>cdcl_twl_stgy_restart (T, m) (U, m)\<close> |
        (TU) \<open>T = U\<close> |
        (final) \<open>get_conflict U \<noteq> None\<close>
      by (auto dest!: cdcl_twl_stgy_restart.intros)
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
    proof cases
      case step
      then show ?thesis
        using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by (rule exI[of _ U]) (fastforce dest!: )
    next
      case [simp]: TU
      then show ?thesis
        using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by fastforce
    next
      case final
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>  unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by fastforce
    qed
  qed
  have cdcl_twl_stgy_restart_with_leftovers1_T_U:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (U, m) \<longleftrightarrow> T \<noteq> U\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<or> T = U\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding rtranclp_unfold by auto
    then show ?thesis
      using wf_not_refl[OF wf_cdcl_twl_stgy_restart, of \<open>(U, m)\<close>]
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of \<open>U\<close>]
        struct_invs_U
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def by auto
  qed
  have brk'_eq: \<open>\<not>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (U, m) \<Longrightarrow> brk'\<close>
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
    subgoal by (rule struct_invs')
    subgoal by (rule stgy_invs)
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart) simp
    subgoal by (rule res_no_clss_to_upd)
    subgoal by (rule res_no_confl)
    subgoal by (auto intro!: struct_invs_S struct_invs_T
          cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    subgoal using struct_invs' by blast
    subgoal using stgy_invs by blast
    subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart) simp
    subgoal by (rule res_no_clss_to_upd)
    subgoal by (rule res_no_confl)
    subgoal by (auto intro!: struct_invs_S struct_invs_T
          cdcl_twl_stgy_restart_with_leftovers1_after_restart)
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
    inv: \<open>case (ebrk, brk, T, m) of  (ebrk, brk, T, m) \<Rightarrow> cdcl_twl_stgy_restart_prog_inv S brk T m\<close> and
    cond: \<open>case (ebrk, brk, T, m) of (ebrk, brk, _) \<Rightarrow> \<not> brk \<and> \<not>ebrk\<close> and
    other_inv: \<open>cdcl_twl_o_prog_spec S' (brk', U)\<close> and
    struct_invs_S: \<open>twl_struct_invs S'\<close> and
    cp: \<open>cdcl_twl_cp\<^sup>*\<^sup>* T S'\<close> and
    lits_to_update: \<open>literals_to_update S' = {#}\<close> and
    \<open>\<forall>S'a. \<not> cdcl_twl_cp S' S'a\<close> and
    \<open>twl_stgy_invs S'\<close>
  shows restart_prog_early_spec:
   \<open>restart_prog U m brk'
    \<le> SPEC
       (\<lambda>x. (case x of (T, n) \<Rightarrow> RES UNIV \<bind> (\<lambda>ebrk. RETURN (ebrk, brk', T, n)))
            \<le> SPEC
               (\<lambda>s'. (case s' of (ebrk, brk, x, xb) \<Rightarrow>
                        cdcl_twl_stgy_restart_prog_inv S brk x xb) \<and>
                     (s', ebrk, brk, T, m)
                     \<in> {((ebrk, brkT, T, n), ebrk, brkS, S, m).
                        twl_struct_invs S \<and>
                        cdcl_twl_stgy_restart_with_leftovers1 (S, m) (T, n)} \<union>
                       {((ebrkT, brkT, T), ebrkS, brkS, S).
                           S = T \<and> (ebrkT \<or> brkT) \<and> \<not> brkS \<and> \<not> ebrkS}))\<close>  (is \<open>?B\<close>)
proof -
  have struct_invs': \<open>cdcl_twl_restart U T \<Longrightarrow> twl_struct_invs T\<close> for T
    using assms(3) cdcl_twl_restart_twl_struct_invs by blast
  have stgy_invs: \<open>cdcl_twl_restart U V \<Longrightarrow>twl_stgy_invs V\<close> for V
    using assms(3) cdcl_twl_restart_twl_stgy_invs by blast
  have res_no_clss_to_upd: \<open>cdcl_twl_restart U V \<Longrightarrow> clauses_to_update V = {#}\<close> for V
    by (auto simp: cdcl_twl_restart.simps)
  have res_no_confl: \<open>cdcl_twl_restart U V \<Longrightarrow> get_conflict V = None\<close> for V
    by (auto simp: cdcl_twl_restart.simps)

  have
    struct_invs_T: \<open>twl_struct_invs T\<close> and
    \<open>twl_stgy_invs T\<close> and
    \<open>brk \<longrightarrow> final_twl_state T\<close> and
    twl_res: \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, m)\<close> and
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
  have
    twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart (T, m) (V, Suc m)\<close> and
    rtranclp_twl_restart_after_restart:
      \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (V, m + 1)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (V, m + 1)\<close> and
    cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V:
      \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (V, Suc m)\<close> and
    cdcl_twl_stgy_restart_with_leftovers1_after_restart:
      \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (V, Suc m)\<close>
    if
      f: \<open>True \<longrightarrow> f (snd (U, m)) < size (get_learned_clss (fst (U, m)))\<close> and
      res: \<open>cdcl_twl_restart U V\<close> and
      [simp]: \<open>brk' = False\<close>
    for V
  proof -
    have \<open>S' \<noteq> U\<close>
      using lits_to_update lits_to_upd_U by auto
    then have \<open>cdcl_twl_o\<^sup>+\<^sup>+ S' U\<close>
      using \<open>cdcl_twl_o\<^sup>*\<^sup>* S' U\<close> unfolding rtranclp_unfold by auto
    then have st: \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U\<close>
      by (meson local.cp rtranclp_cdcl_twl_cp_stgyD rtranclp_tranclp_tranclp
          tranclp_cdcl_twl_o_stgyD)

    show twl_res_T_V: \<open>cdcl_twl_stgy_restart (T, m) (V, Suc m)\<close>
      apply (rule cdcl_twl_stgy_restart.restart_step[of _ U])
      subgoal by (rule st)
      subgoal using f by simp
      subgoal by (rule res)
      done
    show \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (V, Suc m)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by (rule exI[of _ \<open>V\<close>])(auto simp: twl_res_T_V)
    show \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (V, m + 1)\<close>
      using twl_res twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by (auto dest: cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart)
    then show  \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (V, m + 1)\<close>
      unfolding cdcl_twl_stgy_restart_with_leftovers_def apply -
      by (rule exI[of _ V]) auto
    show \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (V, Suc m)\<close>
      using twl_res_T_V
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def
      by fast
  qed
  have
    rtranclp_twl_restart_after_restart_S_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close> and
    rtranclp_twl_restart_after_restart_T_U:
      \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (U, m)\<close>
  proof -
    obtain Ta where
      S_Ta: \<open>cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, 0) (Ta, snd (T, m))\<close>
      \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (T, m))\<close>
      using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by auto
    then have \<open>cdcl_twl_stgy\<^sup>*\<^sup>* Ta (fst (U, m))\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> by auto
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
      using S_Ta unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
    show \<open>cdcl_twl_stgy_restart_with_leftovers (T, m) (U, m)\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding cdcl_twl_stgy_restart_with_leftovers_def
      by fastforce
  qed
  have
    rtranclp_twl_restart_after_restart_brk:
      \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
    if
      [simp]: \<open>brk' = True\<close>
  proof -
    have \<open>full1 cdcl_twl_stgy T U \<or> T = U \<or> get_conflict U \<noteq> None\<close>
      using brk'_no_step \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>
      unfolding rtranclp_unfold full1_def final_twl_state_def by auto
    then consider
        (step) \<open>cdcl_twl_stgy_restart (T, m) (U, m)\<close> |
        (TU) \<open>T = U\<close> |
        (final) \<open>get_conflict U \<noteq> None\<close>
      by (auto dest!: cdcl_twl_stgy_restart.intros)
    then show \<open>cdcl_twl_stgy_restart_with_leftovers (S, 0) (U, m)\<close>
    proof cases
      case step
      then show ?thesis
        using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by (rule exI[of _ U]) (fastforce dest!: )
    next
      case [simp]: TU
      then show ?thesis
        using twl_res unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by fastforce
    next
      case final
      then show ?thesis
        using twl_res \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close>  unfolding cdcl_twl_stgy_restart_with_leftovers_def
        using cdcl_twl_stgy_restart_cdcl_twl_stgy_cdcl_twl_stgy_restart2[of T m U] apply -
        by fastforce
    qed
  qed
  have cdcl_twl_stgy_restart_with_leftovers1_T_U:
    \<open>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (U, m) \<longleftrightarrow> T \<noteq> U\<close>
  proof -
    have \<open>cdcl_twl_stgy\<^sup>+\<^sup>+ T U \<or> T = U\<close>
      using \<open>cdcl_twl_stgy\<^sup>*\<^sup>* T U\<close> unfolding rtranclp_unfold by auto
    then show ?thesis
      using wf_not_refl[OF wf_cdcl_twl_stgy_restart, of \<open>(U, m)\<close>]
      using wf_not_refl[OF tranclp_wf_cdcl_twl_stgy, of \<open>U\<close>]
        struct_invs_U
      unfolding cdcl_twl_stgy_restart_with_leftovers1_def by auto
  qed
  have brk'_eq: \<open>\<not>cdcl_twl_stgy_restart_with_leftovers1 (T, m) (U, m) \<Longrightarrow> brk'\<close>
    using cdcl_o lits_to_upd_U lits_to_update local.cp
    unfolding cdcl_twl_stgy_restart_with_leftovers1_def
    unfolding rtranclp_unfold
    by (auto dest!: tranclp_cdcl_twl_o_stgyD tranclp_cdcl_twl_cp_stgyD
        simp: rtranclp_unfold
        dest: rtranclp_tranclp_tranclp tranclp_trans)

  have H[simp]: \<open>brk = False\<close> \<open>ebrk = False\<close>
    using cond by auto
  show ?B
    unfolding restart_prog_def restart_required_def
    apply (refine_vcg; remove_dummy_vars)
    subgoal using struct_invs_U stgy_invs_U confl_U
      unfolding restart_prog_pre_def cdcl_twl_stgy_restart_prog_inv_def H by fast
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      apply (intro conjI)
      subgoal by (rule struct_invs')
      subgoal by (rule stgy_invs)
      subgoal unfolding H by fast
      subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart) simp_all
      subgoal by (rule res_no_clss_to_upd)
      subgoal by (simp add: res_no_confl)
    done
    subgoal
     using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq struct_invs_T
     by (simp add: clss_to_upd_U confl_U rtranclp_twl_restart_after_restart_S_U
        stgy_invs_U struct_invs_U twl_restart_ops.cdcl_twl_stgy_restart_prog_inv_def
	cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    subgoal
      unfolding cdcl_twl_stgy_restart_prog_inv_def
      apply (intro conjI)
      subgoal by (rule struct_invs')
      subgoal by (rule stgy_invs)
      subgoal unfolding H by fast
      subgoal by (rule cdcl_twl_stgy_restart_with_leftovers_after_restart) simp_all
      subgoal by (rule res_no_clss_to_upd)
      subgoal by (simp add: res_no_confl)
    done
    subgoal
     using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
     by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
	cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V struct_invs_U
	rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
	cdcl_twl_stgy_restart_with_leftovers1_after_restart
	brk'_no_step clss_to_upd_U restart_prog_pre_def rtranclp_twl_restart_after_restart_S_U
	twl_restart_ops.cdcl_twl_stgy_restart_prog_inv_def)
    subgoal
     using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
     by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
	cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V struct_invs_U
	rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
	cdcl_twl_stgy_restart_with_leftovers1_after_restart
	brk'_no_step clss_to_upd_U restart_prog_pre_def rtranclp_twl_restart_after_restart_S_U
	twl_restart_ops.cdcl_twl_stgy_restart_prog_inv_def)
    subgoal
     using cdcl_twl_stgy_restart_with_leftovers1_T_U brk'_eq
     by (auto simp: twl_restart_after_restart struct_invs_S struct_invs_T
	cdcl_twl_stgy_restart_with_leftovers_after_restart_T_V struct_invs_U
	rtranclp_twl_restart_after_restart_brk rtranclp_twl_restart_after_restart_T_U
	cdcl_twl_stgy_restart_with_leftovers1_after_restart)
    done
qed

lemma cdcl_twl_stgy_restart_with_leftovers_refl: \<open>cdcl_twl_stgy_restart_with_leftovers S S\<close>
  unfolding cdcl_twl_stgy_restart_with_leftovers_def
  by (rule exI[of _ \<open>fst S\<close>]) auto

(* declare restart_prog_spec[THEN order_trans, refine_vcg] *)
lemma (in twl_restart) cdcl_twl_stgy_restart_prog_spec:
  assumes \<open>twl_struct_invs S\<close> and \<open>twl_stgy_invs S\<close> and \<open>clauses_to_update S = {#}\<close> and
    \<open>get_conflict S = None\<close>
  shows
    \<open>cdcl_twl_stgy_restart_prog S \<le> SPEC(\<lambda>T. \<exists>n. cdcl_twl_stgy_restart_with_leftovers (S, 0) (T, n) \<and>
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
    (ebrk, brk, T, n) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(ebrk, brk, T, n). cdcl_twl_stgy_restart_prog_inv S\<^sub>0 brk T n\<^esup>
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

end

end
