(* Title:        Fair Zipperposition Loop without Ghosts
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
                 Andrei Popescu <a.popescu at sheffield.ac.uk>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Fair Zipperposition Loop without Ghosts\<close>

text \<open>This version of the fair Zipperposition loop eliminates the ghost state
component @{text D}, thus confirming that @{text D} is indeed a ghost.\<close>

theory Fair_Zipperposition_Loop_without_Ghosts
  imports Fair_Zipperposition_Loop
begin

subsection \<open>Locale\<close>

type_synonym ('t, 'p, 'f) ZLf_wo_ghosts_state = "'t \<times> 'p \<times> 'f option \<times> 'f fset"

locale fair_zipperposition_loop_wo_ghosts =
  w_ghosts?: fair_zipperposition_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q
    \<G>_I_q Equiv_F Prec_F t_empty t_add_llist t_remove_llist t_pick_elem t_llists p_empty p_select
    p_add p_remove p_felems Prec_S
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Inf_G_q :: "'q \<Rightarrow> 'g inference set" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) and
    t_empty :: 't and
    t_add_llist :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_remove_llist :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_pick_elem :: "'t \<Rightarrow> 'f inference \<times> 't" and
    t_llists :: "'t \<Rightarrow> 'f inference llist multiset" and
    p_empty :: 'p and
    p_select :: "'p \<Rightarrow> 'f" and
    p_add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_felems :: "'p \<Rightarrow> 'f fset" and
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
begin

fun wo_ghosts_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> ('t, 'p, 'f) ZLf_wo_ghosts_state" where
  "wo_ghosts_of (T, D, P, Y, A) = (T, P, Y, A)"

inductive
  fair_ZL_wo_ghosts ::
  "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> ('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> bool"
  (infix "\<leadsto>ZLfw" 50)
  where
  compute_infer: "(\<exists>\<iota>s \<in># t_llists T. \<iota>s \<noteq> LNil) \<Longrightarrow> t_pick_elem T = (\<iota>0, T') \<Longrightarrow>
    \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (T, P, None, A) \<leadsto>ZLfw (T', p_add C P, None, A)"
| choose_p: "P \<noteq> p_empty \<Longrightarrow>
    (T, P, None, A) \<leadsto>ZLfw (T, p_remove (p_select P) P, Some (p_select P), A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLfw (T, P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLfw (T, P, Some C', A)"
| delete_bwd: "C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (T, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLfw (T, P, Some C, A)"
| simplify_bwd: "C' |\<notin>| A \<Longrightarrow> C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (T, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLfw (T, p_add C'' P, Some C, A)"
| schedule_infer: "flat_inferences_of (mset \<iota>ss) = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLfw (fold t_add_llist \<iota>ss T, P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<in># t_llists T \<Longrightarrow> lset \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (T, P, Y, A) \<leadsto>ZLfw (t_remove_llist \<iota>s T, P, Y, A)"

inductive
  compute_infer_step ::
  "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> ('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> bool"
where
  "(\<exists>\<iota>s \<in># t_llists T. \<iota>s \<noteq> LNil) \<Longrightarrow> t_pick_elem T = (\<iota>0, T') \<Longrightarrow>
   \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
   compute_infer_step (T, P, None, A) (T', p_add C P, None, A)"

inductive
  choose_p_step :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> ('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> bool"
where
  "P \<noteq> p_empty \<Longrightarrow>
   choose_p_step (T, P, None, A) (T, p_remove (p_select P) P, Some (p_select P), A)"

lemma w_ghosts_compute_infer_step_imp_compute_infer_step:
  assumes "w_ghosts.compute_infer_step St St'"
  shows "compute_infer_step (wo_ghosts_of St) (wo_ghosts_of St')"
  using assms by cases (simp add: compute_infer_step.intros)

lemma choose_p_step_imp_w_ghosts_choose_p_step:
  assumes "choose_p_step (wo_ghosts_of St) (wo_ghosts_of St')"
  shows "w_ghosts.choose_p_step St St'"
  using assms
proof cases
  case (1 P T A)
  note wg_st = this(1) and wg_st' = this(2) and rest = this(3)

  have st: "St = (T, done_of St, P, None, A)"
    using wg_st by (smt (verit) fst_conv snd_conv wo_ghosts_of.elims)
  have st': "St' = (T, done_of St', p_remove (p_select P) P, Some (p_select P), A)"
    using wg_st' by (smt (verit) fst_conv snd_conv wo_ghosts_of.elims)

  show ?thesis
    by (subst st, subst st', simp add: rest w_ghosts.choose_p_step.intros)
qed


subsection \<open>Basic Definitions and Lemmas\<close>

abbreviation todo_of :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> 't" where
  "todo_of St \<equiv> fst St"
abbreviation passive_of :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd St)"
abbreviation yy_of :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd St))"
abbreviation active_of :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd (snd St))"

abbreviation all_formulas_of :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> passive.elems (passive_of St) \<union> set_option (yy_of St) \<union> fset (active_of St)"

definition
  Liminf_zl_fstate :: "('t, 'p, 'f) ZLf_wo_ghosts_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_zl_fstate Sts =
   (Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap (fset \<circ> active_of) Sts))"


subsection \<open>Initial States and Invariants\<close>

inductive is_initial_ZLf_wo_ghosts_state :: "('t, 'p, 'f) ZLf_wo_ghosts_state \<Rightarrow> bool" where
  "flat_inferences_of (mset \<iota>ss) = no_labels.Inf_from {} \<Longrightarrow>
   is_initial_ZLf_wo_ghosts_state (fold t_add_llist \<iota>ss t_empty, p_empty, None, {||})"

lemma is_initial_ZLf_state_imp_is_initial_ZLf_wo_ghosts_state:
  assumes "is_initial_ZLf_state St"
  shows "is_initial_ZLf_wo_ghosts_state (wo_ghosts_of St)"
  using assms by cases (auto intro: is_initial_ZLf_wo_ghosts_state.intros)

lemma is_initial_ZLf_wo_ghosts_state_imp_is_initial_ZLf_state:
  assumes
    init: "is_initial_ZLf_wo_ghosts_state (wo_ghosts_of St)" and
    don: "done_of St = {}"
  shows "is_initial_ZLf_state St"
  using init
  by cases (smt don is_initial_ZLf_state.simps prod.inject prod.exhaust_sel wo_ghosts_of.elims)

end


subsection \<open>Abstract Nonsense for Ghost--Ghostless Conversion\<close>

text \<open>This subsection was originally contributed by Andrei Popescu.\<close>

locale bisim =
  fixes erase :: "'state0 \<Rightarrow> 'state"
  and R :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<leadsto>" 60)
  and R0 :: "'state0 \<Rightarrow> 'state0 \<Rightarrow> bool" (infix "\<leadsto>0" 60)
  assumes simul: "\<And>St0 St'. erase St0 \<leadsto> St' \<Longrightarrow> \<exists>St0'. erase St0' = St' \<and> St0 \<leadsto>0 St0'"
begin

definition lift :: "'state0 \<Rightarrow> 'state \<Rightarrow> 'state0" where
  "lift St0 St' = (SOME St0'. erase St0' = St' \<and> St0 \<leadsto>0 St0')"

lemma lift: "erase St0 \<leadsto> St' \<Longrightarrow> erase (lift St0 St') = St' \<and> St0 \<leadsto>0 lift St0 St'"
  by (smt (verit) lift_def simul someI)

lemmas erase_lift = lift[THEN conjunct1]
lemmas R0_lift = lift[THEN conjunct2]

primcorec theSts0 :: "'state0 \<Rightarrow> 'state llist \<Rightarrow> 'state0 llist" where
  "theSts0 St0 Sts =
   (case Sts of
     LNil \<Rightarrow> LCons St0 LNil
   | LCons St Sts' \<Rightarrow> LCons St0 (theSts0 (lift St0 St) Sts'))"

lemma theSts0_LNil[simp]: "theSts0 St0 LNil = LCons St0 LNil"
  by (subst theSts0.code) auto

lemma theSts0_LCons[simp]: "theSts0 St0 (LCons St Sts') = LCons St0 (theSts0 (lift St0 St) Sts')"
  by (subst theSts0.code) auto

lemma simul_chain0:
  assumes chain: "lnull Sts \<or> (chain (\<leadsto>) Sts \<and> erase St0 \<leadsto> lhd Sts)"
  shows "\<exists>Sts0. lhd Sts0 = St0 \<and> lmap erase (ltl Sts0) = Sts \<and> chain (\<leadsto>0) Sts0"
proof(rule exI[of _ "theSts0 St0 Sts"], safe)
  show "lhd (theSts0 St0 Sts) = St0"
    by (simp add: llist.case_eq_if)
next
  show "lmap erase (ltl (theSts0 St0 Sts)) = Sts"
    using chain
    apply (coinduction arbitrary: Sts St0)
    using lift by (auto simp: llist.case_eq_if) (metis chain.simps eq_LConsD lnull_def)
next
  {
    fix Sts'
    assume "\<exists>St0 Sts. (lnull Sts \<or> chain (\<leadsto>) Sts \<and> erase St0 \<leadsto> lhd Sts) \<and> Sts' = theSts0 St0 Sts"
    hence "chain (\<leadsto>0) Sts'"
      apply (coinduct rule: chain.coinduct)
      apply clarsimp
      apply (erule disjE)
       apply (metis lnull_def theSts0_LNil)
      by (smt (verit, ccfv_threshold) R0_lift chain.simps erase_lift lhd_LCons theSts0_LCons
          theSts0_LNil)
  }
  thus "chain (\<leadsto>0) (theSts0 St0 Sts)"
    using assms by auto
qed

lemma simul_chain:
  assumes
    chain: "chain (\<leadsto>) Sts" and
    hd: "lhd Sts = erase St0"
  shows "\<exists>Sts0. lhd Sts0 = St0 \<and> lmap erase Sts0 = Sts \<and> chain (\<leadsto>0) Sts0"
proof -
  {
    assume nnul: "\<not> lnull (ltl Sts)"
    have "chain (\<leadsto>) (ltl Sts) \<and> erase St0 \<leadsto> lhd (ltl Sts)"
      (is "?thesis1 \<and> ?thesis2")
    proof
      show ?thesis1
        by (simp add: nnul chain chain_ltl)
    next
      show ?thesis2
        by (metis chain chain_consE hd lhd_LCons_ltl lnull_def lnull_ltlI nnul)
    qed
  }
  hence nil_or_chain: "lnull (ltl Sts) \<or> (chain (\<leadsto>) (ltl Sts) \<and> erase St0 \<leadsto> lhd (ltl Sts))"
    by blast

  obtain Sts0 where
    hd_sts0: "lhd Sts0 = St0" and
    erase_tl_sts0: "lmap erase (ltl Sts0) = ltl Sts" and
    chain_sts0: "chain (\<leadsto>0) Sts0"
    using simul_chain0[OF nil_or_chain] by blast

  have erase_hd_sts0: "erase (lhd Sts0) = lhd Sts"
    by (simp add: hd hd_sts0)

  have erase_sts0: "lmap erase Sts0 = Sts"
  proof (cases Sts0 rule: llist.exhaust_sel)
    case LNil
    hence False
      using chain_LNil chain_sts0 by blast
    thus ?thesis
      by blast
  next
    case LCons
    note sts0 = this
    show ?thesis
    proof (cases Sts rule: llist.exhaust_sel)
      case LNil
      hence False
        using chain chain_LNil by blast
      thus ?thesis
        by blast
    next
      case LCons
      note sts = this
      show ?thesis
        by (subst sts0, subst sts, simp add: erase_hd_sts0 erase_tl_sts0)
    qed
  qed

  show ?thesis
    by (rule exI[of _ Sts0]) (use hd_sts0 erase_sts0 chain_sts0 in blast)
qed

end


subsection \<open>Ghost--Ghostless Conversions, the Concrete Version\<close>

context fair_zipperposition_loop_wo_ghosts
begin

lemma
  todo_of_wo_ghosts_of[simp]: "todo_of (wo_ghosts_of St) = w_ghosts.todo_of St" and
  passive_of_wo_ghosts_of[simp]: "passive_of (wo_ghosts_of St) = w_ghosts.passive_of St" and
  yy_of_wo_ghosts_of[simp]: "yy_of (wo_ghosts_of St) = w_ghosts.yy_of St" and
  active_of_wo_ghosts_of[simp]: "active_of (wo_ghosts_of St) = w_ghosts.active_of St"
  by (cases St; simp)+

lemma fair_ZL_step_imp_fair_ZL_wo_ghosts_step:
  assumes "St \<leadsto>ZLf St'"
  shows "wo_ghosts_of St \<leadsto>ZLfw wo_ghosts_of St'"
  using assms by cases (use fair_ZL_wo_ghosts.intros in auto)

lemma fair_ZL_wo_ghosts_step_imp_fair_ZL_step:
  assumes "wo_ghosts_of St0 \<leadsto>ZLfw St'"
  shows "\<exists>St0'. wo_ghosts_of St0' = St' \<and> St0 \<leadsto>ZLf St0'"
  using assms
proof cases
  case (compute_infer T \<iota>0 T' A C P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3-5)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T', D \<union> {\<iota>0}, p_add C P, None, A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, None, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.compute_infer[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (choose_p P T A)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T, D, p_remove (p_select P) P, Some (p_select P), A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, None, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.choose_p[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (delete_fwd C A T P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T, D, P, None, A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Some C, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.delete_fwd[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (simplify_fwd C' C A T P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3,4)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T, D, P, Some C', A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Some C, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.simplify_fwd[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (delete_bwd C' A C T P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3,4)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T, D, P, Some C, A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Some C, A |\<union>| {|C'|})"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.delete_bwd[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (simplify_bwd C' A C'' C T P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3-5)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (T, D, p_add C'' P, Some C, A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Some C, A |\<union>| {|C'|})"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.simplify_bwd[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (schedule_infer \<iota>ss A C T P)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (fold t_add_llist \<iota>ss T, D - flat_inferences_of (mset \<iota>ss), P, None, A |\<union>| {|C|})"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Some C, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.schedule_infer[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
next
  case (delete_orphan_infers \<iota>s T A P Y)
  note wo_st0 = this(1) and st' = this(2) and rest = this(3,4)

  define D :: "'f inference set" where
    "D = done_of St0"
  define St0' :: "('t, 'p, 'f) ZLf_state" where
    "St0' = (t_remove_llist \<iota>s T, D \<union> lset \<iota>s, P, Y, A)"

  have wo_st0': "wo_ghosts_of St0' = St'"
    unfolding St0'_def st' by simp

  have st0: "St0 = (T, D, P, Y, A)"
    using wo_st0 by (smt (verit) D_def fst_conv snd_conv wo_ghosts_of.elims)
  have step0: "St0 \<leadsto>ZLf St0'"
    unfolding st0 St0'_def by (rule fair_ZL.delete_orphan_infers[OF rest])

  show ?thesis
    by (rule exI[of _ St0']) (use wo_st0' step0 in blast)
qed

interpretation bisim: bisim wo_ghosts_of "(\<leadsto>ZLfw)" "(\<leadsto>ZLf)"
proof qed (fact fair_ZL_wo_ghosts_step_imp_fair_ZL_step)

lemma chain_fair_ZL_step_wo_ghosts_imp_chain_fair_ZL_step:
  assumes chain: "chain (\<leadsto>ZLfw) Sts"
  shows "\<exists>Sts0. lmap wo_ghosts_of Sts0 = Sts \<and> chain (\<leadsto>ZLf) Sts0 \<and> done_of (lhd Sts0) = {}"
proof -
  define St0 :: "('t, 'p, 'f) ZLf_state"  where
    "St0 = (todo_of (lhd Sts), {}, passive_of (lhd Sts), yy_of (lhd Sts), active_of (lhd Sts))"

  have hd: "lhd Sts = wo_ghosts_of St0"
    unfolding St0_def by (cases "lhd Sts") auto

  obtain Sts0 where
    wog0: "lmap wo_ghosts_of Sts0 = Sts" and
    chain0: "chain (\<leadsto>ZLf) Sts0" and
    hd0: "lhd Sts0 = St0"
    using bisim.simul_chain[OF chain hd] by blast

  have don0: "done_of (lhd Sts0) = {}"
    unfolding hd0 St0_def by simp

  show ?thesis
    using wog0 chain0 don0 by blast
qed

lemma full_chain_fair_ZL_step_wo_ghosts_imp_full_chain_fair_ZL_step:
  assumes "full_chain (\<leadsto>ZLfw) Sts"
  shows "\<exists>Sts0. Sts = lmap wo_ghosts_of Sts0 \<and> full_chain (\<leadsto>ZLf) Sts0 \<and> done_of (lhd Sts0) = {}"
  by (smt (verit) assms chain_fair_ZL_step_wo_ghosts_imp_chain_fair_ZL_step empty_def
      fair_ZL_step_imp_fair_ZL_wo_ghosts_step full_chain_iff_chain full_chain_not_lnull lfinite_lmap
      llast_lmap llist.map_disc_iff passive.felems_empty todo.llists_empty)


subsection \<open>Completeness\<close>

theorem
  assumes
    full: "full_chain (\<leadsto>ZLfw) Sts" and
    init: "is_initial_ZLf_wo_ghosts_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<longrightarrow> infinitely_often choose_p_step Sts"
  shows
    fair_ZL_wo_ghosts_Liminf_saturated: "saturated (labeled_formulas_of (Liminf_zl_fstate Sts))" and
    fair_ZL_wo_ghosts_complete_Liminf: "B \<in> Bot_F \<Longrightarrow>
      passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_zl_fstate Sts)" and
    fair_ZL_wo_ghosts_complete: "B \<in> Bot_F \<Longrightarrow> passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
proof -
  obtain Sts0 :: "('t, 'p, 'f) ZLf_state llist" where
    full0: "full_chain (\<leadsto>ZLf) Sts0" and
    sts0: "lmap wo_ghosts_of Sts0 = Sts" and
    don0: "done_of (lhd Sts0) = {}"
    using full_chain_fair_ZL_step_wo_ghosts_imp_full_chain_fair_ZL_step[OF full] by blast

  have init0: "is_initial_ZLf_state (lhd Sts0)"
  proof -
    have hd: "lhd (lmap wo_ghosts_of Sts0) = wo_ghosts_of (lhd Sts0)"
      using full0 full_chain_not_lnull llist.map_sel(1) by blast
    show ?thesis
      by (rule is_initial_ZLf_wo_ghosts_state_imp_is_initial_ZLf_state[OF
            init[unfolded sts0[symmetric] hd] don0])
  qed

  have fair0: "infinitely_often w_ghosts.compute_infer_step Sts0 \<longrightarrow>
    infinitely_often w_ghosts.choose_p_step Sts0"
  proof
    assume inf_ci0: "infinitely_often w_ghosts.compute_infer_step Sts0"

    have "infinitely_often compute_infer_step Sts"
      unfolding sts0[symmetric]
      by (rule infinitely_often_lifting[of _ "\<lambda>x. x", unfolded llist.map_ident, OF _ inf_ci0])
        (use w_ghosts_compute_infer_step_imp_compute_infer_step in auto)
    hence inf_cp: "infinitely_often choose_p_step Sts"
      by (simp add: fair)

    show "infinitely_often w_ghosts.choose_p_step Sts0"
      by (rule infinitely_often_lifting[of _ _ _ "\<lambda>x. x", unfolded llist.map_ident,
            OF _ inf_cp[unfolded sts0[symmetric]]])
        (use choose_p_step_imp_w_ghosts_choose_p_step in auto)
  qed

  have "saturated (labeled_formulas_of (w_ghosts.Liminf_zl_fstate Sts0))"
    using fair_ZL_Liminf_saturated[OF full0 init0 fair0] .
  thus "saturated (labeled_formulas_of (Liminf_zl_fstate Sts))"
    unfolding w_ghosts.Liminf_zl_fstate_def Liminf_zl_fstate_def sts0[symmetric]
    by (simp add: llist.map_comp)

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"

    have unsat0: "passive.elems (w_ghosts.passive_of (lhd Sts0)) \<Turnstile>\<inter>\<G> {B}"
    proof -
      have "lhd (lmap wo_ghosts_of Sts0) = wo_ghosts_of (lhd Sts0)"
        using full0 full_chain_not_lnull llist.map_sel(1) by blast
      hence "passive_of (lhd (lmap wo_ghosts_of Sts0)) = w_ghosts.passive_of (lhd Sts0)"
        by simp
      thus ?thesis
        using unsat unfolding sts0[symmetric] by auto
    qed

    have "\<exists>B' \<in> Bot_F. B' \<in> formulas_union (w_ghosts.Liminf_zl_fstate Sts0)"
      by (rule fair_ZL_complete_Liminf[OF full0 init0 fair0 bot unsat0])
    thus "\<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_zl_fstate Sts)"
      unfolding w_ghosts.Liminf_zl_fstate_def Liminf_zl_fstate_def sts0[symmetric]
      by (simp add: llist.map_comp)
    thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
      unfolding Liminf_zl_fstate_def Liminf_llist_def by auto
  }
qed

end


subsection \<open>Specialization with FIFO Queue\<close>

text \<open>As a proof of concept, we specialize the passive set to use a FIFO queue,
thereby eliminating the locale assumptions about the passive set.\<close>

locale fifo_zipperposition_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Inf_G_q :: "'q \<Rightarrow> 'g inference set" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<doteq>\<close> 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<prec>\<cdot>\<close> 50) +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_Prec_S: "minimal_element (\<prec>S) UNIV" and
    transp_Prec_S: "transp (\<prec>S)" and
    countable_Inf_between: "finite A \<Longrightarrow> countable (no_labels.Inf_between A {C})"
begin

sublocale fifo_prover_queue
  .

sublocale fifo_prover_lazy_list_queue
  .

sublocale fair_zipperposition_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F empty add_llist remove_llist pick_elem llists "[]" hd
  "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list Prec_S
proof
  show "po_on (\<prec>S) UNIV"
    using wf_Prec_S minimal_element.po by blast
next
  show "wfp_on (\<prec>S) UNIV"
    using wf_Prec_S minimal_element.wf by blast
next
  show "transp (\<prec>S)"
    by (rule transp_Prec_S)
next
  show "\<And>A C. finite A \<Longrightarrow> countable (no_labels.Inf_between A {C})"
    by (fact countable_Inf_between)
qed

end

end
