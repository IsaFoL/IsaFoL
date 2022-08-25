(* Title:        Fair Zipperposition Loop without Ghosts
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Fair Zipperposition Loop without Ghosts\<close>

theory Fair_Zipperposition_Loop_without_Ghosts
  imports Fair_Zipperposition_Loop
begin


subsection \<open>Locale\<close>

type_synonym ('t, 'p, 'f) fair_ZL_state_wo_ghosts = "'t \<times> 'p \<times> 'f option \<times> 'f fset"

locale fair_zipperposition_loop_wo_ghosts =
  w_ghosts?: fair_zipperposition_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q
    \<G>_I_q Equiv_F Prec_F t_empty t_select t_add t_remove t_felems p_empty p_select p_add p_remove
    p_felems Prec_S
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
    t_empty :: "'t" and
    t_select :: "'t \<Rightarrow> 'f inference llist" and
    t_add :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_remove :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_felems :: "'t \<Rightarrow> 'f inference llist fset" and
    p_empty :: "'p" and
    p_select :: "'p \<Rightarrow> 'f" and
    p_add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_felems :: "'p \<Rightarrow> 'f fset" and
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
begin

inductive
  fair_ZL_wo_ghosts ::
  "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> ('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> bool"
  (infix "\<leadsto>ZLfw" 50)
where
  compute_infer: "T \<noteq> t_empty \<Longrightarrow> t_select T = LCons \<iota>0 \<iota>s \<Longrightarrow>
    \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (T, P, None, A) \<leadsto>ZLfw (t_add \<iota>s (t_remove (t_select T) T), p_add C P, None, A)"
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
| schedule_infer: "flat_inferences_of (set \<iota>ss) = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLfw (fold t_add \<iota>ss T, P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<in> todo.elems T \<Longrightarrow> lset \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (T, P, Y, A) \<leadsto>ZLfw (t_remove \<iota>s T, P, Y, A)"

inductive
  compute_infer_step ::
  "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> ('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> bool"
where
  "T \<noteq> t_empty \<Longrightarrow> t_select T = LCons \<iota>0 \<iota>s \<Longrightarrow> \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
   compute_infer_step (T, P, None, A)
     (t_add \<iota>s (t_remove (t_select T) T), p_add C P, None, A)"

inductive
  choose_p_step ::
  "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> ('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> bool"
where
  "P \<noteq> p_empty \<Longrightarrow>
   choose_p_step (T, P, None, A) (T, p_remove (p_select P) P, Some (p_select P), A)"


subsection \<open>Definitions and Lemmas\<close>

abbreviation todo_of :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> 't" where
  "todo_of St \<equiv> fst St"
abbreviation passive_of :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd St)"
abbreviation yy_of :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd St))"
abbreviation active_of :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd (snd St))"

abbreviation all_formulas_of :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> passive.elems (passive_of St) \<union> set_option (yy_of St) \<union> fset (active_of St)"

definition
  Liminf_zl_fstate :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_zl_fstate Sts =
   (Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap (fset \<circ> active_of) Sts))"


subsection \<open>Initial States and Invariants\<close>

inductive is_initial_fair_ZL_state :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> bool" where
  "flat_inferences_of (set \<iota>ss) = no_labels.Inf_from {} \<Longrightarrow>
   is_initial_fair_ZL_state (fold t_add \<iota>ss t_empty, p_empty, None, {||})"

inductive fair_ZL_invariant :: "('t, 'p, 'f) fair_ZL_state_wo_ghosts \<Rightarrow> bool" where
  "flat_inferences_of (todo.elems T) \<subseteq> Inf_F \<Longrightarrow> fair_ZL_invariant (T, P, Y, A)"


subsection \<open>Completeness\<close>

theorem
  assumes
    full: "full_chain (\<leadsto>ZLfw) Sts" and
    init: "is_initial_fair_ZL_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<Longrightarrow>
      infinitely_often choose_p_step Sts" and
    bot: "B \<in> Bot_F" and
    unsat: "passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"
  shows
    fair_ZL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> formulas_union (Liminf_zl_fstate Sts)" and
    fair_ZL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
  sorry

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

sublocale fifo_passive_set
  .

sublocale fair_zipperposition_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list "[]" hd
  "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list Prec_S
proof unfold_locales
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
