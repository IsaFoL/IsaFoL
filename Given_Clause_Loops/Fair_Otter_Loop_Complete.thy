(* Title:        Completeness of Fair Otter Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Completeness of Fair Otter Loop\<close>

text \<open>The Otter loop is a special case of the iProver loop, with fewer rules.
We can therefore reuse the fair iProver loop's completeness result to derive the
(dynamic) refutational completeness of the fair Otter loop.\<close>

theory Fair_Otter_Loop_Complete
  imports Fair_iProver_Loop
begin


subsection \<open>Completeness\<close>

context fair_otter_loop
begin

theorem
  assumes
    full: "full_chain (\<leadsto>OLf) Sts" and
    init: "is_initial_OLf_state (lhd Sts)"
  shows
    fair_OL_Liminf_saturated: "saturated (state (Liminf_fstate Sts))" and
    fair_OL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>B' \<in> Bot_F. B' \<in> state_union (Liminf_fstate Sts)" and
    fair_OL_complete: "B \<in> Bot_F \<Longrightarrow> fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
proof -
  have ilf_chain: "chain (\<leadsto>ILf) Sts"
    using Lazy_List_Chain.chain_mono fair_IL.ol full_chain_imp_chain full by blast
  hence ilf_full: "full_chain (\<leadsto>ILf) Sts"
    by (metis chain_ILf_invariant_llast full_chain_iff_chain initial_OLf_invariant
        is_final_OLf_state_iff_no_ILf_step is_final_OLf_state_iff_no_OLf_step full init)

  show "saturated (state (Liminf_fstate Sts))"
    by (rule fair_IL_Liminf_saturated[OF ilf_full init])

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"

    show "\<exists>B' \<in> Bot_F. B' \<in> state_union (Liminf_fstate Sts)"
      by (rule fair_IL_complete_Liminf[OF ilf_full init bot unsat])
    show "\<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
      by (rule fair_IL_complete[OF ilf_full init bot unsat])
  }
qed

end


subsection \<open>Specialization with FIFO Queue\<close>

text \<open>As a proof of concept, we specialize the passive set to use a FIFO queue,
thereby eliminating the locale assumptions about the passive set.\<close>

locale fifo_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
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
    finite_Inf_between: "finite A \<Longrightarrow> finite (no_labels.Inf_between A {C})"
begin

sublocale fifo_prover_queue
  .

sublocale fair_otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list Prec_S
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
  show "\<And>A C. finite A \<Longrightarrow> finite (no_labels.Inf_between A {C})"
    by (fact finite_Inf_between)
qed

end

end
