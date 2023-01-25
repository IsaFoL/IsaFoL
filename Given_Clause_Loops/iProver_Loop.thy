(* Title:        iProver Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>iProver Loop\<close>

text \<open>The iProver loop is a variant of the Otter loop that supports the
elimination of clauses that are made redundant by their own children.\<close>

theory iProver_Loop
  imports Otter_Loop
begin

context otter_loop
begin


subsection \<open>Definition\<close>

inductive IL :: "('f \<times> OL_label) set \<Rightarrow> ('f \<times> OL_label) set \<Rightarrow> bool" (infix "\<leadsto>IL" 50)
where
  ol: "St \<leadsto>OL St' \<Longrightarrow> St \<leadsto>IL St'"
| red_by_children: "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = {C'} \<and> C' \<prec>\<cdot> C) \<Longrightarrow>
    state ({}, {}, P, {C}, A) \<leadsto>IL state (M, {}, P, {}, A)"


subsection \<open>Refinement\<close>

lemma red_by_children_in_GC:
  assumes "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = {C'} \<and> C' \<prec>\<cdot> C)"
  shows "state ({}, {}, P, {C}, A) \<leadsto>GC state (M, {}, P, {}, A)"
proof -
  let ?\<N> = "state ({}, {}, P, {}, A)"
  and ?St = "{(C, YY)}"
  and ?St' = "{(x, New) |x. x \<in> M}"

  have "(C, YY) \<in> Red_F (?\<N> \<union> ?St')"
    using assms
  proof
    assume c_in: "C \<in> no_labels.Red_F (A \<union> M)"
    have "A \<union> M \<subseteq> A \<union> M \<union> P" by auto
    also have "fst ` (?\<N> \<union> ?St') = A \<union> M \<union> P"
      by auto
    then have "C \<in> no_labels.Red_F (fst ` (?\<N> \<union> ?St'))"
      by (metis (no_types, lifting) c_in calculation in_mono no_labels.Red_F_of_subset)
    then show "(C, YY) \<in> Red_F (?\<N> \<union> ?St')"
      using no_labels_Red_F_imp_Red_F by blast
  next
    assume assm: "M = {C'} \<and> C' \<prec>\<cdot> C"
    then have "C' \<in> fst ` (?\<N> \<union> ?St')"
      by simp
    then show "(C, YY) \<in> Red_F (?\<N> \<union> ?St')"
      by (metis (mono_tags) assm succ_F_imp_Red_F)
  qed
  then have St_included_in: "?St \<subseteq> Red_F (?\<N> \<union> ?St')"
    by auto

  have prj_of_active_subset_of_St': "fst ` (active_subset ?St') = {}"
    by (simp add: active_subset_def)

  have "?\<N> \<union> ?St \<leadsto>GC ?\<N> \<union> ?St'"
    using process[of _ "?\<N>" "?St" _ "?St'"] St_included_in prj_of_active_subset_of_St' by auto
  moreover have "?\<N> \<union> ?St = state ({}, {}, P, {C}, A)"
    by simp
  moreover have "?\<N> \<union> ?St' = state (M, {}, P, {}, A)"
    by auto
  ultimately show "state ({}, {}, P, {C}, A) \<leadsto>GC state (M, {}, P, {}, A)"
    by simp
qed

theorem IL_step_imp_GC_step: "M \<leadsto>IL M' \<Longrightarrow> M \<leadsto>GC M'"
proof (induction rule: IL.induct)
  case (ol St St')
  then show ?case
    by (simp add: OL_step_imp_GC_step)
next
  case (red_by_children C A M C' P)
  then show ?case using red_by_children_in_GC
    by auto
qed


subsection \<open>Completeness\<close>

theorem
  assumes
    il_chain: "chain (\<leadsto>IL) Sts" and
    act: "active_subset (lhd Sts) = {}" and
    pas: "passive_subset (Liminf_llist Sts) = {}"
  shows
    IL_Liminf_saturated: "saturated (Liminf_llist Sts)" and
    IL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fst ` lhd Sts \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist Sts" and
    IL_complete: "B \<in> Bot_F \<Longrightarrow> fst ` lhd Sts \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> lnth Sts i)"
proof -
  have gc_chain: "chain (\<leadsto>GC) Sts"
    using il_chain IL_step_imp_GC_step chain_mono by blast

  show "saturated (Liminf_llist Sts)"
    using gc.fair_implies_Liminf_saturated gc_chain gc_fair gc_to_red act pas by blast

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "fst ` lhd Sts \<Turnstile>\<inter>\<G> {B}"
  
    show "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist Sts"
      by (rule gc_complete_Liminf[OF gc_chain act pas bot unsat])
    then show "\<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> lnth Sts i)"
      unfolding Liminf_llist_def by auto
  }
qed

end

end
