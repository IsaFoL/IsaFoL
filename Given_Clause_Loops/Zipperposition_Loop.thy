(* Title:        Zipperposition Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021
*)

section \<open>Zipperposition Loop\<close>

theory Zipperposition_Loop
  imports DISCOUNT_Loop
begin

context discount_loop
begin


subsection \<open>Definition and Lemmas\<close>

fun zl_inferences_of :: "'f inference llist set \<Rightarrow> 'f inference set " where
  "zl_inferences_of T = \<Union> {lset x |x. x \<in> T}"

fun
  zl_state :: "'f inference llist set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow>
    'f inference set \<times> ('f \<times> DL_label) set"
where
  "zl_state (T, P, Y, A) = (zl_inferences_of T, formulas_of (P, Y, A))"

inductive
  ZL :: "'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> bool"
  (infix "\<leadsto>ZL" 50)
where
  choose_p: "zl_state (T, P \<union> {C}, {}, A) \<leadsto>ZL zl_state (T, P, {C}, A)"
| delete_fwd: "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    zl_state (T, P, {C}, A) \<leadsto>ZL zl_state (T, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (A \<union> {C'}) \<Longrightarrow>
    zl_state (T, P, {C}, A) \<leadsto>ZL zl_state (T, P, {C'}, A)"
| delete_bwd: "C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    zl_state (T, P, {C}, A \<union> {C'}) \<leadsto>ZL zl_state (T, P, {C}, A)"
| simplify_bwd: "C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    zl_state (T, P, {C}, A \<union> {C'}) \<leadsto>ZL zl_state (T, P \<union> {C''}, {C}, A)"
| compute_infer: "\<iota>0 \<in> no_labels.Red_I (A \<union> {C}) \<Longrightarrow>
    zl_state (T \<union> {(LCons \<iota>0 \<iota>s)}, P, {}, A) \<leadsto>ZL zl_state (T \<union> {\<iota>s}, P \<union> {C}, {}, A)"
| schedule_infer: "zl_inferences_of T' = (no_labels.Inf_between A {C}) \<Longrightarrow>
    zl_state (T, P, {C}, A) \<leadsto>ZL zl_state (T \<union> T', P, {}, A \<union> {C})"
| delete_orphan_formulas: "\<forall>n \<in> {n. enat n < llength \<iota>s}. lnth \<iota>s n \<notin> no_labels.Inf_from A \<Longrightarrow>
    zl_state (T \<union> {\<iota>s}, P, Y, A) \<leadsto>ZL zl_state (T, P, Y, A)"

lemma flatten: " zl_inferences_of {(LCons \<iota>0 \<iota>s)} = zl_inferences_of {\<iota>s} \<union> { \<iota>0 }"
  by auto

lemma distr_zl_inferences_of_wrt_union:
  "zl_inferences_of (T \<union> T') = zl_inferences_of T \<union> zl_inferences_of T'"
  by auto

lemma "zl_inferences_of (T \<union> {\<iota>s}) = zl_inferences_of T \<union> (lset \<iota>s)"
  by auto


subsection \<open>Refinement\<close>

lemma zl_choose_p_in_lgc: "zl_state (T, P \<union> {C}, {}, A) \<leadsto>LGC zl_state (T, P, {C}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  and ?\<T> = "zl_inferences_of T"
  have "Passive \<sqsupset>L YY"
    by (simp add: DL_Prec_L_def)
  then have "(?\<T>, ?\<N> \<union> {(C, Passive)}) \<leadsto>LGC (?\<T>, ?\<N> \<union> {(C, YY)})"
    using relabel_inactive by blast
  then have "(?\<T>, formulas_of (P \<union> {C}, {}, A)) \<leadsto>LGC (?\<T>, formulas_of (P, {C}, A))"
     by (metis PYA_add_passive_formula P0A_add_y_formula)
  then show ?thesis
    by auto
qed

lemma zl_delete_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C)"
  shows "zl_state (T, P, {C}, A) \<leadsto>LGC zl_state (T, P, {}, A)"
  using assms
proof
  assume c_in: "C \<in> no_labels.Red_F A"
  then have "A \<subseteq> fst ` formulas_of (P, {}, A)"
    by simp
  then have "C \<in> no_labels.Red_F (fst ` formulas_of (P, {}, A))"
    by (metis (no_types, lifting) c_in in_mono no_labels.Red_F_of_subset)
  then show ?thesis
    using remove_redundant_no_label by auto
next
  assume "\<exists>C' \<in> A. C' \<preceq>\<cdot> C"
  then obtain C' where c'_in_and_c'_ls_c: "C' \<in> A \<and> C' \<preceq>\<cdot> C"
    by auto
  then have "(C', Active) \<in> formulas_of (P, {}, A)"
    by auto
  moreover have "YY \<sqsupset>L Active"
    by (simp add: DL_Prec_L_def)
  ultimately show ?thesis
    by (metis P0A_add_y_formula remove_succ_L c'_in_and_c'_ls_c zl_state.simps)
qed

lemma zl_simplify_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F_\<G> (A \<union> {C'})"
  shows "zl_state (T, P, {C}, A) \<leadsto>LGC zl_state (T, P, {C'}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  and ?\<M> = "{(C, YY)}"
  and ?\<M>'= "{(C', YY)}"
  have "A \<union> {C'} \<subseteq> fst ` (?\<N> \<union> ?\<M>')"
    by auto
  then have "C \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (verit, ccfv_SIG) assms no_labels.Red_F_of_subset subset_iff)
  then have "(C, YY) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by simp
  then have "?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    by simp
  moreover have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  ultimately have "(zl_inferences_of T, formulas_of (P, {}, A) \<union> {(C, YY)}) \<leadsto>LGC
    (zl_inferences_of T, formulas_of (P, {}, A) \<union> {(C', YY)})"
    using process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  then show ?thesis
    by simp
qed

lemma zl_delete_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C} \<or> C' \<cdot>\<succ> C"
  shows "zl_state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC zl_state (T, P, {C}, A)"
  using assms
proof
  let ?\<N> = "formulas_of (P, {C}, A)"
  assume c'_in: "C' \<in> no_labels.Red_F_\<G> {C}"

  have "{C} \<subseteq> fst ` ?\<N>"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` ?\<N>)"
    by (metis (no_types, lifting) c'_in insert_Diff insert_subset no_labels.Red_F_of_subset)
  then have "(zl_inferences_of T, ?\<N> \<union> {(C', Active)}) \<leadsto>LGC (zl_inferences_of T, ?\<N>)"
    using remove_redundant_no_label by auto

  moreover have "?\<N> \<union> {(C', Active)} = formulas_of (P, {C}, A \<union> {C'})"
    using PYA_add_active_formula by blast
  ultimately have "(zl_inferences_of T, formulas_of (P, {C}, A \<union> {C'})) \<leadsto>LGC
    zl_state (T, P, {C}, A)"
    by simp
  then show ?thesis by auto
next
  assume "C' \<cdot>\<succ> C"
  moreover have "(C, YY) \<in> formulas_of (P, {C}, A)"
    by simp
  ultimately show ?thesis
    by (metis remove_succ_F PYA_add_active_formula zl_state.simps)
qed

lemma zl_simplify_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C, C''}"
  shows "zl_state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC zl_state (T, P \<union> {C''}, {C}, A)"
proof -
  let ?\<M> = "{(C', Active)}"
  and ?\<M>' = "{(C'', Passive)}"
  and ?\<N> = "formulas_of (P, {C}, A)"
  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (z3) DiffI Diff_eq_empty_iff assms empty_iff no_labels.Red_F_of_subset)
  then have \<M>_included: " ?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  then have "(zl_inferences_of T, ?\<N> \<union> ?\<M>) \<leadsto>LGC (zl_inferences_of T, ?\<N> \<union> ?\<M>')"
    using \<M>_included process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  moreover have "?\<N> \<union> ?\<M> = formulas_of(P, {C}, A \<union> {C'})"
  and "?\<N> \<union> ?\<M>' = formulas_of(P \<union> {C''}, {C}, A)"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma zl_compute_infer_in_lgc:
  assumes "\<iota>0 \<in> no_labels.Red_I (A \<union> {C})"
  shows "zl_state (T \<union> {(LCons \<iota>0 \<iota>s)}, P, {}, A) \<leadsto>LGC zl_state (T \<union> {\<iota>s}, P \<union> {C}, {}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  and ?\<M> = "{(C, Passive)}"

  have active_subset_of_\<M>: "active_subset ?\<M> = {}"
    using active_subset_def by auto
  moreover have "A \<union> {C} \<subseteq> fst ` (?\<N> \<union> ?\<M>)" by auto
  ultimately have "\<iota>0 \<in> no_labels.Red_I (fst ` (?\<N> \<union> ?\<M>))"
    by (meson assms no_labels.empty_ord.Red_I_of_subset subsetD)
  then have compute_one_infer:
    "(zl_inferences_of (T \<union> {\<iota>s}) \<union> {\<iota>0}, formulas_of (P, {}, A)) \<leadsto>LGC
     (zl_inferences_of (T \<union> {\<iota>s}), formulas_of (P, {}, A) \<union> {(C, Passive)})"
    by (metis active_subset_of_\<M> step.compute_infer)
  moreover have "zl_inferences_of (T \<union> {(LCons \<iota>0 \<iota>s)}) = zl_inferences_of (T \<union> {\<iota>s}) \<union> {\<iota>0}"
    by (metis Un_assoc distr_zl_inferences_of_wrt_union flatten)
  moreover have "formulas_of (P, {}, A) \<union> {(C, Passive)} = formulas_of (P \<union> {C}, {}, A)"
      using PYA_add_passive_formula by blast
  ultimately show "zl_state (T \<union> {(LCons \<iota>0 \<iota>s)}, P, {}, A) \<leadsto>LGC
             zl_state (T \<union> {\<iota>s}, P \<union> {C}, {}, A)"
    using zl_state.simps by auto
qed

lemma zl_schedule_infer_in_lgc:
  assumes "zl_inferences_of T' = no_labels.Inf_between A {C}"
  shows "zl_state (T, P, {C}, A) \<leadsto>LGC zl_state (T \<union> T', P, {}, A \<union> {C})"
proof -
  let ?\<N>= " formulas_of (P, {}, A) "
  have " fst ` (active_subset ?\<N>) = A "
    by (meson prj_active_subset_of_state)
  then have "zl_inferences_of T' = (no_labels.Inf_between (fst ` (active_subset ?\<N>)) {C})"
    using assms by simp
  then have "(zl_inferences_of T, ?\<N> \<union> {(C, YY)}) \<leadsto>LGC
    (zl_inferences_of T \<union> zl_inferences_of T', ?\<N> \<union> {(C, Active)})"
    using step.schedule_infer by blast
  moreover have "formulas_of (P, {C}, A) = ?\<N> \<union> {(C, YY)}"
    by auto
  moreover have "formulas_of (P, {}, A \<union> {C}) = ?\<N> \<union> {(C, Active)}"
    by auto
  ultimately have H0: "(zl_inferences_of T, formulas_of (P, {C}, A)) \<leadsto>LGC
    (zl_inferences_of T \<union> zl_inferences_of T', formulas_of (P, {}, A \<union> {C}))"
    by presburger
  then show "zl_state (T, P, {C}, A) \<leadsto>LGC zl_state (T \<union> T', P, {}, A \<union> {C})"
    using distr_zl_inferences_of_wrt_union zl_state.simps by presburger
qed

lemma zl_delete_orphan_formulas_in_lgc:
  assumes " \<forall>n \<in> {n. enat n < llength \<iota>s}. lnth \<iota>s n \<notin> no_labels.Inf_from A"
  shows "zl_state (T \<union> {\<iota>s}, P, Y, A) \<leadsto>LGC zl_state (T, P, Y, A)"
proof -
  let ?\<N> = "formulas_of (P, Y, A)"
  and ?\<T>' = "lset \<iota>s"
  and ?\<T>  = "zl_inferences_of T"

  have " {lnth \<iota>s n |n. enat n < llength \<iota>s} \<inter> no_labels.Inf_from A = {}"
    using assms by auto

  moreover have "{lnth \<iota>s n |n. enat n < llength \<iota>s} = lset \<iota>s"
    by (simp add: lset_conv_lnth)

  ultimately have \<iota>s_orphans: "?\<T>' \<inter> no_labels.Inf_from A = {}"
    by auto

  have "fst ` active_subset ?\<N> = A"
    using prj_active_subset_of_state by auto
  then have \<iota>s_orphans: "?\<T>' \<inter> no_labels.Inf_from (fst ` active_subset ?\<N>) = {}"
    using assms \<iota>s_orphans by auto

  have thesis_before_rewriting: "(?\<T> \<union> ?\<T>', ?\<N>) \<leadsto>LGC (?\<T>, ?\<N>)"
    using \<iota>s_orphans step.delete_orphan_formulas by presburger

  have "zl_inferences_of (T \<union> {\<iota>s}) = zl_inferences_of T \<union> zl_inferences_of {\<iota>s}"
    using distr_zl_inferences_of_wrt_union by auto
  moreover have "zl_inferences_of (T \<union> {\<iota>s}) = ?\<T> \<union> (lset \<iota>s)"
    by auto
  ultimately show ?thesis
    using thesis_before_rewriting zl_state.simps by presburger
qed

theorem ZL_step_imp_LGC_step: "T\<M> \<leadsto>ZL T\<M>' \<Longrightarrow> T\<M> \<leadsto>LGC T\<M>'"
proof (induction rule: ZL.induct)
  case (choose_p T P C A)
  then show ?case
    using zl_choose_p_in_lgc by auto
next
  case (delete_fwd C A T P)
  then show ?case
    using zl_delete_fwd_in_lgc by auto
next
  case (simplify_fwd C A C' T P)
  then show ?case
    using zl_simplify_fwd_in_lgc by blast
next
  case (delete_bwd C' C T P A)
  then show ?case
    using zl_delete_bwd_in_lgc by blast
next
  case (simplify_bwd C' C C'' T P A)
  then show ?case
    using zl_simplify_bwd_in_lgc by blast
next
  case (compute_infer \<iota>0 A C T \<iota>s P)
  then show ?case
    using zl_compute_infer_in_lgc by auto
next
  case (schedule_infer T' A C T P)
  then show ?case
    using zl_schedule_infer_in_lgc by blast
next
  case (delete_orphan_formulas \<iota>s A T P Y)
  then show ?case
    using zl_delete_orphan_formulas_in_lgc by auto
qed


section \<open>Completeness\<close>

theorem
  assumes
    zl_chain: "chain (\<leadsto>ZL) Sts" and
    act: "active_subset (snd (lhd Sts)) = {}" and
    pas: "passive_subset (Liminf_llist (lmap snd Sts)) = {}" and
    no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd Sts)" and
    final_sched: "Liminf_llist (lmap fst Sts) = {}" and
    bot: "B \<in> Bot_F" and
    unsat: "fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B}"
  shows
    ZL_complete_Liminf: "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)" and
    ZL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
proof -
  have lgc_chain: "chain (\<leadsto>LGC) Sts"
    using zl_chain ZL_step_imp_LGC_step chain_mono by blast
  show ZL_complete_Liminf: "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)"
    by (rule lgc_complete_Liminf[OF lgc_chain act pas no_prems_init final_sched bot unsat])
  then show OL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
    unfolding Liminf_llist_def by auto
qed

end

end
