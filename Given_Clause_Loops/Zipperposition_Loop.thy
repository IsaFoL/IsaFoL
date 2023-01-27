(* Title:        Zipperposition Loop with Ghost State
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Zipperposition Loop with Ghost State\<close>

text \<open>The Zipperposition loop is a variant of the DISCOUNT loop that can cope
with inferences generating (countably) infinitely many conclusions. The version
formalized here has an additional ghost component @{text D} in its state tuple,
which is used in the refinement proof from the abstract procedure @{text LGC}.\<close>

theory Zipperposition_Loop
  imports DISCOUNT_Loop
begin

context discount_loop
begin


subsection \<open>Basic Definitions and Lemmas\<close>

fun flat_inferences_of :: "'f inference llist multiset \<Rightarrow> 'f inference set" where
  "flat_inferences_of T = \<Union> {lset \<iota> |\<iota>. \<iota> \<in># T}"

fun
  zl_state :: "'f inference llist multiset \<times> 'f inference set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow>
    'f inference set \<times> ('f \<times> DL_label) set"
where
  "zl_state (T, D, P, Y, A) = (flat_inferences_of T - D, labeled_formulas_of (P, Y, A))"

lemma zl_state_alt_def:
  "zl_state (T, D, P, Y, A) =
   (flat_inferences_of T - D, (\<lambda>C. (C, Passive)) ` P \<union> (\<lambda>C. (C, YY)) ` Y \<union> (\<lambda>C. (C, Active)) ` A)"
  by auto

inductive
  ZL :: "'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> bool"
  (infix "\<leadsto>ZL" 50)
where
  compute_infer: "\<iota>0 \<in> no_labels.Red_I (A \<union> {C}) \<Longrightarrow>
    zl_state (T + {#LCons \<iota>0 \<iota>s#}, D, P, {}, A) \<leadsto>ZL zl_state (T + {#\<iota>s#}, D \<union> {\<iota>0}, P \<union> {C}, {}, A)"
| choose_p: "zl_state (T, D, P \<union> {C}, {}, A) \<leadsto>ZL zl_state (T, D, P, {C}, A)"
| delete_fwd: "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    zl_state (T, D, P, {C}, A) \<leadsto>ZL zl_state (T, D, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (A \<union> {C'}) \<Longrightarrow>
    zl_state (T, D, P, {C}, A) \<leadsto>ZL zl_state (T, D, P, {C'}, A)"
| delete_bwd: "C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    zl_state (T, D, P, {C}, A \<union> {C'}) \<leadsto>ZL zl_state (T, D, P, {C}, A)"
| simplify_bwd: "C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    zl_state (T, D, P, {C}, A \<union> {C'}) \<leadsto>ZL zl_state (T, D, P \<union> {C''}, {C}, A)"
| schedule_infer: "flat_inferences_of T' = no_labels.Inf_between A {C} \<Longrightarrow>
    zl_state (T, D, P, {C}, A) \<leadsto>ZL zl_state (T + T', D - flat_inferences_of T', P, {}, A \<union> {C})"
| delete_orphan_infers: "lset \<iota>s \<inter> no_labels.Inf_from A = {} \<Longrightarrow>
    zl_state (T + {#\<iota>s#}, D, P, Y, A) \<leadsto>ZL zl_state (T, D \<union> lset \<iota>s, P, Y, A)"


subsection \<open>Refinement\<close>

lemma zl_compute_infer_in_lgc:
  assumes "\<iota>0 \<in> no_labels.Red_I (A \<union> {C})"
  shows "zl_state (T + {#LCons \<iota>0 \<iota>s#}, D, P, {}, A) \<leadsto>LGC
    zl_state (T + {#\<iota>s#}, D \<union> {\<iota>0}, P \<union> {C}, {}, A)"
proof -
  show ?thesis
  proof (cases "\<iota>0 \<in> D")
    case True
    hence infs: "flat_inferences_of (T + {#LCons \<iota>0 \<iota>s#}) - D =
      flat_inferences_of (T + {#\<iota>s#}) - (D \<union> {\<iota>0})"
      by fastforce
    show ?thesis
      unfolding zl_state.simps infs
      by (rule step.process[of _ "labeled_formulas_of (P, {}, A)" "{}" _ "{(C, Passive)}"])
        (auto simp: active_subset_def)
  next
    case i0_ni: False
    show ?thesis
      unfolding zl_state.simps
    proof (rule step.compute_infer[of _ _ \<iota>0 _ _ "{(C, Passive)}"])
      show "flat_inferences_of (T + {#LCons \<iota>0 \<iota>s#}) - D =
        flat_inferences_of (T + {#\<iota>s#}) - (D \<union> {\<iota>0}) \<union> {\<iota>0}"
        using i0_ni by fastforce
    next
      show "labeled_formulas_of (P \<union> {C}, {}, A) = labeled_formulas_of (P, {}, A) \<union> {(C, Passive)}"
        by auto
    next
      show "active_subset {(C, Passive)} = {}"
        by (auto simp: active_subset_def)
    next
      show "\<iota>0 \<in> no_labels.Red_I_\<G> (fst ` (labeled_formulas_of (P, {}, A) \<union> {(C, Passive)}))"
        by simp (metis (no_types) Un_commute Un_empty_right Un_insert_right Un_upper1 assms
            no_labels.empty_ord.Red_I_of_subset subset_iff)
    qed
  qed
qed

lemma zl_choose_p_in_lgc: "zl_state (T, D, P \<union> {C}, {}, A) \<leadsto>LGC zl_state (T, D, P, {C}, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  and ?\<T> = "flat_inferences_of T - D"
  have "Passive \<sqsupset>L YY"
    by (simp add: DL_Prec_L_def)
  hence "(?\<T>, ?\<N> \<union> {(C, Passive)}) \<leadsto>LGC (?\<T>, ?\<N> \<union> {(C, YY)})"
    using relabel_inactive by blast
  hence "(?\<T>, labeled_formulas_of (P \<union> {C}, {}, A)) \<leadsto>LGC (?\<T>, labeled_formulas_of (P, {C}, A))"
     by (metis PYA_add_passive_formula P0A_add_y_formula)
  thus ?thesis
    by auto
qed

lemma zl_delete_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C)"
  shows "zl_state (T, D, P, {C}, A) \<leadsto>LGC zl_state (T, D, P, {}, A)"
  using assms
proof
  assume c_in: "C \<in> no_labels.Red_F A"
  hence "A \<subseteq> fst ` labeled_formulas_of (P, {}, A)"
    by simp
  hence "C \<in> no_labels.Red_F (fst ` labeled_formulas_of (P, {}, A))"
    by (metis (no_types, lifting) c_in in_mono no_labels.Red_F_of_subset)
  thus ?thesis
    using remove_redundant_no_label by auto
next
  assume "\<exists>C' \<in> A. C' \<preceq>\<cdot> C"
  then obtain C' where c'_in_and_c'_ls_c: "C' \<in> A \<and> C' \<preceq>\<cdot> C"
    by auto
  hence "(C', Active) \<in> labeled_formulas_of (P, {}, A)"
    by auto
  moreover have "YY \<sqsupset>L Active"
    by (simp add: DL_Prec_L_def)
  ultimately show ?thesis
    by (metis P0A_add_y_formula remove_succ_L c'_in_and_c'_ls_c zl_state.simps)
qed

lemma zl_simplify_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F_\<G> (A \<union> {C'})"
  shows "zl_state (T, D, P, {C}, A) \<leadsto>LGC zl_state (T, D, P, {C'}, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  and ?\<M> = "{(C, YY)}"
  and ?\<M>'= "{(C', YY)}"
  have "A \<union> {C'} \<subseteq> fst ` (?\<N> \<union> ?\<M>')"
    by auto
  hence "C \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (verit, ccfv_SIG) assms no_labels.Red_F_of_subset subset_iff)
  hence "(C, YY) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by simp
  hence "?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    by simp
  moreover have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  ultimately have "(flat_inferences_of T - D, labeled_formulas_of (P, {}, A) \<union> {(C, YY)}) \<leadsto>LGC
    (flat_inferences_of T - D, labeled_formulas_of (P, {}, A) \<union> {(C', YY)})"
    using process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  thus ?thesis
    by simp
qed

lemma zl_delete_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C} \<or> C' \<cdot>\<succ> C"
  shows "zl_state (T, D, P, {C}, A \<union> {C'}) \<leadsto>LGC zl_state (T, D, P, {C}, A)"
  using assms
proof
  let ?\<N> = "labeled_formulas_of (P, {C}, A)"
  assume c'_in: "C' \<in> no_labels.Red_F_\<G> {C}"

  have "{C} \<subseteq> fst ` ?\<N>"
    by simp
  hence "C' \<in> no_labels.Red_F_\<G> (fst` ?\<N>)"
    by (metis (no_types, lifting) c'_in insert_Diff insert_subset no_labels.Red_F_of_subset)
  hence "(flat_inferences_of T - D, ?\<N> \<union> {(C', Active)}) \<leadsto>LGC (flat_inferences_of T - D, ?\<N>)"
    using remove_redundant_no_label by auto

  moreover have "?\<N> \<union> {(C', Active)} = labeled_formulas_of (P, {C}, A \<union> {C'})"
    using PYA_add_active_formula by blast
  ultimately have "(flat_inferences_of T - D, labeled_formulas_of (P, {C}, A \<union> {C'})) \<leadsto>LGC
    zl_state (T, D, P, {C}, A)"
    by simp
  thus ?thesis
    by auto
next
  assume "C' \<cdot>\<succ> C"
  moreover have "(C, YY) \<in> labeled_formulas_of (P, {C}, A)"
    by simp
  ultimately show ?thesis
    by (metis remove_succ_F PYA_add_active_formula zl_state.simps)
qed

lemma zl_simplify_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C, C''}"
  shows "zl_state (T, D, P, {C}, A \<union> {C'}) \<leadsto>LGC zl_state (T, D, P \<union> {C''}, {C}, A)"
proof -
  let ?\<M> = "{(C', Active)}"
  and ?\<M>' = "{(C'', Passive)}"
  and ?\<N> = "labeled_formulas_of (P, {C}, A)"
  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by simp
  hence "C' \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (z3) DiffI Diff_eq_empty_iff assms empty_iff no_labels.Red_F_of_subset)
  hence \<M>_included: " ?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  hence "(flat_inferences_of T - D, ?\<N> \<union> ?\<M>) \<leadsto>LGC (flat_inferences_of T - D, ?\<N> \<union> ?\<M>')"
    using \<M>_included process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  moreover have "?\<N> \<union> ?\<M> = labeled_formulas_of(P, {C}, A \<union> {C'})" and
    "?\<N> \<union> ?\<M>' = labeled_formulas_of(P \<union> {C''}, {C}, A)"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma zl_schedule_infer_in_lgc:
  assumes "flat_inferences_of T' = no_labels.Inf_between A {C}"
  shows "zl_state (T, D, P, {C}, A) \<leadsto>LGC
    zl_state (T + T', D - flat_inferences_of T', P, {}, A \<union> {C})"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  have "fst ` active_subset ?\<N> = A"
    by (meson prj_active_subset_of_state)
  hence infs: "flat_inferences_of T' = no_labels.Inf_between (fst ` active_subset ?\<N>) {C}"
    using assms by simp

  have inf: "(flat_inferences_of T - D, ?\<N> \<union> {(C, YY)}) \<leadsto>LGC
    ((flat_inferences_of T - D) \<union> flat_inferences_of T', ?\<N> \<union> {(C, Active)})"
    by (rule step.schedule_infer[of _ _ "flat_inferences_of T'" _ ?\<N> C YY]) (use infs in auto)

  have m_bef: "labeled_formulas_of (P, {C}, A) = ?\<N> \<union> {(C, YY)}"
    by auto
  have t_aft: "flat_inferences_of (T + T') - (D - flat_inferences_of T') =
    (flat_inferences_of T - D) \<union> flat_inferences_of T'"
    by auto
  have m_aft: "labeled_formulas_of (P, {}, A \<union> {C}) = ?\<N> \<union> {(C, Active)}"
    by auto
  show ?thesis
    unfolding zl_state.simps m_bef t_aft m_aft using inf .
qed

lemma zl_delete_orphan_infers_in_lgc:
  assumes inter: "lset \<iota>s \<inter> no_labels.Inf_from A = {}"
  shows "zl_state (T + {#\<iota>s#}, D, P, Y, A) \<leadsto>LGC zl_state (T, D \<union> lset \<iota>s, P, Y, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, Y, A)"

  have inf: "(flat_inferences_of T \<union> lset \<iota>s - D, ?\<N>)
    \<leadsto>LGC (flat_inferences_of T - (D \<union> lset \<iota>s), ?\<N>)"
    by (rule step.delete_orphan_infers[of _ _ "lset \<iota>s - D"])
      (use inter prj_active_subset_of_state in auto)

  have t_bef: "flat_inferences_of (T + {#\<iota>s#}) - D = flat_inferences_of T \<union> lset \<iota>s - D"
    by auto
  show ?thesis
    unfolding zl_state.simps t_bef using inf .
qed

theorem ZL_step_imp_LGC_step: "St \<leadsto>ZL St' \<Longrightarrow> St \<leadsto>LGC St'"
proof (induction rule: ZL.induct)
  case (compute_infer \<iota>0 A C T \<iota>s D P)
  thus ?case
    using zl_compute_infer_in_lgc by auto
next
  case (choose_p T D P C A)
  thus ?case
    using zl_choose_p_in_lgc by auto
next
  case (delete_fwd C A T D P)
  thus ?case
    using zl_delete_fwd_in_lgc by auto
next
  case (simplify_fwd C A C' T D P)
  thus ?case
    using zl_simplify_fwd_in_lgc by blast
next
  case (delete_bwd C' C T D P A)
  thus ?case
    using zl_delete_bwd_in_lgc by blast
next
  case (simplify_bwd C' C C'' T D P A)
  thus ?case
    using zl_simplify_bwd_in_lgc by blast
next
  case (schedule_infer T' A C T D P)
  thus ?case
    using zl_schedule_infer_in_lgc by blast
next
  case (delete_orphan_infers \<iota>s A T D P Y)
  thus ?case
    using zl_delete_orphan_infers_in_lgc by auto
qed


subsection \<open>Completeness\<close>

theorem
  assumes
    zl_chain: "chain (\<leadsto>ZL) Sts" and
    act: "active_subset (snd (lhd Sts)) = {}" and
    pas: "passive_subset (Liminf_llist (lmap snd Sts)) = {}" and
    no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd Sts)" and
    final_sched: "Liminf_llist (lmap fst Sts) = {}"
  shows
    ZL_Liminf_saturated: "saturated (Liminf_llist (lmap snd Sts))" and
    ZL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)" and
    ZL_complete: "B \<in> Bot_F \<Longrightarrow> fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
proof -
  have lgc_chain: "chain (\<leadsto>LGC) Sts"
    using zl_chain ZL_step_imp_LGC_step chain_mono by blast

  show "saturated (Liminf_llist (lmap snd Sts))"
    using act final_sched lgc.fair_implies_Liminf_saturated lgc_chain lgc_fair lgc_to_red
      no_prems_init pas by blast

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B}"

    show ZL_complete_Liminf: "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)"
      by (rule lgc_complete_Liminf[OF lgc_chain act pas no_prems_init final_sched bot unsat])
    thus OL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
      unfolding Liminf_llist_def by auto
  }
qed

end

end
