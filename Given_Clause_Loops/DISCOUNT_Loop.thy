(* Title:        DISCOUNT Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>DISCOUNT Loop\<close>

theory DISCOUNT_Loop
  imports More_Lazy_Given_Clause
begin

locale discount_loop =
  lazy_given_clause Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q
    Red_F_q \<G>_F_q \<G>_I_q Inf_FL Equiv_F Prec_F Prec_L active
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Inf_G_q :: \<open>'q \<Rightarrow> 'g inference set\<close> and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close> and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) and
    Prec_L :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<sqsubset>L" 50) and
    active :: "'l" +
  fixes passive y :: 'l
  assumes
    (* there are exactly 3 labels and there is an order *)
    labels: "\<forall>l::'l. l \<in> {passive, y, active}" and
    order_on_labels: "active \<sqsubset>L y \<and> y \<sqsubset>L passive \<and> active \<sqsubset>L passive"
begin


subsection \<open>definition, abbreviation, type and fun\<close>

abbreviation c_dot_succ :: " 'f \<Rightarrow> 'f \<Rightarrow> bool " (infix "\<cdot>\<succ>" 50) where " C \<cdot>\<succ> C' \<equiv> C' \<prec>\<cdot> C"
abbreviation sqsupset :: " 'l \<Rightarrow> 'l \<Rightarrow> bool " (infix "\<sqsupset>L" 50) where " l \<sqsupset>L l' \<equiv> l' \<sqsubset>L l"

fun formulas_of :: " 'f set \<times> 'f set \<times> 'f set \<Rightarrow> ('f \<times> 'l) set " where
  "formulas_of (P, Y, A) = {(C, passive) | C. C \<in> P} \<union>
                           {(C, y) | C. C \<in> Y} \<union>
                           {(C, active) | C. C \<in> A}"

fun state :: " 'f inference set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f inference set \<times> ('f \<times> 'l) set "
  where "state (T, P, Y, A) = (T, formulas_of (P, Y, A))"

inductive DL :: "('f inference set) \<times> ('f \<times> 'l) set \<Rightarrow>
                             ('f inference set) \<times> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>DL" 50) where
  choose_p: "state ( T, P \<union> {C}, \<emptyset>, A) \<leadsto>DL state ( T, P, {C}, A)"
| delete_fwd: "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
  state ( T, P, {C}, A) \<leadsto>DL state ( T, P, \<emptyset>, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (A \<union> {C'}) \<Longrightarrow>
  state ( T, P, {C}, A) \<leadsto>DL state ( T, P, {C'}, A)"
| delete_bwd: "C' \<in> no_labels.Red_F ({C}) \<or> C' \<cdot>\<succ> C \<Longrightarrow>
  state ( T, P, {C}, A \<union> {C'}) \<leadsto>DL state ( T, P, {C}, A)"
| simplify_bwd: "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
  state ( T, P, {C}, A \<union> {C'}) \<leadsto>DL state ( T, P \<union> {C''}, {C}, A)"
| compute_Infer: "\<iota> \<in> no_labels.Red_I (A \<union> {C}) \<Longrightarrow>
  state ( T \<union> {\<iota>}, P, \<emptyset>, A) \<leadsto>DL state ( T, P, {C}, A)"
| schedule_Infer: "T' = (no_labels.Inf_between A {C}) \<Longrightarrow>
  state ( T, P, {C}, A) \<leadsto>DL state ( T \<union> T', P, \<emptyset>, A \<union> {C})"
| delete_Orphans: "(T' \<inter> no_labels.Inf_from A) = \<emptyset> \<Longrightarrow>
  state ( T \<union> T', P, Y, A) \<leadsto>DL state ( T, P, Y, A)"


subsection \<open>Auxiliary Lemmas\<close>

lemma labels_distinct: " y \<noteq> active \<and> passive \<noteq> active "
proof
  show "y \<noteq> active"
  proof
    assume y_eq_active: " y = active "
    then have "y \<sqsubset>L active"
      using order_on_labels by simp
    then show "False"
      by (metis UNIV_I y_eq_active minimal_element.minimal wf_prec_L)
  qed
next
  show "passive \<noteq> active"
  proof
    assume passive_eq_active: "passive = active "
    then have "passive \<sqsubset>L active"
      using order_on_labels by simp
    then show "False"
      by (metis UNIV_I passive_eq_active minimal_element.minimal wf_prec_L)
  qed
qed

lemma If_f_in_A_then_fl_in_PYA: "C' \<in> A \<Longrightarrow> (C', active) \<in> formulas_of (P, Y, A)"
  by auto

lemma PYA_add_passive_formula [simp]:
  "formulas_of (P, Y, A) \<union> {(C, passive)} = formulas_of (P \<union> {C}, Y, A)"
  by auto

lemma P0A_add_y_formula [simp]: "formulas_of (P, {}, A) \<union> {(C, y)} = formulas_of (P, {C}, A)"
  by auto

lemma PYA_add_active_formula [simp]:
  "formulas_of (P, Y, A) \<union> {(C', active)} = formulas_of (P, Y, A\<union>{C'})"
  by auto

lemma prj_active_subset_of_state: "fst ` (active_subset (formulas_of (P, Y, A))) = A"
proof -
  have "active_subset {(C, y)|C. C \<in> Y} = \<emptyset>" and
       "active_subset {(C, passive)|C. C \<in> P} = \<emptyset>"
    using active_subset_def labels_distinct by auto
  moreover have "active_subset {(C, active)|C. C \<in> A} = {(C, active)|C. C \<in> A}"
    using active_subset_def by fastforce
  ultimately have "fst ` (active_subset (formulas_of (P, Y, A))) = fst ` ({(C, active)|C. C \<in> A})"
    by simp
  then show ?thesis
    by simp
qed

lemma active_subset_of_setOfFormulasWithLabelDiffActive:
  "(l::'l) \<noteq> active \<Longrightarrow> active_subset {(C', l)} = \<emptyset>"
  using active_subset_def labels_distinct by auto

lemma dl_choose_p_in_lgc: "state (T, P \<union> {C}, {}, A) \<leadsto>LGC state (T, P, {C}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  have "passive \<sqsupset>L y"
    by (simp add: order_on_labels)
  moreover have "y \<noteq> active"
    using labels_distinct by simp
  ultimately have "(T, ?\<N> \<union> {(C, passive)}) \<leadsto>LGC (T, ?\<N> \<union> {(C, y)})"
    using P5' by blast
  then have "(T, formulas_of (P \<union> {C}, {}, A)) \<leadsto>LGC (T, formulas_of (P, {C}, A))"
     by (metis PYA_add_passive_formula P0A_add_y_formula)
  then show ?thesis
    by auto
qed

lemma dl_delete_fwd_in_lgc:
  assumes " (C \<in> no_labels.Red_F A) \<or> (\<exists>C'\<in>A. C' \<preceq>\<cdot> C)"
  shows "state (T, P, {C}, A) \<leadsto>LGC state (T, P, {}, A)"
  using assms
proof
  assume c_in: "C \<in> no_labels.Red_F A"
  then have "A \<subseteq> fst ` (formulas_of (P, {}, A))"
    by simp
  then have "C \<in> no_labels.Red_F (fst ` (formulas_of (P, {}, A)))"
    by (metis (no_types, lifting) c_in in_mono no_labels.Red_F_of_subset)
  then show ?thesis
    using P1' by auto
next
  assume "\<exists>C'\<in>A. C' \<preceq>\<cdot> C"
  then obtain C' where c'_in_and_c'_ls_c: "C' \<in> A \<and> C' \<preceq>\<cdot> C"
    by auto
  then have "(C', active) \<in> formulas_of (P, {}, A)"
    by auto
  then have "y \<sqsupset>L active" using order_on_labels
    by simp
  then show ?thesis
     by (metis c'_in_and_c'_ls_c P4' state.simps P0A_add_y_formula If_f_in_A_then_fl_in_PYA)
qed

lemma dl_simplify_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F_\<G> (A \<union> {C'})"
  shows "state (T, P, {C}, A) \<leadsto>LGC state (T, P, {C'}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  and ?\<M> = "{(C, y)}"
  and ?\<M>'= "{(C', y)}"
  have "A \<union> {C'} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by auto
  then have "C \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (verit, ccfv_threshold) assms no_labels.Red_F_of_subset subset_iff)
  then have "(C, y) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using lemma59point1 by simp
  then have "?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    by simp
  moreover have "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive labels_distinct by blast
  ultimately have "(T, formulas_of (P, {}, A) \<union> {(C, y)}) \<leadsto>LGC
                    (T, formulas_of (P, {}, A) \<union> {(C', y)})"
    using process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  then show ?thesis
    by simp
qed

lemma dl_delete_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C} \<or> C' \<cdot>\<succ> C"
  shows "state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC state (T, P, {C}, A)"
  using assms
proof
  let ?\<N> = "formulas_of (P, {C}, A)"
  assume c'_in: "C' \<in> no_labels.Red_F_\<G> {C}"
  have "{C} \<subseteq> fst ` ?\<N>"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` ?\<N>)"
    by (metis (no_types, lifting) c'_in insert_Diff insert_subset no_labels.Red_F_of_subset)
  then have "(T, ?\<N> \<union> {(C', active)}) \<leadsto>LGC (T, ?\<N>)"
    using P1' by auto
  then show ?thesis
    by (metis state.simps PYA_add_active_formula)
next
  assume "C' \<cdot>\<succ> C"
  moreover have "(C, y) \<in> formulas_of (P, {C}, A)"
    by simp
  ultimately show ?thesis
    by (metis P3' state.simps PYA_add_active_formula)
qed

lemma dl_simplify_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C, C''}"
  shows "state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC state (T, P \<union> {C''}, {C}, A)"
proof -
  let ?\<M> = "{(C', active)}"
  and ?\<M>' = "{(C'', passive)}"
  and ?\<N> = "formulas_of (P, {C}, A)"
  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (z3) DiffI Diff_eq_empty_iff assms empty_iff no_labels.Red_F_of_subset)
  then have \<M>_included: " ?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    using lemma59point1 by auto
  have "passive \<noteq> active"
    by (simp add: labels_distinct)
  then have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  then have "(T, ?\<N> \<union> ?\<M>) \<leadsto>LGC (T, ?\<N> \<union> ?\<M>')"
    using \<M>_included process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  moreover have "?\<N> \<union> ?\<M> = formulas_of(P, {C}, A \<union> {C'})"
  and "?\<N> \<union> ?\<M>' = formulas_of(P \<union> {C''}, {C}, A)"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma dl_compute_infer_in_lgc:
  assumes "\<iota> \<in> no_labels.Red_I_\<G> (A \<union> {C})"
  shows "state (T \<union> {\<iota>}, P, {}, A) \<leadsto>LGC state (T, P, {C}, A)"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  and ?\<M> = "{(C, y)}"
  have "A \<union> {C} \<subseteq> fst` (formulas_of (P, {}, A) \<union> {(C, y)})"
    by auto
  then have "\<iota> \<in> no_labels.Red_I_\<G> (fst` (?\<N> \<union> ?\<M>))"
    by (meson assms no_labels.empty_ord.Red_I_of_subset subsetD)
  also have "active_subset ?\<M> = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive labels_distinct by auto
  then have "(T \<union> {\<iota>}, ?\<N>) \<leadsto>LGC (T, ?\<N> \<union> ?\<M>)"
    using calculation compute_infer by blast
  moreover have "?\<N> \<union> ?\<M> = formulas_of(P, {C}, A)"
    by simp
  ultimately show ?thesis
    by auto
qed

lemma dl_schedule_infer_in_lgc:
  assumes "T' = no_labels.Inf_between A {C}"
  shows "state (T, P, {C}, A) \<leadsto>LGC state (T \<union> T', P, {}, A \<union> {C})"
proof -
  let ?\<N> = "formulas_of (P, {}, A)"
  have "fst ` (active_subset ?\<N>) = A"
    using prj_active_subset_of_state by blast
  then have "T' = no_labels.Inf_between (fst ` (active_subset ?\<N>)) {C}"
    using assms by auto
  also have "y \<noteq> active" using labels_distinct
    by simp
  then have "(T, formulas_of (P, {}, A) \<union> {(C, y)}) \<leadsto>LGC
             (T \<union> T', formulas_of (P, {}, A) \<union> {(C, active)})"
    using calculation schedule_infer by blast
  then show ?thesis
    by (metis state.simps P0A_add_y_formula PYA_add_active_formula)
qed

lemma dl_delete_orphans_in_lgc:
  assumes "T' \<inter> no_labels.Inf_from A = {}"
  shows "state (T \<union> T', P, Y, A) \<leadsto>LGC state (T, P, Y, A)"
proof -
  let ?\<N> = "formulas_of (P, Y, A)"
  have "fst ` (active_subset ?\<N>) = A"
    using prj_active_subset_of_state by blast
  then have "T' \<inter> no_labels.Inf_from (fst ` (active_subset ?\<N>)) = {}"
    using assms by simp
  then have "(T \<union> T', ?\<N>) \<leadsto>LGC (T, ?\<N>)"
    using delete_orphans by blast
  then show ?thesis
    by simp
qed

theorem inclusion_ol_in_gc: "(T, \<M>) \<leadsto>DL (T, \<M>') \<Longrightarrow> (T, \<M>) \<leadsto>LGC (T, \<M>') "
proof (induction rule: DL.induct)
  case (choose_p T P C A)
  then show ?case
    using dl_choose_p_in_lgc by auto
next
  case (delete_fwd C A T P)
  then show ?case
    using dl_delete_fwd_in_lgc by auto
next
  case (simplify_fwd C A C' T P)
  then show ?case
    using dl_simplify_fwd_in_lgc by blast
next
  case (delete_bwd C' C T P A)
  then show ?case
    using dl_delete_bwd_in_lgc by blast
next
  case (simplify_bwd C' C C'' T P A)
  then show ?case
    using dl_simplify_bwd_in_lgc by blast
next
  case (compute_Infer \<iota> A C T P)
  then show ?case
    using dl_compute_infer_in_lgc by blast
next
  case (schedule_Infer T' A C T P)
  then show ?case
    using dl_schedule_infer_in_lgc by blast
next
  case (delete_Orphans T' A T P Y)
  then show ?case
    using dl_delete_orphans_in_lgc by blast
qed

end

end
