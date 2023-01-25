(* Title:        DISCOUNT Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>DISCOUNT Loop\<close>

text \<open>The DISCOUNT loop is one of the two best-known given clause procedures. It
is formalized as an instance of the abstract procedure @{text LGC}.\<close>

theory DISCOUNT_Loop
  imports
    Given_Clause_Loops_Util
    More_Given_Clause_Architectures
begin


subsection \<open>Locale\<close>

datatype DL_label =
  Passive | YY | Active

primrec nat_of_DL_label :: "DL_label \<Rightarrow> nat" where
  "nat_of_DL_label Passive = 2"
| "nat_of_DL_label YY = 1"
| "nat_of_DL_label Active = 0"

definition DL_Prec_L :: "DL_label \<Rightarrow> DL_label \<Rightarrow> bool" (infix "\<sqsubset>L" 50) where
  "DL_Prec_L l l' \<longleftrightarrow> nat_of_DL_label l < nat_of_DL_label l'"

locale discount_loop = labeled_lifting_intersection Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q
  Red_F_q \<G>_F_q \<G>_I_q
  "{\<iota>\<^sub>F\<^sub>L :: ('f \<times> 'l) inference. Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F}"
  for
    Bot_F :: "'f set"
    and Inf_F :: "'f inference set"
    and Bot_G :: "'g set"
    and Q :: "'q set"
    and entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool"
    and Inf_G_q :: \<open>'q \<Rightarrow> 'g inference set\<close>
    and Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set"
    and Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set"
    and \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set"
    and \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option"
  + fixes
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50)
  assumes
    equiv_equiv_F: "equivp (\<doteq>)" and
    wf_prec_F: "minimal_element (\<prec>\<cdot>) UNIV" and
    compat_equiv_prec: "C1 \<doteq> D1 \<Longrightarrow> C2 \<doteq> D2 \<Longrightarrow> C1 \<prec>\<cdot> C2 \<Longrightarrow> D1 \<prec>\<cdot> D2" and
    equiv_F_grounding: "q \<in> Q \<Longrightarrow> C1 \<doteq> C2 \<Longrightarrow> \<G>_F_q q C1 \<subseteq> \<G>_F_q q C2" and
    prec_F_grounding: "q \<in> Q \<Longrightarrow> C2 \<prec>\<cdot> C1 \<Longrightarrow> \<G>_F_q q C1 \<subseteq> \<G>_F_q q C2" and
    static_ref_comp: "statically_complete_calculus Bot_F Inf_F (\<Turnstile>\<inter>\<G>)
      no_labels.Red_I_\<G> no_labels.Red_F_\<G>_empty" and
    inf_have_prems: "\<iota>F \<in> Inf_F \<Longrightarrow> prems_of \<iota>F \<noteq> []"
begin

lemma po_on_DL_Prec_L: "po_on (\<sqsubset>L) UNIV"
  by (metis (mono_tags, lifting) DL_Prec_L_def irreflp_onI less_imp_neq order.strict_trans po_on_def
      transp_onI)

lemma wfp_on_DL_Prec_L: "wfp_on (\<sqsubset>L) UNIV"
  unfolding wfp_on_UNIV DL_Prec_L_def by (simp add: wfP_app)

lemma Active_minimal: "l2 \<noteq> Active \<Longrightarrow> Active \<sqsubset>L l2"
  by (cases l2) (auto simp: DL_Prec_L_def)

lemma at_least_two_labels: "\<exists>l2. Active \<sqsubset>L l2"
  using Active_minimal by blast

sublocale lgc?: lazy_given_clause Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F DL_Prec_L Active
  apply unfold_locales
              apply simp
             apply simp
            apply (rule equiv_equiv_F)
          apply (simp add: minimal_element.po wf_prec_F)
          using minimal_element.wf wf_prec_F apply blast
         apply (rule po_on_DL_Prec_L)
        apply (rule wfp_on_DL_Prec_L)
       apply (fact compat_equiv_prec)
      apply (fact equiv_F_grounding)
     apply (fact prec_F_grounding)
    apply (fact Active_minimal)
   apply (rule at_least_two_labels)
  using static_ref_comp statically_complete_calculus.statically_complete apply fastforce
  done

notation lgc.step (infix "\<leadsto>LGC" 50)


subsection \<open>Basic Definitions and Lemmas\<close>

abbreviation c_dot_succ :: "'f \<Rightarrow> 'f \<Rightarrow> bool " (infix "\<cdot>\<succ>" 50) where
  "C \<cdot>\<succ> C' \<equiv> C' \<prec>\<cdot> C"
abbreviation sqsupset :: "DL_label \<Rightarrow> DL_label \<Rightarrow> bool" (infix "\<sqsupset>L" 50) where
  "l \<sqsupset>L l' \<equiv> l' \<sqsubset>L l"

fun labeled_formulas_of :: " 'f set \<times> 'f set \<times> 'f set \<Rightarrow> ('f \<times> DL_label) set " where
  "labeled_formulas_of (P, Y, A) = {(C, Passive) | C. C \<in> P} \<union> {(C, YY) | C. C \<in> Y} \<union>
     {(C, Active) | C. C \<in> A}"

lemma labeled_formulas_of_alt_def:
  "labeled_formulas_of (P, Y, A) =
   (\<lambda>C. (C, Passive)) ` P \<union> (\<lambda>C. (C, YY)) ` Y \<union> (\<lambda>C. (C, Active)) ` A"
  by auto

fun
  state :: "'f inference set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set"
where
  "state (T, P, Y, A) = (T, labeled_formulas_of (P, Y, A))"

lemma state_alt_def:
  "state (T, P, Y, A) = (T, (\<lambda>C. (C, Passive)) ` P \<union> (\<lambda>C. (C, YY)) ` Y \<union> (\<lambda>C. (C, Active)) ` A)"
  by auto

inductive
  DL :: "'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set \<Rightarrow> bool"
  (infix "\<leadsto>DL" 50)
where
  compute_infer: "\<iota> \<in> no_labels.Red_I (A \<union> {C}) \<Longrightarrow>
    state (T \<union> {\<iota>}, P, {}, A) \<leadsto>DL state (T, P, {C}, A)"
| choose_p: "state (T, P \<union> {C}, {}, A) \<leadsto>DL state (T, P, {C}, A)"
| delete_fwd: "C \<in> no_labels.Red_F A \<or> (\<exists>C' \<in> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    state (T, P, {C}, A) \<leadsto>DL state (T, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (A \<union> {C'}) \<Longrightarrow>
    state (T, P, {C}, A) \<leadsto>DL state (T, P, {C'}, A)"
| delete_bwd: "C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    state (T, P, {C}, A \<union> {C'}) \<leadsto>DL state (T, P, {C}, A)"
| simplify_bwd: "C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    state (T, P, {C}, A \<union> {C'}) \<leadsto>DL state (T, P \<union> {C''}, {C}, A)"
| schedule_infer: "T' = no_labels.Inf_between A {C} \<Longrightarrow>
    state (T, P, {C}, A) \<leadsto>DL state (T \<union> T', P, {}, A \<union> {C})"
| delete_orphan_infers: "T' \<inter> no_labels.Inf_from A = {} \<Longrightarrow>
    state (T \<union> T', P, Y, A) \<leadsto>DL state (T, P, Y, A)"

lemma If_f_in_A_then_fl_in_PYA: "C' \<in> A \<Longrightarrow> (C', Active) \<in> labeled_formulas_of (P, Y, A)"
  by auto

lemma PYA_add_passive_formula[simp]:
  "labeled_formulas_of (P, Y, A) \<union> {(C, Passive)} = labeled_formulas_of (P \<union> {C}, Y, A)"
  by auto

lemma P0A_add_y_formula[simp]:
  "labeled_formulas_of (P, {}, A) \<union> {(C, YY)} = labeled_formulas_of (P, {C}, A)"
  by auto

lemma PYA_add_active_formula[simp]:
  "labeled_formulas_of (P, Y, A) \<union> {(C', Active)} = labeled_formulas_of (P, Y, A \<union> {C'})"
  by auto

lemma prj_active_subset_of_state: "fst ` active_subset (labeled_formulas_of (P, Y, A)) = A"
proof -
  have "active_subset {(C, YY) | C. C \<in> Y} = {}" and
       "active_subset {(C, Passive) | C. C \<in> P} = {}"
    using active_subset_def by auto
  moreover have "active_subset {(C, Active) | C. C \<in> A} = {(C, Active) | C. C \<in> A}"
    using active_subset_def by fastforce
  ultimately have "fst ` active_subset (labeled_formulas_of (P, Y, A)) =
    fst ` ({(C, Active) | C. C \<in> A})"
    by simp
  then show ?thesis
    by simp
qed

lemma active_subset_of_setOfFormulasWithLabelDiffActive:
  "l \<noteq> Active \<Longrightarrow> active_subset {(C', l)} = {}"
  using active_subset_def by auto


subsection \<open>Refinement\<close>

lemma dl_compute_infer_in_lgc:
  assumes "\<iota> \<in> no_labels.Red_I_\<G> (A \<union> {C})"
  shows "state (T \<union> {\<iota>}, P, {}, A) \<leadsto>LGC state (T, P, {C}, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  and ?\<M> = "{(C, YY)}"
  have "A \<union> {C} \<subseteq> fst` (labeled_formulas_of (P, {}, A) \<union> {(C, YY)})"
    by auto
  then have "\<iota> \<in> no_labels.Red_I_\<G> (fst` (?\<N> \<union> ?\<M>))"
    by (meson assms no_labels.empty_ord.Red_I_of_subset subsetD)
  also have "active_subset ?\<M> = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto
  then have "(T \<union> {\<iota>}, ?\<N>) \<leadsto>LGC (T, ?\<N> \<union> ?\<M>)"
    using calculation lgc.step.compute_infer by blast
  moreover have "?\<N> \<union> ?\<M> = labeled_formulas_of (P, {C}, A)"
    by simp
  ultimately show ?thesis
    by auto
qed

lemma dl_choose_p_in_lgc: "state (T, P \<union> {C}, {}, A) \<leadsto>LGC state (T, P, {C}, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  have "Passive \<sqsupset>L YY"
    by (simp add: DL_Prec_L_def)
  then have "(T, ?\<N> \<union> {(C, Passive)}) \<leadsto>LGC (T, ?\<N> \<union> {(C, YY)})"
    using relabel_inactive by blast
  then have "(T, labeled_formulas_of (P \<union> {C}, {}, A)) \<leadsto>LGC (T, labeled_formulas_of (P, {C}, A))"
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
  then have "A \<subseteq> fst ` (labeled_formulas_of (P, {}, A))"
    by simp
  then have "C \<in> no_labels.Red_F (fst ` (labeled_formulas_of (P, {}, A)))"
    by (metis (no_types, lifting) c_in in_mono no_labels.Red_F_of_subset)
  then show ?thesis
    using remove_redundant_no_label by auto
next
  assume "\<exists>C'\<in>A. C' \<preceq>\<cdot> C"
  then obtain C' where c'_in_and_c'_ls_c: "C' \<in> A \<and> C' \<preceq>\<cdot> C"
    by auto
  then have "(C', Active) \<in> labeled_formulas_of (P, {}, A)"
    by auto
  then have "YY \<sqsupset>L Active"
    by (simp add: DL_Prec_L_def)
  then show ?thesis
    by (metis c'_in_and_c'_ls_c remove_succ_L state.simps P0A_add_y_formula
        If_f_in_A_then_fl_in_PYA)
qed

lemma dl_simplify_fwd_in_lgc:
  assumes "C \<in> no_labels.Red_F_\<G> (A \<union> {C'})"
  shows "state (T, P, {C}, A) \<leadsto>LGC state (T, P, {C'}, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  and ?\<M> = "{(C, YY)}"
  and ?\<M>'= "{(C', YY)}"
  have "A \<union> {C'} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by auto
  then have "C \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (verit, ccfv_threshold) assms no_labels.Red_F_of_subset subset_iff)
  then have "(C, YY) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by simp
  then have "?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    by simp
  moreover have "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by blast
  ultimately have "(T, labeled_formulas_of (P, {}, A) \<union> {(C, YY)}) \<leadsto>LGC
    (T, labeled_formulas_of (P, {}, A) \<union> {(C', YY)})"
    using process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  then show ?thesis
    by simp
qed

lemma dl_delete_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C} \<or> C' \<cdot>\<succ> C"
  shows "state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC state (T, P, {C}, A)"
  using assms
proof
  let ?\<N> = "labeled_formulas_of (P, {C}, A)"
  assume c'_in: "C' \<in> no_labels.Red_F_\<G> {C}"
  have "{C} \<subseteq> fst ` ?\<N>"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` ?\<N>)"
    by (metis (no_types, lifting) c'_in insert_Diff insert_subset no_labels.Red_F_of_subset)
  then have "(T, ?\<N> \<union> {(C', Active)}) \<leadsto>LGC (T, ?\<N>)"
    using remove_redundant_no_label by auto
  then show ?thesis
    by (metis state.simps PYA_add_active_formula)
next
  assume "C' \<cdot>\<succ> C"
  moreover have "(C, YY) \<in> labeled_formulas_of (P, {C}, A)"
    by simp
  ultimately show ?thesis
    by (metis remove_succ_F state.simps PYA_add_active_formula)
qed

lemma dl_simplify_bwd_in_lgc:
  assumes "C' \<in> no_labels.Red_F_\<G> {C, C''}"
  shows "state (T, P, {C}, A \<union> {C'}) \<leadsto>LGC state (T, P \<union> {C''}, {C}, A)"
proof -
  let ?\<M> = "{(C', Active)}"
  and ?\<M>' = "{(C'', Passive)}"
  and ?\<N> = "labeled_formulas_of (P, {C}, A)"

  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by simp
  then have "C' \<in> no_labels.Red_F_\<G> (fst` (?\<N> \<union> ?\<M>'))"
    by (smt (z3) DiffI Diff_eq_empty_iff assms empty_iff no_labels.Red_F_of_subset)
  then have \<M>_included: "?\<M> \<subseteq> Red_F_\<G> (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  then have "active_subset ?\<M>' = {}"
    using active_subset_def by auto
  then have "(T, ?\<N> \<union> ?\<M>) \<leadsto>LGC (T, ?\<N> \<union> ?\<M>')"
    using \<M>_included process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  moreover have "?\<N> \<union> ?\<M> = labeled_formulas_of(P, {C}, A \<union> {C'})"
  and "?\<N> \<union> ?\<M>' = labeled_formulas_of(P \<union> {C''}, {C}, A)"
    by auto
  ultimately show ?thesis
    by auto
qed

lemma dl_schedule_infer_in_lgc:
  assumes "T' = no_labels.Inf_between A {C}"
  shows "state (T, P, {C}, A) \<leadsto>LGC state (T \<union> T', P, {}, A \<union> {C})"
proof -
  let ?\<N> = "labeled_formulas_of (P, {}, A)"
  have "fst ` (active_subset ?\<N>) = A"
    using prj_active_subset_of_state by blast
  then have "T' = no_labels.Inf_between (fst ` (active_subset ?\<N>)) {C}"
    using assms by auto
  then have "(T, labeled_formulas_of (P, {}, A) \<union> {(C, YY)}) \<leadsto>LGC
    (T \<union> T', labeled_formulas_of (P, {}, A) \<union> {(C, Active)})"
    using lgc.step.schedule_infer by blast
  then show ?thesis
    by (metis state.simps P0A_add_y_formula PYA_add_active_formula)
qed

lemma dl_delete_orphan_infers_in_lgc:
  assumes "T' \<inter> no_labels.Inf_from A = {}"
  shows "state (T \<union> T', P, Y, A) \<leadsto>LGC state (T, P, Y, A)"
proof -
  let ?\<N> = "labeled_formulas_of (P, Y, A)"
  have "fst ` (active_subset ?\<N>) = A"
    using prj_active_subset_of_state by blast
  then have "T' \<inter> no_labels.Inf_from (fst ` (active_subset ?\<N>)) = {}"
    using assms by simp
  then have "(T \<union> T', ?\<N>) \<leadsto>LGC (T, ?\<N>)"
    using lgc.step.delete_orphan_infers by blast
  then show ?thesis
    by simp
qed

theorem DL_step_imp_LGC_step: "T\<M> \<leadsto>DL T\<M>' \<Longrightarrow> T\<M> \<leadsto>LGC T\<M>'"
proof (induction rule: DL.induct)
  case (compute_infer \<iota> A C T P)
  then show ?case
    using dl_compute_infer_in_lgc by blast
next
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
  case (schedule_infer T' A C T P)
  then show ?case
    using dl_schedule_infer_in_lgc by blast
next
  case (delete_orphan_infers T' A T P Y)
  then show ?case
    using dl_delete_orphan_infers_in_lgc by blast
qed


subsection \<open>Completeness\<close>

theorem
  assumes
    dl_chain: "chain (\<leadsto>DL) Sts" and
    act: "active_subset (snd (lhd Sts)) = {}" and
    pas: "passive_subset (Liminf_llist (lmap snd Sts)) = {}" and
    no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd Sts)" and
    final_sched: "Liminf_llist (lmap fst Sts) = {}"
  shows
    DL_Liminf_saturated: "saturated (Liminf_llist (lmap snd Sts))" and
    DL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)" and
    DL_complete: "B \<in> Bot_F \<Longrightarrow> fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
proof -
  have lgc_chain: "chain (\<leadsto>LGC) Sts"
    using dl_chain DL_step_imp_LGC_step chain_mono by blast

  show "saturated (Liminf_llist (lmap snd Sts))"
    using act final_sched lgc.fair_implies_Liminf_saturated lgc_chain lgc_fair lgc_to_red
      no_prems_init pas by blast
  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "fst ` snd (lhd Sts) \<Turnstile>\<inter>\<G> {B}"

    show "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap snd Sts)"
      by (rule lgc_complete_Liminf[OF lgc_chain act pas no_prems_init final_sched bot unsat])
    then show "\<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> snd (lnth Sts i))"
      unfolding Liminf_llist_def by auto
  }
qed

end

end
