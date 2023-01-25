(* Title:        Otter Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Otter Loop\<close>

text \<open>The Otter loop is one of the two best-known given clause procedures. It is
formalized as an instance of the abstract procedure @{text GC}.\<close>

theory Otter_Loop
  imports
    More_Given_Clause_Architectures
    Given_Clause_Loops_Util
begin

datatype OL_label =
  New | XX | Passive | YY | Active

primrec nat_of_OL_label :: "OL_label \<Rightarrow> nat" where
  "nat_of_OL_label New = 4"
| "nat_of_OL_label XX = 3"
| "nat_of_OL_label Passive = 2"
| "nat_of_OL_label YY = 1"
| "nat_of_OL_label Active = 0"

definition OL_Prec_L :: "OL_label \<Rightarrow> OL_label \<Rightarrow> bool" (infix "\<sqsubset>L" 50) where
  "OL_Prec_L l l' \<longleftrightarrow> nat_of_OL_label l < nat_of_OL_label l'"

locale otter_loop = labeled_lifting_intersection Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q
  Red_F_q \<G>_F_q \<G>_I_q
  "{\<iota>\<^sub>F\<^sub>L :: ('f \<times> OL_label) inference. Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F}"
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

lemma po_on_OL_Prec_L: "po_on (\<sqsubset>L) UNIV"
  by (metis (mono_tags, lifting) OL_Prec_L_def irreflp_onI less_imp_neq order.strict_trans po_on_def
      transp_onI)

lemma wfp_on_OL_Prec_L: "wfp_on (\<sqsubset>L) UNIV"
  unfolding wfp_on_UNIV OL_Prec_L_def by (simp add: wfP_app)

lemma Active_minimal: "l2 \<noteq> Active \<Longrightarrow> Active \<sqsubset>L l2"
  by (cases l2) (auto simp: OL_Prec_L_def)

lemma at_least_two_labels: "\<exists>l2. Active \<sqsubset>L l2"
  using Active_minimal by blast

sublocale gc?: given_clause Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F OL_Prec_L Active
  apply unfold_locales
             apply (rule equiv_equiv_F)
            apply (simp add: minimal_element.po wf_prec_F)
           using minimal_element.wf wf_prec_F apply blast
          apply (rule po_on_OL_Prec_L)
         apply (rule wfp_on_OL_Prec_L)
        apply (fact compat_equiv_prec)
       apply (fact equiv_F_grounding)
      apply (fact prec_F_grounding)
     apply (fact Active_minimal)
    apply (rule at_least_two_labels)
   using static_ref_comp statically_complete_calculus.statically_complete apply fastforce
  apply (fact inf_have_prems)
  done

notation gc.step (infix "\<leadsto>GC" 50)


subsection \<open>Basic Definitions and Lemmas\<close>

fun state :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> ('f \<times> OL_label) set" where
  "state (N, X, P, Y, A) =
   {(C, New) | C. C \<in> N} \<union> {(C, XX) | C. C \<in> X} \<union> {(C, Passive) | C. C \<in> P} \<union>
   {(C, YY) | C. C \<in> Y} \<union> {(C, Active) | C. C \<in> A}"

lemma state_alt_def:
  "state (N, X, P, Y, A) =
   (\<lambda>C. (C, New)) ` N \<union> (\<lambda>C. (C, XX)) ` X \<union> (\<lambda>C. (C, Passive)) ` P \<union> (\<lambda>C. (C, YY)) ` Y \<union>
   (\<lambda>C. (C, Active)) ` A"
  by auto

inductive OL :: "('f \<times> OL_label) set \<Rightarrow> ('f \<times> OL_label) set \<Rightarrow> bool" (infix "\<leadsto>OL" 50) where
  choose_n: "C \<notin> N \<Longrightarrow> state (N \<union> {C}, {}, P, {}, A) \<leadsto>OL state (N, {C}, P, {}, A)"
| delete_fwd: "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C' \<in> P \<union> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OL state (N, {}, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OL state (N, {C'}, P, {}, A)"
| delete_bwd_p: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OL state (N, {C}, P, {}, A)"
| simplify_bwd_p: "C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OL state (N \<union> {C''}, {C}, P, {}, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OL state (N, {C}, P, {}, A)"
| simplify_bwd_a: "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OL state (N \<union> {C''}, {C}, P, {}, A)"
| transfer: "state (N, {C}, P, {}, A) \<leadsto>OL state (N, {}, P \<union> {C}, {}, A)"
| choose_p: "C \<notin> P \<Longrightarrow> state ({}, {}, P \<union> {C}, {}, A) \<leadsto>OL state ({}, {}, P, {C}, A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    state ({}, {}, P, {C}, A) \<leadsto>OL state (M, {}, P, {}, A \<union> {C})"

lemma prj_state_union_sets [simp]: "fst ` state (N, X, P, Y, A) = N \<union> X \<union> P \<union> Y \<union> A"
  using prj_fl_set_to_f_set_distr_union prj_labeledN_eq_N by auto

lemma active_subset_of_setOfFormulasWithLabelDiffActive:
  "l \<noteq> Active \<Longrightarrow> active_subset {(C', l)} = {}"
  by (simp add: active_subset_def)

lemma state_add_C_New: "state (N, X, P, Y, A) \<union> {(C, New)} = state (N \<union> {C}, X, P, Y, A)"
  by auto

lemma state_add_C_XX: "state (N, X, P, Y, A) \<union> {(C, XX)} = state (N, X \<union> {C}, P, Y, A)"
  by auto

lemma state_add_C_Passive: "state (N, X, P, Y, A) \<union> {(C, Passive)} = state (N, X, P \<union> {C}, Y, A)"
  by auto

lemma state_add_C_YY: "state (N, X, P, Y, A) \<union> {(C, YY)} = state (N, X, P, Y \<union> {C}, A)"
  by auto

lemma state_add_C_Active: "state (N, X, P, Y, A) \<union> {(C, Active)} = state (N, X, P, Y, A \<union> {C})"
  by auto

lemma prj_ActiveSubset_of_state: "fst ` active_subset (state (N, X, P, Y, A)) = A"
  unfolding active_subset_def by force


subsection \<open>Refinement\<close>

lemma chooseN_in_GC: "state (N \<union> {C}, {}, P, {}, A) \<leadsto>GC state (N, {C}, P, {}, A)"
proof -
  have XX_ls_New: "XX \<sqsubset>L New"
    by (simp add: OL_Prec_L_def)
  hence almost_thesis:
    "state (N, {}, P, {}, A) \<union> {(C, New)} \<leadsto>GC state (N, {}, P, {}, A) \<union> {(C, XX)}"
    using relabel_inactive by blast
  have rewrite_left: "state (N, {}, P, {}, A) \<union> {(C, New)} = state (N \<union> {C}, {}, P, {}, A)"
    using state_add_C_New by blast
  moreover have rewrite_right: "state (N, {}, P, {}, A) \<union> {(C, XX)} =  state (N, {C}, P, {}, A)"
    using state_add_C_XX by auto
  ultimately show ?thesis
    using almost_thesis rewrite_left rewrite_right by simp
qed

lemma deleteFwd_in_GC:
  assumes "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C' \<in> P \<union> A. C' \<preceq>\<cdot> C)"
  shows "state (N, {C}, P, {}, A) \<leadsto>GC state (N, {}, P, {}, A)"
  using assms
proof
  assume c_in_redf_PA: "C \<in> no_labels.Red_F (P \<union> A)"
  have "P \<union> A \<subseteq> N \<union> {} \<union> P \<union> {} \<union> A" by auto
  then have "no_labels.Red_F (P \<union> A) \<subseteq> no_labels.Red_F (N \<union> {} \<union> P \<union> {} \<union> A)"
    using no_labels.Red_F_of_subset by simp
  then have c_in_redf_NPA: "C \<in> no_labels.Red_F (N \<union> {} \<union> P \<union> {} \<union> A)"
    using c_in_redf_PA by auto
  have NPA_eq_prj_state_NPA: "N \<union> {} \<union> P \<union> {} \<union> A = fst ` state (N, {}, P, {}, A)"
    using prj_state_union_sets by simp
  have "C \<in> no_labels.Red_F (fst ` state (N, {}, P, {}, A))"
    using c_in_redf_NPA NPA_eq_prj_state_NPA by fastforce
  then show ?thesis
    using remove_redundant_no_label by auto
next
  assume "\<exists>C' \<in> P \<union> A. C' \<preceq>\<cdot> C"
  then obtain C' where "C' \<in> P \<union> A" and c'_le_c: "C' \<preceq>\<cdot> C"
    by auto
  then have "C' \<in> P \<or> C' \<in> A"
    by blast
  then show ?thesis
  proof
    assume "C' \<in> P"
    then have c'_Passive_in: "(C', Passive) \<in> state (N, {}, P, {}, A)"
      by simp
    have "Passive \<sqsubset>L XX"
      by (simp add: OL_Prec_L_def)
    then have "state (N, {}, P, {}, A) \<union> {(C, XX)} \<leadsto>GC state (N, {}, P, {}, A)"
      using remove_succ_L c'_le_c c'_Passive_in by blast
    then show ?thesis
      by auto
  next
    assume "C' \<in> A"
    then have c'_Active_in_state_NPA: "(C', Active) \<in> state (N, {}, P, {}, A)"
      by simp
    also have Active_ls_x: "Active \<sqsubset>L XX"
      using Active_minimal by simp
    then  have " state (N, {}, P, {}, A) \<union> {(C, XX)} \<leadsto>GC state (N, {}, P, {}, A) "
      using remove_succ_L c'_le_c Active_ls_x c'_Active_in_state_NPA by blast
    then show ?thesis
      by auto
  qed
qed

lemma simplifyFwd_in_GC:
  "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
   state (N, {C}, P, {}, A) \<leadsto>GC state (N, {C'}, P, {}, A)"
proof -
  assume c_in: "C \<in> no_labels.Red_F (P \<union> A \<union> {C'})"
  let ?\<N> = "state (N, {}, P, {}, A)"
  and ?\<M> = "{(C, XX)}" and ?\<M>' = "{(C', XX)}"

  have "P \<union> A \<union> {C'} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by auto
  then have "no_labels.Red_F (P \<union> A \<union> {C'}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using no_labels.Red_F_of_subset by auto
  then have "C \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using c_in by auto
  then have c_x_in: "(C, XX) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  then have "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')"
    by auto
  then have active_subset_of_m': "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto
  show ?thesis
    using c_x_in active_subset_of_m' process[of _ _ "?\<M>" _ "?\<M>'"] by auto
qed

lemma deleteBwdP_in_GC:
  assumes "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C'"
  shows  "state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>GC state (N, {C}, P, {}, A)"
  using assms
  proof
    let ?\<N> = "state (N, {C}, P, {}, A)"
    assume c_ls_c': " C \<prec>\<cdot> C' "

    have "(C, XX) \<in> state (N, {C}, P, {}, A)"
      by simp
    then have "?\<N> \<union> {(C', Passive)} \<leadsto>GC ?\<N>"
      using c_ls_c' remove_succ_F by blast
    also have "?\<N> \<union> {(C', Passive)} = state (N, {C}, P \<union> {C'}, {}, A)"
      by auto
    finally show ?thesis
      by auto
  next
    let ?\<N> = "state (N, {C}, P, {}, A)"
    assume c'_in_redf_c: " C' \<in> no_labels.Red_F_\<G> {C} "
    have " {C} \<subseteq> fst` ?\<N>" by auto
    then have " no_labels.Red_F {C} \<subseteq> no_labels.Red_F (fst` ?\<N>) "
      using no_labels.Red_F_of_subset by auto
    then have " C' \<in> no_labels.Red_F (fst` ?\<N>) "
      using c'_in_redf_c by blast
    then have "?\<N> \<union> {(C', Passive)} \<leadsto>GC ?\<N>"
      using remove_redundant_no_label by blast
    then show ?thesis
      by (metis state_add_C_Passive)
  qed

lemma simplifyBwdP_in_GC:
  assumes "C' \<in> no_labels.Red_F {C, C''}"
  shows "state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>GC state (N \<union> {C''}, {C}, P, {}, A)"
proof -
  let ?\<N> = "state (N, {C}, P, {}, A)"
  and ?\<M> = "{(C', Passive)}"
  and ?\<M>' = "{(C'', New)}"

  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by (smt (z3) Un_commute Un_empty_left Un_insert_right insert_absorb2
        subset_Un_eq state_add_C_New prj_state_union_sets)
  then have "no_labels.Red_F {C, C''} \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using no_labels.Red_F_of_subset by auto
  then have "C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using assms by auto
  then have "(C', Passive) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  then have \<M>_in_redf: "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')" by auto

  have active_subset_\<M>': "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto

  have "?\<N> \<union> ?\<M> \<leadsto>GC ?\<N> \<union> ?\<M>'"
    using \<M>_in_redf active_subset_\<M>' process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  also have "?\<N> \<union> {(C', Passive)} = state (N, {C}, P \<union> {C'}, {}, A)"
    by force
  also have "?\<N> \<union> {(C'', New)} = state (N \<union> {C''}, {C}, P, {}, A)"
    using state_add_C_New by blast
  finally show ?thesis
    by auto
qed

lemma deleteBwdA_in_GC:
  assumes "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' "
  shows "state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>GC state (N, {C}, P, {}, A) "
  using assms
proof
    let ?\<N> = "state (N, {C}, P, {}, A)"
    assume c_ls_c': " C \<prec>\<cdot> C' "

    have " (C, XX) \<in> state (N, {C}, P, {}, A) "
      by simp
    then have "?\<N> \<union> {(C', Active)} \<leadsto>GC ?\<N>"
      using c_ls_c' remove_succ_F by blast
    also have "?\<N> \<union> {(C', Active)} = state (N, {C}, P, {}, A \<union> {C'})"
      by auto
    finally show "state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>GC state (N, {C}, P, {}, A)"
      by auto
next
    let ?\<N> = "state (N, {C}, P, {}, A)"
    assume c'_in_redf_c: " C' \<in> no_labels.Red_F_\<G> {C} "

    have " {C} \<subseteq> fst` ?\<N> "
      by (metis Un_commute Un_upper2 le_supI2 prj_state_union_sets)
    then have " no_labels.Red_F {C} \<subseteq> no_labels.Red_F (fst` ?\<N>) "
      using no_labels.Red_F_of_subset by auto
    then have " C' \<in> no_labels.Red_F (fst` ?\<N>) "
      using c'_in_redf_c by blast
    then have "?\<N> \<union> {(C', Active)} \<leadsto>GC ?\<N>"
      using remove_redundant_no_label by auto
    then show ?thesis
      by (metis state_add_C_Active)
qed

lemma simplifyBwdA_in_GC:
  assumes "C' \<in> no_labels.Red_F {C, C''}"
  shows "state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>GC state (N \<union> {C''}, {C}, P, {}, A)"
proof -
  let ?\<N> = "state (N, {C}, P, {}, A)" and ?\<M> = "{(C', Active)}" and ?\<M>' = "{(C'', New)}"

  have " {C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>') "
    by simp
  then have " no_labels.Red_F {C, C''} \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
    using no_labels.Red_F_of_subset by auto
  then have " C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
    using assms by auto
  then have " (C', Active) \<in> Red_F (?\<N> \<union> ?\<M>') "
    using no_labels_Red_F_imp_Red_F by auto
  then have \<M>_included: " ?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>') "
    by auto

  have "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto
  then have "state (N, {C}, P, {}, A) \<union> {(C', Active)} \<leadsto>GC state (N, {C}, P, {}, A) \<union> {(C'', New)}"
    using \<M>_included process[where ?M="?\<M>" and ?M'="?\<M>'"] by auto
  then show ?thesis
    by (metis state_add_C_New state_add_C_Active)
qed

lemma transfer_in_GC: "state (N, {C}, P, {}, A) \<leadsto>GC state (N, {}, P \<union> {C}, {}, A)"
proof -
  let ?\<N> = "state (N, {}, P, {}, A)"

  have "Passive \<sqsubset>L XX"
    by (simp add: OL_Prec_L_def)
  then have "?\<N> \<union> {(C, XX)} \<leadsto>GC ?\<N> \<union> {(C, Passive)}"
    using relabel_inactive by auto
  then show ?thesis
    by (metis sup_bot_left state_add_C_XX state_add_C_Passive)
qed

lemma chooseP_in_GC: "state ({}, {}, P \<union> {C}, {}, A) \<leadsto>GC state ({}, {}, P, {C}, A)"
proof -
  let ?\<N> = "state ({}, {}, P, {}, A)"

  have "YY \<sqsubset>L Passive"
    by (simp add: OL_Prec_L_def)
  moreover have "YY \<noteq> Active"
    by simp
  ultimately have "?\<N> \<union> {(C, Passive)} \<leadsto>GC ?\<N> \<union> {(C, YY)}"
    using relabel_inactive by auto
  then show ?thesis
    by (metis sup_bot_left state_add_C_Passive state_add_C_YY)
qed

lemma infer_in_GC:
  assumes "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M)"
  shows "state ({}, {}, P, {C}, A) \<leadsto>GC state (M, {}, P, {}, A \<union> {C})"
proof -
  let ?\<M> = "{(C', New) | C'. C' \<in> M}"
  let ?\<N> = "state ({}, {}, P, {}, A)"

  have active_subset_of_\<M>: "active_subset ?\<M> = {}"
    using active_subset_def by auto

  have "A \<union> {C} \<union> M \<subseteq> (fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>)"
    by fastforce
  then have "no_labels.Red_I (A \<union> {C} \<union> M) \<subseteq> no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
    using no_labels.empty_ord.Red_I_of_subset by auto
  moreover have "fst` (active_subset ?\<N>) = A"
    using prj_ActiveSubset_of_state by blast
  ultimately have "no_labels.Inf_between (fst` (active_subset ?\<N>)) {C} \<subseteq>
    no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
    using assms by auto

  then have "?\<N> \<union> {(C, YY)} \<leadsto>GC ?\<N> \<union> {(C, Active)} \<union> ?\<M>"
    using active_subset_of_\<M> prj_fl_set_to_f_set_distr_union step.infer by force
  also have "?\<N> \<union> {(C, YY)} = state ({}, {}, P, {C}, A)"
    by simp
  also have "?\<N> \<union> {(C, Active)} \<union> ?\<M> = state (M, {}, P, {}, A \<union> {C})"
    by force
  finally show ?thesis
    by simp
qed

theorem OL_step_imp_GC_step: "M \<leadsto>OL M' \<Longrightarrow> M \<leadsto>GC M'"
proof (induction rule: OL.induct)
  case (choose_n N C P A)
  then show ?case
    using chooseN_in_GC by auto
next
  case (delete_fwd C P A N)
  then show ?case
    using deleteFwd_in_GC by auto
next
  case (simplify_fwd C P A C' N)
  then show ?case
    using simplifyFwd_in_GC by auto
next
  case (delete_bwd_p C' C N P A)
  then show ?case
    using deleteBwdP_in_GC by auto
next
  case (simplify_bwd_p C' C C'' N P A)
  then show ?case
    using simplifyBwdP_in_GC by auto
next
  case (delete_bwd_a C' C N P A)
  then show ?case
    using deleteBwdA_in_GC by auto
next
  case (simplify_bwd_a C' C N P A C'')
  then show ?case
    using simplifyBwdA_in_GC by blast
next
  case (transfer N C P A)
  then show ?case
    using transfer_in_GC by auto
next
  case (choose_p P C A)
  then show ?case
    using chooseP_in_GC by auto
next
  case (infer A C M P)
  then show ?case
    using infer_in_GC by auto
qed


subsection \<open>Completeness\<close>

theorem
  assumes
    ol_chain: "chain (\<leadsto>OL) Sts" and
    act: "active_subset (lhd Sts) = {}" and
    pas: "passive_subset (Liminf_llist Sts) = {}"
  shows
    OL_Liminf_saturated: "saturated (Liminf_llist Sts)" and
    OL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fst ` lhd Sts \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist Sts" and
    OL_complete: "B \<in> Bot_F \<Longrightarrow> fst ` lhd Sts \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>BL \<in> Bot_FL. BL \<in> lnth Sts i)"
proof -
  have gc_chain: "chain (\<leadsto>GC) Sts"
    using ol_chain OL_step_imp_GC_step chain_mono by blast

  show "saturated (Liminf_llist Sts)"
    using assms(2) gc.fair_implies_Liminf_saturated gc_chain gc_fair gc_to_red pas by blast

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
