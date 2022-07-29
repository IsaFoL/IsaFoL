(* Title:        Otter Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>Otter Loop\<close>

theory Otter_Loop
  imports More_Given_Clause_Architectures
begin

locale otter_loop =
  given_clause Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
    Prec_L active
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
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) and
    Prec_L :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<sqsubset>L" 50) and
    active :: "'l" +
  fixes new xx passive yy :: 'l
  assumes
    (* There are exactly 5 labels and there's an order on labels*)
    five_labels: "\<forall>l. l \<in> {new, xx, passive, yy, active}" and
    order_on_labels: "active \<sqsubset>L yy \<and> yy \<sqsubset>L passive \<and> passive \<sqsubset>L xx \<and> xx \<sqsubset>L new" and
    order_on_labels_trans: "l1 \<sqsubset>L l2 \<Longrightarrow> l2 \<sqsubset>L l3 \<Longrightarrow> l1 \<sqsubset>L l3"
begin


subsection \<open>Definition and Lemmas\<close>

fun state :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> ('f \<times> 'l) set" where
  "state (N, X, P, Y, A) =
   {(C, new) | C. C \<in> N} \<union>
   {(C, xx) | C. C \<in> X} \<union>
   {(C, passive) | C. C \<in> P} \<union>
   {(C, yy) | C. C \<in> Y} \<union>
   {(C, active) | C. C \<in> A}"

inductive OL :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>OL" 50) where
  choose_n: "C \<notin> N \<Longrightarrow> state (N \<union> {C}, {}, P, {}, A) \<leadsto>OL state (N, {C}, P, {}, A)"
| delete_fwd: "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C' \<in> P \<union> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OL state (N, {}, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OL state (N, {C'}, P, {}, A)"
| delete_bwd_p: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OL state(N, {C}, P, {}, A)"
| simplify_bwd_p: "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OL state (N \<union> {C''}, {C}, P, {}, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OL state (N, {C}, P, {}, A)"
| simplify_bwd_a: "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OL state (N \<union> {C''}, {C}, P, {}, A)"
| transfer: "state (N, {C}, P, {}, A) \<leadsto>OL state (N, {}, P \<union> {C}, {}, A)"
| choose_p: "C \<notin> P \<Longrightarrow> state ({}, {}, P \<union> {C}, {}, A) \<leadsto>OL state ({}, {}, P, {C}, A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    state ({}, {}, P, {C}, A) \<leadsto>OL state  (M, {}, P, {}, A \<union> {C})"

lemma labels_distinct:
  assumes "l \<in> {xx, yy, passive, new}"
  shows "l \<noteq> active"
proof
  assume l_active: "l = active"
  then have "active \<sqsubset>L l"
    by (metis assms empty_iff insert_iff order_on_labels order_on_labels_trans)
  then have "l \<sqsubset>L active"
    using l_active by auto
  then show "False"
    by (metis UNIV_I l_active minimal_element.minimal wf_prec_L)
qed

lemma prj_state_union_sets [simp]: "fst ` state (N, X, P, Y, A) = N \<union> X \<union> P \<union> Y \<union> A"
  using prj_fl_set_to_f_set_distr_union prj_labeledN_eq_N by auto

lemma active_subset_of_setOfFormulasWithLabelDiffActive:
  "l \<noteq> active \<Longrightarrow> active_subset {(C', l)} = {}"
  using active_subset_def labels_distinct by auto

lemma state_add_C_new: "state (N, X, P, Y, A) \<union> {(C, new)} = state (N \<union> {C}, X, P, Y, A)"
  by auto

lemma state_add_C_xx: "state (N, X, P, Y, A) \<union> {(C, xx)} = state (N, X \<union> {C}, P, Y, A)"
  by auto

lemma state_add_C_passive:
  "state (N, X, P, Y, A) \<union> {(C, passive)} = state (N, X, P \<union> {C}, Y, A)"
  by auto

lemma state_add_C_yy: "state (N, X, P, Y, A) \<union> {(C, yy)} = state (N, X, P, Y \<union> {C}, A)"
  by auto

lemma state_add_C_active: "state (N, X, P, Y, A) \<union> {(C, active)} = state (N, X, P, Y, A \<union> {C})"
  by auto

lemma prj_activeSubset_of_state: "fst ` active_subset (state (N, X, P, Y, A)) = A"
proof -
  have "active_subset {(C, new) | C. C \<in> N} = {}"
    using labels_distinct active_subset_def by auto
  moreover have "active_subset {(C, yy) | C. C \<in> Y} = {}"
    using labels_distinct active_subset_def by auto
  moreover have "active_subset {(C, passive) | C. C \<in> P} = {}"
    using labels_distinct active_subset_def by auto
  moreover have "active_subset {(C, xx) | C. C \<in> X} = {}"
    using labels_distinct active_subset_def by auto
  moreover have "active_subset {(C, active) | C. C \<in> A} = {(C, active) | C. C \<in> A}"
    using active_subset_def by auto
  ultimately have "fst ` active_subset (state (N, X, P, Y, A)) = fst ` {(C, active) | C. C \<in> A}"
    by auto
  then show ?thesis
    by simp
qed


subsection \<open>Refinement\<close>

lemma chooseN_in_GC: "state (N \<union> {C}, {}, P, {}, A) \<leadsto>GC state (N, {C}, P, {}, A)"
proof -
  have xx_ls_new: "xx \<sqsubset>L new"
    using order_on_labels by auto
  moreover have x_neq_active: "xx \<noteq> active"
    using labels_distinct by simp
  ultimately have almost_thesis:
    "state (N, {}, P, {}, A) \<union> {(C, new)} \<leadsto>GC state (N, {}, P, {}, A) \<union> {(C, xx)}"
    using relabel_inactive by auto
  have rewrite_left: "state (N, {}, P, {}, A) \<union> {(C, new)} = state (N \<union> {C}, {}, P, {}, A)"
    using state_add_C_new by blast
  moreover have rewrite_right: "state (N, {}, P, {}, A) \<union> {(C, xx)} =  state (N, {C}, P, {}, A)"
    using state_add_C_xx by auto
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
    then have c'_passive_in: "(C', passive) \<in> state (N, {}, P, {}, A)"
      by simp
    have "passive \<sqsubset>L xx"
      using order_on_labels by simp
    then have "state (N, {}, P, {}, A) \<union> {(C, xx)} \<leadsto>GC state (N, {}, P, {}, A)"
      using remove_succ_L c'_le_c c'_passive_in by blast
    then show ?thesis
      by auto
  next
    assume "C' \<in> A"
    then have c'_active_in_state_NPA: "(C', active) \<in> state (N, {}, P, {}, A)"
      by simp
    also have active_ls_x: "active \<sqsubset>L xx"
      using active_minimal labels_distinct by simp
    then  have " state (N, {}, P, {}, A) \<union> {(C, xx)} \<leadsto>GC state (N, {}, P, {}, A) "
      using remove_succ_L c'_le_c active_ls_x c'_active_in_state_NPA by blast
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
  and ?\<M> = "{(C, xx)}" and ?\<M>' = "{(C', xx)}"

  have "P \<union> A \<union> {C'} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by auto
  then have "no_labels.Red_F (P \<union> A \<union> {C'}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using no_labels.Red_F_of_subset by auto
  then have "C \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using c_in by auto
  then have c_x_in: "(C, xx) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  then have "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')" by auto
  also have "xx \<noteq> active "
    using labels_distinct by auto
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

    have "(C, xx) \<in> state (N, {C}, P, {}, A)"
      by simp
    then have "?\<N> \<union> {(C', passive)} \<leadsto>GC ?\<N>"
      using c_ls_c' remove_succ_F by blast
    also have "?\<N> \<union> {(C', passive)} = state (N, {C}, P \<union> {C'}, {}, A)"
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
    then have "?\<N> \<union> {(C', passive)} \<leadsto>GC ?\<N>"
      using remove_redundant_no_label by blast
    then show ?thesis
      by (metis state_add_C_passive)
  qed

lemma simplifyBwdP_in_GC:
  assumes "C' \<in> no_labels.Red_F ({C, C''})"
  shows "state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>GC state (N \<union> {C''}, {C}, P, {}, A)"
proof -
  let ?\<N> = "state (N, {C}, P, {}, A)"
  and ?\<M> = "{(C', passive)}"
  and ?\<M>' = "{(C'', new)}"

  have "{C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
    by (smt (z3) Un_commute Un_empty_left Un_insert_right insert_absorb2
        subset_Un_eq state_add_C_new prj_state_union_sets)
  then have "no_labels.Red_F ({C, C''}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using no_labels.Red_F_of_subset by auto
  then have "C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
    using assms by auto
  then have "(C', passive) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using no_labels_Red_F_imp_Red_F by auto
  then have \<M>_in_redf: "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')" by auto

  have "new \<noteq> active "
    by (simp add: labels_distinct)
  then have active_subset_\<M>': "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto

  have "?\<N> \<union> ?\<M> \<leadsto>GC ?\<N> \<union> ?\<M>'"
    using \<M>_in_redf active_subset_\<M>' process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  also have "?\<N> \<union> {(C', passive)} = state (N, {C}, P \<union> {C'}, {}, A)"
    by force
  also have "?\<N> \<union> {(C'', new)} = state (N \<union> {C''}, {C}, P, {}, A)"
    using state_add_C_new by blast
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

    have " (C, xx) \<in> state (N, {C}, P, {}, A) "
      by simp
    then have "?\<N> \<union> {(C', active)} \<leadsto>GC ?\<N>"
      using c_ls_c' remove_succ_F by blast
    also have "?\<N> \<union> {(C', active)} = state (N, {C}, P, {}, A \<union> {C'})"
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
    then have "?\<N> \<union> {(C', active)} \<leadsto>GC ?\<N>"
      using remove_redundant_no_label by auto
    then show ?thesis
      by (metis state_add_C_active)
qed

lemma simplifyBwdA_in_GC:
  assumes "C' \<in> no_labels.Red_F ({C, C''})"
  shows "state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>GC state (N \<union> {C''}, {C}, P, {}, A)"
proof -
  let ?\<N> = "state (N, {C}, P, {}, A)" and ?\<M> = "{(C', active)}" and ?\<M>' = "{(C'', new)}"

  have " {C, C''} \<subseteq> fst` (?\<N> \<union> ?\<M>') "
    by simp
  then have " no_labels.Red_F ({C, C''}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
    using no_labels.Red_F_of_subset by auto
  then have " C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
    using assms by auto
  then have " (C', active) \<in> Red_F (?\<N> \<union> ?\<M>') "
    using no_labels_Red_F_imp_Red_F by auto
  then have \<M>_included: " ?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>') "
    by auto

  have "new \<noteq> active"
    by (simp add: labels_distinct)
  then have "active_subset ?\<M>' = {}"
    using active_subset_of_setOfFormulasWithLabelDiffActive by auto
  then have "state (N, {C}, P, {}, A) \<union> {(C', active)} \<leadsto>GC state (N, {C}, P, {}, A) \<union> {(C'', new)}"
    using \<M>_included process[where ?M="?\<M>" and ?M'="?\<M>'"] by auto
  then show ?thesis
    by (metis state_add_C_new state_add_C_active)
qed

lemma transfer_in_GC: "state (N, {C}, P, {}, A) \<leadsto>GC state  (N, {}, P \<union> {C}, {}, A)"
proof -
  let ?\<N> = "state (N, {}, P, {}, A)"

  have "passive \<sqsubset>L xx"
    by (simp add: order_on_labels)
  moreover have "passive \<noteq> active"
    by (simp add: labels_distinct)
  ultimately have "?\<N> \<union> {(C, xx)} \<leadsto>GC ?\<N> \<union> {(C, passive)}"
    using relabel_inactive by auto
  then show ?thesis
    by (metis sup_bot_left state_add_C_xx state_add_C_passive)
qed

lemma chooseP_in_GC: "state ( {}, {}, P \<union> {C}, {}, A) \<leadsto>GC state  ( {}, {}, P, {C}, A)"
proof -
  let ?\<N> = "state ({}, {}, P, {}, A)"

  have "yy \<sqsubset>L passive"
    by (simp add: order_on_labels)
  moreover have "yy \<noteq> active"
    by (simp add: labels_distinct)
  ultimately have "?\<N> \<union> {(C, passive)} \<leadsto>GC ?\<N> \<union> {(C, yy)}"
    using relabel_inactive by auto
  then show ?thesis
    by (metis sup_bot_left state_add_C_passive state_add_C_yy)
qed

lemma infer_in_GC:
  assumes "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M)"
  shows "state ({}, {}, P, {C}, A) \<leadsto>GC state (M, {}, P, {}, A \<union> {C})"
proof -
  let ?\<M> = "{(C', new) | C'. C' \<in> M}"
  let ?\<N> = "state ({}, {}, P, {}, A)"

  have active_subset_of_\<M>: "active_subset ?\<M> = {}"
    using labels_distinct active_subset_def by auto

  have "A \<union> {C} \<union> M \<subseteq> (fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>)"
    by fastforce
  then have "no_labels.Red_I (A \<union> {C} \<union> M) \<subseteq> no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
    using no_labels.empty_ord.Red_I_of_subset by auto
  moreover have "fst` (active_subset ?\<N>) = A"
    using prj_activeSubset_of_state by blast
  ultimately have "no_labels.Inf_between (fst` (active_subset ?\<N>)) {C} \<subseteq>
    no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
    using assms by auto

  then have "?\<N> \<union> {(C, yy)} \<leadsto>GC ?\<N> \<union> {(C, active)} \<union> ?\<M>"
    using labels_distinct active_subset_of_\<M> prj_fl_set_to_f_set_distr_union step.infer by force
  also have "?\<N> \<union> {(C, yy)} = state ({}, {}, P, {C}, A)"
    by simp
  also have "?\<N> \<union> {(C, active)} \<union> ?\<M> = state (M, {}, P, {}, A \<union> {C})"
    by force
  finally show ?thesis
    by simp
qed

theorem ol_in_gc: "M \<leadsto>OL M' \<Longrightarrow> M \<leadsto>GC M'"
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

end

end
