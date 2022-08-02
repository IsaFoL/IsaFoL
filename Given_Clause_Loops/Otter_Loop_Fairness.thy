theory Otter_Loop_Fairness
  imports Otter_Loop Loop_Fairness_Basis
begin

type_synonym ('p, 'f) fair_OL_state = "'f set \<times> 'f set \<times> 'p \<times> 'f set \<times> 'f set"

locale fair_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  passive_set empty select add remove fformulas
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
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<prec>\<cdot>\<close> 50) and
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    fformulas :: "'p \<Rightarrow> 'f fset" +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_prec_S: "minimal_element (\<prec>S) UNIV"
begin


subsection \<open>Definition and Lemmas\<close>

inductive
  fair_OL :: "('p, 'f) fair_OL_state \<Rightarrow> ('p, 'f) fair_OL_state \<Rightarrow> bool" (infix "\<leadsto>OLf" 50)
where
  choose_n: "C \<notin> N \<Longrightarrow> (N \<union> {C}, {}, P, {}, A) \<leadsto>OLf (N, {C}, P, {}, A)"
| delete_fwd: "C \<in> no_labels.Red_F (formulas P \<union> A) \<or> (\<exists>C' \<in> formulas P \<union> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {}, P, {}, A)"
| simplify_fwd: "C' \<prec>S S \<Longrightarrow> C \<in> no_labels.Red_F (formulas P \<union> A \<union> {C'}) \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {C'}, P, {}, A)"
| delete_bwd_p: "C' \<in> formulas P \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {C}, remove C' P, {}, A)"
| simplify_bwd_p: "C' \<prec>S S \<Longrightarrow> C' \<in> formulas P \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N \<union> {C''}, {C}, remove C' P, {}, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf (N, {C}, P, {}, A)"
| simplify_bwd_a: "C' \<prec>S S \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf (N \<union> {C''}, {C}, P, {}, A)"
| transfer: "(N, {C}, P, {}, A) \<leadsto>OLf (N, {}, add C P, {}, A)"
| choose_p: "fformulas P \<noteq> {||} \<Longrightarrow>
    ({}, {}, P, {}, A) \<leadsto>OLf ({}, {}, remove (select P) P, {select P}, A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    ({}, {}, P, {C}, A) \<leadsto>OLf (M, {}, P, {}, A \<union> {C})"


subsection \<open>Refinement\<close>

lemma fair_OL_step_imp_OL_step:
  assumes olf: "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A')"
  shows "state (N, X, formulas P, Y, A) \<leadsto>OL state (N', X', formulas P', Y', A')"
  using olf
proof cases
  case (choose_n C)
  note unfolds = this(1-7) and c_ni = this(8)
  show ?thesis
    unfolding unfolds by (rule OL.choose_n[OF c_ni])
next
  case (delete_fwd C)
  note unfolds = this(1-7) and c_red = this(8)
  show ?thesis
    unfolding unfolds by (rule OL.delete_fwd[OF c_red])
next
  case (simplify_fwd C' S C)
  note unfolds = this(1-7) and c_red = this(9)
  show ?thesis
    unfolding unfolds by (rule OL.simplify_fwd[OF c_red])
next
  case (delete_bwd_p C' C)
  note unfolds = this(1-7) and c'_in_p = this(8) and c'_red = this(9)

  have p_rm_c'_uni_c': "formulas (remove C' P) \<union> {C'} = formulas P"
    unfolding fformulas_remove by (auto intro: c'_in_p)
  have p_mns_c': "formulas P - {C'} = formulas (remove C' P)"
    unfolding fformulas_remove by auto

  show ?thesis
    unfolding unfolds
    by (rule OL.delete_bwd_p[OF c'_red, of _ "formulas P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (simplify_bwd_p C' S C C'')
  note unfolds = this(1-7) and c'_in_p = this(9) and c'_red = this(10)

  have p_rm_c'_uni_c': "formulas (remove C' P) \<union> {C'} = formulas P"
    unfolding fformulas_remove by (auto intro: c'_in_p)
  have p_mns_c': "formulas P - {C'} = formulas (remove C' P)"
    unfolding fformulas_remove by auto

  show ?thesis
    unfolding unfolds
    by (rule OL.simplify_bwd_p[OF c'_red, of _ "formulas P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (delete_bwd_a C' C)
  note unfolds = this(1-7) and c'_red = this(8)
  show ?thesis
    unfolding unfolds by (rule OL.delete_bwd_a[OF c'_red])
next
  case (simplify_bwd_a C' S C C'')
  note unfolds = this(1-7) and c'_red = this(9)
  show ?thesis
    unfolding unfolds by (rule OL.simplify_bwd_a[OF c'_red])
next
  case (transfer C)
  note unfolds = this(1-7)

  have p_uni_c: "formulas P \<union> {C} = formulas (add C P)"
    unfolding fformulas_add by auto

  show ?thesis
    unfolding unfolds by (rule OL.transfer[of _ C "formulas P", unfolded p_uni_c])
next
  case choose_p
  note unfolds = this(1-8) and p_nemp = this(9)

  have sel_ni_rm: "select P \<notin> formulas (remove (select P) P)"
    unfolding fformulas_remove by auto

  have rm_sel_uni_sel: "formulas (remove (select P) P) \<union> {select P} = formulas P"
    unfolding fformulas_remove using p_nemp select_in_fformulas
    by (metis Un_insert_right finsert.rep_eq finsert_fminus sup_bot_right)

  show ?thesis
    unfolding unfolds
    by (rule OL.choose_p[of "select P" "formulas (remove (select P) P)", OF sel_ni_rm,
          unfolded rm_sel_uni_sel])
next
  case (infer C)
  note unfolds = this(1-7) and infers = this(8)
  show ?thesis
    unfolding unfolds by (rule OL.infer[OF infers])
qed

lemma fair_OL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A') \<Longrightarrow>
   state (N, X, formulas P, Y, A) \<leadsto>GC state (N', X', formulas P', Y', A')"
  by (rule OL_step_imp_GC_step[OF fair_OL_step_imp_OL_step])


subsection \<open>Completeness\<close>

lemma
  assumes "chain (\<leadsto>OLf) Sts"
  shows
    fair_OL_liminf_new_empty: "Liminf_llist (lmap fst Sts) = {}" and
    fair_OL_liminf_xx_empty: "Liminf_llist (lmap (fst \<circ> snd) Sts) = {}" and
    fair_OL_liminf_passive_empty: "Liminf_llist (lmap (formulas \<circ> fst \<circ> snd \<circ> snd) Sts) = {}" and
    fair_OL_liminf_yy_empty: "Liminf_llist (lmap (fst \<circ> snd \<circ> snd \<circ> snd) Sts) = {}"
  sorry



end

end
