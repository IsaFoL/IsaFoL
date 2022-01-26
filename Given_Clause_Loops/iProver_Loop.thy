(* Title:        iProver Loop
   Authors:      Qi Qiu, 2021
                 Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>iProver Loop\<close>

theory iProver_Loop
  imports
    Otter_Loop
    Saturation_Framework.Given_Clause_Architectures
begin

locale iProver_loop = OL?: otter_loop
  Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q
  Red_F_q \<G>_F_q \<G>_I_q Inf_FL Equiv_F Prec_F Prec_L active new x passive y
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
    active :: "'l" and
    new :: 'l and
    x :: 'l and
    passive :: 'l and
    y :: 'l
begin


subsection \<open>definition, abbreviation, type and fun\<close>

inductive iProver_loop :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>IL" 50) where
ol: "\<M> \<leadsto>OL \<M>' \<Longrightarrow>
  \<M> \<leadsto>IL \<M>'"
| replace: "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = { C' } \<and> C' \<prec>\<cdot> C) \<Longrightarrow>
  state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>IL state (M, \<emptyset>, P, \<emptyset>, A)"

lemma replace_in_GC:
  assumes "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = { C' } \<and> C' \<prec>\<cdot> C)"
  shows "state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>GC state (M, \<emptyset>, P, \<emptyset>, A)"
proof -
  let ?\<N> = "state (\<emptyset>, \<emptyset>, P, \<emptyset>, A)"
  and ?\<M> = "{(C, y)}"
  and ?\<M>' = "{(x, new) |x. x\<in>M}"

  have "(C, y) \<in> Red_F (?\<N> \<union> ?\<M>')"
    using assms
  proof
    assume c_in: "C \<in> no_labels.Red_F (A \<union> M)"
    have "A \<union> M \<subseteq> A \<union> M \<union> P" by auto
    also have "fst ` (?\<N> \<union> ?\<M>') = A \<union> M \<union> P"
      by auto
    then have "C \<in> no_labels.Red_F (fst ` (?\<N> \<union> ?\<M>'))"
      by (metis (no_types, lifting) c_in calculation in_mono no_labels.Red_F_of_subset)
    then show "(C, y) \<in> Red_F (?\<N> \<union> ?\<M>')"
      using lemma59point1 by blast
  next
    assume assm: "M = {C'} \<and> C' \<prec>\<cdot> C"
    then have "C' \<in> fst ` (?\<N> \<union> ?\<M>')"
      by simp
    then show "(C, y) \<in> Red_F (?\<N> \<union> ?\<M>')"
      by (metis (mono_tags, lifting) assm lemma59point2)
  qed

  then have \<M>_included_in: "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')"
    by auto

  have "new \<noteq> active"
    by (simp add: labels_distinct)
  then have prj_of_active_subset_of_\<M>': "fst ` (active_subset ?\<M>') = \<emptyset>"
    by (simp add: active_subset_def)

  have "?\<N> \<union> ?\<M> \<leadsto>GC ?\<N> \<union> ?\<M>'"
    using process[of _ "?\<N>" "?\<M>" _ "?\<M>'"] \<M>_included_in prj_of_active_subset_of_\<M>' by auto
  moreover have "?\<N> \<union> ?\<M> = state (\<emptyset>, \<emptyset>, P, {C}, A)"
    by simp
  moreover have "?\<N> \<union> ?\<M>' = state (M, \<emptyset>, P, \<emptyset>, A)"
    by auto
  ultimately show "state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>GC state (M, \<emptyset>, P, \<emptyset>, A)"
    by simp
qed


subsection \<open>Inclusion of IL in GC\<close>

theorem inclusion_ol_in_gc: "M \<leadsto>IL M' \<Longrightarrow> M \<leadsto>GC M'"
proof (induction rule: iProver_loop.induct)
  case (ol \<M> \<M>')
  then show ?case
    by (simp add: inclusion_ol_in_gc)
next
  case (replace C A M C' P)
  then show ?case using replace_in_GC by auto
qed

end

end
