theory Otter_Loop_Fairness
  imports Otter_Loop Loop_Fairness_Basis
begin

type_synonym ('p, 'f) fair_OL_state = "'f set \<times> 'f set \<times> 'p \<times> 'f set \<times> 'f set"

datatype OL_label =
  Active | New | XX | Passive | YY

primrec nat_of_OL_label :: "OL_label \<Rightarrow> nat" where
  "nat_of_OL_label Active = 0"
| "nat_of_OL_label New = 1"
| "nat_of_OL_label XX = 2"
| "nat_of_OL_label Passive = 3"
| "nat_of_OL_label YY = 4"

definition OL_Prec_L :: "OL_label \<Rightarrow> OL_label \<Rightarrow> bool" where
  "OL_Prec_L l l' \<longleftrightarrow> nat_of_OL_label l < nat_of_OL_label l'"

locale fair_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
    OL_Prec_L Active New XX Passive YY +
  ps: passive_set empty select add remove fformulas
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
    select :: "'p \<Rightarrow> 'f \<times> 'p" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    fformulas :: "'p \<Rightarrow> 'f fset"
begin

inductive
  fair_OL :: "('p, 'f) fair_OL_state \<Rightarrow> ('p, 'f) fair_OL_state \<Rightarrow> bool" (infix "\<leadsto>OLf" 50)
where
  choose_n: "C \<notin> N \<Longrightarrow> (N \<union> {C}, {}, P, {}, A) \<leadsto>OLf (N, {C}, P, {}, A)"
| delete_fwd: "C \<in> no_labels.Red_F (formulas P \<union> A) \<or> (\<exists>C' \<in> formulas P \<union> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {}, P, {}, A)"
| simplify_fwd: "C \<in> no_labels.Red_F (formulas P \<union> A \<union> {C'}) \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {C'}, P, {}, A)"
| delete_bwd_p: "C' \<in> formulas P \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, {C}, P, {}, A) \<leadsto>OLf (N, {C}, delete C' P, {}, A)"
(*
| simplify_bwd_p: "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OLf state (N \<union> {C''}, {C}, P, {}, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf state (N, {C}, P, {}, A)"
| simplify_bwd_a: "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf state (N \<union> {C''}, {C}, P, {}, A)"
| transfer: "state (N, {C}, P, {}, A) \<leadsto>OLf state (N, {}, P \<union> {C}, {}, A)"
| choose_p: "C \<notin> P \<Longrightarrow> state ({}, {}, P \<union> {C}, {}, A) \<leadsto>OLf state ({}, {}, P, {C}, A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    state ({}, {}, P, {C}, A) \<leadsto>OLf state  (M, {}, P, {}, A \<union> {C})"
*)


thm gc_fair

end

end
