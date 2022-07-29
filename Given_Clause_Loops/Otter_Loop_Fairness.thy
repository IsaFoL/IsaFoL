theory Otter_Loop_Fairness
  imports Otter_Loop Loop_Fairness_Basis
begin

type_synonym ('p, 'f) fair_OL_state = "'p \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set"

datatype otter_loop_label =
  Active | New | XX | Passive | YY

fun Prec_L :: "otter_loop_label \<Rightarrow> otter_loop_label \<Rightarrow> bool" where
  "Prec_L YY _ \<longleftrightarrow> False"
| "Prec_L Passive YY \<longleftrightarrow> True"
| "Prec_L Passive _ \<longleftrightarrow> False"
| "Prec_L XX YY \<longleftrightarrow> True"
| "Prec_L XX Passive \<longleftrightarrow> True"
| "Prec_L XX _ \<longleftrightarrow> False"
| "Prec_L New YY \<longleftrightarrow> True"
| "Prec_L New Passive \<longleftrightarrow> True"
| "Prec_L New XX \<longleftrightarrow> True"
| "Prec_L New _ \<longleftrightarrow> False"
| "Prec_L Active YY \<longleftrightarrow> True"
| "Prec_L Active Passive \<longleftrightarrow> True"
| "Prec_L Active XX \<longleftrightarrow> True"
| "Prec_L Active New \<longleftrightarrow> True"
| "Prec_L Active Active \<longleftrightarrow> False"

(*
"('f \<times> otter_loop_label) inference set"
*)

locale fair_otter_loop =
  ol: otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Inf_FL Equiv_F
    Prec_F Prec_L Active New XX Passive YY +
  ps: passive_struct
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
    Inf_F :: "'f inference set" and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<doteq>\<close> 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<prec>\<cdot>\<close> 50)
begin

inductive fair_OL :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>OLf" 50) where
  choose_n: "C \<notin> N \<Longrightarrow> state (N \<union> {C}, {}, P, {}, A) \<leadsto>OLf state (N, {C}, P, {}, A) "
| delete_fwd: "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C'\<in> (P \<union> A). C' \<preceq>\<cdot> C) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OLf state (N, {}, P, {}, A) "
| simplify_fwd: "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
    state (N, {C}, P, {}, A) \<leadsto>OLf state (N, {C'}, P, {}, A)"
| delete_bwd_p: "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OLf state(N, {C}, P, {}, A)"
| simplify_bwd_p: "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
    state (N, {C}, P \<union> {C'}, {}, A) \<leadsto>OLf state (N \<union> {C''}, {C}, P, {}, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf state (N, {C}, P, {}, A)"
| simplify_bwd_a: "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow>
    state (N, {C}, P, {}, A \<union> {C'}) \<leadsto>OLf state (N \<union> {C''}, {C}, P, {}, A)"
| transfer: "state (N, {C}, P, {}, A) \<leadsto>OLf state (N, {}, P \<union> {C}, {}, A)"
| choose_p: "C \<notin> P \<Longrightarrow> state ({}, {}, P \<union> {C}, {}, A) \<leadsto>OLf state ({}, {}, P, {C}, A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    state ({}, {}, P, {C}, A) \<leadsto>OLf state  (M, {}, P, {}, A \<union> {C})"



thm gc_fair

end

end
