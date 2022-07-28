(* Title:        Basic Definitions for Stating and Proving the Fairness of Prover Loops
   Authors:      Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022 *)


section \<open>Basic Definitions for Stating and Proving the Fairness of Prover Loops\<close>

text \<open>This section covers concepts that can be shared across the different
prover loops inspired by the literature (e.g., DISCOUNT, Otter).\<close>

theory Loop_Fairness_Basis
  imports
    "HOL-Library.FSet"
    Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Passive Set\<close>

text \<open>The passive set of a given clause prover can be organized in different
ways—e.g., as a priority queue or as a list of queues. This locale abstracts
over the specific data structure.\<close>

locale passive_struct =
  fixes
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f \<times> 'p" and
    add :: "'f list \<Rightarrow> 'p \<Rightarrow> 'p" and
    formulas :: "'p \<Rightarrow> 'f fset"
  assumes
    "formulas empty = {||}" and
    "formulas P \<noteq> {||} \<Longrightarrow> finsert (fst (select P)) (formulas (snd (select P))) = formulas P" and
    "formulas (add Cs P) = fset_of_list Cs |\<union>| formulas P"
begin

inductive step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  stepI: "step P (add F (snd (select P)))"

definition is_struct_fair :: bool where
  "is_struct_fair \<longleftrightarrow> (\<forall>Ps. full_chain step Ps \<longrightarrow> Liminf_llist (lmap (fset \<circ> formulas) Ps) = {})"

end

interpretation fifo: passive_struct "[]" "\<lambda>xs. (hd xs, tl xs)" "\<lambda>ys xs. xs @ ys" fset_of_list
proof
  show "fset_of_list [] = {||}"
    by (auto simp: fset_of_list_elem)
next
  show "\<And>P. fset_of_list P \<noteq> {||} \<Longrightarrow>
    finsert (fst (hd P, tl P)) (fset_of_list (snd (hd P, tl P))) = fset_of_list P"
    by (metis fset_of_list_simps fst_conv list.exhaust_sel snd_conv)
next
  show "\<And>Cs P. fset_of_list (P @ Cs) = fset_of_list Cs |\<union>| fset_of_list P"
    by (simp add: funion_commute)
qed

lemma fifo_is_struct_fair: "fifo.is_struct_fair TYPE('f)"
  unfolding fifo.is_struct_fair_def
proof (intro allI impI)
  fix Ps :: "'f list llist"
  assume "full_chain fifo.step Ps"
  show "Liminf_llist (lmap (fset \<circ> fset_of_list) Ps) = {}"
    sorry

qed

end
