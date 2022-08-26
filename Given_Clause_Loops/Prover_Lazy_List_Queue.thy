(* Title:        Prover Lazy List Queues and Fairness
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Prover Lazy List Queues and Fairness\<close>

text \<open>This section covers the to-do data structure that arises in the
Zipperposition loop.\<close>

theory Prover_Lazy_List_Queue
  imports Prover_Queue
begin


subsection \<open>Locales\<close>

locale prover_llist_queue =
  fixes
    empty :: 'q and
    add_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and (* FIXME *)
    remove_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    llists :: "'q \<Rightarrow> 'e llist multiset"
  assumes
    llists_empty[simp]: "llists empty = {#}" and
    llists_not_empty: "Q \<noteq> empty \<Longrightarrow> llists Q \<noteq> {#}" and
    llists_add[simp]: "llists (add_llist es Q) = llists Q + {#es#}"
(*
    pick_elem
    select_in_felems[simp]: "P \<noteq> empty \<Longrightarrow> select P |\<in>| felems P" and
    felems_remove[simp]: "felems (remove C P) = felems P |-| {|C|}" and
    add_again: "C |\<in>| felems P \<Longrightarrow> add C P = P"
*)
begin


end
