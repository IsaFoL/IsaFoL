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

locale prover_lazy_list_queue =
  fixes
    empty :: 'q and
    add_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    llists :: "'q \<Rightarrow> 'e llist multiset"
  assumes
    llists_empty[simp]: "llists empty = {#}" and
    llists_not_empty: "Q \<noteq> empty \<Longrightarrow> llists Q \<noteq> {#}" and
    llists_add[simp]: "llists (add_llist es Q) = llists Q + {#es#}" and
    llist_remove[simp]: "llists (remove_llist es Q) = llists Q - {#es#}" and
    llists_pick_elem: "(\<exists>es. es \<noteq> LNil \<and> es \<in># llists Q) \<Longrightarrow>
      \<exists>e es. LCons e es \<in># llists Q \<and> fst (pick_elem Q) = e
        \<and> llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#}"
begin

inductive lqueue_step :: "'q \<Rightarrow> 'q \<Rightarrow> bool" where
  lqueue_step_fold_addI: "lqueue_step Q (fold add_llist Cs Q)"
| lqueue_step_fold_removeI: "lqueue_step Q (fold remove_llist Cs Q)"
| queue_step_pick_elemI: "lqueue_step Q (snd (pick_elem Q))"

lemma lqueue_step_idleI: "lqueue_step Q Q"
  using lqueue_step_fold_addI[of _ "[]", simplified] .

inductive pick_lqueue_step_aux :: "'q \<Rightarrow> 'e \<Rightarrow> 'e llist \<Rightarrow> 'q \<Rightarrow> bool" where
  pick_lqueue_step_auxI: "LCons e es \<in># llists Q \<Longrightarrow>
    fst (pick_elem Q) = e \<Longrightarrow>
    llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#} \<Longrightarrow>
    pick_lqueue_step_aux Q e es (snd (pick_elem Q))"

inductive pick_lqueue_step :: "'q \<Rightarrow> 'q \<Rightarrow> bool" where
  "pick_lqueue_step_aux Q e es Q' \<Longrightarrow> pick_lqueue_step Q Q'"

end

locale fair_prover_lazy_list_queue =
  prover_lazy_list_queue empty add_llist remove_llist pick_elem llists
  for
    empty :: 'q and
    add_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    llists :: "'q \<Rightarrow> 'e llist multiset" +
  assumes fair: "chain lqueue_step Qs \<Longrightarrow> infinitely_often pick_lqueue_step Qs \<Longrightarrow>
    enat i < llength Qs \<Longrightarrow> LCons e es \<in># llists (lnth Qs i) \<Longrightarrow>
    \<exists>j \<ge> i. enat (Suc j) < llength Qs \<and> pick_lqueue_step_aux (lnth Qs j) e es (lnth Qs (Suc j))"
begin
end


subsection \<open>Instantiation with FIFO Queue\<close>

text \<open>As a proof of concept, we show that a FIFO queue can serve as a fair
prover lazy list queue.\<close>

locale fifo_prover_lazy_list_queue
begin

fun pick_elem :: "'e llist list \<Rightarrow> 'e \<times> 'e llist list" where
  "pick_elem [] = undefined"
| "pick_elem (LNil # ess) = pick_elem ess"
| "pick_elem (LCons e es # ess) = (e, es # ess)"

sublocale prover_lazy_list_queue "[]" "\<lambda>es ess. ess @ [es]" remove1 pick_elem mset
proof
  show "\<And>Q. \<exists>es. es \<noteq> LNil \<and> es \<in># mset Q \<Longrightarrow>
    \<exists>e es. LCons e es \<in># mset Q \<and> fst (pick_elem Q) = e
      \<and> mset (snd (pick_elem Q)) = mset Q - {#LCons e es#} + {#es#}"
    sorry
qed simp+

end

end
