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
    llists_pick_elem: "(\<exists>es \<in># llists Q. es \<noteq> LNil) \<Longrightarrow>
      \<exists>e es. LCons e es \<in># llists Q \<and> fst (pick_elem Q) = e
        \<and> llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#}"
begin

abbreviation has_elem :: "'q \<Rightarrow> bool" where
  "has_elem Q \<equiv> \<exists>es \<in># llists Q. es \<noteq> LNil"

inductive lqueue_step :: "'q \<Rightarrow> 'q \<Rightarrow> bool" where
  lqueue_step_fold_add_llistI: "lqueue_step Q (fold add_llist ess Q)"
| lqueue_step_fold_remove_llistI: "lqueue_step Q (fold remove_llist ess Q)"
| lqueue_step_pick_elemI: "has_elem Q \<Longrightarrow> lqueue_step Q (snd (pick_elem Q))"

lemma lqueue_step_idleI: "lqueue_step Q Q"
  using lqueue_step_fold_add_llistI[of _ "[]", simplified] .

lemma lqueue_step_add_llistI: "lqueue_step Q (add_llist es Q)"
  using lqueue_step_fold_add_llistI[of _ "[es]", simplified] .

lemma lqueue_step_remove_llistI: "lqueue_step Q (remove_llist es Q)"
  using lqueue_step_fold_remove_llistI[of _ "[es]", simplified] .

lemma llists_fold_add_llist[simp]: "llists (fold add_llist es Q) = mset es + llists Q"
  by (induct es arbitrary: Q) auto

lemma llists_fold_remove_llist[simp]: "llists (fold remove_llist es Q) = llists Q - mset es"
  by (induct es arbitrary: Q) auto

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
| "pick_elem (LNil # ess) =
   (let (e, ess') = pick_elem ess in
      (e, ess' @ [LNil]))"
| "pick_elem (LCons e es # ess) = (e, ess @ [es])"

sublocale prover_lazy_list_queue "[]" "\<lambda>es ess. ess @ [es]" remove1 pick_elem mset
proof
  fix Q :: "'e llist list"
  assume ex_cons: "\<exists>es \<in># mset Q. es \<noteq> LNil"
  show "\<exists>e es. LCons e es \<in># mset Q \<and> fst (pick_elem Q) = e
      \<and> mset (snd (pick_elem Q)) = mset Q - {#LCons e es#} + {#es#}"
    using ex_cons
  proof (induct Q rule: pick_elem.induct)
    case 1
    note ex_cons = this(1)
    have False
      using ex_cons by simp
    thus ?case
      by blast
  next
    case (2 ess)
    note ih = this(1) and ex_cons = this(2)

    obtain e :: 'e and es :: "'e llist" where
      "LCons e es \<in># mset ess" and
      "fst (pick_elem ess) = e" and
      "mset (snd (pick_elem ess)) = mset ess - {#LCons e es#} + {#es#}"
      using ih ex_cons by auto
    thus ?case
      by (auto simp: case_prod_beta)
  next
    case (3 e es ess)
    show ?case
      using add_mset_diff_bothsides by auto
  qed
qed simp+

sublocale fair_prover_lazy_list_queue "[]" "\<lambda>es ess. ess @ [es]" remove1 pick_elem mset
proof
  fix
    Qs :: "'a llist list llist" and
    i :: nat and
    e :: 'a and
    es :: "'a llist"
  assume
    "chain lqueue_step Qs" and
    "infinitely_often pick_lqueue_step Qs" and
    "enat i < llength Qs" and
    "LCons e es \<in># mset (lnth Qs i)"
  show "\<exists>j \<ge> i. enat (Suc j) < llength Qs \<and> pick_lqueue_step_aux (lnth Qs j) e es (lnth Qs (Suc j))"
    sorry
qed

end

end