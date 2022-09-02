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

inductive pick_lqueue_step_aux :: "'q \<times> 'e set \<Rightarrow> 'e \<Rightarrow> 'e llist \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_step_auxI: "LCons e es \<in># llists Q \<Longrightarrow>
    fst (pick_elem Q) = e \<Longrightarrow>
    llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#} \<Longrightarrow>
    pick_lqueue_step_aux (Q, D) e es (snd (pick_elem Q), D \<union> {e})"

inductive pick_lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  "pick_lqueue_step_aux QD e es QD' \<Longrightarrow> pick_lqueue_step QD QD'"

end

locale fair_prover_lazy_list_queue =
  prover_lazy_list_queue empty add_llist remove_llist pick_elem llists
  for
    empty :: 'q and
    add_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    llists :: "'q \<Rightarrow> 'e llist multiset" +
  assumes fair: "chain lqueue_step (lmap fst QDs) \<Longrightarrow> infinitely_often pick_lqueue_step QDs \<Longrightarrow>
    LCons e es \<in># llists (fst (lnth QDs i)) \<Longrightarrow>
    \<exists>j \<ge> i. enat (Suc j) < llength QDs \<and> pick_lqueue_step_aux (lnth QDs j) e es (lnth QDs (Suc j))"
begin

lemma fair_strong:
  assumes
    chain: "chain lqueue_step (lmap fst QDs)" and
    inf: "infinitely_often pick_lqueue_step QDs" and
    es_in: "es \<in># llists (fst (lnth QDs i))" and
    k_lt: "enat k < llength es"
  shows "\<exists>j \<ge> i. enat (Suc j) < llength QDs
    \<and> pick_lqueue_step_aux (lnth QDs j) (lnth es k) (ldrop (Suc k) es) (lnth QDs (Suc j))"
  using es_in k_lt
proof (induct k arbitrary: i es)
  case 0
  note es_in = this(1) and zero_lt = this(2)
  have es_in': "LCons (lnth es 0) (ldrop (Suc 0) es) \<in># llists (fst (lnth QDs i))"
    using es_in by (metis zero_lt ldrop_0 ldrop_enat ldropn_Suc_conv_ldropn zero_enat_def)
  show ?case
    using fair[OF chain inf es_in'] by (simp add: ldrop_enat ldropn_Suc_conv_ldropn)
next
  case (Suc k)
  note ih = this(1) and  es_in = this(2) and sk_lt = this(3)

  have es_in': "LCons (lnth es 0) (ldrop (Suc 0) es) \<in># llists (fst (lnth QDs i))"
    using es_in by (metis gr_zeroI ldrop_enat ldropn_0 ldropn_Suc_conv_ldropn not_less_zero sk_lt
        zero_enat_def)

  obtain j :: nat where
    j_gt: "j \<ge> i" and
    sj_lt: "enat (Suc j) < llength QDs" and
    "pick_lqueue_step_aux (lnth QDs j) (lnth es 0) (ldrop (enat (Suc 0)) es) (lnth QDs (Suc j))"
    sorry
  thm fair[OF chain inf es_in']

  show ?case
    sorry
qed

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
    QDs :: "('e llist list \<times> 'e set) llist" and
    i :: nat and
    e :: 'e and
    es :: "'e llist"
  assume
    "chain lqueue_step (lmap fst QDs)" and
    "infinitely_often pick_lqueue_step QDs" and
    "LCons e es \<in># mset (fst (lnth QDs i))"
  show "\<exists>j \<ge> i. enat (Suc j) < llength QDs
    \<and> pick_lqueue_step_aux (lnth QDs j) e es (lnth QDs (Suc j))"
    sorry
qed

end

end
