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
    nil :: 's and
    llist :: "'s \<Rightarrow> 'e llist" and
    empty :: 'q and
    add_stream :: "'s \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_stream :: "'s \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    streams :: "'q \<Rightarrow> 's multiset"
  assumes
    llist_nil[simp]: "llist nil = LNil" and
    streams_empty[simp]: "streams empty = {#}" and
    streams_not_empty: "Q \<noteq> empty \<Longrightarrow> streams Q \<noteq> {#}" and
    streams_add[simp]: "streams (add_stream es Q) = streams Q + {#es#}" and
    streams_remove[simp]: "streams (remove_stream es Q) = streams Q - {#es#}" and
    streams_pick_elem: "(\<exists>s \<in># streams Q. llist s \<noteq> LNil) \<Longrightarrow>
      \<exists>s \<in># streams Q. \<exists>s'. llist s \<noteq> LNil \<and> llist s' = ltl (llist s)
        \<and> fst (pick_elem Q) = lhd (llist s)
        \<and> streams (snd (pick_elem Q)) = streams Q - {#s#} + {#s'#}"
begin

abbreviation has_elem :: "'q \<Rightarrow> bool" where
  "has_elem Q \<equiv> \<exists>s \<in># streams Q. llist s \<noteq> LNil"

inductive lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  lqueue_step_fold_add_streamI:
  "lqueue_step (Q, D) (fold add_stream ss Q, D - \<Union> {lset (llist s) |s. s \<in> set ss})"
| lqueue_step_fold_remove_streamI:
  "lqueue_step (Q, D) (fold remove_stream ss Q, D \<union> \<Union> {lset (llist s) |s. s \<in> set ss})"
| lqueue_step_pick_elemI: "has_elem Q \<Longrightarrow>
  lqueue_step (Q, D) (snd (pick_elem Q), D \<union> {fst (pick_elem Q)})"

lemma lqueue_step_idleI: "lqueue_step QD QD"
  using lqueue_step_fold_add_streamI[of "fst QD" "snd QD" "[]", simplified] .

lemma lqueue_step_add_streamI: "lqueue_step (Q, D) (add_stream s Q, D - lset (llist s))"
  using lqueue_step_fold_add_streamI[of _ _ "[s]", simplified] .

lemma lqueue_step_remove_streamI: "lqueue_step (Q, D) (remove_stream s Q, D \<union> lset (llist s))"
  using lqueue_step_fold_remove_streamI[of _ _ "[s]", simplified] .

lemma streams_fold_add_stream[simp]: "streams (fold add_stream ss Q) = mset ss + streams Q"
  by (induct ss arbitrary: Q) auto

lemma streams_fold_remove_stream[simp]: "streams (fold remove_stream ss Q) = streams Q - mset ss"
  by (induct ss arbitrary: Q) auto

inductive
  pick_lqueue_step_w_details :: "'q \<times> 'e set \<Rightarrow> 'e \<Rightarrow> 'e llist \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool"
where
  pick_lqueue_step_w_detailsI: "s \<in># streams Q \<Longrightarrow> llist s \<noteq> LNil \<Longrightarrow> llist s' = ltl (llist s) \<Longrightarrow>
    fst (pick_elem Q) = lhd (llist s) \<Longrightarrow>
    streams (snd (pick_elem Q)) = streams Q - {#s#} + {#s'#} \<Longrightarrow>
    pick_lqueue_step_w_details (Q, D) e es s s' (snd (pick_elem Q), D \<union> {e})"

inductive pick_lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_stepI: "pick_lqueue_step_w_details QD e es s s' QD' \<Longrightarrow> pick_lqueue_step QD QD'"

inductive
  remove_lqueue_step_w_details :: "'q \<times> 'e set \<Rightarrow> 'e llist list \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool"
where
  remove_lqueue_step_w_detailsI:
    "remove_lqueue_step_w_details (Q, D) ss
       (fold remove_stream ss Q, D \<union> \<Union> {lset (llist s) |s. s \<in> set ss})"

end

locale fair_prover_lazy_list_queue =
  prover_lazy_list_queue empty add_stream remove_stream pick_elem streams
  for
    empty :: 'q and
    add_stream :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_stream :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    streams :: "'q \<Rightarrow> 'e llist multiset" +
  assumes fair: "chain lqueue_step QDs \<Longrightarrow> infinitely_often pick_lqueue_step QDs \<Longrightarrow>
    LCons e es \<in># streams (fst (lnth QDs i)) \<Longrightarrow>
    \<exists>j \<ge> i. (\<exists>ess. LCons e es \<in> set ess
        \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
      \<or> pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
begin

lemma fair_strong:
  assumes
    chain: "chain lqueue_step QDs" and
    inf: "infinitely_often pick_lqueue_step QDs" and
    es_in: "es \<in># streams (fst (lnth QDs i))" and
    k_lt: "enat k < llength es"
  shows "\<exists>j \<ge> i.
    (\<exists>k' \<le> k. \<exists>ess. ldrop k' es \<in> set ess
         \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
       \<or> pick_lqueue_step_w_details (lnth QDs j) (lnth es k) (ldrop (Suc k) es) (lnth QDs (Suc j))"
  using k_lt
proof (induct k)
  case 0
  note zero_lt = this
  have es_in': "LCons (lnth es 0) (ldrop (Suc 0) es) \<in># streams (fst (lnth QDs i))"
    using es_in by (metis zero_lt ldrop_0 ldrop_enat ldropn_Suc_conv_ldropn zero_enat_def)
  show ?case
    using fair[OF chain inf es_in']
    by (metis dual_order.refl ldrop_enat ldropn_Suc_conv_ldropn zero_lt)
next
  case (Suc k)
  note ih = this(1) and sk_lt = this(2)

  have k_lt: "enat k < llength es"
    using sk_lt Suc_ile_eq order_less_imp_le by blast

  obtain j :: nat where
    j_ge: "j \<ge> i" and
    rem_or_pick_step: "(\<exists>k' \<le> k. \<exists>ess. ldrop (enat k') es \<in> set ess
        \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
      \<or> pick_lqueue_step_w_details (lnth QDs j) (lnth es k) (ldrop (enat (Suc k)) es)
        (lnth QDs (Suc j))"
    using ih[OF k_lt] by blast

  {
    assume "\<exists>k' \<le> k. \<exists>ess. ldrop (enat k') es \<in> set ess
      \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j))"
    hence ?case
      using j_ge le_SucI by blast
  }
  moreover
  {
    assume "pick_lqueue_step_w_details (lnth QDs j) (lnth es k) (ldrop (enat (Suc k)) es)
      (lnth QDs (Suc j))"
    hence cons_in: "LCons (lnth es (Suc k)) (ldrop (enat (Suc (Suc k))) es)
      \<in># streams (fst (lnth QDs (Suc j)))"
      unfolding pick_lqueue_step_w_details.simps using sk_lt
      by (metis fst_conv ldrop_enat ldropn_Suc_conv_ldropn union_mset_add_mset_right
          union_single_eq_member)

    have ?case
      using fair[OF chain inf cons_in] j_ge
      by (smt (z3) dual_order.trans ldrop_enat ldropn_Suc_conv_ldropn le_Suc_eq sk_lt)
  }
  ultimately show ?case
    using rem_or_pick_step by blast
qed

end

end
