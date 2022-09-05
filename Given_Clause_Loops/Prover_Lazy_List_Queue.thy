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

inductive lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  lqueue_step_fold_add_llistI:
  "lqueue_step (Q, D) (fold add_llist ess Q, D - \<Union> {lset es |es. es \<in> set ess})"
| lqueue_step_fold_remove_llistI:
  "lqueue_step (Q, D) (fold remove_llist ess Q, D \<union> \<Union> {lset es |es. es \<in> set ess})"
| lqueue_step_pick_elemI: "has_elem Q \<Longrightarrow>
  lqueue_step (Q, D) (snd (pick_elem Q), D \<union> {fst (pick_elem Q)})"

lemma lqueue_step_idleI: "lqueue_step QD QD"
  using lqueue_step_fold_add_llistI[of "fst QD" "snd QD" "[]", simplified] .

lemma lqueue_step_add_llistI: "lqueue_step (Q, D) (add_llist es Q, D - lset es)"
  using lqueue_step_fold_add_llistI[of _ _ "[es]", simplified] .

lemma lqueue_step_remove_llistI: "lqueue_step (Q, D) (remove_llist es Q, D \<union> lset es)"
  using lqueue_step_fold_remove_llistI[of _ _ "[es]", simplified] .

lemma llists_fold_add_llist[simp]: "llists (fold add_llist es Q) = mset es + llists Q"
  by (induct es arbitrary: Q) auto

lemma llists_fold_remove_llist[simp]: "llists (fold remove_llist es Q) = llists Q - mset es"
  by (induct es arbitrary: Q) auto

inductive pick_lqueue_step_details :: "'q \<times> 'e set \<Rightarrow> 'e \<Rightarrow> 'e llist \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_step_detailsI: "LCons e es \<in># llists Q \<Longrightarrow> fst (pick_elem Q) = e \<Longrightarrow>
    llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#} \<Longrightarrow>
    pick_lqueue_step_details (Q, D) e es (snd (pick_elem Q), D \<union> {e})"

inductive pick_lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_stepI: "pick_lqueue_step_details QD e es QD' \<Longrightarrow> pick_lqueue_step QD QD'"

inductive remove_lqueue_step_details :: "'q \<times> 'e set \<Rightarrow> 'e llist list \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  remove_lqueue_stepI:
    "remove_lqueue_step_details (Q, D) ess
       (fold remove_llist ess Q, D \<union> \<Union> {lset es |es. es \<in> set ess})"

end

locale fair_prover_lazy_list_queue =
  prover_lazy_list_queue empty add_llist remove_llist pick_elem llists
  for
    empty :: 'q and
    add_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove_llist :: "'e llist \<Rightarrow> 'q \<Rightarrow> 'q" and
    pick_elem :: "'q \<Rightarrow> 'e \<times> 'q" and
    llists :: "'q \<Rightarrow> 'e llist multiset" +
  assumes fair: "chain lqueue_step QDs \<Longrightarrow> infinitely_often pick_lqueue_step QDs \<Longrightarrow>
    LCons e es \<in># llists (fst (lnth QDs i)) \<Longrightarrow>
    \<exists>j \<ge> i. (\<exists>ess. LCons e es \<in> set ess
        \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j)))
      \<or>  pick_lqueue_step_details (lnth QDs j) e es (lnth QDs (Suc j))"
begin

lemma fair_strong:
  assumes
    chain: "chain lqueue_step QDs" and
    inf: "infinitely_often pick_lqueue_step QDs" and
    es_in: "es \<in># llists (fst (lnth QDs i))" and
    k_lt: "enat k < llength es"
  shows "\<exists>j \<ge> i.
    (\<exists>k' \<le> k. \<exists>ess. ldrop k' es \<in> set ess
         \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j)))
       \<or> pick_lqueue_step_details (lnth QDs j) (lnth es k) (ldrop (Suc k) es) (lnth QDs (Suc j))"
  using k_lt
proof (induct k)
  case 0
  note zero_lt = this
  have es_in': "LCons (lnth es 0) (ldrop (Suc 0) es) \<in># llists (fst (lnth QDs i))"
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
        \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j)))
      \<or> pick_lqueue_step_details (lnth QDs j) (lnth es k) (ldrop (enat (Suc k)) es)
        (lnth QDs (Suc j))"
    using ih[OF k_lt] by blast

  {
    assume "\<exists>k' \<le> k. \<exists>ess. ldrop (enat k') es \<in> set ess
      \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j))"
    hence ?case
      using j_ge le_SucI by blast
  }
  moreover
  {
    assume "pick_lqueue_step_details (lnth QDs j) (lnth es k) (ldrop (enat (Suc k)) es)
      (lnth QDs (Suc j))"
    hence cons_in: "LCons (lnth es (Suc k)) (ldrop (enat (Suc (Suc k))) es)
      \<in># llists (fst (lnth QDs (Suc j)))"
      unfolding pick_lqueue_step_details.simps using sk_lt
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
    chain: "chain lqueue_step QDs" and
    inf_pick: "infinitely_often pick_lqueue_step QDs" and
    cons_in: "LCons e es \<in># mset (fst (lnth QDs i))"

  {
    assume not_rem_step: "\<not> (\<exists>j \<ge> i. \<exists>ess. LCons e es \<in> set ess
      \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j)))"

    obtain k :: nat where
      k_lt: "k < length (fst (lnth QDs i))" and
      at_k: "fst (lnth QDs i) ! k = LCons e es"
      using cons_in by (metis in_set_conv_nth set_mset_mset)

    have "\<forall>k' \<le> k. \<exists>i' \<ge> i. LCons e es \<in># mset (take (Suc k') (fst (lnth QDs i')))"
    proof -
      have "\<exists>i' \<ge> i. LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs i')))" for l
      proof (induct l)
        case 0
        show ?case
        proof (rule exI[of _ i]; simp)
          show "LCons e es \<in> set (take (Suc k) (fst (lnth QDs i)))"
            by (simp add: at_k k_lt take_Suc_conv_app_nth)
        qed
      next
        case (Suc l)
        (* non_rem_step comes into play here *)
        show ?case
          sorry
      qed
      thus ?thesis
        by (metis diff_add_zero empty_iff list.set(1) set_mset_mset take0)
    qed
    then obtain i' :: nat where
      i'_ge: "i' \<ge> i" and
      cons_in_take: "LCons e es \<in># mset (take 1 (fst (lnth QDs i')))"
      by auto

    have "\<exists>j \<ge> i. pick_lqueue_step_details (lnth QDs j) e es (lnth QDs (Suc j))"
    proof (rule exI[of _ i'], intro conjI i'_ge)
      have cons_in: "LCons e es \<in># mset (fst (lnth QDs i'))"
        by (meson cons_in_take in_multiset_in_set in_set_takeD)
      hence hd: "hd (fst (lnth QDs i')) = LCons e es"
        using cons_in_take
        by (metis One_nat_def empty_iff empty_set hd_conv_nth length_greater_0_conv 
            self_append_conv2 set_ConsD set_mset_mset take0 take_Suc_conv_app_nth)
      hence fst_pick: "fst (pick_elem (fst (lnth QDs i'))) = e"
        by (metis cons_in empty_iff empty_set list.sel(1) neq_Nil_conv pick_elem.simps(3) prod.sel(1) set_mset_mset)

      have "fst (lnth QDs i') \<noteq> []"
        using cons_in by fastforce
      hence snd_pick: "mset (snd (pick_elem (fst (lnth QDs i')))) =
        mset (fst (lnth QDs i')) - {#LCons e es#} + {#es#}"
        using pick_elem.simps(3)
        by (metis hd add_mset_add_mset_same_iff cons_in insert_DiffM list.exhaust_sel
            llists_add mset.simps(2) snd_conv)

(* FIXME
      have "lqueue_step (fst (lnth QDs i') (lnth QDs (Suc i))"
        sorry
*)

      have fst_at_si': "fst (lnth QDs (Suc i')) = snd (pick_elem (fst (lnth QDs i')))"
        sorry

      have snd_at_si': "snd (lnth QDs (Suc i')) = snd (lnth QDs i') \<union> {e}"
        sorry

      show "pick_lqueue_step_details (lnth QDs i') e es (lnth QDs (Suc i'))"
        using pick_lqueue_step_detailsI[OF cons_in fst_pick snd_pick, of "snd (lnth QDs i')"]
        unfolding fst_at_si'[symmetric] snd_at_si'[symmetric] by simp
    qed
  }
  thus "\<exists>j \<ge> i.
      (\<exists>ess. LCons e es \<in> set ess \<and> remove_lqueue_step_details (lnth QDs j) ess (lnth QDs (Suc j)))
    \<or> pick_lqueue_step_details (lnth QDs j) e es (lnth QDs (Suc j))"
    by blast
qed

end

end
