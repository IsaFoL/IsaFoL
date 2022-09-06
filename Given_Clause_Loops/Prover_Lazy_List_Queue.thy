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

inductive pick_lqueue_step_w_details :: "'q \<times> 'e set \<Rightarrow> 'e \<Rightarrow> 'e llist \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_step_w_detailsI: "LCons e es \<in># llists Q \<Longrightarrow> fst (pick_elem Q) = e \<Longrightarrow>
    llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#} \<Longrightarrow>
    pick_lqueue_step_w_details (Q, D) e es (snd (pick_elem Q), D \<union> {e})"

inductive pick_lqueue_step :: "'q \<times> 'e set \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool" where
  pick_lqueue_stepI: "pick_lqueue_step_w_details QD e es QD' \<Longrightarrow> pick_lqueue_step QD QD'"

inductive
  remove_lqueue_step_w_details :: "'q \<times> 'e set \<Rightarrow> 'e llist list \<Rightarrow> 'q \<times> 'e set \<Rightarrow> bool"
where
  remove_lqueue_step_w_detailsI:
    "remove_lqueue_step_w_details (Q, D) ess
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
        \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
      \<or> pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
begin

lemma fair_strong:
  assumes
    chain: "chain lqueue_step QDs" and
    inf: "infinitely_often pick_lqueue_step QDs" and
    es_in: "es \<in># llists (fst (lnth QDs i))" and
    k_lt: "enat k < llength es"
  shows "\<exists>j \<ge> i.
    (\<exists>k' \<le> k. \<exists>ess. ldrop k' es \<in> set ess
         \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
       \<or> pick_lqueue_step_w_details (lnth QDs j) (lnth es k) (ldrop (Suc k) es) (lnth QDs (Suc j))"
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
      \<in># llists (fst (lnth QDs (Suc j)))"
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

  have len: "llength QDs = \<infinity>"
    using inf_pick unfolding infinitely_often_alt_def
    by (metis Suc_ile_eq dual_order.strict_implies_order enat.exhaust enat_ord_simps(2)
        verit_comp_simplify1(3))

  {
    assume not_rem_step: "\<not> (\<exists>j \<ge> i. \<exists>ess. LCons e es \<in> set ess
      \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))"

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
      cons_at_i': "LCons e es \<in># mset (take 1 (fst (lnth QDs i')))"
      by auto
    then obtain j0 :: nat where
      j_ge: "j0 \<ge> i'" and
      "pick_lqueue_step (lnth QDs j0) (lnth QDs (Suc j0))"
      using inf_pick unfolding infinitely_often_alt_def by auto
    then obtain j :: nat where
      j_ge: "j \<ge> i'" and
      pick_step: "pick_lqueue_step (lnth QDs j) (lnth QDs (Suc j))" and
      pick_step_min:
        "\<forall>j'. j' \<ge> i' \<longrightarrow> j' < j \<longrightarrow> \<not> pick_lqueue_step (lnth QDs j') (lnth QDs (Suc j'))"
      using wf_eq_minimal
      sorry
    hence pick_step: "\<exists>e es. pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
      unfolding pick_lqueue_step.simps by simp
    have "pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
    proof -
      have cons_at_j: "LCons e es \<in># mset (take 1 (fst (lnth QDs j)))"
      proof -
        have "LCons e es \<in># mset (take 1 (fst (lnth QDs (i' + l))))" if i'l_le: "i' + l \<le> j" for l
          using i'l_le
        proof (induct l)
          case (Suc l)
          note ih = this(1) and i'sl_le = this(2)

          have i'l_lt: "i' + l < j"
            using i'sl_le by linarith
          have i'l_le: "i' + l \<le> j"
            using i'sl_le by linarith
          note ih = ih[OF i'l_le]

          have step: "lqueue_step (lnth QDs (i' + l)) (lnth QDs (i' + Suc l))"
            by (simp add: chain chain_lnth_rel len)

          show ?case
            using step
          proof cases
            case (lqueue_step_fold_add_llistI Q D ess)
            note defs = this

            have len_q: "length Q \<ge> 1"
              using ih by (metis Suc_eq_plus1 add.commute empty_iff le_add1 length_0_conv list.set(1)
                  list_decode.cases local.lqueue_step_fold_add_llistI(1) prod.sel(1) set_mset_mset
                  take.simps(1))

            have take: "take (Suc 0) (fold (\<lambda>es ess. ess @ [es]) ess Q) = take (Suc 0) Q"
              using len_q
            proof (induct ess arbitrary: Q)
              case (Cons es ess)
              note ih = this(1) and len_q = this(2)
              show ?case
                using len_q by (simp add: ih)
            qed auto

            show ?thesis
              unfolding defs using ih take
              by simp (metis local.lqueue_step_fold_add_llistI(1) prod.sel(1))
          next
            case (lqueue_step_fold_remove_llistI Q D ess)
            note defs = this

            have "remove_lqueue_step_w_details (lnth QDs (i' + l)) ess (lnth QDs (i' + Suc l))"
              unfolding defs by (rule remove_lqueue_step_w_detailsI)
            moreover have "\<not> (\<exists>ess. LCons e es \<in> set ess
              \<and> remove_lqueue_step_w_details (lnth QDs (i' + l)) ess (lnth QDs (i' + Suc l)))"
              using not_rem_step add_Suc_right i'_ge trans_le_add1 by presburger
            ultimately have ees_ni: "LCons e es \<notin> set ess"
              by blast

            obtain Q' :: "'e llist list" where
              q: "Q = LCons e es # Q'"
              using ih by (metis One_nat_def fst_eqD in_set_member in_set_takeD length_pos_if_in_set
                  list.exhaust_sel lqueue_step_fold_remove_llistI(1) member_rec nth_Cons_0
                  set_mset_mset take0 take_Suc_conv_app_nth)

            have take_1: "take 1 (fold remove1 ess Q) = take 1 Q"
              unfolding q using ees_ni
            proof (induct ess arbitrary: Q')
              case (Cons es' ess')
              note ih = this(1) and ees_ni = this(2)

              have ees_ni': "LCons e es \<notin> set ess'"
                using ees_ni by simp
              note ih = ih[OF ees_ni']

              have "es' \<noteq> LCons e es"
                using ees_ni by auto
              thus ?case
                using ih by simp
            qed auto

            show ?thesis
              unfolding defs using ih take_1
              by simp (metis lqueue_step_fold_remove_llistI(1) prod.sel(1))
          next
            case (lqueue_step_pick_elemI Q D)
            note defs = this(1,2) and rest = this(3)

            have "pick_lqueue_step (lnth QDs (i' + l)) (lnth QDs (Suc (i' + l)))"
            proof -
              have "\<exists>e es. pick_lqueue_step_w_details (lnth QDs (i' + l)) e es
                (lnth QDs (Suc (i' + l)))"
                unfolding defs using pick_lqueue_step_w_detailsI
                by (metis add_Suc_right llists_pick_elem lqueue_step_pick_elemI(2) rest)
              thus ?thesis
                using pick_lqueue_stepI by fast
            qed
            moreover have "\<not> pick_lqueue_step (lnth QDs (i' + l)) (lnth QDs (Suc (i' + l)))"
              using pick_step_min[rule_format, OF le_add1 i'l_lt] .
            ultimately show ?thesis
              by blast
          qed
        qed (use cons_at_i' in auto)
        thus ?thesis
          by (metis dual_order.refl j_ge nat_le_iff_add)
      qed
      hence cons_in_fst: "LCons e es \<in># mset (fst (lnth QDs j))"
        using in_set_takeD by force

      have fst_pick: "fst (pick_elem (fst (lnth QDs j))) = e"
        by (smt (verit, del_insts) One_nat_def cons_at_j empty_iff empty_set fst_conv
            in_multiset_in_set length_pos_if_in_set llist.inject llist.simps(3) nth_Cons_0
            pick_elem.elims pick_lqueue_step_w_details.cases pick_step self_append_conv2 set_ConsD
            take0 take_Suc_conv_app_nth)

      have snd_pick: "mset (snd (pick_elem (fst (lnth QDs j)))) =
        mset (fst (lnth QDs j)) - {#LCons e es#} + {#es#}"
        sorry

      show ?thesis
        using cons_in_fst fst_pick snd_pick
        by (smt (verit, ccfv_SIG) pick_step fst_conv pick_lqueue_step_w_details.simps)
    qed

    have "\<exists>j \<ge> i. pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
    proof (rule exI[of _ i'], intro conjI i'_ge)
      have cons_in: "LCons e es \<in># mset (fst (lnth QDs i'))"
        by (meson cons_at_i' in_multiset_in_set in_set_takeD)
      hence hd: "hd (fst (lnth QDs i')) = LCons e es"
        using cons_at_i'
        by (metis One_nat_def empty_iff empty_set hd_conv_nth length_greater_0_conv 
            self_append_conv2 set_ConsD set_mset_mset take0 take_Suc_conv_app_nth)
      hence fst_pick: "fst (pick_elem (fst (lnth QDs i'))) = e"
        by (metis cons_in empty_iff empty_set list.sel(1) neq_Nil_conv pick_elem.simps(3)
            prod.sel(1) set_mset_mset)

      have "fst (lnth QDs i') \<noteq> []"
        using cons_in by fastforce
      hence snd_pick: "mset (snd (pick_elem (fst (lnth QDs i')))) =
        mset (fst (lnth QDs i')) - {#LCons e es#} + {#es#}"
        using pick_elem.simps(3)
        by (metis hd add_mset_add_mset_same_iff cons_in insert_DiffM list.exhaust_sel llists_add
            mset.simps(2) snd_conv)

      have step: "lqueue_step (lnth QDs i') (lnth QDs (Suc i'))"
        by (simp add: chain chain_lnth_rel len)

      have at_si': "lnth QDs (Suc i') =
        (snd (pick_elem (fst (lnth QDs i'))), snd (lnth QDs i') \<union> {e})"
        using step
      proof cases
        case (lqueue_step_fold_add_llistI Q D ess)
        have False
          sorry
        thus ?thesis
          by blast
      next
        case (lqueue_step_fold_remove_llistI Q D ess)
        have False
          sorry
        thus ?thesis
          by blast
      next
        case (lqueue_step_pick_elemI Q D)
        thus ?thesis
          sorry
      qed

      show "pick_lqueue_step_w_details (lnth QDs i') e es (lnth QDs (Suc i'))"
        using pick_lqueue_step_w_detailsI[OF cons_in fst_pick snd_pick, of "snd (lnth QDs i')"]
        unfolding at_si'[symmetric] by simp
    qed
  }
  thus "\<exists>j \<ge> i.
      (\<exists>ess. LCons e es \<in> set ess \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
    \<or> pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
    by blast
qed

end

end
