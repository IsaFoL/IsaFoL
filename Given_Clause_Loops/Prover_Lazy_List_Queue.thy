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


subsection \<open>Basic Lemmas\<close>

lemma ne_and_in_set_take_imp_in_set_take_remove:
  assumes
    "z \<noteq> y" and
    "z \<in> set (take m xs)"
  shows "z \<in> set (take m (remove1 y xs))"
  using assms
proof (induct xs arbitrary: m)
  case (Cons x xs)
  note ih = this(1) and z_ne_y = this(2) and z_in_take_xxs = this(3)

  show ?case
  proof (cases "z = x")
    case True
    thus ?thesis
      by (metis (no_types, lifting) List.hd_in_set gr_zeroI hd_take in_set_remove1 list.sel(1)
          remove1.simps(2) take_eq_Nil z_in_take_xxs z_ne_y)
  next
    case z_ne_x: False

    have z_in_take_xs: "z \<in> set (take m xs)"
      using z_in_take_xxs z_ne_x
      by (smt (verit, del_insts) butlast_take in_set_butlastD in_set_takeD le_cases3 set_ConsD
          take_Cons' take_all)

    show ?thesis
    proof (cases "y = x")
      case y_eq_x: True
      show ?thesis
        using y_eq_x by (simp add: z_in_take_xs)
    next
      case y_ne_x: False

      have "m > 0"
        by (metis gr0I list.set_cases list.simps(3) take_Cons' z_in_take_xxs)
      then obtain m' :: nat where
        m: "m = Suc m'"
        using gr0_implies_Suc by presburger

      have z_in_take_xs': "z \<in> set (take m' xs)"
        using z_in_take_xs z_in_take_xxs z_ne_x by (simp add: m)
      note ih = ih[OF z_ne_y z_in_take_xs']

      show ?thesis
        using y_ne_x ih unfolding m by simp
    qed
  qed
qed simp

lemma in_set_take_imp_in_set_take_fold_append_single:
  assumes "x \<in> set (take n xs)"
  shows "x \<in> set (take n (fold (\<lambda>y ys. ys @ [y]) ys xs))"
  using assms by (induct ys arbitrary: xs) auto

lemma notin_set_and_in_set_take_imp_in_set_take_fold_remove1:
  assumes
    "x \<notin> set ys" and
    "x \<in> set (take m xs)"
  shows "x \<in> set (take m (fold remove1 ys xs))"
  using assms
proof (induct ys arbitrary: xs)
  case (Cons y ys xs)
  note ih = this(1) and x_ni_yys = this(2) and x_in_take_xs = this(3)

  have x_ne_y: "x \<noteq> y"
    using x_ni_yys by simp

  have x_ni_ys: "x \<notin> set ys"
    using x_ni_yys by simp
  have x_in_take_rem_y_xs: "x \<in> set (take m (remove1 y xs))"
    using x_in_take_xs x_ne_y using ne_and_in_set_take_imp_in_set_take_remove by fast
  note ih = ih[OF x_ni_ys x_in_take_rem_y_xs]

  show ?case
    using ih by simp
qed simp


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

type_synonym 'e fifo = "nat \<times> ('e \<times> 'e llist) list"

locale fifo_prover_lazy_list_queue
begin

definition empty :: "'e fifo" where
  "empty = (0, [])"

fun add_llist :: "'e llist \<Rightarrow> 'e fifo \<Rightarrow> 'e fifo" where
  "add_llist LNil (num_nils, ps) = (num_nils + 1, ps)"
| "add_llist (LCons e es) (num_nils, ps) = (num_nils, ps @ [(e, es)])"

fun remove_llist :: "'e llist \<Rightarrow> 'e fifo \<Rightarrow> 'e fifo" where
  "remove_llist LNil (num_nils, ps) = (num_nils - 1, ps)"
| "remove_llist (LCons e es) (num_nils, ps) = (num_nils, remove1 (e, es) ps)"

fun pick_elem :: "'e fifo \<Rightarrow> 'e \<times> 'e fifo" where
  "pick_elem (_, []) = undefined"
| "pick_elem (num_nils, (e, es) # ps) =
   (e,
    (case es of
      LNil \<Rightarrow> (num_nils + 1, ps)
    | LCons e' es' \<Rightarrow> (num_nils, ps @ [(e', es')])))"

fun llists :: "'e fifo \<Rightarrow> 'e llist multiset" where
  "llists (num_nils, ps) = replicate_mset num_nils LNil + mset (map (\<lambda>(e, es). LCons e es) ps)"

sublocale prover_lazy_list_queue empty add_llist remove_llist pick_elem llists
proof
  show "llists empty = {#}"
    unfolding empty_def by simp
next
  fix Q :: "'e fifo"
  assume nemp: "Q \<noteq> empty"
  thus "llists Q \<noteq> {#}"
  proof (cases Q)
    case q: (Pair num_nils ps)
    show ?thesis
      using nemp unfolding q empty_def by auto
  qed
next
  fix es :: "'e llist" and Q :: "'e fifo"
  show "llists (add_llist es Q) = llists Q + {#es#}"
    by (cases Q, cases es) auto
next
  fix es :: "'e llist" and Q :: "'e fifo"
  show "llists (remove_llist es Q) = llists Q - {#es#}"
  proof (cases Q)
    case q: (Pair num_nils ps)
    show ?thesis
    proof (cases es)
      case LNil
      note es = this
      have inter_emp: "{#LCons x y. (x, y) \<in># mset ps#} \<inter># {#LNil#} = {#}"
        by auto
      show ?thesis
      proof (cases num_nils)
        case num_nils: 0
        have nil_ni: "LNil \<notin># {#LCons x y. (x, y) \<in># mset ps#}"
          by auto
        show ?thesis
          unfolding q es num_nils by (auto simp: diff_single_trivial[OF nil_ni])
      next
        case num_nils: (Suc n)
        show ?thesis
          unfolding q es num_nils by auto
      qed
    next
      case (LCons e es')
      note es = this
      show ?thesis
      proof (cases "(e, es') \<in># mset ps")
        case pair_in: True
        show ?thesis
          unfolding q es using pair_in by (auto simp: multiset_union_diff_assoc image_mset_Diff)
      next
        case pair_ni: False
        have cons_ni:
          "LCons e es' \<notin># replicate_mset num_nils LNil + {#LCons x y. (x, y) \<in># mset ps#}"
          using pair_ni by auto
        show ?thesis
          unfolding q es using pair_ni cons_ni by (auto simp: diff_single_trivial)
      qed
    qed
  qed
next
  fix Q :: "'e fifo"
  assume nnil: "\<exists>es \<in># llists Q. es \<noteq> LNil"
  show "\<exists>e es. LCons e es \<in># llists Q \<and> fst (pick_elem Q) = e \<and> llists (snd (pick_elem Q)) = llists Q - {#LCons e es#} + {#es#}"
    using nnil
  proof (cases Q)
    case q: (Pair num_nils ps)
    show ?thesis
    proof (cases ps)
      case ps: Nil
      have False
        using nnil unfolding q ps by (cases "num_nils = 0") auto
      thus ?thesis
        by blast
    next
      case ps: (Cons p ps')
      show ?thesis
      proof (rule exI[of _ "fst p"], rule exI[of _ "snd p"]; intro conjI)
        show "LCons (fst p) (snd p) \<in># llists Q"
          unfolding q ps by (cases p) auto
      next
        show "fst (pick_elem Q) = fst p"
          unfolding q ps by (cases p) auto
      next
        show "llists (snd (pick_elem Q)) = llists Q - {#LCons (fst p) (snd p)#} + {#snd p#}"
        proof (cases p)
          case p: (Pair e es)
          show ?thesis
          proof (cases es)
            case es: LNil
            show ?thesis
              unfolding q ps p es by simp
          next
            case es: (LCons e' es')
            show ?thesis
              unfolding q ps p es by simp
          qed
        qed
      qed
    qed
  qed
qed

sublocale fair_prover_lazy_list_queue empty add_llist remove_llist pick_elem llists
proof
  fix
    QDs :: "('e fifo \<times> 'e set) llist" and
    e :: 'e and
    es :: "'e llist" and
    i :: nat
  assume
    chain: "chain lqueue_step QDs" and
    inf_pick: "infinitely_often pick_lqueue_step QDs" and
    cons_in: "LCons e es \<in># llists (fst (lnth QDs i))"

  have len: "llength QDs = \<infinity>"
    using inf_pick unfolding infinitely_often_alt_def
    by (metis Suc_ile_eq dual_order.strict_implies_order enat.exhaust enat_ord_simps(2)
        verit_comp_simplify1(3))

  {
    assume not_rem_step: "\<not> (\<exists>j \<ge> i. \<exists>ess. LCons e es \<in> set ess
      \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))"

(*
    obtain k :: nat where
      k_lt: "k < length (fst (lnth QDs i))" and
      at_k: "fst (lnth QDs i) ! k = LCons e es"
      using cons_in by (metis in_set_conv_nth set_mset_mset)

    have "\<forall>k' \<le> k. \<exists>i' \<ge> i. LCons e es \<in># mset (take (Suc k') (fst (lnth QDs i')))"
    proof -
      have "\<exists>i' \<ge> i. LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs i')))"
        if l_le: "l \<le> k" for l
        using l_le
      proof (induct l)
        case 0
        show ?case
        proof (rule exI[of _ i]; simp)
          show "LCons e es \<in> set (take (Suc k) (fst (lnth QDs i)))"
            by (simp add: at_k k_lt take_Suc_conv_app_nth)
        qed
      next
        case (Suc l)
        note ih = this(1) and sl_le = this(2)

        have l_le_k: "l \<le> k"
          using sl_le by linarith
        note ih = ih[OF l_le_k]

        obtain i' :: nat where
          i'_ge: "i' \<ge> i" and
          cons_at_i': "LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs i')))"
          using ih by blast
        then obtain j0 :: nat where
          "j0 \<ge> i'" and
          "pick_lqueue_step (lnth QDs j0) (lnth QDs (Suc j0))"
          using inf_pick unfolding infinitely_often_alt_def by auto
        then obtain j :: nat where
          j_ge: "j \<ge> i'" and
          pick_step: "pick_lqueue_step (lnth QDs j) (lnth QDs (Suc j))" and
          pick_step_min:
          "\<forall>j'. j' \<ge> i' \<longrightarrow> j' < j \<longrightarrow> \<not> pick_lqueue_step (lnth QDs j') (lnth QDs (Suc j'))"
          using wfP_exists_minimal[OF wfP_less, of
              "\<lambda>j. j \<ge> i' \<and> pick_lqueue_step (lnth QDs j) (lnth QDs (Suc j))" j0 "\<lambda>j. j"]
          by blast

        have cons_at_le_j: "LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs j')))"
          if j'_ge: "j' \<ge> i'" and j'_le: "j' \<le> j" for j'
        proof -
          have "LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs (i' + m))))"
            if i'm_le: "i' + m \<le> j" for m
            using i'm_le
          proof (induct m)
            case 0
            then show ?case
              using cons_at_i' by fastforce
          next
            case (Suc m)
            note ih = this(1) and i'sm_le = this(2)

            have i'm_lt: "i' + m < j"
              using i'sm_le by linarith
            have i'm_le: "i' + m \<le> j"
              using i'sm_le by linarith
            note ih = ih[OF i'm_le]

            have step: "lqueue_step (lnth QDs (i' + m)) (lnth QDs (i' + Suc m))"
              by (simp add: chain chain_lnth_rel len)

            show ?case
              using step
            proof cases
              case (lqueue_step_fold_add_llistI Q D ess)
              note defs = this
              show ?thesis
                using ih unfolding defs
                by (auto intro: in_set_take_imp_in_set_take_fold_append_single)
            next
              case (lqueue_step_fold_remove_llistI Q D ess)
              note defs = this
              have "remove_lqueue_step_w_details (lnth QDs (i' + m)) ess (lnth QDs (i' + Suc m))"
                unfolding defs by (rule remove_lqueue_step_w_detailsI)
              hence "LCons e es \<notin> set ess"
                using not_rem_step i'_ge by force
              thus ?thesis
                using ih unfolding defs
                by (auto intro: notin_set_and_in_set_take_imp_in_set_take_fold_remove1)
            next
              case (lqueue_step_pick_elemI Q D)
              note defs = this(1,2) and rest = this(3)

              have "pick_lqueue_step (lnth QDs (i' + m)) (lnth QDs (i' + Suc m))"
              proof -
                have "\<exists>e es. pick_lqueue_step_w_details (lnth QDs (i' + m)) e es
                  (lnth QDs (i' + Suc m))"
                  unfolding defs using pick_lqueue_step_w_detailsI
                  by (metis add_Suc_right llists_pick_elem lqueue_step_pick_elemI(2) rest)
                thus ?thesis
                  using pick_lqueue_stepI by fast
              qed

              thm pick_step_min[rule_format, OF le_add1]

              moreover have "\<not> pick_lqueue_step (lnth QDs (i' + m)) (lnth QDs (i' + Suc m))"
                using pick_step_min[rule_format, OF le_add1 i'm_lt] by simp
              ultimately show ?thesis
                by blast
            qed
          qed
          thus ?thesis
            by (metis j'_ge j'_le nat_le_iff_add)
        qed

        show ?case
        proof (rule exI[of _ "Suc j"], intro conjI)
          show "i \<le> Suc j"
            using i'_ge j_ge by linarith
        next
          obtain Q :: "'e llist list" and D :: "'e set" and e' :: 'e and es' :: "'e llist" where
            at_j: "lnth QDs j = (Q, D)" and
            at_sj: "lnth QDs (Suc j) = (snd (pick_elem Q), D \<union> {e'})" and
            pair_in: "LCons e' es' \<in># mset Q" and
            fst: "fst (pick_elem Q) = e'" and
            snd: "mset (snd (pick_elem Q)) = mset Q - {#LCons e' es'#} + {#es'#}"
            using pick_step unfolding pick_lqueue_step.simps pick_lqueue_step_w_details.simps
            by blast

          have cons_at_j: "LCons e es \<in># mset (take (k + 1 - l) (fst (lnth QDs j)))"
            using cons_at_le_j[of j] j_ge by blast

          show "LCons e es \<in># mset (take (k + 1 - Suc l) (fst (lnth QDs (Suc j))))"
            using cons_at_j unfolding at_j at_sj

            sorry
        qed
      qed
      thus ?thesis
        by (metis Suc_eq_plus1 add_right_mono diff_Suc_Suc diff_diff_cancel diff_le_self)
    qed
    then obtain i' :: nat where
      i'_ge: "i' \<ge> i" and
      cons_at_i': "LCons e es \<in># mset (take 1 (fst (lnth QDs i')))"
      by auto
    then obtain j0 :: nat where
      "j0 \<ge> i'" and
      "pick_lqueue_step (lnth QDs j0) (lnth QDs (Suc j0))"
      using inf_pick unfolding infinitely_often_alt_def by auto
    then obtain j :: nat where
      j_ge: "j \<ge> i'" and
      pick_step: "pick_lqueue_step (lnth QDs j) (lnth QDs (Suc j))" and
      pick_step_min:
        "\<forall>j'. j' \<ge> i' \<longrightarrow> j' < j \<longrightarrow> \<not> pick_lqueue_step (lnth QDs j') (lnth QDs (Suc j'))"
      using wfP_exists_minimal[OF wfP_less, of
         "\<lambda>j. j \<ge> i' \<and> pick_lqueue_step (lnth QDs j) (lnth QDs (Suc j))" j0 "\<lambda>j. j"]
      by blast
    hence pick_step_det: "\<exists>e es. pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
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

      obtain Q' :: "'e llist list" where
        fst_at_j: "fst (lnth QDs j) = LCons e es # Q'"
        using cons_at_j by (metis (no_types, lifting) One_nat_def cons_in_fst empty_iff empty_set
            fifo_prover_lazy_list_queue.pick_elem.elims length_pos_if_in_set nth_Cons_0
            self_append_conv2 set_ConsD set_mset_mset take0 take_Suc_conv_app_nth)

      have fst_pick: "fst (pick_elem (fst (lnth QDs j))) = e"
        unfolding fst_at_j by simp
      have snd_pick: "mset (snd (pick_elem (fst (lnth QDs j)))) =
        mset (fst (lnth QDs j)) - {#LCons e es#} + {#es#}"
        unfolding fst_at_j by simp

      show ?thesis
        using cons_in_fst fst_pick snd_pick
        by (smt (verit, ccfv_SIG) pick_step_det fst_conv pick_lqueue_step_w_details.simps)
    qed
*)
    hence "\<exists>j \<ge> i. pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
      (* using i'_ge j_ge le_trans by blast *)
      sorry
  }
  thus "\<exists>j \<ge> i.
      (\<exists>ess. LCons e es \<in> set ess \<and> remove_lqueue_step_w_details (lnth QDs j) ess (lnth QDs (Suc j)))
    \<or> pick_lqueue_step_w_details (lnth QDs j) e es (lnth QDs (Suc j))"
    by blast
qed

end

end
