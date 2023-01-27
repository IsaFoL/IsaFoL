(* Title:        Prover Queue and Fairness
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Prover Queues and Fairness\<close>

text \<open>This section covers the passive set data structure that arises in
different prover loops in the literature (e.g., DISCOUNT, Otter).\<close>

theory Prover_Queue
  imports
    Given_Clause_Loops_Util
    Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Basic Lemmas\<close>

lemma set_drop_fold_maybe_append_singleton:
  "set (drop k (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) ys xs)) \<subseteq> set (drop k (xs @ ys))"
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  note ih = this(1)
  show ?case
  proof (cases "y \<in> set xs")
    case True
    thus ?thesis
      using ih[of xs] set_drop_append_cons[of k xs ys y] by auto
  next
    case False
    then show ?thesis
      using ih[of "xs @ [y]"]
      by simp
  qed
qed simp

lemma fold_maybe_append_removeAll:
  assumes "y \<in> set xs"
  shows "fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) (removeAll y ys) xs =
    fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) ys xs"
  using assms by (induct ys arbitrary: xs) auto


subsection \<open>More on Relational Chains over Lazy Lists\<close>

definition finitely_often :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "finitely_often R xs \<longleftrightarrow>
   (\<exists>i. \<forall>j. i \<le> j \<longrightarrow> enat (Suc j) < llength xs \<longrightarrow> \<not> R (lnth xs j) (lnth xs (Suc j)))"

abbreviation infinitely_often :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "infinitely_often R xs \<equiv> \<not> finitely_often R xs"

lemma infinitely_often_alt_def:
  "infinitely_often R xs \<longleftrightarrow>
   (\<forall>i. \<exists>j. i \<le> j \<and> enat (Suc j) < llength xs \<and> R (lnth xs j) (lnth xs (Suc j)))"
  unfolding finitely_often_def by blast

lemma infinitely_often_lifting:
  assumes
    r_imp_s: "\<forall>x x'. R (f x) (f x') \<longrightarrow> S (g x) (g x')" and
    inf_r: "infinitely_often R (lmap f xs)"
  shows "infinitely_often S (lmap g xs)"
  using inf_r unfolding infinitely_often_alt_def
  by (metis Suc_ile_eq llength_lmap lnth_lmap order_less_imp_le r_imp_s)


subsection \<open>Locales\<close>

text \<open>The passive set of a given clause prover can be organized in different
ways—e.g., as a priority queue or as a list of queues. This locale abstracts
over the specific data structure.\<close>

locale prover_queue =
  fixes
    empty :: 'q and
    select :: "'q \<Rightarrow> 'e" and
    add :: "'e \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove :: "'e \<Rightarrow> 'q \<Rightarrow> 'q" and
    felems :: "'q \<Rightarrow> 'e fset"
  assumes
    felems_empty[simp]: "felems empty = {||}" and
    felems_not_empty: "Q \<noteq> empty \<Longrightarrow> felems Q \<noteq> {||}" and
    select_in_felems[simp]: "Q \<noteq> empty \<Longrightarrow> select Q |\<in>| felems Q" and
    felems_add[simp]: "felems (add e Q) = {|e|} |\<union>| felems Q" and
    felems_remove[simp]: "felems (remove e Q) = felems Q |-| {|e|}" and
    add_again: "e |\<in>| felems Q \<Longrightarrow> add e Q = Q"
begin

abbreviation elems :: "'q \<Rightarrow> 'e set" where
  "elems Q \<equiv> fset (felems Q)"

lemma elems_empty: "elems empty = {}"
  by simp

lemma formula_not_empty[simp]: "Q \<noteq> empty \<Longrightarrow> elems Q \<noteq> {}"
  by (metis bot_fset.rep_eq felems_not_empty fset_cong)

lemma select_in_elems[simp]: "Q \<noteq> empty \<Longrightarrow> select Q \<in> elems Q"
  by (metis fmember.rep_eq select_in_felems)

lemma
  elems_add: "elems (add e Q) = {e} \<union> elems Q" and
  elems_remove: "elems (remove e Q) = elems Q - {e}"
  by simp+

lemma elems_fold_add[simp]: "elems (fold add es Q) = set es \<union> elems Q"
  by (induct es arbitrary: Q) auto

lemma elems_fold_remove[simp]: "elems (fold remove es Q) = elems Q - set es"
  by (induct es arbitrary: Q) auto

inductive queue_step :: "'q \<Rightarrow> 'q \<Rightarrow> bool" where
  queue_step_fold_addI: "queue_step Q (fold add es Q)"
| queue_step_fold_removeI: "queue_step Q (fold remove es Q)"

lemma queue_step_idleI: "queue_step Q Q"
  using queue_step_fold_addI[of _ "[]", simplified] .

lemma queue_step_addI: "queue_step Q (add e Q)"
  using queue_step_fold_addI[of _ "[e]", simplified] .

lemma queue_step_removeI: "queue_step Q (remove e Q)"
  using queue_step_fold_removeI[of _ "[e]", simplified] .

inductive select_queue_step :: "'q \<Rightarrow> 'q \<Rightarrow> bool" where
  select_queue_stepI: "Q \<noteq> empty \<Longrightarrow> select_queue_step Q (remove (select Q) Q)"

end

locale fair_prover_queue = prover_queue empty select add remove felems
  for
    empty :: "'q" and
    select :: "'q \<Rightarrow> 'e" and
    add :: "'e \<Rightarrow> 'q \<Rightarrow> 'q" and
    remove :: "'e \<Rightarrow> 'q \<Rightarrow> 'q" and
    felems :: "'q \<Rightarrow> 'e fset" +
  assumes fair: "chain queue_step Qs \<Longrightarrow> infinitely_often select_queue_step Qs \<Longrightarrow>
    lhd Qs = empty \<Longrightarrow> Liminf_llist (lmap elems Qs) = {}"
begin
end


subsection \<open>Instantiation with FIFO Queue\<close>

text \<open>As a proof of concept, we show that a FIFO queue can serve as a fair
prover queue.\<close>

locale fifo_prover_queue
begin

sublocale prover_queue "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list
proof
  show "\<And>Q. Q \<noteq> [] \<Longrightarrow> fset_of_list Q \<noteq> {||}"
    by (metis fset_of_list.rep_eq fset_simps(1) set_empty)
qed (auto simp: fset_of_list_elem)

lemma queue_step_preserves_distinct:
  assumes
    dist: "distinct Q" and
    step: "queue_step Q Q'"
  shows "distinct Q'"
  using step
proof cases
  case (queue_step_fold_addI es)
  note p' = this(1)
  show ?thesis
    unfolding p'
    using dist
  proof (induct es arbitrary: Q)
    case Nil
    then show ?case
      using dist by auto
  next
    case (Cons e es)
    note ih = this(1) and dist_p = this(2)

    show ?case
    proof (cases "e \<in> set Q")
      case True
      then show ?thesis
        using ih[OF dist_p] by simp
    next
      case c_ni: False
      have dist_pc: "distinct (Q @ [e])"
        using c_ni dist_p by auto
      show ?thesis
        using c_ni using ih[OF dist_pc] by simp
    qed
  qed
next
  case (queue_step_fold_removeI es)
  note p' = this(1)
  show ?thesis
    unfolding p' using dist by (simp add: distinct_fold_removeAll)
qed

lemma chain_queue_step_preserves_distinct:
  assumes
    chain: "chain queue_step Qs" and
    dist_hd: "distinct (lhd Qs)" and
    i_lt: "enat i < llength Qs"
  shows "distinct (lnth Qs i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using dist_hd chain_length_pos[OF chain] by (simp add: lhd_conv_lnth)
next
  case (Suc i)

  have ih: "distinct (lnth Qs i)"
    using Suc.hyps Suc.prems Suc_ile_eq order_less_imp_le by blast

  have "queue_step (lnth Qs i) (lnth Qs (Suc i))"
    by (rule chain_lnth_rel[OF chain Suc.prems])
  then show ?case
    using queue_step_preserves_distinct ih by blast
qed

sublocale fair_prover_queue "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll
  fset_of_list
proof
  fix Qs :: "'e list llist"
  assume
    chain: "chain queue_step Qs" and
    inf_sel: "infinitely_often select_queue_step Qs" and
    hd_emp: "lhd Qs = []"

  show "Liminf_llist (lmap elems Qs) = {}"
  proof (rule ccontr)
    assume lim_nemp: "Liminf_llist (lmap elems Qs) \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Qs" and
      inter_nemp: "\<Inter> ((set \<circ> lnth Qs) ` {j. i \<le> j \<and> enat j < llength Qs}) \<noteq> {}"
      using lim_nemp unfolding Liminf_llist_def by auto

    from inter_nemp obtain e :: 'e where
      "\<forall>Q \<in> lnth Qs ` {j. i \<le> j \<and> enat j < llength Qs}. e \<in> set Q"
      by auto
    hence c_in: "\<forall>j \<ge> i. enat j < llength Qs \<longrightarrow> e \<in> set (lnth Qs j)"
      by auto

    have ps_inf: "llength Qs = \<infinity>"
    proof (rule ccontr)
      assume "llength Qs \<noteq> \<infinity>"
      obtain n :: nat where
        n: "enat n = llength Qs"
        using \<open>llength Qs \<noteq> \<infinity>\<close> by force

      show False
        using inf_sel[unfolded infinitely_often_alt_def]
        by (metis Suc_lessD enat_ord_simps(2) less_le_not_le n)
    qed

    have c_in': "\<forall>j \<ge> i. e \<in> set (lnth Qs j)"
      by (simp add: c_in ps_inf)
    then obtain k :: nat where
      k_lt: "k < length (lnth Qs i)" and
      at_k: "lnth Qs i ! k = e"
      by (meson in_set_conv_nth le_refl)

    have dist: "distinct (lnth Qs i)"
      by (simp add: chain_queue_step_preserves_distinct hd_emp i_lt chain)

    have "\<forall>k' \<le> k + 1. \<exists>i' \<ge> i. e \<notin> set (drop k' (lnth Qs i'))"
    proof -
      have "\<exists>i' \<ge> i. e \<notin> set (drop (k + 1 - l) (lnth Qs i'))" for l
      proof (induct l)
        case 0
        have "e \<notin> set (drop (k + 1) (lnth Qs i))"
          by (simp add: at_k dist distinct_imp_notin_set_drop_Suc k_lt)
        then show ?case
          by auto
      next
        case (Suc l)
        then obtain i' :: nat where
          i'_ge: "i' \<ge> i" and
          c_ni_i': "e \<notin> set (drop (k + 1 - l) (lnth Qs i'))"
          by blast

        obtain i'' :: nat where
          i''_ge: "i'' \<ge> i'" and
          i''_lt: "enat (Suc i'') < llength Qs" and
          sel_step: "select_queue_step (lnth Qs i'') (lnth Qs (Suc i''))"
          using inf_sel[unfolded infinitely_often_alt_def] by blast

        have c_ni_i'_i'': "e \<notin> set (drop (k + 1 - l) (lnth Qs j))"
          if j_ge: "j \<ge> i'" and j_le: "j \<le> i''" for j
          using j_ge j_le
        proof (induct j rule: less_induct)
          case (less d)
          note ih = this(1)

          show ?case
          proof (cases "d < i'")
            case True
            then show ?thesis
              using less.prems(1) by linarith
          next
            case False
            hence d_ge: "d \<ge> i'"
              by simp
            then show ?thesis
            proof (cases "d > i''")
              case True
              then show ?thesis
                using less.prems(2) linorder_not_less by blast
            next
              case False
              hence d_le: "d \<le> i''"
                by simp

              show ?thesis
              proof (cases "d = i'")
                case True
                then show ?thesis
                  using c_ni_i' by blast
              next
                case False
                note d_ne_i' = this(1)

                have dm1_bounds:
                  "d - 1 < d"
                  "i' \<le> d - 1"
                  "d - 1 \<le> i''"
                  using d_ge d_le d_ne_i' by auto
                have ih_dm1: "e \<notin> set (drop (k + 1 - l) (lnth Qs (d - 1)))"
                  by (rule ih[OF dm1_bounds])

                have "queue_step (lnth Qs (d - 1)) (lnth Qs d)"
                  by (metis (no_types, lifting) One_nat_def add_diff_inverse_nat
                      bot_nat_0.extremum_unique chain chain_lnth_rel d_ge d_ne_i' dm1_bounds(2)
                      enat_ord_code(4) le_less_Suc_eq nat_diff_split plus_1_eq_Suc ps_inf)
                then show ?thesis
                proof cases
                  case (queue_step_fold_addI es)

                  note at_d = this(1)

                  have c_in: "e |\<in>| fset_of_list (lnth Qs (d - 1))"
                    by (meson c_in' dm1_bounds(2) fset_of_list_elem i'_ge order_trans)
                  hence "e \<notin> set (drop (k + 1 - l)
                    (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) (removeAll e es)
                       (lnth Qs (d - 1))))"
                  proof -
                    have "set (drop (k + 1 - l)
                        (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) (removeAll e es)
                           (lnth Qs (d - 1)))) \<subseteq>
                      set (drop (k + 1 - l) (lnth Qs (d - 1) @ removeAll e es))"
                      using set_drop_fold_maybe_append_singleton .
                    have "e \<notin> set (drop (k + 1 - l) (lnth Qs (d - 1)))"
                      using ih_dm1 by blast
                    hence "e \<notin> set (drop (k + 1 - l) (lnth Qs (d - 1) @ removeAll e es))"
                      using set_drop_append_subseteq by force
                    thus ?thesis
                      using set_drop_fold_maybe_append_singleton by force
                  qed
                  hence "e \<notin> set (drop (k + 1 - l)
                    (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) es (lnth Qs (d - 1))))"
                    using c_in fold_maybe_append_removeAll
                    by (metis (mono_tags, lifting) fset_of_list_elem)
                  thus ?thesis
                    unfolding at_d by fastforce
                next
                  case (queue_step_fold_removeI es)
                  note at_d = this(1)
                  show ?thesis
                    unfolding at_d using ih_dm1 set_drop_fold_removeAll by fastforce
                qed
              qed
            qed
          qed
        qed

        have "Suc i'' > i"
          using i''_ge i'_ge by linarith
        moreover have "e \<notin> set (drop (k + 1 - Suc l) (lnth Qs (Suc i'')))"
          using sel_step
        proof cases
          case select_queue_stepI
          note at_si'' = this(1) and at_i''_nemp = this(2)

          have at_i''_nnil: "lnth Qs i'' \<noteq> []"
            using at_i''_nemp by auto

          have dist_i'': "distinct (lnth Qs i'')"
            by (simp add: chain_queue_step_preserves_distinct hd_emp chain ps_inf)

          have c_ni_i'': "e \<notin> set (drop (k + 1 - l) (lnth Qs i''))"
            using c_ni_i'_i'' i''_ge by blast

          show ?thesis
            unfolding at_si''
            by (subst distinct_set_drop_removeAll_hd[OF dist_i'' at_i''_nnil])
              (metis Suc_diff_Suc bot_nat_0.not_eq_extremum c_ni_i'' drop0 in_set_dropD
                zero_less_diff)
        qed
        ultimately show ?case
          by (rule_tac x = "Suc i''" in exI) auto
      qed
      thus ?thesis
        by (metis diff_add_zero drop0 in_set_dropD)
    qed
    then obtain i' :: nat where
      "i' \<ge> i"
      "e \<notin> set (lnth Qs i')"
      by fastforce
    then show False
      using c_in' by auto
  qed
qed

end

end
