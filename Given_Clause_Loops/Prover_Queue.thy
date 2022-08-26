(* Title:        Prover Queue and Fairness
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
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


subsection \<open>Prover Queue\<close>

text \<open>The passive set of a given clause prover can be organized in different
ways—e.g., as a priority queue or as a list of queues. This locale abstracts
over the specific data structure.\<close>

locale prover_queue =
  fixes
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    felems :: "'p \<Rightarrow> 'f fset"
  assumes
    felems_empty[simp]: "felems empty = {||}" and
    felems_not_empty[simp]: "P \<noteq> empty \<Longrightarrow> felems P \<noteq> {||}" and
    select_in_felems[simp]: "P \<noteq> empty \<Longrightarrow> select P |\<in>| felems P" and
    felems_add[simp]: "felems (add C P) = {|C|} |\<union>| felems P" and
    felems_remove[simp]: "felems (remove C P) = felems P |-| {|C|}" and
    add_again: "C |\<in>| felems P \<Longrightarrow> add C P = P"
begin

abbreviation elems :: "'p \<Rightarrow> 'f set" where
  "elems P \<equiv> fset (felems P)"

lemma elems_empty: "elems empty = {}"
  by simp

lemma formula_not_empty[simp]: "P \<noteq> empty \<Longrightarrow> elems P \<noteq> {}"
  by (metis bot_fset.rep_eq felems_not_empty fset_cong)

lemma select_in_elems[simp]: "P \<noteq> empty \<Longrightarrow> select P \<in> elems P"
  by (metis fmember.rep_eq select_in_felems)

lemma
  elems_add: "elems (add C P) = {C} \<union> elems P" and
  elems_remove: "elems (remove C P) = elems P - {C}"
  by simp+

lemma elems_fold_add[simp]: "elems (fold add Cs P) = set Cs \<union> elems P"
  by (induct Cs arbitrary: P) auto

lemma elems_fold_remove[simp]: "elems (fold remove Cs P) = elems P - set Cs"
  by (induct Cs arbitrary: P) auto

inductive queue_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  queue_step_fold_addI: "queue_step P (fold add Cs P)"
| queue_step_fold_removeI: "queue_step P (fold remove Cs P)"

lemma queue_step_idleI: "queue_step P P"
  using queue_step_fold_addI[of _ "[]", simplified] .

lemma queue_step_addI: "queue_step P (add C P)"
  using queue_step_fold_addI[of _ "[C]", simplified] .

lemma queue_step_removeI: "queue_step P (remove C P)"
  using queue_step_fold_removeI[of _ "[C]", simplified] .

inductive select_queue_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  select_queue_stepI: "P \<noteq> empty \<Longrightarrow> select_queue_step P (remove (select P) P)"

end

locale fair_prover_queue = prover_queue empty select add remove felems
  for
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    felems :: "'p \<Rightarrow> 'f fset" +
  assumes fair: "chain queue_step Ps \<Longrightarrow> infinitely_often select_queue_step Ps \<Longrightarrow>
    lhd Ps = empty \<Longrightarrow> Liminf_llist (lmap elems Ps) = {}"
begin
end


subsection \<open>Instantiation with FIFO Queue\<close>

text \<open>As a proof of concept, we show that a FIFO queue can serve as a fair
passive set.\<close>

locale fifo_prover_queue
begin

sublocale prover_queue "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list
proof
  show "fset_of_list [] = {||}"
    by (auto simp: fset_of_list_elem)
next
  show "\<And>P. P \<noteq> [] \<Longrightarrow> fset_of_list P \<noteq> {||}"
    by (metis fset_of_list.rep_eq fset_simps(1) set_empty)
next
  show "\<And>P. P \<noteq> [] \<Longrightarrow> hd P |\<in>| fset_of_list P"
    by (metis fset_of_list_elem list.set_sel(1))
next
  show "\<And>C P. fset_of_list (if C \<in> set P then P else P @ [C]) = {|C|} |\<union>| fset_of_list P"
    by (auto simp: funion_commute fset_of_list_elem)
next
  show "\<And>C P. fset_of_list (removeAll C P) = fset_of_list P |-| {|C|}"
    by (auto simp: fset_of_list_elem)
next
  show "\<And>C P. C |\<in>| fset_of_list P \<Longrightarrow> (if C \<in> set P then P else P @ [C]) = P"
    by (auto simp: fset_of_list_elem)
qed

lemma queue_step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "queue_step P P'"
  shows "distinct P'"
  using step
proof cases
  case (queue_step_fold_addI Cs)
  note p' = this(1)
  show ?thesis
    unfolding p'
    using dist
  proof (induct Cs arbitrary: P)
    case Nil
    then show ?case
      using dist by auto
  next
    case (Cons C Cs)
    note ih = this(1) and dist_p = this(2)

    show ?case
    proof (cases "C \<in> set P")
      case True
      then show ?thesis
        using ih[OF dist_p] by simp
    next
      case c_ni: False
      have dist_pc: "distinct (P @ [C])"
        using c_ni dist_p by auto
      show ?thesis
        using c_ni using ih[OF dist_pc] by simp
    qed
  qed
next
  case (queue_step_fold_removeI Cs)
  note p' = this(1)
  show ?thesis
    unfolding p' using dist by (simp add: distinct_fold_removeAll)
qed

lemma chain_queue_step_preserves_distinct:
  assumes
    chain: "chain queue_step Ps" and
    dist_hd: "distinct (lhd Ps)" and
    i_lt: "enat i < llength Ps"
  shows "distinct (lnth Ps i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using dist_hd chain_length_pos[OF chain] by (simp add: lhd_conv_lnth)
next
  case (Suc i)

  have ih: "distinct (lnth Ps i)"
    using Suc.hyps Suc.prems Suc_ile_eq order_less_imp_le by blast

  have "queue_step (lnth Ps i) (lnth Ps (Suc i))"
    by (rule chain_lnth_rel[OF chain Suc.prems])
  then show ?case
    using queue_step_preserves_distinct ih by blast
qed

sublocale fair_prover_queue "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll
  fset_of_list
proof unfold_locales
  fix Ps :: "'f list llist"
  assume
    chain: "chain queue_step Ps" and
    inf_sel: "infinitely_often select_queue_step Ps" and
    hd_emp: "lhd Ps = []"

  show "Liminf_llist (lmap elems Ps) = {}"
  proof (rule ccontr)
    assume lim_nemp: "Liminf_llist (lmap elems Ps) \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Ps" and
      inter_nemp: "\<Inter> ((set \<circ> lnth Ps) ` {j. i \<le> j \<and> enat j < llength Ps}) \<noteq> {}"
      using lim_nemp unfolding Liminf_llist_def by auto

    from inter_nemp obtain C :: 'f where
      "\<forall>P \<in> lnth Ps ` {j. i \<le> j \<and> enat j < llength Ps}. C \<in> set P"
      by auto
    hence c_in: "\<forall>j \<ge> i. enat j < llength Ps \<longrightarrow> C \<in> set (lnth Ps j)"
      by auto

    have ps_inf: "llength Ps = \<infinity>"
    proof (rule ccontr)
      assume "llength Ps \<noteq> \<infinity>"
      obtain n :: nat where
        n: "enat n = llength Ps"
        using \<open>llength Ps \<noteq> \<infinity>\<close> by force

      show False
        using inf_sel[unfolded infinitely_often_alt_def]
        by (metis Suc_lessD enat_ord_simps(2) less_le_not_le n)
    qed

    have c_in': "\<forall>j \<ge> i. C \<in> set (lnth Ps j)"
      by (simp add: c_in ps_inf)
    then obtain k :: nat where
      k_lt: "k < length (lnth Ps i)" and
      at_k: "lnth Ps i ! k = C"
      by (meson in_set_conv_nth le_refl)

    have dist: "distinct (lnth Ps i)"
      by (simp add: chain_queue_step_preserves_distinct hd_emp i_lt chain)

    have "\<forall>k' \<le> k + 1. \<exists>i' \<ge> i. C \<notin> set (drop k' (lnth Ps i'))"
    proof -
      have "\<exists>i' \<ge> i. C \<notin> set (drop (k + 1 - l) (lnth Ps i'))" for l
      proof (induct l)
        case 0
        have "C \<notin> set (drop (k + 1) (lnth Ps i))"
          by (simp add: at_k dist distinct_imp_notin_set_drop_Suc k_lt)
        then show ?case
          by auto
      next
        case (Suc l)
        then obtain i' :: nat where
          i'_ge: "i' \<ge> i" and
          c_ni_i': "C \<notin> set (drop (k + 1 - l) (lnth Ps i'))"
          by blast

        obtain i'' :: nat where
          i''_ge: "i'' \<ge> i'" and
          i''_lt: "enat (Suc i'') < llength Ps" and
          sel_step: "select_queue_step (lnth Ps i'') (lnth Ps (Suc i''))"
          using inf_sel[unfolded infinitely_often_alt_def] by blast

        have c_ni_i'_i'': "C \<notin> set (drop (k + 1 - l) (lnth Ps j))"
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
                have ih_dm1: "C \<notin> set (drop (k + 1 - l) (lnth Ps (d - 1)))"
                  by (rule ih[OF dm1_bounds])

                have "queue_step (lnth Ps (d - 1)) (lnth Ps d)"
                  by (metis (no_types, lifting) One_nat_def add_diff_inverse_nat
                      bot_nat_0.extremum_unique chain chain_lnth_rel d_ge d_ne_i' dm1_bounds(2)
                      enat_ord_code(4) le_less_Suc_eq nat_diff_split plus_1_eq_Suc ps_inf)
                then show ?thesis
                proof cases
                  case (queue_step_fold_addI Ds)

                  note at_d = this(1)

                  have c_in: "C |\<in>| fset_of_list (lnth Ps (d - 1))"
                    by (meson c_in' dm1_bounds(2) fset_of_list_elem i'_ge order_trans)
                  hence "C \<notin> set (drop (k + 1 - l)
                    (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) (removeAll C Ds)
                       (lnth Ps (d - 1))))"
                  proof -
                    have "set (drop (k + 1 - l)
                        (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) (removeAll C Ds)
                           (lnth Ps (d - 1)))) \<subseteq>
                      set (drop (k + 1 - l) (lnth Ps (d - 1) @ removeAll C Ds))"
                      using set_drop_fold_maybe_append_singleton .
                    have "C \<notin> set (drop (k + 1 - l) (lnth Ps (d - 1)))"
                      using ih_dm1 by blast
                    hence "C \<notin> set (drop (k + 1 - l) (lnth Ps (d - 1) @ removeAll C Ds))"
                      using set_drop_append_subseteq by force
                    thus ?thesis
                      using set_drop_fold_maybe_append_singleton by force
                  qed
                  hence "C \<notin> set (drop (k + 1 - l)
                    (fold (\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]) Ds (lnth Ps (d - 1))))"
                    using c_in fold_maybe_append_removeAll
                    by (metis (mono_tags, lifting) fset_of_list_elem)
                  thus ?thesis
                    unfolding at_d by fastforce
                next
                  case (queue_step_fold_removeI Ds)
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
        moreover have "C \<notin> set (drop (k + 1 - Suc l) (lnth Ps (Suc i'')))"
          using sel_step
        proof cases
          case select_queue_stepI
          note at_si'' = this(1) and at_i''_nemp = this(2)

          have at_i''_nnil: "lnth Ps i'' \<noteq> []"
            using at_i''_nemp by auto

          have dist_i'': "distinct (lnth Ps i'')"
            by (simp add: chain_queue_step_preserves_distinct hd_emp chain ps_inf)

          have c_ni_i'': "C \<notin> set (drop (k + 1 - l) (lnth Ps i''))"
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
      then show ?thesis
        by (metis diff_add_zero drop0 in_set_dropD)
    qed
    then obtain i' :: nat where
      "i' \<ge> i"
      "C \<notin> set (lnth Ps i')"
      by fastforce
    then show False
      using c_in' by auto
  qed
qed

end

end
