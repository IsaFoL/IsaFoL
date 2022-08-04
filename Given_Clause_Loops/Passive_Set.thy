(* Title:        Passive Set and Fairness
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Passive Set and Fairness\<close>

text \<open>This section covers concepts that can be shared across the different
prover loops inspired by the literature (e.g., DISCOUNT, Otter).\<close>

theory Passive_Set
  imports
    "HOL-Library.FSet"
    Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Setup and Basic Lemmas\<close>

declare fset_of_list.rep_eq [simp]

lemma distinct_imp_notin_set_drop_Suc:
  assumes
    "distinct xs"
    "i < length xs"
    "xs ! i = x"
  shows "x \<notin> set (drop (Suc i) xs)"
  by (metis Cons_nth_drop_Suc assms distinct.simps(2) distinct_drop)

lemma distinct_set_drop_removeAll_hd:
  assumes
    "distinct xs"
    "xs \<noteq> []"
  shows "set (drop n (removeAll (hd xs) xs)) = set (drop (Suc n) xs)"
  using assms
  by (metis distinct.simps(2) drop_Suc list.exhaust_sel removeAll.simps(2) removeAll_id)

lemma set_drop_removeAll: "set (drop n (removeAll y xs)) \<subseteq> set (drop n xs)"
proof (induct n arbitrary: xs)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons x xs')
    then show ?thesis
      by (metis Suc Suc_n_not_le_n drop_Suc_Cons nat_le_linear removeAll.simps(2)
          set_drop_subset_set_drop subset_code(1))
  qed
qed

lemma set_drop_append_subseteq: "set (drop n (xs @ ys)) \<subseteq> set (drop n xs) \<union> set ys"
  by (metis drop_append set_append set_drop_subset sup.idem sup.orderI sup_mono)


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


subsection \<open>Passive Set\<close>

text \<open>The passive set of a given clause prover can be organized in different
ways—e.g., as a priority queue or as a list of queues. This locale abstracts
over the specific data structure.\<close>

locale passive_set =
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
    felems_remove[simp]: "felems (remove C P) = felems P |-| {|C|}"
begin

abbreviation elems :: "'p \<Rightarrow> 'f set" where
  "elems P \<equiv> fset (felems P)"

lemma elems_empty: "elems empty = {}"
  by simp

lemma formula_not_empty[simp]: "P \<noteq> empty \<Longrightarrow> elems P \<noteq> {}"
  by (metis bot_fset.rep_eq felems_not_empty fset_cong)

lemma select_in_elems[simp]: "P \<noteq> empty \<Longrightarrow> select P \<in> elems P"
  by (metis fmember.rep_eq select_in_felems)

lemma elems_add: "elems (add C P) = {C} \<union> elems P"
  by simp

lemma elems_remove: "elems (remove C P) = elems P - {C}"
  by simp

inductive passive_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  passive_step_idleI: "passive_step P P"
| passive_step_addI: "C \<notin> elems P \<Longrightarrow> passive_step P (add C P)"
| passive_step_removeI: "passive_step P (remove C P)"

inductive select_passive_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  select_passive_stepI: "P \<noteq> empty \<Longrightarrow> select_passive_step P (remove (select P) P)"

end

locale fair_passive_set = passive_set empty select add remove felems
  for
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    felems :: "'p \<Rightarrow> 'f fset" +
  assumes fair: "chain passive_step Ps \<Longrightarrow> infinitely_often select_passive_step Ps \<Longrightarrow>
    lhd Ps = empty \<Longrightarrow> Liminf_llist (lmap elems Ps) = {}"
begin
end


subsection \<open>Instantiation with FIFO Queue\<close>

text \<open>As a proof of concept, we show that a FIFO queue can serve as a fair
passive set.\<close>

locale fifo_passive_set
begin

sublocale passive_set "[]" hd "\<lambda>y xs. xs @ [y]" removeAll fset_of_list
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
  show "\<And>C P. fset_of_list (P @ [C]) = {|C|} |\<union>| fset_of_list P"
    by (simp add: funion_commute)
next
  show "\<And>C P. fset_of_list (removeAll C P) = fset_of_list P |-| {|C|}"
    by (auto simp: fset_of_list_elem)
qed

lemma passive_step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "passive_step P P'"
  shows "distinct P'"
  using step unfolding passive_step.simps
  by (metis dist distinct.simps(2) distinct1_rotate distinct_removeAll fset_of_list.rep_eq
      rotate1.simps(2))

lemma chain_passive_step_preserves_distinct:
  assumes
    chain: "chain passive_step Ps" and
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

  have "passive_step (lnth Ps i) (lnth Ps (Suc i))"
    by (rule chain_lnth_rel[OF chain Suc.prems])
  then show ?case
    using passive_step_preserves_distinct ih by blast
qed

sublocale fair_passive_set "[]" hd "\<lambda>y xs. xs @ [y]" removeAll fset_of_list
proof unfold_locales
  fix Ps :: "'f list llist"
    assume
      chain: "chain passive_step Ps" and
      inf_sel: "infinitely_often select_passive_step Ps" and
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
      by (simp add: chain_passive_step_preserves_distinct hd_emp i_lt chain)

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
          sel_step: "select_passive_step (lnth Ps i'') (lnth Ps (Suc i''))"
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
            then have d_ge: "d \<ge> i'"
              by simp
            then show ?thesis
            proof (cases "d > i''")
              case True
              then show ?thesis
                using less.prems(2) linorder_not_less by blast
            next
              case False
              then have d_le: "d \<le> i''"
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

                have "passive_step (lnth Ps (d - 1)) (lnth Ps d)"
                  by (metis add_leE chain chain_lnth_rel dm1_bounds(1) enat_ord_code(4) le_refl
                      less_imp_Suc_add ordered_cancel_comm_monoid_diff_class.add_diff_inverse
                      plus_1_eq_Suc ps_inf)
                then show ?thesis
                proof cases
                  case passive_step_idleI
                  then show ?thesis
                    using ih_dm1 by presburger
                next
                  case (passive_step_addI D)
                  note at_d = this(1) and d_ni = this(2)

                  have "C |\<in>| fset_of_list (lnth Ps (d - 1))"
                    by (meson c_in' dm1_bounds(2) fset_of_list_elem i'_ge order_trans)
                  hence d_ne: "D \<noteq> C"
                    using d_ni by (meson notin_fset)

                  have "C \<notin> set [D]"
                    using d_ne by simp
                  then have c_ni_dm1: "C \<notin> set (drop (k + 1 - l) (lnth Ps (d - 1) @ [D]))"
                    using ih_dm1 set_drop_append_subseteq[of "k + 1 - l" "lnth Ps (d - 1)" "[D]"]
                    by fast

                  show ?thesis
                    unfolding at_d by (rule c_ni_dm1)
                next
                  case (passive_step_removeI D)
                  note at_d = this(1)

                  show ?thesis
                    unfolding at_d using ih_dm1 set_drop_removeAll by fast
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
          case select_passive_stepI
          note at_si'' = this(1) and at_i''_nemp = this(2)

          have at_i''_nnil: "lnth Ps i'' \<noteq> []"
            using at_i''_nemp by auto

          have dist_i'': "distinct (lnth Ps i'')"
            by (simp add: chain_passive_step_preserves_distinct hd_emp chain ps_inf)

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
