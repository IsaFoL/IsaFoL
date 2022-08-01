(* Title:        Basic Definitions for Stating and Proving the Fairness of Prover Loops
   Authors:      Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022 *)


section \<open>Basic Definitions for Stating and Proving the Fairness of Prover Loops\<close>

text \<open>This section covers concepts that can be shared across the different
prover loops inspired by the literature (e.g., DISCOUNT, Otter).\<close>

theory Loop_Fairness_Basis
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
    fformulas :: "'p \<Rightarrow> 'f fset"
  assumes
    "fformulas empty = {||}" and
    "fformulas (add C P) = {|C|} |\<union>| fformulas P"
    "fformulas (remove C P) = fformulas P |-| {|C|}"
begin

abbreviation formulas :: "'p \<Rightarrow> 'f set" where
  "formulas P \<equiv> fset (fformulas P)"

text \<open>In the first rule, the assumption that the added formulas do not belong to the passive set can
be fulfilled by annotating formulas with timestamps.\<close>

inductive step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  step_addI: "C |\<notin>| fformulas P \<Longrightarrow> step P (add C P)"
| step_removeI: "step P (remove C P)"
| step_selectI: "fformulas P \<noteq> {||} \<Longrightarrow> step P (remove (select P) P)"

inductive select_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  select_stepI: "fformulas P \<noteq> {||} \<Longrightarrow> select_step P (remove (select P) P)"

text \<open>The passive set starts empty. The initial formulas must be added explicitly.\<close>

definition is_fair :: bool where
  "is_fair \<longleftrightarrow>
   (\<forall>Ps. full_chain step Ps \<longrightarrow> infinitely_often select_step Ps \<longrightarrow> lhd Ps = empty \<longrightarrow>
    Liminf_llist (lmap formulas Ps) = {})"

end

locale fifo_passive_set
begin

sublocale passive_set "[]" hd "\<lambda>y xs. xs @ [y]" removeAll fset_of_list
proof
  show "fset_of_list [] = {||}"
    by (auto simp: fset_of_list_elem)
next
  show "\<And>C P. fset_of_list (P @ [C]) = {|C|} |\<union>| fset_of_list P"
    by (simp add: funion_commute)
next
  show "\<And>C P. fset_of_list (removeAll C P) = fset_of_list P |-| {|C|}"
    by (auto simp: fset_of_list_elem)
qed

lemma step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "step P P'"
  shows "distinct P'"
  using step unfolding step.simps
  by (metis dist distinct.simps(2) distinct1_rotate distinct_removeAll fset_of_list_elem
      rotate1.simps(2))

lemma chain_big_step_preserves_distinct:
  assumes
    ps_chain: "chain step Ps" and
    dist_hd: "distinct (lhd Ps)" and
    i_lt: "enat i < llength Ps"
  shows "distinct (lnth Ps i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using dist_hd chain_length_pos[OF ps_chain] by (simp add: lhd_conv_lnth)
next
  case (Suc i)

  have ih: "distinct (lnth Ps i)"
    using Suc.hyps Suc.prems Suc_ile_eq order_less_imp_le by blast

  have "step (lnth Ps i) (lnth Ps (Suc i))"
    by (rule chain_lnth_rel[OF ps_chain Suc.prems])
  then show ?case
    using step_preserves_distinct ih by blast
qed

lemma fifo_passive_set_is_fair: "is_fair TYPE('f)"
  unfolding is_fair_def
proof (intro allI impI)
  fix Ps :: "'f list llist"
    assume
      ps_full: "full_chain step Ps" and
      inf_sel: "infinitely_often select_step Ps" and
      hd_emp: "lhd Ps = []"

  have ps_chain: "chain step Ps"
    by (rule full_chain_imp_chain[OF ps_full])

  show "Liminf_llist (lmap formulas Ps) = {}"
  proof (rule ccontr)
    assume lim_nemp: "Liminf_llist (lmap formulas Ps) \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Ps" and
      inter_nemp: "\<Inter> ((set \<circ> lnth Ps) ` {j. i \<le> j \<and> enat j < llength Ps}) \<noteq> {}"
      using lim_nemp unfolding Liminf_llist_def by auto

    from inter_nemp obtain C :: 'f where
      c_in: "\<forall>P \<in> lnth Ps ` {j. i \<le> j \<and> enat j < llength Ps}. C \<in> set P"
      by auto
    hence c_in': "\<forall>j \<ge> i. enat j < llength Ps \<longrightarrow> C \<in> set (lnth Ps j)"
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

    have c_in'': "\<forall>j \<ge> i. C \<in> set (lnth Ps j)"
      by (simp add: c_in' ps_inf)
    then obtain k :: nat where
      k_lt: "k < length (lnth Ps i)" and
      at_k: "lnth Ps i ! k = C"
      by (meson in_set_conv_nth le_refl)

    have dist: "distinct (lnth Ps i)"
      by (simp add: chain_big_step_preserves_distinct hd_emp i_lt ps_chain)

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
          sel_step: "select_step (lnth Ps i'') (lnth Ps (Suc i''))"
          using inf_sel[unfolded infinitely_often_alt_def] by blast

        have c_ni_i'_i'': "C \<notin> set (drop (k + 1 - l) (lnth Ps j))"
          if j_ge: "j \<ge> i'" and j_le: "j \<le> i''" for j
          using j_ge j_le
        proof (induct j rule: less_induct)
          case (less d)
          then show ?case
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

                have step: "step (lnth Ps (d - 1)) (lnth Ps d)"
                  sorry

                show ?thesis
                  sorry
              qed
            qed
          qed
        qed

        have "Suc i'' > i"
          using i''_ge i'_ge by linarith
        moreover have "C \<notin> set (drop (k + 1 - Suc l) (lnth Ps (Suc i'')))"
          using sel_step
        proof cases
          case select_stepI
          note at_si'' = this(1) and at_i''_nemp = this(2)

          have at_i''_nnil: "lnth Ps i'' \<noteq> []"
            using at_i''_nemp by auto

          have dist_i'': "distinct (lnth Ps i'')"
            by (simp add: chain_big_step_preserves_distinct hd_emp ps_chain ps_inf)

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
      using c_in'' by auto
  qed
qed

end

end
