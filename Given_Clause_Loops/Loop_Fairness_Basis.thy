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


subsection \<open>Setup and Basic Lemma\<close>

declare fset_of_list.rep_eq [simp]

lemma distinct_imp_notin_set_drop_Suc:
  assumes
    "distinct xs"
    "i < length xs"
    "xs ! i = x"
  shows "x \<notin> set (drop (Suc i) xs)"
  by (metis Cons_nth_drop_Suc assms(1) assms(2) assms(3) distinct.simps(2) distinct_drop)


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

text \<open>The assumption that the added formulas do not belong to the passive set can be fulfilled by
annotating formulas with timestamps.\<close>

inductive small_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  small_step_addI: "C |\<notin>| fformulas P \<Longrightarrow> small_step P (add C P)"
| small_step_removeI: "small_step P (remove C P)"

abbreviation formulas :: "'p \<Rightarrow> 'f set" where
  "formulas P \<equiv> fset (fformulas P)"

inductive big_step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  big_stepI: "small_step\<^sup>*\<^sup>* P P' \<Longrightarrow> big_step P (remove (select P') P')"

lemma no_big_step_imp_fformulas_empty:
  assumes no_step: "\<forall>P'. \<not> big_step P P'"
  shows "fformulas P = {||}"
  using big_step.intros no_step by blast

definition is_fair :: bool where
  "is_fair \<longleftrightarrow>
   (\<forall>Ps. full_chain big_step Ps \<longrightarrow> lhd Ps = empty \<longrightarrow> Liminf_llist (lmap formulas Ps) = {})"

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

lemma small_step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "small_step P P'"
  shows "distinct P'"
  using step unfolding small_step.simps
  by (metis dist distinct.simps(2) distinct1_rotate distinct_removeAll fset_of_list_elem
      rotate1.simps(2))

lemma rtranclp_small_step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "small_step\<^sup>*\<^sup>* P P'"
  shows "distinct P'"
  using step
proof induct
  case base
  then show ?case
    by (simp add: dist)
next
  case (step P' P'')
  then show ?case
    using small_step_preserves_distinct by blast
qed

lemma big_step_preserves_distinct:
  assumes
    dist: "distinct P" and
    step: "big_step P P'"
  shows "distinct P'"
  by (metis assms(2) big_step.cases dist distinct_removeAll rtranclp_small_step_preserves_distinct)

lemma chain_big_step_preserves_distinct:
  assumes
    ps_chain: "chain big_step Ps" and
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

  have "big_step (lnth Ps i) (lnth Ps (Suc i))"
    by (rule chain_lnth_rel[OF ps_chain Suc.prems])
  then show ?case
    using big_step_preserves_distinct ih by blast
qed

lemma fifo_passive_set_is_fair: "is_fair TYPE('f)"
  unfolding is_fair_def
proof (intro allI impI)
  fix Ps :: "'f list llist"
  assume ps_full: "full_chain big_step Ps"
  assume hd_emp: "lhd Ps = []"

  have ps_chain: "chain big_step Ps"
    by (rule full_chain_imp_chain[OF ps_full])

  show "Liminf_llist (lmap formulas Ps) = {}"
  proof (rule ccontr)
    assume lim_ne: "Liminf_llist (lmap formulas Ps) \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Ps" and
      inter_ne: "\<Inter> ((set \<circ> lnth Ps) ` {j. i \<le> j \<and> enat j < llength Ps}) \<noteq> {}"
      using lim_ne unfolding Liminf_llist_def by auto

    from inter_ne obtain C :: 'f where
      c_in: "\<forall>P \<in> lnth Ps ` {j. i \<le> j \<and> enat j < llength Ps}. C \<in> set P"
      by auto
    hence c_in': "\<forall>j. i \<le> j \<longrightarrow> enat j < llength Ps \<longrightarrow> C \<in> set (lnth Ps j)"
      by auto

    have ps_inf: "llength Ps = \<infinity>"
    proof (rule ccontr)
      assume "llength Ps \<noteq> \<infinity>"
      obtain n :: nat where
        n: "enat n = llength Ps"
        using \<open>llength Ps \<noteq> \<infinity>\<close> by force

      have n_gz: "n > 0"
        using full_chain_length_pos[OF ps_full] by (metis enat_ord_simps(2) n zero_enat_def)

      have "\<not> big_step (lnth Ps (n - 1)) P" for P
        using full_chain_lnth_not_rel[OF ps_full, of "n - 1" P] Suc_diff_1 n n_gz by presburger
      hence "set (lnth Ps (n - 1)) = {}"
        using no_big_step_imp_fformulas_empty by (metis equals0I fempty_iff fset_of_list_elem)
      moreover have "C \<in> set (lnth Ps (n - 1))"
        using i_lt c_in' n
        by (metis Suc_pred' diff_less enat_ord_simps(2) le_Suc_eq less_numeral_extra(1) n_gz
            nless_le)
      ultimately show False
        by simp
    qed

    have c_in'': "\<forall>j. i \<le> j \<longrightarrow> C \<in> set (lnth Ps j)"
      by (simp add: c_in' ps_inf)
    then obtain k :: nat where
      k_lt: "k < length (lnth Ps i)" and
      at_k: "lnth Ps i ! k = C"
      by (meson in_set_conv_nth le_refl)

    have dist: "distinct (lnth Ps i)"
      by (simp add: chain_big_step_preserves_distinct hd_emp i_lt ps_chain)

    have ni_j: "C \<notin> set (drop (k + 1 - j) (lnth Ps (i + j)))"
      if j_le: "j \<le> k + 1" for j
    proof (induct j)
      case 0
      then show ?case
        using distinct_imp_notin_set_drop_Suc[OF dist k_lt at_k] by simp
    next
      case (Suc j)
      show ?case
        sorry
    qed

    have "C \<notin> set (lnth Ps (i + k + 1))"
      using ni_j[of "k + 1"] by simp
    thus False
      using c_in'' by auto
  qed
qed

end

end
