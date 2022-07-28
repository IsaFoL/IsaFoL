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


subsection \<open>Passive Set\<close>

text \<open>The passive set of a given clause prover can be organized in different
ways—e.g., as a priority queue or as a list of queues. This locale abstracts
over the specific data structure.\<close>

locale passive_struct =
  fixes
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f \<times> 'p" and
    add :: "'f list \<Rightarrow> 'p \<Rightarrow> 'p" and
    formulas :: "'p \<Rightarrow> 'f fset"
  assumes
    "formulas empty = {||}" and
    "formulas P \<noteq> {||} \<Longrightarrow> finsert (fst (select P)) (formulas (snd (select P))) = formulas P" and
    "formulas (add Cs P) = fset_of_list Cs |\<union>| formulas P"
begin

text \<open>The assumption that the selected formula is not immediately readded can be fulfilled by
annotating formulas with timestamps.\<close>

inductive step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  stepI: "fst (select P) \<notin> set Cs \<Longrightarrow> step P (add Cs (snd (select P)))"

definition is_struct_fair :: bool where
  "is_struct_fair \<longleftrightarrow> (\<forall>Ps. full_chain step Ps \<longrightarrow> Liminf_llist (lmap (fset \<circ> formulas) Ps) = {})"

end

interpretation fifo: passive_struct "[]" "\<lambda>xs. (hd xs, tl xs)" "\<lambda>ys xs. xs @ ys" fset_of_list
proof
  show "fset_of_list [] = {||}"
    by (auto simp: fset_of_list_elem)
next
  show "\<And>P. fset_of_list P \<noteq> {||} \<Longrightarrow>
    finsert (fst (hd P, tl P)) (fset_of_list (snd (hd P, tl P))) = fset_of_list P"
    by (metis fset_of_list_simps fst_conv list.exhaust_sel snd_conv)
next
  show "\<And>Cs P. fset_of_list (P @ Cs) = fset_of_list Cs |\<union>| fset_of_list P"
    by (simp add: funion_commute)
qed

lemma fifo_is_struct_fair: "fifo.is_struct_fair TYPE('f)"
  unfolding fifo.is_struct_fair_def
proof (intro allI impI)
  fix Ps :: "'f list llist"
  assume ps_full: "full_chain fifo.step Ps"

  show "Liminf_llist (lmap (fset \<circ> fset_of_list) Ps) = {}"
  proof (rule ccontr)
    assume lim_ne: "Liminf_llist (lmap (fset \<circ> fset_of_list) Ps) \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Ps" and
      inter_ne: "\<Inter> ((set \<circ> lnth Ps) ` {j. i \<le> j \<and> enat j < llength Ps}) \<noteq> {}"
      using lim_ne unfolding Liminf_llist_def by (auto simp: fset_of_list.rep_eq)

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

      have "\<not> fifo.step (lnth Ps (n - 1)) P" for P
        using full_chain_lnth_not_rel[OF ps_full, of "n - 1" P] Suc_diff_1 n n_gz by presburger
      hence "set (lnth Ps (n - 1)) = {}"
        using fifo.step.simps by force
      moreover have "C \<in> set (lnth Ps (n - 1))"
        using i_lt c_in' n
        by (metis Suc_pred' diff_less enat_ord_simps(2) le_Suc_eq less_numeral_extra(1) n_gz
            nless_le)
      ultimately show False
        by simp
    qed

    show False
      sorry
  qed
qed

end
