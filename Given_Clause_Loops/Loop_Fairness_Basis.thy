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


subsection \<open>Setup\<close>

declare fset_of_list.rep_eq [simp]


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

text \<open>The assumption that the added formulas do not belong to the passive set can be fulfilled by
annotating formulas with timestamps.\<close>

inductive step :: "'p \<Rightarrow> 'p \<Rightarrow> bool" where
  stepI: "distinct Cs \<Longrightarrow> set Cs \<inter> fset (formulas P) = {} \<Longrightarrow> step P (add Cs (snd (select P)))"

definition is_struct_fair :: bool where
  "is_struct_fair \<longleftrightarrow>
   (\<forall>Ps. full_chain step Ps \<longrightarrow> lhd Ps = empty \<longrightarrow> Liminf_llist (lmap (fset \<circ> formulas) Ps) = {})"

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

lemma chain_fifo_step_distinct_formulas:
  assumes
    ps_chain: "chain fifo.step Ps" and
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

  show ?case
  proof -
    have step: "fifo.step (lnth Ps i) (lnth Ps (Suc i))"
      by (rule chain_lnth_rel[OF ps_chain Suc.prems])

    show "distinct (lnth Ps (Suc i))"
      using step[unfolded fifo.step.simps, simplified]
      by (metis (no_types, lifting) disjoint_iff_not_equal distinct_append distinct_tl ih
          list.sel(2) tl_append2)
  qed
qed

lemma fifo_is_struct_fair: "fifo.is_struct_fair TYPE('f)"
  unfolding fifo.is_struct_fair_def
proof (intro allI impI)
  fix Ps :: "'f list llist"
  assume ps_full: "full_chain fifo.step Ps"
  assume hd_emp: "lhd Ps = []"

  have ps_chain: "chain fifo.step Ps"
    by (rule full_chain_imp_chain[OF ps_full])

  show "Liminf_llist (lmap (fset \<circ> fset_of_list) Ps) = {}"
  proof (rule ccontr)
    assume lim_ne: "Liminf_llist (lmap (fset \<circ> fset_of_list) Ps) \<noteq> {}"

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

    have c_in'': "\<forall>j. i \<le> j \<longrightarrow> C \<in> set (lnth Ps j)"
      by (simp add: c_in' ps_inf)
    then obtain k :: nat where
      k_lt: "k < length (lnth Ps i)" and
      at_k: "lnth Ps i ! k = C"
      by (meson in_set_conv_nth le_refl)

    have
      ij_bnd: "k - j < length (lnth Ps (i + j))" and
      at_kmj: "lnth Ps (i + j) ! (k - j) = C"
      if j_le: "j \<le> k" for j
      using j_le
    proof (induct j)
      case 0
      {
        case 1
        then show ?case
          by (simp add: k_lt)
      next
        case 2
        then show ?case
          by (simp add: at_k)
      }
    next
      case (Suc j)
      {
        case 1

        have j_le: "j \<le> k"
          using 1 by auto

        have ih: "k - j < length (lnth Ps (i + j))"
          by (rule Suc.hyps(1)[OF j_le])

        have step: "fifo.step (lnth Ps (i + j)) (lnth Ps (i + Suc j))"
          by (simp add: full_chain_lnth_rel ps_full ps_inf)

        have "\<exists>Cs. lnth Ps (i + Suc j) = tl (lnth Ps (i + j)) @ Cs"
          using step[unfolded fifo.step.simps] by auto
        then have "length (lnth Ps (i + Suc j)) + 1 \<ge> length (lnth Ps (i + j))"
          by fastforce
        thus ?case
          using 1 ih by linarith
      next
        case 2
        then show ?case
          sorry
      }
    qed

    have
      ik_bnd: "length (lnth Ps (i + k)) > 0" and
      at_0: "lnth Ps (i + k) ! 0 = C"
      using ij_bnd[of k] at_kmj[of k] by simp+
    from at_0 have c_at_hd_ik:"hd (lnth Ps (i + k)) = C"
      using ik_bnd by (simp add: hd_conv_nth)

    have step: "fifo.step (lnth Ps (i + k)) (lnth Ps (i + k + 1))"
      using full_chain_lnth_rel[OF ps_full]
      by (metis (full_types) Suc_eq_plus1 enat_ord_code(4) ps_inf)

    have "C \<notin> set (lnth Ps (i + k + 1))"
    proof -
      obtain Cs and P where
        at_ik: "lnth Ps (i + k) = P" and
        at_sik: "lnth Ps (i + k + 1) = tl P @ Cs" and
        inter: "set Cs \<inter> fset (fset_of_list P) = {}"
        using step[simplified fifo.step.simps] by auto

      have dist_hd: "distinct (lhd Ps)"
        using hd_emp by simp

      have "length P > 0"
        using at_ik ik_bnd by auto
      moreover have "hd P = C"
        using c_at_hd_ik at_ik by auto
      moreover have "distinct (lnth Ps (i + k))"
        using chain_fifo_step_distinct_formulas[OF ps_chain dist_hd] by (simp add: ps_inf)
      ultimately have c_ni_tl: "C \<notin> set (tl P)"
        using at_ik by (metis distinct.simps(2) hd_Cons_tl length_greater_0_conv)

      have c_ni_cs: "C \<notin> set Cs"
        using inter at_0 at_ik ik_bnd by auto

      thus ?thesis
        using c_ni_tl c_ni_cs at_sik by simp
    qed
    thus False
      using c_in'' by auto
  qed
qed

end
