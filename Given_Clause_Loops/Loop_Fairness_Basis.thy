(* Title:        Basic Definitions for Stating and Proving the Fairness of Prover Loops
   Authors:      Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022 *)


section \<open>Basic Definitions for Stating and Proving the Fairness of Prover Loops\<close>

text \<open>This section covers concepts that can be shared across the different prover loops inspired by
the literature (e.g., DISCOUNT, Otter).\<close>

theory Loop_Fairness_Basis
  imports Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Strategies\<close>

text \<open>A strategy operates on pairs of formulas and timestamps (lower meaning older). Given a
nonempty set of (timestamped) formulas, it nondeterministically selects at least one formula. The
nondeterminism is modeled using a set.\<close>

type_synonym 'f strategy = "('f \<times> nat) set \<Rightarrow> ('f \<times> nat) set"

definition is_strategy_legal :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_legal stgy \<longleftrightarrow> (\<forall>P. stgy P \<subseteq> P) \<and> (\<forall>P. P \<noteq> {} \<longrightarrow> stgy P \<noteq> {})"

inductive strategy_step :: "'f strategy \<Rightarrow> ('f \<times> nat) set \<Rightarrow> ('f \<times> nat) set \<Rightarrow> bool"
  for stgy :: "'f strategy" where
  strategy_step: "finite P \<Longrightarrow> finite N \<Longrightarrow> Ck \<in> stgy P \<Longrightarrow> (\<forall>(_, n) \<in> N. \<forall>(_, m) \<in> P. n > m) \<Longrightarrow>
    strategy_step stgy P ((P - {Ck}) \<union> N)"

definition is_strategy_fair :: "'f strategy \<Rightarrow> bool" where
  "is_strategy_fair stgy \<longleftrightarrow> (\<forall>Ps. full_chain (strategy_step stgy) Ps \<longrightarrow> Liminf_llist Ps = {})"

lemma exists_strategy_step_iff_not_empty:
  assumes
    leg: "is_strategy_legal stgy" and
    fin: "finite P"
  shows "(\<exists>P'. strategy_step stgy P P') \<longleftrightarrow> P \<noteq> {}"
proof (intro iffI exI)
  assume "\<exists>P'. strategy_step stgy P P'"
  then obtain P' where
    step: "strategy_step stgy P P'"
    by blast
  thus "P \<noteq> {}"
    by (metis empty_iff is_strategy_legal_def leg strategy_step.simps subset_empty)
next
  assume p_ne: "P \<noteq> {}"
  show "strategy_step stgy P (P - {SOME Ck. Ck \<in> stgy P})"
    by (rule strategy_step[of _ "{}", simplified, OF fin])
      (metis (full_types) p_ne is_strategy_legal_def leg some_in_eq)
qed


subsection \<open>Strict Age-Based Strategy\<close>

text \<open>A strict age-based strategy performs extremely poorly in practice, but it provides a good
test case for our definitions above.\<close>

definition strict_age_based_strategy :: "'f strategy" where
  "strict_age_based_strategy P = {Ck \<in> P. snd Ck = Inf (snd ` P)}"

lemma is_strict_age_based_strategy_legal:
  "is_strategy_legal strict_age_based_strategy"
  unfolding is_strategy_legal_def
proof (intro allI conjI impI)
  fix P :: "('f \<times> nat) set"
  show "strict_age_based_strategy P \<subseteq> P"
    unfolding strict_age_based_strategy_def by simp
next
  fix P :: "('f \<times> nat) set"
  assume "P \<noteq> {}"
  hence "snd ` P \<noteq> {}"
    by simp
  hence "Inf (snd ` P) \<in> snd ` P"
    using Inf_nat_def1 by presburger
  then show "strict_age_based_strategy P \<noteq> {}"
    unfolding strict_age_based_strategy_def by auto
qed

lemma is_strict_age_based_strategy_fair:
  "is_strategy_fair strict_age_based_strategy"
  unfolding is_strategy_fair_def
proof (intro allI impI)
  fix Ps :: "('f \<times> nat) set llist"
  assume ps_full: "full_chain (strategy_step strict_age_based_strategy) Ps"
  show "Liminf_llist Ps = {}"
  proof (rule ccontr)
    assume lim_ne: "Liminf_llist Ps \<noteq> {}"

    obtain i :: nat where
      i_lt: "enat i < llength Ps" and
      inter_ne: "\<Inter> (lnth Ps ` {j. i \<le> j \<and> enat j < llength Ps}) \<noteq> {}"
      using lim_ne unfolding Liminf_llist_def by auto
    from inter_ne obtain C :: "'f \<times> nat" where
      c_in: "\<forall>P \<in> lnth Ps ` {j. i \<le> j \<and> enat j < llength Ps}. C \<in> P"
      by auto
    hence c_in': "\<forall>j. i \<le> j \<longrightarrow> enat j < llength Ps \<longrightarrow> C \<in> lnth Ps j"
      by auto

    have ps_inf: "llength Ps = \<infinity>"
    proof (rule ccontr)
      assume "llength Ps \<noteq> \<infinity>"
      obtain n :: nat where
        n: "enat n = llength Ps"
        using \<open>llength Ps \<noteq> \<infinity>\<close> by force

      have n_gz: "n > 0"
        using full_chain_length_pos[OF ps_full] by (metis enat_ord_simps(2) n zero_enat_def)

      have "\<not> strategy_step strict_age_based_strategy (lnth Ps (n - 1)) P" for P
        using full_chain_lnth_not_rel[OF ps_full, of "n - 1" P] Suc_diff_1 n n_gz by presburger
      hence "lnth Ps (n - 1) = {}"
        using exists_strategy_step_iff_not_empty[OF is_strict_age_based_strategy_legal]
        (* NEED FINITENESSS *)
        sorry
      moreover have "C \<in> lnth Ps (n - 1)"
        using i_lt c_in' n
        by (metis Suc_pred' diff_less enat_ord_simps(2) le_Suc_eq less_numeral_extra(1) n_gz
            nless_le)
      ultimately show False
        by blast
    qed

    show False
      sorry
  qed
qed

end
