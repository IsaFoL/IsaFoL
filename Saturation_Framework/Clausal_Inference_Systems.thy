(*  Title:       Clausal Inference Systems
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Clausal Inference Systems\<close>

theory Clausal_Inference_Systems
  imports
    Ordered_Resolution_Prover.Unordered_Ground_Resolution
    Standard_Redundancy_Criterion
begin


subsection \<open>Setup\<close>

abbreviation true_lit_curvy :: "'a interp \<Rightarrow> 'a literal \<Rightarrow> bool" (infix "|\<approx>l" 50) where
  "I |\<approx>l L \<equiv> I \<Turnstile>l L"

abbreviation true_cls_curvy :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "|\<approx>" 50) where
  "I |\<approx> C \<equiv> I \<Turnstile> C"

abbreviation true_clss_curvy :: "'a interp \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>s" 50) where
  "I |\<approx>s \<C> \<equiv> I \<Turnstile>s \<C>"

abbreviation true_cls_mset_curvy :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "|\<approx>m" 50) where
  "I |\<approx>m \<C> \<equiv> I \<Turnstile>m \<C>"

no_notation true_lit (infix "\<Turnstile>l" 50)
no_notation true_cls (infix "\<Turnstile>" 50)
no_notation true_clss (infix "\<Turnstile>s" 50)
no_notation true_cls_mset (infix "\<Turnstile>m" 50)


subsection \<open>Consequence Relation\<close>

abbreviation entails_clss :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>\<approx>" 50) where
  "N1 |\<approx>\<approx> N2 \<equiv> \<forall>I. I |\<approx>s N1 \<longrightarrow> I |\<approx>s N2"

lemma entails_iff_unsatisfiable:
  "CC |\<approx>\<approx> {D} \<longleftrightarrow> \<not> satisfiable (CC \<union> {{#- L#} |L. L \<in># D})" (is "_ \<longleftrightarrow> _ (_ \<union> ?NegD)")
proof
  assume "CC |\<approx>\<approx> {D}"
  then have "\<not> I |\<approx>s CC \<union> ?NegD" for I
    unfolding true_clss_def true_cls_def true_lit_def if_distribR HOL.if_bool_eq_conj
    apply (erule_tac x = I in allE)
    apply (simp add: ball_Un)
    apply auto
    using is_pos_neg_not_is_pos apply fastforce
    using is_pos_neg_not_is_pos by fastforce
  then show "\<not> satisfiable (CC \<union> ?NegD)"
    by auto
next
  assume "\<not> satisfiable (CC \<union> ?NegD)"
  then have "\<not> I |\<approx>s CC \<union> ?NegD" for I
    by auto
  then show "CC |\<approx>\<approx> {D}"
    unfolding true_clss_def true_cls_def true_lit_def if_distribR HOL.if_bool_eq_conj
    apply (simp only: ball_Un)
    apply auto
    using is_pos_neg_not_is_pos by fastforce
qed

interpretation consequence_relation "{{#}}" "(|\<approx>\<approx>)"
proof
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 |\<approx>\<approx> N2"
    using true_clss_mono by blast
next
  fix N2 N1 :: "'a clause set"
  assume "\<forall>C \<in> N2. N1 |\<approx>\<approx> {C}"
  then show "N1 |\<approx>\<approx> N2"
    unfolding true_clss_singleton by (simp add: true_clss_def)
qed auto

interpretation compact_consequence_relation "{{#}} :: ('a :: wellorder) clause set" "(|\<approx>\<approx>)"
proof
  fix CC and D :: "'a clause"
  assume "CC |\<approx>\<approx> {D}"
  then show "\<exists>CC' \<subseteq> CC. finite CC' \<and> CC' |\<approx>\<approx> {D}"
    unfolding entails_iff_unsatisfiable
    apply (subst (asm) clausal_logic_compact)
    apply (erule exE)
    apply (rule_tac x = "DD - {{#- L#} |L. L \<in># D}" in exI)
    by auto
qed


subsection \<open>Counterexample-Reducing Inference Systems\<close>

definition clss_of_interp :: "'a set \<Rightarrow> 'a literal multiset set" where
  "clss_of_interp I = {{#(if A \<in> I then Pos else Neg) A#} |A. True}"

lemma true_clss_of_interp_iff_equal[simp]: "J |\<approx>s clss_of_interp I \<longleftrightarrow> J = I"
  unfolding clss_of_interp_def true_clss_def true_cls_def true_lit_def by force

lemma entails_iff_models[simp]:
  "clss_of_interp I |\<approx>\<approx> CC \<longleftrightarrow> I |\<approx>s CC"
  by simp

locale clausal_cex_red_inference_system = inference_system Inf
  for Inf :: "('a :: wellorder) clause inference set" +
  fixes clausal_I_of :: "'a clause set \<Rightarrow> 'a interp"
  assumes clausal_Inf_cex_reducing:
    "{#} \<notin> N \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> clausal_I_of N |\<approx> D \<Longrightarrow>
     (\<And>C. C \<in> N \<Longrightarrow> \<not> clausal_I_of N |\<approx> C \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>Cs E. set Cs \<subseteq> N \<and> clausal_I_of N |\<approx>s set Cs \<and> Infer (Cs @ [D]) E \<in> Inf
        \<and> \<not> clausal_I_of N |\<approx> E \<and> E < D"
begin

abbreviation I_of :: "'a clause set \<Rightarrow> 'a clause set" where
  "I_of N \<equiv> clss_of_interp (clausal_I_of N)"

lemma Inf_cex_reducing:
  assumes
    bot_ni_n: "N \<inter> {{#}} = {}" and
    d_in_n: "D \<in> N" and
    n_ent_d: "\<not> I_of N |\<approx>\<approx> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N |\<approx>\<approx> {C} \<Longrightarrow> D \<le> C"
  shows "\<exists>\<iota> \<in> Inf.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> I_of N |\<approx>\<approx> set (side_prems_of \<iota>)
    \<and> \<not> I_of N |\<approx>\<approx> {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
proof -
  have "{#} \<notin> N"
    using bot_ni_n by auto
  moreover note d_in_n
  moreover have "\<not> clausal_I_of N |\<approx> D"
    using n_ent_d by simp
  moreover have "C \<in> N \<Longrightarrow> \<not> clausal_I_of N |\<approx> C \<Longrightarrow> D \<le> C" for C
    using d_min[of C] by simp
  ultimately obtain Cs E where
    "set Cs \<subseteq> N" and
    "clausal_I_of N |\<approx>s set Cs" and
    "Infer (Cs @ [D]) E \<in> Inf" and
    "\<not> clausal_I_of N |\<approx> E" and
    "E < D"
    using clausal_Inf_cex_reducing by metis
  then show "\<exists>\<iota> \<in> Inf.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> I_of N |\<approx>\<approx> set (side_prems_of \<iota>)
    \<and> \<not> I_of N |\<approx>\<approx> {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
    using snoc_eq_iff_butlast by fastforce
qed

sublocale cex_red_inference_system "{{#}}" "(|\<approx>\<approx>)" Inf I_of
  by unfold_locales (fact Inf_cex_reducing)

end


subsection \<open>Counterexample-Reducing Calculi Equipped with a Standard Redundancy Criterion\<close>

locale clausal_cex_red_calculus_with_std_red_crit =
  calculus_with_std_red_crit Inf "{{#}}" "(|\<approx>\<approx>)" +
  clausal_cex_red_inference_system Inf clausal_I_of
  for
    Inf :: "('a :: wellorder) clause inference set" and
    clausal_I_of :: "'a clause set \<Rightarrow> 'a set"
begin

sublocale cex_red_calculus_with_std_red_crit "{{#}}" "(|\<approx>\<approx>)" I_of
  by unfold_locales

lemma clausal_saturated_model:
  assumes
    "saturated N"
    "{#} \<notin> N"
  shows "clausal_I_of N |\<approx>s N"
  using assms by (simp add: saturated_model[simplified])

corollary clausal_saturated_complete:
  assumes
    "saturated N" and
    "\<forall>I. \<not> I |\<approx>s N"
  shows "{#} \<in> N"
  using assms clausal_saturated_model by blast

end

end
