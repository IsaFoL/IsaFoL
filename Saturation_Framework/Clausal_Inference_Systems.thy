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

abbreviation true_lit_thick :: "'a interp \<Rightarrow> 'a literal \<Rightarrow> bool" (infix "\<TTurnstile>l" 50) where
  "I \<TTurnstile>l L \<equiv> I \<Turnstile>l L"

abbreviation true_cls_thick :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<TTurnstile>" 50) where
  "I \<TTurnstile> C \<equiv> I \<Turnstile> C"

abbreviation true_clss_thick :: "'a interp \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<TTurnstile>s" 50) where
  "I \<TTurnstile>s \<C> \<equiv> I \<Turnstile>s \<C>"

abbreviation true_cls_mset_thick :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<TTurnstile>m" 50) where
  "I \<TTurnstile>m \<C> \<equiv> I \<Turnstile>m \<C>"

no_notation true_lit (infix "\<Turnstile>l" 50)
no_notation true_cls (infix "\<Turnstile>" 50)
no_notation true_clss (infix "\<Turnstile>s" 50)
no_notation true_cls_mset (infix "\<Turnstile>m" 50)


subsection \<open>Consequence Relation\<close>

abbreviation entails_clss :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<TTurnstile>e" 50) where
  "N1 \<TTurnstile>e N2 \<equiv> \<forall>I. I \<TTurnstile>s N1 \<longrightarrow> I \<TTurnstile>s N2"

lemma entails_iff_unsatisfiable_single:
  "CC \<TTurnstile>e {E} \<longleftrightarrow> \<not> satisfiable (CC \<union> {{#- L#} |L. L \<in># E})" (is "_ \<longleftrightarrow> _ (_ \<union> ?NegD)")
proof
  assume "CC \<TTurnstile>e {E}"
  then have "\<not> I \<TTurnstile>s CC \<union> ?NegD" for I
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
  then have "\<not> I \<TTurnstile>s CC \<union> ?NegD" for I
    by auto
  then show "CC \<TTurnstile>e {E}"
    unfolding true_clss_def true_cls_def true_lit_def if_distribR HOL.if_bool_eq_conj
    apply (simp only: ball_Un)
    apply auto
    using is_pos_neg_not_is_pos by fastforce
qed

lemma entails_iff_unsatisfiable:
  "CC \<TTurnstile>e EE \<longleftrightarrow> (\<forall>E \<in> EE. \<not> satisfiable (CC \<union> {{#- L#} |L. L \<in># E}))" (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<forall>E \<in> EE. CC \<TTurnstile>e {E})"
    unfolding true_clss_def by auto
  also have "... \<longleftrightarrow> ?rhs"
    unfolding entails_iff_unsatisfiable_single by auto
  finally show ?thesis
    .
qed

interpretation consequence_relation "{{#}}" "(\<TTurnstile>e)"
proof
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 \<TTurnstile>e N2"
    using true_clss_mono by blast
next
  fix N2 N1 :: "'a clause set"
  assume "\<forall>C \<in> N2. N1 \<TTurnstile>e {C}"
  then show "N1 \<TTurnstile>e N2"
    unfolding true_clss_singleton by (simp add: true_clss_def)
qed auto

interpretation refute_compact_consequence_relation "{{#}} :: ('a :: wellorder) clause set" "(\<TTurnstile>e)"
  by unfold_locales (use clausal_logic_compact in auto)

interpretation compact_consequence_relation "{{#}} :: ('a :: wellorder) clause set" "(\<TTurnstile>e)"
proof
  fix CC EE :: "'a clause set"
  assume
    fin_e: "finite EE" and
    c_ent_e: "CC \<TTurnstile>e EE"

  have "\<forall>E \<in> EE. \<not> satisfiable (CC \<union> {{#- L#} |L. L \<in># E})"
    using c_ent_e[unfolded entails_iff_unsatisfiable] .
  then have "\<forall>E \<in> EE. \<exists>DD \<subseteq> CC \<union> {{#- L#} |L. L \<in># E}. finite DD \<and> \<not> satisfiable DD"
    by (subst (asm) clausal_logic_compact)
  then obtain DD_of where
    d_of: "\<forall>E \<in> EE. DD_of E \<subseteq> CC \<union> {{#- L#} |L. L \<in># E} \<and> finite (DD_of E)
      \<and> \<not> satisfiable (DD_of E)"
    by moura

  define CC' where
    "CC' = (\<Union>E \<in> EE. DD_of E - {{#- L#} |L. L \<in># E})"

  have "CC' \<subseteq> CC"
    unfolding CC'_def using d_of by auto
  moreover have c'_fin: "finite CC'"
    unfolding CC'_def using d_of fin_e by blast
  moreover have "CC' \<TTurnstile>e EE"
    unfolding entails_iff_unsatisfiable
    apply (rule ballI)
    subgoal for E
      apply (rule unsatisfiable_mono[of "DD_of E"])
      using d_of[rule_format, THEN conjunct1, of E]
      unfolding CC'_def
      apply auto[1]
      using d_of
      apply auto
      done
    done
  ultimately show "\<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<TTurnstile>e EE"
    by blast
qed


subsection \<open>Counterexample-Reducing Inference Systems\<close>

definition clss_of_interp :: "'a set \<Rightarrow> 'a literal multiset set" where
  "clss_of_interp I = {{#(if A \<in> I then Pos else Neg) A#} |A. True}"

lemma true_clss_of_interp_iff_equal[simp]: "J \<TTurnstile>s clss_of_interp I \<longleftrightarrow> J = I"
  unfolding clss_of_interp_def true_clss_def true_cls_def true_lit_def by force

lemma entails_iff_models[simp]:
  "clss_of_interp I \<TTurnstile>e CC \<longleftrightarrow> I \<TTurnstile>s CC"
  by simp

locale clausal_cex_red_inference_system = inference_system Inf
  for Inf :: "('a :: wellorder) clause inference set" +
  fixes clausal_I_of :: "'a clause set \<Rightarrow> 'a interp"
  assumes clausal_Inf_cex_reducing:
    "{#} \<notin> N \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> clausal_I_of N \<TTurnstile> D \<Longrightarrow>
     (\<And>C. C \<in> N \<Longrightarrow> \<not> clausal_I_of N \<TTurnstile> C \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>Cs E. set Cs \<subseteq> N \<and> clausal_I_of N \<TTurnstile>s set Cs \<and> Infer (Cs @ [D]) E \<in> Inf
        \<and> \<not> clausal_I_of N \<TTurnstile> E \<and> E < D"
begin

abbreviation I_of :: "'a clause set \<Rightarrow> 'a clause set" where
  "I_of N \<equiv> clss_of_interp (clausal_I_of N)"

lemma Inf_cex_reducing:
  assumes
    bot_ni_n: "N \<inter> {{#}} = {}" and
    d_in_n: "D \<in> N" and
    n_ent_d: "\<not> I_of N \<TTurnstile>e {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<TTurnstile>e {C} \<Longrightarrow> D \<le> C"
  shows "\<exists>\<iota> \<in> Inf.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> I_of N \<TTurnstile>e set (side_prems_of \<iota>)
    \<and> \<not> I_of N \<TTurnstile>e {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
proof -
  have "{#} \<notin> N"
    using bot_ni_n by auto
  moreover note d_in_n
  moreover have "\<not> clausal_I_of N \<TTurnstile> D"
    using n_ent_d by simp
  moreover have "C \<in> N \<Longrightarrow> \<not> clausal_I_of N \<TTurnstile> C \<Longrightarrow> D \<le> C" for C
    using d_min[of C] by simp
  ultimately obtain Cs E where
    "set Cs \<subseteq> N" and
    "clausal_I_of N \<TTurnstile>s set Cs" and
    "Infer (Cs @ [D]) E \<in> Inf" and
    "\<not> clausal_I_of N \<TTurnstile> E" and
    "E < D"
    using clausal_Inf_cex_reducing by metis
  then show "\<exists>\<iota> \<in> Inf.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> I_of N \<TTurnstile>e set (side_prems_of \<iota>)
    \<and> \<not> I_of N \<TTurnstile>e {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
    using snoc_eq_iff_butlast by fastforce
qed

sublocale cex_red_inference_system "{{#}}" "(\<TTurnstile>e)" Inf I_of
  by unfold_locales (fact Inf_cex_reducing)

end


subsection \<open>Counterexample-Reducing Calculi Equipped with a Standard Redundancy Criterion\<close>

locale clausal_cex_red_calculus_with_std_red_crit =
  calculus_with_std_red_crit Inf "{{#}}" "(\<TTurnstile>e)" +
  clausal_cex_red_inference_system Inf clausal_I_of
  for
    Inf :: "('a :: wellorder) clause inference set" and
    clausal_I_of :: "'a clause set \<Rightarrow> 'a set"
begin

sublocale cex_red_calculus_with_std_red_crit "{{#}}" "(\<TTurnstile>e)" I_of
  by unfold_locales

sublocale refute_compact_calculus_with_red_crit "{{#}}" Inf "(\<TTurnstile>e)" Red_Inf Red_F
  by unfold_locales

lemma clausal_saturated_model:
  assumes
    "saturated N"
    "{#} \<notin> N"
  shows "clausal_I_of N \<TTurnstile>s N"
  using assms by (simp add: saturated_model[simplified])

corollary clausal_saturated_complete:
  assumes
    "saturated N" and
    "\<forall>I. \<not> I \<TTurnstile>s N"
  shows "{#} \<in> N"
  using assms clausal_saturated_model by blast

end

end
