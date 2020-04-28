theory Clausal_Inference_Systems
  imports
    Standard_Redundancy_Criterion
    Ordered_Resolution_Prover.Herbrand_Interpretation
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

locale clausal_consequence_relation =
  fixes
    Bot :: "'a clause set" and
    entails :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    Bot_def: "Bot = {{#}}" and
    entails_def: "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>I. I |\<approx>s N1 \<longrightarrow> I |\<approx>s N2)"
begin

sublocale consequence_relation Bot entails
proof
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 \<Turnstile> N2"
    unfolding entails_def using true_clss_mono by blast
next
  fix N2 N1 :: "'a clause set"
  assume "\<forall>C \<in> N2. N1 \<Turnstile> {C}"
  then show "N1 \<Turnstile> N2"
    unfolding entails_def true_clss_singleton by (simp add: true_clss_def)
qed (auto simp: Bot_def entails_def)

end


subsection \<open>Counterexample-Reducing Inference Systems\<close>

definition clss_of_interp :: "'a set \<Rightarrow> 'a literal multiset set" where
  "clss_of_interp I = {{#(if A \<in> I then Pos else Neg) A#} |A. True}"

lemma true_clss_of_interp_iff_equal[simp]: "J |\<approx>s clss_of_interp I \<longleftrightarrow> J = I"
  unfolding clss_of_interp_def true_clss_def true_cls_def true_lit_def by force

lemma (in clausal_consequence_relation) entails_iff_models[simp]:
  "clss_of_interp I \<Turnstile> CC \<longleftrightarrow> I |\<approx>s CC"
  unfolding entails_def by simp

locale clausal_cex_red_inference_system = inference_system Inf + clausal_consequence_relation Bot
  for
    Bot :: "('a :: wellorder) clause set" and
    Inf :: "'a clause inference set" +
  fixes
    clausal_I_of :: "'a clause set \<Rightarrow> 'a interp"
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
    bot_ni_n: "N \<inter> Bot = {}" and
    d_in_n: "D \<in> N" and
    n_ent_d: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {C} \<Longrightarrow> D \<le> C"
  shows "\<exists>\<iota> \<in> Inf.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> I_of N \<Turnstile> set (side_prems_of \<iota>)
    \<and> \<not> I_of N \<Turnstile> {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
proof -
  have "{#} \<notin> N"
    using bot_ni_n Bot_def by blast
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
  thus ?thesis
    using snoc_eq_iff_butlast by fastforce
qed

sublocale cex_red_inference_system Bot entails Inf I_of
  by unfold_locales (fact Inf_cex_reducing)

end


subsection \<open>Counterexample-Reducing Calculi Equipped with a Standard Redundancy Criterion\<close>

locale clausal_cex_red_calculus_with_std_red_crit =
  cex_red_calculus_with_std_red_crit Bot entails "\<lambda>N. clss_of_interp (clausal_I_of N)" Inf +
  clausal_cex_red_inference_system entails Bot Inf clausal_I_of
  for
    Bot :: "('a :: wellorder) clause set" and
    entails :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    Inf :: "'a clause inference set" and
    clausal_I_of :: "'a clause set \<Rightarrow> 'a set"
begin

lemma clausal_saturated_complete:
  assumes
    satur: "saturated N" and
    bot_ni_n: "{#} \<notin> N"
  shows "clausal_I_of N |\<approx>s N"
    using saturated_complete[OF satur] by (simp add: Bot_def bot_ni_n)
end

end
