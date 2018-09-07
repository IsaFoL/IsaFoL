theory Saturation_Lifting
  imports Saturation_Framework
begin

locale redundancy_criterion_lifting = inference_system Bot_F_G entails_G I_G Red_I_G Red_F_G
  for
    Bot_F_G :: \<open>'g\<close> and
    entails_G :: \<open>'g formulas \<Rightarrow> 'g formulas \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    I_G :: \<open>'g inference set\<close> and
    Red_I_G :: \<open>'g formulas \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g formulas \<Rightarrow> 'g formulas\<close>
  + fixes
    Bot_F_F :: \<open>'f\<close> and
    I_F :: \<open>'f inference set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g formulas\<close> and
    \<G>_I :: \<open>'f inference \<Rightarrow> 'g inference set\<close>
  assumes
    Bot_F_map: \<open>\<G>_F Bot_F_F = {Bot_F_G}\<close> and
    inf_map: \<open>\<G>_I \<iota> \<subseteq> Red_I_G (\<G>_F (concl_of \<iota>))\<close>
begin

abbreviation \<G>_set :: \<open>'f formulas \<Rightarrow> 'g formulas\<close> where
  \<open>\<G>_set N \<equiv> \<Union>C \<in> N. \<G>_F C\<close>

lemma \<G>_subset: \<open>N1 \<subseteq> N2 \<Longrightarrow> \<G>_set N1 \<subseteq> \<G>_set N2\<close> by auto

definition entails_\<G>  :: \<open>'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
\<open>N1 \<Turnstile>\<G> N2 \<equiv> (\<G>_set N1) \<Turnstile>G (\<G>_set N2)\<close>

text \<open>lemma 7 in Uwe's notes\<close>
interpretation lifted_consequence_relation: consequence_relation  
  where Bot_F=Bot_F_F and entails=entails_\<G>
proof
  fix N
  show \<open>{Bot_F_F} \<Turnstile>\<G> N\<close> using Bot_F_map bot_implies_all entails_\<G>_def by auto
next
  fix N1 N2 :: \<open>'f formulas\<close>
  assume 
    incl: \<open>N2 \<subseteq> N1\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using incl entails_\<G>_def \<G>_subset subset_entailed by auto
next
  fix N1 N2
  assume
    N1_entails_C: \<open>\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using all_formulas_entailed N1_entails_C entails_\<G>_def 
    by (smt UN_E UN_I easy1 singletonI)
next
  fix N1 N2 N3
  assume
    trans: \<open>N1 \<Turnstile>\<G> N2 \<and> N2 \<Turnstile>\<G> N3\<close>
  show \<open>N1 \<Turnstile>\<G> N3\<close> using trans entails_\<G>_def transitive_entails by blast
qed

end

end

