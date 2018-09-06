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

definition entails_\<G>  :: \<open>'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
\<open>N1 \<Turnstile>\<G> N2 \<equiv> (\<G>_set N1) \<Turnstile>G (\<G>_set N2)\<close>

end

end

