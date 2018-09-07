theory Saturation_Lifting
  imports Saturation_Framework
begin

text \<open>In Uwe's notes, a well-founded partial strict ordering is used.
  For simplicity, I will start by using a total one (wellorder), because there is a type class 
  already defined and lots of theorems. To go from total to partial order, an example to look at is
  the locale order_pair from the theory SN_Orders in the AFP\<close>
locale redundancy_criterion_lifting = inference_system Bot_F_G entails_G I_G Red_I_G Red_F_G
  for
    Bot_F_G :: \<open>'g\<close> and
    entails_G :: \<open>'g formulas \<Rightarrow> 'g formulas \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    I_G :: \<open>'g inference set\<close> and
    Red_I_G :: \<open>'g formulas \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g formulas \<Rightarrow> 'g formulas\<close>
  + fixes
    Bot_F_F :: \<open>'f :: {wellorder}\<close> and
    (*{wellorder} constrains 'f to have a total strict well-founded order *)
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

abbreviation sqsubset :: \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close>  (infix "\<sqsubset>" 50) where \<open>C1 \<sqsubset> C2 \<equiv> C1 < C2\<close>

abbreviation sqsubseteq ::  \<open>'f \<Rightarrow> 'f \<Rightarrow> bool\<close>  (infix "\<sqsubseteq>" 50) where \<open>C1 \<sqsubseteq> C2 \<equiv> C1 \<le> C2\<close>

definition Red_I_\<G> :: "'f formulas \<Rightarrow> 'f inference set" where
  \<open>Red_I_\<G> N = {\<iota> \<in> I_F. \<G>_I \<iota> \<subseteq> Red_I_G (\<G>_set N)}\<close>

definition Red_F_\<G> :: "'f formulas \<Rightarrow> 'f formulas" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F E)}\<close>

text \<open>lemma 8 in Uwe's notes\<close>
lemma Red_F_\<G>_equiv_def: 
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). E \<sqsubset> C \<and> D \<in> \<G>_F E)}\<close>
proof (rule;clarsimp)
  fix C D
  assume 
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. E \<sqsubset> C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close> using not_sec_case by clarsimp 
  have \<open>D \<in> Red_F_G (\<G>_set N) \<or> (\<exists>E\<in>N. E \<sqsubset> C \<and> D \<in> \<G>_F E)\<close> 
    using C_in D_in unfolding Red_F_\<G>_def by auto
  then have \<open>D \<in> Red_F_G (\<G>_set N)\<close> using neg_not_sec_case
    apply auto


end

end

