theory Transition
imports Main

begin
section \<open>Transition\<close>
text \<open>We define here properties to define properties after all possible transitions.\<close>
abbreviation "no_step step S \<equiv> (\<forall>S'. \<not>step S S')"

definition full :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>+\<^sup>\<down>") where
"full transf = (\<lambda>S S'. tranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

definition full0:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_\<^sup>\<down>") where
"full0 transf = (\<lambda>S S'. rtranclp transf S S' \<and> (\<forall>S''. \<not> transf S' S''))"

lemma full0_unfold:
  "full0 r S S' \<longleftrightarrow> ((S = S' \<and> no_step r S') \<or> full r S S')"
  unfolding full0_def full_def by (auto simp add: Nitpick.rtranclp_unfold)

end