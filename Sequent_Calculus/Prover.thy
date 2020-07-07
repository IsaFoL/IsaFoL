theory Prover imports Main begin

datatype 'a form = Pro 'a | Falsity (\<open>\<bottom>\<close>) | Imp \<open>'a form\<close> \<open>'a form\<close> (infix \<open>\<rightarrow>\<close> 0)

primrec semantics where
  \<open>semantics i (Pro n) = i n\<close> |
  \<open>semantics _ \<bottom> = False\<close> |
  \<open>semantics i (p \<rightarrow> q) = (semantics i p \<longrightarrow> semantics i q)\<close>

abbreviation \<open>sc X Y i \<equiv> (\<forall>p \<in> set X. semantics i p) \<longrightarrow> (\<exists>q \<in> set Y. semantics i q)\<close>

function \<mu> where
  \<open>\<mu> A B (Pro n # C) [] = \<mu> (n # A) B C []\<close> |
  \<open>\<mu> A B C (Pro n # D) = \<mu> A (n # B) C D\<close> |
  \<open>\<mu> _ _ (\<bottom> # _) [] = {}\<close> |
  \<open>\<mu> A B C (\<bottom> # D) = \<mu> A B C D\<close> |
  \<open>\<mu> A B ((p \<rightarrow> q) # C) [] = \<mu> A B C [p] \<union> \<mu> A B (q # C) []\<close> |
  \<open>\<mu> A B C ((p \<rightarrow> q) # D) = \<mu> A B (p # C) (q # D)\<close> |
  \<open>\<mu> A B [] [] = (if set A \<inter> set B = {} then {A} else {})\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_,_,C,D). \<Sum>p \<leftarrow> C @ D. size p)\<close>) simp_all

lemma sat: \<open>sc (map Pro A @ C) (map Pro B @ D) (\<lambda>n. n \<in> set L) \<Longrightarrow> L \<notin> \<mu> A B C D\<close>
  by (induct rule: \<mu>.induct) auto

theorem main: \<open>(\<forall>i. sc (map Pro A @ C) (map Pro B @ D) i) \<longleftrightarrow> \<mu> A B C D = {}\<close>
  by (induct rule: \<mu>.induct) (auto simp: sat)

definition \<open>prover p \<equiv> \<mu> [] [] [] [p] = {}\<close>

corollary \<open>prover p \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
  unfolding prover_def by (simp flip: main)

end
