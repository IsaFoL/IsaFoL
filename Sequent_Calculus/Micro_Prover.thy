section \<open>A Micro Prover for Propositional Logic\<close>

theory Micro_Prover imports Main begin

datatype form = Pro nat | Falsity (\<open>\<bottom>\<close>) | Imp form form (infix \<open>\<rightarrow>\<close> 0)

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (if m = n then True else member m A)\<close>

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common A (m # B) = (if member m A then True else common A B)\<close>

function \<mu> where
  \<open>\<mu> A B (Pro n # C) [] = \<mu> (n # A) B C []\<close> |
  \<open>\<mu> A B C (Pro n # D) = \<mu> A (n # B) C D\<close> |
  \<open>\<mu> _ _ (\<bottom> # _) [] = True\<close> |
  \<open>\<mu> A B C (\<bottom> # D) = \<mu> A B C D\<close> |
  \<open>\<mu> A B ((p \<rightarrow> q) # C) [] = (if \<mu> A B C [p] then \<mu> A B (q # C) [] else False)\<close> |
  \<open>\<mu> A B C ((p \<rightarrow> q) # D) = \<mu> A B (p # C) (q # D)\<close> |
  \<open>\<mu> A B [] [] = common A B\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_,_,C,D). size (C @ D) + 2*(\<Sum>p \<leftarrow> C @ D. size p))\<close>) simp_all

section \<open>Prover Execution on Valid Propositions\<close>

proposition \<open>((p \<longrightarrow> False) \<longrightarrow> False) \<longrightarrow> p\<close> by fast

theorem \<open>\<mu> [] [] [] [((Pro 0 \<rightarrow> \<bottom>) \<rightarrow> \<bottom>) \<rightarrow> Pro 0]\<close> by eval

proposition \<open>p \<longrightarrow> p\<close> by fast

theorem \<open>\<mu> [] [] [] [Pro 0 \<rightarrow> Pro 0]\<close> by eval

proposition \<open>p \<longrightarrow> q \<longrightarrow> p\<close> by fast

theorem \<open>\<mu> [] [] [] [Pro 0 \<rightarrow> (Pro 1 \<rightarrow> Pro 0)]\<close> by eval

proposition \<open>(p \<longrightarrow> q \<longrightarrow> r) \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> p \<longrightarrow> r\<close> by fast

theorem \<open>\<mu> [] [] [] [(Pro 0 \<rightarrow> (Pro 1 \<rightarrow> Pro 2)) \<rightarrow> ((Pro 0 \<rightarrow> Pro 1) \<rightarrow> (Pro 0 \<rightarrow> Pro 2))]\<close> by eval

proposition \<open>p \<longrightarrow> q \<longrightarrow> q \<longrightarrow> p\<close> by fast

theorem \<open>\<mu> [] [] [] [Pro 0 \<rightarrow> (Pro 1 \<rightarrow> (Pro 1 \<rightarrow> Pro 0))]\<close> by eval

proposition \<open>p \<longrightarrow> (p \<longrightarrow> q) \<longrightarrow> q\<close> by fast

theorem \<open>\<mu> [] [] [] [Pro 0 \<rightarrow> ((Pro 0 \<rightarrow> Pro 1) \<rightarrow> Pro 1)]\<close> by eval

section \<open>The Micro Prover is Sound and Complete\<close>

function \<mu>' where
  \<open>\<mu>' A B (Pro n # C) [] = \<mu>' (n # A) B C []\<close> |
  \<open>\<mu>' A B C (Pro n # D) = \<mu>' A (n # B) C D\<close> |
  \<open>\<mu>' _ _ (\<bottom> # _) [] = []\<close> |
  \<open>\<mu>' A B C (\<bottom> # D) = \<mu>' A B C D\<close> |
  \<open>\<mu>' A B ((p \<rightarrow> q) # C) [] = \<mu>' A B C [p] @ \<mu>' A B (q # C) []\<close> |
  \<open>\<mu>' A B C ((p \<rightarrow> q) # D) = \<mu>' A B (p # C) (q # D)\<close> |
  \<open>\<mu>' A B [] [] = (if set A \<inter> set B = {} then [A] else [])\<close>
  by pat_completeness simp_all

termination by (relation \<open>measure (\<lambda>(_,_,C,D). size (C @ D) + 2*(\<Sum>p \<leftarrow> C @ D. size p))\<close>) simp_all

lemma member_set: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

lemma common_set: \<open>common A B \<longleftrightarrow> set A \<inter> set B \<noteq> {}\<close>
  by (induct B) (simp_all add: member_set)

lemma micro: \<open>\<mu> A B C D \<longleftrightarrow> \<mu>' A B C D = []\<close>
  by (induct rule: \<mu>.induct) (simp_all add: common_set)

primrec semantics where
  \<open>semantics i (Pro n) = i n\<close> |
  \<open>semantics _ \<bottom> = False\<close> |
  \<open>semantics i (p \<rightarrow> q) = (if semantics i p then semantics i q else True)\<close>

abbreviation \<open>semantics' i X Y \<equiv> (\<forall>p \<in> set X. semantics i p) \<longrightarrow> (\<exists>p \<in> set Y. semantics i p)\<close>

subsection \<open>Sequent Calculus\<close>

inductive SC (\<open>_ \<then> _\<close> 0) where
  Fls_L: \<open>\<bottom> # _ \<then> _\<close> |
  Fls_R: \<open>X \<then> \<bottom> # Y\<close> if \<open>X \<then> Y\<close> |
  Imp_L: \<open>(p \<rightarrow> q) # X \<then> Y\<close> if \<open>X \<then> p # Y\<close> and \<open>q # X \<then> Y\<close> |
  Imp_R: \<open>X \<then> (p \<rightarrow> q) # Y\<close> if \<open>p # X \<then> q # Y\<close> |
  Set_L: \<open>X' \<then> Y\<close> if \<open>X \<then> Y\<close> and \<open>set X' = set X\<close> |
  Set_R: \<open>X \<then> Y'\<close> if \<open>X \<then> Y\<close> and \<open>set Y' = set Y\<close> |
  Basic: \<open>p # _ \<then> p # _\<close>

lemma proper: \<open>X \<then> Y \<Longrightarrow> semantics' i X Y\<close>
  by (induct rule: SC.induct) auto

subsection \<open>Counterexamples\<close>

lemma cex: \<open>L \<in> set (\<mu>' A B C D) \<Longrightarrow> \<not> semantics' (\<lambda>n. n \<in> set L) (map Pro A @ C) (map Pro B @ D)\<close>
  by (induct A B C D rule: \<mu>'.induct) auto

subsection \<open>Correctness\<close>

lemma base: \<open>set A \<inter> set B \<noteq> {} \<Longrightarrow> map Pro A \<then> map Pro B\<close>
proof -
  assume \<open>set A \<inter> set B \<noteq> {}\<close>
  then obtain n A' B' where \<open>set (n # A') = set A\<close> \<open>set (n # B') = set B\<close>
    by auto
  moreover have \<open>map Pro (n # A') \<then> map Pro (n # B')\<close>
    using Basic by simp
  ultimately show ?thesis
    using Set_L Set_R set_map by metis
qed

lemma just: \<open>\<mu>' A B C D = [] \<Longrightarrow> map Pro A @ C \<then> map Pro B @ D\<close>
proof (induct A B C D rule: \<mu>'.induct)
  case (3 A B C)
  have \<open>\<bottom> # map Pro A @ C \<then> map Pro B\<close>
    using Fls_L by simp
  then show ?case
    using Set_L by simp
next
  case (5 A B p q C)
  then have *: \<open>map Pro A @ C \<then> map Pro B @ [p]\<close> \<open>map Pro A @ q # C \<then> map Pro B\<close>
    by simp_all
  have \<open>map Pro A @ C \<then> p # map Pro B\<close> \<open>q # map Pro A @ C \<then> map Pro B\<close>
    by (use * Set_R in simp) (use * Set_L in simp)
  then show ?case
    using Imp_L Set_L by fastforce
next
  case (6 A B C p q D)
  then have \<open>map Pro A @ p # C \<then> map Pro B @ q # D\<close>
    by simp
  then have \<open>p # map Pro A @ C \<then> q # map Pro B @ D\<close>
    using Set_L Set_R Un_insert_right list.set(2) set_append by metis
  then show ?case
    using Imp_R Set_R by fastforce
qed (auto simp: base intro: SC.intros split: if_splits)

theorem main: \<open>\<mu> [] [] [] [p] \<longleftrightarrow> (\<forall>i. semantics i p)\<close>
proof -
  have \<open>\<mu> [] [] [] [p] \<Longrightarrow> semantics i p\<close> for i p
    using just micro proper by fastforce
  then show ?thesis
    using cex micro list.set_intros(1) neq_Nil_conv set_append Un_iff by metis
qed

end
