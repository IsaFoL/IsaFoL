(*  Title:      HOL_Light_Maps_Set.thy
    Author:     Stéphane Glondu, Inria, 2024
*)

section \<open>Type and constant mappings of HOL Light's set theory\<close>

theory HOL_Light_Maps_Set
  imports
    Import_Setup
begin

definition empty where "empty = (\<lambda>_. False)"
definition member where "member = (\<lambda>x A. x \<in> Collect A)"
definition insert where "insert = (\<lambda>x s z. z \<in> Set.insert x (Collect s))"
definition subset where "subset = (\<lambda>A B. Collect A \<subseteq> Collect B)"
definition finite where "finite = (\<lambda>A. Finite_Set.finite (Collect A))"

lemma [import_const EMPTY : empty]: "empty = (\<lambda>(_::'A). False)"
  using empty_def by blast

lemma [import_const IN : member]: "member = (\<lambda>(x::'A) (A::'A \<Rightarrow> bool). A x)"
  using member_def by simp

lemma [import_const INSERT : insert]:
  "insert = (\<lambda>(x::'A) (s::'A \<Rightarrow> bool) (y::'A). member y s \<or> y = x)"
  using insert_def member_def by (metis insert_iff)

lemma [import_const SUBSET : subset]:
  "subset = (\<lambda>(A::'A \<Rightarrow> bool) (B::'A \<Rightarrow> bool). \<forall>(x::'A). member x A \<longrightarrow> member x B)"
  by (simp add: member_def subset_def subset_iff)

lemma [import_const FINITE : finite]:
  "finite = (\<lambda>(a::'A \<Rightarrow> bool). \<forall>(FINITE'::('A \<Rightarrow> bool) \<Rightarrow> bool). (\<forall>(a::'A \<Rightarrow> bool). a = empty \<or> (\<exists>(x::'A) (s::'A \<Rightarrow> bool). a = insert x s \<and> FINITE' s) \<longrightarrow> FINITE' a) \<longrightarrow> FINITE' a)"
proof
  fix a :: "'A \<Rightarrow> bool"
  show "finite a = (\<forall>FINITE'. (\<forall>a. a = empty \<or> (\<exists>x s. a = insert x s \<and> FINITE' s) \<longrightarrow> FINITE' a) \<longrightarrow> FINITE' a)" (is "?L = ?R")
  proof
    assume "?L"
    hence finite_a: "\<forall>P. (\<forall>a. a = {} \<or> (\<exists>x s. a = Set.insert x s \<and> P s) \<longrightarrow> P a) \<longrightarrow> P (Collect a)"
      by (metis finite_def finite_induct)
    show "?R"
    proof
      fix FINITE' :: "('A \<Rightarrow> bool) \<Rightarrow> bool"
      show "(\<forall>a. a = empty \<or> (\<exists>x s. a = insert x s \<and> FINITE' s) \<longrightarrow> FINITE' a) \<longrightarrow> FINITE' a"
      proof
        assume finite_induct: "\<forall>a. a = empty \<or> (\<exists>x s. a = insert x s \<and> FINITE' s) \<longrightarrow> FINITE' a"
        define P :: "'A set \<Rightarrow> bool" where "P = (\<lambda>A. FINITE' (\<lambda>z. z \<in> A))"
        have "\<forall>a. a = {} \<or> (\<exists>x s. a = Set.insert x s \<and> P s) \<longrightarrow> P a"
        proof
          fix a :: "'A set"
          show "a = {} \<or> (\<exists>x s. a = Set.insert x s \<and> P s) \<longrightarrow> P a"
          proof
            assume P_induct: "a = {} \<or> (\<exists>x s. a = Set.insert x s \<and> P s)"
            define A :: "'A \<Rightarrow> bool" where "A = (\<lambda>z. z \<in> a)"
            have "a = {} \<longrightarrow> A = empty"
              by (simp add: A_def empty_def)
            moreover have "(\<exists>x s. a = Set.insert x s \<and> P s) \<longrightarrow> (\<exists>x s. A = insert x s \<and> P (Collect s))"
              unfolding A_def insert_def by fastforce
            ultimately have "A = empty \<or> (\<exists>x s. A = insert x s \<and> FINITE' s)"
              using P_def P_induct by auto
            hence "FINITE' A"
              using finite_induct by metis
            thus "P a"
              using A_def P_def by blast
          qed
        qed
        thus "FINITE' a"
          by (metis finite_a Collect_inj Collect_mem_eq P_def)
      qed
    qed
  next
    assume finite_a: "?R"
    have "\<forall>P. (\<lambda>x. x = {} \<or> (\<exists>A. (\<exists>a. x = Set.insert a A) \<and> P A)) \<le> P \<longrightarrow> P (Collect a)"
    proof
      fix P :: "'A set \<Rightarrow> bool"
      show "(\<lambda>x. x = {} \<or> (\<exists>A. (\<exists>a. x = Set.insert a A) \<and> P A)) \<le> P \<longrightarrow> P (Collect a)"
      proof
        define FINITE' :: "('A \<Rightarrow> bool) \<Rightarrow> bool" where "FINITE' = (\<lambda>A. P (Collect A))"
        assume "(\<lambda>x. x = {} \<or> (\<exists>A. (\<exists>a. x = Set.insert a A) \<and> P A)) \<le> P"
        hence "\<forall>a. a = empty \<or> (\<exists>x s. a = insert x s \<and> FINITE' s) \<longrightarrow> FINITE' a"
          by (smt (verit, best) Collect_cong FINITE'_def empty_def insert_def empty_Collect_eq insert_compr mem_Collect_eq predicate1D)
        thus "P (Collect a)"
          by (metis FINITE'_def finite_a)
        qed
    qed
    thus "?L"
      by (smt (verit, best) finite_def finite.simps predicate1I)
  qed
qed

definition gspec where "gspec = (\<lambda>p. p)"
definition setspec where "setspec = (\<lambda>v P t. P \<and> (v = t))"
definition union where "union = (\<lambda>A B z. z \<in> Collect A \<union> Collect B)"

lemma [import_const GSPEC : gspec]: "gspec = (\<lambda>(p :: 'A \<Rightarrow> bool). p)"
  unfolding gspec_def by auto

lemma [import_const SETSPEC : setspec]: "setspec = (\<lambda>(v :: 't83135) P t. P \<and> (v = t))"
  unfolding setspec_def by auto

lemma [import_const UNION : union]:
  "union = (\<lambda>(s :: 'A \<Rightarrow> bool) t. gspec (\<lambda>z. \<exists>x. setspec z (member x s \<or> member x t) x))"
  unfolding union_def gspec_def setspec_def
  by (simp add: HOL_Light_Maps_Set.member_def)

end
