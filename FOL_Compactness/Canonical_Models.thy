(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Canonical_Models
  imports Skolem_Normal_Form
begin

inductive_set terms_set :: \<open>(nat \<times> nat) set \<Rightarrow> nterm set\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>(Var v) \<in> terms_set fns\<close>
| fn: \<open>(Fun f ts) \<in> terms_set fns\<close>
  if \<open>(f, length ts) \<in> fns\<close> \<open>\<And>t. t \<in> set ts \<Longrightarrow> t \<in> terms_set fns\<close>

(*
inductive_set terms_set :: \<open>(nat \<times> nat) set \<Rightarrow> nterm set\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>(Var v) \<in> terms_set fns\<close>
| fn: \<open>(f, length ts) \<in> fns \<and> set ts \<in> Pow (terms_set fns) \<Longrightarrow> (Fun f ts) \<in> terms_set fns\<close>
*)

(*
(* monotonicity is not proven automatically here. Why? How to fix it? *)
(* \<longrightarrow> avoid the use of list_all in inductive definitions *)

term \<open>t :: nterm\<close>
term size
term \<open>num_funs\<close>

lemma subterm_decreases: \<open>\<forall>t \<in> set ts. num_funs t < num_funs (Fun f ts)\<close>
proof
  fix t
  assume \<open>t \<in> set ts\<close>
  then show \<open>num_funs t < num_funs (Fun f ts)\<close>
  proof (induction t arbitrary: f ts)
    case (Var x)
    then show ?case by simp
  next
    case (Fun g rs)
    have \<open>sum_list (map num_funs ts) \<ge> num_funs (Fun g rs)\<close>
      using Fun(2) by (simp add: sum_list_map_remove1)
    then show ?case by simp
  qed
qed

lemma mono_terms: \<open>mono
  (\<lambda>p x. (\<exists>v. (x :: nterm) = Var v) \<or> 
  (\<exists>f ts. x = Fun f ts \<and> (f, length ts) \<in> fns \<and> FOL_Semantics.list_all p ts))\<close>
  unfolding mono_def apply simp
proof clarsimp
  fix x y f and ts :: "nterm list"
  assume \<open>x \<le> y\<close>
    and \<open>\<not> fold (\<lambda>l b. b \<and> y l) ts True\<close>
    and \<open>(f, length ts) \<in> fns\<close> 
    and \<open>fold (\<lambda>l b. b \<and> x l) ts True\<close>
  then show False
    using subterm_decreases
    by (metis fold_bool_prop le_boolD le_funD)
qed

lemma mono_terms_subgoal: \<open>\<And>(x :: nterm \<Rightarrow> bool) y (xa :: nterm) (f :: nat) ts.
       x (x18 x y xa f ts) \<longrightarrow> y (x18 x y xa f ts) \<Longrightarrow>
       list_all x ts \<longrightarrow> list_all y ts\<close>
  unfolding list_all_def mono_def
  using subterm_decreases fold_bool_prop le_boolD le_funD
  sorry

(* surprisingly I can prove the failed goal statement (mono_terms) but that cannot be used in the 
 * inductive definitions below. Instead, I must use mono_terms_subgoal but I have a hard time 
 * proving that one... *)
inductive terms :: \<open>(nat \<times> nat) set \<Rightarrow> nterm \<Rightarrow> bool\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>terms fns (Var v)\<close>
| fn: \<open>(f, length ts) \<in> fns \<and> list_all (terms fns) ts \<Longrightarrow> terms fns (Fun f ts)\<close>
monos mono_terms_subgoal

inductive_set terms_set :: \<open>(nat \<times> nat) set \<Rightarrow> nterm set\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>(Var v) \<in> terms_set fns\<close>
| fn: \<open>(f, length ts) \<in> fns \<and> list_all (\<lambda>t. t \<in> terms_set fns) ts \<Longrightarrow> (Fun f ts) \<in> terms_set fns\<close>
monos mono_terms_subgoal

(*
fun in_terms :: \<open>(nat \<times> nat) set \<Rightarrow> nterm \<Rightarrow> bool\<close> where
  \<open>in_terms fns (Var v) = True\<close>
| \<open>in_terms fns (Fun f ts) = ((f, length ts) \<in> fns \<and> list_all (in_terms fns) ts)\<close>
*)
(*
primrec in_terms :: \<open>nterm \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool\<close> where
  \<open>in_terms (Var v) fns = True\<close>
| \<open>in_terms (Fun f ts) fns = ((f, length ts) \<in> fns \<and> list_all (\<lambda>t. in_terms t fns) ts)\<close>
*)

*)

(* STUPID_CANONDOM_LEMMA in hol-light *)
lemma stupid_canondom: \<open>t \<in> terms_set (fst \<L>) \<Longrightarrow> functions_term t \<subseteq> (fst \<L>)\<close>
  by (induction t rule: terms_set.induct) auto

(* FINITE_SUBSET_INSTANCE in hol-light *)
lemma finite_subset_instance: \<open>finite t' \<Longrightarrow> t' \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> s} \<Longrightarrow>
  (\<exists>t. finite t \<and> t \<subseteq> s \<and> t' \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> t})\<close>
proof (induction t' rule: finite.induct)
  case emptyI
  then show ?case by blast
next
  case (insertI A a)
  obtain \<phi>a where phi_in: \<open>\<phi>a \<in> s\<close> and phi_ex_subs: \<open>\<exists>\<sigma>. P \<sigma> \<and> a = \<phi>a \<cdot>\<^sub>f\<^sub>m \<sigma>\<close>
    using insertI(3) by auto
  obtain \<Phi> where Phi_subs: \<open>\<Phi> \<subseteq> s\<close> and \<open>finite \<Phi>\<close> and Phi_set: \<open>A \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> \<Phi>}\<close>
    using insertI(3) insertI(2) by auto
  then have \<open>finite (\<phi>a \<triangleright> \<Phi>)\<close>
    by auto
  moreover have \<open>(\<phi>a \<triangleright> \<Phi>) \<subseteq> s\<close>
    using phi_in Phi_subs by auto
  moreover have \<open>a \<triangleright> A \<subseteq> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<sigma> \<phi>. P \<sigma> \<and> \<phi> \<in> (\<phi>a \<triangleright> \<Phi>)}\<close>
    using phi_ex_subs Phi_set by blast
  ultimately show ?case by blast
qed

(* FINITE_SUBSET_SKOLEM in hol-light *)
lemma finite_subset_skolem: \<open>finite u \<Longrightarrow> u \<subseteq> {skolem \<phi> |\<phi>. \<phi> \<in> s} \<Longrightarrow>
  (\<exists>t. finite t \<and> t \<subseteq> s \<and> u = {skolem \<phi> |\<phi>. \<phi> \<in> t})\<close>
proof (induction u rule: finite.induct)
  case emptyI
  then show ?case by auto
next
  case (insertI A a)
  obtain \<phi>a where phi_in: \<open>\<phi>a \<in> s\<close> and phi_ex_subs: \<open>a = skolem \<phi>a\<close>
    using insertI(3) by auto
  obtain \<Phi> where Phi_subs: \<open>\<Phi> \<subseteq> s\<close> and \<open>finite \<Phi>\<close> and Phi_set: \<open>A = {skolem \<phi> |\<phi>. \<phi> \<in> \<Phi>}\<close>
    using insertI(3) insertI(2) by auto
  then have \<open>finite (\<phi>a \<triangleright> \<Phi>)\<close>
    by auto
  moreover have \<open>(\<phi>a \<triangleright> \<Phi>) \<subseteq> s\<close>
    using phi_in Phi_subs by auto
  moreover have \<open>a \<triangleright> A = {skolem \<phi> |\<phi>. \<phi> \<in> (\<phi>a \<triangleright> \<Phi>)}\<close>
    using phi_ex_subs Phi_set by blast
  ultimately show ?case
    by blast
qed

(* VALUATION_EXISTS in hol-light *)
lemma valuation_exists: \<open>\<not> (dom M = {}) \<Longrightarrow> \<exists>\<beta>. is_valuation M \<beta>\<close>
  unfolding dom_def is_valuation_def by fast

(* HOLDS_ITLIST_EXISTS in hol-light *)
lemma holds_itlist_exists: \<open>(M\<^bold>,\<beta> \<Turnstile> (fold (\<lambda>x p. \<^bold>\<exists>x\<^bold>. p) xs \<phi>)) \<equiv> (\<exists>as. length as = length xs \<and>
  list_all (\<lambda>a. a \<in> dom M) as \<and> 
  (M\<^bold>,(fold (\<lambda>xa \<beta>. \<beta>(fst xa := snd xa)) (rev (zip xs as)) \<beta>) \<Turnstile> \<phi>))\<close>
proof (induction xs arbitrary: \<beta> \<phi>)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have \<open>M\<^bold>,\<beta> \<Turnstile> fold (\<lambda>x p. (\<^bold>\<exists> x\<^bold>. p)) (x # xs) \<phi> = M\<^bold>,\<beta> \<Turnstile> fold (\<lambda>x p. (\<^bold>\<exists> x\<^bold>. p)) xs (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>
    by simp
  also have \<open>... = (\<exists>as. length as = length xs \<and>
        list_all (\<lambda>a. a \<in> FOL_Semantics.dom M) as \<and>
        M\<^bold>,fold (\<lambda>xa \<beta>. \<beta>(fst xa := snd xa)) (rev (zip xs as)) \<beta> \<Turnstile> (\<^bold>\<exists>x\<^bold>. \<phi>))\<close>
    using Cons by simp
  then show ?case
    sorry
qed


end