(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024 *)

theory Canonical_Models
  imports Skolem_Normal_Form
begin

(* monotonicity is not proven automatically here. Why? How to fix it? *)

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

end