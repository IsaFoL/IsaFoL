(* Title:        Part of the proof of compactness of first-order logic following Harrison's in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2024
                 Larry Paulson, 2024 *)

theory Canonical_Models
  imports Skolem_Normal_Form
begin

inductive_set terms_set :: \<open>(nat \<times> nat) set \<Rightarrow> nterm set\<close> for fns :: \<open>(nat \<times> nat) set\<close> where
  vars: \<open>(Var v) \<in> terms_set fns\<close>
| fn: \<open>(Fun f ts) \<in> terms_set fns\<close>
  if \<open>(f, length ts) \<in> fns\<close> \<open>\<And>t. t \<in> set ts \<Longrightarrow> t \<in> terms_set fns\<close>

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
lemma holds_itlist_exists: 
  \<open>(M\<^bold>,\<beta> \<Turnstile> (foldr (\<lambda>x p. \<^bold>\<exists>x\<^bold>. p) xs \<phi>)) \<longleftrightarrow> 
     (\<exists>as. length as = length xs \<and> set as \<subseteq> dom M \<and> 
           (M\<^bold>,(foldr (\<lambda>u \<beta>. \<beta>(fst u := snd u)) (rev (zip xs as)) \<beta>) \<Turnstile> \<phi>))\<close>
proof (induction xs arbitrary: \<beta> \<phi>)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
    by (force simp add: Cons length_Suc_conv simp flip: fun_upd_def)
qed

definition canonical :: "(nat \<times> nat) set \<times> (nat \<times> nat) set \<Rightarrow> nterm intrp \<Rightarrow> bool" where
\<open>canonical \<L> \<M> \<equiv> (dom \<M> = terms_set (fst \<L>) \<and> (\<forall>f. intrp_fn \<M> f = Fun f))\<close>


fun formula_to_form :: \<open>(nat\<times>nterm list) formula \<Rightarrow> form\<close> where
  \<open>formula_to_form (formula.Atom (p,ts)) = Atom p ts\<close>
| \<open>formula_to_form \<bottom> = \<^bold>\<bottom>\<close>
| \<open>formula_to_form (formula.Not \<phi>) = \<^bold>\<not> (formula_to_form \<phi>)\<close>
| \<open>formula_to_form (formula.And \<phi> \<psi>) = (formula_to_form \<phi>) \<^bold>\<and> (formula_to_form \<psi>)\<close>
| \<open>formula_to_form (formula.Or \<phi> \<psi>) = (formula_to_form \<phi>) \<^bold>\<or> (formula_to_form \<psi>)\<close>
| \<open>formula_to_form (\<phi> \<^bold>\<rightarrow> \<psi>) = (formula_to_form \<phi>) \<^bold>\<longrightarrow> (formula_to_form \<psi>)\<close>

(* - slight deviation from the hol-light definition where "Atom p ts" appears on the left, which is
   forbidden in Isabelle, I don't see how to define it only for atoms and obtain a propositional
   interpretation. 
   - type translation to bridge with prop compactness result from AFP *)
definition prop_of_model :: "'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> (nat \<times> nterm list) formula \<Rightarrow> bool" where
  \<open>prop_of_model \<M> \<beta> \<phi> \<equiv> \<M>\<^bold>,\<beta> \<Turnstile> formula_to_form \<phi>\<close>

(* the predicates are not defined exactly in the same way here and in hol-light, 
   I replaced the predicate d with the set of all valid atoms and the function returns the list
   of accepted arguments for a given predicate instead of being a Boolean for compatibility.
*)
definition canon_of_prop :: "((nat \<times> nat) set \<times> (nat \<times> nat) set) \<Rightarrow> (form \<Rightarrow> bool) \<Rightarrow> nterm intrp" where
  \<open>canon_of_prop \<L> I \<equiv> Abs_intrp (terms_set (fst \<L>), (\<lambda>f ts. Fun f ts), (\<lambda>p. {ts. I (Atom p ts)}))\<close>

lemma formula_to_form_to_formula: \<open>qfree \<phi> \<Longrightarrow> formula_to_form (form_to_formula \<phi>) = \<phi>\<close>
  by (induction \<phi>) simp+

(* PHOLDS_PROP_OF_MODEL in hol-light *)
lemma pholds_prop_of_model: 
  \<open>qfree \<phi> \<Longrightarrow> (prop_of_model \<M> \<beta>) (form_to_formula \<phi>) \<longleftrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
  unfolding prop_of_model_def using formula_to_form_to_formula by simp

(* PROP_OF_CANON_OF_PROP in hol-light *)
lemma prop_of_canon_of_prop: 
  \<open>prop_of_model (canon_of_prop \<L> I) \<beta> (form_to_formula (Atom p ts)) = I (Atom p ts)\<close>
  unfolding canon_of_prop_def
  sorry

(* HOLDS_CANON_OF_PROP in hol-light *)
lemma holds_canon_of_prop:
  \<open>qfree \<phi> \<Longrightarrow> (canon_of_prop \<L> I)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p \<phi>\<close>
  sorry

(* HOLDS_CANON_OF_PROP_GENERAL in hol-light *)
(* never used afterwards, maybe we can skip it. 
    It is strange to apply a valuation to a formula anyway, it is a kind of misuse of the fact that 
    valuations for canonical models and substitutions have the same type *)
lemma holds_canon_of_prop_general: \<open>qfree \<phi> \<Longrightarrow> (canon_of_prop \<L> I)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)\<close>
  unfolding canon_of_prop_def
  sorry

(* CANONICAL_CANON_OF_PROP in hol-light *)
lemma canonical_canon_of_prop: \<open>canonical \<L> (canon_of_prop \<L> I)\<close>
  unfolding canonical_def canon_of_prop_def
  by (metis dom_Abs_is_fst emptyE intrp_fn_Abs_is_fst_snd struct_def terms_set.vars)

end