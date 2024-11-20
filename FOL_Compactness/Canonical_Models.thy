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

(* STUPID_CANONDOM_LEMMA in HOL Light *)
lemma stupid_canondom: \<open>t \<in> terms_set (fst \<L>) \<Longrightarrow> functions_term t \<subseteq> (fst \<L>)\<close>
  by (induction t rule: terms_set.induct) auto

(* FINITE_SUBSET_INSTANCE in HOL Light *)
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

(* FINITE_SUBSET_SKOLEM in HOL Light *)
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

(* VALUATION_EXISTS in HOL Light *)
lemma valuation_exists: \<open>\<not> (dom M = {}) \<Longrightarrow> \<exists>\<beta>. is_valuation M \<beta>\<close>
  unfolding dom_def is_valuation_def by fast

(* HOLDS_ITLIST_EXISTS in HOL Light *)
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

(* Slight deviation from the HOL Light definition where "Atom p ts" appears on the left, which is
   forbidden in Isabelle, I don't see how to define it only for atoms and obtain a propositional
   interpretation: *)
(* prop_of_model in HOL Light *)
definition pintrp_of_intrp :: "'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> (form \<Rightarrow> bool)" where
  \<open>pintrp_of_intrp \<M> \<beta> = (\<lambda>\<phi>. \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>

(* the predicates are not defined exactly in the same way here and in HOL Light, 
   I replaced the predicate d with the set of all valid atoms and the function returns the list
   of accepted arguments for a given predicate instead of being a Boolean for compatibility.
*)
definition 
  canon_of_prop :: "((nat \<times> nat) set \<times> (nat \<times> nat) set) \<Rightarrow> (form \<Rightarrow> bool) \<Rightarrow> nterm intrp" where
  \<open>canon_of_prop \<L> I \<equiv> Abs_intrp (terms_set (fst \<L>), Fun, (\<lambda>p. {ts. I (Atom p ts)}))\<close>

lemma pholds_pintrp_of_intrp:
  \<open>qfree \<phi> \<Longrightarrow> (pintrp_of_intrp \<M> \<beta>) \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
  unfolding pintrp_of_intrp_def by (induction \<phi>) simp+

(* PROP_OF_CANON_OF_PROP in HOL Light *)
lemma intrp_of_canon_of_prop [simp]:
  \<open>pintrp_of_intrp (canon_of_prop \<L> I) Var (Atom p ts) = I (Atom p ts)\<close>
proof -
  have \<section>: "terms_set (fst \<L>) \<noteq> {}"
    using terms_set.vars by auto
  have "\<forall>t \<in> set ts. \<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),Var\<^esup> = t" 
  proof (induction ts)
    case Nil
    then show ?case by simp
  next
    case (Cons t ts)
    have "\<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),Var\<^esup> = t"
    proof (induction t)
      case (Var x)
      then show ?case
        by simp
    next
      case Fun
      then show ?case
        by (simp add: \<section> struct_def map_idI)
    qed
    with Cons show ?case
      by simp
  qed
  then show ?thesis
    by (simp add: \<section> struct_def canon_of_prop_def pintrp_of_intrp_def holds_def map_idI)
qed

(* HOLDS_CANON_OF_PROP in HOL Light *)
lemma holds_canon_of_prop:
  assumes \<open>qfree \<phi>\<close> shows \<open>(canon_of_prop \<L> I)\<^bold>,Var \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p \<phi>\<close>
proof -
  have "pintrp_of_intrp (canon_of_prop \<L> I) Var \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p \<phi>"
    using assms
    by (induction \<phi>) auto
  with assms show ?thesis
    using pholds_pintrp_of_intrp by blast
qed

(* HOLDS_CANON_OF_PROP_GENERAL in HOL Light *)
(* never used afterwards.
    It is strange to apply a valuation to a formula anyway, it is a kind of misuse of the fact that 
    valuations for canonical models and substitutions have the same type *)
lemma holds_canon_of_prop_general: 
  assumes \<open>qfree \<phi>\<close> shows \<open>(canon_of_prop \<L> I)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)\<close>
proof -
  have "pintrp_of_intrp (canon_of_prop \<L> I) \<beta> \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)"
    using assms
  proof (induction \<phi>)
    case Atom
    have "\<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),\<beta>\<^esup> = t \<cdot> \<beta>" for t
      using term_subst_eval by (metis empty_iff intrp_fn_Abs_is_fst_snd struct_def terms_set.simps)
    moreover have "struct (terms_set (fst \<L>))"
      by (metis empty_iff struct.intro terms_set.vars)
    ultimately show ?case
      by (simp add: canon_of_prop_def pintrp_of_intrp_def Atom)
  qed auto
  with assms show ?thesis
    by (simp add: pholds_pintrp_of_intrp)
qed

(* CANONICAL_CANON_OF_PROP in HOL Light *)
lemma canonical_canon_of_prop: \<open>canonical \<L> (canon_of_prop \<L> I)\<close>
  unfolding canonical_def canon_of_prop_def
  by (metis dom_Abs_is_fst emptyE intrp_fn_Abs_is_fst_snd struct_def terms_set.vars)

(* INTERPRETATION_CANON_OF_PROP in hol-ligh *)
lemma interpretation_canon_of_prop: \<open>is_interpretation \<L> (canon_of_prop \<L> I)\<close>
  unfolding is_interpretation_def canon_of_prop_def
  by (metis (no_types, lifting) canonical_canon_of_prop canonical_def dom_Abs_is_fst 
      intrp_fn_Abs_is_fst_snd intrp_is_struct subset_code(1) terms_set.fn)

(* PROP_VALID_IMP_FOL_VALID in HOL Light *)
lemma prop_valid_imp_fol_valid: \<open>qfree \<phi> \<and> (\<forall>I. I \<Turnstile>\<^sub>p \<phi>) \<Longrightarrow> (\<forall>\<M> \<beta>. \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
  using pholds_pintrp_of_intrp by fast

(* FOL_VALID_IMP_PROP_VALID *)
lemma fol_valid_imp_prop_valid: \<open>qfree \<phi> \<and> (\<forall>\<M> \<beta>. canonical (language {\<phi>}) \<M> \<longrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)
  \<Longrightarrow> \<forall>I. I \<Turnstile>\<^sub>p \<phi>\<close>
  using canonical_canon_of_prop holds_canon_of_prop by blast

(* TODO: as a definition included in Ground_FOL_Compactness, where pholds is defined? *)
abbreviation psatisfies where \<open>psatisfies I \<Phi> \<equiv> \<forall>\<phi>\<in>\<Phi>. I \<phi>\<close>

(* SATISFIES_PSATISFIES *)
lemma satisfies_psatisfies: \<open>(\<forall>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>) \<and> satisfies \<M> \<Phi> \<and> is_valuation \<M> \<beta> \<Longrightarrow>
  psatisfies (pintrp_of_intrp \<M> \<beta>) \<Phi>\<close>
  using pholds_pintrp_of_intrp unfolding satisfies_def by (simp add: pintrp_of_intrp_def)

find_consts name: terms

(* PSATISFIES_INSTANCES in HOL Light *)
lemma psatisfies_instances:
  assumes qf: \<open>(\<And>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>)\<close>
    and ps: \<open>psatisfies I {\<phi> \<cdot>\<^sub>f\<^sub>m \<beta> |\<phi> \<beta>. (\<forall>x. \<beta> x \<in> terms_set (fst \<L>)) \<and> \<phi> \<in> \<Phi>}\<close>
  shows \<open>satisfies (canon_of_prop \<L> I) \<Phi>\<close>
  sorry

(* SATISFIES_INSTANCES in HOL Light *)
lemma satisfies_instances: \<open>(is_interpretation (language \<Xi>) \<M> \<Longrightarrow> 
 (satisfies \<M> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<phi> \<sigma>. \<phi> \<in> \<Phi> \<and> (\<forall>x. \<sigma> x \<in> terms_set (fst (language \<Xi>)))}) \<longleftrightarrow>
  satisfies \<M> \<Phi>)\<close>
  sorry

(* COMPACT_CANON_QFREE in HOL Light *)
(* I don't see the point of \<open>language \<Xi>\<close> here instead of, e.g., \<L> *)
lemma compact_canon_qfree: \<open>(\<forall>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>) \<and> 
  (\<forall>\<Psi>. finite \<Psi> \<and> \<Psi> \<subseteq> \<Phi> \<longrightarrow> (\<exists>\<M>. is_interpretation (language \<Xi>) \<M> \<and> \<not> (dom \<M> = {}) \<and> 
    satisfies \<M> \<Psi>)) \<Longrightarrow> \<exists>\<C>. is_interpretation (language \<Xi>) \<C> \<and> canonical (language \<Xi>) \<C> \<and>
    satisfies \<C> \<Phi>\<close>
  sorry

(* INTERPRETATION_RESTRICTLANGUAGE in HOL Light *)
lemma interpretation_restrictlanguage: \<open>\<Psi> \<subseteq> \<Phi> \<and> is_interpretation (language \<Phi>) \<M> \<Longrightarrow>
  is_interpretation (language \<Psi>) \<M>\<close>
  unfolding is_interpretation_def language_def functions_forms_def predicates_def
  by (metis Union_mono fstI image_mono in_mono)

(* INTERPRETATION_EXTENDLANGUAGE in HOL Light *)
lemma interpretation_extendlanguage: 
  \<open>is_interpretation (language \<Psi>) \<M> \<and> \<not> (dom \<M> = {}) \<and> satisfies \<M> \<Psi> \<Longrightarrow> \<exists>\<M>'. 
    (dom \<M>' = dom \<M>) \<and> (intrp_rel \<M>' = intrp_rel \<M>) \<and> is_interpretation (language \<Phi>) \<M>'
    \<and> satisfies \<M>' \<Psi>\<close>
  unfolding is_interpretation_def language_def functions_forms_def predicates_def satisfies_def
  sorry

(* COMPACT_LS in HOL Light *)
lemma compact_ls: \<open>(\<forall>\<Psi>. finite \<Psi> \<and> \<Psi> \<subseteq>\<Phi> \<Longrightarrow> (\<exists>\<M>. is_interpretation (language \<Phi>) \<M> \<and>
  \<not> (dom \<M> = {}) \<and> satisfies \<M> \<Psi>)) \<Longrightarrow> \<exists>\<C>. is_interpretation (language \<Phi>) \<C> \<and>
  \<not> (dom \<C> = {}) \<and> satisfies \<C> \<Phi>\<close>
  sorry



end