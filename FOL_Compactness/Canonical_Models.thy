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

lemma struct_terms_set [iff]: \<open>struct (terms_set A)\<close>
  by (metis empty_iff struct.intro terms_set.vars)

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

definition canonical :: \<open>(nat \<times> nat) set \<times> (nat \<times> nat) set \<Rightarrow> nterm intrp \<Rightarrow> bool\<close> where
\<open>canonical \<L> \<M> \<equiv> (dom \<M> = terms_set (fst \<L>) \<and> (\<forall>f. intrp_fn \<M> f = Fun f))\<close>

(* Slight deviation from the HOL Light definition where "Atom p ts" appears on the left, which is
   forbidden in Isabelle, I don't see how to define it only for atoms and obtain a propositional
   interpretation: *)
(* prop_of_model in HOL Light *)
definition pintrp_of_intrp :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> (form \<Rightarrow> bool)\<close> where
  \<open>pintrp_of_intrp \<M> \<beta> = (\<lambda>\<phi>. \<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>

(* the predicates are not defined exactly in the same way here and in HOL Light, 
   I replaced the predicate d with the set of all valid atoms and the function returns the list
   of accepted arguments for a given predicate instead of being a Boolean for compatibility.
*)
definition 
  canon_of_prop :: \<open>((nat \<times> nat) set \<times> (nat \<times> nat) set) \<Rightarrow> (form \<Rightarrow> bool) \<Rightarrow> nterm intrp\<close> where
  \<open>canon_of_prop \<L> I \<equiv> Abs_intrp (terms_set (fst \<L>), Fun, (\<lambda>p. {ts. I (Atom p ts)}))\<close>

lemma dom_canon_of_prop [simp]: \<open>dom (canon_of_prop \<L> I) = terms_set (fst \<L>)\<close>
  by (simp add: canon_of_prop_def)

lemma intrp_fn_canon_of_prop [simp]: \<open>intrp_fn (canon_of_prop \<L> I) = Fun\<close>
  by (simp add: canon_of_prop_def)

lemma intrp_rel_canon_of_prop [simp]: \<open>intrp_rel (canon_of_prop \<L> I) = (\<lambda>p. {ts. I (Atom p ts)})\<close>
  by (simp add: canon_of_prop_def)

lemma pholds_pintrp_of_intrp:
  \<open>qfree \<phi> \<Longrightarrow> (pintrp_of_intrp \<M> \<beta>) \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
  unfolding pintrp_of_intrp_def by (induction \<phi>) simp+

(* PROP_OF_CANON_OF_PROP in HOL Light *)
lemma intrp_of_canon_of_prop [simp]:
  \<open>pintrp_of_intrp (canon_of_prop \<L> I) Var (Atom p ts) = I (Atom p ts)\<close>
proof -
  have \<section>: \<open>terms_set (fst \<L>) \<noteq> {}\<close>
    using terms_set.vars by auto
  have \<open>\<forall>t \<in> set ts. \<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),Var\<^esup> = t\<close> 
  proof (induction ts)
    case Nil
    then show ?case by simp
  next
    case (Cons t ts)
    have \<open>\<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),Var\<^esup> = t\<close>
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
  have \<open>pintrp_of_intrp (canon_of_prop \<L> I) Var \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p \<phi>\<close>
    using assms
    by (induction \<phi>) auto
  with assms show ?thesis
    using pholds_pintrp_of_intrp by blast
qed

(* HOLDS_CANON_OF_PROP_GENERAL in HOL Light *)
(* It is strange to apply a valuation to a formula anyway, it is a kind of misuse of the fact that 
    valuations for canonical models and substitutions have the same type *)
lemma holds_canon_of_prop_general: 
  assumes \<open>qfree \<phi>\<close> shows \<open>(canon_of_prop \<L> I)\<^bold>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)\<close>
proof -
  have \<open>pintrp_of_intrp (canon_of_prop \<L> I) \<beta> \<Turnstile>\<^sub>p \<phi> \<longleftrightarrow> I \<Turnstile>\<^sub>p (\<phi> \<cdot>\<^sub>f\<^sub>m \<beta>)\<close>
    using assms
  proof (induction \<phi>)
    case Atom
    have \<open>\<lbrakk>t\<rbrakk>\<^bsup>Abs_intrp (terms_set (fst \<L>), Fun, \<lambda>p. {ts. I (form.Atom p ts)}),\<beta>\<^esup> = t \<cdot> \<beta>\<close> for t
      using term_subst_eval by (metis empty_iff intrp_fn_Abs_is_fst_snd struct_def terms_set.simps)
    moreover have \<open>struct (terms_set (fst \<L>))\<close>
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

(* SATISFIES_PSATISFIES *)
lemma satisfies_psatisfies: \<open>(\<forall>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>) \<and> satisfies \<M> \<Phi> \<and> is_valuation \<M> \<beta> \<Longrightarrow>
  psatisfies (pintrp_of_intrp \<M> \<beta>) \<Phi>\<close>
  using pholds_pintrp_of_intrp satisfies_def by blast

find_consts name: terms

(* PSATISFIES_INSTANCES in HOL Light *)
lemma psatisfies_instances:
  assumes qf: \<open>(\<And>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>)\<close>
    and ps: \<open>psatisfies I {\<phi> \<cdot>\<^sub>f\<^sub>m \<beta> |\<phi> \<beta>. (\<forall>x. \<beta> x \<in> terms_set (fst \<L>)) \<and> \<phi> \<in> \<Phi>}\<close>
  shows \<open>satisfies (canon_of_prop \<L> I) \<Phi>\<close>
  unfolding satisfies_def
  by (smt (verit, ccfv_SIG) dom_canon_of_prop holds_canon_of_prop_general is_valuation_def mem_Collect_eq assms)

(* SATISFIES_INSTANCES in HOL Light *)
lemma satisfies_instances:
  assumes \<open>is_interpretation (language \<Xi>) \<M>\<close>
  shows \<open>satisfies \<M> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> |\<phi> \<sigma>. \<phi> \<in> \<Phi> \<and> (\<forall>x. \<sigma> x \<in> terms_set (fst (language \<Xi>)))} \<longleftrightarrow>
         satisfies \<M> \<Phi>\<close>
  unfolding satisfies_def mem_Collect_eq
proof (intro iffI strip)
  fix \<beta> \<phi>
  assume \<M>: \<open>\<forall>\<beta> \<phi>. is_valuation \<M> \<beta> \<longrightarrow> \<phi> \<in> \<Phi> \<longrightarrow> \<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close> \<open>is_valuation \<M> \<beta>\<close>
    and \<open>\<exists>\<phi>' \<sigma>. \<phi> = \<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma> \<and> \<phi>' \<in> \<Phi> \<and> (\<forall>x. \<sigma> x \<in> terms_set (fst (language \<Xi>)))\<close>
  then obtain \<phi>' \<sigma> where \<sigma>: \<open>\<phi> = \<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>\<close> \<open>\<phi>' \<in> \<Phi>\<close> \<open>\<forall>x. \<sigma> x \<in> terms_set (functions_forms \<Xi>)\<close>
    by (auto simp add: language_def)
  with \<M> assms have \<open>\<M>\<^bold>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) \<Turnstile> \<phi>'\<close>
    by (metis (no_types, lifting) eq_fst_iff interpretation_eval interpretation_sublanguage 
        is_valuation_def language_def stupid_canondom)
  with assms show \<open>\<M>\<^bold>,\<beta> \<Turnstile> \<phi>\<close>
    by (simp add: \<sigma> swap_subst_eval)
qed (metis subst_var terms_set.vars)

(* COMPACT_CANON_QFREE in HOL Light *)
(* I don't see the point of \<open>language \<Xi>\<close> here instead of, e.g., \<L> *)
lemma compact_canon_qfree:
  assumes qf: \<open>\<And>\<phi>. \<phi> \<in> \<Phi> \<longrightarrow> qfree \<phi>\<close>
    and int: \<open>\<And>\<Psi>. \<lbrakk>finite \<Psi>; \<Psi> \<subseteq> \<Phi>\<rbrakk> 
                   \<Longrightarrow> \<exists>\<M>::'a intrp. is_interpretation (language \<Xi>) \<M> \<and> dom \<M> \<noteq> {} \<and> satisfies \<M> \<Psi>\<close>
  obtains \<C> where \<open>is_interpretation (language \<Xi>) \<C>\<close> \<open>canonical (language \<Xi>) \<C>\<close> \<open>satisfies \<C> \<Phi>\<close>
proof -
  define \<Gamma> where "\<Gamma> \<equiv> \<lambda>X. {\<phi> \<cdot>\<^sub>f\<^sub>m \<beta> |\<beta> \<phi>. (\<forall>x. \<beta> x \<in> terms_set (fst (language \<Xi>))) \<and> \<phi> \<in> X}"
  have "psatisfiable (\<Gamma> \<Phi>)"
    unfolding psatisfiable_def
  proof (rule compact_prop)
    fix \<Theta> 
    assume "finite \<Theta>" "\<Theta> \<subseteq> \<Gamma> \<Phi>"
    then have "\<exists>\<Psi>. finite \<Psi> \<and> \<Psi> \<subseteq> \<Phi> \<and> \<Theta> \<subseteq> \<Gamma> \<Psi>"
      using finite_subset_instance \<Gamma>_def by force
    then obtain \<Psi> where \<Psi>: \<open>finite \<Psi>\<close> \<open>\<Psi> \<subseteq> \<Phi>\<close> \<open>\<Theta> \<subseteq> \<Gamma> \<Psi>\<close>
      by auto
    have "psatisfiable \<Theta>"
    proof (rule psatisfiable_mono)
      obtain \<M>::"'a intrp" where \<M>: \<open>is_interpretation (language \<Xi>) \<M>\<close> \<open>dom \<M> \<noteq> {}\<close> \<open>satisfies \<M> \<Psi>\<close>
        using int \<Psi> by meson
      then obtain \<beta> where \<beta>: \<open>is_valuation \<M> \<beta>\<close>
        by (meson valuation_exists)
      moreover have \<open>\<And>\<phi>. \<phi> \<in> \<Gamma> \<Psi> \<longrightarrow> qfree \<phi>\<close>
        using \<Gamma>_def \<Psi> qf qfree_formsubst by auto
      moreover have "satisfies \<M> (\<Gamma> \<Psi>)"
        using \<M> unfolding \<Gamma>_def
        by (smt (verit, del_insts) mem_Collect_eq satisfies_def satisfies_instances)
      ultimately show "psatisfiable (\<Gamma> \<Psi>)"
        by (meson psatisfiable_def satisfies_psatisfies)
    qed (use \<Psi> in auto)
    then show "\<exists>I. psatisfies I \<Theta>"
      using psatisfiable_def by blast
  qed (use qf qfree_formsubst \<Gamma>_def in force)
  with qf that show thesis
    unfolding \<Gamma>_def psatisfiable_def
    by (smt (verit, ccfv_threshold) canonical_canon_of_prop interpretation_canon_of_prop 
        mem_Collect_eq psatisfies_instances)
qed

(* INTERPRETATION_RESTRICTLANGUAGE in HOL Light *)
lemma interpretation_restrictlanguage: \<open>\<Psi> \<subseteq> \<Phi> \<and> is_interpretation (language \<Phi>) \<M> \<Longrightarrow>
  is_interpretation (language \<Psi>) \<M>\<close>
  unfolding is_interpretation_def language_def functions_forms_def predicates_def
  by (metis Union_mono fstI image_mono in_mono)

(* INTERPRETATION_EXTENDLANGUAGE in HOL Light *)
lemma interpretation_extendlanguage: 
  fixes \<M>:: \<open>'a intrp\<close>
  assumes int: \<open>is_interpretation (language \<Psi>) \<M>\<close> and \<open>dom \<M> \<noteq> {}\<close>
    and \<open>satisfies \<M> \<Psi>\<close>
  obtains \<N> where \<open>dom \<N> = dom \<M>\<close> \<open>intrp_rel \<N> = intrp_rel \<M>\<close> 
                    \<open>is_interpretation (language \<Phi>) \<N>\<close> \<open>satisfies \<N> \<Psi>\<close>
proof
  define m where "m \<equiv> (SOME a. a \<in> dom \<M>)"
  have m: "m \<in> dom \<M>"
    by (simp add: \<open>dom \<M> \<noteq> {}\<close> m_def some_in_eq)
  define \<N> where \<open>\<N> \<equiv> Abs_intrp
                    (dom \<M>, 
                     (\<lambda>g zs. if (g,length zs) \<in> functions_forms \<Psi> then intrp_fn \<M> g zs else m),
                     intrp_rel \<M>)\<close>
  show eq: "dom \<N> = dom \<M>" "intrp_rel \<N> = intrp_rel \<M>"
    by (simp_all add: \<N>_def)
  show "is_interpretation (language \<Phi>) \<N>"
  proof -
    have \<section>: "fst (language \<Psi>) = functions_forms \<Psi>"
      by (simp add: language_def)
    obtain \<beta> where "is_valuation \<M> (\<beta> \<M>)"
      by (meson \<open>dom \<M> \<noteq> {}\<close> valuation_exists)
    then have "\<forall>n. \<beta> \<M> n \<in> dom \<M>"
      using is_valuation_def by blast
    with eq m int show ?thesis
      unfolding \<N>_def is_interpretation_def
      by (smt (verit, ccfv_SIG) \<section> intrp_fn_Abs_is_fst_snd intrp_is_struct)
  qed
  show "satisfies \<N> \<Psi>"
    unfolding satisfies_def
  proof (intro strip)
    fix \<beta> \<phi>
    assume \<beta>: "is_valuation \<N> \<beta>" and "\<phi> \<in> \<Psi>"
    then have "is_valuation \<M> \<beta>"
      by (simp add: eq is_valuation_def)
    then have "\<M>\<^bold>,\<beta> \<Turnstile> \<phi>"
      using \<open>\<phi> \<in> \<Psi>\<close> \<open>satisfies \<M> \<Psi>\<close> by (simp add: satisfies_def)
    moreover
    have \<open>(\<N>\<^bold>,\<beta> \<Turnstile> \<phi>) \<longleftrightarrow> (\<M>\<^bold>,\<beta> \<Turnstile> \<phi>)\<close>
    proof (intro holds_cong)
      fix f :: nat and ts :: "'a list"
      assume "(f, length ts) \<in> functions_form \<phi>"
      then show "intrp_fn \<N> f ts = intrp_fn \<M> f ts"
        using \<N>_def \<open>\<phi> \<in> \<Psi>\<close> functions_forms_def by auto
    qed (auto simp: eq)
    ultimately show "\<N>\<^bold>,\<beta> \<Turnstile> \<phi>" by auto
  qed
qed

(* COMPACT_LS in HOL Light *)
lemma compact_ls: \<open>(\<forall>\<Psi>. finite \<Psi> \<and> \<Psi> \<subseteq>\<Phi> \<Longrightarrow> (\<exists>\<M>. is_interpretation (language \<Phi>) \<M> \<and>
  \<not> (dom \<M> = {}) \<and> satisfies \<M> \<Psi>)) \<Longrightarrow> \<exists>\<C>. is_interpretation (language \<Phi>) \<C> \<and>
  \<not> (dom \<C> = {}) \<and> satisfies \<C> \<Phi>\<close>
  sorry

end