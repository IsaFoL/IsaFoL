theory FOL_Compactness
  imports
    Main
    HOL.Zorn
    Ordered_Resolution_Prover.Clausal_Logic
begin


(* A few notes:
 *
 * - There is an AFP entry named "FOL-Fitting", which models the full First-Order logic along with
 *   substitutions and a small natural deduction calculus.
 *   Unfortunately, this will not work for our purpose, as it uses lists internally, while we make
 *   use of (possibly) infinite sets.
 * - We could have used the AFP entry "First-order terms" instead of re-defining terms.
 *   However, we do not really need all the results about substitutions and unification. *)

text \<open>
  On-going formalisation of ``Le nec plus ultra du théorème de compacité'' by Pierre Cagne.

  Basically, we define a Tarski entailment, prove that it is compact, and provide a translation from
  First-Order formulas in CNF to the @{typ \<open>_ clause\<close>} type.
\<close>

no_syntax
  "_MapUpd"  :: "['a ⇀ 'b, maplets] ⇒ 'a ⇀ 'b" ("_/'(_')" [900, 0] 900)

section \<open>Preliminaries\<close>

text \<open>
  First-order terms:
  \<^item> Variables of abstract type \<open>'v\<close>;
  \<^item> Constants of abstract type \<open>'c\<close>;
  \<^item> Or function applications on terms.
\<close> 

(* Definition 1.1 *)
datatype ('c, 'v) tm =
  Var 'v
| Const 'c
| Fn 'v \<open>('c, 'v) tm list\<close>

text \<open>
  First-order formulas:
  \<^item> N-ary relation (predicate) applications on terms;
  \<^item> Negation of a formula;
  \<^item> Conjunction of two formulas;
  \<^item> Existential quantification.
\<close>

(* Definition 1.2 *)
datatype ('c, 'v) fm =
  Rel 'v \<open>('c, 'v) tm list\<close>
| Negation \<open>('c, 'v) fm\<close> (\<open>\<^bold>\<not> _\<close> [70] 70)
| Conjunction \<open>('c, 'v) fm\<close> \<open>('c, 'v) fm\<close> (infixl \<open>\<^bold>\<and>\<close> 65)
| Existential 'v \<open>('c, 'v) fm\<close> (\<open>\<^bold>\<exists> _\<^bold>. _\<close>)
| Top (\<open>\<^bold>\<top>\<close>)
| Bot (\<open>\<^bold>\<bottom>\<close>) 

fun is_atomic :: \<open>('c, 'v) fm \<Rightarrow> bool\<close> where
  \<open>is_atomic (Rel _ _) = True\<close>
| \<open>is_atomic _ = False\<close> 

syntax
  "_FOL_Forall" :: \<open>'v \<Rightarrow> ('c, 'v) fm \<Rightarrow> ('c, 'v) fm\<close> (\<open>\<^bold>\<forall> _\<^bold>. _\<close>)
  "_FOL_Disjunction" :: \<open>('c, 'v) fm \<Rightarrow> ('c, 'v) fm \<Rightarrow> ('c, 'v) fm\<close> (infixl \<open>\<^bold>\<or>\<close> 64)
  "_FOL_Implication" :: \<open>('c, 'v) fm \<Rightarrow> ('c, 'v) fm \<Rightarrow> ('c, 'v) fm\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 50)
(*  "_FOL_Equivalence" :: \<open>('c, 'v) fm \<Rightarrow> ('c, 'v) fm \<Rightarrow> ('c, 'v) fm\<close> (\<open>_ \<^bold>\<longleftrightarrow> _\<close>) *) 

translations
  "\<^bold>\<forall> x\<^bold>. \<phi>" \<rightleftharpoons> "\<^bold>\<exists> x\<^bold>. \<phi>"
  "\<phi> \<^bold>\<or> \<psi>" \<rightleftharpoons> "\<^bold>\<not> (\<^bold>\<not> \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)"
  "\<phi> \<^bold>\<longrightarrow> \<psi>" \<rightleftharpoons> "\<^bold>\<not> \<phi> \<^bold>\<or> \<psi>"
(* NOTE: not permitted because of duplicated variables on the right-hand side.
 * But it's okay. We don't really care too much about equivalence.
 * If we really did, we would define it in the @{typ fm} datatype (same applies to all other
 * notations). *)
(*  "\<phi> \<^bold>\<longleftrightarrow> \<psi>" \<rightleftharpoons> "(\<phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<longrightarrow> \<phi>)" *) 

text \<open>
  We also define the notion of free and bound variables.
  A free variable occurrence is an occurrence not appearing in the scope of any quantifier.
  For example, the first occurrence of \<open>x\<close> in the formula \<open>(x \<^bold>\<doteq> y) \<^bold>\<longleftrightarrow> (\<^bold>\<exists> x\<^bold>. x \<^bold>\<doteq> y)\<close> is free, while
  the second is bound.
\<close> 

fun FV_tm :: \<open>('f, 'v) tm \<Rightarrow> 'v set\<close> where
  \<open>FV_tm (Var v) = {v}\<close>
| \<open>FV_tm (Const _) = {}\<close>
| \<open>FV_tm (Fn _ args) = (\<Union> a \<in> set args. FV_tm a)\<close>

fun FV_fm :: \<open>('f, 'v) fm \<Rightarrow> 'v set\<close> where
  \<open>FV_fm (Rel _ args) = (\<Union> a \<in> set args. FV_tm a)\<close>
| \<open>FV_fm (\<^bold>\<not> \<phi>) = FV_fm \<phi>\<close>
| \<open>FV_fm (\<phi> \<^bold>\<and> \<psi>) = FV_fm \<phi> \<union> FV_fm \<psi>\<close>
| \<open>FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>) = FV_fm \<phi> - {x}\<close>
| \<open>FV_fm \<^bold>\<top> = {}\<close>
| \<open>FV_fm \<^bold>\<bottom> = {}\<close> 

lemma finite_FV_tm: \<open>finite (FV_tm t)\<close>
  by (induction t, auto) 

lemma finite_FV_fm: \<open>finite (FV_fm \<phi>)\<close>
  by (induction \<phi>, auto simp add: finite_FV_tm) 

subsection \<open>Structures and Models\<close> 

text \<open>
  A structure is a 4-uple containing:
  \<^item> \<open>\<cdot>\<^sub>c\<^sup>M \<in> c \<rightarrow> M\<close>  is a function mapping constants to values in \<open>M\<close>;
  \<^item> \<open>\<cdot>\<^sub>f\<^sup>M \<in> M\<^sup>n \<rightarrow> M\<close> is a function mapping function symbols to functions from \<open>M\<^sup>n\<close> to \<open>M\<close>;
  \<^item> \<open>\<cdot>\<^sub>v\<^sup>M \<in> V \<rightarrow> M\<close> is a function mapping (free) variable symbols to values of \<open>M\<close>;
  \<^item> \<open>\<cdot>\<^sub>r\<^sup>M \<in> M\<^sup>n \<rightarrow> \<bool>\<close> (which we could also write \<open>\<cdot>\<^sub>r\<^sup>M \<subseteq> M\<^sup>n\<close>) is a function (relation) mapping values
    of \<open>M\<close> to a truth value.
\<close> 

(* Definition 1.3 *)
record ('c, 'v, 'm) interp =
  interp_const :: \<open>'c \<Rightarrow> 'm\<close> (\<open>CST\<close>)
  interp_var :: \<open>'v \<Rightarrow> 'm\<close> (\<open>VAR\<close>)
  interp_fun :: \<open>'v \<Rightarrow> 'm list \<Rightarrow> 'm\<close> (\<open>FN\<close>)
  interp_rel :: \<open>'v \<Rightarrow> 'm list \<Rightarrow> bool\<close> (\<open>REL\<close>)
  
definition bind_var :: \<open>'v \<Rightarrow> 'm \<Rightarrow> ('c, 'v, 'm) interp \<Rightarrow> ('c, 'v, 'm) interp\<close> where
  \<open>bind_var x y \<M> \<equiv> \<M>\<lparr> interp_var := (\<lambda> z. if x = z then y else VAR \<M> z) \<rparr>\<close> 

syntax
  "_Bind_var" :: \<open>('c, 'v, 'm) interp \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> ('c, 'v, 'm) interp\<close> (\<open>_/'(_ \<mapsto> _')\<close> [80, 50, 50] 80)

translations
  "\<M>(x \<mapsto> v)" \<rightleftharpoons> "CONST bind_var x v \<M>"

text \<open>
  We define the notion of satisfaction inductively on formulas, and evaluation on terms.
\<close>

fun eval :: \<open>('c, 'v) tm \<Rightarrow> ('c, 'v, 'm) interp \<Rightarrow> 'm\<close> (\<open>_\<^sup>_\<close>) where
  \<open>(Var v)\<^sup>\<M> = VAR \<M> v\<close>
| \<open>(Fn f args)\<^sup>\<M> = FN \<M> f [t\<^sup>\<M>. t \<leftarrow> args]\<close> 
| \<open>(Const c)\<^sup>\<M> = CST \<M> c\<close> 

fun satisfies :: \<open>('c, 'v, 'm) interp \<Rightarrow> ('c, 'v) fm \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<close> 60) where
  \<open>\<M> \<turnstile> \<^bold>\<top> = True\<close>
| \<open>\<M> \<turnstile> \<^bold>\<bottom> = False\<close>
| \<open>\<M> \<turnstile> \<^bold>\<not> \<phi> = (\<not> \<M> \<turnstile> \<phi>)\<close>
| \<open>\<M> \<turnstile> \<phi> \<^bold>\<and> \<psi> = (\<M> \<turnstile> \<phi> \<and> \<M> \<turnstile> \<psi>)\<close>
| \<open>\<M> \<turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>) = (\<exists> y :: 'm. \<M>(x \<mapsto> y) \<turnstile> \<phi>)\<close>
| \<open>\<M> \<turnstile> Rel p args = REL \<M> p [t\<^sup>\<M>. t \<leftarrow> args]\<close> 




(* text \<open>
  Modelhood is defined as:
  \<open>C\<close> is a consequence of all the formulas in \<open>M\<close> iff if \<open>\<M>\<close> models all formulas in \<open>M\<close> then
  \<open>\<M>\<close> models \<open>C\<close>.
\<close> 

abbreviation models :: \<open>('c, 'v, 'm) interp \<Rightarrow> ('c, 'v) fm set \<Rightarrow> ('c, 'v) fm \<Rightarrow> bool\<close>
  (\<open>_, _ \<turnstile> _\<close> [80, 30, 80] 80) where
  \<open>\<M>, M \<turnstile> C \<equiv> (\<forall> D \<in> M. eval_fm \<M> D) \<longrightarrow> eval_fm \<M> C\<close> 

lemma top_always_valid: \<open>\<M>, M \<turnstile> \<^bold>\<top>\<close>
  by simp

lemma bot_models_all: \<open>\<M>, {\<^bold>\<bottom>} \<turnstile> C\<close>
  by auto 

lemma models_subsets: \<open>M \<subseteq> M' \<Longrightarrow> \<M>, M \<turnstile> C \<Longrightarrow> \<M>, M' \<turnstile> C\<close>
  by blast 

lemma \<open>\<M>, M \<turnstile> C \<longleftrightarrow> \<M>, M \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<bottom>\<close>
  by auto *) 

text \<open>
  A statement is a formula with no free variable.
\<close> 

typedef ('c, 'v) statement = \<open>{ \<phi> :: ('c, 'v) fm. FV_fm \<phi> = {} }\<close>
  morphisms fm_of of_fm 
  using FV_fm.simps(5)
  by blast

text \<open>
  A theory is simply a set of statements.
\<close> 

type_synonym ('c, 'v) th = \<open>('c, 'v) statement set\<close>    

text \<open>
  An interpretation \<open>\<M>\<close> is a model of a theory \<open>T\<close> if every statement of \<open>T\<close> is satisfied by \<open>\<M>\<close>.
\<close> 

(* Definition 1.5 *)
definition is_model_of :: \<open>('c, 'v, 'm) interp \<Rightarrow> ('c, 'v) th \<Rightarrow> bool\<close> where
  \<open>is_model_of \<M> T \<longleftrightarrow> (\<forall> \<phi> \<in> T. \<M> \<turnstile> fm_of \<phi>)\<close>

definition entails :: \<open>'m itself \<Rightarrow> ('c, 'v) th \<Rightarrow> ('c, 'v) fm \<Rightarrow> bool\<close> where
  \<open>entails _ T \<phi> \<longleftrightarrow> (\<forall> \<M> :: ('c, 'v, 'm) interp. is_model_of \<M> T \<longrightarrow> \<M> \<turnstile> \<phi>)\<close>

syntax
  "_Entails" :: \<open>('c, 'v) th \<Rightarrow> 'm itself \<Rightarrow> ('c, 'v) fm \<Rightarrow> bool\<close> (\<open>_/ \<Turnstile>\<^sub>_/ _\<close> [80, 20, 80] 80)

translations
  "T \<Turnstile>\<^sub>M \<phi>" \<rightleftharpoons> "CONST entails T M \<phi>"

abbreviation sat :: \<open>'m itself \<Rightarrow> ('c, 'v) th \<Rightarrow> bool\<close> where
  \<open>sat _ T \<equiv> (\<exists> \<M> :: ('c, 'v, 'm) interp. is_model_of \<M> T)\<close>

abbreviation unsat :: \<open>'m itself \<Rightarrow> ('c, 'v) th \<Rightarrow> bool\<close> where
  \<open>unsat M T \<equiv> \<not> sat M T\<close> 

lemma unsat_equiv_no_model:
  \<open>unsat (_ :: 'm itself) T \<longleftrightarrow> (\<forall> \<M> :: ('c, 'v, 'm) interp. \<not> is_model_of \<M> T)\<close>
  by (fact not_ex) 

lemma is_model_of_mono: \<open>T' \<subseteq> T \<Longrightarrow> is_model_of \<M> T \<Longrightarrow> is_model_of \<M> T'\<close>
  by (simp add: in_mono is_model_of_def) 

(* Theorem 1.6 *)
theorem sat_compactness: \<open>sat m T \<Longrightarrow> \<forall> T' \<subseteq> T. sat m T'\<close>
  using is_model_of_mono
  by blast


section \<open>Filters and ultrafilters\<close> 

text \<open>
  We take a quick detour into set theory to define appropriate mathematical structures.
\<close>  

(* Definition 2.1 *)
locale filter =
  fixes
    F :: \<open>'a set set\<close> and
    S :: \<open>'a set\<close> 
  assumes
    S_not_empty: \<open>S \<noteq> {}\<close> and 
    F_family_of_subsets_of_S: \<open>F \<subseteq> Pow S\<close> and
    S_in_F: \<open>S \<in> F\<close> and
    empty_not_in_F: \<open>{} \<notin> F\<close> and
    closed_int: \<open>A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F\<close> and
    upwards_closed: \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> F\<close>
(* NOTE: This definition does not correspond to the one of the article.
 * In fact, the one in the article seems to be totally wrong and does not exclude the empty set
 * from being a filter of an empty set.
 * We also cannot prove the lemma 2.2 (counter example: \<open>F = {}\<close> and \<open>S = {}\<close>.
 *
 * Instead, we take the definition from the book:
 * ``Set Theory: The Third Millennium Edition, revised and expanded'' (pp 72-75) *)
begin

lemma F_not_empty: \<open>F \<noteq> {}\<close>
  using S_in_F
  by blast

text \<open>
  A filter is maximal under inclusion if there does not exists a filter strictly containing it.
\<close> 

definition maximal :: bool where
  \<open>maximal \<longleftrightarrow> (\<nexists> F'. filter F' S \<and> F \<subset> F')\<close>

end (* locale filter *)

lemma Inter_non_empty_filter_family_is_filter:
  assumes
    \<F>_family_of_filters: \<open>\<F> = { F. filter F S }\<close> and
    \<F>_non_empty: \<open>\<F> \<noteq> {}\<close>
  shows
    \<open>filter (\<Inter> \<F>) S\<close>
  unfolding filter_def 
proof (intro conjI allI impI)
  fix A B

  show \<open>\<Inter> \<F> \<subseteq> Pow S\<close>
    by (metis CollectD Inter_subset \<F>_family_of_filters \<F>_non_empty filter.F_family_of_subsets_of_S) 
  show \<open>S \<noteq> {}\<close>
    using \<F>_family_of_filters \<F>_non_empty filter.S_not_empty
    by auto
  show \<open>S \<in> \<Inter> \<F>\<close>
    using \<F>_family_of_filters filter.S_in_F
    by auto
  show \<open>{} \<notin> \<Inter> \<F>\<close>
    using \<F>_family_of_filters \<F>_non_empty filter.empty_not_in_F
    by fastforce
  show \<open>A \<in> \<Inter> \<F> \<Longrightarrow> B \<in> \<Inter> \<F> \<Longrightarrow> A \<inter> B \<in> \<Inter> \<F>\<close>
    using \<F>_family_of_filters filter.closed_int
    by fastforce
  show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> \<Inter> \<F> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> \<Inter> \<F>\<close>
    (* Slow *)
    by (smt (verit, best) CollectD FOL_Compactness.filter_def Inter_iff \<F>_family_of_filters) 
qed

lemma Union_chain_is_filter:
  assumes
    \<C>_filter_chain: \<open>subset.chain { F. filter F S } \<C>\<close> and
    \<C>_non_empty: \<open>\<C> \<noteq> {}\<close>
  shows
    \<open>filter (\<Union> \<C>) S\<close>
  unfolding filter_def
proof (intro conjI allI impI)
  fix A B

  show \<open>S \<noteq> {}\<close>
    by (metis \<C>_filter_chain \<C>_non_empty empty_Collect_eq filter.S_not_empty subset_chain_def
        subset_empty)
  show \<open>\<Union> \<C> \<subseteq> Pow S\<close>
    by (metis CollectD Sup_least \<C>_filter_chain filter.F_family_of_subsets_of_S subset_chain_def
        subset_iff)
  show \<open>S \<in> \<Union> \<C>\<close>
    by (metis CollectD Union_iff \<C>_filter_chain \<C>_non_empty filter.S_in_F subset_chain_def
        subset_empty subset_iff)
  show \<open>{} \<notin> \<Union> \<C>\<close>
    by (metis CollectD FOL_Compactness.filter_def Union_iff \<C>_filter_chain subset_chain_def
        subset_iff)
  show \<open>A \<in> \<Union> \<C> \<Longrightarrow> B \<in> \<Union> \<C> \<Longrightarrow> A \<inter> B \<in> \<Union> \<C>\<close>
    using \<C>_filter_chain \<C>_non_empty
    unfolding filter_def
    by (smt (verit, del_insts) Union_iff mem_Collect_eq subsetD subset_chain_def subset_iff)
  show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> \<Union> \<C> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> \<Union> \<C>\<close>
    using \<C>_filter_chain \<C>_non_empty
    unfolding filter_def
    by (smt (verit) Union_iff mem_Collect_eq subset_chain_def subset_iff)
qed

text \<open>
  The Finite Intersection Property (FIP):

  Every finite \<open>H = {X\<^sub>1, \<dots>, X\<^sub>n}\<close> proper subset of a family of sets \<open>\<G>\<close> has a non-empty intersection
  \<open>X\<^sub>1 \<inter> \<dots> \<inter> X\<^sub>n\<close>.
\<close> 

definition fip :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>fip \<G> \<longleftrightarrow> (\<forall> H \<subseteq> \<G>. finite H \<longrightarrow> \<Inter> H \<noteq> {})\<close>  

lemma trivial_filter: \<open>S \<noteq> {} \<Longrightarrow> filter {S} S\<close>
  unfolding filter_def
  by simp 

lemma Inter_finite_subset_in_filter_if: \<open>filter F S \<Longrightarrow> H \<noteq> {} \<Longrightarrow> H \<subseteq> F \<Longrightarrow> finite H \<Longrightarrow> \<Inter> H \<in> F\<close>
proof -
  assume
    F_filter: \<open>filter F S\<close> and
    H_subset: \<open>H \<subseteq> F\<close> and
    H_finite: \<open>finite H\<close> and
    H_not_empty: \<open>H \<noteq> {}\<close> 

  show \<open>\<Inter> H \<in> F\<close>
    using H_subset
  proof (induction rule: finite_ne_induct[OF H_finite H_not_empty]) 
    case insert: (2 x H')

    have \<open>x \<in> F\<close>
      using insert(5)
      by simp
    moreover have \<open>\<Inter> H' \<in> F\<close>
      using insert(4, 5)
      by auto
    ultimately show ?case
      using filter.closed_int[OF F_filter] 
      by simp 
  qed auto 
qed

lemma filter_has_fip: \<open>filter F S \<Longrightarrow> fip F\<close>
  unfolding fip_def
proof (intro allI impI)
  fix H

  assume
    F_filter: \<open>filter F S\<close> and
    H_subset_F: \<open>H \<subseteq> F\<close> and
    finite_H: \<open>finite H\<close>

  have \<open>\<forall> A \<in> H. \<forall> B \<in> H. A \<inter> B \<in> F\<close>
    using filter.closed_int[OF F_filter] H_subset_F
    by blast 

  have \<open>\<Inter> H \<in> F\<close>
    if \<open>H \<noteq> {}\<close>
    by (rule Inter_finite_subset_in_filter_if[OF F_filter that H_subset_F finite_H])
  then show \<open>\<Inter> H \<noteq> {}\<close>
    by (cases \<open>H = {}\<close>, auto simp add: filter.empty_not_in_F[OF F_filter]) 
qed

(* Lemma 2.3 *)
lemma fip_to_filter:
  assumes
    S_not_empty: \<open>S \<noteq> {}\<close> and 
    G_subset_\<P>_S: \<open>G \<subseteq> Pow S\<close> and
    fip_G: \<open>fip G\<close>
  obtains F where
    \<open>filter F S\<close> and
    \<open>G \<subseteq> F\<close>
proof (cases \<open>G = {}\<close>) 
  case True

  have \<open>filter {S} S\<close>
    using trivial_filter[OF S_not_empty]
    by blast 
  then show ?thesis
    using True that
    by blast
next
  case False
  
  define F where
    \<open>F \<equiv> { X. X \<subseteq> S \<and> (\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> X) }\<close>

  have \<open>filter F S\<close>
    unfolding filter_def
  proof (intro conjI allI impI)
    fix A B

    show \<open>S \<noteq> {}\<close>
      by (fact S_not_empty)
    show \<open>F \<subseteq> Pow S\<close>
      unfolding F_def
      by blast 
    show \<open>S \<in> F\<close>
    proof -
      have \<open>\<forall> A \<in> G. A \<subseteq> S\<close>
        using G_subset_\<P>_S
        by fast 
      then have \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> S\<close>
        using False
        by blast
      then show ?thesis
        unfolding F_def
        by blast
    qed
    show \<open>{} \<notin> F\<close> 
    proof (rule ccontr)
      assume \<open>\<not> {} \<notin> F\<close>
      then have \<open>{} \<in> F\<close>
        by blast
      then obtain H where
        \<open>H \<subseteq> G\<close> and
        \<open>finite H\<close> and
        \<open>\<Inter> H \<subseteq> {}\<close>
        unfolding F_def
        by blast
      then show \<open>False\<close>
        using fip_G
        unfolding fip_def
        by blast 
    qed
    show \<open>A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F\<close>
    proof -
      assume
        A_in_F: \<open>A \<in> F\<close> and
        B_in_F: \<open>B \<in> F\<close>
      then have A_subset_S: \<open>A \<subseteq> S\<close> and B_subset_S: \<open>B \<subseteq> S\<close>
        unfolding F_def
        by blast+ 

      obtain H\<^sub>A H\<^sub>B where
        finite_H\<^sub>A: \<open>finite H\<^sub>A\<close> and
        H\<^sub>A_subset_G: \<open>H\<^sub>A \<subseteq> G\<close> and
        Int_H\<^sub>A_subset_A: \<open>\<Inter> H\<^sub>A \<subseteq> A\<close> and
        finite_H\<^sub>B: \<open>finite H\<^sub>B\<close> and
        H\<^sub>B_subset_G: \<open>H\<^sub>B \<subseteq> G\<close> and
        Int_H\<^sub>B_subset_B: \<open>\<Inter> H\<^sub>B \<subseteq> B\<close>
        using A_in_F B_in_F
        unfolding F_def
        by auto

      have \<open>H\<^sub>A \<union> H\<^sub>B \<subseteq> G\<close>
        using H\<^sub>A_subset_G H\<^sub>B_subset_G
        by auto 
      moreover have \<open>(\<Inter> H\<^sub>A) \<inter> (\<Inter> H\<^sub>B) \<subseteq> A \<inter> B\<close>
        using Int_H\<^sub>A_subset_A Int_H\<^sub>B_subset_B 
        by auto
      then have \<open>\<Inter> (H\<^sub>A \<union> H\<^sub>B) \<subseteq> A \<inter> B\<close>
        by blast 
      moreover have \<open>finite (H\<^sub>A \<union> H\<^sub>B)\<close>
        using finite_H\<^sub>A finite_H\<^sub>B
        by blast 
      ultimately have \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> A \<inter> B\<close>
        by blast  
      moreover have \<open>A \<inter> B \<subseteq> S\<close>
        using A_subset_S B_subset_S
        by blast 
      ultimately show ?thesis
        unfolding F_def
        by simp 
    qed
    show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> F\<close>
      unfolding F_def
      by (smt (verit, best) mem_Collect_eq subset_trans) 
  qed
  moreover have \<open>G \<subseteq> F\<close>
    unfolding F_def
  proof (intro subsetI CollectI conjI)  
    fix A x
    assume \<open>A \<in> G\<close> and \<open>x \<in> A\<close>
    then show \<open>x \<in> S\<close>
      using G_subset_\<P>_S
      by blast
  next
    fix A
    assume \<open>A \<in> G\<close>
    moreover have \<open>\<Inter> {A} = A\<close>
      by simp 
    ultimately show \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> A\<close>
      by (metis empty_subsetI finite.simps insert_subset subset_refl)
  qed
  ultimately show ?thesis
    by (rule that)
qed

text \<open>
  An ultrafilter \<open>F\<close> is a filter \<open>F\<close> for which, for all set \<open>A\<close> of the universe, either \<open>A\<close> or \<open>-A\<close>
  is in \<open>F\<close>.
\<close> 

locale ultrafilter = filter F S
  for
    F :: \<open>'a set set\<close> and
    S :: \<open>'a set\<close>
  + assumes
    maximality: \<open>A \<subseteq> S \<Longrightarrow> A \<in> F \<or> S - A \<in> F\<close> 

lemma ultrafilter_is_filter: \<open>ultrafilter F S \<Longrightarrow> filter F S\<close>
  unfolding ultrafilter_def
  by (elim conjunct1)

lemma filter_is_ultrafilter_if_maximal: \<open>filter F S \<and> filter.maximal F S \<longleftrightarrow> ultrafilter F S\<close> 
proof (intro iffI conjI; (elim conjE)?)
  assume
    F_filter: \<open>filter F S\<close> and 
    F_maximal: \<open>filter.maximal F S\<close>

  have S_not_empty: \<open>S \<noteq> {}\<close>
    by (fact filter.S_not_empty[OF F_filter]) 

  show \<open>ultrafilter F S\<close>
  proof (rule ccontr)
    assume \<open>\<not> ultrafilter F S\<close>
    then obtain Y where
      Y_subset_S: \<open>Y \<subseteq> S\<close> and
      Y_not_in_F: \<open>Y \<notin> F\<close> and
      compl_Y_not_in_F: \<open>S - Y \<notin> F\<close>
      by (meson F_filter ultrafilter.intro ultrafilter_axioms.intro) 

    have F_not_empty: \<open>F \<noteq> {}\<close>
      using F_filter filter.S_in_F
      by auto

    let ?G = \<open>F \<union> {Y}\<close>

    have \<open>fip ?G\<close>
      unfolding fip_def
    proof (intro allI impI)
      fix H
      assume
        H_subset: \<open>H \<subseteq> F \<union> {Y}\<close> and
        H_finite: \<open>finite H\<close> 

      have inter_Y_not_empty: \<open>X \<in> F \<Longrightarrow> X \<inter> Y \<noteq> {}\<close> for X
      proof (rule ccontr)
        assume
          X_in_F: \<open>X \<in> F\<close> and
          \<open>\<not> X \<inter> Y \<noteq> {}\<close>
        then have X_inter_Y_empty: \<open>X \<inter> Y = {}\<close>
          by blast
        then have \<open>X \<subseteq> S - Y\<close>
          by (metis Diff_partition Diff_subset_conv Diff_triv FOL_Compactness.filter_def F_filter
              PowD X_in_F Y_subset_S subsetD) 
        then have \<open>S - Y \<in> F\<close>
          by (smt (verit, del_insts) Diff_subset F_filter X_in_F dual_order.strict_trans1
            filter.S_in_F filter.upwards_closed nless_le)  
        then show \<open>False\<close>
          using compl_Y_not_in_F
          by contradiction
      qed

      have H_minus_Y_subset_F: \<open>H - {Y} \<subseteq> F\<close>
        using H_subset
        by auto
      moreover have finite_H_minus_Y: \<open>finite (H - {Y})\<close>
        using H_finite
        by simp 
      ultimately have Inter_H_minus_Y_not_empty: \<open>\<Inter> (H - {Y}) \<noteq> {}\<close>
        using filter_has_fip[OF F_filter, unfolded fip_def, rule_format]
        by blast 

      show \<open>\<Inter> H \<noteq> {}\<close>
      proof (cases \<open>H - {Y} = {}\<close>) 
        case True
        then show ?thesis
          by (metis Diff_empty Diff_insert0 F_not_empty Int_empty_right Inter_H_minus_Y_not_empty
              cInf_singleton equals0I insert_Diff inter_Y_not_empty) 
      next
        case False

        have \<open>\<Inter> (H - {Y}) \<in> F\<close>
          by (rule Inter_finite_subset_in_filter_if[OF F_filter False H_minus_Y_subset_F finite_H_minus_Y])
        then have \<open>Y \<inter> \<Inter> (H - {Y}) \<noteq> {}\<close>
          using inter_Y_not_empty
          by auto 
        then show ?thesis
          by auto 
      qed
    qed
    moreover have \<open>?G \<subseteq> Pow S\<close>
      using F_filter Y_subset_S filter.F_family_of_subsets_of_S
      by blast
    ultimately obtain F' where
      \<open>?G \<subseteq> F'\<close> and 
      \<open>filter F' S\<close>
      using fip_to_filter[OF S_not_empty]
      by metis 
    then have \<open>\<not> filter.maximal F S\<close>
      unfolding filter.maximal_def[OF F_filter]
      using Y_not_in_F
      by blast
    then show \<open>False\<close>
      using F_maximal
      by contradiction
  qed
next
  show \<open>ultrafilter F S \<Longrightarrow> filter F S\<close>
    by (rule ultrafilter_is_filter) 
next
  assume F_ultrafilter: \<open>ultrafilter F S\<close>

  have F_filter: \<open>filter F S\<close>
    by (rule ultrafilter_is_filter[OF F_ultrafilter])

  have ultrafilter_def': \<open>A \<in> F \<or> S - A \<in> F\<close>
    if \<open>A \<subset> S\<close> 
    for A
    using ultrafilter.maximality[OF F_ultrafilter] that
    by blast 

  show \<open>filter.maximal F S\<close>
  proof (rule ccontr)
    assume \<open>\<not> filter.maximal F S\<close>
    then obtain F' A where
      F_subset: \<open>F \<subset> F'\<close> and
      F'_filter: \<open>filter F' S\<close> and
      A_in: \<open>A \<in> F' - F\<close> 
      unfolding filter.maximal_def[OF F_filter]
      by blast
    then have \<open>S - A \<in> F\<close>
      by (metis DiffD1 DiffD2 F_filter PowD antisym_conv1 filter.F_family_of_subsets_of_S
          filter.S_in_F subsetD ultrafilter_def') 
    then show \<open>False\<close>
      by (metis A_in DiffD1 Diff_disjoint F'_filter F_subset filter.closed_int filter.empty_not_in_F
          psubsetD) 
  qed
qed

(* Lemma 2.2 *)
lemma filter_to_ultrafilter : \<open>filter F S \<Longrightarrow> \<exists> F'. F \<subseteq> F' \<and> ultrafilter F' S\<close>
proof -
  assume F_filter: \<open>filter F S\<close>

  let ?P = \<open>{ F'. filter F' S \<and> F \<subseteq> F' }\<close> 

  have P_not_empty: \<open>?P \<noteq> {}\<close>
    using F_filter
    by blast

  have \<open>\<Union> \<C> \<in> ?P\<close>
    if \<open>subset.chain ?P \<C>\<close> and \<open>\<C> \<noteq> {}\<close> 
    for \<C>
  proof -
    have \<open>filter (\<Union> \<C>) S\<close>
      by (smt (verit) Union_chain_is_filter mem_Collect_eq subset_chain_def subset_iff that(1) that(2)) 
    then show \<open>\<Union> \<C> \<in> ?P\<close>
      by (metis (no_types, lifting) CollectD CollectI Sup_bot_conv(1) Sup_upper2 filter.F_not_empty
          subsetD subset_chain_def that(1))
  qed
  then obtain U where
    U_in_P: \<open>U \<in> ?P\<close> and
    \<open>\<forall> X \<in> ?P. U \<subseteq> X \<longrightarrow> X = U\<close>
    using subset_Zorn_nonempty[OF P_not_empty]
    by force
  then have \<open>ultrafilter U S\<close>
    by (smt (verit, del_insts) dual_order.trans filter.maximal_def filter_is_ultrafilter_if_maximal
        mem_Collect_eq psubsetE)
  then show ?thesis
    using U_in_P
    by blast
qed   

section \<open>Ultraproducts\<close> 

text \<open>
  We go back to model theory. 
\<close>

(* definition eq_rel :: \<open>'i set \<Rightarrow> 'i set set \<Rightarrow> ('i \<Rightarrow> 'm) \<Rightarrow> ('i \<Rightarrow> 'm) \<Rightarrow> bool\<close> where
  \<open>eq_rel I S a b \<longleftrightarrow> { i \<in> I. a i = b i } \<in> S\<close>

syntax
  "_Eq" :: \<open>('i \<Rightarrow> 'm) \<Rightarrow> 'i set \<Rightarrow> 'i set set \<Rightarrow> ('i \<Rightarrow> 'm) \<Rightarrow> bool\<close> (\<open>_ \<sim>\<^bsub>_,_\<^esub> _\<close> [50, 40, 40, 50] 50)

translations
  "a \<sim>\<^bsub>I,S\<^esub> b" \<rightleftharpoons> "CONST eq_rel I S a b"

definition eq_class :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set\<close> (\<open>[_]\<^bsub>_\<^esub>\<close>) where
  \<open>[x]\<^bsub>eq\<^esub> \<equiv> { y. eq x y }\<close> 

definition quotient_set :: \<open>'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set set\<close> where
  \<open>quotient_set E eq \<equiv> { [x]\<^bsub>eq\<^esub> | x. x \<in> E }\<close> *) 



















theorem sat_compactness': \<open>sat m T \<longleftrightarrow> (\<exists> T' \<subseteq> T. sat m T')\<close>
  using sat_compactness
  sorry 
   
end (* theory *) 