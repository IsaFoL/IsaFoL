(* Title:        Applications of the Splitting Framework to other architectures
 *               (Splitting without Backtracking)
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)

theory Splitting_Without_Backtracking
  imports
    Main
    Splitting_Calculi
    Saturation_Framework_Extensions.FO_Ordered_Resolution_Prover_Revisited
begin

subsection \<open>Splitting without Backtracking\<close>

text \<open>
  In this section, we show that \<open>O\<^sub>\<bbbP>\<close>, an ordered resolution calculus with parallel selection,
  is closely related to \<open>LA\<close>, an instance of our Splitting Framework @{locale splitting_calculus}
  augmented with the following simplification rule:

  \[ \mprset{fraction={===}
     \inferrule{\<open>C \<or> D \<leftarrow> A\<close>}{\<open>C \<leftarrow> A \<union> {a}\<close> \\ \<open>D \<leftarrow> A \<union> {\<not> a}\<close>}
     \;\textsc{BinSplit} 
  \]
  Note that this simplification rule is applicable only if \<open>a \<in> asn(C)\<close> and if \<open>C \<or> D\<close> is splittable
  into \<open>C, D\<close>. 

  Throughout this section, we will show that \<open>LA\<close> and \<open>O\<^sub>\<bbbP>\<close> basically share the same notion of
  entailment, that the redundancy criterion used in \<open>O\<^sub>\<bbbP>\<close> is stronger than the one used in \<open>LA\<close>, and
  that saturation w.r.t. \<open>LA\<close> implies saturation w.r.t. \<open>O\<^sub>\<bbbP>\<close>.
\<close>
(* FIXME: there will be a slight problem with this simplification rule, in that we do not yet have
 * any way to represent the disjunction.
 * Since @{typ AF}-formulas only take a \<open>'f\<close>, and \<open>'f\<close> is fully abstract, we would probably need to
 * require the existence of a constant \<open>(\<or>\<^sub>F) :: 'f \<Rightarrow> 'f \<Rightarrow> 'f\<close> (although what properties would it
 * have?) in the locale.
 * I do not quite like this, but I don't quite see another way. *)

text \<open>
  We start by defining \<open>LA\<close> as an instance of our locale @{locale splitting_calculus}.
  Note that we do not add the simplification rule \textsc{BinSplit} yet, as it complexifies the
  proofs for lemma 81.
  See locale \<open>???\<close> for the full calculus with \textsc{BinSplit}. 

  By Theorem @{thm splitting_calculus.S_calculus_statically_complete}, we can show that \<open>LA\<close> is
  statically complete, and therefore dynamically complete.
\<close>



(* Report theorem 21 and corollary 22 *)










text \<open>
  Note that similarly to \<open>LA\<close>, \<open>O\<^sub>\<bbbP>\<close> is defined as the pair of an inference system \<open>FPInf\<close> and a
  redundancy criterion \<open>FPRed\<close> (which itself is a pair \<open>(FPRed\<^sub>I, FPRed\<^sub>F)\<close>).
  Since we will be comparing \<open>LA\<close> and \<open>O\<^sub>\<bbbP>\<close>, we will fix \<open>\<bbbP> = V\<close> (although we won't call \<open>O\<^sub>\<bbbP>\<close> \<open>O\<^sub>V\<close>
  to avoid confusion).

  Entailment for \<open>LA\<close> will be denoted as in the locale @{locale splitting_calculus} by the symbols
  \<open>\<Turnstile>\<close> and \<open>\<Turnstile>s\<close> (\<open>\<Turnstile>\<^sub>A\<^sub>F\<close> and \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> when lifted to A-formulas) and entailment for \<open>O\<^sub>\<bbbP>\<close> will be denoted
  by the symbols \<open>\<Turnstile>\<^sub>O\<close> and \<open>\<Turnstile>s\<^sub>O\<close> in order to avoid any name clash.
\<close>
(* NOTE: the AFP entry \<^url>\<open>https://www.isa-afp.org/entries/Ordered_Resolution_Prover.html\<close> uses
 * a datatype @{typ Clausal_Logic.literal} to represent positive or negative atoms.
 * 
 * In the Splitting Framework, we use a similar datatype @{typ Preliminaries_With_Zorn.sign} to
 * represent signedness. Fortunately, both are parameterized by an abstract formula type, so it
 * should be easy to connect both of them through a bijective mapping.
 *
 * The most critical part for the remainder of this file is to find how to actually extract the
 * \<closedblquote>head\<opendblquote> of a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause, i.e. extract \<open>C\<close> from \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close> (which we will need for
 * the definition of \<open>\<alpha>(\<cdot>)\<close> and for \<open>\<lfloor>\<cdot>\<rfloor>\<close>). *)
(* FIXME: I can already see a problem here:
 * \<^item> the Splitting Framework (specifically the @{locale AF_calculus}) uses the datatype @{typ AF},
 *   which is parameterized by two type variables:
 *   \<^item> \<open>'f\<close> for the formulas appearing on the left of the clause's arrow;
 *   \<^item> \<open>'v\<close> for the variables appearing on the right of the clause's arrow.
 * \<^item> the datatype @{typ clause} is parameterized by a single type variable representing the nullary
 *   predicates present in the clauses.
 *   @{typ clause}s are written \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close> in the paper, where \<open>C\<close> supposed to be some type
 *   of clause without \<open>\<bbbP>\<close>-literals (which one though?) and each \<open>L\<^sub>i\<close> is a literal (a positive
 *   or negative nullary predicate).
 *   As noted in the paper, \<open>C\<close> is only a \<open>\<Sigma>\<close>-clause, not a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause.
 *
 * This leads me to think that \<open>\<Sigma>\<^sub>\<bbbP>\<close> is actually \<^emph>\<open>not\<close> defined in @{theory Clausal_Logic} (only
 * \<open>\<Sigma>\<close>-clauses are through the datatoe @{typ clause}) and that we need to define \<open>\<Sigma>\<^sub>\<bbbP>\<close> clauses
 * ourselves.
 * This needs some more investigation, because the \<open>\<G>\<close> functions are defined on @{typ clauses}s.
 *
 *
 * 
 * UPDATE: the more I read this section of the paper (the first few paragraphs of the subsection,
 * until \textsc{BinSplit}), the more I'm starting to believe that we actually need to define
 * \<open>O\<^sub>\<bbbP>\<close> ourselves, using custom clause datatype along the lines of \<open>
     datatype ('f, 'v) \<bbbP>_clause =
       Or \<open>'f\<close> \<open>'v clause\<close> (infix \<open>\<or>\<^sub>\<bbbP>\<close> 60)
   \<close>, which defines what a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause is.
 * Hence, a \<open>\<bbbP>\<close>-clause may just be represented by the type @{typ clause}.
 * There is a catch: how do we define \<open>O\<^sub>\<bbbP>\<close> from \<open>O = (FInf, FRed)\<close>?
 * Moreover, we need to define the parallel selection function, which selects maximal \<bbbP>-literals
 * in pure \<open>\<bbbP>\<close>-clauses and falls back to the original selection function.
 * I guess what \<closedblquote>pure\<opendblquote> means in this context is that \<open>C = \<bottom>\<close> in a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close>?
 *
 * Also note that we need that all \<open>\<bbbP>\<close>-literals be smaller than all \<open>\<Sigma>\<close>-literals.
 * This is required for the proof of lemma 80.
 *
 *
 *
 * For all the properties on \<open>O\<^sub>\<bbbP>\<close>, I guess we will need to instantiate (or extend) the locale
 * @{locale FO_resolution_prover}:
 * \<^item> \<open>S\<close> is the selection function;
 * \<^item> \<open>subst_atm\<close> is the application of a substitution to an atom;
 * \<^item> \<open>subst_id\<close> is the empty substitution;
 * \<^item> \<open>comp_subst\<close> is the substitution composition operator;
 * \<^item> \<open>renamings_apart\<close> ?;
 * \<^item> \<open>atm_of_atms\<close> ?;
 * \<^item> \<open>mgu\<close> is a function finding the most general unifier between atoms;
 * \<^item> \<open>less_atm\<close> is a strict partial ordering on atoms.
 *
 * If we are extending this locale, then we can use \<open>S\<close> as the \<closedblquote>original selection function\<closedblquote>
 * (although we have to provide a correct mapping from \<open>\<bbbP>\<close>-clauses to clauses), and extend \<open>less_atm\<close>
 * so that all \<open>'v\<close> atoms are smaller than any \<open>'f\<close> (\<open>\<Sigma>\<close>-)clause.
 *
 * Do we also need to lift the \<closedblquote>\<open>\<G>\<close> functions\<opendblquote> to \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses? The paper says that they are defined
 * on \<open>\<Sigma>\<close> clauses, but later in lemmas 80 and 81, they are used on \<open>\<Sigma>\<^sub>\<bbbP>\<close> clauses. *)









text \<open>
  We also define the bijective mapping \<alpha>(\<cdot>), symbolising the natural correspondence between
  A-clauses and \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses.
  Formally, \<open>\<alpha>(C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n) \<equiv> C \<leftarrow> {\<not>L\<^sub>1, \<dots>, \<not>L\<^sub>n}\<close>.
  We also prove that it is indeed bijective:
  \<^item> \<open>\<alpha>(\<cdot>)\<close> is \<^emph>\<open>injective\<close>, meaning \<open>\<alpha>(D\<^sub>1) = \<alpha>(D\<^sub>2)\<close> implies \<open>D\<^sub>1 = D\<^sub>2\<close>;
  \<^item> \<open>\<alpha>(\<cdot>)\<close> is \<^emph>\<open>surjective\<close>, meaning that for all \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause \<open>C\<close> there exists an A-clause \<open>D\<close> such
    that \<open>\<alpha>(D) = C\<close>;
  \<^item> \<open>\<alpha>(\<cdot>)\<close> maps its entire domain to \<open>\<Sigma>\<^sub>\<bbbP>\<close> clauses.
    This property is true of all total functions.

  We also define \<open>\<iota>\<alpha>(\<cdot>)\<close> on inferences such that \<open>\<iota>\<alpha>((C\<^sub>n, \<dots>, C\<^sub>1, C\<^sub>0)) \<equiv> (\<alpha>(C\<^sub>n), \<dots>, \<alpha>(C\<^sub>1), \<alpha>(C\<^sub>0))\<close>.
  As usual, we also implicitly lift \<open>\<alpha>(\<cdot>)\<close> to sets.
\<close>
(* NOTE: to prove the bijectivity of \<open>\<alpha>(\<cdot>)\<close> we can use the predicates @{const inj}, @{const surj}
 * and @{const bij} from the theory @{theory Fun}.
 * @{term \<open>bij \<alpha>\<close>} should basically follow from @{term \<open>inj \<alpha>\<close>} and @{term \<open>surj \<alpha>\<close>}. *)



text \<open>
  We also define a version of @{const F_of} on \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, as
  \<open>\<lfloor>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<rfloor> = \<lfloor>C \<leftarrow> {\<not>L\<^sub>1, \<dots>, \<not>L\<^sub>n}\<rfloor> = C\<close>. 
\<close>

(* NOTE: The \<open>\<G>\<close> functions mentioned in the article are defined in the AFP entry
 * \<^url>\<open>https://www.isa-afp.org/theories/saturation_framework_extensions/#FO_Ordered_Resolution_Prover_Revisited.html#offset_5058..5061\<close>
 * (* Sorry for the 100 characters restriction, I can't shorten nor linebreak the link\<dots> :( *)
 *
 * The function of interest are @{const \<G>_F}, @{const \<G>_Fset} and @{const \<G>_I}.
 *)










text \<open>
  Lemma 78 proves that both entailments \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> and \<open>\<Turnstile>\<^sub>O\<close> are equivalent up to \<alpha>-correspondence. 
\<close>
(* Report lemma 78 *)










text \<open>
  Lemma 79 states that if we have some \<open>\<alpha>(\<iota>)\<close> which is a \textsc{Base} inference, and that \<open>\<iota>\<close> only
  contains \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, then \<open>\<iota>\<close> is actually an inference in \<open>FPInf\<close>. 
\<close>
(* Report lemma 79 *)

(* I think that this proof may not be as simple as described in the paper, but I'll see.
 *
 * Specifically, the fact that all \<open>C\<^sub>i\<close> (for \<open>i \<in> {1 ,\<dots>, n}\<close>) are not \<open>\<bottom>\<close> is blurry.
 * Same goes for using the selection function with selected literals: how do we know that the
 * function will select those exactly? . *)











text \<open>
  Lemma 80 is used to prove that the redundancy criterion in \<open>O\<^sub>\<bbbP>\<close> is stronger than the redundancy
  criterion used in \<open>LA\<close>.
  In other words, this means that the set of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses \<open>C\<close> such that \<open>\<alpha>(C)\<close> is redundant according
  to \<open>SRed\<^sub>F(\<alpha>(N))\<close> is included within the set of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses which are redundant according to
  \<open>FPRed\<^sub>F(N)\<close>.
  The same also holds for \<open>SRed\<^sub>I(\<alpha>(N))\<close> and \<open>FPRed\<^sub>I(N)\<close>. 
\<close>
(* NOTE: We can write those lemmas in two equivalent ways (in fact, the second is what needs to be
 * proven when applying \<open>intro subsetI\<close> to the first):
 * \<^item> \<open>{ C. \<alpha>(C) \<in> SRed\<^sub>F(\<alpha>(N)) } \<subseteq> { C \<in> FPRed\<^sub>F(N) }\<close>
 * \<^item> \<open>\<forall> C. \<alpha>(C) \<in> SRed\<^sub>F(\<alpha>(N)) \<longrightarrow> C \<in> FPRed\<^sub>F(N)\<close>
 * The same goes for \<open>SRed\<^sub>I\<close> and \<open>FPRed\<^sub>I\<close>:
 * \<^item> \<open>{ \<iota>. \<iota>\<alpha>(\<iota>) \<in> SRed\<^sub>I(\<alpha>(N)) } \<subseteq> { \<iota> \<in> FPRed\<^sub>I(N) }\<close>
 * \<^item> \<open>\<forall> \<iota>. \<iota>\<alpha>(\<iota>) \<in> SRed\<^sub>I(\<alpha>(N)) \<longrightarrow> \<iota> \<in> FPRed\<^sub>I(N)\<close>
 *
 * The second one is closer to what is proposed in the paper, so I think I'll go with that. *)
(* Report lemma 80 *)










text \<open>
  Lemma 81 shows that the notion of saturation is stronger in \<open>LA\<close>.
  If \<open>N\<close> is saturated w.r.t. \<open>O\<^sub>\<bbbP>\<close>, then \<open>\<alpha>(N)\<close> is saturated w.r.t. \<open>LA\<close>. 
\<close>
(* Report lemma 81 only for SInf (without BinSplit) *)
























text \<open>
  We now augment the earlier calculus \<open>LA\<close> with the simplification rule \textsc{BinSplit}
  (which we show to be sound and to make its premises redundant,
  Theorem @{thm splitting_calculus_with_simps.SInf_with_simps_sound_wrt_entails_sound}
  and Theorem @{thm splitting_calculus_with_simps.simplification_to_redundant} respectively).
\<close> 



text \<open>
  The definition of simplification rules follows what we have been doing in
  @{locale splitting_calculus_with_simps}, i.e. $X\_simp$ indicates the simplification rule itself,
  while $X\_pre$ contains the precondition which must hold for the simplification rule to be
  applicable.
\<close> 




(* Report theorem 14 for the case BinSplit *)





(* Report theorem 19 for the case BinSplit *) 





(* Report lemma 81 for the full calculus with BinSplit *)







end (* theory Splitting_Without_Backtracking *)