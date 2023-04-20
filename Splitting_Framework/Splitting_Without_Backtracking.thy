(* Title:        Applications of the Splitting Framework to other architectures
 *               (Splitting without Backtracking)
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)

theory Splitting_Without_Backtracking
  imports
    Main
    Splitting_Calculi
begin

subsection \<open>Splitting without Backtracking\<close>

text \<open>
  In this section, we show that \<open>O\<^sub>\<bbbP>\<close>, an ordered resolution with parallel selection, is closely
  related to \<open>LA\<close>, an instance of our Splitting Framework @{locale splitting_calculus}
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
  We start by defining \<open>LA\<close> as an instance of our locale @{locale splitting_calculus} that we augment
  with the simplification rule \textsc{BinSplit} (which we show to be sound and to make its premises
  redundant, Theorem @{thm splitting_calculus_with_simps.SInf_with_simps_sound_wrt_entails_sound}
  and Theorem @{thm splitting_calculus_with_simps.simplification_to_redundant} respectively).

  By Theorem @{thm splitting_calculus.S_calculus_statically_complete}, we can show that \<open>LA\<close> is
  statically complete.
\<close>

text \<open>
  The definition of simplification rules follows what we have been doing in
  @{locale splitting_calculus_with_simps}, i.e. $X\_simp$ indicates the simplification rule itself,
  while $X\_pre$ contains the precondition which must hold for the simplification rule to be
  applicable.
\<close> 




(* Report theorem 14 for the case BinSplit *)





(* Report theorem 19 for the case BinSplit *) 












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
 * This needs some more investigation, because the \<open>\<G>\<close> functions are defined on @{typ clauses}s. *)









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



text \<open>
  We also define a version of @{const F_of} on \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, as
  \<open>\<lfloor>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<rfloor> = \<lfloor>C \<leftarrow> {\<not>L\<^sub>1, \<dots>, \<not>L\<^sub>n}\<rfloor> = C\<close>. 
\<close>

(* NOTE: The \<open>\<G>\<close> functions mentioned in the article are defined in the AFP entry
 * \<^url>\<open>https://www.isa-afp.org/theories/saturation_framework_extensions/#FO_Ordered_Resolution_Prover_Revisited.html#offset_5058..5061\<close>
 * (* Sorry for the 100 characters restriction, I can't shorten nor linebreak the link\<dots> :( *)
 *
 * The function of interest are \<open>\<G>_F\<close>, \<open>\<G>_Fset\<close> and \<open>\<G>_I\<close>.
 *)










text \<open>
  Lemma 78 proves that both entailments \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> and \<open>\<Turnstile>\<^sub>O\<close> are equivalent up to \<alpha>-correspondence. 
\<close>
(* Report lemma 78 *)










text \<open>
  Lemma 79 states that if we have some \<open>\<alpha>(\<iota>)\<close> which is a \textsc{Base} inference, and that \<open>\<iota>\<close> only
  contains \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, then \<open>\<iota>\<close> is actually an inference in \<open>FPInf\<close>. 
\<close>
(* I think that this proof may not be as simple as described in the paper, but I'll see. *)
(* Report lemma 79 *)












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
(* Report lemma 81 *)






























(*************************************************************)
(*************************************************************)
(*************************************************************)
(* Please, do not read anything past this line. This is an ugly mess but I'm keeping it
 * only to check if I forgot anything up there. *)

text \<open>
  Currently, these will be only notes that I take while reading the section of the paper.
  I will later reformulate most of them (if not delete half of them).



  Basically, instead of using the \textsc{Split} simplification rule introduced in section 3
  (see the locale @{locale Splitting_Calculi.splitting_calculus_with_simps}), we will be using the
  following splitting simplification rule:

  \[ \mprset{fraction={===}}
     \inferrule{C \vee D \leftarrow A}
               {C \leftarrow A \union \{ p \} \\ D \leftarrow A \union \{ \neg p \}}
     \;\textsc{BinSplit}
  \]

  \<^noindent>{\centering\rule{.5\paperwidth}{0.4pt}}

  We then define the \<open>LA\<close> calculus (which stands for \<closedblquote>Lightweight AVATAR\<opendblquote>):
  Let \<open>O\<close> be \<open>(FInf, FRed)\<close> together with both \<closedblquote>normal\<opendblquote> and sound entailments.
  \<open>LA\<close> is obtained by instantiating our locale @{locale splitting_calculus} (or
  @{locale splitting_calculus_extensions} or @{locale splitting_calculus_with_simps})
  and by adding the simplification rule above, with preconditions \<open>p \<in> asn(C)\<close> and
  \<open>C \<or> D\<close> is splittable into \<open>C\<close> and \<open>D\<close>.

  (* NOTE: quick problem: we require a disjunction over \<open>'f\<close> formulas, which we don't have since
   * \<open>'f\<close> is abstract. We could add a disjunction symbol \<open>(\<or>\<^sub>F) :: 'f \<Rightarrow> 'f \<Rightarrow> 'f\<close> to the locale.
   *
   * Another possibility would be to fully instantiate \<open>'f\<close> with a datatype representing F-formulas,
   * although I don't think that this is a good idea if we don't need it at all.
   *
   * I don't know about any other good possibility though. We'll see with Sophie, I guess. *)

  (* NOTE: We are relating \<open>LA\<close> and \<open>O\<^sub>\<bbbP>\<close>, but where is \<open>O\<^sub>\<bbbP>\<close> defined?
   * Should we define it ourselves?
   * In this case, we'll need to go over [25] and do all the work\<dots>which may actually take some
   * time.
   *
   * NOTE: see the formalization of Bachmair and Ganzinger ordered resolution \<open>O\<close> on the AFP:
   * \<^url>\<open>https://www.isa-afp.org/entries/Ordered_Resolution_Prover.html\<close> and also maybe
   * \<^url>\<open>https://www.isa-afp.org/entries/Saturation_Framework_Extensions.html\<close>. These may contain
   * what we actually want here? *)

  We then define a function \<open>\<alpha>(\<cdot>)\<close> which transforms a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause into an A-clause.
  Formally, \<open>\<alpha>(C \<or> L_1 \<or> \<dots> \<or> L_n) \<equiv> C \<leftarrow> {\<not>L_1, \<dots>, \<not>L_n}\<close>.

  We also overload \<open>\<lfloor>\<cdot>\<rfloor>\<close> on \<open>\<Sigma>\<^sub>\<bbbP>\<close> so that \<open>\<lfloor>C \<or> L_1 \<or> \<dots> \<or> L_n\<rfloor> = \<lfloor>C \<leftarrow> {\<not>L_1, \<dots>, \<not>L_n}\<rfloor> = C\<close>.
  And also have \<open>\<G>\<close> denote the grounding function.

  (* NOTE: should we define \<open>\<G>\<close> or should it be abstract (as a parameter to a new locale)? *)
\<close>



text \<open>
  Let \<open>M\<close> and \<open>N\<close> be sets of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses.
  \<open>M\<close> entails \<open>N\<close> iff \<open>\<alpha>(M)\<close> entails \<open>\<alpha>(N)\<close>.

  In this lemma, we show that the entailments on \<open>\<Sigma>\<^sub>\<bbbP>\<close> clauses is equivalent
  up to \<alpha>-equivalence. 
\<close>
(* Report lemma 78 *)




text \<open>
  This lemma allows us to lift a \textsc{Base} inference \<open>\<alpha>(\<iota>)\<close> to a FP-inference \<open>\<iota>\<close>
  (if, obviously, \<open>\<iota>\<close> is comprised only of \<open>\<Sigma>\<^sub>\<bbbP>\<close> clauses).
\<close>
(* Report lemma 79 *) 




text \<open>
  Lemma 80 is comprised of two parts:
  \<^enum> The first part is used to show that redundancy of formulas is lifted up to \<alpha>-equivalence.
    If \<open>\<alpha>(C) \<in> SRed\<^sub>F(\<alpha>(N))\<close> then \<open>C \<in> FPRed\<^sub>F(N)\<close>.
  \<^enum> The second part shows that redundancy of inferences is also lifted up to \<alpha>-equivalence.
    If \<open>\<alpha>(\<iota>) \<in> SRed\<^sub>I(\<alpha>(N))\<close> then \<open>\<iota>  \<in> FPRed\<^sub>I(N)\<close>.
\<close>
(* Report lemma 80 (1/2) *)

(* Report lemma 80 (2/2) *)





text \<open>
  Lemma 81 shows that saturation can be lifted up to \<alpha>-equivalence.
  Basically, if \<open>N\<close> is saturated w.r.t \<open>O\<^sub>\<bbbP>\<close> then \<open>\<alpha>(N)\<close> is saturated w.r.t \<open>LA\<close>. 
\<close> 
(* Report lemma 81 *) 

end 