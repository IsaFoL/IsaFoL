(* Authors: Stefan Berghofer, TU Muenchen, 2003 / Andreas Halkjær From, DTU Compute, 2017
*)

theory FOL_Berghofer
imports Main
begin


section {* Miscellaneous Utilities *}

text {*
Rules for manipulating goals where both the premises and the conclusion
contain conjunctions of similar structure.
*}

theorem conjE'': "(\<forall>x. P x \<longrightarrow> Q x \<and> R x) \<Longrightarrow>
  ((\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> Q') \<Longrightarrow> ((\<forall>x. P x \<longrightarrow> R x) \<Longrightarrow> R') \<Longrightarrow> Q' \<and> R'"
  by iprover

text {* Some facts about (in)finite sets *}

theorem set_inter_compl_diff [simp]: "- A \<inter> B = B - A" by blast

section {* Terms and formulae *}

text {*
\label{sec:terms}
The datatypes of terms and formulae in {\em de Bruijn notation}
are defined as follows:
*}
  
datatype 'a "term" =
    Var nat
  | App 'a "'a term list"

datatype ('a, 'b) form =
    FF
  | TT
  | Pred 'b "'a term list"
  | And "('a, 'b) form" "('a, 'b) form"
  | Or "('a, 'b) form" "('a, 'b) form"
  | Impl "('a, 'b) form" "('a, 'b) form"
  | Neg "('a, 'b) form"
  | Forall "('a, 'b) form"
  | Exists "('a, 'b) form"

text {*
We use @{text "'a"} and @{text "'b"} to denote the type of
{\em function symbols} and {\em predicate symbols}, respectively.
In applications @{text "App a ts"} and predicates
@{text "Pred a ts"}, the length of @{text "ts"} is considered
to be a part of the function or predicate name, so @{text "App a [t]"}
and @{text "App a [t,u]"} refer to different functions.

The size of a formula is used later for wellfounded induction. The
default implementation provided by the datatype package is not quite
what we need, so here is an alternative version:
*}

primrec size_form :: "('a, 'b) form \<Rightarrow> nat" where
  "size_form FF = 0"
| "size_form TT = 0"
| "size_form (Pred _ _) = 0"
| "size_form (And phi psi) = size_form phi + size_form psi + 1"
| "size_form (Or phi psi) = size_form phi + size_form psi + 1"
| "size_form (Impl phi psi) = size_form phi + size_form psi + 1"
| "size_form (Neg phi) = size_form phi + 1"
| "size_form (Forall phi) = size_form phi + 1"
| "size_form (Exists phi) = size_form phi + 1"


subsection {* Closed terms and formulae *}

text {*
Many of the results proved in the following sections are restricted
to closed terms and formulae. We call a term or formula {\em closed at
level @{text i}}, if it only contains ``loose'' bound variables with
indices smaller than @{text i}.
*}

primrec
  closedt :: "nat \<Rightarrow> 'a term \<Rightarrow> bool"
  and closedts :: "nat \<Rightarrow> 'a term list \<Rightarrow> bool"
where
  "closedt m (Var n) = (n < m)"
| "closedt m (App a ts) = closedts m ts"
| "closedts m [] = True"
| "closedts m (t # ts) = (closedt m t \<and> closedts m ts)"

primrec
  closed :: "nat \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"
where
  "closed m FF = True"
| "closed m TT = True"
| "closed m (Pred b ts) = closedts m ts"
| "closed m (And p q) = (closed m p \<and> closed m q)"
| "closed m (Or p q) = (closed m p \<and> closed m q)"
| "closed m (Impl p q) = (closed m p \<and> closed m q)"
| "closed m (Neg p) = closed m p"
| "closed m (Forall p) = closed (Suc m) p"
| "closed m (Exists p) = closed (Suc m) p"

theorem closedt_mono: assumes le: "i \<le> j"
  shows "closedt i (t::'a term) \<Longrightarrow> closedt j t"
  and "closedts i (ts::'a term list) \<Longrightarrow> closedts j ts" using le
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all


subsection {* Substitution *}

text {*
We now define substitution functions for terms and formulae. When performing
substitutions under quantifiers, we need to {\em lift} the terms to be substituted
for variables, in order for the ``loose'' bound variables to point to the right
position.
*}

primrec
  substt :: "'a term \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term" ("_[_'/_]" [300, 0, 0] 300)
  and substts :: "'a term list \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term list" ("_[_'/_]" [300, 0, 0] 300)
where
  "(Var i)[s/k] = (if k < i then Var (i - 1) else if i = k then s else Var i)"
| "(App a ts)[s/k] = App a (ts[s/k])"
| "[][s/k] = []"
| "(t # ts)[s/k] = t[s/k] # ts[s/k]"

primrec
  liftt :: "'a term \<Rightarrow> 'a term"
  and liftts :: "'a term list \<Rightarrow> 'a term list"
where
  "liftt (Var i) = Var (Suc i)"
| "liftt (App a ts) = App a (liftts ts)"
| "liftts [] = []"
| "liftts (t # ts) = liftt t # liftts ts"

primrec
  subst :: "('a, 'b) form \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> ('a, 'b) form" ("_[_'/_]" [300, 0, 0] 300)
where
  "FF[s/k] = FF"
| "TT[s/k] = TT"
| "(Pred b ts)[s/k] = Pred b (ts[s/k])"
| "(And p q)[s/k] = And (p[s/k]) (q[s/k])"
| "(Or p q)[s/k] = Or (p[s/k]) (q[s/k])"
| "(Impl p q)[s/k] = Impl (p[s/k]) (q[s/k])"
| "(Neg p)[s/k] = Neg (p[s/k])"
| "(Forall p)[s/k] = Forall (p[liftt s/Suc k])"
| "(Exists p)[s/k] = Exists (p[liftt s/Suc k])"

theorem lift_closed [simp]:
  "closedt 0 (t::'a term) \<Longrightarrow> closedt 0 (liftt t)"
  "closedts 0 (ts::'a term list) \<Longrightarrow> closedts 0 (liftts ts)"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem subst_closedt [simp]:
  assumes u: "closedt 0 u"
  shows "closedt (Suc i) t \<Longrightarrow> closedt i (t[u/i])"
  and "closedts (Suc i) ts \<Longrightarrow> closedts i (ts[u/i])"
  using u closedt_mono(1)
  by (induct t and ts rule: closedt.induct closedts.induct) auto

theorem subst_closed [simp]:
  "closedt 0 t \<Longrightarrow> closed (Suc i) p \<Longrightarrow> closed i (p[t/i])"
  by (induct p arbitrary: i t) simp_all

theorem subst_size_form [simp]: "size_form (subst p t i) = size_form p"
  by (induct p arbitrary: i t) simp_all
  

subsection {* Parameters *}

text {*
The introduction rule @{text ForallI} for the universal quantifier,
as well as the elimination rule @{text ExistsE} for the existential
quantifier introduced in \secref{sec:proof-calculus} require the
quantified variable to be replaced by a ``fresh'' parameter. Fitting's
solution is to use a new nullary function symbol for this purpose.
To express that a function symbol is ``fresh'', we introduce functions
for collecting all function symbols occurring in a term or formula.
*}

primrec
  paramst  :: "'a term \<Rightarrow> 'a set"
  and paramsts :: "'a term list \<Rightarrow> 'a set"
where
  "paramst (Var n) = {}"
| "paramst (App a ts) = {a} \<union> paramsts ts"
| "paramsts [] = {}"
| "paramsts (t # ts) = (paramst t \<union> paramsts ts)"

primrec
  params :: "('a, 'b) form \<Rightarrow> 'a set"
where
  "params FF = {}"
| "params TT = {}"
| "params (Pred b ts) = paramsts ts"
| "params (And p q) = params p \<union> params q"
| "params (Or p q) = params p \<union> params q"
| "params (Impl p q) = params p \<union> params q"
| "params (Neg p) = params p"
| "params (Forall p) = params p"
| "params (Exists p) = params p"

text{*
We also define parameter substitution functions on terms and formulae
that apply a function @{text f} to all function symbols.
*}

primrec
  psubstt :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c term"
  and psubstts :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c term list"
where
  "psubstt f (Var i) = Var i"
| "psubstt f (App x ts) = App (f x) (psubstts f ts)"
| "psubstts f [] = []"
| "psubstts f (t # ts) = psubstt f t # psubstts f ts"

primrec
  psubst :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) form \<Rightarrow> ('c, 'b) form"
where
  "psubst f FF = FF"
| "psubst f TT = TT"
| "psubst f (Pred b ts) = Pred b (psubstts f ts)"
| "psubst f (And p q) = And (psubst f p) (psubst f q)"
| "psubst f (Or p q) = Or (psubst f p) (psubst f q)"
| "psubst f (Impl p q) = Impl (psubst f p) (psubst f q)"
| "psubst f (Neg p) = Neg (psubst f p)"
| "psubst f (Forall p) = Forall (psubst f p)"
| "psubst f (Exists p) = Exists (psubst f p)"

theorem psubstt_closed [simp]:
  "closedt i (psubstt f t) = closedt i t"
  "closedts i (psubstts f ts) = closedts i ts"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem psubst_closed [simp]:
  "closed i (psubst f p) = closed i p"
  by (induct p arbitrary: i) simp_all

theorem psubstt_subst [simp]:
  "psubstt f (substt t u i) = substt (psubstt f t) (psubstt f u) i"
  "psubstts f (substts ts u i) = substts (psubstts f ts) (psubstt f u) i"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubstt_lift [simp]:
  "psubstt f (liftt t) = liftt (psubstt f t)"
  "psubstts f (liftts ts) = liftts (psubstts f ts)"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_subst [simp]:
  "psubst f (subst P t i) = subst (psubst f P) (psubstt f t) i"
  by (induct P arbitrary: i t) simp_all

theorem psubstt_upd [simp]:
  "x \<notin> paramst (t::'a term) \<Longrightarrow> psubstt (f(x:=y)) t = psubstt f t"
  "x \<notin> paramsts (ts::'a term list) \<Longrightarrow> psubstts (f(x:=y)) ts = psubstts f ts"
  by (induct t and ts rule: psubstt.induct psubstts.induct) (auto split: sum.split)

theorem psubst_upd [simp]: "x \<notin> params P \<Longrightarrow> psubst (f(x:=y)) P = psubst f P"
  by (induct P) (simp_all del: fun_upd_apply)
  
theorem psubstt_id:
  fixes t :: "'a term" and ts :: "'a term list"
  shows "psubstt id t = t" and "psubstts (\<lambda>x. x) ts = ts"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all
    
theorem psubst_id [simp]: "psubst id = id"
proof
  fix p :: "('a, 'b) form"
  show "psubst id p = id p"
    by (induct p) (simp_all add: psubstt_id)
qed

theorem psubstt_image [simp]:
  "paramst (psubstt f t) = f ` paramst t"
  "paramsts (psubstts f ts) = f ` paramsts ts"
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all add: image_Un)

theorem psubst_image [simp]: "params (psubst f p) = f ` params p"
  by (induct p) (simp_all add: image_Un)


section {* Semantics *}

text {*
\label{sec:semantics}
In this section, we define evaluation functions for terms and formulae.
Evaluation is performed relative to an environment mapping indices of variables
to values. We also introduce a function, denoted by @{text "e\<langle>i:a\<rangle>"}, for inserting
a value @{text a} at position @{text i} into the environment. All values of variables
with indices less than @{text i} are left untouched by this operation, whereas the
values of variables with indices greater or equal than @{text i} are shifted one
position up.
*}

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)  where
  "e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
proof
  fix x
  show "(e\<langle>i:U\<rangle>\<langle>0:T\<rangle>) x = (e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>) x"
    by (cases x) (simp_all add: shift_def)
qed
  
primrec
  evalt :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c"
  and evalts :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c list"
where
  "evalt e f (Var n) = e n"
| "evalt e f (App a ts) = f a (evalts e f ts)"
| "evalts e f [] = []"
| "evalts e f (t # ts) = evalt e f t # evalts e f ts"

primrec
  eval :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"
where
  "eval e f g FF = False"
| "eval e f g TT = True"
| "eval e f g (Pred a ts) = g a (evalts e f ts)"
| "eval e f g (And p q) = ((eval e f g p) \<and> (eval e f g q))"
| "eval e f g (Or p q) = ((eval e f g p) \<or> (eval e f g q))"
| "eval e f g (Impl p q) = ((eval e f g p) \<longrightarrow> (eval e f g q))"
| "eval e f g (Neg p) = (\<not> (eval e f g p))"
| "eval e f g (Forall p) = (\<forall>z. eval (e\<langle>0:z\<rangle>) f g p)"
| "eval e f g (Exists p) = (\<exists>z. eval (e\<langle>0:z\<rangle>) f g p)"

text {*
We write @{text "e,f,g,ps \<Turnstile> p"} to mean that the formula @{text p} is a
semantic consequence of the list of formulae @{text ps} with respect to an
environment @{text e} and interpretations @{text f} and @{text g} for
function and predicate symbols, respectively.
*}

definition
  model :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow>
    ('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"  ("_,_,_,_ \<Turnstile> _" [50,50] 50) where
  "(e,f,g,ps \<Turnstile> p) = (list_all (eval e f g) ps \<longrightarrow> eval e f g p)"

text {*
The following substitution lemmas relate substitution and evaluation functions:
*}

theorem subst_lemma' [simp]:
  "evalt e f (substt t u i) = evalt (e\<langle>i:evalt e f u\<rangle>) f t"
  "evalts e f (substts ts u i) = evalts (e\<langle>i:evalt e f u\<rangle>) f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem lift_lemma [simp]:
  "evalt (e\<langle>0:z\<rangle>) f (liftt t) = evalt e f t"
  "evalts (e\<langle>0:z\<rangle>) f (liftts ts) = evalts e f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem subst_lemma [simp]:
  "eval e f g (subst a t i) = eval (e\<langle>i:evalt e f t\<rangle>) f g a"
  by (induct a arbitrary: e i t) simp_all

theorem upd_lemma' [simp]:
  "n \<notin> paramst t \<Longrightarrow> evalt e (f(n:=x)) t = evalt e f t"
  "n \<notin> paramsts ts \<Longrightarrow> evalts e (f(n:=x)) ts = evalts e f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) auto

theorem upd_lemma [simp]:
  "n \<notin> params p \<Longrightarrow> eval e (f(n:=x)) g p = eval e f g p"
  by (induct p arbitrary: e) simp_all

theorem list_upd_lemma [simp]: "list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
  list_all (eval e (f(n:=x)) g) G = list_all (eval e f g) G"
  by (induct G) simp_all

text {*
In order to test the evaluation function defined above, we apply it
to an example:
*}

theorem ex_all_commute_eval:
  "eval e f g (Impl (Exists (Forall (Pred p [Var 1, Var 0])))
    (Forall (Exists (Pred p [Var 0, Var 1]))))"
  apply simp
txt {*
Simplification yields the following proof state:
@{subgoals [display]}
This is easily proved using intuitionistic logic:
*}
  apply iprover
  done


section {* Proof calculus *}

text {*
\label{sec:proof-calculus}
We now introduce a natural deduction proof calculus for first order logic.
The derivability judgement @{text "G \<turnstile> a"} is defined as an inductive predicate.
*}

inductive
  deriv :: "('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool" ("_ \<turnstile> _" [50,50] 50)
where
  Assum: "a \<in> set G \<Longrightarrow> G \<turnstile> a"
| TTI: "G \<turnstile> TT"
| FFE: "G \<turnstile> FF \<Longrightarrow> G \<turnstile> a"
| NegI: "a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> Neg a"
| NegE: "G \<turnstile> Neg a \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> FF"
| Class: "Neg a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> a"
| AndI: "G \<turnstile> a \<Longrightarrow> G \<turnstile> b \<Longrightarrow> G \<turnstile> And a b"
| AndE1: "G \<turnstile> And a b \<Longrightarrow> G \<turnstile> a"
| AndE2: "G \<turnstile> And a b \<Longrightarrow> G \<turnstile> b"
| OrI1: "G \<turnstile> a \<Longrightarrow> G \<turnstile> Or a b"
| OrI2: "G \<turnstile> b \<Longrightarrow> G \<turnstile> Or a b"
| OrE: "G \<turnstile> Or a b \<Longrightarrow> a # G \<turnstile> c \<Longrightarrow> b # G \<turnstile> c \<Longrightarrow> G \<turnstile> c"
| ImplI: "a # G \<turnstile> b \<Longrightarrow> G \<turnstile> Impl a b"
| ImplE: "G \<turnstile> Impl a b \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> b"
| ForallI: "G \<turnstile> a[App n []/0] \<Longrightarrow> list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
    n \<notin> params a \<Longrightarrow> G \<turnstile> Forall a"
| ForallE: "G \<turnstile> Forall a \<Longrightarrow> G \<turnstile> a[t/0]"
| ExistsI: "G \<turnstile> a[t/0] \<Longrightarrow> G \<turnstile> Exists a"
| ExistsE: "G \<turnstile> Exists a \<Longrightarrow> a[App n []/0] # G \<turnstile> b \<Longrightarrow>
    list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow> n \<notin> params a \<Longrightarrow> n \<notin> params b \<Longrightarrow> G \<turnstile> b"

text {*
The following derived inference rules are sometimes useful in applications.
*}

theorem cut: "G \<turnstile> A \<Longrightarrow> A # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
  by (rule ImplE) (rule ImplI)

theorem cut': "A # G \<turnstile> B \<Longrightarrow> G \<turnstile> A \<Longrightarrow> G \<turnstile> B"
  by (rule ImplE) (rule ImplI)

theorem Class': "Neg A # G \<turnstile> A \<Longrightarrow> G \<turnstile> A"
proof -
  assume "Neg A # G \<turnstile> A"
  have "A # Neg A # G \<turnstile> A"
    by (simp add: Assum)
  moreover have "A # Neg A # G \<turnstile> Neg A"
    by (simp add: Assum)
  ultimately have "A # Neg A # G \<turnstile> FF"
    using NegE by blast
  then have "Neg A # G \<turnstile> FF"
    using cut' \<open>Neg A # G \<turnstile> A\<close> by blast
  then show "G \<turnstile> A"
    using Class by blast
qed

theorem ForallE': "G \<turnstile> Forall a \<Longrightarrow> subst a t 0 # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
  by (rule cut) (rule ForallE)

text {*
As an example, we show that the excluded middle, a commutation property
for existential and universal quantifiers, the drinker principle, as well
as Peirce's law are derivable in the calculus given above.
*}
  
theorem tnd: "[] \<turnstile> Or (Pred p []) (Neg (Pred p []))" (is "_ \<turnstile> ?or")
proof -
  have "[Pred p [], Neg ?or] \<turnstile> Pred p []"
    by (simp add: Assum)
  then have "[Pred p [], Neg ?or] \<turnstile> ?or"
    using OrI1 by blast
  moreover have "[Pred p [], Neg ?or] \<turnstile> Neg ?or"
    by (simp add: Assum)
  ultimately have "[Pred p [], Neg ?or] \<turnstile> FF"
    using NegE by blast
  then have "[Neg ?or] \<turnstile> Neg (Pred p [])"
    using NegI by blast
  then have "[Neg ?or] \<turnstile> ?or"
    using OrI2 by blast
  moreover have "[Neg ?or] \<turnstile> Neg ?or"
    by (simp add: Assum)
  ultimately have "[Neg ?or] \<turnstile> FF"
    using NegE by blast
  then show ?thesis
    using Class by blast
qed
  
theorem ex_all_commute:
  "([]::(nat, 'b) form list) \<turnstile> Impl (Exists (Forall (Pred p [Var 1, Var 0])))
     (Forall (Exists (Pred p [Var 0, Var 1])))"
  apply (rule ImplI)
  apply (rule_tac n=0 in ForallI)
    prefer 2
    apply simp
   prefer 2
   apply simp
  apply simp
  apply (rule_tac n=1 and a="Forall (Pred p [Var 1, Var 0])" in ExistsE)
      apply (rule Assum, simp)
     prefer 2
     apply simp
    prefer 2
    apply simp
   prefer 2
   apply simp
  apply (rule_tac t="App 1 []" in ExistsI)
  apply (rule_tac t="App 0 []" and a="Pred p [App (Suc 0) [], Var 0]" in ForallE')
   apply (rule Assum, simp)
  apply (rule Assum, simp)
  done

theorem drinker: "([]::(nat, 'b) form list) \<turnstile>
  Exists (Impl (Pred P [Var 0]) (Forall (Pred P [Var 0])))"
  apply (rule Class')
  apply (rule_tac t="Var 0" in ExistsI)
  apply simp
  apply (rule ImplI)
  apply (rule_tac n=0 in ForallI)
  prefer 2
  apply simp
  prefer 2
  apply simp
  apply simp
  apply (rule Class)
  apply (rule_tac a="Exists (Impl (Pred P [Var 0]) (Forall (Pred P [Var 0])))" in NegE)
  apply (rule Assum, simp)
  apply (rule_tac t="App 0 []" in ExistsI)
  apply simp
  apply (rule ImplI)
  apply (rule FFE)
  apply (rule_tac a="Pred P [App 0 []]" in NegE)
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  done
    
theorem peirce:
  "[] \<turnstile> Impl (Impl (Impl (Pred P []) (Pred Q [])) (Pred P [])) (Pred P [])"
  apply (rule Class')
  apply (rule ImplI)
  apply (rule_tac a="Impl (Pred P []) (Pred Q [])" in ImplE)
   apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule FFE)
  apply (rule_tac
      a="Impl (Impl (Impl (Pred P []) (Pred Q [])) (Pred P [])) (Pred P [])"
      in NegE)
   apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule Assum, simp)
  done


section {* Correctness *}

text {*
The correctness of the proof calculus introduced in \secref{sec:proof-calculus}
can now be proved by induction on the derivation of @{term "G \<turnstile> p"}, using the
substitution rules proved in \secref{sec:semantics}.
*}

theorem correctness: "G \<turnstile> p \<Longrightarrow> \<forall>e f g. e,f,g,G \<Turnstile> p"
  proof (induct p rule: deriv.induct)
    case (Assum a G)
    then show ?case by (simp add: model_def list_all_iff)
  next
    case (ForallI G a n)
    show ?case proof (intro allI)
      fix f g and e :: "nat \<Rightarrow> 'c"
      have "\<forall>z. e, (f(n := \<lambda>x. z)), g, G \<Turnstile> (a[App n []/0])"
        using ForallI by blast
      then have "\<forall>z. list_all (eval e f g) G \<longrightarrow> eval (e\<langle>0:z\<rangle>) f g a"
        using ForallI unfolding model_def by simp
      then show "e,f,g,G \<Turnstile> Forall a" unfolding model_def by simp
    qed
next
  case (ExistsE G a n b)
  show ?case proof (intro allI)
    fix f g and e :: "nat \<Rightarrow> 'c"
    obtain z where "list_all (eval e f g) G \<longrightarrow> eval (e\<langle>0:z\<rangle>) f g a"
      using ExistsE unfolding model_def by simp blast
    then have "e, (f(n := \<lambda>x. z)), g, G \<Turnstile> b"
      using ExistsE unfolding model_def by simp
    then show "e,f,g,G \<Turnstile> b"
      using ExistsE unfolding model_def by simp
  qed
qed (simp_all add: model_def, blast+)
  
section {* Completeness *}

text {*
The goal of this section is to prove completeness of the natural deduction
calculus introduced in \secref{sec:proof-calculus}. Before we start with the
actual proof, it is useful to note that the following two formulations of
completeness are equivalent:
\begin{enumerate}
\item All valid formulae are derivable, i.e.
  @{text "ps \<Turnstile> p \<Longrightarrow> ps \<turnstile> p"}
\item All consistent sets are satisfiable
\end{enumerate}
The latter property is called the {\em model existence theorem}. To see why 2
implies 1, observe that @{text "Neg p, ps \<notturnstile> FF"} implies
that @{text "Neg p, ps"} is consistent, which, by the model existence theorem,
implies that @{text "Neg p, ps"} has a model, which in turn implies that
@{text "ps \<notTurnstile> p"}. By contraposition, it therefore follows
from @{text "ps \<Turnstile> p"} that @{text "Neg p, ps \<turnstile> FF"}, which allows us to
deduce @{text "ps \<turnstile> p"} using rule @{text Class}.

In most textbooks on logic, a set @{text S} of formulae is called {\em consistent},
if no contradiction can be derived from @{text S} using a {\em specific proof calculus},
i.e.\ @{text "S \<notturnstile> FF"}. Rather than defining consistency relative to
a {\em specific} calculus, Fitting uses the more general approach of describing
properties that all consistent sets must have (see \secref{sec:consistent-sets}).

The key idea behind the proof of the model existence theorem is to
extend a consistent set to one that is {\em maximal} (see \secref{sec:extend}).
In order to do this, we use the fact that the set of formulae is enumerable
(see \secref{sec:enumeration}), which allows us to form a sequence
$\phi_0$, $\phi_1$, $\phi_2$, $\ldots$ containing all formulae.
We can then construct a sequence $S_i$ of consistent sets as follows:
\[
\begin{array}{l}
  S_0 = S \\
  S_{i+1} = \left\{\begin{array}{ll}
    S_i \cup \{\phi_i\} & \hbox{if } S_i \cup \{\phi_i\} \hbox{ consistent} \\
    S_i & \hbox{otherwise}
  \end{array}\right.
\end{array}
\]
To obtain a maximal consistent set, we form the union $\bigcup_i S_i$ of these
sets. To ensure that this union is still consistent, additional closure
(see \secref{sec:closure}) and finiteness (see \secref{sec:finiteness})
properties are needed.
It can be shown that a maximal consistent set is a {\em Hintikka set}
(see \secref{sec:hintikka}). Hintikka sets are satisfiable in {\em Herbrand}
models, where closed terms coincide with their interpretation.
*}


subsection {* Consistent sets *}

text {*
\label{sec:consistent-sets}
In this section, we describe an abstract criterion for consistent sets.
A set of sets of formulae is called a {\em consistency property}, if the
following holds:
*}

definition
  consistency :: "('a, 'b) form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow>
     (\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)) \<and>
     FF \<notin> S \<and> Neg TT \<notin> S \<and>
     (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
     (\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
     (\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
     (\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
     (\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> C) \<and>
     (\<forall>P. Exists P \<in> S \<longrightarrow> (\<exists>x. S \<union> {P[App x []/0]} \<in> C)) \<and>
     (\<forall>P. Neg (Forall P) \<in> S \<longrightarrow> (\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> C)))"

text {*
In \secref{sec:finiteness}, we will show how to extend a consistency property
to one that is of {\em finite character}. However, the above
definition of a consistency property cannot be used for this, since there is
a problem with the treatment of formulae of the form @{text "Exists P"} and
@{text "Neg (Forall P)"}. Fitting therefore suggests to define an {\em alternative
consistency property} as follows:
*}

definition
  alt_consistency :: "('a, 'b) form set set \<Rightarrow> bool" where
  "alt_consistency C = (\<forall>S. S \<in> C \<longrightarrow>
     (\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)) \<and>
     FF \<notin> S \<and> Neg TT \<notin> S \<and>
     (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
     (\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
     (\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
     (\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
     (\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> C) \<and>
     (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Exists P \<in> S \<longrightarrow>
       S \<union> {P[App x []/0]} \<in> C) \<and>
     (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Neg (Forall P) \<in> S \<longrightarrow>
       S \<union> {Neg (P[App x []/0])} \<in> C))"

text {*
Note that in the clauses for @{text "Exists P"} and @{text "Neg (Forall P)"},
the first definition requires the existence of a parameter @{text x} with a certain
property, whereas the second definition requires that all parameters @{text x} that
are new for @{text S} have a certain property. A consistency property can easily be
turned into an alternative consistency property by applying a suitable parameter
substitution:
*}

definition
  mk_alt_consistency :: "('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set" where
  "mk_alt_consistency C = {S. \<exists>f. psubst f ` S \<in> C}"
  
theorem alt_consistency:
  assumes conc: "consistency C"
  shows "alt_consistency (mk_alt_consistency C)" (is "alt_consistency ?C'")
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix f :: "'a \<Rightarrow> 'a" and S :: "('a, 'b) form set"
    
  assume "S \<in> mk_alt_consistency C"
  then obtain f where sc: "psubst f ` S \<in> C" (is "?S' \<in> C")
    unfolding mk_alt_consistency_def by blast
      
  fix p ts
  show "\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
  proof
    assume *: "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
    then have "psubst f (Pred p ts) \<in> ?S'"
      by blast
    then have "Pred p (psubstts f ts) \<in> ?S'"
      by simp
    then have "Neg (Pred p (psubstts f ts)) \<notin> ?S'"
      using conc sc by (simp add: consistency_def)
    then have "Neg (Pred p ts) \<notin> S"
      by force
    then show False
      using * by blast
  qed
    
  have "FF \<notin> ?S'" and "Neg TT \<notin> ?S'"
    using conc sc by (simp_all add: consistency_def)
  then show "FF \<notin> S" and "Neg TT \<notin> S"
    by (force, force)
      
  { fix Z
    assume "Neg (Neg Z) \<in> S"
    then have "psubst f (Neg (Neg Z)) \<in> ?S'"
      by blast
    then have "?S' \<union> {psubst f Z} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {Z} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "And A B \<in> S"
    then have "psubst f (And A B) \<in> ?S'"
      by blast
    then have "?S' \<union> {psubst f A, psubst f B} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {A, B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "Neg (Or A B) \<in> S"
    then have "psubst f (Neg (Or A B)) \<in> ?S'"
      by blast
    then have "?S' \<union> {Neg (psubst f A), Neg (psubst f B)} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {Neg A, Neg B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "Neg (Impl A B) \<in> S"
    then have "psubst f (Neg (Impl A B)) \<in> ?S'"
      by blast
    then have "?S' \<union> {psubst f A, Neg (psubst f B)} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {A, Neg B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "Or A B \<in> S"
    then have "psubst f (Or A B) \<in> ?S'"
      by blast
    then have "?S' \<union> {psubst f A} \<in> C \<or> ?S' \<union> {psubst f B} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {A} \<in> ?C' \<or> S \<union> {B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "Neg (And A B) \<in> S"
    then have "psubst f (Neg (And A B)) \<in> ?S'"
      by blast
    then have "?S' \<union> {Neg (psubst f A)} \<in> C \<or> ?S' \<union> {Neg (psubst f B)} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {Neg A} \<in> ?C' \<or> S \<union> {Neg B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix A B
    assume "Impl A B \<in> S"
    then have "psubst f (Impl A B) \<in> ?S'"
      by blast
    then have "?S' \<union> {Neg (psubst f A)} \<in> C \<or> ?S' \<union> {psubst f B} \<in> C"
      using conc sc by (simp add: consistency_def)
    then show "S \<union> {Neg A} \<in> ?C' \<or> S \<union> {B} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Forall P \<in> S"
    then have "psubst f (Forall P) \<in> ?S'"
      by blast
    then have "?S' \<union> {psubst f P[psubstt f t/0]} \<in> C"
      using \<open>closedt 0 t\<close> conc sc by (simp add: consistency_def)
    then show "S \<union> {P[t/0]} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Neg (Exists P) \<in> S"
    then have "psubst f (Neg (Exists P)) \<in> ?S'"
      by blast
    then have "?S' \<union> {Neg (psubst f P[psubstt f t/0])} \<in> C"
      using \<open>closedt 0 t\<close> conc sc by (simp add: consistency_def)
    then show "S \<union> {Neg (P[t/0])} \<in> ?C'"
      unfolding mk_alt_consistency_def by auto }
    
  { fix P :: "('a, 'b) form" and x f'
    assume "\<forall>a \<in> S. x \<notin> params a" and "Exists P \<in> S"
    moreover have "psubst f (Exists P) \<in> ?S'"
      using calculation by blast
    then have "\<exists>y. ?S' \<union> {psubst f P[App y []/0]} \<in> C"
      using conc sc by (simp add: consistency_def)
    then obtain y where "?S' \<union> {psubst f P[App y []/0]} \<in> C"
      by blast
        
    moreover have "psubst (f(x := y)) ` S = ?S'"
      using calculation by (simp cong add: image_cong)
    moreover have "psubst (f(x := y)) ` S \<union> {psubst (f(x := y)) P[App ((f(x := y)) x) []/0]} \<in> C"
      using calculation by auto
    ultimately have "\<exists>f. psubst f ` S \<union> {psubst f P[App (f x) []/0]} \<in> C"
      by blast
    then show "S \<union> {P[App x []/0]} \<in> ?C'"
      unfolding mk_alt_consistency_def by simp }
    
  { fix P :: "('a, 'b) form" and x
    assume "\<forall>a \<in> S. x \<notin> params a" and "Neg (Forall P) \<in> S"
    moreover have "psubst f (Neg (Forall P)) \<in> ?S'"
      using calculation by blast
    then have "\<exists>y. ?S' \<union> {Neg (psubst f P[App y []/0])} \<in> C"
      using conc sc by (simp add: consistency_def)
    then obtain y where "?S' \<union> {Neg (psubst f P[App y []/0])} \<in> C"
      by blast
        
    moreover have "psubst (f(x := y)) ` S = ?S'"
      using calculation by (simp cong add: image_cong)
    moreover have "psubst (f(x := y)) ` S \<union> {Neg (psubst (f(x := y)) P[App ((f(x := y)) x) []/0])} \<in> C"
      using calculation by auto
    ultimately have "\<exists>f. psubst f ` S \<union> {Neg (psubst f P[App (f x) []/0])} \<in> C"
      by blast
    then show "S \<union> {Neg (P[App x []/0])} \<in> ?C'"
      unfolding mk_alt_consistency_def by simp }
qed

theorem mk_alt_consistency_subset: "C \<subseteq> mk_alt_consistency C"
  unfolding mk_alt_consistency_def
proof
  fix x assume "x \<in> C"
  then have "psubst id ` x \<in> C"
    by simp
  then have "(\<exists>f. psubst f ` x \<in> C)"
    by blast
  then show "x \<in> {S. \<exists>f. psubst f ` S \<in> C}"
    by simp
qed

subsection {* Closure under subsets *}

text {*
\label{sec:closure}
We now show that a consistency property can be extended to one
that is closed under subsets.
*}

definition
  close :: "('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set" where
  "close C = {S. \<exists>S' \<in> C. S \<subseteq> S'}"

definition
  subset_closed :: "'a set set \<Rightarrow> bool" where
  "subset_closed C = (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)"

theorem close_consistency: "consistency C \<Longrightarrow> consistency (close C)"
  unfolding close_def consistency_def
proof (intro allI impI, simp only: mem_Collect_eq,
       elim allE impE bexE, assumption, elim conj_forward)
  fix S x
  assume "x \<in> C" and "S \<subseteq> x"
    
  { assume "\<forall>p ts. \<not> (Pred p ts \<in> x \<and> Neg (Pred p ts) \<in> x)"
    then show "\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
      using \<open>S \<subseteq> x\<close> by blast }
  
  { assume "FF \<notin> x" then show "FF \<notin> S"
      using \<open>S \<subseteq> x\<close> by blast }
    
  { assume "Neg TT \<notin> x" then show "Neg TT \<notin> S"
      using \<open>S \<subseteq> x\<close> by blast }
    
  { assume "\<forall>Z. Neg (Neg Z) \<in> x \<longrightarrow> x \<union> {Z} \<in> C"
    then show "\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {Z}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  { assume "\<forall>A B. And A B \<in> x \<longrightarrow> x \<union> {A, B} \<in> C"
    then show "\<forall>A B. And A B \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {A, B}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  { assume "\<forall>A B. Neg (Or A B) \<in> x \<longrightarrow> x \<union> {Neg A, Neg B} \<in> C"
    then show "\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {Neg A, Neg B}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  { assume *: "\<forall>A B. Or A B \<in> x \<longrightarrow> x \<union> {A} \<in> C \<or> x \<union> {B} \<in> C"
    show "\<forall>A B. Or A B \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {A})) \<or> Bex C (op \<subseteq> (S \<union> {B}))"
    proof (intro allI impI)
      fix A B
      assume "Or A B \<in> S"
      then have "x \<union> {A} \<in> C \<or> x \<union> {B} \<in> C"
        using * \<open>S \<subseteq> x\<close> by blast
      then show "Bex C (op \<subseteq> (S \<union> {A})) \<or> Bex C (op \<subseteq> (S \<union> {B}))"
      proof
        assume "x \<union> {A} \<in> C"
        then have "(x \<union> {A}) \<in> C \<and> (S \<union> {A}) \<subseteq> (x \<union> {A})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      next
        assume "x \<union> {B} \<in> C"
        then have "(x \<union> {B}) \<in> C \<and> (S \<union> {B}) \<subseteq> (x \<union> {B})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      qed
    qed }
    
  { assume *: "\<forall>A B. Neg (And A B) \<in> x \<longrightarrow> x \<union> {Neg A} \<in> C \<or> x \<union> {Neg B} \<in> C"
    show "\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {Neg A})) \<or> Bex C (op \<subseteq> (S \<union> {Neg B}))"
    proof (intro allI impI)
      fix A B
      assume "Neg (And A B) \<in> S"
      then have "x \<union> {Neg A} \<in> C \<or> x \<union> {Neg B} \<in> C"
        using * \<open>S \<subseteq> x\<close> by blast
      then show "Bex C (op \<subseteq> (S \<union> {Neg A})) \<or> Bex C (op \<subseteq> (S \<union> {Neg B}))"
      proof
        assume "x \<union> {Neg A} \<in> C"
        then have "(x \<union> {Neg A}) \<in> C \<and> (S \<union> {Neg A}) \<subseteq> (x \<union> {Neg A})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      next
        assume "x \<union> {Neg B} \<in> C"
        then have "(x \<union> {Neg B}) \<in> C \<and> (S \<union> {Neg B}) \<subseteq> (x \<union> {Neg B})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      qed
    qed }
    
  { assume *: "\<forall>A B. Impl A B \<in> x \<longrightarrow> x \<union> {Neg A} \<in> C \<or> x \<union> {B} \<in> C"
    show "\<forall>A B. Impl A B \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {Neg A})) \<or> Bex C (op \<subseteq> (S \<union> {B}))"
    proof (intro allI impI)
      fix A B
      assume "Impl A B \<in> S"
      then have "x \<union> {Neg A} \<in> C \<or> x \<union> {B} \<in> C"
        using * \<open>S \<subseteq> x\<close> by blast
      then show "Bex C (op \<subseteq> (S \<union> {Neg A})) \<or> Bex C (op \<subseteq> (S \<union> {B}))"
      proof
        assume "x \<union> {Neg A} \<in> C"
        then have "(x \<union> {Neg A}) \<in> C \<and> (S \<union> {Neg A}) \<subseteq> (x \<union> {Neg A})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      next
        assume "x \<union> {B} \<in> C"
        then have "(x \<union> {B}) \<in> C \<and> (S \<union> {B}) \<subseteq> (x \<union> {B})"
          using \<open>S \<subseteq> x\<close> \<open>x \<in> C\<close> by blast
        then show ?thesis by blast
      qed
    qed }
    
  { assume "\<forall>A B. Neg (Impl A B) \<in> x \<longrightarrow> x \<union> {A, Neg B} \<in> C"
    then show "\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {A, Neg B}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  (* TODO: closedt 0 t is not needed for Forall and Neg Exists *)
  { assume " \<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> x \<longrightarrow> x \<union> {P[t/0]} \<in> C"
    then show "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {P[t/0]}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  { assume " \<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> x \<longrightarrow> x \<union> {Neg (P[t/0])} \<in> C"
    then show "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> Bex C (op \<subseteq> (S \<union> {Neg (P[t/0])}))"
      using \<open>S \<subseteq> x\<close> by simp blast }
    
  { assume *: "\<forall>P. Exists P \<in> x \<longrightarrow> (\<exists>y. x \<union> {P[App y []/0]} \<in> C)"
    then show "\<forall>P. Exists P \<in> S \<longrightarrow> (\<exists>y. Bex C (op \<subseteq> (S \<union> {P[App y []/0]})))"
    proof (intro allI impI)
      fix P
      assume "Exists P \<in> S"
      then have "Exists P \<in> x" using \<open>S \<subseteq> x\<close> by blast
      then obtain y where "x \<union> {P[App y []/0]} \<in> C"
        using * by blast
      then have "Bex C (op \<subseteq> (S \<union> {P[App y []/0]}))"
        using \<open>S \<subseteq> x\<close> by auto
      then show "\<exists>y. Bex C (op \<subseteq> (S \<union> {P[App y []/0]}))"
        by blast
    qed }
    
  { assume *: "\<forall>P. Neg (Forall P) \<in> x \<longrightarrow> (\<exists>y. x \<union> {Neg (P[App y []/0])} \<in> C)"
    then show "\<forall>P. Neg (Forall P) \<in> S \<longrightarrow> (\<exists>y. Bex C (op \<subseteq> (S \<union> {Neg (P[App y []/0])})))"
    proof (intro allI impI)
      fix P
      assume "Neg (Forall P) \<in> S"
      then have "Neg (Forall P) \<in> x" using \<open>S \<subseteq> x\<close> by blast
      then obtain y where "x \<union> {Neg (P[App y []/0])} \<in> C"
        using * by blast
      then have "Bex C (op \<subseteq> (S \<union> {Neg (P[App y []/0])}))"
        using \<open>S \<subseteq> x\<close> by auto
      then show "\<exists>y. Bex C (op \<subseteq> (S \<union> {Neg (P[App y []/0])}))"
        by blast
    qed } 
qed

theorem close_closed: "subset_closed (close C)"
  unfolding close_def subset_closed_def by blast

theorem close_subset: "C \<subseteq> close C"
  unfolding close_def by blast

text {*
If a consistency property @{text C} is closed under subsets, so is the
corresponding alternative consistency property:
*}

theorem mk_alt_consistency_closed:
  "subset_closed C \<Longrightarrow> subset_closed (mk_alt_consistency C)"
  unfolding mk_alt_consistency_def subset_closed_def
  proof (intro ballI allI impI)
    fix S S' :: "('a, 'b) form set"
    assume "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
      and "S' \<in> {S. \<exists>f. psubst f ` S \<in> C}"
      and "S \<subseteq> S'"
    then obtain f :: "'a \<Rightarrow> 'a" where
      *: "psubst f ` S' \<in> C" by blast
    
    have "psubst f ` S \<subseteq> psubst f ` S'" using \<open>S \<subseteq> S'\<close> by blast
    also have "psubst f ` S' \<in> C" using * by blast
    moreover note \<open>\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C\<close> and \<open>S \<subseteq> S'\<close>
    ultimately have "psubst f ` S \<in> C" by blast
    then show "S \<in> {S. \<exists>f. psubst f ` S \<in> C}" by blast
  qed

subsection {* Finite character *}

text {*
\label{sec:finiteness}
In this section, we show that an alternative consistency property can
be extended to one of finite character. A set of sets @{text C} is said
to be of finite character, provided that @{text S} is a member of @{text C}
if and only if every subset of @{text S} is.
*}

definition
  finite_char :: "'a set set \<Rightarrow> bool" where
  "finite_char C = (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))"

definition
  mk_finite_char :: "'a set set \<Rightarrow> 'a set set" where
  "mk_finite_char C = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C}"

(* TODO: lots of the cases are very similar *)
theorem finite_alt_consistency:
  "alt_consistency C \<Longrightarrow> subset_closed C \<Longrightarrow> alt_consistency (mk_finite_char C)"
  unfolding alt_consistency_def subset_closed_def mk_finite_char_def
proof (intro allI impI, erule CollectE, elim conjE'')
  fix S
  assume sc: "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
    and sc': "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C"
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S))"
    show "\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
    proof (intro allI impI notI)
      fix p ts
      assume assm: "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
      then have "\<dots> = ({Pred p ts, Neg (Pred p ts)} \<subseteq> S)"
        by blast
      moreover have "finite {Pred p ts, Neg (Pred p ts)}"
        by blast
      moreover have "{Pred p ts, Neg (Pred p ts)} \<in> C"
        using assm sc' by simp
      ultimately show False using * by blast
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> FF \<notin> S"
    show "FF \<notin> S"
    proof
      assume "FF \<in> S"
      also have "FF \<in> S \<longrightarrow> finite {FF} \<longrightarrow> {FF} \<in> C"
        using sc' by simp
      finally show False using * by blast
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> Neg TT \<notin> S"
    show "Neg TT \<notin> S"
    proof
      assume "Neg TT \<in> S"
      also have "Neg TT \<in> S \<longrightarrow> finite {Neg TT} \<longrightarrow> {Neg TT} \<in> C"
        using sc' by simp
      finally show False using * by blast
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C)"
    show "\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix Z S'
      assume "Neg (Neg Z) \<in> S" and "S' \<subseteq> S \<union> {Z}" and "finite S'"
      then have "S' - {Z} \<union> {Neg (Neg Z)} \<subseteq> S"
        by blast
      also have "finite (S' - {Z} \<union> {Neg (Neg Z)})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {Z} \<union> {Neg (Neg Z)} \<in> C"
        using calculation sc' by blast
      moreover have "S' - {Z} \<union> {Neg (Neg Z)} \<union> {Z} \<in> C"
        using calculation * by blast
      then have "\<forall>S \<subseteq> (S' - {Z} \<union> {Neg (Neg Z)} \<union> {Z}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
      
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C)"
    show "\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix A B S'
      assume "And A B \<in> S" and "S' \<subseteq> S \<union> {A, B}" and "finite S'"
      then have "S' - {A, B} \<union> {And A B} \<subseteq> S"
        by blast
      also have "finite (S' - {A, B} \<union> {And A B})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {A, B} \<union> {And A B} \<in> C"
        using calculation sc' by blast
      moreover have "S' - {A, B} \<union> {And A B} \<union> {A, B} \<in> C"
        using calculation * by blast
      then have "\<forall>S \<subseteq> (S' - {A, B} \<union> {And A B} \<union> {A, B}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C)"
    show "\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix A B S'
      assume "Neg (Or A B) \<in> S" and "S' \<subseteq> S \<union> {Neg A, Neg B}" and "finite S'"
      then have "S' - {Neg A, Neg B} \<union> {Neg (Or A B)} \<subseteq> S"
        by blast
      also have "finite (S' - {Neg A, Neg B} \<union> {Neg (Or A B)})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {Neg A, Neg B} \<union> {Neg (Or A B)} \<in> C"
        using calculation sc' by blast
      moreover have "S' - {Neg A, Neg B} \<union> {Neg (Or A B)} \<union> {Neg A, Neg B} \<in> C"
        using calculation * by blast
      then have "\<forall>S \<subseteq> (S' - {Neg A, Neg B} \<union> {Neg (Or A B)} \<union> {Neg A, Neg B}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C)"
    show " \<forall>A B. Or A B \<in> S \<longrightarrow>
            S \<union> {A} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C} \<or>
            S \<union> {B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI, rule ccontr, simp, elim conjE exE)
      fix A B S' S''
      assume "Or A B \<in> S"
        and " S' \<subseteq> insert A S" "finite S'"  "S' \<notin> C"
        and "S'' \<subseteq> insert B S" "finite S''" "S'' \<notin> C"
      
      then have "(S' - {A}) \<union> (S'' - {B}) \<union> {Or A B} \<subseteq> S"
        by blast
      also have "finite (S' - {A} \<union> (S'' - {B}) \<union> {Or A B})"
        using \<open>finite S'\<close> \<open>finite S''\<close> by blast
      moreover have **: "(S' - {A}) \<union> (S'' - {B}) \<union> {Or A B} \<in> C"
        using calculation sc' by blast
      then have
        "((S' - {A}) \<union> (S'' - {B}) \<union> {Or A B}) \<union> {A} \<in> C \<or>
         ((S' - {A}) \<union> (S'' - {B}) \<union> {Or A B}) \<union> {B} \<in> C"
        using * by blast
      then show False proof
        assume "S' - {A} \<union> (S'' - {B}) \<union> {Or A B} \<union> {A} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {A} \<union> (S'' - {B}) \<union> {Or A B}) \<union> {A}. S \<in> C"
          using sc by blast
        then have "S' \<in> C" by blast
        then show False using \<open>S' \<notin> C\<close> by blast
      next
        assume "S' - {A} \<union> (S'' - {B}) \<union> {Or A B} \<union> {B} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {A} \<union> (S'' - {B}) \<union> {Or A B}) \<union> {B}. S \<in> C"
          using sc by blast
        then have "S'' \<in> C" by blast
        then show False using \<open>S'' \<notin> C\<close> by blast
      qed
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C)"
    show " \<forall>A B. Neg (And A B) \<in> S \<longrightarrow>
            S \<union> {Neg A} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C} \<or>
            S \<union> {Neg B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI, rule ccontr, simp, elim conjE exE)
      fix A B S' S''
      assume "Neg (And A B) \<in> S"
        and " S' \<subseteq> insert (Neg A) S" "finite S'"  "S' \<notin> C"
        and "S'' \<subseteq> insert (Neg B) S" "finite S''" "S'' \<notin> C"
      
      then have "(S' - {Neg A}) \<union> (S'' - {Neg B}) \<union> {Neg (And A B)} \<subseteq> S"
        by blast
      also have "finite (S' - {Neg A} \<union> (S'' - {Neg B}) \<union> {Neg (And A B)})"
        using \<open>finite S'\<close> \<open>finite S''\<close> by blast
      moreover have **: "(S' - {Neg A}) \<union> (S'' - {Neg B}) \<union> {Neg (And A B)} \<in> C"
        using calculation sc' by blast
      then have
        "((S' - {Neg A}) \<union> (S'' - {Neg B}) \<union> {Neg (And A B)}) \<union> {Neg A} \<in> C \<or>
         ((S' - {Neg A}) \<union> (S'' - {Neg B}) \<union> {Neg (And A B)}) \<union> {Neg B} \<in> C"
        using * by blast
      then show False proof
        assume "S' - {Neg A} \<union> (S'' - {Neg B}) \<union> {Neg (And A B)} \<union> {Neg A} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {Neg A} \<union> (S'' - {Neg B}) \<union> {Neg (And A B)}) \<union> {Neg A}. S \<in> C"
          using sc by blast
        then have "S' \<in> C" by blast
        then show False using \<open>S' \<notin> C\<close> by blast
      next
        assume "S' - {Neg A} \<union> (S'' - {Neg B}) \<union> {Neg (And A B)} \<union> {Neg B} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {Neg A} \<union> (S'' - {Neg B}) \<union> {Neg (And A B)}) \<union> {Neg B}. S \<in> C"
          using sc by blast
        then have "S'' \<in> C" by blast
        then show False using \<open>S'' \<notin> C\<close> by blast
      qed
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C)"
    show " \<forall>A B. Impl A B \<in> S \<longrightarrow>
            S \<union> {Neg A} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C} \<or>
            S \<union> {B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI, rule ccontr, simp, elim conjE exE)
      fix A B S' S''
      assume "Impl A B \<in> S"
        and " S' \<subseteq> insert (Neg A) S" "finite S'"  "S' \<notin> C"
        and "S'' \<subseteq> insert B S" "finite S''" "S'' \<notin> C"
      
      then have "(S' - {Neg A}) \<union> (S'' - {B}) \<union> {Impl A B} \<subseteq> S"
        by blast
      also have "finite (S' - {Neg A} \<union> (S'' - {B}) \<union> {Impl A B})"
        using \<open>finite S'\<close> \<open>finite S''\<close> by blast
      moreover have **: "(S' - {Neg A}) \<union> (S'' - {B}) \<union> {Impl A B} \<in> C"
        using calculation sc' by blast
      then have
        "((S' - {Neg A}) \<union> (S'' - {B}) \<union> {Impl A B}) \<union> {Neg A} \<in> C \<or>
         ((S' - {Neg A}) \<union> (S'' - {B}) \<union> {Impl A B}) \<union> {B} \<in> C"
        using * by blast
      then show False proof
        assume "S' - {Neg A} \<union> (S'' - {B}) \<union> {Impl A B} \<union> {Neg A} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {Neg A} \<union> (S'' - {B}) \<union> {Impl A B}) \<union> {Neg A}. S \<in> C"
          using sc by blast
        then have "S' \<in> C" by blast
        then show False using \<open>S' \<notin> C\<close> by blast
      next
        assume "S' - {Neg A} \<union> (S'' - {B}) \<union> {Impl A B} \<union> {B} \<in> C"
        then have "\<forall>S \<subseteq> (S' - {Neg A} \<union> (S'' - {B}) \<union> {Impl A B}) \<union> {B}. S \<in> C"
          using sc by blast
        then have "S'' \<in> C" by blast
        then show False using \<open>S'' \<notin> C\<close> by blast
      qed
    qed }
    
  { assume *: "\<forall>S. S \<in> C \<longrightarrow> (\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C)"
    show "\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix A B S'
      assume "Neg (Impl A B) \<in> S" and "S' \<subseteq> S \<union> {A, Neg B}" and "finite S'"
      then have "S' - {A, Neg B} \<union> {Neg (Impl A B)} \<subseteq> S"
        by blast
      also have "finite (S' - {A, Neg B} \<union> {Neg (Impl A B)})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {A, Neg B} \<union> {Neg (Impl A B)} \<in> C"
        using calculation sc' by blast
      ultimately have "S' - {A, Neg B} \<union> {Neg (Impl A B)} \<union> {A, Neg B} \<in> C"
        using * by blast
      then have "\<forall>S \<subseteq> (S' - {A, Neg B} \<union> {Neg (Impl A B)} \<union> {A, Neg B}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
   
  { assume *: " \<forall>S. S \<in> C \<longrightarrow> (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> C)"
    show "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix P t S'
      assume "closedt 0 t"
        and "Forall P \<in> S"
        and "S' \<subseteq> S \<union> {subst P t 0}"
        and "finite S'"
        
      then have "S' - {P[t/0]} \<union> {Forall P} \<subseteq> S"
        by blast
      moreover have "finite (S' - {P[t/0]} \<union> {Forall P})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {P[t/0]} \<union> {Forall P} \<in> C"
        using calculation sc' by blast
      ultimately have "S' - {P[t/0]} \<union> {Forall P} \<union> {P[t/0]} \<in> C"
        using * \<open>closedt 0 t\<close> by blast
      then have "\<forall>S \<subseteq> (S' - {P[t/0]} \<union> {Forall P} \<union> {P[t/0]}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
    
  { assume *: " \<forall>S. S \<in> C \<longrightarrow> (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> C)"
    show "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix P t S'
      assume "closedt 0 t"
        and "Neg (Exists P) \<in> S"
        and "S' \<subseteq> S \<union> {Neg (subst P t 0)}"
        and "finite S'"
        
      then have "S' - {Neg (P[t/0])} \<union> {Neg (Exists P)} \<subseteq> S"
        by blast
      moreover have "finite (S' - {Neg (P[t/0])} \<union> {Neg (Exists P)})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {Neg (P[t/0])} \<union> {Neg (Exists P)} \<in> C"
        using calculation sc' by blast
      ultimately have "S' - {Neg (P[t/0])} \<union> {Neg (Exists P)} \<union> {Neg (P[t/0])} \<in> C"
        using * \<open>closedt 0 t\<close> by blast
      then have "\<forall>S \<subseteq> (S' - {Neg (P[t/0])} \<union> {Neg (Exists P)} \<union> {Neg (P[t/0])}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
    
  { assume *: " \<forall>S. S \<in> C \<longrightarrow> (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Exists P \<in> S \<longrightarrow> S \<union> {P[App x []/0]} \<in> C)"
    show "\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Exists P \<in> S \<longrightarrow> S \<union> {P[App x []/0]} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix P x S'
      assume "\<forall>a\<in>S. x \<notin> params a"
        and "Exists P \<in> S"
        and "S' \<subseteq> S \<union> {P[App x []/0]}"
        and "finite S'"
        
      then have "S' - {P[App x []/0]} \<union> {Exists P} \<subseteq> S"
        by blast
      moreover have "finite (S' - {P[App x []/0]} \<union> {Exists P})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {P[App x []/0]} \<union> {Exists P} \<in> C"
        using calculation sc' by blast
      ultimately have "S' - {P[App x []/0]} \<union> {Exists P} \<union> {P[App x []/0]} \<in> C"
        using * \<open>\<forall>a\<in>S. x \<notin> params a\<close> by blast
      then have "\<forall>S \<subseteq> (S' - {P[App x []/0]} \<union> {Exists P} \<union> {P[App x []/0]}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
    
  { assume *: " \<forall>S. S \<in> C \<longrightarrow> (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Neg (Forall P) \<in> S \<longrightarrow> S \<union> {Neg (P[App x []/0])} \<in> C)"
    show "\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Neg (Forall P) \<in> S \<longrightarrow> S \<union> {Neg (P[App x []/0])} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C}"
    proof (intro allI impI CollectI)
      fix P x S'
      assume "\<forall>a\<in>S. x \<notin> params a"
        and "Neg (Forall P) \<in> S"
        and "S' \<subseteq> S \<union> {Neg (P[App x []/0])}"
        and "finite S'"
        
      then have "S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)} \<subseteq> S"
        by blast
      moreover have "finite (S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)})"
        using \<open>finite S'\<close> by blast
      moreover have "S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)} \<in> C"
        using calculation sc' by blast
      ultimately have "S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)} \<union> {Neg (P[App x []/0])} \<in> C"
        using * \<open>\<forall>a\<in>S. x \<notin> params a\<close> by blast
      then have "\<forall>S \<subseteq> (S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)} \<union> {Neg (P[App x []/0])}). S \<in> C"
        using sc by blast
      then show "S' \<in> C" by blast
    qed }
qed

theorem finite_char: "finite_char (mk_finite_char C)"
  unfolding finite_char_def mk_finite_char_def by blast

theorem finite_char_closed: "finite_char C \<Longrightarrow> subset_closed C"
  unfolding finite_char_def subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume *: "\<forall>S. (S \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C)"
    and "S' \<in> C" and "S \<subseteq> S'"
  then have "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C" by blast
  then show "S \<in> C" using * by blast
qed

theorem finite_char_subset: "subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C"
  unfolding mk_finite_char_def subset_closed_def by blast

subsection {* Enumerating datatypes *}

text {*
\label{sec:enumeration}
In the following section, we will show that elements of datatypes
can be enumerated. This will be done by specifying functions that
map natural numbers to elements of datatypes and vice versa.
*}

subsubsection {* Enumerating pairs of natural numbers *}

text {*
\begin{figure}
\begin{center}
\includegraphics[scale=0.6]{diag}
\end{center}
\caption{Cantor's method for enumerating sets of pairs}\label{fig:diag}
\end{figure}
As a starting point, we show that pairs of natural numbers are enumerable.
For this purpose, we use a method due to Cantor, which is illustrated in
\figref{fig:diag}. The function for mapping natural numbers to pairs of
natural numbers can be characterized recursively as follows:
*}

primrec
  diag :: "nat \<Rightarrow> (nat \<times> nat)"
where
  "diag 0 = (0, 0)"
| "diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))"

theorem diag_le1: "fst (diag (Suc n)) < Suc n"
  by (induct n) (simp_all add: Let_def split_def split: nat.split)

theorem diag_le2: "snd (diag (Suc (Suc n))) < Suc (Suc n)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc _)
    then show ?case using diag_le1
      by (simp add: Let_def split_def split: nat.split)
  qed
qed
  
theorem diag_le3: "fst (diag n) = Suc x \<Longrightarrow> snd (diag n) < n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then show ?case proof (induct n')
    case 0
    then show ?case by simp
  next
    case (Suc n'')
    then show ?case using diag_le2 by simp
  qed
qed

theorem diag_le4: "fst (diag n) = Suc x \<Longrightarrow> x < n"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n')
  then have "fst (diag (Suc n')) < Suc n'"
    using diag_le1 by blast
  then show ?case using Suc by simp
qed

function
  undiag :: "nat \<times> nat \<Rightarrow> nat"
where
  "undiag (0, 0) = 0"
| "undiag (0, Suc y) = Suc (undiag (y, 0))"
| "undiag (Suc x, y) = Suc (undiag (x, Suc y))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)") auto

theorem diag_undiag [simp]: "diag (undiag (x, y)) = (x, y)"
  by (induct rule: undiag.induct) simp_all

subsubsection {* Enumerating trees *}

text {*
When writing enumeration functions for datatypes, it is useful to
note that all datatypes are some kind of trees. In order to
avoid re-inventing the wheel, we therefore write enumeration functions
for trees once and for all. In applications, we then only have to write
functions for converting between trees and concrete datatypes.
*}

datatype btree = Leaf nat | Branch btree btree

function
  diag_btree :: "nat \<Rightarrow> btree"
where
  "diag_btree n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
     | Suc x \<Rightarrow> Branch (diag_btree x) (diag_btree (snd (diag n))))"
  by auto
termination
  by (relation "measure id") (auto intro: diag_le3 diag_le4)

primrec
  undiag_btree :: "btree \<Rightarrow> nat"
where
  "undiag_btree (Leaf n) = undiag (0, n)"
| "undiag_btree (Branch t1 t2) =
     undiag (Suc (undiag_btree t1), undiag_btree t2)"

theorem diag_undiag_btree [simp]: "diag_btree (undiag_btree t) = t"
  by (induct t) simp_all

declare diag_btree.simps [simp del] undiag_btree.simps [simp del]


subsubsection {* Enumerating lists *}

fun
  list_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a list"
where
  "list_of_btree f (Leaf x) = []"
| "list_of_btree f (Branch (Leaf n) t) = f n # list_of_btree f t"

primrec
  btree_of_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> btree"
where
  "btree_of_list f [] = Leaf 0"
| "btree_of_list f (x # xs) = Branch (Leaf (f x)) (btree_of_list f xs)"

definition
  diag_list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "diag_list f n = list_of_btree f (diag_btree n)"

definition
  undiag_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "undiag_list f xs = undiag_btree (btree_of_list f xs)"

theorem diag_undiag_list [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_list d (undiag_list u xs) = xs"
  by (induct xs) (simp_all add: diag_list_def undiag_list_def)


subsubsection {* Enumerating terms *}

fun
  term_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a term"
  and term_list_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a term list"
where
  "term_of_btree f (Leaf m) = Var m"
| "term_of_btree f (Branch (Leaf m) t) =
     App (f m) (term_list_of_btree f t)"
| "term_list_of_btree f (Leaf m) = []"
| "term_list_of_btree f (Branch t1 t2) =
     term_of_btree f t1 # term_list_of_btree f t2"

primrec
  btree_of_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term \<Rightarrow> btree"
  and btree_of_term_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term list \<Rightarrow> btree"
where
  "btree_of_term f (Var m) = Leaf m"
| "btree_of_term f (App m ts) = Branch (Leaf (f m)) (btree_of_term_list f ts)"
| "btree_of_term_list f [] = Leaf 0"
| "btree_of_term_list f (t # ts) = Branch (btree_of_term f t) (btree_of_term_list f ts)"

theorem term_btree: assumes "\<And>x. d (u x) = x"
  shows "term_of_btree d (btree_of_term u t) = t"
  and "term_list_of_btree d (btree_of_term_list u ts) = ts"
  by (induct t and ts rule: btree_of_term.induct btree_of_term_list.induct) (simp_all add: assms)

definition
  diag_term :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a term" where
  "diag_term f n = term_of_btree f (diag_btree n)"

definition
  undiag_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term \<Rightarrow> nat" where
  "undiag_term f t = undiag_btree (btree_of_term f t)"

theorem diag_undiag_term [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_term d (undiag_term u t) = t"
  by (simp add: diag_term_def undiag_term_def term_btree)

fun
  form_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> btree \<Rightarrow> ('a, 'b) form"
where
  "form_of_btree f g (Leaf 0) = FF"
| "form_of_btree f g (Leaf (Suc 0)) = TT"
| "form_of_btree f g (Branch (Leaf 0) (Branch (Leaf m) (Leaf n))) =
     Pred (g m) (diag_list (diag_term f) n)"
| "form_of_btree f g (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     And (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc 0))) (Branch t1 t2)) =
     Or (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc 0)))) (Branch t1 t2)) =
     Impl (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc 0))))) t) =
     Neg (form_of_btree f g t)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0)))))) t) =
     Forall (form_of_btree f g t)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) t) =
     Exists (form_of_btree f g t)"

primrec
  btree_of_form :: "('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) form \<Rightarrow> btree"
where
  "btree_of_form f g FF = Leaf 0"
| "btree_of_form f g TT = Leaf (Suc 0)"
| "btree_of_form f g (Pred b ts) = Branch (Leaf 0)
     (Branch (Leaf (g b)) (Leaf (undiag_list (undiag_term f) ts)))"
| "btree_of_form f g (And a b) = Branch (Leaf (Suc 0))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Or a b) = Branch (Leaf (Suc (Suc 0)))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Impl a b) = Branch (Leaf (Suc (Suc (Suc 0))))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Neg a) = Branch (Leaf (Suc (Suc (Suc (Suc 0)))))
     (btree_of_form f g a)"
| "btree_of_form f g (Forall a) = Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0))))))
     (btree_of_form f g a)"
| "btree_of_form f g (Exists a) = Branch
     (Leaf (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))
     (btree_of_form f g a)"

definition
  diag_form :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> ('a, 'b) form" where
  "diag_form f g n = form_of_btree f g (diag_btree n)"

definition
  undiag_form :: "('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) form \<Rightarrow> nat" where
  "undiag_form f g x = undiag_btree (btree_of_form f g x)"

theorem diag_undiag_form [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> (\<And>x. d' (u' x) = x) \<Longrightarrow>
  diag_form d d' (undiag_form u u' f) = f"
  by (induct f) (simp_all add: diag_form_def undiag_form_def)

definition
  diag_form' :: "nat \<Rightarrow> (nat, nat) form" where
  "diag_form' = diag_form (\<lambda>n. n) (\<lambda>n. n)"

definition
  undiag_form' :: "(nat, nat) form \<Rightarrow> nat" where
  "undiag_form' = undiag_form (\<lambda>n. n) (\<lambda>n. n)"

theorem diag_undiag_form' [simp]: "diag_form' (undiag_form' f) = f"
  by (simp add: diag_form'_def undiag_form'_def)


subsection {* Extension to maximal consistent sets *}

text {*
\label{sec:extend}
Given a set @{text C} of finite character, we show that
the least upper bound of a chain of sets that are elements
of @{text C} is again an element of @{text C}.
*}

definition
  is_chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "is_chain f = (\<forall>n. f n \<subseteq> f (Suc n))"

theorem is_chainD: "is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)"
  by (induct n) (auto simp: is_chain_def)

theorem is_chainD': "is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> m \<le> k \<Longrightarrow> x \<in> f k"
proof -
  assume "is_chain f" and "x \<in> f m" and "m \<le> k"
  then have "\<exists>n. k = m + n" by arith
  then obtain n where "k = m + n" by blast
  then show "x \<in> f k"
    using \<open>is_chain f\<close> \<open>x \<in> f m\<close>
    by (simp add: is_chainD)
qed

theorem chain_index:
  assumes ch: "is_chain f" and fin: "finite F"
  shows "F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n"
  using fin proof (induct rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert x F)
  then have "\<exists>n. F \<subseteq> f n" and "\<exists>m. x \<in> f m" and "F \<subseteq> (\<Union>x. f x)"
    using ch by simp_all
  then obtain n and m where "F \<subseteq> f n" and "x \<in> f m"
    by blast
  have "m \<le> max n m" and "n \<le> max n m" by simp_all
  have "x \<in> f (max n m)"
    using is_chainD' ch \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close> by fast
  also have "F \<subseteq> f (max n m)"
    using is_chainD' ch \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close> by fast
  moreover have "x \<in> f (max n m) \<and> F \<subseteq> f (max n m)"
    using calculation by blast
  ultimately show ?case by blast
qed

lemma chain_union_closed':
  assumes "is_chain f" and "(\<forall>n. f n \<in> C)" and "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
  shows "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C" 
proof (intro allI impI)
  fix S'
  assume "finite S'" and "S' \<subseteq> (\<Union>n. f n)"
  then obtain n where "S' \<subseteq> f n"
    using chain_index \<open>is_chain f\<close> by blast
  also have "f n \<in> C" using \<open>\<forall>n. f n \<in> C\<close> by blast
  ultimately show "S' \<in> C"
    using \<open>\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C\<close> by blast
qed
  
theorem chain_union_closed:
  assumes "finite_char C" and "is_chain f" and "\<forall>n. f n \<in> C"
  shows "(\<Union>n. f n) \<in> C"
proof -
  have "subset_closed C"
    using finite_char_closed \<open>finite_char C\<close> by blast
  then have "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
    using subset_closed_def by blast
  then have "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C" 
    using chain_union_closed' assms by blast
  moreover have "((\<Union>n. f n) \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C)"
    using \<open>finite_char C\<close> unfolding finite_char_def by blast
  ultimately show ?thesis by blast
qed

text {*
We can now define a function @{text Extend} that extends a consistent
set to a maximal consistent set. To this end, we first define an auxiliary
function @{text extend} that produces the elements of an ascending chain of
consistent sets.
*}

primrec (nonexhaustive)
  dest_Neg :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Neg (Neg p) = p"

primrec (nonexhaustive)
  dest_Forall :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Forall (Forall p) = p"

primrec (nonexhaustive)
  dest_Exists :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Exists (Exists p) = p"

primrec
  extend :: "(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> nat \<Rightarrow> (nat, 'b) form set"
where
  "extend S C f 0 = S"
  | "extend S C f (Suc n) = (if extend S C f n \<union> {f n} \<in> C
     then
       (if (\<exists>p. f n = Exists p)
        then extend S C f n \<union> {f n} \<union> {subst (dest_Exists (f n))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0}
        else if (\<exists>p. f n = Neg (Forall p))
        then extend S C f n \<union> {f n} \<union> {Neg (subst (dest_Forall (dest_Neg (f n)))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0)}
        else extend S C f n \<union> {f n})
     else extend S C f n)"

definition
  Extend :: "(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> (nat, 'b) form set" where
  "Extend S C f = (\<Union>n. extend S C f n)"

theorem is_chain_extend: "is_chain (extend S C f)"
  by (simp add: is_chain_def) blast

theorem finite_paramst [simp]: "finite (paramst (t :: 'a term))"
  "finite (paramsts (ts :: 'a term list))"
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all split: sum.split)

theorem finite_params [simp]: "finite (params p)"
  by (induct p) simp_all

theorem finite_params_extend [simp]:
  "\<not> finite (\<Inter>p \<in> S. - params p) \<Longrightarrow> \<not> finite (\<Inter>p \<in> extend S C f n. - params p)"
  by (induct n) simp_all

theorem extend_in_C: "alt_consistency C \<Longrightarrow>
  S \<in> C \<Longrightarrow> \<not> finite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case proof (simp, intro conjI impI)
    assume "\<exists>p. f n = Neg (Forall p)" and "\<exists>p. f n = Exists p"
    then show "insert (dest_Exists (f n)[App
                (SOME k. k \<notin> params (f n) \<and> (\<forall>x\<in>extend S C f n. k \<notin> params x)) []/0])
                (insert (f n) (extend S C f n)) \<in> C"
      by auto
  next
    fix p
    assume "alt_consistency C"
      and "infinite (\<Inter>x\<in>S. - params x)"
      and "\<exists>p. f n = Neg (Forall p)"
      and "\<forall>p. f n \<noteq> Exists p"
      and "insert (f n) (extend S C f n) \<in> C"
    moreover have "\<forall>P x.
          (\<forall>a\<in>insert (f n) (extend S C f n). x \<notin> params a) \<longrightarrow>
          Neg (Forall P) \<in> insert (f n) (extend S C f n) \<longrightarrow>
          insert (Neg (P[App x []/0])) (insert (f n) (extend S C f n)) \<in> C"
      using calculation by (simp add: alt_consistency_def)
    moreover have "f n \<noteq> Exists p" using \<open>\<forall>p. f n \<noteq> Exists p\<close> by blast
    have "\<not> finite (- (\<Union>x\<in>extend S C f n \<union> {f n}. params x))"
      using calculation by simp
    then have "infinite (- (\<Union>x\<in>extend S C f n \<union> {f n}. params x))"
      by blast
    then obtain x where "x \<in> - (\<Union>x\<in>extend S C f n \<union> {f n}. params x)"
      using infinite_imp_nonempty by blast
    moreover have "insert (Neg (dest_Forall (dest_Neg (f n))[App x []/0]))
                      (insert (f n) (extend S C f n)) \<in> C"
      using calculation by fastforce
    show "insert (Neg (dest_Forall (dest_Neg (f n))[
            App (SOME k. k \<notin> params (f n) \<and> (\<forall>x\<in>extend S C f n. k \<notin> params x)) []/0]))
           (insert (f n) (extend S C f n)) \<in> C"
    proof (rule someI2)
      show "x \<notin> params (f n) \<and> (\<forall>x'\<in>extend S C f n. x \<notin> params x')"
        using calculation(7) by blast
    next
      fix x
      assume "x \<notin> params (f n) \<and> (\<forall>x'\<in>extend S C f n. x \<notin> params x')"
      then show "insert (Neg (dest_Forall (dest_Neg (f n))[App x []/0]))
                  (insert (f n) (extend S C f n)) \<in> C"
        using calculation(3) calculation(6) by auto
    qed
  next
    assume "alt_consistency C"
      and "infinite (\<Inter>x\<in>S. - params x)"
      and "\<forall>p. f n \<noteq> Neg (Forall p)"
      and "\<exists>p. f n = Exists p"
      and "insert (f n) (extend S C f n) \<in> C"
    moreover obtain p where "f n = Exists p"
      using \<open>\<exists>p. f n = Exists p\<close> by blast
    moreover have "(\<forall>a\<in>insert (Exists p) (extend S C f n). (SOME k. k \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)) \<notin> params a) \<longrightarrow>
           Exists p \<in> insert (Exists p) (extend S C f n) \<longrightarrow>
           insert (p[App (SOME k. k \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)) []/0]) (insert (Exists p) (extend S C f n)) \<in> C"
      using calculation by (simp add: alt_consistency_def)
    moreover have "infinite (- (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x))"
      using calculation by simp
    then obtain x where *: "x \<in> - (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)"
      using infinite_imp_nonempty by blast
    have "\<forall>a\<in>insert (Exists p) (extend S C f n). 
          (SOME k. k \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)) \<notin> params a"
    proof
      fix a
      assume "a \<in> insert (Exists p) (extend S C f n)"
      show "(SOME k. k \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)) \<notin> params a" 
      proof (rule someI2)
        show "x \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)"
          using * by blast
      next
        fix x
        assume "x \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)"
        then show "x \<notin> params a"
          using \<open>a \<in> insert (Exists p) (extend S C f n)\<close> by blast
      qed
    qed
    ultimately show "insert (dest_Exists (f n)[App (SOME k.
                  k \<notin> params (f n) \<and> (\<forall>x\<in>extend S C f n. k \<notin> params x))
              []/0]) (insert (f n) (extend S C f n)) \<in> C"
      by simp
  qed
qed

text {*
The main theorem about @{text Extend} says that if @{text C} is an
alternative consistency property that is of finite character,
@{text S} is consistent and @{text S} uses only finitely many
parameters, then @{text "Extend S C f"} is again consistent.
*}

theorem Extend_in_C: "alt_consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
  S \<in> C \<Longrightarrow> \<not> finite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C"
  unfolding Extend_def
  using chain_union_closed is_chain_extend extend_in_C
  by blast

theorem Extend_subset: "S \<subseteq> Extend S C f"
proof
  fix x
  assume "x \<in> S"
  then have "x \<in> extend S C f 0" by simp
  then have "\<exists>n. x \<in> extend S C f n" by blast
  then show "x \<in> Extend S C f" by (simp add: Extend_def)
qed

text {*
The @{text Extend} function yields a maximal set:
*}

definition
  maximal :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "maximal S C = (\<forall>S'\<in>C. S \<subseteq> S' \<longrightarrow> S = S')"

theorem extend_maximal:
  "\<forall>y. \<exists>n. y = f n \<Longrightarrow> finite_char C \<Longrightarrow> maximal (Extend S C f) C"
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume "\<forall>y. \<exists>n. y = f n"
    and "finite_char C"
    and "S' \<in> C"
    and "UNION UNIV (extend S C f) \<subseteq> S'"
  moreover have "S' \<subseteq> (\<Union>x. extend S C f x)"
  proof (rule ccontr)
    assume "\<not> S' \<subseteq> (\<Union>x. extend S C f x)"
    then have "\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. extend S C f x)"
      by blast
    then obtain z where "z \<in> S'" and *: "z \<notin> (\<Union>x. extend S C f x)"
      by blast
    then obtain n where "z = f n"
      using \<open>\<forall>y. \<exists>n. y = f n\<close> by blast
    
    from \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close> \<open>z = f n\<close> \<open>z \<in> S'\<close>
    have "extend S C f n \<union> {f n} \<subseteq> S'" by blast

    from \<open>finite_char C\<close>
    have "subset_closed C" using finite_char_closed by blast
    then have "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
      unfolding subset_closed_def by simp
    then have "\<forall>S\<subseteq>S'. S \<in> C"
      using \<open>S' \<in> C\<close> by blast
    then have "extend S C f n \<union> {f n} \<in> C"
      using \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close>
      by blast
    then have "z \<in> extend S C f (Suc n)"
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close> \<open>z = f n\<close>
      by simp
    then show False using * by blast
  qed
  ultimately show "(\<Union>x. extend S C f x) = S'"
    by simp
qed

subsection {* Hintikka sets and Herbrand models *}

text {*
\label{sec:hintikka}
A Hintikka set is defined as follows:
*}

definition
  hintikka :: "('a, 'b) form set \<Rightarrow> bool" where
  "hintikka H =
     ((\<forall>p ts. \<not> (Pred p ts \<in> H \<and> Neg (Pred p ts) \<in> H)) \<and>
     FF \<notin> H \<and> Neg TT \<notin> H \<and>
     (\<forall>Z. Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H) \<and>
     (\<forall>A B. And A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H) \<and>
     (\<forall>A B. Neg (Or A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H) \<and>
     (\<forall>A B. Or A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H) \<and>
     (\<forall>A B. Neg (And A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H) \<and>
     (\<forall>A B. Impl A B \<in> H \<longrightarrow> Neg A \<in> H \<or> B \<in> H) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> H \<longrightarrow> A \<in> H \<and> Neg B \<in> H) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> H \<longrightarrow> subst P t 0 \<in> H) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> H \<longrightarrow> Neg (subst P t 0) \<in> H) \<and>
     (\<forall>P. Exists P \<in> H \<longrightarrow> (\<exists>t. closedt 0 t \<and> subst P t 0 \<in> H)) \<and>
     (\<forall>P. Neg (Forall P) \<in> H \<longrightarrow> (\<exists>t. closedt 0 t \<and> Neg (subst P t 0) \<in> H)))"

text {*
In Herbrand models, each {\em closed} term is interpreted by itself.
We introduce a new datatype @{text hterm} (``Herbrand terms''), which
is similar to the datatype @{text term} introduced in \secref{sec:terms},
but without variables. We also define functions for converting between
closed terms and Herbrand terms.
*}

datatype 'a hterm = HApp 'a "'a hterm list"

primrec
  term_of_hterm :: "'a hterm \<Rightarrow> 'a term"
  and terms_of_hterms :: "'a hterm list \<Rightarrow> 'a term list"
where
  "term_of_hterm (HApp a hts) = App a (terms_of_hterms hts)"
| "terms_of_hterms [] = []"
| "terms_of_hterms (ht # hts) = term_of_hterm ht # terms_of_hterms hts"

theorem herbrand_evalt [simp]:
  "closedt 0 t \<Longrightarrow> term_of_hterm (evalt e HApp t) = t"
  "closedts 0 ts \<Longrightarrow> terms_of_hterms (evalts e HApp ts) = ts"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem herbrand_evalt' [simp]:
  "evalt e HApp (term_of_hterm ht) = ht"
  "evalts e HApp (terms_of_hterms hts) = hts"
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

theorem closed_hterm [simp]:
  "closedt 0 (term_of_hterm (ht::'a hterm))"
  "closedts 0 (terms_of_hterms (hts::'a hterm list))"
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

text {*
We can prove that Hintikka sets are satisfiable in Herbrand models.
Note that this theorem cannot be proved by a simple structural induction
(as claimed in Fitting's book), since a parameter substitution has
to be applied in the cases for quantifiers. However, since parameter
substitution does not change the size of formulae, the theorem can
be proved by well-founded induction on the size of the formula @{text p}.
*}
  
(* TODO: look at the need for measure size_form, wf_induct
  consider showing each conjunct separately
*)

theorem hintikka_model:
  assumes hin: "hintikka H"
  shows "(p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) p) \<and>
  (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg p))"
  using hin unfolding hintikka_def
proof (rule_tac r="measure size_form" and a=p in wf_induct)
  show "wf (measure size_form)"
    by blast
next
  fix x
  assume wf: "\<forall>y. (y, x) \<in> measure size_form \<longrightarrow>
             (y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) y) \<and>
             (Neg y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg y))"
    
  let ?pos = "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) x"
  let ?neg = "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg x)"
    
  show "(x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?pos) \<and>
         (Neg x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?neg)"
  proof (cases x)
    case FF
    show ?thesis proof (intro conjI impI)
      assume "x \<in> H"
      then show ?pos using FF hin by (simp add: hintikka_def)
    next
      assume "Neg x \<in> H"
      then show ?neg using FF by simp
    qed
  next
    case TT
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H"
      then show ?pos using TT by simp
    next
      assume "Neg x \<in> H"
      then show ?neg using TT hin by (simp add: hintikka_def)
    qed
  next
    case (Pred p ts)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then show ?pos using Pred by simp
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Pred p ts) \<in> H" and "closed 0 (Pred p ts)"
        using Pred by simp_all
      then have "Pred p ts \<notin> H"
        using hin unfolding hintikka_def by fast
      then show ?neg
        using Pred \<open>closed 0 (Pred p ts)\<close> by simp
    qed   
  next
    case (And A B)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then have "And A B \<in> H" and "closed 0 (And A B)"
        using And by simp_all
      then have "A \<in> H \<and> B \<in> H"
        using And hin unfolding hintikka_def by blast
      then show ?pos
        using And wf \<open>closed 0 (And A B)\<close> by simp 
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (And A B) \<in> H" and "closed 0 (And A B)"
        using And by simp_all
      then have "Neg A \<in> H \<or> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?neg
        using And wf \<open>closed 0 (And A B)\<close> by fastforce
    qed
  next
    case (Or A B)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then have "Or A B \<in> H" and "closed 0 (Or A B)"
        using Or by simp_all
      then have "A \<in> H \<or> B \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?pos
        using Or wf \<open>closed 0 (Or A B)\<close> by fastforce
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Or A B) \<in> H" and "closed 0 (Or A B)"
        using Or by simp_all
      then have "Neg A \<in> H \<and> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?neg
        using Or wf \<open>closed 0 (Or A B)\<close> by simp
    qed   
  next
    case (Impl A B)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then have "Impl A B \<in> H" and "closed 0 (Impl A B)"
        using Impl by simp_all
      then have "Neg A \<in> H \<or> B \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?pos
        using Impl wf \<open>closed 0 (Impl A B)\<close> by fastforce
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Impl A B) \<in> H" and "closed 0 (Impl A B)"
        using Impl by simp_all
      then have "A \<in> H \<and> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?neg
        using Impl wf \<open>closed 0 (Impl A B)\<close> by simp
    qed
  next
    case (Neg Z)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then show ?pos using Neg wf by simp
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Neg Z) \<in> H" and "closed 0 (Neg (Neg Z))"
        using Neg by simp_all
      then have "Z \<in> H"
        using hin unfolding hintikka_def by blast
      then show ?neg
        using Neg wf \<open>closed 0 (Neg (Neg Z))\<close> by simp
    qed
  next
    case (Forall P)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      have "\<forall>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
      proof (rule allI)
        fix z
        from \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
        have "Forall P \<in> H" and "closed 0 (Forall P)"
          using Forall by simp_all
        then have *: "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> H \<longrightarrow> P[t/0] \<in> H"
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Forall P)\<close>
        have "closed (Suc 0) P" by simp
            
        have "(P[term_of_hterm z/0], Forall P) \<in> measure size_form \<longrightarrow>
              (P[term_of_hterm z/0] \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (P[term_of_hterm z/0]))"
          using Forall wf by blast
        then show "eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
          using * \<open>Forall P \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show ?pos using Forall by simp
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Forall P) \<in> H"
        using Forall by simp
      then have "\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> H"
        using Forall hin unfolding hintikka_def by blast  
      then obtain t where *: "closedt 0 t \<and> Neg (P[t/0]) \<in> H"
        by blast
      then have "closed 0 (P[t/0])"
        using Forall \<open>closed 0 x\<close> by simp
          
      have "(subst P t 0, Forall P) \<in> measure size_form \<longrightarrow>
              (Neg (subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg (subst P t 0)))"
        using Forall wf by blast   
      then have "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg (P[t/0]))"
        using Forall * \<open>closed 0 (P[t/0])\<close> by simp
      then have "\<exists>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
        by auto
      then show ?neg using Forall by simp
    qed 
  next
    case (Exists P)
    then show ?thesis proof (intro conjI impI allI)
      assume "x \<in> H" and "closed 0 x"
      then have "\<exists>t. closedt 0 t \<and> (P[t/0]) \<in> H"
        using Exists hin unfolding hintikka_def by blast  
      then obtain t where *: "closedt 0 t \<and> (P[t/0]) \<in> H"
        by blast
      then have "closed 0 (P[t/0])"
        using Exists \<open>closed 0 x\<close> by simp
          
      have "(subst P t 0, Exists P) \<in> measure size_form \<longrightarrow>
              ((subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (subst P t 0))"
        using Exists wf by blast   
      then have "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (P[t/0])"
        using Exists * \<open>closed 0 (P[t/0])\<close> by simp
      then have "\<exists>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
        by auto
      then show ?pos using Exists by simp
    next
      assume "Neg x \<in> H" and "closed 0 x"
      have "\<forall>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
      proof (rule allI)
        fix z
        from \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
        have "Neg (Exists P) \<in> H" and "closed 0 (Neg (Exists P))"
          using Exists by simp_all
        then have *: "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> H \<longrightarrow> Neg (P[t/0]) \<in> H"
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Neg (Exists P))\<close>
        have "closed (Suc 0) P" by simp
            
        have "(P[term_of_hterm z/0], Exists P) \<in> measure size_form \<longrightarrow>
              (Neg (P[term_of_hterm z/0]) \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg (P[term_of_hterm z/0])))"
          using Exists wf by blast
        then show "\<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
          using * \<open>Neg (Exists P) \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show ?neg using Exists by simp
    qed
  qed
qed

text {*
Using the maximality of @{term "Extend S C f"}, we can show
that @{term "Extend S C f"} yields Hintikka sets:
*}

theorem extend_hintikka:
  assumes fin_ch: "finite_char C"
    and infin_p: "infinite (- (\<Union>p\<in>S. params p))"
    and surj: "\<forall>y. \<exists>n. y = f n"
    and altc: "alt_consistency C"
    and "S \<in> C"
  shows "hintikka (Extend S C f)"
proof -
  have "maximal (Extend S C f) C"
    by (simp add: extend_maximal fin_ch surj)

  have "Extend S C f \<in> C"
    using Extend_in_C assms by blast
      
  have "\<forall>S'\<in>C. Extend S C f \<subseteq> S' \<longrightarrow> Extend S C f = S'"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by blast
      
  have "(\<forall>p ts. \<not> (Pred p ts \<in> Extend S C f \<and> Neg (Pred p ts) \<in> Extend S C f))"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by fast
  
  moreover have "FF \<notin> Extend S C f"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by blast
 
  moreover have "Neg TT \<notin> Extend S C f"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by blast

  moreover have "\<forall>Z. Neg (Neg Z) \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {Z} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by fast
  then have "\<forall>Z. Neg (Neg Z) \<in> Extend S C f \<longrightarrow> Z \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
    
  moreover have "\<forall>A B. And A B \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {A, B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by simp
  then have "\<forall>A B. And A B \<in> Extend S C f \<longrightarrow> A \<in> Extend S C f \<and> B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
    
  moreover have "\<forall>A B. Neg (Or A B) \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {Neg A, Neg B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by fast
  then have "\<forall>A B. Neg (Or A B) \<in> Extend S C f \<longrightarrow> Neg A \<in> Extend S C f \<and> Neg B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
    
  moreover have "\<forall>A B. Or A B \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {A} \<in> C \<or> Extend S C f \<union> {B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by simp
  then have "\<forall>A B. Or A B \<in> Extend S C f \<longrightarrow> A \<in> Extend S C f \<or> B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
  
  moreover have "\<forall>A B. Neg (And A B) \<in> Extend S C f \<longrightarrow>
              Extend S C f \<union> {Neg A} \<in> C \<or> Extend S C f \<union> {Neg B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by simp
  then have "\<forall>A B. Neg (And A B) \<in> Extend S C f \<longrightarrow> Neg A \<in> Extend S C f \<or> Neg B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
  
  moreover have "\<forall>A B. Impl A B \<in> Extend S C f \<longrightarrow>
                       Extend S C f \<union> {Neg A} \<in> C \<or> Extend S C f \<union> {B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def by simp
  then have "\<forall>A B. Impl A B \<in> Extend S C f \<longrightarrow> Neg A \<in> Extend S C f \<or> B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
 
  moreover have "\<forall>A B. Neg (Impl A B) \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {A, Neg B} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def hintikka_def by simp
  then have "\<forall>A B. Neg (Impl A B) \<in> Extend S C f \<longrightarrow> A \<in> Extend S C f \<and> Neg B \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
 
  moreover have "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> Extend S C f \<longrightarrow> Extend S C f \<union> {P[t/0]} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def hintikka_def by simp
  then have "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> Extend S C f \<longrightarrow> P[t/0] \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
 
  moreover have "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> Extend S C f \<longrightarrow>
                       Extend S C f \<union> {Neg (P[t/0])} \<in> C"
    using \<open>Extend S C f \<in> C\<close> altc unfolding alt_consistency_def hintikka_def by simp
  then have "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> Extend S C f \<longrightarrow> Neg (P[t/0]) \<in> Extend S C f"
    using \<open>maximal (Extend S C f) C\<close> unfolding maximal_def by fast
 
  moreover have "\<forall>P. Exists P \<in> Extend S C f \<longrightarrow> (\<exists>t. closedt 0 t \<and> P[t/0] \<in> Extend S C f)"
  proof (intro allI impI)
    fix P
    obtain n where *: "Exists P = f n" using surj by blast
    assume "Exists P \<in> Extend S C f"
    then have "Exists P \<in> (\<Union>n. extend S C f n)"
      using Extend_def by blast
    then have "extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)"
      using * by (simp add: UN_upper)
    then have "extend S C f n \<union> {f n} \<in> C"
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    
    let ?t = "App (SOME k. k \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)) []"

    have "closedt 0 ?t" by simp

    have "P[?t/0] \<in> extend S C f (Suc n)"
      using * \<open>extend S C f n \<union> {f n} \<in> C\<close>
      by simp (metis (no_types, lifting) dest_Exists.simps)
    then have "P[?t/0] \<in> Extend S C f"
      using Extend_def by blast
    then show "\<exists>t. closedt 0 t \<and> P[t/0] \<in> Extend S C f"
      using \<open>closedt 0 ?t\<close> by blast
  qed
    
  moreover have "\<forall>P. Neg (Forall P) \<in> Extend S C f \<longrightarrow>
                     (\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> Extend S C f)"
  proof (intro allI impI)
    fix P
    obtain n where *: "Neg (Forall P) = f n" using surj by blast
    assume "Neg (Forall P) \<in> Extend S C f"
    then have "Neg (Forall P) \<in> (\<Union>n. extend S C f n)"
      using Extend_def by blast
    then have "extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)"
      using * by (simp add: UN_upper)
    then have "extend S C f n \<union> {f n} \<in> C"
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
      
    let ?t = "App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []"

    have "closedt 0 ?t" by simp

    from * \<open>extend S C f n \<union> {f n} \<in> C\<close>
    have "Neg (P[?t/0]) \<in> extend S C f (Suc n)"
      by simp (metis (no_types, lifting) dest_Forall.simps dest_Neg.simps form.distinct(69))     
    then have "Neg (P[?t/0]) \<in> Extend S C f"
      using Extend_def by blast
    then show "\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> Extend S C f"
      using \<open>closedt 0 ?t\<close> by blast
  qed

  ultimately show ?thesis
    unfolding hintikka_def by blast
qed


subsection {* Model existence theorem *}

text {*
\label{sec:model-existence}
Since the result of extending @{text S} is a superset of @{text S},
it follows that each consistent set @{text S} has a Herbrand model:
*}

theorem model_existence:
  assumes "consistency C"
    and "S \<in> C"
    and "infinite (- (\<Union>p \<in> S. params p))"
    and "p \<in> S"
    and "closed 0 p"
  shows "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend S
        (mk_finite_char (mk_alt_consistency (close C))) diag_form') p"
proof (rule hintikka_model [THEN conjunct1, THEN mp, THEN mp])
  have "finite_char (mk_finite_char (mk_alt_consistency (close C)))"
    by (simp add: finite_char)
  moreover have "closed 0 p \<Longrightarrow> infinite (- (\<Union>p\<in>S. params p))"
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> by blast
  moreover have "\<forall>y. y = diag_form' (undiag_form' y)"
    by simp
  then have "\<forall>y. \<exists>n. y = diag_form' n"
    by blast
  moreover have "alt_consistency (mk_finite_char (mk_alt_consistency (close C)))"
    using alt_consistency close_closed close_consistency
      \<open>consistency C\<close> finite_alt_consistency mk_alt_consistency_closed
    by blast
  moreover have "S \<in> close C"
    using close_subset \<open>S \<in> C\<close> by blast
  then have "S \<in> mk_alt_consistency (close C)"
    using mk_alt_consistency_subset by blast
  then have "S \<in> mk_finite_char (mk_alt_consistency (close C))"
    using close_closed finite_char_subset mk_alt_consistency_closed by blast
  ultimately show "hintikka (Extend S (mk_finite_char (mk_alt_consistency (close C))) diag_form')"
    using extend_hintikka \<open>infinite (- (\<Union>p \<in> S. params p))\<close> by blast
next
  show "p \<in> Extend S (mk_finite_char (mk_alt_consistency (close C))) diag_form'"
    using Extend_subset \<open>p \<in> S\<close> by blast
next
  show "closed 0 p"
    using \<open>closed 0 p\<close> by simp
qed


subsection {* Completeness for Natural Deduction *}

text {*
Thanks to the model existence theorem, we can now show the completeness
of the natural deduction calculus introduced in \secref{sec:proof-calculus}.
In order for the model existence theorem to be applicable, we have to prove
that the set of sets that are consistent with respect to @{text "\<turnstile>"} is a
consistency property:
*}

theorem deriv_consistency:
  assumes inf_param: "infinite (UNIV::'a set)"
  shows "consistency {S::('a, 'b) form set. \<exists>G. S = set G \<and> \<not> G \<turnstile> FF}"
  unfolding consistency_def
proof (clarsimp, intro conjI allI impI notI)
  fix G :: "('a, 'b) form list" and p ts
  assume "\<not> G \<turnstile> FF"
    and "Pred p ts \<in> set G" and "Neg (Pred p ts) \<in> set G"
  then have "G \<turnstile> Neg (Pred p ts)" and "G \<turnstile> Pred p ts"
    using Assum by (blast, blast)
  then have "G \<turnstile> FF" using NegE by blast
  then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
next
  fix G :: "('a, 'b) form list"
  assume "\<not> G \<turnstile> FF" and "FF \<in> set G"
  then have "G \<turnstile> FF" using Assum by blast
  then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
next
  fix G :: "('a, 'b) form list"
  assume "\<not> G \<turnstile> FF" and "Neg TT \<in> set G"
  then have "G \<turnstile> Neg TT" using Assum by blast
  moreover have "G \<turnstile> TT" using TTI by blast
  ultimately have "G \<turnstile> FF" using NegE by blast
  then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
next
  fix G :: "('a, 'b) form list" and Z
  assume "\<not> G \<turnstile> FF" and "Neg (Neg Z) \<in> set G"

  then have "G \<turnstile> Neg (Neg Z)"
    using Assum by blast
    
  have "{Z} \<union> set G = set (Z # G)"
    by simp
  moreover have "\<not> Z # G \<turnstile> FF"
  proof
    assume "Z # G \<turnstile> FF"
    then have "G \<turnstile> Neg Z" using NegI by blast
    then have "G \<turnstile> FF" using NegE \<open>G \<turnstile> Neg (Neg Z)\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert Z (set G) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "And A B \<in> set G"
    
  then have "G \<turnstile> And A B"
    using Assum by blast
  then have "G \<turnstile> A" and "G \<turnstile> B"
    using AndE1 AndE2 by blast+

  have "{A, B} \<union> set G = set (A # B # G)"
    by simp
  moreover have "\<not> A # B # G \<turnstile> FF"
  proof
    assume "A # B # G \<turnstile> FF"
    then have "B # G \<turnstile> Neg A" using NegI by blast
    then have "G \<turnstile> Neg A" using cut' \<open>G \<turnstile> B\<close> by blast
    then have "G \<turnstile> FF" using NegE \<open>G \<turnstile> A\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert A (insert B (set G)) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "Neg (Or A B) \<in> set G"
  
  have "A \<in> set (A # Neg B # G)" by simp
  then have "A # Neg B # G \<turnstile> A" using Assum by blast
  then have "A # Neg B # G \<turnstile> Or A B" using OrI1 by blast
  moreover have "A # Neg B # G \<turnstile> Neg (Or A B)"
    by (simp add: Assum \<open>Neg (Or A B) \<in> set G\<close>)
  ultimately have "A # Neg B # G \<turnstile> FF"
    using NegE \<open>A # Neg B # G \<turnstile> Neg (Or A B)\<close> by blast
  then have "Neg B # G \<turnstile> Neg A" using NegI by blast
             
  have "B \<in> set (B # G)" by simp
  then have "B # G \<turnstile> B" using Assum by blast
  then have "B # G \<turnstile> Or A B" using OrI2 by blast
  moreover have "B # G \<turnstile> Neg (Or A B)"
    by (simp add: Assum \<open>Neg (Or A B) \<in> set G\<close>)
  ultimately have "B # G \<turnstile> FF"
    using NegE \<open>B # G \<turnstile> Neg (Or A B)\<close> by blast
  then have "G \<turnstile> Neg B" using NegI by blast

  have "{Neg A, Neg B} \<union> set G = set (Neg A # Neg B # G)"
    by simp
  moreover have "\<not> Neg A # Neg B # G \<turnstile> FF"
  proof
    assume "Neg A # Neg B # G \<turnstile> FF"
    then have "Neg B # G \<turnstile> Neg (Neg A)"
      using NegI by blast
    then have "Neg B # G \<turnstile> FF"
      using NegE \<open>Neg B # G \<turnstile> Neg A\<close> by blast
    then have "G \<turnstile> FF"
      using cut' \<open>G \<turnstile> Neg B\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert (Neg A) (insert (Neg B) (set G)) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "Or A B \<in> set G"
  
  then have "G \<turnstile> Or A B"
    using Assum by blast
    
  show "(\<exists>G'. insert A (set G) = set G' \<and> \<not> G' \<turnstile> FF) \<or>
        (\<exists>G'. insert B (set G) = set G' \<and> \<not> G' \<turnstile> FF)"
  proof (rule ccontr, simp)
    assume "(\<forall>G'. insert A (set G) = set G' \<longrightarrow> G' \<turnstile> FF) \<and>
            (\<forall>G'. insert B (set G) = set G' \<longrightarrow> G' \<turnstile> FF)"
    then have "A # G \<turnstile> FF" and "B # G \<turnstile> FF"
      by simp_all
    then have "G \<turnstile> FF"
      using OrE \<open>G \<turnstile> Or A B\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "Neg (And A B) \<in> set G"
   
  have  "B # A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> A"
    and "B # A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> B"
    by (simp_all add: Assum)
  then have "B # A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> And A B"
    using AndI by blast
  moreover have "B # A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> Neg (And A B)"
    by (simp add: Assum \<open>Neg (And A B) \<in> set G\<close>)
  ultimately have "B # A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> FF"
    using NegE by blast
  then have "A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> Neg B"
    using NegI by blast
  then have "A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> Or (Neg A) (Neg B)"
    using OrI2 by blast
  moreover have "A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> Neg (Or (Neg A) (Neg B))"
    by (simp add: Assum)
  ultimately have "A # Neg (Or (Neg A) (Neg B)) # G \<turnstile> FF"
    using NegE by blast
  then have "Neg (Or (Neg A) (Neg B)) # G \<turnstile> Neg A"
    using NegI by blast
  then have "Neg (Or (Neg A) (Neg B)) # G \<turnstile> Or (Neg A) (Neg B)"
    using OrI1 by blast
  then have "G \<turnstile> Or (Neg A) (Neg B)"
    using Class' by blast
    
  show "(\<exists>G'. insert (Neg A) (set G) = set G' \<and> \<not> G' \<turnstile> FF) \<or>
        (\<exists>G'. insert (Neg B) (set G) = set G' \<and> \<not> G' \<turnstile> FF)"
  proof (rule ccontr, simp)
    assume "(\<forall>G'. insert (Neg A) (set G) = set G' \<longrightarrow> G' \<turnstile> FF) \<and>
            (\<forall>G'. insert (Neg B) (set G) = set G' \<longrightarrow> G' \<turnstile> FF)"
    then have "Neg A # G \<turnstile> FF" and "Neg B # G \<turnstile> FF"
      by simp_all
    then have "G \<turnstile> FF"
      using OrE \<open>G \<turnstile> Or (Neg A) (Neg B)\<close> by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "Impl A B \<in> set G"
      
  have "A # Neg (Or (Neg A) B) # G \<turnstile> A"
    by (simp add: Assum)
  moreover have "A # Neg (Or (Neg A) B) # G \<turnstile> Impl A B"
    by (simp add: Assum \<open>Impl A B \<in> set G\<close>)
  ultimately have "A # Neg (Or (Neg A) B) # G \<turnstile> B"
    using ImplE by blast
  then have "A # Neg (Or (Neg A) B) # G \<turnstile> Or (Neg A) B"
    using OrI2 by blast
  moreover have "A # Neg (Or (Neg A) B) # G \<turnstile> Neg (Or (Neg A) B)"
    by (simp add: Assum)
  ultimately have "A # Neg (Or (Neg A) B) # G \<turnstile> FF"
    using NegE by blast
  then have "Neg (Or (Neg A) B) # G \<turnstile> Neg A"
    using NegI by blast
  then have "Neg (Or (Neg A) B) # G \<turnstile> Or (Neg A) B"
    using OrI1 by blast
  then have "G \<turnstile> Or (Neg A) B"
    using Class' by blast
   
  show "(\<exists>G'. insert (Neg A) (set G) = set G' \<and> \<not> G' \<turnstile> FF) \<or>
        (\<exists>G'. insert B       (set G) = set G' \<and> \<not> G' \<turnstile> FF)"
  proof (rule ccontr, simp)
    assume "(\<forall>G'. insert (Neg A) (set G) = set G' \<longrightarrow> G' \<turnstile> FF) \<and>
            (\<forall>G'. insert B (set G) = set G' \<longrightarrow> G' \<turnstile> FF)"
    then have "Neg A # G \<turnstile> FF" and "B # G \<turnstile> FF"
      by simp_all
    then have "G \<turnstile> FF"
      using OrE \<open>G \<turnstile> Or (Neg A) B\<close> by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
next
  fix G :: "('a, 'b) form list" and A B
  assume "\<not> G \<turnstile> FF" and "Neg (Impl A B) \<in> set G"
         
  have "A # Neg A # Neg B # G \<turnstile> A" by (simp add: Assum)
  moreover have "A # Neg A # Neg B # G \<turnstile> Neg A" by (simp add: Assum)
  ultimately have "A # Neg A # Neg B # G \<turnstile> FF" using NegE by blast
  then have "A # Neg A # Neg B # G \<turnstile> B" using FFE by blast
  then have "Neg A # Neg B # G \<turnstile> Impl A B" using ImplI by blast
  moreover have "Neg A # Neg B # G \<turnstile> Neg (Impl A B)"
    by (simp add: Assum \<open>Neg (Impl A B) \<in> set G\<close>)
  ultimately have "Neg A # Neg B # G \<turnstile> FF" using NegE by blast
  then have "Neg B # G \<turnstile> A" using Class by blast
  
  have "A # B # G \<turnstile> B" by (simp add: Assum)
  then have "B # G \<turnstile> Impl A B" using ImplI by blast
  moreover have "B # G \<turnstile> Neg (Impl A B)"
    by (simp add: Assum \<open>Neg (Impl A B) \<in> set G\<close>)
  ultimately have "B # G \<turnstile> FF" using NegE by blast
  then have "G \<turnstile> Neg B" using NegI by blast
      
  have "{A, Neg B} \<union> set G = set (A # Neg B # G)"
    by simp
  moreover have "\<not> A # Neg B # G \<turnstile> FF"
  proof
    assume "A # Neg B # G \<turnstile> FF"
    then have "Neg B # G \<turnstile> Neg A"
      using NegI by blast
    then have "Neg B # G \<turnstile> FF"
      using NegE \<open>Neg B # G \<turnstile> A\<close> by blast
    then have "G \<turnstile> FF"
      using cut' \<open>G \<turnstile> Neg B\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert A (insert (Neg B) (set G)) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and P and t :: "'a term" 
  assume "\<not> G \<turnstile> FF" and "closedt 0 t" and "Forall P \<in> set G"
  
  then have "G \<turnstile> Forall P" using Assum by blast
  then have "G \<turnstile> P[t/0]" using ForallE by blast
  
  have "{P[t/0]} \<union> (set G) = set (P[t/0] # G)" by simp
  moreover have "\<not> P[t/0] # G \<turnstile> FF"
  proof
    assume "P[t/0] # G \<turnstile> FF"
    then have "G \<turnstile> FF" using cut' \<open>G \<turnstile> P[t/0]\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert (P[t/0]) (set G) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and P and t :: "'a term" 
  assume "\<not> G \<turnstile> FF" and "closedt 0 t" and "Neg (Exists P) \<in> set G"
 
  then have "P[t/0] \<in> set (P[t/0] # G)" by (simp add: Assum)
  then have "P[t/0] # G \<turnstile> P[t/0]" using Assum by blast
  then have "P[t/0] # G \<turnstile> Exists P" using ExistsI by blast
  moreover have "P[t/0] # G \<turnstile> Neg (Exists P)"
    by (simp add: Assum \<open>Neg (Exists P) \<in> set G\<close>)
  ultimately have "P[t/0] # G \<turnstile> FF" using NegE by blast
  then have "G \<turnstile> Neg (P[t/0])" using NegI by blast
    
  have "{Neg (P[t/0])} \<union> (set G) = set (Neg (P[t/0]) # G)" by simp
  moreover have "\<not> (Neg (P[t/0])) # G \<turnstile> FF"
  proof
    assume "Neg (P[t/0]) # G \<turnstile> FF"
    then have "G \<turnstile> FF" using cut' \<open>G \<turnstile> Neg (P[t/0])\<close> by blast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>G'. insert (Neg (P[t/0])) (set G) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and P
  assume "\<not> G \<turnstile> FF" and "Exists P \<in> set G"
  
  then have "G \<turnstile> Exists P" using Assum by blast
 
  have "finite (UNION (set G) params \<union> params P)" by simp
  then have "infinite (UNIV - (UNION (set G) params \<union> params P))"
    using inf_param Diff_infinite_finite by blast
  then have "infinite (- ((\<Union>p\<in>set G. params p) \<union> params P))"
    by (simp add: Compl_eq_Diff_UNIV)
  then obtain x where *: "x \<in> - ((\<Union>p\<in>set G. params p) \<union> params P)"
    using infinite_imp_nonempty by blast
  
  have "{P[App x []/0]} \<union> (set G) = set (P[App x []/0] # G)"
    by simp
  moreover have "\<not> P[App x []/0] # G \<turnstile> FF"
  proof
    assume "P[App x []/0] # G \<turnstile> FF"
    moreover note \<open>G \<turnstile> Exists P\<close>
    moreover have "list_all (\<lambda>p. x \<notin> params p) G"
      using * by (simp add: list_all_iff)
    moreover have "x \<notin> params P"
      using * by simp
    moreover have "x \<notin> params FF"
      by simp
    ultimately have "G \<turnstile> FF"
      using ExistsE by fast
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>x G'. insert (P[App x []/0]) (set G) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
next
  fix G :: "('a, 'b) form list" and P
  assume "\<not> G \<turnstile> FF" and "Neg (Forall P) \<in> set G"
  
  then have "G \<turnstile> Neg (Forall P)" using Assum by blast
 
  have "finite (UNION (set G) params \<union> params P)" by simp
  then have "infinite (UNIV - (UNION (set G) params \<union> params P))"
    using inf_param Diff_infinite_finite by blast
  then have "infinite (- ((\<Union>p\<in>set G. params p) \<union> params P))"
    by (simp add: Compl_eq_Diff_UNIV)
  then obtain x where *: "x \<in> - ((\<Union>p\<in>set G. params p) \<union> params P)"
    using infinite_imp_nonempty by blast
      
  have "Neg (P[App x []/0]) # Neg (Exists (Neg P)) # G \<turnstile> Neg P[App x []/0]"
    by (simp add: Assum)
  then have "Neg (P[App x []/0]) # Neg (Exists (Neg P)) # G \<turnstile> Exists (Neg P)"
    using ExistsI by blast
  moreover have "Neg (P[App x []/0]) # Neg (Exists (Neg P)) # G \<turnstile> Neg (Exists (Neg P))"
    by (simp add: Assum)
  ultimately have "Neg (P[App x []/0]) # Neg (Exists (Neg P)) # G \<turnstile> FF"
    using NegE by blast
  then have "Neg (Exists (Neg P)) # G \<turnstile> P[App x []/0]"
    using Class by blast
  moreover have "list_all (\<lambda>p. x \<notin> params p) (Neg (Exists (Neg P)) # G)"
    using * by (simp add: list_all_iff)
  moreover have "x \<notin> params P"
    using * by simp
  ultimately have "Neg (Exists (Neg P)) # G \<turnstile> Forall P"
    using ForallI by fast
  moreover have "Neg (Exists (Neg P)) # G \<turnstile> Neg (Forall P)"
    by (simp add: Assum \<open>Neg (Forall P) \<in> set G\<close>)
  ultimately have "Neg (Exists (Neg P)) # G \<turnstile> FF"
    using NegE by blast
  then have "G \<turnstile> Exists (Neg P)"
    using Class by blast
      
  have "{Neg (P[App x []/0])} \<union> (set G) = set (Neg (P[App x []/0]) # G)"
    by simp
  moreover have "\<not> Neg (P[App x []/0]) # G \<turnstile> FF"
  proof
    assume "Neg (P[App x []/0]) # G \<turnstile> FF"
    moreover note \<open>G \<turnstile> Exists (Neg P)\<close>
    moreover have "list_all (\<lambda>p. x \<notin> params p) G"
      using * by (simp add: list_all_iff)
    moreover have "x \<notin> params (Neg P)"
      using * by simp
    moreover have "x \<notin> params FF"
      by simp
    ultimately have "G \<turnstile> FF"
      using ExistsE by fastforce
    then show False using \<open>\<not> G \<turnstile> FF\<close> by blast
  qed
  ultimately show "\<exists>x G'. insert (Neg (P[App x []/0])) (set G) = set G' \<and> \<not> G' \<turnstile> FF"
    by blast
qed

text {*
Hence, by contradiction, we have completeness of natural deduction:
*}
      
theorem natded_complete:
  assumes "closed 0 p"
    and "list_all (closed 0) ps"
    and mod: "\<forall>e f g. e,(f :: nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm),(g :: nat \<Rightarrow> nat hterm list \<Rightarrow> bool),ps \<Turnstile> p"
  shows "ps \<turnstile> p"
proof (rule Class, rule ccontr)
  fix e
  assume "\<not> Neg p # ps \<turnstile> FF"
    
  let ?S = "set (Neg p # ps)"
  let ?C = "{set (G :: (nat, nat) form list) | G. \<not> G \<turnstile> FF}"
  let ?f = HApp
  let ?g = "(\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend ?S
              (mk_finite_char (mk_alt_consistency (close ?C))) diag_form')"

  from \<open>list_all (closed 0) ps\<close>
  have "Ball (set ps) (closed 0)"
    by (simp add: Ball_set_list_all)
      
  have "list_all (eval e ?f ?g) (Neg p # ps)"
  proof (simp only: list_all_iff, intro exI ballI)
    fix x
    assume "x \<in> ?S"
    moreover have "consistency ?C"
      using deriv_consistency by blast
    moreover have "?S \<in> ?C"
      using \<open>\<not> Neg p # ps \<turnstile> FF\<close> by blast
    moreover have "infinite (- (\<Union>p\<in>?S. params p))"
      by (simp add: Compl_eq_Diff_UNIV)
    moreover note \<open>closed 0 p\<close> \<open>Ball (set ps) (closed 0)\<close> \<open>x \<in> ?S\<close>
    then have \<open>closed 0 x\<close> by auto
    ultimately show "eval e ?f ?g x"
      using model_existence by simp
  qed
  moreover have "eval e ?f ?g (Neg p)"
    using calculation by simp 
  moreover have "list_all (eval e ?f ?g) ps"
    using calculation by simp
  then have "eval e ?f ?g p"
    using mod unfolding model_def by blast
  ultimately show False by simp
qed

section {* L\"owenheim-Skolem theorem *}

text {*
Another application of the model existence theorem presented in \secref{sec:model-existence}
is the L\"owenheim-Skolem theorem. It says that a set of formulae that is satisfiable in an
{\em arbitrary model} is also satisfiable in a {\em Herbrand model}. The main idea behind the
proof is to show that satisfiable sets are consistent, hence they must be satisfiable in a
Herbrand model.
*}

theorem sat_consistency: "consistency {S. \<not> finite (- (\<Union>p\<in>S. params p)) \<and>
  (\<exists>f. \<forall>(p::('a, 'b)form)\<in>S. eval e f g p)}"
  unfolding consistency_def
proof (intro allI impI, elim CollectE conjE, intro conjI)
  fix S :: "('a, 'b) form set"
          
  let ?C = "{S. infinite (- UNION S params) \<and> (\<exists>f. Ball S (eval e f g))}"
 
  assume inf_params: "infinite (- UNION S params)"
    and "\<exists>f. Ball S (eval e f g)"
  then obtain f where *: "Ball S (eval e f g)" by blast

  show "\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
  proof (intro allI notI)
    fix p ts
    assume "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
    then have "eval e f g (Pred p ts) \<and> eval e f g (Neg (Pred p ts))"
      using * by blast
    then show False by simp
  qed
    
  show "FF \<notin> S"
    using * by fastforce
      
  show "Neg TT \<notin> S"
    using * by fastforce
   
  show "\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> ?C"
  proof (intro allI impI)
    fix Z
    assume "Neg (Neg Z) \<in> S"
    then have "Ball (S \<union> {Neg (Neg Z)}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {Z}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {Z}) params)"
      using inf_params by simp
    ultimately show "S \<union> {Z} \<in> ?C"
      by blast
  qed
    
  show "\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "And A B \<in> S"
    then have "Ball (S \<union> {And A B}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {A, B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {A, B}) params)"
      using inf_params by simp
    ultimately show "S \<union> {A, B} \<in> ?C"
      by blast
  qed
    
  show "\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "Neg (Or A B) \<in> S"
    then have "Ball (S \<union> {Neg (Or A B)}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {Neg A, Neg B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {Neg A, Neg B}) params)"
      using inf_params by simp
    ultimately show "S \<union> {Neg A, Neg B} \<in> ?C"
      by blast
  qed
      
  show "\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "Or A B \<in> S"
       then have "Ball (S \<union> {Or A B}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {A}) (eval e f g) \<or> Ball (S \<union> {B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {A}) params)"
      and "infinite (- UNION (S \<union> {B}) params)"
      using inf_params by simp_all
    ultimately show "S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast
  qed
    
  show "\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "Neg (And A B) \<in> S"
       then have "Ball (S \<union> {Neg (And A B)}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {Neg A}) (eval e f g) \<or> Ball (S \<union> {Neg B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {Neg A}) params)"
      and "infinite (- UNION (S \<union> {Neg B}) params)"
      using inf_params by simp_all
    ultimately show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C"
      by blast
  qed
    
  show "\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "Impl A B \<in> S"
       then have "Ball (S \<union> {Impl A B}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {Neg A}) (eval e f g) \<or> Ball (S \<union> {B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {Neg A}) params)"
      and "infinite (- UNION (S \<union> {B}) params)"
      using inf_params by simp_all
    ultimately show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast
  qed
    
  show "\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> ?C"
  proof (intro allI impI)
    fix A B
    assume "Neg (Impl A B) \<in> S"
    then have "Ball (S \<union> {Neg (Impl A B)}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {A, Neg B}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {A, Neg B}) params)"
      using inf_params by simp
    ultimately show "S \<union> {A, Neg B} \<in> ?C"
      by blast
  qed
    
  show "\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> ?C"
  proof (intro allI impI)
    fix P and t :: "'a term"
    assume "Forall P \<in> S"
    then have "Ball (S \<union> {Forall P}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {P[t/0]}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {P[t/0]}) params)"
      using inf_params by simp
    ultimately show "S \<union> {P[t/0]} \<in> ?C"
      by blast
  qed
    
  show "\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> ?C"
  proof (intro allI impI)
    fix P and t :: "'a term"
    assume "Neg (Exists P) \<in> S"
    then have "Ball (S \<union> {Neg (Exists P)}) (eval e f g)"
      using * by blast
    then have "Ball (S \<union> {Neg (P[t/0])}) (eval e f g)"
      by simp
    moreover have "infinite (- UNION (S \<union> {Neg (P[t/0])}) params)"
      using inf_params by simp
    ultimately show "S \<union> {Neg (P[t/0])} \<in> ?C"
      by blast
  qed
    
  show "\<forall>P. Exists P \<in> S \<longrightarrow> (\<exists>x. S \<union> {P[App x []/0]} \<in> ?C)"
  proof (intro allI impI)
    fix P
    assume "Exists P \<in> S"
    then have "Ball (S \<union> {Exists P}) (eval e f g)"
      using * by blast
    then have "eval e f g (Exists P)"
      by blast
    then obtain z where "eval (e\<langle>0:z\<rangle>) f g P"
      by simp blast
    moreover obtain x where "x \<in> - UNION S params"
      using inf_params infinite_imp_nonempty by blast
    then have "x \<notin> params P"
      using \<open>Exists P \<in> S\<close> by auto
    ultimately have "eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P"
      by simp
    moreover have "Ball S (eval e (f(x := \<lambda>y. z)) g)"
      using * \<open>x \<in> - UNION S params\<close> by simp
    moreover have "infinite (- UNION (S \<union> {P[App x []/0]}) params)"
      using inf_params by simp
    ultimately have "S \<union> {P[App x []/0]} \<in> {S. infinite (- UNION S params) \<and>
                                               (Ball S (eval e (f(x := \<lambda>y. z)) g))}"
      by simp
    then show "\<exists>x. S \<union> {P[App x []/0]} \<in> ?C"
      by blast
  qed
    
  show "\<forall>P. Neg (Forall P) \<in> S \<longrightarrow> (\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C)"
  proof (intro allI impI)
    fix P
    assume "Neg (Forall P) \<in> S"
    then have "Ball (S \<union> {Neg (Forall P)}) (eval e f g)"
      using * by blast
    then have "eval e f g (Neg (Forall P))"
      by blast
    then obtain z where "\<not> eval (e\<langle>0:z\<rangle>) f g P"
      by simp blast
    moreover obtain x where "x \<in> - UNION S params"
      using inf_params infinite_imp_nonempty by blast
    then have "x \<notin> params P"
      using \<open>Neg (Forall P) \<in> S\<close> by auto
    ultimately have "\<not> eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P"
      by simp
    moreover have "Ball S (eval e (f(x := \<lambda>y. z)) g)"
      using * \<open>x \<in> - UNION S params\<close> by simp
    moreover have "infinite (- UNION (S \<union> {Neg (P[App x []/0])}) params)"
      using inf_params by simp
    ultimately have "S \<union> {Neg (P[App x []/0])} \<in> {S. infinite (- UNION S params) \<and>
                                               (Ball S (eval e (f(x := \<lambda>y. z)) g))}"
      by simp
    then show "\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C"
      by blast
  qed
qed

theorem doublep_evalt [simp]:
  "evalt e f (psubstt (\<lambda>n::nat. 2 * n) t) = evalt e (\<lambda>n. f (2*n)) t"
  "evalts e f (psubstts (\<lambda>n::nat. 2 * n) ts) = evalts e (\<lambda>n. f (2*n)) ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem doublep_eval: "\<And>e. eval e f g (psubst (\<lambda>n::nat. 2 * n) p) =
  eval e (\<lambda>n. f (2*n)) g p"
  by (induct p) simp_all

theorem doublep_infinite_params:
  "\<not> finite (- (\<Union>p \<in> psubst (\<lambda>n::nat. 2 * n) ` S. params p))"
proof (rule infinite_super)
  show "infinite (range (\<lambda>n::nat. 2 * n + 1))"
    using inj_onI Suc_1 Suc_mult_cancel1 add_right_imp_eq finite_imageD infinite_UNIV_char_0
    by (metis (no_types, lifting))
next
  have "\<And>m n. Suc (2 * m) \<noteq> 2 * n" by arith
  then show "range (\<lambda>n::nat. (2::nat) * n + (1::nat))
    \<subseteq> - (\<Union>p::(nat, 'a) form\<in>psubst (op * (2::nat)) ` S. params p)"
    by auto
qed

text {*
When applying the model existence theorem, there is a technical
complication. We must make sure that there are infinitely many
unused parameters. In order to achieve this, we encode parameters
as natural numbers and multiply each parameter occurring in the
set @{text S} by @{text 2}.
*}

theorem loewenheim_skolem: "\<forall>p\<in>S. eval e f g p \<Longrightarrow>
  \<forall>p\<in>S. closed 0 p \<longrightarrow> eval e' (\<lambda>n. HApp (2*n)) (\<lambda>a ts.
      Pred a (terms_of_hterms ts) \<in> Extend (psubst (\<lambda>n. 2 * n) ` S)
        (mk_finite_char (mk_alt_consistency (close
          {S. \<not> finite (- (\<Union>p\<in>S. params p)) \<and>
            (\<exists>f. \<forall>p\<in>S. eval e f g p)}))) diag_form') p"
  (is "\<forall>_\<in>_. _ _ _ _ _ \<Longrightarrow> \<forall>_\<in>_. _ _ _ \<longrightarrow> eval _ _ ?g _")
proof (intro ballI impI)
  fix p
  assume "\<forall>p\<in>S. eval e f g p"
    and "p \<in> S"
    and "closed 0 p"
  then have "eval e f g p"
    using \<open>\<forall>p\<in>S. eval e f g p\<close> \<open>p \<in> S\<close> by blast
  then have "Ball S (eval e f g)"
    using \<open>\<forall>p\<in>S. eval e f g p\<close> by blast
  then have "Ball (psubst (op * 2) ` S) (eval e (\<lambda>n. f (n div 2)) g)"
    by (simp add: doublep_eval)
  then have "psubst (op * 2) ` S \<in> {S. infinite (- UNION S params) \<and> (\<exists>f. Ball S (eval e f g))}"
    using doublep_infinite_params by blast
  moreover have "psubst (op * 2) p \<in> psubst (op * 2) ` S"
    using \<open>p \<in> S\<close> by blast
  moreover have "closed 0 (psubst (op * 2) p)"
    using \<open>closed 0 p\<close> by simp
  moreover have "consistency {S. infinite (- UNION S params) \<and> (\<exists>f. Ball S (eval e f g))}"
    using sat_consistency by blast
  ultimately have "eval e' HApp ?g (psubst (op * 2) p)"
    using model_existence by blast
  then show "eval e' (\<lambda>n. HApp (2 * n)) ?g p"
    using doublep_eval by blast
qed

end
