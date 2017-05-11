(* Authors: Stefan Berghofer, TU Muenchen, 2003 / Andreas Halkjær From, DTU Compute, 2017
*)

theory FOL_Berghofer
  imports
    Main
    "~~/src/HOL/Library/Countable"
begin


section {* Miscellaneous Utilities *}

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
| ForallE': "G \<turnstile> Forall a \<Longrightarrow> G \<turnstile> a"
| ExistsI: "G \<turnstile> a[t/0] \<Longrightarrow> G \<turnstile> Exists a"
| ExistsE: "G \<turnstile> Exists a \<Longrightarrow> a[App n []/0] # G \<turnstile> b \<Longrightarrow>
    list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow> n \<notin> params a \<Longrightarrow> n \<notin> params b \<Longrightarrow> G \<turnstile> b"
  
text {*
The following derived inference rules are sometimes useful in applications.
*}

theorem cut: "G \<turnstile> A \<Longrightarrow> A # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
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
    using cut \<open>Neg A # G \<turnstile> A\<close> by blast
  then show "G \<turnstile> A"
    using Class by blast
qed

theorem ForallE'': "G \<turnstile> Forall a \<Longrightarrow> subst a t 0 # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
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
  apply (rule_tac t="App 0 []" and a="Pred p [App (Suc 0) [], Var 0]" in ForallE'')
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
 
lemma remove_shift: "\<forall>e z. g a ((e\<langle>0:z\<rangle>) n) \<Longrightarrow> g a (e n)"
  by (induct n) auto

lemma evalts_shift:
  "\<forall>e (f :: 'b \<Rightarrow> 'a list \<Rightarrow> 'a) (g :: 'c \<Rightarrow> 'a list \<Rightarrow> bool) z.
    g a (evalts (e\<langle>0:z\<rangle>) f ts) \<Longrightarrow>
  (g :: 'c \<Rightarrow> 'a list \<Rightarrow> bool) a (evalts e (f :: 'b \<Rightarrow> 'a list \<Rightarrow> 'a) ts)"
  by meson
  
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
next
  case (ForallE' G a)
  then show ?case
    sorry
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
    using conc sc unfolding consistency_def by presburger+
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
    moreover have "psubst (f(x := y)) `
        S \<union> {psubst (f(x := y)) P[App ((f(x := y)) x) []/0]} \<in> C"
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
    moreover have "psubst (f(x := y)) `
    S \<union> {Neg (psubst (f(x := y)) P[App ((f(x := y)) x) []/0])} \<in> C"
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
    
lemma subset_in_close:
  assumes "S \<subseteq> S'"
  shows "S' \<union> x \<in> C \<longrightarrow> S \<union> x \<in> close C"
proof -
  have "S' \<union> x \<in> close C \<longrightarrow> S \<union> x \<in> close C"
    unfolding close_def using \<open>S \<subseteq> S'\<close> by blast
  then show ?thesis unfolding close_def by blast
qed

theorem close_consistency:
  assumes conc: "consistency C"
  shows "consistency (close C)"
  unfolding consistency_def
proof (intro allI impI conjI)
  fix S
  assume "S \<in> close C"
  then obtain x where "x \<in> C" and "S \<subseteq> x"
    unfolding close_def by blast

  { fix p ts
    have "\<not> (Pred p ts \<in> x \<and> Neg (Pred p ts) \<in> x)"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
      using \<open>S \<subseteq> x\<close> by blast }
  
  { have "FF \<notin> x"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "FF \<notin> S"
      using \<open>S \<subseteq> x\<close> by blast }
    
  { have "Neg TT \<notin> x"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "Neg TT \<notin> S"
      using \<open>S \<subseteq> x\<close> by blast }
    
  { fix Z
    assume "Neg (Neg Z) \<in> S"
    then have "Neg (Neg Z) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {Z} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {Z} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix A B
    assume "And A B \<in> S"
    then have "And A B \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {A, B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {A, B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix A B
    assume "Neg (Or A B) \<in> S"
    then have "Neg (Or A B) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {Neg A, Neg B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {Neg A, Neg B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume "Or A B \<in> S"
    then have "Or A B \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {A} \<in> C \<or> x \<union> {B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {A} \<in> close C \<or> S \<union> {B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix A B
    assume "Neg (And A B) \<in> S"
    then have "Neg (And A B) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {Neg A} \<in> C \<or> x \<union> {Neg B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {Neg A} \<in> close C \<or> S \<union> {Neg B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix A B
    assume "Impl A B \<in> S"
    then have "Impl A B \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {Neg A} \<in> C \<or> x \<union> {B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "S \<union> {Neg A} \<in> close C \<or> S \<union> {B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix A B
    assume "Neg (Impl A B) \<in> S"
    then have "Neg (Impl A B) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {A, Neg B} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "S \<union> {A, Neg B} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Forall P \<in> S"
    then have "Forall P \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {P[t/0]} \<in> C"
      using \<open>closedt 0 t\<close> \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "S \<union> {P[t/0]} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Neg (Exists P) \<in> S"
    then have "Neg (Exists P) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "x \<union> {Neg (P[t/0])} \<in> C"
      using \<open>closedt 0 t\<close> \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "S \<union> {Neg (P[t/0])} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix P
    assume "Exists P \<in> S"
    then have "Exists P \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "\<exists>c. x \<union> {P[App c []/0]} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show "\<exists>c. S \<union> {P[App c []/0]} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
    
  { fix P
    assume "Neg (Forall P) \<in> S"
    then have "Neg (Forall P) \<in> x"
      using \<open>S \<subseteq> x\<close> by blast
    then have "\<exists>c. x \<union> {Neg (P[App c []/0])} \<in> C"
      using \<open>x \<in> C\<close> conc unfolding consistency_def by presburger
    then show "\<exists>c. S \<union> {Neg (P[App c []/0])} \<in> close C"
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
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
  assumes "subset_closed C"
  shows "subset_closed (mk_alt_consistency C)"
  unfolding subset_closed_def mk_alt_consistency_def
proof (intro ballI allI impI)
  fix S S' :: "('a, 'b) form set"
  assume "S \<subseteq> S'" and "S' \<in> {S. \<exists>f. psubst f ` S \<in> C}"
  then obtain f where *: "psubst f ` S' \<in> C"
    by blast
  moreover have "psubst f ` S \<subseteq> psubst f ` S'"
    using \<open>S \<subseteq> S'\<close> by blast
  moreover have "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  ultimately have "psubst f ` S \<in> C"
    by blast
  then show "S \<in> {S. \<exists>f. psubst f ` S \<in> C}"
    by blast
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

theorem finite_alt_consistency:
  assumes altconc: "alt_consistency C"
    and "subset_closed C"
  shows "alt_consistency (mk_finite_char C)"
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix S
  assume "S \<in> mk_finite_char C"
  then have finc: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> C"
    unfolding mk_finite_char_def by blast
    
  have "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then have sc: "\<forall>S' x. S' \<union> x \<in> C \<longrightarrow> (\<forall>S \<subseteq> S' \<union> x. S \<in> C)"
    by blast
      
  { fix p ts
    show "\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
    proof
      assume "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
      then have "{Pred p ts, Neg (Pred p ts)} \<in> C"
        using finc by simp
      then show False
        using altconc unfolding alt_consistency_def by fast
    qed }
    
  show "FF \<notin> S"
  proof
    assume "FF \<in> S"
    then have "{FF} \<in> C"
      using finc by simp
    then show False
      using altconc unfolding alt_consistency_def by fast
  qed
  
  show "Neg TT \<notin> S"
  proof
    assume "Neg TT \<in> S"
    then have "{Neg TT} \<in> C"
      using finc by simp
    then show False
      using altconc unfolding alt_consistency_def by fast
  qed

  { fix Z
    assume *: "Neg (Neg Z) \<in> S"
    show "S \<union> {Z} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {Z} \<union> {Neg (Neg Z)}"
    
      assume "S' \<subseteq> S \<union> {Z}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {Z} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix A B
    assume *: "And A B \<in> S"
    show "S \<union> {A, B} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {A, B} \<union> {And A B}"
    
      assume "S' \<subseteq> S \<union> {A, B}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {A, B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix A B
    assume *: "Neg (Or A B) \<in> S"
    show "S \<union> {Neg A, Neg B} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {Neg A, Neg B} \<union> {Neg (Or A B)}"
    
      assume "S' \<subseteq> S \<union> {Neg A, Neg B}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {Neg A, Neg B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix A B
    assume *: "Neg (Impl A B) \<in> S"
    show "S \<union> {A, Neg B} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {A, Neg B} \<union> {Neg (Impl A B)}"
    
      assume "S' \<subseteq> S \<union> {A, Neg B}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {A, Neg B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix A B
    assume *: "Or A B \<in> S"
    show "S \<union> {A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain Sa and Sb
        where "Sa \<subseteq> S \<union> {A}" and "finite Sa" and "Sa \<notin> C"
          and "Sb \<subseteq> S \<union> {B}" and "finite Sb" and "Sb \<notin> C"
        unfolding mk_finite_char_def by blast
          
      let ?S' = "(Sa - {A}) \<union> (Sb - {B}) \<union> {Or A B}"
          
      have "?S' \<subseteq> S"
        using \<open>Sa \<subseteq> S \<union> {A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have "finite ?S'"
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {A} \<in> C \<or> ?S' \<union> {B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then have "Sa \<in> C \<or> Sb \<in> C"
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }
    
  { fix A B
    assume *: "Neg (And A B) \<in> S"
    show "S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {Neg B} \<in> mk_finite_char C"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain Sa and Sb
        where "Sa \<subseteq> S \<union> {Neg A}" and "finite Sa" and "Sa \<notin> C"
          and "Sb \<subseteq> S \<union> {Neg B}" and "finite Sb" and "Sb \<notin> C"
        unfolding mk_finite_char_def by blast
          
      let ?S' = "(Sa - {Neg A}) \<union> (Sb - {Neg B}) \<union> {Neg (And A B)}"
          
      have "?S' \<subseteq> S"
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {Neg B}\<close> * by blast
      moreover have "finite ?S'"
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {Neg B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then have "Sa \<in> C \<or> Sb \<in> C"
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }
    
  { fix A B
    assume *: "Impl A B \<in> S"
    show "S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain Sa and Sb
        where "Sa \<subseteq> S \<union> {Neg A}" and "finite Sa" and "Sa \<notin> C"
          and "Sb \<subseteq> S \<union> {B}" and "finite Sb" and "Sb \<notin> C"
        unfolding mk_finite_char_def by blast
          
      let ?S' = "(Sa - {Neg A}) \<union> (Sb - {B}) \<union> {Impl A B}"
          
      have "?S' \<subseteq> S"
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have "finite ?S'"
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {B} \<in> C"
        using altconc unfolding alt_consistency_def by simp
      then have "Sa \<in> C \<or> Sb \<in> C"
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }
    
    
  { fix P and t :: "'a term"
    assume *: "Forall P \<in> S" and "closedt 0 t"
    show "S \<union> {P[t/0]} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {P[t/0]} \<union> {Forall P}"
    
      assume "S' \<subseteq> S \<union> {P[t/0]}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {P[t/0]} \<in> C"
        using altconc \<open>closedt 0 t\<close> unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix P and t :: "'a term"
    assume *: "Neg (Exists P) \<in> S" and "closedt 0 t"
    show "S \<union> {Neg (P[t/0])} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {Neg (P[t/0])} \<union> {Neg (Exists P)}"
    
      assume "S' \<subseteq> S \<union> {Neg (P[t/0])}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      then have "?S' \<union> {Neg (P[t/0])} \<in> C"
        using altconc \<open>closedt 0 t\<close> unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix P x
    assume *: "Exists P \<in> S" and "\<forall>a\<in>S. x \<notin> params a"
    show "S \<union> {P[App x []/0]} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {P[App x []/0]} \<union> {Exists P}"
    
      assume "S' \<subseteq> S \<union> {P[App x []/0]}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      moreover have "\<forall>a\<in>?S'. x \<notin> params a"
        using \<open>\<forall>a\<in>S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have "?S' \<union> {P[App x []/0]} \<in> C"
        using altconc \<open>\<forall>a\<in>S. x \<notin> params a\<close> unfolding alt_consistency_def by blast
      then show "S' \<in> C"
        using sc by blast
    qed }
    
  { fix P x
    assume *: "Neg (Forall P) \<in> S" and "\<forall>a\<in>S. x \<notin> params a"
    show "S \<union> {Neg (P[App x []/0])} \<in> mk_finite_char C"
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = "S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)}"
    
      assume "S' \<subseteq> S \<union> {Neg (P[App x []/0])}" and "finite S'"
      then have "?S' \<subseteq> S"
        using * by blast
      moreover have "finite ?S'"
        using \<open>finite S'\<close> by blast
      ultimately have "?S' \<in> C"
        using finc by blast
      moreover have "\<forall>a\<in>?S'. x \<notin> params a"
        using \<open>\<forall>a\<in>S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have "?S' \<union> {Neg (P[App x []/0])} \<in> C"
        using altconc \<open>\<forall>a\<in>S. x \<notin> params a\<close> unfolding alt_consistency_def by simp
      then show "S' \<in> C"
        using sc by blast
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

theorem diag_undiag_form': "diag_form' (undiag_form' f) = f"
  by (simp add: diag_form'_def undiag_form'_def)


subsection {* Enumerating datatypes via countable *}

instantiation "term" :: (countable) countable begin
instance by countable_datatype
end
  
instantiation form :: (countable, countable) countable begin
instance by countable_datatype
end
    
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

theorem is_chainD':
  assumes "is_chain f" and "x \<in> f m" and "m \<le> k"
  shows "x \<in> f k"
proof -
  have "\<exists>n. k = m + n"
    using \<open>m \<le> k\<close> by presburger
  then obtain n where "k = m + n"
    by blast
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
  have "m \<le> max n m" and "n \<le> max n m"
    by simp_all
  have "x \<in> f (max n m)"
    using is_chainD' ch \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close> by fast
  moreover have "F \<subseteq> f (max n m)"
    using is_chainD' ch \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close> by fast
  moreover have "x \<in> f (max n m) \<and> F \<subseteq> f (max n m)"
    using calculation by blast
  ultimately show ?case by blast
qed

lemma chain_union_closed':
  assumes "is_chain f" and "(\<forall>n. f n \<in> C)" and "\<forall>S'\<in>C. \<forall>S\<subseteq>S'. S \<in> C"
    and "finite S'" and "S' \<subseteq> (\<Union>n. f n)"
  shows "S' \<in> C" 
proof -
  note \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  then obtain n where "S' \<subseteq> f n"
    using chain_index \<open>is_chain f\<close>  by blast
  moreover have "f n \<in> C"
    using \<open>\<forall>n. f n \<in> C\<close> by blast
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
  "infinite (\<Inter>p \<in> S. - params p) \<Longrightarrow> infinite (\<Inter>p \<in> extend S C f n. - params p)"
  by (induct n) simp_all
    
lemma infinite_params_available:
  assumes "infinite (- (\<Union>p \<in> S. params p))"
  shows "\<exists>x. x \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)"
proof -
  let ?S' = "extend S C f n \<union> {f n}"

  have "infinite (- (\<Union>x\<in>?S'. params x))"
    using assms by simp
  then obtain x where "x \<in> - (\<Union>x\<in>?S'. params x)"
    using infinite_imp_nonempty by blast   
  then have "\<forall>a\<in>?S'. x \<notin> params a"
    by blast
  then show ?thesis
    by blast
qed
    
lemma extend_in_C_Exists:
  assumes "alt_consistency C"
    and "infinite (- (\<Union>p \<in> S. params p))"
    and "extend S C f n \<union> {f n} \<in> C" (is "?S' \<in> C")
    and "\<exists>p. f n = Exists p"
  shows "extend S C f (Suc n) \<in> C"
proof -
  obtain p where *: "f n = Exists p"
    using \<open>\<exists>p. f n = Exists p\<close> by blast
  have "\<exists>x. x \<notin> (\<Union>p\<in>?S'. params p)"
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> infinite_params_available
    by blast
  moreover have "Exists p \<in> ?S'"
    using * by simp
  then have "\<forall>x. x \<notin> (\<Union>p\<in>?S'. params p) \<longrightarrow> ?S' \<union> {p[App x []/0]} \<in> C"
    using \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close>
    unfolding alt_consistency_def by simp
  ultimately have "(?S' \<union> {p[App (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []/0]}) \<in> C"
    by (metis (mono_tags, lifting) someI2)
  then show ?thesis
    using assms * by simp
qed
    
lemma extend_in_C_Neg_Forall:
  assumes "alt_consistency C"
    and "infinite (- (\<Union>p \<in> S. params p))"
    and "extend S C f n \<union> {f n} \<in> C" (is "?S' \<in> C")
    and "\<forall>p. f n \<noteq> Exists p"
    and "\<exists>p. f n = Neg (Forall p)"
  shows "extend S C f (Suc n) \<in> C"
  proof -
  obtain p where *: "f n = Neg (Forall p)"
    using \<open>\<exists>p. f n = Neg (Forall p)\<close> by blast
  have "\<exists>x. x \<notin> (\<Union>p\<in>?S'. params p)"
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> infinite_params_available
    by blast
  moreover have "Neg (Forall p) \<in> ?S'"
    using * by simp
  then have "\<forall>x. x \<notin> (\<Union>p\<in>?S'. params p) \<longrightarrow> ?S' \<union> {Neg (p[App x []/0])} \<in> C"
    using \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close>
    unfolding alt_consistency_def by simp
  ultimately have "(?S' \<union> {Neg (p[App (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []/0])}) \<in> C"
    by (metis (mono_tags, lifting) someI2)
  then show ?thesis
    using assms * by simp
qed
    
lemma extend_in_C_no_delta:
  assumes "extend S C f n \<union> {f n} \<in> C"
    and "\<forall>p. f n \<noteq> Exists p"
    and "\<forall>p. f n \<noteq> Neg (Forall p)"
  shows "extend S C f (Suc n) \<in> C"
  using assms by simp
    
lemma extend_in_C_stop:
  assumes "extend S C f n \<in> C"
    and "extend S C f n \<union> {f n} \<notin> C"
  shows "extend S C f (Suc n) \<in> C"
  using assms by simp

theorem extend_in_C: "alt_consistency C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case
      using extend_in_C_Exists extend_in_C_Neg_Forall
        extend_in_C_no_delta extend_in_C_stop
      by metis
  qed

text {*
The main theorem about @{text Extend} says that if @{text C} is an
alternative consistency property that is of finite character,
@{text S} is consistent and @{text S} uses only finitely many
parameters, then @{text "Extend S C f"} is again consistent.
*}

theorem Extend_in_C: "alt_consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C"
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
  assumes "\<forall>y. \<exists>n. y = f n"
    and "finite_char C"
  shows "maximal (Extend S C f) C"
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume "S' \<in> C"
    and "(\<Union>x. extend S C f x) \<subseteq> S'"
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
  
theorem hintikka_model:
  assumes hin: "hintikka H"
  shows "(p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) p) \<and>
  (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg p))"
proof (rule_tac r="measure size_form" and a=p in wf_induct)
  show "wf (measure size_form)"
    by blast
next
  let ?eval = "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H)"
    
  fix x
  assume wf: "\<forall>y. (y, x) \<in> measure size_form \<longrightarrow>
                  (y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval y) \<and>
              (Neg y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval (Neg y))"
    
  show "(x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval x) \<and> (Neg x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval (Neg x))"
  proof (cases x)
    case FF
    show ?thesis proof (intro conjI impI)
      assume "x \<in> H"
      then show "?eval x"
        using FF hin by (simp add: hintikka_def)
    next
      assume "Neg x \<in> H"
      then show "?eval (Neg x)" using FF by simp
    qed
  next
    case TT
    show ?thesis proof (intro conjI impI)
      assume "x \<in> H"
      then show "?eval x"
        using TT by simp
    next
      assume "Neg x \<in> H"
      then show "?eval (Neg x)"
        using TT hin by (simp add: hintikka_def)
    qed
  next
    case (Pred p ts)
    show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then show "?eval x" using Pred by simp
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Pred p ts) \<in> H"
        using Pred by simp
      then have "Pred p ts \<notin> H"
        using hin unfolding hintikka_def by fast
      then show "?eval (Neg x)"
        using Pred \<open>closed 0 x\<close> by simp
    qed
  next
    case (Neg Z)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then show "?eval x"
        using Neg wf by simp
    next
      assume "Neg x \<in> H"
      then have "Z \<in> H"
        using Neg hin unfolding hintikka_def by blast
      moreover assume "closed 0 x"
      then have "closed 0 Z"
        using Neg by simp
      ultimately have "?eval Z"
        using Neg wf by simp
      then show "?eval (Neg x)"
        using Neg by simp
    qed
  next
    case (And A B)
    then show ?thesis proof (intro conjI impI)
      assume "x \<in> H" and "closed 0 x"
      then have "And A B \<in> H" and "closed 0 (And A B)"
        using And by simp_all
      then have "A \<in> H \<and> B \<in> H"
        using And hin unfolding hintikka_def by blast
      then show "?eval x"
        using And wf \<open>closed 0 (And A B)\<close> by simp 
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (And A B) \<in> H" and "closed 0 (And A B)"
        using And by simp_all
      then have "Neg A \<in> H \<or> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show "?eval (Neg x)"
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
      then show "?eval x"
        using Or wf \<open>closed 0 (Or A B)\<close> by fastforce
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Or A B) \<in> H" and "closed 0 (Or A B)"
        using Or by simp_all
      then have "Neg A \<in> H \<and> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show "?eval (Neg x)"
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
      then show "?eval x"
        using Impl wf \<open>closed 0 (Impl A B)\<close> by fastforce
    next
      assume "Neg x \<in> H" and "closed 0 x"
      then have "Neg (Impl A B) \<in> H" and "closed 0 (Impl A B)"
        using Impl by simp_all
      then have "A \<in> H \<and> Neg B \<in> H"
        using hin unfolding hintikka_def by blast
      then show "?eval (Neg x)"
        using Impl wf \<open>closed 0 (Impl A B)\<close> by simp
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
              ?eval (P[term_of_hterm z/0]))"
          using Forall wf by blast
        then show "eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
          using * \<open>Forall P \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show "?eval x"
        using Forall by simp
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
              ?eval (Neg (subst P t 0)))"
        using Forall wf by blast   
      then have "?eval (Neg (P[t/0]))"
        using Forall * \<open>closed 0 (P[t/0])\<close> by simp
      then have "\<exists>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
        by auto
      then show "?eval (Neg x)"
        using Forall by simp
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
              ?eval (subst P t 0))"
        using Exists wf by blast   
      then have "?eval (P[t/0])"
        using Exists * \<open>closed 0 (P[t/0])\<close> by simp
      then have "\<exists>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
        by auto
      then show "?eval x"
        using Exists by simp
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
              ?eval (Neg (P[term_of_hterm z/0])))"
          using Exists wf by blast
        then show "\<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P"
          using * \<open>Neg (Exists P) \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show "?eval (Neg x)"
        using Exists by simp
    qed
  qed
qed

text {*
Using the maximality of @{term "Extend S C f"}, we can show
that @{term "Extend S C f"} yields Hintikka sets:
*}

lemma Exists_in_extend:
  assumes "extend S C f n \<union> {f n} \<in> C" (is "?S' \<in> C")
    and "Exists P = f n"
  shows "P[(App (SOME k. k \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)) [])/0] \<in> extend S C f (Suc n)"
    (is "subst P ?t 0 \<in> extend S C f (Suc n)")
proof -
  have "\<exists>p. f n = Exists p"
    using \<open>Exists P = f n\<close> by metis
  then have "extend S C f (Suc n) = (?S' \<union> {(dest_Exists (f n))[?t/0]})"
    using \<open>?S' \<in> C\<close> by simp
  also have "\<dots> = (?S' \<union> {(dest_Exists (Exists P))[?t/0]})"
    using \<open>Exists P = f n\<close> by presburger
  also have "\<dots> = (?S' \<union> {P[?t/0]})"
    by simp
  finally show ?thesis
    by blast
qed
  
lemma Neg_Forall_in_extend:
  assumes "extend S C f n \<union> {f n} \<in> C" (is "?S' \<in> C")
    and "Neg (Forall P) = f n"
  shows "Neg (P[(App (SOME k. k \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)) [])/0]) \<in>
          extend S C f (Suc n)"
    (is "Neg (subst P ?t 0) \<in> extend S C f (Suc n)")
proof -
  have "f n \<noteq> Exists P"
    using \<open>Neg (Forall P) = f n\<close> by auto
  
  have "\<exists>p. f n = Neg (Forall p)"
    using \<open>Neg (Forall P) = f n\<close> by metis
  then have "extend S C f (Suc n) = (?S' \<union> {Neg (dest_Forall (dest_Neg (f n))[?t/0])})"
    using \<open>?S' \<in> C\<close> \<open>f n \<noteq> Exists P\<close> by auto
  also have "\<dots> = (?S' \<union> {Neg (dest_Forall (dest_Neg (Neg (Forall P)))[?t/0])})"
    using \<open>Neg (Forall P) = f n\<close> by presburger
  also have "\<dots> = (?S' \<union> {Neg (P[?t/0])})"
    by simp
  finally show ?thesis
    by blast
qed
    
theorem extend_hintikka:
  assumes fin_ch: "finite_char C"
    and infin_p: "infinite (- (\<Union>p\<in>S. params p))"
    and surj: "\<forall>y. \<exists>n. y = f n"
    and altc: "alt_consistency C"
    and "S \<in> C"
  shows "hintikka (Extend S C f)" (is "hintikka ?H")
  unfolding hintikka_def
proof (intro allI impI conjI)
  have "maximal ?H C"
    by (simp add: extend_maximal fin_ch surj)

  have "?H \<in> C"
    using Extend_in_C assms by blast
      
  have "\<forall>S'\<in>C. ?H \<subseteq> S' \<longrightarrow> ?H = S'"
    using \<open>maximal ?H C\<close>
    unfolding maximal_def by blast
  
  { fix p ts
    show "\<not> (Pred p ts \<in> ?H \<and> Neg (Pred p ts) \<in> ?H)"
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast }
  
  show "FF \<notin> ?H"
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
  
  show "Neg TT \<notin> ?H"
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
      
  { fix Z
    assume "Neg (Neg Z) \<in> ?H"
    then have "?H \<union> {Z} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show "Z \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
      
  { fix A B
    assume "And A B \<in> ?H"
    then have "?H \<union> {A, B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show "A \<in> ?H" and "B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }
    
  { fix A B
    assume "Neg (Or A B) \<in> ?H"
    then have "?H \<union> {Neg A, Neg B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show "Neg A \<in> ?H" and "Neg B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }
    
  { fix A B
    assume "Neg (Impl A B) \<in> ?H"
    then have "?H \<union> {A, Neg B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show "A \<in> ?H" and "Neg B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }
    
  { fix A B
    assume "Or A B \<in> ?H"
    then have "?H \<union> {A} \<in> C \<or> ?H \<union> {B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show "A \<in> ?H \<or> B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
    
  { fix A B
    assume "Neg (And A B) \<in> ?H"
    then have "?H \<union> {Neg A} \<in> C \<or> ?H \<union> {Neg B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by presburger
    then show "Neg A \<in> ?H \<or> Neg B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
    
  { fix A B
    assume "Impl A B \<in> ?H"
    then have "?H \<union> {Neg A} \<in> C \<or> ?H \<union> {B} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by presburger
    then show "Neg A \<in> ?H \<or> B \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
    
  { fix P and t :: "nat term"
    assume "Forall P \<in> ?H" and "closedt 0 t"
    then have "?H \<union> {P[t/0]} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show "P[t/0] \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
    
  { fix P and t :: "nat term"
    assume "Neg (Exists P) \<in> ?H" and "closedt 0 t"
    then have "?H \<union> {Neg (P[t/0])} \<in> C"
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show "Neg (P[t/0]) \<in> ?H"
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }
    
  { fix P
    assume "Exists P \<in> ?H"
    obtain n where *: "Exists P = f n"
      using surj by blast
        
    let ?t = "App (SOME k. k \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)) []"
    have "closedt 0 ?t" by simp
        
    have "Exists P \<in> (\<Union>n. extend S C f n)"
      using \<open>Exists P \<in> ?H\<close> Extend_def by blast
    then have "extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)"
      using * by (simp add: UN_upper)
    then have "extend S C f n \<union> {f n} \<in> C"
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have "P[?t/0] \<in> extend S C f (Suc n)"
      using * Exists_in_extend by blast
    then have "P[?t/0] \<in> ?H"
      using Extend_def by blast
    then show "\<exists>t. closedt 0 t \<and> P[t/0] \<in> ?H"
      using \<open>closedt 0 ?t\<close> by blast }
    
  { fix P
    assume "Neg (Forall P) \<in> ?H"
    obtain n where *: "Neg (Forall P) = f n"
      using surj by blast
   
    let ?t = "App (SOME k. k \<notin> (\<Union>p\<in>extend S C f n \<union> {f n}. params p)) []"
    have "closedt 0 ?t" by simp
        
    have "Neg (Forall P) \<in> (\<Union>n. extend S C f n)"
      using \<open>Neg (Forall P) \<in> ?H\<close> Extend_def by blast
    then have "extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)"
      using * by (simp add: UN_upper)
    then have "extend S C f n \<union> {f n} \<in> C"
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have "Neg (P[?t/0]) \<in> extend S C f (Suc n)"
      using * Neg_Forall_in_extend by blast
    then have "Neg (P[?t/0]) \<in> ?H"
      using Extend_def by blast
    then show "\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> ?H"
      using \<open>closedt 0 ?t\<close> by blast }
qed
  
subsection {* Model existence theorem *}

text {*
\label{sec:model-existence}
Since the result of extending @{text S} is a superset of @{text S},
it follows that each consistent set @{text S} has a Herbrand model:
*}

lemma hintikka_Extend_S:
  assumes "consistency C" and "S \<in> C"
    and "infinite (- (\<Union>p \<in> S. params p))"
  shows "hintikka (Extend S (mk_finite_char (mk_alt_consistency (close C))) from_nat)"
    (is "hintikka (Extend S ?C' from_nat)")
proof -
  have "finite_char ?C'"
    using finite_char by blast
  moreover have "\<forall>y. y = from_nat (to_nat y)"
    by simp
  then have "\<forall>y. \<exists>n. y = from_nat n"
    by blast
  moreover have "alt_consistency ?C'"
    using alt_consistency close_closed close_consistency \<open>consistency C\<close>
      finite_alt_consistency mk_alt_consistency_closed
    by blast
  moreover have "S \<in> close C"
    using close_subset \<open>S \<in> C\<close> by blast
  then have "S \<in> mk_alt_consistency (close C)"
    using mk_alt_consistency_subset by blast
  then have "S \<in> ?C'"
    using close_closed finite_char_subset mk_alt_consistency_closed by blast
  ultimately show ?thesis
    using extend_hintikka \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    by metis
qed

theorem model_existence:
  assumes "consistency C"
    and "S \<in> C"
    and "infinite (- (\<Union>p \<in> S. params p))"
    and "p \<in> S"
    and "closed 0 p"
  shows "eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend S
        (mk_finite_char (mk_alt_consistency (close C))) from_nat) p"
  using assms hintikka_model hintikka_Extend_S Extend_subset 
  by blast

subsection {* Completeness for Natural Deduction *}

text {*
Thanks to the model existence theorem, we can now show the completeness
of the natural deduction calculus introduced in \secref{sec:proof-calculus}.
In order for the model existence theorem to be applicable, we have to prove
that the set of sets that are consistent with respect to @{text "\<turnstile>"} is a
consistency property:
*}

theorem deriv_consistency:
  assumes inf_param: "infinite (UNIV :: 'a set)"
  shows "consistency {S::('a, 'b) form set. \<exists>G. S = set G \<and> \<not> G \<turnstile> FF}"
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: "('a, 'b) form set"
  assume "S \<in> {set G |G. \<not> G \<turnstile> FF}" (is "S \<in> ?C")
  then obtain G :: "('a, 'b) form list"
    where *: "S = set G" and "\<not> G \<turnstile> FF"
    by blast
      
  { fix p ts
    assume "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
    then have "G \<turnstile> Pred p ts" and "G \<turnstile> Neg (Pred p ts)"
      using Assum * by blast+
    then have "G \<turnstile> FF"
      using NegE by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }
    
  { assume "FF \<in> S"
    then have "G \<turnstile> FF"
      using Assum * by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }
    
  { assume "Neg TT \<in> S"
    then have "G \<turnstile> Neg TT"
      using Assum * by blast
    moreover have "G \<turnstile> TT"
      using TTI by blast
    ultimately have "G \<turnstile> FF"
      using NegE by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }
    
  { fix Z
    assume "Neg (Neg Z) \<in> S"
    then have "G \<turnstile> Neg (Neg Z)"
      using Assum * by blast
        
    { assume "Z # G \<turnstile> FF"
      then have "G \<turnstile> Neg Z"
        using NegI by blast
      then have "G \<turnstile> FF"
        using NegE \<open>G \<turnstile> Neg (Neg Z)\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have "\<not> Z # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {Z} = set (Z # G)"
      using * by simp
    ultimately show "S \<union> {Z} \<in> ?C"
      by blast }
    
  { fix A B
    assume "And A B \<in> S"
    then have "G \<turnstile> And A B"
      using Assum * by blast
    then have "G \<turnstile> A" and "G \<turnstile> B"
      using AndE1 AndE2 by blast+
        
    { assume "A # B # G \<turnstile> FF"
      then have "B # G \<turnstile> Neg A"
        using NegI by blast
      then have "G \<turnstile> Neg A"
        using cut \<open>G \<turnstile> B\<close> by blast
      then have "G \<turnstile> FF"
        using NegE \<open>G \<turnstile> A\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have "\<not> A # B # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {A, B} = set (A # B # G)"
      using * by simp
    ultimately show "S \<union> {A, B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (Or A B) \<in> S"
    then have "G \<turnstile> Neg (Or A B)"
      using Assum * by blast
        
    have "A # Neg B # G \<turnstile> A"
      by (simp add: Assum)
    then have "A # Neg B # G \<turnstile> Or A B"
      using OrI1 by blast
    moreover have "A # Neg B # G \<turnstile> Neg (Or A B)"
      using * \<open>Neg (Or A B) \<in> S\<close> by (simp add: Assum)
    ultimately have "A # Neg B # G \<turnstile> FF"
      using NegE \<open>A # Neg B # G \<turnstile> Neg (Or A B)\<close> by blast
    then have "Neg B # G \<turnstile> Neg A"
      using NegI by blast
        
    have "B # G \<turnstile> B"
      by (simp add: Assum)
    then have "B # G \<turnstile> Or A B"
      using OrI2 by blast
    moreover have "B # G \<turnstile> Neg (Or A B)"
      using * \<open>Neg (Or A B) \<in> S\<close> by (simp add: Assum)
    ultimately have "B # G \<turnstile> FF"
      using NegE \<open>B # G \<turnstile> Neg (Or A B)\<close> by blast
    then have "G \<turnstile> Neg B"
      using NegI by blast
        
    { assume "Neg A # Neg B # G \<turnstile> FF"
      then have "Neg B # G \<turnstile> Neg (Neg A)"
        using NegI by blast
      then have "Neg B # G \<turnstile> FF"
        using NegE \<open>Neg B # G \<turnstile> Neg A\<close> by blast
      then have "G \<turnstile> FF"
        using cut \<open>G \<turnstile> Neg B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have "\<not> Neg A # Neg B # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {Neg A, Neg B} = set (Neg A # Neg B # G)"
      using * by simp
    ultimately show "S \<union> {Neg A, Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (Impl A B) \<in> S"
      
    have "A # Neg A # Neg B # G \<turnstile> A"
      by (simp add: Assum)
    moreover have "A # Neg A # Neg B # G \<turnstile> Neg A"
      by (simp add: Assum)
    ultimately have "A # Neg A # Neg B # G \<turnstile> FF"
      using NegE by blast
    then have "A # Neg A # Neg B # G \<turnstile> B"
      using FFE by blast
    then have "Neg A # Neg B # G \<turnstile> Impl A B"
      using ImplI by blast
    moreover have "Neg A # Neg B # G \<turnstile> Neg (Impl A B)"
      using * \<open>Neg (Impl A B) \<in> S\<close> by (simp add: Assum)
    ultimately have "Neg A # Neg B # G \<turnstile> FF"
      using NegE by blast
    then have "Neg B # G \<turnstile> A"
      using Class by blast
        
    have "A # B # G \<turnstile> B"
      by (simp add: Assum)
    then have "B # G \<turnstile> Impl A B"
      using ImplI by blast
    moreover have "B # G \<turnstile> Neg (Impl A B)"
      using * \<open>Neg (Impl A B) \<in> S\<close> by (simp add: Assum)
    ultimately have "B # G \<turnstile> FF"
      using NegE by blast
    then have "G \<turnstile> Neg B"
      using NegI by blast
        
    { assume "A # Neg B # G \<turnstile> FF"
      then have "Neg B # G \<turnstile> Neg A"
        using NegI by blast
      then have "Neg B # G \<turnstile> FF"
        using NegE \<open>Neg B # G \<turnstile> A\<close> by blast
      then have "G \<turnstile> FF"
        using cut \<open>G \<turnstile> Neg B\<close> by blast
      then have False using \<open>\<not> G \<turnstile> FF\<close>
        by blast }
    then have "\<not> A # Neg B # G \<turnstile> FF"
      by blast
    moreover have "{A, Neg B} \<union> S = set (A # Neg B # G)"
      using * by simp
    ultimately show "S \<union> {A, Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume  "Or A B \<in> S"
    then have "G \<turnstile> Or A B"
      using * Assum by blast
        
    { assume "(\<forall>G'. set G' = S \<union> {A} \<longrightarrow> G' \<turnstile> FF)"
        and "(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> G' \<turnstile> FF)"
      then have "A # G \<turnstile> FF" and "B # G \<turnstile> FF"
        using * by simp_all
      then have "G \<turnstile> FF"
        using OrE \<open>G \<turnstile> Or A B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show "S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (And A B) \<in> S"
      
    let ?x = "Or (Neg A) (Neg B)"
      
    have "B # A # Neg ?x # G \<turnstile> A" and "B # A # Neg ?x # G \<turnstile> B"
      by (simp_all add: Assum)
    then have "B # A # Neg ?x # G \<turnstile> And A B"
      using AndI by blast
    moreover have "B # A # Neg ?x # G \<turnstile> Neg (And A B)"
      using * \<open>Neg (And A B) \<in> S\<close> by (simp add: Assum)
    ultimately have "B # A # Neg ?x # G \<turnstile> FF"
      using NegE by blast
    then have "A # Neg ?x # G \<turnstile> Neg B"
      using NegI by blast
    then have "A # Neg ?x # G \<turnstile> ?x"
      using OrI2 by blast
    moreover have "A # Neg ?x # G \<turnstile> Neg ?x"
      by (simp add: Assum)
    ultimately have "A # Neg ?x # G \<turnstile> FF"
      using NegE by blast
    then have "Neg ?x # G \<turnstile> Neg A"
      using NegI by blast
    then have "Neg ?x # G \<turnstile> ?x"
      using OrI1 by blast
    then have "G \<turnstile> Or (Neg A) (Neg B)"
      using Class' by blast
        
    { assume "(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> G' \<turnstile> FF)"
        and "(\<forall>G'. set G' = S \<union> {Neg B} \<longrightarrow> G' \<turnstile> FF)"
      then have "Neg A # G \<turnstile> FF" and "Neg B # G \<turnstile> FF"
        using * by simp_all
      then have "G \<turnstile> FF"
        using OrE \<open>G \<turnstile> Or (Neg A) (Neg B)\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Impl A B \<in> S"
      
    let ?x = "Or (Neg A) B"
      
    have "A # Neg ?x # G \<turnstile> A"
      by (simp add: Assum)
    moreover have "A # Neg ?x # G \<turnstile> Impl A B"
      using * \<open>Impl A B \<in> S\<close> by (simp add: Assum)
    ultimately have "A # Neg ?x # G \<turnstile> B"
      using ImplE by blast
    then have "A # Neg ?x # G \<turnstile> ?x"
      using OrI2 by blast
    moreover have "A # Neg ?x # G \<turnstile> Neg ?x"
      by (simp add: Assum)
    ultimately have "A # Neg ?x # G \<turnstile> FF"
      using NegE by blast
    then have "Neg ?x # G \<turnstile> Neg A"
      using NegI by blast
    then have "Neg ?x # G \<turnstile> ?x"
      using OrI1 by blast
    then have "G \<turnstile> Or (Neg A) B"
      using Class' by blast
        
    { assume "(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> G' \<turnstile> FF)"
        and "(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> G' \<turnstile> FF)"
      then have "Neg A # G \<turnstile> FF" and "B # G \<turnstile> FF"
        using * by simp_all
      then have "G \<turnstile> FF"
        using OrE \<open>G \<turnstile> Or (Neg A) B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Forall P \<in> S"
    then have "G \<turnstile> Forall P"
      using Assum * by blast
    then have "G \<turnstile> P[t/0]"
      using ForallE by blast
        
    { assume "P[t/0] # G \<turnstile> FF"
      then have "G \<turnstile> FF"
        using cut \<open>G \<turnstile> P[t/0]\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have "\<not> P[t/0] # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {P[t/0]} = set (P[t/0] # G)"
      using * by simp
    ultimately show "S \<union> {P[t/0]} \<in> ?C"
      by blast }
    
  { fix P and t :: "'a term"
    assume "closedt 0 t" and "Neg (Exists P) \<in> S"
    then have "G \<turnstile> Neg (Exists P)"
      using Assum * by blast
    then have "P[t/0] \<in> set (P[t/0] # G)"
      by (simp add: Assum)
    then have "P[t/0] # G \<turnstile> P[t/0]"
      using Assum by blast
    then have "P[t/0] # G \<turnstile> Exists P"
      using ExistsI by blast
    moreover have "P[t/0] # G \<turnstile> Neg (Exists P)"
      using * \<open>Neg (Exists P) \<in> S\<close> by (simp add: Assum)
    ultimately have "P[t/0] # G \<turnstile> FF"
      using NegE by blast
    then have "G \<turnstile> Neg (P[t/0])"
      using NegI by blast
        
    { assume "Neg (P[t/0]) # G \<turnstile> FF"
      then have "G \<turnstile> FF"
        using cut \<open>G \<turnstile> Neg (P[t/0])\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have "\<not> Neg (P[t/0]) # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {Neg (P[t/0])} = set (Neg (P[t/0]) # G)"
      using * by simp
    ultimately show "S \<union> {Neg (P[t/0])} \<in> ?C"
      by blast }
    
  { fix P
    assume "Exists P \<in> S"
    then have "G \<turnstile> Exists P"
      using * Assum by blast
        
    have "finite ((\<Union>p \<in> set G. params p) \<union> params P)"
      by simp
    then have "infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))"
      using inf_param Diff_infinite_finite finite_compl by blast
    then have "infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))"
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: "x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)"
      using infinite_imp_nonempty by blast
        
    { assume "P[App x []/0] # G \<turnstile> FF"
      moreover have "list_all (\<lambda>p. x \<notin> params p) G"
        using ** by (simp add: list_all_iff)
      moreover have "x \<notin> params P"
        using ** by simp
      moreover have "x \<notin> params FF"
        by simp
      ultimately have "G \<turnstile> FF"
        using ExistsE \<open>G \<turnstile> Exists P\<close> by fast
      then have False using \<open>\<not> G \<turnstile> FF\<close>
        by blast}
    then have "\<not> P[App x []/0] # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {P[App x []/0]} = set (P[App x []/0] # G)"
      using * by simp
    ultimately show "\<exists>x. S \<union> {P[App x []/0]} \<in> ?C"
      by blast }
    
  { fix P
    assume "Neg (Forall P) \<in> S"
    then have "G \<turnstile> Neg (Forall P)"
      using * Assum by blast
        
    have "finite ((\<Union>p \<in> set G. params p) \<union> params P)"
      by simp
    then have "infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))"
      using inf_param Diff_infinite_finite finite_compl by blast
    then have "infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))"
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: "x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)"
      using infinite_imp_nonempty by blast
        
    let ?x = "Neg (Exists (Neg P))"
        
    have "Neg (P[App x []/0]) # ?x # G \<turnstile> Neg P[App x []/0]"
      by (simp add: Assum)
    then have "Neg (P[App x []/0]) # ?x # G \<turnstile> Exists (Neg P)"
      using ExistsI by blast
    moreover have "Neg (P[App x []/0]) # ?x # G \<turnstile> ?x"
      by (simp add: Assum)
    ultimately have "Neg (P[App x []/0]) # ?x # G \<turnstile> FF"
      using NegE by blast
    then have "?x # G \<turnstile> P[App x []/0]"
      using Class by blast
    moreover have "list_all (\<lambda>p. x \<notin> params p) (?x # G)"
      using ** by (simp add: list_all_iff)
    moreover have "x \<notin> params P"
      using ** by simp
    ultimately have "?x # G \<turnstile> Forall P"
      using ForallI by fast
    moreover have "?x # G \<turnstile> Neg (Forall P)"
      using * \<open>Neg (Forall P) \<in> S\<close> by (simp add: Assum)
    ultimately have "?x # G \<turnstile> FF"
      using NegE by blast
    then have "G \<turnstile> Exists (Neg P)"
      using Class by blast
        
    { assume "Neg (P[App x []/0]) # G \<turnstile> FF"
      moreover have "list_all (\<lambda>p. x \<notin> params p) G"
        using ** by (simp add: list_all_iff)
      moreover have "x \<notin> params P"
        using ** by simp
      moreover have "x \<notin> params FF"
        by simp
      ultimately have "G \<turnstile> FF"
        using ExistsE \<open>G \<turnstile> Exists (Neg P)\<close> by fastforce
      then have False using \<open>\<not> G \<turnstile> FF\<close>
        by blast}
    then have "\<not> Neg (P[App x []/0]) # G \<turnstile> FF"
      by blast
    moreover have "S \<union> {Neg (P[App x []/0])} = set (Neg (P[App x []/0]) # G)"
      using * by simp
    ultimately show "\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C"
      by blast }
qed

text {*
Hence, by contradiction, we have completeness of natural deduction:
*}
      
theorem natded_complete:
  assumes "closed 0 p"
    and "list_all (closed 0) ps"
    and mod: "\<forall>e f g. e,(f :: nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm),
              (g :: nat \<Rightarrow> nat hterm list \<Rightarrow> bool),ps \<Turnstile> p"
  shows "ps \<turnstile> p"
proof (rule Class, rule ccontr)
  fix e
  assume "\<not> Neg p # ps \<turnstile> FF"
    
  let ?S = "set (Neg p # ps)"
  let ?C = "{set (G :: (nat, nat) form list) | G. \<not> G \<turnstile> FF}"
  let ?f = HApp
  let ?g = "(\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend ?S
              (mk_finite_char (mk_alt_consistency (close ?C))) from_nat)"

  from \<open>list_all (closed 0) ps\<close>
  have "\<forall>p \<in> set ps. closed 0 p"
    by (simp add: list_all_iff)

  { fix x
    assume "x \<in> ?S"
    moreover have "consistency ?C"
      using deriv_consistency by blast
    moreover have "?S \<in> ?C"
      using \<open>\<not> Neg p # ps \<turnstile> FF\<close> by blast
    moreover have "infinite (- (\<Union>p\<in>?S. params p))"
      by (simp add: Compl_eq_Diff_UNIV)
    moreover note \<open>closed 0 p\<close> \<open>\<forall>p \<in> set ps. closed 0 p\<close> \<open>x \<in> ?S\<close>
    then have \<open>closed 0 x\<close> by auto
    ultimately have "eval e ?f ?g x"
      using model_existence by blast }
  then have "list_all (eval e ?f ?g) (Neg p # ps)"
    by (simp add: list_all_iff)
  moreover have "eval e ?f ?g (Neg p)"
    using calculation by simp 
  moreover have "list_all (eval e ?f ?g) ps"
    using calculation by simp
  then have "eval e ?f ?g p"
    using mod unfolding model_def by blast
  ultimately show False by simp
qed

subsection {*Completeness for open formulas *}
  
primrec
  free_levels\<^sub>t :: "nat \<Rightarrow> 'a term \<Rightarrow> nat" and
  free_levels\<^sub>t\<^sub>s :: "nat \<Rightarrow> 'a term list \<Rightarrow> nat"
where
  "free_levels\<^sub>t m (Var n) = (if n < m then 0 else n - m + 1)"
| "free_levels\<^sub>t m (App a ts) = free_levels\<^sub>t\<^sub>s m ts"
| "free_levels\<^sub>t\<^sub>s m [] = 0"
| "free_levels\<^sub>t\<^sub>s m (t # ts) = max (free_levels\<^sub>t m t) (free_levels\<^sub>t\<^sub>s m ts)"

primrec
  free_levels :: "nat \<Rightarrow> ('a, 'b) form \<Rightarrow> nat"
where
  "free_levels m FF = 0"
| "free_levels m TT = 0"
| "free_levels m (Pred b ts) = free_levels\<^sub>t\<^sub>s m ts"
| "free_levels m (And p q) = max (free_levels m p) (free_levels m q)"
| "free_levels m (Or p q) = max (free_levels m p) (free_levels m q)"
| "free_levels m (Impl p q) = max (free_levels m p) (free_levels m q)"
| "free_levels m (Neg p) = free_levels m p"
| "free_levels m (Forall p) = free_levels (Suc m) p"
| "free_levels m (Exists p) = free_levels (Suc m) p"

lemma closedt_free_levels:
  "free_levels\<^sub>t 0 (t :: 'a term) \<le> k \<Longrightarrow> closedt k t"
  "free_levels\<^sub>t\<^sub>s 0 (ts :: 'a term list) \<le> k \<Longrightarrow> closedts k ts"
  by (induct t and ts rule: free_levels\<^sub>t.induct free_levels\<^sub>t\<^sub>s.induct) simp_all
    
lemma piecewise_sub: "(if (x :: nat) < m then 0 else x - m + 1) \<le> k \<Longrightarrow> x < k + m"
  by (cases \<open>x < m\<close>) simp_all
  
lemma free_levels_closed_terms:
  "free_levels\<^sub>t m (t :: 'a term) \<le> k \<Longrightarrow> closedt (k + m) t"
  "free_levels\<^sub>t\<^sub>s m (ts :: 'a term list) \<le> k \<Longrightarrow> closedts (k + m) ts"
  using piecewise_sub
  by (induct t and ts rule: free_levels\<^sub>t.induct free_levels\<^sub>t\<^sub>s.induct) auto

lemma free_levels_closed: "free_levels m p \<le> k \<Longrightarrow> closed (k + m) p"
  by (induct p arbitrary: m k) (force simp add: free_levels_closed_terms)+
    
lemma closed_terms_free_levels:
  "closedt (k + m) t \<Longrightarrow> free_levels\<^sub>t m (t :: 'a term) \<le> k"
  "closedts (k + m) ts \<Longrightarrow> free_levels\<^sub>t\<^sub>s m (ts :: 'a term list) \<le> k"
  by (induct t and ts rule: free_levels\<^sub>t.induct free_levels\<^sub>t\<^sub>s.induct) auto

lemma closed_free_levels: "closed (k + m) p \<Longrightarrow> free_levels m p \<le> k"
  by (induct p arbitrary: m k) (simp_all add: closed_terms_free_levels)

lemma free_levels_closed_zero: "(free_levels 0 p = 0) = closed 0 p"
proof
  show "free_levels 0 p = 0 \<Longrightarrow> closed 0 p"
    using free_levels_closed by fastforce
next
  show "closed 0 p \<Longrightarrow> free_levels 0 p = 0"
    using closed_free_levels by force
qed 
    
lemma free_levels_terms_suc:
  "free_levels\<^sub>t m (t :: 'a term) \<le> Suc k \<Longrightarrow> free_levels\<^sub>t (Suc m) t \<le> k"
  "free_levels\<^sub>t\<^sub>s m (ts :: 'a term list) \<le> Suc k \<Longrightarrow> free_levels\<^sub>t\<^sub>s (Suc m) ts \<le> k"
  by (induct t and ts rule: free_levels\<^sub>t.induct free_levels\<^sub>t\<^sub>s.induct) auto
    
lemma free_levels_Forall: "free_levels m p \<le> Suc k \<Longrightarrow> free_levels m (Forall p) \<le> k"
  by (induct p arbitrary: m k) (simp_all add: free_levels_terms_suc)
    
lemma free_levels_terms_suc_eq:
  "free_levels\<^sub>t m (t :: 'a term) = Suc k \<Longrightarrow> free_levels\<^sub>t (Suc m) t = k"
  "free_levels\<^sub>t\<^sub>s m (ts :: 'a term list) = Suc k \<Longrightarrow> free_levels\<^sub>t\<^sub>s (Suc m) ts = k"
  proof (induct and ts rule: free_levels\<^sub>t.induct free_levels\<^sub>t\<^sub>s.induct)
    case (Var x)
    then show ?case proof (induct x)
      case 0
      then show ?case
        by (cases \<open>0 < m\<close>) simp_all
    next
      case (Suc x)
      have "(if Suc x < m then 0 else Suc x - m + 1) = Suc k \<Longrightarrow> x < m \<Longrightarrow> k = 0"
        by (metis Suc_eq_plus1 Suc_inject Suc_lessI diff_self_eq_0 nat.distinct(1))
      then show ?case
        using Suc by auto
    qed
  next
    case (App t ts)
    then show ?case by simp
  next
    case Nil_term
    then show ?case by simp
  next
    case (Cons_term t ts)
    then show ?case
      by (metis free_levels\<^sub>t\<^sub>s.simps(2) free_levels_terms_suc(2) le_refl max_absorb1 max_def)
  qed

lemma free_levels_suc: "free_levels m p = (Suc k) \<Longrightarrow> free_levels m (Forall p) = k"
proof (induct p arbitrary: m k)
  case (Pred p ts)
  then show ?case
    using free_levels_terms_suc_eq by simp
next
  case (And A B)
  then have 1: "Suc k = max (free_levels m A) (free_levels m B)"
    by simp
  have 2: "max (free_levels (Suc m) A) (free_levels (Suc m) B) = free_levels m (Forall (And A B))"
    by simp
  then have "free_levels m (Forall (And A B)) =
      k \<or> max (free_levels m A) (free_levels m B) = free_levels m A"
    by (metis And.hyps(2) 1 free_levels.simps(8) free_levels_Forall max_def)
  then show ?case
    by (metis And.hyps(1) And.prems 1 2 free_levels.simps(8) free_levels_Forall
        max.cobounded1 max_absorb1 max_def)
next
  case (Or A B)
  then have 1: "Suc k = max (free_levels m A) (free_levels m B)"
    by simp
  have 2: "max (free_levels (Suc m) A) (free_levels (Suc m) B) = free_levels m (Forall (Or A B))"
    by simp
  then have "free_levels m (Forall (Or A B)) =
      k \<or> max (free_levels m A) (free_levels m B) = free_levels m A"
    by (metis Or.hyps(2) 1 free_levels.simps(8) free_levels_Forall max_def)
  then show ?case
    by (metis Or.hyps(1) Or.prems 1 2 free_levels.simps(8) free_levels_Forall
        max.cobounded1 max_absorb1 max_def)
next
  case (Impl A B)
  then have 1: "Suc k = max (free_levels m A) (free_levels m B)"
    by simp
  have 2: "max (free_levels (Suc m) A) (free_levels (Suc m) B) = free_levels m (Forall (Impl A B))"
    by simp
  then have "free_levels m (Forall (Impl A B)) =
      k \<or> max (free_levels m A) (free_levels m B) = free_levels m A"
    by (metis Impl.hyps(2) 1 free_levels.simps(8) free_levels_Forall max_def)
  then show ?case
    by (metis Impl.hyps(1) Impl.prems 1 2 free_levels.simps(8) free_levels_Forall
        max.cobounded1 max_absorb1 max_def)
qed simp_all
    
lemma model_impl_premise: "(e,f,g,ps \<Turnstile> (Impl p a)) = (e,f,g,(p#ps) \<Turnstile> a)"
  unfolding model_def by auto
    
primrec build_impl :: "('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "build_impl [] a = a"
| "build_impl (p#ps) a = Impl p (build_impl ps a)"
  
theorem model_build_impl_premises:
  "(e,f,g,ps' \<Turnstile> build_impl ps a) = (e,f,g,(ps@ps') \<Turnstile> a)"
  using model_impl_premise
  unfolding model_def by (induct ps) auto
    
primrec put_Foralls :: "nat \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "put_Foralls (Suc m) p = Forall (put_Foralls m p)"
| "put_Foralls 0 p = p"
  
lemma free_levels_put_Foralls_diff:
  "free_levels m (put_Foralls k p) = free_levels m p - k"
  using free_levels_Forall free_levels_suc by (induct k) force+
  
lemma free_levels_put_Foralls_zero: "free_levels 0 (put_Foralls (free_levels 0 p) p) = 0"
  by (simp add: free_levels_put_Foralls_diff)
  
lemma closed_put_Foralls_free_levels: "closed 0 (put_Foralls (free_levels 0 p) p)"
  using free_levels_put_Foralls_zero free_levels_closed_zero by blast
  
definition univ_close :: "('a, 'b) form \<Rightarrow> ('a, 'b) form" where
  "univ_close p = put_Foralls (free_levels 0 p) p"
  
lemma closed_univ_close: "closed 0 (univ_close p)"
  unfolding univ_close_def using closed_put_Foralls_free_levels by blast
 
lemma valid_implies_forall_no_prems:
  assumes mod: "\<forall>e f g. e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> p"
  shows "e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> Forall p"
  using mod eval.simps(8) list.pred_inject(1) unfolding model_def by simp_all
    
lemma valid_put_Forall_no_prems:
  assumes mod: "\<forall>e f g. e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> p"
  shows "e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> put_Foralls m p"
  using mod by (induct m arbitrary: e f g) (simp_all add: valid_implies_forall_no_prems)
    
lemma valid_univ_close_no_prems:
  assumes mod: "\<forall>e f g. e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> p"
  shows "e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> univ_close p"
  unfolding univ_close_def using mod valid_put_Forall_no_prems by blast

theorem valid_univ_close_build_impl:
  assumes mod: "\<forall>e f g. e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,ps \<Turnstile> p"
  shows "e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,[] \<Turnstile> univ_close (build_impl ps p)"
  using mod by (metis append_self_conv model_build_impl_premises valid_univ_close_no_prems)

theorem valid_subst:
  assumes mod: "\<forall>e f g. e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,ps \<Turnstile> p"
  shows "e,(f :: 'a \<Rightarrow> 'b list \<Rightarrow> 'b),g,(map (\<lambda>p. subst p t m) ps) \<Turnstile> subst p t m"
  using mod by (simp add: model_def list_all_iff)
  
subsubsection {* Deriving the original formula from the universal closure *}

lemma put_Foralls_subst:
  "(put_Foralls m p)[Var k/l] = put_Foralls m (p[Var (m+k)/m+l])"
  by (induct m arbitrary: k l) simp_all
    
lemma put_Foralls_subst_zero:
  "(put_Foralls m p)[Var m/0] = put_Foralls m (p[Var (m+m)/m])"
  by (simp add: put_Foralls_subst)

lemma put_Foralls_suc: "put_Foralls m (Forall p) = put_Foralls (Suc m) p"
  by (induct m) simp_all

theorem deriv_remove_put_Foralls: "[] \<turnstile> put_Foralls m p \<Longrightarrow> [] \<turnstile> p"
  using ForallE' by (induct m) auto
 
theorem deriv_remove_univ_close: "[] \<turnstile> univ_close p \<Longrightarrow> [] \<turnstile> p"
  unfolding univ_close_def using deriv_remove_put_Foralls by blast

subsubsection {* Deriving under assumptions from an implication *}
    
theorem deriv_permute_assumptions: "ps' \<turnstile> q \<Longrightarrow> set ps' = set ps \<Longrightarrow> ps \<turnstile> q"
proof (induct q arbitrary: ps rule: deriv.induct)
  case (Assum a G)
  then show ?case
    using deriv.Assum by blast
next
  case (TTI G)
  then show ?case
    using deriv.TTI by blast
next
  case (FFE G a)
  then show ?case
    using deriv.FFE by blast
next
  case (NegI a G)
  then have "set (a # ps) = set (a # G)"
    by simp
  then have "a # ps \<turnstile> FF"
    using NegI by blast
  then show ?case
    using deriv.NegI by blast
next
  case (NegE G a)
  then have "ps \<turnstile> a" and "ps \<turnstile> Neg a"
    by blast+
  then show ?case
    using deriv.NegE by blast
next
  case (Class a G)
  then have "set (Neg a # ps) = set (Neg a # G)"
    by simp
  then have "Neg a # ps \<turnstile> FF"
    using Class by blast
  then show ?case
    using deriv.Class by blast
next
  case (AndI G a b)
  then have "ps \<turnstile> a" and "ps \<turnstile> b"
    by blast+
  then show ?case
    using deriv.AndI by blast
next
  case (AndE1 G a b)
  then show ?case
    using deriv.AndE1 by blast
next
  case (AndE2 G a b)
  then show ?case
     using deriv.AndE2 by blast
next
  case (OrI1 G a b)
  then show ?case
    using deriv.OrI1 by blast
next
  case (OrI2 G b a)
  then show ?case
    using deriv.OrI2 by blast
next
  case (OrE G a b c)
  then have "ps \<turnstile> Or a b" and "a # ps \<turnstile> c" and "b # ps \<turnstile> c"
   by simp_all
  then show ?case
    using deriv.OrE by blast
next
  case (ImplI a G b)
  then have "a # ps \<turnstile> b"
    by simp
  then show ?case
    using deriv.ImplI by blast
next
  case (ImplE G a b)
  then have "ps \<turnstile> Impl a b" and "ps \<turnstile> a"
    by simp_all
  then show ?case
    using deriv.ImplE by blast
next
  case (ForallI G a n)
  then have "ps \<turnstile> a[App n []/0]" and "list_all (\<lambda>p. n \<notin> params p) ps"
    by (simp_all add: list_all_iff)
  then show ?case
    using ForallI deriv.ForallI by fast
next
  case (ForallE G a t)
  then show ?case
    using deriv.ForallE by blast
next
  case (ForallE' a)
  then show ?case
    using deriv.ForallE' by auto
next
  case (ExistsI G a t)
  then show ?case
    using deriv.ExistsI by blast
next
  case (ExistsE G a n b)
  then have "ps \<turnstile> Exists a" and "(a[App n []/0] # ps) \<turnstile> b" and "list_all (\<lambda>p. n \<notin> params p) ps"
    by (simp_all add: list_all_iff)
  then show ?case
    using ExistsE deriv.ExistsE by fast
qed
  
lemma deriv_psubst:
   "ps \<turnstile> q \<Longrightarrow> inj f \<Longrightarrow> map (psubst f) ps \<turnstile> psubst f q"
proof (induct q rule: deriv.induct)
  case (Assum a G)
  then show ?case
    by (simp add: deriv.Assum)
next
  case (TTI G)
  then show ?case
    using deriv.TTI by simp
next
  case (FFE G a)
  then show ?case
    using deriv.FFE by simp
next
  case (NegI a G)
  then show ?case
    using deriv.NegI by simp
next
  case (NegE G a)
  then show ?case
    using deriv.NegE by simp
next
  case (Class a G)
  then show ?case
    using deriv.Class by simp
next
  case (AndI G a b)
  then show ?case
    using deriv.AndI by simp
next
  case (AndE1 G a b)
  then show ?case
    using deriv.AndE1 by simp
next
  case (AndE2 G a b)
  then show ?case
    using deriv.AndE2 by simp
next
  case (OrI1 G a b)
  then show ?case
    using deriv.OrI1 by simp
next
  case (OrI2 G b a)
  then show ?case
    using deriv.OrI2 by simp
next
  case (OrE G a b c)
  then show ?case
    using deriv.OrE by simp
next
  case (ImplI a G b)
  then show ?case
    using deriv.ImplI by simp
next
  case (ImplE G a b)
  then show ?case
    using deriv.ImplE by simp
next
  case (ForallI G a n)
  then have "f n \<notin> params (psubst f a)"
    by (simp add: inj_image_mem_iff)
  moreover note \<open>list_all (\<lambda>p. n \<notin> params p) G\<close> and \<open>inj f\<close>
  then have "list_all (\<lambda>p. f n \<notin> params p) (map (psubst f) G)"
    by (simp add: list_all_iff inj_image_mem_iff)
  moreover have "map (psubst f) G \<turnstile> psubst f (a[App n []/0])"
    using ForallI by blast
  ultimately show ?case
    using deriv.ForallI by fastforce
next
  case (ForallE G a t)
  then show ?case
    using deriv.ForallE by simp
next
  case (ForallE' a)
  then show ?case
    using deriv.ForallE' by simp
next
  case (ExistsI G a t)
  then show ?case
    using deriv.ExistsI by simp
next
  case (ExistsE G a n b)
  then have "map (psubst f) G \<turnstile> psubst f (Exists a)"
    by blast
  moreover have "f n \<notin> params (psubst f a)" and "f n \<notin> params (psubst f b)"
    using ExistsE by (simp_all add: inj_image_mem_iff)
  moreover note \<open>list_all (\<lambda>p. n \<notin> params p) G\<close> and \<open>inj f\<close>
  then have "list_all (\<lambda>p. f n \<notin> params p) (map (psubst f) G)"
    by (simp add: list_all_iff inj_image_mem_iff)
  moreover have "map (psubst f) (a[App n []/0] # G) \<turnstile> psubst f b"
    using ExistsE by blast
  ultimately show ?case
    using deriv.ExistsE by fastforce
qed    

lemma psubstt_fresh_free:
  "x \<noteq> n \<Longrightarrow> n \<notin> paramst (psubstt (id(n := x)) t)"
  "x \<noteq> n \<Longrightarrow> n \<notin> paramsts (psubstts (id(n := x)) ts)"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

lemma psubst_fresh_free: "x \<noteq> n \<Longrightarrow> n \<notin> params (psubst (id(n := x)) p)"
proof (induct p)
  case (Pred b ts)
  then show ?case
    using psubstt_fresh_free by auto
qed simp_all
    
lemma map_psubst_fresh_free:
  "x \<noteq> n \<Longrightarrow> n \<notin> (\<Union>p \<in> set (map (psubst (id(n := x))) ps). params p)"
proof (induct ps)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  then show ?case
    using psubst_fresh_free by auto
qed
  
lemma psubst_free_id: "n \<notin> params p \<Longrightarrow> p = psubst (id(n := x)) p"
  by auto
    
lemma psubst_free_id_set:
  "n \<notin> (\<Union>a\<in>G. params a) \<Longrightarrow> G \<subseteq> ps \<Longrightarrow> (\<forall>p\<in>ps. p \<in> G \<longrightarrow> psubst (id(n := x)) p \<in> G)"
  using psubst_free_id by simp
  
lemma psubst_fresh_subset:
  assumes "set G \<subseteq> set ps"
    and "n \<noteq> x"
    and "n \<notin> (\<Union>a\<in>set G. params a)"
  shows "set G \<subseteq> set (map (psubst (id(n := x))) ps)"
  using assms by (force simp add: psubst_free_id_set)

lemma deriv_swap_param:
  "ps \<turnstile> q \<Longrightarrow> map (psubst (id(x := n, n := x))) ps \<turnstile> psubst (id(x := n, n := x)) q"
  by (simp add: deriv_psubst inj_on_def)
 
lemma psubstt_fresh_away:
 "fresh \<notin> paramst t \<Longrightarrow> psubstt (id(fresh := n)) (psubstt (id(n := fresh)) t) = t"
 "fresh \<notin> paramsts ts \<Longrightarrow> psubstts (id(fresh := n)) (psubstts (id(n := fresh)) ts) = ts"
  by (induct t and ts rule: psubstt.induct psubstts.induct) auto
    
lemma psubst_fresh_away:
  "fresh \<notin> params p \<Longrightarrow> psubst (id(fresh := n)) (psubst (id(n := fresh)) p) = p"
proof (induct p)
  case (Pred b ts)
  then show ?case
    by (metis params.simps(3) psubst.simps(3) psubstt_fresh_away(2))
qed simp_all
  
lemma map_psubst_fresh_away:
  "fresh \<notin> (\<Union>p \<in> set ps. params p) \<Longrightarrow>
   map (psubst (id(fresh := n))) (map (psubst (id(n := fresh))) ps) = ps"
  using psubst_fresh_away by (induct ps) auto
    
lemma deriv_weaken_assumptions:
  assumes inf_param: "infinite (UNIV :: 'a set)"
  shows "ps' \<turnstile> q \<Longrightarrow> set ps' \<subseteq> set ps \<Longrightarrow> ps \<turnstile> (q :: ('a, 'b) form)"
proof (induct q arbitrary: ps rule: deriv.induct)
  case (Assum a G)
  then have "a \<in> set ps"
    by auto
  then show ?case
    using deriv.Assum by blast
next
  case (TTI G)
  then show ?case
    using deriv.TTI by blast
next
  case (FFE G a)
  then show ?case
    using deriv.FFE by blast
next
  case (NegI a G)
  then have "set (a # G) \<subseteq> set (a # ps)"
    by auto
  then have "a # ps \<turnstile> FF"
    using NegI by blast
  then show ?case
    using deriv.NegI by blast
next
  case (NegE G a)
  then show ?case
    using deriv.NegE by blast
next
  case (Class a G)
  then have "set (Neg a # G) \<subseteq> set (Neg a # ps)"
    by auto
  then have "Neg a # ps \<turnstile> FF"
    using Class by blast
  then show ?case
    using deriv.Class by blast
next
  case (AndI G a b)
  then show ?case
    using deriv.AndI by blast
next
  case (AndE1 G a b)
  then show ?case
    using deriv.AndE1 by blast
next
  case (AndE2 G a b)
  then show ?case
    using deriv.AndE2 by blast
next
  case (OrI1 G a b)
  then show ?case
    using deriv.OrI1 by blast
next
  case (OrI2 G b a)
  then show ?case
    using deriv.OrI2 by blast
next
  case (OrE G a b c)
  then have "set G \<subseteq> set ps" and "set G \<subseteq> set (a # ps)" and "set G \<subseteq> set (b # ps)"
    by auto
  then have "ps \<turnstile> Or a b" and "a # ps \<turnstile> c" and "b # ps \<turnstile> c"
    using OrE by simp_all
  then show ?case
    using deriv.OrE by blast
next
  case (ImplI a G b)
  then have "set (a # G) \<subseteq> set (a # ps)"
    by auto
  then have "a # ps \<turnstile> b"
    using ImplI by blast
  then show ?case
    using deriv.ImplI by blast
next
  case (ImplE G a b)
  then show ?case
    using deriv.ImplE by blast
next
  case (ForallI G a n)
  obtain fresh where *: "fresh \<notin> (\<Union>a\<in>set ps. params a) \<union> params a \<union> {n}"
    using inf_param finite_params
    by (metis List.finite_set ex_new_if_finite finite.emptyI finite.insertI finite_UN finite_Un)
  
  let ?ps_fresh = "map (psubst (id(n := fresh))) ps"
  have "n \<noteq> fresh"
    using * by blast
  then have **: "n \<notin> (\<Union>a\<in>set ?ps_fresh. params a)"
    using map_psubst_fresh_free * by metis
  then have "set G \<subseteq> set ?ps_fresh"
    using ForallI \<open>n \<noteq> fresh\<close> by (metis (no_types, lifting) list_all_iff psubst_fresh_subset UN_E)
  then have "?ps_fresh \<turnstile> a[App n []/0]"
    using ForallI by blast

  moreover have "list_all (\<lambda>p. n \<notin> params p) ?ps_fresh"
    using ** by (simp add: list_all_iff)
  ultimately have "?ps_fresh \<turnstile> Forall a"
    using \<open>n \<notin> params a\<close> deriv.ForallI by fast
  
  then have "map (psubst (id(fresh := n, n := fresh))) ?ps_fresh
              \<turnstile> psubst (id(fresh := n, n := fresh)) (Forall a)"
    using deriv_swap_param by fast
  moreover have "map (psubst (id(fresh := n))) ?ps_fresh = ps"
    using * map_psubst_fresh_away by fast
  then have "map (psubst (id(fresh := n, n := fresh))) ?ps_fresh = ps"
    by (metis (mono_tags, lifting) ** UN_iff map_eq_conv psubst_upd)
  moreover have  "psubst (id(fresh := n, n := fresh)) (Forall a) = Forall a"
    using * ForallI.hyps(4) by simp
  ultimately show "ps \<turnstile> Forall a"
    by simp
next
  case (ForallE G a t)
  then show ?case
    using deriv.ForallE by blast
next
  case (ForallE' a)
  then show ?case
    using deriv.ForallE' by blast
next
  case (ExistsI G a t)
  then show ?case
    using deriv.ExistsI by blast
next
  case (ExistsE G a n b)
  obtain fresh where *: "fresh \<notin> (\<Union>a\<in>set ps. params a) \<union> params a \<union> params b \<union> {n}"
    using inf_param finite_params
    by (metis List.finite_set ex_new_if_finite finite.emptyI finite.insertI finite_UN finite_Un)
  
  let ?ps_fresh = "map (psubst (id(n := fresh))) ps"
  have "n \<noteq> fresh"
    using * by blast
  then have **: "n \<notin> (\<Union>a\<in>set ?ps_fresh. params a)"
    using map_psubst_fresh_free * by metis
  then have "set G \<subseteq> set ?ps_fresh"
    using ExistsE \<open>n \<noteq> fresh\<close> by (metis (no_types, lifting) list_all_iff psubst_fresh_subset UN_E)
  then have "?ps_fresh \<turnstile> Exists a"
    using ExistsE by blast
      
  moreover have "set (a[App n []/0] # G) \<subseteq> set (a[App n []/0] # ?ps_fresh)"
    using \<open>set G \<subseteq> set ?ps_fresh\<close> by auto
  then have "a[App n []/0] # ?ps_fresh \<turnstile> b"
    using ExistsE by blast
      
  moreover have "list_all (\<lambda>p. n \<notin> params p) ?ps_fresh"
    using ** by (simp add: list_all_iff)
  ultimately have "?ps_fresh \<turnstile> b"
    using \<open>n \<notin> params a\<close> \<open>n \<notin> params b\<close> deriv.ExistsE by fast
  
  then have "map (psubst (id(fresh := n, n := fresh))) ?ps_fresh
              \<turnstile> psubst (id(fresh := n, n := fresh)) b"
    using deriv_swap_param by fast
   moreover have "map (psubst (id(fresh := n))) ?ps_fresh = ps"
    using * map_psubst_fresh_away by fast
  then have "map (psubst (id(fresh := n, n := fresh))) ?ps_fresh = ps"
    by (metis (mono_tags, lifting) ** UN_iff map_eq_conv psubst_upd)
  moreover have  "psubst (id(fresh := n, n := fresh)) b = b"
    using * ExistsE.hyps(7) by simp
  ultimately show "ps \<turnstile> b"
    by simp
qed
  
lemma shift_impl_assum:
  assumes "ps \<turnstile> (Impl p q :: ('a, 'b) form)"
    and "infinite (UNIV :: 'a set)"
  shows "p#ps \<turnstile> q"
proof -
  have "set ps \<subseteq> set (p#ps)"
    by auto
  then have "p#ps \<turnstile> Impl p q"
    using assms deriv_weaken_assumptions by blast
  moreover have "p#ps \<turnstile> p"
    by (simp add: Assum)
  ultimately show "p#ps \<turnstile> q"
    using ImplE by blast
qed

lemma shift_build_impl_assums:
  assumes "ps' \<turnstile> build_impl ps (q :: ('a, 'b) form)"
    and "infinite (UNIV :: 'a set)"
  shows "ps @ ps' \<turnstile> q"
proof -
  have "rev ps @ ps' \<turnstile> q"
    using assms
    by (induct ps arbitrary: ps') (simp_all add: shift_impl_assum)
  then show ?thesis
    by (simp add: deriv_permute_assumptions)
qed
  
theorem deriv_build_impl_assums:
  assumes "infinite (UNIV :: 'a set)"
  shows "[] \<turnstile> build_impl ps q \<Longrightarrow> ps \<turnstile> (q :: ('a, 'b) form)"
  using assms shift_build_impl_assums by fastforce
    
theorem natded_complete':
  assumes mod: "\<forall>e f g. e,(f :: nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm),
    (g :: nat \<Rightarrow> nat hterm list \<Rightarrow> bool), ps \<Turnstile> p"
  shows "ps \<turnstile> p"
proof -
  have "\<forall>e f g. e,(f :: nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm),(g :: nat \<Rightarrow> nat hterm list \<Rightarrow> bool),
          [] \<Turnstile> univ_close (build_impl ps p)"
    using mod valid_univ_close_build_impl by blast
  moreover have "closed 0 (univ_close (build_impl ps p))"
    using closed_univ_close by blast
  ultimately have "[] \<turnstile> univ_close (build_impl ps p)"
    using natded_complete by simp
  then have "[] \<turnstile> build_impl ps p"
    using deriv_remove_univ_close by blast
  then show "ps \<turnstile> p"
    using deriv_build_impl_assums by blast
qed

  
section {* L\"owenheim-Skolem theorem *}

text {*
Another application of the model existence theorem presented in \secref{sec:model-existence}
is the L\"owenheim-Skolem theorem. It says that a set of formulae that is satisfiable in an
{\em arbitrary model} is also satisfiable in a {\em Herbrand model}. The main idea behind the
proof is to show that satisfiable sets are consistent, hence they must be satisfiable in a
Herbrand model.
*}
  
theorem sat_consistency:
  "consistency {S. infinite (- (\<Union>p\<in>S. params p)) \<and> (\<exists>f. \<forall>(p::('a, 'b)form)\<in>S. eval e f g p)}"
  unfolding consistency_def
proof (intro allI impI conjI)
  let ?C = "{S. infinite (- (\<Union>p\<in>S. params p)) \<and> (\<exists>f. \<forall>p \<in> S. eval e f g p)}"
  
  fix S :: "('a, 'b) form set"
  assume "S \<in> ?C"
  then have inf_params: "infinite (- (\<Union>p\<in>S. params p))"
    and "\<exists>f. \<forall>p \<in> S. eval e f g p"
    by blast+
  then obtain f where *: "\<forall>x \<in> S. eval e f g x" by blast
    
  { fix p ts
    show "\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)"
    proof
      assume "Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S"
      then have "eval e f g (Pred p ts) \<and> eval e f g (Neg (Pred p ts))"
        using * by blast
      then show False by simp
    qed }
    
  show "FF \<notin> S"
    using * by fastforce
      
  show "Neg TT \<notin> S"
    using * by fastforce
      
  { fix Z
    assume "Neg (Neg Z) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (Neg Z)}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {Z}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {Z}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {Z} \<in> ?C"
      by blast }
    
  { fix A B
    assume "And A B \<in> S"
    then have "\<forall>x \<in> S \<union> {And A B}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {A, B}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {A, B}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {A, B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (Or A B) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (Or A B)}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {Neg A, Neg B}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {Neg A, Neg B}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {Neg A, Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (Impl A B) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (Impl A B)}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {A, Neg B}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {A, Neg B}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {A, Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Or A B \<in> S"
    then have "\<forall>x \<in> S \<union> {Or A B}. eval e f g x"
      using * by blast
    then have "(\<forall>x \<in> S \<union> {A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. eval e f g x)"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {A}. params p))"
      and "infinite (- (\<Union>p \<in> S \<union> {B}. params p))"
      using inf_params by simp_all
    ultimately show "S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Neg (And A B) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (And A B)}. eval e f g x"
      using * by blast
    then have "(\<forall>x \<in> S \<union> {Neg A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {Neg B}. eval e f g x)"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))"
      and "infinite (- (\<Union>p \<in> S \<union> {Neg B}. params p))"
      using inf_params by simp_all
    ultimately show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C"
      by blast }
    
  { fix A B
    assume "Impl A B \<in> S"
    then have "\<forall>x \<in> S \<union> {Impl A B}. eval e f g x"
      using * by blast
    then have "(\<forall>x \<in> S \<union> {Neg A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. eval e f g x)"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))"
      and "infinite (- (\<Union>p \<in> S \<union> {B}. params p))"
      using inf_params by simp_all
    ultimately show "S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C"
      by blast }

  { fix P and t :: "'a term"
    assume "Forall P \<in> S"
    then have "\<forall>x \<in> S \<union> {Forall P}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {P[t/0]}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {P[t/0]}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {P[t/0]} \<in> ?C"
      by blast }
    
  { fix P and t :: "'a term"
    assume "Neg (Exists P) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (Exists P)}. eval e f g x"
      using * by blast
    then have "\<forall>x \<in> S \<union> {Neg (P[t/0])}. eval e f g x"
      by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {Neg (P[t/0])}. params p))"
      using inf_params by simp
    ultimately show "S \<union> {Neg (P[t/0])} \<in> ?C"
      by blast }
    
  { fix P
    assume "Exists P \<in> S"
    then have "\<forall>x \<in> S \<union> {Exists P}. eval e f g x"
      using * by blast
    then have "eval e f g (Exists P)"
      by blast
    then obtain z where "eval (e\<langle>0:z\<rangle>) f g P"
      by auto
    moreover obtain x where **: "x \<in> - (\<Union>p \<in> S. params p)"
      using inf_params infinite_imp_nonempty by blast
    then have "x \<notin> params P"
      using \<open>Exists P \<in> S\<close> by auto
    ultimately have "eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P"
      by simp
    moreover have "\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p"
      using * ** by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {P[App x []/0]}. params p))"
      using inf_params by simp
    ultimately have "S \<union> {P[App x []/0]} \<in>
                      {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p)}"
      by simp
    then show "\<exists>x. S \<union> {P[App x []/0]} \<in> ?C"
      by blast }
    
  { fix P
    assume "Neg (Forall P) \<in> S"
    then have "\<forall>x \<in> S \<union> {Neg (Forall P)}. eval e f g x"
      using * by blast
    then have "eval e f g (Neg (Forall P))"
      by blast
    then obtain z where "\<not> eval (e\<langle>0:z\<rangle>) f g P"
      by auto
    moreover obtain x where **: "x \<in> - (\<Union>p \<in> S. params p)"
      using inf_params infinite_imp_nonempty by blast
    then have "x \<notin> params P"
      using \<open>Neg (Forall P) \<in> S\<close> by auto
    ultimately have "\<not> eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P"
      by simp
    moreover have "\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p"
      using * ** by simp
    moreover have "infinite (- (\<Union>p \<in> S \<union> {P[App x []/0]}. params p))"
      using inf_params by simp
    ultimately have "S \<union> {Neg (P[App x []/0])} \<in>
                      {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p)}"
      by simp
    then show "\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C"
      by blast }
qed

theorem doublep_evalt [simp]:
  "evalt e f (psubstt (\<lambda>n::nat. 2 * n) t) = evalt e (\<lambda>n. f (2*n)) t"
  "evalts e f (psubstts (\<lambda>n::nat. 2 * n) ts) = evalts e (\<lambda>n. f (2*n)) ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem doublep_eval: "\<And>e. eval e f g (psubst (\<lambda>n::nat. 2 * n) p) =
  eval e (\<lambda>n. f (2*n)) g p"
  by (induct p) simp_all

theorem doublep_infinite_params:
  "infinite (- (\<Union>p \<in> psubst (\<lambda>n::nat. 2 * n) ` S. params p))"
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

theorem loewenheim_skolem:
  assumes evalS: "\<forall>p\<in>S. eval e f g p"
  shows "\<forall>p\<in>S. closed 0 p \<longrightarrow> eval e' (\<lambda>n. HApp (2*n)) (\<lambda>a ts.
      Pred a (terms_of_hterms ts) \<in> Extend (psubst (\<lambda>n. 2 * n) ` S)
        (mk_finite_char (mk_alt_consistency (close
          {S. infinite (- (\<Union>p\<in>S. params p)) \<and> (\<exists>f. \<forall>p\<in>S. eval e f g p)}))) from_nat) p"
  (is "\<forall>_\<in>_. _ _ _ \<longrightarrow> eval _ _ ?g _")
  using evalS
proof (intro ballI impI)
  fix p
    
  let ?C = "{S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>x \<in> S. eval e f g x)}"
    
  assume "p \<in> S"
    and "closed 0 p"
  then have "eval e f g p"
    using evalS by blast
  then have "\<forall>x \<in> S. eval e f g x"
    using evalS by blast
  then have "\<forall>p \<in> psubst (op * 2) ` S. eval e (\<lambda>n. f (n div 2)) g p"
    by (simp add: doublep_eval)
  then have "psubst (op * 2) ` S \<in> ?C"
    using doublep_infinite_params by blast
  moreover have "psubst (op * 2) p \<in> psubst (op * 2) ` S"
    using \<open>p \<in> S\<close> by blast
  moreover have "closed 0 (psubst (op * 2) p)"
    using \<open>closed 0 p\<close> by simp
  moreover have "consistency ?C"
    using sat_consistency by blast
  ultimately have "eval e' HApp ?g (psubst (op * 2) p)"
    using model_existence by blast
  then show "eval e' (\<lambda>n. HApp (2 * n)) ?g p"
    using doublep_eval by blast
qed

end
