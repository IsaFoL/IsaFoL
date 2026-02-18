(*
  FOL-Monk - First-Order Logic According to Monk

  Authors: Asta Halkjær Boserup, John Bruntse Larsen, Anders Schlichtkrull & Jørgen Villadsen
*)

theory FOL_Monk imports Main begin

section \<open>Syntax of First-Order Logic\<close>

type_synonym proxy = "unit list"

type_synonym arity = proxy

type_synonym var = proxy

datatype form = Pre proxy arity | Eq var var | Neg form | Imp form form | Uni var form

abbreviation "Truth \<equiv> Uni [] (Eq [] [])"

abbreviation "Falsity \<equiv> Neg Truth"

section \<open>Semantics of First-Order Logic\<close>

primrec eval :: "(var \<Rightarrow> 'a) \<Rightarrow> arity \<Rightarrow> 'a list"
  where
    "eval _ [] = []" |
    "eval e (_ # n) = e n # eval e n"

primrec semantics :: "(var \<Rightarrow> 'a) \<Rightarrow> (proxy \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
  where
    "semantics e g (Pre i n) = g i (eval e n)" |
    "semantics e g (Eq x y) = (e x = e y)" |
    "semantics e g (Neg p) = (\<not> semantics e g p)" |
    "semantics e g (Imp p q) = (semantics e g p \<longrightarrow> semantics e g q)" |
    "semantics e g (Uni x p) = (\<forall>t. semantics (e(x := t)) g p)"

section \<open>Definition of Rules and Axioms\<close>

primrec no_occur_in :: "var \<Rightarrow> form \<Rightarrow> bool"
  where
    "no_occur_in z (Pre _ n) = (length z \<ge> length n)" |
    "no_occur_in z (Eq x y) = (z \<noteq> x \<and> z \<noteq> y)" |
    "no_occur_in z (Neg p) = no_occur_in z p" |
    "no_occur_in z (Imp p q) = (no_occur_in z p \<and> no_occur_in z q)" |
    "no_occur_in z (Uni _ p) = no_occur_in z p"

abbreviation (input) "fail \<equiv> Truth"

definition modusponens :: "form \<Rightarrow> form \<Rightarrow> form"
  where
    "modusponens pq p \<equiv> case pq of Imp p' q \<Rightarrow> if p' = p then q else fail | _ \<Rightarrow> fail"

definition gen :: "var \<Rightarrow> form \<Rightarrow> form"
  where
    "gen x p \<equiv> Uni x p"

definition c1 :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form"
  where
    "c1 p q r \<equiv> Imp (Imp p q) (Imp (Imp q r) (Imp p r))"

definition c2 :: "form \<Rightarrow> form"
  where
    "c2 p \<equiv> Imp (Imp (Neg p) p) p"

definition c3 :: "form \<Rightarrow> form \<Rightarrow> form"
  where
    "c3 p q \<equiv> Imp p (Imp (Neg p) q)"

definition c4 :: "var \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form"
  where
    "c4 x p q \<equiv> Imp (Uni x (Imp p q)) (Imp (Uni x p) (Uni x q))"

definition c5_1 :: "var \<Rightarrow> form \<Rightarrow> form"
  where
    "c5_1 x p \<equiv> if no_occur_in x p then Imp p (Uni x p) else fail"

definition c5_2 :: "var \<Rightarrow> form \<Rightarrow> form"
  where
    "c5_2 x p \<equiv> Imp (Neg (Uni x p)) (Uni x (Neg (Uni x p)))"

definition c5_3 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> form"
  where
    "c5_3 x y p \<equiv> Imp (Uni x (Uni y p)) (Uni y (Uni x p))"

definition c6 :: "var \<Rightarrow> var \<Rightarrow> form"
  where
    "c6 x y \<equiv> Neg (Uni x (Neg (Eq x y)))"

definition c7 :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> form"
  where
    "c7 x y z \<equiv> Imp (Eq x y) (Imp (Eq x z) (Eq y z))"

definition c8 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> form"
  where
    "c8 x y p \<equiv> if x \<noteq> y then Imp (Eq x y) (Imp p (Uni x (Imp (Eq x y) p))) else fail"

section \<open>Definition of Proof System\<close>

inductive OK :: "form \<Rightarrow> bool" ("\<turnstile> _" 0)
  where
    case_modusponens:
    "\<turnstile> pq \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> modusponens pq p" |
    case_gen:
    "\<turnstile> p \<Longrightarrow> \<turnstile> gen _ p" |
    case_c1:
    "\<turnstile> c1 _ _ _" |
    case_c2:
    "\<turnstile> c2 _" |
    case_c3:
    "\<turnstile> c3 _ _" |
    case_c4:
    "\<turnstile> c4 _ _ _" |
    case_c5_1:
    "\<turnstile> c5_1 _ _" |
    case_c5_2:
    "\<turnstile> c5_2 _ _" |
    case_c5_3:
    "\<turnstile> c5_3 _ _ _" |
    case_c6:
    "\<turnstile> c6 _ _" |
    case_c7:
    "\<turnstile> c7 _ _ _" |
    case_c8:
    "\<turnstile> c8 _ _ _"

theorem truth: "\<turnstile> Truth"
  using c8_def case_c8 by metis

section \<open>Soundness of Proof System\<close>

lemma eval_bound: "length x \<ge> length n \<Longrightarrow> eval e n = eval (e(x := t)) n"
  by (induct n) auto

lemma frame_property: "no_occur_in x p \<Longrightarrow> semantics e g p = semantics (e(x := t)) g p"
proof (induct p arbitrary: e)
  case Pre
  then show ?case using eval_bound
    by (metis no_occur_in.simps(1) semantics.simps(1))
next
  case Eq
  then show ?case by fastforce
next
  case Neg
  then show ?case by simp
next
  case Imp
  then show ?case by simp
next
  case Uni
  then show ?case by (metis fun_upd_twist fun_upd_upd no_occur_in.simps(5) semantics.simps(5))
qed

lemma commute_uni: "semantics e g (Uni x (Uni y p)) \<Longrightarrow> semantics e g (Uni y (Uni x p))"
  by (metis fun_upd_twist semantics.simps(5))

lemma sound_c8:
  assumes "x \<noteq> y" "semantics e g (Eq x y)" "semantics e g p"
  shows "semantics e g (Uni x (Imp (Eq x y) p))"
proof -
  have "semantics (e(x := t)) g (Imp (Eq x y) p)" for t
  proof (cases "e y = t")
    case True
    then have "semantics (e(x := t)) g (Eq x y)"
      by simp
    then show ?thesis
      using assms True by auto
  next
    case False
    then show ?thesis
      using assms by simp
  qed
  then show ?thesis
    by simp
qed

lemma sound_modusponens[simp]:
  "semantics e g pq \<Longrightarrow> semantics e g p \<Longrightarrow> semantics e g (modusponens pq p)"
  unfolding modusponens_def by (cases pq) simp_all

theorem soundness: "\<turnstile> p \<Longrightarrow> semantics e g p"
proof (induct p arbitrary: e rule: OK.induct)
  case case_c5_1
  then show ?case
    unfolding c5_1_def using frame_property by fastforce
next
  case case_c5_3
  then show ?case
    unfolding c5_3_def using commute_uni by (metis semantics.simps(4))
next
  case case_c8
  then show ?case
    unfolding c8_def using sound_c8 by simp blast
qed (unfold gen_def c1_def c2_def c3_def c4_def c5_2_def c6_def c7_def, simp_all)

corollary "\<not> (\<turnstile> Falsity)"
  using soundness by fastforce

typedef "thm" = "{p. \<turnstile> p}" using truth by fast

definition "concl \<equiv> Rep_thm"

declare concl_def[simp]

proposition "\<turnstile> concl s"
  using Rep_thm by simp

proposition "\<exists>s. concl s = Truth"
  using truth Abs_thm_inverse by fastforce

setup_lifting type_definition_thm

lift_definition xmodusponens :: "thm \<Rightarrow> thm \<Rightarrow> thm" is modusponens using OK.case_modusponens .

lift_definition xgen :: "var \<Rightarrow> thm \<Rightarrow> thm" is gen using OK.case_gen .

lift_definition xc1 :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> thm" is c1 using OK.case_c1 .

lift_definition xc2 :: "form \<Rightarrow> thm" is c2 using OK.case_c2 .

lift_definition xc3 :: "form \<Rightarrow> form \<Rightarrow> thm" is c3 using OK.case_c3 .

lift_definition xc4 :: "var \<Rightarrow> form \<Rightarrow> form \<Rightarrow> thm" is c4 using OK.case_c4 .

lift_definition xc5_1 :: "var \<Rightarrow> form \<Rightarrow> thm" is c5_1 using OK.case_c5_1 .

lift_definition xc5_2 :: "var \<Rightarrow> form \<Rightarrow> thm" is c5_2 using OK.case_c5_2 .

lift_definition xc5_3 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> thm" is c5_3 using OK.case_c5_3 .

lift_definition xc6 :: "var \<Rightarrow> var \<Rightarrow> thm" is c6 using OK.case_c6 .

lift_definition xc7 :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> thm" is c7 using OK.case_c7 .

lift_definition xc8 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> thm" is c8 using OK.case_c8 .

export_code
  xmodusponens xgen xc1 xc2 xc3 xc4 xc5_1 xc5_2 xc5_3 xc6 xc7 xc8 concl
  in SML module_name X

code_reflect X datatypes form = _ functions
  xmodusponens xgen xc1 xc2 xc3 xc4 xc5_1 xc5_2 xc5_3 xc6 xc7 xc8 concl

ML \<open> open X \<close>

ML_val \<open> concl (xgen [] (xc1
  (Pre ([], []))
  (Pre ([()], []))
  (Pre ([(),()], [])))) \<close>

theorem soundness_thm: "semantics e g (concl s)"
  using Rep_thm soundness by fastforce

corollary "concl s \<noteq> Falsity"
proof
  assume "concl s = Falsity"
  then have "semantics id g Falsity" for g
    using soundness_thm by metis
  then show False
    by simp
qed

end
