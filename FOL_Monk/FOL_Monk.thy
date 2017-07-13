(*
  FOL-Monk - First-Order Logic According to Monk

  Author: John Bruntse Larsen
*)

theory FOL_Monk imports Main
begin

section \<open>Syntax of first-order logic\<close>

datatype form = Pre string nat | Eq nat nat | Neg form | Imp form form | Uni nat form

abbreviation (input) "Falsity \<equiv> Uni 0 (Neg (Eq 0 0))"

abbreviation (input) "Truth \<equiv> Neg Falsity"

section \<open>Semantics of first-order logic\<close>

fun vars :: "nat \<Rightarrow> nat list"
  where
    "vars 0 = []" |
    "vars n = (vars (n-1)) @ [n-1]"

fun semantics :: "(nat \<Rightarrow> 'a) \<Rightarrow> (string \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
  where
    "semantics e g (Eq x y) \<longleftrightarrow> (e x) = (e y)" |
    "semantics e g (Pre p n) \<longleftrightarrow> g p (map e (vars n))" |
    "semantics e g (Neg f) \<longleftrightarrow> \<not> semantics e g f" |
    "semantics e g (Imp p q) \<longleftrightarrow> (semantics e g p \<longrightarrow> semantics e g q)" |
    "semantics e g (Uni x p) \<longleftrightarrow> (\<forall>t. (semantics (e(x := t)) g p))"

section \<open>Definition of rules and axioms\<close>

fun not_occurs_in :: "nat \<Rightarrow> form \<Rightarrow> bool"
  where
    "not_occurs_in x (Pre _ arity) \<longleftrightarrow> x \<ge> arity" |
    "not_occurs_in x (Eq y z) \<longleftrightarrow> x \<noteq> y \<and> x \<noteq> z " |
    "not_occurs_in x (Neg p) \<longleftrightarrow> not_occurs_in x p" |
    "not_occurs_in x (Imp p q) \<longleftrightarrow> not_occurs_in x p \<and> not_occurs_in x q" |
    "not_occurs_in x (Uni y p) \<longleftrightarrow> (x \<noteq> y \<and> not_occurs_in x p)"

corollary not_occurs_falsity: "not_occurs_in 1 Falsity"
  by simp

proposition "x \<noteq> y \<and> x \<noteq> z \<longrightarrow> not_occurs_in x (Eq y z)"
  by simp

proposition "not_occurs_in x p \<longrightarrow> not_occurs_in x (Neg p)"
  by simp

proposition "not_occurs_in x p \<and> not_occurs_in x q \<longrightarrow> not_occurs_in x (Imp p q)"
  by simp

proposition "x \<noteq> y \<and> not_occurs_in x p \<longrightarrow> not_occurs_in x (Uni y p)"
  by simp

datatype "thm" = Thm (concl: form)

abbreviation (input) "fail_thm \<equiv> Thm Truth"

definition modusponens :: "thm \<Rightarrow> thm \<Rightarrow> thm"
  where
    "modusponens s s' \<equiv> case concl s of Imp p q \<Rightarrow>
      let p' = concl s' in if p = p' then Thm q else fail_thm | _ \<Rightarrow> fail_thm"

definition gen :: "nat \<Rightarrow> thm \<Rightarrow> thm"
  where
    "gen x a \<equiv> Thm (Uni x (concl a))"

definition c1 :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> thm"
  where
    "c1 p q r \<equiv> Thm (Imp (Imp p q) (Imp (Imp q r) (Imp p r)))"

definition c2 :: "form \<Rightarrow> thm"
  where
    "c2 p \<equiv> Thm (Imp (Imp (Neg p) p) p)"

definition c3 :: "form \<Rightarrow> form \<Rightarrow> thm"
  where
    "c3 p q \<equiv> Thm (Imp p (Imp (Neg p) q))"

definition c4 :: "nat \<Rightarrow> form \<Rightarrow> form \<Rightarrow> thm"
  where
    "c4 x p q \<equiv> Thm (Imp (Uni x (Imp p q)) (Imp (Uni x p) (Uni x q)))"

definition c5_1 :: "nat \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_1 x p \<equiv> if not_occurs_in x p then Thm (Imp p (Uni x p)) else fail_thm"

definition c5_2 :: "nat \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_2 x p \<equiv> Thm (Imp (Neg (Uni x p)) (Uni x (Neg (Uni x p))))"

definition c5_3 :: "nat \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_3 x y p \<equiv> Thm (Imp (Uni x (Uni y p)) (Uni y (Uni x p)))"

definition c6 :: "nat \<Rightarrow> nat \<Rightarrow> thm"
  where
    "c6 x y \<equiv> if x \<noteq> y then Thm (Neg (Uni x (Neg (Eq x y)))) else fail_thm"

definition c7 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> thm"
  where
    "c7 x y z \<equiv> Thm (Imp (Eq x y) (Imp (Eq x z) (Eq y z)))"

definition c8 :: "nat \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> thm"
  where
    "c8 x y p \<equiv> if x \<noteq> y then Thm (Imp (Eq x y) (Imp p (Uni x (Imp (Eq x y) p)))) else fail_thm"

section \<open>Definition of proof system\<close>

inductive OK :: "form \<Rightarrow> bool" ("\<turnstile> _" 0)
  where
    case_modusponens:
    "\<turnstile> concl f \<Longrightarrow> \<turnstile> concl f' \<Longrightarrow> \<turnstile> concl (modusponens f f')" |
    case_gen:
    "\<turnstile> concl f \<Longrightarrow> \<turnstile> concl (gen _ f)" |
    case_c1:
    "\<turnstile> concl (c1 _ _ _)" |
    case_c2:
    "\<turnstile> concl (c2 _)" |
    case_c3:
    "\<turnstile> concl (c3 _ _)" |
    case_c4:
    "\<turnstile> concl (c4 _ _ _)" |
    case_c5_1:
    "\<turnstile> concl (c5_1 _ _)" |
    case_c5_2:
    "\<turnstile> concl (c5_2 _ _)" |
    case_c5_3:
    "\<turnstile> concl (c5_3 _ _ _)" |
    case_c6:
    "\<turnstile> concl (c6 _ _)" |
    case_c7:
    "\<turnstile> concl (c7 _ _ _)" |
    case_c8:
    "\<turnstile> concl (c8 _ _ _)"

proposition "\<turnstile> Truth"
  by (metis OK.simps c8_def thm.sel)

section \<open>Soundness of proof system\<close>

corollary sound_c1_1: "\<turnstile> concl (c1 p q r) \<Longrightarrow> semantics e g (concl (c1 p q r))"
  by (simp add: c1_def)

lemma "semantics e g (concl (c1 p q r))"
  by (simp add: case_c1 sound_c1_1)

lemma update_identity: "e x = e y \<longrightarrow> semantics e g p \<longrightarrow> semantics (e(x := e y)) g p"
  by (simp add: fun_upd_idem)

lemma frame_property: "not_occurs_in x p \<Longrightarrow> semantics e g p \<Longrightarrow> semantics (e(x := t)) g p"
  sorry

lemmas defs = c1_def c2_def c3_def c4_def c5_1_def c5_2_def c5_3_def c6_def c7_def c8_def

theorem soundness: "\<turnstile> p \<Longrightarrow> semantics e g p"
  apply (induction rule: OK.induct)
             defer
             defer
             apply (simp_all add: defs update_identity frame_property)
    apply (metis fun_upd_twist)
  sorry

corollary "\<not> (\<turnstile> Falsity)"
  using soundness
  by fastforce

end
