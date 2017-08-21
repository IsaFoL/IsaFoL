(*
  FOL-Monk - First-Order Logic According to Monk

  Author: John Bruntse Larsen, Andreas Halkjær From & Jørgen Villadsen
*)

theory FOL_Monk imports Main
begin

section \<open>Syntax of First-Order Logic\<close>

type_synonym arity = nat

type_synonym var = nat

datatype form = Pre string arity | Eq var var | Neg form | Imp form form | Uni var form

abbreviation (input) "Falsity \<equiv> Uni 0 (Neg (Eq 0 0))"

abbreviation (input) "Truth \<equiv> Neg Falsity"

section \<open>Semantics of First-Order Logic\<close>

primrec vars :: "arity \<Rightarrow> var list"
  where
    "vars 0 = []" |
    "vars (Suc n) = vars n @ [n]"

primrec semantics :: "(var \<Rightarrow> 'a) \<Rightarrow> (string \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"
  where
    "semantics e g (Pre i n) = g i (map e (vars n))" |
    "semantics e g (Eq x y) = (e x = e y)" |
    "semantics e g (Neg p) = (\<not> semantics e g p)" |
    "semantics e g (Imp p q) = (semantics e g p \<longrightarrow> semantics e g q)" |
    "semantics e g (Uni x p) = (\<forall>t. semantics (e(x := t)) g p)"

section \<open>Definition of Rules and Axioms\<close>

primrec not_occurs_in :: "var \<Rightarrow> form \<Rightarrow> bool"
  where
    "not_occurs_in x (Pre _ n) = (x \<ge> n)" |
    "not_occurs_in x (Eq y z) = (x \<noteq> y \<and> x \<noteq> z)" |
    "not_occurs_in x (Neg p) = not_occurs_in x p" |
    "not_occurs_in x (Imp p q) = (not_occurs_in x p \<and> not_occurs_in x q)" |
    "not_occurs_in x (Uni y p) = (x \<noteq> y \<and> not_occurs_in x p)"

datatype "thm" = Thm (concl: form)

abbreviation (input) "fail_thm \<equiv> Thm Truth"

definition modusponens :: "thm \<Rightarrow> thm \<Rightarrow> thm"
  where
    "modusponens s s' \<equiv> case concl s of Imp p q \<Rightarrow>
      let p' = concl s' in if p = p' then Thm q else fail_thm | _ \<Rightarrow> fail_thm"

definition gen :: "var \<Rightarrow> thm \<Rightarrow> thm"
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

definition c4 :: "var \<Rightarrow> form \<Rightarrow> form \<Rightarrow> thm"
  where
    "c4 x p q \<equiv> Thm (Imp (Uni x (Imp p q)) (Imp (Uni x p) (Uni x q)))"

definition c5_1 :: "var \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_1 x p \<equiv> if not_occurs_in x p then Thm (Imp p (Uni x p)) else fail_thm"

definition c5_2 :: "var \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_2 x p \<equiv> Thm (Imp (Neg (Uni x p)) (Uni x (Neg (Uni x p))))"

definition c5_3 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> thm"
  where
    "c5_3 x y p \<equiv> Thm (Imp (Uni x (Uni y p)) (Uni y (Uni x p)))"

definition c6 :: "var \<Rightarrow> var \<Rightarrow> thm"
  where
    "c6 x y \<equiv> Thm (Neg (Uni x (Neg (Eq x y))))"

definition c7 :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> thm"
  where
    "c7 x y z \<equiv> Thm (Imp (Eq x y) (Imp (Eq x z) (Eq y z)))"

definition c8 :: "var \<Rightarrow> var \<Rightarrow> form \<Rightarrow> thm"
  where
    "c8 x y p \<equiv> if x \<noteq> y then Thm (Imp (Eq x y) (Imp p (Uni x (Imp (Eq x y) p)))) else fail_thm"

section \<open>Definition of Proof System\<close>

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
   using case_c6 unfolding c6_def by simp

section \<open>Soundness of Proof System\<close>

lemma vars_bound: "x \<ge> n \<Longrightarrow> map e (vars n) = map (e(x := t)) (vars n)"
  by (induct n) simp_all

lemma frame_property: "not_occurs_in x p \<Longrightarrow> semantics e g p = semantics (e(x := t)) g p"
proof (induct p arbitrary: e)
  case (Pre _ n)
  then have "x \<ge> n"
    by simp
  then show ?case
    using vars_bound by (metis semantics.simps(1))
qed (simp_all add: fun_upd_twist)

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

lemma sound_modusponens:
  "semantics e g (concl f) \<Longrightarrow> semantics e g (concl f') \<Longrightarrow>
  semantics e g (concl (modusponens f f'))"
  unfolding modusponens_def by (cases "concl f") simp_all

theorem soundness: "\<turnstile> p \<Longrightarrow> semantics e g p"
proof (induct p arbitrary: e rule: OK.induct)
  case case_modusponens
  then show ?case
    using sound_modusponens by fast
next
  case case_c5_1
  then show ?case
    unfolding c5_1_def using frame_property by fastforce
next
  case case_c5_3
  then show ?case
    unfolding c5_3_def using commute_uni by fastforce
next
  case case_c8
  then show ?case
    unfolding c8_def using sound_c8 by simp blast
qed (simp_all add: gen_def c1_def c2_def c3_def c4_def c5_2_def c6_def c7_def)

corollary "\<not> (\<turnstile> Falsity)"
  using soundness by fastforce

end
