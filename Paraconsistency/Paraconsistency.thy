(* Anders Schlichtkrull & Jørgen Villadsen, DTU Compute, Denmark *)

chapter \<open>On Paraconsistency\<close>

text
\<open>
Paraconsistency concerns inference systems that do not explode given a contradiction.

The Internet Encyclopedia of Philosophy has a survey article on paraconsistent logic.

The following Isabelle theory formalizes a specific paraconsistent many-valued logic.
\<close>

theory Paraconsistency imports Main
  abbrevs
    "Truth" = "\<^bold>\<top>"
    and
    "Falsity" = "\<^bold>\<bottom>"
    and
    "Neg'" = "\<^bold>\<not>"
    and
    "Con'" = "\<^bold>\<and>"
    and
    "Eql" = "\<^bold>\<Leftrightarrow>"
    and
    "Eql'" = "\<^bold>\<leftrightarrow>"
    and
    "Dis'" = "\<^bold>\<or>"
    and
    "Imp" = "\<^bold>\<Rightarrow>"
    and
    "Imp'" = "\<^bold>\<rightarrow>"
    and
    "Box" = "\<^bold>\<box>"
    and
    "Neg" = "\<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown>"
    and
    "Con" = "\<^bold>\<and>\<^bold>\<and>"
    and
    "Dis" = "\<^bold>\<or>\<^bold>\<or>"
    and
    "Cla" = "\<^bold>\<Delta>"
    and
    "Nab" = "\<^bold>\<nabla>"
    and
    "CON" = "[\<^bold>\<and>\<^bold>\<and>]"
    and
    "DIS" = "[\<^bold>\<or>\<^bold>\<or>]"
    and
    "NAB" = "[\<^bold>\<nabla>]"
    and
    "ExiEql" = "[\<^bold>\<exists>\<^bold>=]"
begin

text
\<open>
The details about our logic are in our article in a special issue on logical approaches to
paraconsistency in the Journal of Applied Non-Classical Logics (Volume 15, Number 1, 2005).
\<close>

section \<open>Syntax and Semantics\<close>

subsection \<open>Syntax of Propositional Logic\<close>

text
\<open>
Only the primed operators return indeterminate truth values.
\<close>

type_synonym id = string

datatype fm = Pro id | Truth | Neg' fm | Con' fm fm | Eql fm fm | Eql' fm fm
term "[]"
notation Pro ("\<langle>_\<rangle>" [39] 39)
notation Truth ("\<^bold>\<top>")
notation Neg' ("\<^bold>\<not> _" [40] 40)
notation Con' (infixr "\<^bold>\<and>" 35)
notation Eql (infixr "\<^bold>\<Leftrightarrow>" 25)
notation Eql' (infixr "\<^bold>\<leftrightarrow>" 25)

abbreviation Falsity :: fm ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<^bold>\<not> \<^bold>\<top>"

abbreviation Dis' :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<or>" 30) where
  "p \<^bold>\<or> q \<equiv> \<^bold>\<not> (\<^bold>\<not> p \<^bold>\<and> \<^bold>\<not> q)"

abbreviation Imp :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<Rightarrow>" 25) where
  "p \<^bold>\<Rightarrow> q \<equiv> p \<^bold>\<Leftrightarrow> (p \<^bold>\<and> q)"

abbreviation Imp' :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<rightarrow>" 25) where
  "p \<^bold>\<rightarrow> q \<equiv> p \<^bold>\<leftrightarrow> (p \<^bold>\<and> q)"

abbreviation Box :: "fm \<Rightarrow> fm" ("\<^bold>\<box> _" [40] 40) where
  "\<^bold>\<box> p \<equiv> p \<^bold>\<Leftrightarrow> \<^bold>\<top>"

abbreviation Neg :: "fm \<Rightarrow> fm" ("\<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown> _" [40] 40) where
  "\<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown> p \<equiv> \<^bold>\<box> (\<^bold>\<not> p)"

abbreviation Con :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<and>\<^bold>\<and>" 35) where
  "p \<^bold>\<and>\<^bold>\<and> q \<equiv> \<^bold>\<box> (p \<^bold>\<and> q)"

abbreviation Dis :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infixr "\<^bold>\<or>\<^bold>\<or>" 30) where
  "p \<^bold>\<or>\<^bold>\<or> q \<equiv> \<^bold>\<box> (p \<^bold>\<or> q)"

abbreviation Cla :: "fm \<Rightarrow> fm" ("\<^bold>\<Delta> _" [40] 40) where
  "\<^bold>\<Delta> p \<equiv> (\<^bold>\<box> p) \<^bold>\<or>\<^bold>\<or> (p \<^bold>\<Leftrightarrow> \<^bold>\<bottom>)"

abbreviation Nab :: "fm \<Rightarrow> fm" ("\<^bold>\<nabla> _" [40] 40) where
  "\<^bold>\<nabla> p \<equiv> \<^bold>\<rightharpoondown>\<^bold>\<rightharpoondown> (\<^bold>\<Delta> p)"

subsection \<open>Semantics of Propositional Logic\<close>

text
\<open>
There is a countably infinite number of indeterminate truth values.
\<close>

datatype tv = Det bool | Indet nat

abbreviation DetTrue :: tv ("\<bullet>") where "\<bullet> \<equiv> Det True"
abbreviation DetFalse :: tv ("\<circ>") where "\<circ> \<equiv> Det False"
notation Indet ("\<lfloor>_\<rfloor>" [39] 39)

abbreviation (input) eval_neg :: "tv \<Rightarrow> tv"
where
  "eval_neg x \<equiv>
    (
      case x of
        Det False \<Rightarrow> Det True |
        Det True \<Rightarrow> Det False |
        Indet n \<Rightarrow> Indet n
    )"

fun eval :: "(id \<Rightarrow> tv) \<Rightarrow> fm \<Rightarrow> tv"
where
  "eval i (\<langle>s\<rangle>) = i s" |
  "eval i \<^bold>\<top> = Det True" |
  "eval i (\<^bold>\<not> p) = eval_neg (eval i p)" |
  "eval i (p \<^bold>\<and> q) =
    (
      if eval i p = eval i q then eval i p else
      if eval i p = Det True then eval i q else
      if eval i q = Det True then eval i p else Det False
    )" |
  "eval i (p \<^bold>\<Leftrightarrow> q) =
    (
      if eval i p = eval i q then Det True else Det False
    )" |
  "eval i (p \<^bold>\<leftrightarrow> q) =
    (
      if eval i p = eval i q then Det True else
        (
          case (eval i p, eval i q) of
            (Det True, _) \<Rightarrow> eval i q |
            (_, Det True) \<Rightarrow> eval i p |
            (Det False, _) \<Rightarrow> eval_neg (eval i q) |
            (_, Det False) \<Rightarrow> eval_neg (eval i p) |
            _ \<Rightarrow> Det False
        )
    )"

lemma eval_equality_simplify: "eval i (Eql p q) = Det (eval i p = eval i q)"
  by simp

theorem eval_equality:
  "eval i (Eql' p q) =
    (
      if eval i p = eval i q then Det True else
      if eval i p = Det True then eval i q else
      if eval i q = Det True then eval i p else
      if eval i p = Det False then eval i (Neg' q) else
      if eval i q = Det False then eval i (Neg' p) else
      Det False
    )"
  by (cases "eval i p"; cases "eval i q") simp_all

theorem eval_negation:
  "eval i (Neg' p) =
    (
      if eval i p = Det False then Det True else
      if eval i p = Det True then Det False else
      eval i p
    )"
  by (cases "eval i p") simp_all

corollary "eval i (Cla p) = eval i (Box (Dis' p (Neg' p)))"
  using eval_negation
  by simp

lemma double_negation: "eval i p = eval i (Neg' (Neg' p))"
  using eval_negation
  by simp

subsection \<open>Validity and Consistency\<close>

text
\<open>
Validity gives the set of theorems and the logic has at least a theorem and a non-theorem.
\<close>

definition valid :: "fm \<Rightarrow> bool"
where
  "valid p \<equiv> \<forall>i. eval i p = \<bullet>"

proposition "valid Truth" and "\<not> valid Falsity"
  unfolding valid_def
  by simp_all

section \<open>Truth Tables\<close>

subsection \<open>String Functions\<close>

text
\<open>
The following functions support arbitrary unary and binary truth tables.
\<close>

definition tv_pair_row :: "tv list \<Rightarrow> tv \<Rightarrow> (tv * tv) list"
where
  "tv_pair_row tvs tv \<equiv> map (\<lambda>x. (tv, x)) tvs"

definition tv_pair_table :: "tv list \<Rightarrow> (tv * tv) list list"
where
  "tv_pair_table tvs \<equiv> map (tv_pair_row tvs) tvs"

definition map_row :: "(tv \<Rightarrow> tv \<Rightarrow> tv) \<Rightarrow> (tv * tv) list \<Rightarrow> tv list"
where
  "map_row f tvtvs \<equiv> map (\<lambda>(x, y). f x y) tvtvs"

definition map_table :: "(tv \<Rightarrow> tv \<Rightarrow> tv) \<Rightarrow> (tv * tv) list list \<Rightarrow> tv list list"
where
  "map_table f tvtvss \<equiv> map (map_row f) tvtvss"

definition unary_truth_table :: "fm \<Rightarrow> tv list \<Rightarrow> tv list"
where
  "unary_truth_table p tvs \<equiv>
      map (\<lambda>x. eval ((\<lambda>s. undefined)(''p'' := x)) p) tvs"

definition binary_truth_table :: "fm \<Rightarrow> tv list \<Rightarrow> tv list list"
where
  "binary_truth_table p tvs \<equiv>
      map_table (\<lambda>x y. eval ((\<lambda>s. undefined)(''p'' := x, ''q'' := y)) p) (tv_pair_table tvs)"

definition digit_of_nat :: "nat \<Rightarrow> char"
where
  "digit_of_nat n \<equiv>
   (if n = 1 then (CHR ''1'') else if n = 2 then (CHR ''2'') else if n = 3 then (CHR ''3'') else
    if n = 4 then (CHR ''4'') else if n = 5 then (CHR ''5'') else if n = 6 then (CHR ''6'') else
    if n = 7 then (CHR ''7'') else if n = 8 then (CHR ''8'') else if n = 9 then (CHR ''9'') else
      (CHR ''0''))"

fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n =
      (if n < 10 then [digit_of_nat n] else string_of_nat (n div 10) @ [digit_of_nat (n mod 10)])"

fun string_tv :: "tv \<Rightarrow> string"
where
  "string_tv (Det True) = ''*''" |
  "string_tv (Det False) = ''o''" |
  "string_tv (Indet n) = string_of_nat n"

definition appends :: "string list \<Rightarrow> string"
where
  "appends strs \<equiv> foldr append strs []"

definition appends_nl :: "string list \<Rightarrow> string"
where
  "appends_nl strs \<equiv> ''\<newline>  '' @ foldr (\<lambda>s s'. s @ ''\<newline>  '' @ s') (butlast strs) (last strs) @ ''\<newline>''"

definition string_table :: "tv list list \<Rightarrow> string list list"
where
  "string_table tvss \<equiv> map (map string_tv) tvss"

definition string_table_string :: "string list list \<Rightarrow> string"
where
  "string_table_string strss \<equiv> appends_nl (map appends strss)"

definition unary :: "fm \<Rightarrow> tv list \<Rightarrow> string"
where
  "unary p tvs \<equiv> appends_nl (map string_tv (unary_truth_table p tvs))"

definition binary :: "fm \<Rightarrow> tv list \<Rightarrow> string"
where
  "binary p tvs \<equiv> string_table_string (string_table (binary_truth_table p tvs))"

subsection \<open>Main Truth Tables\<close>

text
\<open>
The omitted Cla (for Classic) is discussed later; Nab (for Nabla) is simply the negation of it.
\<close>

proposition (* Box Truth Table *)
  "unary (Box (Pro ''p'')) [Det True, Det False, Indet 1] = ''
  *
  o
  o
''"
  by code_simp

proposition (* Con' Truth Table *)
  "binary (Con' (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  oooo
  1o1o
  2oo2
''"
  by code_simp

proposition (* Dis' Truth Table *)
  "binary (Dis' (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  ****
  *o12
  *11*
  *2*2
''"
  by code_simp

proposition (* Neg' Truth Table *)
  "unary (Neg' (Pro ''p'')) [Det True, Det False, Indet 1] = ''
  o
  *
  1
''"
  by code_simp

proposition (* Eql' Truth Table *)
  "binary (Eql' (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  o*12
  11*o
  22o*
''"
  by code_simp

proposition (* Imp' Truth Table *)
  "binary (Imp' (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  ****
  *1*1
  *22*
''"
  by code_simp

proposition (* Neg Truth Table *)
  "unary (Neg (Pro ''p'')) [Det True, Det False, Indet 1] = ''
  o
  *
  o
''"
  by code_simp

proposition (* Eql Truth Table *)
  "binary (Eql (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *ooo
  o*oo
  oo*o
  ooo*
''"
  by code_simp

proposition (* Imp Truth Table *)
  "binary (Imp (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *ooo
  ****
  *o*o
  *oo*
''"
  by code_simp

proposition (* Nab Truth Table *)
  "unary (Nab (Pro ''p'')) [Det True, Det False, Indet 1] = ''
  o
  o
  *
''"
  by code_simp

proposition (* Con Truth Table *)
  "binary (Con (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  *ooo
  oooo
  oooo
  oooo
''"
  by code_simp

proposition (* Dis Truth Table *)
  "binary (Dis (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  ****
  *ooo
  *oo*
  *o*o
''"
  by code_simp

section \<open>Basic Theorems\<close>

subsection \<open>Selected Theorems and Non-Theorems\<close>

text
\<open>
Many of the following theorems and non-theorems use assumptions and meta-variables.
\<close>

proposition "valid (Cla (Box p))" and "\<not> valid (Nab (Box p))"
  unfolding valid_def
  by simp_all

proposition "valid (Cla (Cla p))" and "\<not> valid (Nab (Nab p))"
  unfolding valid_def
  by simp_all

proposition "valid (Cla (Nab p))" and "\<not> valid (Nab (Cla p))"
  unfolding valid_def
  by simp_all

proposition "valid (Box p) \<longleftrightarrow> valid (Box (Box p))"
  unfolding valid_def
  by simp

proposition "valid (Neg p) \<longleftrightarrow> valid (Neg' p)"
  unfolding valid_def
  by simp

proposition "valid (Con p q) \<longleftrightarrow> valid (Con' p q)"
  unfolding valid_def
  by simp

proposition "valid (Dis p q) \<longleftrightarrow> valid (Dis' p q)"
  unfolding valid_def
  by simp

proposition "valid (Eql p q) \<longleftrightarrow> valid (Eql' p q)"
  unfolding valid_def
  using eval.simps tv.inject eval_equality eval_negation
  by (metis (full_types))

proposition "valid (Imp p q) \<longleftrightarrow> valid (Imp' p q)"
  unfolding valid_def
  using eval.simps tv.inject eval_equality eval_negation
  by (metis (full_types))

proposition "\<not> valid (Pro ''p'')"
  unfolding valid_def
  by auto

proposition "\<not> valid (Neg' (Pro ''p''))"
proof -
  have "eval (\<lambda>s. Det True) (Neg' (Pro ''p'')) = Det False"
    by simp
  then show ?thesis
    unfolding valid_def
    using tv.inject
    by metis
qed

proposition assumes "valid p" shows "\<not> valid (Neg' p)"
  using assms
  unfolding valid_def
  by simp

proposition assumes "valid (Neg' p)" shows "\<not> valid p"
  using assms
  unfolding valid_def
  by force

proposition "valid (Neg' (Neg' p)) \<longleftrightarrow> valid p"
  unfolding valid_def
  using double_negation
  by simp

theorem conjunction: "valid (Con' p q) \<longleftrightarrow> valid p \<and> valid q"
  unfolding valid_def
  by auto

corollary assumes "valid (Con' p q)" shows "valid p" and "valid q"
  using assms conjunction
  by simp_all

proposition assumes "valid p" and "valid (Imp p q)" shows "valid q"
  using assms eval.simps tv.inject
  unfolding valid_def
  by (metis (full_types))

proposition assumes "valid p" and "valid (Imp' p q)" shows "valid q"
  using assms eval.simps tv.inject eval_equality
  unfolding valid_def
  by (metis (full_types))

subsection \<open>Key Equalities\<close>

text
\<open>
The key equalities are part of the motivation for the semantic clauses.
\<close>

proposition "valid (Eql p (Neg' (Neg' p)))"
  unfolding valid_def
  using double_negation
  by simp

proposition "valid (Eql Truth (Neg' Falsity))"
  unfolding valid_def
  by simp

proposition "valid (Eql Falsity (Neg' Truth))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con' p p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con' Truth p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con' p Truth))"
  unfolding valid_def
  by simp

proposition "valid (Eql Truth (Eql' p p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Eql' Truth p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Eql' p Truth))"
  unfolding valid_def
proof
  fix i
  show "eval i (Eql p (Eql' p Truth)) = Det True"
    by (cases "eval i p") simp_all
qed

proposition "valid (Eql (Neg' p) (Eql' Falsity p))"
  unfolding valid_def
proof
  fix i
  show "eval i (Eql (Neg' p) (Eql' (Neg' Truth) p)) = Det True"
    by (cases "eval i p") simp_all
qed

proposition "valid (Eql (Neg' p) (Eql' p Falsity))"
  unfolding valid_def
  using eval.simps eval_equality eval_negation
  by metis

section \<open>Further Non-Theorems\<close>

subsection \<open>Smaller Domains and Paraconsistency\<close>

text
\<open>
Validity is relativized to a set of indeterminate truth values (called a domain).
\<close>

definition domain :: "nat set \<Rightarrow> tv set"
where
  "domain U \<equiv> {Det True, Det False} \<union> Indet ` U"

theorem universal_domain: "domain {n. True} = {x. True}"
proof -
  have "\<forall>x. x = Det True \<or> x = Det False \<or> x \<in> range Indet"
    using range_eqI tv.exhaust tv.inject
    by metis
  then show ?thesis
    unfolding domain_def
    by blast
qed

definition valid_in :: "nat set \<Rightarrow> fm \<Rightarrow> bool"
where
  "valid_in U p \<equiv> \<forall>i. range i \<subseteq> domain U \<longrightarrow> eval i p = \<bullet>"

abbreviation valid_boole :: "fm \<Rightarrow> bool" where "valid_boole p \<equiv> valid_in {} p"

proposition "valid p \<longleftrightarrow> valid_in {n. True} p"
  unfolding valid_def valid_in_def
  using universal_domain
  by simp

theorem valid_valid_in: assumes "valid p" shows "valid_in U p"
  using assms
  unfolding valid_in_def valid_def
  by simp

theorem transfer: assumes "\<not> valid_in U p" shows "\<not> valid p"
  using assms valid_valid_in
  by blast

proposition "valid_in U (Neg' (Neg' p)) \<longleftrightarrow> valid_in U p"
  unfolding valid_in_def
  using double_negation
  by simp

theorem conjunction_in: "valid_in U (Con' p q) \<longleftrightarrow> valid_in U p \<and> valid_in U q"
  unfolding valid_in_def
  by auto

corollary assumes "valid_in U (Con' p q)" shows "valid_in U p" and "valid_in U q"
  using assms conjunction_in
  by simp_all

proposition assumes "valid_in U p" and "valid_in U (Imp p q)" shows "valid_in U q"
  using assms eval.simps tv.inject
  unfolding valid_in_def
  by (metis (full_types))

proposition assumes "valid_in U p" and "valid_in U (Imp' p q)" shows "valid_in U q"
  using assms eval.simps tv.inject eval_equality
  unfolding valid_in_def
  by (metis (full_types))

abbreviation (input) Explosion :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "Explosion p q \<equiv> Imp' (Con' p (Neg' p)) q"

proposition "valid_boole (Explosion (Pro ''p'') (Pro ''q''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''p'' \<in> {Det True, Det False}"
      "i ''q'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (Explosion (Pro ''p'') (Pro ''q'')) = Det True"
    by (cases "i ''p''"; cases "i ''q''") simp_all
qed

lemma explosion_counterexample: "\<not> valid_in {1} (Explosion (Pro ''p'') (Pro ''q''))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''q'' := Det False)"
  have "range ?i \<subseteq> domain {1}"
    unfolding domain_def
    by (simp add: image_subset_iff)
  moreover have "eval ?i (Explosion (Pro ''p'') (Pro ''q'')) = Indet 1"
    by simp
  moreover have "Indet 1 \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

theorem explosion_not_valid: "\<not> valid (Explosion (Pro ''p'') (Pro ''q''))"
  using explosion_counterexample transfer
  by simp

proposition "\<not> valid (Imp (Con' (Pro ''p'') (Neg' (Pro ''p''))) (Pro ''q''))"
proof -
  obtain i where "eval i (Explosion (Pro ''p'') (Pro ''q'')) \<noteq> Det True"
    using explosion_not_valid unfolding valid_def by fast
  then have "eval i (Imp (Con' (Pro ''p'') (Neg' (Pro ''p''))) (Pro ''q'')) = Det False"
    using eval.simps(5) eval_equality by meson
  then show ?thesis
    unfolding valid_def by fastforce
qed

subsection \<open>Example: Contraposition\<close>

text
\<open>
Contraposition is not valid.
\<close>

abbreviation (input) Contraposition :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "Contraposition p q \<equiv> Eql' (Imp' p q) (Imp' (Neg' q) (Neg' p))"

proposition "valid_boole (Contraposition (Pro ''p'') (Pro ''q''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''p'' \<in> {Det True, Det False}"
      "i ''q'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (Contraposition (Pro ''p'') (Pro ''q'')) = Det True"
    by (cases "i ''p''"; cases "i ''q''") simp_all
qed

proposition "valid_in {1} (Contraposition (Pro ''p'') (Pro ''q''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1}"
  then have
      "i ''p'' \<in> {Det True, Det False, Indet 1}"
      "i ''q'' \<in> {Det True, Det False, Indet 1}"
    unfolding domain_def
    by auto
  then show "eval i (Contraposition (Pro ''p'') (Pro ''q'')) = Det True"
    by (cases "i ''p''"; cases "i ''q''") simp_all
qed

lemma contraposition_counterexample: "\<not> valid_in {1, 2} (Contraposition (Pro ''p'') (Pro ''q''))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''q'' := Indet 2)"
  have "range ?i \<subseteq> domain {1, 2}"
    unfolding domain_def
    by (simp add: image_subset_iff)
  moreover have "eval ?i (Contraposition (Pro ''p'') (Pro ''q'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

theorem contraposition_not_valid: "\<not> valid (Contraposition (Pro ''p'') (Pro ''q''))"
  using contraposition_counterexample transfer
  by simp

subsection \<open>More Than Four Truth Values Needed\<close>

text
\<open>
Cla3 is valid for two indeterminate truth values but not for three indeterminate truth values.
\<close>

lemma ranges: assumes "range i \<subseteq> domain U" shows "eval i p \<in> domain U"
  using assms
  unfolding domain_def
  by (induct p) auto

proposition (* Cla Truth Table *)
  "unary (Cla (Pro ''p'')) [Det True, Det False, Indet 1] = ''
  *
  *
  o
''"
  by code_simp

proposition "valid_boole (Cla p)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "eval i p \<in> {Det True, Det False}"
    using ranges[of i "{}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla p) = Det True"
    by (cases "eval i p") simp_all
qed

proposition "\<not> valid_in {1} (Cla (Pro ''p''))"
proof -
  let ?i = "\<lambda>s. Indet 1"
  have "range ?i \<subseteq> domain {1}"
    unfolding domain_def
    by (simp add: image_subset_iff)
  moreover have "eval ?i (Cla (Pro ''p'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

abbreviation (input) Cla2 :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "Cla2 p q \<equiv> Dis (Dis (Cla p) (Cla q)) (Eql p q)"

proposition (* Cla2 Truth Table *)
  "binary (Cla2 (Pro ''p'') (Pro ''q'')) [Det True, Det False, Indet 1, Indet 2] = ''
  ****
  ****
  ***o
  **o*
''"
  by code_simp

proposition "valid_boole (Cla2 p q)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume range: "range i \<subseteq> domain {}"
  then have
      "eval i p \<in> {Det True, Det False}"
      "eval i q \<in> {Det True, Det False}"
    using ranges[of i "{}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla2 p q) = Det True"
    by (cases "eval i p"; cases "eval i q") simp_all
qed

proposition "valid_in {1} (Cla2 p q)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume range: "range i \<subseteq> domain {1}"
  then have
      "eval i p \<in> {Det True, Det False, Indet 1}"
      "eval i q \<in> {Det True, Det False, Indet 1}"
    using ranges[of i "{1}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla2 p q) = Det True"
    by (cases "eval i p"; cases "eval i q") simp_all
qed

proposition "\<not> valid_in {1, 2} (Cla2 (Pro ''p'') (Pro ''q''))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''q'' := Indet 2)"
  have "range ?i \<subseteq> domain {1, 2}"
    unfolding domain_def
    by (simp add: image_subset_iff)
  moreover have "eval ?i (Cla2 (Pro ''p'') (Pro ''q'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

abbreviation (input) Cla3 :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "Cla3 p q r \<equiv> Dis (Dis (Cla p) (Dis (Cla q) (Cla r))) (Dis (Eql p q) (Dis (Eql p r) (Eql q r)))"

proposition "valid_boole (Cla3 p q r)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "eval i p \<in> {Det True, Det False}"
      "eval i q \<in> {Det True, Det False}"
      "eval i r \<in> {Det True, Det False}"
    using ranges[of i "{}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla3 p q r) = Det True"
    by (cases "eval i p"; cases "eval i q"; cases "eval i r") simp_all
qed

proposition "valid_in {1} (Cla3 p q r)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1}"
  then have
      "eval i p \<in> {Det True, Det False, Indet 1}"
      "eval i q \<in> {Det True, Det False, Indet 1}"
      "eval i r \<in> {Det True, Det False, Indet 1}"
    using ranges[of i "{1}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla3 p q r) = Det True"
    by (cases "eval i p"; cases "eval i q"; cases "eval i r") simp_all
qed

proposition "valid_in {1, 2} (Cla3 p q r)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1, 2}"
  then have
      "eval i p \<in> {Det True, Det False, Indet 1, Indet 2}"
      "eval i q \<in> {Det True, Det False, Indet 1, Indet 2}"
      "eval i r \<in> {Det True, Det False, Indet 1, Indet 2}"
    using ranges[of i "{1, 2}"]
    unfolding domain_def
    by auto
  then show "eval i (Cla3 p q r) = Det True"
    by (cases "eval i p"; cases "eval i q"; cases "eval i r") auto
qed

proposition "\<not> valid_in {1, 2, 3} (Cla3 (Pro ''p'') (Pro ''q'') (Pro ''r''))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''q'' := Indet 2, ''r'' := Indet 3)"
  have "range ?i \<subseteq> domain {1, 2, 3}"
    unfolding domain_def
    by (simp add: image_subset_iff)
  moreover have "eval ?i (Cla3 (Pro ''p'') (Pro ''q'') (Pro ''r'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

section \<open>Further Meta-Theorems\<close>

subsection \<open>Fundamental Definitions and Lemmas\<close>

text
\<open>
The function props collects the set of propositional symbols occurring in a formula.
\<close>

fun props :: "fm \<Rightarrow> id set"
where
  "props Truth = {}" |
  "props (Pro s) = {s}" |
  "props (Neg' p) = props p" |
  "props (Con' p q) = props p \<union> props q" |
  "props (Eql p q) = props p \<union> props q" |
  "props (Eql' p q) = props p \<union> props q"

lemma relevant_props: assumes "\<forall>s \<in> props p. i1 s = i2 s" shows "eval i1 p = eval i2 p"
  using assms
  by (induct p) (simp_all, metis)

fun change_tv :: "(nat \<Rightarrow> nat) \<Rightarrow> tv \<Rightarrow> tv"
where
  "change_tv f (Det b) = Det b" |
  "change_tv f (Indet n) = Indet (f n)"

lemma change_tv_injection: assumes "inj f" shows "inj (change_tv f)"
proof -
  have "change_tv f tv1 = change_tv f tv2 \<Longrightarrow> tv1 = tv2" for tv1 tv2
    using assms
    by (cases tv1; cases tv2) (simp_all add: inj_eq)
  then show ?thesis
    by (simp add: injI)
qed

definition
  change_int :: "(nat \<Rightarrow> nat) \<Rightarrow> (id \<Rightarrow> tv) \<Rightarrow> (id \<Rightarrow> tv)"
where
  "change_int f i \<equiv> \<lambda>s. change_tv f (i s)"

lemma eval_change: assumes "inj f" shows "eval (change_int f i) p = change_tv f (eval i p)"
proof (induct p)
  fix p
  assume "eval (change_int f i) p = change_tv f (eval i p)"
  then have "eval_neg (eval (change_int f i) p) = eval_neg (change_tv f (eval i p))"
    by simp
  then have "eval_neg (eval (change_int f i) p) = change_tv f (eval_neg (eval i p))"
    by (cases "eval i p") (simp_all add: case_bool_if)
  then show "eval (change_int f i) (Neg' p) = change_tv f (eval i (Neg' p))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
(* One liner:
   using ih1 ih2 change_tv.elims assms change_tv_injection by (auto simp add: inj_eq)
*)
  proof (cases "eval i p1 = eval i p2")
    assume a: "eval i p1 = eval i p2"
    then have yes: "eval i (Con' p1 p2) = eval i p1"
      by auto
    from a have "change_tv f (eval i p1) = change_tv f (eval i p2)"
      by auto
    then have "eval (change_int f i) p1 = eval (change_int f i) p2"
      using ih1 ih2
      by auto
    then have "eval (change_int f i) (Con' p1 p2) = eval (change_int f i) p1"
      by auto
    then show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
      using yes ih1
      by auto
  next
    assume a': "eval i p1 \<noteq> eval i p2"
    from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
      using assms ih1 ih2 change_tv_injection the_inv_f_f
      by metis
    show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
    proof (cases "eval i p1 = Det True")
      assume a: "eval i p1 = Det True"
      from a a' have "eval i (Con' p1 p2) = eval i p2"
        by auto
      then have c: "change_tv f (eval i (Con' p1 p2)) = change_tv f (eval i p2)"
        by auto
      from a have b: "eval (change_int f i) p1 = Det True"
        using ih1
        by auto
      from b b' have "eval (change_int f i) (Con' p1 p2) = eval (change_int f i) p2"
        by auto
      then show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
        using c ih2
        by auto
    next
      assume a'': "eval i p1 \<noteq> Det True"
      from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
        using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
        by metis
      show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
      proof (cases "eval i p2 = Det True")
        assume a: "eval i p2 = Det True"
        from a a' a'' have "eval i (Con' p1 p2) = eval i p1"
          by auto
        then have c: "change_tv f (eval i (Con' p1 p2)) = change_tv f (eval i p1)"
          by auto
        from a have b: "eval (change_int f i) p2 = Det True"
          using ih2
          by auto
        from b b' b'' have "eval (change_int f i) (Con' p1 p2) = eval (change_int f i) p1"
          by auto
        then show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
          using c ih1
          by auto
      next
        assume a''': "eval i p2 \<noteq> Det True"
        from a' a'' a''' have "eval i (Con' p1 p2) = Det False"
          by auto
        then have c: "change_tv f (eval i (Con' p1 p2)) = Det False"
          by auto
        from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
          using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
          by metis
        from b' b'' b''' have "eval (change_int f i) (Con' p1 p2) = Det False"
          by auto
        then show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
          using c
          by auto
      qed
    qed
  qed
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  have "Det (eval (change_int f i) p1 = eval (change_int f i) p2) =
      Det (change_tv f (eval i p1) = change_tv f (eval i p2))"
    using ih1 ih2
    by simp
  also have "... = Det ((eval i p1) = (eval i p2))"
    using assms change_tv_injection
    by (simp add: inj_eq)
  also have "... = change_tv f (Det (eval i p1 = eval i p2))"
    by simp
  finally show "eval (change_int f i) (Eql p1 p2) = change_tv f (eval i (Eql p1 p2))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
(* One liner:
   using ih1 ih2 assms by (auto simp add: inj_eq bool.case_eq_if split: tv.splits)
*)
  proof (cases "eval i p1 = eval i p2")
    assume a: "eval i p1 = eval i p2"
    then have yes: "eval i (Eql' p1 p2) = Det True"
      by auto
    from a have "change_tv f (eval i p1) = change_tv f (eval i p2)"
      by auto
    then have "eval (change_int f i) p1 = eval (change_int f i) p2"
      using ih1 ih2
      by auto
    then have "eval (change_int f i) (Eql' p1 p2) = Det True"
      by auto
    then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
      using yes ih1
      by auto
  next
    assume a': "eval i p1 \<noteq> eval i p2"
    show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
    proof (cases "eval i p1 = Det True")
      assume a: "eval i p1 = Det True"
      from a a' have yes: "eval i (Eql' p1 p2) = eval i p2"
        by auto
      from a have "change_tv f (eval i p1) = Det True"
        by auto
      then have b: "eval (change_int f i) p1 = Det True"
        using ih1
        by auto
      from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
        using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
        by metis
      from b b' have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) p2"
        by auto
      then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
        using ih2 yes
        by auto
    next
      assume a'': "eval i p1 \<noteq> Det True"
      show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
      proof (cases "eval i p2 = Det True")
        assume a: "eval i p2 = Det True"
        from a a' a'' have yes: "eval i (Eql' p1 p2) = eval i p1"
          using eval_equality[of i p1 p2]
          by auto
        from a have "change_tv f (eval i p2) = Det True"
          by auto
        then have b: "eval (change_int f i) p2 = Det True"
          using ih2
          by auto
        from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
          using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
          by metis
        from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
          using b b'
          by auto
        from b b' b'' have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) p1"
          using eval_equality[of "change_int f i" p1 p2]
          by auto
        then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
          using ih1 yes
          by auto
      next
        assume a''': "eval i p2 \<noteq> Det True"
        show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
        proof (cases "eval i p1 = Det False")
          assume a: "eval i p1 = Det False"
          from a a' a'' a''' have yes: "eval i (Eql' p1 p2) = eval i (Neg' p2)"
            using eval_equality[of i p1 p2]
            by auto
          from a have "change_tv f (eval i p1) = Det False"
            by auto
          then have b: "eval (change_int f i) p1 = Det False"
            using ih1
            by auto
          from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
            using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
            by metis
          from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
            using b b'
            by auto
          from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
            using b b' b''
            by (metis assms change_tv.simps(1) change_tv_injection inj_eq ih2)
          from b b' b'' b'''
          have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) (Neg' p2)"
            using eval_equality[of "change_int f i" p1 p2]
            by auto
          then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
            using ih2 yes a a' a''' b b' b''' eval_negation
            by metis
        next
          assume a'''': "eval i p1 \<noteq> Det False"
          show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
          proof (cases "eval i p2 = Det False")
            assume a: "eval i p2 = Det False"
            from a a' a'' a''' a'''' have yes: "eval i (Eql' p1 p2) = eval i (Neg' p1)"
              using eval_equality[of i p1 p2]
              by auto
            from a have "change_tv f (eval i p2) = Det False"
              by auto
            then have b: "eval (change_int f i) p2 = Det False"
              using ih2
              by auto
            from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
              using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
              by metis
            from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
              using change_tv.elims ih1 tv.simps(4)
              by auto
            from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
              using b b' b''
              by (metis assms change_tv.simps(1) change_tv_injection inj_eq ih2)
            from a'''' have b'''': "eval (change_int f i) p1 \<noteq> Det False"
              using b b'
              by auto
            from b b' b'' b''' b''''
            have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) (Neg' p1)"
              using eval_equality[of "change_int f i" p1 p2]
              by auto
            then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
              using ih1 yes a a' a''' a'''' b b' b''' b'''' eval_negation a'' b''
              by metis
          next
            assume a''''': "eval i p2 \<noteq> Det False"
            from a' a'' a''' a'''' a''''' have yes: "eval i (Eql' p1 p2) = Det False"
              using eval_equality[of i p1 p2]
              by auto
            from a''''' have "change_tv f (eval i p2) \<noteq> Det False"
              using change_tv_injection inj_eq assms change_tv.simps
              by metis
            then have b: "eval (change_int f i) p2 \<noteq> Det False"
              using ih2
              by auto
            from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
              using assms ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
              by metis
            from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
              using change_tv.elims ih1 tv.simps(4)
              by auto
            from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
              using b b' b''
              by (metis assms change_tv.simps(1) change_tv_injection the_inv_f_f ih2)
            from a'''' have b'''': "eval (change_int f i) p1 \<noteq> Det False"
              by (metis a'' change_tv.simps(2) ih1 string_tv.cases tv.distinct(1))
            from b b' b'' b''' b'''' have "eval (change_int f i) (Eql' p1 p2) = Det False"
              using eval_equality[of "change_int f i" p1 p2]
              by auto
            then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
              using ih1 yes a' a''' a'''' b b' b''' b'''' a'' b''
              by auto
          qed
        qed
      qed
    qed
  qed
qed (simp_all add: change_int_def)

subsection \<open>Only a Finite Number of Truth Values Needed\<close>

text
\<open>
Theorem valid_in_valid is a kind of the reverse of valid_valid_in (or its transfer variant).
\<close>

abbreviation is_indet :: "tv \<Rightarrow> bool"
where
  "is_indet tv \<equiv> (case tv of Det _ \<Rightarrow> False | Indet _ \<Rightarrow> True)"

abbreviation get_indet :: "tv \<Rightarrow> nat"
where
  "get_indet tv \<equiv> (case tv of Det _ \<Rightarrow> undefined | Indet n \<Rightarrow> n)"

theorem valid_in_valid: assumes "card U \<ge> card (props p)" and "valid_in U p" shows "valid p"
proof -
  have "finite U \<Longrightarrow> card (props p) \<le> card U \<Longrightarrow> valid_in U p \<Longrightarrow> valid p" for U p
  proof -
    assume assms: "finite U" "card (props p) \<le> card U" "valid_in U p"
    show "valid p"
      unfolding valid_def
    proof
      fix i
      obtain f where f_p: "(change_int f i) ` (props p) \<subseteq> (domain U) \<and> inj f"
      proof -
        have "finite U \<Longrightarrow> card (props p) \<le> card U \<Longrightarrow>
            \<exists>f. change_int f i ` props p \<subseteq> domain U \<and> inj f" for U p
        proof -
          assume assms: "finite U" "card (props p) \<le> card U"
          show ?thesis
          proof -
            let ?X = "(get_indet ` ((i ` props p) \<inter> {tv. is_indet tv}))"
            have d: "finite (props p)"
              by (induct p) auto
            then have cx: "card ?X \<le> card U"
              using assms surj_card_le Int_lower1 card_image_le finite_Int finite_imageI le_trans
              by metis
            have f: "finite ?X"
              using d
              by simp
            obtain f where f_p: "(\<forall>n \<in> ?X. f n \<in> U) \<and> (inj f)"
            proof -
              have "finite X \<Longrightarrow> finite Y \<Longrightarrow> card X \<le> card Y \<Longrightarrow> \<exists>f. (\<forall>n \<in> X. f n \<in> Y) \<and> inj f"
                  for X Y :: "nat set"
              proof -
                assume assms: "finite X" "finite Y" "card X \<le> card Y"
                show ?thesis
                proof -
                  from assms obtain Z where xyz: "Z \<subseteq> Y \<and> card Z = card X"
                    by (metis card_image card_le_inj)
                  then obtain f where "bij_betw f X Z"
                    by (metis assms(1) assms(2) finite_same_card_bij infinite_super)
                  then have f_p: "(\<forall>n \<in> X. f n \<in> Y) \<and> inj_on f X"
                    using bij_betwE bij_betw_imp_inj_on xyz
                    by blast
                  obtain f' where f': "f' = (\<lambda>n. if n \<in> X then f n else n + Suc (Max Y + n))"
                    by simp
                  have "inj f'"
                    unfolding f' inj_on_def
                    using assms(2) f_p le_add2 trans_le_add2 not_less_eq_eq
                    by (simp, metis Max_ge add.commute inj_on_eq_iff)
                  moreover have "(\<forall>n \<in> X. f' n \<in> Y)"
                    unfolding f'
                    using f_p
                    by auto
                  ultimately show ?thesis
                    by metis
                qed
              qed
              then show "(\<And>f. (\<forall>n \<in> get_indet ` (i ` props p \<inter> {tv. is_indet tv}). f n \<in> U)
                  \<and> inj f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
                using assms cx f
                unfolding inj_on_def
                by metis
            qed
            have "(change_int f i) ` (props p) \<subseteq> (domain U)"
            proof
              fix x
              assume "x \<in> change_int f i ` props p"
              then obtain s where s_p: "s \<in> props p \<and> change_int f i s = x"
                by auto
              then have "change_int f i s \<in> {Det True, Det False} \<union> Indet ` U"
              proof (cases "change_int f i s \<in> {Det True, Det False}")
                case True
                then show ?thesis
                  by auto
              next
                case False
                then obtain n' where "change_int f i s = Indet n'"
                  by (cases "change_int f i s") simp_all
                then have p: "change_tv f (i s) = Indet n'"
                  by (simp add: change_int_def)
                moreover have "n' \<in> U"
                proof -
                  obtain n'' where "f n'' = n'"
                    using calculation change_tv.elims
                    by blast
                  moreover have "s \<in> props p \<and> i s = (Indet n'')"
                    using p calculation change_tv.simps change_tv_injection the_inv_f_f f_p s_p
                    by metis
                  then have "(Indet n'') \<in> i ` props p"
                    using image_iff
                    by metis
                  then have "(Indet n'') \<in> i ` props p \<and> is_indet (Indet n'') \<and>
                      get_indet (Indet n'') = n''"
                    by auto
                  then have "n'' \<in> ?X"
                    using Int_Collect image_iff
                    by metis
                  ultimately show ?thesis
                    using f_p
                    by auto
                qed
                ultimately have "change_tv f (i s) \<in> Indet ` U"
                  by auto
                then have "change_int f i s \<in> Indet ` U"
                  unfolding change_int_def
                  by auto
                then show ?thesis
                  by auto
              qed
              then show "x \<in> domain U"
                unfolding domain_def
                using s_p
                by simp
            qed
            then have "(change_int f i) ` (props p) \<subseteq> (domain U) \<and> (inj f)"
              unfolding domain_def
              using f_p
              by simp
            then show ?thesis
              using f_p
              by metis
          qed
        qed
        then show "(\<And>f. change_int f i ` props p \<subseteq> domain U \<and> inj f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
          using assms
          by metis
      qed
      obtain i2 where i2: "i2 = (\<lambda>s. if s \<in> props p then (change_int f i) s else Det True)"
        by simp
      then have i2_p: "\<forall>s \<in> props p. i2 s = (change_int f i) s"
            "\<forall>s \<in> - props p. i2 s = Det True"
        by auto
      then have "range i2 \<subseteq> (domain U)"
        using i2 f_p
        unfolding domain_def
        by auto
      then have "eval i2 p = Det True"
        using assms
        unfolding valid_in_def
        by auto
      then have "eval (change_int f i) p = Det True"
        using relevant_props[of p i2 "change_int f i"] i2_p
        by auto
      then have "change_tv f (eval i p) = Det True"
        using eval_change f_p
        by auto
      then show "eval i p = Det True"
        by (cases "eval i p") simp_all
    qed
  qed
  then show ?thesis
    using assms subsetI sup_bot.comm_neutral image_is_empty subsetCE UnCI valid_in_def
        Un_insert_left card.empty card.infinite finite.intros(1)
    unfolding domain_def
    by metis
qed

theorem reduce: "valid p \<longleftrightarrow> valid_in {1..card (props p)} p"
  using valid_in_valid transfer
  by force

section \<open>Case Study\<close>

subsection \<open>Abbreviations\<close>

text
\<open>
Entailment takes a list of assumptions.
\<close>

abbreviation (input) Entail :: "fm list \<Rightarrow> fm \<Rightarrow> fm"
where
  "Entail l p \<equiv> Imp (if l = [] then Truth else fold Con' (butlast l) (last l)) p"

theorem entailment_not_chain:
  "\<not> valid (Eql (Entail [Pro ''p'', Pro ''q''] (Pro ''r''))
      (Box ((Imp' (Pro ''p'') (Imp' (Pro ''q'') (Pro ''r''))))))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''r'' := Det False)"
  have "eval ?i (Eql (Entail [Pro ''p'', Pro ''q''] (Pro ''r''))
      (Box ((Imp' (Pro ''p'') (Imp' (Pro ''q'') (Pro ''r'')))))) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_def
    by metis
qed

abbreviation (input) B0 :: fm where "B0 \<equiv> Con' (Con' (Pro ''p'') (Pro ''q'')) (Neg' (Pro ''r''))"

abbreviation (input) B1 :: fm where "B1 \<equiv> Imp' (Con' (Pro ''p'') (Pro ''q'')) (Pro ''r'')"

abbreviation (input) B2 :: fm where "B2 \<equiv> Imp' (Pro ''r'') (Pro ''s'')"

abbreviation (input) B3 :: fm where "B3 \<equiv> Imp' (Neg' (Pro ''s'')) (Neg' (Pro ''r''))"

subsection \<open>Results\<close>

text
\<open>
The paraconsistent logic is usable in contrast to classical logic.
\<close>

theorem classical_logic_is_not_usable: "valid_boole (Entail [B0, B1] p)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''p'' \<in> {Det True, Det False}"
      "i ''q'' \<in> {Det True, Det False}"
      "i ''r'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (Entail [B0, B1] p) = Det True"
    by (cases "i ''p''"; cases "i ''q''"; cases "i ''r''") simp_all
qed

corollary "valid_boole (Entail [B0, B1] (Pro ''r''))"
  by (rule classical_logic_is_not_usable)

corollary "valid_boole (Entail [B0, B1] (Neg' (Pro ''r'')))"
  by (rule classical_logic_is_not_usable)

proposition "\<not> valid (Entail [B0, B1] (Pro ''r''))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''r'' := Det False)"
  have "eval ?i (Entail [B0, B1] (Pro ''r'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_def
    by metis
qed

proposition "valid_boole (Entail [B0, Box B1] p)"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''p'' \<in> {Det True, Det False}"
      "i ''q'' \<in> {Det True, Det False}"
      "i ''r'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (Entail [B0, Box B1] p) = Det True"
    by (cases "i ''p''"; cases "i ''q''"; cases "i ''r''") simp_all
qed

proposition "\<not> valid (Entail [B0, Box B1, Box B2] (Neg' (Pro ''p'')))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''p'' := Det True)"
  have "eval ?i (Entail [B0, Box B1, Box B2] (Neg' (Pro ''p''))) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_def
    by metis
qed

proposition "\<not> valid (Entail [B0, Box B1, Box B2] (Neg' (Pro ''q'')))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''q'' := Det True)"
  have "eval ?i (Entail [B0, Box B1, Box B2] (Neg' (Pro ''q''))) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_def
    by metis
qed

proposition "\<not> valid (Entail [B0, Box B1, Box B2] (Neg' (Pro ''s'')))"
proof -
  let ?i = "(\<lambda>s. Indet 1)(''s'' := Det True)"
  have "eval ?i (Entail [B0, Box B1, Box B2] (Neg' (Pro ''s''))) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_def
    by metis
qed

proposition "valid (Entail [B0, Box B1, Box B2] (Pro ''r''))"
proof -
  have "{1..card (props (Entail [B0, Box B1, Box B2] (Pro ''r'')))} = {1, 2, 3, 4}"
    by code_simp
  moreover have "valid_in {1, 2, 3, 4} (Entail [B0, Box B1, Box B2] (Pro ''r''))"
    unfolding valid_in_def
  proof (rule; rule)
    fix i :: "id \<Rightarrow> tv"
    assume "range i \<subseteq> domain {1, 2, 3, 4}"
    then have icase:
      "i ''p'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''q'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''r'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''s'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      unfolding domain_def
      by auto
    show "eval i (Entail [B0, Box B1, Box B2] (Pro ''r'')) = Det True"
      using icase
      by (cases "i ''p''"; cases "i ''q''"; cases "i ''r''"; cases "i ''s''") simp_all
  qed
  ultimately show ?thesis
    using reduce
    by simp
qed

proposition "valid (Entail [B0, Box B1, Box B2] (Neg' (Pro ''r'')))"
proof -
  have "{1..card (props (Entail [B0, Box B1, Box B2] (Neg' (Pro ''r''))))} = {1, 2, 3, 4}"
    by code_simp
  moreover have "valid_in {1, 2, 3, 4} (Entail [B0, Box B1, Box B2] (Neg' (Pro ''r'')))"
    unfolding valid_in_def
  proof (rule; rule)
    fix i :: "id \<Rightarrow> tv"
    assume "range i \<subseteq> domain {1, 2, 3, 4}"
    then have icase:
      "i ''p'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''q'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''r'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''s'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      unfolding domain_def
      by auto
    show "eval i (Entail [B0, Box B1, Box B2] (Neg' (Pro ''r''))) = Det True"
      using icase
      by (cases "i ''p''"; cases "i ''q''"; cases "i ''r''"; cases "i ''s''") simp_all
  qed
  ultimately show ?thesis
    using reduce
    by simp
qed

proposition "valid (Entail [B0, Box B1, Box B2] (Pro ''s''))"
proof -
  have "{1..card (props (Entail [B0, Box B1, Box B2] (Pro ''s'')))} = {1, 2, 3, 4}"
    by code_simp
  moreover have "valid_in {1, 2, 3, 4} (Entail [B0, Box B1, Box B2] (Pro ''s''))"
    unfolding valid_in_def
  proof (rule; rule)
    fix i :: "id \<Rightarrow> tv"
    assume "range i \<subseteq> domain {1, 2, 3, 4}"
    then have icase:
      "i ''p'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''q'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''r'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      "i ''s'' \<in> {Det True, Det False, Indet 1, Indet 2, Indet 3, Indet 4}"
      unfolding domain_def
      by auto
    show "eval i (Entail [B0, Box B1, Box B2] (Pro ''s'')) = Det True"
      using icase
      by (cases "i ''p''"; cases "i ''q''"; cases "i ''r''"; cases "i ''s''") simp_all
  qed
  ultimately show ?thesis
    using reduce
    by simp
qed

section \<open>Acknowledgements\<close>

text
\<open>
Thanks to the Isabelle developers for making a superb system and for always being willing to help.
\<close>

section \<open>Appendix\<close>

(* Strategy: We define a formula that is valid in the sets {0..<1}, {0..<2}, ..., {0..<n-1} but is
   not valid in the set {0..<n} *)

subsection \<open>Injections from sets to sets\<close>

(* We define the notion of an injection from a set X to a set Y *)

definition inj_from_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj_from_to f X Y \<equiv> inj_on f X \<and> f ` X \<subseteq> Y"

lemma bij_betw_inj_from_to: "bij_betw f X Y \<Longrightarrow> inj_from_to f X Y"
  unfolding bij_betw_def inj_from_to_def by simp

(* Special lemma for finite cardinality only *)

lemma inj_from_to_if_card:
  assumes "card X \<le> card Y"
  assumes "finite X"
  shows "\<exists>f. inj_from_to f X Y"
  unfolding inj_from_to_def
  using assms card_infinite gr_implies_not0 inj_on_iff_card_le le_eq_less_or_eq card_empty
    empty_subsetI finite_imageI finite_subset subset_antisym by metis

subsection \<open>Extension of theory before Appendix\<close>

(* The above theory is extended with abbreviation is_det and a number of lemmas that are similar to
   or generalizations of previous lemmas *)

(* Could maybe be defined more like is_indet or introduce them in the datatype definition *)
abbreviation is_det :: "tv \<Rightarrow> bool" where "is_det tv \<equiv> \<not> is_indet tv"

theorem valid_iff_valid_in:
  assumes "card U \<ge> card (props p)"
  shows "valid p \<longleftrightarrow> valid_in U p"
  using assms valid_in_valid valid_valid_in by blast

(* Generalization of change_tv_injection *)
lemma change_tv_injection_on:
  assumes "inj_on f U"
  shows "inj_on (change_tv f) (domain U)"
proof
  fix x y
  assume "x \<in> domain U" "y \<in> domain U" "change_tv f x = change_tv f y"
  then show "x = y"
    unfolding domain_def using assms inj_onD by (cases x; cases y) auto
qed

(* Similar to change_tv_injection_on *)
lemma change_tv_injection_from_to:
  assumes "inj_from_to f U W"
  shows "inj_from_to (change_tv f) (domain U) (domain W)"
  unfolding inj_from_to_def
proof
  show "inj_on (change_tv f) (domain U)"
    using assms change_tv_injection_on unfolding inj_from_to_def by blast
next
  show "change_tv f ` domain U \<subseteq> domain W"
  proof
    fix x
    assume "x \<in> change_tv f ` domain U"
    then show "x \<in> domain W"
      unfolding domain_def
      by (cases x) (auto, metis Set.set_insert assms image_insert inj_from_to_def insertI1 subsetCE)
  qed
qed

(* Similar to eval_change_inj_on *)
lemma change_tv_surj_on:
  assumes "f ` U = W"
  shows "(change_tv f) ` (domain U) = (domain W)"
proof
  show "change_tv f ` domain U \<subseteq> domain W"
  proof
    fix x
    assume "x \<in> change_tv f ` domain U"
    then show "x \<in> domain W"
    proof
      fix x'
      assume "x = change_tv f x'" "x' \<in> domain U"
      then show "x \<in> domain W"
        unfolding domain_def using assms by fastforce
    qed
  qed
next
  show "domain W \<subseteq> change_tv f ` domain U"
  proof
    fix x
    assume "x \<in> domain W"
    then show "x \<in> change_tv f ` domain U"
      unfolding domain_def using assms image_iff by fastforce
  qed
qed

(* Similar to eval_change_inj_on *)
lemma change_tv_bij_betw:
  assumes "bij_betw f U W"
  shows "bij_betw (change_tv f) (domain U) (domain W)"
  using assms change_tv_injection_on change_tv_surj_on unfolding bij_betw_def by simp

(* Generalization of eval_change *)
lemma eval_change_inj_on:
  assumes "inj_on f U"
  assumes "range i \<subseteq> domain U"
  shows "eval (change_int f i) p = change_tv f (eval i p)"
proof (induct p)
  fix p
  assume "eval (change_int f i) p = change_tv f (eval i p)"
  then have "eval_neg (eval (change_int f i) p) = eval_neg (change_tv f (eval i p))"
    by simp
  then have "eval_neg (eval (change_int f i) p) = change_tv f (eval_neg (eval i p))"
    by (cases "eval i p") (simp_all add: case_bool_if)
  then show "eval (change_int f i) (Neg' p) = change_tv f (eval i (Neg' p))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Con' p1 p2) = change_tv f (eval i (Con' p1 p2))"
    using assms ih1 ih2 change_tv.simps(1) change_tv_injection_on eval.simps(2) eval.simps(4)
      inj_onD ranges by metis
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  have "Det (eval (change_int f i) p1 = eval (change_int f i) p2) =
      Det (change_tv f (eval i p1) = change_tv f (eval i p2))"
    using ih1 ih2
    by simp
  also have "... = Det ((eval i p1) = (eval i p2))"
  proof -
    have "inj_on (change_tv f) (domain U)"
      using assms(1) change_tv_injection_on by simp
    then show ?thesis
      using assms(2) ranges by (simp add: inj_on_eq_iff)
  qed
  also have "... = change_tv f (Det (eval i p1 = eval i p2))"
    by simp
  finally show "eval (change_int f i) (Eql p1 p2) = change_tv f (eval i (Eql p1 p2))"
    by simp
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
    using assms ih1 ih2 inj_on_eq_iff change_tv.simps(1) change_tv_injection_on eval_equality
      eval_negation ranges by smt
qed (simp_all add: change_int_def)

subsection \<open>Logics of equal cardinality are equal\<close>

(* We prove that validity in a set depends only on the cardinality of the set *)

lemma inj_from_to_valid_in:
  assumes "inj_from_to f W U"
  assumes "valid_in U p"
  shows "valid_in W p"
  unfolding valid_in_def proof (rule, rule)
  fix i :: "char list \<Rightarrow> tv"
  assume a: "range i \<subseteq> domain W"
  from assms have valid_p: "\<forall>i. range i \<subseteq> domain U \<longrightarrow> eval i p = \<bullet>"
    unfolding valid_in_def by simp
  have "range (change_int f i) \<subseteq> domain U"
  proof
    fix x
    assume "x \<in> range (change_int f i)"
    then obtain xa where xa: "change_int f i xa = x"
      by blast
    have "inj_from_to (change_tv f) (domain W) (domain U)"
      using change_tv_injection_from_to assms by simp
    then have "(change_tv f) (i xa) \<in> domain U"
      using a by (metis inj_from_to_def image_eqI range_eqI subsetCE)
    then show "x \<in> domain U"
      using xa change_int_def by simp
  qed
  then have "eval (change_int f i) p = \<bullet>"
    using valid_p by simp
  then have "eval (change_int f i) p = \<bullet>"
    by simp
  then have "change_tv f (eval i p) = \<bullet>"
    using a assms(1) eval_change_inj_on unfolding inj_from_to_def by metis
  then show "eval i p = \<bullet>"
    using change_tv.elims tv.distinct(1) by fast
qed

corollary
  assumes "inj_from_to f U W"
  assumes "inj_from_to g W U"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms inj_from_to_valid_in by fast

lemma bij_betw_valid_in:
  assumes "bij_betw f U W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms inj_from_to_valid_in bij_betw_inv bij_betw_inj_from_to by blast

theorem eql_finite_eql_card_valid_in:
  assumes "finite U \<longleftrightarrow> finite W"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
proof (cases "finite U")
  case True
  then show ?thesis
    using assms bij_betw_iff_card bij_betw_valid_in by metis
next
  case False
  then have "(\<exists>f :: nat \<Rightarrow> nat. bij_betw f U UNIV) \<and> (\<exists>g :: nat \<Rightarrow> nat. bij_betw g W UNIV)"
    using assms Schroeder_Bernstein infinite_iff_countable_subset inj_Suc top_greatest by metis
  with bij_betw_valid_in show ?thesis
    by metis
qed

corollary
  assumes "U \<noteq> {}"
  assumes "W \<noteq> {}"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using assms eql_finite_eql_card_valid_in card_gt_0_iff by metis

theorem finite_eql_card_valid_in:
  assumes "finite U"
  assumes "finite W"
  assumes "card U = card W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using eql_finite_eql_card_valid_in by (simp add: assms)

theorem infinite_valid_in:
  assumes "infinite U"
  assumes "infinite W"
  shows "valid_in U p \<longleftrightarrow> valid_in W p"
  using eql_finite_eql_card_valid_in by (simp add: assms)

subsection \<open>Conversions between nats and strings\<close>
definition nat_of_digit :: "char \<Rightarrow> nat" where
  "nat_of_digit c =
   (if c = (CHR ''1'') then 1 else if c = (CHR ''2'') then 2 else if c = (CHR ''3'') then 3 else
    if c = (CHR ''4'') then 4 else if c = (CHR ''5'') then 5 else if c = (CHR ''6'') then 6 else
    if c = (CHR ''7'') then 7 else if c = (CHR ''8'') then 8 else if c = (CHR ''9'') then 9 else 0)"

proposition "range nat_of_digit = {0..<10}"
proof
  show "range nat_of_digit \<subseteq> {0..<10}"
    unfolding nat_of_digit_def by auto
next
  show "{0..<10} \<subseteq> range nat_of_digit"
  proof
    fix x :: nat
    assume a: "x \<in> {0..<10}"
    show "x \<in> range nat_of_digit"
    proof (cases "x = 0")
      case True
      then show ?thesis
        unfolding nat_of_digit_def by auto
    next
      case False
      with a show ?thesis
        unfolding nat_of_digit_def by auto
    qed
  qed
qed

lemma nat_of_digit_of_nat[simp]: "n < 10 \<Longrightarrow> nat_of_digit (digit_of_nat n) = n"
  unfolding digit_of_nat_def nat_of_digit_def
  by simp presburger

function nat_of_string :: "string \<Rightarrow> nat"
  where
    "nat_of_string n = (if length n \<le> 1 then nat_of_digit (last n) else
      (nat_of_string (butlast n)) * 10 + (nat_of_digit (last n)))"
  by simp_all
termination
  by (relation "measure length") simp_all

lemma nat_of_string_step:
  "nat_of_string (string_of_nat (m div 10)) * 10 + m mod 10 = nat_of_string (string_of_nat m)"
  by simp

lemma nat_of_string_of_nat: "nat_of_string (string_of_nat n) = n"
proof (induct rule: string_of_nat.induct)
  case (1 m)
  then show ?case
  proof (cases "m < 10")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "nat_of_string (string_of_nat (m div 10)) = m div 10"
      using 1 by simp
    then have "nat_of_string (string_of_nat (m div 10)) * 10 = (m div 10) * 10"
      by simp
    then have "nat_of_string (string_of_nat (m div 10)) * 10 + (m mod 10) =
        (m div 10) * 10 + (m mod 10)"
      by simp
    also have "... = m"
      by simp
    finally show ?thesis
      using nat_of_string_step by simp
  qed
qed

lemma "inj string_of_nat"
  using inj_on_inverseI nat_of_string_of_nat by metis

subsection \<open>Derived formula constructors\<close>

definition PRO :: "id list \<Rightarrow> fm list" where
  "PRO ids \<equiv> map Pro ids"

definition Pro_nat :: "nat \<Rightarrow> fm" ("\<langle>_\<rangle>\<^sub>1" [40] 40) where
  "\<langle>n\<rangle>\<^sub>1 \<equiv> \<langle>string_of_nat n\<rangle>"

definition PRO_nat :: "nat list \<Rightarrow> fm list" ("\<langle>_\<rangle>\<^sub>1\<^sub>2\<^sub>3" [40] 40) where
  "\<langle>ns\<rangle>\<^sub>1\<^sub>2\<^sub>3 \<equiv> map Pro_nat ns"

definition CON :: "fm list \<Rightarrow> fm" ("[\<^bold>\<and>\<^bold>\<and>] _" [40] 40) where
  "[\<^bold>\<and>\<^bold>\<and>] ps \<equiv> foldr Con ps \<^bold>\<top>"

definition DIS :: "fm list \<Rightarrow> fm" ("[\<^bold>\<or>\<^bold>\<or>] _" [40] 40) where
  "[\<^bold>\<or>\<^bold>\<or>] ps \<equiv> foldr Dis ps \<^bold>\<bottom>"

definition NAB :: "fm list \<Rightarrow> fm" ("[\<^bold>\<nabla>] _" [40] 40) where
  "[\<^bold>\<nabla>] ps \<equiv> [\<^bold>\<and>\<^bold>\<and>] (map Nab ps)"

definition off_diagonal_product :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set" where
  "off_diagonal_product xs ys \<equiv> {(x,y). (x,y) \<in> (xs \<times> ys) \<and> x \<noteq> y }"

definition List_off_diagonal_product :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list" where
  "List_off_diagonal_product xs ys \<equiv> filter (\<lambda>(x,y). not_equal x y) (List.product xs ys)"

definition ExiEql :: "fm list \<Rightarrow> fm" ("[\<^bold>\<exists>\<^bold>=] _" [40] 40) where
  "[\<^bold>\<exists>\<^bold>=] ps \<equiv> [\<^bold>\<or>\<^bold>\<or>] (map (\<lambda>(x,y). x \<^bold>\<Leftrightarrow> y) (List_off_diagonal_product ps ps))"

lemma cla_false_Imp:
  assumes "eval i a = \<bullet>"
  assumes "eval i b = \<circ>"
  shows "eval i (a \<^bold>\<Rightarrow> b) = \<circ>"
  using assms by simp

lemma eval_CON:
  "eval i ([\<^bold>\<and>\<^bold>\<and>] ps) = Det (\<forall>p \<in> set ps. eval i p = \<bullet>)"
  unfolding CON_def
  by (induct ps) simp_all

lemma eval_DIS:
  "eval i ([\<^bold>\<or>\<^bold>\<or>] ps) = Det (\<exists>p \<in> set ps. eval i p = \<bullet>)"
  unfolding DIS_def
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case Cons
  with eval.simps eval_negation foldr.simps list.set_intros o_apply set_ConsD show ?case by smt
qed

lemma eval_Nab: "eval i (\<^bold>\<nabla> p) = Det (is_indet (eval i p))"
proof (induct p)
  case (Pro x)
  then show ?case
    using string_tv.cases tv.simps(5) tv.simps(6) eval_negation
      eval.simps(2) eval.simps(4) eval.simps(5) by smt
next
  case (Neg' p)
  then show ?case
    using eval_negation by fastforce
next
  case (Eql' p1 p2)
  then show ?case
    using string_tv.cases tv.simps(5) tv.simps(6) eval_negation
      eval.simps(2) eval.simps(4) eval.simps(5) by smt
qed auto

lemma eval_NAB:
  "eval i ([\<^bold>\<nabla>] ps) = Det (\<forall>p \<in> set ps. is_indet (eval i p))"
proof (cases "\<forall>p\<in>set ps. is_indet (eval i p)")
  case True
  then have "eval i (NAB ps) = Det True"
    unfolding NAB_def using eval_CON by fastforce
  then show ?thesis
    using True by simp
next
  case False
  then have "\<not> (\<forall>p\<in>set ps. eval i (Nab p) = Det True)"
    using eval_Nab by simp
  then have "\<not> (\<forall>p\<in>set (map Nab ps). eval i p = Det True)"
    by simp
  then have "eval i (NAB ps) = Det False"
    unfolding NAB_def using eval_CON[of i "(map Nab ps)"] by simp
  then show ?thesis
    using False by simp
qed

lemma eval_ExiEql:
  "eval i ([\<^bold>\<exists>\<^bold>=] ps) =
    Det (\<exists>(p1, p2)\<in>(off_diagonal_product (set ps) (set ps)). eval i p1 = eval i p2)"
  using eval_DIS[of i "(map (\<lambda>(x, y). Eql x y) (List_off_diagonal_product ps ps))"]
  unfolding off_diagonal_product_def ExiEql_def List_off_diagonal_product_def
  by auto

subsection \<open>Pigeon hole formula\<close>

definition pigeonhole_fm :: "nat \<Rightarrow> fm" where
  "pigeonhole_fm n \<equiv> [\<^bold>\<nabla>] \<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3 \<^bold>\<Rightarrow> [\<^bold>\<exists>\<^bold>=] \<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3"

definition interp_of_id :: "nat \<Rightarrow> id \<Rightarrow> tv" where
  "interp_of_id maxi i \<equiv> if (nat_of_string i) < maxi then Indet (nat_of_string i) else Det True"

lemma interp_of_id_pigeonhole_fm_False: "eval (interp_of_id n) (pigeonhole_fm n) = Det False"
proof -
  have all_indet: "\<forall>p \<in> set (PRO_nat [0..<n]). is_indet (eval (interp_of_id n) p)"
  proof
    fix p
    assume a: "p \<in> set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)"
    show "is_indet (eval (interp_of_id n) p)"
    proof -
      from a have "p \<in> Pro_nat ` {..<n}"
        unfolding PRO_nat_def using atLeast_upt set_map by metis
      then have "\<exists>m<n. p = Pro (string_of_nat m)"
        unfolding Pro_nat_def by fast
      then show ?thesis
        unfolding interp_of_id_def using nat_of_string_of_nat by fastforce
    qed
  qed
  then have "eval (interp_of_id n) (NAB (PRO_nat [0..<n])) = Det True"
    using eval_NAB by simp
  moreover
  have "\<forall>a b. a \<in> set (map (\<lambda>n. Pro (string_of_nat n)) [0..<n]) \<longrightarrow>
         b \<in> set (map (\<lambda>n. Pro (string_of_nat n)) [0..<n]) \<longrightarrow> a \<noteq> b \<longrightarrow>
         eval (interp_of_id n) a = eval (interp_of_id n) b \<longrightarrow> False"
    using all_indet in_set_conv_nth length_map nat_of_string_of_nat nth_map tv.inject tv.simps(5)
      eval.simps(1)
    unfolding interp_of_id_def PRO_def PRO_nat_def Pro_nat_def
    by smt
  then have "\<forall>(p1, p2)\<in>off_diagonal_product (set (PRO_nat [0..<n])) (set (PRO_nat [0..<n])).
               eval (interp_of_id n) p1 \<noteq> eval (interp_of_id n) p2"
    unfolding off_diagonal_product_def PRO_nat_def Pro_nat_def by blast
  then have "\<not> (\<exists>(p1, p2)\<in>off_diagonal_product (set (PRO_nat [0..<n])) (set (PRO_nat [0..<n])).
              eval (interp_of_id n) p1 = eval (interp_of_id n) p2)"
    by blast
  then have "eval (interp_of_id n) (ExiEql (PRO_nat [0..<n])) = Det False"
    using eval_ExiEql[of "interp_of_id n" "PRO_nat [0..<n]"] by simp
  ultimately
  show ?thesis
    unfolding pigeonhole_fm_def using cla_false_Imp[of "interp_of_id n"] by blast
qed

lemma range_interp_of_id: "range (interp_of_id n) \<subseteq> domain {0..<n}"
  unfolding interp_of_id_def domain_def by (simp add: image_subset_iff)

theorem not_valid_in_n_pigeonhole_fm: "\<not> (valid_in {0..<n} (pigeonhole_fm n))"
  unfolding valid_in_def using interp_of_id_pigeonhole_fm_False[of n] range_interp_of_id[of n]
  by fastforce

theorem not_valid_pigeonhole_fm: "\<not> (valid (pigeonhole_fm n))"
  unfolding valid_def using interp_of_id_pigeonhole_fm_False[of n]
  by fastforce

lemma cla_imp_I:
  assumes "is_det (eval i a)"
  assumes "is_det (eval i b)"
  assumes "eval i a = \<bullet> \<Longrightarrow> eval i b = \<bullet>"
  shows "eval i (a \<^bold>\<Rightarrow> b) = \<bullet>"
proof -
  have "is_det tv = (case tv of Det _ \<Rightarrow> True | Indet _ \<Rightarrow> False)" for tv
    by (metis (full_types) tv.exhaust tv.simps(5) tv.simps(6))
  then show ?thesis
    using assms
    by (metis (full_types) eval.simps(4) eval.simps(5) tv.exhaust tv.simps(6))
qed

lemma is_det_NAB: "is_det (eval i ([\<^bold>\<nabla>] ps))"
  unfolding eval_NAB by auto

lemma is_det_ExiEql: "is_det (eval i ([\<^bold>\<exists>\<^bold>=] ps))"
  using eval_ExiEql by auto

lemma pigeonhole_nat:
  assumes "finite n"
  assumes "finite m"
  assumes "card n > card m"
  assumes "f ` n \<subseteq> m"
  shows "\<exists>x\<in>n. \<exists>y\<in>n. x \<noteq> y \<and> f x = f y"
  using assms not_le inj_on_iff_card_le unfolding inj_on_def
  by metis

lemma pigeonhole_nat_set:
  assumes "f ` {0..<n} \<subseteq> {0..<m}"
  assumes "m < (n :: nat)"
  shows "\<exists>j1\<in>{0..<n}. \<exists>j2\<in>{0..<n}. j1 \<noteq> j2 \<and> f j1 = f j2"
  using assms pigeonhole_nat[of "({0..<n})" "{0..<m}" f]
  by simp

lemma inj_Pro_nat: "(\<langle>p1\<rangle>\<^sub>1) = (\<langle>p2\<rangle>\<^sub>1) \<Longrightarrow> p1 = p2"
  unfolding Pro_nat_def using fm.inject(1) nat_of_string_of_nat
  by metis

lemma eval_true_in_lt_n_pigeonhole_fm:
  assumes "m < n"
  assumes "range i \<subseteq> domain {0..<m}"
  shows "eval i (pigeonhole_fm n) = \<bullet>"
proof -
  {
    assume "eval i (NAB (PRO_nat [0..<n])) = Det True"
    then have "\<forall>p \<in> set (PRO_nat [0..<n]). is_indet (eval i p)"
      using eval_NAB by auto
    then have *: "\<forall>j<n. is_indet (eval i (Pro_nat j))"
      unfolding PRO_nat_def by auto
    have **: "\<forall>j<n. \<exists>k<m. eval i (Pro_nat j) = Indet k"
    proof -
      have "\<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> \<exists>k<m. eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>k\<rfloor>)" for j
      proof (rule_tac x="get_indet (i (string_of_nat j))" in exI)
        show "\<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> get_indet (i (string_of_nat j)) < m \<and>
               eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>get_indet (i (string_of_nat j))\<rfloor>)"
        proof (induct "i (string_of_nat j)")
          case (Det x)
          then show ?case
            unfolding Pro_nat_def using eval.simps(1) tv.simps(5) by metis
        next
          case (Indet x)
          then show ?case
          proof (subgoal_tac "x<m")
            show "(\<lfloor>x\<rfloor>) = i (string_of_nat j) \<Longrightarrow> \<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow>
                   x < m \<Longrightarrow> get_indet (i (string_of_nat j)) < m \<and>
                   eval i (\<langle>j\<rangle>\<^sub>1) = (\<lfloor>get_indet (i (string_of_nat j))\<rfloor>)"
              unfolding Pro_nat_def using eval.simps(1) tv.simps(6) by metis
          next
            show "(\<lfloor>x\<rfloor>) = i (string_of_nat j) \<Longrightarrow> \<forall>j<n. is_indet (eval i (\<langle>j\<rangle>\<^sub>1)) \<Longrightarrow> j < n \<Longrightarrow> x < m"
              using assms(2) atLeast0LessThan unfolding domain_def by fast
          qed
        qed
      qed
      then show ?thesis
        using * by simp
    qed
    then have "\<forall>j<n. \<exists>k<m. get_indet (eval i (Pro_nat j)) = k"
      by fastforce
    then have "(\<lambda>j. get_indet (eval i (Pro_nat j))) ` {0..<n} \<subseteq> {0..<m}"
      by fastforce
    then have "\<exists>j1 \<in> {0..<n}. \<exists>j2 \<in> {0..<n}. j1 \<noteq> j2 \<and> get_indet (eval i (Pro_nat j1)) =
                get_indet (eval i (Pro_nat j2))"
      using assms(1) pigeonhole_nat_set by simp
    then have "\<exists>j1 < n. \<exists>j2 < n. j1 \<noteq> j2 \<and> get_indet (eval i (Pro_nat j1)) =
                get_indet (eval i (Pro_nat j2))"
      using atLeastLessThan_iff by blast
    then have "\<exists>j1 < n. \<exists>j2 < n. j1 \<noteq> j2 \<and> eval i (Pro_nat j1) = eval i (Pro_nat j2)"
      using ** tv.simps(6) by metis
    then have "\<exists>(p1, p2)\<in>off_diagonal_product (set (PRO_nat [0..<n])) (set (PRO_nat [0..<n])).
                 eval i p1 = eval i p2"
    proof (rule_tac P="\<lambda>j1. j1<n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (Pro_nat j1) =
                        eval i (Pro_nat j2))" in exE)
      show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
              \<exists>x<n. \<exists>j2<n. x \<noteq> j2 \<and> eval i (\<langle>x\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)"
        by simp
    next
      show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
              j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
              \<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
              eval i p1 = eval i p2" for j1
      proof (rule_tac P="\<lambda>j2. j2<n \<and> j1 \<noteq> j2 \<and> eval i (Pro_nat j1) = eval i (Pro_nat j2)" in exE)
        show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
                \<exists>x<n. j1 \<noteq> x \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>x\<rangle>\<^sub>1)"
          by simp
      next
        show "\<exists>j1<n. \<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                j1 < n \<and> (\<exists>j2<n. j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1)) \<Longrightarrow>
                j2 < n \<and> j1 \<noteq> j2 \<and> eval i (\<langle>j1\<rangle>\<^sub>1) = eval i (\<langle>j2\<rangle>\<^sub>1) \<Longrightarrow>
                \<exists>(p1, p2)\<in>off_diagonal_product (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)) (set (\<langle>[0..<n]\<rangle>\<^sub>1\<^sub>2\<^sub>3)).
                eval i p1 = eval i p2" for j2
          unfolding off_diagonal_product_def PRO_nat_def using inj_Pro_nat
          by (rule_tac x="(Pro_nat j1, Pro_nat j2)" in bexI) auto
      qed
    qed
    then have "eval i (ExiEql (PRO_nat [0..<n])) = Det True"
      using eval_ExiEql by simp
  }
  then show ?thesis
    unfolding pigeonhole_fm_def using cla_imp_I is_det_ExiEql is_det_NAB by simp
qed

theorem valid_in_lt_n_pigeonhole_fm:
  assumes "m<n"
  shows "valid_in {0..<m} (pigeonhole_fm n)"
  using assms
  unfolding valid_in_def
  using interp_of_id_pigeonhole_fm_False[of n]
  using range_interp_of_id[of n]
  using eval_true_in_lt_n_pigeonhole_fm
  by simp

theorem not_valid_in_pigeonhole_fm_card:
  assumes "finite U"
  shows "\<not> valid_in U (pigeonhole_fm (card U))"
  using assms ex_bij_betw_nat_finite not_valid_in_n_pigeonhole_fm bij_betw_valid_in by metis

theorem not_valid_in_pigeonhole_fm_lt_card:
  assumes "finite (U::nat set)"
  assumes "inj_from_to f U W"
  shows "\<not> valid_in W (pigeonhole_fm (card U))"
proof -
  have "\<not> valid_in U (pigeonhole_fm (card U))"
    using not_valid_in_pigeonhole_fm_card assms by simp
  then show ?thesis
    using assms inj_from_to_valid_in by metis
qed

theorem valid_in_pigeonhole_fm_n_gt_card:
  assumes "finite U"
  assumes "card U < n"
  shows "valid_in U (pigeonhole_fm n)"
  using assms ex_bij_betw_finite_nat bij_betw_valid_in valid_in_lt_n_pigeonhole_fm by metis

subsection \<open>Validity is the intersection of the finite logics\<close>

lemma "valid p \<longleftrightarrow> (\<forall>U. finite U \<longrightarrow> valid_in U p)"
proof
  assume "valid p"
  then show "\<forall>U. finite U \<longrightarrow> valid_in U p"
    using transfer by blast
next
  assume "\<forall>U. finite U \<longrightarrow> valid_in U p"
  then have "valid_in {1..card (props p)} p"
    by simp
  then show "valid p"
    using reduce by simp
qed

subsection \<open>Logics of different cardinalities are different\<close>

lemma finite_card_lt_valid_in_not_valid_in:
  assumes "finite U"
  assumes "card U < card W"
  shows "valid_in U \<noteq> valid_in W"
proof -
  have finite_W: "finite W"
    using assms(2) card_infinite by fastforce
  have "valid_in U (pigeonhole_fm (card W))"
    using valid_in_pigeonhole_fm_n_gt_card assms by simp
  moreover
  have "\<not> valid_in W (pigeonhole_fm (card W))"
    using not_valid_in_pigeonhole_fm_card assms finite_W by simp
  ultimately show ?thesis
    by fastforce
qed

lemma valid_in_UNIV_p_valid: "valid_in UNIV p = valid p"
  using universal_domain valid_def valid_in_def by simp

theorem infinite_valid_in_valid:
  assumes "infinite U"
  shows "valid_in U p \<longleftrightarrow> valid p"
  using assms infinite_valid_in[of U UNIV p] valid_in_UNIV_p_valid by simp

lemma finite_not_finite_valid_in_not_valid_in:
  assumes "finite U \<noteq> finite W"
  shows "valid_in U \<noteq> valid_in W"
proof -
  {
    fix U W :: "nat set"
    assume inf: "infinite U"
    assume fin: "finite W"
    then have valid_in_W_pigeonhole_fm: "valid_in W (pigeonhole_fm (Suc (card W)))"
      using valid_in_pigeonhole_fm_n_gt_card[of W] by simp
    have "\<not> valid (pigeonhole_fm (Suc (card W)))"
      using not_valid_pigeonhole_fm by simp
    then have "\<not> valid_in U (pigeonhole_fm (Suc (card W)))"
      using inf fin infinite_valid_in_valid by simp
    then have "valid_in U \<noteq> valid_in W"
      using valid_in_W_pigeonhole_fm by fastforce
  }
  then show ?thesis
    using assms by metis
qed

lemma card_not_card_valid_in_not_valid_in:
  assumes "card U \<noteq> card W"
  shows "valid_in U \<noteq> valid_in W"
  using assms
proof -
  {
    fix U W :: "nat set"
    assume a: "card U < card W"
    then have "finite W"
      using card_infinite gr_implies_not0 by blast
    then have valid_in_W_pigeonhole_fm: "valid_in W (pigeonhole_fm (Suc (card W)))"
      using valid_in_pigeonhole_fm_n_gt_card[of W] by simp
    have "valid_in U \<noteq> valid_in W"
    proof (cases "finite U")
      case True
      then show ?thesis
        using a finite_card_lt_valid_in_not_valid_in by simp
    next
      case False
      have "\<not> valid (pigeonhole_fm (Suc (card W)))"
        using not_valid_pigeonhole_fm by simp
      then have "\<not> valid_in U (pigeonhole_fm (Suc (card W)))"
        using False infinite_valid_in_valid by simp
      then show ?thesis
        using valid_in_W_pigeonhole_fm by fastforce
    qed
  }
  then show ?thesis
    using assms neqE by metis
qed

subsection \<open>Finite logics are different from infinite logics\<close>

theorem extend: "valid \<noteq> valid_in U" if "finite U"
  using that not_valid_pigeonhole_fm valid_in_pigeonhole_fm_n_gt_card by fastforce

corollary "\<not> (\<exists>n. \<forall>p. valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "\<forall>n. \<exists>p. \<not> (valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "\<not> (\<forall>p. valid p \<longleftrightarrow> valid_in {0..n} p)"
  using extend by fast

corollary "valid \<noteq> valid_in {0..n}"
  using extend by simp

proposition "valid = valid_in {0..}"
  unfolding valid_def valid_in_def
  using universal_domain
  by simp

corollary "valid = valid_in {n..}"
  using infinite_valid_in[of UNIV "{n..}"] universal_domain
  unfolding valid_def valid_in_def
  by (simp add: infinite_Ici)

corollary "\<not> (\<exists>n m. \<forall>p. valid p \<longleftrightarrow> valid_in {m..n} p)"
  using extend by fast

end \<comment> \<open>Paraconsistency file\<close>
