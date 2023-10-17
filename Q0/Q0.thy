theory Q0 
  imports Set_Theory 
  abbrevs "App" = "\<^bold>\<cdot>"
    and "Abs" = "\<^bold>[\<^bold>\<lambda>_:_. _\<^bold>]"
    and "Eql" = "\<^bold>[_ \<^bold>=_\<^bold>= _\<^bold>]"
    and "Con" = "\<^bold>\<and>"
    and "Forall" = "\<^bold>[\<^bold>\<forall>_:_. _\<^bold>]"
    and "Imp" = "\<^bold>\<longrightarrow>"
begin


section \<open>Syntax and Typing\<close>

datatype type_sym =
  Ind |
  Tv |
  Fun type_sym type_sym

type_synonym var_sym = string
type_synonym cst_sym = string

datatype form = 
  Var var_sym type_sym |
  Cst cst_sym type_sym |
  App form form (infix "\<^bold>\<cdot>" 80) |
  Abs var_sym type_sym form ("\<^bold>[\<^bold>\<lambda>_:_. _\<^bold>]" [80,80,80])

fun frees :: "form \<Rightarrow> (var_sym * type_sym) set" where
  "frees (Var x \<alpha>) = {(x,\<alpha>)}"
| "frees (Cst _ _) = {}"
| "frees (A \<^bold>\<cdot> B) = frees A \<union> frees B"
| "frees (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) = frees A - {(x,\<alpha>)}"

inductive wff :: "type_sym \<Rightarrow> form \<Rightarrow> bool" where
  wff_Var: "wff \<alpha> (Var _ \<alpha>)"
| wff_Cst: "wff \<alpha> (Cst _ \<alpha>)"
| wff_App: "wff (Fun \<alpha> \<beta>) A \<Longrightarrow> wff \<beta> B \<Longrightarrow> wff \<alpha> (A \<^bold>\<cdot> B)"
| wff_Abs: "wff \<beta> A \<Longrightarrow> wff (Fun \<beta> \<alpha>) \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"

fun type_of :: "form \<Rightarrow> type_sym" where
  "type_of (Var x \<alpha>) = \<alpha>"
| "type_of (Cst c \<alpha>) = \<alpha>"
| "type_of (A \<^bold>\<cdot> B) =
     (case type_of A of Fun \<beta> \<alpha> \<Rightarrow> \<beta>)"
| "type_of \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] = (Fun (type_of A)) \<alpha>"

lemma type_of[simp]:
  "wff \<alpha> A \<Longrightarrow> type_of A = \<alpha>"
  by (induction rule: wff.induct) auto

lemma wff_Var'[simp, code]: 
  "wff \<beta> (Var x \<alpha>) \<longleftrightarrow> \<beta> = \<alpha>"
  using wff.cases wff_Var by auto

lemma wff_Cst'[simp, code]:
  "wff \<beta> (Cst c \<alpha>) \<longleftrightarrow> \<beta> = \<alpha>"
  using wff.cases wff_Cst by auto

lemma wff_App'[simp]:
  "wff \<alpha> (A \<^bold>\<cdot> B) \<longleftrightarrow> (\<exists>\<beta>. wff (Fun \<alpha> \<beta>) A \<and> wff \<beta> B)"
proof
  assume "wff \<alpha> (A \<^bold>\<cdot> B)"
  then show "\<exists>\<beta>. wff (Fun \<alpha> \<beta>) A \<and> wff \<beta> B" 
    using wff.cases by fastforce
next
  assume "\<exists>\<beta>. wff (Fun \<alpha> \<beta>) A \<and> wff \<beta> B"
  then show "wff \<alpha> (A \<^bold>\<cdot> B)"
    using wff_App by auto
qed

lemma wff_Abs'[simp]:
  "wff \<gamma> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) \<longleftrightarrow> (\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = Fun \<beta> \<alpha>)"
proof
  assume "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  then show "\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = Fun \<beta> \<alpha>" 
    using wff.cases by blast
next
  assume "\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = Fun \<beta> \<alpha>"
  then show "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]" 
    using wff_Abs by auto     
qed

lemma wff_Abs_type_of[code]:
  "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] \<longleftrightarrow> (wff (type_of A) A \<and> \<gamma> = Fun (type_of A) \<alpha>)"
proof
  assume "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  then show "wff (type_of A) A \<and> \<gamma> = Fun (type_of A) \<alpha>" 
    using wff.cases by auto
next
  assume "wff (type_of A) A \<and> \<gamma> = Fun (type_of A) \<alpha>"
  then show "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]" 
    using wff_Abs by auto
qed

lemma wff_App_type_of[code]:
  "wff \<gamma> ((A \<^bold>\<cdot> B)) \<longleftrightarrow> (wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = Fun \<gamma> (type_of B))"
proof
  assume "wff \<gamma> (A \<^bold>\<cdot> B)"
  then show "wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = Fun \<gamma> (type_of B)" 
    by auto
next
  assume "wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = Fun \<gamma> (type_of B)"
  then show "wff \<gamma> (A \<^bold>\<cdot> B)"
    by (metis wff_App')
qed

lemma unique_type:
  "wff \<beta> A \<Longrightarrow> wff \<alpha> A \<Longrightarrow> \<alpha> = \<beta>"
proof (induction arbitrary: \<alpha> rule: wff.induct)
  case (wff_Var \<alpha>' y)
  then show ?case
    by simp
next
  case (wff_Cst \<alpha>' c)
  then show ?case
    by simp 
next
  case (wff_App \<alpha>' \<beta> A B)
  then show ?case
    using wff_App' by blast
next
  case (wff_Abs \<beta> A \<alpha> x)
  then show ?case
    using wff_Abs_type_of by blast
qed


section \<open>Replacement\<close>

inductive replacement :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  replace: "replacement A B A B"
| replace_App_left: "replacement A B C E \<Longrightarrow> replacement A B (C \<^bold>\<cdot> D) (E \<^bold>\<cdot> D)"
| replace_App_right: "replacement A B D E \<Longrightarrow> replacement A B (C \<^bold>\<cdot> D) (C \<^bold>\<cdot> E)"
| replace_Abs: "replacement A B C D \<Longrightarrow> replacement A B \<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>[\<^bold>\<lambda>x:\<alpha>. D\<^bold>]"

lemma replacement_preserves_type:
  assumes "replacement A B C D"
  assumes "wff \<alpha> A"
  assumes "wff \<alpha> B"
  assumes "wff \<beta> C"
  shows "wff \<beta> D"
  using assms
proof (induction arbitrary: \<alpha> \<beta> rule: replacement.induct)
  case (replace A B)
  then show ?case
    using unique_type by auto
next
  case (replace_App_left A B C E D)
  then have "\<exists>\<beta>'. wff (Fun \<beta> \<beta>') C"
    by auto
  then obtain \<beta>' where wff_C: "wff (Fun \<beta> \<beta>') C"
    by auto
  then have e: "wff (Fun \<beta> \<beta>') E"
    using replace_App_left by auto
  define \<alpha>' where "\<alpha>' = Fun \<beta> \<beta>'"
  have "wff \<beta>' D"
    using wff_C unique_type replace_App_left.prems(3) by auto
  then have "wff \<beta> (E \<^bold>\<cdot> D)"
    using e by auto
  then show ?case
    by auto
next
  case (replace_App_right A B D E C)
  have "\<exists>\<beta>'. wff (Fun \<beta> \<beta>') C"
    using replace_App_right.prems(3) by auto
  then obtain \<beta>' where wff_C: "wff (Fun \<beta> \<beta>') C"
    by auto
  have wff_E: "wff \<beta>' E"
    using wff_C unique_type replace_App_right by fastforce
  define \<alpha>' where \<alpha>': "\<alpha>' = Fun \<beta> \<beta>'"
  have "wff \<beta> (C \<^bold>\<cdot> E)"
    using wff_C wff_E by auto
  then show ?case
    using \<alpha>' by auto
next
  case (replace_Abs A B C D x \<alpha>')
  then have "\<exists>\<beta>'. wff \<beta>' D"
    by auto
  then obtain \<beta>' where wff_D: "wff \<beta>' D"
    by auto
  have \<beta>: "\<beta> = Fun \<beta>' \<alpha>'"
    using wff_D unique_type replace_Abs by auto
  have "wff (Fun \<beta>' \<alpha>') (\<^bold>[\<^bold>\<lambda>x:\<alpha>'. D\<^bold>])"
    using wff_D by auto
  then show ?case
    using \<beta> by auto
qed

lemma replacement_preserved_type:
  assumes "replacement A B C D"
  assumes "wff \<alpha> A"
  assumes "wff \<alpha> B"
  assumes "wff \<beta> D"
  shows "wff \<beta> C"
  using assms
proof (induction arbitrary: \<alpha> \<beta> rule: replacement.induct)
  case (replace A B)
  then show ?case 
    using unique_type by auto
next
  case (replace_App_left A B C E D)
  then obtain \<gamma> where \<gamma>: "wff (Fun \<beta> \<gamma>) E \<and> wff \<gamma> D"
    by auto
  then have "wff (Fun \<beta> \<gamma>) C"
    using replace_App_left by auto
  then show ?case
    using \<gamma> by auto 
next
  case (replace_App_right A B D E C)
  then obtain \<gamma> where \<gamma>: "wff (Fun \<beta> \<gamma>) C \<and> wff \<gamma> E"
    by auto
  then have "wff \<gamma> D"
    using replace_App_right by auto
  then show ?case
    using \<gamma> by auto 
next
  case (replace_Abs A B C D x \<alpha>')
  then obtain \<gamma> where "wff \<gamma> D"
    by auto
  then show ?case
    using unique_type replace_Abs by auto
qed


section \<open>Auxillary formulas\<close>
\<comment> \<open>This section formalizes most of the definitions and abbreviations from page 212.
    We formalize enough to define the Q0 proof system.\<close>

definition Eql :: "form \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form" where
  "Eql A B \<alpha> \<equiv> ((Cst ''Q'' (Fun (Fun Tv \<alpha>) \<alpha>)) \<^bold>\<cdot> A) \<^bold>\<cdot> B"

abbreviation Eql' :: "form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" ("\<^bold>[_ \<^bold>=_\<^bold>= _\<^bold>]" [89]) where
  "\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] \<equiv> Eql A B \<alpha>"

definition LHS where
  "LHS EqlAB = (case EqlAB of ((_ \<^bold>\<cdot> A) \<^bold>\<cdot> _) \<Rightarrow> A)"

lemma LHS_def2[simp]: "LHS \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] = A"
  unfolding LHS_def Eql_def by auto

definition RHS where
  "RHS EqlAB = (case EqlAB of (_ \<^bold>\<cdot> B ) \<Rightarrow> B)"

lemma RHS_def2[simp]: "RHS (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = B"
  unfolding RHS_def Eql_def by auto

lemma wff_Eql[simp]:
  "wff \<alpha> A \<Longrightarrow> wff \<alpha> B \<Longrightarrow> wff Tv \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]"
  unfolding Eql_def by force

lemma wff_Eql'[simp]:
  "wff \<beta> \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] \<longleftrightarrow> wff \<alpha> A \<and> wff \<alpha> B \<and> \<beta> = Tv"
  using Eql_def by auto

definition T :: form where
  "T \<equiv> \<^bold>[(Cst ''Q'' (Fun (Fun Tv Tv) Tv)) \<^bold>=Fun (Fun Tv Tv) Tv\<^bold>= (Cst ''Q'' (Fun (Fun Tv Tv) Tv))\<^bold>]"

lemma wff_T[simp]: "wff Tv T"
  unfolding T_def by auto

lemma wff_T'[simp]: "wff \<alpha> T \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_T by blast

abbreviation F :: form where
  "F \<equiv> \<^bold>[\<^bold>[\<^bold>\<lambda> ''x'':Tv. T\<^bold>] \<^bold>=Fun Tv Tv\<^bold>= \<^bold>[\<^bold>\<lambda>''x'':Tv. Var ''x'' Tv\<^bold>]\<^bold>]"

lemma wff_F[simp]: "wff Tv F"
  by auto

lemma wff_F'[simp]: "wff \<alpha> F \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_F by blast

definition PI_Aux :: "type_sym \<Rightarrow> form" where
  "PI_Aux \<alpha> \<equiv> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>]"

lemma wff_PI_Aux[simp]: "wff (Fun Tv \<alpha>) (PI_Aux \<alpha>)"
  unfolding PI_Aux_def by auto

lemma wff_PI_Aux'[simp]:
  "wff \<beta> (PI_Aux \<alpha>) \<longleftrightarrow> \<beta> = (Fun Tv \<alpha>)"
  unfolding PI_Aux_def by auto

definition PI :: "type_sym \<Rightarrow> form" where 
  "PI \<alpha> \<equiv> (Cst ''Q'' (Fun (Fun Tv (Fun Tv \<alpha>)) (Fun Tv \<alpha>))) \<^bold>\<cdot> (PI_Aux \<alpha>)"

lemma wff_PI[simp]: "wff (Fun Tv (Fun Tv \<alpha>)) (PI \<alpha>)"
  unfolding PI_def by auto

definition Forall :: "string \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" ("\<^bold>[\<^bold>\<forall>_:_. _\<^bold>]" [80,80,80]) where 
  "\<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] = (PI \<alpha>) \<^bold>\<cdot> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"

lemma wff_Forall[simp]: "wff Tv A \<Longrightarrow> wff Tv \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]"
  unfolding Forall_def by force

lemma wff_Forall'[simp]: "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] \<longleftrightarrow> wff Tv A \<and> \<beta> = Tv"
proof 
  assume "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]"
  then show "wff Tv A \<and> \<beta> = Tv"
    by (smt Forall_def unique_type type_sym.inject wff_Abs' wff_App' wff_PI)
next
  assume "wff Tv A \<and> \<beta> = Tv"
  then show "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]" 
    unfolding Forall_def by force
qed

definition Con_Aux0 :: "form \<Rightarrow> form \<Rightarrow> form" where
  "Con_Aux0 \<equiv> \<lambda>A B. \<^bold>[\<^bold>\<lambda>''g'':Fun (Fun Tv Tv) Tv. ((Var ''g'' (Fun (Fun Tv Tv) Tv)) \<^bold>\<cdot> A) \<^bold>\<cdot> B\<^bold>]"

lemma wff_Con_Aux0[simp]:
  "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff (Fun Tv (Fun (Fun Tv Tv) Tv)) (Con_Aux0 A B)"
  unfolding Con_Aux0_def by force

lemma wff_Con_Aux0'[simp]:
  "wff \<beta> (Con_Aux0 A B) \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<beta> = (Fun Tv (Fun (Fun Tv Tv) Tv))"
proof
  assume wff: "wff \<beta> (Con_Aux0 A B)"
  then have "wff Tv A"
    unfolding Con_Aux0_def by auto
  moreover
  from wff have "wff Tv B"
    unfolding Con_Aux0_def by auto
  moreover
  from wff have "\<beta> = Fun Tv (Fun (Fun Tv Tv) Tv)"
    unfolding Con_Aux0_def by auto
  ultimately show "wff Tv A \<and> wff Tv B \<and> \<beta> = Fun Tv (Fun (Fun Tv Tv) Tv)"
    by auto
next
  assume "wff Tv A \<and> wff Tv B \<and> \<beta> = Fun Tv (Fun (Fun Tv Tv) Tv)"
  then show "wff \<beta> (Con_Aux0 A B)"
    unfolding Con_Aux0_def by force
qed

definition Con_Aux1 :: form where
  "Con_Aux1 \<equiv> \<^bold>[(Con_Aux0 T T) \<^bold>=(Fun Tv (Fun (Fun Tv Tv) Tv))\<^bold>= (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))\<^bold>]"

lemma wff_Con_Aux1[simp]: "wff Tv Con_Aux1"
  unfolding Con_Aux1_def by auto

lemma wff_Con_Aux1'[simp]: "wff \<alpha> Con_Aux1 \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_Con_Aux1 by blast

definition Con_Aux2 :: form where
  "Con_Aux2 \<equiv> \<^bold>[\<^bold>\<lambda> ''y'':Tv. Con_Aux1\<^bold>]"

lemma wff_Con_Aux2[simp]:
  "wff (Fun Tv Tv) (Con_Aux2)"
  unfolding Con_Aux2_def by auto

lemma wff_Con_Aux2'[simp]:
  "wff \<alpha> (Con_Aux2) \<longleftrightarrow> \<alpha> = Fun Tv Tv"
  unfolding Con_Aux2_def by auto

definition Con_sym :: form where
  "Con_sym \<equiv> \<^bold>[\<^bold>\<lambda> ''x'':Tv. Con_Aux2\<^bold>]"

lemma wff_Con_sym[simp]: "wff (Fun (Fun Tv Tv) Tv) Con_sym"
  unfolding Con_sym_def by auto

lemma wff_Con_sym'[simp]: "wff \<alpha> Con_sym \<longleftrightarrow> \<alpha> =(Fun (Fun Tv Tv) Tv)"
  unfolding Con_sym_def by auto

definition Con :: "form \<Rightarrow> form \<Rightarrow> form" (infix "\<^bold>\<and>" 80) where
  "A \<^bold>\<and> B = (Con_sym \<^bold>\<cdot> A) \<^bold>\<cdot> B"

lemma wff_Con[simp]: "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff Tv (A \<^bold>\<and> B)"
  unfolding Con_def by auto

lemma wff_Con'[simp]: "wff \<alpha> (A \<^bold>\<and> B) \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<alpha> = Tv"
  unfolding Con_def by auto

definition Imp_Aux0 :: form where
  "Imp_Aux0 = Con_sym \<^bold>\<cdot> (Var ''x'' Tv)"

lemma wff_Imp_Aux0[simp]:
  "wff (Fun Tv Tv) Imp_Aux0"
  unfolding Imp_Aux0_def by auto

lemma wff_Imp_Aux0'[simp]:
  "wff \<alpha> Imp_Aux0 \<longleftrightarrow> \<alpha> = Fun Tv Tv"
  unfolding Imp_Aux0_def by auto

definition Imp_Aux1 :: form where
  "Imp_Aux1 \<equiv> Imp_Aux0 \<^bold>\<cdot> (Var ''y'' Tv)"

lemma wff_Imp_Aux1[simp]:
  "wff Tv Imp_Aux1"
  unfolding Imp_Aux1_def by auto

lemma wff_Imp_Aux1'[simp]:
  "wff \<alpha> Imp_Aux1 \<longleftrightarrow> \<alpha> = Tv"
  unfolding Imp_Aux1_def by auto

definition Imp_Aux2 :: form where
  "Imp_Aux2 \<equiv> \<^bold>[Var ''x'' Tv \<^bold>=Tv\<^bold>= Imp_Aux1\<^bold>]"

lemma wff_Imp_Aux2[simp]:
  "wff Tv Imp_Aux2"
  unfolding Imp_Aux2_def by auto

lemma wff_Imp_Aux2'[simp]:
  "wff \<alpha> Imp_Aux2 \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_Imp_Aux2 by blast

definition Imp_Aux3 :: form where
  "Imp_Aux3 \<equiv> \<^bold>[\<^bold>\<lambda> ''y'':Tv. Imp_Aux2\<^bold>]"

lemma wff_Imp_Aux3[simp]:
  "wff (Fun Tv Tv) Imp_Aux3"
  unfolding Imp_Aux3_def by auto

lemma wff_Imp_Aux3'[simp]:
  "wff \<alpha> Imp_Aux3 \<longleftrightarrow> \<alpha> = Fun Tv Tv"
  unfolding Imp_Aux3_def by auto

definition Imp_sym :: form where
  "Imp_sym \<equiv> \<^bold>[\<^bold>\<lambda> ''x'':Tv. Imp_Aux3\<^bold>]"

lemma wff_Imp_sym[simp]:
  "wff (Fun (Fun Tv Tv) Tv) Imp_sym"
  unfolding Imp_sym_def by auto

lemma wff_Imp_sym'[simp]:
  "wff \<alpha> Imp_sym \<longleftrightarrow> \<alpha> = Fun (Fun Tv Tv) Tv"
  unfolding Imp_sym_def by auto

definition Imp :: "form \<Rightarrow> form \<Rightarrow> form" (infix "\<^bold>\<longrightarrow>" 80) where
  "A \<^bold>\<longrightarrow> B = (Imp_sym \<^bold>\<cdot> A) \<^bold>\<cdot> B"

lemma wff_Imp[simp]: "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff Tv (A \<^bold>\<longrightarrow> B)"
  unfolding Imp_def by auto

lemma wff_Imp'[simp]: "wff \<alpha> (A \<^bold>\<longrightarrow> B) \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<alpha> = Tv"
  using Imp_def by auto


section \<open>The Q0 proof system\<close>

definition axiom_1 :: form where
  "axiom_1 \<equiv> 
      \<^bold>[(((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> T) \<^bold>\<and> ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> F)) \<^bold>=Tv\<^bold>=
         \<^bold>[\<^bold>\<forall> ''x'':Tv. ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> (Var ''x'' Tv))\<^bold>]\<^bold>]"

lemma wff_axiom_1[simp]: "wff Tv axiom_1"
  unfolding axiom_1_def by auto

definition axiom_2 :: "type_sym \<Rightarrow> form" where
  "axiom_2 \<alpha> \<equiv>
       \<^bold>[(Var ''x'' \<alpha>) \<^bold>=\<alpha>\<^bold>= (Var ''y'' \<alpha>)\<^bold>]  \<^bold>\<longrightarrow>
       \<^bold>[((Var ''h'' (Fun Tv \<alpha>)) \<^bold>\<cdot> (Var ''x'' \<alpha>)) \<^bold>=Tv\<^bold>= ((Var ''h'' (Fun Tv \<alpha>)) \<^bold>\<cdot> (Var ''y'' \<alpha>))\<^bold>]"

definition axiom_3 :: "type_sym \<Rightarrow> type_sym \<Rightarrow> form" where
  "axiom_3 \<alpha> \<beta> \<equiv>
       \<^bold>[(Var ''f'' (Fun \<alpha> \<beta>)) \<^bold>=Fun \<alpha> \<beta>\<^bold>= (Var ''g'' (Fun \<alpha> \<beta>))\<^bold>] \<^bold>\<longrightarrow>
       \<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[((Var ''f'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) \<^bold>=\<alpha>\<^bold>= ((Var ''g'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))\<^bold>]\<^bold>]"

definition axiom_4_1 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_1 x \<alpha> B \<beta> A \<equiv> \<^bold>[(\<^bold>[\<^bold>\<lambda> x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= B\<^bold>]"

definition axiom_4_1_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> bool" where
  "axiom_4_1_side_condition x \<alpha> B \<beta> A \<equiv> \<exists>s. B = Cst s \<beta> \<or> (B = Var s \<beta> \<and> x \<noteq> s)"

definition axiom_4_1_variant_cst :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_1_variant_cst x \<alpha> c \<beta> A \<equiv> \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. Cst c \<beta>\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= (Cst c \<beta>)\<^bold>]"

definition axiom_4_1_variant_var :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_1_variant_var x \<alpha> y \<beta> A \<equiv>  \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var y \<beta>\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= Var y \<beta>\<^bold>]"

definition axiom_4_1_variant_var_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> bool" where
  "axiom_4_1_variant_var_side_condition x \<alpha> y \<beta> A \<equiv> x \<noteq> y"

definition axiom_4_2 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_2 x \<alpha> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. (Var x \<alpha>)\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<alpha>\<^bold>= A\<^bold>]"

definition axiom_4_3 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow>
                          type_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form  \<Rightarrow> form" where
  "axiom_4_3 x \<alpha> B \<beta> \<gamma> C A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. (B \<^bold>\<cdot> C)\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= ((\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))\<^bold>]"

definition axiom_4_4 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_4 x \<alpha> y \<gamma> B \<delta> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=Fun \<delta> \<gamma>\<^bold>= \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<^bold>]"

definition axiom_4_4_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> bool" where
  "axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A \<equiv> x \<noteq> y \<and> (y, \<gamma>) \<notin> frees A"

definition axiom_4_5 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> type_sym \<Rightarrow> form \<Rightarrow> form" where
  "axiom_4_5 x \<alpha> B \<delta> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=Fun \<delta> \<alpha> \<^bold>= \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]\<^bold>]"

abbreviation \<iota> where
  "\<iota> \<equiv> Cst ''i'' (Fun Ind (Fun Tv Ind))"

abbreviation QQ :: "type_sym \<Rightarrow> form" ("\<^bold>Q _" [80]) where
  "QQ \<alpha> \<equiv> Cst ''Q'' (Fun (Fun Tv \<alpha>) \<alpha>)"

definition axiom_5 where
  "axiom_5 = \<^bold>[(\<iota> \<^bold>\<cdot> ((\<^bold>Q Ind) \<^bold>\<cdot> Cst ''y'' Ind)) \<^bold>=Ind\<^bold>= Cst ''y'' Ind\<^bold>]"

(* rest of the axioms on page 213 *)

inductive axiom :: "form \<Rightarrow> bool" where
  by_axiom_1: "axiom axiom_1"
| by_axiom_2: "axiom (axiom_2 \<alpha>)"
| by_axiom_3: "axiom (axiom_3 \<alpha> \<beta>)"
| by_axiom_4_1: "wff \<alpha> A \<Longrightarrow> wff \<beta> B \<Longrightarrow> axiom_4_1_side_condition x \<alpha> B \<beta> A \<Longrightarrow> axiom (axiom_4_1 x \<alpha> B \<beta> A)"
| by_axiom_4_2: "wff \<alpha> A \<Longrightarrow> axiom (axiom_4_2 x \<alpha> A)"
| by_axiom_4_3: "wff \<alpha> A \<Longrightarrow> wff (Fun \<beta> \<gamma>) B \<Longrightarrow> wff \<gamma> C \<Longrightarrow> axiom (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)"
| by_axiom_4_4: "wff \<alpha> A \<Longrightarrow> wff \<delta> B \<Longrightarrow> axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A \<Longrightarrow> axiom (axiom_4_4 x \<alpha> y \<gamma> B \<delta> A)"
| by_axiom_4_5: "wff \<alpha> A \<Longrightarrow> wff \<delta> B \<Longrightarrow> axiom (axiom_4_5 x \<alpha> B \<delta> A)"
| by_axiom_5: "axiom (axiom_5)"

inductive rule_R :: "form \<Rightarrow> form \<Rightarrow> form \<Rightarrow> bool" where
  "replacement A B C D \<Longrightarrow> rule_R C (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) D"

definition "proof" :: "form \<Rightarrow> form list \<Rightarrow> bool" where
  "proof A p \<longleftrightarrow> (p \<noteq> [] \<and> last p = A \<and>
                    (\<forall>i<length p. axiom (p ! i) 
                  \<or> (\<exists>j<i. \<exists>k<i. rule_R (p ! j) (p ! k) (p ! i))))"

(* Peter Andrews defines theorems directly from "proof", here I instead define it as an inductive predicate based on rule_R *)
inductive "theorem" :: "form \<Rightarrow> bool" where
  by_axiom: "axiom A \<Longrightarrow> theorem A"
| by_rule_R: "theorem A \<Longrightarrow> theorem B \<Longrightarrow> rule_R A B C \<Longrightarrow> theorem C"


section \<open>Semantics\<close>

type_synonym 's frame = "type_sym \<Rightarrow> 's"

type_synonym 's denotation = "cst_sym \<Rightarrow> type_sym \<Rightarrow> 's"

type_synonym 's asg = "var_sym * type_sym \<Rightarrow> 's"

definition agree_off_asg :: "'s asg \<Rightarrow> 's asg \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> bool" where
  "agree_off_asg \<phi> \<psi> x \<alpha> \<longleftrightarrow> (\<forall>y \<beta>. (y\<noteq>x \<or> \<beta> \<noteq> \<alpha>) \<longrightarrow> \<phi> (y,\<beta>) = \<psi> (y,\<beta>))"

lemma agree_off_asg_def2:
  "agree_off_asg \<psi> \<phi> x \<alpha> \<longleftrightarrow> (\<exists>xa. \<phi>((x, \<alpha>) := xa) = \<psi>)"
  unfolding agree_off_asg_def by force

lemma agree_off_asg_disagree_var_sym[simp]: (* new_lemma *)
  "agree_off_asg \<psi> \<phi> x \<alpha> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<psi>(y,\<beta>) = \<phi>(y,\<beta>)"
  unfolding agree_off_asg_def by auto

lemma agree_off_asg_disagree_type_sym[simp]: (* new_lemma *)
  "agree_off_asg \<psi> \<phi> x \<alpha> \<Longrightarrow> \<alpha> \<noteq> \<beta> \<Longrightarrow> \<psi>(y,\<beta>) = \<phi>(y,\<beta>)"
  unfolding agree_off_asg_def by auto


context set_theory
begin

definition wf_frame :: "'s frame \<Rightarrow> bool" where
  "wf_frame D \<longleftrightarrow> D Tv = boolset \<and> (\<forall>\<alpha> \<beta>. D (Fun \<alpha> \<beta>) \<subseteq>: funspace (D \<beta>) (D \<alpha>)) \<and> (\<forall>\<alpha>. D \<alpha> \<noteq> Ø)"
  (* the model locale has defined a cst called "indset" \<comment> arguably, I should map "Ind" to that. But that's not what Peter Andrews does... *)

definition inds :: "'s frame \<Rightarrow> 's" where
  "inds Fr = Fr Ind"

inductive wf_interp :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "wf_frame D \<Longrightarrow>
   \<forall>c \<alpha>. I c \<alpha> \<in>: D \<alpha> \<Longrightarrow>
   \<forall>\<alpha>. I ''Q'' (Fun (Fun Tv \<alpha>) \<alpha>) = iden (D \<alpha>) \<Longrightarrow>
   (I ''i'' (Fun Ind (Fun Tv Ind))) \<in>: funspace (D (Fun Tv Ind)) (D Ind) \<Longrightarrow>
   \<forall>\<alpha> x. x \<in>: D \<alpha> \<longrightarrow> (I ''i'' (Fun Ind (Fun Tv Ind)))\<langle>one_elem_fun x (D \<alpha>)\<rangle> = x \<Longrightarrow>
   wf_interp D I"

definition asg_into_frame :: "'s asg \<Rightarrow> 's frame \<Rightarrow> bool" where
  "asg_into_frame \<phi> D \<longleftrightarrow> (\<forall>x \<alpha>. \<phi> (x, \<alpha>) \<in>: D \<alpha>)"

abbreviation(input) asg_into_interp :: "'s asg \<Rightarrow> 's frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "asg_into_interp \<phi> D I \<equiv> asg_into_frame \<phi> D"

(* Note that because Isabelle's HOL is total, val will also give values to non-wellformed formulas *)
fun val :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> 's asg \<Rightarrow> form \<Rightarrow> 's" where
  "val D I \<phi> (Var x \<alpha>) = \<phi> (x,\<alpha>)"
| "val D I \<phi> (Cst c \<alpha>) = I c \<alpha>"
| "val D I \<phi> (A \<^bold>\<cdot> B) = (val D I \<phi> A)\<langle>val D I \<phi> B\<rangle>"
| "val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] = (abstract (D \<alpha>) (D (type_of B)) (\<lambda>z. val D I (\<phi>((x,\<alpha>):=z)) B))"

fun general_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "general_model D I \<longleftrightarrow> wf_interp D I \<and> (\<forall>\<phi> A \<alpha>. asg_into_interp \<phi> D I \<longrightarrow> wff \<alpha> A \<longrightarrow> val D I \<phi> A \<in>: D \<alpha>)"

fun standard_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "standard_model D I \<longleftrightarrow> wf_interp D I \<and> (\<forall>\<alpha> \<beta>. D (Fun \<alpha> \<beta>) = funspace (D \<beta>) (D \<alpha>))"

lemma asg_into_frame_fun_upd: (* new_lemma *)
  assumes "asg_into_frame \<phi> D"
  assumes "xa \<in>: D \<alpha>"
  shows "asg_into_frame (\<phi>((x, \<alpha>) := xa)) D"
  using assms unfolding asg_into_frame_def by auto

lemma asg_into_interp_fun_upd: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  shows "asg_into_interp (\<phi>((x, \<alpha>) := val D I \<phi> A)) D I"
  using assms asg_into_frame_fun_upd by auto

lemma standard_model_is_general_model: (* new_lemma *) (* property mentioned on page 239 *)
  assumes "standard_model D I"
  shows "general_model D I" 
proof -
  have "wf_interp D I"
    using assms by auto
  moreover
  have "wff \<alpha> A \<Longrightarrow> asg_into_interp \<phi> D I \<Longrightarrow> val D I \<phi> A \<in>: D \<alpha>" for \<phi> \<alpha> A
  proof (induction arbitrary: \<phi> rule: wff.induct)
    case (wff_Var \<alpha> uu)
    then show ?case
      unfolding asg_into_frame_def using assms by auto
  next
    case (wff_Cst \<alpha> uv)
    then show ?case 
      using assms using wf_interp.simps by auto
  next
    case (wff_App \<alpha> \<beta> A B)
    then show ?case
      using apply_in_rng assms by fastforce
  next
    case (wff_Abs \<beta> A \<alpha> x)
    then show ?case 
      using assms abstract_in_funspace asg_into_frame_fun_upd by force
  qed
  ultimately
  have "general_model D I"
    unfolding general_model.simps by auto
  then show "general_model D I"
    by auto
qed

abbreviation agree_on_asg :: "'s asg \<Rightarrow> 's asg \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> bool" where
  "agree_on_asg \<phi> \<psi> x \<alpha> == (\<phi> (x, \<alpha>) = \<psi> (x, \<alpha>))"

(* Corresponds to Andrew's proposition 5400 *)
proposition prop_5400:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "asg_into_interp \<psi> D I"
  assumes "wff \<alpha> A"
  assumes "\<forall>(x,\<alpha>) \<in> frees A. agree_on_asg \<phi> \<psi> x \<alpha>"
  shows "val D I \<phi> A = val D I \<psi> A"
  using assms(4) assms(1-3,5)
proof (induction arbitrary: \<phi> \<psi> rule: wff.induct)
  case (wff_Var \<alpha> x)
  then show ?case by auto
next
  case (wff_Cst \<alpha> c)
  then show ?case by auto
next
  case (wff_App \<alpha> \<beta> A B)
  show ?case
    using wff_App(1,2,5,6,7,8) wff_App(3,4)[of \<phi> \<psi>] by auto
next
  case (wff_Abs \<beta> A \<alpha> x)
  have "abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<phi>((x, \<alpha>) := z)) A) = abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<psi>((x, \<alpha>) := z)) A)"
  proof (rule abstract_extensional, rule, rule)
    fix xa
    assume "xa \<in>: D \<alpha>"
    then have "val D I (\<phi>((x, \<alpha>) := xa)) A \<in>: D \<beta>"
      using wff_Abs asg_into_frame_fun_upd by auto
    moreover
    {
      have "asg_into_frame (\<psi>((x, \<alpha>) := xa)) D"
        using \<open>xa \<in>: D \<alpha>\<close> asg_into_frame_fun_upd wff_Abs by auto
      moreover
      have "asg_into_frame (\<phi>((x, \<alpha>) := xa)) D"
        using \<open>xa \<in>: D \<alpha>\<close> asg_into_frame_fun_upd wff_Abs by auto
      moreover
      have "(\<forall>y\<in>frees A. (\<phi>((x, \<alpha>) := xa)) y = (\<psi>((x, \<alpha>) := xa)) y)"
        using wff_Abs by auto
      ultimately
      have "val D I (\<phi>((x, \<alpha>) := xa)) A = val D I (\<psi>((x, \<alpha>) := xa)) A"
        using assms wff_Abs by (smt case_prodI2) 
    }  
    ultimately
    show "val D I (\<phi>((x, \<alpha>) := xa)) A \<in>: D \<beta> \<and> val D I (\<phi>((x, \<alpha>) := xa)) A = val D I (\<psi>((x, \<alpha>) := xa)) A"
      by auto
  qed
  then show ?case
    using wff_Abs by auto 
qed

(* definitions on page 239 *)
abbreviation satisfies :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> 's asg \<Rightarrow> form \<Rightarrow> bool" where
  "satisfies D I \<phi> A \<equiv> (val D I \<phi> A = true)"

definition valid_in_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> form \<Rightarrow> bool" where
  "valid_in_model D I A \<equiv> (\<forall>\<phi>. asg_into_interp \<phi> D I \<longrightarrow> val D I \<phi> A = true)"

definition valid_general :: "form \<Rightarrow> bool" where
  "valid_general A \<equiv> \<forall>D I. general_model D I \<longrightarrow> valid_in_model D I A"

definition valid_standard :: "form \<Rightarrow> bool" where
  "valid_standard A \<equiv> \<forall>D I. standard_model D I \<longrightarrow> valid_in_model D I A"


section \<open>Semantics of auxillary formulas\<close>

(* Corresponds to Andrew's lemma 5401 a *)
lemma lemma_5401_a:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<beta> B"
  shows "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) = val D I (\<phi>((x,\<alpha>):=val D I \<phi> A)) B"
proof -
  have val_A: "val D I \<phi> A \<in>: D \<alpha>"
    using assms  by simp
  have "asg_into_interp (\<phi>((x, \<alpha>) := val D I \<phi> A)) D I"
    using assms asg_into_frame_fun_upd  by force
  then have val_B: "val D I (\<phi>((x, \<alpha>) := val D I \<phi> A)) B \<in>: D \<beta>"
    using assms by simp

  have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) =
          (abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<phi>((x, \<alpha>) := z)) B))\<langle>val D I \<phi> A\<rangle>"
    using assms by auto
  also
  have "... = val D I (\<phi>((x, \<alpha>) := val D I \<phi> A)) B"
    using apply_abstract val_A val_B by auto
  finally
  show ?thesis 
    by auto
qed

(* Corresponds to Andrew's lemma 5401 b *)
lemma lemma_5401_b_variant_1: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = (boolean (val D I \<phi> A = val D I \<phi> B))"
proof -
  have "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = (I ''Q'' (Fun (Fun Tv \<alpha>) \<alpha>))\<langle>val D I \<phi> A\<rangle>\<langle>val D I \<phi> B\<rangle>"
    unfolding Eql_def by auto
  have "... = (iden (D \<alpha>))\<langle>val D I \<phi> A\<rangle>\<langle>val D I \<phi> B\<rangle>"
    using assms general_model.simps wf_interp.simps by auto 
  also
  have "... = boolean (val D I \<phi> A = val D I \<phi> B)"
    using apply_id using assms general_model.simps by blast
  finally show ?thesis 
    unfolding Eql_def by simp
qed

(* Corresponds to Andrew's lemma 5401 b *)
lemma lemma_5401_b:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = true \<longleftrightarrow> val D I \<phi> A = val D I \<phi> B"
  using lemma_5401_b_variant_1[OF assms] boolean_eq_true by auto

(* Corresponds to Andrew's lemma 5401 b *)
lemma lemma_5401_b_variant_2: \<comment> \<open>Just a reformulation of @{thm lemma_5401_b}'s directions\<close> (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  assumes "val D I \<phi> A = val D I \<phi> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = true"
  using assms(5) lemma_5401_b[OF assms(1,2,3,4)] by auto 

(* Corresponds to Andrew's lemma 5401 b *)
lemma lemma_5401_b_variant_3: \<comment> \<open>Just a reformulation of @{thm lemma_5401_b}'s directions\<close> (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  assumes "val D I \<phi> A \<noteq> val D I \<phi> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = false"
  using assms(5) lemma_5401_b_variant_1[OF assms(1,2,3,4)] by (simp add: boolean_def) 

(* Corresponds to Andrew's lemma 5401 c *)
lemma lemma_5401_c:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "val D I \<phi> T = true"
  using assms lemma_5401_b[OF assms(1,2)] unfolding T_def by auto

(* Corresponds to Andrew's lemma 5401 d *)
lemma lemma_5401_d:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "val D I \<phi> F = false"
proof -
  have "iden boolset \<in>: D (Fun (Fun Tv Tv) Tv)"
    using assms general_model.simps wf_interp.simps wf_frame_def by metis
  then have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>])\<langle>false\<rangle> \<noteq> (val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Var ''x'' Tv\<^bold>])\<langle>false\<rangle>" 
    using assms wf_interp.simps wf_frame_def true_neq_false 
      apply_id[of "iden boolset" "(D (Fun (Fun Tv Tv) Tv))" "iden boolset"]
    unfolding boolean_def Eql_def T_def by auto
  then have neqLR: "val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>] \<noteq> val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Var ''x'' Tv\<^bold>]"
    by metis
  have "val D I \<phi> F = boolean (val D I \<phi> (\<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>]) = val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Var ''x'' Tv\<^bold>])"
    using lemma_5401_b_variant_1[OF assms(1,2), 
        of "Fun Tv Tv" "(\<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>])" "\<^bold>[\<^bold>\<lambda>''x'':Tv. Var ''x'' Tv\<^bold>]"] assms
    by auto
  also
  have "... = boolean False"
    using neqLR by auto
  also
  have "... = false"
    unfolding boolean_def by auto
  finally
  show ?thesis
    by auto
qed

lemma asg_into_interp_fun_upd_true: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "asg_into_interp (\<phi>((x, Tv) := true)) D I"
  using asg_into_interp_fun_upd[OF assms wff_T, of x] lemma_5401_c[OF assms(1,2)] by auto

lemma asg_into_interp_fun_upd_false: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "asg_into_interp (\<phi>((x, Tv) := false)) D I"
  using asg_into_interp_fun_upd[OF assms wff_F, of x] lemma_5401_d[OF assms] by auto

lemma arg_cong3: "a = b \<Longrightarrow> c = d \<Longrightarrow> e = f \<Longrightarrow> h a c e = h b d f" (* new_lemma *)
  by auto

(* Corresponds to Andrew's lemma 5401 e_1 *)
lemma lemma_5401_e_1:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "(val D I \<phi> Con_sym)\<langle>true\<rangle>\<langle>true\<rangle> = true"
proof -               
  define \<phi>' where "\<phi>' \<equiv> \<phi>((''x'',Tv) := val D I \<phi> T)"
  define \<phi>'' where "\<phi>'' \<equiv> \<phi>'((''y'',Tv) :=  val D I \<phi>' T)"
  define \<phi>''' where "\<phi>''' \<equiv> \<lambda>z. \<phi>''((''g'', Fun (Fun Tv Tv) Tv) := z)"
  have \<phi>'_asg_into: "asg_into_interp \<phi>' D I"
    unfolding \<phi>'_def using asg_into_interp_fun_upd[OF assms wff_T] by blast
  have \<phi>''_asg_into: "asg_into_interp \<phi>'' D I"
    unfolding \<phi>''_def using asg_into_interp_fun_upd[OF assms(1) \<phi>'_asg_into wff_T] by blast

  have "(val D I \<phi> Con_sym)\<langle>true\<rangle>\<langle>true\<rangle> = val D I \<phi> ((Con_sym \<^bold>\<cdot> T) \<^bold>\<cdot> T)"
    using lemma_5401_c[OF assms(1,2)] by auto
  also
  have "... = val D I \<phi> ((\<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>]\<^bold>] \<^bold>\<cdot> T) \<^bold>\<cdot> T)"
    unfolding Con_sym_def Con_Aux2_def ..
  also
  have "... = (val D I \<phi> ((\<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>]\<^bold>] \<^bold>\<cdot> T)))\<langle>val D I \<phi> T\<rangle>"
    by simp
  also
  have "... = (val D I (\<phi>((''x'',Tv) := val D I \<phi> T)) ((\<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>])))\<langle>val D I \<phi> T\<rangle>"
    by (metis Con_Aux2_def lemma_5401_a[OF assms(1,2)] wff_Con_Aux2 wff_T)
  also
  have "... = (val D I \<phi>' ((\<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>])))\<langle>val D I \<phi> T\<rangle>"
    unfolding \<phi>'_def ..
  also
  have "... = (val D I \<phi>' ((\<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>])))\<langle>val D I \<phi>' T\<rangle>"
    using \<phi>'_asg_into assms(2) lemma_5401_c[OF assms(1)] by auto
  also
  have "... = (val D I \<phi>' (\<^bold>[\<^bold>\<lambda>''y'':Tv. Con_Aux1\<^bold>] \<^bold>\<cdot> T))"
    by simp
  also
  have "... = (val D I (\<phi>'((''y'',Tv) :=  val D I \<phi>' T)) (Con_Aux1))"
    by (meson \<phi>'_asg_into assms(1) lemma_5401_a[OF assms(1)] set_theory_axioms wff_Con_Aux1 wff_T)
  also
  have "... = (val D I \<phi>'' (Con_Aux1))"
    unfolding \<phi>''_def ..
  also
  have "... = val D I \<phi>'' \<^bold>[Con_Aux0 T T \<^bold>=Fun Tv (Fun (Fun Tv Tv) Tv)\<^bold>=
                           Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv)\<^bold>]"
    unfolding Con_Aux1_def ..
  also
  have "... = true"
  proof (rule lemma_5401_b_variant_2[OF assms(1)])
    show "wff (Fun Tv (Fun (Fun Tv Tv) Tv)) (Con_Aux0 T T)"
      by auto
  next
    show "wff (Fun Tv (Fun (Fun Tv Tv) Tv)) (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))"
      by auto
  next
    show "asg_into_frame \<phi>'' D"
      using \<phi>''_asg_into by blast
  next
    have "val D I \<phi>'' (Con_Aux0 T T) = 
          val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':Fun (Fun Tv Tv) Tv. (Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> T) \<^bold>\<cdot> T\<^bold>]"
      unfolding Con_Aux0_def ..
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv)
                  (\<lambda>z. val D I (\<phi>''((''g'', Fun (Fun Tv Tv) Tv) := z)) 
                     ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> T) \<^bold>\<cdot> T))"
      by (simp only: val.simps(4) type_of.simps type_sym.case)
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> T) \<^bold>\<cdot> T))"
      unfolding \<phi>'''_def ..
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>val D I (\<phi>''' z) T\<rangle>
                     \<langle>val D I (\<phi>''' z) T\<rangle>)"
      unfolding val.simps(3) ..
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>true\<rangle>\<langle>true\<rangle>)"
    proof (rule abstract_extensional')
      fix x
      assume "x \<in>: D (Fun (Fun Tv Tv) Tv)"
      then have "val D I (\<phi>''' x) ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> T) \<^bold>\<cdot> T) \<in>: D Tv"
        using Con_Aux0_def \<phi>'''_def \<phi>''_asg_into asg_into_frame_fun_upd assms(1) 
          general_model.elims(2) type_sym.inject wff_Abs_type_of wff_Con_Aux0 wff_T 
        by (metis wff_App wff_Var)
      then show "val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>val D I (\<phi>''' x) T\<rangle>
                   \<langle>val D I (\<phi>''' x) T\<rangle> 
                 \<in>: D Tv"
        by simp
    next
      fix x
      assume "x \<in>: D (Fun (Fun Tv Tv) Tv)"
      then have "val D I (\<phi>''' x) T = true"
        unfolding \<phi>'''_def using  \<phi>''_asg_into asg_into_frame_fun_upd 
          lemma_5401_c[OF assms(1)] by blast
      then show "val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>val D I (\<phi>''' x) T\<rangle>
                   \<langle>val D I (\<phi>''' x) T\<rangle> =
                 val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>true\<rangle>\<langle>true\<rangle>" by auto
    qed
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) (Var ''g'' (Fun (Fun Tv Tv) Tv))
                     \<langle>val D I (\<phi>''' z) (Var ''x'' Tv)\<rangle>\<langle>val D I (\<phi>''' z) (Var ''y'' Tv)\<rangle>)"
    proof (rule abstract_extensional')
      fix x
      assume x_in_D: "x \<in>: D (Fun (Fun Tv Tv) Tv)"
      then have "val D I (\<phi>''' x) ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> T) \<^bold>\<cdot> T) \<in>: D Tv"
        using Con_Aux0_def \<phi>'''_def \<phi>''_asg_into asg_into_frame_fun_upd assms(1) 
          general_model.elims(2) type_sym.inject wff_Abs_type_of wff_Con_Aux0 wff_T 
        by (metis wff_App wff_Var)
      then have "val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>val D I (\<phi>''' x) T\<rangle>
                   \<langle>val D I (\<phi>''' x) T\<rangle> \<in>: D Tv"
        by simp
      then show "val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>true\<rangle>\<langle>true\<rangle> \<in>: D Tv"
        by (metis \<phi>'''_def \<phi>''_asg_into lemma_5401_c[OF assms(1)] asg_into_frame_fun_upd x_in_D)
    next
      fix x
      assume x_in_D: "x \<in>: D (Fun (Fun Tv Tv) Tv)"
      then have "val D I (\<phi>''' x) (Var ''x'' Tv) = true"
        unfolding \<phi>'''_def \<phi>''_def \<phi>'_def using lemma_5401_c[OF assms(1,2)] by auto
      moreover
      from x_in_D have "val D I (\<phi>''' x) (Var ''y'' Tv) = true"
        unfolding \<phi>'''_def \<phi>''_def using \<phi>'_asg_into lemma_5401_c[OF assms(1)] by auto
      ultimately
      show "val D I (\<phi>''' x) (Var ''g'' (Fun (Fun Tv Tv) Tv))\<langle>true\<rangle>\<langle>true\<rangle> =
        val D I (\<phi>''' x)
          (Var ''g'' (Fun (Fun Tv Tv) Tv))
            \<langle>val D I (\<phi>''' x) (Var ''x'' Tv)\<rangle>\<langle>val D I (\<phi>''' x) (Var ''y'' Tv)\<rangle>" 
        by auto
    qed
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv) (\<lambda>z. val D I (\<phi>''' z) 
                  ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> (Var ''x'' Tv)) \<^bold>\<cdot> (Var ''y'' Tv)))"
      unfolding val.simps(3) ..
    also
    have "... = abstract (D (Fun (Fun Tv Tv) Tv)) (D Tv)
                  (\<lambda>z. val D I (\<phi>''((''g'', Fun (Fun Tv Tv) Tv) := z)) 
                         ((Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> (Var ''x'' Tv)) \<^bold>\<cdot> (Var ''y'' Tv)))"
      unfolding \<phi>'''_def ..
    also
    have "... = val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':Fun (Fun Tv Tv) Tv.
                                (Var ''g'' (Fun (Fun Tv Tv) Tv) \<^bold>\<cdot> (Var ''x'' Tv)) \<^bold>\<cdot> (Var ''y'' Tv)\<^bold>]"
      by (simp only: val.simps(4) type_of.simps type_sym.case)
    also
    have "... = val D I \<phi>'' (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))"
      unfolding Con_Aux0_def ..
    finally
    show "val D I \<phi>'' (Con_Aux0 T T) = val D I \<phi>'' (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))" 
      by auto
  qed
  finally show ?thesis .
qed

(* Corresponds to Andrew's lemma 5401 e_2 *)
lemma lemma_5401_e_2:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Con_sym)\<langle>false\<rangle>\<langle>y\<rangle> = false"
proof -
  (* x is gonna be the function of the type specified in z0 that returns its first argument.
     In order to prove z0 I need to express the function in the syntax of Q0 *)
  define give_x :: form where "give_x = \<^bold>[\<^bold>\<lambda>''y'':Tv. Var ''x'' Tv\<^bold>]"
  define give_fst :: form where "give_fst = \<^bold>[\<^bold>\<lambda> ''x'':Tv. give_x\<^bold>]"
  define val_give_fst :: 's where "val_give_fst = val D I \<phi> give_fst"
  have wff_give_x: "wff (Fun Tv Tv) give_x"
    unfolding give_x_def by auto

  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> 
               b \<in>: D Tv \<Longrightarrow> 
               val D I (\<phi>((''x'', Tv) := a)) give_x \<in>: D (type_of give_x)"
    using wff_give_x asg_into_frame_def assms(1,2) by auto
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_x\<langle>b\<rangle> = a"
    unfolding give_x_def by auto
  ultimately
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow>
               b \<in>: D Tv \<Longrightarrow> 
               abstract (D Tv) (D (type_of give_x)) (\<lambda>z. val D I (\<phi>((''x'', Tv) := z)) give_x)\<langle>a\<rangle>\<langle>b\<rangle>
               = a"
    by auto
  then have val_give_fst_simp: "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val_give_fst\<langle>a\<rangle>\<langle>b\<rangle> = a"
    unfolding val_give_fst_def give_fst_def by auto

  have wff_give_fst: "wff (Fun (Fun Tv Tv) Tv) give_fst"
    unfolding give_fst_def give_x_def by auto
  then have val_give_fst_fun: "val_give_fst \<in>: D (Fun (Fun Tv Tv) Tv)"
    unfolding val_give_fst_def using assms by auto

  have "val D I (\<phi>((''x'', Tv) := false, 
                   (''y'', Tv) := y, 
                   (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T \<in>: D Tv"
    by (smt Pair_inject wff_give_fst assms(1,2,3) fun_upd_twist general_model.simps
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_true[OF assms(1)] 
        asg_into_interp_fun_upd_false[OF assms(1)] type_sym.distinct(5) val_give_fst_def wff_T)
  then have val_give_fst_D:
      "val_give_fst\<langle>val D I (\<phi>((''x'', Tv) := false, 
                               (''y'', Tv) := y, 
                               (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T\<rangle>
                   \<langle>val D I (\<phi>((''x'', Tv) := false, 
                               (''y'', Tv) := y, 
                               (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T\<rangle>
       \<in>: D Tv"
    using val_give_fst_simp[of
        "val D I (\<phi>((''x'', Tv) := false, 
                    (''y'', Tv) := y, 
                    (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T" 
        "val D I (\<phi>((''x'', Tv) := false, 
                     (''y'', Tv) := y, 
                     (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T" ]
    by auto

  have false_y_TV: "false \<in>: D Tv \<and> y \<in>: D Tv"
    using assms(1) assms(3) wf_frame_def wf_interp.simps by auto
  then have val_give_fst_in_D: "val_give_fst\<langle>false\<rangle>\<langle>y\<rangle> \<in>: D Tv"
    using val_give_fst_simp by auto

  have "true \<in>: D Tv"
    by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
  from this val_give_fst_in_D false_y_TV have "val_give_fst\<langle>true\<rangle>\<langle>true\<rangle> \<noteq> val_give_fst\<langle>false\<rangle>\<langle>y\<rangle>"
    using val_give_fst_simp true_neq_false by auto
  then have val_give_fst_not_false: 
    "val_give_fst\<langle>val D I (\<phi>((''x'', Tv) := false, 
                             (''y'', Tv) := y, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T\<rangle>
                 \<langle>val D I (\<phi>((''x'', Tv) := false, 
                             (''y'', Tv) := y, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_fst)) T\<rangle> 
     \<noteq> val_give_fst\<langle>false\<rangle>\<langle>y\<rangle>"
    using asg_into_frame_fun_upd assms(1) assms(2) lemma_5401_c false_y_TV val_give_fst_fun by auto
  have Con_Aux0TT_neq_Con_Aux0xy: 
    "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) (Con_Aux0 T T) \<noteq> 
     val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))"
    unfolding Con_Aux0_def using abstract_cong_specific[of
        val_give_fst
        "(D (Fun (Fun Tv Tv) Tv))" 
        "(\<lambda>z. z\<langle>val D I (\<phi>((''x'', Tv) := false, 
                           (''y'', Tv) := y, 
                           (''g'', Fun (Fun Tv Tv) Tv) := z)) T\<rangle>
                \<langle>val D I (\<phi>((''x'', Tv) := false, 
                            (''y'', Tv) := y, 
                            (''g'', Fun (Fun Tv Tv) Tv) := z)) T\<rangle>)" 
        "(D Tv)"
        "(\<lambda>z. z\<langle>false\<rangle>\<langle>y\<rangle>)"]
    using val_give_fst_fun val_give_fst_D val_give_fst_in_D val_give_fst_not_false by auto

  have "asg_into_frame (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) D"
    using asg_into_interp_fun_upd_false[OF assms(1)] general_model.simps[of D I] assms wff_Con_Aux1
     asg_into_interp_fun_upd_true[OF assms(1)] by auto
  then have val_Con_Aux1: "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) Con_Aux1 = false"
    unfolding Con_Aux1_def using Con_Aux0TT_neq_Con_Aux0xy lemma_5401_b_variant_3[OF assms(1)] 
    by auto

  have "y \<in>: D Tv"
    using general_model.simps lemma_5401_d[OF assms(1,2)] wff_F assms
    by (metis lemma_5401_c[OF assms(1,2)] wff_T) 
  moreover
  have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) Con_Aux1 \<in>: D Tv"
    using asg_into_interp_fun_upd_false[OF assms(1)] general_model.simps[of D I] assms wff_Con_Aux1 
      asg_into_interp_fun_upd_true[OF assms(1)] by auto
  moreover
  have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) Con_Aux1 = false"
    using val_Con_Aux1 by auto
  ultimately
  have val_y: "(val D I (\<phi>((''x'', Tv) := false)) Con_Aux2)\<langle>y\<rangle> = false"
    unfolding Con_Aux2_def by simp

  have 11: "val D I (\<phi>((''x'', Tv) := false)) Con_Aux2 \<in>: D (Fun Tv Tv)"
    using asg_into_interp_fun_upd_false[OF assms(1,2)] general_model.simps[of D I] assms
      wff_Con_Aux2 by blast 
  moreover
  have "val D I (\<phi>((''x'', Tv) := false)) Con_Aux2\<langle>y\<rangle> = false"
    using val_y by auto
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Con_Aux2\<^bold>])\<langle>false\<rangle>\<langle>y\<rangle> = false"
    using false_y_TV by simp
  then show "(val D I \<phi> Con_sym)\<langle>false\<rangle>\<langle>y\<rangle> = false"
    unfolding Con_sym_def by auto
qed

(* Corresponds to Andrew's lemma 5401 e_3 *)
lemma lemma_5401_e_3:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Con_sym)\<langle>x\<rangle>\<langle>false\<rangle> = false"
proof -
  (* proof adapted from lemma_5401_e_2 *)
  define give_y :: form where "give_y = (\<^bold>[\<^bold>\<lambda> ''y'':Tv. (Var ''y'' Tv)\<^bold>])"
  define give_snd :: form where "give_snd = \<^bold>[\<^bold>\<lambda> ''x'':Tv. give_y\<^bold>]"
  define val_give_snd :: 's where "val_give_snd = val D I \<phi> give_snd"
  have wff_give_y: "wff (Fun Tv Tv) give_y"
    unfolding give_y_def by auto

  have  "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> a \<in>: D Tv"
    by simp
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_y \<in>: D (type_of give_y)"
    using wff_give_y asg_into_frame_def assms(1) assms(2) by auto
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_y\<langle>b\<rangle> = b"
    unfolding give_y_def by auto
  ultimately
  have val_give_snd_simp: "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val_give_snd\<langle>a\<rangle>\<langle>b\<rangle> = b"
    unfolding val_give_snd_def give_snd_def by auto

  have wff_give_snd: "wff (Fun (Fun Tv Tv) Tv) give_snd"
    unfolding give_snd_def give_y_def by auto
  then have val_give_snd_in_D: "val_give_snd \<in>: D (Fun (Fun Tv Tv) Tv)"
    unfolding val_give_snd_def using assms
    by auto

  then have "val D I (\<phi>((''x'', Tv) := x, 
                   (''y'', Tv) := false, 
                   (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T \<in>: D Tv"
    by (smt Pair_inject wff_give_snd assms(1,2,3) 
        fun_upd_twist general_model.simps asg_into_interp_fun_upd[OF assms(1,2)] 
        asg_into_interp_fun_upd_false[OF assms(1)] asg_into_interp_fun_upd_true[OF assms(1)] 
        type_sym.distinct(5) val_give_snd_def wff_T)
  then have val_give_snd_app_in_D: 
    "val_give_snd\<langle>val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T\<rangle>
                 \<langle>val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T\<rangle>
     \<in>: D Tv"
    using val_give_snd_simp[of
        "val D I (\<phi>((''x'', Tv) := x, 
                    (''y'', Tv) := false, 
                    (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T" 
        "val D I (\<phi>((''x'', Tv) := x, 
                     (''y'', Tv) := false, 
                     (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T" ]
    by auto

  have false_and_x_in_D: "false \<in>: D Tv \<and> x \<in>: D Tv"
    using assms(1,3) wf_frame_def wf_interp.simps by auto
  then have val_give_snd_app_x_false_in_D: "val_give_snd\<langle>x\<rangle>\<langle>false\<rangle> \<in>: D Tv"
    using val_give_snd_simp by auto

  have "true \<in>: D Tv"
    by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
  then have "val_give_snd\<langle>true\<rangle>\<langle>true\<rangle> \<noteq> val_give_snd\<langle>x\<rangle>\<langle>false\<rangle>"
    using val_give_snd_simp true_neq_false val_give_snd_app_in_D false_and_x_in_D by auto
  then have
    "val_give_snd\<langle>val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T\<rangle>
                 \<langle>val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', Fun (Fun Tv Tv) Tv) := val_give_snd)) T\<rangle> \<noteq>
     val_give_snd\<langle>x\<rangle>\<langle>false\<rangle>"
    using asg_into_frame_fun_upd assms(1) assms(2) lemma_5401_c false_and_x_in_D val_give_snd_in_D
    by auto
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) (Con_Aux0 T T) \<noteq> 
        val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) 
          (Con_Aux0 (Var ''x'' Tv) (Var ''y'' Tv))"
    unfolding Con_Aux0_def
    using abstract_cong_specific[of 
        val_give_snd 
        "(D (Fun (Fun Tv Tv) Tv))" 
        "(\<lambda>z. z\<langle>val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false, (''g'', Fun (Fun Tv Tv) Tv) := z))
             T\<rangle>\<langle>val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false, (''g'', Fun (Fun Tv Tv) Tv) := z)) T\<rangle>)" 
        "(D Tv)"
        "(\<lambda>z. z\<langle>x\<rangle>\<langle>false\<rangle>)"
        ]
    using val_give_snd_in_D val_give_snd_app_x_false_in_D val_give_snd_app_in_D by auto
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) Con_Aux1 = false"
    using asg_into_frame_fun_upd assms(1,2) lemma_5401_b_variant_3 false_and_x_in_D
    unfolding Con_Aux1_def by auto
  then have val_Con_Aux2_false: "(val D I (\<phi>((''x'', Tv) := x)) Con_Aux2)\<langle>false\<rangle> = false"
    unfolding Con_Aux2_def using false_and_x_in_D by simp

  have "x \<in>: D Tv"
    by (simp add: false_and_x_in_D)
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) Con_Aux2 \<in>: D (Fun Tv Tv)"
    by (metis assms(1,3) general_model.simps lemma_5401_c[OF assms(1,2)] 
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_false[OF assms(1,2)] 
        wff_Con_Aux2 wff_T)
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) Con_Aux2\<langle>false\<rangle> = false"
    using val_Con_Aux2_false by auto
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Con_Aux2\<^bold>])\<langle>x\<rangle>\<langle>false\<rangle> = false"
    by auto
  then show "(val D I \<phi> Con_sym)\<langle>x\<rangle>\<langle>false\<rangle> = false"
    unfolding Con_sym_def by auto
qed

(* Corresponds to Andrew's lemma 5401 e *)
lemma lemma_5401_e_variant_1: (* new_lemma *)
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "y = true \<or> y = false"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Con_sym)\<langle>x\<rangle>\<langle>y\<rangle> = boolean (x = true \<and> y = true)"
proof (cases "y = true")
  case True
  note True_outer = this
  then show ?thesis
  proof (cases "x = true")
    case True
    then show ?thesis
      using True_outer assms lemma_5401_e_1 unfolding boolean_def by auto
  next
    case False
    then show ?thesis
      using True_outer assms  lemma_5401_e_2 unfolding boolean_def by auto
  qed
next
  case False
  note False_outer = this
  then show ?thesis 
  proof (cases "x = true")
    case True
    then show ?thesis
      using False_outer assms lemma_5401_e_3 unfolding boolean_def by auto
  next
    case False
    then show ?thesis
      using False_outer assms lemma_5401_e_2 unfolding boolean_def by auto
  qed
qed

lemma asg_into_interp_is_true_or_false: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "\<phi> (x, Tv) = true \<or> \<phi> (x, Tv) = false"
proof -
  have "wff Tv (Var x Tv)"
    by auto
  then have "val D I \<phi> (Var x Tv) \<in>: D Tv"
    using assms general_model.simps by blast
  then have "val D I \<phi> (Var x Tv) \<in>: boolset"
    using assms unfolding general_model.simps wf_interp.simps wf_frame_def by auto
  then show ?thesis
    using mem_boolset by simp 
qed

lemma wff_Tv_is_true_or_false: (* new_lemma *)
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  shows "val D I \<phi> A = true \<or> val D I \<phi> A = false"
proof -
  have "val D I \<phi> A \<in>: D Tv"
    using assms by auto
  then have "val D I \<phi> A \<in>: boolset"
    using assms unfolding general_model.simps wf_interp.simps wf_frame_def by force
  then show ?thesis
    using mem_boolset by blast
qed

(* Corresponds to Andrew's lemma 5401 2 *)
lemma lemma_5401_e_variant_2: (* new_lemma *)
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  assumes "wff Tv B"
  shows "(val D I \<phi> (A \<^bold>\<and> B)) = boolean (satisfies D I \<phi> A \<and> satisfies D I \<phi> B)"
  using assms wff_Tv_is_true_or_false[of \<phi> D I] lemma_5401_e_variant_1 unfolding Con_def by auto

(* Corresponds to Andrew's lemma 5401 f_1 *)
lemma lemma_5401_f_1:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Imp_sym)\<langle>false\<rangle>\<langle>y\<rangle> = true"
proof -
  have val_Imp_Aux1_false: "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) Imp_Aux1 = false"
    using assms asg_into_interp_fun_upd_false[OF assms(1)] asg_into_interp_fun_upd_true[OF assms(1)] 
      boolean_def lemma_5401_e_variant_1 unfolding Imp_Aux1_def Imp_Aux0_def by auto 

  have "asg_into_frame (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) D"
    using assms(1, 2, 3) lemma_5401_c[OF assms(1)] asg_into_interp_fun_upd set_theory_axioms wff_T
      asg_into_interp_fun_upd_false by metis
  then have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) Imp_Aux2 = true"
    using lemma_5401_b_variant_1[OF assms(1)] val_Imp_Aux1_false unfolding boolean_def Imp_Aux2_def 
    by auto
  then have val_Imp_Aux3_true: "(val D I (\<phi>((''x'', Tv) := false)) Imp_Aux3)\<langle>y\<rangle> = true"
    unfolding Imp_Aux3_def using assms(1,3) wf_frame_def wf_interp.simps by auto 

  have "val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':Tv. Imp_Aux3\<^bold>]\<langle>false\<rangle>\<langle>y\<rangle> = true"
  proof -
    have "false \<in>: D Tv"
      by (metis asg_into_frame_def asg_into_interp_fun_upd_false assms(1) assms(2) fun_upd_same)
    then have "val D I (\<phi>((''x'', Tv) := false)) Imp_Aux3 = val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Imp_Aux3\<^bold>]\<langle>false\<rangle>"
      using asg_into_interp_fun_upd_false assms(1,2) by force
    then show ?thesis
      by (metis val_Imp_Aux3_true)
  qed
  then show "(val D I \<phi> Imp_sym)\<langle>false\<rangle>\<langle>y\<rangle> = true"
    unfolding Imp_sym_def by auto
qed

(* Corresponds to Andrew's lemma 5401 f_2 *)
lemma lemma_5401_f_2:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Imp_sym)\<langle>x\<rangle>\<langle>true\<rangle> = true"
proof -
  have asg: "asg_into_frame (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) D"
    using assms(1) assms(2) assms(3) asg_into_interp_fun_upd_false asg_into_interp_fun_upd_true[OF assms(1)] by blast
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) Imp_Aux1 = x"
    using lemma_5401_e_variant_1 assms unfolding boolean_def Imp_Aux1_def Imp_Aux0_def by auto
  then have val_Imp_Aux2_true: "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) Imp_Aux2 = true"
    using asg lemma_5401_b_variant_1[OF assms(1)] boolean_eq_true unfolding Imp_Aux2_def by auto 

  have val_Imp_Aux3_true: "val D I (\<phi>((''x'', Tv) := x)) Imp_Aux3\<langle>true\<rangle> = true"
    unfolding Imp_Aux3_def using val_Imp_Aux2_true assms(1) wf_frame_def wf_interp.simps by auto 

  have "x \<in>: D Tv"
    by (metis asg_into_frame_def assms(1) assms(3) fun_upd_same asg_into_interp_fun_upd_false 
        asg_into_interp_fun_upd_true[OF assms(1,2)])
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) Imp_Aux3 \<in>: D (Fun Tv Tv)"
    using wff_Imp_Aux3
    by (metis assms(1,2,3) general_model.simps lemma_5401_c[OF assms(1,2)]
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_false wff_T)
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. Imp_Aux3\<^bold>])\<langle>x\<rangle>\<langle>true\<rangle> = true"
    using val_Imp_Aux3_true by auto
  then show "(val D I \<phi> Imp_sym)\<langle>x\<rangle>\<langle>true\<rangle> = true"
    unfolding Imp_sym_def by auto
qed

(* Corresponds to Andrew's lemma 5401 f_3 *)
lemma lemma_5401_f_3:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "(val D I \<phi> Imp_sym)\<langle>true\<rangle>\<langle>false\<rangle> = false"
proof -
  have asg: "asg_into_frame (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) D"
    by (meson assms(1) assms(2) asg_into_interp_fun_upd_false set_theory_axioms asg_into_interp_fun_upd_true[OF assms(1,2)])
  moreover
  have "false = true \<or> false = false"
    unfolding boolean_def by auto
  moreover
  have "boolean (true = true \<and> false = true) = false"
    unfolding boolean_def by auto
  ultimately
  have 3: "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) Imp_Aux1 = false"
    unfolding Imp_Aux1_def Imp_Aux0_def using lemma_5401_e_variant_1 assms by auto
  then have Imp_Aux2_false: "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) Imp_Aux2 = false"
    unfolding Imp_Aux2_def using subst lemma_5401_b_variant_1[OF assms(1)] asg boolean_def by auto

  have asdff: "wff Tv Imp_Aux2"
    by auto

  have false_Tv: "false \<in>: D Tv"
    using assms(1) wf_frame_def wf_interp.simps by auto
  moreover
  have "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) Imp_Aux2 \<in>: D Tv"
    by (simp add: Imp_Aux2_false false_Tv)
  moreover
  have "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) Imp_Aux2 = false"
    using Imp_Aux2_false by auto
  ultimately 
  have Imp_Aux3_app_false: "val D I (\<phi>((''x'', Tv) := true)) Imp_Aux3\<langle>false\<rangle> = false"
    unfolding Imp_Aux3_def
    by auto

  have wff_Imp_Aux3: "wff (Fun Tv Tv) Imp_Aux3"
    by auto

  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':Tv. Imp_Aux3\<^bold>])\<langle>true\<rangle>\<langle>false\<rangle> = false"
  proof -
    have "true \<in>: D Tv"
      by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
    moreover
    have "val D I (\<phi>((''x'', Tv) := true)) Imp_Aux3 \<in>: D (Fun Tv Tv)"
      using wff_Imp_Aux3 
      by (metis assms(1) general_model.simps asg_into_interp_fun_upd_true[OF assms(1,2)])
    moreover
    have "val D I (\<phi>((''x'', Tv) := true)) Imp_Aux3\<langle>false\<rangle> = false"
      using Imp_Aux3_app_false by auto
    ultimately
    show ?thesis
      by auto
  qed
  then show "(val D I \<phi> Imp_sym)\<langle>true\<rangle>\<langle>false\<rangle> = false"
    unfolding Imp_sym_def by auto
qed

(* Corresponds to Andrew's lemma 5401 f *)
lemma lemma_5401_f_variant_1: (* new_lemma *)
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "x = true \<or> x = false"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Imp_sym)\<langle>x\<rangle>\<langle>y\<rangle> = boolean (x = true \<longrightarrow> y = true)"
proof (cases "y = true")
  case True
  note True_outer = this
  then show ?thesis
  proof (cases "x = true")
    case True
    then show ?thesis
      using True_outer assms lemma_5401_f_2 unfolding boolean_def by auto
  next
    case False
    then show ?thesis
      using True_outer assms  lemma_5401_f_2 unfolding boolean_def by auto
  qed
next
  case False
  note False_outer = this
  then show ?thesis 
  proof (cases "x = true")
    case True
    then show ?thesis
      using False_outer assms lemma_5401_f_3 unfolding boolean_def by auto
  next
    case False
    then show ?thesis
      using False_outer assms lemma_5401_f_1 unfolding boolean_def by auto
  qed
qed

(* Corresponds to Andrew's lemma 5401 f *)
lemma lemma_5401_f_variant_2: (* new_lemma *)
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  assumes "wff Tv B"
  shows "(val D I \<phi> (A \<^bold>\<longrightarrow> B)) = boolean (satisfies D I \<phi> A \<longrightarrow> satisfies D I \<phi> B)"
  using assms unfolding Imp_def
  by (simp add: lemma_5401_f_variant_1 wff_Tv_is_true_or_false)

(* Corresponds to Andrew's lemma 5401 g *)
lemma lemma_5401_g:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff Tv A"
  shows "satisfies D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] \<longleftrightarrow> (\<forall>\<psi>. asg_into_interp \<psi> D I \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A)"
proof -
  have "wff (Fun Tv \<alpha>) (PI_Aux \<alpha>)"
    by auto
  then have PI_Aux_in_D: "val D I \<phi> (PI_Aux \<alpha>) \<in>: D (Fun Tv \<alpha>)"
    using assms(1,2) by auto

  have "wff (Fun Tv \<alpha>) (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>])"
    using assms by auto
  moreover
  have "\<forall>\<phi>. asg_into_frame \<phi> D \<longrightarrow> (\<forall>A \<alpha>. wff \<alpha> A \<longrightarrow> val D I \<phi> A \<in>: D \<alpha>)"
    using assms(1) by auto
  then have "\<forall>t cs. val D I \<phi> \<^bold>[\<^bold>\<lambda>cs:t. A\<^bold>] \<in>: D (Fun Tv t)"
    using wff_Abs assms(1,2,3) by presburger
  then have "abstract (D \<alpha>) (D Tv) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) A) \<in>: D (Fun Tv \<alpha>)"
    using assms(3) by simp
  ultimately
  have val_lambda_A: "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) \<in>: D (Fun Tv \<alpha>)"
    using assms by auto

  have true_and_A_in_D: "\<forall>z. z \<in>: D \<alpha> \<longrightarrow> true \<in>: D Tv \<and> val D I (\<phi>((x, \<alpha>) := z)) A \<in>: D Tv"
    by (metis assms(1,2,3) general_model.simps lemma_5401_c[OF assms(1,2)] asg_into_frame_fun_upd wff_T)

  have "satisfies D I \<phi> \<^bold>[\<^bold>\<forall> x: \<alpha>. A\<^bold>] \<longleftrightarrow> val D I \<phi> \<^bold>[\<^bold>\<forall>x: \<alpha>. A\<^bold>] = true"
    by auto
  moreover have "... \<longleftrightarrow> val D I \<phi> (PI \<alpha>)\<langle>val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]\<rangle> = true"
    unfolding Forall_def by simp
  moreover have "... \<longleftrightarrow> I ''Q'' (Fun (Fun Tv (Fun Tv \<alpha>)) (Fun Tv \<alpha>))
                           \<langle>val D I \<phi> (PI_Aux \<alpha>)\<rangle>\<langle>val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]\<rangle> =
                         true"
    unfolding PI_def by simp
  moreover have "... \<longleftrightarrow> (iden (D (Fun Tv \<alpha>)))\<langle>val D I \<phi> (PI_Aux \<alpha>)\<rangle>\<langle>val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]\<rangle> =
                         true"
    unfolding PI_def using wf_interp.simps assms by simp
  moreover have "... \<longleftrightarrow> val D I \<phi> (PI_Aux \<alpha>) = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
    using PI_Aux_in_D val_lambda_A apply_id_true by auto
  moreover have "... \<longleftrightarrow> val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':\<alpha>. T\<^bold>] = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
    unfolding PI_Aux_def by auto
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. val D I (\<phi>((''x'', \<alpha>) := z)) T) = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
    using assms wff_T by simp
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. true) = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  proof -
    have "\<forall>x. x \<in>: D \<alpha> \<longrightarrow> val D I (\<phi>((''x'', \<alpha>) := x)) T \<in>: D Tv \<and> true \<in>: D Tv"
      using true_and_A_in_D assms(1,2)  asg_into_frame_fun_upd by auto
    moreover
    have "\<forall>x. x \<in>: D \<alpha> \<longrightarrow> val D I (\<phi>((''x'', \<alpha>) := x)) T \<in>: D Tv \<and> satisfies D I (\<phi>((''x'', \<alpha>) := x)) T"
      using set_theory_axioms true_and_A_in_D assms(1) assms(2) lemma_5401_c[OF assms(1)] 
        asg_into_frame_fun_upd by auto
    ultimately
    have "abstract (D \<alpha>) (D Tv) (\<lambda>z. val D I (\<phi>((''x'', \<alpha>) := z)) T) = abstract (D \<alpha>) (D Tv) (\<lambda>z. true)"
      using abstract_extensional by auto
    then show ?thesis
      by auto
  qed
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. true) = val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>])"
    by auto
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. true) = 
                         abstract (D \<alpha>) (D Tv) (\<lambda>z. val D I (\<phi>((x, \<alpha>) := z)) A)"
    using assms by simp
  moreover have "... \<longleftrightarrow> (\<forall>z. z \<in>: D \<alpha> \<longrightarrow> true \<in>: D Tv \<and> true = val D I (\<phi>((x, \<alpha>) := z)) A)"
  proof -
    have "\<forall>z. z \<in>: D \<alpha> \<longrightarrow> true \<in>: D Tv \<and> val D I (\<phi>((x, \<alpha>) := z)) A \<in>: D Tv"
      using true_and_A_in_D by auto
    then show ?thesis
      using abstract_cong_extensional by auto
  qed
  moreover have "... \<longleftrightarrow> (\<forall>z. z \<in>: D \<alpha> \<longrightarrow> true = val D I (\<phi>((x, \<alpha>) := z)) A)"
    by (metis assms(1,2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
  moreover have "... \<longleftrightarrow> (\<forall>z. z \<in>: D \<alpha> \<longrightarrow> satisfies D I (\<phi>((x, \<alpha>) := z)) A)"
    by auto
  moreover have "... \<longleftrightarrow> (\<forall>\<psi>. asg_into_interp \<psi> D I \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A)"
  proof -
    show ?thesis
    proof
      assume A_sat: "\<forall>z. z \<in>: D \<alpha> \<longrightarrow> satisfies D I (\<phi>((x, \<alpha>) := z)) A"
      show "\<forall>\<psi>. asg_into_frame \<psi> D \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A"
      proof (rule; rule; rule)
        fix \<psi>
        assume a1: "asg_into_frame \<psi> D"
        assume a2: "agree_off_asg \<psi> \<phi> x \<alpha>"
        have "\<exists>xa. (\<phi>((x, \<alpha>) := xa)) = \<psi>"
          using a1 a2 agree_off_asg_def2 by blast
        then show "satisfies D I \<psi> A"
          using A_sat a1 a2 by (metis asg_into_frame_def fun_upd_same)
      qed
    next
      assume "\<forall>\<psi>. asg_into_frame \<psi> D \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A"
      then show "\<forall>z. z \<in>: D \<alpha> \<longrightarrow> satisfies D I (\<phi>((x, \<alpha>) := z)) A"
        using asg_into_frame_fun_upd asg_into_interp_fun_upd[OF assms(1,2)] assms(2) fun_upd_other 
        unfolding agree_off_asg_def by auto
    qed
  qed
  ultimately show ?thesis
    by auto
qed

(* Corresponds to Andrew's lemma 5401 g *)
theorem lemma_5401_g_variant_1:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  shows "val D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] = boolean (\<forall>\<psi>. asg_into_interp \<psi> D I \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A)"
proof -
  have "val D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] = (if satisfies D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] then true else false)"
    using assms wff_Forall wff_Tv_is_true_or_false by metis
  then show ?thesis
    using assms lemma_5401_g[symmetric] unfolding boolean_def by auto
qed


section \<open>Soundness\<close>

lemma fun_sym_asg_to_funspace: (* new_lemma *)
  assumes "asg_into_frame \<phi> D"
  assumes "general_model D I"
  shows "\<phi> (f, Fun \<alpha> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
proof -
  have "wff (Fun \<alpha> \<beta>) (Var f (Fun \<alpha> \<beta>))"
    by auto
  then have "val D I \<phi> (Var f (Fun \<alpha> \<beta>)) \<in>: D (Fun \<alpha> \<beta>)"
    using assms
    using general_model.simps by blast
  then show "\<phi> (f, Fun \<alpha> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
    using assms unfolding general_model.simps wf_interp.simps wf_frame_def
    by (simp add: set_theory_axioms subs_def)
qed

lemma fun_sym_interp_to_funspace: (* new_lemma *)
  assumes "asg_into_frame \<phi> D"
  assumes "general_model D I"
  shows "I f (Fun \<alpha> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
proof -
  have "wff (Fun \<alpha> \<beta>) (Cst f (Fun \<alpha> \<beta>))"
    by auto
  then have "val D I \<phi> (Cst f (Fun \<alpha> \<beta>)) \<in>: D (Fun \<alpha> \<beta>)"
    using assms general_model.simps by blast
  then show "I f (Fun \<alpha> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
    using assms set_theory_axioms subs_def unfolding general_model.simps wf_interp.simps 
      wf_frame_def by auto
qed

(* Corresponds to Andrew's theorem 5402 a for rule R *)
theorem theorem_5402_a_rule_R:
  assumes A_eql_B: "valid_general (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>])"
  assumes "valid_general C"
  assumes "rule_R C (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) C'"
  assumes "wff \<alpha> A"
  assumes "wff \<alpha> B"
  assumes "wff \<beta> C"
  shows "valid_general C'"
  unfolding valid_general_def proof (rule, rule, rule)
  (* based on the book *)
  fix D :: "type_sym \<Rightarrow> 's" and I :: "char list \<Rightarrow> type_sym \<Rightarrow> 's"
  assume DI: "general_model D I"
  then have "valid_in_model D I (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>])"
    using A_eql_B unfolding valid_general_def by auto
  then have x: "\<forall>\<phi>. asg_into_frame \<phi> D \<longrightarrow> (val D I \<phi> A = val D I \<phi> B)"
    unfolding valid_in_model_def using lemma_5401_b[OF DI, of _ \<alpha> A B ] assms(4,5) by auto
  have r: "replacement A B C C'"
    using assms(3) using Eql_def rule_R.cases by fastforce 
  from r have "\<forall>\<phi>. asg_into_frame \<phi> D \<longrightarrow> (val D I \<phi> C = val D I \<phi> C')"
    using x assms(4,5,6) 
  proof (induction arbitrary: \<beta> rule: replacement.induct)
    case (replace A B)
    then show ?case by auto
  next
    case (replace_App_left A B C E D')
    define \<alpha>' where "\<alpha>' = type_of C" (* Or E *)
    define \<beta>' where "\<beta>' = type_of D'"
    show ?case
    proof (rule, rule)
      fix \<phi>
      assume asg: "asg_into_frame \<phi> D"
      have \<alpha>': "\<alpha>' = Fun \<beta> \<beta>'"
        using form.distinct(11) form.distinct(3) form.distinct(7) form.inject(3) replace_App_left.prems(4) wff.simps
        by (metis \<alpha>'_def \<beta>'_def wff_App_type_of)
          (* I could make a lemma of this idea *)
      from asg have "wff \<alpha>' C"
        using replace_App_left
        using form.distinct(11) form.distinct(3) form.distinct(7) form.inject(3) wff.simps
        by (metis \<alpha>' \<beta>'_def type_of wff_App')   
      then have "val D I \<phi> C = val D I \<phi> E"
        using asg replace_App_left by auto
      then show "val D I \<phi> (C \<^bold>\<cdot> D') = val D I \<phi> (E \<^bold>\<cdot> D')"
        using \<alpha>' by auto
    qed
  next
    case (replace_App_right A B D' E C)
    define \<alpha>' where "\<alpha>' = type_of C"
    define \<beta>' where "\<beta>' = type_of D'"
    show ?case 
    proof (rule, rule)
      fix \<phi>
      assume asg: "asg_into_frame \<phi> D"
      have \<alpha>': "\<alpha>' = Fun \<beta> \<beta>'"
        using form.distinct(11) form.distinct(3) form.distinct(7) form.inject(3) 
          replace_App_right.prems(4) wff.simps by (metis \<alpha>'_def \<beta>'_def type_of wff_App')
      from asg have "wff \<beta>' D'"
        using \<beta>'_def replace_App_right.prems(4) by fastforce
      then have "val D I \<phi> D' = val D I \<phi> E"
        using asg replace_App_right by auto
      then show "val D I \<phi> (C \<^bold>\<cdot> D') = val D I \<phi> (C \<^bold>\<cdot> E)"
        using \<alpha>' by auto
    qed
  next
    case (replace_Abs A B C D' x \<alpha>')
    define \<beta>' where "\<beta>' = type_of C"
    show ?case
    proof (rule, rule)
      fix \<phi>
      assume asg: "asg_into_frame \<phi> D"
      then have val_C_eql_val_D':
        "\<forall>z. z \<in>: D \<alpha>' \<longrightarrow> val D I (\<phi>((x, \<alpha>') := z)) C = val D I (\<phi>((x, \<alpha>') := z)) D'"
        using asg replace_App_right
        by (metis form.distinct(11) form.distinct(5) form.distinct(9) form.inject(4) 
            asg_into_frame_fun_upd replace_Abs.IH replace_Abs.prems(1) replace_Abs.prems(2) 
            replace_Abs.prems(3) replace_Abs.prems(4) wff.cases)

      have val_C_eql_val_D'_type: 
        "\<forall>z. z \<in>: D \<alpha>' \<longrightarrow>
                val D I (\<phi>((x, \<alpha>') := z)) C \<in>: D (type_of C) \<and>
                  val D I (\<phi>((x, \<alpha>') := z)) C = val D I (\<phi>((x, \<alpha>') := z)) D'"
      proof (rule; rule)
        fix z 
        assume a2: "z \<in>: D \<alpha>'"
        have "val D I (\<phi>((x, \<alpha>') := z)) C \<in>: D (type_of C)"
          using DI asg a2 asg_into_frame_fun_upd replace_Abs.prems(4) by auto
        moreover
        have "val D I (\<phi>((x, \<alpha>') := z)) C = val D I (\<phi>((x, \<alpha>') := z)) D'"
          using a2 val_C_eql_val_D' replace_Abs by auto
        ultimately
        show
          "val D I (\<phi>((x, \<alpha>') := z)) C \<in>: D (type_of C) \<and>
          val D I (\<phi>((x, \<alpha>') := z)) C = val D I (\<phi>((x, \<alpha>') := z)) D'"
          by auto
      qed
      have "wff (type_of C) D'"
        using replacement_preserves_type replace_Abs.hyps replace_Abs.prems(2) 
          replace_Abs.prems(3) replace_Abs.prems(4) wff_Abs_type_of by blast
      then have same_type: 
        "abstract (D \<alpha>') (D (type_of C)) (\<lambda>z. val D I (\<phi>((x, \<alpha>') := z)) D') =
         abstract (D \<alpha>') (D (type_of D')) (\<lambda>z. val D I (\<phi>((x, \<alpha>') := z)) D')"
        using type_of by presburger
      then show "val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>'. C\<^bold>] = val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>'. D'\<^bold>])"
        using val_C_eql_val_D'_type same_type 
          abstract_extensional[of _ _ _ "\<lambda>xa. val D I (\<phi>((x, \<alpha>') := xa)) D'"]
        by (simp add: val_C_eql_val_D'_type same_type)
    qed
  qed
  then show "valid_in_model D I C'"
    using assms(2) DI unfolding valid_in_model_def valid_general_def by auto
qed

theorem Fun_Tv_Tv_frame_subs_funspace: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "D (Fun Tv Tv) \<subseteq>: funspace (boolset) (boolset)"
  by (metis assms(1) general_model.elims(2) wf_frame_def wf_interp.simps)

(* Corresponds to Andrew's theorem 5402 a for axiom 1 *)
theorem theorem_5402_a_axiom_1_variant: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> axiom_1"
proof (cases "(\<phi> (''g'',Fun Tv Tv))\<langle>true\<rangle> = true \<and> (\<phi> (''g'',Fun Tv Tv))\<langle>false\<rangle> = true")
  (* Proof following Peter Andrew's proof of lemma_5402 *)
  case True
  then have val: "val D I \<phi> (((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> T) \<^bold>\<and> ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> F)) = true"
    using assms lemma_5401_e_variant_2 by (auto simp add: boolean_eq_true lemma_5401_c[OF assms(1,2)] lemma_5401_d[OF assms(1,2)])
  have "\<forall>\<psi>. asg_into_frame \<psi> D \<longrightarrow> 
            agree_off_asg \<psi> \<phi> ''x'' Tv \<longrightarrow> 
            satisfies D I \<psi> (Var ''g'' (Fun Tv Tv) \<^bold>\<cdot> Var ''x'' Tv)"
  proof (rule; rule; rule)
    fix \<psi>
    assume \<psi>: "asg_into_frame \<psi> D" "agree_off_asg \<psi> \<phi> ''x'' Tv"
    then have "\<psi> (''x'', Tv) = true \<or> \<psi> (''x'', Tv) = false"
      using asg_into_interp_is_true_or_false assms
      by auto
    then show " satisfies D I \<psi> (Var ''g'' (Fun Tv Tv) \<^bold>\<cdot> Var ''x'' Tv)"
      using True \<psi> unfolding agree_off_asg_def by auto
  qed
  then have  "val D I \<phi> (\<^bold>[\<^bold>\<forall>''x'':Tv. ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> (Var ''x'' Tv))\<^bold>]) = true"
    using lemma_5401_g using assms by auto
  then show ?thesis
    unfolding axiom_1_def
    using lemma_5401_b[OF assms(1,2)] val by auto
next
  case False
  have xx: "D (Fun Tv Tv) \<subseteq>: funspace (boolset) (boolset)" 
    using assms Fun_Tv_Tv_frame_subs_funspace by auto
  have "\<phi> (''g'', Fun Tv Tv) \<in>: D (Fun Tv Tv)"
    using assms
    by (simp add: asg_into_frame_def) 
  then have 0: "\<phi> (''g'', Fun Tv Tv) \<in>: funspace (D Tv) (D Tv)"
    using assms(1) assms(2) fun_sym_asg_to_funspace by blast

  from False have "(\<phi> (''g'', Fun Tv Tv)\<langle>true\<rangle> \<noteq> true \<or> \<phi> (''g'', Fun Tv Tv)\<langle>false\<rangle> \<noteq> true)"
    by auto
  then have "\<exists>z. \<phi> (''g'', Fun Tv Tv)\<langle>z\<rangle> = false \<and> z \<in>: D Tv"
  proof
    assume a: "\<phi> (''g'', Fun Tv Tv)\<langle>true\<rangle> \<noteq> true"
    have "\<phi> (''g'', Fun Tv Tv)\<langle>true\<rangle> \<in>: boolset"
      by (metis "0" apply_abstract assms(1) boolset_def general_model.elims(2) in_funspace_abstract 
          mem_two true_def wf_frame_def wf_interp.simps)
    from this a have "\<phi> (''g'', Fun Tv Tv)\<langle>true\<rangle> = false \<and> true \<in>: D Tv"
      using assms(1) wf_frame_def wf_interp.simps by auto  
    then show "\<exists>z. \<phi> (''g'', Fun Tv Tv)\<langle>z\<rangle> = false \<and> z \<in>: D Tv"
      by auto
  next
    assume a: "\<phi> (''g'', Fun Tv Tv)\<langle>false\<rangle> \<noteq> true"
    have "\<phi> (''g'', Fun Tv Tv)\<langle>false\<rangle> \<in>: boolset"
      by (metis "0" apply_abstract assms(1) boolset_def general_model.elims(2) in_funspace_abstract 
          mem_two false_def wf_frame_def wf_interp.simps)
    from this a have "\<phi> (''g'', Fun Tv Tv)\<langle>false\<rangle> = false \<and> false \<in>: D Tv" 
      using assms(1) wf_frame_def wf_interp.simps by auto
    then show "\<exists>z. \<phi> (''g'', Fun Tv Tv)\<langle>z\<rangle> = false \<and> z \<in>: D Tv"
      by auto
  qed
  then obtain z where z_p: "\<phi> (''g'', Fun Tv Tv)\<langle>z\<rangle> = false \<and> z \<in>: D Tv"
    by auto
  have "boolean (satisfies D I \<phi> (Var ''g'' (Fun Tv Tv) \<^bold>\<cdot> T)
          \<and> satisfies D I \<phi> (Var ''g'' (Fun Tv Tv) \<^bold>\<cdot> F)) = false"
    using False
    by (smt boolean_def val.simps(1) val.simps(3) lemma_5401_c[OF assms(1,2)] 
        lemma_5401_d[OF assms(1,2)])
  then have 1: "val D I \<phi> ( 
         ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> T) \<^bold>\<and>
         ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> F)) = false"
    using lemma_5401_e_variant_2 assms by auto
  have 3: "asg_into_frame (\<phi>((''x'', Tv) := z)) D \<and>
    agree_off_asg (\<phi>((''x'', Tv) := z)) \<phi> ''x'' Tv \<and>
    \<phi> (''g'', Fun Tv Tv)\<langle>(\<phi>((''x'', Tv) := z)) (''x'', Tv)\<rangle> \<noteq> true"
    using z_p Pair_inject agree_off_asg_def2 asg_into_frame_fun_upd assms(2) true_neq_false by fastforce
  then have 2: "val D I \<phi> (\<^bold>[\<^bold>\<forall>''x'':Tv. ((Var ''g'' (Fun Tv Tv)) \<^bold>\<cdot> (Var ''x'' Tv))\<^bold>]) = false"
    using  lemma_5401_g_variant_1 assms boolean_def by auto
  then show ?thesis
    unfolding axiom_1_def using 1 2 lemma_5401_b_variant_2[OF assms(1,2)] by auto 
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 1 *)
theorem theorem_5402_a_axiom_1: "valid_general axiom_1"
  using theorem_5402_a_axiom_1_variant unfolding valid_general_def valid_in_model_def by auto

(* Corresponds to Andrew's theorem 5402 a for axiom 2 *)
theorem theorem_5402_a_axiom_2_variant: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_2 \<alpha>)"
proof (cases "\<phi>(''x'',\<alpha>) = \<phi>(''y'',\<alpha>)")
  (* Proof following Peter Andrew's proof of lemma_5402 *)
  case True
  have "val D I \<phi> ((Var ''h'' (Fun Tv \<alpha>)) \<^bold>\<cdot> (Var ''x'' \<alpha>)) = 
           (\<phi> (''h'', (Fun Tv \<alpha>)))\<langle>\<phi> (''x'', \<alpha>)\<rangle>"
    using assms by auto
  also
  have "... = \<phi> (''h'', (Fun Tv \<alpha>))\<langle>\<phi> (''y'', \<alpha>)\<rangle>"
    using True by auto
  also
  have "... = val D I \<phi> ((Var ''h'' (Fun Tv \<alpha>)) \<^bold>\<cdot> (Var ''y'' \<alpha>))"
    using assms by auto
  finally
  show ?thesis
    unfolding axiom_2_def 
    using lemma_5401_f_variant_2 assms lemma_5401_b_variant_1[OF assms(1,2)] boolean_def by auto
next
  case False
  have "asg_into_frame \<phi> D"
    using assms(2) by blast
  moreover
  have "general_model D I"
    using assms(1) by blast
  ultimately
  have 
    "boolean (satisfies D I \<phi> \<^bold>[Var ''x'' \<alpha> \<^bold>=\<alpha>\<^bold>= Var ''y'' \<alpha>\<^bold>] \<longrightarrow>
       satisfies D I \<phi>
         \<^bold>[(Var ''h'' (Fun Tv \<alpha>) \<^bold>\<cdot> Var ''x'' \<alpha>) \<^bold>=Tv\<^bold>= Var ''h'' (Fun Tv \<alpha>) \<^bold>\<cdot> Var ''y'' \<alpha>\<^bold>]) =
       true"
    using boolean_eq_true lemma_5401_b by auto
  then
  show ?thesis
    using assms lemma_5401_f_variant_2 unfolding axiom_2_def by auto
qed                                   

(* Corresponds to Andrew's theorem 5402 a for axiom 2 *)
theorem theorem_5402_a_axiom_2: "valid_general (axiom_2 \<alpha>)"
  using theorem_5402_a_axiom_2_variant unfolding valid_general_def valid_in_model_def by auto

(* Below I have versions with "satisfies" and versions with "valid". But it's a bit inconsistent which
   are called variants and which are not. The "satisfies" versions should be called variant
   Actually, we should just come up with better names entirely.
 *)

(* Corresponds to Andrew's theorem 5402 a for axiom 3 *)
theorem theorem_5402_a_axiom_3_variant: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_3 \<alpha> \<beta>)"
proof (cases "\<phi> (''f'',Fun \<alpha> \<beta>) = \<phi> (''g'',Fun \<alpha> \<beta>)")
  case True
    (* Peter Andrews also proves that "V\<phi>[f\<alpha>\<beta> = g\<alpha>\<beta>] = T", but as we
     see it is not necessary. The reason is that to prove an implication true
     it suffices to show that its consequent is true. In that case
     the value of the antecedent is irrelevant. *)
  have "asg_into_frame \<phi> D"
    using assms(2) by blast
  moreover
  have "general_model D I"
    using assms(1) by blast
  moreover
  have "wff Tv \<^bold>[Var ''f'' (Fun \<alpha> \<beta>) \<^bold>=Fun \<alpha> \<beta>\<^bold>= Var ''g'' (Fun \<alpha> \<beta>)\<^bold>]"
    by simp
  moreover
  have "wff Tv \<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[(Var ''f'' (Fun \<alpha> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>) \<^bold>=\<alpha>\<^bold>= Var ''g'' (Fun \<alpha> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>\<^bold>]\<^bold>]"
    by simp
  moreover
  {
    fix \<psi>
    assume agree: "agree_off_asg \<psi> \<phi> ''x'' \<beta>"
    assume asg: "asg_into_interp \<psi> D I"
    have "val D I \<psi> ((Var ''f'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) = \<psi> (''f'',Fun \<alpha> \<beta>)\<langle>\<psi> (''x'', \<beta>)\<rangle>"
      by auto
    also
    have "... = \<phi> (''f'',Fun \<alpha> \<beta>)\<langle>\<psi> (''x'', \<beta>)\<rangle>"
      using agree by auto
    also
    have "... = \<phi> (''g'',Fun \<alpha> \<beta>)\<langle>\<psi> (''x'', \<beta>)\<rangle>"
      using True by auto
    also
    have "... = \<psi> (''g'',Fun \<alpha> \<beta>)\<langle>\<psi> (''x'', \<beta>)\<rangle>"
      using agree by auto
    also
    have "... = val D I \<psi> ((Var ''g'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))"
      by auto
    finally
    have 
      "val D I \<psi>
            (\<^bold>[((Var ''f'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) \<^bold>=\<alpha>\<^bold>= ((Var ''g'' (Fun \<alpha> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))\<^bold>]) 
       = true"
      using lemma_5401_b_variant_1[OF assms(1)] assms agree asg boolean_eq_true by auto
  }
  then have 
    "boolean (satisfies D I \<phi> \<^bold>[Var ''f'' (Fun \<alpha> \<beta>) \<^bold>=Fun \<alpha> \<beta>\<^bold>= Var ''g'' (Fun \<alpha> \<beta>)\<^bold>] \<longrightarrow>
      satisfies D I \<phi>
       \<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[(Var ''f'' (Fun \<alpha> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>) \<^bold>=\<alpha>\<^bold>= Var ''g'' (Fun \<alpha> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>\<^bold>]\<^bold>]) =
      true"
    using assms lemma_5401_g_variant_1 by (simp add: boolean_eq_true)
  ultimately
  show ?thesis
    unfolding axiom_3_def using lemma_5401_f_variant_2 by auto
next
  case False
  then show ?thesis
    using lemma_5401_f_variant_2 assms lemma_5401_b
    unfolding boolean_def axiom_3_def by simp
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 3 *)
theorem theorem_5402_a_axiom_3: "valid_general (axiom_3 \<alpha> \<beta>)"
  using theorem_5402_a_axiom_3_variant unfolding valid_general_def valid_in_model_def by auto

thm lemma_5401_a



(* Corresponds to Andrew's theorem 5402 a for axiom 4_1 with a constant *)
theorem theorem_5402_a_axiom_4_1_variant_cst: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  shows "satisfies D I \<phi> (axiom_4_1_variant_cst x \<alpha> c \<beta> A)"
proof -
  let ?\<psi> = "\<phi>((x,\<alpha>):=val D I \<phi> A)"
  have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. (Cst c \<beta>)\<^bold>] \<^bold>\<cdot> A) = val D I ?\<psi> (Cst c \<beta>)"
     by (rule lemma_5401_a[of _ _ _ _ _ \<beta>]; use assms in auto)
  then have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Cst c \<beta>\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> (Cst c \<beta>)"
    by auto
  moreover
  have "wff \<beta> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Cst c \<beta>\<^bold>] \<^bold>\<cdot> A)"
    using assms by auto
  ultimately
  show ?thesis
    unfolding axiom_4_1_variant_cst_def
    using lemma_5401_b_variant_2[OF assms(1,2)] by auto
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 4_1 *)
theorem theorem_5402_a_axiom_4_1_variant_var: (* new_lemma *)
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  assumes "axiom_4_1_variant_var_side_condition x \<alpha> y \<beta> A"
  shows "satisfies D I \<phi> (axiom_4_1_variant_var x \<alpha> y \<beta> A)"
proof -
  let ?\<psi> = "\<phi>((x,\<alpha>):=val D I \<phi> A)"
  have  "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. (Var y \<beta>)\<^bold>] \<^bold>\<cdot> A) = val D I ?\<psi> (Var y \<beta>)"
    by (rule lemma_5401_a[of _ _ _ _ _  \<beta>], use assms in auto)
  then have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var y \<beta>\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> (Var y \<beta>)"   
    using assms unfolding axiom_4_1_variant_var_side_condition_def by auto
  moreover
  have "wff \<beta> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var y \<beta>\<^bold>] \<^bold>\<cdot> A)"
    using assms by auto
  moreover
  have "wff \<beta> (Var y \<beta>)"
    using assms by auto
  ultimately
  show ?thesis
    unfolding axiom_4_1_variant_var_def
    using lemma_5401_b_variant_2[OF assms(1,2)] by auto
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 4_1 *)
theorem theorem_5402_a_axiom_4_1:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "axiom_4_1_side_condition x \<alpha> y \<beta> A"
  assumes "wff \<alpha> A"
  shows "satisfies D I \<phi> (axiom_4_1 x \<alpha> y \<beta> A)"
  using assms theorem_5402_a_axiom_4_1_variant_cst theorem_5402_a_axiom_4_1_variant_var
  unfolding axiom_4_1_variant_cst_def axiom_4_1_variant_var_side_condition_def
    axiom_4_1_side_condition_def axiom_4_1_variant_var_def
    axiom_4_1_def by auto

(* Corresponds to Andrew's theorem 5402 a for axiom 4_2 *)
theorem theorem_5402_a_axiom_4_2: 
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  shows "satisfies D I \<phi> (axiom_4_2 x \<alpha> A)"
proof -
  let ?\<psi> = "\<phi>((x,\<alpha>):=val D I \<phi> A)"
  have "wff \<alpha> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var x \<alpha>\<^bold>] \<^bold>\<cdot> A)"
    using assms by auto
  moreover
  have "wff \<alpha> A"
    using assms by auto
  moreover
  have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var x \<alpha>\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> A"
    using lemma_5401_a[of _ _ _ _ _ \<alpha> _ _] assms by auto
  ultimately
  show ?thesis
    unfolding axiom_4_2_def by (rule lemma_5401_b_variant_2[OF assms(1,2)])
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 4_3 *)
theorem theorem_5402_a_axiom_4_3: 
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  assumes "wff (Fun \<beta> \<gamma>) B"
  assumes "wff \<gamma> C"
  shows "satisfies D I \<phi> (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)"
proof -
  let ?\<psi> = "\<phi>((x,\<alpha>):=val D I \<phi> A)"
  let ?E = "B \<^bold>\<cdot> C"

  have "val D I \<phi> (LHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)) = val D I ?\<psi> ?E"
    by (metis LHS_def2 assms(3) assms(4) assms(5) axiom_4_3_def lemma_5401_a[OF assms(1,2)] wff_App)
  moreover
  have "... = val D I ?\<psi> (B \<^bold>\<cdot> C)"
    by simp
  moreover
  have "... = (val D I ?\<psi> B)\<langle>val D I ?\<psi> C\<rangle>"
    by simp
  moreover
  have "... = (val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A))\<langle>val D I \<phi> (App \<^bold>[\<^bold>\<lambda>x :\<alpha>. C\<^bold>] A)\<rangle>"
    by (metis assms(3) assms(4) assms(5) lemma_5401_a[OF assms(1,2)])
  moreover
  have "... = val D I \<phi> (RHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A))"
    unfolding axiom_4_3_def by auto
  ultimately
  have "val D I \<phi> (LHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)) = val D I \<phi> (RHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A))"
    by auto
  then have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B \<^bold>\<cdot> C\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> ((\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))"
    unfolding axiom_4_3_def by auto
  moreover
  have "wff \<beta> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B \<^bold>\<cdot> C\<^bold>] \<^bold>\<cdot> A)"
    using assms by auto
  moreover
  have "wff \<beta> ((\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))"
    using assms by auto
  ultimately
  show ?thesis
    unfolding axiom_4_3_def using lemma_5401_b_variant_2[OF assms(1,2)] by auto
qed

lemma lemma_to_help_with_theorem_5402_a_axiom_4_4:
  assumes lambda_eql_lambda_lambda: 
    "\<And>z. z \<in>: D \<gamma> \<Longrightarrow> val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<langle>z\<rangle> = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<langle>z\<rangle>" 
  assumes \<psi>_eql: "\<psi> = \<phi>((x, \<alpha>) := val D I \<phi> A)" 
  assumes "asg_into_frame \<phi> D" 
  assumes "general_model D I" 
  assumes "axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A" 
  assumes "wff \<alpha> A" 
  assumes "wff \<delta> B"
  shows "val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>] = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]"
proof -
  {
    fix e
    assume e_in_D: "e \<in>: D \<gamma>"
    then have "val D I (\<psi>((y, \<gamma>) := e)) B \<in>: D (type_of B)"
      using asg_into_frame_fun_upd assms(3,4,6,7) \<psi>_eql by auto
    then have val_lambda_B: "val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<langle>e\<rangle> = val D I (\<psi>((y, \<gamma>) := e)) B"
      using e_in_D by auto
    have
      "val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<langle>e\<rangle> = 
       abstract (D \<alpha>) (D (type_of B))
         (\<lambda>z. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := z)) B)\<langle>val D I (\<phi>((y, \<gamma>) := e)) A\<rangle>"
      using apply_abstract e_in_D asg_into_frame_fun_upd assms(3,4,6,7) by auto
    then have "val D I (\<psi>((y, \<gamma>) := e)) B =
        abstract (D \<alpha>) (D (type_of B))
         (\<lambda>z. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := z)) B)\<langle>val D I (\<phi>((y, \<gamma>) := e)) A\<rangle>" 
      using val_lambda_B lambda_eql_lambda_lambda e_in_D by metis
  }
  note val_eql_abstract = this

  have 
    "\<forall>e. e \<in>: D \<gamma> \<longrightarrow>
            val D I (\<psi>((y, \<gamma>) := e)) B \<in>: D (type_of B) \<and>
            val D I (\<psi>((y, \<gamma>) := e)) B =
            abstract (D \<alpha>) (D (type_of B))
              (\<lambda>za. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := za)) B)\<langle>val D I (\<phi>((y, \<gamma>) := e)) A\<rangle>"
    using asg_into_frame_fun_upd assms(3,4,6,7) \<psi>_eql val_eql_abstract by auto
  then have 
    "abstract (D \<gamma>) (D (type_of B)) (\<lambda>z. val D I (\<psi>((y, \<gamma>) := z)) B) =
     abstract (D \<gamma>) (D (type_of B))
       (\<lambda>z. abstract (D \<alpha>) (D (type_of B))
         (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B)\<langle>val D I (\<phi>((y, \<gamma>) := z)) A\<rangle>)"
    by (rule abstract_extensional)
  then show ?thesis 
    by auto
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 4_4 *)
theorem theorem_5402_a_axiom_4_4:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A"
  assumes "wff \<alpha> A"
  assumes "wff \<delta> B"
  shows "satisfies D I \<phi> (axiom_4_4 x \<alpha> y \<gamma> B \<delta> A)"
proof -
  define \<psi> where "\<psi> = \<phi>((x,\<alpha>):=val D I \<phi> A)"
  let ?E = "\<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]"
  have fr: "(y, \<gamma>) \<notin> frees A"
    using assms(3) axiom_4_4_side_condition_def by blast
  {
    fix z
    assume z_in_D: "z \<in>: D \<gamma>"
    define \<phi>' where "\<phi>' = \<phi>((y,\<gamma>) := z)"
    have "asg_into_frame \<phi>' D"
      using assms z_in_D unfolding asg_into_frame_def \<phi>'_def by auto
    moreover
    have "\<forall>(x, \<alpha>)\<in>frees A. agree_on_asg \<phi> \<phi>' x \<alpha>"
      using fr unfolding \<phi>'_def by auto
    ultimately
    have "val D I \<phi> A = val D I \<phi>' A"
      using prop_5400[OF assms(1), of _ _ \<alpha>] assms(2) assms(4) by blast 
    then have Az: "\<phi>'((x,\<alpha>):=(val D I \<phi>' A)) = \<psi>((y,\<gamma>):=z)"
      using assms(3) unfolding axiom_4_4_side_condition_def
      by (simp add: fun_upd_twist \<phi>'_def \<psi>_def) 
    then have "abstract (D \<gamma>) (D (type_of B)) (\<lambda>z. val D I (\<psi>((y, \<gamma>) := z)) B)\<langle>z\<rangle> = 
               val D I (\<psi>((y, \<gamma>) := z)) B"
      using apply_abstract_matchable assms(1,2,4,5) type_of asg_into_frame_fun_upd 
        general_model.elims(2) set_theory_axioms z_in_D by (metis \<phi>'_def)
    then have "(val D I \<psi> ?E)\<langle>z\<rangle> = (val D I (\<psi>((y,\<gamma>):=z)) B)"
      by auto
    moreover
    have "... = val D I \<phi>' (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A)"
      using assms(1,2,4,5) asg_into_frame_fun_upd lemma_5401_a set_theory_axioms z_in_D
      by (metis Az \<phi>'_def) 
    moreover
    have "... = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<langle>z\<rangle>"
    proof -
      have valA: "val D I \<phi>' A \<in>: D \<alpha>"
        using \<phi>'_def asg_into_frame_fun_upd z_in_D assms by simp
      have valB: "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B \<in>: D (type_of B)" 
        using asg_into_frame_fun_upd z_in_D assms by (simp add: Az \<psi>_def) 
      have valA': "val D I (\<phi>((y, \<gamma>) := z)) A \<in>: D \<alpha>"
        using z_in_D assms asg_into_frame_fun_upd set_theory_axioms valA unfolding \<psi>_def \<phi>'_def 
        by blast
      have valB':
        "val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := val D I (\<phi>((y, \<gamma>) := z)) A)) B 
         \<in>: D (type_of B)"
        using asg_into_frame_fun_upd z_in_D assms valB \<phi>'_def by blast 
      have
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := val D I (\<phi>((y, \<gamma>) := z)) A)) B"
        unfolding \<psi>_def \<phi>'_def by (metis apply_abstract asg_into_frame_fun_upd set_theory_axioms)
      then have valB_eql_abs: 
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         abstract (D \<alpha>) (D (type_of B))
           (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B)\<langle>val D I (\<phi>((y, \<gamma>) := z)) A\<rangle>"
        using valA' valB' by auto
      then have "abstract (D \<alpha>) (D (type_of B))
              (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B)\<langle>val D I (\<phi>((y, \<gamma>) := z)) A\<rangle> 
            \<in>: D (type_of B)"
        using valB assms z_in_D by auto
      then have 
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         abstract (D \<gamma>) (D (type_of B))
           (\<lambda>z. abstract (D \<alpha>) (D (type_of B))
             (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B)\<langle>val D I (\<phi>((y, \<gamma>) := z)) A\<rangle>)\<langle>z\<rangle>"
        using z_in_D valB_eql_abs by auto
      then show "val D I \<phi>' (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<langle>z\<rangle>"
        using valA valB by auto
    qed
    ultimately
    have "val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<langle>z\<rangle> = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<langle>z\<rangle>"
      by simp
  }
  note lambda_eql_lambda_lambda = this
  have equal_funs: "val D I \<psi> ?E = val D I \<phi> (\<^bold>[\<^bold>\<lambda>y:\<gamma>. (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]) \<^bold>\<cdot> A\<^bold>])"
    using lambda_eql_lambda_lambda \<psi>_def assms lemma_to_help_with_theorem_5402_a_axiom_4_4 by metis
  have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]"
    using equal_funs by (metis \<psi>_def assms(1,2,4,5) lemma_5401_a wff_Abs) 
  then have "satisfies D I \<phi> \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=Fun \<delta> \<gamma>\<^bold>= \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<^bold>]"
    using lemma_5401_b[OF assms(1,2)] assms by auto
  then show ?thesis
    unfolding axiom_4_4_def .
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 4_5 *)
theorem theorem_5402_a_axiom_4_5:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  assumes "wff \<delta> B"
  shows "satisfies D I \<phi> (axiom_4_5 x \<alpha> B \<delta> A)"
proof -
  define \<psi> where "\<psi> = \<phi>((x,\<alpha>):=val D I \<phi> A)"
  let ?E = "\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]"

  {
    assume val: "\<forall>\<phi>. asg_into_frame \<phi> D \<longrightarrow> (\<forall>A \<alpha>. wff \<alpha> A \<longrightarrow> val D I \<phi> A \<in>: D \<alpha>)"
    assume asg: "asg_into_frame \<phi> D"
    assume wffA: "wff \<alpha> A"
    assume wffB: "wff \<delta> B"
    have valA: "val D I \<phi> A \<in>: D \<alpha>"
      using val asg wffA by blast
    have "\<forall>t cs. val D I \<phi> \<^bold>[\<^bold>\<lambda>cs:t. B\<^bold>] \<in>: D (Fun \<delta> t)"
      using val asg wffB wff_Abs by blast
    then have "abstract (D \<alpha>) (D (Fun \<delta> \<alpha>)) (\<lambda>u. abstract (D \<alpha>) (D \<delta>) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) B))\<langle>val D I \<phi> A\<rangle> 
             = abstract (D \<alpha>) (D \<delta>) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) B)"
      using valA wffB by simp
  }
  note abstract_eql = this

  have "val D I \<psi> ?E = val D I \<phi> ?E"
    using prop_5400[OF assms(1), of _ _ "Fun \<delta> \<alpha>"] \<psi>_def assms(2) by auto
  then show ?thesis
    unfolding axiom_4_5_def using lemma_5401_b[OF assms(1,2)] assms abstract_eql by auto
qed

(* Corresponds to Andrew's theorem 5402 a for axiom 5 *)
theorem theorem_5402_a_axiom_5:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_5)"
proof -
  have iden_eql: "iden (D Ind)\<langle>I ''y'' Ind\<rangle> = one_elem_fun (I ''y'' Ind) (D Ind)" (* This should maybe be a lemma *)
  proof -
    have "I ''y'' Ind \<in>: D Ind"
      using assms unfolding  general_model.simps wf_interp.simps[simplified] iden_def one_elem_fun_def
      by auto
    moreover
    have "abstract (D Ind) boolset (\<lambda>y. boolean (I ''y'' Ind = y)) \<in>: funspace (D Ind) boolset"
      using boolean_in_boolset by auto
    ultimately
    show ?thesis
      unfolding iden_def one_elem_fun_def by auto
  qed

  have "val D I \<phi> (\<iota> \<^bold>\<cdot> ((\<^bold>Q Ind) \<^bold>\<cdot> Cst ''y'' Ind)) = 
          val D I \<phi> \<iota>\<langle>val D I \<phi> ((\<^bold>Q Ind) \<^bold>\<cdot> Cst ''y'' Ind)\<rangle>"
    by auto
  moreover
  have "... = val D I \<phi> (Cst ''y'' Ind)"
    using assms iden_eql unfolding general_model.simps wf_interp.simps[simplified] by auto
  ultimately
  show ?thesis
    unfolding axiom_5_def using lemma_5401_b[OF assms(1,2)] by auto
qed

lemma theorem_isa_Tv:
  assumes "theorem A"
  shows "wff Tv A"
  using assms proof (induction)
  case (by_axiom A)
  then show ?case 
  proof (induction)
    case by_axiom_1
    then show ?case 
      unfolding axiom_1_def by auto
  next
    case (by_axiom_2 \<alpha>)
    then show ?case 
      unfolding axiom_2_def by auto
  next
    case (by_axiom_3 \<alpha> \<beta>)
    then show ?case 
      unfolding axiom_3_def by auto
  next
    case (by_axiom_4_1 \<alpha> A \<beta> B x)
    then show ?case 
      unfolding axiom_4_1_def by auto
  next
    case (by_axiom_4_2 \<alpha> A x)
    then show ?case 
      unfolding axiom_4_2_def by auto
  next
    case (by_axiom_4_3 \<alpha> A \<beta> \<gamma> B C x)
    then show ?case 
      unfolding axiom_4_3_def by auto
  next
    case (by_axiom_4_4 \<alpha> A \<delta> B x y \<gamma>)
    then show ?case 
      unfolding axiom_4_4_def by auto
  next
    case (by_axiom_4_5 \<alpha> A \<delta> B x)
    then show ?case 
      unfolding axiom_4_5_def by auto
  next
    case by_axiom_5
    then show ?case 
      unfolding axiom_5_def by auto
  qed
next
  case (by_rule_R A B C)
  then show ?case
    by (smt replacement_preserves_type rule_R.cases wff_Eql')
qed

(* Corresponds to Andrew's theorem 5402 a *)
theorem theorem_5402_a_general:
  assumes "theorem A"
  shows "valid_general A"
  using assms 
proof (induction)
  case (by_axiom A)
  then show ?case
  proof (induction)
    case by_axiom_1
    then show ?case 
      using theorem_5402_a_axiom_1 by auto
  next
    case (by_axiom_2 \<alpha>)
    then show ?case 
      using theorem_5402_a_axiom_2 by auto
  next
    case (by_axiom_3 \<alpha> \<beta>)
    then show ?case 
      using theorem_5402_a_axiom_3 by auto
  next
    case (by_axiom_4_1 \<alpha> A \<beta> B x)
    then show ?case 
      using theorem_5402_a_axiom_4_1
      unfolding valid_general_def valid_in_model_def by auto
  next
    case (by_axiom_4_2 \<alpha> A x)
    then show ?case 
      using theorem_5402_a_axiom_4_2 
      unfolding valid_general_def valid_in_model_def by auto
  next
    case (by_axiom_4_3 \<alpha> A \<beta> \<gamma> B C x)
    then show ?case 
      using theorem_5402_a_axiom_4_3 
      unfolding valid_general_def valid_in_model_def by auto
  next
    case (by_axiom_4_4 \<alpha> A \<delta> B x y \<gamma>)
    then show ?case 
      using theorem_5402_a_axiom_4_4 
      unfolding valid_general_def valid_in_model_def by auto
  next
    case (by_axiom_4_5 \<alpha> A \<delta> B x)
    then show ?case 
      using theorem_5402_a_axiom_4_5 
      unfolding valid_general_def valid_in_model_def by auto
  next
    case by_axiom_5
    then show ?case
      using theorem_5402_a_axiom_5 
      unfolding valid_general_def valid_in_model_def by auto
  qed
next
  case (by_rule_R C AB C')
  then have C_isa_Tv: "wff Tv C"
    using theorem_isa_Tv by blast
  have "\<exists>A B \<beta>. AB = \<^bold>[A \<^bold>=\<beta>\<^bold>= B\<^bold>] \<and> wff \<beta> A \<and> wff \<beta> B"
    using by_rule_R rule_R.simps theorem_isa_Tv by fastforce
  then obtain A B \<beta> where A_B_\<beta>_p: "AB = \<^bold>[A \<^bold>=\<beta>\<^bold>= B\<^bold>] \<and> wff \<beta> A \<and> wff \<beta> B"
    by blast
  then have R: "rule_R C \<^bold>[A \<^bold>=\<beta>\<^bold>= B\<^bold>] C'"
    using by_rule_R by auto
  then have "replacement A B C C'"
    using Eql_def rule_R.cases by fastforce
  show ?case
    using theorem_5402_a_rule_R[of A B \<beta> C C' Tv] by_rule_R.IH R
      A_B_\<beta>_p C_isa_Tv by auto
qed

(* Corresponds to Andrew's theorem 5402 a *)
theorem theorem_5402_a_standard:
  assumes "theorem A"
  shows "valid_standard A"
  using theorem_5402_a_general assms standard_model_is_general_model valid_general_def 
    valid_standard_def by blast


end

end
