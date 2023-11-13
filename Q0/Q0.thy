section \<open>Q0 abbreviations\<close>

theory Q0
  imports Set_Theory 
  abbrevs "App" = "\<^bold>\<cdot>"
    and "Abs" = "\<^bold>[\<^bold>\<lambda>_:_. _\<^bold>]"
    and "Eql" = "\<^bold>[_ \<^bold>=_\<^bold>= _\<^bold>]"
    and "Con" = "\<^bold>\<and>"
    and "Forall" = "\<^bold>[\<^bold>\<forall>_:_. _\<^bold>]"
    and "Imp" = "\<^bold>\<longrightarrow>"
    and "Fun" = "\<^bold>\<Leftarrow>"
begin

lemma arg_cong3: "a = b \<Longrightarrow> c = d \<Longrightarrow> e = f \<Longrightarrow> h a c e = h b d f"
  by auto


section \<open>Syntax and typing\<close>

datatype type_sym =
  Ind | 
  Tv |
  Fun type_sym type_sym (infixl "\<^bold>\<Leftarrow>" 80)

type_synonym var_sym = string
type_synonym cst_sym = string

datatype trm =
  Var var_sym type_sym |
  Cst cst_sym type_sym |
  App trm trm (infixl "\<^bold>\<cdot>" 80) |
  Abs var_sym type_sym trm ("\<^bold>[\<^bold>\<lambda>_:_. _\<^bold>]" [80,80,80])

fun vars :: "trm \<Rightarrow> (var_sym * type_sym) set" where
  "vars (Var x \<alpha>) = {(x,\<alpha>)}"
| "vars (Cst _ _) = {}"
| "vars (A \<^bold>\<cdot> B) = vars A \<union> vars B"
| "vars (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) = {(x,\<alpha>)} \<union> vars A"

fun frees :: "trm \<Rightarrow> (var_sym * type_sym) set" where
  "frees (Var x \<alpha>) = {(x,\<alpha>)}"
| "frees (Cst _ _) = {}"
| "frees (A \<^bold>\<cdot> B) = frees A \<union> frees B"
| "frees (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) = frees A - {(x,\<alpha>)}"

lemma frees_subset_vars:
  "frees A \<subseteq> vars A"
  by (induction A) auto

inductive wff :: "type_sym \<Rightarrow> trm \<Rightarrow> bool" where
  wff_Var: "wff \<alpha> (Var _ \<alpha>)"
| wff_Cst: "wff \<alpha> (Cst _ \<alpha>)"
| wff_App: "wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) A \<Longrightarrow> wff \<beta> B \<Longrightarrow> wff \<alpha> (A \<^bold>\<cdot> B)"
| wff_Abs: "wff \<alpha> A \<Longrightarrow> wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>[\<^bold>\<lambda>x:\<beta>. A\<^bold>]"

fun type_of :: "trm \<Rightarrow> type_sym" where
  "type_of (Var x \<alpha>) = \<alpha>"
| "type_of (Cst c \<alpha>) = \<alpha>"
| "type_of (A \<^bold>\<cdot> B) =
     (case type_of A of \<beta> \<^bold>\<Leftarrow> \<alpha> \<Rightarrow> \<beta>)"
| "type_of \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] = (type_of A) \<^bold>\<Leftarrow> \<alpha>"

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
  "wff \<alpha> (A \<^bold>\<cdot> B) \<longleftrightarrow> (\<exists>\<beta>. wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) A \<and> wff \<beta> B)"
proof
  assume "wff \<alpha> (A \<^bold>\<cdot> B)"
  then show "\<exists>\<beta>. wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) A \<and> wff \<beta> B" 
    using wff.cases by fastforce
next
  assume "\<exists>\<beta>. wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) A \<and> wff \<beta> B"
  then show "wff \<alpha> (A \<^bold>\<cdot> B)"
    using wff_App by auto
qed

lemma wff_Abs'[simp]:
  "wff \<gamma> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) \<longleftrightarrow> (\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = \<beta> \<^bold>\<Leftarrow> \<alpha>)"
proof
  assume "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  then show "\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = \<beta> \<^bold>\<Leftarrow> \<alpha>" 
    using wff.cases by blast
next
  assume "\<exists>\<beta>. wff \<beta> A \<and> \<gamma> = \<beta> \<^bold>\<Leftarrow> \<alpha>"
  then show "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]" 
    using wff_Abs by auto     
qed

lemma wff_Abs_type_of[code]:
  "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] \<longleftrightarrow> (wff (type_of A) A \<and> \<gamma> = (type_of A) \<^bold>\<Leftarrow> \<alpha>)"
proof
  assume "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  then show "wff (type_of A) A \<and> \<gamma> = (type_of A) \<^bold>\<Leftarrow> \<alpha>" 
    using wff.cases by auto
next
  assume "wff (type_of A) A \<and> \<gamma> = (type_of A) \<^bold>\<Leftarrow> \<alpha>"
  then show "wff \<gamma> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]" 
    using wff_Abs by auto
qed

lemma wff_App_type_of[code]:
  "wff \<gamma> ((A \<^bold>\<cdot> B)) \<longleftrightarrow> (wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = \<gamma> \<^bold>\<Leftarrow> (type_of B))"
proof
  assume "wff \<gamma> (A \<^bold>\<cdot> B)"
  then show "wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = \<gamma> \<^bold>\<Leftarrow> (type_of B)" 
    by auto
next
  assume "wff (type_of A) A \<and> wff (type_of B) B \<and> type_of A = \<gamma> \<^bold>\<Leftarrow> (type_of B)"
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

inductive replacement :: "trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
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
  then have "\<exists>\<beta>'. wff (\<beta> \<^bold>\<Leftarrow> \<beta>') C"
    by auto
  then obtain \<beta>' where wff_C: "wff (\<beta> \<^bold>\<Leftarrow> \<beta>') C"
    by auto
  then have e: "wff (\<beta> \<^bold>\<Leftarrow> \<beta>') E"
    using replace_App_left by auto
  define \<alpha>' where "\<alpha>' = \<beta> \<^bold>\<Leftarrow> \<beta>'"
  have "wff \<beta>' D"
    using wff_C unique_type replace_App_left.prems(3) by auto
  then have "wff \<beta> (E \<^bold>\<cdot> D)"
    using e by auto
  then show ?case
    by auto
next
  case (replace_App_right A B D E C)
  have "\<exists>\<beta>'. wff (\<beta> \<^bold>\<Leftarrow> \<beta>') C"
    using replace_App_right.prems(3) by auto
  then obtain \<beta>' where wff_C: "wff (\<beta> \<^bold>\<Leftarrow> \<beta>') C"
    by auto
  have wff_E: "wff \<beta>' E"
    using wff_C unique_type replace_App_right by fastforce
  define \<alpha>' where \<alpha>': "\<alpha>' = \<beta> \<^bold>\<Leftarrow> \<beta>'"
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
  have \<beta>: "\<beta> = \<beta>' \<^bold>\<Leftarrow> \<alpha>'"
    using wff_D unique_type replace_Abs by auto
  have "wff (\<beta>' \<^bold>\<Leftarrow> \<alpha>') (\<^bold>[\<^bold>\<lambda>x:\<alpha>'. D\<^bold>])"
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
  then obtain \<gamma> where \<gamma>: "wff (\<beta> \<^bold>\<Leftarrow> \<gamma>) E \<and> wff \<gamma> D"
    by auto
  then have "wff (\<beta> \<^bold>\<Leftarrow> \<gamma>) C"
    using replace_App_left by auto
  then show ?case
    using \<gamma> by auto 
next
  case (replace_App_right A B D E C)
  then obtain \<gamma> where \<gamma>: "wff (\<beta> \<^bold>\<Leftarrow> \<gamma>) C \<and> wff \<gamma> E"
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


section \<open>Defined wffs\<close>
  \<comment> \<open>This section formalizes most of the definitions and abbreviations from page 212.
    We formalize enough to define the Q0 proof system.\<close>


subsection \<open>Common expressions\<close>

abbreviation (input) Var_yi ("y\<^sub>i") where
  "y\<^sub>i == Cst ''y'' Ind"

abbreviation (input) Var_xo ("x\<^sub>o") where
  "x\<^sub>o == Var ''x'' Tv"

abbreviation (input) Var_yo ("y\<^sub>o") where
  "y\<^sub>o == Var ''y'' Tv"

abbreviation (input) Fun_oo ("oo") where
  "oo == Tv \<^bold>\<Leftarrow> Tv"

abbreviation (input) Fun_ooo ("ooo") where
  "ooo == oo \<^bold>\<Leftarrow> Tv"

abbreviation (input) Var_goo ("g\<^sub>o\<^sub>o") where
  "g\<^sub>o\<^sub>o == Var ''g'' oo"

abbreviation (input) Var_gooo ("g\<^sub>o\<^sub>o\<^sub>o") where
  "g\<^sub>o\<^sub>o\<^sub>o == Var ''g'' ooo"


subsection \<open>Equality symbol\<close>

abbreviation QQ :: "type_sym \<Rightarrow> trm" ("\<^bold>Q") where
  "\<^bold>Q \<alpha> \<equiv> Cst ''Q'' \<alpha>"


subsection \<open>Description or selection operator\<close>

abbreviation \<iota>\<iota> :: "trm" ("\<^bold>\<iota>") where
  "\<^bold>\<iota> \<equiv> Cst ''i'' (Ind \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> Ind))"


subsection \<open>Equality\<close>

definition Eql :: "trm \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm" where
  "Eql A B \<alpha> \<equiv> (\<^bold>Q (Tv \<^bold>\<Leftarrow> \<alpha> \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<cdot> A \<^bold>\<cdot> B"

abbreviation Eql' :: "trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" ("\<^bold>[_ \<^bold>=_\<^bold>= _\<^bold>]" [89]) where
  "\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] \<equiv> Eql A B \<alpha>"

definition LHS where
  "LHS EqlAB = (case EqlAB of (_ \<^bold>\<cdot> A \<^bold>\<cdot> _) \<Rightarrow> A)"

lemma LHS_def2[simp]: "LHS \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] = A"
  unfolding LHS_def Eql_def by auto

definition RHS where
  "RHS EqlAB = (case EqlAB of (_ \<^bold>\<cdot> B ) \<Rightarrow> B)"

lemma RHS_def2[simp]: "RHS (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = B"
  unfolding RHS_def Eql_def by auto

lemma wff_Eql[simp]:
  "wff \<alpha> A \<Longrightarrow> wff \<alpha> B \<Longrightarrow> wff Tv \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]"
  unfolding Eql_def by force

lemma wff_Eql_iff[simp]:
  "wff \<beta> \<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>] \<longleftrightarrow> wff \<alpha> A \<and> wff \<alpha> B \<and> \<beta> = Tv"
  using Eql_def by auto


subsection \<open>Truth\<close>

definition T :: trm where
  "T \<equiv> \<^bold>[(\<^bold>Q ooo) \<^bold>=ooo\<^bold>= (\<^bold>Q ooo)\<^bold>]"

lemma wff_T[simp]: "wff Tv T"
  unfolding T_def by auto

lemma wff_T_iff[simp]: "wff \<alpha> T \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_T by blast

subsection \<open>Falsity\<close>

abbreviation F :: trm where
  "F \<equiv> \<^bold>[\<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>] \<^bold>= oo\<^bold>= \<^bold>[\<^bold>\<lambda>''x'':Tv. x\<^sub>o\<^bold>]\<^bold>]"

lemma wff_F[simp]: "wff Tv F"
  by auto

lemma wff_F_iff[simp]: "wff \<alpha> F \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_F by blast


subsection \<open>Pi\<close>

definition PI :: "type_sym \<Rightarrow> trm" where
  "PI \<alpha> \<equiv> (\<^bold>Q (Tv \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> \<alpha>) \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> \<alpha>))) \<^bold>\<cdot> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>]"

lemma wff_PI[simp]: "wff (Tv \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> \<alpha>)) (PI \<alpha>)"
  unfolding PI_def by auto

lemma wff_PI_subterm[simp]: "wff (Tv \<^bold>\<Leftarrow> \<alpha>) \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>]"
  by auto

lemma wff_PI_subterm_iff[simp]:
  "wff \<beta> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>] \<longleftrightarrow> \<beta> = (Tv \<^bold>\<Leftarrow> \<alpha>)"
  by auto


subsection \<open>Forall\<close>

definition Forall :: "string \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" ("\<^bold>[\<^bold>\<forall>_:_. _\<^bold>]" [80,80,80]) where 
  "\<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] = (PI \<alpha>) \<^bold>\<cdot> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"

lemma wff_Forall[simp]: "wff Tv A \<Longrightarrow> wff Tv \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]"
  unfolding Forall_def by force

lemma wff_Forall_iff[simp]: "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] \<longleftrightarrow> wff Tv A \<and> \<beta> = Tv"
proof 
  assume "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]"
  then show "wff Tv A \<and> \<beta> = Tv"
    by (smt Forall_def unique_type type_sym.inject wff_Abs' wff_App' wff_PI)
next
  assume "wff Tv A \<and> \<beta> = Tv"
  then show "wff \<beta> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>]" 
    unfolding Forall_def by force
qed


subsection \<open>Conjunction symbol\<close>

definition Con_sym :: trm where
  "Con_sym \<equiv>
    \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv.
      \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>]  \<^bold>=Tv \<^bold>\<Leftarrow> ooo\<^bold>=  \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]
    \<^bold>]\<^bold>]"

lemma wff_Con_sym[simp]: "wff ooo Con_sym"
  unfolding Con_sym_def by auto

lemma wff_Con_sym'[simp]: "wff \<alpha> Con_sym \<longleftrightarrow> \<alpha> = ooo"
  unfolding Con_sym_def by auto


lemma wff_Con_sym_subterm0[simp]:
  "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff (Tv \<^bold>\<Leftarrow> ooo) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> A \<^bold>\<cdot> B\<^bold>]"
  by force

lemma wff_Con_sym_subterm0_iff[simp]:
  "wff \<beta> \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> A \<^bold>\<cdot> B\<^bold>] \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<beta> = (Tv \<^bold>\<Leftarrow> ooo)"
proof
  assume wff: "wff \<beta> \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> A \<^bold>\<cdot> B\<^bold>]"
  then have "wff Tv A"
    by auto
  moreover
  from wff have "wff Tv B"
    by auto
  moreover
  from wff have "\<beta> = Tv \<^bold>\<Leftarrow> ooo"
    by auto
  ultimately show "wff Tv A \<and> wff Tv B \<and> \<beta> = Tv \<^bold>\<Leftarrow> ooo"
    by auto
next
  assume "wff Tv A \<and> wff Tv B \<and> \<beta> = Tv \<^bold>\<Leftarrow> ooo"
  then show "wff \<beta> \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> A \<^bold>\<cdot> B\<^bold>]"
    by force
qed

lemma wff_Con_sym_subterm1[simp]:
  "wff Tv \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]"
  by auto

lemma wff_Con_sym_subterm1_iff[simp]:
  "wff \<alpha> \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>] \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_Con_sym_subterm1 by blast

lemma wff_Con_sym_subterm2[simp]:
  "wff oo \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]"
  by auto

lemma wff_Con_sym_subterm2_iff[simp]:
  "wff \<alpha> \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot>  x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<longleftrightarrow> \<alpha> = oo"
  by auto

subsection \<open>Conjunction\<close>

definition Con :: "trm \<Rightarrow> trm \<Rightarrow> trm" (infix "\<^bold>\<and>" 80) where
  "A \<^bold>\<and> B = Con_sym \<^bold>\<cdot> A \<^bold>\<cdot> B"

lemma wff_Con[simp]: "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff Tv (A \<^bold>\<and> B)"
  unfolding Con_def by auto

lemma wff_Con_iff[simp]: "wff \<alpha> (A \<^bold>\<and> B) \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<alpha> = Tv"
  unfolding Con_def by auto


subsection \<open>Implication symbol\<close>

definition Imp_sym :: trm where
  "Imp_sym \<equiv> \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]\<^bold>]"

lemma wff_Imp_sym[simp]:
  "wff ooo Imp_sym"
  unfolding Imp_sym_def by auto

lemma wff_Imp_sym_iff[simp]:
  "wff \<alpha> Imp_sym \<longleftrightarrow> \<alpha> = ooo"
  unfolding Imp_sym_def by auto

lemma wff_Imp_sym_subterm0[simp]:
  "wff Tv (x\<^sub>o \<^bold>\<and> y\<^sub>o)"
  by auto

lemma wff_Imp_sym_subterm0_iff[simp]:
  "wff \<alpha> (x\<^sub>o \<^bold>\<and> y\<^sub>o) \<longleftrightarrow> \<alpha> = Tv"
   by auto

lemma wff_Imp_sym_subterm1[simp]:
  "wff Tv \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]"
  by auto

lemma wff_Imp_sym_subterm1_iff[simp]:
  "wff \<alpha> \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] \<longleftrightarrow> \<alpha> = Tv"
  using unique_type wff_Imp_sym_subterm1 by blast

lemma wff_Imp_sym_subterm2[simp]:
  "wff oo \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]"
  by auto

lemma wff_Imp_sym_subterm2_iff[simp]:
  "wff \<alpha> \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<longleftrightarrow> \<alpha> = oo"
  by auto


subsection \<open>Implication\<close>

definition Imp :: "trm \<Rightarrow> trm \<Rightarrow> trm" (infix "\<^bold>\<longrightarrow>" 80) where
  "A \<^bold>\<longrightarrow> B = Imp_sym \<^bold>\<cdot> A \<^bold>\<cdot> B"

lemma wff_Imp[simp]: "wff Tv A \<Longrightarrow> wff Tv B \<Longrightarrow> wff Tv (A \<^bold>\<longrightarrow> B)"
  unfolding Imp_def by auto

lemma wff_Imp_iff[simp]: "wff \<alpha> (A \<^bold>\<longrightarrow> B) \<longleftrightarrow> wff Tv A \<and> wff Tv B \<and> \<alpha> = Tv"
  using Imp_def by auto


section \<open>The Q0 proof system\<close>

definition axiom_1 :: trm where
  "axiom_1 \<equiv> \<^bold>[((g\<^sub>o\<^sub>o \<^bold>\<cdot> T) \<^bold>\<and> (g\<^sub>o\<^sub>o \<^bold>\<cdot> F)) \<^bold>=Tv\<^bold>= \<^bold>[\<^bold>\<forall>''x'':Tv. g\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o\<^bold>]\<^bold>]"

lemma wff_axiom_1[simp]: "wff Tv axiom_1"
  unfolding axiom_1_def by auto

definition axiom_2 :: "type_sym \<Rightarrow> trm" where
  "axiom_2 \<alpha> \<equiv>
       \<^bold>[(Var ''x'' \<alpha>) \<^bold>=\<alpha>\<^bold>= (Var ''y'' \<alpha>)\<^bold>] \<^bold>\<longrightarrow>
       \<^bold>[((Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<cdot> (Var ''x'' \<alpha>)) \<^bold>=Tv\<^bold>= ((Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<cdot> (Var ''y'' \<alpha>))\<^bold>]"

definition axiom_3 :: "type_sym \<Rightarrow> type_sym \<Rightarrow> trm" where
  "axiom_3 \<alpha> \<beta> \<equiv>
       \<^bold>[\<^bold>[(Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>=\<alpha> \<^bold>\<Leftarrow> \<beta>\<^bold>= (Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>))\<^bold>] \<^bold>=Tv\<^bold>=
       \<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[((Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) \<^bold>=\<alpha>\<^bold>= ((Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))\<^bold>]\<^bold>]\<^bold>]"

definition axiom_4_1 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_1 x \<alpha> B \<beta> A \<equiv> \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= B\<^bold>]"

definition axiom_4_1_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> bool" where
  "axiom_4_1_side_condition x \<alpha> B \<beta> A \<equiv> (\<exists>c. B = Cst c \<beta>) \<or> (\<exists>y. B = Var y \<beta> \<and> (x \<noteq> y \<or> \<alpha> \<noteq> \<beta>))"

definition axiom_4_2 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_2 x \<alpha> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var x \<alpha>\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<alpha>\<^bold>= A\<^bold>]"

definition axiom_4_3 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow>
                          type_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm  \<Rightarrow> trm" where
  "axiom_4_3 x \<alpha> B \<beta> \<gamma> C A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. B \<^bold>\<cdot> C\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= ((\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))\<^bold>]"

definition axiom_4_4 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_4 x \<alpha> y \<gamma> B \<delta> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<delta> \<^bold>\<Leftarrow> \<gamma>\<^bold>= \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<^bold>]"

definition axiom_4_4_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> bool" where
  "axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A \<equiv> (x \<noteq> y \<or> \<alpha> \<noteq> \<gamma>) \<and> (y, \<gamma>) \<notin> vars A"

definition axiom_4_5 :: "var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_5 x \<alpha> B \<delta> A = \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<delta> \<^bold>\<Leftarrow> \<alpha> \<^bold>= \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]\<^bold>]"

definition axiom_5 where
  "axiom_5 = \<^bold>[(\<^bold>\<iota> \<^bold>\<cdot> ((\<^bold>Q (Tv \<^bold>\<Leftarrow> Ind \<^bold>\<Leftarrow> Ind)) \<^bold>\<cdot> y\<^sub>i)) \<^bold>=Ind\<^bold>= y\<^sub>i\<^bold>]"

inductive axiom :: "trm \<Rightarrow> bool" where
  by_axiom_1: 
  "axiom axiom_1"
| by_axiom_2: 
  "axiom (axiom_2 \<alpha>)"
| by_axiom_3: 
  "axiom (axiom_3 \<alpha> \<beta>)"
| by_axiom_4_1: 
  "wff \<alpha> A \<Longrightarrow>
   wff \<beta> B \<Longrightarrow>
   axiom_4_1_side_condition x \<alpha> B \<beta> A \<Longrightarrow>
   axiom (axiom_4_1 x \<alpha> B \<beta> A)"
| by_axiom_4_2: 
  "wff \<alpha> A \<Longrightarrow>
   axiom (axiom_4_2 x \<alpha> A)"
| by_axiom_4_3: 
  "wff \<alpha> A \<Longrightarrow>
   wff (\<beta> \<^bold>\<Leftarrow> \<gamma>) B \<Longrightarrow>
   wff \<gamma> C \<Longrightarrow>
   axiom (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)"
| by_axiom_4_4: 
  "wff \<alpha> A \<Longrightarrow>
   wff \<delta> B \<Longrightarrow>
   axiom_4_4_side_condition x \<alpha> y \<gamma> B \<delta> A \<Longrightarrow>
   axiom (axiom_4_4 x \<alpha> y \<gamma> B \<delta> A)"
| by_axiom_4_5: 
  "wff \<alpha> A \<Longrightarrow>
   wff \<delta> B \<Longrightarrow>
   axiom (axiom_4_5 x \<alpha> B \<delta> A)"
| by_axiom_5: 
  "axiom (axiom_5)"

inductive rule_R :: "trm \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> bool" where
  "replacement A B C D \<Longrightarrow> rule_R C (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) D"

definition "proof" :: "trm \<Rightarrow> trm list \<Rightarrow> bool" where
  "proof A p \<longleftrightarrow> (p \<noteq> [] \<and> last p = A \<and>
                    (\<forall>i<length p. axiom (p ! i) 
                  \<or> (\<exists>j<i. \<exists>k<i. rule_R (p ! j) (p ! k) (p ! i))))"

(* Peter Andrews defines theorems directly from "proof", here I instead define it as an inductive predicate based on rule_R *)
inductive "theorem" :: "trm \<Rightarrow> bool" where
  by_axiom: "axiom A \<Longrightarrow> theorem A"
| by_rule_R: "theorem A \<Longrightarrow> theorem B \<Longrightarrow> rule_R A B C \<Longrightarrow> theorem C"

(* Two variant formulations of axiom 4_1: *)
definition axiom_4_1_variant_cst :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_1_variant_cst x \<alpha> c \<beta> A \<equiv> \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. Cst c \<beta>\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= (Cst c \<beta>)\<^bold>]"

definition axiom_4_1_variant_var :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> trm" where
  "axiom_4_1_variant_var x \<alpha> y \<beta> A \<equiv>  \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. Var y \<beta>\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<beta>\<^bold>= Var y \<beta>\<^bold>]"

definition axiom_4_1_variant_var_side_condition :: "var_sym \<Rightarrow> type_sym \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> trm \<Rightarrow> bool" where
  "axiom_4_1_variant_var_side_condition x \<alpha> y \<beta> A \<equiv> x \<noteq> y \<or> \<alpha> \<noteq> \<beta>"


section \<open>Semantics\<close>

type_synonym 's frame = "type_sym \<Rightarrow> 's"

type_synonym 's denotation = "cst_sym \<Rightarrow> type_sym \<Rightarrow> 's"

type_synonym 's asg = "var_sym * type_sym \<Rightarrow> 's"

definition agree_off_asg :: "'s asg \<Rightarrow> 's asg \<Rightarrow> var_sym \<Rightarrow> type_sym \<Rightarrow> bool" where
  "agree_off_asg \<phi> \<psi> x \<alpha> \<longleftrightarrow> (\<forall>y \<beta>. (y\<noteq>x \<or> \<beta> \<noteq> \<alpha>) \<longrightarrow> \<phi> (y,\<beta>) = \<psi> (y,\<beta>))"

lemma agree_off_asg_def2:
  "agree_off_asg \<psi> \<phi> x \<alpha> \<longleftrightarrow> (\<exists>xa. \<phi>((x, \<alpha>) := xa) = \<psi>)"
  unfolding agree_off_asg_def by force

lemma agree_off_asg_disagree_var_sym[simp]:
  "agree_off_asg \<psi> \<phi> x \<alpha> \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<psi>(y,\<beta>) = \<phi>(y,\<beta>)"
  unfolding agree_off_asg_def by auto

lemma agree_off_asg_disagree_type_sym[simp]:
  "agree_off_asg \<psi> \<phi> x \<alpha> \<Longrightarrow> \<alpha> \<noteq> \<beta> \<Longrightarrow> \<psi>(y,\<beta>) = \<phi>(y,\<beta>)"
  unfolding agree_off_asg_def by auto


context set_theory
begin

definition wf_frame :: "'s frame \<Rightarrow> bool" where
  "wf_frame D \<longleftrightarrow> D Tv = boolset \<and> (\<forall>\<alpha> \<beta>. D (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<subseteq>: funspace (D \<beta>) (D \<alpha>)) \<and> (\<forall>\<alpha>. D \<alpha> \<noteq> Ø)"

definition inds :: "'s frame \<Rightarrow> 's" where
  "inds Fr = Fr Ind"

inductive wf_interp :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "wf_frame D \<Longrightarrow>
   \<forall>c \<alpha>. I c \<alpha> \<in>: D \<alpha> \<Longrightarrow>
   \<forall>\<alpha>. I ''Q'' (Tv \<^bold>\<Leftarrow> \<alpha> \<^bold>\<Leftarrow> \<alpha>) = iden (D \<alpha>) \<Longrightarrow>
   (I ''i'' (Ind \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> Ind))) \<in>: funspace (D (Tv \<^bold>\<Leftarrow> Ind)) (D Ind) \<Longrightarrow>
   \<forall>x. x \<in>: D Ind \<longrightarrow> (I ''i'' (Ind \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> Ind))) \<cdot> one_elem_fun x (D Ind) = x \<Longrightarrow>
   wf_interp D I"

definition asg_into_frame :: "'s asg \<Rightarrow> 's frame \<Rightarrow> bool" where
  "asg_into_frame \<phi> D \<longleftrightarrow> (\<forall>x \<alpha>. \<phi> (x, \<alpha>) \<in>: D \<alpha>)"

abbreviation(input) asg_into_interp :: "'s asg \<Rightarrow> 's frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "asg_into_interp \<phi> D I \<equiv> asg_into_frame \<phi> D"

(* Note that because Isabelle's HOL is total, val will also give values to trms that are not wffs *)
fun val :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> 's asg \<Rightarrow> trm \<Rightarrow> 's" where
  "val D I \<phi> (Var x \<alpha>) = \<phi> (x,\<alpha>)"
| "val D I \<phi> (Cst c \<alpha>) = I c \<alpha>"
| "val D I \<phi> (A \<^bold>\<cdot> B) = val D I \<phi> A \<cdot> val D I \<phi> B"
| "val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] = abstract (D \<alpha>) (D (type_of B)) (\<lambda>z. val D I (\<phi>((x,\<alpha>):=z)) B)"

fun general_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "general_model D I \<longleftrightarrow> wf_interp D I \<and> (\<forall>\<phi> A \<alpha>. asg_into_interp \<phi> D I \<longrightarrow> wff \<alpha> A \<longrightarrow> val D I \<phi> A \<in>: D \<alpha>)"

fun standard_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> bool" where
  "standard_model D I \<longleftrightarrow> wf_interp D I \<and> (\<forall>\<alpha> \<beta>. D (\<alpha> \<^bold>\<Leftarrow> \<beta>) = funspace (D \<beta>) (D \<alpha>))"

lemma asg_into_frame_fun_upd:
  assumes "asg_into_frame \<phi> D"
  assumes "xa \<in>: D \<alpha>"
  shows "asg_into_frame (\<phi>((x, \<alpha>) := xa)) D"
  using assms unfolding asg_into_frame_def by auto

lemma asg_into_interp_fun_upd:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  shows "asg_into_interp (\<phi>((x, \<alpha>) := val D I \<phi> A)) D I"
  using assms asg_into_frame_fun_upd by auto

lemma standard_model_is_general_model: (* property mentioned on page 239 *)
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

(* Corresponds to Andrews' proposition 5400 *)
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
  have "abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<phi>((x, \<alpha>) := z)) A) = 
        abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<psi>((x, \<alpha>) := z)) A)"
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
abbreviation satisfies :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> 's asg \<Rightarrow> trm \<Rightarrow> bool" where
  "satisfies D I \<phi> A \<equiv> (val D I \<phi> A = true)"

definition valid_in_model :: "'s frame \<Rightarrow> 's denotation \<Rightarrow> trm \<Rightarrow> bool" where
  "valid_in_model D I A \<equiv> (\<forall>\<phi>. asg_into_interp \<phi> D I \<longrightarrow> val D I \<phi> A = true)"

definition valid_general :: "trm \<Rightarrow> bool" where
  "valid_general A \<equiv> \<forall>D I. general_model D I \<longrightarrow> valid_in_model D I A"

definition valid_standard :: "trm \<Rightarrow> bool" where
  "valid_standard A \<equiv> \<forall>D I. standard_model D I \<longrightarrow> valid_in_model D I A"


section \<open>Semantics of defined wffs\<close>

(* Corresponds to Andrews' lemma 5401 a *)
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
          (abstract (D \<alpha>) (D \<beta>) (\<lambda>z. val D I (\<phi>((x, \<alpha>) := z)) B)) \<cdot> val D I \<phi> A"
    using assms by auto
  also
  have "... = val D I (\<phi>((x, \<alpha>) := val D I \<phi> A)) B"
    using apply_abstract val_A val_B by auto
  finally
  show ?thesis 
    by auto
qed

(* Corresponds to Andrews' lemma 5401 b *)
lemma lemma_5401_b_variant_1:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = (boolean (val D I \<phi> A = val D I \<phi> B))"
proof -
  have "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = (I ''Q'' (Tv \<^bold>\<Leftarrow> \<alpha> \<^bold>\<Leftarrow> \<alpha>)) \<cdot> val D I \<phi> A \<cdot> val D I \<phi> B"
    unfolding Eql_def by auto
  have "... = (iden (D \<alpha>)) \<cdot> val D I \<phi> A \<cdot> val D I \<phi> B"
    using assms general_model.simps wf_interp.simps by auto 
  also
  have "... = boolean (val D I \<phi> A = val D I \<phi> B)"
    using apply_id using assms general_model.simps by blast
  finally show ?thesis 
    unfolding Eql_def by simp
qed

(* Corresponds to Andrews' lemma 5401 b *)
lemma lemma_5401_b:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = true \<longleftrightarrow> val D I \<phi> A = val D I \<phi> B"
  using lemma_5401_b_variant_1[OF assms] boolean_eq_true by auto

(* Corresponds to Andrews' lemma 5401 b *)
lemma lemma_5401_b_variant_2: \<comment> \<open>Just a reformulation of @{thm [source] lemma_5401_b}'s directions\<close> 
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  assumes "val D I \<phi> A = val D I \<phi> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = true"
  using assms(5) lemma_5401_b[OF assms(1,2,3,4)] by auto 

(* Corresponds to Andrews' lemma 5401 b *)
lemma lemma_5401_b_variant_3: \<comment> \<open>Just a reformulation of @{thm [source] lemma_5401_b}'s directions\<close> 
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A" "wff \<alpha> B"
  assumes "val D I \<phi> A \<noteq> val D I \<phi> B"
  shows "val D I \<phi> (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) = false"
  using assms(5) lemma_5401_b_variant_1[OF assms(1,2,3,4)] by (simp add: boolean_def) 

(* Corresponds to Andrews' lemma 5401 c *)
lemma lemma_5401_c:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "val D I \<phi> T = true"
  using assms lemma_5401_b[OF assms(1,2)] unfolding T_def by auto

(* Corresponds to Andrews' lemma 5401 d *)
lemma lemma_5401_d:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "val D I \<phi> F = false"
proof -
  have "iden boolset \<in>: D ooo"
    using assms general_model.simps wf_interp.simps wf_frame_def by metis
  then have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>]) \<cdot> false \<noteq> (val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. x\<^sub>o\<^bold>]) \<cdot> false" 
    using assms wf_interp.simps wf_frame_def true_neq_false 
      apply_id[of "iden boolset" "(D ooo)" "iden boolset"]
    unfolding boolean_def Eql_def T_def by auto
  then have neqLR: "val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>] \<noteq> val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. x\<^sub>o\<^bold>]"
    by metis
  have "val D I \<phi> F = boolean (val D I \<phi> (\<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>]) = val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. x\<^sub>o\<^bold>])"
    using lemma_5401_b_variant_1[OF assms(1,2), 
        of "oo" "(\<^bold>[\<^bold>\<lambda>''x'':Tv. T\<^bold>])" "\<^bold>[\<^bold>\<lambda>''x'':Tv. x\<^sub>o\<^bold>]"] assms
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

lemma asg_into_interp_fun_upd_true:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "asg_into_interp (\<phi>((x, Tv) := true)) D I"
  using asg_into_interp_fun_upd[OF assms wff_T, of x] lemma_5401_c[OF assms(1,2)] by auto

lemma asg_into_interp_fun_upd_false:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "asg_into_interp (\<phi>((x, Tv) := false)) D I"
  using asg_into_interp_fun_upd[OF assms wff_F, of x] lemma_5401_d[OF assms] by auto

(* Corresponds to Andrews' lemma 5401 e_1 *)
lemma lemma_5401_e_1:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "(val D I \<phi> Con_sym) \<cdot> true \<cdot> true = true"
proof -
  define \<phi>' where "\<phi>' \<equiv> \<phi>((''x'',Tv) := val D I \<phi> T)"
  define \<phi>'' where "\<phi>'' \<equiv> \<phi>'((''y'',Tv) :=  val D I \<phi>' T)"
  define \<phi>''' where "\<phi>''' \<equiv> \<lambda>z. \<phi>''((''g'', ooo) := z)"
  have \<phi>'_asg_into: "asg_into_interp \<phi>' D I"
    unfolding \<phi>'_def using asg_into_interp_fun_upd[OF assms wff_T] by blast
  have \<phi>''_asg_into: "asg_into_interp \<phi>'' D I"
    unfolding \<phi>''_def using asg_into_interp_fun_upd[OF assms(1) \<phi>'_asg_into wff_T] by blast

  have "(val D I \<phi> Con_sym) \<cdot> true \<cdot> true = val D I \<phi> (Con_sym \<^bold>\<cdot> T \<^bold>\<cdot> T)"
    using lemma_5401_c[OF assms(1,2)] by auto
  also
  have "... = val D I \<phi> (\<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]\<^bold>] \<^bold>\<cdot> T \<^bold>\<cdot> T)"
    unfolding Con_sym_def by auto 
  also
  have "... = (val D I \<phi> ((\<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]\<^bold>] \<^bold>\<cdot> T))) \<cdot> val D I \<phi> T"
    by simp
  also
  have "... = (val D I (\<phi>((''x'',Tv) := val D I \<phi> T)) ((\<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]))) \<cdot> val D I \<phi> T"
    by (metis lemma_5401_a[OF assms(1,2)] wff_Con_sym_subterm2 wff_T)
  also
  have "... = (val D I \<phi>' ((\<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]))) \<cdot> val D I \<phi> T"
    unfolding \<phi>'_def ..
  also
  have "... = (val D I \<phi>' ((\<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]))) \<cdot> val D I \<phi>' T"
    using \<phi>'_asg_into assms(2) lemma_5401_c[OF assms(1)] by auto
  also
  have "... = (val D I \<phi>' (\<^bold>[\<^bold>\<lambda>''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<^bold>\<cdot> T))"
    by simp
  also
  have "... = (val D I (\<phi>'((''y'',Tv) :=  val D I \<phi>' T)) (\<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]))"
    by (meson \<phi>'_asg_into assms(1) lemma_5401_a[OF assms(1)] wff_Con_sym_subterm1 wff_T)
  also
  have "... = (val D I \<phi>'' (\<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]))"
    unfolding \<phi>''_def ..
  also
  have "... = true"
  proof (rule lemma_5401_b_variant_2[OF assms(1)])
    show "wff (Tv \<^bold>\<Leftarrow> ooo) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>]"
      by auto
  next
    show "wff (Tv \<^bold>\<Leftarrow> ooo) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]"
      by auto
  next
    show "asg_into_frame \<phi>'' D"
      using \<phi>''_asg_into by blast
  next
    have "val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] = abstract (D ooo) (D Tv)
                  (\<lambda>z. val D I (\<phi>''((''g'', ooo) := z)) 
                     (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T))"
      by (simp only: val.simps(4) type_of.simps type_sym.case)
    also
    have "... = abstract (D ooo) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T))"
      unfolding \<phi>'''_def ..
    also
    have "... = abstract (D ooo) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) g\<^sub>o\<^sub>o\<^sub>o \<cdot> val D I (\<phi>''' z) T
                     \<cdot> val D I (\<phi>''' z) T)"
      unfolding val.simps(3) ..
    also
    have "... = abstract (D ooo) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) g\<^sub>o\<^sub>o\<^sub>o \<cdot> true \<cdot> true)"
    proof (rule abstract_extensional')
      fix x
      assume "x \<in>: D ooo"
      then have "val D I (\<phi>''' x) (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T) \<in>: D Tv"
        using \<phi>'''_def \<phi>''_asg_into asg_into_frame_fun_upd assms(1) 
          general_model.elims(2) type_sym.inject wff_Abs_type_of wff_Con_sym_subterm0 wff_T 
        by (metis wff_App wff_Var)
      then show "val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> val D I (\<phi>''' x) T \<cdot>
                   val D I (\<phi>''' x) T
                 \<in>: D Tv"
        by simp
    next
      fix x
      assume "x \<in>: D ooo"
      then have "val D I (\<phi>''' x) T = true"
        unfolding \<phi>'''_def using  \<phi>''_asg_into asg_into_frame_fun_upd 
          lemma_5401_c[OF assms(1)] by blast
      then show "val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> val D I (\<phi>''' x) T \<cdot>
                   val D I (\<phi>''' x) T =
                 val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> true \<cdot> true" by auto
    qed
    also
    have "... = abstract (D ooo) (D Tv) 
                  (\<lambda>z. val D I (\<phi>''' z) g\<^sub>o\<^sub>o\<^sub>o \<cdot>
                         val D I (\<phi>''' z) x\<^sub>o \<cdot> val D I (\<phi>''' z) y\<^sub>o)"
    proof (rule abstract_extensional')
      fix x
      assume x_in_D: "x \<in>: D ooo"
      then have "val D I (\<phi>''' x) (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T) \<in>: D Tv"
        using \<phi>'''_def \<phi>''_asg_into asg_into_frame_fun_upd assms(1) 
          general_model.elims(2) type_sym.inject wff_Abs_type_of wff_Con_sym_subterm0 wff_T 
        by (metis wff_App wff_Var)
      then have "val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> val D I (\<phi>''' x) T \<cdot>
                   val D I (\<phi>''' x) T \<in>: D Tv"
        by simp
      then show "val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> true \<cdot> true \<in>: D Tv"
        by (metis \<phi>'''_def \<phi>''_asg_into lemma_5401_c[OF assms(1)] asg_into_frame_fun_upd x_in_D)
    next
      fix x
      assume x_in_D: "x \<in>: D ooo"
      then have "val D I (\<phi>''' x) x\<^sub>o = true"
        unfolding \<phi>'''_def \<phi>''_def \<phi>'_def using lemma_5401_c[OF assms(1,2)] by auto
      moreover
      from x_in_D have "val D I (\<phi>''' x) y\<^sub>o = true"
        unfolding \<phi>'''_def \<phi>''_def using \<phi>'_asg_into lemma_5401_c[OF assms(1)] by auto
      ultimately
      show "val D I (\<phi>''' x) g\<^sub>o\<^sub>o\<^sub>o \<cdot> true \<cdot> true =
        val D I (\<phi>''' x)
          g\<^sub>o\<^sub>o\<^sub>o \<cdot>
            val D I (\<phi>''' x) x\<^sub>o \<cdot> val D I (\<phi>''' x) y\<^sub>o" 
        by auto
    qed
    also
    have "... = abstract (D ooo) (D Tv) (\<lambda>z. val D I (\<phi>''' z)
                  (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o))"
      unfolding val.simps(3) ..
    also
    have "... = abstract (D ooo) (D Tv)
                  (\<lambda>z. val D I (\<phi>''((''g'', ooo) := z)) 
                         (g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o))"
      unfolding \<phi>'''_def ..
    also
    have "... = val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':ooo.
                                g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]"
      by (simp only: val.simps(4) type_of.simps type_sym.case)
    finally
    show "val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] = val D I \<phi>'' \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]" 
      .
  qed
  finally show ?thesis .
qed

(* Corresponds to Andrews' lemma 5401 e_2 *)
lemma lemma_5401_e_2:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Con_sym) \<cdot> false \<cdot> y = false"
proof -
  define give_x :: trm where "give_x = \<^bold>[\<^bold>\<lambda>''y'':Tv. x\<^sub>o\<^bold>]"
  define give_fst :: trm where "give_fst = \<^bold>[\<^bold>\<lambda> ''x'':Tv. give_x\<^bold>]"
  define val_give_fst :: 's where "val_give_fst = val D I \<phi> give_fst"
  have wff_give_x: "wff oo give_x"
    unfolding give_x_def by auto

  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> 
               b \<in>: D Tv \<Longrightarrow> 
               val D I (\<phi>((''x'', Tv) := a)) give_x \<in>: D (type_of give_x)"
    using wff_give_x asg_into_frame_def assms(1,2) by auto
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_x \<cdot> b = a"
    unfolding give_x_def by auto
  ultimately
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow>
               b \<in>: D Tv \<Longrightarrow> 
               abstract (D Tv) (D (type_of give_x)) (\<lambda>z. val D I (\<phi>((''x'', Tv) := z)) give_x) \<cdot> a \<cdot> b
               = a"
    by auto
  then have val_give_fst_simp: "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val_give_fst \<cdot> a \<cdot> b = a"
    unfolding val_give_fst_def give_fst_def by auto

  have wff_give_fst: "wff ooo give_fst"
    unfolding give_fst_def give_x_def by auto
  then have val_give_fst_fun: "val_give_fst \<in>: D ooo"
    unfolding val_give_fst_def using assms by auto

  have "val D I (\<phi>((''x'', Tv) := false, 
                   (''y'', Tv) := y, 
                   (''g'', ooo) := val_give_fst)) T \<in>: D Tv"
    by (smt Pair_inject wff_give_fst assms(1,2,3) fun_upd_twist general_model.simps
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_true[OF assms(1)] 
        asg_into_interp_fun_upd_false[OF assms(1)] type_sym.distinct(5) val_give_fst_def wff_T)
  then have val_give_fst_D:
    "val_give_fst \<cdot> val D I (\<phi>((''x'', Tv) := false, 
                               (''y'', Tv) := y, 
                               (''g'', ooo) := val_give_fst)) T \<cdot>
                      val D I (\<phi>((''x'', Tv) := false, 
                               (''y'', Tv) := y, 
                               (''g'', ooo) := val_give_fst)) T
       \<in>: D Tv"
    using val_give_fst_simp[of
        "val D I (\<phi>((''x'', Tv) := false, 
                    (''y'', Tv) := y, 
                    (''g'', ooo) := val_give_fst)) T" 
        "val D I (\<phi>((''x'', Tv) := false, 
                     (''y'', Tv) := y, 
                     (''g'', ooo) := val_give_fst)) T" ]
    by auto

  have false_y_TV: "false \<in>: D Tv \<and> y \<in>: D Tv"
    using assms(1) assms(3) wf_frame_def wf_interp.simps by auto
  then have val_give_fst_in_D: "val_give_fst \<cdot> false \<cdot> y \<in>: D Tv"
    using val_give_fst_simp by auto

  have "true \<in>: D Tv"
    by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
  from this val_give_fst_in_D false_y_TV have "val_give_fst \<cdot> true \<cdot> true \<noteq> val_give_fst \<cdot> false \<cdot> y"
    using val_give_fst_simp true_neq_false by auto
  then have val_give_fst_not_false: 
    "val_give_fst \<cdot> val D I (\<phi>((''x'', Tv) := false, 
                             (''y'', Tv) := y, 
                             (''g'', ooo) := val_give_fst)) T
                  \<cdot> val D I (\<phi>((''x'', Tv) := false, 
                             (''y'', Tv) := y, 
                             (''g'', ooo) := val_give_fst)) T 
     \<noteq> val_give_fst \<cdot> false \<cdot> y"
    using asg_into_frame_fun_upd assms(1) assms(2) lemma_5401_c false_y_TV val_give_fst_fun by auto
  have Con_sym_subterm0TT_neq_Con_sym_subterm0xy: 
    "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<noteq> 
     val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]"
    using abstract_cong_specific[of
        val_give_fst
        "(D ooo)" 
        "(\<lambda>z. z \<cdot> val D I (\<phi>((''x'', Tv) := false, 
                           (''y'', Tv) := y, 
                           (''g'', ooo) := z)) T
                 \<cdot> val D I (\<phi>((''x'', Tv) := false, 
                            (''y'', Tv) := y, 
                            (''g'', ooo) := z)) T)" 
        "(D Tv)"
        "(\<lambda>z. z \<cdot> false \<cdot> y)"]
    using val_give_fst_fun val_give_fst_D val_give_fst_in_D val_give_fst_not_false by auto

  have "asg_into_frame (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) D"
    using asg_into_interp_fun_upd_false[OF assms(1)] general_model.simps[of D I] assms wff_Con_sym_subterm1
      asg_into_interp_fun_upd_true[OF assms(1)] by auto
  then have val_Con_sym_subterm1: "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>] = false"
    using Con_sym_subterm0TT_neq_Con_sym_subterm0xy lemma_5401_b_variant_3[OF assms(1)] 
    by auto

  have "y \<in>: D Tv"
    using general_model.simps lemma_5401_d[OF assms(1,2)] wff_F assms
    by (metis lemma_5401_c[OF assms(1,2)] wff_T) 
  moreover
  have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>] \<in>: D Tv"
    using asg_into_interp_fun_upd_false[OF assms(1)] general_model.simps[of D I] assms wff_Con_sym_subterm1 
      asg_into_interp_fun_upd_true[OF assms(1)] by auto
  moreover
  have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>] = false"
    using val_Con_sym_subterm1 by auto
  ultimately
  have val_y: "(val D I (\<phi>((''x'', Tv) := false)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]) \<cdot> y = false"
    by simp

  have 11: "val D I (\<phi>((''x'', Tv) := false)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<in>: D oo"
    using asg_into_interp_fun_upd_false[OF assms(1,2)] general_model.simps[of D I] assms
      wff_Con_sym_subterm2 by blast 
  moreover
  have "val D I (\<phi>((''x'', Tv) := false)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<cdot> y = false"
    using val_y by auto
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]\<^bold>]) \<cdot> false \<cdot> y = false"
    using false_y_TV by simp
  then show "(val D I \<phi> Con_sym) \<cdot> false \<cdot> y = false"
    unfolding Con_sym_def by auto
qed

(* Corresponds to Andrews' lemma 5401 e_3 *)
lemma lemma_5401_e_3:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Con_sym) \<cdot> x \<cdot> false = false"
proof -
  (* proof adapted from lemma_5401_e_2 *)
  define give_y :: trm where "give_y = (\<^bold>[\<^bold>\<lambda> ''y'':Tv. y\<^sub>o\<^bold>])"
  define give_snd :: trm where "give_snd = \<^bold>[\<^bold>\<lambda> ''x'':Tv. give_y\<^bold>]"
  define val_give_snd :: 's where "val_give_snd = val D I \<phi> give_snd"
  have wff_give_y: "wff oo give_y"
    unfolding give_y_def by auto

  have  "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> a \<in>: D Tv"
    by simp
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_y \<in>: D (type_of give_y)"
    using wff_give_y asg_into_frame_def assms(1) assms(2) by auto
  moreover
  have "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val D I (\<phi>((''x'', Tv) := a)) give_y \<cdot> b = b"
    unfolding give_y_def by auto
  ultimately
  have val_give_snd_simp: "\<And>a b. a \<in>: D Tv \<Longrightarrow> b \<in>: D Tv \<Longrightarrow> val_give_snd \<cdot> a \<cdot> b = b"
    unfolding val_give_snd_def give_snd_def by auto

  have wff_give_snd: "wff ooo give_snd"
    unfolding give_snd_def give_y_def by auto
  then have val_give_snd_in_D: "val_give_snd \<in>: D ooo"
    unfolding val_give_snd_def using assms
    by auto

  then have "val D I (\<phi>((''x'', Tv) := x, 
                   (''y'', Tv) := false, 
                   (''g'', ooo) := val_give_snd)) T \<in>: D Tv"
    by (smt Pair_inject wff_give_snd assms(1,2,3) 
        fun_upd_twist general_model.simps asg_into_interp_fun_upd[OF assms(1,2)] 
        asg_into_interp_fun_upd_false[OF assms(1)] asg_into_interp_fun_upd_true[OF assms(1)] 
        type_sym.distinct(5) val_give_snd_def wff_T)
  then have val_give_snd_app_in_D: 
    "val_give_snd \<cdot> val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', ooo) := val_give_snd)) T
                  \<cdot> val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', ooo) := val_give_snd)) T
     \<in>: D Tv"
    using val_give_snd_simp[of
        "val D I (\<phi>((''x'', Tv) := x, 
                    (''y'', Tv) := false, 
                    (''g'', ooo) := val_give_snd)) T" 
        "val D I (\<phi>((''x'', Tv) := x, 
                     (''y'', Tv) := false, 
                     (''g'', ooo) := val_give_snd)) T" ]
    by auto

  have false_and_x_in_D: "false \<in>: D Tv \<and> x \<in>: D Tv"
    using assms(1,3) wf_frame_def wf_interp.simps by auto
  then have val_give_snd_app_x_false_in_D: "val_give_snd \<cdot> x \<cdot> false \<in>: D Tv"
    using val_give_snd_simp by auto

  have "true \<in>: D Tv"
    by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
  then have "val_give_snd \<cdot> true \<cdot> true \<noteq> val_give_snd \<cdot> x \<cdot> false"
    using val_give_snd_simp true_neq_false val_give_snd_app_in_D false_and_x_in_D by auto
  then have
    "val_give_snd \<cdot> val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', ooo) := val_give_snd)) T
                  \<cdot> val D I (\<phi>((''x'', Tv) := x, 
                             (''y'', Tv) := false, 
                             (''g'', ooo) := val_give_snd)) T \<noteq>
     val_give_snd \<cdot> x \<cdot> false"
    using asg_into_frame_fun_upd assms(1) assms(2) lemma_5401_c false_and_x_in_D val_give_snd_in_D
    by auto
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<noteq> 
        val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) 
          \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]"
    using abstract_cong_specific[of 
        val_give_snd 
        "(D ooo)" 
        "(\<lambda>z. z \<cdot> val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false, (''g'', ooo) := z))
             T \<cdot> val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false, (''g'', ooo) := z)) T)" 
        "(D Tv)"
        "(\<lambda>z. z \<cdot> x \<cdot> false)"
        ]
    using val_give_snd_in_D val_give_snd_app_x_false_in_D val_give_snd_app_in_D by auto
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := false)) \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>] = false"
    using asg_into_frame_fun_upd assms(1,2) lemma_5401_b_variant_3 false_and_x_in_D by auto
  then have val_Con_sym_subterm2_false: "(val D I (\<phi>((''x'', Tv) := x)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]) \<cdot> false = false"
    using false_and_x_in_D by simp

  have "x \<in>: D Tv"
    by (simp add: false_and_x_in_D)
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<in>: D oo"
    by (metis assms(1,3) general_model.simps lemma_5401_c[OF assms(1,2)] 
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_false[OF assms(1,2)] 
        wff_Con_sym_subterm2 wff_T)
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>] \<cdot> false = false"
    using val_Con_sym_subterm2_false by auto
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[\<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> T \<^bold>\<cdot> T\<^bold>] \<^bold>=(Tv \<^bold>\<Leftarrow> ooo)\<^bold>= \<^bold>[\<^bold>\<lambda>''g'':ooo. g\<^sub>o\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o \<^bold>\<cdot> y\<^sub>o\<^bold>]\<^bold>]\<^bold>]\<^bold>]) \<cdot> x \<cdot> false = false"
    by auto
  then show "(val D I \<phi> Con_sym) \<cdot> x \<cdot> false = false"
    unfolding Con_sym_def by auto
qed

(* Corresponds to Andrews' lemma 5401 e *)
lemma lemma_5401_e_variant_1:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "y = true \<or> y = false"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Con_sym) \<cdot> x \<cdot> y = boolean (x = true \<and> y = true)"
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

lemma asg_into_interp_is_true_or_false:
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

lemma wff_Tv_is_true_or_false:
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

(* Corresponds to Andrews' lemma 5401 e *)
lemma lemma_5401_e_variant_2:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  assumes "wff Tv B"
  shows "(val D I \<phi> (A \<^bold>\<and> B)) = boolean (satisfies D I \<phi> A \<and> satisfies D I \<phi> B)"
  using assms wff_Tv_is_true_or_false[of \<phi> D I] lemma_5401_e_variant_1 unfolding Con_def by auto

(* Corresponds to Andrews' lemma 5401 f_1 *)
lemma lemma_5401_f_1:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Imp_sym) \<cdot> false \<cdot> y = true"
proof -
  define Imp_subterm2 :: trm where
    "Imp_subterm2 \<equiv> \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]"

  have val_Imp_subterm0_false: "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) (x\<^sub>o \<^bold>\<and> y\<^sub>o) = false"
    using assms asg_into_interp_fun_upd_false[OF assms(1)] asg_into_interp_fun_upd_true[OF assms(1)] 
      boolean_def lemma_5401_e_variant_2 by auto

  have "asg_into_frame (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) D"
    using assms(1, 2, 3) lemma_5401_c[OF assms(1)] asg_into_interp_fun_upd wff_T
      asg_into_interp_fun_upd_false by metis
  then have "val D I (\<phi>((''x'', Tv) := false, (''y'', Tv) := y)) \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] = true"
    using lemma_5401_b_variant_1[OF assms(1)] val_Imp_subterm0_false unfolding boolean_def by auto
  then have val_Imp_subterm2_true: "(val D I (\<phi>((''x'', Tv) := false)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]) \<cdot> y = true"
    using assms(1,3) wf_frame_def wf_interp.simps by auto 

  have "val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]\<^bold>] \<cdot> false \<cdot> y = true"
  proof -
    have "false \<in>: D Tv"
      by (metis asg_into_frame_def asg_into_interp_fun_upd_false assms(1) assms(2) fun_upd_same)
    then have "val D I (\<phi>((''x'', Tv) := false)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] = val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]\<^bold>] \<cdot> false"
      using asg_into_interp_fun_upd_false assms(1,2) Imp_subterm2_def[symmetric] wff_Imp_sym_subterm2_iff by force
    then show ?thesis
      by (metis val_Imp_subterm2_true)
  qed
  then show "(val D I \<phi> Imp_sym) \<cdot> false \<cdot> y = true"
    unfolding Imp_sym_def Imp_subterm2_def by auto
qed

(* Corresponds to Andrews' lemma 5401 f_2 *)
lemma lemma_5401_f_2:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "x = true \<or> x = false"
  shows "(val D I \<phi> Imp_sym) \<cdot> x \<cdot> true = true"
proof -
  have asg: "asg_into_frame (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) D"
    using assms(1,2,3) asg_into_interp_fun_upd_false asg_into_interp_fun_upd_true[OF assms(1)] by blast
  then have "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) (x\<^sub>o \<^bold>\<and> y\<^sub>o) = x"
    using lemma_5401_e_variant_2 assms unfolding boolean_def by auto
  then have val_Imp_subterm1_true: "val D I (\<phi>((''x'', Tv) := x, (''y'', Tv) := true)) \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] = true"
    using asg lemma_5401_b_variant_1[OF assms(1)] boolean_eq_true  by auto 

  have val_Imp_subterm2_true: "val D I (\<phi>((''x'', Tv) := x)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<cdot> true = true"
    using val_Imp_subterm1_true assms(1) wf_frame_def wf_interp.simps by auto 

  have "x \<in>: D Tv"
    by (metis asg_into_frame_def assms(1) assms(3) fun_upd_same asg_into_interp_fun_upd_false 
        asg_into_interp_fun_upd_true[OF assms(1,2)])
  moreover
  have "val D I (\<phi>((''x'', Tv) := x)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<in>: D oo"
    using wff_Imp_sym_subterm2
    by (metis assms(1,2,3) general_model.simps lemma_5401_c[OF assms(1,2)]
        asg_into_interp_fun_upd[OF assms(1,2)] asg_into_interp_fun_upd_false wff_T)
  ultimately
  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]\<^bold>]) \<cdot> x \<cdot> true = true"
    using val_Imp_subterm2_true by auto
  then show "(val D I \<phi> Imp_sym) \<cdot> x \<cdot> true = true"
    unfolding Imp_sym_def by auto
qed

(* Corresponds to Andrews' lemma 5401 f_3 *)
lemma lemma_5401_f_3:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "(val D I \<phi> Imp_sym) \<cdot> true \<cdot> false = false"
proof -
  have asg: "asg_into_frame (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) D"
    by (meson assms(1,2) asg_into_interp_fun_upd_false asg_into_interp_fun_upd_true)
  moreover
  have "false = true \<or> false = false"
    unfolding boolean_def by auto
  moreover
  have "boolean (true = true \<and> false = true) = false"
    unfolding boolean_def by auto
  ultimately
  have 3: "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) (x\<^sub>o \<^bold>\<and> y\<^sub>o) = false"
    using lemma_5401_e_variant_2 assms by auto
  then have Imp_subterm1_false: "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] = false"
    using subst lemma_5401_b_variant_1[OF assms(1)] asg boolean_def by auto

  have asdff: "wff Tv \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]"
    by auto

  have false_Tv: "false \<in>: D Tv"
    using assms(1) wf_frame_def wf_interp.simps by auto
  moreover
  have "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] \<in>: D Tv"
    by (simp add: Imp_subterm1_false false_Tv)
  moreover
  have "val D I (\<phi>((''x'', Tv) := true, (''y'', Tv) := false)) \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>] = false"
    using Imp_subterm1_false by auto
  ultimately 
  have Imp_subterm2_app_false: "val D I (\<phi>((''x'', Tv) := true)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<cdot> false = false"
    by auto

  have wff_Imp_sym_subterm2: "wff oo \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]"
    by auto

  have "(val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':Tv. \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>]\<^bold>]) \<cdot> true \<cdot> false = false"
  proof -
    have "true \<in>: D Tv"
      by (metis assms(1) assms(2) general_model.simps lemma_5401_c[OF assms(1,2)] wff_T)
    moreover
    have "val D I (\<phi>((''x'', Tv) := true)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<in>: D oo"
      using wff_Imp_sym_subterm2 
      by (metis assms(1) general_model.simps asg_into_interp_fun_upd_true[OF assms(1,2)])
    moreover
    have "val D I (\<phi>((''x'', Tv) := true)) \<^bold>[\<^bold>\<lambda> ''y'':Tv. \<^bold>[x\<^sub>o \<^bold>=Tv\<^bold>= (x\<^sub>o \<^bold>\<and> y\<^sub>o)\<^bold>]\<^bold>] \<cdot> false = false"
      using Imp_subterm2_app_false by auto
    ultimately
    show ?thesis
      by auto
  qed
  then show "(val D I \<phi> Imp_sym) \<cdot> true \<cdot> false = false"
    unfolding Imp_sym_def by auto
qed

(* Corresponds to Andrews' lemma 5401 f *)
lemma lemma_5401_f_variant_1:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "x = true \<or> x = false"
  assumes "y = true \<or> y = false"
  shows "(val D I \<phi> Imp_sym) \<cdot> x \<cdot> y = boolean (x = true \<longrightarrow> y = true)"
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

(* Corresponds to Andrews' lemma 5401 f *)
lemma lemma_5401_f_variant_2:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  assumes "wff Tv B"
  shows "(val D I \<phi> (A \<^bold>\<longrightarrow> B)) = boolean (satisfies D I \<phi> A \<longrightarrow> satisfies D I \<phi> B)"
  using assms unfolding Imp_def
  by (simp add: lemma_5401_f_variant_1 wff_Tv_is_true_or_false)

(* Corresponds to Andrews' lemma 5401 g *)
lemma lemma_5401_g:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff Tv A"
  shows "satisfies D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] \<longleftrightarrow> 
        (\<forall>\<psi>. asg_into_interp \<psi> D I \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A)"
proof -
  have "wff (Tv \<^bold>\<Leftarrow> \<alpha>) \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>]"
    by auto
  then have PI_subterm_in_D: "val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>] \<in>: D (Tv \<^bold>\<Leftarrow> \<alpha>)"
    using assms(1,2) general_model.simps by blast

  have "wff (Tv \<^bold>\<Leftarrow> \<alpha>) (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>])"
    using assms by auto
  moreover
  have "\<forall>\<phi>. asg_into_frame \<phi> D \<longrightarrow> (\<forall>A \<alpha>. wff \<alpha> A \<longrightarrow> val D I \<phi> A \<in>: D \<alpha>)"
    using assms(1) by auto
  then have "\<forall>t cs. val D I \<phi> \<^bold>[\<^bold>\<lambda>cs:t. A\<^bold>] \<in>: D (Tv \<^bold>\<Leftarrow> t)"
    using wff_Abs assms(1,2,3) by presburger
  then have "abstract (D \<alpha>) (D Tv) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) A) \<in>: D (Tv \<^bold>\<Leftarrow> \<alpha>)"
    using assms(3) by simp
  ultimately
  have val_lambda_A: "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]) \<in>: D (Tv \<^bold>\<Leftarrow> \<alpha>)"
    using assms by auto

  have true_and_A_in_D: "\<forall>z. z \<in>: D \<alpha> \<longrightarrow> true \<in>: D Tv \<and> val D I (\<phi>((x, \<alpha>) := z)) A \<in>: D Tv"
    by (metis assms(1,2,3) general_model.simps lemma_5401_c[OF assms(1,2)] asg_into_frame_fun_upd wff_T)

  have "satisfies D I \<phi> \<^bold>[\<^bold>\<forall> x: \<alpha>. A\<^bold>] \<longleftrightarrow> val D I \<phi> \<^bold>[\<^bold>\<forall>x: \<alpha>. A\<^bold>] = true"
    by auto
  moreover have "... \<longleftrightarrow> val D I \<phi> (PI \<alpha>) \<cdot> val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] = true"
    unfolding Forall_def by simp
  moreover have "... \<longleftrightarrow> I ''Q'' ((Tv \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<Leftarrow> (Tv \<^bold>\<Leftarrow> \<alpha>))
                            \<cdot> val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>] \<cdot> val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] =
                         true"
    unfolding PI_def by simp
  moreover have "... \<longleftrightarrow> (iden (D (Tv \<^bold>\<Leftarrow> \<alpha>))) \<cdot> val D I \<phi> \<^bold>[\<^bold>\<lambda> ''x'':\<alpha>. T\<^bold>] \<cdot> val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>] =
                         true"
    unfolding PI_def using wf_interp.simps assms by simp
  moreover have "... \<longleftrightarrow> val D I \<phi> \<^bold>[\<^bold>\<lambda>''x'':\<alpha>. T\<^bold>] = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
    using PI_subterm_in_D val_lambda_A apply_id_true by auto
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. val D I (\<phi>((''x'', \<alpha>) := z)) T) = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
    using assms wff_T by simp
  moreover have "... \<longleftrightarrow> abstract (D \<alpha>) (D Tv) (\<lambda>z. true) = val D I \<phi> \<^bold>[\<^bold>\<lambda>x:\<alpha>. A\<^bold>]"
  proof -
    have "\<forall>x. x \<in>: D \<alpha> \<longrightarrow> val D I (\<phi>((''x'', \<alpha>) := x)) T \<in>: D Tv \<and> true \<in>: D Tv"
      using true_and_A_in_D assms(1,2)  asg_into_frame_fun_upd by auto
    moreover
    have "\<forall>x. x \<in>: D \<alpha> \<longrightarrow> val D I (\<phi>((''x'', \<alpha>) := x)) T \<in>: D Tv \<and> satisfies D I (\<phi>((''x'', \<alpha>) := x)) T"
      using true_and_A_in_D assms(1) assms(2) lemma_5401_c[OF assms(1)] asg_into_frame_fun_upd by auto
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
      using abstract_iff_extensional by auto
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

(* Corresponds to Andrews' lemma 5401 g *)
theorem lemma_5401_g_variant_1:
  assumes "asg_into_interp \<phi> D I"
  assumes "general_model D I"
  assumes "wff Tv A"
  shows "val D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] =
        boolean (\<forall>\<psi>. asg_into_interp \<psi> D I \<longrightarrow> agree_off_asg \<psi> \<phi> x \<alpha> \<longrightarrow> satisfies D I \<psi> A)"
proof -
  have "val D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] = (if satisfies D I \<phi> \<^bold>[\<^bold>\<forall>x:\<alpha>. A\<^bold>] then true else false)"
    using assms wff_Forall wff_Tv_is_true_or_false by metis
  then show ?thesis
    using assms lemma_5401_g[symmetric] unfolding boolean_def by auto
qed


section \<open>Soundness\<close>

lemma fun_sym_asg_to_funspace:
  assumes "asg_into_frame \<phi> D"
  assumes "general_model D I"
  shows "\<phi> (f, \<alpha> \<^bold>\<Leftarrow> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
proof -
  have "wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) (Var f (\<alpha> \<^bold>\<Leftarrow> \<beta>))"
    by auto
  then have "val D I \<phi> (Var f (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<in>: D (\<alpha> \<^bold>\<Leftarrow> \<beta>)"
    using assms
    using general_model.simps by blast
  then show "\<phi> (f, \<alpha> \<^bold>\<Leftarrow> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
    using assms unfolding general_model.simps wf_interp.simps wf_frame_def
    by (simp add: subs_def)
qed

lemma fun_sym_interp_to_funspace:
  assumes "asg_into_frame \<phi> D"
  assumes "general_model D I"
  shows "I f (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
proof -
  have "wff (\<alpha> \<^bold>\<Leftarrow> \<beta>) (Cst f (\<alpha> \<^bold>\<Leftarrow> \<beta>))"
    by auto
  then have "val D I \<phi> (Cst f (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<in>: D (\<alpha> \<^bold>\<Leftarrow> \<beta>)"
    using assms general_model.simps by blast
  then show "I f (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<in>: funspace (D \<beta>) (D \<alpha>)"
    using assms subs_def unfolding general_model.simps wf_interp.simps wf_frame_def by auto
qed

(* Corresponds to Andrews' theorem 5402 a for rule R *)
theorem theorem_5402_a_rule_R:
  assumes A_eql_B: "valid_general (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>])"
  assumes "valid_general C"
  assumes "rule_R C (\<^bold>[A \<^bold>=\<alpha>\<^bold>= B\<^bold>]) C'"
  assumes "wff \<alpha> A"
  assumes "wff \<alpha> B"
  assumes "wff \<beta> C"
  shows "valid_general C'"
  unfolding valid_general_def 
proof (rule allI, rule allI, rule impI)
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
    define \<alpha>' where "\<alpha>' = type_of C"
    define \<beta>' where "\<beta>' = type_of D'"
    show ?case
    proof (rule, rule)
      fix \<phi>
      assume asg: "asg_into_frame \<phi> D"
      have \<alpha>': "\<alpha>' = \<beta> \<^bold>\<Leftarrow> \<beta>'"
        using trm.distinct(11) trm.distinct(3,7) trm.inject(3) replace_App_left.prems(4) wff.simps
        by (metis \<alpha>'_def \<beta>'_def wff_App_type_of)
      from asg have "wff \<alpha>' C"
        using replace_App_left trm.distinct(3,7,11) trm.inject(3) wff.simps
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
      have \<alpha>': "\<alpha>' = \<beta> \<^bold>\<Leftarrow> \<beta>'"
        using trm.distinct(11) trm.distinct(3) trm.distinct(7) trm.inject(3) 
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
        by (metis trm.distinct(11) trm.distinct(5) trm.distinct(9) trm.inject(4) 
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

theorem Fun_Tv_Tv_frame_subs_funspace:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "D oo \<subseteq>: funspace (boolset) (boolset)"
  by (metis assms(1) general_model.elims(2) wf_frame_def wf_interp.simps)

(* Corresponds to Andrews' theorem 5402 a for axiom 1 *)
theorem theorem_5402_a_axiom_1_variant:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> axiom_1"
proof (cases "(\<phi> (''g'',oo)) \<cdot> true = true \<and> (\<phi> (''g'',oo)) \<cdot> false = true")
  case True
  then have val: "val D I \<phi> ((g\<^sub>o\<^sub>o \<^bold>\<cdot> T) \<^bold>\<and> (g\<^sub>o\<^sub>o \<^bold>\<cdot> F)) = true"
    using assms lemma_5401_e_variant_2
    by (auto simp add: boolean_eq_true lemma_5401_c[OF assms(1,2)] lemma_5401_d[OF assms(1,2)])
  have "\<forall>\<psi>. asg_into_frame \<psi> D \<longrightarrow> 
            agree_off_asg \<psi> \<phi> ''x'' Tv \<longrightarrow> 
            satisfies D I \<psi> (g\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o)"
  proof (rule; rule; rule)
    fix \<psi>
    assume \<psi>: "asg_into_frame \<psi> D" "agree_off_asg \<psi> \<phi> ''x'' Tv"
    then have "\<psi> (''x'', Tv) = true \<or> \<psi> (''x'', Tv) = false"
      using asg_into_interp_is_true_or_false assms
      by auto
    then show " satisfies D I \<psi> (g\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o)"
      using True \<psi> unfolding agree_off_asg_def by auto
  qed
  then have  "val D I \<phi> (\<^bold>[\<^bold>\<forall>''x'':Tv. (g\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o)\<^bold>]) = true"
    using lemma_5401_g using assms by auto
  then show ?thesis
    unfolding axiom_1_def
    using lemma_5401_b[OF assms(1,2)] val by auto
next
  case False
  have "\<phi> (''g'', oo) \<in>: D oo"
    using assms
    by (simp add: asg_into_frame_def) 
  then have 0: "\<phi> (''g'', oo) \<in>: funspace (D Tv) (D Tv)"
    using assms(1) assms(2) fun_sym_asg_to_funspace by blast

  from False have "(\<phi> (''g'', oo) \<cdot> true \<noteq> true \<or> \<phi> (''g'', oo) \<cdot> false \<noteq> true)"
    by auto
  then have "\<exists>z. \<phi> (''g'', oo) \<cdot> z = false \<and> z \<in>: D Tv"
  proof
    assume a: "\<phi> (''g'', oo) \<cdot> true \<noteq> true"
    have "\<phi> (''g'', oo) \<cdot> true \<in>: boolset"
      by (metis "0" apply_abstract assms(1) boolset_def general_model.elims(2) in_funspace_abstract 
          mem_two true_def wf_frame_def wf_interp.simps)
    from this a have "\<phi> (''g'', oo) \<cdot> true = false \<and> true \<in>: D Tv"
      using assms(1) wf_frame_def wf_interp.simps by auto  
    then show "\<exists>z. \<phi> (''g'', oo) \<cdot> z = false \<and> z \<in>: D Tv"
      by auto
  next
    assume a: "\<phi> (''g'', oo) \<cdot> false \<noteq> true"
    have "\<phi> (''g'', oo) \<cdot> false \<in>: boolset"
      by (metis "0" apply_abstract assms(1) boolset_def general_model.elims(2) in_funspace_abstract 
          mem_two false_def wf_frame_def wf_interp.simps)
    from this a have "\<phi> (''g'', oo) \<cdot> false = false \<and> false \<in>: D Tv" 
      using assms(1) wf_frame_def wf_interp.simps by auto
    then show "\<exists>z. \<phi> (''g'', oo) \<cdot> z = false \<and> z \<in>: D Tv"
      by auto
  qed
  then obtain z where z_p: "\<phi> (''g'', oo) \<cdot> z = false \<and> z \<in>: D Tv"
    by auto
  have "boolean (satisfies D I \<phi> (g\<^sub>o\<^sub>o \<^bold>\<cdot> T)
          \<and> satisfies D I \<phi> (g\<^sub>o\<^sub>o \<^bold>\<cdot> F)) = false"
    using False
    by (smt boolean_def val.simps(1) val.simps(3) lemma_5401_c[OF assms(1,2)] 
        lemma_5401_d[OF assms(1,2)])
  then have 1: "val D I \<phi> ( 
         (g\<^sub>o\<^sub>o \<^bold>\<cdot> T) \<^bold>\<and>
         (g\<^sub>o\<^sub>o \<^bold>\<cdot> F)) = false"
    using lemma_5401_e_variant_2 assms by auto
  have 3: "asg_into_frame (\<phi>((''x'', Tv) := z)) D \<and>
    agree_off_asg (\<phi>((''x'', Tv) := z)) \<phi> ''x'' Tv \<and>
    \<phi> (''g'', oo) \<cdot> (\<phi>((''x'', Tv) := z)) (''x'', Tv) \<noteq> true"
    using z_p Pair_inject agree_off_asg_def2 asg_into_frame_fun_upd assms(2) true_neq_false by fastforce
  then have 2: "val D I \<phi> (\<^bold>[\<^bold>\<forall>''x'':Tv. (g\<^sub>o\<^sub>o \<^bold>\<cdot> x\<^sub>o)\<^bold>]) = false"
    using  lemma_5401_g_variant_1 assms boolean_def by auto
  then show ?thesis
    unfolding axiom_1_def using 1 2 lemma_5401_b_variant_2[OF assms(1,2)] by auto 
qed

(* Corresponds to Andrews' theorem 5402 a for axiom 1 *)
theorem theorem_5402_a_axiom_1: "valid_general axiom_1"
  using theorem_5402_a_axiom_1_variant unfolding valid_general_def valid_in_model_def by auto

(* Corresponds to Andrews' theorem 5402 a for axiom 2 *)
theorem theorem_5402_a_axiom_2_variant:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_2 \<alpha>)"
proof (cases "\<phi>(''x'',\<alpha>) = \<phi>(''y'',\<alpha>)")
  case True
  have "val D I \<phi> ((Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<cdot> (Var ''x'' \<alpha>)) = 
           (\<phi> (''h'', (Tv \<^bold>\<Leftarrow> \<alpha>))) \<cdot> \<phi> (''x'', \<alpha>)"
    using assms by auto
  also
  have "... = \<phi> (''h'', (Tv \<^bold>\<Leftarrow> \<alpha>)) \<cdot> \<phi> (''y'', \<alpha>)"
    using True by auto
  also
  have "... = val D I \<phi> ((Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>)) \<^bold>\<cdot> (Var ''y'' \<alpha>))"
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
         \<^bold>[(Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>) \<^bold>\<cdot> Var ''x'' \<alpha>) \<^bold>=Tv\<^bold>= Var ''h'' (Tv \<^bold>\<Leftarrow> \<alpha>) \<^bold>\<cdot> Var ''y'' \<alpha>\<^bold>]) =
       true"
    using boolean_eq_true lemma_5401_b by auto
  then
  show ?thesis
    using assms lemma_5401_f_variant_2 unfolding axiom_2_def by auto
qed                                   

(* Corresponds to Andrews' theorem 5402 a for axiom 2 *)
theorem theorem_5402_a_axiom_2: "valid_general (axiom_2 \<alpha>)"
  using theorem_5402_a_axiom_2_variant unfolding valid_general_def valid_in_model_def by auto

(* Corresponds to Andrews' theorem 5402 a for axiom 3 *)
theorem theorem_5402_a_axiom_3_variant:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_3 \<alpha> \<beta>)"
proof (cases "\<phi> (''f'',\<alpha> \<^bold>\<Leftarrow> \<beta>) = \<phi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>)")
  case True
  {
    fix \<psi>
    assume agree: "agree_off_asg \<psi> \<phi> ''x'' \<beta>"
    assume asg: "asg_into_interp \<psi> D I"
    have "val D I \<psi> ((Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) = \<psi> (''f'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
      by auto
    also
    have "... = \<phi> (''f'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
      using agree by auto
    also
    have "... = \<phi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
      using True by auto
    also
    have "... = \<psi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
      using agree by auto
    also
    have "... = val D I \<psi> ((Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))"
      by auto
    finally
    have 
      "val D I \<psi>
            (\<^bold>[((Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) \<^bold>=\<alpha>\<^bold>= ((Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))\<^bold>]) 
       = true"
      using lemma_5401_b_variant_1[OF assms(1)] assms agree asg boolean_eq_true by auto
  }
  then have "satisfies D I \<phi>
        (\<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[(Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>) \<^bold>=\<alpha>\<^bold>= Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>\<^bold>]\<^bold>])"
    using assms lemma_5401_g by force
  moreover
  have "satisfies D I \<phi> \<^bold>[Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>=\<alpha> \<^bold>\<Leftarrow> \<beta>\<^bold>= Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)\<^bold>]"
    using True assms using lemma_5401_b_variant_2 wff_Var by auto
  ultimately
  show ?thesis
    using axiom_3_def lemma_5401_b_variant_2 assms by auto
next
  case False
  then have "\<exists>z. z \<in>: D \<beta> \<and> \<phi> (''f'', \<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z \<noteq> \<phi> (''g'', \<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z"
    using funspace_difference_witness[of "\<phi> (''f'', \<alpha> \<^bold>\<Leftarrow> \<beta>)" "D \<beta>" "D \<alpha>" "\<phi> (''g'', \<alpha> \<^bold>\<Leftarrow> \<beta>)"]
      assms(1,2) fun_sym_asg_to_funspace by blast
  then obtain z where
    z\<beta>: "z \<in>: D \<beta>" and
    z_neq: "\<phi> (''f'', \<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z \<noteq> \<phi> (''g'', \<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z"
    by auto
  define \<psi> where "\<psi> = (\<phi>((''x'',\<beta>):= z))"
  have agree: "agree_off_asg \<psi> \<phi> ''x'' \<beta>"
    using \<psi>_def agree_off_asg_def2 by blast
  have asg: "asg_into_interp \<psi> D I"
    using z\<beta> \<psi>_def asg_into_frame_fun_upd assms(2) by blast
  have "val D I \<psi> ((Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) = \<psi> (''f'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
    by auto
  moreover
  have "... = \<phi> (''f'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z"
    by (simp add: \<psi>_def)
  moreover
  have "... \<noteq> \<phi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z"
    using False z_neq by blast
  moreover
  have "\<phi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> z = \<psi> (''g'',\<alpha> \<^bold>\<Leftarrow> \<beta>) \<cdot> \<psi> (''x'', \<beta>)"
    by (simp add: \<psi>_def)
  moreover
  have "... = val D I \<psi> ((Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))"
    by auto
  ultimately
  have 
    "val D I \<psi>
            (\<^bold>[((Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>)) \<^bold>=\<alpha>\<^bold>= ((Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)) \<^bold>\<cdot> (Var ''x'' \<beta>))\<^bold>]) 
       = false"
    by (metis asg assms(1) lemma_5401_b_variant_3 wff_App wff_Var)
  have "val D I \<phi>
        (\<^bold>[\<^bold>\<forall>''x'':\<beta>. \<^bold>[(Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>) \<^bold>=\<alpha>\<^bold>= Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>\<^bold>]\<^bold>]) = false"
    by (smt (verit) \<open>val D I \<psi> \<^bold>[(Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>) \<^bold>=\<alpha>\<^bold>= Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>\<cdot> Var ''x'' \<beta>\<^bold>] = false\<close> 
        agree asg assms(1,2) lemma_5401_g wff_App wff_Eql wff_Forall wff_Tv_is_true_or_false wff_Var)
  moreover
  have "val D I \<phi> \<^bold>[Var ''f'' (\<alpha> \<^bold>\<Leftarrow> \<beta>) \<^bold>=\<alpha> \<^bold>\<Leftarrow> \<beta>\<^bold>= Var ''g'' (\<alpha> \<^bold>\<Leftarrow> \<beta>)\<^bold>] = false"
    using False assms(1,2) lemma_5401_b_variant_3 wff_Var by auto
  ultimately show ?thesis
    using assms(1,2) axiom_3_def lemma_5401_b by auto
qed

(* Corresponds to Andrews' theorem 5402 a for axiom 3 *)
theorem theorem_5402_a_axiom_3: "valid_general (axiom_3 \<alpha> \<beta>)"
  using theorem_5402_a_axiom_3_variant unfolding valid_general_def valid_in_model_def by auto

(* Corresponds to Andrews' theorem 5402 a for axiom 4_1 with a constant *)
theorem theorem_5402_a_axiom_4_1_variant_cst:
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

(* Corresponds to Andrews' theorem 5402 a for axiom 4_1 *)
theorem theorem_5402_a_axiom_4_1_variant_var:
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

(* Corresponds to Andrews' theorem 5402 a for axiom 4_1 *)
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

(* Corresponds to Andrews' theorem 5402 a for axiom 4_2 *)
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

(* Corresponds to Andrews' theorem 5402 a for axiom 4_3 *)
theorem theorem_5402_a_axiom_4_3: 
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  assumes "wff \<alpha> A"
  assumes "wff (\<beta> \<^bold>\<Leftarrow> \<gamma>) B"
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
  have "... = (val D I ?\<psi> B) \<cdot> val D I ?\<psi> C"
    by simp
  moreover
  have "... = (val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A)) \<cdot> val D I \<phi> (App \<^bold>[\<^bold>\<lambda>x :\<alpha>. C\<^bold>] A)"
    by (metis assms(3) assms(4) assms(5) lemma_5401_a[OF assms(1,2)])
  moreover
  have "... = val D I \<phi> (RHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A))"
    unfolding axiom_4_3_def by auto
  ultimately
  have "val D I \<phi> (LHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A)) = val D I \<phi> (RHS (axiom_4_3 x \<alpha> B \<beta> \<gamma> C A))"
    by auto
  then have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B \<^bold>\<cdot> C\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))"
    unfolding axiom_4_3_def by auto
  moreover
  have "wff \<beta> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B \<^bold>\<cdot> C\<^bold>] \<^bold>\<cdot> A)"
    using assms by auto
  moreover
  have "wff \<beta> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A \<^bold>\<cdot> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. C\<^bold>] \<^bold>\<cdot> A))"
    using assms by auto
  ultimately
  show ?thesis
    unfolding axiom_4_3_def using lemma_5401_b_variant_2[OF assms(1,2)] by auto
qed

lemma lemma_to_help_with_theorem_5402_a_axiom_4_4:
  assumes lambda_eql_lambda_lambda: 
    "\<And>z. z \<in>: D \<gamma> \<Longrightarrow> val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>] \<cdot> z = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>] \<cdot> z" 
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
    then have val_lambda_B: "val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>] \<cdot> e = val D I (\<psi>((y, \<gamma>) := e)) B"
      using e_in_D by auto
    have
      "val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>] \<cdot> e = 
       abstract (D \<alpha>) (D (type_of B))
         (\<lambda>z. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := z)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := e)) A"
      using apply_abstract e_in_D asg_into_frame_fun_upd assms(3,4,6,7) by auto
    then have "val D I (\<psi>((y, \<gamma>) := e)) B =
        abstract (D \<alpha>) (D (type_of B))
         (\<lambda>z. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := z)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := e)) A" 
      using val_lambda_B lambda_eql_lambda_lambda e_in_D by metis
  }
  note val_eql_abstract = this

  have 
    "\<forall>e. e \<in>: D \<gamma> \<longrightarrow>
            val D I (\<psi>((y, \<gamma>) := e)) B \<in>: D (type_of B) \<and>
            val D I (\<psi>((y, \<gamma>) := e)) B =
            abstract (D \<alpha>) (D (type_of B))
              (\<lambda>za. val D I (\<phi>((y, \<gamma>) := e, (x, \<alpha>) := za)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := e)) A"
    using asg_into_frame_fun_upd assms(3,4,6,7) \<psi>_eql val_eql_abstract by auto
  then have 
    "abstract (D \<gamma>) (D (type_of B)) (\<lambda>z. val D I (\<psi>((y, \<gamma>) := z)) B) =
     abstract (D \<gamma>) (D (type_of B))
       (\<lambda>z. abstract (D \<alpha>) (D (type_of B))
         (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := z)) A)"
    by (rule abstract_extensional)
  then show ?thesis 
    by auto
qed

(* Corresponds to Andrews' theorem 5402 a for axiom 4_4 *)
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
  have fr: "(y, \<gamma>) \<notin> vars A"
    using assms(3) axiom_4_4_side_condition_def by blast
  {
    fix z
    assume z_in_D: "z \<in>: D \<gamma>"
    define \<phi>' where "\<phi>' = \<phi>((y,\<gamma>) := z)"
    have "asg_into_frame \<phi>' D"
      using assms z_in_D unfolding asg_into_frame_def \<phi>'_def by auto
    moreover
    have "\<forall>(x, \<alpha>)\<in>vars A. agree_on_asg \<phi> \<phi>' x \<alpha>"
      using fr unfolding \<phi>'_def by auto
    ultimately
    have "val D I \<phi> A = val D I \<phi>' A"
      using prop_5400[OF assms(1), of _ _ \<alpha>] assms(2) assms(4) frees_subset_vars by blast
    then have Az: "\<phi>'((x,\<alpha>):=(val D I \<phi>' A)) = \<psi>((y,\<gamma>):=z)"
      using assms(3) unfolding axiom_4_4_side_condition_def
      by (simp add: fun_upd_twist \<phi>'_def \<psi>_def) 
    then have "abstract (D \<gamma>) (D (type_of B)) (\<lambda>z. val D I (\<psi>((y, \<gamma>) := z)) B) \<cdot> z = 
               val D I (\<psi>((y, \<gamma>) := z)) B"
      using apply_abstract_matchable assms(1,2,4,5) type_of asg_into_frame_fun_upd 
        general_model.elims(2) z_in_D by (metis \<phi>'_def)
    then have "(val D I \<psi> ?E) \<cdot> z = (val D I (\<psi>((y,\<gamma>):=z)) B)"
      by auto
    moreover
    have "... = val D I \<phi>' (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A)"
      using assms(1,2,4,5) asg_into_frame_fun_upd lemma_5401_a z_in_D
      by (metis Az \<phi>'_def) 
    moreover
    have "... = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>] \<cdot> z"
    proof -
      have valA: "val D I \<phi>' A \<in>: D \<alpha>"
        using \<phi>'_def asg_into_frame_fun_upd z_in_D assms by simp
      have valB: "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B \<in>: D (type_of B)" 
        using asg_into_frame_fun_upd z_in_D assms by (simp add: Az \<psi>_def) 
      have valA': "val D I (\<phi>((y, \<gamma>) := z)) A \<in>: D \<alpha>"
        using z_in_D assms asg_into_frame_fun_upd valA unfolding \<psi>_def \<phi>'_def 
        by blast
      have valB':
        "val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := val D I (\<phi>((y, \<gamma>) := z)) A)) B 
         \<in>: D (type_of B)"
        using asg_into_frame_fun_upd z_in_D assms valB \<phi>'_def by blast 
      have
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := val D I (\<phi>((y, \<gamma>) := z)) A)) B"
        unfolding \<psi>_def \<phi>'_def by (metis apply_abstract asg_into_frame_fun_upd)
      then have valB_eql_abs: 
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         abstract (D \<alpha>) (D (type_of B))
           (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := z)) A"
        using valA' valB' by auto
      then have "abstract (D \<alpha>) (D (type_of B))
              (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := z)) A 
            \<in>: D (type_of B)"
        using valB assms z_in_D by auto
      then have 
        "val D I (\<phi>'((x, \<alpha>) := val D I \<phi>' A)) B =
         abstract (D \<gamma>) (D (type_of B))
           (\<lambda>z. abstract (D \<alpha>) (D (type_of B))
             (\<lambda>za. val D I (\<phi>((y, \<gamma>) := z, (x, \<alpha>) := za)) B) \<cdot> val D I (\<phi>((y, \<gamma>) := z)) A) \<cdot> z"
        using z_in_D valB_eql_abs by auto
      then show "val D I \<phi>' (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>] \<cdot> z"
        using valA valB by auto
    qed
    ultimately
    have "val D I \<psi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>] \<cdot> z = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>] \<cdot> z"
      by simp
  }
  note lambda_eql_lambda_lambda = this
  have equal_funs: "val D I \<psi> ?E = val D I \<phi> (\<^bold>[\<^bold>\<lambda>y:\<gamma>. (\<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>]) \<^bold>\<cdot> A\<^bold>])"
    using lambda_eql_lambda_lambda \<psi>_def assms lemma_to_help_with_theorem_5402_a_axiom_4_4 by metis
  have "val D I \<phi> (\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) = val D I \<phi> \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]"
    using equal_funs by (metis \<psi>_def assms(1,2,4,5) lemma_5401_a wff_Abs) 
  then have "satisfies D I \<phi> \<^bold>[(\<^bold>[\<^bold>\<lambda>x:\<alpha>. \<^bold>[\<^bold>\<lambda>y:\<gamma>. B\<^bold>]\<^bold>] \<^bold>\<cdot> A) \<^bold>=\<delta> \<^bold>\<Leftarrow> \<gamma>\<^bold>= \<^bold>[\<^bold>\<lambda>y:\<gamma>. \<^bold>[\<^bold>\<lambda>x:\<alpha>. B\<^bold>] \<^bold>\<cdot> A\<^bold>]\<^bold>]"
    using lemma_5401_b[OF assms(1,2)] assms by auto
  then show ?thesis
    unfolding axiom_4_4_def .
qed

(* Corresponds to Andrews' theorem 5402 a for axiom 4_5 *)
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
    have "\<forall>t cs. val D I \<phi> \<^bold>[\<^bold>\<lambda>cs:t. B\<^bold>] \<in>: D (\<delta> \<^bold>\<Leftarrow> t)"
      using val asg wffB wff_Abs by blast
    then have "abstract (D \<alpha>) (D (\<delta> \<^bold>\<Leftarrow> \<alpha>)) 
                 (\<lambda>u. abstract (D \<alpha>) (D \<delta>) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) B)) \<cdot> val D I \<phi> A =
               abstract (D \<alpha>) (D \<delta>) (\<lambda>u. val D I (\<phi>((x, \<alpha>) := u)) B)"
      using valA wffB by simp
  }
  note abstract_eql = this

  have "val D I \<psi> ?E = val D I \<phi> ?E"
    using prop_5400[OF assms(1), of _ _ "\<delta> \<^bold>\<Leftarrow> \<alpha>"] \<psi>_def assms(2) by auto
  then show ?thesis
    unfolding axiom_4_5_def using lemma_5401_b[OF assms(1,2)] assms abstract_eql by auto
qed

(* Corresponds to Andrews' theorem 5402 a for axiom 5 *)
theorem theorem_5402_a_axiom_5:
  assumes "general_model D I"
  assumes "asg_into_interp \<phi> D I"
  shows "satisfies D I \<phi> (axiom_5)"
proof -
  have iden_eql: "iden (D Ind) \<cdot> I ''y'' Ind = one_elem_fun (I ''y'' Ind) (D Ind)"
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

  have "val D I \<phi> (\<^bold>\<iota> \<^bold>\<cdot> ((\<^bold>Q (Tv \<^bold>\<Leftarrow> Ind \<^bold>\<Leftarrow> Ind)) \<^bold>\<cdot> y\<^sub>i)) = 
          val D I \<phi> \<^bold>\<iota> \<cdot> val D I \<phi> ((\<^bold>Q (Tv \<^bold>\<Leftarrow> Ind \<^bold>\<Leftarrow> Ind)) \<^bold>\<cdot> y\<^sub>i)"
    by auto
  moreover
  have "... = val D I \<phi> y\<^sub>i"
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
    by (smt replacement_preserves_type rule_R.cases wff_Eql_iff)
qed

(* Corresponds to Andrews' theorem 5402 a *)
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

(* Corresponds to Andrews' theorem 5402 a *)
theorem theorem_5402_a_standard:
  assumes "theorem A"
  shows "valid_standard A"
  using theorem_5402_a_general assms standard_model_is_general_model valid_general_def 
    valid_standard_def by blast

end

end
