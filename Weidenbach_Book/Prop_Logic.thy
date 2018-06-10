theory Prop_Logic
imports Main
begin

chapter \<open>Normalisation\<close>

text \<open>We define here the normalisation from formula towards conjunctive and disjunctive normal form,
  including normalisation towards multiset of multisets to represent CNF.\<close>

section \<open>Logics\<close>

text \<open>In this section we define the syntax of the formula and an abstraction over it to have simpler
  proofs. After that we define some properties like subformula and rewriting.\<close>

subsection \<open>Definition and Abstraction\<close>

text \<open>The propositional logic is defined inductively. The type parameter is the type of the
  variables. \<close>
datatype 'v propo =
  FT | FF | FVar "'v" | FNot "'v propo" | FAnd "'v propo" "'v propo" | FOr "'v propo" "'v propo"
  | FImp "'v propo" "'v propo" | FEq "'v propo" "'v propo"

text \<open>We do not define any notation for the formula, to distinguish properly between the formulas
  and Isabelle's logic.\<close>


text \<open>To ease the proofs, we will write the the formula on a homogeneous manner, namely a connecting
  argument and a list of arguments.\<close>
datatype 'v connective = CT | CF | CVar "'v" | CNot | CAnd | COr | CImp | CEq

abbreviation "nullary_connective \<equiv> {CF} \<union> {CT} \<union> {CVar x | x. True}"
definition "binary_connectives \<equiv> {CAnd, COr, CImp, CEq}"


text \<open>We define our own induction principal: instead of distinguishing every constructor, we group
  them by arity.\<close>

lemma propo_induct_arity[case_names nullary unary binary]:
  fixes \<phi> \<psi> :: "'v propo"
  assumes nullary: "\<And>\<phi> x. \<phi> = FF \<or> \<phi> = FT \<or> \<phi> = FVar x \<Longrightarrow> P \<phi>"
  and unary: "\<And>\<psi>. P \<psi> \<Longrightarrow> P (FNot \<psi>)"
  and binary: "\<And>\<phi> \<psi>1 \<psi>2. P \<psi>1 \<Longrightarrow> P \<psi>2 \<Longrightarrow> \<phi> = FAnd \<psi>1 \<psi>2 \<or> \<phi> = FOr \<psi>1 \<psi>2 \<or> \<phi> = FImp \<psi>1 \<psi>2
    \<or> \<phi> = FEq \<psi>1 \<psi>2 \<Longrightarrow> P \<phi>"
  shows "P \<psi>"
  apply (induct rule: propo.induct)
  using assms by metis+

text \<open>The function @{term conn} is the interpretation of our representation (connective and list of
  arguments). We define any thing that has no sense to be false\<close>
fun conn :: "'v connective \<Rightarrow> 'v propo list \<Rightarrow> 'v propo" where
"conn CT [] = FT" |
"conn CF [] = FF" |
"conn (CVar v) [] = FVar v" |
"conn CNot [\<phi>] = FNot \<phi>" |
"conn CAnd (\<phi> # [\<psi>]) = FAnd \<phi> \<psi>" |
"conn COr (\<phi> # [\<psi>]) = FOr \<phi> \<psi>" |
"conn CImp (\<phi> # [\<psi>]) = FImp \<phi> \<psi>" |
"conn CEq (\<phi> # [\<psi>]) = FEq \<phi> \<psi>" |
"conn _ _ = FF"

text \<open>We will often use case distinction, based on the arity of the @{typ "'v connective"}, thus we
  define our own splitting principle.\<close>
lemma connective_cases_arity[case_names nullary binary unary]:
  assumes nullary: "\<And>x. c = CT \<or> c = CF \<or> c = CVar x \<Longrightarrow> P"
  and binary: "c \<in> binary_connectives \<Longrightarrow> P"
  and unary: "c = CNot \<Longrightarrow> P"
  shows "P"
  using assms by (cases c) (auto simp: binary_connectives_def)

(*Maybe is this version better, by adding nullary_connective[simp] *)
lemma connective_cases_arity_2[case_names nullary unary binary]:
  assumes nullary: "c \<in> nullary_connective \<Longrightarrow> P"
  and unary: "c = CNot \<Longrightarrow> P"
  and binary: "c \<in> binary_connectives \<Longrightarrow> P"
  shows "P"
  using assms by (cases c, auto simp add: binary_connectives_def)


text \<open>Our previous definition is not necessary correct (connective and list of arguments), so we
  define an inductive predicate.\<close>
inductive wf_conn :: "'v connective \<Rightarrow> 'v propo list \<Rightarrow> bool" for c :: "'v connective" where
wf_conn_nullary[simp]: "(c = CT \<or> c = CF \<or> c = CVar v) \<Longrightarrow> wf_conn c []" |
wf_conn_unary[simp]: "c = CNot \<Longrightarrow> wf_conn c [\<psi>]" |
wf_conn_binary[simp]: "c \<in> binary_connectives \<Longrightarrow> wf_conn c (\<psi> # \<psi>' # [])"
thm wf_conn.induct
lemma wf_conn_induct[consumes 1, case_names CT CF CVar CNot COr CAnd CImp CEq]:
  assumes "wf_conn c x" and
    "\<And>v. c = CT \<Longrightarrow> P []" and
    "\<And>v. c = CF \<Longrightarrow> P []" and
    "\<And>v. c = CVar v \<Longrightarrow> P []" and
    "\<And>\<psi>. c = CNot \<Longrightarrow> P [\<psi>]" and
    "\<And>\<psi> \<psi>'. c = COr \<Longrightarrow> P [\<psi>, \<psi>']" and
    "\<And>\<psi> \<psi>'. c = CAnd \<Longrightarrow> P [\<psi>, \<psi>']" and
    "\<And>\<psi> \<psi>'. c = CImp \<Longrightarrow> P [\<psi>, \<psi>']" and
    "\<And>\<psi> \<psi>'. c = CEq \<Longrightarrow> P [\<psi>, \<psi>']"
  shows "P x"
  using assms by induction (auto simp: binary_connectives_def)


subsection \<open>Properties of the Abstraction\<close>

text \<open>First we can define simplification rules.\<close>
lemma wf_conn_conn[simp]:
  "wf_conn CT l \<Longrightarrow> conn CT l = FT"
  "wf_conn CF l \<Longrightarrow> conn CF l = FF"
  "wf_conn (CVar x) l \<Longrightarrow> conn (CVar x) l = FVar x"
  apply (simp_all add: wf_conn.simps)
  unfolding binary_connectives_def by simp_all


lemma wf_conn_list_decomp[simp]:
  "wf_conn CT l \<longleftrightarrow> l = []"
  "wf_conn CF l \<longleftrightarrow> l = []"
  "wf_conn (CVar x) l \<longleftrightarrow> l = []"
  "wf_conn CNot (\<xi> @ \<phi> # \<xi>') \<longleftrightarrow> \<xi> = [] \<and> \<xi>' = []"
  apply (simp_all add: wf_conn.simps)
       unfolding binary_connectives_def apply simp_all
  by (metis append_Nil append_is_Nil_conv list.distinct(1) list.sel(3) tl_append2)


lemma wf_conn_list:
  "wf_conn c l \<Longrightarrow> conn c l = FT \<longleftrightarrow> (c = CT \<and> l = [])"
  "wf_conn c l \<Longrightarrow> conn c l = FF \<longleftrightarrow> (c = CF \<and> l = [])"
  "wf_conn c l \<Longrightarrow> conn c l = FVar x \<longleftrightarrow> (c = CVar x \<and> l = [])"
  "wf_conn c l \<Longrightarrow> conn c l = FAnd a b \<longleftrightarrow> (c = CAnd \<and> l = a # b # [])"
  "wf_conn c l \<Longrightarrow> conn c l = FOr a b \<longleftrightarrow> (c = COr \<and> l = a # b # [])"
  "wf_conn c l \<Longrightarrow> conn c l = FEq a b \<longleftrightarrow> (c = CEq \<and> l = a # b # [])"
  "wf_conn c l \<Longrightarrow> conn c l = FImp a b \<longleftrightarrow> (c = CImp \<and> l = a # b # [])"
  "wf_conn c l \<Longrightarrow> conn c l = FNot a \<longleftrightarrow> (c = CNot \<and> l = a # [])"
  apply (induct l rule: wf_conn.induct)
  unfolding binary_connectives_def by auto

text \<open>In the binary connective cases, we will often decompose the list of arguments (of length 2)
  into two elements.\<close>
lemma list_length2_decomp: "length l = 2 \<Longrightarrow> (\<exists> a b. l = a # b # [])"
  apply (induct l, auto)
  by (rename_tac l, case_tac l, auto)

text \<open>@{term wf_conn} for binary operators means that there are two arguments.\<close>
lemma wf_conn_bin_list_length:
  fixes l :: "'v propo list"
  assumes conn: "c \<in> binary_connectives"
  shows "length l = 2 \<longleftrightarrow> wf_conn c l"
proof
  assume "length l = 2"
  then show "wf_conn c l" using wf_conn_binary list_length2_decomp using conn by metis
next
  assume "wf_conn c l"
  then show "length l = 2" (is "?P l")
    proof (cases rule: wf_conn.induct)
      case wf_conn_nullary
      then show "?P []" using conn binary_connectives_def
        using connective.distinct(11) connective.distinct(13) connective.distinct(9) by blast
    next
      fix \<psi> :: "'v propo"
      case wf_conn_unary
      then show "?P [\<psi>]" using conn binary_connectives_def
        using connective.distinct by blast
    next
      fix \<psi> \<psi>':: "'v propo"
      show "?P [\<psi>, \<psi>']" by auto
    qed
qed

lemma wf_conn_not_list_length[iff]:
  fixes l :: "'v propo list"
  shows "wf_conn CNot l \<longleftrightarrow> length l = 1"
  apply auto
  apply (metis append_Nil connective.distinct(5,17,27) length_Cons list.size(3) wf_conn.simps
    wf_conn_list_decomp(4))
  by (simp add: length_Suc_conv wf_conn.simps)


text \<open>Decomposing the Not into an element is moreover very useful.\<close>
lemma wf_conn_Not_decomp:
  fixes l :: "'v propo list" and a :: "'v"
  assumes corr: "wf_conn CNot l"
  shows "\<exists> a. l = [a]"
  by (metis (no_types, lifting) One_nat_def Suc_length_conv corr length_0_conv
    wf_conn_not_list_length)


text \<open>The @{term wf_conn} remains correct if the length of list does not change. This lemma is very
  useful when we do one rewriting step\<close>
lemma wf_conn_no_arity_change:
  "length l = length l' \<Longrightarrow> wf_conn c l \<longleftrightarrow> wf_conn c l'"
proof -
  {
    fix l l'
    have "length l = length l' \<Longrightarrow> wf_conn c l \<Longrightarrow> wf_conn c l'"
      apply (cases c l rule: wf_conn.induct, auto)
      by (metis wf_conn_bin_list_length)
  }
  then show "length l = length l' \<Longrightarrow> wf_conn c l = wf_conn c l'" by metis
qed

lemma wf_conn_no_arity_change_helper:
  "length (\<xi> @ \<phi> # \<xi>') = length (\<xi> @ \<phi>' # \<xi>') "
  by auto

text \<open>The injectivity of @{term conn} is useful to prove equality of the connectives and the lists.\<close>
lemma conn_inj_not:
  assumes correct: "wf_conn c l"
  and conn: "conn c l = FNot \<psi>"
  shows "c = CNot" and "l = [\<psi>]"
  apply (cases c l rule: wf_conn.cases)
  using correct conn unfolding binary_connectives_def apply auto
  apply (cases c l rule: wf_conn.cases)
  using correct conn unfolding binary_connectives_def by auto


lemma conn_inj:
  fixes c ca :: "'v connective" and l \<psi>s :: "'v propo list"
  assumes corr: "wf_conn ca l"
  and corr': "wf_conn c \<psi>s"
  and eq: "conn ca l = conn c \<psi>s"
  shows "ca = c \<and> \<psi>s = l"
  using corr
proof (cases ca l rule: wf_conn.cases)
  case (wf_conn_nullary v)
  then show "ca = c \<and> \<psi>s = l" using assms
      by (metis conn.simps(1) conn.simps(2) conn.simps(3) wf_conn_list(1-3))
next
  case (wf_conn_unary \<psi>')
  then have *: "FNot \<psi>' = conn c \<psi>s" using conn_inj_not eq assms by auto
  then have "c = ca" by (metis conn_inj_not(1) corr' wf_conn_unary(2))
  moreover have "\<psi>s = l" using * conn_inj_not(2) corr' wf_conn_unary(1) by force
  ultimately show "ca = c \<and> \<psi>s = l" by auto
next
  case (wf_conn_binary \<psi>' \<psi>'')
  then show "ca = c \<and> \<psi>s = l"
    using eq corr' unfolding binary_connectives_def apply (cases ca, auto simp add: wf_conn_list)
    using wf_conn_list(4-7) corr' by metis+
qed



subsection \<open>Subformulas and Properties\<close>

text \<open>A characterization using sub-formulas is interesting for rewriting: we will define our
  relation on the sub-term level, and then lift the rewriting on the term-level. So the rewriting
  takes place on a subformula.\<close>


inductive subformula :: "'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" (infix "\<preceq>" 45) for \<phi> where
subformula_refl[simp]: "\<phi> \<preceq> \<phi>" |
subformula_into_subformula: "\<psi> \<in> set l \<Longrightarrow> wf_conn c l \<Longrightarrow> \<phi> \<preceq> \<psi> \<Longrightarrow> \<phi> \<preceq> conn c l"

text \<open>On the @{prop subformula_into_subformula}, we can see why we use our @{term conn}
  representation: one case is enough to express the subformulas property instead of listing all
  the cases.\<close>

text \<open>This is an example of a property related to subformulas.\<close>
lemma subformula_in_subformula_not:
shows b: "FNot \<phi> \<preceq> \<psi> \<Longrightarrow> \<phi> \<preceq> \<psi>"
  apply (induct rule: subformula.induct)
  using subformula_into_subformula wf_conn_unary subformula_refl list.set_intros(1) subformula_refl
    by (fastforce intro: subformula_into_subformula)+

lemma subformula_in_binary_conn:
  assumes conn: "c \<in> binary_connectives"
  shows "f \<preceq> conn c [f, g]"
  and "g \<preceq> conn c [f, g]"
proof -
  have a: "wf_conn c (f# [g])" using conn wf_conn_binary binary_connectives_def by auto
  moreover have b: "f \<preceq> f" using subformula_refl by auto
  ultimately show "f \<preceq> conn c [f, g]"
    by (metis append_Nil in_set_conv_decomp subformula_into_subformula)
next
  have a: "wf_conn c ([f] @ [g])" using conn wf_conn_binary binary_connectives_def by auto
  moreover have b: "g \<preceq> g" using subformula_refl by auto
  ultimately show "g \<preceq> conn c [f, g]" using subformula_into_subformula by force
qed

lemma subformula_trans:
 "\<psi> \<preceq> \<psi>' \<Longrightarrow> \<phi> \<preceq> \<psi> \<Longrightarrow> \<phi> \<preceq> \<psi>'"
  apply (induct \<psi>' rule: subformula.inducts)
  by (auto simp: subformula_into_subformula)

lemma subformula_leaf:
  fixes \<phi> \<psi> :: "'v propo"
  assumes incl: "\<phi> \<preceq>  \<psi>"
  and simple: "\<psi> = FT \<or> \<psi> = FF \<or> \<psi> = FVar x"
  shows "\<phi> = \<psi>"
  using incl simple
  by (induct rule: subformula.induct, auto simp: wf_conn_list)

lemma subfurmula_not_incl_eq:
  assumes "\<phi> \<preceq> conn c l"
  and "wf_conn c l"
  and "\<forall>\<psi>. \<psi> \<in> set l \<longrightarrow> \<not> \<phi> \<preceq> \<psi>"
  shows "\<phi> = conn c l"
  using assms apply (induction "conn c l" rule: subformula.induct, auto)
  using conn_inj by blast

lemma wf_subformula_conn_cases:
  "wf_conn c l \<Longrightarrow> \<phi> \<preceq> conn c l \<longleftrightarrow> (\<phi> = conn c l \<or> (\<exists>\<psi>. \<psi> \<in> set l \<and> \<phi> \<preceq> \<psi>))"
  apply standard
    using subfurmula_not_incl_eq apply metis
  by (auto simp add: subformula_into_subformula)

lemma subformula_decomp_explicit[simp]:
  "\<phi> \<preceq> FAnd \<psi> \<psi>' \<longleftrightarrow> (\<phi> = FAnd \<psi> \<psi>' \<or> \<phi> \<preceq> \<psi> \<or> \<phi> \<preceq> \<psi>')" (is "?P FAnd")
  "\<phi> \<preceq> FOr \<psi> \<psi>' \<longleftrightarrow> (\<phi> = FOr \<psi> \<psi>' \<or> \<phi> \<preceq> \<psi> \<or> \<phi> \<preceq> \<psi>')"
  "\<phi> \<preceq> FEq \<psi> \<psi>' \<longleftrightarrow> (\<phi> = FEq \<psi> \<psi>' \<or> \<phi> \<preceq> \<psi> \<or> \<phi> \<preceq> \<psi>')"
  "\<phi> \<preceq> FImp \<psi> \<psi>' \<longleftrightarrow> (\<phi> = FImp \<psi> \<psi>' \<or> \<phi> \<preceq> \<psi> \<or> \<phi> \<preceq> \<psi>')"
proof -
  have "wf_conn CAnd [\<psi>, \<psi>']" by (simp add: binary_connectives_def)
  then have "\<phi> \<preceq> conn CAnd [\<psi>, \<psi>'] \<longleftrightarrow>
    (\<phi> = conn CAnd [\<psi>, \<psi>'] \<or> (\<exists>\<psi>''. \<psi>'' \<in> set [\<psi>, \<psi>'] \<and> \<phi> \<preceq> \<psi>''))"
    using wf_subformula_conn_cases by metis
  then show "?P FAnd" by auto
next
  have "wf_conn COr [\<psi>, \<psi>']" by (simp add: binary_connectives_def)
  then have "\<phi> \<preceq> conn COr [\<psi>, \<psi>'] \<longleftrightarrow>
    (\<phi> = conn COr [\<psi>, \<psi>'] \<or> (\<exists>\<psi>''. \<psi>'' \<in> set [\<psi>, \<psi>'] \<and> \<phi> \<preceq> \<psi>''))"
    using wf_subformula_conn_cases by metis
  then show "?P FOr" by auto
next
  have "wf_conn CEq [\<psi>, \<psi>']" by (simp add: binary_connectives_def)
  then have "\<phi> \<preceq> conn CEq [\<psi>, \<psi>'] \<longleftrightarrow>
    (\<phi> = conn CEq [\<psi>, \<psi>'] \<or> (\<exists>\<psi>''. \<psi>'' \<in> set [\<psi>, \<psi>'] \<and> \<phi> \<preceq> \<psi>''))"
    using wf_subformula_conn_cases by metis
  then show "?P FEq" by auto
next
  have "wf_conn CImp [\<psi>, \<psi>']" by (simp add: binary_connectives_def)
  then have "\<phi> \<preceq> conn CImp [\<psi>, \<psi>'] \<longleftrightarrow>
    (\<phi> = conn CImp [\<psi>, \<psi>'] \<or> (\<exists>\<psi>''. \<psi>'' \<in> set [\<psi>, \<psi>'] \<and> \<phi> \<preceq> \<psi>''))"
    using wf_subformula_conn_cases by metis
  then show "?P FImp" by auto
qed

lemma wf_conn_helper_facts[iff]:
  "wf_conn CNot [\<phi>]"
  "wf_conn CT []"
  "wf_conn CF []"
  "wf_conn (CVar x) []"
  "wf_conn CAnd [\<phi>, \<psi>]"
  "wf_conn COr [\<phi>, \<psi>]"
  "wf_conn CImp [\<phi>, \<psi>]"
  "wf_conn CEq [\<phi>, \<psi>]"
  using wf_conn.intros unfolding binary_connectives_def by fastforce+

lemma exists_c_conn: "\<exists> c l. \<phi> = conn c l \<and> wf_conn c l"
  by (cases \<phi>) force+

lemma subformula_conn_decomp[simp]:
  assumes wf: "wf_conn c l"
  shows "\<phi> \<preceq> conn c l \<longleftrightarrow> (\<phi> = conn c l \<or> (\<exists> \<psi>\<in> set l. \<phi> \<preceq> \<psi>))" (is "?A \<longleftrightarrow> ?B")
proof (rule iffI)
  {
    fix \<xi>
    have "\<phi> \<preceq> \<xi> \<Longrightarrow> \<xi> = conn c l \<Longrightarrow> wf_conn c l \<Longrightarrow> \<forall>x::'a propo\<in>set l. \<not> \<phi> \<preceq> x \<Longrightarrow> \<phi> = conn c l"
      apply (induct rule: subformula.induct)
        apply simp
      using conn_inj by blast
  }
  moreover assume ?A
  ultimately show ?B using wf by metis
next
  assume ?B
  then show "\<phi> \<preceq> conn c l" using wf wf_subformula_conn_cases by blast
qed

lemma subformula_leaf_explicit[simp]:
  "\<phi> \<preceq> FT \<longleftrightarrow> \<phi> = FT"
  "\<phi> \<preceq> FF \<longleftrightarrow> \<phi> = FF"
  "\<phi> \<preceq> FVar x \<longleftrightarrow> \<phi> = FVar x"
  apply auto
  using subformula_leaf by metis +

text \<open>The variables inside the formula gives precisely the variables that are needed for the
  formula.\<close>
primrec vars_of_prop:: "'v propo \<Rightarrow> 'v set" where
"vars_of_prop FT = {}" |
"vars_of_prop FF = {}" |
"vars_of_prop (FVar x) = {x}" |
"vars_of_prop (FNot \<phi>) = vars_of_prop \<phi>" |
"vars_of_prop (FAnd \<phi> \<psi>) = vars_of_prop \<phi> \<union> vars_of_prop \<psi>" |
"vars_of_prop (FOr \<phi> \<psi>) = vars_of_prop \<phi> \<union> vars_of_prop \<psi>" |
"vars_of_prop (FImp \<phi> \<psi>) = vars_of_prop \<phi> \<union> vars_of_prop \<psi>" |
"vars_of_prop (FEq \<phi> \<psi>) = vars_of_prop \<phi> \<union> vars_of_prop \<psi>"

lemma vars_of_prop_incl_conn:
  fixes \<xi> \<xi>' :: "'v propo list" and \<psi> :: "'v propo" and c :: "'v connective"
  assumes corr: "wf_conn c l" and incl: "\<psi> \<in> set l"
  shows "vars_of_prop \<psi> \<subseteq> vars_of_prop (conn c l)"
proof (cases c rule: connective_cases_arity_2)
  case nullary
  then have False using corr incl by auto
  then show "vars_of_prop \<psi> \<subseteq> vars_of_prop (conn c l)" by blast
next
  case binary note c = this
  then obtain a b where ab: "l = [a, b]"
    using wf_conn_bin_list_length list_length2_decomp corr by metis
  then have "\<psi> = a \<or> \<psi> = b" using incl by auto
  then show "vars_of_prop \<psi> \<subseteq> vars_of_prop (conn c l)"
    using ab c unfolding binary_connectives_def by auto
next
  case unary note c = this
  fix \<phi> :: "'v propo"
  have "l = [\<psi>]" using corr c incl split_list by force
  then show "vars_of_prop \<psi> \<subseteq> vars_of_prop (conn c l)" using c by auto
qed

text \<open>The set of variables is compatible with the subformula order.\<close>
lemma subformula_vars_of_prop:
  "\<phi> \<preceq> \<psi> \<Longrightarrow> vars_of_prop \<phi> \<subseteq> vars_of_prop \<psi>"
  apply (induct rule: subformula.induct)
  apply simp
  using vars_of_prop_incl_conn by blast


subsection \<open>Positions\<close>

text \<open>Instead of 1 or 2 we use @{term L} or @{term R}\<close>
datatype sign = L | R

text \<open>We use @{term nil} instead of @{term \<epsilon>}.\<close>
fun pos :: "'v propo \<Rightarrow> sign list set" where
"pos FF = {[]}" |
"pos FT = {[]}" |
"pos (FVar x) = {[]}" |
"pos (FAnd \<phi> \<psi>) = {[]} \<union> { L # p | p. p\<in> pos \<phi>} \<union> { R # p | p. p\<in> pos \<psi>}" |
"pos (FOr \<phi> \<psi>) = {[]} \<union> { L # p | p. p\<in> pos \<phi>} \<union> { R # p | p. p\<in> pos \<psi>}" |
"pos (FEq \<phi> \<psi>) = {[]} \<union> { L # p | p. p\<in> pos \<phi>} \<union> { R # p | p. p\<in> pos \<psi>}" |
"pos (FImp \<phi> \<psi>) = {[]} \<union> { L # p | p. p\<in> pos \<phi>} \<union> { R # p | p. p\<in> pos \<psi>}" |
"pos (FNot \<phi>) = {[]} \<union> { L # p | p. p\<in> pos \<phi>}"

lemma finite_pos: "finite (pos \<phi>)"
  by (induct \<phi>, auto)

lemma finite_inj_comp_set:
  fixes s :: "'v set"
  assumes finite: "finite s"
  and inj: "inj f"
  shows "card ({f p |p. p \<in> s}) = card s"
  using finite
proof (induct s rule: finite_induct)
  show "card {f p |p. p \<in> {}} = card {}" by auto
next
  fix x :: "'v" and s:: "'v set"
  assume f: "finite s" and notin: "x \<notin> s"
  and IH: "card {f p |p. p \<in> s} = card s"
  have f': "finite {f p |p. p \<in> insert x s}" using f by auto
  have notin': "f x \<notin> {f p |p. p \<in> s}" using notin inj injD by fastforce
  have "{f p |p. p \<in> insert x s} = insert (f x) {f p |p. p\<in> s}" by auto
  then have "card {f p |p. p \<in> insert x s} = 1 + card {f p |p. p \<in> s}"
    using finite card_insert_disjoint f' notin' by auto
  moreover have "\<dots> = card (insert x s)" using notin f IH by auto
  finally show "card {f p |p. p \<in> insert x s} = card (insert x s)" .
qed

lemma cons_inject:
  "inj ((#) s)"
  by (meson injI list.inject)

lemma finite_insert_nil_cons:
  "finite s \<Longrightarrow> card (insert [] {L # p |p. p \<in> s}) = 1 + card {L # p |p. p \<in> s}"
  using card_insert_disjoint by auto


lemma cord_not[simp]:
  "card (pos (FNot \<phi>)) = 1 + card (pos \<phi>)"
by (simp add: cons_inject finite_inj_comp_set finite_pos)

lemma card_seperate:
  assumes "finite s1" and "finite s2"
  shows "card ({L # p |p. p \<in> s1} \<union> {R # p |p. p \<in> s2}) = card ({L # p |p. p \<in> s1})
           + card({R # p |p. p \<in> s2})" (is "card (?L\<union>?R) = card ?L + card ?R")
proof -
  have "finite ?L" using assms by auto
  moreover have "finite ?R" using assms by auto
  moreover have "?L \<inter> ?R = {}" by blast
  ultimately show ?thesis using assms card_Un_disjoint by blast
qed

definition prop_size where "prop_size \<phi> = card (pos \<phi>)"

lemma prop_size_vars_of_prop:
  fixes \<phi> :: "'v propo"
  shows "card (vars_of_prop \<phi>) \<le> prop_size \<phi>"
  (* TODO Tune proof *)
  unfolding prop_size_def apply (induct \<phi>, auto simp add: cons_inject finite_inj_comp_set finite_pos)
proof -
  fix \<phi>1 \<phi>2 :: "'v propo"
  assume IH1: "card (vars_of_prop \<phi>1) \<le> card (pos \<phi>1)"
  and IH2: "card (vars_of_prop \<phi>2) \<le> card (pos \<phi>2)"
  let ?L = "{L # p |p. p \<in> pos \<phi>1}"
  let ?R = "{R # p |p. p \<in> pos \<phi>2}"
  have "card (?L \<union> ?R) = card ?L +  card ?R"
    using card_seperate finite_pos by blast
  moreover have "\<dots> = card (pos \<phi>1) + card (pos \<phi>2)"
    by (simp add: cons_inject finite_inj_comp_set finite_pos)
  moreover have "\<dots> \<ge> card (vars_of_prop \<phi>1) + card (vars_of_prop \<phi>2)" using IH1 IH2 by arith
  then have "\<dots> \<ge> card (vars_of_prop \<phi>1 \<union> vars_of_prop \<phi>2)" using card_Un_le le_trans by blast
  ultimately
    show "card (vars_of_prop \<phi>1 \<union> vars_of_prop \<phi>2) \<le> Suc (card (?L \<union> ?R))"
         "card (vars_of_prop \<phi>1 \<union> vars_of_prop \<phi>2) \<le> Suc (card (?L \<union> ?R))"
         "card (vars_of_prop \<phi>1 \<union> vars_of_prop \<phi>2) \<le> Suc (card (?L \<union> ?R))"
         "card (vars_of_prop \<phi>1 \<union> vars_of_prop \<phi>2) \<le> Suc (card (?L \<union> ?R))"
    by auto
qed

value "pos (FImp (FAnd (FVar P) (FVar Q)) (FOr (FVar P) (FVar Q)))"

inductive path_to :: "sign list \<Rightarrow> 'v propo \<Rightarrow> 'v propo \<Rightarrow> bool" where
path_to_refl[intro]: "path_to [] \<phi> \<phi>" |
path_to_l: "c\<in>binary_connectives \<or> c = CNot \<Longrightarrow> wf_conn c (\<phi>#l) \<Longrightarrow> path_to p \<phi> \<phi>'\<Longrightarrow>
  path_to (L#p) (conn c (\<phi>#l)) \<phi>'" |
path_to_r: "c\<in>binary_connectives \<Longrightarrow> wf_conn c (\<psi>#\<phi>#[]) \<Longrightarrow> path_to p \<phi> \<phi>' \<Longrightarrow>
  path_to (R#p) (conn c (\<psi>#\<phi>#[])) \<phi>'"

text \<open>There is a deep link between subformulas and pathes: a (correct) path leads to a subformula
  and a subformula is associated to a given path.\<close>
lemma path_to_subformula:
  "path_to p \<phi> \<phi>' \<Longrightarrow> \<phi>' \<preceq> \<phi>"
  apply (induct rule: path_to.induct)
    apply simp
   apply (metis list.set_intros(1) subformula_into_subformula)
  using subformula_trans subformula_in_binary_conn(2) by metis

lemma subformula_path_exists:
  fixes \<phi> \<phi>':: "'v propo"
  shows "\<phi>' \<preceq> \<phi> \<Longrightarrow> \<exists>p. path_to p \<phi> \<phi>'"
proof (induct rule: subformula.induct)
  case subformula_refl
  have "path_to [] \<phi>' \<phi>'" by auto
  then show "\<exists>p. path_to p \<phi>' \<phi>'" by metis
next
  case (subformula_into_subformula \<psi> l c)
  note wf = this(2) and IH = this(4) and \<psi> = this(1)
  then obtain p where p: "path_to p \<psi> \<phi>'" by metis
  {
    fix x :: "'v"
    assume "c = CT \<or> c = CF \<or> c = CVar x"
    then have "False" using subformula_into_subformula by auto
    then have "\<exists>p. path_to p (conn c l) \<phi>'" by blast
  }
  moreover {
    assume c: "c = CNot"
    then have "l = [\<psi>]" using wf \<psi> wf_conn_Not_decomp by fastforce
    then have "path_to (L # p) (conn c l) \<phi>'" by (metis c wf_conn_unary p path_to_l)
   then have "\<exists>p. path_to p (conn c l) \<phi>'" by blast
  }
  moreover {
    assume c: "c\<in> binary_connectives"
    obtain a b where ab: "[a, b] = l" using subformula_into_subformula c wf_conn_bin_list_length
      list_length2_decomp by metis
    then have "a = \<psi> \<or> b = \<psi>" using \<psi> by auto
    then have "path_to (L # p) (conn c l) \<phi>' \<or> path_to (R # p) (conn c l) \<phi>'" using c path_to_l
      path_to_r p ab by (metis wf_conn_binary)
    then have "\<exists>p. path_to p (conn c l) \<phi>'" by blast
  }
  ultimately show "\<exists>p. path_to p (conn c l) \<phi>'" using connective_cases_arity by metis
qed

fun replace_at :: "sign list \<Rightarrow> 'v propo \<Rightarrow> 'v propo \<Rightarrow> 'v propo" where
"replace_at [] _ \<psi> = \<psi>" |
"replace_at (L # l) (FAnd \<phi> \<phi>') \<psi> = FAnd (replace_at l \<phi> \<psi>) \<phi>'"|
"replace_at (R # l) (FAnd \<phi> \<phi>') \<psi> = FAnd \<phi> (replace_at l \<phi>' \<psi>)" |
"replace_at (L # l) (FOr \<phi> \<phi>') \<psi> = FOr (replace_at l \<phi> \<psi>) \<phi>'" |
"replace_at (R # l) (FOr \<phi> \<phi>') \<psi> = FOr \<phi> (replace_at l \<phi>' \<psi>)" |
"replace_at (L # l) (FEq \<phi> \<phi>') \<psi> = FEq (replace_at l \<phi> \<psi>) \<phi>'"|
"replace_at (R # l) (FEq \<phi> \<phi>') \<psi> = FEq \<phi> (replace_at l \<phi>' \<psi>)" |
"replace_at (L # l) (FImp \<phi> \<phi>') \<psi> = FImp (replace_at l \<phi> \<psi>) \<phi>'"|
"replace_at (R # l) (FImp \<phi> \<phi>') \<psi> = FImp \<phi> (replace_at l \<phi>' \<psi>)" |
"replace_at (L # l) (FNot \<phi>) \<psi> = FNot (replace_at l \<phi> \<psi>)"


section \<open>Semantics over the Syntax\<close>

text \<open>Given the syntax defined above, we define a semantics, by defining an evaluation function
  @{term eval}. This function is the bridge between the logic as we define it here and the built-in
  logic of Isabelle.\<close>
fun eval :: "('v \<Rightarrow> bool) \<Rightarrow> 'v propo \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
"\<A> \<Turnstile> FT = True" |
"\<A> \<Turnstile> FF = False" |
"\<A> \<Turnstile> FVar v = (\<A> v)" |
"\<A> \<Turnstile> FNot \<phi> = (\<not>(\<A>\<Turnstile> \<phi>))" |
"\<A> \<Turnstile> FAnd \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A>\<Turnstile>\<phi>\<^sub>1 \<and> \<A>\<Turnstile>\<phi>\<^sub>2)" |
"\<A> \<Turnstile> FOr \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A>\<Turnstile>\<phi>\<^sub>1 \<or> \<A>\<Turnstile>\<phi>\<^sub>2)" |
"\<A> \<Turnstile> FImp \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A>\<Turnstile>\<phi>\<^sub>1 \<longrightarrow> \<A>\<Turnstile>\<phi>\<^sub>2)" |
"\<A> \<Turnstile> FEq \<phi>\<^sub>1 \<phi>\<^sub>2 = (\<A>\<Turnstile>\<phi>\<^sub>1 \<longleftrightarrow> \<A> \<Turnstile>\<phi>\<^sub>2)"

definition evalf (infix "\<Turnstile>f" 50) where
"evalf \<phi> \<psi> = (\<forall>A. A \<Turnstile> \<phi> \<longrightarrow> A \<Turnstile> \<psi>)"

text \<open>The deduction rule is in the book. And the proof looks like to the one of the book.\<close>
theorem deduction_theorem:
  "\<phi> \<Turnstile>f \<psi> \<longleftrightarrow> (\<forall>A. A \<Turnstile> FImp \<phi> \<psi>)"
proof
  assume H: "\<phi> \<Turnstile>f \<psi>"
  {
    fix A
    have "A \<Turnstile> FImp \<phi> \<psi>"
      proof (cases "A \<Turnstile> \<phi>")
        case True
        then have "A \<Turnstile> \<psi>" using H unfolding evalf_def by metis
        then show "A \<Turnstile> FImp \<phi> \<psi>" by auto
      next
        case False
        then show "A \<Turnstile> FImp \<phi> \<psi>" by auto
      qed
  }
  then show "\<forall>A. A \<Turnstile> FImp \<phi> \<psi>" by blast
next
  assume A: "\<forall>A. A \<Turnstile> FImp \<phi> \<psi>"
  show "\<phi> \<Turnstile>f \<psi>"
    proof (rule ccontr)
      assume "\<not> \<phi> \<Turnstile>f \<psi>"
      then obtain A where "A \<Turnstile> \<phi>" and "\<not> A \<Turnstile> \<psi>" using evalf_def by metis
      then have "\<not> A \<Turnstile> FImp \<phi> \<psi>" by auto
      then show False using A by blast
    qed
qed

text \<open>A shorter proof:\<close>
lemma "\<phi> \<Turnstile>f \<psi> \<longleftrightarrow> (\<forall>A. A\<Turnstile> FImp \<phi> \<psi>)"
  by (simp add: evalf_def)

definition same_over_set:: "('v \<Rightarrow> bool) \<Rightarrow>('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> bool" where
"same_over_set A B S = (\<forall>c\<in>S. A c = B c)"

text \<open>If two mapping @{term A} and @{term B} have the same value over the variables, then the same
  formula are satisfiable.\<close>
lemma same_over_set_eval:
  assumes "same_over_set A B (vars_of_prop \<phi>)"
  shows "A \<Turnstile> \<phi> \<longleftrightarrow> B \<Turnstile> \<phi>"
  using assms unfolding same_over_set_def by (induct \<phi>, auto)

end
