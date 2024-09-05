(* Title:        Part of the proof of compactness of first-order logic following Harrison's one in
 *               HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)

theory FOL_Syntax
  imports
    Main
    HOL.Zorn
    Propositional_Proof_Systems.Compactness
    First_Order_Terms.Term
begin

(* This heavily reuses Ghilain's FOL_Compactness code, with simplifications for nat type
   and renamings to follow Harrison's text *)

(* Comments starting with != indicate discrepancies with Harrison's formalisation *)

no_notation Not ("\<^bold>\<not>")
no_notation And (infix "\<^bold>\<and>" 68)
no_notation Or  (infix "\<^bold>\<or>" 68)

(* ---------------------------------------------------------------------------------------*)
(* To remove once the following have been integrated to the AFP in First_Order_Terms.Term *)
lemma count_terms: \<^marker>\<open>contributor \<open>Sophie Tourret\<close>\<close>
  "OFCLASS(('f::countable, 'v::countable) term,countable_class)" 
  by countable_datatype

instance "term" :: (countable, countable) countable
  \<^marker>\<open>contributor \<open>Sophie Tourret\<close>\<close>
  using count_terms by simp
(* ---------------------------------------------------------------------------------------*)

type_synonym nterm = \<open>(nat, nat) term\<close>

lemma count_nterms: "OFCLASS(nterm,countable_class)"
  using count_terms by simp

instance formula :: (countable) countable
  by countable_datatype

term "test (0, [Var 0])"

fun functions_term :: \<open>nterm \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_term (Var _) = {}\<close>
| \<open>functions_term (Fun f ts) = {(f, length ts)} \<union> (\<Union> t \<in> set ts. functions_term t)\<close>

datatype form =
  Bot (\<open>\<^bold>\<bottom>\<close>)
| Atom (pred:nat) (args:\<open>nterm list\<close>)
| Implies form form (infixl \<open>\<^bold>\<longrightarrow>\<close> 85)
| Forall nat form (\<open>\<^bold>\<forall> _\<^bold>. _\<close> [0, 70] 70)

fun functions_form :: \<open>form \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_form \<^bold>\<bottom> = {}\<close>
| \<open>functions_form (Atom p ts) = (\<Union> t \<in> set ts. functions_term t)\<close> 
| \<open>functions_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = functions_form \<phi> \<union> functions_form \<psi>\<close>
| \<open>functions_form (\<^bold>\<forall> x\<^bold>. \<phi>) = functions_form \<phi>\<close>

fun predicates_form :: \<open>form \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>predicates_form \<^bold>\<bottom> = {}\<close>
| \<open>predicates_form (Atom p ts) = {(p, length ts)}\<close>
| \<open>predicates_form (\<phi> \<^bold>\<longrightarrow> \<psi>) = predicates_form \<phi> \<union> predicates_form \<psi>\<close>
| \<open>predicates_form (\<^bold>\<forall> x\<^bold>. \<phi>) = predicates_form \<phi>\<close>

definition functions_forms :: \<open>form set \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_forms fms = \<Union> {functions_form f |f. f \<in> fms}\<close>

definition predicates :: \<open>form set \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>predicates fms = \<Union> {predicates_form f |f. f \<in> fms}\<close>

definition language :: \<open>form set \<Rightarrow> ((nat \<times> nat) set \<times> (nat \<times> nat) set)\<close> where
  \<open>language fms = (functions_forms fms, predicates fms)\<close>

lemma lang_singleton: \<open>language {p} = (functions_form p, predicates_form p)\<close>
  unfolding language_def functions_forms_def predicates_def by simp

abbreviation (input) Not :: \<open>form \<Rightarrow> form\<close> (\<open>\<^bold>\<not> _\<close> [90] 90) where
  \<open>\<^bold>\<not> \<phi> \<equiv> \<phi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation (input) Top :: \<open>form\<close> (\<open>\<^bold>\<top>\<close>) where
  \<open>\<^bold>\<top> \<equiv> \<^bold>\<not> \<^bold>\<bottom>\<close>

abbreviation (input) Or :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infixl \<open>\<^bold>\<or>\<close> 84) where
  \<open>\<phi> \<^bold>\<or> \<psi> \<equiv> (\<phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> \<psi>\<close>

abbreviation (input) And :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infixl \<open>\<^bold>\<and>\<close> 84) where
  \<open>\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not> (\<^bold>\<not> \<phi> \<^bold>\<or> \<^bold>\<not> \<psi>)\<close>

abbreviation (input) Equiv :: \<open>form \<Rightarrow> form \<Rightarrow> form\<close>
  (infix \<open>\<^bold>\<longleftrightarrow>\<close> 70) where
  \<open>\<phi> \<^bold>\<longleftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<and> \<psi> \<^bold>\<longrightarrow> \<phi>)\<close> 

abbreviation (input) Exists :: \<open>nat \<Rightarrow> form \<Rightarrow> form\<close>
  (\<open>\<^bold>\<exists> _\<^bold>. _\<close> [0, 70] 70) where
  \<open>\<^bold>\<exists> x\<^bold>. \<phi> \<equiv> \<^bold>\<not> (\<^bold>\<forall> x\<^bold>. \<^bold>\<not> \<phi>)\<close>

lemma ex_all_distinct: \<open>\<^bold>\<forall>x\<^bold>. \<phi> \<noteq> \<^bold>\<exists>y\<^bold>. \<psi>\<close>
  by simp

abbreviation FVT :: \<open>nterm \<Rightarrow> nat set\<close> where
  \<open>FVT \<equiv> vars_term\<close>

fun FV :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>FV \<^bold>\<bottom> = {}\<close>
| \<open>FV (Atom _ ts) = (\<Union> a \<in> set ts. FVT a)\<close>
| \<open>FV (\<phi> \<^bold>\<longrightarrow> \<psi>) = FV \<phi> \<union> FV \<psi>\<close>
| \<open>FV (\<^bold>\<forall> x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>

lemma FV_all_subs: \<open>FV \<phi> \<subseteq> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<union> {x}\<close>
  by fastforce

lemma FV_exists: \<open>FV (\<^bold>\<exists>x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>
  by simp

lemma finite_FV: \<open>finite (FV \<phi>)\<close>
  by (induction \<phi>, auto)

fun BV :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>BV \<^bold>\<bottom> = {}\<close>
| \<open>BV (Atom _ args') = {}\<close>
| \<open>BV (\<phi> \<^bold>\<longrightarrow> \<psi>) = {}\<close>
| \<open>BV (\<^bold>\<forall> x\<^bold>. \<phi>) = BV \<phi> \<union> {x}\<close>

lemma finite_BV: \<open>finite (BV \<phi>)\<close>
  by (induction \<phi>, auto)

(* != substitutions over terms are defined in the Term theory *)

definition variant :: \<open>nat set \<Rightarrow> nat\<close> where
  \<open>variant s = Max s + 1\<close>

lemma variant_finite: \<open>finite s \<Longrightarrow> \<not> (variant s \<in> s)\<close>
  unfolding variant_def using Max_ge less_le_not_le by auto

lemma variant_form: \<open>\<not> variant (FV \<phi>) \<in> FV \<phi>\<close>
  using variant_finite finite_FV by blast

fun formsubst :: \<open>form \<Rightarrow> (nat, nat) subst \<Rightarrow> form\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m _ = \<^bold>\<bottom>\<close> 
| \<open>(Atom p ts) \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<phi> \<^bold>\<longrightarrow> \<psi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
| \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =
    (let \<sigma>' = \<sigma>(x := Var x);
         z = if \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)
             then variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')) else x in
    \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>

fun formsubst2 :: \<open>form \<Rightarrow> (nat, nat) subst \<Rightarrow> form\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m2\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m2 _ = \<^bold>\<bottom>\<close> 
| \<open>(Atom p ts) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<phi> \<^bold>\<longrightarrow> \<psi>) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>) \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>)\<close>
| \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m2 \<sigma> = (let \<sigma>' = \<sigma>(x := Var x) in
    (if \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)
    then (let z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>')) in
      \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>(x := Var z)))
    else \<^bold>\<forall> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>')))\<close>

lemma formsubst_def_switch: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>\<close>
proof (induction \<phi> arbitrary: \<sigma> rule: form.induct)
  case Bot
  then show ?case
    by fastforce
next
  case (Atom x1 x2)
  then show ?case
    by fastforce
next
  case (Implies x1 x2)
  then show ?case
    by fastforce
next
  case (Forall x1 x2)
  then show ?case
    by (smt (verit, best) formsubst.simps(4) formsubst2.simps(4))
qed

lemma termsubst_valuation: \<open>\<forall>x\<in>FVT t. \<sigma> x = \<sigma>' x \<Longrightarrow> t \<cdot> \<sigma> = t \<cdot> \<sigma>'\<close>
  using eval_same_vars by blast

lemma termsetsubst_valuation: \<open>\<forall>y \<in> T. \<forall>x\<in>FVT y. \<sigma> x = \<sigma>' x \<Longrightarrow> t \<in> T \<Longrightarrow> t \<cdot> \<sigma> = t \<cdot> \<sigma>'\<close>
  using termsubst_valuation by fast

lemma formsubst_valuation: \<open>\<forall>x\<in>(FV \<phi>). (Var x) \<cdot> \<sigma> = (Var x) \<cdot> \<sigma>' \<Longrightarrow> \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
proof (induction \<phi> arbitrary: \<sigma> \<sigma>' rule:form.induct)
  case Bot
  then show ?case by simp
next
  case (Atom x1 x2)
  then show ?case
    using termsetsubst_valuation
    by auto
next
  case (Implies x1 x2)
  then show ?case by simp
next
  case (Forall x \<phi>)
  define \<sigma>'' where "\<sigma>'' = \<sigma>(x := Var x)"
  define \<sigma>''' where "\<sigma>''' = \<sigma>'(x := Var x)"
  have ex_var_equiv: \<open>\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>'' y) \<equiv> \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>''' y)\<close>
    using \<sigma>''_def \<sigma>'''_def Forall(2)
    by (smt (verit, ccfv_threshold) eval_term.simps(1) fun_upd_other fun_upd_same)
  have sig_x_subst: \<open>\<forall>y\<in>FV \<phi>. Var y \<cdot> \<sigma>(x := Var z) = Var y \<cdot> \<sigma>'(x := Var z)\<close> for z
    using Forall(2) by simp
  show ?case
  proof (cases \<open>\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>'' y)\<close>)
    case True
    then have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (let z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'')) in \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by (simp add: \<sigma>''_def)
    also have \<open>... = (let z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>''')) in \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'(x := Var z)))\<close>
      using sig_x_subst \<sigma>'''_def by (metis Forall.IH \<sigma>''_def)
    also have \<open>... = (\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
      using True \<sigma>'''_def ex_var_equiv formsubst.simps(4) by presburger
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using Forall.IH \<sigma>'''_def \<sigma>''_def ex_var_equiv sig_x_subst by auto
  qed
qed

(* != needed in HOL-Light but seems trivial in modern Isabelle/HOL *)
lemma \<open>{x. \<exists>y. y \<in> (s \<union> t) \<and> P x y} = {x. \<exists>y. y \<in> s \<and> P x y} \<union> {x. \<exists>y. y \<in> t \<and> P x y}\<close>
  by blast

lemma formsubst_structure_bot: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<bottom> \<longleftrightarrow> \<phi> = \<^bold>\<bottom>\<close>
  by (smt (verit) form.distinct(5) form.simps(5) form.simps(7) formsubst.elims)

find_theorems formsubst
thm form.distinct
find_theorems name: FOL_Syntax.form

lemma formsubst_structure_pred: \<open>(\<exists>p ts. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p ts) \<longleftrightarrow> (\<exists>p ts. \<phi> = Atom p ts)\<close>
proof (cases \<phi>)
  case (Forall x \<psi>)
  then show ?thesis
    using formsubst_def_switch by (metis (no_types, lifting) form.distinct(10) formsubst.simps(4))
qed auto

lemma formsubst_structure_imp: \<open>(\<exists>\<phi>1 \<phi>2. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<longleftrightarrow> (\<exists>\<psi>1 \<psi>2. \<phi> = \<psi>1 \<^bold>\<longrightarrow> \<psi>2)\<close>
proof (cases \<phi>)
  case (Forall x \<psi>)
  then show ?thesis
    using formsubst_def_switch
    by (metis (no_types, lifting) form.distinct(11) formsubst.simps(4))
qed auto

lemma formsubst_structure_all: \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>))\<close>
proof (cases \<phi>)
  case (Forall x \<psi>)
  then show ?thesis
    using formsubst_def_switch
    by (metis (no_types, lifting) formsubst.simps(4))
qed auto

lemma formsubst_structure_not: \<open>(\<exists>\<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Not \<psi>) \<longleftrightarrow> (\<exists>\<psi>. \<phi> = Not \<psi>)\<close>
  using formsubst_structure_imp formsubst_structure_bot
  by (metis form.sel(4) formsubst.simps(3))

lemma formsubst_structure_not_all_imp: 
  \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
proof (cases \<phi>)
  case Bot
  then show ?thesis by simp
next
  case (Atom p ts)
  then show ?thesis by simp
next
  case (Implies \<phi>1 \<phi>2)
  then show ?thesis
    by (metis form.inject(2) formsubst.simps(3) formsubst_structure_all formsubst_structure_not)
next
  case (Forall y \<psi>)
  then show ?thesis
    by (metis form.distinct(11) formsubst_structure_not)
qed

lemma formsubst_structure_all_not: 
  \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>))\<close>
proof
  show \<open>\<exists>x \<psi>. \<phi> = \<^bold>\<forall> x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom> \<Longrightarrow> \<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall> x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    by (smt (verit, ccfv_threshold) formsubst.simps(1) formsubst.simps(3) formsubst.simps(4))
next
  assume \<open>\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
  then obtain z \<psi>' where phi_sub_is: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. \<psi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    by blast
  then obtain x \<phi>' where phi_is: \<open>\<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'\<close>
    using formsubst_structure_all by blast
  then have \<open>\<exists>\<sigma>'. \<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>' = \<psi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    using phi_sub_is
    by (metis (no_types, lifting) form.sel(6) formsubst.simps(4))
  then obtain \<sigma>' where \<open>\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>' = \<psi>' \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    by blast
  then have \<open>\<exists>\<psi>. \<phi>' = \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    using formsubst_structure_imp formsubst_structure_not by blast
  then show \<open>\<exists>x \<psi>. \<phi> = \<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
    using phi_is by blast
qed

lemma formsubst_structure_ex: \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<exists>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<exists>x\<^bold>. \<psi>))\<close>
proof
  assume \<open>\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<exists>x\<^bold>. \<psi>)\<close>
  (*have \<open>(\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
    (* sledgehammer (veriT) segfalts on this one ! *)
    sorry*)
  then show \<open>\<exists>x \<psi>. \<phi> = (\<^bold>\<exists>x\<^bold>. \<psi>)\<close>
  proof (induction \<phi>)
    case Bot
    then have False by auto
    then show ?case by auto
  next
    case (Atom p ts)
    then have False by auto
    then show ?case by auto
  next
    case (Implies \<phi>1 \<phi>2)
    then obtain x \<psi> where imp_def: \<open>\<phi>1 \<^bold>\<longrightarrow> \<phi>2 \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>) \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>
      by blast
    then have bot_right: \<open>\<phi>2 = \<^bold>\<bottom>\<close>
      by (simp add: formsubst_structure_bot)
    have \<open>\<phi>1  \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi> \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
      using imp_def by simp
    then have ex_eq: \<open>\<exists>x2 \<psi>2. \<phi>1  \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x2\<^bold>. \<psi>2 \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
      by blast
    then have \<open>\<exists>x2 \<psi>2. \<phi>1 = (\<^bold>\<forall>x2\<^bold>. \<psi>2 \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
      using formsubst_structure_all_not by blast
    then show ?case
      using bot_right by auto
  next
    case (Forall x1 \<phi>)
    have False
      using Forall(2) formsubst_def_switch by (metis form.distinct(11) formsubst_structure_all)
    then show ?case by auto
  qed
next
  assume \<open>(\<exists>x \<psi>. \<phi> = (\<^bold>\<exists>x\<^bold>. \<psi>))\<close>
  then show \<open>\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<exists>x\<^bold>. \<psi>)\<close>
    by (smt (verit, ccfv_threshold) formsubst.simps(1) formsubst.simps(3) formsubst.simps(4))
qed 

lemma formsubst_structure: \<open>(\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<bottom> \<longleftrightarrow> \<phi> = \<^bold>\<bottom>) \<and> 
  ((\<exists>p ts. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p ts) \<longleftrightarrow> (\<exists>p ts. \<phi> = Atom p ts)) \<and>
  ((\<exists>\<phi>1 \<phi>2. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = \<phi>1 \<^bold>\<longrightarrow> \<phi>2) \<longleftrightarrow> (\<exists>\<psi>1 \<psi>2. \<phi> = \<psi>1 \<^bold>\<longrightarrow> \<psi>2)) \<and> 
  ((\<exists>x \<psi>. \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<^bold>\<forall>x\<^bold>. \<psi>)) \<longleftrightarrow> (\<exists>x \<psi>. \<phi> = (\<^bold>\<forall>x\<^bold>. \<psi>)))\<close>
  using formsubst_structure_bot formsubst_structure_pred formsubst_structure_imp formsubst_structure_all
  by auto

lemma formsubst_fv: \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = {x. \<exists>y. y \<in> (FV \<phi>) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
proof (induction \<phi> arbitrary: \<sigma> rule:form.induct)
  case (Atom x1 x2)
  have \<open>FV (Atom x1 x2 \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<Union>a \<in> set x2. FVT (a  \<cdot> \<sigma>))\<close>
    by auto
  also have \<open>... = {x. \<exists>y. y \<in> (\<Union>a \<in> set x2. FVT a) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
  proof 
    show \<open>(\<Union>a\<in>set x2. FVT (a \<cdot> \<sigma>)) \<subseteq> {x. \<exists>y. y \<in> (\<Union>a\<in>set x2. FVT a) \<and> x \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
    proof
      fix v
      assume \<open>v \<in> (\<Union>a\<in>set x2. FVT (a \<cdot> \<sigma>))\<close>
      then obtain a where a_is: \<open>a \<in> set x2\<close> \<open>v \<in> FVT (a \<cdot> \<sigma>)\<close>
        by auto
      then obtain ya where \<open>ya \<in> FVT a\<close> \<open>v \<in> FVT (Var ya \<cdot> \<sigma>)\<close>
        using eval_term.simps(1) vars_term_subst_apply_term by force
      then show \<open>v \<in> {x. \<exists>y. y \<in> (\<Union>a\<in>set x2. FVT a) \<and> x \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
        using a_is by auto
    qed
  next
    show \<open>{x. \<exists>y. y \<in> (\<Union>a\<in>set x2. FVT a) \<and> x \<in> FVT (Var y \<cdot> \<sigma>)} \<subseteq> (\<Union>a\<in>set x2. FVT (a \<cdot> \<sigma>))\<close>
    proof
      fix v
      assume \<open>v \<in> {x. \<exists>y. y \<in> (\<Union>a\<in>set x2. FVT a) \<and> x \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
      then obtain yv where \<open>yv \<in> (\<Union>a\<in>set x2. FVT a)\<close> \<open>v \<in> FVT (Var yv \<cdot> \<sigma>)\<close>
        by auto
      then show \<open>v \<in> (\<Union>a\<in>set x2. FVT (a \<cdot> \<sigma>))\<close>
        using vars_term_subst_apply_term by fastforce
    qed
  qed
  also have \<open>... = {x. \<exists>y. y \<in> (FV (Atom x1 x2)) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
    by auto
  finally show ?case .
next
  case (Forall x \<phi>)
  define \<sigma>' where "\<sigma>' = \<sigma>(x := Var x)"
  show ?case
  proof (cases "\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)")
    case True
    then obtain y where y_in: \<open>y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>)\<close> and x_in: \<open>x \<in> FVT (\<sigma>' y)\<close>
      by blast
    then have y_neq_x: \<open>y \<noteq> x\<close> by simp
    then have y_in2: \<open>y \<in> FV \<phi>\<close>
      using y_in by fastforce
    have x_in2: \<open>x \<in> FVT (Var y \<cdot> \<sigma>)\<close>
      using x_in y_neq_x unfolding \<sigma>'_def by simp
  
    define z where "z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))"
    have x_in3: \<open>x \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))\<close>
      using x_in2 y_neq_x by simp

    have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))\<close>
      using z_def formsubst_def_switch
      by (smt (verit, ccfv_threshold) True \<sigma>'_def formsubst.simps(4))
    then have \<open>FV ((\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))} - {z}\<close>
      using Forall[of "\<sigma>(x := Var z)"] using FV.simps(4) by presburger
    also have \<open>... = {xa. \<exists>y. y \<in> FV \<phi> - {x} \<and> xa \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
    proof
      show \<open>{xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))} - {z} \<subseteq> 
        {xa. \<exists>y. y \<in> FV \<phi> - {x} \<and> xa \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
      proof
        fix xa
        assume xa_in: \<open>xa \<in> {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))} - {z}\<close>
        then obtain ya where ya_in: \<open>ya \<in> FV \<phi>\<close> and xa_image: \<open>xa \<in> FVT (Var ya \<cdot> \<sigma>(x := Var z))\<close>
          by blast
        have ya_neq_x: \<open>ya \<noteq> x\<close> using xa_image xa_in by fastforce
        then have \<open>xa \<in> FVT (Var ya \<cdot> \<sigma>)\<close> using xa_image by simp
        moreover have \<open>ya \<in> FV \<phi> - {x}\<close>
          using ya_neq_x ya_in by blast
        ultimately show \<open>xa \<in> {xa. \<exists>y. y \<in> FV \<phi> - {x} \<and> xa \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
          by auto
      qed
    next
      show \<open>{xa. \<exists>y. y \<in> FV \<phi> - {x} \<and> xa \<in> FVT (Var y \<cdot> \<sigma>)} \<subseteq> 
        {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))} - {z}\<close>
      proof
        fix xa
        assume xa_in: \<open>xa \<in> {xa. \<exists>y. y \<in> FV \<phi> - {x} \<and> xa \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
        then obtain ya where ya_in:  \<open>ya \<in> FV \<phi> - {x}\<close> and xa_image: \<open>xa \<in> FVT (Var ya \<cdot> \<sigma>)\<close>
          by blast
        have ya_neq: \<open>ya \<noteq> x\<close> using ya_in by blast
        then have xa_in2: \<open>xa \<in> FVT (Var ya \<cdot> \<sigma>(x := Var z))\<close> using xa_image by simp
        then have \<open>xa \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))\<close> 
          using ya_in Forall by force
        then have \<open>xa \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
          using ya_neq Forall xa_image ya_in unfolding \<sigma>'_def by auto
        then have \<open>xa \<noteq> z\<close> using z_def unfolding variant_def
          by (metis Max_ge Suc_eq_plus1 finite_FV lessI less_le_not_le)
        moreover have \<open>ya \<in> FV \<phi>\<close> using ya_in by blast
        ultimately show \<open>xa \<in> {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> FVT (Var y \<cdot> \<sigma>(x := Var z))} - {z}\<close>
          using xa_in2 by blast
      qed
    qed
    finally show ?thesis by simp
  next
    case False
    then have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
      using formsubst_def_switch \<sigma>'_def by fastforce
    then have \<open>FV ((\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = {z. \<exists>y. y \<in> FV \<phi> \<and> z \<in> FVT (Var y \<cdot> \<sigma>')} - {x}\<close>
      using Forall by simp
    also have \<open>... = {z. \<exists>y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> z \<in> FVT (Var y \<cdot> \<sigma>)}\<close>
      using False unfolding \<sigma>'_def by auto
    finally show ?thesis .
  qed
qed auto

thm formsubst_fv

lemma subst_var: \<open>\<phi> \<cdot>\<^sub>f\<^sub>m Var = \<phi>\<close>
  by (induction \<phi>) auto

lemma formsubst_rename: \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) - {y} = FV \<phi> - {x} - {y}\<close>
proof (cases "y = x")
  case True
  then have \<open>subst x (Var y) = Var\<close>
    by simp
  then have \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) = FV \<phi>\<close>
    using subst_var by metis
  then show ?thesis
    using True by simp
next
  case False
  show ?thesis
  proof
    show \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) - {y} \<subseteq> FV \<phi> - {x} - {y}\<close>
    proof
      fix v
      assume v_in: \<open>v \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) - {y}\<close>
      moreover have \<open>v \<noteq> x\<close>
        using v_in
        by (smt (verit, ccfv_threshold) DiffE Term.term.simps(17) eval_term.simps(1)
            formsubst_fv fun_upd_other insert_iff mem_Collect_eq subst_def subst_simps(1))
      moreover have \<open>v \<in> FV \<phi>\<close>
        by (smt (verit, del_insts) DiffE Term.term.simps(17) eval_term.simps(1) formsubst_fv 
            fun_upd_other mem_Collect_eq subst_def subst_simps(1) subst_var v_in)
      ultimately show \<open>v \<in> FV \<phi> - {x} - {y}\<close>
        by blast
    qed
  next
    show \<open>FV \<phi> - {x} - {y} \<subseteq> FV (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) - {y}\<close>
      using formsubst_fv False by (smt (verit, del_insts) Diff_iff Term.term.simps(17) 
          mem_Collect_eq singleton_iff subsetI subst_ident)
  qed
qed

lemma termsubst_functions_term:
  \<open>functions_term (t \<cdot> \<sigma>) = functions_term t \<union> {x. \<exists>y. y \<in> FVT t \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>)}\<close>
  by (induction t arbitrary: \<sigma>) auto

lemma formsubst_functions_form: 
  \<open>functions_form (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = functions_form \<phi> \<union> {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>)}\<close>
proof (induction \<phi> arbitrary: \<sigma>)
  case Bot
  then show ?case by simp
next
  case (Atom p ts)
  show ?case
    using termsubst_functions_term by auto
next
  case (Implies \<phi> \<psi>)
  then show ?case by auto
next
  case (Forall x \<phi>)
  define \<sigma>' where \<open>\<sigma>' = \<sigma>(x := Var x)\<close>
  define z where \<open>z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>'))\<close>
  have fun_terms_set_eq: \<open>{xa. \<exists>y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> xa \<in> functions_term (Var y \<cdot> \<sigma>)} =
    (if (\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y))
    then {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> functions_term ((Var y) \<cdot> \<sigma>(x := Var z))}
    else {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>')})\<close> (is "?lhs = ?rhs")
  proof
    show \<open>?lhs \<subseteq> ?rhs\<close>
    proof
      fix v
      assume v_in: "v \<in> ?lhs"
      have \<open>\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y) \<Longrightarrow> v \<in> {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> functions_term ((Var y) \<cdot> \<sigma>(x := Var z))}\<close>
        using v_in by auto
      moreover have \<open>\<nexists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y) \<Longrightarrow> v \<in> {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>')}\<close>
        using v_in \<sigma>'_def by auto
      ultimately show "v \<in> ?rhs"
        by argo
    qed
  next
    show \<open>?rhs \<subseteq> ?lhs\<close>
    proof
      fix v
      assume v_in: \<open>v \<in> ?rhs\<close>
      have \<open>\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y) \<Longrightarrow> v \<in> ?lhs\<close>
        using v_in by (smt (verit, del_insts) Diff_empty Diff_insert0 FV.simps(4)
            Term.term.simps(17) empty_iff eval_term.simps(1) eval_with_fresh_var fun_upd_same
            functions_term.simps(1) insertE insert_Diff mem_Collect_eq)
      moreover have \<open>\<nexists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y) \<Longrightarrow> v \<in> ?lhs\<close>
        using v_in by (smt (verit, ccfv_threshold) Diff_iff FV.simps(4) \<sigma>'_def empty_iff
            eval_term.simps(1) fun_upd_other fun_upd_same functions_term.simps(1) insertE
            mem_Collect_eq)
      ultimately show \<open>v \<in> ?lhs\<close>
        by argo
    qed
  qed
  have \<open>functions_form ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = functions_form ((\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m2 \<sigma>)\<close>
    using formsubst_def_switch by simp
  also have \<open>... = (if (\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y))
    then functions_form (\<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>(x := Var z)))
    else functions_form (\<^bold>\<forall> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m2 \<sigma>')))\<close>
    using \<sigma>'_def z_def by (smt (verit) formsubst2.simps(4))
  also have \<open>... = (if (\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y))
    then functions_form \<phi> \<union> {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> functions_term ((Var y) \<cdot> \<sigma>(x := Var z))}
    else functions_form \<phi> \<union> {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>')})\<close>
    using formsubst_def_switch Forall by auto
  also have \<open>... = functions_form \<phi> \<union> (if (\<exists>y. y \<in> FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y))
    then {xa. \<exists>y. y \<in> FV \<phi> \<and> xa \<in> functions_term ((Var y) \<cdot> \<sigma>(x := Var z))}
    else {x. \<exists>y. y \<in> FV \<phi> \<and> x \<in> functions_term ((Var y) \<cdot> \<sigma>')})\<close>
    by auto
  finally show ?case
    using fun_terms_set_eq by auto
qed

lemma formsubst_predicates: \<open>predicates_form (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = predicates_form \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma> rule: predicates_form.induct)
  case (4 x \<phi>)
  then show ?case
    by (metis (no_types, lifting) formsubst.simps(4) predicates_form.simps(4))
qed auto

lemma formsubst_language_rename: \<open>language {\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)} = language {\<phi>}\<close>
  using lang_singleton formsubst_predicates formsubst_functions_form by (simp add: subst_def)

end