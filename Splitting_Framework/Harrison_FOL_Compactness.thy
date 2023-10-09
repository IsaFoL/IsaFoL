(* Title:        Proof of compactness of first-order logic following Harrison's one in HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)


theory Harrison_FOL_Compactness
  imports
    Main
    HOL.Zorn
    First_Order_Terms.Term
begin

(* This heavily reuses Ghilain's FOL_Compactness code, with simplifications for nat type
   and renamings to follow Harrison's text *)

(* Comments starting with != indicate discrepencies with Harrison's formalisation *)


type_synonym nterm = \<open>(nat, nat) term\<close>


fun functions_term :: \<open>nterm \<Rightarrow> (nat \<times> nat) set\<close> where
  \<open>functions_term (Var _) = {}\<close>
| \<open>functions_term (Fun f ts) = {(f, length ts)} \<union> (\<Union> t \<in> set ts. functions_term t)\<close>

datatype form =
  Bot (\<open>\<^bold>\<bottom>\<close>)
| Atom nat \<open>nterm list\<close>
| Implies form form (infixl \<open>\<^bold>\<longrightarrow>\<close> 85)
| Forall nat form (\<open>\<^bold>\<forall> _\<^bold>. _\<close> [0, 70] 70)

thm form.induct

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

lemma \<open>language {p} = (functions_form p, predicates_form p)\<close>
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

abbreviation FVT :: \<open>nterm \<Rightarrow> nat set\<close> where
  \<open>FVT \<equiv> vars_term\<close>

fun FV :: \<open>form \<Rightarrow> nat set\<close> where
  \<open>FV \<^bold>\<bottom> = {}\<close>
| \<open>FV (Atom _ args') = (\<Union> a \<in> set args'. FVT a)\<close>
| \<open>FV (\<phi> \<^bold>\<longrightarrow> \<psi>) = FV \<phi> \<union> FV \<psi>\<close>
| \<open>FV (\<^bold>\<forall> x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>

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

fun formsubst :: \<open>form \<Rightarrow> (nat, nat) subst \<Rightarrow> form\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m _ = \<^bold>\<bottom>\<close> 
| \<open>(Atom p ts) \<cdot>\<^sub>f\<^sub>m \<sigma> = Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<phi> \<^bold>\<longrightarrow> \<psi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<^bold>\<longrightarrow> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
| \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =
    (let \<sigma>' = \<sigma>(x := Var x);
         z = if \<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)
             then variant (FV (\<^bold>\<forall> x\<^bold>. \<phi>)) else x in
    \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>

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
    then have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (let z = variant (FV (\<^bold>\<forall> x\<^bold>. \<phi>)) in \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by (simp add: \<sigma>''_def)
    also have \<open>... = (let z = variant (FV (\<^bold>\<forall> x\<^bold>. \<phi>)) in \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'(x := Var z)))\<close>
      using sig_x_subst by (metis Forall.IH)
    also have \<open>... = (\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>'\<close>
      using True \<sigma>'''_def ex_var_equiv formsubst.simps(4) by presburger
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using Forall.IH \<sigma>'''_def \<sigma>''_def ex_var_equiv sig_x_subst by auto
  qed
qed

(* needed in HOL-Light but seems trivial in modern Isabelle/HOL *)
lemma \<open>{x. \<exists>y. y \<in> (s \<union> t) \<and> P x y} = {x. \<exists>y. y \<in> s \<and> P x y} \<union> {x. \<exists>y. y \<in> t \<and> P x y}\<close>
  by blast


lemma \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = {x. \<exists>y. y \<in> (FV \<phi>) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
proof (induction \<phi> arbitrary: \<sigma> rule:form.induct)
  case Bot
  then show ?case by simp
next
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
  case (Implies \<phi>1 \<phi>2)
  then show ?case by auto
next
  case (Forall x \<phi>)
  define \<sigma>' where "\<sigma>' = \<sigma>(x := Var x)"
  have \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z} = FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {y}\<close> for y z
  proof
    have \<open>y \<notin> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z}\<close>
    proof (rule ccontr)
      assume \<open>\<not> y \<notin> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z}\<close>
      then have \<open>y \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z))\<close>
        by auto
      then have \<open>Var y \<in> \<sigma>(y := Var z) ` (UNIV::nat set)\<close>
        sorry
      then show False
        sorry
    qed
    show \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z} \<subseteq> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {y}\<close>
    proof
      fix x
      assume \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z}\<close>
      show \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {y}\<close>
        sorry 
    qed
  next
    show \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {y} \<subseteq> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z}\<close>
    proof
      fix x
      assume \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {y}\<close>
      show \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var z)) - {z}\<close>
        sorry
    qed
  qed
  show ?case
  proof (cases \<open>\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)\<close>)
    case True
    then have \<open>FV ((\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) =
      FV ((let z = variant (FV (\<^bold>\<forall> x\<^bold>. \<phi>)) in \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))))\<close>
      by (simp add: \<sigma>'_def)
    also have \<open>... = (let z = variant (FV (\<^bold>\<forall> x\<^bold>. \<phi>)) in FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)) - {z})\<close>
      by (meson FV.simps(4))
    also have \<open>... = FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) - {x}\<close>
      sorry
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed


end