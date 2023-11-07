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

(* Comments starting with != indicate discrepancies with Harrison's formalisation *)


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
| \<open>FV (Atom _ ts) = (\<Union> a \<in> set ts. FVT a)\<close>
| \<open>FV (\<phi> \<^bold>\<longrightarrow> \<psi>) = FV \<phi> \<union> FV \<psi>\<close>
| \<open>FV (\<^bold>\<forall> x\<^bold>. \<phi>) = FV \<phi> - {x}\<close>

lemma FV_all_subs: \<open>FV \<phi> \<subseteq> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<union> {x}\<close>
  by fastforce

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

(* needed in HOL-Light but seems trivial in modern Isabelle/HOL *)
lemma \<open>{x. \<exists>y. y \<in> (s \<union> t) \<and> P x y} = {x. \<exists>y. y \<in> s \<and> P x y} \<union> {x. \<exists>y. y \<in> t \<and> P x y}\<close>
  by blast

lemma \<open>FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = {x. \<exists>y. y \<in> (FV \<phi>) \<and> x \<in> FVT ((Var y) \<cdot> \<sigma>)}\<close>
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


locale struct =
  fixes
    M :: \<open>'m set\<close> and
    FN :: \<open>nat \<Rightarrow> 'm list \<Rightarrow> 'm\<close> and
    REL :: \<open>nat \<Rightarrow> 'm list set\<close> 
  assumes
    M_nonempty: \<open>M \<noteq> {}\<close> and 
    FN_dom_to_dom: \<open>\<forall> f es. (\<forall> e \<in> set es. e \<in> M) \<longrightarrow> FN f es \<in> M\<close> and
    REL_to_dom: \<open>\<forall> p. \<forall> es \<in> REL p. \<forall> e \<in> set es. e \<in> M\<close> 

definition is_vars :: \<open>'m set \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> bool\<close> where
  [simp]: \<open>is_vars M \<beta> \<longleftrightarrow> (\<forall> v. \<beta> v \<in> M)\<close> 

typedef 'm intrp =
  \<open>{ (M :: 'm set, FN :: nat \<Rightarrow> 'm list \<Rightarrow> 'm, REL :: nat \<Rightarrow> 'm list set). struct M FN REL }\<close>
  using struct.intro
  by fastforce

setup_lifting type_definition_intrp

lift_definition dom :: \<open>'m intrp \<Rightarrow> 'm set\<close> is fst .
lift_definition interp_fn :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list \<Rightarrow> 'm)\<close> is \<open>fst \<circ> snd\<close> .
lift_definition interp_rel :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm list set)\<close> is \<open>snd \<circ> snd\<close> .

lemma intrp_is_struct: \<open>struct (dom \<M>) (interp_fn \<M>) (interp_rel \<M>)\<close>
  by transfer auto 

lemma dom_Abs_is_fst [simp]: \<open>struct M FN REL \<Longrightarrow> dom (Abs_intrp (M, FN, REL)) = M\<close>
  by (simp add: Abs_intrp_inverse dom.rep_eq) 

lemma interp_fn_Abs_is_fst_snd [simp]: \<open>struct M FN REL \<Longrightarrow> interp_fn (Abs_intrp (M, FN, REL)) = FN\<close>
  by (simp add: Abs_intrp_inverse interp_fn.rep_eq) 

lemma interp_rel_Abs_is_snd_snd [simp]: 
  \<open>struct M FN REL \<Longrightarrow> interp_rel (Abs_intrp (M, FN, REL)) = REL\<close>
  by (simp add: Abs_intrp_inverse interp_rel.rep_eq) 

lemma FN_dom_to_dom: \<open>\<forall> t \<in> set ts. t \<in> dom \<M> \<Longrightarrow> interp_fn \<M> f ts \<in> dom \<M>\<close>
  by (meson intrp_is_struct struct.FN_dom_to_dom) 

fun eval
  :: \<open>nterm \<Rightarrow> 'm intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> 'm\<close>
  (\<open>\<lbrakk>_\<rbrakk>\<^bsup>_,_\<^esup>\<close> [50, 0, 0] 70) where
  \<open>\<lbrakk>Var v\<rbrakk>\<^bsup>_,\<beta>\<^esup> = \<beta> v\<close>
| \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close> 

fun holds
  :: \<open>'m intrp \<Rightarrow> (nat \<Rightarrow> 'm) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_,_ \<Turnstile> _\<close> [30, 30, 80] 80) where
  \<open>\<M>,\<beta> \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<M>,\<beta> \<Turnstile> Atom p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
| \<open>\<M>,\<beta> \<Turnstile> \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((\<M>,\<beta> \<Turnstile> \<phi>) \<longrightarrow> (\<M>,\<beta> \<Turnstile> \<psi>))\<close>
| \<open>\<M>,\<beta> \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> (\<forall>a \<in> dom \<M>. \<M>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>

lemma holds_indep_\<beta>_if:
  \<open>\<forall> v \<in> FV \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v \<Longrightarrow> \<M>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close>
proof (induction \<phi> arbitrary: \<beta>\<^sub>1 \<beta>\<^sub>2)
  case Bot
  then show ?case
    by simp
next
  case (Atom p ts)
  then have \<open>\<forall> t \<in> set ts. \<forall> v \<in> FVT t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
    by simp 
  then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts] = [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts]\<close>
  proof (induction ts) 
    case Nil
    then show ?case
      by simp
  next
    case (Cons a ts)
    then show ?case
    proof (induction a)
      case (Var x)
      then show ?case
        by simp 
    next
      case (Fun f ts')
      then have \<open>\<forall> t \<in> set ts'. \<forall> v \<in> FVT t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
        by simp 
      then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts'] = [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts']\<close>
        using Cons.IH Fun.IH Fun.prems(2)
        by force
      then have \<open>interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts'] = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts']\<close>
        by argo 
      then show ?case
        using Cons.IH Fun.prems(2)
        by force 
    qed
  qed
  then have \<open>[\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>1\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^sub>2\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    by argo
  then show ?case
    by simp
next
  case (Implies \<phi> \<psi>)
  then have
    \<open>\<forall>v \<in> FV \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close> and
    \<open>\<forall>v \<in> FV \<psi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
    by auto
  then have
    \<open>\<M>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close> and
    \<open>\<M>,\<beta>\<^sub>1 \<Turnstile> \<psi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<psi>\<close>
    using Implies.IH by auto
  then show ?case
    by simp
next
  case (Forall x \<phi>)
  then have \<open>\<forall>a \<in> dom \<M>. (\<M>,\<beta>\<^sub>1(x := a) \<Turnstile> \<phi>) = (\<M>,\<beta>\<^sub>2(x := a) \<Turnstile> \<phi>)\<close>
    by simp
  then show ?case 
    by simp
qed

lemma holds_indep_intrp_if:
  fixes
    \<phi> :: form and
    \<M> \<M>' :: \<open>'m intrp\<close> 
  assumes
    dom_eq: \<open>dom \<M> = dom \<M>'\<close> and
    rel_eq: \<open>\<forall> p. interp_rel \<M> p = interp_rel \<M>' p\<close> and
    fn_eq: \<open>\<forall> f ts. (f, length ts) \<in> functions_form \<phi> \<longrightarrow> interp_fn \<M> f ts = interp_fn \<M>' f ts\<close>
  shows
    \<open>\<forall>\<beta>.  \<M>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>',\<beta> \<Turnstile> \<phi>\<close>
  using fn_eq
proof (intro allI impI, induction \<phi>)
  case (Atom p ts)

  have all_fn_sym_in: \<open>(\<Union> t \<in> set ts. functions_term t) \<subseteq> functions_form (Atom p ts)\<close> (is \<open>?A \<subseteq> _\<close>)
    by simp 

  have eval_tm_eq: \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>\<close>
    if \<open>functions_term t \<subseteq> functions_form (Atom p ts)\<close> 
    for t 
    using that
  proof (induction t) 
    case (Fun f ts') 

    have \<open>\<forall> t' \<in> set ts'. functions_term t' \<subseteq> functions_form (Atom p ts)\<close>
      using Fun.prems
      by auto
    moreover have \<open>(f, length [\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']) \<in> functions_form (Atom p ts)\<close>
      using Fun.prems
      by fastforce 
    ultimately show ?case
      using Fun.IH Atom.prems(1)[rule_format, of f \<open>[\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']\<close>] 
      by (smt (verit, del_insts) eval.simps(2) map_eq_conv)
  qed auto 

  have \<open>\<M>,\<beta> \<Turnstile> Atom p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    by simp
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M>' p\<close>
    by (simp add: rel_eq)
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M>' p\<close>
    using eval_tm_eq all_fn_sym_in
    by (metis (mono_tags, lifting) UN_subset_iff map_eq_conv)
  also have \<open>... \<longleftrightarrow> \<M>',\<beta> \<Turnstile> Atom p ts\<close>
    by auto 
  finally show ?case .
next
  case (Forall x \<phi>)

  have \<open>\<M>,\<beta> \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> (\<forall> a \<in> dom \<M>. \<M>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by simp 
  also have \<open>... = (\<forall> a \<in> dom \<M>. \<M>',\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    using Forall.IH Forall.prems by simp
  also have \<open>... = (\<forall> a \<in> dom \<M>'. \<M>',\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by (simp add: dom_eq)
  also have \<open>... = (\<M>',\<beta> \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
    by auto 
  finally show ?case . 
qed auto

abbreviation (input) \<open>eval_subst \<M> \<beta> \<sigma> v \<equiv> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>

lemma subst_lemma_terms: \<open>\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>\<close>
proof (induction t)
  case (Var v)
  then show ?case
    by auto 
next
  case (Fun f ts)

  have \<open>\<lbrakk>Fun f ts \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>Fun f [t \<cdot> \<sigma>. t \<leftarrow> ts]\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
    by auto
  also have \<open>... = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> [t \<cdot> \<sigma>. t \<leftarrow> ts]]\<close>
    by auto 
  also have \<open>... = interp_fn \<M> f [\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    unfolding map_map
    by (meson comp_apply)
  also have \<open>... = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>. t \<leftarrow> ts]\<close>
    using Fun.IH
    by (smt (verit, best) map_eq_conv) 
  also have \<open>... = \<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>\<close>
    by auto 
  finally show ?case .
qed

lemma eval_indep_\<beta>_if:
  assumes \<open>\<forall> v \<in> FVT t. \<beta> v = \<beta>' v\<close>
  shows \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>'\<^esup>\<close>
    using assms
proof (induction t)
  case (Var v)
  then show ?case
    by auto 
next
  case (Fun f ts)
  then show ?case
    by (smt (verit, ccfv_SIG) eval.simps(2) map_eq_conv term.set_intros(4)) 
qed

lemma concat_map: \<open>[f t. t \<leftarrow> [g t. t \<leftarrow> ts]] = [f (g t). t \<leftarrow> ts]\<close> by simp

find_theorems "_(_ := _)" name: Term

lemma \<open>\<nexists>y. x \<in> FVT (\<sigma> y) \<Longrightarrow> \<sigma> x = Var x \<Longrightarrow> (\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) = (\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)\<close>
proof
  fix v
  assume x_idem: \<open>\<sigma> x = Var x\<close> and
    case_false: \<open>\<nexists>y. x \<in> FVT (\<sigma> y)\<close>
  show \<open>\<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
  proof (induction "\<sigma> v")
    case (Var y)
    then show ?case
      proof (cases "y=x")
        case True
        then have \<open>\<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = a\<close>
          using Var by simp
        have \<open>((\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v = (if v = x then a else \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)\<close>
          by simp
        then have \<open>((\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v = a\<close>
          using True Var x_idem
          sorry
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
  next
    case (Fun x1a x2)
    then show ?case sorry
  qed
qed


lemma swap_subst_eval: \<open>\<M>,\<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,(\<lambda>v. eval_subst \<M> \<beta> \<sigma> v) \<Turnstile> \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma> \<beta>)
  case (Atom p ts)
  have \<open>\<M>,\<beta> \<Turnstile> (Atom p ts \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,\<beta> \<Turnstile> (Atom p [t \<cdot> \<sigma>. t \<leftarrow> ts])\<close>
    by auto
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> [t \<cdot> \<sigma>. t \<leftarrow> ts]] \<in> interp_rel \<M> p\<close>
    by auto
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    using concat_map[of "\<lambda>t. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>" "\<lambda>t. t \<cdot> \<sigma>"] by presburger
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    using subst_lemma_terms[of _ \<sigma> \<M> \<beta>] by auto
  finally show ?case
    by simp
next
  case (Forall x \<phi>)
  define \<sigma>' where "\<sigma>' = \<sigma>(x := Var x)"
  show ?case
  proof (cases "\<exists> y. y \<in> FV (\<^bold>\<forall> x\<^bold>. \<phi>) \<and> x \<in> FVT (\<sigma>' y)")
    case False
    then have \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
      using formsubst_def_switch \<sigma>'_def by fastforce
    then have \<open>\<M>,\<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<forall>a \<in> dom \<M>. \<M>,\<beta>(x := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
      by auto
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>)\<close>
      using Forall by blast
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
    proof
      assume forward: \<open>\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using forward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by (metis (mono_tags, lifting) DiffI FV.simps(4) False eval_indep_\<beta>_if fun_upd_other singletonD)
          moreover have \<open>v = x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            using \<sigma>'_def by auto
          ultimately show \<open>\<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by simp
        qed
        ultimately show \<open>\<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    next
      assume backward: \<open>\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using backward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by (metis (mono_tags, lifting) DiffI FV.simps(4) False eval_indep_\<beta>_if fun_upd_other singletonD)
          moreover have \<open>v = x \<Longrightarrow> \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            using \<sigma>'_def by auto
          ultimately show \<open>\<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup> = ((\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by simp
        qed
        ultimately show \<open>\<M>,(\<lambda>v. \<lbrakk>\<sigma>' v\<rbrakk>\<^bsup>\<M>,\<beta>(x := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    qed
    also have \<open>... = (\<M>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
      by (smt (verit, ccfv_SIG) \<sigma>'_def fun_upd_apply holds.simps(4) holds_indep_\<beta>_if)
    finally show ?thesis .
  next
    case True
    define z where \<open>z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    then have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =  \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))\<close>
      using True formsubst_def_switch \<sigma>'_def by (smt (verit, best) formsubst.simps(4))
    then have \<open>\<M>,\<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<forall>a \<in> dom \<M>. \<M>,\<beta>(z := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by auto
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>)\<close>
      using Forall by blast
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(z := a) \<Turnstile> \<phi>)\<close>
    proof
      assume forward: \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(z := a) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using forward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(z := a)) v\<close>
          sorry
        ultimately show \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(z := a) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    next
      assume backward: \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(z := a) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
        sorry
    qed
    then show ?thesis sorry
  qed

qed auto


end