(* Title:        Proof of compactness of first-order logic following Harrison's one in HOL-Light
 * Author:       Sophie Tourret <sophie.tourret at inria.fr>, 2023 *)


theory Harrison_FOL_Compactness
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



definition test :: "'a::countable \<Rightarrow> bool" where
  \<open>test x = True\<close>

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

fun eval (* HOL-Light: termval *)
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

(* HOL-Light: termval_termsubst *)
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
    then have x_ex: \<open>\<exists>y. y \<in> FV \<phi> - {x} \<and> x \<in> FVT (\<sigma>' y)\<close>
      by simp
    then have x_in: \<open>x \<in> FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
      using formsubst_fv
      by auto
    define z where \<open>z = variant (FV (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    then have \<open>z \<noteq> x\<close>
      using x_in variant_form by auto
    have \<open>(\<^bold>\<forall> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =  \<^bold>\<forall> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))\<close>
      using z_def True formsubst_def_switch \<sigma>'_def by (smt (verit, best) formsubst.simps(4))
    then have \<open>\<M>,\<beta> \<Turnstile> ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<forall>a \<in> dom \<M>. \<M>,\<beta>(z := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by auto
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>)\<close>
      using Forall by blast
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
    proof
      assume forward: \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using forward by blast
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = 
          ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume v_in: \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> z \<notin> FVT (\<sigma> v)\<close>
            using z_def variant_form by (smt (verit, ccfv_threshold) \<sigma>'_def eval_term.simps(1) 
              formsubst_fv fun_upd_other mem_Collect_eq)
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
            by (simp add: eval_indep_\<beta>_if)
          then have \<open>v \<noteq> x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          moreover have \<open>v = x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          ultimately show 
            \<open>\<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
        qed
        ultimately show \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    next
      assume backward: \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
      show \<open>\<forall>a\<in>dom \<M>. \<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
      proof
        fix a
        assume \<open>a \<in> dom \<M>\<close>
        then have \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>\<close>
          using backward by auto
        moreover have \<open>\<forall>v\<in>FV \<phi>. (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = 
          ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
        proof
          fix v
          assume v_in: \<open>v \<in> FV \<phi>\<close>
          then have \<open>v \<noteq> x \<Longrightarrow> z \<notin> FVT (\<sigma> v)\<close>
            using z_def variant_form by (smt (verit, ccfv_threshold) \<sigma>'_def eval_term.simps(1) 
              formsubst_fv fun_upd_other mem_Collect_eq)
          then have \<open>v \<noteq> x \<Longrightarrow> \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
            by (simp add: eval_indep_\<beta>_if)
          then have \<open>v \<noteq> x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          moreover have \<open>v = x \<Longrightarrow>
            (\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) v = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
          ultimately show 
            \<open>\<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = ((\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a)) v\<close>
            by auto
        qed
        ultimately show \<open>\<M>,(\<lambda>v. \<lbrakk>(\<sigma>(x := Var z)) v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup>) \<Turnstile> \<phi>\<close>
          using holds_indep_\<beta>_if by fast
      qed
    qed
    also have \<open>... = (\<forall>a \<in> dom \<M>. \<M>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>)(x := a) \<Turnstile> \<phi>)\<close>
      by (smt (verit, ccfv_SIG) fun_upd_apply holds_indep_\<beta>_if)
    also have \<open>... = (\<M>,(\<lambda>v. \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>) \<Turnstile> (\<^bold>\<forall> x\<^bold>. \<phi>))\<close>
      by auto
    finally show ?thesis .
  qed
qed auto

definition satisfies :: "'m intrp \<Rightarrow> form set \<Rightarrow> bool" where
  \<open>satisfies \<M> S \<equiv> (\<forall>\<beta> \<phi>. is_vars (dom \<M>) \<beta> \<and> \<phi> \<in> S \<longrightarrow> \<M>,\<beta> \<Turnstile> \<phi>)\<close>


(* propositional compactness *)

fun qfree :: \<open>form \<Rightarrow> bool\<close> where
  \<open>qfree \<^bold>\<bottom> = True\<close>
| \<open>qfree (Atom p ts) = True\<close>
| \<open>qfree (\<phi> \<^bold>\<longrightarrow> \<psi>) = (qfree \<phi> \<and> qfree \<psi>)\<close>
| \<open>qfree (\<^bold>\<forall> x\<^bold>. \<phi>) = False\<close>


lemma qfree_no_quantif: \<open>qfree r \<Longrightarrow> \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)\<close>
  using qfree.simps(3) qfree.simps(4) by blast



(* typedef qfree_form = \<open>{\<phi>::form. qfree \<phi>}\<close>
  using qfree.simps(1) by blast 

setup_lifting type_definition_qfree_form *)

(* != propositional compactness is not proved as in Harrison.
      Instead the existing AFP entry is reused *)

fun form_to_formula :: "form \<Rightarrow> (nat\<times>nterm list) formula" where
  \<open>form_to_formula \<^bold>\<bottom> = \<bottom>\<close>
| \<open>form_to_formula (Atom p ts) = formula.Atom (p,ts)\<close>
| \<open>form_to_formula (\<phi> \<^bold>\<longrightarrow> \<psi>) = Imp (form_to_formula \<phi>) (form_to_formula \<psi>)\<close>
| \<open>form_to_formula (\<^bold>\<forall> x\<^bold>. \<phi>) = \<bottom>\<close>

fun pholds :: \<open>(form \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool\<close> (\<open>_ \<Turnstile>\<^sub>p _\<close> [30, 80] 80) where
  \<open>I \<Turnstile>\<^sub>p \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>I \<Turnstile>\<^sub>p Atom p ts \<longleftrightarrow> I (Atom p ts)\<close>
| \<open>I \<Turnstile>\<^sub>p \<phi> \<^bold>\<longrightarrow> \<psi> \<longleftrightarrow> ((I \<Turnstile>\<^sub>p \<phi>) \<longrightarrow> (I \<Turnstile>\<^sub>p \<psi>))\<close>
| \<open>I \<Turnstile>\<^sub>p (\<^bold>\<forall> x\<^bold>. \<phi>) \<longleftrightarrow> I (\<^bold>\<forall> x\<^bold>. \<phi>)\<close>

definition psatisfiable :: "form set \<Rightarrow> bool" where
  \<open>psatisfiable S \<equiv> \<exists>I. \<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>

definition val_to_prop_val :: "(form \<Rightarrow> bool) \<Rightarrow> ((nat \<times> nterm list) \<Rightarrow> bool)" where
  \<open>val_to_prop_val I = (\<lambda>x. I (Atom (fst x) (snd x)))\<close>

lemma pentails_equiv: \<open>qfree \<phi> \<Longrightarrow> (I \<Turnstile>\<^sub>p \<phi> \<equiv> (val_to_prop_val I) \<Turnstile> (form_to_formula \<phi>))\<close>
proof (induction \<phi>)
  case Bot
  then show ?case
    unfolding val_to_prop_val_def by simp
next
  case (Atom x1 x2)
  then show ?case
    unfolding val_to_prop_val_def by simp
next
  case (Implies \<phi>1 \<phi>2)
  then have \<open>qfree \<phi>1\<close> and \<open>qfree \<phi>2\<close> by simp+
  then have \<open>I \<Turnstile>\<^sub>p \<phi>1 = val_to_prop_val I \<Turnstile> form_to_formula \<phi>1\<close> and
            \<open>I \<Turnstile>\<^sub>p \<phi>2 = val_to_prop_val I \<Turnstile> form_to_formula \<phi>2\<close>
    using Implies(1) Implies(2) by simp+
  then show ?case by simp
next
  case (Forall x1 \<phi>)
  then have False by simp
  then show ?case by simp
qed

lemma pentails_equiv_set:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>psatisfiable S \<equiv> sat (form_to_formula ` S)\<close>
proof -
  {
    assume psat_s: \<open>psatisfiable S\<close>
    then obtain I where I_is: \<open>\<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>
      unfolding psatisfiable_def by blast
    define \<A> where \<open>\<A> = val_to_prop_val I\<close>
    then have \<open>\<forall>\<phi>\<in>S. \<A> \<Turnstile> (form_to_formula \<phi>)\<close>
      using pentails_equiv all_qfree I_is by blast
    then have \<open>sat (form_to_formula ` S)\<close>
      unfolding sat_def by blast
  }
  moreover {
    assume \<open>sat (form_to_formula ` S)\<close>
    then obtain \<A> where a_is: \<open>\<forall>\<phi>\<in>S. \<A> \<Turnstile> form_to_formula \<phi>\<close>
      by (meson image_eqI sat_def)
    define I where i_is: \<open>I = (\<lambda>x. \<A> (pred x, args x))\<close>
    then have \<open>\<A> = val_to_prop_val I\<close>
      unfolding val_to_prop_val_def by simp
    then have \<open>\<forall>\<phi>\<in>S. I \<Turnstile>\<^sub>p \<phi>\<close>
      using pentails_equiv all_qfree a_is by blast
    then have \<open>psatisfiable S\<close>
      unfolding psatisfiable_def by auto
  }
  ultimately show \<open>psatisfiable S \<equiv> sat (form_to_formula ` S)\<close>
    by argo
qed

definition finsat :: "form set \<Rightarrow> bool" where
  \<open>finsat S \<equiv> \<forall>T\<subseteq>S. finite T \<longrightarrow> psatisfiable T\<close>

lemma finsat_fin_sat_eq:
  assumes all_qfree: \<open>\<forall>\<phi>\<in>S. qfree \<phi>\<close>
  shows \<open>finsat S \<equiv> fin_sat (form_to_formula ` S)\<close>
proof -
  {
    assume finsat_s: \<open>finsat S\<close>
    have \<open>fin_sat (form_to_formula ` S)\<close>
      unfolding fin_sat_def
    proof clarsimp
      fix s
      assume 
        s_in: "s \<subseteq> form_to_formula ` S" and
        fin_s: \<open>finite s\<close>
      then obtain t where \<open>t \<subseteq> S\<close> and \<open>s = form_to_formula ` t\<close> and \<open>finite t\<close>
        by (meson finite_subset_image)
      then show "sat s"
        using pentails_equiv_set[of t] all_qfree by (meson finsat_s finsat_def subsetD)
      qed
  }
  moreover
  {
    assume fin_sat_s: \<open>fin_sat (form_to_formula ` S)\<close>
    have \<open>finsat S\<close>
      unfolding finsat_def
    proof clarsimp
      fix T
      assume
        \<open>T \<subseteq> S\<close> and
        \<open>finite T\<close>
      then show \<open>psatisfiable T\<close>
        using pentails_equiv_set fin_sat_s unfolding fin_sat_def
        by (meson assms finite_imageI image_mono subset_iff)
    qed
  }
  ultimately show \<open>finsat S \<equiv> fin_sat (form_to_formula ` S)\<close>
    by argo
qed

lemma psatisfiable_mono: \<open>psatisfiable S  \<Longrightarrow> T \<subseteq> S \<Longrightarrow> psatisfiable T\<close>
  unfolding psatisfiable_def by blast

lemma finsat_mono: \<open>finsat S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> finsat T\<close>
  unfolding finsat_def by blast

lemma finsat_satisfiable: \<open>psatisfiable S \<Longrightarrow> finsat S\<close>
  unfolding psatisfiable_def finsat_def by blast

lemma prop_compactness: \<open>(\<forall>\<phi> \<in> S. qfree \<phi>) \<Longrightarrow> finsat S = psatisfiable S\<close>
proof -
  assume all_qfree: \<open>\<forall>\<phi> \<in> S. qfree \<phi>\<close>
  have \<open>finsat S = fin_sat (form_to_formula ` S)\<close>
    using finsat_fin_sat_eq[OF all_qfree] by simp
  also have \<open>... = sat (form_to_formula ` S)\<close>
    using compactness[of "form_to_formula ` S"] by argo
      (* for this step, countability of formula and term was critical!!!*)
  also have \<open>... = psatisfiable S\<close>
    using pentails_equiv_set[OF all_qfree] by simp
  finally show \<open>finsat S = psatisfiable S\<close>
    . 
qed

(* prenex normal form *)

inductive is_prenex :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> is_prenex \<phi>\<close> 
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
| \<open>is_prenex \<phi> \<Longrightarrow> is_prenex (\<^bold>\<exists>x\<^bold>. \<phi>)\<close>

inductive universal :: "form \<Rightarrow> bool" where
  \<open>qfree \<phi> \<Longrightarrow> universal \<phi>\<close>
| \<open>universal \<phi> \<Longrightarrow> universal (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>

fun size :: "form \<Rightarrow> nat" where
  \<open>size \<^bold>\<bottom> = 1\<close>
| \<open>size (Atom p ts) = 1\<close>
| \<open>size (\<phi> \<^bold>\<longrightarrow> \<psi>) = size \<phi> + size \<psi>\<close>
| \<open>size (\<^bold>\<forall> x\<^bold>. \<phi>) = 1 + size \<phi>\<close>

lemma wf_size: \<open>wfP (\<lambda>\<phi> \<psi>. size \<phi> < size \<psi>)\<close>
  by (simp add: wfP_if_convertible_to_nat)

(*
instantiation form :: wellorder
begin

definition less_eq_form where less_eq_size: \<open>\<phi> \<le> \<psi> \<longleftrightarrow> (size \<phi> = size \<psi>) \<or> (size \<phi> < size \<psi>)\<close>

definition less_form where less_size: \<open>\<phi> < \<psi> \<longleftrightarrow> size \<phi> < size \<psi>\<close>

instance
proof
  fix \<phi> \<psi>::form
  show \<open>(\<phi> < \<psi>) = (\<phi> \<le> \<psi> \<and> \<not> \<psi> \<le> \<phi>)\<close>
    using less_eq_size less_size by presburger
next
  fix \<phi>::form
  show \<open>\<phi> \<le> \<phi>\<close> 
    using less_eq_size by simp
next
  fix \<phi> \<psi> \<xi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<xi> \<Longrightarrow> \<phi> \<le> \<xi>\<close>
    using less_eq_size by auto
next
  fix \<phi> \<psi>::form
  show \<open>\<phi> \<le> \<psi> \<Longrightarrow> \<psi> \<le> \<phi> \<Longrightarrow> \<phi> = \<psi>\<close>
(* not true! ! ! *)
    oops
end
*)

lemma size_indep_subst: \<open>size (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = size \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma>)
  case (Forall x \<phi>)
  have \<open>\<exists>z \<sigma>'.(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by (meson formsubst.simps(4))
  then obtain z \<sigma>' where \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')\<close>
    by blast
  then have \<open>size ((\<^bold>\<forall>x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = size (\<^bold>\<forall>z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>'))\<close>
    by argo
  also have \<open>... = size (\<^bold>\<forall>x\<^bold>. \<phi>)\<close>
    using Forall by auto
  finally show ?case .
qed auto


lemma prenex_distinct: \<open>(\<^bold>\<forall>x\<^bold>. \<phi>) \<noteq> (\<^bold>\<exists>y\<^bold>. \<psi>)\<close>
  by auto

(*
inductive to_prenex to_prenex_left to_prenex_right where
  \<open>to_prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>to_prenex (Atom p ts) = Atom p ts\<close>
| \<open>to_prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = to_prenex_left (to_prenex \<phi>) (to_prenex \<psi>)\<close>
| \<open>to_prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (to_prenex \<phi>)\<close>
| \<open>to_prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = \<^bold>\<forall>x\<^bold>. (to_prenex_left \<phi> \<psi>)\<close> (*TODO: just a test, to correct *)
| \<open>to_prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = \<^bold>\<exists>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
| \<open>qfree \<phi> \<Longrightarrow> to_prenex_left \<phi> \<psi> = \<phi> \<^bold>\<longrightarrow> \<psi>\<close>
| \<open>to_prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = \<^bold>\<forall>x\<^bold>. (to_prenex_right \<phi> \<psi>)\<close>
*)
(*   let y = VARIANT(FV(p) UNION FV(!!x q)) in
                   !!y (Prenex_right p (formsubst (valmod (x,V y) V) q)))  *)

lemma uniq_all_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)" (* necessaire pour décharger le "THE" *)
  using Uniq_def by blast

lemma uniq_all_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_all_x Uniq_def
  by (smt (verit, ccfv_threshold) form.inject(3))

lemma uniq_ex_x: "Uniq (\<lambda>x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)"
  using Uniq_def by blast

lemma uniq_ex_p: \<open>Uniq ((\<lambda>p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p))\<close>
  using uniq_ex_x Uniq_def
  by (smt (verit, best) form.inject(2) form.inject(3))

definition ppat :: "(nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (nat \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> (form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> form" where
  \<open>ppat A B C r = (if (\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) then
    A (THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p) (THE p. r = \<^bold>\<forall>(THE x. \<exists>p. r = \<^bold>\<forall>x\<^bold>. p)\<^bold>. p)
  else (if \<exists>x p. r = \<^bold>\<exists>x\<^bold>. p then
    B (THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p) (THE p. r = \<^bold>\<exists>(THE x. \<exists>p. r = \<^bold>\<exists>x\<^bold>. p)\<^bold>. p) 
   else C r))\<close>

lemma ppat_simpA: \<open>\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p\<close>
  unfolding ppat_def by simp

(* simplified unneeded hypotheses: (\<forall>x p. ppat A B C (\<^bold>\<forall>x\<^bold>. p) = A x p) \<Longrightarrow> (\<forall>x p. ppat A B C (\<^bold>\<exists>x\<^bold>. p) = B x p) *)
lemma ppat_last: \<open>(\<forall>r. \<not>(\<exists>x p. r = \<^bold>\<forall>x\<^bold>. p) \<and> \<not>(\<exists>x p. r = \<^bold>\<exists>x\<^bold>. p)) \<Longrightarrow> ppat A B C r = C r\<close>
  by blast

(* idem here *)
lemma ppat_last_qfree: \<open>qfree r \<Longrightarrow> ppat A B C r = C r\<close>
  using qfree_no_quantif ppat_last by (simp add: ppat_def)

(* holds but useless because not recursive *)
lemma ppat_to_ex_qfree:
  \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = ((A :: form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form) p) x q) \<and>
  (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = (B p) x q) \<and> 
  (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q))\<close>
proof
  define f where \<open>f = (\<lambda>p q. ppat (A p) (B p) (C p) q)\<close>
  have A_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<forall>x\<^bold>. q) = (A p) x q)\<close> and 
    B_eq: \<open>(\<forall>x p q. ppat (A p) (B p) (C p) (\<^bold>\<exists>x\<^bold>. q) = (B p) x q)\<close>
    unfolding ppat_def by simp+
  have  C_eq: \<open>(\<forall>p q. qfree q \<longrightarrow> ppat (A p) (B p) (C p) q = (C p) q)\<close>
    using ppat_last_qfree by blast
  show \<open>(\<forall>x p q. f p (\<^bold>\<forall> x\<^bold>. q) = A p x q) \<and> (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p x q) \<and> (\<forall>p q. qfree q \<longrightarrow> f p q = (C p) q)\<close>
    using A_eq B_eq C_eq unfolding f_def by blast
qed

term \<open>\<forall>\<phi>. \<exists>g. \<forall>\<psi>. g \<psi> = ppat (A g \<phi>) (B g \<phi>) (C \<phi>) \<psi>\<close> (* proven subgoal abstraction *)
term \<open>\<exists>f. \<forall>\<phi> \<psi>. f \<phi> \<psi> = ppat (prenex_right_forall f \<phi>) (prenex_right_exists f \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close> (* same after choice *)
term \<open>A g \<phi> = (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
term \<open>A = (\<lambda>g \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

(*
lemma ppat_to_ex_qfree_rec:
  assumes
    \<open>\<exists>(g :: form \<Rightarrow> form). \<forall>p q. g q = ppat (A g p) (B g p) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = A (f p) p x q) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B (f p) p x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
  using assms ppat_last_qfree
sorry


lemma ppat_to_ex_qfree_rec2:
  assumes
    \<open>\<forall>(p :: form). \<exists>g. \<forall>q. g q = ppat (A p g) (B p g) (C p) q\<close>
  shows
    \<open>(\<exists>f. (\<forall>x p q. f p (\<^bold>\<forall>x\<^bold>. q) = (A p (f p) x q)) \<and>
      (\<forall>x p q. f p (\<^bold>\<exists>x\<^bold>. q) = B p (f p) x q) \<and> 
      (\<forall>p q. qfree q \<longrightarrow> f p q = C p q))\<close>
sorry
*)

thm wf_induct

lemma "wfP ((<) :: (nat \<Rightarrow> nat \<Rightarrow> bool))"
  using wfP_less .

thm wfP_less

(*(!f g x. (!z. z << x ==> (f z = g z) /\ S z (f z))
                      ==> (H f x = H g x) /\ S x (H f x))
             ==> ?f:A->B. !x. (f x = H f x)`, *)

(*
WF_EQ = prove
 (`WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\ !y. y << x ==> ~P(y))`
*)

lemma wfP_eq: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow> ((\<exists>(x::'a). P x) \<equiv> (\<exists>x. P x \<and> (\<forall>y. y < x \<longrightarrow> \<not>P y)))\<close>
  by (smt (verit) mem_Collect_eq wfP_eq_minimal)

(*
WF_IND = prove
 (`WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)`,
*)
lemma wfP_ind: \<open>wfP ((<) :: ('a::ord \<Rightarrow> 'a \<Rightarrow> bool)) \<Longrightarrow>
  (\<forall>(x::'a). (\<forall>y. y <  x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x)\<close>
  by (metis wfP_induct)

lemma dependent_wfP_choice:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r"
    and P: "\<And>x f. (\<And>y. R y x \<Longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r"
  shows "\<exists>f. \<forall>x. P f x (f x)"
proof -
  have wf_R: \<open>wf {(x,y). R x y}\<close> using assms(1) unfolding wfP_def .
  have eq_P: \<open>(\<forall>z. (z, x) \<in> {(x, y). R x y} \<longrightarrow> f z = g z) \<Longrightarrow> P f x r = P g x r\<close> for f g x r
    using assms(2) by blast
  have ex_P: \<open>(\<forall>y. (y, x) \<in> {(x, y). R x y} \<longrightarrow> P f y (f y)) \<Longrightarrow> \<exists>r. P f x r\<close> for x f
    using assms(3) by blast
  show \<open>\<exists>f. \<forall>x. P f x (f x)\<close>
    using dependent_wf_choice[of "{(x,y). R x y}" P, OF wf_R] eq_P ex_P by blast
qed

lemma dependent_wfP_choice2:
  fixes P :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "wfP R"
    and adm: "\<And>f g x r. (\<And>z. R z x \<Longrightarrow> f z = g z) \<Longrightarrow> P f x = P g x"
  shows "\<exists>f. \<forall>x. P f x = (f x)"
proof -
  have adm_rel: \<open>(\<forall>z. R z x \<longrightarrow> f z = g z) \<Longrightarrow> (P f x = r) = (P g x = r)\<close> for f g x r
    using adm by fastforce
  have P_rel: \<open>(\<forall>y. R y x \<longrightarrow> P f y = (f y)) \<Longrightarrow> \<exists>r. P f x = r\<close> for x f
    by simp
  show "\<exists>f. \<forall>x. P f x = (f x)"
    using dependent_wfP_choice[of R \<open>\<lambda>f x r. P f x = r\<close>] assms(1) adm_rel P_rel by blast
qed

lemma size_rec: 
  \<open>\<forall>f g x. (\<forall>(z::form). size z < size x \<longrightarrow> (f z = g z)) \<longrightarrow> (H f x = H g x) \<Longrightarrow> (\<exists>f. \<forall>x. f x = H f x)\<close>
  using dependent_wfP_choice2[OF wf_size] by metis

abbreviation prenex_right_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

abbreviation prenex_right_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_right_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p \<phi> (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>

lemma prenex_right_ex: 
  \<open>\<exists>prenex_right. (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>))\<close>
proof -
  have \<open>\<forall>\<phi>. \<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = ppat 
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. prenex_right_only (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
  proof
    fix \<phi>
    define A where \<open>A = (\<lambda>g x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in (\<^bold>\<forall>y\<^bold>. g (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<psi>. (let y = variant(FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_right_only. \<forall>\<psi>. prenex_right_only \<psi> = 
      ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_right_only g:: "form \<Rightarrow> form" and \<psi>
      assume IH: \<open>\<forall>z. size z < size \<psi> \<longrightarrow> prenex_right_only z = g z\<close>
      show \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> =
        ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
      proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'")
        case True
        then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<forall>x\<^bold>. \<psi>'"
          by blast
        then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          A prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = A g x \<psi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<psi>'. \<psi> = \<^bold>\<forall> x\<^bold>. \<psi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<psi>'. \<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'")
          case True
          then obtain x \<psi>' where psi_is: "\<psi> = \<^bold>\<exists>x\<^bold>. \<psi>'"
            by blast
          then have smaller: \<open>size (\<psi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<psi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_right_only) (B prenex_right_only) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi> = 
          B prenex_right_only x \<psi>'\<close>
          unfolding ppat_def by (simp add: psi_is)
        also have \<open>... = B g x \<psi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<psi>. (\<phi> \<^bold>\<longrightarrow> \<psi>)) \<psi>\<close>
          unfolding ppat_def by (simp add: psi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_right. \<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = ppat
                (prenex_right_forall prenex_right \<phi>)
                (prenex_right_exists prenex_right \<phi>) 
                ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    using choice[of "\<lambda>\<phi> p. \<forall>\<psi>. p \<psi> =
            ppat (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<forall>x\<^bold>. \<psi>)) in \<^bold>\<forall>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>x \<psi>. let y = variant (FV \<phi> \<union> FV (\<^bold>\<exists>x\<^bold>. \<psi>)) in (\<^bold>\<exists>y\<^bold>. p (\<psi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              ((\<^bold>\<longrightarrow>) \<phi>) \<psi>"] by blast
  then obtain prenex_right where prenex_right_is: \<open>\<forall>\<phi> \<psi>. prenex_right \<phi> \<psi> = 
    ppat (prenex_right_forall prenex_right \<phi>) (prenex_right_exists prenex_right \<phi>) ((\<^bold>\<longrightarrow>) \<phi>) \<psi>\<close>
    by blast
(* then show each property separately *)
  have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>\<close>
    using prenex_right_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<psi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)\<close>
    using prenex_right_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

 (* is it unique? \<rightarrow> No, it is undefined in the last case if \<not>qfree \<phi>. Use SOME  *)
definition prenex_right where "prenex_right = (SOME prenex_right.
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<forall>x\<^bold>. \<psi>) = prenex_right_forall prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_right \<phi> (\<^bold>\<exists>x\<^bold>. \<psi>) = prenex_right_exists prenex_right \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_right \<phi> \<psi> = (\<phi> \<^bold>\<longrightarrow> \<psi>)))"

abbreviation prenex_left_forall :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_forall \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

abbreviation prenex_left_exists :: "(form \<Rightarrow> form \<Rightarrow> form) \<Rightarrow> form \<Rightarrow> nat \<Rightarrow> form \<Rightarrow> form" where 
  \<open>prenex_left_exists \<equiv> 
    (\<lambda>p \<phi> x \<psi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))) \<psi>)))\<close>

lemma prenex_left_ex:
  \<open>\<exists>prenex_left. (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>)
    \<and> (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>)\<close>
proof -
  have \<open>\<forall>\<psi>. \<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> = ppat
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. prenex_left_only (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
  proof
    fix \<psi>
    define A where \<open>A = (\<lambda>g x \<phi>. (let y = variant(FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. g (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    define B where \<open>B = (\<lambda>p x \<phi>. (let y = variant(FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m (subst x (Var y))))))\<close>
    show \<open>\<exists>prenex_left_only. \<forall>\<phi>. prenex_left_only \<phi> =
      ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    proof (rule size_rec, (rule allI)+, (rule impI))
      fix prenex_left_only g:: "form \<Rightarrow> form" and \<phi>
      assume IH: \<open>\<forall>z. size z < size \<phi> \<longrightarrow> prenex_left_only z = g z\<close>
      show \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> =
        ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
      proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'")
        case True
        then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<forall>x\<^bold>. \<phi>'"
          by blast
        then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
          using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          A prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = A g x \<phi>'\<close>
          unfolding A_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
      next
        case False
        assume falseAll: \<open>\<not>(\<exists>x \<phi>'. \<phi> = \<^bold>\<forall> x\<^bold>. \<phi>')\<close>
        then show ?thesis
        proof (cases "\<exists>x \<phi>'. \<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'")
          case True
          then obtain x \<phi>' where phi_is: "\<phi> = \<^bold>\<exists>x\<^bold>. \<phi>'"
            by blast
          then have smaller: \<open>size (\<phi>' \<cdot>\<^sub>f\<^sub>m \<sigma>) < size \<phi>\<close> for \<sigma>
            using size_indep_subst by simp
        have \<open>ppat (A prenex_left_only) (B prenex_left_only) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi> = 
          B prenex_left_only x \<phi>'\<close>
          unfolding ppat_def by (simp add: phi_is)
        also have \<open>... = B g x \<phi>'\<close>
          unfolding B_def using IH smaller by presburger
        also have \<open>... = ppat (A g) (B g) (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
          unfolding ppat_def by (simp add: phi_is)
        finally show ?thesis .
        next
          case False
          then show ?thesis
            using falseAll ppat_last unfolding ppat_def by argo
        qed 
      qed
    qed
  qed
  then have \<open>\<exists>prenex_left_argswap. \<forall>\<psi> \<phi>. prenex_left_argswap \<psi> \<phi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left_argswap \<psi> (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    using choice[of "\<lambda>\<psi> p. \<forall>\<phi>. p \<phi> =
            ppat (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y))))
              (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall>y\<^bold>. p (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)))
              (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>"] by blast
  then have \<open>\<exists>prenex_left. \<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<forall>x\<^bold>. \<phi>) \<union> FV \<psi>) in (\<^bold>\<exists>y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>))
    (\<lambda>x \<phi>. let y = variant (FV (\<^bold>\<exists>x\<^bold>. \<phi>) \<union> FV \<psi>) in \<^bold>\<forall> y\<^bold>. prenex_left (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var y)) \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by force
  then obtain prenex_left where prenex_left_is: \<open>\<forall>\<phi> \<psi>. prenex_left \<phi> \<psi> = ppat
    (\<lambda>x \<phi>. prenex_left_forall prenex_left \<phi> x \<psi>)
    (\<lambda>x \<phi>. prenex_left_exists prenex_left \<phi> x \<psi>)
    (\<lambda>\<phi>. prenex_right \<phi> \<psi>) \<phi>\<close>
    by blast
  have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> =  prenex_left_forall prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>\<close>
    using prenex_left_is unfolding ppat_def by simp
  moreover have \<open>\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>\<close>
    using prenex_left_is by (metis (no_types, lifting) ppat_last_qfree)
  ultimately show ?thesis
    by blast
qed

definition prenex_left where \<open>prenex_left = (SOME prenex_left.
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<forall>x\<^bold>. \<phi>) \<psi> = prenex_left_forall prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> x \<psi>. prenex_left (\<^bold>\<exists>x\<^bold>. \<phi>) \<psi> = prenex_left_exists prenex_left \<phi> x \<psi>) \<and>
  (\<forall>\<phi> \<psi>. qfree \<phi> \<longrightarrow> prenex_left \<phi> \<psi> = prenex_right \<phi> \<psi>))\<close>

fun prenex where
  \<open>prenex \<^bold>\<bottom> = \<^bold>\<bottom>\<close>
| \<open>prenex (Atom p ts) = Atom p ts\<close>
| \<open>prenex (\<phi> \<^bold>\<longrightarrow> \<psi>) = prenex_left (prenex \<phi>) (prenex \<psi>)\<close>
| \<open>prenex (\<^bold>\<forall>x\<^bold>. \<phi>) = \<^bold>\<forall>x\<^bold>. (prenex \<phi>)\<close>

theorem \<open>is_prenex (prenex \<phi>) \<and> (FV (prenex \<phi>) = FV \<phi>) \<and> (language {prenex \<phi>} = language {\<phi>}) \<and>
  (\<forall>I \<beta>. \<not>(dom I = {}) \<longrightarrow> (I, \<beta> \<Turnstile> (prenex \<phi>)) \<longleftrightarrow> (I, \<beta> \<Turnstile> \<phi>))\<close>
proof (induction \<phi> rule: form.induct)
  case Bot
  then show ?case
    by (metis is_prenex.simps prenex.simps(1) qfree.simps(1))
next
  case (Atom x1 x2)
  then show ?case
    using is_prenex.intros(1) prenex.simps(2) qfree.simps(2) by presburger
next
  case (Implies x1 x2)
  then show ?case sorry
next
  case (Forall x1 x2)
  have \<open>is_prenex (prenex (\<^bold>\<forall> x1\<^bold>. x2))\<close>
    using Forall using is_prenex.intros(2) prenex.simps(4) by presburger
  moreover have \<open>FV (prenex (\<^bold>\<forall> x1\<^bold>. x2)) = FV (\<^bold>\<forall> x1\<^bold>. x2)\<close>
    using Forall FV.simps(4) prenex.simps(4) by presburger
  moreover have \<open>language {prenex (\<^bold>\<forall> x1\<^bold>. x2)} = language {\<^bold>\<forall> x1\<^bold>. x2}\<close>
    using Forall
    sorry
  moreover have \<open>(\<forall>I \<beta>. Harrison_FOL_Compactness.dom I \<noteq> {} \<longrightarrow>
    I,\<beta> \<Turnstile> prenex (\<^bold>\<forall> x1\<^bold>. x2) = I,\<beta> \<Turnstile> (\<^bold>\<forall> x1\<^bold>. x2))\<close>
    using Forall
    sorry
  then show ?case
    sorry
qed

end