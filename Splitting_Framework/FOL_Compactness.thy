theory FOL_Compactness
  imports
    Main
    HOL.Zorn
    Ordered_Resolution_Prover.Clausal_Logic
    First_Order_Terms.Term
    "HOL-Library.FuncSet"
    "HOL-Library.Countable"
begin

(* TODO: Review the notations used!! *)


text \<open>
  On-going formalisation of ``Le nec plus ultra du théorème de compacité'' by Pierre Cagne.

  Basically, we define a Tarski entailment and prove that it is compact.
\<close>

no_syntax
  "_MapUpd"  :: "['a ⇀ 'b, maplets] ⇒ 'a ⇀ 'b" ("_/'(_')" [900, 0] 900)

section \<open>Preliminaries\<close>

text \<open>
  First-order terms:
  \<^item> Variables of abstract type \<open>'v\<close>;
  \<^item> Constants of abstract type \<open>'c\<close>;
  \<^item> Or function applications on terms.

  Note that our \<open>tm\<close> type models constants as 0-ary functions, i.e. \<open>c()\<close>.
\<close> 

(* Definition 1.1 *)
type_synonym ('f, 'v) tm = \<open>('f, 'v) term\<close> 

text \<open>
  First-order formulas:
  \<^item> N-ary relation (predicate) applications on terms;
  \<^item> Negation of a formula;
  \<^item> Conjunction of two formulas;
  \<^item> Existential quantification.
\<close>

(* Definition 1.2 *)
datatype ('f, 'p, 'v) fm =
  Rel 'p \<open>('f, 'v) tm list\<close>
| Negation \<open>('f, 'p, 'v) fm\<close> (\<open>\<^bold>\<not> _\<close> [90] 90)
| Conjunction \<open>('f, 'p, 'v) fm\<close> \<open>('f, 'p, 'v) fm\<close> (infixl \<open>\<^bold>\<and>\<close> 85)
| Existential 'v \<open>('f, 'p, 'v) fm\<close> (\<open>\<^bold>\<exists> _\<^bold>. _\<close> [0, 70] 70)
| Bot (\<open>\<^bold>\<bottom>\<close>)

fun is_atomic :: \<open>('f, 'p, 'v) fm \<Rightarrow> bool\<close> where
  \<open>is_atomic (Rel _ _) = True\<close>
| \<open>is_atomic _ = False\<close>

text \<open>
  Some input shortcuts (because we can). 
\<close> 

abbreviation (input) Forall :: \<open>'v \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm\<close> (\<open>\<^bold>\<forall> _\<^bold>. _\<close> [0, 70] 70) where
  \<open>\<^bold>\<forall> x\<^bold>. \<phi> \<equiv> \<^bold>\<not> (\<^bold>\<exists> x\<^bold>. \<^bold>\<not> \<phi>)\<close>

abbreviation (input) Disjunction :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm\<close>
  (infixl \<open>\<^bold>\<or>\<close> 84) where
  \<open>\<phi> \<^bold>\<or> \<psi> \<equiv> \<^bold>\<not> (\<^bold>\<not> \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<close>

abbreviation (input) Implication :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm\<close>
  (infixr \<open>\<^bold>\<longrightarrow>\<close> 70) where
  \<open>\<phi> \<^bold>\<longrightarrow> \<psi> \<equiv> \<^bold>\<not> \<phi> \<^bold>\<or> \<psi>\<close>

abbreviation (input) Equivalence :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm\<close>
  (infix \<open>\<^bold>\<longleftrightarrow>\<close> 70) where
  \<open>\<phi> \<^bold>\<longleftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<longrightarrow> \<psi> \<^bold>\<and> \<psi> \<^bold>\<longrightarrow> \<phi>)\<close> 

abbreviation (input) Top :: \<open>('f, 'p, 'v) fm\<close> (\<open>\<^bold>\<top>\<close>) where
  \<open>\<^bold>\<top> \<equiv> \<^bold>\<not> \<^bold>\<bottom>\<close> 

text \<open>
  We also define the notion of free and bound variables.
  A free variable occurrence is an occurrence not appearing in the scope of any quantifier.
  For example, the first occurrence of \<open>x\<close> in the formula \<open>(x \<^bold>\<doteq> y) \<^bold>\<longleftrightarrow> (\<^bold>\<exists> x\<^bold>. x \<^bold>\<doteq> y)\<close> is free, while
  the second is bound (assuming that a predicate \<open>\<^bold>\<doteq>\<close> of arity 2 is defined).
\<close> 

fun size_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> nat\<close> where
  \<open>size_fm \<^bold>\<bottom> = 1\<close>
| \<open>size_fm (Rel p ts) = 1\<close>
| \<open>size_fm (\<^bold>\<not> \<phi>) = 1 + size_fm \<phi>\<close>
| \<open>size_fm (\<phi> \<^bold>\<and> \<psi>) = size_fm \<phi> + size_fm \<psi>\<close>
| \<open>size_fm (\<^bold>\<exists> x\<^bold>. \<phi>) = 1 + size_fm \<phi>\<close> 

lemma [measure_function]: \<open>is_measure size_fm\<close> ..

abbreviation FV_tm :: \<open>('f, 'v) tm \<Rightarrow> 'v set\<close> where
  \<open>FV_tm \<equiv> vars_term\<close>

fun FV_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> 'v set\<close> where
  \<open>FV_fm (Rel _ args') = (\<Union> a \<in> set args'. FV_tm a)\<close>
| \<open>FV_fm (\<^bold>\<not> \<phi>) = FV_fm \<phi>\<close>
| \<open>FV_fm (\<phi> \<^bold>\<and> \<psi>) = FV_fm \<phi> \<union> FV_fm \<psi>\<close>
| \<open>FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>) = FV_fm \<phi> - {x}\<close>
| \<open>FV_fm \<^bold>\<bottom> = {}\<close>

lemma finite_FV_fm: \<open>finite (FV_fm \<phi>)\<close>
  by (induction \<phi>, auto) 

fun subst_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'p, 'v) fm\<close> (infixl \<open>\<cdot>\<^sub>f\<^sub>m\<close> 75) where
  \<open>\<^bold>\<bottom> \<cdot>\<^sub>f\<^sub>m _ = \<^bold>\<bottom>\<close> 
| \<open>(Rel p ts) \<cdot>\<^sub>f\<^sub>m \<sigma> = Rel p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
| \<open>(\<^bold>\<not> \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = \<^bold>\<not> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
| \<open>(\<phi> \<^bold>\<and> \<psi>) \<cdot>\<^sub>f\<^sub>m \<sigma> = (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<^bold>\<and> (\<psi> \<cdot>\<^sub>f\<^sub>m \<sigma>)\<close>
| \<open>(\<^bold>\<exists> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma> =
    (let \<sigma>' = \<sigma>(x := Var x);
         z = if \<exists> y. y \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>) \<and> x \<in> FV_tm (\<sigma>' y)
             then (\<some> z. z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>')) else x in
    \<^bold>\<exists> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close> 

lemma [termination_simp]: \<open>size_fm (subst_fm \<phi> \<sigma>) = size_fm \<phi>\<close>
proof (induction \<phi> arbitrary: \<sigma>)
  case (Existential x \<phi>)
  then show ?case
    by (metis (no_types, lifting) size_fm.simps(5) subst_fm.simps(5)) 
qed auto

text \<open>
  A formula \<open>\<phi>\<close> is in Clausal Normal Form (CNF) if:
  \<^item> it is the empty clause \<open>\<^bold>\<bottom>\<close>, or
  \<^item> it is the application of a predicate, or
  \<^item> it is the negation of the application of a predicate, or
  \<^item> it is of the form \<open>\<psi> \<^bold>\<or> \<rho>\<close> where \<open>\<psi>\<close> and \<open>\<rho>\<close> are in CNF.
\<close>

fun is_cnf :: \<open>('f, 'p, 'v) fm \<Rightarrow> bool\<close> where
  \<open>is_cnf (\<phi> \<^bold>\<or> \<psi>) \<longleftrightarrow> is_cnf \<phi> \<and> is_cnf \<psi>\<close>
| \<open>is_cnf (Rel _ _) \<longleftrightarrow> True\<close>
| \<open>is_cnf (\<^bold>\<not> Rel _ _) \<longleftrightarrow> True\<close>
| \<open>is_cnf \<^bold>\<bottom> \<longleftrightarrow> True\<close>
| \<open>is_cnf _ \<longleftrightarrow> False\<close>

(* fun eq_upto_renaming :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close> (infix \<open>\<equiv>\<^sub>R\<close> 50) where
 *   \<open>\<^bold>\<bottom> \<equiv>\<^sub>R \<^bold>\<bottom> \<longleftrightarrow> True\<close>
 * | \<open>Rel p ts \<equiv>\<^sub>R Rel p' ts' \<longleftrightarrow> p = p' \<and> ts = ts'\<close>
 * | \<open>\<^bold>\<not> \<phi> \<equiv>\<^sub>R \<^bold>\<not> \<psi> \<longleftrightarrow> \<phi> \<equiv>\<^sub>R \<psi>\<close>
 * | \<open>(\<phi> \<^bold>\<and> \<psi>) \<equiv>\<^sub>R (\<phi>' \<^bold>\<and> \<psi>') \<longleftrightarrow> \<phi> \<equiv>\<^sub>R \<phi>' \<and> \<psi> \<equiv>\<^sub>R \<psi>'\<close>
 * | \<open>(\<^bold>\<exists> x\<^bold>. \<phi>) \<equiv>\<^sub>R (\<^bold>\<exists> y\<^bold>. \<psi>) \<longleftrightarrow>
 *     (let z = \<some> z. z \<notin> FV_fm \<phi> \<union> FV_fm \<psi> in
 *     (\<phi> \<cdot>\<^sub>f\<^sub>m subst x (Var z)) \<equiv>\<^sub>R (\<psi> \<cdot>\<^sub>f\<^sub>m subst y (Var z)))\<close>
 * | \<open>_ \<equiv>\<^sub>R _ \<longleftrightarrow> False\<close> 
 * 
 * lemma neg_eq_rename_neg: 
 *   assumes \<open>\<^bold>\<not> \<phi> \<equiv>\<^sub>R \<psi>\<close>
 *   obtains \<rho> where
 *     \<open>\<psi> = \<^bold>\<not> \<rho>\<close>
 *   (\* Slow *\)
 *   by (smt (verit) assms eq_upto_renaming.elims(1) fm.simps(14) fm.simps(16)) 
 * 
 * lemma subst_fm_x_x_is_fm: \<open>subst_fm \<phi> (subst x (Var x)) = \<phi>\<close>
 *   by (induction \<phi>) auto
 * 
 * lemma subst_fm_var_not_in_FV: \<open>x \<notin> FV_fm \<phi> \<Longrightarrow> subst_fm \<phi> (subst x t) = \<phi>\<close> 
 * proof (induction \<phi>)
 *   case (Existential y \<phi>)
 * 
 *   consider
 *     (a) \<open>x = y\<close>
 *   | (b) \<open>x \<noteq> y\<close>
 *     by blast 
 *   then show ?case
 *   proof (cases) 
 *     case a
 *     then show ?thesis
 *       by (smt (verit, best) DiffD2 Diff_insert_absorb Existential.prems Term.term.simps(17)
 *           fun_upd_upd insert_iff subst_def subst_fm.simps(5) subst_fm_x_x_is_fm subst_simps(2))
 *   next
 *     case b
 *     then have \<open>x \<notin> FV_fm \<phi>\<close>
 *       using Existential.prems
 *       by simp 
 *     then have \<open>subst_fm \<phi> (subst x t) = \<phi>\<close>
 *       using Existential.IH
 *       by auto 
 *     then show ?thesis
 *       by (smt (verit, del_insts) Diff_iff Existential.prems FV_fm.simps(4) Term.term.simps(17) b
 *           fun_upd_other fun_upd_triv singleton_iff subst_def subst_fm.simps(5)) 
 *   qed
 * qed (auto simp add: list.map_ident_strong)
 * 
 * (\* lemma \<open>subst_fm (subst_fm \<phi> \<sigma>) \<rho> \<equiv>\<^sub>R subst_fm \<phi> (\<sigma> \<circ>\<^sub>s \<rho>)\<close>
 * proof (induction \<phi>)
 *   case (Existential x \<phi>)
 *   then show ?case
 *     apply auto
 *      
 *     sorry
 * qed auto
 * 
 * lemma \<open>\<phi> \<equiv>\<^sub>R \<psi> \<Longrightarrow> subst_fm \<phi> \<sigma> \<equiv>\<^sub>R subst_fm \<psi> \<sigma>\<close>
 * proof (induction \<phi> \<psi> rule: eq_upto_renaming.induct)
 *   case (5 x \<phi> y \<psi>)
 *   then show ?case
 *     apply auto
 *     subgoal sorry
 *     subgoal sorry
 *     subgoal sorry 
 *     sorry
 * qed (simp; meson eq_upto_renaming.simps)+
 * (\* Some subgoals are discharged already by \<open>simp\<close>. In those cases, we do not want to apply \<open>meson\<close>
 *  * at all. \<open>;\<close> allows us to do just that (because it tries to iterate an empty list of subgoals).
 *  * Alternatively, I think that just \<open>meson eq_upto_renaming.simps subst_fm.simps\<close> should work just
 *  * fine, but I did not test it. *\) *\)
 * 
 * lemma apply_subst_term_upd_cancel:
 *   assumes \<open>y \<notin> FV_tm t\<close>
 *   shows \<open>t \<cdot> \<sigma>(y := t') = t \<cdot> \<sigma>\<close>
 *   by (simp add: assms term_subst_eq_conv) 
 * 
 * lemma apply_subst_term_chain_upd_cancel:
 *   assumes \<open>y \<notin> FV_tm t\<close>
 *   shows \<open>t' \<cdot> subst y t \<cdot> \<sigma>(y := Var y) = t' \<cdot> subst y t \<cdot> \<sigma>\<close>
 *   using assms
 * proof (induction t') 
 *   case (Var v)
 * 
 *   show ?case
 *     unfolding subst_def
 *     by (metis assms fun_upd_other fun_upd_same subst_apply_term.simps(1) term_subst_eq) 
 * next
 *   case (Fun f ts)
 *   then show ?case
 *     by auto
 * qed
 * 
 * lemma \<open>FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = \<Union> (FV_tm ` \<sigma> ` FV_fm \<phi>)\<close>
 * proof (induction \<phi> arbitrary: \<sigma>)
 *   case (Rel p ts)
 *   then show ?case
 *     by (simp add: vars_term_subst) 
 * next
 *   case (Existential x \<phi>)
 *   then show ?case
 *      
 *     sorry
 * qed auto 
 * 
 * lemma
 *   assumes \<open>y \<notin> FV_tm t\<close>
 *   shows \<open>\<phi> \<cdot>\<^sub>f\<^sub>m subst y t \<cdot>\<^sub>f\<^sub>m \<sigma>(y := Var y) \<equiv>\<^sub>R \<phi> \<cdot>\<^sub>f\<^sub>m subst y t \<cdot>\<^sub>f\<^sub>m \<sigma>\<close>
 *   using assms
 * proof (induction \<phi>) 
 *   case (Rel p ts)
 * 
 *   show ?case
 *     using apply_subst_term_chain_upd_cancel[OF Rel.prems(1), of _ \<sigma>]
 *     by auto (smt (verit, best) fun_upd_same term_subst_eq term_subst_eq_rev) 
 * next
 *   case (Existential x \<phi>)
 *   then show ?case
 *     apply auto
 *      
 *     sorry
 * qed auto *)

context
  assumes UNIV_contains_all_vars: \<open>\<forall> \<phi> :: ('f, 'p, 'v) fm. FV_fm \<phi> \<subset> UNIV\<close>
begin

lemma ex_fresh_var:
  fixes \<phi> :: \<open>('f, 'p, 'v) fm\<close> 
  obtains v where
    \<open>v \<notin> FV_fm \<phi>\<close>
  using UNIV_contains_all_vars
  by blast

end (* context *)

definition is_ground_tm :: \<open>('f, 'v) tm \<Rightarrow> bool\<close> where
  \<open>is_ground_tm t \<equiv> \<forall> \<sigma>. t \<cdot> \<sigma> = t\<close>

definition is_ground_subst :: \<open>('f, 'v) subst \<Rightarrow> bool\<close> where
  \<open>is_ground_subst \<sigma> \<equiv> \<forall> t. is_ground_tm (t \<cdot> \<sigma>)\<close> 

lemma tm_is_ground_iff_closed: \<open>is_ground_tm t \<longleftrightarrow> FV_tm t = {}\<close>
proof (induction t) 
  case (Var v)

  have \<open>\<not> is_ground_tm (Var v)\<close>
    unfolding is_ground_tm_def
    by auto 
  moreover have \<open>FV_tm (Var v) \<noteq> {}\<close>
    by auto 
  ultimately show ?case
    by blast
next
  case (Fun f ts)

  have \<open>\<forall> t \<in> set ts. is_ground_tm t \<longleftrightarrow> FV_tm t = {}\<close>
    using Fun.IH
    by (intro ballI)
  moreover have \<open>\<forall> \<sigma>. (Fun f ts) \<cdot> \<sigma> = Fun f [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
    by auto 
  ultimately have \<open>(\<forall> \<sigma>. Fun f [t \<cdot> \<sigma>. t \<leftarrow> ts] = Fun f ts) \<longleftrightarrow> FV_tm (Fun f ts) = {}\<close>
    unfolding is_ground_tm_def
    (* Slow-ish *)
    by (smt (z3) empty_iff equals0I subst_apply_term.simps(2) subst_apply_term_empty subst_ident
        subst_simps(1) term.distinct(1) term.inject(2) term_subst_eq term_subst_eq_rev) 
  then show ?case
    unfolding is_ground_tm_def
    by auto 
qed

lemma ground_tm_subst: \<open>is_ground_tm t \<Longrightarrow> t \<cdot> \<sigma> = t\<close>
  unfolding is_ground_tm_def
  by blast

lemma subst_term_ground_subst_is_ground: \<open>is_ground_subst \<sigma> \<Longrightarrow> is_ground_tm (t \<cdot> \<sigma>)\<close>
  unfolding is_ground_subst_def
  by blast

text \<open>
  The grounding function \<open>\<G>\<close> returns all ground instances of a set of formulas.
\<close> 

abbreviation \<open>\<G> N \<equiv> \<Union> \<phi> \<in> N. {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close> 

lemma ex_ground_subst: \<open>\<exists> \<sigma> :: ('f, 'v) subst. is_ground_subst \<sigma>\<close>
  unfolding is_ground_subst_def
proof -
  obtain f :: 'f and \<sigma> :: \<open>('f, 'v) subst\<close> where
    \<open>\<forall> v. \<sigma> v = Fun f []\<close>
    by force
  moreover have \<open>is_ground_tm (Fun f [])\<close>
    unfolding is_ground_tm_def
    by simp 
  ultimately have \<open>is_ground_tm (t \<cdot> \<sigma>)\<close>
    for t
    unfolding is_ground_tm_def
    by (induction t, auto)
  then have \<open>\<forall> t. is_ground_tm (t \<cdot> \<sigma>)\<close>
    by blast 
  then show \<open>\<exists> \<sigma> :: ('f, 'v) subst. \<forall> t. is_ground_tm (t \<cdot> \<sigma>)\<close>
    by blast 
qed 

text \<open>
  Extract the language \<open>\<L>\<close> used in the formula.
  Function (and predicate) symbols are bundled together with their respective arities.
\<close> 

fun fn_sym_tm :: \<open>('f, 'v) tm \<Rightarrow> ('f \<times> nat) set\<close> where
  \<open>fn_sym_tm (Var _) = {}\<close>
| \<open>fn_sym_tm (Fun f ts) = {(f, length ts)} \<union> (\<Union> t \<in> set ts. fn_sym_tm t)\<close>

fun fn_sym_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('f \<times> nat) set\<close> where
  \<open>fn_sym_fm \<^bold>\<bottom> = {}\<close>
| \<open>fn_sym_fm (\<phi> \<^bold>\<and> \<psi>) = fn_sym_fm \<phi> \<union> fn_sym_fm \<psi>\<close>
| \<open>fn_sym_fm (\<^bold>\<not> \<phi>) = fn_sym_fm \<phi>\<close>
| \<open>fn_sym_fm (\<^bold>\<exists> x\<^bold>. \<phi>) = fn_sym_fm \<phi>\<close>
| \<open>fn_sym_fm (Rel p ts) = (\<Union> t \<in> set ts. fn_sym_tm t)\<close> 

fun pred_sym_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('p \<times> nat) set\<close> where
  \<open>pred_sym_fm \<^bold>\<bottom> = {}\<close>
| \<open>pred_sym_fm (\<phi> \<^bold>\<and> \<psi>) = pred_sym_fm \<phi> \<union> pred_sym_fm \<psi>\<close>
| \<open>pred_sym_fm (\<^bold>\<not> \<phi>) = pred_sym_fm \<phi>\<close>
| \<open>pred_sym_fm (\<^bold>\<exists> x\<^bold>. \<phi>) = pred_sym_fm \<phi>\<close>
| \<open>pred_sym_fm (Rel p ts) = {(p, length ts)}\<close>

abbreviation \<open>language S \<equiv> (\<Union> \<phi> \<in> S. fn_sym_fm \<phi>, \<Union> \<phi> \<in> S. pred_sym_fm \<phi>)\<close> 

inductive_set terms :: \<open>('f \<times> nat) set \<times> ('p \<times> nat) set \<Rightarrow> ('f, 'v) tm set\<close>
  for \<L> :: \<open>('f \<times> nat) set \<times> ('p \<times> nat) set\<close> where
  var: \<open>Var (v :: 'v) \<in> terms \<L>\<close>
| fn: \<open>(f, length ts) \<in> fst \<L> \<Longrightarrow> list_all (\<lambda> t. t \<in> terms \<L>) ts \<Longrightarrow> Fun f ts \<in> terms \<L>\<close> 
  
subsection \<open>Structures and Models\<close>

text \<open>
  A structure is a 3-uple containing:
  \<^item> \<open>\<cdot>\<^sub>f\<^sup>M \<in> M\<^sup>n \<rightarrow> M\<close> is a function mapping function symbols to functions from \<open>M\<^sup>n\<close> to \<open>M\<close>;
  \<^item> \<open>\<cdot>\<^sub>v\<^sup>M \<in> V \<rightarrow> M\<close> is a function mapping (free) variable symbols to values of \<open>M\<close>;
  \<^item> \<open>\<cdot>\<^sub>r\<^sup>M \<in> M\<^sup>n \<rightarrow> \<bool>\<close> (which we could also write \<open>\<cdot>\<^sub>r\<^sup>M \<subseteq> M\<^sup>n\<close>) is a function (relation) mapping values
    of \<open>M\<close> to a truth value.
\<close> 

(* Definition 1.3 *)
locale struct =
  fixes
    M :: \<open>'m set\<close> and
    FN :: \<open>'f \<Rightarrow> 'm list \<Rightarrow> 'm\<close> and
    REL :: \<open>'p \<Rightarrow> 'm list set\<close> 
  assumes
    M_nonempty: \<open>M \<noteq> {}\<close> and 
    FN_dom_to_dom: \<open>\<forall> f es. (\<forall> e \<in> set es. e \<in> M) \<longrightarrow> FN f es \<in> M\<close> and
    REL_to_dom: \<open>\<forall> p. \<forall> es \<in> REL p. \<forall> e \<in> set es. e \<in> M\<close> 

definition is_vars :: \<open>'m set \<Rightarrow> ('v \<Rightarrow> 'm) \<Rightarrow> bool\<close> where
  [simp]: \<open>is_vars M \<beta> \<longleftrightarrow> (\<forall> v. \<beta> v \<in> M)\<close> 

text \<open>
  We are only interested in domains which are countable.
\<close> 

typedef ('f, 'p, 'm) model =
  \<open>{ (M :: 'm set, FN :: 'f \<Rightarrow> 'm list \<Rightarrow> 'm, REL :: 'p \<Rightarrow> 'm list set). struct M FN REL }\<close>
  using struct.intro
  by fastforce

setup_lifting type_definition_model

lift_definition dom :: \<open>('f, 'p, 'm) model \<Rightarrow> 'm set\<close> is fst .
lift_definition interp_fn :: \<open>('f, 'p, 'm) model \<Rightarrow> ('f \<Rightarrow> 'm list \<Rightarrow> 'm)\<close> is \<open>fst \<circ> snd\<close> .
lift_definition interp_rel :: \<open>('f, 'p, 'm) model \<Rightarrow> ('p \<Rightarrow> 'm list set)\<close> is \<open>snd \<circ> snd\<close> .

lemma model_is_struct: \<open>struct (dom \<M>) (interp_fn \<M>) (interp_rel \<M>)\<close>
  by transfer auto 

lemma dom_Abs_is_fst [simp]: \<open>struct M FN REL \<Longrightarrow> dom (Abs_model (M, FN, REL)) = M\<close>
  by (simp add: Abs_model_inverse dom.rep_eq) 

lemma interp_fn_Abs_is_fst_snd [simp]: \<open>struct M FN REL \<Longrightarrow> interp_fn (Abs_model (M, FN, REL)) = FN\<close>
  by (simp add: Abs_model_inverse interp_fn.rep_eq) 

lemma interp_rel_Abs_is_snd_snd [simp]: \<open>struct M FN REL \<Longrightarrow> interp_rel (Abs_model (M, FN, REL)) = REL\<close>
  by (simp add: Abs_model_inverse interp_rel.rep_eq) 

lemma FN_dom_to_dom: \<open>\<forall> t \<in> set ts. t \<in> dom \<M> \<Longrightarrow> interp_fn \<M> f ts \<in> dom \<M>\<close>
  by (meson model_is_struct struct.FN_dom_to_dom)  

text \<open>
  We use canonical models to prove (un-)satisfiability.

  A canonical model is a model whose domain is the set of terms and where function symbols are
  interpreted as ``themselves'' (i.e. \<open>\<lbrakk>f(t\<^sub>1, \<dots>, t\<^sub>n)\<rbrakk>\<^bsup>\<J>,\<beta>\<^esup> = f(\<lbrakk>t\<^sub>1\<rbrakk>\<^bsup>\<J>,\<beta>\<^esup>, \<dots>, \<lbrakk>t\<^sub>n\<rbrakk>\<^bsup>\<J>,\<beta>\<^esup>)\<close>).
  This is also refered to as ``Herbrand models'' in the literature.
\<close> 

definition is_canonical
  :: \<open>('f, 'p, ('f, 'v) tm) model \<Rightarrow> ('f \<times> nat) set \<times> ('p \<times> nat) set \<Rightarrow> bool\<close> where
  \<open>is_canonical \<M> \<L> \<longleftrightarrow> dom \<M> = terms \<L> \<and> interp_fn \<M> = Fun\<close> 

text \<open>
  We define the notion of satisfaction inductively on formulas, and evaluation on terms.
\<close>

fun eval
  :: \<open>('f, 'v) tm \<Rightarrow> ('f, 'p, 'm) model \<Rightarrow> ('v \<Rightarrow> 'm) \<Rightarrow> 'm\<close>
  (\<open>\<lbrakk>_\<rbrakk>\<^bsup>_,_\<^esup>\<close> [50, 0, 0] 70) where
  \<open>\<lbrakk>Var v\<rbrakk>\<^bsup>_,\<beta>\<^esup> = \<beta> v\<close>
| \<open>\<lbrakk>Fun f args'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> args']\<close> 


fun satisfies
  :: \<open>('f, 'p, 'm) model \<Rightarrow> ('v \<Rightarrow> 'm) \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close>
  (\<open>_,_ \<Turnstile> _\<close> [30, 30, 80] 80) where
  \<open>\<M>,\<beta> \<Turnstile> \<^bold>\<bottom> \<longleftrightarrow> False\<close>
| \<open>\<M>,\<beta> \<Turnstile> \<^bold>\<not> \<phi> \<longleftrightarrow> (\<not> (\<M>,\<beta> \<Turnstile> \<phi>))\<close>
| \<open>\<M>,\<beta> \<Turnstile> \<phi> \<^bold>\<and> \<psi> \<longleftrightarrow> (\<M>,\<beta> \<Turnstile> \<phi>) \<and> (\<M>,\<beta> \<Turnstile> \<psi>)\<close>
| \<open>\<M>,\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>) \<longleftrightarrow> (\<exists> y \<in> dom \<M>. \<M>,\<beta>(x := y) \<Turnstile> \<phi>)\<close>
| \<open>\<M>,\<beta> \<Turnstile> Rel p args' \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> args'] \<in> interp_rel \<M> p\<close> 

lemma satisfies_indep_\<beta>_if:
  \<open>\<forall> v \<in> FV_fm \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v \<Longrightarrow> \<M>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close>
proof (induction \<phi> arbitrary: \<beta>\<^sub>1 \<beta>\<^sub>2)
  case (Rel p ts)
  then have \<open>\<forall> t \<in> set ts. \<forall> v \<in> FV_tm t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
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
      then have \<open>\<forall> t \<in> set ts'. \<forall> v \<in> FV_tm t. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
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
    by auto 
next
  case (Conjunction \<phi> \<psi>)
  then have
    \<open>\<forall> v \<in> FV_fm \<phi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close> and
    \<open>\<forall> v \<in> FV_fm \<psi>. \<beta>\<^sub>1 v = \<beta>\<^sub>2 v\<close>
    by auto
  then have
    \<open>\<M>,\<beta>\<^sub>1 \<Turnstile> \<phi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<phi>\<close> and
    \<open>\<M>,\<beta>\<^sub>1 \<Turnstile> \<psi> \<longleftrightarrow> \<M>,\<beta>\<^sub>2 \<Turnstile> \<psi>\<close>
    using Conjunction.IH
    by auto
  then show ?case
    by simp 
next
  case (Existential x \<phi>)

  show ?case (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
  proof (intro iffI)
    assume ?lhs
    then obtain a where
      a_in_M: \<open>a \<in> dom \<M>\<close> and
      \<open>\<M>,\<beta>\<^sub>1(x := a) \<Turnstile> \<phi>\<close>
      by auto
    then have \<open>\<M>,\<beta>\<^sub>2(x := a) \<Turnstile> \<phi>\<close>
      using Existential.IH Existential.prems
      by (smt (verit, best) DiffI FV_fm.simps(4) empty_iff fun_upd_apply insert_iff) 
    then show ?rhs
      using a_in_M
      by auto 
  next
    assume ?rhs
    then obtain a where
      a_in_M: \<open>a \<in> dom \<M>\<close> and
      \<open>\<M>,\<beta>\<^sub>2(x := a) \<Turnstile> \<phi>\<close>
      by auto
    then have \<open>\<M>,\<beta>\<^sub>1(x := a) \<Turnstile> \<phi>\<close>
      using Existential.IH Existential.prems
      by (smt (verit, best) DiffI FV_fm.simps(4) empty_iff fun_upd_apply insert_iff) 
    then show ?lhs
      using a_in_M
      by auto
  qed
qed auto 

lemma satisfies_indep_model_if:
  fixes
    \<phi> :: \<open>('f, 'p, 'v) fm\<close> and
    \<M> \<M>' :: \<open>('f, 'p, 'm) model\<close> 
  assumes
    dom_eq: \<open>dom \<M> = dom \<M>'\<close> and
    rel_eq: \<open>\<forall> p. interp_rel \<M> p = interp_rel \<M>' p\<close> and
    fn_eq: \<open>\<forall> f ts. (f, length ts) \<in> fn_sym_fm \<phi> \<longrightarrow> interp_fn \<M> f ts = interp_fn \<M>' f ts\<close>
  shows
    \<open>\<forall> \<beta>. is_vars (dom \<M>) \<beta> \<longrightarrow> \<M>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> \<M>',\<beta> \<Turnstile> \<phi>\<close>
  using fn_eq
proof (intro allI impI, induction \<phi>)
  case (Rel p ts)

  have all_fn_sym_in: \<open>(\<Union> t \<in> set ts. fn_sym_tm t) \<subseteq> fn_sym_fm (Rel p ts)\<close> (is \<open>?A \<subseteq> _\<close>)
    by simp 

  have eval_tm_eq: \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = \<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>\<close>
    if \<open>fn_sym_tm t \<subseteq> fn_sym_fm (Rel p ts)\<close> 
    for t 
    using that
  proof (induction t) 
    case (Fun f ts') 

    have \<open>\<forall> t' \<in> set ts'. fn_sym_tm t' \<subseteq> fn_sym_fm (Rel p ts)\<close>
      using Fun.prems
      by auto
    moreover have \<open>(f, length [\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']) \<in> fn_sym_fm (Rel p ts)\<close>
      using Fun.prems
      by fastforce 
    ultimately show ?case
      using Fun.IH Rel.prems(1)[rule_format, of f \<open>[\<lbrakk>t'\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t' \<leftarrow> ts']\<close>] 
      by (smt (verit, del_insts) eval.simps(2) map_eq_conv)
  qed auto 

  have \<open>\<M>,\<beta> \<Turnstile> Rel p ts \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    by simp
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M>' p\<close>
    by (simp add: rel_eq)
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>',\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M>' p\<close>
    using eval_tm_eq all_fn_sym_in
    by (metis (mono_tags, lifting) UN_subset_iff map_eq_conv)
  also have \<open>... \<longleftrightarrow> \<M>',\<beta> \<Turnstile> Rel p ts\<close>
    by auto 
  finally show ?case .
next
  case (Existential x \<phi>)

  have \<open>\<M>,\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>) \<longleftrightarrow> (\<exists> a \<in> dom \<M>. \<M>,\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by simp 
  also have \<open>... = (\<exists> a \<in> dom \<M>. \<M>',\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    using Existential.IH Existential.prems
    by fastforce
  also have \<open>... = (\<exists> a \<in> dom \<M>'. \<M>',\<beta>(x := a) \<Turnstile> \<phi>)\<close>
    by (simp add: dom_eq)
  also have \<open>... = \<M>',\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>)\<close>
    by auto 
  finally show ?case . 
qed auto


(* text \<open>
  Modelhood is defined as:
  \<open>C\<close> is a consequence of all the formulas in \<open>M\<close> iff if \<open>\<M>\<close> models all formulas in \<open>M\<close> then
  \<open>\<M>\<close> models \<open>C\<close>.
\<close> 

abbreviation models :: \<open>('c, 'v, 'm) interp \<Rightarrow> ('c, 'v) fm set \<Rightarrow> ('c, 'v) fm \<Rightarrow> bool\<close>
  (\<open>_, _ \<turnstile> _\<close> [80, 30, 80] 80) where
  \<open>\<M>, M \<turnstile> C \<equiv> (\<forall> D \<in> M. eval_fm \<M> D) \<longrightarrow> eval_fm \<M> C\<close> 

lemma top_always_valid: \<open>\<M>, M \<turnstile> \<^bold>\<top>\<close>
  by simp

lemma bot_models_all: \<open>\<M>, {\<^bold>\<bottom>} \<turnstile> C\<close>
  by auto 

lemma models_subsets: \<open>M \<subseteq> M' \<Longrightarrow> \<M>, M \<turnstile> C \<Longrightarrow> \<M>, M' \<turnstile> C\<close>
  by blast 

lemma \<open>\<M>, M \<turnstile> C \<longleftrightarrow> \<M>, M \<union> {\<^bold>\<not> C} \<turnstile> \<^bold>\<bottom>\<close>
  by auto *)  

text \<open>
  An interpretation \<open>\<M>\<close> is a model of a set of formulas \<open>T\<close> if every formula of \<open>T\<close> is satisfied by
  \<open>\<M>\<close> (under any valuation).
\<close> 

(* Definition 1.5 *)
definition is_model_of
  :: \<open>('f, 'p, 'm) model \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> bool\<close>
  where
  \<open>is_model_of \<M> T \<longleftrightarrow> (\<forall> \<phi> \<in> T. \<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>)\<close>

lemma is_model_of_conj_iff:
  \<open>is_model_of \<M> {\<phi> \<^bold>\<and> \<psi>} \<longleftrightarrow>
    is_model_of \<M> {\<phi>} \<and> is_model_of \<M> {\<psi>}\<close>
  unfolding is_model_of_def
proof (intro iffI conjI ballI; (elim conjE)?)
  fix \<phi>'
  assume
    \<open>\<forall> \<phi> \<in> {\<phi> \<^bold>\<and> \<psi>}. \<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>\<close> and
    \<open>\<phi>' \<in> {\<phi>}\<close>
  then have
    \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi> \<^bold>\<and> \<psi>\<close> and
    \<phi>'_is: \<open>\<phi>' = \<phi>\<close>
    by blast+
  then have \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>\<close>
    by simp 
  then show \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>'\<close>
    unfolding \<phi>'_is . 
next
  fix \<psi>'
  assume
    \<open>\<forall> \<phi> \<in> {\<phi> \<^bold>\<and> \<psi>}. \<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>\<close> and
    \<open>\<psi>' \<in> {\<psi>}\<close>
  then have
    \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi> \<^bold>\<and> \<psi>\<close> and
    \<psi>'_is: \<open>\<psi>' = \<psi>\<close> 
    by blast+
  then have \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<psi>\<close>
    by auto 
  then show \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<psi>'\<close>
    unfolding \<psi>'_is .
next
  fix \<phi>'
  assume
    \<open>\<phi>' \<in> {\<phi> \<^bold>\<and> \<psi>}\<close> and
    \<open>\<forall> \<phi> \<in> {\<phi>}. \<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>\<close> and
    \<open>\<forall> \<psi> \<in> {\<psi>}. \<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<psi>\<close>
  then have
    \<phi>'_is: \<open>\<phi>' = \<phi> \<^bold>\<and> \<psi>\<close> and
    \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>\<close> and
    \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<psi>\<close>
    by blast+
  then have \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi> \<^bold>\<and> \<psi>\<close>
    by simp 
  then show \<open>\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>'\<close>
    unfolding \<phi>'_is . 
qed

definition entails :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close> where
  \<open>entails _ T \<phi> \<longleftrightarrow>
    (\<forall> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> T \<longrightarrow> (\<forall> V. is_vars (dom \<M>) V \<longrightarrow> \<M>,V \<Turnstile> \<phi>))\<close>

abbreviation entails_set :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> bool\<close> where
  \<open>entails_set (m :: 'm itself) M N \<equiv> (\<forall> \<phi> \<in> N. entails m M \<phi>)\<close>

abbreviation entails_\<G> :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close> where
  \<open>entails_\<G> m T \<phi> \<equiv> entails_set m (\<G> T) (\<G> {\<phi>})\<close>

abbreviation entails_\<G>_set :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> bool\<close> where
  \<open>entails_\<G>_set m M N \<equiv> entails_set m (\<G> M) (\<G> N)\<close>

syntax
  "_Entails" :: \<open>('f, 'p, 'v) fm set \<Rightarrow> 'm itself \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close>
    (\<open>_/ \<Turnstile>\<^sub>_/ _\<close> [80, 20, 80] 80)
  "_Entails_set" :: \<open>('f, 'p, 'v) fm set \<Rightarrow> 'm itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> bool\<close>
    (\<open>_/ \<Turnstile>\<^sup>s\<^sup>e\<^sup>t\<^sub>_/ _\<close> [80, 20, 80] 80)
  "_Entails_G" :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> bool\<close>
    (\<open>_/ \<Turnstile>\<^sub>\<G>\<^sub>_/ _\<close> [80, 20, 80] 80)
  "_Entails_G_set" :: \<open>'m itself \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, 'v) fm set \<Rightarrow> bool\<close>
    (\<open>_/ \<Turnstile>\<^sup>s\<^sup>e\<^sup>t\<^sub>\<G>\<^sub>_/ _\<close> [80, 20, 80] 80)
  
translations
  "T \<Turnstile>\<^sub>m \<phi>" \<rightleftharpoons> "CONST entails m T \<phi>"
  "M \<Turnstile>\<^sup>s\<^sup>e\<^sup>t\<^sub>m N" \<rightleftharpoons> "CONST entails_set m M N"
  "T \<Turnstile>\<^sub>\<G>\<^sub>m \<phi>" \<rightleftharpoons> "CONST entails_\<G> m T \<phi>"
  "M \<Turnstile>\<^sup>s\<^sup>e\<^sup>t\<^sub>\<G>\<^sub>m N" \<rightleftharpoons> "CONST entails_\<G>_set m M N"

abbreviation satisfiable :: \<open>('f, 'p, 'v) fm set \<Rightarrow> bool\<close> where
  \<open>satisfiable T \<equiv>
    (\<exists> \<M> :: ('f, 'p, ('f, 'v) tm) model. is_canonical \<M> (language T) \<and> is_model_of \<M> T)\<close> 

abbreviation unsatisfiable :: \<open>('f, 'p, 'v) fm set \<Rightarrow> bool\<close> where
  \<open>unsatisfiable T \<equiv> \<not> satisfiable T\<close>  
   
lemma unsat_equiv_no_model:
  \<open>unsatisfiable T \<longleftrightarrow>
    (\<forall> \<M> :: ('f, 'p, ('f, 'v) tm) model. is_canonical \<M> (language T) \<longrightarrow> \<not> is_model_of \<M> T)\<close>
  for T :: \<open>('f, 'p, 'v) fm set\<close>
  by blast 

lemma is_model_of_mono: \<open>T' \<subseteq> T \<Longrightarrow> is_model_of \<M> T \<Longrightarrow> is_model_of \<M> T'\<close>
  by (simp add: in_mono is_model_of_def)

lemma unsat_iff_entails_bot: \<open>T \<Turnstile>\<^sub>m \<^bold>\<bottom> \<longleftrightarrow> (\<forall> \<M> :: ('f, 'p, 'm) model. \<not> is_model_of \<M> T)\<close>
  for m :: \<open>'m itself\<close>
proof -
  have \<open>\<not> (\<M>,\<beta> \<Turnstile> \<^bold>\<bottom>)\<close> for \<M> \<beta>
    by auto
  moreover have \<open>\<exists> \<beta>. is_vars (dom \<M>) \<beta>\<close> for \<M>
    unfolding is_vars_def
    using model_is_struct struct.M_nonempty
    by fastforce
  ultimately have \<open>\<not> (\<forall> \<beta>. is_vars (dom \<M>) \<beta> \<longrightarrow> \<M>,\<beta> \<Turnstile> \<^bold>\<bottom>)\<close> (is \<open>\<not> (?P \<M>)\<close>)
    for \<M> :: \<open>('f, 'p, 'm) model\<close>
    by blast 
  then have \<open>(is_model_of \<M> T \<longrightarrow> ?P m \<M>) \<longleftrightarrow> \<not> is_model_of \<M> T\<close>
    for \<M> :: \<open>('f, 'p, 'm) model\<close>
    by blast
  then have \<open>\<forall> \<M> :: ('f, 'p, 'm) model. (is_model_of \<M> T \<longrightarrow> ?P m \<M>) \<longleftrightarrow> \<not> is_model_of \<M> T\<close>
    by blast 
  then have
    \<open>(\<forall> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> T \<longrightarrow> ?P m \<M>) \<longleftrightarrow>
     (\<forall> \<M> :: ('f, 'p, 'm) model. \<not> is_model_of \<M> T)\<close>
    by auto 
  then show ?thesis 
    unfolding entails_def
    by auto
qed

lemma sat_iff_not_entails_bot: \<open>\<not> T \<Turnstile>\<^sub>m \<^bold>\<bottom> \<longleftrightarrow> (\<exists> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> T)\<close>
  for m :: \<open>'m itself\<close>
  by (simp add: unsat_iff_entails_bot) 

subsection \<open>Important results on satisfiability\<close>

lemma map_map_is_map: \<open>map (\<lambda> f. h f x) (map (\<lambda> y. g y) L) = map (\<lambda> y. h (g y) x) L\<close>
  by simp 

lemma map_map_is_map2: \<open>map (\<lambda> f. f i) (map (\<lambda> x. g x) L) = map (\<lambda> x. g x i) L\<close>
  by auto

subsubsection \<open>The substitution lemma\<close>

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
  assumes \<open>\<forall> v \<in> FV_tm t. \<beta> v = \<beta>' v\<close>
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

lemma eval_fun_upd_if:
  assumes
    \<open>v \<in> FV_fm \<phi>\<close> and
    \<open>v \<noteq> x \<longrightarrow> z \<notin> FV_tm (\<sigma> v)\<close>
  shows ‹eval_subst \<M> (\<beta>(z := a)) (\<sigma>(x := Var z)) v = ((eval_subst \<M> \<beta> \<sigma>)(x := a)) v\<close>
proof (cases \<open>v = x\<close>) 
  case True
  then show ?thesis
    by simp 
next
  case False

  have \<open>z \<notin> FV_tm (\<sigma> v)\<close>
    using assms(2)[THEN impE, OF False]
    by argo
  then have \<open>\<forall> v' \<in> FV_tm (\<sigma> v). (\<beta>(z := a)) v' = \<beta> v'\<close>
    by fastforce 
  then have \<open>\<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>(z := a)\<^esup> = \<lbrakk>\<sigma> v\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>\<close>
    by (rule eval_indep_\<beta>_if)
  then show ?thesis
    by auto 
qed

lemma free_set_eq_if:
  assumes \<open>\<forall> v \<in> FV_fm \<phi> - {x}. z \<notin> FV_tm (\<sigma> v)\<close>
  shows
    \<open>{z'. \<exists> y \<in> FV_fm \<phi>. z' \<in> FV_tm ((\<sigma>(x := Var z)) y)} - {z} =
     {z'. \<exists> y \<in> FV_fm \<phi> - {x}. z' \<in> FV_tm (\<sigma> y)}\<close>
    (is \<open>?lhs = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  fix w
  assume \<open>w \<in> ?lhs\<close>
  then have w_neq: \<open>w \<noteq> z\<close> and \<open>\<exists> y \<in> FV_fm \<phi>. w \<in> FV_tm ((\<sigma>(x := Var z)) y)\<close>
    by auto
  then obtain y where
    y_free: \<open>y \<in> FV_fm \<phi>\<close> and
    w_free: \<open>w \<in> FV_tm ((\<sigma>(x := Var z)) y)\<close>
    by blast
  then have y_neq: \<open>y \<noteq> x\<close>
    using w_neq
    by force

  have \<open>w \<in> FV_tm (\<sigma> y)\<close>
    using w_free y_neq
    by auto
  moreover have \<open>y \<in> FV_fm \<phi> - {x}\<close>
    using y_free y_neq
    by blast
  ultimately have \<open>\<exists> y \<in> FV_fm \<phi> - {x}. w \<in> FV_tm (\<sigma> y)\<close>
    by blast  
  then show \<open>w \<in> ?rhs\<close>
    by blast   
next
  fix w 
  assume \<open>w \<in> ?rhs›
  then have \<open>\<exists> y \<in> FV_fm \<phi> - {x}. w \<in> FV_tm (\<sigma> y)\<close>
    by blast 
  then obtain y where
    \<open>y \<in> FV_fm \<phi> - {x}\<close> and
    w_free: \<open>w \<in> FV_tm (\<sigma> y)\<close>
    by blast
  then have y_free: \<open>y \<in> FV_fm \<phi>\<close> and y_neq: \<open>y \<noteq> x\<close>
    by auto
  then have w_free': \<open>w \<in> FV_tm ((\<sigma>(x := Var z)) y)\<close>
    using w_free
    by force

  have \<open>w \<noteq> z\<close>
    using y_free y_neq assms w_free
    by blast
  moreover have \<open>w \<in> {w. \<exists> y \<in> FV_fm \<phi>. w \<in> FV_tm ((\<sigma>(x := Var z)) y)}\<close>
    using w_free' y_free
    by blast
  ultimately show \<open>w \<in> ?lhs\<close>
    by blast 
qed

context
  assumes UNIV_contains_all_vars: \<open>\<forall> \<phi> :: ('f, 'p, 'v) fm. FV_fm \<phi> \<subset> UNIV\<close>
begin

lemma free_vars_subst_fm: \<open>FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) = {x. \<exists> v \<in> FV_fm \<phi>. x \<in> FV_tm (\<sigma> v)}\<close>
  for \<phi> :: \<open>('f, 'p, 'v) fm\<close>
proof (induction rule: subst_fm.induct) 
  case (1 \<sigma>)
  then show ?case
    by auto 
next
  case (2 p ts \<sigma>)

  have \<open>FV_fm (Rel p ts \<cdot>\<^sub>f\<^sub>m \<sigma>) = (\<Union> t \<in> set ts. FV_tm (t \<cdot> \<sigma>))\<close>
    by force 
  also have \<open>... = (\<Union> t \<in> set ts. \<Union> (FV_tm ` \<sigma> ` FV_tm t))\<close>
    by (meson vars_term_subst)
  also have \<open>... = (\<Union> t \<in> set ts. \<Union> v \<in> FV_tm t. FV_tm (\<sigma> v))\<close>
    by blast
  also have \<open>... = (\<Union> v \<in> (\<Union> t \<in> set ts. FV_tm t). FV_tm (\<sigma> v))\<close>
    by blast
  also have \<open>... = (\<Union> v \<in> FV_fm (Rel p ts). FV_tm (\<sigma> v))\<close>
    by auto 
  also have \<open>... = {x. \<exists> v \<in> FV_fm (Rel p ts). x \<in> FV_tm (\<sigma> v)}\<close>
    by blast 
  finally show ?case .
next
  case (3 \<phi> \<sigma>)
  then show ?case
    by auto 
next
  case (4 \<phi> \<psi> \<sigma>)
  then show ?case
    by auto
next
  case ex: (5 x \<phi> \<sigma>)

  show ?case
  proof (cases \<open>\<exists> y. y \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>) \<and> x \<in> FV_tm ((\<sigma>(x := Var x)) y)\<close>)
    case True
      
    let ?z = \<open>\<some> z. z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
      
    have z_bound: \<open>\<forall> v \<in> FV_fm \<phi> - {x}. z \<notin> FV_tm (\<sigma> v)\<close>
      if \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close> 
      for z
      by (metis (mono_tags, lifting) DiffD1 DiffD2 True ex.IH(1) fun_upd_other mem_Collect_eq
          singleton_iff that)
    moreover obtain z where
      z_bound': \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
      using ex_fresh_var[OF UNIV_contains_all_vars] .
    then have \<open>?z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
      by (rule someI)
    ultimately have dummy_z_bound: \<open>\<forall> v \<in> FV_fm \<phi> - {x}. ?z \<notin> FV_tm (\<sigma> v)\<close> . 

    have \<open>FV_fm ((\<^bold>\<exists> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = (let z = ?z in FV_fm (\<^bold>\<exists> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))))\<close>
      using True
      by (smt (verit, ccfv_SIG) Eps_cong subst_fm.simps(5))
    also have \<open>... = (let z = ?z in FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)) - {z})\<close>
      by auto 
    also have \<open>... = (let z = ?z in {w. \<exists> v \<in> FV_fm \<phi>. w \<in> FV_tm ((\<sigma>(x := Var z)) v)} - {z})\<close>
      using True ex.IH(2)
      by presburger
    also have \<open>... = {w. \<exists> v \<in> FV_fm \<phi> - {x}. w \<in> FV_tm (\<sigma> v)}\<close>
      using free_set_eq_if[OF dummy_z_bound]
      by presburger 
    also have \<open>... = {w. \<exists> v \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>). w \<in> FV_tm (\<sigma> v)}\<close>
      by auto 
    finally show ?thesis . 
  next
    case False
    then have \<open>\<forall> v \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>). x \<notin> FV_tm ((\<sigma>(x := Var x)) v)\<close>
      by blast 
    then have x_bound: \<open>\<forall> v \<in> FV_fm \<phi> - {x}. x \<notin> FV_tm (\<sigma> v)\<close>
      by auto 

    have \<open>FV_fm ((\<^bold>\<exists> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) = FV_fm (\<^bold>\<exists> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)))\<close>
      using False
      by auto 
    also have \<open>... = FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)) - {x}\<close>
      by simp 
    also have \<open>... = {z. \<exists> y \<in> FV_fm \<phi>. z \<in> FV_tm ((\<sigma>(x := Var x)) y)} - {x}\<close>
      using ex.IH False
      by presburger 
    also have \<open>... = {z. \<exists> y \<in> FV_fm \<phi> - {x}. z \<in> FV_tm (\<sigma> y)}\<close>
      using free_set_eq_if[OF x_bound] .
    also have \<open>... = {z. \<exists> y \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>). z \<in> FV_tm (\<sigma> y)}\<close>
      by simp 
    finally show ?thesis .
  qed
qed

lemma subst_lemma_form: \<open>\<M>,\<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,(eval_subst \<M> \<beta> \<sigma>) \<Turnstile> \<phi>\<close>
  for \<phi> :: \<open>('f, 'p, 'v) fm\<close>
proof (induction \<phi> arbitrary: \<sigma> \<beta>)
  case (Rel p ts)

  have \<open>\<M>,\<beta> \<Turnstile> (Rel p ts \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,\<beta> \<Turnstile> Rel p [t \<cdot> \<sigma>. t \<leftarrow> ts]\<close>
    by auto 
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> [t \<cdot> \<sigma>. t \<leftarrow> ts]] \<in> interp_rel \<M> p\<close>
    by auto 
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t \<cdot> \<sigma>\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    unfolding map_map
    by (smt (verit, ccfv_SIG) comp_apply map_eq_conv)  
  also have \<open>... \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,eval_subst \<M> \<beta> \<sigma>\<^esup>. t \<leftarrow> ts] \<in> interp_rel \<M> p\<close>
    by (simp add: subst_lemma_terms) 
  also have \<open>... \<longleftrightarrow> \<M>,eval_subst \<M> \<beta> \<sigma> \<Turnstile> Rel p ts\<close>
    by auto 
  finally show ?case . 
next
  case (Negation \<phi>)
  then show ?case
    by auto 
next
  case (Conjunction \<phi> \<psi>)
  then show ?case
    by auto 
next
  case (Existential x \<phi>)

  show ?case
  proof (cases \<open>\<exists> y. y \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>) \<and> x \<in> FV_tm ((\<sigma>(x := Var x)) y)\<close>)
    case True

    have \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)) \<longleftrightarrow> (\<forall> v \<in> FV_fm \<phi>. z \<notin> FV_tm ((\<sigma>(x := Var x)) v))\<close>
      for z
      using free_vars_subst_fm
      by fastforce 
    also have \<open>... z \<longleftrightarrow> (\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> z \<notin> FV_tm (\<sigma> v))\<close>
      for z
      using True
      by force
    finally have
      z_not_free_iff: \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)) \<longleftrightarrow> (\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> z \<notin> FV_tm (\<sigma> v))\<close>
      for z .

    let ?z = \<open>\<some> z. z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close> 

    have \<open>\<M>,\<beta> \<Turnstile> ((\<^bold>\<exists> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> (let z = ?z in \<M>,\<beta> \<Turnstile> (\<^bold>\<exists> z\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z))))\<close>
      using True
      by (smt (verit, best) Eps_cong subst_fm.simps(5))  
    also have \<open>... \<longleftrightarrow> (let z = ?z in \<exists> a \<in> dom \<M>. \<M>,\<beta>(z := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var z)))\<close>
      by simp
    also have \<open>... \<longleftrightarrow> (let z = ?z in \<exists> a \<in> dom \<M>. \<M>,eval_subst \<M> (\<beta>(z := a)) (\<sigma>(x := Var z)) \<Turnstile> \<phi>)\<close>
      using Existential.IH
      by fastforce 
    also have \<open>... \<longleftrightarrow> (\<exists> a \<in> dom \<M>. \<M>,(eval_subst \<M> \<beta> \<sigma>)(x := a) \<Turnstile> \<phi>)\<close>
      (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
    proof (intro iffI)
      assume ?lhs
      then obtain a z where
        a_in_dom: \<open>a \<in> dom \<M>\<close> and
        z_is: \<open>z = ?z\<close> and 
        \<phi>_sat: \<open>\<M>,eval_subst \<M> (\<beta>(z := a)) (\<sigma>(x := Var z)) \<Turnstile> \<phi>\<close>
        by metis

      have \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
        using z_is ex_fresh_var[OF UNIV_contains_all_vars]
        by (metis someI_ex)
      then have \<open>\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> z \<notin> FV_tm (\<sigma> v)\<close>
        unfolding z_not_free_iff . 
      then have
        \<open>\<forall> v \<in> FV_fm \<phi>. eval_subst \<M> (\<beta>(z := a)) (\<sigma>(x := Var z)) v = ((eval_subst \<M> \<beta> \<sigma>)(x := a)) v\<close>
        by (metis eval_fun_upd_if) 
      then show ?rhs
        using \<phi>_sat a_in_dom
        by (smt (verit, best) satisfies_indep_\<beta>_if) 
    next
      assume ?rhs
      then obtain a where
        a_in_dom: \<open>a \<in> dom \<M>\<close> and
        \<phi>_sat: \<open>\<M>,(eval_subst \<M> \<beta> \<sigma>)(x := a) \<Turnstile> \<phi>\<close>
        by blast

      obtain z where
        \<open>z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
        using ex_fresh_var[OF UNIV_contains_all_vars] . 
      then have \<open>?z \<notin> FV_fm (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x))\<close>
        by (metis someI_ex) 
      then have \<open>\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> ?z \<notin> FV_tm (\<sigma> v)\<close>
        unfolding z_not_free_iff . 
      then have
        \<open>let z = ?z in \<forall> v \<in> FV_fm \<phi>. eval_subst \<M> (\<beta>(z := a)) (\<sigma>(x := Var z)) v =
         ((eval_subst \<M> \<beta> \<sigma>)(x := a)) v\<close>
        by (metis eval_fun_upd_if)
      then show ?lhs
        by (smt (verit, ccfv_threshold) \<phi>_sat a_in_dom satisfies_indep_\<beta>_if) 
    qed
    also have \<open>... \<longleftrightarrow> \<M>,eval_subst \<M> \<beta> \<sigma> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>)\<close>
      by simp 
    finally show ?thesis .
  next
    case False

    have \<open>\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> v \<in> FV_fm (\<^bold>\<exists> x\<^bold>. \<phi>)\<close>
      by auto  
    then have \<open>\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> x \<notin> FV_tm ((\<sigma>(x := Var x)) v)\<close>
      using False
      by blast 
    then have x_bound: \<open>\<forall> v \<in> FV_fm \<phi>. v \<noteq> x \<longrightarrow> x \<notin> FV_tm (\<sigma> v)\<close>
      by fastforce 

    have \<open>\<M>,\<beta> \<Turnstile> ((\<^bold>\<exists> x\<^bold>. \<phi>) \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)))\<close>
      using False
      by auto 
    also have \<open>... \<longleftrightarrow> (\<exists> a \<in> dom \<M>. \<M>,\<beta>(x := a) \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>(x := Var x)))\<close>
      by auto 
    also have \<open>... \<longleftrightarrow> (\<exists> a \<in> dom \<M>. \<M>,eval_subst \<M> (\<beta>(x := a)) (\<sigma>(x := Var x)) \<Turnstile> \<phi>)\<close>
      using Existential.IH
      by blast 
    also have \<open>... \<longleftrightarrow> (\<exists> a \<in> dom \<M>. \<M>,(eval_subst \<M> \<beta> \<sigma>)(x := a) \<Turnstile> \<phi>)\<close>
      by (smt (verit, ccfv_SIG) eval_fun_upd_if fun_upd_def satisfies_indep_\<beta>_if x_bound) 
    also have \<open>... \<longleftrightarrow> \<M>,eval_subst \<M> \<beta> \<sigma> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>)\<close>
      by auto 
    finally show ?thesis .
  qed
next
  case Bot
  then show ?case
    by auto  
qed

lemma eval_in_dom_if: \<open>is_vars (dom \<M>) \<beta> \<Longrightarrow> \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> \<in> dom \<M>\<close>
proof (induction t)   
  case (Fun f ts)

  have \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> = interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    by auto 
  moreover have \<open>\<forall> t \<in> set ts. \<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup> \<in> dom \<M>\<close>
    using Fun.IH Fun.prems
    by blast 
  then have \<open>interp_fn \<M> f [\<lbrakk>t\<rbrakk>\<^bsup>\<M>,\<beta>\<^esup>. t \<leftarrow> ts] \<in> dom \<M>\<close>
    by (simp add: FN_dom_to_dom) 
  ultimately show ?case
    by argo 
qed auto

lemma model_is_model_of_all_subst: \<open>is_model_of \<M> {\<phi>} \<Longrightarrow> \<forall> \<sigma>. is_model_of \<M> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>}\<close>
  for
    \<phi> :: \<open>('f, 'p, 'v) fm\<close> and
    \<M> :: \<open>('f, 'p, 'm) model\<close>
  unfolding is_model_of_def
proof (intro allI ballI impI) 
  fix \<sigma> \<phi>' and \<beta> :: \<open>'v \<Rightarrow> 'm\<close> 
  assume
    \<phi>_sat: \<open>\<forall> \<phi> \<in> {\<phi>}. \<forall> \<beta>. is_vars (dom \<M>) \<beta> \<longrightarrow> \<M>,\<beta> \<Turnstile> \<phi>\<close> and
    \<phi>'_in: \<open>\<phi>' \<in> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>}\<close> and
    \<beta>_val: \<open>is_vars (dom \<M>) \<beta>\<close>

  have \<open>\<phi>' = \<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>\<close>
    using \<phi>'_in
    by blast  
  moreover have \<open>\<M>,\<beta> \<Turnstile> (\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>) \<longleftrightarrow> \<M>,eval_subst \<M> \<beta> \<sigma> \<Turnstile> \<phi>\<close>
    by (simp add: subst_lemma_form)
  moreover have \<open>is_vars (dom \<M>) (eval_subst \<M> \<beta> \<sigma>)\<close>
    unfolding is_vars_def
    using eval_in_dom_if[OF \<beta>_val]
    by blast 
  then have \<open>\<M>,eval_subst \<M> \<beta> \<sigma> \<Turnstile> \<phi>\<close>
    using \<phi>_sat
    by blast 
  ultimately show \<open>\<M>,\<beta> \<Turnstile> \<phi>'\<close>
    by blast 
qed

lemma is_model_of_iff: \<open>is_model_of \<M> T \<longleftrightarrow> (\<forall> \<phi> \<in> T. is_model_of \<M> {\<phi>})\<close>
  unfolding is_model_of_def
  by blast 

lemma is_model_of_indiv: \<open>is_model_of \<M> T \<Longrightarrow> \<forall> \<sigma>. \<forall> \<phi> \<in> T. is_model_of \<M> {\<phi> \<cdot>\<^sub>f\<^sub>m \<sigma>}\<close>
  for
    T :: \<open>('f, 'p, 'v) fm set\<close> and
    \<M> :: \<open>('f, 'p, 'm) model\<close>
  by (meson is_model_of_iff model_is_model_of_all_subst)

lemma is_model_of_grounding: \<open>is_model_of \<M> T \<Longrightarrow> is_model_of \<M> (\<G> T)\<close>
  for
    T :: \<open>('f, 'p, 'v) fm set\<close> and
    \<M> :: \<open>('f, 'p, 'm) model\<close>
  using is_model_of_iff is_model_of_indiv
  by fastforce

subsubsection \<open>Grounding equi-satisfiability\<close>

lemma grounding_bot_is_bot[simp]: \<open>\<G> {\<^bold>\<bottom>} = {\<^bold>\<bottom>}\<close>
  using ex_ground_subst
  by auto

lemma \<open>\<not> N \<Turnstile>\<^sub>m \<^bold>\<bottom> \<longleftrightarrow> \<not> N \<Turnstile>\<^sub>\<G>\<^sub>m \<^bold>\<bottom>\<close>
  for
    N :: \<open>('f, 'p, 'v) fm set\<close> and
    m :: \<open>'m itself\<close>
proof (intro iffI)
  assume \<open>\<not> N \<Turnstile>\<^sub>m \<^bold>\<bottom>\<close>
  then have \<open>\<exists> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> N\<close>
    using unsat_iff_entails_bot
    by blast
  then have \<open>\<exists> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> (\<G> N)\<close>
    using is_model_of_grounding
    by blast
  then show \<open>\<not> N \<Turnstile>\<^sub>\<G>\<^sub>m \<^bold>\<bottom>\<close>
    using grounding_bot_is_bot unsat_iff_entails_bot
    by auto
next
  assume \<open>\<not> N \<Turnstile>\<^sub>\<G>\<^sub>m \<^bold>\<bottom>\<close>
  show \<open>\<not> N \<Turnstile>\<^sub>m \<^bold>\<bottom>\<close>
    (* TODO *)
    sorry 
qed

end (* context *)

subsubsection \<open>Other results\<close>

lemma satD:
  \<open>satisfiable T \<Longrightarrow>
    \<exists> \<M> :: ('f, 'p, ('f, 'v) tm) model. is_canonical \<M> (language T) \<and> is_model_of \<M> T\<close>
  for T :: \<open>('f, 'p, 'v) fm set\<close> .

lemma satI: \<open>\<exists> \<M> :: ('f, 'p, 'm) model. is_model_of \<M> T \<Longrightarrow> satisfiable T\<close>
  for T :: \<open>('f, 'p, 'v) fm set\<close>
  sorry 



section \<open>Filters and ultrafilters\<close> 

text \<open>
  We take a quick detour into set theory to define appropriate mathematical structures.
\<close>  

(* Definition 2.1 *)
locale filter =
  fixes
    F :: \<open>'a set set\<close> and
    S :: \<open>'a set\<close> 
  assumes
    S_not_empty: \<open>S \<noteq> {}\<close> and 
    F_family_of_subsets_of_S: \<open>F \<subseteq> Pow S\<close> and
    S_in_F: \<open>S \<in> F\<close> and
    empty_not_in_F: \<open>{} \<notin> F\<close> and
    closed_int: \<open>A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F\<close> and
    upwards_closed: \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> F\<close>
(* NOTE: This definition does not correspond to the one of the article.
 * In fact, the one in the article seems to be totally wrong and does not exclude the empty set
 * from being a filter of an empty set.
 * We also cannot prove the lemma 2.2 (counter example: \<open>F = {}\<close> and \<open>S = {}\<close>).
 *
 * Instead, we take the definition from the book:
 * ``Set Theory: The Third Millennium Edition, revised and expanded'' (pp 72-75)
 *
 * Other variants exists (e.g. without @{thm S_in_F}) but they should be all equivalent. *)
begin

lemma F_not_empty: \<open>F \<noteq> {}\<close>
  using S_in_F
  by blast

lemma in_F_subset_S: \<open>x \<in> F \<Longrightarrow> x \<subseteq> S\<close>
  using F_family_of_subsets_of_S
  by blast 

lemma closed_int': \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<inter> B \<in> F \<Longrightarrow> A \<in> F \<and> B \<in> F\<close>
proof (intro conjI) 
  assume
    A_subset_S: \<open>A \<subseteq> S\<close> and
    B_subset_S: \<open>B \<subseteq> S\<close> and 
    inter_in_F: \<open>A \<inter> B \<in> F\<close>

  have \<open>A \<inter> B \<subseteq> A\<close>
    by blast 
  then show \<open>A \<in> F\<close>
    using upwards_closed[OF in_F_subset_S[OF inter_in_F] A_subset_S inter_in_F]
    by auto 

  have \<open>A \<inter> B \<subseteq> B\<close>
    by blast
  then show \<open>B \<in> F\<close>
    using upwards_closed[OF in_F_subset_S[OF inter_in_F] B_subset_S inter_in_F]
    by blast 
qed

text \<open>
  A filter is maximal under inclusion if there does not exists a filter strictly containing it.
\<close> 

definition maximal :: bool where
  \<open>maximal \<longleftrightarrow> (\<nexists> F'. filter F' S \<and> F \<subset> F')\<close>

end (* locale filter *)

lemma Inter_non_empty_filter_family_is_filter:
  assumes
    \<F>_family_of_filters: \<open>\<F> = { F. filter F S }\<close> and
    \<F>_non_empty: \<open>\<F> \<noteq> {}\<close>
  shows
    \<open>filter (\<Inter> \<F>) S\<close>
  unfolding filter_def 
proof (intro conjI allI impI)
  fix A B

  show \<open>\<Inter> \<F> \<subseteq> Pow S\<close>
    by (metis CollectD Inter_subset \<F>_family_of_filters \<F>_non_empty filter.F_family_of_subsets_of_S) 
  show \<open>S \<noteq> {}\<close>
    using \<F>_family_of_filters \<F>_non_empty filter.S_not_empty
    by auto
  show \<open>S \<in> \<Inter> \<F>\<close>
    using \<F>_family_of_filters filter.S_in_F
    by auto
  show \<open>{} \<notin> \<Inter> \<F>\<close>
    using \<F>_family_of_filters \<F>_non_empty filter.empty_not_in_F
    by fastforce
  show \<open>A \<in> \<Inter> \<F> \<Longrightarrow> B \<in> \<Inter> \<F> \<Longrightarrow> A \<inter> B \<in> \<Inter> \<F>\<close>
    using \<F>_family_of_filters filter.closed_int
    by fastforce
  show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> \<Inter> \<F> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> \<Inter> \<F>\<close>
    (* Slow *)
    by (smt (verit, best) CollectD filter_def Inter_iff \<F>_family_of_filters) 
qed

lemma Union_chain_is_filter:
  assumes
    \<C>_filter_chain: \<open>subset.chain { F. filter F S } \<C>\<close> and
    \<C>_non_empty: \<open>\<C> \<noteq> {}\<close>
  shows
    \<open>filter (\<Union> \<C>) S\<close>
  unfolding filter_def
proof (intro conjI allI impI)
  fix A B

  show \<open>S \<noteq> {}\<close>
    by (metis \<C>_filter_chain \<C>_non_empty empty_Collect_eq filter.S_not_empty subset_chain_def
        subset_empty)
  show \<open>\<Union> \<C> \<subseteq> Pow S\<close>
    by (metis CollectD Sup_least \<C>_filter_chain filter.F_family_of_subsets_of_S subset_chain_def
        subset_iff)
  show \<open>S \<in> \<Union> \<C>\<close>
    by (metis CollectD Union_iff \<C>_filter_chain \<C>_non_empty filter.S_in_F subset_chain_def
        subset_empty subset_iff)
  show \<open>{} \<notin> \<Union> \<C>\<close>
    by (metis CollectD filter_def Union_iff \<C>_filter_chain subset_chain_def
        subset_iff)
  show \<open>A \<in> \<Union> \<C> \<Longrightarrow> B \<in> \<Union> \<C> \<Longrightarrow> A \<inter> B \<in> \<Union> \<C>\<close>
    using \<C>_filter_chain \<C>_non_empty
    unfolding filter_def
    by (smt (verit, del_insts) Union_iff mem_Collect_eq subsetD subset_chain_def subset_iff)
  show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> \<Union> \<C> \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> \<Union> \<C>\<close>
    using \<C>_filter_chain \<C>_non_empty
    unfolding filter_def
    by (smt (verit) Union_iff mem_Collect_eq subset_chain_def subset_iff)
qed

text \<open>
  The Finite Intersection Property (FIP):

  Every finite \<open>H = {X\<^sub>1, \<dots>, X\<^sub>n}\<close> proper subset of a family of sets \<open>\<G>\<close> has a non-empty intersection
  \<open>X\<^sub>1 \<inter> \<dots> \<inter> X\<^sub>n\<close>.
\<close> 

definition fip :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>fip G \<longleftrightarrow> (\<forall> H \<subseteq> G. finite H \<longrightarrow> \<Inter> H \<noteq> {})\<close>  

lemma trivial_filter: \<open>S \<noteq> {} \<Longrightarrow> filter {S} S\<close>
  unfolding filter_def
  by simp 

lemma Inter_finite_subset_in_filter_if: \<open>filter F S \<Longrightarrow> H \<noteq> {} \<Longrightarrow> H \<subseteq> F \<Longrightarrow> finite H \<Longrightarrow> \<Inter> H \<in> F\<close>
proof -
  assume
    F_filter: \<open>filter F S\<close> and
    H_subset: \<open>H \<subseteq> F\<close> and
    H_finite: \<open>finite H\<close> and
    H_not_empty: \<open>H \<noteq> {}\<close> 

  show \<open>\<Inter> H \<in> F\<close>
    using H_subset
  proof (induction rule: finite_ne_induct[OF H_finite H_not_empty]) 
    case insert: (2 x H')

    have \<open>x \<in> F\<close>
      using insert(5)
      by simp
    moreover have \<open>\<Inter> H' \<in> F\<close>
      using insert(4, 5)
      by auto
    ultimately show ?case
      using filter.closed_int[OF F_filter] 
      by simp 
  qed auto 
qed

lemma filter_has_fip: \<open>filter F S \<Longrightarrow> fip F\<close>
  unfolding fip_def
proof (intro allI impI)
  fix H

  assume
    F_filter: \<open>filter F S\<close> and
    H_subset_F: \<open>H \<subseteq> F\<close> and
    finite_H: \<open>finite H\<close>

  have \<open>\<forall> A \<in> H. \<forall> B \<in> H. A \<inter> B \<in> F\<close>
    using filter.closed_int[OF F_filter] H_subset_F
    by blast 

  have \<open>\<Inter> H \<in> F\<close>
    if \<open>H \<noteq> {}\<close>
    by (rule Inter_finite_subset_in_filter_if[OF F_filter that H_subset_F finite_H])
  then show \<open>\<Inter> H \<noteq> {}\<close>
    by (cases \<open>H = {}\<close>, auto simp add: filter.empty_not_in_F[OF F_filter]) 
qed

(* Lemma 2.3 *)
lemma fip_to_filter:
  assumes
    S_not_empty: \<open>S \<noteq> {}\<close> and 
    G_subset_\<P>_S: \<open>G \<subseteq> Pow S\<close> and
    fip_G: \<open>fip G\<close>
  obtains F where
    \<open>filter F S\<close> and
    \<open>G \<subseteq> F\<close>
proof (cases \<open>G = {}\<close>) 
  case True

  have \<open>filter {S} S\<close>
    using trivial_filter[OF S_not_empty]
    by blast 
  then show ?thesis
    using True that
    by blast
next
  case False
  
  define F where
    \<open>F \<equiv> { X. X \<subseteq> S \<and> (\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> X) }\<close>

  have \<open>filter F S\<close>
    unfolding filter_def
  proof (intro conjI allI impI)
    fix A B

    show \<open>S \<noteq> {}\<close>
      by (fact S_not_empty)
    show \<open>F \<subseteq> Pow S\<close>
      unfolding F_def
      by blast 
    show \<open>S \<in> F\<close>
    proof -
      have \<open>\<forall> A \<in> G. A \<subseteq> S\<close>
        using G_subset_\<P>_S
        by fast 
      then have \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> S\<close>
        using False
        by blast
      then show ?thesis
        unfolding F_def
        by blast
    qed
    show \<open>{} \<notin> F\<close> 
    proof (rule ccontr)
      assume \<open>\<not> {} \<notin> F\<close>
      then have \<open>{} \<in> F\<close>
        by blast
      then obtain H where
        \<open>H \<subseteq> G\<close> and
        \<open>finite H\<close> and
        \<open>\<Inter> H \<subseteq> {}\<close>
        unfolding F_def
        by blast
      then show \<open>False\<close>
        using fip_G
        unfolding fip_def
        by blast 
    qed
    show \<open>A \<in> F \<Longrightarrow> B \<in> F \<Longrightarrow> A \<inter> B \<in> F\<close>
    proof -
      assume
        A_in_F: \<open>A \<in> F\<close> and
        B_in_F: \<open>B \<in> F\<close>
      then have A_subset_S: \<open>A \<subseteq> S\<close> and B_subset_S: \<open>B \<subseteq> S\<close>
        unfolding F_def
        by blast+ 

      obtain H\<^sub>A H\<^sub>B where
        finite_H\<^sub>A: \<open>finite H\<^sub>A\<close> and
        H\<^sub>A_subset_G: \<open>H\<^sub>A \<subseteq> G\<close> and
        Int_H\<^sub>A_subset_A: \<open>\<Inter> H\<^sub>A \<subseteq> A\<close> and
        finite_H\<^sub>B: \<open>finite H\<^sub>B\<close> and
        H\<^sub>B_subset_G: \<open>H\<^sub>B \<subseteq> G\<close> and
        Int_H\<^sub>B_subset_B: \<open>\<Inter> H\<^sub>B \<subseteq> B\<close>
        using A_in_F B_in_F
        unfolding F_def
        by auto

      have \<open>H\<^sub>A \<union> H\<^sub>B \<subseteq> G\<close>
        using H\<^sub>A_subset_G H\<^sub>B_subset_G
        by auto 
      moreover have \<open>(\<Inter> H\<^sub>A) \<inter> (\<Inter> H\<^sub>B) \<subseteq> A \<inter> B\<close>
        using Int_H\<^sub>A_subset_A Int_H\<^sub>B_subset_B 
        by auto
      then have \<open>\<Inter> (H\<^sub>A \<union> H\<^sub>B) \<subseteq> A \<inter> B\<close>
        by blast 
      moreover have \<open>finite (H\<^sub>A \<union> H\<^sub>B)\<close>
        using finite_H\<^sub>A finite_H\<^sub>B
        by blast 
      ultimately have \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> A \<inter> B\<close>
        by blast  
      moreover have \<open>A \<inter> B \<subseteq> S\<close>
        using A_subset_S B_subset_S
        by blast 
      ultimately show ?thesis
        unfolding F_def
        by simp 
    qed
    show \<open>A \<subseteq> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow> A \<in> F \<Longrightarrow> A \<subseteq> B \<Longrightarrow> B \<in> F\<close>
      unfolding F_def
      by (smt (verit, best) mem_Collect_eq subset_trans) 
  qed
  moreover have \<open>G \<subseteq> F\<close>
    unfolding F_def
  proof (intro subsetI CollectI conjI)  
    fix A x
    assume \<open>A \<in> G\<close> and \<open>x \<in> A\<close>
    then show \<open>x \<in> S\<close>
      using G_subset_\<P>_S
      by blast
  next
    fix A
    assume \<open>A \<in> G\<close>
    moreover have \<open>\<Inter> {A} = A\<close>
      by simp 
    ultimately show \<open>\<exists> H \<subseteq> G. finite H \<and> \<Inter> H \<subseteq> A\<close>
      by (metis empty_subsetI finite.simps insert_subset subset_refl)
  qed
  ultimately show ?thesis
    by (rule that)
qed

text \<open>
  An ultrafilter \<open>F\<close> on \<open>S\<close> is a filter \<open>F\<close> on \<open>S\<close> for which, for all subset \<open>A\<close> of \<open>S\<close>,
  either \<open>A\<close> or \<open>S - A\<close> is in \<open>F\<close>.
\<close> 

locale ultrafilter = filter F S
  for
    F :: \<open>'a set set\<close> and
    S :: \<open>'a set\<close>
  + assumes
    maximality: \<open>A \<subseteq> S \<Longrightarrow> A \<in> F \<or> S - A \<in> F\<close> 

lemma ultrafilter_is_filter: \<open>ultrafilter F S \<Longrightarrow> filter F S\<close>
  unfolding ultrafilter_def
  by (elim conjunct1)

lemma filter_is_ultrafilter_if_maximal: \<open>filter F S \<and> filter.maximal F S \<longleftrightarrow> ultrafilter F S\<close> 
proof (intro iffI conjI; (elim conjE)?)
  assume
    F_filter: \<open>filter F S\<close> and 
    F_maximal: \<open>filter.maximal F S\<close>

  have S_not_empty: \<open>S \<noteq> {}\<close>
    by (fact filter.S_not_empty[OF F_filter]) 

  show \<open>ultrafilter F S\<close>
  proof (rule ccontr)
    assume \<open>\<not> ultrafilter F S\<close>
    then obtain Y where
      Y_subset_S: \<open>Y \<subseteq> S\<close> and
      Y_not_in_F: \<open>Y \<notin> F\<close> and
      compl_Y_not_in_F: \<open>S - Y \<notin> F\<close>
      by (meson F_filter ultrafilter.intro ultrafilter_axioms.intro) 

    have F_not_empty: \<open>F \<noteq> {}\<close>
      using F_filter filter.S_in_F
      by auto

    let ?G = \<open>F \<union> {Y}\<close>

    have \<open>fip ?G\<close>
      unfolding fip_def
    proof (intro allI impI)
      fix H
      assume
        H_subset: \<open>H \<subseteq> F \<union> {Y}\<close> and
        H_finite: \<open>finite H\<close> 

      have inter_Y_not_empty: \<open>X \<in> F \<Longrightarrow> X \<inter> Y \<noteq> {}\<close> for X
      proof (rule ccontr)
        assume
          X_in_F: \<open>X \<in> F\<close> and
          \<open>\<not> X \<inter> Y \<noteq> {}\<close>
        then have X_inter_Y_empty: \<open>X \<inter> Y = {}\<close>
          by blast
        then have \<open>X \<subseteq> S - Y\<close>
          by (metis Diff_partition Diff_subset_conv Diff_triv filter_def F_filter
              PowD X_in_F Y_subset_S subsetD) 
        then have \<open>S - Y \<in> F\<close>
          by (smt (verit, del_insts) Diff_subset F_filter X_in_F dual_order.strict_trans1
            filter.S_in_F filter.upwards_closed nless_le)  
        then show \<open>False\<close>
          using compl_Y_not_in_F
          by contradiction
      qed

      have H_minus_Y_subset_F: \<open>H - {Y} \<subseteq> F\<close>
        using H_subset
        by auto
      moreover have finite_H_minus_Y: \<open>finite (H - {Y})\<close>
        using H_finite
        by simp 
      ultimately have Inter_H_minus_Y_not_empty: \<open>\<Inter> (H - {Y}) \<noteq> {}\<close>
        using filter_has_fip[OF F_filter, unfolded fip_def, rule_format]
        by blast 

      show \<open>\<Inter> H \<noteq> {}\<close>
      proof (cases \<open>H - {Y} = {}\<close>) 
        case True
        then show ?thesis
          by (metis Diff_empty Diff_insert0 F_not_empty Int_empty_right Inter_H_minus_Y_not_empty
              cInf_singleton equals0I insert_Diff inter_Y_not_empty) 
      next
        case False

        have \<open>\<Inter> (H - {Y}) \<in> F\<close>
          by (rule Inter_finite_subset_in_filter_if
                [OF F_filter False H_minus_Y_subset_F finite_H_minus_Y])
        then have \<open>Y \<inter> \<Inter> (H - {Y}) \<noteq> {}\<close>
          using inter_Y_not_empty
          by auto 
        then show ?thesis
          by auto 
      qed
    qed
    moreover have \<open>?G \<subseteq> Pow S\<close>
      using F_filter Y_subset_S filter.F_family_of_subsets_of_S
      by blast
    ultimately obtain F' where
      \<open>?G \<subseteq> F'\<close> and 
      \<open>filter F' S\<close>
      using fip_to_filter[OF S_not_empty]
      by metis 
    then have \<open>\<not> filter.maximal F S\<close>
      unfolding filter.maximal_def[OF F_filter]
      using Y_not_in_F
      by blast
    then show \<open>False\<close>
      using F_maximal
      by contradiction
  qed
next
  show \<open>ultrafilter F S \<Longrightarrow> filter F S\<close>
    by (rule ultrafilter_is_filter) 
next
  assume F_ultrafilter: \<open>ultrafilter F S\<close>

  have F_filter: \<open>filter F S\<close>
    by (rule ultrafilter_is_filter[OF F_ultrafilter])

  have ultrafilter_def': \<open>A \<in> F \<or> S - A \<in> F\<close>
    if \<open>A \<subset> S\<close> 
    for A
    using ultrafilter.maximality[OF F_ultrafilter] that
    by blast 

  show \<open>filter.maximal F S\<close>
  proof (rule ccontr)
    assume \<open>\<not> filter.maximal F S\<close>
    then obtain F' A where
      F_subset: \<open>F \<subset> F'\<close> and
      F'_filter: \<open>filter F' S\<close> and
      A_in: \<open>A \<in> F' - F\<close> 
      unfolding filter.maximal_def[OF F_filter]
      by blast
    then have \<open>S - A \<in> F\<close>
      by (metis DiffD1 DiffD2 F_filter PowD antisym_conv1 filter.F_family_of_subsets_of_S
          filter.S_in_F subsetD ultrafilter_def') 
    then show \<open>False\<close>
      by (metis A_in DiffD1 Diff_disjoint F'_filter F_subset filter.closed_int filter.empty_not_in_F
          psubsetD) 
  qed
qed

(* Lemma 2.2 *)
lemma filter_to_ultrafilter : \<open>filter F S \<Longrightarrow> \<exists> F'. F \<subseteq> F' \<and> ultrafilter F' S\<close>
proof -
  assume F_filter: \<open>filter F S\<close>

  let ?P = \<open>{ F'. filter F' S \<and> F \<subseteq> F' }\<close> 

  have P_not_empty: \<open>?P \<noteq> {}\<close>
    using F_filter
    by blast

  have \<open>\<Union> \<C> \<in> ?P\<close>
    if \<open>subset.chain ?P \<C>\<close> and \<open>\<C> \<noteq> {}\<close> 
    for \<C>
  proof -
    have \<open>filter (\<Union> \<C>) S\<close>
      by (smt (verit) Union_chain_is_filter mem_Collect_eq subset_chain_def subset_iff that) 
    then show \<open>\<Union> \<C> \<in> ?P\<close>
      by (metis (no_types, lifting) CollectD CollectI Sup_bot_conv(1) Sup_upper2 filter.F_not_empty
          subsetD subset_chain_def that(1))
  qed
  then obtain U where
    U_in_P: \<open>U \<in> ?P\<close> and
    \<open>\<forall> X \<in> ?P. U \<subseteq> X \<longrightarrow> X = U\<close>
    using subset_Zorn_nonempty[OF P_not_empty]
    by force
  then have \<open>ultrafilter U S\<close>
    by (smt (verit, del_insts) dual_order.trans filter.maximal_def filter_is_ultrafilter_if_maximal
        mem_Collect_eq psubsetE)
  then show ?thesis
    using U_in_P
    by blast
qed   



section \<open>Ultraproducts\<close> 

locale ultraprod =
  fixes
    I :: \<open>'i set\<close> and
    F :: \<open>'i set set\<close> and
    \<M> :: \<open>'i \<Rightarrow> ('f, 'p, 'm) model\<close> and 
    VARs :: \<open>'i \<Rightarrow> 'v \<Rightarrow> 'm\<close>
  assumes
    all_structs: \<open>\<forall> i \<in> I. is_vars (dom (\<M> i)) (VARs i)\<close> and
    F_ultrafilter: \<open>ultrafilter F I\<close>
begin 

lemma F_filter: \<open>filter F I\<close>
  by (rule ultrafilter_is_filter[OF F_ultrafilter]) 

text \<open>
  We go back to model theory.

  First, we define a natural equivalence relation on the indexed cartesian product.
\<close>

abbreviation prod_eq :: \<open>('i \<Rightarrow> 'm) rel\<close> (\<open>'(\<sim>')\<close>) where
  \<open>prod_eq \<equiv>
    { (f, g). f \<in> (\<Pi> i \<in> I. dom (\<M> i)) \<and> g \<in> (\<Pi> i \<in> I. dom (\<M> i)) \<and> {i \<in> I. f i = g i} \<in> F }\<close>

lemma refl_prod_eq: \<open>refl_on (\<Pi> i \<in> I. dom (\<M> i)) (\<sim>)\<close>
proof
  show \<open>(\<sim>) \<subseteq> (\<Pi> i \<in> I. dom (\<M> i)) \<times> (\<Pi> i \<in> I. dom (\<M> i))\<close>
    by blast 
next 
  fix f 
  assume f_in: \<open>f \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
  then show \<open>(f, f) \<in> (\<sim>)\<close>
  proof -
    have \<open>{i \<in> I. f i = f i} = I\<close>
      by auto 
    moreover have \<open>I \<in> F\<close>
      using filter.S_in_F[OF F_filter] .
    ultimately have \<open>{i \<in> I. f i = f i} \<in> F\<close>
      by presburger 
    then show ?thesis
      using f_in
      by blast 
  qed
qed 

lemma sym_prod_eq: \<open>sym (\<sim>)\<close>
proof
  fix f g :: \<open>'i \<Rightarrow> 'm\<close>
  assume f_sim_g: \<open>(f, g) \<in> (\<sim>)\<close>
  then have \<open>{i \<in> I. f i = g i} \<in> F\<close>
    by blast 
  then have \<open>{i \<in> I. g i = f i} \<in> F\<close>
    by (smt (verit, ccfv_threshold) Collect_cong) 
  then show \<open>(g, f) \<in> (\<sim>)\<close>
    using f_sim_g
    by blast 
qed

lemma trans_prod_eq: \<open>trans (\<sim>)\<close>
proof
  fix f g h
  assume
    f_sim_g: \<open>(f, g) \<in> (\<sim>)\<close> and
    g_sim_h: \<open>(g, h) \<in> (\<sim>)\<close>
  then have
    \<open>{i \<in> I. f i = g i} \<in> F\<close> (is \<open>?S1 \<in> _\<close>) and
    \<open>{i \<in> I. g i = h i} \<in> F\<close> (is \<open>?S2 \<in> _\<close>)
    by blast+
  then have \<open>?S1 \<inter> ?S2 \<in> F\<close>
    using filter.closed_int[OF F_filter]
    by blast
  then have \<open>{i \<in> I. f i = g i \<and> g i = h i} \<in> F\<close> (is \<open>?S3 \<in> _\<close>)
    by (simp add: Collect_conj_eq Int_left_commute inf.commute)
  moreover have \<open>?S3 \<subseteq> {i \<in> I. f i = h i}\<close>
    by auto 
  moreover have \<open>{i \<in> I. f i = h i} \<subseteq> I\<close>
    by auto 
  ultimately show \<open>(f, h) \<in> (\<sim>)\<close>
    using filter.upwards_closed[OF F_filter, of \<open>{i \<in> I. f i = g i \<and> g i = h i}\<close>] f_sim_g g_sim_h
    by blast   
qed

lemma equiv_prod_eq: \<open>equiv (\<Pi> i \<in> I. dom (\<M> i)) (\<sim>)\<close>
  by (simp add: equivI refl_prod_eq sym_prod_eq trans_prod_eq) 


lemma prod_eq_class_nonempty: \<open>f \<in> (\<Pi> i \<in> I. dom (\<M> i)) \<Longrightarrow> prod_eq `` {f} \<noteq> {}\<close>
  using equiv_class_self equiv_prod_eq
  by fastforce

text \<open>
  The ultraproduct of \<open>S\<close> by the ultrafilter \<open>U\<close> is the quotient set of the cartesian product
  \<open>\<Pi> i \<in> I. S i\<close> by the equivalence relation \<open>prod_eq' I U\<close>.
\<close> 

(* Definition 2.5 *)
abbreviation ultraproduct :: \<open>('i \<Rightarrow> 'm set) \<Rightarrow> ('i \<Rightarrow> 'm) set set\<close> where
  \<open>ultraproduct S \<equiv> (\<Pi> i \<in> I. S i) // (\<sim>)\<close>

lemma ultraproduct_nonempty: \<open>\<forall> i \<in> I. S i \<noteq> {} \<Longrightarrow> ultraproduct S \<noteq> {}\<close>
  by auto

section \<open>Models, using ultraproducts\<close>

definition rep :: \<open>('i \<Rightarrow> 'm) set \<Rightarrow> 'i \<Rightarrow> 'm\<close> where
  \<open>rep cls = (\<some> x. x \<in> cls)\<close>

lemma rep_in_cls: \<open>C \<noteq> {} \<Longrightarrow> rep C \<in> C\<close>
  unfolding rep_def
  by (simp add: some_in_eq)

lemma rep_relates_to_elem_of_equiv_class:
  \<open>f \<in> (\<Pi> i \<in> I. dom (\<M> i)) \<Longrightarrow> (rep ((\<sim>) `` {f}), f) \<in> (\<sim>)\<close>
  unfolding rep_def
  by (metis (no_types, lifting) Image_singleton_iff equiv_class_self equiv_prod_eq someI_ex sym_def
      sym_prod_eq) 

lemma rep_of_elem_ultraproduct_in_pi:
  \<open>x \<in> ultraproduct (dom \<circ> \<M>) \<Longrightarrow> rep x \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
  using equiv_Eps_preserves equiv_prod_eq rep_def
  by auto

lemma elem_in_pi_to_ultraproduct:
  \<open>x \<in> (\<Pi> i \<in> I. dom (\<M> i)) \<Longrightarrow> (\<sim>) `` {x} \<in> ultraproduct (dom \<circ> \<M>)\<close>
  by (metis (no_types, lifting) Pi_iff comp_apply quotientI) 

lemma elem_eq_class_in_pi: \<open>(\<sim>) `` {f} \<in> ultraproduct (dom \<circ> \<M>) \<Longrightarrow> f \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
  by (smt (verit, del_insts) Pi_iff comp_def disjnt_equiv_class equiv_class_eq_iff equiv_prod_eq
      quotientE) 

lemma struct_Mi: \<open>\<forall> i \<in> I. struct (dom (\<M> i)) (interp_fn (\<M> i)) (interp_rel (\<M> i))\<close>
  using model_is_struct
  by blast 

lemma vars_Mi: \<open>\<forall> i \<in> I. is_vars (dom (\<M> i)) (VARs i)\<close>
  using all_structs
  by blast

text \<open>
  The model \<open>\<UU>\<close> on universe \<open>A\<close> is obtained by interpreting the language as follows:
  \<^item> If \<open>P(x\<^sub>1, \<dots>, x\<^sub>n)\<close> is a predicate, then \<open>P\<^sup>\<UU>([f\<^sub>1], \<dots>, [f\<^sub>n])\<close> iff
    \<open>{x \<in> I. P\<^bsup>\<UU>\<^sub>x\<^esup>(f\<^sub>1(x), \<dots>, f\<^sub>n(x))} \<in> F\<close>;
  \<^item> If \<open>F(x\<^sub>1, \<dots>, x\<^sub>n)\<close> is a function, then \<open>F\<^sup>U([f\<^sub>1], \<dots>, [f\<^sub>n]) = [f]\<close> where
    for all \<open>x \<in> I\<close>, \<open>f(x) = F\<^bsup>\<UU>\<^sub>x\<^esup>(f\<^sub>1(x), \<dots>, f\<^sub>n(x))\<close>.
\<close>

abbreviation A :: \<open>('i \<Rightarrow> 'm) set set\<close> where
  \<open>A \<equiv> ultraproduct (dom \<circ> \<M>)\<close>

lemma A_nonempty: \<open>A \<noteq> {}\<close>
  using struct_Mi struct.M_nonempty
  by auto 

definition FN :: \<open>'f \<Rightarrow> ('i \<Rightarrow> 'm) set list \<Rightarrow> ('i \<Rightarrow> 'm) set\<close> where
  \<open>FN f e \<equiv> (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [rep e\<^sub>i i. e\<^sub>i \<leftarrow> e]}\<close>

definition REL :: \<open>'p \<Rightarrow> ('i \<Rightarrow> 'm) set list set\<close> where
  \<open>REL p = {e. (\<forall> x \<in> set e. x \<in> A) \<and> {i \<in> I. [rep e\<^sub>i i. e\<^sub>i \<leftarrow> e] \<in> interp_rel (\<M> i) p} \<in> F}\<close> 

sublocale \<A>_struct: struct A FN REL
  unfolding struct_def 
proof (intro allI impI conjI ballI)
  show \<open>A \<noteq> {}\<close>
    by (fact A_nonempty)
next
  fix f es
  assume \<open>\<forall> e \<in> set es. e \<in> A\<close>
  then have \<open>\<forall> e \<in> set es. rep e \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
    using A_nonempty rep_of_elem_ultraproduct_in_pi
    by auto 
  then have \<open>\<forall> e \<in> set [rep e\<^sub>i. e\<^sub>i \<leftarrow> es]. e \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
    by simp 
  then have \<open>\<forall> e \<in> set [rep e\<^sub>i. e\<^sub>i \<leftarrow> es]. \<forall> i \<in> I. e i \<in> dom (\<M> i)\<close>
    by blast
  then have \<open>\<forall> i \<in> I. \<forall> e \<in> set [rep e\<^sub>i i. e\<^sub>i \<leftarrow> es]. e \<in> dom (\<M> i)\<close>
    by simp 
  then have \<open>interp_fn (\<M> i) f [rep e\<^sub>i i. e\<^sub>i \<leftarrow> es] \<in> dom (\<M> i)\<close>
    if \<open>i \<in> I\<close> 
    for i
    using struct.FN_dom_to_dom[OF struct_Mi[rule_format, OF that]] that 
    by blast
  then have \<open>(\<lambda> i \<in> I. interp_fn (\<M> i) f [rep e\<^sub>i i. e\<^sub>i \<leftarrow> es]) \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
    by blast 
  then show \<open>FN f es \<in> A\<close>
    unfolding FN_def
    by (smt (verit, best) Pi_mono comp_eq_dest_lhs quotientI subset_iff)
next
  fix p es e
  assume
    \<open>es \<in> REL p\<close> and
    e_in: \<open>e \<in> set es\<close>
  then have \<open>\<forall> e \<in> set es. e \<in> A\<close> and \<open>{i \<in> I. [rep e\<^sub>i i. e\<^sub>i \<leftarrow> es] \<in> interp_rel (\<M> i) p} \<in> F\<close> 
    unfolding REL_def
    by blast+  
  then show \<open>e \<in> A\<close>
    using e_in
    by blast
qed  

abbreviation \<open>\<A> \<equiv> Abs_model (A, FN, REL)\<close> 

lemma dom_\<A> [simp]: \<open>dom \<A> = A\<close>
  using \<A>_struct.struct_axioms
  by auto 

lemma interp_fn_\<A> [simp]: \<open>interp_fn \<A> = FN\<close>
  using \<A>_struct.struct_axioms
  by auto

lemma interp_rel_\<A> [simp]: \<open>interp_rel \<A> = REL\<close>
  using \<A>_struct.struct_axioms
  by auto

text \<open>
  We show that the choice of representatives in \<open>\<UU>\<close> does not matter. 
\<close>

lemma list_all2_iff_eq_maps:
  assumes
    \<open>length xs = length ys\<close> 
  shows
    \<open>list_all2 (\<lambda> x y. f x = g y) xs ys \<longleftrightarrow> [f x. x \<leftarrow> xs] = [g y. y \<leftarrow> ys]\<close>
  by (induction xs ys rule: list_induct2', auto) 

lemma lists_related_to_inter_in_filter:
  assumes
    \<open>as \<noteq> []\<close> and
    \<open>length as = length bs\<close> and
    \<open>list_all2 (in_rel (\<sim>)) as bs\<close>
  shows \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)) \<in> F\<close>
proof -
  have \<open>list_all (\<lambda> A. A \<in> F) (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)\<close>
    using assms(2, 3)
    by (auto simp add: list_all2_conv_all_nth list_all_length)
  then show \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)) \<in> F\<close>
    using assms(2, 3)
  proof (induction arbitrary: bs rule: list_nonempty_induct[OF assms(1)])
    case (1 x)
    then obtain y where
      \<open>bs = [y]\<close> and
      \<open>(x, y) \<in> (\<sim>)\<close>
      by (metis (no_types, lifting) in_rel_def list_all2_Cons1 list_all2_Nil) 
    then have
      \<open>map2 (\<lambda> a b. {i \<in> I. a i = b i}) [x] bs = [{i \<in> I. x i = y i}]\<close> and
      \<open>{i \<in> I. x i = y i} \<in> F\<close> 
      by simp+
    then show ?case
      by auto 
  next
    case (2 x xs)
    then obtain y ys where
      bs_is: \<open>bs = y # ys\<close> and
      x_sym_y: \<open>(x, y) \<in> (\<sim>)\<close> and
      \<open>list_all2 (in_rel (\<sim>)) xs ys\<close> and
      \<open>length xs = length ys\<close>
      by (smt (verit, best) in_rel_def list_all2_Cons1 list_all2_lengthD) 
    then have \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) xs ys)) \<in> F\<close>
      using "2.IH" "2.prems"(1)
      by fastforce
    moreover have \<open>{i \<in> I. x i = y i} \<in> F\<close>
      using x_sym_y
      by blast
    ultimately have \<open>{i \<in> I. x i = y i} \<inter> \<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) xs ys)) \<in> F\<close>
      using filter.closed_int[OF F_filter]
      by blast 
    then show ?case
      unfolding bs_is
      by simp  
  qed
qed

lemma inter_map2_to_set_compr:
  assumes
    \<open>as \<noteq> []\<close> and 
    \<open>length as = length bs\<close> and
    \<open>list_all2 (in_rel (\<sim>)) as bs\<close>
  shows \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)) =
    {i \<in> I. \<forall> (a, b) \<in> set (zip as bs). a i = b i}\<close>
  using assms(2, 3)
proof (induction arbitrary: bs rule: list_nonempty_induct[OF assms(1)])
  case (1 x)
  then obtain y where
    bs_is: \<open>bs = [y]\<close> and
    \<open>(x, y) \<in> (\<sim>)\<close>
    by (metis (no_types, lifting) in_rel_def list_all2_Cons1 list_all2_Nil) 
  then show ?case
    unfolding bs_is
    by simp 
next
  case (2 x xs)
  then obtain y ys where
    bs_is: \<open>bs = y # ys\<close> and
    \<open>(x, y) \<in> (\<sim>)\<close> and
    \<open>list_all2 (in_rel (\<sim>)) xs ys\<close> and
    \<open>length xs = length ys\<close>
    by (smt (verit, ccfv_SIG) in_rel_def list_all2_Cons1 list_all2_lengthD) 
  then have \<open>\<Inter> (set (map2 (\<lambda> x y. {i \<in> I. x i = y i}) xs ys)) =
    {i \<in> I. \<forall> (a, b) \<in> set (zip xs ys). a i = b i}\<close>
    using "2.IH"
    by presburger
  then have \<open>{i \<in> I. x i = y i} \<inter> \<Inter> (set (map2 (\<lambda> x y. {i \<in> I. x i = y i}) xs ys)) =
    {i \<in> I. x i = y i} \<inter> {i \<in> I. \<forall> (a, b) \<in> set (zip xs ys). a i = b i}\<close>
    by blast 
  moreover have \<open>{i \<in> I. x i = y i} \<inter> \<Inter> (set (map2 (\<lambda> x y. {i \<in> I. x i = y i}) xs ys)) =
    \<Inter> (set (map2 (\<lambda> x y. {i \<in> I. x i = y i}) (x # xs) (y # ys)))\<close>
    by simp 
  moreover have \<open>{i \<in> I. x i = y i} \<inter> {i \<in> I. \<forall> (a, b) \<in> set (zip xs ys). a i = b i} =
    {i \<in> I. \<forall> (a, b) \<in> set (zip (x # xs) (y # ys)). a i = b i}\<close>
  proof -
    have \<open>{i \<in> I. x i = y i} \<inter> {i \<in> I. \<forall> (a, b) \<in> set (zip xs ys). a i = b i} =
      {i \<in> I. x i = y i \<and> (\<forall> (a, b) \<in> set (zip xs ys). a i = b i)}\<close>
      by blast
    also have \<open>... = {i \<in> I. \<forall> (a, b) \<in> set (zip (x # xs) (y # ys)). a i = b i}\<close>
      by auto 
    finally show ?thesis . 
  qed
  ultimately show ?case
    unfolding bs_is
    by simp 
qed 

lemma well_definedness_REL:
  assumes
    \<open>length as = length bs\<close> and
    \<open>list_all2 (in_rel (\<sim>)) as bs\<close>
  shows
    \<open>{i \<in> I. [a i. a \<leftarrow> as] \<in> interp_rel (\<M> i) p} \<in> F \<longleftrightarrow>
       {i \<in> I. [b i. b \<leftarrow> bs] \<in> interp_rel (\<M> i) p} \<in> F\<close>
proof (cases \<open>as = []\<close>) 
  case True
  then have \<open>bs = []\<close>
    using assms(1)
    by simp 
  then show ?thesis
    using True
    by auto
next
  case False
  then have bs_not_empty: \<open>bs \<noteq> []\<close>
    using assms(1)
    by auto

  have dummy_A_in_F: \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)) \<in> F\<close>
    (is \<open>?A \<in> _\<close>)
    by (rule lists_related_to_inter_in_filter[OF False assms(1, 2)]) 

  have dummy_A_is: \<open>?A = {i \<in> I. \<forall> (a, b) \<in> set (zip as bs). a i = b i}\<close>
    by (fact inter_map2_to_set_compr[OF False assms(1, 2)]) 

  let ?Pa = \<open>{i \<in> I. [a i. a \<leftarrow> as] \<in> interp_rel (\<M> i) p}\<close>
  let ?Pb = \<open>{i \<in> I. [b i. b \<leftarrow> bs] \<in> interp_rel (\<M> i) p}\<close>

  have Pa_inter_A_eq_Pb_inter_A: \<open>?Pa \<inter> ?A = ?Pb \<inter> ?A\<close>
    unfolding dummy_A_is
  proof -
    have \<open>?Pa \<inter> {i \<in> I. \<forall> (a, b) \<in> set (zip as bs). a i = b i} =
      {i \<in> I. [a i. a \<leftarrow> as] \<in> interp_rel (\<M> i) p \<and> (\<forall> (a, b) \<in> set (zip as bs). a i = b i)}\<close>
      (is \<open>?lhs = _\<close>)
      by fastforce 
    also have
      \<open>... = {i \<in> I. [b i. b \<leftarrow> bs] \<in> interp_rel (\<M> i) p \<and> (\<forall> (a, b) \<in> set (zip as bs). a i = b i)}\<close>
      using assms(1, 2)
    proof (induction arbitrary: bs rule: list_nonempty_induct[OF False])
      case (1 x)
      then obtain y where
        bs_is: \<open>bs = [y]\<close> and
        \<open>(x, y) \<in> (\<sim>)\<close>
        by (metis (no_types, lifting) in_rel_def list_all2_Cons1 list_all2_Nil) 
      then show ?case
        unfolding bs_is
        by fastforce 
    next
      case (2 x xs)
      then obtain y ys where
        bs_is: \<open>bs = y # ys\<close> and
        \<open>(x, y) \<in> (\<sim>)\<close> and
        \<open>list_all2 (in_rel (\<sim>)) xs ys\<close> and
        len_eq: \<open>length xs = length ys\<close>
        by (smt (verit, best) in_rel_def list_all2_Cons1 list_all2_lengthD) 
      then have
        \<open>{i \<in> I. [a i. a \<leftarrow> xs] \<in> interp_rel (\<M> i) p \<and> (\<forall> (a, b) \<in> set (zip xs ys). a i = b i)} =
        {i \<in> I. [b i. b \<leftarrow> ys] \<in> interp_rel (\<M> i) p \<and> (\<forall> (a, b) \<in> set (zip xs ys). a i = b i)}\<close>
        using "2.IH"
        by presburger

      show ?case
        unfolding bs_is
      proof (intro subset_antisym subsetI; clarsimp)
        fix i
        assume
          \<open>i \<in> I\<close> and
          \<open>(y i # map (\<lambda> a. a i) xs) \<in> interp_rel (\<M> i) p\<close> and 
          \<open>x i = y i\<close> and 
          \<open>\<forall> (a, b) \<in> set (zip xs ys). a i = b i\<close>
        then show \<open>(y i # map (\<lambda> b. b i) ys) \<in> interp_rel (\<M> i) p\<close>
          using len_eq
        proof (induction xs ys rule: list_induct2')
          case (4 x' xs' y' ys')
          then have \<open>list_all2 (\<lambda> a b. a i = b i) (x' # xs') (y' # ys')\<close>
            by (meson list_all2I)
          then have \<open>[b i. b \<leftarrow> y' # ys'] = [a i. a \<leftarrow> x' # xs']\<close>
            unfolding list_all2_iff_eq_maps[OF "4.prems"(5)] 
            by simp 
          then show ?case
            using "4.prems"(2)
            by presburger
        qed auto 
      next
        fix i
        assume
          \<open>i \<in> I\<close> and
          \<open>(y i # map (\<lambda> a. a i) ys) \<in> interp_rel (\<M> i) p\<close> and 
          \<open>x i = y i\<close> and 
          \<open>\<forall> (a, b) \<in> set (zip xs ys). a i = b i\<close>
        then show \<open>(y i # map (\<lambda> b. b i) xs) \<in> interp_rel (\<M> i) p\<close>
          using len_eq 
        proof (induction xs ys rule: list_induct2')
          case (4 x' xs' y' ys')
          then have \<open>list_all2 (\<lambda> a b. a i = b i) (x' # xs') (y' # ys')\<close>
            by (meson list_all2I) 
          then have \<open>[b i. b \<leftarrow> y' # ys'] = [a i. a \<leftarrow> x' # xs']\<close>
            unfolding list_all2_iff_eq_maps[OF "4.prems"(5)]
            by simp 
          then show ?case
            using "4.prems"(2)
            by presburger
        qed auto 
      qed
    qed
    also have
      \<open>... = ?Pb \<inter> {i \<in> I. \<forall> (a, b) \<in> set (zip as bs). a i = b i}\<close>
      (is \<open>_ = ?rhs\<close>)
      by fastforce 
    finally show \<open>?lhs = ?rhs\<close> .
  qed
  then show \<open>?Pa \<in> F \<longleftrightarrow> ?Pb \<in> F\<close>
    using filter.closed_int[OF F_filter] filter.upwards_closed[OF F_filter]
    by (smt (verit, ccfv_threshold) CollectD dummy_A_in_F inf_le1 subset_eq) 
  (* proof (intro iffI)
   *   assume \<open>?Pa \<in> F\<close>
   *   then have \<open>?Pa \<inter> ?A \<in> F\<close>
   *     using filter.closed_int[OF F_filter _ dummy_A_in_F]
   *     by blast 
   *   moreover have \<open>?Pa \<inter> ?A \<subseteq> ?Pb\<close>
   *     using Pa_inter_A_eq_Pb_inter_A
   *     by blast  
   *   ultimately show \<open>?Pb \<in> F\<close>
   *     using filter.upwards_closed[OF F_filter]
   *     by (metis (no_types, lifting) CollectD F_filter filter.in_F_subset_S subsetI) 
   * next
   *   assume \<open>?Pb \<in> F\<close>
   *   then have \<open>?Pb \<inter> ?A \<in> F›
   *     using filter.closed_int[OF F_filter _ dummy_A_in_F]
   *     by blast
   *   moreover have \<open>?Pb \<inter> ?A \<subseteq> ?Pa\<close>
   *     using Pa_inter_A_eq_Pb_inter_A
   *     by blast 
   *   ultimately show \<open>?Pa \<in> F\<close>
   *     using filter.upwards_closed[OF F_filter]
   *     by (metis (no_types, lifting) CollectD F_filter filter.in_F_subset_S subsetI) 
   * qed *)
qed

lemma well_definedness_FN:
  assumes
    \<open>length as = length bs\<close> and
    \<open>list_all2 (in_rel (\<sim>)) as bs\<close>
  shows
    \<open>(\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [a i. a \<leftarrow> as]} =
       (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [b i. b \<leftarrow> bs]}\<close>
proof (cases \<open>as = []\<close>) 
  case True
  then have \<open>bs = []\<close>
    using assms(1)
    by simp 
  then show ?thesis
    using True
    by fastforce 
next
  case False

  have
    all_as_in_Pi: \<open>list_all (\<lambda> a. a \<in> (\<Pi> i \<in> I. dom (\<M> i))) as\<close> and
    all_bs_in_Pi: \<open>list_all (\<lambda> b. b \<in> (\<Pi> i \<in> I. dom (\<M> i))) bs\<close>
    using assms(1, 2)
    by (induction as bs rule: list_induct2', auto) 

  have \<open>{i \<in> I. interp_fn (\<M> i) f [a i. a \<leftarrow> as] = interp_fn (\<M> i) f [b i. b \<leftarrow> bs]} \<in> F\<close>
  proof - 
    have dummy_A_in_F: \<open>\<Inter> (set (map2 (\<lambda> a b. {i \<in> I. a i = b i}) as bs)) \<in> F\<close>
      (is \<open>?A \<in> _\<close>)
      by (fact lists_related_to_inter_in_filter[OF False assms(1, 2)]) 

    have dummy_A_is: \<open>?A = {i \<in> I. \<forall> (a, b) \<in> set (zip as bs). a i = b i}\<close>
      (is \<open>_ = ?B\<close>)
      by (fact inter_map2_to_set_compr[OF False assms(1, 2)]) 
    then have \<open>?B \<in> F\<close>
      using dummy_A_in_F
      by fastforce
    moreover have \<open>?B \<subseteq> {i \<in> I. [a i. a \<leftarrow> as] = [b i. b \<leftarrow> bs]}\<close>
      using assms(1) 
      by (induct as bs rule: list_induct2', auto)
    ultimately have \<open>{i \<in> I. [a i. a \<leftarrow> as] = [b i. b \<leftarrow> bs]} \<in> F\<close>
      using filter.upwards_closed[OF F_filter]
      by (metis (mono_tags, lifting) CollectD subsetI) 
    moreover have
      \<open>{i \<in> I. [a i. a \<leftarrow> as] = [b i. b \<leftarrow> bs]} \<subseteq>
       {i \<in> I. interp_fn (\<M> i) f [a i. a \<leftarrow> as] = interp_fn (\<M> i) f [b i. b \<leftarrow> bs]}\<close>
      by auto 
    ultimately show ?thesis
      using filter.upwards_closed[OF F_filter] 
      by (metis (no_types, lifting) CollectD subsetI) 
  qed
  moreover have \<open>(\<lambda> i \<in> I. interp_fn (\<M> i) f [a i. a \<leftarrow> as]) \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
  proof -
    have \<open>list_all (\<lambda> a. a \<in> (\<Pi> i \<in> I. dom (\<M> i))) as\<close>
      by (fact all_as_in_Pi)
    then have \<open>list_all (\<lambda> a. a i \<in> dom (\<M> i)) as\<close>
      if \<open>i \<in> I\<close>
      for i
      by (metis (no_types, lifting) PiE list.pred_mono_strong that) 
    then have \<open>interp_fn (\<M> i) f [a i. a \<leftarrow> as] \<in> dom (\<M> i)\<close>
      if \<open>i \<in> I\<close>
      for i
      using
        struct.FN_dom_to_dom[OF struct_Mi[rule_format, OF that], rule_format, of \<open>[a i. a \<leftarrow> as]\<close> f]
      by (smt (verit, del_insts) imageE list.pred_set list.set_map that) 
    then show ?thesis
      by blast 
  qed
  moreover have \<open>(\<lambda> i \<in> I. interp_fn (\<M> i) f [b i. b \<leftarrow> bs]) \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
  proof -
    have \<open>list_all (\<lambda> b. b \<in> (\<Pi> i \<in> I. dom (\<M> i))) bs\<close>
      by (fact all_bs_in_Pi)
    then have \<open>list_all (\<lambda> b. b i \<in> dom (\<M> i)) bs\<close>
      if \<open>i \<in> I\<close>
      for i
      by (metis (no_types, lifting) PiE list.pred_mono_strong that) 
    then have \<open>interp_fn (\<M> i) f [b i. b \<leftarrow> bs] \<in> dom (\<M> i)\<close>
      if \<open>i \<in> I\<close>
      for i
      using
        struct.FN_dom_to_dom[OF struct_Mi[rule_format, OF that], rule_format, of \<open>[b i. b \<leftarrow> bs]\<close> f]
      by (smt (verit, del_insts) imageE list.pred_set list.set_map that) 
    then show ?thesis
      by blast 
  qed
  ultimately have
    \<open>(\<lambda> i \<in> I. interp_fn (\<M> i) f [a i. a \<leftarrow> as], \<lambda> i \<in> I. interp_fn (\<M> i) f [b i. b \<leftarrow> bs]) \<in> (\<sim>)\<close>
    by (smt (verit, best) Collect_cong case_prodI mem_Collect_eq restrict_apply') 

  then show ?thesis
    unfolding equiv_class_eq_iff[OF equiv_prod_eq]
    by fastforce 
qed

lemma fun_upd_rep_is_rep_fun_upd: \<open>(\<lambda> v. rep (\<beta> v) i)(x := rep a i) = (\<lambda> v. rep ((\<beta>(x := a)) v) i)\<close>
proof -
  have \<open>(\<lambda> v. rep (\<beta> v) i)(x := rep a i) = (\<lambda> v. if v = x then rep a i else rep (\<beta> v) i)\<close>
    by fastforce 
  also have \<open>... = (\<lambda> v. (if v = x then rep a else rep (\<beta> v)) i)\<close>
    by fastforce  
  also have \<open>... = (\<lambda> v. rep (if x = v then a else \<beta> v) i)\<close>
    by fastforce 
  also have \<open>... = (\<lambda> v. rep ((\<beta>(x := a)) v) i)\<close>
    by fastforce 
  finally show ?thesis . 
qed

lemma lam_i_eval_in_Pi:
  assumes \<open>is_vars (dom \<A>) \<beta>\<close> 
  shows \<open>(\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>) \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close>
proof (induction t) 
  case (Var v)
  then show ?case
    using assms
    unfolding is_vars_def
    using equiv_Eps_preserves[OF equiv_prod_eq] rep_def rep_of_elem_ultraproduct_in_pi
    by fastforce
next
  case (Fun f ts)

  have \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M> i,\<lambda>v. rep (\<beta> v) i\<^esup> = interp_fn (\<M> i) f [\<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>. t \<leftarrow> ts]\<close>
    if \<open>i \<in> I\<close>
    for i
    by simp 
  moreover have \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup> \<in> dom (\<M> i)\<close>
    if
      \<open>i \<in> I\<close> and
      \<open>t \<in> set ts\<close>
    for i t
    using Fun[OF that(2)]
    by (meson PiE restrict_Pi_cancel that(1)) 
  then have \<open>\<forall> t \<in> set ts. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup> \<in> dom (\<M> i)\<close>
    if \<open>i \<in> I\<close>
    for i
    using that
    by blast
  then have \<open>interp_fn (\<M> i) f [\<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>. t \<leftarrow> ts] \<in> dom (\<M> i)\<close>
    if \<open>i \<in> I\<close>
    for i
    using struct.FN_dom_to_dom[OF struct_Mi[rule_format, OF that]] that 
    by simp 
  ultimately show ?case
    by force
qed

lemma eval_\<UU>_is_eq_class:
  assumes \<open>is_vars (dom \<A>) \<beta>\<close> 
  shows \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup> = (\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}\<close>
proof (induction t) 
  case (Var v)

  have \<open>\<lbrakk>Var v\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup> = \<beta> v\<close>
    by simp 
  moreover
  {
    have \<open>(\<lambda> i \<in> I. \<lbrakk>Var v\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>) = (\<lambda> i \<in> I. rep (\<beta> v) i)\<close>
      by auto 
    then have
      \<open>(\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>Var v\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>} = (\<sim>) `` {\<lambda> i \<in> I. rep (\<beta> v) i}\<close>
      by argo
    also have \<open>... = \<beta> v\<close>
    proof -
      have \<open>(\<lambda> i \<in> I. rep (\<beta> v) i, rep (\<beta> v)) \<in> (\<sim>)\<close>
        by (smt (verit, ccfv_SIG) Collect_cong assms case_prodD case_prodI dom_\<A> is_vars_def
            mem_Collect_eq refl_onD refl_prod_eq rep_of_elem_ultraproduct_in_pi restrict_Pi_cancel
            restrict_apply') 
      then have \<open>(\<sim>) `` {\<lambda> i \<in> I. rep (\<beta> v) i} = (\<sim>) `` {rep (\<beta> v)}\<close>
        by (metis (no_types, lifting) equiv_class_eq_iff equiv_prod_eq) 
      also have \<open>... = \<beta> v\<close>
        by (smt (verit, best) assms dom_\<A> elem_eq_class_in_pi equiv_class_eq_iff equiv_prod_eq
            is_vars_def quotientE rep_relates_to_elem_of_equiv_class) 
      finally show ?thesis .
    qed
    finally have \<open>(\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>Var v\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>} = \<beta> v\<close> . 
  }
  ultimately show ?case .. 
next
  case (Fun f ts)
 
  have \<open>\<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup> = FN f [\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup>. t \<leftarrow> ts]\<close>
    using interp_fn_\<A> 
    by simp
  also have \<open>... = (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [rep e i. e \<leftarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup>. t \<leftarrow> ts]]}\<close>
    unfolding FN_def
    by blast 
  also have \<open>... = (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [rep (\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup>) i. t \<leftarrow> ts]}\<close>
    unfolding map_map_is_map ..
  also have \<open>... = (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f
    [rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}) i. t \<leftarrow> ts]}\<close>
    using Fun.IH
    by (smt (verit, ccfv_SIG) map_eq_conv restrict_ext) 
  also have
    \<open>... = (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [(\<lambda> i \<in> I. ⟦t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>) i. t \<leftarrow> ts]}\<close>
  proof -
    let ?as = \<open>[rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}). t \<leftarrow> ts]\<close>
    let ?bs = \<open>[(\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>). t \<leftarrow> ts]\<close>

    have len_eq: \<open>length ?as = length ?bs\<close>
      by auto 
    then have \<open>list_all2 (in_rel (\<sim>)) ?as ?bs\<close>
    proof (induction ts) 
      case (Cons t ts)

      have \<open>(rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}),
        (\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>)) \<in> (\<sim>)\<close>
        using lam_i_eval_in_Pi[OF assms, of t] rep_relates_to_elem_of_equiv_class
        by presburger 
      moreover have \<open>list_all2 (in_rel (\<sim>))
        [rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}). t \<leftarrow> ts]
        [(\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>). t \<leftarrow> ts]\<close>
        using Cons
        by fastforce 
      ultimately show ?case
        by (smt (z3) in_rel_def list.simps(9) list_all2_Cons1 restrict_ext) 
    qed auto 
    then have
      \<open>(\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [e\<^sub>i i. e\<^sub>i \<leftarrow> ?as]} =
        (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [e\<^sub>i i. e\<^sub>i \<leftarrow> ?bs]}\<close>
      using well_definedness_FN[OF len_eq]
      by meson 
    then show ?thesis
      unfolding map_map_is_map2 .
  qed
  also have \<open>... = (\<sim>) `` {\<lambda> i \<in> I. interp_fn (\<M> i) f [\<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>. t \<leftarrow> ts]}\<close>
    by force 
  also have \<open>... = (\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>Fun f ts\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}\<close>
    by auto 
  finally show ?case . 
qed

lemma some_i_in_Mi: 
  assumes
    \<open>a \<in> A\<close> and
    \<open>i \<in> I\<close>
  shows \<open>(\<some> y. y \<in> a) i \<in> dom (\<M> i)\<close>
  using assms(1) assms(2) equiv_Eps_preserves equiv_prod_eq
  by fastforce

lemma in_filter_ex_if_ex_in_filter:
  shows 
    \<open>(\<exists> a \<in> dom \<A>. {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep a i) \<Turnstile> \<phi>} \<in> F) \<Longrightarrow>
      {i \<in> I. \<exists> a \<in> dom (\<M> i). \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := a) \<Turnstile> \<phi>} \<in> F\<close>
    (is \<open>?lhs \<Longrightarrow> ?rhs\<close>)
proof -
  assume ?lhs
  then obtain a where
    a_in_A: \<open>a \<in> dom \<A>\<close> and
    \<open>{i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep a i) \<Turnstile> \<phi>} \<in> F\<close>
    by blast
  then have \<open>{i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := (\<some> y. y \<in> a) i) \<Turnstile> \<phi>} \<in> F\<close>
    unfolding rep_def
    by blast
  moreover have \<open>\<M> i,(\<lambda> v. rep (\<beta> v) i)(x := (\<some> y. y \<in> a) i) \<Turnstile> \<phi>\<close> 
    if
      \<open>\<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep a i) \<Turnstile> \<phi>\<close> and
      \<open>i \<in> I\<close>
    for i
    using rep_def that(1)
    by force
  then have \<open>{i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep a i) \<Turnstile> \<phi>} \<subseteq>
    {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := (\<some> y. y \<in> a) i) \<Turnstile> \<phi>}\<close>
    using Collect_mono_iff
    by blast 
  moreover have \<open>a \<in> A\<close>
    using a_in_A
    by (subst (asm) dom_\<A>) 
  ultimately show ?rhs
    using filter.upwards_closed[OF F_filter, of \<open>{i \<in> I. \<M> i,(\<lambda>v. rep (\<beta> v) i)
      (x := (SOME y. y \<in> a) i) \<Turnstile> \<phi>}\<close>]
    by (smt (verit, best) Eps_cong Pi_iff mem_Collect_eq rep_def rep_of_elem_ultraproduct_in_pi
        subsetI) 
qed 

lemma inline_restrict_in_set_compr:
  \<open>{i \<in> I. P [(\<lambda> i \<in> I. f g i) i. g \<leftarrow> L]} = {i \<in> I. P [f g i. g \<leftarrow> L]}\<close>
  by force 

abbreviation (input) I_fm :: \<open>('f, 'p, 'v) fm \<Rightarrow> ('v \<Rightarrow> ('i \<Rightarrow> 'm) set) \<Rightarrow> 'i set\<close> (\<open>I\<^bsub>_\<^esub>\<^bsup>_\<^esup>\<close>) where
  \<open>I\<^bsub>\<chi>\<^esub>\<^bsup>\<beta>\<^esup> \<equiv> {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<chi>}\<close>

(* Theorem 3.1 *)
theorem los:
  assumes \<open>is_vars (dom \<A>) \<beta>\<close>
    \<comment>\<open>This assumption is crucial because we don't want to consider cases where \<open>\<beta>\<close> maps variables
      to equivalence classes on a relation other than @{const prod_eq}.
      Ideally, this would have been a restriction on the type of \<open>\<beta>\<close> but this doesn't seem to be
      possible in Isabelle.\<close>
  shows \<open>\<A>,\<beta> \<Turnstile> \<phi> \<longleftrightarrow> I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
  using assms
proof (induction \<phi> arbitrary: \<beta>) 
  case (Rel p e)

  have \<open>\<A>,\<beta> \<Turnstile> Rel p e \<longleftrightarrow> [\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup>. t \<leftarrow> e] \<in> REL p\<close> (is \<open>_ \<longleftrightarrow> ?e \<in> _\<close>)
    using interp_rel_\<A>
    by auto 
  also have
    \<open>... \<longleftrightarrow> (\<forall> x \<in> set ?e. x \<in> A) \<and> {i \<in> I. [rep e\<^sub>i i. e\<^sub>i \<leftarrow> ?e] \<in> interp_rel (\<M> i) p} \<in> F\<close>
    unfolding REL_def
    by blast 
  also have
    \<open>... \<longleftrightarrow> (\<forall> x \<in> set ?e. x \<in> A) \<and> {i \<in> I. [rep (\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup>) i. t \<leftarrow> e] \<in> interp_rel (\<M> i) p} \<in> F\<close>
    unfolding map_map_is_map
    by blast
  also have \<open>... \<longleftrightarrow> (\<forall> x \<in> set ?e. x \<in> A) \<and> {i \<in> I. 
    [rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}) i. t \<leftarrow> e] \<in> interp_rel (\<M> i) p} \<in> F\<close>
    using eval_\<UU>_is_eq_class[OF Rel.prems(1)]
    by simp 
  also have \<open>... \<longleftrightarrow> (\<forall> x \<in> set ?e. x \<in> A) \<and>
    {i \<in> I. [\<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>. t \<leftarrow> e] \<in> interp_rel (\<M> i) p} \<in> F\<close>
  proof -
    let ?as = \<open>[rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}). t \<leftarrow> e]\<close> 
    let ?bs = \<open>[(\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>). t \<leftarrow> e]\<close>

    have len_eq: \<open>length ?as = length ?bs\<close>
      by simp 
    then have \<open>list_all2 (in_rel (\<sim>)) ?as ?bs\<close>
    proof (induction e)
      case (Cons e es)

      have \<open>(rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>e\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}),
        \<lambda> i \<in> I. \<lbrakk>e\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>) \<in> (\<sim>)\<close>
        using lam_i_eval_in_Pi[OF Rel.prems(1), of e] rep_relates_to_elem_of_equiv_class
        by presburger 
      moreover have \<open>list_all2 (in_rel (\<sim>))
        [rep ((\<sim>) `` {\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>}). t \<leftarrow> es]
        [(\<lambda> i \<in> I. \<lbrakk>t\<rbrakk>\<^bsup>\<M> i,\<lambda> v. rep (\<beta> v) i\<^esup>). t \<leftarrow> es]\<close>
        using Cons
        by fastforce 
      ultimately show ?case
        by (smt (verit, ccfv_SIG) in_rel_def list.simps(9) list_all2_Cons1 restrict_ext) 
    qed auto 
    then have
      \<open>{i \<in> I. [e\<^sub>i i. e\<^sub>i \<leftarrow> ?as] \<in> interp_rel (\<M> i) p} \<in> F \<longleftrightarrow>
       {i \<in> I. [e\<^sub>i i. e\<^sub>i \<leftarrow> ?bs] \<in> interp_rel (\<M> i) p} \<in> F\<close>
      using well_definedness_REL[OF len_eq]
      by blast 
    then show ?thesis
      unfolding map_map_is_map2
      by (intro iffI conjI; blast?)
         (smt (verit, ccfv_threshold) Collect_cong map_eq_conv restrict_apply)+
  qed
  also have \<open>... \<longleftrightarrow> I\<^bsub>Rel p e\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
  proof -
    have \<open>\<lbrakk>t\<rbrakk>\<^bsup>\<A>,\<beta>\<^esup> \<in> dom \<A>\<close>
      if \<open>t \<in> set e\<close> 
      for t 
      using lam_i_eval_in_Pi[OF Rel.prems] eval_\<UU>_is_eq_class[OF Rel.prems] dom_\<A> that
      by (smt (verit, ccfv_threshold) Pi_iff comp_apply quotientI) 
    then show ?thesis
      using quotientI dom_\<A> interp_rel_\<A>
      by auto
  qed
  finally show ?case .
next
  case (Negation \<phi>)

  have \<open>\<A>,\<beta> \<Turnstile> \<^bold>\<not> \<phi> \<longleftrightarrow> \<not> \<A>,\<beta> \<Turnstile> \<phi>\<close>
    by auto 
  also have \<open>... \<longleftrightarrow> I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<notin> F\<close>
    using Negation.IH[OF Negation.prems(1)]
    by blast
  also have \<open>... \<longleftrightarrow> I - I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    using ultrafilter.maximality[OF F_ultrafilter, of \<open>I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup>\<close>]
    by (metis (mono_tags, lifting) CollectD Diff_disjoint F_filter filter.closed_int
        filter.empty_not_in_F subsetI) 
  also have \<open>... \<longleftrightarrow> {i \<in> I. \<not> \<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<phi>} \<in> F\<close>
    by (smt (verit) Collect_cong Diff_iff mem_Collect_eq minus_set_def) 
  also have \<open>... \<longleftrightarrow> I\<^bsub>\<^bold>\<not> \<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    by auto 
  finally show ?case . 
next
  case (Conjunction \<phi> \<psi>)

  have \<open>\<A>,\<beta> \<Turnstile> \<phi> \<^bold>\<and> \<psi> \<longleftrightarrow> \<A>,\<beta> \<Turnstile> \<phi> \<and> \<A>,\<beta> \<Turnstile> \<psi>\<close>
    by auto 
  also have \<open>... \<longleftrightarrow> I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F \<and> I\<^bsub>\<psi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    using Conjunction.IH[OF Conjunction.prems(1)]
    by blast 
  also have \<open>... \<longleftrightarrow> I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<inter> I\<^bsub>\<psi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    using filter.closed_int[OF F_filter, of \<open>I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup>\<close> \<open>I\<^bsub>\<psi>\<^esub>\<^bsup>\<beta>\<^esup>\<close>]
          filter.closed_int'[OF F_filter, of \<open>I\<^bsub>\<phi>\<^esub>\<^bsup>\<beta>\<^esup>\<close> \<open>I\<^bsub>\<psi>\<^esub>\<^bsup>\<beta>\<^esup>\<close>] 
    by blast 
  also have \<open>... \<longleftrightarrow> I\<^bsub>\<phi> \<^bold>\<and> \<psi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    (* /!\ Very slow /!\ *)
    by auto (smt (verit, del_insts) Collect_cong Collect_conj_eq)+
  finally show ?case . 
next
  \<comment>\<open>See \<^url>\<open>http://www.maths.gla.ac.uk/~gbellamy/LMS/PrestNotes.pdf\<close> (p10) for the proof of this case.
    It is not exactly the same underneath, but close enough.\<close>

  case (Existential x \<phi>)

  show ?case
  proof (intro iffI)
    assume \<open>\<A>,\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>)\<close>
    then have *: \<open>\<exists> a \<in> dom \<A>. \<A>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
      by auto 
    then have \<open>\<exists> a \<in> dom \<A>. {i \<in> I. \<M> i,(\<lambda> v. rep ((\<beta>(x := a)) v) i) \<Turnstile> \<phi>} \<in> F\<close> 
    proof -
      obtain a where
        a_in_A: \<open>a \<in> dom \<A>\<close> and
        \<phi>_entailed: \<open>\<A>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
        using "*"
        by blast
      then have \<open>is_vars (dom \<A>) (\<beta>(x := a))\<close> 
        using Existential.prems
        by auto
      then show ?thesis
        using Existential.IH[of \<open>\<beta>(x := a)\<close>] \<phi>_entailed a_in_A 
        by blast 
    qed 
    then have \<open>\<exists> a \<in> dom \<A>. {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep a i) \<Turnstile> \<phi>} \<in> F\<close>
      by (simp add: fun_upd_rep_is_rep_fun_upd)
    then have \<open>{i \<in> I. \<exists> a \<in> dom (\<M> i). \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := a) \<Turnstile> \<phi>} \<in> F\<close> 
      using in_filter_ex_if_ex_in_filter
      by fastforce 
    then show \<open>I\<^bsub>\<^bold>\<exists> x\<^bold>. \<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
      by auto 
  next
    assume \<open>I\<^bsub>\<^bold>\<exists> x\<^bold>. \<phi>\<^esub>\<^bsup>\<beta>\<^esup> \<in> F\<close>
    then have ex_unfolded:
      \<open>{i \<in> I. \<exists> a \<in> dom (\<M> i). \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := a) \<Turnstile> \<phi>} \<in> F\<close>
      (is \<open>?K \<in> F\<close>) 
      by auto
    then have \<open>\<forall> i \<in> ?K. \<exists> a \<in> dom (\<M> i). \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := a) \<Turnstile> \<phi>\<close>
      by force
    then have
      \<open>\<exists> u. \<forall> i \<in> ?K. u i \<in> dom (\<M> i) \<and> (\<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>)\<close>
      by meson
    then obtain u_tmp where
      u_tmp_in_dom: \<open>u_tmp \<in> (\<Pi> i \<in> ?K. dom (\<M> i))\<close> and
      u_tmp_def: \<open>\<forall> i \<in> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u_tmp i) \<Turnstile> \<phi>\<close>
      by fastforce 
    then have
      \<open>\<exists> u. (\<forall> i \<in> I. u i \<in> dom (\<M> i)) \<and> (\<forall> i \<in> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>)\<close>
    proof -
      have \<open>\<forall> i \<in> ?K. u_tmp i \<in> dom (\<M> i)\<close>
        using u_tmp_in_dom
        by auto
      moreover have \<open>\<forall> i \<in> I. dom (\<M> i) \<noteq> {}\<close>
        using struct.M_nonempty struct_Mi
        by blast
      ultimately have \<open>\<exists> u. (\<forall> i \<in> ?K. u i = u_tmp i) \<and> (\<forall> i \<in> I - ?K. u i = (\<some> x. x \<in> dom (\<M> i)))\<close>
      proof -
        let ?u = \<open>\<lambda> i \<in> I. if i \<in> ?K then u_tmp i else (\<some> x. x \<in> dom (\<M> i))\<close>
        have \<open>\<forall> i \<in> ?K. ?u i = u_tmp i\<close>
          by auto 
        moreover have \<open>\<forall> i \<in> I - ?K. ?u i = (\<some> x. x \<in> dom (\<M> i))\<close>
          by auto 
        ultimately show ?thesis
          by blast 
      qed
      then obtain u where
        u_eq_u_tmp: \<open>\<forall> i \<in> ?K. u i = u_tmp i\<close> and
        u_arbitrary: \<open>\<forall> i \<in> I - ?K. u i = (\<some> x. x \<in> dom (\<M> i))\<close>
        by blast
          
      have \<open>\<forall> i \<in> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>\<close>
        using u_tmp_def u_eq_u_tmp 
        by auto
      moreover have \<open>I - ?K \<union> ?K = I\<close>
        by blast
      then have \<open>\<forall> i \<in> I. (i \<in> ?K \<longrightarrow> u i = u_tmp i) \<and> (i \<in> I - ?K \<longrightarrow> u i = (\<some> x. x \<in> dom (\<M> i)))\<close>
        using u_arbitrary u_eq_u_tmp 
        by blast
      then have \<open>\<forall> i \<in> I. (i \<in> ?K \<longrightarrow> u i = u_tmp i) \<and> (i \<in> I - ?K \<longrightarrow> u i \<in> dom (\<M> i))\<close>
        using some_i_in_Mi struct_Mi[rule_format, THEN struct.M_nonempty]
        by (simp add: some_in_eq) 
      then have \<open>\<forall> i \<in> I. u i \<in> dom (\<M> i)\<close>
        using u_tmp_in_dom[unfolded Pi_iff]
        by fastforce
      ultimately show ?thesis
        by blast
    qed
    then have
      \<open>\<exists> u \<in> (\<Pi> i \<in> I. dom (\<M> i)). (\<forall> i \<in> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>)\<close>
      by (auto intro: Pi_iff) 
    then obtain u where
      u_in_dom: \<open>u \<in> (\<Pi> i \<in> I. dom (\<M> i))\<close> and
      u_def: \<open>\<forall> i \<in> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>\<close>
      by blast 

    define c where
      \<open>c \<equiv> (\<sim>) `` {u}\<close>

    have \<open>{i \<in> I. rep c i = u i} \<in> F\<close>
      using rep_relates_to_elem_of_equiv_class[OF u_in_dom] c_def
      by fastforce
    then have
      \<open>\<exists> I' \<subseteq> I. I' \<in> F \<and> (\<forall> i \<in> I'. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep c i) \<Turnstile> \<phi> \<longleftrightarrow>
        \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>)\<close>
      by (smt (verit, best) F_filter filter.in_F_subset_S mem_Collect_eq)
    then obtain I' where
      \<open>I' \<subseteq> I\<close> and
      \<open>I' \<in> F\<close> and
      entails_equiv_in_I':
      \<open>\<forall> i \<in> I'. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep c i) \<Turnstile> \<phi> \<longleftrightarrow>
        \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := u i) \<Turnstile> \<phi>\<close>
      by blast
    then have I'_inter_K_in_F: \<open>I' \<inter> ?K \<in> F\<close>
      using filter.closed_int[OF F_filter _ ex_unfolded]
      by blast 
    then have \<open>\<forall> i \<in> I' \<inter> ?K. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep c i) \<Turnstile> \<phi>\<close>
      by (simp add: entails_equiv_in_I' u_def) 
    then have \<open>I' \<inter> ?K \<subseteq> {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep c i) \<Turnstile> \<phi>}\<close>
      by blast 
    then have \<open>{i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep c i) \<Turnstile> \<phi>} \<in> F\<close>
      using filter.upwards_closed[OF F_filter _ _ I'_inter_K_in_F] CollectD
      by force
    then have
      \<open>\<exists> u \<in> dom \<A>. {i \<in> I. \<M> i,(\<lambda> v. rep (\<beta> v) i)(x := rep u i) \<Turnstile> \<phi>} \<in> F\<close>
      unfolding c_def
      using dom_\<A> u_in_dom
      by (smt (verit, ccfv_SIG) Collect_cong Pi_iff comp_apply quotientI)
    then have *: \<open>\<exists> u \<in> dom \<A>. {i \<in> I. \<M> i,(\<lambda> v. rep ((\<beta>(x := u)) v) i) \<Turnstile> \<phi>} \<in> F\<close>
      by (simp add: fun_upd_rep_is_rep_fun_upd)  
    then have \<open>\<exists> a \<in> dom \<A>. \<A>,\<beta>(x := a) \<Turnstile> \<phi>\<close>
    proof -
      obtain u where
        u_in_A: \<open>u \<in> dom \<A>\<close> and
        set_in_F: \<open>{i \<in> I. \<M> i,(\<lambda> v. rep ((\<beta>(x := u)) v) i) \<Turnstile> \<phi>} \<in> F\<close>
        using "*"
        by blast
      then have \<open>is_vars (dom \<A>) (\<beta>(x := u))\<close>
        using Existential.prems
        by auto
      then have \<open>\<A>,\<beta>(x := u) \<Turnstile> \<phi>\<close> 
        using Existential.IH(1) set_in_F 
        by blast 
      then show ?thesis
        using u_in_A
        by blast 
    qed
    then show \<open>\<A>,\<beta> \<Turnstile> (\<^bold>\<exists> x\<^bold>. \<phi>)\<close> 
      by simp
  qed
next
  case Bot

  have \<open>\<not> (\<A>,\<beta> \<Turnstile> \<^bold>\<bottom>)\<close>
    by simp 
  moreover have \<open>I\<^bsub>\<^bold>\<bottom>\<^esub>\<^bsup>\<beta>\<^esup> = {}\<close>
    by simp 
  moreover have \<open>{} \<notin> F\<close>
    using filter.empty_not_in_F[OF F_filter] . 
  ultimately show ?case
    by auto 
qed

end (* locale ultraprod *)



section \<open>Compactness proof of full first-order logic\<close>

lemma sat_compactness1: \<open>satisfiable T \<Longrightarrow> \<forall> T' \<subseteq> T. finite T' \<longrightarrow> satisfiable T'\<close>
  using is_model_of_mono satI
  by blast

abbreviation (input) I_fm2 
  :: \<open>'i set \<Rightarrow> ('i \<Rightarrow> ('f, 'p, 'm) model) \<Rightarrow> ('i \<Rightarrow> 'v \<Rightarrow> 'm) \<Rightarrow> ('f, 'p, 'v) fm \<Rightarrow> 'i set\<close>
  (\<open>_\<^bsup>_,_\<^esup>\<^bsub>_\<^esub>\<close>) where
  \<open>I\<^bsup>\<M>,\<beta>\<^esup>\<^bsub>\<phi>\<^esub> \<equiv> {i \<in> I. \<M> i,\<beta> i \<Turnstile> \<phi>}\<close> 

text \<open>
  The name of this lemma comes from the drawing:
  \<^verbatim>\<open>A \<leftrightarrow> B\<newline>\<updown>  \<updown>\<newline>C \<leftrightarrow> D\<close>
\<close> 
lemma iff_square: \<open>A \<longleftrightarrow> B \<Longrightarrow> C \<longleftrightarrow> D \<Longrightarrow> B \<longleftrightarrow> D \<Longrightarrow> A \<longleftrightarrow> C\<close>
  by blast 

lemma sat_compactness2:
  \<open>\<forall> T' \<subseteq> T. finite T' \<longrightarrow> satisfiable T' \<Longrightarrow> satisfiable T\<close>
  for
    T :: \<open>('f, 'p, 'v) fm set\<close> 
proof (cases \<open>T = {}\<close>) 
  case True
  then show ?thesis
    by (meson emptyE is_model_of_def satI) 
next
  case False

  \<comment>\<open>This proof is mostly inspired by the one in
    \<^url>\<open>https://www.people.vcu.edu/~bmcody/Compactness-Notes.pdf\<close>, although slightly modified here
    and there.\<close>

  let ?I = \<open>{ T' :: ('f, 'p, 'v) fm set. finite T' \<and> T' \<subseteq> T }\<close>

  have dummy_I_nonempty: \<open>?I \<noteq> {}\<close>
    using False
    by blast 

  assume \<open>\<forall> T' \<subseteq> T. finite T' \<longrightarrow> satisfiable T'\<close>
  then have \<open>\<forall> T' \<in> ?I. satisfiable T'\<close>
    by blast 
  then obtain
    \<M> :: \<open>('f, 'p, 'v) fm set \<Rightarrow> ('f, 'p, ('f, 'v) tm) model\<close> where
    \<open>\<forall> i \<in> ?I. is_canonical (\<M> i) (language i) \<and> is_model_of (\<M> i) i\<close>
    by moura
  then have 
    all_\<M>_canonical: \<open>\<forall> i \<in> ?I. is_canonical (\<M> i) (language i)\<close> and
    i_modelled_by: \<open>\<forall> i \<in> ?I. is_model_of (\<M> i) i\<close>
    by blast+ 
  then have
    structs: \<open>\<forall> i \<in> ?I. struct (dom (\<M> i)) (interp_fn (\<M> i)) (interp_rel (\<M> i))\<close>
    using model_is_struct
    by blast

  have \<open>\<forall> f. \<forall> i\<^sub>1 \<in> ?I. \<forall> i\<^sub>2 \<in> ?I. interp_fn (\<M> i\<^sub>1) f = interp_fn (\<M> i\<^sub>2) f\<close>
    using all_\<M>_canonical[unfolded is_canonical_def]
    by auto 

  let ?\<beta> = \<open>\<lambda> i _. \<some> x. x \<in> dom (\<M> i)\<close>

  have vars: \<open>\<forall> i \<in> ?I. is_vars (dom (\<M> i)) (?\<beta> i)\<close>
    unfolding is_vars_def
    using some_in_eq struct.M_nonempty structs
    by fastforce

  define star where
    \<open>star \<equiv> \<lambda> i \<in> ?I. {j \<in> ?I. i \<subseteq> j}\<close>

  have star_nonempty: \<open>star i \<noteq> {}\<close>
    if \<open>i \<in> ?I\<close>
    for i
    unfolding star_def
    using that
    by auto

  have \<open>fip {star i | i. i \<in> ?I}\<close> (is \<open>fip ?J\<close>)
    unfolding fip_def 
  proof (intro allI impI) 
    fix H
    assume
      H_subset: \<open>H \<subseteq> ?J\<close> and
      H_finite: \<open>finite H\<close> 

    have inter_star_is_star_union: \<open>star i\<^sub>0 \<inter> star i\<^sub>1 = star (i\<^sub>0 \<union> i\<^sub>1)\<close>
      if
        \<open>i\<^sub>0 \<in> ?I\<close> and
        \<open>i\<^sub>1 \<in> ?I\<close>
      for i\<^sub>0 i\<^sub>1
    proof -
      have \<open>star i\<^sub>0 \<inter> star i\<^sub>1 = {j \<in> ?I. i\<^sub>0 \<subseteq> j} \<inter> {j \<in> ?I. i\<^sub>1 \<subseteq> j}\<close>
        unfolding star_def
        using that
        by auto 
      also have \<open>... = {j \<in> ?I. i\<^sub>0 \<subseteq> j \<and> i\<^sub>1 \<subseteq> j}\<close>
        by fast 
      also have \<open>... = {j \<in> ?I. i\<^sub>0 \<union> i\<^sub>1 \<subseteq> j}\<close>
        by auto 
      also have \<open>... = star (i\<^sub>0 \<union> i\<^sub>1)\<close>
        unfolding star_def
        using that
        by simp 
      finally show ?thesis .
    qed
    moreover have \<open>star (i\<^sub>0 \<union> i\<^sub>1) \<noteq> {}\<close>
      if
        \<open>i\<^sub>0 \<in> ?I\<close> and
        \<open>i\<^sub>1 \<in> ?I\<close>
      for i\<^sub>0 i\<^sub>1
      using star_nonempty that
      by auto
    ultimately have inter_star_nonempty: \<open>star i\<^sub>0 \<inter> star i\<^sub>1 \<noteq> {}\<close>
      if
        \<open>i\<^sub>0 \<in> ?I\<close> and
        \<open>i\<^sub>1 \<in> ?I\<close>
      for i\<^sub>0 i\<^sub>1
      using that
      by auto 

    have \<open>\<forall> i \<in> H. \<exists> x \<in> ?I. i = star x\<close>
      using H_subset
      by blast 
    then obtain f where
      all_in_H_is_star: \<open>\<forall> i \<in> H. f i \<in> ?I \<and> i = star (f i)\<close>
      by moura 

    have \<open>\<exists> i \<in> ?I. \<Inter> H = star i\<close>
      if \<open>H \<noteq> {}\<close>
      using H_subset all_in_H_is_star
    proof (induction rule: finite_ne_induct[OF H_finite that])
      case insert: (2 x F)
      then obtain i\<^sub>0 where
        i\<^sub>0_in_dummy_I: \<open>i\<^sub>0 \<in> ?I\<close> and
        \<open>\<Inter> F = star i\<^sub>0\<close>
        by auto 
      moreover obtain i\<^sub>1 where
        i\<^sub>1_in_dummy_I: \<open>i\<^sub>1 \<in> ?I\<close> and
        \<open>x = star i\<^sub>1\<close>
        using insert.prems(2)
        by auto
      ultimately have
        \<open>x \<inter> \<Inter> F = star (i\<^sub>1 \<union> i\<^sub>0)\<close>
        using inter_star_is_star_union
        by auto 
      moreover have \<open>i\<^sub>1 \<union> i\<^sub>0 \<in> ?I\<close>
        using i\<^sub>0_in_dummy_I i\<^sub>1_in_dummy_I
        by blast 
      ultimately show ?case
        by auto 
    qed auto 
    then show \<open>\<Inter> H \<noteq> {}\<close>
      by (cases \<open>H = {}\<close>; fastforce simp: star_nonempty)
  qed
  moreover have \<open>?J \<subseteq> Pow ?I\<close>
    unfolding star_def
    by auto 
  ultimately obtain F where
    \<open>filter F ?I\<close> and
    dummy_J_subset: \<open>?J \<subseteq> F\<close>
    using fip_to_filter[OF dummy_I_nonempty, of ?J]
    by blast 
  then obtain F' where
    F'_ultrafilter: \<open>ultrafilter F' ?I\<close> and
    F_subset: \<open>F \<subseteq> F'\<close>
    using filter_to_ultrafilter[of F ?I]
    by blast 

  interpret ultraprod ?I F' \<M> ?\<beta>
    unfolding ultraprod_def
    using F'_ultrafilter structs vars
    by blast 

  {
    fix \<phi> and \<beta> :: \<open>'v \<Rightarrow> _ set\<close> 
    assume
      \<open>\<phi> \<in> T\<close> and
      vars: \<open>is_vars (dom \<A>) \<beta>\<close> 
    then have
      singleton_\<phi>_in_dummy_I: \<open>{\<phi>} \<in> ?I\<close> and
      \<open>\<forall> i \<in> ?I. \<phi> \<in> i \<longrightarrow> \<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<phi>\<close>
    proof (blast, intro ballI impI)
      fix i
      assume
        i_in_dummy_I: \<open>i \<in> ?I\<close> and
        \<phi>_in_i: \<open>\<phi> \<in> i\<close> and
        \<phi>_in_T: \<open>\<phi> \<in> T\<close>

      have \<open>\<forall> \<beta>. is_vars (dom (\<M> i)) \<beta> \<longrightarrow> \<M> i,\<beta> \<Turnstile> \<phi>\<close>
        using \<phi>_in_i i_in_dummy_I i_modelled_by is_model_of_def
        by blast
      then show \<open>\<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<phi>\<close>
        using vars dom_\<A> i_in_dummy_I rep_def some_i_in_Mi
        by auto
    qed
    then have \<open>{i \<in> ?I. \<phi> \<in> i} \<subseteq> {i \<in> ?I. \<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<phi>}\<close>
      by blast 
    moreover have \<open>{i \<in> ?I. \<phi> \<in> i} \<in> ?J\<close>
    proof -
      have \<open>{i \<in> ?I. \<phi> \<in> i} = {i \<in> ?I. {\<phi>} \<subseteq> i}\<close>
        by simp
      moreover have \<open>{i \<in> ?I. {\<phi>} \<subseteq> i} = star {\<phi>}\<close>
        unfolding star_def
        using singleton_\<phi>_in_dummy_I
        by simp 
      then have \<open>{i \<in> ?I. {\<phi>} \<subseteq> i} \<in> ?J\<close>
        using singleton_\<phi>_in_dummy_I
        by blast 
      ultimately show ?thesis
        by argo
    qed
    then have \<open>{i \<in> ?I. \<phi> \<in> i} \<in> F'\<close>
      using F_subset dummy_J_subset
      by fastforce 
    ultimately have \<open>{i \<in> ?I. \<M> i,(\<lambda> v. rep (\<beta> v) i) \<Turnstile> \<phi>} \<in> F'\<close>
      using filter.upwards_closed[OF ultrafilter_is_filter[OF F'_ultrafilter]]
      by (metis (mono_tags, lifting) mem_Collect_eq subsetI) 
    then have \<open>\<A>,\<beta> \<Turnstile> \<phi>\<close>
      unfolding los[OF vars] .
  }
  then have \<open>is_model_of \<A> T\<close>
    unfolding is_model_of_def
    by blast
  then show ?thesis  
    using satI
    by blast 
qed

(* Theorem 1.6 and 3.2 *)
theorem sat_compactness: \<open>satisfiable T \<longleftrightarrow> (\<forall> T' \<subseteq> T. finite T' \<longrightarrow> satisfiable T')\<close>
  using sat_compactness1 sat_compactness2
  by blast 
   
end (* theory *) 