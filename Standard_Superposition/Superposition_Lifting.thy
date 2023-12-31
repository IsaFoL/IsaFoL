(*  Title:       Superposition_Lifting
    Author:      Simon Robillard <simon.robillard at chalmers.se>, 2018

NOTE: unmaintained since 2020 and I (Mathias Fleury) does not know how
to update it. I am not sure that it is even important
*)

theory Superposition_Lifting
imports
    Saturation_Framework.Calculus Saturation_Framework_Extensions.Soundness
    "HOL-Library.Multiset" "HOL-Library.Uprod"
    First_Order_Terms.Unification
begin

(* literals, clauses *)

datatype ('f, 'v) literal = Lit (polarity: bool) (eq: \<open>('f, 'v) term uprod\<close>)

lemma literal_exhaust_2 [case_names Pos Neg, cases type: literal]:
  \<open>(\<And>s t. L = Lit True (Upair s t) \<Longrightarrow> P) \<Longrightarrow> (\<And>s t. L = Lit False (Upair s t) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (metis(full_types) literal.exhaust uprod_exhaust)

lemma literal_exhaust_1 [case_names Lit]:
  obtains p s t where \<open>L = Lit p (Upair s t)\<close>
  by (metis(full_types) literal.exhaust uprod_exhaust)

type_synonym ('f, 'v) clause = \<open>('f, 'v) literal multiset\<close>

fun vars_lit :: \<open>('f, 'v) literal \<Rightarrow> 'v set\<close>
  where
    \<open>vars_lit (Lit p e) = (\<Union>t \<in> set_uprod e. vars_term t)\<close>

abbreviation ground_term :: \<open>('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>ground_term t \<equiv> vars_term t = {}\<close>

abbreviation ground_lit :: \<open>('f, 'v) literal \<Rightarrow> bool\<close>
  where \<open>ground_lit L \<equiv> vars_lit L = {}\<close>

abbreviation ground_cl :: \<open>('f, 'v) clause \<Rightarrow> bool\<close>
  where \<open>ground_cl C \<equiv> \<forall>L \<in># C. ground_lit L\<close>

typedef ('f, 'v) ground_clause = \<open>{C :: ('f, 'v) clause. ground_cl C}\<close>
  apply(rule_tac x = \<open>{#}\<close> in exI)
  by simp

lemma ground_lit_upair: \<open>ground_lit (Lit p (Upair s t)) \<Longrightarrow> ground_term s \<and> ground_term t\<close>
  by simp

lemma ground_subclause: \<open>Rep_ground_clause C = C' + C'' \<Longrightarrow> ground_cl C' \<and> ground_cl C''\<close>
  using Rep_ground_clause [of C] by auto

(* substitutions *)

fun subst_apply_lit :: \<open>('f, 'v) literal \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) literal\<close>
  where
   \<open>subst_apply_lit (Lit p e) \<sigma> = (Lit p (map_uprod (\<lambda>t. t \<cdot> \<sigma>) e))\<close>

fun subst_apply_cl :: \<open>('f, 'v) clause \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) clause\<close>
  where \<open>subst_apply_cl C \<sigma> = {# subst_apply_lit L \<sigma>. L \<in># C #}\<close>

lemma subst_upair: \<open>subst_apply_lit (Lit p (Upair s t)) \<sigma> = Lit p (Upair (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))\<close>
  by (simp add: map_uprod.abs_eq)

lemma subst_lit_comp: \<open>subst_apply_lit L (\<sigma> \<circ>\<^sub>s \<tau>) = subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>\<close>
proof (cases L; simp) qed

lemma subst_ground_term: \<open>ground_term t \<Longrightarrow> t \<cdot> \<sigma> = t\<close>
  by (metis empty_iff subst_ident term_subst_eq)

lemma subst_ground_uprod: \<open>(\<forall>t \<in> set_uprod e. ground_term t) \<Longrightarrow> map_uprod (\<lambda>t. t \<cdot> \<sigma>) e = e\<close>
  by (simp add: subst_ground_term uprod.map_cong0 uprod.map_ident)

lemma subst_ground_lit: \<open>ground_lit L \<Longrightarrow> subst_apply_lit L \<sigma> = L\<close>
  by (metis ground_lit_upair literal_exhaust_1 subst_ground_term subst_upair)

lemma subst_cl_comp: \<open>subst_apply_cl C (\<sigma> \<circ>\<^sub>s \<tau>) = subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>\<close>
proof -
  have \<open>subst_apply_cl C (\<sigma> \<circ>\<^sub>s \<tau>) = {# subst_apply_lit L (\<sigma> \<circ>\<^sub>s \<tau>). L \<in># C #}\<close> by auto
  also have \<open>... = {# subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>. L \<in># C #}\<close> using subst_lit_comp by metis
  also have \<open>... = {# subst_apply_lit L' \<tau>. L' \<in># {# subst_apply_lit L \<sigma>. L \<in># C #} #}\<close>
    by (smt empty_iff image_mset_cong image_mset_single insert_iff multiset.map_comp set_mset_add_mset_insert set_mset_empty)
  finally show ?thesis by auto
qed

lemma subst_ground_cl: \<open>ground_cl C \<Longrightarrow> subst_apply_cl C \<sigma> = C\<close>
  by (simp add: subst_ground_lit image_mset_cong)

lemma ex_grounding_subst:
  \<open>\<exists>\<sigma> :: ('f, 'v) subst. \<forall>t. ground_term (t \<cdot> \<sigma>)\<close>
proof -
  obtain f :: \<open>'f\<close> and t :: \<open>('f, 'v) term\<close> where \<open>t = Fun f []\<close> and \<open>ground_term t\<close> by auto
  have \<open>ground_term (s \<cdot> (\<lambda>x. t))\<close> for s :: \<open>('f, 'v) term\<close>
  proof (induct s; simp add: \<open>ground_term t\<close>) qed
  then show ?thesis by auto
qed

lemma ex_ground_instance: \<open>\<exists>\<sigma> :: ('f, 'v) subst. ground_cl (subst_apply_cl C \<sigma>)\<close>
proof -
  obtain \<sigma> :: \<open>('f, 'v) subst\<close> where ground_subst: \<open>ground_term (t \<cdot> \<sigma>)\<close> for t
    using ex_grounding_subst by auto
  have \<open>L \<in># subst_apply_cl C \<sigma> \<Longrightarrow> ground_lit L\<close> for L
  proof -
    assume \<open>L \<in># subst_apply_cl C \<sigma>\<close>
    then obtain L' where \<open>subst_apply_lit L' \<sigma> = L\<close> by auto
    then show \<open>ground_lit L\<close>
    proof (cases L' rule: literal_exhaust_1)
      case (Lit p s t)
      then show \<open>subst_apply_lit L' \<sigma> = L \<Longrightarrow> L' = Lit p (Upair s t) \<Longrightarrow> ground_lit L\<close>
        using ground_subst subst_upair [of p s t \<sigma>] by auto
    qed
  qed
  then show ?thesis by auto
qed

(* semantics *)

(* unfortunately, it is not possible to define a type for ordered TRS, as the definition would rely on fixed type arguments *)
type_synonym ('f, 'v) trs = \<open>(('f, 'v) term \<times> ('f, 'v) term) set\<close>

type_synonym ('f, 'v) interp = \<open>(('f, 'v) term \<times> ('f, 'v) term) set\<close>

definition fun_comp :: \<open>('f, 'v) interp \<Rightarrow> bool\<close>
  where \<open>fun_comp I = (\<forall>f a1 a2. length a1 = length a2 \<longrightarrow> (\<forall>n. n < length a1 \<longrightarrow> (nth a1 n, nth a2 n) \<in> I) \<longrightarrow> (Fun f a1, Fun f a2) \<in> I)\<close>

(*fun congruence :: \<open>('f, 'v) interp \<Rightarrow> bool\<close>
  where \<open>congruence I = (refl_on {t. ground_term t} I \<and> trans I \<and> sym I \<and> fun_comp I)\<close>*)

typedef ('f, 'v) fo_interp = \<open>{I :: ('f, 'v) interp. refl_on {t. ground_term t} I \<and> trans I \<and> sym I \<and> fun_comp I}\<close>
proof -
  let ?I = \<open>{(t,t) | t. ground_term t}\<close>
  have \<open>refl_on {t. ground_term t} ?I\<close> unfolding refl_on_def by auto
  moreover have \<open>trans ?I\<close> unfolding trans_def by auto
  moreover have \<open>sym ?I\<close> unfolding sym_def by auto
  moreover have \<open>fun_comp ?I\<close>
  proof -
    have \<open>length a1 = length a2 \<Longrightarrow> (\<forall>n<length a1. (a1 ! n, a2 ! n) \<in> ?I) \<Longrightarrow> (Fun f a1, Fun f a2) \<in> ?I\<close> for f and a1 a2 :: \<open>('a, 'b) term list\<close>
    proof -
      assume \<open>length a1 = length a2\<close> and subterms: \<open>\<forall>n<length a1. (a1 ! n, a2 ! n) \<in> ?I\<close>
      then have \<open>a1 = a2\<close>
        by (smt Pair_inject mem_Collect_eq nth_equalityI)
      moreover have \<open>ground_term (Fun f a1)\<close>
      proof -
        have \<open>vars_term (Fun f a1) = \<Union> (vars_term ` set a1)\<close> by auto
        moreover have \<open>t \<in> set a1 \<Longrightarrow> vars_term t = {}\<close> for t
          by (smt Pair_inject in_set_conv_nth mem_Collect_eq subterms)
        ultimately show ?thesis by auto
      qed
      ultimately show \<open>(Fun f a1, Fun f a2) \<in> ?I\<close> by simp
    qed
    then show ?thesis unfolding fun_comp_def by blast
  qed
  ultimately show ?thesis by auto
qed

lift_definition validate_eq :: \<open>('f, 'v) fo_interp \<Rightarrow> ('f, 'v) term uprod \<Rightarrow> bool\<close>
is \<open>\<lambda> I p. p \<in> Rep_fo_interp I\<close>
  using Rep_fo_interp unfolding eq_upair_def sym_def by auto

fun validate_ground_lit :: \<open>('f, 'v) fo_interp \<Rightarrow> ('f, 'v) literal \<Rightarrow> bool\<close>
  where
   \<open>validate_ground_lit I (Lit p e) = (if p then validate_eq I e else \<not> validate_eq I e)\<close>

definition validate_clause :: \<open>('f, 'v) fo_interp \<Rightarrow> ('f, 'v) clause \<Rightarrow> bool\<close>
  where \<open>validate_clause I C = (\<forall>\<sigma>. ground_cl (subst_apply_cl C \<sigma>) \<longrightarrow> (\<exists>L \<in># C. validate_ground_lit I (subst_apply_lit L \<sigma>)))\<close>

definition entail :: \<open>('f, 'v) clause set \<Rightarrow> ('f, 'v) clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>F" 50)
  where
\<open>N1 \<Turnstile>F N2 \<equiv> \<forall>I. (\<forall>C \<in> N1. validate_clause I C) \<longrightarrow> (\<forall>C \<in> N2. validate_clause I C)\<close>

definition ground_entail :: \<open>('f, 'v) ground_clause set \<Rightarrow> ('f, 'v) ground_clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50)
  where
\<open>N1 \<Turnstile>G N2 = (Rep_ground_clause ` N1 \<Turnstile>F Rep_ground_clause ` N2)\<close>

abbreviation empty_clause :: \<open>('f, 'v) clause\<close> ("\<bottom>F")
  where
  \<open>\<bottom>F \<equiv> {#}\<close>

abbreviation empty_ground_clause :: \<open>('f, 'v) ground_clause\<close> ("\<bottom>G")
  where
  \<open>\<bottom>G \<equiv> Abs_ground_clause {#}\<close>

lemma Rep_empty_ground_clause [simp]: \<open>Rep_ground_clause \<bottom>G = \<bottom>F\<close>
  using Abs_ground_clause_inverse [of \<open>\<bottom>F\<close>] by auto

lemma validate_instance:
  \<open>validate_clause I C \<Longrightarrow> validate_clause I (subst_apply_cl C \<sigma>)\<close>
proof -
  assume validate_C: \<open>validate_clause I C\<close>
  then have \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl C \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
  proof -
    assume \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>)\<close>
    then have \<open>ground_cl (subst_apply_cl C (\<sigma> \<circ>\<^sub>s \<tau>))\<close> using subst_cl_comp by metis
    then obtain L where L_elem: \<open>L \<in># C \<and> validate_ground_lit I (subst_apply_lit L (\<sigma> \<circ>\<^sub>s \<tau>))\<close>
      using validate_C unfolding validate_clause_def by blast
    then have \<open>subst_apply_lit L \<sigma> \<in># subst_apply_cl C \<sigma> \<and> validate_ground_lit I (subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>)\<close>
      using subst_lit_comp [of L \<sigma> \<tau>] by auto
    then show ?thesis by blast
  qed
  then show ?thesis unfolding validate_clause_def by blast
qed

interpretation fo_consequence: consequence_relation \<open>{\<bottom>F}\<close> \<open>(\<Turnstile>F)\<close>
proof
  show \<open>{\<bottom>F} \<noteq> {}\<close>
    by auto
  show \<open>B \<in> {\<bottom>F} \<Longrightarrow> {B} \<Turnstile>F N1\<close> for B :: \<open>('f, 'v) clause\<close> and N1
    unfolding entail_def validate_clause_def by auto
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N2 N1 :: \<open>('f, 'v) clause set\<close>
    unfolding entail_def by auto
  show \<open>\<forall>C \<in> N2. N1 \<Turnstile>F {C} \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N2 N1 :: \<open>('f, 'v) clause set\<close>
    unfolding entail_def by auto
  show \<open>N1 \<Turnstile>F N2 \<Longrightarrow> N2 \<Turnstile>F N3 \<Longrightarrow> N1 \<Turnstile>F N3\<close> for N1 N2 N3 :: \<open>('f, 'v) clause set\<close>
    unfolding entail_def validate_clause_def by fast
qed

interpretation ground_consequence: consequence_relation \<open>{\<bottom>G} :: ('f, 'v) ground_clause set\<close> \<open>(\<Turnstile>G)\<close>
proof
  show \<open>{\<bottom>G} \<noteq> {}\<close>
    by auto
  show \<open>B \<in> {\<bottom>G} \<Longrightarrow> {B} \<Turnstile>G N1\<close> for B :: \<open>('f, 'v) ground_clause\<close> and N1
    unfolding ground_entail_def entail_def validate_clause_def by auto
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>G N2\<close> for N2 N1 :: \<open>('f, 'v) ground_clause set\<close>
    unfolding ground_entail_def entail_def by auto
  show \<open>\<forall>C \<in> N2. N1 \<Turnstile>G {C} \<Longrightarrow> N1 \<Turnstile>G N2\<close> for N2 N1 :: \<open>('f, 'v) ground_clause set\<close>
    unfolding ground_entail_def entail_def by auto
  show \<open>N1 \<Turnstile>G N2 \<Longrightarrow> N2 \<Turnstile>G N3 \<Longrightarrow> N1 \<Turnstile>G N3\<close> for N1 N2 N3 :: \<open>('f, 'v) ground_clause set\<close>
    unfolding ground_entail_def entail_def validate_clause_def by presburger
qed

(* we require a total simplification ordering on ground terms, and an under-approximation of that
   order for non-ground clauses *)

locale superposition =
  fixes term_ord :: \<open>(('f,'v) term \<times> ('f,'v) term) set\<close>
    and selection :: \<open>('f, 'v) clause \<Rightarrow> ('f, 'v) literal multiset\<close>
  assumes term_ord_trans: \<open>trans term_ord\<close>
      and term_ord_antisym: \<open>(s,t) \<in> term_ord \<Longrightarrow> (t,s) \<in> term_ord \<Longrightarrow> s = t\<close>
      and term_ord_term_comp: \<open>(s, t) \<in> term_ord \<Longrightarrow> \<not> ((Fun f (a1 @ t # a2), Fun f (a1 @ s # a2)) \<in> term_ord \<or> Fun f (a1 @ t # a2) = Fun f (a1 @ s # a2))\<close>
      and term_ord_subterm_comp: \<open>s \<in> set argl \<Longrightarrow> \<not> ((Fun f argl, s) \<in> term_ord \<or> Fun f argl = s)\<close>
      and wf_term_ord: \<open>wf term_ord\<close>
      and term_ord_ground_total: \<open>total_on {t. ground_term t} term_ord\<close>
      and term_ord_stable_grounding: \<open>\<And> \<sigma> :: ('f,'v) subst. (s, t) \<in> term_ord \<Longrightarrow> ground_term (s \<cdot> \<sigma>) \<Longrightarrow> ground_term (t \<cdot> \<sigma>) \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> term_ord\<close>
      and selection_subset: \<open>selection C \<subseteq># C\<close>
      and selection_neg_lit: \<open>\<not> Lit True p \<in># selection C\<close>
      and selection_stable_renaming: \<open>is_renaming \<sigma> \<Longrightarrow> subst_apply_cl (selection C) \<sigma> = selection (subst_apply_cl C \<sigma>)\<close>
begin

(* extend order to literals and clauses *)
abbreviation term_lt :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> (infix "\<prec>" 60)
  where
  \<open>term_lt s t \<equiv> (s,t) \<in> term_ord\<close>

abbreviation term_le :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> (infix "\<preceq>" 60)
  where
  \<open>term_le s t \<equiv> (s,t) \<in> term_ord \<or> s = t\<close>

lift_definition mset_pair :: \<open>'a uprod \<Rightarrow> 'a multiset\<close>
is \<open>\<lambda> (x, y). {#x, y#}\<close>
  by auto

lemma mset_upair [simp]: \<open>mset_pair (Upair s t) = {#s, t#}\<close>
  by (simp add: Upair.abs_eq mset_pair.abs_eq)

lemma mset_pair_size: \<open>size (mset_pair (Upair s t)) = 2\<close>
  by auto

fun mset_lit :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) term multiset\<close>
  where
    \<open>mset_lit (Lit p e) = (if p then mset_pair e else mset_pair e + mset_pair e)\<close>

lemma mset_lit_inj: \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> L1 = L2\<close>
proof -
  have inj: \<open>mset_lit (Lit p1 (Upair s t)) = mset_lit (Lit p2 (Upair u v)) \<Longrightarrow> p1 = p2 \<and> (Upair s t) = (Upair u v)\<close> for p1 p2 s t u v
  proof -
    assume eq: \<open>mset_lit (Lit p1 (Upair s t)) = mset_lit (Lit p2 (Upair u v))\<close>
    have pol: \<open>p1 = p2\<close>
    proof (rule ccontr)
      assume \<open>p1 \<noteq> p2\<close>
      then have \<open>size (mset_lit (Lit p1 (Upair s t))) \<noteq> size (mset_lit (Lit p2 (Upair u v)))\<close> using mset_lit.simps mset_pair_size by auto
      then show False using eq by auto
    qed
    have \<open>(Upair s t) = (Upair u v)\<close>
    proof (cases p1)
      case True
      then have \<open>{#s,t#} = {#u,v#}\<close>
        using eq mset_lit.simps pol by auto
      then show ?thesis
        by (metis Upair_inject add_mset_eq_single add_mset_remove_trivial diff_union_swap)
    next
      case False
      then have \<open>{#s,s,t,t#} = {#u,u,v,v#}\<close>
        using eq mset_lit.simps pol
        by (metis add_mset_add_single add_mset_commute mset_upair union_mset_add_mset_right)
      then show ?thesis
        by (smt Upair_inject add_mset_eq_single add_mset_remove_trivial diff_union_swap)
    qed
    then show ?thesis using pol by auto
  qed
  show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> L1 = L2\<close>
  proof -
    assume \<open>mset_lit L1 = mset_lit L2\<close>
    then show \<open>L1 = L2\<close>
    proof (cases L1 rule: literal_exhaust_1)
      case (Lit p1 s t)
      then show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> L1 = Lit p1 (Upair s t) \<Longrightarrow> L1 = L2\<close>
      proof (cases L2 rule: literal_exhaust_1)
        case (Lit p2 u v)
        then show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> L1 = Lit p1 (Upair s t) \<Longrightarrow> L1 = Lit p1 (Upair s t) \<Longrightarrow> L2 = Lit p2 (Upair u v) \<Longrightarrow> L1 = L2\<close>
          using inj by auto
      qed
    qed
  qed
qed

lemma ground_mset_lit: \<open>ground_lit L \<Longrightarrow> t \<in># mset_lit L \<Longrightarrow> ground_term t\<close>
proof (cases L rule: literal_exhaust_1)
  case (Lit p u v)
  then show \<open>ground_lit L \<Longrightarrow> t \<in># mset_lit L \<Longrightarrow> L = Lit p (Upair u v) \<Longrightarrow> ground_term t\<close>
    by (metis equals0D ground_lit_upair insert_iff mset_lit.simps mset_upair set_mset_add_mset_insert set_mset_empty union_iff)
qed

definition lit_ord :: \<open>(('f,'v) literal \<times> ('f,'v) literal) set\<close>
  where
    \<open>lit_ord = inv_image (mult term_ord) mset_lit\<close>

abbreviation lit_lt :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) literal \<Rightarrow> bool\<close> (infix "\<prec>L" 60)
  where
  \<open>lit_lt L1 L2 \<equiv> (L1,L2) \<in> lit_ord\<close>

abbreviation lit_le :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) literal \<Rightarrow> bool\<close> (infix "\<preceq>L" 60)
  where
  \<open>lit_le L1 L2 \<equiv> (L1,L2) \<in> lit_ord \<or> L1 = L2\<close>

definition clause_ord :: \<open>(('f,'v) clause \<times> ('f,'v) clause) set\<close>
  where
    \<open>clause_ord = mult lit_ord\<close>

abbreviation clause_lt :: \<open>('f,'v) clause \<Rightarrow> ('f,'v) clause \<Rightarrow> bool\<close> (infix "\<prec>F" 60)
  where
  \<open>clause_lt C1 C2 \<equiv> (C1,C2) \<in> clause_ord\<close>

definition clause_set_ord :: \<open>(('f,'v) clause set \<times> ('f,'v) clause set) set\<close>
  where \<open>clause_set_ord = inv_image (mult clause_ord) mset_set\<close>

definition ground_clause_ord :: \<open>(('f,'v) ground_clause \<times> ('f,'v) ground_clause) set\<close>
  where
    \<open>ground_clause_ord = inv_image clause_ord Rep_ground_clause\<close>

abbreviation ground_clause_lt :: \<open>('f,'v) ground_clause \<Rightarrow> ('f,'v) ground_clause \<Rightarrow> bool\<close> (infix "\<prec>G" 60)
  where
  \<open>ground_clause_lt C1 C2 \<equiv> (C1,C2) \<in> ground_clause_ord\<close>

abbreviation ground_clause_le :: \<open>('f,'v) ground_clause \<Rightarrow> ('f,'v) ground_clause \<Rightarrow> bool\<close> (infix "\<preceq>G" 60)
  where
  \<open>ground_clause_le C1 C2 \<equiv> (C1,C2) \<in> ground_clause_ord \<or> C1 = C2\<close>

definition ground_clause_set_ord :: \<open>(('f,'v) ground_clause set \<times> ('f,'v) ground_clause set) set\<close>
  where \<open>ground_clause_set_ord = inv_image clause_set_ord (image Rep_ground_clause)\<close>

lemma term_ord_ground_term_comp: \<open>ground_term (Fun f (a1 @ s # a2)) \<Longrightarrow> ground_term (Fun f (a1 @ t # a2)) \<Longrightarrow> s \<prec> t \<Longrightarrow> Fun f (a1 @ s # a2) \<prec> Fun f (a1 @ t # a2)\<close>
  by (smt mem_Collect_eq superposition.term_ord_term_comp superposition_axioms term_ord_ground_total total_on_def)

lemma term_ord_ground_subterm_comp: \<open>ground_term (Fun f (a1 @ t # a2)) \<Longrightarrow> t \<prec> Fun f (a1 @ t # a2)\<close>
proof -
  assume ground_f: \<open>ground_term (Fun f (a1 @ t # a2))\<close>
  then have \<open>ground_term t \<and> \<not> Fun f (a1 @ t # a2) \<preceq> t\<close>
    using term_ord_subterm_comp by auto
  then show ?thesis using ground_f term_ord_ground_total unfolding total_on_def by blast
qed

lemma trans_lit_ord: \<open>trans lit_ord\<close>
  by (simp add: lit_ord_def mult_def trans_inv_image)

lemma trans_clause_ord: \<open>trans clause_ord\<close>
  by (simp add: clause_ord_def mult_def trans_inv_image)

lemma trans_ground_clause_ord: \<open>trans (ground_clause_ord)\<close>
  by (simp add: ground_clause_ord_def trans_clause_ord trans_inv_image)

lemma wf_lit_ord: \<open>wf lit_ord\<close>
  unfolding lit_ord_def
  using wf_term_ord wf_mult wf_inv_image by blast

lemma wf_clause_ord: \<open>wf clause_ord\<close>
  unfolding clause_ord_def
  using wf_lit_ord wf_mult wf_inv_image by blast

lemma wf_clause_set_ord: \<open>wf clause_set_ord\<close>
  unfolding clause_set_ord_def
  using wf_clause_ord wf_mult wf_inv_image by blast

lemma wf_ground_clause_ord: \<open>wf ground_clause_ord\<close>
  unfolding ground_clause_ord_def
  using wf_clause_ord wf_inv_image by blast

lemma wf_ground_clause_set_ord: \<open>wf ground_clause_set_ord\<close>
  unfolding ground_clause_set_ord_def
  using wf_clause_set_ord wf_inv_image by blast

lemma mult_max:
  assumes \<open>\<forall>x \<in># N. (x, y) \<in> ord\<close>
  assumes \<open>y \<in># M\<close>
  shows \<open>(N, M) \<in> mult ord\<close>
  by (metis (no_types, opaque_lifting) add.left_neutral assms empty_iff mult_def one_step_implies_mult set_mset_empty)

lemma max_in_mset: \<open>trans R \<Longrightarrow> total_on (set_mset M) R \<Longrightarrow> M \<noteq> {#} \<Longrightarrow> (\<exists>y \<in># M. \<forall>x \<in># M. x = y \<or> (x, y) \<in> R)\<close>
proof -
  assume tr: \<open>trans R\<close>
  show \<open>total_on (set_mset M) R \<Longrightarrow> M \<noteq> {#} \<Longrightarrow> (\<exists>y \<in># M. \<forall>x \<in># M. x = y \<or> (x, y) \<in> R)\<close>
  proof (induct M)
    case empty
    then show ?case by auto
  next
    case (add x M)
    then show ?case
    proof (cases \<open>M = {#}\<close>)
      case True
      then show ?thesis by auto
    next
      case False
      with add obtain y where y_elem: \<open>y \<in># M\<close> and y_max: \<open>\<forall>x \<in># M. x = y \<or> (x, y) \<in> R\<close>
        by (metis add_mset_remove_trivial in_diffD total_on_def)
      then consider \<open>(x, y) \<in> R \<or> x = y\<close> | \<open>(y, x) \<in> R\<close> using add unfolding total_on_def by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using y_elem y_max by auto
      next
        case 2
        then show ?thesis using tr y_max
          by (metis insertE set_mset_add_mset_insert transD union_single_eq_member)
      qed
    qed
  qed
qed

lemma mult_total: \<open>irrefl R \<Longrightarrow> trans R \<Longrightarrow> total_on S R \<Longrightarrow> total_on {x. set_mset x \<subseteq> S} (mult R)\<close>
proof -
  assume ir: \<open>irrefl R\<close> and tr: \<open>trans R\<close> and total: \<open>total_on S R\<close>
  have constr: \<open>set_mset M \<subseteq> S \<Longrightarrow> set_mset N \<subseteq> S \<Longrightarrow> M = N \<or> (M,N) \<in> mult R \<or> (N,M) \<in> mult R\<close> for M N
  proof (induct \<open>size (M + N)\<close> arbitrary: M N rule: less_induct)
    case (less M N)
    consider (no_inter) \<open>M \<inter># N = {#}\<close> | (inter) \<open>size ((M - N) + (N - M)) < size (M + N)\<close>
      by (metis add_strict_mono diff_less multiset_inter_commute nonempty_has_size size_Diff_subset_Int size_union subset_mset.inf_bot_right)
    then show ?case
    proof cases
      case no_inter
      consider (empty) \<open>M = {#} \<or> N = {#}\<close> | (no_empty) \<open>M \<noteq> {#} \<and> N \<noteq> {#}\<close> by auto
      then show ?thesis
      proof cases
        case empty
        then show ?thesis
          by (metis add_cancel_left_left empty_iff one_step_implies_mult set_mset_empty)
      next
        case no_empty
        have \<open>total_on (set_mset M) R\<close>
          by (meson subsetD total_on_def total less)
        then obtain m where m_elem: \<open>m \<in># M\<close> and m_max: \<open>\<forall>x \<in># M. x = m \<or> (x, m) \<in> R\<close>
          using max_in_mset [of R M] tr no_empty by blast
        have \<open>total_on (set_mset N) R\<close>
          by (meson subsetD total_on_def total less)
        then obtain n where n_elem: \<open>n \<in># N\<close> and n_max: \<open>\<forall>x \<in># N. x = n \<or> (x, n) \<in> R\<close>
          using max_in_mset [of R N] tr no_empty by blast
        consider (lt) \<open>(m,n) \<in> R\<close> | (gt) \<open>(n,m) \<in> R\<close> | (eq) \<open>m = n\<close>
          by (meson total less m_elem n_elem subsetD total_on_def)
        then show ?thesis
        proof cases
          case lt
          then show ?thesis
            using one_step_implies_mult [of N M R \<open>{#}\<close>] m_max n_max n_elem
            by (metis add.left_neutral no_empty transD tr)
        next
          case gt
          then show ?thesis
            using one_step_implies_mult [of M N R \<open>{#}\<close>] m_max n_max m_elem
            by (metis add.left_neutral no_empty transD tr)
        next
          case eq
          then show ?thesis using no_inter m_elem n_elem
            by (meson disjunct_not_in)
        qed
      qed
    next
      case inter
      with less consider \<open>(M - N, N - M) \<in> mult R \<or> (N - M, M - N) \<in> mult R\<close> | \<open>M - N = N - M\<close>
        by (meson in_diffD subsetD subsetI)
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using ir
          using mult_cancel_max[OF tr] by (metis irreflD irrefl_on_def)
      next
        case 2
        then show ?thesis
          by (metis Diff_eq_empty_iff_mset add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_intersect_right_idem inter_mset_def multiset_inter_commute subset_mset.add_diff_assoc)
      qed
    qed
  qed
  then show \<open>total_on {x. set_mset x \<subseteq> S} (mult R)\<close>
    unfolding total_on_def by blast
qed

lemma lit_ord_ground_total: \<open>total_on {L. ground_lit L} lit_ord\<close>
proof -
  have gr: \<open>ground_lit L \<Longrightarrow> set_mset (mset_lit L) \<subseteq> {t. ground_term t}\<close> for L
    using ground_mset_lit by auto
  have \<open>total_on {x. set_mset x \<subseteq> {t. ground_term t}} (mult term_ord)\<close>
    using mult_total [of term_ord \<open>{t. ground_term t}\<close>] term_ord_ground_total term_ord_trans wf_term_ord
    by (simp add: irreflI)
  then have \<open>ground_lit L1 \<Longrightarrow> ground_lit L2 \<Longrightarrow> (mset_lit L1, mset_lit L2) \<in> mult term_ord \<or> (mset_lit L2, mset_lit L1) \<in> mult term_ord \<or> L1 = L2\<close> for L1 L2
    using gr mset_lit_inj unfolding total_on_def by blast
  then show ?thesis unfolding lit_ord_def inv_image_def total_on_def by auto
qed

lemma clause_ord_distinct: \<open>C1 \<prec>F C2 \<Longrightarrow> C1 \<noteq> C2\<close>
  using clause_ord_def wf_clause_ord by auto

lemma clause_ord_asymmetric: \<open>C1 \<prec>F C2 \<Longrightarrow> \<not> C2 \<prec>F C1\<close>
  unfolding clause_ord_def
  using clause_ord_def wf_clause_ord wf_not_sym by fastforce

definition ground_term_ord :: \<open>(('f, 'v) term \<times> ('f, 'v) term) set\<close>
  where \<open>ground_term_ord = {(s,t). ground_term s \<and> ground_term t \<and> s \<prec> t}\<close>

lemma ground_clause_ord_total: \<open>total ground_clause_ord\<close>
proof -
  have \<open>set_mset (Rep_ground_clause C) \<subseteq> {L. ground_lit L}\<close> for C :: \<open>('f,'v) ground_clause\<close>
    using Rep_ground_clause by fast
  moreover have \<open>total_on {x. set_mset x \<subseteq> {L. ground_lit L}} (mult lit_ord)\<close>
    using Rep_ground_clause mult_total [of lit_ord \<open>{L. ground_lit L}\<close>]
          trans_lit_ord lit_ord_ground_total wf_lit_ord
    by (simp add: irreflI)
  ultimately show ?thesis
    unfolding ground_clause_ord_def inv_image_def clause_ord_def total_on_def
    by (simp add: Rep_ground_clause_inject)
qed

lemma ground_clause_ord_distinct: \<open>C1 \<prec>G C2 \<Longrightarrow> C1 \<noteq> C2\<close>
  unfolding ground_clause_ord_def inv_image_def
  using clause_ord_distinct by fastforce

lemma ground_clause_ord_asymmetric: \<open>C1 \<prec>G C2 \<Longrightarrow> \<not> C2 \<prec>G C1\<close>
  unfolding ground_clause_ord_def
  using ground_clause_ord_def wf_ground_clause_ord wf_not_sym by fastforce

(* inferences *)

definition eresolution_inferences :: \<open>('f, 'v) clause inference set\<close> where
\<open>eresolution_inferences = {Infer [{# L #} + C] (subst_apply_cl C \<sigma>)
                          | L s s' C \<sigma>. is_mgu \<sigma> {(s, s')}
                                      \<and> L = Lit False (Upair s s')
                                      \<and> (selection ({# L #} + C) = {#} \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit L \<sigma>)
                                        \<or> L \<in># selection ({# L #} + C))}\<close>

definition efactoring_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>efactoring_inferences = {Infer [{# L #} + {# L' #} + C] (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>)
                         | L L' s t C \<sigma>. \<exists>u u'. is_mgu \<sigma> {(u,u')}
                                       \<and> L = Lit True (Upair u s)
                                       \<and> L' = Lit True (Upair u' t)
                                       \<and> \<not> u \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                       \<and> selection ({# L #} + {# L' #} + C) = {#}
                                       \<and> (\<forall>M \<in># {# L' #} +  C. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit L \<sigma>)}\<close>

(* subterm s t u v \<equiv> t can be obtained from s by replacing one occurrence of u by v*)
inductive subterm_replace :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> where
  base: \<open>subterm_replace s t s t\<close> |
  step: \<open>subterm_replace s t u v \<Longrightarrow> subterm_replace (Fun f (a1 @ s # a2)) (Fun f (a1 @ t # a2)) u v\<close>

(* TODO renamings *)
definition pos_superposition_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>pos_superposition_inferences = {Infer [{# L #} + C , {# L' #} + D] (subst_apply_cl ({# Lit True (Upair vs u) #} + C + D) \<sigma>)
                                | L L' u vs C D \<sigma>. \<exists>s t t' vt. is_mgu \<sigma> {(t, t')}
                                                               \<and> L = Lit True (Upair s t)
                                                               \<and> L' = Lit True (Upair vt u)
                                                               \<and> subterm_replace vs vt s t'
                                                               \<and> is_Fun t'
                                                               \<and> \<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                                               \<and> \<not> vt \<cdot> \<sigma> \<preceq> u \<cdot> \<sigma>
                                                               \<and> subst_apply_lit L \<sigma> \<prec>L subst_apply_lit L' \<sigma>
                                                               \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit L \<sigma>)
                                                               \<and> (\<forall>M \<in># D. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit L' \<sigma>)
                                                               \<and> selection ({# L #} + C) = {#}
                                                               \<and> selection ({# L' #} + D) = {#}}\<close>

definition neg_superposition_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>neg_superposition_inferences = {Infer [{# L #} + C , {# L' #} + D] (subst_apply_cl ({# Lit False (Upair vs u) #} + C + D) \<sigma>)
                                | L L' u vs C D \<sigma>. \<exists>s t t' vt. is_mgu \<sigma> {(t, t')}
                                                 \<and> L = Lit True (Upair s t)
                                                 \<and> L' = Lit False (Upair vt u)
                                                 \<and> subterm_replace vs vt s t'
                                                 \<and> is_Fun t'
                                                 \<and> \<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                                 \<and> \<not> vt \<cdot> \<sigma> \<preceq> u \<cdot> \<sigma>
                                                 \<and> subst_apply_lit L \<sigma> \<prec>L subst_apply_lit L' \<sigma>
                                                 \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit L \<sigma>)
                                                 \<and> ((L' \<in># selection ({# L' #} + D)) \<or> (selection ({# L' #} + D) = {#} \<and> (\<forall>M \<in># D. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit L' \<sigma>)))
                                                 \<and> selection ({# L #} + C) = {#}}\<close>

abbreviation superposition_inference_system :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>superposition_inference_system \<equiv> eresolution_inferences
                                \<union> efactoring_inferences
                                \<union> pos_superposition_inferences
                                \<union> neg_superposition_inferences\<close>

fun Rep_ground_inference :: \<open>('f, 'v) ground_clause inference \<Rightarrow> ('f, 'v) clause inference\<close>
  where
    \<open>Rep_ground_inference \<iota> = Infer (map Rep_ground_clause (prems_of \<iota>)) (Rep_ground_clause (concl_of \<iota>))\<close>

definition ground_superposition_inference_system :: \<open>('f, 'v) ground_clause inference set\<close>
  where
  \<open>ground_superposition_inference_system = {\<iota>. Rep_ground_inference \<iota> \<in> superposition_inference_system}\<close>

(* helper lemmas for soundness of superposition rule *)
lemma subterm_replace_interp:
  assumes \<open>subterm_replace s t u v\<close>
      and \<open>validate_eq I (Upair u v)\<close>
      and \<open>ground_term s\<close>
      and \<open>ground_term t\<close>
    shows \<open>validate_eq I (Upair s t)\<close>
proof -
  have \<open>subterm_replace s t u v \<Longrightarrow> ground_term s \<Longrightarrow> ground_term t \<Longrightarrow> (s, t) \<in> Rep_fo_interp I\<close>
  proof (induction s arbitrary: t)
    case (Var x) then show ?case by auto (* vacuous case *)
  next
    case (Fun f args)
    then have \<open>subterm_replace (Fun f args) t u v\<close> by auto
    then show \<open>(Fun f args, t) \<in> Rep_fo_interp I\<close>
    proof cases
      case base
      then have \<open>(u, v) = (Fun f args, t)\<close> by auto
      with assms(2) show ?thesis
        by (simp add: Upair.abs_eq validate_eq.abs_eq)
    next
      case (step s' t' a1 a2)
      from Fun step have \<open>(s', t') \<in> Rep_fo_interp I\<close> by auto (* apply induction hypothesis *)
      have \<open>n < length (a1 @ s' # a2) \<Longrightarrow> ground_term ((a1 @ s' # a2) ! n)\<close> for n
        by (metis Fun(3) emptyE equals0I local.step(1) nth_mem term.set_intros(4))
      moreover have \<open>n < length (a1 @ t' # a2) \<Longrightarrow> ground_term ((a1 @ t' # a2) ! n)\<close> for n
        by (metis Fun(4) emptyE equals0I local.step(2) nth_mem term.set_intros(4))
      moreover have \<open>refl_on {t. ground_term t} (Rep_fo_interp I)\<close> using Rep_fo_interp by auto
      ultimately have \<open>n < length (a1 @ s' # a2) \<Longrightarrow> ((a1 @ s' # a2) ! n, (a1 @ t' # a2) ! n) \<in> Rep_fo_interp I\<close> for n
        using \<open>(s', t') \<in> Rep_fo_interp I\<close> unfolding refl_on_def
        by (smt mem_Collect_eq nth_Cons' nth_append)
      then have \<open>(Fun f (a1 @ s' # a2), Fun f (a1 @ t' # a2)) \<in> Rep_fo_interp I\<close>
        using Rep_fo_interp [of I] unfolding fun_comp_def by fastforce
      then show ?thesis using step by auto
    qed
  qed
  then show ?thesis using assms
    by (simp add: Upair.abs_eq validate_eq.abs_eq)
qed

lemma subterm_replace_stable_subst:
  \<open>subterm_replace s t u v \<Longrightarrow> subterm_replace (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) (u \<cdot> \<sigma>) (v \<cdot> \<sigma>)\<close>
proof (induction s arbitrary: t)
  case (Var x)
  then show ?case
  proof cases
    case base
    then show ?thesis using subterm_replace.base by blast
  qed
next
  case (Fun x1a x2)
  then have \<open>subterm_replace (Fun x1a x2) t u v\<close> by auto
  then show ?case
  proof cases
    case base
    then show ?thesis using subterm_replace.base by blast
  next
    case (step s' t' a1 a2)
    with Fun subterm_replace.step show ?thesis by fastforce
  qed
qed

lemma soundness: \<open>\<iota> \<in> superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close>
proof -
  assume \<open>\<iota> \<in> superposition_inference_system\<close>
  then consider (res) \<open>\<iota> \<in> eresolution_inferences\<close>
    | (fact) \<open>\<iota> \<in> efactoring_inferences\<close>
    | (sup) \<open>\<iota> \<in> pos_superposition_inferences \<or> \<iota> \<in> neg_superposition_inferences\<close>
    by auto
  then show \<open>set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close>
  proof cases
    case res (* soundness of equality resolution *)
    then obtain s s' C \<sigma> L
      where \<iota>_def: \<open>\<iota> = Infer [{# L #} + C] (subst_apply_cl C \<sigma>)\<close>
        and L_def: \<open>L = Lit False (Upair s s')\<close>
        and mgu: \<open>is_mgu \<sigma> {(s, s')}\<close>
      unfolding eresolution_inferences_def by auto
    have \<open>validate_clause I ({# L #} + C) \<Longrightarrow> validate_clause I (subst_apply_cl C \<sigma>)\<close> for I
    proof -
      assume \<open>validate_clause I ({# L #} + C)\<close>
      then have validate_prem_\<sigma>: \<open>validate_clause I (subst_apply_cl({# L #} + C) \<sigma>)\<close> using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl C \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume ground_C: \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>)\<close>
        (* the grounding of the conclusion is not necessarily a grounding of the premise, so we must extend it *)
        obtain \<upsilon> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (subst_apply_cl (subst_apply_cl ({# L #} + C) \<sigma>) \<tau>) \<upsilon>)\<close>
          using ex_ground_instance by fast
        then have grounding: \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# L #} + C) \<sigma>) (\<tau> \<circ>\<^sub>s \<upsilon>))\<close> using subst_cl_comp by metis
        then obtain L' where \<open>L' \<in># subst_apply_cl ({# L #} + C) \<sigma>\<close> and validate_L: \<open>validate_ground_lit I (subst_apply_lit L' (\<tau> \<circ>\<^sub>s \<upsilon>))\<close>
          using validate_prem_\<sigma> unfolding validate_clause_def by blast
        then consider (a) \<open>L' = subst_apply_lit L \<sigma>\<close> | (b) \<open>L' \<in># subst_apply_cl C \<sigma>\<close> by auto
        then show \<open>\<exists>L \<in># subst_apply_cl C \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
        proof cases
          case a
          then have \<open>subst_apply_lit L' (\<tau> \<circ>\<^sub>s \<upsilon>) = Lit False (Upair (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s' \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close>
            using L_def by simp
          with validate_L have \<open>validate_ground_lit I (Lit False (Upair (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s' \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>)))\<close> by auto
          then have \<open>\<not> validate_eq I (Upair (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s' \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> by simp
          with mgu have \<open>\<not> validate_eq I (Upair (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> unfolding is_mgu_def unifiers_def by simp
          moreover have \<open>ground_term (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>)\<close> using grounding L_def by auto
          ultimately show ?thesis
            using Rep_fo_interp [of I]
            unfolding refl_on_def
            by (simp add: Upair.abs_eq validate_eq.abs_eq) (* contradiction *)
        next
          case b
          with ground_C have \<open>ground_lit (subst_apply_lit L' \<tau>)\<close> by auto
          with validate_L have \<open>validate_ground_lit I (subst_apply_lit L' \<tau>)\<close>
            using subst_ground_lit [of \<open>subst_apply_lit L' \<tau>\<close> \<upsilon>] subst_lit_comp by metis
          with b show ?thesis by auto
        qed
      qed
      then show ?thesis unfolding validate_clause_def by auto
    qed
    then show ?thesis using \<iota>_def unfolding entail_def by auto
  next
    case fact (* soundness of equality factoring *)
    then obtain L L' s t u u' C \<sigma>
      where \<iota>_def: \<open>\<iota> = Infer [{# L #} + {# L' #} + C] (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>)\<close>
        and mgu: \<open>is_mgu \<sigma> {(u, u')}\<close>
        and L_def: \<open>L = Lit True (Upair u s)\<close>
        and L'_def: \<open>L' = Lit True (Upair u' t)\<close>
      unfolding efactoring_inferences_def by blast
    have \<open>validate_clause I ({# L #} + {# L' #} + C) \<Longrightarrow> validate_clause I (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>)\<close> for I
    proof -
      assume \<open>validate_clause I ({# L #} + {# L' #} + C)\<close>
      then have validate_prem_\<sigma>: \<open>validate_clause I (subst_apply_cl ({# L #} + {# L' #} + C) \<sigma>)\<close>
        using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl ({# Lit False (Upair t s) #} +{# L' #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>) \<tau>)\<close>
        then have \<open>ground_cl (subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) (\<sigma> \<circ>\<^sub>s \<tau>))\<close>
          using subst_cl_comp by metis
        then have ground: \<open>ground_cl (subst_apply_cl C (\<sigma> \<circ>\<^sub>s \<tau>)) \<and> ground_term (s \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) \<and> ground_term (t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) \<and> ground_term (u' \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>))\<close> using L'_def by auto
        with mgu have \<open>ground_term (u \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>))\<close> unfolding is_mgu_def unifiers_def by auto
        with ground L_def L'_def have \<open>ground_cl (subst_apply_cl ({# L #} + {# L' #} + C) (\<sigma> \<circ>\<^sub>s \<tau>))\<close> by auto
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# L #} + {# L' #} + C) \<sigma>) \<tau>)\<close>
          using subst_cl_comp [of \<open>{# L #} + {# L' #} + C\<close> \<sigma> \<tau>] by argo
        with validate_prem_\<sigma> have validate_L: \<open>\<exists>M \<in># subst_apply_cl ({# L #} + {# L' #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit M \<tau>)\<close>
          unfolding validate_clause_def by fast
        consider (a) \<open>\<exists>M \<in># subst_apply_cl ({# L' #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit M \<tau>)\<close>
               | (b) \<open>\<forall>M \<in># subst_apply_cl ({# L' #} + C) \<sigma>. \<not> validate_ground_lit I (subst_apply_lit M \<tau>)\<close>
          by auto
        then show \<open>\<exists>M \<in># subst_apply_cl ({# Lit False (Upair t s) #} + {# L' #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit M \<tau>)\<close>
        proof cases
          case a
          then show ?thesis by auto
        next
          case b
          with validate_L have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>)\<close> by auto
          then have \<open>validate_eq I (Upair (u \<cdot> \<sigma> \<cdot> \<tau>) (s \<cdot> \<sigma> \<cdot> \<tau>))\<close> using L_def by simp
          then have I_u_s: \<open>validate_eq I (Upair (u' \<cdot> \<sigma> \<cdot> \<tau>) (s \<cdot> \<sigma> \<cdot> \<tau>))\<close> using mgu unfolding is_mgu_def unifiers_def by auto
          from b have \<open>\<not> validate_ground_lit I (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>)\<close> by auto
          then have I_u_t: \<open>\<not> validate_eq I (Upair (u' \<cdot> \<sigma> \<cdot> \<tau>) (t \<cdot> \<sigma> \<cdot> \<tau>))\<close>
            using L'_def by simp
          from I_u_s I_u_t have \<open>\<not> validate_eq I (Upair (t \<cdot> \<sigma> \<cdot> \<tau>) (s \<cdot> \<sigma> \<cdot> \<tau>))\<close>
            using Rep_fo_interp [of I]
            by (smt Upair.abs_eq mem_Collect_eq symE trans_def validate_eq.abs_eq)
          then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (Lit False (Upair t s)) \<sigma>) \<tau>)\<close> by simp
          then show ?thesis by auto
        qed
      qed
      then show ?thesis unfolding validate_clause_def by blast
    qed
    then show ?thesis using \<iota>_def unfolding entail_def by force
  next
    case sup (* soundness of superposition *)
    then obtain s t t' u vs vt Le L L' C D \<sigma> b
      where \<iota>_def: \<open>\<iota> = Infer [{#Le#} + C, {#L#} + D] (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close>
        and Le_def: \<open>Le = Lit True (Upair s t)\<close>
        and L_def: \<open>L = Lit b (Upair vt u) \<and> L' = Lit b (Upair vs u)\<close>
        and mgu: \<open>is_mgu \<sigma> {(t, t')}\<close>
        and subterm: \<open>subterm_replace vs vt s t'\<close>
      unfolding pos_superposition_inferences_def neg_superposition_inferences_def by blast
    have \<open>validate_clause I ({#Le#} + C) \<Longrightarrow> validate_clause I ({#L#} + D) \<Longrightarrow> validate_clause I (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close> for I
    proof -
      assume \<open>validate_clause I ({#Le#} + C)\<close> and \<open>validate_clause I ({#L#} + D)\<close>
      then have validate_prems_\<sigma>: \<open>validate_clause I (subst_apply_cl ({#Le#} + C) \<sigma>) \<and> validate_clause I (subst_apply_cl ({#L#} + D) \<sigma>)\<close>
        using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L'#} + C + D) \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl ({#L'#} + C + D) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume ground_CD: \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L'#} + C + D) \<sigma>) \<tau>)\<close>
        (* the grounding of the conclusion is not necessarily a grounding of the premises, so we must extend it *)
        obtain \<upsilon> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (subst_apply_cl (subst_apply_cl ({#Le#} + C + {#L#} + D) \<sigma>) \<tau>) \<upsilon>)\<close>
          using ex_ground_instance by fast
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#Le#} + C + {#L#} + D) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
          using subst_cl_comp by metis
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#Le#} + C) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
              and \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L#} + D) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close> by auto
        then have \<open>(\<exists>L\<in>#subst_apply_cl ({#Le#} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>)))
                 \<and> (\<exists>L\<in>#subst_apply_cl ({#L#} + D) \<sigma>. validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>)))\<close>
          using validate_prems_\<sigma> unfolding validate_clause_def by blast
        then consider (1) \<open>\<exists>L. (L \<in># subst_apply_cl C \<sigma> \<or> L \<in># subst_apply_cl D \<sigma>) \<and> validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close> |
                      (2) \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit Le \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>)) \<and> validate_ground_lit I (subst_apply_lit (subst_apply_lit L \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
          by auto
        then have \<open>\<exists>L \<in># subst_apply_cl ({#L'#} + C + D) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
        proof cases
          case 1
          then obtain L
            where L_elem: \<open>L \<in># subst_apply_cl C \<sigma> \<or> L \<in># subst_apply_cl D \<sigma>\<close>
              and L_validate: \<open>validate_ground_lit I (subst_apply_lit L (\<tau> \<circ>\<^sub>s \<upsilon>))\<close> by auto
          then have \<open>vars_lit (subst_apply_lit L \<tau>) = {}\<close>
            using ground_CD by auto
          then have \<open>subst_apply_lit L (\<tau> \<circ>\<^sub>s \<upsilon>) = subst_apply_lit L \<tau>\<close>
            using subst_ground_lit [of \<open>subst_apply_lit L \<tau>\<close> \<upsilon>] subst_lit_comp [of L \<tau> \<upsilon>] by auto
          with L_elem L_validate show ?thesis by auto
        next
          case 2
          then have s_t_I: \<open>validate_eq I (Upair (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (t \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> using Le_def by simp
          from subterm have \<open>subterm_replace (vs \<cdot> \<sigma>) (vt \<cdot> \<sigma>) (s \<cdot> \<sigma>) (t' \<cdot> \<sigma>)\<close>
            using subterm_replace_stable_subst by blast
          then have \<open>subterm_replace (vs \<cdot> \<sigma>) (vt \<cdot> \<sigma>) (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)\<close>
            using mgu unfolding is_mgu_def unifiers_def by auto
          then have \<open>subterm_replace (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (t \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>)\<close>
            using mgu subterm_replace_stable_subst by blast
          moreover have \<open>ground_term (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<and> ground_term (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>)\<close>
          proof -
            have \<open>ground_lit (subst_apply_lit (subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>) \<upsilon>)\<close>
              by (simp add: subst_lit_comp \<open>ground_cl (subst_apply_cl (subst_apply_cl (add_mset L \<bottom>F + D) \<sigma>) (\<tau> \<circ>\<^sub>s \<upsilon>))\<close>)
            moreover have \<open>ground_lit (subst_apply_lit (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>) \<upsilon>)\<close>
              using ground_CD subst_ground_lit by fastforce
            ultimately show ?thesis using L_def by force
          qed
          ultimately have vs_vt_I: \<open>validate_eq I (Upair (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> using s_t_I subterm_replace_interp by simp
          have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>)\<close>
          proof (cases b)
            case True
            with L_def have \<open>validate_eq I (Upair (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> using 2 by auto
            with vs_vt_I have \<open>validate_eq I (Upair (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close>
              using Rep_fo_interp [of I]
              by (smt Upair.abs_eq mem_Collect_eq transE validate_eq.abs_eq)
            then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>) \<upsilon>)\<close>
              using True L_def by simp
            then show ?thesis using ground_CD subst_ground_lit by fastforce
          next
            case False
            with L_def have \<open>\<not> validate_eq I (Upair (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> using 2 by auto
            with vs_vt_I have \<open>\<not> validate_eq I (Upair (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close>
              using Rep_fo_interp [of I]
              by (smt Upair.abs_eq mem_Collect_eq symE transE validate_eq.abs_eq)
            then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>) \<upsilon>)\<close>
              using False L_def by simp
            then show ?thesis using ground_CD subst_ground_lit by fastforce
          qed
          then show ?thesis by auto
        qed
        then show ?thesis by auto
      qed
      then show ?thesis unfolding validate_clause_def by auto
    qed
    then show ?thesis unfolding entail_def using \<iota>_def by auto
  qed
qed

interpretation ground_inf: sound_inference_system ground_superposition_inference_system \<open>{\<bottom>G}\<close> \<open>(\<Turnstile>G)\<close>
proof
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>G {concl_of \<iota>}\<close> for \<iota>
  proof -
    assume \<open>\<iota> \<in> ground_superposition_inference_system\<close>
    then have \<open>Rep_ground_inference \<iota> \<in> superposition_inference_system\<close>
      unfolding ground_superposition_inference_system_def by auto
    then have \<open>set (prems_of (Rep_ground_inference \<iota>)) \<Turnstile>F {concl_of (Rep_ground_inference \<iota>)}\<close>
      using soundness by blast
    then show \<open>set (prems_of \<iota>) \<Turnstile>G {concl_of \<iota>}\<close> unfolding ground_entail_def by force
  qed
qed

definition Red_ground_clause :: \<open>('f, 'v) ground_clause set \<Rightarrow> ('f, 'v) ground_clause set\<close> where
\<open>Red_ground_clause N = {C. \<exists>N' \<subseteq> N. finite N' \<and> N' \<Turnstile>G {C}
                        \<and> (\<forall>D \<in> N'. D \<prec>G C)}\<close>

definition Red_ground_Inf :: \<open>('f, 'v) ground_clause set \<Rightarrow> ('f, 'v) ground_clause inference set\<close> where
\<open>Red_ground_Inf N = {\<iota>. (Rep_ground_inference \<iota>) \<in> superposition_inference_system
                     \<and> (\<exists>N' \<subseteq> N. finite N' \<and> N' \<Turnstile>G {concl_of \<iota>}
                     \<and> (\<forall>D \<in> N'. \<exists>P \<in> set (prems_of \<iota>). D \<prec>G P))}\<close>

lemma Red_ground_clause_entails: \<open>N \<Turnstile>G Red_ground_clause N\<close>
  unfolding ground_entail_def
proof (rule fo_consequence.all_formulas_entailed)
  show \<open>\<forall>C\<in>Rep_ground_clause ` Red_ground_clause N. Rep_ground_clause ` N \<Turnstile>F {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Rep_ground_clause ` Red_ground_clause N\<close>
    then obtain C' N' where C_def: \<open>C = Rep_ground_clause C'\<close> and \<open>N' \<subseteq> N\<close> and \<open>N' \<Turnstile>G {C'}\<close> unfolding Red_ground_clause_def by auto
    then have \<open>N \<Turnstile>G {C'}\<close>
      using ground_consequence.subset_entailed [of \<open>N'\<close> N] ground_consequence.entails_trans [of N N' \<open>{C'}\<close>] by auto
    with C_def show \<open>Rep_ground_clause ` N \<Turnstile>F {C}\<close> unfolding ground_entail_def by auto
  qed
qed

lemma smaller_clause_set:
  assumes \<open>finite N\<close>
  assumes \<open>C \<in> N\<close>
  assumes \<open>\<forall>C' \<in> N'. C' \<prec>F C\<close>
  shows \<open>(N - {C} \<union> N', N) \<in> clause_set_ord\<close>
proof -
  have eq: \<open>mset_set (N - {C}) + {#C#} = mset_set N\<close> using assms(1,2)
    using mset_set.remove by fastforce
  have \<open>\<forall>C'\<in>#mset_set N'. \<exists>D\<in>#{#C#}. C' \<prec>F D\<close> using assms(3)
    by (metis elem_mset_set empty_not_add_mset insert_DiffM mset_set.infinite multi_member_last)
  then have \<open>(mset_set (N - {C}) + mset_set N', mset_set (N - {C}) + {#C#}) \<in> mult clause_ord\<close>
    using one_step_implies_mult [of \<open>{#C#}\<close> \<open>mset_set N'\<close> clause_ord \<open>mset_set (N - {C})\<close>] by auto
  with eq have i: \<open>(mset_set (N - {C}) + mset_set N', mset_set N) \<in> mult clause_ord\<close> by auto
  have \<open>mset_set (N - {C} \<union> N') \<subseteq># mset_set (N - {C}) + mset_set N'\<close>
  by (smt UnE count_mset_set(1) count_mset_set(3) finite_Un leI mset_set.infinite mset_subset_eq_add_left mset_subset_eq_add_right subseteq_mset_def zero_order(3))
  then have ii: \<open>mset_set (N - {C} \<union> N') = mset_set (N - {C}) + mset_set N' \<or> (mset_set (N - {C} \<union> N'), mset_set (N - {C}) + mset_set N') \<in> mult clause_ord\<close>
    by (metis (no_types, lifting) add.left_neutral add_diff_cancel_left' add_diff_cancel_right' empty_iff one_step_implies_mult set_mset_empty subset_mset.le_add_same_cancel2 subset_mset.le_iff_add)
  with i ii have \<open>(mset_set (N - {C} \<union> N'), mset_set N) \<in> mult clause_ord\<close>
    by (metis mult_def transitive_closure_trans(2))
  then show ?thesis unfolding clause_set_ord_def by auto
qed

lemma smaller_ground_clause_set:
  assumes \<open>finite N\<close>
  assumes \<open>C \<in> N\<close>
  assumes \<open>\<forall>C' \<in> N'. C' \<prec>G C\<close>
  shows \<open>(N - {C} \<union> N', N) \<in> ground_clause_set_ord\<close>
proof -
  from assms(1) have \<open>finite (Rep_ground_clause ` N)\<close> by auto
  moreover from assms(2) have \<open>Rep_ground_clause C \<in> Rep_ground_clause ` N\<close> by auto
  moreover from assms(3) have \<open>\<forall>C' \<in> (Rep_ground_clause ` N'). C' \<prec>F Rep_ground_clause C\<close>
    unfolding ground_clause_ord_def by auto
  ultimately have \<open>(Rep_ground_clause ` N - {Rep_ground_clause C} \<union> Rep_ground_clause ` N', Rep_ground_clause ` N) \<in> clause_set_ord\<close>
    using smaller_clause_set by auto
  moreover have \<open>Rep_ground_clause ` N - {Rep_ground_clause C} \<union> Rep_ground_clause ` N' = Rep_ground_clause ` (N - {C} \<union> N')\<close>
    using Rep_ground_clause_inject by fastforce
  ultimately show ?thesis unfolding ground_clause_set_ord_def by auto
qed

(* the next two lemmas show that redundant clauses in a set N play no role in deciding whether a
   clause or inference is redundant in N *)
lemma minimal_Red_ground_clause_subset:
  assumes \<open>C \<in> Red_ground_clause N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> C \<in> Red_ground_clause M \<and> (\<forall>D \<in> M. D \<notin> Red_ground_clause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>G {C} \<and> (\<forall>D \<in> NC1. D \<prec>G C)\<close> (is \<open>?P NC1\<close>)
    unfolding Red_ground_clause_def by auto
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> ground_clause_set_ord \<Longrightarrow> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>ground_clause_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] wf_ground_clause_set_ord by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_ground_clause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_ground_clause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>G {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. E \<prec>G D\<close>
      using Red_ground_clause_def by auto
    (* construct a smaller set than NC0 in which C is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> ground_clause_set_ord\<close>
      using smaller_ground_clause_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>G {C}\<close>
    proof -
      from ND1_entails have \<open>?NCC \<Turnstile>G NC0 - {D} \<union> {D}\<close>
        by (meson ground_consequence.entail_union ground_consequence.entails_trans inf_sup_ord(3) inf_sup_ord(4) ground_consequence.subset_entailed)
      also have \<open>NC0 - {D} \<union> {D} \<Turnstile>G NC0\<close> using ground_consequence.subset_entailed [of NC0 \<open>NC0 - {D} \<union> {D}\<close>] by blast
      also have \<open>NC0 \<Turnstile>G {C}\<close> using NC0_prop Red_ground_clause_entails ground_consequence.entail_set_all_formulas by blast
      finally show ?thesis by auto
    qed
    moreover have \<open>\<forall>E \<in> ?NCC. E \<prec>G C\<close>
    proof
      fix E
      assume \<open>E \<in> ?NCC\<close>
      then consider (a) \<open>E \<in> NC0\<close> | (b) \<open>E \<in> ND1\<close> by blast
      then show \<open>E \<prec>G C\<close>
      proof cases
        case a
        then show ?thesis using NC0_prop by auto
      next
        case b
        then have \<open>E \<prec>G D\<close> using ND1_ord by auto
        also have \<open>D \<prec>G C\<close> using \<open>D \<in> NC0\<close> NC0_prop by auto
        finally show ?thesis using trans_ground_clause_ord by auto
      qed
    qed
    ultimately show False using NC0_min by blast
  qed
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> C \<in> Red_ground_clause NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_ground_clause N)\<close>
    using Red_ground_clause_def by blast
  then show ?thesis by auto
qed

lemma minimal_Red_ground_Inf_subset:
  assumes \<open>\<iota> \<in> Red_ground_Inf N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> \<iota> \<in> Red_ground_Inf M \<and> (\<forall>D \<in> M. D \<notin> Red_ground_clause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>G {concl_of \<iota>} \<and> (\<forall>D \<in> NC1. \<exists>P\<in>set (prems_of \<iota>). D \<prec>G P)\<close> (is \<open>?P NC1\<close>)
    unfolding Red_ground_Inf_def by auto
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> ground_clause_set_ord \<Longrightarrow> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>ground_clause_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] wf_ground_clause_set_ord by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_ground_clause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_ground_clause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>G {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. E \<prec>G D\<close>
      using Red_ground_clause_def by auto
    (* construct a smaller set than NC0 in which \<iota> is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> ground_clause_set_ord\<close>
      using smaller_ground_clause_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>G {concl_of \<iota>}\<close>
    proof -
      from ND1_entails have \<open>?NCC \<Turnstile>G NC0 - {D} \<union> {D}\<close>
        by (meson ground_consequence.entail_union ground_consequence.entails_trans inf_sup_ord(3) inf_sup_ord(4) ground_consequence.subset_entailed)
      also have \<open>NC0 - {D} \<union> {D} \<Turnstile>G NC0\<close> using ground_consequence.subset_entailed [of NC0 \<open>NC0 - {D} \<union> {D}\<close>] by blast
      also have \<open>NC0 \<Turnstile>G {concl_of \<iota>}\<close> using NC0_prop Red_ground_clause_entails ground_consequence.entail_set_all_formulas by blast
      finally show ?thesis by auto
    qed
    moreover have \<open>\<forall>E \<in> ?NCC. \<exists>P\<in>set (prems_of \<iota>).  E \<prec>G P\<close>
    proof
      fix E
      assume \<open>E \<in> ?NCC\<close>
      then consider (a) \<open>E \<in> NC0\<close> | (b) \<open>E \<in> ND1\<close> by blast
      then show \<open>\<exists>P \<in> set (prems_of \<iota>). E \<prec>G P\<close>
      proof cases
        case a
        then show ?thesis using NC0_prop by auto
      next
        case b
        obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close> and P_prop: \<open>D \<prec>G P\<close> using \<open>D \<in> NC0\<close> NC0_prop by auto
        from b have \<open>E \<prec>G D\<close> using ND1_ord by auto
        also have \<open>D \<prec>G P\<close> using P_prop .
        finally show ?thesis using trans_ground_clause_ord P_elem by auto
      qed
    qed
    ultimately show False using NC0_min by blast
  qed
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> \<iota> \<in> Red_ground_Inf NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_ground_clause N)\<close>
    using Red_ground_Inf_def assms by blast
  then show ?thesis by auto
qed

lemma subterm_replace_ground: \<open>ground_term t \<Longrightarrow> ground_term u \<Longrightarrow> subterm_replace s t u v \<Longrightarrow> ground_term s \<and> ground_term v\<close>
proof (induction s arbitrary: t)
  case (Var x)
  from \<open>subterm_replace (Var x) t u v\<close> show ?case
  proof cases
    case base
    with \<open>ground_term t\<close> and \<open>ground_term u\<close> show ?thesis by auto
  qed
next
  case (Fun f args)
  from \<open>subterm_replace (Fun f args) t u v\<close> show ?case
  proof cases
    case base
    with \<open>ground_term t\<close> and \<open>ground_term u\<close> show ?thesis by auto
  next
    case (step s' t' a1 a2)
    with Fun show ?thesis by auto
  qed
qed

lemma subterm_replace_ground_left: \<open>ground_term s \<Longrightarrow> subterm_replace s t u v \<Longrightarrow> ground_term u\<close>
proof (induction s arbitrary: t)
  case (Var x)
  then show ?case by auto (* contradiction *)
next
  case (Fun f args)
  from \<open>subterm_replace (Fun f args) t u v\<close> show ?case
  proof cases
    case base
    with \<open>ground_term (Fun f args)\<close> show ?thesis by auto
  next
    case (step s' t' a1 a2)
    with Fun \<open>ground_term (Fun f args)\<close> show ?thesis by auto
  qed
qed

lemma subterm_replace_ground_right: \<open>ground_term t \<Longrightarrow> subterm_replace s t u v \<Longrightarrow> ground_term v\<close>
proof (induction t arbitrary: s)
  case (Var x)
  then show ?case by auto (* contradiction *)
next
  case (Fun f args)
  from \<open>subterm_replace s (Fun f args) u v\<close> show ?case
  proof cases
    case base
    with \<open>ground_term (Fun f args)\<close> show ?thesis by auto
  next
    case (step s' t' a1 a2)
    with Fun \<open>ground_term (Fun f args)\<close> show ?thesis by auto
  qed
qed

lemma subterm_replace_ord:
  assumes \<open>ground_term vs\<close>
      and \<open>ground_term vt\<close>
      and \<open>s \<prec> t\<close>
      and \<open>subterm_replace vs vt s t\<close>
    shows \<open>vs \<prec> vt\<close>
proof -
  have \<open>subterm_replace vs vt s t \<Longrightarrow> ground_term vs \<Longrightarrow> ground_term vt \<Longrightarrow> s \<prec> t \<Longrightarrow> vs \<prec> vt\<close>
  proof (induct rule: subterm_replace.induct)
    case (base s t)
    then show ?case by auto
  next
    case (step s t u v f a1 a2)
    then show ?case using step by (simp add: term_ord_ground_term_comp)
  qed
  then show ?thesis using assms by blast
qed

lemma subterm_replace_ord_2:
  assumes \<open>ground_term t\<close>
      and \<open>ground_term vt\<close>
      and \<open>subterm_replace vs vt s t\<close>
    shows \<open>t \<preceq> vt\<close>
proof -
  have \<open>subterm_replace vs vt s t \<Longrightarrow> ground_term vt \<Longrightarrow> ground_term t \<Longrightarrow> t \<preceq> vt\<close>
  proof (induct rule: subterm_replace.induct)
    case (base s t)
    then show ?case by blast
  next
    case (step s t u v f a1 a2)
    then have gr: \<open>ground_term v \<and> ground_term t \<and> ground_term (Fun f (a1 @ t # a2))\<close> by auto
    have \<open>v \<preceq> t\<close> using gr step by blast
    moreover have \<open>t \<prec> Fun f (a1 @ t # a2)\<close> using gr term_ord_ground_subterm_comp by blast
    ultimately show ?case using term_ord_trans unfolding trans_def by blast
  qed
  then show ?thesis using assms by blast
qed

lemma exists_premise_greater:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<exists>D \<in> set (prems_of \<iota>). concl_of \<iota> \<prec>G D\<close>
proof -
  from assms consider (res) \<open>Rep_ground_inference \<iota> \<in> eresolution_inferences\<close>
    | (fact) \<open>Rep_ground_inference \<iota> \<in> efactoring_inferences\<close>
    | (supr) \<open>Rep_ground_inference \<iota> \<in> pos_superposition_inferences \<or> Rep_ground_inference \<iota> \<in> neg_superposition_inferences\<close>
    unfolding ground_superposition_inference_system_def by auto
  then show ?thesis
  proof cases
    case res
    then obtain s s' C \<sigma> where prems_def: \<open>Rep_ground_clause ` (set (prems_of \<iota>)) = {{#Lit False (Upair s s')#} + C}\<close>
                           and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl C \<sigma>\<close>
      unfolding eresolution_inferences_def by auto
    then obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close> and P_def: \<open>Rep_ground_clause P = {#Lit False (Upair s s')#} + C\<close> by blast
    then have \<open>ground_cl C\<close> using Rep_ground_clause [of P] by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) = C\<close> using subst_ground_cl [of C \<sigma>] concl_def by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) \<subset># Rep_ground_clause P\<close> using P_def by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) \<prec>F Rep_ground_clause P\<close>
      by (simp add: clause_ord_def subset_implies_mult)
    then have \<open>concl_of \<iota> \<prec>G P\<close> unfolding ground_clause_ord_def by auto
    then show ?thesis using P_elem by auto
  next
    case fact
    then obtain L L' s t u u' C \<sigma> where \<open>Rep_ground_inference \<iota> = Infer [{#L#} + {#L'#} + C] (subst_apply_cl ({#Lit False (Upair t s)#} + {#L'#} + C) \<sigma>)\<close>
                                    and L_def: \<open>L = Lit True (Upair u s)\<close>
                                    and L'_def: \<open>L' = Lit True (Upair u' t)\<close>
                                    and ord: \<open>\<not> u \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>\<close>
                                    and mgu: \<open>is_mgu \<sigma> {(u, u')}\<close>
                                    and L_max: \<open>\<forall>M \<in># {#L'#} + C. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit L \<sigma>\<close>
      unfolding efactoring_inferences_def by blast
    then obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close>
                    and P_def: \<open>Rep_ground_clause P = {# L #} + {# L' #} + C\<close>
                    and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl ({#Lit False (Upair t s)#} + {#L'#} + C) \<sigma>\<close> by force
    then have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term u \<and> ground_term u' \<and> ground_cl C\<close>
      using Rep_ground_clause [of P] L_def L'_def by auto
    then have \<open>ground_cl ({#Lit False (Upair t s)#} + {#L'#} + C)\<close> using L'_def by auto
    then have concl_def': \<open>Rep_ground_clause (concl_of \<iota>) = {#Lit False (Upair t s)#} + {#L'#} + C\<close>
      using subst_ground_cl concl_def by metis
    have ord': \<open>s \<prec> u\<close>
      using ground ord subst_ground_term term_ord_ground_total unfolding total_on_def
    by (metis (mono_tags, lifting) mem_Collect_eq)
    moreover have \<open>t \<preceq> s\<close>
    proof (rule ccontr)
      assume \<open>\<not> t \<preceq> s\<close>
      then have \<open>s \<prec> t\<close>
        by (metis (mono_tags, lifting) ground mem_Collect_eq term_ord_ground_total total_on_def)
      then have \<open>({#u#} + {#s#}, {#u#} + {#t#}) \<in> mult term_ord\<close>
        using one_step_implies_mult [of \<open>{#t#}\<close> \<open>{#s#}\<close> term_ord \<open>{#u#}\<close>] by auto
      then have \<open>({#u,s#}, {#u,t#}) \<in> mult term_ord\<close>
        by (metis add_mset_add_single union_commute)
      moreover have \<open>u = u'\<close> using ground mgu unfolding is_mgu_def unifiers_def
        by (metis (no_types, lifting) fst_conv in_unifiersE is_mgu_def mgu singletonI snd_conv subst_ground_term)
      ultimately have \<open>L \<prec>L L'\<close> using L_def L'_def unfolding lit_ord_def by simp
      moreover have \<open>L' \<preceq>L L\<close> using L_max ground L_def L'_def subst_ground_lit
        by (simp add: subst_ground_term)
      ultimately show False
        by (simp add: wf_lit_ord wf_not_sym)
    qed
    ultimately have \<open>s \<prec> u \<and> t \<prec> u\<close>
      using term_ord_trans unfolding trans_def by auto
    then have \<open>({#t, t, s, s#}, {#u, s#}) \<in> mult term_ord\<close>
      using one_step_implies_mult [of \<open>{#u#}\<close> \<open>{#t,t,s#}\<close> term_ord \<open>{#s#}\<close>] by auto
    then have \<open>Lit False (Upair t s) \<prec>L L\<close> using L_def unfolding lit_ord_def
      by (smt add_mset_add_single case_prodI inv_image_def mem_Collect_eq mset_lit.simps mset_upair union_mset_add_mset_left union_mset_add_mset_right)
    then have \<open>(Rep_ground_clause (concl_of \<iota>), Rep_ground_clause P) \<in> mult lit_ord\<close>
      using one_step_implies_mult [of \<open>{#L#}\<close> \<open>{#Lit False (Upair t s)#}\<close> lit_ord \<open>{#L'#} + C\<close>] concl_def' P_def
      by (simp add: union_commute)
    then show ?thesis using P_elem unfolding ground_clause_ord_def clause_ord_def by auto
  next
    case supr
    then obtain s t t' u vs vt Le L L' C D \<sigma> b where \<open>Rep_ground_inference \<iota> = Infer [{#Le#} + C, {#L#} + D] (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close>
                                                 and ord: \<open>\<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma> \<and> \<not> vt \<cdot> \<sigma> \<preceq> u \<cdot> \<sigma>\<close>
                                                 and Le_def: \<open>Le = Lit True (Upair s t)\<close>
                                                 and L_def: \<open>L = Lit b (Upair vt u) \<and> L' = Lit b (Upair vs u)\<close>
                                                 and subterm: \<open>subterm_replace vs vt s t'\<close>
                                                 and mgu: \<open>is_mgu \<sigma> {(t, t')}\<close>
                                                 and lit_ord: \<open>subst_apply_lit Le \<sigma> \<prec>L subst_apply_lit L \<sigma>\<close>
                                                 and eq_max: \<open>\<forall>M\<in>#C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit Le \<sigma>\<close>
      unfolding pos_superposition_inferences_def neg_superposition_inferences_def by blast
    then obtain P1 P2 where \<open>P1 \<in> set (prems_of \<iota>)\<close>
                        and \<open>Rep_ground_clause P1 = {#Le#} + C\<close>
                        and P2_elem: \<open>P2 \<in> set (prems_of \<iota>)\<close>
                        and P2_def: \<open>Rep_ground_clause P2 = {#L#} + D\<close>
                        and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl ({#L'#} + C + D) \<sigma>\<close> by fastforce
    then have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term u \<and> ground_term vt \<and> ground_cl C \<and> ground_cl D\<close>
      using Rep_ground_clause [of P1] Rep_ground_clause [of P2] L_def Le_def by auto
    with subterm subterm_replace_ground have ground': \<open>ground_term t' \<and> ground_term vs\<close> by metis
    then have \<open>ground_cl ({#L'#} + C + D)\<close> using L_def ground by auto
    then have concl_def': \<open>Rep_ground_clause (concl_of \<iota>) = {#L'#} + C + D\<close>
      using concl_def subst_ground_cl by metis
    from mgu have \<open>t \<cdot> \<sigma> = t' \<cdot> \<sigma>\<close>
      unfolding is_mgu_def unifiers_def by auto
    then have \<open>t' = t\<close> using ground ground' subst_ground_term by metis
    from ord ground subst_ground_term have \<open>\<not> t \<preceq> s\<close> by metis
    with ground term_ord_ground_total have \<open>s \<prec> t\<close> unfolding total_on_def by auto
    then have vs_vt_ord: \<open>vs \<prec> vt\<close>
      using subterm subterm_replace_ord ground ground' \<open>t' = t\<close> by metis
    have lit_ord': \<open>L' \<prec>L L\<close>
    proof (cases b)
      case True
      then have \<open>mset_lit L = {#vt,u#} \<and> mset_lit L' = {#vs,u#}\<close> using L_def by auto
      moreover have \<open>({#vs,u#}, {#vt,u#}) \<in> mult term_ord\<close>
        using one_step_implies_mult [of \<open>{#vt#}\<close> \<open>{#vs#}\<close> term_ord \<open>{#u#}\<close>] vs_vt_ord by auto
      ultimately show ?thesis unfolding lit_ord_def by auto
    next
      case False
      then have \<open>mset_lit L = {#vt,vt,u,u#} \<and> mset_lit L' = {#vs,vs,u,u#}\<close> using L_def by auto
      moreover have \<open>({#vs,vs,u,u#}, {#vt,vt,u,u#}) \<in> mult term_ord\<close>
        using one_step_implies_mult [of \<open>{#vt,vt#}\<close> \<open>{#vs,vs#}\<close> term_ord \<open>{#u,u#}\<close>] vs_vt_ord by auto
      ultimately show ?thesis unfolding lit_ord_def by auto
    qed
    have \<open>M \<in># {# L' #} + C \<Longrightarrow> M \<prec>L L\<close> for M
    proof -
      assume \<open>M \<in># {# L' #} + C\<close>
      then consider (a) \<open>M = L'\<close> | (b) \<open>M \<in># C\<close> by auto
      then show \<open>M \<prec>L L\<close>
      proof cases
        case a
        with lit_ord' show ?thesis by auto
      next
        case b
        then have \<open>subst_apply_lit M \<sigma> \<prec>L subst_apply_lit Le \<sigma>\<close> using eq_max by auto
        then have \<open>subst_apply_lit M \<sigma> \<prec>L subst_apply_lit L \<sigma>\<close> using trans_lit_ord lit_ord by (meson transE)
        moreover have \<open>ground_lit M \<and> ground_lit L\<close> using b ground L_def by auto
        ultimately show ?thesis using subst_ground_lit by metis
      qed
    qed
    then have \<open>({#L'#} + C + D, {#L#} + D) \<in> mult lit_ord\<close>
      using one_step_implies_mult [of \<open>{#L#}\<close> \<open>{#L'#} + C\<close> lit_ord \<open>D\<close>]
      by (simp add: union_commute)
    then have \<open>concl_of \<iota> \<prec>G P2\<close>
      using concl_def' P2_def
      unfolding ground_clause_ord_def clause_ord_def by auto
    with P2_elem show ?thesis by auto
  qed
qed

lemma Red_Inf_concl_of:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<iota> \<in> Red_ground_Inf {concl_of \<iota>}\<close>
proof -
  let ?N' = \<open>{concl_of \<iota>}\<close>
  have \<open>?N' \<Turnstile>G {concl_of \<iota>}\<close> by (simp add: ground_consequence.subset_entailed)
  moreover have \<open>\<forall>D\<in>?N'. \<exists>P\<in>set (prems_of \<iota>). D \<prec>G P\<close>
  proof
    fix D
    assume \<open>D \<in> ?N'\<close>
    then have \<open>D = concl_of \<iota>\<close> by auto
    then obtain P where \<open>P \<in> set (prems_of \<iota>)\<close>
                    and \<open>D \<prec>G P\<close>
      using exists_premise_greater [of \<iota>] assms by blast
    then show \<open>\<exists>P\<in>set (prems_of \<iota>). D \<prec>G P\<close> by blast
  qed
  moreover have \<open>Rep_ground_inference \<iota> \<in> superposition_inference_system\<close>
    using assms unfolding ground_superposition_inference_system_def by blast
  ultimately show ?thesis unfolding Red_ground_Inf_def by blast
qed

lemma Red_ground_clause_entailed: \<open>N - Red_ground_clause N \<Turnstile>G Red_ground_clause N\<close>
  unfolding ground_entail_def
proof (rule fo_consequence.all_formulas_entailed)
  show \<open>\<forall>C \<in> Rep_ground_clause ` Red_ground_clause N. Rep_ground_clause ` (N - Red_ground_clause N) \<Turnstile>F {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Rep_ground_clause ` Red_ground_clause N\<close>
    then obtain C' where \<open>C' \<in> Red_ground_clause N\<close>
                     and C'_def: \<open>Rep_ground_clause C' = C\<close> by auto
    then obtain M  where M_subset: \<open>M \<subseteq> N\<close>
                     and M_Red: \<open>C' \<in> Red_ground_clause M\<close>
                     and M_min: \<open>\<forall>D \<in> M. D \<notin> Red_ground_clause N\<close>
      using minimal_Red_ground_clause_subset by metis
    with M_subset have \<open>M \<subseteq> N - Red_ground_clause N\<close> by auto
    then have \<open>N - Red_ground_clause N \<Turnstile>G M\<close> using ground_consequence.subset_entailed by auto
    also have \<open>M \<Turnstile>G Red_ground_clause M\<close> using Red_ground_clause_entails by auto
    also have \<open>Red_ground_clause M \<Turnstile>G {C'}\<close> using M_Red ground_consequence.subset_entailed by blast
    finally show \<open>Rep_ground_clause `  (N - Red_ground_clause N) \<Turnstile>F {C}\<close>
      using C'_def unfolding ground_entail_def by auto
  qed
qed

interpretation calculus \<open>{\<bottom>G}\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause
proof
  show \<open>Red_ground_Inf N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_ground_Inf_def ground_superposition_inference_system_def by auto
next
  show \<open>B \<in> {\<bottom>G} \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> N - Red_ground_clause N \<Turnstile>G {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> {\<bottom>G}\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have \<open>Rep_ground_clause ` N \<Turnstile>F {\<bottom>F}\<close>
      unfolding ground_entail_def by auto
    then have N_unsat: \<open>\<exists>C \<in> Rep_ground_clause ` N. \<not>validate_clause I C\<close> for I
      unfolding entail_def validate_clause_def by simp
    assume \<open>\<not> N - Red_ground_clause N \<Turnstile>G {B}\<close>
    then have \<open>\<not> Rep_ground_clause ` (N - Red_ground_clause N) \<Turnstile>F {Rep_ground_clause B}\<close>
      unfolding ground_entail_def by auto
    with N_unsat obtain I where I_model: \<open>C \<in> Rep_ground_clause ` (N - Red_ground_clause N) \<Longrightarrow> validate_clause I C\<close> for C
      unfolding entail_def validate_clause_def by metis
    with N_unsat obtain C where \<open>C \<in> Rep_ground_clause ` (Red_ground_clause N)\<close>
                          and C_not_valid: \<open>\<not> validate_clause I C\<close>
      by blast
    with Red_ground_clause_entailed I_model have \<open>validate_clause I C\<close>
      unfolding ground_entail_def entail_def by blast
    with C_not_valid show False by blast
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_ground_clause N \<subseteq> Red_ground_clause N'\<close> for N N' unfolding Red_ground_clause_def by fast
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_ground_Inf N \<subseteq> Red_ground_Inf N'\<close> for N N' unfolding Red_ground_Inf_def by fast
next
  show \<open>N' \<subseteq> Red_ground_clause N \<Longrightarrow> Red_ground_clause N \<subseteq> Red_ground_clause (N - N')\<close> for N' N
  proof
    fix C
    assume N'_subset: \<open>N' \<subseteq> Red_ground_clause N\<close> and \<open>C \<in> Red_ground_clause N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>C \<in> Red_ground_clause M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_ground_clause N)\<close>
      using minimal_Red_ground_clause_subset by metis
    then have \<open>C \<in> Red_ground_clause M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>C \<in> Red_ground_clause (N - N')\<close> unfolding Red_ground_clause_def by fast
  qed
next
  show \<open>N' \<subseteq> Red_ground_clause N \<Longrightarrow> Red_ground_Inf N \<subseteq> Red_ground_Inf (N - N')\<close> for N' N
  proof
    fix \<iota>
    assume N'_subset: \<open>N' \<subseteq> Red_ground_clause N\<close> and \<open>\<iota> \<in> Red_ground_Inf N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>\<iota> \<in> Red_ground_Inf M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_ground_clause N)\<close>
      using minimal_Red_ground_Inf_subset by metis
    then have \<open>\<iota> \<in> Red_ground_Inf M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>\<iota> \<in> Red_ground_Inf (N - N')\<close> unfolding Red_ground_Inf_def by fast
  qed
next
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_ground_Inf N\<close> for \<iota> N
  proof -
    assume \<open>\<iota> \<in> ground_superposition_inference_system\<close>
    then have \<open>\<iota> \<in> Red_ground_Inf {concl_of \<iota>}\<close>
      using Red_Inf_concl_of [of \<iota>] by blast
    then show \<open>concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_ground_Inf N\<close> unfolding Red_ground_Inf_def by fast
  qed
qed

(* rewriting *)

inductive local_rewrite_by_trs :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where
    eq: \<open>(t, s) \<in> S \<Longrightarrow> local_rewrite_by_trs S t s\<close> |
    func: \<open>(t, s) \<in> S \<Longrightarrow> local_rewrite_by_trs S (Fun f (a1 @ t # a2)) (Fun f (a1 @ s # a2))\<close>

inductive rewrite_by_trs :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where
    rew: \<open>local_rewrite_by_trs S t s \<Longrightarrow> rewrite_by_trs S t s\<close> |
    trans: \<open>local_rewrite_by_trs S u t \<Longrightarrow> rewrite_by_trs S t s \<Longrightarrow> rewrite_by_trs S u s\<close>

definition confluent :: \<open>('f, 'v) trs \<Rightarrow> bool\<close>
  where \<open>confluent TRS = (!s t u. rewrite_by_trs TRS s t \<longrightarrow> rewrite_by_trs TRS s u \<longrightarrow> (\<exists>v. rewrite_by_trs TRS t v \<and> rewrite_by_trs TRS u v))\<close>

definition locally_confluent :: \<open>('f, 'v) trs \<Rightarrow> bool\<close>
  where \<open>locally_confluent TRS = (!s t u. local_rewrite_by_trs TRS s t \<longrightarrow> local_rewrite_by_trs TRS s u \<longrightarrow> (\<exists>v. rewrite_by_trs TRS t v \<and> rewrite_by_trs TRS u v))\<close>

definition irreducible :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>irreducible TRS t = (\<forall>s. \<not>rewrite_by_trs TRS t s)\<close>

definition normal_form :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>normal_form TRS t s = (irreducible TRS s \<and> (s = t \<or> rewrite_by_trs TRS t s))\<close>

definition equiv_class_of_trs :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) interp\<close>
  where \<open>equiv_class_of_trs S = {(s,t) | s t. ground_term s \<and> ground_term t \<and> (\<exists>u. normal_form S s u \<and> normal_form S t u)}\<close>

abbreviation ordered :: \<open>('f, 'v) trs \<Rightarrow> bool\<close>
  where \<open>ordered S \<equiv> \<forall> (t, s) \<in> S. s \<prec> t\<close>

lemma terminating_locally_confluent:
  assumes \<open>locally_confluent TRS\<close>
      and \<open>ordered TRS\<close>
    shows \<open>confluent TRS\<close>
proof -
  have \<open>rewrite_by_trs TRS s t \<Longrightarrow> rewrite_by_trs TRS s u \<Longrightarrow> (\<exists>v. rewrite_by_trs TRS t v \<and> rewrite_by_trs TRS u v)\<close> for s t u
    sorry
  then show ?thesis unfolding confluent_def by blast
qed

lemma rewrite_trans: \<open>rewrite_by_trs S s t \<Longrightarrow> rewrite_by_trs S t u \<Longrightarrow> rewrite_by_trs S s u\<close>
proof (induct rule: rewrite_by_trs.induct; simp add: rewrite_by_trs.trans) qed

lemma non_ground_comparison:
  \<open>ground_term t \<Longrightarrow> \<not> ground_term s \<Longrightarrow> \<not> s \<prec> t\<close> for s t
proof -
  assume \<open>ground_term t\<close> and \<open>\<not> ground_term s\<close>
  let ?\<sigma> = \<open>\<lambda>x. t\<close>
  have grounding: \<open>ground_term (s \<cdot> ?\<sigma>)\<close> for s :: \<open>('f, 'v) term\<close> proof (induct s; simp add: \<open>ground_term t\<close>) qed
  have \<open>\<not> ground_term s \<Longrightarrow> \<not> s \<cdot> ?\<sigma> \<prec> t \<cdot> ?\<sigma>\<close>
  proof (induct s)
    case (Var x)
    then show ?case using subst_ground_term wf_term_ord \<open>ground_term t\<close> by fastforce
  next
    case (Fun f args)
    then obtain s' where \<open>s' \<in> set args\<close>
                     and \<open>vars_term s' \<noteq> {}\<close>
                     and nlt: \<open>\<not> s' \<cdot> ?\<sigma> \<prec> t \<cdot> ?\<sigma>\<close> by auto
    then have \<open>\<not> (Fun f args) \<cdot> ?\<sigma> \<preceq> s' \<cdot> ?\<sigma>\<close>
      using term_ord_subterm_comp by auto
    then have \<open>s' \<cdot> ?\<sigma> \<prec> Fun f args \<cdot> ?\<sigma>\<close>
      using grounding term_ord_ground_total unfolding total_on_def by blast
    moreover have le: \<open>t \<cdot> ?\<sigma> \<preceq> s' \<cdot> ?\<sigma>\<close>
      using nlt grounding term_ord_ground_total unfolding total_on_def by blast
    ultimately show \<open>\<not> Fun f args \<cdot> ?\<sigma> \<prec> t \<cdot> ?\<sigma>\<close>
      using le term_ord_trans nlt unfolding trans_def by blast
  qed
  then show ?thesis
    using \<open>\<not> ground_term s\<close> grounding term_ord_stable_grounding by blast
qed

lemma ordered_trs_preserve_groundness_local:
  \<open>local_rewrite_by_trs S t t' \<Longrightarrow> ordered S \<Longrightarrow> ground_term t \<Longrightarrow> ground_term t'\<close>
proof (induct rule: local_rewrite_by_trs.induct)
  case (eq t s S)
  then show ?case
    using non_ground_comparison by fast
next
  case (func t s S f a1 a2)
  then show ?case
    using non_ground_comparison by fastforce
qed

lemma ordered_trs_preserve_groundness:
  \<open>rewrite_by_trs S t t' \<Longrightarrow> ordered S \<Longrightarrow> ground_term t \<Longrightarrow> ground_term t'\<close>
proof (induct rule: rewrite_by_trs.induct)
  case (rew S t s)
  then show ?case
    using ordered_trs_preserve_groundness_local by auto
next
  case (trans S u t s)
  then show ?case
    using ordered_trs_preserve_groundness_local by blast
qed

lemma ordered_local_rewriting: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> local_rewrite_by_trs S t s \<Longrightarrow> s \<prec> t\<close>
proof -
  assume \<open>local_rewrite_by_trs S t s\<close>
  then show \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> s \<prec> t\<close>
  proof (induct rule: local_rewrite_by_trs.induct)
    case (eq t s S)
    then show ?case by blast
  next
    case (func t s S f a1 a2)
    then have \<open>ground_term (Fun f (a1 @ s # a2)) \<and> ground_term (Fun f (a1 @ t # a2))\<close> 
      using list.set(2) non_ground_comparison set_append by fastforce
    moreover have \<open>\<not> Fun f (a1 @ t # a2) \<preceq> Fun f (a1 @ s # a2)\<close> using term_ord_term_comp func by blast
    ultimately show ?case using term_ord_ground_total unfolding total_on_def
      by (metis (mono_tags, lifting) mem_Collect_eq)
  qed
qed

lemma ordered_rewriting: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> rewrite_by_trs S t s \<Longrightarrow> s \<prec> t\<close>
proof -
  assume \<open>rewrite_by_trs S t s\<close>
  then show \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> s \<prec> t\<close>
  proof (induct rule: rewrite_by_trs.induct)
    case (rew S t s)
    then show ?case
      using ordered_local_rewriting by blast
  next
    case (trans S u t s)
    then have \<open>s \<prec> t \<and> t \<prec> u\<close> 
      using ordered_local_rewriting ordered_trs_preserve_groundness_local by blast
    then show ?case using term_ord_trans trans_def by fast
  qed
qed

lemma normal_form_le: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> normal_form S t s \<Longrightarrow> s \<preceq> t\<close>
  using normal_form_def ordered_rewriting by blast

lemma ordered_normalizing: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> \<exists>t'. normal_form S t t'\<close>
proof -
  assume \<open>ordered S\<close> and \<open>ground_term t\<close>
  have \<open>ground_term t \<longrightarrow> (\<exists>t'. normal_form S t t')\<close>
  proof (rule wf_induct [of \<open>term_ord\<close>])
    show \<open>wf term_ord\<close> using wf_term_ord .
  next
    show \<open>\<forall>s. s \<prec> t \<longrightarrow> ground_term s \<longrightarrow> (\<exists>s'. normal_form S s s') \<Longrightarrow> ground_term t \<longrightarrow> (\<exists>t'. normal_form S t t')\<close> for t
    proof -
      assume ind: \<open>\<forall>s. s \<prec> t \<longrightarrow> ground_term s \<longrightarrow> (\<exists>s'. normal_form S s s')\<close>
      show \<open>ground_term t \<longrightarrow> (\<exists>t'. normal_form S t t')\<close>
      proof (cases \<open>irreducible S t\<close>)
        case True
        then show ?thesis unfolding normal_form_def by blast
      next
        case False
        then obtain s where rew: \<open>local_rewrite_by_trs S t s\<close> unfolding irreducible_def
          using rewrite_by_trs.cases by blast
        show ?thesis
        proof
          assume \<open>ground_term t\<close>
          then have \<open>ground_term s \<and> s \<prec> t\<close>
            using ordered_local_rewriting ordered_trs_preserve_groundness_local \<open>ordered S\<close> rew by metis
          then obtain s' where \<open>normal_form S s s'\<close> using ind by blast
          then have \<open>irreducible S s' \<and> rewrite_by_trs S t s'\<close>
            using rewrite_by_trs.rew rewrite_by_trs.trans rew
            unfolding normal_form_def by blast
          then show \<open>\<exists>t'. normal_form S t t'\<close> unfolding normal_form_def by blast
        qed
      qed
    qed
  qed
  then show ?thesis using \<open>ground_term t\<close> by auto
qed

lemma unique_normal_form: \<open>ordered S \<Longrightarrow> confluent S \<Longrightarrow> ground_term t \<Longrightarrow> \<exists>!s. normal_form S t s\<close>
proof -
  assume \<open>ordered S\<close> and conf: \<open>confluent S\<close> and \<open>ground_term t\<close>
  then obtain s where nf_s: \<open>normal_form S t s\<close> using ordered_normalizing by blast
  show \<open>\<exists>!s. normal_form S t s\<close>
  proof
    show \<open>normal_form S t s\<close> using nf_s .
    show \<open>normal_form S t s' \<Longrightarrow> s' = s\<close> for s'
    proof -
      assume nf_s': \<open>normal_form S t s'\<close>
      then consider \<open>s = s'\<close>
        | \<open>rewrite_by_trs S s s'\<close>
        | \<open>rewrite_by_trs S s' s\<close>
        | \<open>rewrite_by_trs S t s' \<and> rewrite_by_trs S t s\<close>
        using nf_s unfolding normal_form_def by auto
      then show \<open>s' = s\<close>
      proof cases
        case 1
        then show ?thesis by auto
      next
        case 2
        then show ?thesis using nf_s unfolding normal_form_def irreducible_def by blast
      next
        case 3
        then show ?thesis using nf_s' unfolding normal_form_def irreducible_def by blast
      next
        case 4
        then obtain u where \<open>normal_form S s u\<close> and \<open>normal_form S s' u\<close>
          using conf \<open>ground_term t\<close> nf_s'
          unfolding equiv_class_of_trs_def confluent_def normal_form_def irreducible_def by blast
        then have \<open>s = u \<and> s' = u\<close> using nf_s nf_s'
          unfolding normal_form_def irreducible_def by auto
        then show ?thesis by auto
      qed
    qed
  qed
qed

lemma equiv_class_refl: \<open>ordered S \<Longrightarrow> refl_on {t. ground_term t} (equiv_class_of_trs S)\<close>
  unfolding equiv_class_of_trs_def refl_on_def
  using ordered_normalizing by auto

lemma equiv_class_sym: \<open>sym (equiv_class_of_trs S)\<close>
  unfolding equiv_class_of_trs_def sym_def by blast

lemma equiv_class_trans: \<open>confluent S \<Longrightarrow> trans (equiv_class_of_trs S)\<close>
  by (smt Pair_inject mem_Collect_eq trans_def equiv_class_of_trs_def normal_form_def confluent_def irreducible_def)

lemma fun_comp_step:
  assumes \<open>confluent S\<close>
      and \<open>(x, y) \<in> equiv_class_of_trs S\<close>
      and \<open>(Fun f (a1 @ x # a2'), Fun f (a1 @ x # a3')) \<in> equiv_class_of_trs S\<close>
    shows \<open>(Fun f (a1 @ x # a2'), Fun f (a1 @ y # a3')) \<in> equiv_class_of_trs S\<close>
proof -
  obtain u where \<open>normal_form S x u\<close>
             and \<open>normal_form S y u\<close>
    using assms(2,3)
    unfolding equiv_class_of_trs_def by auto
  then show ?thesis
    by (metis assms(1,3) confluent_def irreducible_def normal_form_def)
qed

lemma equiv_class_fun_comp:
  assumes \<open>ordered S\<close>
      and \<open>confluent S\<close>
    shows \<open>fun_comp (equiv_class_of_trs S)\<close>
proof -
  have nf: \<open>length a2 = length a3 \<Longrightarrow> (\<forall>t \<in> set a1. ground_term t) \<Longrightarrow> (\<forall>n<length a2. (a2 ! n, a3 ! n) \<in> equiv_class_of_trs S) \<Longrightarrow>
       (Fun f (a1 @ a2), Fun f (a1 @ a3)) \<in> equiv_class_of_trs S\<close> for f a1 a2 a3
  proof (induct a2 arbitrary: a1 a3)
    case Nil
    then have \<open>Fun f (a1 @ []) = Fun f a1 \<and> Fun f (a1 @ a3) = Fun f a1\<close> by auto
    moreover have \<open>ground_term (Fun f a1)\<close> using Nil by auto
    ultimately show ?case using assms(1) ordered_normalizing unfolding equiv_class_of_trs_def by auto
  next
    case (Cons x a2')
    then obtain y a3' where a3_def: \<open>a3 = y # a3'\<close>
      by (metis list.set_cases nth_equalityI nth_mem)
    then have \<open>length a2' = length a3'\<close>
          and equiv: \<open>(x,y) \<in> equiv_class_of_trs S\<close>
          and \<open>\<forall>n<length a2'. (a2' ! n, a3' ! n) \<in> equiv_class_of_trs S\<close> using Cons by auto
    moreover have \<open>\<forall>t \<in> set (a1 @ [x]). ground_term t\<close> using Cons equiv unfolding equiv_class_of_trs_def
      by (smt Pair_inject Un_iff emptyE empty_set insert_iff list.set(2) mem_Collect_eq set_append)
    ultimately have \<open>(Fun f ((a1 @ [x]) @ a2'), Fun f ((a1 @ [x]) @ a3')) \<in> equiv_class_of_trs S\<close> using Cons(1) by blast
    then show ?case using fun_comp_step equiv a3_def assms by auto
  qed
  show ?thesis using nf [of _ _ \<open>[]\<close>] unfolding fun_comp_def by auto
qed

lemma equiv_class_fo: \<open>ordered S \<Longrightarrow> confluent S \<Longrightarrow> Rep_fo_interp (Abs_fo_interp (equiv_class_of_trs S)) = equiv_class_of_trs S\<close>
  using equiv_class_refl equiv_class_sym equiv_class_trans equiv_class_fun_comp Abs_fo_interp_inverse by fast

definition production :: \<open>('f, 'v) trs \<Rightarrow> ('f,'v) ground_clause \<Rightarrow> ('f,'v) interp\<close>
  where \<open>production TRS C = {(t,s) | t s L C'. s \<prec> t
                                             \<and> Rep_ground_clause C = {# L #} + C'
                                             \<and> L = Lit True (Upair t s)
                                             \<and> (\<forall>L' \<in># C'. L' \<prec>L L)
                                             \<and> selection (Rep_ground_clause C) = {#}
                                             \<and> \<not> validate_clause (Abs_fo_interp (equiv_class_of_trs TRS)) (Rep_ground_clause C)
                                             \<and> \<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (insert (t,s) TRS))) C'
                                             \<and> irreducible TRS t}\<close>

context
  fixes N :: \<open>('f,'v) ground_clause set\<close>
begin

function trs_of_clause :: \<open>('f,'v) ground_clause \<Rightarrow> ('f, 'v) trs\<close>
  where
    \<open>trs_of_clause C = (let trs_upto = \<Union>(trs_of_clause ` {B \<in> N. B \<prec>G C})
                        in trs_upto \<union> production trs_upto C)\<close>
  by auto
termination using wf_ground_clause_ord by (rule local.termination [of ground_clause_ord, simplified])

end

definition canonical_interp_ground :: \<open>('f,'v) ground_clause set \<Rightarrow> ('f,'v) fo_interp\<close>
  where \<open>canonical_interp_ground N = Abs_fo_interp (equiv_class_of_trs (\<Union>(trs_of_clause N ` N)))\<close>

definition canonical_interp :: \<open>('f,'v) clause set \<Rightarrow> ('f,'v) fo_interp\<close>
  where \<open>canonical_interp N = canonical_interp_ground (Abs_ground_clause ` N)\<close>

lemma local_rewrite_rel_subset:
  \<open>local_rewrite_by_trs S1 t s \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> local_rewrite_by_trs S2 t s\<close>
  using local_rewrite_by_trs.simps by auto

lemma rewrite_rel_subset:
  \<open>rewrite_by_trs S1 t s \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> rewrite_by_trs S2 t s\<close>
proof -
  assume \<open>rewrite_by_trs S1 t s\<close>
  then show \<open>S1 \<subseteq> S2 \<Longrightarrow> rewrite_by_trs S2 t s\<close>
  proof (induct rule: rewrite_by_trs.induct)
    case (rew S t s)
    then show ?case
      using rewrite_by_trs.rew local_rewrite_rel_subset by blast
  next
    case (trans S u t s)
    then show ?case
      using rewrite_by_trs.trans local_rewrite_rel_subset by blast
  qed
qed

lemma equiv_class_subset:
  \<open>ordered S2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> equiv_class_of_trs S1 \<subseteq> equiv_class_of_trs S2\<close>
proof -
  assume ord: \<open>ordered S2\<close> and subset: \<open>S1 \<subseteq> S2\<close>
  have \<open>(u, v) \<in> equiv_class_of_trs S1 \<Longrightarrow> (u, v) \<in> equiv_class_of_trs S2\<close> for u v
  proof -
    assume \<open>(u, v) \<in> equiv_class_of_trs S1\<close>
    then obtain w where nf_u: \<open>normal_form S1 u w\<close>
                    and nf_v: \<open>normal_form S1 v w\<close>
                    and ground: \<open>ground_term u \<and> ground_term v \<and> ground_term w\<close>
      unfolding equiv_class_of_trs_def
      by (smt Pair_inject mem_Collect_eq normal_form_def ord ordered_trs_preserve_groundness subset subset_eq)
    then obtain w' where \<open>normal_form S2 w w'\<close>
      using ord ordered_normalizing by metis
    then have \<open>normal_form S2 u w' \<and> normal_form S2 v w'\<close>
      using nf_u nf_v rewrite_trans [of S2] ord rewrite_rel_subset subset unfolding normal_form_def by blast
    then show ?thesis using ground unfolding equiv_class_of_trs_def by blast
  qed
  then show ?thesis by auto
qed

lemma ordered_production: \<open>ordered (production N C)\<close>
  unfolding production_def by blast

lemma ground_production: \<open>(lhs, rhs) \<in> production N C \<Longrightarrow> ground_term lhs \<and> ground_term rhs\<close>
proof -
  assume \<open>(lhs, rhs) \<in> production N C\<close>
  then obtain L C C' where L_def: \<open>L = Lit True (Upair lhs rhs)\<close>
                       and \<open>Rep_ground_clause C = {#L#} + C'\<close>
    unfolding production_def by blast
  then have \<open>L \<in># Rep_ground_clause C\<close> by auto
  with L_def show ?thesis using Rep_ground_clause by force
qed

lemma ordered_trs_of_clause: \<open>ordered (trs_of_clause N C)\<close>
proof (rule wf_induct [of "ground_clause_ord"])
  show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord .
next
  show \<open>\<forall>B. B \<prec>G C \<longrightarrow> ordered (trs_of_clause N B) \<Longrightarrow> ordered (trs_of_clause N C)\<close> for C
  proof -
    let ?trs_upto = \<open>\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
    assume \<open>\<forall>B. B \<prec>G C \<longrightarrow> ordered (trs_of_clause N B)\<close>
    then have \<open>ordered ?trs_upto\<close> by blast
    then show ?thesis
      using trs_of_clause.simps [of N C] ordered_production
      by (metis (no_types, lifting) UnE)
  qed
qed

lemma ordered_canonical_trs: \<open>ordered (\<Union> (trs_of_clause N ` N'))\<close>
  using ordered_trs_of_clause by fast

lemma confluent_trs_of_clause: \<open>confluent (trs_of_clause N C)\<close>
  sorry

lemma confluent_canonical_trs: \<open>confluent (\<Union> (trs_of_clause N ` N'))\<close>
  sorry

lemma canonical_interp_fo: \<open>Rep_fo_interp (canonical_interp S) = equiv_class_of_trs (\<Union> (trs_of_clause (Abs_ground_clause ` S) ` Abs_ground_clause ` S))\<close>
  unfolding canonical_interp_def canonical_interp_ground_def
  using equiv_class_fo ordered_canonical_trs confluent_canonical_trs by metis

lemma ex_max_literal: \<open>ground_cl C \<Longrightarrow> C \<noteq> \<bottom>F \<Longrightarrow> (\<exists>L \<in># C. \<forall>L' \<in># C. L' \<preceq>L L)\<close>
proof (induction C rule: multiset_induct)
  case empty (* vacuous case *)
  then show ?case
    using Rep_ground_clause_inject by fastforce
next
  case (add L1 C1)
  then have ground_C1: \<open>ground_cl C1\<close> and ground_L1: \<open>ground_lit L1\<close> by auto
  show \<open>\<exists>L \<in># add_mset L1 C1. \<forall>L' \<in># add_mset L1 C1. L' \<preceq>L L\<close>
  proof (cases C1)
    case empty (* singleton clause *)
    then show ?thesis by auto
  next
    case (add L2 C2)
    with ground_C1 add.IH obtain Lmax where Lmax_elem: \<open>Lmax \<in># C1\<close>
                                        and Lmax_def: \<open>\<forall>L'\<in>#C1. L' \<preceq>L Lmax\<close> by auto
    then consider (a) \<open>Lmax \<prec>L L1\<close> | (b) \<open>L1 \<preceq>L Lmax\<close> using ground_L1 ground_C1 lit_ord_ground_total unfolding total_on_def by blast
    then show ?thesis
    proof cases
      case a
      then have \<open>L'\<in># C1 \<Longrightarrow> L' \<preceq>L L1\<close> for L'
      proof -
        assume \<open>L' \<in># C1\<close>
        then have \<open>L' \<preceq>L Lmax\<close> using Lmax_def by auto
        then show ?thesis using a trans_lit_ord unfolding trans_def by blast
      qed
      moreover have \<open>L1 \<preceq>L L1\<close> using Lmax_def by auto
      ultimately show ?thesis by auto
    next
      case b
      then have \<open>\<forall>L'\<in># add_mset L1 C1. L' \<preceq>L Lmax\<close> using Lmax_def by auto
      then show ?thesis using Lmax_elem by auto
    qed
  qed
qed

lemma local_rewrite_requires_smaller_lhs:
  \<open>local_rewrite_by_trs S t t' \<Longrightarrow> ground_term t \<Longrightarrow> ordered S \<Longrightarrow> \<exists>s s'. (s, s') \<in> S \<and> ground_term s \<and> s \<preceq> t\<close>
proof (induct rule: local_rewrite_by_trs.induct)
  case (eq t s S)
  then show ?case by blast
next
  case (func t s S f a1 a2)
  then obtain u u' where rule_elem: \<open>(u, u') \<in> S\<close>
                     and le: \<open>u \<preceq> t\<close>
                     and ground_u: \<open>ground_term u\<close> by auto
  have \<open>t \<prec> Fun f (a1 @ t # a2) \<and> ground_term t\<close>
    using term_ord_ground_subterm_comp func by auto
  then have \<open>u \<prec> Fun f (a1 @ t # a2)\<close>
    using le term_ord_trans func ground_u unfolding trans_def by blast
  then show ?case using rule_elem ground_u by blast
qed

lemma rewrite_requires_smaller_lhs:
  \<open>rewrite_by_trs S t t' \<Longrightarrow> ground_term t \<Longrightarrow> ordered S \<Longrightarrow> \<exists>s s'. (s, s') \<in> S \<and> ground_term s \<and> s \<preceq> t\<close>
  using rewrite_by_trs.simps local_rewrite_requires_smaller_lhs by blast

(* Lemma 3 (negative literal) *)
lemma production_lhs_greater_neg:
  assumes \<open>(t, s) \<in> production TRS C\<close>
  assumes \<open>Lit False (Upair ul ur) \<in># Rep_ground_clause D\<close>
  assumes \<open>D \<preceq>G C\<close>
  shows \<open>ur \<prec> t \<and> ul \<prec> t\<close>
proof -
  from assms(1) obtain L where L_def: \<open>L = Lit True (Upair t s)\<close>
                           and L_elem: \<open>L \<in># Rep_ground_clause C\<close>
                           and L_max: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L L \<or> L' = L\<close>
                           and lt: \<open>s \<prec> t\<close>
    unfolding production_def by fastforce
  have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term ur \<and> ground_term ul\<close>
    using L_def L_elem assms(2) Rep_ground_clause by force
  show ?thesis
  proof (rule ccontr)
    assume \<open>\<not> (ur \<prec> t \<and> ul \<prec> t)\<close>
    then have \<open>t \<preceq> ur \<or> t \<preceq> ul\<close> using ground term_ord_ground_total unfolding total_on_def by blast
    then consider \<open>(s \<prec> ur \<and> t \<prec> ur) \<or> (s \<prec> ul \<and> t \<prec> ul)\<close> | \<open>s \<prec> ur \<and> t = ur\<close> | \<open>s \<prec> ul \<and> t = ul\<close>
      using lt ground term_ord_trans unfolding trans_def by meson
    then have \<open>({#s, t#}, {#ul, ul, ur, ur#}) \<in> mult term_ord\<close>
    proof cases
      case 1
      then show ?thesis using mult_max [of \<open>{#s, t#}\<close>] by auto
    next
      case 2
      then have \<open>({#s, t#}, add_mset ul {#s, t#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
      also have \<open>add_mset ul {#s, t#} = {#ul, ur#} + {#s#}\<close> using 2 by force
      also have \<open>({#ul, ur#} + {#s#}, add_mset ur {#ul, ur#}) \<in> mult1 term_ord\<close> unfolding mult1_def using 2 by force
      also have \<open>add_mset ur {#ul, ur#} = {#ul, ur, ur#}\<close> by force
      also have \<open>({#ul, ur, ur#}, add_mset ul {#ul, ur, ur#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
      finally show ?thesis unfolding mult_def by blast
    next
      case 3
      then have \<open>({#s, t#}, add_mset ur {#s, t#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
      also have \<open>add_mset ur {#s, t#} = {#ul, ur#} + {#s#}\<close> using 3 by force
      also have \<open>({#ul, ur#} + {#s#}, add_mset ul {#ul, ur#}) \<in> mult1 term_ord\<close> unfolding mult1_def using 3 by force
      also have \<open>({#ul, ul, ur#}, add_mset ur {#ul, ul, ur#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
      also have \<open>add_mset ur {#ul, ul, ur#} = {#ul, ul, ur, ur#}\<close> by force
      finally show ?thesis unfolding mult_def by blast
    qed
    then have \<open>L \<prec>L Lit False (Upair ul ur)\<close> using L_def
      by (smt add_mset_add_single case_prodI inv_image_def lit_ord_def mem_Collect_eq mset_lit.simps mset_upair union_mset_add_mset_left union_mset_add_mset_right)
    then have Neq_gt: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L Lit False (Upair ul ur)\<close>
      using L_max
      by (metis transD trans_lit_ord)
    then have \<open>(Rep_ground_clause C, Rep_ground_clause D) \<in> clause_ord\<close>
      using mult_max assms(2) unfolding clause_ord_def lit_ord_def by fast
    then have \<open>C \<prec>G D\<close> unfolding ground_clause_ord_def using assms(2) by auto
    then show False using assms(3) ground_clause_ord_asymmetric ground_clause_ord_distinct by metis
  qed
qed

(* Lemma 3 (positive literal) *)
lemma production_lhs_greater_pos:
  assumes \<open>(t, s) \<in> production TRS C\<close>
  assumes \<open>Lit True (Upair ul ur) \<in># Rep_ground_clause D\<close>
  assumes \<open>D \<preceq>G C\<close>
  shows \<open>ur \<preceq> t \<and> ul \<preceq> t\<close>
proof -
  from assms(1) obtain L where L_def: \<open>L = Lit True (Upair t s)\<close>
                           and L_elem: \<open>L \<in># Rep_ground_clause C\<close>
                           and L_max: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L L \<or> L' = L\<close>
                           and lt: \<open>s \<prec> t\<close>
    unfolding production_def by fastforce
  have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term ur \<and> ground_term ul\<close>
    using L_def L_elem assms(2) Rep_ground_clause by force
  show ?thesis
  proof (rule ccontr)
    assume \<open>\<not> (ur \<preceq> t \<and> ul \<preceq> t)\<close>
    then have \<open>t \<prec> ur \<or> t \<prec> ul\<close> using ground term_ord_ground_total unfolding total_on_def by blast
    then have \<open>(s \<prec> ur \<and> t \<prec> ur) \<or> (s \<prec> ul \<and> t \<prec> ul)\<close>
      using lt ground term_ord_trans unfolding trans_def by auto
    then have \<open>({#s, t#}, {#ul, ur#}) \<in> mult term_ord\<close>
      using mult_max [of \<open>{#s, t#}\<close>] by auto
    then have \<open>L \<prec>L Lit True (Upair ul ur)\<close> using L_def
      by (simp add: add_mset_commute lit_ord_def)
    then have Eq_gt: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L Lit True (Upair ul ur)\<close>
      using L_max
      by (metis transD trans_lit_ord)
    then have \<open>(Rep_ground_clause C, Rep_ground_clause D) \<in> clause_ord\<close>
      using mult_max assms(2) unfolding clause_ord_def lit_ord_def by fast
    then have \<open>C \<prec>G D\<close> unfolding ground_clause_ord_def using assms(2) by auto
    then show False using assms(3) ground_clause_ord_asymmetric ground_clause_ord_distinct by metis
  qed
qed

lemma ex_productive_clause:
  \<open>D \<in> N \<longrightarrow> (t, s) \<in> trs_of_clause N D \<longrightarrow> (\<exists>C \<in> N. C \<preceq>G D \<and> (t, s) \<in> production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C)\<close> (is \<open>?P D\<close>)
proof (rule wf_induct [of "ground_clause_ord"])
  show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord .
next
  show \<open>\<forall>D'. D' \<prec>G D \<longrightarrow> ?P D' \<Longrightarrow> ?P D\<close> for D
  proof -
    assume ind_hyp: \<open>\<forall>D'. D' \<prec>G D \<longrightarrow> ?P D'\<close>
    have \<open>D \<in> N \<Longrightarrow> (t, s) \<in> trs_of_clause N D \<Longrightarrow> (\<exists>C\<in>N. C \<preceq>G D \<and> (t, s) \<in> production (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) C)\<close>
    proof -
      let ?trs_upto = \<open>\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close>
      assume D_elem: \<open>D \<in> N\<close> and \<open>(t, s) \<in> trs_of_clause N D\<close>
      then consider (prod) \<open>(t, s) \<in> production ?trs_upto D\<close> | (lt) \<open>(t, s) \<in> ?trs_upto\<close>
        using trs_of_clause.simps
        by (metis (mono_tags, lifting) UnE)
      then show \<open>\<exists>C\<in>N. C \<preceq>G D \<and> (t, s) \<in> production (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close>
      proof cases
        case prod
        then show ?thesis using D_elem by blast
      next
        case lt
        then obtain D' where \<open>D' \<in> N\<close> and D'_lt: \<open>D' \<prec>G D\<close> and \<open>(t, s) \<in> trs_of_clause N D'\<close> by blast
        with ind_hyp obtain C where C_elem: \<open>C \<in> N\<close>
                                and C_le: \<open>C \<preceq>G D'\<close>
                                and rule_elem: \<open>(t, s) \<in> production (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close> by blast
        have \<open>C \<prec>G D\<close> using D'_lt C_le trans_ground_clause_ord unfolding trans_def by blast
        then show ?thesis using C_elem rule_elem by blast
      qed
    qed
    then show ?thesis by blast
  qed
qed

(* rewrite rules with a LHS larger than t do not affect rewriting of t *)
lemma lhs_gt_no_local_rewrite:
  assumes \<open>local_rewrite_by_trs TRS2 t u\<close>
      and \<open>ordered TRS2\<close>
      and \<open>TRS1 \<subseteq> TRS2\<close>
      and \<open>(\<forall>lhs rhs. (lhs, rhs) \<in> TRS2 - TRS1 \<longrightarrow> t \<prec> lhs)\<close>
      and \<open>ground_term t\<close>
    shows \<open>local_rewrite_by_trs TRS1 t u\<close>
proof -
  have no_rewrite: \<open>local_rewrite_by_trs TRS2 t' u \<Longrightarrow> ordered TRS2 \<Longrightarrow> TRS1 \<subseteq> TRS2 \<Longrightarrow> (\<forall>lhs rhs. (lhs, rhs) \<in> TRS2 - TRS1 \<longrightarrow> t \<prec> lhs) \<Longrightarrow> ground_term t' \<Longrightarrow> t' \<preceq> t \<Longrightarrow> local_rewrite_by_trs TRS1 t' u\<close> for t'
  proof (induct rule: local_rewrite_by_trs.induct)
    case (eq t' s' TRS)
    then show ?case
      by (meson DiffI local_rewrite_by_trs.eq wf_not_sym wf_term_ord)
  next
    case (func t' s' TRS f a1 a2)
    then show ?case
      by (meson DiffI local_rewrite_by_trs.func term_ord_ground_subterm_comp term_ord_trans transD wf_not_sym wf_term_ord)
  qed
  then show ?thesis using assms by blast
qed

lemma lhs_gt_no_rewrite:
  assumes \<open>rewrite_by_trs TRS2 t u\<close>
      and \<open>ordered TRS2\<close>
      and \<open>TRS1 \<subseteq> TRS2\<close>
      and \<open>(\<forall>lhs rhs. (lhs, rhs) \<in> TRS2 - TRS1 \<longrightarrow> t \<prec> lhs)\<close>
      and \<open>ground_term t\<close>
    shows \<open>rewrite_by_trs TRS1 t u\<close>
proof -
  have \<open>rewrite_by_trs TRS2 t u \<Longrightarrow> ordered TRS2 \<Longrightarrow> TRS1 \<subseteq> TRS2 \<Longrightarrow> (\<forall>lhs rhs. (lhs, rhs) \<in> TRS2 - TRS1 \<longrightarrow> t \<prec> lhs) \<Longrightarrow> ground_term t \<Longrightarrow> rewrite_by_trs TRS1 t u\<close>
  proof (induct rule: rewrite_by_trs.induct)
    case (rew S t s)
    then have \<open>local_rewrite_by_trs TRS1 t s\<close> using lhs_gt_no_local_rewrite by blast
    then show ?case
      using rewrite_by_trs.rew by blast
  next
    case (trans S u t s)
    then have \<open>local_rewrite_by_trs TRS1 u t\<close> using lhs_gt_no_local_rewrite by blast
    moreover have \<open>rewrite_by_trs TRS1 t s\<close>
      by (metis (mono_tags, lifting) transD trans(1,3-7) ordered_local_rewriting ordered_trs_preserve_groundness_local term_ord_trans)
    ultimately show ?case 
      using rewrite_by_trs.trans by blast
  qed
  then show ?thesis using assms by auto
qed

lemma negative_literal_normalized:
  assumes \<open>C \<in> N\<close>
  assumes \<open>Lit False (Upair s t) \<in># Rep_ground_clause C\<close>
  assumes \<open>normal_form (\<Union>(trs_of_clause N ` N)) s u \<or> (\<exists>D \<in> N. C \<prec>G D \<and> normal_form (trs_of_clause N D) s u)\<close>
  shows \<open>normal_form (trs_of_clause N C) s u\<close>
  unfolding normal_form_def
proof
  consider (a) \<open>normal_form (\<Union>(trs_of_clause N ` N)) s u\<close>
         | (b) \<open>\<exists>D \<in> N. C \<prec>G D \<and> normal_form (trs_of_clause N D) s u\<close>
    using assms(3) ..
  then show \<open>irreducible (trs_of_clause N C) u\<close>
  proof cases
    case a
    then show ?thesis using assms(1)
      by (meson Sup_upper image_iff irreducible_def normal_form_def rewrite_rel_subset)
  next
    case b
    then obtain D where nf: \<open>normal_form (trs_of_clause N D) s u\<close>
                    and \<open>D \<in> N\<close>
                    and \<open>C \<prec>G D\<close> by blast
    then have \<open>trs_of_clause N C \<subseteq> trs_of_clause N D\<close>
      by (smt UN_I UnCI assms(1) mem_Collect_eq subsetI superposition.trs_of_clause.simps superposition_axioms)
    then show ?thesis using assms(1) nf
      by (meson irreducible_def normal_form_def rewrite_rel_subset)
  qed
next
  consider (eq) \<open>u = s\<close> | (rew) \<open>rewrite_by_trs (\<Union>(trs_of_clause N ` N)) s u \<or> (\<exists>D \<in> N. C \<prec>G D \<and> rewrite_by_trs (trs_of_clause N D) s u)\<close>
    using assms(3) unfolding normal_form_def by blast
  then show \<open>u = s \<or> rewrite_by_trs (trs_of_clause N C) s u\<close>
  proof cases
    case eq
    then show ?thesis by blast
  next
    case rew
    have \<open>ground_term s\<close> using assms(2) Rep_ground_clause by fastforce
    (* rewriting rules outside of trs_of_clause N C have a LHS that is larger than the term to rewrite *)
    have lhs_gt: \<open>(lhs, rhs) \<in> \<Union>(trs_of_clause N ` N) - trs_of_clause N C \<Longrightarrow> s \<prec> lhs\<close> for lhs rhs
    proof -
      assume rule_elem: \<open>(lhs, rhs) \<in> \<Union>(trs_of_clause N ` N) - trs_of_clause N C\<close>
      then obtain B where \<open>B \<in> N\<close> and \<open>(lhs, rhs) \<in> trs_of_clause N B\<close> by blast
      then obtain B' where B'_elem: \<open>B' \<in> N\<close> and rule_elem': \<open>(lhs, rhs) \<in> production (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G B'})) B'\<close>
        using ex_productive_clause by blast
      then have rule_elem'': \<open>(lhs, rhs) \<in> trs_of_clause N B'\<close>
        by (smt Collect_cong Un_iff superposition.trs_of_clause.simps superposition_axioms)
      have C_lt: \<open>C \<prec>G B'\<close>
      proof (rule ccontr)
        assume \<open>\<not> C \<prec>G B'\<close>
        then consider (lt) \<open>B' \<prec>G C\<close> | (eq) \<open>B' = C\<close> using ground_clause_ord_total unfolding total_on_def by blast
        then have \<open>(lhs, rhs) \<in> trs_of_clause N C\<close>
        proof cases
          case lt
          then have \<open>(lhs, rhs) \<in> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close> using B'_elem rule_elem'' by blast
          then show ?thesis using trs_of_clause.simps [of N C]
            by (metis (no_types, lifting) UnCI)
        next
          case eq
          then show ?thesis using rule_elem'' by blast
        qed
        then show False using rule_elem by blast
      qed
      then show ?thesis using production_lhs_greater_neg rule_elem' assms(2) by blast
    qed
    (* combine with the previous lemma to conclude *)
    consider (a) \<open>rewrite_by_trs (\<Union>(trs_of_clause N ` N)) s u\<close>
           | (b) \<open>\<exists>D \<in> N. C \<prec>G D \<and> rewrite_by_trs (trs_of_clause N D) s u\<close>
      using rew ..
    then show ?thesis
    proof cases
      case a
      have \<open>ordered (\<Union> (trs_of_clause N ` N))\<close>
        using ordered_trs_of_clause by blast
      then show ?thesis
        using a lhs_gt lhs_gt_no_rewrite [of \<open>\<Union>(trs_of_clause N ` N)\<close> s u \<open>trs_of_clause N C\<close>] \<open>ground_term s\<close> assms(1)
        unfolding normal_form_def by blast
    next
      case b
      then obtain D where rew_s_u: \<open>rewrite_by_trs (trs_of_clause N D) s u\<close>
                      and D_elem: \<open>D \<in> N\<close>
                      and D_gt: \<open>C \<prec>G D\<close> by blast
      then have \<open>(lhs, rhs) \<in> trs_of_clause N D - trs_of_clause N C \<Longrightarrow> s \<prec> lhs\<close> for lhs rhs using lhs_gt by blast
      moreover have \<open>trs_of_clause N C \<subseteq> trs_of_clause N D\<close> using assms(1) D_elem D_gt
        by (smt UN_I Un_iff mem_Collect_eq subrelI trs_of_clause.simps)
      ultimately show ?thesis
        using rew_s_u lhs_gt_no_rewrite [of \<open>trs_of_clause N D\<close> s u \<open>trs_of_clause N C\<close>] \<open>ground_term s\<close> assms(1) ordered_trs_of_clause [of N D]
        unfolding normal_form_def by blast
    qed
  qed
qed

lemma positive_literal_normalized:
  assumes \<open>C \<in> N\<close>
  assumes \<open>C \<prec>G D\<close>
  assumes \<open>D \<in> N\<close>
  assumes \<open>(s, t) \<notin> equiv_class_of_trs (trs_of_clause N C)\<close>
  assumes \<open>Lit True (Upair s t) \<in># Rep_ground_clause C\<close>
  assumes \<open>normal_form (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})) s u\<close>
  shows \<open>normal_form (trs_of_clause N C) s u\<close>
  unfolding normal_form_def
proof
  show \<open>irreducible (trs_of_clause N C) u\<close>
  proof -
    have \<open>irreducible (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})) u\<close>
      using assms(6) unfolding normal_form_def by blast
    moreover have \<open>trs_of_clause N C \<subseteq> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close>
      using assms(1,2) by blast
    ultimately show ?thesis using rewrite_rel_subset unfolding irreducible_def by blast
  qed
next
  consider (eq) \<open>u = s\<close> | (rew) \<open>rewrite_by_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})) s u\<close>
    using assms(6) unfolding normal_form_def by blast
  then show \<open>u = s \<or> rewrite_by_trs (trs_of_clause N C) s u\<close>
  proof cases
    case eq
    then show ?thesis by blast
  next
    case rew
    show ?thesis
    proof -
      have lhs_gt: \<open>(lhs, rhs) \<in> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D}) - trs_of_clause N C \<Longrightarrow> s \<prec> lhs\<close> for lhs rhs
      proof -
        assume rule_elem: \<open>(lhs, rhs) \<in> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D}) - trs_of_clause N C\<close>
        then have \<open>(lhs, rhs) \<in> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close> by blast
        then obtain D' where rule_elem': \<open>(lhs, rhs) \<in> production (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D'})) D'\<close> and D'_elem: \<open>D' \<in> N\<close>
          using ex_productive_clause assms(3) by blast
        have \<open>C \<preceq>G D'\<close>
        proof (rule ccontr)
          assume \<open>\<not> C \<preceq>G D'\<close>
          then have D'_lt: \<open>D' \<prec>G C\<close>
            using ground_clause_ord_total unfolding total_on_def by blast
          have \<open>(lhs, rhs) \<in> trs_of_clause N D'\<close>
            using trs_of_clause.simps [of N D'] rule_elem'
            by (metis (no_types, lifting) Un_iff)
          then have \<open>(lhs, rhs) \<in> trs_of_clause N C\<close> using D'_lt D'_elem trs_of_clause.simps [of N C]
            by (metis (no_types, lifting) UN_I Un_iff mem_Collect_eq)
          then show False using rule_elem by blast
        qed
        then have \<open>s \<preceq> lhs \<and> t \<preceq> lhs\<close>
          using production_lhs_greater_pos [of lhs rhs \<open>\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D'})\<close> D'] rule_elem' assms(5) by blast
        moreover have \<open>s \<noteq> lhs\<close>
        proof
          assume \<open>s = lhs\<close>
          then have \<open>irreducible (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D'})) s\<close>
            using rule_elem' unfolding production_def by blast
          then have \<open>irreducible (trs_of_clause N C) s\<close> sorry
          then have \<open>s = t\<close> sorry
          then show False sorry
        qed
        ultimately show ?thesis sorry
      qed
      moreover have \<open>trs_of_clause N C \<subseteq> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close>
        using assms(1,2) by blast
      moreover have \<open>ordered (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D}))\<close>
        using ordered_trs_of_clause by blast
      moreover have \<open>ground_term s\<close>
        using assms(5) Rep_ground_clause [of C] by auto
      ultimately show ?thesis using rew lhs_gt_no_rewrite [of \<open>\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close> s u \<open>trs_of_clause N C\<close>] by blast
    qed
  qed
qed

(* during the construction of the model, a clause that is valid at some point will not be falsified later *)
(* Corollary 4 *)
lemma model_construction_monotonic:
  assumes \<open>C \<in> N\<close>
  assumes \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Rep_ground_clause C)\<close> (is \<open>?valid_upto C\<close>)
  shows \<open>(\<forall>D \<in> N. C \<prec>G D \<longrightarrow> validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N D))) (Rep_ground_clause C)) \<and>
         validate_clause (canonical_interp_ground N) (Rep_ground_clause C)\<close> (is \<open>?valid C\<close>)
proof -
  have \<open>C \<in> N \<longrightarrow> ?valid_upto C \<longrightarrow> ?valid C\<close>
  proof (rule wf_induct [of \<open>ground_clause_ord\<close>])
    show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord by auto
  next
    show \<open>\<forall>B. B \<prec>G C \<longrightarrow> B \<in> N \<longrightarrow> ?valid_upto B \<longrightarrow> ?valid B \<Longrightarrow> C \<in> N \<longrightarrow> ?valid_upto C \<longrightarrow> ?valid C\<close> for C
    proof -
      assume ind: \<open>\<forall>B. B \<prec>G C \<longrightarrow> B \<in> N \<longrightarrow> ?valid_upto B \<longrightarrow> ?valid B\<close>
      have \<open>C \<in> N \<Longrightarrow> ?valid_upto C \<Longrightarrow> ?valid C\<close>
      proof -
        assume C_elem: \<open>C \<in> N\<close>
           and valid_upto_C: \<open>?valid_upto C\<close>
        from ex_ground_instance obtain \<sigma> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>)\<close>
          by fast
        with valid_upto_C obtain L where L_elem: \<open>L \<in># Rep_ground_clause C\<close>
                                     and \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (subst_apply_lit L \<sigma>)\<close>
          unfolding validate_clause_def by blast
        then have valid_L: \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) L\<close>
          using subst_ground_lit [of L \<sigma>] Rep_ground_clause [of C] by (smt mem_Collect_eq)
        have valid_L' :\<open>(\<forall>D \<in> N . C \<prec>G D \<longrightarrow> validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N D))) L) \<and> validate_ground_lit (canonical_interp_ground N) L\<close>
        proof (cases L rule: literal_exhaust_2)
          case (Pos s t)
          (* The literal that makes the clause true is positive. It will remain true since rules are only be added to the TRS *)
          with valid_L have \<open>(s, t) \<in> Rep_fo_interp (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C)))\<close>
            using validate_ground_lit.simps by (metis Upair.abs_eq validate_eq.abs_eq)
          then have st_elem: \<open>(s, t) \<in> equiv_class_of_trs (trs_of_clause N C)\<close>
            using equiv_class_fo ordered_trs_of_clause confluent_trs_of_clause by metis
          moreover have \<open>\<forall>D \<in> N. C \<prec>G D \<longrightarrow> trs_of_clause N C \<subseteq> trs_of_clause N D\<close> using C_elem
            by (smt UN_I Un_iff mem_Collect_eq subsetI trs_of_clause.simps)
          ultimately have st_elem': \<open>\<forall>D \<in> N. C \<prec>G D \<longrightarrow> (s, t) \<in> equiv_class_of_trs (trs_of_clause N D)\<close>
            using equiv_class_subset ordered_trs_of_clause [of N] by (meson subsetD)
          from st_elem C_elem have st_elem'': \<open>(s, t) \<in> equiv_class_of_trs (\<Union> (trs_of_clause N ` N))\<close>
            using equiv_class_subset ordered_canonical_trs [of N]
            by (smt confluent_canonical_trs confluent_def confluent_trs_of_clause equiv_class_of_trs_def irreducible_def mem_Collect_eq normal_form_def unique_normal_form)
          show ?thesis unfolding canonical_interp_ground_def using Pos st_elem' st_elem''
            by (metis Upair.abs_eq equiv_class_fo ordered_canonical_trs confluent_canonical_trs ordered_trs_of_clause confluent_trs_of_clause validate_eq.abs_eq validate_ground_lit.simps)
        next
          case (Neg s t)
          (* Rules added later cannot be used to rewrite terms occurring in a negative literal *)
          with valid_L have \<open>(s, t) \<notin> Rep_fo_interp (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C)))\<close>
            using validate_ground_lit.simps by (metis Upair.abs_eq validate_eq.abs_eq)
          then have s_t_not_elem: \<open>(s, t) \<notin> equiv_class_of_trs (trs_of_clause N C)\<close>
            using equiv_class_fo ordered_trs_of_clause confluent_trs_of_clause by metis
          show ?thesis
          proof -
            have \<open>D \<in> N \<Longrightarrow> C \<prec>G D \<Longrightarrow> validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N D))) L\<close> for D
            proof -
              assume D_elem: \<open>D \<in> N\<close> and D_gt: \<open>C \<prec>G D\<close>
              have \<open>normal_form (trs_of_clause N D) s u \<Longrightarrow> normal_form (trs_of_clause N C) s u\<close> for u
                using negative_literal_normalized Neg L_elem C_elem D_elem D_gt
                by (metis (full_types))
              moreover have \<open>normal_form (trs_of_clause N D) t u \<Longrightarrow> normal_form (trs_of_clause N C) t u\<close> for u
                using negative_literal_normalized Neg L_elem C_elem D_elem D_gt Upair_inject [of s t t s]
                by (metis (full_types))
              ultimately have \<open>(s, t) \<notin> equiv_class_of_trs (trs_of_clause N D)\<close>
                using s_t_not_elem
                unfolding equiv_class_of_trs_def by blast
              then show ?thesis using Neg
                by (metis Upair.abs_eq equiv_class_fo ordered_trs_of_clause confluent_trs_of_clause validate_eq.abs_eq validate_ground_lit.simps)
            qed
            moreover have \<open>validate_ground_lit (canonical_interp_ground N) L\<close>
            proof -
              have \<open>normal_form (\<Union>(trs_of_clause N ` N)) s u \<Longrightarrow> normal_form (trs_of_clause N C) s u\<close> for u
                using negative_literal_normalized Neg L_elem C_elem
                by (metis (full_types))
              moreover have \<open>normal_form (\<Union>(trs_of_clause N ` N)) t u \<Longrightarrow> normal_form (trs_of_clause N C) t u\<close> for u
                using negative_literal_normalized Neg L_elem C_elem Upair_inject [of s t t s]
                by (metis (full_types))
              ultimately have \<open>(s, t) \<notin> equiv_class_of_trs (\<Union> (trs_of_clause N ` N))\<close>
                using s_t_not_elem unfolding equiv_class_of_trs_def by blast
              then have \<open>(s, t) \<notin> Rep_fo_interp (canonical_interp_ground N)\<close>
                unfolding canonical_interp_ground_def
                using equiv_class_fo ordered_canonical_trs confluent_canonical_trs by presburger
              then show ?thesis using Neg
                by (simp add: Upair.abs_eq validate_eq.abs_eq)
            qed
            ultimately show ?thesis by blast
          qed
        qed
        moreover have \<open>subst_apply_lit L \<sigma> = L\<close> for \<sigma> using L_elem Rep_ground_clause subst_ground_lit by fast
        ultimately show ?thesis using L_elem  unfolding validate_clause_def by metis
      qed
      then show ?thesis by blast
    qed
  qed
  then show ?thesis using assms by blast
qed

lemma eql_in_equiv_class:
  \<open>ordered TRS \<Longrightarrow> ground_term s \<Longrightarrow> ground_term t \<Longrightarrow> s = t \<or> (t, s) \<in> TRS \<or> (s, t) \<in> TRS \<Longrightarrow> (t, s) \<in> equiv_class_of_trs TRS\<close>
proof -
  assume ord: \<open>ordered TRS\<close>
     and ground_s: \<open>ground_term s\<close>
     and ground_t: \<open>ground_term t\<close>
     and \<open>s = t \<or> (t, s) \<in> TRS \<or> (s, t) \<in> TRS\<close>
  then consider (eq) \<open>s = t\<close> | (left) \<open>(t, s) \<in> TRS\<close> | (right) \<open>(s, t) \<in> TRS\<close> by blast
  then show \<open>(t, s) \<in> equiv_class_of_trs TRS\<close>
  proof cases
    case eq
    then show ?thesis
      unfolding equiv_class_of_trs_def
      using ord ordered_normalizing ground_s ground_t by fast
  next
    case left
    with ord ordered_normalizing obtain s' where \<open>normal_form TRS s s'\<close> using ground_s by blast
    then have \<open>rewrite_by_trs TRS t s' \<and> irreducible TRS s' \<and> (s' = s \<or> rewrite_by_trs TRS s s')\<close>
      using left local_rewrite_by_trs.eq rewrite_by_trs.trans rew
      unfolding normal_form_def by fast
    then show ?thesis using ground_s ground_t unfolding equiv_class_of_trs_def normal_form_def by blast
  next
    case right
    with ord ordered_normalizing obtain t' where \<open>normal_form TRS t t'\<close> using ground_t by blast
    then have \<open>rewrite_by_trs TRS s t' \<and> irreducible TRS t' \<and> (t' = t \<or> rewrite_by_trs TRS t t')\<close>
      using right local_rewrite_by_trs.eq rewrite_by_trs.trans rew
      unfolding normal_form_def by fast
    then show ?thesis using ground_s ground_t unfolding equiv_class_of_trs_def normal_form_def by blast
  qed
qed

(* Corollary 5 *)
lemma productive_clause_satisfied:
  assumes \<open>production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C \<noteq> {}\<close>
  shows \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Rep_ground_clause C)\<close>
proof -
  from assms obtain t s where ts_elem: \<open>(t, s) \<in> production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close> by fast
  then obtain L C' where L_def: \<open>L = Lit True (Upair t s)\<close>
                     and C_def: \<open>Rep_ground_clause C = {# L #} + C'\<close> unfolding production_def by blast
  from ts_elem have rewrite: \<open>(t, s) \<in> trs_of_clause N C\<close>
    by (metis (no_types, lifting) Un_iff trs_of_clause.simps)
  from C_def have L_elem: \<open>L \<in># Rep_ground_clause C\<close> by auto
  then have L_ground: \<open>ground_lit L\<close> using C_def Rep_ground_clause by fast
  then have \<open>ground_term s \<and> ground_term t\<close> using L_def by force
  then have \<open>(t, s) \<in> equiv_class_of_trs (trs_of_clause N C)\<close>
    using rewrite eql_in_equiv_class ordered_trs_of_clause by presburger
  then have \<open>validate_eq (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Upair t s)\<close>
    unfolding validate_eq_def map_fun_def id_def comp_def
    using equiv_class_fo ordered_trs_of_clause confluent_trs_of_clause
    by (metis validate_eq.abs_eq validate_eq.rep_eq Uprod.Upair.abs_eq)
  then have \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) L\<close>
    using L_def validate_ground_lit.simps(1) by metis
  then show ?thesis
    using L_elem L_ground subst_ground_lit
    unfolding validate_clause_def by metis
qed

lemma productive_clause_remainder:
  assumes \<open>(t,s) \<in> production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close>
      and \<open>Rep_ground_clause C = {#Lit True (Upair t s)#} + C'\<close>
      and \<open>C \<prec>G D\<close>
      and \<open>C \<in> N\<close>
      and \<open>D \<in> N\<close>
    shows \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})))) C'\<close>
proof -
  let ?trs_upto = \<open>\<lambda>C. \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
  from assms(1) obtain L' C'' where C''_nvalid: \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (insert (t, s) (?trs_upto C)))) C''\<close>
                                and C_nvalid: \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (?trs_upto C))) (Rep_ground_clause C)\<close>
                                and C_def: \<open>Rep_ground_clause C = {#L'#} + C''\<close>
                                and L'_max: \<open>\<forall>L''\<in>#C''. L'' \<prec>L L'\<close>
                                and L'_def: \<open>L' = Lit True (Upair t s)\<close>
                                and ord: \<open>s \<prec> t\<close>
                                and s_t_ground: \<open>ground_term s \<and> ground_term t\<close>
    using ground_production
    unfolding production_def by blast
  have \<open>C' = C''\<close>
    using assms(2) L'_def C_def by auto
  moreover have \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (?trs_upto D))) C''\<close>
  proof
    assume \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (?trs_upto D))) C''\<close>
    moreover have \<open>ground_cl (subst_apply_cl C'' Var)\<close>
      using C_def ground_subclause subst_ground_cl [of C''] by metis
    (* consider the literal M that makes the clause true *)
    ultimately obtain M where M_elem: \<open>M \<in># C''\<close>
                          and \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (?trs_upto D))) (subst_apply_lit M Var)\<close>
      unfolding validate_clause_def by blast
    moreover have subst_M: \<open>subst_apply_lit M \<sigma> = M\<close> for \<sigma>
      using subst_ground_lit ground_subclause C_def M_elem by fast
    ultimately have valid_M: \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (?trs_upto D))) M\<close>
      by metis
    have \<open>ground_cl C''\<close> using C_def ground_subclause by blast
    then have nvalid_M: \<open>\<not> validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (insert (t, s) (?trs_upto C)))) M\<close>
      using C''_nvalid subst_M M_elem unfolding validate_clause_def
      by (metis (no_types, lifting))
    have M_elem': \<open>M \<in># Rep_ground_clause C\<close>
      using M_elem C_def by auto
    then have nvalid_M_2: \<open>\<not> validate_ground_lit (Abs_fo_interp (equiv_class_of_trs (?trs_upto C))) M\<close>
      using C_nvalid C_def subst_M unfolding validate_clause_def
      by (metis (no_types, lifting))
    show False
    proof (cases M rule: literal_exhaust_2)
      case (Pos u v)
      then have \<open>validate_eq (Abs_fo_interp (equiv_class_of_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D})))) (Upair u v)\<close>
        using valid_M validate_ground_lit.simps
        by (metis (no_types, lifting))
      then have \<open>(u, v) \<in> equiv_class_of_trs (?trs_upto D)\<close>
        by (metis (no_types, lifting) UN_E Upair.abs_eq equiv_class_fo ordered_trs_of_clause confluent_trs_of_clause confluent_canonical_trs validate_eq.abs_eq)
      then obtain u' where nf_u: \<open>normal_form (?trs_upto D) u u'\<close>
                       and nf_v: \<open>normal_form (?trs_upto D) v u'\<close>
                       and u_v_ground: \<open>ground_term u \<and> ground_term v\<close>
        unfolding equiv_class_of_trs_def by blast
      have \<open>(lhs, rhs) \<in> ?trs_upto D - insert (t, s) (?trs_upto C) \<Longrightarrow> u \<prec> lhs \<and> v \<prec> lhs\<close> for lhs rhs
      proof -
        assume \<open>(lhs, rhs) \<in> ?trs_upto D - insert (t, s) (?trs_upto C)\<close>
        then obtain D' where rule_elem: \<open>(lhs, rhs) \<in> trs_of_clause N D'\<close>
                         and \<open>D' \<in> N\<close>
                         and \<open>D' \<prec>G D\<close>
                         and rule_nelem: \<open>(lhs, rhs) \<notin> insert (t, s) (?trs_upto C)\<close> by fast
        then obtain D'' where \<open>(lhs, rhs) \<in> production (?trs_upto D'') D''\<close>
                          and \<open>D'' \<preceq>G D'\<close>
                          and D''_elem: \<open>D'' \<in> N\<close> using ex_productive_clause by meson
        then have \<open>(lhs, rhs) \<in> trs_of_clause N D''\<close> using trs_of_clause.simps [of N D'']
          by (metis (no_types, lifting) Un_iff)
        then have \<open>\<not> D'' \<prec>G C\<close> using rule_nelem D''_elem by blast
        then consider (eq) \<open>C = D''\<close> | (gt) \<open>C \<prec>G D''\<close>
          using ground_clause_ord_total unfolding total_on_def by blast
        then show \<open>u \<prec> lhs \<and> v \<prec> lhs\<close>
        proof cases
          case eq
          then show ?thesis sorry
        next
          case gt
          then show ?thesis sorry
        qed
      qed
      have \<open>rewrite_by_trs (?trs_upto D) u u' \<Longrightarrow> rewrite_by_trs (insert (t, s) (?trs_upto C)) u u'\<close>
      proof -
        assume \<open>rewrite_by_trs (?trs_upto D) u u'\<close>
        then show \<open>rewrite_by_trs (insert (t, s) (?trs_upto C)) u u'\<close>
        proof (induct)
          case (rew S t s)
          then show ?case sorry
        next
          case (trans S u t s)
          then show ?case sorry
        qed
      qed
      then have \<open>ground_term u'\<close> using u_v_ground
        by (metis (no_types, lifting) UN_E nf_u normal_form_def ordered_trs_of_clause ordered_trs_preserve_groundness)
      moreover have \<open>ordered (insert (t, s) (?trs_upto C))\<close> using ord ordered_trs_of_clause by blast
      ultimately obtain u'' where \<open>normal_form (insert (t, s) (?trs_upto C)) u' u''\<close> using ordered_normalizing by blast
      have \<open>normal_form (insert (t, s) (?trs_upto C)) u u'' \<and> normal_form (insert (t, s) (?trs_upto C)) v u''\<close> sorry
      then show False using nvalid_M Pos u_v_ground validate_ground_lit.simps(1) unfolding equiv_class_of_trs_def sorry
    next
      case (Neg u v)
      with nvalid_M_2 have \<open>(u, v) \<in> equiv_class_of_trs (?trs_upto C)\<close> 
        by (metis (no_types, lifting) Upair.abs_eq confluent_canonical_trs equiv_class_fo ordered_canonical_trs validate_eq.abs_eq validate_ground_lit.simps)
      moreover have \<open>?trs_upto C \<subseteq> ?trs_upto D\<close>
        using assms(3,4,5)
        by (smt UN_least UN_upper mem_Collect_eq transE trans_ground_clause_ord)
      moreover have \<open>ordered (?trs_upto D)\<close>
        using ordered_trs_of_clause by blast
      ultimately have \<open>(u, v) \<in> equiv_class_of_trs (?trs_upto D)\<close>
        using assms(4,5) equiv_class_subset [of \<open>?trs_upto D\<close> \<open>?trs_upto C\<close>] by blast
      then show False using valid_M Neg validate_ground_lit.simps
        by (metis (no_types, lifting) Upair.abs_eq \<open>ordered (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G D}))\<close> confluent_canonical_trs equiv_class_fo validate_eq.abs_eq)
    qed
  qed
  ultimately show \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs (?trs_upto D))) C'\<close> by blast
qed

(* Theorem 6 *)
lemma model_construction:
  assumes \<open>saturated N\<close>
  assumes \<open>\<bottom>G \<notin> N\<close>
  assumes \<open>C \<in> N\<close>
  shows \<open>(production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C = {} \<longleftrightarrow> validate_clause (Abs_fo_interp (equiv_class_of_trs (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})))) (Rep_ground_clause C))
         \<and> validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Rep_ground_clause C)\<close> (is \<open>(?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C\<close>)
proof -
  have \<open>C \<in> N \<longrightarrow> ((?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C)\<close>
  proof (rule wf_induct [of \<open>ground_clause_ord\<close>])
    show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord .
  next
    show \<open>\<forall>B. B \<prec>G C \<longrightarrow> B \<in> N \<longrightarrow> ((?P1 B \<longleftrightarrow> ?P2 B) \<and> ?P3 B) \<Longrightarrow> C \<in> N \<longrightarrow> ((?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C)\<close> for C
    proof -
      let ?trs_upto = \<open>\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
      assume ind: \<open>\<forall>B. B \<prec>G C \<longrightarrow> B \<in> N \<longrightarrow> ((?P1 B \<longleftrightarrow> ?P2 B) \<and> ?P3 B)\<close>
      show \<open>C \<in> N \<longrightarrow> ((?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C)\<close>
      proof
        assume C_elem: \<open>C \<in> N\<close>
        show \<open>(?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C\<close>
        proof -
          have P1_P2_equiv: \<open>?P1 C \<longleftrightarrow> ?P2 C\<close>
          proof
            show \<open>?P1 C \<Longrightarrow> ?P2 C\<close>
            proof -
              assume \<open>?P1 C\<close>
              then have trs_def: \<open>trs_of_clause N C = \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
                by (smt Collect_cong sup_bot.right_neutral superposition.trs_of_clause.simps superposition_axioms)
              then have trs_prop: \<open>ordered ?trs_upto\<close>
                using ordered_trs_of_clause by blast
              (* helper lemma: the inference of any inference between C and smaller clauses is already true in the model *)
              have valid_concl: \<open>\<iota> \<in> ground_inf.Inf_from {B \<in> N. B \<preceq>G C} \<Longrightarrow> validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (Rep_ground_clause (concl_of \<iota>))\<close> for \<iota>
              proof -
                assume \<iota>_elem: \<open>\<iota> \<in> ground_inf.Inf_from {B \<in> N. B \<preceq>G C}\<close>
                (* by the saturation hypothesis, the conclusion is entailed by smaller clauses in N *)
                then have  \<open>\<iota> \<in> Red_ground_Inf N\<close>
                  using assms(1) unfolding saturated_def ground_inf.Inf_from_def by blast
                then obtain N' where N'_subset: \<open>N' \<subseteq> N\<close>
                                 and entail: \<open>Rep_ground_clause ` N' \<Turnstile>F {Rep_ground_clause (concl_of \<iota>)}\<close>
                                 and \<open>\<forall>B \<in> N'. \<exists>P\<in>set (prems_of \<iota>). B \<prec>G P\<close>
                  unfolding Red_ground_Inf_def ground_entail_def by auto
                then have C_gt: \<open>\<forall>B \<in> N'. B \<prec>G C\<close>
                  using \<iota>_elem unfolding ground_inf.Inf_from_def
                  by (smt ground_clause_ord_distinct ground_clause_ord_total mem_Collect_eq subsetD transE trans_ground_clause_ord)
                (* by induction, the entailing clauses are true in the model *)
                have \<open>B \<in> Rep_ground_clause ` N' \<Longrightarrow> validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) B\<close> for B
                proof -
                  assume B_elem: \<open>B \<in> Rep_ground_clause ` N'\<close>
                  then have \<open>Abs_ground_clause B \<in> N'\<close>
                    using Rep_ground_clause_inverse
                    by (metis imageE)
                  then have Abs_B_elem: \<open>Abs_ground_clause B \<prec>G C \<and> Abs_ground_clause B \<in> N\<close> using C_gt N'_subset by blast
                  then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N (Abs_ground_clause B)))) (Rep_ground_clause (Abs_ground_clause B))\<close>
                    using ind Rep_ground_clause_inverse by blast
                  then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Rep_ground_clause (Abs_ground_clause B))\<close>
                    using Abs_B_elem model_construction_monotonic assms(1,2) C_elem by blast
                  then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) B\<close>
                    using B_elem Rep_ground_clause Abs_ground_clause_inverse
                    by (smt imageE)
                  then show ?thesis using B_elem trs_def by argo
                qed
                (* hence, the conclusion is true in the model *)
                then show ?thesis
                  using entail trs_prop unfolding entail_def by fast
              qed
              let ?\<sigma> = \<open>Var\<close> (* identity substitution *)
              have subst_\<sigma>: \<open>subst_apply_lit L ?\<sigma> = L\<close> for L :: \<open>('f,'v) literal\<close>
                by (smt subst_apply_lit.simps literal_exhaust_1 subst_apply_term_empty subst_upair)
              consider (neg_lit) \<open>selection (Rep_ground_clause C) \<noteq> {#} \<or> (\<exists>s t. Lit False (Upair s t) \<in># Rep_ground_clause C \<and> (\<forall>L \<in># Rep_ground_clause C. L \<preceq>L Lit False (Upair s t)))\<close>
                     | (pos_lit) \<open>selection (Rep_ground_clause C) = {#} \<and> (\<forall>s t. Lit False (Upair s t) \<in># Rep_ground_clause C \<longrightarrow> (\<exists>L \<in># Rep_ground_clause C. \<not> L \<preceq>L Lit False (Upair s t)))\<close> by blast
              then show \<open>?P2 C\<close>
              proof cases
                case neg_lit
                then obtain s t where selection_C: \<open>Lit False (Upair s t) \<in># selection (Rep_ground_clause C)
                                                    \<or> (selection (Rep_ground_clause C) = {#} \<and> Lit False (Upair s t) \<in># Rep_ground_clause C \<and> (\<forall>L' \<in># Rep_ground_clause C. L' \<preceq>L Lit False (Upair s t)))\<close>
                  using selection_neg_lit
                  by (metis (full_types) mset_lit.cases multiset_nonemptyE uprod_exhaust)
                then have L_elem: \<open>Lit False (Upair s t) \<in># Rep_ground_clause C\<close> using selection_subset
                  by (meson mset_subset_eqD)
                then obtain C' where C_def: \<open>Rep_ground_clause C = {#Lit False (Upair s t)#} + C'\<close>
                  by (metis insert_DiffM2 union_commute)
                from L_elem have L_ground: \<open>ground_lit (Lit False (Upair s t))\<close> using Rep_ground_clause by fast
                consider (s_t_distinct) \<open>(s, t) \<notin> equiv_class_of_trs ?trs_upto\<close>
                       | (s_t_equiv) \<open>(s, t) \<in> equiv_class_of_trs ?trs_upto\<close> by blast
                then show ?thesis
                proof cases
                  case s_t_distinct
                  (* s and t are not equivalent in the model, the clause is satisfied *)
                  then have \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit (Lit False (Upair s t)) \<sigma>)\<close> for \<sigma>
                    using validate_ground_lit.simps L_ground subst_ground_lit [of \<open>Lit False (Upair s t)\<close> \<sigma>]
                    by (metis (no_types, lifting) Upair.abs_eq confluent_canonical_trs equiv_class_fo trs_prop validate_eq.abs_eq)
                  then show ?thesis using L_elem unfolding validate_clause_def by blast
                next
                  case s_t_equiv
                  (* s and t are equivalent in the model *)
                  consider (eq) \<open>s = t\<close> | (lt) \<open>s \<prec> t \<or> t \<prec> s\<close>
                    using L_ground term_ord_ground_total unfolding total_on_def by auto
                  then show ?thesis
                  proof cases
                    case eq
                    (* there exists an eql resolution inference from C *)
                    have \<open>Infer [{#Lit False (Upair s s)#} + C'] C' \<in> eresolution_inferences\<close>
                    proof -
                      have \<open>Infer [{#Lit False (Upair s s)#} + C'] C' = Infer [{#Lit False (Upair s s)#} + C'] (subst_apply_cl C' ?\<sigma>)\<close>
                        using C_def Rep_ground_clause subst_ground_cl [of C' ?\<sigma>]
                        by (smt mem_Collect_eq union_iff)
                      moreover have \<open>is_mgu ?\<sigma> {(s, s)}\<close> by auto
                      moreover have \<open>(selection ({#Lit False (Upair s s)#} + C') = {#} \<and> (\<forall>M\<in>#C'. subst_apply_lit M ?\<sigma> \<preceq>L subst_apply_lit (Lit False (Upair s s)) ?\<sigma>)) \<or> Lit False (Upair s s) \<in># selection ({#Lit False (Upair s s)#} + C')\<close>
                      proof -
                        consider \<open>(Lit False (Upair s s)) \<in># selection ({#Lit False (Upair s s)#} + C')\<close>
                               | \<open>selection ({#Lit False (Upair s s)#} + C') = {#} \<and> (\<forall>L' \<in># C'. L' \<preceq>L Lit False (Upair s s))\<close>
                          using eq C_def selection_C by auto
                        moreover have \<open>subst_apply_lit L ?\<sigma> = L\<close> for L :: \<open>('f, 'v) literal\<close> proof (cases L; auto) qed
                        ultimately show ?thesis by auto
                      qed
                      ultimately show ?thesis unfolding eresolution_inferences_def by blast
                    qed
                    moreover have C'_rep: \<open>Rep_ground_clause (Abs_ground_clause C') = C'\<close>
                      using Abs_ground_clause_inverse C_def
                      by (smt Rep_ground_clause mem_Collect_eq union_iff)
                    ultimately have \<open>Infer [C] (Abs_ground_clause C') \<in> ground_superposition_inference_system\<close>
                      unfolding ground_superposition_inference_system_def using Rep_ground_inference.simps C_def eq by auto
                    then have \<open>Infer [C] (Abs_ground_clause C') \<in> ground_inf.Inf_from {B \<in> N. B \<preceq>G C}\<close>
                      using C_elem unfolding ground_inf.Inf_from_def by auto
                    (* it conclusion C' is already true in the model *)
                    then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) C'\<close>
                      using valid_concl [of \<open>Infer [C] (Abs_ground_clause C')\<close>] inference.sel(2) [of \<open>[C]\<close> \<open>Abs_ground_clause C'\<close>] C'_rep by argo
                    (* C includes C', so its true as well *)
                    moreover have \<open>ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>) \<Longrightarrow> ground_cl (subst_apply_cl C' \<sigma>)\<close> for \<sigma> :: \<open>('f,'v) subst\<close> using C_def by auto
                    moreover have \<open>L \<in># C' \<Longrightarrow> L \<in># Rep_ground_clause C\<close> for L using C_def by auto
                    ultimately show ?thesis unfolding validate_clause_def by meson
                  next
                    case lt
                    (* s' and t' are introduced to break the symmetry *)
                    then obtain s' t' where s_t_lt: \<open>s' \<prec> t'\<close>
                                        and s_t_def: \<open>s = s' \<and> t = t' \<or> s = t' \<and> t = s'\<close>
                                        and s_t_ground: \<open>ground_term s' \<and> ground_term t'\<close>
                      using L_ground by auto
                    obtain u where nf_s: \<open>normal_form ?trs_upto s' u\<close>
                               and nf_t: \<open>normal_form ?trs_upto t' u\<close>
                      using s_t_equiv s_t_ground s_t_def
                      unfolding equiv_class_of_trs_def by blast
                    then have \<open>u \<preceq> s' \<and> ground_term u\<close>
                      using normal_form_le [of ?trs_upto] ordered_trs_preserve_groundness [of ?trs_upto] trs_prop s_t_ground
                      unfolding normal_form_def by presburger
                    (* the normal form u of s and t is strictly smaller than the largest of the two
                       terms, so there is a rewrite rule is the TRS that can be used to rewrite
                       that larger term *)
                    then have \<open>u \<noteq> t'\<close> using s_t_lt term_ord_trans unfolding trans_def
                      by (meson wf_not_sym wf_term_ord)
                    then have \<open>rewrite_by_trs ?trs_upto t' u\<close>
                      using nf_t unfolding normal_form_def by blast
                    then have \<open>\<exists>lhs rhs u'. subterm_replace u' t' rhs lhs \<and> (lhs, rhs) \<in> ?trs_upto\<close>
                    proof (induct ?trs_upto t' u rule: rewrite_by_trs.induct)
                      case (rew t s)
                      then show ?case
                        by (meson \<open>rewrite_by_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) t' u\<close> confluent_canonical_trs confluent_def irreducible_def nf_t normal_form_def)
                    next
                      case (trans u''' t''' s''')
                      then show ?case
                        by (meson \<open>rewrite_by_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) t' u\<close> confluent_canonical_trs confluent_def irreducible_def nf_t normal_form_def)
                    qed
                    then obtain lhs rhs u' where repl: \<open>subterm_replace u' t' rhs lhs\<close>
                                             and rule_in_trs: \<open>(lhs, rhs) \<in> ?trs_upto\<close> by blast
                    (* there is a productive clause B corresponding to that rewrite rule *)
                    then obtain A where \<open>(lhs, rhs) \<in> trs_of_clause N A\<close> and \<open>A \<prec>G C\<close> and \<open>A \<in> N\<close> by blast
                    then obtain B where rule_elem: \<open>(lhs, rhs) \<in> production (\<Union> (trs_of_clause N ` {A \<in> N. A \<prec>G B})) B\<close>
                                    and B_elem: \<open>B \<in> N\<close>
                                    and \<open>B \<preceq>G A\<close> using ex_productive_clause by blast
                    then obtain L B' where B_def: \<open>Rep_ground_clause B = {# L #} + B'\<close>
                                       and L_def: \<open>L = Lit True (Upair lhs rhs)\<close>
                                       and L_max: \<open>\<forall>L'\<in>#B'. L' \<prec>L L\<close>
                                       and selection_B: \<open>selection (Rep_ground_clause B) = {#}\<close>
                      unfolding production_def by blast
                    have B_lt: \<open>B \<prec>G C\<close> using \<open>B \<preceq>G A\<close> \<open>A \<prec>G C\<close>
                      by (metis (no_types, lifting) transE trans_ground_clause_ord)
                    from rule_elem have rule_ground: \<open>ground_term lhs \<and> ground_term rhs\<close> using ground_production by blast
                    with repl s_t_ground have u'_ground: \<open>ground_term u'\<close> by (meson subterm_replace_ground)
                    from rule_elem have rule_ord: \<open>rhs \<prec> lhs\<close> unfolding production_def by force
                    have ground_concl: \<open>ground_cl ({# Lit False (Upair u' s') #} + B' + C')\<close>
                      using s_t_ground u'_ground ground_subclause [of C \<open>{#Lit False (Upair s t)#}\<close> C'] C_def ground_subclause [of B \<open>{#L#}\<close> B'] B_def by auto
                    (* there exists a positive superposition inference between C and B*)
                    have \<open>Infer [{# L #} + B' , {# Lit False (Upair s t)#} + C'] (subst_apply_cl ({#Lit False (Upair u' s')#} + B' + C') ?\<sigma>) \<in> neg_superposition_inferences\<close>
                    proof -
                      have \<open>is_mgu ?\<sigma> {(lhs, lhs)}\<close> by auto
                      moreover have \<open>L = Lit True (Upair rhs lhs)\<close>
                        using L_def by simp
                      moreover have \<open>Lit False (Upair s t) = Lit False (Upair t' s')\<close>
                        using s_t_def by auto
                      moreover have \<open>subterm_replace u' t' rhs lhs\<close>
                        using repl .
                      moreover have \<open>is_Fun lhs\<close>
                        using rule_ground by auto
                      moreover have \<open>\<not> lhs \<cdot> ?\<sigma> \<preceq> rhs \<cdot> ?\<sigma>\<close>
                        using rule_ord subst_ground_term rule_ground term_ord_trans unfolding trans_def
                        by (metis wf_not_sym wf_term_ord)
                      moreover have \<open>\<not> t' \<cdot> ?\<sigma> \<preceq> s' \<cdot> ?\<sigma>\<close>
                        using s_t_lt s_t_ground subst_ground_term term_ord_trans unfolding trans_def
                        by (metis wf_not_sym wf_term_ord)
                      moreover have \<open>subst_apply_lit L ?\<sigma> \<prec>L subst_apply_lit (Lit False (Upair s t)) ?\<sigma>\<close>
                      proof -
                        have \<open>lhs \<preceq> t'\<close> using subterm_replace_ord repl rule_ground s_t_ground subterm_replace_ord_2 by metis
                        then have \<open>lhs \<preceq> t' \<and> rhs \<prec> t'\<close> using rule_ord
                          using rule_ground s_t_ground term_ord_trans unfolding trans_def by blast
                        then consider (eq) \<open>lhs = t' \<and> rhs \<prec> t'\<close> | (lt) \<open>lhs \<prec> t' \<and> rhs \<prec> t'\<close> by blast
                        then have \<open>({#lhs, rhs#}, {#s', s', t', t'#}) \<in> mult term_ord\<close>
                        proof cases
                          case eq
                          then have \<open>({#t',rhs#}, {#t',t'#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
                          also have \<open>({#t',t'#}, {#s',t',t'#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
                          also have \<open>({#s',t',t'#}, {#s',s',t',t'#}) \<in> mult1 term_ord\<close> unfolding mult1_def by force
                          finally show ?thesis using eq unfolding mult_def by auto
                        next
                          case lt
                          then show ?thesis
                            using mult_max [of \<open>{#lhs, rhs#}\<close> t' term_ord \<open>{#s', s', t', t'#}\<close>] by auto
                        qed
                        moreover have \<open>mset_lit (subst_apply_lit L ?\<sigma>) = {#lhs, rhs#}\<close>
                          using L_def by auto
                        moreover have \<open>mset_lit (subst_apply_lit (Lit False (Upair s t)) ?\<sigma>) = {#s',s',t',t'#}\<close>
                          using s_t_def by fastforce
                        ultimately show ?thesis unfolding lit_ord_def inv_image_def by auto
                      qed
                      moreover have \<open>(\<forall>M\<in>#B'. subst_apply_lit M ?\<sigma> \<prec>L subst_apply_lit L ?\<sigma>)\<close>
                        using L_max subst_\<sigma> by auto
                      moreover have \<open>Lit False (Upair s t) \<in># selection ({#Lit False (Upair s t)#} + C') \<or> selection ({#Lit False (Upair s t)#} + C') = {#} \<and> (\<forall>M\<in>#C'. subst_apply_lit M ?\<sigma> \<preceq>L subst_apply_lit (Lit False (Upair s t)) ?\<sigma>)\<close>
                        using selection_C subst_\<sigma> C_def by auto
                      moreover have \<open>selection ({# L #} + B') = {#}\<close>
                        using selection_B B_def by auto
                      ultimately show ?thesis unfolding neg_superposition_inferences_def by blast
                    qed
                    moreover have concl_rep: \<open>Rep_ground_clause (Abs_ground_clause ({# Lit False (Upair u' s') #} + B' + C')) = {# Lit False (Upair u' s') #} + B' + C'\<close>
                      using Abs_ground_clause_inverse ground_concl by blast
                    ultimately have \<open>Infer [B , C] (Abs_ground_clause ({# Lit False (Upair u' s') #} + B' + C')) \<in> ground_superposition_inference_system\<close>
                      using B_def C_def subst_\<sigma> unfolding ground_superposition_inference_system_def by auto
                    then have \<open>Infer [B , C] (Abs_ground_clause ({# Lit False (Upair u' s') #} + B' + C')) \<in> ground_inf.Inf_from {B \<in> N. B \<preceq>G C}\<close>
                      using B_lt B_elem C_elem unfolding ground_inf.Inf_from_def by auto
                    (* the conclusion of that inference is already true in the model *)
                    then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) ({# Lit False (Upair u' s') #} + B' + C')\<close>
                      using valid_concl [of \<open>Infer [B , C] (Abs_ground_clause ({# Lit False (Upair u' s') #} + B' + C'))\<close>] inference.sel(2) [of \<open>[B , C]\<close>] concl_rep by metis
                    then have \<open>\<exists>L \<in># {# Lit False (Upair u' s') #} + B' + C'. validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) L \<and> ground_lit L\<close>
                      using subst_ground_cl [of \<open>{# Lit False (Upair u' s') #} + B' + C'\<close>] subst_ground_lit ground_concl
                      unfolding validate_clause_def
                      by (metis (no_types, lifting))
                    then obtain L' where L'_elem: \<open>L' \<in># ({# Lit False (Upair u' s') #} + B' + C')\<close>
                                     and L'_ground: \<open>ground_lit L'\<close>
                                     and L'_valid: \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) L'\<close> by blast
                    from L'_elem consider \<open>L' = Lit False (Upair u' s')\<close> | \<open>L' \<in># B'\<close> | \<open>L' \<in># C'\<close> by auto
                    then show ?thesis
                      by (meson \<open>rewrite_by_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})) t' u\<close> confluent_canonical_trs confluent_def irreducible_def nf_s normal_form_def)
                  qed
                qed
              next
                case pos_lit
                obtain L where L_elem: \<open>L \<in># Rep_ground_clause C\<close>
                           and L_max: \<open>\<forall>L' \<in># Rep_ground_clause C. L' \<preceq>L L\<close>
                  using ex_max_literal [of \<open>Rep_ground_clause C\<close>] assms(2) C_elem Rep_ground_clause [of C]
                  by (metis (no_types, opaque_lifting) Rep_ground_clause_inverse add.left_neutral ground_subclause)
                then show ?thesis
                proof (cases L)
                  case (Pos s t)
                  then obtain C' where C_def: \<open>Rep_ground_clause C = {# Lit True (Upair s t) #} + C'\<close> using L_elem
                    by (metis add.commute insert_DiffM2)
                  then have s_t_ground: \<open>ground_term s \<and> ground_term t\<close>
                    using ground_subclause by fastforce
                  consider (a) \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) C'\<close>
                         | (b) \<open>s = t\<close>
                         | (c) \<open>\<not> validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) C' \<and> s \<noteq> t\<close> by blast
                  then show ?thesis
                  proof cases
                    case a
                    show ?thesis unfolding validate_clause_def
                    proof
                      show \<open>ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>) \<longrightarrow> (\<exists>L\<in>#Rep_ground_clause C. validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit L \<sigma>))\<close> for \<sigma>
                      proof
                        assume \<open>ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>)\<close>
                        then have \<open>ground_cl (subst_apply_cl C' \<sigma>)\<close> using C_def by auto
                        then obtain L' where \<open>L' \<in># C'\<close> and \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit L' \<sigma>)\<close>
                          using a unfolding validate_clause_def by blast
                        then show \<open>\<exists>L\<in>#Rep_ground_clause C. validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit L \<sigma>)\<close>
                          using C_def by (metis (no_types, lifting) UnCI set_mset_union)
                      qed
                    qed
                  next
                    case b
                    then have \<open>(s, t) \<in> equiv_class_of_trs ?trs_upto\<close>
                      using s_t_ground eql_in_equiv_class trs_prop by presburger
                    then have \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) L\<close>
                      using Pos validate_ground_lit.simps s_t_ground
                      by (metis (no_types, lifting) Upair.abs_eq confluent_canonical_trs equiv_class_fo trs_prop validate_eq.abs_eq)
                    moreover have \<open>subst_apply_lit L \<sigma> = L\<close> for \<sigma>
                      using s_t_ground Pos subst_ground_lit [of L] by auto
                    ultimately show ?thesis using L_elem unfolding validate_clause_def
                      by (metis (no_types, lifting))
                  next
                    case c
                    (* symmetry breaking *)
                    then obtain t' s' where s_t_ord: \<open>s' \<prec> t'\<close>
                                        and L_def: \<open>L = Lit True (Upair s' t')\<close>
                                        and ground_s': \<open>ground_term s'\<close>
                                        and ground_t': \<open>ground_term t'\<close>
                      using Pos s_t_ground term_ord_ground_total unfolding total_on_def
                      by (smt Upair_inject mem_Collect_eq)
                    consider (non_strict_max) \<open>L \<in># C'\<close>
                           | (strict_max) \<open>\<forall>L' \<in># C'. L' \<prec>L L\<close> using L_max C_def by auto
                    then show ?thesis
                    proof cases
                      case non_strict_max
                      then obtain C'' where C'_def: \<open>C' = {# L #} + C''\<close>
                        by (metis insert_DiffM2 union_commute)
                      (* there exists a positive superposition inference from C *)
                      then have ground_concl: \<open>ground_cl ({# Lit False (Upair s' s') #} + {# L #} + C'')\<close>
                        using ground_s' C'_def C_def ground_subclause by fastforce
                      then have \<open>Infer [{# L #} + {# L #} + C''] (subst_apply_cl ({# Lit False (Upair s' s') #} + {# L #} + C'') ?\<sigma>) \<in> efactoring_inferences\<close>
                      proof -
                        have \<open>is_mgu ?\<sigma> {(t', t')}\<close> by auto
                        moreover have \<open>L = Lit True (Upair t' s')\<close> using L_def by auto
                        moreover have \<open>\<not> t' \<cdot> ?\<sigma> \<preceq> s' \<cdot> ?\<sigma>\<close> using s_t_ord
                          by (metis subst_apply_term_empty wf_not_sym wf_term_ord)
                        moreover have \<open>selection ({#L#} + {#L#} + C'') = {#}\<close> using pos_lit C_def C'_def Pos by auto
                        moreover have \<open>M \<in># {#L#} + C'' \<Longrightarrow> subst_apply_lit M ?\<sigma> \<preceq>L subst_apply_lit L ?\<sigma>\<close> for M
                          using L_max C'_def C_def subst_\<sigma> by auto
                        ultimately show ?thesis unfolding efactoring_inferences_def by blast
                      qed
                      moreover have concl_rep: \<open>Rep_ground_clause (Abs_ground_clause ({# Lit False (Upair s' s') #} + {# L #} + C'')) = subst_apply_cl ({# Lit False (Upair s' s') #} + {# L #} + C'') ?\<sigma>\<close>
                        using ground_concl Abs_ground_clause_inverse [of \<open>{# Lit False (Upair s' s') #} + {# L #} + C''\<close>] subst_ground_cl [of \<open>{# Lit False (Upair s' s') #} + {# L #} + C''\<close> ?\<sigma>] by auto
                      moreover have \<open>Rep_ground_clause C = {# L #} + {# L #} + C''\<close>
                        using C_def C'_def Pos by auto
                      ultimately have \<open>Infer [C] (Abs_ground_clause ({# Lit False (Upair s' s') #} + {# L #} + C'')) \<in> ground_superposition_inference_system\<close>
                        unfolding ground_superposition_inference_system_def by auto
                      then have \<open>Infer [C] (Abs_ground_clause ({# Lit False (Upair s' s') #} + {# L #} + C'')) \<in> ground_inf.Inf_from {B \<in> N. B \<preceq>G C}\<close>
                        using C_elem unfolding ground_inf.Inf_from_def by auto
                      then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (Rep_ground_clause (Abs_ground_clause ({# Lit False (Upair s' s') #} + {# L #} + C'')))\<close>
                        using valid_concl by (smt inference.sel(2))
                      then have valid_concl: \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) ({# Lit False (Upair s' s') #} + {# L #} + C'')\<close>
                        using ground_concl Abs_ground_clause_inverse [of \<open>{# Lit False (Upair s' s') #} + {# L #} + C''\<close>]
                        by (smt mem_Collect_eq)
                      have \<open>\<exists>L\<in>#Rep_ground_clause C. validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit L \<sigma>)\<close> for \<sigma>
                      proof -
                        have \<open>ground_cl (subst_apply_cl ({# Lit False (Upair s' s') #} + {# L #} + C'') \<sigma>)\<close> using ground_concl subst_ground_cl by metis
                        then obtain L' where valid_L: \<open>validate_ground_lit (Abs_fo_interp (equiv_class_of_trs ?trs_upto)) (subst_apply_lit L' \<sigma>)\<close>
                                        and \<open>L' \<in># {# Lit False (Upair s' s') #} + {# L #} + C''\<close> using valid_concl unfolding validate_clause_def
                          by (meson union_iff union_single_eq_member)
                        then consider (1) \<open>L' \<in># {# Lit False (Upair s' s') #}\<close> | (2) \<open>L' \<in># {# L #} + C''\<close> by (meson union_iff)
                        then show ?thesis
                        proof cases
                          case 1
                          then have \<open>subst_apply_lit L' \<sigma> = Lit False (Upair s' s')\<close> using ground_s' subst_ground_lit
                            by (metis ground_concl mset_add multi_member_this single_eq_add_mset union_assoc)
                          then have \<open>(s', s') \<notin> equiv_class_of_trs ?trs_upto\<close>
                            using valid_L validate_ground_lit.simps
                            by (metis (no_types, lifting) Upair.abs_eq confluent_canonical_trs equiv_class_fo trs_prop validate_eq.abs_eq)
                          then show ?thesis using trs_prop ground_s' eql_in_equiv_class by fast (* contradiction *)
                        next
                          case 2
                          then have L_elem: \<open>L' \<in># Rep_ground_clause C\<close>
                            using C_def C'_def by auto
                          then show ?thesis
                            using L_elem valid_L by blast
                        qed
                      qed
                      then show ?thesis unfolding validate_clause_def by blast
                    next
                      case strict_max
                      then show ?thesis
                      proof (cases \<open>irreducible ?trs_upto t\<close>)
                        case True
                        then show ?thesis sorry
                      next
                        case False
                        then show ?thesis sorry
                      qed
                    qed
                  qed
                next
                  case (Neg s t)
                  then show ?thesis using pos_lit L_max L_elem by blast (* contradiction *)
                qed
              qed
            qed
          next
            show \<open>?P2 C \<Longrightarrow> ?P1 C\<close> unfolding production_def by blast
          qed
          have P3: \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (trs_of_clause N C))) (Rep_ground_clause C)\<close>
          proof (cases \<open>production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C = {}\<close>)
            case True (* clause is not productive, must be true as shown above *)
            then have \<open>validate_clause (Abs_fo_interp (equiv_class_of_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})))) (Rep_ground_clause C)\<close>
              using P1_P2_equiv by blast
            moreover have \<open>trs_of_clause N C = \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
              using True by (metis (no_types, lifting) sup_bot.right_neutral trs_of_clause.simps)
            ultimately show ?thesis by argo
          next
            case False (* clause is productive, therefore true by construction *)
            then show ?thesis using productive_clause_satisfied by blast
          qed
          show ?thesis using P1_P2_equiv P3 by blast
        qed
      qed
    qed
  qed
  then show ?thesis using assms by blast
qed

theorem canonical_interp_model:
  assumes \<open>saturated N\<close>
  assumes \<open>\<bottom>G \<notin> N\<close>
  assumes \<open>C \<in> N\<close>
  shows \<open>validate_clause (canonical_interp_ground N) (Rep_ground_clause C)\<close>
  using model_construction model_construction_monotonic assms by blast

interpretation statically_complete_calculus \<open>{\<bottom>G}\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause
proof
  have \<open>saturated N \<Longrightarrow> \<forall>C \<in> N. C \<notin> {\<bottom>G} \<Longrightarrow> B \<in> {\<bottom>G} \<Longrightarrow> \<not> N \<Turnstile>G {B}\<close> for B N
  proof
    assume saturated: \<open>saturated N\<close> and no_empty_cl: \<open>\<forall>C \<in> N. C \<notin> {\<bottom>G}\<close> and \<open>B \<in> {\<bottom>G}\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have \<open>Rep_ground_clause ` N \<Turnstile>F {\<bottom>F}\<close>
      unfolding ground_entail_def by auto
    then have N_unsat: \<open>\<exists>C \<in> Rep_ground_clause ` N. \<not> validate_clause I C\<close> for I
      unfolding entail_def validate_clause_def by auto
    (* model for N *)
    then have \<open>C \<in> N \<Longrightarrow> validate_clause (canonical_interp (Rep_ground_clause ` N)) (Rep_ground_clause C)\<close> for C
      using canonical_interp_model saturated no_empty_cl by blast
    with N_unsat show False by blast
  qed
  then show \<open>B \<in> {\<bottom>G} \<Longrightarrow> saturated N \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> \<exists>B'\<in>{\<bottom>G}. B' \<in> N\<close> for B N by blast
qed

(* First-order calculus *)

(* To ground first-order inferences, we need their unifier *)
(*datatype 'b fo_inference = Fo_Infer (inf: \<open>'b fclause inference\<close>) (subst: \<open>'b subst\<close>)*)

definition fo_eresolution_inferences :: \<open>('a, 'v) clause inference set\<close> where
\<open>fo_eresolution_inferences = {Infer [P] (fcl_remove_trms C) | P C \<sigma>. \<exists> C'. eresolution (Rep_fclause P) C \<sigma> FirstOrder C'}\<close>

definition fo_efactoring_inferences :: \<open>'a fclause inference set\<close> where
\<open>fo_efactoring_inferences = {Infer [P] (fcl_remove_trms C) | P C \<sigma>. \<exists> C'. efactoring (Rep_fclause P) C \<sigma> FirstOrder C'}\<close>

definition fo_superposition_inferences :: \<open>'a fclause inference set\<close> where
\<open>fo_superposition_inferences = {Infer [P1 , P2] (fcl_remove_trms C) | P1 P2 C \<sigma>. \<exists> C'. superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'}\<close>

abbreviation fo_superposition_inference_system :: \<open>'a fclause inference set\<close>
  where
\<open>fo_superposition_inference_system \<equiv> fo_eresolution_inferences
                                   \<union> fo_efactoring_inferences
                                   \<union> fo_superposition_inferences\<close>

interpretation fo_inf: sound_inference_system \<open>empty_fclauses\<close> \<open>(\<Turnstile>F)\<close> fo_superposition_inference_system
proof
  show \<open>\<iota> \<in> fo_superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close> for \<iota>
  proof -
    assume \<open>\<iota> \<in> fo_superposition_inference_system\<close>
    then consider (a) \<open>\<iota> \<in> fo_eresolution_inferences\<close>
      | (b) \<open>\<iota> \<in> fo_efactoring_inferences\<close>
      | (c) \<open>\<iota> \<in> fo_superposition_inferences\<close>
      by auto
    then show \<open>set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close>
    proof cases
      case a
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and eresolution: \<open>eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        using fo_eresolution_inferences_def Rep_fclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_fclause P)) (cl_ecl C)\<close>
        using eresolution_is_sound by force
      moreover have \<open>cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
        using fcl_remove_trms_cl_ecl eresolution_preserves_finiteness finite_P eresolution by blast
      ultimately show ?thesis
        unfolding fclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case b
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and efactoring: \<open>efactoring (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        using fo_efactoring_inferences_def Rep_fclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_fclause P)) (cl_ecl C)\<close>
        using efactoring_is_sound by force
      moreover have \<open>cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
        using fcl_remove_trms_cl_ecl efactoring_preserves_finiteness finite_P efactoring by blast
      ultimately show ?thesis
        unfolding fclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case c
      then obtain P1 P2 C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] (fcl_remove_trms C)\<close>
          and finite_P1: \<open>finite (cl_ecl (Rep_fclause P1))\<close>
          and finite_P2: \<open>finite (cl_ecl (Rep_fclause P2))\<close>
          and superposition: \<open>superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'\<close>
        using fo_superposition_inferences_def Rep_fclause by fastforce
      then have \<open>set_entails_clause {cl_ecl (Rep_fclause P1), cl_ecl (Rep_fclause P2)} (cl_ecl C)\<close>
        using superposition_is_sound by force
      moreover have \<open>cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
        using fcl_remove_trms_cl_ecl superposition_preserves_finiteness finite_P1 finite_P2 superposition by blast
      ultimately show ?thesis
        unfolding fclause_entails_def using \<iota>_def by auto
    qed
  qed
qed

abbreviation subst_fclause :: \<open>'a subst \<Rightarrow> 'a fclause \<Rightarrow> 'a gclause\<close>
  where \<open>subst_fclause \<sigma> F \<equiv> Abs_gclause (Ecl (subst_cl (cl_ecl (Rep_fclause F)) \<sigma>) {})\<close>

abbreviation grounding_subst :: \<open>'a subst \<Rightarrow> 'a fclause \<Rightarrow> bool\<close>
  where \<open>grounding_subst \<sigma> F \<equiv> ground_clause (subst_cl (cl_ecl (Rep_fclause F)) \<sigma>)\<close>

lemma Rep_subst_fclause:
  \<open>grounding_subst \<sigma> F \<Longrightarrow> Rep_gclause (subst_fclause \<sigma> F) = Ecl (subst_cl (cl_ecl (Rep_fclause F)) \<sigma>) {}\<close>
  using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause F)) \<sigma>) {}\<close>]
        Rep_fclause [of F] by simp

definition grounding_clause :: \<open>'a fclause \<Rightarrow> 'a gclause set\<close>
  where \<open>grounding_clause F = { subst_fclause \<sigma> F | \<sigma>. grounding_subst \<sigma> F }\<close>

(* Since substitutions are not recorded in inferences, we use this function to get them back *)
(*fun gen_substs :: \<open>'a fclause inference \<Rightarrow> 'a subst set\<close>
  where \<open>gen_substs \<iota> = { subst I | I. inf I = \<iota> \<and> I \<in> fo_eresolution_inferences \<union> fo_efactoring_inferences \<union> fo_superposition_inferences }\<close>

definition grounding_inference :: \<open>'a fclause inference \<Rightarrow> 'a gclause inference set\<close>
  where \<open>grounding_inference \<iota> = { Infer (map (subst_fclause (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>)) (subst_fclause (\<sigma> \<lozenge> \<theta>) (concl_of \<iota>))
                                 | \<sigma> \<theta>. list_all (grounding_subst (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>) \<and> \<sigma> \<in> gen_substs \<iota>}\<close>*)

definition grounding_inference :: \<open>'a fclause inference \<Rightarrow> 'a gclause inference set\<close>
  where \<open>grounding_inference \<iota> = { Infer (map (subst_fclause \<sigma>) (prems_of \<iota>)) (subst_fclause \<sigma> (concl_of \<iota>))
                                 | \<sigma>. list_all (grounding_subst \<sigma>) (prems_of \<iota>) \<and> grounding_subst \<sigma> (concl_of \<iota>)}
                                 \<inter> ground_superposition_inference_system\<close>

(*lemma grounding_prems_grounding_concl:
  assumes \<open>\<iota> \<in> fo_superposition_inference_system\<close>
  assumes \<open>list_all (grounding_subst \<sigma>) (prems_of \<iota>)\<close>
  shows \<open>grounding_subst \<sigma> (concl_of \<iota>)\<close>
proof -
  have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) \<subseteq> (\<Union>C \<in> set (prems_of \<iota>). vars_of_cl (cl_ecl (Rep_fclause C)))\<close>
  proof -
    from assms(1) consider (refl) \<open>\<iota> \<in> inf ` fo_eresolution_inferences\<close>
      | (fact) \<open>\<iota> \<in> inf ` fo_efactoring_inferences\<close>
      | (supr) \<open>\<iota> \<in> inf ` fo_superposition_inferences\<close>
      by auto
    then show ?thesis
    proof cases
      case refl
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and eresolution: \<open>eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
          and idem: \<open>Idem \<sigma>\<close>
        using fo_eresolution_inferences_def Rep_fclause by fastforce
      then obtain L1 t s
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_fclause P)\<close>
        and L1_def: \<open>L1 = Neg (Eq s t) \<or> L1 = Neg (Eq t s)\<close>
        and mgu: \<open>MGU \<sigma> t s\<close>
        and cl_C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_fclause P) - {L1}) \<sigma>\<close>
        unfolding eresolution_def orient_lit_inst_def ck_unifier_def by fastforce
      have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) = vars_of_cl (cl_ecl (Rep_fclause (fcl_remove_trms C)))\<close>
        using \<iota>_def by auto
      also have \<open>... = vars_of_cl (cl_ecl C)\<close>
        using fcl_remove_trms_cl_ecl [of C] finite_P eresolution_preserves_finiteness [of \<open>Rep_fclause P\<close> C \<sigma> FirstOrder C'] eresolution
        by auto
      also have \<open>... = vars_of_cl (subst_cl (cl_ecl (Rep_fclause P) - {L1}) \<sigma>)\<close> using cl_C_def by auto
      also have \<open>... \<subseteq> vars_of s \<union> vars_of t \<union> vars_of_cl (cl_ecl (Rep_fclause P) - {L1})\<close> using no_variable_introduction_cl mgu idem by blast
      also have \<open>... \<subseteq> vars_of_cl (cl_ecl (Rep_fclause P))\<close> using L1_elem L1_def by force
      also have \<open>... = (\<Union>C\<in>set (prems_of \<iota>). vars_of_cl (cl_ecl (Rep_fclause C)))\<close> using \<iota>_def by auto
      finally show ?thesis by auto
    next
      case fact
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and efactoring: \<open>efactoring (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
          and idem: \<open>Idem \<sigma>\<close>
        using fo_efactoring_inferences_def Rep_fclause by fastforce
      then obtain L1 L2 L' t s v u
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_fclause P)\<close>
        and L1_def: \<open>L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t) \<or> L1 = Neg (Eq t s) \<or> L1 = Neg (Eq s t)\<close>
        and L2_def: \<open>L2 = Pos (Eq u v) \<or> L2 = Pos (Eq v u) \<or> L2 = Neg (Eq u v) \<or> L2 = Neg (Eq v u)\<close>
        and L2_elem: \<open>L2 \<in> cl_ecl (Rep_fclause P) - {L1}\<close>
        and L'_def: \<open>L' = Neg (Eq s v)\<close>
        and C'_def: \<open>C' = cl_ecl (Rep_fclause P) - {L2} \<union> {L'}\<close>
        and cl_C_def: \<open>cl_ecl C = subst_cl C' \<sigma>\<close>
        and \<open>ck_unifier t u \<sigma> FirstOrder\<close>
        unfolding efactoring_def orient_lit_inst_def by metis
      then have mgu: \<open>MGU \<sigma> t u\<close>
        unfolding ck_unifier_def by metis
      have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) = vars_of_cl (cl_ecl (Rep_fclause (fcl_remove_trms C)))\<close>
        using \<iota>_def by auto
      also have \<open>... = vars_of_cl (cl_ecl C)\<close>
        using fcl_remove_trms_cl_ecl [of C] finite_P efactoring_preserves_finiteness [of \<open>Rep_fclause P\<close> C \<sigma> FirstOrder C'] efactoring
        by auto
      also have \<open>... = vars_of_cl (subst_cl (cl_ecl (Rep_fclause P) - {L2} \<union> {L'}) \<sigma>)\<close> using C'_def cl_C_def by auto
      also have \<open>... \<subseteq> vars_of t \<union> vars_of u \<union> vars_of_cl (cl_ecl (Rep_fclause P) - {L2} \<union> {L'})\<close> using no_variable_introduction_cl mgu idem by blast
      also have \<open>... \<subseteq> vars_of t \<union> vars_of u \<union> vars_of_cl (cl_ecl (Rep_fclause P) - {L2}) \<union> vars_of s \<union> vars_of v\<close> using L'_def by auto
      also have \<open>... \<subseteq> vars_of t \<union> vars_of u \<union> vars_of_cl (cl_ecl (Rep_fclause P)) \<union> vars_of s \<union> vars_of v\<close> by auto
      also have \<open>... \<subseteq> vars_of u \<union> vars_of_cl (cl_ecl (Rep_fclause P)) \<union> vars_of v\<close> using L1_def L1_elem by fastforce
      also have \<open>... \<subseteq> vars_of_cl (cl_ecl (Rep_fclause P))\<close> using L2_def L2_elem by force
      also have \<open>... = (\<Union>C\<in>set (prems_of \<iota>). vars_of_cl (cl_ecl (Rep_fclause C)))\<close> using \<iota>_def by auto
      finally show ?thesis by auto
    next
      case supr
      then obtain P1 P2 C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] (fcl_remove_trms C)\<close>
          and finite_P1: \<open>finite (cl_ecl (Rep_fclause P1))\<close>
          and finite_P2: \<open>finite (cl_ecl (Rep_fclause P2))\<close>
          and superposition: \<open>superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'\<close>
          and idem: \<open>Idem \<sigma>\<close>
        using fo_superposition_inferences_def Rep_fclause by fastforce
      then obtain L M s t t' u u' v p polarity L' cl_P1 cl_P2
        where L_elem: \<open>L \<in> cl_ecl (Rep_fclause P1)\<close>
          and L_def: \<open>orient_lit_inst L t s polarity \<sigma>\<close>
          and M_elem: \<open>M \<in> cl_ecl (Rep_fclause P2)\<close>
          and M_def: \<open>orient_lit_inst M u v pos \<sigma>\<close>
          and \<open>ck_unifier u' u \<sigma> FirstOrder\<close>
          and subterm: \<open>subterm t p u'\<close>
          and rep_subterm: \<open>replace_subterm t p v t'\<close>
          and cl_C_def: \<open>cl_ecl C = subst_cl C' \<sigma>\<close>
          and C'_def: \<open>C' = cl_P1 - {L} \<union> (cl_P2 - {M} \<union> {L'})\<close>
          and cl_P1_def: \<open>cl_P1 = cl_ecl (Rep_fclause P1)\<close>
          and cl_P2_def: \<open>cl_P2 = cl_ecl (Rep_fclause P2)\<close>
          and L'_def: \<open>L' = mk_lit polarity (Eq t' s)\<close>
        unfolding superposition_def by auto
      then have mgu: \<open>MGU \<sigma> u' u\<close> unfolding ck_unifier_def by auto
      have L_vars: \<open>vars_of_lit L = vars_of s \<union> vars_of t\<close> using L_def unfolding orient_lit_inst_def by auto
      have M_vars: \<open>vars_of_lit M = vars_of u \<union> vars_of v\<close> using M_def unfolding orient_lit_inst_def by auto
      have \<open>vars_of_lit (mk_lit polarity (Eq t' s)) = vars_of t' \<union> vars_of s\<close> proof (cases polarity; auto) qed
      then have \<open>vars_of_lit L' = vars_of t' \<union> vars_of s\<close> using L'_def by auto
      moreover have u'_vars: \<open>vars_of u' \<subseteq> vars_of t\<close> using subterm vars_subterm by auto
      ultimately have L'_vars: \<open>vars_of_lit L' \<subseteq> vars_of t \<union> vars_of v \<union> vars_of s\<close>
        using vars_of_replacement [where ?s = \<open>t'\<close> and ?t = t and ?p = p and ?v = v] rep_subterm by auto
      have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) = vars_of_cl (cl_ecl (Rep_fclause (fcl_remove_trms C)))\<close>
        using \<iota>_def by auto
      also have \<open>... = vars_of_cl (cl_ecl C)\<close>
        using fcl_remove_trms_cl_ecl [of C] finite_P1 finite_P2 superposition_preserves_finiteness [of \<open>Rep_fclause P1\<close> \<open>Rep_fclause P2\<close> C \<sigma> FirstOrder C'] superposition
        by auto
      also have \<open>... = vars_of_cl (subst_cl (cl_ecl (Rep_fclause P1) - {L} \<union> (cl_ecl (Rep_fclause P2) - {M} \<union> {L'})) \<sigma>)\<close>
        using cl_C_def C'_def cl_P1_def cl_P2_def by auto
      also have \<open>... \<subseteq> vars_of_cl (subst_cl (cl_ecl (Rep_fclause P1)) \<sigma>) \<union> vars_of_cl (subst_cl (cl_ecl (Rep_fclause P2)) \<sigma>) \<union> vars_of_lit (subst_lit L' \<sigma>)\<close> by auto
      also have \<open>... \<subseteq> vars_of_cl (cl_ecl (Rep_fclause P1)) \<union> vars_of_cl (cl_ecl (Rep_fclause P2)) \<union> vars_of_lit L' \<union> vars_of u \<union> vars_of u'\<close>
        using no_variable_introduction_lit [of \<sigma> u' u] no_variable_introduction_cl [of \<sigma> u' u] mgu idem by blast
      also have \<open>... \<subseteq> vars_of_cl (cl_ecl (Rep_fclause P1)) \<union> vars_of_cl (cl_ecl (Rep_fclause P2)) \<union> vars_of t \<union> vars_of v \<union> vars_of s \<union> vars_of u\<close>
        using L'_vars u'_vars by auto
      also have \<open>... = vars_of_cl (cl_ecl (Rep_fclause P1)) \<union> vars_of_cl (cl_ecl (Rep_fclause P2)) \<union> vars_of_lit L \<union> vars_of_lit M\<close>
        using L_vars M_vars by auto
      also have \<open>... \<subseteq> vars_of_cl (cl_ecl (Rep_fclause P1)) \<union> vars_of_cl (cl_ecl (Rep_fclause P2))\<close>
        using L_elem M_elem by auto
      also have \<open>... = (\<Union>C\<in>set (prems_of \<iota>). vars_of_cl (cl_ecl (Rep_fclause C)))\<close>using \<iota>_def by auto
      finally show ?thesis by auto
    qed
  qed
  moreover have \<open>C \<in> set (prems_of \<iota>) \<Longrightarrow> ground_on (vars_of_cl (cl_ecl (Rep_fclause C))) \<sigma>\<close> for C
    using assms(2) ground_clauses_and_ground_substs unfolding list_all_def by blast
  ultimately have \<open>ground_on (vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>)))) \<sigma>\<close> unfolding ground_on_def by blast
  then show ?thesis
    using ground_substs_yield_ground_clause by blast
qed*)

(*lemma eresolution_grounding:
  assumes \<open>eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
  assumes \<open>grounding_subst (\<sigma> \<lozenge> \<theta>) P\<close>
  assumes \<open>Idem \<sigma>\<close>
  shows \<open>\<exists>C'. eresolution (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close>
proof -
  from assms(1) obtain t s Cl_P Cl_C trms_C L
    where i: \<open>eligible_literal L (Rep_fclause P) \<sigma>\<close>
      and ii: \<open>L \<in> cl_ecl (Rep_fclause P)\<close>
      and iii: \<open>Cl_C = cl_ecl C\<close>
      and iv: \<open>Cl_P = cl_ecl (Rep_fclause P)\<close>
      and v: \<open>orient_lit_inst L t s neg \<sigma>\<close>
      and vi: \<open>ck_unifier t s \<sigma> FirstOrder\<close>
      and vii: \<open>C = Ecl Cl_C trms_C\<close>
      and viii: \<open>trms_C = get_trms Cl_C (dom_trms Cl_C (subst_set (trms_ecl (Rep_fclause P) \<union> {t}) \<sigma>)) FirstOrder\<close>
      and ix: \<open>Cl_C = subst_cl C' \<sigma>\<close>
      and x: \<open>C' = Cl_P - {L}\<close>
    unfolding eresolution_def by auto
  let ?t = \<open>t \<lhd> (\<sigma> \<lozenge> \<theta>)\<close>
  let ?s = \<open>s \<lhd> (\<sigma> \<lozenge> \<theta>)\<close>
  let ?Cl_P = \<open>subst_cl Cl_P (\<sigma> \<lozenge> \<theta>)\<close>
  let ?Cl_C = \<open>subst_cl Cl_C (\<sigma> \<lozenge> \<theta>)\<close>
  let ?trms_C = \<open>(\<lambda>x. x \<lhd> (\<sigma> \<lozenge> \<theta>)) ` trms_C\<close>
  let ?L = \<open>subst_lit L (\<sigma> \<lozenge> \<theta>)\<close>
  have \<open>eligible_literal ?L (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) []\<close> using i Rep_subst_fclause assms(2) sorry
  moreover have \<open>?L \<in> cl_ecl (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P))\<close> using ii Rep_subst_fclause assms(2) by auto
  moreover have \<open>?Cl_C = cl_ecl (subst_ecl C (\<sigma> \<lozenge> \<theta>))\<close> using iii by (metis (no_types, lifting) cl_ecl.simps subst_ecl.simps vii)
  moreover have \<open>?Cl_P = cl_ecl (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P))\<close> using iv Rep_subst_fclause assms(2) by auto
  moreover have \<open>orient_lit_inst ?L (?t) (?s) neg []\<close> using v unfolding orient_lit_inst_def sorry
  moreover have \<open>ck_unifier (?t) (?s) [] Ground\<close> using vi Unifier_def ck_unifier_def ck_unifier_thm by fastforce
  moreover have \<open>subst_ecl C (\<sigma> \<lozenge> \<theta>) = Ecl ?Cl_C ?trms_C\<close> sorry
  moreover have \<open>?trms_C = get_trms ?Cl_C (dom_trms ?Cl_C (subst_set (trms_ecl (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) \<union> {?t}) [])) Ground\<close> sorry
  moreover have \<open>?Cl_C = subst_cl (subst_cl C' (\<sigma> \<lozenge> \<theta>)) []\<close> using ix assms(3) subst_cl_empty unfolding Idem_def by (metis composition_of_substs_cl subst_eq_cl)
  moreover have \<open>subst_cl C' (\<sigma> \<lozenge> \<theta>) = ?Cl_P - {?L}\<close> sorry
  ultimately show ?thesis unfolding eresolution_def by blast
qed*)

(*lemma grounding_inference_preserves_system:
  \<open>\<kappa> \<in> grounding_inference \<iota> \<Longrightarrow> \<kappa> \<in> ground_superposition_inference_system\<close>
proof -
  assume \<open>\<kappa> \<in> grounding_inference \<iota>\<close>
  then obtain \<sigma> \<theta>
    where \<kappa>_def: \<open>\<kappa> = Infer (map (subst_fclause (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>)) (subst_fclause (\<sigma> \<lozenge> \<theta>) (concl_of \<iota>))\<close>
      and \<open>Fo_Infer \<iota> \<sigma> \<in> fo_eresolution_inferences \<union> fo_efactoring_inferences \<union> fo_superposition_inferences \<close>
      and grounding_prems: \<open>list_all (grounding_subst (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>)\<close>
    unfolding grounding_inference_def by force
  then consider (refl) \<open>\<exists>P C C'. \<iota> = Infer [P] (fcl_remove_trms C) \<and> eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
    | (fact) \<open>\<exists>P C C'. \<iota> = Infer [P] (fcl_remove_trms C) \<and> efactoring (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
    | (supr) \<open>\<exists>P1 P2 C C'. \<iota> = Infer [P1, P2] (fcl_remove_trms C) \<and> superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'\<close>
    unfolding fo_eresolution_inferences_def fo_efactoring_inferences_def fo_superposition_inferences_def by blast
  then show \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
  proof cases
    case refl
    then obtain P C C'
      where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
        and \<open>eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close> by auto
    then have \<open>eresolution (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close> sorry
    moreover from \<iota>_def \<kappa>_def have \<open>\<kappa> = Infer [subst_fclause (\<sigma> \<lozenge> \<theta>) P] (gcl_remove_trms (subst_ecl C (\<sigma> \<lozenge> \<theta>)))\<close> sorry
    moreover have \<open>ground_clause (cl_ecl (subst_ecl C (\<sigma> \<lozenge> \<theta>)))\<close> sorry
    ultimately have \<open>\<kappa> \<in> ground_eresolution_inferences\<close> unfolding ground_eresolution_inferences_def by blast
    then show ?thesis sorry
  next
    case fact
    then show ?thesis sorry
  next
    case supr
    then show ?thesis sorry
  qed
qed
(*proof -
  assume \<iota>_elem: \<open>\<iota> \<in> fo_superposition_inference_system\<close> and \<kappa>_elem: \<open>\<kappa> \<in> grounding_inference \<iota>\<close>
  then consider (refl) \<open>\<iota> \<in> fo_eresolution_inferences\<close>
    | (fact) \<open>\<iota> \<in> fo_efactoring_inferences\<close>
    | (supr) \<open>\<iota> \<in> fo_superposition_inferences\<close> by auto
  then show \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
  proof cases
    case refl
    then obtain P C \<sigma> C'
      where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
        and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
        and eresolution: \<open>eresolution (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        and idem: \<open>Idem \<sigma>\<close>
      using fo_eresolution_inferences_def Rep_fclause by fastforce
    with \<kappa>_elem obtain \<theta>
      where \<kappa>_def: \<open>\<kappa> = Infer [subst_fclause \<theta> P] (subst_fclause \<theta> (fcl_remove_trms C))\<close>
        and \<theta>_grounding_prems: \<open>grounding_subst \<theta> P\<close>
      unfolding grounding_inference_def list_all_def by auto
    from finite_P eresolution have finite_C: \<open>finite (cl_ecl C)\<close> using eresolution_preserves_finiteness by blast
    from \<theta>_grounding_prems \<iota>_elem have \<theta>_grounding_concl: \<open>grounding_subst \<theta> (fcl_remove_trms C)\<close>
      using \<iota>_def grounding_prems_grounding_concl [of \<iota> \<theta>] by auto
    have concl_def: \<open>subst_fclause \<theta> (fcl_remove_trms C) = Abs_gclause (Ecl (subst_cl (cl_ecl C) \<theta>) {})\<close>
      using finite_C substs_preserve_finiteness [of \<open>cl_ecl C\<close> \<theta>] fcl_remove_trms_cl_ecl by auto
    have \<open>\<kappa> \<in> ground_eresolution_inferences\<close>
    proof -
      have concl_def': \<open>gcl_remove_trms (subst_ecl C \<theta>) = Abs_gclause (Ecl (subst_cl (cl_ecl C) \<theta>) {})\<close>
        by (metis (no_types, lifting) cl_ecl.simps gcl_remove_trms.elims subst_ecl.simps cl_ecl.elims trms_ecl.simps)
      have \<open>\<kappa> = Infer [subst_fclause \<theta> P] (gcl_remove_trms (subst_ecl C \<theta>))\<close>
        using concl_def concl_def' \<kappa>_def by auto
      moreover have \<open>eresolution (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close>
        using eresolution idem \<theta>_grounding_prems eresolution_grounding by blast
      moreover have \<open>ground_clause (cl_ecl (subst_ecl C \<theta>))\<close>
      proof -
        have \<open>cl_ecl (subst_ecl C \<theta>) = subst_cl (cl_ecl C) \<theta>\<close>
          by (smt cl_ecl.elims eclause.inject subst_ecl.simps)
        then show ?thesis
          using \<theta>_grounding_concl finite_C substs_preserve_finiteness fcl_remove_trms_cl_ecl by auto
      qed
      ultimately show ?thesis unfolding ground_eresolution_inferences_def sorry
    qed
    then show ?thesis by auto
  next
    case fact
    then show ?thesis sorry
  next
    case supr
    then show ?thesis sorry
  qed
qed*)*)

interpretation grounding_function empty_fclauses \<open>(\<Turnstile>F)\<close> fo_superposition_inference_system
  empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause grounding_clause grounding_inference
proof
  show \<open>B \<in> empty_fclauses \<Longrightarrow> grounding_clause B \<noteq> {}\<close> for B
  proof -
    assume \<open>B \<in> empty_fclauses\<close>
    then have \<open>cl_ecl (Rep_fclause B) = {}\<close> by auto
    then have \<open>ground_clause (subst_cl (cl_ecl (Rep_fclause B)) [])\<close> by auto
    then show \<open>grounding_clause B \<noteq> {}\<close> unfolding grounding_clause_def by blast
  qed
next
  show \<open>B \<in> empty_fclauses \<Longrightarrow> grounding_clause B \<subseteq> empty_gclauses\<close> for B
  proof
    fix C
    assume \<open>B \<in> empty_fclauses\<close> and \<open>C \<in> grounding_clause B\<close>
    then obtain \<sigma> where \<open>C = Abs_gclause (Ecl (subst_cl (cl_ecl (Rep_fclause B)) \<sigma>) {})\<close>
                    and \<open>cl_ecl (Rep_fclause B) = {}\<close> unfolding grounding_clause_def by blast
    then have \<open>Rep_gclause C = Ecl {} {}\<close> using Abs_gclause_inverse [of \<open>Ecl {} {}\<close>] by auto
    then show \<open>C \<in> empty_gclauses\<close> by auto
  qed
next
  show \<open>grounding_clause C \<inter> empty_gclauses \<noteq> {} \<longrightarrow> C \<in> empty_fclauses\<close> for C
  proof
    assume \<open>grounding_clause C \<inter> empty_gclauses \<noteq> {}\<close>
    then obtain B where \<open>B \<in> grounding_clause C\<close> and \<open>B \<in> empty_gclauses\<close> by auto
    then obtain \<sigma> where \<open>ground_clause (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close>
                    and \<open>B = Abs_gclause (Ecl (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>) {})\<close>
                    and \<open>cl_ecl (Rep_gclause B) = {}\<close> unfolding grounding_clause_def by auto
    moreover have \<open>finite (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close> using Rep_fclause [of C] by auto
    ultimately have \<open>subst_cl (cl_ecl (Rep_fclause C)) \<sigma> = {}\<close>
      using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>) {}\<close>] by auto
    then have \<open>cl_ecl (Rep_fclause C) = {}\<close> by auto
    then show \<open>C \<in> empty_fclauses\<close> by auto
  qed
next
  show \<open>\<iota> \<in> fo_superposition_inference_system \<Longrightarrow> grounding_inference \<iota> \<subseteq> Red_ground_Inf (grounding_clause (concl_of \<iota>))\<close> for \<iota>
  proof
    fix \<kappa>
    assume \<open>\<iota> \<in> fo_superposition_inference_system\<close> and \<open>\<kappa> \<in> grounding_inference \<iota>\<close>
    then obtain \<sigma> where \<open>\<kappa> = Infer (map (subst_fclause \<sigma>) (prems_of \<iota>)) (subst_fclause \<sigma> (concl_of \<iota>))\<close>
                    and \<open>concl_of \<kappa> \<in> grounding_clause (concl_of \<iota>)\<close>
                    and \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
      unfolding grounding_inference_def grounding_clause_def by auto
    then show \<open>\<kappa> \<in> Red_ground_Inf (grounding_clause (concl_of \<iota>))\<close>
      using Red_Inf_of_Inf_to_N by auto
  qed
qed

(* show that the notion of entailment obtained by grounding is equivalent to the standard definition *)
lemma grounding_validate_clause:
  \<open>fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C) = validate_clause I (cl_ecl (Rep_fclause C))\<close>
proof -
  assume \<open>fo_interpretation I\<close>
  show ?thesis
  proof
    show \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C) \<Longrightarrow> validate_clause I (cl_ecl (Rep_fclause C))\<close>
    proof -
      assume validate: \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C)\<close>
      have \<open>ground_clause (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>) \<Longrightarrow> validate_ground_clause I (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close> for \<sigma>
      proof -
        assume ground: \<open>ground_clause (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close>
        then have \<open>subst_fclause \<sigma> C \<in> grounding_clause C\<close> unfolding grounding_clause_def by auto
        then have \<open>validate_clause I (cl_ecl (Rep_gclause (subst_fclause \<sigma> C)))\<close> using validate by simp
        moreover have \<open>cl_ecl (Rep_gclause (subst_fclause \<sigma> C)) = subst_cl (cl_ecl (Rep_fclause C)) \<sigma>\<close>
          using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>) {}\<close>] Rep_fclause [of C] ground by simp
        ultimately have \<open>validate_clause I (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close> by metis
        then show \<open>validate_ground_clause I (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close> using ground
          by (metis substs_preserve_ground_clause validate_clause.simps)
      qed
      then show ?thesis by auto
    qed
  next
    show \<open>validate_clause I (cl_ecl (Rep_fclause C)) \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C)\<close>
    proof -
      assume validate: \<open>validate_clause I (cl_ecl (Rep_fclause C))\<close>
      have \<open>D \<in> cl_ecl ` Rep_gclause ` grounding_clause C \<Longrightarrow> validate_clause I D\<close> for D
      proof -
        assume \<open>D \<in> cl_ecl ` Rep_gclause ` grounding_clause C\<close>
        then obtain \<sigma> where D_def: \<open>D = cl_ecl (Rep_gclause (subst_fclause \<sigma> C))\<close>
                        and ground: \<open>ground_clause (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>)\<close> unfolding grounding_clause_def by auto
        then have \<open>D = subst_cl (cl_ecl (Rep_fclause C)) \<sigma>\<close>
          using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause C)) \<sigma>) {}\<close>] Rep_fclause [of C] by auto
        with ground validate have \<open>ground_clause D\<close> and \<open>validate_ground_clause I D\<close> by auto
        then have \<open>validate_ground_clause I (subst_cl D \<sigma>')\<close> for \<sigma>'
          by (metis substs_preserve_ground_clause)
        then show \<open>validate_clause I D\<close> by auto
      qed
      then show ?thesis by auto
    qed
  qed
qed

lemma grounding_validate_clause_set:
  \<open>fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N) = validate_clause_set I (cl_ecl ` Rep_fclause ` N)\<close>
proof -
  assume fo_I: \<open>fo_interpretation I\<close>
  show ?thesis
  proof
    show \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N) \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_fclause ` N)\<close>
    proof -
      assume validate: \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N)\<close>
      then have \<open>C \<in> N \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C)\<close> for C by fastforce
      then have \<open>C \<in> (cl_ecl ` Rep_fclause ` N) \<Longrightarrow> validate_clause I C\<close> for C using grounding_validate_clause fo_I by blast
      then show ?thesis by auto
    qed
  next
    show \<open>validate_clause_set I (cl_ecl ` Rep_fclause ` N) \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N)\<close>
    proof -
      assume validate: \<open>validate_clause_set I (cl_ecl ` Rep_fclause ` N)\<close>
      have \<open>C \<in> cl_ecl ` Rep_gclause ` \<G>_set N \<Longrightarrow> validate_clause I C\<close> for C
      proof -
        assume \<open>C \<in> cl_ecl ` Rep_gclause ` \<G>_set N\<close>
        then obtain D where \<open>D \<in> N\<close> and C_elem: \<open>C \<in> cl_ecl ` Rep_gclause ` grounding_clause D\<close> by auto
        with validate have \<open>validate_clause I (cl_ecl (Rep_fclause D))\<close> by auto
        then have \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause D)\<close> using grounding_validate_clause fo_I by blast
        with C_elem show ?thesis by auto
      qed
      then show ?thesis by auto
    qed
  qed
qed

lemma entails_equiv: \<open>N1 \<Turnstile>F N2 \<longleftrightarrow> entails_\<G> N1 N2\<close>
proof
  show \<open>N1 \<Turnstile>F N2 \<Longrightarrow> entails_\<G> N1 N2\<close>
  proof -
    assume \<open>N1 \<Turnstile>F N2\<close>
    then have \<open>C \<in> N2 \<Longrightarrow> fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_fclause ` N1) \<Longrightarrow> validate_clause I (cl_ecl (Rep_fclause C))\<close> for C I
      unfolding fclause_entails_def set_entails_clause_def by auto
    then have \<open>C \<in> N2 \<Longrightarrow> fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N1) \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C)\<close> for C I
      using grounding_validate_clause_set grounding_validate_clause by blast
    then show \<open>entails_\<G> N1 N2\<close> unfolding entails_\<G>_def gclause_entails_def set_entails_clause_def by simp
  qed
next
  show \<open>entails_\<G> N1 N2 \<Longrightarrow> N1 \<Turnstile>F N2\<close>
  proof -
    assume \<open>entails_\<G> N1 N2\<close>
    then have \<open>C \<in> N2 \<Longrightarrow> fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` \<G>_set N1) \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` grounding_clause C)\<close> for I C
      unfolding entails_\<G>_def gclause_entails_def set_entails_clause_def by force
    then have \<open>C \<in> N2 \<Longrightarrow> fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_fclause ` N1) \<Longrightarrow> validate_clause I (cl_ecl (Rep_fclause C))\<close> for C I
      using grounding_validate_clause_set grounding_validate_clause by blast
    then show \<open>N1 \<Turnstile>F N2\<close> unfolding fclause_entails_def set_entails_clause_def by auto
  qed
qed

interpretation nonground_lifting: nonground_static_refutational_complete_calculus grounding_clause grounding_inference
empty_fclauses \<open>(\<Turnstile>F)\<close> fo_superposition_inference_system empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause
proof
  show \<open>\<iota> \<in> ground_inf.Inf_from (\<G>_set N) \<Longrightarrow> \<iota> \<in> Red_ground_Inf (\<G>_set N) \<or> (\<exists>\<kappa>. \<kappa> \<in> fo_inf.Inf_from N \<and> \<iota> \<in> grounding_inference \<kappa>)\<close> for N \<iota>
  proof -
    assume \<open>\<iota> \<in> ground_inf.Inf_from (\<G>_set N)\<close>
    then consider (refl) \<open>\<iota> \<in> ground_eresolution_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      | (fact) \<open>\<iota> \<in> ground_efactoring_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      | (supr) \<open>\<iota> \<in> ground_superposition_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      unfolding ground_inf.Inf_from_def by auto
    then show \<open>\<iota> \<in> Red_ground_Inf (\<G>_set N) \<or> (\<exists>\<kappa>. \<kappa> \<in> fo_inf.Inf_from N \<and> \<iota> \<in> grounding_inference \<kappa>)\<close>
    proof cases
      case refl
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (gcl_remove_trms C)\<close>
          and eresolution: \<open>eresolution (Rep_gclause P) C \<sigma> Ground C'\<close>
          and \<open>ground_clause (cl_ecl C)\<close>
          and \<open>P \<in> \<G>_set N\<close>
        unfolding ground_eresolution_inferences_def by auto
      then obtain P' \<theta>
        where P'_elem: \<open>P' \<in> N\<close>
          and P_subst: \<open>subst_fclause \<theta> P' = P\<close>
          and grounding_\<theta>: \<open>grounding_subst \<theta> P'\<close>
        unfolding grounding_clause_def by blast
      from eresolution obtain L1 s t
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_gclause P)\<close>
          and L1_def: \<open>orient_lit_inst L1 t s neg \<sigma>\<close>
          and C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_gclause P) - {L1}) \<sigma>\<close>
        unfolding eresolution_def by blast
      with P_subst have \<open>L1 \<in> subst_cl (cl_ecl (Rep_fclause P')) \<theta>\<close>
        using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause P')) \<theta>) {}\<close>] Rep_fclause [of P'] grounding_\<theta> by force
      then obtain L1'
        where L1'_elem: \<open>L1' \<in> cl_ecl (Rep_fclause P')\<close>
          and L1'_def: \<open>L1 = subst_lit L1' \<theta>\<close> by auto
      let ?D = \<open>Abs_fclause (Ecl (cl_ecl (Rep_fclause P') - {L1'}) {})\<close>
      have \<open>cl_ecl C = cl_ecl (Rep_gclause P) - {L1}\<close>
        using C_def substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause P) - {L1}\<close> \<sigma>] Rep_gclause [of P] by auto
      also have \<open>... = cl_ecl (Rep_gclause (subst_fclause \<theta> P')) - {subst_lit L1' \<theta>}\<close>
        using P_subst L1'_def by auto
      also have \<open>... = subst_cl (cl_ecl (Rep_fclause P')) \<theta> - {subst_lit L1' \<theta>}\<close>
        using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause P')) \<theta>) {}\<close>] Rep_fclause [of P'] grounding_\<theta> by auto
      also have \<open>... \<subseteq> subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta>\<close> using L1'_elem by auto
      finally have \<open>cl_ecl C \<subset> subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta> \<or> cl_ecl C = subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta>\<close> by auto
        using Abs_gclause_inverse [of \<open>Ecl (subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta>) {}\<close>] Rep_fclause [of P'] by auto
      then have D_subst: \<open>subst_fclause \<theta> ?D = gcl_remove_trms C\<close> by auto
      have grounding_\<theta>_D: \<open>grounding_subst \<theta> ?D\<close>
        using Abs_fclause_inverse [of \<open>Ecl (cl_ecl (Rep_fclause P') - {L1'}) {}\<close>] Rep_fclause [of P'] grounding_\<theta> by auto
      let ?\<kappa> = \<open>Infer [P'] ?D\<close>
      have \<open>?\<kappa> \<in> fo_eresolution_inferences\<close> sorry
      moreover have \<open>set (prems_of ?\<kappa>) \<subseteq> N\<close> using P'_elem by auto
      moreover have \<open>\<iota> \<in> grounding_inference ?\<kappa>\<close>
      proof -
        have \<open>\<iota> = Infer (map (subst_fclause \<theta>) (prems_of ?\<kappa>)) (subst_fclause \<theta> (concl_of ?\<kappa>))\<close> using \<iota>_def P_subst D_subst by auto
        moreover have \<open>list_all (grounding_subst \<theta>) (prems_of ?\<kappa>)\<close> using grounding_\<theta> by auto
        moreover have \<open>grounding_subst \<theta> (concl_of ?\<kappa>)\<close> using grounding_\<theta>_D by auto
        moreover have \<open>\<iota> \<in> ground_superposition_inference_system\<close> using refl by auto
        ultimately show \<open>\<iota> \<in> grounding_inference ?\<kappa>\<close> unfolding grounding_inference_def by blast
      qed
      ultimately show ?thesis unfolding fo_inf.Inf_from_def by blast
    next
      case fact
      then show ?thesis sorry
    next
      case supr
      then show ?thesis sorry
    qed
  qed
qed

end
end
