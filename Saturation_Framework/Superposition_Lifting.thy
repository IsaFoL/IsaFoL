(*  Title:       Superposition_Lifting
    Author:      Simon Robillard <simon.robillard at chalmers.se>, 2018
*)

theory Superposition_Lifting
  imports Calculi "HOL-Library.Multiset" First_Order_Terms.Unification
begin

(* literals, clauses *)

datatype ('f, 'v) literal = Eq \<open>('f, 'v) term\<close> \<open>('f, 'v) term\<close> | Neq \<open>('f, 'v) term\<close> \<open>('f, 'v) term\<close>

type_synonym ('f, 'v) clause = \<open>('f, 'v) literal multiset\<close>

fun vars_lit :: \<open>('f, 'v) literal \<Rightarrow> 'v set\<close>
  where
    \<open>vars_lit (Eq s t) = vars_term s \<union> vars_term t\<close> |
    \<open>vars_lit (Neq s t) = vars_term s \<union> vars_term t\<close>

abbreviation ground_term :: \<open>('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>ground_term t \<equiv> vars_term t = {}\<close>

abbreviation ground_lit :: \<open>('f, 'v) literal \<Rightarrow> bool\<close>
  where \<open>ground_lit L \<equiv> vars_lit L = {}\<close>

abbreviation ground_cl :: \<open>('f, 'v) clause \<Rightarrow> bool\<close>
  where \<open>ground_cl C \<equiv> \<forall>L \<in># C. ground_lit L\<close>

typedef ('f, 'v) ground_clause = \<open>{C :: ('f, 'v) clause. ground_cl C}\<close>
apply(rule_tac x = \<open>{#}\<close> in exI)
  by simp

(* substitutions *)

fun subst_apply_lit :: \<open>('f, 'v) literal \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) literal\<close>
  where
   \<open>subst_apply_lit (Eq s t) \<sigma> = (Eq (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))\<close>
 | \<open>subst_apply_lit (Neq s t) \<sigma> = (Neq (s \<cdot> \<sigma>) (t \<cdot> \<sigma>))\<close>

fun subst_apply_cl :: \<open>('f, 'v) clause \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) clause\<close>
  where \<open>subst_apply_cl C \<sigma> = {# subst_apply_lit L \<sigma>. L \<in># C #}\<close>

lemma subst_lit_comp: \<open>subst_apply_lit L (\<sigma> \<circ>\<^sub>s \<tau>) = subst_apply_lit (subst_apply_lit L \<sigma>) \<tau>\<close>
proof (cases L, auto) qed

lemma subst_ground_term: \<open>ground_term t \<Longrightarrow> t \<cdot> \<sigma> = t\<close>
  by (metis empty_iff subst_ident term_subst_eq)

lemma subst_ground_lit: \<open>ground_lit L \<Longrightarrow> subst_apply_lit L \<sigma> = L\<close>
proof (cases L)
  case (Eq s t)
  assume \<open>ground_lit L\<close>
  then have \<open>ground_term s \<and> ground_term t\<close> using \<open>L = Eq s t\<close> by auto
  then have \<open>s \<cdot> \<sigma> = s \<and> t \<cdot> \<sigma> = t\<close> using subst_ground_term by auto
  then show \<open>subst_apply_lit L \<sigma> = L\<close> using \<open>L = Eq s t\<close> by simp
next
  case (Neq s t)
  assume \<open>ground_lit L\<close>
  then have \<open>ground_term s \<and> ground_term t\<close> using \<open>L = Neq s t\<close> by auto
  then have \<open>s \<cdot> \<sigma> = s \<and> t \<cdot> \<sigma> = t\<close>
    by (metis equals0D subst_ident term_subst_eq)
  then show \<open>subst_apply_lit L \<sigma> = L\<close> using \<open>L = Neq s t\<close> by simp
qed

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
    then obtain L' where \<open>L = subst_apply_lit L' \<sigma>\<close> by auto
    then show \<open>ground_lit L\<close>
    proof (cases L'; simp add: ground_subst) qed
  qed
  then show ?thesis by auto
qed

lemma ex_subst_Rep_ground_clause: \<open>\<exists>\<sigma> :: ('f, 'v) subst. ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>)\<close>
  by (smt Rep_ground_clause mem_Collect_eq subst_ground_cl)

(* semantics *)

type_synonym ('f, 'v) trs = \<open>(('f, 'v) term \<times> ('f, 'v) term) set\<close>

(* TODO add congruence requirement in the definition? *)
type_synonym ('f, 'v) interp = \<open>(('f, 'v) term \<times> ('f, 'v) term) set\<close>

definition fun_comp :: \<open>('f, 'v) interp \<Rightarrow> bool\<close>
  where \<open>fun_comp I = (\<forall>f a1 a2. (\<forall>n. (nth a1 n, nth a2 n) \<in> I) \<longrightarrow> length a1 = length a2 \<longrightarrow> (Fun f a1, Fun f a2) \<in> I)\<close>

fun congruence :: \<open>('f, 'v) interp \<Rightarrow> bool\<close>
  where \<open>congruence I = (refl I \<and> trans I \<and> sym I \<and> fun_comp I)\<close>

fun validate_ground_lit :: \<open>('f, 'v) interp \<Rightarrow> ('f, 'v) literal \<Rightarrow> bool\<close>
  where
   \<open>validate_ground_lit I (Eq s t) = ((s,t) \<in> I)\<close>
 | \<open>validate_ground_lit I (Neq s t) = ((s,t) \<notin> I)\<close>

definition validate_clause :: \<open>('f, 'v) interp \<Rightarrow> ('f, 'v) clause \<Rightarrow> bool\<close>
  where \<open>validate_clause I C = (\<forall>\<sigma>. ground_cl (subst_apply_cl C \<sigma>) \<longrightarrow> (\<exists>L \<in># C. validate_ground_lit I (subst_apply_lit L \<sigma>)))\<close>

definition entail :: \<open>('f, 'v) clause set \<Rightarrow> ('f, 'v) clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>F" 50)
  where
\<open>N1 \<Turnstile>F N2 \<equiv> \<forall>I. congruence I \<longrightarrow> (\<forall>C \<in> N1. validate_clause I C) \<longrightarrow> (\<forall>C \<in> N2. validate_clause I C)\<close>

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

lemma validate_subset:
  \<open>C1 \<subseteq># Rep_ground_clause C2 \<Longrightarrow> validate_clause I C1 \<Longrightarrow> validate_clause I (Rep_ground_clause C2)\<close> sorry

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
  assumes term_ord_trans: \<open>(s,t) \<in> term_ord \<Longrightarrow> (t,u) \<in> term_ord \<Longrightarrow> \<not> ((u,s) \<in> term_ord \<or> u = s)\<close>
      and term_ord_antisym: \<open>(s,t) \<in> term_ord \<Longrightarrow> (t,s) \<in> term_ord \<Longrightarrow> s = t\<close>
      and term_ord_term_comp: \<open>(s, t) \<in> term_ord \<Longrightarrow> \<not> ((Fun f (a1 @ t # a2), Fun f (a1 @ s # a2)) \<in> term_ord \<or> Fun f (a1 @ t # a2) = Fun f (a1 @ s # a2))\<close>
      and term_ord_subterm_comp: \<open>s \<in> set argl \<Longrightarrow> \<not> ((Fun f argl, s) \<in> term_ord \<or> Fun f argl = s)\<close>
      and wf_term_ord: \<open>wf term_ord\<close>
      and term_ord_ground_total: \<open>total_on {t. ground_term t} term_ord\<close>
      and term_ord_stable_grounding: \<open>\<And> \<sigma> :: ('f,'v) subst. (s, t) \<in> term_ord \<Longrightarrow> ground_term (s \<cdot> \<sigma>) \<Longrightarrow> ground_term (t \<cdot> \<sigma>) \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> term_ord\<close>
      and selection_subset: \<open>selection C \<subseteq># C\<close>
      and selection_neg_lit: \<open>\<not> Eq s t \<in># selection C\<close>
      (* TODO add stability under renaming for selection *)
begin

(* extend order to literals and clauses *)
abbreviation term_lt :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> (infix "\<prec>" 60)
  where
  \<open>term_lt s t \<equiv> (s,t) \<in> term_ord\<close>

abbreviation term_le :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> (infix "\<preceq>" 60)
  where
  \<open>term_le s t \<equiv> (s,t) \<in> term_ord \<or> s = t\<close>

fun mset_lit :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) term multiset\<close>
  where
    \<open>mset_lit (Eq s t) = {# s, t #}\<close>
  | \<open>mset_lit (Neq s t) = {# s, s, t, t #}\<close>

definition lit_ord :: \<open>(('f,'v) literal \<times> ('f,'v) literal) set\<close>
  where
    \<open>lit_ord = inv_image (mult term_ord) mset_lit\<close>

abbreviation lit_lt :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) literal \<Rightarrow> bool\<close> (infix "\<prec>L" 60)
  where
  \<open>lit_lt L1 L2 \<equiv> (L1,L2) \<in> lit_ord\<close>

abbreviation lit_le :: \<open>('f,'v) literal \<Rightarrow> ('f,'v) literal \<Rightarrow> bool\<close> (infix "\<preceq>L" 60)
  where
  \<open>lit_le L1 L2 \<equiv> (L1,L2) \<in> lit_ord \<or> mset_lit L1 = mset_lit L2\<close>

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
  \<open>ground_clause_le C1 C2 \<equiv> (C1,C2) \<in> ground_clause_ord \<or> {# mset_lit L. L \<in># Rep_ground_clause C1 #} = {# mset_lit L. L \<in># Rep_ground_clause C2 #}\<close>

definition ground_clause_set_ord :: \<open>(('f,'v) ground_clause set \<times> ('f,'v) ground_clause set) set\<close>
  where \<open>ground_clause_set_ord = inv_image clause_set_ord (image Rep_ground_clause)\<close>

lemma term_ord_ground_trans: \<open>ground_term s \<Longrightarrow> ground_term t \<Longrightarrow> ground_term u \<Longrightarrow> s \<prec> t \<Longrightarrow> t \<prec> u \<Longrightarrow> s \<prec> u\<close>
  using term_ord_trans term_ord_ground_total unfolding total_on_def by blast

lemma term_ord_ground_subterm_comp: \<open>ground_term (Fun f (a1 @ t # a2)) \<Longrightarrow> t \<prec> Fun f (a1 @ t # a2)\<close>
proof -
  assume ground_f: \<open>ground_term (Fun f (a1 @ t # a2))\<close>
  then have \<open>ground_term t \<and> \<not> Fun f (a1 @ t # a2) \<preceq> t\<close>
    using term_ord_subterm_comp by auto
  then show ?thesis using ground_f term_ord_ground_total unfolding total_on_def by blast
qed

lemma trans_lit_ord: \<open>trans lit_ord\<close>
proof
  fix L1 L2 L3
  assume \<open>L1 \<prec>L L2\<close> and \<open>L2 \<prec>L L3\<close>
  then have \<open>(mset_lit L1, mset_lit L2) \<in> mult term_ord\<close> and \<open>(mset_lit L2, mset_lit L3) \<in> mult term_ord\<close>
    unfolding lit_ord_def by auto
  then have \<open>(mset_lit L1, mset_lit L3) \<in> mult term_ord\<close> by (simp add: mult_def trancl_def)
  then show \<open>L1 \<prec>L L3\<close> unfolding lit_ord_def by auto
qed

lemma trans_ground_clause_ord: \<open>trans (ground_clause_ord)\<close>
proof
  fix C1 C2 C3
  assume \<open>C1 \<prec>G C2\<close> and \<open>C2 \<prec>G C3\<close>
  then have \<open>Rep_ground_clause C1 \<prec>F Rep_ground_clause C2\<close> and \<open>Rep_ground_clause C2 \<prec>F Rep_ground_clause C3\<close>
    unfolding ground_clause_ord_def by auto
  then have \<open>Rep_ground_clause C1 \<prec>F Rep_ground_clause C3\<close> unfolding clause_ord_def by (simp add: mult_def trancl_def)
  then show \<open>C1 \<prec>G C3\<close> unfolding ground_clause_ord_def by auto
qed

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

lemma lit_ord_ground_total: \<open>ground_lit L1 \<Longrightarrow> ground_lit L2 \<Longrightarrow> L1 \<prec>L L2 \<or> L2 \<preceq>L L1\<close>
  sorry

lemma ground_clause_ord_total: \<open>C1 \<prec>G C2 \<or> C2 \<preceq>G C1\<close>
  sorry

lemma ground_clause_ord_distinct: \<open>C1 \<prec>G C2 \<Longrightarrow> {# mset_lit L. L \<in># Rep_ground_clause C1 #} \<noteq> {# mset_lit L. L \<in># Rep_ground_clause C2 #}\<close>
  sorry

lemma ground_clause_ord_asymmetric: \<open>C1 \<prec>G C2 \<Longrightarrow> \<not> C2 \<prec>G C1\<close>
  sorry

lemma mult_max:
  assumes \<open>\<forall>x \<in># N. (x, y) \<in> ord\<close>
  assumes \<open>y \<in># M\<close>
  shows \<open>(N, M) \<in> mult ord\<close>
  by (metis (no_types, hide_lams) add.left_neutral assms empty_iff mult_def one_step_implies_mult set_mset_empty)

(* inferences *)

definition eresolution_inferences :: \<open>('f, 'v) clause inference set\<close> where
\<open>eresolution_inferences = {Infer [{# Neq s s' #} + C] (subst_apply_cl C \<sigma>)
                          | s s' C \<sigma>. is_mgu \<sigma> {(s, s')}
                                    \<and> (selection ({# Neq s s' #} + C) = {#} \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit (Neq s s') \<sigma>)
                                       \<or> Neq s s' \<in># selection ({# Neq s s' #} + C))}\<close>

definition efactoring_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>efactoring_inferences = {Infer [{# Eq u t #} + {# Eq u' s #} + C] (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>)
                         | s t u u' C \<sigma>. is_mgu \<sigma> {(u,u')}
                                       \<and> \<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                       \<and> \<not> u \<cdot> \<sigma> \<preceq> t \<cdot> \<sigma>
                                       \<and> selection ({# Eq u t #} + {# Eq u' s #} + C) = {#}
                                       \<and> (\<forall>M \<in># {# Eq u' s #} +  C. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit (Eq u' s) \<sigma>)}\<close>

(* the restriction \<not> u \<cdot> \<sigma> \<preceq> t \<cdot> \<sigma> is not found in Uwe's manuscript *)

(* subterm s t u v \<equiv> t can be obtained from s by replacing one occurrence of u by v*)
inductive subterm_replace :: \<open>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool\<close> where
  base: \<open>subterm_replace s t s t\<close> |
  step: \<open>subterm_replace s t u v \<Longrightarrow> subterm_replace (Fun f (a1 @ s # a2)) (Fun f (a1 @ t # a2)) u v\<close>

(* TODO renamings *)
definition pos_superposition_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>pos_superposition_inferences = {Infer [{# Eq t s #} + C , {# Eq vt u #} + D] (subst_apply_cl ({# Eq vs u #} + C + D) \<sigma>)
                                | s t u vs vt C D \<sigma>. \<exists>t'. is_mgu \<sigma> {(t, t')}
                                                        \<and> subterm_replace vs vt s t'
                                                        \<and> \<not> is_Var t'
                                                        \<and> \<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                                        \<and> \<not> u \<cdot> \<sigma> \<preceq> vt \<cdot> \<sigma>
                                                        \<and> subst_apply_lit (Eq t s) \<sigma> \<prec>L subst_apply_lit (Eq vt u) \<sigma>
                                                        \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit (Eq t s) \<sigma>)
                                                        \<and> (\<forall>M \<in># D. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit (Eq vt u) \<sigma>)
                                                        \<and> selection ({# Eq t s #} + C) = {#}
                                                        \<and> selection ({# Eq vt u #} + D) = {#}}\<close>

definition neg_superposition_inferences :: \<open>('f, 'v) clause inference set\<close>
  where
\<open>neg_superposition_inferences = {Infer [{# Eq t s #} + C , {# Neq vt u #} + D] (subst_apply_cl ({# Neq vs u #} + C + D) \<sigma>)
                                | s t u vs vt C D \<sigma>. \<exists>t'. is_mgu \<sigma> {(t, t')}
                                                        \<and> subterm_replace vs vt s t'
                                                        \<and> \<not> is_Var t'
                                                        \<and> \<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma>
                                                        \<and> \<not> u \<cdot> \<sigma> \<preceq> vt \<cdot> \<sigma>
                                                        \<and> subst_apply_lit (Eq t s) \<sigma> \<prec>L subst_apply_lit (Neq vt u) \<sigma>
                                                        \<and> (\<forall>M \<in># C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit (Eq t s) \<sigma>)
                                                        \<and> ((Neq vt u \<in># selection ({# Neq vt u #} + D)) \<or> (selection ({# Neq vt u #} + D) = {#} \<and> (\<forall>M \<in># D. subst_apply_lit M \<sigma> \<preceq>L subst_apply_lit (Neq vt u) \<sigma>)))
                                                        \<and> selection ({# Eq t s #} + C) = {#}}\<close>

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
  \<open>congruence I \<Longrightarrow> subterm_replace s t u v \<Longrightarrow> (u, v) \<in> I \<Longrightarrow> (s, t) \<in> I\<close>
proof -
  assume \<open>congruence I\<close>
  then have \<open>refl I\<close> and \<open>fun_comp I\<close> by auto
  assume \<open>(u,v) \<in> I\<close>
  show \<open>subterm_replace s t u v \<Longrightarrow> (s, t) \<in> I\<close>
  proof (induction s arbitrary: t)
    case (Var x)
    assume \<open>subterm_replace (Var x) t u v\<close>
    then show \<open>(Var x, t) \<in> I\<close>
    proof cases
      case base
      then have \<open>(u,v) = (Var x, t)\<close> by auto
      with \<open>(u,v) \<in> I\<close> show ?thesis by auto
    qed
  next
    case (Fun f args)
    then have \<open>subterm_replace (Fun f args) t u v\<close> by auto
    then show \<open>(Fun f args, t) \<in> I\<close>
    proof cases
      case base
      then have \<open>(u,v) = (Fun f args, t)\<close> by auto
      with \<open>(u,v) \<in> I\<close> show ?thesis by auto
    next
      case (step s' t' a1 a2)
      from Fun step have \<open>(s',t') \<in> I\<close> by auto (* apply induction hypothesis *)
      have \<open>(a1 @ s' # a2) ! n = (a1 @ t' # a2) ! n \<or> ((a1 @ s' # a2) ! n = s' \<and> (a1 @ t' # a2) ! n = t')\<close> for n
        by (simp add: nth_Cons' nth_append)
      then have \<open>((a1 @ s' # a2) ! n, (a1 @ t' # a2) ! n) \<in> I\<close> for n
        using \<open>refl I\<close> \<open>(s', t') \<in> I\<close> unfolding refl_on_def by (metis iso_tuple_UNIV_I)
      then have \<open>(Fun f (a1 @ s' # a2), Fun f (a1 @ t' # a2)) \<in> I\<close>
        using \<open>fun_comp I\<close> unfolding fun_comp_def by fastforce
      then show ?thesis using step by auto
    qed
  qed
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
    then obtain s s' C \<sigma>
      where \<iota>_def: \<open>\<iota> = Infer [{# Neq s s' #} + C] (subst_apply_cl C \<sigma>)\<close>
        and mgu: \<open>is_mgu \<sigma> {(s, s')}\<close>
      unfolding eresolution_inferences_def by auto
    have \<open>congruence I \<Longrightarrow> validate_clause I ({# Neq s s' #} + C) \<Longrightarrow> validate_clause I (subst_apply_cl C \<sigma>)\<close> for I
    proof -
      assume cong: \<open>congruence I\<close> and \<open>validate_clause I ({# Neq s s' #} + C)\<close>
      then have validate_prem_\<sigma>: \<open>validate_clause I (subst_apply_cl({# Neq s s' #} + C) \<sigma>)\<close> using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl C \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume ground_C: \<open>ground_cl (subst_apply_cl (subst_apply_cl C \<sigma>) \<tau>)\<close>
        (* the grounding of the conclusion is not necessarily a grounding of the premise, so we must extend it *)
        obtain \<upsilon> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (subst_apply_cl (subst_apply_cl ({# Neq s s' #} + C) \<sigma>) \<tau>) \<upsilon>)\<close>
          using ex_ground_instance by fast
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Neq s s' #} + C) \<sigma>) (\<tau> \<circ>\<^sub>s \<upsilon>))\<close> using subst_cl_comp by metis
        then obtain L where \<open>L \<in># subst_apply_cl ({#Neq s s'#} + C) \<sigma>\<close> and validate_L: \<open>validate_ground_lit I (subst_apply_lit L (\<tau> \<circ>\<^sub>s \<upsilon>))\<close>
          using validate_prem_\<sigma> unfolding validate_clause_def by blast
        then consider (a) \<open>L = subst_apply_lit (Neq s s') \<sigma>\<close> | (b) \<open>L \<in># subst_apply_cl C \<sigma>\<close> by auto
        then show \<open>\<exists>L \<in># subst_apply_cl C \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
        proof cases
          case a
          with validate_L have \<open>validate_ground_lit I (Neq (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s' \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>))\<close> by auto
          then have \<open>(s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, s' \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<notin> I\<close> by auto
          with mgu have \<open>(s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<notin> I\<close> unfolding is_mgu_def unifiers_def by auto
          moreover from cong have \<open>refl I\<close> by auto
          ultimately show ?thesis unfolding refl_on_def by blast (* contradiction *)
        next
          case b
          with ground_C have \<open>vars_lit (subst_apply_lit L \<tau>) = {}\<close> by auto
          with validate_L have \<open>validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
            using subst_ground_lit [of \<open>subst_apply_lit L \<tau>\<close> \<upsilon>] subst_lit_comp by metis
          with b show ?thesis by auto
        qed
      qed
      then show ?thesis unfolding validate_clause_def by auto
    qed
    then show ?thesis using \<iota>_def unfolding entail_def by auto
  next
    case fact (* soundness of equality factoring *)
    then obtain s t u u' C \<sigma>
      where \<iota>_def: \<open>\<iota> = Infer [{# Eq u t #} + {# Eq u' s #} + C] (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>)\<close>
        and mgu: \<open>is_mgu \<sigma> {(u, u')}\<close>
      unfolding efactoring_inferences_def by blast
    have \<open>congruence I \<Longrightarrow> validate_clause I ({# Eq u t #} + {# Eq u' s #} + C) \<Longrightarrow> validate_clause I (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>)\<close> for I
    proof -
      assume cong: \<open>congruence I\<close> and \<open>validate_clause I ({# Eq u t #} + {# Eq u' s #} + C)\<close>
      then have validate_prem_\<sigma>: \<open>validate_clause I (subst_apply_cl ({# Eq u t #} + {# Eq u' s #} + C) \<sigma>)\<close>
        using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) \<sigma>) \<tau>)\<close>
        then have \<open>ground_cl (subst_apply_cl ({# Eq u t #} + {# Neq t s #} + C) (\<sigma> \<circ>\<^sub>s \<tau>))\<close>
          using subst_cl_comp by metis
        then have i: \<open>ground_cl (subst_apply_cl C (\<sigma> \<circ>\<^sub>s \<tau>))\<close>
              and ii: \<open>vars_term (s \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) = {}\<close>
              and iii: \<open>vars_term (t \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) = {}\<close>
              and iv: \<open>vars_term (u \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) = {}\<close> by auto
        with mgu have \<open>vars_term (u' \<cdot> (\<sigma> \<circ>\<^sub>s \<tau>)) = {}\<close> unfolding is_mgu_def unifiers_def by auto
        with i ii iii iv have \<open>ground_cl (subst_apply_cl ({# Eq u t #} + {# Eq u' s #} + C) (\<sigma> \<circ>\<^sub>s \<tau>))\<close> by auto
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({# Eq u t #} + {# Eq u' s #} + C) \<sigma>) \<tau>)\<close>
          using subst_cl_comp [of \<open>{# Eq u t #} + {# Eq u' s #} + C\<close> \<sigma> \<tau>] by argo
        with validate_prem_\<sigma> have validate_L: \<open>\<exists>L \<in># subst_apply_cl ({# Eq u t #} + {# Eq u' s #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
          unfolding validate_clause_def by fast
        consider (a) \<open>\<exists>L \<in># subst_apply_cl ({# Eq u t #} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
          | (b) \<open>\<forall>L \<in># subst_apply_cl ({# Eq u t #} + C) \<sigma>. \<not> validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
          by auto
        then show \<open>\<exists>L \<in># subst_apply_cl ({#Eq u t#} + {#Neq t s#} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
        proof cases
          case a
          then show ?thesis by auto
        next
          case b
          with validate_L have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (Eq u' s) \<sigma>) \<tau>)\<close> by auto
          then have \<open>(u' \<cdot> \<sigma> \<cdot> \<tau>, s \<cdot> \<sigma> \<cdot> \<tau>) \<in> I\<close> by auto
          then have I_u_s: \<open>(u \<cdot> \<sigma> \<cdot> \<tau>, s \<cdot> \<sigma> \<cdot> \<tau>) \<in> I\<close> using mgu unfolding is_mgu_def unifiers_def by auto
          from b have \<open>\<not> validate_ground_lit I (subst_apply_lit (subst_apply_lit (Eq u t) \<sigma>) \<tau>)\<close> by auto
          then have I_u_t: \<open>(u \<cdot> \<sigma> \<cdot> \<tau>, t \<cdot> \<sigma> \<cdot> \<tau>) \<notin> I\<close> by auto
          from cong have \<open>trans I\<close> and \<open>sym I\<close> by auto
          with I_u_s I_u_t have \<open>(t \<cdot> \<sigma> \<cdot> \<tau>, s \<cdot> \<sigma> \<cdot> \<tau>) \<notin> I\<close> by (meson symE transD)
          then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (Neq t s) \<sigma>) \<tau>)\<close> by auto
          then show ?thesis by auto
        qed
      qed
      then show ?thesis unfolding validate_clause_def by blast
    qed
    then show ?thesis using \<iota>_def unfolding entail_def by force
  next
    case sup (* soundness of superposition *)
    then obtain s t t' u vs vt L L' C D \<sigma>
      where \<iota>_def: \<open>\<iota> = Infer [{#Eq t s#} + C, {#L#} + D] (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close>
        and L_def: \<open>L = Eq vt u \<and> L' = Eq vs u \<or> L = Neq vt u \<and> L' = Neq vs u\<close>
        and mgu: \<open>is_mgu \<sigma> {(t, t')}\<close>
        and subterm: \<open>subterm_replace vs vt s t'\<close>
      unfolding pos_superposition_inferences_def neg_superposition_inferences_def by blast
    have \<open>congruence I \<Longrightarrow> validate_clause I ({#Eq t s#} + C) \<Longrightarrow> validate_clause I ({#L#} + D) \<Longrightarrow> validate_clause I (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close> for I
    proof -
      assume cong: \<open>congruence I\<close> and \<open>validate_clause I ({#Eq t s#} + C)\<close> and \<open>validate_clause I ({#L#} + D)\<close>
      then have validate_prems_\<sigma>: \<open>validate_clause I (subst_apply_cl ({#Eq t s#} + C) \<sigma>) \<and> validate_clause I (subst_apply_cl ({#L#} + D) \<sigma>)\<close>
        using validate_instance by blast
      have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L'#} + C + D) \<sigma>) \<tau>) \<Longrightarrow> (\<exists>L \<in># subst_apply_cl ({#L'#} + C + D) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>))\<close> for \<tau>
      proof -
        assume ground_CD: \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L'#} + C + D) \<sigma>) \<tau>)\<close>
        (* the grounding of the conclusion is not necessarily a grounding of the premises, so we must extend it *)
        obtain \<upsilon> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (subst_apply_cl (subst_apply_cl ({#Eq t s#} + C + {#L#} + D) \<sigma>) \<tau>) \<upsilon>)\<close>
          using ex_ground_instance by fast
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#Eq t s#} + C + {#L#} + D) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
          using subst_cl_comp by metis
        then have \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#Eq t s#} + C) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
              and \<open>ground_cl (subst_apply_cl (subst_apply_cl ({#L#} + D) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close> by auto
        then have \<open>(\<exists>L\<in>#subst_apply_cl ({#Eq t s#} + C) \<sigma>. validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>)))
                 \<and> (\<exists>L\<in>#subst_apply_cl ({#L#} + D) \<sigma>. validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>)))\<close>
          using validate_prems_\<sigma> unfolding validate_clause_def by blast
        then consider (a) \<open>\<exists>L. (L \<in># subst_apply_cl C \<sigma> \<or> L \<in># subst_apply_cl D \<sigma>) \<and> validate_ground_lit I (subst_apply_lit L (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close> |
                      (b) \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (Eq t s) \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>)) \<and> validate_ground_lit I (subst_apply_lit (subst_apply_lit L \<sigma>) (\<tau>  \<circ>\<^sub>s \<upsilon>))\<close>
          by auto
        then have \<open>\<exists>L \<in># subst_apply_cl ({#L'#} + C + D) \<sigma>. validate_ground_lit I (subst_apply_lit L \<tau>)\<close>
        proof cases
          case a
          then obtain L
            where L_elem: \<open>L \<in># subst_apply_cl C \<sigma> \<or> L \<in># subst_apply_cl D \<sigma>\<close>
              and L_validate: \<open>validate_ground_lit I (subst_apply_lit L (\<tau> \<circ>\<^sub>s \<upsilon>))\<close> by auto
          then have \<open>vars_lit (subst_apply_lit L \<tau>) = {}\<close>
            using ground_CD by auto
          then have \<open>subst_apply_lit L (\<tau> \<circ>\<^sub>s \<upsilon>) = subst_apply_lit L \<tau>\<close>
            using subst_ground_lit [of \<open>subst_apply_lit L \<tau>\<close> \<upsilon>] subst_lit_comp [of L \<tau> \<upsilon>] by auto
          with L_elem L_validate show ?thesis by auto
        next
          case b
          then have \<open>(t \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<in> I\<close> by auto
          then have s_t_I: \<open>(s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, t \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<in> I\<close> using cong by (meson congruence.elims(1) symE)
          from subterm have \<open>subterm_replace (vs \<cdot> \<sigma>) (vt \<cdot> \<sigma>) (s \<cdot> \<sigma>) (t' \<cdot> \<sigma>)\<close>
            using subterm_replace_stable_subst by blast
          then have \<open>subterm_replace (vs \<cdot> \<sigma>) (vt \<cdot> \<sigma>) (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)\<close>
            using mgu unfolding is_mgu_def unifiers_def by auto
          then have \<open>subterm_replace (vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (s \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) (t \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>)\<close>
            using mgu subterm_replace_stable_subst by blast
          with s_t_I have vs_vt_I: \<open>(vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<in> I\<close> using subterm_replace_interp cong by blast
          consider (pos) \<open>L = Eq vt u \<and> L' = Eq vs u\<close>
                 | (neg) \<open>L = Neq vt u \<and> L' = Neq vs u\<close>
            using L_def by auto
          then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>)\<close>
          proof cases
            case pos
            with b have \<open>(vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<in> I\<close> by auto
            with vs_vt_I have \<open>(vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<in> I\<close> using cong
              by (meson congruence.elims(2) trans_def)
            then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>) \<upsilon>)\<close>
              using pos by auto
            then show ?thesis using ground_CD subst_ground_lit by fastforce
          next
            case neg
            with b have \<open>(vt \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<notin> I\<close> by auto
            with cong vs_vt_I have \<open>(vs \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>, u \<cdot> \<sigma> \<cdot> \<tau> \<cdot> \<upsilon>) \<notin> I\<close>
              by (meson congruence.elims(2) symE transD)
            then have \<open>validate_ground_lit I (subst_apply_lit (subst_apply_lit (subst_apply_lit L' \<sigma>) \<tau>) \<upsilon>)\<close>
              using neg by auto
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
  have \<open>ground_term vs \<Longrightarrow> ground_term vt \<Longrightarrow> ground_term s \<Longrightarrow> ground_term t \<Longrightarrow> s \<prec> t \<Longrightarrow> subterm_replace vs vt s t \<Longrightarrow> vs \<prec> vt\<close>
  proof (induction vs arbitrary: vt)
    case (Var x)
    then show ?case by auto (* contradiction *)
  next
    case (Fun f args)
    from \<open>subterm_replace (Fun f args) vt s t\<close> show ?case
    proof cases
      case base
      with \<open>s \<prec> t\<close> show ?thesis by auto
    next
      case (step s' t' a1 a2)
      with Fun have \<open>s' \<prec> t'\<close> by auto
      then have \<open>\<not> Fun f (a1 @ t' # a2) \<preceq> Fun f (a1 @ s' # a2)\<close>
        using term_ord_term_comp by auto
      moreover from Fun step have \<open>ground_term (Fun f (a1 @ s' # a2))\<close> and \<open>ground_term (Fun f (a1 @ t' # a2))\<close> by auto
      ultimately have \<open>Fun f (a1 @ s' # a2) \<prec> Fun f (a1 @ t' # a2)\<close>
        using term_ord_ground_total unfolding total_on_def
        by (metis (mono_tags, lifting) mem_Collect_eq)
      with step show ?thesis by auto
    qed
  qed
  then show ?thesis using assms subterm_replace_ground_left subterm_replace_ground_right by metis
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
    then obtain s s' C \<sigma> where prems_def: \<open>Rep_ground_clause ` (set (prems_of \<iota>)) = {{#Neq s s'#} + C}\<close>
                           and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl C \<sigma>\<close>
      unfolding eresolution_inferences_def by auto
    then obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close> and P_def: \<open>Rep_ground_clause P = {#Neq s s'#} + C\<close> by blast
    then have \<open>ground_cl C\<close> using Rep_ground_clause [of P] by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) = C\<close> using subst_ground_cl [of C \<sigma>] concl_def by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) \<subset># Rep_ground_clause P\<close> using P_def by auto
    then have \<open>Rep_ground_clause (concl_of \<iota>) \<prec>F Rep_ground_clause P\<close>
      by (simp add: clause_ord_def subset_implies_mult)
    then have \<open>concl_of \<iota> \<prec>G P\<close> unfolding ground_clause_ord_def by auto
    then show ?thesis using P_elem by auto
  next
    case fact
    then obtain s t u u' C \<sigma> where prems_def: \<open>Rep_ground_clause ` (set (prems_of \<iota>)) = {{#Eq u t#} + {#Eq u' s#} + C}\<close>
                               and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl ({#Eq u t#} + {#Neq t s#} + C) \<sigma>\<close>
                               and ord: \<open>\<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma> \<and> \<not> u \<cdot> \<sigma> \<preceq> t \<cdot> \<sigma>\<close>
                               and mgu: \<open>is_mgu \<sigma> {(u, u')}\<close>
      unfolding efactoring_inferences_def by auto
    then obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close> and P_def: \<open>Rep_ground_clause P = {#Eq u t#} + {#Eq u' s#} + C\<close> by blast
    then have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term u \<and> ground_term u' \<and> ground_cl C\<close>
      using Rep_ground_clause [of P] by auto
    then have \<open>ground_cl ({#Eq u t#} + {#Neq t s#} + C)\<close> by auto
    then have concl_def': \<open>Rep_ground_clause (concl_of \<iota>) = {#Eq u t#} + {#Neq t s#} + C\<close>
      using subst_ground_cl concl_def by metis
    have ord': \<open>s \<prec> t \<and> t \<prec> u\<close> 
      using ground ord subst_ground_term term_ord_ground_total unfolding total_on_def
      by (metis (mono_tags, lifting) mem_Collect_eq)
    from mgu have \<open>u' \<cdot> \<sigma> = u \<cdot> \<sigma>\<close> unfolding is_mgu_def unifiers_def by auto
    with ground have \<open>u' = u\<close> using subst_ground_term by metis
    with ord' ground term_ord_trans term_ord_ground_total have \<open>s \<prec> u' \<and> t \<prec> u'\<close>
      unfolding total_on_def
      by (metis (mono_tags, lifting) mem_Collect_eq)
    then have \<open>Neq t s \<prec>L Eq u' s\<close>
      using one_step_implies_mult [of \<open>{#u'#}\<close> \<open>{#t,t,s#}\<close> term_ord \<open>{#s#}\<close>] unfolding lit_ord_def by auto
    then have \<open>(Rep_ground_clause (concl_of \<iota>), Rep_ground_clause P) \<in> mult lit_ord\<close>
      using one_step_implies_mult [of \<open>{#Eq u' s#}\<close> \<open>{#Neq t s#}\<close> lit_ord \<open>{#Eq u t#} + C\<close>] concl_def' P_def by auto
    then show ?thesis using P_elem unfolding ground_clause_ord_def clause_ord_def by auto
  next
    case supr
    then obtain s t t' u vs vt L L' C D \<sigma> where \<open>Rep_ground_inference \<iota> = Infer [{#Eq t s#} + C, {#L#} + D] (subst_apply_cl ({#L'#} + C + D) \<sigma>)\<close>
                                            and ord: \<open>\<not> t \<cdot> \<sigma> \<preceq> s \<cdot> \<sigma> \<and> \<not> u \<cdot> \<sigma> \<preceq> vt \<cdot> \<sigma>\<close>
                                            and L_def: \<open>L = Eq vt u \<and> L' = Eq vs u \<or> L = Neq vt u \<and> L' = Neq vs u\<close>
                                            and subterm: \<open>subterm_replace vs vt s t'\<close>
                                            and mgu: \<open>is_mgu \<sigma> {(t, t')}\<close>
                                            and lit_ord: \<open>subst_apply_lit (Eq t s) \<sigma> \<prec>L subst_apply_lit L \<sigma>\<close>
                                            and eq_max: \<open>\<forall>M\<in>#C. subst_apply_lit M \<sigma> \<prec>L subst_apply_lit (Eq t s) \<sigma>\<close>
      unfolding pos_superposition_inferences_def neg_superposition_inferences_def by blast
    then obtain P1 P2 where \<open>P1 \<in> set (prems_of \<iota>)\<close>
                        and \<open>Rep_ground_clause P1 = {#Eq t s#} + C\<close>
                        and P2_elem: \<open>P2 \<in> set (prems_of \<iota>)\<close>
                        and P2_def: \<open>Rep_ground_clause P2 = {#L#} + D\<close>
                        and concl_def: \<open>Rep_ground_clause (concl_of \<iota>) = subst_apply_cl ({#L'#} + C + D) \<sigma>\<close> by fastforce
    then have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term u \<and> ground_term vt \<and> ground_cl C \<and> ground_cl D\<close>
      using Rep_ground_clause [of P1] Rep_ground_clause [of P2] L_def by auto
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
    consider (pos) \<open>L = Eq vt u \<and> L' = Eq vs u\<close> | (neg) \<open>L = Neq vt u \<and> L' = Neq vs u\<close> using L_def by auto
    then have lit_ord': \<open>L' \<prec>L L\<close>
    proof cases
      case pos
      have \<open>({#vs,u#}, {#vt, u#}) \<in> mult term_ord\<close>
        using one_step_implies_mult [of \<open>{#vt#}\<close> \<open>{#vs#}\<close> term_ord \<open>{#u#}\<close>] vs_vt_ord by auto
      with pos show ?thesis unfolding lit_ord_def by auto
    next
      case neg
      have \<open>({#vs,vs,u,u#}, {#vt,vt,u,u#}) \<in> mult term_ord\<close>
        using one_step_implies_mult [of \<open>{#vt,vt#}\<close> \<open>{#vs,vs#}\<close> term_ord \<open>{#u,u#}\<close>] vs_vt_ord by auto
      with neg show ?thesis unfolding lit_ord_def by auto
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
        then have \<open>subst_apply_lit M \<sigma> \<prec>L subst_apply_lit (Eq t s) \<sigma>\<close> using eq_max by auto
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

interpretation calculus_with_red_crit \<open>{\<bottom>G}\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause
proof
  show \<open>Red_ground_Inf N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_ground_Inf_def ground_superposition_inference_system_def by auto
next
  show \<open>B \<in> {\<bottom>G} \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> N - Red_ground_clause N \<Turnstile>G {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> {\<bottom>G}\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have \<open>Rep_ground_clause ` N \<Turnstile>F {\<bottom>F}\<close>
      unfolding ground_entail_def by auto
    then have N_unsat: \<open>congruence I \<Longrightarrow> (\<exists>C \<in> Rep_ground_clause ` N. \<not>validate_clause I C)\<close> for I
      unfolding entail_def validate_clause_def by simp
    assume \<open>\<not> N - Red_ground_clause N \<Turnstile>G {B}\<close>
    then have \<open>\<not> Rep_ground_clause ` (N - Red_ground_clause N) \<Turnstile>F {Rep_ground_clause B}\<close>
      unfolding ground_entail_def by auto
    with N_unsat obtain I where fo_I: \<open>congruence I\<close>
                          and I_model: \<open>C \<in> Rep_ground_clause ` (N - Red_ground_clause N) \<Longrightarrow> validate_clause I C\<close> for C
      unfolding entail_def validate_clause_def by metis
    with N_unsat obtain C where \<open>C \<in> Rep_ground_clause ` (Red_ground_clause N)\<close>
                          and C_novalid: \<open>\<not> validate_clause I C\<close>
      by blast
    with Red_ground_clause_entailed fo_I I_model have \<open>validate_clause I C\<close>
      unfolding ground_entail_def entail_def by blast
    with C_novalid show False by blast
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

inductive rewrite_by_trs :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where
    eq: \<open>(t, s) \<in> S \<Longrightarrow> rewrite_by_trs S t s\<close> |
    func: \<open>rewrite_by_trs S t s \<Longrightarrow> rewrite_by_trs S (Fun f (a1 @ t # a2)) (Fun f (a1 @ s # a2))\<close> |
    trans: \<open>rewrite_by_trs S u t \<Longrightarrow> rewrite_by_trs S t s \<Longrightarrow> rewrite_by_trs S u s\<close>

definition irreducible :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>irreducible TRS t = (\<forall>s. \<not>rewrite_by_trs TRS t s)\<close>

definition normal_form :: \<open>('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close>
  where \<open>normal_form TRS t s = (irreducible TRS s \<and> (s = t \<or> rewrite_by_trs TRS t s))\<close>

definition equiv_class_of_trs :: \<open>('f, 'v) trs \<Rightarrow> ('f,'v) interp\<close>
  where \<open>equiv_class_of_trs S = {(s,t) | s t. ground_term s \<and> ground_term t \<and> (\<exists>u. normal_form S s u \<and> normal_form S t u)}\<close>

abbreviation ordered :: \<open>('f, 'v) trs \<Rightarrow> bool\<close>
  where \<open>ordered S \<equiv> \<forall> (t, s) \<in> S. s \<prec> t\<close>

lemma ordered_trs_preserve_groundness:
  \<open>rewrite_by_trs S t t' \<Longrightarrow> ordered S \<Longrightarrow> ground_term t \<Longrightarrow> ground_term t'\<close>
proof (induct rule: rewrite_by_trs.induct)
  case (eq t s S)
  have \<open>\<not> ground_term s \<Longrightarrow> \<not> s \<prec> t\<close>
  proof -
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
        using le term_ord_trans by blast
    qed
    then show \<open>\<not> ground_term s \<Longrightarrow> \<not> s \<prec> t\<close> using term_ord_stable_grounding grounding by blast
  qed
  then show ?case using eq by blast
next
  case (func S t s f a1 a2)
  then show ?case by auto
next
  case (trans S u t s)
  then show ?case by fast
qed

lemma ordered_rewriting: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> rewrite_by_trs S t s \<Longrightarrow> s \<prec> t\<close>
proof -
  assume \<open>rewrite_by_trs S t s\<close>
  then show \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> s \<prec> t\<close>
  proof (induct rule: rewrite_by_trs.induct)
    case (eq t s S)
    then show ?case by blast
  next
    case (func S t s f a1 a2)
    then have \<open>ground_term (Fun f (a1 @ s # a2)) \<and> ground_term (Fun f (a1 @ t # a2))\<close> using ordered_trs_preserve_groundness by auto
    moreover have \<open>\<not> Fun f (a1 @ t # a2) \<preceq> Fun f (a1 @ s # a2)\<close> using term_ord_term_comp func by auto
    ultimately show ?case using term_ord_ground_total unfolding total_on_def
      by (metis (mono_tags, lifting) mem_Collect_eq)
  next
    case (trans S u t s)
    then have ground: \<open>ground_term s \<and> ground_term t \<and> ground_term u\<close> using ordered_trs_preserve_groundness by simp
    moreover have \<open>\<not> u \<preceq> s\<close> using term_ord_trans trans ground by blast
    then show ?case
      using ground term_ord_ground_total
      unfolding total_on_def by blast
  qed
qed

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
        then obtain s where rew: \<open>rewrite_by_trs S t s\<close> unfolding irreducible_def by blast
        show ?thesis
        proof
          assume \<open>ground_term t\<close>
          then have \<open>ground_term s \<and> s \<prec> t\<close>
            using ordered_rewriting ordered_trs_preserve_groundness \<open>ordered S\<close> rew by metis
          then obtain s' where \<open>normal_form S s s'\<close> using ind by blast
          then have \<open>irreducible S s' \<and> rewrite_by_trs S t s'\<close>
            using rewrite_by_trs.trans rew
            unfolding normal_form_def by blast
          then show \<open>\<exists>t'. normal_form S t t'\<close> unfolding normal_form_def by blast
        qed
      qed
    qed
  qed
  then show ?thesis using \<open>ground_term t\<close> by auto
qed

lemma ordered_confluent: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> rewrite_by_trs S t s \<Longrightarrow> rewrite_by_trs S t u \<Longrightarrow> (u, s) \<in> equiv_class_of_trs S\<close>
  sorry

lemma ordered_unique_normal_form: \<open>ordered S \<Longrightarrow> ground_term t \<Longrightarrow> \<exists>!s. normal_form S t s\<close>
proof -
  assume ord: \<open>ordered S\<close> and \<open>ground_term t\<close>
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
          using ord ordered_confluent \<open>ground_term t\<close>
          unfolding equiv_class_of_trs_def by blast
        then have \<open>s = u \<and> s' = u\<close> using nf_s nf_s'
          unfolding normal_form_def irreducible_def by auto
        then show ?thesis by auto
      qed
    qed
  qed
qed

(* TODO prove normalization for non-ground terms as well, or require the TRS to be a congruence only for ground terms? *)
lemma equiv_class_refl: \<open>ordered S \<Longrightarrow> refl (equiv_class_of_trs S)\<close>
  unfolding equiv_class_of_trs_def refl_on_def
  using ordered_normalizing sorry

lemma equiv_class_sym: \<open>ordered S \<Longrightarrow> sym (equiv_class_of_trs S)\<close>
  unfolding equiv_class_of_trs_def sym_def by blast

lemma equiv_class_trans: \<open>ordered S \<Longrightarrow> trans (equiv_class_of_trs S)\<close>
  unfolding trans_def equiv_class_of_trs_def
  using ordered_unique_normal_form by blast

lemma equiv_class_fun_comp: \<open>ordered S \<Longrightarrow> fun_comp (equiv_class_of_trs S)\<close>
  unfolding fun_comp_def
  sorry

lemma equiv_class_fo: \<open>ordered S \<Longrightarrow> congruence (equiv_class_of_trs S)\<close>
  using equiv_class_refl equiv_class_sym equiv_class_trans equiv_class_fun_comp by simp

definition production :: \<open>('f, 'v) trs \<Rightarrow> ('f,'v) ground_clause \<Rightarrow> ('f,'v) interp\<close>
  where \<open>production TRS C = {(t,s) | t s L C'. s \<prec> t
                                         \<and> Rep_ground_clause C = {# L #} + C'
                                         \<and> (L = Eq s t \<or> L = Eq t s)
                                         \<and> (\<forall>L' \<in># C'. L' \<prec>L L)
                                         \<and> selection (Rep_ground_clause C) = {#}
                                         \<and> \<not> validate_clause (equiv_class_of_trs TRS) (Rep_ground_clause C)
                                         \<and> \<not> validate_clause (equiv_class_of_trs (insert (t,s) TRS)) C'
                                         \<and> irreducible TRS t}\<close>

context
  fixes N :: \<open>('f,'v) ground_clause set\<close>
begin

function trs_of_clause :: \<open>('f,'v) ground_clause \<Rightarrow> ('f, 'v) trs\<close>
  where
    \<open>trs_of_clause C = (let trs_smaller = \<Union>(trs_of_clause ` {B \<in> N. B \<prec>G C})
                        in trs_smaller \<union> production trs_smaller C)\<close>
  by auto
termination using wf_ground_clause_ord by (rule local.termination [of ground_clause_ord, simplified])

end

lemma trs_of_clause_simp:
  \<open>trs_of_clause N C = \<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C}) \<union> production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close>
  by (metis trs_of_clause.simps)

definition canonical_interp_ground :: \<open>('f,'v) ground_clause set \<Rightarrow> ('f,'v) interp\<close>
  where \<open>canonical_interp_ground N = equiv_class_of_trs (\<Union>(trs_of_clause N ` N))\<close>

definition canonical_interp :: \<open>('f,'v) clause set \<Rightarrow> ('f,'v) interp\<close>
  where \<open>canonical_interp N = canonical_interp_ground (Abs_ground_clause ` N)\<close>

lemma rewrite_rel_subset:
  \<open>rewrite_by_trs S1 t s \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> rewrite_by_trs S2 t s\<close>
proof -
  assume \<open>rewrite_by_trs S1 t s\<close>
  then show \<open>S1 \<subseteq> S2 \<Longrightarrow> rewrite_by_trs S2 t s\<close>
  proof (induct rule: rewrite_by_trs.induct)
    case (eq t s S)
    then show ?case using rewrite_by_trs.eq by blast
  next
    case (func S t s f a1 a2)
    then show ?case using rewrite_by_trs.func by blast
  next
    case (trans S u t s)
    then show ?case using rewrite_by_trs.trans by blast
  qed
qed

lemma equiv_class_subset:
  \<open>ordered S2 \<Longrightarrow> S1 \<subseteq> S2 \<Longrightarrow> equiv_class_of_trs S1 \<subseteq> equiv_class_of_trs S2\<close>
proof -
  assume ord: \<open>ordered S2\<close> and subset: \<open>S1 \<subseteq> S2\<close>
  then have \<open>rewrite_by_trs S1 t s \<Longrightarrow> rewrite_by_trs S2 t s\<close>
    for s t using rewrite_rel_subset by blast
  then have \<open>(u, v) \<in> equiv_class_of_trs S1 \<Longrightarrow> (u, v) \<in> equiv_class_of_trs S2\<close> for u v
  proof -
    assume \<open>(u, v) \<in> equiv_class_of_trs S1\<close>
    then obtain w where \<open>normal_form S1 u w\<close>
                    and \<open>normal_form S1 v w\<close>
                    and ground_u: \<open>ground_term u\<close>
                    and ground_v: \<open>ground_term v\<close>
      unfolding equiv_class_of_trs_def by blast
    then consider \<open>u = v\<close> | \<open>rewrite_by_trs S1 u v\<close> | \<open>rewrite_by_trs S1 v u\<close> | \<open>rewrite_by_trs S1 u w \<and> rewrite_by_trs S1 v w\<close>
      unfolding normal_form_def by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using ord equiv_class_refl unfolding refl_on_def by simp
    next
      case 2
      then have \<open>rewrite_by_trs S2 u v\<close>
        using subset rewrite_rel_subset by blast
      moreover obtain z where \<open>normal_form S2 v z\<close> using ord ordered_normalizing ground_v by blast
      ultimately have \<open>normal_form S2 u z \<and> normal_form S2 v z\<close>
        unfolding normal_form_def
        using rewrite_by_trs.trans by blast
      then show ?thesis unfolding equiv_class_of_trs_def using ground_u ground_v by blast
    next
      case 3
      then have \<open>rewrite_by_trs S2 v u\<close>
        using subset rewrite_rel_subset by blast
      moreover obtain z where \<open>normal_form S2 u z\<close> using ord ordered_normalizing ground_u by blast
      ultimately have \<open>normal_form S2 u z \<and> normal_form S2 v z\<close>
        unfolding normal_form_def
        using rewrite_by_trs.trans by blast
      then show ?thesis unfolding equiv_class_of_trs_def using ground_u ground_v by blast
    next
      case 4
      then have rew: \<open>rewrite_by_trs S2 u w \<and> rewrite_by_trs S2 v w\<close>
        using subset rewrite_rel_subset by blast
      then have \<open>ground_term w\<close>
        using ordered_trs_preserve_groundness ord ground_u by blast
      then obtain z where \<open>normal_form S2 w z\<close> using ord ordered_normalizing by blast
      then have \<open>normal_form S2 u z \<and> normal_form S2 v z\<close>
        unfolding normal_form_def
        using rewrite_by_trs.trans rew by blast
      then show ?thesis unfolding equiv_class_of_trs_def using ground_u ground_v by blast
    qed
  qed
  then show ?thesis by auto
qed

lemma ordered_production: \<open>ordered (production N C)\<close>
  unfolding production_def by blast

lemma ordered_trs_of_clause: \<open>ordered (trs_of_clause N C)\<close>
proof (rule wf_induct [of "ground_clause_ord"])
  show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord .
next
  show \<open>\<forall>B. B \<prec>G C \<longrightarrow> ordered (trs_of_clause N B) \<Longrightarrow> ordered (trs_of_clause N C)\<close> for C
  proof -
    let ?trs_smaller = \<open>\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
    assume \<open>\<forall>B. B \<prec>G C \<longrightarrow> ordered (trs_of_clause N B)\<close>
    then have \<open>ordered ?trs_smaller\<close> by blast
    then show ?thesis
      using trs_of_clause.simps [of N C] ordered_production
      by (metis (no_types, lifting) UnE)
  qed
qed

lemma ordered_canonical_trs: \<open>ordered (\<Union> (trs_of_clause S ` S))\<close>
  using ordered_trs_of_clause by fast
 
lemma canonical_interp_fo: \<open>congruence (canonical_interp S)\<close>
  unfolding canonical_interp_def canonical_interp_ground_def
  using equiv_class_fo ordered_canonical_trs by blast

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
    then consider (a) \<open>Lmax \<prec>L L1\<close> | (b) \<open>L1 \<preceq>L Lmax\<close> using ground_L1 ground_C1 lit_ord_ground_total by metis
    then show ?thesis
    proof cases
      case a
      then have \<open>L'\<in># C1 \<Longrightarrow> L' \<preceq>L L1\<close> for L'
      proof -
        assume \<open>L' \<in># C1\<close>
        then have \<open>L' \<preceq>L Lmax\<close> using Lmax_def by auto
        then show ?thesis using a trans_lit_ord unfolding trans_def
          by (metis in_inv_image lit_ord_def)
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

lemma rewrite_requires_smaller_lhs:
  \<open>rewrite_by_trs S t t' \<Longrightarrow> ground_term t \<Longrightarrow> ordered S \<Longrightarrow> \<exists>s s'. (s, s') \<in> S \<and> ground_term s \<and> s \<preceq> t\<close>
proof (induct rule: rewrite_by_trs.induct)
  case (eq t s S)
  then show ?case by blast
next
  case (func S t s f a1 a2)
  then obtain u u' where rule_elem: \<open>(u, u') \<in> S\<close>
                     and le: \<open>u \<preceq> t\<close>
                     and ground_u: \<open>ground_term u\<close> by auto
  have \<open>t \<prec> Fun f (a1 @ t # a2) \<and> ground_term t\<close>
    using term_ord_ground_subterm_comp func by auto
  then have \<open>u \<prec> Fun f (a1 @ t # a2)\<close>
    using le term_ord_ground_trans func ground_u by blast
  then show ?case using rule_elem ground_u by blast
next
  case (trans S u t s)
  then show ?case by auto
qed

(* Lemma 3 (negative literal) *)
lemma production_lhs_greater_neg:
  assumes \<open>(t, s) \<in> production TRS C\<close>
  assumes \<open>Neq ul ur \<in># Rep_ground_clause D\<close>
  assumes \<open>D \<preceq>G C\<close>
  shows \<open>ur \<prec> t \<and> ul \<prec> t\<close>
proof -
  from assms(1) obtain L where L_def: \<open>L = Eq s t \<or> L = Eq t s\<close>
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
      using lt ground term_ord_ground_trans by auto
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
    then have \<open>L \<prec>L Neq ul ur\<close> using L_def
      by (metis add_mset_commute in_inv_image lit_ord_def mset_lit.simps(1) mset_lit.simps(2))
    then have Neq_gt: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L Neq ul ur\<close>
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
  assumes \<open>Eq ul ur \<in># Rep_ground_clause D\<close>
  assumes \<open>D \<preceq>G C\<close>
  shows \<open>ur \<preceq> t \<and> ul \<preceq> t\<close>
proof -
  from assms(1) obtain L where L_def: \<open>L = Eq s t \<or> L = Eq t s\<close>
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
      using lt ground term_ord_ground_trans by auto
    then have \<open>({#s, t#}, {#ul, ur#}) \<in> mult term_ord\<close>
      using mult_max [of \<open>{#s, t#}\<close>] by auto
    then have \<open>L \<prec>L Eq ul ur\<close> using L_def
      by (metis add_mset_commute in_inv_image lit_ord_def mset_lit.simps(1))
    then have Eq_gt: \<open>\<forall>L'\<in># Rep_ground_clause C. L' \<prec>L Eq ul ur\<close>
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
      let ?trs_smaller = \<open>\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G D})\<close>
      assume D_elem: \<open>D \<in> N\<close> and \<open>(t, s) \<in> trs_of_clause N D\<close>
      then consider (prod) \<open>(t, s) \<in> production ?trs_smaller D\<close> | (lt) \<open>(t, s) \<in> ?trs_smaller\<close>
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
        have \<open>C \<prec>G D\<close> using D'_lt C_le trans_ground_clause_ord unfolding trans_def
          by (metis ground_clause_ord_distinct ground_clause_ord_total)
        then show ?thesis using C_elem rule_elem by blast
      qed
    qed
    then show ?thesis by blast
  qed
qed

lemma equiv_clauses_production:
  \<open>{# mset_lit L. L \<in># Rep_ground_clause C1 #} = {# mset_lit L. L \<in># Rep_ground_clause C2 #} \<Longrightarrow> production TRS C1 = production TRS C2\<close>
proof -
  have subset: \<open>{# mset_lit L. L \<in># Rep_ground_clause C1 #} = {# mset_lit L. L \<in># Rep_ground_clause C2 #} \<Longrightarrow> production TRS C1 \<subseteq> production TRS C2\<close> for C1 C2
  proof
    fix s t
    assume \<open>image_mset mset_lit (Rep_ground_clause C1) = image_mset mset_lit (Rep_ground_clause C2)\<close> and \<open>(t, s) \<in> production TRS C1\<close>
    show \<open>(t, s) \<in> production TRS C2\<close> sorry
  qed
  then show \<open>{# mset_lit L. L \<in># Rep_ground_clause C1 #} = {# mset_lit L. L \<in># Rep_ground_clause C2 #} \<Longrightarrow> production TRS C1 = production TRS C2\<close> by (simp add: eq_iff)
qed

lemma equiv_clauses_trs:
  \<open>{# mset_lit L. L \<in># Rep_ground_clause C1 #} = {# mset_lit L. L \<in># Rep_ground_clause C2 #} \<Longrightarrow> trs_of_clause N C1 = trs_of_clause N C2\<close>
  by (smt Collect_cong equiv_clauses_production ground_clause_ord_total superposition.ground_clause_ord_distinct superposition.trs_of_clause.simps superposition_axioms trans_def trans_ground_clause_ord)

lemma negative_literal_normalized:
  assumes \<open>C \<in> N\<close>
  assumes \<open>Neq s t \<in># Rep_ground_clause C \<or> Neq t s \<in># Rep_ground_clause C\<close>
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
        then consider (lt) \<open>B' \<prec>G C\<close> | (eq) \<open>{# mset_lit L. L \<in># Rep_ground_clause B' #} = {# mset_lit L. L \<in># Rep_ground_clause C #}\<close> using ground_clause_ord_total by blast
        then have \<open>(lhs, rhs) \<in> trs_of_clause N C\<close>
        proof cases
          case lt
          then have \<open>(lhs, rhs) \<in> \<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close> using B'_elem rule_elem'' by blast
          then show ?thesis using trs_of_clause.simps [of N C]
            by (metis (no_types, lifting) UnCI)
        next
          case eq
          then show ?thesis using equiv_clauses_trs rule_elem'' by blast
        qed
        then show False using rule_elem by blast
      qed
      then show ?thesis using production_lhs_greater_neg rule_elem' assms(2) by blast
    qed
    (* such rules cannot be used to rewrite s *)
    have no_rewrite: \<open>rewrite_by_trs TRS s' u' \<Longrightarrow> ordered TRS \<Longrightarrow> trs_of_clause N C \<subseteq> TRS \<Longrightarrow> (\<forall>lhs rhs. (lhs, rhs) \<in> TRS - trs_of_clause N C \<longrightarrow> s \<prec> lhs) \<Longrightarrow> ground_term s' \<Longrightarrow> s' \<preceq> s \<Longrightarrow> rewrite_by_trs (trs_of_clause N C) s' u'\<close> for TRS s' u'
    proof (induct TRS s' u' rule: rewrite_by_trs.induct)
      case (eq t' s' TRS)
      then have \<open>(t', s') \<in> trs_of_clause N C\<close>
        by (meson DiffI wf_not_sym wf_term_ord)
      then show ?case using rewrite_by_trs.eq by blast
    next
      case (func TRS t' s' f a1 a2)
      have \<open>vars_term t' \<subseteq> vars_term (Fun f (a1 @ t' # a2))\<close> by auto
      then have \<open>ground_term t'\<close> using func by blast
      have \<open>t' \<prec> Fun f (a1 @ t' # a2)\<close> using func term_ord_ground_subterm_comp by blast
      then have \<open>t' \<preceq> s\<close> using func \<open>ground_term t'\<close> \<open>ground_term s\<close> term_ord_ground_trans by blast
      then show ?case using rewrite_by_trs.func func \<open>ground_term t'\<close> by blast
    next
      case (trans TRS u' t' s')
      then have \<open>ground_term t'\<close>
        using ordered_trs_preserve_groundness by blast
      then have \<open>t' \<prec> u'\<close> using trans ordered_rewriting by metis
      with trans have \<open>t' \<preceq> s\<close> using \<open>ground_term s\<close> \<open>ground_term t'\<close> term_ord_ground_trans by blast
      with trans show ?case using \<open>ground_term t'\<close> rewrite_by_trs.trans by blast
    qed
    (* combine the two arguments above to conclude *)
    consider (a) \<open>rewrite_by_trs (\<Union>(trs_of_clause N ` N)) s u\<close>
           | (b) \<open>\<exists>D \<in> N. C \<prec>G D \<and> rewrite_by_trs (trs_of_clause N D) s u\<close>
      using rew ..
    then show ?thesis
    proof cases
      case a
      have \<open>ordered (\<Union> (trs_of_clause N ` N))\<close>
        using ordered_trs_of_clause by blast
      then show ?thesis
        using a lhs_gt no_rewrite [of \<open>\<Union> (trs_of_clause N ` N)\<close> s u] \<open>ground_term s\<close> assms(1)
        unfolding normal_form_def by blast
    next
      case b
      then obtain D where rew_s_u: \<open>rewrite_by_trs (trs_of_clause N D) s u\<close>
                      and D_elem: \<open>D \<in> N\<close>
                      and D_gt: \<open>C \<prec>G D\<close> by blast
      then have \<open>(lhs, rhs) \<in> trs_of_clause N D - trs_of_clause N C \<Longrightarrow> s \<prec> lhs\<close> for lhs rhs using lhs_gt by blast
      moreover have \<open>trs_of_clause N C \<subseteq> trs_of_clause N D\<close> using assms(1) D_elem D_gt
        by (smt UN_I Un_iff mem_Collect_eq subrelI trs_of_clause_simp)
      ultimately show ?thesis
        using rew_s_u no_rewrite [of \<open>trs_of_clause N D\<close> s u] \<open>ground_term s\<close> assms(1) ordered_trs_of_clause [of N D]
        unfolding normal_form_def by blast
    qed
  qed
qed

(* during the construction of the model, a clause that is valid at some point will not be falsified later *)
(* Corollary 4 *)
lemma model_construction_monotonic:
  assumes \<open>saturated N\<close>
  assumes \<open>\<bottom>G \<notin> N\<close>
  assumes \<open>C \<in> N\<close>
  assumes \<open>validate_clause (equiv_class_of_trs (trs_of_clause N C)) (Rep_ground_clause C)\<close> (is \<open>?valid_upto C\<close>)
  shows \<open>(\<forall>D \<in> N. C \<prec>G D \<longrightarrow> validate_clause (equiv_class_of_trs (trs_of_clause N D)) (Rep_ground_clause C)) \<and>
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
        from ex_subst_Rep_ground_clause obtain \<sigma> :: \<open>('f, 'v) subst\<close> where \<open>ground_cl (subst_apply_cl (Rep_ground_clause C) \<sigma>)\<close>
          by fast
        with valid_upto_C obtain L where L_elem: \<open>L \<in># Rep_ground_clause C\<close>
                                     and \<open>validate_ground_lit (equiv_class_of_trs (trs_of_clause N C)) (subst_apply_lit L \<sigma>)\<close>
          unfolding validate_clause_def by blast
        then have valid_L: \<open>validate_ground_lit (equiv_class_of_trs (trs_of_clause N C)) L\<close>
          using subst_ground_lit [of L \<sigma>] Rep_ground_clause [of C] by (smt mem_Collect_eq)
        have valid_L' :\<open>(\<forall>D \<in> N . C \<prec>G D \<longrightarrow> validate_ground_lit (equiv_class_of_trs (trs_of_clause N D)) L) \<and> validate_ground_lit (canonical_interp_ground N) L\<close>
        proof (cases L)
          (* The literal that makes the clause true is positive. It will remain true since rules are only be added to the TRS *)
          case (Eq s t)
          with valid_L have st_elem: \<open>(s, t) \<in> equiv_class_of_trs (trs_of_clause N C)\<close>
            using validate_ground_lit.simps(1) by blast
          moreover have \<open>\<forall>D \<in> N. C \<prec>G D \<longrightarrow> trs_of_clause N C \<subseteq> trs_of_clause N D\<close> using C_elem
            by (smt UN_I Un_iff mem_Collect_eq subsetI trs_of_clause_simp)
          ultimately have st_elem': \<open>\<forall>D \<in> N. C \<prec>G D \<longrightarrow> (s, t) \<in> equiv_class_of_trs (trs_of_clause N D)\<close>
            using equiv_class_subset ordered_trs_of_clause [of N] by (meson subsetD)
          from st_elem C_elem have st_elem'': \<open>(s, t) \<in> equiv_class_of_trs (\<Union>(trs_of_clause N ` N))\<close>
            using equiv_class_subset ordered_canonical_trs [of N] by blast
          show ?thesis unfolding canonical_interp_ground_def using Eq st_elem' st_elem''
            by (meson validate_ground_lit.simps(1))
        next
          (* Rules added later cannot be used to rewrite terms occurring in a negative literal *)
          case (Neq s t)
          with valid_L have not_equiv: \<open>(s, t) \<notin> equiv_class_of_trs (trs_of_clause N C)\<close>
            using validate_ground_lit.simps(2) by blast
          show ?thesis
          proof -
            have \<open>D \<in> N \<Longrightarrow> C \<prec>G D \<Longrightarrow> validate_ground_lit (equiv_class_of_trs (trs_of_clause N D)) L\<close> for D
            proof -
              assume D_elem: \<open>D \<in> N\<close> and D_gt: \<open>C \<prec>G D\<close>
              have \<open>normal_form (trs_of_clause N D) s u \<Longrightarrow> normal_form (trs_of_clause N C) s u\<close> for u
                using negative_literal_normalized Neq L_elem C_elem D_elem D_gt by blast
              moreover have \<open>normal_form (trs_of_clause N D) t u \<Longrightarrow> normal_form (trs_of_clause N C) t u\<close> for u
                using negative_literal_normalized Neq L_elem C_elem D_elem D_gt by blast
              ultimately have \<open>(s, t) \<notin> equiv_class_of_trs (trs_of_clause N D)\<close>
                using not_equiv
                unfolding equiv_class_of_trs_def by blast
              then show ?thesis using Neq validate_ground_lit.simps(2) by blast
            qed
            moreover have \<open>validate_ground_lit (canonical_interp_ground N) L\<close>
            proof -
              have \<open>normal_form (\<Union>(trs_of_clause N ` N)) s u \<Longrightarrow> normal_form (trs_of_clause N C) s u\<close> for u
                using negative_literal_normalized Neq L_elem C_elem by blast
              moreover have \<open>normal_form (\<Union>(trs_of_clause N ` N)) t u \<Longrightarrow> normal_form (trs_of_clause N C) t u\<close> for u
                using negative_literal_normalized Neq L_elem C_elem by blast
              ultimately have \<open>(s, t) \<notin> canonical_interp_ground N\<close>
                using not_equiv
                unfolding canonical_interp_ground_def equiv_class_of_trs_def by blast
              then show ?thesis using Neq by auto
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

lemma equality_in_equiv_class:
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
      using left rewrite_by_trs.eq rewrite_by_trs.trans
      unfolding normal_form_def by fast
    then show ?thesis using ground_s ground_t unfolding equiv_class_of_trs_def normal_form_def by blast
  next
    case right
    with ord ordered_normalizing obtain t' where \<open>normal_form TRS t t'\<close> using ground_t by blast
    then have \<open>rewrite_by_trs TRS s t' \<and> irreducible TRS t' \<and> (t' = t \<or> rewrite_by_trs TRS t t')\<close>
      using right rewrite_by_trs.eq rewrite_by_trs.trans
      unfolding normal_form_def by fast
    then show ?thesis using ground_s ground_t unfolding equiv_class_of_trs_def normal_form_def by blast
  qed
qed

(* Corollary 5 *)
lemma productive_clause_satisfied:
  assumes \<open>production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C \<noteq> {}\<close>
  shows \<open>validate_clause (equiv_class_of_trs (trs_of_clause N C)) (Rep_ground_clause C)\<close>
proof -
  from assms obtain t s where ts_elem: \<open>(t, s) \<in> production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C\<close> by fast
  then obtain L C' where L_def: \<open>L = Eq s t \<or> L = Eq t s\<close>
                     and C_def: \<open>Rep_ground_clause C = {# L #} + C'\<close> unfolding production_def by blast
  from ts_elem have rewrite: \<open>(t, s) \<in> trs_of_clause N C\<close>
    by (metis (no_types, lifting) Un_iff trs_of_clause_simp)
  from C_def have L_elem: \<open>L \<in># Rep_ground_clause C\<close> by auto
  then have L_ground: \<open>ground_lit L\<close> using C_def Rep_ground_clause by fast
  then have \<open>ground_term s \<and> ground_term t\<close> using L_def by force
  then have \<open>(t, s) \<in> equiv_class_of_trs (trs_of_clause N C) \<and> (s, t) \<in> equiv_class_of_trs (trs_of_clause N C)\<close>
    using rewrite equality_in_equiv_class ordered_trs_of_clause by presburger
  then have \<open>validate_ground_lit (equiv_class_of_trs (trs_of_clause N C)) L\<close>
    using L_def validate_ground_lit.simps(1) by blast
  then show ?thesis
    using L_elem L_ground subst_ground_lit
    unfolding validate_clause_def by metis
qed

(* Theorem 6 *)
lemma model_construction:
  assumes \<open>saturated N\<close>
  assumes \<open>\<bottom>G \<notin> N\<close>
  assumes \<open>C \<in> N\<close>
  shows \<open>(production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C = {} \<longleftrightarrow> validate_clause (equiv_class_of_trs (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C}))) (Rep_ground_clause C))
         \<and> validate_clause (equiv_class_of_trs (trs_of_clause N C)) (Rep_ground_clause C)\<close> (is \<open>(?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C\<close>)
proof -
  have \<open>C \<in> N \<longrightarrow> ((?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C)\<close>
  proof (rule wf_induct [of \<open>ground_clause_ord\<close>])
    show \<open>wf ground_clause_ord\<close> using wf_ground_clause_ord .
  next
    show \<open>\<forall>B. B \<prec>G C \<longrightarrow> B \<in> N \<longrightarrow> ((?P1 B \<longleftrightarrow> ?P2 B) \<and> ?P3 B) \<Longrightarrow> C \<in> N \<longrightarrow> ((?P1 C \<longleftrightarrow> ?P2 C) \<and> ?P3 C)\<close> for C
    proof -
      let ?trs_smaller = \<open>\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})\<close>
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
              consider (a) \<open>selection (Rep_ground_clause C) \<noteq> {#} \<or> (\<exists>s t. (Neq s t) \<in># Rep_ground_clause C \<and> (\<forall>L' \<in># Rep_ground_clause C. L' \<prec>L (Neq s t)))\<close>
                     | (c) \<open>selection (Rep_ground_clause C) = {#} \<and> (\<forall>s t. (Neq s t) \<in># Rep_ground_clause C \<longrightarrow> (\<exists>L. L \<in># Rep_ground_clause C \<and> (Neq s t) \<preceq>L L))\<close> by blast         
              then show \<open>?P2 C\<close>
              proof cases
                case a
                then obtain s t where select: \<open>(Neq s t) \<in># selection (Rep_ground_clause C) \<or> (selection (Rep_ground_clause C) = {#} \<and> (Neq s t) \<in># Rep_ground_clause C \<and> (\<forall>L' \<in># Rep_ground_clause C. L' \<prec>L (Neq s t)))\<close>
                  using selection_neg_lit
                  by (metis mset_lit.cases multiset_nonemptyE)
                then have s_t_elem: \<open>(Neq s t) \<in># Rep_ground_clause C\<close> using selection_subset
                  by (meson mset_subset_eqD)
                then have L_ground: \<open>ground_lit (Neq s t)\<close> using Rep_ground_clause by fast
                consider (a1) \<open>(s, t) \<in> equiv_class_of_trs ?trs_smaller\<close>
                       | (a2) \<open>(s, t) \<notin> equiv_class_of_trs ?trs_smaller\<close> by blast
                then show ?thesis
                proof cases
                  case a1
                  consider (eq) \<open>s = t\<close> | (lt) \<open>s \<prec> t\<close> | (gt) \<open>t \<prec> s\<close>
                    using L_ground term_ord_ground_total unfolding total_on_def by auto
                  then show ?thesis
                  proof cases
                    case eq
                    then obtain D where C_def: \<open>Rep_ground_clause C = {#Neq s s#} + D\<close> using s_t_elem
                      by (metis insert_DiffM2 union_commute)
                    (* there exists an equality resolution inference from C *)
                    have \<open>Infer [{# Neq s s#} + D] D \<in> eresolution_inferences\<close>
                    proof -
                      let ?\<sigma> = \<open>Var\<close> (* identity substitution *)
                      have \<open>Infer [{#Neq s s#} + D] D = Infer [{#Neq s s#} + D] (subst_apply_cl D ?\<sigma>)\<close>
                        using C_def Rep_ground_clause subst_ground_cl [of D ?\<sigma>]
                        by (smt mem_Collect_eq union_iff)
                      moreover have \<open>is_mgu ?\<sigma> {(s, s)}\<close> by auto
                      moreover have \<open>(selection ({#Neq s s#} + D) = {#} \<and> (\<forall>M\<in>#D. subst_apply_lit M ?\<sigma> \<preceq>L subst_apply_lit (Neq s s) ?\<sigma>)) \<or> Neq s s \<in># selection ({#Neq s s#} + D)\<close>
                      proof -
                        consider (a) \<open>(Neq s s) \<in># selection ({#Neq s s#} + D)\<close>
                               | (b) \<open>selection ({#Neq s s#} + D) = {#} \<and> (\<forall>L' \<in># D. L' \<prec>L (Neq s s))\<close>
                          using eq C_def select by auto
                        moreover have \<open>subst_apply_lit L ?\<sigma> = L\<close> for L :: \<open>('f, 'v) literal\<close> proof (cases L; auto) qed
                        ultimately show ?thesis by auto
                      qed
                      ultimately show ?thesis unfolding eresolution_inferences_def by blast
                    qed
                    moreover have D_rep: \<open>Rep_ground_clause (Abs_ground_clause D) = D\<close>
                      using Abs_ground_clause_inverse C_def
                      by (smt Rep_ground_clause mem_Collect_eq union_iff)
                    ultimately have \<open>Infer [C] (Abs_ground_clause D) \<in> ground_superposition_inference_system\<close>
                      unfolding ground_superposition_inference_system_def using Rep_ground_inference.simps C_def by auto
                    then have \<open>Infer [C] (Abs_ground_clause D) \<in> Red_ground_Inf N\<close>
                      using C_elem assms(1) unfolding saturated_def ground_inf.Inf_from_def by auto
                    (* by the saturation hypothesis, the conclusion D is entailed by smaller clauses in N *)
                    then obtain N' where N'_subset: \<open>N' \<subseteq> N\<close>
                                     and entail: \<open>Rep_ground_clause ` N' \<Turnstile>F {D}\<close>
                                     and C_gt: \<open>\<forall>B \<in> N'. B \<prec>G C\<close>
                      unfolding Red_ground_Inf_def ground_entail_def using D_rep by auto
                    (* by induction, the entailing clauses are true in the model *)
                    have \<open>B \<in> Rep_ground_clause ` N' \<Longrightarrow> validate_clause (equiv_class_of_trs ?trs_smaller) B\<close> for B
                    proof -
                      assume B_elem: \<open>B \<in> Rep_ground_clause ` N'\<close>
                      then have \<open>Abs_ground_clause B \<in> N'\<close>
                        using Rep_ground_clause_inverse
                        by (metis imageE)
                      then have Abs_B_elem: \<open>Abs_ground_clause B \<prec>G C \<and> Abs_ground_clause B \<in> N\<close> using C_gt N'_subset by blast
                      then have \<open>validate_clause (equiv_class_of_trs (trs_of_clause N (Abs_ground_clause B))) (Rep_ground_clause (Abs_ground_clause B))\<close>
                        using ind Rep_ground_clause_inverse by blast
                      then have \<open>validate_clause (equiv_class_of_trs (trs_of_clause N C)) (Rep_ground_clause (Abs_ground_clause B))\<close>
                        using Abs_B_elem model_construction_monotonic [of N \<open>Abs_ground_clause B\<close>] assms(1,2) C_elem by blast
                      then have \<open>validate_clause (equiv_class_of_trs (trs_of_clause N C)) B\<close>
                        using B_elem Rep_ground_clause Abs_ground_clause_inverse
                        by (smt imageE)
                      then show ?thesis using B_elem trs_def by argo
                    qed
                    (* hence, D is true in the model *)
                    then have \<open>validate_clause (equiv_class_of_trs ?trs_smaller) D\<close>
                      using entail equiv_class_fo ordered_trs_of_clause unfolding entail_def
                      by (metis (no_types, lifting) insert_iff trs_def)
                    (* C includes D, so its true as well *)
                    moreover have \<open>D \<subseteq># Rep_ground_clause C\<close> using C_def by auto
                    ultimately show ?thesis using validate_subset by blast
                  next
                    case lt
                    then show ?thesis sorry
                  next
                    case gt
                    then show ?thesis sorry
                  qed
                next
                  case a2
                  show ?thesis sorry
                qed
              next
                case b
                then show ?thesis sorry
              next
                case c
                then show ?thesis sorry
              qed
            qed
          next
            show \<open>?P2 C \<Longrightarrow> ?P1 C\<close> unfolding production_def by blast
          qed
          have P3: \<open>validate_clause (equiv_class_of_trs (trs_of_clause N C)) (Rep_ground_clause C)\<close>
          proof (cases \<open>production (\<Union>(trs_of_clause N ` {B \<in> N. B \<prec>G C})) C = {}\<close>)
            case True (* clause is not productive, must be true as shown above *)
            then have \<open>validate_clause (equiv_class_of_trs (\<Union> (trs_of_clause N ` {B \<in> N. B \<prec>G C}))) (Rep_ground_clause C)\<close>
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

lemma canonical_interp_model:
  assumes \<open>saturated N\<close>
  assumes \<open>\<bottom>G \<notin> N\<close>
  assumes \<open>C \<in> N\<close>
  shows \<open>validate_clause (canonical_interp_ground N) (Rep_ground_clause C)\<close>
  using model_construction canonical_interp_monotonic assms by blast

interpretation static_refutational_complete_calculus \<open>{\<bottom>G}\<close> \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_ground_Inf Red_ground_clause
proof
  have \<open>saturated N \<Longrightarrow> \<forall>C \<in> N. C \<notin> {\<bottom>G} \<Longrightarrow> B \<in> {\<bottom>G} \<Longrightarrow> \<not> N \<Turnstile>G {B}\<close> for B N
  proof
    assume saturated: \<open>saturated N\<close> and no_empty_cl: \<open>\<forall>C \<in> N. C \<notin> {\<bottom>G}\<close> and \<open>B \<in> {\<bottom>G}\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have \<open>Rep_ground_clause ` N \<Turnstile>F {\<bottom>F}\<close>
      unfolding ground_entail_def by auto
    then have N_unsat: \<open>congruence I \<Longrightarrow> (\<exists>C \<in> Rep_ground_clause ` N. \<not> validate_clause I C)\<close> for I
      unfolding entail_def validate_clause_def by auto
    (* model for N *)
    have \<open>C \<in> N \<Longrightarrow> validate_clause (canonical_interp (Rep_ground_clause ` N)) (Rep_ground_clause C)\<close> for C
      using canonical_interp_model saturated no_empty_cl by blast
    with canonical_interp_fo and N_unsat show False by blast
  qed
  then show \<open>B \<in> {\<bottom>G} \<Longrightarrow> saturated N \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> \<exists>B'\<in>{\<bottom>G}. B' \<in> N\<close> for B N by blast
qed

(* First-order calculus *)

(* To ground first-order inferences, we need their unifier *)
(*datatype 'b fo_inference = Fo_Infer (inf: \<open>'b fclause inference\<close>) (subst: \<open>'b subst\<close>)*)

definition fo_eresolution_inferences :: \<open>'a clause inference set\<close> where
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