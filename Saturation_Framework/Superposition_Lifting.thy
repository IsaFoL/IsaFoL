(*  Title:       Superposition_Lifting
    Author:      Simon Robillard <simon.robillard at chalmers.se>, 2018
*)

theory Superposition_Lifting
  imports Nonground_Calculus_Lifting SuperCalc.superposition
begin

(* We only consider non-extended clauses (trms_ecl must be empty). The definition of completeness
   for extended clauses is too complex to fit in the framework, since its requires a saturated set
   of (possibly extended) clauses obtained from an initial set of non-extended clauses. *)
typedef 'a gclause = \<open>{C :: 'a eclause. finite (cl_ecl C)
                                               \<and> ground_clause (cl_ecl C)
                                               \<and> trms_ecl C = {}}\<close>
apply(rule_tac x = \<open>Ecl {} {}\<close> in exI)
  by simp

typedef 'a fclause = \<open>{C :: 'a eclause. finite (cl_ecl C)
                                               \<and> trms_ecl C = {}}\<close>
apply(rule_tac x = \<open>Ecl {} {}\<close> in exI)
  by simp

context basic_superposition
begin

definition gclause_entails :: \<open>'a gclause set \<Rightarrow> 'a gclause set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50)
  where
\<open>N1 \<Turnstile>G N2 \<equiv> \<forall>C2 \<in> N2. set_entails_clause (cl_ecl ` Rep_gclause ` N1) (cl_ecl (Rep_gclause C2))\<close>

abbreviation empty_gclauses :: \<open>'a gclause set\<close>
  where \<open>empty_gclauses \<equiv> {C. cl_ecl (Rep_gclause C) = {}}\<close>

lemma empty_clause_entails: \<open>set_entails_clause {{}} C\<close>
  unfolding set_entails_clause_def by auto

interpretation consequence_relation empty_gclauses \<open>(\<Turnstile>G)\<close>
proof
  show \<open>B \<in> empty_gclauses \<Longrightarrow> {B} \<Turnstile>G N1\<close> for B :: \<open>'a gclause\<close> and N1
    unfolding gclause_entails_def using empty_clause_entails by auto
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>G N2\<close> for N2 N1 :: \<open>'a gclause set\<close>
    unfolding gclause_entails_def
    by (simp add: set_entails_clause_member set_mp)
  show \<open>\<forall>C\<in>N2. N1 \<Turnstile>G {C} \<Longrightarrow> N1 \<Turnstile>G N2\<close> for N2 N1 :: \<open>'a gclause set\<close>
    unfolding gclause_entails_def by fast
  show \<open>N1 \<Turnstile>G N2 \<Longrightarrow> N2 \<Turnstile>G N3 \<Longrightarrow> N1 \<Turnstile>G N3\<close> for N1 N2 N3 :: \<open>'a gclause set\<close>
    unfolding gclause_entails_def set_entails_clause_def by force
qed

(* since the inferences as defined in Supercalc.superposition produce extended clauses, we need
   to modify their conclusions *)
fun gcl_remove_trms :: \<open>'a eclause \<Rightarrow> 'a gclause\<close>
  where \<open>gcl_remove_trms C = Abs_gclause (Ecl (cl_ecl C) {})\<close>

lemma gcl_remove_trms_cl_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> cl_ecl (Rep_gclause (gcl_remove_trms C)) = cl_ecl C\<close>
  using Abs_gclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

lemma gcl_remove_trms_trms_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> trms_ecl (Rep_gclause (gcl_remove_trms C)) = {}\<close>
  using Abs_gclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

(* the definitions of ground inferences could be more precise and require \<sigma> = [] and C' = cl_ecl C,
   but this information is not useful and makes it more difficult to show that our notion of
   saturation implies saturation as defined in Supercalc.superposition *)
definition ground_reflexion_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_reflexion_inferences = {Infer [P] (gcl_remove_trms C) | P C. \<exists> \<sigma> C'. reflexion (Rep_gclause P) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

definition ground_factorization_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_factorization_inferences = {Infer [P] (gcl_remove_trms C) | P C. \<exists> \<sigma> C'. factorization (Rep_gclause P) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

definition ground_superposition_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_superposition_inferences = {Infer [P1 , P2] (gcl_remove_trms C) | P1 P2 C. \<exists> \<sigma> C'. superposition (Rep_gclause P1) (Rep_gclause P2) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

abbreviation ground_superposition_inference_system :: \<open>'a gclause inference set\<close>
  where
\<open>ground_superposition_inference_system \<equiv> ground_reflexion_inferences
                                       \<union> ground_factorization_inferences
                                       \<union> ground_superposition_inferences\<close>

interpretation ground_inf: sound_inference_system \<open>empty_gclauses\<close> \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system
proof
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>G {concl_of \<iota>}\<close> for \<iota>
  proof -
    assume \<open>\<iota> \<in> ground_superposition_inference_system\<close>
    then consider (a) \<open>\<iota> \<in> ground_reflexion_inferences\<close>
      | (b) \<open>\<iota> \<in> ground_factorization_inferences\<close>
      | (c) \<open>\<iota> \<in> ground_superposition_inferences\<close>
      by auto
    then show \<open>set (prems_of \<iota>) \<Turnstile>G {concl_of \<iota>}\<close>
    proof cases
      case a
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (gcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_gclause P))\<close>
          and reflexion: \<open>reflexion (Rep_gclause P) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_reflexion_inferences_def Rep_gclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_gclause P)) (cl_ecl C)\<close>
        using reflexion_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (gcl_remove_trms C)) = cl_ecl C\<close>
        using gcl_remove_trms_cl_ecl ground_C reflexion_preserves_finiteness finite_P reflexion by blast
      ultimately show ?thesis
        unfolding gclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case b
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (gcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_gclause P))\<close>
          and factorization: \<open>factorization (Rep_gclause P) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_factorization_inferences_def Rep_gclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_gclause P)) (cl_ecl C)\<close>
        using factorization_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (gcl_remove_trms C)) = cl_ecl C\<close>
        using gcl_remove_trms_cl_ecl ground_C factorization_preserves_finiteness finite_P factorization by blast
      ultimately show ?thesis
        unfolding gclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case c
      then obtain P1 P2 C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] (gcl_remove_trms C)\<close>
          and finite_P1: \<open>finite (cl_ecl (Rep_gclause P1))\<close>
          and finite_P2: \<open>finite (cl_ecl (Rep_gclause P2))\<close>
          and superposition: \<open>superposition (Rep_gclause P1) (Rep_gclause P2) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_superposition_inferences_def Rep_gclause by fastforce
      then have \<open>set_entails_clause {cl_ecl (Rep_gclause P1), cl_ecl (Rep_gclause P2)} (cl_ecl C)\<close>
        using superposition_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (gcl_remove_trms C)) = cl_ecl C\<close>
        using gcl_remove_trms_cl_ecl ground_C superposition_preserves_finiteness finite_P1 finite_P2 superposition by blast
      ultimately show ?thesis
        unfolding gclause_entails_def using \<iota>_def by auto
    qed
  qed
qed

(* orderings on clauses and sets of clauses *)
definition gclause_ord :: \<open>('a gclause \<times> 'a gclause) set\<close>
  where \<open>gclause_ord \<equiv> {(C,D). (mset_ecl (Rep_gclause C, []), mset_ecl (Rep_gclause D, [])) \<in> mult (mult (trm_ord))}\<close>

lemma gclause_ord_trans: \<open>trans gclause_ord\<close>
  by (metis (no_types, lifting) gclause_ord_def mult_def transI transitive_closure_trans(2) case_prodD case_prodI mem_Collect_eq)

lemma gclause_ord_wf: \<open>wf gclause_ord\<close>
proof -
  have \<open>wf (mult trm_ord)\<close> using trm_ord_wf and wf_mult  by auto
  then have \<open>wf (mult (mult trm_ord))\<close> using wf_mult  by auto
  thus ?thesis 
    using gclause_ord_def and measure_wf [of \<open>(mult (mult trm_ord))\<close> gclause_ord \<open>\<lambda>C. mset_ecl (Rep_gclause C, [])\<close>] by blast
qed

definition gclause_set_ord :: \<open>('a gclause set \<times> 'a gclause set) set\<close>
  where \<open>gclause_set_ord = {(S1, S2). (mset_set S1, mset_set S2) \<in> mult gclause_ord}\<close>

lemma gclause_set_ord_wf: \<open>wf gclause_set_ord\<close>
proof -
  have \<open>wf (mult gclause_ord)\<close>
    using wf_mult gclause_ord_wf by auto
  then show ?thesis
    using gclause_set_ord_def measure_wf [of \<open>mult gclause_ord\<close> gclause_set_ord mset_set] by blast
qed

lemma substitution_irrelevance: \<open>mset_ecl (Rep_gclause D, \<sigma>) = mset_ecl (Rep_gclause D, [])\<close>
proof -
  from Rep_gclause have ground: \<open>ground_clause (cl_ecl (Rep_gclause D))\<close> by blast
  then have \<open>L \<in># mset_set (cl_ecl (Rep_gclause D)) \<Longrightarrow> subst_lit L \<sigma> = subst_lit L []\<close> for L
    by (metis substs_preserve_ground_lit elem_mset_set empty_iff mset_set.infinite set_mset_empty)
  then have eq: \<open>L \<in># mset_set (cl_ecl (Rep_gclause D)) \<Longrightarrow> mset_lit (subst_lit L \<sigma>) = mset_lit (subst_lit L [])\<close> for L
    by auto
  have \<open>mset_ecl (Rep_gclause D, \<sigma>) = {# (mset_lit (subst_lit L \<sigma>)). L \<in># (mset_set (cl_ecl (Rep_gclause D))) #}\<close> by auto
  with eq have \<open>mset_ecl (Rep_gclause D, \<sigma>) = {# (mset_lit (subst_lit L [])). L \<in># (mset_set (cl_ecl (Rep_gclause D))) #}\<close>
    using image_mset_cong by force
  then show ?thesis by auto
qed

(* the original definition of redundant_clause does not fit our framework because it also accounts
   for entailment by equal clauses, not just smaller ones. For example, this implies that any
   clause C is redundant in {C}, even ones that are not redundant in {}.
   
   The original definition doesn't require a finite set either. Proving that such a set always
   exists would require a proof of compactness.
*)
definition Red_gclause :: \<open>'a gclause set \<Rightarrow> 'a gclause set\<close> where
\<open>Red_gclause N = {C. \<exists>N' \<subseteq> N. finite N' \<and> N' \<Turnstile>G {C} \<and> (\<forall>D \<in> N'. (D, C) \<in> gclause_ord)}\<close>

definition Red_Inf_sup :: \<open>'a gclause set \<Rightarrow> 'a gclause inference set\<close> where
\<open>Red_Inf_sup N = {\<iota>. \<iota> \<in> ground_superposition_inference_system
                 \<and> (\<exists>N' \<subseteq> N. finite N' \<and> N' \<Turnstile>G {concl_of \<iota>} \<and> (\<forall>D \<in> N'. \<exists>P \<in> set (prems_of \<iota>). (D, P) \<in> gclause_ord))}\<close>

(* connect our definition of redundant inference to the definition used in SuperCalc.superposition *)
lemma Red_Inf_redundant_inference:
  assumes \<open>\<iota> \<in> Red_Inf_sup N\<close>
  shows \<open>redundant_inference (Rep_gclause (concl_of \<iota>)) (Rep_gclause ` N) (Rep_gclause ` set (prems_of \<iota>)) \<sigma>\<close>
proof -
  from assms obtain N' where i: \<open>N' \<subseteq> N\<close>
                         and ii: \<open>N' \<Turnstile>G {concl_of \<iota>}\<close>
                         and iii: \<open>(\<forall>D\<in>N'. \<exists>P\<in>set (prems_of \<iota>). (D, P) \<in> gclause_ord)\<close>
    unfolding Red_Inf_sup_def by auto
  let ?S = \<open>instances (Rep_gclause ` N')\<close>
  have \<open>?S \<subseteq> instances (Rep_gclause ` N)\<close>
    using i unfolding instances_def by blast
  moreover have \<open>set_entails_clause (clset_instances ?S) (cl_ecl (Rep_gclause (concl_of \<iota>)))\<close>
  proof -
    have \<open>cl_ecl ` Rep_gclause ` N' \<subseteq> clset_instances (instances (Rep_gclause ` N'))\<close>
    proof
      fix cl_C
      assume \<open>cl_C \<in> cl_ecl ` Rep_gclause ` N'\<close>
      then obtain C where cl_C_def: \<open>cl_C = cl_ecl (Rep_gclause C)\<close> and C_elem: \<open>C \<in> N'\<close> by auto
      then have ground_cl_C: \<open>ground_clause cl_C\<close> using Rep_gclause [of C] by auto
      then have subst_irrelevant: \<open>subst_cl cl_C [] = cl_C\<close>
        using substs_preserve_ground_clause by blast
      then have \<open>(Rep_gclause C, []) \<in> instances (Rep_gclause ` N')\<close>
        unfolding instances_def using cl_C_def C_elem ground_cl_C by auto
      then show \<open>cl_C \<in> clset_instances (instances (Rep_gclause ` N'))\<close>
        unfolding clset_instances_def using cl_C_def subst_irrelevant by auto
    qed
    then show ?thesis using ii unfolding gclause_entails_def set_entails_clause_def by fastforce
  qed
  moreover have \<open>\<forall>x \<in> ?S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (concl_of \<iota>)))\<close>
  proof
    fix x
    assume \<open>x \<in> ?S\<close>
    then have \<open>trms_ecl (fst x) = {}\<close> unfolding instances_def using Rep_gclause by fastforce
    then show \<open>subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (concl_of \<iota>)))\<close>
      unfolding subterms_inclusion_def by auto
  qed
  moreover have \<open>\<forall>x \<in> ?S. \<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). (x, (D, \<sigma>)) \<in> ecl_ord\<close>
  proof
    fix x
    assume \<open>x \<in> ?S\<close>
    then obtain C where \<open>C \<in> N'\<close> and C_def: \<open>Rep_gclause C = fst x\<close> unfolding instances_def by auto
    then obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close>
                    and \<open>(mset_ecl (Rep_gclause C, []), mset_ecl (Rep_gclause P, [])) \<in> mult (mult trm_ord)\<close>
      using iii unfolding gclause_ord_def by auto
    then have \<open>(mset_ecl (fst x, snd x), mset_ecl (Rep_gclause P, \<sigma>)) \<in> mult (mult trm_ord)\<close>
      using C_def substitution_irrelevance by metis
    then have \<open>(x, (Rep_gclause P, \<sigma>)) \<in> ecl_ord\<close> unfolding ecl_ord_def by auto
    moreover have \<open>Rep_gclause P \<in> Rep_gclause ` set (prems_of \<iota>)\<close> using P_elem by auto
    ultimately show \<open>\<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). (x, (D, \<sigma>)) \<in> ecl_ord\<close> by auto
  qed
  ultimately show ?thesis unfolding redundant_inference_def by auto
qed

lemma redundant_inference_gcl_remove_trms:
  assumes \<open>redundant_inference (Rep_gclause (gcl_remove_trms C)) N P \<sigma>\<close>
  assumes \<open>ground_clause (cl_ecl C)\<close>
  assumes \<open>finite (cl_ecl C)\<close>
  shows \<open>redundant_inference C N P \<sigma>\<close>
proof -
  from assms obtain S where i: \<open>S \<subseteq> instances N\<close>
                        and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_gclause (gcl_remove_trms C)))\<close>
                        and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (gcl_remove_trms C)))\<close>
                        and iv: \<open>\<forall>x \<in> S. \<exists>D \<in> P. (x,(D,\<sigma>)) \<in> ecl_ord\<close>
    unfolding redundant_inference_def by auto
  with ii have ii': \<open>set_entails_clause (clset_instances S) (cl_ecl C)\<close>
    using gcl_remove_trms_cl_ecl assms by auto
  with iii have \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) {}\<close>
    using gcl_remove_trms_trms_ecl assms by auto
  then have iii': \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) X\<close> for X
    unfolding subterms_inclusion_def by fast
  then show \<open>redundant_inference C N P \<sigma>\<close> 
    unfolding redundant_inference_def 
    using i ii' iii' iv by auto
qed

lemma Red_gclause_entails: \<open>N \<Turnstile>G Red_gclause N\<close>
proof (rule all_formulas_entailed)
  show \<open>\<forall>C\<in>Red_gclause N. N \<Turnstile>G {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_gclause N\<close>
    then obtain N' where \<open>N' \<subseteq> N\<close> and \<open>N' \<Turnstile>G {C}\<close> unfolding Red_gclause_def by auto
    then show \<open>N \<Turnstile>G {C}\<close> using subset_entailed [of \<open>N'\<close> N] entails_trans [of N N' \<open>{C}\<close>] by auto
  qed
qed

lemma smaller_gclause_set:
  assumes \<open>finite N\<close>
  assumes \<open>C \<in> N\<close>
  assumes \<open>\<forall>C' \<in> N'. (C', C) \<in> gclause_ord\<close>
  shows \<open>(N - {C} \<union> N', N) \<in> gclause_set_ord\<close>
proof -
  have eq: \<open>mset_set (N - {C}) + {#C#} = mset_set N\<close> using assms(1,2)
    using mset_set.remove by fastforce
  have \<open>\<forall>C'\<in>#mset_set N'. \<exists>D\<in>#{#C#}. (C', D) \<in> gclause_ord\<close> using assms(3)
    by (metis elem_mset_set empty_iff mset_set.infinite set_mset_add_mset_insert set_mset_empty singletonI)
  then have \<open>(mset_set (N - {C}) + mset_set N', mset_set (N - {C}) + {#C#}) \<in> mult gclause_ord\<close>
    using one_step_implies_mult [of \<open>{#C#}\<close> \<open>mset_set N'\<close> gclause_ord \<open>mset_set (N - {C})\<close>] by auto
  with eq have i: \<open>(mset_set (N - {C}) + mset_set N', mset_set N) \<in> mult gclause_ord\<close> by auto
  have \<open>mset_set (N - {C} \<union> N') \<subseteq># mset_set (N - {C}) + mset_set N'\<close>
  by (smt UnE count_mset_set(1) count_mset_set(3) finite_Un leI mset_set.infinite mset_subset_eq_add_left mset_subset_eq_add_right subseteq_mset_def zero_order(3))
  then have ii: \<open>mset_set (N - {C} \<union> N') = mset_set (N - {C}) + mset_set N' \<or> (mset_set (N - {C} \<union> N'), mset_set (N - {C}) + mset_set N') \<in> mult gclause_ord\<close>
    using multisets_continued.multiset_order_inclusion_eq gclause_ord_trans by auto
  with i ii have \<open>(mset_set (N - {C} \<union> N'), mset_set N) \<in> mult gclause_ord\<close>
    by (metis mult_def transitive_closure_trans(2))
  then show ?thesis unfolding gclause_set_ord_def by auto
qed

(* the next two lemmas show that redundant clauses in a set N play no role in deciding whether a
   clause or inference is redundant in N *)
lemma minimal_Red_gclause_subset:
  assumes \<open>C \<in> Red_gclause N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> C \<in> Red_gclause M \<and> (\<forall>D \<in> M. D \<notin> Red_gclause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>G {C} \<and> (\<forall>D \<in> NC1. (D, C) \<in> gclause_ord)\<close> (is \<open>?P NC1\<close>)
    unfolding Red_gclause_def by auto
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> gclause_set_ord ==> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>gclause_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] gclause_set_ord_wf by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_gclause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_gclause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>G {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. (E,D) \<in> gclause_ord\<close>
      using Red_gclause_def by auto
    (* construct a smaller set than NC0 in which C is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> gclause_set_ord\<close>
      using smaller_gclause_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>G {C}\<close>
    proof -
      from ND1_entails have \<open>?NCC \<Turnstile>G NC0 - {D} \<union> {D}\<close>
        by (meson entail_union entails_trans inf_sup_ord(3) inf_sup_ord(4) subset_entailed)
      also have \<open>NC0 - {D} \<union> {D} \<Turnstile>G NC0\<close> using subset_entailed [of NC0 \<open>NC0 - {D} \<union> {D}\<close>] by blast
      also have \<open>NC0 \<Turnstile>G {C}\<close> using NC0_prop Red_gclause_entails entail_set_all_formulas by blast
      finally show ?thesis by auto
    qed
    moreover have \<open>\<forall>E \<in> ?NCC. (E,C) \<in> gclause_ord\<close>
    proof
      fix E
      assume \<open>E \<in> ?NCC\<close>
      then consider (a) \<open>E \<in> NC0\<close> | (b) \<open>E \<in> ND1\<close> by blast
      then show \<open>(E,C) \<in> gclause_ord\<close>
      proof cases
        case a
        then show ?thesis using NC0_prop by auto
      next
        case b
        then have \<open>(E,D) \<in> gclause_ord\<close> using ND1_ord by auto
        also have \<open>(D,C) \<in> gclause_ord\<close> using \<open>D \<in> NC0\<close> NC0_prop by auto
        finally show ?thesis using gclause_ord_trans by auto
      qed
    qed
    ultimately show False using NC0_min by blast
  qed
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> C \<in> Red_gclause NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_gclause N)\<close>
    using Red_gclause_def by blast
  then show ?thesis by auto
qed

lemma minimal_Red_Inf_sup_subset:
  assumes \<open>\<iota> \<in> Red_Inf_sup N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> \<iota> \<in> Red_Inf_sup M \<and> (\<forall>D \<in> M. D \<notin> Red_gclause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>G {concl_of \<iota>} \<and> (\<forall>D \<in> NC1. \<exists>P\<in>set (prems_of \<iota>). (D, P) \<in> gclause_ord)\<close> (is \<open>?P NC1\<close>)
    unfolding Red_Inf_sup_def by auto
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> gclause_set_ord ==> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>gclause_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] gclause_set_ord_wf by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_gclause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_gclause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>G {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. (E,D) \<in> gclause_ord\<close>
      using Red_gclause_def by auto
    (* construct a smaller set than NC0 in which \<iota> is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> gclause_set_ord\<close>
      using smaller_gclause_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>G {concl_of \<iota>}\<close>
    proof -
      from ND1_entails have \<open>?NCC \<Turnstile>G NC0 - {D} \<union> {D}\<close>
        by (meson entail_union entails_trans inf_sup_ord(3) inf_sup_ord(4) subset_entailed)
      also have \<open>NC0 - {D} \<union> {D} \<Turnstile>G NC0\<close> using subset_entailed [of NC0 \<open>NC0 - {D} \<union> {D}\<close>] by blast
      also have \<open>NC0 \<Turnstile>G {concl_of \<iota>}\<close> using NC0_prop Red_gclause_entails entail_set_all_formulas by blast
      finally show ?thesis by auto
    qed
    moreover have \<open>\<forall>E \<in> ?NCC. \<exists>P\<in>set (prems_of \<iota>).  (E,P) \<in> gclause_ord\<close>
    proof
      fix E
      assume \<open>E \<in> ?NCC\<close>
      then consider (a) \<open>E \<in> NC0\<close> | (b) \<open>E \<in> ND1\<close> by blast
      then show \<open>\<exists>P \<in> set (prems_of \<iota>). (E,P) \<in> gclause_ord\<close>
      proof cases
        case a
        then show ?thesis using NC0_prop by auto
      next
        case b
        obtain P where P_elem: \<open>P \<in> set (prems_of \<iota>)\<close> and P_prop: \<open>(D,P) \<in> gclause_ord\<close> using \<open>D \<in> NC0\<close> NC0_prop by auto
        from b have \<open>(E,D) \<in> gclause_ord\<close> using ND1_ord by auto
        also have \<open>(D,P) \<in> gclause_ord\<close> using P_prop .
        finally show ?thesis using gclause_ord_trans P_elem by auto
      qed
    qed
    ultimately show False using NC0_min by blast
  qed
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> \<iota> \<in> Red_Inf_sup NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_gclause N)\<close>
    using Red_Inf_sup_def assms by blast
  then show ?thesis by auto
qed

lemma subst_lit_empty: \<open>subst_lit L [] = L\<close>
  by (metis subst_Nil subst_equation.elims subst_lit.elims subst_lit.simps(1))

lemma subst_cl_empty:
  \<open>subst_cl C [] = C\<close>
proof -
  from subst_lit_empty have \<open>subst_lit L [] = L\<close> for L :: \<open>'b literal\<close> .
  then show ?thesis by auto
qed

lemma mset_ecl_empty: \<open>mset_ecl (C, []) = {# mset_lit L. L \<in># mset_set (cl_ecl C) #}\<close>
  by (metis (no_types, lifting) subst_lit_empty image_mset_cong mset_ecl.simps)

lemma exists_premise_greater:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<exists>D \<in> set (prems_of \<iota>). (concl_of \<iota>, D) \<in> gclause_ord\<close>
proof -
  from assms consider (refl) \<open>\<iota> \<in> ground_reflexion_inferences\<close>
    | (fact) \<open>\<iota> \<in> ground_factorization_inferences\<close>
    | (supr) \<open>\<iota> \<in> ground_superposition_inferences\<close> by auto
  then show ?thesis
  proof cases
    case refl
    then obtain P C C' \<sigma> where reflexion: \<open>reflexion (Rep_gclause P) C \<sigma> Ground C'\<close>
                           and ground_C: \<open>ground_clause (cl_ecl C)\<close>
                           and prems_def: \<open>set (prems_of \<iota>) = {P}\<close>
                           and concl_def: \<open>concl_of \<iota> = gcl_remove_trms C\<close>
      unfolding ground_reflexion_inferences_def by auto
    then obtain L1
      where L1_elem: \<open>L1 \<in> cl_ecl (Rep_gclause P)\<close>
      and C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_gclause P) - { L1 }) \<sigma>\<close>
      unfolding reflexion_def by blast
    have \<open>finite (cl_ecl C)\<close>
      using Rep_gclause [of P] reflexion_preserves_finiteness reflexion by blast
    then have \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) = cl_ecl C\<close> using concl_def gcl_remove_trms_cl_ecl [of C] ground_C by auto
    also have \<open>... = cl_ecl (Rep_gclause P) - { L1 }\<close>
      using Rep_gclause [of P] C_def substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause P) - {L1}\<close> \<sigma>] by auto
    finally have \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) \<union> { L1 } = cl_ecl (Rep_gclause P)\<close> and \<open>L1 \<notin> cl_ecl (Rep_gclause (concl_of \<iota>))\<close> using L1_elem by auto
    then have \<open>mset_set (cl_ecl (Rep_gclause P)) = mset_set (cl_ecl (Rep_gclause (concl_of \<iota>))) + {# L1 #}\<close>
      using mset_set_insert [of L1 \<open>cl_ecl (Rep_gclause (concl_of \<iota>))\<close>] Rep_gclause [of \<open>concl_of \<iota>\<close>] by auto
    then have \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) \<subset># mset_ecl (Rep_gclause P, [])\<close> using subst_lit_empty by auto
    then have \<open>(mset_ecl (Rep_gclause (concl_of \<iota>), []), mset_ecl (Rep_gclause P, [])) \<in> mult (mult trm_ord)\<close>
      using subset_implies_mult by blast
    then show ?thesis using prems_def unfolding gclause_ord_def by auto
  next
    case fact
    then obtain P C C' \<sigma> where factorization: \<open>factorization (Rep_gclause P) C \<sigma> Ground C'\<close>
                           and ground_C: \<open>ground_clause (cl_ecl C)\<close>
                           and prems_def: \<open>set (prems_of \<iota>) = {P}\<close>
                           and concl_def: \<open>concl_of \<iota> = gcl_remove_trms C\<close>
      unfolding ground_factorization_inferences_def by auto
    then obtain L' L1 L2 s t u v
      where C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_gclause P) - {L2} \<union> {L'}) \<sigma>\<close>
        and L1_def: \<open>L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t)\<close>
        and L1_elem: \<open>L1 \<in> cl_ecl (Rep_gclause P)\<close>
        and L2_def: \<open>L2 = Pos (Eq u v) \<or> L2 = Pos (Eq v u)\<close>
        and L2_elem: \<open>L2 \<in> cl_ecl (Rep_gclause P)\<close>
        and L'_def: \<open>L' = Neg (Eq s v)\<close>
        and s_t_order: \<open>(t \<lhd> \<sigma>, s \<lhd> \<sigma>) \<notin> trm_ord\<close>
        and s_t_neq: \<open>t \<lhd> \<sigma> \<noteq> s \<lhd> \<sigma>\<close>
        and u_v_order: \<open>(u \<lhd> \<sigma>, v \<lhd> \<sigma>) \<notin> trm_ord\<close>
        and t_v_neq: \<open>t \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>\<close>
        and unifier: \<open>ck_unifier t u \<sigma> Ground\<close>
      unfolding factorization_def orient_lit_inst_def by blast
    (* all terms are ground and the order is total on them *)
    from L1_elem and Rep_gclause [of P] have \<open>vars_of_lit L1 = {}\<close> by auto
    with L1_def have ground_s_t: \<open>ground_term s \<and> ground_term t\<close> unfolding ground_term_def by auto
    then have s_t_def: \<open>s \<lhd> \<sigma> = s \<and> t \<lhd> \<sigma> = t\<close> using substs_preserve_ground_terms by blast
    with s_t_order trm_ord_ground_total ground_s_t s_t_neq have s_t_order': \<open>(s, t) \<in> trm_ord\<close> by auto
    from L2_elem and Rep_gclause [of P] have \<open>vars_of_lit L2 = {}\<close> by auto
    with L2_def have ground_u_v: \<open>ground_term u \<and> ground_term v\<close> unfolding ground_term_def by auto
    then have u_v_def: \<open>u \<lhd> \<sigma> = u \<and> v \<lhd> \<sigma> = v\<close> using substs_preserve_ground_terms by blast
    with s_t_def unifier have u_t_eq: \<open>u = t\<close> unfolding ck_unifier_def Unifier_def by auto
    with u_v_order trm_ord_ground_total ground_u_v ground_s_t t_v_neq u_v_def s_t_def have v_t_order: \<open>(v, t) \<in> trm_ord\<close> by auto
    with L2_def L'_def u_t_eq have \<open>mset_lit L' = {#s,s,v,v#} \<and> mset_lit L2 = {#t,v#}\<close> by auto
    (* the new literal is smaller than the one in the premise *)
    with v_t_order s_t_order' have lit_smaller: \<open>(mset_lit L', mset_lit L2) \<in> mult trm_ord\<close>
      by (smt add_mset_commute empty_iff insert_iff mset_ordering_singleton mult_cancel_add_mset set_mset_add_mset_insert set_mset_empty trm_ord_irrefl trm_ord_trans)
    (* the conclusion itself *)
    have ground_concl: \<open>ground_clause (cl_ecl (Rep_gclause P) - {L2} \<union> {L'})\<close>
      using Rep_gclause [of P] ground_s_t ground_u_v L'_def unfolding ground_term_def by auto
    have \<open>finite (cl_ecl C)\<close>
      using Rep_gclause [of P] factorization_preserves_finiteness factorization by blast
    then have \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) = cl_ecl C\<close> using concl_def gcl_remove_trms_cl_ecl [of C] ground_C by auto
    then have cl_concl_def: \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) = cl_ecl (Rep_gclause P) - {L2} \<union> {L'}\<close>
      using C_def ground_concl substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause P) - {L2} \<union> {L'}\<close> \<sigma>] by metis
    then have \<open>(mset_ecl (Rep_gclause (concl_of \<iota>), []), mset_ecl (Rep_gclause P, [])) \<in> mult (mult trm_ord)\<close>
    proof (cases \<open>L' \<in> cl_ecl (Rep_gclause P) - {L2}\<close>)
      case True
      then have \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) \<union> {L2} = cl_ecl (Rep_gclause P)\<close>
        using cl_concl_def L2_elem by auto
      moreover have \<open>L2 \<notin> cl_ecl (Rep_gclause (concl_of \<iota>))\<close>
        using cl_concl_def L2_def L'_def by blast
      ultimately have \<open>mset_set (cl_ecl (Rep_gclause P)) = mset_set (cl_ecl (Rep_gclause (concl_of \<iota>))) + {#L2#}\<close>
        using mset_set_insert [of L2 \<open>cl_ecl (Rep_gclause (concl_of \<iota>))\<close>] Rep_gclause [of \<open>concl_of \<iota>\<close>] by auto
      then have \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) \<subset># mset_ecl (Rep_gclause P, [])\<close> using subst_lit_empty by auto
      then have \<open>(mset_ecl (Rep_gclause (concl_of \<iota>), []), mset_ecl (Rep_gclause P, [])) \<in> mult (mult trm_ord)\<close>
        using subset_implies_mult by blast
      then show ?thesis using prems_def unfolding gclause_ord_def by auto
    next
      case False
      then have \<open>mset_set (cl_ecl (Rep_gclause P) - {L2} \<union> {L'}) = mset_set (cl_ecl (Rep_gclause P) - {L2}) + {# L' #}\<close>
        using multisets_continued.mset_set_insert Rep_gclause [of P] by auto
      then have \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P) - {L2}) + {#L'#} #}\<close>
        using mset_ecl_empty cl_concl_def by presburger
      then have mset_concl_def: \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P) - {L2}) #} + {#mset_lit L'#}\<close>
        by auto
      have \<open>cl_ecl (Rep_gclause P) = cl_ecl (Rep_gclause P) - {L2} \<union> {L2}\<close>
        using L2_elem by auto
      then have \<open>mset_set (cl_ecl (Rep_gclause P)) = mset_set (cl_ecl (Rep_gclause P) - {L2}) + {#L2#}\<close>
        using Rep_gclause [of P] multisets_continued.mset_set_insert [of L2 \<open>cl_ecl (Rep_gclause P) - {L2}\<close>] by auto
      then have \<open>mset_ecl (Rep_gclause P, []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P) - {L2}) + {#L2#} #}\<close>
        using mset_ecl_empty by presburger
      then have mset_P_def: \<open>mset_ecl (Rep_gclause P, []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P) - {L2}) #} + {#mset_lit L2#}\<close>
        by auto
      from mset_P_def mset_concl_def lit_smaller show ?thesis
        using one_step_implies_mult [of \<open>{#mset_lit L2#}\<close> \<open>{#mset_lit L'#}\<close> \<open>mult trm_ord\<close> \<open>{# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P) - {L2}) #}\<close>] by auto
    qed
    then show ?thesis using prems_def unfolding gclause_ord_def by auto
  next
    case supr
    then obtain P1 P2 C C' \<sigma> where superposition: \<open>superposition (Rep_gclause P1) (Rep_gclause P2) C \<sigma> Ground C'\<close>
                               and ground_C: \<open>ground_clause (cl_ecl C)\<close>
                               and prems_def: \<open>set (prems_of \<iota>) = {P1, P2}\<close>
                               and concl_def: \<open>concl_of \<iota> = gcl_remove_trms C\<close>
      unfolding ground_superposition_inferences_def by auto
    then obtain L L' M s t t' u u' p v polarity
      where C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_gclause P1) - {L} \<union> (cl_ecl (Rep_gclause P2) - {M} \<union> {L'})) \<sigma>\<close>
        and M_def: \<open>orient_lit_inst M u v pos \<sigma>\<close>
        and L_def: \<open>orient_lit_inst L t s polarity \<sigma>\<close>
        and L'_def: \<open>L' = mk_lit polarity (Eq t' s)\<close>
        and L_elem: \<open>L \<in> cl_ecl (Rep_gclause P1)\<close>
        and M_elem: \<open>M \<in> cl_ecl (Rep_gclause P2)\<close>
        and u_v_neq: \<open>u \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>\<close>
        and subterm: \<open>subterm t p u'\<close>
        and replacement: \<open>replace_subterm t p v t'\<close>
        and M_max_lit: \<open>strictly_maximal_literal (Rep_gclause P2) M \<sigma>\<close>
        and M_L_order: \<open>(subst_lit M \<sigma>, subst_lit L \<sigma>) \<in> lit_ord\<close>
        and unifier : \<open>ck_unifier u' u \<sigma> Ground\<close>
      unfolding superposition_def by force
    have ground_L': \<open>vars_of_lit L' = {}\<close>
    proof -
      have \<open>vars_of_lit L' = vars_of t' \<union> vars_of s\<close>
        using L'_def by (metis (full_types) mk_lit.elims vars_of_lit.simps vars_of_eq.simps)
      also have \<open>... = vars_of t'\<close>
        using L_def L_elem Rep_gclause [of P1] unfolding orient_lit_inst_def by force
      also have \<open>... \<subseteq> vars_of t \<union> vars_of v\<close>
        using vars_of_replacement replacement by fast
      also have \<open>... = vars_of v\<close>
        using L_def L_elem Rep_gclause [of P1] unfolding orient_lit_inst_def by force
      also have \<open>... = {}\<close>
        using M_def M_elem Rep_gclause [of P2] unfolding orient_lit_inst_def by force
      finally show ?thesis by auto
    qed
    have \<open>u' \<lhd> \<sigma> = u \<lhd> \<sigma>\<close> using unifier unfolding ck_unifier_def Unifier_def by auto
    then have \<open>(u' \<lhd> \<sigma>, v \<lhd> \<sigma>) \<notin> trm_ord\<close> and \<open>u' \<lhd> \<sigma> \<noteq> v \<lhd> \<sigma>\<close> using M_def u_v_neq unfolding orient_lit_inst_def by auto
    moreover have \<open>ground_term u'\<close>
      using L_def L_elem Rep_gclause [of P1] vars_subterm [of t p u'] subterm unfolding ground_term_def orient_lit_inst_def by force
    moreover have \<open>ground_term v\<close>
      using M_def M_elem Rep_gclause [of P2] unfolding ground_term_def orient_lit_inst_def by force
    ultimately have \<open>(v, u') \<in> trm_ord\<close> using trm_ord_ground_total substs_preserve_ground_terms by metis
    then have t'_t_order: \<open>(t', t) \<in> trm_ord\<close>
      using subterm replacement replacement_monotonic [of v \<open>[]\<close> u' t p t'] by auto
    (* the new literal is smaller than the one resolved upon *)
    consider (neg) \<open>mset_lit L' = {#s,s,t',t'#} \<and> mset_lit L = {#s,s,t,t#}\<close> | (pos) \<open>mset_lit L' = {#s,t'#} \<and> mset_lit L = {#s,t#}\<close>
      using L'_def L_def unfolding orient_lit_inst_def by fastforce
    then have lit_smaller: \<open>(mset_lit L', mset_lit L) \<in> mult trm_ord\<close>
    proof cases
      case neg
      then show ?thesis using one_step_implies_mult [of \<open>{#t,t#}\<close> \<open>{#t',t'#}\<close> trm_ord \<open>{#s,s#}\<close>] t'_t_order
        by (smt empty_not_add_mset insert_DiffM2 insert_iff set_mset_add_mset_insert union_commute union_is_single union_mset_add_mset_right)
    next
      case pos
      then show ?thesis using t'_t_order
        by (simp add: mset_ordering_singleton mult_cancel_add_mset trm_ord_irrefl trm_ord_trans)
    qed
    (* compare the conclusion and P1 *)
    have ground_concl: \<open>ground_clause (cl_ecl (Rep_gclause P1) - {L} \<union> (cl_ecl (Rep_gclause P2) - {M} \<union> {L'}))\<close>
      using Rep_gclause [of P1] Rep_gclause [of P2] ground_L' by auto
    have \<open>finite (cl_ecl C)\<close>
      using Rep_gclause [of P1] Rep_gclause [of P2] superposition_preserves_finiteness superposition by blast
    then have \<open>cl_ecl (Rep_gclause (concl_of \<iota>)) = cl_ecl C\<close> using concl_def gcl_remove_trms_cl_ecl [of C] ground_C by auto
    also have \<open>... = cl_ecl (Rep_gclause P1) - {L} \<union> (cl_ecl (Rep_gclause P2) - {M} \<union> {L'})\<close>
      using C_def ground_concl substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause P1) - {L} \<union> (cl_ecl (Rep_gclause P2) - {M} \<union> {L'})\<close>] by blast
    also have \<open>... = cl_ecl (Rep_gclause P1) - {L} \<union> ((cl_ecl (Rep_gclause P2) - {M} \<union> {L'}) - (cl_ecl (Rep_gclause P1) - {L}))\<close> by blast
    finally have \<open>mset_set (cl_ecl (Rep_gclause (concl_of \<iota>))) = mset_set (cl_ecl (Rep_gclause P1) - {L}) + mset_set ((cl_ecl (Rep_gclause P2) - {M} \<union> {L'}) - (cl_ecl (Rep_gclause P1) - {L}))\<close>
      using mset_set_Union [of \<open>cl_ecl (Rep_gclause P1) - {L}\<close> \<open>cl_ecl (Rep_gclause P2) - {M} \<union> {L'} - (cl_ecl (Rep_gclause P1) - {L})\<close>]
             Rep_gclause [of P1] Rep_gclause [of P2] by fastforce
    then have \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P1) - {L}) + mset_set ((cl_ecl (Rep_gclause P2) - {M} \<union> {L'}) - (cl_ecl (Rep_gclause P1) - {L})) #}\<close>
      using mset_ecl_empty by presburger
    then have mset_ecl_concl: \<open>mset_ecl (Rep_gclause (concl_of \<iota>), []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P1) - {L}) #} + {# mset_lit L. L \<in># mset_set ((cl_ecl (Rep_gclause P2) - {M} \<union> {L'}) - (cl_ecl (Rep_gclause P1) - {L})) #}\<close>
      by auto
    have \<open>cl_ecl (Rep_gclause P1) = cl_ecl (Rep_gclause P1) - {L} \<union> {L}\<close> using L_elem by auto
    then have \<open>mset_set (cl_ecl (Rep_gclause P1)) = mset_set (cl_ecl (Rep_gclause P1) - {L}) + mset_set {L}\<close>
      using Rep_gclause [of P1] mset_set_Union [of \<open>cl_ecl (Rep_gclause P1) - {L}\<close> \<open>{L}\<close>] by auto
    then have \<open>mset_ecl (Rep_gclause P1, []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P1) - {L}) + mset_set {L} #}\<close>
      using mset_ecl_empty by presburger
    then have mset_ecl_P1: \<open>mset_ecl (Rep_gclause P1, []) = {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P1) - {L}) #} + {# mset_lit L #}\<close> by auto
    have L_greater: \<open>k \<in># {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P2) - {M} \<union> {L'} - (cl_ecl (Rep_gclause P1) - {L})) #} \<Longrightarrow> (k, mset_lit L) \<in> mult trm_ord\<close> for k
    proof -
      assume \<open>k \<in># {# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P2) - {M} \<union> {L'} - (cl_ecl (Rep_gclause P1) - {L})) #}\<close>
      then have \<open>k \<in> mset_lit ` (cl_ecl (Rep_gclause P2) - {M} \<union> {L'} - (cl_ecl (Rep_gclause P1) - {L}))\<close>
        using Rep_gclause [of P1] Rep_gclause [of P2] by simp
      then obtain Lk where \<open>Lk \<in> cl_ecl (Rep_gclause P2) - {M} \<union> {L'} - (cl_ecl (Rep_gclause P1) - {L})\<close>
                      and k_def: \<open>k = mset_lit Lk\<close> by auto
      then consider (a) \<open>Lk \<in> cl_ecl (Rep_gclause P2) - {M}\<close> | (b) \<open>Lk = L'\<close> by blast
      then show ?thesis
      proof cases
        case a
        then have \<open>(subst_lit Lk \<sigma>, subst_lit M \<sigma>) \<in> lit_ord\<close> using M_max_lit unfolding strictly_maximal_literal_def by blast
        then have \<open>(subst_lit Lk \<sigma>, subst_lit L \<sigma>) \<in> lit_ord\<close> using M_L_order lit_ord_trans unfolding trans_def by blast
        moreover have \<open>subst_lit Lk \<sigma> = Lk\<close>
          using a substs_preserve_ground_lit Rep_gclause [of P2] by fast
        moreover have \<open>subst_lit L \<sigma> = L\<close>
          using L_elem substs_preserve_ground_lit Rep_gclause [of P1] by fast
        ultimately show ?thesis using k_def unfolding lit_ord_def by auto
      next
        case b
        then show ?thesis using lit_smaller k_def by auto
      qed
    qed
    from mset_ecl_concl mset_ecl_P1 L_greater have \<open>(mset_ecl (Rep_gclause (concl_of \<iota>), []), mset_ecl (Rep_gclause P1, [])) \<in> mult (mult trm_ord)\<close>
      using one_step_implies_mult [of \<open>{# mset_lit L #}\<close> \<open>{# mset_lit L. L \<in># mset_set ((cl_ecl (Rep_gclause P2) - {M} \<union> {L'}) - (cl_ecl (Rep_gclause P1) - {L})) #}\<close> \<open>mult trm_ord\<close> \<open>{# mset_lit L. L \<in># mset_set (cl_ecl (Rep_gclause P1) - {L}) #}\<close>]
      by force
    then show ?thesis using prems_def unfolding gclause_ord_def by auto
  qed
qed

lemma Red_Inf_concl_of:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<iota> \<in> Red_Inf_sup {concl_of \<iota>}\<close>
proof -
  let ?N' = \<open>{concl_of \<iota>}\<close>
  have \<open>?N' \<Turnstile>G {concl_of \<iota>}\<close> by (simp add: subset_entailed)
  moreover have \<open>\<forall>D\<in>?N'. \<exists>P\<in>set (prems_of \<iota>). (D, P) \<in> gclause_ord\<close>
  proof
    fix D
    assume \<open>D \<in> {concl_of \<iota>}\<close>
    then have D_def: \<open>D = concl_of \<iota>\<close> by auto
    then obtain cl_P where \<open>cl_P \<in> set (prems_of \<iota>)\<close>
                    and \<open>(concl_of \<iota>, cl_P) \<in> gclause_ord\<close>
      using exists_premise_greater [of \<iota>] assms by blast
    then show \<open>\<exists>P\<in>set (prems_of \<iota>). (D, P) \<in> gclause_ord\<close> unfolding gclause_ord_def ecl_ord_def using D_def by blast
  qed
  ultimately show ?thesis using assms unfolding Red_Inf_sup_def by blast
qed

lemma Red_gclause_entailed: \<open>N - Red_gclause N \<Turnstile>G Red_gclause N\<close>
proof (rule all_formulas_entailed)
  show \<open>\<forall>C \<in> Red_gclause N. N - Red_gclause N \<Turnstile>G {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_gclause N\<close>
    then obtain M where M_subset: \<open>M \<subseteq> N\<close>
                    and M_Red: \<open>C \<in> Red_gclause M\<close>
                    and M_min: \<open>\<forall>D \<in> M. D \<notin> Red_gclause N\<close>
      using minimal_Red_gclause_subset by metis
    with M_subset have \<open>M \<subseteq> N - Red_gclause N\<close> by auto
    then have \<open>N - Red_gclause N \<Turnstile>G M\<close> using subset_entailed by auto
    also have \<open>M \<Turnstile>G Red_gclause M\<close> using Red_gclause_entails by auto
    also have \<open>Red_gclause M \<Turnstile>G {C}\<close> using M_Red subset_entailed by auto
    finally show \<open>N - Red_gclause N \<Turnstile>G {C}\<close> by auto
  qed
qed

interpretation calculus empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_gclause
proof
  show \<open>Red_Inf_sup N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_Inf_sup_def by auto
next
  show \<open>B \<in> empty_gclauses \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> N - Red_gclause N \<Turnstile>G {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> empty_gclauses\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have N_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not>validate_clause_set I (cl_ecl ` Rep_gclause ` N)\<close> for I
      unfolding gclause_entails_def set_entails_clause_def by auto
    assume \<open>\<not> N - Red_gclause N \<Turnstile>G {B}\<close>
    with N_unsat obtain I where fo_I: \<open>fo_interpretation I\<close>
                          and I_model: \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` (N - Red_gclause N))\<close>
                          and \<open>\<not>validate_clause_set I (cl_ecl ` Rep_gclause ` N)\<close>
      unfolding gclause_entails_def set_entails_clause_def by blast
    then obtain C where \<open>C \<in> Rep_gclause ` N\<close>
                    and \<open>C \<notin> Rep_gclause ` (N - Red_gclause N)\<close>
                    and C_novalid: \<open>\<not> validate_clause I (cl_ecl C)\<close>
      by (smt image_iff validate_clause_set.simps)
    then have \<open>C \<in> Rep_gclause ` (Red_gclause N)\<close> by blast
    then obtain cl_C where \<open>C = Rep_gclause cl_C\<close>
                       and \<open>cl_C \<in> Red_gclause N\<close> by auto
    with Red_gclause_entailed fo_I I_model have \<open>validate_clause I (cl_ecl C)\<close>
      unfolding gclause_entails_def set_entails_clause_def by blast
    with C_novalid show False by blast
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_gclause N \<subseteq> Red_gclause N'\<close> for N N' unfolding Red_gclause_def by fast
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close> for N N' unfolding Red_Inf_sup_def by fast
next
  show \<open>N' \<subseteq> Red_gclause N \<Longrightarrow> Red_gclause N \<subseteq> Red_gclause (N - N')\<close> for N' N
  proof
    fix C
    assume N'_subset: \<open>N' \<subseteq> Red_gclause N\<close> and \<open>C \<in> Red_gclause N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>C \<in> Red_gclause M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_gclause N)\<close>
      using minimal_Red_gclause_subset by metis
    then have \<open>C \<in> Red_gclause M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>C \<in> Red_gclause (N - N')\<close> unfolding Red_gclause_def by fast
  qed
next
  show \<open>N' \<subseteq> Red_gclause N \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup (N - N')\<close> for N' N
  proof
    fix \<iota>
    assume N'_subset: \<open>N' \<subseteq> Red_gclause N\<close> and \<open>\<iota> \<in> Red_Inf_sup N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>\<iota> \<in> Red_Inf_sup M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_gclause N)\<close>
      using minimal_Red_Inf_sup_subset by metis
    then have \<open>\<iota> \<in> Red_Inf_sup M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>\<iota> \<in> Red_Inf_sup (N - N')\<close> unfolding Red_Inf_sup_def by fast
  qed
next
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_sup N\<close> for \<iota> N
  proof -
    assume \<open>\<iota> \<in> ground_superposition_inference_system\<close>
    then have \<open>\<iota> \<in> Red_Inf_sup {concl_of \<iota>}\<close>
      using Red_Inf_concl_of [of \<iota>] by blast
    then show \<open>concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_sup N\<close> unfolding Red_Inf_sup_def by fast
  qed
qed

lemma derivable_factorization:
  assumes \<open>P \<in> Rep_gclause ` N\<close>
      and \<open>factorization P C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_factorization_inferences. concl_of \<iota> = gcl_remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P is ground *)
  have inv_P: \<open>Rep_gclause (Abs_gclause P) = P\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P] (gcl_remove_trms C)\<close>
  have \<open>?\<iota> \<in> ground_factorization_inferences\<close>
    unfolding ground_factorization_inferences_def using inv_P assms(2,3) by auto
  moreover have \<open>Rep_gclause ` set (prems_of ?\<iota>) = {P}\<close> using inv_P by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_gclause P} \<subseteq> N\<close> using assms(1)
      by (metis Rep_gclause_inverse empty_subsetI image_iff insert_subset)
    then show ?thesis by auto
  qed
  ultimately show ?thesis by force
qed

lemma derivable_reflexion:
  assumes \<open>P \<in> Rep_gclause ` N\<close>
      and \<open>reflexion P C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_reflexion_inferences. concl_of \<iota> = gcl_remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P is ground *)
  have inv_P: \<open>Rep_gclause (Abs_gclause P) = P\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P] (gcl_remove_trms C)\<close>
  have \<open>?\<iota> \<in> ground_reflexion_inferences\<close>
    unfolding ground_reflexion_inferences_def using inv_P assms(2,3) by auto
  moreover have \<open>Rep_gclause ` set (prems_of ?\<iota>) = {P}\<close> using inv_P by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_gclause P} \<subseteq> N\<close> using assms(1)
      by (metis Rep_gclause_inverse empty_subsetI image_iff insert_subset)
    then show ?thesis by auto
  qed
  ultimately show ?thesis by force
qed

lemma derivable_superposition:
  assumes \<open>P1 \<in> Rep_gclause ` N\<close>
      and \<open>P2 \<in> Rep_gclause ` N\<close>
      and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_superposition_inferences. concl_of \<iota> = gcl_remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P1, P2} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P1, P2 and C are ground *)
  have inv_P1: \<open>Rep_gclause (Abs_gclause P1) = P1\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  have inv_P2: \<open>Rep_gclause (Abs_gclause P2) = P2\<close>
    using Abs_gclause_inverse Rep_gclause assms(2) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P1, Abs_gclause P2] (gcl_remove_trms C)\<close>
  have \<open>?\<iota> \<in> ground_superposition_inferences\<close>
    unfolding ground_superposition_inferences_def using inv_P1 inv_P2 assms(2,3,4) by auto
  moreover have \<open>Rep_gclause ` set (prems_of ?\<iota>) = {P1, P2}\<close> using inv_P1 inv_P2 by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_gclause P1, Abs_gclause P2} \<subseteq> N\<close> using assms(1,2)
      by (smt Rep_gclause_inverse image_iff insert_iff mem_Collect_eq singletonD subsetI)
    then show ?thesis by auto
  qed
  moreover have \<open>concl_of ?\<iota> = gcl_remove_trms C\<close> by auto
  ultimately show ?thesis by blast
qed

lemma derivable_gclause:
  assumes \<open>derivable C P (Rep_gclause ` N) \<sigma> Ground C'\<close>
  assumes \<open>ground_clause (cl_ecl C)\<close>
  shows \<open>\<exists> \<iota> \<in> ground_inf.Inf_from N. concl_of \<iota> = gcl_remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = P\<close>
proof -
  from assms(1) consider
      (a) \<open>\<exists>P1 P2. P1 \<in> (Rep_gclause ` N) \<and> P2 \<in> (Rep_gclause ` N) \<and> P = {P1, P2} \<and> superposition P1 P2 C \<sigma> Ground C'\<close>
    | (b) \<open>\<exists>P1. P1 \<in> (Rep_gclause ` N) \<and> P = {P1} \<and> factorization P1 C \<sigma> Ground C'\<close>
    | (c) \<open>\<exists>P1. P1 \<in> (Rep_gclause ` N) \<and> P = {P1} \<and> reflexion P1 C \<sigma> Ground C'\<close>
    unfolding derivable_def by blast
  then show \<open>\<exists> \<iota> \<in> ground_inf.Inf_from N. concl_of \<iota> = gcl_remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = P\<close>
  proof cases
    case a
    then obtain P1 P2 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                        and \<open>P2 \<in> (Rep_gclause ` N)\<close>
                        and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
                        and \<open>P = {P1, P2}\<close>
      by auto
    then show ?thesis using derivable_superposition assms(2) unfolding ground_inf.Inf_from_def by blast
  next
    case b
    then obtain P1 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                     and \<open>factorization P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_factorization assms(2) unfolding ground_inf.Inf_from_def by blast
  next
    case c
    then obtain P1 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                     and \<open>reflexion P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_reflexion assms(2) unfolding ground_inf.Inf_from_def by blast
  qed
qed

(* connect our definition of saturation to the definition is SuperCalc.superposition *)
lemma saturation_gclauses:
  assumes \<open>saturated N\<close>
  shows \<open>ground_inference_saturated (Rep_gclause ` N)\<close>
proof -
  have \<open>derivable C P (Rep_gclause `  N) \<sigma> Ground C' \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> redundant_inference C (Rep_gclause ` N) P \<sigma>\<close> for C P \<sigma> C'
  proof -
    assume derivable: \<open>derivable C P (Rep_gclause ` N) \<sigma> Ground C'\<close> and ground: \<open>ground_clause (cl_ecl C)\<close>
    then obtain \<iota> where \<open>\<iota> \<in> Red_Inf_sup N\<close>
                    and \<open>concl_of \<iota> = gcl_remove_trms C\<close>
                    and P_def: \<open>P = Rep_gclause ` (set (prems_of \<iota>))\<close>
      using assms(1) saturated_def derivable_gclause by blast
    then have red_inf: \<open>redundant_inference (Rep_gclause (gcl_remove_trms C)) (Rep_gclause ` N) P \<sigma>\<close>
      using Red_Inf_redundant_inference by metis
    have \<open>finite (cl_ecl C)\<close>
      using P_def derivable derivable_clauses_are_finite Rep_gclause by blast
    with red_inf ground show ?thesis using redundant_inference_gcl_remove_trms by auto
  qed
  then show ?thesis
    unfolding ground_inference_saturated_def by auto
qed

definition canonical_interp :: \<open>'a gclause set \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool\<close>
  where \<open>canonical_interp N = same_values (\<lambda>x. (trm_rep x (Rep_gclause ` N)))\<close>

lemma canonical_interp_fo: \<open>fo_interpretation (canonical_interp N)\<close>
  unfolding canonical_interp_def using trm_rep_compatible_with_structure same_values_fo_int by metis

lemma subst_ecl_ground_clause:
  assumes \<open>ground_clause (cl_ecl C)\<close>
  assumes \<open>trms_ecl C = {}\<close>
  shows \<open>subst_ecl C \<sigma> = C\<close>
proof -
  from assms(1) have \<open>subst_cl (cl_ecl C) \<sigma> = cl_ecl C\<close>
    using substs_preserve_ground_clause by blast
  moreover have \<open>{t \<lhd> \<sigma> |t. t \<in> trms_ecl C} = trms_ecl C\<close> using assms(2) by auto
  ultimately show ?thesis
    by (smt Collect_cong cl_ecl.simps subst_ecl.simps trms_ecl.elims)
qed

lemma closed_under_renaming_gclauses:
  shows \<open>closed_under_renaming (Rep_gclause ` N)\<close>
proof -
  have \<open>C \<in> (Rep_gclause ` N) \<Longrightarrow> renaming_cl C D \<Longrightarrow> D \<in> (Rep_gclause ` N)\<close> for C D
  proof -
    assume C_elem: \<open>C \<in> (Rep_gclause ` N)\<close> and \<open>renaming_cl C D\<close>
    then obtain \<eta> where \<open>subst_ecl C \<eta> = D\<close> and \<open>trms_ecl C = {}\<close> and \<open>ground_clause (cl_ecl C)\<close>
      using Rep_gclause
      unfolding renaming_cl_def by blast
    then have \<open>C = D\<close> using subst_ecl_ground_clause [of C] by auto 
    with C_elem show \<open>D \<in> (Rep_gclause ` N)\<close> by auto
  qed
  then show ?thesis unfolding closed_under_renaming_def by blast
qed

lemma canonical_interp_model:
  assumes \<open>saturated N\<close>
  assumes \<open>\<forall>C \<in> N. C \<notin> empty_gclauses\<close>
  assumes \<open>C \<in> Rep_gclause ` N\<close>
  assumes \<open>ground_clause (subst_cl (cl_ecl C) \<sigma>)\<close>
  shows \<open>validate_ground_clause (canonical_interp N) (subst_cl (cl_ecl C) \<sigma>)\<close>
proof -
  let ?S = \<open>Rep_gclause ` N\<close>
  have \<open>ground_inference_saturated ?S\<close> using assms(1) saturation_gclauses by auto
  moreover from assms(2) have \<open>\<forall>x \<in> ?S. (cl_ecl x) \<noteq> {}\<close> by auto
  moreover have \<open>\<forall>x \<in> ?S. finite (cl_ecl x)\<close> using Rep_gclause by blast
  moreover have \<open>all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. (trm_rep t ?S))\<close>
  proof -
    have \<open>trms_ecl C = {}\<close> using Rep_gclause assms(3) by blast
    then have \<open>subst_set (trms_ecl C) \<sigma> = {}\<close> by auto
    then show ?thesis unfolding all_trms_irreducible_def by blast
  qed
  moreover have \<open>\<forall>x \<in> ?S. well_constrained x\<close>
  proof
    fix C
    assume \<open>C \<in> ?S\<close>
    then have \<open>trms_ecl C = {}\<close> using Rep_gclause assms(3) by blast
    then show \<open>well_constrained C\<close> unfolding well_constrained_def by blast
  qed
  moreover have \<open>closed_under_renaming ?S\<close> using closed_under_renaming_gclauses by auto
  ultimately show \<open>validate_ground_clause (canonical_interp N) (subst_cl (cl_ecl C) \<sigma>)\<close>
    unfolding canonical_interp_def
    using assms(4) int_clset_is_a_model [of ?S \<open>(C, \<sigma>)\<close>]
    by (metis (no_types, lifting) assms(3) fst_eqD snd_eqD)
qed

interpretation static_refutational_complete_calculus empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_gclause
proof
  have \<open>saturated N \<Longrightarrow> \<forall>C \<in> N. C \<notin> empty_gclauses \<Longrightarrow> B \<in> empty_gclauses \<Longrightarrow> \<not> N \<Turnstile>G {B}\<close> for B N
  proof
    assume saturated: \<open>saturated N\<close> and no_empty_cl: \<open>\<forall>C \<in> N. C \<notin> empty_gclauses\<close> and \<open>B \<in> empty_gclauses\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have N'_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not> validate_clause_set I (cl_ecl ` Rep_gclause ` N)\<close> for I
      unfolding gclause_entails_def set_entails_clause_def by auto
    (* model for N *)
    have \<open>validate_clause_set (canonical_interp N) (cl_ecl ` (Rep_gclause ` N))\<close>
    proof -
      have \<open>cl_C \<in> cl_ecl ` Rep_gclause ` N \<Longrightarrow> ground_clause (subst_cl cl_C \<sigma>_C) \<Longrightarrow> validate_ground_clause (canonical_interp N) (subst_cl cl_C \<sigma>_C)\<close> for cl_C \<sigma>_C
      proof -
        assume \<open>cl_C \<in> cl_ecl ` Rep_gclause ` N\<close> and \<open>ground_clause (subst_cl cl_C \<sigma>_C)\<close>
        then obtain C where \<open>C \<in> Rep_gclause ` N\<close> and \<open>cl_C = cl_ecl C\<close> and \<open>ground_clause (subst_cl cl_C \<sigma>_C)\<close> by auto
        then show \<open>validate_ground_clause (canonical_interp N) (subst_cl cl_C \<sigma>_C)\<close>
          using canonical_interp_model [of N C \<sigma>_C] saturated no_empty_cl by blast
      qed
      then show ?thesis by auto
    qed
    with canonical_interp_fo and N'_unsat show False by blast
  qed
  then show \<open>saturated N \<Longrightarrow> B \<in> empty_gclauses \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> \<exists>B'\<in>empty_gclauses. B' \<in> N\<close> for B N by blast
qed

(* First-order calculus *)

definition fclause_entails :: \<open>'a fclause set \<Rightarrow> 'a fclause set \<Rightarrow> bool\<close> (infix "\<Turnstile>F" 50)
  where
\<open>N1 \<Turnstile>F N2 \<equiv> \<forall>C2 \<in> N2. set_entails_clause (cl_ecl ` Rep_fclause ` N1) (cl_ecl (Rep_fclause C2))\<close>

abbreviation empty_fclauses :: \<open>'a fclause set\<close>
  where \<open>empty_fclauses \<equiv> {C. cl_ecl (Rep_fclause C) = {}}\<close>

interpretation consequence_relation empty_fclauses \<open>(\<Turnstile>F)\<close>
proof
  show \<open>B \<in> empty_fclauses \<Longrightarrow> {B} \<Turnstile>F N1\<close> for B :: \<open>'a fclause\<close> and N1
    unfolding fclause_entails_def using empty_clause_entails by auto
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N2 N1 :: \<open>'a fclause set\<close>
    unfolding fclause_entails_def
    by (simp add: set_entails_clause_member set_mp)
  show \<open>\<forall>C\<in>N2. N1 \<Turnstile>F {C} \<Longrightarrow> N1 \<Turnstile>F N2\<close> for N2 N1 :: \<open>'a fclause set\<close>
    unfolding fclause_entails_def by fast
  show \<open>N1 \<Turnstile>F N2 \<Longrightarrow> N2 \<Turnstile>F N3 \<Longrightarrow> N1 \<Turnstile>F N3\<close> for N1 N2 N3 :: \<open>'a fclause set\<close>
    unfolding fclause_entails_def set_entails_clause_def by force
qed

fun fcl_remove_trms :: \<open>'a eclause \<Rightarrow> 'a fclause\<close>
  where \<open>fcl_remove_trms C = Abs_fclause (Ecl (cl_ecl C) {})\<close>

lemma fcl_remove_trms_cl_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
  using Abs_fclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

lemma fcl_remove_trms_trms_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> trms_ecl (Rep_fclause (fcl_remove_trms C)) = {}\<close>
  using Abs_fclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

lemma subst_mod:
  \<open>Var y \<noteq> t \<Longrightarrow> y \<in> vars_of t \<Longrightarrow> Var y \<lhd> \<sigma> \<noteq> Var y \<Longrightarrow> t \<noteq> t \<lhd> \<sigma>\<close>
proof (induct t)
  case (Var z)
  then show \<open>Var z \<noteq> Var z \<lhd> \<sigma>\<close> by auto
next
  case (Const c)
  then show \<open>Const c \<noteq> Const c \<lhd> \<sigma>\<close> by auto
next
  case (Comb t1 t2)
  then show \<open>t1 \<cdot> t2 \<noteq> t1 \<cdot> t2 \<lhd> \<sigma>\<close>
  proof (cases \<open>y \<in> vars_of t1\<close>)
    case True
    with Comb show ?thesis proof (cases \<open>Var y = t1\<close>; force) qed
  next
    case False
    with Comb show ?thesis proof (cases \<open>Var y = t2\<close>; force) qed
  qed
qed

lemma Idem_range_dom:
  assumes \<open>Idem \<sigma>\<close>
  assumes \<open>y \<in> vars_of (Var x \<lhd> \<sigma>)\<close>
  assumes \<open>x \<noteq> y\<close>
  shows \<open>Var y \<lhd> \<sigma> = Var y\<close>
proof (cases \<open>Var y = Var x \<lhd> \<sigma>\<close>)
  case True
  then have \<open>Var x \<lhd> \<sigma> = Var y \<and> Var x \<lhd> \<sigma> \<lhd> \<sigma> = Var y \<lhd> \<sigma>\<close> by simp
  moreover have \<open>Var x \<lhd> \<sigma> \<lhd> \<sigma> = Var x \<lhd> \<sigma>\<close>
    using assms(1) unfolding Idem_def by (metis comp_subst_terms subst_sym)
  ultimately show ?thesis by auto
next
  case False
  with subst_mod assms(2,3) have \<open>Var y \<lhd> \<sigma> \<noteq> Var y \<Longrightarrow> Var x \<lhd> \<sigma> \<noteq> Var x \<lhd> \<sigma> \<lhd> \<sigma>\<close> by fast
  then show ?thesis
    using assms(1) unfolding Idem_def using comp_subst_terms subst_sym by blast
qed

lemma Idem_MGU_no_variable_introduction:
  assumes MGU: \<open>MGU \<sigma> s t\<close>
  assumes Idem: \<open>Idem \<sigma>\<close>
  shows \<open>vars_of (u \<lhd> \<sigma>) \<subseteq> vars_of s \<union> vars_of t \<union> vars_of u\<close>
proof -
  have \<open>vars_of (Var x \<lhd> \<sigma>) \<subseteq> vars_of s \<union> vars_of t \<union> {x}\<close> for x
  proof (rule ccontr)
    assume \<open>\<not> vars_of (Var x \<lhd> \<sigma>) \<subseteq> vars_of s \<union> vars_of t \<union> {x}\<close>
    then obtain y where y_in_vars: \<open>y \<in> vars_of (Var x \<lhd> \<sigma>)\<close>
                    and y_not_elem_s: \<open>y \<notin> vars_of s\<close>
                    and y_not_elem_t: \<open>y \<notin> vars_of t\<close>
                    and neq_x_y: \<open>x \<noteq> y\<close> by auto
    then have \<sigma>_on_y: \<open>Var y \<lhd> \<sigma> = Var y\<close> using Idem_range_dom Idem by auto
    show False
    proof (cases \<open>Var y = Var x \<lhd> \<sigma>\<close>)
      case True (* Var y = Var x \<lhd> \<sigma> *)
      let ?\<theta> = \<open>(y, Var y) # (\<sigma> \<lozenge> [(y, Var x)])\<close>
      have \<open>Unifier ?\<theta> s t\<close> unfolding Unifier_def
      proof -
        have \<open>s \<lhd> ?\<theta> = s \<lhd> \<sigma> \<lozenge> [(y, Var x)]\<close> using y_not_elem_s by (simp add: repl_invariance)
        moreover have \<open>t \<lhd> ?\<theta> = t \<lhd> \<sigma> \<lozenge> [(y, Var x)]\<close> using y_not_elem_t by (simp add: repl_invariance)
        moreover have \<open>s \<lhd> \<sigma> = t \<lhd> \<sigma>\<close> using MGU unfolding MGU_def Unifier_def by auto
        ultimately show \<open>s \<lhd> ?\<theta> = t \<lhd> ?\<theta>\<close> by auto
      qed
      (* \<theta> cannot be an instance of \<sigma> *)
      with MGU obtain \<gamma> where instance_of_\<sigma>: \<open>?\<theta> \<doteq> \<sigma> \<lozenge> \<gamma>\<close> unfolding MGU_def by auto
      have \<open>Var x \<lhd> ?\<theta> = Var x \<lhd> \<sigma> \<lozenge> [(y, Var x)]\<close> using neq_x_y by (metis assoc.simps(2) subst.simps(1))
      also have \<open>... = Var x \<lhd> \<sigma> \<lhd> [(y, Var x)]\<close> by auto
      also have \<open>... = Var y \<lhd> [(y, Var x)]\<close> using \<open>Var y = Var x \<lhd> \<sigma>\<close> by auto
      finally have \<open>Var x \<lhd> ?\<theta> = Var x\<close> by auto
      moreover have \<open>Var y \<lhd> ?\<theta> = Var y\<close> by auto
      ultimately have \<open>Var x \<lhd> ?\<theta> \<noteq> Var y \<lhd> ?\<theta>\<close> using neq_x_y by simp
      then have \<open>Var x \<lhd> \<sigma> \<lozenge> \<gamma> \<noteq> Var y \<lhd> \<sigma> \<lozenge> \<gamma>\<close> using instance_of_\<sigma> by (metis (no_types, lifting) subst_eq_dest)
      then have \<open>Var x \<lhd> \<sigma> \<lhd> \<gamma> \<noteq> Var y \<lhd> \<sigma> \<lhd> \<gamma>\<close> by auto
      then have \<open>Var y \<lhd> \<gamma> \<noteq> Var y \<lhd> \<gamma>\<close> using \<sigma>_on_y \<open>Var y = Var x \<lhd> \<sigma>\<close> by auto
      then show False by auto
    next
      case False (* Var y \<noteq> Var x \<lhd> \<sigma> *)
      let ?\<theta> = \<open>[(y, Var x)] \<lozenge> \<sigma>\<close>
      have \<open>Unifier ?\<theta> s t\<close> unfolding Unifier_def
      proof -
        from y_not_elem_s have \<open>s = s \<lhd> [(y, Var x)]\<close> by (simp add: repl_invariance)
        moreover from y_not_elem_t have \<open>t = t \<lhd> [(y, Var x)]\<close> by (simp add: repl_invariance)
        moreover from MGU have \<open>s \<lhd> \<sigma> = t \<lhd> \<sigma>\<close> unfolding MGU_def Unifier_def by blast
        ultimately have \<open>s \<lhd> [(y, Var x)] \<lhd> \<sigma> = t \<lhd> [(y, Var x)] \<lhd> \<sigma>\<close> by auto
        then show \<open>s \<lhd> ?\<theta> = t \<lhd> ?\<theta>\<close> using subst_comp by metis
      qed
      (* \<theta> cannot be an instance of \<sigma> *)
      with MGU obtain \<gamma> where instance_of_\<sigma>: \<open>?\<theta> \<doteq> \<sigma> \<lozenge> \<gamma>\<close> unfolding MGU_def by auto
      then have \<open>Var y \<lhd> [(y, Var x)] \<lozenge> \<sigma> = Var y \<lhd> \<sigma> \<lozenge> \<gamma>\<close> unfolding subst_eq_def by auto
      with \<sigma>_on_y have \<gamma>_on_y: \<open>Var x \<lhd> \<sigma> = Var y \<lhd> \<gamma>\<close> by auto
      have neq: \<open>Var x \<lhd> \<sigma> \<noteq> Var x \<lhd> \<sigma> \<lhd> \<gamma>\<close> using subst_mod [of y \<open>Var x \<lhd> \<sigma>\<close> \<gamma>] \<open>Var y \<noteq> Var x \<lhd> \<sigma>\<close> y_in_vars \<gamma>_on_y by auto
      from instance_of_\<sigma> have \<open>Var x \<lhd> [(y, Var x)] \<lozenge> \<sigma> = Var x \<lhd> \<sigma> \<lozenge> \<gamma>\<close> by blast
      with neq_x_y instance_of_\<sigma> have \<open>Var x \<lhd> \<sigma> = Var x \<lhd> \<sigma> \<lhd> \<gamma>\<close> by auto
      then show False using neq by auto
    qed
  qed
  then show ?thesis using vars_of_instances [of u \<sigma>] by auto
qed

lemma no_variable_introduction_lit:
  assumes \<open>MGU \<sigma> s t\<close>
  assumes \<open>Idem \<sigma>\<close>
  shows \<open>vars_of_lit (subst_lit L \<sigma>) \<subseteq> vars_of s \<union> vars_of t \<union> vars_of_lit L\<close>
proof (cases L)
  case (Pos e)
  then show ?thesis
  proof (cases e)
    case (Eq u1 u2)
    then show ?thesis using Pos assms Idem_MGU_no_variable_introduction [of \<sigma> s t] by auto
  qed
next
  case (Neg e)
  then show ?thesis
  proof (cases e)
    case (Eq u1 u2)
    then show ?thesis using Neg assms Idem_MGU_no_variable_introduction [of \<sigma> s t] by auto
  qed
qed

lemma no_variable_introduction_cl:
  assumes \<open>MGU \<sigma> s t\<close>
  assumes \<open>Idem \<sigma>\<close>
  shows \<open>vars_of_cl (subst_cl C \<sigma>) \<subseteq> vars_of s \<union> vars_of t \<union> vars_of_cl C\<close>
proof
  fix x
  assume \<open>x \<in> vars_of_cl (subst_cl C \<sigma>)\<close>
  then obtain L where \<open>L \<in> C\<close> and \<open>x \<in> vars_of_lit (subst_lit L \<sigma>)\<close> by auto
  then show \<open>x \<in> vars_of s \<union> vars_of t \<union> vars_of_cl C\<close>
    using no_variable_introduction_lit [of \<sigma> s t] assms by auto
qed

(* To ground first-order inferences, we need their unifier *)
(*datatype 'b fo_inference = Fo_Infer (inf: \<open>'b fclause inference\<close>) (subst: \<open>'b subst\<close>)*)

definition fo_reflexion_inferences :: \<open>'a fclause inference set\<close> where
\<open>fo_reflexion_inferences = {Infer [P] (fcl_remove_trms C) | P C \<sigma>. \<exists> C'. reflexion (Rep_fclause P) C \<sigma> FirstOrder C'}\<close>

definition fo_factorization_inferences :: \<open>'a fclause inference set\<close> where
\<open>fo_factorization_inferences = {Infer [P] (fcl_remove_trms C) | P C \<sigma>. \<exists> C'. factorization (Rep_fclause P) C \<sigma> FirstOrder C'}\<close>

definition fo_superposition_inferences :: \<open>'a fclause inference set\<close> where
\<open>fo_superposition_inferences = {Infer [P1 , P2] (fcl_remove_trms C) | P1 P2 C \<sigma>. \<exists> C'. superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'}\<close>

abbreviation fo_superposition_inference_system :: \<open>'a fclause inference set\<close>
  where
\<open>fo_superposition_inference_system \<equiv> fo_reflexion_inferences
                                   \<union> fo_factorization_inferences
                                   \<union> fo_superposition_inferences\<close>

interpretation fo_inf: sound_inference_system \<open>empty_fclauses\<close> \<open>(\<Turnstile>F)\<close> fo_superposition_inference_system
proof
  show \<open>\<iota> \<in> fo_superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close> for \<iota>
  proof -
    assume \<open>\<iota> \<in> fo_superposition_inference_system\<close>
    then consider (a) \<open>\<iota> \<in> fo_reflexion_inferences\<close>
      | (b) \<open>\<iota> \<in> fo_factorization_inferences\<close>
      | (c) \<open>\<iota> \<in> fo_superposition_inferences\<close>
      by auto
    then show \<open>set (prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}\<close>
    proof cases
      case a
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and reflexion: \<open>reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        using fo_reflexion_inferences_def Rep_fclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_fclause P)) (cl_ecl C)\<close>
        using reflexion_is_sound by force
      moreover have \<open>cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
        using fcl_remove_trms_cl_ecl reflexion_preserves_finiteness finite_P reflexion by blast
      ultimately show ?thesis
        unfolding fclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case b
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and factorization: \<open>factorization (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        using fo_factorization_inferences_def Rep_fclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_fclause P)) (cl_ecl C)\<close>
        using factorization_is_sound by force
      moreover have \<open>cl_ecl (Rep_fclause (fcl_remove_trms C)) = cl_ecl C\<close>
        using fcl_remove_trms_cl_ecl factorization_preserves_finiteness finite_P factorization by blast
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
  where \<open>gen_substs \<iota> = { subst I | I. inf I = \<iota> \<and> I \<in> fo_reflexion_inferences \<union> fo_factorization_inferences \<union> fo_superposition_inferences }\<close>

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
    from assms(1) consider (refl) \<open>\<iota> \<in> inf ` fo_reflexion_inferences\<close>
      | (fact) \<open>\<iota> \<in> inf ` fo_factorization_inferences\<close>
      | (supr) \<open>\<iota> \<in> inf ` fo_superposition_inferences\<close>
      by auto
    then show ?thesis
    proof cases
      case refl
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
          and reflexion: \<open>reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
          and idem: \<open>Idem \<sigma>\<close>
        using fo_reflexion_inferences_def Rep_fclause by fastforce
      then obtain L1 t s
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_fclause P)\<close>
        and L1_def: \<open>L1 = Neg (Eq s t) \<or> L1 = Neg (Eq t s)\<close>
        and mgu: \<open>MGU \<sigma> t s\<close>
        and cl_C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_fclause P) - {L1}) \<sigma>\<close>
        unfolding reflexion_def orient_lit_inst_def ck_unifier_def by fastforce
      have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) = vars_of_cl (cl_ecl (Rep_fclause (fcl_remove_trms C)))\<close>
        using \<iota>_def by auto
      also have \<open>... = vars_of_cl (cl_ecl C)\<close>
        using fcl_remove_trms_cl_ecl [of C] finite_P reflexion_preserves_finiteness [of \<open>Rep_fclause P\<close> C \<sigma> FirstOrder C'] reflexion
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
          and factorization: \<open>factorization (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
          and idem: \<open>Idem \<sigma>\<close>
        using fo_factorization_inferences_def Rep_fclause by fastforce
      then obtain L1 L2 L' t s v u
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_fclause P)\<close>
        and L1_def: \<open>L1 = Pos (Eq t s) \<or> L1 = Pos (Eq s t) \<or> L1 = Neg (Eq t s) \<or> L1 = Neg (Eq s t)\<close>
        and L2_def: \<open>L2 = Pos (Eq u v) \<or> L2 = Pos (Eq v u) \<or> L2 = Neg (Eq u v) \<or> L2 = Neg (Eq v u)\<close>
        and L2_elem: \<open>L2 \<in> cl_ecl (Rep_fclause P) - {L1}\<close>
        and L'_def: \<open>L' = Neg (Eq s v)\<close>
        and C'_def: \<open>C' = cl_ecl (Rep_fclause P) - {L2} \<union> {L'}\<close>
        and cl_C_def: \<open>cl_ecl C = subst_cl C' \<sigma>\<close>
        and \<open>ck_unifier t u \<sigma> FirstOrder\<close>
        unfolding factorization_def orient_lit_inst_def by metis
      then have mgu: \<open>MGU \<sigma> t u\<close>
        unfolding ck_unifier_def by metis
      have \<open>vars_of_cl (cl_ecl (Rep_fclause (concl_of \<iota>))) = vars_of_cl (cl_ecl (Rep_fclause (fcl_remove_trms C)))\<close>
        using \<iota>_def by auto
      also have \<open>... = vars_of_cl (cl_ecl C)\<close>
        using fcl_remove_trms_cl_ecl [of C] finite_P factorization_preserves_finiteness [of \<open>Rep_fclause P\<close> C \<sigma> FirstOrder C'] factorization
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

(*lemma reflexion_grounding:
  assumes \<open>reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
  assumes \<open>grounding_subst (\<sigma> \<lozenge> \<theta>) P\<close>
  assumes \<open>Idem \<sigma>\<close>
  shows \<open>\<exists>C'. reflexion (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close>
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
    unfolding reflexion_def by auto
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
  ultimately show ?thesis unfolding reflexion_def by blast
qed*)

(*lemma grounding_inference_preserves_system:
  \<open>\<kappa> \<in> grounding_inference \<iota> \<Longrightarrow> \<kappa> \<in> ground_superposition_inference_system\<close>
proof -
  assume \<open>\<kappa> \<in> grounding_inference \<iota>\<close>
  then obtain \<sigma> \<theta>
    where \<kappa>_def: \<open>\<kappa> = Infer (map (subst_fclause (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>)) (subst_fclause (\<sigma> \<lozenge> \<theta>) (concl_of \<iota>))\<close>
      and \<open>Fo_Infer \<iota> \<sigma> \<in> fo_reflexion_inferences \<union> fo_factorization_inferences \<union> fo_superposition_inferences \<close>
      and grounding_prems: \<open>list_all (grounding_subst (\<sigma> \<lozenge> \<theta>)) (prems_of \<iota>)\<close>
    unfolding grounding_inference_def by force
  then consider (refl) \<open>\<exists>P C C'. \<iota> = Infer [P] (fcl_remove_trms C) \<and> reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
    | (fact) \<open>\<exists>P C C'. \<iota> = Infer [P] (fcl_remove_trms C) \<and> factorization (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
    | (supr) \<open>\<exists>P1 P2 C C'. \<iota> = Infer [P1, P2] (fcl_remove_trms C) \<and> superposition (Rep_fclause P1) (Rep_fclause P2) C \<sigma> FirstOrder C'\<close>
    unfolding fo_reflexion_inferences_def fo_factorization_inferences_def fo_superposition_inferences_def by blast
  then show \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
  proof cases
    case refl
    then obtain P C C'
      where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
        and \<open>reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close> by auto
    then have \<open>reflexion (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close> sorry
    moreover from \<iota>_def \<kappa>_def have \<open>\<kappa> = Infer [subst_fclause (\<sigma> \<lozenge> \<theta>) P] (gcl_remove_trms (subst_ecl C (\<sigma> \<lozenge> \<theta>)))\<close> sorry
    moreover have \<open>ground_clause (cl_ecl (subst_ecl C (\<sigma> \<lozenge> \<theta>)))\<close> sorry
    ultimately have \<open>\<kappa> \<in> ground_reflexion_inferences\<close> unfolding ground_reflexion_inferences_def by blast
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
  then consider (refl) \<open>\<iota> \<in> fo_reflexion_inferences\<close>
    | (fact) \<open>\<iota> \<in> fo_factorization_inferences\<close>
    | (supr) \<open>\<iota> \<in> fo_superposition_inferences\<close> by auto
  then show \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
  proof cases
    case refl
    then obtain P C \<sigma> C'
      where \<iota>_def: \<open>\<iota> = Infer [P] (fcl_remove_trms C)\<close>
        and finite_P: \<open>finite (cl_ecl (Rep_fclause P))\<close>
        and reflexion: \<open>reflexion (Rep_fclause P) C \<sigma> FirstOrder C'\<close>
        and idem: \<open>Idem \<sigma>\<close>
      using fo_reflexion_inferences_def Rep_fclause by fastforce
    with \<kappa>_elem obtain \<theta>
      where \<kappa>_def: \<open>\<kappa> = Infer [subst_fclause \<theta> P] (subst_fclause \<theta> (fcl_remove_trms C))\<close>
        and \<theta>_grounding_prems: \<open>grounding_subst \<theta> P\<close>
      unfolding grounding_inference_def list_all_def by auto
    from finite_P reflexion have finite_C: \<open>finite (cl_ecl C)\<close> using reflexion_preserves_finiteness by blast
    from \<theta>_grounding_prems \<iota>_elem have \<theta>_grounding_concl: \<open>grounding_subst \<theta> (fcl_remove_trms C)\<close>
      using \<iota>_def grounding_prems_grounding_concl [of \<iota> \<theta>] by auto
    have concl_def: \<open>subst_fclause \<theta> (fcl_remove_trms C) = Abs_gclause (Ecl (subst_cl (cl_ecl C) \<theta>) {})\<close>
      using finite_C substs_preserve_finiteness [of \<open>cl_ecl C\<close> \<theta>] fcl_remove_trms_cl_ecl by auto
    have \<open>\<kappa> \<in> ground_reflexion_inferences\<close>
    proof -
      have concl_def': \<open>gcl_remove_trms (subst_ecl C \<theta>) = Abs_gclause (Ecl (subst_cl (cl_ecl C) \<theta>) {})\<close>
        by (metis (no_types, lifting) cl_ecl.simps gcl_remove_trms.elims subst_ecl.simps cl_ecl.elims trms_ecl.simps)
      have \<open>\<kappa> = Infer [subst_fclause \<theta> P] (gcl_remove_trms (subst_ecl C \<theta>))\<close>
        using concl_def concl_def' \<kappa>_def by auto
      moreover have \<open>reflexion (Rep_gclause (subst_fclause (\<sigma> \<lozenge> \<theta>) P)) (subst_ecl C (\<sigma> \<lozenge> \<theta>)) [] Ground (subst_cl C' (\<sigma> \<lozenge> \<theta>))\<close>
        using reflexion idem \<theta>_grounding_prems reflexion_grounding by blast
      moreover have \<open>ground_clause (cl_ecl (subst_ecl C \<theta>))\<close>
      proof -
        have \<open>cl_ecl (subst_ecl C \<theta>) = subst_cl (cl_ecl C) \<theta>\<close>
          by (smt cl_ecl.elims eclause.inject subst_ecl.simps)
        then show ?thesis
          using \<theta>_grounding_concl finite_C substs_preserve_finiteness fcl_remove_trms_cl_ecl by auto
      qed
      ultimately show ?thesis unfolding ground_reflexion_inferences_def sorry
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
  empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_gclause grounding_clause grounding_inference
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
  show \<open>\<iota> \<in> fo_superposition_inference_system \<Longrightarrow> grounding_inference \<iota> \<subseteq> Red_Inf_sup (grounding_clause (concl_of \<iota>))\<close> for \<iota>
  proof
    fix \<kappa>
    assume \<open>\<iota> \<in> fo_superposition_inference_system\<close> and \<open>\<kappa> \<in> grounding_inference \<iota>\<close>
    then obtain \<sigma> where \<open>\<kappa> = Infer (map (subst_fclause \<sigma>) (prems_of \<iota>)) (subst_fclause \<sigma> (concl_of \<iota>))\<close>
                    and \<open>concl_of \<kappa> \<in> grounding_clause (concl_of \<iota>)\<close>
                    and \<open>\<kappa> \<in> ground_superposition_inference_system\<close>
      unfolding grounding_inference_def grounding_clause_def by auto
    then show \<open>\<kappa> \<in> Red_Inf_sup (grounding_clause (concl_of \<iota>))\<close>
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
empty_fclauses \<open>(\<Turnstile>F)\<close> fo_superposition_inference_system empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_gclause
proof
  show \<open>\<iota> \<in> ground_inf.Inf_from (\<G>_set N) \<Longrightarrow> \<iota> \<in> Red_Inf_sup (\<G>_set N) \<or> (\<exists>\<kappa>. \<kappa> \<in> fo_inf.Inf_from N \<and> \<iota> \<in> grounding_inference \<kappa>)\<close> for N \<iota>
  proof -
    assume \<open>\<iota> \<in> ground_inf.Inf_from (\<G>_set N)\<close>
    then consider (refl) \<open>\<iota> \<in> ground_reflexion_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      | (fact) \<open>\<iota> \<in> ground_factorization_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      | (supr) \<open>\<iota> \<in> ground_superposition_inferences \<and> set (prems_of \<iota>) \<subseteq> \<G>_set N\<close>
      unfolding ground_inf.Inf_from_def by auto
    then show \<open>\<iota> \<in> Red_Inf_sup (\<G>_set N) \<or> (\<exists>\<kappa>. \<kappa> \<in> fo_inf.Inf_from N \<and> \<iota> \<in> grounding_inference \<kappa>)\<close>
    proof cases
      case refl
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (gcl_remove_trms C)\<close>
          and reflexion: \<open>reflexion (Rep_gclause P) C \<sigma> Ground C'\<close>
          and \<open>ground_clause (cl_ecl C)\<close>
          and \<open>P \<in> \<G>_set N\<close>
        unfolding ground_reflexion_inferences_def by auto
      then obtain P' \<theta>
        where P'_elem: \<open>P' \<in> N\<close>    
          and P_subst: \<open>subst_fclause \<theta> P' = P\<close>
          and grounding_\<theta>: \<open>grounding_subst \<theta> P'\<close>
        unfolding grounding_clause_def by blast
      from reflexion obtain L1 s t
        where L1_elem: \<open>L1 \<in> cl_ecl (Rep_gclause P)\<close>
          and L1_def: \<open>orient_lit_inst L1 t s neg \<sigma>\<close>
          and C_def: \<open>cl_ecl C = subst_cl (cl_ecl (Rep_gclause P) - {L1}) \<sigma>\<close>
        unfolding reflexion_def by blast
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
      also have \<open>... = subst_cl (cl_ecl (Rep_fclause P')) - {subst_lit L1' \<theta>}\<close>
      also have \<open>... = subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta>\<close> using L1'_elem by try0
      have \<open>subst_cl (cl_ecl (Rep_fclause P') - {L1'}) \<theta> = cl_ecl C\<close> sorry
      then have \<open>subst_cl (cl_ecl (Rep_fclause ?D)) \<theta> = cl_ecl C\<close>
        using Abs_fclause_inverse [of \<open>Ecl (cl_ecl (Rep_fclause P') - {L1'}) {}\<close>] Rep_fclause [of P'] by auto
      then have D_subst: \<open>subst_fclause \<theta> ?D = gcl_remove_trms C\<close> by auto
      have grounding_\<theta>_D: \<open>grounding_subst \<theta> ?D\<close>
        using Abs_fclause_inverse [of \<open>Ecl (cl_ecl (Rep_fclause P') - {L1'}) {}\<close>] Rep_fclause [of P'] grounding_\<theta> by auto
      let ?\<kappa> = \<open>Infer [P'] ?D\<close>
      have \<open>?\<kappa> \<in> fo_reflexion_inferences\<close> sorry
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