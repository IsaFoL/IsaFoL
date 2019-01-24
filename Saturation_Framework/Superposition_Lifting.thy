theory Superposition_Lifting
  imports Nonground_Calculus_Lifting SuperCalc.superposition
begin

typedef 'a ground_eclause = \<open>{C :: 'a eclause. finite (cl_ecl C)
                                             \<and> ground_clause (cl_ecl C)}\<close>
apply(rule_tac x = \<open>Ecl {} {}\<close> in exI)
  by simp

definition eclause_entails :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause set \<Rightarrow> bool\<close> (infix "\<Turnstile>E" 50)
  where
\<open>N1 \<Turnstile>E N2 \<equiv> \<forall>C2 \<in> N2. set_entails_clause (cl_ecl ` Rep_ground_eclause ` N1) (cl_ecl (Rep_ground_eclause C2))\<close>

abbreviation empty_eclauses :: \<open>'a ground_eclause set\<close>
  where \<open>empty_eclauses \<equiv> {C. cl_ecl (Rep_ground_eclause C) = {}}\<close>

lemma empty_clause_entails: \<open>set_entails_clause {{}} C\<close>
  unfolding set_entails_clause_def by auto

interpretation consequence_relation empty_eclauses \<open>(\<Turnstile>E)\<close>
proof
  show \<open>B \<in> empty_eclauses \<Longrightarrow> {B} \<Turnstile>E N1\<close> for B :: \<open>'a ground_eclause\<close> and N1
    unfolding eclause_entails_def
    using empty_clause_entails by force
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>E N2\<close> for N2 N1 :: \<open>'a ground_eclause set\<close>
    unfolding eclause_entails_def
    by (simp add: set_entails_clause_member set_mp)
  show \<open>\<forall>C\<in>N2. N1 \<Turnstile>E {C} \<Longrightarrow> N1 \<Turnstile>E N2\<close> for N2 N1 :: \<open>'a ground_eclause set\<close>
    unfolding eclause_entails_def by fast
  show \<open>N1 \<Turnstile>E N2 \<Longrightarrow> N2 \<Turnstile>E N3 \<Longrightarrow> N1 \<Turnstile>E N3\<close> for N1 N2 N3 :: \<open>'a ground_eclause set\<close>
    unfolding eclause_entails_def set_entails_clause_def by force
qed

context basic_superposition
begin

definition ground_reflexion_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_reflexion_inferences = {Infer [P] C | P C. \<exists> \<sigma> C'. reflexion (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C'}\<close>

definition ground_factorization_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_factorization_inferences = {Infer [P] C | P C. \<exists> \<sigma> C'. factorization (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C'}\<close>

definition ground_superposition_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_superposition_inferences = {Infer [P1 , P2] C | P1 P2 C. \<exists> \<sigma> C'. superposition (Rep_ground_eclause P1) (Rep_ground_eclause P2) (Rep_ground_eclause C) \<sigma> Ground C'}\<close>

abbreviation ground_superposition_inference_system :: \<open>'a ground_eclause inference set\<close>
  where
\<open>ground_superposition_inference_system \<equiv> ground_reflexion_inferences
                                       \<union> ground_factorization_inferences
                                       \<union> ground_superposition_inferences\<close>

interpretation sound_inference_system \<open>empty_eclauses\<close> \<open>(\<Turnstile>E)\<close> ground_superposition_inference_system
proof
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> set (prems_of \<iota>) \<Turnstile>E {concl_of \<iota>}\<close> for \<iota>
  proof -
    assume \<open>\<iota> \<in> ground_superposition_inference_system\<close>
    then consider (a) \<open>\<iota> \<in> ground_reflexion_inferences\<close>
      | (b) \<open>\<iota> \<in> ground_factorization_inferences\<close>
      | (c) \<open>\<iota> \<in> ground_superposition_inferences\<close>
      by auto
    then show \<open>set (prems_of \<iota>) \<Turnstile>E {concl_of \<iota>}\<close>
    proof cases
      case a
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] C\<close> and \<open>finite (cl_ecl (Rep_ground_eclause P))\<close> and \<open>reflexion (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C'\<close>
        using ground_reflexion_inferences_def Rep_ground_eclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_ground_eclause P)) (cl_ecl (Rep_ground_eclause C))\<close>
        using reflexion_is_sound by force
      then show ?thesis
        unfolding eclause_entails_def clause_entails_clause_def set_entails_clause_def \<iota>_def by simp
    next
      case b
      then obtain P C \<sigma> k C'
        where \<iota>_def: \<open>\<iota> = Infer [P] C\<close> and \<open>finite (cl_ecl (Rep_ground_eclause P))\<close> and \<open>factorization (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> k C'\<close>
        using ground_factorization_inferences_def Rep_ground_eclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_ground_eclause P)) (cl_ecl (Rep_ground_eclause C))\<close>
        using factorization_is_sound by force
      then show ?thesis
        unfolding eclause_entails_def clause_entails_clause_def set_entails_clause_def \<iota>_def by simp
    next
      case c
      then obtain P1 P2 C \<sigma> k C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] C\<close> and \<open>finite (cl_ecl (Rep_ground_eclause P1))\<close> and \<open>finite (cl_ecl (Rep_ground_eclause P2))\<close> and \<open>superposition (Rep_ground_eclause P1) (Rep_ground_eclause P2) (Rep_ground_eclause C) \<sigma> k C'\<close>
        using ground_superposition_inferences_def Rep_ground_eclause by fastforce
      then have \<open>set_entails_clause {cl_ecl (Rep_ground_eclause P1), cl_ecl (Rep_ground_eclause P2)} (cl_ecl (Rep_ground_eclause C))\<close>
        using superposition_is_sound by force
      moreover have \<open>{cl_ecl (Rep_ground_eclause C1) |C1. C1 \<in> set (prems_of \<iota>)} = {cl_ecl (Rep_ground_eclause P1), cl_ecl (Rep_ground_eclause P2)}\<close>
        using \<iota>_def by force
      ultimately show ?thesis
        unfolding eclause_entails_def \<iota>_def by simp
    qed
  qed
qed

(* check definition against notion of saturation as defined by Nicolas *)
definition Red_Inf_sup :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause inference set\<close> where
\<open>Red_Inf_sup N = {\<iota>. \<iota> \<in> ground_superposition_inference_system
                 \<and> (\<forall> \<sigma>. redundant_inference (Rep_ground_eclause (concl_of \<iota>)) (Rep_ground_eclause ` N) (Rep_ground_eclause ` (set (prems_of \<iota>))) \<sigma>) }\<close>

definition Red_eclause :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause set\<close> where
\<open>Red_eclause N = {C. \<exists> \<sigma> C'. redundant_clause (Rep_ground_eclause C) (Rep_ground_eclause ` N) \<sigma> C'}\<close>

lemma redundant_inference_superset:
  \<open>N \<subseteq> N' \<Longrightarrow> redundant_inference C N P \<sigma> \<Longrightarrow> redundant_inference C N' P \<sigma>\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have \<open>instances N \<subseteq> instances N'\<close> unfolding instances_def by auto
  then show \<open>redundant_inference C N P \<sigma> \<Longrightarrow> redundant_inference C N' P \<sigma>\<close> unfolding redundant_inference_def by fastforce
qed

lemma redundant_clause_superset:
  \<open>N \<subseteq> N' \<Longrightarrow> redundant_clause C N \<sigma> C' \<Longrightarrow> redundant_clause C N' \<sigma> C'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have \<open>instances N \<subseteq> instances N'\<close> unfolding instances_def by auto
  then show \<open>redundant_clause C N \<sigma> C' \<Longrightarrow> redundant_clause C N' \<sigma> C'\<close> unfolding redundant_clause_def by fastforce
qed

definition gecl_ord :: \<open>('a ground_eclause \<times> 'a ground_eclause) set\<close>
  where \<open>gecl_ord \<equiv> {(C,D). (mset_ecl (Rep_ground_eclause C, []), mset_ecl (Rep_ground_eclause D, [])) \<in> mult (mult (trm_ord))}\<close>

lemma wf_gecl_ord: \<open>wf gecl_ord\<close>
proof -
  have \<open>wf (mult trm_ord)\<close> using trm_ord_wf and wf_mult  by auto
  then have \<open>wf (mult (mult trm_ord))\<close> using wf_mult  by auto
  thus ?thesis 
    using gecl_ord_def and measure_wf [of \<open>(mult (mult trm_ord))\<close> gecl_ord \<open>\<lambda>C. mset_ecl (Rep_ground_eclause C, [])\<close>] by blast
qed

lemma wf_mult_gecl_ord: \<open>wf (mult gecl_ord)\<close>
  using wf_mult wf_gecl_ord by auto

lemma Red_eclause_finite_subset: \<open>C \<in> Red_eclause N \<Longrightarrow> \<exists>N' \<subseteq> N. finite N' \<and> C \<in> Red_eclause N' \<and> (\<forall>D \<in> N'. (D,C) \<in>gecl_ord)\<close>
proof -
  assume \<open>C \<in> Red_eclause N\<close>
  then obtain cl_C \<sigma>_C where \<open>redundant_clause (Rep_ground_eclause C) (Rep_ground_eclause ` N) \<sigma>_C cl_C\<close>
    unfolding Red_eclause_def by auto
  then obtain S where i: \<open>S \<subseteq> instances (Rep_ground_eclause ` N)\<close>
                  and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_ground_eclause C))\<close>
                  and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_ground_eclause C))\<close>
                  and iv: \<open>\<forall>x \<in> S. (mset_ecl x, mset_cl (cl_C, \<sigma>_C)) \<in> mult (mult trm_ord)
                           \<or> (mset_ecl ((fst x),(snd x))) = mset_cl (cl_C, \<sigma>_C)\<close>
    unfolding redundant_clause_def by auto
  let ?N' = \<open>{C. \<exists>\<sigma>. (Rep_ground_eclause C, \<sigma>) \<in> S}\<close>
  have \<open>?N' \<subseteq> N\<close> using i instances_def
    by (smt Collect_mem_eq Collect_mono_iff Pair_inject Rep_ground_eclause_inject image_iff)
  moreover have \<open>finite ?N'\<close> sorry
  moreover have \<open>C \<in> Red_eclause ?N'\<close>
  proof -
    have \<open>S \<subseteq> instances (Rep_ground_eclause ` ?N')\<close>
      by (smt i imageE image_eqI instances_def mem_Collect_eq subsetCE subsetI)
    with ii iii iv have \<open>redundant_clause (Rep_ground_eclause C) (Rep_ground_eclause ` ?N') \<sigma>_C cl_C\<close>
      unfolding redundant_clause_def by auto
    then show ?thesis unfolding Red_eclause_def by auto
  qed
  moreover have \<open>D \<in> ?N' \<Longrightarrow> (D,C) \<in> gecl_ord\<close> for D sorry
  ultimately show ?thesis by auto
qed

lemma Red_eclause_entails: \<open>N \<Turnstile>E Red_eclause N\<close>
proof (intro all_formulas_entailed)
  show \<open>\<forall>C\<in>Red_eclause N. N \<Turnstile>E {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain cl_C \<sigma>_C where \<open>redundant_clause (Rep_ground_eclause C) (Rep_ground_eclause ` N) \<sigma>_C cl_C\<close>
      unfolding Red_eclause_def by auto
    then obtain S where i: \<open>S \<subseteq> instances (Rep_ground_eclause ` N)\<close>
                    and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_ground_eclause C))\<close>
      unfolding redundant_clause_def by auto
    have \<open>D \<in> clset_instances S \<Longrightarrow> set_entails_clause (cl_ecl ` Rep_ground_eclause ` N) D\<close> for D
    proof -
      assume \<open>D \<in> clset_instances S\<close>
      with i obtain cl_D \<sigma>_D where \<open>D = subst_cl (cl_ecl cl_D) \<sigma>_D\<close>
                               and \<open>cl_D \<in> Rep_ground_eclause ` N\<close>
                               and \<open>ground_clause (subst_cl (cl_ecl cl_D) \<sigma>_D)\<close>
        unfolding clset_instances_def instances_def by auto
      then show \<open>set_entails_clause (cl_ecl ` Rep_ground_eclause ` N) D\<close>
        by (metis (no_types, lifting) Rep_ground_eclause imageI image_subset_iff mem_Collect_eq set_entails_clause_member subset_eq substs_preserve_ground_clause)
    qed
    with ii have \<open>set_entails_clause (cl_ecl ` Rep_ground_eclause ` N) (cl_ecl (Rep_ground_eclause C))\<close>
      unfolding set_entails_clause_def by auto
    then show \<open>N \<Turnstile>E {C}\<close> unfolding eclause_entails_def by auto
  qed
qed

lemma Red_eclause_superset: \<open>N \<subseteq> N' \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause N'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have inst_subset: \<open>instances (Rep_ground_eclause ` N) \<subseteq> instances (Rep_ground_eclause ` N')\<close>
    using instances_def by auto
  then show \<open>Red_eclause N \<subseteq> Red_eclause N'\<close>
    by (smt CollectI Red_eclause_def \<open>N \<subseteq> N'\<close> image_Un mem_Collect_eq redundant_clause_superset subsetI subset_Un_eq)
qed

lemma minimal_redundancy_subset:
  assumes \<open>C \<in> Red_eclause N\<close>
  shows \<open>\<exists>M. set_mset M \<subseteq> N \<and> C \<in> Red_eclause (set_mset M) \<and> (\<forall>X. (X, M) \<in> mult gecl_ord \<longrightarrow> set_mset X \<subseteq> N \<longrightarrow> C \<notin> Red_eclause (set_mset X))\<close>
proof -
  from assms obtain N' where \<open>finite N'\<close> and \<open>N' \<subseteq> N\<close> and \<open>C \<in> Red_eclause N'\<close> using Red_eclause_finite_subset by metis
  then have \<open>set_mset (mset_set N') \<subseteq> N \<and> C \<in> Red_eclause (set_mset (mset_set N'))\<close> (is \<open>?P (mset_set N')\<close>) by auto
  then obtain M where M'_prop: \<open>?P M\<close> and M'_min: \<open>(X, M) \<in> mult gecl_ord ==> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>mult gecl_ord\<close> \<open>mset_set N'\<close> \<open>{x. ?P x}\<close>] and wf_mult_gecl_ord by auto
  then show ?thesis by blast
qed

lemma redundant_minimal_subset: \<open>C \<in> Red_eclause N \<Longrightarrow> C \<in> Red_eclause (N - Red_eclause N)\<close> sorry

lemma Red_eclause_entailed: \<open>N - Red_eclause N \<Turnstile>E Red_eclause N\<close>
proof (intro all_formulas_entailed)
  show \<open>\<forall>C \<in> Red_eclause N. N - Red_eclause N \<Turnstile>E {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain M where M_subset: \<open>set_mset M \<subseteq> N\<close>
                    and C_Red: \<open>C \<in> Red_eclause (set_mset M)\<close>
                    and \<open>(\<forall>X. (X, M) \<in> mult gecl_ord \<longrightarrow> set_mset X \<subseteq> N \<longrightarrow> C \<notin> Red_eclause (set_mset X))\<close>
      using minimal_redundancy_subset by metis
    have \<open>D \<in> set_mset M \<Longrightarrow> D \<notin> Red_eclause N\<close> for D sorry
    with M_subset have \<open>set_mset M \<subseteq> N - Red_eclause N\<close> by auto
    then have \<open>N - Red_eclause N \<Turnstile>E set_mset M\<close> using subset_entailed by auto
    moreover have \<open>set_mset M \<Turnstile>E {C}\<close> using C_Red Red_eclause_entails entail_set_all_formulas by auto
    ultimately show \<open>N - Red_eclause N \<Turnstile>E {C}\<close> using entails_trans by auto
  qed
qed

interpretation calculus empty_eclauses \<open>(\<Turnstile>E)\<close> ground_superposition_inference_system \<open>(\<Turnstile>E)\<close> Red_Inf_sup Red_eclause
proof
  show \<open>Red_Inf_sup N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_Inf_sup_def by auto
next
  show \<open>B \<in> empty_eclauses \<Longrightarrow> N \<Turnstile>E {B} \<Longrightarrow> N - Red_eclause N \<Turnstile>E {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> empty_eclauses\<close> and \<open>N \<Turnstile>E {B}\<close>
    then have N_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not>validate_clause_set I (cl_ecl ` Rep_ground_eclause ` N)\<close> for I
      unfolding eclause_entails_def set_entails_clause_def by auto
    assume \<open>\<not> N - Red_eclause N \<Turnstile>E {B}\<close>
    with N_unsat obtain I where fo_I: \<open>fo_interpretation I\<close>
                          and I_model: \<open>validate_clause_set I (cl_ecl ` Rep_ground_eclause ` (N - Red_eclause N))\<close>
                          and \<open>\<not>validate_clause_set I (cl_ecl ` Rep_ground_eclause ` N)\<close>
      unfolding eclause_entails_def set_entails_clause_def by fast
    then obtain C where \<open>C \<in> Red_eclause N\<close> and \<open>\<not> validate_clause I (cl_ecl (Rep_ground_eclause C))\<close>
      by (smt DiffI image_iff validate_clause_set.simps)
    moreover with Red_eclause_entailed fo_I I_model have \<open>validate_clause I (cl_ecl (Rep_ground_eclause C))\<close>
      unfolding eclause_entails_def set_entails_clause_def by blast
    ultimately show False by blast
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause N'\<close> for N N' using Red_eclause_superset by auto
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close> for N N'
  proof -
    assume subset: \<open>N \<subseteq> N'\<close>
    then have inst_subset: \<open>instances (Rep_ground_eclause ` N) \<subseteq> instances (Rep_ground_eclause ` N')\<close>
      using instances_def by auto
    then show \<open>Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close>
      by (smt Red_Inf_sup_def image_Un mem_Collect_eq redundant_inference_superset subset subsetI subset_Un_eq)
  qed
next
  show \<open>N' \<subseteq> Red_eclause N \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause (N - N')\<close> for N' N
  proof
    fix C
    assume \<open>N' \<subseteq> Red_eclause N\<close>
    then have subset: \<open>N - Red_eclause N \<subseteq> N - N'\<close> by blast
    assume \<open>C \<in> Red_eclause N\<close>
    with redundant_minimal_subset have \<open>C \<in> Red_eclause (N - Red_eclause N)\<close> by auto
    with subset show \<open>C \<in> Red_eclause (N - N')\<close>
      by (smt image_mono mem_Collect_eq redundant_clause_superset Red_eclause_def)
  qed
next
  show \<open>N' \<subseteq> Red_eclause N \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup (N - N')\<close> for N' N sorry
next
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_sup N\<close> for \<iota> N sorry
qed

lemma derivable_ground_eclause:
  assumes \<open>ground_clause (cl_ecl C)\<close>
  assumes \<open>derivable C P (Rep_ground_eclause ` N) \<sigma> Ground C'\<close>
  shows \<open>\<exists> \<iota> \<in> Inf_from N. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = P\<close>
proof -
  from assms consider
      (a) \<open>\<exists>P1 P2. P1 \<in> (Rep_ground_eclause ` N) \<and> P2 \<in> (Rep_ground_eclause ` N) \<and> P = {P1, P2} \<and> superposition P1 P2 C \<sigma> Ground C'\<close>
    | (b) \<open>\<exists>P1. P1 \<in> (Rep_ground_eclause ` N) \<and> P = {P1} \<and> factorization P1 C \<sigma> Ground C'\<close>
    | (c) \<open>\<exists>P1. P1 \<in> (Rep_ground_eclause ` N) \<and> P = {P1} \<and> reflexion P1 C \<sigma> Ground C'\<close>
    unfolding derivable_def by blast
  then show \<open>\<exists> \<iota> \<in> Inf_from N. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = P\<close>
  proof cases
  case a
    (*then obtain P1 P2 where P_prop1: \<open>P = {P1, P2}\<close>
                      and P_prop2: \<open>P1 \<in> (Rep_ground_eclause ` N) \<and> P2 \<in> (Rep_ground_eclause ` N)\<close>
                      and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
                      and \<open>finite (cl_ecl P1)\<close>
                      and \<open>finite (cl_ecl P2)\<close> using Rep_ground_eclause by blast
    then have \<open>Infer [Abs_ground_eclause P1, Abs_ground_eclause P2] (Abs_ground_eclause C) \<in> ground_superposition_inferences\<close>
      unfolding ground_superposition_inferences_def using Abs_ground_eclause_inverse by blast
    with P_prop1 and Inf_from_def show ?thesis (*by force *) sorry*)
    show ?thesis sorry
  next
    case b
    (*then obtain P1 where P_prop: \<open>P = {P1}\<close>
                   and P_prop2: \<open>P1 \<in> (Rep_ground_eclause ` N)\<close>
                   and \<open>factorization P1 C \<sigma> Ground C'\<close>
                   and \<open>finite (cl_ecl P1)\<close>
                   and \<open>ground_clause (cl_ecl P1)\<close>
                   and \<open>finite (cl_ecl C)\<close>
      using factorization_preserves_finiteness Rep_ground_eclause by blast
    then have \<open>factorization (Rep_ground_eclause (Abs_ground_eclause P1)) C \<sigma> Ground C'\<close>
      using Abs_ground_eclause_inverse assms(1) by try0
    then have inf: \<open>Infer [Abs_ground_eclause P1] (Abs_ground_eclause C) \<in> ground_factorization_inferences\<close>
      unfolding ground_factorization_inferences_def using Abs_ground_eclause_inverse assms(1) by try0
    from P_prop have \<open>P \<subseteq> Abs_ground_eclause ` {P1}\<close> by (metis image_eqI subsetI Rep_ground_eclause_inverse)
    then have \<open>P = { Abs_ground_eclause P1 }\<close> using P_prop by auto
    with Inf_from_def and P_prop2 and inf show ?thesis sorry*)
    show ?thesis sorry
  next
    case c
    (*then obtain P1 where P_prop: \<open>Rep_ground_eclause ` P = {P1} \<and> P1 \<in> (Rep_ground_eclause ` N)\<close>
                   and \<open>reflexion P1 (Rep_ground_eclause C) \<sigma> Ground C'\<close>
                   and \<open>finite (cl_ecl P1)\<close> using Rep_ground_eclause by blast
    then have \<open>Infer [Abs_ground_eclause P1] C \<in> ground_reflexion_inferences\<close>
      unfolding ground_reflexion_inferences_def using Rep_ground_eclause_inverse by blast
    with P_prop and Inf_from_def show ?thesis (*by force *) sorry*)
    show ?thesis sorry
  qed
qed

lemma saturation_ground_eclauses:
  assumes \<open>saturated N\<close>
  shows \<open>ground_inference_saturated (Rep_ground_eclause ` N)\<close>
proof -
  have \<open>derivable C P (Rep_ground_eclause ` N) \<sigma> Ground C' \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> redundant_inference C (Rep_ground_eclause ` N) P \<sigma>\<close> for C P \<sigma> C'
  proof -
    assume \<open>derivable C P (Rep_ground_eclause ` N) \<sigma> Ground C'\<close> and \<open>ground_clause (cl_ecl C)\<close>
    then obtain \<iota> where \<open>\<iota> \<in> Red_Inf_sup N \<and> Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` (set (prems_of \<iota>)) = P\<close>
      using assms saturated_def derivable_ground_eclause by blast
    then show \<open>redundant_inference C (Rep_ground_eclause ` N) P \<sigma>\<close>
      using Red_Inf_sup_def by auto
  qed
  then show ?thesis unfolding ground_inference_saturated_def by auto
qed

interpretation static_refutational_complete_calculus empty_eclauses \<open>(\<Turnstile>E)\<close> ground_superposition_inference_system \<open>(\<Turnstile>E)\<close> Red_Inf_sup Red_eclause
proof
  have \<open>saturated N \<Longrightarrow> \<forall>C \<in> N. C \<notin> empty_eclauses \<Longrightarrow> B \<in> empty_eclauses \<Longrightarrow> \<not> N \<Turnstile>E {B}\<close> for B N
  proof -
    assume \<open>saturated N\<close>
    then have i: \<open>ground_inference_saturated (Rep_ground_eclause ` N)\<close> using saturation_ground_eclauses by auto
    have ii: \<open>\<forall>x \<in> (Rep_ground_eclause ` N). (finite (cl_ecl x))\<close> using Rep_ground_eclause by auto
    assume \<open>\<forall>C \<in> N. C \<notin> empty_eclauses\<close>
    then have iv: \<open>\<forall>x \<in> (Rep_ground_eclause ` N). (cl_ecl x) \<noteq> {}\<close> by auto
    show \<open>\<not> N \<Turnstile>E {B}\<close> sorry
  qed
  then show \<open>saturated N \<Longrightarrow> B \<in> empty_eclauses \<Longrightarrow> N \<Turnstile>E {B} \<Longrightarrow> \<exists>B'\<in>empty_eclauses. B' \<in> N\<close> for B N by blast

qed

end
end