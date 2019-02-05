theory Superposition_Lifting
  imports Nonground_Calculus_Lifting SuperCalc.superposition
begin

(* Ideally, this type would contain only well_constrained clauses, but this is not possible since
   the definition of well_constrained depends on the term ordering, which is not instantiated yet *)
typedef 'a ground_eclause = \<open>{C :: 'a eclause. finite (cl_ecl C)
                                               \<and> ground_clause (cl_ecl C)}\<close>
apply(rule_tac x = \<open>Ecl {} {}\<close> in exI)
  by simp

context basic_superposition
begin

(* In order to discard non well_constrained clauses, they are excluded from the definition of
   entailement, which makes them always redundant *)
abbreviation wellc_eclauses :: \<open>'a ground_eclause set \<Rightarrow> 'a eclause set\<close>
  where \<open>wellc_eclauses N \<equiv> {C \<in> Rep_ground_eclause ` N. well_constrained C}\<close>

definition eclause_entails :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause set \<Rightarrow> bool\<close> (infix "\<Turnstile>E" 50)
  where
\<open>N1 \<Turnstile>E N2 \<equiv> \<forall>C2 \<in> N2. well_constrained (Rep_ground_eclause C2) \<longrightarrow>
                       set_entails_clause (cl_ecl ` wellc_eclauses N1) (cl_ecl (Rep_ground_eclause C2))\<close>

abbreviation empty_eclauses :: \<open>'a ground_eclause set\<close>
  where \<open>empty_eclauses \<equiv> {C. cl_ecl (Rep_ground_eclause C) = {} \<and> well_constrained (Rep_ground_eclause C)}\<close>

lemma empty_clause_entails: \<open>set_entails_clause {{}} C\<close>
  unfolding set_entails_clause_def by auto

interpretation consequence_relation empty_eclauses \<open>(\<Turnstile>E)\<close>
proof
  show \<open>B \<in> empty_eclauses \<Longrightarrow> {B} \<Turnstile>E N1\<close> for B :: \<open>'a ground_eclause\<close> and N1
  proof -
    assume \<open>B \<in> empty_eclauses\<close>
    then have \<open>wellc_eclauses {B} = {Rep_ground_eclause B}\<close> and \<open>cl_ecl (Rep_ground_eclause B) = {}\<close> by auto
    then show \<open>{B} \<Turnstile>E N1\<close>
      unfolding eclause_entails_def
      using empty_clause_entails by force
  qed
  show \<open>N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile>E N2\<close> for N2 N1 :: \<open>'a ground_eclause set\<close>
    unfolding eclause_entails_def
    by (smt CollectI image_eqI set_entails_clause_member set_mp)
  show \<open>\<forall>C\<in>N2. N1 \<Turnstile>E {C} \<Longrightarrow> N1 \<Turnstile>E N2\<close> for N2 N1 :: \<open>'a ground_eclause set\<close>
    unfolding eclause_entails_def by fast
  show \<open>N1 \<Turnstile>E N2 \<Longrightarrow> N2 \<Turnstile>E N3 \<Longrightarrow> N1 \<Turnstile>E N3\<close> for N1 N2 N3 :: \<open>'a ground_eclause set\<close>
  proof -
    assume \<open>N1 \<Turnstile>E N2\<close> and \<open>N2 \<Turnstile>E N3\<close>
    have \<open>C \<in> N3 \<Longrightarrow> well_constrained (Rep_ground_eclause C) \<Longrightarrow> set_entails_clause (cl_ecl ` wellc_eclauses N1) (cl_ecl (Rep_ground_eclause C))\<close> for C
    proof -
      assume \<open>C \<in> N3\<close> and \<open>well_constrained (Rep_ground_eclause C)\<close>
      then have \<open>set_entails_clause (cl_ecl ` wellc_eclauses N2) (cl_ecl (Rep_ground_eclause C))\<close>
        using \<open>N2 \<Turnstile>E N3\<close> unfolding eclause_entails_def by auto
      moreover have \<open>D \<in> Rep_ground_eclause ` N2 \<and> well_constrained D \<Longrightarrow> set_entails_clause (cl_ecl ` wellc_eclauses N1) (cl_ecl D)\<close> for D
        using \<open>N1 \<Turnstile>E N2\<close> unfolding eclause_entails_def by auto
      ultimately show ?thesis
        unfolding eclause_entails_def set_entails_clause_def by force
    qed
    then show \<open>N1 \<Turnstile>E N3\<close> unfolding eclause_entails_def by auto
  qed
qed

definition ground_reflexion_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_reflexion_inferences = {Infer [P] C | P C. \<exists> \<sigma> C'. reflexion (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C' \<and> well_constrained (Rep_ground_eclause P)}\<close>

definition ground_factorization_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_factorization_inferences = {Infer [P] C | P C. \<exists> \<sigma> C'. factorization (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C'  \<and> well_constrained (Rep_ground_eclause P)}\<close>

definition ground_superposition_inferences :: \<open>'a ground_eclause inference set\<close> where
\<open>ground_superposition_inferences = {Infer [P1 , P2] C | P1 P2 C. \<exists> \<sigma> C'. superposition (Rep_ground_eclause P1) (Rep_ground_eclause P2) (Rep_ground_eclause C) \<sigma> Ground C' \<and> well_constrained (Rep_ground_eclause P1) \<and> well_constrained (Rep_ground_eclause P2)}\<close>

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
        where \<iota>_def: \<open>\<iota> = Infer [P] C\<close>
          and \<open>finite (cl_ecl (Rep_ground_eclause P))\<close>
          and \<open>reflexion (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> Ground C'\<close>
          and P_constraint: \<open>well_constrained (Rep_ground_eclause P)\<close>
        using ground_reflexion_inferences_def Rep_ground_eclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_ground_eclause P)) (cl_ecl (Rep_ground_eclause C))\<close>
        using reflexion_is_sound by force
      then show ?thesis
        unfolding eclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def P_constraint by simp
    next
      case b
      then obtain P C \<sigma> k C'
        where \<iota>_def: \<open>\<iota> = Infer [P] C\<close>
          and \<open>finite (cl_ecl (Rep_ground_eclause P))\<close>
          and \<open>factorization (Rep_ground_eclause P) (Rep_ground_eclause C) \<sigma> k C'\<close>
          and P_constraint: \<open>well_constrained (Rep_ground_eclause P)\<close>
        using ground_factorization_inferences_def Rep_ground_eclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_ground_eclause P)) (cl_ecl (Rep_ground_eclause C))\<close>
        using factorization_is_sound by force
      then show ?thesis
        unfolding eclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def P_constraint by simp
    next
      case c
      then obtain P1 P2 C \<sigma> k C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] C\<close>
          and \<open>finite (cl_ecl (Rep_ground_eclause P1))\<close>
          and \<open>finite (cl_ecl (Rep_ground_eclause P2))\<close>
          and \<open>superposition (Rep_ground_eclause P1) (Rep_ground_eclause P2) (Rep_ground_eclause C) \<sigma> k C'\<close>
          and P1_constraint: \<open>well_constrained (Rep_ground_eclause P1)\<close>
          and P2_constraint: \<open>well_constrained (Rep_ground_eclause P2)\<close>
        using ground_superposition_inferences_def Rep_ground_eclause by fastforce
      then have \<open>set_entails_clause {cl_ecl (Rep_ground_eclause P1), cl_ecl (Rep_ground_eclause P2)} (cl_ecl (Rep_ground_eclause C))\<close>
        using superposition_is_sound by force
      moreover have \<open>(cl_ecl ` wellc_eclauses (set (prems_of \<iota>))) = {cl_ecl (Rep_ground_eclause P1), cl_ecl (Rep_ground_eclause P2)}\<close>
        using \<iota>_def P1_constraint P2_constraint by force
      ultimately show ?thesis
        unfolding eclause_entails_def using \<iota>_def by auto
    qed
  qed
qed

definition gecl_ord :: \<open>('a ground_eclause \<times> 'a ground_eclause) set\<close>
  where \<open>gecl_ord \<equiv> {(C,D). (mset_ecl (Rep_ground_eclause C, []), mset_ecl (Rep_ground_eclause D, [])) \<in> mult (mult (trm_ord))}\<close>

lemma gecl_ord_trans: \<open>trans gecl_ord\<close>
  by (metis (no_types, lifting) gecl_ord_def mult_def transI transitive_closure_trans(2) case_prodD case_prodI mem_Collect_eq)

definition gecl_set_ord :: \<open>('a ground_eclause set \<times> 'a ground_eclause set) set\<close>
  where \<open>gecl_set_ord = {(S1, S2). (mset_set S1, mset_set S2) \<in> mult gecl_ord}\<close>

definition Red_Inf_sup :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause inference set\<close> where
\<open>Red_Inf_sup N = {\<iota>. \<iota> \<in> ground_superposition_inference_system
                 \<and> redundant_inference (Rep_ground_eclause (concl_of \<iota>)) (Rep_ground_eclause ` N) (Rep_ground_eclause ` (set (prems_of \<iota>))) [] }\<close>

(* the original definition of redundant_clause does not fit our framework because it also accounts
   for entailment by equal clauses, not just smaller ones. For example, this implies that any
   clause C is redundant in {C}, even ones that are not redundant in {}. *)
definition redundant_clause' :: \<open>'a eclause \<Rightarrow> 'a eclause set  \<Rightarrow> 'a subst \<Rightarrow> 'a clause \<Rightarrow> bool\<close>
  where \<open>redundant_clause' C S \<sigma> C' =
    (\<exists>S'. S' \<subseteq> instances S
          \<and> set_entails_clause (clset_instances S') (cl_ecl C)
          \<and> (\<forall>x \<in> S'. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl C))
          \<and> (\<forall>x \<in> S'. (mset_ecl (fst x, snd x),mset_cl (C',\<sigma>)) \<in> mult (mult trm_ord)))\<close>

definition Red_eclause :: \<open>'a ground_eclause set \<Rightarrow> 'a ground_eclause set\<close> where
\<open>Red_eclause N = {C. \<not> well_constrained (Rep_ground_eclause C)
                     \<or> redundant_clause' (Rep_ground_eclause C) (wellc_eclauses N) [] (cl_ecl (Rep_ground_eclause C))}\<close>

lemma substitution_irrelevance: \<open>mset_ecl (Rep_ground_eclause D, \<sigma>) = mset_ecl (Rep_ground_eclause D, [])\<close>
proof -
  from Rep_ground_eclause have ground: \<open>ground_clause (cl_ecl (Rep_ground_eclause D))\<close> by blast
  then have \<open>L \<in># mset_set (cl_ecl (Rep_ground_eclause D)) \<Longrightarrow> subst_lit L \<sigma> = subst_lit L []\<close> for L
    by (metis substs_preserve_ground_lit elem_mset_set empty_iff mset_set.infinite set_mset_empty)
  then have eq: \<open>L \<in># mset_set (cl_ecl (Rep_ground_eclause D)) \<Longrightarrow> mset_lit (subst_lit L \<sigma>) = mset_lit (subst_lit L [])\<close> for L
    by auto
  have \<open>mset_ecl (Rep_ground_eclause D, \<sigma>) = {# (mset_lit (subst_lit L \<sigma>)). L \<in># (mset_set (cl_ecl (Rep_ground_eclause D))) #}\<close> by auto
  with eq have \<open>mset_ecl (Rep_ground_eclause D, \<sigma>) = {# (mset_lit (subst_lit L [])). L \<in># (mset_set (cl_ecl (Rep_ground_eclause D))) #}\<close>
    using image_mset_cong by force
  then show ?thesis by auto
qed

definition gecl_trms :: \<open>'a ground_eclause \<Rightarrow> 'a trm set\<close>
  where \<open>gecl_trms C = trms_ecl (Rep_ground_eclause C)\<close>

lemma Red_eclause_alt_def: \<open>C \<in> Red_eclause N \<Longrightarrow> (\<exists>N' \<subseteq> N. finite N' \<and> N' \<Turnstile>E {C} \<and> (\<forall>D \<in> N'. (D, C) \<in> gecl_ord))\<close>
proof -
  assume \<open>C \<in> Red_eclause N\<close>
  then consider (a) \<open>\<not> well_constrained (Rep_ground_eclause C)\<close>
              | (b) \<open>redundant_clause' (Rep_ground_eclause C) (wellc_eclauses N) [] (cl_ecl (Rep_ground_eclause C))\<close>
    unfolding Red_eclause_def by auto
  then show ?thesis
  proof cases
    case a
    then have \<open>{} \<subseteq> N \<and> finite {} \<and> {} \<Turnstile>E {C} \<and> (\<forall>D \<in> {}. (D, C) \<in> gecl_ord)\<close>
      unfolding eclause_entails_def by auto
    then show ?thesis by auto
  next
    case b
    then obtain S where i: \<open>S \<subseteq> instances (wellc_eclauses N)\<close>
                    and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_ground_eclause C))\<close>
                    and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_ground_eclause C))\<close>
                    and iv: \<open>\<forall>x \<in> S. (mset_ecl x, mset_cl (cl_ecl (Rep_ground_eclause C), [])) \<in> mult (mult trm_ord)\<close>
    unfolding redundant_clause'_def by auto
    let ?N' = \<open>{C. \<exists>\<sigma>. (Rep_ground_eclause C, \<sigma>) \<in> S}\<close>
    have \<open>?N' \<subseteq> N\<close> using i instances_def
      by (smt Collect_mem_eq Collect_mono_iff Pair_inject Rep_ground_eclause_inject image_iff)
    moreover have \<open>?N' \<Turnstile>E {C}\<close>
    proof -
      have \<open>clset_instances S = cl_ecl ` wellc_eclauses ?N'\<close>
      proof
        show \<open>clset_instances S \<subseteq> cl_ecl ` wellc_eclauses ?N'\<close>
        proof
          fix C
          assume \<open>C \<in> clset_instances S\<close>
          then obtain cl_C \<sigma>_C where member_S: \<open>(cl_C, \<sigma>_C) \<in> S\<close>
                                 and C_def: \<open>C = subst_cl (cl_ecl cl_C) \<sigma>_C\<close>
            unfolding clset_instances_def by auto
          with i have member_N: \<open>cl_C \<in> Rep_ground_eclause ` N\<close> and well_constrained: \<open>well_constrained cl_C\<close>
            unfolding instances_def by auto
          then have \<open>ground_clause (cl_ecl cl_C)\<close> using Rep_ground_eclause by blast
          then have \<open>C = cl_ecl cl_C\<close>
            using C_def substs_preserve_ground_clause [of \<open>cl_ecl cl_C\<close> \<sigma>_C] by blast
          then show \<open>C \<in> cl_ecl ` wellc_eclauses ?N'\<close>
            using member_S member_N well_constrained by blast
        qed
      next
        show \<open>cl_ecl ` wellc_eclauses ?N' \<subseteq> clset_instances S\<close>
        proof
          fix C
          assume \<open>C \<in> cl_ecl ` wellc_eclauses ?N'\<close>
          then obtain cl_C \<sigma>_C where member_S: \<open>(Rep_ground_eclause cl_C, \<sigma>_C) \<in> S\<close> and \<open>C = cl_ecl (Rep_ground_eclause cl_C)\<close> by auto
          then have \<open>C = subst_cl (cl_ecl (Rep_ground_eclause cl_C)) \<sigma>_C\<close>
            using Rep_ground_eclause substs_preserve_ground_clause [of \<open>cl_ecl (Rep_ground_eclause cl_C)\<close> \<sigma>_C] by blast
          with member_S show \<open>C \<in> clset_instances S\<close> unfolding clset_instances_def by auto
        qed
      qed
      then show ?thesis using ii unfolding eclause_entails_def by force
    qed
    moreover have \<open>D \<in> ?N' \<Longrightarrow> (D,C) \<in> gecl_ord\<close> for D
    proof -
      assume \<open>D \<in> ?N'\<close>
      then obtain \<sigma>_D where \<open>(Rep_ground_eclause D, \<sigma>_D) \<in> S\<close> by auto
      then have \<open>(mset_ecl (Rep_ground_eclause D, []), mset_cl (cl_ecl (Rep_ground_eclause C), [])) \<in> mult (mult trm_ord)\<close>
        using iv substitution_irrelevance [of D \<sigma>_D] by auto
      then show ?thesis unfolding gecl_ord_def by auto
    qed
    moreover have \<open>finite ?N'\<close> sorry (* follows from wellfoundedness and totality of gecl_ord on well_constrained ground clauses *)
    ultimately show ?thesis by auto
  qed
qed

lemma Red_Inf_redundant_inference_any_subst:
  assumes \<open>\<iota> \<in> Red_Inf_sup N\<close>
  shows \<open>redundant_inference (Rep_ground_eclause (concl_of \<iota>)) (Rep_ground_eclause ` N) (Rep_ground_eclause ` set (prems_of \<iota>)) \<sigma>\<close>
proof -
  have \<open>redundant_inference (Rep_ground_eclause (concl_of \<iota>)) (Rep_ground_eclause ` N) (Rep_ground_eclause ` set (prems_of \<iota>)) []\<close>
    using assms unfolding Red_Inf_sup_def by auto
  then obtain S where i: \<open>S \<subseteq> instances (Rep_ground_eclause ` N)\<close>
                  and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_ground_eclause (concl_of \<iota>)))\<close>
                  and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_ground_eclause (concl_of \<iota>)))\<close>
                  and iv: \<open>\<forall>x \<in> S. \<exists>D \<in> Rep_ground_eclause ` set (prems_of \<iota>). (x,(D,[])) \<in> ecl_ord\<close>
    unfolding redundant_inference_def by auto
  have iv': \<open>x \<in> S \<Longrightarrow> \<exists>D \<in> Rep_ground_eclause ` set (prems_of \<iota>). (x, (D, \<sigma>)) \<in> ecl_ord\<close> for x
  proof -
    assume \<open>x \<in> S\<close>
    with iv obtain cl_D where \<open>cl_D \<in> set (prems_of \<iota>)\<close> and \<open>(x, (Rep_ground_eclause cl_D, [])) \<in> ecl_ord\<close> by blast
    with substitution_irrelevance [of cl_D \<sigma>] show ?thesis unfolding ecl_ord_def by force
  qed
  from i ii iii iv' show ?thesis unfolding redundant_inference_def by auto
qed

lemma wf_gecl_ord: \<open>wf gecl_ord\<close>
proof -
  have \<open>wf (mult trm_ord)\<close> using trm_ord_wf and wf_mult  by auto
  then have \<open>wf (mult (mult trm_ord))\<close> using wf_mult  by auto
  thus ?thesis 
    using gecl_ord_def and measure_wf [of \<open>(mult (mult trm_ord))\<close> gecl_ord \<open>\<lambda>C. mset_ecl (Rep_ground_eclause C, [])\<close>] by blast
qed

lemma wf_gecl_set_ord: \<open>wf gecl_set_ord\<close>
proof -
  have \<open>wf (mult gecl_ord)\<close>
    using wf_mult wf_gecl_ord by auto
  then show ?thesis
    using gecl_set_ord_def measure_wf [of \<open>mult gecl_ord\<close> gecl_set_ord mset_set] by blast
qed

lemma subset_Red_eclause : \<open>N \<subseteq> N' \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause N'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have instances_subset: \<open>instances (wellc_eclauses N) \<subseteq> instances (wellc_eclauses N')\<close>
    unfolding instances_def by auto
  then have \<open>redundant_clause' C (wellc_eclauses N) \<sigma> C' \<Longrightarrow> redundant_clause' C (wellc_eclauses N') \<sigma> C'\<close> for C C' \<sigma>
    unfolding redundant_clause'_def by auto
  then show \<open>Red_eclause N \<subseteq> Red_eclause N'\<close>
    using Collect_cong Red_eclause_def by auto
qed

lemma subset_Red_Inf_sup : \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have \<open>instances (Rep_ground_eclause ` N) \<subseteq> instances (Rep_ground_eclause ` N')\<close>
    unfolding instances_def by auto
  then have \<open>redundant_inference C (Rep_ground_eclause ` N) P \<sigma> \<Longrightarrow> redundant_inference C (Rep_ground_eclause ` N') P \<sigma>\<close> for \<iota> :: \<open>'a ground_eclause inference\<close> and C P \<sigma>
    using redundant_inference_def by fastforce
  then show ?thesis unfolding Red_Inf_sup_def by blast
qed

lemma Red_eclause_entails: \<open>N \<Turnstile>E Red_eclause N\<close>
proof
  show \<open>\<forall>C\<in>Red_eclause N. N \<Turnstile>E {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain N' where \<open>N' \<subseteq> N\<close> and i: \<open>N' \<Turnstile>E {C}\<close> using Red_eclause_alt_def by metis
    then have ii: \<open>N \<Turnstile>E N'\<close> using subset_entailed by auto
    from i ii show \<open>N \<Turnstile>E {C}\<close> using entails_trans [of N N' \<open>{C}\<close>] by auto
  qed
qed

lemma smaller_gecl_set:
  assumes \<open>finite N\<close>
  assumes \<open>C \<in> N\<close>
  assumes \<open>\<forall>C' \<in> N'. (C', C) \<in> gecl_ord\<close>
  shows \<open>(N - {C} \<union> N', N) \<in> gecl_set_ord\<close>
proof -
  have eq: \<open>mset_set (N - {C}) + {#C#} = mset_set N\<close> using assms(1,2)
    using mset_set.remove by fastforce
  have \<open>\<forall>C'\<in>#mset_set N'. \<exists>D\<in>#{#C#}. (C', D) \<in> gecl_ord\<close> using assms(3)
    by (metis elem_mset_set empty_iff mset_set.infinite set_mset_add_mset_insert set_mset_empty singletonI)
  then have \<open>(mset_set (N - {C}) + mset_set N', mset_set (N - {C}) + {#C#}) \<in> mult gecl_ord\<close>
    using one_step_implies_mult [of \<open>{#C#}\<close> \<open>mset_set N'\<close> gecl_ord \<open>mset_set (N - {C})\<close>] by auto
  with eq have i: \<open>(mset_set (N - {C}) + mset_set N', mset_set N) \<in> mult gecl_ord\<close> by auto
  have \<open>mset_set (N - {C} \<union> N') \<subseteq># mset_set (N - {C}) + mset_set N'\<close>
    by (smt UnE count_mset_set(1) count_mset_set(3) finite_Un leI mset_set.infinite mset_subset_eq_add_right subset_mset.le_add_same_cancel1 subseteq_mset_def zero_order(3))
  then have ii: \<open>mset_set (N - {C} \<union> N') = mset_set (N - {C}) + mset_set N' \<or> (mset_set (N - {C} \<union> N'), mset_set (N - {C}) + mset_set N') \<in> mult gecl_ord\<close>
    using multisets_continued.multiset_order_inclusion_eq gecl_ord_trans by auto
  with i ii have \<open>(mset_set (N - {C} \<union> N'), mset_set N) \<in> mult gecl_ord\<close>
    by (metis mult_def transitive_closure_trans(2))
  then show ?thesis unfolding gecl_set_ord_def by auto
qed

lemma minimal_redundancy_subset:
  assumes \<open>C \<in> Red_eclause N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> C \<in> Red_eclause M \<and> (\<forall>D \<in> M. D \<notin> Red_eclause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>E {C} \<and> (\<forall>D \<in> NC1. (D, C) \<in> gecl_ord)\<close> (is \<open>?P NC1\<close>)
    using Red_eclause_alt_def by metis
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> gecl_set_ord ==> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>gecl_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] wf_gecl_set_ord by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_eclause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_eclause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>E {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. (E,D) \<in> gecl_ord\<close>
      using Red_eclause_alt_def by metis
    (* construct a smaller set than NC0 in which C is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> gecl_set_ord\<close>
      using smaller_gecl_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>E {C}\<close>
    proof -
      have \<open>?NCC \<Turnstile>E NC0 - {D} \<union> {D}\<close> using all_formulas_entailed ND1_entails
        by (meson entail_union entails_trans inf_sup_ord(3) inf_sup_ord(4) subset_entailed)
      also have \<open>NC0 - {D} \<union> {D} \<Turnstile>E NC0\<close> using subset_entailed [of NC0 \<open>NC0 - {D} \<union> {D}\<close>] by blast
      also have \<open>NC0 \<Turnstile>E {C}\<close> using NC0_prop Red_eclause_entails entail_set_all_formulas by blast
      finally show ?thesis by auto
    qed
    moreover have \<open>\<forall>E \<in> ?NCC. (E,C) \<in> gecl_ord\<close>
    proof
      fix E
      assume \<open>E \<in> ?NCC\<close>
      then consider (a) \<open>E \<in> NC0\<close> | (b) \<open>E \<in> ND1\<close> by blast
      then show \<open>(E,C) \<in> gecl_ord\<close>
      proof cases
        case a
        then show ?thesis using NC0_prop by auto
      next
        case b
        then have \<open>(E,D) \<in> gecl_ord\<close> using ND1_ord by auto
        also have \<open>(D,C) \<in> gecl_ord\<close> using \<open>D \<in> NC0\<close> NC0_prop by auto
        finally show ?thesis using gecl_ord_trans by auto
      qed
    qed
    ultimately show False using NC0_min by blast
  qed
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> C \<in> Red_eclause NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_eclause N)\<close>
    unfolding Red_eclause_def sorry
  then show ?thesis by auto
qed

lemma Red_eclause_entailed: \<open>N - Red_eclause N \<Turnstile>E Red_eclause N\<close>
proof
  show \<open>\<forall>C \<in> Red_eclause N. N - Red_eclause N \<Turnstile>E {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain M where M_subset: \<open>M \<subseteq> N\<close>
                    and M_Red: \<open>C \<in> Red_eclause M\<close>
                    and M_min: \<open>\<forall>D \<in> M. D \<notin> Red_eclause N\<close>
      using minimal_redundancy_subset by metis
    with M_subset have \<open>M \<subseteq> N - Red_eclause N\<close> by auto
    then have \<open>N - Red_eclause N \<Turnstile>E M\<close> using subset_entailed by auto
    also have \<open>M \<Turnstile>E Red_eclause M\<close> using Red_eclause_entails by auto
    also have \<open>Red_eclause M \<Turnstile>E {C}\<close> using M_Red subset_entailed by auto
    finally show \<open>N - Red_eclause N \<Turnstile>E {C}\<close> by auto
  qed
qed

lemma exists_premise_greater:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<exists>D \<in> Rep_ground_eclause ` set (prems_of \<iota>). ((Rep_ground_eclause (concl_of \<iota>), []), (D , [])) \<in> ecl_ord\<close>
  sorry

lemma Red_Inf_concl_of:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<iota> \<in> Red_Inf_sup {concl_of \<iota>}\<close>
proof -
  (* preliminaries *)
  have subst_irrelevant: \<open>subst_cl (cl_ecl (Rep_ground_eclause (concl_of \<iota>))) [] = cl_ecl (Rep_ground_eclause (concl_of \<iota>))\<close>
    using Rep_ground_eclause [of \<open>concl_of \<iota>\<close>]
      and substs_preserve_ground_clause [of \<open>cl_ecl (Rep_ground_eclause (concl_of \<iota>))\<close> \<open>[]\<close>] by auto
  (* proof of redundancy *)
  let ?S = \<open>{(Rep_ground_eclause (concl_of \<iota>), [])}\<close>
  have \<open>?S \<subseteq> instances {Rep_ground_eclause (concl_of \<iota>)}\<close>
    unfolding instances_def
    using subst_irrelevant
    and Rep_ground_eclause [of \<open>concl_of \<iota>\<close>] by auto
  moreover have \<open>set_entails_clause (clset_instances ?S) (cl_ecl (Rep_ground_eclause (concl_of \<iota>)))\<close>
    unfolding clset_instances_def set_entails_clause_def
    using subst_irrelevant by auto
  moreover have \<open>\<forall>x \<in> ?S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_ground_eclause (concl_of \<iota>)))\<close>
  proof -
    have \<open>subst_set (trms_ecl (Rep_ground_eclause (concl_of \<iota>))) [] = trms_ecl (Rep_ground_eclause (concl_of \<iota>))\<close> by auto
    then show ?thesis using subterms_inclusion_refl by auto
  qed
  moreover have \<open>\<forall>x \<in> ?S. \<exists>D \<in> Rep_ground_eclause ` set (prems_of \<iota>). ((fst x, snd x), (D , [])) \<in> ecl_ord\<close>
    using exists_premise_greater assms by force
  ultimately have \<open>redundant_inference (Rep_ground_eclause (concl_of \<iota>)) {Rep_ground_eclause (concl_of \<iota>)} (Rep_ground_eclause ` set (prems_of \<iota>)) []\<close>
    unfolding redundant_inference_def by blast
  then show ?thesis using assms unfolding Red_Inf_sup_def by auto
qed

interpretation calculus empty_eclauses \<open>(\<Turnstile>E)\<close> ground_superposition_inference_system \<open>(\<Turnstile>E)\<close> Red_Inf_sup Red_eclause
proof
  show \<open>Red_Inf_sup N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_Inf_sup_def by auto
next
  show \<open>B \<in> empty_eclauses \<Longrightarrow> N \<Turnstile>E {B} \<Longrightarrow> N - Red_eclause N \<Turnstile>E {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> empty_eclauses\<close> and \<open>N \<Turnstile>E {B}\<close>
    then have N_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not>validate_clause_set I (cl_ecl ` wellc_eclauses N)\<close> for I
      unfolding eclause_entails_def set_entails_clause_def by auto
    assume \<open>\<not> N - Red_eclause N \<Turnstile>E {B}\<close>
    with N_unsat obtain I where fo_I: \<open>fo_interpretation I\<close>
                          and I_model: \<open>validate_clause_set I (cl_ecl ` wellc_eclauses (N - Red_eclause N))\<close>
                          and \<open>\<not>validate_clause_set I (cl_ecl ` wellc_eclauses N)\<close>
      unfolding eclause_entails_def set_entails_clause_def by blast
    then obtain C where \<open>C \<in> wellc_eclauses N\<close>
                    and \<open>C \<notin> wellc_eclauses (N - Red_eclause N)\<close>
                    and C_novalid: \<open>\<not> validate_clause I (cl_ecl C)\<close>
      by (smt image_iff validate_clause_set.simps)
    then have \<open>C \<in> wellc_eclauses (Red_eclause N)\<close> by blast
    then obtain cl_C where \<open>C = Rep_ground_eclause cl_C\<close>
                       and \<open>well_constrained C\<close>
                       and \<open>cl_C \<in> Red_eclause N\<close> by auto
    with Red_eclause_entailed fo_I I_model have \<open>validate_clause I (cl_ecl C)\<close>
      unfolding eclause_entails_def set_entails_clause_def by blast
    with C_novalid show False by blast
  qed
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause N'\<close> for N N' using subset_Red_eclause by auto
next
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close> for N N' using subset_Red_Inf_sup by auto
next
  show \<open>N' \<subseteq> Red_eclause N \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause (N - N')\<close> for N' N
  proof
    fix C
    assume N'_subset: \<open>N' \<subseteq> Red_eclause N\<close> and \<open>C \<in> Red_eclause N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>C \<in> Red_eclause M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_eclause N)\<close>
      using minimal_redundancy_subset by metis
    then have \<open>C \<in> Red_eclause M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>C \<in> Red_eclause (N - N')\<close> using subset_Red_eclause by auto
  qed
next
  show \<open>N' \<subseteq> Red_eclause N \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup (N - N')\<close> for N' N
  proof
    fix \<iota>
    assume \<open>N' \<subseteq> Red_eclause N\<close> and \<open>\<iota> \<in> Red_Inf_sup N\<close>
    show \<open>\<iota> \<in> Red_Inf_sup (N - N')\<close> sorry
  qed
next
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_sup N\<close> for \<iota> N
    using Red_Inf_concl_of [of \<iota>] subset_Red_Inf_sup [of \<open>{concl_of \<iota>}\<close> N] by auto
qed

lemma derivable_factorization:
  assumes \<open>P \<in> wellc_eclauses N\<close>
      and \<open>factorization P C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_factorization_inferences. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P and C are ground_eclauses *)
  have \<open>finite (cl_ecl C)\<close>
    using factorization_preserves_finiteness assms(1,2) Rep_ground_eclause by blast
  then have inv_C: \<open>Rep_ground_eclause (Abs_ground_eclause C) = C\<close>
    using Abs_ground_eclause_inverse assms(3) by auto
  have inv_P: \<open>Rep_ground_eclause (Abs_ground_eclause P) = P\<close>
    using Abs_ground_eclause_inverse Rep_ground_eclause assms(1) by auto
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_ground_eclause P] (Abs_ground_eclause C)\<close>
  have \<open>?\<iota> \<in> ground_factorization_inferences\<close>
    unfolding ground_factorization_inferences_def using inv_C inv_P assms(1,2) by auto
  moreover have \<open>Rep_ground_eclause (concl_of ?\<iota>) = C\<close> using inv_C by auto
  moreover have \<open>Rep_ground_eclause ` set (prems_of ?\<iota>) = {P}\<close> using inv_P by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_ground_eclause P} \<subseteq> N\<close> using assms(1)
      by (metis (mono_tags, lifting) Rep_ground_eclause_inverse image_iff mem_Collect_eq singletonD subsetI)
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed

lemma derivable_reflexion:
  assumes \<open>P \<in> wellc_eclauses N\<close>
      and \<open>reflexion P C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_reflexion_inferences. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P and C are ground_eclauses *)
  have \<open>finite (cl_ecl C)\<close>
    using reflexion_preserves_finiteness assms(1,2) Rep_ground_eclause by blast
  then have inv_C: \<open>Rep_ground_eclause (Abs_ground_eclause C) = C\<close>
    using Abs_ground_eclause_inverse assms(3) by auto
  have inv_P: \<open>Rep_ground_eclause (Abs_ground_eclause P) = P\<close>
    using Abs_ground_eclause_inverse Rep_ground_eclause assms(1) by auto
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_ground_eclause P] (Abs_ground_eclause C)\<close>
  have \<open>?\<iota> \<in> ground_reflexion_inferences\<close>
    unfolding ground_reflexion_inferences_def using inv_C inv_P assms(1,2) by auto
  moreover have \<open>Rep_ground_eclause (concl_of ?\<iota>) = C\<close> using inv_C by auto
  moreover have \<open>Rep_ground_eclause ` set (prems_of ?\<iota>) = {P}\<close> using inv_P by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_ground_eclause P} \<subseteq> N\<close> using assms(1)
      by (metis (mono_tags, lifting) Rep_ground_eclause_inverse image_iff mem_Collect_eq singletonD subsetI)
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed

lemma derivable_superposition:
  assumes \<open>P1 \<in> wellc_eclauses N\<close>
      and \<open>P2 \<in> wellc_eclauses N\<close>
      and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_superposition_inferences. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = {P1, P2} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P1, P2 and C are ground_eclauses *)
  have \<open>finite (cl_ecl C)\<close>
    using superposition_preserves_finiteness assms(1,2,3) Rep_ground_eclause by blast
  then have inv_C: \<open>Rep_ground_eclause (Abs_ground_eclause C) = C\<close>
    using Abs_ground_eclause_inverse assms(4) by auto
  have inv_P1: \<open>Rep_ground_eclause (Abs_ground_eclause P1) = P1\<close>
    using Abs_ground_eclause_inverse Rep_ground_eclause assms(1) by auto
  have inv_P2: \<open>Rep_ground_eclause (Abs_ground_eclause P2) = P2\<close>
    using Abs_ground_eclause_inverse Rep_ground_eclause assms(2) by auto
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_ground_eclause P1, Abs_ground_eclause P2] (Abs_ground_eclause C)\<close>
  have \<open>?\<iota> \<in> ground_superposition_inferences\<close>
    unfolding ground_superposition_inferences_def using inv_C inv_P1 inv_P2 assms(1,2,3) by auto
  moreover have \<open>Rep_ground_eclause (concl_of ?\<iota>) = C\<close> using inv_C by auto
  moreover have \<open>Rep_ground_eclause ` set (prems_of ?\<iota>) = {P1, P2}\<close> using inv_P1 inv_P2 by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_ground_eclause P1, Abs_ground_eclause P2} \<subseteq> N\<close> using assms(1,2)
      by (smt Rep_ground_eclause_inverse image_iff insert_iff mem_Collect_eq singletonD subsetI)
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed

lemma derivable_ground_eclause:
  assumes \<open>derivable C P (wellc_eclauses N) \<sigma> Ground C'\<close>
  assumes \<open>ground_clause (cl_ecl C)\<close>
  shows \<open>\<exists> \<iota> \<in> Inf_from N. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = P\<close>
proof -
  from assms(1) consider
      (a) \<open>\<exists>P1 P2. P1 \<in> (wellc_eclauses N) \<and> P2 \<in> (wellc_eclauses N) \<and> P = {P1, P2} \<and> superposition P1 P2 C \<sigma> Ground C'\<close>
    | (b) \<open>\<exists>P1. P1 \<in> (wellc_eclauses N) \<and> P = {P1} \<and> factorization P1 C \<sigma> Ground C'\<close>
    | (c) \<open>\<exists>P1. P1 \<in> (wellc_eclauses N) \<and> P = {P1} \<and> reflexion P1 C \<sigma> Ground C'\<close>
    unfolding derivable_def by blast
  then show \<open>\<exists> \<iota> \<in> Inf_from N. Rep_ground_eclause (concl_of \<iota>) = C \<and> Rep_ground_eclause ` set (prems_of \<iota>) = P\<close>
  proof cases
    case a
    then obtain P1 P2 where \<open>P1 \<in> (wellc_eclauses N)\<close>
                        and \<open>P2 \<in> (wellc_eclauses N)\<close>
                        and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
                        and \<open>P = {P1, P2}\<close>
      by auto
    then show ?thesis using derivable_superposition assms(2) unfolding Inf_from_def by blast
  next
    case b
    then obtain P1 where \<open>P1 \<in> (wellc_eclauses N)\<close>
                     and \<open>factorization P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_factorization assms(2) unfolding Inf_from_def by blast
  next
    case c
    then obtain P1 where \<open>P1 \<in> (wellc_eclauses N)\<close>
                     and \<open>reflexion P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_reflexion assms(2) unfolding Inf_from_def by blast
  qed
qed

lemma saturation_ground_eclauses:
  assumes \<open>saturated N\<close>
  shows \<open>ground_inference_saturated (wellc_eclauses N)\<close>
proof -
  have \<open>derivable C P (wellc_eclauses N) \<sigma> Ground C' \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> redundant_inference C (wellc_eclauses N) P \<sigma>\<close> for C P \<sigma> C'
  proof -
    assume \<open>derivable C P (wellc_eclauses N) \<sigma> Ground C'\<close> and \<open>ground_clause (cl_ecl C)\<close>
    then obtain \<iota> where \<open>\<iota> \<in> Red_Inf_sup N\<close>
                    and eq1: \<open>Rep_ground_eclause (concl_of \<iota>) = C\<close>
                    and eq2: \<open>Rep_ground_eclause ` (set (prems_of \<iota>)) = P\<close>
      using assms(1) saturated_def derivable_ground_eclause by blast
    then have \<open>\<iota> \<in> Red_Inf_sup (N - Red_eclause N)\<close>
      using Red_Inf_without_redundant_clauses by auto
    moreover have \<open>N - Red_eclause N \<subseteq> {C \<in> N. well_constrained (Rep_ground_eclause C)}\<close>
      unfolding Red_eclause_def by blast
    ultimately have \<open>\<iota> \<in> Red_Inf_sup {C \<in> N. well_constrained (Rep_ground_eclause C)}\<close>
      using Red_Inf_of_subset by blast
    then have \<open>redundant_inference C (Rep_ground_eclause ` {C \<in> N. well_constrained (Rep_ground_eclause C)}) P \<sigma>\<close>
      using Red_Inf_redundant_inference_any_subst eq1 eq2 by blast
    moreover have \<open>(Rep_ground_eclause ` {C \<in> N. well_constrained (Rep_ground_eclause C)}) = wellc_eclauses N\<close> by blast
    ultimately show \<open>redundant_inference C (wellc_eclauses N) P \<sigma>\<close> by auto
  qed
  then show ?thesis
    unfolding ground_inference_saturated_def by auto
qed

definition canonical_interp :: \<open>'a ground_eclause set \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool\<close>
  where \<open>canonical_interp N = same_values (\<lambda>x. (trm_rep x (wellc_eclauses N)))\<close>

lemma canonical_interp_fo: \<open>fo_interpretation (canonical_interp N)\<close>
  unfolding canonical_interp_def using trm_rep_compatible_with_structure same_values_fo_int by metis

lemma subst_ecl_ground_clause:
  assumes \<open>ground_clause (cl_ecl C)\<close>
  assumes \<open>well_constrained C\<close>
  shows \<open>subst_ecl C \<sigma> = C\<close>
proof -
  from assms(1) have \<open>subst_cl (cl_ecl C) \<sigma> = cl_ecl C\<close>
    using substs_preserve_ground_clause by blast
  moreover have \<open>{t \<lhd> \<sigma> |t. t \<in> trms_ecl C} = trms_ecl C\<close>
  proof -
    have \<open>t \<in> trms_ecl C \<Longrightarrow> subst t \<sigma> = t\<close> for t
    proof -
      assume \<open>t \<in> trms_ecl C\<close>
      with assms(2) have \<open>dom_trm t (cl_ecl C)\<close> unfolding well_constrained_def by auto
      then have \<open>vars_of t \<subseteq> vars_of_cl (cl_ecl C)\<close> using dom_trm_vars by auto
      then have \<open>vars_of t = {}\<close> using assms(1) by auto
      then show \<open>subst t \<sigma> = t\<close>
        by (simp add: ground_term_def substs_preserve_ground_terms)
    qed
    then show ?thesis by force
  qed
  ultimately show ?thesis
    by (smt Collect_cong cl_ecl.simps subst_ecl.simps trms_ecl.elims)
qed

lemma closed_under_renaming_ground_eclauses:
  shows \<open>closed_under_renaming (wellc_eclauses N)\<close>
proof -
  have \<open>C \<in> (wellc_eclauses N) \<Longrightarrow> renaming_cl C D \<Longrightarrow> D \<in> (wellc_eclauses N)\<close> for C D
  proof -
    assume C_elem: \<open>C \<in> (wellc_eclauses N)\<close> and \<open>renaming_cl C D\<close>
    then obtain \<eta> where \<open>D = subst_ecl C \<eta>\<close> and \<open>well_constrained C\<close> and \<open>ground_clause (cl_ecl C)\<close>
      using Rep_ground_eclause
      unfolding renaming_cl_def by blast
    then have \<open>C = D\<close> using subst_ecl_ground_clause by auto
    with C_elem show \<open>D \<in> (wellc_eclauses N)\<close> by auto
  qed
  then show ?thesis unfolding closed_under_renaming_def by blast
qed

lemma canonical_interp_model:
  assumes \<open>saturated N\<close>
  assumes \<open>\<forall>C \<in> N. C \<notin> empty_eclauses\<close>
  assumes \<open>C \<in> wellc_eclauses N\<close>
  assumes \<open>ground_clause (subst_cl (cl_ecl C) \<sigma>)\<close>
  assumes \<open>all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. (trm_rep t (Rep_ground_eclause ` N)))\<close>
  shows \<open>validate_ground_clause (canonical_interp N) (subst_cl (cl_ecl C) \<sigma>)\<close>
proof -
  let ?S = \<open>wellc_eclauses N\<close>
  have \<open>ground_inference_saturated ?S\<close> using assms(1) saturation_ground_eclauses by auto
  moreover from assms(2) have \<open>\<forall>x \<in> ?S. (cl_ecl x) \<noteq> {}\<close> by auto
  moreover have \<open>\<forall>x \<in> ?S. finite (cl_ecl x)\<close> using Rep_ground_eclause by blast
  moreover have \<open>all_trms_irreducible (subst_set (trms_ecl C) \<sigma>) (\<lambda>t. (trm_rep t ?S))\<close> sorry
  moreover have \<open>\<forall>x \<in> ?S. well_constrained x\<close> by auto
  moreover have \<open>closed_under_renaming ?S\<close> using closed_under_renaming_ground_eclauses by auto
  ultimately show \<open>validate_ground_clause (canonical_interp N) (subst_cl (cl_ecl C) \<sigma>)\<close>
    unfolding canonical_interp_def
    using assms(4) int_clset_is_a_model [of ?S \<open>(C, \<sigma>)\<close>]
    by (metis (no_types, lifting) assms(3) fst_eqD snd_eqD)
qed

interpretation static_refutational_complete_calculus empty_eclauses \<open>(\<Turnstile>E)\<close> ground_superposition_inference_system \<open>(\<Turnstile>E)\<close> Red_Inf_sup Red_eclause
proof
  have \<open>saturated N \<Longrightarrow> \<forall>C \<in> N. C \<notin> empty_eclauses \<Longrightarrow> B \<in> empty_eclauses \<Longrightarrow> \<not> N \<Turnstile>E {B}\<close> for B N
  proof -
    assume \<open>saturated N\<close> and \<open>\<forall>C \<in> N. C \<notin> empty_eclauses\<close>
    then have saturated: \<open>saturated (N - Red_eclause N)\<close> and no_empty_cl: \<open>\<forall>C \<in> N - Red_eclause N. C \<notin> empty_eclauses\<close>
      using saturated_without_redundant_clauses by auto
    show \<open>B \<in> empty_eclauses \<Longrightarrow> \<not> N \<Turnstile>E {B}\<close>
    proof
      let ?N' = \<open>wellc_eclauses (N - Red_eclause N)\<close>
      assume \<open>B \<in> empty_eclauses\<close> and \<open>N \<Turnstile>E {B}\<close>
      then have N'_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not> validate_clause_set I (cl_ecl ` ?N')\<close> for I
        using Red_F_Bot unfolding eclause_entails_def set_entails_clause_def by auto
      (* model for N - Red_eclause N *)
      have \<open>validate_clause_set (canonical_interp (N - Red_eclause N)) (cl_ecl ` ?N')\<close>
      proof -
        have \<open>cl_C \<in> cl_ecl ` ?N' \<Longrightarrow> ground_clause (subst_cl cl_C \<sigma>_C) \<Longrightarrow> validate_ground_clause (canonical_interp (N - Red_eclause N)) (subst_cl cl_C \<sigma>_C)\<close> for cl_C \<sigma>_C
        proof -
          assume \<open>cl_C \<in> cl_ecl ` ?N'\<close> and \<open>ground_clause (subst_cl cl_C \<sigma>_C)\<close>
          then obtain C where \<open>C \<in> ?N'\<close> and \<open>cl_C = cl_ecl C\<close> and \<open>ground_clause (subst_cl cl_C \<sigma>_C)\<close> by auto
          moreover have \<open>all_trms_irreducible (subst_set (trms_ecl C) \<sigma>_C) (\<lambda>t. trm_rep t (Rep_ground_eclause ` (N - Red_eclause N)))\<close> sorry (* might come from non-redundance*)
          ultimately show \<open>validate_ground_clause (canonical_interp (N - Red_eclause N)) (subst_cl cl_C \<sigma>_C)\<close>
            using canonical_interp_model [of \<open>N - Red_eclause N\<close> C \<sigma>_C] saturated no_empty_cl by blast
        qed
        then show ?thesis by auto
      qed
      with canonical_interp_fo and N'_unsat show False by blast
    qed
  qed
  then show \<open>saturated N \<Longrightarrow> B \<in> empty_eclauses \<Longrightarrow> N \<Turnstile>E {B} \<Longrightarrow> \<exists>B'\<in>empty_eclauses. B' \<in> N\<close> for B N by blast
qed

end
end