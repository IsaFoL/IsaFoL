theory Superposition_Lifting
  imports Nonground_Calculus_Lifting SuperCalc.superposition
begin

(* Ideally, this type would contain only well_constrained clauses, but this is not possible since
   the definition of well_constrained depends on the term ordering, which is not instantiated yet *)
typedef 'a gclause = \<open>{C :: 'a eclause. finite (cl_ecl C)
                                               \<and> ground_clause (cl_ecl C)
                                               \<and> trms_ecl C = {}}\<close>
apply(rule_tac x = \<open>Ecl {} {}\<close> in exI)
  by simp

context basic_superposition
begin

definition gclause_entails :: \<open>'a gclause set \<Rightarrow> 'a gclause set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50)
  where
\<open>N1 \<Turnstile>G N2 \<equiv> \<forall>C2 \<in> N2. set_entails_clause (cl_ecl ` Rep_gclause ` N1) (cl_ecl (Rep_gclause C2))\<close>

definition equiv_gclause :: \<open>'a gclause \<Rightarrow> 'a gclause \<Rightarrow> bool\<close> (infix "\<approx>G" 60)
  where
\<open>C1 \<approx>G C2 \<equiv> mset_cl (cl_ecl (Rep_gclause C1), []) = mset_cl (cl_ecl (Rep_gclause C2), [])\<close>

lemma equiv_gclause_symmetric [symmetric] :
  \<open>C \<approx>G D = D \<approx>G C\<close> unfolding equiv_gclause_def by auto

lemma equiv_gclause_trans [trans] :
  \<open>C \<approx>G D \<Longrightarrow> D \<approx>G E \<Longrightarrow> C \<approx>G E\<close> unfolding equiv_gclause_def by auto

lemma equiv_lit_validate:
  \<open>fo_interpretation I \<Longrightarrow> mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 = validate_ground_lit I L2\<close>
proof -
  assume fo: \<open>fo_interpretation I\<close>
  have main: \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 \<Longrightarrow> validate_ground_lit I L2\<close> for L1 L2
  proof (cases L1; cases L2)
    show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 \<Longrightarrow> L1 = Pos e1 \<Longrightarrow> L2 = Pos e2 \<Longrightarrow> validate_ground_lit I L2\<close> for e1 e2
    proof (cases e1, cases e2, auto)
      fix x1 x2 x1' x2' :: \<open>'a trm\<close>
      assume \<open>{#x1, x2#} = {#x1', x2'#}\<close>
      then consider \<open>(x1 = x1' \<and> x2 = x2')\<close> | \<open>(x1 = x2' \<and> x2 = x1')\<close>
        by (metis (no_types, lifting) add_eq_conv_ex add_mset_eq_single)
      moreover have \<open>symmetric I\<close> using fo unfolding fo_interpretation_def congruence_def equivalence_relation_def by auto
      ultimately show \<open>I x1 x2 \<Longrightarrow> I x1' x2'\<close> unfolding symmetric_def by auto
    qed
  next
    show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 \<Longrightarrow> L1 = Pos e1 \<Longrightarrow> L2 = Neg e2 \<Longrightarrow> validate_ground_lit I L2\<close> for e1 e2
    proof (cases e1, cases e2, simp add: add_eq_conv_ex) qed
  next
    show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 \<Longrightarrow> L1 = Neg e1 \<Longrightarrow> L2 = Pos e2 \<Longrightarrow> validate_ground_lit I L2\<close> for e1 e2
    proof (cases e1, cases e2, simp add: add_eq_conv_ex) qed
  next
    show \<open>mset_lit L1 = mset_lit L2 \<Longrightarrow> validate_ground_lit I L1 \<Longrightarrow> L1 = Neg e1 \<Longrightarrow> L2 = Neg e2 \<Longrightarrow> validate_ground_lit I L2\<close> for e1 e2
    proof (cases e1, cases e2, auto)
      fix x1 x2 x1' x2' :: \<open>'a trm\<close>
      assume \<open>{#x1, x1, x2, x2#} = {#x1', x1', x2', x2'#}\<close>
      then consider \<open>(x1 = x1' \<and> x2 = x2')\<close> | \<open>(x1 = x2' \<and> x2 = x1')\<close>
      proof (cases \<open>x1 = x2\<close>; cases \<open>x1' = x2'\<close>; metis insert_iff multi_drop_mem_not_eq set_mset_add_mset_insert zero_diff) qed
      moreover have \<open>symmetric I\<close> using fo unfolding fo_interpretation_def congruence_def equivalence_relation_def by auto
      ultimately show \<open>\<not> I x1 x2 \<Longrightarrow> I x1' x2' \<Longrightarrow> False\<close> unfolding symmetric_def by auto
    qed
  qed
  assume \<open>mset_lit L1 = mset_lit L2\<close>
  with main show ?thesis by metis
qed

lemma equiv_gclause_validate:
\<open>fo_interpretation I \<Longrightarrow> C \<approx>G D \<Longrightarrow> validate_clause I (cl_ecl (Rep_gclause C)) = validate_clause I (cl_ecl (Rep_gclause D))\<close>
proof -
  assume fo: \<open>fo_interpretation I\<close>
  have main: \<open>C \<approx>G D \<Longrightarrow> validate_clause I (cl_ecl (Rep_gclause C)) \<Longrightarrow> validate_clause I (cl_ecl (Rep_gclause D))\<close> for C D
  proof -
    assume equiv: \<open>C \<approx>G D\<close> and \<open>validate_clause I (cl_ecl (Rep_gclause C))\<close>
    then obtain L where validate: \<open>L \<in> cl_ecl (Rep_gclause C) \<and> validate_ground_lit I L\<close>
      using substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause C)\<close> \<open>[]\<close>] Rep_gclause [of C] by fastforce
    then have \<open>mset_lit L \<in># mset_cl (cl_ecl (Rep_gclause C), [])\<close>
      using Rep_gclause [of C] substs_preserve_ground_lit [of \<open>cl_ecl (Rep_gclause C)\<close> L \<open>[]\<close>] by force
    with equiv have \<open>mset_lit L \<in># mset_cl (cl_ecl (Rep_gclause D), [])\<close>
      unfolding equiv_gclause_def by auto
    then obtain L' where \<open>L' \<in># mset_set (cl_ecl (Rep_gclause D))\<close>
                     and mset_lit_eq: \<open>mset_lit (subst_lit L' []) = mset_lit L\<close> by auto
    then have L'_elem: \<open>L' \<in> cl_ecl (Rep_gclause D)\<close> by (meson count_mset_set(3) not_in_iff)
    with mset_lit_eq have \<open>mset_lit L' = mset_lit L\<close>
      using Rep_gclause [of D] substs_preserve_ground_lit [of \<open>cl_ecl (Rep_gclause D)\<close> L' \<open>[]\<close>] by auto
    with validate and fo have \<open>validate_ground_lit I L'\<close>
      using equiv_lit_validate by blast
    then have \<open>\<exists>L' \<in> cl_ecl (Rep_gclause D). validate_ground_lit I L'\<close> using L'_elem by auto
    then show ?thesis
      using substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause D)\<close>] Rep_gclause [of D] by auto
  qed
  assume \<open>C \<approx>G D\<close>
  with main show ?thesis using equiv_gclause_symmetric [of C D] by blast
qed

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

fun remove_trms :: \<open>'a eclause \<Rightarrow> 'a gclause\<close>
  where \<open>remove_trms C = Abs_gclause (Ecl (cl_ecl C) {})\<close>

lemma remove_trms_cl_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> cl_ecl (Rep_gclause (remove_trms C)) = cl_ecl C\<close>
  using Abs_gclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

lemma remove_trms_trms_ecl:
  \<open>finite (cl_ecl C) \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> trms_ecl (Rep_gclause (remove_trms C)) = {}\<close>
  using Abs_gclause_inverse [of \<open>Ecl (cl_ecl C) {}\<close>] by auto

definition ground_reflexion_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_reflexion_inferences = {Infer [P] (remove_trms C) | P C. \<exists> \<sigma> C'. reflexion (Rep_gclause P) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

definition ground_factorization_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_factorization_inferences = {Infer [P] (remove_trms C) | P C. \<exists> \<sigma> C'. factorization (Rep_gclause P) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

definition ground_superposition_inferences :: \<open>'a gclause inference set\<close> where
\<open>ground_superposition_inferences = {Infer [P1 , P2] (remove_trms C) | P1 P2 C. \<exists> \<sigma> C'. superposition (Rep_gclause P1) (Rep_gclause P2) C \<sigma> Ground C' \<and> ground_clause (cl_ecl C)}\<close>

abbreviation ground_superposition_inference_system :: \<open>'a gclause inference set\<close>
  where
\<open>ground_superposition_inference_system \<equiv> ground_reflexion_inferences
                                       \<union> ground_factorization_inferences
                                       \<union> ground_superposition_inferences\<close>

interpretation sound_inference_system \<open>empty_gclauses\<close> \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system
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
        where \<iota>_def: \<open>\<iota> = Infer [P] (remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_gclause P))\<close>
          and reflexion: \<open>reflexion (Rep_gclause P) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_reflexion_inferences_def Rep_gclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_gclause P)) (cl_ecl C)\<close>
        using reflexion_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (remove_trms C)) = cl_ecl C\<close>
        using remove_trms_cl_ecl ground_C reflexion_preserves_finiteness finite_P reflexion by blast
      ultimately show ?thesis
        unfolding gclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case b
      then obtain P C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P] (remove_trms C)\<close>
          and finite_P: \<open>finite (cl_ecl (Rep_gclause P))\<close>
          and factorization: \<open>factorization (Rep_gclause P) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_factorization_inferences_def Rep_gclause by fastforce
      then have \<open>clause_entails_clause (cl_ecl (Rep_gclause P)) (cl_ecl C)\<close>
        using factorization_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (remove_trms C)) = cl_ecl C\<close>
        using remove_trms_cl_ecl ground_C factorization_preserves_finiteness finite_P factorization by blast
      ultimately show ?thesis
        unfolding gclause_entails_def clause_entails_clause_def set_entails_clause_def using \<iota>_def by auto
    next
      case c
      then obtain P1 P2 C \<sigma> C'
        where \<iota>_def: \<open>\<iota> = Infer [P1, P2] (remove_trms C)\<close>
          and finite_P1: \<open>finite (cl_ecl (Rep_gclause P1))\<close>
          and finite_P2: \<open>finite (cl_ecl (Rep_gclause P2))\<close>
          and superposition: \<open>superposition (Rep_gclause P1) (Rep_gclause P2) C \<sigma> Ground C'\<close>
          and ground_C: \<open>ground_clause (cl_ecl C)\<close>
        using ground_superposition_inferences_def Rep_gclause by fastforce
      then have \<open>set_entails_clause {cl_ecl (Rep_gclause P1), cl_ecl (Rep_gclause P2)} (cl_ecl C)\<close>
        using superposition_is_sound by force
      moreover have \<open>cl_ecl (Rep_gclause (remove_trms C)) = cl_ecl C\<close>
        using remove_trms_cl_ecl ground_C superposition_preserves_finiteness finite_P1 finite_P2 superposition by blast
      ultimately show ?thesis
        unfolding gclause_entails_def using \<iota>_def by auto
    qed
  qed
qed

definition gclause_ord :: \<open>('a gclause \<times> 'a gclause) set\<close>
  where \<open>gclause_ord \<equiv> {(C,D). (mset_ecl (Rep_gclause C, []), mset_ecl (Rep_gclause D, [])) \<in> mult (mult (trm_ord))}\<close>

lemma gclause_ord_trans: \<open>trans gclause_ord\<close>
  by (metis (no_types, lifting) gclause_ord_def mult_def transI transitive_closure_trans(2) case_prodD case_prodI mem_Collect_eq)

lemma gclause_ord_total:
  \<open>\<not> C \<approx>G D \<Longrightarrow> (C,D) \<in> gclause_ord \<or> (D,C) \<in> gclause_ord\<close> sorry

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

definition Red_Inf_sup :: \<open>'a gclause set \<Rightarrow> 'a gclause inference set\<close> where
\<open>Red_Inf_sup N = {\<iota>. \<iota> \<in> ground_superposition_inference_system
                 \<and> redundant_inference (Rep_gclause (concl_of \<iota>)) (Rep_gclause ` N) (Rep_gclause ` (set (prems_of \<iota>))) [] }\<close>

(* the original definition of redundant_clause does not fit our framework because it also accounts
   for entailment by equal clauses, not just smaller ones. For example, this implies that any
   clause C is redundant in {C}, even ones that are not redundant in {}. *)
definition redundant_clause' :: \<open>'a eclause \<Rightarrow> 'a eclause set  \<Rightarrow> 'a subst \<Rightarrow> 'a clause \<Rightarrow> bool\<close>
  where \<open>redundant_clause' C S \<sigma> C' =
    (\<exists>S'. S' \<subseteq> instances S
          \<and> set_entails_clause (clset_instances S') (cl_ecl C)
          \<and> (\<forall>x \<in> S'. (mset_ecl (fst x, snd x),mset_cl (C',\<sigma>)) \<in> mult (mult trm_ord)))\<close>

definition Red_eclause :: \<open>'a gclause set \<Rightarrow> 'a gclause set\<close> where
\<open>Red_eclause N = {C. redundant_clause' (Rep_gclause C) (Rep_gclause ` N) [] (cl_ecl (Rep_gclause C))}\<close>

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

definition gclause_trms :: \<open>'a gclause \<Rightarrow> 'a trm set\<close>
  where \<open>gclause_trms C = trms_ecl (Rep_gclause C)\<close>

lemma regular_entailment_set:
  assumes \<open>N \<Turnstile>G M\<close>
  shows \<open>\<exists>N' \<subseteq> N. N' \<Turnstile>G M \<and> (\<forall>C D. C \<in> N' \<and> D \<in> N' \<and> C \<noteq> D \<longrightarrow> \<not> C \<approx>G D)\<close>
proof -
  let ?mset = \<open>\<lambda>C. mset_cl (cl_ecl (Rep_gclause C), [])\<close>
  let ?N' = \<open>\<Union>cl \<in> (?mset ` N) . {SOME C. C \<in> N \<and> ?mset C = cl}\<close>
  have \<open>?N' \<subseteq> N\<close>
  proof
    fix C
    assume \<open>C \<in> ?N'\<close>
    then obtain cl_C where cl_elem: \<open>cl_C \<in> ?mset ` N\<close>
                     and \<open>C = (SOME C. C \<in> N \<and> ?mset C = cl_C)\<close> by auto
    then show \<open>C \<in> N\<close> using someI_ex [of \<open>\<lambda>x. x \<in> N \<and> ?mset x = cl_C\<close>] by blast
  qed
  moreover have \<open>?N' \<Turnstile>G M\<close>
  proof -
    have \<open>?N' \<Turnstile>G N\<close>
    proof -
      have \<open>C \<in> N \<Longrightarrow> fo_interpretation I \<Longrightarrow> validate_clause_set I (cl_ecl ` Rep_gclause ` ?N') \<Longrightarrow> validate_clause I (cl_ecl (Rep_gclause C))\<close> for I C
      proof -
        assume \<open>C \<in> N\<close> and fo: \<open>fo_interpretation I\<close> and model: \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` ?N')\<close>
        then obtain D where \<open>D \<in> ?N'\<close> and \<open>?mset D = ?mset C\<close>
          using someI_ex [of \<open>\<lambda>x. x \<in> N \<and> ?mset x = ?mset C\<close>] by fast
        with fo and model have \<open>C \<approx>G D\<close> and \<open>validate_clause I (cl_ecl (Rep_gclause D))\<close> unfolding equiv_gclause_def by auto
        then show ?thesis using equiv_gclause_validate and fo by auto
      qed
      then show ?thesis unfolding gclause_entails_def set_entails_clause_def by auto
    qed
    also have \<open>N \<Turnstile>G M\<close> using assms .
    finally show ?thesis .
  qed
  moreover have \<open>C \<in> ?N' \<Longrightarrow> D \<in> ?N' \<Longrightarrow> C \<noteq> D \<Longrightarrow> \<not> C \<approx>G D\<close> for C D
  proof -
    assume \<open>C \<in> ?N'\<close> and \<open>D \<in> ?N'\<close> and noteq: \<open>C \<noteq> D\<close>
    then obtain cl_C cl_D where \<open>cl_C \<in> ?mset ` N\<close>
                            and \<open>cl_D \<in> ?mset ` N\<close>
                            and \<open>C = (SOME C. C \<in> N \<and> ?mset C = cl_C)\<close>
                            and \<open>D = (SOME D. D \<in> N \<and> ?mset D = cl_D)\<close> by auto
    then show ?thesis
      using someI_ex [of \<open>\<lambda>x. x \<in> N \<and> ?mset x = cl_C\<close>]
        and someI_ex [of \<open>\<lambda>x. x \<in> N \<and> ?mset x = cl_D\<close>]
        and noteq unfolding equiv_gclause_def by fastforce
  qed
  ultimately show ?thesis by meson
qed

lemma wf_total_bounded:
  assumes \<open>wf r\<close>
  assumes \<open>up \<in> S\<close>
  assumes bounded: \<open>\<forall>x \<in> S. x = up \<or> (x, up) \<in> r\<close>
  assumes total: \<open>\<forall>x \<in> S. \<forall>y \<in> S. x = y \<or> (x,y) \<in> r \<or> (y,x) \<in> r\<close>
  shows \<open>finite S\<close>
proof -
  let ?S' = \<open>\<lambda> x. {s \<in> S. (s,x) \<in> r}\<close> (* subset of S up to a maximum element *)
  let ?P = \<open>\<lambda>x. x \<in> S \<longrightarrow> finite (?S' x)\<close> (* finiteness of that subset *)
  have \<open>?P up\<close>
  proof (induction rule : wf_induct [of r])
    show \<open>wf r\<close> using assms by auto
  next
    fix y
    assume ind_hyp: \<open>\<forall>x. (x, y) \<in> r \<longrightarrow> x \<in> S \<longrightarrow> finite (?S' x)\<close>
    show \<open>y \<in> S \<longrightarrow> finite (?S' y)\<close>
    proof
      assume \<open>y \<in> S\<close>
      then consider (a) \<open>?S' y = {}\<close> | (b) \<open>\<exists>x. (x,y) \<in> r \<and> y \<in> S\<close> by blast
      then show \<open>finite (?S' y)\<close>
      proof cases
        (* y is minimal w.r.t. r *)
        case a
        show ?thesis by (simp add: a)
      next
        (* otherwise, consider the largest element of the set, i.e., the predecessor of y *)
        let ?largest = \<open>\<lambda>x S. x \<in> S \<and> (\<forall>y \<in> S. x \<noteq> y \<longrightarrow> (y,x) \<in> r)\<close>
        case b
        have \<open>\<exists>p. ?largest p (?S' y)\<close> sorry
        then obtain p where p_def: \<open>?largest p (?S' y)\<close> by auto
        then have \<open>?S' y \<subseteq> ?S' p \<union> {p}\<close> using total by auto
        moreover have \<open>finite (?S' p)\<close> using ind_hyp and p_def by auto
        ultimately show \<open>finite (?S' y)\<close>
          by (metis (no_types, lifting) finite.emptyI finite_Un finite_insert rev_finite_subset)
      qed
      have \<open>x \<in> ?S' y \<Longrightarrow> finite (?S' x)\<close> for x using ind_hyp by blast
    qed
  qed
  then have \<open>finite (?S' up)\<close> using assms by auto
  moreover have \<open>S \<subseteq> ?S' up \<union> {up}\<close> using assms by blast
  ultimately show ?thesis using finite_subset by fastforce
qed

lemma Red_eclause_alt_def: \<open>C \<in> Red_eclause N \<Longrightarrow> (\<exists>N' \<subseteq> N. finite N'
                                                             \<and> N' \<Turnstile>G {C}
                                                             \<and> (\<forall>D \<in> N'. (D, C) \<in> gclause_ord))\<close>
proof -
  assume \<open>C \<in> Red_eclause N\<close>
  then obtain S where i: \<open>S \<subseteq> instances (Rep_gclause ` N)\<close>
                  and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_gclause C))\<close>
                  and iii: \<open>\<forall>x \<in> S. (mset_ecl x, mset_cl (cl_ecl (Rep_gclause C), [])) \<in> mult (mult trm_ord)\<close>
    unfolding Red_eclause_def redundant_clause'_def by auto
  (* first consider a subset N1 that entails C *)
  let ?N1 = \<open>{C. \<exists>\<sigma>. (Rep_gclause C, \<sigma>) \<in> S}\<close>
  have N1_subset: \<open>?N1 \<subseteq> N\<close> using i instances_def
    by (smt Collect_mem_eq Collect_mono_iff Pair_inject Rep_gclause_inject image_iff)
  have N1_entail: \<open>?N1 \<Turnstile>G {C}\<close>
  proof -
    have \<open>clset_instances S = cl_ecl ` Rep_gclause ` ?N1\<close>
    proof
      show \<open>clset_instances S \<subseteq> cl_ecl ` Rep_gclause ` ?N1\<close>
      proof
      fix C
        assume \<open>C \<in> clset_instances S\<close>
        then obtain cl_C \<sigma>_C where member_S: \<open>(cl_C, \<sigma>_C) \<in> S\<close>
                               and C_def: \<open>C = subst_cl (cl_ecl cl_C) \<sigma>_C\<close>
          unfolding clset_instances_def by auto
        with i have member_N: \<open>cl_C \<in> Rep_gclause ` N\<close>
          unfolding instances_def by auto
        then have \<open>ground_clause (cl_ecl cl_C)\<close> using Rep_gclause by blast
        then have \<open>C = cl_ecl cl_C\<close>
          using C_def substs_preserve_ground_clause [of \<open>cl_ecl cl_C\<close> \<sigma>_C] by blast
        then show \<open>C \<in> cl_ecl ` Rep_gclause ` ?N1\<close>
          using member_S member_N by blast
      qed
    next
    show \<open>cl_ecl ` Rep_gclause ` ?N1 \<subseteq> clset_instances S\<close>
    proof
        fix C
        assume \<open>C \<in> cl_ecl ` Rep_gclause ` ?N1\<close>
        then obtain cl_C \<sigma>_C where member_S: \<open>(Rep_gclause cl_C, \<sigma>_C) \<in> S\<close> and \<open>C = cl_ecl (Rep_gclause cl_C)\<close> by auto
        then have \<open>C = subst_cl (cl_ecl (Rep_gclause cl_C)) \<sigma>_C\<close>
          using Rep_gclause substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause cl_C)\<close> \<sigma>_C] by blast
        with member_S show \<open>C \<in> clset_instances S\<close> unfolding clset_instances_def by auto
      qed
    qed
    then show ?thesis using ii unfolding gclause_entails_def by force
  qed
  (* The set N2 might contain duplicate clauses, so we consider a subset N2  without such problematic clauses  *)
  from N1_subset N1_entail obtain N2 where N2_subset: \<open>N2 \<subseteq> ?N1\<close>
                                       and N2_entail: \<open>N2 \<Turnstile>G {C}\<close>
                                       and N2_distinct: \<open>\<forall>C D. C \<in> N2 \<and> D \<in> N2 \<and> C \<noteq> D \<longrightarrow> \<not> C \<approx>G D\<close>
    using regular_entailment_set [of ?N1 \<open>{C}\<close>] by blast
  have \<open>N2 \<subseteq> N\<close> using N2_subset N1_subset by auto
  moreover have C_up: \<open>\<forall>D \<in> N2. (D,C) \<in> gclause_ord\<close>
  proof
    fix D
    assume \<open>D \<in> N2\<close>
    then have \<open>D \<in> ?N1\<close> using N2_subset by auto
    then obtain \<sigma>_D where \<open>(Rep_gclause D, \<sigma>_D) \<in> S\<close> by auto
    then have \<open>(mset_ecl (Rep_gclause D, []), mset_cl (cl_ecl (Rep_gclause C), [])) \<in> mult (mult trm_ord)\<close>
      using iii substitution_irrelevance [of D \<sigma>_D] by auto
    then show \<open>(D, C) \<in> gclause_ord\<close> unfolding gclause_ord_def by auto
  qed
  moreover have \<open>finite N2\<close>
  proof -
    have \<open>\<forall>X Y. X \<in> (N2 \<union> {C}) \<and> Y \<in> (N2 \<union> {C}) \<longrightarrow> X = Y \<or> (X,Y) \<in> gclause_ord \<or> (Y,X) \<in> gclause_ord\<close>
      using C_up N2_distinct gclause_ord_total by blast
    with gclause_ord_wf and C_up have \<open>finite (N2 \<union> {C})\<close>
      using wf_total_bounded [of \<open>gclause_ord\<close> C \<open>N2 \<union> {C}\<close>] by blast
    then show \<open>finite N2\<close> by auto
  qed
  ultimately show ?thesis using N2_entail N2_subset by blast
qed

lemma Red_Inf_redundant_inference_any_subst:
  assumes \<open>\<iota> \<in> Red_Inf_sup N\<close>
  shows \<open>redundant_inference (Rep_gclause (concl_of \<iota>)) (Rep_gclause ` N) (Rep_gclause ` set (prems_of \<iota>)) \<sigma>\<close>
proof -
  have \<open>redundant_inference (Rep_gclause (concl_of \<iota>)) (Rep_gclause ` N) (Rep_gclause ` set (prems_of \<iota>)) []\<close>
    using assms unfolding Red_Inf_sup_def by auto
  then obtain S where i: \<open>S \<subseteq> instances (Rep_gclause ` N)\<close>
                  and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_gclause (concl_of \<iota>)))\<close>
                  and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (concl_of \<iota>)))\<close>
                  and iv: \<open>\<forall>x \<in> S. \<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). (x,(D,[])) \<in> ecl_ord\<close>
    unfolding redundant_inference_def by auto
  have iv': \<open>x \<in> S \<Longrightarrow> \<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). (x, (D, \<sigma>)) \<in> ecl_ord\<close> for x
  proof -
    assume \<open>x \<in> S\<close>
    with iv obtain cl_D where \<open>cl_D \<in> set (prems_of \<iota>)\<close> and \<open>(x, (Rep_gclause cl_D, [])) \<in> ecl_ord\<close> by blast
    with substitution_irrelevance [of cl_D \<sigma>] show ?thesis unfolding ecl_ord_def by force
  qed
  from i ii iii iv' show ?thesis unfolding redundant_inference_def by auto
qed

lemma redundant_inference_remove_trms:
  assumes \<open>redundant_inference (Rep_gclause (remove_trms C)) N P \<sigma>\<close>
  assumes \<open>ground_clause (cl_ecl C)\<close>
  assumes \<open>finite (cl_ecl C)\<close>
  shows \<open>redundant_inference C N P \<sigma>\<close>
proof -
  from assms obtain S where i: \<open>S \<subseteq> instances N\<close>
                        and ii: \<open>set_entails_clause (clset_instances S) (cl_ecl (Rep_gclause (remove_trms C)))\<close>
                        and iii: \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (remove_trms C)))\<close>
                        and iv: \<open>\<forall>x \<in> S. \<exists>D \<in> P. (x,(D,\<sigma>)) \<in> ecl_ord\<close>
    unfolding redundant_inference_def by auto
  with ii have ii': \<open>set_entails_clause (clset_instances S) (cl_ecl C)\<close>
    using remove_trms_cl_ecl assms by auto
  with iii have \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) {}\<close>
    using remove_trms_trms_ecl assms by auto
  then have iii': \<open>\<forall>x \<in> S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) X\<close> for X
    unfolding subterms_inclusion_def by fast
  then show \<open>redundant_inference C N P \<sigma>\<close> 
    unfolding redundant_inference_def 
    using i ii' iii' iv by auto
qed

lemma subset_Red_eclause : \<open>N \<subseteq> N' \<Longrightarrow> Red_eclause N \<subseteq> Red_eclause N'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have instances_subset: \<open>instances (Rep_gclause ` N) \<subseteq> instances (Rep_gclause ` N')\<close>
    unfolding instances_def by auto
  then have \<open>redundant_clause' C (Rep_gclause ` N) \<sigma> C' \<Longrightarrow> redundant_clause' C (Rep_gclause ` N') \<sigma> C'\<close> for C C' \<sigma>
    unfolding redundant_clause'_def by auto
  then show \<open>Red_eclause N \<subseteq> Red_eclause N'\<close>
    using Collect_cong Red_eclause_def by auto
qed

lemma subset_Red_Inf_sup : \<open>N \<subseteq> N' \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup N'\<close>
proof -
  assume \<open>N \<subseteq> N'\<close>
  then have \<open>instances (Rep_gclause ` N) \<subseteq> instances (Rep_gclause ` N')\<close>
    unfolding instances_def by auto
  then have \<open>redundant_inference C (Rep_gclause ` N) P \<sigma> \<Longrightarrow> redundant_inference C (Rep_gclause ` N') P \<sigma>\<close> for \<iota> :: \<open>'a gclause inference\<close> and C P \<sigma>
    using redundant_inference_def by fastforce
  then show ?thesis unfolding Red_Inf_sup_def by blast
qed

lemma Red_gclause_entails: \<open>N \<Turnstile>G Red_eclause N\<close>
proof
  show \<open>\<forall>C\<in>Red_eclause N. N \<Turnstile>G {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain N' where \<open>N' \<subseteq> N\<close> and i: \<open>N' \<Turnstile>G {C}\<close> using Red_eclause_alt_def by metis
    then have ii: \<open>N \<Turnstile>G N'\<close> using subset_entailed by auto
    from i ii show \<open>N \<Turnstile>G {C}\<close> using entails_trans [of N N' \<open>{C}\<close>] by auto
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

lemma minimal_Red_eclause_subset:
  assumes \<open>C \<in> Red_eclause N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> C \<in> Red_eclause M \<and> (\<forall>D \<in> M. D \<notin> Red_eclause N)\<close>
proof -
  from assms obtain NC1 where \<open>NC1 \<subseteq> N \<and> finite NC1 \<and> NC1 \<Turnstile>G {C} \<and> (\<forall>D \<in> NC1. (D, C) \<in> gclause_ord)\<close> (is \<open>?P NC1\<close>)
    using Red_eclause_alt_def by metis
  then obtain NC0 where NC0_prop: \<open>?P NC0\<close> and NC0_min: \<open>(X, NC0) \<in> gclause_set_ord ==> \<not> (?P X)\<close> for X
    using wfE_min [of \<open>gclause_set_ord\<close> \<open>NC1\<close> \<open>{x. ?P x}\<close>] wf_gclause_set_ord by auto
  have \<open>D \<in> NC0 \<Longrightarrow> D \<notin> Red_eclause N\<close> for D
  proof
    assume \<open>D \<in> NC0\<close> and \<open>D \<in> Red_eclause N\<close>
    then obtain ND1 where ND1_subset: \<open>ND1 \<subseteq> N\<close>
                      and ND1_finite: \<open>finite ND1\<close>
                      and ND1_entails: \<open>ND1 \<Turnstile>G {D}\<close>
                      and ND1_ord: \<open>\<forall>E \<in> ND1. (E,D) \<in> gclause_ord\<close>
      using Red_eclause_alt_def by metis
    (* construct a smaller set than NC0 in which C is also redundant. This contradicts the minimality of NC0. *)
    let ?NCC = \<open>NC0 - {D} \<union> ND1\<close>
    have \<open>?NCC \<subseteq> N\<close> using ND1_subset and NC0_prop by auto
    moreover have \<open>finite ?NCC\<close>
      using ND1_finite NC0_prop by blast
    moreover have \<open>(?NCC, NC0) \<in> gclause_set_ord\<close>
      using smaller_gclause_set \<open>D \<in> NC0\<close> NC0_prop ND1_ord by blast
    moreover have \<open>?NCC \<Turnstile>G {C}\<close>
    proof -
      have \<open>?NCC \<Turnstile>G NC0 - {D} \<union> {D}\<close> using all_formulas_entailed ND1_entails
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
  with NC0_prop have \<open>NC0 \<subseteq> N \<and> C \<in> Red_eclause NC0 \<and> (\<forall>D \<in> NC0. D \<notin> Red_eclause N)\<close>
    unfolding Red_eclause_def sorry
  then show ?thesis by auto
qed

lemma Red_eclause_entailed: \<open>N - Red_eclause N \<Turnstile>G Red_eclause N\<close>
proof
  show \<open>\<forall>C \<in> Red_eclause N. N - Red_eclause N \<Turnstile>G {C}\<close>
  proof
    fix C
    assume \<open>C \<in> Red_eclause N\<close>
    then obtain M where M_subset: \<open>M \<subseteq> N\<close>
                    and M_Red: \<open>C \<in> Red_eclause M\<close>
                    and M_min: \<open>\<forall>D \<in> M. D \<notin> Red_eclause N\<close>
      using minimal_Red_eclause_subset by metis
    with M_subset have \<open>M \<subseteq> N - Red_eclause N\<close> by auto
    then have \<open>N - Red_eclause N \<Turnstile>G M\<close> using subset_entailed by auto
    also have \<open>M \<Turnstile>G Red_eclause M\<close> using Red_gclause_entails by auto
    also have \<open>Red_eclause M \<Turnstile>G {C}\<close> using M_Red subset_entailed by auto
    finally show \<open>N - Red_eclause N \<Turnstile>G {C}\<close> by auto
  qed
qed

lemma exists_premise_greater:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). ((Rep_gclause (concl_of \<iota>), []), (D , [])) \<in> ecl_ord\<close>
  sorry

lemma Red_Inf_concl_of:
  assumes \<open>\<iota> \<in> ground_superposition_inference_system\<close>
  shows \<open>\<iota> \<in> Red_Inf_sup {concl_of \<iota>}\<close>
proof -
  (* preliminaries *)
  have subst_irrelevant: \<open>subst_cl (cl_ecl (Rep_gclause (concl_of \<iota>))) [] = cl_ecl (Rep_gclause (concl_of \<iota>))\<close>
    using Rep_gclause [of \<open>concl_of \<iota>\<close>]
      and substs_preserve_ground_clause [of \<open>cl_ecl (Rep_gclause (concl_of \<iota>))\<close> \<open>[]\<close>] by auto
  (* proof of redundancy *)
  let ?S = \<open>{(Rep_gclause (concl_of \<iota>), [])}\<close>
  have \<open>?S \<subseteq> instances {Rep_gclause (concl_of \<iota>)}\<close>
    unfolding instances_def
    using subst_irrelevant
    and Rep_gclause [of \<open>concl_of \<iota>\<close>] by auto
  moreover have \<open>set_entails_clause (clset_instances ?S) (cl_ecl (Rep_gclause (concl_of \<iota>)))\<close>
    unfolding clset_instances_def set_entails_clause_def
    using subst_irrelevant by auto
  moreover have \<open>\<forall>x \<in> ?S. subterms_inclusion (subst_set (trms_ecl (fst x)) (snd x)) (trms_ecl (Rep_gclause (concl_of \<iota>)))\<close>
  proof -
    have \<open>subst_set (trms_ecl (Rep_gclause (concl_of \<iota>))) [] = trms_ecl (Rep_gclause (concl_of \<iota>))\<close> by auto
    then show ?thesis using subterms_inclusion_refl by auto
  qed
  moreover have \<open>\<forall>x \<in> ?S. \<exists>D \<in> Rep_gclause ` set (prems_of \<iota>). ((fst x, snd x), (D , [])) \<in> ecl_ord\<close>
    using exists_premise_greater assms by force
  ultimately have \<open>redundant_inference (Rep_gclause (concl_of \<iota>)) {Rep_gclause (concl_of \<iota>)} (Rep_gclause ` set (prems_of \<iota>)) []\<close>
    unfolding redundant_inference_def by blast
  then show ?thesis using assms unfolding Red_Inf_sup_def by auto
qed

lemma minimal_Red_Inf_sup_subset:
  assumes \<open>\<iota> \<in> Red_Inf_sup N\<close>
  shows \<open>\<exists>M. M \<subseteq> N \<and> \<iota> \<in> Red_Inf_sup M \<and> (\<forall>D \<in> M. D \<notin> Red_eclause N)\<close>
  sorry

interpretation calculus empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_eclause
proof
  show \<open>Red_Inf_sup N \<subseteq> ground_superposition_inference_system\<close> for N
    unfolding Red_Inf_sup_def by auto
next
  show \<open>B \<in> empty_gclauses \<Longrightarrow> N \<Turnstile>G {B} \<Longrightarrow> N - Red_eclause N \<Turnstile>G {B}\<close> for B N
  proof (rule ccontr)
    assume B_empty: \<open>B \<in> empty_gclauses\<close> and \<open>N \<Turnstile>G {B}\<close>
    then have N_unsat: \<open>fo_interpretation I \<Longrightarrow> \<not>validate_clause_set I (cl_ecl ` Rep_gclause ` N)\<close> for I
      unfolding gclause_entails_def set_entails_clause_def by auto
    assume \<open>\<not> N - Red_eclause N \<Turnstile>G {B}\<close>
    with N_unsat obtain I where fo_I: \<open>fo_interpretation I\<close>
                          and I_model: \<open>validate_clause_set I (cl_ecl ` Rep_gclause ` (N - Red_eclause N))\<close>
                          and \<open>\<not>validate_clause_set I (cl_ecl ` Rep_gclause ` N)\<close>
      unfolding gclause_entails_def set_entails_clause_def by blast
    then obtain C where \<open>C \<in> Rep_gclause ` N\<close>
                    and \<open>C \<notin> Rep_gclause ` (N - Red_eclause N)\<close>
                    and C_novalid: \<open>\<not> validate_clause I (cl_ecl C)\<close>
      by (smt image_iff validate_clause_set.simps)
    then have \<open>C \<in> Rep_gclause ` (Red_eclause N)\<close> by blast
    then obtain cl_C where \<open>C = Rep_gclause cl_C\<close>
                       and \<open>cl_C \<in> Red_eclause N\<close> by auto
    with Red_eclause_entailed fo_I I_model have \<open>validate_clause I (cl_ecl C)\<close>
      unfolding gclause_entails_def set_entails_clause_def by blast
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
      using minimal_Red_eclause_subset by metis
    then have \<open>C \<in> Red_eclause M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>C \<in> Red_eclause (N - N')\<close> using subset_Red_eclause by auto
  qed
next
  show \<open>N' \<subseteq> Red_eclause N \<Longrightarrow> Red_Inf_sup N \<subseteq> Red_Inf_sup (N - N')\<close> for N' N
  proof
    fix \<iota>
    assume N'_subset: \<open>N' \<subseteq> Red_eclause N\<close> and \<open>\<iota> \<in> Red_Inf_sup N\<close>
    then obtain M where \<open>M \<subseteq> N\<close> and \<open>\<iota> \<in> Red_Inf_sup M\<close> and \<open>(\<forall>D \<in> M. D \<notin> Red_eclause N)\<close>
      using minimal_Red_Inf_sup_subset by metis
    then have \<open>\<iota> \<in> Red_Inf_sup M\<close> and \<open>M \<subseteq> N - N'\<close> using N'_subset by auto
    then show \<open>\<iota> \<in> Red_Inf_sup (N - N')\<close> using subset_Red_Inf_sup by auto
  qed
next
  show \<open>\<iota> \<in> ground_superposition_inference_system \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_Inf_sup N\<close> for \<iota> N
    using Red_Inf_concl_of [of \<iota>] subset_Red_Inf_sup [of \<open>{concl_of \<iota>}\<close> N] by auto
qed

lemma derivable_factorization:
  assumes \<open>P \<in> Rep_gclause ` N\<close>
      and \<open>factorization P C \<sigma> Ground C'\<close>
      and \<open>ground_clause (cl_ecl C)\<close>
    shows \<open>\<exists> \<iota> \<in> ground_factorization_inferences. concl_of \<iota> = remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P is ground *)
  have inv_P: \<open>Rep_gclause (Abs_gclause P) = P\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P] (remove_trms C)\<close>
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
    shows \<open>\<exists> \<iota> \<in> ground_reflexion_inferences. concl_of \<iota> = remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P is ground *)
  have inv_P: \<open>Rep_gclause (Abs_gclause P) = P\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P] (remove_trms C)\<close>
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
    shows \<open>\<exists> \<iota> \<in> ground_superposition_inferences. concl_of \<iota> = remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = {P1, P2} \<and> set (prems_of \<iota>) \<subseteq> N\<close>
proof -
  (* show that P1, P2 and C are gclauses *)
  have inv_P1: \<open>Rep_gclause (Abs_gclause P1) = P1\<close>
    using Abs_gclause_inverse Rep_gclause assms(1) by blast
  have inv_P2: \<open>Rep_gclause (Abs_gclause P2) = P2\<close>
    using Abs_gclause_inverse Rep_gclause assms(2) by blast
  (* show properties of \<iota> *)
  let ?\<iota> = \<open>Infer [Abs_gclause P1, Abs_gclause P2] (remove_trms C)\<close>
  have \<open>?\<iota> \<in> ground_superposition_inferences\<close>
    unfolding ground_superposition_inferences_def using inv_P1 inv_P2 assms(2,3,4) by auto
  moreover have \<open>Rep_gclause ` set (prems_of ?\<iota>) = {P1, P2}\<close> using inv_P1 inv_P2 by auto
  moreover have \<open>set (prems_of ?\<iota>) \<subseteq> N\<close>
  proof -
    have \<open>{Abs_gclause P1, Abs_gclause P2} \<subseteq> N\<close> using assms(1,2)
      by (smt Rep_gclause_inverse image_iff insert_iff mem_Collect_eq singletonD subsetI)
    then show ?thesis by auto
  qed
  moreover have \<open>concl_of ?\<iota> = remove_trms C\<close> by auto
  ultimately show ?thesis by blast
qed

lemma derivable_gclause:
  assumes \<open>derivable C P (Rep_gclause ` N) \<sigma> Ground C'\<close>
  assumes \<open>ground_clause (cl_ecl C)\<close>
  shows \<open>\<exists> \<iota> \<in> Inf_from N. concl_of \<iota> = remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = P\<close>
proof -
  from assms(1) consider
      (a) \<open>\<exists>P1 P2. P1 \<in> (Rep_gclause ` N) \<and> P2 \<in> (Rep_gclause ` N) \<and> P = {P1, P2} \<and> superposition P1 P2 C \<sigma> Ground C'\<close>
    | (b) \<open>\<exists>P1. P1 \<in> (Rep_gclause ` N) \<and> P = {P1} \<and> factorization P1 C \<sigma> Ground C'\<close>
    | (c) \<open>\<exists>P1. P1 \<in> (Rep_gclause ` N) \<and> P = {P1} \<and> reflexion P1 C \<sigma> Ground C'\<close>
    unfolding derivable_def by blast
  then show \<open>\<exists> \<iota> \<in> Inf_from N. concl_of \<iota> = remove_trms C \<and> Rep_gclause ` set (prems_of \<iota>) = P\<close>
  proof cases
    case a
    then obtain P1 P2 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                        and \<open>P2 \<in> (Rep_gclause ` N)\<close>
                        and \<open>superposition P1 P2 C \<sigma> Ground C'\<close>
                        and \<open>P = {P1, P2}\<close>
      by auto
    then show ?thesis using derivable_superposition assms(2) unfolding Inf_from_def by blast
  next
    case b
    then obtain P1 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                     and \<open>factorization P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_factorization assms(2) unfolding Inf_from_def by blast
  next
    case c
    then obtain P1 where \<open>P1 \<in> (Rep_gclause ` N)\<close>
                     and \<open>reflexion P1 C \<sigma> Ground C'\<close>
                     and \<open>P = {P1}\<close>
      by auto
    then show ?thesis using derivable_reflexion assms(2) unfolding Inf_from_def by blast
  qed
qed

lemma saturation_gclauses:
  assumes \<open>saturated N\<close>
  shows \<open>ground_inference_saturated (Rep_gclause ` N)\<close>
proof -
  have \<open>derivable C P (Rep_gclause `  N) \<sigma> Ground C' \<Longrightarrow> ground_clause (cl_ecl C) \<Longrightarrow> redundant_inference C (Rep_gclause ` N) P \<sigma>\<close> for C P \<sigma> C'
  proof -
    assume derivable: \<open>derivable C P (Rep_gclause ` N) \<sigma> Ground C'\<close> and ground: \<open>ground_clause (cl_ecl C)\<close>
    then obtain \<iota> where \<open>\<iota> \<in> Red_Inf_sup N\<close>
                    and \<open>concl_of \<iota> = remove_trms C\<close>
                    and P_def: \<open>P = Rep_gclause ` (set (prems_of \<iota>))\<close>
      using assms(1) saturated_def derivable_gclause by blast
    then have red_inf: \<open>redundant_inference (Rep_gclause (remove_trms C)) (Rep_gclause ` N) P \<sigma>\<close>
      using Red_Inf_redundant_inference_any_subst by metis
    have \<open>finite (cl_ecl C)\<close>
      using P_def derivable derivable_clauses_are_finite Rep_gclause by blast
    with red_inf ground show ?thesis using redundant_inference_remove_trms by auto
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

interpretation static_refutational_complete_calculus empty_gclauses \<open>(\<Turnstile>G)\<close> ground_superposition_inference_system \<open>(\<Turnstile>G)\<close> Red_Inf_sup Red_eclause
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

end
end