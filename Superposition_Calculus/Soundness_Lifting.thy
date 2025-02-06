theory Soundness_Lifting
  imports
    Saturation_Framework_Extensions.Clausal_Calculus
    Saturation_Framework.Lifting_to_Non_Ground_Calculi
begin

context lifting_intersection
begin

lemma lift_soundness:
  assumes
    sound_G: "\<forall>q \<in> Q. sound_inference_system  (Inf_G_q q) Bot_G (entails_q q)" and
    None: "\<forall>q \<in> Q. \<forall>\<iota> \<in> Inf_F. \<G>_I_q q \<iota> = None \<longrightarrow> \<G>_F_q q (concl_of \<iota>) = {}" (* TODO: Weaken *) and
    prems: "\<forall>q \<in> Q. \<forall>\<iota> \<in> Inf_F. \<Union> (set ` prems_of ` the (\<G>_I_q q \<iota>)) \<subseteq> \<G>_Fset_q q (set (prems_of \<iota>))" and
    concl: "\<forall>q \<in> Q. \<forall>\<iota> \<in> Inf_F. \<G>_F_q q (concl_of \<iota>) \<subseteq> concl_of ` the (\<G>_I_q q \<iota>)"
  shows
    "sound_inference_system Inf_F Bot_F entails_\<G>"
  unfolding sound_inference_system_def sound_inference_system_axioms_def
proof (intro conjI allI impI)

  show "consequence_relation Bot_F (\<Turnstile>\<inter>\<G>)"
    using intersect_cons_rel_family 
    by blast

  then interpret consequence_relation Bot_F "(\<Turnstile>\<inter>\<G>)" .

  fix \<iota>
  assume \<iota>: "\<iota> \<in> Inf_F"

  show "set (prems_of \<iota>) \<Turnstile>\<inter>\<G> {concl_of \<iota>}"
  proof (unfold entails_def, intro ballI)

    fix q
    assume q_in: "q \<in> Q"

    interpret lifted_q_calc:
      tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q q" "Inf_G_q q" "Red_I_q q"
      "Red_F_q q" "\<G>_F_q q" "\<G>_I_q q"
      using q_in by (simp add: standard_lifting_family)

    interpret sound_inference_system "Inf_G_q q" Bot_G "entails_q q"
      by (simp add: q_in sound_G)

    show "entails_q q (\<G>_Fset_q q (set (prems_of \<iota>))) (\<G>_Fset_q q {concl_of \<iota>})"
    proof (cases "\<G>_I_q q \<iota> = None")
      case True
      then have "\<G>_F_q q (concl_of \<iota>) = {}"
        using None \<iota> q_in
        by blast

      then show ?thesis
        by (simp add: lifted_q_calc.ground.subset_entailed)
    next
      case False
      have xx: "\<G>_F_q q (concl_of \<iota>) \<subseteq> concl_of ` the (\<G>_I_q q \<iota>)"
        using concl
        using \<iota> q_in by blast

      from False have "the (\<G>_I_q q \<iota>) \<subseteq> Inf_G_q q"
        by (simp add: \<open>\<iota> \<in> Inf_F\<close> lifted_q_calc.grounded_inf_in_ground_inf)

      then have "\<And>\<iota>\<^sub>G. \<iota>\<^sub>G \<in> the (\<G>_I_q q \<iota>) \<Longrightarrow> entails_q q (set (prems_of \<iota>\<^sub>G)) {concl_of \<iota>\<^sub>G}"
        using sound
        by blast

      then have sound': "entails_q q (\<Union>(set ` prems_of ` the (\<G>_I_q q \<iota>))) (concl_of ` the (\<G>_I_q q \<iota>))"
        by (smt (verit) Sup_upper image_iff lifted_q_calc.ground.all_formulas_entailed lifted_q_calc.ground.entails_trans
            lifted_q_calc.ground.subset_entailed)

      with prems 
      have "entails_q q (lifted_q_calc.\<G>_Fset (set (inference.prems_of \<iota>))) (concl_of ` the (\<G>_I_q q \<iota>))"
        by (meson \<iota> lifted_q_calc.ground.entails_trans lifted_q_calc.ground.subset_entailed q_in)

      with xx show ?thesis 
        using sound
        by (metis lifted_q_calc.ground.entail_unions lifted_q_calc.ground.entails_trans lifted_q_calc.ground.subset_entailed singletonD)
     qed
  qed 
qed

abbreviation ground_Inf_underapproximated :: "'q \<Rightarrow> 'f set \<Rightarrow> bool" where
  "ground_Inf_underapproximated q N \<equiv>
   {\<iota>. \<exists>\<iota>'\<in> Inf_from N. \<G>_I_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I_q q \<iota>')} \<union> Red_I_q q (\<G>_Fset_q q N)
    \<subseteq> ground.Inf_from_q q (\<G>_Fset_q q N)"

lemma lift_soundness':
  assumes
    sound_G: "\<forall>q \<in> Q. sound_inference_system  (Inf_G_q q) Bot_G (entails_q q)" and
    underapproximated: "\<exists>q \<in> Q. ground_Inf_underapproximated q N"
  shows
    "sound_inference_system Inf_F Bot_F entails_\<G>"
  thm statically_complete_calculus_def statically_complete_calculus_axioms_def
  sorry

end

end
