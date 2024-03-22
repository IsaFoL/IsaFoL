theory Ground_Superposition_Welltypedness_Preservation
  imports Ground_Superposition
begin

lemma (in ground_superposition_calculus) ground_superposition_preserves_typing:
  assumes
    step: "ground_superposition D E C" and
    wt_D: "well_typed_cls \<F> D" and
    wt_E: "well_typed_cls \<F> E"
  shows "well_typed_cls \<F> C"
  using step
proof (cases D E C rule: ground_superposition.cases)
  case hyps: (ground_superpositionI L\<^sub>E E' L\<^sub>D D' \<P> \<kappa> t u t')
  show ?thesis
    unfolding \<open>C = add_mset (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)) (E' + D')\<close>
    unfolding well_typed_cls_add_mset well_typed_cls_plus
  proof (intro conjI)
    have "\<exists>\<tau>. has_type \<F> \<kappa>\<langle>t\<rangle>\<^sub>G \<tau> \<and> has_type \<F> u \<tau>"
    proof -
      have "well_typed_lit \<F> L\<^sub>E"
        using wt_E
        unfolding \<open>E = add_mset L\<^sub>E E'\<close> well_typed_cls_add_mset
        by argo
      hence "well_typed_atm \<F> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>E = \<P> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)\<close> well_typed_lit_def
        by auto
      thus ?thesis
        unfolding well_typed_atm_def by simp
    qed

    moreover have "\<exists>\<tau>. has_type \<F> t \<tau> \<and> has_type \<F> t' \<tau>"
    proof -
      have "well_typed_lit \<F> L\<^sub>D"
        using wt_D
        unfolding \<open>D = add_mset L\<^sub>D D'\<close> well_typed_cls_add_mset
        by argo
      hence "well_typed_atm \<F> (Upair t t')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>D = t \<approx> t'\<close> well_typed_lit_def
        by auto
      thus ?thesis
        unfolding well_typed_atm_def by simp
    qed

    ultimately have "\<exists>\<tau>. has_type \<F> \<kappa>\<langle>t'\<rangle>\<^sub>G \<tau> \<and> has_type \<F> u \<tau>"
      using gctxt_apply_term_preserves_typing[of \<F> \<kappa> t _ _ t']
      by blast
    hence "well_typed_atm \<F> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)"
      unfolding well_typed_atm_def by simp
    thus "well_typed_lit \<F> (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u))"
      unfolding well_typed_lit_def
      using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
  next
    show "well_typed_cls \<F> E'"
      using wt_E
      unfolding \<open>E = add_mset L\<^sub>E E'\<close> well_typed_cls_add_mset
      by argo
  next
    show "well_typed_cls \<F> D'"
      using wt_D
      unfolding \<open>D = add_mset L\<^sub>D D'\<close> well_typed_cls_add_mset
      by argo
  qed
qed

lemma (in ground_superposition_calculus) ground_eq_resolution_preserves_typing:
  assumes
    step: "ground_eq_resolution D C" and
    wt_D: "well_typed_cls \<F> D"
  shows "well_typed_cls \<F> C"
  using step
proof (cases D C rule: ground_eq_resolution.cases)
  case (ground_eq_resolutionI L t)
  thus ?thesis
    using wt_D
    unfolding well_typed_cls_def
    by simp
qed

lemma (in ground_superposition_calculus) ground_eq_factoring_preserves_typing:
  assumes
    step: "ground_eq_factoring D C" and
    wt_D: "well_typed_cls \<F> D"
  shows "well_typed_cls \<F> C"
  using step
proof (cases D C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
  hence "well_typed_lit \<F> (t \<approx> t')" and "well_typed_lit \<F> (t \<approx> t'')" and "well_typed_cls \<F> P'"
    unfolding atomize_conj
    using wt_D well_typed_cls_add_mset by metis
  hence "\<exists>\<tau>. has_type \<F> t \<tau> \<and> has_type \<F> t' \<tau>" "\<exists>\<tau>. has_type \<F> t \<tau> \<and> has_type \<F> t'' \<tau>"
    unfolding atomize_conj well_typed_lit_def well_typed_atm_def by simp
  hence t_t'_same_type: "\<exists>\<tau>. has_type \<F> t' \<tau> \<and> has_type \<F> t'' \<tau>"
    using right_unique_has_type[THEN right_uniqueD] by metis

  show ?thesis
    unfolding \<open>C = add_mset (t' !\<approx> t'') (add_mset (t \<approx> t'') P')\<close> well_typed_cls_add_mset
  proof (intro conjI)
    show "well_typed_lit \<F> (t' !\<approx> t'')"
      using t_t'_same_type
      unfolding well_typed_lit_def well_typed_atm_def by simp
  next
    show "well_typed_lit \<F> (t \<approx> t'')"
      using \<open>well_typed_lit \<F> (t \<approx> t'')\<close> .
  next
    show "well_typed_cls \<F> P'"
      using \<open>well_typed_cls \<F> P'\<close> .
  qed
qed

end