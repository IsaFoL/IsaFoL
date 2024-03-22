theory Ground_Superposition_Welltypedness_Preservation
  imports Ground_Superposition
begin

lemma (in ground_superposition_calculus) ground_superposition_preserves_typing:
  assumes
    step: "ground_superposition P1 P2 C" and
    wt_P1: "well_typed_cls \<F> P1" and
    wt_P2: "well_typed_cls \<F> P2"
  shows "well_typed_cls \<F> C"
  using step
proof (cases P1 P2 C rule: ground_superposition.cases)
  case hyps: (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
  show ?thesis
    unfolding \<open>C = add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2')\<close>
    unfolding well_typed_cls_add_mset well_typed_cls_plus
  proof (intro conjI)
    have "\<exists>\<tau>. has_type \<F> s\<langle>t\<rangle>\<^sub>G \<tau> \<and> has_type \<F> s' \<tau>"
    proof -
      have "well_typed_lit \<F> L\<^sub>1"
        using wt_P2
        unfolding \<open>P2 = add_mset L\<^sub>1 P\<^sub>1'\<close> well_typed_cls_add_mset
        by argo
      hence "well_typed_atm \<F> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>1 = \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')\<close> well_typed_lit_def
        by auto
      thus ?thesis
        unfolding well_typed_atm_def by simp
    qed

    moreover have "\<exists>\<tau>. has_type \<F> t \<tau> \<and> has_type \<F> t' \<tau>"
    proof -
      have "well_typed_lit \<F> L\<^sub>2"
        using wt_P1
        unfolding \<open>P1 = add_mset L\<^sub>2 P\<^sub>2'\<close> well_typed_cls_add_mset
        by argo
      hence "well_typed_atm \<F> (Upair t t')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>2 = t \<approx> t'\<close> well_typed_lit_def
        by auto
      thus ?thesis
        unfolding well_typed_atm_def by simp
    qed

    ultimately have "\<exists>\<tau>. has_type \<F> s\<langle>t'\<rangle>\<^sub>G \<tau> \<and> has_type \<F> s' \<tau>"
      using gctxt_apply_term_preserves_typing[of \<F> s t _ _ t']
      by blast
    hence "well_typed_atm \<F> (Upair s\<langle>t'\<rangle>\<^sub>G s')"
      unfolding well_typed_atm_def by simp
    thus "well_typed_lit \<F> (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s'))"
      unfolding well_typed_lit_def
      using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
  next
    show "well_typed_cls \<F> P\<^sub>1'"
      using wt_P2
      unfolding \<open>P2 = add_mset L\<^sub>1 P\<^sub>1'\<close> well_typed_cls_add_mset
      by argo
  next
    show "well_typed_cls \<F> P\<^sub>2'"
      using wt_P1
      unfolding \<open>P1 = add_mset L\<^sub>2 P\<^sub>2'\<close> well_typed_cls_add_mset
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