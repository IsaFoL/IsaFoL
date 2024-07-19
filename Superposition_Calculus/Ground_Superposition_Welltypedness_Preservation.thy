theory Ground_Superposition_Welltypedness_Preservation
  imports Ground_Superposition
begin

lemma (in ground_superposition_calculus) ground_superposition_preserves_typing:
  assumes
    step: "ground_superposition D E C" and
    wt_D: "welltyped\<^sub>c \<F> D" and
    wt_E: "welltyped\<^sub>c \<F> E"
  shows "welltyped\<^sub>c \<F> C"
  using step
proof (cases D E C rule: ground_superposition.cases)
  case hyps: (ground_superpositionI L\<^sub>E E' L\<^sub>D D' \<P> \<kappa> t u t')
  show ?thesis
    unfolding \<open>C = add_mset (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)) (E' + D')\<close>
    unfolding welltyped\<^sub>c_add_mset welltyped\<^sub>c_plus
  proof (intro conjI)
    have "\<exists>\<tau>. welltyped \<F> \<kappa>\<langle>t\<rangle>\<^sub>G \<tau> \<and> welltyped \<F> u \<tau>"
    proof -
      have "welltyped\<^sub>l \<F> L\<^sub>E"
        using wt_E
        unfolding \<open>E = add_mset L\<^sub>E E'\<close> welltyped\<^sub>c_add_mset
        by argo
      hence "welltyped\<^sub>a \<F> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>E = \<P> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)\<close> welltyped\<^sub>l_def
        by auto
      thus ?thesis
        unfolding welltyped\<^sub>a_def by simp
    qed

    moreover have "\<exists>\<tau>. welltyped \<F> t \<tau> \<and> welltyped \<F> t' \<tau>"
    proof -
      have "welltyped\<^sub>l \<F> L\<^sub>D"
        using wt_D
        unfolding \<open>D = add_mset L\<^sub>D D'\<close> welltyped\<^sub>c_add_mset
        by argo
      hence "welltyped\<^sub>a \<F> (Upair t t')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>D = t \<approx> t'\<close> welltyped\<^sub>l_def
        by auto
      thus ?thesis
        unfolding welltyped\<^sub>a_def by simp
    qed

    ultimately have "\<exists>\<tau>. welltyped \<F> \<kappa>\<langle>t'\<rangle>\<^sub>G \<tau> \<and> welltyped \<F> u \<tau>"
      using gctxt_apply_term_preserves_typing[of \<F> \<kappa> t _ _ t']
      by blast
    hence "welltyped\<^sub>a \<F> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)"
      unfolding welltyped\<^sub>a_def by simp
    thus "welltyped\<^sub>l \<F> (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u))"
      unfolding welltyped\<^sub>l_def
      using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
  next
    show "welltyped\<^sub>c \<F> E'"
      using wt_E
      unfolding \<open>E = add_mset L\<^sub>E E'\<close> welltyped\<^sub>c_add_mset
      by argo
  next
    show "welltyped\<^sub>c \<F> D'"
      using wt_D
      unfolding \<open>D = add_mset L\<^sub>D D'\<close> welltyped\<^sub>c_add_mset
      by argo
  qed
qed

lemma (in ground_superposition_calculus) ground_eq_resolution_preserves_typing:
  assumes
    step: "ground_eq_resolution D C" and
    wt_D: "welltyped\<^sub>c \<F> D"
  shows "welltyped\<^sub>c \<F> C"
  using step
proof (cases D C rule: ground_eq_resolution.cases)
  case (ground_eq_resolutionI L D' t)
  thus ?thesis
    using wt_D
    unfolding welltyped\<^sub>c_def
    by simp
qed

lemma (in ground_superposition_calculus) ground_eq_factoring_preserves_typing:
  assumes
    step: "ground_eq_factoring D C" and
    wt_D: "welltyped\<^sub>c \<F> D"
  shows "welltyped\<^sub>c \<F> C"
  using step
proof (cases D C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 D' t t' t'')
  hence "welltyped\<^sub>l \<F> (t \<approx> t')" and "welltyped\<^sub>l \<F> (t \<approx> t'')" and "welltyped\<^sub>c \<F> D'"
    unfolding atomize_conj
    using wt_D welltyped\<^sub>c_add_mset by metis

  hence "\<exists>\<tau>. welltyped \<F> t \<tau> \<and> welltyped \<F> t' \<tau>" "\<exists>\<tau>. welltyped \<F> t \<tau> \<and> welltyped \<F> t'' \<tau>"
    unfolding atomize_conj welltyped\<^sub>l_def welltyped\<^sub>a_def by simp

  hence t_t'_same_type: "\<exists>\<tau>. welltyped \<F> t' \<tau> \<and> welltyped \<F> t'' \<tau>"
    using welltyped_right_unique[THEN right_uniqueD] by metis

  show ?thesis
    unfolding \<open>C = add_mset (t' !\<approx> t'') (add_mset (t \<approx> t'') D')\<close> welltyped\<^sub>c_add_mset
  proof (intro conjI)
    show "welltyped\<^sub>l \<F> (t' !\<approx> t'')"
      using t_t'_same_type
      unfolding welltyped\<^sub>l_def welltyped\<^sub>a_def by simp
  next
    show "welltyped\<^sub>l \<F> (t \<approx> t'')"
      using \<open>welltyped\<^sub>l \<F> (t \<approx> t'')\<close> .
  next
    show "welltyped\<^sub>c \<F> D'"
      using \<open>welltyped\<^sub>c \<F> D'\<close> .
  qed
qed

end