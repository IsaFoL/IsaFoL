theory Ground_Superposition_Welltypedness_Preservation
  imports Ground_Superposition Ground_Typing
begin

locale ground_superposition_welltypedness_preservation = 
  ground_superposition_calculus where select = select + 
  ground_typing where \<F> = \<F>
for 
  select :: "'f gatom clause \<Rightarrow> 'f gatom clause" and
  \<F> :: "('f, 'ty) fun_types"
begin

lemma ground_superposition_preserves_typing:
  assumes
    step: "ground_superposition D E C" and
    wt_D: "clause.is_welltyped D" and
    wt_E: "clause.is_welltyped E"
  shows "clause.is_welltyped C"
  using step
proof (cases D E C rule: ground_superposition.cases)
  case hyps: (ground_superpositionI L\<^sub>E E' L\<^sub>D D' \<P> \<kappa> t u t')
  show ?thesis
    unfolding \<open>C = add_mset (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)) (E' + D')\<close>
    unfolding clause.is_welltyped_add_mset clause.is_welltyped_plus
  proof (intro conjI)
    have "\<exists>\<tau>. term.welltyped \<kappa>\<langle>t\<rangle>\<^sub>G \<tau> \<and> term.welltyped u \<tau>"
    proof -
      have "literal.is_welltyped L\<^sub>E"
        using wt_E
        unfolding \<open>E = add_mset L\<^sub>E E'\<close> clause.is_welltyped_add_mset
        by argo

      hence "atom.is_welltyped (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>E = \<P> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u)\<close> literal.typing_defs atom.typing_defs
        by auto

      thus ?thesis
        unfolding atom.typing_defs 
        by simp
    qed

    moreover have "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t' \<tau>"
    proof -
      have "literal.is_welltyped L\<^sub>D"
        using wt_D
        unfolding \<open>D = add_mset L\<^sub>D D'\<close> clause.is_welltyped_add_mset
        by argo

      hence "atom.is_welltyped (Upair t t')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>D = t \<approx> t'\<close> literal.typing_defs atom.typing_defs
        by auto

      thus ?thesis
        unfolding atom.typing_defs
        by simp
    qed

    ultimately have "\<exists>\<tau>. term.welltyped \<kappa>\<langle>t'\<rangle>\<^sub>G \<tau> \<and> term.welltyped u \<tau>"
      using term.welltyped_context_compatible
      by blast

    hence "atom.is_welltyped (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)"
      unfolding atom.typing_defs
      by simp

    thus "literal.is_welltyped (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u))"
      unfolding literal.typing_defs atom.typing_defs
      using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
  next
    show "clause.is_welltyped E'"
      using wt_E
      unfolding \<open>E = add_mset L\<^sub>E E'\<close> clause.is_welltyped_add_mset
      by argo
  next
    show "clause.is_welltyped D'"
      using wt_D
      unfolding \<open>D = add_mset L\<^sub>D D'\<close> clause.is_welltyped_add_mset
      by argo
  qed
qed

lemma ground_eq_resolution_preserves_typing:
  assumes
    step: "ground_eq_resolution D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using step
proof (cases D C rule: ground_eq_resolution.cases)
  case (ground_eq_resolutionI L D' t)
  thus ?thesis
    using wt_D
    unfolding clause.typing_defs
    by simp
qed

lemma ground_eq_factoring_preserves_typing:
  assumes
    step: "ground_eq_factoring D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using step
proof (cases D C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 D' t t' t'')

  hence 
    "literal.is_welltyped (t \<approx> t')" and 
    "literal.is_welltyped (t \<approx> t'')" and 
    "clause.is_welltyped D'"
    unfolding atomize_conj
    using wt_D clause.is_welltyped_add_mset 
    by metis

  hence 
    "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t' \<tau>" 
    "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t'' \<tau>"
    unfolding atomize_conj literal.typing_defs atom.typing_defs
    by simp

  hence t_t'_same_type: "\<exists>\<tau>. term.welltyped t' \<tau> \<and> term.welltyped t'' \<tau>"
    using term.welltyped_right_unique[THEN right_uniqueD] 
    by metis

  show ?thesis
    unfolding \<open>C = add_mset (t' !\<approx> t'') (add_mset (t \<approx> t'') D')\<close> clause.is_welltyped_add_mset
  proof (intro conjI)
    show "literal.is_welltyped (t' !\<approx> t'')"
      using t_t'_same_type
      unfolding literal.typing_defs atom.typing_defs 
      by simp
  next
    show "literal.is_welltyped (t \<approx> t'')"
      using \<open>literal.is_welltyped (t \<approx> t'')\<close> .
  next
    show "clause.is_welltyped D'"
      using \<open>clause.is_welltyped D'\<close> .
  qed
qed

end

end
