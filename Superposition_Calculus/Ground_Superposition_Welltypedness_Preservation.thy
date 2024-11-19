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
  case hyps: (ground_superpositionI L\<^sub>E E' L\<^sub>D D' \<P> c t u t')

(* 
  TODO: Would be enough
 
  show ?thesis
    using wt_D wt_E hyps(4)
    unfolding hyps
    by fastforce
    (* or by (auto 4 3) *)
  *)

  show ?thesis
    unfolding \<open>C = add_mset (\<P> (Upair c\<langle>t'\<rangle>\<^sub>G u)) (E' + D')\<close>
    unfolding clause.is_welltyped_add clause.is_welltyped_plus
  proof (intro conjI)
    have "\<exists>\<tau>. term.welltyped c\<langle>t\<rangle>\<^sub>G \<tau> \<and> term.welltyped u \<tau>"
    proof -
      have "literal.is_welltyped L\<^sub>E"
        using wt_E
        unfolding \<open>E = add_mset L\<^sub>E E'\<close> clause.is_welltyped_add
        by argo

      hence "atom.is_welltyped (Upair c\<langle>t\<rangle>\<^sub>G u)"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>E = \<P> (Upair c\<langle>t\<rangle>\<^sub>G u)\<close> literal.welltyped_def
        by auto

      thus ?thesis
        unfolding atom.welltyped_def
        by simp
    qed

    moreover have "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t' \<tau>"
    proof -
      have "literal.is_welltyped L\<^sub>D"
        using wt_D
        unfolding \<open>D = add_mset L\<^sub>D D'\<close> clause.is_welltyped_add
        by argo

      hence "atom.is_welltyped (Upair t t')"
        using \<open>\<P> \<in> {Pos, Neg}\<close>
        unfolding \<open>L\<^sub>D = t \<approx> t'\<close> literal.welltyped_def
        by auto

      thus ?thesis
        unfolding atom.welltyped_def
        by simp
    qed

    ultimately have "\<exists>\<tau>. term.welltyped c\<langle>t'\<rangle>\<^sub>G \<tau> \<and> term.welltyped u \<tau>"
      using term.welltyped_context_compatible
      by blast

    hence "atom.is_welltyped (Upair c\<langle>t'\<rangle>\<^sub>G u)"
      unfolding atom.welltyped_def
      by simp

    thus "literal.is_welltyped (\<P> (Upair c\<langle>t'\<rangle>\<^sub>G u))"
      unfolding literal.welltyped_def 
      using \<open>\<P> \<in> {Pos, Neg}\<close> 
      by auto
  next
    show "clause.is_welltyped E'"
      using wt_E
      unfolding \<open>E = add_mset L\<^sub>E E'\<close> clause.is_welltyped_add
      by argo
  next
    show "clause.is_welltyped D'"
      using wt_D
      unfolding \<open>D = add_mset L\<^sub>D D'\<close> clause.is_welltyped_add
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
    by simp
qed

(*
TODO: 
lemma ground_eq_factoring_preserves_typing:
  assumes
    step: "ground_eq_factoring D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using assms
  by(cases rule: ground_eq_factoring.cases) auto*)

lemma ground_eq_factoring_preserves_typing:
  assumes
    step: "ground_eq_factoring D C" and
    wt_D: "clause.is_welltyped D"
  shows "clause.is_welltyped C"
  using step
proof (cases D C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 D' t t' t'')

  then have 
    "literal.is_welltyped (t \<approx> t')" and 
    "literal.is_welltyped (t \<approx> t'')" and 
    "clause.is_welltyped D'"
    using wt_D 
    unfolding atomize_conj
    by simp

  hence 
    "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t' \<tau>" 
    "\<exists>\<tau>. term.welltyped t \<tau> \<and> term.welltyped t'' \<tau>"
    unfolding atomize_conj literal.welltyped_def atom.welltyped_def
    by simp

  hence t_t'_same_type: "\<exists>\<tau>. term.welltyped t' \<tau> \<and> term.welltyped t'' \<tau>"
    using term.welltyped_right_unique[THEN right_uniqueD] 
    by metis

  show ?thesis
    unfolding \<open>C = add_mset (t' !\<approx> t'') (add_mset (t \<approx> t'') D')\<close> clause.is_welltyped_add
  proof (intro conjI)
    show "literal.is_welltyped (t' !\<approx> t'')"
      using t_t'_same_type
      unfolding literal.welltyped_def atom.welltyped_def
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
