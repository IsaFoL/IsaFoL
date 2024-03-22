theory Ground_Superposition_Soundness
  imports Ground_Superposition
begin

lemma (in ground_superposition_calculus) soundness_ground_superposition:
  assumes
    step: "ground_superposition P1 P2 C"
  shows "G_entails {P1, P2} {C}"
  using step
proof (cases P1 P2 C rule: ground_superposition.cases)
  case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')

  show ?thesis
    unfolding G_entails_def true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "'f gterm rel"
    let ?I' = "(\<lambda>(t\<^sub>1, t). Upair t\<^sub>1 t) ` I"
    assume "refl I" and "trans I" and "sym I" and "compatible_with_gctxt I" and
      "?I' \<TTurnstile> P1" and "?I' \<TTurnstile> P2"
    then obtain K1 K2 :: "'f gatom literal" where
      "K1 \<in># P1" and "?I' \<TTurnstile>l K1" and "K2 \<in># P2" and "?I' \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "?I' \<TTurnstile> C"
    proof (cases "K2 = \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')")
      case K1_def: True
      hence "?I' \<TTurnstile>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        using \<open>?I' \<TTurnstile>l K2\<close> by simp

      show ?thesis
      proof (cases "K1 = Pos (Upair t t')")
        case K2_def: True
        hence "(t, t') \<in> I"
          using \<open>?I' \<TTurnstile>l K1\<close> true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp

        have ?thesis if "\<P> = Pos"
        proof -
          from that have "(s\<langle>t\<rangle>\<^sub>G, s') \<in> I"
            using \<open>?I' \<TTurnstile>l K2\<close> K1_def true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp
          hence "(s\<langle>t'\<rangle>\<^sub>G, s') \<in> I"
            using \<open>(t, t') \<in> I\<close>
            using \<open>compatible_with_gctxt I\<close> \<open>refl I\<close> \<open>sym I\<close> \<open>trans I\<close>
            by (meson compatible_with_gctxtD refl_onD1 symD trans_onD)
          hence "?I' \<TTurnstile>l Pos (Upair s\<langle>t'\<rangle>\<^sub>G s')"
            by blast
          thus ?thesis
            unfolding ground_superpositionI that
            by simp
        qed

        moreover have ?thesis if "\<P> = Neg"
        proof -
          from that have "(s\<langle>t\<rangle>\<^sub>G, s') \<notin> I"
            using \<open>?I' \<TTurnstile>l K2\<close> K1_def true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by simp
          hence "(s\<langle>t'\<rangle>\<^sub>G, s') \<notin> I"
            using \<open>(t, t') \<in> I\<close>
            using \<open>compatible_with_gctxt I\<close> \<open>trans I\<close>
            by (metis compatible_with_gctxtD transD)
          hence "?I' \<TTurnstile>l Neg (Upair s\<langle>t'\<rangle>\<^sub>G s')"
            by (meson \<open>sym I\<close> true_lit_simps(2) true_lit_uprod_iff_true_lit_prod(2))
          thus ?thesis
            unfolding ground_superpositionI that by simp
        qed

        ultimately show ?thesis
          using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
      next
        case False
        hence "K1 \<in># P\<^sub>2'"
          using \<open>K1 \<in># P1\<close>
          unfolding ground_superpositionI by simp
        hence "?I' \<TTurnstile> P\<^sub>2'"
          using \<open>?I' \<TTurnstile>l K1\<close> by blast
        thus ?thesis
          unfolding ground_superpositionI by simp
      qed
    next
      case False
      hence "K2 \<in># P\<^sub>1'"
        using \<open>K2 \<in># P2\<close>
        unfolding ground_superpositionI by simp
      hence "?I' \<TTurnstile> P\<^sub>1'"
        using \<open>?I' \<TTurnstile>l K2\<close> by blast
      thus ?thesis
        unfolding ground_superpositionI by simp
    qed
  qed
qed

lemma (in ground_superposition_calculus) soundness_ground_eq_resolution:
  assumes step: "ground_eq_resolution P C"
  shows "G_entails {P} {C}"
  using step
proof (cases P C rule: ground_eq_resolution.cases)
  case (ground_eq_resolutionI L D' t)
  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'f gterm rel"
    assume "refl I" and "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile> P"
    then obtain K where "K \<in># P" and "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l K"
      by (auto simp: true_cls_def)
    hence "K \<noteq> L"
      by (metis \<open>refl I\<close> ground_eq_resolutionI(2) pair_imageI reflD true_lit_simps(2))
    hence "K \<in># C"
      using \<open>K \<in># P\<close> \<open>P = add_mset L D'\<close> \<open>C = D'\<close> by simp
    thus "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile> C"
      using \<open>(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l K\<close> by blast
  qed
qed

lemma (in ground_superposition_calculus) soundness_ground_eq_factoring:
  assumes step: "ground_eq_factoring P C"
  shows "G_entails {P} {C}"
  using step
proof (cases P C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'f gterm rel"
    let ?I' = "(\<lambda>(t\<^sub>1, t). Upair t\<^sub>1 t) ` I"
    assume "trans I" and "sym I" and "?I' \<TTurnstile> P"
    then obtain K :: "'f gatom literal" where
      "K \<in># P" and "?I' \<TTurnstile>l K"
      by (auto simp: true_cls_def)

    show "?I' \<TTurnstile> C"
    proof (cases "K = L\<^sub>1 \<or> K = L\<^sub>2")
      case True
      hence "I \<TTurnstile>l Pos (t, t') \<or> I \<TTurnstile>l Pos (t, t'')"
        unfolding ground_eq_factoringI
        using \<open>?I' \<TTurnstile>l K\<close> true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] by metis
      hence "I \<TTurnstile>l Pos (t, t'') \<or> I \<TTurnstile>l Neg (t', t'')"
      proof (elim disjE)
        assume "I \<TTurnstile>l Pos (t, t')"
        then show ?thesis
          unfolding true_lit_simps
          by (metis \<open>trans I\<close> transD)
      next
        assume "I \<TTurnstile>l Pos (t, t'')"
        then show ?thesis
          by simp
      qed
      hence "?I' \<TTurnstile>l Pos (Upair t t'') \<or> ?I' \<TTurnstile>l Neg (Upair t' t'')"
        unfolding true_lit_uprod_iff_true_lit_prod[OF \<open>sym I\<close>] .
      thus ?thesis
        unfolding ground_eq_factoringI
        by (metis true_cls_add_mset)
    next
      case False
      hence "K \<in># P'"
        using \<open>K \<in># P\<close>
        unfolding ground_eq_factoringI
        by auto
      hence "K \<in># C"
        by (simp add: ground_eq_factoringI(1,2,7))
      thus ?thesis
        using \<open>(\<lambda>(t\<^sub>1, t). Upair t\<^sub>1 t) ` I \<TTurnstile>l K\<close> by blast
    qed
  qed
qed

sublocale ground_superposition_calculus \<subseteq> sound_inference_system where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails
proof unfold_locales
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> G_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding G_Inf_def
    using soundness_ground_superposition
    using soundness_ground_eq_resolution
    using soundness_ground_eq_factoring
    by (auto simp: G_entails_def)
qed

end