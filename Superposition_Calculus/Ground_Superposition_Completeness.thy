theory Ground_Superposition_Completeness
  imports Ground_Superposition
begin

sublocale ground_superposition_calculus \<subseteq> statically_complete_calculus where
  Bot = G_Bot and
  Inf = G_Inf and
  entails = G_entails and
  Red_I = Red_I and
  Red_F = Red_F
proof unfold_locales
  fix B :: "'f atom clause" and N :: "'f atom clause set"
  assume "B \<in> G_Bot" and "saturated N"
  hence "B = {#}"
    by simp

  assume "G_entails N {B}"
  hence "{#} \<in> N"
    unfolding \<open>B = {#}\<close>
  proof (rule contrapos_pp)
    assume "{#} \<notin> N"

    define I :: "'f gterm rel" where
      "I = (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>"

    show "\<not> G_entails N G_Bot"
      unfolding G_entails_def not_all not_imp
    proof (intro exI conjI)
      show "refl I"
        by (simp only: I_def refl_join)
    next
      show "trans I"
        unfolding I_def
      proof (rule trans_join)
        have "wf ((rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<inverse>)"
        proof (rule wf_converse_rewrite_inside_gctxt)
          fix s t
          assume "(s, t) \<in> (\<Union>D \<in> N. equation N D)"
          then obtain C where "C \<in> N" "(s, t) \<in> equation N C"
            by auto
          thus "t \<prec>\<^sub>t s"
            by (auto elim: mem_equationE)
        qed auto
        thus "SN (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))"
          unfolding SN_iff_wf .
      next
        show "WCR (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))"
          using WCR_Union_rewrite_sys .
      qed
    next
      show "sym I"
        by (simp only: I_def sym_join)
    next
      show "compatible_with_gctxt I"
        unfolding I_def
        by (simp only: I_def compatible_with_gctxt_join compatible_with_gctxt_rewrite_inside_gctxt)
    next
      show "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s N"
        unfolding I_def
        using model_construction(2)[OF \<open>saturated N\<close> \<open>{#} \<notin> N\<close>]
        by (simp add: true_clss_def)
    next
      show "\<not> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s G_Bot"
        by simp
    qed
  qed
  thus "\<exists>B'\<in>G_Bot. B' \<in> N"
    by auto
qed

end