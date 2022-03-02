theory WB_More_Refinement_Loops
imports
  Weidenbach_Book_Base.WB_List_More
  "HOL-Library.Cardinality"
  "HOL-Eisbach.Eisbach"
  "HOL-Library.Rewrite"
  "Refine_Monadic.Refine_While"
  "Refine_Monadic.Refine_Foreach"
begin

lemma SPEC_add_information: \<open>P \<Longrightarrow> A \<le> SPEC Q \<Longrightarrow> A \<le> SPEC(\<lambda>x. Q x \<and> P)\<close>
  by auto

lemma bind_refine_spec: \<open>(\<And>x. \<Phi> x \<Longrightarrow> f x \<le> \<Down> R M) \<Longrightarrow> M' \<le> SPEC \<Phi> \<Longrightarrow> M' \<bind> f \<le> \<Down> R M\<close>
  by (auto simp add: pw_le_iff refine_pw_simps)

lemma intro_spec_iff:
  \<open>(RES X \<bind> f \<le> M) = (\<forall>x\<in>X. f x \<le> M)\<close>
  using intro_spec_refine_iff[of X f Id M] by auto

lemma case_prod_bind:
  assumes \<open>\<And>x1 x2. x = (x1, x2) \<Longrightarrow> f x1 x2 \<le> \<Down> R I\<close>
  shows \<open>(case x of (x1, x2) \<Rightarrow> f x1 x2) \<le> \<Down> R I\<close>
  using assms by (cases x) auto

lemma (in transfer) transfer_bool[refine_transfer]:
  assumes "\<alpha> fa \<le> Fa"
  assumes "\<alpha> fb \<le> Fb"
  shows "\<alpha> (case_bool fa fb x) \<le> case_bool Fa Fb x"
  using assms by (auto split: bool.split)

lemma ref_two_step': \<open>A \<le> B \<Longrightarrow> \<Down> R A \<le>  \<Down> R B\<close>
  by (auto intro: ref_two_step)

lemma RES_RETURN_RES: \<open>RES \<Phi> \<bind> (\<lambda>T. RETURN (f T)) = RES (f ` \<Phi>)\<close>
  by (simp add: bind_RES_RETURN_eq setcompr_eq_image)

lemma RES_RES_RETURN_RES: \<open>RES A \<bind> (\<lambda>T. RES (f T)) = RES (\<Union>(f ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps)

lemma RES_RES2_RETURN_RES: \<open>RES A \<bind> (\<lambda>(T, T'). RES (f T T')) = RES (\<Union>(uncurry f ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def)

lemma RES_RES3_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(T, T', T''). RES (f T T' T'')) = RES (\<Union>((\<lambda>(a, b, c). f a b c) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def)

(* taken from IICF*)
lemma meta_same_imp_rule: "(\<lbrakk>PROP P; PROP P\<rbrakk> \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> PROP Q)"
  by rule
lemma split_prod_bound: "(\<lambda>p. f p) = (\<lambda>(a,b). f (a,b))" by auto

lemma RES_RETURN_RES3:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T, T', T''). RETURN (f T T' T'')) = RES ((\<lambda>(a, b, c). f a b c) ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c). f a b c\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  by auto

lemma RES_RES_RETURN_RES2: \<open>RES A \<bind> (\<lambda>(T, T'). RETURN (f T T')) = RES (uncurry f ` A)\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def)

lemma bind_refine_res: \<open>(\<And>x. x \<in> \<Phi> \<Longrightarrow> f x \<le> \<Down> R M) \<Longrightarrow> M' \<le> RES \<Phi> \<Longrightarrow> M' \<bind> f \<le> \<Down> R M\<close>
  by (auto simp add: pw_le_iff refine_pw_simps)

lemma RES_RETURN_RES_RES2:
   \<open>RES \<Phi> \<bind> (\<lambda>(T, T'). RETURN (f T T')) = RES (uncurry f ` \<Phi>)\<close>
  using RES_RES2_RETURN_RES[of \<open>\<Phi>\<close> \<open>\<lambda>T T'. {f T T'}\<close>]
  apply (subst (asm)(2) split_prod_bound)
  by (auto simp: RETURN_def uncurry_def)

text \<open>
  This theorem adds the invariant at the beginning of next iteration to the current invariant,
  i.e., the invariant is added as a post-condition on the current iteration.

  This is useful to reduce duplication in theorems while refining.
\<close>

lemma RECT_WHILEI_body_add_post_condition:
    \<open>REC\<^sub>T (WHILEI_body (\<bind>) RETURN I' b' f) x' =
     (REC\<^sub>T (WHILEI_body (\<bind>) RETURN (\<lambda>x'. I' x' \<and> (b' x' \<longrightarrow> f x' = FAIL \<or> f x' \<le> SPEC I')) b' f) x')\<close>
  (is \<open>REC\<^sub>T ?f x' = REC\<^sub>T ?f' x'\<close>)
proof -
  have le: \<open>flatf_gfp ?f x' \<le> flatf_gfp ?f' x'\<close> for x'
  proof (induct arbitrary: x' rule: flatf_ord.fixp_induct[where b = top and
        f = ?f'])
    case 1
    then show ?case
      unfolding fun_lub_def pw_le_iff
      by (rule ccpo.admissibleI)
        (smt chain_fun flat_lub_in_chain mem_Collect_eq nofail_simps(1))
  next
    case 2
    then show ?case by (auto simp: WHILEI_mono_ge)
  next
    case 3
    then show ?case by simp
  next
    case (4 x)
    have  \<open>(RES X \<bind> f \<le> M) = (\<forall>x\<in>X. f x \<le> M)\<close> for x f M X
      using intro_spec_refine_iff[of _ _ \<open>Id\<close>] by auto
    thm bind_refine_RES(2)[of _ Id, simplified]
    have [simp]: \<open>flatf_mono FAIL (WHILEI_body (\<bind>) RETURN I' b' f)\<close>
      by (simp add: WHILEI_mono_ge)

    have \<open>flatf_gfp ?f x' = ?f (?f (flatf_gfp ?f)) x'\<close>
      apply (subst flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      apply (subst flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      ..
    also have \<open>\<dots> = WHILEI_body (\<bind>)
        RETURN (\<lambda>x'. I' x' \<and> (b' x' \<longrightarrow> f x' = FAIL \<or> f x' \<le> SPEC I')) b' f
        (WHILEI_body (\<bind>) RETURN I' b' f (flatf_gfp (WHILEI_body (\<bind>) RETURN I' b' f))) x'\<close>
      apply (subst (1) WHILEI_body_def, subst (1) WHILEI_body_def)
      apply (subst (2) WHILEI_body_def, subst (2) WHILEI_body_def)
      apply simp_all
      apply (cases \<open>f x'\<close>)
       apply (auto simp: RES_RETURN_RES nofail_def[symmetric] pw_RES_bind_choose
          split: if_splits)
      done
    also have \<open>\<dots> =  WHILEI_body (\<bind>)
      RETURN (\<lambda>x'. I' x' \<and> (b' x' \<longrightarrow> f x' = FAIL \<or> f x' \<le> SPEC I')) b' f
      ((flatf_gfp (WHILEI_body (\<bind>) RETURN I' b' f))) x'\<close>
      apply (subst (2) flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      ..
    finally have unfold1: \<open>flatf_gfp (WHILEI_body (\<bind>) RETURN I' b' f) x' =
         ?f' (flatf_gfp (WHILEI_body (\<bind>) RETURN I' b' f)) x'\<close>
      .
    have [intro!]: \<open>(\<And>x. g x \<le> (h:: 'a \<Rightarrow> 'a nres) x) \<Longrightarrow> fx \<bind> g \<le> fx \<bind> h\<close> for g h fx fy
      by (refine_rcg bind_refine'[where R = \<open>Id\<close>, simplified]) fast
    show ?case
      apply (subst unfold1)
      using 4 unfolding WHILEI_body_def by auto
  qed

  have ge: \<open>flatf_gfp ?f x' \<ge>  flatf_gfp ?f' x'\<close> for x'
  proof (induct arbitrary: x' rule: flatf_ord.fixp_induct[where b = top and
        f = ?f])
    case 1
    then show ?case
      unfolding fun_lub_def pw_le_iff
      by (rule ccpo.admissibleI) (smt chain_fun flat_lub_in_chain mem_Collect_eq nofail_simps(1))
  next
    case 2
    then show ?case by (auto simp: WHILEI_mono_ge)
  next
    case 3
    then show ?case by simp
  next
    case (4 x)
    have  \<open>(RES X \<bind> f \<le> M) = (\<forall>x\<in>X. f x \<le> M)\<close> for x f M X
      using intro_spec_refine_iff[of _ _ \<open>Id\<close>] by auto
    thm bind_refine_RES(2)[of _ Id, simplified]
    have [simp]: \<open>flatf_mono FAIL ?f'\<close>
      by (simp add: WHILEI_mono_ge)
    have H: \<open>A = FAIL \<longleftrightarrow> \<not>nofail A\<close> for A by (auto simp: nofail_def)
    have \<open>flatf_gfp ?f' x' = ?f' (?f' (flatf_gfp ?f')) x'\<close>
      apply (subst flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      apply (subst flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      ..
    also have \<open>\<dots> = ?f (?f' (flatf_gfp ?f')) x'\<close>
      apply (subst (1) WHILEI_body_def, subst (1) WHILEI_body_def)
      apply (subst (2) WHILEI_body_def, subst (2) WHILEI_body_def)
      apply simp_all
      apply (cases \<open>f x'\<close>)
       apply (auto simp: RES_RETURN_RES nofail_def[symmetric] pw_RES_bind_choose
          eq_commute[of \<open>FAIL\<close>] H
          split: if_splits
          cong: if_cong)
      done
    also have \<open>\<dots> = ?f (flatf_gfp ?f') x'\<close>
      apply (subst (2) flatf_ord.fixp_unfold)
       apply (solves \<open>simp\<close>)
      ..
    finally have unfold1: \<open>flatf_gfp ?f' x' =
         ?f (flatf_gfp ?f') x'\<close>
      .
    have [intro!]: \<open>(\<And>x. g x \<le>(h:: 'a \<Rightarrow> 'a nres) x) \<Longrightarrow> fx \<bind> g \<le> fx \<bind> h\<close> for g h fx fy
      by (refine_rcg bind_refine'[where R = \<open>Id\<close>, simplified]) fast
    show ?case
      apply (subst unfold1)
      using 4
      unfolding WHILEI_body_def
      by (auto intro: bind_refine'[where R = \<open>Id\<close>, simplified])
  qed
  show ?thesis
    unfolding RECT_def
    using le[of x'] ge[of x'] by (auto simp: WHILEI_body_trimono)
qed

lemma WHILEIT_add_post_condition:
 \<open>(WHILEIT I' b' f' x') =
  (WHILEIT (\<lambda>x'. I' x' \<and> (b' x' \<longrightarrow> f' x' = FAIL \<or> f' x' \<le> SPEC I'))
    b' f' x')\<close>
  unfolding WHILEIT_def
  apply (subst RECT_WHILEI_body_add_post_condition)
  ..

lemma WHILEIT_rule_stronger_inv:
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close> and
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> and
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> \<Phi> s\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> SPEC \<Phi>\<close>
proof -
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)
  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> SPEC \<Phi>\<close>
    by (rule WHILEIT_rule) (use assms in \<open>auto simp: \<close>)
  finally show ?thesis .
qed

lemma RES_RETURN_RES2:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T, T'). RETURN (f T T')) = RES (uncurry f ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>uncurry f\<close>]
  apply (subst (asm)(2) split_prod_bound)
  by auto

lemma WHILEIT_rule_stronger_inv_RES:
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close>
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> and
   \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> s \<in> \<Phi>\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> RES \<Phi>\<close>
proof -
  have RES_SPEC: \<open>RES \<Phi> = SPEC(\<lambda>s. s \<in> \<Phi>)\<close>
    by auto
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)
  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> RES \<Phi>\<close>
    unfolding RES_SPEC
    by (rule WHILEIT_rule) (use assms in \<open>auto simp: \<close>)
  finally show ?thesis .
qed


subsubsection \<open>Merge Post-Conditions\<close>

lemma Down_add_assumption_middle:
  assumes
    \<open>nofail U\<close> and
    \<open>V \<le> \<Down> {(T1, T0). Q T1 T0 \<and> P T1 \<and> Q' T1 T0} U\<close> and
    \<open>W \<le> \<Down> {(T2, T1). R T2 T1} V\<close>
  shows \<open>W \<le> \<Down> {(T2, T1). R T2 T1 \<and> P T1} V\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by blast

lemma Down_del_assumption_middle:
  assumes
    \<open>S1 \<le> \<Down> {(T1, T0). Q T1 T0 \<and> P T1 \<and> Q' T1 T0} S0\<close>
  shows \<open>S1 \<le> \<Down> {(T1, T0). Q T1 T0 \<and> Q' T1 T0} S0\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by blast

lemma Down_add_assumption_beginning:
  assumes
    \<open>nofail U\<close> and
    \<open>V \<le> \<Down> {(T1, T0). P T1 \<and> Q' T1 T0} U\<close> and
    \<open>W \<le> \<Down> {(T2, T1). R T2 T1} V\<close>
  shows \<open>W \<le> \<Down> {(T2, T1). R T2 T1 \<and> P T1} V\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by blast

lemma Down_add_assumption_beginning_single:
  assumes
    \<open>nofail U\<close> and
    \<open>V \<le> \<Down> {(T1, T0). P T1} U\<close> and
    \<open>W \<le> \<Down> {(T2, T1). R T2 T1} V\<close>
  shows \<open>W \<le> \<Down> {(T2, T1). R T2 T1 \<and> P T1} V\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by blast

lemma Down_del_assumption_beginning:
  fixes U :: \<open>'a nres\<close> and V :: \<open>'b nres\<close> and Q Q' :: \<open>'b \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes
    \<open>V \<le> \<Down> {(T1, T0). Q T1 T0 \<and> Q' T1 T0} U\<close>
  shows \<open>V \<le> \<Down> {(T1, T0). Q' T1 T0} U\<close>
  using assms unfolding nres_rel_def fun_rel_def pw_le_iff pw_conc_inres pw_conc_nofail
  by blast

method unify_Down_invs2_normalisation_post =
  ((unfold meta_same_imp_rule True_implies_equals conj_assoc)?)

method unify_Down_invs2 =
  (match premises in
      \<comment> \<open>if the relation 2-1 has not assumption, we add True. Then we call out method again and
           this time it will match since it has an assumption.\<close>
      I: \<open>S1 \<le> \<Down> R10 S0\<close> and
      J[thin]: \<open>S2 \<le> \<Down> R21 S1\<close>
       for S1:: \<open>'b nres\<close> and S0 :: \<open>'a nres\<close> and S2 :: \<open>'c nres\<close> and R10 R21 \<Rightarrow>
        \<open>insert True_implies_equals[where P = \<open>S2 \<le> \<Down> R21 S1\<close>, symmetric,
           THEN equal_elim_rule1, OF J]\<close>
    \<bar> I[thin]: \<open>S1 \<le> \<Down> {(T1, T0). P T1} S0\<close> (multi) and
      J[thin]: _ for S1:: \<open>'b nres\<close> and S0 :: \<open>'a nres\<close> and P :: \<open>'b \<Rightarrow> bool\<close> \<Rightarrow>
       \<open>match J[uncurry] in
         J[curry]: \<open>_ \<Longrightarrow> S2 \<le> \<Down> {(T2, T1). R T2 T1} S1\<close> for S2 :: \<open>'c nres\<close> and R \<Rightarrow>
          \<open>insert Down_add_assumption_beginning_single[where P = P and R = R and
               W = S2 and V = S1 and U = S0, OF _ I J];
           unify_Down_invs2_normalisation_post\<close>
       \<bar> _ \<Rightarrow> \<open>fail\<close>\<close>
   \<bar> I[thin]: \<open>S1 \<le> \<Down> {(T1, T0). P T1 \<and> Q' T1 T0} S0\<close> (multi) and
     J[thin]: _ for S1:: \<open>'b nres\<close> and S0 :: \<open>'a nres\<close> and Q' and P :: \<open>'b \<Rightarrow> bool\<close> \<Rightarrow>
       \<open>match J[uncurry] in
         J[curry]: \<open>_ \<Longrightarrow> S2 \<le> \<Down> {(T2, T1). R T2 T1} S1\<close> for S2 :: \<open>'c nres\<close> and R \<Rightarrow>
          \<open>insert Down_add_assumption_beginning[where Q' = Q' and P = P and R = R and
              W = S2 and V = S1 and U = S0,
              OF _ I J];
           insert Down_del_assumption_beginning[where Q = \<open>\<lambda>S _. P S\<close> and Q' = Q' and V = S1 and
             U = S0, OF I];
          unify_Down_invs2_normalisation_post\<close>
       \<bar> _ \<Rightarrow> \<open>fail\<close>\<close>
   \<bar> I[thin]: \<open>S1 \<le> \<Down> {(T1, T0). Q T0 T1\<and> Q' T1 T0} S0\<close> (multi) and
     J: _ for S1:: \<open>'b nres\<close> and S0 :: \<open>'a nres\<close> and Q Q' \<Rightarrow>
       \<open>match J[uncurry] in
         J[curry]: \<open>_ \<Longrightarrow> S2 \<le> \<Down> {(T2, T1). R T2 T1} S1\<close> for S2 :: \<open>'c nres\<close> and R \<Rightarrow>
          \<open>insert Down_del_assumption_beginning[where Q = \<open>\<lambda> x y. Q y x\<close> and Q' = Q', OF I];
           unify_Down_invs2_normalisation_post\<close>
       \<bar> _ \<Rightarrow> \<open>fail\<close>\<close>
  )

text \<open>Example:\<close>
lemma
  assumes
    \<open>nofail S0\<close> and
    1: \<open>S1 \<le> \<Down> {(T1, T0). Q T1 T0 \<and> P T1 \<and> P' T1 \<and> P''' T1 \<and> Q' T1 T0 \<and> P42 T1} S0\<close> and
    2: \<open>S2 \<le> \<Down> {(T2, T1). R T2 T1} S1\<close>
  shows \<open>S2
     \<le> \<Down> {(T2, T1).
           R T2 T1 \<and>
           P T1 \<and> P' T1 \<and> P''' T1 \<and> P42 T1}
         S1\<close>
  using assms apply -
  apply unify_Down_invs2+
  apply fast
  done

subsubsection \<open>Inversion Tactics\<close>

lemma refinement_trans_long:
  \<open>A = A' \<Longrightarrow> B = B' \<Longrightarrow> R \<subseteq> R' \<Longrightarrow> A \<le> \<Down> R B \<Longrightarrow> A' \<le> \<Down> R' B'\<close>
  by (meson pw_ref_iff subsetCE)

lemma mem_set_trans:
  \<open>A \<subseteq> B \<Longrightarrow> a \<in> A \<Longrightarrow> a \<in> B\<close>
  by auto

lemma fun_rel_syn_invert:
  \<open>a = a' \<Longrightarrow> b \<subseteq> b' \<Longrightarrow> (fun_rel_syn a b) \<subseteq> (a' \<rightarrow> b')\<close>
  by (auto simp: refine_rel_defs)

lemma nres_rel_mono:
  \<open>a \<subseteq> a'  \<Longrightarrow> \<langle>a\<rangle> nres_rel \<subseteq> \<langle>a'\<rangle> nres_rel\<close>
  by (fastforce simp: refine_rel_defs nres_rel_def pw_ref_iff)

lemma weaken_SPEC2: \<open>m' \<le> SPEC \<Phi> \<Longrightarrow> m = m' \<Longrightarrow> (\<And>x. \<Phi> x \<Longrightarrow> \<Psi> x) \<Longrightarrow> m \<le> SPEC \<Psi>\<close>
  using weaken_SPEC by auto

method match_spec_trans =
  (match conclusion in \<open>f \<le> SPEC R\<close> for f :: \<open>'a nres\<close> and R :: \<open>'a \<Rightarrow> bool\<close> \<Rightarrow>
    \<open>print_term f; match premises in I: \<open>_ \<Longrightarrow> _ \<Longrightarrow> f' \<le> SPEC R'\<close> for f' :: \<open>'a nres\<close> and
         R' :: \<open>'a \<Rightarrow> bool\<close>
       \<Rightarrow> \<open>print_term f'; rule weaken_SPEC2[of f' R' f R]\<close>\<close>)

lemma bind_rule_complete_RES: \<open>(M \<bind> f \<le> RES \<Phi>) = (M \<le> SPEC (\<lambda>x. f x \<le> RES \<Phi>))\<close>
  by (auto simp: pw_le_iff refine_pw_simps)


subsubsection \<open>More Simplification Theorems\<close>

lemma nofail_Down_nofail: \<open>nofail gS \<Longrightarrow> fS \<le> \<Down> R gS \<Longrightarrow> nofail fS\<close>
  using pw_ref_iff by blast

text \<open>This is the refinement version of @{thm WHILEIT_add_post_condition}.\<close>
lemma WHILEIT_refine_with_post:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes IREF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF:
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x'; f' x' \<le> SPEC I' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "WHILEIT I b f x \<le>\<Down>R (WHILEIT I' b' f' x')"
  apply (subst (2) WHILEIT_add_post_condition)
  apply (rule WHILEIT_refine)
  subgoal using R0 by blast
  subgoal using IREF by blast
  subgoal using COND_REF by blast
  subgoal using STEP_REF by auto
  done


subsection \<open>Some Refinement\<close>

lemma Collect_eq_comp: \<open>{(c, a). a = f c} O {(x, y). P x y} = {(c, y). P (f c) y}\<close>
  by auto

lemma Collect_eq_comp_right:
  \<open>{(x, y). P x y} O {(c, a). a = f c} = {(x, c). \<exists>y. P x y \<and> c = f y} \<close>
  by auto


lemma no_fail_spec_le_RETURN_itself: \<open>nofail f \<Longrightarrow> f \<le> SPEC(\<lambda>x. RETURN x \<le> f)\<close>
  by (metis RES_rule nres_order_simps(21) the_RES_inv)

lemma refine_add_invariants':
  assumes
    \<open>f S \<le> \<Down> {(S, S'). Q' S S' \<and> Q S} gS\<close> and
    \<open>y \<le> \<Down> {((i, S), S'). P i S S'} (f S)\<close> and
    \<open>nofail gS\<close>
  shows \<open>y \<le> \<Down> {((i, S), S'). P i S S' \<and> Q S'} (f S)\<close>
  using assms unfolding pw_le_iff pw_conc_inres pw_conc_nofail
  by force

lemma "weaken_\<Down>": \<open>R' \<subseteq> R \<Longrightarrow> f \<le> \<Down> R' g \<Longrightarrow> f \<le> \<Down> R g\<close>
  by (meson pw_ref_iff subset_eq)

method match_Down =
  (match conclusion in \<open>f \<le> \<Down> R g\<close> for f g R \<Rightarrow>
    \<open>match premises in I: \<open>f \<le> \<Down> R' g\<close> for R'
       \<Rightarrow> \<open>rule "weaken_\<Down>"[OF _ I]\<close>\<close>)

lemma Ball2_split_def: \<open>(\<forall>(x, y) \<in> A. P x y) \<longleftrightarrow> (\<forall>x y. (x, y) \<in> A \<longrightarrow> P x y)\<close>
  by blast

lemma in_pair_collect_simp: "(a,b)\<in>{(a,b). P a b} \<longleftrightarrow> P a b"
  by auto

lemma refine_SPEC_refine_Down:
  \<open>f \<le> SPEC C \<longleftrightarrow> f \<le> \<Down> {(T', T). T = T' \<and> C T'} (SPEC C)\<close>
  apply (rule iffI)
  subgoal
    by (rule SPEC_refine)  auto
  subgoal
    by (metis (no_types, lifting) RETURN_ref_SPECD SPEC_cons_rule dual_order.trans
         in_pair_collect_simp no_fail_spec_le_RETURN_itself nofail_Down_nofail nofail_simps(2))
  done


lemma Down_id_eq: "\<Down> Id a = a"
  by auto

lemma Down_itself_via_SPEC:
  assumes \<open>I \<le> SPEC P\<close> and \<open>\<And>x. P x \<Longrightarrow> (x, x) \<in> R\<close>
  shows \<open>I \<le> \<Down> R I\<close>
  using assms by (meson inres_SPEC pw_ref_I)
lemma RES_ASSERT_moveout:
  "(\<And>a. a \<in> P \<Longrightarrow> Q a) \<Longrightarrow> do {a \<leftarrow> RES P; ASSERT(Q a); (f a)} =
   do {a\<leftarrow> RES P; (f a)}"
  apply (subst dual_order.eq_iff)
  apply (rule conjI)
  subgoal
    by (refine_rcg bind_refine_RES[where R=Id, unfolded Down_id_eq])
      auto
  subgoal
    by (refine_rcg bind_refine_RES[where R=Id, unfolded Down_id_eq])
      auto
  done

lemma bind_if_inverse:
  \<open>do {
    S \<leftarrow> H;
    if b then f S else g S
    } =
    (if b then do {S \<leftarrow> H; f S} else do {S \<leftarrow> H; g S})
  \<close> for H :: \<open>'a nres\<close>
  by auto


lemma bind_cong_nres: \<open>(\<And>x. g x = g' x) \<Longrightarrow> (do {a \<leftarrow> f :: 'a nres;  g a}) =
  (do {a \<leftarrow> f :: 'a nres;  g' a})\<close>
  by auto

lemma case_prod_cong:
  \<open>(\<And>a b. f a b = g a b) \<Longrightarrow> (case x of (a, b) \<Rightarrow> f a b) = (case x of (a, b) \<Rightarrow> g a b)\<close>
  by (cases x) auto

lemma if_replace_cond: \<open>(if b then P b else Q b) = (if b then P True else Q False)\<close>
  by auto


lemma foldli_cong2:
  assumes
    le: \<open>length l = length l'\<close> and
    \<sigma>: \<open>\<sigma> = \<sigma>'\<close> and
    c: \<open>c = c'\<close> and
    H: \<open>\<And>\<sigma> x. x < length l \<Longrightarrow> c' \<sigma> \<Longrightarrow> f (l ! x) \<sigma> = f' (l' ! x) \<sigma>\<close>
  shows \<open>foldli l c f \<sigma> = foldli l' c' f' \<sigma>'\<close>
proof -
  show ?thesis
    using le H unfolding c[symmetric] \<sigma>[symmetric]
  proof (induction l arbitrary: l' \<sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a l l'') note IH=this(1) and le = this(2) and H = this(3)
    show ?case
      using le H[of \<open>Suc _\<close>] H[of 0] IH[of \<open>tl l''\<close> \<open>f' (hd l'') \<sigma>\<close>]
      by (cases l'') auto
  qed
qed

lemma foldli_foldli_list_nth:
  \<open>foldli xs c P a = foldli [0..<length xs] c (\<lambda>i. P (xs ! i)) a\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons x xs) note IH = this(1)
  have 1: \<open>[0..<length (x # xs)] = 0 # [1..<length (x#xs)]\<close>
    by (subst upt_rec)  simp
  have 2: \<open>[1..<length (x#xs)] = map Suc [0..<length xs]\<close>
    by (induction xs) auto
  have AB: \<open>foldli [0..<length (x # xs)] c (\<lambda>i. P ((x # xs) ! i)) a =
      foldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a\<close>
      (is \<open>?A = ?B\<close>)
    unfolding 1 ..
  {
    assume [simp]: \<open>c a\<close>
    have \<open>foldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a =
       foldli [1..<length (x#xs)] c (\<lambda>i. P ((x # xs) ! i)) (P x a)\<close>
      by simp
    also have \<open>\<dots>  = foldli [0..<length xs] c (\<lambda>i. P (xs ! i)) (P x a)\<close>
      unfolding 2
      by (rule foldli_cong2) auto
    finally have \<open>?A = foldli [0..<length xs] c (\<lambda>i. P (xs ! i)) (P x a)\<close>
      using AB
      by simp
  }
  moreover {
    assume [simp]: \<open>\<not>c a\<close>
    have \<open>?B = a\<close>
      by simp
  }
  ultimately show ?case by (auto simp: IH)
qed

lemma RES_RES13_RETURN_RES: \<open>do {
  (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount) \<leftarrow> RES A;
  RES (f M N D Q W vm \<phi> clvls cach lbd outl stats fast_ema slow_ema ccount
      vdom avdom lcount)
} = RES (\<Union>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount)\<in>A. f M N D Q W vm \<phi> clvls cach lbd outl stats fast_ema slow_ema ccount
      vdom avdom lcount)\<close>
  by (force simp:  pw_eq_iff refine_pw_simps uncurry_def)


lemma RES_SPEC_conv: \<open>RES P = SPEC (\<lambda>v. v \<in> P)\<close>
  by auto

lemma add_invar_refineI_P: \<open>A \<le> \<Down> {(x,y). R x y} B \<Longrightarrow> (nofail A \<Longrightarrow>A \<le> SPEC P) \<Longrightarrow>
  A \<le> \<Down> {(x,y). R x y \<and> P x} B\<close>
  using add_invar_refineI[of \<open>\<lambda>_. A\<close> _  _ \<open>\<lambda>_. B\<close> P, where R=\<open>{(x,y). R x y}\<close> and I=P]
  by auto


lemma (in -)WHILEIT_rule_stronger_inv_RES':
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close>
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> and
   \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> RETURN s \<le> \<Down> H (RES \<Phi>)\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> \<Down> H (RES \<Phi>)\<close>
proof -
  have RES_SPEC: \<open>RES \<Phi> = SPEC(\<lambda>s. s \<in> \<Phi>)\<close>
    by auto
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)
  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> \<Down> H (RES \<Phi>)\<close>
    unfolding RES_SPEC conc_fun_SPEC
    apply (rule WHILEIT_rule[OF assms(1)])
    subgoal using assms(2,3) by auto
    subgoal using assms(4) by auto
    subgoal using assms(5) unfolding RES_SPEC conc_fun_SPEC by auto
    done
  finally show ?thesis .
qed

lemma same_in_Id_option_rel:
  \<open>x = x' \<Longrightarrow> (x, x') \<in> \<langle>Id\<rangle>option_rel\<close>
  by auto

definition find_in_list_between :: \<open>('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat option nres\<close> where
  \<open>find_in_list_between P a b C = do {
      (x, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> a \<and> i \<le> length C \<and> i \<le> b \<and> (\<forall>j\<in>{a..<i}. \<not>P (C!j)) \<and>
        (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> P (C ! j) \<and> j < b \<and> j \<ge> a))\<^esup>
        (\<lambda>(found, i). found = None \<and> i < b)
        (\<lambda>(_, i). do {
          ASSERT(i < length C);
          if P (C!i) then RETURN (Some i, i) else RETURN (None, i+1)
        })
        (None, a);
      RETURN x
  }\<close>

lemma find_in_list_between_spec:
  assumes \<open>a \<le> length C\<close> and \<open>b \<le> length C\<close> and \<open>a \<le> b\<close>
  shows
    \<open>find_in_list_between P a b C \<le> SPEC(\<lambda>i.
       (i \<noteq> None \<longrightarrow>  P (C ! the i) \<and> the i \<ge> a \<and> the i < b) \<and>
       (i = None \<longrightarrow> (\<forall>j. j \<ge> a \<longrightarrow> j < b \<longrightarrow> \<not>P (C!j))))\<close>
  unfolding find_in_list_between_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(f, i). Suc (length C) -
    (i + (if f = None then 0 else 1)))\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: less_Suc_eq)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done


lemma nfoldli_cong2:
  assumes
    le: \<open>length l = length l'\<close> and
    \<sigma>: \<open>\<sigma> = \<sigma>'\<close> and
    c: \<open>c = c'\<close> and
    H: \<open>\<And>\<sigma> x. x < length l \<Longrightarrow> c' \<sigma> \<Longrightarrow> f (l ! x) \<sigma> = f' (l' ! x) \<sigma>\<close>
  shows \<open>nfoldli l c f \<sigma> = nfoldli l' c' f' \<sigma>'\<close>
proof -
  show ?thesis
    using le H unfolding c[symmetric] \<sigma>[symmetric]
  proof (induction l arbitrary: l' \<sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a l l'') note IH=this(1) and le = this(2) and H = this(3)
    show ?case
      using le H[of \<open>Suc _\<close>] H[of 0] IH[of \<open>tl l''\<close> \<open>_\<close>]
      by (cases l'')
        (auto intro: bind_cong_nres)
  qed
qed

lemma nfoldli_nfoldli_list_nth:
  \<open>nfoldli xs c P a = nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i)) a\<close>
proof (induction xs arbitrary: a)
  case Nil
  then show ?case by auto
next
  case (Cons x xs) note IH = this(1)
  have 1: \<open>[0..<length (x # xs)] = 0 # [1..<length (x#xs)]\<close>
    by (subst upt_rec)  simp
  have 2: \<open>[1..<length (x#xs)] = map Suc [0..<length xs]\<close>
    by (induction xs) auto
  have AB: \<open>nfoldli [0..<length (x # xs)] c (\<lambda>i. P ((x # xs) ! i)) a =
      nfoldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a\<close>
      (is \<open>?A = ?B\<close>)
    unfolding 1 ..
  {
    assume [simp]: \<open>c a\<close>
    have \<open>nfoldli (0 # [1..<length (x#xs)]) c (\<lambda>i. P ((x # xs) ! i)) a =
       do {
         \<sigma> \<leftarrow> (P x a);
         nfoldli [1..<length (x#xs)] c (\<lambda>i. P ((x # xs) ! i)) \<sigma>
        }\<close>
      by simp
    moreover have \<open>nfoldli [1..<length (x#xs)] c (\<lambda>i. P ((x # xs) ! i)) \<sigma>  =
       nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i)) \<sigma>\<close> for \<sigma>
      unfolding 2
      by (rule nfoldli_cong2) auto
    ultimately have \<open>?A = do {
         \<sigma> \<leftarrow> (P x a);
         nfoldli [0..<length xs] c (\<lambda>i. P (xs ! i))  \<sigma>
        }\<close>
      using AB
      by (auto intro: bind_cong_nres)
  }
  moreover {
    assume [simp]: \<open>\<not>c a\<close>
    have \<open>?B = RETURN a\<close>
      by simp
  }
  ultimately show ?case by (auto simp: IH intro: bind_cong_nres)
qed

(*TODO kill once shared*)
definition "list_mset_rel \<equiv> br mset (\<lambda>_. True)"

lemma
  Nil_list_mset_rel_iff:
    \<open>([], aaa) \<in> list_mset_rel \<longleftrightarrow> aaa = {#}\<close> and
  empty_list_mset_rel_iff:
    \<open>(a, {#}) \<in> list_mset_rel \<longleftrightarrow> a = []\<close>
  by (auto simp: list_mset_rel_def br_def)

definition list_rel_mset_rel where list_rel_mset_rel_internal:
\<open>list_rel_mset_rel \<equiv> \<lambda>R. \<langle>R\<rangle>list_rel O list_mset_rel\<close>

lemma list_rel_mset_rel_def[refine_rel_defs]:
  \<open>\<langle>R\<rangle>list_rel_mset_rel = \<langle>R\<rangle>list_rel O list_mset_rel\<close>
  unfolding relAPP_def list_rel_mset_rel_internal ..

lemma list_rel_mset_rel_imp_same_length: \<open>(a, b) \<in> \<langle>R\<rangle>list_rel_mset_rel \<Longrightarrow> length a = size b\<close>
  by (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def
      dest: list_rel_imp_same_length)

lemma while_upt_while_direct1:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } \<le> do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
  apply (refine_vcg WHILET_refine[where R = \<open>{((l, x'), (i::nat, x::'a)). x= x' \<and> i \<le> b \<and> i \<ge> a \<and>
     l = drop (i-a) [a..<b]}\<close>])
  subgoal by auto
  subgoal by (auto simp: FOREACH_cond_def)
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by auto
  done

lemma while_upt_while_direct2:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } \<ge> do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
  apply (refine_vcg WHILET_refine[where R = \<open>{((i::nat, x::'a), (l, x')). x= x' \<and> i \<le> b \<and> i \<ge> a \<and>
    l = drop (i-a) [a..<b]}\<close>])
  subgoal by auto
  subgoal by (auto simp: FOREACH_cond_def)
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by (auto simp: FOREACH_body_def intro!: bind_refine[OF Id_refine])
  subgoal by auto
  done

lemma while_upt_while_direct:
  "b \<ge> a \<Longrightarrow>
  do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x})
      ([a..<b],\<sigma>);
    RETURN \<sigma>
  } = do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (\<lambda>(i, x). i < b \<and> c x) (\<lambda>(i, x). do {ASSERT (i < b);  \<sigma>'\<leftarrow>f i x; RETURN (i+1,\<sigma>')
}) (a,\<sigma>);
    RETURN \<sigma>
  }"
  using while_upt_while_direct1[of a b] while_upt_while_direct2[of a b]
  unfolding dual_order.eq_iff by fast


lemma while_nfoldli:
  "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l,\<sigma>);
    RETURN \<sigma>
  } \<le> nfoldli l c f \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply (subst WHILET_unfold)
  apply (simp add: FOREACH_cond_def)

  apply (subst WHILET_unfold)
  apply (auto
    simp: FOREACH_cond_def FOREACH_body_def
    intro: bind_mono Refine_Basic.bind_mono(1))
 done

lemma nfoldli_while: "nfoldli l c f \<sigma>
          \<le>
         (WHILE\<^sub>T\<^bsup>I\<^esup>
           (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l, \<sigma>) \<bind>
          (\<lambda>(_, \<sigma>). RETURN \<sigma>))"
proof (induct l arbitrary: \<sigma>)
  case Nil thus ?case by (subst WHILEIT_unfold) (auto simp: FOREACH_cond_def)
next
  case (Cons x ls)
  show ?case
  proof (cases "c \<sigma>")
    case False thus ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def
      by simp
  next
    case [simp]: True
    from Cons show ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply clarsimp
      apply (rule Refine_Basic.bind_mono)
      apply simp_all
      done
  qed
qed

lemma while_eq_nfoldli: "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (\<lambda>x. do {ASSERT (FOREACH_cond c x); FOREACH_body f x}) (l,\<sigma>);
    RETURN \<sigma>
  } = nfoldli l c f \<sigma>"
  apply (rule antisym)
  apply (rule while_nfoldli)
  apply (rule order_trans[OF nfoldli_while[where I="\<lambda>_. True"]])
  apply (simp add: WHILET_def)
  done
lemma RES_RETURN_RES5:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5). RETURN (f T1 T2 T3 T4 T5)) =
    RES ((\<lambda>(a, b, c, d, e). f a b c d e) ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e). f a b c d e\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  by simp

lemma RES_RETURN_RES6:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5, T6). RETURN (f T1 T2 T3 T4 T5 T6)) =
    RES ((\<lambda>(a, b, c, d, e, f'). f a b c d e f') ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e, f'). f a b c d e f'\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  apply (subst (asm)(6) split_prod_bound)
  by simp

lemma RES_RETURN_RES7:
   \<open>SPEC \<Phi> \<bind> (\<lambda>(T1, T2, T3, T4, T5, T6, T7). RETURN (f T1 T2 T3 T4 T5 T6 T7)) =
    RES ((\<lambda>(a, b, c, d, e, f', g). f a b c d e f' g) ` {T. \<Phi> T})\<close>
  using RES_RETURN_RES[of \<open>Collect \<Phi>\<close> \<open>\<lambda>(a, b, c, d, e, f', g). f a b c d e f' g\<close>]
  apply (subst (asm)(2) split_prod_bound)
  apply (subst (asm)(3) split_prod_bound)
  apply (subst (asm)(4) split_prod_bound)
  apply (subst (asm)(5) split_prod_bound)
  apply (subst (asm)(6) split_prod_bound)
  apply (subst (asm)(7) split_prod_bound)
  by simp

lemma RES_RES7_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h). RES (f a b c d e g h)) =
   RES (\<Union>((\<lambda>(a, b, c, d, e, g, h). f a b c d e g h) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def
    split: prod.splits)


lemma RES_RES8_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h, i). RES (f a b c d e g h i)) =
   RES (\<Union>((\<lambda>(a, b, c, d, e, g, h, i). f a b c d e g h i) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def
    split: prod.splits)

lemma RES_RES9_RETURN_RES:
   \<open>RES A \<bind> (\<lambda>(a, b, c, d, e, g, h, i, j). RES (f a b c d e g h i j)) =
   RES (\<Union>((\<lambda>(a, b, c, d, e, g, h, i, j). f a b c d e g h i j) ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps uncurry_def Bex_def
    split: prod.splits)

lemma fold_eq_nfoldli:
  "RETURN (fold f l s) = nfoldli l (\<lambda>_. True) (\<lambda>x s. RETURN (f x s)) s"
  by (induction l arbitrary: s) auto

text \<open>This lemma cannot be moved to \<^theory>\<open>Weidenbach_Book_Base.WB_List_More\<close>, because the syntax
 \<^term>\<open>CARD('a)\<close> does not exist there.\<close>
lemma finite_length_le_CARD:
  assumes \<open>distinct (xs :: 'a :: finite list)\<close>
  shows \<open>length xs \<le> CARD('a)\<close>
proof -
  have \<open>set xs \<subseteq> UNIV\<close>
    by auto
  show ?thesis
    by (metis assms card_ge_UNIV distinct_card le_cases)
qed

end

