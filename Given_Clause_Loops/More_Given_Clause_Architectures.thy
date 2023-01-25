(* Title:        More Lemmas about Given Clause Architectures 
   Authors:      Qi Qiu, 2021
                 Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>More Lemmas about Given Clause Architectures\<close>

text \<open>This section proves lemmas about Tourret's formalization of the abstract
given clause procedures @{text GC} and @{text LGC}.\<close>

theory More_Given_Clause_Architectures
  imports Saturation_Framework.Given_Clause_Architectures
begin


subsection \<open>Inference System\<close>

context inference_system
begin

lemma Inf_from_empty: "Inf_from {} = {\<iota> \<in> Inf. prems_of \<iota> = []}"
  using Inf_from_def by auto

end


subsection \<open>Given Clause Procedure Basis\<close>

context given_clause_basis
begin

lemma no_labels_entails_mono_left: "M \<subseteq> N \<Longrightarrow> M \<Turnstile>\<inter>\<G> P \<Longrightarrow> N \<Turnstile>\<inter>\<G> P"
  using no_labels.entails_trans no_labels.subset_entailed by blast

lemma no_labels_Red_F_imp_Red_F:
  assumes "C \<in> no_labels.Red_F (fst ` \<N>)"
  shows "(C, l) \<in> Red_F \<N> "
proof -
  let ?N = "fst ` \<N>"
  have c_in_red_f_g_q: "\<forall>q \<in> Q. C \<in> no_labels.Red_F_\<G>_q q ?N"
    using no_labels.Red_F_def assms by auto
  moreover have redfgq_eq_redfeq:
    "\<forall>q \<in> Q. no_labels.Red_F_\<G>_q q ?N = no_labels.Red_F_\<G>_empty_q q ?N"
    using no_labels.Red_F_\<G>_empty_q_def no_labels.Red_F_\<G>_q_def by auto
  ultimately have "\<forall>q \<in> Q. C \<in> no_labels.Red_F_\<G>_empty_q q ?N"
    by simp
  then have "\<forall>q \<in> Q. \<G>_F_q q C \<subseteq> Red_F_q q (no_labels.\<G>_Fset_q q ?N)"
    using redfgq_eq_redfeq no_labels.Red_F_\<G>_q_def by auto
  moreover have "\<forall>q \<in> Q. \<G>_F_L_q q (C, l) = \<G>_F_q q C"
    by simp
  moreover have "\<forall>q \<in> Q. no_labels.\<G>_Fset_q q ?N = \<G>_Fset_q q \<N>"
    by auto
  ultimately have "\<forall>q \<in> Q. \<G>_F_L_q q (C, l) \<subseteq> Red_F_q q (\<G>_Fset_L_q q \<N>)"
    by auto
  then have "\<forall>q \<in> Q. (C, l) \<in> Red_F_\<G>_q q \<N>"
    using c_in_red_f_g_q Red_F_\<G>_q_def by force
  then show "(C, l) \<in> Red_F \<N>"
    using Red_F_def by simp
qed

lemma succ_F_imp_Red_F:
  assumes
    "C' \<in> fst ` \<N>" and
    "C' \<prec>\<cdot> C"
  shows "(C, l) \<in> Red_F \<N>"
proof -
  have "\<exists>l'. (C', l') \<in> \<N>"
    using assms by auto
  then obtain l' where
    c'_l'_in: "(C', l') \<in> \<N>"
    by auto
  then have c'_l'_ls_c_l: "(C', l') \<sqsubset> (C, l)"
    using assms Prec_FL_def by simp
  moreover have g_f_q_included: "\<forall>q \<in> Q. \<G>_F_q q C \<subseteq>  \<G>_F_q q C'"
    using assms prec_F_grounding by simp
  ultimately have "\<forall>q \<in> Q. \<G>_F_L_q q (C, l) \<subseteq> \<G>_F_L_q q (C, l)"
    by auto
  then have "\<forall>q \<in> Q. (C, l) \<in> Red_F_\<G>_q q \<N>"
    using c'_l'_in c'_l'_ls_c_l g_f_q_included Red_F_\<G>_q_def by fastforce
  thus " (C, l) \<in> Red_F \<N> "
    using Red_F_def by auto
qed

lemma succ_L_imp_Red_F:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<preceq>\<cdot> C" and
    "l' \<sqsubset>L l"
  shows "(C, l) \<in> Red_F \<N>"
proof -
  have c'_l'_ls_c_l: "(C', l') \<sqsubset> (C, l)"
    using Prec_FL_def assms by auto
  have c'_le_c: "C' \<preceq>\<cdot> C"
    using assms by simp
  then show "(C, l) \<in> Red_F \<N>"
  proof
    assume c'_ls_c: " C' \<prec>\<cdot> C "
    have "C' \<in> fst ` \<N>"
      by (metis assms(1) eq_fst_iff rev_image_eqI)
     then show ?thesis
      using c'_ls_c succ_F_imp_Red_F by blast
  next
    assume c'_eq_c: " C' \<doteq> C "
    have c_eq_c': "C \<doteq> C'"
      using c'_eq_c equiv_equiv_F equivp_symp by force
    have "\<forall>q \<in> Q. \<G>_F_q q C' = \<G>_F_q q C"
      using c'_eq_c c_eq_c' equiv_F_grounding subset_antisym by auto
    then have "\<forall>q \<in> Q. \<G>_F_L_q q (C, l) = \<G>_F_L_q q (C', l')" by auto
    then have "\<forall>q \<in> Q. (C, l) \<in> Red_F_\<G>_q q \<N>"
      using assms(1) c'_l'_ls_c_l Red_F_\<G>_q_def by auto
    then show ?thesis
      using Red_F_def by auto
  qed
qed

lemma prj_fl_set_to_f_set_distr_union [simp]: "fst ` (\<M> \<union> \<N>) = fst ` \<M> \<union> fst ` \<N>"
  by (rule Set.image_Un)

lemma prj_labeledN_eq_N [simp]: "fst ` {(C, l) | C. C \<in> N} = N"
proof -
  let ?\<N> = "{(C, l) | C. C \<in> N}"
  have "fst` ?\<N> = N"
    proof
      show "fst` ?\<N> \<subseteq> N"
        by fastforce
    next
      show "fst` ?\<N> \<supseteq> N"
      proof
        fix x
        assume "x \<in> N"
        then have "(x, l) \<in> ?\<N>"
          by auto
        then show "x \<in> fst` ?\<N>"
          by force
      qed
    qed
    then show "fst` ?\<N> = N"
      by simp
qed

end


subsection \<open>Given Clause Procedure\<close>

context given_clause
begin

lemma remove_redundant:
  assumes "(C, l) \<in> Red_F \<N>"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have "{(C, l)} \<subseteq> Red_F (\<N> \<union> {})"
    using assms by simp
  moreover have "active_subset {} = {}"
    using active_subset_def by simp
  ultimately show "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
    by (metis process sup_bot_right)
qed

lemma remove_redundant_no_label:
  assumes " C \<in> no_labels.Red_F (fst ` \<N>)"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have "(C, l) \<in> Red_F \<N>"
    using no_labels_Red_F_imp_Red_F assms by simp
  then show ?thesis
    using remove_redundant by auto
qed

lemma add_inactive:
  assumes "l \<noteq> active"
  shows "\<N> \<leadsto>GC \<N> \<union> {(C, l)}"
proof -
  have active_subset_C_l: "active_subset {(C, l)} = {}"
    using active_subset_def assms by simp
  also have "{} \<subseteq> Red_F (\<N> \<union> {(C, l)})"
    by simp
  finally show "\<N> \<leadsto>GC \<N> \<union> {(C, l)}"
    by (metis active_subset_C_l process sup_bot.right_neutral)
qed

lemma remove_succ_F:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<prec>\<cdot> C"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have "C' \<in> fst ` \<N>"
    by (metis assms(1) fst_conv rev_image_eqI)
  then have "{(C, l)} \<subseteq> Red_F (\<N>)"
    using assms succ_F_imp_Red_F by auto
  then show ?thesis
    using remove_redundant by simp
qed

lemma remove_succ_L:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<preceq>\<cdot> C" and
    "l' \<sqsubset>L l"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have "(C, l) \<in> Red_F \<N>"
    using assms succ_L_imp_Red_F by auto
  then show "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
    using remove_redundant by auto
qed

lemma relabel_inactive:
  assumes
    "l' \<sqsubset>L l" and
    "l' \<noteq> active"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N> \<union> {(C, l')}"
proof -
  have active_subset_c_l': "active_subset {(C, l')} = {}"
    using active_subset_def assms by auto

  have "C \<doteq> C "
    by (simp add: equiv_equiv_F equivp_reflp)
  moreover have "(C, l') \<in> \<N> \<union> {(C, l')} "
    by auto
  ultimately have "(C, l) \<in> Red_F (\<N> \<union> {(C, l')})"
    using assms succ_L_imp_Red_F[of _ _ "\<N> \<union> {(C, l')}"] by auto
  then have "{(C, l)} \<subseteq> Red_F (\<N> \<union> {(C, l')})"
    by auto

  then show "\<N> \<union> {(C, l)} \<leadsto>GC \<N> \<union> {(C, l')}"
    using active_subset_c_l' process[of _ _ "{(C, l)}" _ "{(C, l')}"] by auto
qed

end


subsection \<open>Lazy Given Clause Procedure\<close>

context lazy_given_clause
begin

lemma remove_redundant:
  assumes "(C, l) \<in> Red_F \<N>"
  shows "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
proof -
  have "{(C, l)} \<subseteq> Red_F \<N>"
    using assms by simp
  moreover have "active_subset {} = {}"
    using active_subset_def by simp
  ultimately show "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
    by (metis process sup_bot_right)
qed

lemma remove_redundant_no_label:
  assumes "C \<in> no_labels.Red_F (fst ` \<N>)"
  shows "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
proof -
  have "(C, l) \<in> Red_F \<N>"
    using no_labels_Red_F_imp_Red_F assms by simp
  then show "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
    using remove_redundant by auto
qed

lemma add_inactive:
  assumes "l \<noteq> active"
  shows "(T, \<N>) \<leadsto>LGC (T, \<N> \<union> {(C, l)})"
proof -
  have active_subset_C_l: "active_subset {(C, l)} = {}"
    using active_subset_def assms by simp
  also have "{} \<subseteq> Red_F (\<N> \<union> {(C, l)})"
    by simp
  finally show "(T, \<N>) \<leadsto>LGC (T, \<N> \<union> {(C, l)})"
    by (metis active_subset_C_l process sup_bot.right_neutral)
qed

lemma remove_succ_F:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<prec>\<cdot> C"
  shows "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
proof -
  have "C' \<in> fst ` \<N>"
    by (metis assms(1) fst_conv rev_image_eqI)
  then have "{(C, l)} \<subseteq> Red_F (\<N>)"
    using assms succ_F_imp_Red_F by auto
  then show ?thesis
    using remove_redundant by simp
qed

lemma remove_succ_L:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<preceq>\<cdot> C" and
    "l' \<sqsubset>L l"
  shows "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
proof -
  have "(C, l) \<in> Red_F \<N>"
    using assms succ_L_imp_Red_F by auto
  then show "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N>)"
    using remove_redundant by auto
qed

lemma relabel_inactive:
  assumes
    "l' \<sqsubset>L l" and
    "l' \<noteq> active"
  shows "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N> \<union> {(C, l')})"
proof -
  have active_subset_c_l': "active_subset {(C, l')} = {}"
    using active_subset_def assms by auto

  have "C \<doteq> C "
    by (simp add: equiv_equiv_F equivp_reflp)
  moreover have "(C, l') \<in> \<N> \<union> {(C, l')} "
    by auto
  ultimately have "(C, l) \<in> Red_F (\<N> \<union> {(C, l')})"
    using assms succ_L_imp_Red_F[of _ _ "\<N> \<union> {(C, l')}"] by auto
  then have "{(C, l)} \<subseteq> Red_F (\<N> \<union> {(C, l')})"
    by auto

  then show "(T, \<N> \<union> {(C, l)}) \<leadsto>LGC (T, \<N> \<union> {(C, l')})"
    using active_subset_c_l' process[of _ _ "{(C, l)}" _ "{(C, l')}"] by auto
qed

end

end
