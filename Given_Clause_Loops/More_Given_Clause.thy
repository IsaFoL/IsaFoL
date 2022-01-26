(* Title:        More Given Clause Lemmas
   Authors:      Qi Qiu, 2021
                 Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>More Given Clause Lemmas\<close>

theory More_Given_Clause
  imports
    More_Given_Clause_Basis
    Saturation_Framework.Given_Clause_Architectures
begin

context given_clause
begin

lemma P0:
  assumes "(C, l) \<in> Red_F \<N>"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have "{(C, l)} \<subseteq> Red_F (\<N> \<union> \<emptyset>)"
    using assms by simp
  moreover have "active_subset \<emptyset> = \<emptyset>"
    using active_subset_def by simp
  ultimately show "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
    by (metis process sup_bot_right)
qed

lemma P1:
  assumes " C \<in> no_labels.Red_F (fst ` \<N>)"
  shows "\<N> \<union> {(C, l::'l)} \<leadsto>GC \<N>"
proof -
  have "(C, l) \<in> Red_F \<N>"
    using lemma59point1 assms by simp
  then show "\<N> \<union> {(C, l::'l)} \<leadsto>GC \<N>"
    using P0 by auto
qed

lemma P2:
  assumes "l \<noteq> active"
  shows "\<N> \<leadsto>GC \<N> \<union> {(C, l)}"
proof -
  have active_subset_C_l: "active_subset {(C, l)} = \<emptyset>"
    using active_subset_def assms by simp
  also have "\<emptyset> \<subseteq> Red_F (\<N> \<union> {(C, l)})"
    by simp
  finally show "\<N> \<leadsto>GC \<N> \<union> {(C, l)}"
    by (metis active_subset_C_l process sup_bot.right_neutral)
qed

lemma P3:
  assumes
    "(C', l') \<in> \<N>" and
    "C' \<prec>\<cdot> C"
  shows " \<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have " C' \<in> fst ` \<N> "
    by (metis assms(1) fst_conv rev_image_eqI)
  then have "{(C, l)} \<subseteq> Red_F (\<N>)"
    using assms lemma59point2 by auto
  then show ?thesis
    using P0 by simp
qed

lemma P4:
  assumes
    "(C', l') \<in> \<N>" and
    "l' \<sqsubset>L l" and
    "C' \<preceq>\<cdot> C"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
proof -
  have " (C, l) \<in> Red_F \<N> "
    using assms lemma59point3 by auto
  then show "\<N> \<union> {(C, l)} \<leadsto>GC \<N>"
    using P0 by auto
qed

lemma P5:
  assumes
    "l' \<sqsubset>L l" and
    "l' \<noteq> active"
  shows "\<N> \<union> {(C, l)} \<leadsto>GC \<N> \<union> {(C, l')}"
proof -
  have active_subset_c_l': "active_subset {(C, l')} = \<emptyset>"
    using active_subset_def assms by auto

  have "C \<doteq> C "
    by (simp add: equiv_equiv_F equivp_reflp)
  moreover have "(C, l') \<in> \<N> \<union> {(C, l')} "
    by auto
  ultimately have "(C, l) \<in> Red_F (\<N> \<union> {(C, l')})"
    using assms lemma59point3[of _ _ "\<N> \<union> {(C, l')}"] by auto
  then have "{(C, l)} \<subseteq> Red_F (\<N> \<union> {(C, l')})"
    by auto

  then show "\<N> \<union> {(C, l)} \<leadsto>GC \<N> \<union> {(C, l')}"
    using active_subset_c_l' process[of _ _ "{(C, l)}" _ "{(C, l')}"] by auto
qed

end

end
