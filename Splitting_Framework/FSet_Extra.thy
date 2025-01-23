(* Title:        Formalizing an abstract calculus based on splitting in a modular way
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)

theory FSet_Extra
  imports Main "HOL-Library.FSet"
begin

text \<open>
  This theory contains some additional lemmas regarding sets and finite sets, which were useful 
  in the process of proving some lemmas in \<^file>\<open>Modular_Splitting_Calculi.thy\<close> and
  \<^file>\<open>Modular_Lightweight_Avatar.thy\<close>.
\<close> 

(*<*)
(*! Where should we put this? *)
lemma Union_of_singleton_is_setcompr: \<open>(\<Union> x \<in> A. { y. y = f x \<and> P x }) = { f x | x. x \<in> A \<and> P x }\<close>
  by auto
(*>*)

(* to move to Set of Fset theory? *)

lemma finite_because_singleton: \<open>(\<forall>C1 \<in> S. \<forall>C2 \<in> S. C1 = C2) \<longrightarrow> finite S\<close> for S
  by (metis finite.simps is_singletonI' is_singleton_the_elem)

lemma finite_union_of_finite_is_finite: \<open>finite E \<Longrightarrow> (\<forall>D \<in> E. finite({f C |C. P C \<and> g C = D})) \<Longrightarrow>
                                  finite({f C |C. P C \<and> g C \<in> E})\<close>
proof -
  assume finite_E: \<open>finite E\<close> and
         all_finite: \<open>\<forall>D \<in> E. finite({f C |C. P C \<and> g C = D})\<close>
  have \<open>finite (\<Union>{{f C |C. P C \<and> g C = D} |D. D\<in>E})\<close>
    using finite_E all_finite finite_UN_I
    by (simp add: setcompr_eq_image)
  moreover have \<open>{f C |C. P C \<and> g C \<in> E} \<subseteq> \<Union>{{f C |C. P C \<and> g C = D} |D. D\<in>E}\<close>
    by blast
  ultimately show ?thesis by (meson finite_subset)
qed



(* to move to Fset theory? *)
definition list_of_fset :: "'a fset \<Rightarrow> 'a list" where
  \<open>list_of_fset A = (SOME l. fset_of_list l = A)\<close>

lemma fin_set_fset: "finite A \<Longrightarrow> \<exists>Af. fset Af = A" by (metis finite_list fset_of_list.rep_eq)

lemma fimage_snd_zip_is_snd [simp]:
  \<open>length x = length y \<Longrightarrow> (\<lambda>(x, y). y) |`| fset_of_list (zip x y) = fset_of_list y\<close>
proof -
  assume length_x_eq_length_y: \<open>length x = length y\<close>
  have \<open>(\<lambda>(x, y). y) |`| fset_of_list A = fset_of_list (map (\<lambda>(x, y). y) A)\<close> for A
    by auto
  then show ?thesis
    using length_x_eq_length_y
    by (smt (verit, ccfv_SIG) cond_case_prod_eta map_snd_zip snd_conv)
qed

lemma if_in_ffUnion_then_in_subset: \<open>x |\<in>| ffUnion A \<Longrightarrow> \<exists> a. a |\<in>| A \<and> x |\<in>| a\<close>
  by (induct \<open>A\<close> rule: fset_induct, fastforce+)

lemma fset_ffUnion_subset_iff_all_fsets_subset: \<open>fset (ffUnion A) \<subseteq> B \<longleftrightarrow> fBall A (\<lambda> x. fset x \<subseteq> B)\<close>
proof (intro fBallI subsetI iffI)
  fix a x
  assume ffUnion_A_subset_B: \<open>fset (ffUnion A) \<subseteq> B\<close> and
         a_in_A: \<open>a |\<in>| A\<close> and
         x_in_fset_a: \<open>x \<in> fset a\<close>
  then have \<open>x |\<in>| a\<close>
    by simp
  then have \<open>x |\<in>| ffUnion A\<close>
    by (metis a_in_A ffunion_insert funion_iff set_finsert)
  then show \<open>x \<in> B\<close>
    using ffUnion_A_subset_B by blast
next
  fix x
  assume all_in_A_subset_B: \<open>fBall A (\<lambda> x. fset x \<subseteq> B)\<close> and
         \<open>x \<in> fset (ffUnion A)\<close>
  then have \<open>x |\<in>| ffUnion A\<close>
    by simp
  then obtain a where \<open>a |\<in>| A\<close> and
                      x_in_a: \<open>x |\<in>| a\<close>
    by (meson if_in_ffUnion_then_in_subset)
  then have \<open>fset a \<subseteq> B\<close>
    using all_in_A_subset_B
    by blast
  then show \<open>x \<in> B\<close>
    using x_in_a by blast
qed

lemma fBall_fset_of_list_iff_Ball_set: \<open>fBall (fset_of_list A) P \<longleftrightarrow> Ball (set A) P\<close>
  by (simp add: fset_of_list.rep_eq)

lemma wf_fsubset: \<open>wfP (|\<subset>|)\<close>
proof -
  have \<open>wfP (\<lambda> A B. fcard A < fcard B)\<close>
    by (metis (no_types, lifting) in_measure wfPUNIVI wf_induct wf_measure)
  then show \<open>wfP (|\<subset>|)\<close>
    by (smt (verit, ccfv_threshold) pfsubset_fcard_mono wfPUNIVI wfP_induct)
qed
 
lemma non_zero_fcard_of_non_empty_set: \<open>fcard A > 0 \<longleftrightarrow> A \<noteq> {||}\<close>
  by (metis bot.not_eq_extremum fcard_fempty less_numeral_extra(3) pfsubset_fcard_mono)

lemma fimage_of_non_fempty_is_non_fempty: \<open>A \<noteq> {||} \<Longrightarrow> f |`| A \<noteq> {||}\<close>
  unfolding fimage_is_fempty
  by blast

lemma Union_empty_if_set_empty_or_all_empty:
  \<open>ffUnion A = {||} \<Longrightarrow> A = {||} \<or> fBall A (\<lambda> x. x = {||})\<close>
  by (metis (mono_tags, lifting) ffunion_insert finsert_absorb funion_fempty_right)

lemma fBall_fimage_is_fBall: \<open>fBall (f |`| A) P \<longleftrightarrow> fBall A (\<lambda> x. P (f x))\<close>
  by auto

end