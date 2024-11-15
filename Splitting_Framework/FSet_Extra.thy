theory FSet_Extra
  imports Main "HOL-Library.FSet"
begin

text \<open>
  This theory contains some additional lemmas regarding finite sets, which were useful in the process
  of proving some lemmas in \<^file>\<open>Splitting_Calculi.thy\<close> and \<^file>\<open>Splitting_Without_Backtracking.thy\<close>.
\<close> 

(* to move to Fset theory? *)
definition list_of_fset :: "'a fset \<Rightarrow> 'a list" where
  \<open>list_of_fset A = (SOME l. fset_of_list l = A)\<close>

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