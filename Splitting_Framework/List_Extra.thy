theory List_Extra
  imports Main
begin

text \<open>
  This theory contains some extra lemmas that were useful in proving some lemmas in
  \<^file>\<open>Splitting_Calculi.thy\<close> and \<^file>\<open>Splitting_Without_Backtracking.thy\<close>.
\<close>

lemma map2_first_is_first [simp]: \<open>length x = length y \<Longrightarrow> map2 (\<lambda> x y. x) x y = x\<close>
  by (metis fst_def map_eq_conv map_fst_zip)

lemma map2_second_is_second [simp]: \<open>length A = length B \<Longrightarrow> map2 (\<lambda> x y. y) A B = B\<close>
  by (metis map_eq_conv map_snd_zip snd_def)

lemma list_all_exists_is_exists_list_all2:
  assumes \<open>list_all (\<lambda> x. \<exists> y. P x y) xs\<close>
  shows \<open>\<exists> ys. list_all2 P xs ys\<close>
  using assms
  by (induct xs, auto)

lemma ball_set_f_to_ball_set_map: \<open>(\<forall> x \<in> set A. P (f x)) \<longleftrightarrow> (\<forall> x \<in> set (map f A). P x)\<close>
  by simp

lemma list_all_ex_to_ex_list_all2:
  \<open>list_all (\<lambda> x. \<exists> y. P x y) A \<longleftrightarrow> (\<exists> ys. length A = length ys \<and> list_all2 (\<lambda> x y. P x y) A ys)\<close>
  by (metis list_all2_conv_all_nth list_all_exists_is_exists_list_all2 list_all_length)

lemma list_all2_to_map:
  assumes lengths_eq: \<open>length A = length B\<close>
  shows \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all P (map2 f A B)\<close>
proof -
  have \<open>list_all2 (\<lambda> x y. P (f x y)) A B \<longleftrightarrow> list_all (\<lambda> (x, y). P (f x y)) (zip A B)\<close>
    by (simp add: lengths_eq list_all2_iff list_all_iff)
  also have \<open>... \<longleftrightarrow> list_all (\<lambda> x. P x) (map2 f A B)\<close>
    by (simp add: case_prod_beta list_all_iff)
  finally show ?thesis .
qed

end