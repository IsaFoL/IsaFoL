theory List_Extra
  imports Main "HOL-Library.Quotient_List"
begin

text \<open>
  This theory contains some extra lemmas that were useful in proving some lemmas in
  \<^file>\<open>Modular_Splitting_Calculus.thy\<close> and \<^file>\<open>Lightweight_Avatar.thy\<close>.
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

(*<*)
(*! All these could belong in the \<open>List\<close> theory, although these definitions lack a few lemmas
 *  which aren't useful in our case.
 *  Note that it would be better to remove calls to the \<open>smt\<close> method as these take a bit long. *)
primrec zip3 :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> ('a \<times> 'b \<times> 'c) list\<close> where
  \<open>zip3 xs ys [] = []\<close>
  | \<open>zip3 xs ys (z # zs) =
  (case xs of [] \<Rightarrow> [] | x # xs \<Rightarrow>
  (case ys of [] \<Rightarrow> [] | y # ys \<Rightarrow> (x, y, z) # zip3 xs ys zs))\<close>

abbreviation map3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list\<close> where
  \<open>map3 f xs ys zs \<equiv> map (\<lambda>(x, y, z). f x y z) (zip3 xs ys zs)\<close> 

fun list_all3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool\<close> where
  \<open>list_all3 p [] [] [] = HOL.True\<close>
| \<open>list_all3 p (x # xs) (y # ys) (z # zs) = (p x y z \<and> list_all3 p xs ys zs)\<close>
| \<open>list_all3 _ _ _ _ = False\<close> 

lemma list_all3_length_eq1: \<open>list_all3 P xs ys zs \<Longrightarrow> length xs = length ys\<close>
  by (induction P xs ys zs rule: list_all3.induct, auto)

lemma list_all3_length_eq2: \<open>list_all3 P xs ys zs \<Longrightarrow> length ys = length zs\<close>
  by (induction P xs ys zs rule: list_all3.induct, auto) 

lemma list_all3_length_eq3: \<open>list_all3 P xs ys zs \<Longrightarrow> length xs = length zs\<close>
  using list_all3_length_eq1 list_all3_length_eq2
  by fastforce 

lemma list_all2_ex_to_ex_list_all3:
  \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys \<longleftrightarrow> (\<exists> zs. list_all3 P xs ys zs)\<close>
proof (intro iffI)
  assume \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys\<close>
  then show \<open>\<exists> zs. list_all3 P xs ys zs\<close>
    by (induct xs ys; metis list_all3.simps(1) list_all3.simps(2))
next
  assume \<open>\<exists> zs. list_all3 P xs ys zs\<close>
  then obtain zs where
    all3_xs_ys_zs: \<open>list_all3 P xs ys zs\<close> 
    by blast
  then show \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys\<close>
    using all3_xs_ys_zs
    by (induction P xs ys zs rule: list_all3.induct, auto)
qed 

lemma list_all3_conj_distrib: \<open>list_all3 (\<lambda> x y z. P x y z \<and> Q x y z) xs ys zs \<longleftrightarrow>
  list_all3 P xs ys zs \<and> list_all3 Q xs ys zs\<close>
  by (induction \<open>\<lambda> x y z. P x y z \<and> Q x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all3_conv_list_all_3: \<open>list_all3 (\<lambda> x y z. P z) xs ys zs \<Longrightarrow> list_all P zs\<close>
proof -
  assume \<open>list_all3 (\<lambda> x y z. P z) xs ys zs\<close> (is \<open>list_all3 ?P xs ys zs\<close>)
  then show \<open>list_all P zs\<close> 
    by (induction ?P xs ys zs rule: list_all3.induct, auto)
qed

lemma list_all3_reorder:
  \<open>list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> x z y. P x y z) xs zs ys\<close>
  by (induction \<open>\<lambda> x y z. P x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all3_reorder2:
  \<open>list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> y z x. P x y z) ys zs xs\<close>
  by (induction \<open>\<lambda> x y z. P x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all2_conj_distrib:
  \<open>list_all2 (\<lambda> x y. P x y \<and> Q x y) A B \<longleftrightarrow> list_all2 P A B \<and> list_all2 Q A B\<close>
  by (smt (verit, ccfv_SIG) list_all2_conv_all_nth)

(* This lemma depends on "HOL-Library.Quotient_List" in its proof. *)
lemma list_all_bex_ex_list_all2_conv:
  \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs \<longleftrightarrow> (\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys')\<close>
proof (intro iffI)
  assume \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs\<close>
  then have \<open>list.list_all (\<lambda> x. \<exists> y. y \<in> ys \<and> P x y) xs\<close>
    by meson 
  then have \<open>\<exists> ys'. list_all2 (\<lambda> x y. y \<in> ys \<and> P x y) xs ys'\<close>
    by (induct xs, auto)
  then have \<open>\<exists> ys'. list_all2 (\<lambda> x y. y \<in> ys) xs ys' \<and> list_all2 (\<lambda> x y. P x y) xs ys'\<close>
    using list_all2_conj_distrib
    by blast
  then have \<open>\<exists> ys'. list.list_all (\<lambda> y. y \<in> ys) ys' \<and> list_all2 P xs ys'\<close>
    by (metis list_all2_conv_all_nth list_all_length)
  then show \<open>\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys'\<close>
    by (metis list.pred_set subsetI)
next
  assume \<open>\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys'\<close>
  then show \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs\<close>
    (* /!\ A bit slow /!\ *)
    by (smt (verit, del_insts) list.pred_set list_all2_find_element subsetD) 
qed 
(*>*)

end