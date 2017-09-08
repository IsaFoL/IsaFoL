theory Map2 imports Main begin

abbreviation image2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b) set \<Rightarrow> 'c set" where
  "image2 f s \<equiv> (case_prod f) ` s"

(* Definition is from "$AFP/Jinja/DFA/Listn.thy" *)
definition map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
  "map2 f = (\<lambda>xs ys. map (case_prod f) (zip xs ys))"

lemma map2_length[simp]: "length (map2 f as bs) = min (length as) (length bs)"
  unfolding map2_def by auto

lemma map2_empty_l[simp]: "map2 f [] ys = []"
  unfolding map2_def by auto

lemma map2_empty_r[simp]: "map2 f xs [] = []"
  unfolding map2_def by auto

lemma map2_empty_iff[simp]: "(map2 f xs ys = []) \<longleftrightarrow> (xs = [] \<or> ys = [])"
  unfolding map2_def
  by (metis list.exhaust list.simps(3) list.simps(9) map2_def map2_empty_l map2_empty_r zip_Cons_Cons)

lemma image_map2: "length t = length s \<Longrightarrow>
         g ` set (map2 f t s) = set (map2 (\<lambda>a b. g (f a b)) t s)"
  unfolding map2_def by (induction t arbitrary: s) auto

lemma inj_map2[iff]: "inj (map2 f) = inj f" oops

lemma map2_nth[simp]: "length t = length s \<Longrightarrow> i < length s \<Longrightarrow> (map2 f s t) ! i = f (s!i) (t!i)"
  unfolding map2_def by (induction t arbitrary: s) auto

lemma map2_tl: "length t = length s \<Longrightarrow> (map2 f (tl t) (tl s)) = tl (map2 f (t) (s))"
  unfolding map2_def apply (induction t arbitrary: s)
   apply auto
  by (smt Suc_length_conv list.sel(3) list.simps(9) zip_Cons_Cons)

lemma map2_Cons[simp]: "map2 f (x # xs) (y # ys) = f x y # map2 f xs ys"
  unfolding map2_def
  by auto

lemma set_map2_ex:
  assumes "length t = length s"
  shows "set (map2 f s t) = {x. \<exists>i<length t. x = f (s ! i) (t ! i)}"
proof (rule; rule)
  fix x
  assume "x \<in> set (map2 f s t)"
  then obtain i where i_p: "i < length (map2 f s t) \<and> x = ((map2 f s t) ! i)"
    by (metis in_set_conv_nth)
  from i_p have "i < length t"
    by auto
  moreover
  from this i_p have "x = f (s ! i) (t ! i)"
    using map2_nth assms by auto
  ultimately
  show "x \<in> {x. \<exists>i<length t. x = f (s ! i) (t ! i)}"
    using assms by auto
next
  fix x
  assume "x \<in> {x. \<exists>i<length t. x = f (s ! i) (t ! i)}"
  then obtain i where i_p: "i<length t \<and> x = f (s ! i) (t ! i)"
    by auto
  then have "i < length (map2 f s t)"
    using assms by auto
  moreover
  from i_p have "x = ((map2 f s t) ! i)"
    using map2_nth assms by auto
  ultimately
  show "x \<in> set (map2 f s t)"
    by (metis in_set_conv_nth)
qed

end
