theory Utils
  imports Main
begin


lemma foldr_inject[simp]:
  assumes
    f_inject: "\<And>w x y z. f w x = f y z \<longleftrightarrow> w = y \<and> x = z" and
    f_distinct_a: "\<And>x y. f x y \<noteq> a" and
    f_distinct_b: "\<And>x y. f x y \<noteq> b"
  shows "foldr f xs a = foldr f ys b \<longleftrightarrow> xs = ys \<and> a = b"   
  using f_distinct_a f_distinct_b f_inject
  by (induction xs ys arbitrary: a b rule: List.list_induct2') auto

thm foldr_inject List.foldr_inject

declare fold_inject[simp]

lemma
  fixes z :: "'a" and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
  assumes
    f_inject: "\<And>w x y z. f w x = f y z \<Longrightarrow> w = y \<and> x = z" and
    f_distinct_a: "\<And>x y. f x y \<noteq> a" and
    f_distinct_b: "\<And>x y. f x y \<noteq> b" and
    "foldl f a xs = foldl f b ys"
  shows "a = b" and "xs = ys"
  unfolding atomize_conj
proof -
  show  "a = b \<and> xs = ys"
    using \<open>foldl f a xs = foldl f b ys\<close> f_distinct_a f_distinct_b
  proof (induction xs ys arbitrary: a b rule: List.rev_induct2)
    case (3 y ys)
    hence False
      by (metis foldl_Cons foldl_Nil foldl_append)
    thus ?case ..
  next
    case (4 x xs y ys)
    have "f (foldl f a xs) x = f (foldl f b ys) y"
      using "4.prems"(1) by simp
    hence "foldl f a xs = foldl f b ys" and "x = y"
      using f_inject by simp_all
    hence "a = b \<and> xs = ys"
      using "4.prems"(2,3) "4.IH" by metis
    thus ?case
      using \<open>x = y\<close> by metis
  qed simp_all
qed

lemma inj_foldl:
  fixes z :: "'a" and f :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
  assumes f_inject: "\<And>w x y z. f w x = f y z \<Longrightarrow> w = y \<and> x = z" and f_neq_z: "\<And>x y. f x y \<noteq> z"
  shows "inj (foldl f z)"
proof (rule injI)
  fix xs ys :: "'b list"
  assume "foldl f z xs = foldl f z ys"
  thus "xs = ys"
    using f_neq_z
  proof (induction xs ys arbitrary: z rule: List.rev_induct2)
    case (3 y ys)
    hence False
      by (metis foldl_Cons foldl_Nil foldl_append)
    thus ?case ..
  next
    case (4 x xs y ys)
    have "f (foldl f z xs) x = f (foldl f z ys) y"
      using "4.prems"(1) by simp
    hence "foldl f z xs = foldl f z ys" and "x = y"
      using f_inject by simp_all
    hence "xs = ys"
      using "4.prems"(2) "4.IH" by metis
    thus ?case
      using \<open>x = y\<close> by metis
  qed simp_all
qed

end