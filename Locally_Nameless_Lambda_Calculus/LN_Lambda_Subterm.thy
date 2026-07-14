theory LN_Lambda_Subterm
  imports LN_Lambda_Term
begin

primrec subterms where
  "subterms (Const c \<tau>s ts) = {#Const c \<tau>s ts#}" |
  "subterms (Free x) = {#Free x#}" |
  "subterms (Bound n) = {#Bound n#}" |
  "subterms (App t\<^sub>1 t\<^sub>2) = add_mset (App t\<^sub>1 t\<^sub>2) (subterms t\<^sub>1 + subterms t\<^sub>2)" |
  "subterms (Abs \<tau> t) = add_mset (Abs \<tau> t) (subterms t)"

fun strip_comb where
  "strip_comb xs (App f x) = strip_comb (x # xs) f" |
  "strip_comb xs f = (f, xs)"

abbreviation strip_comb' where
  "strip_comb' \<equiv> strip_comb []"

lemma "size (fst (strip_comb ts t)) \<le> size t"
proof (induction t arbitrary: ts)
  case (App t1 t2)
  have "size (fst (strip_comb (t2 # ts) t1)) \<le> Suc (size t1 + size t2)"
    using App.IH(1)[of "t2 # ts"] by presburger
  then show ?case
    by simp
qed simp_all

lemma snd_strip_comb_lt:
  assumes "x \<in> set (snd (strip_comb ts t))"
  shows "size x < size t \<or> x \<in> set ts"
  using assms
proof (induction t arbitrary: ts)
  case (App t1 t2)
  then show ?case
    by fastforce
qed simp_all

lemma snd_strip_comb_lt':
  assumes "strip_comb ts t = (f, xs)"
  assumes "x \<in> set xs"
  shows "size x < size t \<or> x \<in> set ts"
  using assms
proof (induction t arbitrary: ts)
  case (App t1 t2)
  then show ?case
    by fastforce
qed simp_all

lemma snd_strip_comb'_lt:
  assumes "x \<in> set (snd (strip_comb' t))"
  shows "size x < size t"
  using assms snd_strip_comb_lt[of x "[]" t]
  by simp

lemma FOO:
  "(f, xs) = strip_comb [t\<^sub>2] t\<^sub>1 \<Longrightarrow> (i, x) \<in> set (zip [0..<length xs] xs) \<Longrightarrow>
    size x < Suc (size t\<^sub>1 + size t\<^sub>2)"
proof (induction t\<^sub>1 arbitrary: f xs)
  case (App t\<^sub>11 t\<^sub>12)
  have "x \<in> set xs"
    by (meson App.prems(2) in_set_zipE)
  have "size x < size (App t\<^sub>11 t\<^sub>12) \<or> x \<in> set [t\<^sub>2]"
    using App.prems(1)
    using snd_strip_comb_lt'[OF _ \<open>x \<in> set xs\<close>, of "[t\<^sub>2]" "App t\<^sub>11 t\<^sub>12" f]
    by metis
  then show ?case
    by auto
qed simp_all

inductive is_subterm_of :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  refl: "is_subterm_of t t" |
  Const: "is_subterm_of s (Const c \<tau>s ts)"
    if "\<exists>t \<in> set ts. is_subterm_of s t" |
  Abs: "is_subterm_of s (Abs \<tau> t)"
    if "is_subterm_of s t" |
  App: "is_subterm_of s (App t\<^sub>1 t\<^sub>2)"
    if "is_subterm_of s t\<^sub>1 \<or> is_subterm_of s t\<^sub>2"

definition is_proper_subterm_of :: "('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> ('\<tau>, '\<Sigma>, '\<V>) preterm \<Rightarrow> bool" where
  "is_proper_subterm_of s t \<longleftrightarrow> is_subterm_of s t \<and> s \<noteq> t"

lemma is_subterm_of_trans:
  assumes "is_subterm_of t\<^sub>1 t\<^sub>2" and "is_subterm_of t\<^sub>2 t\<^sub>3"
  shows "is_subterm_of t\<^sub>1 t\<^sub>3"
  using assms(2,1)
proof (induction t\<^sub>2 t\<^sub>3 arbitrary: t\<^sub>1 rule: is_subterm_of.induct)
  case (refl t)
  then show ?case by assumption
next
  case (Const ts s c \<tau>s)
  then show ?case
    by (metis is_subterm_of.Const)
next
  case (Abs s t \<tau>)
  then show ?case
    by (metis is_subterm_of.Abs)
next
  case (App s t\<^sub>1' t\<^sub>2')
  then show ?case
    by (metis is_subterm_of.App)
qed

lemma size_lt_or_eq_if_is_subterm_of:
  "is_subterm_of s t \<Longrightarrow> s = t \<or> size s < size t"
proof (induction s t rule: is_subterm_of.induct)
  case (refl t)
  then show ?case by simp
next
  case (Const ts s c \<tau>s)
  then obtain t where "t \<in> set ts" and "size s \<le> size t"
    by fastforce
  hence "size s \<le> size_list size ts"
    using size_list_estimation' by fast
  then show ?case
    by simp
next
  case (Abs s \<tau> t)
  then show ?case by auto
next
  case (App s t\<^sub>1 t\<^sub>2)
  then show ?case by auto
qed

lemma is_subterm_of_antisym:
  fixes t\<^sub>1 t\<^sub>2 :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  shows "is_subterm_of t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_subterm_of t\<^sub>2 t\<^sub>1 \<Longrightarrow> t\<^sub>1 = t\<^sub>2"
  using size_lt_or_eq_if_is_subterm_of[of t\<^sub>1 t\<^sub>2] size_lt_or_eq_if_is_subterm_of[of t\<^sub>2 t\<^sub>1]
  by auto

text \<open>The following interpretation has the side effect of registering the partial order so the
"order" method can use it.\<close>

global_interpretation is_subterm_of: order is_subterm_of is_proper_subterm_of
proof unfold_locales
  show "\<And>x y. is_subterm_of x y \<Longrightarrow> is_subterm_of y x \<Longrightarrow> x = y"
    using is_subterm_of_antisym .
next
  show "\<And>x. is_subterm_of x x"
    using is_subterm_of.refl .
next
  show "\<And>x y z. is_subterm_of x y \<Longrightarrow> is_subterm_of y z \<Longrightarrow> is_subterm_of x z"
    using is_subterm_of_trans .
next
  show "\<And>x y. is_proper_subterm_of x y = (is_subterm_of x y \<and> \<not> is_subterm_of y x)"
    by (metis is_proper_subterm_of_def is_subterm_of_antisym)
qed

hide_fact is_subterm_of.refl is_subterm_of_antisym is_subterm_of_trans

text \<open>Prefer the standard names @{thm is_subterm_of.order_antisym is_subterm_of.order_trans
  is_subterm_of.order_refl}.\<close>

lemma wfp_is_proper_subterm_of: "wfp is_proper_subterm_of"
proof (rule wfp_if_convertible_to_nat)
  fix x y :: "('\<tau>, '\<Sigma>, '\<V>) preterm"
  assume "is_proper_subterm_of x y"
  thus "size x < size y"
    using size_lt_or_eq_if_is_subterm_of
    by (auto simp: is_proper_subterm_of_def)
qed

lemma is_subterm_of_fst_strip_comb: "is_subterm_of (fst (strip_comb xs t)) t"
  by (induction t rule: strip_comb.induct) (simp_all add: is_subterm_of.App)

lemma snd_strip_comb_in_list_or_substerm:
  "s \<in> set (snd (strip_comb xs t)) \<Longrightarrow> s \<in> set xs \<or> is_subterm_of s t"
proof (induction t rule: strip_comb.induct)
  case (1 xs f x)
  then show ?case
    using is_subterm_of.App by auto
qed simp_all

lemma strip_comb'_subterm_of:
  "s = fst (strip_comb' t) \<or> s \<in> set (snd (strip_comb' t)) \<Longrightarrow> is_subterm_of s t"
  by (metis empty_iff is_subterm_of_fst_strip_comb list.set(1) snd_strip_comb_in_list_or_substerm)

inductive is_orange_subterm_at where
  Nil: "is_orange_subterm_at u u []" |
  App: "is_orange_subterm_at v (App t\<^sub>1 t\<^sub>2) (i # p)"
    if "strip_comb' (App t\<^sub>1 t\<^sub>2) = (f, us)"
    and "i < length us"
    and "is_Const f \<or> is_Bound f"
    and "is_orange_subterm_at v (us ! i) p" |
  Abs: "is_orange_subterm_at v (Abs \<tau> t) (0 # p)"
if "is_orange_subterm_at v t p"

text \<open>Contrary to Definition 2.2 of the paper, our positions count starting at zero.\<close>

lemma subterm_if_orange_subterm:
  assumes "is_orange_subterm_at s t p"
  shows "is_subterm_of s t"
  using assms
proof (induction s t p rule: is_orange_subterm_at.induct)
  case (Nil u)
  then show ?case
    by (simp add: is_subterm_of.intros)
next
  case (App t\<^sub>1 t\<^sub>2 f us i v p)
  then show ?case
    by (metis is_subterm_of.dual_order.trans nth_mem snd_conv strip_comb'_subterm_of)
next
  case (Abs v t p \<tau>)
  then show ?case
    by (simp add: is_subterm_of.intros)
qed

end
