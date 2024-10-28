theory FSet_Extra
  imports "HOL-Library.FSet"
begin

locale finite_set =
  fixes set :: "'b \<Rightarrow> 'a set"
  assumes finite_set [simp]: "\<And>b. finite (set b)"
begin

abbreviation finite_set :: "'b \<Rightarrow> 'a fset" where 
  "finite_set b \<equiv> Abs_fset (set b)"

lemma finite_set': "set b \<in> {A. finite A}"
  by simp

lemma fset_finite_set [simp]: "fset (finite_set b) = set b"
  using Abs_fset_inverse[OF finite_set'].

end

end
