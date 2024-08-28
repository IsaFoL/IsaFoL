theory The_Optional
  imports Main
begin

definition The_optional :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "The_optional P = (if \<exists>!x. P x then Some (THE x. P x) else None)"

lemma The_optional_eq_SomeD: "The_optional P = Some x \<Longrightarrow> P x"
  unfolding The_optional_def
  by (metis option.discI option.inject theI_unique)

lemma Some_eq_The_optionalD: "Some x = The_optional P \<Longrightarrow> P x"
  using The_optional_eq_SomeD by metis

lemma The_optional_eq_NoneD: "The_optional P = None \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma None_eq_The_optionalD: "None = The_optional P \<Longrightarrow> \<nexists>!x. P x"
  unfolding The_optional_def
  by (metis option.discI)

lemma The_optional_eq_SomeI:
  assumes "\<exists>\<^sub>\<le>\<^sub>1x. P x" and "P x"
  shows "The_optional P = Some x"
  using assms by (metis The_optional_def the1_equality')

end