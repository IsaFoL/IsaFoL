theory Uprod_Extra
  imports
    "HOL-Library.Multiset"
    "HOL-Library.Uprod"
begin

lemma Upair_sym: "Upair x y = Upair y x"
  by (metis Upair_inject)

lemma ex_ordered_Upair:
  assumes tot: "totalp_on (set_uprod p) R"
  shows "\<exists>x y. p = Upair x y \<and> R\<^sup>=\<^sup>= x y"
proof -
  obtain x y where "p = Upair x y"
    by (metis uprod_exhaust)

  show ?thesis
  proof (cases "R\<^sup>=\<^sup>= x y")
    case True
    show ?thesis
    proof (intro exI conjI)
      show "p = Upair x y"
        using \<open>p = Upair x y\<close> .
    next
      show "R\<^sup>=\<^sup>= x y"
        using True by simp
    qed
  next
    case False
    then show ?thesis
    proof (intro exI conjI)
      show "p = Upair y x"
        using \<open>p = Upair x y\<close> by simp
    next
      from tot have "R y x"
        using False
        by (simp add: \<open>p = Upair x y\<close> totalp_on_def)
      thus "R\<^sup>=\<^sup>= y x"
        by simp
    qed
  qed
qed

definition mset_uprod :: "'a uprod \<Rightarrow> 'a multiset" where
  "mset_uprod = case_uprod (Abs_commute (\<lambda>x y. {#x, y#}))"

lemma Abs_commute_inverse_mset[simp]:
  "apply_commute (Abs_commute (\<lambda>x y. {#x, y#})) = (\<lambda>x y. {#x, y#})"
  by (simp add: Abs_commute_inverse)

lemma set_mset_mset_uprod[simp]: "set_mset (mset_uprod up) = set_uprod up"
  by (simp add: mset_uprod_def case_uprod.rep_eq set_uprod.rep_eq case_prod_beta)

lemma mset_uprod_Upair[simp]: "mset_uprod (Upair x y) = {#x, y#}"
  by (simp add: mset_uprod_def)

end