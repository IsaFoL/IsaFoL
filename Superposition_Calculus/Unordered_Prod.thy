theory Unordered_Prod
  imports "HOL-Library.Multiset"
begin

typedef 'a uprod = \<open>{M :: 'a multiset. size M = 2}\<close>
  morphisms mset_uprod Abs_uprod
proof -
  have "{#undefined, undefined#} \<in> {M :: 'a multiset. size M = 2}"
    by simp
  thus "\<exists>x :: 'a multiset. x \<in> {M. size M = 2}"
    by metis
qed

setup_lifting type_definition_uprod

lift_bnf (no_warn_wits) 'a uprod
  by auto

definition uprod_prod where
  "uprod_prod p = Abs_uprod {#fst p, snd p#}"

definition make_uprod where
  "make_uprod t\<^sub>1 t\<^sub>2 \<equiv> Abs_uprod {#t\<^sub>1, t\<^sub>2#}"

lemma make_uprod_sym: "make_uprod t\<^sub>1 t\<^sub>2 = make_uprod t\<^sub>2 t\<^sub>1"
  by (simp add: make_uprod_def add_mset_commute)

lemma make_uprod_eq_make_uprod_iff: "make_uprod x y = make_uprod z w \<longleftrightarrow> x = z \<and> y = w \<or> x = w \<and> y = z"
  by (smt (verit) Abs_uprod_inverse One_nat_def Suc_1 add_eq_conv_ex make_uprod_def mem_Collect_eq
      single_eq_add_mset size_add_mset size_empty)

lemma ex_make_uprod: "\<exists>x y. p = make_uprod x y"
proof -
  have "size (mset_uprod p) = 2"
    using mset_uprod by auto
  then obtain x y where "mset_uprod p = {#x, y#}"
    by (metis Suc_1 add_cancel_left_left size_1_singleton_mset size_mset_SucE
        union_mset_add_mset_left)
  show ?thesis
  proof (intro exI)
    show "p = make_uprod x y"
      by (metis \<open>mset_uprod p = {#x, y#}\<close> make_uprod_def mset_uprod_inverse)
  qed
qed

lemma mset_uprod_make_uprod[simp]: "mset_uprod (make_uprod x y) = {#x, y#}"
  by (simp add: Abs_uprod_inverse make_uprod_def)

lemma set_uprod_make_uprod[simp]: "set_uprod (make_uprod x y) = {x, y}"
  by (simp add: Abs_uprod_inverse make_uprod_def set_uprod_def)

lemma map_uprod_make_uprod[simp]: "map_uprod f (make_uprod x y) = make_uprod (f x) (f y)"
  by (metis comp_apply image_mset_add_mset image_mset_single make_uprod_def map_uprod_def
      mset_uprod_make_uprod)

lemma ex_ordered_make_uprod:
  assumes tot: "totalp_on (set_uprod p) R"
  shows "\<exists>x y. p = make_uprod x y \<and> R\<^sup>=\<^sup>= x y"
proof -
  have "size (mset_uprod p) = 2"
    using mset_uprod by auto
  then obtain x y where "mset_uprod p = {#x, y#}"
    by (metis Suc_1 add_cancel_left_left size_1_singleton_mset size_mset_SucE
        union_mset_add_mset_left)
  show ?thesis
  proof (cases "R\<^sup>=\<^sup>= x y")
    case True
    show ?thesis
    proof (intro exI conjI)
      show "p = make_uprod x y"
        by (metis \<open>mset_uprod p = {#x, y#}\<close> make_uprod_def mset_uprod_inverse)
    next
      show "R\<^sup>=\<^sup>= x y"
        using True by simp
    qed
  next
    case False
    then show ?thesis
    proof (intro exI conjI)
      show "p = make_uprod y x"
        by (metis \<open>mset_uprod p = {#x, y#}\<close> make_uprod_sym mset_uprod_inverse mset_uprod_make_uprod)
    next
      from tot have "R y x"
        using False
        by (simp add: \<open>mset_uprod p = {#x, y#}\<close> set_uprod_def totalp_on_def)
      thus "R\<^sup>=\<^sup>= y x"
        by simp
    qed
  qed
qed


end