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

definition make_uprod (infix "\<approx>" 60) where
  "t\<^sub>1 \<approx> t\<^sub>2 \<equiv> Abs_uprod {#t\<^sub>1, t\<^sub>2#}"

lemma make_uprod_sym: "t\<^sub>1 \<approx> t\<^sub>2 = t\<^sub>2 \<approx> t\<^sub>1"
  by (simp add: make_uprod_def add_mset_commute)

lemma make_uprod_eq_make_uprod_iff: "x \<approx> y = z \<approx> w \<longleftrightarrow> x = z \<and> y = w \<or> x = w \<and> y = z"
  by (smt (verit) Abs_uprod_inverse One_nat_def Suc_1 add_eq_conv_ex make_uprod_def mem_Collect_eq
      single_eq_add_mset size_add_mset size_empty)

lemma ex_make_uprod: "\<exists>x y. p = x \<approx> y"
proof -
  have "size (mset_uprod p) = 2"
    using mset_uprod by auto
  then obtain x y where "mset_uprod p = {#x, y#}"
    by (metis Suc_1 add_cancel_left_left size_1_singleton_mset size_mset_SucE
        union_mset_add_mset_left)
  show ?thesis
  proof (intro exI)
    show "p = x \<approx> y"
      by (metis \<open>mset_uprod p = {#x, y#}\<close> make_uprod_def mset_uprod_inverse)
  qed
qed

lemma mset_uprod_make_uprod[simp]: "mset_uprod (x \<approx> y) = {#x, y#}"
  by (simp add: Abs_uprod_inverse make_uprod_def)

lemma set_uprod_make_uprod[simp]: "set_uprod (x \<approx> y) = {x, y}"
  by (simp add: Abs_uprod_inverse make_uprod_def set_uprod_def)


end