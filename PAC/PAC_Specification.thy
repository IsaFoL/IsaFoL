theory PAC_Specification
  imports "HOL-Library.Poly_Mapping" "HOL-Algebra.Polynomials" "Polynomials.MPoly_Type_Class"
  "HOL-Algebra.Module"
  "HOL-Library.Countable_Set"
begin

type_synonym int_poly = \<open>((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 int)\<close>
definition polynom_bool :: \<open>int_poly set\<close> where
  \<open>polynom_bool = (\<lambda>c. Var\<^sub>0 c ^ 2 - Var\<^sub>0 c) ` UNIV\<close>

term \<open>ideal (A \<union> polynom_bool)\<close>

abbreviation pac_ideal where
  \<open>pac_ideal A \<equiv> ideal (A \<union> polynom_bool)\<close>

lemma
  fixes A :: \<open>(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set\<close>
  assumes \<open>p \<in> ideal A\<close>
  shows \<open>p * q \<in> ideal A\<close>
  by (metis assms ideal.span_scale semiring_normalization_rules(7))

lemma X2_X_in_pac_ideal:
  \<open>Var\<^sub>0 c ^ 2 - Var\<^sub>0 c \<in> pac_ideal A\<close>
  unfolding polynom_bool_def
  by (auto intro: ideal.span_base)

lemma pac_ideal_Xsq2_iff:
  \<open>Var\<^sub>0 c ^ 2 \<in> pac_ideal A \<longleftrightarrow> Var\<^sub>0 c \<in> pac_ideal A\<close>
  apply (subst (2) ideal.span_add_eq[symmetric, OF X2_X_in_pac_ideal[of c]])
  apply auto
  done

text \<open>The PAC format contains three kind of steps:
  \<^item> add that adds up two polynoms that are known.
  \<^item> mult that multiply a known polynom with another one.
  \<^item> del that removes a polynom that cannot be reused anymore.

To model the simplification that happens, we add the \<^term>\<open>p - p' \<in> polynom_bool\<close>
stating that \<^term>\<open>p\<close> and  \<^term>\<open>p'\<close> are equivalent.
\<close>
inductive PAC_Format :: \<open>int_poly set \<Rightarrow> int_poly set \<Rightarrow> bool\<close> where
add:
  \<open>PAC_Format A (insert p' A)\<close>
if
   \<open>p \<in> A\<close> \<open>q \<in> A\<close>
   \<open>p+q - p' \<in> polynom_bool\<close> |
mult:
  \<open>PAC_Format A (insert p' A)\<close>
if
   \<open>p \<in> A\<close>
   \<open>p*q - p' \<in> polynom_bool\<close> |
del:
   \<open>p \<in> A \<Longrightarrow> PAC_Format A (A - {p})\<close>

lemma diff_in_polynom_bool_pac_idealI:
  \<open>p - p' \<in> polynom_bool \<Longrightarrow> p \<in> pac_ideal A \<Longrightarrow>  p' \<in> pac_ideal A\<close>
  by (smt Un_insert_right add_diff_cancel group_eq_aux ideal.span_diff ideal.span_superset
      insertCI mk_disjoint_insert subsetD)

lemma PAC_Format_subset_ideal:
  \<open>PAC_Format A B \<Longrightarrow> B \<subseteq> pac_ideal A\<close>
  apply (induction rule:PAC_Format.induct)
    apply (auto simp: ideal.span_add_eq ideal.span_base
      intro: diff_in_polynom_bool_pac_idealI)
  by (smt diff_in_polynom_bool_pac_idealI ideal.span_scale ideal.span_superset le_sup_iff
      semiring_normalization_rules(7) subsetD)

text \<open>
  In general, if deletions are disallowed, then the stronger \<^term>\<open>B = pac_ideal A\<close> holds.
\<close>

lemma rtranclp_PAC_Format_subset_ideal:
  \<open>rtranclp PAC_Format A B \<Longrightarrow> B \<subseteq> pac_ideal A\<close>
  apply (induction rule:rtranclp_induct)
  apply (auto 5 3 intro: ideal.span_base dest!: PAC_Format_subset_ideal
      dest: ideal.span_subset_spanI)
  by (meson ideal.span_subset_spanI ideal.span_superset le_sup_iff subsetD)


end