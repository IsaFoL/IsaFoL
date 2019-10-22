theory PAC_Specification
  imports PAC_More_Poly
begin

type_synonym int_poly = \<open>int mpoly\<close>
definition polynom_bool :: \<open>int_poly set\<close> where
  \<open>polynom_bool = (\<lambda>c. Var c ^ 2 - Var c) ` UNIV\<close>

abbreviation pac_ideal where
  \<open>pac_ideal A \<equiv> ideal (A \<union> polynom_bool)\<close>

lemma
  fixes A :: \<open>(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set\<close>
  assumes \<open>p \<in> ideal A\<close>
  shows \<open>p * q \<in> ideal A\<close>
  by (metis assms ideal.span_scale semiring_normalization_rules(7))

lemma X2_X_in_pac_ideal:
  \<open>Var c ^ 2 - Var c \<in> pac_ideal A\<close>
  unfolding polynom_bool_def
  by (auto intro: ideal.span_base)

lemma pac_ideal_Xsq2_iff:
  \<open>Var c ^ 2 \<in> pac_ideal A \<longleftrightarrow> Var c \<in> pac_ideal A\<close>
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
inductive PAC_Format :: \<open>int_poly set \<Rightarrow> int_poly set \<Rightarrow> bool\<close> for A :: \<open>int_poly set\<close> where
add:
  \<open>PAC_Format A (insert p' A)\<close>
if
   \<open>p \<in> A\<close> \<open>q \<in> A\<close>
   \<open>p+q - p' \<in> ideal polynom_bool\<close> |
mult:
  \<open>PAC_Format A (insert p' A)\<close>
if
   \<open>p \<in> A\<close>
   \<open>p*q - p' \<in> ideal polynom_bool\<close> |
del:
   \<open>p \<in> A \<Longrightarrow> PAC_Format A (A - {p})\<close>

lemma diff_in_polynom_bool_pac_idealI:
   assumes a1: "p \<in> pac_ideal A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
 proof -
   have "insert p polynom_bool \<subseteq> pac_ideal A"
     using a1 by (meson ideal.span_superset insert_subset le_sup_iff)
   then show ?thesis
     using a2 by (metis (no_types) ideal.eq_span_insert_eq ideal.span_subset_spanI ideal.span_superset insert_subset subsetD)
qed

lemma diff_in_polynom_bool_pac_idealI2:
   assumes a1: "p \<in> A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
   using diff_in_polynom_bool_pac_idealI[OF _ assms(2), of A] assms(1)
   by (auto simp: ideal.span_base)

lemma pac_ideal_alt_def:
  \<open>pac_ideal A = ideal (A \<union> ideal polynom_bool)\<close>
  by (meson ideal.span_eq ideal.span_mono ideal.span_superset le_sup_iff subset_trans sup_ge2)

lemma PAC_Format_subset_ideal:
  \<open>PAC_Format A B \<Longrightarrow> B \<subseteq> pac_ideal A\<close>
  apply (induction rule:PAC_Format.induct)
  subgoal
    apply (auto simp: ideal.span_add_eq ideal.span_base pac_ideal_alt_def
      intro: diff_in_polynom_bool_pac_idealI[unfolded pac_ideal_alt_def])
   by (metis cancel_comm_monoid_add_class.diff_cancel diff_in_polynom_bool_pac_idealI
     diff_in_polynom_bool_pac_idealI2 ideal.span_add ideal.span_zero pac_ideal_alt_def)
  subgoal for p q p'
    using  diff_in_polynom_bool_pac_idealI[unfolded pac_ideal_alt_def,
      of \<open>p * q\<close> A p']
    apply (auto simp: ideal.span_add_eq ideal.span_base pac_ideal_alt_def
        ac_simps
      intro: diff_in_polynom_bool_pac_idealI[unfolded pac_ideal_alt_def])
    by (metis UnCI ideal.span_base ideal.span_scale
       pac_ideal_alt_def semiring_normalization_rules(7))
  subgoal
    by (auto simp: ideal.span_add_eq ideal.span_base pac_ideal_alt_def
        ac_simps
      intro: diff_in_polynom_bool_pac_idealI[unfolded pac_ideal_alt_def])
  done

text \<open>
  In general, if deletions are disallowed, then the stronger \<^term>\<open>B = pac_ideal A\<close> holds.
\<close>

lemma rtranclp_PAC_Format_subset_ideal:
  \<open>rtranclp PAC_Format A B \<Longrightarrow> B \<subseteq> pac_ideal A\<close>
  apply (induction rule:rtranclp_induct)
  apply (auto 5 3 intro: ideal.span_base dest!: PAC_Format_subset_ideal
      dest: ideal.span_subset_spanI)
  by (meson ideal.span_subset_spanI ideal.span_superset le_sup_iff subsetD)


lemma ideal_mult_right_in:
  \<open>a \<in> ideal A \<Longrightarrow> a * b \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))

lemma ideal_mult_right_in2:
  \<open>a \<in> ideal A \<Longrightarrow> b * a \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale)


end