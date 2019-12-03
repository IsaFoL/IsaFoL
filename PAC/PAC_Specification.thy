theory PAC_Specification
  imports PAC_More_Poly
begin

type_synonym int_poly = \<open>int mpoly\<close>
definition polynom_bool :: \<open>int_poly set\<close> where
  \<open>polynom_bool = (\<lambda>c. Var c ^ 2 - Var c) ` UNIV\<close>

definition pac_ideal where
  \<open>pac_ideal A \<equiv> ideal (A \<union> polynom_bool)\<close>

lemma
  fixes A :: \<open>(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set\<close>
  assumes \<open>p \<in> ideal A\<close>
  shows \<open>p * q \<in> ideal A\<close>
  by (metis assms ideal.span_scale semiring_normalization_rules(7))

lemma X2_X_in_pac_ideal:
  \<open>Var c ^ 2 - Var c \<in> pac_ideal A\<close>
  unfolding polynom_bool_def pac_ideal_def
  by (auto intro: ideal.span_base)

lemma pac_idealI1[intro]:
  \<open>p \<in> A \<Longrightarrow> p \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  by (auto intro: ideal.span_base)

lemma pac_idealI2[intro]:
  \<open>p \<in> ideal A \<Longrightarrow> p \<in> pac_ideal A\<close>
  using ideal.span_subspace_induct pac_ideal_def by blast

lemma pac_idealI3[intro]:
  \<open>p \<in> ideal A \<Longrightarrow> p*q \<in> pac_ideal A\<close>
  by (metis ideal.span_scale mult.commute pac_idealI2)

lemma pac_ideal_Xsq2_iff:
  \<open>Var c ^ 2 \<in> pac_ideal A \<longleftrightarrow> Var c \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  apply (subst (2) ideal.span_add_eq[symmetric, OF X2_X_in_pac_ideal[of c, unfolded pac_ideal_def]])
  apply auto
  done

text \<open>The PAC format contains three kind of steps:
  \<^item> add that adds up two polynoms that are known.
  \<^item> mult that multiply a known polynom with another one.
  \<^item> del that removes a polynom that cannot be reused anymore.

To model the simplification that happens, we add the \<^term>\<open>p - p' \<in> polynom_bool\<close>
stating that \<^term>\<open>p\<close> and  \<^term>\<open>p'\<close> are equivalent.
\<close>

type_synonym pac_st = \<open>(nat set \<times> int_poly multiset)\<close>
inductive PAC_Format :: \<open>pac_st \<Rightarrow> pac_st \<Rightarrow> bool\<close> where
add:
  \<open>PAC_Format (\<V>, A) (\<V>, add_mset p' A)\<close>
if
   \<open>p \<in># A\<close> \<open>q \<in># A\<close>
   \<open>p+q - p' \<in> ideal polynom_bool\<close>
   \<open>vars p' \<subseteq> vars (p + q)\<close> |
mult:
  \<open>PAC_Format (\<V>, A) (\<V>, add_mset p' A)\<close>
if
   \<open>p \<in># A\<close>
   \<open>p*q - p' \<in> ideal polynom_bool\<close>
   \<open>vars p' \<subseteq> vars (p * q)\<close>
   \<open>vars q \<subseteq> \<V>\<close> |
del:
   \<open>p \<in># A \<Longrightarrow> PAC_Format (\<V>, A) (\<V>, A - {#p#})\<close> |
ext:
  \<open>PAC_Format (\<V>, A) (\<V> \<union> {x \<in> vars p'. x \<notin> \<V>}, add_mset p' A)\<close>
  if
    \<open>x \<in> vars p'\<close>
    \<open>coeff p' (Poly_Mapping.single x 1) = -1 \<or> coeff p' (Poly_Mapping.single x 1) = 1\<close>
    \<open>x \<notin> \<V>\<close>

lemmas  PAC_Format_induct_split =
   PAC_Format.induct[split_format(complete), of V A V' A' for V A V' A']

lemma PAC_Format_induct[consumes 1, case_names add mult del ext]:
  assumes
    \<open>PAC_Format (\<V>, A) (\<V>', A')\<close> and
    cases:
      \<open>\<And>p q p'  A \<V>. p \<in># A \<Longrightarrow> q \<in># A \<Longrightarrow> p+q - p' \<in> ideal polynom_bool \<Longrightarrow> vars p' \<subseteq> vars (p + q) \<Longrightarrow> P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p q p' A \<V>. p \<in># A \<Longrightarrow> p*q - p' \<in> ideal polynom_bool \<Longrightarrow> vars p' \<subseteq> vars (p * q) \<Longrightarrow> vars q \<subseteq> \<V> \<Longrightarrow>
        P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p A \<V>. p \<in># A \<Longrightarrow> P \<V> A \<V> (A - {#p#})\<close>
      \<open>\<And>p' x. x \<in> vars p' \<Longrightarrow> coeff p' (Poly_Mapping.single x 1) = -1 \<or> coeff p' (Poly_Mapping.single x 1) = 1 \<Longrightarrow>
        x \<notin> \<V> \<Longrightarrow> P \<V> A (\<V> \<union> {x \<in> vars p'. x \<notin> \<V>}) (add_mset p' A)\<close>
  shows
     \<open>P \<V> A \<V>' A'\<close>
  using assms(1) apply -
  by (induct V\<equiv>\<V> A\<equiv>A \<V>' A' rule: PAC_Format_induct_split)
   (auto intro: assms(1) cases)

lemma diff_in_polynom_bool_pac_idealI:
   assumes a1: "p \<in> pac_ideal A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
 proof -
   have "insert p polynom_bool \<subseteq> pac_ideal A"
     using a1 unfolding pac_ideal_def by (meson ideal.span_superset insert_subset le_sup_iff)
   then show ?thesis
     using a2 unfolding pac_ideal_def by (metis (no_types) ideal.eq_span_insert_eq ideal.span_subset_spanI ideal.span_superset insert_subset subsetD)
qed

lemma diff_in_polynom_bool_pac_idealI2:
   assumes a1: "p \<in> A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
   using diff_in_polynom_bool_pac_idealI[OF _ assms(2), of A] assms(1)
   by (auto simp: ideal.span_base)

lemma pac_ideal_alt_def:
  \<open>pac_ideal A = ideal (A \<union> ideal polynom_bool)\<close>
  unfolding pac_ideal_def
  by (meson ideal.span_eq ideal.span_mono ideal.span_superset le_sup_iff subset_trans sup_ge2)

definition restricted_ideal_to where
  \<open>restricted_ideal_to B A = {p \<in> A. vars p  \<subseteq> B}\<close>

abbreviation restricted_ideal_to\<^sub>I where
  \<open>restricted_ideal_to\<^sub>I B A \<equiv> restricted_ideal_to B (pac_ideal (set_mset A))\<close>

abbreviation restricted_ideal_to\<^sub>V where
  \<open>restricted_ideal_to\<^sub>V B \<equiv> restricted_ideal_to (\<Union>(vars ` set_mset B))\<close>

abbreviation restricted_ideal_to\<^sub>V\<^sub>I where
  \<open>restricted_ideal_to\<^sub>V\<^sub>I B A \<equiv> restricted_ideal_to (\<Union>(vars ` set_mset B)) (pac_ideal (set_mset A))\<close>


lemma restricted_idealI:
  \<open>p \<in> pac_ideal (set_mset A) \<Longrightarrow> vars p \<subseteq> C \<Longrightarrow> p \<in> restricted_ideal_to\<^sub>I C A\<close>
  unfolding restricted_ideal_to_def
  by auto

lemma pac_ideal_insert_already_in:
  \<open>pq \<in> pac_ideal (set_mset A) \<Longrightarrow> pac_ideal (insert pq (set_mset A)) = pac_ideal (set_mset A)\<close>
  by (auto simp: pac_ideal_alt_def ideal.span_insert_idI)

lemma pac_ideal_add:
  \<open>p \<in># A \<Longrightarrow> q \<in># A \<Longrightarrow> p + q \<in> pac_ideal (set_mset A)\<close>
  by (simp add: ideal.span_add ideal.span_base pac_ideal_def)
lemma pac_ideal_mult:
  \<open>p \<in># A \<Longrightarrow> p * q \<in> pac_ideal (set_mset A)\<close>
  by (simp add: ideal.span_base pac_idealI3)

lemma pac_ideal_mono:
  \<open>A \<subseteq> B \<Longrightarrow> pac_ideal A \<subseteq> pac_ideal B\<close>
  using ideal.span_mono[of \<open>A \<union> _\<close> \<open>B \<union> _\<close>]
  by (auto simp: pac_ideal_def intro: ideal.span_mono)

lemma not_in_vars_coeff0:
  \<open>x \<notin> vars p \<Longrightarrow> MPoly_Type.coeff p (monomial (Suc 0) x) = 0\<close>
  apply (subst not_not[symmetric])
  apply (subst coeff_keys[symmetric])
  apply (auto simp: vars_def)
  done

lemma keys_mapping_sum_add:
  \<open>finite A \<Longrightarrow> keys (mapping_of (\<Sum>v \<in> A. f v)) \<subseteq> \<Union>(keys ` mapping_of ` f ` UNIV)\<close>
  apply (induction A rule: finite_induct)
  apply (auto simp add: zero_mpoly.rep_eq plus_mpoly.rep_eq
    keys_plus_ninv_comm_monoid_add)
  by (metis (no_types, lifting) Poly_Mapping.keys_add UN_E UnE subset_eq)

lemma vars_sum_vars_union:
  fixes f :: \<open>int mpoly \<Rightarrow> int mpoly\<close>
  assumes \<open>finite {v. f v \<noteq> 0}\<close>
  shows \<open>vars (\<Sum>v | f v \<noteq> 0. f v * v) \<subseteq> \<Union>(vars ` {v. f v \<noteq> 0}) \<union> \<Union>(vars ` f ` {v. f v \<noteq> 0})\<close>
    (is \<open>?A \<subseteq> ?B\<close>)
proof
  fix p
  assume \<open>p \<in> vars (\<Sum>v | f v \<noteq> 0. f v * v)\<close>
  then obtain x where \<open>x \<in> keys (mapping_of (\<Sum>v | f v \<noteq> 0. f v * v))\<close> and
    p: \<open>p \<in> keys x\<close>
    by (auto simp: vars_def times_mpoly.rep_eq simp del: keys_mult)
  then have \<open>x \<in> (\<Union>x. keys (mapping_of (f x) * mapping_of x))\<close>
    using keys_mapping_sum_add[of \<open>{v. f v \<noteq> 0}\<close> \<open>\<lambda>x. f x * x\<close>] assms
    by (auto simp: vars_def times_mpoly.rep_eq simp del: keys_mult)
  then have \<open>x \<in> (\<Union>x. {a+b| a b. a \<in> keys (mapping_of (f x)) \<and> b \<in> keys (mapping_of x)})\<close>
    using Union_mono[OF ] keys_mult by fast
  then show \<open>p \<in> ?B\<close>
    using p apply (auto simp: keys_add)
    by (metis (no_types, lifting) Poly_Mapping.keys_add UN_I UnE empty_iff
      in_mono keys_zero vars_def zero_mpoly.rep_eq)
qed

lemma span_explicit':
  fixes b :: \<open>int mpoly set\<close>
  assumes b: \<open>\<Union> (vars `b) \<subseteq> \<V>\<close>
  shows
    "{v \<in> ideal.span b. vars v \<subseteq> \<V>} = {(\<Sum>v | f v \<noteq> 0. f v * v) | f. finite {v. f v \<noteq> 0} \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> b) \<and> (\<forall>v. f v \<noteq> 0 \<longrightarrow> vars (f v) \<subseteq> \<V>)}"
  (is \<open>?A = ?B\<close>)
proof (standard; standard)
  fix x
  assume \<open>x \<in> ?B\<close>
  then obtain f where
    x: \<open>x = (\<Sum>v | f v \<noteq> 0. f v * v)\<close> and
    fin: \<open>finite {v. f v \<noteq> 0}\<close> and
    v_b: \<open>\<And>v. f v \<noteq> 0 \<Longrightarrow> v \<in> b\<close> and
    f_b: \<open>\<And>v. f v \<noteq> 0 \<Longrightarrow> vars (f v) \<subseteq> \<V>\<close>
    unfolding ideal.span_explicit'
    by auto
  then have \<open>x \<in> ideal.span b\<close>
    unfolding ideal.span_explicit'
    by auto
  moreover have \<open>\<Union> (vars ` {v. f v \<noteq> 0}) \<union> \<Union> (vars ` f ` {v. f v \<noteq> 0}) \<subseteq> \<V>\<close>
    using f_b v_b b by blast
  then have \<open>vars x \<subseteq> \<V>\<close>
    using vars_sum_vars_union[of f] fin
    unfolding x
    apply auto
    by blast
  ultimately show \<open>x \<in> ?A\<close>
    by auto
next
  fix x
  assume \<open>x \<in> ?A\<close>
  then have \<open>x \<in> ideal b\<close> and
    \<open>vars x \<subseteq> \<V>\<close>
    by auto
  from More_Modules.ideal.spanE[OF this(1)] obtain A q where
    \<open>x = (\<Sum>b\<in>A. q b * b)\<close>
    \<open>finite A\<close> and
    \<open>A \<subseteq> b\<close>
    by metis
    oops

lemma ideal_insert':
  \<open>More_Modules.ideal (insert a S) = {y. \<exists>x k. y = x + k * a \<and> x \<in> More_Modules.ideal S}\<close>
    apply (auto simp: pac_ideal_def ideal.span_insert
      intro: exI[of _ \<open>_ - k * a\<close>])
   apply (rule_tac x = \<open>x - k * a\<close> in exI)
   apply auto
   apply (rule_tac x = \<open>k\<close> in exI)
   apply auto
   done


lemma vars_in_right_only:
  "x \<in> vars q \<Longrightarrow> x \<notin> vars p \<Longrightarrow> x \<in> vars (p+q)"
  apply (auto simp: vars_def keys_def plus_mpoly.rep_eq
    lookup_plus_fun)
  by (metis add.left_neutral gr_implies_not0)

lemma [simp]:
  \<open>vars 0 = {}\<close>
  by (simp add: vars_def zero_mpoly.rep_eq)

lemma
  fixes p :: \<open>int mpoly\<close>
  assumes
    x'_p: \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    \<open>MPoly_Type.coeff p (monomial (Suc 0) x') = 1\<close> and
    vars: \<open>vars (xa + k * p) \<subseteq> \<V>\<close> and
    \<open>xa \<in> More_Modules.ideal (set_mset A \<union> polynom_bool)\<close>
  shows \<open>k = 0\<close>
proof (rule ccontr)
  assume \<open>k \<noteq> 0\<close>
  define p' where \<open>p' \<equiv> p - Var x'\<close>
  have \<open>p = Var x' + p'\<close>
    unfolding p'_def
    by auto

  have \<open>vars (xa + k * p) = vars (xa + (k * p' + k*Var x'))\<close>
    by (auto simp: p'_def algebra_simps)
  have \<open>x' \<notin> vars (xa + k * p)\<close>
    using vars x' by auto
  then have \<open>x' \<notin> vars (k*p)\<close>
    using vars_add[of xa \<open>k*p\<close>]
    apply auto
    sorry

oops













lemma PAC_Format_subset_ideal:
  \<open>PAC_Format (\<V>, A) (\<V>', B) \<Longrightarrow> \<Union>(vars ` set_mset A) \<subseteq> \<V> \<Longrightarrow>
     restricted_ideal_to\<^sub>I \<V> B \<subseteq> restricted_ideal_to\<^sub>I \<V> A \<and> \<V> \<subseteq> \<V>' \<and> \<Union>(vars ` set_mset B) \<subseteq> \<V>'\<close>
  unfolding restricted_ideal_to_def
  apply (induction rule:PAC_Format_induct)
  subgoal for p q pq A \<V>
    using vars_add
    by (fastforce simp: ideal.span_add_eq ideal.span_base pac_ideal_insert_already_in[OF diff_in_polynom_bool_pac_idealI[of \<open>p + q\<close> \<open>_\<close> pq]]
        pac_ideal_add
      intro!: diff_in_polynom_bool_pac_idealI[of \<open>p + q\<close> \<open>_\<close> pq])
  subgoal for p q pq
    using vars_mult[of p q]
    by (force simp: ideal.span_add_eq ideal.span_base pac_ideal_mult
      pac_ideal_insert_already_in[OF diff_in_polynom_bool_pac_idealI[of \<open>p*q\<close> \<open>_\<close> pq]])
  subgoal for p A
    using pac_ideal_mono[of \<open>set_mset (A - {#p#})\<close> \<open>set_mset A\<close>]
    by (auto dest: in_diffD)
  subgoal for p x'
    apply auto
    apply (auto simp: pac_ideal_def ideal_insert' vars_add)
    sledgehammer
find_theorems "vars (_ + _)"
    thm ideal.span_insert[of a S]
    try0
  done


text \<open>
  In general, if deletions are disallowed, then the stronger \<^term>\<open>B = pac_ideal A\<close> holds.
\<close>
lemma restricted_ideal_to_restricted_ideal_to\<^sub>ID:
  \<open>restricted_ideal_to \<V> (set_mset A) \<subseteq> restricted_ideal_to\<^sub>I \<V> A\<close>
   by (auto simp add: Collect_disj_eq pac_idealI1 restricted_ideal_to_def)


lemma rtranclp_PAC_Format_subset_ideal:
  \<open>rtranclp PAC_Format (\<V>, A) (\<V>', B) \<Longrightarrow> \<Union>(vars ` set_mset A) \<subseteq> \<V> \<Longrightarrow>
     restricted_ideal_to \<V> (set_mset B) \<subseteq> restricted_ideal_to\<^sub>I \<V> A \<and> \<V> \<subseteq> \<V>' \<and> \<Union>(vars ` set_mset B) \<subseteq> \<V>'\<close>
  apply (induction rule:rtranclp_induct[of PAC_Format \<open>(_, _)\<close> \<open>(_, _)\<close>, split_format(complete)])
  subgoal
    by (simp add: restricted_ideal_to_restricted_ideal_to\<^sub>ID)
  subgoal
    apply (drule PAC_Format_subset_ideal)
    apply simp_all
    apply auto
    sledgehammer
  apply (simp_all add: ideal.span_base 
       ideal.span_subset_spanI restricted_ideal_to_restricted_ideal_to\<^sub>ID)


      apply (auto simp add: Collect_disj_eq pac_idealI1 restricted_ideal_to_def conj_disj_distribR Collect_conv_if
        dest!: multi_member_split split: if_splits)
apply auto
      sorry
  by (meson ideal.span_subset_spanI ideal.span_superset le_sup_iff subsetD)
find_theorems "{_. _ = _ \<and>  _}"

lemma ideal_mult_right_in:
  \<open>a \<in> ideal A \<Longrightarrow> a * b \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))

lemma ideal_mult_right_in2:
  \<open>a \<in> ideal A \<Longrightarrow> b * a \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale)


end