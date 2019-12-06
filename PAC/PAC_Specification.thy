theory PAC_Specification
  imports PAC_More_Poly
begin

find_theorems \<open>genideal _ {}\<close>
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
extend:
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
    by (auto simp: vars_def times_mpoly.rep_eq)
  then have \<open>x \<in> (\<Union>x. {a+b| a b. a \<in> keys (mapping_of (f x)) \<and> b \<in> keys (mapping_of x)})\<close>
    using Union_mono[OF ] keys_mult by fast
  then show \<open>p \<in> ?B\<close>
    using p apply (auto simp: keys_add)
    by (metis (no_types, lifting) Poly_Mapping.keys_add UN_I UnE empty_iff
      in_mono keys_zero vars_def zero_mpoly.rep_eq)
qed


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


lemma polynom_sum_monoms:
  fixes p :: \<open>'a :: {comm_monoid_add,cancel_comm_monoid_add} mpoly\<close>
  shows
     \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
     \<open>keys (mapping_of p) \<subseteq> I \<Longrightarrow> finite I \<Longrightarrow> p = (\<Sum>x\<in>I. MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
proof -
  define J where \<open>J \<equiv> keys (mapping_of p)\<close>
  define a where \<open>a x \<equiv> coeff p x\<close> for x
  have \<open>finite (keys (mapping_of p))\<close>
    by auto
  have \<open>p = (\<Sum>x\<in>I. MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
    if \<open>finite I\<close> and \<open>keys (mapping_of p) \<subseteq> I\<close>
    for I
    using that
    unfolding a_def
   proof (induction I arbitrary: p rule: finite_induct)
      case empty
      then have \<open>p = 0\<close>
        using empty coeff_all_0 coeff_keys by blast
      then show ?case using empty by (auto simp: zero_mpoly.rep_eq)
    next
      case (insert x F) note fin = this(1) and xF = this(2) and IH = this(3) and
        incl = this(4)
      let ?p = \<open>p - MPoly_Type.monom x (MPoly_Type.coeff p x)\<close>
      have \<open>?p = (\<Sum>xa\<in>F. MPoly_Type.monom xa (MPoly_Type.coeff ?p xa))\<close>
        apply (rule IH)
        using incl apply auto
        by (smt Diff_iff Diff_insert_absorb add_diff_cancel_right'
          remove_term_keys remove_term_sum subsetD xF)
      also have \<open>... = (\<Sum>xa\<in>F. MPoly_Type.monom xa (MPoly_Type.coeff p xa))\<close>
        apply (use xF in \<open>auto intro!: sum.cong\<close>)
        by (metis (mono_tags, hide_lams) add_diff_cancel_right' remove_term_coeff
          remove_term_sum when_def)
      finally show ?case
        using xF fin apply auto
        by (metis add.commute add_diff_cancel_right' remove_term_sum)
    qed
    from this[of I] this[of J] show
     \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
     \<open>keys (mapping_of p) \<subseteq> I \<Longrightarrow> finite I \<Longrightarrow> p = (\<Sum>x\<in>I. MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
     by (auto simp: J_def)
qed


definition decrease_key::"'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::{monoid_add, minus,one}) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "decrease_key k0 f = Abs_poly_mapping (\<lambda>k. if k = k0 \<and> lookup f k \<noteq> 0 then lookup f k - 1 else lookup f k)"

lemma remove_key_lookup:
  "lookup (decrease_key k0 f) k = (if k = k0 \<and> lookup f k \<noteq> 0 then lookup f k - 1 else lookup f k)"
  unfolding decrease_key_def using finite_subset apply (simp add: lookup_Abs_poly_mapping)
  apply (subst lookup_Abs_poly_mapping)
  apply (auto intro: finite_subset[of _ \<open>{x. lookup f x \<noteq> 0}\<close>])
  apply (subst lookup_Abs_poly_mapping)
  apply (auto intro: finite_subset[of _ \<open>{x. lookup f x \<noteq> 0}\<close>])
  done

lemma polynom_split_on_var:
  fixes p :: \<open>'a :: {comm_monoid_add,cancel_comm_monoid_add,semiring_0,comm_semiring_1} mpoly\<close>
  obtains q r where
    \<open>p = monom (monomial (Suc 0) x') 1 * q + r\<close> and
    \<open>x' \<notin> vars r\<close>
proof -
  have [simp]: \<open>{x \<in> keys (mapping_of p). x' \<in> keys x} \<union>
        {x \<in> keys (mapping_of p). x' \<notin> keys x} = keys (mapping_of p)\<close>
    by auto
  have
    \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close> (is \<open>_ = (\<Sum>x \<in> ?I. ?f x)\<close>)
    using polynom_sum_monoms(1)[of p] .
  also have \<open>... = (\<Sum>x\<in> {x \<in> ?I. x' \<in> keys x}. ?f x) + (\<Sum>x\<in> {x \<in> ?I. x' \<notin> keys x}. ?f x)\<close> (is \<open>_ = ?pX + ?qX\<close>)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) auto
  finally have 1: \<open>p = ?pX + ?qX\<close> .
  have H: \<open>0 < lookup x x' \<Longrightarrow> (\<lambda>k. (if x' = k then Suc 0 else 0) +
          (if k = x' \<and> 0 < lookup x k then lookup x k - 1
           else lookup x k)) = lookup x\<close> for x x'
      by auto
  have H: \<open>x' \<in> keys x \<Longrightarrow> monomial (Suc 0) x' + Abs_poly_mapping (\<lambda>k. if k = x' \<and> 0 < lookup x k then lookup x k - 1 else lookup x k) = x\<close>
    for x and x' :: nat
    apply (simp only: keys_def single.abs_eq)
    apply (subst plus_poly_mapping.abs_eq)
    apply (auto simp: eq_onp_def intro!: finite_subset[of \<open>{_. _ \<and> _}\<close> \<open>{xa. 0 < lookup x xa}\<close>])
    apply (smt bounded_nat_set_is_finite lessI mem_Collect_eq neq0_conv when_cong when_neq_zero)
    apply (rule finite_subset[of _  \<open>{xa. 0 < lookup x xa}\<close>])
    by (auto simp: when_def H split: if_splits)

  have [simp]: \<open>x' \<in> keys x \<Longrightarrow>
        MPoly_Type.monom (monomial (Suc 0) x' + decrease_key x' x) n =
        MPoly_Type.monom x n\<close> for x n and x'
        apply (subst mpoly.mapping_of_inject[symmetric], subst poly_mapping.lookup_inject[symmetric])
        unfolding mapping_of_monom lookup_single
        apply (auto intro!: ext simp: decrease_key_def when_def H)
        done
  have pX: \<open>?pX = monom (monomial (Suc 0) x') 1 * (\<Sum>x\<in> {x \<in> ?I. x' \<in> keys x}. MPoly_Type.monom (decrease_key x' x) (MPoly_Type.coeff p x))\<close>
    (is \<open>_ = _ * ?pX'\<close>)
    by (subst sum_distrib_left, subst mult_monom)
     (auto intro!: sum.cong)
  have \<open>x' \<notin> vars ?qX\<close>
    using vars_setsum[of \<open>{x. x \<in> keys (mapping_of p) \<and> x' \<notin> keys x}\<close> \<open>?f\<close>]
    by auto (metis (mono_tags, lifting) UN_E mem_Collect_eq subsetD vars_monom_subset)

  then show ?thesis
    using that[of ?pX' ?qX]
    unfolding pX[symmetric] 1[symmetric]
    by blast
qed

lemma vars_Un_nointer:
  \<open>keys (mapping_of p) \<inter>  keys (mapping_of q) = {} \<Longrightarrow> vars (p + q) = vars p \<union> vars q\<close>
  apply (auto simp: vars_def)
  apply (metis (no_types, hide_lams) Poly_Mapping.keys_add UnE in_mono plus_mpoly.rep_eq)
  apply (smt IntI UN_I add.right_neutral coeff_add coeff_keys empty_iff empty_iff in_keys_iff)
  apply (smt IntI UN_I add.left_neutral coeff_add coeff_keys empty_iff empty_iff in_keys_iff)
  done

lemmas [simp] = zero_mpoly.rep_eq

lemma vars_mult_monom:
  fixes p :: \<open>int mpoly\<close>
  shows \<open>vars (p * (monom (monomial (Suc 0) x') 1)) = (if p = 0 then {} else insert x' (vars p))\<close>
proof -
(*  have 0: \<open>a = x - b \<longleftrightarrow> x = a + b\<close> for x a :: \<open>nat \<Rightarrow>\<^sub>0 nat\<close> and b
    apply (auto simp: ac_simps)
    apply transfer
    supply[[show_types]]
    apply (auto intro!: ext simp: ac_simps)
    sledgehammer
    sorry
  have  \<open>(\<Sum>aa. (if aa = monomial (Suc 0) x' then 1 else 0) when
                   x = a + aa) = (if a = x - monomial (Suc 0) x' then 1 else 0)\<close> for x a
   unfolding 0
   using Sum_any.not_neutral_obtains_not_neutral by force

  show ?thesis
    apply (auto simp: vars_def times_mpoly.rep_eq)
    apply (smt Poly_Mapping.keys_add Un_iff in_keys_timesE in_mono lookup_eq_zero_in_keys_contradict lookup_single_not_eq)
    apply (auto simp: keys_def times_poly_mapping.rep_eq prod_fun_def)[]
    
    sorry
    find_theorems "lookup (_ * _)"
    *)
  let ?v = \<open>monom (monomial (Suc 0) x') 1\<close>
  have
    p: \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close> (is \<open>_ = (\<Sum>x \<in> ?I. ?f x)\<close>)
    using polynom_sum_monoms(1)[of p] .
  have pv: \<open>p * ?v = (\<Sum>x \<in> ?I. ?f x * ?v)\<close>
    by (subst p) (auto simp:  field_simps sum_distrib_left)
  define I where \<open>I \<equiv> ?I\<close>
  have in_keysD: \<open>x \<in> keys (mapping_of (\<Sum>x\<in>I. MPoly_Type.monom x (h x)))  \<Longrightarrow> x \<in> I\<close>
   if \<open>finite I\<close> for I and h :: \<open>_ \<Rightarrow> int\<close> and x
   using that apply (induction rule: finite_induct)
   apply auto
   by (smt coeff_add coeff_keys empty_iff insert_iff keys_single monom.rep_eq)
  have in_keys: \<open>keys (mapping_of (\<Sum>x\<in>I. MPoly_Type.monom x (h x))) = (\<Union>x \<in> I. (if h x  = 0 then {} else {x}))\<close>
   if \<open>finite I\<close> for I and h :: \<open>_ \<Rightarrow> int\<close> and x
   supply in_keysD[dest]
   using that apply (induction rule: finite_induct)
   apply (auto simp: plus_mpoly.rep_eq dest: in_keysD)
   apply (subst (asm) MPoly_Type_Class.keys_plus_eqI)
   apply (auto split: if_splits)
   apply (subst (asm) MPoly_Type_Class.keys_plus_eqI)
   apply (auto split: if_splits)
   apply (subst MPoly_Type_Class.keys_plus_eqI)
   apply (auto split: if_splits)
   apply (subst MPoly_Type_Class.keys_plus_eqI)
   apply (auto split: if_splits)
   done

  have H[simp]: \<open>vars ((\<Sum>x\<in>I. MPoly_Type.monom x (h x))) = (\<Union>x\<in>I. (if h x  = 0 then {} else keys x))\<close>
   if \<open>finite I\<close> for I and h :: \<open>_ \<Rightarrow> int\<close>
   using that by (auto simp: vars_def in_keys)

  have sums: \<open>(\<Sum>x\<in>I.
        MPoly_Type.monom (x + a') (c x)) =
       (\<Sum>x\<in> (\<lambda>x. x + a') ` I.
        MPoly_Type.monom x (c (x - a')))\<close>
    if \<open>finite I\<close> for I a' c q
    using that apply (induction rule: finite_induct)
    apply auto
    apply (subst sum.insert)
    apply auto
    done
  have non_zero_keysEx: \<open>p \<noteq> 0 \<Longrightarrow> \<exists>a. a \<in> keys (mapping_of p)\<close> for p :: \<open>int mpoly\<close>
     using mapping_of_inject by (fastforce simp add: ex_in_conv)
  have \<open>finite I\<close> \<open>keys (mapping_of p) \<subseteq> I\<close>
    unfolding I_def by auto
  then show
     \<open>vars (p * (monom (monomial (Suc 0) x') 1)) = (if p = 0 then {} else insert x' (vars p))\<close>
     apply (subst pv, subst I_def[symmetric], subst mult_monom)
     apply (auto simp: mult_monom sums I_def)
     using Poly_Mapping.keys_add vars_def apply fastforce
     apply (auto dest!: non_zero_keysEx)
     apply (rule_tac x= \<open>a + monomial (Suc 0) x'\<close> in bexI)
     apply (auto simp: coeff_keys)
     apply (simp add: in_keys_iff lookup_add)
     apply (auto simp: vars_def)
     apply (rule_tac x= \<open>xa + monomial (Suc 0) x'\<close> in bexI)
     apply (auto simp: coeff_keys)
     apply (simp add: in_keys_iff lookup_add)
     done
qed

lemma polynom_decomp_alien_var:
  fixes q A b :: \<open>int mpoly\<close>
  assumes
    q: \<open>q = A * (monom (monomial (Suc 0) x') 1) + b\<close> and
    x: \<open>x' \<notin> vars q\<close> \<open>x' \<notin> vars b\<close>
  shows
    \<open>A = 0\<close> and
    \<open>q = b\<close>
proof -
  let ?A = \<open>A * (monom (monomial (Suc 0) x') 1)\<close>
  have \<open>?A = q - b\<close>
    using arg_cong[OF q, of \<open>\<lambda>a. a - b\<close>]
    by auto
  moreover have \<open>x' \<notin> vars (q - b)\<close>
    using x vars_in_right_only
    by fastforce
  ultimately have \<open>x' \<notin> vars (?A)\<close>
    by simp
  then have \<open>?A = 0\<close>
    by (auto simp: vars_mult_monom split: if_splits)
  then show \<open>A = 0\<close>
    apply auto
    by (metis (full_types) empty_iff insert_iff mult_zero_right vars_mult_monom)
  then show \<open>q = b\<close>
    using q by auto
qed

lemma vars_unE: \<open>x \<in> vars (a * b) \<Longrightarrow> (x \<in> vars a \<Longrightarrow> thesis) \<Longrightarrow> (x \<in> vars b \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
   using vars_mult[of a b] by auto

lemma
  assumes \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    p_x_coeff: \<open>coeff p (monomial (Suc 0) x') = 1\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close> and
    q: \<open>q \<in> More_Modules.ideal (insert p (set_mset A \<union> polynom_bool))\<close> and
    leading: \<open>x' \<notin> vars (p - Var x')\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynom_bool)\<close>
proof -
  obtain r t where
    q: \<open>q = (\<Sum>a\<in>t. r a * a)\<close> and
    fin_t: \<open>finite t\<close> and
    t: \<open>t \<subseteq> insert p (set_mset A \<union> polynom_bool)\<close>
    using q unfolding ideal.span_explicit
    by auto

  define t' where \<open>t' \<equiv> t - {p}\<close>
  have t': \<open>t = (if p \<in> t then insert p t' else t')\<close> and
    t''[simp]: \<open>p \<notin> t'\<close>
    unfolding t'_def by auto
  show ?thesis
  proof (cases \<open>r p = 0 \<or> p \<notin> t\<close>)
    case True
    have
      q: \<open>q = (\<Sum>a\<in>t'. r a * a)\<close> and
     fin_t: \<open>finite t'\<close> and
      t: \<open>t' \<subseteq> set_mset A \<union> polynom_bool\<close>
      using q fin_t t True t''
      apply (subst (asm) t')
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def)
      using q fin_t t True t''
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def)
      done
    then show ?thesis
      by (auto simp: ideal.span_explicit)
  next
    case False
    then have \<open>r p \<noteq> 0\<close> and \<open>p \<in> t\<close>
      by auto
    then have t: \<open>t = insert p t'\<close>
      by (auto simp: t'_def)
    define p' where \<open>p' \<equiv> p - Var x'\<close>
    let ?v = \<open>Var x'\<close>
    have p_p': \<open>p = ?v + p'\<close>
      by (auto simp: p'_def)

   define pv' :: \<open>int mpoly\<close> where \<open>pv' = ?v * ?v - ?v\<close>
   define pv :: \<open>int mpoly\<close> where \<open>pv = (if pv' \<in> t then pv' else 0)\<close>

   define t'' where \<open>t'' = t - {p, pv}\<close>
   have \<open>MPoly_Type.coeff pv (monomial (Suc 0) x') \<noteq> 1\<close>
     by (auto simp: pv_def pv'_def coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def
       times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
   then have [iff]: \<open>pv' \<noteq> p\<close>
     using False p_x_coeff
     by (auto simp: pv_def)

   have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
     by (auto simp: pv_def pv'_def coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
       times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
   then have \<open>\<forall>a. \<exists>g h. r a = ?v * g + h \<and> x' \<notin> vars h\<close>
     using polynom_split_on_var[of \<open>r _\<close> x']
     by metis
   then obtain g h where
     r: \<open>r a = ?v * g a + h a\<close> and
     x'_h: \<open>x' \<notin> vars (h a)\<close> for a
     using polynom_split_on_var[of \<open>r a\<close> x']
     by metis

  have eq2: \<open>(\<Sum>a\<in>t'. h a * a) = (\<Sum>a\<in>(t' - {pv'}). h a * a) + (if pv' \<in> t' then h pv' * (?v - 1) else 0) * ?v\<close>
    (is \<open>_ = ?NOx' + ?bx' * ?v\<close>)
    apply (cases \<open>pv' \<in> t'\<close>)
    by (subst sum.remove[of _ pv']) (use fin_t in \<open>auto simp: t pv'_def field_simps\<close>)

  have q1: \<open>q = (\<Sum>a\<in>t'. ?v * g a * a) + (\<Sum>a\<in>t'. h a * a) + ?v * g p * p' + h p * p' + r p * ?v\<close>
    using fin_t t'' unfolding q t r
    by (auto simp: field_simps comm_monoid_add_class.sum.distrib p_p')
  also have q1: \<open>... = (\<Sum>a\<in>t'. ?v * g a * a) + ?NOx' + ?bx' * ?v + g p * p' * ?v + h p * p' + r p * ?v\<close>
    using fin_t unfolding q t r eq2
    by (auto simp: field_simps comm_monoid_add_class.sum.distrib)
  also have \<open>... = (r p + (\<Sum>a\<in>t'. g a * a) + ?bx' + g p * p') * ?v + (h p * p' + ?NOx')\<close> (is \<open>_ = ?X' * ?v' + ?NOx''\<close>)
    by (auto simp: field_simps sum_distrib_left r)
  finally have q_decomp: \<open>q = ?X' * ?v' + ?NOx''\<close>
   .


  have [iff]: \<open>monomial (Suc 0) c = 0 - monomial (Suc 0) c = False\<close> for c
    by (metis One_nat_def diff_is_0_eq' le_eq_less_or_eq less_Suc_eq_le monomial_0_iff single_diff zero_neq_one)

  have [simp]: \<open>vars ((Var c)\<^sup>2 - Var c :: int mpoly) = {c}\<close> for c
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq split: if_splits)
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq when_def ac_simps adds_def lookup_plus_fun
      power2_eq_square times_mpoly.rep_eq minus_mpoly.rep_eq split: if_splits)
    apply (rule_tac x = \<open>(2 :: nat \<Rightarrow>\<^sub>0 nat) * monomial (Suc 0) c\<close> in exI)
    apply (auto dest: monomial_0D simp: plus_eq_zero_2 lookup_plus_fun mult_2)
    by (meson Suc_neq_Zero monomial_0D plus_eq_zero_2)

  have [simp]: \<open>x' \<in> vars m \<Longrightarrow> m \<in> polynom_bool \<Longrightarrow> m = pv'\<close> for m
    by (auto simp: polynom_bool_def pv'_def semiring_normalization_rules(29))

   have ISABELLE_COME_ON1: \<open>m\<in>t' - {pv'} \<Longrightarrow> x' \<notin> vars (h m * m)\<close> for m
     using fin_t x'_h vars_mult[of \<open>h m\<close> m]
       \<open>t \<subseteq> insert p (set_mset A \<union> polynom_bool)\<close>
       assms(2,3)
     apply (auto simp: elim!: vars_unE)
     apply (cases \<open>m \<in># A\<close>)
     apply auto
     apply (cases \<open>m \<in> polynom_bool\<close>)
     apply (auto)
     using t'_def by blast

   have \<open>x' \<notin> (\<Union>m\<in>t' - {pv'}. vars (h m * m))\<close>
     using fin_t x'_h vars_mult[of \<open>h _\<close>]
       \<open>t \<subseteq> insert p (set_mset A \<union> polynom_bool)\<close>
       ISABELLE_COME_ON1
     by (auto simp: pv'_def)
   then have \<open>x' \<notin> vars ?NOx'\<close>
     using vars_setsum[of \<open>t' - {pv'}\<close> \<open>\<lambda>a. h a * a\<close>] fin_t x'_h
       \<open>t \<subseteq> insert p (set_mset A \<union> polynom_bool)\<close>
     by (auto simp: t)

  moreover {
    have \<open>x' \<notin> vars p'\<close>
      using assms(7)
      unfolding p'_def
      by auto
    then have \<open>x' \<notin> vars (h p * p')\<close>
      using vars_mult[of \<open>h p\<close> p'] x'_h
      by auto
  }
  ultimately have
    \<open>x' \<notin> vars q\<close>
    \<open>x' \<notin> vars ?NOx''\<close>
    using x' vars_q vars_add[of \<open>h p * p'\<close> \<open>\<Sum>a\<in>t'. h a * a\<close>] x'_h
    apply auto
    by (meson UnE in_mono vars_add)
  then have \<open>?X' = 0\<close> and q_decomp: \<open>q = ?NOx''\<close>
    unfolding mon[symmetric]
    by (rule polynom_decomp_alien_var[OF q_decomp[unfolded mon[symmetric]]])+

  then have \<open>r p = - ?bx' + (\<Sum>a\<in>t'. (- g a) * a) - (g p * p')\<close>
    (is \<open>_ = ?pv + ?CL - ?p'\<close>)
    unfolding add.assoc add_eq_0_iff equation_minus_iff
    by (auto simp: sum_negf ac_simps)

thm q_decomp
  then have \<open>r p = (\<Sum>a\<in>t'. (- g a) * a)\<close>
    sorry

  then have rpp: \<open>r p * p = (\<Sum>a\<in>t'. (- g a * p) * a)\<close>
    by (auto simp: sum_distrib_left ac_simps)

  have \<open>q = (\<Sum>a\<in>t'. (r a + - g a * p) * a)\<close>
    using fin_t unfolding q
    by (auto simp: t rpp q
         comm_monoid_add_class.sum.distrib[symmetric]
        intro!: sum.cong)
     (auto simp: field_simps)

  then show ?thesis
    using fin_t \<open>t \<subseteq> insert p (set_mset A \<union> polynom_bool)\<close>
    by (force simp: ideal.span_explicit t)
  qed
qed


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
    apply (auto simp: pac_ideal_def vars_add)

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