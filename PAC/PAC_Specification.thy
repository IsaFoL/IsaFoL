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
extend:
  \<open>PAC_Format (\<V>, A) (\<V> \<union> {x \<in> vars p'. x \<notin> \<V>}, add_mset p' A)\<close>
  if
    \<open>x \<in> vars p'\<close>
    \<open>coeff p' (Poly_Mapping.single x 1) = 1\<close>
    \<open>(p' - Var x)^2 - (p' - Var x) = 0\<close>
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



lemma ideal_insert':
  \<open>More_Modules.ideal (insert a S) = {y. \<exists>x k. y = x + k * a \<and> x \<in> More_Modules.ideal S}\<close>
    apply (auto simp: pac_ideal_def ideal.span_insert
      intro: exI[of _ \<open>_ - k * a\<close>])
   apply (rule_tac x = \<open>x - k * a\<close> in exI)
   apply auto
   apply (rule_tac x = \<open>k\<close> in exI)
   apply auto
   done


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


lemma polynom_split_on_var2:
  fixes p :: \<open>int mpoly\<close>
  assumes \<open>x' \<notin> vars s\<close>
  obtains q r where
    \<open>p = (monom (monomial (Suc 0) x') 1 - s) * q + r\<close> and
    \<open>x' \<notin> vars r\<close>
proof -
  have eq[simp]: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
    by (simp add: Var.abs_eq Var\<^sub>0_def monom.abs_eq)
  have \<open>\<forall>m \<le> n. \<forall>P::int mpoly. degree P x' < m \<longrightarrow> (\<exists>A B. P = (Var x' - s) * A + B \<and> x' \<notin> vars B)\<close> for n
  proof (induction n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then have IH: \<open>m\<le>n \<Longrightarrow> MPoly_Type.degree P x' < m \<Longrightarrow>
              (\<exists>A B. P = (Var x' - s) * A + B \<and> x' \<notin> vars B)\<close> for m P
      by fast
    show ?case
    proof (intro allI impI)
     fix m and P :: \<open>int mpoly\<close>
     assume \<open>m \<le> Suc n\<close> and deg: \<open>MPoly_Type.degree P x' < m\<close>
     consider
       \<open>m \<le> n\<close> |
       \<open>m = Suc n\<close>
       using \<open>m \<le> Suc n\<close> by linarith
     then show \<open>\<exists>A B. P = (Var x' - s) * A + B \<and> x' \<notin> vars B\<close>
     proof cases
       case 1
       then show \<open>?thesis\<close>
         using Suc deg by blast
     next
       case [simp]: 2
       obtain A B where
         P: \<open>P = Var x' * A + B\<close> and
         \<open>x' \<notin> vars B\<close>
         using polynom_split_on_var[of P x'] unfolding eq by blast
       have P': \<open>P = (Var x' - s) * A + (s * A + B)\<close>
         by (auto simp: field_simps P)
       have \<open>A = 0 \<or> degree (s * A) x' < degree P x'\<close>
         using deg \<open>x' \<notin> vars B\<close> \<open>x' \<notin> vars s\<close> degree_times_le[of s A x'] deg
         unfolding P
         by (auto simp: degree_sum_notin degree_mult_Var' degree_mult_Var degree_notin_vars
           split: if_splits)
       then obtain A' B' where
         sA: \<open>s*A = (Var x' - s) * A' + B'\<close> and
         \<open>x' \<notin> vars B'\<close>
         using IH[of \<open>m-1\<close> \<open>s*A\<close>] deg apply auto
         by (metis \<open>x' \<notin> vars B\<close> add.right_neutral mult_zero_right vars_in_right_only)
       have \<open>P = (Var x' - s) * (A + A') + (B' + B)\<close>
         unfolding P' sA by (auto simp: field_simps)
       moreover have \<open>x' \<notin> vars (B' + B)\<close>
         using \<open>x' \<notin> vars B'\<close>  \<open>x' \<notin> vars B\<close>
         by (meson UnE subset_iff vars_add)
       ultimately show ?thesis
         by fast
     qed
   qed
  qed
  then show ?thesis
    using that unfolding eq
    by blast
qed

lemma polynom_split_on_var_diff_sq2:
 fixes p :: \<open>int mpoly\<close>
  obtains q r s where
    \<open>p = monom (monomial (Suc 0) x') 1 * q + r + s * (monom (monomial (Suc 0) x') 1^2 - monom (monomial (Suc 0) x') 1)\<close> and
    \<open>x' \<notin> vars r\<close> and
    \<open>x' \<notin> vars q\<close>
proof -
  let ?v = \<open>monom (monomial (Suc 0) x') 1 :: int mpoly\<close>
  have H: \<open>n < m \<Longrightarrow> n > 0 \<Longrightarrow> \<exists>q. ?v^n = ?v + q * (?v^2 - ?v)\<close> for n m :: nat
  proof (induction m arbitrary: n)
    case 0
    then show ?case by auto
  next
    case (Suc m n) note IH = this(1-)
    consider
      \<open>n < m\<close> |
      \<open>m = n\<close> \<open>n > 1\<close> |
      \<open>n = 1\<close>
      using IH
      by (cases \<open>n < m\<close>; cases n) auto
    then show ?case
    proof cases
      case 1
      then show ?thesis using IH by auto
    next
      case 2
      have eq: \<open>?v^(n) = ((?v :: int mpoly) ^ (n-2)) * (?v^2-?v) + ?v^(n-1)\<close>
        using 2 by (auto simp: field_simps power_eq_if
          ideal.scale_right_diff_distrib)
      obtain q where
        q: \<open>?v^(n-1) = ?v + q * (?v^2 - ?v)\<close>
        using IH(1)[of \<open>n-1\<close>] 2
        by auto
      show ?thesis
        using q unfolding eq
        by (auto intro!: exI[of _ \<open>?v ^ (n - 2) + q\<close>] simp: distrib_right)
    next
      case 3
      then show \<open>?thesis\<close>
        by auto
    qed
  qed
  have H: \<open>n>0 \<Longrightarrow> \<exists>q. ?v^n = ?v + q * (?v^2-?v)\<close> for n
    using H[of n \<open>n+1\<close>]
    by auto
  obtain qr :: \<open>nat \<Rightarrow> int mpoly\<close> where
     qr: \<open>n > 0 \<Longrightarrow> ?v^n = ?v + qr n * (?v^2-?v)\<close> for n
   using H[of ]
   by metis
  have vn: \<open>(if lookup x x' = 0 then 1 else Var x' ^ lookup x x') =
    (if lookup x x' = 0 then 1 else ?v) + (if lookup x x' = 0 then 0 else 1) * qr (lookup x x') * (?v^2-?v)\<close> for x
    by (simp add: qr[symmetric] Var_def Var\<^sub>0_def monom.abs_eq[symmetric] cong: if_cong)

  have q: \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close>
    by (rule polynom_sum_monoms(1)[of p])
  have [simp]:
    \<open>lookup x x' = 0 \<Longrightarrow>
    Abs_poly_mapping (\<lambda>k. lookup x k when k \<noteq> x') = x\<close> for x
    by (cases x, auto simp: poly_mapping.Abs_poly_mapping_inject)
      (auto intro!: ext simp: when_def)
  have [simp]: \<open>finite {x. 0 < (a when x' = x)}\<close> for a :: nat
    by (metis (no_types, lifting) infinite_nat_iff_unbounded less_not_refl lookup_single lookup_single_not_eq mem_Collect_eq)

  have [simp]: \<open>((\<lambda>x. x + monomial (Suc 0) x') ^^ (n))
     (monomial (Suc 0) x') = Abs_poly_mapping (\<lambda>k. (if k = x' then n+1 else 0))\<close> for n
    by (induction n)
     (auto simp: single_def Abs_poly_mapping_inject plus_poly_mapping.abs_eq eq_onp_def cong:if_cong)
  have [simp]: \<open>0 < lookup x x' \<Longrightarrow>
    Abs_poly_mapping (\<lambda>k. lookup x k when k \<noteq> x') +
    Abs_poly_mapping (\<lambda>k. if k = x' then lookup x x' - Suc 0 + 1 else 0) =
    x\<close> for x
    apply (cases x, auto simp: poly_mapping.Abs_poly_mapping_inject plus_poly_mapping.abs_eq eq_onp_def)
    apply (subst plus_poly_mapping.abs_eq)
    apply (auto simp: poly_mapping.Abs_poly_mapping_inject plus_poly_mapping.abs_eq eq_onp_def)
    apply (metis (no_types, lifting) finite_nat_set_iff_bounded less_numeral_extra(3) mem_Collect_eq when_neq_zero zero_less_iff_neq_zero)
    apply (subst Abs_poly_mapping_inject)
    apply auto
    apply (metis (no_types, lifting) finite_nat_set_iff_bounded less_numeral_extra(3) mem_Collect_eq when_neq_zero zero_less_iff_neq_zero)
    done
  define f where
    \<open>f x = (MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x)) *
      (if lookup x x' = 0 then 1 else Var x' ^ (lookup x x'))\<close> for x
  have f_alt_def: \<open>f x = MPoly_Type.monom x (MPoly_Type.coeff p x)\<close> for x
    by (auto simp: f_def monom_def remove_key_def Var_def MPoly_monomial_power Var\<^sub>0_def
      mpoly.MPoly_inject monomial_inj times_mpoly.abs_eq
      times_mpoly.abs_eq mult_single)
  have p: \<open>p = (\<Sum>x\<in>keys (mapping_of p).
       MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x) *
       (if lookup x x' = 0 then 1 else ?v)) +
          (\<Sum>x\<in>keys (mapping_of p).
       MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x) *
       (if lookup x x' = 0 then 0
        else 1) * qr (lookup x x')) *
             (?v\<^sup>2 - ?v)\<close>
    (is \<open>_ = ?a + ?v2v\<close>)
    apply (subst q)
    unfolding f_alt_def[symmetric, abs_def] f_def vn semiring_class.distrib_left
      comm_semiring_1_class.semiring_normalization_rules(18) semiring_0_class.sum_distrib_right
    by (simp add: semiring_class.distrib_left
      sum.distrib)

  have I: \<open>keys (mapping_of p) = {x \<in> keys (mapping_of p). lookup x x' = 0} \<union> {x \<in> keys (mapping_of p). lookup x x' \<noteq> 0}\<close>
    by auto

  have \<open>p = (\<Sum>x | x \<in> keys (mapping_of p) \<and> lookup x x' = 0.
       MPoly_Type.monom x (MPoly_Type.coeff p x)) +
    (\<Sum>x | x \<in> keys (mapping_of p) \<and> lookup x x' \<noteq> 0.
       MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x)) *
       (MPoly_Type.monom (monomial (Suc 0) x') 1) +
     (\<Sum>x | x \<in> keys (mapping_of p) \<and> lookup x x' \<noteq> 0.
        MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x) *
        qr (lookup x x')) *
             (?v\<^sup>2 - ?v)\<close>
    (is \<open>p = ?A + ?B * _ + ?C * _\<close>)
    unfolding semiring_0_class.sum_distrib_right[of _ _ \<open>(MPoly_Type.monom (monomial (Suc 0) x') 1)\<close>]
    apply (subst p)
    apply (subst (2)I)
    apply (subst I)
    apply (subst comm_monoid_add_class.sum.union_disjoint)
    apply auto[3]
    apply (subst comm_monoid_add_class.sum.union_disjoint)
    apply auto[3]
    apply (subst (4) sum.cong[OF refl, of _ _ \<open>\<lambda>x. MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x) *
        qr (lookup x x')\<close>])
    apply (auto; fail)
    apply (subst (3) sum.cong[OF refl, of _ _ \<open>\<lambda>x. 0\<close>])
    apply (auto; fail)
    apply (subst (2) sum.cong[OF refl, of _ _ \<open>\<lambda>x. MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x) *
       (MPoly_Type.monom (monomial (Suc 0) x') 1)\<close>])
    apply (auto; fail)
    apply (subst (1) sum.cong[OF refl, of _ _ \<open>\<lambda>x. MPoly_Type.monom x (MPoly_Type.coeff p x)\<close>])
    apply (auto)
    by (smt f_alt_def f_def mult_cancel_left1)

  moreover have \<open>x' \<notin> vars ?A\<close>
    using vars_setsum[of \<open>{x \<in> keys (mapping_of p). lookup x x' = 0}\<close>
      \<open>\<lambda>x. MPoly_Type.monom x (MPoly_Type.coeff p x)\<close>]
    apply auto
    apply (drule set_rev_mp, assumption)
    apply (auto dest!: lookup_eq_zero_in_keys_contradict)
    by (meson lookup_eq_zero_in_keys_contradict subsetD vars_monom_subset)
  moreover have \<open>x' \<notin> vars ?B\<close>
    using vars_setsum[of \<open>{x \<in> keys (mapping_of p). lookup x x' \<noteq> 0}\<close>
      \<open>\<lambda>x. MPoly_Type.monom (remove_key x' x) (MPoly_Type.coeff p x)\<close>]
    apply auto
    apply (drule set_rev_mp, assumption)
    apply (auto dest!: lookup_eq_zero_in_keys_contradict)
    apply (drule subsetD[OF vars_monom_subset])
    apply (auto simp: remove_key_keys[symmetric])
    done
  ultimately show ?thesis apply -
    apply (rule that[of ?B ?A ?C])
    apply (auto simp: ac_simps)
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

lemma polynom_decomp_alien_var2:
  fixes q A b :: \<open>int mpoly\<close>
  assumes
    q: \<open>q = A * (monom (monomial (Suc 0) x') 1 + p) + b\<close> and
    x: \<open>x' \<notin> vars q\<close> \<open>x' \<notin> vars b\<close> \<open>x' \<notin> vars p\<close>
  shows
    \<open>A = 0\<close> and
    \<open>q = b\<close>
proof -
  let ?x = \<open>monom (monomial (Suc 0) x') 1\<close>
  have x'[simp]: \<open>?x = Var x'\<close>
    by (simp add: Var.abs_eq Var\<^sub>0_def monom.abs_eq)
  have \<open>\<exists>n Ax A'. A = ?x * Ax + A' \<and> x' \<notin> vars A' \<and> degree Ax x' = n\<close>
    using polynom_split_on_var[of A x'] by metis
  from wellorder_class.exists_least_iff[THEN iffD1, OF this] obtain Ax A' n where
    A: \<open>A = Ax * ?x + A'\<close> and
    \<open>x' \<notin> vars A'\<close> and
    n: \<open>MPoly_Type.degree Ax x' = n\<close> and
    H: \<open>\<And>m Ax A'. m < n \<longrightarrow>
                   A \<noteq> Ax * MPoly_Type.monom (monomial (Suc 0) x') 1 + A' \<or>
                   x' \<in> vars A' \<or> MPoly_Type.degree Ax x' \<noteq> m\<close>
    unfolding wellorder_class.exists_least_iff[of \<open>\<lambda>n. \<exists>Ax A'. A = Ax * ?x + A' \<and> x' \<notin> vars A' \<and>
      degree Ax x' = n\<close>]
    by (auto simp: field_simps)

  have \<open>q = (A + Ax * p) * monom (monomial (Suc 0) x') 1 + (p * A' + b)\<close>
    unfolding q A by (auto simp: field_simps)
  moreover have \<open>x' \<notin> vars q\<close> \<open>x' \<notin> vars (p * A' + b)\<close>
    using x \<open>x' \<notin> vars A'\<close> apply (auto elim!: )
    by (smt UnE add.assoc add.commute calculation subset_iff vars_in_right_only vars_mult)
  ultimately have \<open>A + Ax * p = 0\<close> \<open>q = p * A' + b\<close>
    by (rule polynom_decomp_alien_var)+

  have A': \<open>A' = -Ax * ?x - Ax * p\<close>
    using \<open>A + Ax * p = 0\<close> unfolding A
    by (metis (no_types, lifting) add_uminus_conv_diff eq_neg_iff_add_eq_0 minus_add_cancel mult_minus_left)

  have \<open>A = - (Ax * p)\<close>
    using A unfolding A'
    apply auto
    done

  obtain Axx Ax' where
    Ax: \<open>Ax = ?x * Axx + Ax'\<close> and
    \<open>x' \<notin> vars Ax'\<close>
    using polynom_split_on_var[of Ax x'] by metis

  have \<open>A = ?x * (- Axx * p) + (- Ax' * p)\<close>
    unfolding \<open>A = - (Ax * p)\<close> Ax
    by (auto simp: field_simps)

  moreover have \<open>x' \<notin> vars (-Ax' * p)\<close>
    using \<open>x' \<notin> vars Ax'\<close> by (metis (no_types, hide_lams) UnE add.right_neutral
      add_minus_cancel assms(4) subsetD vars_in_right_only vars_mult)
   moreover have \<open>Axx \<noteq> 0 \<Longrightarrow> MPoly_Type.degree (- Axx * p) x' < degree Ax x'\<close>
     using degree_times_le[of Axx p x'] x
     by (auto simp: Ax degree_sum_notin \<open>x' \<notin> vars Ax'\<close> degree_mult_Var'
       degree_notin_vars)
   ultimately have [simp]: \<open>Axx = 0\<close>
     using H[of \<open>MPoly_Type.degree (- Axx * p) x'\<close> \<open>- Axx * p\<close> \<open>- Ax' * p\<close>]
     by (auto simp: n)
  then have [simp]: \<open>Ax' = Ax\<close>
    using Ax by auto

  show \<open>A = 0\<close>
    using A \<open>A = - (Ax * p)\<close> \<open>x' \<notin> vars (- Ax' * p)\<close> \<open>x' \<notin> vars A'\<close> polynom_decomp_alien_var(1) by force
  then show \<open>q = b\<close>
    using q by auto
qed

lemma vars_unE: \<open>x \<in> vars (a * b) \<Longrightarrow> (x \<in> vars a \<Longrightarrow> thesis) \<Longrightarrow> (x \<in> vars b \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
   using vars_mult[of a b] by auto


lemma in_keys_minusI1:
  assumes "t \<in> keys p" and "t \<notin> keys q"
  shows "t \<in> keys (p - q)"
  using assms unfolding in_keys_iff lookup_minus by simp

lemma in_keys_minusI2:
  fixes t :: \<open>'a\<close> and q :: \<open>'a \<Rightarrow>\<^sub>0 'b :: {cancel_comm_monoid_add,group_add}\<close>
  assumes "t \<in> keys q" and "t \<notin> keys p"
  shows "t \<in> keys (p - q)"
  using assms unfolding in_keys_iff lookup_minus by simp

lemma extensions_are_safe:
  assumes \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    p_x_coeff: \<open>coeff p (monomial (Suc 0) x') = 1\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close> and
    q: \<open>q \<in> More_Modules.ideal (insert p (set_mset A \<union> polynom_bool))\<close> and
    leading: \<open>x' \<notin> vars (p - Var x')\<close> and
    diff: \<open>(Var x' - p)^2 - (Var x' - p) \<in> More_Modules.ideal polynom_bool\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynom_bool)\<close>
proof -
  define p' where \<open>p' \<equiv> p - Var x'\<close>
  let ?v = \<open>Var x' :: int mpoly\<close>
  have p_p': \<open>p = ?v + p'\<close>
    by (auto simp: p'_def)
  define q' where \<open>q' \<equiv> Var x' - p\<close>
  have q_q': \<open>p = ?v - q'\<close>
    by (auto simp: q'_def)
  have diff: \<open>q'^2 - q' \<in> More_Modules.ideal polynom_bool\<close>
    using diff unfolding q_q' by auto

  have [simp]: \<open>vars ((Var c)\<^sup>2 - Var c :: int mpoly) = {c}\<close> for c
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq split: if_splits)
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq when_def ac_simps adds_def lookup_plus_fun
      power2_eq_square times_mpoly.rep_eq minus_mpoly.rep_eq split: if_splits)
    apply (rule_tac x = \<open>(2 :: nat \<Rightarrow>\<^sub>0 nat) * monomial (Suc 0) c\<close> in exI)
    apply (auto dest: monomial_0D simp: plus_eq_zero_2 lookup_plus_fun mult_2)
    by (meson Suc_neq_Zero monomial_0D plus_eq_zero_2)


  have eq: \<open>More_Modules.ideal (insert p (set_mset A \<union> polynom_bool)) =
      More_Modules.ideal (insert p (set_mset A \<union> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}))\<close>
      (is \<open>?A = ?B\<close> is \<open>_ = More_Modules.ideal ?trimmed\<close>)
  proof -
     let ?C = \<open>insert p (set_mset A \<union> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'})\<close>
     let ?D = \<open>(\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
     have diff: \<open>q'^2 - q' \<in> More_Modules.ideal ?D\<close> (is \<open>?q \<in> _\<close>)
     proof -
       obtain r t where
         q: \<open>?q = (\<Sum>a\<in>t. r a * a)\<close> and
         fin_t: \<open>finite t\<close> and
         t: \<open>t \<subseteq> polynom_bool\<close>
         using diff unfolding ideal.span_explicit
         by auto
       show ?thesis
       proof (cases \<open>?v^2-?v \<notin> t\<close>)
         case True
         then show \<open>?thesis\<close>
           using q fin_t t unfolding ideal.span_explicit
           by (auto intro!: exI[of _ \<open>t - {?v^2 -?v}\<close>] exI[of _ r]
             simp: polynom_bool_def sum_diff1)
        next
          case False
          define t' where \<open>t' = t - {?v^2 - ?v}\<close>
          have t_t': \<open>t = insert (?v^2 - ?v) t'\<close> and
            notin: \<open>?v^2 - ?v \<notin> t'\<close> and
            \<open>t' \<subseteq> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
            using False t unfolding t'_def polynom_bool_def by auto
          have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
            by (auto simp: coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
              times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
          then have \<open>\<forall>a. \<exists>g h. r a = ?v * g + h \<and> x' \<notin> vars h\<close>
            using polynom_split_on_var[of \<open>r _\<close> x']
            by metis
          then obtain g h where
            r: \<open>r a = ?v * g a + h a\<close> and
            x'_h: \<open>x' \<notin> vars (h a)\<close> for a
            using polynom_split_on_var[of \<open>r a\<close> x']
            by metis
          have  \<open>?q = ((\<Sum>a\<in>t'. g a * a) + r (?v^2-?v) * (?v - 1)) * ?v + (\<Sum>a\<in>t'. h a * a)\<close>
            using fin_t notin unfolding t_t' q r
            by (auto simp: field_simps comm_monoid_add_class.sum.distrib
              power2_eq_square ideal.scale_left_commute sum_distrib_left)
          moreover have \<open>x' \<notin> vars ?q\<close>
            by (metis (no_types, hide_lams) Groups.add_ac(2) Un_iff add_diff_cancel_left'
              diff_minus_eq_add in_mono leading q'_def semiring_normalization_rules(29)
              vars_in_right_only vars_mult)
          moreover {
            have \<open>x' \<notin> (\<Union>m\<in>t' - {?v^2-?v}. vars (h m * m))\<close>
              using fin_t x'_h vars_mult[of \<open>h _\<close>] \<open>t \<subseteq> polynom_bool\<close>
              by (auto simp: polynom_bool_def t_t' elim!: vars_unE)
            then have \<open>x' \<notin> vars (\<Sum>a\<in>t'. h a * a)\<close>
              using vars_setsum[of \<open>t'\<close> \<open>\<lambda>a. h a * a\<close>] fin_t x'_h t notin
              by (auto simp: t_t')
          }
          ultimately have \<open>?q = (\<Sum>a\<in>t'. h a * a)\<close>
            unfolding mon[symmetric]
            by (rule polynom_decomp_alien_var(2)[unfolded])
          then show ?thesis
            using t fin_t \<open>t' \<subseteq> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
            unfolding ideal.span_explicit t_t'
            by auto
       qed
    qed
    have eq1: \<open>More_Modules.ideal (insert p (set_mset A \<union> polynom_bool)) =
      More_Modules.ideal (insert (?v^2 - ?v) ?C)\<close>
      (is \<open>More_Modules.ideal _ = More_Modules.ideal (insert _ ?C)\<close>)
      by (rule arg_cong[of _ _ More_Modules.ideal])
       (auto simp: polynom_bool_def)
    moreover have \<open>?v^2 - ?v \<in> More_Modules.ideal ?C\<close>
    proof -
      have \<open>?v - q' \<in> More_Modules.ideal ?C\<close>
        by (auto simp: q_q' ideal.span_base)
      from ideal.span_scale[OF this, of \<open>?v + q' - 1\<close>] have \<open>(?v - q') * (?v + q' - 1) \<in> More_Modules.ideal ?C\<close>
        by (auto simp: field_simps)
      moreover have \<open>q'^2 - q' \<in> More_Modules.ideal ?C\<close>
        using diff by (smt Un_insert_right ideal.span_mono insert_subset subsetD sup_ge2)
      ultimately have \<open>(?v - q') * (?v + q' - 1) + (q'^2 - q') \<in> More_Modules.ideal ?C\<close>
        by (rule ideal.span_add)
      moreover have \<open>?v^2 - ?v = (?v - q') * (?v + q' - 1) + (q'^2 - q')\<close>
        by (auto simp: p'_def q_q' field_simps power2_eq_square)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis
      using ideal.span_insert_idI by blast
  qed

  have \<open>n < m \<Longrightarrow> n > 0 \<Longrightarrow> \<exists>q. ?v^n = ?v + q * (?v^2 - ?v)\<close> for n m :: nat
  proof (induction m arbitrary: n)
    case 0
    then show ?case by auto
  next
    case (Suc m n) note IH = this(1-)
    consider
      \<open>n < m\<close> |
      \<open>m = n\<close> \<open>n > 1\<close> |
      \<open>n = 1\<close>
      using IH
      by (cases \<open>n < m\<close>; cases n) auto
    then show ?case
    proof cases
      case 1
      then show ?thesis using IH by auto
    next
      case 2
      have eq: \<open>?v^(n) = ((?v :: int mpoly) ^ (n-2)) * (?v^2-?v) + ?v^(n-1)\<close>
        using 2 by (auto simp: field_simps power_eq_if
          ideal.scale_right_diff_distrib)
      obtain q where
        q: \<open>?v^(n-1) = ?v + q * (?v^2 - ?v)\<close>
        using IH(1)[of \<open>n-1\<close>] 2
        by auto
      show ?thesis
        using q unfolding eq
        by (auto intro!: exI[of _ \<open>Var x' ^ (n - 2) + q\<close>] simp: distrib_right)
    next
      case 3
      then show \<open>?thesis\<close>
        by auto
    qed
  qed

  obtain r t where
    q: \<open>q = (\<Sum>a\<in>t. r a * a)\<close> and
    fin_t: \<open>finite t\<close> and
    t: \<open>t \<subseteq> ?trimmed\<close>
    using q unfolding eq unfolding ideal.span_explicit
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
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def polynom_bool_def)
      done
    then show ?thesis
      by (auto simp: ideal.span_explicit)
  next
    case False
    then have \<open>r p \<noteq> 0\<close> and \<open>p \<in> t\<close>
      by auto
    then have t: \<open>t = insert p t'\<close>
      by (auto simp: t'_def)

   have \<open>x' \<notin> vars (- p')\<close>
     using leading p'_def vars_in_right_only by fastforce
   have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
     by (auto simp:coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
       times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
   then have \<open>\<forall>a. \<exists>g h. r a = (?v + p') * g + h \<and> x' \<notin> vars h\<close>
     using polynom_split_on_var2[of x' \<open>-p'\<close> \<open>r _\<close>]  \<open>x' \<notin> vars (- p')\<close>
     by (metis diff_minus_eq_add)
   then obtain g h where
     r: \<open>r a = p * g a + h a\<close> and
     x'_h: \<open>x' \<notin> vars (h a)\<close> for a
     using polynom_split_on_var2[of x' p' \<open>r a\<close>] unfolding p_p'[symmetric]
     by metis


  have ISABLLE_come_on: \<open>a * (p * g a) = p * (a * g a)\<close> for a
    by auto
  have q1: \<open>q = p * (\<Sum>a\<in>t'. g a * a) + (\<Sum>a\<in>t'. h a * a) + p * r p\<close>
    (is \<open>_ = _ + ?NOx' + _\<close>)
    using fin_t t'' unfolding q t ISABLLE_come_on r
    apply (subst semiring_class.distrib_right)+
    apply (auto simp: comm_monoid_add_class.sum.distrib semigroup_mult_class.mult.assoc
      ISABLLE_come_on simp flip: semiring_0_class.sum_distrib_right
         semiring_0_class.sum_distrib_left)
    by (auto simp: field_simps)
  also have \<open>... = ((\<Sum>a\<in>t'. g a * a) + r p) * p + (\<Sum>a\<in>t'. h a * a)\<close>
    by (auto simp: field_simps)
  finally have q_decomp: \<open>q = ((\<Sum>a\<in>t'. g a * a) + r p) * p + (\<Sum>a\<in>t'. h a * a)\<close>
    (is \<open>q = ?X * p + ?NOx'\<close>).


   have [iff]: \<open>monomial (Suc 0) c = 0 - monomial (Suc 0) c = False\<close> for c
     by (metis One_nat_def diff_is_0_eq' le_eq_less_or_eq less_Suc_eq_le monomial_0_iff single_diff zero_neq_one)
  have \<open>x \<in> t' \<Longrightarrow> x' \<in> vars x \<Longrightarrow> False\<close> for x
    using  \<open>t \<subseteq> ?trimmed\<close> t assms(2,3)
    apply (auto simp: polynom_bool_def dest!: multi_member_split)
    apply (frule set_rev_mp)
    apply assumption
    apply (auto dest!: multi_member_split)
    done
   then have \<open>x' \<notin> (\<Union>m\<in>t'. vars (h m * m))\<close>
     using fin_t x'_h vars_mult[of \<open>h _\<close>]
     by (auto simp: t elim!: vars_unE)
   then have \<open>x' \<notin> vars ?NOx'\<close>
     using vars_setsum[of \<open>t'\<close> \<open>\<lambda>a. h a * a\<close>] fin_t x'_h
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
    \<open>x' \<notin> vars ?NOx'\<close>
    \<open>x' \<notin> vars p'\<close>
    using x' vars_q vars_add[of \<open>h p * p'\<close> \<open>\<Sum>a\<in>t'. h a * a\<close>] x'_h
      leading p'_def
    by auto
  then have \<open>?X = 0\<close> and q_decomp: \<open>q = ?NOx'\<close>
    unfolding mon[symmetric] p_p'
    using polynom_decomp_alien_var2[OF q_decomp[unfolded p_p' mon[symmetric]]]
    by auto

  then have \<open>r p = (\<Sum>a\<in>t'. (- g a) * a)\<close>
    (is \<open>_ = ?CL\<close>)
    unfolding add.assoc add_eq_0_iff equation_minus_iff
    by (auto simp: sum_negf ac_simps)


  then have q2: \<open>q = (\<Sum>a\<in>t'. a * (r a - p * g a))\<close>
    using fin_t unfolding q
    apply (auto simp: t r q
         comm_monoid_add_class.sum.distrib[symmetric]
         sum_distrib_left
         sum_distrib_right
         left_diff_distrib
        intro!: sum.cong)
    apply (auto simp: field_simps)
    done
  then show \<open>?thesis\<close>
    using t fin_t \<open>t \<subseteq> ?trimmed\<close> unfolding ideal.span_explicit
    by (auto intro!: exI[of _ t'] exI[of _ \<open>\<lambda>a. r a - p * g a\<close>]
      simp: field_simps polynom_bool_def)
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