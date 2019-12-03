theory PAC_Specification
  imports PAC_More_Poly
begin

inductive_set my_ideal :: \<open>'a :: {plus,times} set \<Rightarrow> 'a set\<close> for A :: \<open>'a set\<close> where
  \<open>a \<in> A \<Longrightarrow> a \<in> my_ideal A\<close> |
  \<open>a \<in> my_ideal A \<Longrightarrow> b \<in> my_ideal A \<Longrightarrow> a + b \<in> my_ideal A\<close>|
  \<open>a \<in> my_ideal A \<Longrightarrow> a*b \<in> my_ideal A\<close>

type_synonym int_poly = \<open>int mpoly\<close>
definition polynom_bool :: \<open>int_poly set\<close> where
  \<open>polynom_bool = (\<lambda>c. Var c ^ 2 - Var c) ` UNIV\<close>

abbreviation poly_partial_object :: \<open>int_poly partial_object\<close> where
  \<open>poly_partial_object \<equiv> \<lparr>carrier = UNIV\<rparr>\<close>

abbreviation poly_monoid :: \<open>int_poly monoid\<close> where
  \<open>poly_monoid \<equiv> partial_object.extend poly_partial_object \<lparr>mult = (*), one = 1\<rparr>\<close>

abbreviation poly_ring_scheme where
  \<open>poly_ring_scheme \<equiv> monoid.extend poly_monoid \<lparr>zero = 0, add = (+)\<rparr>\<close>

definition pac_ideal where
  \<open>pac_ideal A = Ideal.genideal poly_ring_scheme (A \<union> polynom_bool)\<close>

lemma
  fixes A :: \<open>(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1) set\<close>
  assumes \<open>p \<in> ideal A\<close>
  shows \<open>p * q \<in> ideal A\<close>
  by (metis assms ideal.span_scale semiring_normalization_rules(7))

lemma genidealI1:
  \<open>x \<in> A \<Longrightarrow> x \<in> Ideal.genideal p A\<close>
  unfolding pac_ideal_def genideal_def
  by auto

lemma X2_X_in_pac_ideal:
  \<open>Var c ^ 2 - Var c \<in> pac_ideal A\<close>
  unfolding polynom_bool_def pac_ideal_def
  by (auto intro: genidealI1)

lemma pac_idealI1[intro]:
  \<open>p \<in> A \<Longrightarrow> p \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  by (auto intro: genidealI1)

lemma [simp]:
  \<open>carrier (partial_object.extend a b) = carrier a\<close>
  \<open>carrier (monoid.extend a' b) = carrier a'\<close>
  \<open>mult (monoid.extend a' b) = mult a'\<close>
  \<open>mult (partial_object.extend poly_partial_object \<lparr>mult = m, one = one'\<rparr>) = m\<close>
  \<open>one (partial_object.extend poly_partial_object \<lparr>mult = m, one = one'\<rparr>) = one'\<close>
  \<open>add (monoid.extend poly_monoid \<lparr>zero = z'', add = a''\<rparr>) = a''\<close>
  \<open>zero (monoid.extend poly_monoid \<lparr>zero = z'', add = a''\<rparr>) = z''\<close>
  \<open>one (poly_ring_scheme) = 1\<close>
  apply (auto simp: partial_object.defs monoid.extend_def)
  done

lemma [simp]:
  \<open>carrier poly_ring_scheme = UNIV\<close>
  \<open>mult poly_ring_scheme = (*)\<close>
  \<open>add poly_ring_scheme = (+)\<close>
  \<open>a_inv poly_ring_scheme = uminus\<close>
  \<open>one poly_ring_scheme = 1\<close>
  apply (auto simp: a_inv_def m_inv_def)
  unfolding m_inv_def
  apply (auto intro!: ext the_equality simp: ac_simps add_eq_0_iff)
  done


lemma ring_poly_ring_scheme[intro]:
  \<open>ring poly_ring_scheme\<close>
  by standard
   (auto simp: field_simps Units_def intro: exI[of _ \<open>-_\<close>])

lemma pac_idealI3[intro]:
  \<open>p \<in> A \<Longrightarrow> p*q \<in> pac_ideal A\<close>
  using ideal.I_r_closed[of _ poly_ring_scheme p q]
  by (auto simp: pac_ideal_def genideal_def dest: ideal.I_r_closed)

(*
lemma \<open>Ideal.ideal A p \<Longrightarrow> x \<in> carrier p \<Longrightarrow> (add p) x y \<in> carrier p \<longleftrightarrow> y \<in> carrier p\<close>
  using ring.ring_simprules(1)[of p \<open>x\<close> y]
    ring.ring_simprules(1)[of p \<open>(a_inv p x)\<close> \<open>add p x y\<close>]
    ring.ring_simprules(18)[of p x y]
  ring.ring_simprules(3)[of p \<open>x\<close>]
  apply (auto simp: Ideal.ideal.axioms(2))
  apply (auto simp: ring.ring_simprules ac_simps)
  
  oops
  thm ideal.span_add_eq
  find_theorems  Ideal.ideal
find_theorems ring a_inv
thm ring.ring_simprules(18-)
lemma pac_ideal_Xsq2_iff:
  \<open>Var c ^ 2 \<in> pac_ideal A \<longleftrightarrow> Var c \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  using ideal.I_r_closed[of _ poly_ring_scheme p q]
  apply (auto simp: pac_ideal_def genideal_def dest: ideal.I_r_closed)
  apply (subst (2) ideal.span_add_eq[symmetric, OF X2_X_in_pac_ideal[of c, unfolded pac_ideal_def]])
  apply auto
  done
*)


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
   \<open>p+q - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool\<close>
   \<open>vars p' \<subseteq> vars (p + q)\<close> |
mult:
  \<open>PAC_Format (\<V>, A) (\<V>, add_mset p' A)\<close>
if
   \<open>p \<in># A\<close>
   \<open>p*q - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool\<close>
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
      \<open>\<And>p q p'  A \<V>. p \<in># A \<Longrightarrow> q \<in># A \<Longrightarrow> p+q - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool \<Longrightarrow> vars p' \<subseteq> vars (p + q) \<Longrightarrow> P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p q p' A \<V>. p \<in># A \<Longrightarrow> p*q - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool \<Longrightarrow> vars p' \<subseteq> vars (p * q) \<Longrightarrow> vars q \<subseteq> \<V> \<Longrightarrow>
        P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p A \<V>. p \<in># A \<Longrightarrow> P \<V> A \<V> (A - {#p#})\<close>
      \<open>\<And>p' x. x \<in> vars p' \<Longrightarrow> coeff p' (Poly_Mapping.single x 1) = -1 \<or> coeff p' (Poly_Mapping.single x 1) = 1 \<Longrightarrow>
        x \<notin> \<V> \<Longrightarrow> P \<V> A (\<V> \<union> {x \<in> vars p'. x \<notin> \<V>}) (add_mset p' A)\<close>
  shows
     \<open>P \<V> A \<V>' A'\<close>
  using assms(1) apply -
  by (induct V\<equiv>\<V> A\<equiv>A \<V>' A' rule: PAC_Format_induct_split)
   (auto intro: assms(1) cases)

lemma IdealI2[intro]:
   assumes a2: "p \<in> Ideal.genideal poly_ring_scheme polynom_bool"
   shows \<open>p \<in> pac_ideal A\<close>
proof -
  show ?thesis
    using assms
    unfolding pac_ideal_def
    by (auto simp: genideal_def)
qed

lemma ideal_a_closed:
  \<open>Ideal.ideal A p \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> add p x y \<in> A\<close>
  unfolding pac_ideal_def
  using
    ring.ring_simprules(1)[of p x y]
  by (auto simp: Ideal.ideal.axioms(2) additive_subgroup.a_closed ideal_def)

lemma ideal_a_inv_closed:
  \<open>Ideal.ideal A p \<Longrightarrow> x \<in> carrier p \<Longrightarrow> a_inv p x \<in> A \<longleftrightarrow> x \<in> A\<close>
  using
    ring.ring_simprules(3)[of _ x, OF Ideal.ideal.axioms(2), of A p]
    ring.ring_simprules(3)[of _ \<open>a_inv p x\<close>, OF Ideal.ideal.axioms(2), of A p]
  apply (auto simp: additive_subgroup.a_inv_closed ideal_def)
  apply (drule additive_subgroup.a_inv_closed)
  apply (auto dest: additive_subgroup.a_inv_closed simp: ideal_def ring.ring_simprules)
  done

lemma pac_ideal_a_close[intro]:
  \<open>x \<in> pac_ideal A \<Longrightarrow> y \<in> pac_ideal A \<Longrightarrow> x + y \<in> pac_ideal A\<close>
  using ideal_a_closed[of _ poly_ring_scheme x y]
  unfolding pac_ideal_def
  apply (auto simp: genideal_def)
  done

lemma uminus_pac_ideal_iff [iff]:
  \<open>-y \<in> pac_ideal A \<longleftrightarrow> y \<in> pac_ideal A\<close>
   using
    ring.ring_simprules(3)[of _ y, OF Ideal.ideal.axioms(2), of _ poly_ring_scheme]
    ring.ring_simprules(3)[of _ \<open>-y\<close>, OF Ideal.ideal.axioms(2), of _ poly_ring_scheme]
  unfolding pac_ideal_def
  apply (auto simp: Ideal.ideal.axioms(2) genideal_def ideal_a_inv_closed simp del: ring.ring_simprules(3))
  apply (frule_tac ideal_a_inv_closed[of _ _ y])
    apply simp_all
  apply (frule_tac ideal_a_inv_closed[of _ _ y])
    apply simp_all
  done

lemma pac_ideal_a_close_diff:
  \<open>x \<in> pac_ideal A \<Longrightarrow> y \<in> pac_ideal A \<Longrightarrow> x - y \<in> pac_ideal A\<close>
  using pac_ideal_a_close[of x A \<open>-y\<close>]
  by auto

lemma diff_in_polynom_bool_pac_idealI:
   assumes a1: "p \<in> pac_ideal A"
   assumes a2: "p - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
proof -
  have \<open>p - p' \<in> pac_ideal A\<close>
    using a2 by auto
  from pac_ideal_a_close[OF this, of \<open>-p\<close>] show ?thesis
    using a1 by auto
qed

lemma diff_in_polynom_bool_pac_idealI2:
   assumes a1: "p \<in> A"
   assumes a2: "p - p' \<in> Ideal.genideal poly_ring_scheme polynom_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
proof -
  have \<open>p - p' \<in> pac_ideal A\<close>
    using a2 by auto
  from pac_ideal_a_close[OF this, of \<open>-p\<close>] show ?thesis
    using a1 by auto
qed

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
  by (auto simp: pac_ideal_def genideal_def)

lemma pac_ideal_add:
  \<open>p \<in> A \<Longrightarrow> q \<in> A \<Longrightarrow> p + q \<in> pac_ideal A\<close>
  by (auto intro!: pac_ideal_a_close)

lemma pac_ideal_mono:
  \<open>A \<subseteq> B \<Longrightarrow> pac_ideal A \<subseteq> pac_ideal B\<close>
  by (auto simp: pac_ideal_def genideal_def)

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

lemma pac_ideal_insert_new_irrel:
  assumes \<open>x \<in> vars p\<close>
    \<open>x \<notin> \<V>\<close>
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close>
    \<open>MPoly_Type.coeff p (monomial (Suc 0) x) = 1 \<or> MPoly_Type.coeff p (monomial (Suc 0) x) = -1\<close> and
    xa: \<open>xa \<in> pac_ideal (insert p (set_mset A))\<close> and
    \<open>vars xa \<subseteq> \<V>\<close>
  shows \<open>xa \<in> pac_ideal (set_mset A)\<close>
proof -
  have IH: \<open>Ideal.ideal x poly_ring_scheme \<and>
        p \<in> x \<and> set_mset A \<subseteq> x \<and> polynom_bool \<subseteq> x \<longrightarrow>
        xa \<in> x\<close> for x
    using xa
    by (auto simp: pac_ideal_def genideal_def)


  show ?thesis
    unfolding pac_ideal_def genideal_def
  proof clarify
    fix B
    assume H:
      \<open>Ideal.ideal B poly_ring_scheme\<close>
      \<open>set_mset A \<union> polynom_bool \<subseteq> B\<close>
    let ?B = \<open>genideal poly_ring_scheme (B \<union> {p})\<close>
    have \<open>set_mset A \<union> polynom_bool \<subseteq> ?B\<close>
      using H(2) by (auto simp: genideal_def)
    moreover have \<open>p \<in> ?B\<close>
      by (auto simp: genideal_def)
    moreover have \<open>Ideal.ideal ?B poly_ring_scheme\<close>
      by (rule ring.genideal_ideal)
       auto
    ultimately have \<open>xa \<in> ?B\<close>
      using IH by (auto)
    then show \<open>xa \<in> B\<close>
      apply (auto simp: pac_ideal_def genideal_def)
      sorry
  qed
qed

lemma finsum_cong:
  \<open>finite A \<Longrightarrow> A \<subseteq> carrier p \<Longrightarrow> abelian_monoid p \<Longrightarrow> f \<in> A \<rightarrow> carrier p \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> g x = f x) \<Longrightarrow> finsum p f A = finsum p g A\<close>
  apply (induction rule: finite_induct)
  apply (auto simp: abelian_monoid.finsum_insert abelian_monoid.finsum_empty)
  apply (subst abelian_monoid.finsum_insert)
  apply auto
  done

lemma
  assumes \<open>ring p\<close> and
    I_P: \<open>I \<subseteq> carrier p\<close> and
    fin: \<open>finite I\<close>
  shows \<open>genideal p I = {finsum p (\<lambda>x. mult p (f x) x) I| f. \<forall>x \<in> I. f x \<in> carrier p}\<close>
    (is \<open>?A = ?B\<close> is \<open>_ = {?P f| f. _}\<close> is \<open>_ = {?P' I f| f. _}\<close>)
proof
  have abel[simp]: \<open>abelian_monoid p\<close>
    using abelian_group.axioms(1) assms(1) ring_def by blast
  have fx_carrier[intro!, simp]: \<open>f x \<in> carrier p \<Longrightarrow> x \<in> carrier p \<Longrightarrow> mult p (f x) x \<in> carrier p\<close> for f x
    by (rule ring.ring_simprules[OF assms(1)])

  have H: \<open>\<exists>fb. fb \<in> I \<rightarrow> carrier p \<and> ?P f \<oplus>\<^bsub>p\<^esub> ?P fa = ?P fb\<close> if \<open>f \<in> I \<rightarrow> carrier p\<close>  \<open>fa \<in> I \<rightarrow> carrier p\<close> for f fa
    using fin that I_P
  proof (induction I arbitrary: f fa rule: finite_induct)
    case empty
    then show ?case
      by (auto simp: abelian_monoid.finsum_empty abelian_monoidE(2)
      abelian_monoidE(2)[OF abel] ring.ring_simprules(15)[OF assms(1)])
  next
    case (insert x F) note fin = this(1) and xF = this(2) and IH = this(3) and H = this(4-)
    obtain fb where
       fb: \<open>fb \<in> F \<rightarrow> carrier p \<and> ?P' F f \<oplus>\<^bsub>p\<^esub> ?P' F fa = ?P' F fb\<close>
       using IH[of f fa] H
       by auto
    define fb' where \<open>fb' = (\<lambda>a. if a = x then add p (f a) (fa a) else fb a)\<close>
    have fb'_x: \<open>fb' x = add p (f x) (fa x)\<close>
      unfolding fb'_def by auto
    have \<open>fb' \<in> insert x F \<rightarrow> carrier p\<close> and
      \<open>?P' F f \<oplus>\<^bsub>p\<^esub> ?P' F fa = ?P' F fb'\<close>
      using fb H fin xF by (auto simp: fb'_def ring.ring_simprules[OF assms(1)] intro!: finsum_cong)
    moreover {
    have \<open>f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (fa x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x)) =
         f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> fa x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x)\<close>
      using H
      apply (auto simp: fb'_x ring.ring_simprules[OF assms(1)] ac_simps)
      by (simp add: Pi_iff abelian_groupE(1) abelian_monoid.finsum_closed abelian_monoidE(3) assms(1) ring.is_abelian_group subsetD)
   also have \<open>... = (f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> fa x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x)\<close>
       using H
      apply (auto simp: fb'_x ring.ring_simprules[OF assms(1)] field_simps)
      by (smt Pi_iff abel abelian_monoid.finsum_closed abelian_monoidE(3) assms(1) ring.ring_simprules(10) ring.ring_simprules(5) subsetD)
   also have \<open>... = ((f x \<oplus>\<^bsub>p\<^esub> fa x) \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x)\<close>
       using H
      by (auto simp: fb'_x ring.ring_simprules[OF assms(1)] field_simps)
    finally have \<open>f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub>
    (fa x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x)) =
    fb' x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> ((\<Oplus>\<^bsub>p\<^esub>x\<in>F. f x \<otimes>\<^bsub>p\<^esub> x) \<oplus>\<^bsub>p\<^esub> (\<Oplus>\<^bsub>p\<^esub>x\<in>F. fa x \<otimes>\<^bsub>p\<^esub> x))\<close>
      using H
      apply (auto simp: fb'_x ring.ring_simprules(15)[OF assms(1)] ac_simps)
      by (simp add: Pi_iff abelian_monoid.finsum_closed abelian_monoidE(3) assms(1) ring.ring_simprules(1) ring.ring_simprules(5) subset_iff)
    }
    ultimately show ?case
      using H xF
      apply (auto intro!: exI[of _ fb'] simp: abelian_monoid.finsum_insert)
      apply (subst abelian_monoid.finsum_insert)
      apply (auto intro: fin)
      apply (subst abelian_monoid.finsum_insert)
      apply (auto intro: fin)
      apply (subst abelian_monoid.finsum_insert)
      apply (auto intro: fin)
      done
  qed

  have [simp]: \<open>finsum p ((\<otimes>\<^bsub>p\<^esub>) \<zero>\<^bsub>p\<^esub>)I = zero p\<close>
    using fin I_P apply (induction rule: finite_induct)
    apply (auto simp: abelian_monoid.finsum_insert abelian_monoid.finsum_empty abelian_monoidE(2)
      abelian_monoidE(2)[OF abel] ring.ring_simprules(15)[OF assms(1)])
      apply (subst abelian_monoid.finsum_insert)
      apply (auto intro: fin simp: ring.ring_simprules[OF assms(1)])
     done
have inv[intro,simp]: \<open>x \<in> carrier p \<Longrightarrow> a_inv p x \<in> carrier p\<close> for x
  using
    ring.ring_simprules(3)[of _ x, OF Ideal.ideal.axioms(2), of ?A p]
    ring.ring_simprules(3)[of _ \<open>a_inv p x\<close>, OF Ideal.ideal.axioms(2), of ?A p]
    ring.genideal_ideal[of p I]
  by (auto simp: assms)

have [simp]:
  \<open> \<forall>x\<in>I. f x \<in> carrier p \<Longrightarrow>
        x \<in> I \<Longrightarrow> f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> \<ominus>\<^bsub>p\<^esub> f x \<otimes>\<^bsub>p\<^esub> x = \<zero>\<^bsub>p\<^esub>\<close> 
  \<open> \<forall>x\<in>I. f x \<in> carrier p \<Longrightarrow>
        x \<in> I \<Longrightarrow> \<ominus>\<^bsub>p\<^esub> f x \<otimes>\<^bsub>p\<^esub> x \<oplus>\<^bsub>p\<^esub> f x \<otimes>\<^bsub>p\<^esub> x = \<zero>\<^bsub>p\<^esub>\<close>for f x
   using I_P assms(1) in_mono ring.l_minus ring.ring_simprules(16) apply fastforce
   by (smt I_P fx_carrier assms(1) ring.l_minus ring.ring_simprules(9) subsetD)

have \<open>subgroup ?B (add_monoid p)\<close>
    apply (standard)
    subgoal
      apply (auto simp: assms intro!: H)
      apply (smt I_P Pi_iff abel abelian_monoid.finsum_closed assms(1) ring.ring_simprules(5) subset_iff)
      done
    subgoal for x y
      apply clarify
      subgoal for f fa
        using H[of f fa]
        by auto
      done
    subgoal
      by (auto intro!: exI[of _ \<open>\<lambda>_. zero p\<close>] simp: ring.ring_simprules[OF assms(1)])
    subgoal for x
      apply (auto simp: intro!: )
      apply (rule_tac x= \<open>\<lambda>x. a_inv p (f x)\<close> in exI)
      apply (auto simp: m_inv_def intro!: the_equality)
      apply (smt I_P Pi_I' inv abel abelian_monoid.finsum_closed assms(1) in_mono monoid.m_closed ring_def)
      apply (subst abelian_monoid.finsum_addf[symmetric])
      using I_P apply (auto cong: finsum_cong)
      apply (subst finsum_cong[of _ _ _ \<open>\<lambda>_. zero p\<close>])
      apply (auto simp: assms ring.ring_simprules(2)[OF assms(1)] abelian_monoid.finsum_zero[OF abel])
      apply (subst abelian_monoid.finsum_addf[symmetric])
      using I_P apply auto
      apply (subst finsum_cong[of _ _ _ \<open>\<lambda>_. zero p\<close>])
      using I_P apply (auto simp: assms ring.ring_simprules(2)[OF assms(1)] abelian_monoid.finsum_zero[OF abel])
      defer
      find_theorems \<open>(THE _. _) = _\<close>
      find_theorems \<open>add _ _ _ = zero _\<close>
  using
    ring.ring_simprules(3)[of _ \<open>f _\<close>, OF Ideal.ideal.axioms(2), of I p]
    ring.ring_simprules(3)[of _ \<open>a_inv p (f _)\<close>, OF Ideal.ideal.axioms(2), of i p]
  apply (auto simp: additive_subgroup.a_inv_closed ideal_def)
  apply (drule additive_subgroup.a_inv_closed)
  apply (auto dest: additive_subgroup.a_inv_closed simp: ideal_def ring.ring_simprules)
      apply (rule group.inv_closed)
      apply auto
      
      term ring
    
    apply (rule H)
    find_theorems  a_inv carrier
    thm ideal_a_inv_closed
    sorry
  have \<open>Ideal.ideal ?B p\<close>
    apply (rule idealI)
    apply (auto intro: assms)
find_theorems \<open>_ \<subseteq> _\<close> Ideal.ideal
find_theorems \<open>genideal _ _ \<subseteq> _\<close>
thm ring.ideal_incl_iff
term \<open>a_r_coset S\<close>
lemma \<open>A = a_r_coset poly_ring_scheme\<close>
  unfolding a_r_coset_def r_coset_def
apply auto
sorry
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
    by (force simp: ideal.span_add_eq ideal.span_base pac_idealI3
      pac_ideal_insert_already_in[OF diff_in_polynom_bool_pac_idealI[of \<open>p*q\<close> \<open>_\<close> pq]])
  subgoal for p A
    using pac_ideal_mono[of \<open>set_mset (A - {#p#})\<close> \<open>set_mset A\<close>]
    by (auto dest: in_diffD)
  subgoal for p x
    using pac_ideal_insert_new_irrel
    by (auto simp:)
  done

text \<open>
  In general, if deletions are disallowed, then the stronger \<^term>\<open>B = pac_ideal A\<close> holds.
\<close>
lemma restricted_ideal_to_restricted_ideal_to\<^sub>ID:
  \<open>restricted_ideal_to \<V> (set_mset A) \<subseteq> restricted_ideal_to\<^sub>I \<V> A\<close>
   by (auto simp add: Collect_disj_eq pac_idealI1 restricted_ideal_to_def)


lemma rtranclp_PAC_Format_subset_ideal:
  \<open>rtranclp PAC_Format (\<V>, A) (\<V>', B) \<Longrightarrow> \<Union>(vars ` set_mset A) \<subseteq> \<V> \<Longrightarrow>
     restricted_ideal_to\<^sub>I \<V> B \<subseteq> restricted_ideal_to\<^sub>I \<V> A \<and> \<V> \<subseteq> \<V>' \<and> \<Union>(vars ` set_mset B) \<subseteq> \<V>'\<close>
  apply (induction rule:rtranclp_induct[of PAC_Format \<open>(_, _)\<close> \<open>(_, _)\<close>, split_format(complete)])
  subgoal
    by (simp add: restricted_ideal_to_restricted_ideal_to\<^sub>ID)
  subgoal
    apply (drule PAC_Format_subset_ideal)
    apply simp_all
    apply auto
    by (smt Collect_mono_iff mem_Collect_eq restricted_ideal_to_def subset_trans)
  done

end