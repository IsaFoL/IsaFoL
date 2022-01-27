(*
  File:         PAC_Checker_Specification.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory LPAC_Checker_Specification
  imports LPAC_Specification
    Refine_Imperative_HOL.IICF
    PAC_Checker.Finite_Map_Multiset
    PAC_Checker.PAC_Checker_Specification
begin

section \<open>Checker Algorithm\<close>

subsection \<open>Version for the paper\<close>

lemma vars_mult_Var:
  \<open>vars (Var x * p) = (if p = 0 then {} else insert x (vars p))\<close>
  for p :: \<open>'a :: {comm_monoid_add,cancel_comm_monoid_add,semiring_0,comm_semiring_1,ring_1_no_zero_divisors} mpoly\<close>
proof -
  have \<open>p \<noteq> 0 \<Longrightarrow>
    \<exists>xa. (\<exists>k. xa = monomial (Suc 0) x + k) \<and>
         lookup (mapping_of p) (xa - monomial (Suc 0) x) \<noteq> 0 \<and>
         0 < lookup xa x\<close>
   by (metis (no_types, opaque_lifting) One_nat_def ab_semigroup_add_class.add.commute
     add_diff_cancel_right' aux lookup_add lookup_single_eq mapping_of_inject
     neq0_conv one_neq_zero plus_eq_zero_2 zero_mpoly.rep_eq)
  then show ?thesis
    apply (auto simp: vars_def times_mpoly.rep_eq Var.rep_eq
    elim!: in_keys_timesE dest: keys_add')
    apply (auto simp: keys_def lookup_times_monomial_left Var.rep_eq Var\<^sub>0_def adds_def
      lookup_add eq_diff_eq'[symmetric])
    done
qed

lemma keys_mult_monomial:
  \<open>keys (monomial (n :: 'a :: {comm_monoid_add,cancel_comm_monoid_add,semiring_0,comm_semiring_1,ring_1_no_zero_divisors}) k * mapping_of a) = (if n = 0 then {} else ((+) k) ` keys (mapping_of a))\<close>
proof -
  have [simp]: \<open>(\<Sum>aa. (if k = aa then n else 0) *
               (\<Sum>q. lookup (mapping_of a) q when k + xa = aa + q)) =
        (\<Sum>aa. (if k = aa then n * (\<Sum>q. lookup (mapping_of a) q when k + xa = aa + q) else 0))\<close>
      for xa
    by (smt Sum_any.cong mult_not_zero)
  show ?thesis
    apply (auto simp: vars_def times_mpoly.rep_eq Const.rep_eq times_poly_mapping.rep_eq
      Const\<^sub>0_def elim!: in_keys_timesE split: if_splits)
    apply (auto simp: lookup_monomial_If prod_fun_def
      keys_def times_poly_mapping.rep_eq)
    done
qed

lemma vars_add_monom2:
assumes "p2 = monom (monomial (1) x') (1::'a::{comm_monoid_add,cancel_comm_monoid_add,semiring_0,comm_semiring_1,ring_1_no_zero_divisors})  * A"  "x' \<notin> vars p1"
shows "vars (p1 + p2) = vars p1 \<union> vars p2"
proof -
  have "keys (mapping_of p2) = (+) (monomial (Suc 0) x') ` keys (mapping_of A)"
    unfolding assms by (simp add: times_mpoly.rep_eq keys_mult_monomial times_mpoly.rep_eq
      keys_mult_monomial)
  then have "keys (mapping_of (p1+p2)) = keys (mapping_of p1) \<union> keys (mapping_of p2)"
    using assms(2) apply -
    apply (subst keys_add)
    apply (auto split: if_splits simp: plus_mpoly.rep_eq vars_def)
    by (metis One_nat_def in_keys_iff lookup_add lookup_single_eq one_neq_zero plus_eq_zero)
  then show ?thesis unfolding vars_def by simp
qed

lemma polynomial_split_on_var_restricted:
  fixes p :: \<open>'a :: {comm_monoid_add,cancel_comm_monoid_add,semiring_0,comm_semiring_1,ring_1_no_zero_divisors} mpoly\<close>
  obtains q r where
    \<open>p = monom (monomial (Suc 0) x') 1 * q + r\<close> and
    \<open>x' \<notin> vars r\<close> and
    \<open>vars q \<subseteq> vars p\<close>
    \<open>vars r \<subseteq> vars p\<close>
proof -
  have [simp]: \<open>{x \<in> keys (mapping_of p). x' \<in> keys x} \<union>
        {x \<in> keys (mapping_of p). x' \<notin> keys x} = keys (mapping_of p)\<close>
    by auto
  have
    \<open>p = (\<Sum>x\<in>keys (mapping_of p). MPoly_Type.monom x (MPoly_Type.coeff p x))\<close> (is \<open>_ = (\<Sum>x \<in> ?I. ?f x)\<close>)
    using polynomial_sum_monoms(1)[of p] .
  also have \<open>... = (\<Sum>x\<in> {x \<in> ?I. x' \<in> keys x}. ?f x) + (\<Sum>x\<in> {x \<in> ?I. x' \<notin> keys x}. ?f x)\<close> (is \<open>_ = ?pX + ?qX\<close>)
    by (subst comm_monoid_add_class.sum.union_disjoint[symmetric]) auto
  finally have 1: \<open>p = ?pX + ?qX\<close> .
  have H: \<open>0 < lookup x x' \<Longrightarrow> (\<lambda>k. (if x' = k then Suc 0 else 0) +
          (if k = x' \<and> 0 < lookup x k then lookup x k - 1
           else lookup x k)) = lookup x\<close> for x x'
    by auto
  have [simp]: \<open>finite {x. 0 < (Suc 0 when x' = x)}\<close> for x' :: nat and x
    by (smt bounded_nat_set_is_finite lessI mem_Collect_eq neq0_conv when_cong when_neq_zero)
  have H: \<open>x' \<in> keys x \<Longrightarrow> monomial (Suc 0) x' + Abs_poly_mapping (\<lambda>k. if k = x' \<and> 0 < lookup x k then lookup x k - 1 else lookup x k) = x\<close>
    for x and x' :: nat
    apply (simp only: keys_def single.abs_eq)
    apply (subst plus_poly_mapping.abs_eq)
    by (auto simp: eq_onp_def when_def H
        intro!: finite_subset[of \<open>{xa. (xa = x' \<and> 0 < lookup x xa \<longrightarrow> Suc 0 < lookup x x') \<and>
           (xa \<noteq> x' \<longrightarrow> 0 < lookup x xa)}\<close> \<open>{xa. 0 < lookup x xa}\<close>])

  have [simp]: \<open>x' \<in> keys x \<Longrightarrow>
        MPoly_Type.monom (monomial (Suc 0) x' + decrease_key x' x) n =
        MPoly_Type.monom x n\<close> for x n and x'
    apply (subst mpoly.mapping_of_inject[symmetric], subst poly_mapping.lookup_inject[symmetric])
    unfolding mapping_of_monom lookup_single
    apply (auto intro!: ext simp: decrease_key_def when_def H)
    done
  have Var_x': \<open>Var x' = MPoly_Type.monom (monomial (Suc 0) x') 1\<close>
    by (simp add: Var.abs_eq Var\<^sub>0_def monom.abs_eq)
  have pX: \<open>?pX = monom (monomial (Suc 0) x') 1 * (\<Sum>x\<in> {x \<in> ?I. x' \<in> keys x}. MPoly_Type.monom (decrease_key x' x) (MPoly_Type.coeff p x))\<close>
    (is \<open>_ = _ * ?pX'\<close>)
    by (subst sum_distrib_left, subst mult_monom)
     (auto intro!: sum.cong)
  have \<open>x' \<notin> vars ?qX\<close>
    using vars_setsum[of \<open>{x. x \<in> keys (mapping_of p) \<and> x' \<notin> keys x}\<close> \<open>?f\<close>]
    by (auto dest!: vars_monom_subset[unfolded subset_eq Ball_def, rule_format])
  moreover have \<open>vars ?qX \<subseteq> vars p\<close>
    apply (subst (3)1)
    unfolding pX
    apply auto
    subgoal for x
      apply (subst add.commute)
      apply (subst vars_add_monom2[of _ x' \<open>(\<Sum>x | x \<in> keys (mapping_of p) \<and> x' \<in> keys x.
    MPoly_Type.monom (decrease_key x' x) (MPoly_Type.coeff p x))\<close>])
      apply auto
      using calculation by blast
    done
  moreover have \<open>vars ?pX' \<subseteq> vars p\<close>
    apply (subst (3)1)
    unfolding pX
    apply auto
    subgoal for x
      apply (subst add.commute)
      apply (subst vars_add_monom2[of _ x' \<open>(\<Sum>x | x \<in> keys (mapping_of p) \<and> x' \<in> keys x.
    MPoly_Type.monom (decrease_key x' x) (MPoly_Type.coeff p x))\<close>])
      apply auto[]
      using calculation apply blast
        unfolding Var_x'[symmetric]
        apply (auto simp: vars_mult_Var elim!: )
      done
    done
  ultimately show ?thesis
    using that[of ?pX' ?qX]
    unfolding pX[symmetric] 1[symmetric]
    by auto
qed


lemma ideal_span_explicit_vars:
  fixes q :: \<open>int mpoly\<close>
  assumes \<open>finite b\<close> and
   q:  \<open>q \<in> More_Modules.ideal b\<close>
  shows
    \<open>q \<in> {\<Sum>a\<in>t. r a * a |t r. finite t \<and> t \<subseteq> b \<and> (\<forall>a \<in> t. vars (r a) \<subseteq> \<Union>(vars ` b) \<union> vars q) }\<close>
  (is "_ \<in> ?B")
proof -
  obtain r t where
    q: \<open>q = (\<Sum>a\<in>t. r a * a)\<close> and
    fin_t: \<open>finite t\<close> and
    t: \<open>t \<subseteq> b\<close>
    using q unfolding ideal.span_explicit
    by auto
  let ?\<Sigma>' = \<open>\<Union>(vars ` r ` t) - (\<Union>(vars ` b) \<union> vars q)\<close>
  let ?\<Sigma> = \<open>\<Union>(vars ` r ` t)\<close>
  have H: \<open>q \<in> {\<Sum>a\<in>t. r a * a |t r. finite t \<and> t \<subseteq> b \<and> (\<forall>a \<in> t. vars (r a) \<subseteq> ?\<Sigma> - \<Sigma>)}\<close>
    if \<open>\<Sigma> \<subseteq> ?\<Sigma>'\<close>
    for \<Sigma>
  proof -
    have \<open>finite \<Sigma>\<close>
      by (rule finite_subset[OF that])
       (auto intro!: finite_UN_I fin_t finite_UN_I vars_finite)
    then show ?thesis
      using that
    proof (induction rule: finite_induct)
      case empty
      then show ?case
        using q fin_t t by blast
    next
      case (insert x F)
      then have
        \<open>F \<subseteq> \<Union> (vars ` r ` t) - (\<Union> (vars ` b)\<union> vars q)\<close>
        \<open>x \<in> \<Union> (vars ` r ` t)\<close> and
        x_notin: \<open>x \<notin> \<Union> (vars ` b)\<close> \<open>x \<notin> vars q\<close> and
        q: \<open>q \<in> {\<Sum>a\<in>ta. ra a * a |ta ra. finite ta \<and> ta \<subseteq> b \<and> (\<forall>a\<in>ta. vars (ra a) \<subseteq> ?\<Sigma> - F)}\<close>
        by auto

      obtain r' t' where
        q: \<open>q = (\<Sum>a\<in>t'. r' a * a)\<close> and
        fin_t: \<open>finite t'\<close> and
        t: \<open>t' \<subseteq> b\<close> and
        vars: \<open>a \<in> t' \<Longrightarrow> vars (r' a) \<subseteq> ?\<Sigma> - F\<close> for a
        using q by auto

      have \<open>\<exists>g' h'. r' a = g' + h' * Var x \<and> x \<notin> vars g' \<and> vars g' \<subseteq> vars (r' a) \<and>
         vars h' \<subseteq> vars (r' a)\<close> if \<open>a \<in> t'\<close> for a
        by (metis One_nat_def Var.abs_eq Var\<^sub>0_def ab_semigroup_add_class.add.commute
          ab_semigroup_mult_class.mult.commute monom.abs_eq polynomial_split_on_var_restricted)
      then obtain g' h' where
        r': \<open>r' a = g' a + h' a * Var x\<close> and
        NOX: \<open>x \<notin> vars (g' a)\<close> and
        var_g': \<open>vars (g' a) \<subseteq> vars (r' a)\<close> and
        var_h': \<open>vars (h' a) \<subseteq> vars (r' a)\<close> if \<open>a \<in> t'\<close> for a
        by metis
      have \<open>q = (\<Sum>a\<in>t'. g' a * a + h' a * a * Var x)\<close>
        unfolding q by (auto intro!: sum.cong simp: r' field_simps)
      also have \<open>... = (\<Sum>a\<in>t'. g' a * a) + (\<Sum>a\<in>t'. h' a * a) * Var x\<close>
        by (auto simp: r' comm_monoid_add_class.sum.distrib sum_distrib_right)
      finally have \<open>q = (\<Sum>a\<in>t'. g' a * a) + (\<Sum>a\<in>t'. h' a * a) * Var x\<close> (is \<open>_ = ?NOX + ?X * Var x\<close>)
        .

      moreover {
        have \<open>x \<notin> (\<Union>a\<in>t'. vars (g' a * a))\<close>
          using NOX t x_notin
          by (auto elim!: vars_unE)
        then have \<open>x \<notin> vars ?NOX\<close>
          using vars_setsum[OF fin_t] by auto
     }
     ultimately have \<open>q = ?NOX\<close>
       by (metis (no_types, lifting) add_cancel_left_right degree_mult_Var degree_notin_vars
         mult_eq_0_iff nat.simps(3) vars_in_right_only x_notin(2))
     moreover {
       have \<open>a \<in> t' \<Longrightarrow> vars (g' a) \<subseteq> ?\<Sigma> - F\<close> for a
         using vars[of a] r'[of a] var_g'[of a]
         by auto
       then have \<open>(\<forall>a\<in>t'. vars (g' a) \<subseteq> \<Union> (vars ` r ` t) - insert x F)\<close>
         using NOX by auto
     }
     ultimately show ?case
       using fin_t t polynomial_decomp_alien_var[of q \<open>?NOX\<close> x ?X]
       by auto
    qed
  qed
  have \<open>\<Union> (vars ` r ` t) -
               (\<Union> (vars ` r ` t) - (\<Union> (vars ` b) \<union> vars q)) \<subseteq> (\<Union> (vars ` b) \<union> vars q)\<close>
    by auto
  with H[of \<open>\<Union> (vars ` r ` t) - (\<Union> (vars ` b) \<union> vars q)\<close>] show "q \<in> ?B"
    by (smt (verit, best) mem_Collect_eq subset_iff)
qed

lemma vars_polynomial_constraints[simp]: \<open>vars ((Var ca)\<^sup>2 - Var ca) = {ca}\<close> for ca
  apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq split: if_splits)
   apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq when_def ac_simps adds_def lookup_plus_fun
      power2_eq_square times_mpoly.rep_eq minus_mpoly.rep_eq split: if_splits)
  apply (rule_tac x = \<open>(2 :: nat \<Rightarrow>\<^sub>0 nat) * monomial (Suc 0) ca\<close> in exI)
  apply (auto dest: monomial_0D simp: plus_eq_zero_2 lookup_plus_fun mult_2)
  by (meson Suc_neq_Zero monomial_0D plus_eq_zero_2)

text \<open>This is an important lemma, because it shows the equivalence between the Isabelle version of
the theorems and the paper version that restricts the polynomial constraints to only the relevant
variables.\<close>
lemma cut_ideal_to_relevant_vars:
  assumes
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynomial_bool) \<longleftrightarrow>
    q \<in> More_Modules.ideal (set_mset A \<union> (\<lambda>c. Var c ^ 2 - Var c) ` \<V>)\<close>
    (is \<open>q \<in> ?A \<longleftrightarrow> q \<in> ?B\<close> is \<open>_ \<in> More_Modules.ideal ?f \<longleftrightarrow> _ \<in> More_Modules.ideal ?r\<close>)
proof
  assume \<open>q \<in> ?B\<close>
  moreover have \<open>?B \<subseteq> ?A\<close>
    by (rule ideal.span_mono) (auto simp: polynomial_bool_def)
  ultimately show \<open>q \<in> ?A\<close>
    by blast
next
  assume q: \<open>q \<in> ?A\<close>
  then obtain r t where
    q: \<open>q = (\<Sum>a\<in>t. r a * a)\<close> and
    fin_t: \<open>finite t\<close> and
    t: \<open>t \<subseteq> set_mset A \<union> polynomial_bool\<close>
    unfolding ideal.span_explicit
    by auto
  have t2: \<open>t \<subseteq> ?r \<union> (t \<inter> polynomial_bool - ?r)\<close>
    using t by auto
  let ?\<Sigma> = \<open>t \<inter> (?f - ?r)\<close>
  have fin_\<Sigma>: \<open>finite ?\<Sigma>\<close>
    using fin_t by auto
  have \<open>\<exists>t' r. q = (\<Sum>a\<in>t'. r a * a) \<and> finite t' \<and> t' \<subseteq> ?r \<union> (?\<Sigma> - E)\<close> if \<open>E \<subseteq> ?\<Sigma>\<close> for E
  proof -
    have \<open>finite E\<close>
      using that fin_\<Sigma> finite_subset by blast
    then show ?thesis
      using t2 that
    proof (induction rule: finite_induct)
      case empty
      then show ?case using q fin_t t by fast
    next
      case (insert x E)
      have \<open>\<exists>t' r. q = (\<Sum>a\<in>t'. r a * a) \<and> finite t' \<and> t' \<subseteq> ?r \<union> (?\<Sigma> - E)\<close> and
        x: \<open>x \<in> ?\<Sigma>\<close>
        apply (rule insert.IH | rule insert.prems | use insert.prems in auto; fail)+
        done
      then obtain t' r where
       q: \<open>q = (\<Sum>a\<in>t'. r a * a)\<close> and
        fin_t': \<open>finite t'\<close> and
        t'': \<open>t' \<subseteq> ?r \<union> (?\<Sigma> - E)\<close>
        by auto
      obtain c where x: \<open>x = (Var c)\<^sup>2 - Var c\<close> and \<open>c \<notin> \<V>\<close> and \<open>x \<in> t\<close>
        using insert.prems(2) by (auto simp: polynomial_bool_def)
      show ?case
      proof (cases \<open>x \<in> t'\<close>)
        case False
        then show ?thesis using q fin_t' t'' by auto
      next
        case True
        define t'' where \<open>t'' = t' - {x}\<close>
        then have t''[simp]: \<open>t' = insert x t''\<close> \<open>x \<notin> t''\<close> \<open>finite t''\<close>
          using True fin_t' by auto
        have \<open>t'' \<subseteq> ?r \<union> (?\<Sigma> - E) - {x}\<close>
          using \<open>t' \<subseteq> ?r \<union> (?\<Sigma> - E)\<close> apply (auto simp: x)
          using t''(2) x apply blast
          using t''(2) x apply force+
          done
        then have \<open>t'' \<subseteq> ?r \<union> (?\<Sigma> - insert x E)\<close>
          by auto
        have \<open>\<exists>g h. r a = Var c * g + h \<and> c \<notin> vars h\<close> for a
          by (rule polynomial_split_on_var[of \<open>r a\<close> c])
           (auto simp add: Var.abs_eq Var\<^sub>0_def monom.abs_eq)
        then obtain g h where
          r: \<open>r a = Var c * g a + h a\<close> and
          c: \<open>c \<notin> vars (h a)\<close> for a
          by metis
        have [simp]: \<open>vars x = {c}\<close>
          by (auto simp: x)
        have r': \<open>r a * a = Var c * (g a * a) + h a *a\<close> for a
          unfolding r by (auto simp: field_simps)
        have \<open>q = ((\<Sum>a\<in>t''. g a * a) + r x * (Var c - 1)) * Var c + (\<Sum>a\<in>t''. h a * a)\<close>
          unfolding q t''
          apply (simp add: sum.insert_if)
          apply (subst (2)r')
          apply (auto simp: comm_monoid_add_class.sum.insert_if ring_distribs
            sum.distrib simp flip: ideal.scale_sum_left sum_distrib_right sum_distrib_left)
          apply (subst (2)x)
          by (auto simp: field_simps power2_eq_square)
        moreover {
        have \<open>c \<notin> (\<Union>m\<in>t''. vars (h m * m))\<close>
          using fin_t vars_mult[of \<open>h _\<close>] c
          apply (auto simp: t elim!: vars_unE)
          using \<open>t'' \<subseteq> ?r \<union> (?\<Sigma> - insert x E)\<close> apply -
          apply (frule set_rev_mp)
          apply assumption
          apply auto
          apply (meson UN_I \<open>c \<notin> \<V>\<close> assms(1) subset_iff)
          using \<open>c \<notin> \<V>\<close> apply fastforce
          by (metis (no_types, lifting) vars_polynomial_constraints
            \<open>\<And>thesis. (\<And>c. \<lbrakk>x = (Var c)\<^sup>2 - Var c; c \<notin> \<V>; x \<in> t\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>vars x = {c}\<close>
            imageE mk_disjoint_insert polynomial_bool_def singleton_insert_inj_eq')
        then have \<open>c \<notin> vars (\<Sum>a\<in>t''. h a * a)\<close>
          using c vars_setsum[of t'' \<open>\<lambda>a. h a * a\<close>]
          by auto
      }
      moreover have \<open>c \<notin> vars q\<close>
        using \<open>c \<notin> \<V>\<close> vars_q by blast
      ultimately have \<open>q = (\<Sum>a\<in>t''. h a * a)\<close>
        by (metis (no_types, lifting) One_nat_def Var.abs_eq Var\<^sub>0_def monom.abs_eq
            polynomial_decomp_alien_var(2))
      
      then show ?thesis
        using \<open>t'' \<subseteq> ?r \<union> (?\<Sigma> - insert x E)\<close>
        by (auto intro!: exI[of _ t''])
    qed
  qed
qed
  from this[of ?\<Sigma>] show \<open>q \<in> ?B\<close>
    unfolding ideal.span_explicit
    by auto
qed


text \<open>This version is close to the paper proof of proposition 1. However, it is still too far away
to be included as is in the actual paper.\<close>
lemma extensions_are_safe:
  assumes \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    A: \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    p_x_coeff: \<open>coeff p (monomial (Suc 0) x') = 1\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close> and
    q: \<open>q \<in> More_Modules.ideal (insert p (set_mset A \<union> polynomial_bool))\<close> and
    leading: \<open>x' \<notin> vars (p - Var x')\<close> and
    diff: \<open>(Var x' - p)\<^sup>2 - (Var x' - p) \<in> More_Modules.ideal polynomial_bool\<close> and
    varsp: \<open>vars p \<subseteq> insert x' \<V>\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynomial_bool)\<close>
proof -
  define p' where \<open>p' \<equiv> p - Var x'\<close>
  let ?v = \<open>Var x' :: int mpoly\<close>
  have p_p': \<open>p = ?v + p'\<close>
    by (auto simp: p'_def)
  define q' where \<open>q' \<equiv> Var x' - p\<close>
  have q_q': \<open>p = ?v - q'\<close>
    by (auto simp: q'_def)
  have diff: \<open>q'^2 - q' \<in> More_Modules.ideal polynomial_bool\<close>
    using diff unfolding q_q' by auto
  have \<open>vars q' \<subseteq> \<V>\<close>
    using leading apply -
    unfolding diff_conv_add_uminus q'_def
    apply standard
    by (metis (no_types, lifting) diff_add_cancel diff_conv_add_uminus in_mono insertCI insertE
        leading minus_diff_eq vars_subst_in_left_only_iff vars_uminus varsp)

  then have \<open>vars (q'\<^sup>2 - q') \<subseteq> \<V>\<close>
    unfolding diff_conv_add_uminus apply -
    apply standard
    apply (elim in_vars_addE)
    by (auto elim!: in_vars_addE vars_unE simp: power2_eq_square)

  have q: \<open>q \<in> More_Modules.ideal (set_mset (add_mset p A) \<union> (\<lambda>c. Var c ^ 2 - Var c) ` insert x' \<V>)\<close>
    by (rule cut_ideal_to_relevant_vars[THEN iffD1])
     (use vars_q q varsp A in auto)
  moreover have eq: \<open>More_Modules.ideal (set_mset (add_mset p A) \<union> (\<lambda>c. Var c ^ 2 - Var c) ` insert x' \<V>) =
     More_Modules.ideal (set_mset (add_mset p A) \<union> (\<lambda>c. Var c ^ 2 - Var c) ` \<V>)\<close>
    (is \<open>_ = More_Modules.ideal ?trimmed\<close>)
  proof -
    have 1: \<open>(Var x' - p)\<^sup>2 - (Var x' - p) \<in> More_Modules.ideal (set_mset {#} \<union> (\<lambda>c. Var c ^ 2 - Var c) ` \<V>)\<close>
      unfolding q'_def[symmetric]
      by (rule cut_ideal_to_relevant_vars[of \<open>{#}\<close> \<V> \<open>q'^2 - q'\<close>, THEN iffD1])
        (use \<open>vars (q'\<^sup>2 - q') \<subseteq> \<V>\<close> A diff  in auto)
    have eq: \<open>(Var x')\<^sup>2 - (Var x') = (q'\<^sup>2 - q') + p * (2 * Var x' - p - 1)\<close>
      unfolding q'_def
      by (auto simp: power2_eq_square field_simps)
    have \<open>(Var x')\<^sup>2 - (Var x') \<in> More_Modules.ideal ((set_mset (add_mset p A) \<union> (\<lambda>c. Var c ^ 2 - Var c) ` \<V>))\<close>
      unfolding eq
      apply (subst ideal.span_add_eq)
       apply (use 1 q'_def ideal.span_mono[of \<open>((\<lambda>c. (Var c)\<^sup>2 - Var c) ` \<V>)\<close> \<open>((set_mset (add_mset p A) \<union> (\<lambda>c. Var c ^ 2 - Var c) ` \<V>))\<close>] 
          in auto; fail)[]
       apply (rule ideal_mult_right_in; rule ideal.span_base)
      by auto 
    then show ?thesis
      by (auto intro!: ideal.span_insert_idI)
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
      t: \<open>t' \<subseteq> set_mset A \<union> polynomial_bool\<close>
      using q fin_t t True t''
      apply (subst (asm) t')
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def)
      using q fin_t t True t''
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def polynomial_bool_def)
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
   moreover have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
     by (auto simp: coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
       times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
   ultimately have \<open>\<forall>a. \<exists>g h. r a = (?v + p') * g + h \<and> x' \<notin> vars h\<close>
     using polynomial_split_on_var2[of x' \<open>-p'\<close> \<open>r _\<close>]
     by (metis diff_minus_eq_add)
   then obtain g h where
     r: \<open>r a = p * g a + h a\<close> and
     x'_h: \<open>x' \<notin> vars (h a)\<close> for a
     unfolding p_p'[symmetric]
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

    have \<open>x \<in> t' \<Longrightarrow> x' \<in> vars x \<Longrightarrow> False\<close> for x
      using  \<open>t \<subseteq> ?trimmed\<close> t assms(2,3)
      apply (auto simp: polynomial_bool_def dest!: multi_member_split)
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
      using polynomial_decomp_alien_var2[OF q_decomp[unfolded p_p' mon[symmetric]]]
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
        simp: field_simps polynomial_bool_def)
  qed
qed


text \<open>

In this level of refinement, we define the first level of the
implementation of the checker, both with the specification as
on ideals and the first version of the loop.

\<close>

subsection \<open>Algorithm\<close>

datatype ('a, 'b, 'lbls) pac_step =
  CL (pac_srcs: \<open>('a \<times> 'lbls) list\<close>) (new_id: 'lbls) (pac_res: 'a) |
  Extension (new_id: 'lbls) (new_var: 'b) (pac_res: 'a) |
  Del (pac_src1: 'lbls)

definition check_linear_comb :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat set \<Rightarrow> (int mpoly \<times> nat) list \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>check_linear_comb \<A> \<V> xs n r = SPEC(\<lambda>b. b \<longrightarrow> (\<forall>i \<in> set xs. snd i \<in># dom_m \<A> \<and> vars (fst i) \<subseteq> \<V>) \<and> n \<notin># dom_m \<A> \<and>
  vars r \<subseteq> \<V> \<and> xs \<noteq> [] \<and> (\<Sum>(p,n) \<in>#mset xs. the (fmlookup \<A> n) * p) - r \<in> ideal polynomial_bool)\<close>

lemma PAC_Format_LC:
  assumes
    i: \<open>((\<V>, A), \<V>\<^sub>B, B) \<in> polys_rel_full\<close> and
    st: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, B)\<close> and
    vars: \<open>\<forall>i\<in>#x11. snd i \<in># dom_m A \<and> vars (fst i) \<subseteq> \<V>\<close> and
    AV: \<open>\<Union> (vars ` set_mset (ran_m A)) \<subseteq> \<V>\<close> and
    fin: \<open>x11 \<noteq> {#}\<close> and
    r: \<open>(\<Sum>x\<in>#x11. case x of (p, n) \<Rightarrow> the (fmlookup A n) * p) - r \<in> More_Modules.ideal polynomial_bool\<close>
    \<open>vars r \<subseteq> \<V>\<close>
  shows \<open>PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset r B)\<close>
proof -
  have AB: \<open>i \<in># dom_m A \<Longrightarrow> the (fmlookup A i) \<in># B\<close> and BA: \<open>B = ran_m A\<close> for i
    using i by (auto simp: polys_rel_full_def polys_rel_def)
  have \<open>PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset ((\<Sum>x\<in>#x11. case x of (p, n) \<Rightarrow> the (fmlookup A n) * p)) B)\<close>
    using fin vars
  proof (induction x11)
    case empty
    then show ?case by auto
  next
    case (add x F)
    then have IH: \<open>F \<noteq> {#} \<Longrightarrow> PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset (\<Sum>(p,n)\<in>#F. the (fmlookup A n) * p) B)\<close> and
      x_A: \<open>snd x \<in># dom_m A\<close> and
      x_var: \<open>vars (fst x) \<subseteq> \<V>\<close> and
      x_in: \<open>the (fmlookup A (snd x)) \<in># B\<close>
      using AB[of \<open>snd x\<close>] by auto
    have vars_A: \<open>vars (the (fmlookup A (snd x))) \<subseteq> \<V>\<close>
      using AV x_A
      by (auto simp: ran_m_def)
    let ?B = \<open>(add_mset (\<Sum>(p,n)\<in>#F. the (fmlookup A n) * p) B)\<close>
    let ?p = \<open>(\<Sum>(p,n)\<in>#F. the (fmlookup A n) * p)\<close>
    let ?q = \<open>(\<Sum>(p,n)\<in>#{#x#}. the (fmlookup A n) * p)\<close>
    let ?vars = \<open>\<lambda>A. \<Union> (vars ` set_mset (A)) \<subseteq> \<V>\<close>
    consider
      (empty) \<open>F = {#}\<close> |
      (nempty) \<open>F \<noteq> {#}\<close>
      by blast
    then show ?case
    proof cases
      case empty2: empty
      have \<open>PAC_Format (\<V>, B) (\<V>, add_mset ((\<Sum>x\<in>#{#x#}. case x of (p, n) \<Rightarrow> the (fmlookup A n) * p)) B)\<close>
        apply (cases x)
        apply (rule PAC_Format.intros(2)[OF x_in, of \<open>fst x\<close>])
        by (use x_var vars_A in \<open>auto simp: ideal.span_zero elim!: vars_unE\<close>)
      then show ?thesis
        using empty2 by auto
    next
      case nempty
      then have IH: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>, B) (\<V>, add_mset ?p B)\<close>
        using IH by auto
      from rtranclp_PAC_Format_subset_ideal[OF this] have vars2: \<open>?vars ?B\<close>
        using AV unfolding BA[symmetric] by auto
      have 1:
        \<open>PAC_Format (\<V>, ?B) (\<V>, add_mset (the (fmlookup A (snd x)) * fst x) ?B)\<close> (is \<open>PAC_Format _ (_, ?C)\<close>)
        apply (cases x)
        apply (rule PAC_Format.intros(2)[of \<open>the (fmlookup A (snd x))\<close> _ \<open>fst x\<close>])
        by (use x_in x_var vars_A in \<open>auto simp: ideal.span_zero elim!: vars_unE\<close>)
      from PAC_Format_subset_ideal[OF this] have \<open>?vars (add_mset (the (fmlookup A (snd x)) * fst x) ?B)\<close>
        using vars2 by auto
      have 2: \<open>PAC_Format (\<V>, ?C) (\<V>, add_mset (\<Sum>(p,n)\<in>#add_mset x F. the (fmlookup A n) * p) ?C)\<close>  (is \<open>PAC_Format _ (_, ?D)\<close>)
        apply (cases x)
        apply (rule PAC_Format.intros(1)[of \<open>?p\<close> _ ?q])
        by (use insert x_in x_var vars_A vars2 in \<open>auto simp: ideal.span_zero elim!: in_vars_addE vars_unE\<close>)
      then have 3:  \<open>PAC_Format\<^sup>*\<^sup>* (\<V>, ?D) (\<V>, add_mset (\<Sum>(p,n)\<in># add_mset x F. the (fmlookup A n) * p) B)\<close>
        using  PAC_Format.del[of ?p ?D \<V>]
          PAC_Format.del[of \<open>the (fmlookup A (snd x)) * fst x\<close> \<open>remove1_mset ?p ?D\<close> \<V>]
        by (auto 4 7)
      show ?thesis
        using IH 1 2 3 by auto
    qed
  qed
  moreover have \<open>PAC_Format (\<V>, add_mset (\<Sum>(p,n)\<in>#x11. the (fmlookup A n) * p) B)
    (\<V>, add_mset r (add_mset (\<Sum>(p,n)\<in>#x11. the (fmlookup A n) * p) B))\<close> (is \<open>PAC_Format _ ?E\<close>)
    by (rule PAC_Format.intros(2)[of \<open>(\<Sum>(p,n)\<in>#x11. the (fmlookup A n) * p)\<close> _ 1])
      (use r in auto)
  moreover  have \<open>PAC_Format ?E (\<V>, add_mset r B)\<close>
    using  PAC_Format.del[of \<open>(\<Sum>(p,n)\<in>#x11. the (fmlookup A n) * p)\<close> \<open>snd ?E\<close> \<open>fst ?E\<close>]
   by auto
  ultimately show ?thesis
    using st by auto
qed

definition PAC_checker_step_inv where
  \<open>PAC_checker_step_inv spec stat \<V> A \<longleftrightarrow>
  (\<forall>i\<in>#dom_m A. vars (the (fmlookup A i)) \<subseteq> \<V>) \<and>
  vars spec \<subseteq> \<V>\<close>

definition check_extension_precalc
  :: \<open>(nat, int mpoly) fmap \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int mpoly \<Rightarrow> (bool) nres\<close>
 where
  \<open>check_extension_precalc A \<V> i v p' =
     SPEC(\<lambda>b. b \<longrightarrow> (i \<notin># dom_m A \<and>
     (v \<notin> \<V> \<and>
           (p')\<^sup>2 - (p') \<in> ideal polynomial_bool \<and>
            vars (p') \<subseteq> \<V>)))\<close>

definition PAC_checker_step
  ::  \<open>int_poly \<Rightarrow> (status \<times> fpac_step) \<Rightarrow> (int_poly, nat, nat) pac_step \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker_step = (\<lambda>spec (stat, (\<V>, A)) st. case st of
     CL _ _ _ \<Rightarrow>
  do {
         ASSERT(PAC_checker_step_inv spec stat \<V> A);
         r \<leftarrow> normalize_poly_spec (pac_res st);
        eq \<leftarrow> check_linear_comb A \<V> (pac_srcs st) (new_id st) r;
        st' \<leftarrow> SPEC(\<lambda>st'. (\<not>is_failed st' \<and> is_found st' \<longrightarrow> r - spec \<in> ideal polynomial_bool));
        if eq
        then RETURN (merge_status stat st', \<V>, fmupd (new_id st) r A)
        else RETURN (FAILED, (\<V>, A))
   }
   | Del _ \<Rightarrow>
       do {
        ASSERT(PAC_checker_step_inv spec stat \<V> A);
        eq \<leftarrow> check_del A (pac_src1 st);
        if eq
        then RETURN (stat, (\<V>, fmdrop (pac_src1 st) A))
        else RETURN (FAILED, (\<V>, A))
   }
   | Extension _ _ _ \<Rightarrow>
       do {
         ASSERT(PAC_checker_step_inv spec stat \<V> A);
        r \<leftarrow> normalize_poly_spec (pac_res st);
        (eq) \<leftarrow> check_extension_precalc A \<V> (new_id st) (new_var st) r;
        if eq
        then do {
          r0 \<leftarrow> SPEC(\<lambda>r0. r0  =  (r - Var (new_var st)) \<and>
              vars r0 = vars (r) \<union> {new_var st});
         RETURN (stat,
          insert (new_var st) \<V>, fmupd (new_id st) (r0) A)}
        else RETURN (FAILED, (\<V>, A))
   }
          )\<close>


lemma PAC_checker_step_PAC_checker_specification2:
  fixes a :: \<open>status\<close>
  assumes AB: \<open>((\<V>, A),(\<V>\<^sub>B, B)) \<in> polys_rel_full\<close> and
    \<open>\<not>is_failed a\<close> and
    [simp,intro]: \<open>a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    A\<^sub>0B: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (\<V>, B)\<close> and
    spec\<^sub>0: \<open>vars spec \<subseteq> \<V>\<^sub>0\<close>  and
    vars_A\<^sub>0: \<open>\<Union> (vars ` set_mset A\<^sub>0) \<subseteq> \<V>\<^sub>0\<close>
  shows \<open>PAC_checker_step spec (a, (\<V>, A)) st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification_step2 (\<V>\<^sub>0, A\<^sub>0) spec (\<V>, B))\<close>
proof -
  have
    \<open>\<V>\<^sub>B = \<V>\<close>and
    [simp, intro]:\<open>(A, B) \<in> polys_rel\<close>
    using AB
    by (auto simp: polys_rel_full_def)
  have H0: \<open>2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r \<in> pac_ideal
                (insert (the (fmlookup A x12))
                  ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close> for x12 r Aa
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute 
         diff_in_polynomial_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)+
  then have H0': \<open>\<And>Aa. 2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          spec \<in> pac_ideal (insert (the (fmlookup A x12)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
    for r x12
    by (metis (no_types, lifting) diff_in_polynomial_bool_pac_idealI)

  have H1: \<open> x12 \<in># dom_m A \<Longrightarrow>
       2 * the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       vars spec \<subseteq> vars r \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close> for x12 r
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x12)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynomial_bool\<close> \<open>2 * the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     by (auto dest!: multi_member_split simp: ran_m_def 
         intro: H0')
   have H2': \<open>the (fmlookup A x11) + the (fmlookup A x12) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       B = add_mset (the (fmlookup A x11)) {#the (fmlookup A x). x \<in># Aa#} \<Longrightarrow>
       (the (fmlookup A x11) + the (fmlookup A x12) - r
        \<in> More_Modules.ideal
            (insert (the (fmlookup A x11))
              ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa \<union> polynomial_bool)) \<Longrightarrow>
        - r
        \<in> More_Modules.ideal
            (insert (the (fmlookup A x11))
              ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa \<union> polynomial_bool))) \<Longrightarrow>
       r \<in> pac_ideal (insert (the (fmlookup A x11)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
     for r x12 x11 A Aa
     by (metis (mono_tags, lifting) Un_insert_left diff_diff_eq2 diff_in_polynomial_bool_pac_idealI diff_zero
       ideal.span_diff ideal.span_neg minus_diff_eq pac_idealI1 pac_ideal_def set_image_mset
       set_mset_add_mset_insert union_single_eq_member)
   have H2: \<open>x11 \<in># dom_m A \<Longrightarrow>
       x12 \<in># dom_m A \<Longrightarrow>
       the (fmlookup A x11) + the (fmlookup A x12) - r
       \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       r - spec \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       spec \<in> pac_ideal (set_mset B)\<close>  for x12 r x11
     using \<open>(A,B) \<in> polys_rel\<close>
      ideal.span_add[OF ideal.span_add[OF ideal.span_neg ideal.span_neg,
         of \<open>the (fmlookup A x11)\<close> _  \<open>the (fmlookup A x12)\<close>],
      of \<open>set_mset B \<union> polynomial_bool\<close> \<open>the (fmlookup A x11) + the (fmlookup A x12) - r\<close>]
     unfolding polys_rel_def
     by (subgoal_tac \<open>r \<in> pac_ideal (set_mset B)\<close>)
       (auto dest!: multi_member_split simp: ran_m_def ideal.span_base 
         intro: diff_in_polynomial_bool_pac_idealI simp: H2')

   have H3': \<open>the (fmlookup A x12) * q - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          spec - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
          r \<in> pac_ideal (insert (the (fmlookup A x12)) ((\<lambda>x. the (fmlookup A x)) ` set_mset Aa))\<close>
     for Aa x12 r q
     by (metis (no_types, lifting) ab_semigroup_mult_class.mult.commute diff_in_polynomial_bool_pac_idealI
       ideal.span_base pac_idealI3 set_image_mset set_mset_add_mset_insert union_single_eq_member)

  have [intro]: \<open>spec \<in> pac_ideal (set_mset B) \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> and
    vars_B: \<open>\<Union> (vars ` set_mset B) \<subseteq> \<V>\<close>and
    vars_B: \<open>\<Union> (vars ` set_mset (ran_m A)) \<subseteq> \<V>\<close>
    using rtranclp_PAC_Format_subset_ideal[OF A\<^sub>0B  vars_A\<^sub>0] spec\<^sub>0 \<open>(A, B) \<in> polys_rel\<close>[unfolded polys_rel_def, simplified]
    by (smt in_mono mem_Collect_eq restricted_ideal_to_def)+
  have spec_found: \<open>PAC_Format\<^sup>*\<^sup>* (\<V>\<^sub>0, A\<^sub>0) (V, add_mset r B) \<Longrightarrow>
    r - spec \<in> ideal polynomial_bool \<Longrightarrow> spec \<in> pac_ideal (set_mset A\<^sub>0)\<close> for V B r
    using rtranclp_PAC_Format_subset_ideal[of \<V>\<^sub>0 A\<^sub>0 V \<open>add_mset r B\<close>]  vars_A\<^sub>0 spec\<^sub>0
    by (smt diff_in_polynomial_bool_pac_idealI2 in_mono mem_Collect_eq restricted_ideal_to_def
      rtranclp_PAC_Format_subset_ideal union_single_eq_member)

  have eq_successI: \<open>st' \<noteq> FAILED \<Longrightarrow>
       st' \<noteq> FOUND \<Longrightarrow> st' = SUCCESS\<close> for st'
    by (cases st') auto
  have vars_diff_inv: \<open>vars (Var x2 - r) = vars (r - Var x2 :: int mpoly)\<close> for x2 r
    using vars_uminus[of \<open>Var x2 - r\<close>]
    by (auto simp del: vars_uminus)
  have vars_add_inv: \<open>vars (Var x2 + r) = vars (r + Var x2 :: int mpoly)\<close> for x2 r
    unfolding add.commute[of \<open>Var x2\<close> r] ..
  have pre: \<open>PAC_checker_step_inv spec a \<V> A\<close>
    unfolding PAC_checker_step_inv_def
    using assms
    by (smt UN_I in_dom_in_ran_m  rtranclp_PAC_Format_subset_ideal subset_iff vars_B)
 have G[intro]: \<open> b\<^sup>2 - b \<in> ideal polynomial_bool\<close>
    if \<open>a - b \<in> ideal polynomial_bool\<close> \<open>a\<^sup>2 - a \<in> ideal polynomial_bool\<close>
    for a b
  proof -
    have \<open>(a-b) * (a+b-1) \<in> ideal polynomial_bool\<close>
      using ideal_mult_right_in that(1) by blast
    then have \<open>-(a-b) * (a+b-1) \<in> ideal polynomial_bool\<close>
      using ideal.span_neg ideal_mult_right_in that(1) by blast
    then have \<open>-(a-b) * (a+b-1) + (a\<^sup>2 - a) \<in>  ideal polynomial_bool\<close>
      using ideal.span_add that(2) by blast
    then show \<open>?thesis\<close>
      by (auto simp: algebra_simps power2_eq_square)
  qed
  have [iff]: \<open>a \<noteq> FAILED\<close> and
    [intro]: \<open>a \<noteq> SUCCESS \<Longrightarrow> a = FOUND\<close> and
    [simp]: \<open>merge_status a FOUND = FOUND\<close>
    using assms(2) by (cases a; auto)+
  note [[goals_limit=1]]
  show ?thesis
    unfolding PAC_checker_step_def PAC_checker_specification_step_spec_def
      normalize_poly_spec_alt_def 
      check_extension_precalc_def polys_rel_full_def check_linear_comb_def
    apply (cases st)
    apply clarsimp_all
    subgoal for x11 x12 x13
      apply (refine_vcg lhs_step_If)
      subgoal by (rule pre)
      subgoal for r eqa st'
        using assms vars_B PAC_Format_LC[OF assms(1), of \<V>\<^sub>0 A\<^sub>0 \<open>mset x11\<close> r]
          spec_found[of \<V> r B] rtranclp_trans[of PAC_Format \<open>(\<V>\<^sub>0, A\<^sub>0)\<close> \<open>(\<V>, B)\<close> \<open>(\<V>, add_mset r B)\<close>]
        apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(merge_status a st',\<V>,add_mset r B)\<close> in exI)
        apply (auto simp: polys_rel_update_remove ran_m_mapsto_upd_notin
          intro: PAC_Format_add_and_remove dest: rtranclp_PAC_Format_subset_ideal)
        done
      subgoal
        by (rule RETURN_SPEC_refine)
         (auto simp: Ex_status_iff dest: rtranclp_PAC_Format_subset_ideal)
      done
    subgoal for x31 x32 x34
      apply (refine_vcg lhs_step_If)
      subgoal by (rule pre)
      subgoal for r0 x r
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (rule_tac x = \<open>(a,insert x32 \<V>, add_mset r B)\<close> in exI)
        apply clarsimp_all
          apply (intro conjI)
        by (auto simp: intro!: polys_rel_update_remove PAC_Format_add_and_remove(5-)
          dest: rtranclp_PAC_Format_subset_ideal)
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    subgoal for x11
      unfolding check_del_def
      apply (refine_vcg lhs_step_If)
      subgoal by (rule pre)
      subgoal for eq
        using assms vars_B apply -
        apply (rule RETURN_SPEC_refine)
        apply (cases \<open>x11 \<in># dom_m A\<close>)
        subgoal
          apply (rule_tac x = \<open>(a,\<V>, remove1_mset (the (fmlookup A x11)) B)\<close> in exI)
          apply (auto simp: polys_rel_update_remove PAC_Format_add_and_remove
               is_failed_def is_success_def is_found_def
            dest!: eq_successI
            split: if_splits
            dest: rtranclp_PAC_Format_subset_ideal
            intro: PAC_Format_add_and_remove)
          done
        subgoal
          apply (rule_tac x = \<open>(a,\<V>, B)\<close> in exI)
          apply (auto simp: fmdrop_irrelevant
               is_failed_def is_success_def is_found_def
            dest!: eq_successI
            split: if_splits
            dest: rtranclp_PAC_Format_subset_ideal
            intro: PAC_Format_add_and_remove)
          done
        done
      subgoal
        by (rule RETURN_SPEC_refine)
          (auto simp: Ex_status_iff)
      done
    done
qed

definition PAC_checker
  :: \<open>int_poly \<Rightarrow> fpac_step \<Rightarrow> status \<Rightarrow> (int_poly, nat, nat) pac_step list \<Rightarrow>
    (status \<times> fpac_step) nres\<close>
where
  \<open>PAC_checker spec A b st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b :: status, A :: fpac_step), st). \<not>is_failed b \<and> st \<noteq> [])
       (\<lambda>((bA), st). do {
          ASSERT(st \<noteq> []);
          S \<leftarrow> PAC_checker_step spec (bA) (hd st);
          RETURN (S, tl st)
        })
      ((b, A), st);
    RETURN S
  }\<close>

lemma PAC_checker_PAC_checker_specification2:
  \<open>(A, B) \<in>  polys_rel_full \<Longrightarrow>
    \<not>is_failed a \<Longrightarrow>
    (a = FOUND \<Longrightarrow> spec \<in> pac_ideal (set_mset (snd B))) \<Longrightarrow>
    \<Union>(vars ` set_mset (ran_m (snd A))) \<subseteq> fst B \<Longrightarrow>
    vars spec \<subseteq> fst B \<Longrightarrow>
  PAC_checker spec A a st \<le> \<Down> (status_rel \<times>\<^sub>r polys_rel_full) (PAC_checker_specification2 spec B)\<close>
  unfolding PAC_checker_def conc_fun_RES
  apply (subst RES_SPEC_eq)
  apply (refine_vcg WHILET_rule[where
      I = \<open>\<lambda>((bB), st). bB \<in> (status_rel \<times>\<^sub>r polys_rel_full)\<inverse> ``
                      Collect (PAC_checker_specification_spec spec B)\<close>
    and R = \<open>measure (\<lambda>(_, st).  Suc (length st))\<close>])
  subgoal by auto
  subgoal apply (auto simp: PAC_checker_specification_spec_def)
    apply (cases B; cases A)
    apply (auto simp:polys_rel_def polys_rel_full_def Image_iff)
    done
  subgoal by auto
  subgoal
    apply auto
    apply (rule
     PAC_checker_step_PAC_checker_specification2[of _ _ _ _ _ _ _ \<open>fst B\<close>, THEN order_trans])
     apply assumption
     apply assumption
     apply (auto intro: PAC_checker_specification_spec_trans simp: conc_fun_RES)
     apply (auto simp: PAC_checker_specification_spec_def polys_rel_full_def polys_rel_def
       dest: PAC_Format_subset_ideal
       dest: is_failed_is_success_completeD; fail)+
    by (auto simp: Image_iff intro: PAC_checker_specification_spec_trans
        simp: polys_rel_def polys_rel_full_def)
  subgoal
    by auto
  done

subsection \<open>Full Checker\<close>

definition full_checker
  :: \<open>int_poly \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (int_poly, nat,nat) pac_step list \<Rightarrow> (status \<times> _) nres\<close>
 where
  \<open>full_checker spec0 A pac = do {
     spec \<leftarrow> normalize_poly_spec spec0;
     (st, \<V>, A) \<leftarrow> remap_polys_change_all spec {} A;
     if is_failed st then
     RETURN (st, \<V>, A)
     else do {
       \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars spec0 \<subseteq> \<V>');
       PAC_checker spec (\<V>, A) st pac
    }
}\<close>

lemma full_checker_spec:
  assumes \<open>(A, A') \<in> polys_rel\<close>
  shows
      \<open>full_checker spec A pac \<le> \<Down>{((st, G), (st', G')). (st, st') \<in> status_rel \<and>
           (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> polys_rel_full)}
        (PAC_checker_specification spec (A'))\<close>
proof -
  have H: \<open>set_mset b \<subseteq> pac_ideal (set_mset (ran_m A)) \<Longrightarrow>
       x \<in> pac_ideal (set_mset b) \<Longrightarrow> x \<in> pac_ideal (set_mset A')\<close> for b x
    using assms apply -
    by (drule pac_ideal_mono) (auto simp: polys_rel_def pac_ideal_idemp)
  have 1: \<open>x \<in> {(st, \<V>', A').
          ( \<not> is_failed st \<longrightarrow> pac_ideal (set_mset (ran_m x2)) =
              pac_ideal (set_mset (ran_m A')) \<and>
              \<Union> (vars ` set_mset (ran_m ABC)) \<subseteq> \<V>' \<and>
              \<Union> (vars ` set_mset (ran_m A')) \<subseteq> \<V>') \<and>
            (st = FOUND \<longrightarrow> speca \<in># ran_m A')} \<Longrightarrow>
         x = (st, x') \<Longrightarrow> x' = (\<V>, Aa) \<Longrightarrow>((\<V>', Aa), \<V>', ran_m Aa) \<in> polys_rel_full\<close> for Aa speca x2 st x \<V>' \<V> x' ABC
    by (auto simp: polys_rel_def polys_rel_full_def)
  have H1: \<open>\<And>a aa b xa x x1a x1 x2 speca.
       vars spec \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m A)) \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m x2a)) \<subseteq> x1b \<Longrightarrow>
       restricted_ideal_to\<^sub>I x1b b \<subseteq> restricted_ideal_to\<^sub>I x1b (ran_m x2a) \<Longrightarrow>
       xa \<in> restricted_ideal_to\<^sub>I (\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec) b \<Longrightarrow>
       xa \<in> restricted_ideal_to\<^sub>I (\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec) (ran_m x2a)\<close>
    for x1b b xa x2a
    by (drule restricted_ideal_to_mono[of _ _ _ _ \<open>\<Union> (vars ` set_mset (ran_m A)) \<union> vars spec\<close>])
      auto
  have H2: \<open>\<And>a aa b speca x2 x1a x1b x2a.
       spec - speca \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
       vars spec \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m A)) \<subseteq> x1b \<Longrightarrow>
       \<Union> (vars ` set_mset (ran_m x2a)) \<subseteq> x1b \<Longrightarrow>
       speca \<in> pac_ideal (set_mset (ran_m x2a)) \<Longrightarrow>
       restricted_ideal_to\<^sub>I x1b b \<subseteq> restricted_ideal_to\<^sub>I x1b (ran_m x2a) \<Longrightarrow>
       spec \<in> pac_ideal (set_mset (ran_m x2a))\<close>
    by (metis (no_types, lifting) group_eq_aux ideal.span_add ideal.span_base in_mono
        pac_ideal_alt_def sup.cobounded2)

  show ?thesis
    supply[[goals_limit=1]]
    unfolding full_checker_def normalize_poly_spec_def
      PAC_checker_specification_def remap_polys_change_all_def
    apply (refine_vcg PAC_checker_PAC_checker_specification2[THEN order_trans, of _ _]
      lhs_step_If)
    subgoal by (auto simp: is_failed_def RETURN_RES_refine_iff)
    apply (rule 1; assumption)
    subgoal
      using fmap_ext assms by (auto simp: polys_rel_def ran_m_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal for speca x1 x2 x x1a x2a x1b
      apply (rule ref_two_step[OF conc_fun_R_mono])
       apply auto[]
      using assms
      by (auto simp add: PAC_checker_specification_spec_def conc_fun_RES polys_rel_def H1 H2
          polys_rel_full_def
          dest!: rtranclp_PAC_Format_subset_ideal dest: is_failed_is_success_completeD)
    done
qed


lemma full_checker_spec':
  shows
    \<open>(uncurry2 full_checker, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A)) \<in>
       (Id \<times>\<^sub>r polys_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>{((st, G), (st', G')). (st, st') \<in> status_rel \<and>
           (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> polys_rel_full)}\<rangle>nres_rel\<close>
  using full_checker_spec
  by (auto intro!: frefI nres_relI)

end

