theory PAC_More_Poly
  imports "HOL-Library.Poly_Mapping" "HOL-Algebra.Polynomials" "Polynomials.MPoly_Type_Class"
  "HOL-Algebra.Module"
  "HOL-Library.Countable_Set"
begin


lemma Const\<^sub>0_add:
  \<open>Const\<^sub>0 (a + b) = Const\<^sub>0 a + Const\<^sub>0 b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

lemma Const_mult:
  \<open>Const (a * b) = Const a * Const b\<close>
  by transfer
     (simp add: Const\<^sub>0_def times_monomial_monomial)

lemma Const\<^sub>0_mult:
  \<open>Const\<^sub>0 (a * b) = Const\<^sub>0 a * Const\<^sub>0 b\<close>
  by transfer
     (simp add: Const\<^sub>0_def times_monomial_monomial)

lemma Const0[simp]:
  \<open>Const 0 = 0\<close>
  by transfer (simp add: Const\<^sub>0_def)

lemma (in -) Const_uminus[simp]:
  \<open>Const (-n) = - Const n\<close>
  by transfer
    (auto simp: Const\<^sub>0_def monomial_uminus)

lemma [simp]: \<open>Const\<^sub>0 0 = 0\<close>
  \<open>MPoly 0 = 0\<close>
  supply [[show_sorts]]
  by (auto simp: Const\<^sub>0_def zero_mpoly_def)

lemma Const_add:
  \<open>Const (a + b) = Const a + Const b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

instance mpoly :: (comm_semiring_1) comm_semiring_1
  by standard

lemma degree_uminus[simp]:
  \<open>degree (-A) x' = degree A x'\<close>
  by (auto simp: degree_def uminus_mpoly.rep_eq)

lemma degree_sum_notin:
  \<open>x' \<notin> vars B \<Longrightarrow> degree (A + B) x' = degree A x'\<close>
  apply (auto simp: degree_def)
  apply (rule arg_cong[of _ _ Max])
  apply (auto simp: plus_mpoly.rep_eq)
  apply (smt Poly_Mapping.keys_add UN_I UnE image_iff in_keys_iff subsetD vars_def)
  by (smt UN_I add.right_neutral imageI lookup_add not_in_keys_iff_lookup_eq_zero vars_def)

lemma degree_notin_vars:
  \<open>x \<notin> (vars B) \<Longrightarrow> degree (B :: 'a :: {monoid_add} mpoly) x = 0\<close>
  using degree_sum_notin[of x B 0]
  by auto

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


lemma vars_in_right_only:
  "x \<in> vars q \<Longrightarrow> x \<notin> vars p \<Longrightarrow> x \<in> vars (p+q)"
  apply (auto simp: vars_def keys_def plus_mpoly.rep_eq
    lookup_plus_fun)
  by (metis add.left_neutral gr_implies_not0)

lemma [simp]:
  \<open>vars 0 = {}\<close>
  by (simp add: vars_def zero_mpoly.rep_eq)


lemma vars_Un_nointer:
  \<open>keys (mapping_of p) \<inter>  keys (mapping_of q) = {} \<Longrightarrow> vars (p + q) = vars p \<union> vars q\<close>
  apply (auto simp: vars_def)
  apply (metis (no_types, hide_lams) Poly_Mapping.keys_add UnE in_mono plus_mpoly.rep_eq)
  apply (smt IntI UN_I add.right_neutral coeff_add coeff_keys empty_iff empty_iff in_keys_iff)
  apply (smt IntI UN_I add.left_neutral coeff_add coeff_keys empty_iff empty_iff in_keys_iff)
  done

lemmas [simp] = zero_mpoly.rep_eq

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

lemma in_mapping_mult_single:
  \<open>x \<in> (\<lambda>x. lookup x x') ` keys (mapping_of A * (Var\<^sub>0 x' :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b :: {monoid_mult,zero_neq_one,semiring_0})) \<longleftrightarrow>
    x > 0 \<and> x - 1 \<in> (\<lambda>x. lookup x x') ` keys (mapping_of A)\<close>
  apply (auto  elim!: in_keys_timesE simp: lookup_add)
  apply (auto simp: keys_def lookup_times_monomial_right Var\<^sub>0_def)
  apply (metis One_nat_def lookup_single_eq lookup_single_not_eq one_neq_zero)
  apply (metis (mono_tags) add_diff_cancel_right' imageI lookup_single_eq lookup_single_not_eq mem_Collect_eq)
  apply (subst image_iff)
  apply (cases x)
  apply simp
  apply (rule_tac x= \<open>xa + Poly_Mapping.single x' 1\<close> in bexI)
  apply (auto simp: lookup_add)
  done

lemma Max_Suc_Suc_Max:
  \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Max (insert 0 (Suc ` A)) =
    Suc (Max (insert 0 A))\<close>
  by (induction rule: finite_induct)
   (auto simp: hom_Max_commute)

lemma [simp]:
  \<open>keys (Var\<^sub>0 x' :: ('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b :: {zero_neq_one}) = {Poly_Mapping.single x' 1}\<close>
  by (auto simp: Var\<^sub>0_def)


lemma degree_mult_Var:
  \<open>degree (A * Var x') x' = (if A = 0 then 0 else Suc (degree A x'))\<close> for A :: \<open>int mpoly\<close>
  apply (auto simp: degree_def times_mpoly.rep_eq)
  apply (subst arg_cong[of _ \<open>insert 0
          (Suc ` ((\<lambda>x. lookup x x') ` keys (mapping_of A)))\<close> Max])
  apply (auto simp: image_image Var.rep_eq lookup_plus_fun in_mapping_mult_single
    hom_Max_commute
  elim!: in_keys_timesE intro!: Max_Suc_Suc_Max
    split: if_splits)[]
   apply (subst Max_Suc_Suc_Max)
   apply auto
   using mapping_of_inject by fastforce

lemma degree_mult_Var':
  \<open>degree (Var x' * A) x' = (if A = 0 then 0 else Suc (degree A x'))\<close> for A :: \<open>int mpoly\<close>
 by (simp add: degree_mult_Var semiring_normalization_rules(7)) 

lemma degree_add_max:
  \<open>degree (A + B) x \<le> max (degree A x) (degree B x)\<close>
  apply (auto simp: degree_def plus_mpoly.rep_eq
       max_def
    dest!: set_rev_mp[OF _ Poly_Mapping.keys_add])
  by (smt Max_ge dual_order.trans finite_imageI finite_insert finite_keys
    image_subset_iff nat_le_linear subset_insertI)

lemma degree_times_le:
  \<open>degree (A * B) x \<le> degree A x + degree B x\<close>
  by (auto simp: degree_def times_mpoly.rep_eq
       max_def lookup_add add_mono
    dest!: set_rev_mp[OF _ Poly_Mapping.keys_add]
    elim!: in_keys_timesE)


lemma monomial_inj:
  "monomial c s = monomial (d::'b::zero_neq_one) t \<longleftrightarrow> (c = 0 \<and> d = 0) \<or> (c = d \<and> s = t)"
  apply (auto simp: monomial_inj Poly_Mapping.single_def
    poly_mapping.Abs_poly_mapping_inject when_def
    cong: if_cong
    split: if_splits)
    apply metis
    apply metis
    apply metis
    apply metis
    done

lemma MPoly_monomial_power':
  \<open>MPoly (monomial 1 x') ^ (n+1) =  MPoly (monomial (1) (((\<lambda>x. x + x') ^^ n) x'))\<close>
  by (induction n)
   (auto simp: times_mpoly.abs_eq mult_single ac_simps)

lemma MPoly_monomial_power:
  \<open>n > 0 \<Longrightarrow> MPoly (monomial 1 x') ^ (n) =  MPoly (monomial (1) (((\<lambda>x. x + x') ^^ (n - 1)) x'))\<close>
  using MPoly_monomial_power'[of _ \<open>n-1\<close>]
  by auto


lemma vars_uminus[simp]:
  \<open>vars (-p) = vars p\<close>
  by (auto simp: vars_def uminus_mpoly.rep_eq)

lemma coeff_uminus[simp]:
  \<open>MPoly_Type.coeff (-p) x = -MPoly_Type.coeff p x\<close>
  by (auto simp: coeff_def uminus_mpoly.rep_eq)

end