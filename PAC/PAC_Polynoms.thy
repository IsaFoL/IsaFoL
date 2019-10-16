theory PAC_Polynoms
  imports PAC_Specification
    Weidenbach_Book_Base.WB_List_More
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

lemma poly_embed_EX:
  \<open>\<exists>\<phi>. bij (\<phi> :: string list \<Rightarrow> nat)\<close>
  by (rule countableE_infinite[of \<open>UNIV :: string list set\<close>])
     (auto intro!: infinite_UNIV_listI)

text \<open>Using a multiset instead of a list has some advantage from an abstract point of view.\<close>
type_synonym mset_polynom =
  \<open>(string multiset * int) multiset\<close>

lemma Const_add:
  \<open>Const (a + b) = Const a + Const b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

definition normalized_poly :: \<open>mset_polynom \<Rightarrow> bool\<close> where
  \<open>normalized_poly p \<longleftrightarrow>
     distinct_mset p\<close>

lemma normalized_poly_simps[simp]:
  \<open>normalized_poly {#}\<close>
  \<open>normalized_poly (add_mset t p) \<longleftrightarrow>
    t \<notin># p \<and> normalized_poly p\<close>
  by (auto simp: normalized_poly_def)


(*

*)

instance mpoly :: (comm_semiring_1) comm_semiring_1
  by standard

lemma [simp]: \<open>Const\<^sub>0 0 = 0\<close>
  \<open>MPoly 0 = 0\<close>
  supply [[show_sorts]]
  by (auto simp: Const\<^sub>0_def zero_mpoly_def)

context
  fixes R :: \<open>string multiset \<Rightarrow> string multiset \<Rightarrow> bool\<close>
begin

text \<open>
  The following function implements a very trivial multiplication. The result
  is not normalised. Therefore, we have the non-\<^text>\<open>raw\<close> version that also
  partially normalise the resulting polynoms, but not fully (as this would require
  to sort the list).
\<close>


definition mult_poly_by_monom :: \<open>string multiset * int \<Rightarrow> mset_polynom \<Rightarrow> mset_polynom\<close> where
  \<open>mult_poly_by_monom  = (\<lambda>ys q. image_mset (\<lambda>xs. (fst xs + fst ys, snd ys * snd xs)) q)\<close>


definition mult_poly_raw :: \<open>mset_polynom \<Rightarrow> mset_polynom \<Rightarrow> mset_polynom\<close> where
  \<open>mult_poly_raw p q =
    (fold_mset (\<lambda>y. (+) (mult_poly_by_monom y q)) {#} p)\<close>


definition remove_powers :: \<open>mset_polynom \<Rightarrow> mset_polynom\<close> where
  \<open>remove_powers xs =  image_mset (apfst remdups_mset) xs\<close>
end

lemma (in -) Const_uminus[simp]:
  \<open>Const (-n) = - Const n\<close>
  by transfer
    (auto simp: Const\<^sub>0_def monomial_uminus)

locale poly_embed =
  fixes \<phi> :: \<open>string \<Rightarrow> nat\<close>
  assumes \<open>bij \<phi>\<close>
begin

definition poly_of_vars :: "string multiset \<Rightarrow> ('a :: {comm_semiring_1}) mpoly" where
  \<open>poly_of_vars xs = fold_mset (\<lambda>a b. Var (\<phi> a) * b) (0 :: 'a mpoly) xs\<close>

lemma poly_of_vars_simps[simp]:
  shows
    \<open>poly_of_vars (add_mset x xs) = Var (\<phi> x) * (poly_of_vars xs :: ('a :: {comm_semiring_1}) mpoly)\<close> (is ?A) and
    \<open>poly_of_vars (xs + ys) = poly_of_vars xs * (poly_of_vars ys :: ('a :: {comm_semiring_1}) mpoly)\<close> (is ?B)
proof -
  interpret comp_fun_commute \<open>(\<lambda>a b. (b :: 'a :: {comm_semiring_1} mpoly) * Var (\<phi> a))\<close>
    by standard
      (auto simp: algebra_simps ac_simps
         Var_def times_monomial_monomial intro!: ext)
  note [[show_types]]
  show ?A
    by (auto simp: comp_fun_commute.fold_mset_add_mset
      poly_of_vars_def comp_fun_commute_axioms fold_mset_fusion mult.assoc
      ac_simps)
  show ?B
    apply (auto simp: comp_fun_commute.fold_mset_add_mset
      poly_of_vars_def mult.assoc ac_simps)
    by (smt comp_fun_commute_axioms fold_mset_fusion mult.commute mult_zero_right)
qed


definition mononom_of_vars where
  \<open>mononom_of_vars \<equiv> (\<lambda>(xs, n). (+) (Const n * poly_of_vars xs))\<close>

interpretation comp_fun_commute \<open>mononom_of_vars\<close>
  by standard
    (auto simp: algebra_simps ac_simps mononom_of_vars_def
       Var_def times_monomial_monomial intro!: ext)

lemma [simp]:
  \<open>poly_of_vars {#} = 0\<close>
  by (auto simp: poly_of_vars_def)

lemma mononom_of_vars_add[simp]:
  \<open>NO_MATCH 0 b \<Longrightarrow> mononom_of_vars xs b = Const (snd xs) * poly_of_vars (fst xs) + b\<close>
  by (cases xs)
    (auto simp: ac_simps mononom_of_vars_def)

definition polynom_of_mset :: \<open>mset_polynom \<Rightarrow> _\<close> where
  \<open>polynom_of_mset p = sum_mset (mononom_of_vars `# p) 0\<close>

lemma polynom_of_mset_append[simp]:
  \<open>polynom_of_mset (xs + ys) = polynom_of_mset xs + polynom_of_mset ys\<close>
  by (auto simp: ac_simps Const_def polynom_of_mset_def)

lemma polynom_of_mset_Cons[simp]:
  \<open>polynom_of_mset (add_mset x ys) = Const (snd x) * poly_of_vars (fst x) + polynom_of_mset ys\<close>
  by (cases x)
    (auto simp: ac_simps polynom_of_mset_def mononom_of_vars_def)

lemma polynom_of_mset_empty[simp]:
  \<open>polynom_of_mset {#} = 0\<close>
  by (auto simp: polynom_of_mset_def)

interpretation comp_fun_commute \<open>(\<lambda>y. (+) (mult_poly_by_monom y ys))\<close>
  by standard auto

lemma mult_poly_by_monom_simps[simp]:
  \<open>mult_poly_by_monom t {#} = {#}\<close>
  \<open>mult_poly_by_monom t (ps + qs) =  mult_poly_by_monom t ps + mult_poly_by_monom t qs\<close>
  \<open>mult_poly_by_monom a (add_mset p ps) = add_mset (fst a + fst p, snd a * snd p) (mult_poly_by_monom a ps)\<close>
proof -
  interpret comp_fun_commute \<open>(\<lambda>xs. add_mset (xs + t))\<close> for t
    by standard auto
  show
    \<open>mult_poly_by_monom t (ps + qs) =  mult_poly_by_monom t ps + mult_poly_by_monom t qs\<close> for t
    by (induction ps)
      (auto simp: mult_poly_by_monom_def)
  show
    \<open>mult_poly_by_monom a (add_mset p ps) = add_mset (fst a + fst p, snd a * snd p) (mult_poly_by_monom a ps)\<close>
    \<open>mult_poly_by_monom t {#} = {#}\<close>for t
    by (auto simp: mult_poly_by_monom_def)
qed


lemma polynom_of_mset_mult_poly_by_monom[simp]:
  \<open>polynom_of_mset (mult_poly_by_monom x ys) =
       (Const (snd x) * poly_of_vars (fst x) * polynom_of_mset ys)\<close>
 by (induction ys)
   (auto simp: Const_mult algebra_simps)

lemma polynom_of_mset_mult_poly_raw[simp]:
  \<open>polynom_of_mset (mult_poly_raw xs ys) = polynom_of_mset xs * polynom_of_mset ys\<close>
  unfolding mult_poly_raw_def
  by (induction xs arbitrary: ys)
   (auto simp: Const_mult algebra_simps)

lemma ideal_mult_right_in:
  \<open>a \<in> ideal A \<Longrightarrow> a * b \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))

lemma ideal_mult_right_in2:
  \<open>a \<in> ideal A \<Longrightarrow> b * a \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))


lemma X2_X_polynom_bool_mult_in:
  \<open>Var (x1) * (Var (x1) * p) -  Var (x1) * p \<in> More_Modules.ideal polynom_bool\<close>
  using ideal_mult_right_in[OF  X2_X_in_pac_ideal[of x1 \<open>{}\<close>], of p]
  by (auto simp: right_diff_distrib ac_simps power2_eq_square)


lemma polynom_of_list_remove_powers_polynom_bool:
  \<open>(polynom_of_mset xs) - polynom_of_mset (remove_powers xs) \<in> ideal polynom_bool\<close>
proof (induction xs)
  case empty
  then show \<open>?case\<close> by (auto simp: remove_powers_def ideal.span_zero)
next
  case (add x xs)
  have H1: \<open>x1 \<in># x2 \<Longrightarrow>
       Var (\<phi> x1) * poly_of_vars x2 - p \<in> More_Modules.ideal polynom_bool \<longleftrightarrow>
       poly_of_vars x2 - p \<in> More_Modules.ideal polynom_bool
       \<close> for x1 x2 p
    apply (subst (2) ideal.span_add_eq[symmetric,
      of \<open>Var (\<phi> x1) * poly_of_vars x2 - poly_of_vars x2\<close>])
    apply (drule multi_member_split)
    apply (auto simp: X2_X_polynom_bool_mult_in)
    done

  have diff: \<open>poly_of_vars (x) - poly_of_vars (remdups_mset (x)) \<in> ideal polynom_bool\<close> for x
    apply (induction x)
    apply (auto simp: remove_powers_def ideal.span_zero H1)
    apply (metis ideal.span_scale right_diff_distrib)
    done
  show ?case
    using add
    apply (cases x)
    subgoal for ys y
      using ideal_mult_right_in2[OF diff, of \<open>poly_of_vars ys\<close> ys]
      apply (auto simp: remove_powers_def right_diff_distrib
        ideal.span_diff ideal.span_add ac_simps)
     by (smt add.right_neutral fold_mset_empty mult_zero_right poly_of_vars_def poly_of_vars_simps(2))
    done
qed

end

end

