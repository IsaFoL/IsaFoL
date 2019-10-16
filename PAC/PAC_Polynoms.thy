theory PAC_Polynoms
  imports PAC_Specification
    Weidenbach_Book_Base.WB_List_More
begin


lemma poly_embed_EX:
  \<open>\<exists>\<phi>. bij (\<phi> :: string list \<Rightarrow> nat)\<close>
  by (rule countableE_infinite[of \<open>UNIV :: string list set\<close>])
     (auto intro!: infinite_UNIV_listI)

type_synonym list_polynom =
  \<open>(string multiset * nat) list\<close>

abbreviation  (in -)vars :: \<open>list_polynom \<Rightarrow> string multiset list\<close> where
  \<open>vars p \<equiv> map fst p\<close>

abbreviation vars2 :: \<open>list_polynom \<Rightarrow> string multiset set\<close> where
  \<open>vars2 p \<equiv> fst ` set p\<close>


lemma Const_add:
  \<open>Const (a + b) = Const a + Const b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

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

definition normalized_poly :: \<open>list_polynom \<Rightarrow> bool\<close> where
  \<open>normalized_poly p \<longleftrightarrow>
     distinct (map fst p) \<and>
     0 \<notin> snd ` set p\<close>

lemma normalized_poly_simps[simp]:
  \<open>normalized_poly []\<close>
  \<open>normalized_poly [(t, n)] \<longleftrightarrow> n \<noteq> 0\<close>
  \<open>normalized_poly ((t, n) # p) \<longleftrightarrow>
    n \<noteq> 0 \<and> t \<notin> fst ` set p \<and> normalized_poly p\<close>
  by (auto simp: normalized_poly_def)


fun merge_coeffs :: \<open>list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>merge_coeffs [] = []\<close> |
  \<open>merge_coeffs [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then merge_coeffs ((xs, n + m) # p)
    else (xs, n) # merge_coeffs ((ys, m) # p))\<close>


lemma fst_normalize_polynom_subset:
  \<open>vars2 (merge_coeffs p) \<subseteq> vars2 p\<close>
  by (induction p rule: merge_coeffs.induct)  auto


lemma fst_normalize_polynom_Cons_subset[simp]:
  \<open>vars2 (merge_coeffs p) = vars2 p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by auto
  done

lemma distinct_merge_coeffs:
  assumes \<open>sorted_wrt R (map fst xs)\<close> and \<open>transp R\<close> \<open>antisymp R\<close>
  shows \<open>distinct (map fst (merge_coeffs xs))\<close>
  using assms
  by (induction xs rule: merge_coeffs.induct)
    (auto dest: antisympD)



fun remove_empty_coeffs :: \<open>list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>remove_empty_coeffs [] = []\<close> |
  \<open>remove_empty_coeffs ((xs, n) # p) =
    (if n \<noteq> 0 then [(xs, n)] else []) @ remove_empty_coeffs p\<close>
lemma remove_empty_coeffs_notin_0:
  \<open>0 \<notin> snd ` set (remove_empty_coeffs xs)\<close>
  by (induction xs) auto


lemma in_set_remove_empty_coeffsD:
  \<open>x \<in> set (remove_empty_coeffs xs) \<Longrightarrow> x \<in> set xs\<close>
  by (induction xs) auto

lemma distinct_remove_empty_coeffs:
  \<open>distinct (vars  xs) \<Longrightarrow> distinct (vars (remove_empty_coeffs xs))\<close>
  by (induction xs) (auto dest!: in_set_remove_empty_coeffsD)

definition normalize_poly where
  \<open>normalize_poly p = remove_empty_coeffs (merge_coeffs p)\<close>


context
  fixes R :: \<open>string multiset \<Rightarrow> string multiset \<Rightarrow> bool\<close>
begin

fun add_poly :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>add_poly [] p = p\<close> |
  \<open>add_poly p [] = p\<close> |
  \<open>add_poly ((xs, n) # p) ((ys, m) # q) =
    (if xs = ys then (xs, n + m) # add_poly p q
    else if R xs ys then (xs, n) # add_poly p ((ys, m) # q)
    else (ys, m) # add_poly ((xs, n) # p) q)\<close>

lemma add_poly_simps[simp]:
  \<open>add_poly p [] = p\<close>
  by (cases p) auto

lemma notin_vars_notin_add_polyD:
  \<open>x \<notin> vars2 xs \<Longrightarrow>  x \<notin> vars2 ys \<Longrightarrow> x \<notin> vars2 (add_poly xs ys)\<close>
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x xs y ys
    by (auto simp: Const_add algebra_simps)
  done

lemma notin_vars_notin_add_polyD2:
  \<open>x \<notin> vars2 xs \<Longrightarrow>  x \<notin> vars2 ys \<Longrightarrow> (x, a) \<notin> set (add_poly xs ys)\<close>
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by (auto simp: image_iff)
  subgoal
    by (auto simp: image_iff)
  subgoal for x xs y ys
    by (auto simp: Const_add algebra_simps)
  done


lemma normalized_poly_add_poly:
  assumes \<open>sorted_wrt R (map fst xs)\<close> and \<open>transp R\<close> \<open>antisymp R\<close>
     \<open>sorted_wrt R (map fst ys)\<close>
     \<open>normalized_poly xs\<close> \<open>normalized_poly ys\<close>
  shows \<open>normalized_poly (add_poly xs ys)\<close>
  using assms
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x n xs y m ys
    apply (auto simp: Const_add algebra_simps notin_vars_notin_add_polyD2
      dest: antisympD)
    apply (smt antisympD fst_conv image_iff insert_iff list.set(2) notin_vars_notin_add_polyD)
    apply (smt antisympD fst_conv image_iff insert_iff list.set(2) notin_vars_notin_add_polyD)
    done
  done

end


lemma normalized_poly_normalize_poly:
  assumes \<open>sorted_wrt R (map fst xs)\<close> and \<open>transp R\<close> \<open>antisymp R\<close>
  shows \<open>normalized_poly (normalize_poly xs)\<close>
  using distinct_merge_coeffs[OF assms]
  remove_empty_coeffs_notin_0[]
  by (auto simp: normalize_poly_def normalized_poly_def
    distinct_remove_empty_coeffs)

text \<open>
  The following function implements a very trivial multiplication. The result
  is not normalised. Therefore, we have the non-\<^text>\<open>raw\<close> version that also
  partially normalise the resulting polynoms, but not fully (as this would require
  to sort the list).
\<close>
fun mult_poly_raw :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>mult_poly_raw [] p = []\<close> |
  \<open>mult_poly_raw p [] = []\<close> |
  \<open>mult_poly_raw ((xs, m) # p) q =
     map (\<lambda>(ys, n). (xs + ys, n * m)) q @
     mult_poly_raw p q\<close>

definition mult_poly :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>mult_poly xs ys = normalize_poly (mult_poly_raw xs ys)\<close>

definition remove_powers :: \<open>list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>remove_powers xs = map (\<lambda>(a, b). (remdups_mset a, b)) xs\<close>

locale poly_embed =
  fixes \<phi> :: \<open>string \<Rightarrow> nat\<close>
  assumes \<open>bij \<phi>\<close>
begin

definition poly_of_vars :: "char list multiset \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 int" where
  \<open>poly_of_vars xs = fold_mset (\<lambda>a b. Var\<^sub>0 (\<phi> a) * b) 0 xs\<close>

lemma poly_of_vars_simps[simp]:
  \<open>poly_of_vars (add_mset x xs) = Var\<^sub>0 (\<phi> x) * (poly_of_vars xs)\<close>
  \<open>poly_of_vars (xs + ys) = poly_of_vars xs * (poly_of_vars ys)\<close>
proof -
  interpret comp_fun_commute \<open>(\<lambda>a b. b * Var\<^sub>0 (\<phi> a))\<close>
    by standard
      (auto simp: algebra_simps
         Var\<^sub>0_def times_monomial_monomial intro!: ext)

  show
    \<open>poly_of_vars (add_mset x xs) = Var\<^sub>0 (\<phi> x) * (poly_of_vars xs)\<close>
    by (auto simp: comp_fun_commute.fold_mset_add_mset
      poly_of_vars_def comp_fun_commute_axioms fold_mset_fusion mult.assoc
      ac_simps)
  show
    \<open>poly_of_vars (xs + ys) = poly_of_vars xs * (poly_of_vars ys)\<close>
    apply (auto simp: comp_fun_commute.fold_mset_add_mset
      poly_of_vars_def mult.assoc ac_simps)
    by (smt comp_fun_commute_axioms fold_mset_fusion mult.commute mult_zero_right)
qed

fun polynom_of_list :: \<open>list_polynom \<Rightarrow> _\<close> where
  \<open>polynom_of_list [] = Const\<^sub>0 0\<close> |
  \<open>polynom_of_list ((xs, n) # p) =
     Const\<^sub>0 n * poly_of_vars xs + polynom_of_list p\<close>

lemma polynom_of_list_append[simp]:
  \<open>polynom_of_list (xs @ ys) = polynom_of_list xs + polynom_of_list ys\<close>
  by (induction xs arbitrary: ys)
    (auto simp: ac_simps Const\<^sub>0_def)

lemma polynom_of_list_Cons[simp]:
  \<open>polynom_of_list (x # ys) = Const\<^sub>0 (snd x) * poly_of_vars (fst x) + polynom_of_list ys\<close>
  by (cases x)
    (auto simp: ac_simps)

lemma polynom_of_list_cong:
  \<open>mset xs = mset ys \<Longrightarrow> polynom_of_list xs = polynom_of_list ys\<close>
proof (induction xs arbitrary: ys)
  case Nil
  then show \<open>?case\<close> by auto
next
  case (Cons x xs) note IH = this(1) and eq = this(2)
  have \<open>x \<in> set ys\<close>
    using eq mset_eq_setD by fastforce
  then obtain ys1 ys2 where
    ys: \<open>ys = ys1 @ x # ys2\<close>
    by (auto dest: split_list)
  show ?case
    using IH[of \<open>ys1 @ ys2\<close>] eq
    by (auto simp: ys algebra_simps)
qed

lemma polynom_of_list_merge_coeffs[simp]:
  \<open>polynom_of_list (merge_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs rule: merge_coeffs.induct)
    (auto simp: Const\<^sub>0_add algebra_simps)

lemma polynom_of_list_remove_empty_coeffs[simp]:
  \<open>polynom_of_list (remove_empty_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs)
    (auto simp: Const\<^sub>0_add Const\<^sub>0_def algebra_simps)

lemmas [simp] = Const\<^sub>0_zero

lemma polynom_of_list_add_poly[simp]:
  \<open>polynom_of_list (add_poly R xs ys) = polynom_of_list xs + polynom_of_list ys\<close>
  apply (induction xs ys rule: add_poly.induct[of _ R])
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x m xs y n ys
    by (auto simp: Const\<^sub>0_add algebra_simps)
  done


lemma polynom_of_list_map_mult:
  \<open>polynom_of_list (map (\<lambda>(ys, n). (ys + x, f n)) va) =
     poly_of_vars x *
     polynom_of_list (map (\<lambda>(ys, n). (ys, f n)) va)\<close>
  by (induction va)
   (auto simp: Const_add algebra_simps)

lemma polynom_of_list_map_mult2:
  \<open>polynom_of_list (map (\<lambda>(ys, n). (ys, n * m)) va) =
     Const\<^sub>0 m *
     polynom_of_list (map (\<lambda>(ys, n). (ys, n)) va)\<close>
  by (induction va)
    (auto simp: Const\<^sub>0_add algebra_simps Const\<^sub>0_mult)


lemma polynom_of_list_mult_poly_raw[simp]:
  \<open>polynom_of_list (mult_poly_raw xs ys) = polynom_of_list xs * polynom_of_list ys\<close>
  apply (induction xs ys rule: mult_poly_raw.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x m xs ys
    by (cases ys)
     (auto simp: Const\<^sub>0_add algebra_simps
       polynom_of_list_map_mult polynom_of_list_map_mult2
      Const\<^sub>0_mult)
  done


lemma polynom_of_list_normalize_poly[simp]:
  \<open>polynom_of_list (normalize_poly xs) = polynom_of_list xs\<close>
  by (auto simp: normalize_poly_def)


lemma polynom_of_list_mult_poly[simp]:
  \<open>polynom_of_list (mult_poly xs ys) = polynom_of_list xs * polynom_of_list ys\<close>
  by (auto simp: mult_poly_def)


lemma (in -) ideal_mult_right_in:
  \<open>a \<in> ideal A \<Longrightarrow> a * b \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))

lemma (in -) ideal_mult_right_in2:
  \<open>a \<in> ideal A \<Longrightarrow> b * a \<in> More_Modules.ideal A\<close>
  by (metis ideal.span_scale linordered_field_class.sign_simps(5))


lemma (in -) X2_X_polynom_bool_mult_in:
  \<open>Var\<^sub>0 (x1) * (Var\<^sub>0 (x1) * p) -  Var\<^sub>0 (x1) * p \<in> More_Modules.ideal polynom_bool\<close>
  using ideal_mult_right_in[OF  X2_X_in_pac_ideal[of x1 \<open>{}\<close>], of p]
  by (auto simp: right_diff_distrib ac_simps power2_eq_square)


lemma polynom_of_list_remove_powers_polynom_bool:
  \<open>(polynom_of_list xs) - polynom_of_list (remove_powers xs) \<in> ideal polynom_bool\<close>
proof (induction xs)
  case Nil
  then show \<open>?case\<close> by (auto simp: remove_powers_def ideal.span_zero)
next
  case (Cons x xs)
  have H1: \<open>x1 \<in># x2 \<Longrightarrow>
       Var\<^sub>0 (\<phi> x1) * poly_of_vars x2 - p \<in> More_Modules.ideal polynom_bool \<longleftrightarrow>
       poly_of_vars x2 - p \<in> More_Modules.ideal polynom_bool
       \<close> for x1 x2 p
    apply (subst (2) ideal.span_add_eq[symmetric,
      of \<open>Var\<^sub>0 (\<phi> x1) * poly_of_vars x2 - poly_of_vars x2\<close>])
    apply (drule multi_member_split)
    apply (auto simp: X2_X_polynom_bool_mult_in)
    done

  have \<open>poly_of_vars (x) - poly_of_vars (remdups_mset (x)) \<in> ideal polynom_bool\<close> for x
    apply (induction x)
    apply (auto simp: remove_powers_def ideal.span_zero H1)
    apply (metis ideal.span_scale right_diff_distrib)
    done
  from ideal_mult_right_in2[OF this, of \<open>Const\<^sub>0 (snd x)\<close> \<open>fst x\<close>]
  show ?case
    using Cons
    apply (cases x)
    apply (auto simp: remove_powers_def right_diff_distrib
      ideal.span_diff ideal.span_add ac_simps)
   by (metis (no_types, lifting) add.commute add_diff_add ideal.span_add_eq)
qed

end

end

