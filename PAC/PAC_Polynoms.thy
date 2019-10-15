theory PAC_Polynoms
  imports PAC_Specification
begin


lemma poly_embed_EX:
  \<open>\<exists>\<phi>. bij (\<phi> :: string list \<Rightarrow> nat)\<close>
  by (rule countableE_infinite[of \<open>UNIV :: string list set\<close>])
     (auto intro!: infinite_UNIV_listI)

type_synonym list_polynom =
  \<open>(string set * nat) list\<close>

abbreviation  (in -)vars :: \<open>list_polynom \<Rightarrow> string set list\<close> where
  \<open>vars p \<equiv> map fst p\<close>

abbreviation vars2 :: \<open>list_polynom \<Rightarrow> string set set\<close> where
  \<open>vars2 p \<equiv> fst ` set p\<close>


lemma Const_add:
  \<open>Const (a + b) = Const a + Const b\<close>
  by transfer
   (simp add: Const\<^sub>0_def single_add)

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



locale poly_embed =
  fixes \<phi> :: \<open>string \<Rightarrow> nat\<close>
  assumes \<open>bij \<phi>\<close>
begin

fun polynom_of_list :: \<open>list_polynom \<Rightarrow> _ mpoly\<close> where
  \<open>polynom_of_list [] = 0\<close> |
  \<open>polynom_of_list ((xs, n) # p) =
     Const n * (Finite_Set.fold (\<lambda>a b. Const (\<phi> a) * b) 0 xs) + polynom_of_list p\<close>

lemma polynom_of_list_merge_coeffs[simp]:
  \<open>polynom_of_list (merge_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs rule: merge_coeffs.induct)
    (auto simp: Const_add algebra_simps)

lemma polynom_of_list_remove_empty_coeffs[simp]:
  \<open>polynom_of_list (remove_empty_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs)
    (auto simp: Const_add algebra_simps)

lemma normalized_poly_normalize_poly:
  assumes \<open>sorted_wrt R (map fst xs)\<close> and \<open>transp R\<close> \<open>antisymp R\<close>
  shows \<open>normalized_poly (normalize_poly xs)\<close>
  using distinct_merge_coeffs[OF assms]
  remove_empty_coeffs_notin_0[]
  by (auto simp: normalize_poly_def normalized_poly_def
    distinct_remove_empty_coeffs)

context
  fixes R :: \<open>string set \<Rightarrow> string set \<Rightarrow> bool\<close>
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

lemma polynom_of_list_add_poly[simp]:
  \<open>polynom_of_list (add_poly xs ys) = polynom_of_list xs + polynom_of_list ys\<close>
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x xs y ys
    by (auto simp: Const_add algebra_simps)
  done

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
      apply (smt fst_conv image_iff insert_iff list.set(2) notin_vars_notin_add_polyD)
      apply (smt fst_conv image_iff insert_iff list.set(2) notin_vars_notin_add_polyD)
    done
  done

end

end

end