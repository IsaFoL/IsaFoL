theory PAC_Polynoms_List
  imports PAC_Polynoms
begin

type_synonym list_polynom =
  \<open>(term_poly * int) list\<close>

type_synonym list_polynom_order =
  \<open>term_poly \<Rightarrow> term_poly \<Rightarrow> bool\<close>

definition normalized_poly_l :: \<open>list_polynom_order \<Rightarrow> list_polynom \<Rightarrow> bool\<close> where
  \<open>normalized_poly_l R xs \<longleftrightarrow>
    normalized_poly (mset xs) \<and>
    sorted_wrt R (map fst xs)\<close>

lemma normalized_poly_l_simps[simp]:
  \<open>normalized_poly_l R []\<close>
  \<open>normalized_poly_l R ((y, n) # p) \<longleftrightarrow>
    normalized_poly_l R p \<and>
    n \<noteq> 0 \<and>
    y \<notin>  fst ` set p \<and>
    (\<forall>x \<in> set p. R y (fst x))\<close>
  unfolding normalized_poly_l_def normalized_poly_def
  by auto

fun merge_coeffs :: \<open>list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>merge_coeffs [] = []\<close> |
  \<open>merge_coeffs [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then merge_coeffs ((xs, n + m) # p)
    else (xs, n) # merge_coeffs ((ys, m) # p))\<close>


abbreviation  (in -)mononoms_l :: \<open>list_polynom \<Rightarrow> term_poly list\<close> where
  \<open>mononoms_l p \<equiv> map fst p\<close>

abbreviation  (in -)mononoms :: \<open>list_polynom \<Rightarrow> term_poly set\<close> where
  \<open>mononoms p \<equiv> fst `set p\<close>

lemma fst_normalize_polynom_subset:
  \<open>mononoms (merge_coeffs p) \<subseteq> mononoms p\<close>
  by (induction p rule: merge_coeffs.induct)  auto


lemma fst_normalize_polynom_Cons_subset[simp]:
  \<open>mononoms (merge_coeffs p) = mononoms p\<close>
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
  \<open>distinct (mononoms_l xs) \<Longrightarrow> distinct (mononoms_l (remove_empty_coeffs xs))\<close>
  by (induction xs) (auto dest!: in_set_remove_empty_coeffsD)

definition normalize_poly where
  \<open>normalize_poly p = remove_empty_coeffs (merge_coeffs p)\<close>


context
  fixes R :: \<open>list_polynom_order\<close>
begin

fun add_poly :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom nres\<close> where
  \<open>add_poly [] p = RETURN p\<close> |
  \<open>add_poly p [] = p\<close> |
  \<open>add_poly ((xs, n) # p) ((ys, m) # q) =
    (if xs = ys then if n + m = 0 then add_poly p q else (xs, n + m) # add_poly p q
    else if R xs ys then (xs, n) # add_poly p ((ys, m) # q)
    else (ys, m) # add_poly ((xs, n) # p) q)\<close>

lemma add_poly_simps[simp]:
  \<open>add_poly p [] = p\<close>
  by (cases p) auto

lemma notin_mononoms_notin_add_polyD:
  \<open>x \<notin> mononoms xs \<Longrightarrow>  x \<notin> mononoms ys \<Longrightarrow> x \<notin> mononoms (add_poly xs ys)\<close>
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x xs y ys
    by (auto simp: Const_add algebra_simps)
  done


lemma notin_mononoms_notin_add_polyD2:
  \<open>x \<notin> mononoms xs \<Longrightarrow>  x \<notin> mononoms ys \<Longrightarrow> (x, a) \<notin> set (add_poly xs ys)\<close>
  apply (induction xs ys rule: add_poly.induct)
  subgoal
    by (auto simp: image_iff)
  subgoal
    by (auto simp: image_iff)
  subgoal for x xs y ys
    by (auto simp: Const_add algebra_simps)
  done

lemma in_set_add_poly_in_mononoms_eitherE:
  \<open>(x, a) \<in>  set (add_poly xs ys) \<Longrightarrow> (x \<in> mononoms xs \<Longrightarrow> P) \<Longrightarrow> (x \<in> mononoms ys \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using notin_mononoms_notin_add_polyD2 by blast

lemma total_onD:
  \<open>total_on R' A \<Longrightarrow> (\<not>R' x y) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> R' y x\<close>
  unfolding total_on_def
  by (auto simp: total_on_def)


lemma normalized_poly_l_add_poly:
  \<open>transp R \<Longrightarrow> antisymp R \<Longrightarrow> total_on R UNIV \<Longrightarrow> normalized_poly_l R p \<Longrightarrow> normalized_poly_l R q \<Longrightarrow>
    normalized_poly_l R (add_poly p q)\<close>
  apply (induction p q rule: add_poly.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal for xs n p ys m q
    by auto 
     ((auto elim!: in_set_add_poly_in_mononoms_eitherE dest: antisympD transpD
        dest!: total_onD)+)
  done
end


context poly_embed
begin

fun polynom_of_list :: \<open>list_polynom \<Rightarrow> _\<close> where
  \<open>polynom_of_list [] = Const 0\<close> |
  \<open>polynom_of_list ((xs, n) # p) =
     Const n * poly_of_vars xs + polynom_of_list p\<close>

lemma polynom_of_list_alt_def[simp]:
  \<open>polynom_of_list xs = polynom_of_mset (mset xs)\<close>
  by (induction xs) (auto)

declare polynom_of_list.simps[simp del]

lemma polynom_of_list_cong:
  \<open>mset xs = mset ys \<Longrightarrow> polynom_of_list xs = polynom_of_list ys\<close>
  by auto


lemma polynom_of_list_merge_coeffs[simp]:
  \<open>polynom_of_list (merge_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs rule: merge_coeffs.induct)
    (auto simp: Const_add algebra_simps)

lemma polynom_of_list_remove_empty_coeffs[simp]:
  \<open>polynom_of_list (remove_empty_coeffs xs) = polynom_of_list xs\<close>
  by (induction xs)
    (auto simp: Const_add Const_def algebra_simps)



lemma polynom_of_list_add_poly[simp]:
  \<open>polynom_of_list (add_poly R xs ys) = polynom_of_list xs + polynom_of_list ys\<close>
  apply (induction xs ys rule: add_poly.induct[of _ R])
  subgoal
    by auto
  subgoal
    by auto
  subgoal for x m xs y n ys
    by (auto simp: Const_add algebra_simps group_add_class.add_eq_0_iff2)
  done


lemma polynom_of_list_map_mult:
  \<open>polynom_of_list (map (\<lambda>(ys, n). (ys + x, f n)) va) =
     poly_of_vars x *
     polynom_of_list (map (\<lambda>(ys, n). (ys, f n)) va)\<close>
  by (induction va)
   (auto simp: Const_add algebra_simps)

lemma polynom_of_list_map_mult2:
  \<open>polynom_of_list (map (\<lambda>(ys, n). (ys, n * m)) va) =
     Const m *
     polynom_of_list (map (\<lambda>(ys, n). (ys, n)) va)\<close>
  by (induction va)
    (auto simp: Const_add algebra_simps Const_mult)

fun mult_poly_raw_l :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>mult_poly_raw_l [] p = []\<close> |
  \<open>mult_poly_raw_l p [] = []\<close> |
  \<open>mult_poly_raw_l ((xs, m) # p) q =
     map (\<lambda>(ys, n). (xs + ys, n * m)) q @
     mult_poly_raw_l p q\<close>

definition mult_poly_l :: \<open>list_polynom \<Rightarrow> list_polynom \<Rightarrow> list_polynom\<close> where
  \<open>mult_poly_l xs ys = normalize_poly (mult_poly_raw_l xs ys)\<close>

lemma mult_poly_raw_l_mult_poly_raw:
  \<open>mset (mult_poly_raw_l p q) = mult_poly_raw (mset p) (mset q)\<close>
  by (induction p q rule: mult_poly_raw_l.induct)
    (auto simp: mult_poly_raw_def algebra_simps mult_poly_by_monom_def
    intro!: image_mset_cong)

lemma polynom_of_list_mult_mult_poly_raw_l[simp]:
  \<open>polynom_of_list (mult_poly_raw_l xs ys) = polynom_of_list xs * polynom_of_list ys\<close>
  by (auto simp: mult_poly_raw_l_mult_poly_raw)

lemma polynom_of_mset_remove_empty_coeffs[simp]:
  \<open>polynom_of_mset (mset (remove_empty_coeffs xs)) =
            polynom_of_mset (mset xs)\<close>
  by (induction xs) auto


lemma polynom_of_mset_merge_coeffs[simp]:
  \<open>polynom_of_mset (mset (merge_coeffs xs)) =
            polynom_of_mset (mset xs)\<close>
  apply (induction xs)
  apply auto
  using polynom_of_list_merge_coeffs by auto


lemma polynom_of_list_normalize_poly[simp]:
  \<open>polynom_of_list (normalize_poly xs) = polynom_of_list xs\<close>
  by (auto simp: normalize_poly_def)


lemma polynom_of_list_mult_poly[simp]:
  \<open>polynom_of_list (mult_poly_l xs ys) = polynom_of_list xs * polynom_of_list ys\<close>
  unfolding mult_poly_l_def polynom_of_list_normalize_poly
    polynom_of_list_mult_mult_poly_raw_l
  ..

end

end
