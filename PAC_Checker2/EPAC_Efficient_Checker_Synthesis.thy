theory EPAC_Efficient_Checker_Synthesis
  imports EPAC_Efficient_Checker
    EPAC_Perfectly_Shared_Vars
    PAC_Checker.PAC_Checker_Synthesis
begin
type_synonym sllist_polynomial = \<open>(nat list \<times> int) list\<close>

definition vars_llist_in_s :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close> where
  \<open>vars_llist_in_s = (\<lambda>(\<V>,\<D>) p. vars_llist p \<subseteq> set_mset \<V>)\<close>

lemma vars_llist_in_s_vars_llist[simp]:
  assumes \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
  shows \<open>vars_llist_in_s \<V> p \<longleftrightarrow> vars_llist p \<subseteq> set_mset \<D>\<V>\<close>
  using assms unfolding perfectly_shared_vars_rel_def perfectly_shared_vars_def vars_llist_in_s_def
  by auto

definition (in -)perfect_shared_var_order_s :: \<open>(nat, string)shared_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>perfect_shared_var_order_s \<D> x y = do {
    eq \<leftarrow> perfectly_shared_strings_equal_l \<D> x y;
    if eq then RETURN EQUAL
    else do {
      x \<leftarrow> get_var_nameS \<D> x;
      y \<leftarrow> get_var_nameS \<D> y;
      if (x, y) \<in> var_order_rel then RETURN (LESS)
      else RETURN (GREATER)
        }}\<close>

lemma perfect_shared_var_order_s_perfect_shared_var_order:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(i, i') \<in> perfectly_shared_var_rel \<V>\<close>and
    \<open>(j, j') \<in> perfectly_shared_var_rel \<V>\<close>
  shows \<open>perfect_shared_var_order_s \<V> i j \<le>\<Down>Id (perfect_shared_var_order \<V>\<D> i' j')\<close>
proof -
  show ?thesis
    unfolding perfect_shared_var_order_s_def perfect_shared_var_order_def
    apply (refine_rcg perfectly_shared_strings_equal_l_perfectly_shared_strings_equal
      get_var_nameS_spec)
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    done
qed

definition (in -) perfect_shared_term_order_rel_s
  :: \<open>(nat, string) shared_vars \<Rightarrow> nat list\<Rightarrow> nat list \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel_s \<V> xs ys  = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         eq \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
         if eq = EQUAL then RETURN (b, tl xs, tl ys)
         else RETURN (eq, xs, ys)
      }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>

lemma perfect_shared_term_order_rel_s_perfect_shared_term_order_rel:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>perfect_shared_term_order_rel_s \<V> xs ys \<le> \<Down>Id (perfect_shared_term_order_rel \<V>\<D> xs' ys')\<close>
  using assms
  unfolding perfect_shared_term_order_rel_s_def perfect_shared_term_order_rel_def
  apply (refine_rcg WHILET_refine[where R = \<open>Id \<times>\<^sub>r perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>]
    perfect_shared_var_order_s_perfect_shared_var_order)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  done


definition (in -)add_poly_l_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<times> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>add_poly_l_s \<D> = REC\<^sub>T
  (\<lambda>add_poly_l (p, q).
  case (p,q) of
    (p, []) \<Rightarrow> RETURN p
    | ([], q) \<Rightarrow> RETURN q
    | ((xs, n) # p, (ys, m) # q) \<Rightarrow> do {
    comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
    if comp = EQUAL then if n + m = 0 then add_poly_l (p, q)
    else do {
      pq \<leftarrow> add_poly_l (p, q);
      RETURN ((xs, n + m) # pq)
    }
    else if comp = LESS
    then do {
      pq \<leftarrow> add_poly_l (p, (ys, m) # q);
      RETURN ((xs, n) # pq)
    }
    else do {
      pq \<leftarrow> add_poly_l ((xs, n) # p, q);
      RETURN ((ys, m) # pq)
    }
  })\<close>


lemma add_poly_l_s_add_poly_l:
  fixes xs :: \<open>sllist_polynomial \<times> sllist_polynomial\<close>
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V> \<times>\<^sub>r perfectly_shared_polynom \<V>\<close>
  shows \<open>add_poly_l_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (add_poly_l_prep \<V>\<D> xs')\<close>
proof -
  have x: \<open>x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow> x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel\<close> for x
    by auto
  show ?thesis
    unfolding add_poly_l_s_def add_poly_l_prep_def
    apply (refine_rcg assms perfect_shared_term_order_rel_s_perfect_shared_term_order_rel)
    apply (rule x)
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
      (*many boring goals, some require unification*)
    by (auto)
qed

definition (in -) mult_monoms_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>mult_monoms_s \<D> xs ys = REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<D> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> f (tl xs, tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (tl xs, ys);
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> f (xs, tl ys);
        RETURN (hd ys # pq)
      }
   }
 }) (xs, ys)\<close>

lemma mult_monoms_s_simps:
  \<open>mult_monoms_s \<V> xs ys =
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) (tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) ys;
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> mult_monoms_s \<V> xs (tl ys);
        RETURN (hd ys # pq)
      }
   }
 }\<close>
  apply (subst mult_monoms_s_def)
  apply (subst RECT_unfold, refine_mono)
  unfolding prod.case[of _ \<open>(xs,ys)\<close>]
  apply (subst mult_monoms_s_def[symmetric])+
  apply (auto intro!: bind_cong[OF refl])
  done

lemma mult_monoms_s_mult_monoms_prep:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>mult_monoms_s \<V> xs ys \<le> \<Down>(perfectly_shared_monom \<V>) ((mult_monoms_prep \<V>\<D> xs' ys'))\<close>
proof -
  have [refine]: \<open>((xs, ys), xs', ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>
    using assms by auto
  have x: \<open>a \<le> \<Down> (perfectly_shared_monom \<V>) b \<Longrightarrow> a \<le> \<Down> (perfectly_shared_monom \<V>) b\<close> for a b
    by auto
  show ?thesis
    using assms unfolding mult_monoms_s_def mult_monoms_prep_def
    apply (refine_vcg perfect_shared_var_order_s_perfect_shared_var_order)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    done
qed


definition (in -) mult_term_s
  :: \<open>(nat,string)shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow>  _ \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>mult_term_s = (\<lambda>\<V> qs (p, m) b. nfoldli qs (\<lambda>_. True) (\<lambda>(q, n) b. do {pq \<leftarrow> mult_monoms_s \<V> p q; RETURN ((pq, m * n) # b)}) b)\<close>

definition mult_poly_s :: \<open>(nat,string) shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mult_poly_s \<V> p q = nfoldli p (\<lambda>_. True) (mult_term_s \<V> q) []\<close>

lemma mult_term_s_mult_monoms_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<close>
    \<open>(zs, zs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_term_s \<V> xs ys zs \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_monoms_prop \<V>\<D> xs' ys' zs')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_term_s_def mult_monoms_prop_def
    by (refine_rcg mult_monoms_s_mult_monoms_prep)
     auto
qed

lemma mult_poly_s_mult_poly_raw_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_poly_s \<V> xs ys \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_poly_raw_prop \<V>\<D> xs' ys')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_poly_s_def mult_poly_raw_prop_def
    by (refine_rcg mult_term_s_mult_monoms_prop)
     auto
qed


lemma op_eq_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

abbreviation ordered_assn :: \<open>ordered \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>ordered_assn \<equiv> id_assn\<close>

lemma op_eq_ordered_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: ordered \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    ordered_assn\<^sup>k *\<^sub>a ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


abbreviation monom_s_assn where
  \<open>monom_s_assn \<equiv> list_assn uint64_nat_assn\<close>

abbreviation poly_s_assn where
  \<open>poly_s_assn \<equiv> list_assn (monom_s_assn \<times>\<^sub>a int_assn)\<close>

sepref_decl_intf wordered is ordered

sepref_register EQUAL LESS GREATER UNKNOWN get_var_nameS perfect_shared_var_order_s perfect_shared_term_order_rel_s
lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return EQUAL), uncurry0 (RETURN EQUAL)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return LESS), uncurry0 (RETURN LESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return GREATER), uncurry0 (RETURN GREATER)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return UNKNOWN), uncurry0 (RETURN UNKNOWN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by (sepref_to_hoare; sep_auto)+

sepref_definition perfect_shared_var_order_s_impl
  is \<open>uncurry2 perfect_shared_var_order_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding perfect_shared_var_order_s_def perfectly_shared_strings_equal_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_var_order_s_impl.refine

sepref_definition perfect_shared_term_order_rel_s_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding perfect_shared_term_order_rel_s_def
   by sepref

lemmas [sepref_fr_rules] = perfect_shared_term_order_rel_s_impl.refine

sepref_definition add_poly_l_prep_impl
  is \<open>uncurry add_poly_l_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (poly_s_assn \<times>\<^sub>a poly_s_assn)\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding add_poly_l_s_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemma [sepref_fr_rules]:
  \<open>(return o is_Nil, RETURN o is_Nil)\<in> (list_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare)
    (sep_auto split: list.splits)

sepref_definition mult_monoms_s_impl
  is \<open>uncurry2 mult_monoms_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding mult_monoms_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_monoms_s_impl.refine

sepref_definition mult_term_s_impl
  is \<open>uncurry3 mult_term_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a int_assn)\<^sup>k *\<^sub>a poly_s_assn\<^sup>k\<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_term_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_term_s_impl.refine


sepref_definition mult_poly_s_impl
  is \<open>uncurry2 mult_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k\<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] =
  mult_poly_s_impl.refine

fun mergeR :: "_ \<Rightarrow> _ \<Rightarrow>  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "mergeR  \<Phi> f (x#xs) (y#ys) = do {
         ASSERT(\<Phi> x y);
         b \<leftarrow> f x y;
         if b then do {zs \<leftarrow> mergeR \<Phi> f xs (y#ys); RETURN (x # zs)}
         else do {zs \<leftarrow> mergeR \<Phi> f (x#xs) ys; RETURN (y # zs)}
       }"
| "mergeR  \<Phi> f xs [] = RETURN xs"
| "mergeR \<Phi> f [] ys = RETURN ys"

lemma mergeR_merge:
  assumes \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close> and
    \<open>(xs,xs')\<in>Id\<close>and
    \<open>(ys,ys')\<in>Id\<close>
  shows
    \<open>mergeR \<Phi> f xs ys \<le> \<Down>Id (RETURN (merge f' xs' ys'))\<close>
proof -
  have xs: \<open>xs' = xs\<close> \<open>ys' = ys\<close>
    using assms
    by auto
  show ?thesis
    using assms(1,2) unfolding xs
    apply (induction f' xs ys arbitrary: xs' ys' rule: merge.induct)
    subgoal for f' x xs y ys
      unfolding mergeR.simps merge.simps
      apply (refine_rcg)
      subgoal by simp
      subgoal premises p
        using p(1,2,3,4,5) p(4)[of x y, simplified]
        apply auto
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        done
      done
    subgoal by auto
    subgoal by auto
    done
qed

lemma merge_alt:
  "RETURN (merge f xs ys) = SPEC(\<lambda>zs. zs = merge f xs ys \<and> set zs = set xs \<union> set ys)"
  by (induction f xs ys rule: merge.induct)
   (clarsimp_all simp: Collect_conv_if insert_commute)

fun msortR :: "_ \<Rightarrow> _ \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "msortR \<Phi> f [] = RETURN []"
| "msortR \<Phi> f [x] = RETURN [x]"
| "msortR \<Phi> f xs = do {
    as \<leftarrow> msortR \<Phi> f (take (size xs div 2) xs);
    bs \<leftarrow> msortR \<Phi> f (drop (size xs div 2) xs);
   mergeR \<Phi> f as bs
  }"

lemma set_msort[simp]: \<open>set (msort f xs) = set xs\<close>
   by (meson mset_eq_setD mset_msort)

lemma msortR_msort:
  assumes \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close>
  shows
    \<open>msortR \<Phi> f xs \<le> \<Down>Id (RETURN (msort f' xs))\<close>
proof -
  have a: \<open>set (take (length xs div 2) (y # xs)) \<subseteq> insert x (insert y (set xs))\<close>
    \<open>set (drop (length xs div 2) (y # xs)) \<subseteq> insert x (insert y (set xs))\<close>
    for x y xs
    by (auto dest: in_set_takeD in_set_dropD)
  have H: \<open>RETURN (msort f' (x#y#xs)) = do {
    let as = msort f' (take (size (x#y#xs) div 2) (x#y#xs));
    let bs = msort f' (drop (size (x#y#xs) div 2) (x#y#xs));
    ASSERT(set (as) \<subseteq> set (x#y#xs));
    ASSERT(set (bs) \<subseteq> set (x#y#xs));
    RETURN (merge f' as bs)}\<close> for x y xs f'
    unfolding Let_def
    by (auto simp: a)
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
  using assms
  apply (induction f' xs rule: msort.induct)
  subgoal by auto
  subgoal by auto
  subgoal premises p for f' x y xs
    using p
    unfolding msortR.simps H
    apply (refine_vcg mergeR_merge p)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  done
qed

lemma merge_list_rel:
  assumes \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set ys \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set ys' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close> and
    \<open>(ys,ys') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(merge f xs ys, merge f' xs' ys') \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  show ?thesis
    using assms
  proof (induction f' xs' ys' arbitrary: f xs ys rule: merge.induct)
    case (1 f' x' xs' y' y's)
    have \<open>f' x' y' \<Longrightarrow>
      (PAC_Checker_Init.merge f (tl xs) ys, PAC_Checker_Init.merge f' xs' (y' # y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    moreover have \<open>\<not>f' x' y' \<Longrightarrow>
      (PAC_Checker_Init.merge f ( xs) (tl ys), PAC_Checker_Init.merge f' (x' # xs') (y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    ultimately show ?case
      using 1(1,4-5) 1(3)[of \<open>hd xs\<close> \<open>hd ys\<close> x' y']
      by (auto simp: list_rel_split_left_iff)
  qed  (auto simp: list_rel_split_left_iff)

qed

lemma msort_list_rel:
  assumes  \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set xs' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(msort f xs, msort f' xs') \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  show ?thesis
    using assms
  proof (induction f' xs' arbitrary: xs f rule: msort.induct)
    case (3 f'' v vb vc)
    have xs: \<open>
      (msort f (take (length xs div 2) xs), msort f'' (take (length (v # vb # vc) div 2) (v # vb # vc))) \<in> \<langle>R\<rangle>list_rel\<close>
      \<open>(msort f (drop (length xs div 2) xs), msort f'' (drop (length (v # vb # vc) div 2) (v # vb # vc))) \<in> \<langle>R\<rangle>list_rel\<close>
      subgoal
        apply (rule 3)
        using 3(3-) apply (force dest!:  in_set_dropD in_set_takeD list_rel_imp_same_length)
        using 3(4) apply (auto simp: list_rel_imp_same_length dest: list_rel_takeD)
        done
      subgoal
        apply (rule 3)
        using 3(3-) apply (force dest!:  in_set_dropD in_set_takeD list_rel_imp_same_length
          dest: )
        using 3(4) apply (auto simp: list_rel_imp_same_length dest: list_rel_dropD)
        done
      done
    have H: \<open>(PAC_Checker_Init.merge f (msort f (x # take (length xsaa div 2) (xa # xsaa)))
      (msort f (drop (length xsaa div 2) (xa # xsaa))),
      PAC_Checker_Init.merge f''  (msort f'' (v # take (length vc div 2) (vb # vc)))
      (msort f'' (drop (length vc div 2) (vb # vc))))
      \<in> \<langle>R\<rangle>list_rel\<close>
      if \<open>xs = x # xa # xsaa\<close> and
        \<open> (x, v) \<in> R\<close> and
        \<open>(xa, vb) \<in> R\<close> and
        \<open> (xa, vb) \<in> R\<close>
      for x xa xsaa
      apply (rule merge_list_rel)
      subgoal for xb y x' y'
        by (rule 3(3))
          (use that in \<open>auto dest: in_set_takeD in_set_dropD\<close>)
      subgoal
        by (use xs(1) 3(4) that in auto)
      subgoal
        by (use xs(2) 3(4) that in auto)
      done
    show ?case
      using 3(3-) H by (auto simp: list_rel_split_left_iff)
  qed (auto simp: list_rel_split_left_iff intro!: )
qed


lemma msortR_alt_def:
  \<open>(msortR \<Phi> f xs) = REC\<^sub>T(\<lambda>msortR' xs.
  if length xs \<le> 1 then RETURN xs else do {
    let xs1 = (take ((size xs) div 2) xs);
    let xs2 = (drop ((size xs) div 2) xs);
    as \<leftarrow> msortR' xs1;
    bs \<leftarrow> msortR' xs2;
    (mergeR \<Phi> f as bs)
  }) xs
      \<close>
 apply (induction \<Phi> f xs rule: msortR.induct)
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 done
lemma in_set_rel_inD: \<open>(x,y) \<in>\<langle>R\<rangle>list_rel \<Longrightarrow> a \<in> set x \<Longrightarrow> \<exists>b \<in> set y. (a,b)\<in> R\<close>
  by (metis (no_types, lifting) Un_iff list.set_intros(1) list_relE3 list_rel_append1 set_append split_list_first)

lemma perfectly_shared_monom_eqD: \<open>(a, ab) \<in> perfectly_shared_monom \<V> \<Longrightarrow> ab = map ((the \<circ>\<circ> fmlookup) (fst (snd \<V>))) a\<close>
  by (induction a arbitrary: ab)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
      list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def)


lemma msortR_sort_spec:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<V>\<D>\<close>
 shows
  \<open>msortR (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)}) xs
  \<le>\<Down>(perfectly_shared_polynom \<V>)
  (sort_poly_spec xs')
   \<close>
proof -
  have [iff]: \<open>sorted_wrt (rel2p (Id \<union> term_order_rel)) (map fst (msort (\<lambda>xs ys. rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) xs'))\<close>
    unfolding sorted_wrt_map
    apply (rule sorted_msort)
    apply (smt Un_iff pair_in_Id_conv rel2p_def term_order_rel_trans transp_def)
    apply (auto simp: rel2p_def)
    using total_on_lexord_less_than_char_linear var_order_rel_def by auto
  have [iff]:
    \<open>(a,b)\<in> \<langle>\<langle>(perfectly_shared_var_rel \<V>)\<inverse>\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<longleftrightarrow> (b,a)\<in>perfectly_shared_polynom \<V>\<close> for a b
    by (metis converse_Id converse_iff inv_list_rel_eq inv_prod_rel_eq)

  show ?thesis
    apply (rule order_trans[OF msortR_msort[where
      f'=\<open> \<lambda>xs ys. (map (the o fmlookup (fst (snd \<V>))) (fst xs), map (the o fmlookup (fst (snd \<V>))) (fst ys)) \<in> Id \<union> term_order_rel\<close>]])
    subgoal for x y
      apply (cases x, cases y)
      using assms by (auto simp: list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
        perfectly_shared_vars_rel_def append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
        dest!: split_list split: prod.splits)
      subgoal for x y
        using assms(2,3) apply -
        apply (frule in_set_rel_inD)
        apply assumption
        apply (frule in_set_rel_inD[of _ _ _ y])
        apply assumption
        apply (elim bexE)+
        subgoal for x' y'
          apply (refine_vcg perfect_shared_term_order_rel_s_perfect_shared_term_order_rel[OF assms(1), THEN order_trans,
            of _ \<open>fst x'\<close> _ \<open>fst y'\<close>])
          subgoal
            by (cases x', cases x) auto
          subgoal
            by (cases y', cases y) auto
          subgoal
            using assms
            apply (clarsimp dest!: split_list intro!: perfect_shared_term_order_rel_spec[THEN order_trans]
              simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
              vars_llist_def)
            apply (rule perfect_shared_term_order_rel_spec[THEN order_trans])
            apply auto[]
            apply auto[]
            apply simp
            apply (clarsimp_all simp: perfectly_shared_monom_eqD)
            apply (cases x, cases y, cases x', cases y')
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD)
            apply (case_tac xa)
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD simp: lexord_irreflexive)
            by (meson lexord_irreflexive term_order_rel_trans var_order_rel_antisym)
          done
        done
      unfolding sort_poly_spec_def conc_fun_RES
      apply auto
      apply (subst Image_iff)
      apply (rule_tac x= \<open>msort (\<lambda>xs ys.  rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) (xs')\<close> in bexI)
      apply (auto intro!: msort_list_rel simp flip: perfectly_shared_monom_eqD
          simp: assms)
      apply (auto simp: rel2p_def)
      done
qed

sepref_register take drop
lemma [sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry (return oo take), uncurry (RETURN oo take)) \<in> nat_assn\<^sup>k *\<^sub>a (list_assn R)\<^sup>k \<rightarrow>\<^sub>a list_assn R\<close>
  apply sepref_to_hoare
  using assms unfolding is_pure_conv CONSTRAINT_def
  apply (sep_auto simp add: list_assn_pure_conv)
  apply (sep_auto simp: pure_def list_rel_takeD)
  done

lemma [sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry (return oo drop), uncurry (RETURN oo drop)) \<in> nat_assn\<^sup>k *\<^sub>a (list_assn R)\<^sup>k \<rightarrow>\<^sub>a list_assn R\<close>
  apply sepref_to_hoare
  using assms unfolding is_pure_conv CONSTRAINT_def
  apply (sep_auto simp add: list_assn_pure_conv)
  apply (sep_auto simp: pure_def list_rel_dropD)
  done

definition mergeR_vars :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mergeR_vars \<V> = mergeR
   (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)})\<close>
lemma mergeR_alt_def:
  \<open>(mergeR \<Phi> f xs ys) = REC\<^sub>T(\<lambda>mergeR xs.
  case xs of
    ([], ys) \<Rightarrow> RETURN ys
  | (xs, []) \<Rightarrow> RETURN xs
  | (x # xs, y # ys) \<Rightarrow> do {
    ASSERT(\<Phi> x y);
     b \<leftarrow> f x y;
    if b then do {
       zs \<leftarrow> mergeR (xs, y # ys);
       RETURN (x # zs)
    }
    else do {
     zs \<leftarrow> mergeR (x # xs, ys);
     RETURN (y # zs)
    }
  })
  (xs, ys)\<close>
 apply (induction \<Phi> f xs ys rule: mergeR.induct)
 subgoal
   apply (subst RECT_unfold, refine_mono)
   apply (simp add:)
   apply (rule bind_cong[OF refl])+
   apply auto
   done
 subgoal
   by (subst RECT_unfold, refine_mono)
    (simp split: list.splits)
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 done

sepref_definition mergeR_vars_impl
  is \<open>uncurry2 mergeR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mergeR_vars_def mergeR_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mergeR_vars_impl.refine


definition msortR_vars :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>msortR_vars \<V> = msortR
   (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
  (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)})\<close>

sepref_register mergeR_vars msortR_vars

sepref_definition msortR_vars_impl
  is \<open>uncurry msortR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding msortR_vars_def msortR_alt_def  mergeR_vars_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] =
  msortR_vars_impl.refine

lemma perfectly_shared_monom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_monom \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_eqD by blast

lemma perfectly_shared_monom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
    list_rel_split_left_iff perfectly_shared_vars_rel_def perfectly_shared_vars_def
    list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
    add_mset_eq_add_mset
    dest!: multi_member_split[of _ \<open>dom_m _\<close>])

lemma perfectly_shared_polynom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_polynom \<V> \<Longrightarrow> y = y'\<close>
  by (induction x arbitrary: y y')
    (auto dest: perfectly_shared_monom_unique_left simp: list_rel_split_right_iff)
lemma perfectly_shared_polynom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto dest: perfectly_shared_monom_unique_right simp: list_rel_split_left_iff
    list_rel_split_right_iff)

fun merge_coeffs_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>merge_coeffs_s [] = []\<close> |
  \<open>merge_coeffs_s [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs_s ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs_s ((xs, n + m) # p) else merge_coeffs_s p
      else (xs, n) # merge_coeffs_s ((ys, m) # p))\<close>

lemma perfectly_shared_merge_coeffs_merge_coeffs:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>(merge_coeffs_s xs, merge_coeffs xs') \<in> (perfectly_shared_polynom \<V>)\<close>
  using assms
  apply (induction xs arbitrary: xs' rule: merge_coeffs_s.induct)
  subgoal
    by auto
  subgoal
    by (auto simp: list_rel_split_right_iff)
  subgoal
    by(auto simp: list_rel_split_right_iff dest: perfectly_shared_monom_unique_left
      perfectly_shared_monom_unique_right)
  done

definition normalize_poly_s :: \<open>_\<close> where
  \<open>normalize_poly_s \<V> p =  do {
  p \<leftarrow> msortR_vars \<V> p;
  RETURN (merge_coeffs_s p)
  }\<close>

lemma normalize_poly_s_normalize_poly_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>normalize_poly_s \<V> xs \<le> \<Down> (perfectly_shared_polynom \<V>) (normalize_poly xs')\<close>
  unfolding normalize_poly_s_def normalize_poly_def
  by (refine_rcg msortR_sort_spec[unfolded msortR_vars_def[symmetric]] assms
    perfectly_shared_merge_coeffs_merge_coeffs)

definition check_linear_combi_l_s_dom_err :: \<open>sllist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_dom_err p r = SPEC (\<lambda>_. True)\<close>

definition mult_poly_full_s :: \<open>_\<close> where
  \<open>mult_poly_full_s \<V> p q = do {
    pq \<leftarrow> mult_poly_s \<V> p q;
   normalize_poly_s \<V> pq
  }\<close>

lemma mult_poly_full_s_mult_poly_full_prop:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close> and
    \<open>vars_llist ys' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>mult_poly_full_s \<V> xs ys \<le> \<Down> (perfectly_shared_polynom \<V>) (mult_poly_full_prop \<D>\<V> xs' ys')\<close>
  unfolding mult_poly_full_s_def mult_poly_full_prop_def
  by (refine_rcg mult_poly_s_mult_poly_raw_prop assms normalize_poly_s_normalize_poly_s)
   (use assms in auto)

thm linear_combi_l_prep_def
thm linear_combi_l_def
thm check_linear_combi_l_def

definition (in -)linear_combi_l_prep_s
  :: \<open>nat \<Rightarrow> _ \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _ \<Rightarrow> (sllist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>
where
  \<open>linear_combi_l_prep_s i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      let (q :: llist_polynomial, i) = hd xs;
      if (i \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p i;
        RETURN (p, xs, error_msg i err)
      } else do {
        ASSERT(fmlookup A i \<noteq> None);
        let r = the (fmlookup A i);
        (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
        q \<leftarrow> mult_poly_full_s \<V> q r;
        pq \<leftarrow> add_poly_l_s \<V> (p, q);
        RETURN (pq, tl xs, CSUCCESS)
        }
        })
        ([], xs, CSUCCESS)
          }\<close>

lemma normalize_poly_sharedS_normalize_poly_shared:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> Id\<close>
  shows \<open>normalize_poly_sharedS \<V> xs
    \<le> \<Down>(bool_rel \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (normalize_poly_shared \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>full_normalize_poly xs \<le> \<Down> Id (full_normalize_poly xs')\<close>
    using assms by auto
  show ?thesis
    unfolding normalize_poly_sharedS_def normalize_poly_shared_def
    by (refine_rcg assms import_poly_no_newS_import_poly_no_new)
qed


lemma linear_combi_l_prep_s_linear_combi_l_prep:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close>
    \<open>(xs,xs') \<in> Id\<close>
  shows \<open>linear_combi_l_prep_s i A \<V> xs
    \<le> \<Down>(perfectly_shared_polynom \<V> \<times>\<^sub>r Id \<times>\<^sub>r Id)
    (linear_combi_l_prep2 j B \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_s_dom_err a b
    \<le> \<Down> Id
    (check_linear_combi_l_dom_err c d)\<close> for a b c d
    unfolding check_linear_combi_l_dom_err_def check_linear_combi_l_s_dom_err_def
    by auto
  show ?thesis
    unfolding linear_combi_l_prep_s_def linear_combi_l_prep2_def
    apply (refine_rcg normalize_poly_sharedS_normalize_poly_shared
      mult_poly_full_s_mult_poly_full_prop add_poly_l_s_add_poly_l)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using fmap_rel_nat_rel_dom_m[OF assms(2)] unfolding in_dom_m_lookup_iff by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition check_linear_combi_l_s_mult_err :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_mult_err pq r = SPEC (\<lambda>_. True)\<close>

definition weak_equality_l_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> bool nres\<close> where
  \<open>weak_equality_l_s p q = RETURN (p = q)\<close>

definition check_linear_combi_l_s where
  \<open>check_linear_combi_l_s spec A \<V> i xs r = do {
  (mem_err, r) \<leftarrow> import_poly_no_newS \<V> r;
  if mem_err \<or> i \<in># dom_m A \<or> xs = []
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i (i \<in># dom_m A) (xs = []) (mem_err);
    RETURN (error_msg i err, r)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l_prep_s i A \<V> xs;
    if (is_cfailed err)
    then do {
      RETURN (err, r)
    }
    else do {
      b \<leftarrow> weak_equality_l_s p r;
      b' \<leftarrow> weak_equality_l_s r spec;
      if b then (if b' then RETURN (CFOUND, r) else RETURN (CSUCCESS, r)) else do {
        c \<leftarrow> check_linear_combi_l_s_mult_err p r;
        RETURN (error_msg i c, r)
      }
    }
        }}\<close>
lemma weak_equality_l_s_weak_equality_l:
  fixes a :: sllist_polynomial and b :: llist_polynomial and \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(a,b) \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(c,d) \<in> perfectly_shared_polynom \<V>\<close>
  shows
    \<open>weak_equality_l_s a c \<le>\<Down>bool_rel (weak_equality_l b d)\<close>
  using assms perfectly_shared_polynom_unique_left[OF assms(2), of d]
    perfectly_shared_polynom_unique_right[OF assms(1,2), of c]
  unfolding weak_equality_l_s_def weak_equality_l_def
  by auto
    lemma check_linear_combi_l_s_check_linear_combi_l:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(xs,xs')\<in> Id\<close>
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>check_linear_combi_l_s spec A \<V> i r xs
    \<le> \<Down>(Id \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (check_linear_combi_l_prop spec' B \<D>\<V> j r' xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_pre_err a b c d \<le> \<Down>Id (check_linear_combi_l_pre_err u x y z)\<close>
    for a b c d u x y z
    by  (auto simp: check_linear_combi_l_pre_err_def)
  have [refine]: \<open>check_linear_combi_l_s_mult_err a b \<le> \<Down>Id (check_linear_combi_l_mult_err u x)\<close>
    for a b u x
    by  (auto simp: check_linear_combi_l_s_mult_err_def check_linear_combi_l_mult_err_def)

  show ?thesis
    unfolding check_linear_combi_l_s_def check_linear_combi_l_prop_def
    apply (refine_rcg import_poly_no_newS_import_poly_no_new assms
      linear_combi_l_prep_s_linear_combi_l_prep weak_equality_l_s_weak_equality_l)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

definition check_extension_l_s_new_var_multiple_err :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_s_new_var_multiple_err v p = SPEC (\<lambda>_. True)\<close>

definition check_extension_l_s_side_cond_err
  :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close>
where
  \<open>check_extension_l_s_side_cond_err v p p' q = SPEC (\<lambda>_. True)\<close>

definition (in -)check_extension_l2_s
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> (nat,string)shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial \<Rightarrow> (string code_status \<times> sllist_polynomial \<times> (nat,string)shared_vars) nres\<close>
where
\<open>check_extension_l2_s spec A \<V> i v p = do {
  let pre = i \<notin># dom_m A \<and> v \<notin> set_mset (fst \<V>) \<and> ([v], -1) = hd p;
  let p' = tl p;
  let nonew = vars_llist_in_s \<V> p';
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  let p' = tl p;
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p';
        RETURN (error_msg i c, [], \<V>)
      }
      else do {
         p2 \<leftarrow> mult_poly_full_s \<V> p' p';
         let p'' = map (\<lambda>(a,b). (a, -b)) p';
         q \<leftarrow> add_poly_l_s \<V> (p2, p'');
         eq \<leftarrow> weak_equality_l_s q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>)
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>)
        }
      }
    }
           }\<close>
lemma list_rel_tlD: \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (tl a, tl b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (metis list.sel(2) list.sel(3) list_rel_simp(1) list_rel_simp(2) list_rel_simp(4) neq_NilE)

lemma check_extension_l2_prop_alt_def:
  \<open>check_extension_l2_prop spec A \<V> i v p = do {
  let pre = i \<notin># dom_m A \<and> v \<notin> set_mset \<V> \<and> ([v], -1) \<in> set p;
  let p' = remove1 ([v], -1) p;
  let nonew = vars_llist p' \<subseteq> set_mset \<V>;
  (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  let p' = p';

  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p';
        RETURN (error_msg i c, [], \<V>)
      }
      else do {
         ASSERT(vars_llist p' \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p' p';
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p';
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>)
        }
      }
    }
 }\<close>
    unfolding check_extension_l2_prop_def Let_def by (auto intro!: bind_cong[OF refl])

lemma list_rel_mapI: \<open>(xs,ys) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (f x, g y) \<in> S) \<Longrightarrow> (map f xs, map g ys) \<in> \<langle>S\<rangle>list_rel\<close>
  by (induction xs arbitrary: ys)
     (auto simp: list_rel_split_right_iff)
lemma check_extension_l2_s_check_extension_l2:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(xs,xs')\<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>xs' = ([r], -1) # ys\<close>
  shows \<open>check_extension_l2_s spec A \<V> i r xs
    \<le> \<Down>{((err, p, A), (err', p', A')).
    (err, err') \<in> Id \<and>
    (p, p') \<in> perfectly_shared_polynom A \<and>
    (\<not>is_cfailed err \<longrightarrow> (A, A') \<in> {(a,b). (a,b) \<in> perfectly_shared_vars_rel \<and> perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom a})}
    (check_extension_l2_prop spec' B \<D>\<V> j r' xs')\<close>
proof -
  have [refine]: \<open>check_extension_l_s_new_var_multiple_err a b \<le>\<Down>Id (check_extension_l_new_var_multiple_err a' b')\<close> for a a' b b'
    by (auto simp: check_extension_l_s_new_var_multiple_err_def check_extension_l_new_var_multiple_err_def)

  have [refine]: \<open>check_extension_l_dom_err i \<le> \<Down> (Id) (check_extension_l_dom_err j)\<close>
    by (auto simp: check_extension_l_dom_err_def)
  have [refine]: \<open>check_extension_l_s_side_cond_err a b c d \<le> \<Down>Id (check_extension_l_side_cond_err a' b' c' d')\<close> for a b c d a' b' c' d'
    by (auto simp: check_extension_l_s_side_cond_err_def check_extension_l_side_cond_err_def)
  have G: \<open>(a, b) \<in> import_poly_rel \<V> x \<Longrightarrow> \<not>alloc_failed (fst a) \<Longrightarrow>
    (snd (snd a), snd (snd b)) \<in> perfectly_shared_vars_rel\<close> for a b x
    by auto
  show ?thesis
    unfolding check_extension_l2_s_def check_extension_l2_prop_alt_def nres_monad3
    apply (refine_rcg import_polyS_import_poly assms mult_poly_full_s_mult_poly_full_prop)
    subgoal using assms by (auto simp add: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
    subgoal using assms by (simp)
    subgoal using assms by (cases xs, auto)
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by (cases xs; auto dest: list_rel_tlD)
    subgoal using assms by (cases xs; auto dest: list_rel_tlD)
      apply (rule add_poly_l_s_add_poly_l)
    subgoal by auto
    subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c p2 p2a
      using assms
      by (cases xs; auto intro!: list_rel_mapI[of _ _ \<open>perfectly_shared_monom x2c \<times>\<^sub>r int_rel\<close>]
        dest: list_rel_tlD)
    apply (rule weak_equality_l_s_weak_equality_l)
    apply (rule G, assumption)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

definition PAC_checker_l_step_s
  :: \<open>sllist_polynomial \<Rightarrow> string code_status \<times> (nat,string)shared_vars \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close>
where
  \<open>PAC_checker_l_step_s = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT (\<not>is_cfailed st');
    case st of
     CL _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> full_normalize_poly (pac_res st);
        (eq, r) \<leftarrow> check_linear_combi_l_s spec A \<V> (new_id st) (pac_srcs st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmupd (new_id st) r A)
       else RETURN (eq, \<V>, A)
     }
    | Del _ \<Rightarrow>
       do {
        eq \<leftarrow> check_del_l spec A (pac_src1 st);
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmdrop (pac_src1 st) A)
        else RETURN (eq, \<V>, A)
     }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (([new_var st], -1) # (pac_res st));
        (eq, r, \<V>) \<leftarrow> check_extension_l2_s spec A (\<V>) (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then RETURN (st', \<V>, fmupd (new_id st) r A)
        else RETURN (eq, \<V>, A)
     }}
          )\<close>
lemma is_cfailed_merge_cstatus:
  "is_cfailed (merge_cstatus c d) \<longleftrightarrow> is_cfailed c \<or> is_cfailed d"
  by (cases c; cases d) auto
          find_theorems "case_pac_step" If
lemma check_extension_l2_s_check_extension_l2:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(err, err') \<in> Id\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>PAC_checker_l_step_s spec (err, \<V>, A) st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
     \<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel)}
    (PAC_checker_l_step_prep spec' (err', \<D>\<V>, B) st')\<close>
proof -
  find_theorems is_cfailed merge_cstatus
  have HID: \<open>f = f' \<Longrightarrow> f \<le> \<Down>Id f'\<close> for f f'
    by auto
  show ?thesis
    unfolding PAC_checker_l_step_s_def PAC_checker_l_step_prep_def pac_step.case_eq_if
      prod.simps
    apply (refine_rcg check_linear_combi_l_s_check_linear_combi_l
      check_extension_l2_s_check_extension_l2)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by (auto simp: is_cfailed_merge_cstatus intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto


find_theorems fmap_rel fmupd



find_theorems list_rel map
 find_theorems weak_equality_l_s weak_equality_l

    
thm check_extension_l2_prop_def

thm PAC_checker_l_step_prep_def

find_theorems linear_combi_l_prep
    term linear_combi_l_prep
    find_theorems add_poly_l
    term check_linear_combi_l
thm full_normalize_poly_def
  find_theorems sort_poly_spec
  find_theorems
  thm sort_poly_spec_def
end
