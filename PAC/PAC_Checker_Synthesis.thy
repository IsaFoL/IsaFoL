theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort PAC_Checker_Relation
    PAC_Checker_Init
    "../Weidenbach_Book/Watched_Literals/WB_More_Refinement_Loops"
begin

section \<open>Code Synthesis of the Checker\<close>

abbreviation vars_assn where
  \<open>vars_assn \<equiv> hs.assn string_assn\<close>

fun vars_of_monom_in where
  \<open>vars_of_monom_in [] _ = True\<close> |
  \<open>vars_of_monom_in (x # xs) \<V> \<longleftrightarrow> x \<in> \<V> \<and> vars_of_monom_in xs \<V>\<close>

fun vars_of_poly_in where
  \<open>vars_of_poly_in [] _ = True\<close> |
  \<open>vars_of_poly_in ((x, _) # xs) \<V> \<longleftrightarrow> vars_of_monom_in x \<V> \<and> vars_of_poly_in xs \<V>\<close>

lemma vars_of_monom_in_alt_def:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> set xs \<subseteq> \<V>\<close>
  by (induction xs)
   auto

lemma vars_llist_alt_def:
  \<open>vars_llist xs \<subseteq> \<V> \<longleftrightarrow> vars_of_poly_in xs \<V>\<close>
  by (induction xs)
   (auto simp: vars_llist_def vars_of_monom_in_alt_def)

lemma vars_of_monom_in_alt_def2:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> fold (\<lambda>x b. b \<and> x \<in> \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal
    by auto
  subgoal
    by (induction xs)
     auto
  done

lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued string_rel\<close>
  \<open>Sepref_Constraints.CONSTRAINT IS_LEFT_UNIQUE string_rel\<close>
  by (auto simp: CONSTRAINT_def single_valued_def
    string_rel_def IS_LEFT_UNIQUE_def literal.explode_inject)

sepref_definition vars_of_monom_in_impl
  is \<open>uncurry (RETURN oo vars_of_monom_in)\<close>
  :: \<open>(list_assn string_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding vars_of_monom_in_alt_def2
  by sepref

declare vars_of_monom_in_impl.refine[sepref_fr_rules]

lemma vars_of_poly_in_alt_def2:
  \<open>vars_of_poly_in xs \<V> \<longleftrightarrow> fold (\<lambda>(x, _) b. b \<and> vars_of_monom_in x \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal
    by auto
  subgoal
    by (induction xs)
     auto
  done


sepref_definition vars_of_poly_in_impl
  is \<open>uncurry (RETURN oo vars_of_poly_in)\<close>
  :: \<open>(poly_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding vars_of_poly_in_alt_def2
  by sepref

declare vars_of_poly_in_impl.refine[sepref_fr_rules]


term vars_llist

definition union_vars_monom :: \<open>string list \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_monom xs \<V> = fold insert xs \<V>\<close>

definition union_vars_poly :: \<open>llist_polynom \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_poly xs \<V> = fold (\<lambda>(xs, _) \<V>. union_vars_monom xs \<V>) xs \<V>\<close>

lemma union_vars_monom_alt_def:
  \<open>union_vars_monom xs \<V> = \<V> \<union> set xs\<close>
  unfolding union_vars_monom_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y)
      auto
  subgoal
    by (induction xs)
     auto
  done

lemma union_vars_poly_alt_def:
  \<open>union_vars_poly xs \<V> = \<V> \<union> vars_llist xs\<close>
  unfolding union_vars_poly_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y)
      (auto simp: union_vars_monom_alt_def)
  subgoal
    by (induction xs)
     (auto simp: vars_llist_def union_vars_monom_alt_def)
   done

sepref_definition union_vars_monom_impl
  is \<open>uncurry (RETURN oo union_vars_monom)\<close>
  :: \<open>(list_assn string_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_monom_def
  by sepref

declare union_vars_monom_impl.refine[sepref_fr_rules]

sepref_definition union_vars_poly_impl
  is \<open>uncurry (RETURN oo union_vars_poly)\<close>
  :: \<open>(poly_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_def
  by sepref

declare union_vars_poly_impl.refine[sepref_fr_rules]




hide_const (open) Autoref_Fix_Rel.CONSTRAINT

fun status_assn where
  \<open>status_assn _ CSUCCESS CSUCCESS = emp\<close> |
  \<open>status_assn _ CFOUND CFOUND = emp\<close> |
  \<open>status_assn R (CFAILED a) (CFAILED b) = R a b\<close> |
  \<open>status_assn _ _ _ = false\<close>

lemma SUCCESS_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return CSUCCESS), uncurry0 (RETURN CSUCCESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  by (sepref_to_hoare)
    sep_auto

lemma FOUND_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return CFOUND), uncurry0 (RETURN CFOUND)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  by (sepref_to_hoare)
    sep_auto

lemma is_success_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  ((return o is_cfound), (RETURN o is_cfound)) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare)
  apply (case_tac xi; case_tac x)
  apply  sep_auto+
  done

lemma is_cfailed_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  ((return o is_cfailed), (RETURN o is_cfailed)) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare)
  apply (case_tac xi; case_tac x)
  apply  sep_auto+
  done

lemma merge_cstatus_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  (uncurry (return oo merge_cstatus), uncurry (RETURN oo merge_cstatus)) \<in>
    (status_assn R)\<^sup>k *\<^sub>a  (status_assn R)\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  apply (sepref_to_hoare)
  by (case_tac b; case_tac bi; case_tac a; case_tac ai; sep_auto simp: is_pure_conv pure_app_eq)

sepref_definition add_poly_impl
  is \<open>add_poly_l\<close>
  :: \<open>(poly_assn \<times>\<^sub>a poly_assn)\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


declare add_poly_impl.refine[sepref_fr_rules]


sepref_register mult_monomials
lemma mult_monoms_alt_def:
  \<open>(RETURN oo mult_monoms) x y = REC\<^sub>T
    (\<lambda>f (p, q).
      case (p, q) of
        ([], _) \<Rightarrow> RETURN q
       | (_, []) \<Rightarrow> RETURN p
       | (x # p, y # q) \<Rightarrow>
        (if x = y then do {
          pq \<leftarrow> f (p, q);
           RETURN (x # pq)}
        else if (x, y) \<in> var_order_rel
        then do {
          pq \<leftarrow> f (p, y # q);
          RETURN (x # pq)}
        else do {
          pq \<leftarrow>  f (x # p, q);
          RETURN (y # pq)}))
     (x, y)\<close>
  apply (induction x y rule: mult_monoms.induct)
  subgoal for p
    apply (subst RECT_unfold)
    apply refine_mono
    apply (cases p)
    apply auto
    done
  subgoal for p
    apply (subst RECT_unfold)
    apply refine_mono
    apply (cases p)
    apply auto
    done
  subgoal for x p y q
    apply (subst RECT_unfold)
    apply refine_mono
    apply (auto simp: let_to_bind_conv)
    apply (metis let_to_bind_conv)+
    done
  done


sepref_definition mult_monoms_impl
  is \<open>uncurry (RETURN oo mult_monoms)\<close>
  :: \<open>(monom_assn)\<^sup>k *\<^sub>a (monom_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    var_order'_def[symmetric]
    term_order_rel'_alt_def
    mult_monoms_alt_def
    var_order_rel_var_order
  by sepref

declare mult_monoms_impl.refine[sepref_fr_rules]

sepref_definition mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>(monomial_assn)\<^sup>k *\<^sub>a (monomial_assn)\<^sup>k \<rightarrow>\<^sub>a (monomial_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_monomials_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


lemma map_append_alt_def2:
  \<open>(RETURN o (map_append f b)) xs = REC\<^sub>T
    (\<lambda>g xs. case xs of [] \<Rightarrow> RETURN b
      | x # xs \<Rightarrow> do {
           y \<leftarrow> g xs;
           RETURN (f x # y)
     }) xs\<close>
   apply (subst eq_commute)
  apply (induction f b xs rule: map_append.induct)
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  done


definition map_append_poly_mult where
  \<open>map_append_poly_mult x = map_append (mult_monomials x)\<close>

declare mult_monomials_impl.refine[sepref_fr_rules]

sepref_definition map_append_poly_mult_impl
  is \<open>uncurry2 (RETURN ooo map_append_poly_mult)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding map_append_poly_mult_def
    map_append_alt_def2
  by sepref

declare map_append_poly_mult_impl.refine[sepref_fr_rules]

text \<open>TODO @{thm map_by_foldl} is the worst possible implementation of map!\<close>
sepref_definition mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  supply [[eta_contract = false, show_abbrevs=false]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    foldl_conv_fold
    fold_eq_nfoldli
    map_append_poly_mult_def[symmetric]
    map_append_alt_def[symmetric]
  by sepref

declare mult_poly_raw_impl.refine[sepref_fr_rules]


sepref_definition mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

declare mult_poly_impl.refine[sepref_fr_rules]

lemma single_valued_monom_rel: \<open>single_valued monom_rel\<close>
  by (rule list_rel_sv)
    (auto intro!: frefI simp: string_rel_def
    rel2p_def single_valued_def p2rel_def)

lemma single_valued_monomial_rel:
  \<open>single_valued monomial_rel\<close>
  using single_valued_monom_rel
  by (auto intro!: frefI simp:
    rel2p_def single_valued_def p2rel_def)

lemma single_valued_monom_rel': \<open>IS_LEFT_UNIQUE monom_rel\<close>
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (rule list_rel_sv)
   (auto intro!: frefI simp: string_rel_def
    rel2p_def single_valued_def p2rel_def literal.explode_inject)


lemma single_valued_monomial_rel':
  \<open>IS_LEFT_UNIQUE monomial_rel\<close>
  using single_valued_monom_rel'
  unfolding IS_LEFT_UNIQUE_def inv_list_rel_eq
  by (auto intro!: frefI simp:
    rel2p_def single_valued_def p2rel_def)

lemma inverse_monomial:
  \<open>monom_rel\<inverse> \<times>\<^sub>r int_rel = (monom_rel \<times>\<^sub>r int_rel)\<inverse>\<close>
  by (auto)

lemma eq_poly_rel_eq[sepref_import_param]:
  \<open>((=), (=)) \<in> poly_rel \<rightarrow> poly_rel \<rightarrow> bool_rel\<close>
  using list_rel_sv[of \<open>monomial_rel\<close>, OF single_valued_monomial_rel]
  using list_rel_sv[OF single_valued_monomial_rel'[unfolded IS_LEFT_UNIQUE_def inv_list_rel_eq]]
  unfolding inv_list_rel_eq[symmetric]
  by (auto intro!: frefI simp:
      rel2p_def single_valued_def p2rel_def
    simp del: inv_list_rel_eq)

sepref_definition weak_equality_p_impl
  is \<open>uncurry weak_equality_p\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding weak_equality_p_def
  by sepref

declare weak_equality_p_impl.refine[sepref_fr_rules]
sepref_register add_poly_l mult_poly_full

abbreviation raw_string_assn :: \<open>string \<Rightarrow> string \<Rightarrow> assn\<close> where
  \<open>raw_string_assn \<equiv> list_assn id_assn\<close>

definition show_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>show_nat i = show i\<close>

lemma [sepref_import_param]:
  \<open>(show_nat, show_nat) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel\<close>
  by (auto intro: fun_relI)

lemma status_assn_pure_conv:
  \<open>status_assn (id_assn) a b = id_assn a b\<close>
  by (cases a; cases b)
    (auto simp: pure_def)


lemma [sepref_fr_rules]:
  \<open>(uncurry3 (\<lambda>x y. return oo (error_msg_not_equal_dom x y)), uncurry3 check_not_equal_dom_err) \<in>
  poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding show_nat_def[symmetric] list_assn_pure_conv
    prod_assn_pure_conv check_not_equal_dom_err_def
  by (sepref_to_hoare; sep_auto simp: error_msg_not_equal_dom_def list_assn_aux_append)



lemma [sepref_fr_rules]:
  \<open>(return o error_msg_notin_dom, RETURN o error_msg_notin_dom) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(return o error_msg_reused_dom, RETURN o error_msg_reused_dom) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(uncurry (return oo error_msg), uncurry (RETURN oo error_msg)) \<in> nat_assn\<^sup>k *\<^sub>a raw_string_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding error_msg_notin_dom_def list_assn_pure_conv list_rel_id_simp
  unfolding status_assn_pure_conv
  unfolding show_nat_def[symmetric]
  by (sepref_to_hoare; sep_auto; fail)+

sepref_definition check_addition_l_impl
  is \<open>uncurry6 check_addition_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_addition_l_impl.refine[sepref_fr_rules]

sepref_register check_mult_l_dom_err

definition check_mult_l_dom_err_impl where
  \<open>check_mult_l_dom_err_impl pd p ia i =
    (if pd then ''The polynom with id '' @ show p @ '' was not found'' else '''') @
    (if ia then ''The id of the resulting id '' @ show i @ '' was was already given'' else '''')\<close>

definition check_mult_l_mult_err_impl where
  \<open>check_mult_l_mult_err_impl p q pq r =
    ''Multiplying '' @ show p @ '' by '' @ show q @ '' gives '' @ show pq @ '' and not '' @ show r\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_dom_err_impl x y))),
   uncurry3 (check_mult_l_dom_err)) \<in> bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_dom_err_def check_mult_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_mult_err_impl x y))),
   uncurry3 (check_mult_l_mult_err)) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_mult_err_def check_mult_l_mult_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_mult_l_impl
  is \<open>uncurry6 check_mult_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_mult_l_impl.refine[sepref_fr_rules]

definition check_ext_l_dom_err_impl :: \<open>nat \<Rightarrow> _\<close>  where
  \<open>check_ext_l_dom_err_impl p =
    ''There is already a polynom with index '' @ show p\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_ext_l_dom_err_impl))),
    (check_extension_l_dom_err)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_dom_err_def check_ext_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


definition check_extension_l_no_new_var_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_no_new_var_err_impl p =
    ''No new variable could be found in polynom '' @ show p\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_extension_l_no_new_var_err_impl))),
    (check_extension_l_no_new_var_err)) \<in> poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_no_new_var_err_impl_def check_extension_l_no_new_var_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_side_cond_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_impl v p r s =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' polynom is '' @ show p @ ''side condition p*p - p = '' @ show s @ '' and should be 0''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry3 (\<lambda>x y. return oo (check_extension_l_side_cond_err_impl x y))),
    uncurry3 (check_extension_l_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_side_cond_err_impl_def check_extension_l_side_cond_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_new_var_multiple_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_impl v p =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' but appears several times in the polynom '' @ show p\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry (return oo (check_extension_l_new_var_multiple_err_impl))),
    uncurry (check_extension_l_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_new_var_multiple_err_impl_def
     check_extension_l_new_var_multiple_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


sepref_register check_extension_l_dom_err fmlookup'
  check_extension_l_side_cond_err check_extension_l_no_new_var_err
  find_undefined_var_l_only find_undefined_var_l_fun
  check_extension_l_new_var_multiple_err

sepref_definition find_undefined_var_l_only_impl
  is \<open>uncurry (RETURN oo find_undefined_var_l_only)\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a option_assn (string_assn \<times>\<^sub>a int_assn)\<close>
  unfolding find_undefined_var_l_only_alt_def[abs_def]
  by sepref

declare find_undefined_var_l_only_impl.refine[sepref_fr_rules]

lemma [sepref_import_param]:
  assumes \<open>CONSTRAINT IS_LEFT_UNIQUE R\<close>  \<open>CONSTRAINT IS_RIGHT_UNIQUE R\<close>
  shows \<open>(remove1, remove1) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel\<close>
  apply (intro fun_relI)
  subgoal premises p for x y xs ys
    using p(2) p(1) assms
    by (induction xs ys rule: list_rel_induct)
      (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  done

sepref_definition find_undefined_var_l_fun_impl
  is \<open>uncurry find_undefined_var_l_fun\<close>
  :: \<open>vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a option_assn (string_assn \<times>\<^sub>a int_assn \<times>\<^sub>a poly_assn)\<close>
  supply option.splits[split]
  unfolding find_undefined_var_l_fun_def
    option.case_eq_if HOL_list.fold_custom_empty
  by sepref

lemma find_undefined_var_l_fun_find_undefined_var_l:
  \<open>(uncurry find_undefined_var_l_fun, uncurry find_undefined_var_l) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  using find_undefined_var_l_alt_def
  by (auto intro!: ext frefI nres_relI)

lemmas [sepref_fr_rules] =
  find_undefined_var_l_fun_impl.refine[FCOMP find_undefined_var_l_fun_find_undefined_var_l]

definition uminus_poly :: \<open>llist_polynom \<Rightarrow> llist_polynom\<close> where
  \<open>uminus_poly p' = map (\<lambda>(a, b). (a, - b)) p'\<close>

sepref_register uminus_poly
lemma [sepref_import_param]:
  \<open>(map (\<lambda>(a, b). (a, - b)), uminus_poly) \<in> poly_rel \<rightarrow> poly_rel\<close>
  unfolding uminus_poly_def
  apply (intro fun_relI)
  subgoal for p p'
    by (induction p p' rule: list_rel_induct)
     auto
  done

lemma check_extension_l_alt_def:
\<open>check_extension_l spec A \<V> i p = do {
  b \<leftarrow> RETURN (i \<notin># dom_m A);
  if \<not>b
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, None)
  } else do {
    v \<leftarrow> find_undefined_var_l \<V> p;
    case v of
      None \<Rightarrow> do {
        c \<leftarrow> check_extension_l_no_new_var_err p;
        RETURN (error_msg i c, None)
      }
    | Some (v, c, p') \<Rightarrow> do {
        let b = vars_llist p' \<subseteq> \<V>;
        if \<not>b
        then do {
          c \<leftarrow> check_extension_l_new_var_multiple_err v p';
          RETURN (error_msg i c, None)
        }
        else do {
           p2 \<leftarrow> mult_poly_full p' p';
           let up = (if c = -1 then map (\<lambda>(a, b). (a, -b)) p' else p');
           q \<leftarrow> add_poly_l (p2, up);
           eq \<leftarrow> weak_equality_p q [];
           if eq then do {
             RETURN (CSUCCESS, Some v)
           } else do {
            c \<leftarrow> check_extension_l_side_cond_err v p p' q;
            RETURN (error_msg i c, None)
          }
        }
      }
    }
  }\<close>
  by (auto simp: check_extension_l_def)

sepref_register find_undefined_var_l vars_of_poly_in
  weak_equality_p

sepref_definition check_extension_l_impl
  is \<open>uncurry4 check_extension_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a option_assn string_assn\<close>
  supply option.splits[split]
  supply [[goals_limit=1]]
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
    check_extension_l_alt_def
    not_not
    option.case_eq_if
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_extension_l_impl.refine[sepref_fr_rules]

definition check_del_l_dom_err_impl where
  \<open>check_del_l_dom_err_impl p =
    (''The polynom with id '' @ show p @ '' was not found'')\<close>


lemma [sepref_fr_rules]:
  \<open>(return o (check_del_l_dom_err_impl),
   (check_del_l_dom_err)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_del_l_dom_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


sepref_definition check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_del_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = check_del_l_impl.refine

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>monomial_rel\<rangle>list_rel\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynoms_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l check_del_l check_extension_l

lemma pac_step_rel_assn_alt_def:
  \<open>hn_ctxt (pac_step_rel_assn nat_assn poly_assn) b bi =
       hn_val
        (p2rel
          (\<langle>nat_rel, poly_rel\<rangle>pac_step_rel_raw)) b bi\<close>
  unfolding poly_assn_list hn_ctxt_def
  by (induction nat_assn poly_assn b bi rule: pac_step_rel_assn.induct)
   (auto simp: p2rel_def hn_val_unfold pac_step_rel_raw.simps relAPP_def
    pure_app_eq)


term Del
lemma is_AddD_import[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close>
  shows
    \<open>(return o pac_res, RETURN o pac_res) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a
       (pac_step_rel_assn K V)\<^sup>k \<rightarrow> V\<close>
    \<open>(return o pac_src1, RETURN o pac_src1) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Del x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o new_id, RETURN o new_id) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o is_Add, RETURN o is_Add) \<in>  (pac_step_rel_assn K V)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Mult, RETURN o is_Mult) \<in> (pac_step_rel_assn K V)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Del, RETURN o is_Del) \<in> (pac_step_rel_assn K V)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Extension, RETURN o is_Extension) \<in> (pac_step_rel_assn K V)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi; auto simp: is_pure_conv ent_true_drop pure_app_eq)+
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi;
      auto simp: is_pure_conv ent_true_drop pure_app_eq; fail)+
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi; auto simp: is_pure_conv ent_true_drop pure_app_eq)+
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    done
  subgoal
    using assms
    apply sepref_to_hoare
    apply sep_auto
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    apply (case_tac x; case_tac xi)
    apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
    done
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow>
  (return o pac_src2, RETURN o pac_src2) \<in> [\<lambda>x. is_Add x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> K\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure V \<Longrightarrow>
  (return o pac_mult, RETURN o pac_mult) \<in> [\<lambda>x. is_Mult x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> V\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma is_Mult_lastI:
  \<open>\<not> is_Add b \<Longrightarrow> \<not>is_Mult b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k) apac_step is "('k) pac_step"

sepref_register merge_cstatus full_normalize_poly
find_theorems poly_assn list_rel

lemma poly_rel_the_pure:
  \<open>poly_rel = the_pure poly_assn\<close> and
  nat_rel_the_pure:
  \<open>nat_rel = the_pure nat_assn\<close> and
 WTF_RF: \<open>pure (the_pure nat_assn) = nat_assn\<close>
  unfolding poly_assn_list
  by auto

sepref_definition check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (nat_assn) poly_assn)\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
  by sepref


declare check_step_impl.refine[sepref_fr_rules]

instantiation pac_step :: (heap) heap
begin

instance
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where
    f: \<open>inj f\<close>
    by blast
  obtain g :: \<open>nat \<times> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat\<close> where
    g: \<open>inj g\<close>
    by blast
  have [iff]: \<open>g a = g b \<longleftrightarrow> a = b\<close>  \<open>f a' = f b' \<longleftrightarrow> a' = b'\<close> for a b a' b'
    using f g unfolding inj_def by blast+
  let ?f = \<open>\<lambda>x :: 'a pac_step.
     g (case x of
        Add a b c d \<Rightarrow> (0, a, b, c, f d)
      | Del a  \<Rightarrow> (1, a, 0, 0, 0)
      | Mult a b c d \<Rightarrow> (2, a, f b, c, f d)
      | Extension a b \<Rightarrow> (3, a, f b, 0, 0))\<close>
   have \<open>inj ?f\<close>
     apply (auto simp: inj_def)
     apply (case_tac x; case_tac y)
     apply auto
     done
   then show \<open>\<exists>f :: 'a pac_step \<Rightarrow> nat. inj f\<close>
     by blast
qed

end

lemma safe_pac_step_rel_assn[safe_constraint_rules]:
  "is_pure K \<Longrightarrow> is_pure V \<Longrightarrow> is_pure (pac_step_rel_assn K V)"
  by (auto simp: step_rewrite_pure(1)[symmetric] is_pure_conv)

sepref_register PAC_checker_l_step PAC_checker_l_step' fully_normalize_poly_impl

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

sepref_definition PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (list_assn (pac_step_rel_assn (nat_assn) poly_assn))\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
    apply (subst nres_bind_let_law)
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

declare PAC_checker_l_impl.refine[sepref_fr_rules]

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>


sepref_register upper_bound_on_dom op_fmap_empty
sepref_definition remap_polys_l_impl
  is \<open>uncurry2 remap_polys_l2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding remap_polys_l2_def op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    union_vars_poly_alt_def[symmetric]
  apply (subst while_upt_while_direct)
  apply simp
  apply (rewrite at \<open>op_fmap_empty\<close> annotate_assn[where A=\<open>polys_assn\<close>])
  by sepref

thm remap_polys_l2_remap_polys_l

lemma remap_polys_l2_remap_polys_l:
  \<open>(uncurry2 remap_polys_l2, uncurry2 remap_polys_l) \<in> (Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI fun_relI nres_relI)
  using remap_polys_l2_remap_polys_l by auto

lemma [sepref_fr_rules]:
   \<open>(uncurry2 remap_polys_l_impl,
     uncurry2 remap_polys_l) \<in> poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
       status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
   using hfcomp_tcomp_pre[OF remap_polys_l2_remap_polys_l remap_polys_l_impl.refine]
   by (auto simp: hrp_comp_def hfprod_def)

sepref_register remap_polys_l

sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (nat_assn) poly_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  by sepref

sepref_definition PAC_update_impl
  is \<open>uncurry2 (RETURN ooo fmupd)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a (polys_assn_input)\<^sup>d \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding comp_def
  by sepref

sepref_definition PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

sepref_definition empty_vars_impl
  is \<open>uncurry0 (RETURN {})\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding hs.fold_custom_empty
  by sepref

export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del Add Mult nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension
  in SML_imp module_name PAC_Checker
  file "code/checker.sml"


section \<open>Correctness theorem\<close>

context poly_embed
begin

definition full_poly_assn where
  \<open>full_poly_assn = hr_comp poly_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>

definition full_poly_input_assn where
  \<open>full_poly_input_assn = hr_comp
        (hr_comp polys_assn_input
          (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
        polys_rel\<close>

definition fully_pac_assn where
  \<open>fully_pac_assn = (list_assn
        (hr_comp (pac_step_rel_assn nat_assn poly_assn)
          (p2rel
            (\<langle>nat_rel,
             fully_unsorted_poly_rel O
             mset_poly_rel\<rangle>pac_step_rel_raw))))\<close>

definition code_status_assn where
  \<open>code_status_assn = hr_comp (status_assn raw_string_assn)
                            code_status_status_rel\<close>

definition full_vars_assn where
  \<open>full_vars_assn = hr_comp (hs.assn string_assn)
                              (\<langle>var_rel\<rangle>set_rel)\<close>

lemma polys_rel_full_polys_rel:
  \<open>polys_rel_full = Id \<times>\<^sub>r polys_rel\<close>
  by (auto simp: polys_rel_full_def)

definition full_polys_assn :: \<open>_\<close> where
\<open>full_polys_assn = hr_comp (hr_comp polys_assn
                              (\<langle>nat_rel,
                               sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            polys_rel\<close>

text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).

\<close>

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (full_poly_assn)\<^sup>k *\<^sub>a
      (full_poly_input_assn)\<^sup>d *\<^sub>a
      (fully_pac_assn)\<^sup>k \<rightarrow>\<^sub>a code_status_assn \<times>\<^sub>a
                           full_vars_assn \<times>\<^sub>a full_polys_assn\<close>
  using 
    full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
    FCOMP full_checker_spec',
    unfolded full_poly_assn_def[symmetric]
      full_poly_input_assn_def[symmetric]
      fully_pac_assn_def[symmetric]
      code_status_assn_def[symmetric]
      full_vars_assn_def[symmetric]
      polys_rel_full_polys_rel
      hr_comp_prod_conv
      full_polys_assn_def[symmetric]]
   by auto

end

definition \<phi> :: \<open>string \<Rightarrow> nat\<close> where
  \<open>\<phi> = (SOME \<phi>. bij \<phi>)\<close>

lemma bij_\<phi>: \<open>bij \<phi>\<close>
  using someI[of \<open> \<lambda>\<phi> :: string \<Rightarrow> nat. bij \<phi>\<close>]
  unfolding \<phi>_def[symmetric]
  using poly_embed_EX
  by auto

global_interpretation PAC: poly_embed where
  \<phi> = \<phi>
  apply standard
  apply (use bij_\<phi> in \<open>auto simp: bij_def\<close>)
  done

text \<open>The full correctness theorem is @{thm PAC.PAC_full_correctness}.\<close>

end
