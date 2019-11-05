theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort
begin

definition string_rel :: \<open>(String.literal \<times> string) set\<close> where
  \<open>string_rel = {(x, y). y = String.explode x}\<close>

abbreviation string_assn :: \<open>string \<Rightarrow> String.literal \<Rightarrow> assn\<close> where
  \<open>string_assn \<equiv> pure string_rel\<close>

lemma eq_string_eq:
  \<open>((=), (=)) \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
 by (auto intro!: frefI simp: string_rel_def String.less_literal_def
    less_than_char_def rel2p_def literal.explode_inject)

lemmas eq_string_eq_hnr =
   eq_string_eq[sepref_import_param]


abbreviation monom_rel where
  \<open>monom_rel \<equiv> \<langle>string_rel\<rangle>list_rel\<close>

abbreviation monom_assn where
  \<open>monom_assn \<equiv> list_assn string_assn\<close>

abbreviation monomial_rel where
  \<open>monomial_rel \<equiv> monom_rel \<times>\<^sub>r int_rel\<close>

abbreviation monomial_assn where
  \<open>monomial_assn \<equiv> monom_assn \<times>\<^sub>a int_assn\<close>

abbreviation poly_rel where
  \<open>poly_rel \<equiv> \<langle>monomial_rel\<rangle>list_rel\<close>


abbreviation poly_assn where
  \<open>poly_assn \<equiv> list_assn monomial_assn\<close>

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hm_fmap_assn nat_assn poly_assn\<close>

lemma string_rel_string_assn:
  \<open>(\<up> ((c, a) \<in> string_rel)) = string_assn a c\<close>
  by (auto simp: pure_app_eq)

lemma single_valued_string_rel:
   \<open>single_valued string_rel\<close>
   by (auto simp: single_valued_def string_rel_def)

lemma IS_LEFT_UNIQUE_string_rel:
   \<open>IS_LEFT_UNIQUE string_rel\<close>
   by (auto simp: IS_LEFT_UNIQUE_def single_valued_def string_rel_def
     literal.explode_inject)

lemma IS_RIGHT_UNIQUE_string_rel:
   \<open>IS_RIGHT_UNIQUE string_rel\<close>
   by (auto simp: single_valued_def string_rel_def
     literal.explode_inject)

lemma eq_string_monom_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using safe_constraint_rules(37)[OF IS_LEFT_UNIQUE_string_rel]
  using IS_RIGHT_UNIQUE_string_rel
  apply (subst (asm)list_rel_sv_iff[symmetric])
  by sepref_to_hoare
   (sep_auto simp: list_assn_pure_conv string_rel_string_assn
       single_valued_def IS_LEFT_UNIQUE_def
     dest!: mod_starD
     simp flip: inv_list_rel_eq)


definition term_order_rel' where
  [simp]: \<open>term_order_rel' x y = ((x, y) \<in> term_order_rel)\<close>

lemma term_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$term_order_rel \<equiv> term_order_rel'$x$y\<close>
  by auto

lemma term_order_rel_alt_def:
  \<open>term_order_rel = lexord (p2rel char.lexordp)\<close>
  by (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def intro!: arg_cong[of _ _ lexord])


instantiation char :: linorder
begin
  definition less_char where [symmetric, simp]: "less_char = PAC_Polynoms_Term.less_char" 
  definition less_eq_char where [symmetric, simp]: "less_eq_char = PAC_Polynoms_Term.less_eq_char"
instance
  apply standard
  using char.linorder_axioms
  by (auto simp: class.linorder_def class.order_def class.preorder_def
       less_eq_char_def less_than_char_def class.order_axioms_def
       class.linorder_axioms_def p2rel_def less_char_def)
end


instantiation list :: (linorder) linorder
begin
  definition less_list where  "less_list = lexordp (<)" 
  definition less_eq_list where "less_eq_list = lexordp_eq"

instance
  apply standard
  apply (auto simp: less_list_def less_eq_list_def List.lexordp_def
    lexordp_conv_lexord lexordp_into_lexordp_eq lexordp_antisym
    antisym_def lexordp_eq_refl lexordp_eq_linear intro: lexordp_eq_trans
    dest: lexordp_eq_antisym)
  apply (metis lexordp_antisym lexordp_conv_lexord lexordp_eq_conv_lexord)
  using lexordp_conv_lexord lexordp_conv_lexordp_eq apply blast
  done

end


lemma term_order_rel'_alt_def_lexord:
    \<open>term_order_rel' x y = ord_class.lexordp x y\<close> and
  term_order_rel'_alt_def:
    \<open>term_order_rel' x y \<longleftrightarrow> x < y\<close>
proof -
  show
    \<open>term_order_rel' x y = ord_class.lexordp x y\<close>
    \<open>term_order_rel' x y \<longleftrightarrow> x < y\<close>
    unfolding less_than_char_of_char[symmetric, abs_def]
    by (auto simp: lexordp_conv_lexord less_eq_list_def
         less_list_def lexordp_def var_order_rel_def
         rel2p_def term_order_rel_alt_def p2rel_def)
qed

lemma list_rel_list_rel_order_iff:
  assumes \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel\<close> \<open>(a', b') \<in> \<langle>string_rel\<rangle>list_rel\<close>
  shows \<open>a < a' \<longleftrightarrow> b < b'\<close>
proof
  have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (a, cs) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> b = cs\<close> for cs
     using safe_constraint_rules(37)[OF IS_LEFT_UNIQUE_string_rel]
     using IS_RIGHT_UNIQUE_string_rel
     by (subst (asm)list_rel_sv_iff[symmetric])
       (auto simp: single_valued_def)
  assume \<open>a < a'\<close>
  then consider
    u u' where \<open>a' = a @ u # u'\<close> |
    u aa v w aaa where \<open>a = u @ aa # v\<close> \<open>a' = u @ aaa # w\<close> \<open>aa < aaa\<close>
    by (subst (asm) less_list_def)
     (auto simp: lexord_def List.lexordp_def
      list_rel_append1 list_rel_split_right_iff)
  then show \<open>b < b'\<close>
  proof cases
    case 1
    then show \<open>b < b'\<close>
      using assms
      by (subst less_list_def)
        (auto simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff dest: H)
  next
    case 2
    then obtain u' aa' v' w' aaa' where
       \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
       \<open>(aa, aa') \<in> string_rel\<close>
       \<open>(aaa, aaa') \<in> string_rel\<close>
      using assms
      apply (auto simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff dest: H)
      by (metis (no_types, hide_lams) H list_rel_append2 list_rel_simp(4))
    with \<open>aa < aaa\<close> have \<open>aa' < aaa'\<close>
      by (auto simp: string_rel_def less_literal.rep_eq less_list_def
        lexordp_conv_lexord lexordp_def char.lexordp_conv_lexord
          simp flip: lexord_code less_char_def
            PAC_Polynoms_Term.less_char_def)
    then show \<open>b < b'\<close>
      using \<open>b = u' @ aa' # v'\<close> \<open>b' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
next
  have H: \<open>(a, b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow>
       (a', b) \<in> \<langle>string_rel\<rangle>list_rel \<Longrightarrow> a = a'\<close> for a a' b
     using safe_constraint_rules(37)[OF IS_LEFT_UNIQUE_string_rel]
     by (auto simp: single_valued_def IS_LEFT_UNIQUE_def
       simp flip: inv_list_rel_eq)
  assume \<open>b < b'\<close>
  then consider
    u u' where \<open>b' = b @ u # u'\<close> |
    u aa v w aaa where \<open>b = u @ aa # v\<close> \<open>b' = u @ aaa # w\<close> \<open>aa < aaa\<close>
    by (subst (asm) less_list_def)
     (auto simp: lexord_def List.lexordp_def
      list_rel_append1 list_rel_split_right_iff)
  then show \<open>a < a'\<close>
  proof cases
    case 1
    then show \<open>a < a'\<close>
      using assms
      by (subst less_list_def)
        (auto simp: lexord_def List.lexordp_def
        list_rel_append2 list_rel_split_left_iff dest: H)
  next
    case 2
    then obtain u' aa' v' w' aaa' where
       \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
       \<open>(aa', aa) \<in> string_rel\<close>
       \<open>(aaa', aaa) \<in> string_rel\<close>
      using assms
      by (auto simp: lexord_def List.lexordp_def
        list_rel_append2 list_rel_split_left_iff dest: H)
    with \<open>aa < aaa\<close> have \<open>aa' < aaa'\<close>
      by (auto simp: string_rel_def less_literal.rep_eq less_list_def
        lexordp_conv_lexord lexordp_def char.lexordp_conv_lexord
          simp flip: lexord_code less_char_def
            PAC_Polynoms_Term.less_char_def)
    then show \<open>a < a'\<close>
      using \<open>a = u' @ aa' # v'\<close> \<open>a' = u' @ aaa' # w'\<close>
      by (subst less_list_def)
        (fastforce simp: lexord_def List.lexordp_def
        list_rel_append1 list_rel_split_right_iff)
  qed
qed


lemma string_rel_le[sepref_import_param]:
  shows \<open>((<), (<)) \<in> \<langle>string_rel\<rangle>list_rel \<rightarrow>  \<langle>string_rel\<rangle>list_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: fun_relI simp: list_rel_list_rel_order_iff)


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

definition full_quicksort_poly where
  \<open>full_quicksort_poly = full_quicksort_ref (\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel) fst\<close>

lemma down_eq_id_list_rel: \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close>
  by auto

definition quicksort_poly:: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom) nres\<close> where
  \<open>quicksort_poly x y  z = quicksort_ref (\<le>) fst (x, y, z)\<close>

term partition_between_ref

definition partition_between_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom \<times> nat) nres\<close> where
  \<open>partition_between_poly = partition_between_ref (\<le>) fst\<close>

definition partition_main_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> (llist_polynom \<times> nat) nres\<close> where
  \<open>partition_main_poly = partition_main (\<le>)  fst\<close>

lemma full_quicksort_sort_poly_spec:
  \<open>(full_quicksort_poly, sort_poly_spec) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
proof -
  have xs: \<open>(xs, xs) \<in> \<langle>Id\<rangle>list_rel\<close> and \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close> for x xs
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding full_quicksort_poly_def
    apply (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down_curry, THEN order_trans])
    subgoal
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def)
      apply (smt PAC_Checker_Synthesis.less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)
      done
    subgoal
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        PAC_Checker_Synthesis.less_char_def)
      done
    subgoal by fast
    apply (rule xs)
    apply (subst down_eq_id_list_rel)
    unfolding sorted_wrt_map sort_poly_spec_def
    apply (rule full_quicksort_correct_sorted[where R = \<open>(\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel)\<close> and h = \<open>fst\<close>,
       THEN order_trans])
    subgoal
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def)
      apply (smt PAC_Checker_Synthesis.less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)
      done
    subgoal for x y
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        PAC_Checker_Synthesis.less_char_def)
      done
   subgoal
    by (auto simp: rel2p_def p2rel_def)
   done
qed

lemma le_term_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or>  term_order_rel' x y)\<close>
  apply (intro ext)
  apply (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def)
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  done

sepref_definition partition_main_poly_impl
  is \<open>uncurry2 partition_main_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_main_poly_def partition_main_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    le_term_order_rel'
  by sepref

declare partition_main_poly_impl.refine[sepref_fr_rules]

sepref_definition partition_between_poly_impl
  is \<open>uncurry2 partition_between_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_between_poly_def partition_between_ref_def
    partition_main_poly_def[symmetric]
  unfolding choose_pivot3_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def choose_pivot_def
    le_term_order_rel'
  by sepref

declare partition_between_poly_impl.refine[sepref_fr_rules]


lemma safe_poly_vars:
  shows
  [safe_constraint_rules]:
    "is_pure (poly_assn)" and
  [safe_constraint_rules]:
    "is_pure (monom_assn)" and
  [safe_constraint_rules]:
    "is_pure (monomial_assn)" and
  [safe_constraint_rules]:
    "is_pure string_assn"
  by (auto intro!: pure_prod list_assn_pure simp: prod_assn_pure_conv)

sepref_definition quicksort_poly_impl
  is \<open>uncurry2 quicksort_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding partition_main_poly_def quicksort_ref_def quicksort_poly_def
    partition_between_poly_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = quicksort_poly_impl.refine

sepref_register quicksort_poly
sepref_definition full_quicksort_poly_impl
  is \<open>full_quicksort_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding full_quicksort_poly_def full_quicksort_ref_def
    quicksort_poly_def[symmetric]
    le_term_order_rel'[symmetric]
    term_order_rel'_def[symmetric]
    List.null_def
  by sepref


lemmas sort_poly_spec_hnr[sepref_fr_rules] =
  full_quicksort_poly_impl.refine[FCOMP full_quicksort_sort_poly_spec]

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

definition var_order' where
  [simp]: \<open>var_order' = var_order\<close>

lemma var_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$var_order_rel \<equiv> var_order'$x$y\<close>
  by (auto simp: p2rel_def rel2p_def)

lemma var_order_rel_alt_def:
  \<open>var_order_rel = p2rel char.lexordp\<close>
  apply (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def)
  using char.lexordp_conv_lexord apply auto
  done

lemma var_order_rel_var_order:
  \<open>(x, y) \<in> var_order_rel \<longleftrightarrow> var_order x y\<close>
  by (auto simp: rel2p_def)

lemma var_order_string_le[sepref_import_param]:
  \<open>((<), var_order') \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
  apply (auto intro!: frefI simp: string_rel_def String.less_literal_def
     rel2p_def linorder.lexordp_conv_lexord[OF char.linorder_axioms,
      unfolded less_eq_char_def] var_order_rel_def
      p2rel_def
      simp flip: PAC_Polynoms_Term.less_char_def)
  using char.lexordp_conv_lexord apply auto
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


declare mult_monomials_impl.refine[sepref_fr_rules]

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
    map_by_foldl[symmetric]
  apply (rewrite in "_" eta_expand[where f = \<open>(@) u\<close> for u])
  by sepref

declare mult_poly_raw_impl.refine[sepref_fr_rules]


lemma merge_coeffs_alt_def:
  \<open>(RETURN o merge_coeffs) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [_] => RETURN p
     | ((xs, n) # (ys, m) # p) \<Rightarrow>
      (if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # p) else f p
       else do {p \<leftarrow> f ((ys, m) # p); RETURN ((xs, n) # p)})))
    p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  subgoal
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

find_theorems is_pure invalid_assn
lemma hn_invalid_recover:
  \<open>is_pure R \<Longrightarrow> hn_invalid R = (\<lambda>x y. R x y * true)\<close>
  \<open>is_pure R \<Longrightarrow> invalid_assn R = (\<lambda>x y. R x y * true)\<close>
  by (auto simp: is_pure_conv invalid_pure_recover hn_ctxt_def intro!: ext)

lemma invalid_assn_distrib:
  \<open>invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn = invalid_assn (monom_assn \<times>\<^sub>a int_assn)\<close>
    apply (simp add: invalid_pure_recover hn_invalid_recover
      safe_constraint_rules)
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars(2))
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars)
    apply (auto intro!: ext)
    done

lemma WTF_RF_recover:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb
        x'a \<or>\<^sub>A
       hn_ctxt monomial_assn xb x'a \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a\<close>
   by (smt assn_aci(5) hn_ctxt_def invalid_assn_distrib invalid_pure_recover is_pure_conv merge_thms(4) merge_true_star reorder_enttI safe_poly_vars(3) star_aci(2) star_aci(3))

lemma WTF_RF:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb x'a *
       (hn_invalid poly_assn la l'a * hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid poly_assn l l' *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a *
       hn_ctxt poly_assn
        la l'a *
       hn_ctxt poly_assn l l' *
       (hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px)\<close>
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xa x' *
       (hn_ctxt poly_assn l l' * hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xa x' *
       hn_ctxt poly_assn l l' *
       hn_ctxt poly_assn ax px *
       emp\<close>
  by sepref_dbg_trans_step+

sepref_definition merge_coeffs_impl
  is \<open>RETURN o merge_coeffs\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs_alt_def
    HOL_list.fold_custom_empty
  apply (rewrite in \<open>_\<close> annotate_assn[where A=\<open>poly_assn\<close>])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply (rule WTF_RF)
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply (rule WTF_RF)
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done
(*FIXME!*)

declare merge_coeffs_impl.refine[sepref_fr_rules]
sepref_definition normalize_poly_impl
  is \<open>normalize_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding normalize_poly_def
  by sepref

declare normalize_poly_impl.refine[sepref_fr_rules]

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

sepref_definition check_addition_l_impl
  is \<open>uncurry4 check_addition_l\<close>
  :: \<open>polys_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

declare check_addition_l_impl.refine[sepref_fr_rules]

sepref_definition check_mult_l_impl
  is \<open>uncurry4 check_mult_l\<close>
  :: \<open>polys_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

declare check_mult_l_impl.refine[sepref_fr_rules]

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>monomial_rel\<rangle>list_rel\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynoms_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l

lemma [fcomp_norm_unfold]:
  \<open>pure (p2rel (\<langle>K, V\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V)\<close>
  \<open>monomial_assn = pure (monom_rel \<times>\<^sub>r int_rel)\<close> and
  poly_assn_list[fcomp_norm_unfold]:
    \<open>poly_assn = pure (\<langle>monom_rel \<times>\<^sub>r int_rel\<rangle>list_rel)\<close>
  subgoal
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    apply (auto simp: relAPP_def p2rel_def pure_def)
    done
  subgoal H
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    by (simp add: list_assn_pure_conv)
  subgoal
    unfolding H
    by (simp add: list_assn_pure_conv relAPP_def)
  done

term poly_rel

lemma is_AddD_import[sepref_import_param]:
  \<open>(is_AddD, is_AddD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(pac_res, pac_res) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> V\<close>
  \<open>(pac_src1, pac_src1) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> K\<close>
  \<open>(new_id, new_id) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> K\<close>
  \<open>(is_Add, is_Add) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_AddD, is_AddD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_Mult, is_Mult) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  \<open>(is_MultD, is_MultD) \<in> p2rel (\<langle>K, V\<rangle>pac_step_rel_raw) \<rightarrow> bool_rel\<close>
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  subgoal
    apply (intro fun_relI)
    apply (case_tac a; case_tac a')
    apply (auto intro!: simp: p2rel_def)
    apply (auto simp: relAPP_def)
    done
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow>
  (return o pac_src2, RETURN o pac_src2) \<in> [\<lambda>x. is_Add x \<or> is_AddD x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> K\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure V \<Longrightarrow>
  (return o pac_mult, RETURN o pac_mult) \<in> [\<lambda>x. is_Mult x \<or> is_MultD x]\<^sub>a (pac_step_rel_assn K V)\<^sup>k \<rightarrow> V\<close>
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  apply (case_tac x; case_tac xi)
  apply (auto simp: is_pure_conv ent_true_drop pure_app_eq)
  done

lemma is_Mult_lastI:
  \<open>\<not> is_AddD b \<Longrightarrow>
       \<not> is_Add b \<Longrightarrow>
       \<not> is_MultD b \<Longrightarrow> is_Mult b\<close>
  by (cases b) auto

sepref_definition check_step_impl
  is \<open>uncurry PAC_checker_l_step\<close>
  :: \<open>polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (nat_assn) poly_assn)\<^sup>d \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_step_def
    pac_step.case_eq_if
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply (subst poly_assn_list)
  apply (rule entt_refl)
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

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
      | AddD a b c d \<Rightarrow> (1, a, b, c, f d)
      | Mult a b c d \<Rightarrow> (2, a, f b, c, f d)
      | MultD a b c d \<Rightarrow> (3, a, f b, c, f d))\<close>>
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
  by (auto simp: fcomp_norm_unfold(30)[symmetric] is_pure_conv)

sepref_register PAC_checker_l_step
sepref_definition PAC_checker_l_impl
  is \<open>uncurry PAC_checker_l\<close>
  :: \<open>polys_assn\<^sup>d *\<^sub>a (array_assn (pac_step_rel_assn (nat_assn) poly_assn))\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def
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


end