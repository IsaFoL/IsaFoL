theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort
begin

definition string_rel :: \<open>(String.literal \<times> string) set\<close> where
  \<open>string_rel = {(x, y). y = String.explode x}\<close>

abbreviation string_assn :: \<open>string \<Rightarrow> String.literal \<Rightarrow> assn\<close> where
  \<open>string_assn \<equiv> pure string_rel\<close>

lemma var_order_string_le:
  \<open>((<), var_order) \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: frefI simp: string_rel_def String.less_literal_def
    less_than_char_def rel2p_def linorder.lexordp_conv_lexord[OF char.linorder_axioms,
      unfolded less_eq_char_def less_char_def] var_order_rel_def
      less_char_def p2rel_def)

lemmas var_order_string_le_hnr =
   var_order_string_le[sepref_import_param]

lemma eq_string_eq:
  \<open>((=), (=)) \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
 by (auto intro!: frefI simp: string_rel_def String.less_literal_def
    less_than_char_def rel2p_def literal.explode_inject)

lemmas eq_string_eq_hnr =
   eq_string_eq[sepref_import_param]


abbreviation monom_assn where
  \<open>monom_assn \<equiv> list_assn string_assn\<close>

abbreviation poly_assn where
  \<open>poly_assn \<equiv> list_assn (prod_assn monom_assn int_assn)\<close>

abbreviation polys_assn where
  \<open>polys_assn \<equiv> hm_fmap_assn nat_assn poly_assn\<close>

find_theorems list_assn \<open>((=), (=))\<close>

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


lemma [sepref_import_param]:
  shows \<open>((<), (<)) \<in> \<langle>string_rel\<rangle>list_rel \<rightarrow>  \<langle>string_rel\<rangle>list_rel \<rightarrow> bool_rel\<close>
  by (auto intro!: fun_relI simp: list_rel_list_rel_order_iff)

sepref_definition add_poly_impl
  is \<open>add_poly_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref



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
  \<open>full_quicksort_poly xs
    \<le> sort_poly_spec xs\<close>
proof -
  have xs: \<open>(xs, xs) \<in> \<langle>Id\<rangle>list_rel\<close> and \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close> for x
    by auto
  show ?thesis
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


sepref_definition quicksort_poly_impl
  is \<open>uncurry2 quicksort_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding partition_main_poly_def quicksort_ref_def quicksort_poly_def
    partition_between_poly_def[symmetric]
  by sepref

declare quicksort_poly_impl.refine[sepref_fr_rules]

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



end