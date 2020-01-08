theory PAC_Checker_Relation
  imports PAC_Checker WB_Sort "Native_Word.Uint64"
begin

section \<open>Various Refinement Relations\<close>

text \<open>When writing this, it was not possible to share the definition with the IsaSAT version.\<close>
definition uint64_nat_rel :: "(uint64 \<times> nat) set" where
 \<open>uint64_nat_rel = br nat_of_uint64 (\<lambda>_. True)\<close>

abbreviation uint64_nat_assn where
  \<open>uint64_nat_assn \<equiv> pure uint64_nat_rel\<close>

instantiation uint32 :: hashable
begin
definition hashcode_uint32 :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint32 n = n\<close>

definition def_hashmap_size_uint32 :: \<open>uint32 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint32 = (\<lambda>_. 16)\<close>
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint32_def)
end

instantiation uint64 :: hashable
begin
definition hashcode_uint64 :: \<open>uint64 \<Rightarrow> uint32\<close> where
  \<open>hashcode_uint64 n = (uint32_of_nat (nat_of_uint64 ((n) AND ((2 :: uint64)^32 -1))))\<close>

definition def_hashmap_size_uint64 :: \<open>uint64 itself \<Rightarrow> nat\<close> where
  \<open>def_hashmap_size_uint64 = (\<lambda>_. 16)\<close>
  \<comment> \<open>same as @{typ nat}\<close>
instance
  by standard (simp add: def_hashmap_size_uint64_def)
end

lemma word_nat_of_uint64_Rep_inject[simp]: \<open>nat_of_uint64 ai = nat_of_uint64 bi \<longleftrightarrow> ai = bi\<close>
  by transfer simp

instance uint64 :: heap
  by standard (auto simp: inj_def exI[of _ nat_of_uint64])

instance uint64 :: semiring_numeral
  by standard

lemma nat_of_uint64_012[simp]: \<open>nat_of_uint64 0 = 0\<close> \<open>nat_of_uint64 2 = 2\<close> \<open>nat_of_uint64 1 = 1\<close>
  by (transfer, auto)+

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
  \<open>polys_assn \<equiv> hm_fmap_assn uint64_nat_assn poly_assn\<close>

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

lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued string_rel\<close>
  \<open>Sepref_Constraints.CONSTRAINT IS_LEFT_UNIQUE string_rel\<close>
  by (auto simp: CONSTRAINT_def single_valued_def
    string_rel_def IS_LEFT_UNIQUE_def literal.explode_inject)

lemma eq_string_monom_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using single_valued_monom_rel' IS_RIGHT_UNIQUE_string_rel
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
     using single_valued_monom_rel' IS_RIGHT_UNIQUE_string_rel
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
     using single_valued_monom_rel'
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

(* TODO Move *)
lemma [sepref_import_param]:
  assumes \<open>CONSTRAINT IS_LEFT_UNIQUE R\<close>  \<open>CONSTRAINT IS_RIGHT_UNIQUE R\<close>
  shows \<open>(remove1, remove1) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel\<close>
  apply (intro fun_relI)
  subgoal premises p for x y xs ys
    using p(2) p(1) assms
    by (induction xs ys rule: list_rel_induct)
      (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  done

instantiation pac_step :: (heap, heap, heap) heap
begin

instance
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where
    f: \<open>inj f\<close>
    by blast
  obtain g :: \<open>nat \<times> nat \<times> nat \<times> nat \<times> nat \<Rightarrow> nat\<close> where
    g: \<open>inj g\<close>
    by blast
  obtain h :: \<open>'b \<Rightarrow> nat\<close> where
    h: \<open>inj h\<close>
    by blast
  obtain i :: \<open>'c \<Rightarrow> nat\<close> where
    i: \<open>inj i\<close>
    by blast
  have [iff]: \<open>g a = g b \<longleftrightarrow> a = b\<close>\<open>h a'' = h b'' \<longleftrightarrow> a'' = b''\<close>  \<open>f a' = f b' \<longleftrightarrow> a' = b'\<close>
    \<open>i a''' = i b''' \<longleftrightarrow> a''' = b'''\<close>  for a b a' b' a'' b'' a''' b'''
    using f g h i unfolding inj_def by blast+
  let ?f = \<open>\<lambda>x :: ('a, 'b, 'c) pac_step.
     g (case x of
        Add a b c d \<Rightarrow>     (0, i a,  i b,  i c, f d)
      | Del a  \<Rightarrow>          (1, i a,    0,   0,   0)
      | Mult a b c d \<Rightarrow>    (2, i a, f b, i c, f d)
      | Extension a b c \<Rightarrow> (3, i a, f c, 0, h b))\<close>
   have \<open>inj ?f\<close>
     apply (auto simp: inj_def)
     apply (case_tac x; case_tac y)
     apply auto
     done
   then show \<open>\<exists>f :: ('a, 'b, 'c) pac_step \<Rightarrow> nat. inj f\<close>
     by blast
qed

end

end