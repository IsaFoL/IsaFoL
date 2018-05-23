theory Watched_Literals_Watch_List_Code_Common
  imports Watched_Literals_Watch_List_Domain
    Bits_Natural WB_Word_Assn
begin
text \<open>
  First we instantiate our types with sort heap and default, to have compatibility with code
  generation. The idea is simplify to create injections into the components of our datatypes.
\<close>
instance literal :: (heap) heap
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where f: \<open>inj f\<close>
    by blast
  then have Hf: \<open>f x = f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  let ?f = \<open>\<lambda>L. (is_pos L, f (atm_of L))\<close>
  have \<open>OFCLASS(bool \<times> nat, heap_class)\<close>
   by standard
  then obtain g :: \<open>bool \<times> nat \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: 'a literal \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instance annotated_lit :: (heap, heap, heap) heap
proof standard
  let ?f = \<open>\<lambda>L:: ('a, 'b, 'c) annotated_lit.
      (if is_decided L then Some (lit_dec L) else None,
       if is_decided L then None else Some (lit_prop L), if is_decided L then None else Some (mark_of L))\<close>
  have f: \<open>inj ?f\<close>
    unfolding inj_on_def Ball_def
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then have Hf: \<open>?f x = ?f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>OFCLASS('a option \<times> 'b option \<times> 'c option, heap_class)\<close>
   by standard
  then obtain g :: \<open>'a option \<times> 'b option \<times> 'c option \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: ('a, 'b, 'c) annotated_lit \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instantiation literal :: (default) default
begin

definition default_literal where
\<open>default_literal = Pos default\<close>
instance by standard

end

instantiation fmap :: (type, type) default
begin

definition default_fmap where
\<open>default_fmap = fmempty\<close>
instance by standard

end


subsection \<open>Declaration of some Operators and Implementation\<close>

sepref_decl_op atm_of: \<open>atm_of :: nat literal \<Rightarrow> nat\<close> ::
  \<open>(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat \<times> _) set)\<close> .

lemma [def_pat_rules]:
  \<open>atm_of \<equiv> op_atm_of\<close>
  by auto

sepref_decl_op lit_of: \<open>lit_of :: (nat, nat) ann_lit \<Rightarrow> nat literal\<close> ::
  \<open>(Id :: ((nat, nat) ann_lit \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set)\<close> .

lemma [def_pat_rules]:
  \<open>lit_of \<equiv> op_lit_of\<close>
  by auto


lemma \<open>(return o (\<lambda>n. shiftr n 1), RETURN o shiftr1) \<in> word_nat_assn\<^sup>k \<rightarrow>\<^sub>a word_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def word_nat_rel_def unat_shiftr br_def)

section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

definition propagated where
  \<open>propagated L C = (L, Some C)\<close>

lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      lit_of_natP_def br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition decided where
  \<open>decided L = (L, None)\<close>

lemma decided_hnr[sepref_fr_rules]:
  \<open>(return o decided, RETURN o Decided) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def decided_def case_prod_beta p2rel_def
      lit_of_natP_def br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = bitXOR L 1\<close>

lemma uminus_lit_imp_uminus:
  \<open>(RETURN o uminus_lit_imp, RETURN o uminus) \<in>
     nat_lit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
  by (intro frefI nres_relI) (auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
      lit_of_natP_def nat_lit_rel_def split: option.splits, presburger)

definition uminus_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>uminus_code L = bitXOR L 1\<close>

lemma uminus_lit_hnr[sepref_fr_rules]:
  \<open>(return o uminus_code, RETURN o uminus) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
proof -
  have [simp]: \<open>nat_of_uint32 1 = 1\<close>
    by transfer auto
  have [simp]: \<open>0 XOR Suc 0 = Suc 0\<close>
    unfolding bitXOR_nat_def
    by auto
  have [simp]: \<open>bin_last (2 + n) = bin_last n\<close> for n
    by (auto simp: bin_last_def)
  have [simp]: \<open>bin_rest (2 + n) = 1 + (bin_rest n)\<close> for n
    by (auto simp: bin_rest_def)
  have \<open>bin_nth (2 + n XOR 1) na \<longleftrightarrow> bin_nth (2 + (n XOR 1)) na\<close> for n na
    by (induction na)  auto

  then have [simp]: \<open>((2 + n) XOR 1) = 2 + ( ( ( n XOR 1)))\<close> for n :: int
    by (auto simp: bin_eq_iff)

  have [simp]: \<open>Suc (Suc n) XOR Suc 0 = Suc (Suc (n XOR Suc 0))\<close> for n :: nat
    unfolding bitXOR_nat_def
    by (auto simp: nat_add_distrib)

  have [simp]: \<open>2 * q XOR Suc 0 = Suc (2 * q)\<close> for q :: nat
    by (induction q)  auto

  have 1: \<open>(return o (\<lambda>L. bitXOR L 1), RETURN o uminus_lit_imp) \<in>
     uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
    unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
    apply sepref_to_hoare
    apply (sep_auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
        lit_of_natP_def uint32_nat_rel_def br_def nat_of_uint32_XOR bitXOR_1_if_mod_2
        split: option.splits)
    using One_nat_def bitXOR_1_if_mod_2 by presburger
  show ?thesis
    using 1[FCOMP uminus_lit_imp_uminus] unfolding unat_lit_rel_def uminus_code_def .
qed


subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym clauses_wl = \<open>uint32 arrayO_raa\<close>

abbreviation ann_lit_wl_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_assn \<equiv> uint32_assn *a (option_assn nat_assn)\<close>

abbreviation ann_lit_wl_fast_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl_fast \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_fast_assn \<equiv> uint32_assn *a (option_assn uint32_nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

abbreviation clause_ll_assn :: \<open>nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn\<close> where
  \<open>clause_ll_assn \<equiv> array_assn unat_lit_assn\<close>

abbreviation clause_l_assn :: \<open>nat clause \<Rightarrow> uint32 list \<Rightarrow> assn\<close> where
  \<open>clause_l_assn \<equiv> list_mset_assn unat_lit_assn\<close>

abbreviation clauses_l_assn :: \<open>nat clauses \<Rightarrow> uint32 list list \<Rightarrow> assn\<close> where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation clauses_to_update_l_assn :: \<open>nat multiset \<Rightarrow> nat list \<Rightarrow> assn\<close> where
  \<open>clauses_to_update_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation clauses_to_update_ll_assn :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> assn\<close> where
  \<open>clauses_to_update_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: \<open>nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn\<close> where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn unat_lit_assn)\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  \<open>nat_trail \<times> clauses_wl \<times> uint32 array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l \<times> watched_wl\<close>

lemma clause_l_assn_alt_def:
  \<open>clause_l_assn = hr_comp (list_assn unat_lit_assn) list_mset_rel\<close>
  by (simp add: list_assn_list_mset_rel_eq_list_mset_assn)


subsubsection \<open>Refinement of the Watched Function\<close>

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>

definition watched_by_nth :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_nth = (\<lambda>(M, N, D, NE, UE, Q, W) L i. W L ! i)\<close>

definition watched_app :: \<open>(nat literal \<Rightarrow> nat list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_app M L i \<equiv> M L ! i\<close>

sepref_decl_op watched_app: \<open>watched_app ::(nat literal \<Rightarrow> nat list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> ::
  \<open>(Id :: ((nat literal \<Rightarrow> nat list) \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> nat_rel \<rightarrow>
     nat_rel\<close>
  .

lemma [def_pat_rules]:
  \<open>watched_app $ M $ L $ i \<equiv> op_watched_app $ M $ L $ i\<close>
  by (auto simp: watched_app_def)

lemma watched_by_nth_watched_app:
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd) S) K w\<close>
  by (cases S) (auto simp: watched_app_def)


subsubsection \<open>More Operations\<close>

lemma nat_of_uint32_shiftr: \<open>nat_of_uint32 (shiftr xi n) = shiftr (nat_of_uint32 xi) n\<close>
  by transfer (auto simp: shiftr_div_2n unat_def shiftr_nat_def)

definition atm_of_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>atm_of_code L = shiftr L 1\<close>

lemma atm_of_hnr[sepref_fr_rules]:
  \<open>(return o atm_of_code, RETURN o op_atm_of) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def lit_of_natP_def uint32_nat_rel_def br_def
      Collect_eq_comp unat_lit_rel_def nat_of_uint32_shiftr nat_lit_rel_def atm_of_code_def)

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      split: if_splits)

lemma lit_of_fast_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: unat_lit_rel_def uint32_nat_rel_def)
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      hr_comp_def prod.splits case_prod_beta
      split: if_splits)
  done

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo (op =))) \<in>
    (pure unat_lit_rel)\<^sup>k *\<^sub>a (pure unat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have [simp]: \<open>even bi \<Longrightarrow> even ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  have [dest]: \<open>odd bi \<Longrightarrow> odd ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  show ?thesis
    by sepref_to_hoare
       (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def nat_lit_rel_def
        br_def Collect_eq_comp uint32_nat_rel_def dvd_div_eq_iff unat_lit_rel_def
      split: if_splits)+
qed


subsection \<open>Code Generation\<close>

subsubsection \<open>More Operations\<close>

fun literals_to_update_wll :: \<open>twl_st_wll \<Rightarrow> lit_queue_l\<close> where
  \<open>literals_to_update_wll (M, N, D, NE, UE, Q, W) = Q\<close>

definition literals_to_update_wll_empty :: \<open>twl_st_wll \<Rightarrow> bool\<close> where
  \<open>literals_to_update_wll_empty = (\<lambda>(M, N, D, NE, UE, Q, W). is_Nil Q)\<close>

definition literals_to_update_wl_empty :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty = (\<lambda>(M, N, D, NE, UE, Q, W). Q = {#})\<close>

definition select_and_remove_from_literals_to_update_wl' :: \<open>twl_st_wll \<Rightarrow> twl_st_wll \<times> uint32\<close> where
  \<open>select_and_remove_from_literals_to_update_wl' =
    (\<lambda>(M, N, D, NE, UE, Q, W).  ((M, N, D, NE, UE, tl Q, W), hd Q))\<close>

lemma in_nat_list_rel_list_all2_in_set_iff:
    \<open>(a, aa) \<in> nat_lit_rel \<Longrightarrow>
       list_all2 (\<lambda>x x'. (x, x') \<in> nat_lit_rel) b ba \<Longrightarrow>
       a \<in> set b \<longleftrightarrow> aa \<in> set ba\<close>
  apply (subgoal_tac \<open>length b = length ba\<close>)
  subgoal
    apply (rotate_tac 2)
    apply (induction b ba rule: list_induct2)
     apply (solves simp)
    apply (auto simp: p2rel_def lit_of_natP_same_leftD lit_of_natP_same_rightD nat_lit_rel_def)[]
    done
  subgoal using list_all2_lengthD by auto
  done

definition is_decided_wl where
  \<open>is_decided_wl L \<longleftrightarrow> snd L = None\<close>

lemma is_decided_wl_is_decided:
  \<open>(RETURN o is_decided_wl, RETURN o is_decided) \<in> nat_ann_lit_rel \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
  by (auto simp: nat_ann_lit_rel_def is_decided_wl_def is_decided_def intro!: frefI nres_relI
      elim: ann_lit_of_pair.elims)

sepref_definition is_decided_wl_code
  is \<open>(RETURN o is_decided_wl)\<close>
  :: \<open>ann_lit_wl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_decided_wl_def[abs_def]
  by sepref

sepref_definition is_decided_wl_fast_code
  is \<open>(RETURN o is_decided_wl)\<close>
  :: \<open>ann_lit_wl_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_decided_wl_def[abs_def]
  by sepref

lemma ann_lit_of_pair_if:
  \<open>ann_lit_of_pair (L, D) = (if D = None then Decided L else Propagated L (the D))\<close>
  by (cases D) auto

lemma
  is_decided_wl_code[sepref_fr_rules]:
    \<open>(is_decided_wl_code, RETURN o is_decided) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close> (is ?slow) and
  is_decided_wl_fast_code[sepref_fr_rules]:
    \<open>(is_decided_wl_fast_code, RETURN o is_decided) \<in> pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
   (is ?fast)
proof -
  have 1: \<open>hr_comp ann_lit_wl_assn nat_ann_lit_rel = pair_nat_ann_lit_assn\<close>
    by (fastforce simp: case_prod_beta hr_comp_def[abs_def] pure_def nat_ann_lit_rel_def
        prod_assn_def ann_lit_of_pair_if ex_assn_def imp_ex Abs_assn_eqI(1) ex_simps(1)[symmetric]
        simp del: pair_of_ann_lit.simps literal_of_nat.simps ex_simps(1)
        split: if_splits)
  show ?slow
    using is_decided_wl_code.refine[FCOMP is_decided_wl_is_decided]
    unfolding 1 .
  show ?fast
    using is_decided_wl_fast_code.refine[FCOMP is_decided_wl_is_decided]
    unfolding 1 .
qed

definition get_maximum_level_remove where
  \<open>get_maximum_level_remove M D L =  get_maximum_level M (remove1_mset L D)\<close>

lemma in_list_all2_ex_in: \<open>a \<in> set xs \<Longrightarrow> list_all2 R xs ys \<Longrightarrow> \<exists>b \<in> set ys. R a b\<close>
  apply (subgoal_tac \<open>length xs = length ys\<close>)
   apply (rotate_tac 2)
   apply (induction xs ys rule: list_induct2)
    apply ((solves auto)+)[2]
  using list_all2_lengthD by blast

lemma
  nat_lit_assn_right_unique:
    \<open>CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) nat_lit_assn\<close> and
  nat_lit_assn_left_unique:
    \<open>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) nat_lit_assn\<close>
   by (auto simp: IS_PURE_def single_valued_def p2rel_def IS_LEFT_UNIQUE_def nat_lit_rel_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)

definition find_decomp_wl_imp :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 D L. do {
    let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) D);
    let k = count_decided M\<^sub>0;
    (_, M) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M')))\<^esup>
         (\<lambda>(j, M). j > lev)
         (\<lambda>(j, M). do {
            ASSERT(M \<noteq> []);
            if is_decided (hd M)
            then RETURN (j-1, tl M)
            else RETURN (j, tl M)}
         )
         (k, M\<^sub>0);
    RETURN M
  })\<close>

lemma ex_decomp_get_ann_decomposition_iff:
  \<open>(\<exists>M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)) \<longleftrightarrow>
    (\<exists>M2. M = M2 @ Decided K # M1)\<close>
  using get_all_ann_decomposition_ex by fastforce

lemma count_decided_tl_if:
  \<open>M \<noteq> [] \<Longrightarrow> count_decided (tl M) = (if is_decided (hd M) then count_decided M - 1 else count_decided M)\<close>
  by (cases M) auto

lemma count_decided_butlast:
  \<open>count_decided (butlast xs) = (if is_decided (last xs) then count_decided xs - 1 else count_decided xs)\<close>
  by (cases xs rule: rev_cases) (auto simp: count_decided_def)

definition find_decomp_wl' where
  \<open>find_decomp_wl' =
     (\<lambda>(M::(nat, nat) ann_lits) (D::nat clause) (L::nat literal).
        SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (D - {#-L#}) + 1))\<close>

definition get_conflict_wl_is_None :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None = (\<lambda>(M, N, D, NE, UE, Q, W). is_None D)\<close>

lemma get_conflict_wl_is_None: \<open>get_conflict_wl S = None \<longleftrightarrow> get_conflict_wl_is_None S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_def split: option.splits)

lemma watched_by_nth_watched_app':
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)


context isasat_input_bounded
begin

lemma (in -) safe_minus_nat_assn:
  \<open>(uncurry (return oo op -), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

lemma (in -) hd_decided_count_decided_ge_1:
  \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close>
  by (cases x) auto

definition (in -) find_decomp_wl_imp' :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l list \<Rightarrow> nat \<Rightarrow>
    nat clause \<Rightarrow> nat clauses \<Rightarrow> nat clauses \<Rightarrow> nat lit_queue_wl \<Rightarrow>
    (nat literal \<Rightarrow> watched) \<Rightarrow> _ \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp' = (\<lambda>M N U D NE UE W Q L. find_decomp_wl_imp M D L)\<close>

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_rll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_rll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def)

lemma nth_aa_watched_app[sepref_fr_rules]:
  \<open>(uncurry2 nth_aa_u, uncurry2 (RETURN ooo op_watched_app)) \<in>
   [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0 \<and> i < length (W L)]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>CONSTRAINT is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry2 nth_aa_u, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_app))
  \<in> [comp_PRE
       (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f p2rel lit_of_natP \<times>\<^sub>f nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((x, L), L'). L < length x \<and> L' < length (x ! L))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       ((arrayO_assn
                          (arl_assn nat_assn))\<^sup>k *\<^sub>a
                        uint32_nat_assn\<^sup>k *\<^sub>a
                        nat_assn\<^sup>k)
                       (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f
                        p2rel lit_of_natP \<times>\<^sub>f
                        nat_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF nth_aa_uint_hnr nth_ll_watched_app, OF P]
     .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (fastforce simp: comp_PRE_def prod_rel_def_internal relAPP_def map_fun_rel_def[abs_def]
        p2rel_def lit_of_natP_def literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def nat_lit_rel_def p2rel_def
        unat_lit_rel_def hr_comp_pure)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 op_watched_app_def .
qed

definition (in -) is_pos_code :: \<open>uint32 \<Rightarrow> bool\<close> where
  \<open>is_pos_code L \<longleftrightarrow> bitAND L 1 = 0\<close>

lemma (in -) is_pos_hnr[sepref_fr_rules]:
  \<open>(return o is_pos_code, RETURN o is_pos) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(RETURN o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> nat_lit_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding bitAND_1_mod_2 is_pos_code_def
    by (intro nres_relI frefI) (auto simp: nat_lit_rel_def lit_of_natP_def split: if_splits)
  have 2: \<open>(return o is_pos_code, RETURN o (\<lambda>L. bitAND L 1 = 0)) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    apply sepref_to_hoare
    using nat_of_uint32_ao[of _ 1]
    by (sep_auto simp: p2rel_def lit_of_natP_def unat_lit_rel_def uint32_nat_rel_def
        nat_lit_rel_def br_def nat_of_uint32_012 is_pos_code_def
        nat_of_uint32_0_iff nat_0_AND uint32_0_AND
        split: if_splits)+
  show ?thesis
    using 2[FCOMP 1] unfolding unat_lit_rel_def .
qed


subsubsection \<open>Unit Propagation: Step\<close>

definition delete_index_and_swap_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>delete_index_and_swap_update W K w = W(K := delete_index_and_swap (W K) w)\<close>

text \<open>The precondition is not necessary.\<close>
lemma delete_index_and_swap_ll_delete_index_and_swap_update:
  \<open>(uncurry2 (RETURN ooo delete_index_and_swap_ll), uncurry2 (RETURN ooo delete_index_and_swap_update))
  \<in>[\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
      \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: delete_index_and_swap_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update' nat_lit_rel_def
      simp del: literal_of_nat.simps)

lemma delete_index_and_swap_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2  delete_index_and_swap_aa_u, uncurry2 (RETURN ooo delete_index_and_swap_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0 \<and> j < length (W L)]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 delete_index_and_swap_aa_u, uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update))
  \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>j. i < length l \<and> j < length_ll l i) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update)
                      x))]\<^sub>a hrp_comp ((arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) \<rightarrow>
     hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF delete_index_and_swap_aa_ll_hnr_u
        delete_index_and_swap_ll_delete_index_and_swap_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff nat_lit_rel_def)
    using even_Suc by blast
  have ba_length_a_b: \<open>ba < length (a b)\<close>
    if bN: \<open>b \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      H: \<open>\<And>aa bb. (\<forall>x\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x) \<and>
          (bb, b) \<in> nat_lit_rel \<longrightarrow>
          bb < length aa \<and>
          ba < length (aa ! bb)\<close>
    for a :: \<open>nat literal \<Rightarrow> nat list\<close> and b :: \<open>nat literal\<close> and ba :: nat
  proof -
    obtain aa where
      aa: \<open>\<forall>x\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x\<close>
      using ex_list_watched[of a] by blast
    then have \<open>nat_of_lit b < length aa\<close> and aa_b_a_b: \<open>aa ! nat_of_lit b = a b\<close>
      using bN by blast+

    obtain bb where bb: \<open>(bb, b) \<in> nat_lit_rel\<close>
      using b[of b] by blast
    show ?thesis
      using H[of aa bb] aa bb aa_b_a_b by (auto simp: p2rel_def lit_of_natP_def nat_lit_rel_def)
  qed

  have pre: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def map_fun_rel_def lit_of_natP_def
        image_image ba_length_a_b
        Pos_div2_iff Neg_div2_iff all_conj_distrib length_ll_def
        intro!: ext split: if_splits)
    by (auto simp: p2rel_def nat_lit_rel_def lit_of_natP_def split: if_splits)

  have
    1: \<open>hrp_comp (nat_assn\<^sup>k) nat_rel = nat_assn\<^sup>k\<close> and
    2: \<open>hrp_comp (uint32_nat_assn\<^sup>k) nat_lit_rel = unat_lit_assn\<^sup>k\<close>
     by (auto simp: hrp_comp_def)
  have init: \<open>?init' = ?init\<close>
    unfolding prod_hrp_comp 1 2 hrp_comp_dest by blast

  have post: \<open>?post' = ?post\<close>
    by simp
  show ?thesis
    using H unfolding pre init .
qed

definition (in isasat_input_ops) append_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>append_update W L a = W(L:= W (L) @ [a])\<close>

lemma append_ll_append_update:
  \<open>(uncurry2 (RETURN ooo (\<lambda>xs i j. append_ll xs (nat_of_uint32 i) j)), uncurry2 (RETURN ooo append_update))
  \<in>  [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f
     \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f unat_lit_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update' append_update_def nat_lit_rel_def unat_lit_rel_def br_def
      uint32_nat_rel_def
      simp del: literal_of_nat.simps)

lemma append_el_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 append_el_aa_u', uncurry2 (RETURN ooo append_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open> (uncurry2 append_el_aa_u', uncurry2 (RETURN \<circ>\<circ>\<circ> append_update))
  \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f unat_lit_rel \<times>\<^sub>f nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>x. nat_of_uint32 i < length l) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> append_update)
                      x))]\<^sub>a hrp_comp ((arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a uint32_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f unat_lit_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
     \<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF append_aa_hnr_u
        append_ll_append_update, of nat_assn] unfolding append_el_aa_append_el_aa_u' by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff nat_lit_rel_def)
    using even_Suc by blast

  have pre: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def map_fun_rel_def lit_of_natP_def image_image
        Pos_div2_iff Neg_div2_iff all_conj_distrib length_ll_def
        intro!: ext split: if_splits)
    by (auto simp: p2rel_def lit_of_natP_def unat_lit_rel_def br_def nat_lit_rel_def uint32_nat_rel_def
        split: if_splits)

  have
    1: \<open>hrp_comp (nat_assn\<^sup>k) nat_rel = nat_assn\<^sup>k\<close> and
    2: \<open>hrp_comp (uint32_assn\<^sup>k) unat_lit_rel = unat_lit_assn\<^sup>k\<close>
     by (auto simp: hrp_comp_def)
  have init: \<open>?init' = ?init\<close>
    unfolding prod_hrp_comp 1 2 hrp_comp_dest by blast

  have post: \<open>?post' = ?post\<close>
    by simp
  show ?thesis
    using H unfolding pre init by blast
qed


definition (in isasat_input_ops) is_decided_hd_trail_wl where
  \<open>is_decided_hd_trail_wl S = is_decided (hd (get_trail_wl S))\<close>

definition (in isasat_input_ops) is_decided_hd_trail_wll :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>is_decided_hd_trail_wll = (\<lambda>(M, N, D, NE, UE, Q, W).
     RETURN (is_decided (hd M))
   )\<close>

lemma
  pair_nat_ann_lit_assn_Decided_Some:
    \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
  pair_nat_ann_lit_assn_Propagated_None:
    \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
  by (auto simp: nat_ann_lit_rel_def pure_def)

lemma Propagated_eq_ann_lit_of_pair_iff:
  \<open>Propagated x21 x22 = ann_lit_of_pair (a, b) \<longleftrightarrow> x21 = a \<and> b = Some x22\<close>
  by (cases b) auto

definition lit_and_ann_of_propagated_code where
  \<open>lit_and_ann_of_propagated_code = (\<lambda>L::ann_lit_wl. (fst L, the (snd L)))\<close>

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o lit_and_ann_of_propagated_code, RETURN o lit_and_ann_of_propagated) \<in>
   [\<lambda>L. \<not>is_decided L]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  unfolding lit_and_ann_of_propagated_code_def
  apply sepref_to_hoare
  apply (rename_tac x x')
  apply (case_tac x)
  by (sep_auto simp: nat_ann_lit_rel_def p2rel_def lit_of_natP_def
      Propagated_eq_ann_lit_of_pair_iff unat_lit_rel_def uint32_nat_rel_def Collect_eq_comp
      br_def Collect_eq_comp nat_lit_rel_def
      simp del: literal_of_nat.simps)+

lemma set_mset_all_lits_of_mm_atms_of_ms_iff:
  \<open>set_mset (all_lits_of_mm A) = set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atms_of_ms (set_mset A) = atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  apply (auto simp: atms_of_s_def in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def
      atms_of_def atm_of_eq_atm_of in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  apply (auto simp: in_all_lits_of_mm_ain_atms_of_iff in_implies_atm_of_on_atms_of_ms)
  done -- \<open>TODO tune proof\<close>


definition (in -) card_max_lvl where
  \<open>card_max_lvl M C \<equiv> size (filter_mset (\<lambda>L. get_level M L = count_decided M) C)\<close>

lemma card_max_lvl_add_mset: \<open>card_max_lvl M (add_mset L C) =
  (if get_level M L = count_decided M then 1 else 0) +
    card_max_lvl M C\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_empty[simp]: \<open>card_max_lvl M {#} = 0\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_all_poss:
   \<open>card_max_lvl M C = card_max_lvl M (poss (atm_of `# C))\<close>
  unfolding card_max_lvl_def
  apply (induction C)
  subgoal by auto
  subgoal for L C
    using get_level_uminus[of M L]
    by (cases L) (auto)
  done

lemma card_max_lvl_distinct_cong:
  assumes
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C) \<Longrightarrow> (L \<in> atms_of C')\<close> and
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C') \<Longrightarrow> (L \<in> atms_of C)\<close> and
    \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> and
    \<open>distinct_mset C'\<close> \<open>\<not>tautology C'\<close>
  shows \<open>card_max_lvl M C = card_max_lvl M C'\<close>
proof -
  have [simp]: \<open>NO_MATCH (Pos x) L \<Longrightarrow> get_level M L = get_level M (Pos (atm_of L))\<close> for x L
    by (simp add: get_level_def)
  have [simp]: \<open>atm_of L \<notin> atms_of C' \<longleftrightarrow> L \<notin># C' \<and> -L \<notin># C'\<close> for L C'
    by (cases L) (auto simp: atm_iff_pos_or_neg_lit)
  then have [iff]: \<open>atm_of L \<in> atms_of C' \<longleftrightarrow> L \<in># C' \<or> -L \<in># C'\<close> for L C'
    by blast
  have H: \<open>distinct_mset {#L \<in># poss (atm_of `# C). get_level M L = count_decided M#}\<close>
    if \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> for C
    using that by (induction C) (auto simp: tautology_add_mset atm_of_eq_atm_of)
  show ?thesis
    apply (subst card_max_lvl_all_poss)
    apply (subst (2) card_max_lvl_all_poss)
    unfolding card_max_lvl_def
    apply (rule arg_cong[of _ _ size])
    apply (rule distinct_set_mset_eq)
    subgoal by (rule H) (use assms in fast)+
    subgoal by (rule H) (use assms in fast)+
    subgoal using assms by (auto simp: atms_of_def imageI image_iff) blast+
    done
qed

end

end
