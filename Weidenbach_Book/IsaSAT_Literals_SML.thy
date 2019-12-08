theory IsaSAT_Literals_SML
  imports Watched_Literals.WB_Word_Assn
    Watched_Literals.Array_UInt IsaSAT_Literals
begin
hide_const (open) IsaSAT_Literals.uint32_max IsaSAT_Literals.uint64_max
hide_fact (open) IsaSAT_Literals.uint32_max_def IsaSAT_Literals.uint64_max_def

lemma [simp]: \<open>IsaSAT_Literals.uint32_max = uint32_max\<close>
    \<open>IsaSAT_Literals.uint64_max = uint64_max\<close>
  by (auto simp: IsaSAT_Literals.uint32_max_def uint32_max_def
    IsaSAT_Literals.uint64_max_def uint64_max_def)

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

definition uminus_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>uminus_code L = bitXOR L 1\<close>

definition unat_lit_rel :: \<open>(uint32 \<times> nat literal) set\<close> where
  \<open>unat_lit_rel \<equiv> uint32_nat_rel O nat_lit_rel\<close>

lemma nat_of_uint32_shiftr: \<open>nat_of_uint32 (shiftr xi n) = shiftr (nat_of_uint32 xi) n\<close>
  by transfer (auto simp: shiftr_div_2n unat_def shiftr_nat_def)

definition atm_of_code :: \<open>uint32 \<Rightarrow> uint32\<close> where
  \<open>atm_of_code L = shiftr L 1\<close>


lemma append_ll_append_update:
  \<open>(uncurry2 (RETURN ooo (\<lambda>xs i j. append_ll xs (nat_of_uint32 i) j)), uncurry2 (RETURN ooo append_update))
  \<in>  [\<lambda>((W, L), i). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
     \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>f unat_lit_rel \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def nat_lit_rel_def
      nth_list_update' append_update_def nat_lit_rel_def unat_lit_rel_def br_def
      uint32_nat_rel_def append_update_def
      simp del: literal_of_nat.simps)
type_synonym ann_lit_wl = \<open>uint32 \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>
type_synonym ann_lit_wl_fast = \<open>uint32 \<times> uint64 option\<close>
type_synonym ann_lits_wl_fast = \<open>ann_lit_wl_fast list\<close>

definition nat_ann_lit_rel :: \<open>(ann_lit_wl \<times> (nat, nat) ann_lit) set\<close> where
  nat_ann_lit_rel_internal_def: \<open>nat_ann_lit_rel = \<langle>uint32_nat_rel, \<langle>nat_rel\<rangle>option_rel\<rangle>ann_lit_rel\<close>

lemma ann_lit_rel_def:
  \<open>\<langle>R, R'\<rangle>ann_lit_rel = {(a, b). \<exists>c d. (fst a, c) \<in> R \<and> (snd a, d) \<in> R' \<and>
      b = ann_lit_of_pair (literal_of_nat c, d)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_internal_def relAPP_def ..

lemma nat_ann_lit_rel_def:
  \<open>nat_ann_lit_rel = {(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat (nat_of_uint32 a), b)) a)}\<close>
  unfolding nat_ann_lit_rel_internal_def ann_lit_rel_def
  apply (auto simp: option_rel_def ex_disj_distrib uint32_nat_rel_def br_def)
   apply (case_tac b)
    apply auto
   apply (case_tac b)
   apply auto
  done

definition nat_ann_lits_rel :: \<open>(ann_lits_wl \<times> (nat, nat) ann_lits) set\<close> where
  \<open>nat_ann_lits_rel = \<langle>nat_ann_lit_rel\<rangle>list_rel\<close>

lemma nat_ann_lits_rel_Cons[iff]:
  \<open>(x # xs, y # ys) \<in> nat_ann_lits_rel \<longleftrightarrow> (x, y) \<in> nat_ann_lit_rel \<and> (xs, ys) \<in> nat_ann_lits_rel\<close>
  by (auto simp: nat_ann_lits_rel_def)

lemma is_decided_wl_is_decided:
  \<open>(RETURN o is_decided_wl, RETURN o is_decided) \<in> nat_ann_lit_rel \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
  by (auto simp: nat_ann_lit_rel_def is_decided_wl_def is_decided_def intro!: frefI nres_relI
      elim: ann_lit_of_pair.elims)


definition (in -) is_pos_code :: \<open>uint32 \<Rightarrow> bool\<close> where
  \<open>is_pos_code L \<longleftrightarrow> bitAND L 1 = 0\<close>

definition lit_and_ann_of_propagated_code where
  \<open>lit_and_ann_of_propagated_code = (\<lambda>L::ann_lit_wl. (fst L, the (snd L)))\<close>


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

sepref_decl_op watched_app:
  \<open>watched_app ::(nat literal \<Rightarrow> (nat \<times> _) list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close>
::
  \<open>(Id :: ((nat literal \<Rightarrow> (nat watcher) list) \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> nat_rel \<rightarrow>
     nat_rel \<times>\<^sub>r (Id :: (nat literal \<times> _) set) \<times>\<^sub>r bool_rel\<close>
  .

lemma (in -) safe_minus_nat_assn:
  \<open>(uncurry (return oo (-)), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

definition map_fun_rel_assn
   :: \<open>(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn\<close>
where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto
abbreviation nat_lit_assn :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> assn\<close> where
  \<open>nat_lit_assn \<equiv> pure nat_lit_rel\<close>

abbreviation unat_lit_assn :: \<open>nat literal \<Rightarrow> uint32 \<Rightarrow> assn\<close> where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

lemma hr_comp_uint32_nat_assn_nat_lit_rel[simp]:
  \<open>hr_comp uint32_nat_assn nat_lit_rel = unat_lit_assn\<close>
  by (auto simp: hrp_comp_def hr_comp_def uint32_nat_rel_def
  hr_comp_pure br_def unat_lit_rel_def)

abbreviation pair_nat_ann_lit_assn :: \<open>(nat, nat) ann_lit \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lit_assn \<equiv> pure nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lits_assn \<equiv> list_assn pair_nat_ann_lit_assn\<close>

abbreviation pair_nat_ann_lit_fast_assn :: \<open>(nat, nat) ann_lit \<Rightarrow> ann_lit_wl_fast \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lit_fast_assn \<equiv> hr_comp (uint32_assn *a option_assn uint64_nat_assn) nat_ann_lit_rel\<close>

abbreviation pair_nat_ann_lits_fast_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> ann_lits_wl_fast \<Rightarrow> assn\<close> where
  \<open>pair_nat_ann_lits_fast_assn \<equiv> list_assn pair_nat_ann_lit_fast_assn\<close>


subsubsection \<open>Code\<close>

lemma [sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def)

lemma \<open>(return o (\<lambda>n. shiftr n 1), RETURN o shiftr1) \<in> word_nat_assn\<^sup>k \<rightarrow>\<^sub>a word_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: shiftr1_def word_nat_rel_def unat_shiftr br_def)


(*lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

lemma decided_hnr[sepref_fr_rules]:
  \<open>(return o decided, RETURN o Decided) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def decided_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

*)      
      
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
        uint32_nat_rel_def br_def nat_of_uint32_XOR bitXOR_1_if_mod_2
        split: option.splits)
    using One_nat_def bitXOR_1_if_mod_2 by presburger
  show ?thesis
    using 1[FCOMP uminus_lit_imp_uminus[unfolded convert_fref]] unfolding unat_lit_rel_def uminus_code_def .
qed

abbreviation ann_lit_wl_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_assn \<equiv> uint32_assn *a (option_assn nat_assn)\<close>

abbreviation ann_lit_wl_fast_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl_fast \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_fast_assn \<equiv> uint32_assn *a (option_assn uint64_nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

type_synonym clause_wl = \<open>uint32 array\<close>
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

type_synonym unit_lits_wl = \<open>uint32 list list\<close>
abbreviation unit_lits_assn :: \<open>nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn\<close> where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn unat_lit_assn)\<close>


lemma atm_of_hnr[sepref_fr_rules]:
  \<open>(return o atm_of_code, RETURN o op_atm_of) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def uint32_nat_rel_def br_def
      Collect_eq_comp unat_lit_rel_def nat_of_uint32_shiftr nat_lit_rel_def atm_of_code_def)

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: p2rel_def nat_ann_lit_rel_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      split: if_splits)

lemma lit_of_fast_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> pair_nat_ann_lit_fast_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: unat_lit_rel_def uint32_nat_rel_def)
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def uint32_nat_rel_def
      Collect_eq_comp br_def unat_lit_rel_def nat_lit_rel_def ann_lit_of_pair_alt_def
      hr_comp_def prod.splits case_prod_beta
      split: if_splits)
  done

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    (pure unat_lit_rel)\<^sup>k *\<^sub>a (pure unat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have [simp]: \<open>even bi \<Longrightarrow> even ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  have [dest]: \<open>odd bi \<Longrightarrow> odd ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  show ?thesis
    by sepref_to_hoare
       (sep_auto simp: p2rel_def nat_ann_lit_rel_def nat_lit_rel_def
        br_def Collect_eq_comp uint32_nat_rel_def dvd_div_eq_iff unat_lit_rel_def
      split: if_splits)+
qed

lemma (in -) is_pos_hnr[sepref_fr_rules]:
  \<open>(return o is_pos_code, RETURN o is_pos) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(RETURN o (\<lambda>L. bitAND L 1 = 0), RETURN o is_pos) \<in> nat_lit_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding bitAND_1_mod_2 is_pos_code_def
    by (intro nres_relI frefI) (auto simp: nat_lit_rel_def br_def split: if_splits, presburger)
  have 2: \<open>(return o is_pos_code, RETURN o (\<lambda>L. bitAND L 1 = 0)) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    apply sepref_to_hoare
    using nat_of_uint32_ao[of _ 1]
    by (sep_auto simp: p2rel_def unat_lit_rel_def uint32_nat_rel_def
        nat_lit_rel_def br_def is_pos_code_def
        nat_of_uint32_0_iff nat_0_AND uint32_0_AND
        split: if_splits)+
  show ?thesis
    using 2[FCOMP 1[unfolded convert_fref]] unfolding unat_lit_rel_def .
qed

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o lit_and_ann_of_propagated_code, RETURN o lit_and_ann_of_propagated) \<in>
   [\<lambda>L. \<not>is_decided L]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> (unat_lit_assn *a nat_assn)\<close>
  unfolding lit_and_ann_of_propagated_code_def
  apply sepref_to_hoare
  apply (rename_tac x x')
  apply (case_tac x)
  by (sep_auto simp: nat_ann_lit_rel_def p2rel_def nat_lit_rel_def
      Propagated_eq_ann_lit_of_pair_iff unat_lit_rel_def uint32_nat_rel_def Collect_eq_comp
      br_def Collect_eq_comp nat_lit_rel_def
      simp del: literal_of_nat.simps)+

lemma Pos_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> isasat_input_bounded \<A>]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2)

lemma Neg_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n +1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> isasat_input_bounded \<A>]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2_plus1 uint32_max_def)

lemma Pos_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. L \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2 uint32_max_def)

lemma Neg_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n + 1), RETURN o Neg) \<in> [\<lambda>L. L \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      nat_of_uint32_distrib_mult2 uint32_max_def nat_of_uint32_add)

subsection \<open>Declaration of some Operators and Implementation\<close>

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat watched\<close>

lemma [def_pat_rules]:
  \<open>watched_app $ M $ L $ i \<equiv> op_watched_app $ M $ L $ i\<close>
  by (auto simp: watched_app_def)


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

end