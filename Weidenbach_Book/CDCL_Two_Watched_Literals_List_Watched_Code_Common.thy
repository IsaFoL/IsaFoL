theory CDCL_Two_Watched_Literals_List_Watched_Code_Common
  imports CDCL_Two_Watched_Literals_Code_Common CDCL_Two_Watched_Literals_List_Watched_Domain
    Bits_Natural WB_Word_Assn CDCL_Two_Watched_Literals_Lookup_Conflict
begin

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

definition uminus_code where
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
  \<open>ann_lit_wl_assn \<equiv> prod_assn uint32_assn (option_assn nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> array_assn unat_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> clauses_wl \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> arlO_assn clause_ll_assn\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> uint32 list \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn unat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> uint32 list list \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation clauses_to_update_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation clauses_to_update_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: "nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn" where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn unat_lit_assn)\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times> uint32 array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l \<times> watched_wl"


subsubsection \<open>Refinement of the Watched Function\<close>

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>
term watched_by_nth
definition watched_by_nth :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_nth = (\<lambda>(M, N, U, D, NP, UP, Q, W) L i. W L ! i)\<close>

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
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd o snd) S) K w\<close>
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

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo op_nat_lit_eq)) \<in>
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

definition delete_index_and_swap_ll where
  \<open>delete_index_and_swap_ll xs i j =
     xs[i:= delete_index_and_swap (xs!i) j]\<close>

definition delete_index_and_swap_aa where
  \<open>delete_index_and_swap_aa xs i j = do {
     x \<leftarrow> last_aa xs i;
     xs \<leftarrow> update_aa xs i j x;
     set_butlast_aa xs i
  }\<close>


lemma delete_index_and_swap_aa_ll_hnr[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric])


lemma nth_nat_of_uint32_nth': \<open>Array.nth x (nat_of_uint32 L) = Array.nth' x (integer_of_uint32 L)\<close>
  by (auto simp: Array.nth'_def nat_of_uint32_code)

lemma nth_aa_u_code[code]:
  \<open>nth_aa_u x L L' = nth_u_code x L \<bind> (\<lambda>x. arl_get x L' \<bind> return)\<close>
  unfolding nth_aa_u_def nth_aa_def arl_get_u_def[symmetric]  Array.nth'_def[symmetric]
   nth_nat_of_uint32_nth' nth_u_code_def[symmetric] ..

definition last_aa_u where
  \<open>last_aa_u xs i = last_aa xs (nat_of_uint32 i)\<close>

lemma last_aa_u_code[code]:
  \<open>last_aa_u xs i = nth_u_code xs i \<bind> arl_last\<close>
  unfolding last_aa_u_def last_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u_code_def[symmetric] ..

definition update_aa_u where  
  \<open>update_aa_u xs i j = update_aa xs (nat_of_uint32 i) j\<close>

lemma Array_upd_upd': \<open>Array.upd i x a = Array.upd' a (of_nat i) x \<then> return a\<close>
  by (auto simp: Array.upd'_def upd_return)

definition Array_upd_u where
  \<open>Array_upd_u i x a = Array.upd (nat_of_uint32 i) x a\<close>


lemma Array_upd_u_code[code]: \<open>Array_upd_u i x a = heap_array_set'_u a i x \<then> return a\<close>
  unfolding Array_upd_u_def heap_array_set'_u_def
  Array.upd'_def
  by (auto simp: nat_of_uint32_code upd_return)


lemma update_aa_u_code[code]:
  \<open>update_aa_u a i j y = do {
      x \<leftarrow> nth_u_code a i;
      a' \<leftarrow> arl_set x j y;
      Array_upd_u i a' a 
    }\<close> -- \<open>is the Array.upd really needed?\<close>
  unfolding update_aa_u_def update_aa_def nth_nat_of_uint32_nth' nth_nat_of_uint32_nth'
    arl_get_u_def[symmetric] nth_u_code_def[symmetric]
    heap_array_set'_u_def[symmetric] Array_upd_u_def[symmetric]
  by auto

definition set_butlast_aa_u where
  \<open>set_butlast_aa_u xs i = set_butlast_aa xs (nat_of_uint32 i)\<close>

lemma set_butlast_aa_u_code[code]:
  \<open>set_butlast_aa_u a i = do {
      x \<leftarrow> nth_u_code a i;
      a' \<leftarrow> arl_butlast x;
      Array_upd_u i a' a
    }\<close> -- \<open>Replace the \<^term>\<open>i\<close>-th element by the itself execpt the last element.\<close>
  unfolding set_butlast_aa_u_def set_butlast_aa_def
   nth_u_code_def Array_upd_u_def
  by (auto simp: Array.nth'_def nat_of_uint32_code)


definition delete_index_and_swap_aa_u where
   \<open>delete_index_and_swap_aa_u xs i = delete_index_and_swap_aa xs (nat_of_uint32 i)\<close>

lemma delete_index_and_swap_aa_u_code[code]:
\<open>delete_index_and_swap_aa_u xs i j = do {
     x \<leftarrow> last_aa_u xs i;
     xs \<leftarrow> update_aa_u xs i j x;
     set_butlast_aa_u xs i
  }\<close>
  unfolding delete_index_and_swap_aa_u_def delete_index_and_swap_aa_def
   last_aa_u_def update_aa_u_def set_butlast_aa_u_def
  by auto

lemma delete_index_and_swap_aa_ll_hnr_u[sepref_fr_rules]:
  assumes \<open>is_pure R\<close>
  shows \<open>(uncurry2 delete_index_and_swap_aa_u, uncurry2 (RETURN ooo delete_index_and_swap_ll))
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO_assn (arl_assn R))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO_assn (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def delete_index_and_swap_aa_u_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric] uint32_nat_rel_def br_def)


subsection \<open>Code Generation\<close>

subsubsection \<open>More Operations\<close>

fun literals_to_update_wll :: \<open>twl_st_wll \<Rightarrow> lit_queue_l\<close> where
  \<open>literals_to_update_wll (M, N, U, D, NP, UP, Q, W) = Q\<close>

definition literals_to_update_wll_empty :: \<open>twl_st_wll \<Rightarrow> bool\<close> where
  \<open>literals_to_update_wll_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q)\<close>

definition literals_to_update_wl_empty :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q = {#})\<close>

definition select_and_remove_from_literals_to_update_wl' :: \<open>twl_st_wll \<Rightarrow> twl_st_wll \<times> uint32\<close> where
  \<open>select_and_remove_from_literals_to_update_wl' =
    (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>

lemma nat_lit_eq[sepref_fr_rules]: \<open>(uncurry (return oo op =), uncurry (RETURN oo op =)) \<in>
   nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def nat_lit_rel_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)

lemma unat_lit_eq[sepref_fr_rules]: \<open>(uncurry (return oo op =), uncurry (RETURN oo op =)) \<in>
   (unat_lit_assn)\<^sup>k *\<^sub>a (unat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def unat_lit_rel_def
      uint32_nat_rel_def br_def nat_lit_rel_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)

sepref_thm list_contains_WHILE_array
  is \<open>uncurry (\<lambda>(l::nat) xs. do{ b \<leftarrow> list_contains_WHILE l xs; RETURN (fst b)})\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a (array_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding list_contains_WHILE_def
  by sepref

concrete_definition list_contains_WHILE_array_code
   uses list_contains_WHILE_array.refine_raw
   is "(uncurry ?f,_)\<in>_"

lemma list_contains_WHILE_in_set: \<open>list_contains_WHILE l xs \<le>
      \<Down> ({((b', i), b, ys). b' = b \<and>  ys = nths xs {i..<length xs} \<and> i \<le> length xs} O
          Collect (case_prod (\<lambda>(b', ys). op = b')))
        (RETURN (l \<in> set xs))\<close>
  (is \<open>_ \<le> \<Down> ?A _\<close>)
proof -
  show \<open>list_contains_WHILE l xs \<le>
      \<Down> ({((b', i), b, ys). b' = b \<and>  ys = nths xs {i..<length xs} \<and> i \<le> length xs} O
          Collect (case_prod (\<lambda>(b', ys). op = b')))
        (RETURN (l \<in> set xs))\<close>
    (is \<open>_ \<le> \<Down> ?B _\<close>)
    unfolding list_contains_WHILE_def op_list_contains_def
    using ref_two_step[OF WHILE\<^sub>T_nth_WHILE\<^sub>T_list[of \<open>\<lambda>_. True\<close> xs \<open>op = l\<close>]
        op_list_contains, unfolded conc_fun_chain]
    by simp
qed

definition list_contains_WHILE_f where
  \<open>list_contains_WHILE_f l xs = do{ b \<leftarrow> list_contains_WHILE l xs; RETURN (fst b)}\<close>

lemma list_contains_WHILE_f_op_list_contains:
  \<open>(uncurry list_contains_WHILE_f, uncurry (RETURN oo op_list_contains)) \<in>
   Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel
\<close>
proof -
  have 1: \<open>RETURN oo op_list_contains = (\<lambda>l xs. do {b \<leftarrow> RETURN (op_list_contains l xs); RETURN b})\<close>
    by fastforce
  note bind_refine' = bind_refine[where R=Id, simplified]

  show ?thesis
    unfolding list_contains_WHILE_f_def 1
    by (intro frefI nres_relI)
      (auto simp add: fref_def nres_rel_def uncurry_def
        simp del: nres_monad1 nres_monad2
        intro!: bind_refine'  intro!: list_contains_WHILE_in_set)
qed

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

lemma list_contains_WHILE_code_op_list_contains[sepref_fr_rules]:
  \<open>(uncurry list_contains_WHILE_array_code,
    uncurry (RETURN oo op_list_contains)) \<in>
    unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(uncurry (RETURN oo op_list_contains), uncurry (RETURN oo op_list_contains)) \<in>
         nat_lit_rel \<times>\<^sub>r \<langle>nat_lit_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (auto simp: list_rel_def in_nat_list_rel_list_all2_in_set_iff)
  term nat_lit_rel
  have 2: \<open>hr_comp (hr_comp (array_assn uint32_nat_assn) (\<langle>nat_rel\<rangle>list_rel))
       (\<langle>nat_lit_rel\<rangle>list_rel) = array_assn unat_lit_assn\<close>
    by (simp add: array_assn_def unat_lit_rel_def hr_comp_assoc list_rel_compp)

  show ?thesis
    using list_contains_WHILE_array_code.refine[unfolded list_contains_WHILE_f_def[symmetric],
        FCOMP list_contains_WHILE_f_op_list_contains, FCOMP 1]
    unfolding 2 unfolding unat_lit_rel_def .
qed

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

lemma ann_lit_of_pair_if:
  \<open>ann_lit_of_pair (L, D) = (if D = None then Decided L else Propagated L (the D))\<close>
  by (cases D) auto

lemma is_decided_wl_code[sepref_fr_rules]:
  \<open>(is_decided_wl_code, RETURN o is_decided) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>hr_comp ann_lit_wl_assn nat_ann_lit_rel = pair_nat_ann_lit_assn\<close>
    by (fastforce simp: case_prod_beta hr_comp_def[abs_def] pure_def nat_ann_lit_rel_def
        prod_assn_def ann_lit_of_pair_if ex_assn_def imp_ex Abs_assn_eqI(1) ex_simps(1)[symmetric]
        simp del: pair_of_ann_lit.simps literal_of_nat.simps ex_simps(1)
        split: if_splits)
  show ?thesis
    using is_decided_wl_code.refine[FCOMP is_decided_wl_is_decided]
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

definition find_decomp_wl_imp :: "(nat, nat) ann_lits \<Rightarrow> nat clause \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres" where
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

definition no_skip where
  \<open>no_skip S = (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None S)))\<close>

definition no_resolve where
  \<open>no_resolve S = (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None S)))\<close>

definition get_conflict_wl_is_None :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_None D)\<close>

lemma get_conflict_wl_is_None: \<open>get_conflict_wl S = None \<longleftrightarrow> get_conflict_wl_is_None S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_def split: option.splits)

lemma watched_by_nth_watched_app':
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)


context twl_array_code
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
  \<open>find_decomp_wl_imp' = (\<lambda>M N U D NP UP W Q L. find_decomp_wl_imp M D L)\<close>

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

definition (in -) is_pos_code where
  \<open>is_pos_code L \<longleftrightarrow> bitAND L 1 = 0\<close>

lemma (in -) is_pos_hnr[sepref_fr_rules]:
  \<open>(return o is_pos_code, RETURN o is_pos) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(RETURN o is_pos_code, RETURN o is_pos) \<in> nat_lit_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding bitAND_1_mod_2 is_pos_code_def
    by (intro nres_relI frefI) (auto simp: nat_lit_rel_def lit_of_natP_def split: if_splits)
  have 2: \<open>(return o is_pos_code, RETURN o is_pos_code) \<in> uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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

definition delete_index_and_swap_update :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b list" where
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

definition (in twl_array_code_ops) append_update :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list" where
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

lemma literals_to_update_wl_literals_to_update_wl_empty:
  \<open>literals_to_update_wl S = {#} \<longleftrightarrow> literals_to_update_wl_empty S\<close>
  by (cases S) (auto simp: literals_to_update_wl_empty_def)

definition get_conflict_wl_is_Nil :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W). D \<noteq> None \<and> Multiset.is_empty (the D))\<close>

definition get_conflict_wll_is_Nil :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>

lemma get_conflict_wll_is_Nil_get_conflict_wl_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil, RETURN o get_conflict_wl_is_Nil) \<in>
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI) (auto simp: get_conflict_wll_is_Nil_def get_conflict_wl_is_Nil_def
      split: option.splits)

lemma get_conflict_wl_get_conflict_wl_is_Nil:
  \<open>get_conflict_wl S\<^sub>0 = Some {#} \<longleftrightarrow> get_conflict_wl_is_Nil S\<^sub>0\<close>
  by (cases S\<^sub>0) (auto simp add: get_conflict_wl_is_Nil_def Multiset.is_empty_def split: option.splits)

definition is_decided_hd_trail_wl where
  \<open>is_decided_hd_trail_wl S = is_decided (hd (get_trail_wl S))\<close>

definition is_decided_hd_trail_wll :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>is_decided_hd_trail_wll = (\<lambda>(M, N, U, D, NP, UP, Q, W).
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
   [\<lambda>L. \<not>is_decided L]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> (unat_lit_assn *assn nat_assn)\<close>
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

end

end
