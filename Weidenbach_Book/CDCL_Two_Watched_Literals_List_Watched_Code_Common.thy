theory CDCL_Two_Watched_Literals_List_Watched_Code_Common
  imports CDCL_Two_Watched_Literals_Code_Common
    CDCL_Two_Watched_Literals_List_Watched_Domain
    Bits_Natural WB_Word_Assn
begin


section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

definition propagated where
  \<open>propagated L C = (L, Some C)\<close>

lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      lit_of_natP_def br_def  nat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition decided where
  \<open>decided L = (L, None)\<close>

lemma decided_hnr[sepref_fr_rules]:
  \<open>(return o decided, RETURN o Decided) \<in>
     nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def decided_def case_prod_beta p2rel_def
      lit_of_natP_def br_def  nat_lit_rel_def nat_lit_rel_def
      split: option.splits)

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = bitXOR L 1\<close>

lemma uminus_lit_imp_uminus:
  \<open>(RETURN o uminus_lit_imp, RETURN o uminus) \<in>
     nat_lit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_rel\<rangle>nres_rel\<close>
  unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
  by (intro frefI nres_relI) (auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
      lit_of_natP_def nat_lit_rel_def split: option.splits, presburger)

lemma bitXOR_uminus[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. bitXOR L 1), RETURN o uminus) \<in>
     nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn\<close>
proof -
  have 1: \<open>(return o (\<lambda>L. bitXOR L 1), RETURN o uminus_lit_imp) \<in>
     nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
    unfolding bitXOR_1_if_mod_2 uminus_lit_imp_def
    by sepref_to_hoare
     (sep_auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
        lit_of_natP_def  br_def bitXOR_1_if_mod_2
        split: option.splits)
  show ?thesis
    using 1[FCOMP uminus_lit_imp_uminus] .
qed


subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym clauses_wl = \<open>nat arrayO_raa\<close>
abbreviation ann_lit_wl_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_assn \<equiv> prod_assn nat_assn (option_assn nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> array_assn nat_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> clauses_wl \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> arlO_assn clause_ll_assn\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat list list \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation clauses_to_update_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation clauses_to_update_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: "nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn" where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn nat_lit_assn)\<close>

abbreviation conflict_assn :: "nat clause \<Rightarrow> nat array_list \<Rightarrow> assn" where
  \<open>conflict_assn \<equiv> hr_comp (arl_assn nat_lit_assn) list_mset_rel\<close>

abbreviation conflict_option_assn :: "nat clause option \<Rightarrow> nat array_list option \<Rightarrow> assn" where
  \<open>conflict_option_assn \<equiv> option_assn conflict_assn\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times> nat array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
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

definition valued_impl :: "(nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option nres" where
  \<open>valued_impl M L =
    nfoldli M
     (\<lambda>brk. brk = None)
     (\<lambda>L' _. do {
       let L\<^sub>1 = atm_of L;
       let L\<^sub>2 = (lit_of L');
       let L\<^sub>2' = atm_of (lit_of L');
       if L = L\<^sub>2 then RETURN (Some True)
       else
         if L\<^sub>1 = L\<^sub>2' then RETURN (Some False) else RETURN None
    })
    None\<close>

lemma valued_impl_valued:
  assumes \<open>no_dup M\<close>
  shows \<open>valued_impl M L = RETURN (valued M L)\<close>
  using assms
  apply (induction M)
   apply (simp add: valued_def valued_impl_def Decided_Propagated_in_iff_in_lits_of_l
      atm_of_eq_atm_of)[]
  by (auto simp add: valued_def valued_impl_def defined_lit_map dest: in_lits_of_l_defined_litD)

lemma valued_impl_spec:
  shows \<open>(uncurry valued_impl, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). no_dup M]\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding fref_def nres_rel_def
  by (auto simp: valued_impl_valued IS_ID_def)

lemma atm_of_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. shiftr L 1), RETURN o op_atm_of) \<in> (pure nat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def lit_of_natP_def  br_def
      Collect_eq_comp nat_lit_rel_def nat_lit_rel_def)

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> (pure nat_ann_lit_rel)\<^sup>k \<rightarrow>\<^sub>a (pure nat_lit_rel)\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def
      Collect_eq_comp br_def nat_lit_rel_def nat_lit_rel_def
      split: if_splits)
  unfolding br_def
   apply (case_tac b)
    apply simp_all
  apply (case_tac b)
   apply (auto
      elim!: run_elims
      simp: hoare_triple_def snga_assn_def Let_def new_addrs_def relH_def in_range.simps mod_emp)
  done

text \<open>This lemma is present in Isabelle repository:\<close>
lemma (in semidom_divide) dvd_div_eq_iff:
  "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> a div c = b div c \<longleftrightarrow> a = b"
  by (elim dvdE, cases "c = 0") simp_all

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo op_nat_lit_eq)) \<in>
    (pure nat_lit_rel)\<^sup>k *\<^sub>a (pure nat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have [simp]: \<open>even bi \<Longrightarrow> even ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  have [simp]: \<open>odd bi \<Longrightarrow> odd ai \<Longrightarrow> ai div 2 = bi div 2 \<Longrightarrow> ai = bi\<close> for ai bi :: nat
    by presburger
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def nat_lit_rel_def
        br_def Collect_eq_comp dvd_div_eq_iff nat_lit_rel_def
      split: if_splits)+
qed

text \<open>TODO Move to declaration\<close>
sepref_definition valued_impl' is \<open>uncurry valued_impl\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_impl_def Let_def
  by sepref

lemma valued_impl'[sepref_fr_rules]: \<open>(uncurry valued_impl', uncurry (RETURN oo valued)) \<in>
   [\<lambda>(a, b). no_dup a]\<^sub>a pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  using valued_impl'.refine[FCOMP valued_impl_spec] by auto

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

definition find_unwatched' :: "(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> (nat option) nres" where
\<open>find_unwatched' M N' C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length (N'!C) \<and> (\<forall>j\<in>{2..<i}. -((N'!C)!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M ((N'!C)!j) \<or> (N'!C)!j \<in> lits_of_l M) \<and> j < length (N'!C) \<and> j \<ge> 2))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length (N'!C))
    (\<lambda>(_, i). do {
      ASSERT(i < length (N'!C));
      case valued M ((N'!C)!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
      }
    )
    (None, 2::nat);
   RETURN (fst S)
  }
\<close>
lemma find_unwatched'_find_unwatched: \<open>find_unwatched' M N' C = find_unwatched M (N'!C)\<close>
  unfolding find_unwatched'_def find_unwatched_def
  by auto

sepref_definition find_unwatched'_impl
  is \<open>uncurry2 find_unwatched'\<close>
  :: \<open>[\<lambda>((M, N'), C). no_dup M \<and> C < length N']\<^sub>a
        pair_nat_ann_lits_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
        option_assn nat_assn\<close>
  unfolding find_unwatched'_def nth_rll_def[symmetric] length_rll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare find_unwatched'_impl.refine[sepref_fr_rules]


subsection \<open>Code Generation\<close>

subsubsection \<open>More Operations\<close>

fun literals_to_update_wll :: \<open>twl_st_wll \<Rightarrow> lit_queue_l\<close> where
  \<open>literals_to_update_wll (M, N, U, D, NP, UP, Q, W) = Q\<close>

definition literals_to_update_wll_empty :: \<open>twl_st_wll \<Rightarrow> bool\<close> where
  \<open>literals_to_update_wll_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q)\<close>

definition literals_to_update_wl_empty :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q = {#})\<close>

definition select_and_remove_from_literals_to_update_wl' :: \<open>twl_st_wll \<Rightarrow> twl_st_wll \<times> nat\<close> where
  \<open>select_and_remove_from_literals_to_update_wl' =
    (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>

lemma nat_lit_eq[sepref_fr_rules]: \<open>(uncurry (return oo op =), uncurry (RETURN oo op =)) \<in>
   (nat_lit_assn)\<^sup>k *\<^sub>a (nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def nat_lit_rel_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)

sepref_thm list_contains_WHILE_array
  is \<open>uncurry (\<lambda>(l::nat) xs. do{ b \<leftarrow> list_contains_WHILE l xs; RETURN (fst b)})\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (array_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding list_contains_WHILE_def
  by sepref

concrete_definition list_contains_WHILE_array_code
   uses list_contains_WHILE_array.refine_raw
   is "(uncurry ?f,_)\<in>_"

lemma list_contains_WHILE_in_set: \<open>list_contains_WHILE l xs \<le>
      \<Down> ({((b', i), b, ys). b' = b \<and>  ys = sublist xs {i..<length xs} \<and> i \<le> length xs} O
          Collect (case_prod (\<lambda>(b', ys). op = b')))
        (RETURN (l \<in> set xs))\<close>
  (is \<open>_ \<le> \<Down> ?A _\<close>)
proof -
  show \<open>list_contains_WHILE l xs \<le>
      \<Down> ({((b', i), b, ys). b' = b \<and>  ys = sublist xs {i..<length xs} \<and> i \<le> length xs} O
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
    nat_lit_assn\<^sup>k *\<^sub>a (clause_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(uncurry (RETURN oo op_list_contains), uncurry (RETURN oo op_list_contains)) \<in>
         nat_lit_rel \<times>\<^sub>r \<langle>nat_lit_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (auto simp: list_rel_def in_nat_list_rel_list_all2_in_set_iff)
  term nat_lit_rel
  have 2: \<open>hr_comp (hr_comp (array_assn nat_assn) (\<langle>nat_rel\<rangle>list_rel))
       (\<langle>nat_lit_rel\<rangle>list_rel) = array_assn nat_lit_assn\<close>
    by (simp add: array_assn_def nat_lit_rel_def hr_comp_assoc list_rel_compp)

  show ?thesis
    using list_contains_WHILE_array_code.refine[unfolded list_contains_WHILE_f_def[symmetric],
        FCOMP list_contains_WHILE_f_op_list_contains, FCOMP 1]
    unfolding 2 unfolding nat_lit_rel_def .
qed

definition get_level_wl where
  \<open>get_level_wl M L =
     snd (fold (\<lambda>i (found, l::nat). if atm_of (lit_of (M!i)) = atm_of L \<or> found
                   then if is_decided (M!i) then (True, l+1) else (True, l)
                   else (found, l)
               )
          [0..<length M]
          (False, 0))\<close>

lemma get_level_wl_get_level:
  \<open>get_level_wl M L = get_level M L\<close>
proof -
  define f where
    \<open>f x = (\<lambda>(found, l::nat). if atm_of (lit_of x) = atm_of L \<or> found
                   then if is_decided x
                     then (True, l+1)
                     else (True, l)
                   else (found, l)
               )\<close> for x :: \<open>('a literal, 'a literal, 'b) annotated_lit\<close>
  have [simp]: \<open>f a (False, i) = (True, i + (if is_decided a then 1 else 0))\<close>  if \<open>atm_of (lit_of a) = atm_of L\<close>  for i a
    using that unfolding f_def by auto
  have [simp]: \<open>f a (True, k) = (True, k + (if is_decided a then 1 else 0))\<close> for a k
    unfolding f_def by auto
  have [simp]: \<open>f a (False, k) = (False, k)\<close> if \<open>atm_of (lit_of a) \<noteq> atm_of L\<close> for a k
    using that unfolding f_def by auto
  have [simp]: \<open>snd (fold f M (True, k)) = k + count_decided M\<close> for M and k :: nat
    by (induction M arbitrary: k) (auto simp: get_maximum_level_add_mset)
  have [simp]: \<open>snd (fold f M (False, k)) = k + get_level M L\<close>
      for M and k :: nat
    apply (induction M arbitrary: k)
    subgoal by simp
    subgoal for a D k
      by (cases \<open>atm_of (lit_of a) = atm_of L\<close>) (auto simp: get_maximum_level_add_mset)
    done

  show ?thesis
    unfolding get_level_wl_def f_def[symmetric]
      fold_idx_conv[symmetric]
    by simp
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

text \<open>TODO: as levels are less than the numbers of literals, change to \<^typ>\<open>nat\<close>?\<close>
sepref_definition get_level_wl_code
  is \<open>uncurry (RETURN oo get_level_wl)\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_level_wl_def[abs_def]
  by sepref

declare get_level_wl_code.refine[sepref_fr_rules]

definition maximum_level_remove where
  \<open>maximum_level_remove M D L =
     snd (fold (\<lambda>i (found, l). if D!i = L \<and> \<not>found then (True, l) else (found, max (get_level M (D!i)) l))
          [0..<length D]
          (False, 0))\<close>

lemma get_level_wl_code_get_level[sepref_fr_rules]:
  \<open>(uncurry get_level_wl_code, uncurry (RETURN oo (get_level :: (nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> nat))) \<in>
    pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  using get_level_wl_code.refine unfolding get_level_wl_get_level[abs_def] .

sepref_definition maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo maximum_level_remove)\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a (arl_assn nat_lit_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_remove_def[abs_def]
  by sepref

declare maximum_level_remove_code.refine

lemma maximum_level_remove:
  \<open>maximum_level_remove M D L = get_maximum_level M (remove1_mset L (mset D))\<close>
proof -
  define f where
    \<open>f x = (\<lambda>(found, l).
              if x = L \<and> \<not> found then (True, l)
              else (found, max (get_level M x) l))\<close> for x
  have [simp]: \<open>f L (False, i) = (True, i)\<close> for i
    unfolding f_def by auto
  have [simp]: \<open>f a (True, k) = (True, max (get_level M a) k)\<close> for a k
    unfolding f_def by auto
  have [simp]: \<open>f a (False, k) = (False, max (get_level M a) k)\<close> if \<open>a \<noteq> L\<close> for a k
    using that unfolding f_def by auto
  have [simp]: \<open>snd (fold f D (True, k)) = max k (get_maximum_level M (mset D))\<close> for D and k :: nat
    by (induction D arbitrary: k) (auto simp: get_maximum_level_add_mset)
  have [simp]: \<open>snd (fold f D (False, k)) = max k (get_maximum_level M (remove1_mset L (mset D)))\<close>
      for D and k :: nat
    apply (induction D arbitrary: k)
    subgoal by simp
    subgoal for a D k
      by (cases \<open>a = L\<close>) (auto simp: get_maximum_level_add_mset)
    done

  show ?thesis
    unfolding maximum_level_remove_def f_def[symmetric]
      fold_idx_conv[symmetric]
    by simp
qed

definition get_maximum_level_remove where
  \<open>get_maximum_level_remove M D L =  get_maximum_level M (remove1_mset L D)\<close>

lemma maximum_level_remove_code_get_maximum_level_remove[sepref_fr_rules]:
  \<open>(uncurry2 (maximum_level_remove_code),
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    pair_nat_ann_lits_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
proof -
  have 1:
  \<open>(uncurry2 (RETURN ooo maximum_level_remove),
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    ((Id \<times>\<^sub>r list_mset_rel) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    by (auto intro!: nres_relI frefI simp: list_mset_rel_def br_def maximum_level_remove
        get_maximum_level_remove_def)
  show ?thesis
    using maximum_level_remove_code.refine[FCOMP 1] .
qed


definition count_decided_wl :: "('a, 'b, 'c) annotated_lit list \<Rightarrow> nat" where
  \<open>count_decided_wl M =
    fold (\<lambda>i j. if is_decided (M!i) then j+1 else j)
      [0..<length M]
       0\<close>
lemma count_decided_wl_count_decided:
  \<open>count_decided_wl M = count_decided M\<close>
proof -
  define f where
    \<open>f x = (\<lambda>j::nat. if is_decided x then j+1 else j)\<close> for x :: \<open>('a, 'b, 'c) annotated_lit\<close>
  have [simp]: \<open>f a 0 = (if is_decided a then 1 else 0)\<close> for a
    unfolding f_def by auto
  have [simp]: \<open>f a k = k + 1\<close> if \<open>is_decided a\<close> for a k
    using that unfolding f_def by auto
  have [simp]: \<open>f a k = k\<close> if \<open>\<not>is_decided a\<close> for a k
    using that unfolding f_def by auto
  have [simp]: \<open>fold f M k = k + count_decided M\<close> for k :: nat
    apply (induction M arbitrary: k)
    subgoal by simp
    subgoal by (auto simp: get_maximum_level_add_mset)
    done

  show ?thesis
    unfolding count_decided_wl_def f_def[symmetric]
      fold_idx_conv[symmetric]
    by simp
qed

sepref_definition count_decided_wl_code
  is \<open>RETURN o count_decided_wl\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding count_decided_wl_def
  by sepref

lemmas count_decided_wl_code[sepref_fr_rules] = count_decided_wl_code.refine[unfolded count_decided_wl_count_decided]


definition find_first_eq where
  \<open>find_first_eq x xs = WHILE\<^sub>T\<^bsup>\<lambda>i. i \<le> length xs\<^esup>
       (\<lambda>i. i < length xs \<and> xs!i \<noteq> x)
       (\<lambda>i. RETURN (i+1))
       0\<close>

lemma find_first_eq_index:
  shows \<open>find_first_eq x xs \<le> \<Down> nat_rel (RETURN (index xs x))\<close>
proof -
  have H:
    \<open>WHILE\<^sub>T\<^bsup>\<lambda>i. i \<le> length xs\<^esup>
       (\<lambda>i. i < length xs \<and> xs!i \<noteq> x)
       (\<lambda>i. RETURN (i+1))
       k
     \<le> \<Down> nat_rel
       (RETURN (k + index (sublist xs {k..<length xs}) x))\<close>
    if \<open>k < length xs\<close> for k
    using that
  proof (cases xs)
    case Nil
    then show ?thesis using that by simp
  next
    case xs: (Cons a xs')
    have index_first: \<open>index (sublist (a # xs') {n..<Suc (length xs')}) ((a # xs') ! n) = 0\<close>
      if \<open>n < length xs'\<close> for n
      using that by (metis index_Cons length_Cons less_SucI sublist_upt_Suc)
    have [simp]: "sublist (a # xs') {n..<Suc (length xs')} =
    (a # xs') ! n # sublist (a # xs') {Suc n..<Suc (length xs')}"
      if a2: "n < length xs'" for n -- \<open>auto is not able to derive it automatically
      because of @{thm length_Cons}\<close>
      using a2 by (metis length_Cons less_SucI sublist_upt_Suc)

    have \<open>k < Suc (length xs')\<close>
      using that xs by auto
    then show ?thesis
      unfolding find_first_eq_def less_eq_Suc_le Suc_le_mono xs
      apply (induction rule: inc_induct)
      subgoal by (auto simp: sublist_single_if WHILEIT_unfold)[]
      subgoal by (subst WHILEIT_unfold) (auto simp: sublist_single_if index_first sublist_upt_Suc)
      done
  qed
  have [simp]: \<open>find_first_eq x [] \<le> RETURN 0\<close>
    unfolding find_first_eq_def by (auto simp: WHILEIT_unfold)[]
  have [simp]: \<open>sublist xs {0..<length xs} = xs\<close>
    by (simp add: sublist_id_iff)
  show ?thesis
    apply (cases \<open>xs = []\<close>)
     apply (solves simp)
    using H[of 0] unfolding find_first_eq_def by simp
qed

definition is_in_arl where
  \<open>is_in_arl x xs = do {
    i \<leftarrow> find_first_eq x xs;
    RETURN (i < length xs)
  }\<close>

lemma in_list_all2_ex_in: \<open>a \<in> set xs \<Longrightarrow> list_all2 R xs ys \<Longrightarrow> \<exists>b \<in> set ys. R a b\<close>
  apply (subgoal_tac \<open>length xs = length ys\<close>)
   apply (rotate_tac 2)
   apply (induction xs ys rule: list_induct2)
    apply ((solves auto)+)[2]
  using list_all2_lengthD by blast

lemma is_in_arl_op_mset_contains:
  assumes \<open>IS_RIGHT_UNIQUE R\<close> and \<open>IS_LEFT_UNIQUE R\<close>
  shows \<open>(uncurry is_in_arl, uncurry (RETURN oo op_mset_contains)) \<in>
   R \<times>\<^sub>r (list_mset_rel O \<langle>R\<rangle>mset_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
proof -
  let ?f = \<open>\<lambda>(x::'a) xs. do {let i = index xs x; RETURN (i < length xs)}\<close>
  have 1: \<open>(uncurry ?f, uncurry (RETURN oo op_mset_contains)) \<in>
   R \<times>\<^sub>r (list_mset_rel O \<langle>R\<rangle>mset_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
    apply (intro frefI nres_relI)
      using assms
    apply (auto simp:list_mset_rel_def mset_rel_def p2rel_def[abs_def] rel_mset_def br_def
        index_less_size_conv
        dest: in_list_all2_ex_in)
       apply (metis in_set_conv_nth list_all2_conv_all_nth mset_eq_setD rel2p_def single_valued_def)
      by (metis IS_LEFT_UNIQUED in_set_conv_nth list_all2_conv_all_nth mset_eq_setD rel2p_def)
  have \<open>is_in_arl x xs\<le> \<Down> bool_rel (?f x xs)\<close> for x xs
    unfolding is_in_arl_def
    by (refine_vcg find_first_eq_index) auto
  then have 2: \<open>(uncurry is_in_arl, uncurry ?f) \<in> Id \<times>\<^sub>r \<langle>Id\<rangle> list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (force simp: uncurry_def)
  have 3: \<open>\<langle>Id\<rangle>list_rel O list_mset_rel O \<langle>R\<rangle>mset_rel = (list_mset_rel O \<langle>R\<rangle>mset_rel)\<close>
    by simp
  show ?thesis
    using 2[FCOMP 1, unfolded 3] .
qed


lemma
  nat_lit_assn_right_unique:
    \<open>CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) nat_lit_assn\<close> and
  nat_lit_assn_left_unique:
    \<open>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) nat_lit_assn\<close>
   by (auto simp: IS_PURE_def single_valued_def p2rel_def IS_LEFT_UNIQUE_def nat_lit_rel_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)


sepref_definition is_in_arl_code
  is \<open>uncurry is_in_arl\<close>
  :: \<open>(pure nat_lit_rel)\<^sup>k *\<^sub>a (arl_assn (nat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_in_arl_def find_first_eq_def short_circuit_conv
  supply [[goals_limit = 1]]
  by sepref

lemma is_in_arl_op_mset_contains_nat_lit_rel[sepref_fr_rules]:
  shows \<open>(uncurry is_in_arl_code, uncurry (RETURN oo op_mset_contains)) \<in>
   (pure nat_lit_rel)\<^sup>k *\<^sub>a conflict_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>IS_LEFT_UNIQUE Id\<close>
    using IS_LEFT_UNIQUE_def single_valued_def by auto
  have 2: \<open>list_mset_rel O \<langle>Id\<rangle>mset_rel = list_mset_rel\<close>
    by (auto simp add: list_mset_rel_def mset_rel_def br_def Collect_eq_comp rel2p_def[abs_def]
        p2rel_def rel_mset_def list.rel_eq)
  have 3: \<open>(hr_comp (arl_assn nat_lit_assn) (list_mset_rel O \<langle>Id\<rangle>mset_rel)) = conflict_assn\<close>
    by (auto simp: hr_comp_def[abs_def] 2)
  show ?thesis
    using is_in_arl_code.refine[FCOMP is_in_arl_op_mset_contains, of Id]
    by (auto simp: 1 3)
qed


text \<open>The order is \<^emph>\<open>not\<close> preserved. However, the function moves only one element (and therefore,
  is compatible with a reasonable refinement to arrays).\<close>
definition remove1_wl where
  \<open>remove1_wl x xs = do {
     i \<leftarrow> find_first_eq x xs;
    let l = length xs;
    if i = l
    then RETURN xs
    else do {
      ASSERT(pre_list_swap((xs, i), l-1));
      RETURN (butlast (swap xs i (l - 1)))}
   }
\<close>

sepref_definition find_first_eq_code
  is \<open>uncurry find_first_eq\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding find_first_eq_def short_circuit_conv
  by sepref

declare find_first_eq_code.refine[sepref_fr_rules]

sepref_definition remove1_wl_code
  is \<open>uncurry remove1_wl\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a arl_assn nat_assn\<close>
  unfolding remove1_wl_def short_circuit_conv
  by sepref

lemma remove1_wl_remove1: \<open>(uncurry remove1_wl, uncurry (RETURN oo remove1)) \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>{(l, l'). mset l = mset l'}\<rangle> nres_rel\<close>
proof -
  have 1: \<open>RETURN (remove1 x xs) = RES {index xs x} \<bind>  (\<lambda>_. RETURN (remove1 x xs))\<close> for x and
    xs :: \<open>'a list\<close>
    unfolding RETURN_def[symmetric] by auto
  have [simp]: \<open>aa \<in> set ba \<Longrightarrow> ba \<noteq> []\<close> for aa and ba :: \<open>'a list\<close>
    by (cases ba) auto
  have [simp]: \<open>last ba = aa\<close> if \<open>Suc (index ba aa) = length ba\<close> and \<open>ba \<noteq> []\<close> for ba :: \<open>'a list\<close>
    and aa
    using that by (metis One_nat_def Suc_to_right index_conv_size_if_notin last_conv_nth
        n_not_Suc_n nth_index)
  have [simp]: \<open>do {
               i \<leftarrow> find_first_eq aa ba;
               let l = length ba;
               if i = l then RETURN ba
               else do {
                 _ \<leftarrow> ASSERT (pre_list_swap ((ba, i), l - 1));
                 RETURN (butlast (swap ba i (l - 1)))
               }
             }
       \<le> \<Down> {(l, l'). mset l = mset l'}
           (RETURN (remove1 aa ba))\<close> for aa and ba :: \<open>'a list\<close>
    apply (subst 1)
    apply (rule bind_refine_RES(2))
    unfolding RETURN_def[symmetric] Let_def
     apply (rule find_first_eq_index)
    apply (auto simp: mset_butlast_remove1_mset last_list_update swap_def
        mset_update nth_list_update')
    done
  show ?thesis
    by (intro frefI nres_relI) (clarsimp simp: remove1_wl_def)
qed

(* TODO Move *)
lemma diff_add_mset_remove1: \<open>NO_MATCH {#} N \<Longrightarrow> M - add_mset a N = remove1_mset a (M - N)\<close>
  by auto

lemma list_all2_remove: \<open>lit_of_natP a aa \<Longrightarrow>
       list_all2 lit_of_natP xs ys \<Longrightarrow>
       \<exists>xs'. mset xs' = remove1_mset a (mset xs) \<and>
            (\<exists>ys'. mset ys' = remove1_mset aa (mset ys) \<and> list_all2 lit_of_natP xs' ys')\<close>
  apply (rotate_tac 1)
proof (induction xs ys rule: list_all2_induct)
  case Nil
  then show ?case by auto
next
  case (Cons x y xs ys) note IH = this(3) and p = this(1, 2, 4)

  have ax: \<open>{#a, x#} = {#x, a#}\<close>
    by auto
  have rem1: \<open>remove1_mset a (remove1_mset x M) = remove1_mset x (remove1_mset a M)\<close> for M
    by (auto simp: ax)
  have H: \<open>x = a \<longleftrightarrow> y = aa\<close>
    using lit_of_natP_same_leftD lit_of_natP_same_rightD p(1) p(3) by blast
   obtain xs' ys' where
    \<open>mset xs' = remove1_mset a (mset xs)\<close> and
    \<open>mset ys' = remove1_mset aa (mset ys)\<close> and
    \<open>list_all2 lit_of_natP xs' ys'\<close>
    using IH p by auto
   then show ?case
    apply (cases \<open>x \<noteq> a\<close>)
    subgoal
      using p
      by (auto intro!: exI[of _ \<open>x#xs'\<close>] exI[of _ \<open>y#ys'\<close>]
          simp: diff_add_mset_remove1 rem1 add_mset_remove_trivial_If in_remove1_mset_neq H
          simp del: diff_diff_add_mset)
    subgoal
      using p
      apply simp
      apply (auto
          simp: diff_add_mset_remove1 rem1 add_mset_remove_trivial_If in_remove1_mset_neq
          remove_1_mset_id_iff_notin H
          simp del: diff_diff_add_mset)
      done
    done
qed

lemma remove1_remove1_mset: \<open>(uncurry (RETURN oo remove1), uncurry (RETURN oo remove1_mset)) \<in>
    nat_lit_rel \<times>\<^sub>r (list_mset_rel O \<langle>nat_lit_rel\<rangle> mset_rel) \<rightarrow>\<^sub>f
    \<langle>list_mset_rel O \<langle>nat_lit_rel\<rangle> mset_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  using list_all2_remove
  by (fastforce simp: remove1_wl_def list_mset_rel_def br_def mset_rel_def p2rel_def
      rel2p_def[abs_def] rel_mset_def Collect_eq_comp nat_lit_rel_def)


lemma list_all2_op_eq_map_right_iff': \<open>list_all2 (\<lambda>L L'. L' = (f L)) a aa \<longleftrightarrow> aa = map f a \<close>
  apply (induction a arbitrary: aa)
   apply (auto; fail)
  by (rename_tac aa, case_tac aa) (auto)

lemma ex_assn_def_pure_eq_middle3:
  \<open>(\<exists>\<^sub>Aba b bb. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Ab ba bb. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Ab bb ba. f b ba bb * \<up> (ba = h b bb) * P b ba bb) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * P b (h b bb) bb)\<close>
  \<open>(\<exists>\<^sub>Aba b bb. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  \<open>(\<exists>\<^sub>Ab ba bb. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  \<open>(\<exists>\<^sub>Ab bb ba. f b ba bb * \<up> (ba = h b bb \<and> Q b ba bb)) = (\<exists>\<^sub>Ab bb. f b (h b bb) bb * \<up>(Q b (h b bb) bb))\<close>
  by (subst ex_assn_def, subst (3) ex_assn_def, auto)+

lemma ex_assn_def_pure_eq_middle2:
  \<open>(\<exists>\<^sub>Aba b. f b ba  * \<up> (ba = h b) * P b ba) = (\<exists>\<^sub>Ab . f b (h b) * P b (h b))\<close>
  \<open>(\<exists>\<^sub>Ab ba. f b ba  * \<up> (ba = h b) * P b ba) = (\<exists>\<^sub>Ab . f b (h b) * P b (h b))\<close>
  \<open>(\<exists>\<^sub>Ab ba. f b ba  * \<up> (ba = h b \<and> Q b ba)) = (\<exists>\<^sub>Ab. f b (h b) * \<up>(Q b (h b)))\<close>
  \<open>(\<exists>\<^sub>A ba b. f b ba  * \<up> (ba = h b \<and> Q b ba)) = (\<exists>\<^sub>Ab. f b (h b) * \<up>(Q b (h b)))\<close>
  by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

lemma ex_assn_skip_first2:
  \<open>(\<exists>\<^sub>Aba bb. f bb * \<up>(P ba bb)) = (\<exists>\<^sub>Abb. f bb * \<up>(\<exists>ba. P ba bb))\<close>
  \<open>(\<exists>\<^sub>Abb ba. f bb * \<up>(P ba bb)) = (\<exists>\<^sub>Abb. f bb * \<up>(\<exists>ba. P ba bb))\<close>
  apply (subst ex_assn_swap)
  by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

lemma remove1_wl_code_op_mset_delete[sepref_fr_rules]:
  \<open>(uncurry (remove1_wl_code), uncurry (RETURN oo op_mset_delete)) \<in>
     nat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow>\<^sub>a conflict_assn\<close>
  (is \<open>_ \<in> _ *\<^sub>a ?c\<^sup>d \<rightarrow>\<^sub>a ?o\<close>)
proof -
  have H: \<open>(uncurry remove1_wl_code, uncurry (RETURN \<circ>\<circ> remove1_mset))
    \<in> (pure (nat_lit_rel))\<^sup>k *\<^sub>a
   (hr_comp (hr_comp (arl_assn nat_assn) (\<langle>nat_rel\<rangle>list_rel))
     (list_mset_rel O
      \<langle>nat_lit_rel\<rangle>mset_rel))\<^sup>d \<rightarrow>\<^sub>a hr_comp
    (hr_comp (arl_assn nat_assn) {(l, l'). mset l = mset l'})
     (list_mset_rel O \<langle>nat_lit_rel\<rangle>mset_rel)\<close>
  (is \<open>_ \<in> _ *\<^sub>a ?c'\<^sup>d \<rightarrow>\<^sub>a ?o'\<close>)
    using remove1_wl_code.refine[FCOMP remove1_wl_remove1, FCOMP remove1_remove1_mset] .
  have a_eq_ex_iff: \<open>(\<exists>xs. mset xs = mset ba \<and> literal_of_nat `# mset xs = a) \<longleftrightarrow>
        (a = literal_of_nat `# mset ba)\<close>
       for a ba
    using ex_mset[of \<open>mset ba\<close>]
    by (auto simp del: literal_of_nat.simps)

  have c: \<open>?c' = ?c\<close>
    by (auto simp: hr_comp_def[abs_def]
          ex_assn_def_pure_eq_middle2
         ex_assn_def_pure_eq_middle3
         list_mset_rel_def br_def mset_rel_def
          rel2p_def[abs_def]
          p2rel_def a_eq_ex_iff
          rel_mset_def
          Collect_eq_comp
          nat_lit_rel_def
          lit_of_natP_def
          list_all2_op_eq_map_right_iff
          arl_assn_def list_rel_def
        simp del: literal_of_nat.simps
        intro!: ext)

   have ex_iff: \<open>(\<exists>b. mset ba = mset b \<and> a = literal_of_nat `# mset b) \<longleftrightarrow>
         a = literal_of_nat `# mset ba\<close>
    for a ba bb
    using ex_mset[of \<open>mset ba\<close>]
    by (auto simp del: literal_of_nat.simps)

  have o': \<open>?o' = ?o\<close>
        by (auto simp: hr_comp_def[abs_def]
          ex_assn_def_pure_eq_middle2
         ex_assn_def_pure_eq_middle3
         list_mset_rel_def br_def mset_rel_def
          rel2p_def[abs_def]
          p2rel_def a_eq_ex_iff
          rel_mset_def ex_iff
          Collect_eq_comp
          nat_lit_rel_def
          lit_of_natP_def ex_assn_skip_first2
          list_all2_op_eq_map_right_iff
          arl_assn_def list_rel_def
        simp del: literal_of_nat.simps
        intro!: ext)

  show ?thesis
    using H unfolding c o' op_mset_delete_def .
qed

definition maximum_level :: \<open>(nat, nat) ann_lits \<Rightarrow> nat literal list \<Rightarrow> nat\<close> where
  \<open>maximum_level M D = fold (\<lambda>i l. max (get_level M (D!i)) l) [0..<length D] 0\<close>

sepref_definition maximum_level_code
  is \<open>uncurry (RETURN oo (maximum_level :: (nat, nat) ann_lits \<Rightarrow> nat literal list \<Rightarrow> nat))\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a (arl_assn nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_def
  by sepref

lemma maximum_level_get_maximum_level:
  \<open>(uncurry (RETURN oo maximum_level), uncurry (RETURN oo get_maximum_level)) \<in>
    Id \<times>\<^sub>r list_mset_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
proof -
  define f where \<open>f M x \<equiv> max (get_level M x)\<close>
    for M :: \<open>(nat, nat) ann_lits\<close> and x

  have [simp]: \<open>fold (f M) D k = max k (get_maximum_level M (mset D))\<close> for M D k
    by (induction D arbitrary: k) (auto simp: get_maximum_level_add_mset f_def)
  show ?thesis
    unfolding maximum_level_def
    apply (intro frefI nres_relI)
    unfolding f_def[symmetric]
      fold_idx_conv[symmetric]
    by (auto simp: list_mset_rel_def br_def)
qed

lemma maximum_level_code_get_maximum_level[sepref_fr_rules]:
  \<open>(uncurry maximum_level_code, uncurry (RETURN oo get_maximum_level))
    \<in> pair_nat_ann_lits_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  using maximum_level_code.refine[FCOMP maximum_level_get_maximum_level] .

text \<open>TODO: avoid copy of the list (use index)\<close>
definition union_mset_list_fold where
  \<open>union_mset_list_fold xs ys =
    (let xs' = op_list_copy xs in
    fold (\<lambda>i zs. if ys!i \<in> set xs' then zs else zs @ [ys!i])
      [0..<length ys]
      xs)\<close>

lemma union_mset_list_fold_union_mset:
  fixes xs ys :: \<open>'a list\<close>
  assumes \<open>distinct xs\<close> and \<open>distinct ys\<close>
  shows \<open>mset (union_mset_list_fold xs ys) = mset xs \<union># mset ys\<close>
proof -
  define f where
    \<open>f xs x zs = (if x \<in> set xs then zs else zs @ [x])\<close>
    for xs and x :: \<open>'a\<close> and zs :: \<open>'a list\<close>
  have 1: \<open>a \<notin> set ys \<Longrightarrow>
       a \<in> set xs \<Longrightarrow>
       mset ys - mset xs = add_mset a (mset ys) - mset xs\<close> for a and xs ys :: \<open>'a list\<close>
    by (metis add_mset_diff_bothsides diff_intersect_left_idem in_multiset_in_set insert_DiffM
        inter_add_right1)
  have [simp]: \<open>mset (fold (f xs) ys xs') = mset xs' + (mset ys - mset xs)\<close> for xs'
    using assms
    by (induction ys arbitrary: xs xs') (auto simp: f_def 1)
  show ?thesis
    unfolding union_mset_list_fold_def
      f_def[symmetric]
      fold_idx_conv[symmetric]
    by (simp add: sup_subset_mset_def)
qed

lemma is_in_arl_op_list_contains:
  assumes \<open>IS_RIGHT_UNIQUE R\<close> and \<open>IS_LEFT_UNIQUE R\<close>
  shows \<open>(uncurry is_in_arl, uncurry (RETURN oo op_list_contains)) \<in>
   R \<times>\<^sub>r (\<langle>R\<rangle>list_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
proof -
  let ?f = \<open>\<lambda>(x::'a) xs. do {let i = index xs x; RETURN (i < length xs)}\<close>
  have 1: \<open>(uncurry ?f, uncurry (RETURN oo op_list_contains)) \<in>
   R \<times>\<^sub>r (\<langle>R\<rangle>list_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
    apply (intro frefI nres_relI)
    using assms
    apply (auto simp: set_rel_def p2rel_def[abs_def] rel_set_def br_def
        index_less_size_conv list_rel_def
        dest: in_list_all2_ex_in)
     apply (metis (no_types, lifting) IS_RIGHT_UNIQUED in_list_all2_ex_in)
    by (smt IS_LEFT_UNIQUED list_all2_conv_all_nth mem_Collect_eq set_conv_nth)

  have \<open>is_in_arl x xs\<le> \<Down> bool_rel (?f x xs)\<close> for x xs
    unfolding is_in_arl_def
    by (refine_vcg find_first_eq_index) auto
  then have 2: \<open>(uncurry is_in_arl, uncurry ?f) \<in> Id \<times>\<^sub>r \<langle>Id\<rangle> list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (force simp: uncurry_def)
  have 3: \<open>\<langle>Id\<rangle>list_rel O \<langle>R\<rangle>list_rel = \<langle>R\<rangle>list_rel\<close>
    by simp
  show ?thesis
    using 2[FCOMP 1, unfolded 3] .
qed

lemma is_in_arl_code_op_list_contains[sepref_fr_rules]:
  \<open>(uncurry is_in_arl_code, uncurry (RETURN oo op_list_contains)) \<in>
    nat_lit_assn\<^sup>k *\<^sub>a (arl_assn nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(uncurry is_in_arl, uncurry (RETURN oo op_list_contains)) \<in>
   Id \<times>\<^sub>r (\<langle>Id\<rangle>list_rel) \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle> nres_rel\<close>
    by (rule is_in_arl_op_list_contains) (auto simp: IS_LEFT_UNIQUE_def)
  have 2: \<open>hr_comp (arl_assn nat_lit_assn) (\<langle>Id\<rangle>list_rel) = arl_assn nat_lit_assn\<close>
    by (auto)
  show ?thesis
    using is_in_arl_code.refine[FCOMP 1] unfolding 2 .
qed

sepref_definition union_mset_list_fold_code
  is \<open>uncurry (RETURN oo union_mset_list_fold)\<close>
  :: \<open>(arl_assn nat_lit_assn)\<^sup>d *\<^sub>a (arl_assn nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a arl_assn nat_lit_assn\<close>
  unfolding union_mset_list_fold_def
  by sepref


lemma union_mset_list_fold_op_union_mset:
  \<open>(uncurry (RETURN oo union_mset_list_fold), uncurry (RETURN oo op \<union>#)) \<in>
   [\<lambda>(a, b). distinct_mset a \<and> distinct_mset b]\<^sub>flist_mset_rel \<times>\<^sub>r list_mset_rel \<rightarrow> \<langle>list_mset_rel\<rangle> nres_rel\<close>
  by (auto simp: list_mset_rel_def br_def intro!: union_mset_list_fold_union_mset[symmetric]
      intro!: frefI nres_relI)

lemma union_mset_list_fold_code_op_union_mset[sepref_fr_rules]:
  \<open>(uncurry union_mset_list_fold_code, uncurry (RETURN oo op \<union>#)) \<in>
   [\<lambda>(a, b). distinct_mset a \<and> distinct_mset b]\<^sub>a conflict_assn\<^sup>d *\<^sub>a conflict_assn\<^sup>k \<rightarrow> conflict_assn\<close>
  using union_mset_list_fold_code.refine[FCOMP union_mset_list_fold_op_union_mset] .

lemma arl_is_empty_is_empty[sepref_fr_rules]: \<open>(arl_is_empty, RETURN o Multiset.is_empty) \<in> conflict_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: Multiset.is_empty_def hr_comp_def list_mset_rel_def br_def arl_assn_def)

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

lemma find_decomp_wl_code_find_decomp_wl:
  assumes D: \<open>D \<noteq> None\<close> \<open>D \<noteq> Some {#}\<close> and M\<^sub>0: \<open>M\<^sub>0 \<noteq> []\<close> and ex_decomp: \<open>ex_decomp_of_max_lvl M\<^sub>0 D L\<close> and
    L: \<open>L = lit_of (hd M\<^sub>0)\<close> and
    no_r: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    no_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W))\<close> and
    E: \<open>E = the D\<close>
  shows
   \<open>find_decomp_wl_imp M\<^sub>0 E L \<le> find_decomp_wl (M\<^sub>0, N, U, D, NP, UP, Q, WS) L\<close>
proof -
  define f where
    \<open>f M\<^sub>0 D L \<equiv> (\<lambda>M\<^sub>0 D L. do {
       let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) D);
       let k = count_decided M\<^sub>0;
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
         (k, M\<^sub>0)}) M\<^sub>0 D L\<close> for M\<^sub>0 :: "(nat, nat) ann_lits" and D :: "nat clause" and L :: "nat literal"
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>'a list\<close>
    by (metis append.assoc append_Cons append_Nil list.exhaust list.sel(3) tl_Nil)
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2
  have [iff]: \<open>convert_lits_l N M = [] \<longleftrightarrow> M = []\<close> for M
    by (cases M) auto
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have dist_D: \<open>distinct_mset (the D)\<close>
    using D dist by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)

  have M\<^sub>0_CNot_D: \<open>M\<^sub>0 \<Turnstile>as CNot (the D)\<close>
    using D confl by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
  have \<open>atm_of L \<notin> atms_of (remove1_mset (- L) (the D))\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>-L \<notin># remove1_mset (- L) (the D)\<close>
      using dist_D by (meson distinct_mem_diff_mset multi_member_last)
    ultimately have \<open>L \<in># the D\<close>
      using D by (auto simp: atms_of_def atm_of_eq_atm_of dest: in_diffD)

    then have \<open>-L \<in> lits_of_l M\<^sub>0\<close>
      using M\<^sub>0_CNot_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then show False
      using n_d L M\<^sub>0 by (cases M\<^sub>0) (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  qed
  moreover have \<open>L \<in> set (N!C)\<close> if \<open> hd M\<^sub>0 = Propagated L C\<close> and \<open>C > 0\<close> for C
    using confl D M\<^sub>0 L that
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases M\<^sub>0; cases \<open>hd M\<^sub>0\<close>) (auto 5 5 simp: cdcl\<^sub>W_restart_mset_state
        split: if_splits)
  ultimately have \<open>count_decided M\<^sub>0 \<noteq> get_maximum_level M\<^sub>0 (remove1_mset (- L) (the D))\<close>
    using count_decided_ge_get_maximum_level[of \<open>tl M\<^sub>0\<close> \<open>remove1_mset (- L) (the D)\<close>]
    using no_r no_s M\<^sub>0 L D get_maximum_level_convert_lits_l[of N M\<^sub>0]
    by (cases M\<^sub>0; cases \<open>hd M\<^sub>0\<close>)
      (auto 5 5 simp: cdcl\<^sub>W_restart_mset.resolve.simps cdcl\<^sub>W_restart_mset.skip.simps
        cdcl\<^sub>W_restart_mset_state split: if_splits)
  then have count_max: \<open>count_decided M\<^sub>0 > get_maximum_level M\<^sub>0 (remove1_mset (- L) (the D))\<close>
    using count_decided_ge_get_maximum_level[of M\<^sub>0 \<open>remove1_mset (- L) (the D)\<close>]
    by linarith
  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto
  have H: \<open>f M\<^sub>0 (the D) L \<le> SPEC (\<lambda>(_, M1). \<exists>K M2. (Decided K # M1, M2)
                                       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
                                       get_level M\<^sub>0 K =
                                       get_maximum_level M\<^sub>0
                                        (remove1_mset (- L) (the D)) +
                                       1)\<close>
    unfolding f_def Let_def
    apply (refine_rcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M). length M)\<close>])
    subgoal by simp
    subgoal by auto
    subgoal using M\<^sub>0 by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal
      using ex_decomp count_max
      by (auto simp: count_decided_butlast butlast_nil_iff eq_commute[of \<open>[_]\<close>] ex_decomp_of_max_lvl_def
          intro: butlast)
    subgoal for s D M'
      apply clarsimp
      apply (intro conjI impI)
      subgoal
        apply (cases M')
          by (auto intro: butlast count_decided_tl_if)
      subgoal by (auto simp: count_decided_butlast count_decided_tl_if)[]
      subgoal by (cases M') (auto simp: count_decided_ge_get_maximum_level)
      subgoal by (cases M') (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
      subgoal by (cases M') (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] last_conv_nth H intro: butlast
          cong: if_cong split: if_splits)
      subgoal by (cases M') auto
      done
    subgoal for s D M
      using count_max
      apply (auto simp: count_decided_ge_get_maximum_level ex_decomp_get_ann_decomposition_iff
          get_lev_last)
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append)
        apply (metis append_butlast_last_id count_decided_nil neq0_conv)
       defer
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append snoc_eq_iff_butlast' count_decided_ge_get_maximum_level
          ex_decomp_get_ann_decomposition_iff get_lev_last)
      done
    done
  have find_decomp_wl_code: \<open>find_decomp_wl_imp M\<^sub>0 D L = do {(_, j) \<leftarrow> f M\<^sub>0 D L; RETURN j}\<close> for L D M\<^sub>0
    unfolding find_decomp_wl_imp_def f_def by (auto simp: Let_def)
  show ?thesis
    using H unfolding find_decomp_wl_def find_decomp_wl_code E
    by refine_vcg auto
qed

definition find_decomp_wl'  where
  \<open>find_decomp_wl' =
     (\<lambda>(M::(nat, nat) ann_lits) (N::nat clauses_l) (U :: nat) (D::nat clause) (
         NP::nat clauses) (UP::nat clauses) (Q::nat lit_queue_wl) (W::(nat literal \<Rightarrow> watched)) (
     L::nat literal). SPEC(\<lambda>M1. \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (D - {#-L#}) + 1))\<close>

definition no_skip where
  \<open>no_skip S = (no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None S)))\<close>

definition no_resolve where
  \<open>no_resolve S = (no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None S)))\<close>

lemma find_decomp_wl'_find_decomp_wl:
  \<open>find_decomp_wl' M N U (the D) NP UP Q WS L = find_decomp_wl (M, N, U, D, NP, UP, Q, WS) L\<close>
  \<open>find_decomp_wl' M N U D' NP UP Q WS L = find_decomp_wl (M, N, U, Some D', NP, UP, Q, WS) L\<close>
  by (auto simp: find_decomp_wl'_def find_decomp_wl_def)

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)
  thm frefI
lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry8 (\<lambda>M N U D NP UP Q W L. find_decomp_wl_imp M D L), uncurry8 find_decomp_wl') \<in>
  [\<lambda>((((((((M, N), U), D), NP), UP), Q), W), L). D \<noteq> {#} \<and> M \<noteq> [] \<and> ex_decomp_of_max_lvl M (Some D) L \<and>
     L = lit_of (hd M) \<and> no_resolve (M, N, U, Some D, NP, UP, Q, W) \<and>
       no_skip (M, N, U, Some D, NP, UP, Q, W) \<and>
      twl_struct_invs (twl_st_of_wl None (M, N, U, Some D, NP, UP, Q, W))]\<^sub>f
   (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding find_decomp_wl'_find_decomp_wl no_resolve_def no_skip_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S') (auto intro!: find_decomp_wl_code_find_decomp_wl)
  done

definition get_conflict_wl_is_None :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_None D)\<close>

lemma get_conflict_wl_is_None: \<open>get_conflict_wl S = None \<longleftrightarrow> get_conflict_wl_is_None S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_def split: option.splits)

lemma watched_by_nth_watched_app':
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)


context twl_array_code
begin

sepref_definition (in -) find_decomp_wl_imp_code
  is \<open>uncurry2 (find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, D), L). M \<noteq> []]\<^sub>a
         pair_nat_ann_lits_assn\<^sup>d *\<^sub>a conflict_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k
    \<rightarrow> pair_nat_ann_lits_assn\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
  supply [[goals_limit=1]]
  by sepref

lemmas find_decomp_wl_imp_code_refine[sepref_fr_rules] = find_decomp_wl_imp_code.refine

definition (in -) find_decomp_wl_imp' :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l list \<Rightarrow> nat \<Rightarrow>
    nat clause \<Rightarrow> nat clauses \<Rightarrow> nat clauses \<Rightarrow> nat lit_queue_wl \<Rightarrow>
    (nat literal \<Rightarrow> watched) \<Rightarrow> _ \<Rightarrow> (nat, nat) ann_lits nres\<close> where
  \<open>find_decomp_wl_imp' = (\<lambda>M N U D NP UP W Q L. find_decomp_wl_imp M D L)\<close>

lemma (in -) id_mset_hnr[sepref_fr_rules]:
 \<open>(arl_of_array_raa, (RETURN o mset)) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a clause_ll_assn\<^sup>d \<rightarrow> conflict_assn\<close>
  unfolding list_assn_pure_conv list_mset_assn_def the_pure_pure
  by sepref_to_hoare (sep_auto simp: list_mset_assn_def mset_rel_def rel_mset_def hr_comp_def
      rel2p_def[abs_def] p2rel_def list_mset_rel_def br_def Collect_eq_comp pure_def list_rel_def
      arl_of_array_raa_def array_assn_def is_array_def arl_assn_def is_array_list_def)

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_ll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_ll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def)

lemma nth_aa_watched_app[sepref_fr_rules]:
  \<open>(uncurry2 nth_aa, uncurry2 (RETURN ooo op_watched_app)) \<in>
   [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0 \<and> i < length (W L)]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_app))
  \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f p2rel lit_of_natP \<times>\<^sub>f nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0) (\<lambda>_ ((l, i), j). i < length l \<and> j < length_ll l i)
       (\<lambda>_. True)]\<^sub>a hrp_comp ((arrayO_assn (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                       (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f p2rel lit_of_natP \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF nth_aa_hnr nth_ll_watched_app, OF P]
    unfolding op_watched_app_def .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (fastforce simp: comp_PRE_def prod_rel_def_internal relAPP_def map_fun_rel_def[abs_def]
        p2rel_def lit_of_natP_def literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def nat_lit_rel_def p2rel_def
        nat_lit_rel_def hr_comp_pure)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 op_watched_app_def .
qed

lemma length_aa_length_ll_f[sepref_fr_rules]:
  \<open>(uncurry length_aa, uncurry (RETURN oo length_ll_f)) \<in>
   [\<lambda>(W, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry length_aa, uncurry (RETURN \<circ>\<circ> length_ll_f))
       \<in> [comp_PRE
            (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel)
            (\<lambda>(W, L). L \<in> snd ` D\<^sub>0)
            (\<lambda>_ (xs, i). i < length xs)
            (\<lambda>_. True)]\<^sub>a hrp_comp
                            ((arrayO_assn (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                            (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<rightarrow>
          hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_aa_hnr length_ll_length_ll_f]
    unfolding op_watched_app_def .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (fastforce simp: comp_PRE_def prod_rel_def_internal relAPP_def map_fun_rel_def[abs_def]
        p2rel_def lit_of_natP_def literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
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

thm delete_index_and_swap_aa_ll_hnr[to_hnr, unfolded hn_refine_def, simplified]

lemma delete_index_and_swap_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN ooo delete_index_and_swap_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0 \<and> j < length (W L)]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update))
  \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>j. i < length l \<and> j < length_ll l i) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update)
                      x))]\<^sub>a hrp_comp ((arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF delete_index_and_swap_aa_ll_hnr
        delete_index_and_swap_ll_delete_index_and_swap_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff nat_lit_rel_def)
    using even_Suc by blast
  have ba_length_a_b: \<open>ba < length (a b)\<close>
    if bN: \<open>b \<in># N\<^sub>1\<close> and
      H: \<open>\<And>aa bb. (\<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x) \<and>
          (bb, b) \<in> nat_lit_rel \<longrightarrow>
          bb < length aa \<and>
          ba < length (aa ! bb)\<close>
    for a :: \<open>nat literal \<Rightarrow> nat list\<close> and b :: \<open>nat literal\<close> and ba :: nat
  proof -
    obtain aa where
      aa: \<open>\<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x\<close>
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
    2: \<open>hrp_comp (nat_assn\<^sup>k) nat_lit_rel = nat_lit_assn\<^sup>k\<close>
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
  \<open>(uncurry2 (RETURN ooo append_ll), uncurry2 (RETURN ooo append_update))
  \<in>  [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f
     \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update' append_update_def nat_lit_rel_def nat_lit_rel_def br_def
      simp del: literal_of_nat.simps)

lemma append_el_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 append_el_aa, uncurry2 (RETURN ooo append_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 append_el_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> append_update))
  \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0) (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>x. i < length l) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> append_update)
                      x))]\<^sub>a hrp_comp ((arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>f nat_lit_rel \<times>\<^sub>f nat_rel) \<rightarrow> hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
     \<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF append_aa_hnr
        append_ll_append_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff nat_lit_rel_def)
    using even_Suc by blast

  have pre: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def map_fun_rel_def lit_of_natP_def image_image
        Pos_div2_iff Neg_div2_iff all_conj_distrib length_ll_def
        intro!: ext split: if_splits)
    by (auto simp: p2rel_def lit_of_natP_def nat_lit_rel_def br_def nat_lit_rel_def
        split: if_splits)

  have
    1: \<open>hrp_comp (nat_assn\<^sup>k) nat_rel = nat_assn\<^sup>k\<close> and
    2: \<open>hrp_comp (nat_assn\<^sup>k) nat_lit_rel = nat_lit_assn\<^sup>k\<close>
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

lemma list_assn_list_mset_rel_eq_list_mset_assn:
  assumes p: \<open>is_pure R\<close>
  shows \<open>hr_comp (list_assn R) list_mset_rel = list_mset_assn R\<close>
proof -
  define R' where \<open>R' = the_pure R\<close>
  then have R: \<open>R = pure R'\<close>
    using p by auto
  show ?thesis
    apply (auto simp: list_mset_assn_def
        list_assn_pure_conv
        relcomp.simps hr_comp_pure mset_rel_def br_def
        p2rel_def rel2p_def[abs_def] rel_mset_def R list_mset_rel_def list_rel_def)
      using list_all2_reorder_left_invariance by fastforce
qed

lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)"]
  CN_FALSEI[of is_pure "twl_st_l_assn"]

definition get_conflict_wl_is_Nil :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W). D \<noteq> None \<and> Multiset.is_empty (the D))\<close>

definition get_conflict_wll_is_Nil :: \<open>nat twl_st_wl \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>

definition (in -)the_is_empty where
  \<open>the_is_empty D = Multiset.is_empty (the D)\<close>

lemma get_conflict_wll_is_Nil_get_conflict_wl_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil, RETURN o get_conflict_wl_is_Nil) \<in>
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI) (auto simp: get_conflict_wll_is_Nil_def get_conflict_wl_is_Nil_def
      split: option.splits)

lemma
  Nil_list_mset_rel_iff:
    \<open>([], aaa) \<in> list_mset_rel \<longleftrightarrow> aaa = {#}\<close> and
  empty_list_mset_rel_iff:
    \<open>(a, {#}) \<in> list_mset_rel \<longleftrightarrow> a = []\<close>
  by (auto simp: list_mset_rel_def br_def)

text \<open>The important point in the following theorem is the \<^term>\<open>hfkeep\<close>.\<close>
lemma (in -) the_is_empty[sepref_fr_rules]:
  \<open>((arl_is_empty o the), RETURN o the_is_empty) \<in> [\<lambda>D. D \<noteq> None]\<^sub>a (conflict_option_assn)\<^sup>k \<rightarrow> bool_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x)
   apply simp
  apply (case_tac xi)
   apply (simp add: hn_ctxt_def)
  apply (sep_auto simp: hn_ctxt_def invalidate_clone' vassn_tagI invalid_assn_const
      arl_is_empty_def the_is_empty_def Multiset.is_empty_def
      hr_comp_def arl_assn_def is_array_list_def list_mset_rel_def
      br_def)
  done

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

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>L::ann_lit_wl. (fst L, the (snd L))), RETURN o lit_and_ann_of_propagated) \<in>
   [\<lambda>L. \<not>is_decided L]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> (nat_lit_assn *assn nat_assn)\<close>
  apply sepref_to_hoare
  apply (rename_tac x x')
  apply (case_tac x)
  by (sep_auto simp: nat_ann_lit_rel_def p2rel_def lit_of_natP_def
      Propagated_eq_ann_lit_of_pair_iff nat_lit_rel_def  Collect_eq_comp
      br_def Collect_eq_comp nat_lit_rel_def
      simp del: literal_of_nat.simps)+

definition op_mset_arl_empty :: "'a multiset" where
  \<open>op_mset_arl_empty = {#}\<close>

lemma arl_empty_op_mset_arl_empy[sepref_fr_rules]:
  \<open>(uncurry0 arl_empty, uncurry0 (RETURN op_mset_arl_empty)) \<in>
  unit_assn\<^sup>k \<rightarrow>\<^sub>a conflict_assn\<close>
  by sepref_to_hoare
    (use lms_empty_aref in \<open>sep_auto simp: op_mset_arl_empty_def hr_comp_def arl_assn_def\<close>)

text \<open>TODO move upper\<close>
lemma (in -) id_list_of_mset[sepref_fr_rules]:
  \<open>(return o id, list_of_mset) \<in> conflict_assn\<^sup>d \<rightarrow>\<^sub>a arl_assn nat_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: hr_comp_def list_of_mset_def arl_assn_def list_mset_rel_def
      br_def)

definition (in -) find_lit_of_max_level_wl_imp where
  \<open>find_lit_of_max_level_wl_imp M D L = do {
      let k = maximum_level_remove M D (-L);
      j \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>i. i < length D \<and> (\<forall>j<i. D!j \<noteq> -L \<longrightarrow> get_level M (D!j) \<noteq> k)\<^esup>
        (\<lambda>i. D!i \<noteq> -L \<longrightarrow> get_level M (D!i) \<noteq> k)
        (\<lambda>i. RETURN (i+1))
        0;
      ASSERT(j < length D);
      RETURN (D!j)
  }\<close>
term maximum_level_remove_code
sepref_definition (in -) maximum_level_remove_code_array
  is \<open>uncurry2 (RETURN ooo maximum_level_remove)\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a (array_assn nat_lit_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_remove_def[abs_def]
  by sepref

declare (in -) maximum_level_remove_code_array.refine[sepref_fr_rules]
declare (in -) maximum_level_remove_code.refine[sepref_fr_rules]

definition find_lit_of_max_level_wl_imp' where
  \<open>find_lit_of_max_level_wl_imp' M N U D NP UP WS Q L = find_lit_of_max_level_wl_imp M D L\<close>


text \<open>TODO: share with simpel impelemtation\<close>
lemma in_remove1_msetI: \<open>x \<noteq> a \<Longrightarrow> x \<in># M \<Longrightarrow> x \<in># remove1_mset a M\<close>
  by (simp add: in_remove1_mset_neq)

definition (in -) remove1_and_add_first :: "nat literal \<Rightarrow> nat literal \<Rightarrow> nat literal list \<Rightarrow> nat literal list nres" where
  \<open>remove1_and_add_first L L' D = do {
      let i = index D L;
      let j = index D L';
      ASSERT(pre_list_swap ((D, 0), i));
      let D = swap D 0 i;
      let j = (if j = 0 then i else j);
      let one = 1;
      ASSERT(pre_list_swap ((D, one), j));
      RETURN (swap D one j)
   }
   \<close>

lemma (in -)find_first_eq_code_index[sepref_fr_rules]:
  \<open>(uncurry (\<lambda>xs a. find_first_eq_code a xs), uncurry (RETURN oo op_list_index)) \<in>
      (arl_assn nat_lit_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
proof -
  have 0: \<open>(uncurry (\<lambda>xs a. find_first_eq_code a xs), uncurry (\<lambda>xs a. find_first_eq a xs))
  \<in> (arl_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
    using find_first_eq_code.refine by (sep_auto simp: hfref_def ac_simps)
  have 1: \<open>(uncurry (\<lambda>xs a. find_first_eq a xs), uncurry (RETURN oo index)) \<in>
        \<langle>nat_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (auto simp: find_first_eq_index[simplified])
  have \<open>list_all2 (\<lambda>x x'. (x, x') \<in> nat_lit_rel) a aa \<Longrightarrow>
       (b, ba) \<in> nat_lit_rel \<Longrightarrow> find_index (\<lambda>x. x = b) a = find_index (\<lambda>x. x = ba) aa\<close> for a aa b ba
    by (induction a aa rule: list_all2_induct)
      (auto dest: lit_of_natP_same_rightD lit_of_natP_same_leftD p2relD simp: nat_lit_rel_def)
  then have 2: \<open>(uncurry (RETURN oo index), uncurry (RETURN oo index)) \<in>
        \<langle>nat_lit_rel\<rangle> list_rel \<times>\<^sub>r nat_lit_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (auto simp: index_def list_rel_def)
  have 3: \<open>(hr_comp (hr_comp (arl_assn nat_assn) (\<langle>nat_rel\<rangle>list_rel)) (\<langle>nat_lit_rel\<rangle>list_rel)) =
   arl_assn nat_lit_assn\<close>
    by (simp add: hr_comp_assoc list_rel_compp nat_lit_rel_def arl_assn_def)

  show ?thesis
    using 0[FCOMP 1, FCOMP 2] unfolding 3 by simp
qed

sepref_definition (in -)remove1_and_add_first_code
  is \<open>uncurry2 (remove1_and_add_first)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a (arl_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a (arl_assn nat_lit_assn)\<close>
  unfolding remove1_and_add_first_def
  by sepref

lemma (in -)remove1_and_add_first_code_list_of_mset2[sepref_fr_rules]:
  \<open>(uncurry2 remove1_and_add_first_code, uncurry2 (list_of_mset2))
  \<in> [\<lambda>((L, L'), D). L \<in># D \<and> L' \<in># D \<and> L \<noteq> L' \<and> distinct_mset D]\<^sub>a
     nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow> arl_assn nat_lit_assn\<close>
  (is \<open>_ \<in> [?P]\<^sub>a _ \<rightarrow> _\<close>)
proof -
  have \<open>aa \<in> set ba \<Longrightarrow>
       bb \<in> set ba \<Longrightarrow>
       aa \<noteq> bb \<Longrightarrow> distinct ba \<Longrightarrow> remove1_and_add_first aa bb ba \<le> list_of_mset2 aa bb (mset ba)\<close>
    for aa ba bb
    unfolding remove1_and_add_first_def list_of_mset2_def
    apply refine_vcg
    subgoal by auto
    subgoal by (cases ba) auto
    subgoal
      by auto
    subgoal
      by (cases ba) auto
    subgoal
      by (cases ba) auto
    done
  then have 1: \<open>(uncurry2 (remove1_and_add_first), uncurry2 (list_of_mset2)) \<in> [?P]\<^sub>f
       (Id \<times>\<^sub>r Id) \<times>\<^sub>r list_mset_rel \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
    by (intro nres_relI frefI) (auto simp: list_mset_rel_def br_def)

  show ?thesis
    using remove1_and_add_first_code.refine[FCOMP 1] .
qed

lemma [sepref_fr_rules]: \<open>(arl_length, RETURN o size) \<in> conflict_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: hr_comp_def arl_assn_def list_mset_rel_def br_def list_rel_def
      dest: list_all2_lengthD)

lemma length_a_hnr[sepref_fr_rules]: \<open>(length_a, RETURN o op_list_length) \<in> (arrayO_assn R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

definition (in -) single_of_mset_imp :: \<open>'a list \<Rightarrow> 'a nres\<close> where
  \<open>single_of_mset_imp D = do{ASSERT (D \<noteq> []); RETURN (D!0)}\<close>

sepref_definition(in -) single_of_mset_imp_code
  is \<open>single_of_mset_imp\<close>
  :: \<open>(arl_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a nat_lit_assn\<close>
  unfolding single_of_mset_imp_def
  by sepref

lemma (in -)single_of_mset_imp_code_single_of_mset[sepref_fr_rules]:
  \<open>(single_of_mset_imp_code, single_of_mset) \<in> [\<lambda>D. D \<noteq> {#} \<and> size D \<le> 1]\<^sub>a
     conflict_assn\<^sup>d \<rightarrow> nat_lit_assn\<close>
proof -
  have 1: \<open>(single_of_mset_imp, single_of_mset) \<in> [\<lambda>D. D \<noteq> {#} \<and> size D \<le> 1]\<^sub>f list_mset_rel \<rightarrow>
      \<langle>Id\<rangle> nres_rel\<close>
    apply (intro frefI nres_relI)
    by (rename_tac x, case_tac x)
      (auto simp: single_of_mset_def single_of_mset_imp_def list_mset_rel_def br_def
        intro!: frefI nres_relI)
  show ?thesis
    using single_of_mset_imp_code.refine[FCOMP 1] by simp
qed

definition find_unassigned_lit_wl_D :: \<open>_\<close> where
  \<open>find_unassigned_lit_wl_D = (\<lambda>(M, N, U, D, NP, UP, WS, Q). do {
    S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, xs). (\<exists>ys. N\<^sub>0' = ys @ xs \<and>
            (brk = None \<longrightarrow> (\<forall>L \<in> set ys. defined_lit M L)) \<and>
            (brk \<noteq> None \<longrightarrow> undefined_lit M (the brk) \<and> the brk = last ys \<and> ys \<noteq> []))\<^esup>
      (\<lambda>(brk, xs). is_None brk \<and> xs \<noteq> [])
      (\<lambda>(_, xs). do {
         ASSERT(xs \<noteq> []);
         ASSERT(no_dup M);
         RETURN (if is_None(valued M (hd xs)) then Some (hd xs) else None, tl xs)
        })
      (None, N\<^sub>0');
    RETURN (fst S)
   }
   )\<close>

sepref_register N\<^sub>0'
declare N_hnr'[sepref_fr_rules]

lemma N_hnr[sepref_import_param]: "(N\<^sub>0,N\<^sub>0')\<in>\<langle>nat_lit_rel\<rangle>list_rel"
  unfolding N\<^sub>0'_def
  by (auto simp del: literal_of_nat.simps simp: p2rel_def lit_of_natP_def
      nat_lit_rel_def  nat_lit_rel_def br_def Collect_eq_comp
      list_rel_def list_all2_op_eq_map_right_iff)


lemma set_mset_lits_of_atms_of_mm_atms_of_ms_iff:
  \<open>set_mset (lits_of_atms_of_mm A) = set_mset N\<^sub>1 \<longleftrightarrow> atms_of_ms (set_mset A) = atms_of N\<^sub>1\<close>
  apply (auto simp: atms_of_s_def in_lits_of_atms_of_mm_ain_atms_of_iff atms_of_ms_def
      atms_of_def atm_of_eq_atm_of in_N\<^sub>1_iff)
  apply (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff in_implies_atm_of_on_atms_of_ms)
  done -- \<open>TODO tune proof\<close>

lemma Ball_mset_add: \<open>Multiset.Ball (M + N) P \<longleftrightarrow> Multiset.Ball M P \<and> Multiset.Ball N P\<close>
  by auto

lemma find_unassigned_lit_wl_D_find_unassigned_lit_wl:
  \<open>(find_unassigned_lit_wl_D, find_unassigned_lit_wl) \<in>
  [\<lambda>S. literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of_wl None S) \<and>
    get_conflict_wl S = None]\<^sub>f
  Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle>nres_rel\<close>
proof -
  have le_minus_iff: \<open>(a::nat) \<le> a - Suc b \<longleftrightarrow> a = 0\<close> for a b
    by auto
  have le_Down_option_rel[iff]: \<open>S \<le> \<Down> (\<langle>Id\<rangle>option_rel) T \<longleftrightarrow> S\<le>T\<close> for S T :: \<open>'a option nres\<close>
    by auto
  have [simp]: \<open>valued M L = None \<longleftrightarrow> undefined_lit M L\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    and L :: \<open>nat literal\<close>
    by (auto simp: valued_def)
  have H: \<open>defined_lit M L\<close> if \<open>valued M L = Some x\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    and L :: \<open>nat literal\<close> and x
    using that
    by (auto simp: valued_def Decided_Propagated_in_iff_in_lits_of_l
        split: option.splits if_splits)
  show ?thesis
    apply (intro nres_relI frefI)
  apply clarify
  unfolding find_unassigned_lit_wl_D_def find_unassigned_lit_wl_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (size o snd)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by (auto split: list.splits)
  subgoal for a aa ab ac ad ae af b ag ah ai aj ak al am ba x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m s an bb
    apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv
      (state\<^sub>W_of (twl_st_of_wl None (ag, ah, ai, aj, ak, al, am, ba)))\<close>)
    subgoal by (simp add: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset_state)
    subgoal by (subst (asm)twl_struct_invs_def,
       subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def) fast
    done
  subgoal premises p for a aa ab ac ad ae af b M N U D NP UP WS Q x1 x2 x1a x2a x1b x2b x1c
       x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h x1i x2i x1j x2j x1k x2k x1l
       x2l x1m x2m s brk xs brk' xs'
  proof -
    thm p
    note lit_N\<^sub>0 = p(2) and struct_invs = p(3) and inv = p(19) and cont = p(20) and s = p(21) and
      out = p(24)
    obtain ys where
      ys: \<open>N\<^sub>0' = ys @ xs\<close> and
      brk_None: \<open>(brk = None \<longrightarrow> Ball (set ys) (defined_lit x1))\<close> and
      brk_Some: \<open>(brk \<noteq> None \<longrightarrow> undefined_lit x1 (the brk))\<close>
      using inv s by blast
    show ?thesis
      apply (rule exI[of _ \<open>ys @ [hd xs]\<close>])
      using ys cont s out brk_None by (auto split: option.splits simp: H)
  qed
  subgoal by (auto split:)
  subgoal premises p using p(1,5-) by auto
  subgoal premises p for M'' N'' U'' D'' NP'' UP'' WS'' Q'' M N U D NP UP WS Q x1 x2 x1a x2a x1b x2b x1c
    x2c x1d x2d x1e x2e x1f x2f M' x2g N' x2h U' x2i D' x2j NP' x2k UP' _ WS' Q'  s
  proof -
    thm p
    note lit_N\<^sub>0 = p(2) and struct_invs = p(3) and confl = p(4) and st = p(1,5-18) and inv = p(19) and
      cont = p(20) and s = p(21)
    have [simp]: \<open>M' = M\<close> \<open>N' = N\<close> \<open>U' = U\<close> \<open>D' = D\<close> \<open>NP' = NP\<close> \<open>UP' = UP\<close> \<open>WS' = WS\<close> \<open>Q' = Q\<close>
      \<open>x1 = M\<close> \<open>M'' = M\<close> \<open>N'' = N\<close> \<open>U'' = U\<close> \<open>D'' = D\<close> \<open>NP'' = NP\<close> \<open>UP'' = UP\<close> \<open>WS'' = WS\<close> \<open>Q'' = Q\<close>
      using st by auto
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q)))\<close> and
      unit: \<open>unit_clss_inv (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>atms_of_ms (mset ` set (tl N)) = atms_of_ms (mset ` set (take U (tl N))) \<union>
              atms_of_ms (mset ` set (drop U (tl N)))\<close>
      by (subst append_take_drop_id[of U, symmetric], subst set_append) (simp add: image_Un)
    ultimately have 0: \<open>atms_of_ms ((mset ` set (take U (tl N))) \<union> set_mset NP) =
       atms_of_ms (mset ` set (tl N) \<union> set_mset NP)\<close> and
      UP_NP: \<open>atms_of_ms (set_mset UP) \<subseteq>
       atms_of_ms (mset ` set (tl N) \<union> set_mset NP)\<close>
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset_state drop_Suc)
    have 1: \<open>mset `# mset (take U (tl N)) + NP +
             (mset `# mset (drop (Suc U) N) + UP) = mset `# mset (tl N) + NP + UP\<close>
      by (subst (2) append_take_drop_id[symmetric, of \<open>tl N\<close> U], subst mset_append)
        (simp add: drop_Suc)
    have in_N\<^sub>1: \<open>Neg x \<in># N\<^sub>1 \<longleftrightarrow> x \<in> atms_of N\<^sub>1\<close>\<open>Pos x \<in># N\<^sub>1 \<longleftrightarrow> x \<in> atms_of N\<^sub>1\<close> for x
      using in_N\<^sub>1_iff[of \<open>Neg x\<close>] in_N\<^sub>1_iff[of \<open>Pos x\<close>] by simp_all
    have tl_N_NP_N\<^sub>1: \<open>atms_of_ms (mset ` set (tl N) \<union> set_mset NP) = atms_of_s (set_mset N\<^sub>1)\<close>
      using lit_N\<^sub>0 0 UP_NP unfolding is_N\<^sub>1_def
      by (subst (asm) set_mset_lits_of_atms_of_mm_atms_of_ms_iff)
        (auto simp add: clauses_def mset_take_mset_drop_mset' in_lits_of_atms_of_mm_ain_atms_of_iff
          cdcl\<^sub>W_restart_mset_state 1 lits_of_atms_of_mm_union in_N\<^sub>1)
    let ?L = \<open>the (fst s)\<close>
    obtain brk xs where s': \<open>s = (brk, xs)\<close> by (cases s)
    obtain ys where
      ys: \<open>N\<^sub>0' = ys @ xs\<close> and
      brk_None: \<open>(brk = None \<longrightarrow> Ball (set ys) (defined_lit x1))\<close> and
      brk_Some: \<open>(brk \<noteq> None \<longrightarrow> undefined_lit x1 (the brk) \<and> the brk = last ys \<and> ys \<noteq> [])\<close>
      using inv s s' by blast
    have H: \<open>Neg (atm_of y) \<notin> ys \<Longrightarrow> Pos (atm_of y) \<notin> ys \<Longrightarrow> y \<notin> ys\<close>
      for y and ys :: \<open>nat literal set\<close>
      by (cases y) auto

    have \<open>undefined_lit M ?L\<close>
      using inv s cont by auto
    moreover have [dest!]:  \<open>\<And>C. C\<in># NP \<Longrightarrow>  \<exists>L. C = {#L#} \<and>
                (D = None \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
                (0 < count_decided M \<longrightarrow>
                 get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
      using unit by (auto simp del: set_mset_union simp: Ball_mset_add)
    ultimately have L_not_NP: \<open>atm_of ?L \<notin> atms_of_ms (set_mset NP)\<close>
      using unit confl s' s by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
          atms_of_ms_def atms_of_def atm_of_eq_atm_of)
    moreover have L_N\<^sub>0': \<open>atm_of ?L \<in> atms_of_s (set N\<^sub>0')\<close>
      using inv cont cont H[of \<open>last ys\<close> \<open>set ys\<close>] s' ys brk_Some s
      by auto
    have N\<^sub>0_N\<^sub>1: \<open>atms_of_s (set N\<^sub>0') = atms_of_s (set_mset N\<^sub>1)\<close>
      by (auto simp: N\<^sub>1_def N\<^sub>0''_def uminus_lit_swap[symmetric])
    show ?thesis
      using L_N\<^sub>0' L_not_NP unfolding N\<^sub>0_N\<^sub>1 tl_N_NP_N\<^sub>1[symmetric] 0[symmetric]
      by (simp add: mset_take_mset_drop_mset')
  qed
 subgoal premises p for M'' N'' U'' D'' NP'' UP'' WS'' Q'' M N U D NP UP WS Q x1 x2 x1a x2a x1b x2b x1c
    x2c x1d x2d x1e x2e x1f x2f M' x2g N' x2h U' x2i D' x2j NP' x2k UP' _ WS' Q'  s
  proof -
    thm p
    note lit_N\<^sub>0 = p(2) and struct_invs = p(3) and confl = p(4) and st = p(1,5-18) and inv = p(19) and
      cont = p(20) and s = p(21)
    have S[simp]: \<open>M' = M\<close> \<open>N' = N\<close> \<open>U' = U\<close> \<open>D' = D\<close> \<open>NP' = NP\<close> \<open>UP' = UP\<close> \<open>WS' = WS\<close> \<open>Q' = Q\<close>
      \<open>x1 = M\<close> \<open>M'' = M\<close> \<open>N'' = N\<close> \<open>U'' = U\<close> \<open>D'' = D\<close> \<open>NP'' = NP\<close> \<open>UP'' = UP\<close> \<open>WS'' = WS\<close> \<open>Q'' = Q\<close>
      using st by auto
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q)))\<close> and
      unit: \<open>unit_clss_inv (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>atms_of_ms (mset ` set (tl N)) = atms_of_ms (mset ` set (take U (tl N))) \<union>
              atms_of_ms (mset ` set (drop U (tl N)))\<close>
      by (subst append_take_drop_id[of U, symmetric], subst set_append) (simp add: image_Un)
    ultimately have 0: \<open>atms_of_ms ((mset ` set (take U (tl N))) \<union> set_mset NP) =
       atms_of_ms (mset ` set (tl N) \<union> set_mset NP)\<close> and
      UP_NP: \<open>atms_of_ms (set_mset UP) \<subseteq>
       atms_of_ms (mset ` set (tl N) \<union> set_mset NP)\<close>
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset_state drop_Suc)
    have 1: \<open>mset `# mset (take U (tl N)) + NP +
             (mset `# mset (drop (Suc U) N) + UP) = mset `# mset (tl N) + NP + UP\<close>
      by (subst (2) append_take_drop_id[symmetric, of \<open>tl N\<close> U], subst mset_append)
        (simp add: drop_Suc)
    have in_N\<^sub>1: \<open>Neg x \<in># N\<^sub>1 \<longleftrightarrow> x \<in> atms_of N\<^sub>1\<close>\<open>Pos x \<in># N\<^sub>1 \<longleftrightarrow> x \<in> atms_of N\<^sub>1\<close> for x
      using in_N\<^sub>1_iff[of \<open>Neg x\<close>] in_N\<^sub>1_iff[of \<open>Pos x\<close>] by simp_all
    have tl_N_NP_N\<^sub>1: \<open>atms_of_ms (mset ` set (tl N) \<union> set_mset NP) = atms_of_s (set_mset N\<^sub>1)\<close>
      using lit_N\<^sub>0 0 UP_NP unfolding is_N\<^sub>1_def
      by (subst (asm) set_mset_lits_of_atms_of_mm_atms_of_ms_iff)
        (auto simp add: clauses_def mset_take_mset_drop_mset' in_lits_of_atms_of_mm_ain_atms_of_iff
          cdcl\<^sub>W_restart_mset_state 1 lits_of_atms_of_mm_union in_N\<^sub>1)
    let ?L = \<open>the (fst s)\<close>
    obtain brk xs where s': \<open>s = (brk, xs)\<close> by (cases s)
    obtain ys where
      ys: \<open>N\<^sub>0' = ys @ xs\<close> and
      brk_None: \<open>(brk = None \<longrightarrow> Ball (set ys) (defined_lit x1))\<close> and
      brk_Some: \<open>(brk \<noteq> None \<longrightarrow> undefined_lit x1 (the brk) \<and> the brk = last ys \<and> ys \<noteq> [])\<close>
      using inv s s' by blast
    have H: \<open>Neg (atm_of y) \<notin> ys \<Longrightarrow> Pos (atm_of y) \<notin> ys \<Longrightarrow> y \<notin> ys\<close>
      for y and ys :: \<open>nat literal set\<close>
      by (cases y) auto


    have [dest!]:  \<open>\<And>C. C\<in># NP \<Longrightarrow>  \<exists>L. C = {#L#} \<and>
                (D = None \<longrightarrow> get_level M L = 0 \<and> L \<in> lits_of_l M) \<and>
                (0 < count_decided M \<longrightarrow>
                 get_level M L = 0 \<and> L \<in> lits_of_l M)\<close>
      using unit by (auto simp del: set_mset_union simp: Ball_mset_add)
    then have L_not_NP: \<open>atm_of L \<notin> atms_of_ms (set_mset NP)\<close> if \<open>undefined_lit M L\<close> for L
      using unit confl s' s that by (auto simp: Decided_Propagated_in_iff_in_lits_of_l
          atms_of_ms_def atms_of_def atm_of_eq_atm_of)
    then have H: \<open>(atm_of L \<in> atms_of_ms (mset ` set (take U (tl N)))) =
           (atm_of L \<in> atms_of_ms (mset ` set (take U (tl N)) \<union> set_mset NP))\<close> if \<open>undefined_lit M L\<close> for L
      using that by auto

    have N\<^sub>0_N\<^sub>1: \<open>atms_of_s (set N\<^sub>0') = atms_of_s (set_mset N\<^sub>1)\<close>
      by (auto simp: N\<^sub>1_def N\<^sub>0''_def uminus_lit_swap[symmetric])
    have [simp]: \<open>defined_lit M (Pos (atm_of L)) \<longleftrightarrow> defined_lit M L\<close>
         \<open>defined_lit M (Neg (atm_of L)) \<longleftrightarrow> defined_lit M L\<close> for L
      by (cases L; solves\<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l\<close>)+
    have atm: \<open>atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))) =
      atms_of_ms (mset ` set (take U (tl N)))\<close> by (simp add: mset_take_mset_drop_mset')
    show ?thesis
      unfolding S atm
      apply clarify
      apply (subst (asm)H)
       apply (solves simp)
      unfolding N\<^sub>0_N\<^sub>1[symmetric] tl_N_NP_N\<^sub>1 0
      using brk_None s' s ys cont
      by auto
  qed
  done
qed

end


definition find_first_eq_map :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> nat nres" where
  \<open>find_first_eq_map f x xs = WHILE\<^sub>T\<^bsup>\<lambda>i. i \<le> length xs\<^esup>
       (\<lambda>i. i < length xs \<and> f (xs!i) \<noteq> x)
       (\<lambda>i. RETURN (i+1))
       0\<close>

lemma find_first_eq_map_index:
  shows \<open>find_first_eq_map f x xs \<le> \<Down> nat_rel (RETURN (index (map f xs) x))\<close>
proof -
  have H:
    \<open>WHILE\<^sub>T\<^bsup>\<lambda>i. i \<le> length xs\<^esup>
       (\<lambda>i. i < length xs \<and> f (xs!i) \<noteq> x)
       (\<lambda>i. RETURN (i+1))
       k
     \<le> \<Down> nat_rel
       (RETURN (k + index (sublist (map f xs) {k..<length xs}) x))\<close>
    if \<open>k < length xs\<close> for k
    using that
  proof (cases xs)
    case Nil
    then show ?thesis using that by simp
  next
    case xs: (Cons a xs')
    have index_first: \<open>index (sublist (a # xs') {n..<Suc (length xs')}) ((a # xs') ! n) = 0\<close>
      if \<open>n < length xs'\<close> for n
      using that by (metis index_Cons length_Cons less_SucI sublist_upt_Suc)
    have [simp]: "sublist (f a # map f xs') {n..<Suc (length xs')} =
    (f a # map f xs') ! n # sublist (f a # map f xs') {Suc n..<Suc (length xs')}"
      if a2: "n < length xs'" for n -- \<open>auto is not able to derive it automatically
      because of @{thm length_Cons}\<close>
      using a2
      apply (subst length_Cons[of a, symmetric])+
      apply (subst length_map[of f \<open>a # xs'\<close>, symmetric])+
      by (metis length_Cons length_map less_SucI sublist_upt_Suc)
    have [simp]: \<open>(f a # map f xs') ! n = f ((a # xs') ! n)\<close> if \<open>n < length (a#xs')\<close> for n
      unfolding list.map[symmetric]
      by (subst nth_map) (use that in auto)

    have \<open>k < Suc (length xs')\<close>
      using that xs by auto
    then show ?thesis
      unfolding find_first_eq_def less_eq_Suc_le Suc_le_mono xs
      apply (induction rule: inc_induct)
      subgoal by (auto simp: sublist_single_if WHILEIT_unfold )[]
      subgoal by (subst WHILEIT_unfold) (auto simp: sublist_single_if index_first sublist_upt_Suc)
      done
  qed
  have [simp]: \<open>find_first_eq_map f x [] \<le> RETURN 0\<close>
    unfolding find_first_eq_map_def by (auto simp: WHILEIT_unfold)[]
  have [simp]: \<open>sublist (map f xs) {0..<length xs} = map f xs\<close>
    by (simp add: sublist_id_iff)
  show ?thesis
    apply (cases \<open>xs = []\<close>)
     apply (solves simp)
    using H[of 0] unfolding find_first_eq_map_def by simp
qed

end
