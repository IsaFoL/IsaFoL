theory CDCL_Two_Watched_Literals_List_Watched_Code
  imports CDCL_Two_Watched_Literals_List_Watched Array_Array_List
    CDCL_Two_Watched_Literals_Code_Common
begin

section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

lemma Pos_div2_iff: \<open>Pos (bb div 2) = b \<longleftrightarrow> is_pos b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close> for bb :: nat
  by (cases b) auto
lemma Neg_div2_iff: \<open>Neg (bb div 2) = b \<longleftrightarrow> is_neg b \<and> (bb = 2 * atm_of b \<or> bb = 2 * atm_of b + 1)\<close> for bb :: nat
  by (cases b) auto

text \<open>
  Modeling \<^typ>\<open>nat literal\<close> via the transformation associating \<^term>\<open>2*n\<close> or \<^term>\<open>2*n+1\<close>
  has some advantages over the transformation to positive or negative integers: 0 is not an issue.\<close>
fun nat_of_lit :: \<open>nat literal \<Rightarrow> nat\<close> where
  \<open>nat_of_lit (Pos L) = 2*L\<close>
| \<open>nat_of_lit (Neg L) = 2*L + 1\<close>

lemma nat_of_lit_def: \<open>nat_of_lit L = (if is_pos L then 2*atm_of L else 2*atm_of L + 1)\<close>
  by (cases L) auto

fun literal_of_nat :: \<open>nat \<Rightarrow> nat literal\<close> where
  \<open>literal_of_nat n = (if even n then Pos (n div 2) else Neg (n div 2))\<close>

lemma lit_of_nat_nat_of_lit[simp]: \<open>literal_of_nat (nat_of_lit L) = L\<close>
  by (cases L) auto

lemma nat_of_lit_lit_of_nat[simp]: \<open>nat_of_lit (literal_of_nat n) = n\<close>
  by auto

lemma atm_of_lit_of_nat: \<open>atm_of (literal_of_nat n) = n div 2\<close>
  by auto

text \<open>There is probably a more ``closed'' form from the following theorem, but it is unclear if
  that is useful or not.\<close>
lemma uminus_lit_of_nat:
  \<open>- (literal_of_nat n) = (if even n then literal_of_nat (n+1) else literal_of_nat (n-1))\<close>
  by (auto elim!: oddE)

definition lit_of_natP where
  \<open>lit_of_natP L L' \<longleftrightarrow> literal_of_nat L = L'\<close>

abbreviation nat_lit_rel where
  \<open>nat_lit_rel \<equiv> p2rel lit_of_natP\<close>

abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> pure nat_lit_rel\<close>

fun pair_of_ann_lit :: "('a, 'b) ann_lit \<Rightarrow> 'a literal \<times> 'b option" where
  \<open>pair_of_ann_lit (Propagated L D) = (L, Some D)\<close>
| \<open>pair_of_ann_lit (Decided L) = (L, None)\<close>

fun ann_lit_of_pair :: "'a literal \<times> 'b option \<Rightarrow> ('a, 'b) ann_lit" where
  \<open>ann_lit_of_pair (L, Some D) = Propagated L D\<close>
| \<open>ann_lit_of_pair (L, None) = Decided L\<close>

lemma ann_lit_of_pair_pair_of_ann_lit: \<open>ann_lit_of_pair (pair_of_ann_lit L) = L\<close>
  by (cases L) auto

lemma pair_of_ann_lit_ann_lit_of_pair: \<open>pair_of_ann_lit (ann_lit_of_pair L) = L\<close>
  by (cases L; cases \<open>snd L\<close>) auto

type_synonym ann_lit_wl = \<open>nat \<times> nat option\<close>
type_synonym ann_lits_wl = \<open>ann_lit_wl list\<close>

definition nat_ann_lit_rel :: "(ann_lit_wl \<times> (nat, nat) ann_lit) set" where
  \<open>nat_ann_lit_rel = ({(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat a, b)) a)})\<close>

definition nat_ann_lits_rel :: "(ann_lits_wl \<times> (nat, nat) ann_lits) set" where
  \<open>nat_ann_lits_rel = \<langle>(Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel) O nat_ann_lit_rel\<rangle>list_rel\<close>

abbreviation pair_nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> ann_lit_wl \<Rightarrow> assn" where
  \<open>pair_nat_ann_lit_assn \<equiv> pure (nat_ann_lit_rel)\<close>

abbreviation pair_nat_ann_lits_assn :: "(nat, nat) ann_lits \<Rightarrow> ann_lits_wl \<Rightarrow> assn" where
  \<open>pair_nat_ann_lits_assn \<equiv> list_assn (pair_nat_ann_lit_assn)\<close>

definition propagated where
  \<open>propagated L C = (L, Some C)\<close>

lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      lit_of_natP_def simp del: literal_of_nat.simps
      split: option.splits)

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = (if L mod 2 = 0 then L + 1 else L - 1)\<close>

lemma uminus_lit_imp_hnr[sepref_fr_rules]:
  \<open>(return o uminus_lit_imp, RETURN o uminus) \<in>
     nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: nat_ann_lit_rel_def uminus_lit_imp_def case_prod_beta p2rel_def
      lit_of_natP_def
      split: option.splits)
  by presburger

lemma literal_of_neq_eq_nat_of_lit_eq_iff: \<open>literal_of_nat b = L \<longleftrightarrow> b = nat_of_lit L\<close>
  by (auto simp del: literal_of_nat.simps)

lemma nat_of_lit_eq_iff[iff]: \<open>nat_of_lit xa = nat_of_lit x \<longleftrightarrow> x = xa\<close>
  apply (cases x; cases xa) by auto presburger+

lemma nat_ann_lits_rel_Cons[iff]:
  \<open>(x # xs, y # ys) \<in> nat_ann_lits_rel \<longleftrightarrow> (x, y) \<in> nat_ann_lit_rel \<and> (xs, ys) \<in> nat_ann_lits_rel\<close>
  by (auto simp: nat_ann_lits_rel_def)

lemma lit_of_natP_same_rightD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP bi a \<Longrightarrow> a = b\<close>
  by (auto simp: p2rel_def lit_of_natP_def)

lemma lit_of_natP_same_leftD: \<open>lit_of_natP bi b \<Longrightarrow> lit_of_natP ai b \<Longrightarrow> ai = bi\<close>
  apply (auto simp: p2rel_def lit_of_natP_def split: if_splits)
  apply presburger
  apply presburger
  done


subsection \<open>State Conversion\<close>

subsubsection \<open>Functions and Types:\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym working_queue_ll = "nat list"
type_synonym lit_queue_l = "nat list"
type_synonym nat_trail = \<open>(nat \<times> nat option) list\<close>
type_synonym clause_wl = \<open>nat array_list\<close>
type_synonym clauses_wl = \<open>nat array_list array\<close>
type_synonym unit_lits_wl = \<open>nat list list\<close>

type_synonym watched_wl = \<open>(nat array_list) array\<close>

abbreviation ann_lit_wl_assn :: \<open>ann_lit_wl \<Rightarrow> ann_lit_wl \<Rightarrow> assn\<close> where
  \<open>ann_lit_wl_assn \<equiv> prod_assn nat_assn (option_assn nat_assn)\<close>

abbreviation ann_lits_wl_assn :: \<open>ann_lits_wl \<Rightarrow> ann_lits_wl \<Rightarrow> assn\<close> where
  \<open>ann_lits_wl_assn \<equiv> list_assn ann_lit_wl_assn\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> arl_assn nat_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> clauses_wl \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> arrayO (arl_assn nat_lit_assn)\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat list list \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation working_queue_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation working_queue_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: "nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn" where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn nat_lit_assn)\<close>

abbreviation conflict_assn :: "nat clause \<Rightarrow> nat array_list \<Rightarrow> assn" where
  \<open>conflict_assn \<equiv> hr_comp clause_ll_assn list_mset_rel\<close>

abbreviation conflict_option_assn :: "nat clause option \<Rightarrow> nat array_list option \<Rightarrow> assn" where
  \<open>conflict_option_assn \<equiv> option_assn conflict_assn\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times> nat array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l \<times> watched_wl"

notation prod_assn (infixr "*assn" 90)


subsubsection \<open>Refinement of the Watched Function\<close>

definition map_fun_rel :: "(nat \<times> nat literal) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> (nat literal \<Rightarrow> 'a)) set" where
  map_fun_rel_def_internal: \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto

definition map_fun_rel_assn :: "(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>

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
   apply (simp add: valued_def valued_impl_def Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of)[]
  by (auto simp add: valued_def valued_impl_def defined_lit_map dest: in_lits_of_l_defined_litD)

lemma hrp_comp_Id2[simp]: \<open>hrp_comp A Id = A\<close>
  unfolding hrp_comp_def
  by auto

lemma valued_impl_spec:
  shows \<open>(uncurry valued_impl, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). no_dup M]\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding fref_def nres_rel_def
  by (auto simp: valued_impl_valued IS_ID_def)

lemma atm_of_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>n. n div 2), RETURN o op_atm_of) \<in> (pure nat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def lit_of_natP_def)
thm Abs_assn_inverse nth_rule

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> (pure nat_ann_lit_rel)\<^sup>k \<rightarrow>\<^sub>a (pure nat_lit_rel)\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def
      split: if_splits)
   apply (case_tac b)
    apply auto[2]
  apply (case_tac b)
   apply (auto
      elim!: run_elims
      simp: hoare_triple_def snga_assn_def
      Let_def Let_def new_addrs_def relH_def in_range.simps  mod_emp
      )
  done

lemma op_eq_op_nat_lit_eq[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo op_nat_lit_eq)) \<in>
    (pure nat_lit_rel)\<^sup>k *\<^sub>a (pure nat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: p2rel_def nat_ann_lit_rel_def lit_of_natP_def
      split: if_splits)
   apply (auto
      elim!: run_elims
      simp: hoare_triple_def snga_assn_def
      Let_def Let_def new_addrs_def relH_def in_range.simps  mod_emp
      )
    apply presburger
  apply presburger
  done

sepref_definition valued_impl' is \<open>uncurry valued_impl\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_impl_def Let_def
  by sepref

lemma valued_impl'[sepref_fr_rules]: \<open>(uncurry valued_impl', uncurry (RETURN oo valued)) \<in>
   [\<lambda>(a, b). no_dup a]\<^sub>a pair_nat_ann_lits_assn\<^sup>k *\<^sub>a (pure nat_lit_rel)\<^sup>k \<rightarrow> option_assn bool_assn\<close>
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
     \<in> [\<lambda>((l,i), j). i < length l \<and> j < length_ll l i]\<^sub>a (arrayO (arl_assn R))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
         \<rightarrow> (arrayO (arl_assn R))\<close>
  using assms unfolding delete_index_and_swap_aa_def
  by sepref_to_hoare (sep_auto dest: le_length_ll_nemptyD
      simp: delete_index_and_swap_ll_def update_ll_def last_ll_def set_butlast_ll_def
      length_ll_def[symmetric])
no_notation Ref.update ("_ := _" 62)


definition find_unwatched' :: "(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> (bool option \<times> nat) nres" where
\<open>find_unwatched' M N' C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length (N'!C) \<and> (\<forall>j\<in>{2..<i}. -((N'!C)!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M ((N'!C)!i) \<and> i < length (N'!C))) \<and>
    (found = Some True \<longrightarrow> ((N'!C)!i \<in> lits_of_l M \<and> i < length (N'!C)))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length (N'!C))
    (\<lambda>(_, i). do {
      ASSERT(i < length (N'!C));
      case valued M ((N'!C)!i) of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some True, i)} else do { RETURN (None, i+1)})
      }
    )
    (None, 2::nat)
  }
\<close>

lemma find_unwatched'_find_unwatched: \<open>find_unwatched' M N' C = find_unwatched M (N'!C)\<close>
  unfolding find_unwatched'_def find_unwatched_def
  by auto

sepref_definition find_unwatched'_impl
  is \<open>uncurry2 find_unwatched'\<close>
  :: \<open>[\<lambda>((M, N'), C). no_dup M \<and> C < length N']\<^sub>a pair_nat_ann_lits_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn bool_assn *assn nat_assn\<close>
  unfolding find_unwatched'_def nth_ll_def[symmetric] length_ll_def[symmetric]
    supply [[goals_limit=1]]
  by sepref

declare find_unwatched'_impl.refine[sepref_fr_rules]


subsection \<open>Refinement\<close>

text \<open>We start in a context where we have an initial set of literals. It should be
  a context, but this is not compatible with the refinement framework. It does only appear in
  the specifications.\<close>
locale twl_array_code =
  fixes N\<^sub>0 :: \<open>nat literal multiset\<close>
begin

text \<open>This is the \<^emph>\<open>completion\<close> of \<^term>\<open>N\<^sub>0\<close>, containing the positive and the negation of every
  literal of \<^term>\<open>N\<^sub>0\<close>:\<close>
definition N\<^sub>1 where \<open>N\<^sub>1 = N\<^sub>0 + uminus `# N\<^sub>0\<close>

abbreviation D\<^sub>0 :: \<open>(nat \<times> nat literal) set\<close> where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset N\<^sub>1\<close>

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_ll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_ll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def)

definition length_ll_f where
  \<open>length_ll_f W L = length (W L)\<close>

lemma length_ll_length_ll_f:
  \<open>(uncurry (RETURN oo length_ll), uncurry (RETURN oo length_ll_f)) \<in>
     [\<lambda>(W, L). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r p2rel lit_of_natP) \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding length_ll_def length_ll_f_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def lit_of_natP_def)

abbreviation array_watched_assn :: "(nat literal \<Rightarrow> nat list) \<Rightarrow> (nat array_list) array \<Rightarrow> assn" where
  \<open>array_watched_assn \<equiv> hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)\<close>

definition twl_st_l_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll \<Rightarrow> assn\<close> where
\<open>twl_st_l_assn \<equiv>
  (pair_nat_ann_lits_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  unit_lits_assn *assn
  unit_lits_assn *assn
  clause_l_assn *assn
  array_watched_assn
  )\<close>

lemma ex_list_watched:
  fixes W :: \<open>nat literal \<Rightarrow> nat list\<close>
  shows \<open>\<exists>aa. \<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = W x\<close>
  (is \<open>\<exists>aa. ?P aa\<close>)
proof -
  define D' where \<open>D' = D\<^sub>0\<close>
  define N\<^sub>1' where \<open>N\<^sub>1' = N\<^sub>1\<close>
  define D'' where \<open>D'' = mset_set (snd ` D')\<close>
  let ?f = \<open>(\<lambda>L a. a[nat_of_lit L:= W L])\<close>
  interpret comp_fun_commute ?f
    apply standard
    apply (case_tac \<open>y = x\<close>)
     apply (solves simp)
    apply (intro ext)
    apply (subst (asm) lit_of_nat_nat_of_lit[symmetric])
    apply (subst (asm)(3) lit_of_nat_nat_of_lit[symmetric])
    apply (clarsimp simp only: comp_def intro!: list_update_swap)
    done
  define aa where
    \<open>aa \<equiv> fold_mset ?f (replicate (1+Max (nat_of_lit ` snd ` D')) []) (mset_set (snd ` D'))\<close>
  have length_fold: \<open>length (fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l M) = length l\<close> for l M
    by (induction M) auto
  have length_aa: \<open>length aa = Suc (Max (nat_of_lit ` snd ` D'))\<close>
    unfolding aa_def D''_def[symmetric] by (simp add: length_fold)
  have H: \<open>x \<in># N\<^sub>1 \<Longrightarrow>
      length l \<ge> Suc (Max (nat_of_lit ` set_mset N\<^sub>1)) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset N\<^sub>1) ! nat_of_lit x = W x\<close>
    for x l
    unfolding N\<^sub>1'_def[symmetric]
    apply (induction N\<^sub>1' arbitrary: l)
    subgoal by simp
    subgoal for xa Ls l
      apply (case_tac \<open>(nat_of_lit ` set_mset Ls) = {}\<close>)
       apply (solves simp)
      apply (auto simp: nth_list_update_neq less_Suc_eq_le length_fold)
      apply (subst nth_list_update_neq)
       apply (auto simp: less_Suc_eq_le Max.insert)[]
      apply (auto simp: less_Suc_eq_le)[]
      done
    done
  have H': \<open>aa ! nat_of_lit x = W x\<close> if \<open>x \<in># N\<^sub>1\<close> for x
    using that unfolding aa_def D'_def
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le intro!: H)
  have \<open>?P aa\<close>
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le length_aa H')
  then show ?thesis
    by blast
qed

lemma nth_aa_watched_app[sepref_fr_rules]:
  \<open>(uncurry2 nth_aa, uncurry2 (RETURN ooo op_watched_app)) \<in>
   [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0 \<and> i < length (W L)]\<^sub>a
     array_watched_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> op_watched_app))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((l, i), j). i < length l \<and> j < length_ll l i)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                       ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel) \<rightarrow>
                    hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF nth_aa_hnr nth_ll_watched_app, OF P]
    unfolding op_watched_app_def .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    apply (auto simp: comp_PRE_def intro!: ext simp: prod_rel_def_internal
        relAPP_def map_fun_rel_def[abs_def] p2rel_def lit_of_natP_def
        literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        simp del: literal_of_nat.simps)
      done

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp
    by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3  .
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
                            ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                            (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<rightarrow>
          hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_aa_hnr length_ll_length_ll_f]
    unfolding op_watched_app_def .

  have 1: \<open>?pre' = ?pre\<close>
    using ex_list_watched
    by (auto simp: comp_PRE_def intro!: ext simp: prod_rel_def_internal
        relAPP_def map_fun_rel_def[abs_def] p2rel_def lit_of_natP_def
        literal_of_neq_eq_nat_of_lit_eq_iff length_ll_def
        simp del: literal_of_nat.simps)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp
    by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3  .
qed

text \<open>
  \<^item> TODO: use \<open>let L = K\<close> instead of \<open>let L = ((N!C)) ! i\<close>.\<close>
definition unit_propagation_inner_loop_body_wl_D :: "nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl_D K w S = do {
    let (M, N, U, D', NP, UP, Q, W) = S;
    ASSERT(K \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
    ASSERT(w < length (watched_by S K));
    ASSERT(K \<in> snd ` D\<^sub>0);
    let C = (W K) ! w;
    ASSERT(C > 0);
    ASSERT(no_dup M);
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let i = (if (N!C) ! 0 = K then 0 else 1);
    ASSERT(i < length (N!C));
    ASSERT(1-i < length (N!C));
    let L = ((N!C)) ! i;
    ASSERT(L = K);
    let L' = ((N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN (w+1, (M, N, U, D', NP, UP, Q, W))
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched_l (N!C)). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (w+1, (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))}
        else do {RETURN (w+1, (Propagated L' C # M, N, U, D', NP, UP, add_mset (-L') Q, W))}
      else do {
        ASSERT(snd f < length (N!C));
        let K' = (N!C) ! (snd f);
        ASSERT(K' \<in># lits_of_atms_of_mm (mset `# mset (tl N) + NP));
        ASSERT(K' \<in> snd ` D\<^sub>0);
        let N' = list_update N C (swap (N!C) i (snd f));
        let W = W(L := delete_index_and_swap (W L) w);
        let W = W(K':= W K' @ [C]);
        ASSERT(K \<noteq> K');
        RETURN (w, (M, N', U, D', NP, UP, Q, W))
      }
    }
   }
\<close>

definition delete_index_and_swap_update :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b list" where
  \<open>delete_index_and_swap_update W K w = W(K := delete_index_and_swap (W K) w)\<close>

text \<open>The precondition is not necessary.\<close>
lemma delete_index_and_swap_ll_delete_index_and_swap_update:
  \<open>(uncurry2 (RETURN ooo delete_index_and_swap_ll), uncurry2 (RETURN ooo delete_index_and_swap_update))
  \<in>[\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
      \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: delete_index_and_swap_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update'
      simp del: literal_of_nat.simps)

lemma delete_index_and_swap_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN ooo delete_index_and_swap_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0 \<and> j < length (W L)]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>j. i < length l \<and> j < length_ll l i) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update)
                      x))]\<^sub>a hrp_comp ((arrayO (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r
                               nat_rel) \<rightarrow> hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF delete_index_and_swap_aa_ll_hnr
        delete_index_and_swap_ll_delete_index_and_swap_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff )
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
      using H[of aa bb] aa bb aa_b_a_b by (auto simp: p2rel_def lit_of_natP_def)
  qed

  have pre: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def map_fun_rel_def lit_of_natP_def
        image_image ba_length_a_b
        Pos_div2_iff Neg_div2_iff all_conj_distrib length_ll_def
        intro!: ext split: if_splits)
    by (auto simp: p2rel_def lit_of_natP_def split: if_splits)

  have
    1: \<open>hrp_comp (nat_assn\<^sup>k) nat_rel = nat_assn\<^sup>k\<close> and
    2: \<open>hrp_comp (nat_assn\<^sup>k) nat_lit_rel = nat_lit_assn\<^sup>k\<close>
     by (auto simp: hrp_comp_def)
  have init: \<open>?init' = ?init\<close>
    unfolding prod_hrp_comp 1 2 hrp_comp_dest by blast

  have post: \<open>?post' = ?post\<close>
    by simp
  show ?thesis
    using H unfolding pre init
    .
qed

definition append_update :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list" where
  \<open>append_update W L a = W(L:= W L @ [a])\<close>

lemma append_ll_append_update:
  \<open>(uncurry2 (RETURN ooo append_ll), uncurry2 (RETURN ooo append_update))
  \<in>  [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f
     (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update' append_update_def
      simp del: literal_of_nat.simps)

lemma append_el_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 append_el_aa, uncurry2 (RETURN ooo append_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 append_el_aa,
   uncurry2 (RETURN \<circ>\<circ>\<circ> append_update))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>x. i < length l) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> append_update) x))]\<^sub>a
    hrp_comp ((arrayO (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
      ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel) \<rightarrow>
    hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF append_aa_hnr
        append_ll_append_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> nat_lit_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff )
    using even_Suc by blast

  have pre: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def map_fun_rel_def (* p2rel_def *) lit_of_natP_def
        image_image
        Pos_div2_iff Neg_div2_iff all_conj_distrib length_ll_def
        intro!: ext split: if_splits)
    by (auto simp: p2rel_def lit_of_natP_def split: if_splits)

  have
    1: \<open>hrp_comp (nat_assn\<^sup>k) nat_rel = nat_assn\<^sup>k\<close> and
    2: \<open>hrp_comp (nat_assn\<^sup>k) nat_lit_rel = nat_lit_assn\<^sup>k\<close>
     by (auto simp: hrp_comp_def)
  have init: \<open>?init' = ?init\<close>
    unfolding prod_hrp_comp 1 2 hrp_comp_dest by blast

  have post: \<open>?post' = ?post\<close>
    by simp
  show ?thesis
    using H unfolding pre init
    .
qed

definition is_N\<^sub>1 :: "nat literal multiset \<Rightarrow> bool" where
  \<open>is_N\<^sub>1 S \<longleftrightarrow> set_mset S = set_mset N\<^sub>1\<close>

abbreviation literals_are_N\<^sub>0 where
  \<open>literals_are_N\<^sub>0 S \<equiv>
     is_N\<^sub>1 (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of_wl None S))))\<close>

lemma mset_tl_update_swap:
  \<open>i < length xs \<Longrightarrow> j < length (xs ! i) \<Longrightarrow> k < length (xs ! i) \<Longrightarrow>
  mset `# mset (tl (xs [i := swap (xs ! i) j k])) = mset `# mset (tl xs)\<close>
  apply (cases i)
  subgoal by (cases xs) auto
  subgoal for i'
    apply (subgoal_tac \<open>(xs ! Suc i') \<in># (mset (tl xs))\<close>)
     defer
     apply (solves \<open>auto simp: nth_in_set_tl\<close>)
    apply (auto simp: tl_update_swap mset_update nth_tl)[]
    by (metis image_mset_add_mset insert_DiffM set_mset_mset)
  done

lemma unit_propagation_inner_loop_body_wl_D_spec:
  assumes
    K: \<open>K \<in> snd ` D\<^sub>0\<close> and
    N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>unit_propagation_inner_loop_body_wl_D K w S \<le>
      \<Down> {((n', T'), (n, T)). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
        (unit_propagation_inner_loop_body_wl K w S)\<close>
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
    by (cases S)
  have valued: \<open>(valued M (N ! (W K ! w) ! (1 - (if N ! (W K ! w) ! 0 = K then 0 else 1))),
     valued M' (N' ! (W' K ! w) ! (1 - (if N' ! (W' K ! w) ! 0 = K then 0 else 1)))) \<in> Id\<close>
    if \<open>N=N'\<close> and \<open>M = M'\<close> and \<open>W = W'\<close>
    for N N' :: \<open>nat literal list list\<close> and
    M M' :: \<open>(nat literal, nat literal, nat) annotated_lit list\<close> and W W'
    using that by auto
  have find_unwatched: \<open>find_unwatched M (N ! (W K ! w))
    \<le> \<Down> Id (find_unwatched M' (N' ! (W' K ! w)))\<close>
    if \<open>N=N'\<close> and \<open>M = M'\<close> and \<open>W = W'\<close>
    for N N' :: \<open>nat literal list list\<close> and
      M M' :: \<open>(nat literal, nat literal, nat) annotated_lit list\<close> and W W'
    by (auto simp: that)
  have \<open>mset `# mset (take n (tl xs)) +
    mset `# mset (drop (Suc n) xs) =
    mset `# mset (tl xs)\<close> for n :: nat and xs
    unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc
      append_take_drop_id ..
  then have m: \<open>(mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b)) =
         (mset `# mset (tl xs)) + a + b\<close>
    for a b xs and n :: nat
    by auto
  show ?thesis
    unfolding unit_propagation_inner_loop_body_wl_D_def unit_propagation_inner_loop_body_wl_def S
      watched_by.simps
    supply [[goals_limit=1]]
    apply (refine_vcg valued find_unwatched(* remove_dummy_vars *))
    subgoal by simp
    subgoal using K .
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m)
    subgoal by simp
    subgoal by simp
    subgoal
      using N\<^sub>0 unfolding S
      by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
          clauses_def image_image m lits_of_atms_of_mm_union is_N\<^sub>1_def)
    subgoal by simp
    subgoal
      using N\<^sub>0 by (simp add: S clauses_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' m mset_tl_update_swap)
    done
qed

lemma
  shows unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry2 unit_propagation_inner_loop_body_wl_D, uncurry2 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>((K, w), S). literals_are_N\<^sub>0 S \<and> K \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r {(T', T).
       T = T' \<and> literals_are_N\<^sub>0 T}\<rangle> nres_rel\<close> (is \<open>?G1\<close>) and
  unit_propagation_inner_loop_body_wl_D_unit_propagation_inner_loop_body_wl_D_weak:
   \<open>(uncurry2 unit_propagation_inner_loop_body_wl_D, uncurry2 unit_propagation_inner_loop_body_wl) \<in>
    [\<lambda>((K, w), S). literals_are_N\<^sub>0 S \<and> K \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
   (is \<open>?G2\<close>)
proof -
  have 1: \<open>nat_rel \<times>\<^sub>r {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} =
     {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}\<close>
    by auto
  show ?G1
    unfolding fref_def 1
    by (auto simp add: nres_rel_def uncurry_def snd_conv simp del: twl_st_of_wl.simps
        intro!: unit_propagation_inner_loop_body_wl_D_spec)
  moreover have \<open> \<langle>nat_rel \<times>\<^sub>r
              {(T', T).
               T = T' \<and>
               is_N\<^sub>1
                (lits_of_atms_of_mm
                  (cdcl\<^sub>W_restart_mset.clauses
                    (convert_to_state
                      (twl_st_of None (st_l_of_wl None T)))))}\<rangle>nres_rel \<subseteq> \<langle>Id\<rangle> nres_rel\<close>
    (is \<open>\<langle>?R\<rangle> nres_rel \<subseteq> _\<close>)
    using "weaken_\<Down>"[of ?R Id]
    by (auto simp: nres_rel_def prod_rel_def)
  ultimately show ?G2
    unfolding fref_def by (auto 11 0)
qed

definition unit_propagation_inner_loop_wl_loop_D :: "nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres" where
  \<open>unit_propagation_inner_loop_wl_loop_D L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>\<lambda>(w, S). twl_struct_invs (twl_st_of_wl (Some (L, w)) S) \<and>
        twl_stgy_invs (twl_st_of_wl (Some (L, w)) S) \<and>
         additional_WS_invs (st_l_of_wl (Some (L, w)) S) \<and>
        correct_watching S \<and> w \<le> length (watched_by S L) \<and>
        literals_are_N\<^sub>0 S \<and> L \<in> snd ` D\<^sub>0\<^esup>
      (\<lambda>(w, (M, N, U, D, NP, UP, Q, W)). w < length (W L) \<and> D = None)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl_D L w S
      })
      (0, S\<^sub>0)
  }
  \<close>

lemma unit_propagation_inner_loop_wl_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and K: \<open>K \<in> snd ` local.D\<^sub>0\<close>
  shows \<open>unit_propagation_inner_loop_wl_loop_D K S \<le>
     \<Down> {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
       (unit_propagation_inner_loop_wl_loop K S)\<close>
proof -
  have u: \<open>unit_propagation_inner_loop_body_wl_D K w S \<le>
         \<Down> {((n', T'), n, T). n' = n \<and> T = T' \<and> literals_are_N\<^sub>0 T'}
           (unit_propagation_inner_loop_body_wl K' w' S')\<close>
  if \<open>K \<in> snd ` local.D\<^sub>0\<close> and \<open>literals_are_N\<^sub>0 S\<close> and
    \<open>K = K'\<close> and \<open>w = w'\<close> and \<open>S = S'\<close> for S S' and w w' and K K'
    using unit_propagation_inner_loop_body_wl_D_spec[of K S w] that by auto
  have \<open>mset `# mset (take n (tl xs)) + mset `# mset (drop (Suc n) xs) = mset `# mset (tl xs)\<close>
    for n :: nat and xs
    unfolding image_mset_union[symmetric] mset_append[symmetric] drop_Suc
      append_take_drop_id ..
  then have m: \<open>(mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b)) =
         (mset `# mset (tl xs)) + a + b\<close>
    for a b xs and n :: nat
    by auto

  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_def unit_propagation_inner_loop_wl_loop_def
    apply (refine_vcg u)
    subgoal using N\<^sub>0 by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using K by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition unit_propagation_inner_loop_wl_D :: "nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>unit_propagation_inner_loop_wl_D L S\<^sub>0 = do {
     wS \<leftarrow> unit_propagation_inner_loop_wl_loop_D L S\<^sub>0;
     RETURN (snd wS)
  }\<close>

lemma unit_propagation_inner_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and K: \<open>K \<in> snd ` local.D\<^sub>0\<close>
  shows \<open>unit_propagation_inner_loop_wl_D K S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_inner_loop_wl K S)\<close>
proof -
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_D_def unit_propagation_inner_loop_wl_def
    apply (refine_vcg unit_propagation_inner_loop_wl_spec)
    subgoal using N\<^sub>0 .
    subgoal using K .
    subgoal by auto
    done
qed

definition unit_propagation_outer_loop_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>unit_propagation_outer_loop_wl_D S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      correct_watching S \<and> additional_WS_invs (st_l_of_wl None S)\<^esup>
      (\<lambda>S. pending_wl S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(pending_wl S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_pending_wl S;
        ASSERT(L \<in># lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of_wl None S))));
        unit_propagation_inner_loop_wl_D L S'
      })
      (S\<^sub>0 :: nat twl_st_wl)\<close>

lemma unit_propagation_outer_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>unit_propagation_outer_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_outer_loop_wl S)\<close>
proof -
  have select: \<open>select_and_remove_from_pending_wl S \<le>
    \<Down> {((T', L'), (T, L)). T = T' \<and> L = L' \<and>  T = set_pending_wl (pending_wl S - {#L#}) S}
       (select_and_remove_from_pending_wl S')\<close>
    if \<open>S = S'\<close> for S S' :: \<open>nat twl_st_wl\<close>
    unfolding select_and_remove_from_pending_wl_def select_and_remove_from_pending_def
    apply (rule RES_refine)
    using that unfolding select_and_remove_from_pending_wl_def by blast
  have unit_prop: \<open>literals_are_N\<^sub>0 S \<Longrightarrow>
          K \<in> snd ` D\<^sub>0 \<Longrightarrow>
          unit_propagation_inner_loop_wl_D K S
          \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (unit_propagation_inner_loop_wl K' S')\<close>
    if \<open>K = K'\<close> and \<open>S = S'\<close> for K K' and S S' :: \<open>nat twl_st_wl\<close>
    unfolding that by (rule unit_propagation_inner_loop_wl_D_spec)
  show ?thesis
    unfolding unit_propagation_outer_loop_wl_D_def unit_propagation_outer_loop_wl_def
    apply (refine_vcg select unit_prop)
    subgoal using N\<^sub>0 by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S T'L' TL T' L' T L by (cases S') auto
    subgoal by auto
    subgoal by auto
    subgoal for S' S T'L' TL T' L' T L using N\<^sub>0 by (cases S') auto
    subgoal by (auto simp: is_N\<^sub>1_def)
    done
qed


definition skip_and_resolve_loop_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>skip_and_resolve_loop_wl_D S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      (H, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S).
           skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
           additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S \<and> literals_are_N\<^sub>0 S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, Q, W) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None);
            let D' = the (get_conflict_wl (M, N, U, D, NP, UP, Q, W));
            ASSERT(is_proped (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)));
            ASSERT(C < length N);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, Some D', NP, UP, Q, W))}
            else do {
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then do {
                let E = remove1_mset (-L) D';
                let NC = op_list_copy (N!C);
                let F = (if C = 0 then {#} else (remove1_mset L (mset NC)));
                ASSERT(distinct_mset F);
                ASSERT(distinct_mset E);
                let G = E \<union># F;
                RETURN (G = {#}, (tl M, N, U, Some G, NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, Some D', NP, UP, Q, W))}
          }}
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
      RETURN S
    }
  \<close>

context
begin
text \<open>Auxiliary definition: it helps to prove refinements. Once the \<^term>\<open>RETURN\<close> is removed,
  the invariants form the \<^term>\<open>WHILE\<close>--loop are not dropped.\<close>
private definition skip_and_resolve_loop_wl_D' :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>skip_and_resolve_loop_wl_D' S\<^sub>0 =
    do {
      ASSERT(get_conflict_wl S\<^sub>0 \<noteq> None);
      S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, S).
           skip_and_resolve_loop_inv (twl_st_of_wl None S\<^sub>0) (brk, twl_st_of_wl None S) \<and>
           additional_WS_invs (st_l_of_wl None S) \<and> correct_watching S \<and> literals_are_N\<^sub>0 S\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_wl S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, Q, W) = S in
          do {
            ASSERT(M \<noteq> []);
            ASSERT(get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None);
            let D' = the (get_conflict_wl (M, N, U, D, NP, UP, Q, W));
            ASSERT(is_proped (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))));
            let (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)));
            ASSERT(C < length N);
            if -L \<notin># D' then
              do {RETURN (False, (tl M, N, U, Some D', NP, UP, Q, W))}
            else
              if get_maximum_level M (remove1_mset (-L) D') = count_decided M
              then do {
                ASSERT(distinct_mset (if C = 0 then {#} else mset (remove1 L (N!C))));
                ASSERT(distinct_mset (remove1_mset (-L) D'));
                RETURN (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C))) = {#},
                   (tl M, N, U, Some (remove1_mset (-L) D' \<union># (if C = 0 then {#} else mset (remove1 L (N!C)))),
                     NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, Some D', NP, UP, Q, W))}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some {#}, S\<^sub>0);
     RETURN S
    }
  \<close>

lemma twl_struct_invs_is_N\<^sub>1_clauses_init_clss:
  fixes S\<^sub>0 :: \<open>nat twl_st_wl\<close>
  defines \<open>S \<equiv> twl_st_of_wl None S\<^sub>0\<close>
  defines \<open>clss \<equiv> (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (convert_to_state S)))\<close>
  defines \<open>init \<equiv> (lits_of_atms_of_mm (init_clss (convert_to_state S)))\<close>
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close>
  shows \<open>is_N\<^sub>1 clss \<longleftrightarrow> is_N\<^sub>1 init\<close>
proof -

  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state S)\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def S_def
    by fast
  then have
    \<open>set_mset clss =
     set_mset init\<close>
    unfolding clss_def init_def S_def
    by (cases S\<^sub>0) (auto simp: clauses_def mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset_state
        cdcl\<^sub>W_restart_mset.no_strange_atm_def in_lits_of_atms_of_mm_ain_atms_of_iff)
  then show \<open>is_N\<^sub>1 clss \<longleftrightarrow> is_N\<^sub>1 init\<close>
    unfolding is_N\<^sub>1_def by blast
qed

lemma cdcl_twl_o_literals_are_N\<^sub>0_invs:
  fixes S :: \<open>nat twl_st_wl\<close>
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<^sub>0\<close> and
    cdcl: \<open>cdcl_twl_o\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T)\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close>
  shows \<open>literals_are_N\<^sub>0 T\<close>
proof -
  let ?S = \<open>twl_st_of_wl None S\<^sub>0\<close> and ?T = \<open>twl_st_of_wl None T\<close>
  have cdcl_stgy: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (convert_to_state ?S) (convert_to_state ?T)\<close>
    apply (rule rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy)
    subgoal using rtranclp_cdcl_twl_o_stgyD[OF cdcl] .
    subgoal using invs .
    done
  have init: \<open>init_clss (convert_to_state ?S) = init_clss (convert_to_state ?T)\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_restart_init_clss)
    using cdcl_stgy by (blast dest: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  have invs_T: \<open>twl_struct_invs (twl_st_of_wl None T)\<close>
    using cdcl invs rtranclp_cdcl_twl_o_stgyD rtranclp_cdcl_twl_stgy_twl_struct_invs by blast
  show ?thesis
    using N\<^sub>0
    unfolding twl_struct_invs_is_N\<^sub>1_clauses_init_clss[of S\<^sub>0, OF invs]
      twl_struct_invs_is_N\<^sub>1_clauses_init_clss[of T, OF invs_T] init[symmetric]
    .
qed

lemma skip_and_resolve_loop_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close>
  shows \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto
  have D'\<^sub>1: \<open>skip_and_resolve_loop_wl_D' S \<le> \<Down> {((b, T'), T). T' = T} (skip_and_resolve_loop_wl S)\<close>
    unfolding skip_and_resolve_loop_wl_D'_def skip_and_resolve_loop_wl_def
    apply (refine_vcg 1)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for brk'S' brkS brk' S'
      by (rule cdcl_twl_o_literals_are_N\<^sub>0_invs[of S])
        (use N\<^sub>0 in \<open>auto simp: skip_and_resolve_loop_inv_def\<close>)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state (twl_st_of_wl None S))\<close>)
      subgoal
        by (cases M; cases \<open>hd M\<close>) (auto simp add: clauses_def
            cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal for brk'S' brkS brk S brk' S' M x2b N x2c U x2d D x2e NP x2f UP x2g WS
       Q M' x2i N' x2j U' x2k D' x2l NP' x2m UP' x2n WS' Q' L C L' C'
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state (twl_st_of_wl None S))\<close>)
      subgoal
        by (cases M; cases \<open>hd M\<close>) (auto simp add: clauses_def
            cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
            cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
      subgoal
        apply (subst (asm) skip_and_resolve_loop_inv_def)
        apply (subst (asm) twl_struct_invs_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by force
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  have H: \<open>do {S \<leftarrow> H; RETURN S} = H\<close> for H :: \<open>'a nres\<close>
    by simp
  have D'\<^sub>2: \<open>skip_and_resolve_loop_wl_D' S \<le>
     \<Down> {((b', T'), (b, T)). b = b' \<and> T' = T \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl_D' S)\<close>
    unfolding H skip_and_resolve_loop_wl_D'_def
    apply (refine_vcg 1)
    subgoal by auto
    subgoal for b'T' bT b' T' by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: mset_take_mset_drop_mset' clauses_def)
    subgoal by auto
    subgoal by (auto simp: clauses_def)
    subgoal by auto
    subgoal by (auto simp: mset_take_mset_drop_mset' clauses_def)
    subgoal by auto
    done
  have S: \<open>({((b', T'), b, T). b = b' \<and> T' = T \<and> local.literals_are_N\<^sub>0 T} O Collect (case_prod (\<lambda>(b, y). op = y)))
   = {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  have D'\<^sub>3: \<open>local.skip_and_resolve_loop_wl_D' S \<le> \<Down> {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
    using conc_trans[OF D'\<^sub>2 D'\<^sub>1] unfolding conc_fun_chain S .
  have D'\<^sub>4: \<open>skip_and_resolve_loop_wl_D S \<le> \<Down> {(T, (b, T')). T' = T} (skip_and_resolve_loop_wl_D' S)\<close>
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_D'_def COPY_def
    op_list_copy_def
    apply (rewrite at \<open>let _ = remove1_mset _ _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = If _ _ _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = _ ! _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = _ \<union># _ in _\<close> Let_def)
    apply (rewrite mset_remove1[symmetric])+
    by refine_vcg auto
  have S: \<open>{(T, b, T'). T' = T} O {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} =
     {(T', T). T = T' \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  show ?thesis
    using conc_trans[OF D'\<^sub>4 D'\<^sub>3] unfolding conc_fun_chain S .
qed

end

definition find_lit_of_max_level_wl' :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _  \<Rightarrow> _  \<Rightarrow> _  \<Rightarrow> _  \<Rightarrow> _  \<Rightarrow>
   nat literal nres" where
  \<open>find_lit_of_max_level_wl' M N U D NP UP Q W L =
     find_lit_of_max_level_wl (M, N, U, Some D, NP, UP, Q, W) L\<close>

definition backtrack_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>backtrack_wl_D S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, Q, W) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D \<noteq> None);
        ASSERT(D \<noteq> Some {#});
        ASSERT(ex_decomp_of_max_lvl M D L);
        ASSERT(-L \<in># the D);
        ASSERT(twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        let E = the D;
        M1 \<leftarrow> find_decomp_wl (M, N, U, Some E, NP, UP, Q, W) L;
        D' \<leftarrow> list_of_mset E;

        if length D' > 1
        then do {
          ASSERT(\<forall>L' \<in># the D - {#-L#}. get_level M L' = get_level M1 L');
          L' \<leftarrow> find_lit_of_max_level_wl' M1 N U E NP UP Q W L;
          ASSERT(atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(atm_of L' \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(L \<in> snd ` D\<^sub>0);
          ASSERT(L' \<in> snd ` D\<^sub>0);
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' D'))], U,
            None, NP, UP, add_mset L {#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset_list D' UP, add_mset L {#}, W)
        }
      }
    }
  \<close>

lemma in_N\<^sub>1_iff: \<open>L \<in># N\<^sub>1 \<longleftrightarrow> atm_of L \<in> atms_of N\<^sub>1\<close>
  by (auto simp: N\<^sub>1_def atms_of_def atm_of_eq_atm_of)

lemma backtrack_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some {#}, S), get_conflict_wl S = Some {#}, S) \<in> Id\<close>
    by auto
  have 2: \<open>find_decomp_wl S L \<le> \<Down> Id (find_decomp_wl S' L')\<close>
    if \<open>S = S'\<close> and \<open>L = L'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and L L'
    using that by auto
  have 3: \<open>find_lit_of_max_level_wl S M \<le> \<Down> Id (find_lit_of_max_level_wl S' M')\<close>
    if \<open>S = S'\<close> and \<open>M = M'\<close>
    for S S' :: \<open>nat twl_st_wl\<close> and M M'
    using that by auto
  have H: \<open>mset `# mset (take n (tl xs)) + a + (mset `# mset (drop (Suc n) xs) + b) =
   mset `# mset (tl xs) + a + b\<close> for n xs a b
    apply (subst (2) append_take_drop_id[of n \<open>tl xs\<close>, symmetric])
    apply (subst mset_append)
    by (auto simp: drop_Suc)
  have N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm N) = set_mset N\<^sub>1 \<longleftrightarrow> atms_of_mm N = atms_of N\<^sub>1\<close> for N M
    apply (auto simp: in_lits_of_atms_of_mm_ain_atms_of_iff atms_of_ms_def atms_of_def
        atm_of_eq_atm_of N\<^sub>1_def in_implies_atm_of_on_atms_of_ms
        image_Un)
      using in_implies_atm_of_on_atms_of_ms in_lits_of_atms_of_mm_ain_atms_of_iff by fastforce
  have list_of_mset: \<open>list_of_mset D \<le> \<Down> {(E, F). E = F \<and> D = mset E} (list_of_mset D')\<close>
    if \<open>D = D'\<close> for D D'
    using that by (auto simp: list_of_mset_def intro!: RES_refine)
  show ?thesis
    unfolding backtrack_wl_D_def backtrack_wl_def find_lit_of_max_level_wl'_def
    apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)+
    supply [[goals_limit=1]]
    apply (refine_vcg 1 2 3 list_of_mset)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0
        apply (cases M)
         apply simp
        apply (simp add: twl_struct_invs_is_N\<^sub>1_clauses_init_clss mset_take_mset_drop_mset'
            image_image cdcl\<^sub>W_restart_mset_state clauses_def H in_N\<^sub>1_iff)
        by (auto simp: (* is_N\<^sub>1_def *) in_lits_of_atms_of_mm_ain_atms_of_iff mset_take_mset_drop_mset'
            clauses_def H (* N\<^sub>1 *) image_image cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>atms_of N\<^sub>1\<close>] in_N\<^sub>1_iff is_N\<^sub>1_def)
      subgoal
       apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
       apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
       by fast
      done
    subgoal for M SN N SU U SD D SNP NP SUP UP SWS WS W M1 M1a L' L'a
      apply (subgoal_tac \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>)
      subgoal
        using N\<^sub>0
        apply (simp add: twl_struct_invs_is_N\<^sub>1_clauses_init_clss mset_take_mset_drop_mset'
            image_image cdcl\<^sub>W_restart_mset_state clauses_def H in_N\<^sub>1_iff)
        by (auto simp: (* is_N\<^sub>1_def *) in_lits_of_atms_of_mm_ain_atms_of_iff mset_take_mset_drop_mset'
            clauses_def H (* N\<^sub>1 *) image_image cdcl\<^sub>W_restart_mset.no_strange_atm_def
            cdcl\<^sub>W_restart_mset_state eq_commute[of _ \<open>atms_of N\<^sub>1\<close>] in_N\<^sub>1_iff is_N\<^sub>1_def)
      subgoal
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast
      done
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' E E' L L'
    proof -
      thm p
      note SWS = p(1) and SUP = p(2) and SNP = p(3) and SD = p(4) and SU = p(5) and SN = p(6) and
        S = p(7) and M_not_Nil = p(15) and lvl_count_decided = p(10) and D_not_None = p(18) and
        D_not_Some_Nil = p(19) and ex_decomp = p(20) and stgy_invs = p(21) and struct_invs = p(23)
        and no_skip = p(32) and M1_M1a = p(35) and EE' = p(36) and L'_La = p(41) and
        atm_hd = p(42) and atm_L = p(43) and S_expand = p(1-14)
      have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>
        using struct_invs
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast

      show ?thesis (is \<open>(?T', ?T) \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}\<close>)
      proof -
        have T: \<open>?T = ?T'\<close> and DD': \<open>D = D'\<close>
          using M1_M1a L'_La S_expand EE' by auto

        have is_N\<^sub>1_add: \<open>is_N\<^sub>1 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset N\<^sub>1\<close> if \<open>is_N\<^sub>1 B\<close> for A B
          using that unfolding is_N\<^sub>1_def by auto

        have LL: \<open>xa \<in> set E' \<longleftrightarrow> xa \<in># (the D)\<close> for xa
          using EE' D_not_None S_expand by auto
        have atms_take_U_N: \<open>atms_of_ms (mset ` set (take U (tl N))) \<subseteq> atms_of_ms (mset ` set (tl N))\<close>
          by (auto simp: atms_of_ms_def dest: in_set_takeD)

        have \<open>set_mset
             (lits_of_atms_of_m (add_mset (- lit_of (hd M)) (add_mset L' (mset E - {#- lit_of (hd M), L'#})))) \<subseteq> set_mset N\<^sub>1\<close>
        proof (cases M)
          case Nil
          then show ?thesis using M_not_Nil by fast
        next
          case (Cons L''' M')
          have
            alien_confl:\<open>atms_of (the D) \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>\<forall>L mark. Propagated L mark \<in> set (convert_lits_l N M) \<longrightarrow>
                atms_of mark \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>atms_of_ms (mset ` set (drop (Suc U) N)) \<subseteq>
                 atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close> and
            \<open>atms_of_mm UP \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close>
            \<open>atm_of ` lits_of_l M \<subseteq> atms_of_ms (mset ` set (take U (tl N))) \<union> atms_of_mm NP\<close>
            using M_not_Nil alien N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE'
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
                image_image
                dest!: in_atms_of_minusD)
          have K_N: \<open>atm_of L' \<in> atms_of N\<^sub>1\<close>
            if \<open>atm_of L' \<in> atms_of_ms (mset ` set (tl N))\<close>
            for L' :: \<open>nat literal\<close>
            using M_not_Nil N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE' that
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
                cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
                in_lits_of_atms_of_m_ain_atms_of_iff LL
                mset_take_mset_drop_mset' H image_image
                dest!: in_atms_of_minusD)
          moreover have K_NP: \<open>atm_of L' \<in> atms_of N\<^sub>1\<close> if \<open>atm_of L' \<in> atms_of_mm NP\<close>
            for L' :: \<open>nat literal\<close>
            using M_not_Nil N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] atm_hd atm_L D_not_None EE' that
            unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
            by (auto simp add: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
                cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
                in_lits_of_atms_of_m_ain_atms_of_iff LL
                mset_take_mset_drop_mset' H image_image
                dest!: in_atms_of_minusD)
          moreover have \<open>xa \<in> set E \<Longrightarrow> atm_of xa \<in> atms_of N\<^sub>1\<close> for xa
            using alien_confl EE' atms_take_U_N DD' by (auto intro: K_N K_NP)
          ultimately show ?thesis
            using atm_hd atm_L
            by (auto simp add: in_N\<^sub>1_iff in_lits_of_atms_of_m_ain_atms_of_iff mset_take_mset_drop_mset'
                dest!: in_atms_of_minusD)
        qed
        then have \<open>literals_are_N\<^sub>0 ?T\<close>
          using N\<^sub>0 EE'
          by (cases \<open>Suc U - length N\<close>; cases N)
            (simp_all add: clauses_def mset_take_mset_drop_mset' S_expand
              lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset (* is_N\<^sub>1_def *)
              in_lits_of_atms_of_mm_ain_atms_of_iff is_N\<^sub>1_add)
        then show ?thesis
          unfolding T by blast
      qed
    qed
    subgoal premises p for M SN N SU U SD D SNP NP SUP UP SWS WS W M' SN' N'
      SU' U' SD' D' SNP' NP' SUP' UP' SWS' WS' W' M''' M'' E E'
    proof -
      thm p
      note SWS = p(1) and SUP = p(2) and SNP = p(3) and SD = p(4) and SU = p(5) and SN = p(6) and
        S = p(7) and M_not_Nil = p(15) and lvl_count_decided = p(10) and D_not_None = p(18) and
        D_not_Some_Nil = p(19) and ex_decomp = p(20) and stgy_invs = p(22) and struct_invs = p(23)
        and no_skip = p(33) and M1_M1a = p(35) and E_E' = p(36) and
        S_expand = p(1-14)
      have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, WS, W)))\<close>
        using struct_invs
        apply (subst (asm) twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        apply (subst (asm) cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def)
        by fast

      show ?thesis (is \<open>(?T', ?T) \<in> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}\<close>)
      proof -
        have T: \<open>?T = ?T'\<close>
          using M1_M1a S_expand E_E' by auto

        have is_N\<^sub>1_add: \<open>is_N\<^sub>1 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset N\<^sub>1\<close> if \<open>is_N\<^sub>1 B\<close> for A B
          using that unfolding is_N\<^sub>1_def by auto


        have \<open>atms_of_ms (mset ` set (take U (tl N))) \<subseteq> atms_of_ms (mset ` set (tl N))\<close>
          by (auto simp: atms_of_ms_def dest: in_set_takeD)

        then have \<open>set_mset (lits_of_atms_of_m (the D)) \<subseteq> set_mset N\<^sub>1\<close>
          using M_not_Nil alien N\<^sub>0[unfolded is_N\<^sub>1_def, symmetric] D_not_None
          unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
          apply (cases M)
          by (auto 5 5 simp: in_lits_of_atms_of_mm_ain_atms_of_iff atm_of_eq_atm_of
              cdcl\<^sub>W_restart_mset_state clauses_def in_N\<^sub>1_iff S_expand
              in_lits_of_atms_of_m_ain_atms_of_iff
              mset_take_mset_drop_mset' H image_image
              dest!: in_atms_of_minusD)

        then have \<open>literals_are_N\<^sub>0 ?T\<close>
          using  N\<^sub>0
          by (cases \<open>Suc U - length N\<close>; cases N)
            (simp_all add: clauses_def mset_take_mset_drop_mset' S_expand
              lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset (* is_N\<^sub>1_def *)
              in_lits_of_atms_of_mm_ain_atms_of_iff is_N\<^sub>1_add)
        then show ?thesis
          using T by blast
      qed
    qed
    done
qed


subsubsection \<open>Decide or Skip\<close>

definition decide_wl_or_skip_D :: "'v twl_st_wl \<Rightarrow> (bool \<times> 'v twl_st_wl) nres" where
  \<open>decide_wl_or_skip_D S = (do {
    ASSERT(twl_struct_invs (twl_st_of_wl None S));
    ASSERT(twl_stgy_invs (twl_st_of_wl None S));
    ASSERT(additional_WS_invs (st_l_of_wl None S));
    ASSERT(get_conflict_wl S = None);
    L \<leftarrow> find_unassigned_lit_wl S;
    if L \<noteq> None
    then do {
      let (M, N, U, D, NP, UP, Q, W) = S;
      ASSERT(L \<noteq> None);
      let K = the L;
      RETURN (False, (Decided K # M, N, U, D, NP, UP, {#-K#}, W))}
    else do {RETURN (True, S)}
  })
\<close>

theorem decide_wl_or_skip_D_spec:
 \<open>literals_are_N\<^sub>0 S \<Longrightarrow>
    decide_wl_or_skip_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T} (decide_wl_or_skip S)\<close>
  unfolding decide_wl_or_skip_D_def decide_wl_or_skip_def
  apply refine_vcg
  subgoal by simp
  subgoal by (simp add: clauses_def)
  subgoal by simp
  done


subsubsection \<open>Backtrack, Skip, Resolve or Decide\<close>

definition cdcl_twl_o_prog_wl_D :: "nat twl_st_wl \<Rightarrow> (bool \<times> nat twl_st_wl) nres" where
  \<open>cdcl_twl_o_prog_wl_D S =
    do {
      ASSERT(twl_struct_invs (twl_st_of_wl None S));
      ASSERT(twl_stgy_invs (twl_st_of_wl None S));
      ASSERT(additional_WS_invs (st_l_of_wl None S));
      do {
        if get_conflict_wl S = None
        then decide_wl_or_skip_D S
        else do {
          T \<leftarrow> skip_and_resolve_loop_wl_D S;
          ASSERT(get_conflict_wl T \<noteq> None);
          if get_conflict_wl T \<noteq> Some {#}
          then do {U \<leftarrow> backtrack_wl_D T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

theorem cdcl_twl_o_prog_wl_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), (b, T)). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
     (cdcl_twl_o_prog_wl S)\<close>
proof -
  have 1: \<open>backtrack_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl T)\<close> if \<open>literals_are_N\<^sub>0 S\<close> and \<open>S = T\<close> for S T
    using backtrack_wl_D_spec[of S] that by fast
  have 2: \<open>skip_and_resolve_loop_wl_D S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl T)\<close>
    if N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> \<open>S = T\<close>
    for S T
    using skip_and_resolve_loop_wl_D_spec[of S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_o_prog_wl_D_def cdcl_twl_o_prog_wl_def
    apply (refine_vcg decide_wl_or_skip_D_spec 1 2)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done
qed



subsubsection \<open>Full Strategy\<close>

definition cdcl_twl_stgy_prog_wl_D :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>cdcl_twl_stgy_prog_wl_D S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of_wl None T) \<and>
          twl_stgy_invs (twl_st_of_wl None T) \<and>
          (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of_wl None T)) \<and>
          cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None S\<^sub>0) (twl_st_of_wl None T) \<and>
          (\<not>brk \<longrightarrow> get_conflict_wl T = None) \<and>
          literals_are_N\<^sub>0 T\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_wl_D S;
          cdcl_twl_o_prog_wl_D T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>

theorem cdcl_twl_stgy_prog_wl_D_spec:
  assumes \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>cdcl_twl_stgy_prog_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
     (cdcl_twl_stgy_prog_wl S)\<close>
proof -
  have 1: \<open>((False, S), False, S) \<in> Id\<close> by fast
  have 2: \<open>unit_propagation_outer_loop_wl_D S \<le> \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (unit_propagation_outer_loop_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using unit_propagation_outer_loop_wl_D_spec[of S] that by fast
  have 3: \<open>cdcl_twl_o_prog_wl_D S \<le> \<Down> {((b', T'), b, T). b = b' \<and> T = T' \<and> literals_are_N\<^sub>0 T}
    (cdcl_twl_o_prog_wl T)\<close> if \<open>S = T\<close> \<open>literals_are_N\<^sub>0 S\<close> for S T
    using cdcl_twl_o_prog_wl_D_spec[of S] that by fast
  show ?thesis
    using assms
    unfolding cdcl_twl_stgy_prog_wl_D_def cdcl_twl_stgy_prog_wl_def
    apply (refine_vcg 1 2 3)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x x' x1 x2 S'
      by (cases x') fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end -- \<open>end of locale @{locale twl_array_code}\<close>


subsection \<open>Code Generation\<close>


fun pending_wll :: \<open>twl_st_wll \<Rightarrow> nat list\<close> where
  \<open>pending_wll (M, N, U, D, NP, UP, Q, W) = Q\<close>

definition pending_wll_empty :: \<open>twl_st_wll \<Rightarrow> bool\<close> where
  \<open>pending_wll_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q)\<close>

definition pending_wl_empty :: \<open>nat twl_st_wl \<Rightarrow> bool\<close>  where
  \<open>pending_wl_empty = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q = {#})\<close>


definition select_and_remove_from_pending_wl' :: \<open>twl_st_wll \<Rightarrow> twl_st_wll \<times> nat\<close> where
  \<open>select_and_remove_from_pending_wl' =
    (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>

sepref_thm list_contains_WHILE_arl
  is \<open>uncurry (\<lambda>(l::nat) xs. do{ b \<leftarrow> list_contains_WHILE l xs; RETURN (fst b)})\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding list_contains_WHILE_def
  by sepref

concrete_definition list_contains_WHILE_arl_code
   uses list_contains_WHILE_arl.refine_raw
   is "(uncurry ?f,_)\<in>_"
term list_contains_WHILE_arl_code

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
    by (auto intro!: ext)
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
    apply (auto simp: p2rel_def lit_of_natP_same_leftD lit_of_natP_same_rightD)[]
    done
  subgoal using list_all2_lengthD by auto
  done

lemma list_contains_WHILE_code_op_list_contains[sepref_fr_rules]:
  \<open>(uncurry list_contains_WHILE_arl_code,
    uncurry (RETURN oo op_list_contains)) \<in>
    nat_lit_assn\<^sup>k *\<^sub>a (clause_ll_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>(uncurry (RETURN oo op_list_contains), uncurry (RETURN oo op_list_contains)) \<in>
         nat_lit_rel \<times>\<^sub>r \<langle>nat_lit_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    by (intro frefI nres_relI) (auto simp: list_rel_def in_nat_list_rel_list_all2_in_set_iff)
  term nat_lit_rel
  have 2: \<open>hr_comp (hr_comp (arl_assn nat_assn) (\<langle>nat_rel\<rangle>list_rel))
       (\<langle>nat_lit_rel\<rangle>list_rel) = arl_assn nat_lit_assn\<close>
    by (simp add: arl_assn_def)

  show ?thesis
    using list_contains_WHILE_arl_code.refine[unfolded list_contains_WHILE_f_def[symmetric],
        FCOMP list_contains_WHILE_f_op_list_contains, FCOMP 1]
    unfolding 2 .
qed

(* TODO Move out of the locale *)
definition  get_level_wl where
  \<open>get_level_wl M L =
     snd (fold (\<lambda>i (found, l::nat). if atm_of (lit_of (M!i)) = atm_of L \<or> found
                   then if is_decided (M!i)
                     then (True, l+1)
                     else (True, l)
                   else
                     (found, l)
               )
          [0..<length M]
          (False, 0))\<close>

lemma  get_level_wl_get_level:
  \<open>get_level_wl M L = get_level M L\<close>
proof -
  define f where
    \<open>f x = (\<lambda>(found, l::nat). if atm_of (lit_of x) = atm_of L \<or> found
                   then  if is_decided x
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

(* TODO Move out *)
definition  is_decided_wl where
  \<open>is_decided_wl L \<longleftrightarrow> snd L = None\<close>

lemma  is_decided_wl_is_decided:
  \<open>(RETURN o is_decided_wl, RETURN o is_decided) \<in> nat_ann_lit_rel \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
  by (auto simp: nat_ann_lit_rel_def is_decided_wl_def is_decided_def intro!: frefI nres_relI
      elim: ann_lit_of_pair.elims)
sepref_definition   is_decided_wl_code
  is \<open>(RETURN o is_decided_wl)\<close>
  :: \<open>ann_lit_wl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding is_decided_wl_def[abs_def]
  by sepref

lemma  ann_lit_of_pair_if:
  \<open>ann_lit_of_pair (L, D) = (if D = None then Decided L else Propagated L (the D))\<close>
  by (cases D) auto

lemma is_decided_wl_code[sepref_fr_rules]:
  \<open>(is_decided_wl_code, RETURN o is_decided) \<in> pair_nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  have 1: \<open>hr_comp ann_lit_wl_assn nat_ann_lit_rel = pair_nat_ann_lit_assn\<close>
    by (auto simp: case_prod_beta hr_comp_def[abs_def] pure_def nat_ann_lit_rel_def
        prod_assn_def ann_lit_of_pair_if ex_assn_def imp_ex Abs_assn_eqI(1) ex_simps(1)[symmetric]
        simp del: pair_of_ann_lit.simps literal_of_nat.simps ex_simps(1)
        split: if_splits
        intro!: ext)
  show ?thesis
    using is_decided_wl_code.refine[FCOMP is_decided_wl_is_decided]
    unfolding 1 .
qed

sepref_definition  get_level_wl_code
  is \<open>uncurry (RETURN oo get_level_wl)\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_level_wl_def[abs_def]
  by sepref

declare  get_level_wl_code.refine[sepref_fr_rules]

definition maximum_level_remove where
  \<open>maximum_level_remove M D L =
     snd (fold (\<lambda>i (found, l). if D!i = L \<and> \<not>found then (True, l) else (found, max (get_level M (D!i)) l))
          [0..<length D]
          (False, 0))\<close>

lemma  get_level_wl_code_get_level[sepref_fr_rules]:
  \<open>(uncurry get_level_wl_code, uncurry (RETURN oo (get_level :: (nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> nat))) \<in>
    pair_nat_ann_lits_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  using get_level_wl_code.refine unfolding get_level_wl_get_level[abs_def] .

sepref_definition  maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo maximum_level_remove)\<close>
  :: \<open>pair_nat_ann_lits_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_remove_def[abs_def]
  by sepref

declare maximum_level_remove_code.refine
thm maximum_level_remove_code.refine

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
  have [simp]: \<open>fold f M k = k + count_decided M\<close>
      for D and k :: nat
    apply (induction M arbitrary: k)
    subgoal by simp
    subgoal for a D
      by (auto simp: get_maximum_level_add_mset)
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
   by (auto simp: IS_PURE_def single_valued_def p2rel_def IS_LEFT_UNIQUE_def
      dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)
lemma [sepref_fr_rules]: \<open>(uncurry (return oo op =), uncurry (RETURN oo op =)) \<in>
   (pure nat_lit_rel)\<^sup>k *\<^sub>a (pure nat_lit_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def dest: lit_of_natP_same_rightD lit_of_natP_same_leftD)

sepref_definition is_in_arl_code
  is \<open>uncurry is_in_arl\<close>
  :: \<open>(pure nat_lit_rel)\<^sup>k *\<^sub>a (arl_assn (pure nat_lit_rel))\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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
  have 3: \<open>(hr_comp clause_ll_assn (list_mset_rel O \<langle>Id\<rangle>mset_rel)) = conflict_assn\<close>
    by (auto simp: hr_comp_def[abs_def] 2 intro!: ext)
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
term arl_butlast
sepref_definition find_first_eq_code
  is \<open>uncurry find_first_eq\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding find_first_eq_def short_circuit_conv
  supply arl_butlast_hnr[sepref_fr_rules]
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
  have 1: \<open>RETURN (remove1 x xs) = RES {index xs x} \<bind>  (\<lambda>_. RETURN (remove1 x xs))\<close> for x xs
    unfolding RETURN_def[symmetric] by auto
  have [simp]: \<open>aa \<in> set ba \<Longrightarrow> ba \<noteq> []\<close> for aa ba
    by (cases ba) auto
  have [simp]: \<open>last ba = aa\<close> if \<open>Suc (index ba aa) = length ba\<close> and \<open>ba \<noteq> []\<close> for ba aa
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
           (RETURN (remove1 aa ba))\<close> for aa ba
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
proof (induction xs ys arbitrary: b rule: list_all2_induct)
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
    using IH p  by auto
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
  by (fastforce simp: remove1_wl_def list_mset_rel_def br_def mset_rel_def p2rel_def rel2p_def[abs_def]
      rel_mset_def Collect_eq_comp)


lemma remove1_wl_code_op_mset_delete[sepref_fr_rules]:
  \<open>(uncurry (remove1_wl_code), uncurry (RETURN oo op_mset_delete)) \<in>
     nat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow>\<^sub>a conflict_assn\<close>
  (is \<open>_ \<in> _ *\<^sub>a ?c\<^sup>d \<rightarrow>\<^sub>a ?o\<close>)
proof -
  have H: \<open>(uncurry remove1_wl_code, uncurry (RETURN \<circ>\<circ> remove1_mset))
  \<in> CDCL_Two_Watched_Literals_List_Watched_Code.nat_lit_assn\<^sup>k *\<^sub>a
     (hr_comp (hr_comp (arl_assn nat_assn) (\<langle>nat_rel\<rangle>list_rel))
       (list_mset_rel O
        \<langle>nat_lit_rel\<rangle>mset_rel))\<^sup>d \<rightarrow>\<^sub>a hr_comp
       (hr_comp (arl_assn nat_assn) {(l, l'). mset l = mset l'})
       (list_mset_rel O \<langle>nat_lit_rel\<rangle>mset_rel)\<close>
  (is \<open>_ \<in> _ *\<^sub>a ?c'\<^sup>d \<rightarrow>\<^sub>a ?o'\<close>)
    using remove1_wl_code.refine[FCOMP remove1_wl_remove1, FCOMP remove1_remove1_mset] .
  have 1:
    \<open>(\<exists>\<^sub>Aba bb. f bb * \<up> (bb = ba) * P ba) = (\<exists>\<^sub>Aba. f ba * P ba)\<close> for P f
    by (sep_auto simp: ex_assn_def)
  have [simp]:
    \<open>(\<exists>\<^sub>Aba bb. f bb * \<up> (bb = ba \<and> P ba)) = (\<exists>\<^sub>Aba. f ba * \<up> (P ba))\<close> for P f
    unfolding import_param_3 mult.assoc[symmetric] 1 ..
  have 2: \<open>(\<exists>\<^sub>Aba bb.
           is_array_list bb (aa, b) *
           \<up> (list_all2 lit_of_natP bb ba \<and> a = mset ba))
    = (\<exists>\<^sub>A bb.
           is_array_list bb (aa, b) *
           \<up> (\<exists>ba. list_all2 lit_of_natP bb ba \<and> a = mset ba))\<close>
    for a aa b
    apply (subst ex_assn_swap)
    unfolding ex_assn_move_out[symmetric] ent_ex_up_swap ..
  have 3: \<open>(\<exists>xs. mset xs = mset ba \<and>
                   (\<exists>ys. mset ys = a \<and>
                         list_all2 lit_of_natP xs ys)) \<longleftrightarrow>
     (\<exists>b. list_all2 lit_of_natP ba b \<and> a = mset b)\<close> for a ba
    using list_all2_reorder_left_invariance by fastforce
  have "4a": \<open>(\<exists>\<^sub>Aba bb.
           is_array_list bb (aa, b) *
           \<up> (mset bb = mset ba \<and>
              (\<exists>b. list_all2 lit_of_natP ba b \<and> a = mset b))) =
      (\<exists>\<^sub>Abb.
           is_array_list bb (aa, b) *
           \<up> (\<exists>ba. (mset bb = mset ba \<and>
              (\<exists>b. list_all2 lit_of_natP ba b \<and> a = mset b))))\<close> for a aa b
    apply (subst ex_assn_swap)
    apply(subst ex_assn_move_out[symmetric])+
    apply (subst ent_ex_up_swap)
    ..
  have "4b": \<open>(\<exists>\<^sub>Aba bb.
           is_array_list bb (aa, b) *
           \<up> (list_all2 lit_of_natP bb ba \<and> a = mset ba)) =
     (\<exists>\<^sub>Abb.
           is_array_list bb (aa, b) *
           \<up> (\<exists>ba. list_all2 lit_of_natP bb ba \<and> a = mset ba)) \<close>  for a aa b
    apply (subst ex_assn_swap)
    apply(subst ex_assn_move_out[symmetric])+
    apply (subst ent_ex_up_swap)
    ..
  have 4: \<open>(\<exists>b. mset ba = mset b \<and>
                  (\<exists>ba. list_all2 lit_of_natP b ba \<and>
                        a = mset ba)) =
           (\<exists>b. list_all2 lit_of_natP ba b \<and> a = mset b)\<close> for bb ba a
    using list_all2_reorder_left_invariance by fastforce
  have c: \<open>?c' = ?c\<close>
    by (auto simp: hr_comp_def[abs_def] list_mset_rel_def mset_rel_def arl_assn_def
        p2rel_def rel2p_def[abs_def] br_def Collect_eq_comp rel_mset_def list_rel_def
        list.rel_eq 2 3
        intro!: ext)
  have o': \<open>?o' = ?o\<close>
    by (auto simp: hr_comp_def[abs_def] list_mset_rel_def mset_rel_def arl_assn_def
        list_rel_def list.rel_eq 3 "4a" "4b" 4
        p2rel_def rel2p_def[abs_def] br_def Collect_eq_comp rel_mset_def intro!: ext)

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
  have 2: \<open>hr_comp clause_ll_assn (\<langle>Id\<rangle>list_rel) = arl_assn nat_lit_assn\<close>
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
thm get_all_ann_decomposition_exists_prepend

lemma ex_decomp_get_ann_decomposition_iff:
  \<open>(\<exists>M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)) \<longleftrightarrow>
    (\<exists>M2. M = M2 @ Decided K # M1)\<close>
  using get_all_ann_decomposition_ex by fastforce
lemma count_decided_tl_if:
  \<open>M \<noteq> [] \<Longrightarrow> count_decided (tl M) = (if is_decided (hd M) then count_decided M - 1 else count_decided M)\<close>
  by (cases M) auto

(* TODO replace  get_maximum_level_skip_first by this version: *)
lemma get_maximum_level_skip_first[simp]:
  assumes "atm_of (lit_of K) \<notin> atms_of D"
  shows "get_maximum_level (K # M) D = get_maximum_level M D"
  using assms unfolding get_maximum_level_def atms_of_def
    atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
  by (smt atm_of_in_atm_of_set_in_uminus get_level_skip_beginning image_iff lit_of.simps(2)
      multiset.map_cong0)

lemma convert_lits_l_true_annot: \<open>convert_lits_l N M \<Turnstile>a A \<longleftrightarrow> M \<Turnstile>a A\<close>
  unfolding true_annot_def by auto

lemma convert_lits_l_true_annots: \<open>convert_lits_l N M \<Turnstile>as A \<longleftrightarrow> M \<Turnstile>as A\<close>
  unfolding true_annots_def by (auto simp: convert_lits_l_true_annot)

lemma count_decided_butlast:
  \<open>count_decided (butlast xs) = (if is_decided (last xs) then count_decided xs - 1 else count_decided xs)\<close>
  by (cases xs rule: rev_cases) (auto simp: count_decided_def)

lemma find_decomp_wl_code_find_decomp_wl:
  assumes D: \<open>D \<noteq> None\<close> \<open>D \<noteq> Some {#}\<close> and M\<^sub>0: \<open>M\<^sub>0 \<noteq> []\<close> and ex_decomp: \<open>ex_decomp_of_max_lvl M\<^sub>0 D L\<close> and
    L: \<open>L = lit_of (hd M\<^sub>0)\<close> and
    no_r: \<open>no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    no_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W))\<close> and
    E: \<open>E = the D\<close>
  shows
   \<open>find_decomp_wl_imp M\<^sub>0 E L \<le>(find_decomp_wl (M\<^sub>0, N, U, D, NP, UP, Q, WS) L)\<close>
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
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g
    by (metis append.assoc append_Cons append_Nil list.exhaust list.sel(3) tl_Nil)
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2
  have H: \<open>x2g ! n = x1 ! n\<close> if \<open>x2g = take (length x2g) x1\<close> and \<open>n < length x2g\<close>
    for x2g x1 n
    by (subst that(1)) (use that(2) in \<open>auto simp: nth_take\<close>)
  have [iff]: \<open>convert_lits_l N M = [] \<longleftrightarrow> M = []\<close> for M
    by (cases M) auto
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (convert_to_state (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (convert_to_state (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (convert_to_state (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have dist_D: \<open>distinct_mset (the D)\<close>
    using D dist by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)

  have M\<^sub>0_CNot_D: \<open>M\<^sub>0 \<Turnstile>as CNot (the D)\<close>
    using D confl by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def convert_lits_l_true_annots)
  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def convert_lits_l_true_annots)
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
convert_lits_l_true_annots split: if_splits)
  ultimately have \<open>count_decided M\<^sub>0 \<noteq> get_maximum_level M\<^sub>0 (remove1_mset (- L) (the D))\<close>
    using count_decided_ge_get_maximum_level[of \<open>tl M\<^sub>0\<close> \<open>remove1_mset (- L) (the D)\<close>]
    using no_r no_s M\<^sub>0 L D get_maximum_level_convert_lits_l[of N M\<^sub>0]
    by (cases M\<^sub>0; cases \<open>hd M\<^sub>0\<close>)
      (auto 5 5 simp: cdcl\<^sub>W_restart_mset.resolve.simps cdcl\<^sub>W_restart_mset.skip.simps
        cdcl\<^sub>W_restart_mset_state split: if_splits)
  then have count_max: \<open>count_decided M\<^sub>0 > get_maximum_level M\<^sub>0 (remove1_mset (- L) (the D))\<close>
    using count_decided_ge_get_maximum_level[of M\<^sub>0 \<open>remove1_mset (- L) (the D)\<close>]
    by linarith
  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M
    by (auto)
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
      subgoal by (auto simp: count_decided_butlast count_decided_tl_if count_decided_not_Nil)[]
      subgoal by (cases M') (auto simp: count_decided_ge_get_maximum_level)
      subgoal by (cases M') (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
      subgoal by (cases M') (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] last_conv_nth count_decided_not_Nil H
          intro: butlast
          cong: if_cong split: if_splits)
      subgoal by (cases M') (auto simp: count_decided_not_Nil)
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

abbreviation "uncurry6 f \<equiv> uncurry (uncurry5 f)"
abbreviation "uncurry7 f \<equiv> uncurry (uncurry6 f)"
abbreviation "uncurry8 f \<equiv> uncurry (uncurry7 f)"
abbreviation "uncurry9 f \<equiv> uncurry (uncurry8 f)"

definition no_skip where
  \<open>no_skip S = (no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of_wl None S)))\<close>

definition no_resolve where
  \<open>no_resolve S = (no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of_wl None S)))\<close>

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

context twl_array_code
begin

definition get_conflict_wl_is_None_code :: \<open>twl_st_wll \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_code = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_None D)\<close>

definition get_conflict_wl_is_None :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_None D)\<close>

lemma get_conflict_wl_is_None_code_hnr[unfolded twl_st_l_assn_def, sepref_fr_rules]:
  \<open>(return o get_conflict_wl_is_None_code, RETURN o get_conflict_wl_is_None) \<in>
     twl_st_l_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_code_def get_conflict_wl_is_None_def
    twl_st_l_assn_def
  by sepref_to_hoare (sep_auto split: option.splits)

lemma get_conflict_wl_is_None: \<open>get_conflict_wl S = None \<longleftrightarrow> get_conflict_wl_is_None S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_def split: option.splits)

lemma watched_by_nth_watched_app':
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)

sepref_definition find_decomp_wl_imp_code
  is \<open>uncurry8 (\<lambda>M N U D NP UP Q W L. find_decomp_wl_imp M D L)\<close>
  :: \<open>[\<lambda>((((((((M, N), D), U), NP), UP), WS), Q), L). M \<noteq> []]\<^sub>a
         (pair_nat_ann_lits_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    nat_lit_assn\<^sup>k
    \<rightarrow> pair_nat_ann_lits_assn\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

thm find_decomp_wl_imp_code.refine

lemma find_decomp_wl_code[sepref_fr_rules]:
  \<open>(uncurry8 find_decomp_wl_imp_code,
      uncurry8 find_decomp_wl')
  \<in> [\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). D \<noteq> {#} \<and> M \<noteq> [] \<and> ex_decomp_of_max_lvl M (Some D) L \<and>
        L = lit_of (hd M) \<and>
     (no_skip (M, N, U, Some D, NP, UP, Q, W))  \<and>
     no_resolve (M, N, U, Some D, NP, UP, Q, W) \<and>
      twl_struct_invs (twl_st_of_wl None (M, N, U, Some D, NP, UP, Q, W))]\<^sub>a
    (pair_nat_ann_lits_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    nat_lit_assn\<^sup>k
    \<rightarrow> pair_nat_ann_lits_assn\<close>
  (is \<open> _ \<in> [?P]\<^sub>a  _ \<rightarrow> _\<close>)
proof -
  have H: \<open>(uncurry2 (uncurry2 (uncurry2 (uncurry2 find_decomp_wl_imp_code))), uncurry2 (uncurry2 (uncurry2 (uncurry2 find_decomp_wl'))))
  \<in> [\<lambda>((((((((a, b), ba), bb), bc), bd), be), bf), bg).
         bb \<noteq> {#} \<and>
         a \<noteq> [] \<and>
         ex_decomp_of_max_lvl a (Some bb) bg \<and>
         bg = lit_of (hd a) \<and>
         no_resolve (a, b, ba, Some bb, bc, bd, be, bf) \<and>
         no_skip (a, b, ba, Some bb, bc, bd, be, bf) \<and>
         twl_struct_invs
          (convert_lits_l b a, {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take ba (tl b))#},
           {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc ba) b)#}, Some bb, bc, bd, {#},
           be)]\<^sub>a pair_nat_ann_lits_assn\<^sup>d *\<^sub>a (arrayO clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a
                  clause_l_assn\<^sup>k *\<^sub>a
                  (hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k *\<^sub>a
                  CDCL_Two_Watched_Literals_List_Watched_Code.nat_lit_assn\<^sup>k \<rightarrow> pair_nat_ann_lits_assn\<close>
    (is \<open> _ \<in> [?Q]\<^sub>a  _ \<rightarrow> _\<close>)
    using find_decomp_wl_imp_code.refine[FCOMP find_decomp_wl_imp_find_decomp_wl'] .
  have QP: \<open>?Q = ?P\<close>
    by auto
  show ?thesis
    using H unfolding QP .
qed


sepref_register "unit_propagation_inner_loop_body_wl_D"
lemma (in -) id_mset_hnr[sepref_fr_rules]:
 \<open>((return o id), (RETURN o mset)) \<in> (clause_ll_assn)\<^sup>d \<rightarrow>\<^sub>a conflict_assn\<close>
  unfolding list_assn_pure_conv list_mset_assn_def the_pure_pure
  by sepref_to_hoare (sep_auto simp: list_mset_assn_def  mset_rel_def rel_mset_def hr_comp_def
      rel2p_def[abs_def] p2rel_def list_mset_rel_def br_def Collect_eq_comp pure_def list_rel_def)

sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app' watched_app_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  supply [[goals_limit=1]]
  by sepref -- \<open>Takes around 1min\<close>

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_body_wl_D.refine_raw
   is "(uncurry2 ?f,_)\<in>_"
prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def
lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_assn_def]


sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding twl_st_l_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is "(uncurry ?f,_)\<in>_"
prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def
lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of N\<^sub>0, unfolded twl_st_l_assn_def]

lemma pending_wll_empty_hnr[unfolded twl_st_l_assn_def, sepref_fr_rules]:
  \<open>(return o pending_wll_empty, RETURN o pending_wl_empty) \<in> twl_st_l_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S'\<close>)
  by (sep_auto simp: twl_st_l_assn_def pending_wll_empty_def pending_wl_empty_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil
      split: list.splits)+


lemma pending_wl_pending_wl_empty:
  \<open>pending_wl S = {#} \<longleftrightarrow> pending_wl_empty S\<close>
  by (cases S) (auto simp: pending_wl_empty_def)

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

lemma hd_select_and_remove_from_pending_refine:
  \<open>(return o select_and_remove_from_pending_wl',
       select_and_remove_from_pending_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>S. \<not>pending_wl_empty S]\<^sub>a
    twl_st_l_assn\<^sup>d \<rightarrow> twl_st_l_assn *assn nat_lit_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  let ?int = \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>
  define twl_st_l_interm_rel_1 :: \<open>(_ \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_l_interm_rel_1 \<equiv> Id \<times>\<^sub>r \<langle>\<langle>Id\<rangle> list_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r
     \<langle>Id\<rangle>option_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r list_mset_rel \<times>\<^sub>r Id\<close>
  have 1:
    \<open>(RETURN o ?int,
       select_and_remove_from_pending_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#}]\<^sub>f
    twl_st_l_interm_rel_1 \<rightarrow> \<langle>twl_st_l_interm_rel_1 \<times>\<^sub>r Id\<rangle>nres_rel\<close>
    unfolding fref_def
    apply clarify
    apply (rename_tac a aa ab ac ad ae af b ag ah ai aj ak al am ba)
    apply (case_tac af)
     apply (auto simp: fref_def nres_rel_def twl_st_l_interm_rel_1_def
        select_and_remove_from_pending_wl_def RETURN_RES_refine_iff list_mset_rel_def br_def)
    done
  define twl_st_l_interm_assn_2 :: \<open>_ \<Rightarrow> twl_st_wll \<Rightarrow> assn\<close> where
    \<open>twl_st_l_interm_assn_2 \<equiv>
       (pair_nat_ann_lits_assn *assn clauses_ll_assn *assn nat_assn *assn
       conflict_option_assn *assn
       unit_lits_assn *assn
       unit_lits_assn *assn
       list_assn nat_lit_assn *assn
       array_watched_assn
      )\<close>
  have 2:
    \<open>(return o select_and_remove_from_pending_wl', RETURN o ?int) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> []]\<^sub>a
    twl_st_l_interm_assn_2\<^sup>d \<rightarrow> twl_st_l_interm_assn_2 *assn nat_lit_assn\<close>
    unfolding select_and_remove_from_pending_wl'_def twl_st_l_interm_assn_2_def
    apply sepref_to_hoare
    by (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) x\<close>;
        case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) xi\<close>) sep_auto+
  have H: \<open>(return \<circ> select_and_remove_from_pending_wl',
             select_and_remove_from_pending_wl)
            \<in> [comp_PRE twl_st_l_interm_rel_1
                 (\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#})
                 (\<lambda>_ (_, _, _, _, _, _, Q, _). Q \<noteq> [])
                 (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_l_interm_assn_2\<^sup>d)
                                 twl_st_l_interm_rel_1 \<rightarrow> hr_comp
                          (twl_st_l_interm_assn_2 *assn
                           CDCL_Two_Watched_Literals_List_Watched_Code.nat_lit_assn)
                          (twl_st_l_interm_rel_1 \<times>\<^sub>r Id)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF 2 1] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def twl_st_l_interm_rel_1_def in_br_conv list_mset_rel_def
        pending_wl_empty_def
        intro!: ext)

  have im: \<open>?im' = ?im\<close>
    unfolding twl_st_l_interm_assn_2_def twl_st_l_interm_rel_1_def prod_hrp_comp
    by (auto simp: prod_hrp_comp hrp_comp_def list_assn_list_mset_rel_eq_list_mset_assn
        twl_st_l_assn_def hr_comp_invalid)

 have post: \<open>?f' = ?f\<close>
   by (auto simp: comp_PRE_def twl_st_l_interm_assn_2_def
       twl_st_l_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       twl_st_l_interm_rel_1_def)
  show ?thesis using H unfolding pre post im .
qed


lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)"]
  CN_FALSEI[of is_pure "twl_st_l_assn"]

lemmas hd_select_and_remove_from_pending_refine'[sepref_fr_rules] =
    hd_select_and_remove_from_pending_refine[unfolded twl_st_l_assn_def]

thm unit_propagation_inner_loop_wl_loop_D_code_refine[to_hnr]

sepref_register unit_propagation_inner_loop_wl_D
sepref_register unit_propagation_inner_loop_wl_loop_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding twl_array_code.unit_propagation_inner_loop_wl_D_def twl_st_l_assn_def
    pending_wl_pending_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_D.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_assn_def]


sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def twl_st_l_assn_def
    pending_wl_pending_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D_code
   uses twl_array_code.unit_propagation_outer_loop_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_code_def

lemmas unit_propagation_outer_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_assn_def]

definition get_conflict_wl_is_Nil :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W). \<not>is_None D \<and> Multiset.is_empty (the D))\<close>

definition get_conflict_wll_is_Nil :: \<open>twl_st_wll \<Rightarrow> bool Heap\<close> where
  \<open>get_conflict_wll_is_Nil = (\<lambda>(M, N, U, D, NP, UP, Q, W).
   do {
     if is_None D
     then return False
     else arl_is_empty (the D)
   })\<close>
lemma
  Nil_list_mset_rel_iff:
    \<open>([], aaa) \<in> list_mset_rel \<longleftrightarrow> aaa = {#}\<close> and
  empty_list_mset_rel_iff:
    \<open>(a, {#}) \<in> list_mset_rel \<longleftrightarrow> a = []\<close>
  by (auto simp: list_mset_rel_def br_def)

lemma get_conflict_wll_is_Nil_hnr[unfolded twl_st_l_assn_def, sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil, RETURN o get_conflict_wl_is_Nil) \<in> twl_st_l_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S'\<close>)
  by (sep_auto simp: twl_st_l_assn_def get_conflict_wl_is_Nil_def get_conflict_wll_is_Nil_def
      Multiset.is_empty_def Nil_list_mset_rel_iff empty_list_mset_rel_iff
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil arl_assn_def hr_comp_def null_def)+

lemma get_conflict_wl_get_conflict_wl_is_Nil:
  \<open>get_conflict_wl S\<^sub>0 = Some {#} \<longleftrightarrow> get_conflict_wl_is_Nil S\<^sub>0\<close>
  by (cases S\<^sub>0) (auto simp add: get_conflict_wl_is_Nil_def Multiset.is_empty_def split: option.splits)

definition is_decided_hd_trail_wl where
  \<open>is_decided_hd_trail_wl S = is_decided (hd (get_trail_wl S))\<close>

definition is_decided_hd_trail_wll :: \<open>twl_st_wll \<Rightarrow> bool Heap\<close> where
  \<open>is_decided_hd_trail_wll = (\<lambda>(M, N, U, D, NP, UP, Q, W).
     return (is_None (snd (hd M)))
   )\<close>

lemma
  pair_nat_ann_lit_assn_Decided_Some:
    \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
  pair_nat_ann_lit_assn_Propagated_None:
    \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
  by (auto simp: nat_ann_lit_rel_def pure_def)


lemma is_decided_hd_trail_wll_hnr[unfolded twl_st_l_assn_def, sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wll, RETURN o is_decided_hd_trail_wl) \<in> [\<lambda>(M, _). M \<noteq> []]\<^sub>atwl_st_l_assn\<^sup>k \<rightarrow> bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). M) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). M) S'\<close>;
     case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd M) S\<close>;
     case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd M) S'\<close>)
  by (sep_auto simp: twl_st_l_assn_def is_decided_hd_trail_wll_def is_decided_hd_trail_wl_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil hr_comp_def null_def
      pair_nat_ann_lit_assn_Decided_Some pair_nat_ann_lit_assn_Propagated_None
      split: option.splits)+

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
      Propagated_eq_ann_lit_of_pair_iff
      simp del: literal_of_nat.simps)+

definition op_mset_arl_empty :: "'a multiset" where
  \<open>op_mset_arl_empty = {#}\<close>

lemma arl_empty_op_mset_arl_empy[sepref_fr_rules]:
  \<open>(uncurry0 arl_empty, uncurry0 (RETURN op_mset_arl_empty)) \<in>
  unit_assn\<^sup>k \<rightarrow>\<^sub>a conflict_assn\<close>
  by sepref_to_hoare
    (use lms_empty_aref in \<open>sep_auto simp: op_mset_arl_empty_def hr_comp_def arl_assn_def\<close>)

sepref_register skip_and_resolve_loop_wl_D
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>If _ \<hole> _\<close> op_mset_arl_empty_def[symmetric])
  unfolding twl_st_l_assn_def
    pending_wl_pending_wl_empty
    get_conflict_wl.simps get_trail_wl.simps get_conflict_wl_get_conflict_wl_is_Nil
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    maximum_level_remove[symmetric]
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
  by sepref



concrete_definition (in -) skip_and_resolve_loop_wl_D_code
   uses twl_array_code.skip_and_resolve_loop_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_assn_def]

text \<open>TODO move upper\<close>
lemma (in -) id_list_of_mset[sepref_fr_rules]:
  \<open>(return o id, list_of_mset) \<in> conflict_assn\<^sup>d \<rightarrow>\<^sub>a clause_ll_assn\<close>
  by sepref_to_hoare (sep_auto simp: hr_comp_def list_of_mset_def arl_assn_def list_mset_rel_def
      br_def)

definition (in -) find_lit_of_max_level_wl_imp where
  \<open>find_lit_of_max_level_wl_imp M D L = do {
      let k = maximum_level_remove M D (-L);
      j \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>i. i < length D \<and> (\<forall>j<i. get_level M (D!j) \<noteq> k)\<^esup>
        (\<lambda>i. get_level M (D!i) \<noteq> k)
        (\<lambda>i. RETURN (i+1))
        0;
      ASSERT(j < length D);
      RETURN (D!j)
  }\<close>

declare maximum_level_remove_code.refine[sepref_fr_rules]
sepref_definition find_lit_of_max_level_wl_imp_code
  is \<open>uncurry8 (\<lambda>M N U D NP UP WS Q L. find_lit_of_max_level_wl_imp M D L)\<close>
  :: \<open>(pair_nat_ann_lits_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (clause_ll_assn)\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    nat_lit_assn\<^sup>k
    \<rightarrow>\<^sub>a nat_lit_assn\<close>
  unfolding find_lit_of_max_level_wl_imp_def get_maximum_level_remove_def[symmetric]
    thm maximum_level_remove_code.refine
  supply [[goals_limit=1]]
  by sepref
thm find_lit_of_max_level_wl_imp_code.refine

lemma find_lit_of_max_level_wl_imp_code_find_lit_of_max_level_wl'[sepref_fr_rules]:
  \<open>(uncurry8 find_lit_of_max_level_wl_imp_code, uncurry8 find_lit_of_max_level_wl') \<in>
   [\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L). L = lit_of (hd M) \<and>
     (\<exists>K\<in>#remove1_mset (-L) D. get_level M K = get_maximum_level M (remove1_mset (- L) D)) \<and>
     get_level M L \<noteq> get_maximum_level M (remove1_mset (- L) D)]\<^sub>a
   (pair_nat_ann_lits_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    nat_lit_assn\<^sup>k
    \<rightarrow> nat_lit_assn\<close>
  (is \<open>_ \<in> [?P]\<^sub>a _ \<rightarrow> _\<close>)
proof -
  have \<open>K \<in># remove1_mset (-L) D' \<Longrightarrow>
    get_level M K = get_maximum_level M (remove1_mset (- L) D') \<Longrightarrow>
    (D, D') \<in> list_mset_rel \<Longrightarrow>
    get_level M L \<noteq> get_maximum_level M (remove1_mset (- L) (mset D)) \<Longrightarrow>
    (let k = get_maximum_level M (remove1_mset (- L) (mset D))
     in WHILE\<^sub>T\<^bsup>\<lambda>i. i < length D \<and> (\<forall>j<i. get_level M (D ! j) \<noteq> k)\<^esup> (\<lambda>i. get_level M (D ! i) \<noteq> k) (\<lambda>i. RETURN (Suc i)) 0 \<bind> (\<lambda>j. ASSERT (j < length D) \<bind> (\<lambda>_. RETURN (D ! j))))
    \<le> SPEC (\<lambda>L'. L' \<in># remove1_mset (- L) D' \<and> get_level M L' = get_maximum_level M (remove1_mset (- L) D'))\<close>
    for D' :: \<open>nat clause\<close> and K :: \<open>nat literal\<close> and M :: \<open>(nat, nat) ann_lits\<close> and L and
    D :: \<open>nat clause_l\<close>
    apply (refine_vcg WHILEIT_rule[where R =\<open>measure (\<lambda>i. Suc (length D) - i)\<close>])
    subgoal by auto
    subgoal by (auto simp: list_mset_rel_def br_def)
    subgoal by auto
    subgoal apply (auto simp add: list_mset_rel_def br_def
          in_set_conv_nth dest!: in_diffD)
      by (metis less_antisym not_less_eq)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def less_Suc_eq)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal apply (auto simp add: not_less_eq list_mset_rel_def br_def)
        by (metis get_level_uminus in_remove1_mset_neq nth_mem_mset)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    done
  then have 1: \<open>(uncurry8 (\<lambda>M N U D NP UP WS Q. find_lit_of_max_level_wl_imp M D),
    uncurry8 find_lit_of_max_level_wl') \<in>
     [?P]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    unfolding find_lit_of_max_level_wl_imp_def find_lit_of_max_level_wl'_def
      find_lit_of_max_level_wl_def maximum_level_remove
    by (intro frefI nres_relI) (auto simp add: uncurry_def list_mset_rel_def br_def)
  show ?thesis
    using find_lit_of_max_level_wl_imp_code.refine[FCOMP 1] .
qed

definition backtrack_wl_D' :: "nat twl_st_wl \<Rightarrow> nat twl_st_wl nres" where
  \<open>backtrack_wl_D' S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, Q, W) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D \<noteq> None);
        ASSERT(D \<noteq> Some {#});
        ASSERT(ex_decomp_of_max_lvl M D L);
        ASSERT(-L \<in># the D);
        ASSERT(twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        let E = the D;
        M1 \<leftarrow> find_decomp_wl (M, N, U, Some E, NP, UP, Q, W) L;

        if size E > 1
        then do {
          L' \<leftarrow> find_lit_of_max_level_wl' M1 N U E NP UP Q W L;
          D' \<leftarrow> list_of_mset E;
          ASSERT(atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(atm_of L' \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(L \<in> snd ` D\<^sub>0);
          ASSERT(L' \<in> snd ` D\<^sub>0);
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' D'))], U,
            None, NP, UP, add_mset L {#}, W(-L:= W (-L) @ [length N], L':= W L' @ [length N]))
        }
        else do {
          D' \<leftarrow> list_of_mset E;
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset_list D' UP, add_mset L {#}, W)
        }
      }
    }
  \<close>
lemma [sepref_fr_rules]: \<open>(arl_length, RETURN o size) \<in> conflict_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: hr_comp_def arl_assn_def list_mset_rel_def br_def list_rel_def
      dest: list_all2_lengthD)
lemma length_a_hnr[sepref_fr_rules]: \<open>(length_a, RETURN o op_list_length) \<in> (arrayO R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto

sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D'\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding backtrack_wl_D'_def PR_CONST_def
  unfolding twl_st_l_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lms_fold_custom_empty
  unfolding no_skip_def[symmetric] no_resolve_def[symmetric]
    find_decomp_wl'_find_decomp_wl[symmetric] option.sel
  supply [[goals_limit=1]]
  apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  oops
end

definition remove1_and_add_first_abs where
  \<open>remove1_and_add_first_abs L L' D = [L, L'] @ remove1 L (remove1 L' D)\<close>

definition remove1_and_add_first :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  \<open>remove1_and_add_first L L' D =
     (let xs = length D in
      let D = D @ [L] in
      let D = D @ [L'] in
      let D = swap D 0 xs in
      swap D 1 (xs+1))
   \<close>


sepref_definition remove1_and_add_first_code
  is \<open>uncurry2 (RETURN ooo remove1_and_add_first)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d \<rightarrow>\<^sub>a clause_ll_assn\<close>
  unfolding remove1_and_add_first_def
  by sepref

lemma \<open>(uncurry2 (RETURN ooo remove1_and_add_first), uncurry2 (RETURN ooo remove1_and_add_first_abs))
  \<in> [\<lambda>((L, L'), D). L \<in> set D \<and> L' \<in> set D \<and> L \<noteq> L' \<and> distinct D]\<^sub>f
    (Id \<times>\<^sub>r Id) \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>{(l, l'). mset l = mset l'}\<rangle>nres_rel\<close>
(*   apply (auto intro!: nres_relI frefI simp: remove1_and_add_first_def remove1_and_add_first_abs_def
      Let_def swap_def nth_list_update' nth_append list_update_append mset_update) *)
  sorry


lemma \<open>(uncurry2 remove1_and_add_first_code, uncurry2 (RETURN ooo remove1_and_add_first_abs))
  \<in> [\<lambda>((L, L'), D). L \<in># D \<and> L' \<in># D \<and> L \<noteq> L' \<and> distinct_mset D]\<^sub>a
    nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow> conflict_assn\<close>









export_code "unit_propagation_inner_loop_wl_D_code" in Haskell
export_code "pending_wll_empty" in Haskell

export_code "unit_propagation_inner_loop_wl_loop_D_code" in Haskell

end