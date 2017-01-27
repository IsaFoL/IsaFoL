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

abbreviation lit_of_nat_rel where
  \<open>lit_of_nat_rel \<equiv> p2rel lit_of_natP\<close>

abbreviation nat_ann_lit_assn :: "nat literal \<Rightarrow> nat \<Rightarrow> assn" where
  \<open>nat_ann_lit_assn \<equiv> pure lit_of_nat_rel\<close>

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
     nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      lit_of_natP_def simp del: literal_of_nat.simps
      split: option.splits)

definition uminus_lit_imp :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>uminus_lit_imp L = (if L mod 2 = 0 then L + 1 else L - 1)\<close>

lemma uminus_lit_imp_hnr[sepref_fr_rules]:
  \<open>(return o uminus_lit_imp, RETURN o uminus) \<in>
     nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_ann_lit_assn\<close>
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

abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat literal \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> (id_assn :: nat literal \<Rightarrow> _)\<close>

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

abbreviation nat_ann_lits_assn :: "ann_lits_l \<Rightarrow> ann_lits_wl \<Rightarrow> assn" where
  \<open>nat_ann_lits_assn \<equiv> list_assn pair_nat_ann_lit_assn\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> arl_assn nat_ann_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> clauses_wl \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> arrayO (arl_assn nat_ann_lit_assn)\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_ann_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat list list \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation working_queue_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation working_queue_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_ll_assn \<equiv> list_assn nat_assn\<close>

abbreviation unit_lits_assn :: "nat clauses \<Rightarrow> unit_lits_wl \<Rightarrow> assn" where
  \<open>unit_lits_assn \<equiv> list_mset_assn (list_mset_assn nat_ann_lit_assn)\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times> clause_wl option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
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
  \<open>(return o (\<lambda>n. n div 2), RETURN o op_atm_of) \<in> (pure lit_of_nat_rel)\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: p2rel_def lit_of_natP_def)
thm Abs_assn_inverse nth_rule

lemma lit_of_hnr[sepref_fr_rules]:
  \<open>(return o fst, RETURN o op_lit_of) \<in> (pure nat_ann_lit_rel)\<^sup>k \<rightarrow>\<^sub>a (pure lit_of_nat_rel)\<close>
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
    (pure lit_of_nat_rel)\<^sup>k *\<^sub>a (pure lit_of_nat_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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
  :: \<open>nat_ann_lits_assn\<^sup>k *\<^sub>a nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_impl_def Let_def
  by sepref

lemma valued_impl'[sepref_fr_rules]: \<open>(uncurry valued_impl', uncurry (RETURN oo valued)) \<in>
   [\<lambda>(a, b). no_dup a]\<^sub>a nat_ann_lits_assn\<^sup>k *\<^sub>a (pure lit_of_nat_rel)\<^sup>k \<rightarrow> option_assn bool_assn\<close>
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
  :: \<open>[\<lambda>((M, N'), C). no_dup M \<and> C < length N']\<^sub>a nat_ann_lits_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn bool_assn *assn nat_assn\<close>
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

abbreviation nat_lit_rel :: "(nat literal \<times> nat literal) set" where
  \<open>nat_lit_rel \<equiv> (Id :: (nat literal \<times> _)set)\<close>


(* sepref_register N\<^sub>0
lemma N_hnr[sepref_import_param]: "(N\<^sub>0,N\<^sub>0)\<in>\<langle>nat_lit_rel\<rangle>mset_rel"
  using mset_sorted_list_of_multiset[of N\<^sub>0]
  by (auto simp: mset_rel_def[abs_def] rel2p_dflt list_all2_eq[symmetric]
      p2rel_def rel_mset_def simp del: mset_sorted_list_of_multiset) *)

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
  (nat_ann_lits_assn *assn clauses_ll_assn *assn nat_assn *assn
  option_assn clause_ll_assn *assn
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
     array_watched_assn\<^sup>k *\<^sub>a nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> op_watched_app))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((l, i), j). i < length l \<and> j < length_ll l i)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                       ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow>
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
     array_watched_assn\<^sup>k *\<^sub>a nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry length_aa, uncurry (RETURN \<circ>\<circ> length_ll_f))
       \<in> [comp_PRE
            (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel)
            (\<lambda>(W, L). L \<in> snd ` D\<^sub>0)
            (\<lambda>_ (xs, i). i < length xs)
            (\<lambda>_. True)]\<^sub>a hrp_comp
                            ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                            (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<rightarrow>
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
        then do {RETURN (w+1, (M, N, U, Some (N!C), NP, UP, {#}, W))}
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
  \<in>[\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel \<rightarrow>
      \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: delete_index_and_swap_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update'
      simp del: literal_of_nat.simps)

lemma delete_index_and_swap_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN ooo delete_index_and_swap_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0 \<and> j < length (W L)]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 delete_index_and_swap_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel) (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>j. i < length l \<and> j < length_ll l i) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> delete_index_and_swap_update)
                      x))]\<^sub>a hrp_comp ((arrayO (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                              ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r
                               nat_rel) \<rightarrow> hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF delete_index_and_swap_aa_ll_hnr
        delete_index_and_swap_ll_delete_index_and_swap_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> lit_of_nat_rel\<close> for b
    apply (auto simp: p2rel_def lit_of_natP_def Pos_div2_iff Neg_div2_iff )
    using even_Suc by blast
  have ba_length_a_b: \<open>ba < length (a b)\<close>
    if bN: \<open>b \<in># N\<^sub>1\<close> and
      H: \<open>\<And>aa bb. (\<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x) \<and>
          (bb, b) \<in> lit_of_nat_rel \<longrightarrow>
          bb < length aa \<and>
          ba < length (aa ! bb)\<close>
    for a :: \<open>nat literal \<Rightarrow> nat list\<close> and b :: \<open>nat literal\<close> and ba :: nat
  proof -
    obtain aa where
      aa: \<open>\<forall>x\<in>#N\<^sub>1. nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x\<close>
      using ex_list_watched[of a] by blast
    then have \<open>nat_of_lit b < length aa\<close> and aa_b_a_b: \<open>aa ! nat_of_lit b = a b\<close>
      using bN by blast+

    obtain bb where bb: \<open>(bb, b) \<in> lit_of_nat_rel\<close>
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
    2: \<open>hrp_comp (nat_assn\<^sup>k) lit_of_nat_rel = nat_ann_lit_assn\<^sup>k\<close>
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
     (\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel D\<^sub>0\<rangle>nres_rel\<close>
  by (auto simp: append_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def lit_of_natP_def
      nth_list_update' append_update_def
      simp del: literal_of_nat.simps)

lemma append_el_aa_hnr[sepref_fr_rules]:
  shows \<open>(uncurry2 append_el_aa, uncurry2 (RETURN ooo append_update))
     \<in> [\<lambda>((W,L), j). L \<in> snd ` D\<^sub>0]\<^sub>a
        array_watched_assn\<^sup>d *\<^sub>a nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> array_watched_assn\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  have H: \<open>(uncurry2 append_el_aa,
   uncurry2 (RETURN \<circ>\<circ>\<circ> append_update))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0)
       (\<lambda>x y. case y of (x, xa) \<Rightarrow> (case x of (l, i) \<Rightarrow> \<lambda>x. i < length l) xa)
       (\<lambda>x. nofail (uncurry2 (RETURN \<circ>\<circ>\<circ> append_update) x))]\<^sub>a
    hrp_comp ((arrayO (arl_assn nat_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
      ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel) \<rightarrow>
    hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)
\<close>
    (is \<open>?a \<in> [?pre']\<^sub>a ?init' \<rightarrow> ?post'\<close>)
    using hfref_compI_PRE[OF append_aa_hnr
        append_ll_append_update, of nat_assn] by simp
  have b: \<open>\<exists>bb. (bb, b) \<in> lit_of_nat_rel\<close> for b
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
    2: \<open>hrp_comp (nat_assn\<^sup>k) lit_of_nat_rel = nat_ann_lit_assn\<^sup>k\<close>
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

sepref_register "unit_propagation_inner_loop_body_wl_D"
sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
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
term get_conflict_wl
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
lemma watched_by_nth_watched_app:
  \<open>watched_by S K = ((snd o snd o snd o snd o snd o snd o snd) S) K\<close>
  by (cases S) (auto simp: watched_app_def)

sepref_register unit_propagation_inner_loop_wl_loop_D
sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_ann_lit_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_assn_def swap_ll_def[symmetric]
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


sepref_register unit_propagation_outer_loop_wl_D

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
            if -L \<notin> set D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, Q, W))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_l L D' (if C = 0 then [L] else N!C) = [],
                   (tl M, N, U, Some (resolve_cls_l L D' (if C = 0 then [L] else N!C)),
                     NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, D, NP, UP, Q, W))}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some [], S\<^sub>0);
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
            if -L \<notin> set D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, Q, W))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_l L D' (if C = 0 then [L] else N!C) = [],
                   (tl M, N, U, Some (resolve_cls_l L D' (if C = 0 then [L] else N!C)),
                     NP, UP, Q, W))}
              else
                do {RETURN (True, (M, N, U, D, NP, UP, Q, W))}
          }
        )
        (get_conflict_wl S\<^sub>0 = Some [], S\<^sub>0);
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
  have 1: \<open>((get_conflict_wl S = Some [], S), get_conflict_wl S = Some [], S) \<in> Id\<close>
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
    done
  have S: \<open>({((b', T'), b, T). b = b' \<and> T' = T \<and> local.literals_are_N\<^sub>0 T} O Collect (case_prod (\<lambda>(b, y). op = y)))
   = {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  have D'\<^sub>3: \<open>local.skip_and_resolve_loop_wl_D' S \<le> \<Down> {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} (skip_and_resolve_loop_wl S)\<close>
    using conc_trans[OF D'\<^sub>2 D'\<^sub>1] unfolding conc_fun_chain S .
  have D'\<^sub>4: \<open>skip_and_resolve_loop_wl_D S \<le> \<Down> {(T, (b, T')). T' = T} (skip_and_resolve_loop_wl_D' S)\<close>
    unfolding skip_and_resolve_loop_wl_D_def skip_and_resolve_loop_wl_D'_def
    by refine_vcg auto
  have S: \<open> {(T, b, T'). T' = T} O {((b', T'), T). T' = T \<and> local.literals_are_N\<^sub>0 T} =
     {(T', T). T = T' \<and> local.literals_are_N\<^sub>0 T}\<close>
    by auto
  show ?thesis
    using conc_trans[OF D'\<^sub>4 D'\<^sub>3] unfolding conc_fun_chain S .
qed

end

lemma backtrack_wl_D_spec:
  assumes N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close>
  shows \<open>backtrack_wl S \<le>
     \<Down> {(T', T). T = T' \<and> literals_are_N\<^sub>0 T}
       (backtrack_wl S)\<close>
proof -
  have 1: \<open>((get_conflict_wl S = Some [], S), get_conflict_wl S = Some [], S) \<in> Id\<close>
    by auto
  show ?thesis(* slpit the function in WHILE + RETURN, and prove invariants on WHILE first *)
    unfolding backtrack_wl_def skip_and_resolve_loop_wl_def
    apply (refine_vcg 1)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal using N\<^sub>0 apply (auto simp: clauses_def mset_take_mset_drop_mset'
          lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset) sorry
    subgoal using N\<^sub>0 apply (auto simp: clauses_def mset_take_mset_drop_mset'
          lits_of_atms_of_mm_union lits_of_atms_of_mm_add_mset)
        sorry
    done
qed

end -- \<open>end of locale @{locale twl_array_code}\<close>

export_code "unit_propagation_inner_loop_body_wl_D_code" in Haskell

end