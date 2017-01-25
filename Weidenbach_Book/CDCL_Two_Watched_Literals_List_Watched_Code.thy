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

text \<open>We start in a context where we have an initial set of literals.\<close>
context
  fixes N\<^sub>0 :: \<open>nat literal list list\<close>
begin

abbreviation D\<^sub>0 where
  \<open>D\<^sub>0 \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset (lits_of_atms_of_mm (mset `# mset N\<^sub>0))\<close>

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_ll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D\<^sub>0]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D\<^sub>0) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_ll_def
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
  shows \<open>(\<exists>aa. \<forall>x\<in>#lits_of_atms_of_mm (mset `# mset N\<^sub>0). nat_of_lit x < length aa \<and>
     aa ! nat_of_lit x = W x)\<close>
  (is \<open>\<exists>aa. ?P aa\<close>)
proof -
  define D' where \<open>D' = D\<^sub>0\<close>
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
  define Ls where \<open>Ls = lits_of_atms_of_mm (mset `# mset N\<^sub>0)\<close>
  have H: \<open>x \<in># Ls \<Longrightarrow>
      length l \<ge> Suc  (Max (nat_of_lit ` set_mset Ls)) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset Ls) ! nat_of_lit x = W x\<close>
    for x l
    apply (induction Ls arbitrary: l)
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
  have H': \<open>x \<in># lits_of_atms_of_mm (mset `# mset N\<^sub>0) \<Longrightarrow> aa ! nat_of_lit x = W x\<close> for x
    unfolding aa_def D'_def
    by (auto simp: D'_def image_image remdups_mset_def[symmetric]
        less_Suc_eq_le Ls_def[symmetric] intro!: H)
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

text \<open>TODO: use \<open>let L = K\<close> instead of \<open>let L = ((N!C)) ! i\<close>.\<close>
definition unit_propagation_inner_loop_body_wl :: "nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl K w S = do {
    let (M, N, U, D', NP, UP, Q, W) = S;
    ASSERT(w < length (watched_by S K));
    ASSERT(K \<in> snd ` D\<^sub>0);
    let C = (W K) ! w;
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
    if bN: \<open>b \<in># lits_of_atms_of_mm (mset `# mset N\<^sub>0)\<close> and
      H: \<open>\<And>aa bb. (\<forall>x\<in>#lits_of_atms_of_mm (mset `# mset N\<^sub>0).
              nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x) \<and>
          (bb, b) \<in> lit_of_nat_rel \<longrightarrow>
          bb < length aa \<and>
          ba < length (aa ! bb)\<close>
    for a :: \<open>nat literal \<Rightarrow> nat list\<close> and b :: \<open>nat literal\<close> and ba :: nat
  proof -
    obtain aa where
      aa: \<open>\<forall>x\<in>#lits_of_atms_of_mm (mset `# mset N\<^sub>0).
          nat_of_lit x < length aa \<and> aa ! nat_of_lit x = a x\<close>
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

sepref_definition unit_propagation_inner_loop_body_wl_code
  is \<open>uncurry2 (unit_propagation_inner_loop_body_wl :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_def length_ll_def[symmetric]
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  supply [[goals_limit=1]]
  by sepref -- \<open>Takes around 1min\<close>


end -- \<open>end of context\<close>

export_code "unit_propagation_inner_loop_body_wl_code" in Haskell

end