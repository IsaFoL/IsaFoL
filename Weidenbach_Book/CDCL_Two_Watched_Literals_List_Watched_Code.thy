theory CDCL_Two_Watched_Literals_List_Watched_Code
  imports CDCL_Two_Watched_Literals_List_Watched Array_Array_List
    CDCL_Two_Watched_Literals_Code_Common
begin

section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

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


subsection \<open>State Conversion\<close>

subsubsection \<open>Refinement of the Watched Function\<close>

definition watched_rel :: "('a \<Rightarrow> 'b) \<Rightarrow> nat clauses_l \<Rightarrow> ('a list \<times> (nat literal \<Rightarrow> 'b)) set" where
  \<open>watched_rel R N =
    (br (\<lambda>W. (\<lambda>L. R (W!(nat_of_lit L))))
        (\<lambda>W. \<forall>L \<in># lits_of_atms_of_mm (mset `# mset N). nat_of_lit L < length W))\<close>

text \<open>Some functions and types:\<close>

abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat literal \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> (id_assn :: nat literal \<Rightarrow> _)\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym working_queue_ll = "nat list"
type_synonym lit_queue_l = "nat literal list"
type_synonym nat_trail = \<open>(nat \<times> nat option) list\<close>
type_synonym clause_wl = \<open>nat array_list\<close>
type_synonym clauses_wl = \<open>nat array_list array\<close>
type_synonym watched_wl = \<open>nat array_list array\<close>

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

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation working_queue_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation working_queue_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_ll_assn \<equiv> list_assn nat_assn\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times>
      clause_wl option \<times> nat clauses_l \<times> nat clauses_l \<times> lit_queue_l \<times> watched_wl"

notation prod_assn (infixr "*assn" 90)

locale test =
  fixes N :: \<open>nat literal list list\<close>
begin

definition map_fun_rel :: "(nat \<times> nat literal) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> (nat literal \<Rightarrow> 'a)) set" where
  \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

definition map_fun_rel_assn :: "(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto

definition max_index where
\<open>max_index = MMax (nat_of_lit `# lits_of_atms_of_mm (mset `# mset N))\<close>

abbreviation D where
  \<open>D \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset (lits_of_atms_of_mm (mset `# mset N))\<close>

abbreviation array_watched_assn :: "(nat literal \<Rightarrow> nat list) \<Rightarrow> (nat array \<times> nat) array  \<Rightarrow> assn" where
  \<open>array_watched_assn \<equiv> hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D)\<close>

definition twl_st_l_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll \<Rightarrow> assn\<close> where
\<open>twl_st_l_assn \<equiv>
  (nat_ann_lits_assn *assn clauses_ll_assn *assn nat_assn *assn
  option_assn clause_ll_assn *assn
  clauses_l_assn *assn
  clauses_l_assn *assn
  clause_l_assn *assn
  array_watched_assn
  )\<close>


definition truc_muche :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>truc_muche S = do {RETURN S}\<close>

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

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_ll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_ll_def
  by (fastforce simp: fref_def map_fun_rel_def[abs_def] relAPP_def prod_rel_def_internal
      nres_rel_def_internal p2rel_def lit_of_natP_def)

lemma literal_of_neq_eq_nat_of_lit_eq_iff: \<open>literal_of_nat b = L \<longleftrightarrow> b = nat_of_lit L\<close>
  by (auto simp del: literal_of_nat.simps)

lemma nat_of_lit_eq_iff[iff]: \<open>nat_of_lit xa = nat_of_lit x \<longleftrightarrow> x = xa\<close>
  apply (cases x; cases xa) by auto presburger+

lemma nth_aa_watched_app[sepref_fr_rules]:
  \<open>(uncurry2 nth_aa, uncurry2 (RETURN ooo op_watched_app)) \<in>
   [\<lambda>((W, L), i). L \<in> snd ` D \<and> i < length (W L)]\<^sub>a array_watched_assn\<^sup>k *\<^sub>a nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have H: \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> op_watched_app))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D)
       (\<lambda>_ ((l, i), j). i < length l \<and> j < length (l ! i))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a
                        nat_assn\<^sup>k *\<^sub>a
                        nat_assn\<^sup>k)
                       ((\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r
                        nat_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF nth_aa_hnr nth_ll_watched_app, OF P]
    unfolding op_watched_app_def .
  have \<open>(\<forall>aa. \<exists>x\<in>#lits_of_atms_of_mm (mset `# mset N).
               nat_of_lit x < length aa \<longrightarrow>
               aa ! nat_of_lit x \<noteq> W x) = False\<close>
    (is \<open>(\<forall>aa. ?P aa) = False\<close>)
    for W :: \<open>nat literal \<Rightarrow> nat list\<close>
  proof -
    define D' where \<open>D' = D\<close>
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
    define aa where \<open>aa \<equiv> fold_mset ?f (replicate (1+Max (nat_of_lit ` snd ` D')) [])
     (mset_set (snd ` D'))\<close>
    have length_fold:  \<open>length (fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l M) = length l\<close>
      for l M
      by (induction M) auto
    have length_aa: \<open>length aa = Suc (Max (nat_of_lit ` snd ` D'))\<close>
      unfolding aa_def D''_def[symmetric] by (simp add: length_fold)
    define Ls where \<open>Ls = lits_of_atms_of_mm (mset `# mset N)\<close>
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
    have H': \<open>x \<in># lits_of_atms_of_mm (mset `# mset N) \<Longrightarrow> aa ! nat_of_lit x = W x\<close> for x
      unfolding aa_def D'_def
      by (auto simp: D'_def image_image remdups_mset_def[symmetric]
          less_Suc_eq_le Ls_def[symmetric] intro!: H)
    have \<open>\<not>?P aa\<close>
      by (auto simp: D'_def image_image remdups_mset_def[symmetric]
          less_Suc_eq_le length_aa H')
    then show ?thesis
      by blast
  qed

  then have 1: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def intro!: ext simp: prod_rel_def_internal
        relAPP_def map_fun_rel_def[abs_def] p2rel_def lit_of_natP_def
        literal_of_neq_eq_nat_of_lit_eq_iff
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

lemma watched_by_nth_watched_app:
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd o snd) S) K w\<close>
  by (cases S) (auto simp: watched_app_def)

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

text \<open>TODO this lemma should not be used\<close>
lemma nh_ctxt_option_assn_bool_assn: \<open>hn_ctxt (option_assn bool_assn) aa c = hn_val Id aa c\<close>
  apply (cases aa; cases c)
  by (auto simp: hn_ctxt_def pure_def)

sepref_definition valued_impl' is \<open>uncurry valued_impl\<close>
  :: \<open>nat_ann_lits_assn\<^sup>k *\<^sub>a nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_impl_def Let_def
  by sepref

lemma valued_impl'[sepref_fr_rules]: \<open>(uncurry valued_impl', uncurry (RETURN oo valued)) \<in>
   [\<lambda>(a, b). no_dup a]\<^sub>a nat_ann_lits_assn\<^sup>k *\<^sub>a (pure lit_of_nat_rel)\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  using valued_impl'.refine[FCOMP valued_impl_spec] by auto

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

definition unit_propagation_inner_loop_body_wl :: "nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres"  where
  \<open>unit_propagation_inner_loop_body_wl K w S = do {
    let (M, N, U, D', NP, UP, Q, W) = S;
    ASSERT(w < length (watched_by S K));
    ASSERT(K \<in> snd ` D);
    let C = (W K) ! w;
    ASSERT(no_dup M);
    ASSERT(C < length N);
    let zero = 0;
    ASSERT(zero < length (N!C));
    let i = (if (N!C) ! zero = K then 0 else 1);
    ASSERT(i < length (N!C));
    ASSERT(1-i < length (N!C));
    let L = ((N!C)) ! i;
    ASSERT(L = K);
    let L' = ((N!C)) ! (1 - i);
    ASSERT(L' \<in># mset (watched_l (N!C)) - {#L#});
    ASSERT (mset (watched_l (N!C)) = {#L, L'#});
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN (w+1, S)
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
        let N' = list_update N C (swap (N!C) i (snd f));
        ASSERT(K \<noteq> K');
        RETURN (w, (M, N', U, D', NP, UP, Q, W(* (K := delete_index_and_swap (watched_by S L) w , K':= W K' @ [C])*)))
      }
    }
   }
\<close>

sepref_definition unit_propagation_inner_loop_body_wl_code
  is \<open>uncurry2 (unit_propagation_inner_loop_body_wl :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_ann_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_assn_def
    supply [[goals_limit=1]]
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
                      apply sepref_dbg_trans_step_keep
    apply simp

  oops

end