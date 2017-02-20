theory CDCL_Two_Watched_Literals_List_Watched_Trail_Code
imports CDCL_Two_Watched_Literals_List_Watched_Code
begin
context twl_array_code
begin

definition valued_atm_on_trail where
  \<open>valued_atm_on_trail M L =
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

type_synonym trail_int = \<open>(nat, nat) ann_lits \<times> bool option list \<times> nat\<close>
type_synonym trail_assn = \<open>(nat \<times> nat option) list \<times> bool option array \<times> nat\<close>

definition trail_ref :: \<open>(trail_int \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_ref = {((M', xs, k), M). M = M' \<and> no_dup M \<and>
    (\<forall>L \<in># N\<^sub>1. atm_of L < length xs \<and> xs ! (atm_of L) = valued_atm_on_trail M (atm_of L)) \<and>
    k = count_decided M}\<close>

abbreviation trail_conc :: \<open>trail_int \<Rightarrow> trail_assn \<Rightarrow> assn\<close> where
  \<open>trail_conc \<equiv> pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn nat_assn\<close>

definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, k).
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)], k))\<close>

definition trail_assn :: "(nat, nat) ann_lits \<Rightarrow> trail_assn \<Rightarrow> assn" where
  \<open>trail_assn = hr_comp trail_conc trail_ref\<close>

lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref  \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
    (auto simp: trail_ref_def valued_atm_on_trail_def cons_trail_Propagated_def
      cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

lemma is_pos_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. L mod 2 = 0), RETURN o is_pos) \<in> nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare, rename_tac x xi, case_tac x)
   apply (sep_auto simp: p2rel_def lit_of_natP_def)+
  by presburger

sepref_definition cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, k)). atm_of L < length xs]\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d\<rightarrow>
    trail_conc\<close>
  unfolding cons_trail_Propagated_tr_def
  supply [[goals_limit = 1]]
  by sepref

lemma cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
  \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref)
         (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
         (\<lambda>_ ((L, C), M, xs, k). atm_of L < length xs)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
              (pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn nat_assn)\<^sup>d)
            (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref) \<rightarrow>
       hr_comp (pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn nat_assn) trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

fun cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', xs, k).
     (Decided L # M', xs[atm_of L := Some (is_pos L)], k+1))\<close>

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_ref  \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
    (auto simp: trail_ref_def valued_atm_on_trail_def cons_trail_Decided_tr_def
      Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

sepref_definition cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, (M, xs, k)). atm_of L < length xs]\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d \<rightarrow>
    trail_conc\<close>
  unfolding cons_trail_Decided_tr_def
  supply [[goals_limit = 1]]
  by sepref

lemma cons_trail_Decided_tr_code_cons_trail_Decided_tr[sepref_fr_rules]:
  \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a nat_lit_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN \<circ>\<circ> cons_trail_Decided))
\<in> [comp_PRE (Id \<times>\<^sub>f trail_ref) (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, M, xs, k). atm_of L < length xs)
     (\<lambda>_. True)]\<^sub>a
   hrp_comp (nat_lit_assn\<^sup>k *\<^sub>a
        (pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn nat_assn)\<^sup>d)
     (Id \<times>\<^sub>f trail_ref) \<rightarrow>
    hr_comp (pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn nat_assn) trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_code.refine cons_trail_Decided_tr] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

type_synonym twl_st_wll_trail =
  "trail_assn \<times> clauses_wl \<times> nat \<times> nat array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l \<times> watched_wl"

definition twl_st_l_trail_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_l_trail_assn \<equiv>
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  unit_lits_assn *assn
  unit_lits_assn *assn
  clause_l_assn *assn
  array_watched_assn
  )\<close>

definition valued_trail:: \<open>trail_int \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>valued_trail = (\<lambda>(M, xs, k) L. do {
     ASSERT(atm_of L < length xs);
     (case xs ! (atm_of L) of
       None \<Rightarrow> RETURN None
     | Some v \<Rightarrow> if is_pos L then RETURN (Some v)
       else RETURN (Some (\<not>v)))
  })\<close>

sepref_definition valued_trail_code
  is \<open>uncurry valued_trail\<close>
  :: \<open>trail_conc\<^sup>k *\<^sub>a  nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_trail_def
  supply [[goals_limit = 1]]
  by sepref


lemma valued_trail_code_valued[sepref_fr_rules]:
  \<open>(uncurry valued_trail_code, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>valued_atm_on_trail M (atm_of L) = (if is_pos L then valued M L else map_option uminus (valued M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: valued_atm_on_trail_def valued_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry valued_trail, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_ref \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
      (auto simp: trail_ref_def valued_def valued_trail_def
        split: if_splits option.splits)

  show ?thesis
    using valued_trail_code.refine[FCOMP 2, unfolded trail_assn_def[symmetric]] .
qed


definition find_unwatched'' :: "(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> (bool option \<times> nat) nres" where
\<open>find_unwatched'' M N' C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length (N'!C) \<and> (\<forall>j\<in>{2..<i}. -((N'!C)!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M ((N'!C)!i) \<and> i < length (N'!C))) \<and>
    (found = Some True \<longrightarrow> ((N'!C)!i \<in> lits_of_l M \<and> i < length (N'!C))) \<and>
    literals_are_in_N\<^sub>0 (mset (N'!C))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length (N'!C))
    (\<lambda>(_, i). do {
      ASSERT(i < length (N'!C));
      ASSERT((N'!C)!i \<in> snd ` D\<^sub>0);
      case valued M ((N'!C)!i) of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some True, i)} else do { RETURN (None, i+1)})
      }
    )
    (None, 2::nat)
  }
\<close>

sepref_definition find_unwatched''_code
  is \<open>uncurry2 find_unwatched''\<close>
  :: \<open>[\<lambda>((M, N), C). C < length N]\<^sub>a trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn bool_assn *assn nat_assn\<close>
  unfolding find_unwatched''_def
  by sepref

lemma literals_are_in_N\<^sub>0_in_N\<^sub>1:
  assumes
    N1: \<open>literals_are_in_N\<^sub>0 (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># N\<^sub>1\<close>
proof -
  have \<open>xs ! i \<in># mset xs\<close>
    using i_xs by auto
  then have \<open>xs ! i \<in> set_mset (lits_of_atms_of_m (mset xs))\<close>
    by (auto simp: in_lits_of_atms_of_m_ain_atms_of_iff)
  then show ?thesis
    using N1 unfolding literals_are_in_N\<^sub>0_def by blast
qed

lemma find_unwatched''_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 find_unwatched''_code, uncurry2 find_unwatched') \<in>
     [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C)) \<and> C < length N]\<^sub>a
     trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn bool_assn *assn nat_assn\<close>
proof -
    have 1: \<open>(uncurry2 find_unwatched'', uncurry2 find_unwatched') \<in>
       [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C))]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
      unfolding find_unwatched''_def find_unwatched'_def uncurry_def
      apply (intro frefI nres_relI)
      apply clarify
      apply refine_vcg
      subgoal by simp
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
      subgoal by (auto simp: image_image literals_are_in_N\<^sub>0_in_N\<^sub>1)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
  show ?thesis
    using find_unwatched''_code.refine[FCOMP 1 ] .
qed

sepref_register unit_propagation_inner_loop_body_wl_D
sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_trail_assn\<close>
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app' watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty twl_st_l_trail_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  unfolding cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]
  by sepref -- \<open>slow!\<close>

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_body_wl_D.refine_raw
   is "(uncurry2 ?f,_)\<in>_"
prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]


sepref_register unit_propagation_inner_loop_wl_loop_D
sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_l_trail_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding twl_st_l_trail_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is "(uncurry ?f,_)\<in>_"
prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def
lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]


sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding twl_array_code.unit_propagation_inner_loop_wl_D_def twl_st_l_trail_assn_def
    pending_wl_pending_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_D.refine_raw
   is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]


definition pending_wll_empty' :: \<open>twl_st_wll_trail \<Rightarrow> bool\<close> where
  \<open>pending_wll_empty' = (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q)\<close>

lemma pending_wll_empty_hnr[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(return o pending_wll_empty', RETURN o pending_wl_empty) \<in> twl_st_l_trail_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S'\<close>)
  by (sep_auto simp: twl_st_l_trail_assn_def pending_wll_empty_def pending_wl_empty_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil pending_wll_empty'_def
      split: list.splits)+

definition select_and_remove_from_pending_wl'' :: \<open>twl_st_wll_trail \<Rightarrow> twl_st_wll_trail \<times> nat\<close> where
  \<open>select_and_remove_from_pending_wl'' =
    (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>


lemma hd_select_and_remove_from_pending_wl''_refine[unfolded twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(return o select_and_remove_from_pending_wl'',
       select_and_remove_from_pending_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>S. \<not>pending_wl_empty S]\<^sub>a
    twl_st_l_trail_assn\<^sup>d \<rightarrow> twl_st_l_trail_assn *assn nat_lit_assn\<close>
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
  define twl_st_l_interm_assn_2 :: \<open>_ \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
    \<open>twl_st_l_interm_assn_2 \<equiv>
       (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
       conflict_option_assn *assn
       unit_lits_assn *assn
       unit_lits_assn *assn
       list_assn nat_lit_assn *assn
       array_watched_assn
      )\<close>
  have 2:
    \<open>(return o select_and_remove_from_pending_wl'', RETURN o ?int) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> []]\<^sub>a
    twl_st_l_interm_assn_2\<^sup>d \<rightarrow> twl_st_l_interm_assn_2 *assn nat_lit_assn\<close>
    unfolding select_and_remove_from_pending_wl''_def twl_st_l_interm_assn_2_def
    apply sepref_to_hoare
    by (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) x\<close>;
        case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) xi\<close>) sep_auto+
  have H: \<open>(return \<circ> select_and_remove_from_pending_wl'',
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
        pending_wl_empty_def)

  have im: \<open>?im' = ?im\<close>
    unfolding twl_st_l_interm_assn_2_def twl_st_l_interm_rel_1_def prod_hrp_comp
    by (auto simp: prod_hrp_comp hrp_comp_def list_assn_list_mset_rel_eq_list_mset_assn
        twl_st_l_trail_assn_def hr_comp_invalid)

 have post: \<open>?f' = ?f\<close>
   by (auto simp: comp_PRE_def twl_st_l_interm_assn_2_def
       twl_st_l_trail_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       twl_st_l_interm_rel_1_def)
  show ?thesis using H unfolding pre post im .
qed

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_l_trail_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_trail_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def twl_st_l_trail_assn_def
    pending_wl_pending_wl_empty
  by sepref


concrete_definition (in -) unit_propagation_outer_loop_wl_D_code
   uses twl_array_code.unit_propagation_outer_loop_wl_D.refine_raw
   is "(?f,_)\<in>_"

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_code_def

lemmas unit_propagation_outer_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_l_trail_assn_def]

end
end