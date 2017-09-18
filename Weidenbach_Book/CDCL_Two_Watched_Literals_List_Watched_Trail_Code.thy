theory CDCL_Two_Watched_Literals_List_Watched_Trail_Code
  imports CDCL_Two_Watched_Literals_List_Watched_Code_Common CDCL_Two_Watched_Literals_VMTF
begin

no_notation Ref.update ("_ := _" 62)

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)

subsection \<open>Code Generation\<close>

subsubsection \<open>Types and Refinement Relations\<close>

type_synonym trail_int = \<open>(nat, nat) ann_lits \<times> bool option list \<times> nat list \<times> nat\<close>
type_synonym trail_int_assn = \<open>(uint32 \<times> nat option) list \<times> bool option array \<times> uint32 array \<times> uint32\<close>

type_synonym vmtf_assn = \<open>uint32 al_vmtf_atm array \<times> nat \<times> uint32 option \<times> uint32 option\<close>
type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> uint32 array_list\<close>

type_synonym phase_saver_assn = \<open>bool array\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_int_assn \<times> clauses_wl \<times> nat \<times> conflict_option_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>

definition valued_atm_on_trail where
  \<open>valued_atm_on_trail M L =
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

instance al_vmtf_atm :: (heap) heap
proof intro_classes
  let ?to_pair = \<open>\<lambda>x::'a al_vmtf_atm. (stamp x, get_prev x, get_next x)\<close>
  have inj': \<open>inj ?to_pair\<close>
    unfolding inj_def by (intro allI) (case_tac x; case_tac y; auto)
  obtain to_nat :: \<open>nat \<times> 'a option \<times> 'a option \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o ?to_pair)\<close>
    using inj' by (blast intro: inj_comp)
  then show \<open>\<exists>to_nat :: 'a al_vmtf_atm \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

context twl_array_code_ops
begin

text \<open>TODO: It would be more performant to have:
   \<^term>\<open>defined_lit M L \<longrightarrow> lvls ! (atm_of L) = get_level M L\<close>\<close>
definition trailt_ref :: \<open>(trail_int \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trailt_ref = {((M', xs, lvls, k), M). M = M' \<and> no_dup M \<and>
    (\<forall>L \<in># N\<^sub>1. atm_of L < length xs \<and> xs ! (atm_of L) = valued_atm_on_trail M (atm_of L)) \<and>
    (\<forall>L \<in># N\<^sub>1. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1)}\<close>

end

abbreviation trailt_conc :: \<open>trail_int \<Rightarrow> trail_int_assn \<Rightarrow> assn\<close> where
  \<open>trailt_conc \<equiv> pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn
      array_assn uint32_nat_assn *assn uint32_nat_assn\<close>

definition l_vmtf_atm_rel where
\<open>l_vmtf_atm_rel = {(a', a). stamp a = stamp a' \<and>
   (get_prev a', get_prev a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel \<and>
   (get_next a', get_next a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel}\<close>

abbreviation l_vmtf_atm_assn where
\<open>l_vmtf_atm_assn \<equiv> pure l_vmtf_atm_rel\<close>

lemma l_vmtf_ATM_ref[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo l_vmtf_ATM), uncurry2 (RETURN ooo l_vmtf_ATM)) \<in>
    nat_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a
    l_vmtf_atm_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: l_vmtf_atm_rel_def uint32_nat_rel_def br_def option_assn_alt_def
     split: option.splits)

lemma stamp_ref[sepref_fr_rules]: \<open>(return o stamp, RETURN o stamp) \<in> l_vmtf_atm_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare
    (auto simp: ex_assn_move_out(2)[symmetric] return_cons_rule ent_ex_up_swap l_vmtf_atm_rel_def
      simp del: ex_assn_move_out)

lemma get_next_ref[sepref_fr_rules]: \<open>(return o get_next, RETURN o get_next) \<in> l_vmtf_atm_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule l_vmtf_atm_rel_def)

lemma get_prev_ref[sepref_fr_rules]: \<open>(return o get_prev, RETURN o get_prev) \<in> l_vmtf_atm_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule l_vmtf_atm_rel_def)

abbreviation vmtf_conc where
  \<open>vmtf_conc \<equiv> (array_assn l_vmtf_atm_assn *assn nat_assn *assn option_assn uint32_nat_assn
    *assn option_assn uint32_nat_assn)\<close>


abbreviation vmtf_remove_conc :: \<open>vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close> where
  \<open>vmtf_remove_conc \<equiv> vmtf_conc *assn arl_assn uint32_nat_assn\<close>

definition update_next_search where
  \<open>update_next_search L = (\<lambda>((A, m, lst, next_search), removed). ((A, m, lst, L), removed))\<close>

lemma update_next_search_ref[sepref_fr_rules]:
  \<open>(uncurry (return oo update_next_search), uncurry (RETURN oo update_next_search)) \<in>
      (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: update_next_search_def)

sepref_definition (in -)l_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo l_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a (array_assn l_vmtf_atm_assn)\<^sup>d \<rightarrow> array_assn l_vmtf_atm_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split]
  unfolding l_vmtf_dequeue_def vmtf_dequeue_pre_alt_def
  by sepref

declare l_vmtf_dequeue_code.refine[sepref_fr_rules]

sepref_definition vmtf_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_dequeue)\<close>
   :: \<open>[\<lambda>(L,(A,m,lst,next_search)). L < length A \<and> vmtf_dequeue_pre (L, A)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_dequeue_def
  by sepref

declare vmtf_dequeue_code.refine[sepref_fr_rules]

sepref_definition vmtf_enqueue_code
   is \<open>uncurry (RETURN oo vmtf_enqueue)\<close>
   :: \<open>[\<lambda>(L,(A,m,lst,next_search)). L < length A \<and> (lst \<noteq> None \<longrightarrow> the lst < length A)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_enqueue_def
  by sepref

declare vmtf_enqueue_code.refine[sepref_fr_rules]

sepref_definition vmtf_en_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_en_dequeue)\<close>
   :: \<open>[\<lambda>(L,(A,m,lst,next_search)). L < length A \<and> (lst \<noteq> None \<longrightarrow> the lst < length A) \<and>
        vmtf_dequeue_pre (L,A)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_dequeue_def[simp] if_splits[split] vmtf_dequeue_pre_def[simp]
  unfolding vmtf_en_dequeue_def
  by sepref

declare vmtf_en_dequeue_code.refine[sepref_fr_rules]


definition insert_sort_inner_nth where
  \<open>insert_sort_inner_nth A = insert_sort_inner (\<lambda>remove n. stamp (A ! (remove ! n)))\<close>

definition insert_sort_nth where
  \<open>insert_sort_nth = (\<lambda>(A, _). insert_sort (\<lambda>remove n. stamp (A ! (remove ! n))))\<close>


lemma insert_sort_inner_nth_code_helper:
  assumes \<open>\<forall>x\<in>set ba. x < length a\<close>  and
      \<open>b < length ba\<close> and
     mset: \<open>mset ba = mset a2'\<close>  and
      \<open>a1' < length a2'\<close>
  shows \<open>a2' ! b < length a\<close>
  using nth_mem[of b a2'] mset_eq_setD[OF mset] mset_eq_length[OF mset] assms
  by (auto simp del: nth_mem)

sepref_definition (in -) insert_sort_inner_nth_code
   is \<open>uncurry2 insert_sort_inner_nth\<close>
   :: \<open>[\<lambda>((xs, remove), n). (\<forall>x\<in>#mset remove. x < length xs) \<and> n < length remove]\<^sub>a
  (array_assn l_vmtf_atm_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
  arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_inner_nth_def insert_sort_inner_def
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]  insert_sort_inner_nth_code_helper[intro]
  by sepref

declare insert_sort_inner_nth_code.refine[sepref_fr_rules]

sepref_definition (in -) insert_sort_nth_code
   is \<open>uncurry insert_sort_nth\<close>
   :: \<open>[\<lambda>(vm, remove). (\<forall>x\<in>#mset remove. x < length (fst vm))]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_nth_def insert_sort_def insert_sort_inner_nth_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare insert_sort_nth_code.refine[sepref_fr_rules]

lemma (in -) id_ref: \<open>(return o id, RETURN o id) \<in> R\<^sup>d \<rightarrow>\<^sub>a R\<close>
  by sepref_to_hoare sep_auto

lemma insert_sort_nth_reorder:
   \<open>(uncurry insert_sort_nth, uncurry reorder_remove) \<in>
      Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  using insert_sort_reorder_remove[unfolded fref_def nres_rel_def]
  by (intro frefI nres_relI) (fastforce simp: insert_sort_nth_def)

lemma (in -) insert_sort_nth_code_reorder_remove[sepref_fr_rules]:
   \<open>(uncurry insert_sort_nth_code, uncurry reorder_remove) \<in>
      [\<lambda>((a, _), b). \<forall>x\<in>set b. x < length a]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d \<rightarrow> arl_assn uint32_nat_assn\<close>
  using insert_sort_nth_code.refine[FCOMP insert_sort_nth_reorder]
  by auto

context twl_array_code_ops
begin

lemma vmtf_imp_insert_sort_nth_code_preD:
  assumes vmtf: \<open>vm \<in> vmtf_imp M\<close>
  shows \<open>\<forall>x\<in>set (snd vm). x < length (fst (fst vm))\<close>
proof -
  obtain A m lst next_search remove where
    vm: \<open>vm = ((A, m, lst, next_search), remove)\<close>
    by (cases vm) auto

  obtain xs' ys' where
    l_vmtf: \<open>l_vmtf (ys' @ xs') m A\<close> and
    lst: \<open>lst = option_hd (ys' @ xs')\<close> and
    next_search: \<open>next_search = option_hd xs'\<close> and
    abs_vmtf: \<open>abs_l_vmtf_remove_inv M ((set xs', set ys'), set remove)\<close> and
    notin: \<open>l_vmtf_notin (ys' @ xs') m A\<close> and
    atm_A: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and
    \<open>\<forall>L\<in>set (ys' @ xs'). L \<in> atms_of N\<^sub>1\<close>
    using vmtf unfolding vmtf_imp_def vm by fast
  show ?thesis
    using atm_A abs_vmtf unfolding abs_l_vmtf_remove_inv_def
    by (auto simp: vm)
qed

sepref_thm vmtf_flush_code
   is \<open>vmtf_flush\<close>
   :: \<open>[\<lambda>a. \<exists>M. a \<in> vmtf_imp M]\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] vmtf_imp_insert_sort_nth_code_preD[dest]
  unfolding vmtf_flush_def
  apply (rewrite
        at \<open>[]\<close> in \<open>\<lambda>(_, removed). do {removed' \<leftarrow> _; (vm, _) \<leftarrow> _; RETURN (_, \<hole>)}\<close>
        to \<open>emptied_list removed'\<close>
          emptied_list_def[symmetric]
     )
  by sepref


concrete_definition (in -) vmtf_flush_code
   uses twl_array_code_ops.vmtf_flush_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_code_def

lemmas trail_dump_code_refine[sepref_fr_rules] =
   vmtf_flush_code.refine[of N\<^sub>0]

declare vmtf_flush_code.refine[sepref_fr_rules]

end

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>

type_synonym twl_st_wl_int =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

type_synonym twl_st_wl_int_trail_ref =
  \<open>trail_int \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

fun get_clauses_wl_int :: \<open>twl_st_wl_int \<Rightarrow> nat clauses_l\<close> where
  \<open>get_clauses_wl_int (M, N, U, D, _) = N\<close>

fun get_trail_wl_int :: \<open>twl_st_wl_int \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_int (M, N, U, D, _) = M\<close>


context twl_array_code_ops
begin

abbreviation trail_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_int_assn \<Rightarrow> assn\<close> where
  \<open>trail_assn \<equiv> hr_comp trailt_conc trailt_ref\<close>

definition twl_st_ref :: \<open>(twl_st_wl_int \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_ref =
  {((M', N', U', D', Q', W', vm, \<phi>), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and> D = D' \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_imp M \<and>
    phase_saving \<phi> \<and>
    no_dup M
  }\<close>

definition twl_st_int_assn :: \<open>twl_st_wl_int \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_int_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  )\<close>

definition twl_st_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_assn = hr_comp twl_st_int_assn twl_st_ref\<close>

definition literals_are_in_N\<^sub>0_int where
  \<open>literals_are_in_N\<^sub>0_int S = literals_are_in_N\<^sub>0_mm (mset `# mset (tl (get_clauses_wl_int S)))\<close>

lemma literals_are_in_N\<^sub>0_int_in_D\<^sub>0:
  assumes \<open>literals_are_in_N\<^sub>0_int S\<close> and
    \<open>i < length (get_clauses_wl_int S)\<close> and
    \<open>j < length (get_clauses_wl_int S ! i)\<close> and
    \<open>i > 0\<close>
  shows \<open>get_clauses_wl_int S ! i ! j \<in> snd ` D\<^sub>0\<close>
  using assms literals_are_in_N\<^sub>0_mm_in_N\<^sub>1[of \<open>tl (get_clauses_wl_int S)\<close> \<open>i - 1\<close> j]
  by (auto simp: literals_are_in_N\<^sub>0_int_def image_image nth_tl)

lemma literals_are_in_N\<^sub>0_int_in_D\<^sub>0':
  assumes \<open>literals_are_in_N\<^sub>0_int S\<close> and
    \<open>i < length (get_clauses_wl_int S)\<close> and
    \<open>j < length (get_clauses_wl_int S ! i)\<close> and
    \<open>i > 0\<close> and N: \<open>N = get_clauses_wl_int S\<close>
  shows \<open>N ! i ! j \<in> snd ` D\<^sub>0\<close>
  using literals_are_in_N\<^sub>0_int_in_D\<^sub>0[OF assms(1-4)] unfolding N .

end


lemma Pot_unat_lit_assn':
  \<open>(return o (\<lambda>n. 2 * n), RETURN o Pos) \<in> [\<lambda>L. L < upperN div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  apply sepref_to_hoare
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2 upperN_def)


context twl_array_code
begin

lemma Pot_unat_lit_assn:
  \<open>(return o (\<lambda>n. 2 * n), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in># N\<^sub>1]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_N1_less_than_upperN
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2 upperN_def)

lemma Neg_unat_lit_assn:
  \<open>(return o (\<lambda>n. 2 * n +1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in># N\<^sub>1]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_N1_less_than_upperN
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2_plus1 upperN_def)

end


subsubsection \<open>Refining code\<close>


context twl_array_code
begin

paragraph \<open>Unit propagation, body of the inner loop\<close>

definition (in -) set_conflict :: \<open>nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict N i _ = Some (mset (N!i))\<close>

definition (in -) conflict_add :: \<open>nat literal \<Rightarrow> conflict_rel \<Rightarrow> conflict_rel\<close> where
  \<open>conflict_add = (\<lambda>L (n, xs). (if xs ! atm_of L = None then n + 1 else n,
      xs[atm_of L := Some (is_pos L)]))\<close>


lemma conflict_add_conflict_rel:
  assumes confl: \<open>((n, xs), C) \<in> conflict_rel\<close> and uL_C: \<open>-L \<notin># C\<close> and L_N\<^sub>1: \<open>L \<in># N\<^sub>1\<close>
  shows \<open>(conflict_add L (n, xs), {#L#} \<union># C) \<in> conflict_rel\<close>
proof -
  have
    n: \<open>n = size C\<close> and
    mset: \<open>mset_as_position xs C\<close> and
    atm: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length xs\<close>
    using confl unfolding conflict_rel_def by blast+
  have \<open>distinct_mset C\<close>
    using mset by (blast dest: mset_as_position_distinct_mset)
  have atm_L_xs: \<open>atm_of L < length xs\<close>
    using atm L_N\<^sub>1 by (auto simp: atms_of_def)
  then show ?thesis
  proof (cases \<open>L \<in># C\<close>)
    case True
    with mset have xs: \<open>xs ! atm_of L = Some (is_pos L)\<close> \<open>xs ! atm_of L \<noteq> None\<close>
      by (auto dest: mset_as_position_nth)
    moreover have \<open>{#L#} \<union># C = C\<close>
      using True by (simp add: subset_mset.sup.absorb2)
    ultimately show ?thesis
      using n mset atm True
      by (auto simp: conflict_rel_def conflict_add_def xs[symmetric])
  next
    case False
    with mset have \<open>xs ! atm_of L = None\<close>
      using mset_as_position_in_iff_nth[of xs C L]
       mset_as_position_in_iff_nth[of xs C \<open>-L\<close>]  atm_L_xs uL_C
      by (cases L; cases \<open>xs ! atm_of L\<close>) auto
    then show ?thesis
      using n mset atm False atm_L_xs uL_C
      by (auto simp: conflict_rel_def conflict_add_def
          intro!: mset_as_position.intros)
  qed
qed

definition conflict_merge where
  \<open>conflict_merge D  = (\<lambda>(b, xs). do {
     (_, (i, xs)) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, zs). i \<le> length D \<and> length (snd zs) = length (snd xs) \<and>
             Suc i < upperN \<and> Suc (fst zs) < upperN \<^esup>
       (\<lambda>(i, zs). i < length D)
       (\<lambda>(i, zs). do{
           ASSERT(i < length D);
           ASSERT(Suc i < upperN);
           RETURN(Suc i, conflict_add (D!i) zs)})
       (0, xs);
     RETURN (False, i, xs)
   })\<close>

definition conflict_merge_aa where
  \<open>conflict_merge_aa C i xs = conflict_merge (C ! i) xs\<close>

type_synonym (in -) conflict_assn = \<open>uint32 \<times> bool option array\<close>
type_synonym (in -) conflict_rel = \<open>nat \<times> bool option list\<close>

abbreviation (in -) conflict_rel_assn :: \<open>conflict_rel \<Rightarrow> conflict_assn \<Rightarrow> assn\<close> where
 \<open>conflict_rel_assn \<equiv> (uint32_nat_assn *assn array_assn (option_assn bool_assn))\<close>


type_synonym (in -) conflict_option_assn = \<open>bool \<times> uint32 \<times> bool option array\<close>
type_synonym (in -) conflict_option_rel = \<open>bool \<times> nat \<times> bool option list\<close>

abbreviation (in -)conflict_option_rel_assn :: \<open>conflict_option_rel \<Rightarrow> conflict_option_assn \<Rightarrow> assn\<close> where
 \<open>conflict_option_rel_assn \<equiv> (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn))\<close>

lemma literals_are_in_N\<^sub>0_in_N\<^sub>1:
  assumes
    N1: \<open>literals_are_in_N\<^sub>0 (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># N\<^sub>1\<close>
proof -
  have \<open>xs ! i \<in># mset xs\<close>
    using i_xs by auto
  then have \<open>xs ! i \<in> set_mset (all_lits_of_m (mset xs))\<close>
    by (auto simp: in_all_lits_of_m_ain_atms_of_iff)
  then show ?thesis
    using N1 unfolding literals_are_in_N\<^sub>0_def by blast
qed

sepref_register conflict_merge_aa
sepref_thm conflict_merge_code
  is \<open>uncurry2 (PR_CONST conflict_merge_aa)\<close>
  :: \<open>[\<lambda>((N, i), (_, xs)). i < length N \<and> (\<forall>j<length (N!i). atm_of (N!i!j) < length (snd xs))]\<^sub>a
        clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] upperN_def[simp] uint32_nat_assn_one[sepref_fr_rules]
  unfolding conflict_merge_aa_def conflict_merge_def conflict_add_def PR_CONST_def
  apply (rewrite at \<open>_ + \<hole>\<close> annotate_assn[where A = \<open>uint32_nat_assn\<close>])
  apply (subst nth_rll_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) conflict_merge_code
   uses twl_array_code.conflict_merge_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) conflict_merge_code_def

lemmas conflict_merge_aa_refine[sepref_fr_rules] =
   conflict_merge_code.refine[OF twl_array_code_axioms]

definition conflict_merge'_step where
  \<open>conflict_merge'_step i zs D C = (
      let D' = mset (take i D);
          E = remdups_mset (D' + (C - D' - image_mset uminus D')) in
      ((False, fst zs, snd zs), Some E) \<in> option_conflict_rel \<and>
      literals_are_in_N\<^sub>0 E)\<close>

lemma mset_as_position_remove:
  \<open>mset_as_position xs D \<Longrightarrow> L < length xs \<Longrightarrow> mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) D))\<close>
proof (induction rule: mset_as_position.induct)
  case (empty n)
  then have [simp]: \<open>replicate n None[L := None] = replicate n None\<close>
    using list_update_id[of \<open>replicate n None\<close> L] by auto
  show ?case by (auto intro: mset_as_position.intros)
next
  case (add xs P K xs')
  show ?case
  proof (cases \<open>L = atm_of K\<close>)
    case True
    then show ?thesis
      using add by (cases K) auto
  next
    case False
    have map: \<open>mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) P))\<close>
      using add by auto
    have \<open>K \<notin># P - {#Pos L, Neg L#}\<close> \<open>-K \<notin># P - {#Pos L, Neg L#}\<close>
      by (auto simp: add.hyps dest!: in_diffD)
    then show ?thesis
      using mset_as_position.add[OF map, of \<open>K\<close> \<open>xs[L := None, atm_of K := Some (is_pos K)]\<close>]
        add False list_update_swap[of \<open>atm_of K\<close> L xs] apply simp
      apply (subst diff_add_mset_swap)
      by auto
  qed
qed

lemma option_conflict_rel_update_None:
  assumes  \<open>((False, (n, xs)), Some D) \<in> option_conflict_rel\<close> and L_xs : \<open>L < length xs\<close>
  shows \<open>((False, (if xs!L = None then n else n - 1, xs[L := None])), Some (D - {# Pos L, Neg L #})) \<in> option_conflict_rel\<close>
proof -
  have [simp]: "L \<notin># A \<Longrightarrow> A - add_mset L' (add_mset L B) = A - add_mset L' B"
    for A B :: \<open>'a multiset\<close> and L L'
    by (metis add_mset_commute minus_notin_trivial)
  have "n = size D" and map: "mset_as_position xs D"
    using assms by (auto simp: option_conflict_rel_def conflict_rel_def)
  have xs_None_iff: "xs ! L = None \<longleftrightarrow> Pos L \<notin># D \<and> Neg L \<notin># D"
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  have 1: \<open>xs ! L = None \<Longrightarrow> D - {#Pos L, Neg L#} = D\<close>
    using assms by (auto simp: xs_None_iff minus_notin_trivial)
  have 2: \<open>xs ! L = None \<Longrightarrow> xs[L := None] = xs\<close>
   using map list_update_id[of xs L] by (auto simp: 1)
  have 3: \<open>xs ! L = Some y \<longleftrightarrow> (y \<and> Pos L \<in># D \<and> Neg L \<notin># D) \<or> (\<not>y \<and> Pos L \<notin># D \<and> Neg L \<in># D)\<close> for y
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  show ?thesis
    using assms mset_as_position_remove[of xs D L]
    by (auto simp: option_conflict_rel_def conflict_rel_def 1 2 3 size_remove1_mset_If minus_notin_trivial
        mset_as_position_remove)
qed

lemma conflict_add_option_conflict_rel:
  assumes ocr: \<open>((False, (n, zs)), Some D) \<in> option_conflict_rel\<close> and
    \<open>literals_are_in_N\<^sub>0 D\<close> and L_N\<^sub>1: \<open>L \<in># N\<^sub>1\<close>
  shows
    \<open>((False, conflict_add L (n, zs)), Some (remdups_mset (remove1_mset (-L) (add_mset L D))))
        \<in> option_conflict_rel\<close>
proof -
  have minus_remove1_mset:  \<open>A - {#L, L'#} = remove1_mset L (remove1_mset L' A)\<close>
    for L L' and A :: \<open>'a multiset\<close>
    by (auto simp: ac_simps)
  have c_r: \<open>((n, zs), D) \<in> conflict_rel\<close>
    using ocr unfolding option_conflict_rel_def by auto
  then have L: \<open>atm_of L < length zs\<close>
    using L_N\<^sub>1 unfolding conflict_rel_def by (auto simp: in_N\<^sub>1_atm_of_in_atms_of_iff)
  have [simp]: \<open>distinct_mset D\<close>
    using mset_as_position_distinct_mset[of zs D] c_r unfolding conflict_rel_def by auto
  then have uL_DLL: \<open>- L \<notin># D - {#L, - L#}\<close> and L_DLL: \<open>L \<notin># D - {#L, - L#}\<close>
    using distinct_mem_diff_mset by force+
  have [simp]: \<open>zs ! atm_of L \<noteq> None \<Longrightarrow> n > 0\<close>
    using mset_as_position_in_iff_nth[of zs D L] mset_as_position_in_iff_nth[of zs D \<open>-L\<close>] L c_r unfolding conflict_rel_def
    by (cases L) (auto dest: size_diff_se)
  have \<open>((False, (if zs!(atm_of L) = None then n else n - 1,
         zs[atm_of L := None])), Some (D - {#L, -L#})) \<in> option_conflict_rel\<close>
    using option_conflict_rel_update_None[OF ocr L]
    by (metis (no_types, lifting) add_mset_commute literal.exhaust_sel uminus_Neg uminus_Pos)
  then have \<open>((if zs ! atm_of L = None then n else n - 1, zs[atm_of L := None]), D - {#L, - L#}) \<in> conflict_rel\<close>
    by (auto simp: option_conflict_rel_def)
  from conflict_add_conflict_rel[OF this _ L_N\<^sub>1] have \<open>((False, (if zs!(atm_of L) = None then n+1 else n, zs[atm_of L := Some (is_pos L)])), Some (add_mset L (D - {#L, -L#}))) \<in> option_conflict_rel\<close>
    using uL_DLL L_DLL L by (auto simp: option_conflict_rel_def conflict_add_def)
  moreover have \<open>add_mset L (D - {#L, - L#}) = remdups_mset (remove1_mset (- L) (add_mset L D))\<close>
    using uL_DLL L_DLL unfolding minus_remove1_mset
    by (auto simp: minus_notin_trivial distinct_mset_remdups_mset_id simp del: diff_diff_add_mset
       dest: in_diffD)
  ultimately show ?thesis
    by (auto simp: conflict_add_def)
qed

lemma (in -) notin_add_mset_remdups_mset:
  \<open>a \<notin># A \<Longrightarrow> add_mset a (remdups_mset A) = remdups_mset (add_mset a A)\<close>
  by auto

lemma (in -) not_tautology_minus:
  \<open>\<not>tautology A \<Longrightarrow> \<not>tautology (A - B)\<close>
  by (auto simp: tautology_decomp dest: in_diffD)

lemma (in -)remdups_mset_inv: \<open>remdups_mset (remdups_mset S) = remdups_mset S\<close>
  by (auto simp: remdups_mset_def)

lemma literals_are_in_N\<^sub>0_add_mset: \<open>literals_are_in_N\<^sub>0 (add_mset L A) \<longleftrightarrow> literals_are_in_N\<^sub>0 A \<and> L \<in># N\<^sub>1\<close>
  unfolding literals_are_in_N\<^sub>0_def by (auto simp: all_lits_of_m_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff)

lemma all_lits_of_m_remdups_mset:
  \<open>set_mset (all_lits_of_m (remdups_mset N)) = set_mset (all_lits_of_m N)\<close>
  by (auto simp: all_lits_of_m_def)

lemma literals_are_in_N\<^sub>0_remdups: \<open>literals_are_in_N\<^sub>0 (remdups_mset N) = literals_are_in_N\<^sub>0 N\<close>
  by (auto simp: literals_are_in_N\<^sub>0_def all_lits_of_m_remdups_mset)

lemma (in -) diff_le_mono2_mset: \<open>A \<subseteq># B \<Longrightarrow> C - B \<subseteq># C - A\<close>
  apply (auto simp: subseteq_mset_def ac_simps)
  by (simp add: diff_le_mono2)

lemma mset_as_position_tautology: \<open>mset_as_position xs C \<Longrightarrow> \<not>tautology C\<close>
  by (induction rule: mset_as_position.induct) (auto simp: tautology_add_mset)

lemma conflict_merge'_spec:
  assumes
      o: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close> and
      dist: \<open>distinct D\<close> and
      lits: \<open>literals_are_in_N\<^sub>0 (mset D)\<close> and
      tauto: \<open>\<not>tautology (mset D)\<close> and
      \<open>literals_are_in_N\<^sub>0 C\<close>
  shows \<open>conflict_merge D (b, n, xs) \<le> \<Down> option_conflict_rel
            (RETURN (Some (mset D \<union># (C - image_mset uminus (mset D)))))\<close>
proof -
  have [simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) < upperN\<close> for a
    using simple_clss_size_upper_div2[of \<open>mset D\<close>] assms by (auto simp: upperN_def)
  have Suc_N_upperN: \<open>Suc n < upperN\<close>
    using assms simple_clss_size_upper_div2[of C] mset_as_position_distinct_mset[of xs C]
      conflict_rel_not_tautolgy[of n xs C]
    unfolding option_conflict_rel_def conflict_rel_def
    by (auto simp: upperN_def)
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_conflict_rel \<Longrightarrow> literals_are_in_N\<^sub>0 C \<Longrightarrow>
        Suc (Suc a) < upperN\<close> for b a ba C
    using conflict_rel_size[of a ba C] by (auto simp: option_conflict_rel_def
        conflict_rel_def upperN_def)
  have [simp]: \<open>remdups_mset C = C\<close>
    using o mset_as_position_distinct_mset[of xs C] by (auto simp: option_conflict_rel_def conflict_rel_def
        distinct_mset_remdups_mset_id)
  have \<open>\<not>tautology C\<close>
    using mset_as_position_tautology o by (auto simp: option_conflict_rel_def
        conflict_rel_def)
  have \<open>distinct_mset C\<close>
    using mset_as_position_distinct_mset[of _ C] o
    unfolding option_conflict_rel_def conflict_rel_def by auto
  have inv: "conflict_merge'_step x1 x2 D C"
    if
      "(b, n, xs) = (b', n')" and
      "case s of
       (i, zs) \<Rightarrow>
         i \<le> length D \<and>
         length (snd zs) = length (snd n') \<and>
         Suc i < upperN \<and> Suc (fst zs) < upperN" and
      "case s of (i, zs) \<Rightarrow> conflict_merge'_step i zs D C" and
      "case s of (i, zs) \<Rightarrow> i < length D" and
      "s = (j, zs)" and
      j_le_D: "j < length D" and
      "Suc j < upperN" and
      "(Suc j, conflict_add (D ! j) zs) = (x1, x2)"
    for b :: bool and n :: nat and xs b' n' s j zs x1 x2
  proof -
    have notin_notin_diff_iff: \<open>a \<notin># B \<Longrightarrow> a \<in># A - B \<longleftrightarrow> a \<in># A\<close> for a :: \<open>nat literal\<close> and A B
      by (auto dest: in_diffD simp add: in_diff_count not_in_iff)
    have Dj: \<open>D ! j \<in># N\<^sub>1\<close>
      using lits j_le_D literals_are_in_N\<^sub>0_in_N\<^sub>1 by blast
    have Dj_D: \<open>D ! j \<notin> set(take j D)\<close>
      using dist j_le_D apply (subst (asm) append_take_drop_id[of \<open>Suc j\<close> D, symmetric])
      unfolding distinct_append by (auto simp: take_Suc_conv_app_nth)

    have \<open>- D ! j \<notin> set D\<close>
      using tauto nth_mem[OF j_le_D] by auto
    then have uDj_jD: \<open>- D ! j \<notin> set(take j D)\<close>
      by (auto dest: in_set_takeD)

    have
      [simp]: \<open>j < length D\<close> \<open>x1 = Suc j\<close> \<open>x2 = conflict_add (D ! j) zs\<close> and
      ocr: \<open>((False, (fst zs, snd zs)), Some (remdups_mset (mset (take j D) + (C - (mset (take j D) + uminus `# mset (take j D))))))
        \<in> option_conflict_rel\<close> and
      lits: \<open>literals_are_in_N\<^sub>0 (remdups_mset (mset (take j D) + (C - (mset (take j D) + uminus `# mset (take j D)))))\<close>
      using that unfolding conflict_merge'_step_def Let_def by auto

    define CD where
      \<open>CD = (C - mset (take j D) - uminus `# mset (take j D))\<close>

    have [simp]: \<open>literals_are_in_N\<^sub>0
      (remdups_mset (mset (take j D) + (C - add_mset (- D ! j) (add_mset (D ! j) (mset (take j D) + uminus `# mset (take j D))))))\<close>
       using that by (auto simp: conflict_merge'_step_def Let_def literals_are_in_N\<^sub>0_remdups
          ac_simps CD_def[symmetric] diff_le_mono2_mset intro: literals_are_in_N\<^sub>0_mono)

    have [simp]: \<open>D ! j \<in># C - (mset (take j D) + uminus `# mset (take j D)) \<longleftrightarrow> D !j \<in># C\<close>
      apply (rule notin_notin_diff_iff)
      using uDj_jD Dj_D by auto

    have [simp]: \<open>D ! j \<notin># C - add_mset (- D ! j)
             (add_mset (D ! j)
               (mset (take j D) + uminus `# mset (take j D)))\<close>
      using uDj_jD Dj_D
      by (metis (full_types) \<open>distinct_mset C\<close> add_mset_commute distinct_mem_diff_mset union_single_eq_member)
    have H: \<open>((False, conflict_add (D ! j) zs), Some C) \<in> option_conflict_rel \<Longrightarrow> C = C' \<Longrightarrow>
      ((False, conflict_add (D ! j) zs), Some C') \<in> option_conflict_rel\<close>
      for C C'
      by auto
    have \<open>distinct_mset CD\<close>
      using \<open>distinct_mset C\<close> unfolding CD_def by auto
    then have [simp]: \<open>D ! j \<notin># remove1_mset (D ! j) CD\<close>
      by (meson distinct_mem_diff_mset multi_member_last)
    then have [simp]: \<open>D ! j \<notin># CD - {#- D ! j, D ! j#}\<close>
      by (auto simp del: diff_diff_add_mset remdups_mset_singleton_sum
            simp: diff_diff_add_mset[symmetric] diff_add_mset_remove1
            dest: in_diffD)
    have \<open>\<not>tautology CD\<close>
      using \<open>\<not>tautology C\<close> by (auto simp: not_tautology_minus CD_def)
    then have in_CD_uCD: \<open>D ! j \<in># CD \<Longrightarrow> - D ! j \<notin># CD\<close>
      using tautology_minus by blast
    then have DJ_notin_CD: \<open>D ! j \<in># C \<Longrightarrow> - D ! j \<notin># CD\<close>
      by (auto simp: CD_def dest: in_diffD)
    have DJ_in_CD: \<open>D ! j \<in># C \<Longrightarrow> D ! j \<in># CD\<close>
      unfolding CD_def by auto
    have [simp]: \<open>x \<notin># C \<Longrightarrow> x \<notin># CD\<close> for x
      unfolding CD_def by (auto dest: in_diffD)
    have 3: "remdups_mset
       (remove1_mset (- D ! j) (remdups_mset (mset (take j D) + CD))) =
      remdups_mset (remove1_mset (- D ! j) (mset (take j D) + CD))"
      if
        "D ! j \<notin># C" and
        "- D ! j \<notin> set (take j D)" and
        "D ! j \<notin> set (take j D)"
      by (smt \<open>distinct_mset CD\<close> add_diff_cancel_left' add_mset_remove_trivial
          diff_single_trivial diff_union_single_conv3 distinct_mset_add_mset
          in_multiset_in_set insert_DiffM notin_notin_diff_iff remdups_mset_inv remdups_mset_singleton_sum uDj_jD)
    have [simp]: \<open>D ! j \<notin># remove1_mset (- D ! j) (remove1_mset (D ! j) CD)\<close>
      using uDj_jD Dj_D unfolding CD_def
      by (smt Multiset.diff_add \<open>D ! j \<notin># C - add_mset (- D ! j) (add_mset (D ! j) (mset (take j D) + uminus `# mset (take j D)))\<close> add_diff_cancel_left' add_mset_add_single diff_union_single_conv3 in_multiset_in_set notin_notin_diff_iff)
    have thesis: \<open>((False, conflict_add (D ! j) zs), Some (remdups_mset (remove1_mset (- D ! j)
              (add_mset (D ! j) (remdups_mset (mset (take j D) + (C - (mset (take j D) + uminus `# mset (take j D)))))))))
         \<in> option_conflict_rel\<close>
      using  conflict_add_option_conflict_rel[OF ocr lits Dj, unfolded surjective_pairing[symmetric]] .

    have \<open>literals_are_in_N\<^sub>0 (remdups_mset (mset (take x1 D) + (C - mset (take x1 D) - uminus `# mset (take x1 D))))\<close>
      using \<open>D ! j \<in># N\<^sub>1\<close> by (auto simp: take_Suc_conv_app_nth
          conflict_merge'_step_def Let_def in_remove1_mset_neq
          literals_are_in_N\<^sub>0_add_mset)
    moreover {
      have CD': \<open>C - add_mset (- D ! j) (add_mset (D ! j) (mset (take j D) + uminus `# mset (take j D)))
           = CD - {#-D!j, D!j#}\<close>
        unfolding CD_def by auto
      have CD'': \<open>C - (mset (take j D) + uminus `# mset (take j D)) = CD\<close>
        unfolding CD_def by auto
      have [simp]: \<open>D ! j \<notin># remove1_mset (- D ! j) (remove1_mset (D ! j) (mset (take j D) + CD))\<close>
        using uDj_jD Dj_D by (auto simp: diff_union_single_conv3)

      have \<open>remdups_mset (remove1_mset (- D ! j) (remdups_mset (mset (take j D) + CD))) =
        add_mset (D ! j) (remdups_mset (mset (take j D) + (CD - {#- D ! j, D ! j#})))\<close>
        if \<open>D ! j \<in># CD\<close>
      proof -
        have \<open>remdups_mset (remove1_mset (- D ! j) (remdups_mset (mset (take j D) + CD))) =
          remdups_mset (add_mset (D ! j) (remove1_mset (D ! j) (remove1_mset (- D ! j) (mset (take j D) + CD))))\<close>
          using uDj_jD Dj_D that by (auto simp: in_remove1_mset_neq in_CD_uCD remdups_mset_inv)
        also have \<open>\<dots> = remdups_mset (add_mset (D ! j) (remove1_mset (- D ! j) (remove1_mset (D ! j) (mset (take j D) + CD))))\<close>
          by (subst diff_right_commute[of _ \<open>{#D!j#}\<close> \<open>{#-D!j#}\<close>]) auto
        finally show ?thesis
          using uDj_jD Dj_D that
          by (auto simp del: diff_diff_add_mset remdups_mset_singleton_sum
              simp: diff_diff_add_mset[symmetric] diff_add_mset_remove1 notin_add_mset_remdups_mset
                diff_union_single_conv3[symmetric])
      qed
      moreover have \<open>remdups_mset (remove1_mset (- D ! j) (remdups_mset (mset (take j D) + CD))) =
        remdups_mset (mset (take j D) + (CD - {#- D ! j, D ! j#}))\<close> if \<open>D ! j \<notin># CD\<close>
        using uDj_jD Dj_D that "3" DJ_in_CD
        by (auto simp: diff_add_mset_remove1 diff_union_single_conv3[symmetric])
      ultimately have \<open>((False, fst x2, snd x2), Some (remdups_mset (mset (take x1 D) + (C - mset (take x1 D) - uminus `# mset (take x1 D)))))
      \<in> option_conflict_rel\<close>
        using uDj_jD Dj_D by (fastforce simp: take_Suc_conv_app_nth
          conflict_merge'_step_def Let_def in_remove1_mset_neq
          diff_union_single_conv3 CD' CD_def[symmetric] CD''
          intro!: H[OF thesis]) }
    ultimately show ?thesis
      unfolding conflict_merge'_step_def Let_def by simp
  qed
  have dist_D: \<open>distinct_mset (mset D)\<close>
    using dist by auto
  have dist_CD: \<open>distinct_mset (C - mset D - uminus `# mset D)\<close>
    using \<open>distinct_mset C\<close> by auto

  have confl: \<open>conflict_merge D (b, n, xs)
    \<le> \<Down> option_conflict_rel
       (RETURN (Some (mset D \<union># (C - mset D - uminus `# mset D))))\<close>
    unfolding conflict_merge_aa_def conflict_merge_def PR_CONST_def
    distinct_mset_rempdups_union_mset[OF dist_D dist_CD]
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(j, _). length D - j)\<close> and
          I' = \<open>\<lambda>(i, zs). conflict_merge'_step i zs D C\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: upperN_def)
    subgoal using Suc_N_upperN by auto
    subgoal using assms by (simp add: upperN_def conflict_merge'_step_def option_conflict_rel_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for b' n' s i zs by (cases \<open>snd s\<close>) (auto simp: conflict_add_def split: if_splits)
    subgoal for b' n' s j zs
      using dist lits tauto
      by (auto simp: option_conflict_rel_def take_Suc_conv_app_nth
          literals_are_in_N\<^sub>0_in_N\<^sub>1)
    subgoal for b' n' s j zs using assms
      by (cases zs) (auto simp add: conflict_add_def conflict_merge'_step_def Let_def)
    subgoal for b' n' s j zs
      by (rule inv)
    subgoal by auto
    subgoal using assms by (auto simp: option_conflict_rel_def conflict_merge'_step_def Let_def)
    done
  have count_D: \<open>count (mset D) a = 1 \<or> count (mset D) a = 0\<close> for a
    using dist_D unfolding distinct_mset_def by auto
  have count_C: \<open>count C a = 1 \<or> count C a = 0\<close> for a
    using \<open>distinct_mset C\<close> unfolding distinct_mset_def by auto
  have \<open>mset D \<union># (C - mset D - image_mset uminus (mset D)) = mset D \<union># (C - image_mset uminus (mset D))\<close>
    apply (rule multiset_eqI)
    subgoal for a
      using count_D[of a] count_C[of a] by (auto simp: max_def)
    done
  then show ?thesis
    using confl by simp
qed

lemma conflict_merge_aa_mark_conflict:
  \<open>(uncurry2 conflict_merge_aa, uncurry2(RETURN ooo set_conflict)) \<in>
    [\<lambda>((N, i), xs). i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
       literals_are_in_N\<^sub>0 (mset (N ! i)) \<and> \<not>tautology (mset (N ! i))]\<^sub>f
    \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<rightarrow>
      \<langle>option_conflict_rel\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>\<not>tautology (mset C) \<Longrightarrow> j < length C \<Longrightarrow> -C ! j \<notin> set (take j C)\<close> for j C
    by (meson in_multiset_in_set in_set_takeD nth_mem_mset tautology_minus)
  have [simp]: \<open>distinct C \<Longrightarrow> j < length C \<Longrightarrow> C ! j \<notin> set (take j C)\<close> for j C
    by (simp add: index_nth_id index_take)
  have H: \<open>conflict_merge_aa N i (b, n, xs) \<le> \<Down> option_conflict_rel (RETURN (Some (mset (N ! i))))\<close>
    if
      \<open>i < length N\<close> and
      ocr: \<open>((b, n, xs), None) \<in> option_conflict_rel\<close> and
     dist: \<open>distinct (N! i)\<close> and
     lits: \<open>literals_are_in_N\<^sub>0 (mset (N ! i))\<close> and
     tauto: \<open>\<not>tautology (mset (N ! i))\<close>
    for b n xs N i
  proof -
    have [simp]: \<open>remdups_mset (mset (N ! i)) = mset (N!i)\<close>
      using distinct_mset_remdups_mset_id[of \<open>mset (N!i)\<close>] dist by auto
    have conflict_merge_normalise: \<open>conflict_merge C (b, zs) = conflict_merge C (False, zs)\<close> for C zs
      unfolding conflict_merge_def by auto
    have T: \<open>((False, n, xs), Some {#}) \<in> option_conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def by auto
    then show ?thesis unfolding conflict_merge_aa_def
      using conflict_merge'_spec[of False n xs \<open>{#}\<close> \<open>N!i\<close>] that dist
      by (auto simp: conflict_merge_normalise)
  qed
  show ?thesis
    unfolding conflict_merge_def set_conflict_def uncurry_def
    by (intro nres_relI frefI) (auto simp: H)
qed

theorem conflict_merge_code_mark_conflict[sepref_fr_rules]:
  \<open>(uncurry2 conflict_merge_code, uncurry2 (RETURN \<circ>\<circ>\<circ> set_conflict)) \<in>
  [\<lambda>((N, i), xs). i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
    literals_are_in_N\<^sub>0 (mset (N ! i)) \<and> \<not> tautology (mset (N ! i))]\<^sub>a
  clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> conflict_option_assn\<close>
   (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>(uncurry2 conflict_merge_code, uncurry2 (RETURN \<circ>\<circ>\<circ> set_conflict))
  \<in> [comp_PRE (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel)
      (\<lambda>((N, i), xs). i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
          literals_are_in_N\<^sub>0 (mset (N ! i)) \<and> \<not> tautology (mset (N ! i)))
      (\<lambda>_ ((N, i), _, xs). i < length N \<and> (\<forall>j<length (N ! i). atm_of (N ! i ! j) < length (snd xs)))
      (\<lambda>_. True)]\<^sub>a
    hrp_comp (clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (bool_assn *assn uint32_nat_assn *assn
                       array_assn (option_assn bool_assn))\<^sup>d)
            (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel) \<rightarrow>
    hr_comp (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn))
        option_conflict_rel\<close>
   (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF conflict_merge_code.refine[unfolded PR_CONST_def]
        conflict_merge_aa_mark_conflict[unfolded PR_CONST_def], OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def in_br_conv list_mset_rel_def in_N\<^sub>1_atm_of_in_atms_of_iff
        literals_to_update_wl_empty_def option_conflict_rel_def conflict_rel_def
        dest: literals_are_in_N\<^sub>0_in_N\<^sub>1)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp conflict_option_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have post: \<open>?f' = ?f\<close>
    by (auto simp: twl_st_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       conflict_option_assn_def)
  show ?thesis using H unfolding PR_CONST_def pre post im .
qed

lemma unit_prop_body_wl_invD:
  fixes S w K
  defines \<open>C \<equiv> (watched_by S K) ! w\<close>
  assumes inv: \<open>unit_prop_body_wl_inv S w K\<close>
  shows \<open>distinct((get_clauses_wl S)!C)\<close> and \<open>get_conflict_wl S = None\<close>
proof -
  obtain M N U D' NP UP Q W where
     S: \<open>S = (M, N, U, D', NP, UP, Q, W)\<close>
    by (cases S)
  have
     struct_invs: \<open>twl_struct_invs (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))\<close> and
     \<open>additional_WS_invs (st_l_of_wl (Some (K, w)) S)\<close> and
     corr: \<open>correct_watching S\<close> and
     \<open>w < length (watched_by S K)\<close> and
     confl: \<open>get_conflict_wl S = None\<close> and
     w_ge_0: \<open>0 < watched_by S K ! w\<close> and
     w_le_length: \<open>w < length (watched_by S K)\<close> and
     w_le_length_S: \<open>watched_by S K ! w < length (get_clauses_wl S)\<close>
    using inv unfolding unit_prop_body_wl_inv_def by fast+

  show \<open>get_conflict_wl S = None\<close>
    using confl .
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
       (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close> and
      \<open>\<forall>D\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))).
      \<not> tautology D\<close>
      and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
    (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close>
    using struct_invs unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>distinct_mset_set (mset ` set (tl N))\<close>
    apply (subst append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
    apply (subst set_append)
    apply (subst image_Un)
    apply (subst distinct_mset_set_union)
    using dist
    by (auto simp: C_def S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset drop_Suc)
  moreover have NC: \<open>N!C \<in> set (tl N)\<close>
     using w_ge_0 w_le_length_S unfolding C_def S
     by (auto intro!: nth_in_set_tl)
  ultimately show \<open>distinct((get_clauses_wl S)!C)\<close>
     unfolding distinct_mset_set_def S by simp
qed

lemma (in -)[sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)

fun watched_by_int:: \<open>twl_st_wl_int \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, U, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, W) = W\<close>

fun (in -) get_watched_wl_int :: \<open>twl_st_wl_int \<Rightarrow> nat list list\<close> where
  \<open>get_watched_wl_int (_, _, _, _, _, W, _) = W\<close>

definition (in -) watched_by_app_int :: \<open>twl_st_wl_int \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app_int = (\<lambda>(M, N, U, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

lemma watched_by_app_watched_by_app_int:
  \<open>(uncurry2 (RETURN ooo watched_by_app_int), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_ref \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_int_def watched_by_app_def twl_st_ref_def map_fun_rel_def)

sepref_thm watched_by_app_int_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_int)\<close>
  :: \<open>[\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_int S) \<and> K < length (watched_by_int S L)]\<^sub>a
        twl_st_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_int_def twl_st_int_assn_def nth_rll_def[symmetric]
  by sepref

concrete_definition (in -) watched_by_app_int_code
   uses twl_array_code.watched_by_app_int_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_int_code_def

lemmas watched_by_app_int_code_refine[sepref_fr_rules] =
   watched_by_app_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma watched_by_app_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 watched_by_app_int_code, uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K).  L \<in> snd ` D\<^sub>0 \<and> K < length (watched_by S L)]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 watched_by_app_int_code, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_by_app))
  \<in> [comp_PRE (twl_st_ref \<times>\<^sub>f Id \<times>\<^sub>f nat_rel)
      (\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L))
      (\<lambda>_ ((S, L), K).
          nat_of_lit L < length (get_watched_wl_int S) \<and>
          K < length (watched_by_int S L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_ref \<times>\<^sub>f Id \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF watched_by_app_int_code_refine[unfolded PR_CONST_def]
        watched_by_app_watched_by_app_int[unfolded PR_CONST_def]] .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def twl_st_assn_def twl_st_ref_def map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

(* TODO Move *)
lemma (in -) twl_struct_invs_length_clause_ge_2:
  assumes
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    i: \<open>i > 0\<close> \<open>i < length (get_clauses_wl S)\<close>
 shows \<open>length (get_clauses_wl S ! i) \<ge> 2\<close>
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)
  have \<open>twl_st_inv (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) (M, N, U, D, NP, UP, WS, Q)))\<close>
    using struct unfolding S twl_struct_invs_def by fast
  then have \<open>\<forall>x\<in>set (tl N). 2 \<le> length x \<and> distinct x\<close>
    by (auto simp: twl_st_inv.simps mset_take_mset_drop_mset')
  then show ?thesis
    using i by (auto simp: nth_in_set_tl S)
qed
(* End Move *)


lemma unit_prop_body_wl_D_invD:
  assumes \<open>unit_prop_body_wl_D_inv S w L\<close>
  shows
    \<open>w < length (watched_by S L)\<close> and
    \<open>watched_by_app S L w < length (get_clauses_wl S)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close> and
    \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    \<open>watched_by_app S L w > 0\<close> and
    \<open>literals_are_N\<^sub>0 S\<close> and
    \<open>get_conflict_wl S = None\<close> and
    \<open>literals_are_in_N\<^sub>0 (mset (get_clauses_wl S ! watched_by_app S L w))\<close> and
(*     \<open>\<not> tautology (mset (get_clauses_wl S ! watched_by_app S L w))\<close> and *)
    \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
proof -
  show \<open>L \<in> snd ` D\<^sub>0\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def by fast
  show \<open>w < length (watched_by S L)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by fast
  show S_L_W_le_S: \<open>watched_by_app S L w < length (get_clauses_wl S)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast
  show \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      additional_WS_invs_def by force
  show le: \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      additional_WS_invs_def by force
  have nempty: \<open>get_clauses_wl S \<noteq> []\<close> and S_L_w_ge_0: \<open>0 < watched_by_app S L w\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    additional_WS_invs_def watched_by_app_def by auto
  obtain M N U D NP UP W Q where
    S: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_N\<^sub>0 (mset (get_clauses_wl S ! watched_by_app S L w))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def apply -
    apply (rule literals_are_in_N\<^sub>0_nth[of _ _ M U D NP UP Q W])
    apply (rule S_L_W_le_S)
    apply (rule S_L_w_ge_0)
    using S by (auto simp del: twl_st_of.simps)
  then show \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close>
    using le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>)
    by (auto simp: literals_are_in_N\<^sub>0_def all_lits_of_m_add_mset)

  show \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close>
    using lits_N le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>;
        cases \<open>tl (tl (get_clauses_wl S ! watched_by_app S L w))\<close>)
    by (auto simp: literals_are_in_N\<^sub>0_def all_lits_of_m_add_mset)

  show S_L_W_ge_0: \<open>watched_by_app S L w > 0\<close> and \<open>literals_are_N\<^sub>0 S\<close> and \<open>get_conflict_wl S = None\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    stgy: \<open>twl_stgy_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    all_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
          (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))). \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L)
            (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>\<forall>D\<in>mset ` set (tl (get_clauses_wl S)). distinct_mset D\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    unfolding set_append
    using dist
    apply (cases S)
    by (auto simp: drop_Suc cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset
        watched_by_app_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct)
  then show \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
    using S_L_W_le_S S_L_W_ge_0 nempty
    by (cases S; cases \<open>get_clauses_wl S\<close>)
       (auto simp:  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct
         cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset watched_by_app_def)
qed

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) ! i ! j\<close>

definition (in -) access_lit_in_clauses_int where
  \<open>access_lit_in_clauses_int = (\<lambda>(M, N, _) i j.  N ! i ! j)\<close>


sepref_thm access_lit_in_clauses_int_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_int)\<close>
  :: \<open>[\<lambda>(((_,N,_), i), j). i < length N \<and> j < length_rll N i]\<^sub>a
      twl_st_int_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp]
  unfolding twl_st_int_assn_def access_lit_in_clauses_int_def
  by sepref

concrete_definition (in -) access_lit_in_clauses_int_code
   uses twl_array_code.access_lit_in_clauses_int_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_int_code_def

lemmas access_lit_in_clauses_int_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma access_lit_in_clauses_int_access_lit_in_clauses:
  \<open>(uncurry2 (RETURN ooo access_lit_in_clauses_int), uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
   twl_st_ref \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: access_lit_in_clauses_int_def twl_st_ref_def access_lit_in_clauses_def)

lemma access_lit_in_clauses_refine[sepref_fr_rules]:
  \<open>(uncurry2 access_lit_in_clauses_int_code, uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
    [\<lambda>((S, i), j). i < length (get_clauses_wl S) \<and> j < length_rll (get_clauses_wl S) i]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    unat_lit_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 access_lit_in_clauses_int_code, uncurry2 (RETURN \<circ>\<circ>\<circ> access_lit_in_clauses))
  \<in> [comp_PRE (twl_st_ref \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) (\<lambda>_. True)
      (\<lambda>_ (((_, N, _), i), j). i < length N \<and> j < length_rll N i) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_int_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_ref \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF access_lit_in_clauses_int_code_refine[unfolded PR_CONST_def]
        access_lit_in_clauses_int_access_lit_in_clauses[unfolded PR_CONST_def]] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_ref_def
      map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

definition (in -) find_unwatched_wl_s  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_s = (\<lambda>(M, N, U, D, NP, UP, Q, W) i. do {
    find_unwatched_l M (N ! i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S ! C) = find_unwatched_wl_s S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_s_def)

definition find_unwatched_wl_s_int  :: \<open>twl_st_wl_int \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_s_int = (\<lambda>(M, N, U, D, Q, W, vm, \<phi>) i. do {
    find_unwatched M (N ! i)
  })\<close>

paragraph \<open>Value of a literal\<close>

definition (in -) valued_trail :: \<open>trail_int \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>valued_trail = (\<lambda>(M, xs, lvls, k) L. do {
     ASSERT(atm_of L < length xs);
     (case xs ! (atm_of L) of
       None \<Rightarrow> RETURN None
     | Some v \<Rightarrow> if is_pos L then RETURN (Some v)
       else RETURN (Some (\<not>v)))
  })\<close>

sepref_thm valued_trail_code
  is \<open>uncurry valued_trail\<close>
  :: \<open>trailt_conc\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_trail_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) valued_trail_code
   uses twl_array_code.valued_trail_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) valued_trail_code_def

lemmas valued_trail_code_valued_refine_code[sepref_fr_rules] =
   valued_trail_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

lemma valued_trail_code_valued_refine[sepref_fr_rules]:
  \<open>(uncurry valued_trail_code, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>valued_atm_on_trail M (atm_of L) = (if is_pos L then valued M L else map_option uminus (valued M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: valued_atm_on_trail_def valued_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry valued_trail, uncurry (RETURN oo valued)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trailt_ref \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
      (auto simp: trailt_ref_def valued_def valued_trail_def trailt_ref_def
        split: if_splits option.splits)
  show ?thesis
    using valued_trail_code.refine[FCOMP 2, OF twl_array_code_axioms] .
qed

definition valued_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>valued_st S = valued (get_trail_wl S)\<close>

definition valued_st_int :: \<open>twl_st_wl_int_trail_ref \<Rightarrow> _ \<Rightarrow> bool option nres\<close> where
  \<open>valued_st_int = (\<lambda>(M, _) L. valued_trail M L)\<close>

(* TODO Move? *)
definition twl_st_int_trail_ref_assn :: \<open>twl_st_wl_int_trail_ref \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_int_trail_ref_assn =
  (trailt_conc *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  )\<close>

definition twl_st_trail_ref :: \<open>(twl_st_wl_int_trail_ref \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_trail_ref =
  {((M', N', U', D', Q', W', vm, \<phi>), (M, N, U, D, NP, UP, Q, W)).
    (M', M) \<in> trailt_ref \<and> N' = N \<and> U' = U \<and> D = D' \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_imp M \<and>
    phase_saving \<phi> \<and>
    no_dup M
  }\<close>

lemma twl_st_trail_ref_alt_def:
  \<open>twl_st_trail_ref =
    (trailt_ref \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O twl_st_ref\<close>
  by (force simp: twl_st_trail_ref_def twl_st_ref_def)

lemma twl_st_int_trail_ref_assn_twl_st_int_assn:
  \<open>hr_comp twl_st_int_trail_ref_assn
    (trailt_ref \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) =
     twl_st_int_assn\<close>
  unfolding twl_st_int_trail_ref_assn_def twl_st_int_assn_def
  by simp

lemma twl_st_ref_assn_assn:
  \<open>hr_comp twl_st_int_trail_ref_assn twl_st_trail_ref = twl_st_assn\<close>
  unfolding twl_st_assn_def twl_st_trail_ref_alt_def
  hr_comp_assoc[symmetric] twl_st_int_trail_ref_assn_twl_st_int_assn
  ..

sepref_thm valued_st_int_code
  is \<open>uncurry valued_st_int\<close>
  :: \<open>twl_st_int_trail_ref_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_st_int_def twl_st_int_trail_ref_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) valued_st_int_code
   uses twl_array_code.valued_st_int_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) valued_st_int_code_def

lemmas valued_st_int_code_valued_refine_code[sepref_fr_rules] =
   valued_st_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma valued_st_int_code_valued_st_refine[sepref_fr_rules]:
  \<open>(uncurry valued_st_int_code, uncurry (RETURN oo valued_st)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>valued_atm_on_trail M (atm_of L) = (if is_pos L then valued M L else map_option uminus (valued M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: valued_atm_on_trail_def valued_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry valued_st_int, uncurry (RETURN oo valued_st)) \<in>
     [\<lambda>(_, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_trail_ref \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
       (auto simp: trailt_ref_def valued_st_def valued_trail_def trailt_ref_def
        twl_st_trail_ref_def valued_def valued_st_int_def
        split: if_splits option.splits)
  show ?thesis
    using valued_st_int_code.refine[FCOMP 2, OF twl_array_code_axioms,
      unfolded twl_st_ref_assn_assn] .
qed

sepref_thm find_unwatched_wl_s_int_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_s_int))\<close>
  :: \<open>[\<lambda>(S, i). i < length (get_clauses_wl_int S) \<and> i > 0 \<and> literals_are_in_N\<^sub>0_int S]\<^sub>a
         twl_st_int_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_N\<^sub>0_int_in_D\<^sub>0'[intro]
  unfolding find_unwatched_wl_s_int_def twl_st_int_assn_def PR_CONST_def
  find_unwatched_def
  by sepref

concrete_definition (in -) find_unwatched_wl_s_int_code
   uses twl_array_code.find_unwatched_wl_s_int_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_s_int_code_def

lemmas find_unwatched_wl_s_int_code_find_unwatched_wl_s_int[sepref_fr_rules] =
   find_unwatched_wl_s_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

theorem find_unwatched_wl_s_int_find_unwatched_wl_s:
  \<open>(uncurry find_unwatched_wl_s_int, uncurry find_unwatched_wl_s)
    \<in> [\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_N\<^sub>0 S \<and>
      length (get_clauses_wl S ! i) \<ge> 2]\<^sub>f
      twl_st_ref \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_unwatched_wl_s_def find_unwatched_wl_s_int_def twl_st_ref_def
    find_unwatched)

theorem find_unwatched_wl_s_int_code_find_unwatched_wl_s[sepref_fr_rules]:
  \<open>(uncurry find_unwatched_wl_s_int_code, uncurry find_unwatched_wl_s)
    \<in> [\<lambda>(S, i). \<exists>w L. unit_prop_body_wl_D_inv S w L \<and> i = watched_by_app S L w]\<^sub>a
      twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry find_unwatched_wl_s_int_code, uncurry find_unwatched_wl_s)
    \<in> [comp_PRE (twl_st_ref \<times>\<^sub>f nat_rel)
         (\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_N\<^sub>0 S \<and>
            2 \<le> length (get_clauses_wl S ! i))
         (\<lambda>_ (S, i). i < length (get_clauses_wl_int S) \<and> 0 < i \<and> literals_are_in_N\<^sub>0_int S)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (twl_st_int_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (twl_st_ref \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp (option_assn nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unwatched_wl_s_int_code_find_unwatched_wl_s_int[unfolded PR_CONST_def]
    find_unwatched_wl_s_int_find_unwatched_wl_s] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
  proof -
    have [simp]: \<open>mset `# mset (take ai (tl ah)) + ak + (mset `# mset (drop (Suc ai) ah) + al) =
      mset `# mset (tl ah) + ak + al\<close> for ai ah ak al
      apply (subst (6) append_take_drop_id[of ai, symmetric])
      unfolding mset_append drop_Suc
      by auto
    have [intro]: \<open>literals_are_in_N\<^sub>0_int T\<close> and \<open>get_clauses_wl_int T = get_clauses_wl S\<close> if
       \<open>is_N\<^sub>1 (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close> and
       \<open>(T, S) \<in> twl_st_ref\<close>
      for S and T
      using that apply (auto simp: twl_st_ref_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' clauses_def literals_are_in_N\<^sub>0_int_def)
      apply (auto simp add: all_lits_of_mm_union literals_are_in_N\<^sub>0_mm_def is_N\<^sub>1_def)
      done
    show ?thesis
      unfolding comp_PRE_def
      apply (intro ext impI conjI)
      subgoal
        using that by (auto dest: simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
            unit_propagation_inner_loop_body_l_inv_def watched_by_app_def)
      subgoal
        by (use that in \<open>auto simp: comp_PRE_def unit_prop_body_wl_D_inv_def
            mset_take_mset_drop_mset clauses_def mset_take_mset_drop_mset' drop_Suc
             unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
            unit_propagation_inner_loop_body_l_inv_def twl_st_ref_def
          simp del: twl_st_of.simps st_l_of_wl.simps\<close>)
      done
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma unit_prop_body_wl_D_invI:
  assumes \<open>unit_prop_body_wl_D_inv b ba a\<close>
  shows \<open>watched_by b a ! ba < length (get_clauses_wl b)\<close>
  subgoal
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    by auto
  done

lemmas unit_prop_body_wl_D_invD' =
  unit_prop_body_wl_D_invD[of \<open>(M, N, U, D, NP, UP, WS, Q)\<close> for M N U D NP UP WS Q,
   unfolded watched_by_app_def,
    simplified] unit_prop_body_wl_D_invD(7)

definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, lvls, k).
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)],
      lvls[atm_of L := k], k))\<close>


lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trailt_ref \<rightarrow> \<langle>trailt_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
    (auto simp: trailt_ref_def valued_atm_on_trail_def cons_trail_Propagated_def uminus_lit_swap
        trailt_ref_def cons_trail_Propagated_tr_def
        cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update'
      dest: vmtf_imp_consD)

lemma undefined_lit_count_decided_upperN:
  assumes
    M_N\<^sub>1: \<open>\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>Suc (count_decided M) < upperN\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# N\<^sub>1)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# N\<^sub>1))\<close>
    using length_filter_le[of is_decided M] unfolding upperN_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset N\<^sub>1))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># N\<^sub>1 \<Longrightarrow> atm_of xa < upperN div 2\<close> for xa
    using in_N1_less_than_upperN
    by (cases xa) (auto simp: upperN_def)
  have \<open>remdups_mset (atm_of `# N\<^sub>1) \<subseteq># mset [0..<upperN div 2]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (auto simp del: literal_of_nat.simps simp: distinct_mset_mset_set)
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset N\<^sub>1) = size (remdups_mset N\<^sub>1)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# N\<^sub>1)) \<le> upperN div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: upperN_def)
qed

sepref_thm cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trailt_conc\<^sup>d \<rightarrow> trailt_conc\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_code
  uses "twl_array_code.cons_trail_Propagated_tr_code.refine_raw"
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Propagated_tr_code_def

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] =
  cons_trail_Propagated_tr_code.refine[OF twl_array_code_axioms]

lemma cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
  \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trailt_ref)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trailt_conc\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trailt_ref) \<rightarrow> hr_comp trailt_conc trailt_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr,
        OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trailt_ref_def trailt_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre .
qed

definition mark_conflict_wl' :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>mark_conflict_wl' = (\<lambda>C (M, N, U, D, NP, UP, Q, W). (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))\<close>

lemma mark_conflict_wl'_alt_def:
  \<open>mark_conflict_wl' i S = mark_conflict_wl (get_clauses_wl S ! i) S\<close>
  by (cases S) (auto simp: mark_conflict_wl'_def mark_conflict_wl_def)

definition mark_conflict_wl'_int :: \<open>nat \<Rightarrow> twl_st_wl_int \<Rightarrow> twl_st_wl_int\<close> where
  \<open>mark_conflict_wl'_int = (\<lambda>C (M, N, U, D, Q, W). (M, N, U, set_conflict N C D, {#}, W))\<close>

fun get_conflict_wl_int :: \<open>twl_st_wl_int \<Rightarrow> nat cconflict\<close> where
  \<open>get_conflict_wl_int (_, _, _, D, _) = D\<close>

sepref_thm mark_conflict_wl'_int_code
  is \<open>uncurry (RETURN (* PR_CONST *) oo mark_conflict_wl'_int)\<close>
  :: \<open>[\<lambda>(C, S). get_conflict_wl_int S = None \<and> C < length (get_clauses_wl_int S) \<and>
      distinct (get_clauses_wl_int S ! C) \<and> literals_are_in_N\<^sub>0 (mset (get_clauses_wl_int S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl_int S ! C))]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d \<rightarrow> twl_st_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding mark_conflict_wl'_int_def twl_st_int_assn_def IICF_List_Mset.lms_fold_custom_empty
  by sepref

concrete_definition (in -) mark_conflict_wl'_int_code
  uses "twl_array_code.mark_conflict_wl'_int_code.refine_raw"
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) mark_conflict_wl'_int_code_def

lemmas mark_conflict_wl'_int_code[sepref_fr_rules] =
  mark_conflict_wl'_int_code.refine[OF twl_array_code_axioms]

lemma mark_conflict_wl'_int_mark_conflict_wl':
  \<open>(uncurry (RETURN oo mark_conflict_wl'_int), uncurry (RETURN oo mark_conflict_wl')) \<in>
    nat_rel \<times>\<^sub>r twl_st_ref \<rightarrow>\<^sub>f \<langle>twl_st_ref\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
     (auto simp: twl_st_ref_def mark_conflict_wl'_int_def mark_conflict_wl'_def
        set_conflict_def)

lemma mark_conflict_wl'_int_code_mark_conflict_wl'[sepref_fr_rules]:
  \<open>(uncurry mark_conflict_wl'_int_code, uncurry (RETURN oo mark_conflict_wl')) \<in>
    [\<lambda>(C, S). get_conflict_wl S = None \<and> C < length (get_clauses_wl S) \<and>
      distinct (get_clauses_wl S ! C) \<and> literals_are_in_N\<^sub>0 (mset (get_clauses_wl S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl S ! C))]\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
    twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry mark_conflict_wl'_int_code, uncurry (RETURN \<circ>\<circ> mark_conflict_wl'))
  \<in> [comp_PRE (nat_rel \<times>\<^sub>f twl_st_ref) (\<lambda>_. True)
       (\<lambda>_ (C, S). get_conflict_wl_int S = None \<and> C < length (get_clauses_wl_int S) \<and>
           distinct (get_clauses_wl_int S ! C) \<and> literals_are_in_N\<^sub>0 (mset (get_clauses_wl_int S ! C)) \<and>
           \<not> tautology (mset (get_clauses_wl_int S ! C)))
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (nat_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d) (nat_rel \<times>\<^sub>f twl_st_ref) \<rightarrow>
     hr_comp twl_st_int_assn twl_st_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF mark_conflict_wl'_int_code mark_conflict_wl'_int_mark_conflict_wl']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def by auto
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition update_clause_wl_int :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_int \<Rightarrow>
    (nat \<times> twl_st_wl_int) nres\<close> where
  \<open>update_clause_wl_int = (\<lambda>(L::nat literal) C w i f (M, N, U, D, Q, W, vm). do {
     let K' = (N!C) ! f;
     let N' = list_update N C (swap (N!C) i f);
     let W = W[nat_of_lit L := delete_index_and_swap (W ! nat_of_lit L) w];
     RETURN (w, (M, N', U, D, Q,
            W[nat_of_lit K':= W ! nat_of_lit K' @ [C]],
            vm))
  })\<close>

lemma update_clause_wl_int_update_clause_wl:
  \<open>(uncurry5 update_clause_wl_int, uncurry5 (update_clause_wl)) \<in>
   [\<lambda>(((((L, C), w), i), f), S). (get_clauses_wl S ! C) ! f \<noteq> L]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref \<rightarrow> \<langle>nat_rel \<times>\<^sub>r twl_st_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: update_clause_wl_int_def update_clause_wl_def twl_st_ref_def Let_def
      map_fun_rel_def)

lemma append_el_aa_hnr'[sepref_fr_rules]:
  shows \<open>(uncurry2 (\<lambda>xs i j. append_el_aa xs (nat_of_uint32 i) j), uncurry2 (RETURN ooo append_ll))
     \<in> [\<lambda>((W,L), j). L < length W]\<^sub>a
        (arrayO_assn (arl_assn nat_assn))\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> (arrayO_assn (arl_assn nat_assn))\<close>
    (is \<open>?a \<in> [?pre]\<^sub>a ?init \<rightarrow> ?post\<close>)
  using append_aa_hnr_u[of nat_assn, simplified] unfolding hfref_def  uint32_nat_rel_def br_def pure_def
   hn_refine_def
  by auto

lemma length_delete_index_and_swap_ll[simp]: \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)

sepref_thm update_clause_wl_int_code
  is \<open>uncurry5 update_clause_wl_int\<close>
  :: \<open>
    [\<lambda>(((((L, C), w), i), f), S).
      C < length (get_clauses_wl_int S) \<and>
      f < length (get_clauses_wl_int S ! C) \<and>
      i < length (get_clauses_wl_int S ! C) \<and>
      nat_of_lit L < length (get_watched_wl_int S) \<and>
      nat_of_lit ((get_clauses_wl_int S ! C) ! f)  < length (get_watched_wl_int S) \<and>
      w < length (get_watched_wl_int S ! nat_of_lit L)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d \<rightarrow>
       nat_assn *assn twl_st_int_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_int_def twl_st_int_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric] delete_index_and_swap_ll_def[symmetric]
   append_ll_def[symmetric]
  by sepref


concrete_definition (in -) update_clause_wl_int_code
  uses "twl_array_code.update_clause_wl_int_code.refine_raw"
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_int_code_def

lemmas update_clause_wl_int_code[sepref_fr_rules] =
  update_clause_wl_int_code.refine[OF twl_array_code_axioms]

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S ! watched_by_app S L C))\<close>
    (is ?tauto is \<open>\<not>tautology (?D)\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (watched_by_app S L C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    val: \<open>valued_st S (get_clauses_wl S ! watched_by_app S L C !
         (1 - (if access_lit_in_clauses S (watched_by_app S L C) 0 = L then 0 else 1))) = Some False\<close>
      (is \<open>valued_st _ (_ ! _ ! ?i) = Some False\<close>)
  for S C xj L
proof  -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)

  have \<open>consistent_interp (lits_of_l (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))))\<close>
    \<open>no_dup (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))))\<close> and
    valid: \<open>valid_annotation (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    by (cases S) (auto simp: cdcl\<^sub>W_restart_mset_state)

  have \<open>additional_WS_invs (st_l_of_wl (Some (L, C)) S)\<close> and C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S ! (watched_by S L ! C))).
         - L \<in> lits_of_l (get_trail_wl S)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def watched_by_app_def
    by auto
  moreover {
    have \<open>additional_WS_invs (st_l_of_wl (Some (L, C)) S)\<close> and \<open>C < length (watched_by S L)\<close> and
      \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
    then have \<open>add_mset L WS \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
      apply (cases \<open>drop C (watched_by S L)\<close>)
      apply (simp add: S image_image split: if_splits)
      apply (simp add: S image_image split: if_splits)
      unfolding ex_disj_distrib
      by blast
    from mset_subset_eq_insertD[OF this] have \<open>- L \<in> lits_of_l (convert_lits_l N M)\<close>
      by (auto simp: lits_of_def)
  }
  moreover have \<open>- ?C ! ?i \<in> lits_of_l (convert_lits_l N M)\<close>
    using val by (auto simp: S valued_st_def watched_by_app_def valued_def
        access_lit_in_clauses_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  moreover have length_C: \<open>length ?C \<ge> 2\<close>
    apply (rule twl_struct_invs_length_clause_ge_2)
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by (auto simp: watched_by_app_def)
  moreover {
    have QL: \<open>Q L ! C = hd (drop C (Q L))\<close>
      using confl C_le length_C by (auto simp: S hd_drop_conv_nth split: )
    have \<open>L \<in># mset (watched_l ?C)\<close>
      using valid confl C_le length_C by (auto simp: QL S take_2_if watched_by_app_def)
    then have \<open>N ! (Q L ! C) ! 0 = L \<or> N ! (Q L ! C) ! 1 = L\<close>
      using confl C_le length_C by (auto simp: S take_2_if watched_by_app_def QL split: if_splits)
  }
  ultimately have Not: \<open>lits_of_l (get_trail_wl S) \<Turnstile>s CNot ?D\<close>
    unfolding true_clss_def_iff_negation_in_model
    apply (subst (2) append_take_drop_id[symmetric, of _ 2])
    unfolding mset_append watched_by_app_def access_lit_in_clauses_def
    by (auto simp: S take_2_if hd_conv_nth split: if_splits)
  show ?thesis
    using consistent_CNot_not_tautology[OF cons Not] .
qed

lemma
  find_unwatched_get_clause_neq_L:
    \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<noteq> L\<close> (is ?neq)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv (Some xj) (watched_by S L ! C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof (rule ccontr)
  have is_N\<^sub>1_alt_def_sym: \<open>is_N\<^sub>1 (all_lits_of_mm A) \<longleftrightarrow> atms_of N\<^sub>1 = atms_of_mm A\<close> for A
    unfolding is_N\<^sub>1_alt_def by metis
  assume eq[simplified, simp]: \<open>\<not> ?neq\<close>
  let ?C = \<open>get_clauses_wl S ! watched_by_app S L C\<close>
  let ?L = \<open>get_clauses_wl S ! watched_by_app S L C ! xj\<close>
  have corr: \<open>correct_watching S\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    unfolding correct_watching.simps twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
  moreover have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>watched_by_app S L C > 0\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  ultimately have in_watched: \<open>watched_by_app S L C \<in># mset (watched_by S L)\<close>
    using inv by (auto simp: watched_by_app_def dest: unit_prop_body_wl_D_invD)

  have \<open>literals_are_N\<^sub>0 S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>L \<in> snd ` D\<^sub>0\<close>
    using inv by (auto intro: unit_prop_body_wl_D_invD)
  ultimately have \<open>L \<in># all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)) + get_unit_init_clss S)\<close>
    using alien
    by (cases S)
        (auto 5 5 simp: get_unit_init_clss_def clauses_def mset_take_mset_drop_mset drop_Suc
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        is_N\<^sub>1_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_N\<^sub>1_atm_of_in_atms_of_iff
        dest: in_atms_of_mset_takeD)
    then have H: \<open>mset (watched_by S L) =
      mset_set {x. Suc 0 \<le> x \<and> x < length (get_clauses_wl S) \<and> L \<in> set (watched_l (get_clauses_wl S ! x))}\<close>
      using corr by (cases S)
          (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
          watched_by.simps get_unit_init_clss_def)
  have L_in_watched: \<open>L \<in> set (watched_l ?C)\<close>
    using in_watched unfolding H
    by (cases S)
        (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
        watched_by.simps get_unit_init_clss_def)
  have \<open>xj \<ge> 2\<close> and \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def unit_prop_body_wl_find_unwatched_inv_def
    by (cases S; auto simp: watched_by_app_def)+

  then have L_in_unwatched: \<open>L \<in> set (unwatched_l ?C)\<close>
    by (auto simp: in_set_drop_conv_nth intro!: exI[of _ xj])
  have \<open>distinct_mset_set (mset ` set (tl (get_clauses_wl S)))\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    using dist unfolding  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def set_append
    by (cases S)
        (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset image_Un drop_Suc)
  then have dist_C: \<open>distinct ?C\<close>
    using inv by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset
      intro: unit_prop_body_wl_D_invD)
  then show False
    using L_in_watched L_in_unwatched by (cases ?C; cases \<open>tl ?C\<close>; cases \<open>tl (tl ?C)\<close>) auto
qed

lemma update_clause_wl_int_code_update_clause_wl[sepref_fr_rules]:
  \<open>(uncurry5 update_clause_wl_int_code, uncurry5 update_clause_wl) \<in>
    [\<lambda>(((((L, C), w), i), f), S).
      unit_prop_body_wl_D_inv S w L \<and>
      unit_prop_body_wl_D_find_unwatched_inv (Some f) C S \<and>
      C = watched_by S L ! w \<and>
      i = (if get_clauses_wl S ! C ! 0 = L then 0 else 1)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
       nat_assn *assn twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry5 update_clause_wl_int_code, uncurry5 update_clause_wl) \<in>
    [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref)
       (\<lambda>(((((L, C), w), i), f), S). get_clauses_wl S ! C ! f \<noteq> L)
       (\<lambda>_ (((((L, C), w), i), f), S).
           C < length (get_clauses_wl_int S) \<and>
           f < length (get_clauses_wl_int S ! C) \<and>
           i < length (get_clauses_wl_int S ! C) \<and>
           nat_of_lit L < length (get_watched_wl_int S) \<and>
           nat_of_lit (get_clauses_wl_int S ! C ! f)
           < length (get_watched_wl_int S) \<and>
           w < length (get_watched_wl_int S ! nat_of_lit L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
        twl_st_int_assn\<^sup>d)
      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref) \<rightarrow>
    hr_comp (nat_assn *assn twl_st_int_assn) (nat_rel \<times>\<^sub>f twl_st_ref)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF update_clause_wl_int_code update_clause_wl_int_update_clause_wl]
    .
  have [dest]: \<open>literals_are_in_N\<^sub>0_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
    if \<open>unit_prop_body_wl_D_inv S w L\<close>
    for S w L
  proof -
    have \<open>literals_are_N\<^sub>0 S\<close>
      using that unfolding twl_st_ref_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def by fast
    then  have \<open> set_mset (all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))) \<subseteq>
       set_mset N\<^sub>1\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>get_learned_wl S\<close>])
      unfolding mset_append all_lits_of_mm_union
      apply (cases S)
      by (auto simp:  mset_take_mset_drop_mset' literals_are_in_N\<^sub>0_mm_def clauses_def
           drop_Suc all_lits_of_mm_union is_N\<^sub>1_def)
    then show ?thesis
      unfolding literals_are_in_N\<^sub>0_mm_def by blast
  qed
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    unfolding comp_PRE_def
    apply (cases x)
    apply (clarify)
    apply (intro conjI impI allI)
    subgoal for L C w i f M N U D NP UP Q W
      using that find_unwatched_get_clause_neq_L[of f \<open>(M, N, U, D, NP, UP, Q, W)\<close> L w]
      by (auto simp add: watched_by_app_def)
    subgoal for L C w i f M N U D NP UP Q W y
      apply (subgoal_tac \<open>literals_are_in_N\<^sub>0_mm (mset `# mset (tl N))\<close>)
      subgoal
        using literals_are_in_N\<^sub>0_mm_in_N\<^sub>1[of \<open>tl N\<close> \<open>(W L ! w - 1)\<close> f]
        using that unfolding comp_PRE_def twl_st_ref_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def
        by (auto dest: simp: nth_tl )[]
      subgoal
        using that by auto
      done
    done
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition propgate_lit_wl_int :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> twl_st_wl_int \<Rightarrow> twl_st_wl_int\<close> where
  \<open>propgate_lit_wl_int = (\<lambda>L' C (M, N, U, D, Q, W).
      (Propagated L' C # M, N, U, D, add_mset (-L') Q, W))\<close>

lemma propgate_lit_wl_int_propgate_lit_wl:
  \<open>(uncurry2 (RETURN ooo propgate_lit_wl_int), uncurry2 (RETURN ooo propgate_lit_wl)) \<in>
  [\<lambda>((L, C), S). undefined_lit (get_trail_wl S) L]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref \<rightarrow> \<langle>twl_st_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_ref_def propgate_lit_wl_int_def propgate_lit_wl_def
      vmtf_imp_consD)

sepref_thm propgate_lit_wl_int_code
  is \<open>uncurry2 (RETURN ooo (PR_CONST propgate_lit_wl_int))\<close>
  :: \<open>[\<lambda>((L, C), S). undefined_lit (get_trail_wl_int S) L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d \<rightarrow> twl_st_int_assn\<close>
  unfolding PR_CONST_def propgate_lit_wl_int_def twl_st_int_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) propgate_lit_wl_int_code
  uses "twl_array_code.propgate_lit_wl_int_code.refine_raw"
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propgate_lit_wl_int_code_def

lemmas propgate_lit_wl_int_code[sepref_fr_rules] =
  propgate_lit_wl_int_code.refine[OF twl_array_code_axioms]

lemma propgate_lit_wl_int_code_propgate_lit_wl[sepref_fr_rules]:
  \<open>(uncurry2 propgate_lit_wl_int_code, uncurry2 (RETURN ooo propgate_lit_wl)) \<in>
    [\<lambda>((L, C), S). undefined_lit (get_trail_wl S) L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref)
       (\<lambda>((L, C), S). undefined_lit (get_trail_wl S) L)
       (\<lambda>_ ((L, C), S). undefined_lit (get_trail_wl_int S) L \<and> L \<in> snd ` D\<^sub>0)
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d)
        (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_ref) \<rightarrow>
     hr_comp twl_st_int_assn twl_st_ref
\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propgate_lit_wl_int_code[unfolded PR_CONST_def]
       propgate_lit_wl_int_propgate_lit_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def
    by (auto simp: image_image)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma undefined_lit_valued_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow> valued_st S L \<noteq> Some True \<and> valued_st S L \<noteq> Some False\<close>
  by (auto simp: valued_st_def valued_def)

lemma find_unwatched_le_length:
  \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_s S (watched_by_app S L C)\<close>
  for S L C xj
  using that unfolding find_unwatched_wl_s_def find_unwatched_l_def
  by (cases S) auto

lemma find_unwatched_in_D\<^sub>0: \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in> snd ` D\<^sub>0\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_s S (watched_by_app S L C)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof -
  have \<open>literals_are_N\<^sub>0 S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover {
    have xj: \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
      using find_unw by (cases S) (auto simp: find_unwatched_wl_s_def find_unwatched_l_def)
    have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close> \<open>watched_by_app S L C > 0\<close>
      using inv by (blast intro: unit_prop_body_wl_D_invD)+
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
      using xj
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset watched_by.simps
          in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def nth_in_set_tl
          intro!: bexI[of _ \<open>get_clauses_wl S ! watched_by_app S L C\<close>])
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))\<close>
      apply (subst (asm)(3) append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
      unfolding mset_append
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset' watched_by.simps
          all_lits_of_mm_union drop_Suc) }
  ultimately show ?thesis
    by (auto simp: image_image is_N\<^sub>1_def)
qed

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context twl_array_code
begin

sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  supply
    if_splits[split] unit_prop_body_wl_D_invD[intro,dest]
    watched_by_app_def[symmetric,simp]
    access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro]
    length_rll_def[simp] find_unwatched_not_tauto[dest]
  supply undefined_lit_valued_st_iff[iff]
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_app_def[symmetric] access_lit_in_clauses_def[symmetric]
    find_unwatched_l_find_unwatched_wl_s
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  find_unwatched_wl_s_int_def[symmetric] valued_st_def[symmetric]
  mark_conflict_wl'_alt_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_body_wl_D.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

sepref_register unit_propagation_inner_loop_body_wl_D

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_int :: \<open>twl_st_wl_int \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_int = (\<lambda>(M, N, U, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>

lemma length_ll_fs_int_length_ll_fs:
    \<open>(uncurry (RETURN oo length_ll_fs_int), uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_ref \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: length_ll_fs_def length_ll_fs_int_def twl_st_ref_def map_fun_rel_def)

lemma (in -) get_watched_wl_int_def: \<open>get_watched_wl_int = (\<lambda>(M, N, U, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) (auto intro!: ext)

sepref_thm length_ll_fs_int_code
  is \<open>uncurry (RETURN oo length_ll_fs_int)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_int S)]\<^sub>a twl_st_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_int_def get_watched_wl_int_def twl_st_int_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_int_code
   uses twl_array_code.length_ll_fs_int_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_int_code_def

lemmas length_ll_fs_int_code_refine[sepref_fr_rules] =
   length_ll_fs_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma length_ll_fs_int_code_length_ll_fs[sepref_fr_rules]:
  \<open>(uncurry length_ll_fs_int_code, uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
thm hfref_compI_PRE_aux[OF length_ll_fs_int_code_refine length_ll_fs_int_length_ll_fs]
  have H: \<open>?fun \<in> [comp_PRE (twl_st_ref \<times>\<^sub>f Id) (\<lambda>(S, L). L \<in> snd ` D\<^sub>0)
    (\<lambda>_ (S, L). nat_of_lit L < length (get_watched_wl_int S))
    (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                   (twl_st_ref \<times>\<^sub>f Id) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_ll_fs_int_code_refine length_ll_fs_int_length_ll_fs]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def
    by (auto simp: image_image map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma length_ll_fs_alt_def: \<open>length_ll_fs S L = length_ll_f (watched_by S) L\<close>
  by (cases S) (auto simp: length_ll_fs_def length_ll_f_def)

definition (in -) get_conflict_wl_is_None_int :: \<open>twl_st_wl_int \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_int = (\<lambda>(M, N, U, D, Q, W, _). is_None D)\<close>

lemma get_conflict_wl_is_None_int_get_conflict_wl_is_None:
    \<open>(RETURN o get_conflict_wl_is_None_int,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_ref \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_ref_def get_conflict_wl_is_None_int_def get_conflict_wl_is_None_def
     split: option.splits)

sepref_thm get_conflict_wl_is_None_int_code
  is \<open>RETURN o get_conflict_wl_is_None_int\<close>
  :: \<open>twl_st_int_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_int_def get_watched_wl_int_def twl_st_int_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_int_code
   uses twl_array_code.get_conflict_wl_is_None_int_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_int_code_def

lemmas get_conflict_wl_is_None_int_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma get_conflict_wl_is_None_int_code_get_conflict_wl_is_None[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_int_code, RETURN o get_conflict_wl_is_None) \<in>
     twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_int_code_refine[FCOMP get_conflict_wl_is_None_int_get_conflict_wl_is_None]
  unfolding twl_st_assn_def by fast

sepref_register unit_propagation_inner_loop_wl_loop_D

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric] length_ll_fs_alt_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None length_ll_fs_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

paragraph \<open>Unit propagation, inner loop\<close>

sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms]


paragraph \<open>Unit propagation, outer loop\<close>

type_synonym (in -) twl_st_wl_int_W_list =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat literal list \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_int
  :: \<open>twl_st_wl_int_W_list \<Rightarrow> twl_st_wl_int_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_int =
     (\<lambda>(M, N, U, D, Q, W, other).  ((M, N, U, D, tl Q, W, other), hd Q))\<close>

definition twl_st_wl_int_W_list_rel :: \<open>(twl_st_wl_int_W_list \<times> twl_st_wl_int) set\<close> where
  \<open>twl_st_wl_int_W_list_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     (Id :: (nat cconflict \<times> _)set) \<times>\<^sub>r
     (list_mset_rel :: (nat literal list \<times> nat lit_queue_wl) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id\<close>

definition twl_st_int_W_list_rel_assn :: \<open>twl_st_wl_int_W_list \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_int_W_list_rel_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  (list_assn unat_lit_assn) *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  )\<close>

lemma twl_st_wl_int_W_list_rel_twl_st_rel: \<open>twl_st_wl_int_W_list_rel O twl_st_ref =
   {((M', N', U', D', Q', W', vm, \<phi>), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     D = D' \<and>
     (Q', Q) \<in> list_mset_rel \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf_imp M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_ref_def twl_st_wl_int_W_list_rel_def
  by force

lemma twl_st_int_assn_W_list:
  \<open>twl_st_int_assn = hr_comp twl_st_int_W_list_rel_assn twl_st_wl_int_W_list_rel\<close>
  unfolding twl_st_int_assn_def twl_st_int_W_list_rel_assn_def twl_st_wl_int_W_list_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn)

lemma twl_st_assn_W_list:
  \<open>twl_st_assn = hr_comp twl_st_int_W_list_rel_assn (twl_st_wl_int_W_list_rel O twl_st_ref)\<close>
  apply (subst hr_comp_assoc[symmetric])
  apply (subst twl_st_int_assn_W_list[symmetric])
  unfolding twl_st_assn_def ..


definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q)\<close>

definition get_literals_to_update_wl_int_W_list where
   \<open>get_literals_to_update_wl_int_W_list = (\<lambda>(M, N, U, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_int_empty :: \<open>twl_st_wl_int_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_int_empty = (\<lambda>(M, N, U, D, Q, W, oth). Q = [])\<close>

lemma select_and_remove_from_literals_to_update_wl_int_select_and_remove_from_literals_to_update_wl:
  \<open>(RETURN o select_and_remove_from_literals_to_update_wl_int,
    select_and_remove_from_literals_to_update_wl) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>f
      (twl_st_wl_int_W_list_rel O twl_st_ref) \<rightarrow>
       \<langle>(twl_st_wl_int_W_list_rel O twl_st_ref) \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_int_def
  select_and_remove_from_literals_to_update_wl_def get_literals_to_update_wl_int_W_list_def
  twl_st_wl_int_W_list_rel_twl_st_rel get_literals_to_update_wl_def
  literals_to_update_wl_empty_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y,
      case_tac \<open>get_literals_to_update_wl_int_W_list y\<close>)
  unfolding get_literals_to_update_wl_def get_literals_to_update_wl_int_W_list_def
  by (auto intro!: RETURN_SPEC_refine simp: nempty_list_mset_rel_iff)

sepref_thm select_and_remove_from_literals_to_update_wl_int_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_int\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_int_empty S]\<^sub>a twl_st_int_W_list_rel_assn\<^sup>d \<rightarrow> twl_st_int_W_list_rel_assn *assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_int_def twl_st_int_W_list_rel_assn_def
    literals_to_update_wl_int_empty_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) select_and_remove_from_literals_to_update_wl_int_code
   uses twl_array_code.select_and_remove_from_literals_to_update_wl_int_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_int_code_def

lemmas select_and_remove_from_literals_to_update_wl_int_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

theorem select_and_remove_from_literals_to_update_wl_int_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_int_code,
     select_and_remove_from_literals_to_update_wl)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty S]\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *assn
          unat_lit_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun
    \<in> [comp_PRE (twl_st_wl_int_W_list_rel O twl_st_ref)
         (\<lambda>S. \<not> literals_to_update_wl_empty S)
         (\<lambda>_ S. \<not> literals_to_update_wl_int_empty S)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_int_W_list_rel_assn\<^sup>d) (twl_st_wl_int_W_list_rel O twl_st_ref) \<rightarrow>
      hr_comp (twl_st_int_W_list_rel_assn *assn unat_lit_assn)
           ((twl_st_wl_int_W_list_rel O twl_st_ref) \<times>\<^sub>f Id)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_int_code_refine
      select_and_remove_from_literals_to_update_wl_int_select_and_remove_from_literals_to_update_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def literals_to_update_wl_int_empty_def
      literals_to_update_wl_empty_def twl_st_wl_int_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm literals_to_update_wl_int_empty_code
  is \<open>RETURN o literals_to_update_wl_int_empty\<close>
  :: \<open>twl_st_int_W_list_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_int_def twl_st_int_W_list_rel_assn_def
    literals_to_update_wl_int_empty_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_int_empty_code
   uses twl_array_code.literals_to_update_wl_int_empty_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_int_empty_code_def

lemmas literals_to_update_wl_int_empty_code_refine[sepref_fr_rules] =
   literals_to_update_wl_int_empty_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

lemma literals_to_update_wl_int_empty_literals_to_update_wl_empty:
  \<open>(RETURN o literals_to_update_wl_int_empty, RETURN o literals_to_update_wl_empty) \<in>
    twl_st_wl_int_W_list_rel O twl_st_ref \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding literals_to_update_wl_int_empty_def literals_to_update_wl_empty_def
    twl_st_wl_int_W_list_rel_twl_st_rel
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: Nil_list_mset_rel_iff empty_list_mset_rel_iff)

lemma literals_to_update_wl_int_empty_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_int_empty_code, RETURN \<circ> literals_to_update_wl_empty)
     \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_int_empty_code_refine[FCOMP literals_to_update_wl_int_empty_literals_to_update_wl_empty]
  unfolding twl_st_assn_W_list[symmetric]
  .

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref


paragraph \<open>Skip and resolve\<close>

definition get_conflict_wll_is_Nil_int :: \<open>twl_st_wl_int \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil_int = (\<lambda>(M, N, U, D, Q, W, _).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>

sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil_int)\<close>
  :: \<open>twl_st_int_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_int_def twl_st_int_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses twl_array_code.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma get_conflict_wll_is_Nil_int_get_conflict_wll_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil_int, get_conflict_wll_is_Nil) \<in> twl_st_ref \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: get_conflict_wll_is_Nil_int_def get_conflict_wll_is_Nil_def twl_st_ref_def
      split: option.splits)

lemma get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, get_conflict_wll_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code[FCOMP get_conflict_wll_is_Nil_int_get_conflict_wll_is_Nil]
  unfolding twl_st_assn_def[symmetric] .

lemma get_conflict_wll_is_Nil_code_get_conflict_wl_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN \<circ> get_conflict_wl_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[FCOMP
   get_conflict_wll_is_Nil_get_conflict_wl_is_Nil[unfolded PR_CONST_def]]
  by auto

lemma in_literals_are_in_N\<^sub>0_in_D\<^sub>0:
  assumes \<open>literals_are_in_N\<^sub>0 D\<close> and \<open>L \<in># D\<close>
  shows \<open>L \<in> snd ` D\<^sub>0\<close>
  using assms by (cases L) (auto simp: image_image literals_are_in_N\<^sub>0_def all_lits_of_m_def)


paragraph \<open>Level of a literal\<close>

definition get_level_trail :: \<open>trail_int \<Rightarrow> uint32 \<Rightarrow> nat\<close> where
  \<open>get_level_trail = (\<lambda>(M, xs, lvls, k) L. lvls ! (nat_of_uint32 (L >> 1)))\<close>

sepref_thm get_level_code
  is \<open>uncurry (RETURN oo get_level_trail)\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), L). nat_of_uint32 L div 2 < length lvls]\<^sub>a
  trailt_conc\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_trail_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_code
   uses twl_array_code.get_level_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_code_def

lemmas get_level_code_get_level_code[sepref_fr_rules] =
   get_level_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

lemma get_level_code_get_level[sepref_fr_rules]:
  \<open>(uncurry get_level_code, uncurry (RETURN oo get_level)) \<in>
   [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [simp]: \<open>(ba, bb) \<in> nat_lit_rel \<Longrightarrow> ba div 2 = atm_of bb\<close> for ba bb
    by (auto simp: p2rel_def lit_of_natP_def atm_of_lit_of_nat nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 1: \<open>(uncurry (RETURN oo get_level_trail), uncurry (RETURN oo get_level)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trailt_ref \<times>\<^sub>f unat_lit_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI, rename_tac x y, case_tac x) (auto simp: image_image trailt_ref_def get_level_trail_def
        nat_shiftr_div2 shiftr1_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        nat_of_uint32_shiftr trailt_ref_def)

  have H: \<open>(uncurry get_level_code, uncurry (RETURN \<circ>\<circ> get_level))
\<in> [comp_PRE (trailt_ref \<times>\<^sub>f unat_lit_rel)
     (\<lambda>(M, L). L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((M, xs, lvls, k), L).
         nat_of_uint32 L div 2 < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (trailt_conc\<^sup>k *\<^sub>a
                      uint32_assn\<^sup>k)
                     (trailt_ref \<times>\<^sub>f
                      unat_lit_rel) \<rightarrow> hr_comp
                 uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_code.refine 1, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trailt_ref_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
      trailt_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed

(* TODO: get_level M (Pos i) is inefficient (i*2 div 2) *)
definition maximum_level_remove' :: \<open>(nat, nat) ann_lits \<Rightarrow> conflict_rel \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>maximum_level_remove'  = (\<lambda>M (n, xs) L. do {
       S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, lev, n). i \<le> length xs \<and>
               n = size (filter_mset (op \<noteq> None) (mset (nths xs {i..<length xs})))\<^esup>
             (\<lambda>(i, lev, n). n > 0)
             (\<lambda>(i, lev, n). do {
                  ASSERT(i < length xs);
                  ASSERT(i < upperN - 1);
                  ASSERT(n > 0);
                  if xs ! i = None then RETURN (i+1, lev, n)
                  else
                    if i = atm_of L then
                      RETURN (i+1, lev, n - 1)
                    else do{ ASSERT(Pos i \<in># N\<^sub>1); RETURN (i+1, max (get_level M (Pos i)) lev, n - 1)}
                }
             )
             (0, 0, n);
       RETURN (fst (snd S))
     })
     \<close>

sepref_register maximum_level_remove'
sepref_thm maximum_level_remove_code
  is \<open>uncurry2 (PR_CONST maximum_level_remove')\<close>
  :: \<open>trail_assn\<^sup>k *\<^sub>a (uint32_nat_assn *assn array_assn (option_assn bool_assn))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k
       \<rightarrow>\<^sub>a
       uint32_nat_assn\<close>
  unfolding maximum_level_remove'_def[abs_def] zero_uint32_def[symmetric] one_nat_uint32_def[symmetric]
    fast_minus_def[symmetric] upperN_def PR_CONST_def
  supply in_literals_are_in_N\<^sub>0_in_D\<^sub>0[intro] one_nat_uint32_def[simp] fast_minus_def[simp]
  supply uint32_nat_assn_zero_uint32[sepref_fr_rules] Pot_unat_lit_assn[sepref_fr_rules]
  supply [[goals_limit = 1]]
  apply (rewrite in "ASSERT (\<hole> < length _)" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite in "If _ _ (If _ (RETURN (_, \<hole>, _)) _)" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite in "If _ (RETURN (_, \<hole>, _)) _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite in "\<lambda>(i, lev, y). \<hole> < _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite in "_ + \<hole>" annotate_assn[where A=uint32_nat_assn])
  by sepref

concrete_definition (in -) maximum_level_remove_code
   uses twl_array_code.maximum_level_remove_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms maximum_level_remove_code_def

lemmas select_and_remove_from_literals_to_update_wl''_code[sepref_fr_rules] =
   maximum_level_remove_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma maximum_level_remove'_get_maximum_level_remove:
  \<open>(uncurry2 maximum_level_remove', uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    [\<lambda>((M, D), L). literals_are_in_N\<^sub>0 D \<and> L \<in># D]\<^sub>f
      Id \<times>\<^sub>f conflict_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  define maximum_level_remove'' :: \<open>(nat, nat) ann_lits \<Rightarrow> conflict_rel \<Rightarrow> nat literal \<Rightarrow>
       (nat \<times> nat \<times> nat) nres\<close> where
    \<open>maximum_level_remove''  = (\<lambda>M (n, xs) L. do {
        WHILE\<^sub>T\<^bsup>\<lambda>(i, lev, n). i \<le> length xs \<and>
               n = size (filter_mset (op \<noteq> None) (mset (nths xs {i..<length xs})))\<^esup>
             (\<lambda>(i, lev, n). n > 0)
             (\<lambda>(i, lev, n). do {
                  ASSERT(i < length xs);
                  ASSERT(i < upperN - 1);
                  ASSERT(n > 0);
                  if xs ! i = None then RETURN (i+1, lev, n)
                  else
                    if i = atm_of L then
                      RETURN (i+1, lev, n - 1)
                    else do{ ASSERT(Pos i \<in># N\<^sub>1); RETURN (i+1, max (get_level M (Pos i)) lev, n - 1)}
                }
             )
             (0, 0, n)
       })
       \<close>
  have maximum_level_remove''_def:  \<open>maximum_level_remove'' M (n, xs) L = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, lev, n). i \<le> length xs \<and>
               n = size (filter_mset (op \<noteq> None) (mset (nths xs {i..<length xs})))\<^esup>
             (\<lambda>(i, lev, n). n > 0)
             (\<lambda>(i, lev, n). do {
                  ASSERT(i < length xs);
                  ASSERT(i < upperN - 1);
                  ASSERT(n > 0);
                  if xs ! i = None then RETURN (i+1, lev, n)
                  else
                    if i = atm_of L then
                      RETURN (i+1, lev, n - 1)
                    else do{ ASSERT(Pos i \<in># N\<^sub>1); RETURN (i+1, max (get_level M (Pos i)) lev, n - 1)}
                }
             )
             (0, 0, n)
       }\<close> for M xs L n
    unfolding maximum_level_remove''_def by fast
  have size_ge_0_notnil: \<open>a < length xs'\<close>
    if \<open>0 < size (filter_mset (op \<noteq> None) (mset (nths xs' {a..<length xs'})))\<close>
    for xs' a
    by (rule ccontr) (use that in auto)
  have [iff]: \<open>(\<not> atm_of L < a \<and> atm_of L = a) \<longleftrightarrow> atm_of L = (a :: nat)\<close> for a L
    by auto
  let ?f = \<open>\<lambda>L C. replicate_mset (count C L) L\<close>
  have filter_eq: \<open>{#L \<in># C. atm_of L = a#} = ?f (Pos a) C + ?f (Neg a) C
    \<close> for C a
    apply (rule multiset_eqI, rename_tac x)
    by (case_tac x, auto simp: multiset_eq_iff count_eq_zero_iff)

  have filter_le_Suc:
    \<open>{#L \<in># C. atm_of L < Suc a#} = ?f (Pos a) C + ?f (Neg a) C + {#L \<in># C. atm_of L < a#}\<close>
    for L C a f
    by (cases \<open>Pos (Suc a) \<in># C\<close>; cases \<open>Neg (Suc a) \<in># C\<close>)
       (auto simp: less_Suc_eq filter_union_or_split filter_eq)
  have count0:
    \<open>count C (Pos a) = 0\<close> \<open> count C (Neg a) = 0\<close>
    if \<open>x2 ! a = None\<close> and \<open>mset_as_position x2 C\<close> \<open>a < length x2\<close>
    for x2 a C
    using mset_as_position_nth[of x2 C \<open>Pos a\<close>]
      mset_as_position_nth[of x2 C \<open>Neg a\<close>]  that
    by (auto simp: count_eq_zero_iff)
  have Suc_minus_Suc_Suc:
    \<open>Suc (2 * a) - (b + c) < Suc (Suc (2 * a)) - (b + c)\<close>
    if \<open>b < a\<close> \<open>c < a\<close> for a b c
    using that by auto
  have Suc_minus_Suc_Suc':
    \<open>(2 * a) - (b + c) < (Suc (2 * a)) - (b + c)\<close>
    if \<open>b < a\<close> \<open>c < a\<close> for a b c
    using that by auto
  have length_filter_le: \<open>length (filter (op \<noteq> None) (nths x2 {a..<length x2})) < length x2\<close>
    if \<open>x2 ! a = None\<close> \<open>a < length x2 \<close>
    for a x2
  proof -
    have \<open>length (filter P (nths x2 A)) \<le> length (filter P x2)\<close> for P A
      apply (induction x2 arbitrary: A)
      subgoal by auto
      subgoal premises IH for a x2 A
        using IH[of \<open>{j. Suc j \<in> A}\<close>] by (auto simp: nths_Cons)
      done
    then have \<open>length (filter (op \<noteq> None) (nths x2 {a..<length x2})) \<le>
        length (filter (op \<noteq> None) x2)\<close>
      by auto
    also have \<open>length (filter (op \<noteq> None) x2) < length x2\<close>
      apply (rule length_filter_less[of \<open>x2!a\<close>])
      using that by (auto dest!: nth_mem)
    finally show ?thesis .
  qed
  have maximum_level_remove'': \<open>maximum_level_remove'' M (n, xs) L \<le> \<Down> Id
     (SPEC(\<lambda>(i, lev, n). lev = get_maximum_level_remove M C L))\<close>
    if xs: \<open>mset_as_position xs C\<close> and n_C: \<open>n = size C\<close> and L_C: \<open>L \<in># C\<close> and
     N\<^sub>0: \<open>literals_are_in_N\<^sub>0 C\<close>
    for xs C M n K L
  proof -
    have Pos_in_N\<^sub>1: \<open>Pos a \<in># N\<^sub>1\<close>
      if \<open>a < length xs\<close> and
         \<open>xs ! a \<noteq> None\<close>
       for a
    proof -
      have \<open>Pos a \<in># C \<or> Neg a \<in># C\<close>
        using mset_as_position_in_iff_nth[OF xs, of \<open>Pos a\<close>]
            mset_as_position_in_iff_nth[OF xs, of \<open>Neg a\<close>] that
        by auto
      then show ?thesis
        using N\<^sub>0
        by (metis atm_iff_pos_or_neg_lit in_N\<^sub>1_atm_of_in_atms_of_iff in_clause_in_all_lits_of_m
            literal.sel(1) literals_are_in_N\<^sub>0_def subsetCE)
    qed
    have count_L: \<open>count C L = 1\<close>
      using L_C mset_as_position_distinct_mset[OF xs] unfolding distinct_mset_def by blast
    then have count_uL: \<open>count C (-L) = 0\<close>
      using mset_as_position_nth[OF xs, of \<open>-L\<close>] mset_as_position_nth[OF xs, of L]
      by (cases L) (auto simp: count_greater_zero_iff[symmetric] simp del: count_greater_zero_iff)
    have count_C: \<open>count C a = 0 \<or> count C a = 1\<close> for a
      using L_C mset_as_position_distinct_mset[OF xs] unfolding distinct_mset_count_less_1
      by (cases \<open>count C a\<close>; cases \<open>count C a - 1\<close>)
        (auto dest: HOL.spec[of _ a])
    have count_1_neg: \<open>count C a = 1 \<Longrightarrow> count C (-a) = 0\<close> for a
      using mset_as_position_nth[OF xs, of \<open>-a\<close>] mset_as_position_nth[OF xs, of a]
      by (cases a) (auto simp: count_greater_zero_iff[symmetric] simp del: count_greater_zero_iff)
    have mset_as_position_SomeD:
      \<open>count C (Pos a) = 1 \<or> count C (Neg a) = 1\<close> if \<open>x2 ! a = Some y\<close> and xs: \<open>mset_as_position x2 C\<close> and \<open>a < length x2\<close>
      for a x2 y
      using that mset_as_position_in_iff_nth[OF xs, of \<open>Pos a\<close>] mset_as_position_in_iff_nth[OF xs, of \<open>Neg a\<close>]
      count_1_neg[of \<open>Pos a\<close>] count_1_neg[of \<open>Neg a\<close>] count_C[of \<open>Pos a\<close>] count_C[of \<open>Neg a\<close>]
      by (cases \<open>x2 ! a\<close>) (auto simp: count_greater_zero_iff[symmetric] simp del: count_greater_zero_iff)
    have [simp]: \<open>get_level M (Neg a) = get_level M (Pos a)\<close> for a
      using get_level_uminus[of M \<open>Neg a\<close>] by auto
    have H: \<open>filter_mset (op \<noteq> None) (mset (nths x2 {x1a..<length x2})) = {#} \<Longrightarrow>
        {#L \<in># C. atm_of L < x1a#} = C\<close> if xs: \<open>mset_as_position x2 C\<close> for x2 x1a
      apply (rule multiset_eqI)
      subgoal for x
        using that mset_as_position_in_iff_nth[OF xs, of x] (* TODO Proof *)
        apply (auto simp: filter_mset_empty_conv Ball_set_nths Ball_atLeastLessThan_iff
            count_greater_zero_iff[symmetric] simp del: count_greater_zero_iff)
        by (meson count_inI mset_as_position_atm_le_length)
      done
    have le_upperN_1: "a < upperN - 1"
      if
        nempty: "case s of
          (i, lev, n) \<Rightarrow>
           i \<le> length xs \<and>
           n = size (filter_mset (op \<noteq> None) (mset (nths xs {i..<length xs})))" and
        m: "case s of
         (i, lev, n) \<Rightarrow>
           mset_as_position xs C \<and>
           lev = get_maximum_level_remove M {#L \<in># C. atm_of L < i#} L" and
        n: "case s of (i, lev, xa) \<Rightarrow> 0 < xa" and
        s: "s = (a, b)" "b = (aa, ba)" and
        a: "a < length xs"
      for s a b aa ba
    proof (rule ccontr)
      assume F: \<open>\<not> ?thesis\<close>
      from nempty n obtain i where
        \<open>xs ! i \<noteq> None\<close> and i_a: \<open>i \<in> {a..<length xs}\<close>
        by (force simp: filter_mset_empty_conv nonempty_has_size[symmetric] set_nths s)
      then have \<open>Pos i \<in># C \<or> Neg i \<in># C\<close>
        using m mset_as_position_in_iff_nth[of xs C \<open>Pos i\<close>] mset_as_position_in_iff_nth[of xs C \<open>Neg i\<close>]
          a by auto
      then have \<open>Pos i \<in># N\<^sub>1 \<or> Neg i \<in># N\<^sub>1\<close>
        using in_literals_are_in_N\<^sub>0_in_D\<^sub>0[OF N\<^sub>0, of \<open>Pos i\<close>] in_literals_are_in_N\<^sub>0_in_D\<^sub>0[OF N\<^sub>0, of \<open>Neg i\<close>]
        by (auto simp: image_image)
      then have \<open>i < upperN div 2\<close>
        using in_N1_less_than_upperN by (auto simp: upperN_def)
      moreover have \<open>i \<ge> upperN - 1\<close>
        using i_a F by (auto simp: not_less_eq)
      ultimately show False by linarith
    qed
    show ?thesis
      unfolding maximum_level_remove''_def
      apply (refine_vcg WHILEIT_rule_stronger_inv[where
            R = \<open>measure (\<lambda>(i, lev, n). length xs + 2 - i + n)\<close> and
            I' = \<open>\<lambda>(i, lev, n). mset_as_position xs C \<and> lev = get_maximum_level_remove M (filter_mset (\<lambda>L. atm_of L < i) C) L\<close>])
      subgoal by auto
      subgoal by auto
      subgoal
        using xs n_C by (auto simp: mset_filter[symmetric] mset_as_position_length_not_None)
      subgoal using xs by auto
      subgoal by (auto simp: get_maximum_level_remove_def)
      subgoal for n' xs' by (auto dest: size_ge_0_notnil)
      subgoal for s a b aa ba by (rule le_upperN_1)
      subgoal by auto
      subgoal by auto
      subgoal using xs by (auto simp: nths_upt_Suc')
      subgoal using xs by auto
      subgoal using xs by (auto simp: count0 get_maximum_level_remove_def filter_le_Suc)
      subgoal by (auto simp: mset_filter[symmetric] length_filter_le
            intro!: Suc_minus_Suc_Suc)
      subgoal by auto
      subgoal by (auto simp: nths_upt_Suc')
      subgoal by auto
      subgoal
        using count_L count_uL
        by (cases L)
           (auto simp: nths_upt_Suc' get_maximum_level_remove_def filter_le_Suc
            get_maximum_level_add_mset)
      subgoal by auto
      subgoal by (auto simp: Pos_in_N\<^sub>1)
      subgoal by auto
      subgoal by (auto simp: nths_upt_Suc')
      subgoal by auto
      subgoal for s a b aa ba x1 x2 x1a x2a
        using count_L count_uL count_C[of \<open>Pos a\<close>] count_C[of \<open>Neg a\<close>]
        count_1_neg[of \<open>Pos a\<close>] count_1_neg[of \<open>Neg a\<close>]
        apply (cases L) by (auto simp: filter_le_Suc nths_upt_Suc'
            get_maximum_level_remove_def get_maximum_level_add_mset
            dest!: mset_as_position_SomeD)
      subgoal by (auto simp: nths_upt_Suc')
      subgoal by (auto simp: nths_upt_Suc' H)
      done
  qed

  show ?thesis
    apply (intro frefI nres_relI ext)
    unfolding maximum_level_remove'_def get_maximum_level_remove_def uncurry_def
      maximum_level_remove''_def[symmetric]
    subgoal for x y (* TODO proof *)
      apply (cases x; cases \<open>fst x\<close>; cases y)
      apply auto
      apply (refine_vcg maximum_level_remove'')
      apply (rule order.trans)
       apply (rule maximum_level_remove'')
      by (auto simp: conflict_rel_def get_maximum_level_remove_def)
    done
qed

lemma maximum_level_remove_code_get_maximum_level_remove[sepref_fr_rules]:
  \<open>(uncurry2 maximum_level_remove_code,
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    [\<lambda>((M, D), L). literals_are_in_N\<^sub>0 D \<and> L \<in># D]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f conflict_rel \<times>\<^sub>f Id)
        (\<lambda>((M, D), L). literals_are_in_N\<^sub>0 D \<and> L \<in># D) (\<lambda>_ _. True)
        (\<lambda>_. True)]\<^sub>a
      hrp_comp ((hr_comp trailt_conc trailt_ref)\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
               (Id \<times>\<^sub>f conflict_rel \<times>\<^sub>f Id) \<rightarrow>
      hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl''_code[unfolded PR_CONST_def]
      maximum_level_remove'_get_maximum_level_remove]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def literals_to_update_wl_int_empty_def
      literals_to_update_wl_empty_def twl_st_wl_int_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric] conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition is_decided_hd_trail_wl_int :: \<open>twl_st_wl_int \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_int = (\<lambda>(M, _). is_decided (hd M))\<close>

lemma is_decided_hd_trail_wl_int_is_decided_hd_trail_wl:
  \<open>(RETURN o is_decided_hd_trail_wl_int, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_ref \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: is_decided_hd_trail_wl_int_def is_decided_hd_trail_wl_def twl_st_ref_def)

lemma get_trail_wl_int_def: \<open>get_trail_wl_int = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

definition hd_trail_code :: \<open>trail_int_assn \<Rightarrow> uint32 \<times> nat option\<close> where
  \<open>hd_trail_code = (\<lambda>(M, _). hd M)\<close>

lemma hd_trail_code_hd[sepref_fr_rules]:
  \<open>(return o hd_trail_code, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>k \<rightarrow> pair_nat_ann_lit_assn\<close>
  unfolding hd_trail_code_def op_list_hd_def
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>fst (xi)\<close>)
  apply (sep_auto simp:  trailt_ref_def hr_comp_def)+
  done

sepref_thm is_decided_hd_trail_wl_int_code
  is \<open>RETURN o is_decided_hd_trail_wl_int\<close>
  :: \<open>[\<lambda>S. get_trail_wl_int S \<noteq> []]\<^sub>a twl_st_int_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_int_def twl_st_int_assn_def
    supply get_trail_wl_int_def[simp]
  by sepref


concrete_definition (in -) is_decided_hd_trail_wl_int_code
   uses twl_array_code.is_decided_hd_trail_wl_int_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms is_decided_hd_trail_wl_int_code_def

lemmas is_decided_hd_trail_wl_int_code[sepref_fr_rules] =
   is_decided_hd_trail_wl_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma is_decided_hd_trail_wl_int_code_is_decided_hd_trail_wl[sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wl_int_code, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_ref (\<lambda>S. get_trail_wl S \<noteq> []) (\<lambda>_ S. get_trail_wl_int S \<noteq> [])
        (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_int_assn\<^sup>k)
                     twl_st_ref \<rightarrow> hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_decided_hd_trail_wl_int_code
      is_decided_hd_trail_wl_int_is_decided_hd_trail_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def literals_to_update_wl_int_empty_def
      literals_to_update_wl_empty_def twl_st_wl_int_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric] conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma get_trail_twl_st_of_wl_get_trail_wl_empty_iff:
  \<open>get_trail (twl_st_of None (st_l_of_wl None S)) = [] \<longleftrightarrow> get_trail_wl S = []\<close>
  by (cases S) auto

definition (in -) is_in_conflict :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> bool\<close> where
  \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

definition (in -) is_in_conflict_option_assn :: \<open>nat literal \<Rightarrow> (bool \<times> nat \<times> bool option list) \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_option_assn = (\<lambda>L (_, _, xs). xs ! atm_of L = Some (is_pos L))\<close>

lemma is_in_conflict_option_assn_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_conflict_option_assn), uncurry (RETURN oo is_in_conflict)) \<in>
     [\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r option_conflict_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  subgoal for Lxs LC
    using conflict_rel_atm_in_iff[of _ \<open>snd (snd (snd Lxs))\<close>]
    apply (cases Lxs)
    by (auto simp: is_in_conflict_option_assn_def is_in_conflict_def option_conflict_rel_def)
  done

sepref_definition (in -) is_in_conflict_option_assn_code
  is \<open>uncurry (RETURN oo is_in_conflict_option_assn)\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_in_conflict_option_assn_def
  by sepref


lemma is_in_conflict_option_assn_code_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry is_in_conflict_option_assn_code,
     uncurry (RETURN oo is_in_conflict)) \<in>
    [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_N\<^sub>0 (the C) \<and> C \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f option_conflict_rel) (\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0)
          (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>k) (Id \<times>\<^sub>f option_conflict_rel)
       \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_in_conflict_option_assn_code.refine is_in_conflict_option_assn_is_in_conflict]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] conflict_assn_def conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition literal_is_in_conflict :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict L S \<longleftrightarrow> L \<in># the (get_conflict_wl S)\<close>

definition literal_is_in_conflict_int :: \<open>nat literal \<Rightarrow> twl_st_wl_int \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict_int = (\<lambda>L (M, N, U, D, _). L \<in># the D)\<close>

lemma literal_is_in_conflict_int_literal_is_in_conflict:
  \<open>(uncurry (RETURN oo literal_is_in_conflict_int), uncurry (RETURN oo literal_is_in_conflict)) \<in>
   Id \<times>\<^sub>r twl_st_ref \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (auto simp: literal_is_in_conflict_int_def literal_is_in_conflict_def twl_st_ref_def)

sepref_thm literal_is_in_conflict_int_code
  is \<open>uncurry (RETURN oo literal_is_in_conflict_int)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and> get_conflict_wl_int S \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding literal_is_in_conflict_int_def twl_st_int_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def
  by sepref

concrete_definition (in -) literal_is_in_conflict_int_code
   uses twl_array_code.literal_is_in_conflict_int_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) literal_is_in_conflict_int_code_def

lemmas literal_is_in_conflict_int_code_refine[sepref_fr_rules] =
   literal_is_in_conflict_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma literal_is_in_conflict_int_code_literal_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry literal_is_in_conflict_int_code,
     uncurry (RETURN oo literal_is_in_conflict)) \<in>
    [\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_N\<^sub>0 (the (get_conflict_wl S)) \<and> get_conflict_wl S \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f twl_st_ref) (\<lambda>_. True)
         (\<lambda>_ (L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and>
           get_conflict_wl_int S \<noteq> None)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>k) (Id \<times>\<^sub>f twl_st_ref) \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF literal_is_in_conflict_int_code_refine literal_is_in_conflict_int_literal_is_in_conflict]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_ref_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_int :: \<open>twl_st_wl_int \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st_int = (\<lambda>(M, _). (lit_of (hd M), mark_of (hd M)))\<close>

lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in> [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+

sepref_thm lit_and_ann_of_propagated_st_int_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_int\<close>
  :: \<open>[\<lambda>S. is_proped (hd (get_trail_wl_int S)) \<and> get_trail_wl_int S \<noteq> []]\<^sub>a
       twl_st_int_assn\<^sup>k \<rightarrow> (unat_lit_assn *assn nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_int_def[simp]
  unfolding lit_and_ann_of_propagated_st_int_def twl_st_int_assn_def
  by sepref

concrete_definition (in -) lit_and_ann_of_propagated_st_int_code
   uses twl_array_code.lit_and_ann_of_propagated_st_int_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_and_ann_of_propagated_st_int_code_def

lemmas lit_and_ann_of_propagated_st_int_code_refine[sepref_fr_rules] =
   lit_and_ann_of_propagated_st_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma lit_and_ann_of_propagated_st_int_lit_and_ann_of_propagated_st:
   \<open>(RETURN o lit_and_ann_of_propagated_st_int, RETURN o lit_and_ann_of_propagated_st) \<in>
   [\<lambda>S. is_proped (hd (get_trail_wl S))]\<^sub>f twl_st_ref \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y; case_tac x; case_tac y; case_tac \<open>hd (fst x)\<close>)
  by (auto simp: twl_st_ref_def lit_and_ann_of_propagated_st_int_def lit_and_ann_of_propagated_st_def)

lemma lit_and_ann_of_propagated_st_refine[sepref_fr_rules]:
  \<open>(lit_and_ann_of_propagated_st_int_code,
     (RETURN o lit_and_ann_of_propagated_st)) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> is_proped (hd (get_trail_wl S))]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn *assn nat_assn \<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_ref (\<lambda>S. is_proped (hd (get_trail_wl S)))
         (\<lambda>_ S. is_proped (hd (get_trail_wl_int S)) \<and> get_trail_wl_int S \<noteq> [])
         (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_int_assn\<^sup>k) twl_st_ref \<rightarrow>
    hr_comp (unat_lit_assn *assn nat_assn) (Id \<times>\<^sub>f nat_rel)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF lit_and_ann_of_propagated_st_int_code_refine lit_and_ann_of_propagated_st_int_lit_and_ann_of_propagated_st]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_ref_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma skip_and_resolve_hd_in_D\<^sub>0:
  assumes
    L: "(L, a2'a) = lit_and_ann_of_propagated_st a2'" and
    is_proped: "is_proped (hd (get_trail_wl a2'))" and
    struct: "twl_struct_invs (twl_st_of None (st_l_of_wl None a2'))" and
    nempty: "get_trail_wl a2' \<noteq> []" and
    N\<^sub>1: "is_N\<^sub>1
      (all_lits_of_mm
        (cdcl\<^sub>W_restart_mset.clauses
          (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))))"
   shows "- L \<in> snd ` D\<^sub>0"
proof -
  obtain M' where
    M': \<open>get_trail_wl a2' = Propagated L a2'a # M'\<close>
    using is_proped L nempty by (cases \<open>get_trail_wl a2'\<close>; cases \<open>hd (get_trail_wl a2')\<close>)
      (auto simp: lit_and_ann_of_propagated_st_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
    using N\<^sub>1 M' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases a2')
     (auto simp: cdcl\<^sub>W_restart_mset_state image_image mset_take_mset_drop_mset'
        in_N\<^sub>1_atm_of_in_atms_of_iff clauses_def is_N\<^sub>1_alt_def)
qed


definition tl_state_wl_int :: \<open>twl_st_wl_int \<Rightarrow> twl_st_wl_int\<close> where
  \<open>tl_state_wl_int = (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>).
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of (lit_of (hd M))) vmtf, \<phi>))\<close>

lemma tl_state_wl_int_alt_def:
    \<open>tl_state_wl_int =  (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>).
      (let L = lit_of (hd M) in
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of L) vmtf, \<phi>)))\<close>
  by (auto simp: tl_state_wl_int_def Let_def)

definition (in twl_array_code_ops) tl_trailt_tr :: \<open>trail_int \<Rightarrow> trail_int\<close> where
  \<open>tl_trailt_tr = (\<lambda>(M', xs, lvls, k). (tl M', xs[atm_of (lit_of (hd M')) := None], lvls[atm_of (lit_of (hd M')) := 0],
    if is_decided (hd M') then k-1 else k))\<close>

sepref_thm tl_trail_tr_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[\<lambda>(M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs  \<and> atm_of (lit_of (hd M)) < length lvls \<and>
    (is_decided (hd M) \<longrightarrow> k \<ge> 1)]\<^sub>a
        trailt_conc\<^sup>d \<rightarrow> trailt_conc\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_def
  apply (rewrite at \<open>_ - 1\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_zero[sepref_fr_rules]
  by sepref

concrete_definition (in -) tl_trail_tr_code
  uses twl_array_code.tl_trail_tr_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_code_def

lemmas tl_trail_tr_coded_refine[sepref_fr_rules] =
   tl_trail_tr_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma tl_trail_tr:
  \<open>((RETURN o tl_trailt_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trailt_ref \<rightarrow> \<langle>trailt_ref\<rangle>nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trailt_ref_def comp_def RETURN_refine_iff trailt_ref_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal by (auto simp: trailt_ref_def valued_atm_on_trail_def tl_trailt_tr_def)
      subgoal by (auto simp: trailt_ref_def valued_atm_on_trail_def tl_trailt_tr_def)
      subgoal by (auto simp: valued_atm_on_trail_def tl_trailt_tr_def)
      subgoal
        by (cases \<open>lit_of L\<close>)
            (auto simp: valued_atm_on_trail_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: tl_trailt_tr_def in_N\<^sub>1_atm_of_in_atms_of_iff
            dest: no_dup_consistentD abs_l_vmtf_unset_vmtf_unset')
      subgoal
        by (auto simp: tl_trailt_tr_def)
      done
    done
qed

lemma tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
  \<open>(tl_trail_tr_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, b), x) \<in> trailt_ref \<Longrightarrow> x = a\<close> for a aa ab b x
    by (auto simp: trailt_ref_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
  have H: \<open>(tl_trail_tr_code, RETURN \<circ> tl)
      \<in> [comp_PRE trailt_ref (\<lambda>M. M \<noteq> [])
            (\<lambda>_ (M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and>
             atm_of (lit_of (hd M)) < length lvls \<and> (is_decided (hd M) \<longrightarrow> 1 \<le> k))
            (\<lambda>_. True)]\<^sub>a
         hrp_comp (trailt_conc\<^sup>d) trailt_ref \<rightarrow> hr_comp trailt_conc trailt_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_code.refine tl_trail_tr, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trailt_ref_def phase_saving_def
        in_N\<^sub>1_atm_of_in_atms_of_iff vmtf_imp_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre by simp
qed

fun get_vmtf_int :: \<open>twl_st_wl_int \<Rightarrow> _\<close> where
  \<open>get_vmtf_int (M, N, U, D, WS, W, vmtf, _) = vmtf\<close>

end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context twl_array_code
begin

lemma literals_are_N\<^sub>0_hd_trail_in_D\<^sub>0:
  assumes
    N\<^sub>1: \<open>literals_are_N\<^sub>0 S\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    nil: \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
     using nil N\<^sub>1 by (cases S; cases \<open>get_trail_wl S\<close>)
        (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
          in_N\<^sub>1_atm_of_in_atms_of_iff image_image mset_take_mset_drop_mset' clauses_def
          is_N\<^sub>1_alt_def)
qed

sepref_thm tl_state_wl_int_code
  is \<open>RETURN o tl_state_wl_int\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, ((A, m, lst, next_search), _), \<phi>). M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A)]\<^sub>a
      twl_st_int_assn\<^sup>d \<rightarrow> twl_st_int_assn\<close>
  supply [[goals_limit=1]] option.splits[split] get_vmtf_int.simps[simp] if_splits[split]
  option.splits[split]
  supply [[goals_limit=1]] option.splits[split] get_vmtf_int.simps[simp] literals_are_N\<^sub>0_hd_trail_in_D\<^sub>0[intro]
  unfolding tl_state_wl_int_alt_def[abs_def] twl_st_int_assn_def get_trail_wl_int_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp]
    short_circuit_conv
  by sepref


concrete_definition (in -) tl_state_wl_int_code
  uses twl_array_code.tl_state_wl_int_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_state_wl_int_code_def

lemmas tl_state_wl_int_code_refine[sepref_fr_rules] =
   tl_state_wl_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma tl_state_wl_int_tl_state_wl: \<open>(RETURN o tl_state_wl_int, RETURN o tl_state_wl) \<in>
  [\<lambda>S. get_trail_wl S \<noteq> [] \<and> lit_of(hd (get_trail_wl S)) \<in> snd ` D\<^sub>0]\<^sub>f twl_st_ref \<rightarrow> \<langle>twl_st_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: twl_st_ref_def tl_state_wl_int_def tl_state_wl_def abs_l_vmtf_unset_vmtf_unset'
    in_N\<^sub>1_atm_of_in_atms_of_iff phase_saving_def dest: no_dup_tlD)

lemma tl_state_wl_refine[sepref_fr_rules]:
  \<open>(tl_state_wl_int_code, RETURN o tl_state_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of None (st_l_of_wl None S))]\<^sub>a
      twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
   \<in> [comp_PRE twl_st_ref
        (\<lambda>S. get_trail_wl S \<noteq> [] \<and> lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0)
         (\<lambda>_ (M, N, U, D, WS, Q, ((A, m, lst, next_search), _), \<phi>).
            M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length \<phi> \<and>
            atm_of (lit_of (hd M)) < length A \<and>
             (next_search \<noteq> None \<longrightarrow> the next_search < length A))
            (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_int_assn\<^sup>d) twl_st_ref \<rightarrow> hr_comp twl_st_int_assn twl_st_ref\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF tl_state_wl_int_code_refine tl_state_wl_int_tl_state_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_N\<^sub>0_hd_trail_in_D\<^sub>0[of x]
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_ref_def phase_saving_def in_N\<^sub>1_atm_of_in_atms_of_iff
      vmtf_imp_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition (in -) get_max_lvl_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>get_max_lvl_st S L = get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L\<close>

lemma (in -) get_max_lvl_st_alt_def:
  \<open>get_max_lvl_st = (\<lambda>(M, N, U, D, _) L. get_maximum_level_remove M (the D) L)\<close>
  unfolding get_max_lvl_st_def
  by (intro ext, rename_tac S L, case_tac S) auto


type_synonym (in -) twl_st_wl_int_conflict =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    (bool \<times> nat \<times> bool option list) \<times> nat literal multiset \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>


definition get_max_lvl_st_int :: \<open>twl_st_wl_int_conflict \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>get_max_lvl_st_int = (\<lambda>(M, N, U, (_, D), _) L. maximum_level_remove' M (D) L)\<close>

definition twl_st_wl_int_conflict_rel :: \<open>(twl_st_wl_int_conflict \<times> twl_st_wl_int) set\<close> where
  \<open>twl_st_wl_int_conflict_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     (option_conflict_rel :: _ set) \<times>\<^sub>r
     (Id :: (nat lit_queue_wl \<times> _) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id\<close>

definition twl_st_int_conflict_assn :: \<open>twl_st_wl_int_conflict \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_int_conflict_assn =
  trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_rel_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  \<close>

lemma twl_st_wl_int_conflict_rel_twl_st_rel: \<open>twl_st_wl_int_conflict_rel O twl_st_ref =
   {((M', N', U', D', Q', W', vm, \<phi>), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf_imp M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_ref_def twl_st_wl_int_conflict_rel_def
  by force

lemma get_max_lvl_st_int_get_max_lvl_st:
  \<open>(uncurry (PR_CONST get_max_lvl_st_int), uncurry (RETURN oo get_max_lvl_st)) \<in>
   [\<lambda>((M, N, U, D, _), L). literals_are_in_N\<^sub>0 (the D) \<and> L \<in># the D \<and> D \<noteq> None]\<^sub>f
   (twl_st_wl_int_conflict_rel O twl_st_ref) \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  using maximum_level_remove'_get_maximum_level_remove[unfolded fref_def nres_rel_def]
  unfolding get_max_lvl_st_int_def get_max_lvl_st_def twl_st_wl_int_conflict_rel_twl_st_rel
  apply (intro frefI nres_relI)
  by (auto simp: option_conflict_rel_def)

lemma twl_st_int_assn_int_conflict_assn:
  \<open>twl_st_int_assn = hr_comp twl_st_int_conflict_assn twl_st_wl_int_conflict_rel\<close>
  unfolding twl_st_int_assn_def twl_st_int_conflict_assn_def
    twl_st_wl_int_conflict_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn conflict_option_assn_def)


lemma twl_st_assn_confl_assn:
  \<open>twl_st_assn = hr_comp twl_st_int_conflict_assn (twl_st_wl_int_conflict_rel O twl_st_ref)\<close>
  apply (subst hr_comp_assoc[symmetric])
  apply (subst twl_st_int_assn_int_conflict_assn[symmetric])
  unfolding twl_st_assn_def ..

sepref_register get_max_lvl_st_int
sepref_thm get_max_lvl_st_int_code
  is \<open>uncurry (PR_CONST get_max_lvl_st_int)\<close>
  :: \<open>twl_st_int_conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding get_max_lvl_st_int_def twl_st_int_conflict_assn_def PR_CONST_def
  by sepref


concrete_definition (in -) get_max_lvl_st_int_code
  uses twl_array_code.get_max_lvl_st_int_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) get_max_lvl_st_int_code_def

lemmas get_max_lvl_st_int_code_refine[sepref_fr_rules] =
   get_max_lvl_st_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma get_max_lvl_st_refine[sepref_fr_rules]:
  \<open>(uncurry get_max_lvl_st_int_code, uncurry (RETURN oo get_max_lvl_st)) \<in>
    [\<lambda>(S, L). literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of None (st_l_of_wl None S)) \<and>
       L \<in># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None]\<^sub>a
      twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
     \<in> [comp_PRE (twl_st_wl_int_conflict_rel O twl_st_ref \<times>\<^sub>f Id)
          (\<lambda>((M, N, U, D, _), L). literals_are_in_N\<^sub>0 (the D) \<and> L \<in># the D \<and> D \<noteq> None)
          (\<lambda>_ _. True) (\<lambda>_. True)]\<^sub>a
        hrp_comp (twl_st_int_conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                     (twl_st_wl_int_conflict_rel O twl_st_ref \<times>\<^sub>f Id) \<rightarrow>
        hr_comp uint32_nat_assn nat_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF get_max_lvl_st_int_code_refine get_max_lvl_st_int_get_max_lvl_st]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[of \<open>fst x\<close>]
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_ref_def phase_saving_def in_N\<^sub>1_atm_of_in_atms_of_iff
      vmtf_imp_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
      twl_st_assn_def twl_st_int_assn_int_conflict_assn[symmetric]
      twl_st_assn_confl_assn[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


lemma count_decided_trail_ref:
  \<open>(RETURN o (\<lambda>(_, _, _, k). k), RETURN o count_decided) \<in> trailt_ref \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trailt_ref_def)

lemma count_decided_trail:
   \<open>(return o (\<lambda>(_, _, _, k). k), RETURN o (\<lambda>(_, _, _, k). k)) \<in> trailt_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare sep_auto

lemmas count_decided_trail_code[sepref_fr_rules] =
   count_decided_trail[FCOMP count_decided_trail_ref]

definition count_decided_st where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

sepref_thm count_decided_st_code
  is \<open>RETURN o count_decided_st\<close>
  :: \<open>twl_st_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding count_decided_st_def twl_st_int_assn_def
  by sepref

concrete_definition (in -) count_decided_st_code
  uses twl_array_code.count_decided_st_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) count_decided_st_code_def

lemmas count_decided_st_code_refine[sepref_fr_rules] =
   count_decided_st_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o count_decided_st, RETURN o count_decided_st) \<in> twl_st_ref \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_ref_def)

lemma count_decided_refine[sepref_fr_rules]:
  \<open>(count_decided_st_code, RETURN \<circ> count_decided_st) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using count_decided_st_code_refine[FCOMP count_decided_st_count_decided_st]
  unfolding twl_st_assn_def
  .

lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) conflict_remove1 :: \<open>nat literal \<Rightarrow> conflict_rel \<Rightarrow> conflict_rel\<close> where
  \<open>conflict_remove1 =
     (\<lambda>L (n,xs). if xs ! (atm_of L) = None then (n, xs) else (n-1, xs [atm_of L := None]))\<close>

lemma conflict_remove1:
  \<open>(uncurry (RETURN oo conflict_remove1), uncurry (RETURN oo remove1_mset)) \<in>
  [\<lambda>(L,C). L \<in># C \<and> -L \<notin># C \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f conflict_rel \<rightarrow> \<langle>conflict_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac y; case_tac x)
  subgoal for x y a b aa ab c
    using mset_as_position_remove[of c b \<open>atm_of aa\<close>]
    by (cases \<open>aa\<close>)
       (auto simp: conflict_rel_def conflict_remove1_def  conflict_rel_atm_in_iff minus_notin_trivial2
      size_remove1_mset_If in_N\<^sub>1_atm_of_in_atms_of_iff minus_notin_trivial mset_as_position_in_iff_nth)
   done

sepref_thm conflict_remove1_code
  is \<open>uncurry (RETURN oo conflict_remove1)\<close>
  :: \<open>[\<lambda>(L, (n,xs)). n > 0 \<and> atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>d \<rightarrow> conflict_rel_assn\<close>
  supply [[goals_limit=2]] one_nat_uint32[sepref_fr_rules] one_nat_uint32_def[simp]
  unfolding conflict_remove1_def one_nat_uint32_def[symmetric] fast_minus_def[symmetric]
  by sepref

find_theorems one_nat_uint32
concrete_definition (in -) conflict_remove1_code
  uses twl_array_code.conflict_remove1_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) conflict_remove1_code_def

lemmas conflict_remove1_code_refine[sepref_fr_rules] =
   conflict_remove1_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma conflict_remove1_code_op_nset_delete[sepref_fr_rules]:
  \<open>(uncurry conflict_remove1_code, uncurry (RETURN \<circ>\<circ> op_mset_delete))
    \<in> [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> L \<in># C \<and> -L \<notin># C]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow> conflict_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (Id \<times>\<^sub>f conflict_rel) (\<lambda>(L, C). L \<in># C \<and> - L \<notin># C \<and> L \<in> snd ` D\<^sub>0)
              (\<lambda>_ (L, n, xs). 0 < n \<and> atm_of L < length xs)
              (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>d) (Id \<times>\<^sub>f conflict_rel) \<rightarrow>
    hr_comp conflict_rel_assn conflict_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF conflict_remove1_code_refine conflict_remove1]
    unfolding op_mset_delete_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that neq0_conv
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (fastforce simp: image_image twl_st_ref_def phase_saving_def in_N\<^sub>1_atm_of_in_atms_of_iff
      vmtf_imp_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma conflict_option_assn_the[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>C. C \<noteq> None]\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> conflict_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_def conflict_option_assn_def conflict_rel_def hr_comp_def
    option_conflict_rel_def)

lemma conflict_option_assn_Some[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. (False, C)), RETURN o Some) \<in> conflict_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_def conflict_option_assn_def conflict_rel_def hr_comp_def
    option_conflict_rel_def bool_assn_alt_def)

lemma resolve_cls_wl'_union_uminus_zero_index:
  assumes
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C = 0\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = remove1_mset (-L) (the (get_conflict_wl S))\<close>
  using assms by (auto simp: resolve_cls_wl'_def)

(* TODO Move *)
declare cdcl\<^sub>W_restart_mset_state[simp]
(* End Move *)

definition (in -) conflict_merge_abs_union :: \<open>'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> 'v cconflict\<close> where
\<open>conflict_merge_abs_union N i C = Some (mset (N!i) \<union># (the C - uminus `# mset (N!i)))\<close>

lemma
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C < length (get_clauses_wl S)\<close> and
    L_confl: \<open>-L \<in># the (get_conflict_wl S)\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows
    resolve_cls_wl'_union_uminus_positive_index:
      \<open>C > 0 \<Longrightarrow> resolve_cls_wl' S C L = remove1_mset L (the (conflict_merge_abs_union (get_clauses_wl S) C (get_conflict_wl S)))\<close>
       (is \<open>_ \<Longrightarrow> ?Res\<close>) and
    resolve_cls_wl'_not_tauto_confl: \<open>\<not>tautology (the (get_conflict_wl S))\<close> (is ?tauto) and
    resolve_cls_wl'_not_tauto_cls: \<open>C > 0 \<Longrightarrow> \<not>tautology (mset (get_clauses_wl S ! C))\<close>
      (is \<open>_ \<Longrightarrow> ?tauto_cls\<close>) and
    resolve_cls_wl'_L_in_cls: \<open>C > 0 \<Longrightarrow> L \<in> set (get_clauses_wl S ! C)\<close> (is \<open>_ \<Longrightarrow> ?L_in_cls\<close>) and
    resolve_cls_wl'_in:
      \<open>C > 0 \<Longrightarrow> L \<in># (the (conflict_merge_abs_union (get_clauses_wl S) C (get_conflict_wl S)))\<close>
      (is \<open>_ \<Longrightarrow> ?L_in_union\<close>) and
    resolve_cls_wl'_notin:
      \<open>C > 0 \<Longrightarrow> -L \<notin># (the (conflict_merge_abs_union (get_clauses_wl S) C (get_conflict_wl S)))\<close>
      (is \<open>_ \<Longrightarrow> ?L_notin_union\<close>)

proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (Propagated L C # M, N, U, Some D, NP, UP, W, Q)\<close>
    using confl tr by (cases S; cases \<open>get_conflict_wl S\<close>; cases \<open>hd (get_trail_wl S)\<close>;
        cases \<open>get_trail_wl S\<close>) auto
  obtain D' where
    D: \<open>D = add_mset (-L) D'\<close>
    using L_confl by (auto simp: S dest: multi_member_split)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def by fast
  then have
     confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     M_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>
     unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have dist_D: \<open>distinct_mset D\<close>
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  have undef_L: \<open>undefined_lit M L\<close> and n_d: \<open>no_dup M\<close>
    using M_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S cdcl\<^sub>W_restart_mset_state split: if_splits)
  have M_D: \<open>Propagated L (mset (N ! C)) # convert_lits_l N M \<Turnstile>as CNot D\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases C) (auto simp: S cdcl\<^sub>W_restart_mset_state true_annots_true_cls)

  have M_D': \<open>Propagated L C # M \<Turnstile>as CNot D\<close>
    using M_D by (auto simp: true_annots_true_cls split: if_splits)
  have tauto_D: \<open>\<not>tautology D\<close>
    using M_D' n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l (Propagated L C # M)\<close> D]
    by (auto dest!: distinct_consistent_interp simp: true_annots_true_cls)
  then show ?tauto
    by (auto simp: S)

  assume C': \<open>C > 0\<close>
  have \<open>L \<in># mset (N ! C)\<close> and
    M_C: \<open>M \<Turnstile>as CNot (mset (N!C) - {#L#})\<close>
    using C C' confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (fastforce simp: S cdcl\<^sub>W_restart_mset_state)+
  from multi_member_split[OF this(1)] obtain C' where
    C'': \<open>mset (N ! C) = add_mset L C'\<close>
    by auto
  moreover have uL_C': \<open>-L \<notin># C'\<close>
    using M_C undef_L by (auto simp: C'' true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l)
  ultimately show ?tauto_cls
    using M_C n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> \<open>C'\<close>]
    by (auto 5 5 dest!: distinct_consistent_interp simp: tautology_add_mset true_annots_true_cls C' S)
  have get_clss_S: \<open>get_clauses_wl S = N\<close>
    by (auto simp: S)
  show ?L_in_cls
    unfolding in_multiset_in_set[symmetric] get_clss_S C'' by simp

  have n_d_L: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> False\<close> for L
    using distinct_consistent_interp[OF n_d] by (auto simp: consistent_interp_def)

  have uL_C'': \<open>-L \<notin># C' - uminus `# D'\<close>
    using uL_C' by (auto dest!: in_diffD)
  moreover have \<open>D' - uminus `# C' = D'\<close>
    apply (rule minus_eq_id_forall_notin_mset[THEN iffD2])
    unfolding Ball_def
    apply (rule impI conjI allI)
    subgoal for L'
      using undef_L n_d M_D' M_C n_d_L[of L']
      by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)
    done
  moreover have \<open>L \<notin># D'\<close>
    using tauto_D by (auto simp: tautology_add_mset D S)
  ultimately show ?Res
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        conflict_merge_abs_union_def)
  show ?L_in_union
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        conflict_merge_abs_union_def)
  show ?L_notin_union
    using C C' uL_C' uL_C'' dist_D unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        conflict_merge_abs_union_def dest: in_diffD)
qed

lemma conflict_merge_aa_conflict_merge_abs_union_aa:
  \<open>(uncurry2 (conflict_merge_aa), uncurry2 (RETURN ooo conflict_merge_abs_union)) \<in>
     [\<lambda>((N, i), C). distinct (N!i) \<and> literals_are_in_N\<^sub>0 (mset (N!i)) \<and> \<not> tautology (mset (N!i)) \<and>
         literals_are_in_N\<^sub>0 (the C) \<and> C \<noteq> None]\<^sub>f
    Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<rightarrow> \<langle>option_conflict_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using conflict_merge'_spec[of \<open>fst (snd x)\<close> \<open>fst (snd (snd x))\<close> \<open>snd (snd (snd x))\<close>
       \<open>the (snd y)\<close> \<open>(fst (fst y)) ! snd (fst y)\<close>]
    unfolding conflict_merge_abs_union_def conflict_merge_aa_def
    by (cases x; cases y) auto
  done

lemma conflict_merge_code_conflict_merge_abs_union[sepref_fr_rules]:
  \<open>(uncurry2 conflict_merge_code, uncurry2 (RETURN ooo conflict_merge_abs_union)) \<in>
    [\<lambda>((N, i), C). distinct (N!i) \<and> literals_are_in_N\<^sub>0 (mset (N!i)) \<and> \<not> tautology (mset (N!i)) \<and>
         literals_are_in_N\<^sub>0 (the C) \<and> C \<noteq> None \<and> i < length N]\<^sub>a
    clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (conflict_option_assn)\<^sup>d \<rightarrow> conflict_option_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
     \<in> [comp_PRE
           (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel)
           (\<lambda>((N, i), C). distinct (N ! i) \<and> literals_are_in_N\<^sub>0 (mset (N ! i)) \<and>
              \<not> tautology (mset (N ! i)) \<and> literals_are_in_N\<^sub>0 (the C) \<and> C \<noteq> None)
           (\<lambda>_ ((N, i), _, xs). i < length N \<and>
              (\<forall>j<length (N ! i). atm_of (N ! i ! j) < length (snd xs)))
           (\<lambda>_. True)]\<^sub>a
      hrp_comp (clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>d)
                   (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel) \<rightarrow>
      hr_comp (bool_assn *assn conflict_rel_assn) option_conflict_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF conflict_merge_aa_refine[unfolded PR_CONST_def]
      conflict_merge_aa_conflict_merge_abs_union_aa]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_in_N\<^sub>0_in_N\<^sub>1
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_ref_def phase_saving_def in_N\<^sub>1_atm_of_in_atms_of_iff
      vmtf_imp_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep hr_comp_prod_conv conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition update_confl_tl_wl_int :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_int \<Rightarrow> bool \<times> twl_st_wl_int\<close> where
  \<open>update_confl_tl_wl_int = (\<lambda>C L (M, N, U, D, Q, W, vmtf, \<phi>).
     (let D' = if C = 0 then remove1_mset (-L) (the D)
               else remove1_mset L (the (conflict_merge_abs_union N C D));
          L' = atm_of L in
    (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_dump_and_unset L' vmtf, save_phase L \<phi>))))\<close>

lemma resolve_cls_wl'_if_conflict_merge_abs_union:
  assumes
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>C < length (get_clauses_wl S)\<close> and
    \<open>- L \<in># the (get_conflict_wl S)\<close> and
    \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
    \<open>is_proped (hd (get_trail_wl S))\<close> and
    \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = (if C = 0 then remove1_mset (-L) (the (get_conflict_wl S))
               else remove1_mset L (the (conflict_merge_abs_union (get_clauses_wl S) C (get_conflict_wl S))))\<close>
  using resolve_cls_wl'_union_uminus_positive_index[of \<open>S\<close> C L] assms
  unfolding conflict_merge_abs_union_def[symmetric]
  by (auto simp: resolve_cls_wl'_def)

lemma update_confl_tl_wl_int_state_helper:
   \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<Longrightarrow> get_trail_wl S \<noteq> [] \<Longrightarrow>
    is_proped (hd (get_trail_wl S)) \<Longrightarrow> L = lit_of (hd (get_trail_wl S))\<close>
  by (cases S; cases \<open>hd (get_trail_wl S)\<close>) auto

lemma update_confl_tl_wl_int_update_confl_tl_wl:
  \<open>(uncurry2 (RETURN ooo update_confl_tl_wl_int), uncurry2 (RETURN ooo update_confl_tl_wl)) \<in>
  [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and> C < length (get_clauses_wl S) \<and>
    get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> - L \<in># the (get_conflict_wl S) \<and>
     (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and> L \<in> snd ` D\<^sub>0 \<and>
    twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S))]\<^sub>f
   nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_ref \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_ref\<rangle>nres_rel\<close>
  supply [[goals_limit = 2]]
  apply (intro frefI nres_relI)
  subgoal for CLS' CLS
    unfolding case_prod_beta uncurry_def update_confl_tl_wl_int_def comp_def
    using resolve_cls_wl'_if_conflict_merge_abs_union[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close> \<open>snd (fst CLS)\<close>,
        symmetric]
        update_confl_tl_wl_int_state_helper[of \<open>snd (fst CLS)\<close> \<open>fst (fst CLS)\<close>  \<open>snd CLS\<close>]
    by (cases \<open>CLS'\<close>; cases CLS)
       (auto simp: twl_st_ref_def update_confl_tl_wl_int_def update_confl_tl_wl_def
        abs_l_vmtf_unset_vmtf_unset' Let_def save_phase_def
        in_N\<^sub>1_atm_of_in_atms_of_iff phase_saving_def abs_l_vmtf_unset_vmtf_dump_unset
        dest: no_dup_tlD)
  done

lemma uminus_N\<^sub>0_iff: \<open>- L \<in># N\<^sub>1 \<longleftrightarrow> L \<in># N\<^sub>1\<close>
   by (simp add: in_N\<^sub>1_atm_of_in_atms_of_iff)

lemma conflict_merge_abs_union_None: \<open>conflict_merge_abs_union a b c \<noteq> None\<close>
  unfolding conflict_merge_abs_union_def by auto


lemma conflict_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> conflict_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: conflict_assn_def conflict_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff
    nat_of_uint32_012)+


sepref_thm update_confl_tl_wl_code
  is \<open>uncurry2 (RETURN ooo update_confl_tl_wl_int)\<close>
  :: \<open>[\<lambda>((i, L), (M, N, U, D, W, Q, ((A, m, lst, next_search), _), \<phi>)).
      (i > 0 \<longrightarrow> distinct (N ! i)) \<and>
      (i > 0 \<longrightarrow> literals_are_in_N\<^sub>0 (mset (N! i))) \<and>
      (i > 0 \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
      i < length N \<and>
      literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None \<and>
      M \<noteq> [] \<and>
      L \<in> snd ` D\<^sub>0 \<and> -L \<in># the D \<and> L \<notin># the D \<and>
      (i > 0 \<longrightarrow> (L \<in> set (N ! i) \<and> -L \<notin> set (N ! i))) \<and>
      (i > 0 \<longrightarrow> (-L \<notin># the (conflict_merge_abs_union N i D) \<and> L \<in># the (conflict_merge_abs_union N i D))) \<and>
      atm_of (lit_of (hd M)) < length \<phi> \<and>
      atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = lit_of (hd M)
         ]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d \<rightarrow> bool_assn *assn twl_st_int_assn\<close>
  supply image_image[simp] uminus_N\<^sub>0_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  supply conflict_merge_abs_union_None[simplified, simp]
  unfolding update_confl_tl_wl_int_def twl_st_int_assn_def vmtf_dump_and_unset_def vmtf_dump_def
   vmtf_unset_def save_phase_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) update_confl_tl_wl_code
  uses twl_array_code.update_confl_tl_wl_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_confl_tl_wl_code_def

lemmas update_confl_tl_wl_code_refine[sepref_fr_rules] =
   update_confl_tl_wl_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma update_confl_tl_wl_code_update_confl_tl_wl[sepref_fr_rules]:
  \<open>(uncurry2 update_confl_tl_wl_code, uncurry2 (RETURN ooo update_confl_tl_wl))
    \<in> [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
        get_conflict_wl S \<noteq> None \<and>
        get_trail_wl S \<noteq> [] \<and>
        - L \<in># the (get_conflict_wl S) \<and>
        (L, C) = lit_and_ann_of_propagated_st S \<and>
        literals_are_N\<^sub>0 S \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S)) \<and>
        additional_WS_invs (st_l_of_wl None S)]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> bool_assn *assn twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
   [comp_PRE (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_ref)
    (\<lambda>((C, L), S).
        twl_struct_invs (twl_st_of_wl None S) \<and>
        C < length (get_clauses_wl S) \<and>
        get_conflict_wl S \<noteq> None \<and>
        get_trail_wl S \<noteq> [] \<and>
        - L \<in># the (get_conflict_wl S) \<and>
        (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
        L \<in> snd ` D\<^sub>0 \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S)))
    (\<lambda>_ ((i, L), M, N, U, D, W, Q, ((A, m, lst, next_search), _), \<phi>).
        (i > 0 \<longrightarrow> distinct (N ! i)) \<and>
        (i > 0 \<longrightarrow> literals_are_in_N\<^sub>0 (mset (N ! i))) \<and>
        (i > 0 \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
        i < length N \<and>
        literals_are_in_N\<^sub>0 (the D) \<and>
        D \<noteq> None \<and>
        M \<noteq> [] \<and>
        L \<in> snd ` D\<^sub>0 \<and>
        - L \<in># the D \<and>
        L \<notin># the D \<and>
        (i > 0 \<longrightarrow> (L \<in> set (N ! i) \<and> - L \<notin> set (N ! i))) \<and>
        (i > 0 \<longrightarrow> (- L \<notin># the (conflict_merge_abs_union N i D) \<and>
          L \<in># the (conflict_merge_abs_union N i D))) \<and>
        atm_of (lit_of (hd M)) < length \<phi> \<and>
        atm_of (lit_of (hd M)) < length A \<and>
        (next_search \<noteq> None \<longrightarrow> the next_search < length A) \<and> L = lit_of (hd M))
    (\<lambda>_. True)]\<^sub>a
    hrp_comp (nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_int_assn\<^sup>d)
             (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_ref) \<rightarrow>
    hr_comp (bool_assn *assn twl_st_int_assn) (bool_rel \<times>\<^sub>f twl_st_ref)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF update_confl_tl_wl_code_refine
       update_confl_tl_wl_int_update_confl_tl_wl]
    .
  have pre: \<open>?pre' x\<close> (is \<open>comp_PRE ?rel ?\<Phi> ?\<Psi> _ x\<close>) if \<open>?pre x\<close> for x
  unfolding comp_PRE_def
  proof (intro allI impI conjI)
    obtain C L S where
      [simp]: \<open>x = ((C,L), S)\<close>
      by (cases x) auto
    obtain M N U D W Q NP UP where
      [simp]: \<open>S = (M, N, U, D, NP, UP, W, Q)\<close>
      by (cases S) auto
    have LC: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
      lits_N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
      trail_nempty: \<open>get_trail_wl S \<noteq> []\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
      proped: \<open>is_proped (hd (get_trail_wl S))\<close> and
      confl: \<open>get_conflict_wl S \<noteq> None\<close> and
      L_confl: \<open>-L \<in># the(get_conflict_wl S)\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)
    have lits_D: \<open>literals_are_in_N\<^sub>0 (the (get_conflict_wl S))\<close>
      by (rule literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0)
       (use lits_N\<^sub>0 confl struct_invs in auto)
    have C_le: \<open>C < length (get_clauses_wl S)\<close>
      using trail_nempty LC proped add_invs trail_nempty unfolding additional_WS_invs_def
      by (cases M; cases \<open>hd M\<close>) auto
    moreover have L_D\<^sub>0: \<open>L \<in> snd ` D\<^sub>0\<close>
      using L_confl confl lits_D
      by (cases \<open>get_conflict_wl S\<close>)
        (auto simp: image_image literals_are_in_N\<^sub>0_add_mset uminus_N\<^sub>0_iff
            dest: multi_member_split)
    ultimately show \<open>?\<Phi> x\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)

    fix x'
    assume x'x: \<open>(x', x) \<in> nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_ref\<close>
    then obtain S' where
      [simp]: \<open>x' = ((C, L), S')\<close>
      by (cases x') auto
    obtain Q' A m lst next_search oth \<phi> where
      [simp]: \<open>S' = (M, N, U, D, W, Q', ((A, m, lst, next_search), oth), \<phi>)\<close>
      using x'x by (cases S') (auto simp: twl_st_ref_def)
    have in_atms_le: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length A\<close> and \<phi>: \<open>phase_saving \<phi>\<close> and
      vmtf: \<open>\<exists>xs' ys'. l_vmtf (ys' @ xs') m A \<and> lst = option_hd (ys' @ xs') \<and> next_search = option_hd xs'\<close>
      using x'x unfolding twl_st_ref_def vmtf_imp_def by auto
    then have atm_L_le_A: \<open>atm_of L < length A\<close>
      using L_D\<^sub>0 by (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff)
    have atm_L_le_\<phi>: \<open>atm_of L < length \<phi>\<close>
      using L_D\<^sub>0 \<phi> unfolding phase_saving_def by (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff)
    obtain xs' ys' where
      \<open>l_vmtf (ys' @ xs') m A\<close> and \<open>lst = option_hd (ys' @ xs')\<close> and \<open>next_search = option_hd xs'\<close>
      using vmtf by blast
    then have next_search: \<open>the next_search < length A\<close> if \<open>next_search \<noteq> None\<close>
      apply - by (rule l_vmtf_le_length[of \<open>ys' @ xs'\<close> m A]) (use that in auto)
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      using struct_invs unfolding twl_struct_invs_def by fast
    then have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>distinct_mset_set (mset ` set (tl N))\<close>
      apply (subst append_take_drop_id[of U, symmetric])
      unfolding set_append image_Un
      by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def mset_take_mset_drop_mset drop_Suc)
    then have dist_NC:  \<open>distinct (N ! C)\<close> if \<open>C > 0\<close>
      using that C_le nth_in_set_tl[of C N] by (auto simp: distinct_mset_set_def)

    have lits_NC: \<open>literals_are_in_N\<^sub>0 (mset (N ! C))\<close> if \<open>C > 0\<close>
      by (rule literals_are_in_N\<^sub>0_nth) (use C_le that lits_N\<^sub>0 in auto)
    have L_hd_M: \<open>L = lit_of (hd M)\<close>
      by (cases M; cases \<open>hd M\<close>) (use trail_nempty LC proped in auto)

    have \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have L_notin_D: \<open>L \<notin># the D\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have tauto: \<open>\<not>tautology (mset (N ! C))\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_not_tauto_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that
      by auto
    have L_NC: \<open>L \<in> set (N ! C)\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_L_in_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that by auto
    have L_NC': \<open>-L \<notin> set (N ! C)\<close> if \<open>C > 0\<close>
      using tauto that L_NC apply (auto simp: tautology_decomp)
      by (metis (full_types) nat_of_lit.cases uminus_Pos uminus_of_uminus_id)
    then have uL_conflict_merge: \<open>- L \<notin># the (conflict_merge_abs_union N C D)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_notin[of S C L] struct_invs C_le LC proped
       trail_nempty
      by (auto simp: conflict_merge_abs_union_def dest: in_diffD)
    then have L_conflict_merge: \<open>L \<in># the (conflict_merge_abs_union N C D)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_in[of S C L] struct_invs C_le LC proped
       trail_nempty L_confl
      by (auto dest: in_diffD)

    show \<open>?\<Psi> x x'\<close>
      using confl L_confl dist_NC lits_NC C_le trail_nempty L_D\<^sub>0 tauto lits_D L_notin_D L_NC
      uL_conflict_merge L_conflict_merge atm_L_le_A atm_L_le_\<phi> next_search
      by (auto simp: L_hd_M[symmetric])
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context twl_array_code
begin

sepref_register skip_and_resolve_loop_wl_D
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] get_trail_twl_st_of_wl_get_trail_wl_empty_iff[simp] is_decided_hd_trail_wl_def[simp]
    is_decided_no_proped_iff[simp] skip_and_resolve_hd_in_D\<^sub>0[intro] literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[intro]
   get_conflict_l_st_l_of_wl[simp] literal_is_in_conflict_def[simp]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)
  unfolding
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps get_conflict_wl_get_conflict_wl_is_Nil
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    maximum_level_remove[symmetric]
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
    literal_is_in_conflict_def[symmetric]
    lit_and_ann_of_propagated_st_def[symmetric]
    get_max_lvl_st_def[symmetric]
    count_decided_st_alt_def[symmetric]
  by sepref
  (* apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
                  apply sepref_dbg_trans_step_keep
                    apply sepref_dbg_side_unfold apply (auto simp: )[] *)

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
   uses twl_array_code.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms]
end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context twl_array_code
begin
term twl_st_assn
definition (in -) lit_of_hd_trail_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal\<close> where
  \<open> lit_of_hd_trail_st S = lit_of (hd (get_trail_wl S))\<close>

definition lit_of_hd_trail_st_int :: \<open>twl_st_wl_int_trail_ref \<Rightarrow> nat literal\<close> where
  \<open> lit_of_hd_trail_st_int = (\<lambda>((M, _), _). lit_of (hd M))\<close>

lemma lit_of_hd_trail_st_int_lit_of_hd_trail_st:
   \<open>(RETURN o lit_of_hd_trail_st_int, RETURN o lit_of_hd_trail_st) \<in>
  [\<lambda>S. get_trail_wl S \<noteq>  []]\<^sub>f twl_st_trail_ref \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    by (auto simp: lit_of_hd_trail_st_def twl_st_trail_ref_def trailt_ref_def lit_of_hd_trail_st_int_def
      intro!: frefI nres_relI)

sepref_thm lit_of_hd_trail_st_code
  is \<open>RETURN o lit_of_hd_trail_st_int\<close>
  :: \<open>[\<lambda>((M, _), _). M \<noteq> []]\<^sub>a twl_st_int_trail_ref_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_int_def twl_st_int_trail_ref_assn_def
  by sepref

concrete_definition (in -) lit_of_hd_trail_st_code
   uses twl_array_code.lit_of_hd_trail_st_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_code_def

lemmas lit_of_hd_trail_st_code_refine_code[sepref_fr_rules] =
   lit_of_hd_trail_st_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

theorem lit_of_hd_trail_st_code_lit_of_hd_trail_st[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_st_code, RETURN o lit_of_hd_trail_st)
    \<in> [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_trail_ref (\<lambda>S. get_trail_wl S \<noteq> [])
        (\<lambda>_ ((M, _), _). M \<noteq> []) (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_int_trail_ref_assn\<^sup>k) twl_st_trail_ref \<rightarrow>
      hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_st_code_refine_code
    lit_of_hd_trail_st_int_lit_of_hd_trail_st] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_trail_ref_def trailt_ref_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_ref_assn_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

thm conflict_assn_def conflict_rel_def


type_synonym (in -) conflict_rel_with_cls = \<open>nat clause_l \<times> bool option list\<close>
type_synonym (in -) conflict_with_cls_assn = \<open>uint32 array \<times> bool option array\<close>

type_synonym twl_st_wll_confl_with_cls =
  \<open>trail_int_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>


definition option_conflict_rel_with_cls :: \<open>(conflict_rel_with_cls \<times> nat clause option) set\<close> where
  \<open>option_conflict_rel_with_cls = {((C, xs), D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length xs)}\<close>

definition option_conflict_rel_with_cls1 :: \<open>(nat clause_l \<times> nat clause option) set\<close> where
  \<open>option_conflict_rel_with_cls1 = {(C, D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel}\<close>

abbreviation (in -) conflict_with_cls_int_assn :: \<open>conflict_rel_with_cls \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_assn \<equiv>
    (array_assn unat_lit_assn *assn array_assn (option_assn bool_assn))\<close>

definition conflict_to_conflict_with_cls :: \<open>conflict_option_rel \<Rightarrow> conflict_rel_with_cls nres\<close> where
  \<open>conflict_to_conflict_with_cls = (\<lambda>(_, n, xs). do {
     let D = replicate n (Pos 0);
     (_, _, C, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, m, C, zs). i \<le> length zs \<and> length zs = length xs \<and> length C = n \<and>
          m \<le> length C\<^esup>
       (\<lambda>(i, m, C, zs). m > 0)
       (\<lambda>(i, m, C, zs). do {
           ASSERT(i < length xs);
           ASSERT(i < upperN div 2);
           ASSERT(m > 0);
           ASSERT(zs ! i \<noteq> None \<longrightarrow> Pos i \<in># N\<^sub>1);
           case zs ! i of
             None \<Rightarrow> RETURN (i+1, m, C, zs)
           | Some b \<Rightarrow> RETURN (i+1, m-1, C[m-1 := (if b then Pos i else Neg i)], zs[i := None])
       })
       (0, n, D, xs);
     RETURN (C, zs)
  }
  )\<close>

lemma conflict_to_conflict_with_cls_id:
  \<open>(conflict_to_conflict_with_cls, RETURN o id) \<in>
    [\<lambda>C. C \<noteq> None \<and> literals_are_in_N\<^sub>0 (the C)]\<^sub>f option_conflict_rel \<rightarrow> \<langle>option_conflict_rel_with_cls\<rangle> nres_rel\<close>
proof -
  have H: \<open>conflict_to_conflict_with_cls (b, n, xs) \<le> \<Down> option_conflict_rel_with_cls (RETURN (Some C))\<close>
    if ocr: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close> and lits_N\<^sub>0: \<open>literals_are_in_N\<^sub>0 C\<close>
    for b n xs C
  proof -
    define I' where
      [simp]: \<open>I' = (\<lambda>(i, m, D, zs). ((b, m, zs), Some (filter_mset (\<lambda>L. atm_of L \<ge> i) C)) \<in> option_conflict_rel \<and>
               i + m \<le> length zs \<and> (\<forall>k < i. zs ! k = None) \<and>
              mset (drop m D) = filter_mset (\<lambda>L. atm_of L < i) C)\<close>
    let ?I' = I'

    let ?I = \<open>\<lambda>xs n (i, m, D, zs). i \<le> length zs \<and> length zs = length xs \<and> length D = n \<and>
      m \<le> length D\<close>
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open> distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length xs\<close> and
       n_size: \<open>n = size C\<close>
      using mset_as_position_length_not_None[of xs C] that  mset_as_position_distinct_mset[of xs C]
        mset_as_position_tautology[of xs C]
      by (auto simp: option_conflict_rel_def conflict_rel_def)
    have size_C: \<open>size C \<le> upperN div 2\<close>
      using simple_clss_size_upper_div2[OF lits_N\<^sub>0 dist_C tauto_C] .

    have final: "((ad, bd), Some C) \<in> option_conflict_rel_with_cls"
      if
        s0: "?I baa aa s" and
        s1: "?I' s" and
        s:
          "\<not> (case s of (i, m, C, zs) \<Rightarrow> 0 < m)"
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have [simp]: \<open>ac = 0\<close> \<open>s = (ab, 0, ad, bd)\<close> \<open>bb = (0, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close>
        \<open>n = aa\<close>\<open>xs = baa\<close>
        using s by auto
      have \<open>((b, 0, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using s1 by auto
      then have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close> and map': \<open>mset_as_position bd {#}\<close>
        unfolding option_conflict_rel_def conflict_rel_def by auto
      have [simp]: \<open>length bd = length xs\<close>
        using s0 by auto
      have [iff]: \<open>\<not>x < ab \<longleftrightarrow> ab \<le> x\<close> for x
        by auto
      have \<open>{#L \<in># C. atm_of L < ab#} = C\<close>
        using multiset_partition[of C \<open>\<lambda>L. atm_of L < ab\<close>] by auto
      then have [simp]: \<open>mset ad = C\<close>
        using s1 by auto

      show ?thesis
        using map' atms_le_xs by (auto simp: option_conflict_rel_with_cls_def list_mset_rel_def br_def)
    qed
    have init: "I' (0, aa, replicate aa (Pos 0), baa)"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)"
      for a ba aa baa
      using ocr that n_le n_size size_C by auto

    have in_N\<^sub>1: "Pos ab \<in># N\<^sub>1"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        cond: "case s of (i, m, C, zs) \<Rightarrow> 0 < m" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_baa: "ab < length baa" and
        bd_ab: "bd ! ab \<noteq> None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length bd\<close>
        using b unfolding option_conflict_rel_def conflict_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' cond s unfolding I' by auto
      then have ab_in_C: \<open>Pos ab \<in># C \<or> Neg ab \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_N\<^sub>0 by auto
      then show ?thesis
        using lits_N\<^sub>0
        by (auto dest!: multi_member_split simp: literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff)
    qed
    have le_upperN_div2: "ab < upperN div 2"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)" and
        "?I baa aa s" and
        I': "I' s" and
        m: "case s of (i, m, C, zs) \<Rightarrow> 0 < m" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)" and
        "ab < length baa"
      for a ba aa baa s ab bb ac bc ad bd
    proof (rule ccontr)
      assume le: \<open>\<not> ?thesis\<close>
      have \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using I' s unfolding I'_def by auto
      have \<open>L \<in># C \<Longrightarrow> atm_of L < upperN div 2\<close> for L
        using lits_N\<^sub>0 in_N1_less_than_upperN
        by (cases L)  (auto dest!: multi_member_split simp: literals_are_in_N\<^sub>0_add_mset upperN_def)
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close>
        using le by (force simp: filter_mset_empty_conv)
      then show False
        using m s ocr unfolding option_conflict_rel_def conflict_rel_def by auto
    qed
    have IH_I': "I' (ab + 1, ac, ad, bd)"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "case s of (i, m, C, zs) \<Rightarrow> 0 < m" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab < upperN div 2" and
        "0 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># N\<^sub>1" and
        bd_ab: "bd ! ab = None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have [simp]: \<open>s = (ab, ac, ad, bd)\<close> \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close>
        \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa \<close> \<open>length bd = length baa\<close>
        using s I by auto
      have
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close> and
        \<open>ab + ac \<le> length bd\<close> and
        le_ab_None: \<open>\<forall>k<ab. bd ! k = None\<close>
        using I' unfolding I'_def by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length bd\<close>
        using b unfolding option_conflict_rel_def conflict_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>Pos ab \<notin># C\<close> \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_N\<^sub>0 by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        unfolding less_Suc_eq_le unfolding le_eq_less_or_eq
        using ab_in_C dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      then have mset_drop: \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using I' by auto

      have \<open>x \<in>#C \<Longrightarrow> atm_of x \<noteq> ab\<close> for x
        using bd_ab ocr
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> x]
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> \<open>-x\<close>]
        unfolding option_conflict_rel_def conflict_rel_def
        by force
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using s by (force intro!: filter_mset_cong2)
      then have ocr': \<open>((b, ac, bd), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using I' s by auto

      have
        x1a: \<open>ac = size {#L \<in># C. ab \<le> atm_of L#}\<close> and
        map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close>
        using ocr unfolding option_conflict_rel_def conflict_rel_def by auto

      have [iff]: \<open>ab + length (filter (op \<noteq> None) x2b) = length x2b \<longleftrightarrow> ab = length (filter (op = None) x2b)\<close> for x2b
        using sum_length_filter_compl[of \<open>op \<noteq> None\<close> x2b] by auto
      have filter_take_ab: \<open>filter (op = None) (take ab bd) = take ab bd\<close>
        apply (rule filter_id_conv[THEN iffD2])
        using le_ab_None by (auto simp: nth_append take_set split: if_splits)
      have \<open>filter (op = None) (drop ab bd) \<noteq> []\<close>
        using hd_drop_conv_nth[of ab bd] bd_ab ab_le
        by (cases \<open>drop ab bd\<close>) auto
      then have \<open>ab < length (filter (op = None) bd)\<close>
        apply (subst (2) append_take_drop_id[symmetric, of _ ab])
        unfolding filter_append length_append filter_take_ab
        using I' ab_le by auto
      then have Suc_le_bd: \<open>Suc (ab + ac) \<le> length bd\<close>
        using b mset_as_position_length_not_None[OF map] x1a
          sum_length_filter_compl[of \<open>op \<noteq> None\<close> bd]
        by auto
      have le_Suc_None: \<open>k < Suc ab \<Longrightarrow> bd ! k = None\<close> for k
        using le_ab_None bd_ab  by (auto simp: less_Suc_eq)

      show ?thesis using mset_drop ocr' Suc_le_bd le_Suc_None unfolding I'_def by auto
    qed
    have IH_I'_notin: "I' (ab + 1, ac - 1, ad[ac - 1 := if x then Pos ab else Neg ab],
          bd[ab := None])"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "case s of (i, m, C, zs) \<Rightarrow> 0 < m" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab < upperN div 2" and
        "0 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># N\<^sub>1" and
        bd_ab_x: "bd ! ab = Some x"
      for a ba aa baa s ab bb ac bc ad bd x
    proof -
      have [simp]: \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa\<close>
        \<open>s = (ab, (ac, (ad, bd)))\<close>
        \<open>length baa = length bd\<close>
        using I s by auto
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using I' by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length bd\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using b unfolding option_conflict_rel_def conflict_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>(if x then Pos ab else Neg ab) \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab_x lits_N\<^sub>0 by auto
      have \<open>distinct_mset {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>\<not> tautology {#L \<in># C. ab \<le> atm_of L#}\<close>
        using mset_as_position_distinct_mset[OF map] mset_as_position_tautology[OF map] by fast+
      have [iff]: \<open>\<not> ab < atm_of a \<and> ab = atm_of a \<longleftrightarrow>  (ab = atm_of a)\<close> for a :: \<open>nat literal\<close> and ab
        by auto
      have H1: \<open>{#L \<in># C.  ab \<le> atm_of L#} = (if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv)
      have H2: \<open>{#L \<in># C. Suc ab \<le> atm_of L#} = remove1_mset (Pos ab) (remove1_mset (Neg ab) {#L \<in># C. ab \<le> atm_of L#})\<close>
        by (auto simp: H1)
      have map': \<open>mset_as_position (bd[ab := None]) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        unfolding H2
        apply (rule mset_as_position_remove)
        using map ab_le by auto
      have c_r: \<open>((b, ac - Suc 0, bd[ab := None]), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_conflict_rel\<close>
        using ocr b map' by (auto simp: option_conflict_rel_def conflict_rel_def H1)
      have H3: \<open>(if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      have ac_ge0: \<open>ac > 0\<close>
        using m by auto
      then have \<open>ac - Suc 0 < length ad\<close> and \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close>
        using I' I by auto
      then have 3: \<open>mset (drop (ac - Suc 0) (ad[ac - Suc 0 := (if x then Pos ab else Neg ab)])) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using Cons_nth_drop_Suc[symmetric, of \<open>ac - 1\<close> \<open>ad\<close>] ac_ge0
        by (auto simp: drop_update_swap H3[symmetric])

      show ?thesis
          using b c_r that 3 s unfolding I'_def by auto
    qed
    show ?thesis
      supply WHILEIT_rule[refine_vcg del]
      unfolding conflict_to_conflict_with_cls_def Let_def
      apply (refine_vcg WHILEIT_rule_stronger_inv[where
            R = \<open>measure (\<lambda>(i :: nat, m :: nat, D :: nat clause_l, zs :: bool option list). length zs - i)\<close> and
            I' = \<open>?I'\<close>])
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal by auto
      subgoal by auto
      subgoal by (rule init)
      subgoal using n_le by auto
      subgoal by (rule le_upperN_div2)
      subgoal by auto
      subgoal by (rule in_N\<^sub>1) assumption+
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I')
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal using b by (auto simp: less_Suc_eq)
      subgoal by auto
      subgoal by (rule IH_I'_notin)
      subgoal by auto
      subgoal by (rule final) assumption+
      done
    qed

  show ?thesis
    by (intro frefI nres_relI) (auto intro!: H)
qed


lemma conflict_to_conflict_with_cls_code_helper:
  \<open>zero_uint32 < upperN div 2\<close>
  \<open>a1'b < upperN div 2 \<Longrightarrow> a1'b + one_nat_uint32 < upperN\<close>
  \<open> 0 < a1'c \<Longrightarrow> one_nat_uint32 \<le> a1'c\<close>
  \<open>fast_minus a1'c one_nat_uint32  = a1'c - 1\<close>
  by (auto simp: upperN_def zero_uint32_def one_nat_uint32_def fast_minus_def)

lemmas uint32_nat_assn_plus'[sepref_fr_rules] = uint32_nat_assn_plus[unfolded upperN_def[symmetric]]
declare uint32_nat_assn_plus[sepref_fr_rules del]

sepref_register conflict_to_conflict_with_cls
sepref_thm conflict_to_conflict_with_cls_code
  is \<open>PR_CONST conflict_to_conflict_with_cls\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a conflict_with_cls_int_assn\<close>
  supply uint32_nat_assn_zero_uint32[sepref_fr_rules] [[goals_limit=1]]
   Pot_unat_lit_assn'[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
   conflict_to_conflict_with_cls_code_helper[simp]
  unfolding conflict_to_conflict_with_cls_def array_fold_custom_replicate
    fast_minus_def[of \<open>_ :: nat\<close>, symmetric] PR_CONST_def
  apply (rewrite at "\<hole> < length _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "_ ! \<hole> \<noteq> None" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "\<hole> < _" zero_uint32_def[symmetric])
  apply (rewrite at \<open>Pos \<hole>\<close> zero_uint32_def[symmetric])
  apply (rewrite at \<open>(\<hole>, _, _, _)\<close> zero_uint32_def[symmetric])
  apply (rewrite at "(zero_uint32, \<hole>, _, _)" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>_ + \<hole>\<close> one_nat_uint32_def[symmetric])+
  apply (rewrite at \<open>fast_minus _ \<hole>\<close> one_nat_uint32_def[symmetric])+
  by sepref
(*   apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
                    apply sepref_dbg_trans_step_keep
                    apply sepref_dbg_side_unfold apply (auto simp: )[] *)


concrete_definition (in -) conflict_to_conflict_with_cls_code
   uses twl_array_code.conflict_to_conflict_with_cls_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_to_conflict_with_cls_code_def

lemmas conflict_to_conflict_with_cls_code_refine[sepref_fr_rules] =
   conflict_to_conflict_with_cls_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

definition conflict_with_cls_assn :: \<open>nat clause option \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_assn \<equiv> hr_comp conflict_with_cls_int_assn option_conflict_rel_with_cls\<close>

definition conflict_to_conflict_with_cls_spec where
  \<open>conflict_to_conflict_with_cls_spec = id\<close>

lemma conflict_to_conflict_with_cls_code_id[sepref_fr_rules]:
  \<open>(conflict_to_conflict_with_cls_code, RETURN \<circ> conflict_to_conflict_with_cls_spec)
      \<in> [\<lambda>x. x \<noteq> None \<and> literals_are_in_N\<^sub>0 (the x)]\<^sub>a
       conflict_option_assn\<^sup>d \<rightarrow> conflict_with_cls_assn\<close>
  using conflict_to_conflict_with_cls_code_refine[unfolded PR_CONST_def,
      FCOMP conflict_to_conflict_with_cls_id]
  unfolding conflict_with_cls_assn_def conflict_option_assn_def conflict_to_conflict_with_cls_spec_def
    by auto

definition (in -) extract_shorter_conflict_l_trivial :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v cconflict \<Rightarrow> 'v cconflict\<close> where
  \<open>extract_shorter_conflict_l_trivial M D = Some (filter_mset (\<lambda>L. get_level M L > 0) (the D))\<close>

definition (in -) extract_shorter_conflict_st_trivial :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>extract_shorter_conflict_st_trivial = (\<lambda>(M, N, U, D, NP, UP, Q, W).
  RETURN (M, N, U, extract_shorter_conflict_l_trivial M D, NP, UP, Q, W))\<close>

definition extract_shorter_conflict_st_trivial_int :: \<open>twl_st_wl_int \<Rightarrow> twl_st_wl_int nres\<close>
  where
\<open>extract_shorter_conflict_st_trivial_int = (\<lambda>(M, N, U, D, oth).
  RETURN (M, N, U, extract_shorter_conflict_l_trivial M D, oth))\<close>

lemma extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial:
  \<open>(extract_shorter_conflict_st_trivial_int, extract_shorter_conflict_st_trivial) \<in>
    [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_ref \<rightarrow> \<langle>twl_st_ref\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: extract_shorter_conflict_st_trivial_int_def conflict_to_conflict_with_cls_spec_def
        extract_shorter_conflict_st_trivial_def twl_st_ref_def RETURN_def
     intro!: RES_refine)

definition (in -) sum_mod_upperN where
  \<open>sum_mod_upperN a b = (a + b) mod upperN\<close>

lemma (in -) nat_of_uint32_plus:
  \<open>nat_of_uint32 (a + b) = (nat_of_uint32 a + nat_of_uint32 b) mod (2 ^ 32)\<close>
  by transfer (auto simp: unat_word_ariths)

lemma (in -) sum_mod_upperN: \<open>(uncurry (return oo op +), uncurry (RETURN oo sum_mod_upperN)) \<in> uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a
  uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: sum_mod_upperN_def uint32_nat_rel_def br_def nat_of_uint32_plus upperN_def)

definition extract_shorter_conflict_list_removed :: \<open>(nat, nat) ann_lits \<Rightarrow> conflict_option_rel \<Rightarrow>
  (conflict_option_rel \<times> (nat literal \<times> nat) option) nres\<close> where
\<open>extract_shorter_conflict_list_removed = (\<lambda>M (_, (n, xs)). do {
   (_, _, m, zs, L) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(i, m', m, xs, L). i \<le> length xs \<and> m \<le> n \<and> i + 1 < upperN \<and> m \<ge> m'\<^esup>
       (\<lambda>(i, m', _). m' > 0)
       (\<lambda>(i, m', m, zs, L). do {
          ASSERT(i < length zs);
          ASSERT(m' > 0);
          case zs ! i of
            None \<Rightarrow> RETURN (i+1, m', m, zs, L)
          | Some b \<Rightarrow>  do {
               ASSERT(Pos i \<in> snd ` D\<^sub>0);
               let k = get_level M (Pos i) in
               if k > 0 then (* Keep *)
                 (case L of
                   None \<Rightarrow> RETURN (i+1, m' - 1, m, zs, Some (if b then Pos i else Neg i, k))
                 | Some (_, k') \<Rightarrow>
                   if k > k' then
                     RETURN (i + 1, m' - 1, m, zs, Some (if b then Pos i else Neg i, k))
                   else
                     RETURN (i + 1, m' - 1, m, zs, L))
               else (* delete *)
                 RETURN (i + 1, m' - 1, m - 1, zs[i := None], L)
            }
        })
     (0, n, n, xs, None);
    RETURN ((False, (m, zs)), L)
  })\<close>

definition highest_lit where
  \<open>highest_lit M C L \<longleftrightarrow>
     (L = None \<longrightarrow> C = {#}) \<and>
     (L \<noteq> None \<longrightarrow> get_level M (fst (the L)) = snd (the L) \<and>
        snd (the L) = get_maximum_level M C \<and>
        fst (the L) \<in># C
        )\<close>


lemma extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial:
  shows \<open>(uncurry extract_shorter_conflict_list_removed, uncurry (RETURN oo extract_shorter_conflict_l_trivial)) \<in>
      [\<lambda>(M', D). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None \<and> M = M']\<^sub>f Id \<times>\<^sub>f option_conflict_rel \<rightarrow>
         \<langle>{((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and> highest_lit M (the C) L \<and>
           (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))}\<rangle> nres_rel\<close>
  (is \<open>?C \<in> [?pre]\<^sub>f _ \<times>\<^sub>f _ \<rightarrow> \<langle>?post\<rangle> nres_rel\<close>)
proof -
  have H: \<open>extract_shorter_conflict_list_removed M (b, n, xs)
       \<le> \<Down> ?post (RETURN (extract_shorter_conflict_l_trivial M (Some C)))\<close>
    if lits: \<open>literals_are_in_N\<^sub>0 C\<close> and ocr: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close>
    for C b n xs
  proof -
    let ?C = \<open>\<lambda>M i C. filter_mset (\<lambda>L. atm_of L < i \<longrightarrow> get_level M L \<noteq> 0) C\<close>
    let ?D = \<open>\<lambda>M i C. filter_mset (\<lambda>L. atm_of L < i \<and> get_level M L \<noteq> 0) C\<close>
    define I' where
      \<open>I' = (\<lambda>(i, m', m, zs, L). highest_lit M (?D M i C) L \<and>
              ((False, (m, zs)), Some (?C M i C))
        \<in> option_conflict_rel \<and> (i < length zs \<longrightarrow> zs ! i \<noteq> None \<longrightarrow> Pos i \<in> snd ` D\<^sub>0) \<and>
        i + m' \<le> length zs \<and> length xs = length zs \<and>
        m' = size (filter_mset (\<lambda>L. atm_of L \<ge> i) C) \<and>
        (m' > 0 \<longrightarrow> i + m' + count_list (drop i zs) None = length xs) \<and>
        (m' > 0 \<longrightarrow> i \<le> upperN div 2))\<close>
    have [simp]: \<open>b = False\<close>
      using ocr unfolding option_conflict_rel_def by auto
    have n: \<open>n = size C\<close> and map: \<open>mset_as_position xs C\<close>
      using ocr by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def)
    have \<open>xs ! i = None \<longleftrightarrow> Pos i \<notin># C \<and> Neg i \<notin># C\<close> if \<open>i < length xs\<close> for i
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos i\<close>] that
        mset_as_position_in_iff_nth[OF map, of \<open>Neg i\<close>]
      by (cases \<open>xs ! i\<close>) auto
    have xs_Some:
       \<open>xs ! i = Some y \<longleftrightarrow> (y \<longrightarrow> Pos i \<in># C) \<and> (\<not>y \<longrightarrow> Neg i \<in># C)\<close> if \<open>i < length xs\<close> for i y
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos i\<close>] that
        mset_as_position_in_iff_nth[OF map, of \<open>Neg i\<close>]
      by (cases \<open>xs ! i\<close>) auto
    have n_ge_upperN: \<open>n > upperN div 2 \<Longrightarrow> {#L \<in># C. n \<le> atm_of L#} = {#}\<close> for n
      using lits in_N1_less_than_upperN
      by (auto simp: filter_mset_empty_conv literals_are_in_N\<^sub>0_add_mset nat_of_lit_def upperN_def
          dest!: multi_member_split split: if_splits)
    define I where
      \<open>I n = (\<lambda>(i :: nat, m'::nat, m :: nat, xs :: bool option list, L:: (nat literal \<times> nat) option).
         i \<le> length xs \<and> m \<le> n \<and> i + 1 < upperN \<and> m \<ge> m')\<close>
      for n :: nat
    have I'_mapD: \<open>I' (i, m, n, xs, L) \<Longrightarrow> mset_as_position xs {#L \<in># C. \<not> (atm_of L < i \<and> get_level M L = 0)#}\<close>
      for i m n xs L
      unfolding I'_def option_conflict_rel_def conflict_rel_def by auto
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open> distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length xs\<close> and
       n_size: \<open>n = size C\<close>
      using mset_as_position_length_not_None[of xs C] that  mset_as_position_distinct_mset[of xs C]
        mset_as_position_tautology[of xs C]
      by (auto simp: option_conflict_rel_def conflict_rel_def)
    have init_I: \<open>I n (0, n, n, xs, None)\<close>
      using ocr lits unfolding I_def
      by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def upperN_def
          mset_as_position_length_not_None[OF map] xs_Some literals_are_in_N\<^sub>0_add_mset
          image_image in_N\<^sub>1_atm_of_in_atms_of_iff
          dest!: multi_member_split[of _ C])
    have \<open>length xs - count_list xs None + count_list xs None = length xs\<close>
      using count_le_length[of xs None] by auto
    then have init_I': \<open>I' (0, n, n, xs, None)\<close>
      using ocr lits unfolding I'_def
      by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def
          mset_as_position_length_not_None[OF map] xs_Some literals_are_in_N\<^sub>0_add_mset
          image_image in_N\<^sub>1_atm_of_in_atms_of_iff removeAll_filter_not_eq[symmetric]
          length_removeAll_count_list upperN_def
          dest!: multi_member_split[of _ C])
    have notin_I': "I' (ab + 1, ac, ad, ae, be)"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)" and
        I: "I aa s" and
        I': "I' s" and
        m: "case s of (i, m', uu) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)" and
        None: "ae ! ab = None"
      for ab ac ad ae be a ba aa baa s bb bc bd
    proof -
      have ab_le: \<open>ab < length ae\<close>
        using s I I' m unfolding I'_def I_def by auto
      have map: \<open>mset_as_position ae {#L \<in># C. \<not> (atm_of L < ab \<and> get_level M L = 0)#}\<close>
        using I'_mapD[OF I'[unfolded s]] .
      have Pos: \<open>Pos ab \<notin># C\<close> and Neg: \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] ab_le None
        mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>] by auto
      have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. ab < atm_of L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab#} =  {#L \<in># C. atm_of L < ab#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. ab < atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have 3: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos (Suc ab)\<close>] ab_le None
        mset_as_position_in_iff_nth[OF map, of \<open>Neg (Suc ab)\<close>] lits
        by (auto dest!: multi_member_split simp: literals_are_in_N\<^sub>0_add_mset image_image
            in_N\<^sub>1_atm_of_in_atms_of_iff)
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab \<and> 0 < get_level M L#} = {#L \<in># C. atm_of L < ab \<and> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        subgoal ..
        done
      have 4: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> upperN div 2\<close>
        using n_ge_upperN[of \<open>Suc ab\<close>] by (cases \<open>upperN div 2 \<le> ab\<close>; auto simp: upperN_def)
      have \<open>ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop ab ae) None =
           length ae\<close>
        using that xs_Some unfolding I'_def I_def by (auto simp: 3)
      then have \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
         length ae \<close>
        using Cons_nth_drop_Suc[symmetric, of ab ae] ab_le None by auto
      then show ?thesis
        using that xs_Some m unfolding I'_def I_def by (auto simp: 3 4)
    qed
    have in_I'_no_found: "I' (ab + 1, ac - 1, ad, ae, Some (if x then Pos ab else Neg ab, get_level M (Pos ab)))"
      if
        "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = None"
      for a ba aa baa s ab bb ac bc ad bd ae be x
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_N\<^sub>1: "Pos ab \<in># N\<^sub>1" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff literals_are_in_N\<^sub>0_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some (?L, get_level M (Pos ab)))\<close>
        using shl unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto

      have ab_upperN: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> upperN div 2\<close>
        using n_ge_upperN[of \<open>Suc ab\<close>] by (cases \<open>upperN div 2 \<le> ab\<close>; auto simp: upperN_def)
      then show ?thesis
        using ab_le Some shl' ab_N\<^sub>1 ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_upperN cond
        unfolding I'_def by auto
    qed
    have in_I'_found_upd: "I' (ab + 1, ac - 1, ad, ae,
          Some (if x then Pos ab else Neg ab, get_level M (Pos ab)))"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
          "xa = (af, bf)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = Some xa" and
        lev_bf: "bf < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x xa af bf
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "xa = (af, bf)"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_N\<^sub>1: "Pos ab \<in># N\<^sub>1" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff literals_are_in_N\<^sub>0_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some (?L, get_level M (Pos ab)))\<close>
        using shl lev_bf unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto
      have [simp]: \<open>sum_mod_upperN ab (Suc 0) = ab + Suc 0\<close>
        unfolding sum_mod_upperN_def
        apply (rule nat_mod_eq')
        apply (rule ccontr)
        using n_ge_upperN[of ab] cond ac
        by (auto simp: upperN_def not_less_eq)
      have ab_upperN: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> upperN div 2\<close>
        using n_ge_upperN[of \<open>Suc ab\<close>] by (cases \<open>upperN div 2 \<le> ab\<close>; auto simp: upperN_def)
      show ?thesis
        using ab_le Some shl' ab_N\<^sub>1 ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_upperN
        unfolding I'_def
        by auto
    qed
    have in_I'_found_no_upd: "I' (ab + 1, ac - 1, ad, ae, be)"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
          "xa = (af, bf)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = Some xa" and
        lev_bf: "\<not> bf < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x xa af bf
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "xa = (af, bf)"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_N\<^sub>1: "Pos ab \<in># N\<^sub>1" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff literals_are_in_N\<^sub>0_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some xa)\<close>
        using shl lev_bf unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto
      have ab_upperN: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> upperN div 2\<close>
        using n_ge_upperN[of \<open>Suc ab\<close>] by (cases \<open>upperN div 2 \<le> ab\<close>; auto simp: upperN_def)
      show ?thesis
        using ab_le Some shl' ab_N\<^sub>1 ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_upperN
        unfolding I'_def by auto
    qed
    have I'_in_remove: "I' (ab + 1, ac - 1, ad - 1, ae[ab := None], be)"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "\<not> 0 < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_N\<^sub>1: "Pos ab \<in># N\<^sub>1" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_N\<^sub>1_atm_of_in_atms_of_iff literals_are_in_N\<^sub>0_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      have 1: \<open>(?D M (Suc ab) C) =  (?D M ab C)\<close>
        apply (rule filter_mset_cong2)
        subgoal for L
          using lev_ab by (cases L) (auto simp: less_Suc_eq_le order.order_iff_strict get_level_Neg_Pos)
        subgoal ..
        done
      have shl': \<open>highest_lit M (?D M (Suc ab) C) be\<close>
        using shl unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)

      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = add_mset ?L {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (subst distinct_mset_add_mset_filter)
        subgoal using dist_C .
        subgoal using \<open>?L \<in># C\<close> .
        subgoal using lev_ab by (auto simp: get_level_Neg_Pos)
        apply (rule filter_mset_cong2)
        subgoal for L
          using lev_ab \<open>?L \<in># C\<close> tauto_C by (cases L) (auto simp: less_Suc_eq_le)
        subgoal ..
        done

      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} - {#Pos ab, Neg ab#} =
         {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        using lev_ab unfolding ocr_e by (auto simp: get_level_Neg_Pos)

      have ocr': \<open>((False, ad - Suc 0, ae[ab := None]),
           Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#})
         \<in> option_conflict_rel\<close>
        using ocr ab_le \<open>?L \<in># C\<close> tauto_C
        mset_as_position_remove[OF I'_mapD[OF I'[unfolded s]], of \<open>atm_of ?L\<close>]
        unfolding option_conflict_rel_def conflict_rel_def ocr_e by (cases x) auto
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto

      have ab_upperN: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> upperN div 2\<close>
        using n_ge_upperN[of \<open>Suc ab\<close>] by (cases \<open>upperN div 2 \<le> ab\<close>; auto simp: upperN_def)
      show ?thesis
        using ab_le Some shl' ab_N\<^sub>1 ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_upperN
        unfolding I'_def by auto
    qed
    have final: "(((False, ad, ae), be), Some {#L \<in># the (Some C). 0 < get_level M L#})
      \<in> {((D, L), C).
          (D, C) \<in> option_conflict_rel \<and>
          C \<noteq> None \<and> highest_lit M (the C) L \<and> (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))}"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "\<not> (case s of (i, m', uu_) \<Rightarrow> 0 < m')" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
      for a ba aa baa s ab bb ac bc ad bd ae be
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "ac = 0"
        using s cond by auto

      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        [simp]: "length baa = length ae" and
        (* ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and *)
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' unfolding I'_def
        by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L using ac by (auto simp: filter_mset_empty_conv)
        subgoal by (rule refl)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<and> 0 < get_level M L#} = {#L \<in># C. 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L using ac by (auto simp: filter_mset_empty_conv)
        subgoal by (rule refl)
        done
      have le_ae: \<open>\<forall>L\<in>atms_of N\<^sub>1. L < length ae\<close>
        using I I' ocr unfolding I'_def option_conflict_rel_def conflict_rel_def
        by auto
      show ?thesis
        using ocr shl le_ae by auto
    qed
    show ?thesis
      unfolding extract_shorter_conflict_list_removed_def extract_shorter_conflict_l_trivial_def
        I_def[symmetric]
      apply (refine_vcg
         WHILEIT_rule_stronger_inv[where R=\<open>measure (\<lambda>(i, _). Suc (length xs) - i)\<close> and
           I' = I'])
      subgoal by auto
      subgoal using init_I by auto
      subgoal using init_I' by auto
      subgoal unfolding I'_def I_def by auto
      subgoal by auto
      subgoal unfolding I'_def I_def upperN_def by auto
      subgoal by (rule notin_I')
      subgoal unfolding I'_def by auto
      subgoal unfolding I'_def by auto
      subgoal by (auto simp: I'_def I_def upperN_def)
      subgoal by (rule in_I'_no_found)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def upperN_def I'_def by auto
      subgoal by (rule in_I'_found_upd)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def I'_def upperN_def by auto
      subgoal by (rule in_I'_found_no_upd)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def I'_def upperN_def by auto
      subgoal by (rule I'_in_remove)
      subgoal unfolding I'_def by auto
      subgoal by (rule final)
      done
  qed
  then show ?thesis
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply auto
    done
qed

definition extract_shorter_conflict_list where
  \<open>extract_shorter_conflict_list = (\<lambda>M C. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     let C = extract_shorter_conflict_l_trivial M C;
     RETURN (map_option (add_mset (-K)) C)
  })\<close>

definition extract_shorter_conflict_list_int where
  \<open>extract_shorter_conflict_list_int = (\<lambda>M (b, (n, xs)). do {
     let K = lit_of (hd M);
     ASSERT(atm_of K < length xs);
     ASSERT(n \<ge> 1);
     let xs = xs[atm_of K := None];
     ((b, (n, xs)), L) \<leftarrow> extract_shorter_conflict_list_removed M (b, (n - 1, xs));
     ASSERT(atm_of K < length xs);
     ASSERT(n + 1 < upperN);
     RETURN ((b, (n + 1, xs[atm_of K := Some (is_neg K)])), L)
  })\<close>


lemma extract_shorter_conflict_list_extract_shorter_conflict_l_trivial_spec:
  \<open>literals_are_in_N\<^sub>0 (the ba) \<and> (\<exists>y. ba = Some y) \<and> ((a, aa, b), ba) \<in> option_conflict_rel \<and> M = M' \<Longrightarrow>
    extract_shorter_conflict_list_removed M (a, aa, b) \<le> \<Down> {((D, L), C).
      (D, C) \<in> option_conflict_rel \<and> (\<exists>y. C = Some y) \<and> highest_lit M (the C) L \<and>
      (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))}
    (RETURN (extract_shorter_conflict_l_trivial M' ba))\<close>
  apply simp
    apply (rule extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial[
        unfolded fref_def nres_rel_def, simplified, rule_format])
  by fast

lemma literals_are_in_N\<^sub>0_sub:
  \<open>literals_are_in_N\<^sub>0 y \<Longrightarrow> literals_are_in_N\<^sub>0 (y - z)\<close>
  using literals_are_in_N\<^sub>0_mono[of y \<open>y - z\<close>] by auto

lemma extract_shorter_conflict_l_trivial_subset_msetD:
  \<open>extract_shorter_conflict_l_trivial M (Some (remove1_mset (- lit_of (hd M)) D)) = Some D' \<Longrightarrow> D' \<subseteq># D\<close>
  apply (auto simp: extract_shorter_conflict_l_trivial_def)
  by (metis Diff_eq_empty_iff_mset diff_le_mono2_mset diff_subset_eq_self diff_zero multiset_filter_subset)

lemma extract_shorter_conflict_list_int_extract_shorter_conflict_list:
  \<open>(uncurry extract_shorter_conflict_list_int, uncurry extract_shorter_conflict_list)
   \<in> [\<lambda>(M', D). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
         literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and>  - lit_of (hd M) \<in># the D \<and>
         lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and> get_level M (lit_of (hd M)) > 0 \<and>
          \<not>tautology (the D)]\<^sub>f
      Id \<times>\<^sub>f option_conflict_rel \<rightarrow>
       \<langle>{((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and>
          highest_lit M (remove1_mset (-lit_of (hd M)) (the C)) L \<and>
          (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))}\<rangle>nres_rel\<close>
  supply extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial[refine_vcg]
  unfolding extract_shorter_conflict_list_def extract_shorter_conflict_list_int_def uncurry_def
  apply (intro frefI nres_relI)
  apply clarify
  apply refine_rcg
  subgoal
    by (cases M)
      (auto simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
        literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff)
  subgoal by (auto simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
        literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff
        dest: multi_member_split)
  unfolding conc_fun_RETURN[symmetric]
   apply (rule extract_shorter_conflict_list_extract_shorter_conflict_l_trivial_spec)
  subgoal for a aa ab b ac ba y
    using mset_as_position_remove[of b y \<open>atm_of (- lit_of (hd M))\<close>]
    apply (cases \<open>lit_of (hd M)\<close>)
    apply (auto intro!: ASSERT_refine_left
        simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
        size_remove1_mset_If minus_notin_trivial2 minus_notin_trivial)
    done
  subgoal for M' b n zs ac ba D x' x1 x1a x2 x1b x2a L
    apply (auto intro!: ASSERT_refine_left)
    subgoal
      apply (cases M)
       apply (auto simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
      done
    subgoal for D'
      using simple_clss_size_upper_div2[of D'] literals_are_in_N\<^sub>0_mono[of D D']
        distinct_mset_mono[of D' D] not_tautology_mono[of D' D]
      by (auto simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff upperN_def
          dest!: extract_shorter_conflict_l_trivial_subset_msetD)
    subgoal
      by (auto simp: literals_are_in_N\<^sub>0_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
    done
  done

abbreviation extract_shorter_conflict_l_trivial_pre where
\<open>extract_shorter_conflict_l_trivial_pre \<equiv> \<lambda>(M, D). literals_are_in_N\<^sub>0 (mset (fst D))\<close>

term extract_shorter_conflict_list_int
term \<open>bool_assn *assn conflict_rel_assn\<close>
term conflict_option_rel_assn

definition (in -) lit_of_hd_trail where
  \<open>lit_of_hd_trail M = lit_of (hd M)\<close>


definition (in -) lit_of_hd_trail_int where
  \<open>lit_of_hd_trail_int = (\<lambda>(M, _). lit_of (hd M))\<close>

lemma lit_of_hd_trail_int_lit_of_hd_trail:
   \<open>(RETURN o lit_of_hd_trail_int, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trailt_ref \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
   by (auto simp: lit_of_hd_trail_def trailt_ref_def lit_of_hd_trail_int_def
      intro!: frefI nres_relI)

sepref_definition (in -) lit_of_hd_trail_code
  is \<open>RETURN o lit_of_hd_trail_int\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trailt_conc\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_int_def
  by sepref

theorem lit_of_hd_trail_code_lit_of_hd_trail[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE trailt_ref (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trailt_conc\<^sup>k)
                     trailt_ref \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_code.refine
      lit_of_hd_trail_int_lit_of_hd_trail] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_trail_ref_def trailt_ref_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_ref_assn_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_register extract_shorter_conflict_list_removed
sepref_register extract_shorter_conflict_l_trivial


(*extract_shorter_conflict_list_removed  *)
sepref_thm extract_shorter_conflict_list_removed_code
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_removed)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *assn
       option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>
  supply [[goals_limit = 1]] uint32_nat_assn_zero_uint32[sepref_fr_rules]
    Pot_unat_lit_assn[sepref_fr_rules] one_nat_uint32_def[simp]
    Neg_unat_lit_assn[sepref_fr_rules] zero_uint32_def[simp]
  unfolding extract_shorter_conflict_list_removed_def PR_CONST_def
  extract_shorter_conflict_list_int_def
  lit_of_hd_trail_def[symmetric] Let_def
   zero_uint32_def[symmetric]
  fast_minus_def[symmetric] one_nat_uint32_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_removed_code
   uses twl_array_code.extract_shorter_conflict_list_removed_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_removed_code_def

lemmas extract_shorter_conflict_list_removed_code_extract_shorter_conflict_list_removed[sepref_fr_rules] =
  extract_shorter_conflict_list_removed_code.refine[of N\<^sub>0,
      OF twl_array_code_axioms]

sepref_thm extract_shorter_conflict_l_trivial'
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_int)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *assn
       option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_def PR_CONST_def
  extract_shorter_conflict_list_int_def
  lit_of_hd_trail_def[symmetric] Let_def one_nat_uint32_def[symmetric]
  fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_l_trivial_code
   uses twl_array_code.extract_shorter_conflict_l_trivial'.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_def

lemmas extract_shorter_conflict_l_trivial_code_wl_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code.refine[of N\<^sub>0,
      OF twl_array_code_axioms]

type_synonym (in -) conflict_rel_with_cls_with_highest =
  \<open>conflict_option_rel \<times> (nat literal \<times> nat)option\<close>

definition option_conflict_rel_with_cls_with_highest2
  :: \<open>nat literal \<Rightarrow> (nat, 'a) ann_lits \<Rightarrow> (conflict_rel_with_cls_with_highest \<times> nat clause option) set\<close> where
  \<open>option_conflict_rel_with_cls_with_highest2 K M = {(((b, xs), L), D).
     D \<noteq> None \<and> ((b, xs), D) \<in> option_conflict_rel \<and> highest_lit M (remove1_mset K (the D)) L \<and>
     (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd xs))}\<close>

abbreviation option_conflict_rel_with_cls_with_highest where
  \<open>option_conflict_rel_with_cls_with_highest M \<equiv> option_conflict_rel_with_cls_with_highest2 (-lit_of (hd M)) M\<close>

lemmas option_conflict_rel_with_cls_with_highest_def = option_conflict_rel_with_cls_with_highest2_def

type_synonym (in -) conflict_with_cls_with_highest_assn =
   \<open>conflict_option_assn \<times> (uint32 \<times> uint32) option\<close>

abbreviation conflict_with_cls_int_with_highest_assn
 :: \<open>conflict_rel_with_cls_with_highest \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_with_highest_assn \<equiv>
    (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn)) *assn option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>

definition conflict_with_cls_with_cls_with_highest_assn
  :: \<open>(nat, 'a) ann_lits \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_with_cls_with_highest_assn M \<equiv>
    hr_comp conflict_with_cls_int_with_highest_assn (option_conflict_rel_with_cls_with_highest M)\<close>

lemma extract_shorter_conflict_list_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_list, uncurry (RETURN oo extract_shorter_conflict_l_trivial)) \<in>
  [\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> -lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M))]\<^sub>f
   Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: extract_shorter_conflict_list_def extract_shorter_conflict_l_trivial_def
      Let_def)

text \<open>
  This is the \<^emph>\<open>direct\<close> composition of the refinement theorems. Only the version lifted to
  state should be used (to get rid of the \<^term>\<open>M\<close> that appears in the refinement relation).
\<close>
lemma extract_shorter_conflict_l_trivial_code_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_l_trivial_code,
     uncurry (RETURN \<circ>\<circ> extract_shorter_conflict_l_trivial))
    \<in> [\<lambda>(M', D). M' \<noteq> [] \<and> literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None \<and> M' = M \<and>
         -lit_of (hd M) \<in># the D \<and>  0 < get_level M (lit_of (hd M)) \<and>
         literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and> literals_are_in_N\<^sub>0 (the D) \<and>
         distinct_mset (the D) \<and> \<not>tautology (the D)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> (conflict_with_cls_with_cls_with_highest_assn M)\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel)
       (\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> - lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M)))
       (\<lambda>_. comp_PRE (Id \<times>\<^sub>f option_conflict_rel)
              (\<lambda>(M', D). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
                  literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and> - lit_of (hd M) \<in># the D \<and>
                  lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and>
                  0 < get_level M (lit_of (hd M)) \<and> \<not> tautology (the D))
              (\<lambda>_ (M, b, n, xs). M \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
    hrp_comp (hrp_comp ((hr_comp trailt_conc trailt_ref)\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>d)
                       (Id \<times>\<^sub>f option_conflict_rel))
              (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel) \<rightarrow>
    hr_comp (hr_comp ((bool_assn *assn conflict_rel_assn) *assn
                        option_assn (unat_lit_assn *assn uint32_nat_assn))
                     {((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and>
                      highest_lit M (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
                       (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))})
             Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
       hfref_compI_PRE_aux[OF extract_shorter_conflict_l_trivial_code_wl_D[unfolded PR_CONST_def]
          extract_shorter_conflict_list_int_extract_shorter_conflict_list, of M]
       extract_shorter_conflict_list_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
    by (auto simp: comp_PRE_def option_conflict_rel_with_cls_def list_mset_rel_def br_def
        map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def[symmetric]
       conflict_with_cls_with_cls_with_highest_assn_def option_conflict_rel_with_cls_with_highest_def
       hr_comp_Id2
    apply (rule arg_cong[of _ _ \<open>hr_comp _\<close>])
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

type_synonym (in -) twl_st_wl_confl_extracted_int =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    conflict_rel_with_cls_with_highest \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

definition twl_st_ref_confl_extracted2 
  :: \<open>nat literal \<Rightarrow> (twl_st_wl_confl_extracted_int \<times> twl_st_wl_int) set\<close> where
\<open>twl_st_ref_confl_extracted2 L =
  {((M', N', U', D', Q', W', vm', \<phi>'), (M, N, U, D, Q, W, vm, \<phi>)).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest2 L M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi>
  }\<close>

definition twl_st_ref_confl_extracted :: \<open>(twl_st_wl_confl_extracted_int \<times> twl_st_wl_int) set\<close> where
\<open>twl_st_ref_confl_extracted =
  {((M', N', U', D', Q', W', vm', \<phi>'), (M, N, U, D, Q, W, vm, \<phi>)).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi>
  }\<close>

type_synonym (in -) twl_st_wll_trail_confl_extracted =
  \<open>trail_int_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_with_highest_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>


definition twl_st_confl_extracted_int_assn
  :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close> where
\<open>twl_st_confl_extracted_int_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_with_cls_int_with_highest_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  )\<close>

definition twl_st_confl_extracted_assn
  :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_ref_confl_extracted O twl_st_ref)\<close>

definition twl_st_confl_extracted_assn2
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn2 L = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_ref_confl_extracted2 L O twl_st_ref)\<close>

lemma extract_shorter_conflict_st_trivial_int_alt_def:
  \<open>extract_shorter_conflict_st_trivial_int = (\<lambda>(M, N, U, D, oth).
  RETURN (M, N, U, ASSN_ANNOT (conflict_with_cls_with_cls_with_highest_assn M)
     (extract_shorter_conflict_l_trivial M D), oth))\<close>
  unfolding extract_shorter_conflict_st_trivial_int_def ASSN_ANNOT_def ..


type_synonym (in -) twl_st_wl_int_W_confl_with_cls =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    conflict_rel_with_cls \<times> nat clause \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

definition twl_st_wl_int_W_confl_with_cls :: \<open>(twl_st_wl_int_W_confl_with_cls \<times> twl_st_wl_int) set\<close> where
  \<open>twl_st_wl_int_W_confl_with_cls =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     option_conflict_rel_with_cls \<times>\<^sub>r
     Id  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id\<close>

definition twl_st_wl_int_W_confl_with_cls_assn
  :: \<open>twl_st_wl_int_W_confl_with_cls \<Rightarrow> twl_st_wll_confl_with_cls \<Rightarrow> assn\<close> where
\<open>twl_st_wl_int_W_confl_with_cls_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_with_cls_int_assn *assn
  (list_mset_assn unat_lit_assn) *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc
  )\<close>

lemma twl_st_wl_int_W_confl_with_cls_twl_st_rel: \<open>twl_st_wl_int_W_confl_with_cls O twl_st_ref =
   {((M', N', U', D', Q', W', vm, \<phi>), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf_imp M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_ref_def twl_st_wl_int_W_confl_with_cls_def
  by force

definition twl_st_assn_confl_cls_int :: \<open>twl_st_wl_int \<Rightarrow> twl_st_wll_confl_with_cls \<Rightarrow> assn\<close> where
  \<open>twl_st_assn_confl_cls_int = hr_comp twl_st_wl_int_W_confl_with_cls_assn
     (twl_st_wl_int_W_confl_with_cls)\<close>

definition twl_st_assn_confl_cls :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_confl_with_cls \<Rightarrow> assn\<close> where
  \<open>twl_st_assn_confl_cls = hr_comp twl_st_wl_int_W_confl_with_cls_assn
     (twl_st_wl_int_W_confl_with_cls O twl_st_ref)\<close>

lemma twl_st_assn_confl_cls_int_alt_def:
  \<open>twl_st_assn_confl_cls_int = trail_assn *assn
         clauses_ll_assn *assn
         nat_assn *assn
         conflict_with_cls_assn *assn
         clause_l_assn *assn arrayO_assn (arl_assn nat_assn) *assn vmtf_remove_conc *assn phase_saver_conc\<close>
  unfolding twl_st_assn_confl_cls_int_def twl_st_wl_int_W_confl_with_cls_assn_def twl_st_wl_int_W_confl_with_cls_def
  hr_comp_prod_conv conflict_with_cls_assn_def[symmetric]
  by auto

lemma twl_st_assn_confl_cls_alt_def:
  \<open>twl_st_assn_confl_cls = hr_comp twl_st_assn_confl_cls_int twl_st_ref\<close>
  unfolding twl_st_assn_confl_cls_def twl_st_assn_confl_cls_int_def hr_comp_assoc ..

definition extract_shorter_conflict_list_st_int:: \<open>twl_st_wl_int_conflict \<Rightarrow> _ nres\<close> where
  \<open>extract_shorter_conflict_list_st_int = (\<lambda>(M, N, U, D, oth). do {
     D \<leftarrow> extract_shorter_conflict_list_int M D;
     RETURN (M, N, U, D, oth)})
\<close>

sepref_register extract_shorter_conflict_list_int
sepref_thm extract_shorter_conflict_list_st_int_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>(M,_). M \<noteq> []]\<^sub>a
      twl_st_int_conflict_assn\<^sup>d \<rightarrow>
        trail_assn *assn clauses_ll_assn *assn
       nat_assn *assn
       ((bool_assn *assn conflict_rel_assn) *assn option_assn (unat_lit_assn *assn uint32_nat_assn)) *assn
       clause_l_assn *assn
       arrayO_assn (arl_assn nat_assn) *assn
       vmtf_remove_conc *assn phase_saver_conc\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_st_int_def twl_st_int_conflict_assn_def
    PR_CONST_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_st_int_code
   uses twl_array_code.extract_shorter_conflict_list_st_int_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_st_int_code_def

lemmas extract_shorter_conflict_list_st_int_code[sepref_fr_rules] =
  extract_shorter_conflict_list_st_int_code.refine[of N\<^sub>0,
      OF twl_array_code_axioms]
typ twl_st_wl_confl_extracted_int
term extract_shorter_conflict_list_st_int

definition extract_shorter_conflict_list_st where
  \<open>extract_shorter_conflict_list_st =
     (\<lambda>(M, N, U, D, oth). do {
        D \<leftarrow> extract_shorter_conflict_list M D;
        RETURN (M, N, U, D, oth)})\<close>

lemma extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial:
  \<open>(extract_shorter_conflict_list_st, extract_shorter_conflict_st_trivial) \<in>
     [\<lambda>S. get_trail_wl S \<noteq> [] \<and> -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and> get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) > 0]\<^sub>f
     Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding extract_shorter_conflict_list_st_def extract_shorter_conflict_st_trivial_def
  extract_shorter_conflict_list_def
  by (intro frefI nres_relI)
    (auto simp: Let_def extract_shorter_conflict_l_trivial_def)

lemma extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_int:
  \<open>(extract_shorter_conflict_list_st_int, extract_shorter_conflict_st_trivial_int) \<in>
     [\<lambda>S. get_conflict_wl_int S \<noteq> None \<and> get_trail_wl_int S \<noteq> [] \<and>
     literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and>
         -lit_of (hd (get_trail_wl_int S)) \<in># the (get_conflict_wl_int S) \<and>
         0 < get_level (get_trail_wl_int S) (lit_of (hd (get_trail_wl_int S))) \<and>
         literals_are_in_N\<^sub>0 (lit_of `# mset (get_trail_wl_int S)) \<and> literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and>
         distinct_mset (the (get_conflict_wl_int S)) \<and> \<not>tautology (the (get_conflict_wl_int S))]\<^sub>f
      (twl_st_wl_int_conflict_rel) \<rightarrow> \<langle>twl_st_ref_confl_extracted\<rangle>nres_rel\<close>
proof -
  have H: \<open>a \<noteq> [] \<Longrightarrow>
   - lit_of (hd a) \<in># the ac \<Longrightarrow>
   (\<exists>y. ac = Some y) \<Longrightarrow> 0 < get_level a (lit_of (hd a)) \<Longrightarrow>
   extract_shorter_conflict_list_st (a, aa, ab, ac, ad, ae, af, b)
       \<le> \<Down> Id (RETURN (a, aa, ab, extract_shorter_conflict_l_trivial a ac, ad, ae, af, b))\<close>
    for a :: \<open>(nat, nat) ann_lits\<close> and aa :: \<open>nat clauses_l\<close> and
          ab :: nat and ac and ad ae :: \<open>nat clauses\<close> and af :: \<open>nat clause\<close> and
          b ::\<open>nat literal \<Rightarrow> nat list\<close>
    using extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial[unfolded fref_def
      extract_shorter_conflict_st_trivial_def nres_rel_def, simplified, rule_format,
      of a ac aa ab ad ae af b] by auto
  have H':
    \<open>M \<noteq> [] \<and>
     (\<exists>y. ba = Some y) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     literals_are_in_N\<^sub>0 (the ba) \<and>
     M \<noteq> [] \<and>
     literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     lit_of (hd M) \<notin># the ba \<and>
     distinct_mset (the ba) \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     \<not> tautology (the ba) \<and>
     ((a, aa, b), ba) \<in> option_conflict_rel \<Longrightarrow>
     extract_shorter_conflict_list_int M (a, aa, b)
     \<le> \<Down> {((D, L), C).
           (D, C) \<in> option_conflict_rel \<and>
           (\<exists>y. C = Some y) \<and>
           highest_lit M
            (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
           (\<forall>L\<in>atms_of N\<^sub>1. L < length (snd (snd D)))}
         (RETURN (extract_shorter_conflict_l_trivial M ba))\<close> for a aa b ba M
    using extract_shorter_conflict_list_int_extract_shorter_conflict_list
       [FCOMP extract_shorter_conflict_list_extract_shorter_conflict_l_trivial,
         unfolded fref_def
            extract_shorter_conflict_st_trivial_def nres_rel_def, of M] by auto
  show ?thesis
    apply (intro nres_relI frefI)
    subgoal for S' S
      apply (cases S; cases S')
      apply (auto simp: extract_shorter_conflict_list_st_int_def
          extract_shorter_conflict_st_trivial_int_def twl_st_wl_int_conflict_rel_def)
    apply (rule intro_bind_refine[OF H', of _ \<open>get_conflict_wl_int S\<close>])
    subgoal by auto
    subgoal
      by (auto simp: twl_st_ref_confl_extracted_def option_conflict_rel_with_cls_with_highest_def)
    done
  done
qed


fun get_trail_wl_int_conflict :: \<open>twl_st_wl_int_conflict \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_int_conflict (M, N, U, D, _) = M\<close>

sepref_register extract_shorter_conflict_list_st_int
sepref_thm extract_shorter_conflict_st_trivial_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>S. get_trail_wl_int_conflict S \<noteq> []]\<^sub>a twl_st_int_conflict_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding  twl_st_confl_extracted_int_assn_def PR_CONST_def
    extract_shorter_conflict_list_st_int_def twl_st_int_conflict_assn_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_st_trivial_code
   uses twl_array_code.extract_shorter_conflict_st_trivial_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

lemmas extract_shorter_conflict_st_code_refine[sepref_fr_rules] =
   extract_shorter_conflict_st_trivial_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

definition extract_shorter_conflict_st_trivial_pre where
  \<open>extract_shorter_conflict_st_trivial_pre S \<longleftrightarrow> (get_conflict_wl S \<noteq> None \<and>
          get_trail_wl S \<noteq> [] \<and>
          literals_are_in_N\<^sub>0 (the (get_conflict_wl S)) \<and>
          - lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
          0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) \<and>
          literals_are_in_N\<^sub>0 (lit_of `# mset (get_trail_wl S)) \<and>
          literals_are_in_N\<^sub>0 (the (get_conflict_wl S)) \<and>
          distinct_mset (the (get_conflict_wl S)) \<and> \<not> tautology (the (get_conflict_wl S)))\<close>

lemma extract_shorter_conflict_st_trivial_hnr[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_st_trivial) \<in>
    [extract_shorter_conflict_st_trivial_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
       \<in> [comp_PRE twl_st_ref (\<lambda>S. get_conflict_wl S \<noteq> None)
               (\<lambda>_. comp_PRE twl_st_wl_int_conflict_rel
                  (\<lambda>S. get_conflict_wl_int S \<noteq> None \<and>
                     get_trail_wl_int S \<noteq> [] \<and>
                     literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and>
                     - lit_of (hd (get_trail_wl_int S)) \<in># the (get_conflict_wl_int S) \<and>
                     0 < get_level (get_trail_wl_int S) (lit_of (hd (get_trail_wl_int S))) \<and>
                     literals_are_in_N\<^sub>0 (lit_of `# mset (get_trail_wl_int S)) \<and>
                     literals_are_in_N\<^sub>0 (the (get_conflict_wl_int S)) \<and> distinct_mset (the (get_conflict_wl_int S)) \<and> \<not> tautology (the (get_conflict_wl_int S)))
                 (\<lambda>_ S. get_trail_wl_int_conflict S \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
      hrp_comp (hrp_comp (twl_st_int_conflict_assn\<^sup>d) twl_st_wl_int_conflict_rel) twl_st_ref \<rightarrow>
     hr_comp (hr_comp twl_st_confl_extracted_int_assn twl_st_ref_confl_extracted) twl_st_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
        hfref_compI_PRE_aux[OF extract_shorter_conflict_st_code_refine[unfolded PR_CONST_def]
           extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_int]
         extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def twl_st_wl_int_conflict_rel_def extract_shorter_conflict_st_trivial_pre_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_ref_def
      map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl:
  \<open>(extract_shorter_conflict_st_trivial, extract_shorter_conflict_wl) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      get_conflict_wl S \<noteq> None \<and> no_skip S \<and> no_resolve S \<and> get_conflict_wl S \<noteq> Some {#}]\<^sub>f
    Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>extract_shorter_conflict_st_trivial S \<le>  (extract_shorter_conflict_wl S)\<close>
    if
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
      (is \<open>twl_struct_invs ?S\<close>) and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
      D: \<open>get_conflict_wl S \<noteq> None\<close> \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
      n_s_s: \<open>no_skip S\<close> and
      n_s_r: \<open>no_resolve S\<close>
    for S
  proof -
    obtain M N U D NP UP Q W where
      [simp]: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
      by (cases S)
    have
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of ?S)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?S)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl D unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    then have M_nempty: \<open>M ~= []\<close>
      using D by auto
    have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) \<Turnstile>p the D\<close>
      using that(2-) learned
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of ?S) \<Turnstile>pm
        filter_mset (\<lambda>L. get_level (trail (state\<^sub>W_of ?S)) L > 0) (the (conflicting (state\<^sub>W_of ?S)))\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(1))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using M_nempty by (cases M, auto simp: cdcl\<^sub>W_restart_mset_state)
      done
    moreover have \<open>- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of ?S)) \<in>#
      {#L \<in># the (conflicting (state\<^sub>W_of ?S)). 0 < get_level (trail (state\<^sub>W_of ?S)) L#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using M_nempty by (cases M, auto simp: cdcl\<^sub>W_restart_mset_state)
      done
    moreover have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) =
          mset ` set (tl N) \<union> set_mset NP \<union> set_mset UP\<close>
      apply (subst (2) append_take_drop_id[of U \<open>tl N\<close>, symmetric])
      unfolding set_append drop_Suc
      by auto
    ultimately show ?thesis
      using that(2-) D M_nempty
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
          extract_shorter_conflict_st_trivial_def extract_shorter_conflict_wl_def
          extract_shorter_conflict_l_trivial_def)
  qed
  show ?thesis
    by (intro frefI nres_relI) (auto intro!: H)
qed

definition extract_shorter_conflict_wl_pre where
  \<open>extract_shorter_conflict_wl_pre S \<longleftrightarrow>
      twl_struct_invs (twl_st_of_wl None S) \<and>
            twl_stgy_invs (twl_st_of_wl None S) \<and>
            get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> no_skip S \<and> no_resolve S \<and>
            literals_are_N\<^sub>0 S\<close>

lemma literals_are_N\<^sub>0_trail_literals_are_in_N\<^sub>0:
  assumes
    N\<^sub>0: \<open>literals_are_N\<^sub>0 S\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
  shows \<open>literals_are_in_N\<^sub>0 (lit_of `# mset (get_trail_wl S))\<close> (is \<open>literals_are_in_N\<^sub>0 ?M\<close>)
proof -
  have [simp]: \<open>lit_of ` set (convert_lits_l b a) =  lit_of ` set a\<close> for a b
    by (induction a) auto
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have N: \<open>atms_of ?M \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S)))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def atms_of_def
    by (cases S)
      (auto simp: mset_take_mset_drop_mset')

  have \<open>is_N\<^sub>1 (all_lits_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S))))\<close>
    using twl_struct_invs_is_N\<^sub>1_clauses_init_clss[OF struct] N\<^sub>0 by fast
  then show ?thesis
    using N in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff
    by (fastforce simp: literals_are_in_N\<^sub>0_def is_N\<^sub>1_def )
qed

lemma extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre:
  assumes \<open>extract_shorter_conflict_wl_pre S\<close>
  shows \<open>extract_shorter_conflict_st_trivial_pre S\<close>
proof -
  have
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    confl_nempty: \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
    n_s: \<open>no_skip S\<close> and
    n_r: \<open>no_resolve S\<close> and
    lits: \<open>literals_are_N\<^sub>0 S\<close>
    using assms unfolding extract_shorter_conflict_wl_pre_def by fast+

  have invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  have
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have lits_conf: \<open>literals_are_in_N\<^sub>0 (the (get_conflict_wl S))\<close>
    using literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[OF lits confl struct_invs] .

  have trail: \<open>get_trail_wl S \<noteq> []\<close>
    using conf confl confl_nempty unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def apply (cases S)
    by auto
  have uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># {#L \<in># the (get_conflict_wl S).
         0 < get_level (get_trail_wl S) L#}\<close>
    using cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2)[of \<open>state\<^sub>W_of (twl_st_of_wl None S)\<close>]
     n_s n_r confl invs stgy_invs trail confl_nempty unfolding no_skip_def no_resolve_def twl_stgy_invs_def
    by (cases S) simp
  have lev_L: \<open>0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S)))\<close> and
    uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close>
    using uL_D by auto

  have lits_trail: \<open>literals_are_in_N\<^sub>0 (lit_of `# mset (get_trail_wl S))\<close>
    using literals_are_N\<^sub>0_trail_literals_are_in_N\<^sub>0[OF lits struct_invs] .
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl S))\<close>
    using dist confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)

  have tr: \<open>get_trail_wl S \<Turnstile>as CNot (the (get_conflict_wl S))\<close>
    using conf confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    using lev_inv  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (cases S) (auto dest!: distinct_consistent_interp)
  have tauto: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
    using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
  show ?thesis
    using lits_conf confl trail lits_trail uL_D lev_L dist_confl tauto
    unfolding extract_shorter_conflict_st_trivial_pre_def
    by (intro conjI) fast+
qed

lemma extract_shorter_conflict_wl_code_extract_shorter_conflict_wl[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_wl)
    \<in> [extract_shorter_conflict_wl_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE Id
     (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
          twl_stgy_invs (twl_st_of_wl None S) \<and>
          get_conflict_wl S \<noteq> None \<and>
          no_skip S \<and>
          no_resolve S \<and> get_conflict_wl S \<noteq> Some {#})
     (\<lambda>_. extract_shorter_conflict_st_trivial_pre)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_assn\<^sup>d)
                    Id \<rightarrow> hr_comp twl_st_confl_extracted_assn
                           Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_shorter_conflict_st_trivial_hnr[unfolded PR_CONST_def]
        extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    using extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre[of x]
    unfolding comp_PRE_def extract_shorter_conflict_wl_pre_def
    by (auto simp: comp_PRE_def twl_st_ref_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by auto
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_confl_cls_alt_def by auto

  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed


definition find_decomp_wl_imp :: "(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> nat literal \<Rightarrow> vmtf_remove_int \<Rightarrow>
   ((nat, nat) ann_lits \<times> vmtf_remove_int) nres" where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 D L vm. do {
    let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) (the D));
    let k = count_decided M\<^sub>0;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M'))) \<and>
           vm' \<in> vmtf_imp M \<and> literals_are_in_N\<^sub>0 (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j > lev)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            if is_decided (hd M)
            then let L = atm_of (lit_of (hd M)) in RETURN (j-1, tl M, vmtf_unset L vm)
            else let L = atm_of (lit_of (hd M)) in RETURN (j, tl M, vmtf_unset L vm)}
         )
         (k, M\<^sub>0, vm);
    RETURN (M, vm')
  })\<close>

sepref_thm vmtf_unset_code
  is \<open>uncurry (RETURN oo vmtf_unset)\<close>
  :: \<open>[\<lambda>(L, vm). \<exists>M. L = atm_of(lit_of (hd M)) \<and> vm \<in> vmtf_imp M \<and> M \<noteq> [] \<and>
          literals_are_in_N\<^sub>0 (lit_of `# mset M)]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_imp_def[simp] in_N\<^sub>1_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_N\<^sub>0_add_mset[simp]
  unfolding vmtf_unset_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) vmtf_unset_code
   uses twl_array_code.vmtf_unset_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_unset_code_def

lemmas vmtf_unset_code_code[sepref_fr_rules] =
   vmtf_unset_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

definition find_decomp_wl_imp_pre where
  \<open>find_decomp_wl_imp_pre = (\<lambda>(((M, D), L), vm). M \<noteq> [] \<and> D \<noteq> None \<and>
      literals_are_in_N\<^sub>0 (the D) \<and> -L \<in># the D \<and>
      literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and> vm \<in> vmtf_imp M)\<close>

definition (in -) get_maximum_level_remove_int :: \<open>(nat, 'a) ann_lits \<Rightarrow>
    conflict_rel_with_cls_with_highest \<Rightarrow> nat literal \<Rightarrow>  nat\<close> where
  \<open>get_maximum_level_remove_int = (\<lambda>_ (_, D) _.
    (case D of None \<Rightarrow> 0 | Some i \<Rightarrow> snd i))\<close>

(* TODO Move *)
lemma (in -)snd_hnr_pure:
   \<open>CONSTRAINT is_pure B \<Longrightarrow> (return \<circ> snd, RETURN \<circ> snd) \<in> (A *assn B)\<^sup>k \<rightarrow>\<^sub>a B\<close>
  apply sepref_to_hoare
  apply sep_auto
  by (metis SLN_def SLN_left assn_times_comm ent_pure_pre_iff_sng ent_refl ent_star_mono
      ent_true is_pure_assn_def is_pure_iff_pure_assn)
(* End Move *)

sepref_thm get_maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo get_maximum_level_remove_int)\<close>
  :: \<open>trail_assn\<^sup>k  *\<^sub>a conflict_with_cls_int_with_highest_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a
       uint32_nat_assn\<close>
  supply uint32_nat_assn_zero_uint32[sepref_fr_rules]
    snd_hnr_pure[sepref_fr_rules]
  unfolding get_maximum_level_remove_int_def zero_uint32_def[symmetric]
  by sepref

concrete_definition (in -) get_maximum_level_remove_code
   uses twl_array_code.get_maximum_level_remove_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) get_maximum_level_remove_code_def

lemmas get_maximum_level_remove_code_hnr[sepref_fr_rules] =
   get_maximum_level_remove_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

definition (in -) get_maximum_level_remove' where
  \<open>get_maximum_level_remove' M D L = get_maximum_level_remove M (the D) L\<close>

lemma (in -)get_maximum_level_remove_single_removed[simp]: \<open>get_maximum_level_remove M {#L#} L = 0\<close>
  unfolding get_maximum_level_remove_def by auto

lemma (in -) get_maximum_level_remove_empty[simp]: \<open>get_maximum_level_remove M {#} = (\<lambda>_. 0)\<close>
 unfolding get_maximum_level_remove_def by auto

lemma get_maximum_level_remove_int_get_maximum_level_remove':
  \<open>(uncurry2 (RETURN ooo get_maximum_level_remove_int), uncurry2 (RETURN ooo get_maximum_level_remove')) \<in>
     [\<lambda>((M', D), L). M' = M \<and> L = -lit_of (hd M) \<and> M' \<noteq> [] \<and> D \<noteq> None]\<^sub>f Id \<times>\<^sub>f (option_conflict_rel_with_cls_with_highest M) \<times>\<^sub>f Id \<rightarrow>
    \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: get_maximum_level_remove_int_def get_maximum_level_remove'_def
      option_conflict_rel_with_cls_with_highest_def highest_lit_def
      get_maximum_level_remove_def[symmetric] remove1_mset_empty_iff
      split: option.splits)

lemma get_maximum_level_remove'_hnr[sepref_fr_rules]:
  \<open>(uncurry2 get_maximum_level_remove_code, uncurry2 (RETURN \<circ>\<circ>\<circ> get_maximum_level_remove'))
     \<in> [\<lambda>((a, b), ba). a = M \<and> ba = - lit_of (hd M) \<and> a \<noteq> [] \<and> b \<noteq> None]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
   uint32_nat_assn\<close>
  using get_maximum_level_remove_code_hnr[FCOMP get_maximum_level_remove_int_get_maximum_level_remove']
  unfolding conflict_with_cls_with_cls_with_highest_assn_def[symmetric] by simp

sepref_register find_decomp_wl_imp
sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry3 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>(((M', D), L), vm). M' = M \<and> L = lit_of (hd M') \<and> M' \<noteq> [] \<and> find_decomp_wl_imp_pre (((M', D), L), vm)]\<^sub>a
         trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_assn *assn vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def get_maximum_level_remove'_def[symmetric]
  supply [[goals_limit=1]]   literals_are_in_N\<^sub>0_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses twl_array_code.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

abbreviation (in -) nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>

definition find_decomp_wl_vmtf  where
  \<open>find_decomp_wl_vmtf =
     (\<lambda>(M::(nat, nat) ann_lits) (D::nat clause option) (L::nat literal) _.
        SPEC(\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1 \<and> vm \<in> vmtf_imp M1))\<close>


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, U, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, U, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat literal \<Rightarrow> twl_st_wl_int \<Rightarrow>
    twl_st_wl_int nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>L (M, N, U, D, W, Q, vm, \<phi>).  do{
     (M', vm) \<leftarrow> find_decomp_wl_vmtf M D L vm;
    RETURN (M', N, U, D, W, Q, vm, \<phi>)
  })\<close>


lemma
  assumes
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W))\<close> and
    D: \<open>D \<noteq> None\<close> \<open>E \<noteq> None\<close> \<open>the E \<noteq> {#}\<close> and M\<^sub>0: \<open>M\<^sub>0 \<noteq> []\<close> and ex_decomp: \<open>ex_decomp_of_max_lvl M\<^sub>0 D L\<close> and
    L: \<open>L = lit_of (hd M\<^sub>0)\<close> and
    E_D\<^sub>0: \<open>the E \<subseteq># the D\<close> and
    D\<^sub>0: \<open>D \<noteq> None\<close> and
   vm: \<open>vm \<in> vmtf_imp M\<^sub>0\<close> and
   lits: \<open>literals_are_in_N\<^sub>0 (lit_of `# mset M\<^sub>0)\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp M\<^sub>0 E L vm \<le>
          (* \<Down> {((M', vm'), (M, vm)). M = M' \<and> vm \<in> vmtf_imp M \<and> vm = vm' \<and>
               count_decided M' = get_maximum_level M\<^sub>0 (remove1_mset (-L) (the E)) } *)
            (find_decomp_wl_vmtf M\<^sub>0 E L vm)\<close>
     (is ?decomp)
proof -
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
  have \<open>distinct_mset (the D)\<close>
    using D\<^sub>0 dist by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)
  then have dist_D: \<open>distinct_mset (the E)\<close>
    using distinct_mset_mono[OF E_D\<^sub>0] by fast
  have \<open>M\<^sub>0 \<Turnstile>as CNot (the D)\<close>
    using D\<^sub>0 confl by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  then have M\<^sub>0_CNot_D: \<open>M\<^sub>0 \<Turnstile>as CNot (the E)\<close>
    using E_D\<^sub>0 by (simp add: mset_subset_eqD true_annots_true_cls_def_iff_negation_in_model)

  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
  have \<open>atm_of L \<notin> atms_of (remove1_mset (- L) (the E))\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>-L \<notin># remove1_mset (- L) (the E)\<close>
      using dist_D by (meson distinct_mem_diff_mset multi_member_last)
    ultimately have \<open>L \<in># the E\<close>
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
  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_N\<^sub>0 (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of N\<^sub>1\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_N\<^sub>0_add_mset in_N\<^sub>1_atm_of_in_atms_of_iff)
  thm WHILEIT_rule
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_wl_vmtf_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal by simp
    subgoal by auto
    subgoal using M\<^sub>0 by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal
      using ex_decomp get_level_Succ_count_decided_neq (*TODO Proof*)
      apply (auto simp: count_decided_butlast butlast_nil_iff eq_commute[of \<open>[_]\<close>] ex_decomp_of_max_lvl_def
          intro: butlast)
      by (metis E_D\<^sub>0 count_decided_ge_get_level get_maximum_level_mono mset_le_subtract
          not_less_eq_eq)
    subgoal using vm by auto
    subgoal using lits by auto
    subgoal using lits by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by (auto simp: count_decided_butlast count_decided_tl_if)[]
    subgoal for s a b aa ba x1 x2 x1a x2a by (cases aa) (auto simp: count_decided_ge_get_maximum_level)
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: abs_l_vmtf_unset_vmtf_unset' atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_N\<^sub>0_add_mset)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: abs_l_vmtf_unset_vmtf_unset' atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_N\<^sub>0_add_mset)
    subgoal by auto
    subgoal for s D M
      apply (auto simp: count_decided_ge_get_maximum_level ex_decomp_get_ann_decomposition_iff
          get_lev_last)
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append simp del: append_butlast_last_id)
        apply (metis append_butlast_last_id)
       defer
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append snoc_eq_iff_butlast' count_decided_ge_get_maximum_level
          ex_decomp_get_ann_decomposition_iff get_lev_last)
      done
    done
qed


definition find_decomp_wl_vmtf_pre where
  \<open>find_decomp_wl_vmtf_pre = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and>
      vm \<in> vmtf_imp M)\<close>

lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry3 find_decomp_wl_imp, uncurry3 find_decomp_wl_vmtf) \<in>
    [find_decomp_wl_vmtf_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: find_decomp_wl_vmtf_pre_def simp del: twl_st_of_wl.simps
     intro!: find_decomp_wl_imp_le_find_decomp_wl')

definition find_decomp_wl_vmtf_pre_full where
  \<open>find_decomp_wl_vmtf_pre_full M' = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_N\<^sub>0 (lit_of `# mset M) \<and>
      vm \<in> vmtf_imp M \<and> literals_are_in_N\<^sub>0 (the E) \<and> -L \<in># the E \<and> M = M')\<close>

lemma find_decomp_wl_pre_full_alt_def:
  \<open>find_decomp_wl_vmtf_pre_full M = (\<lambda>(((b, a), c), d). find_decomp_wl_vmtf_pre (((b, a), c), d) \<and>
         b = M \<and>
         c = lit_of (hd b) \<and>
         b \<noteq> [] \<and>
              find_decomp_wl_imp_pre (((b, a), c), d))\<close>
  apply (intro ext)
  unfolding find_decomp_wl_vmtf_pre_def find_decomp_wl_imp_pre_def find_decomp_wl_vmtf_pre_full_def
  by fastforce

sepref_register find_decomp_wl_vmtf
lemma find_decomp_wl_imp_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry3 find_decomp_wl_imp_code, uncurry3 (PR_CONST find_decomp_wl_vmtf))
     \<in> [find_decomp_wl_vmtf_pre_full M]\<^sub>a
     trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_assn *assn vmtf_remove_conc\<close>
  using find_decomp_wl_imp_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def find_decomp_wl_pre_full_alt_def[symmetric]
  .


(* TODO Move *)
lemma (in -) Down_itself_via_SPEC:
  assumes \<open>I \<le> SPEC P\<close> and \<open>\<And>x. P x \<Longrightarrow> (x, x) \<in> R\<close>
  shows \<open>I \<le> \<Down> R I\<close>
  using assms by (meson inres_SPEC pw_ref_I)
(* End Move *)

thm backtrack_wl_def

lemma (in -) bind_if_inverse:
  \<open>do {
    S \<leftarrow> H;
    if b then f S else g S
    } =
    (if b then do {S \<leftarrow> H; f S} else do {S \<leftarrow> H; g S})
  \<close> for H :: \<open>'a nres\<close>
  by auto

lemma get_all_ann_decomposition_get_level:
  assumes
    L': \<open>L' = lit_of (hd M')\<close> and
    nd: \<open>no_dup M'\<close> and
    decomp: \<open>(Decided K # a, M2) \<in> set (get_all_ann_decomposition M')\<close> and
    lev_K: \<open>get_level M' K = Suc (get_maximum_level M' (remove1_mset (- L') y))\<close> and
    L: \<open>L \<in># remove1_mset (- lit_of (hd M')) y\<close>
  shows \<open>get_level a L = get_level M' L\<close>
proof -
  obtain M3 where M3: \<open>M' = M3 @ M2 @ Decided K # a\<close>
    using decomp by blast
  from lev_K have lev_L: \<open>get_level M' L < get_level M' K\<close>
    using get_maximum_level_ge_get_level[OF L, of M'] unfolding L'[symmetric] by auto
  have [simp]: \<open>get_level (M3 @ M2 @ Decided K # a) K = Suc (count_decided a)\<close>
    using nd unfolding M3 by auto
  have undef:\<open>undefined_lit (M3 @ M2) L\<close>
    using lev_L get_level_skip_end[of \<open>M3 @ M2\<close> L \<open>Decided K # a\<close>] unfolding M3
    by auto
  then have \<open>atm_of L \<noteq> atm_of K\<close>
    using lev_L unfolding M3 by auto
  then show ?thesis
    using undef unfolding M3 by (auto simp: get_level_cons_if)

qed

lemma find_decomp_wl_st_int_find_decomp_wl_st:
  \<open>(uncurry find_decomp_wl_st_int, uncurry find_decomp_wl_st) \<in>
   [\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> get_trail_wl S = M \<and>
       no_dup (get_trail_wl S) \<and> L = lit_of(hd M)]\<^sub>f
   nat_lit_lit_rel \<times>\<^sub>r twl_st_ref \<rightarrow>
   \<langle>{(S', S). (S', S) \<in> twl_st_ref \<and>
     (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the (get_conflict_wl S)). get_level (get_trail_wl S) L = get_level M L)}\<rangle>nres_rel\<close>
  unfolding twl_st_wl_int_W_confl_with_cls_twl_st_rel
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for L' M' N' U' D' K' W' Q' A' m'  _ _ \<phi> L M N U D NP UP W Q
    apply (auto simp: find_decomp_wl_st_int_def find_decomp_wl_st_def option_conflict_rel_with_cls_def
        list_mset_rel_def br_def twl_st_ref_def
        intro!: bind_refine[where R' =
          \<open>{((Ms', vm'), Ms). Ms = Ms' \<and> (\<exists>M''. M = M'' @ Ms) \<and> vm' \<in> vmtf_imp Ms &
               (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the D). get_level Ms L = get_level M L)}\<close>]
          dest: no_dup_appendD)
    apply (auto simp: find_decomp_wl_vmtf_def find_decomp_wl'_def intro:
        dest: no_dup_appendD)
    apply (rule RES_refine)
    apply (auto)
      apply (rule_tac x=K in exI; auto 5 5)
     apply (auto intro: get_all_ann_decomposition_get_level)
    done
  done

fun set_conflict_wl where
  \<open>set_conflict_wl D (M, N, U, _, oth) = (M, N, U, D, oth)\<close>

definition twl_st_confl_extracted_int_assn' where
 \<open>twl_st_confl_extracted_int_assn' M =
  (hr_comp trailt_conc trailt_ref *assn
      clauses_ll_assn *assn
      nat_assn *assn
      conflict_with_cls_with_cls_with_highest_assn M *assn
      clause_l_assn *assn
      arrayO_assn (arl_assn nat_assn) *assn
      vmtf_remove_conc *assn phase_saver_conc)\<close>
term twl_st_confl_extracted_int_assn

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(L, (M', N, U, D, W, Q, vm, \<phi>)). find_decomp_wl_vmtf_pre_full M (((M', D), L), vm)]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a (twl_st_confl_extracted_int_assn' M)\<^sup>d \<rightarrow>
        (twl_st_confl_extracted_int_assn' M)\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def twl_st_int_assn_def twl_st_confl_extracted_int_assn'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses twl_array_code.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def

lemmas find_decomp_wl_imp'_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_code.refine[of N\<^sub>0, OF twl_array_code_axioms]


lemma find_decomp_wl_st_find_decomp_wl:
  \<open>(uncurry find_decomp_wl_st, uncurry find_decomp_wl) \<in> [\<lambda>_. True]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding no_resolve_def no_skip_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S')
        (auto intro!: find_decomp_wl_imp_le_find_decomp_wl'
        simp: find_decomp_wl_st_def find_decomp_wl'_def find_decomp_wl_def
        SPEC_RETURN_RES)
  done

thm
  find_decomp_wl_imp'_code_hnr
  find_decomp_wl_st_find_decomp_wl

(* TODO Move *)
lemma (in -) hfref_imp2: "(\<And>x y. S x y \<Longrightarrow>\<^sub>t S' x y) \<Longrightarrow> [P]\<^sub>a RR \<rightarrow> S \<subseteq> [P]\<^sub>a RR \<rightarrow> S'"
    apply clarsimp
    apply (erule hfref_cons)
    apply (simp_all add: hrp_imp_def)
    done

lemma (in -)hr_comp_mono_entails: \<open>B \<subseteq> C \<Longrightarrow> hr_comp a B x y \<Longrightarrow>\<^sub>A hr_comp a C x y\<close>
  unfolding hr_comp_def entails_def
  by auto

lemma (in -)hfref_imp_mono_result:
  "B \<subseteq> C \<Longrightarrow> [P]\<^sub>a RR \<rightarrow> hr_comp a B \<subseteq> [P]\<^sub>a RR \<rightarrow> hr_comp a C"
  unfolding hfref_def hn_refine_def
  apply clarify
  subgoal for aa b c aaa
    apply (rule cons_post_rule[of _ _
          \<open>\<lambda>r. snd RR aaa c * (\<exists>\<^sub>Ax. hr_comp a B x r * \<up> (RETURN x \<le> b aaa)) * true\<close>])
     apply (solves auto)
    using hr_comp_mono_entails[of B C a ]
    apply (auto intro!: ent_ex_preI)
    apply (rule_tac x=xa in ent_ex_postI)
    apply (auto intro!: ent_star_mono ac_simps)
    done
  done

lemma (in -) hfref_weaken_change_pre:
  assumes "(f,h) \<in> hfref P R S"
  assumes "\<And>x. P x \<Longrightarrow> (fst R x, snd R x) = (fst R' x, snd R' x)"
  assumes "\<And>y x. S y x \<Longrightarrow>\<^sub>t S' y x"
  shows "(f,h) \<in> hfref P R' S'"
proof -
  have \<open>(f,h) \<in> hfref P R' S\<close>
    using assms
    by (auto simp: hfref_def)
  then show ?thesis
    using hfref_imp2[of S S' P R'] assms(3) by auto
qed
(* End Move *)

lemma twl_st_ref_confl_extracted_twl_st_ref:
  \<open>twl_st_ref_confl_extracted O twl_st_ref =
    {((M', N', U', D', Q', W', vm, \<phi>), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf_imp M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_ref_confl_extracted_def twl_st_ref_def
  by force


lemma extract_shorter_conflict_st_trivial_hnr[sepref_fr_rules]:
  \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl) \<in>
    [\<lambda>(L, S). get_trail_wl S = M]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a twl_st_confl_extracted_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
       \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f Id)
     (\<lambda>(L, S).
         \<exists>D\<^sub>0. get_conflict_wl S \<noteq> None \<and>
               the (get_conflict_wl S) \<noteq> {#} \<and>
               get_trail_wl S \<noteq> [] \<and>
               ex_decomp_of_max_lvl (get_trail_wl S)
                (get_conflict_wl S) L \<and>
               L = lit_of (hd (get_trail_wl S)) \<and>
               twl_struct_invs
                (twl_st_of_wl None (set_conflict_wl D\<^sub>0 S)) \<and>
               the (get_conflict_wl S) \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None)
     (\<lambda>_. comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_ref)
           (\<lambda>(L, S).
               get_conflict_wl S \<noteq> None \<and>
               get_conflict_wl S \<noteq> Some {#})
           (\<lambda>_ (L, M', N, U, D, W, Q, vm, \<phi>).
               find_decomp_wl_vmtf_pre_full M (((M', D), L), vm))
           (\<lambda>_. True))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    (hrp_comp
                      (unat_lit_assn\<^sup>k *\<^sub>a
                       (twl_st_confl_extracted_int_assn' M)\<^sup>d)
                      (nat_lit_lit_rel \<times>\<^sub>f twl_st_ref))
                    (nat_lit_lit_rel \<times>\<^sub>f
                     Id) \<rightarrow> hr_comp
                             (hr_comp
                               (twl_st_confl_extracted_int_assn' M)
                               twl_st_ref)
                             Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[
      OF hfref_compI_PRE_aux[OF find_decomp_wl_imp'_code_hnr[unfolded PR_CONST_def]
            find_decomp_wl_st_int_find_decomp_wl_st]
         find_decomp_wl_st_find_decomp_wl]

    .
  have HH: \<open>H = H' \<Longrightarrow> unat_lit_assn *assn H = unat_lit_assn *assn H'\<close> for H H'
    by auto
  have 2: \<open>(a *assn b *assn c *assn (hr_comp d d')*assn e *assn f*assn g) =
       hr_comp (a *assn b *assn c *assn d *assn e *assn f *assn g)
           (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r d' \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)\<close>
    for a :: \<open>'a \<Rightarrow> 'b \<Rightarrow> assn\<close> and  b c d d' e f g
    by auto

  define twl_st_ref' :: \<open>(twl_st_wl_int \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_ref' =
      {((M'', N', U', D', Q', W', vm, \<phi>), (M', N, U, D, NP, UP, Q, W)).
        M' = M'' \<and> M' = M \<and> N' = N \<and> U' = U \<and> D = D' \<and>
         Q' = Q \<and>
        (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
        vm \<in> vmtf_imp M \<and>
        phase_saving \<phi> \<and>
        no_dup M
      }\<close>
  have decomp_1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_ref
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp (twl_st_confl_extracted_int_assn' M)
            (twl_st_ref')
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    by (auto simp: hr_comp_def twl_st_ref_def twl_st_ref'_def ex_assn_pair_split intro!: ext)
  have decomp_2: \<open>hr_comp twl_st_confl_extracted_int_assn
     (twl_st_ref_confl_extracted O twl_st_ref) (M, aa, ab, ac, ad, ae, af, b) =
       hr_comp twl_st_confl_extracted_int_assn
     (twl_st_ref_confl_extracted O twl_st_ref') (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
  proof -
    have [simp]: \<open>(a, M, X) \<in> twl_st_ref_confl_extracted O twl_st_ref \<longleftrightarrow>
          (a, M, X) \<in> twl_st_ref_confl_extracted O twl_st_ref'\<close> for X a
      by (auto simp: twl_st_ref_confl_extracted_def twl_st_ref_def twl_st_ref'_def)
    show ?thesis
      by (auto simp: hr_comp_def intro!: ext)
  qed
  have decomp: \<open>((Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (option_conflict_rel_with_cls_with_highest M \<times>\<^sub>f
          (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))) O twl_st_ref') =
     (twl_st_ref_confl_extracted O twl_st_ref')\<close>
    apply (auto simp: twl_st_ref_confl_extracted_def twl_st_ref'_def)
     apply fast
    apply force
    done
  have 1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_ref
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp twl_st_confl_extracted_int_assn
         (twl_st_ref_confl_extracted O twl_st_ref)
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    apply (subst decomp_1)
    apply (subst decomp_2)

    unfolding twl_st_confl_extracted_int_assn'_def twl_st_ref_confl_extracted_twl_st_ref
    twl_st_confl_extracted_int_assn_def conflict_with_cls_with_cls_with_highest_assn_def
    apply (subst 2)
    apply (subst hr_comp_assoc)
    apply (subst decomp)
    ..
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    sorry
  have \<open>?c \<in> [?pre]\<^sub>a ?im' \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H apply assumption
    using pre ..
  then have \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_change_pre)
    subgoal
      unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
        twl_st_confl_extracted_assn_def hr_comp_assoc
      by (auto simp: 1 intro!: ext)
    subgoal
      by auto
    done
  then have 3: \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl)
    \<in> [\<lambda>(L, S).
           get_trail_wl S =
           M]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                (hr_comp twl_st_confl_extracted_int_assn
                  (twl_st_ref_confl_extracted O
                   twl_st_ref))\<^sup>d \<rightarrow> hr_comp twl_st_confl_extracted_int_assn
                                      ((Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (option_conflict_rel_with_cls_with_highest M \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))) O
                                       twl_st_ref)\<close>
    (is \<open>?c \<in> [_]\<^sub>a _ \<rightarrow> hr_comp _ ?ref\<close>)
    unfolding twl_st_confl_extracted_int_assn'_def hr_comp_Id2
      conflict_with_cls_with_cls_with_highest_assn_def
      twl_st_confl_extracted_assn_def
    apply (subst (asm) 2)
    unfolding twl_st_confl_extracted_int_assn_def[symmetric] hr_comp_assoc
    .

  have incl: \<open>?ref \<subseteq> twl_st_ref_confl_extracted O twl_st_ref\<close>
    unfolding twl_st_ref_confl_extracted_twl_st_ref
    apply (auto simp: twl_st_ref_def)
    sorry
  show ?thesis
    unfolding twl_st_confl_extracted_assn_def
    apply (rule subsetD[OF hfref_imp_mono_result[OF incl]])
    apply (rule 3)
    done
  oops

  term find_lit_of_max_level

unfolding twl_st_assn_confl_assn
  twl_st_confl_extracted_int_assn'_def twl_st_ref_def twl_st_ref_confl_extracted_def
twl_st_confl_extracted_int_assn_def
    apply (auto intro!: H)
  have \<open>(hr_comp (twl_st_confl_extracted_int_assn' M)
      (twl_st_ref O Id))\<^sup>d =
    (hr_comp twl_st_confl_extracted_int_assn
      (twl_st_ref_confl_extracted O twl_st_ref))\<^sup>d\<close>
    unfolding twl_st_confl_extracted_int_assn'_def twl_st_confl_extracted_int_assn_def

    apply auto
    sorry
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn
    apply simp
    sorry
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn sorry

  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry find_decomp_wl_st\<close>
  :: \<open>[\<lambda>(L, S). get_conflict_wl S \<noteq> Some {#} \<and> get_trail_wl S \<noteq> [] \<and> literals_are_in_N\<^sub>0 D]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a twl_st_confl_extracted_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
  unfolding find_decomp_wl_st_def PR_CONST_def twl_st_int_assn_def
  supply [[goals_limit = 1]]
 apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  -- \<open>Translation stops at the \<open>set\<close> operation\<close>
                  apply sepref_dbg_trans_step_keep
                    apply sepref_dbg_side_unfold apply (auto simp: )[]



lemma find_decomp_wl_code[sepref_fr_rules]:
  \<open>(uncurry8 find_decomp_wl_imp'_code,
      uncurry8 find_decomp_wl')
  \<in> [\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). \<exists>D\<^sub>0. D \<noteq> {#} \<and> M \<noteq> [] \<and> ex_decomp_of_max_lvl M (Some D) L \<and> L = lit_of (hd M) \<and>
       (twl_struct_invs (twl_st_of_wl None (M, N, U, D\<^sub>0, NP, UP, Q, W)) \<and>
       literals_are_in_N\<^sub>0 D \<and> D \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None)]\<^sub>a
    (trail_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k
    \<rightarrow> trail_assn\<close>
  (is \<open> _ \<in> [?P]\<^sub>a _ \<rightarrow> _\<close>)
proof -
  have H: \<open>(uncurry8 find_decomp_wl_imp'_code, uncurry8 find_decomp_wl')
    \<in> [\<lambda>((((((((a, b), ba), bb), bc), bd), be), bf), bg).
        bb \<noteq> {#} \<and>
        a \<noteq> []\<and>
        ex_decomp_of_max_lvl a (Some bb) bg \<and>
        bg = lit_of (hd a) \<and>
        (\<exists>D\<^sub>0. twl_struct_invs
                (convert_lits_l b a,
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (take ba (tl b))#},
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (drop (Suc ba) b)#},
                 D\<^sub>0, bc, bd, {#}, be) \<and>
               bb \<subseteq># the D\<^sub>0 \<and> (\<exists>y. D\<^sub>0 = Some y)) \<and>
        literals_are_in_N\<^sub>0
         bb]\<^sub>a
     (trail_assn)\<^sup>d *\<^sub>a (arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
        clauses_l_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a
     (hr_comp (arrayO_assn (arl_assn nat_assn))
         (\<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset N\<^sub>1)))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
     trail_assn\<close>
    (is \<open> _ \<in> [?Q]\<^sub>a _ \<rightarrow> _\<close>)
    using find_decomp_wl_imp'_code.refine[unfolded find_decomp_wl_imp'_def PR_CONST_def, FCOMP
        find_decomp_wl_imp_find_decomp_wl'[unfolded find_decomp_wl_imp'_def], OF twl_array_code_axioms]
      .

  have QP: \<open>?Q = ?P\<close>
    by (auto intro!: ext)
  show ?thesis
    using H unfolding QP .
qed

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context twl_array_code
begin

lemma backtrack_wl_D_invD:
  assumes \<open>backtrack_wl_D_inv S\<close>
  shows \<open>get_trail_wl S \<noteq> []\<close> \<open>extract_shorter_conflict_wl_pre S\<close>
  using assms unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl
  apply (cases S; auto)
  using assms literals_are_N\<^sub>0_conflict_literals_are_in_N\<^sub>0[of S]
  unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl get_conflict_l_st_l_of_wl
  no_skip_def no_resolve_def
  by (auto simp del: split_paired_All)

sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] backtrack_wl_D_invD[simp]
  unfolding backtrack_wl_D_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  -- \<open>Translation stops at the \<open>set\<close> operation\<close>
                  apply sepref_dbg_trans_step_keep
                    apply sepref_dbg_side_unfold apply (auto simp: )[]
  by sepref \<comment> \<open>slow\<close>


concrete_definition (in -) backtrack_wl_D_code
   uses twl_array_code.backtrack_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]



subsubsection \<open>Operations on the trail\<close>

paragraph \<open>Cons\<close>

definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trailt_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trailt \<Rightarrow> trailt\<close> where
  \<open>cons_trailt_Propagated_tr = (\<lambda>L C (M', xs, lvls, k).
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)],
      lvls[atm_of L := k], k))\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', vm, \<phi>).
     (cons_trailt_Propagated_tr L C M', vm, \<phi>))\<close>

end


context twl_array_code
begin

lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
    (auto simp: trail_ref_def valued_atm_on_trail_def cons_trail_Propagated_def uminus_lit_swap
        trailt_ref_def cons_trailt_Propagated_tr_def
        cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update'
      dest: vmtf_imp_consD)

lemma undefined_lit_count_decided_upperN:
  assumes
    M_N\<^sub>1: \<open>\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>Suc (count_decided M) < upperN\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# N\<^sub>1)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# N\<^sub>1))\<close>
    using length_filter_le[of is_decided M] unfolding upperN_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset N\<^sub>1))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># N\<^sub>1 \<Longrightarrow> atm_of xa < upperN div 2\<close> for xa
    using in_N1_less_than_upperN
    by (cases xa) (auto simp: upperN_def)
  have \<open>remdups_mset (atm_of `# N\<^sub>1) \<subseteq># mset [0..<upperN div 2]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (auto simp del: literal_of_nat.simps simp: distinct_mset_mset_set)
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset N\<^sub>1) = size (remdups_mset N\<^sub>1)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# N\<^sub>1)) \<le> upperN div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: upperN_def)
qed

sepref_thm cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), ((M, xs, lvls, k), vm, \<phi>)). atm_of L < length xs \<and> atm_of L < length lvls]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d \<rightarrow> trail_conc\<close>
  unfolding cons_trail_Propagated_tr_def cons_trailt_Propagated_tr_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_code
  uses "twl_array_code.cons_trail_Propagated_tr_code.refine_raw"
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Propagated_tr_code_def

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] = cons_trail_Propagated_tr_code.refine[OF twl_array_code_axioms]

lemma cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
  \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_ref)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), ((M, xs, lvls, k), vm, \<phi>)). atm_of L < length xs \<and> atm_of L < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trail_ref) \<rightarrow> hr_comp trail_conc trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr,
        OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def trailt_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

fun (in twl_array_code_ops) cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition (in twl_array_code_ops) cons_trailt_Decided_tr :: \<open>nat literal \<Rightarrow> trailt \<Rightarrow> trailt\<close> where
  \<open>cons_trailt_Decided_tr = (\<lambda>L (M', xs, lvls, k).
     (Decided L # M', xs[atm_of L := Some (is_pos L)], lvls[atm_of L := k+1], k+1))\<close>

definition (in twl_array_code_ops) cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_int \<Rightarrow> trail_int\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', vm, \<phi>). (cons_trailt_Decided_tr L M', vm, \<phi>))\<close>

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
    (auto simp: trail_ref_def trailt_ref_def valued_atm_on_trail_def cons_trail_Decided_tr_def
        cons_trailt_Decided_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update'
        uminus_lit_swap
      dest: vmtf_imp_consD)

lemma (in -) bind_ref_tag_False_True: \<open>bind_ref_tag a (RETURN b) \<longleftrightarrow> a=b\<close>
  unfolding bind_ref_tag_def by auto

lemma undefined_lit_count_decided_upperN':
  assumes
    M_N\<^sub>1: \<open>\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close> and v: \<open>v = 1\<close>
  shows \<open>count_decided M + v < upperN\<close>
  using undefined_lit_count_decided_upperN[OF assms(1-4)] unfolding v by simp

lemma undefined_lit_count_decided_upperN'':
  assumes
    M_N\<^sub>1: \<open>\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>count_decided M < upperN - 1\<close>
  using undefined_lit_count_decided_upperN[OF assms(1-4)] by simp

sepref_thm cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, ((M, xs, lvls, k), vm, \<phi>)). atm_of L < length xs \<and> atm_of L < length lvls \<and>
       (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1) \<and> k = count_decided M \<and> undefined_lit M L \<and> no_dup M \<and>
        L \<in> snd ` D\<^sub>0]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d \<rightarrow>
    trail_conc\<close>
  unfolding cons_trail_Decided_tr_def cons_trailt_Decided_tr_def
  supply [[goals_limit = 1]]
  supply undefined_lit_count_decided_upperN'[intro!] upperN_def[symmetric]
  supply uint32_nat_assn_one[sepref_fr_rules] bind_ref_tag_False_True[simp]
  supply undefined_lit_count_decided_upperN''[unfolded upperN_def, simplified, intro!]
  by sepref

concrete_definition (in -) cons_trail_Decided_tr_code
  uses "twl_array_code.cons_trail_Decided_tr_code.refine_raw"
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) cons_trail_Decided_tr_code_def

lemmas cons_trail_Decided_tr_code[sepref_fr_rules] = cons_trail_Decided_tr_code.refine[OF twl_array_code_axioms]

lemma cons_trail_Decided_tr_code_cons_trail_Decided_tr[sepref_fr_rules]:
  \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN \<circ>\<circ> cons_trail_Decided))
    \<in> [comp_PRE (Id \<times>\<^sub>f trail_ref) (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
        (\<lambda>_ (L, ((M, xs, lvls, k), vm, \<phi>)).
            atm_of L < length xs \<and>
            atm_of L < length lvls \<and>
            (\<forall>L\<in>set M. lit_of L \<in># N\<^sub>1) \<and>
            k = count_decided M \<and> undefined_lit M L \<and> no_dup M \<and> L \<in> snd ` D\<^sub>0)
        (\<lambda>_. True)]\<^sub>a hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a trail_conc\<^sup>d) (Id \<times>\<^sub>f trail_ref) \<rightarrow>
          hr_comp trail_conc trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_code.refine cons_trail_Decided_tr, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def trailt_ref_def image_image intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed


paragraph \<open>tl\<close>

definition (in twl_array_code_ops) tl_trailt_tr :: \<open>trailt \<Rightarrow> trailt\<close> where
  \<open>tl_trailt_tr = (\<lambda>(M', xs, lvls, k). (tl M', xs[atm_of (lit_of (hd M')) := None], lvls[atm_of (lit_of (hd M')) := 0],
    if is_decided (hd M') then k-1 else k))\<close>

definition (in twl_array_code_ops) tl_trail_tr :: \<open>trail_int \<Rightarrow> trail_int\<close> where
  \<open>tl_trail_tr = (\<lambda>(M', vm, \<phi>). (tl_trailt_tr M', vmtf_unset (atm_of (lit_of (hd (fst M')))) vm, \<phi>))\<close>

lemma tl_trail_tr:
  \<open>((RETURN o tl_trail_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
proof -
  have \<open>La \<notin> A \<Longrightarrow>  -La \<notin> A \<Longrightarrow> Pos (atm_of La) \<in> A \<Longrightarrow> False\<close> for La A
    by (metis literal.exhaust_sel uminus_Pos uminus_Neg)
  have [intro]:
    \<open>Pos (atm_of La) \<notin> lits_of_l M's \<Longrightarrow> Neg (atm_of La) \<notin> lits_of_l M's \<Longrightarrow> get_level M's La = 0\<close>
    for La M's
    by (rule atm_of_notin_get_level_eq_0) (cases La; auto simp: Decided_Propagated_in_iff_in_lits_of_l)


  show ?thesis \<comment> \<open>TODO tune proof\<close>
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_ref_def comp_def RETURN_refine_iff trailt_ref_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal by (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def)
      subgoal by (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def)
      subgoal \<comment> \<open>Trail ref\<close>
        by (cases \<open>lit_of L\<close>)
            (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def
          Decided_Propagated_in_iff_in_lits_of_l eq_commute[of _ \<open>lit_of _\<close>] )
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal \<comment> \<open>VMTF\<close>
        by (auto simp: tl_trail_tr_def tl_trailt_tr_def in_N\<^sub>1_atm_of_in_atms_of_iff
            dest: no_dup_consistentD abs_l_vmtf_unset_vmtf_unset')
      subgoal \<comment> \<open>Phase saving\<close>
        by (auto simp: tl_trail_tr_def tl_trailt_tr_def)
      done
    done
qed

lemma tl_trail_tr_alt_def:
  \<open>tl_trail_tr = case_prod
    (\<lambda>(M', xs, lvls, k) (((A, m, lst, next_search), removed), \<phi>).
        let trail = tl M'; K = hd M'; L = atm_of (lit_of K) in
        ((tl M', xs[L := None], lvls[L := 0], if is_decided K then k - 1 else k),
            if next_search = None \<or> stamp (A ! the next_search) < stamp (A ! L)
                        then ((A, m, lst, Some L), removed) else ((A, m, lst, next_search), removed),
        \<phi>))\<close>
  unfolding tl_trail_tr_def tl_trailt_tr_def vmtf_unset_def
  by (auto intro!: ext simp: Let_def)

sepref_thm tl_trail_tr_code
  is \<open>RETURN o tl_trail_tr\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), ((A, m, lst, next_search), _), \<phi>). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and>
          atm_of (lit_of (hd M)) < length lvls \<and> atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
         (is_decided (hd M) \<longrightarrow> k \<ge> 1)]\<^sub>a
        trail_conc\<^sup>d \<rightarrow> trail_conc\<close>
  supply if_splits[split] option.splits[split] bind_ref_tag_False_True[simp]
  unfolding tl_trail_tr_alt_def
  apply (rewrite at \<open>_ = None \<or> _\<close> short_circuit_conv)
  apply (rewrite at \<open>_ - 1\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_zero[sepref_fr_rules]
  by sepref

concrete_definition (in -) tl_trail_tr_code
  uses twl_array_code.tl_trail_tr_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_code_def

lemmas tl_trail_tr_coded_refine[sepref_fr_rules] =
   tl_trail_tr_code.refine[of N\<^sub>0, OF twl_array_code_axioms]


lemma tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
  \<open>(tl_trail_tr_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, b), x) \<in> trailt_ref \<Longrightarrow> x = a\<close> for a aa ab b x
    by (auto simp: trailt_ref_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
  have H: \<open>(tl_trail_tr_code, RETURN \<circ> tl)
     \<in> [comp_PRE trail_ref (\<lambda>M. M \<noteq> [])
     (\<lambda>_ ((M, xs, lvls, k), ((A, m, lst, next_search), uu), \<phi>).
         M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length xs \<and>
         atm_of (lit_of (hd M)) < length lvls \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow> the next_search < length A) \<and>
         (is_decided (hd M) \<longrightarrow> k \<ge> 1))
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_conc\<^sup>d) trail_ref \<rightarrow> hr_comp trail_conc trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_code.refine tl_trail_tr, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def trailt_ref_def phase_saving_def
        in_N\<^sub>1_atm_of_in_atms_of_iff vmtf_imp_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed

paragraph \<open>tl and dump\<close>

definition (in -) tl_dump where
  \<open>tl_dump = tl\<close>

definition (in -) rescore :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>rescore M = M\<close>

definition (in twl_array_code_ops) tl_trail_tr_dump :: \<open>trail_int \<Rightarrow> trail_int\<close> where
  \<open>tl_trail_tr_dump =
     (\<lambda>(M', vm, \<phi>). (tl_trailt_tr M', vmtf_dump_and_unset (atm_of (lit_of (hd (fst M')))) vm,
      save_phase (lit_of (hd (fst M'))) \<phi>))\<close>


lemma tl_trail_tr_dump:
  \<open>((RETURN o tl_trail_tr_dump), (RETURN o tl_dump)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_ref \<rightarrow> \<langle>trail_ref\<rangle>nres_rel\<close>
proof -
  have \<open>La \<notin> A \<Longrightarrow>  -La \<notin> A \<Longrightarrow> Pos (atm_of La) \<in> A \<Longrightarrow> False\<close> for La A
    by (metis literal.exhaust_sel uminus_Pos uminus_Neg)
  have [intro]:
    \<open>Pos (atm_of La) \<notin> lits_of_l M's \<Longrightarrow> Neg (atm_of La) \<notin> lits_of_l M's \<Longrightarrow> get_level M's La = 0\<close>
    for La M's
    by (rule atm_of_notin_get_level_eq_0) (cases La; auto simp: Decided_Propagated_in_iff_in_lits_of_l)


  show ?thesis \<comment> \<open>TODO tune proof\<close>
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_ref_def comp_def RETURN_refine_iff trailt_ref_def tl_dump_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal by (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_dump_def tl_trailt_tr_def)
      subgoal by (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_def tl_trailt_tr_def)
      subgoal \<comment> \<open>Trail ref\<close>
        by (cases \<open>lit_of L\<close>)
            (auto simp: trail_ref_def valued_atm_on_trail_def tl_trail_tr_dump_def tl_trailt_tr_def
          Decided_Propagated_in_iff_in_lits_of_l eq_commute[of _ \<open>lit_of _\<close>] )
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trail_tr_dump_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trail_tr_dump_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: valued_atm_on_trail_def tl_trailt_tr_def atm_of_eq_atm_of get_level_cons_if)
      subgoal \<comment> \<open>VMTF\<close>
        by (auto simp: tl_trail_tr_def tl_trail_tr_dump_def in_N\<^sub>1_atm_of_in_atms_of_iff
            dest: no_dup_consistentD abs_l_vmtf_unset_vmtf_dump_unset)
      subgoal \<comment> \<open>Phase saving\<close>
        by (auto simp: tl_trail_tr_def tl_trail_tr_dump_def save_phase_def phase_saving_def)
      done
    done
qed



lemma tl_trail_tr_dump_alt_def:
  \<open>tl_trail_tr_dump = case_prod
    (\<lambda>(M', xs, lvls, k) (((A, m, lst, next_search), removed), \<phi>).
        let trail = tl M'; K = hd M'; L = atm_of (lit_of K) in
        ((tl M', xs[L := None], lvls[L := 0], if is_decided K then k - 1 else k),
            vmtf_dump_and_unset L ((A, m, lst, next_search), removed),
        save_phase (lit_of K) \<phi>))\<close>
  unfolding tl_trail_tr_dump_def tl_trailt_tr_def
  by (auto intro!: ext simp: Let_def)

sepref_thm tl_trail_tr_dump_code
  is \<open>RETURN o tl_trail_tr_dump\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), ((A, m, lst, next_search), _), \<phi>). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and>
          atm_of (lit_of (hd M)) < length lvls \<and> atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
         (is_decided (hd M) \<longrightarrow> k \<ge> 1)]\<^sub>a
        trail_conc\<^sup>d \<rightarrow> trail_conc\<close>
  supply if_splits[split] option.splits[split] bind_ref_tag_False_True[simp]
  unfolding tl_trail_tr_dump_alt_def save_phase_def vmtf_dump_and_unset_def vmtf_dump_def
   vmtf_unset_def
  apply (rewrite at \<open>_ = None \<or> _\<close> short_circuit_conv)
  apply (rewrite at \<open>_ - 1\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_zero[sepref_fr_rules]
  by sepref


concrete_definition (in -) tl_trail_tr_dump_code
  uses twl_array_code.tl_trail_tr_dump_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_dump_code_def

lemmas tl_trail_tr_dump_code_refine[sepref_fr_rules] =
   tl_trail_tr_dump_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma tl_trail_tr_dump_code_op_list_tl[sepref_fr_rules]:
  \<open>(tl_trail_tr_dump_code, (RETURN o tl_dump)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, b), x) \<in> trailt_ref \<Longrightarrow> x = a\<close> for a aa ab b x
    by (auto simp: trailt_ref_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
  have H: \<open>(tl_trail_tr_dump_code, RETURN \<circ> tl_dump)
     \<in> [comp_PRE trail_ref (\<lambda>M. M \<noteq> [])
     (\<lambda>_ ((M, xs, lvls, k), ((A, m, lst, next_search), uu), \<phi>).
         M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length xs \<and>
         atm_of (lit_of (hd M)) < length lvls \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow> the next_search < length A) \<and>
         (is_decided (hd M) \<longrightarrow> k \<ge> 1))
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_conc\<^sup>d) trail_ref \<rightarrow> hr_comp trail_conc trail_ref\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_dump_code.refine tl_trail_tr_dump, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def trailt_ref_def phase_saving_def
        in_N\<^sub>1_atm_of_in_atms_of_iff vmtf_imp_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed



lemma hd_trail[sepref_fr_rules]:
  \<open>(return o hd o fst o fst, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>k \<rightarrow> pair_nat_ann_lit_assn\<close>
  apply sepref_to_hoare
  apply (auto simp: trail_assn_def trail_ref_def mod_star_conv hr_comp_def intro!: return_cons_rule)
  apply (case_tac x)
   apply auto
  apply (case_tac a)
   apply (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def trailt_ref_def)
  apply (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def trailt_ref_def mod_star_conv)
  done

sepref_thm is_decided_hd_trail_wll_code
  is \<open>is_decided_hd_trail_wll\<close>
  :: \<open>[\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wll_def twl_st_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) is_decided_hd_trail_wll_code
   uses twl_array_code.is_decided_hd_trail_wll_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) is_decided_hd_trail_wll_code_def

lemmas is_decided_hd_trail_wll_code_refine[sepref_fr_rules] =
   is_decided_hd_trail_wll_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]



lemma
  trail_assn_Cons_Nil:
     \<open>hr_comp trailt_conc trailt_ref (a # list) ([], ah, ba) = false\<close> and
  trail_assn_Cons_Decided_Some:
     \<open>hr_comp trailt_conc trailt_ref  (Decided x1 # list) ((aba, Some x2) # list', ah, ba) = false\<close> and
  trail_assn_Cons_Propagated_None:
    \<open>hr_comp trailt_conc trailt_ref  (Propagated x21 x22 # list) ((aba, None) # list', ah, ba) = false\<close>
proof -
  thm trailt_ref_def
  have [simp]: \<open>(case b of (a, b, c) \<Rightarrow> P a b c) = P (fst b) (fst (snd b)) (snd (snd b))\<close> for P b
    by (cases b) auto
  have [simp]: \<open>(case b of (a, b) \<Rightarrow> P a b) = P (fst b) (snd b)\<close> for P b
    by (cases b) auto
  have [simp]: \<open>(aa = [] \<and> aa = a # list \<and> P) = False\<close> for aa a list P
    by auto

  show \<open>hr_comp trailt_conc trailt_ref  (a # list) ([], ah, ba) = false\<close>
    by (sep_auto simp: hr_comp_def trailt_ref_def eq_commute[of _ \<open>fst _\<close>] ex_assn_pair_split
        simp del: prod.collapse)

  have [simp]: \<open>pair_nat_ann_lit_assn (Decided x1) (aba, Some x2) = false\<close> and
    [simp]: \<open>pair_nat_ann_lit_assn (Propagated x21 x22) (aba, None) = false\<close>
    by (auto simp: nat_ann_lit_rel_def pure_def)
  have [simp]: \<open>(\<exists>\<^sub>Aa aa ab b. f a aa ab b * f' a aa ab b * \<up> (a = h aa ab b \<and> P a aa ab b)) =
      (\<exists>\<^sub>Aaa ab b. f (h aa ab b) aa ab b * f' (h aa ab b) aa ab b * \<up> (P (h aa ab b) aa ab b)) \<close>
    for f f' P h
      by (subst ex_assn_def, subst (2) ex_assn_def, auto)+

  show \<open>hr_comp trailt_conc trailt_ref (Decided x1 # list) ((aba, Some x2) # list', ah, ba) = false\<close>
    by (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>]
        ex_assn_pair_split trailt_ref_def
        simp del: prod.collapse)
  show \<open>hr_comp trailt_conc trailt_ref (Propagated x21 x22 # list) ((aba, None) # list', ah, ba) = false\<close>
    by (sep_auto simp: trail_assn_def hr_comp_def trail_ref_def eq_commute[of _ \<open>fst _\<close>] ex_assn_pair_split
        trailt_ref_def
        simp del: prod.collapse)
qed

lemma is_decided_hd_trail_wll_hnr[unfolded twl_st_assn_def, sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wll_code, RETURN o is_decided_hd_trail_wl) \<in> [\<lambda>(M, _). M \<noteq> []]\<^sub>atwl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
proof -
  have [dest]: \<open>((a, aa, ab, b), x) \<in> trailt_ref \<Longrightarrow> x = a\<close> for a aa ab b x
    by (auto simp: trailt_ref_def)
  show ?thesis
    apply sepref_to_hoare
    unfolding is_decided_hd_trail_wl_def is_decided_wl_code_def is_decided_hd_trail_wll_code_def
    apply (rename_tac S' S)
    apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). fst (fst M)) S\<close>;
           case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd (fst (fst M))) S\<close>;
       case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). M) S'\<close>;
       case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). hd M) S'\<close>)
    by (sep_auto simp: twl_st_assn_def is_decided_hd_trail_wll_code_def is_decided_hd_trail_wl_def
        list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil hr_comp_def null_def trail_assn_Cons_Decided_Some
        pair_nat_ann_lit_assn_Decided_Some pair_nat_ann_lit_assn_Propagated_None trail_assn_Cons_Nil
        trail_assn_Cons_Propagated_None trail_assn_def trail_ref_def
        split: option.splits intro!: return_cons_rule)+
qed


paragraph \<open>Level of a literal\<close>

definition get_level_trail :: \<open>trail_int \<Rightarrow> uint32 \<Rightarrow> nat\<close> where
  \<open>get_level_trail = (\<lambda>((M, xs, lvls, k), _, _) L. lvls! (nat_of_uint32 (L >> 1)))\<close>

sepref_thm get_level_code
  is \<open>uncurry (RETURN oo get_level_trail)\<close>
  :: \<open>[\<lambda>(((M, xs, lvls, k), _, _), L). nat_of_uint32 L div 2 < length lvls]\<^sub>a
  trail_conc\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_trail_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_code
   uses twl_array_code.get_level_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_code_def

lemmas get_level_code_get_level_code[sepref_fr_rules] =
   get_level_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

lemma get_level_code_get_level:
  \<open>(uncurry get_level_code, uncurry (RETURN oo get_level)) \<in>
   [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [simp]: \<open>(ba, bb) \<in> nat_lit_rel \<Longrightarrow> ba div 2 = atm_of bb\<close> for ba bb
    by (auto simp: p2rel_def lit_of_natP_def atm_of_lit_of_nat nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 1: \<open>(uncurry (RETURN oo get_level_trail), uncurry (RETURN oo get_level)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_ref \<times>\<^sub>f unat_lit_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI) (auto simp: image_image trail_ref_def get_level_trail_def
        nat_shiftr_div2 shiftr1_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        nat_of_uint32_shiftr trailt_ref_def)
  thm hfref_compI_PRE_aux[OF get_level_code.refine 1, OF twl_array_code_axioms]
  have H: \<open>(uncurry get_level_code, uncurry (RETURN \<circ>\<circ> get_level))
\<in> [comp_PRE (trail_ref \<times>\<^sub>f unat_lit_rel)
     (\<lambda>(M, L). L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (((M, xs, lvls, k), _, _), L).
         nat_of_uint32 L div 2 < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (trail_conc\<^sup>k *\<^sub>a
                      uint32_assn\<^sup>k)
                     (trail_ref \<times>\<^sub>f
                      unat_lit_rel) \<rightarrow> hr_comp
                 uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_code.refine 1, OF twl_array_code_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_ref_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
      trailt_ref_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: trail_assn_def hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed


paragraph \<open>Level of the state\<close>

lemma count_decided_trail_ref:
  \<open>(RETURN o (\<lambda>((_, _, _, k),_,_). k), RETURN o count_decided) \<in> trail_ref \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trail_ref_def trailt_ref_def)

lemma count_decided_trail:
   \<open>(return o (\<lambda>((_, _, _, k),_,_). k), RETURN o (\<lambda>((_, _, _, k),_,_). k)) \<in> trail_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare sep_auto

lemmas count_decided_trail_code[sepref_fr_rules] =
   count_decided_trail[FCOMP count_decided_trail_ref, unfolded trail_assn_def[symmetric]]


paragraph \<open>Find next decision\<close>

definition find_unwatched'' :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close> where
\<open>find_unwatched'' M N' C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length (N'!C) \<and> (\<forall>j\<in>{2..<i}. -((N'!C)!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M ((N'!C)!j) \<or> (N'!C)!j \<in> lits_of_l M) \<and>
        j < length (N'!C) \<and> j \<ge> 2)) \<and> literals_are_in_N\<^sub>0 (mset (N'!C))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length (N'!C))
    (\<lambda>(_, i). do {
      ASSERT(i < length (N'!C));
      ASSERT((N'!C)!i \<in> snd ` D\<^sub>0);
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
sepref_thm find_unwatched''_code
  is \<open>uncurry2 find_unwatched''\<close>
  :: \<open>[\<lambda>((M, N), C). C < length N]\<^sub>a trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
        option_assn nat_assn\<close>
  unfolding find_unwatched''_def
  unfolding nth_rll_def[symmetric] length_rll_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched''_code
  uses "twl_array_code.find_unwatched''_code.refine_raw"
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_unwatched''_code_def

lemmas find_unwatched''_code_refine = find_unwatched''_code.refine[of N\<^sub>0]



lemma find_unwatched''_code_hnr[sepref_fr_rules]:
  \<open>(uncurry2 find_unwatched''_code, uncurry2 find_unwatched') \<in>
     [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C)) \<and> C < length N]\<^sub>a
     trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
proof -
  have 0: \<open>((None, 2), None, 2) \<in> Id\<close>
    by auto
  have val: \<open>(val, val') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>val = val'\<close> for val val'
    using that by auto
  have 1: \<open>(uncurry2 find_unwatched'', uncurry2 find_unwatched') \<in>
       [\<lambda>((M, N), C). literals_are_in_N\<^sub>0 (mset (N!C))]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
      unfolding find_unwatched''_def find_unwatched'_def uncurry_def
      apply (intro frefI nres_relI)
      apply (refine_vcg 0 val)
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
      subgoal by auto
      done
  show ?thesis
    using find_unwatched''_code.refine[FCOMP 1, OF twl_array_code_axioms] .
qed


paragraph \<open>Bump scores\<close>

definition trail_bump where
  \<open>trail_bump = (\<lambda>(M, vm, \<phi>). do{
      vm' \<leftarrow> vmtf_flush vm;
      RETURN (M, vm', \<phi>)})\<close>

thm trail_dump_code_refine
sepref_thm trail_dump_code
  is trail_bump
  :: \<open>[\<lambda>(M, vm, \<phi>). vm \<in> vmtf_imp (fst M)]\<^sub>a trail_conc\<^sup>d \<rightarrow> trail_conc\<close>
  supply [[goals_limit=1]] trail_dump_code_refine[sepref_fr_rules]
  unfolding trail_bump_def
  by sepref

concrete_definition (in -) trail_dump_code
   uses twl_array_code.trail_dump_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) trail_dump_code_def

lemmas trail_dump_code_refine[sepref_fr_rules] =
   trail_dump_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

lemma trail_bump_rescore:
  \<open>(trail_bump, RETURN o rescore) \<in> trail_ref \<rightarrow>\<^sub>f \<langle>trail_ref\<rangle>nres_rel\<close>
proof -
  have r_id_def: \<open>(RETURN o rescore) y = do {
       _ \<leftarrow>  (RES (vmtf_imp y));
       RETURN y}\<close>
    if \<open>(x, y) \<in> trail_ref\<close>
    for x y
    apply (subst unused_bind_RES_ne)
    using that by (auto simp: rescore_def trail_ref_def)
  show ?thesis
    unfolding trail_bump_def
    apply (intro nres_relI frefI)
    apply clarify
    apply (subst r_id_def)
     apply assumption
    unfolding trail_ref_def
    apply (refine_vcg vmtf_imp_change_removed_order)
    apply clarify
    apply assumption
     apply rule
    apply auto
    done
qed

lemma trail_dump_code_rescore[sepref_fr_rules]:
   \<open>(trail_dump_code, RETURN \<circ> rescore) \<in> trail_assn\<^sup>d \<rightarrow>\<^sub>a trail_assn\<close>
   (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
proof -
  have H: \<open>(trail_dump_code, RETURN \<circ> rescore)
    \<in> [comp_PRE trail_ref (\<lambda>_. True) (\<lambda>_ (M, vm, \<phi>). vm \<in> vmtf_imp (fst M)) (\<lambda>_. True)]\<^sub>a
       hrp_comp (trail_conc\<^sup>d) trail_ref \<rightarrow> hr_comp trail_conc
          trail_ref\<close>
    (is \<open>_ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?im'\<close>)
    using hfref_compI_PRE_aux[OF trail_dump_code_refine trail_bump_rescore] .
  have cond: \<open>?cond' = ?cond\<close>
    by (auto simp: comp_PRE_def trail_ref_def trailt_ref_def intro!: ext)
  have pre: \<open>?pre' = ?pre\<close>
    unfolding trail_assn_def  hrp_comp_dest ..
  have im: \<open>?im' = ?im\<close>
    unfolding trail_assn_def  hrp_comp_dest ..
  show ?thesis
    using H unfolding cond pre im .
qed


paragraph \<open>Rescore conflict clause\<close>

definition rescore_clause :: \<open>'a clause_l \<Rightarrow> (nat, nat) ann_lits \<Rightarrow>  (nat, nat) ann_lits\<close> where
\<open>rescore_clause C M = M\<close>
term trail_ref

definition (in twl_array_code_ops) vmtf_rescore_body :: \<open>nat clause_l \<Rightarrow> vmtf_remove_int \<times> phase_saver  \<Rightarrow> (nat \<times> vmtf_remove_int \<times> phase_saver) nres\<close> where
  \<open>vmtf_rescore_body C = (\<lambda>(vm, \<phi>). do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm, \<phi>). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length \<phi> \<and> atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm, \<phi>). i < length C)
           (\<lambda>(i, vm, \<phi>). do {
               ASSERT(i < length C);
               let vm' = vmtf_dump (atm_of (C!i)) vm;
               let \<phi>' = save_phase_inv (C!i) \<phi>;
               RETURN(i+1, vm', \<phi>')
             })
           (0, vm, \<phi>)
    })\<close>

definition (in twl_array_code_ops) vmtf_rescore :: \<open>nat clause_l \<Rightarrow> trail_int  \<Rightarrow> trail_int nres\<close> where
  \<open>vmtf_rescore C = (\<lambda>(M, vm, \<phi>). do {
      (_, vm, \<phi>) \<leftarrow> vmtf_rescore_body C (vm, \<phi>);
      RETURN (M, vm, \<phi>)
    })\<close>

sepref_thm vmtf_rescore_code
  is \<open>uncurry vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_conc\<^sup>d \<rightarrow>\<^sub>a trail_conc\<close>
  unfolding vmtf_rescore_def vmtf_dump_and_unset_def save_phase_inv_def vmtf_dump_def vmtf_unset_def
  vmtf_rescore_body_def
  supply [[goals_limit = 1]] is_None_def[simp] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_code
   uses twl_array_code.vmtf_rescore_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_code_def

lemmas vmtf_rescore_code_refine[sepref_fr_rules] =
   vmtf_rescore_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma vmtf_rescore_score_clause:
  \<open>(uncurry vmtf_rescore, uncurry (RETURN oo rescore_clause)) \<in>
     [\<lambda>(C, M). literals_are_in_N\<^sub>0 (mset C)]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>r trail_ref) \<rightarrow> \<langle>trail_ref\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body C (vm, \<phi>) \<le> RES {(i, vm, \<phi>). ((M, vm, \<phi>), M') \<in> trail_ref}\<close>
    if M: \<open>((M, vm, \<phi>), M') \<in> trail_ref\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of N\<^sub>1\<close>
    for C vm \<phi> M M'
    unfolding vmtf_rescore_body_def vmtf_dump_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm, \<phi>). ((M, vm, \<phi>), M') \<in> trail_ref\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using M C by (auto simp: trail_ref_def vmtf_imp_def phase_saving_def)
    subgoal using M by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding save_phase_inv_def by auto
    subgoal using C unfolding trail_ref_def phase_saving_def save_phase_inv_def
      by (auto simp: vmtf_imp_append_remove_iff)
    subgoal by simp
    done
  have K: \<open>((a, b),(a', b')) \<in> A \<times>\<^sub>f B \<longleftrightarrow> (a, a') \<in> A \<and> (b, b') \<in> B\<close> for a b a' b' A B
    by auto
  show ?thesis
    unfolding vmtf_rescore_def rescore_clause_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule bind_refine_spec)
     prefer 2
     apply (subst (asm) K)
     apply (rule H)
      apply clarify
      apply assumption
    subgoal apply auto
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_N\<^sub>0_def)
    subgoal by auto
    done
qed

lemma vmtf_rescore_code_rescore_clause[sepref_fr_rules]:
  \<open>(uncurry vmtf_rescore_code, uncurry (RETURN \<circ>\<circ> rescore_clause))
     \<in> [\<lambda>(a, b). literals_are_in_N\<^sub>0 (mset a)]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
  using vmtf_rescore_code.refine[FCOMP vmtf_rescore_score_clause, OF twl_array_code_axioms]
  unfolding trail_assn_def
  by auto


subsubsection \<open>Transitions\<close>

(*TODO Move*)
definition (in -) conflict_assn_is_None :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>conflict_assn_is_None = (\<lambda>(b, _, _). b)\<close>

lemma conflict_assn_is_None_is_None: \<open>(RETURN o conflict_assn_is_None, RETURN o is_None) \<in>
  option_conflict_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_conflict_rel_def conflict_assn_is_None_def split: option.splits)

lemma conflict_assn_is_None_conflict_assn_is_None:
 \<open>(return o conflict_assn_is_None, RETURN o conflict_assn_is_None) \<in>
  (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn))\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: conflict_assn_is_None_def)

lemma conflict_assn_is_None_is_none_Code[sepref_fr_rules]:
  \<open>(return \<circ> conflict_assn_is_None, RETURN \<circ> is_None) \<in> conflict_option_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using conflict_assn_is_None_conflict_assn_is_None[FCOMP conflict_assn_is_None_is_None,
  unfolded conflict_option_assn_def[symmetric]] .

definition (in -) conflict_assn_is_empty :: \<open>_ \<Rightarrow> bool\<close> where
  \<open>conflict_assn_is_empty = (\<lambda>(_, n, _). n = 0)\<close>

lemma conflict_assn_is_empty_is_empty: \<open>(RETURN o conflict_assn_is_empty, RETURN o (\<lambda>D. Multiset.is_empty(the D))) \<in>
  [\<lambda>D. D \<noteq> None]\<^sub>f
  option_conflict_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
   (auto simp: option_conflict_rel_def conflict_assn_is_empty_def conflict_rel_def Multiset.is_empty_def
      split: option.splits)

lemma conflict_assn_is_empty_conflict_assn_is_empty:
 \<open>(return o conflict_assn_is_empty, RETURN o conflict_assn_is_empty) \<in>
  (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn))\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_is_empty_def uint32_nat_rel_def br_def nat_of_uint32_0_iff)

lemma conflict_assn_is_empty_is_empty_code[sepref_fr_rules]:
  \<open>(return \<circ> conflict_assn_is_empty, RETURN \<circ> the_is_empty) \<in>
      [\<lambda>D. D \<noteq> None]\<^sub>a conflict_option_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using conflict_assn_is_empty_conflict_assn_is_empty[FCOMP conflict_assn_is_empty_is_empty,
  unfolded conflict_option_assn_def[symmetric]] unfolding the_is_empty_def
  by simp
(*End MOVE*)

sepref_register unit_propagation_inner_loop_wl_loop_D
sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def length_ll_def[symmetric] PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric]
  unfolding nth_ll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding twl_st_assn_def swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def
lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]


paragraph \<open>Unit propagation, inner loop\<close>

sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_inner_loop_wl_D_def twl_st_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]


lemma literals_to_update_wll_empty_hnr[unfolded twl_st_assn_def, sepref_fr_rules]:
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W). is_Nil Q), RETURN o literals_to_update_wl_empty) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) S'\<close>)
  by (sep_auto simp: twl_st_assn_def literals_to_update_wll_empty_def literals_to_update_wl_empty_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil
      split: list.splits)+

concrete_definition (in -) literals_to_update_wll_empty'
   uses twl_array_code.literals_to_update_wll_empty_hnr
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wll_empty'_def

lemmas literals_to_update_wll_empty'_code[sepref_fr_rules] =
   literals_to_update_wll_empty'.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

lemma hd_select_and_remove_from_literals_to_update_wl''_refine:
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q)),
       select_and_remove_from_literals_to_update_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>a
    twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *assn unat_lit_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  let ?int = \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W).  ((M, N, U, D, NP, UP, tl Q, W), hd Q))\<close>
  define twl_st_l_interm_rel_1 :: \<open>(_ \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_l_interm_rel_1 \<equiv> Id \<times>\<^sub>r \<langle>\<langle>Id\<rangle> list_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r
     \<langle>Id\<rangle>option_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r list_mset_rel \<times>\<^sub>r Id\<close>
  have 1:
    \<open>(RETURN o ?int,
       select_and_remove_from_literals_to_update_wl :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal) nres) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#}]\<^sub>f
    twl_st_l_interm_rel_1 \<rightarrow> \<langle>twl_st_l_interm_rel_1 \<times>\<^sub>r Id\<rangle>nres_rel\<close>
    unfolding fref_def
    apply clarify
    apply (rename_tac a aa ab ac ad ae af b ag ah ai aj ak al am ba)
    apply (case_tac af)
     apply (auto simp: fref_def nres_rel_def twl_st_l_interm_rel_1_def
        select_and_remove_from_literals_to_update_wl_def RETURN_RES_refine_iff list_mset_rel_def br_def)
    done
  define twl_st_l_interm_assn_2 :: \<open>_ \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
    \<open>twl_st_l_interm_assn_2 \<equiv>
       (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
       conflict_option_assn *assn
       unit_lits_assn *assn
       unit_lits_assn *assn
       list_assn unat_lit_assn *assn
       array_watched_assn
      )\<close>
  have 2:
    \<open>(return o (\<lambda>(M, N, U, D, NP, UP, Q, W). ((M, N, U, D, NP, UP, tl Q, W), hd Q)), RETURN o ?int) \<in>
    [\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> []]\<^sub>a
    twl_st_l_interm_assn_2\<^sup>d \<rightarrow> twl_st_l_interm_assn_2 *assn unat_lit_assn\<close>
    unfolding twl_st_l_interm_assn_2_def
    apply sepref_to_hoare
    by (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) x\<close>;
        case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). Q) xi\<close>) sep_auto+
  have H: \<open>(return \<circ> (\<lambda>(M, N, U, D, NP, UP, Q, W). ((M, N, U, D, NP, UP, tl Q, W), hd Q)),
             select_and_remove_from_literals_to_update_wl)
            \<in> [comp_PRE twl_st_l_interm_rel_1
                 (\<lambda>(_, _, _, _, _, _, Q, _). Q \<noteq> {#})
                 (\<lambda>_ (_, _, _, _, _, _, Q, _). Q \<noteq> [])
                 (\<lambda>_. True)]\<^sub>a
              hrp_comp (twl_st_l_interm_assn_2\<^sup>d) twl_st_l_interm_rel_1 \<rightarrow>
              hr_comp (twl_st_l_interm_assn_2 *assn unat_lit_assn) (twl_st_l_interm_rel_1 \<times>\<^sub>r Id)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF 2 1] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def twl_st_l_interm_rel_1_def in_br_conv list_mset_rel_def
        literals_to_update_wl_empty_def)

  have im: \<open>?im' = ?im\<close>
    unfolding twl_st_l_interm_assn_2_def twl_st_l_interm_rel_1_def prod_hrp_comp
    by (auto simp: prod_hrp_comp hrp_comp_def list_assn_list_mset_rel_eq_list_mset_assn
        twl_st_assn_def hr_comp_invalid)

 have post: \<open>?f' = ?f\<close>
   by (auto simp: comp_PRE_def twl_st_l_interm_assn_2_def
       twl_st_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       twl_st_l_interm_rel_1_def)
  show ?thesis using H unfolding pre post im .
qed

concrete_definition (in -) hd_select_and_remove_from_literals_to_update_wl''
   uses twl_array_code.hd_select_and_remove_from_literals_to_update_wl''_refine
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) hd_select_and_remove_from_literals_to_update_wl''_def

lemmas [sepref_fr_rules] =
   hd_select_and_remove_from_literals_to_update_wl''.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]


paragraph \<open>Unit propagation, outer loop\<close>

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def twl_st_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D_code
   uses twl_array_code.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_code_def

lemmas unit_propagation_outer_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]


paragraph \<open>Skip and resolve\<close>

sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil)\<close>
  :: \<open>twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_def twl_st_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses twl_array_code.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of N\<^sub>0, unfolded twl_st_assn_def,
    FCOMP get_conflict_wll_is_Nil_get_conflict_wl_is_Nil]

lemma get_conflict_wll_is_Nil_hnr[unfolded twl_st_assn_def, sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN o get_conflict_wl_is_Nil) \<in>
     twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac S' S)
  apply (case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S\<close>;
      case_tac \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). D) S'\<close>)
  by (sep_auto simp: twl_st_assn_def get_conflict_wl_is_Nil_def get_conflict_wll_is_Nil_def
      Multiset.is_empty_def Nil_list_mset_rel_iff empty_list_mset_rel_iff
      get_conflict_wll_is_Nil_code_def
      list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil arl_assn_def hr_comp_def null_def)+

declare get_level_code_get_level[sepref_fr_rules]

lemma in_literals_are_in_N\<^sub>0_in_D\<^sub>0:
  assumes \<open>literals_are_in_N\<^sub>0 D\<close> and \<open>L \<in># D\<close>
  shows \<open>L \<in> snd ` D\<^sub>0\<close>
  using assms by (cases L) (auto simp: image_image literals_are_in_N\<^sub>0_def all_lits_of_m_def)

sepref_thm maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo maximum_level_remove)\<close>
  :: \<open>[\<lambda>((M, D), L). literals_are_in_N\<^sub>0 (mset D)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding maximum_level_remove_def[abs_def]
  supply in_literals_are_in_N\<^sub>0_in_D\<^sub>0[intro]
  supply uint32_nat_assn_zero_uint32[sepref_fr_rules]
  supply [[goals_limit = 1]]
  apply (rewrite in "(False, \<hole>)" zero_uint32_def[symmetric])
  apply (rewrite in "[\<hole>..<_]" annotate_assn[where A=nat_assn])
  by sepref

concrete_definition (in -) maximum_level_remove_code
   uses twl_array_code.maximum_level_remove_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms maximum_level_remove_code_def

lemmas select_and_remove_from_literals_to_update_wl''_code_[sepref_fr_rules] =
   maximum_level_remove_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

lemma maximum_level_remove_code_get_maximum_level_remove[sepref_fr_rules]:
  \<open>(uncurry2 maximum_level_remove_code,
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    [\<lambda>((M, D), L). literals_are_in_N\<^sub>0 D]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have 1:
  \<open>(uncurry2 (RETURN ooo maximum_level_remove),
     uncurry2 (RETURN ooo get_maximum_level_remove)) \<in>
    ((Id \<times>\<^sub>r list_mset_rel) \<times>\<^sub>r Id) \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    by (auto intro!: nres_relI frefI simp: list_mset_rel_def br_def maximum_level_remove
        get_maximum_level_remove_def)
  have H: \<open>(uncurry2 maximum_level_remove_code,
   uncurry2 (RETURN \<circ>\<circ>\<circ> get_maximum_level_remove))
  \<in> [comp_PRE (Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id) (\<lambda>_. True) (\<lambda>_ ((M, D), L). literals_are_in_N\<^sub>0 (mset D))
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k) (Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id) \<rightarrow>
        hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux [OF maximum_level_remove_code.refine 1, OF twl_array_code_axioms] .
  have 1: \<open>?pre' = ?pre\<close> \<comment> \<open>TODO tune proof\<close>
    apply (auto simp: comp_PRE_def
        list_mset_rel_def br_def
        simp del: literal_of_nat.simps intro!: ext)
    by (metis mset_sorted_list_of_multiset)

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

sepref_register skip_and_resolve_loop_wl_D
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>If _ \<hole> _\<close> op_mset_arl_empty_def[symmetric])
  apply (rewrite in \<open>let _ = _ \<union># _ in RETURN(_ = {#}, tl _, _)\<close> tl_dump_def[symmetric])
  unfolding twl_st_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps get_conflict_wl_get_conflict_wl_is_Nil
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    maximum_level_remove[symmetric]
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
  by sepref

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
   uses twl_array_code.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]


paragraph \<open>Backjumping\<close>

sepref_thm find_lit_of_max_level_wl_imp_code
  is \<open>uncurry8 find_lit_of_max_level_wl_imp'\<close>
  :: \<open>[\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L). literals_are_in_N\<^sub>0 (mset D)]\<^sub>a
       (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a
          unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding find_lit_of_max_level_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_lit_of_max_level_wl_imp'_def
  supply in_literals_are_in_N\<^sub>0_in_D\<^sub>0[intro]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) find_lit_of_max_level_wl_imp_code
   uses twl_array_code.find_lit_of_max_level_wl_imp_code.refine_raw
   is \<open>(uncurry8 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_lit_of_max_level_wl_imp_code_def

lemmas find_lit_of_max_level_wl_imp_code[sepref_fr_rules] =
   find_lit_of_max_level_wl_imp_code.refine[of N\<^sub>0, OF twl_array_code_axioms]


lemma find_lit_of_max_level_wl_imp_code_find_lit_of_max_level_wl'[sepref_fr_rules]:
  \<open>(uncurry8 find_lit_of_max_level_wl_imp_code, uncurry8 find_lit_of_max_level_wl') \<in>
   [\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L). distinct_mset D \<and>
     (\<exists>K\<in>#remove1_mset (-L) D. get_level M K = get_maximum_level M (remove1_mset (- L) D)) \<and>
     literals_are_in_N\<^sub>0 D]\<^sub>a
   (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k
    \<rightarrow> unat_lit_assn\<close>
    (is \<open>_ \<in> [?P]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have \<open>K \<in># remove1_mset (-L) (mset D) \<Longrightarrow> distinct D \<Longrightarrow>
    get_level M K = get_maximum_level M (remove1_mset (- L) (mset D)) \<Longrightarrow>
    find_lit_of_max_level_wl_imp M D L
    \<le> find_lit_of_max_level_wl' M N U (mset D) NP UP Q W L\<close>
    for D' :: \<open>nat clause\<close> and K :: \<open>nat literal\<close> and M :: \<open>(nat, nat) ann_lits\<close> and L and
    D :: \<open>nat clause_l\<close> and N and U :: nat and NP UP and Q and W
    unfolding find_lit_of_max_level_wl_imp_def maximum_level_remove find_lit_of_max_level_wl'_def
        find_lit_of_max_level_wl_def
    apply (refine_vcg WHILEIT_rule[where R =\<open>measure (\<lambda>i. Suc (length D) - i)\<close>])
    subgoal by auto
    subgoal by (auto simp: list_mset_rel_def br_def)
    subgoal by auto
    subgoal apply (auto simp add: list_mset_rel_def br_def in_set_conv_nth distinct_mset_remove1_All
          dest!: in_diffD)
      by (metis Suc_lessI less_SucE)+
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def less_Suc_eq)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def distinct_mset_remove1_All
intro!: in_remove1_msetI)
    subgoal by (auto simp add: not_less_eq list_mset_rel_def br_def distinct_mset_remove1_All)
    done
  then have 1: \<open>(uncurry8 find_lit_of_max_level_wl_imp',
    uncurry8 find_lit_of_max_level_wl') \<in>
     [?P]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    unfolding find_lit_of_max_level_wl_imp'_def
    by (intro frefI nres_relI) (auto simp add: uncurry_def list_mset_rel_def br_def)
  have H: \<open>(uncurry8 find_lit_of_max_level_wl_imp_code, uncurry8 find_lit_of_max_level_wl')
    \<in> [comp_PRE
       (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id)
       (\<lambda>((((((((M, N), U), D), NP), UP), WS), Q), L).
           distinct_mset D \<and>
           (\<exists>K\<in>#remove1_mset (- L) D.
               get_level M K = get_maximum_level M (remove1_mset (- L) D)) \<and>
           literals_are_in_N\<^sub>0 D)
       (\<lambda>_ ((((((((M, N), U), D), NP), UP), WS), Q), L).
           literals_are_in_N\<^sub>0 (mset D))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
                        (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a
                        clauses_l_assn\<^sup>k *\<^sub>a
                        clauses_l_assn\<^sup>k *\<^sub>a
                        clause_l_assn\<^sup>k *\<^sub>a
                        (hr_comp (arrayO_assn (arl_assn nat_assn))
                          (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k *\<^sub>a
                        unat_lit_assn\<^sup>k)
                       (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f list_mset_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f
                        Id \<times>\<^sub>f
                        Id \<times>\<^sub>f
                        Id) \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux [OF find_lit_of_max_level_wl_imp_code.refine 1, OF twl_array_code_axioms] .
  have 1: \<open>?pre' = ?P\<close>
    by (auto simp: comp_PRE_def list_mset_rel_def br_def simp del: literal_of_nat.simps intro!: ext)
  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp by (auto simp: hrp_comp_def hr_comp_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry2 find_decomp_wl_imp\<close>
  :: \<open>[\<lambda>((M, D), L). M \<noteq> [] \<and> literals_are_in_N\<^sub>0 D]\<^sub>a
         trail_assn\<^sup>d *\<^sub>a conflict_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k
    \<rightarrow> trail_assn\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
  supply [[goals_limit=1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses twl_array_code.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of N\<^sub>0, OF twl_array_code_axioms]

lemma hd_decided_count_decided_ge_1: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry8 (PR_CONST find_decomp_wl_imp')\<close>
  :: \<open>[\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). D \<noteq> {#} \<and> M \<noteq> [] \<and> literals_are_in_N\<^sub>0 D]\<^sub>a
      (trail_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
         unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
      unat_lit_assn\<^sup>k \<rightarrow> trail_assn\<close>
  unfolding find_decomp_wl_imp'_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses twl_array_code.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry8 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def
thm find_decomp_wl_imp'_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
    unfolded twl_st_assn_def]


lemma find_decomp_wl_code[sepref_fr_rules]:
  \<open>(uncurry8 find_decomp_wl_imp'_code,
      uncurry8 find_decomp_wl')
  \<in> [\<lambda>((((((((M::(nat, nat) ann_lits, N), U::nat), D::nat clause), NP::nat clauses), UP:: nat clauses),
        Q), W), L). \<exists>D\<^sub>0. D \<noteq> {#} \<and> M \<noteq> [] \<and> ex_decomp_of_max_lvl M (Some D) L \<and> L = lit_of (hd M) \<and>
       (twl_struct_invs (twl_st_of_wl None (M, N, U, D\<^sub>0, NP, UP, Q, W)) \<and>
       literals_are_in_N\<^sub>0 D \<and> D \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None)]\<^sub>a
    (trail_assn\<^sup>d *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
       unit_lits_assn\<^sup>k *\<^sub>a unit_lits_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k) *\<^sub>a
    unat_lit_assn\<^sup>k
    \<rightarrow> trail_assn\<close>
  (is \<open> _ \<in> [?P]\<^sub>a _ \<rightarrow> _\<close>)
proof -
  have H: \<open>(uncurry8 find_decomp_wl_imp'_code, uncurry8 find_decomp_wl')
    \<in> [\<lambda>((((((((a, b), ba), bb), bc), bd), be), bf), bg).
        bb \<noteq> {#} \<and>
        a \<noteq> []\<and>
        ex_decomp_of_max_lvl a (Some bb) bg \<and>
        bg = lit_of (hd a) \<and>
        (\<exists>D\<^sub>0. twl_struct_invs
                (convert_lits_l b a,
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (take ba (tl b))#},
                 {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x))
                 . x \<in># mset (drop (Suc ba) b)#},
                 D\<^sub>0, bc, bd, {#}, be) \<and>
               bb \<subseteq># the D\<^sub>0 \<and> (\<exists>y. D\<^sub>0 = Some y)) \<and>
        literals_are_in_N\<^sub>0
         bb]\<^sub>a
     (trail_assn)\<^sup>d *\<^sub>a (arlO_assn clause_ll_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>k *\<^sub>a
        clauses_l_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a
     (hr_comp (arrayO_assn (arl_assn nat_assn))
         (\<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset N\<^sub>1)))\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
     trail_assn\<close>
    (is \<open> _ \<in> [?Q]\<^sub>a _ \<rightarrow> _\<close>)
    using find_decomp_wl_imp'_code.refine[unfolded find_decomp_wl_imp'_def PR_CONST_def, FCOMP
        find_decomp_wl_imp_find_decomp_wl'[unfolded find_decomp_wl_imp'_def], OF twl_array_code_axioms]
      .

  have QP: \<open>?Q = ?P\<close>
    by (auto intro!: ext)
  show ?thesis
    using H unfolding QP .
qed

definition (in -) extract_shorter_conflict_l_trivial :: \<open>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>_ \<Rightarrow>
'v clause nres\<close> where
\<open>extract_shorter_conflict_l_trivial M N U D NP UP W Q \<equiv> SPEC(op = (filter_mset (\<lambda>L. get_level M L > 0) (the D)))\<close>

definition extract_shorter_conflict_list where
\<open>extract_shorter_conflict_list M N U D NP UP W Q == do {
   let D = the D;
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, D'). i \<le> length D \<and> mset D' = filter_mset (\<lambda>L. get_level M L > 0) (mset (take i D))\<^esup>
     (\<lambda>(i, _). i < length D)
     (\<lambda>(i, D'). do {
          ASSERT(i < length D);
          ASSERT(D!i \<in> snd ` D\<^sub>0);
          if get_level M (D!i) > 0 then RETURN (i+1, D' @ [D!i]) else RETURN (i+1, D')
        })
     (0, []);
    RETURN (snd S)
  }\<close>

lemma extract_shorter_conflict_list_SPEC:
  assumes N\<^sub>0: \<open>literals_are_in_N\<^sub>0 (mset (the D))\<close>
  shows \<open>extract_shorter_conflict_list M N U D NP UP W Q \<le> \<Down> Id
    (SPEC (\<lambda>D'. mset D' = filter_mset (\<lambda>L. get_level M L > 0) (mset (the D))))\<close>
proof -
  have take_Suc: \<open>take (Suc n) xs = take n xs @ [xs ! n]\<close> if \<open>n < length xs\<close> for n xs
    using that unfolding take_map_nth_alt_def by auto
  show ?thesis
    unfolding extract_shorter_conflict_l_trivial_def extract_shorter_conflict_list_def
    Let_def
    apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(i, _). Suc (length (the D)) - i)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using N\<^sub>0  by (auto simp: image_image literals_are_in_N\<^sub>0_def literals_are_in_N\<^sub>0_in_N\<^sub>1)
    subgoal by auto
    subgoal by (auto simp: nths_upt_Suc' take_Suc)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: nths_upt_Suc' take_Suc)
    subgoal by auto
    subgoal for s
      by (cases \<open>fst s < length (the D)\<close>) auto
    done
qed


abbreviation (in -) uncurry_swap3 where
\<open>uncurry_swap3 f \<equiv> \<lambda> ((a, b), c). f (a, b, c)\<close>

abbreviation (in -) uncurried_swap8 where
\<open>uncurried_swap8 f \<equiv> \<lambda> (((((((M, N), U), D), NP), UP), Q), W). f (M, N, U, D, NP, UP, Q, W)\<close>

lemma (in -) op_list_append_alt_def:
  \<open>op_list_append xs x = xs @ [x]\<close>
  by (auto simp: op_list_append_def)

(*TODO: Instead of nat, use uint32*)
abbreviation extract_shorter_conflict_l_trivial_pre where
\<open>extract_shorter_conflict_l_trivial_pre \<equiv> \<lambda>(((((((M, N), U), D), NP), UP), W), Q).
    D \<noteq> None \<and> literals_are_in_N\<^sub>0 (mset (the D))\<close>
sepref_register extract_shorter_conflict_l_trivial
sepref_thm extract_shorter_conflict_l_trivial'
  is \<open>uncurry7 (PR_CONST extract_shorter_conflict_list)\<close>
  :: \<open>[extract_shorter_conflict_l_trivial_pre]\<^sub>a
   trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
        *\<^sub>a (option_assn (arl_assn unat_lit_assn))\<^sup>d *\<^sub>a unit_lits_assn\<^sup>k
        *\<^sub>a unit_lits_assn\<^sup>k
        *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k \<rightarrow> arl_assn unat_lit_assn\<close>
  supply [[goals_limit = 1]]
  supply le_nat_uint32_hnr[sepref_fr_rules]
  unfolding extract_shorter_conflict_list_def PR_CONST_def twl_st_assn_def
  op_list_append_alt_def[symmetric]
  apply (rewrite in "(_, \<hole>)" arl.fold_custom_empty)
  by sepref

concrete_definition (in -) extract_shorter_conflict_l_trivial_code
   uses twl_array_code.extract_shorter_conflict_l_trivial'.refine_raw
   is \<open>(uncurry7 ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_def

lemmas extract_shorter_conflict_l_trivial_code_wl_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code.refine[of N\<^sub>0,
      OF twl_array_code_axioms]

definition (in -) extract_shorter_conflict_wl' where
\<open>extract_shorter_conflict_wl' M N U D NP UP W Q =
  extract_shorter_conflict_wl (M, N, U, D, NP, UP, W, Q)\<close>

lemma extract_shorter_conflict_l_trivial_code_wl':
  \<open>(uncurry7 extract_shorter_conflict_l_trivial_code, uncurry7 (PR_CONST extract_shorter_conflict_wl'))
    \<in> [\<lambda>(((((((M, N), U), D), NP), UP), Q), W).
         twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
         twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
         get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None \<and>
         - lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)))
            \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W)) \<and>
         no_skip (M, N, U, D, NP, UP, Q, W) \<and>
         no_resolve (M, N, U, D, NP, UP, Q, W) \<and>
         literals_are_in_N\<^sub>0 (the D)]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
      *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a unit_lits_assn\<^sup>k
      *\<^sub>a unit_lits_assn\<^sup>k
      *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a array_watched_assn\<^sup>k \<rightarrow>
      conflict_assn\<close>
    (is \<open> _ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?post\<close>)
proof -
   have H: \<open>uncurry7 extract_shorter_conflict_l_trivial x <= \<Down> Id
       (uncurry7 extract_shorter_conflict_wl' y)\<close>
    if
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))\<close>
         (is \<open>twl_struct_invs ?S\<close>) and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))\<close> and
      L: \<open>-lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W))) \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W))\<close> and
      D: \<open>get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None\<close> \<open>get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> Some {#}\<close>
          (is \<open>get_conflict_wl ?T ~= _\<close>) and
      n_s_s: \<open>no_skip (M, N, U, D, NP, UP, Q, W)\<close> and
      n_s_r: \<open>no_resolve (M, N, U, D, NP, UP, Q, W)\<close> and
      \<open>x = (((((((M, N), U), D), NP), UP), Q), W)\<close> and
      \<open>y = (((((((M, N), U), D), NP), UP), Q), W)\<close>
  for N NP UP D L M U Q W x y
  proof -
    have
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of ?S)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?S)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl D unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    then have M_nempty: \<open>M ~= []\<close>
      using D by auto
    have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) \<Turnstile>p the D\<close>
      using that(2-) learned
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of ?S) \<Turnstile>pm
        filter_mset (\<lambda>L. get_level (trail (state\<^sub>W_of ?S)) L > 0) (the (conflicting (state\<^sub>W_of ?S)))\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(1))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using M_nempty by (cases M, auto simp: cdcl\<^sub>W_restart_mset_state)
      done
    moreover have \<open>- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of ?S)) \<in>#
      {#L \<in># the (conflicting (state\<^sub>W_of ?S)). 0 < get_level (trail (state\<^sub>W_of ?S)) L#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using D by (auto simp: cdcl\<^sub>W_restart_mset_state)
      subgoal using M_nempty by (cases M, auto simp: cdcl\<^sub>W_restart_mset_state)
      done
    moreover have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) =
          mset ` set (tl N) \<union> set_mset NP \<union> set_mset UP\<close>
          apply (subst (2) append_take_drop_id[of U \<open>tl N\<close>, symmetric])
          unfolding set_append drop_Suc
          by auto
    ultimately show ?thesis
      using that(2-) D M_nempty
      by (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset'
        extract_shorter_conflict_l_trivial_def extract_shorter_conflict_wl_def
        extract_shorter_conflict_wl'_def)
  qed
  have R': \<open>(uncurry7 extract_shorter_conflict_list, uncurry7 extract_shorter_conflict_l_trivial) \<in>
     [\<lambda>(((((((M, N), U), D), NP), UP), Q), W). literals_are_in_N\<^sub>0 (the D) \<and> D ~= None]\<^sub>f
        Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f \<langle>list_mset_rel\<rangle>option_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow>
        \<langle>list_mset_rel\<rangle>nres_rel\<close>
    unfolding extract_shorter_conflict_l_trivial_def
    apply (intro frefI nres_relI)
    apply clarsimp
    apply (rule order.trans)
    apply (rule extract_shorter_conflict_list_SPEC)
    apply (auto simp: conc_fun_RES option_rel_def list_mset_rel_def br_def)
    done
  have R: \<open>(uncurry7 extract_shorter_conflict_l_trivial, uncurry7 extract_shorter_conflict_wl') \<in>
     [?cond]\<^sub>f
      (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    apply (intro nres_relI frefI)
    apply clarify
    apply (rule H)
    apply assumption+
    apply auto
    done
  have H0: \<open>(uncurry7 extract_shorter_conflict_l_trivial_code,
     uncurry7 extract_shorter_conflict_l_trivial)
    \<in> [comp_PRE
        (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>list_mset_rel\<rangle>option_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id)
        (\<lambda>(((((((M, N), U), D), NP), UP), Q), W). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None)
        (\<lambda>_ (((((((M, N), U), D), NP), UP), W), Q).
            D \<noteq> None \<and> literals_are_in_N\<^sub>0 (mset (the D))) (\<lambda>_. True)]\<^sub>a
      hrp_comp (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
                  (option_assn (arl_assn unat_lit_assn))\<^sup>d *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a
                  clauses_l_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a
                  (hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k)
          (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>list_mset_rel\<rangle>option_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
      conflict_assn\<close>
      (is \<open> _ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?post'\<close>)
      using hfref_compI_PRE_aux[OF extract_shorter_conflict_l_trivial_code.refine,
      OF twl_array_code_axioms, unfolded PR_CONST_def, OF R' ] .
    have cond: \<open>?cond' = (\<lambda>(((((((M, N), U), D), NP), UP), Q), W). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None)\<close>
      by (auto simp: comp_PRE_def option_rel_def list_mset_rel_def br_def
       intro!: ext)
  have pre: \<open>?pre' =
      (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
      (conflict_option_assn)\<^sup>d *\<^sub>a
      clauses_l_assn\<^sup>k *\<^sub>a
      clauses_l_assn\<^sup>k *\<^sub>a
      clause_l_assn\<^sup>k *\<^sub>a
      (hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k)\<close>
    unfolding prod_hrp_comp twl_st_assn_def hr_comp_invalid
    by (auto simp: hrp_comp_def hr_comp_def hr_comp_invalid)
  have im: \<open>?post' = ?post\<close>
    by (auto simp: hrp_comp_def hr_comp_def)

  have H0': \<open>(uncurry7 extract_shorter_conflict_l_trivial_code,
     uncurry7 extract_shorter_conflict_l_trivial)
    \<in> [(\<lambda>(((((((M, N), U), D), NP), UP), Q), W). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None)]\<^sub>a
      (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
      (conflict_option_assn)\<^sup>d *\<^sub>a
      clauses_l_assn\<^sup>k *\<^sub>a
      clauses_l_assn\<^sup>k *\<^sub>a
      clause_l_assn\<^sup>k *\<^sub>a
      (hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k) \<rightarrow>
      conflict_assn\<close>
       using H0 unfolding pre cond .
  have H: \<open>(uncurry7 extract_shorter_conflict_l_trivial_code, uncurry7 extract_shorter_conflict_wl')
    \<in> [comp_PRE (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id)
        (\<lambda>(((((((M, N), U), D), NP), UP), Q), W).
            twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
            twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
            get_conflict_wl (M, N, U, D, NP, UP, Q, W) \<noteq> None \<and>
            - lit_of (hd (get_trail_wl (M, N, U, D, NP, UP, Q, W)))
            \<in># the (get_conflict_wl (M, N, U, D, NP, UP, Q, W)) \<and>
            no_skip (M, N, U, D, NP, UP, Q, W) \<and>
            no_resolve (M, N, U, D, NP, UP, Q, W) \<and>
            literals_are_in_N\<^sub>0 (the D))
        (\<lambda>_ (((((((M, N), U), D), NP), UP), Q), W). literals_are_in_N\<^sub>0 (the D) \<and> D \<noteq> None) (\<lambda>_. True)]\<^sub>a
      hrp_comp (trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a
                  clauses_l_assn\<^sup>k *\<^sub>a clauses_l_assn\<^sup>k *\<^sub>a clause_l_assn\<^sup>k *\<^sub>a
                  (hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>k)
          (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow>
      hr_comp conflict_assn Id\<close>
      (is \<open> _ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?post'\<close>)
      using hfref_compI_PRE_aux[OF H0' R ] .
  have cond: \<open>?cond' = ?cond\<close>
    unfolding comp_PRE_def by (auto intro!: ext)
  have pre: \<open>?pre' = ?pre\<close>
    unfolding prod_hrp_comp twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have im: \<open>?post' = ?post\<close>
    by (auto simp: hrp_comp_def hr_comp_def)
   show ?thesis
    unfolding PR_CONST_def
     using H unfolding cond pre im .
qed

concrete_definition (in -) extract_shorter_conflict_l_trivial_code_wl'
   uses twl_array_code.extract_shorter_conflict_l_trivial_code_wl'
   is \<open>(uncurry7 ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_wl'_def

sepref_register extract_shorter_conflict_wl'

thm extract_shorter_conflict_l_trivial_code_wl'.refine[of N\<^sub>0,
      OF twl_array_code_axioms]
lemmas extract_shorter_conflict_l_trivial_code_wl'_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code_wl'.refine[of N\<^sub>0, unfolded PR_CONST_def,
      OF twl_array_code_axioms]


lemma backtrack_wl_D_alt_def:
  \<open>backtrack_wl_D S\<^sub>0 =
   do {
      let (M, N, U, D, NP, UP, Q, W) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(no_step cdcl\<^sub>W_restart_mset.resolve (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W))));
        ASSERT(D ~= None);
        ASSERT(literals_are_in_N\<^sub>0 (the D));
        ASSERT(-L \<in># the D);
        D' \<leftarrow> extract_shorter_conflict_wl (M, N, U, D, NP, UP, Q, W);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D' \<noteq> {#});
        ASSERT(ex_decomp_of_max_lvl M (Some D') L);
        ASSERT(D' \<subseteq># the D);
        ASSERT(-L \<in># D');
        ASSERT(literals_are_in_N\<^sub>0 D');
        ASSERT(\<forall>L\<in># D'. defined_lit M L);
        M1 \<leftarrow> find_decomp_wl (M, N, U, Some D', NP, UP, Q, W) L;

        if size D' > 1
        then do {
          ASSERT(\<forall>L' \<in># D' - {#-L#}. get_level M L' = get_level M1 L');
          ASSERT(\<exists>L' \<in># D' - {#-L#}. get_level M L' = get_maximum_level M (D' - {#-L#}));
          ASSERT(\<exists>L' \<in># D' - {#-L#}. get_level M1 L' = get_maximum_level M1 (D' - {#-L#}));
          ASSERT(get_level M L > get_maximum_level M (D' - {#-L#}));
          ASSERT(distinct_mset D');
          L' \<leftarrow> find_lit_of_max_level_wl' M1 N U D' NP UP Q W L;
          ASSERT(L \<noteq> -L');
          ASSERT(-L \<in># D');
          ASSERT(L' \<in># D');
          let K = -L;
          D' \<leftarrow> list_of_mset2 K L' D';
          ASSERT(atm_of L \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(atm_of L' \<in> atms_of_mm (mset `# mset (tl N) + NP));
          ASSERT(-L \<in> snd ` D\<^sub>0);
          ASSERT(L' \<in> snd ` D\<^sub>0);
          ASSERT(undefined_lit M1 (-L));
          let W = W(L':= W L' @ [length N]);
          let W = W(-L:= W (-L) @ [length N]);
          let D'' = array_of_arl D';
          RETURN (rescore (rescore_clause D'' (Propagated (-L) (length N) # M1)), N @ [D''], U,
            None, NP, UP, {#L#}, W)
        }
        else do {
          D' \<leftarrow> single_of_mset D';
          ASSERT(undefined_lit M1 (-L));
          ASSERT(-L \<in> snd ` D\<^sub>0);
          RETURN (rescore (Propagated (-L) 0 # M1), N, U, None, NP, add_mset {#D'#} UP, add_mset L {#}, W)
        }
      }
    }
  \<close>
  unfolding backtrack_wl_D_def Let_def rescore_clause_def rescore_def by fast


lemma bind_ref_tag_SPEC: \<open>bind_ref_tag a (SPEC P) \<longleftrightarrow> P a\<close>
  unfolding bind_ref_tag_def by auto

lemma backtrack_wl_D_helper: \<open>literals_are_in_N\<^sub>0 xd \<Longrightarrow> RETURN xk \<le> list_of_mset2 xh La xd \<Longrightarrow> literals_are_in_N\<^sub>0 (mset (array_of_arl xk))\<close>
  apply (auto simp: bind_ref_tag_False_True array_of_arl_def list_of_mset2_def bind_ref_tag_SPEC)
  done

sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  unfolding backtrack_wl_D_alt_def PR_CONST_def backtrack_wl_D_helper[simp]
  unfolding twl_st_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric]
    extract_shorter_conflict_wl'_def[symmetric]
    cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  apply (rewrite at \<open>(_, add_mset (add_mset _ \<hole>) _, _)\<close> lms_fold_custom_empty)
  unfolding no_skip_def[symmetric] no_resolve_def[symmetric]
    find_decomp_wl'_find_decomp_wl[symmetric] option.sel add_mset_list.simps
  by sepref \<comment> \<open>slow\<close>


concrete_definition (in -) backtrack_wl_D_code
   uses twl_array_code.backtrack_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]


paragraph \<open>Decide\<close>

lemma (in -)not_is_None_not_None: \<open>\<not>is_None s \<Longrightarrow> s \<noteq> None\<close>
  by (auto split: option.splits)

definition (in -) defined_atm :: \<open>('v, nat) ann_lits \<Rightarrow> 'v \<Rightarrow> bool\<close> where
\<open>defined_atm M L = defined_lit M (Pos L)\<close>

definition (in -) defined_atm_impl where
  \<open>defined_atm_impl = (\<lambda>(M, xs, lvls, k) L. do {
      ASSERT(L < length xs);
      RETURN (xs!L \<noteq> None)
    })\<close>

sepref_thm defined_atm_impl
  is \<open>uncurry defined_atm_impl\<close>
  :: \<open>(trailt_conc)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding defined_atm_impl_def
  by sepref

concrete_definition (in -) defined_atm_code
   uses twl_array_code.defined_atm_impl.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) defined_atm_code_def

lemmas undefined_atm_impl_refine[sepref_fr_rules] =
   defined_atm_code.refine[OF twl_array_code_axioms]

lemma undefined_atm_impl:
  \<open>(uncurry defined_atm_impl, uncurry (RETURN oo defined_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>f trailt_ref \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
proof -
  have H: \<open>L < length xs\<close> (is \<open>?length\<close>) and
    none: \<open>defined_atm M L \<longleftrightarrow> xs ! L \<noteq> None\<close> (is ?undef)
    if L_N: \<open>Pos L \<in># N\<^sub>1\<close> and  tr: \<open>((M', xs, lvls, k), M) \<in> trailt_ref\<close>
    for M xs lvls k M' L
  proof -
    have
       \<open>M = M'\<close> and
       \<open>\<forall>L\<in>#N\<^sub>1. atm_of L < length xs \<and> xs ! atm_of L = valued_atm_on_trail M (atm_of L)\<close>
      using tr unfolding trailt_ref_def by fast+
    then have L: \<open>L < length xs\<close> and xsL: \<open>xs ! L = valued_atm_on_trail M L\<close>
      using L_N by force+
    show ?length
      using L .
    show ?undef
      using xsL by (auto simp: valued_atm_on_trail_def defined_atm_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  qed
  show ?thesis
    unfolding defined_atm_impl_def
    by (intro frefI nres_relI) (auto 5 5 simp: none H intro!: ASSERT_leI)
qed

lemma undefined_atm_code_ref[sepref_fr_rules]:
  \<open>(uncurry defined_atm_code, uncurry (RETURN \<circ>\<circ> defined_atm)) \<in>
     [\<lambda>(a, b). Pos b \<in> snd ` D\<^sub>0]\<^sub>a (hr_comp trailt_conc trailt_ref)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using undefined_atm_impl_refine[FCOMP undefined_atm_impl] .

abbreviation (in -) undefined_atm where
  \<open>undefined_atm M L \<equiv> \<not>defined_atm M L\<close>

sepref_register vmtf_find_next_undef
sepref_thm vmtf_find_next_undef_code
  is \<open>uncurry (PR_CONST vmtf_find_next_undef)\<close>
  :: \<open>vmtf_remove_conc\<^sup>k *\<^sub>a (hr_comp trailt_conc trailt_ref)\<^sup>k \<rightarrow>\<^sub>a option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_def PR_CONST_def
  apply (rewrite at \<open>WHILE\<^sub>T\<^bsup>_\<^esup> (\<lambda> _ . \<hole>) _ _\<close> short_circuit_conv)
  apply (rewrite in \<open>If \<hole> _ _\<close> defined_atm_def[symmetric])
  apply (rewrite in \<open>If _ \<hole> _\<close> defined_atm_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_find_next_undef_code
  uses twl_array_code.vmtf_find_next_undef_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_find_next_undef_code_def

lemmas vmtf_find_next_undef_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_code.refine[OF twl_array_code_axioms, unfolded twl_st_assn_def]

definition (in twl_array_code_ops) find_undefined_atm where
  \<open>find_undefined_atm M = SPEC(\<lambda>(M', L). (L \<noteq> None \<longrightarrow> Pos (the L) \<in>snd ` D\<^sub>0 \<and> undefined_atm M (the L)) \<and>
     (L = None \<longrightarrow> (\<forall>K\<in>snd ` D\<^sub>0. defined_lit M K)) \<and> M = M')\<close>

definition (in twl_array_code_ops) vmtf_find_next_undef_upd
  :: \<open>(nat, nat)ann_lits \<times> vmtf_remove_int \<times> phase_saver \<Rightarrow>
        (((nat, nat)ann_lits \<times> vmtf_remove_int \<times> phase_saver) \<times> nat option)nres\<close> where
  \<open>vmtf_find_next_undef_upd = (\<lambda>(M, vm, \<phi>::bool list). do{
      L \<leftarrow>  vmtf_find_next_undef vm M;
      RETURN ((M, update_next_search L vm, \<phi>), L)
  })\<close>

definition trail_ref_except_ann_lits where
 \<open>trail_ref_except_ann_lits = {((M, ((A, m, lst, next_search), removed), \<phi>::bool list), M').
        M = M' \<and> ((A, m, lst, next_search), removed) \<in> vmtf_imp M}\<close>

lemma vmtf_find_next_undef_upd:
  \<open>(vmtf_find_next_undef_upd, find_undefined_atm) \<in>
     trail_ref_except_ann_lits \<rightarrow>\<^sub>f
      \<langle>trail_ref_except_ann_lits \<times>\<^sub>r \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding vmtf_find_next_undef_upd_def trail_ref_except_ann_lits_def find_undefined_atm_def
        update_next_search_def
  apply (intro frefI nres_relI)
  apply (clarify)
  apply (rule bind_refine_spec)
  prefer 2
    apply (rule vmtf_find_next_undef_ref[simplified]; assumption)
  by (auto intro!: RETURN_SPEC_refine simp: image_image defined_atm_def[symmetric])

definition phase_saver_ref where
  \<open>phase_saver_ref = {(M, M'). M = M' \<and> phase_saving M}\<close>

sepref_register vmtf_find_next_undef_upd
sepref_thm vmtf_find_next_undef_upd_code
  is \<open>PR_CONST vmtf_find_next_undef_upd\<close>
  :: \<open>(hr_comp trailt_conc trailt_ref *assn vmtf_remove_conc *assn hr_comp phase_saver_conc phase_saver_ref)\<^sup>d \<rightarrow>\<^sub>a
     (hr_comp trailt_conc trailt_ref *assn vmtf_remove_conc *assn hr_comp phase_saver_conc phase_saver_ref) *assn
        option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_upd_def PR_CONST_def
  by sepref

concrete_definition (in -) vmtf_find_next_undef_upd_code
  uses twl_array_code.vmtf_find_next_undef_upd_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_find_next_undef_upd_code_def

lemmas vmtf_find_next_undef_upd_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_upd_code.refine[OF twl_array_code_axioms, unfolded twl_st_assn_def]

context
begin

private lemma swap_ex_assn_8_10: \<open>(\<exists>\<^sub>Aag ah ai aj ak bd al am an be. P ag ah ai aj ak bd al am an be) =
  (\<exists>\<^sub>Aag ah ai aj ak bd am an be al. P ag ah ai aj ak bd al am an be)\<close>
  for P :: \<open>'aa \<Rightarrow> 'ab \<Rightarrow> 'ac \<Rightarrow> 'ad \<Rightarrow> 'ae \<Rightarrow> 'af \<Rightarrow>'ag \<Rightarrow> 'ah \<Rightarrow> 'ai \<Rightarrow> 'aj \<Rightarrow> assn\<close>
  unfolding ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ab \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ac \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ad \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ae \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'af \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ah \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'ai \<Rightarrow>assn\<close>]
            ex_assn_swap[of \<open>_ :: 'ag \<Rightarrow>'aj \<Rightarrow>assn\<close>]
  ..

text \<open>This incredible ugly proof is the best way I have found to swap the order of the literals.\<close>
private lemma swap_ex_assn_8:
  \<open>(\<exists>\<^sub>A(a::'a) (b::'b) (c::'c) (d::'d) (e::'e) (f::'f) (g::'g) (h::'h) (i::'i).
     P a b c d e f g h i) =
  (\<exists>\<^sub>A(g::'g) (h::'h) (i::'i) (a::'a) (b::'b) (c::'c) (d::'d) (e::'e) (f::'f).
     P a b c d e f g h i)\<close>
  unfolding
   ex_assn_swap[of \<open>_ :: 'b \<Rightarrow>'a \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'c \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'c \<Rightarrow>'b \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'd \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'd \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'd \<Rightarrow>'c \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'e \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'e \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'e \<Rightarrow>'c \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'e \<Rightarrow>'d \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'f \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'f \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'f \<Rightarrow>'c \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'f \<Rightarrow>'d \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'f \<Rightarrow>'e \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'c \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'d \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'e \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'g \<Rightarrow>'f \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'c \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'d \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'e \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'f \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'h \<Rightarrow>'g \<Rightarrow>assn\<close>]

   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'a \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'b \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'c \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'d \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'e \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'f \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'g \<Rightarrow>assn\<close>]
   ex_assn_swap[of \<open>_ :: 'i \<Rightarrow>'h \<Rightarrow>assn\<close>]
  ..

private lemma eq_out_of_ex_assn_replace:
  \<open>\<up> (a = b) * P a = \<up> (a = b) * P b\<close>
  by (metis (full_types) pure_false star_aci(2) star_false_right)

lemma vmtf_find_next_undef_upd_code[sepref_fr_rules]:
  \<open>(vmtf_find_next_undef_upd_code, PR_CONST (find_undefined_atm)) \<in>
      trail_assn\<^sup>d \<rightarrow>\<^sub>a trail_assn *assn option_assn uint32_nat_assn\<close>
  (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
proof -
  have H: \<open>(vmtf_find_next_undef_upd_code, find_undefined_atm)
  \<in> [comp_PRE trail_ref_except_ann_lits (\<lambda>_. True) (\<lambda>_ _. True)
      (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((hr_comp trailt_conc trailt_ref *assn
                       vmtf_remove_conc *assn
                       hr_comp phase_saver_conc phase_saver_ref)\<^sup>d)
                     trail_ref_except_ann_lits \<rightarrow> hr_comp
          ((hr_comp trailt_conc trailt_ref *assn
            vmtf_remove_conc *assn
            hr_comp phase_saver_conc phase_saver_ref) *assn
           option_assn uint32_nat_assn)
          (trail_ref_except_ann_lits \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?im'\<close>)
    using hfref_compI_PRE_aux[OF vmtf_find_next_undef_upd_code_ref, unfolded PR_CONST_def,
      OF vmtf_find_next_undef_upd] .
  have cond: \<open>?cond' = ?cond\<close>
    unfolding comp_PRE_def by auto
  have [simp]: \<open>(\<exists>\<^sub>Aa b. P a b * \<up>(f a b \<and> a = b \<and> g a b)) =
        (\<exists>\<^sub>Aa. P a a * \<up>(f a a \<and>  g a a))\<close>
    for P f g
  proof -
    have \<open>(\<exists>\<^sub>Aa b. P a b * \<up>(f a b \<and> a = b \<and> g a b)) =
        (\<exists>\<^sub>Aa b. P a b * \<up>(f a b) * \<up>(a = b) * \<up>(g a b)) \<close>
      unfolding import_param_3 mult.assoc[symmetric] ..
    also have \<open>\<dots> = (\<exists>\<^sub>Aa. P a a * \<up>(f a a) * \<up>(g a a))\<close>
      by (subst ex_assn_def_pure_eq_middle2) standard
    finally show ?thesis by simp
  qed
  have KH: \<open>(\<exists>\<^sub>Aag ah ai aj ak bd al am an be bf.
           pure (\<langle>nat_ann_lit_rel\<rangle>list_rel) al a * (array_assn id_assn am aa * (array_assn uint32_nat_assn an ab * uint32_nat_assn be b)) *
           (array_assn l_vmtf_atm_assn ag ac * pure (nat_rel \<times>\<^sub>f (\<langle>uint32_nat_rel\<rangle>option_rel \<times>\<^sub>f \<langle>uint32_nat_rel\<rangle>option_rel)) (ah, ai, aj) (ad, ae, ba) *
            arl_assn uint32_nat_assn ak bb *
            phase_saver_conc bf bc) *
           \<up> (((al, am, an, be), af) \<in> trailt_ref \<and> bf = bd \<and> phase_saving bf \<and> af = x \<and> ((ag, ah, ai, aj), ak) \<in> vmtf_imp af)) =
       (\<exists>\<^sub>Aag ah ai aj ak al am an bd.
           pure (\<langle>nat_ann_lit_rel\<rangle>list_rel) af a * (array_assn id_assn ag aa * (array_assn uint32_nat_assn ah ab * uint32_nat_assn ai b)) *
           (array_assn l_vmtf_atm_assn aj ac * pure (nat_rel \<times>\<^sub>f (\<langle>uint32_nat_rel\<rangle>option_rel \<times>\<^sub>f \<langle>uint32_nat_rel\<rangle>option_rel)) (ak, al, am) (ad, ae, ba) *
            arl_assn uint32_nat_assn an bb *
            phase_saver_conc bd bc) *
           \<up> (((af, ag, ah, ai), x) \<in> trailt_ref \<and> ((aj, ak, al, am), an) \<in> vmtf_imp x \<and> phase_saving bd))\<close>
    (is \<open>?A = ?B\<close> is \<open>(\<exists>\<^sub>Aag ah ai aj ak bd al am an be bf.
       ?P al am an be  ag  ah ai aj ak bf * \<up> (?R al am an be \<and> bf = bd \<and> ?\<phi> bf \<and>af = x \<and> ?S ag ah ai aj ak)) =
       (\<exists>\<^sub>Aag ah ai aj ak al am an bd.
           ?P' ag ah ai aj ak al am an bd *
           \<up> (?R' ah ag ai \<and> ?S' aj ak al am an \<and> ?\<phi> bd))\<close>)
    for x and ab ac bc aa af a bb b ad ae ba
  proof -
    have 1: \<open>((af, ag, ah, ai), x) \<in> trailt_ref \<longleftrightarrow> ((af, ag, ah, ai), x) \<in> trailt_ref \<and> af = x\<close>
      for af ag ah ai x by (auto simp: trailt_ref_def)

    have \<open>?A = (\<exists>\<^sub>Aag ah ai aj ak bd al am an be bf.
       ?P al am an be  ag  ah ai aj ak bf * \<up> (?R al am an be) * \<up> (bf = bd) * \<up> (?\<phi> bf) * \<up> (af = x) * \<up> (?S ag ah ai aj ak))\<close>
      unfolding import_param_3 mult.assoc[symmetric] ..
    also have \<open>\<dots> = (\<exists>\<^sub>Aag ah ai aj ak bd al am an be bf.
       ?P al am an be ag ah ai aj ak bf * \<up> (?R al am an be) * \<up> (bf = bd) *( \<up> (?\<phi> bf) * \<up> (af = x) * \<up> (?S ag ah ai aj ak)))\<close>
      by auto
    also have \<open>\<dots> = (\<exists>\<^sub>Aag ah ai aj ak bd al am an be.
       ?P al am an be ag ah ai aj ak bd * \<up> (?R al am an be) * (\<up> (?\<phi> bd) * \<up> (af = x) * \<up> (?S ag ah ai aj ak)))\<close>
      apply (subst ex_assn_def_pure_eq_middle2) ..
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd al am an be.
       ?P al am an be ag ah ai aj ak bd * \<up> (?R al am an be) * \<up> (?\<phi> bd) * \<up> (?S ag ah ai aj ak))\<close>
      unfolding ex_assn_move_out(2)
      by (auto simp: conj_left_commute)
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd al am an be.
       ?P al am an be ag ah ai aj ak bd * \<up> (?R al am an be \<and> al = af) * \<up> (?\<phi> bd) * \<up> (?S ag ah ai aj ak))\<close>
      apply (subst 1)
      by (auto simp: conj_left_commute)
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd al am an be.
       ?P al am an be ag ah ai aj ak bd * \<up> (?R al am an be) * \<up> (al = af) * \<up> (?\<phi> bd) * \<up> (?S ag ah ai aj ak))\<close>
      unfolding import_param_3 mult.assoc[symmetric] ..
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd al am an be.
       (?P al am an be ag ah ai aj ak bd * \<up> (?R al am an be)) * \<up> (al = af) * (\<up> (?\<phi> bd) * \<up> (?S ag ah ai aj ak)))\<close>
      by (auto simp: conj_left_commute)
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd am an be.
       ?P af am an be ag ah ai aj ak bd * \<up> (?R af am an be) * (\<up> (?\<phi> bd) * \<up> (?S ag ah ai aj ak)))\<close>
      apply (subst swap_ex_assn_8_10)
      apply (subst ex_assn_def_pure_eq_middle2)
      by (auto simp: conj_left_commute)
    finally have \<open>?A = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd am an be.
       ?P af am an be ag ah ai aj ak bd * \<up> (?R af am an be \<and> ?\<phi> bd \<and> ?S ag ah ai aj ak))\<close> by simp
    then have A: \<open>?A = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak bd am an be.
       ?P af am an be ag ah ai aj ak bd * \<up> (?R af am an be \<and> ?S ag ah ai aj ak \<and> ?\<phi> bd))\<close>
      (is \<open>_ = _ * ?A'\<close>)
      by (simp add: conj_commute)

    have \<open>?B = (\<exists>\<^sub>Aag ah ai aj ak al am an bd.
           ?P' ag ah ai aj ak al am an bd *
           \<up> (?R' ah ag ai \<and> af = x \<and> ?S' aj ak al am an \<and> ?\<phi> bd))\<close>
      by (subst 1) auto
    also have \<open>\<dots> = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak al am an bd.
           ?P' ag ah ai aj ak al am an bd *
           \<up> (?R' ah ag ai \<and> ?S' aj ak al am an \<and> ?\<phi> bd))\<close>
      (is \<open>_ = _ * ?B'\<close>)
      unfolding ex_assn_move_out(2)
      by (auto simp: conj_left_commute)
    finally have B: \<open>?B = \<up> (af = x) * (\<exists>\<^sub>Aag ah ai aj ak al am an bd.
           ?P' ag ah ai aj ak al am an bd *
           \<up> (?R' ah ag ai \<and> ?S' aj ak al am an \<and> ?\<phi> bd))\<close> .

    have normalise_name: \<open>(\<exists>\<^sub>Aag ah ai aj ak al am an bd. P ag ah ai aj ak al am an bd) =
        (\<exists>\<^sub>Axa xb xc xd xe xf xg xh xi. P xa xb xc xd xe xf xg xh xi)\<close> for P
      ..
    show ?thesis
      unfolding A
      apply (subst B)
      apply (subst swap_ex_assn_8)
      apply (subst normalise_name)
      apply (subst (2) normalise_name)
      apply (subst eq_out_of_ex_assn_replace)
      apply (subst (2) eq_out_of_ex_assn_replace)
      ..
  qed

  have *: \<open>hr_comp
      (hr_comp trailt_conc trailt_ref *assn
       vmtf_remove_conc *assn hr_comp phase_saver_conc phase_saver_ref)
      trail_ref_except_ann_lits = hr_comp trail_conc trail_ref\<close>
    by (sep_auto simp: phase_saver_ref_def trail_ref_except_ann_lits_def trail_ref_def
      hr_comp_def ex_assn_pair_split list_assn_pure_conv option_assn_pure_conv
       intro!: ext arg_cong[of _ _ ex_assn] KH)
  then have pre: \<open>?pre' = ?pre\<close>
    unfolding trail_assn_def hrp_comp_dest
    by (auto simp: trail_ref_except_ann_lits_def intro!: ext)

  have im: \<open>?im' = ?im\<close>
    unfolding trail_assn_def hrp_comp_dest hr_comp_prod_conv
    unfolding *
    by auto
  show ?thesis
    using H unfolding cond pre im PR_CONST_def .
qed

definition lit_of_found_atm where
\<open>lit_of_found_atm M L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

end


definition (in twl_array_code_ops) lit_of_found_atm_D
  :: \<open>trail_int \<Rightarrow> nat option \<Rightarrow> (nat literal option)nres\<close> where
  \<open>lit_of_found_atm_D = (\<lambda>(M, vm, \<phi>::bool list) L. do{
      case L of
        None \<Rightarrow> RETURN None
      | Some L \<Rightarrow> do {
          ASSERT(L < length \<phi>);
          if \<phi>!L then RETURN (Some (Pos L)) else RETURN (Some (Neg L))
        }
  })\<close>

lemma PosL_N\<^sub>1_le_upperN_div_2: \<open>Pos L \<in># N\<^sub>1 \<Longrightarrow> L < upperN div 2\<close>
  using in_N1_less_than_upperN by (auto simp: upperN_def)

lemma NegL_N\<^sub>1_le_upperN_div_2: \<open>Neg L \<in># N\<^sub>1 \<Longrightarrow> L < upperN div 2\<close>
  using in_N1_less_than_upperN by (auto simp: upperN_def)

(* TODO: tune proof*)
lemma Pos_ref[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. 2 * L), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in> snd ` D\<^sub>0]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def upperN_def
      Collect_eq_comp lit_of_natP_def nat_of_uint32_shiftr nat_of_uint32_distrib_mult2
      dest!: PosL_N\<^sub>1_le_upperN_div_2)

lemma Neg_ref[sepref_fr_rules]:
  \<open>(return o (\<lambda>L. 2 * L + 1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in> snd ` D\<^sub>0]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def upperN_def
      Collect_eq_comp lit_of_natP_def nat_of_uint32_shiftr nat_of_uint32_distrib_mult2_plus1
      dest!: PosL_N\<^sub>1_le_upperN_div_2)

definition (in twl_array_code_ops) lit_of_found_atm_D_pre where
\<open>lit_of_found_atm_D_pre = (\<lambda>(M, L). L \<noteq> None \<longrightarrow> Pos (the L) \<in> snd ` D\<^sub>0)\<close>

sepref_register lit_of_found_atm_D
sepref_thm lit_of_found_atm_D_code
  is \<open>uncurry (PR_CONST lit_of_found_atm_D)\<close>
  :: \<open>[lit_of_found_atm_D_pre]\<^sub>a trail_conc\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow> option_assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_D_pre_def
  by sepref

concrete_definition (in -) lit_of_found_atm_D_code
  uses twl_array_code.lit_of_found_atm_D_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) lit_of_found_atm_D_code_def

lemmas lit_of_found_atm_D_code_ref[sepref_fr_rules] =
   lit_of_found_atm_D_code.refine[OF twl_array_code_axioms]

lemma lit_of_found_atm_D_ref:
  \<open>(uncurry (PR_CONST lit_of_found_atm_D), uncurry lit_of_found_atm) \<in>
    [lit_of_found_atm_D_pre]\<^sub>f trail_ref \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle> nres_rel\<close>
  unfolding lit_of_found_atm_D_def lit_of_found_atm_def PR_CONST_def
  by (intro nres_relI frefI)
    (auto simp: trail_ref_def lit_of_found_atm_D_pre_def phase_saving_def
        in_N\<^sub>1_atm_of_in_atms_of_iff
      split: option.splits)

thm lit_of_found_atm_D_code_ref lit_of_found_atm_D_ref

lemma lit_of_found_atm_D_code_hfref[sepref_fr_rules]:
  \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
  \<in> [lit_of_found_atm_D_pre]\<^sub>a trail_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
      option_assn unat_lit_assn\<close>
  (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
proof -
  have H: \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
    \<in> [comp_PRE (trail_ref \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel) lit_of_found_atm_D_pre
          (\<lambda>_. lit_of_found_atm_D_pre)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (trail_conc\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d)
              (trail_ref \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel) \<rightarrow>
      hr_comp (option_assn unat_lit_assn) (\<langle>Id\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?im'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_found_atm_D_code_ref,
      OF lit_of_found_atm_D_ref, unfolded PR_CONST_def] .
  have cond: \<open>?cond' = ?cond\<close>
    unfolding comp_PRE_def by (auto intro!: ext simp: lit_of_found_atm_D_pre_def image_image)
  have pre: \<open>?pre' = ?pre\<close>
    unfolding trail_assn_def prod_hrp_comp hrp_comp_keep hrp_comp_dest
    by auto
  have im: \<open>?im' = ?im\<close>
    by auto
  show ?thesis
    using H unfolding cond pre im PR_CONST_def .
qed

definition find_unassigned_lit_wl_D' :: \<open>nat twl_st_wl \<Rightarrow> (nat twl_st_wl \<times> nat literal option) nres\<close> where
\<open>find_unassigned_lit_wl_D' = (\<lambda>(M, N, U, D, NP, UP, WS, Q). do {
    (M, L) \<leftarrow> find_undefined_atm M;
    ASSERT(lit_of_found_atm_D_pre(M, L));
    L \<leftarrow> lit_of_found_atm M L;
    RETURN ((M, N, U, D, NP, UP, WS, Q), L)
  })\<close>

lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D', find_unassigned_lit_wl_D :: nat twl_st_wl \<Rightarrow> _) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> literals_are_N\<^sub>0 S \<and>
      get_conflict_wl S = None]\<^sub>f Id \<rightarrow>
      \<langle>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel\<rangle> nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto
  have atms: \<open>atms_of N\<^sub>1 =
         atms_of_ms ((\<lambda>x. mset (take 2 x) + mset (drop 2 x)) ` set (take U (tl N))) \<union>
         atms_of_mm NP \<and> (\<forall>y. atm_of y \<in> atms_of_mm NP \<longrightarrow> defined_lit M y)\<close>
      if inv: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close> and
        N\<^sub>0: \<open>literals_are_N\<^sub>0 (M, N, U, D, NP, UP, WS, Q)\<close> and
        confl: \<open>get_conflict_wl (M, N, U, D, NP, UP, WS, Q) = None\<close>
      for M N U D NP UP WS Q
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm
            (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q)))\<close> and
        unit: \<open>unit_clss_inv (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close>
      using inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>defined_lit M L\<close> if NP: \<open>atm_of L\<in> atms_of_mm NP\<close> for L
    proof -
      obtain C where C_NP: \<open>C \<in># NP\<close> and L_C: \<open>atm_of L \<in> atms_of C\<close>
         using NP unfolding atms_of_ms_def by auto
      have \<open>C\<in>set_mset NP \<Longrightarrow> \<exists>L. C = {#L#} \<and> get_level M L = 0 \<and> L \<in> lits_of_l M\<close> for C
         using unit confl by auto
      from this[of C] obtain L' where \<open>C = {#L'#}\<close> and \<open>L' \<in> lits_of_l M\<close>
         using C_NP by auto
      then show ?thesis
        using L_C by (auto simp: Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of)
    qed
    ultimately show ?thesis
      using N\<^sub>0 unfolding is_N\<^sub>1_alt_def
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset_state
        mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def simp del: unit_clss_inv.simps)
  qed
  show ?thesis
   unfolding find_unassigned_lit_wl_D'_def find_unassigned_lit_wl_D_def find_undefined_atm_def
    ID_R lit_of_found_atm_def
   apply (intro frefI nres_relI)
   apply clarify
   apply (refine_vcg)
   subgoal by (auto simp: lit_of_found_atm_D_pre_def)
   subgoal by (auto simp: lit_of_found_atm_D_pre_def)
   subgoal by (auto simp: lit_of_found_atm_D_pre_def defined_atm_def)
   subgoal by (auto simp: lit_of_found_atm_D_pre_def in_N\<^sub>1_atm_of_in_atms_of_iff
     simp del: twl_st_of_wl.simps dest!: atms)
   subgoal by (auto simp: lit_of_found_atm_D_pre_def in_N\<^sub>1_atm_of_in_atms_of_iff
     simp del: twl_st_of_wl.simps dest!: atms)
   done
qed

sepref_register find_undefined_atm
sepref_register find_unassigned_lit_wl_D'
sepref_register lit_of_found_atm
sepref_thm find_unassigned_lit_wl_D_code
  is \<open>PR_CONST find_unassigned_lit_wl_D'\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn *assn option_assn unat_lit_assn\<close>
  unfolding find_unassigned_lit_wl_D'_def PR_CONST_def twl_st_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_unassigned_lit_wl_D_code
  uses twl_array_code.find_unassigned_lit_wl_D_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_unassigned_lit_wl_D_code_def

lemmas find_unassigned_lit_wl_D_code[sepref_fr_rules] =
   find_unassigned_lit_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

lemma find_unassigned_lit_wl_D_code_hfref[unfolded twl_st_assn_def, sepref_fr_rules]:
  \<open>(find_unassigned_lit_wl_D_code, find_unassigned_lit_wl_D)
  \<in> [\<lambda>S. literals_are_N\<^sub>0 S \<and> twl_struct_invs (twl_st_of_wl None S) \<and> get_conflict_wl S = None]\<^sub>a
    twl_st_assn\<^sup>d \<rightarrow>
    twl_st_assn *assn option_assn unat_lit_assn\<close>
  (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
proof -
  have H: \<open>(find_unassigned_lit_wl_D_code, find_unassigned_lit_wl_D)
  \<in> [comp_PRE Id
      (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
           literals_are_N\<^sub>0 S \<and> get_conflict_wl S = None)
      (\<lambda>_ _. True)
      (\<lambda>_. True)]\<^sub>a
    hrp_comp ((trail_assn *assn clauses_ll_assn *assn nat_assn *assn conflict_option_assn *assn
        clauses_l_assn *assn clauses_l_assn *assn clause_l_assn *assn
        hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0))\<^sup>d) Id \<rightarrow>
    hr_comp ((trail_assn *assn clauses_ll_assn *assn nat_assn *assn conflict_option_assn *assn
        clauses_l_assn *assn clauses_l_assn *assn clause_l_assn *assn
        hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D\<^sub>0)) *assn
        option_assn unat_lit_assn) (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?cond']\<^sub>a ?pre' \<rightarrow> ?im'\<close>)
    using hfref_compI_PRE_aux[OF find_unassigned_lit_wl_D_code[unfolded PR_CONST_def],
      OF find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[unfolded PR_CONST_def]] .
  have cond: \<open>?cond' = ?cond\<close>
    unfolding comp_PRE_def by (auto intro!: ext simp: lit_of_found_atm_D_pre_def image_image)
  have pre: \<open>?pre' = ?pre\<close>
    unfolding trail_assn_def prod_hrp_comp hrp_comp_keep hrp_comp_dest twl_st_assn_def
    by auto
  have im: \<open>?im' = ?im\<close>
    unfolding twl_st_assn_def
    by auto
  show ?thesis
    using H unfolding cond pre im PR_CONST_def .
qed

sepref_register decide_wl_or_skip_D
sepref_thm decide_wl_or_skip_D_code
  is \<open>PR_CONST decide_wl_or_skip_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_assn\<close>
  unfolding decide_wl_or_skip_D_def PR_CONST_def twl_st_assn_def
    cons_trail_Decided.simps[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) decide_wl_or_skip_D_code
   uses twl_array_code.decide_wl_or_skip_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) decide_wl_or_skip_D_code_def

lemmas decide_wl_or_skip_D_code_def_refine[sepref_fr_rules] =
   decide_wl_or_skip_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]


subsubsection \<open>Combining Together: the Other Rules\<close>
term get_conflict_wl_is_None
sepref_register get_conflict_wl_is_None
sepref_thm (in twl_array_code_ops) get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None\<close>
  :: \<open>twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_def twl_st_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_code
   uses twl_array_code_ops.get_conflict_wl_is_None_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_code_def

lemmas (in twl_array_code_ops)get_conflict_wl_is_None_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_code.refine[of N\<^sub>0, unfolded twl_st_assn_def]


sepref_register cdcl_twl_o_prog_wl_D
sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_def PR_CONST_def twl_st_assn_def
  unfolding get_conflict_wl_is_None get_conflict_wl_get_conflict_wl_is_Nil
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses twl_array_code.cdcl_twl_o_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]


subsubsection \<open>Combining Together: Full Strategy\<close>

sepref_register cdcl_twl_stgy_prog_wl_D
sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_def PR_CONST_def twl_st_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_code
   uses twl_array_code.cdcl_twl_stgy_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_code_def

lemmas cdcl_twl_stgy_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_code.refine[of N\<^sub>0, unfolded twl_st_assn_def]

concrete_definition (in -) select_and_remove_from_literals_to_update_wl''_code
   uses twl_array_code.hd_select_and_remove_from_literals_to_update_wl''_refine
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms select_and_remove_from_literals_to_update_wl''_code_def

lemmas select_and_remove_from_literals_to_update_wl''_code_2[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl''_code.refine[of N\<^sub>0, unfolded twl_st_assn_def]

end

export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.ML"

end