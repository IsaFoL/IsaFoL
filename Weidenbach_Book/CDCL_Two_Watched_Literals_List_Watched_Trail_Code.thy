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
  \<open>insert_sort_nth =  (\<lambda>(A, _). insert_sort (\<lambda>remove n. stamp (A ! (remove ! n))))\<close>


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

end


subsubsection \<open>Refining code\<close>


context twl_array_code
begin

paragraph \<open>Inner Loop of the Propagation\<close>

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
  \<open>conflict_merge C  = (\<lambda>(b, xs). do {
     S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, zs). i \<le> length C \<and> length (snd zs) = length (snd xs) \<and>
            ((False, zs), Some (mset (take i C))) \<in> option_conflict_rel \<and> Suc i < upperN \<and> Suc (fst zs) < upperN \<^esup>
       (\<lambda>(i, zs). i < length C)
       (\<lambda>(i, zs). do{
           ASSERT(i < length C);
           ASSERT(Suc i < upperN);
           RETURN(Suc i, conflict_add (C!i) zs)})
       (0, xs);
     RETURN (False, snd S)
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
      \<open>((b, n, xs), None) \<in> option_conflict_rel\<close> and
     dist: \<open>distinct (N! i)\<close> and
     lits: \<open>literals_are_in_N\<^sub>0 (mset (N ! i))\<close> and
     tauto: \<open>\<not>tautology (mset (N ! i))\<close>
    for b n xs N i
  proof -
    have [simp]: \<open>a < length (N!i) \<Longrightarrow> Suc (Suc a) < upperN\<close> for a
      using simple_clss_size_upper_div2[of \<open>mset (N!i)\<close>] that by (auto simp: upperN_def)

    show ?thesis
      unfolding conflict_merge_aa_def conflict_merge_def PR_CONST_def
      apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(j, _). length (N!i) - j)\<close>])
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal using that by (auto simp: option_conflict_rel_def)
      subgoal by (simp add: upperN_def)
      subgoal using that by (auto simp add: option_conflict_rel_def conflict_rel_def upperN_def)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal for b' n' s i zs by (cases \<open>snd s\<close>) (auto simp: conflict_add_def split: if_splits)
      subgoal for b' n' s j zs
        using conflict_add_conflict_rel[of \<open>fst zs\<close> \<open>snd zs\<close> \<open>mset (take j (N ! i))\<close> \<open>N ! i ! j\<close>]
        dist lits tauto
        by (auto simp: option_conflict_rel_def take_Suc_conv_app_nth
            literals_are_in_N\<^sub>0_in_N\<^sub>1)
      subgoal using that by (auto simp add: option_conflict_rel_def conflict_rel_def)
      subgoal for b' n' s j zs by (cases \<open>snd s\<close>)
         (auto simp: conflict_add_def option_conflict_rel_def conflict_rel_def)
      subgoal by auto
      subgoal using that by auto
      done
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
  shows \<open>distinct((get_clauses_wl S)!C)\<close> and \<open>get_conflict_wl S = None\<close> and
    \<open>\<not>tautology(mset((get_clauses_wl S)!C))\<close>
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
    no_tauto: \<open>\<forall>D\<in>#init_clss (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))).
      \<not> tautology D\<close>
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
  show \<open>\<not>tautology(mset((get_clauses_wl S)!C))\<close>
     using no_tauto NC
    apply (subst (asm) append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
    apply (subst (asm) set_append)
    by (auto simp: C_def drop_Suc S cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset)
qed

lemma (in -)[sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)

fun watched_by_int:: \<open>twl_st_wl_int \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, U, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, W) = W\<close>

fun get_watched_wl_int :: \<open>twl_st_wl_int \<Rightarrow> nat list list\<close> where
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

(* TODO Move, but introduce a proper name for the constant on the right-hand side *)
lemma (in -) nth_aa_uint_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows
    \<open>(uncurry2 (\<lambda>x L L'. nth_aa x (nat_of_uint32 L) L'), uncurry2 (RETURN ooo nth_rll)) \<in>
       [\<lambda>((x, L), L'). L < length x \<and> L' < length (x ! L)]\<^sub>a
       (arrayO_assn (arl_assn R))\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> R\<close>
  by sepref_to_hoare
    (use assms in \<open>sep_auto simp: uint32_nat_rel_def br_def length_ll_def nth_ll_def
     nth_rll_def\<close>)
(* End Move *)

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


(* get_conflict_wl S = None
 distinct (get_clauses_wl b ! xa)
 literals_are_in_N\<^sub>0 (mset (get_clauses_wl b ! xa))
\<not> tautology (mset (get_clauses_wl b ! xa))
 *)

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
    \<open>\<not> tautology (mset (get_clauses_wl S ! watched_by_app S L w))\<close> and
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
          (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S)))\<close> and
    init_tauto: \<open>\<forall>D\<in>#init_clss (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))).
        \<not> tautology D\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))). \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L)
            (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  then have \<open>\<forall>D\<in>mset ` set (tl (get_clauses_wl S)). \<not> tautology D\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    unfolding set_append
    using init_tauto learned_tauto
    apply (cases S)
    by (auto simp: drop_Suc cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset
        watched_by_app_def)
  then show \<open>\<not> tautology (mset (get_clauses_wl S ! watched_by_app S L w))\<close>
    using S_L_W_le_S S_L_W_ge_0 nempty
    by (cases S; cases \<open>get_clauses_wl S\<close>)
       (auto simp: cdcl\<^sub>W_restart_mset_state clauses_def mset_take_mset_drop_mset watched_by_app_def)
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
   valued_st_int_code.refine[of N\<^sub>0, OF twl_array_code_axioms, unfolded twl_st_assn_def]

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

definition literals_are_in_N\<^sub>0_mm :: \<open>nat clauses \<Rightarrow> bool\<close> where
  \<open>literals_are_in_N\<^sub>0_mm C \<longleftrightarrow> set_mset (all_lits_of_mm C) \<subseteq> set_mset N\<^sub>1\<close>

(* TODO Move up *)
fun get_clauses_wl_int :: \<open>twl_st_wl_int \<Rightarrow> nat clauses_l\<close> where
  \<open>get_clauses_wl_int (M, N, U, D, _) = N\<close>
(* End Move up *)

(* TODO Move *)
definition literals_are_in_N\<^sub>0_int where
  \<open>literals_are_in_N\<^sub>0_int S = literals_are_in_N\<^sub>0_mm (mset `# mset (tl (get_clauses_wl_int S)))\<close>

lemma literals_are_in_N\<^sub>0_mm_in_N\<^sub>1:
  assumes
    N1: \<open>literals_are_in_N\<^sub>0_mm (mset `# mset xs)\<close> and
    i_xs: \<open>i < length xs\<close> and j_xs: \<open>j < length (xs ! i)\<close>
  shows \<open>xs ! i ! j \<in># N\<^sub>1\<close>
proof -
  have \<open>xs ! i \<in># mset xs\<close>
    using i_xs by auto
  thm in_all_lits_of_m_ain_atms_of_iff
  then have \<open>xs ! i ! j \<in> set_mset (all_lits_of_mm (mset `# mset xs))\<close>
    using j_xs by (auto simp: in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def Bex_def
      intro!: exI[of _ \<open>xs ! i\<close>])
  then show ?thesis
    using N1 unfolding literals_are_in_N\<^sub>0_mm_def by blast
qed
(* End Move *)

(* TODO unify name with equivalent for \<^term>\<open>literals_are_in_N\<^sub>0\<close>*)
lemma literals_are_in_N\<^sub>0_int_length_in_D\<^sub>0:
  assumes \<open>literals_are_in_N\<^sub>0_int S\<close> and
    \<open>i < length (get_clauses_wl_int S)\<close> and
    \<open>j < length (get_clauses_wl_int S ! i)\<close> and
    \<open>i > 0\<close>
  shows \<open>get_clauses_wl_int S ! i ! j \<in> snd ` D\<^sub>0\<close>
  using assms literals_are_in_N\<^sub>0_mm_in_N\<^sub>1[of \<open>tl (get_clauses_wl_int S)\<close> \<open>i - 1\<close> j]
  by (auto simp: literals_are_in_N\<^sub>0_int_def image_image nth_tl)

lemma literals_are_in_N\<^sub>0_int_length_in_D\<^sub>0':
  assumes \<open>literals_are_in_N\<^sub>0_int S\<close> and
    \<open>i < length (get_clauses_wl_int S)\<close> and
    \<open>j < length (get_clauses_wl_int S ! i)\<close> and
    \<open>i > 0\<close> and N: \<open>N = get_clauses_wl_int S\<close>
  shows \<open>N ! i ! j \<in> snd ` D\<^sub>0\<close>
  using literals_are_in_N\<^sub>0_int_length_in_D\<^sub>0[OF assms(1-4)] unfolding N .

find_theorems find_unwatched return
find_theorems return defined_lit
sepref_thm find_unwatched_wl_s_int_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_s_int))\<close>
  :: \<open>[\<lambda>(S, i). i < length (get_clauses_wl_int S) \<and> i > 0 \<and> literals_are_in_N\<^sub>0_int S]\<^sub>a
         twl_st_int_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_N\<^sub>0_int_length_in_D\<^sub>0'[intro]
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

(* sepref_register find_unwatched_wl_s *)
theorem find_unwatched_wl_s_int_code_find_unwatched_wl_s[sepref_fr_rules]:
  \<open>(uncurry find_unwatched_wl_s_int_code, uncurry ((* PR_CONST *) find_unwatched_wl_s))
    \<in> [\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_N\<^sub>0 S \<and>
         2 \<le> length (get_clauses_wl S ! i)]\<^sub>a
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
       hr_comp (option_assn nat_assn) Id
\<close>
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
    have \<open>literals_are_in_N\<^sub>0_int T\<close> and \<open>get_clauses_wl_int T = get_clauses_wl S\<close> if
       \<open>is_N\<^sub>1 (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close> and
       \<open>(T, S) \<in> twl_st_ref\<close>
      for S and T
      using that apply (auto simp: twl_st_ref_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' clauses_def literals_are_in_N\<^sub>0_int_def)
      apply (auto simp add: all_lits_of_mm_union literals_are_in_N\<^sub>0_mm_def is_N\<^sub>1_def)
      done
    then show ?thesis
      using that unfolding comp_PRE_def
      by (intro ext impI)(use that in \<open>fastforce simp: comp_PRE_def
            mset_take_mset_drop_mset clauses_def mset_take_mset_drop_mset' drop_Suc
          simp del: twl_st_of.simps st_l_of_wl.simps\<close>)
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

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] = cons_trail_Propagated_tr_code.refine[OF twl_array_code_axioms]

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

(* TODO Move to declaration *)
declare delete_index_and_swap_aa_ll_hnr_u[sepref_fr_rules]

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

lemma update_clause_wl_int_code_update_clause_wl[sepref_fr_rules]:
  \<open>(uncurry5 update_clause_wl_int_code, uncurry5 update_clause_wl) \<in>
    [\<lambda>(((((L, C), w), i), f), S).
      (get_clauses_wl S ! C) ! f \<noteq> L \<and>
      C < length (get_clauses_wl S) \<and>
      f < length (get_clauses_wl S ! C) \<and>
      i < length (get_clauses_wl S ! C) \<and>
      L \<in> snd ` D\<^sub>0 \<and>
      (get_clauses_wl S ! C) ! f \<in> snd ` D\<^sub>0 \<and>
      w < length (get_watched_wl S L)]\<^sub>a
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
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_ref_def  map_fun_rel_def
    by auto
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


(* TODO Move up *)
fun get_trail_wl_int :: \<open>twl_st_wl_int \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_int (M, N, U, D, _) = M\<close>
(* End Move up *)

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

lemma find_unwatched_get_clause_neq_L:
  \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<noteq> L\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_s S (watched_by_app S L C)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof (rule ccontr)
  have is_N\<^sub>1_alt_def_sym: \<open>is_N\<^sub>1 (all_lits_of_mm A) \<longleftrightarrow> atms_of N\<^sub>1 = atms_of_mm A\<close> for A
    unfolding is_N\<^sub>1_alt_def by metis
  assume eq[simplified, simp]: \<open>\<not> ?thesis\<close>
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
    using find_unw unfolding find_unwatched_wl_s_def find_unwatched_l_def
    by (cases S; auto)+
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

sepref_register unit_propagation_inner_loop_body_wl_D
sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  supply unit_prop_body_wl_D_invD[intro,dest]  find_unwatched_in_D\<^sub>0[intro]
   find_unwatched_le_length[intro] find_unwatched_get_clause_neq_L[intro]
   length_rll_def[simp]
    if_splits[split]
  access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro, simp, dest]
  length_rll_def[simp]
  watched_by.simps[simp del] undefined_lit_valued_st_iff[iff]
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_app_def[symmetric] access_lit_in_clauses_def[symmetric]
    find_unwatched_l_find_unwatched_wl_s
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  find_unwatched_wl_s_int_def[symmetric] valued_st_def[symmetric]
  mark_conflict_wl'_alt_def[symmetric]
  supply [[goals_limit=1]]

  supply unit_prop_body_wl_invD[dest, intro]
     supply find_unwatched_get_clause_neq_L[simp]
     apply sepref
     done

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses twl_array_code.unit_propagation_inner_loop_body_wl_D.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>
prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of N\<^sub>0, OF twl_array_code_axioms,
     unfolded twl_st_assn_def]

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