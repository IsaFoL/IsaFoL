theory IsaSAT_Initialisation
  imports IsaSAT_Setup Watched_Literals_Watch_List_Initialisation
begin

no_notation Ref.update ("_ := _" 62)


section \<open>Code for the initialisation of the Data Structure\<close>

context isasat_input_bounded
begin

type_synonym (in -) 'v twl_st_wl_init = \<open>'v twl_st_wl \<times> 'v clauses\<close>


type_synonym (in -) vmtf_remove_int_option_fst_As = \<open>vmtf_option_fst_As \<times> nat list\<close>

definition (in isasat_input_ops) vmtf_init
   :: \<open>(nat, nat) ann_lits \<Rightarrow> vmtf_remove_int_option_fst_As set\<close>
where
  \<open>vmtf_init M = {((ns, m, fst_As, lst_As, next_search), to_remove).
   \<A>\<^sub>i\<^sub>n \<noteq> {#} \<longrightarrow> (fst_As \<noteq> None \<and> lst_As \<noteq> None \<and> ((ns, m, the fst_As, the lst_As, next_search),
     to_remove) \<in> vmtf M)}\<close>

type_synonym (in -) twl_st_wl_heur_init =
  \<open>(nat,nat)ann_lits \<times> nat clauses_l \<times> nat clause option \<times> nat lit_queue_wl \<times>
    nat list list \<times> vmtf_remove_int_option_fst_As \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd\<close>

abbreviation (in -) vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn nat_vmtf_node_assn *a nat_assn *a
    option_assn uint32_nat_assn *a option_assn uint32_nat_assn *a option_assn uint32_nat_assn)\<close>

type_synonym (in -)vmtf_assn_option_fst_As =
  \<open>(uint32, nat) vmtf_node array \<times> nat \<times> uint32 option \<times> uint32 option \<times> uint32 option\<close>

type_synonym (in -)vmtf_remove_assn_option_fst_As = \<open>vmtf_assn_option_fst_As \<times> uint32 array_list\<close>

abbreviation (in -)vmtf_remove_conc_option_fst_As
  :: \<open>vmtf_remove_int_option_fst_As \<Rightarrow> vmtf_remove_assn_option_fst_As \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc_option_fst_As \<equiv> vmtf_conc_option_fst_As *a arl_assn uint32_nat_assn\<close>

definition (in isasat_input_ops) twl_st_heur_init
  :: \<open>(twl_st_wl_heur_init \<times> nat twl_st_wl_init) set\<close>
where
\<open>twl_st_heur_init =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd), ((M, N, D, NE, UE, Q, W), OC)).
    M' = M \<and> N' = N \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach
  }\<close>

type_synonym (in -)twl_st_wll_trail_init =
  \<open>trail_pol_assn \<times> clauses_wl \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn\<close>

definition (in isasat_input_ops) isasat_init_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close>
where
\<open>isasat_init_assn =
  trail_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc_option_fst_As *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn *a
  lbd_assn\<close>

definition (in isasat_input_ops) twl_st_init_assn
  :: \<open>nat twl_st_wl_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close>
where
  \<open>twl_st_init_assn = hr_comp isasat_init_assn twl_st_heur_init\<close>

fun (in -)get_conflict_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat clause option\<close> where
  \<open>get_conflict_wl_heur_init (_, _, D, _) = D\<close>

fun (in -) get_watched_list_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat list list\<close> where
  \<open>get_watched_list_heur_init (_, _, _, _, W, _) = W\<close>

fun (in -) get_trail_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur_init (M, _, _, _, _, _, _) = M\<close>

definition (in isasat_input_ops) propagate_unit_cls
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>propagate_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q, WS), OC).
     ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, add_mset (-L) Q, WS), OC))\<close>

definition (in isasat_input_ops) propagate_unit_cls_heur
 :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>propagate_unit_cls_heur = (\<lambda>L (M, N, D, Q, oth). do {
     ASSERT(undefined_lit M L \<and> L \<in> snd ` D\<^sub>0);
     RETURN (Propagated L 0 # M, N, D, add_mset (-L) Q, oth)})\<close>

lemma propagate_unit_cls_heur_propagate_unit_cls:
  \<open>(uncurry propagate_unit_cls_heur, uncurry (RETURN oo propagate_unit_init_wl)) \<in>
   [\<lambda>(L, S). undefined_lit (get_trail_wl (fst S)) L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def propagate_unit_cls_heur_def propagate_unit_init_wl_def
       vmtf_init_def image_image
      intro: vmtf_consD)

sepref_thm propagate_unit_cls_code
  is \<open>uncurry (PR_CONST propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding propagate_unit_cls_heur_def isasat_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) propagate_unit_cls_code
   uses isasat_input_bounded.propagate_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) propagate_unit_cls_code_def

lemmas propagate_unit_cls_heur_hnr[sepref_fr_rules] =
   propagate_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) already_propagated_unit_cls
   :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q, WS), OC).
     ((M, N, D, add_mset {#L#} NE, UE, Q, WS), OC))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_heur
   :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_heur = (\<lambda>L (M, N, D, Q, oth).
     RETURN (M, N, D, Q, oth))\<close>

lemma already_propagated_unit_cls_heur_already_propagated_unit_cls:
  \<open>(uncurry already_propagated_unit_cls_heur, uncurry (RETURN oo already_propagated_unit_init_wl)) \<in>
   list_mset_rel \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def already_propagated_unit_cls_heur_def
     already_propagated_unit_init_wl_def
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_code
  is \<open>uncurry already_propagated_unit_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def isasat_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) already_propagated_unit_cls_code
   uses isasat_input_bounded.already_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_code_def

lemmas already_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem already_propagated_unit_cls_hnr[sepref_fr_rules]:
  \<open>(uncurry already_propagated_unit_cls_code, uncurry (RETURN \<circ>\<circ> already_propagated_unit_init_wl))
  \<in> clause_l_assn\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  using already_propagated_unit_cls_heur_hnr[FCOMP already_propagated_unit_cls_heur_already_propagated_unit_cls]
  unfolding twl_st_init_assn_def[symmetric] clause_l_assn_alt_def[symmetric] by simp

definition (in -) set_conflict_unit :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_unit L _ = Some {#L#}\<close>

definition (in isasat_input_ops) conflict_propagated_unit_cls
 :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>conflict_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q, WS), OC).
     ((M, N, set_conflict_unit L D, add_mset {#L#} NE, UE, {#}, WS), OC))\<close>

definition (in isasat_input_ops) conflict_propagated_unit_cls_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>conflict_propagated_unit_cls_heur = (\<lambda>L (M, N, D, Q, oth). do {
     ASSERT(L \<in> snd ` D\<^sub>0 \<and> D = None);
     RETURN (M, N, set_conflict_unit L D, {#}, oth)
    })\<close>

lemma conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls:
  \<open>(uncurry conflict_propagated_unit_cls_heur, uncurry (RETURN oo set_conflict_init_wl)) \<in>
   [\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> get_conflict_init_wl S = None]\<^sub>f
      nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def conflict_propagated_unit_cls_heur_def conflict_propagated_unit_cls_def
       image_image set_conflict_init_wl_def set_conflict_unit_def
     intro: vmtf_consD)

definition (in isasat_input_ops) set_conflict_unit_heur where
  \<open>set_conflict_unit_heur = (\<lambda> L (b, n, xs). RETURN (False, 1, xs[atm_of L := Some (is_pos L)]))\<close>

lemma set_conflict_unit_heur_set_conflict_unit:
  \<open>(uncurry set_conflict_unit_heur, uncurry (RETURN oo set_conflict_unit)) \<in>
    [\<lambda>(L, D). D = None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<rightarrow>
     \<langle>option_lookup_clause_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def set_conflict_unit_heur_def set_conflict_unit_def
      option_lookup_clause_rel_def lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      intro!: mset_as_position.intros)

sepref_thm set_conflict_unit_code
  is \<open>uncurry set_conflict_unit_heur\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn\<close>
  supply one_uint32_nat[sepref_fr_rules]
  unfolding set_conflict_unit_heur_def one_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) set_conflict_unit_code
   uses isasat_input_bounded.set_conflict_unit_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_unit_code_def

lemmas set_conflict_unit_heur_hnr[sepref_fr_rules] =
   set_conflict_unit_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem set_conflict_unit_hnr[sepref_fr_rules]:
  \<open>(uncurry set_conflict_unit_code, uncurry (RETURN oo set_conflict_unit))
    \<in> [\<lambda>(L, D). D = None \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d  \<rightarrow> option_lookup_clause_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
     (\<lambda>(L, D). D = None \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a
                      conflict_option_rel_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f
                      option_lookup_clause_rel) \<rightarrow> hr_comp
                  conflict_option_rel_assn
                  option_lookup_clause_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_conflict_unit_heur_hnr
    set_conflict_unit_heur_set_conflict_unit] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def image_image
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep option_lookup_clause_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm conflict_propagated_unit_cls_code
  is \<open>uncurry (PR_CONST conflict_propagated_unit_cls_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl_heur_init S = None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) conflict_propagated_unit_cls_code
   uses isasat_input_bounded.conflict_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_propagated_unit_cls_code_def

lemmas conflict_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   conflict_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

text \<open>TODO: why is sepref not able to handle the inlined version of the Let for True?\<close>
definition (in isasat_input_ops) add_init_cls_heur
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>  where
  \<open>add_init_cls_heur = (\<lambda>C (M, N, D, Q, WS, oth). do {
     let L = hd C; let L' = hd (tl C);
     let b = True; let C = op_array_of_list C;
     (N, i) \<leftarrow> fm_add_new b C N;
     let WS = WS[nat_of_lit L := WS ! nat_of_lit L @ [i]];
     let WS = WS[nat_of_lit L' := WS ! nat_of_lit L' @ [i]];
     RETURN (M, N, D, Q, WS, oth)})\<close>

lemma length_C_nempty_iff: \<open>length C \<ge> 2 \<longleftrightarrow> C \<noteq> [] \<and> tl C \<noteq> []\<close>
  by (cases C; cases \<open>tl C\<close>) auto

sepref_thm add_init_cls_code
  is \<open>uncurry add_init_cls_heur\<close>
  :: \<open>[\<lambda>(C, S). length C \<ge> 2 \<and> nat_of_lit (hd C) < length (get_watched_list_heur_init S) \<and>
        nat_of_lit (hd (tl C)) < length (get_watched_list_heur_init S)]\<^sub>a
      (list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def isasat_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  unfolding isasat_init_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric] length_C_nempty_iff
  by sepref

concrete_definition (in -) add_init_cls_code
   uses isasat_input_bounded.add_init_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) add_init_cls_code_def

lemmas add_init_cls_heur_hnr[sepref_fr_rules] =
   add_init_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

text \<open>TODO Move\<close>
lemma (in -)RES_RETURN_RES_RES2:
   \<open>RES \<Phi> \<bind> (\<lambda>(T, T'). RETURN (f T T')) = RES (uncurry f ` \<Phi>)\<close>
  using RES_RES2_RETURN_RES[of \<open>\<Phi>\<close> \<open>\<lambda>T T'. {f T T'}\<close>]
  apply (subst (asm)(2) split_prod_bound)
  by (auto simp: RETURN_def uncurry_def)

lemma add_init_cls_heur_add_init_cls:
  \<open>(uncurry add_init_cls_heur, uncurry (add_to_clauses_init_wl)) \<in>
   [\<lambda>(C, S). length C \<ge> 2 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> distinct C]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (fastforce simp: twl_st_heur_init_def add_init_cls_heur_def add_to_clauses_init_wl_def Let_def
      fm_add_new_def get_fresh_index_def RES_RETURN_RES RES_RETURN_RES2 RES_RES2_RETURN_RES
      RES_RETURN_RES_RES2 length_C_nempty_iff
      map_fun_rel_def neq_Nil_conv
      intro!: RES_refine)

definition (in isasat_input_ops) already_propagated_unit_cls_conflict
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls_conflict = (\<lambda>L ((M, N, D, NE, UE, Q, WS), OC).
     ((M, N, D, add_mset {#L#} NE, UE, {#}, WS), OC))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_conflict_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_conflict_heur = (\<lambda>L (M, N, D, Q, oth).
     RETURN (M, N, D, {#}, oth))\<close>

lemma already_propagated_unit_cls_conflict_heur_already_propagated_unit_cls_conflict:
  \<open>(uncurry already_propagated_unit_cls_conflict_heur,
     uncurry (RETURN oo already_propagated_unit_cls_conflict)) \<in>
   Id \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def already_propagated_unit_cls_conflict_heur_def
      already_propagated_unit_cls_conflict_def
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_conflict_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def isasat_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) already_propagated_unit_cls_conflict_code
   uses isasat_input_bounded.already_propagated_unit_cls_conflict_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_conflict_code_def

lemmas already_propagated_unit_cls_conflict_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma already_propagated_unit_cls_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry already_propagated_unit_cls_conflict_code,
      uncurry (RETURN \<circ>\<circ> already_propagated_unit_cls_conflict))
  \<in> unat_lit_assn\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
  using already_propagated_unit_cls_conflict_heur_hnr
    [FCOMP already_propagated_unit_cls_conflict_heur_already_propagated_unit_cls_conflict]
  unfolding twl_st_init_assn_def[symmetric] by simp

definition (in -) set_conflict_empty :: \<open>nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_empty _ = Some {#}\<close>

definition (in -) lookup_set_conflict_empty :: \<open>conflict_option_rel \<Rightarrow> conflict_option_rel\<close> where
\<open>lookup_set_conflict_empty  = (\<lambda>(b, s) . (False, s))\<close>

lemma lookup_set_conflict_empty_set_conflict_empty:
  \<open>(RETURN o lookup_set_conflict_empty, RETURN o set_conflict_empty) \<in>
     [\<lambda>D. D = None]\<^sub>f option_lookup_clause_rel \<rightarrow> \<langle>option_lookup_clause_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: set_conflict_empty_def
      lookup_set_conflict_empty_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

sepref_definition (in -) set_conflict_empty_code
  is \<open>RETURN o lookup_set_conflict_empty\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d  \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding lookup_set_conflict_empty_def
  by sepref

lemma set_conflict_empty_hnr[sepref_fr_rules]:
  \<open>(set_conflict_empty_code, RETURN \<circ> set_conflict_empty)
   \<in> [\<lambda>x. x = None]\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> option_lookup_clause_assn\<close>
  using set_conflict_empty_code.refine[FCOMP lookup_set_conflict_empty_set_conflict_empty]
  unfolding option_lookup_clause_assn_def .

definition (in isasat_input_ops) set_empty_clause_as_conflict_heur
   :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>set_empty_clause_as_conflict_heur = (\<lambda> (M, N, D, Q, WS).
     RETURN (M, N, set_conflict_empty D, {#}, WS))\<close>

lemma set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict:
  \<open>(set_empty_clause_as_conflict_heur, RETURN o add_empty_conflict_init_wl) \<in>
   twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: set_empty_clause_as_conflict_heur_def add_empty_conflict_init_wl_def
      twl_st_heur_init_def set_conflict_empty_def)

sepref_thm set_empty_clause_as_conflict_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>[\<lambda>S. get_conflict_wl_heur_init S = None]\<^sub>a isasat_init_assn\<^sup>d \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_assn_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) set_empty_clause_as_conflict_code
   uses isasat_input_bounded.set_empty_clause_as_conflict_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) set_empty_clause_as_conflict_code_def

lemmas set_empty_clause_as_conflict_heur_hnr[sepref_fr_rules] =
   set_empty_clause_as_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem set_empty_clause_as_conflict_hnr[sepref_fr_rules]:
  \<open>(set_empty_clause_as_conflict_code, RETURN o add_empty_conflict_init_wl)
    \<in> [\<lambda>S. get_conflict_wl (fst S) = None]\<^sub>a twl_st_init_assn\<^sup>d  \<rightarrow> twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur_init (\<lambda>_. True)
     (\<lambda>_ S.
         get_conflict_wl_heur_init S =
         None)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    (isasat_init_assn\<^sup>d)
                    twl_st_heur_init \<rightarrow> hr_comp
                    isasat_init_assn
                    twl_st_heur_init\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_empty_clause_as_conflict_heur_hnr
    set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_init_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition (in -) add_clause_to_others_heur
   :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_clause_to_others_heur = (\<lambda> _ (M, N, D, Q, WS).
      RETURN (M, N, D, Q, WS))\<close>

lemma add_clause_to_others_heur_add_clause_to_others:
  \<open>(uncurry add_clause_to_others_heur, uncurry (RETURN oo add_to_other_init)) \<in>
   \<langle>Id\<rangle>list_rel \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: add_clause_to_others_heur_def add_to_other_init.simps
      twl_st_heur_init_def)

sepref_thm add_clause_to_others_code
  is \<open>uncurry add_clause_to_others_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_clause_to_others_heur_def isasat_init_assn_def
  by sepref

concrete_definition (in -) add_clause_to_others_code
   uses isasat_input_bounded.add_clause_to_others_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) add_clause_to_others_code_def

lemmas add_clause_to_others_heur_hnr[sepref_fr_rules] =
   add_clause_to_others_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma add_clause_to_others_hnr[sepref_fr_rules]:
  \<open>(uncurry add_clause_to_others_code, uncurry (RETURN \<circ>\<circ> add_to_other_init))
   \<in> (list_assn unat_lit_assn)\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
  using add_clause_to_others_heur_hnr[FCOMP add_clause_to_others_heur_add_clause_to_others,
  unfolded twl_st_init_assn_def[symmetric]] .

definition (in -)list_length_1 where
  [simp]: \<open>list_length_1 C \<longleftrightarrow> length C = 1\<close>

definition (in -)list_length_1_code where
  \<open>list_length_1_code C \<longleftrightarrow> (case C of [_] \<Rightarrow> True | _ \<Rightarrow> False)\<close>

lemma (in -)list_length_1_hnr[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R \<close>
  shows \<open>(return o list_length_1_code, RETURN o list_length_1) \<in> (list_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
proof -
  obtain R' where
     \<open>R' = the_pure R\<close> and
     R_R': \<open>R = pure R'\<close>
    using assms by fastforce
  show ?thesis
    unfolding R_R' list_assn_pure_conv
    by (sepref_to_hoare)
       (sep_auto simp: list_length_1_code_def list_rel_def list_all2_lengthD[symmetric]
        split: list.splits)
qed

definition (in isasat_input_ops) init_dt_step_wl_heur
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> (twl_st_wl_heur_init) nres\<close>
where
  \<open>init_dt_step_wl_heur C S = do {
     if get_conflict_wl_heur_init S = None
     then do {
         if is_Nil C
         then set_empty_clause_as_conflict_heur S
         else if list_length_1 C
         then do {
           ASSERT (C \<noteq> []);
           let L = hd C;
           ASSERT(L \<in> snd ` D\<^sub>0);
           let val_L = polarity (get_trail_wl_heur_init S) L;
           if val_L = None
           then do { (propagate_unit_cls_heur L S)}
           else
             if val_L = Some True
             then do { (already_propagated_unit_cls_heur C S)}
             else do { (conflict_propagated_unit_cls_heur L S)}
           }
         else do {
          ASSERT(length C \<ge> 2);
          ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
          ASSERT(nat_of_lit (hd C) < length (get_watched_list_heur_init S));
          ASSERT(nat_of_lit (hd (tl C)) < length (get_watched_list_heur_init S));
          add_init_cls_heur C S}}
     else add_clause_to_others_heur C S
  }\<close>

named_theorems twl_st_heur_init
lemma [twl_st_heur_init]:
  assumes \<open>(S, T) \<in>  twl_st_heur_init\<close>
  shows \<open>get_trail_init_wl T = get_trail_wl_heur_init S\<close>
  using assms
  by (cases S; auto simp: twl_st_heur_init_def; fail)+

find_theorems get_trail_wl_heur_init get_trail_init_wl
lemma init_dt_step_wl_heur_init_dt_step_wl:
  \<open>(uncurry init_dt_step_wl_heur, uncurry init_dt_step_wl) \<in>
   [\<lambda>(C, S). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> distinct C]\<^sub>f
      Id \<times>\<^sub>f twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_step_wl_heur_def init_dt_step_wl_def uncurry_def
    option.case_eq_if
  supply RETURN_as_SPEC_refine[refine2 del]
  apply (intro frefI nres_relI)
  apply (refine_vcg
      set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict[THEN fref_to_Down,
        unfolded comp_def]
      propagate_unit_cls_heur_propagate_unit_cls[THEN fref_to_Down_curry, unfolded comp_def]
      already_propagated_unit_cls_heur_already_propagated_unit_cls[THEN fref_to_Down_curry,
        unfolded comp_def]
      conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls[THEN fref_to_Down_curry,
        unfolded comp_def]
      add_init_cls_heur_add_init_cls[THEN fref_to_Down_curry,
        unfolded comp_def]
      add_clause_to_others_heur_add_clause_to_others[THEN fref_to_Down_curry,
        unfolded comp_def])
  subgoal by (auto simp: twl_st_heur_init_def)
  subgoal by (auto simp: twl_st_heur_init_def is_Nil_def split: list.splits)
  subgoal by simp
  subgoal by auto
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset split: list.splits)
  subgoal by (auto simp: polarity_def twl_st_heur_init_def split: list.splits)
  subgoal by (auto simp: twl_st_heur_init_def)
  subgoal by (auto simp: twl_st_heur_init_def)
  subgoal by (auto simp: twl_st_heur_init_def)
  subgoal by (auto simp add: twl_st_heur_init polarity_def)
  subgoal by simp
  subgoal by (auto simp: list_mset_rel_def br_def)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal
    by (auto simp: twl_st_heur_init_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
        split: list.splits)
  subgoal by simp
  subgoal
    by (auto simp: twl_st_heur_init_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
      split: list.splits)
  subgoal for x y x1 x2 C x2a
    by (cases C; cases \<open>tl C\<close>)
      (auto simp: twl_st_heur_init_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
        split: list.splits)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  done

definition get_conflict_wl_is_None_init :: \<open>nat twl_st_wl_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_init = (\<lambda>((M, N, D, NE, UE, Q, W), OC). is_None D)\<close>

definition (in -) get_conflict_wl_is_None_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur_init = (\<lambda>(M, N, D, Q, W, _). is_None D)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None_init ) \<in>
    twl_st_heur_init \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_init_def get_conflict_wl_is_None_heur_init_def
      get_conflict_wl_is_None_init_def split: option.splits)

definition (in -) get_conflict_wl_is_None_init where
  \<open>get_conflict_wl_is_None_init = get_conflict_wl_is_None\<close>

sepref_thm get_conflict_wl_is_None_init_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_def isasat_init_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_init_code
   uses isasat_input_bounded.get_conflict_wl_is_None_init_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_init_code_def

lemmas get_conflict_wl_is_None_init_code_hnr[sepref_fr_rules] =
   get_conflict_wl_is_None_init_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma get_conflict_wl_is_None_code_get_conflict_wl_is_None_no_lvls[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_init_code, RETURN o get_conflict_wl_is_None_init) \<in>
     twl_st_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_init_code_hnr[FCOMP get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init]
  unfolding twl_st_init_assn_def get_conflict_wl_is_None_init_def
  by fast

definition polarity_st_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _ \<Rightarrow> bool option\<close> where
  \<open>polarity_st_heur_init = (\<lambda>(M, _) L. polarity M L)\<close>

sepref_thm polarity_st_heur_init_code
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>a isasat_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_init_code
   uses isasat_input_bounded.polarity_st_heur_init_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_init_code_def

lemmas polarity_st_heur_init_hr[sepref_fr_rules] =
   polarity_st_heur_init_code.refine[OF isasat_input_bounded_axioms]

definition polarity_st_init :: \<open>'v twl_st_wl_init \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st_init S = polarity (get_trail_wl (fst S))\<close>

lemma get_conflict_wl_is_None_init:
   \<open>get_conflict_wl (fst S) = None \<longleftrightarrow> get_conflict_wl_is_None_init S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_init_def split: option.splits)

lemma is_Nil_hnr[sepref_fr_rules]:
 \<open>(return o is_Nil, RETURN o is_Nil) \<in> (list_assn R)\<^sup>k\<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto split: list.splits)

(* TODO Move *)
lemma get_conflict_wl_is_None_heur_init_alt_def:
  \<open>get_conflict_wl_is_None_heur_init S \<longleftrightarrow> get_conflict_wl_heur_init S = None\<close>
  by (auto simp: get_conflict_wl_is_None_heur_init_def split: option.splits)

lemma polarity_st_heur_init_alt_def:
  \<open>polarity_st_heur_init S L = polarity (get_trail_wl_heur_init S) L\<close>
  by (cases S) (auto simp: polarity_st_heur_init_def)

(* End Move *)

sepref_register (in isasat_input_ops) init_dt_step_wl
  get_conflict_wl_is_None_heur_init already_propagated_unit_cls_heur
  conflict_propagated_unit_cls_heur add_clause_to_others_heur
  add_init_cls_heur set_empty_clause_as_conflict_heur

sepref_register polarity_st_heur_init propagate_unit_cls_heur

sepref_thm init_dt_step_wl_code
  is \<open>uncurry (PR_CONST init_dt_step_wl_heur)\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a
       isasat_init_assn\<close>
  supply polarity_None_undefined_lit[simp] polarity_st_init_def[simp]
  option.splits[split] get_conflict_wl_is_None_heur_init_alt_def[simp]
  tri_bool_eq_def[simp]
  unfolding init_dt_step_wl_heur_def lms_fold_custom_empty PR_CONST_def
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding
    cons_trail_Propagated_def[symmetric] get_conflict_wl_is_None_init
    polarity_st_heur_init_alt_def[symmetric]
    get_conflict_wl_is_None_heur_init_alt_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] UNSET_def[symmetric]
    tri_bool_eq_def[symmetric]
  by sepref

concrete_definition (in -) init_dt_step_wl_code
  uses "isasat_input_bounded.init_dt_step_wl_code.refine_raw"
  is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) init_dt_step_wl_code_def

lemmas init_dt_step_wl_code_refine[sepref_fr_rules] =
  init_dt_step_wl_code.refine[OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) init_dt_wl_heur
 :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> (twl_st_wl_heur_init) nres\<close>
where
  \<open>init_dt_wl_heur CS S = nfoldli CS (\<lambda>_. True) (init_dt_step_wl_heur) S\<close>

sepref_register (in isasat_input_ops) init_dt_wl_heur

end

definition nat_lit_list_hm_ref_rel :: \<open>(('a set \<times> 'a list) \<times> 'a list) set\<close> where
  \<open>nat_lit_list_hm_ref_rel = {((s, xs), l). l = xs \<and> s = set l}\<close>

abbreviation nat_lit_lits_init_ref_assn where
  \<open>nat_lit_lits_init_ref_assn \<equiv> hs.assn uint32_nat_assn *a list_assn uint32_nat_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp nat_lit_lits_init_ref_assn nat_lit_list_hm_ref_rel\<close>

definition in_map_atm_of :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>in_map_atm_of L N \<longleftrightarrow> L \<in> set N\<close>

sepref_definition nat_lit_lits_init_assn_assn_in
  is \<open>uncurry (RETURN oo (\<lambda>L (s, xs). L \<in> s))\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_lits_init_ref_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref

lemma nat_lit_lits_init_assn_ref_in:
  \<open>(uncurry (RETURN oo (\<lambda>L (s, xs). L \<in> s)), uncurry (RETURN oo in_map_atm_of)) \<in>
    nat_rel \<times>\<^sub>r nat_lit_list_hm_ref_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def in_map_atm_of_def)

sepref_definition nat_lit_lits_init_assn_assn_prepend
  is \<open>uncurry (RETURN oo (\<lambda>L (s, xs). (insert L s, L # xs)))\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_lits_init_ref_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_lits_init_ref_assn\<close>
  by sepref

lemma nat_lit_lits_init_assn_ref_list_prepend:
  \<open>(uncurry (RETURN oo (\<lambda>L (s, xs). (insert L s, L # xs))),
      uncurry (RETURN oo op_list_prepend)) \<in>
    Id \<times>\<^sub>r nat_lit_list_hm_ref_rel \<rightarrow>\<^sub>f \<langle>nat_lit_list_hm_ref_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def in_map_atm_of_def)

lemma nat_lit_lits_init_assn_assn_prepend[sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_prepend, uncurry (RETURN \<circ>\<circ> op_list_prepend))
      \<in> uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using nat_lit_lits_init_assn_assn_prepend.refine[FCOMP nat_lit_lits_init_assn_ref_list_prepend] .

lemma nat_lit_lits_init_assn_assn_id[sepref_fr_rules]:
  \<open>(return o snd, RETURN o id) \<in> nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a list_assn uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_lit_list_hm_ref_rel_def hr_comp_def)

lemma in_map_atm_of_hnr[sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in, uncurry (RETURN \<circ>\<circ> in_map_atm_of))
     \<in> uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using nat_lit_lits_init_assn_assn_in.refine[FCOMP nat_lit_lits_init_assn_ref_in] .


definition extract_atms_cls :: \<open>'a clause_l \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = fold (\<lambda>L \<A>\<^sub>i\<^sub>n. if atm_of L \<in> set \<A>\<^sub>i\<^sub>n then \<A>\<^sub>i\<^sub>n else atm_of L # \<A>\<^sub>i\<^sub>n) C \<A>\<^sub>i\<^sub>n\<close>

sepref_definition extract_atms_cls_imp
  is \<open>uncurry (RETURN oo extract_atms_cls)\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_cls_def in_map_atm_of_def[symmetric]
  by sepref

declare extract_atms_cls_imp.refine[sepref_fr_rules]

definition extract_atms_clss:: \<open>'a clause_l list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>  where
  \<open>extract_atms_clss N \<A>\<^sub>i\<^sub>n = fold extract_atms_cls N \<A>\<^sub>i\<^sub>n\<close>

sepref_definition extract_atms_clss_imp
  is \<open>uncurry (RETURN oo extract_atms_clss)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_clss_def in_map_atm_of_def[symmetric]
  by sepref

lemma id_extract_atms_clss: \<open>extract_atms_clss = (\<lambda>a b. id (extract_atms_clss a b))\<close>
  by auto

sepref_definition extract_atms_clss_imp_list_assn
  is \<open>uncurry (RETURN oo extract_atms_clss)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a list_assn uint32_nat_assn\<close>
  supply extract_atms_clss_imp.refine[sepref_fr_rules]
  apply (rewrite at \<open>extract_atms_clss\<close> id_extract_atms_clss)
  by sepref

definition op_extract_list_empty where
  \<open>op_extract_list_empty = []\<close>

lemma extract_atms_clss_imp_empty_rel:
  \<open>(uncurry0 (RETURN ({}, [])), uncurry0 (RETURN op_extract_list_empty)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_list_hm_ref_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def op_extract_list_empty_def)

sepref_definition extract_atms_clss_imp_empty_assn
  is \<open>uncurry0 (RETURN ({}, []))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_lits_init_ref_assn\<close>
  unfolding hs.fold_custom_empty HOL_list.fold_custom_empty
  by sepref

lemma extract_atms_clss_imp_empty_assn[sepref_fr_rules]:
  \<open>(uncurry0 extract_atms_clss_imp_empty_assn, uncurry0 (RETURN op_extract_list_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp_empty_assn.refine[FCOMP extract_atms_clss_imp_empty_rel] .

declare extract_atms_clss_imp_list_assn.refine[sepref_fr_rules]
declare atm_of_hnr[sepref_fr_rules]

lemma extract_atms_cls_Cons:
  \<open>extract_atms_cls (L # C) \<A>\<^sub>i\<^sub>n = extract_atms_cls C (if atm_of L \<in> set \<A>\<^sub>i\<^sub>n then \<A>\<^sub>i\<^sub>n else atm_of L # \<A>\<^sub>i\<^sub>n)\<close>
  unfolding extract_atms_cls_def fold.simps by simp

lemma extract_atms_cls_Nil[simp]:
  \<open>extract_atms_cls [] \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n\<close>
  unfolding extract_atms_cls_def fold.simps by simp

lemma extract_atms_clss_Cons[simp]:
  \<open>extract_atms_clss (C # Cs) N = extract_atms_clss Cs (extract_atms_cls C N)\<close>
  by (simp add: extract_atms_clss_def)

lemma distinct_extract_atms_cls: \<open>distinct (extract_atms_cls x N) \<longleftrightarrow> distinct N\<close>
  apply (induction x arbitrary: N)
  subgoal by (auto simp: extract_atms_clss_def)
  subgoal premises p for a x N
    using p by (auto simp: extract_atms_cls_Cons)
  done

lemma distinct_extract_atms_clss: \<open>distinct (extract_atms_clss x N) \<longleftrightarrow> distinct N\<close>
  apply (induction x arbitrary: N)
  subgoal by (auto simp: extract_atms_clss_def)
  subgoal premises p for a x N
    using p by (auto simp: distinct_extract_atms_cls)
  done

definition (in -) all_lits_of_atms_m :: \<open>'a multiset \<Rightarrow> 'a clause\<close> where
 \<open>all_lits_of_atms_m N = poss N + negs N\<close>

lemma (in -) all_lits_of_atms_m_nil[simp]: \<open>all_lits_of_atms_m {#} = {#}\<close>
  unfolding all_lits_of_atms_m_def by auto

definition (in -) all_lits_of_atms_mm :: \<open>'a multiset multiset \<Rightarrow> 'a clause\<close> where
 \<open>all_lits_of_atms_mm N = poss (\<Union># N) + negs (\<Union># N)\<close>

lemma all_lits_of_atms_m_all_lits_of_m:
  \<open>all_lits_of_atms_m N = all_lits_of_m (poss N)\<close>
  unfolding all_lits_of_atms_m_def all_lits_of_m_def
  by (induction N) auto

lemma in_extract_atms_clsD:
  \<open>set (extract_atms_cls C \<A>\<^sub>i\<^sub>n) = atms_of_s (set C) \<union> set \<A>\<^sub>i\<^sub>n\<close>
  apply (induction C arbitrary: \<A>\<^sub>i\<^sub>n)
  subgoal by auto
  subgoal premises IH for L' C \<A>\<^sub>i\<^sub>n
    using IH(1)[of \<open>(if atm_of L' \<in> set \<A>\<^sub>i\<^sub>n then \<A>\<^sub>i\<^sub>n else atm_of L' # \<A>\<^sub>i\<^sub>n)\<close>]
    by (auto simp: extract_atms_cls_def split: if_splits)
  done

lemma in_extract_atms_clssD:
  fixes \<A>\<^sub>i\<^sub>n :: \<open>'a list\<close>
  shows
    \<open>set (extract_atms_clss C \<A>\<^sub>i\<^sub>n) = atms_of_s (\<Union>(set`set C)) \<union> set \<A>\<^sub>i\<^sub>n\<close>
  apply (induction C arbitrary: \<A>\<^sub>i\<^sub>n)
  subgoal by (auto simp: extract_atms_clss_def)
  subgoal premises IH for L' C \<A>\<^sub>i\<^sub>n
    using IH(1)[of \<open>extract_atms_cls L' \<A>\<^sub>i\<^sub>n\<close>]
    by (auto simp: extract_atms_clss_def in_extract_atms_clsD split: if_splits)
  done


context isasat_input_bounded
begin

fun (in isasat_input_ops) correct_watching_init :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_init (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_atms_m \<A>\<^sub>i\<^sub>n. mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>


definition (in isasat_input_ops) init_dt_wl_heur_spec
  :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> bool\<close>
where
  \<open>init_dt_wl_heur_spec CS T TOC \<longleftrightarrow>
    (\<exists>T' TOC'. (TOC, TOC') \<in> twl_st_heur_init \<and> (T, T') \<in> twl_st_heur_init \<and>
        init_dt_wl_spec CS T' TOC')\<close>

definition (in isasat_input_ops) init_state :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset\<close> where
  \<open>init_state N = (
    let _ = \<A>\<^sub>i\<^sub>n in
    ([]:: (nat, nat clause) ann_lits), (N :: nat clauses), ({#}::nat clauses),
      (None :: nat clause option))\<close>

text \<open>We add a spurious dependency to the parameter of the locale:\<close>
definition (in isasat_input_ops) empty_watched :: \<open>nat literal \<Rightarrow> nat list\<close> where
  \<open>empty_watched = (let _ = \<A>\<^sub>i\<^sub>n in (\<lambda>_. []))\<close>

lemma (in isasat_input_ops) empty_watched_alt_def:
  \<open>empty_watched = (\<lambda>_. [])\<close>
  unfolding empty_watched_def Let_def ..

definition (in isasat_input_ops) init_state_wl :: \<open>nat twl_st_wl\<close> where
  \<open>init_state_wl = ([], fmempty, None, {#}, {#}, {#}, empty_watched)\<close>

definition (in isasat_input_ops) init_state_wl_heur :: \<open>twl_st_wl_heur_init nres\<close> where
  \<open>init_state_wl_heur = do {
    W \<leftarrow> SPEC (\<lambda>W. (W, empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0);
    vm \<leftarrow> RES (vmtf_init []);
    \<phi> \<leftarrow> SPEC phase_saving;
    cach \<leftarrow> SPEC cach_refinement_empty;
    let lbd = empty_lbd;
    RETURN ([], fmempty, None, {#}, W, vm, \<phi>, zero_uint32_nat, cach, lbd)}\<close>


definition (in isasat_input_ops) twl_st_heur_init_wl :: \<open>(twl_st_wl_heur_init \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_init_wl =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd), (M, N, D, NE, UE, Q, W)).
    M' = M \<and> N' = N \<and>
    D' = D \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach
  }\<close>

lemma (in isasat_input_ops) init_state_wl_heur_init_state_wl:
  \<open>(uncurry0 init_state_wl_heur, uncurry0 (RETURN init_state_wl)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>twl_st_heur_init_wl\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
      (auto simp: init_state_wl_heur_def init_state_wl_def
        RES_RETURN_RES bind_RES_RETURN_eq RES_RES_RETURN_RES RETURN_def
        twl_st_heur_init_wl_def
        intro!: RES_refine)

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_init_wl \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_init_wl_def
      get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_def
      split: option.splits)

definition (in isasat_input_ops) twl_st_init_wl_assn
where
  \<open>twl_st_init_wl_assn = hr_comp isasat_init_assn twl_st_heur_init_wl\<close>

lemma get_conflict_wl_is_None_init_wl_hnr[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_init_code, RETURN \<circ> get_conflict_wl_is_None)
    \<in> twl_st_init_wl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_init_code_hnr[FCOMP get_conflict_wl_is_None_heur_get_conflict_wl_is_None]
  unfolding isasat_init_assn_def[symmetric]twl_st_init_wl_assn_def[symmetric]
  .

end


definition (in -)to_init_state :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl_init\<close> where
  \<open>to_init_state S = (S, {#})\<close>

definition (in -) from_init_state :: \<open>nat twl_st_wl_init \<Rightarrow> nat twl_st_wl\<close> where
  \<open>from_init_state = fst\<close>

lemma (in isasat_input_ops) id_to_init_state:
  \<open>(RETURN o id, RETURN o to_init_state) \<in> twl_st_heur_init_wl \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: to_init_state_def twl_st_heur_init_wl_def
      twl_st_heur_init_def)

definition to_init_state_code where
  \<open>to_init_state_code = id\<close>

lemma (in isasat_input_ops) to_init_state_code_hnr:
  \<open>(return o to_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding to_init_state_code_def
  by (rule id_ref)


lemma (in isasat_input_ops) to_init_state_hnr[sepref_fr_rules]:
 \<open>(return \<circ> to_init_state_code, RETURN \<circ> to_init_state) \<in>
   twl_st_init_wl_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
  using to_init_state_code_hnr[FCOMP id_to_init_state]
  unfolding twl_st_init_wl_assn_def twl_st_init_assn_def .

lemma (in isasat_input_ops) id_from_init_state:
  \<open>(RETURN o id, RETURN o from_init_state) \<in> twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init_wl\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: from_init_state_def twl_st_heur_init_wl_def
      twl_st_heur_init_def)

definition from_init_state_code where
  \<open>from_init_state_code = id\<close>

lemma (in isasat_input_ops) from_init_state_code_hnr:
  \<open>(return o from_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding from_init_state_code_def
  by (rule id_ref)

lemma (in isasat_input_ops) from_init_state_hnr[sepref_fr_rules]:
 \<open>(return \<circ> from_init_state_code, RETURN \<circ> from_init_state) \<in>
   twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_wl_assn\<close>
  using from_init_state_code_hnr[FCOMP id_from_init_state]
  unfolding twl_st_init_wl_assn_def twl_st_init_assn_def .

definition conflict_is_None_heur_wl where
  \<open>conflict_is_None_heur_wl = (\<lambda>(M, N, U, D, _). is_None D)\<close>


definition initialise_VMTF :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> vmtf_remove_int_option_fst_As nres\<close> where
\<open>initialise_VMTF N n = do {
   let A = replicate n (VMTF_Node 0 None None);
   (_, A, n, cnext) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(N, A, st, cnext). N \<noteq> [])
      (\<lambda>(N, A, st, cnext). do {
        ASSERT(N \<noteq> []);
        let L = nat_of_uint32 (hd N);
        ASSERT(L < length A);
        ASSERT(cnext \<noteq> None \<longrightarrow> the cnext < length A);
        RETURN (tl N, vmtf_cons A L cnext st, st+1, Some L)
      })
      (N, A, 0::nat, None);
   RETURN ((A, n, cnext, (if N = [] then None else Some (nat_of_uint32 (hd N))), cnext), [])
  }\<close>

sepref_definition initialise_VMTF_code
  is \<open>uncurry initialise_VMTF\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_remove_conc_option_fst_As\<close>
  supply nat_of_uint32_int32_assn[sepref_fr_rules]
  unfolding initialise_VMTF_def vmtf_cons_def
  apply (rewrite in \<open>((_, _, _, _), \<hole>)\<close> annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>(_, _, _, Some \<hole>)\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>WHILE\<^sub>T _ _ (_, _, _, \<hole>)\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>do {ASSERT _; let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>((_, _, _, _), ASSN_ANNOT _ \<hole>)\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _ \<close> array_fold_custom_replicate op_list_replicate_def[symmetric])
  apply (rewrite in \<open>VMTF_Node 0 \<hole> _\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>VMTF_Node 0 _ \<hole>\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

declare initialise_VMTF_code.refine[sepref_fr_rules]


lemma initialise_VMTF:
  shows \<open>(uncurry initialise_VMTF, uncurry (\<lambda>N n. RES (isasat_input_ops.vmtf_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N)]\<^sub>f
      (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow>
      \<langle>(\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel)
        \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
proof -
  have vmtf_ns_notin_empty: \<open>vmtf_ns_notin [] 0 (replicate n (VMTF_Node 0 None None))\<close> for n
    unfolding vmtf_ns_notin_def
    by auto

  have K2: \<open>distinct N \<Longrightarrow> fst_As < length N \<Longrightarrow> N!fst_As \<in> set (take fst_As N) \<Longrightarrow> False\<close>
    for fst_As x N
    by (metis (no_types, lifting) in_set_conv_nth length_take less_not_refl min_less_iff_conj
      nth_eq_iff_index_eq nth_take)
  have W_ref: \<open>WHILE\<^sub>T (\<lambda>(N, A, st, cnext). N \<noteq> [])
        (\<lambda>(N, A, st, cnext).
            ASSERT (N \<noteq> []) \<bind>
            (\<lambda>_. ASSERT (nat_of_uint32 (hd N) < length A) \<bind>
                 (\<lambda>_. ASSERT (cnext \<noteq> None \<longrightarrow> the cnext < length A) \<bind>
                      (\<lambda>_. RETURN
                            (tl N, vmtf_cons A (nat_of_uint32 (hd N)) cnext st,
                             st + 1, Some (nat_of_uint32 (hd N)))))))
        (N', replicate n' (VMTF_Node 0 None None), 0, None)
    \<le> SPEC(\<lambda>(N'', A', st, cnext).
      vmtf_ns (rev (map (nat_of_uint32) (take (length N' - length N'') N'))) st A'
      \<and> cnext = map_option (nat_of_uint32) (option_last (take (length N' - length N'') N')) \<and>
    N'' = drop st N' \<and> length N'' \<le> length N' \<and> st \<le> length N' \<and>
    length A' = n \<and> N'' = [] \<and> vmtf_ns_notin (rev (map (nat_of_uint32) (take (length N' - length N'') N'))) st A'
      )\<close>
    if L_N: \<open>\<forall>L\<in># N. L < n\<close> and
       dist: \<open>distinct_mset N\<close> and
       ref: \<open>((N', n'), N, n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<times>\<^sub>f nat_rel\<close>
     for N N' n n'
  proof -
  have [simp]: \<open>n = n'\<close> and NN': \<open>(N', N) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    using ref by auto
  have \<open>inj_on nat_of_uint32 S\<close> for S
    by (auto simp: inj_on_def)
  then have dist: \<open>distinct N'\<close>
    using NN' dist by (auto simp: list_rel_def uint32_nat_rel_def br_def list_mset_rel_def
      list_all2_op_eq_map_right_iff' distinct_image_mset_inj list_rel_mset_rel_def)
  have L_N: \<open>\<forall>L\<in>set N'. nat_of_uint32 L < n\<close>
    using L_N ref by (auto simp: list_rel_def uint32_nat_rel_def br_def list_mset_rel_def
      list_all2_op_eq_map_right_iff' list_rel_mset_rel_def)

  show ?thesis
    apply (refine_rcg WHILET_rule[where R = \<open>measure (\<lambda>(N', _). length N')\<close> and
     I = \<open>\<lambda>(N'', A', st, cnext). vmtf_ns (rev (map (nat_of_uint32) (take (length N' - length N'') N'))) st A'
      \<and> cnext = map_option (nat_of_uint32) (option_last (take (length N' - length N'') N')) \<and>
    N'' = drop st N' \<and> length N'' \<le> length N' \<and> st \<le> length N' \<and> (N'' \<noteq> [] \<longrightarrow> st < length N') \<and>
    length A' = n \<and> vmtf_ns_notin (rev (map (nat_of_uint32) (take (length N' - length N'') N'))) st A'\<close>])
    subgoal by auto
    subgoal by (auto intro: vmtf_ns.intros)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: vmtf_ns_notin_empty)
    subgoal for S N' x2 A' x2a fst_As cnext
      unfolding assert_bind_spec_conv
      apply (intro conjI)
      subgoal
        using L_N dist
        by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
            option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
      subgoal
        using L_N dist
        by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
            option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
      subgoal (*TODO tune proof*)
        using L_N dist List.last_in_set[of \<open>take fst_As N'\<close>] set_take_subset[of fst_As N']
        apply (auto simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
            option_last_def hd_rev last_map)
        by (metis List.last_in_set diff_le_self diff_less_mono2 vmtf_ns_le_length last_map
          le_eq_less_or_eq len_greater_imp_nonempty length_drop length_rev list.map_disc_iff
          rev_take set_rev)
      subgoal
        apply (rule RETURN_rule)
        apply (clarify intro!: RETURN_rule)
        apply (intro conjI)
        subgoal
          using L_N dist
          by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
              option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
        subgoal
          using L_N dist
          by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
              option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
        subgoal by (auto simp: drop_Suc tl_drop)
        subgoal by auto
        subgoal by auto
        subgoal by (auto simp: tl_drop)
        subgoal by auto
        subgoal
          using L_N dist
          by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
              option_last_def hd_rev last_map intro!: vmtf_notin_vmtf_cons dest: K2)
        subgoal
          using L_N dist
          by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
              option_last_def hd_rev last_map intro!: vmtf_notin_vmtf_cons dest: K2)
        done
      done
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
  have [simp]: \<open>isasat_input_ops.vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l N [] ((nat_of_uint32 ` set N', {}), {})\<close>
    if \<open>(N', y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel\<close> and \<open>(y, N) \<in> list_mset_rel\<close> for N N' y
    using that unfolding isasat_input_ops.vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
      uint32_nat_rel_def br_def list_mset_rel_def list_all2_op_eq_map_right_iff')
  have in_N_in_N1: \<open>L \<in> set N' \<Longrightarrow>  nat_of_uint32 L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l N)\<close>
    if \<open>(N', y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel\<close> and \<open>(y, N) \<in> list_mset_rel\<close> for L N N' y
    using that by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
      uint32_nat_rel_def br_def list_mset_rel_def list_all2_op_eq_map_right_iff')

  have length_ba: \<open>\<forall>L\<in># N. L < length ba \<Longrightarrow> L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l N) \<Longrightarrow>
     L < length ba\<close>
    if \<open>(N', y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel\<close> and \<open>(y, N) \<in> list_mset_rel\<close>
    for L ba N N' y
    using that
    by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def nat_shiftr_div2 nat_of_uint32_shiftr
      atms_of_def image_image image_Un split: if_splits)
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding initialise_VMTF_def Let_def uncurry_def conc_Id id_def isasat_input_ops.vmtf_init_def
    apply clarify
    apply (rule specify_left)
     apply (rule W_ref; assumption)
    subgoal for N' n' N n st
      apply (case_tac st)
      apply clarify
      apply (subst RETURN_RES_refine_iff)
      apply (unfold isasat_input_ops.vmtf_def)
      apply (clarsimp)
      apply (intro conjI impI)
      subgoal N' by (auto simp: list_rel_mset_rel_def br_def list_mset_rel_def)
      subgoal
        apply (rule exI[of _ \<open>map nat_of_uint32 (rev N')\<close>])
        apply (rule_tac exI[of _ \<open>[]\<close>])
        apply (intro conjI)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last)
        subgoal
          by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_last_def last_map
              hd_rev list_rel_mset_rel_def br_def list_mset_rel_def)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last hd_map)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last hd_map)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last hd_rev last_map)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last list_rel_mset_rel_def)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last list_rel_mset_rel_def dest: length_ba)
        subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
              map_option_option_last list_rel_mset_rel_def dest: in_N_in_N1)
        done
      done
    done
qed

definition finalise_init where
  \<open>finalise_init = id\<close>

(* TODO Move *)
definition arl_replicate where
 "arl_replicate init_cap x \<equiv> do {
    let n = max init_cap minimum_capacity;
    a \<leftarrow> Array.new n x;
    return (a,init_cap)
  }"

definition \<open>op_arl_replicate = op_list_replicate\<close>
lemma arl_fold_custom_replicate:
  \<open>replicate = op_arl_replicate\<close>
  unfolding op_arl_replicate_def op_list_replicate_def ..

lemma list_replicate_arl_hnr[sepref_fr_rules]:
  assumes p:  \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry arl_replicate, uncurry (RETURN oo op_arl_replicate)) \<in> nat_assn\<^sup>k *\<^sub>a R\<^sup>k \<rightarrow>\<^sub>a arl_assn R\<close>
proof -
  obtain R' where
     R'[symmetric]: \<open>R' = the_pure R\<close> and
     R_R': \<open>R = pure R'\<close>
    using assms by fastforce
  have [simp]: \<open>pure R' b bi = \<up>((bi, b) \<in> R')\<close> for b bi
    by (auto simp: pure_def)
  have [simp]: \<open>min a (max a 16) = a\<close> for a :: nat
    by auto
  show ?thesis
    using assms unfolding op_arl_replicate_def
    by sepref_to_hoare
      (sep_auto simp: arl_replicate_def arl_assn_def hr_comp_def R' R_R' list_rel_def
        is_array_list_def minimum_capacity_def
        intro!: list_all2_replicate)
qed
(* End Move *)
context isasat_input_bounded
begin

sepref_register init_dt_step_wl_heur
sepref_thm init_dt_wl_code
  is \<open>uncurry (PR_CONST init_dt_wl_heur)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a
       isasat_init_assn\<close>
  unfolding init_dt_wl_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) init_dt_wl_code
  uses "isasat_input_bounded.init_dt_wl_code.refine_raw"
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) init_dt_wl_code_def

end

text \<open>The value 160 is random (but larger than the default 16 for array lists).\<close>
definition finalise_init_code :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>finalise_init_code =
    (\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls, cach,
       lbd). do {
     ASSERT(lst_As \<noteq> None \<and> fst_As \<noteq> None);
     RETURN (M', N', D', Q', W', ((ns, m, the fst_As, the lst_As, next_search), to_remove), \<phi>,
       clvls, cach, lbd, take1(replicate 160 (Pos zero_uint32_nat)),
         (0::uint64, 0::uint64, 0::uint64))
     })\<close>


lemma (in isasat_input_ops)finalise_init_finalise_init:
  \<open>(finalise_init_code, RETURN o finalise_init) \<in>
   [\<lambda>S. get_conflict_wl S = None \<and> \<A>\<^sub>i\<^sub>n \<noteq> {#}]\<^sub>f twl_st_heur_init_wl \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: finalise_init_def twl_st_heur_def twl_st_heur_init_def twl_st_heur_init_wl_def
      finalise_init_code_def vmtf_init_def out_learned_def take1_def)

(* TODO Move *)
lemma zero_uin64_hnr: \<open>(uncurry0 (return 0), uncurry0 (RETURN 0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto
(* End Move *)

sepref_thm (in isasat_input_ops) finalise_init_code'
  is \<open>finalise_init_code\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply zero_uin64_hnr[sepref_fr_rules] [[goals_limit=1]]
    Pos_unat_lit_assn'[sepref_fr_rules] uint_max_def[simp] op_arl_replicate_def[simp]
  unfolding finalise_init_code_def isasat_init_assn_def isasat_assn_def
    arl.fold_custom_empty arl_fold_custom_replicate
  by sepref


concrete_definition (in -) finalise_init_code'
   uses isasat_input_ops.finalise_init_code'.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) finalise_init_code'_def

lemmas (in isasat_input_ops)finalise_init_hnr[sepref_fr_rules] =
   finalise_init_code'.refine[of \<A>\<^sub>i\<^sub>n]

definition (in -) init_rll :: \<open>nat \<Rightarrow> (nat, 'v clause_l \<times> bool) fmap\<close> where
  \<open>init_rll n = fmempty\<close>

definition (in -) init_aa :: \<open>nat \<Rightarrow> 'v list\<close> where
  \<open>init_aa n = []\<close>


lemma (in -)arrayO_raa_empty_sz_empty_list[sepref_fr_rules]:
  \<open>(arrayO_raa_empty_sz, RETURN o init_aa) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a (arlO_assn clause_ll_assn)\<close>
  by sepref_to_hoare (sep_auto simp: init_rll_def hr_comp_def clauses_ll_assn_def init_aa_def)

definition init_rll_list where
  \<open>init_rll_list n =
    (let e = ASSN_ANNOT clause_ll_assn op_array_empty in
     let N = init_aa n in
     RETURN (N @ [e]))\<close>


lemma (in -)empty_array_init_rll:
  \<open>(init_rll_list, RETURN o init_rll) \<in>
    nat_rel\<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>clauses_l_fmat\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply  (auto simp: init_rll_def hr_comp_def clauses_ll_assn_def
    list_fmap_rel_def init_rll_list_def init_aa_def)
    apply (case_tac i)
    apply auto
  done

sepref_definition init_rll_list_code
  is \<open>init_rll_list\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arlO_assn clause_ll_assn\<close>
  unfolding init_rll_list_def
  by sepref

lemma (in -)arrayO_raa_empty_sz_init_rll[sepref_fr_rules]:
  \<open>(init_rll_list_code, RETURN o init_rll) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a clauses_ll_assn\<close>
  using init_rll_list_code.refine[FCOMP empty_array_init_rll]
  unfolding clauses_ll_assn_def[symmetric]
  by auto

definition init_lrl :: \<open>nat \<Rightarrow> 'a list list\<close> where
  \<open>init_lrl n = replicate n []\<close>

lemma arrayO_ara_empty_sz_init_lrl: \<open>arrayO_ara_empty_sz n = init_lrl n\<close>
  by (induction n) (auto simp: arrayO_ara_empty_sz_def init_lrl_def)

lemma (in -)arrayO_raa_empty_sz_init_lrl[sepref_fr_rules]:
  \<open>(arrayO_ara_empty_sz_code, RETURN o init_lrl) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl_assn R)\<close>
  using arrayO_ara_empty_sz_code.refine unfolding arrayO_ara_empty_sz_init_lrl .

definition init_trail_D :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> trail_pol nres\<close> where
  \<open>init_trail_D \<A>\<^sub>i\<^sub>n n m = do {
     let M = replicate m UNSET;
     let M' = replicate n zero_uint32_nat;
     let M'' = replicate n None;
     RETURN (([], M, M', M'', zero_uint32_nat))
  }\<close>

sepref_register initialise_VMTF


sepref_definition init_trail_D_code
  is \<open>uncurry2 init_trail_D\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding init_trail_D_def PR_CONST_def
  apply (rewrite in \<open>((\<hole>, _, _, _))\<close> HOL_list.fold_custom_empty)
  apply (rewrite in \<open>((\<hole>, _, _, _))\<close> annotate_assn[where A=\<open>list_assn unat_lit_assn\<close>])

  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_code.refine[sepref_fr_rules]

definition init_state_wl_D' :: \<open>uint32 list \<Rightarrow>  (trail_pol \<times> _ \<times> _) nres\<close> where
  \<open>init_state_wl_D' \<A>\<^sub>i\<^sub>n = do {
     let n = Suc (nat_of_uint32 (fold max \<A>\<^sub>i\<^sub>n 0));
     let m = 2 * n;
     M \<leftarrow> init_trail_D \<A>\<^sub>i\<^sub>n n m;
     let N = init_rll n;
     let D = (True, zero_uint32_nat, replicate n None);
     let WS = init_lrl m;
     vm \<leftarrow> initialise_VMTF \<A>\<^sub>i\<^sub>n n;
     let \<phi> = replicate n False;
     let cach = (replicate n SEEN_UNKNOWN, []);
     let lbd = empty_lbd;
     RETURN (M, N, D, [], WS, vm, \<phi>, zero_uint32_nat, cach, lbd)
  }\<close>


sepref_definition init_state_wl_D'_code
  is \<open>init_state_wl_D'\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn *a clauses_ll_assn *a
    conflict_option_rel_assn *a
    list_assn unat_lit_assn *a
    (arrayO_assn (arl_assn nat_assn)) *a
    vmtf_remove_conc_option_fst_As *a
    phase_saver_conc *a uint32_nat_assn *a
    cach_refinement_l_assn *a lbd_assn\<close>
  unfolding init_state_wl_D'_def
  apply (rewrite at \<open>(_, _, _, \<hole>, _, _)\<close> HOL_list.fold_custom_empty)
  apply (rewrite at \<open>(_, _, _, \<hole>, _)\<close> annotate_assn[where A=\<open>list_assn unat_lit_assn\<close>])
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> arl.fold_custom_empty)
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>clauses_ll_assn\<close>])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>(arrayO_assn (arl_assn nat_assn))\<close>])
  supply [[goals_limit = 1]]
  by sepref

lemma (in isasat_input_ops) in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n:\<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<longleftrightarrow> atm_of L \<in># \<A>\<^sub>i\<^sub>n\<close>
  by (cases L) (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma init_trail_D_ref:
  \<open>(uncurry2 init_trail_D, uncurry2 (RETURN ooo (\<lambda> _ _ _. []))) \<in> [\<lambda>((N, n), m). mset N = \<A>\<^sub>i\<^sub>n \<and>
    distinct N \<and> (\<forall>L\<in>set N. L < n) \<and> m = 2 * n]\<^sub>f
    \<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>
   \<langle>isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n\<rangle> nres_rel\<close>
proof -
  have K: \<open>(\<forall>L\<in>set N. nat_of_uint32 L < n) \<longleftrightarrow>
     (\<forall>L \<in># (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (nat_of_uint32 `# mset N)). atm_of L < n)\<close> for N n
    apply (rule iffI)
    subgoal by (auto simp: isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by (metis (full_types) image_eqI isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n literal.sel(1)
          set_image_mset set_mset_mset)
    done
  have K': \<open>(\<forall>L\<in>set N. L < n) \<Longrightarrow>
     (\<forall>L \<in># (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset N)). nat_of_lit L < 2 * n)\<close>
     (is \<open>?A \<Longrightarrow> ?B\<close>) for N n
     (*TODO proof*)
  proof -
    assume ?A
    then show ?B
      apply (auto simp: isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
      apply (case_tac L)
      apply auto
      done
  qed
  show ?thesis
    unfolding init_trail_D_def
    apply (intro frefI nres_relI)
    unfolding uncurry_def Let_def comp_def isasat_input_ops.trail_pol_def
    apply clarify
    unfolding RETURN_refine_iff
    apply clarify
    apply (intro conjI)
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    subgoal using K' by (auto simp: polarity_def)
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    done
qed


lemma init_state_wl_D':
  \<open>(init_state_wl_D', isasat_input_ops.init_state_wl_heur) \<in>
    [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>f \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel  \<rightarrow>
      \<langle>isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n \<times>\<^sub>r Id \<times>\<^sub>r
         isasat_input_ops.option_lookup_clause_rel \<A>\<^sub>i\<^sub>n \<times>\<^sub>r list_mset_rel \<times>\<^sub>r \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>r
           Id \<times>\<^sub>r \<langle>bool_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r isasat_input_ops.cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have init_state_wl_heur_alt_def: \<open>isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n = do {
    let M = [];
    let N = fmempty;
    let D = None;
    W \<leftarrow> SPEC (\<lambda>W. (W, isasat_input_ops.empty_watched \<A>\<^sub>i\<^sub>n ) \<in> \<langle>Id\<rangle>map_fun_rel (isasat_input_ops.D\<^sub>0 \<A>\<^sub>i\<^sub>n));
    vm \<leftarrow> RES (isasat_input_ops.vmtf_init \<A>\<^sub>i\<^sub>n []);
    \<phi> \<leftarrow> SPEC (isasat_input_ops.phase_saving \<A>\<^sub>i\<^sub>n);
    cach \<leftarrow> SPEC (isasat_input_ops.cach_refinement_empty \<A>\<^sub>i\<^sub>n);
    let lbd = empty_lbd;
    RETURN (M, N, D, {#}, W, vm, \<phi>, zero_uint32_nat, cach, lbd)}\<close> for \<A>\<^sub>i\<^sub>n
    unfolding isasat_input_ops.init_state_wl_heur_def Let_def by auto

  have tr: \<open>distinct_mset \<A>\<^sub>i\<^sub>n \<and> (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. L < b) \<Longrightarrow>
        (\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
     b' = 2 * b \<Longrightarrow>
      init_trail_D \<A>\<^sub>i\<^sub>n' b (2 * b) \<le> \<Down> (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) (RETURN [])\<close> for b' b \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n' x
    by (rule init_trail_D_ref[unfolded fref_def nres_rel_def, simplified, rule_format])
       (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def)
  have [simp]: \<open>comp_fun_idem (max :: 'a::linorder \<Rightarrow> _)\<close>
    unfolding comp_fun_idem_def comp_fun_commute_def comp_fun_idem_axioms_def
    by (auto simp: max_def[abs_def] intro!: ext)
  have [simp]: \<open>fold max x a = Max (insert a (set x))\<close> for x and a :: \<open>'a :: linorder\<close>
    by (auto simp: Max.eq_fold comp_fun_idem.fold_set_fold)
  have in_N0: \<open>L \<in> set \<A>\<^sub>i\<^sub>n \<Longrightarrow> nat_of_uint32 L  < Suc (nat_of_uint32 (Max (insert 0 (set \<A>\<^sub>i\<^sub>n))))\<close>
    for L \<A>\<^sub>i\<^sub>n
    using Max_ge[of \<open>insert 0 (set \<A>\<^sub>i\<^sub>n)\<close> L]
    apply (auto simp del: Max_ge simp: nat_shiftr_div2 nat_of_uint32_shiftr)
    using div_le_mono le_imp_less_Suc nat_of_uint32_le_iff by blast
  define P where \<open>P x = {(a, b). b = [] \<and> (a, b) \<in> isasat_input_ops.trail_pol x}\<close> for x
  have P: \<open>(c, []) \<in> P x \<longleftrightarrow> (c, []) \<in> isasat_input_ops.trail_pol x\<close> for c x
    unfolding P_def by auto
  have init: \<open>init_trail_D \<A>\<^sub>i\<^sub>n' (Suc (nat_of_uint32 (fold max \<A>\<^sub>i\<^sub>n' 0)))
          (2 * Suc (nat_of_uint32 (fold max \<A>\<^sub>i\<^sub>n' 0))) \<le>
     SPEC (\<lambda>c. (c, []) \<in> P \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>distinct_mset \<A>\<^sub>i\<^sub>n\<close> and x: \<open>(\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    for \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n'
    unfolding x P
    by (rule tr[unfolded conc_fun_RETURN])
       (use that in
         \<open>auto simp: shiftr1_def nat_shiftr_div2 nat_of_uint32_shiftr list_rel_mset_rel_def
            list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff' list_mset_rel_def
           dest: in_N0\<close>)

  have [simp]: \<open>([], {#}) \<in> list_mset_rel\<close>
    by (auto simp: list_mset_rel_def br_def)
  have H:
   \<open>(replicate (Suc (Suc (2 * nat_of_uint32 (Max (insert 0 (set x)))))) [],
       isasat_input_ops.empty_watched \<A>\<^sub>i\<^sub>n)
    \<in> \<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))\<close>
    if \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    for \<A>\<^sub>i\<^sub>n x
    using that unfolding map_fun_rel_def
    by (auto simp: isasat_input_ops.empty_watched_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
        list_rel_mset_rel_def list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        list_mset_rel_def
        intro!: nth_replicate dest!: in_N0
        simp del: replicate.simps)
  have initialise_VMTF: \<open>(\<forall>L\<in>#aa. L < b) \<and> distinct_mset aa \<and> (a, aa) \<in>
          \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
        initialise_VMTF a b \<le> RES (isasat_input_ops.vmtf_init aa [])\<close>
    for aa b a
    using initialise_VMTF[unfolded fref_def nres_rel_def] by auto
  have [simp]: \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow> L \<in># y \<Longrightarrow> L < Suc (nat_of_uint32 (Max (insert 0 (set x))))\<close>
    for x y L
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def uint32_nat_rel_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def dest: in_N0)

  have initialise_VMTF: \<open>initialise_VMTF x (Suc (nat_of_uint32 (fold max x 0))) \<le>
       \<Down> Id (RES (isasat_input_ops.vmtf_init y []))\<close>
    if \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close> and \<open>(M, []) \<in> P y\<close> and \<open>distinct_mset y\<close> for x y M
    using that
    by (auto simp: P_def intro!: initialise_VMTF in_N0)
  have [simp]: \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
         L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow> L < Suc (nat_of_uint32 (Max (insert 0 (set x))))\<close>
    for x L \<A>\<^sub>i\<^sub>n
    unfolding isasat_input_ops.atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def uint32_nat_rel_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def)
  have cach: \<open>RETURN (replicate (Suc (nat_of_uint32 (fold max x 0))) SEEN_UNKNOWN, [])
      \<le> \<Down> (isasat_input_ops.cach_refinement \<A>\<^sub>i\<^sub>n)
          (SPEC (isasat_input_ops.cach_refinement_empty y))\<close>
    if
      \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n\<close> and
      \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    for M W vm vma \<phi> x y
  proof -
    show ?thesis
      unfolding isasat_input_ops.cach_refinement_empty_def RETURN_RES_refine_iff
        isasat_input_ops.cach_refinement_alt_def Bex_def
      by (rule exI[of _ \<open>\<lambda>_. SEEN_UNKNOWN\<close>]) (use that in
          \<open>auto simp: map_fun_rel_def
             isasat_input_ops.empty_watched_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
             list_rel_mset_rel_def list_rel_def uint32_nat_rel_def br_def
             list_all2_op_eq_map_right_iff' list_mset_rel_def
            simp del: replicate_Suc
            dest!: in_N0\<close>)

  qed
  show ?thesis
    apply (intro frefI nres_relI)
    subgoal for x y
    unfolding init_state_wl_heur_alt_def init_state_wl_D'_def
    apply (rewrite in \<open>let _ = Suc _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = 2 * _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = fmempty in _\<close> Let_def)
    apply (rewrite in \<open>let _ = init_rll _ in _\<close> Let_def)
    apply (refine_vcg init[of y x] initialise_VMTF cach)
    subgoal by auto
    subgoal using H by (auto simp: P_def init_rll_def init_lrl_def)
    apply assumption
    subgoal by simp
    subgoal unfolding isasat_input_ops.phase_saving_def by auto
    subgoal by fast
    subgoal by fast
    subgoal by (auto simp: P_def init_rll_def isasat_input_ops.option_lookup_clause_rel_def
          isasat_input_ops.lookup_clause_rel_def
          simp del: replicate.simps
          intro!: mset_as_position.intros)
    done
  done
qed

(* TODO replace list_mset_assn_pure_conv by this: *)
lemma (in -)list_mset_assn_pure_conv':
  \<open>list_mset_assn (pure R) = pure (\<langle>R\<rangle>list_rel_mset_rel)\<close>
  apply (intro ext)
  using list_all2_reorder_left_invariance
  by (fastforce
    simp: list_rel_mset_rel_def list_mset_assn_def
      mset_rel_def rel2p_def[abs_def] rel_mset_def p2rel_def
      list_mset_rel_def[abs_def] Collect_eq_comp br_def
      list_rel_mset_rel_def list_rel_def Collect_eq_comp_right
    intro!: arg_cong[of _ _ \<open>\<lambda>b. pure b _ _\<close>])

lemma init_state_wl_heur_hnr:
  \<open>(init_state_wl_D'_code, isasat_input_ops.init_state_wl_heur)
    \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
      (list_mset_assn uint32_nat_assn)\<^sup>k \<rightarrow>
      isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
       \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
         (hr_comp (list_assn uint32_assn) (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel))\<^sup>k \<rightarrow>
         hr_comp trail_pol_assn (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) *a
         clauses_ll_assn *a
         hr_comp conflict_option_rel_assn (isasat_input_ops.option_lookup_clause_rel \<A>\<^sub>i\<^sub>n) *a
         hr_comp (list_assn unat_lit_assn) list_mset_rel *a
         hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>\<langle>nat_rel\<rangle>list_rel\<rangle>list_rel) *a
         vmtf_remove_conc_option_fst_As *a hr_comp phase_saver_conc (\<langle>bool_rel\<rangle>list_rel) *a
         uint32_nat_assn *a isasat_input_ops.cach_refinement_assn \<A>\<^sub>i\<^sub>n *a lbd_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using init_state_wl_D'_code.refine[FCOMP init_state_wl_D', of \<A>\<^sub>i\<^sub>n]
    unfolding isasat_input_ops.cach_refinement_assn_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def by fast
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep list_assn_pure_conv
    by (auto simp: hrp_comp_def hr_comp_def list_mset_assn_pure_conv')
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep isasat_input_ops.isasat_init_assn_def
      isasat_input_ops.option_lookup_clause_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def list_assn_list_mset_rel_eq_list_mset_assn)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
qed

lemma init_state_wl_heur_init_state_wl:
  \<open>(isasat_input_ops.init_state_wl_heur, RETURN o isasat_input_ops.init_state_wl)
  \<in> [\<lambda>N. N = \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<rightarrow> \<langle>isasat_input_ops.twl_st_heur_init_wl \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  using isasat_input_ops.init_state_wl_heur_init_state_wl
  unfolding fref_def nres_rel_def
  by auto


lemma init_dt_wl_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>_. init_dt_wl_code), uncurry2 (isasat_input_ops.init_dt_wl_heur))
  \<in> [\<lambda>((N, S), S'). isasat_input_bounded N \<and> N = \<A>\<^sub>i\<^sub>n]\<^sub>a
    (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a
      (isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
    isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding PR_CONST_def
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using init_dt_wl_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>(snd (fst c), snd c)\<close> \<open>(snd (fst a), snd a)\<close>]
    by (cases a)
       (sep_auto dest!: frame_rule_left[of \<open>_ * isasat_input_ops.isasat_init_assn _ _ _\<close> _ _
            \<open>list_mset_assn uint32_nat_assn \<A>\<^sub>i\<^sub>n (fst (fst a))\<close>])
  done

lemma (in isasat_input_bounded) init_dt_wl_heur_init_dt_wl:
  \<open>(uncurry init_dt_wl_heur, uncurry init_dt_wl) \<in>
    [\<lambda>(CS, S). (\<forall>C \<in> set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)) \<and> distinct_mset_set (mset ` set CS)]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
proof -
  have H: \<open>\<And>x y x1 x2 x1a x2a.
       (\<forall>C\<in>set x1. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)) \<and> distinct_mset_set (mset ` set x1) \<Longrightarrow>
       (x1a, x1) \<in> \<langle>Id\<rangle>list_rel \<Longrightarrow>
       (x1a, x1) \<in> \<langle>{(C, C'). C = C' \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and>
          distinct C}\<rangle>list_rel\<close>
    apply (auto simp: list_rel_def list_all2_conj)
    apply (auto simp: list_all2_conv_all_nth distinct_mset_set_def)
    done

  show ?thesis
    unfolding init_dt_wl_heur_def init_dt_wl_def uncurry_def
    apply (intro frefI nres_relI)
    apply (case_tac y rule: prod.exhaust)
    apply (case_tac x rule: prod.exhaust)
    apply (simp only: prod.case prod_rel_iff)
    apply (refine_vcg init_dt_step_wl_heur_init_dt_step_wl[THEN fref_to_Down_curry] H)
         apply normalize_goal+
    subgoal by fast
    subgoal by fast
    subgoal by simp
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end
