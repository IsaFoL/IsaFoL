theory CDCL_Two_Watched_Literals_IsaSAT
imports CDCL_Two_Watched_Literals_IsaSAT_CDCL
begin

lemma distinct_nat_of_uint32[iff]:
  \<open>distinct_mset (nat_of_uint32 `# A) \<longleftrightarrow> distinct_mset A\<close>
  \<open>distinct (map nat_of_uint32 xs) \<longleftrightarrow> distinct xs\<close>
  using distinct_image_mset_inj[of nat_of_uint32]
  by (auto simp: inj_on_def distinct_map)


declare isasat_input_bounded.append_el_aa_hnr[sepref_fr_rules]
declare isasat_input_bounded.polarity_pol_code_polarity_refine[sepref_fr_rules]
  isasat_input_bounded.cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]

definition finalise_init where
  \<open>finalise_init = id\<close>

context isasat_input_bounded
begin

type_synonym (in -) vmtf_remove_int_option_lst = \<open>vmtf_option_lst \<times> nat list\<close>

definition (in isasat_input_ops) vmtf_init :: \<open>(nat, nat) ann_lits \<Rightarrow> vmtf_remove_int_option_lst set\<close> where
\<open>vmtf_init M = {((ns, m, lst, next_search), to_remove).
   \<A>\<^sub>i\<^sub>n \<noteq> {#} \<longrightarrow> (lst \<noteq> None \<and> ((ns, m, the lst, next_search), to_remove) \<in> vmtf M)}\<close>

type_synonym (in -) twl_st_wl_heur_init =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat clause option \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int_option_lst \<times> bool list \<times>
    nat\<close>

abbreviation (in -) vmtf_conc_option_lst where
  \<open>vmtf_conc_option_lst \<equiv> (array_assn nat_vmtf_node_assn *assn nat_assn *assn option_assn uint32_nat_assn
    *assn option_assn uint32_nat_assn)\<close>

type_synonym (in -)vmtf_assn_option_lst = \<open>uint32 vmtf_node array \<times> nat \<times> uint32 option \<times> uint32 option\<close>
type_synonym (in -)vmtf_remove_assn_option_lst = \<open>vmtf_assn_option_lst \<times> uint32 array_list\<close>

abbreviation (in -)vmtf_remove_conc_option_lst 
  :: \<open>vmtf_remove_int_option_lst \<Rightarrow> vmtf_remove_assn_option_lst \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc_option_lst \<equiv> vmtf_conc_option_lst *assn arl_assn uint32_nat_assn\<close>

definition (in isasat_input_ops) twl_st_heur_init :: \<open>(twl_st_wl_heur_init \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_init =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M
  }\<close>

type_synonym (in -)twl_st_wll_trail_init =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_option_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn_option_lst \<times> phase_saver_assn \<times>
    uint32\<close>

definition (in isasat_input_ops) twl_st_heur_init_assn :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close> where
\<open>twl_st_heur_init_assn =
  trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc_option_lst *assn phase_saver_conc *assn
  uint32_nat_assn\<close>

definition (in isasat_input_ops) twl_st_init_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close> where
\<open>twl_st_init_assn = hr_comp twl_st_heur_init_assn twl_st_heur_init\<close>

definition (in isasat_input_ops) propagate_unit_cls :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
  \<open>propagate_unit_cls = (\<lambda>L (M, N, U, D, NP, UP, Q, WS).
     (Propagated L 0 # M, N, U, D, add_mset {#L#} NP, UP, add_mset (-L) Q, WS))\<close>

definition (in isasat_input_ops) propagate_unit_cls_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>propagate_unit_cls_heur = (\<lambda>L (M, N, U, D, Q, oth).
     (Propagated L 0 # M, N, U, D, add_mset (-L) Q, oth))\<close>

lemma propagate_unit_cls_heur_propagate_unit_cls:
  \<open>(uncurry (RETURN oo propagate_unit_cls_heur), uncurry (RETURN oo propagate_unit_cls)) \<in>
   [\<lambda>(L, S). undefined_lit (get_trail_wl S) L]\<^sub>f Id \<times>\<^sub>r twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def propagate_unit_cls_heur_def propagate_unit_cls_def vmtf_init_def
      intro: vmtf_consD)

sepref_thm propagate_unit_cls_code
  is \<open>uncurry (RETURN oo propagate_unit_cls_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> undefined_lit (fst S) L]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d  \<rightarrow> twl_st_heur_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding propagate_unit_cls_heur_def twl_st_heur_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) propagate_unit_cls_code
   uses isasat_input_bounded.propagate_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) propagate_unit_cls_code_def

lemmas propagate_unit_cls_heur_hnr[sepref_fr_rules] =
   propagate_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem propagate_unit_cls_hnr[sepref_fr_rules]:
  \<open>(uncurry propagate_unit_cls_code, uncurry (RETURN oo propagate_unit_cls))
    \<in> [\<lambda>(L, S). undefined_lit (get_trail_wl S) L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d  \<rightarrow> twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_init)
     (\<lambda>(L, S). undefined_lit (get_trail_wl S) L)
     (\<lambda>_ (L, S). L \<in> snd ` D\<^sub>0 \<and> undefined_lit (fst S) L)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d)
                    (nat_lit_lit_rel \<times>\<^sub>f
                     twl_st_heur_init) \<rightarrow> hr_comp
          twl_st_heur_init_assn twl_st_heur_init\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propagate_unit_cls_heur_hnr
    propagate_unit_cls_heur_propagate_unit_cls] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_init_def image_image)
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

definition (in isasat_input_ops) already_propagated_unit_cls :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
  \<open>already_propagated_unit_cls = (\<lambda>L (M, N, U, D, NP, UP, Q, WS).
     (M, N, U, D, add_mset {#L#} NP, UP, Q, WS))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_heur
   :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close>
where
  \<open>already_propagated_unit_cls_heur = (\<lambda>L (M, N, U, D, Q, oth).
     (M, N, U, D, Q, oth))\<close>

lemma already_propagated_unit_cls_heur_already_propagated_unit_cls:
  \<open>(uncurry (RETURN oo already_propagated_unit_cls_heur), uncurry (RETURN oo already_propagated_unit_cls)) \<in>
   nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def already_propagated_unit_cls_heur_def already_propagated_unit_cls_def
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_code
  is \<open>uncurry (RETURN oo already_propagated_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d  \<rightarrow>\<^sub>a twl_st_heur_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def twl_st_heur_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) already_propagated_unit_cls_code
   uses isasat_input_bounded.already_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_code_def

lemmas already_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem already_propagated_unit_cls_hnr[sepref_fr_rules]:
  \<open>(uncurry already_propagated_unit_cls_code, uncurry (RETURN \<circ>\<circ> already_propagated_unit_cls))
  \<in> unat_lit_assn\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  using already_propagated_unit_cls_heur_hnr[FCOMP already_propagated_unit_cls_heur_already_propagated_unit_cls]
  unfolding twl_st_init_assn_def[symmetric] by simp

definition (in -) set_conflict_unit :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_unit L _ = Some {#L#}\<close>

definition (in isasat_input_ops) conflict_propagated_unit_cls :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
  \<open>conflict_propagated_unit_cls = (\<lambda>L (M, N, U, D, NP, UP, Q, WS).
     (M, N, U, set_conflict_unit L D, add_mset {#L#} NP, UP, {#}, WS))\<close>

definition conflict_propagated_unit_cls_heur 
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close>
where
  \<open>conflict_propagated_unit_cls_heur = (\<lambda>L (M, N, U, D, Q, oth).
     (M, N, U, set_conflict_unit L D, {#}, oth))\<close>

lemma conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls:
  \<open>(uncurry (RETURN oo conflict_propagated_unit_cls_heur), uncurry (RETURN oo conflict_propagated_unit_cls)) \<in>
   nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def conflict_propagated_unit_cls_heur_def conflict_propagated_unit_cls_def
      intro: vmtf_consD)

definition (in isasat_input_ops) set_conflict_unit_heur where
  \<open>set_conflict_unit_heur = (\<lambda> L (b, n, xs). (False, 1, xs[atm_of L := Some (is_pos L)]))\<close>

lemma set_conflict_unit_heur_set_conflict_unit:
  \<open>(uncurry (RETURN oo set_conflict_unit_heur), uncurry (RETURN oo set_conflict_unit)) \<in>
    [\<lambda>(L, D). D = None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f option_conflict_rel \<rightarrow>
     \<langle>option_conflict_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def set_conflict_unit_heur_def set_conflict_unit_def
      option_conflict_rel_def conflict_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      intro!: mset_as_position.intros)

sepref_thm set_conflict_unit_code
  is \<open>uncurry (RETURN oo set_conflict_unit_heur)\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn\<close>
  supply one_nat_uint32[sepref_fr_rules]
  unfolding set_conflict_unit_heur_def one_nat_uint32_def[symmetric]
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
      unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d  \<rightarrow> conflict_option_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_conflict_rel)
     (\<lambda>(L, D). D = None \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a
                      conflict_option_rel_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f
                      option_conflict_rel) \<rightarrow> hr_comp
                  conflict_option_rel_assn
                  option_conflict_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_conflict_unit_heur_hnr
    set_conflict_unit_heur_set_conflict_unit] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def option_conflict_rel_def conflict_rel_def image_image
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

(* TODO Move *)
fun get_conflict_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat clause option\<close> where
  \<open>get_conflict_wl_heur_init (_, _, _, D, _) = D\<close>

fun get_watched_list_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat list list\<close> where
  \<open>get_watched_list_heur_init (_, _, _, _, _, W, _) = W\<close>
(* End Move *)

sepref_thm conflict_propagated_unit_cls_code
  is \<open>uncurry (RETURN oo conflict_propagated_unit_cls_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl_heur_init S = None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d  \<rightarrow> twl_st_heur_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def twl_st_heur_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) conflict_propagated_unit_cls_code
   uses isasat_input_bounded.conflict_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_propagated_unit_cls_code_def

lemmas conflict_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   conflict_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

theorem conflict_propagated_unit_cls_hnr[sepref_fr_rules]:
  \<open>(uncurry conflict_propagated_unit_cls_code, uncurry (RETURN oo conflict_propagated_unit_cls))
    \<in> [\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl S = None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d  \<rightarrow> twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_init) (\<lambda>_. True)
       (\<lambda>_ (L, S).
           L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl_heur_init S = None)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (unat_lit_assn\<^sup>k *\<^sub>a
                        twl_st_heur_init_assn\<^sup>d)
                       (nat_lit_lit_rel \<times>\<^sub>f
                        twl_st_heur_init) \<rightarrow> hr_comp
           twl_st_heur_init_assn twl_st_heur_init\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF conflict_propagated_unit_cls_heur_hnr
    conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_init_def image_image)
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

definition (in isasat_input_ops) add_init_cls
  :: \<open>nat clause_l \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close>  where
  \<open>add_init_cls = (\<lambda>C (M, N, U, D, NP, UP, Q, WS). do {
           let U = length N;
           let WS = WS((hd C) := WS (hd C) @ [U]);
           let WS = WS((hd (tl C)) := WS (hd (tl C)) @ [U]);
           RETURN (M, N @ [op_array_of_list C], U, D, NP, UP, Q, WS)})\<close>

definition (in isasat_input_ops) add_init_cls_heur
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>  where
  \<open>add_init_cls_heur = (\<lambda>C (M, N, U, D, Q, WS, oth). do {
     let U = length N;
     let WS = WS[nat_of_lit (hd C) := WS ! nat_of_lit (hd C) @ [U]];
     let WS = WS[nat_of_lit (hd (tl C)) := WS ! nat_of_lit (hd (tl C)) @ [U]];
     RETURN (M, N @ [op_array_of_list C], U, D, Q, WS, oth)})\<close>

sepref_thm add_init_cls_code
  is \<open>uncurry add_init_cls_heur\<close>
  :: \<open>[\<lambda>(C, S). C \<noteq> [] \<and> tl C \<noteq>[] \<and> nat_of_lit (hd C) < length (get_watched_list_heur_init S) \<and>
        nat_of_lit (hd (tl C)) < length (get_watched_list_heur_init S)]\<^sub>a
      (list_assn unat_lit_assn)\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d  \<rightarrow> twl_st_heur_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def twl_st_heur_init_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  unfolding twl_st_heur_init_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric] delete_index_and_swap_ll_def[symmetric]
   append_ll_def[symmetric]
  by sepref

concrete_definition (in -) add_init_cls_code
   uses isasat_input_bounded.add_init_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) add_init_cls_code_def

lemmas add_init_cls_heur_hnr[sepref_fr_rules] =
   add_init_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma add_init_cls_heur_add_init_cls:
  \<open>(uncurry add_init_cls_heur, uncurry (add_init_cls)) \<in>
   [\<lambda>(C, S). length C \<ge> 2 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def add_init_cls_heur_def add_init_cls_def Let_def
      map_fun_rel_def)

theorem add_init_cls_hnr[sepref_fr_rules]:
  \<open>(uncurry add_init_cls_code, uncurry add_init_cls)
    \<in> [\<lambda>(C, S). length C \<ge> 2 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)]\<^sub>a
      (list_assn unat_lit_assn)\<^sup>k *\<^sub>a twl_st_init_assn\<^sup>d  \<rightarrow> twl_st_init_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f twl_st_heur_init)
     (\<lambda>(C, S).
         2 \<le> length C \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C))
     (\<lambda>_ (C, S).
         C \<noteq> [] \<and>
         tl C \<noteq> [] \<and>
         nat_of_lit (hd C)
         < length (get_watched_list_heur_init S) \<and>
         nat_of_lit (hd (tl C))
         < length (get_watched_list_heur_init S))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     ((list_assn unat_lit_assn)\<^sup>k *\<^sub>a
                      twl_st_heur_init_assn\<^sup>d)
                     (Id \<times>\<^sub>f
                      twl_st_heur_init) \<rightarrow> hr_comp
        twl_st_heur_init_assn twl_st_heur_init\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF add_init_cls_heur_hnr
    add_init_cls_heur_add_init_cls] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    apply (cases \<open>fst x\<close>; cases \<open>tl (fst x)\<close>)
    using that by (auto simp: comp_PRE_def twl_st_heur_init_def image_image map_fun_rel_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
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

definition (in isasat_input_ops) already_propagated_unit_cls_conflict
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close>
where
  \<open>already_propagated_unit_cls_conflict = (\<lambda>L (M, N, U, D, NP, UP, Q, WS).
     (M, N, U, D, add_mset {#L#} NP, UP, {#}, WS))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_conflict_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close>
where
  \<open>already_propagated_unit_cls_conflict_heur = (\<lambda>L (M, N, U, D, Q, oth).
     (M, N, U, D, {#}, oth))\<close>

lemma already_propagated_unit_cls_conflict_heur_already_propagated_unit_cls_conflict:
  \<open>(uncurry (RETURN oo already_propagated_unit_cls_conflict_heur),
     uncurry (RETURN oo already_propagated_unit_cls_conflict)) \<in>
   Id \<times>\<^sub>r twl_st_heur_init \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_init_def already_propagated_unit_cls_conflict_heur_def
      already_propagated_unit_cls_conflict_def
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_conflict_code
  is \<open>uncurry (RETURN oo already_propagated_unit_cls_conflict_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_init_assn\<^sup>d  \<rightarrow>\<^sub>a twl_st_heur_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def twl_st_heur_init_assn_def is_in_conflict_def[symmetric]
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

definition (in isasat_input_ops) init_dt_step_wl 
  :: \<open>nat clause_l \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close>
where
  \<open>init_dt_step_wl C S = do {
     if get_conflict_wl S = None
     then do {
         if length C = 1
         then do {
           ASSERT (C \<noteq> []);
           let L = hd C;
           ASSERT(L \<in> snd ` D\<^sub>0);
           let val_L = polarity (get_trail_wl S) L;
           if val_L = None
           then do {RETURN (propagate_unit_cls L S)}
           else
             if val_L = Some True
             then do {RETURN (already_propagated_unit_cls L S)}
             else do {RETURN (conflict_propagated_unit_cls L S)}
           }
         else do {
          ASSERT(length C \<ge> 2);
          ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
          add_init_cls C S}}
    else do {
        if length C = 1
        then do {
          ASSERT (C \<noteq> []);
          let L = hd C;
          RETURN (already_propagated_unit_cls_conflict L S)}
        else do {
          ASSERT(hd C \<in> snd ` D\<^sub>0);
          ASSERT(length C \<ge> 2);
          ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
          add_init_cls C S}}
  }\<close>


definition (in -) get_conflict_wl_is_None_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur_init = (\<lambda>(M, N, U, D, Q, W, _). is_None D)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_init \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_init_def get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_def
     split: option.splits)

definition (in -) get_conflict_wl_is_None_init where
  \<open>get_conflict_wl_is_None_init = get_conflict_wl_is_None\<close>

sepref_thm get_conflict_wl_is_None_init_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>twl_st_heur_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_def twl_st_heur_init_assn_def length_ll_def[symmetric]
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

type_synonym (in -) twl_st_wl_heur_init_trail_ref =
  \<open>trail_pol \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int_option_lst \<times> bool list \<times> nat\<close>

definition (in isasat_input_ops) twl_st_heur_pol_init
   :: \<open>(twl_st_wl_heur_init_trail_ref \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_pol_init =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls), (M, N, U, D, NP, UP, Q, W)).
    (M', M) \<in> trail_pol \<and> N' = N \<and> U' = U \<and> D = D' \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M
  }\<close>
definition twl_st_heur_pol_init_assn
  :: \<open>twl_st_wl_heur_init_trail_ref \<Rightarrow> _ \<Rightarrow> assn\<close>
where
  \<open>twl_st_heur_pol_init_assn =
    (trail_pol_assn *assn clauses_ll_assn *assn nat_assn *assn
    conflict_option_assn *assn
    clause_l_assn *assn
    arrayO_assn (arl_assn nat_assn) *assn
    vmtf_remove_conc_option_lst *assn phase_saver_conc *assn
    uint32_nat_assn
    )\<close>

lemma (in isasat_input_ops) twl_st_trail_no_clvls_ref_alt_def:
  \<open>twl_st_heur_pol_init =
    (trail_pol \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O twl_st_heur_init\<close>
  by (force simp: twl_st_heur_pol_init_def twl_st_heur_init_def)

lemma twl_st_heur_init_assn_twl_st_heur_pol_init_assn:
  \<open>twl_st_heur_init_assn =
  hr_comp twl_st_heur_pol_init_assn
       (trail_pol \<times>\<^sub>f
        (Id \<times>\<^sub>f
         (nat_rel \<times>\<^sub>f
          (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))))\<close>
  unfolding twl_st_heur_pol_init_assn_def twl_st_heur_init_assn_def hr_comp_prod_conv
  by simp

lemma twl_st_heur_init_assn_assn:
  \<open>hr_comp twl_st_heur_pol_init_assn twl_st_heur_pol_init = twl_st_init_assn\<close>
  unfolding twl_st_init_assn_def twl_st_trail_no_clvls_ref_alt_def
  hr_comp_assoc[symmetric] twl_st_heur_init_assn_twl_st_heur_pol_init_assn
  ..

definition polarity_st_heur_init :: \<open>twl_st_wl_heur_init_trail_ref \<Rightarrow> _ \<Rightarrow> bool option nres\<close> where
  \<open>polarity_st_heur_init = (\<lambda>(M, _) L. polarity_pol M L)\<close>


sepref_thm polarity_st_heur_init_code
  is \<open>uncurry polarity_st_heur_init\<close>
  :: \<open>twl_st_heur_pol_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding polarity_st_heur_init_def twl_st_heur_pol_init_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_init_code
   uses isasat_input_bounded.polarity_st_heur_init_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_init_code_def

lemmas polarity_st_heur_init_code_polarity_refine_code[sepref_fr_rules] =
   polarity_st_heur_init_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma polarity_st_heur_code_polarity_st_refine[sepref_fr_rules]:
  \<open>(uncurry polarity_st_heur_init_code, uncurry (RETURN oo polarity_st)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a twl_st_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>polarity_atm M (atm_of L) = (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: polarity_atm_def polarity_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry polarity_st_heur_init, uncurry (RETURN oo polarity_st)) \<in>
     [\<lambda>(_, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_heur_pol_init \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
       (auto simp: trail_pol_def polarity_st_def (* polarity_def *)
        twl_st_heur_pol_init_def polarity_pol_def polarity_st_heur_init_def
        split: if_splits option.splits)
  show ?thesis
    using polarity_st_heur_init_code.refine[FCOMP 2, OF isasat_input_bounded_axioms,
      unfolded twl_st_heur_init_assn_assn] .
qed

sepref_register (in isasat_input_ops) init_dt_step_wl
sepref_thm init_dt_step_wl_code
  is \<open>uncurry (PR_CONST init_dt_step_wl)\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>d *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a
       twl_st_init_assn\<close>
  supply polarity_None_undefined_lit[simp] polarity_st_def[simp] get_conflict_wl_is_None_def[simp]
  option.splits[split] get_conflict_wl_is_None_init_def[simp]
  unfolding init_dt_step_wl_def lms_fold_custom_empty PR_CONST_def
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding
    cons_trail_Propagated_def[symmetric] get_conflict_wl_is_None
    polarity_st_def[symmetric]
    get_conflict_wl_is_None_init_def[symmetric]
  by sepref

concrete_definition (in -) init_dt_step_wl_code
  uses "isasat_input_bounded.init_dt_step_wl_code.refine_raw"
  is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) init_dt_step_wl_code_def

lemmas init_dt_step_wl_code_refine[sepref_fr_rules] =
  init_dt_step_wl_code.refine[OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) init_dt_wl where
  \<open>init_dt_wl CS S = nfoldli CS (\<lambda>_. True) (init_dt_step_wl) S\<close>

sepref_register (in isasat_input_ops) init_dt_wl

sepref_thm init_dt_wl_code
  is \<open>uncurry (PR_CONST init_dt_wl)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a
       twl_st_init_assn\<close>
  unfolding init_dt_wl_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) init_dt_wl_code
  uses "isasat_input_bounded.init_dt_wl_code.refine_raw"
  is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) init_dt_wl_code_def

lemmas init_dt_wl_code_refine[sepref_fr_rules] =
  init_dt_wl_code.refine[OF isasat_input_bounded_axioms]

end

definition nat_lit_list_hm_ref_rel :: "(('a set \<times> 'a list) \<times> 'a list) set" where
  \<open>nat_lit_list_hm_ref_rel = {((s, xs), l). l = xs \<and> s = set l}\<close>

abbreviation nat_lit_lits_init_ref_assn where
  \<open>nat_lit_lits_init_ref_assn \<equiv> hs.assn uint32_nat_assn *assn list_assn uint32_nat_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp nat_lit_lits_init_ref_assn nat_lit_list_hm_ref_rel\<close>

definition in_map_atm_of :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
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

definition extract_atms_clss:: \<open>'a clauses_l \<Rightarrow> 'a list \<Rightarrow> 'a list\<close>  where
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

lemma all_lits_of_atms_mm_all_lits_of_mm:
  \<open>all_lits_of_atms_mm N = all_lits_of_mm (poss `# N)\<close>
  unfolding all_lits_of_atms_mm_def all_lits_of_mm_def
  by (induction N) auto

lemma all_lits_of_atms_m_all_lits_of_m:
  \<open>all_lits_of_atms_m N = all_lits_of_m (poss N)\<close>
  unfolding all_lits_of_atms_m_def all_lits_of_m_def
  by (induction N) auto

lemma all_lits_of_m_extract_atms_cls: \<open>set_mset (all_lits_of_atms_m (mset (extract_atms_cls C \<A>\<^sub>i\<^sub>n))) =
   set_mset (all_lits_of_m (mset C) + all_lits_of_atms_m (mset \<A>\<^sub>i\<^sub>n))\<close>
  apply (induction C arbitrary: \<A>\<^sub>i\<^sub>n)
  subgoal by simp
  subgoal by (auto simp add: extract_atms_cls_Cons all_lits_of_m_add_mset uminus_literal_def
        in_all_lits_of_m_ain_atms_of_iff insert_absorb all_lits_of_atms_m_all_lits_of_m)
  done

lemma nat_of_lit_uint_max_nat_of_lit_uminus_uint_max:
  \<open>nat_of_lit (-L) < uint_max \<longleftrightarrow> nat_of_lit L < uint_max\<close>
  by (cases L) (auto simp: uint_max_def)

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

lemma is_\<L>\<^sub>a\<^sub>l\<^sub>l_extract_atms_clss:
  assumes upper: \<open>\<forall>L \<in> set \<A>\<^sub>i\<^sub>n. L < uint_max div 2\<close>
  assumes uint_max: \<open>\<forall>C \<in> set N. \<forall>L \<in> set C. nat_of_lit L < uint_max\<close>
  shows
   \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss N \<A>\<^sub>i\<^sub>n))
     (all_lits_of_mm (mset `# mset N) + all_lits_of_atms_m (mset \<A>\<^sub>i\<^sub>n))\<close>
proof -
  have atm_of_\<A>\<^sub>i\<^sub>n_iff: \<open>atm_of x \<in> set \<A>\<^sub>i\<^sub>n \<longleftrightarrow>
         x \<in> (- literal_of_nat \<circ>\<circ> op *) 2 ` set \<A>\<^sub>i\<^sub>n \<or> x \<in> (literal_of_nat \<circ>\<circ> op *) 2 ` set \<A>\<^sub>i\<^sub>n\<close>
    for x \<A>\<^sub>i\<^sub>n
    by (cases x) auto
  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_add: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n B\<close> for A B \<A>\<^sub>i\<^sub>n
    using that unfolding isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by auto
  have H1: \<open>xa \<in> set \<A>\<^sub>i\<^sub>n \<Longrightarrow> literal_of_nat (2 * xa) \<in> Pos ` set \<A>\<^sub>i\<^sub>n\<close> for xa \<A>\<^sub>i\<^sub>n
    by auto
  have H2: \<open>xa \<in> set \<A>\<^sub>i\<^sub>n \<Longrightarrow> - literal_of_nat (2 * xa) \<in> Neg ` set \<A>\<^sub>i\<^sub>n\<close> for xa \<A>\<^sub>i\<^sub>n
    by auto
  show ?thesis
    using upper uint_max
  proof (induction N arbitrary: \<A>\<^sub>i\<^sub>n)
    case Nil
    then show ?case
      using H1 H2
      by (auto simp: extract_atms_cls_def extract_atms_clss_def isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def in_all_lits_of_m_ain_atms_of_iff
          atm_of_eq_atm_of all_lits_of_atms_m_all_lits_of_m
          atm_of_\<A>\<^sub>i\<^sub>n_iff
          simp del: nat_of_lit.simps literal_of_nat.simps)
  next
    case (Cons C Cs \<A>\<^sub>i\<^sub>n) note IH = this(1) and H=this(2-)
    have \<open>2 * L < uint_max \<longleftrightarrow> L < uint_max div 2\<close> for L
      by (auto simp: uint_max_def)
    then have \<open>\<forall>L\<in>set (extract_atms_cls C \<A>\<^sub>i\<^sub>n). L < uint_max div 2\<close>
      using Cons
      by (auto simp: in_extract_atms_clsD nat_of_lit_uint_max_nat_of_lit_uminus_uint_max)
    then show ?case
      using IH[of \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n\<close>, unfolded isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def] H
      by (simp add: all_lits_of_mm_add_mset isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
          all_lits_of_m_extract_atms_cls ac_simps comp_def)
  qed
qed


context isasat_input_bounded
begin

fun correct_watching_init :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_init (M, N, U, D, NP, UP, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_atms_m \<A>\<^sub>i\<^sub>n. mset (W L) = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>


lemma clause_to_update_append: \<open>N \<noteq> [] \<Longrightarrow> clause_to_update La (M, N @ [C], U, D, NP, UP, WS, Q) =
     clause_to_update La (M, N, U, D, NP, UP, WS, Q) +
    (if La \<in> set (watched_l C) then {#length N#} else {#})\<close>
  unfolding clause_to_update_def get_clauses_l.simps
  by (auto simp: clause_to_update_def nth_append)

definition HH :: \<open>(nat twl_st_wl \<times> nat twl_st_l) set\<close> where
  \<open>HH = {((M', N', U', D', NP', UP', Q', WS'), (M, N, U, D, NP, UP, WS, Q)).
               M = M' \<and> N = N' \<and> U = U' \<and> D = D' \<and> NP = NP' \<and> UP = UP' \<and> Q = Q' \<and> WS = {#} \<and>
               (* U = length N - 1 \<and> *) UP = {#} \<and> N \<noteq> [] \<and>
               correct_watching_init (M', N', U', D', NP', UP', Q', WS') \<and>
               set_mset (all_lits_of_mm (mset `# mset (tl N) + NP)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
               (\<forall>L \<in> lits_of_l M. {#L#} \<in># NP) \<and>
               (\<forall>L \<in> set M. \<exists>K. L = Propagated K 0) \<and>
               (D \<noteq> None \<longrightarrow> Q = {#})}\<close>


lemma literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (add_mset L M) \<longleftrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n M \<and> atm_of L \<in># \<A>\<^sub>i\<^sub>n\<close>
  by (cases L)
   (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def image_image all_lits_of_m_add_mset uminus_lit_swap
         simp del: literal_of_nat.simps)

lemma init_dt_step_wl_init_dt_step_l:
  assumes
    S'S: \<open>(S', S) \<in> HH\<close> and
    lits_C: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close> and
    dist_C: \<open>distinct C\<close>
  shows \<open>init_dt_step_wl C S' \<le> \<Down> HH (init_dt_step_l C S)\<close>
proof -
  have val: \<open>(val, val') \<in> \<langle>Id\<rangle>option_rel\<close> if \<open>val = val'\<close> for val val'
    using that by auto
  have [simp]: \<open>clause_to_update L (M, N, U, D, NP, UP, WS, Q) =
       clause_to_update L (M', N', U', D', NP', UP', WS', Q')\<close>
    if \<open>N = N'\<close>
    for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' and L :: \<open>nat literal\<close>
    by (auto simp: clause_to_update_def that)
  note literal_of_nat.simps[simp del] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[simp]
  have hd_C: \<open>hd C \<in> snd ` (\<lambda>L. (nat_of_lit L, L)) ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      \<open>-hd C \<in> snd ` (\<lambda>L. (nat_of_lit L, L)) ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if \<open>C \<noteq> []\<close>
    using assms(3-) that lits_C
    by (cases C; cases \<open>hd C\<close>;
        auto simp: HH_def correct_watching.simps clause_to_update_def image_image
        all_lits_of_mm_add_mset all_lits_of_m_add_mset isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
        clauses_def mset_take_mset_drop_mset' literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)+

  have hd_tl_C: \<open>hd (tl C) \<in> snd ` (\<lambda>L. (nat_of_lit L, L)) ` set_mset (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>C \<noteq> []\<close> and \<open>tl C \<noteq> []\<close>
    using assms(3-) that lits_C by (cases C; cases \<open>tl C\<close>)
      (auto simp: HH_def Let_def clause_to_update_append
        clauses_def mset_take_mset_drop_mset' image_image all_lits_of_m_add_mset
        isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n_def)

  obtain M N U D NP Q WS where
    S': \<open>S' = (M, N, U, D, NP, {#}, Q, WS)\<close> and
    S: \<open>S = (M, N, U, D, NP, {#}, {#}, Q)\<close> and
    H: \<open>correct_watching_init (M, N, U, D, NP, {#}, Q, WS)\<close>
     \<open>set_mset (all_lits_of_mm (mset `# mset (tl N) + NP)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
     \<open>\<forall>L\<in>lits_of_l M. {#L#} \<in># NP\<close>
     \<open>\<forall>L\<in>set M. \<exists>K. L = Propagated K 0\<close>
     \<open>N \<noteq> []\<close>
     \<open>D \<noteq> None \<longrightarrow> Q = {#}\<close>
    using S'S unfolding HH_def
    by (cases S'; cases S) (auto simp: HH_def)
  have le2_no_confl:
    \<open>((M, N @ [op_array_of_list C], length N, D, NP, {#},
        Q, WS
        (hd C := WS (hd C) @ [length N],
         hd (tl C) :=
           (WS(hd C := WS (hd C) @ [length N]))
            (hd (tl C)) @
           [length N])),
       M, N @ [C], length N, None, NP, {#}, {#}, Q)
      \<in> HH\<close>
    if
      dist: \<open>distinct C\<close> and
      [simp]: \<open>D = None\<close> and
      \<open>length C \<noteq> 1\<close> and
      \<open>length C \<noteq> 1\<close> and
      \<open>C \<noteq> []\<close> and
      \<open>tl C \<noteq> []\<close> and
      C_ge2: \<open>2 \<le> length C\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
  proof -
    obtain L1 L2 C' where C: \<open>C = L1 # L2 # C'\<close>
      using C_ge2 by (cases C; cases \<open>tl C\<close>) auto
    have [simp]: \<open>L2 \<noteq> L1\<close>
      using dist unfolding C by auto
    have \<open>set_mset (all_lits_of_mm (mset `# mset (tl (N @ [L1 # L2 # C'])) + NP)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using lits_C H unfolding C
      by (auto simp add: all_lits_of_mm_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          all_lits_of_m_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    then show ?thesis
      using H
      unfolding HH_def C
      by (auto simp: clause_to_update_append all_lits_of_mm_add_mset
          all_lits_of_m_add_mset)
  qed
  have unit_confl:
    \<open>((M, N, U, D, add_mset {#hd C#} NP, {#}, {#}, WS), M, N,
       U, Some (the D), add_mset {#hd C#} NP, {#}, {#}, {#})
      \<in> HH\<close>
    if
      D: \<open>D \<noteq> None\<close> and
      [simp]: \<open>C \<noteq> []\<close> and
      \<open>C \<noteq> []\<close>
  proof -
    show ?thesis
      using H D lits_C
      unfolding HH_def
      by (cases C) (auto simp: clause_to_update_append all_lits_of_mm_add_mset
          all_lits_of_m_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  qed
  have le1_propa_no_confl:
    \<open>((Propagated (hd C) 0 # M, N, U, D, add_mset {#hd C#} NP,
        {#}, add_mset (- hd C) Q, WS),
       Propagated (hd C) 0 # M, N, U, None,
       add_mset {#hd C#} NP, {#}, {#}, add_mset (- hd C) Q)
      \<in> HH\<close>
    if
      [simp]: \<open>D = None\<close> and
      [simp]: \<open>C \<noteq> []\<close>
    using H hd_C
    by (auto simp: HH_def all_lits_of_mm_add_mset all_lits_of_m_add_mset)

  have ge2_confl:
    \<open>((M, N @ [op_array_of_list C], length N, D, NP, {#}, Q, WS
        (hd C := WS (hd C) @ [length N],
         hd (tl C) :=
           (WS(hd C := WS (hd C) @ [length N])) (hd (tl C)) @
           [length N])),
       M, N @ [C], length N, Some (the D), NP, {#}, {#}, {#})
      \<in> HH\<close>
    if
      [simp]: \<open>D \<noteq> None\<close> and
      C: \<open>C \<noteq> []\<close> \<open>tl C \<noteq> []\<close>
    using H hd_C hd_tl_C dist_C C lits_C
    by (cases C; cases \<open>tl C\<close>)
      (auto simp: HH_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
        clause_to_update_append uminus_\<A>\<^sub>i\<^sub>n_iff literals_are_in_\<L>\<^sub>i\<^sub>n_def)
  have C_ge_2_iff: \<open>2 \<le> length C \<longleftrightarrow> C \<noteq> [] \<and> tl C \<noteq> []\<close>
    by (cases C; cases \<open>tl C\<close>) auto
  show ?thesis
    using assms(3-)
    unfolding init_dt_step_wl_def init_dt_step_l_def option.case_eq_if
      already_propagated_unit_cls_def conflict_propagated_unit_cls_def
      propagate_unit_cls_def S' Let_def prod.case S set_conflict_unit_def add_init_cls_def
      already_propagated_unit_cls_conflict_def
    apply (refine_rcg val)
    subgoal using S'S by (auto simp: HH_def)
    subgoal by fast
    subgoal by (rule hd_C) assumption
    subgoal using H by (auto simp: HH_def)
    subgoal by (rule le1_propa_no_confl)
    subgoal by auto
    subgoal using H hd_C by (cases C)
        (auto simp: HH_def all_lits_of_mm_add_mset all_lits_of_m_add_mset)
    subgoal using H hd_C by (cases C)
        (auto simp: HH_def all_lits_of_mm_add_mset all_lits_of_m_add_mset)
    subgoal unfolding C_ge_2_iff by fast
    subgoal using lits_C .
    subgoal by (rule le2_no_confl)
    subgoal by fast
    subgoal by (rule unit_confl)
    subgoal by (rule hd_C) assumption+
    subgoal using C_ge_2_iff by fast
    subgoal using lits_C .
    subgoal by (rule ge2_confl) assumption+
    done
qed

lemma init_dt_wl_init_dt_l:
  assumes
    S'S: \<open>(S', S) \<in> HH\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close> and
    \<open>\<forall>C\<in>set CS. distinct C\<close>
  shows \<open>init_dt_wl CS S' \<le> \<Down> HH (init_dt_l CS S)\<close>
  using assms
  supply literal_of_nat.simps[simp del]
  apply (induction CS arbitrary: S S')
  subgoal by (simp add: init_dt_wl_def init_dt_l_def)
  subgoal premises p for a CS S S'
    using p(2-)
    unfolding init_dt_wl_def init_dt_l_def nfoldli_simps(2) if_True apply -
    apply (rule bind_refine)
     apply (rule init_dt_step_wl_init_dt_step_l[of _ _]; solves \<open>simp\<close>)
    apply (rule p(1)[unfolded init_dt_wl_def init_dt_l_def]; solves \<open>simp\<close>)
    done
  done

lemma all_lits_of_mm_in_all_lits_of_m_in_iff:
  \<open>set_mset (all_lits_of_mm (mset `# mset CS)) \<subseteq> A \<longleftrightarrow>
    (\<forall>C\<in>set CS. set_mset (all_lits_of_m (mset C)) \<subseteq> A)\<close>
  by (auto simp: all_lits_of_mm_def all_lits_of_m_def)

lemma init_dt_init_dt_l_full:
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    length: \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    dec:\<open>\<forall>s\<in>set (get_trail_wl S). \<not>is_decided s\<close> and
    confl: \<open>get_conflict_wl S = None \<longrightarrow> literals_to_update_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>set_mset (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    no_learned: \<open>get_unit_learned S = {#}\<close> and
    confl_in_clss: \<open>get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS\<close> and
    trail_in_NP: \<open>\<forall>L \<in> lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S\<close> and
    prop_NP: \<open>\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0\<close> and
    upper: \<open>\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L < uint_max\<close> and
    is_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (mset `# mset CS))\<close> and
    lits_upd_confl: \<open>get_conflict_wl S \<noteq> None \<longrightarrow> literals_to_update_wl S = {#}\<close>
  shows
    \<open>init_dt_wl CS S \<le> SPEC(\<lambda>T.
      is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (mset `# mset CS +
          cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<and>
       twl_struct_invs (twl_st_of_wl None T) \<and> twl_stgy_invs (twl_st_of_wl None T) \<and>
       additional_WS_invs (st_l_of_wl None T) \<and>
       correct_watching_init T \<and>
       cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None T))) =
         mset `# mset CS +
         cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) \<and>
      get_unit_learned T = {#} \<and>
      get_learned_wl T = length (get_clauses_wl T) - 1 \<and>
      count_decided (get_trail_wl T) = 0 \<and>
      (get_conflict_wl T \<noteq> None \<longrightarrow> the (get_conflict_wl T) \<in># mset `# mset CS) \<and>
      (\<forall>L \<in> lits_of_l (get_trail_wl T). {#L#} \<in># get_unit_init_clss T) \<and>
      (\<forall>L \<in> set (get_trail_wl T). \<exists>K. L = Propagated K 0) \<and>
      (get_conflict_wl T \<noteq> None \<longrightarrow> literals_to_update_wl T = {#}))\<close>
proof -
  define T where \<open>T = st_l_of_wl None S\<close>
  have CS_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
    using is_\<L>\<^sub>a\<^sub>l\<^sub>l all_lits_of_mm_in_all_lits_of_m_in_iff unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_in_\<L>\<^sub>i\<^sub>n_def
    by blast
  have w_q: \<open>clauses_to_update_l T = {#}\<close>
    by (cases S) (simp add: T_def)
  have tr_T_S: \<open>get_trail_l T = get_trail_wl S\<close> and p_T_S: \<open>literals_to_update_l T = literals_to_update_wl S\<close> and
    c_T_S: \<open>get_conflict_l T = get_conflict_wl S\<close> and
    l_T_S: \<open>get_learned_l T = get_learned_wl S\<close>and
    cl_T_S: \<open>get_clauses_l T = get_clauses_wl S\<close>
    by (cases S; simp add: T_def)+
  have
    dist_T: \<open>\<forall>C \<in> set (rev CS). distinct C\<close> and
    length_T: \<open>\<forall>C \<in> set (rev CS). length C \<ge> 1\<close> and
    struct_T: \<open>twl_struct_invs (twl_st_of None T)\<close> and
    stgy_T: \<open>twl_stgy_invs (twl_st_of None T)\<close> and
    w_q_T: \<open>clauses_to_update_l T = {#}\<close> and
    tr_T: \<open>\<forall>s\<in>set (get_trail_l T). \<not> is_decided s\<close> and
    c_T: \<open>get_conflict_l T = None \<longrightarrow> literals_to_update_l T = uminus `# lit_of `# mset (get_trail_l T)\<close> and
    add_invs_T: \<open>additional_WS_invs T\<close> and
    le_T: \<open>get_learned_l T = length (get_clauses_l T) - 1\<close> and
    confl_in_clss_T: \<open>get_conflict_l T \<noteq> None \<longrightarrow> the (get_conflict_l T) \<in># mset `# mset (rev CS)\<close>
    by (use assms in \<open>simp add: T_def[symmetric]  w_q tr_T_S p_T_S c_T_S l_T_S cl_T_S; fail\<close>)+
  note init = init_dt_full[of \<open>rev CS\<close> T, OF dist_T length_T struct_T w_q_T tr_T c_T
      add_invs_T le_T stgy_T] init_dt_confl_in_clauses[OF confl_in_clss_T]
  have i: \<open>init_dt_l CS T \<le> \<Down> Id (SPEC(\<lambda>T. twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
      cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None T)) =
        mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)) \<and>
      get_learned_l T = length (get_clauses_l T) - 1 \<and> additional_WS_invs T \<and>
      count_decided (get_trail_l T) = 0 \<and>
      (get_conflict_l T \<noteq> None \<longrightarrow> the (get_conflict_l T) \<in># mset `# mset CS)))
      \<close>
    apply (subst init_dt_init_dt_l[of \<open>rev CS\<close>, unfolded rev_rev_ident, symmetric];
        use assms in \<open>simp add: T_def[symmetric]  w_q tr_T_S p_T_S c_T_S l_T_S cl_T_S\<close>)
    apply (intro conjI)
    using init apply (simp_all add: count_decided_def)
    done
  have Un_eq_iff_subset: \<open>A \<union> B = A \<longleftrightarrow> B \<subseteq> A\<close> for A B
    by blast
  have [simp]: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n (A + all_lits_of_mm B) \<longleftrightarrow>
       set_mset (all_lits_of_mm B) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    if \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n A\<close> for A B
    using that by (simp add: isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.literals_are_in_\<L>\<^sub>i\<^sub>n_def
        Un_eq_iff_subset)
  have CS_\<L>\<^sub>a\<^sub>l\<^sub>l': \<open>set_mset (all_lits_of_mm (mset `# mset CS)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using is_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def by (clarsimp simp: HH_def all_lits_of_mm_union)
  have \<open>set_mset (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq>
   set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using S_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (cases S)(clarsimp simp: mset_take_mset_drop_mset' clauses_def HH_def cl_T_S)
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  show ?thesis
    apply (rule order.trans)
     apply (rule conc_trans[OF init_dt_wl_init_dt_l i, of S, unfolded \<L>\<^sub>a\<^sub>l\<^sub>l_def[symmetric]])
    subgoal using clss watch S_\<L>\<^sub>a\<^sub>l\<^sub>l no_learned trail_in_NP prop_NP lits_upd_confl
      by (auto simp: HH_def T_def clauses_def mset_take_mset_drop_mset' get_unit_learned_def
            get_unit_init_clss_def \<L>\<^sub>a\<^sub>l\<^sub>l_def
          simp del: correct_watching_init.simps literal_of_nat.simps)
    subgoal using CS_\<L>\<^sub>a\<^sub>l\<^sub>l by auto
    subgoal using dist .
    subgoal using is_\<L>\<^sub>a\<^sub>l\<^sub>l CS_\<L>\<^sub>a\<^sub>l\<^sub>l' S_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding conc_fun_RES
      by (clarsimp simp: HH_def all_lits_of_mm_union mset_take_mset_drop_mset'
          clauses_def get_unit_learned_def get_unit_init_clss_def \<L>\<^sub>a\<^sub>l\<^sub>l_def
          simp del: literal_of_nat.simps)
    done
qed

lemma init_dt_init_dt_l:
  fixes CS
  defines \<open>S \<equiv> ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    length: \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    upper: \<open>\<forall>C\<in>set CS. \<forall>L\<in>set C. nat_of_lit L < uint_max\<close> and
    is_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (mset `# mset CS))\<close>
  shows
    \<open>init_dt_wl CS S \<le> SPEC(\<lambda>S.
       is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (mset `# mset CS)) \<and>
       twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
       correct_watching S \<and>
       additional_WS_invs (st_l_of_wl None S) \<and>
       get_unit_learned S = {#} \<and>
       count_decided (get_trail_wl S) = 0 \<and>
       get_learned_wl S = length (get_clauses_wl S) - 1 \<and>
       cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) =
         mset `# mset CS \<and>
       (get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS) \<and>
       (\<forall>L\<in>lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S) \<and>
       (\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0) \<and>
       (get_conflict_wl S \<noteq> None \<longrightarrow> literals_to_update_wl S = {#}))\<close>
proof -
  have clss_empty: \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) = {#}\<close>
    by (auto simp: S_def cdcl\<^sub>W_restart_mset.clauses_def)
  have
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    dec:\<open>\<forall>s\<in>set (get_trail_wl S). \<not>is_decided s\<close> and
    confl: \<open>get_conflict_wl S = None \<longrightarrow> literals_to_update_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>set_mset (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    no_learned: \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). UP) S = {#}\<close> and
    learned_nil: \<open>get_unit_learned S = {#}\<close> and
    confl_nil: \<open>get_conflict_wl S = None\<close> and
    trail_in_NP: \<open>\<forall>L\<in>lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S\<close> and
    prop_NP: \<open>\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0\<close>
    unfolding S_def by (auto simp:
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def additional_WS_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def get_unit_learned_def)
  note HH = init_dt_init_dt_l_full[of CS S, unfolded clss_empty,
        OF dist length struct dec confl aff_invs learned stgy_invs watch clss _ learned_nil,
        unfolded empty_neutral trail_in_NP]
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  have \<open>set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<subseteq> set_mset (all_lits_of_m \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    by (fastforce simp: all_lits_of_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_def image_image uminus_lit_swap)
  then have [simp]: \<open>set_mset (all_lits_of_m \<L>\<^sub>a\<^sub>l\<^sub>l) = set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    by (fastforce simp: all_lits_of_m_def \<L>\<^sub>a\<^sub>l\<^sub>l_def image_image uminus_lit_swap
        simp del: literal_of_nat.simps)
  have [simp]: \<open>all_lits_of_atms_m \<A>\<^sub>i\<^sub>n = \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    by (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_def all_lits_of_atms_m_def)
  show ?thesis
    apply (rule order.trans)
     apply (rule HH)
    using upper is_\<L>\<^sub>a\<^sub>l\<^sub>l
    by (clarsimp_all simp: correct_watching.simps isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def clauses_def
        mset_take_mset_drop_mset' get_unit_learned_def confl_nil trail_in_NP prop_NP)
qed

definition (in isasat_input_ops) init_state :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset\<close> where
  \<open>init_state N = (
    let _ = \<A>\<^sub>i\<^sub>n in
    ([]:: (nat, nat clause) ann_lits), (N :: nat clauses), ({#}::nat clauses),
      (None :: nat clause option))\<close>

text \<open>We add a spurious depency to the parameter of the locale:\<close>
definition (in isasat_input_ops) empty_watched :: \<open>nat literal \<Rightarrow> nat list\<close> where
  \<open>empty_watched = (let _ = \<A>\<^sub>i\<^sub>n in (\<lambda>_. []))\<close>

lemma (in isasat_input_ops) empty_watched_alt_def:
  \<open>empty_watched = (\<lambda>_. [])\<close>
  unfolding empty_watched_def Let_def ..

definition (in isasat_input_ops) init_state_wl :: \<open>nat twl_st_wl\<close> where
  \<open>init_state_wl = ([], [[]], 0, None, {#}, {#}, {#}, empty_watched)\<close>

definition (in isasat_input_ops) init_state_wl_heur :: \<open>twl_st_wl_heur_init nres\<close> where
  \<open>init_state_wl_heur = do {
    W \<leftarrow> SPEC (\<lambda>W. (W, empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0);
    vm \<leftarrow> RES (vmtf_init []);
    \<phi> \<leftarrow> SPEC phase_saving;
    RETURN ([], [[]], 0, None, {#}, W, vm, \<phi>, zero_uint32_nat)}\<close>


lemma (in isasat_input_ops) init_state_wl_heur_init_state_wl:
  \<open>(uncurry0 init_state_wl_heur, uncurry0 (RETURN init_state_wl)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>twl_st_heur_init\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
      (auto simp: init_state_wl_heur_def init_state_wl_def
        RES_RETURN_RES bind_RES_RETURN_eq RES_RES_RETURN_RES RETURN_def
        twl_st_heur_init_def
        intro!: RES_refine)

end

text \<open>to get a full SAT:
  \<^item> either we fully apply \<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<close>
  \<^item> or we can stop early.
\<close>
definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T U \<or>
         (CS \<noteq> {#} \<and> cdcl\<^sub>W_restart_mset.clauses U = CS \<and> learned_clss U = {#} \<and>
            conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv U))
  }\<close>

definition (in -) SAT_wl :: \<open>nat clauses_l \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS [];
    let S = isasat_input_ops.init_state_wl (mset \<A>\<^sub>i\<^sub>n');
    T \<leftarrow> isasat_input_ops.init_dt_wl (mset \<A>\<^sub>i\<^sub>n') CS S;
    if get_conflict_wl T \<noteq> None
    then RETURN T
    else if CS = [] then RETURN (([], [], 0, None, {#}, {#}, {#}, \<lambda>_. undefined))
    else do {
       ASSERT (extract_atms_clss CS [] \<noteq> []);
       ASSERT(isasat_input_bounded_nempty (mset \<A>\<^sub>i\<^sub>n'));
       isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset \<A>\<^sub>i\<^sub>n') (finalise_init T)
    }
  }\<close>


definition (in -)map_uint32_of_lit where
  \<open>map_uint32_of_lit = map (uint32_of_nat)\<close>

lemma (in -) map_uint32_of_lit[sepref_fr_rules]:
  \<open>(return o id, RETURN o map_uint32_of_lit) \<in>
     (list_assn uint32_nat_assn)\<^sup>d \<rightarrow>\<^sub>a list_assn uint32_assn\<close>
  unfolding list_assn_pure_conv
  by sepref_to_hoare
   (sep_auto simp: unat_lit_rel_def uint32_nat_rel_def Collect_eq_comp br_def nat_lit_rel_def
      lit_of_natP_def map_uint32_of_lit_def list_rel_def list_all2_op_eq_map_right_iff' comp_def
      list.rel_eq
      simp del: literal_of_nat.simps)



definition initialise_VMTF :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> vmtf_remove_int_option_lst nres\<close> where
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
   RETURN ((A, n, cnext, cnext), [])
  }\<close>

sepref_definition initialise_VMTF_code
  is \<open>uncurry initialise_VMTF\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_remove_conc_option_lst\<close>
  supply nat_of_uint32_int32_assn[sepref_fr_rules]
  unfolding initialise_VMTF_def vmtf_cons_def
  apply (rewrite in "((_, _, _, _), \<hole>)" annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])
  apply (rewrite in "(_, _, _, Some \<hole>)" annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in "WHILE\<^sub>T _ _ (_, _, _, \<hole>)" annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in "do {ASSERT _; let _ = \<hole>; _}" annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>((_, _, _, _), ASSN_ANNOT _ \<hole>)\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _ \<close> array_fold_custom_replicate op_list_replicate_def[symmetric])
  apply (rewrite in "VMTF_Node 0 \<hole> _" annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in "VMTF_Node 0 _ \<hole>" annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

declare initialise_VMTF_code.refine[sepref_fr_rules]


lemma initialise_VMTF:
  shows \<open>(uncurry initialise_VMTF, uncurry (\<lambda>N n. RES (isasat_input_ops.vmtf_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N)]\<^sub>f
      (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow>
      \<langle>(\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel)
        \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
proof -
  have vmtf_ns_notin_empty: \<open>vmtf_ns_notin [] 0 (replicate n (VMTF_Node 0 None None))\<close> for n
    unfolding vmtf_ns_notin_def
    by auto

  have K2: \<open>distinct N \<Longrightarrow> lst < length N \<Longrightarrow> N!lst \<in> set (take lst N) \<Longrightarrow> False\<close>
    for lst x N
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
    subgoal for S N' x2 A' x2a lst cnext
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
        using L_N dist List.last_in_set[of \<open>take lst N'\<close>] set_take_subset[of lst N']
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
      apply (intro conjI)
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
              map_option_option_last)
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

lemma initialise_VMTF_href:
  \<open>(uncurry initialise_VMTF_code, uncurry (\<lambda>N (_::nat). RES (isasat_input_ops.vmtf_init N []))) \<in>
   [\<lambda>(N, n). (\<forall>L\<in>#N. L < n) \<and> distinct_mset N]\<^sub>a
   (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> vmtf_remove_conc_option_lst\<close>
proof -
  have H: \<open>hr_comp (list_assn uint32_assn)
                (\<langle>uint32_nat_rel\<rangle>list_rel O list_mset_rel) = list_mset_assn uint32_nat_assn\<close>
    unfolding list_mset_assn_def list_assn_pure_conv
    by (auto simp: mset_rel_def p2rel_def rel_mset_def list_mset_rel_def list_rel_def
      br_def uint32_nat_rel_def list_all2_op_eq_map_right_iff' Collect_eq_comp list.rel_eq hr_comp_pure
        rel2p_def[abs_def])
  show ?thesis
    using initialise_VMTF_code.refine[FCOMP initialise_VMTF] unfolding H list_rel_mset_rel_def
    by simp
qed

definition finalise_init_code where
  \<open>finalise_init_code = (\<lambda>(M', N', U', D', Q', W', ((ns, m, lst, next_search), to_remove), \<phi>, clvls). 
     (M', N', U', D', Q', W', ((ns, m, the lst, next_search), to_remove), \<phi>, clvls))\<close>

lemma (in isasat_input_ops)finalise_init_finalise_init:
  \<open>(RETURN o finalise_init_code, RETURN o finalise_init) \<in>
   [\<lambda>S. get_conflict_wl S = None \<and> \<A>\<^sub>i\<^sub>n \<noteq> {#}]\<^sub>f twl_st_heur_init \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: finalise_init_def twl_st_heur_def twl_st_heur_init_def
      finalise_init_code_def vmtf_init_def)

sepref_thm (in isasat_input_ops) finalise_init_code'
  is \<open>RETURN o finalise_init_code\<close>
  :: \<open> [\<lambda>(M', N', U', D', Q', W', ((ns, m, lst, next_search), to_remove), \<phi>, clvls). lst \<noteq> None]\<^sub>a
     twl_st_heur_init_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  unfolding finalise_init_code_def twl_st_heur_init_assn_def twl_st_heur_assn_def
  by sepref


concrete_definition (in -) finalise_init_code'
   uses isasat_input_ops.finalise_init_code'.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) finalise_init_code'_def

lemmas (in isasat_input_ops)finalise_init_hnr[sepref_fr_rules] =
   finalise_init_code'.refine[of \<A>\<^sub>i\<^sub>n]

lemma (in isasat_input_ops)finalise_init_code_hnr[sepref_fr_rules]:
  \<open>(finalise_init_code', RETURN o (PR_CONST finalise_init)) \<in>
   [\<lambda>S. get_conflict_wl S = None \<and> \<A>\<^sub>i\<^sub>n \<noteq> {#}]\<^sub>a twl_st_init_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur_init
     (\<lambda>S. get_conflict_wl S = None \<and> \<A>\<^sub>i\<^sub>n \<noteq> {#})
     (\<lambda>_ (M', N', U', D', Q', W', ((ns, m, lst,
         next_search), to_remove), \<phi>, clvls). lst \<noteq> None)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_init_assn\<^sup>d)
                    twl_st_heur_init \<rightarrow> hr_comp
           twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF finalise_init_hnr
    finalise_init_finalise_init] unfolding PR_CONST_def .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_init_def trail_pol_def option_conflict_rel_def
        conflict_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff vmtf_init_def)

  have im: \<open>?im' = ?im\<close> and f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def
    twl_st_assn_def twl_st_heur_init_assn_def twl_st_init_assn_def
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def f apply assumption
    using pre ..
qed


definition extract_model_of_state where
  \<open>extract_model_of_state U = fold (\<lambda>x s. lit_of x # s) (get_trail_wl U) []\<close>

definition IsaSAT :: \<open>nat clauses_l \<Rightarrow> nat literal list option nres\<close> where
  \<open>IsaSAT CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset (extract_atms_clss CS []);
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let S = isasat_input_ops.init_state_wl \<A>\<^sub>i\<^sub>n';
    T \<leftarrow> isasat_input_ops.init_dt_wl \<A>\<^sub>i\<^sub>n' CS S;
    if \<not>get_conflict_wl_is_None_init T
    then RETURN None
    else if CS = [] then RETURN (Some [])
    else do {
       ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
       ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
       let T = finalise_init T;
       U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D \<A>\<^sub>i\<^sub>n' T;
       RETURN (if get_conflict_wl U = None then Some (extract_model_of_state U) else None)
   }
  }\<close>

definition (in -) init_rll :: \<open>nat \<Rightarrow> 'a list list\<close> where
  \<open>init_rll n = []\<close>

lemma (in -)arrayO_raa_empty_sz_init_rll[sepref_fr_rules]:
  \<open>(arrayO_raa_empty_sz, RETURN o init_rll) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a arlO_assn R\<close>
  by sepref_to_hoare (sep_auto simp: init_rll_def)

definition init_lrl :: \<open>nat \<Rightarrow> 'a list list\<close> where
  \<open>init_lrl n = replicate n []\<close>

lemma arrayO_ara_empty_sz_init_lrl: \<open>arrayO_ara_empty_sz n = init_lrl n\<close>
  by (induction n) (auto simp: arrayO_ara_empty_sz_def init_lrl_def)

lemma (in -)arrayO_raa_empty_sz_init_lrl[sepref_fr_rules]:
  \<open>(arrayO_ara_empty_sz_code, RETURN o init_lrl) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl_assn R)\<close>
  using arrayO_ara_empty_sz_code.refine unfolding arrayO_ara_empty_sz_init_lrl .

lemma shiftr1_fref[sepref_fr_rules]: \<open>(return o shiftr1, RETURN o shiftr1) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto


definition init_trail_D :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> trail_pol nres\<close> where
  \<open>init_trail_D \<A>\<^sub>i\<^sub>n n = do {
     let M = replicate n None;
     let M' = replicate n zero_uint32_nat;
     RETURN (([], M, M', zero_uint32_nat))
  }\<close>

sepref_register initialise_VMTF

sepref_definition init_trail_D_code
  is \<open>uncurry init_trail_D\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding init_trail_D_def PR_CONST_def
  apply (rewrite in "((\<hole>, _, _, _))" HOL_list.fold_custom_empty)
  apply (rewrite in "((\<hole>, _, _, _))" annotate_assn[where A=pair_nat_ann_lits_assn])

  apply (rewrite in "let _ = \<hole> in _" annotate_assn[where A=\<open>array_assn (option_assn bool_assn)\<close>])
  apply (rewrite in "let _ = \<hole> in _" annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in "let _ = _ in _" array_fold_custom_replicate)
  apply (rewrite in "let _ = _ in _" array_fold_custom_replicate)
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_code.refine[sepref_fr_rules]

definition init_state_wl_D' :: \<open>uint32 list \<Rightarrow>  (trail_pol \<times> _ list list \<times>
     nat \<times> _) nres\<close> where
  \<open>init_state_wl_D' \<A>\<^sub>i\<^sub>n = do {
     let n = Suc (nat_of_uint32 (fold max \<A>\<^sub>i\<^sub>n 0));
     let m = 2 * n;
     M \<leftarrow> init_trail_D \<A>\<^sub>i\<^sub>n n;
     let e = [];
     let N = init_rll n;
     let N = N @ [e];
     let D = (True, zero_uint32_nat, replicate n None);
     let WS = init_lrl m;
     vm \<leftarrow> initialise_VMTF \<A>\<^sub>i\<^sub>n n;
     let \<phi> = replicate n False;

     RETURN (M, N, 0, D, [], WS, vm, \<phi>, zero_uint32_nat)
  }\<close>

lemma (in -)atm_of_uminus_lit_of_nat: \<open>atm_of (- literal_of_nat x) = x div 2\<close>
  by (cases x) auto


lemma shiftr1_uint_fref: \<open>(return o (\<lambda>n. n >> 1), RETURN o shiftr1) \<in>
   uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by (sepref_to_hoare)
   (sep_auto simp: shiftr1_def uint32_nat_rel_def br_def nat_of_uint32_shiftr)


term isasat_input_ops.twl_st_assn
sepref_definition init_state_wl_D'_code
  is \<open>init_state_wl_D'\<close>
  :: \<open>(list_assn uint32_assn)\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn *assn clauses_ll_assn *assn nat_assn *assn
    conflict_option_rel_assn *assn
    list_assn unat_lit_assn *assn
    (arrayO_assn (arl_assn nat_assn)) *assn
    vmtf_remove_conc_option_lst *assn
    phase_saver_conc *assn uint32_nat_assn\<close>
  unfolding init_state_wl_D'_def
  apply (rewrite at \<open>(_, _, _, \<hole>, _, _)\<close> HOL_list.fold_custom_empty)
  apply (rewrite at \<open>(_, _, _, _, \<hole>, _)\<close> annotate_assn[where A=\<open>list_assn unat_lit_assn\<close>])
  apply (rewrite at \<open>let _ = \<hole> in _\<close> array.fold_custom_empty)
  apply (rewrite at "let _ = \<hole> in _" annotate_assn[where A=\<open>array_assn unat_lit_assn\<close>])
  unfolding array_fold_custom_replicate
  apply (rewrite at "let _ = _; _ = \<hole> in _" annotate_assn[where A=\<open>clauses_ll_assn\<close>])
  apply (rewrite at "let _ = _ @ _; _= _; _= \<hole> in _" annotate_assn[where A=\<open>(arrayO_assn (arl_assn nat_assn))\<close>])
  supply [[goals_limit = 1]]
  by sepref

lemma init_trail_D_ref:
  \<open>(uncurry init_trail_D, uncurry (RETURN oo (\<lambda> _ _. []))) \<in> [\<lambda>(N, n). mset N = \<A>\<^sub>i\<^sub>n \<and>
    distinct N \<and> (\<forall>L\<in>set N. L< n)]\<^sub>f
    \<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow>
   \<langle>isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n\<rangle> nres_rel\<close>
proof -
  have K: \<open>(\<forall>L\<in>set N. nat_of_uint32 L < n) \<longleftrightarrow>
     (\<forall>L \<in># (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (nat_of_uint32 `# mset N)). atm_of L < n)\<close> for N n
     (*TODO proof*)
    apply (auto simp: nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    by (metis (full_types) UnCI image_eqI literal.sel(1))

  show ?thesis
    unfolding init_trail_D_def
    apply (intro frefI nres_relI)
    unfolding uncurry_def Let_def comp_def
    apply clarify
    by (auto 5 5 simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
      list_mset_rel_def Collect_eq_comp)
qed

lemma init_state_wl_D':
  \<open>(init_state_wl_D', isasat_input_ops.init_state_wl_heur) \<in>
    [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>f \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel  \<rightarrow>
      \<langle>isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n \<times>\<^sub>r \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>r
         nat_rel \<times>\<^sub>r isasat_input_ops.option_conflict_rel \<A>\<^sub>i\<^sub>n \<times>\<^sub>r list_mset_rel \<times>\<^sub>r \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>r
           Id \<times>\<^sub>r \<langle>bool_rel\<rangle>list_rel\<times>\<^sub>r Id\<rangle>nres_rel\<close>
proof -
  have init_state_wl_heur_alt_def: \<open>isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n = do {
    let M = [];
    let N = [[]];
    let D = None;
    W \<leftarrow> SPEC (\<lambda>W. (W, isasat_input_ops.empty_watched \<A>\<^sub>i\<^sub>n ) \<in> \<langle>Id\<rangle>map_fun_rel (isasat_input_ops.D\<^sub>0 \<A>\<^sub>i\<^sub>n));
    vm \<leftarrow> RES (isasat_input_ops.vmtf_init \<A>\<^sub>i\<^sub>n []);
    \<phi> \<leftarrow> SPEC (isasat_input_ops.phase_saving \<A>\<^sub>i\<^sub>n);
    RETURN (M, N, 0, D, {#}, W, vm, \<phi>, zero_uint32_nat)}\<close> for \<A>\<^sub>i\<^sub>n
    unfolding isasat_input_ops.init_state_wl_heur_def Let_def by auto

  have tr: \<open>distinct_mset \<A>\<^sub>i\<^sub>n \<and> (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. L < b) \<Longrightarrow> (\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
      init_trail_D \<A>\<^sub>i\<^sub>n' b \<le> \<Down> (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) (RETURN [])\<close> for b \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n' x
    by (rule init_trail_D_ref[unfolded fref_def nres_rel_def, simplified, rule_format])
       (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def)
  have [simp]: \<open>comp_fun_idem (max :: 'a::linorder \<Rightarrow> _)\<close>
    unfolding comp_fun_idem_def comp_fun_commute_def comp_fun_idem_axioms_def
    by (auto simp: max_def[abs_def] intro!: ext)
  have [simp]: \<open>fold max x a = Max (insert a (set x))\<close> for x and a :: \<open>'a :: linorder\<close>
    by (auto simp: Max.eq_fold comp_fun_idem.fold_set_fold)
  have in_N0[dest]: \<open>L \<in> set \<A>\<^sub>i\<^sub>n \<Longrightarrow> nat_of_uint32 L  < Suc (nat_of_uint32 (Max (insert 0 (set \<A>\<^sub>i\<^sub>n))))\<close>
    for L \<A>\<^sub>i\<^sub>n
    using Max_ge[of \<open>insert 0 (set \<A>\<^sub>i\<^sub>n)\<close> L]
    apply (auto simp del: Max_ge simp: nat_shiftr_div2 nat_of_uint32_shiftr)
    using div_le_mono le_imp_less_Suc nat_of_uint32_le_iff by blast
  define P where \<open>P x = {(a, b). b = [] \<and> (a, b) \<in> isasat_input_ops.trail_pol x}\<close> for x
  have P: \<open>(c, []) \<in> P x \<longleftrightarrow> (c, []) \<in> isasat_input_ops.trail_pol x\<close> for c x
    unfolding P_def by auto
  have init: \<open>init_trail_D \<A>\<^sub>i\<^sub>n' (Suc (nat_of_uint32 (fold max \<A>\<^sub>i\<^sub>n' 0))) \<le>
     SPEC (\<lambda>c. (c, []) \<in> P \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>distinct_mset \<A>\<^sub>i\<^sub>n\<close> and x: \<open>(\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    for \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n'
    unfolding x P
    by (rule tr[unfolded conc_fun_RETURN])
       (use that in \<open>auto simp: shiftr1_def nat_shiftr_div2 nat_of_uint32_shiftr list_rel_mset_rel_def
      list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff' list_mset_rel_def\<close>)

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
      list_rel_mset_rel_def list_rel_mset_rel_def
      list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff' list_mset_rel_def
     intro!: nth_replicate dest!: in_N0
     simp del: replicate.simps)
  have initialise_VMTF: \<open>(\<forall>L\<in>#aa. L < b) \<and> distinct_mset aa \<and> (a, aa) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
        initialise_VMTF a b \<le> RES (isasat_input_ops.vmtf_init aa [])\<close>
    for aa b a
    using initialise_VMTF[unfolded fref_def nres_rel_def] by auto
  have [simp]: \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow> L \<in># y \<Longrightarrow> L < Suc (nat_of_uint32 (Max (insert 0 (set x))))\<close>
    for x y L
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def uint32_nat_rel_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def)

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

  show ?thesis
    apply (intro frefI nres_relI)
    subgoal for x y
    unfolding init_state_wl_heur_alt_def init_state_wl_D'_def
    apply (rewrite in \<open>let _ = Suc _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = 2 * _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = [] in _\<close> Let_def)
    apply (rewrite in \<open>let _ = init_rll _ in _\<close> Let_def)
    apply (refine_vcg init[of y x] initialise_VMTF)
    subgoal by auto
    subgoal using H by (auto simp: P_def init_rll_def init_lrl_def)
    apply assumption
    subgoal by simp
    subgoal unfolding isasat_input_ops.phase_saving_def by auto
    subgoal by (auto simp: P_def init_rll_def isasat_input_ops.option_conflict_rel_def
          isasat_input_ops.conflict_rel_def
          simp del: replicate.simps
          intro!: mset_as_position.intros)
    done
  done
qed

lemma init_state_wl_heur_hnr:
  \<open>(init_state_wl_D'_code, isasat_input_ops.init_state_wl_heur)
    \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
      (hr_comp (list_assn uint32_assn) (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel))\<^sup>k \<rightarrow>
      isasat_input_ops.twl_st_heur_init_assn \<A>\<^sub>i\<^sub>n\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and>
          distinct_mset
           \<A>\<^sub>i\<^sub>n]\<^sub>a (hr_comp (list_assn uint32_assn)
                    (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel))\<^sup>k \<rightarrow>
      hr_comp trail_pol_assn (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) *assn
      hr_comp clauses_ll_assn (\<langle>\<langle>nat_lit_lit_rel\<rangle>list_rel\<rangle>list_rel) *assn
      nat_assn *assn
      hr_comp conflict_option_rel_assn (isasat_input_ops.option_conflict_rel \<A>\<^sub>i\<^sub>n) *assn
      hr_comp (list_assn unat_lit_assn) list_mset_rel *assn
      hr_comp (arrayO_assn (arl_assn nat_assn)) (\<langle>\<langle>nat_rel\<rangle>list_rel\<rangle>list_rel) *assn
      vmtf_remove_conc_option_lst *assn hr_comp phase_saver_conc (\<langle>bool_rel\<rangle>list_rel) *assn
      uint32_nat_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  init_state_wl_D'_code.refine[FCOMP init_state_wl_D', of \<A>\<^sub>i\<^sub>n] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def by fast
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep isasat_input_ops.twl_st_heur_init_assn_def
      isasat_input_ops.conflict_option_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def list_assn_list_mset_rel_eq_list_mset_assn)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f apply assumption
    using pre ..
qed

lemma init_state_wl_heur_init_state_wl:
  \<open>(isasat_input_ops.init_state_wl_heur, RETURN o isasat_input_ops.init_state_wl)
  \<in> [\<lambda>N. N = \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<rightarrow> \<langle>isasat_input_ops.twl_st_heur_init
                    \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  using isasat_input_ops.init_state_wl_heur_init_state_wl
  unfolding fref_def nres_rel_def
  by auto

lemma init_state_wl_D'_code_ref[sepref_fr_rules]:
  \<open>(init_state_wl_D'_code, RETURN o isasat_input_ops.init_state_wl) \<in>
    [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a (list_mset_assn uint32_nat_assn)\<^sup>k \<rightarrow>
      isasat_input_ops.twl_st_init_assn \<A>\<^sub>i\<^sub>n\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset
         \<A>\<^sub>i\<^sub>n]\<^sub>a (hr_comp
                  (list_assn uint32_assn)
                  (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel),
                 hr_comp
                  (list_assn uint32_assn)
                  (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel)) \<rightarrow> hr_comp
          (isasat_input_ops.twl_st_heur_init_assn
            \<A>\<^sub>i\<^sub>n)
          (isasat_input_ops.twl_st_heur_init \<A>\<^sub>i\<^sub>n)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using init_state_wl_heur_hnr[FCOMP init_state_wl_heur_init_state_wl, of \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n, simplified] .
  have im: \<open>?im' = ?im\<close>
    by (auto simp: list_mset_assn_def list_rel_mset_rel_def hr_comp_assoc[symmetric]
        list_assn_comp list_assn_list_mset_rel_eq_list_mset_assn)
  show ?thesis
    using H unfolding im isasat_input_ops.twl_st_init_assn_def[symmetric] .
qed


text \<open>It is not possible to discharge assumption of the rule directly, but here, it works. This avoids
  guessing form the \<open>sepref\<close> tools:\<close>
declare init_state_wl_D'_code_ref[to_hnr, OF refl, sepref_fr_rules]

lemma [sepref_fr_rules]:
  \<open>(return o uint32_of_nat, RETURN o uint32_of_nat) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_assn\<close>
  by sepref_to_hoare sep_auto

lemmas (in isasat_input_bounded)init_dt_wl_code_refine'[sepref_fr_rules] =
  init_dt_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma (in -)id_mset_list_assn_list_mset_assn:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(return o id, RETURN o mset) \<in> (list_assn R)\<^sup>d \<rightarrow>\<^sub>a list_mset_assn R\<close>
proof -
  obtain R' where R: \<open>R = pure R'\<close>
    using assms is_pure_conv unfolding CONSTRAINT_def by blast
  then have R': \<open>the_pure R = R'\<close>
    unfolding R by auto
  show ?thesis
    apply (subst R)
    apply (subst list_assn_pure_conv)
    apply sepref_to_hoare
    by (sep_auto simp: list_mset_assn_def R' pure_def list_mset_rel_def mset_rel_def
       p2rel_def rel2p_def[abs_def] rel_mset_def br_def Collect_eq_comp list_rel_def)
qed

lemma cdcl_twl_stgy_prog_wl_D_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_prog_wl_D_code), uncurry isasat_input_ops.cdcl_twl_stgy_prog_wl_D)
  \<in> [\<lambda>(N, _). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n]\<^sub>a
     (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    apply (cases a)
    by (sep_auto
      dest!: frame_rule_left[of \<open>isasat_input_ops.twl_st_assn _ _ _\<close> _ _\<open>list_mset_assn uint32_nat_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done

declare cdcl_twl_stgy_prog_wl_D_code_ref'[to_hnr, OF refl, sepref_fr_rules]

lemma init_dt_wl_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 (\<lambda>_. init_dt_wl_code), uncurry2 (isasat_input_ops.init_dt_wl))
  \<in> [\<lambda>((N, S), S'). isasat_input_bounded N \<and> N = \<A>\<^sub>i\<^sub>n]\<^sub>a
    (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a
      (isasat_input_ops.twl_st_init_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow>
    isasat_input_ops.twl_st_init_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding PR_CONST_def
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using init_dt_wl_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>(snd (fst c), snd c)\<close> \<open>(snd (fst a), snd a)\<close>]
    by (cases a)
       (sep_auto dest!: frame_rule_left[of \<open>_ * isasat_input_ops.twl_st_init_assn _ _ _\<close> _ _
            \<open>list_mset_assn uint32_nat_assn \<A>\<^sub>i\<^sub>n (fst (fst a))\<close>])
  done

lemma pair_nat_ann_lits_assn_alt_def:
  \<open>pair_nat_ann_lits_assn at ag =  list_assn (\<lambda>a c. \<up> ((c, a) \<in> nat_ann_lit_rel)) at ag\<close>
  by (auto simp: nat_ann_lit_rel_def pure_def)

definition get_trail_wl_code :: \<open> twl_st_wll_trail \<Rightarrow> (uint32 \<times> nat option) list\<close> where
  \<open>get_trail_wl_code = (\<lambda>((M, _), _). M)\<close>

lemma (in isasat_input_bounded) get_trail_wl[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code, RETURN o get_trail_wl) \<in>  twl_st_assn\<^sup>d \<rightarrow>\<^sub>a  pair_nat_ann_lits_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: twl_st_assn_def twl_st_heur_def hr_comp_def trail_pol_def twl_st_heur_assn_def
      pair_nat_ann_lits_assn_alt_def[symmetric] twl_st_heur_init_assn_def get_trail_wl_code_def)

lemma [sepref_fr_rules]:
  \<open>(return o get_trail_wl_code,
   RETURN \<circ> get_trail_wl) \<in> [\<lambda>_. isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>a (isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> pair_nat_ann_lits_assn\<close>
  using isasat_input_bounded.get_trail_wl[of \<A>\<^sub>i\<^sub>n] by (auto simp: hfref_def)

lemma extract_model_of_state_alt_def:
  \<open>extract_model_of_state U = rev (map lit_of (get_trail_wl U))\<close>
proof -
  have [simp]: \<open>fold (\<lambda>x. op # (lit_of x)) U s = rev (map lit_of U) @ s\<close> for U s
    unfolding foldl_conv_fold[symmetric]
    by (induction U arbitrary: s)  auto
  show ?thesis
    unfolding extract_model_of_state_def by auto
qed

sepref_definition extract_model_of_state_code
  is \<open>RETURN o extract_model_of_state\<close>
  :: \<open>[\<lambda>_. isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>a (isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> list_assn unat_lit_assn\<close>
  unfolding extract_model_of_state_def map_by_foldl[symmetric]
     comp_def foldl_conv_fold foldl_conv_fold
  unfolding HOL_list.fold_custom_empty
  supply [[goals_limit = 1]]
  by sepref


declare extract_model_of_state_code.refine[sepref_fr_rules]
declare isasat_input_ops.finalise_init_code_hnr[unfolded PR_CONST_def, sepref_fr_rules]

sepref_definition IsaSAT_code
  is \<open>IsaSAT\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a option_assn (list_assn unat_lit_assn)\<close>
  unfolding IsaSAT_def
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
  supply isasat_input_bounded.init_dt_wl_code_refine'[sepref_fr_rules] get_conflict_wl_is_None_init_def[simp]
  isasat_input_bounded.get_conflict_wl_is_None_code_get_conflict_wl_is_None[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_code_get_conflict_wl_is_None_no_lvls[sepref_fr_rules]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>Some \<hole>\<close> HOL_list.fold_custom_empty)
  supply [[goals_limit = 1]]
  by sepref

code_printing constant nth_u_code \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt _))"

code_printing constant heap_array_set'_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"

export_code IsaSAT_code checking SML_imp
export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
  in SML_imp module_name SAT_Solver file "code/IsaSAT_solver.sml"

definition TWL_to_clauses_state_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset) set\<close> where
  \<open>TWL_to_clauses_state_conv = {(S', S). S = state\<^sub>W_of (twl_st_of_wl None S')}\<close>

(* TODO Move *)
lemma (in -) true_clss_cls_empty_empty[iff]:
  \<open>{} \<Turnstile>p {#} \<longleftrightarrow> False\<close>
  unfolding true_clss_cls_def consistent_interp_def by auto

lemma full_cdcl\<^sub>W_init_state:
  \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding full_def rtranclp_unfold
  by (subst tranclp_unfold_begin)
     (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

(* End Move *)
lemma extract_atms_cls_empty_iff: \<open>extract_atms_cls Cs C0 = [] \<longleftrightarrow> (C0 = [] \<and> Cs = [])\<close>
  unfolding extract_atms_cls_def
  by (induction Cs arbitrary: C0) force+

lemma extract_atms_clss_empty_iff:
   \<open>extract_atms_clss CS C0  = [] \<longleftrightarrow> (C0 = [] \<and> (\<forall>C \<in> set CS. C = []))\<close>
proof -
  have \<open>fold extract_atms_cls Cs C0 = [] \<longleftrightarrow> (C0 = [] \<and> (\<forall>C \<in> set Cs. C = []))\<close> for Cs
    unfolding extract_atms_clss_def
    apply (induction Cs arbitrary: C0)
    subgoal by auto
    subgoal by (auto simp: extract_atms_cls_empty_iff)
    done
  then show ?thesis
    unfolding extract_atms_clss_def .
qed

lemma cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and> (\<forall>C \<in># CS. size C \<ge> 1) \<and>
        (\<forall>C \<in># CS. \<forall>L \<in># C. nat_of_lit L < uint_max)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>TWL_to_clauses_state_conv\<rangle>nres_rel\<close>
proof -
  have in_list_mset_rel: \<open>(CS', y) \<in> list_mset_rel \<longleftrightarrow> y = mset CS'\<close> for CS' y
    by (auto simp: list_mset_rel_def br_def)
  have in_list_mset_rel_mset_rel:
    \<open>(mset CS', CS) \<in> \<langle>list_mset_rel\<rangle>mset_rel \<longleftrightarrow> CS = mset `# mset CS'\<close> for CS CS'
    by (auto simp: list_mset_rel_def br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)

  have \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' [])) (all_lits_of_mm (mset `# mset CS'))\<close>
    for CS'
    by (auto simp add: isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
      all_lits_of_mm_add_mset in_extract_atms_clssD in_extract_atms_clsD
      all_lits_of_mm_def atms_of_s_def image_image image_Un)
  have extract_nempty: \<open>extract_atms_clss xs [] \<noteq> []\<close>
  if
    H: \<open>Multiset.Ball ys distinct_mset \<and> (\<forall>C\<in>#ys. 1 \<le> size C) \<and> (\<forall>C\<in>#ys. \<forall>L\<in>#C. nat_of_lit L < uint_max)\<close> and
    rel: \<open>(xs, ys) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
    le_xs: \<open>length xs \<noteq> 0\<close>
  for xs ys
  proof -
    obtain x xs' where [simp]: \<open>xs = x # xs'\<close>
      using le_xs by (cases xs) auto
    obtain xy where
      xs_xy: \<open>(xs, xy) \<in> list_mset_rel\<close> and xy_ys: \<open>(xy, ys) \<in> \<langle>list_mset_rel\<rangle>mset_rel\<close>
      using rel by auto
    have xy[simp]: \<open>xy = mset xs\<close>
      using xs_xy by (auto simp: list_mset_rel_def br_def)
    have \<open>mset x \<in># ys\<close>
      using in_list_mset_rel_mset_rel[THEN iffD1, OF xy_ys[unfolded xy]]
      by auto
    then have [simp]: \<open>x \<noteq> []\<close>
      using H by auto
    show ?thesis
      by (auto simp: extract_atms_clss_empty_iff extract_atms_cls_empty_iff)
  qed
  have if_no_confl_ref:
    \<open>(if get_conflict_wl S\<^sub>0 \<noteq> None then RETURN S\<^sub>0
      else if CS' = [] then RETURN ([], [], 0, None, {#}, {#}, {#}, \<lambda>_. undefined)
       else
         do{ ASSERT (extract_atms_clss CS' [] \<noteq> []);
             ASSERT(isasat_input_bounded_nempty (mset (extract_atms_clss CS' [])));
             isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) S\<^sub>0})
    \<le> \<Down> TWL_to_clauses_state_conv
        (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                    (CS \<noteq> {#} \<and> cdcl\<^sub>W_restart_mset.clauses U = CS \<and> learned_clss U = {#} \<and> conflicting U \<noteq> None
                    \<and> backtrack_lvl U = 0 \<and> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv U)))\<close>
    if
      CS_p: \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. 1 \<le> size C) \<and>
         (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L < uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close> and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S\<^sub>0)\<close> and
      corr_w: \<open>correct_watching S\<^sub>0\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S\<^sub>0)\<close> and
      UP: \<open>get_unit_learned S\<^sub>0 = {#}\<close> and
      count_dec: \<open>count_decided (get_trail_wl S\<^sub>0) = 0\<close> and
      U: \<open>get_learned_wl S\<^sub>0 = length (get_clauses_wl S\<^sub>0) - 1\<close> and
      clss: \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0))) = mset `# mset CS'\<close> and
      trail: \<open>(\<forall>L\<in>lits_of_l (get_trail_wl S\<^sub>0). {#L#} \<in># get_unit_init_clss S\<^sub>0) \<and> (\<forall>L\<in>set (get_trail_wl S\<^sub>0). \<exists>K. L = Propagated K 0)\<close>
    for CS CS' S\<^sub>0
  proof (cases \<open>get_conflict_wl S\<^sub>0 = None\<close>)
    case False
    then have confl: \<open>get_conflict_wl S\<^sub>0 = None \<longleftrightarrow> False\<close>
      by auto
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of (twl_st_of_wl None S\<^sub>0))\<close>
      using struct_invs unfolding twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then have H: \<open>get_trail_wl S\<^sub>0 = []\<close> if \<open>CS = {#}\<close>
      using add_invs that CS clss count_dec U
      by (cases S\<^sub>0; cases \<open>get_trail_wl S\<^sub>0\<close>; cases \<open>hd (get_trail_wl S\<^sub>0)\<close> )
        (auto simp: clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        cdcl\<^sub>W_restart_mset_state additional_WS_invs_def split: if_splits)
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S\<^sub>0))\<close>
      using struct_invs unfolding twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    then have [simp]: \<open>CS' \<noteq> []\<close>
      using clss False CS H le
      by (cases S\<^sub>0)
         (auto simp add: clauses_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
        cdcl\<^sub>W_restart_mset_state  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    show ?thesis
      unfolding confl if_False apply simp
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0))\<close>])
      apply (intro conjI)
     subgoal by (cases S\<^sub>0) (clarsimp_all simp: TWL_to_clauses_state_conv_def mset_take_mset_drop_mset'
          clauses_def get_unit_learned_def in_list_mset_rel in_list_mset_rel_mset_rel)
     subgoal
       apply (rule disjI2)
       using \<L>\<^sub>a\<^sub>l\<^sub>l struct_invs stgy_invs corr_w UP count_dec U clss trail False
       by (cases S\<^sub>0) (clarsimp simp: twl_struct_invs_def CS isasat_input_ops.init_state_def full_def
           get_unit_learned_def cdcl\<^sub>W_restart_mset_state)
      done
  next
    case True
    then have confl: \<open>get_conflict_wl S\<^sub>0 = None \<longleftrightarrow> True\<close>
      by auto
    obtain M N NP Q W where
      S\<^sub>0: \<open>S\<^sub>0 = (M, N, length N - 1, None, NP, {#}, Q, W)\<close>
      using stgy_invs UP U True by (cases S\<^sub>0) (auto simp: clauses_def mset_take_mset_drop_mset' get_unit_learned_def)
    have N_NP: \<open>mset `# mset (tl N) + NP = mset `# mset CS'\<close>
      using clss by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0)
    have trail_in_NP: \<open>\<forall>L\<in>lits_of_l M. {#L#} \<in># NP\<close>
      using trail unfolding S\<^sub>0 by (auto simp: get_unit_init_clss_def)
    have n_d: \<open>no_dup M\<close>
      using struct_invs by (auto simp: twl_struct_invs_def S\<^sub>0
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
    have prop_M: \<open>\<forall>L\<in> set M. \<exists>K. L = Propagated K 0\<close>
      using trail by (auto simp: S\<^sub>0)
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have 0: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], CS, {#}, None)
       (convert_lits_l N M, mset `# mset CS', {#}, None)\<close>
      using trail_in_NP prop_M n_d
      apply (induction M)
      subgoal by (auto simp: CS)
      subgoal for L M
        apply (rule rtranclp.rtrancl_into_rtrancl)
         apply (simp; fail)
        apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
         apply (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def CS
            N_NP[symmetric])
        done
      done
    then have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state CS)
       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0)))\<close>
      using 0 by (auto simp: S\<^sub>0 CS mset_take_mset_drop_mset' N_NP init_state.simps)

    have \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' [])) (all_lits_of_mm (mset `# mset CS'))\<close>
      by (auto simp add: isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
        all_lits_of_mm_add_mset in_extract_atms_clssD in_extract_atms_clsD
        all_lits_of_mm_def atms_of_s_def image_image image_Un)
    have [simp]: \<open>isasat_input_bounded (mset (extract_atms_clss CS' []))\<close>
      unfolding isasat_input_bounded_def
    proof
      fix L
      assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))\<close>
      then obtain C where
        L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
        by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
           isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
      have \<open>\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L < uint_max\<close>
        using CS_p by auto
      then have \<open>nat_of_lit L < uint_max \<or> nat_of_lit (-L) < uint_max\<close>
        using L unfolding CS by auto
      then show \<open>nat_of_lit L < uint_max\<close>
        using L
        by (cases L) (auto simp: CS in_extract_atms_clssD uint_max_def)
    qed
    then have 2: \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) S\<^sub>0
       \<le> SPEC (\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0)))
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None T))))\<close>
      using isasat_input_bounded.cdcl_twl_stgy_prog_wl_spec_final2[of
              \<open>mset (extract_atms_clss CS' [])\<close> S\<^sub>0]  CS_p \<L>\<^sub>a\<^sub>l\<^sub>l
            struct_invs stgy_invs corr_w add_invs clss 1 True by auto
    have [simp]: \<open>extract_atms_clss CS' [] \<noteq> []\<close> if \<open>CS' \<noteq> []\<close>
      apply (rule extract_nempty)
        apply (rule CS_p)
       apply (rule CS'_CS)
      using that by (auto simp: extract_atms_clss_empty_iff)
    have [simp]: \<open>isasat_input_bounded_nempty (mset (extract_atms_clss CS' []))\<close> if \<open>CS' \<noteq> []\<close>
      by (auto simp: isasat_input_bounded_nempty_def
          isasat_input_bounded_nempty_axioms_def that)

    have empty_trail: \<open>RETURN ([], [], 0, None, {#}, {#}, {#}, \<lambda>_. undefined)
    \<le> \<Down> TWL_to_clauses_state_conv
        (SPEC
          (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS)
                U \<or>
               CS \<noteq> {#} \<and>
               cdcl\<^sub>W_restart_mset.clauses U = CS \<and>
               learned_clss U = {#} \<and>
               (\<exists>y. conflicting U = Some y) \<and>
               backtrack_lvl U = 0 \<and>
               cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv U))\<close> if \<open>CS' = []\<close>
    proof -
      have [simp]:\<open>CS = {#}\<close>
        using that CS'_CS by (auto simp: list_mset_rel_def br_def)
      show ?thesis
        unfolding TWL_to_clauses_state_conv_def
        by (rule RETURN_SPEC_refine) (use full_cdcl\<^sub>W_init_state in auto)
    qed
    have \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) S\<^sub>0
      \<le> \<Down> TWL_to_clauses_state_conv
      (SPEC (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS)))\<close>
      by (auto simp: TWL_to_clauses_state_conv_def conc_fun_RES rtranclp_fullI
          intro!: weaken_SPEC[OF SPEC_add_information[OF 1 2]])
    then show ?thesis
      unfolding confl if_True
      by (auto intro: ref_two_step empty_trail)
  qed
  have [simp]: \<open>isasat_input_bounded (mset (extract_atms_clss CS' []))\<close>
    if CS_p: \<open>\<forall>C\<in>set CS'. \<forall>L\<in>set C. nat_of_lit L < uint_max\<close>
    for CS'
  unfolding isasat_input_bounded_def
      proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))\<close>
    then obtain C where
      L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have \<open>nat_of_lit L < uint_max \<or> nat_of_lit (-L) < uint_max\<close>
      using L CS_p by auto
    then show \<open>nat_of_lit L < uint_max\<close>
      using L
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def)
  qed

  show ?thesis
    unfolding SAT_wl_def SAT_def
     isasat_input_ops.empty_watched_alt_def finalise_init_def id_def
    apply (intro frefI nres_relI)
    subgoal for x y
      apply (rewrite at \<open>let _ = extract_atms_clss _ _ in _\<close> Let_def)
      apply (rewrite at \<open>let _ = isasat_input_ops.init_state_wl _ in _\<close> Let_def)
      apply (simp only: if_False isasat_input_ops.init_state_wl_def
          isasat_input_ops.empty_watched_alt_def)
      apply (refine_vcg bind_refine_spec isasat_input_bounded.init_dt_init_dt_l)
      subgoal by (rule if_no_confl_ref; auto)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal using \<L>\<^sub>a\<^sub>l\<^sub>l by simp
      done
    done
qed

definition model_if_satisfiable :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>model_if_satisfiable CS = SPEC (\<lambda>M.
           if satisfiable (set_mset CS) then M \<noteq> None \<and> set (the M) \<Turnstile>sm CS else M = None)\<close>

definition SAT' :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>SAT' CS = do {
     T \<leftarrow> SAT CS;
     RETURN(if conflicting T = None then Some(rev (map lit_of (trail T))) else None)
  }
\<close>


context conflict_driven_clause_learning\<^sub>W
begin

lemma rtranclp_cdcl\<^sub>W_restart_learned_clauses_entailed:
  assumes
    \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
  using assms(1)
proof induction
  case base
  then show ?case using assms by fast
next
  case (step T U) note ST = this(1) and TU = this(2) and learned = this(3)
  have \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using assms(2) rtranclp_cdcl\<^sub>W_all_struct_inv_inv step.hyps(1) by blast
  then have l: \<open>cdcl\<^sub>W_learned_clause T\<close>
    by (auto simp: cdcl\<^sub>W_all_struct_inv_def)
  from TU l learned show ?case
    by (rule cdcl\<^sub>W_learned_clauses_entailed)
qed

lemma rtranclp_cdcl\<^sub>W_stgy_learned_clauses_entailed:
  assumes
    \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
  using assms rtranclp_cdcl\<^sub>W_restart_learned_clauses_entailed
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
end

lemma conflict_of_level_unsatisfiable:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses S))\<close>
proof -

  obtain M N U D where S: \<open>S = (M, N, U, Some D)\<close>
    by (cases S) (use confl in auto)

  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition)
      (use dec in \<open>auto simp: count_decided_def filter_empty_conv S \<close>)
  have
    N_U: \<open>N \<Turnstile>psm U\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    N_U_M: \<open>set_mset N \<union> set_mset U \<Turnstile>ps unmark_l M\<close> and
    n_d: \<open>no_dup M\<close> and
    N_U_D: \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using assms
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def all_decomposition_implies_def
        S clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
  have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close>
    by (rule true_clss_clss_true_clss_cls_true_clss_clss[OF N_U_M M_D])
  then have \<open>set_mset N \<Turnstile>ps CNot D\<close> \<open>set_mset N \<Turnstile>p D\<close>
    using N_U N_U_D true_clss_clss_left_right by blast+
  then have \<open>unsatisfiable (set_mset N)\<close>
    by (rule true_clss_clss_CNot_true_clss_cls_unsatisfiable)

  then show ?thesis
    by (auto simp: S clauses_def dest: satisfiable_decreasing)
qed

lemma SAT_model_if_satisfiable:
  \<open>(SAT', model_if_satisfiable) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and> (\<forall>C \<in># CS. size C \<ge> 1)]\<^sub>f Id\<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in>[\<lambda>CS. ?P CS]\<^sub>f Id \<rightarrow> _\<close>)
proof -
  have H: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (init_state CS)\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (init_state CS)\<close>
    if \<open>?P CS\<close> for CS
    using that by (auto simp:
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def additional_WS_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def get_unit_learned_def
        distinct_mset_set_def)
  show ?thesis
    unfolding SAT'_def model_if_satisfiable_def SAT_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      using H[of CS]
        cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>init_state CS\<close>]
      by (fastforce intro!: le_SPEC_bindI simp: RES_RETURN_RES clauses_def
          true_annots_true_cls lits_of_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
          dest: conflict_of_level_unsatisfiable)
    done
qed

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn unat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have ex_remove_xs: \<open>(\<exists>xs. mset xs = mset x \<and> {#literal_of_nat (nat_of_uint32 x). x \<in># mset xs#} = y) \<longleftrightarrow>
       ({#literal_of_nat (nat_of_uint32 x). x \<in># mset x#} = y)\<close>
    for x y
    by auto

  show ?thesis
    unfolding list_assn_pure_conv list_mset_assn_pure_conv list_mset_assn_pure_conv list_rel_mset_rel_internal
    apply (auto simp: hr_comp_def)
    apply (auto simp: ent_ex_up_swap list_mset_assn_def pure_def)
    using ex_mset[of \<open>map (\<lambda>x. literal_of_nat (nat_of_uint32 x)) `# mset xs'\<close>]
    by (auto simp add: list_mset_rel_def br_def mset_rel_def unat_lit_rel_def
        uint32_nat_rel_def nat_lit_rel_def
        p2rel_def Collect_eq_comp rel2p_def lit_of_natP_def[abs_def]
        list_all2_op_eq_map_map_right_iff rel_mset_def rel2p_def[abs_def]
        list_all2_op_eq_map_right_iff' ex_remove_xs list_rel_def
        list_all2_op_eq_map_right_iff
        simp del: literal_of_nat.simps)
qed

lemma IsaSAT_code: \<open>(IsaSAT_code, SAT')
    \<in> [\<lambda>x. Multiset.Ball x distinct_mset \<and> (\<forall>C\<in>#x. Suc 0 \<le> size C) \<and>
         (\<forall>C\<in>#x. \<forall>L\<in>#C. nat_of_lit L < uint_max)]\<^sub>a
      clauses_l_assn\<^sup>k \<rightarrow> option_assn (list_assn unat_lit_assn)\<close>
proof -
  define empty_trail where
     \<open>empty_trail = Some ([] :: nat literal list)\<close>
  have IsaSAT: \<open>IsaSAT CS =
    do {
     ASSERT (isasat_input_bounded (mset (extract_atms_clss CS [])));
     ASSERT (distinct (extract_atms_clss CS []));
     T \<leftarrow> SAT_wl CS;
     RETURN (if get_conflict_wl T = None then Some (extract_model_of_state T) else None)
    }\<close> for CS
    unfolding IsaSAT_def SAT_wl_def Let_def get_conflict_wl_is_None_init_def
     finalise_init_def id_def get_conflict_wl_is_None[symmetric] empty_trail_def
    by (force cong: bind_cong simp: extract_model_of_state_def intro: bind_cong)

  have 2: \<open>Multiset.Ball y distinct_mset \<and>
       (\<forall>C\<in>#y. 1 \<le> size C)\<Longrightarrow>
       (x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<Longrightarrow>
        (\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L < uint_max) \<Longrightarrow>
       SAT_wl x \<le> \<Down> TWL_to_clauses_state_conv (SAT y)\<close> for x y
    using cdcl_twl_stgy_prog_wl_spec_final2[unfolded fref_def nres_rel_def] by simp
  have [simp]: \<open>SAT {#} = SPEC (\<lambda>U. U = init_state {#})\<close>
    using full_cdcl\<^sub>W_init_state unfolding SAT_def Let_def
    by auto
  have SAT': \<open>SAT' CS =
       do {
        ASSERT(True);ASSERT(True);
          U \<leftarrow> SAT CS;
          RETURN(if conflicting U = None then Some (rev (map lit_of (trail U))) else None)
      } \<close> for CS
    unfolding SAT'_def SAT_def empty_trail_def by (auto simp: RES_RETURN_RES)
  have 3: \<open>ASSERT (isasat_input_bounded (mset (extract_atms_clss x []))) \<le> \<Down> unit_rel (ASSERT True)\<close>
    if CS_p: \<open>(\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L < uint_max)\<close> and
       CS: \<open>(x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close>
       for x y
    apply (rule ASSERT_refine)
    unfolding isasat_input_bounded_def
  proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss x []))\<close>
    then obtain C where
      L: \<open>C\<in>set x \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
         isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have \<open>\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L < uint_max\<close>
      using CS_p by auto
    then have \<open>nat_of_lit L < uint_max \<or> nat_of_lit (-L) < uint_max\<close>
      using L CS by (auto simp: list_mset_rel_def br_def mset_rel_def rel2p_def[abs_def] p2rel_def
        rel_mset_def list_all2_op_eq_map_right_iff')
    then show \<open>nat_of_lit L < uint_max\<close>
      using L
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def)
  qed
  have 4: \<open>ASSERT (distinct (extract_atms_clss x [])) \<le> \<Down> unit_rel (ASSERT True)\<close> for x
    by (auto simp: distinct_extract_atms_clss)
  have IsaSAT_SAT: \<open>(IsaSAT, SAT')\<in>
     [\<lambda>CS. Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. 1 \<le> size C) \<and>
      (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L < uint_max)]\<^sub>f
     list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle> option_rel\<rangle>nres_rel\<close>
    unfolding SAT' IsaSAT
    apply (intro frefI nres_relI bind_refine if_refine)
         apply (rule 3; simp; fail)
        apply (rule 4; simp; fail)
     apply (rule 2)
    by (auto simp: TWL_to_clauses_state_conv_def convert_lits_l_def extract_model_of_state_alt_def)
  show ?thesis
    using IsaSAT_code.refine[FCOMP IsaSAT_SAT] unfolding list_assn_list_mset_rel_clauses_l_assn .
qed

lemmas IsaSAT_code_full_correctness = IsaSAT_code[FCOMP SAT_model_if_satisfiable]

end