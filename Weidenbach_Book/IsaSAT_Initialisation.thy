theory IsaSAT_Initialisation
  imports IsaSAT_Setup IsaSAT_VMTF Watched_Literals.Watched_Literals_Watch_List_Initialisation
begin

no_notation Ref.update ("_ := _" 62)

lemma isasat_input_ops_\<L>\<^sub>a\<^sub>l\<^sub>l_empty[simp]:
  \<open>isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l {#} = {#}\<close>
  unfolding isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

section \<open>Code for the initialisation of the Data Structure\<close>

text \<open>The initialisation is done in three different steps:
  \<^enum> First, we extract all the atoms that appear in the problem and initialise the state with empty values.
    This part is called \<^emph>\<open>initialisation\<close> below.
  \<^enum> Then, we go over all clauses and insert them in our memory module. We call this phase \<^emph>\<open>parsing\<close>.
  \<^enum> Finally, we calculate the watch list.

Splitting the second from the third step makes it easier to add preprocessing and more important
to add a bounded mode.
\<close>

subsection \<open>Initialisation of the state\<close>

definition (in -) atoms_hash_empty where
 [simp]: \<open>atoms_hash_empty _ = {}\<close>

sepref_register atoms_hash_empty

context isasat_input_ops
begin

definition (in -) atoms_hash_int_empty where
  \<open>atoms_hash_int_empty n = RETURN (replicate n False)\<close>

lemma  (in isasat_input_ops)atoms_hash_int_empty_atoms_hash_empty:
  \<open>(atoms_hash_int_empty, RETURN o atoms_hash_empty) \<in>
   [\<lambda>n. (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < n)]\<^sub>f nat_rel \<rightarrow> \<langle>atoms_hash_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (use Max_less_iff in \<open>auto simp: atoms_hash_rel_def atoms_hash_int_empty_def atoms_hash_empty_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def
      dest: spec[of _ "Pos _"]\<close>)

sepref_definition (in -) atoms_hash_empty_code
  is \<open>atoms_hash_int_empty\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a phase_saver_conc\<close>
  unfolding atoms_hash_int_empty_def array_fold_custom_replicate
  by sepref

lemmas  (in isasat_input_ops)atoms_hash_empty_hnr[sepref_fr_rules] =
  atoms_hash_empty_code.refine[FCOMP atoms_hash_int_empty_atoms_hash_empty,
     unfolded atoms_hash_assn_def[symmetric]]

definition (in -) distinct_atms_empty where
  \<open>distinct_atms_empty _ = {}\<close>

definition (in -) distinct_atms_int_empty where
  \<open>distinct_atms_int_empty n = RETURN ([], atoms_hash_empty n)\<close>

lemma distinct_atms_int_empty_distinct_atms_empty:
  \<open>(distinct_atms_int_empty, RETURN o distinct_atms_empty) \<in>
     nat_rel \<rightarrow>\<^sub>f \<langle>distinct_atoms_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: distinct_atoms_rel_def distinct_atms_empty_def distinct_atms_int_empty_def)


sepref_thm (in isasat_input_ops) distinct_atms_empty_code
  is \<open>distinct_atms_int_empty\<close>
  :: \<open>[\<lambda>n. (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < n)]\<^sub>a nat_assn\<^sup>k \<rightarrow> arl_assn uint32_nat_assn *a atoms_hash_assn\<close>
  unfolding distinct_atms_int_empty_def array_fold_custom_replicate
    arl.fold_custom_empty
  by sepref

concrete_definition (in -) distinct_atms_empty_code
   uses isasat_input_ops.distinct_atms_empty_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) distinct_atms_empty_code_def

lemmas distinct_atms_empty_hnr[sepref_fr_rules] =
   distinct_atms_empty_code.refine[of \<A>\<^sub>i\<^sub>n, FCOMP distinct_atms_int_empty_distinct_atms_empty,
     unfolded distinct_atoms_assn_def[symmetric]]

end

context isasat_input_bounded
begin


type_synonym (in -) vmtf_remove_int_option_fst_As = \<open>vmtf_option_fst_As \<times> nat set\<close>

definition (in isasat_input_ops) vmtf_init
   :: \<open>(nat, nat) ann_lits \<Rightarrow> vmtf_remove_int_option_fst_As set\<close>
where
  \<open>vmtf_init M = {((ns, m, fst_As, lst_As, next_search), to_remove).
   \<A>\<^sub>i\<^sub>n \<noteq> {#} \<longrightarrow> (fst_As \<noteq> None \<and> lst_As \<noteq> None \<and> ((ns, m, the fst_As, the lst_As, next_search),
     to_remove) \<in> vmtf M)}\<close>

type_synonym (in -) twl_st_wl_heur_init =
  \<open>(nat,nat)ann_lits \<times> arena \<times> conflict_option_rel \<times> nat \<times>
    (nat \<times> nat literal \<times> bool) list list \<times> vmtf_remove_int_option_fst_As \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd \<times> vdom\<close>

type_synonym (in -) twl_st_wl_heur_init_full =
  \<open>(nat,nat)ann_lits \<times> arena \<times> conflict_option_rel \<times> nat \<times>
    (nat \<times> nat literal \<times> bool) list list \<times> vmtf_remove_int_option_fst_As \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd \<times> vdom\<close>

abbreviation (in -) vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a
    option_assn uint32_nat_assn *a option_assn uint32_nat_assn *a option_assn uint32_nat_assn)\<close>

type_synonym (in -)vmtf_assn_option_fst_As =
  \<open>(uint32, uint64) vmtf_node array \<times> uint64 \<times> uint32 option \<times> uint32 option \<times> uint32 option\<close>

type_synonym (in -)vmtf_remove_assn_option_fst_As = \<open>vmtf_assn_option_fst_As \<times> (uint32 array \<times> nat) \<times> bool array\<close>

abbreviation (in isasat_input_ops) vmtf_remove_conc_option_fst_As
  :: \<open>vmtf_remove_int_option_fst_As \<Rightarrow> vmtf_remove_assn_option_fst_As \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc_option_fst_As \<equiv> vmtf_conc_option_fst_As *a distinct_atoms_assn\<close>

text \<open>The initialisation relation is stricter in the sense that it already includes the relation
of atom inclusion.

Remark that we replace \<^term>\<open>(D = None \<longrightarrow> j \<le> length M)\<close> by \<^term>\<open>j \<le> length M\<close>: this simplifies the
proofs and does not make a difference in the generated code, since there are no conflict analysis
at that level anyway.
\<close>
text \<open>KILL duplicates below, but difference:
  vmtf vs vmtf\_init
  watch list vs no WL
  OC vs non-OC
  \<close>
definition (in isasat_input_ops) twl_st_heur_parsing_no_WL
  :: \<open>(twl_st_wl_heur_init \<times> nat twl_st_wl_init) set\<close>
where
\<open>twl_st_heur_parsing_no_WL =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), ((M, N, D, NE, UE, Q), OC)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D',  D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    mset vdom = dom_m N \<and>
    set_mset
     (all_lits_of_mm
       ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>

definition (in isasat_input_ops) twl_st_heur_parsing
  :: \<open>(twl_st_wl_heur_init \<times> (nat twl_st_wl \<times> nat clauses)) set\<close>
where
\<open>twl_st_heur_parsing =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), ((M, N, D, NE, UE, Q, W), OC)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D',  D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    mset vdom = dom_m N \<and>
    vdom_m W N = set_mset (dom_m N) \<and>
    set_mset
     (all_lits_of_mm
       ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>


definition (in isasat_input_ops) twl_st_heur_parsing_no_WL_wl :: \<open>(_ \<times> nat twl_st_wl_init') set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), (M, N, D, NE, UE, Q)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    set_mset (dom_m N) \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>

definition (in isasat_input_ops) twl_st_heur_parsing_no_WL_wl_no_watched :: \<open>(twl_st_wl_heur_init_full \<times> nat twl_st_wl_init) set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl_no_watched =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), ((M, N, D, NE, UE, Q), OC)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    set_mset (dom_m N) \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>

(* TODO used? *)
definition (in isasat_input_ops) twl_st_heur_parsing_no_WL_wl_full :: \<open>(twl_st_wl_heur_init_full \<times> nat twl_st_wl_init_full) set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl_full =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), ((M, N, D, NE, UE, Q, W), OC)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    vdom_m W N = set_mset (dom_m N) \<and>
    set_mset (dom_m N) \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>

definition (in isasat_input_ops) twl_st_heur_parsing_no_WL_wl_no_watched_full :: \<open>(twl_st_wl_heur_init_full \<times> _) set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl_no_watched_full =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), ((M, N, D, NE, UE, Q), OC)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    set_mset (dom_m N) \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>


definition (in isasat_input_ops) twl_st_heur_post_parsing_wl :: \<open>(twl_st_wl_heur_init_full \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_post_parsing_wl =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom), (M, N, D, NE, UE, Q, W)).
    M' = M \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> vmtf_init M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    set_mset (dom_m N) \<subseteq> set vdom \<and>
    vdom_m W N \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + NE + UE)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0
  }\<close>


type_synonym (in -)twl_st_wll_trail_init =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> vdom_assn\<close>


type_synonym (in -)twl_st_wll_trail_fast_init =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl_uint32 \<times> vmtf_remove_assn_option_fst_As \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> vdom_assn\<close>

definition (in isasat_input_ops) isasat_init_assn
  :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wll_trail_init \<Rightarrow> assn\<close>
where
\<open>isasat_init_assn =
  trail_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_assn *a
  vmtf_remove_conc_option_fst_As *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn *a
  lbd_assn *a
  vdom_assn\<close>

end


subsubsection \<open>VMTF\<close>

definition initialise_VMTF :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> vmtf_remove_int_option_fst_As nres\<close> where
\<open>initialise_VMTF N n = do {
   let A = replicate n (VMTF_Node zero_uint64_nat None None);
   let to_remove = distinct_atms_empty n;
   ASSERT(length N \<le> uint32_max);
   (n, A, cnext) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, A, cnext). i < length_u N)
      (\<lambda>(i, A, cnext). do {
        ASSERT(i < length_u N);
        let L = nat_of_uint32 (N ! i);
        ASSERT(L < length A);
        ASSERT(cnext \<noteq> None \<longrightarrow> the cnext < length A);
        ASSERT(i + 1 \<le> uint_max);
        RETURN (i + one_uint32_nat, vmtf_cons A L cnext (uint64_of_uint32_conv i), Some L)
      })
      (zero_uint32_nat, A, None);
   RETURN ((A, uint64_of_uint32_conv n, cnext, (if N = [] then None else Some (nat_of_uint32 (N!0))), cnext), to_remove)
  }\<close>

sepref_thm (in isasat_input_ops) initialise_VMTF_code
  is \<open>uncurry initialise_VMTF\<close>
  :: \<open>[\<lambda>(N, n). (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < n)]\<^sub>a (arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> vmtf_remove_conc_option_fst_As\<close>
  supply nat_of_uint32_int32_assn[sepref_fr_rules] uint64_max_def[simp] uint32_max_def[simp]
  unfolding initialise_VMTF_def vmtf_cons_def Suc_eq_plus1 one_uint64_nat_def[symmetric]
  apply (rewrite in \<open>(_, _, Some \<hole>)\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>WHILE\<^sub>T _ _ (_, _, \<hole>)\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>do {ASSERT _; let _ = \<hole>; _}\<close> annotate_assn[where A=\<open>uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = \<hole> in _ \<close> array_fold_custom_replicate op_list_replicate_def[symmetric])
  apply (rewrite in \<open>VMTF_Node zero_uint64_nat \<hole> _\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>VMTF_Node zero_uint64_nat _ \<hole>\<close> annotate_assn[where A=\<open>option_assn uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) initialise_VMTF_code
  uses "isasat_input_ops.initialise_VMTF_code.refine_raw"
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) initialise_VMTF_code_def 

declare initialise_VMTF_code.refine[sepref_fr_rules]

lemmas (in isasat_input_ops) initialise_VMTF_hnr[sepref_fr_rules] =
   initialise_VMTF_code.refine[of \<A>\<^sub>i\<^sub>n]

lemma initialise_VMTF:
  shows \<open>(uncurry initialise_VMTF, uncurry (\<lambda>N n. RES (isasat_input_ops.vmtf_init N []))) \<in>
      [\<lambda>(N,n). (\<forall>L\<in># N. L < n) \<and> (distinct_mset N) \<and> size N < uint32_max]\<^sub>f
      (\<langle>uint32_nat_rel\<rangle>list_rel_mset_rel) \<times>\<^sub>f nat_rel \<rightarrow>
      \<langle>(\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel \<times>\<^sub>r \<langle>nat_rel\<rangle> option_rel)
        \<times>\<^sub>r \<langle>Id\<rangle>set_rel\<rangle>nres_rel\<close>
    (is \<open>(?init, ?R) \<in> _\<close>)
proof -
  have vmtf_ns_notin_empty: \<open>vmtf_ns_notin [] 0 (replicate n (VMTF_Node 0 None None))\<close> for n
    unfolding vmtf_ns_notin_def
    by auto

  have K2: \<open>distinct N \<Longrightarrow> fst_As < length N \<Longrightarrow> N!fst_As \<in> set (take fst_As N) \<Longrightarrow> False\<close>
    for fst_As x N
    by (metis (no_types, lifting) in_set_conv_nth length_take less_not_refl min_less_iff_conj
      nth_eq_iff_index_eq nth_take)
  have W_ref: \<open>WHILE\<^sub>T (\<lambda>(i, A, cnext). i < length_u N')
        (\<lambda>(i, A, cnext). do {
              _ \<leftarrow> ASSERT (i < length_u N');
              let L = nat_of_uint32 (N' ! i);
              _ \<leftarrow> ASSERT (L < length A);
              _ \<leftarrow> ASSERT (cnext \<noteq> None \<longrightarrow> the cnext < length A);
              _ \<leftarrow> ASSERT (i + 1 \<le> uint_max);
              RETURN
               (i + one_uint32_nat,
                vmtf_cons A L cnext (uint64_of_uint32_conv i), Some L)
            })
        (zero_uint32_nat, replicate n' (VMTF_Node zero_uint64_nat None None),
         None)
    \<le> SPEC(\<lambda>(i, A', cnext).
      vmtf_ns (rev (map (nat_of_uint32) (take i N'))) i A'
        \<and> cnext = map_option (nat_of_uint32) (option_last (take i N')) \<and>  i = length N' \<and>
          length A' = n \<and> vmtf_ns_notin (rev (map (nat_of_uint32) (take i N'))) i A'
      )\<close>
    (is \<open>_ \<le> SPEC ?P\<close>)
    if H: \<open>case y of (N, n) \<Rightarrow>(\<forall>L\<in># N. L < n) \<and> distinct_mset N \<and> size N < uint32_max\<close> and
       ref: \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<times>\<^sub>f nat_rel\<close> and
       st[simp]: \<open>x = (N', n')\<close> \<open>y = (N, n)\<close>
     for N N' n n' A x y
  proof -
  have [simp]: \<open>n = n'\<close> and NN': \<open>(N', N) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    using ref unfolding st by auto
  have \<open>inj_on nat_of_uint32 S\<close> for S
    by (auto simp: inj_on_def)
  then have dist: \<open>distinct N'\<close>
    using NN' H by (auto simp: list_rel_def uint32_nat_rel_def br_def list_mset_rel_def
      list_all2_op_eq_map_right_iff' distinct_image_mset_inj list_rel_mset_rel_def)
  have L_N: \<open>\<forall>L\<in>set N'. nat_of_uint32 L < n\<close>
    using H ref by (auto simp: list_rel_def uint32_nat_rel_def br_def list_mset_rel_def
      list_all2_op_eq_map_right_iff' list_rel_mset_rel_def)
  let ?Q = \<open>\<lambda>(i, A', cnext).
      vmtf_ns (rev (map (nat_of_uint32) (take i N'))) i A' \<and> i \<le> length N' \<and>
      cnext = map_option (nat_of_uint32) (option_last (take i N')) \<and>
      length A' = n \<and> vmtf_ns_notin (rev (map (nat_of_uint32) (take i N'))) i A'\<close>
  show ?thesis
    apply (refine_vcg WHILET_rule[where R = \<open>measure (\<lambda>(i, _). length N' + 1 - i)\<close> and I = \<open>?Q\<close>])
    subgoal by auto
    subgoal by (auto intro: vmtf_ns.intros)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for S N' x2 A'
      unfolding assert_bind_spec_conv vmtf_ns_notin_def
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
          option_last_def hd_rev last_map intro!: vmtf_cons dest: K2)
    subgoal by auto
    subgoal
      using L_N dist
      by (auto simp: take_Suc_conv_app_nth hd_drop_conv_nth nat_shiftr_div2 nat_of_uint32_shiftr
          option_last_def hd_rev last_map)
    subgoal
      using L_N dist
      by (auto simp: last_take_nth_conv option_last_def)
    subgoal
      using H dist ref
      by (auto simp: last_take_nth_conv option_last_def list_rel_mset_rel_imp_same_length)
    subgoal
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth option_last_def hd_rev last_map intro!: vmtf_cons
          dest: K2)
    subgoal by (auto simp: take_Suc_conv_app_nth)
    subgoal by (auto simp: take_Suc_conv_app_nth)
    subgoal by auto
    subgoal
      using L_N dist
      by (auto 5 5 simp: take_Suc_conv_app_nth hd_rev last_map option_last_def
          intro!: vmtf_notin_vmtf_cons dest: K2 split: if_splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  qed
  have [simp]: \<open>isasat_input_ops.vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l n' [] ((nat_of_uint32 ` set N, {}), {})\<close>
    if \<open>(N, n') \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close> for N N' n'
    using that unfolding isasat_input_ops.vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
      uint32_nat_rel_def br_def list_mset_rel_def list_all2_op_eq_map_right_iff'
      list_rel_mset_rel_def)
  have in_N_in_N1: \<open>L \<in> set N' \<Longrightarrow>  nat_of_uint32 L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l N)\<close>
    if \<open>(N', y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel\<close> and \<open>(y, N) \<in> list_mset_rel\<close> for L N N' y
    using that by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def atms_of_def image_image image_Un list_rel_def
      uint32_nat_rel_def br_def list_mset_rel_def list_all2_op_eq_map_right_iff')

  have length_ba: \<open>\<forall>L\<in># N. L < length ba \<Longrightarrow> L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l N) \<Longrightarrow>
     L < length ba\<close>
    if \<open>(N', y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close>
    for L ba N N' y
    using that
    by (auto simp: isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def nat_shiftr_div2 nat_of_uint32_shiftr
      atms_of_def image_image image_Un split: if_splits)
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding initialise_VMTF_def uncurry_def conc_Id id_def isasat_input_ops.vmtf_init_def
    apply (refine_rcg) 
   subgoal by (auto dest: list_rel_mset_rel_imp_same_length)
    apply (rule specify_left)
     apply (rule W_ref; assumption?)
    subgoal for N' N'n' n' Nn N n st
      apply (case_tac st)
      apply clarify
      apply (subst RETURN_RES_refine_iff)
      apply (auto dest: list_rel_mset_rel_imp_same_length)
      unfolding isasat_input_ops.vmtf_def in_pair_collect_simp prod.case
      apply (rule exI[of _ \<open>map nat_of_uint32 (rev (fst N'))\<close>])
      apply (rule_tac exI[of _ \<open>[]\<close>])
      apply (intro conjI)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last)
      subgoal
        by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_last_def last_map
            hd_rev list_rel_mset_rel_def br_def list_mset_rel_def)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last hd_map hd_conv_nth)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last hd_map last_map)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last hd_rev last_map distinct_atms_empty_def)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last list_rel_mset_rel_def)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last dest: length_ba)
      subgoal by (auto simp: rev_map[symmetric] isasat_input_ops.vmtf_def option_hd_rev
            map_option_option_last list_rel_mset_rel_def dest: in_N_in_N1)
      done
    done
qed


subsection \<open>Parsing\<close>

context isasat_input_bounded
begin
fun (in -)get_conflict_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> conflict_option_rel\<close> where
  \<open>get_conflict_wl_heur_init (_, _, D, _) = D\<close>

fun (in -)get_clauses_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> arena\<close> where
  \<open>get_clauses_wl_heur_init (_, N, _) = N\<close>

fun (in -) get_trail_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur_init (M, _, _, _, _, _, _) = M\<close>

definition (in isasat_input_ops) propagate_unit_cls
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>propagate_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, Q), OC))\<close>

definition (in isasat_input_ops) propagate_unit_cls_heur
 :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>propagate_unit_cls_heur = (\<lambda>L (M, N, D, Q). do {
     ASSERT(undefined_lit M L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
     RETURN (Propagated L 0 # M, N, D, Q)})\<close>

lemma propagate_unit_cls_heur_propagate_unit_cls:
  \<open>(uncurry propagate_unit_cls_heur, uncurry (RETURN oo propagate_unit_init_wl)) \<in>
   [\<lambda>(L, S). undefined_lit (get_trail_init_wl S) L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_parsing_no_WL_def propagate_unit_cls_heur_def propagate_unit_init_wl_def
       vmtf_init_def image_image all_lits_of_mm_add_mset all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
      intro!: vmtf_consD)

sepref_thm propagate_unit_cls_code
  is \<open>uncurry (PR_CONST propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] DECISION_REASON_def[simp]
  unfolding propagate_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) propagate_unit_cls_code
   uses isasat_input_bounded.propagate_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) propagate_unit_cls_code_def

lemmas propagate_unit_cls_heur_hnr[sepref_fr_rules] =
   propagate_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

(*
sepref_thm propagate_unit_cls_fast_code
  is \<open>uncurry (PR_CONST propagate_unit_cls_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding propagate_unit_cls_heur_def isasat_init_fast_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric] zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) propagate_unit_cls_fast_code
   uses isasat_input_bounded.propagate_unit_cls_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) propagate_unit_cls_fast_code_def

lemmas propagate_unit_cls_fast_heur_hnr[sepref_fr_rules] =
   propagate_unit_cls_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)

definition (in isasat_input_ops) already_propagated_unit_cls
   :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((M, N, D, add_mset {#L#} NE, UE, Q), OC))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_heur
   :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_heur = (\<lambda>L (M, N, D, Q, oth).
     RETURN (M, N, D, Q, oth))\<close>

lemma already_propagated_unit_cls_heur_already_propagated_unit_cls:
  \<open>(uncurry already_propagated_unit_cls_heur, uncurry (RETURN oo already_propagated_unit_init_wl)) \<in>
  [\<lambda>(C, S). literals_are_in_\<L>\<^sub>i\<^sub>n C]\<^sub>f list_mset_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_parsing_no_WL_def already_propagated_unit_cls_heur_def
     already_propagated_unit_init_wl_def all_lits_of_mm_add_mset all_lits_of_m_add_mset literals_are_in_\<L>\<^sub>i\<^sub>n_def
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_code
  is \<open>uncurry already_propagated_unit_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) already_propagated_unit_cls_code
   uses isasat_input_bounded.already_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_code_def

lemmas already_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]
(*
sepref_thm already_propagated_unit_cls_fast_code
  is \<open>uncurry already_propagated_unit_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_fast_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_heur_def isasat_init_fast_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) already_propagated_unit_cls_fast_code
   uses isasat_input_bounded.already_propagated_unit_cls_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_fast_code_def

lemmas already_propagated_unit_cls_fast_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)


definition (in -) set_conflict_unit :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_unit L _ = Some {#L#}\<close>

definition (in isasat_input_ops) set_conflict_unit_heur where
  \<open>set_conflict_unit_heur = (\<lambda> L (b, n, xs). RETURN (False, 1, xs[atm_of L := Some (is_pos L)]))\<close>

lemma set_conflict_unit_heur_set_conflict_unit:
  \<open>(uncurry set_conflict_unit_heur, uncurry (RETURN oo set_conflict_unit)) \<in>
    [\<lambda>(L, D). D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<rightarrow>
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
  unfolding set_conflict_unit_heur_def one_uint32_nat_def[symmetric] ISIN_def[symmetric]
  by sepref

concrete_definition (in -) set_conflict_unit_code
   uses isasat_input_bounded.set_conflict_unit_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_unit_code_def

lemmas set_conflict_unit_heur_hnr[sepref_fr_rules] =
   set_conflict_unit_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) conflict_propagated_unit_cls
 :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>conflict_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((M, N, set_conflict_unit L D, add_mset {#L#} NE, UE, {#}), OC))\<close>

definition (in isasat_input_ops) conflict_propagated_unit_cls_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>conflict_propagated_unit_cls_heur = (\<lambda>L (M, N, D, Q, oth). do {
     ASSERT(atm_of L < length (snd (snd D)));
      D \<leftarrow> set_conflict_unit_heur L D;
     RETURN (M, N, D, length_u M, oth)
    })\<close>

lemma conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls:
  \<open>(uncurry conflict_propagated_unit_cls_heur, uncurry (RETURN oo set_conflict_init_wl)) \<in>
   [\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> get_conflict_init_wl S = None]\<^sub>f
      nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
proof -
  have set_conflict_init_wl_alt_def:
    \<open>RETURN oo set_conflict_init_wl = (\<lambda>L ((M, N, D, NE, UE, Q), OC). do {
      D \<leftarrow> RETURN (set_conflict_unit L D);
      RETURN ((M, N, Some {#L#}, add_mset {#L#} NE, UE, {#}), OC)
   })\<close>
    by (auto intro!: ext simp: set_conflict_init_wl_def)
  have [refine0]: \<open>D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> (y, None) \<in> option_lookup_clause_rel \<Longrightarrow> L = L' \<Longrightarrow>
    set_conflict_unit_heur L' y \<le> \<Down> {(D, D'). (D, D') \<in> option_lookup_clause_rel \<and> D' = Some {#L#}}
       (RETURN (set_conflict_unit L D))\<close>
    for L D y L'
    apply (rule order_trans)
    apply (rule set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry,
      unfolded comp_def, of L D L' y])
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      unfolding conc_fun_RETURN
      by (auto simp: set_conflict_unit_def)
    done

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding set_conflict_init_wl_alt_def conflict_propagated_unit_cls_heur_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg)
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def option_lookup_clause_rel_def
        lookup_clause_rel_def atms_of_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def conflict_propagated_unit_cls_heur_def conflict_propagated_unit_cls_def
        image_image set_conflict_unit_def
        intro!: set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry])
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def conflict_propagated_unit_cls_heur_def conflict_propagated_unit_cls_def
        image_image set_conflict_unit_def all_lits_of_mm_add_mset all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
        intro!: set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry])
    done
qed



theorem set_conflict_unit_hnr[sepref_fr_rules]:
  \<open>(uncurry set_conflict_unit_code, uncurry (RETURN oo set_conflict_unit))
    \<in> [\<lambda>(L, D). D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a option_lookup_clause_assn\<^sup>d \<rightarrow> option_lookup_clause_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_lookup_clause_rel)
     (\<lambda>(L, D). D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)
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
  :: \<open>[\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow> isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) conflict_propagated_unit_cls_code
   uses isasat_input_bounded.conflict_propagated_unit_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_propagated_unit_cls_code_def

lemmas conflict_propagated_unit_cls_heur_hnr[sepref_fr_rules] =
   conflict_propagated_unit_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms,
     unfolded PR_CONST_def]
(*
sepref_thm conflict_propagated_unit_cls_fast_code
  is \<open>uncurry (PR_CONST conflict_propagated_unit_cls_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> get_conflict_wl_heur_init S = None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_init_fast_assn\<^sup>d  \<rightarrow> isasat_init_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding conflict_propagated_unit_cls_heur_def isasat_init_fast_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) conflict_propagated_unit_cls_fast_code
   uses isasat_input_bounded.conflict_propagated_unit_cls_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_propagated_unit_cls_fast_code_def

lemmas conflict_propagated_unit_cls_heur_fast_hnr[sepref_fr_rules] =
   conflict_propagated_unit_cls_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)

sepref_register fm_add_new

definition (in isasat_input_ops) add_init_cls_heur
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>  where
  \<open>add_init_cls_heur = (\<lambda>C (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, vdom). do {
     let C = op_array_of_list C;
     ASSERT(length C \<le> uint_max + 2);
     ASSERT(length C \<ge> 2);
    (N, i) \<leftarrow> fm_add_new True C N;
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, vdom @ [nat_of_uint32_conv i])})\<close>

lemma length_C_nempty_iff: \<open>length C \<ge> 2 \<longleftrightarrow> C \<noteq> [] \<and> tl C \<noteq> []\<close>
  by (cases C; cases \<open>tl C\<close>) auto

sepref_thm add_init_cls_code
  is \<open>uncurry add_init_cls_heur\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric] nat_of_uint32_conv_def
  unfolding isasat_init_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric]
    append_ll_def[symmetric]
  by sepref

concrete_definition (in -) add_init_cls_code
   uses isasat_input_bounded.add_init_cls_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) add_init_cls_code_def

lemmas add_init_cls_heur_hnr[sepref_fr_rules] =
   add_init_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]
(*
sepref_thm add_init_cls_fast_code
  is \<open>uncurry add_init_cls_heur\<close>
  :: \<open>[\<lambda>(C, S). length C \<ge> 2 \<and> nat_of_lit (hd C) < length (get_watched_list_heur_init S) \<and>
        nat_of_lit (hd (tl C)) < length (get_watched_list_heur_init S) \<and>
       isasat_fast_init S \<and> packed (get_clauses_wl_heur_init S)]\<^sub>a
      (list_assn unat_lit_assn)\<^sup>k *\<^sub>a isasat_init_fast_assn\<^sup>d  \<rightarrow> isasat_init_fast_assn\<close>
  supply [[goals_limit=1]] append_ll_def[simp]
  unfolding add_init_cls_heur_def isasat_init_fast_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  unfolding isasat_init_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] isasat_fast
    append_ll_def[symmetric] length_C_nempty_iff
  by sepref

concrete_definition (in -) add_init_cls_fast_code
   uses isasat_input_bounded.add_init_cls_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) add_init_cls_fast_code_def

lemmas add_init_cls_heur_fast_hnr[sepref_fr_rules] =
   add_init_cls_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)

context
  fixes
    x :: \<open>nat literal list \<times> twl_st_wl_heur_init\<close> and
    y :: \<open>nat literal list \<times> nat twl_st_wl_init\<close>
  assumes
    pre: \<open>case y of  (C, S) \<Rightarrow>  2 \<le> length C \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and>
       distinct C\<close> and
    xy: \<open>(x, y) \<in> Id \<times>\<^sub>f twl_st_heur_parsing_no_WL\<close>
begin

context
  fixes
    x1 :: \<open>nat literal list\<close> and
    x1b :: \<open>(nat, nat) ann_lits\<close> and
    x2a :: \<open>nat clauses_l \<times> nat literal multiset option \<times>  nat literal multiset multiset \<times>
      nat literal multiset multiset \<times> nat literal multiset\<close> and
    x1c :: \<open>nat clauses_l\<close> and
    x2b :: \<open>nat literal multiset option \<times>
                      nat literal multiset multiset \<times>
                      nat literal multiset multiset \<times>
                      nat literal multiset\<close> and
    x1d :: \<open>nat literal multiset option\<close> and
    x2c :: \<open>nat literal multiset multiset \<times>
                   nat literal multiset multiset \<times>
                   nat literal multiset\<close> and
    x1e :: \<open>nat literal multiset multiset\<close> and
    x2d :: \<open>nat literal multiset multiset \<times> nat literal multiset\<close> and
    x1f :: \<open>nat literal multiset multiset\<close> and
    x1g :: \<open>nat literal multiset\<close> and
    x1a :: \<open>nat twl_st_wl_init'\<close>
  assumes
   x1:
    \<open>x2d = (x1f, x1g)\<close>
    \<open>x2c = (x1e, x2d)\<close>
    \<open>x2b = (x1d, x2c)\<close>
    \<open>x2a = (x1c, x2b)\<close>
    \<open>x1a = (x1b, x2a)\<close>
begin

context
  fixes
    x2 :: \<open>nat twl_st_wl_init\<close> and
    x2g :: \<open>nat literal multiset multiset\<close>
  assumes
   y: \<open>x2 = (x1a, x2g)\<close>
    \<open>y = (x1, x2)\<close>
begin


lemma add_init_pre1: \<open>length (op_array_of_list x1h) \<le> uint_max + 2\<close> if  \<open>x = (x1h, x2h)\<close>
  using pre clss_size_uint_max[of \<open>mset x1h\<close>] that xy
  by (auto simp: y)

lemma add_init_pre2: \<open>2 \<le> length (op_array_of_list x1h)\<close>  if  \<open>x = (x1h, x2h)\<close>
  using pre xy that by (auto simp: y)

context
  fixes x1h :: \<open>nat literal list\<close> and 
  x2h :: \<open>(nat, nat) ann_lits\<times>
      arena \<times>
      (bool \<times> nat \<times> bool option list) \<times>
      nat \<times>
      (nat \<times> nat literal \<times> bool) list list \<times>
      (((nat, nat) vmtf_node list \<times>
        nat \<times> nat option \<times> nat option \<times> nat option) \<times>
       nat set) \<times>
      bool list \<times>
      nat \<times>
      (nat \<Rightarrow> minimize_status) \<times>
      bool list \<times>
      nat list\<close> and
    x1i :: \<open>(nat, nat) ann_lits\<close> and
    x2i :: \<open>arena \<times>  (bool \<times> nat \<times> bool option list) \<times>
                          nat \<times>
                                (nat \<times> nat literal \<times> bool) list list \<times>
                          (((nat, nat) vmtf_node list \<times>
                            nat \<times> nat option \<times> nat option \<times> nat option) \<times>
                           nat set) \<times>
                          bool list \<times>
                          nat \<times>
                          (nat \<Rightarrow> minimize_status) \<times>
                          bool list \<times>
                          nat list\<close> and
    x1j :: \<open>arena\<close> and
    x2j :: \<open>(bool \<times> nat \<times> bool option list) \<times>
                                   nat \<times>
                                (nat \<times> nat literal \<times> bool) list list \<times>
                                   (((nat, nat) vmtf_node list \<times>
                                     nat \<times>
                                     nat option \<times> nat option \<times> nat option) \<times>
                                    nat set) \<times>
                                   bool list \<times>
                                   nat \<times>
                                   (nat \<Rightarrow> minimize_status) \<times>
                                   bool list \<times>
                                   nat list\<close> and x1k :: \<open>bool \<times>
                 nat \<times>
                 bool option list\<close> and
    x2k :: \<open>nat \<times>
              (nat \<times> nat literal \<times> bool) list list \<times>
       (((nat, nat) vmtf_node list \<times>
         nat \<times> nat option \<times> nat option \<times> nat option) \<times>
        nat set) \<times>
       bool list \<times>
       nat \<times>
       (nat \<Rightarrow> minimize_status) \<times>
       bool list \<times>
       nat list\<close> and
    x1l :: \<open>nat\<close> and
    x2l :: \<open>(nat \<times> nat literal \<times> bool) list list \<times>(((nat, nat) vmtf_node list \<times>
    nat \<times> nat option \<times> nat option \<times> nat option) \<times>
   nat set) \<times>
  bool list \<times>
  nat \<times>
  (nat \<Rightarrow> minimize_status) \<times>
  bool list \<times>
  nat list\<close> and
  x1m :: \<open>(nat \<times> nat literal \<times> bool) list list\<close> and
    x2m :: \<open>(((nat, nat) vmtf_node list \<times>
    nat \<times> nat option \<times> nat option \<times> nat option) \<times>
   nat set) \<times>
  bool list \<times>
  nat \<times>
  (nat \<Rightarrow> minimize_status) \<times>
  bool list \<times>
  nat list\<close> and x1n :: \<open>((nat, nat) vmtf_node list \<times>
                         nat \<times> nat option \<times> nat option \<times> nat option) \<times>
                        nat set\<close> and x2n :: \<open>bool list \<times>
      nat \<times>
      (nat \<Rightarrow> minimize_status) \<times>
      bool list \<times>
      nat list\<close> and x1o :: \<open>bool list\<close> and x2o :: \<open>nat \<times>
           (nat \<Rightarrow> minimize_status) \<times>
           bool list \<times>
           nat list\<close> and x1p :: \<open>nat\<close> and x2p :: \<open>(nat \<Rightarrow> minimize_status) \<times>
          bool list \<times>
          nat list\<close> and x1q :: \<open>nat
                                \<Rightarrow> minimize_status\<close> and x2q :: \<open>bool list \<times>
                       nat list\<close> and x1r :: \<open>bool list\<close> and x2r :: \<open>nat list\<close>
  assumes
    x:
      \<open>x2q = (x1r, x2r)\<close>
      \<open>x2p = (x1q, x2q)\<close>
      \<open>x2o = (x1p, x2p)\<close>
      \<open>x2n = (x1o, x2o)\<close>
      \<open>x2m = (x1n, x2n)\<close>
      \<open>x2l = (x1m, x2m)\<close>
      \<open>x2k = (x1l, x2l)\<close>
      \<open>x2j = (x1k, x2k)\<close>
      \<open>x2i = (x1j, x2j)\<close>
      \<open>x2h = (x1i, x2i)\<close>
      \<open>x = (x1h, x2h)\<close>
begin


private lemma st:
    \<open>x1h = x1\<close> and
    rel: \<open>((x1i, x1j, x1k, x1l, x1m, x1n, x1o, x1p, x1q, x1r, x2r), x1a, x2g)
     \<in> twl_st_heur_parsing_no_WL\<close>
  using xy x y by auto

private lemma
    x1h_x1: \<open>x1h = x1\<close> and
    \<open>x1i = x1b\<close> and
    valid: \<open>valid_arena x1j x1c (set x2r)\<close> and
    \<open>(x1k, x1d) \<in> option_lookup_clause_rel\<close> and
    \<open>x1g = {#- lit_of x. x \<in># mset (drop x1l (rev x1b))#}\<close> and
    \<open>x1n \<in> vmtf_init x1b\<close> and
    \<open>phase_saving x1o\<close> and
    \<open>no_dup x1b\<close> and
    \<open>cach_refinement_empty x1q\<close> and
    vdom: \<open>mset x2r = dom_m x1c\<close> and
    watched: \<open>(x1m, empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
    var_incl:
      \<open>set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m x1c#} + x1e + x1f)) \<subseteq> set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  using xy unfolding x y x1 twl_st_heur_parsing_no_WL_def
  by auto

private lemma add_new_alt_def:
   \<open>(SPEC
          (\<lambda>(N', i).
              N' = fmupd i (D'', False) x1c \<and>
              0 < i \<and>
              i \<notin># dom_m x1c \<and>
              (\<forall>L\<in>#all_lits_of_mm (mset `# ran_mf x1c + (x1e + x1f)).
                  i \<notin> fst ` set (x2f L)))) \<ge>
        (SPEC
          (\<lambda>(N', i).
              N' = fmupd i (D'', False) x1c \<and>
              0 < i \<and>
              i \<notin> vdom_m x2f x1c))\<close>
    if lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D'')\<close> for D'' N NE UE W
  using lits pre vdom var_incl
  by (auto simp: y vdom_m_def literals_are_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def x1 ac_simps)

lemma init_fm_add_new:
  \<open>fm_add_new True (op_array_of_list x1h) x1j
       \<le> \<Down>  {((arena, i), (N', i')). valid_arena arena N' (insert i (set x2r)) \<and> i = i' \<and>
            i \<notin># dom_m x1c \<and> i = length x1j + header_size x1h}
          (SPEC
            (\<lambda>(N', ia).
                0 < ia \<and> ia \<notin># dom_m x1c \<and> N' = fmupd ia (x1, True) x1c))\<close>
  (is \<open>_ \<le> \<Down> ?qq _\<close>)
  unfolding x1h_x1
  apply (rule order_trans)
  apply (rule fm_add_new_append_clause)
  using valid vdom pre xy valid_arena_in_vdom_le_arena[OF valid] arena_lifting(2)[OF valid]
  by (fastforce simp: x1h_x1 y vdom_m_def
    intro!: RETURN_RES_refine valid_arena_append_clause)

lemma add_init_cls_final_rel:
  fixes xa :: \<open>arena \<times> nat\<close> and x' :: \<open>nat clauses_l \<times> nat\<close> and
     x1s :: \<open>nat clauses_l\<close> and x2s :: \<open>nat\<close> and
     x1t :: \<open>arena\<close> and x2t :: \<open>nat\<close>
  assumes
    \<open>(xa, x')
     \<in> {((arena, i), (N', i')). valid_arena arena N' (insert i (set x2r)) \<and> i = i' \<and>
            i \<notin># dom_m x1c \<and> i = length x1j + header_size x1h}\<close> and
    \<open>x' \<in> {(N', ia). 0 < ia \<and> ia \<notin># dom_m x1c \<and> N' = fmupd ia (x1, True) x1c}\<close> and
    \<open>x' = (x1s, x2s)\<close> and
    \<open>xa = (x1t, x2t)\<close>
  shows \<open>((x1i, x1t, x1k, x1l, x1m,
           x1n, x1o, x1p, x1q, x1r, x2r @ [nat_of_uint32_conv x2t]),
          (x1b, x1s, x1d, x1e, x1f, x1g), x2g)
         \<in> twl_st_heur_parsing_no_WL\<close>
proof -
  show ?thesis
    using pre assms rel xy unfolding x y x1 twl_st_heur_parsing_no_WL_def
    apply (auto simp: twl_st_heur_parsing_no_WL_def nat_of_uint32_conv_def
      intro!: )
    apply (auto simp: vdom_m_simps5 ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
      literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    done
qed
end
end
end
end

lemma add_init_cls_heur_add_init_cls:
  \<open>(uncurry add_init_cls_heur, uncurry (add_to_clauses_init_wl)) \<in>
   [\<lambda>(C, S). length C \<ge> 2 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> distinct C]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
proof -
  have add_to_clauses_init_wl_alt_def:
   \<open>add_to_clauses_init_wl = (\<lambda>i ((M, N, D, NE, UE, Q), OC). do {
     let b = (length i = 2);
    (N', ia) \<leftarrow> SPEC (\<lambda>(N', ia). ia > 0 \<and> ia \<notin># dom_m N \<and> N' = fmupd ia (i, True) N);
    RETURN ((M, N', D, NE, UE, Q), OC)
  })\<close>
    by (auto simp: add_to_clauses_init_wl_def get_fresh_index_def Let_def
     RES_RES2_RETURN_RES RES_RES_RETURN_RES2 RES_RETURN_RES uncurry_def image_iff
    intro!: ext)
  show ?thesis
  unfolding add_init_cls_heur_def add_to_clauses_init_wl_alt_def uncurry_def Let_def
    to_watcher_def id_def
  apply (intro frefI nres_relI)
  apply (refine_rcg init_fm_add_new)
  subgoal
    by (rule add_init_pre1)
  subgoal
    by (rule add_init_pre2)
  apply assumption+
  subgoal by (rule add_init_cls_final_rel)
  done
qed

definition (in isasat_input_ops) already_propagated_unit_cls_conflict
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls_conflict = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((M, N, D, add_mset {#L#} NE, UE, {#}), OC))\<close>

definition (in isasat_input_ops) already_propagated_unit_cls_conflict_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_conflict_heur = (\<lambda>L (M, N, D, Q, oth).
     RETURN (M, N, D, length_u M, oth))\<close>

lemma already_propagated_unit_cls_conflict_heur_already_propagated_unit_cls_conflict:
  \<open>(uncurry already_propagated_unit_cls_conflict_heur,
     uncurry (RETURN oo already_propagated_unit_cls_conflict)) \<in>
   [\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_parsing_no_WL_def already_propagated_unit_cls_conflict_heur_def
      already_propagated_unit_cls_conflict_def all_lits_of_mm_add_mset
      all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
      intro: vmtf_consD)

sepref_thm already_propagated_unit_cls_conflict_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def isasat_init_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  by sepref

concrete_definition (in -) already_propagated_unit_cls_conflict_code
   uses isasat_input_bounded.already_propagated_unit_cls_conflict_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_conflict_code_def

lemmas already_propagated_unit_cls_conflict_heur_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

(*
sepref_thm already_propagated_unit_cls_conflict_fast_code
  is \<open>uncurry already_propagated_unit_cls_conflict_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_init_fast_assn\<^sup>d  \<rightarrow>\<^sub>a isasat_init_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding already_propagated_unit_cls_conflict_heur_def isasat_init_fast_assn_def
  PR_CONST_def cons_trail_Propagated_def[symmetric]
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) already_propagated_unit_cls_conflict_fast_code
   uses isasat_input_bounded.already_propagated_unit_cls_conflict_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) already_propagated_unit_cls_conflict_fast_code_def

lemmas already_propagated_unit_cls_conflict_heur_fast_hnr[sepref_fr_rules] =
   already_propagated_unit_cls_conflict_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)

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
  \<open>set_empty_clause_as_conflict_heur = (\<lambda> (M, N, (_, (n, xs)), Q, WS).
     RETURN (M, N, (False, (n, xs)), length_u M, WS))\<close>

lemma set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict:
  \<open>(set_empty_clause_as_conflict_heur, RETURN o add_empty_conflict_init_wl) \<in>
  [\<lambda>S. get_conflict_init_wl S = None]\<^sub>f
   twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: set_empty_clause_as_conflict_heur_def add_empty_conflict_init_wl_def
      twl_st_heur_parsing_no_WL_def set_conflict_empty_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

sepref_thm set_empty_clause_as_conflict_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_assn_def
  by sepref

concrete_definition (in -) set_empty_clause_as_conflict_code
   uses isasat_input_bounded.set_empty_clause_as_conflict_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) set_empty_clause_as_conflict_code_def

lemmas set_empty_clause_as_conflict_heur_hnr[sepref_fr_rules] =
   set_empty_clause_as_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

(*
sepref_thm set_empty_clause_as_conflict_fast_code
  is \<open>set_empty_clause_as_conflict_heur\<close>
  :: \<open>[\<lambda>S. get_conflict_wl_heur_init S = None]\<^sub>a isasat_init_fast_assn\<^sup>d \<rightarrow> isasat_init_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_empty_clause_as_conflict_heur_def isasat_init_fast_assn_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) set_empty_clause_as_conflict_fast_code
   uses isasat_input_bounded.set_empty_clause_as_conflict_fast_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) set_empty_clause_as_conflict_fast_code_def

lemmas set_empty_clause_as_conflict_heur_fast_hnr[sepref_fr_rules] =
   set_empty_clause_as_conflict_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms] *)
(*
theorem set_empty_clause_as_conflict_hnr[sepref_fr_rules]:
  \<open>(set_empty_clause_as_conflict_code, RETURN o add_empty_conflict_init_wl)
    \<in> [\<lambda>S. get_conflict_wl (fst S) = None]\<^sub>a twl_st_init_assn\<^sup>d  \<rightarrow> twl_st_init_assn\<close>
    (is ?slow is  \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
     and
  set_empty_clause_as_conflict_fast_hnr[sepref_fr_rules]:
    \<open>(set_empty_clause_as_conflict_fast_code, RETURN o add_empty_conflict_init_wl)
      \<in> [\<lambda>S. get_conflict_wl (fst S) = None]\<^sub>a twl_st_init_fast_assn\<^sup>d  \<rightarrow> twl_st_init_fast_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?prefast]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur_parsing_no_WL (\<lambda>_. True) (\<lambda>_ S. get_conflict_wl_heur_init S = None)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_init_assn\<^sup>d) twl_st_heur_parsing_no_WL \<rightarrow>
       hr_comp isasat_init_assn twl_st_heur_parsing_no_WL\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_empty_clause_as_conflict_heur_hnr
    set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_parsing_no_WL_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..

  have H: \<open>?cfast
    \<in> [comp_PRE twl_st_heur_parsing_no_WL (\<lambda>_. True) (\<lambda>_ S. get_conflict_wl_heur_init S = None)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_init_fast_assn\<^sup>d) twl_st_heur_parsing_no_WL \<rightarrow>
       hr_comp isasat_init_fast_assn twl_st_heur_parsing_no_WL\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_empty_clause_as_conflict_heur_fast_hnr
    set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_parsing_no_WL_def)
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_fast_assn_def by simp
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_init_fast_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed *)

definition (in -) add_clause_to_others_heur
   :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_clause_to_others_heur = (\<lambda> _ (M, N, D, Q, WS).
      RETURN (M, N, D, Q, WS))\<close>

lemma add_clause_to_others_heur_add_clause_to_others:
  \<open>(uncurry add_clause_to_others_heur, uncurry (RETURN oo add_to_other_init)) \<in>
   \<langle>Id\<rangle>list_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: add_clause_to_others_heur_def add_to_other_init.simps
      twl_st_heur_parsing_no_WL_def)

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

definition (in -) get_conflict_wl_is_None_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur_init = (\<lambda>(M, N, (b, _), Q, _). b)\<close>


definition (in isasat_input_ops) init_dt_step_wl_heur
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> (twl_st_wl_heur_init) nres\<close>
where
  \<open>init_dt_step_wl_heur C S = do {
     if get_conflict_wl_is_None_heur_init S
     then do {
        if is_Nil C
        then set_empty_clause_as_conflict_heur S
        else if list_length_1 C
        then do {
          ASSERT (C \<noteq> []);
          let L = hd C;
          ASSERT(L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
          let val_L = polarity (get_trail_wl_heur_init S) L;
          if val_L = None
          then propagate_unit_cls_heur L S
          else
            if val_L = Some True
            then already_propagated_unit_cls_heur C S
            else conflict_propagated_unit_cls_heur L S
        }
        else do {
          ASSERT(length C \<ge> 2);
          ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset C));
          add_init_cls_heur C S
       }
     }
     else add_clause_to_others_heur C S
  }\<close>

named_theorems twl_st_heur_parsing_no_WL
lemma [twl_st_heur_parsing_no_WL]:
  assumes \<open>(S, T) \<in>  twl_st_heur_parsing_no_WL\<close>
  shows \<open>get_trail_init_wl T = get_trail_wl_heur_init S\<close>
  using assms
  by (cases S; auto simp: twl_st_heur_parsing_no_WL_def; fail)+


definition get_conflict_wl_is_None_init :: \<open>nat twl_st_wl_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_init = (\<lambda>((M, N, D, NE, UE, Q), OC). is_None D)\<close>

lemma get_conflict_wl_is_None_init_alt_def:
  \<open>get_conflict_wl_is_None_init S \<longleftrightarrow> get_conflict_init_wl S = None\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_init_def split: option.splits)

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None_init) \<in>
    twl_st_heur_parsing_no_WL \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_parsing_no_WL_def get_conflict_wl_is_None_heur_init_def option_lookup_clause_rel_def
      get_conflict_wl_is_None_init_def split: option.splits)

definition (in -) get_conflict_wl_is_None_init where
  \<open>get_conflict_wl_is_None_init = get_conflict_wl_is_None\<close>

lemma init_dt_step_wl_heur_init_dt_step_wl:
  \<open>(uncurry init_dt_step_wl_heur, uncurry init_dt_step_wl) \<in>
   [\<lambda>(C, S). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> distinct C]\<^sub>f
      Id \<times>\<^sub>f twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_step_wl_heur_def init_dt_step_wl_def uncurry_def
    option.case_eq_if get_conflict_wl_is_None_init_alt_def[symmetric]
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
  subgoal by (auto simp: twl_st_heur_parsing_no_WL_def get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init[THEN fref_to_Down_unRET_Id])
  subgoal by (auto simp: twl_st_heur_parsing_no_WL_def is_Nil_def split: list.splits)
  subgoal by (simp add: get_conflict_wl_is_None_init_alt_def)
  subgoal by auto
  subgoal by simp
  subgoal by simp
  subgoal by (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset split: list.splits)
  subgoal by (auto simp: polarity_def twl_st_heur_parsing_no_WL_def split: list.splits)
  subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
  subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
  subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
  subgoal by (auto simp add: twl_st_heur_parsing_no_WL polarity_def)
  subgoal by simp
  subgoal by (auto simp: list_mset_rel_def br_def)
  subgoal by simp
  subgoal by (simp add: get_conflict_wl_is_None_init_alt_def)
  subgoal by simp
  subgoal
    by (auto simp: twl_st_heur_parsing_no_WL_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
        split: list.splits)
  subgoal by simp
  subgoal
    by (auto simp: twl_st_heur_parsing_no_WL_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
      split: list.splits)
  subgoal for x y x1 x2 C x2a
    by (cases C; cases \<open>tl C\<close>)
      (auto simp: twl_st_heur_parsing_no_WL_def map_fun_rel_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
        split: list.splits)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  done


lemma (in -) get_conflict_wl_is_None_heur_init_alt_def:
  \<open>RETURN o get_conflict_wl_is_None_heur_init = (\<lambda>(M, N, (b, _), Q, W, _). RETURN b)\<close>
  by (auto simp: get_conflict_wl_is_None_heur_init_def intro!: ext)

sepref_thm get_conflict_wl_is_None_init_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_alt_def isasat_init_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_init_code
   uses isasat_input_bounded.get_conflict_wl_is_None_init_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_init_code_def

lemmas get_conflict_wl_is_None_init_code_hnr[sepref_fr_rules] =
   get_conflict_wl_is_None_init_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

(*
sepref_thm get_conflict_wl_is_None_init_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur_init\<close>
  :: \<open>isasat_init_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_init_def isasat_init_fast_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_init_fast_code
   uses isasat_input_bounded.get_conflict_wl_is_None_init_fast_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_init_fast_code_def

lemmas get_conflict_wl_is_None_init_fast_code_hnr[sepref_fr_rules] =
   get_conflict_wl_is_None_init_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma get_conflict_wl_is_None_fast_code_get_conflict_wl_is_None_no_lvls[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_init_fast_code, RETURN o get_conflict_wl_is_None_init) \<in>
     twl_st_init_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_init_fast_code_hnr[FCOMP get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init]
  unfolding twl_st_init_fast_assn_def get_conflict_wl_is_None_init_def
  by fast *)

definition polarity_st_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> _ \<Rightarrow> bool option\<close> where
  \<open>polarity_st_heur_init = (\<lambda>(M, _) L. polarity M L)\<close>

lemma polarity_st_heur_init_alt_def:
  \<open>polarity_st_heur_init S L = polarity (get_trail_wl_heur_init S) L\<close>
  by (cases S) (auto simp: polarity_st_heur_init_def)

sepref_thm polarity_st_heur_init_code
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a isasat_init_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_init_code
   uses isasat_input_bounded.polarity_st_heur_init_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_init_code_def

lemmas polarity_st_heur_init_hr[sepref_fr_rules] =
   polarity_st_heur_init_code.refine[OF isasat_input_bounded_axioms]
(*
sepref_thm polarity_st_heur_init_fast_code
  is \<open>uncurry (RETURN oo polarity_st_heur_init)\<close>
  :: \<open>[\<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a isasat_init_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_init_def isasat_init_fast_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_init_fast_code
   uses isasat_input_bounded.polarity_st_heur_init_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_init_fast_code_def

lemmas polarity_st_heur_init_fast_hr[sepref_fr_rules] =
   polarity_st_heur_init_fast_code.refine[OF isasat_input_bounded_axioms] *)

definition polarity_st_init :: \<open>'v twl_st_wl_init \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st_init S = polarity (get_trail_init_wl S)\<close>

lemma get_conflict_wl_is_None_init:
   \<open>get_conflict_init_wl S = None \<longleftrightarrow> get_conflict_wl_is_None_init S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_init_def split: option.splits)

lemma is_Nil_hnr[sepref_fr_rules]:
 \<open>(return o is_Nil, RETURN o is_Nil) \<in> (list_assn R)\<^sup>k\<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto split: list.splits)

sepref_register (in isasat_input_ops) init_dt_step_wl
  get_conflict_wl_is_None_heur_init already_propagated_unit_cls_heur
  conflict_propagated_unit_cls_heur add_clause_to_others_heur
  add_init_cls_heur set_empty_clause_as_conflict_heur

sepref_register polarity_st_heur_init propagate_unit_cls_heur

sepref_thm init_dt_step_wl_code
  is \<open>uncurry (PR_CONST init_dt_step_wl_heur)\<close>
  :: \<open>[\<lambda>(C, S). True]\<^sub>a (list_assn unat_lit_assn)\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>
       isasat_init_assn\<close>
  supply [[goals_limit=1]]
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
(*

sepref_thm init_dt_step_wl_fast_code
  is \<open>uncurry (PR_CONST init_dt_step_wl_heur)\<close>
  :: \<open>[\<lambda>(_, S). isasat_fast_init S \<and> packed(get_clauses_wl_heur_init S)]\<^sub>a
       (list_assn unat_lit_assn)\<^sup>d *\<^sub>a isasat_init_fast_assn\<^sup>d \<rightarrow>
       isasat_init_fast_assn\<close>
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

concrete_definition (in -) init_dt_step_wl_fast_code
  uses "isasat_input_bounded.init_dt_step_wl_fast_code.refine_raw"
  is "(uncurry ?f,_)\<in>_"

prepare_code_thms (in -) init_dt_step_wl_fast_code_def

lemmas init_dt_step_wl_fast_code_refine[sepref_fr_rules] =
  init_dt_step_wl_fast_code.refine[OF isasat_input_bounded_axioms] *)

definition (in isasat_input_ops) init_dt_wl_heur
 :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>init_dt_wl_heur CS S = nfoldli CS (\<lambda>_. True)
     (\<lambda>C S. do {
        init_dt_step_wl_heur C S}) S\<close>

(* definition (in isasat_input_ops) init_dt_wl_heur_fast
 :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> (twl_st_wl_heur_init) nres\<close>
where
  \<open>init_dt_wl_heur_fast CS S = nfoldli CS (\<lambda>_. True)
     (\<lambda>C S. do {
        ASSERT(isasat_fast_init S);
        ASSERT (packed (get_clauses_wl_heur_init S));
        init_dt_step_wl_heur C S}) S\<close> *)

sepref_register (in isasat_input_ops) init_dt_wl_heur

(* lemma (in isasat_input_ops)init_dt_wl_heur_fast_invariants:
  assumes
    \<open>RETURN T \<le> init_dt_step_wl_heur C S\<close> and
    (* \<open>packed (get_clauses_wl_heur_init S)\<close> and *)
    \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S)\<close> and
    (* \<open>Suc ((Max_dom (get_clauses_wl_heur_init S)) + length CS) < uint_max - Suc 0\<close> *)
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
 shows
    (* \<open>Max_dom_wl_heur T + length CS < uint_max - Suc 0\<close> (is ?A) *)
    (* \<open>packed (get_clauses_wl_heur_init T)\<close> (is ?B) and *)
    \<open>length (get_watched_list_heur_init T) = length (get_watched_list_heur_init S)\<close> (is ?C)
proof -
  (* show ?A
    using assms (* TODO Proof *)
    by (cases S; cases T; cases C; cases \<open>tl C\<close>)
      (auto simp: init_dt_step_wl_heur_def Let_def set_empty_clause_as_conflict_heur_def
        propagate_unit_cls_heur_def image_image polarity_def already_propagated_unit_cls_heur_def
        conflict_propagated_unit_cls_heur_def add_clause_to_others_heur_def get_fresh_index_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset add_init_cls_heur_def fm_add_new_packed_def RES_RETURN_RES
        RES_RES_RETURN_RES2 get_fresh_index_packed_alt_def max_def remove1_mset_ge_Max_some
        Max_dom_alt_def[symmetric] Max_dom_fmupd_irrel
        split: if_splits list.splits)
  show ?B
    using assms (* TODO Proof *)
    by (cases S; cases T; cases C; cases \<open>tl C\<close>)
      (auto simp: init_dt_step_wl_heur_def Let_def set_empty_clause_as_conflict_heur_def
        propagate_unit_cls_heur_def image_image polarity_def already_propagated_unit_cls_heur_def
        conflict_propagated_unit_cls_heur_def add_clause_to_others_heur_def get_fresh_index_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset add_init_cls_heur_def fm_add_new_packed_def RES_RETURN_RES
        RES_RES_RETURN_RES2 get_fresh_index_packed_alt_def packed0_fmud_Suc_Max_dom
        split: if_splits list.splits) *)
  show ?C
    using assms (* TODO Proof *)
    by (cases S; cases T; cases C; cases \<open>tl C\<close>)
      (auto simp: init_dt_step_wl_heur_def Let_def set_empty_clause_as_conflict_heur_def
        propagate_unit_cls_heur_def image_image polarity_def already_propagated_unit_cls_heur_def
        conflict_propagated_unit_cls_heur_def add_clause_to_others_heur_def get_fresh_index_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset add_init_cls_heur_def RES_RETURN_RES
        RES_RES_RETURN_RES2 packed0_fmud_Suc_Max_dom
        split: if_splits list.splits)
qed *)
(*
lemma (in isasat_input_ops)init_dt_wl_heur_fast_le:
   \<open>Max_dom (get_clauses_wl_heur_init S) + length CS < uint_max - 1 \<Longrightarrow>
   \<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<Longrightarrow>
packed (get_clauses_wl_heur_init S) \<Longrightarrow>
\<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S) \<Longrightarrow>
  \<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S) \<Longrightarrow>
    init_dt_wl_heur_fast CS S \<le> init_dt_wl_heur CS S\<close>
  unfolding init_dt_wl_heur_fast_def init_dt_wl_heur_def Max_dom_def init_dt_wl_heur_fast_def
  apply (induction CS arbitrary: S)
  subgoal
    apply auto
    done
  subgoal premises H
    using H
    apply (auto intro!: ASSERT_leI dest: multi_member_split)
     apply (auto dest!: multi_member_split)[]
     apply (case_tac \<open>set_mset A = {}\<close>)
      apply auto[2]
    defer
    apply (rule Refine_Basic.bind_mono(1))
     apply simp
    apply (rule order.trans)
     apply (rule H)
         apply (auto simp: Max_dom_alt_def[symmetric] intro: init_dt_wl_heur_fast_invariants
        dest: init_dt_wl_heur_fast_invariants(3))
    done
  done *)

(*
lemma (in isasat_input_ops)init_dt_wl_heur_fast_ge:
   \<open>Max_dom (get_clauses_wl_heur_init S) + length CS < uint_max - 1 \<Longrightarrow>
   \<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<Longrightarrow>
packed (get_clauses_wl_heur_init S) \<Longrightarrow>
\<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S) \<Longrightarrow>
  \<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S) \<Longrightarrow>
    init_dt_wl_heur_fast CS S \<ge> init_dt_wl_heur CS S\<close>
  unfolding init_dt_wl_heur_fast_def init_dt_wl_heur_def Max_dom_def init_dt_wl_heur_fast_def
  apply (induction CS arbitrary: S)
  subgoal
    apply auto
    done
  subgoal premises H
    using H
    apply (auto intro!: ASSERT_leI simp: le_ASSERT_iff dest: multi_member_split)
    apply (rule Refine_Basic.bind_mono(1))
     apply simp
    apply (rule order.trans)
     apply (rule H)
         apply (auto simp: Max_dom_alt_def[symmetric] intro: init_dt_wl_heur_fast_invariants
        dest: init_dt_wl_heur_fast_invariants(3))
    done
  done *)
(*
lemma (in isasat_input_ops)init_dt_wl_heur_fast_init_dt_wl_heur:
  assumes
    \<open>Max_dom_wl_heur S + length CS < uint_max - 1\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close> and
    \<open>packed (get_clauses_wl_heur_init S)\<close> and
    \<open>\<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S)\<close> and
    \<open>\<forall>L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length (get_watched_list_heur_init S)\<close>
  shows \<open>init_dt_wl_heur_fast CS S =
         init_dt_wl_heur CS S\<close>
  using init_dt_wl_heur_fast_le[OF assms]
  using init_dt_wl_heur_fast_ge[OF assms]
  by simp *)

end


subsection \<open>Extractions of the atoms in the state\<close>

definition init_valid_rep :: "nat list \<Rightarrow> nat set \<Rightarrow> bool" where
  \<open>init_valid_rep xs l \<longleftrightarrow>
      (\<forall>L\<in>l. L < length xs) \<and>
      (\<forall>L \<in> l.  (xs ! L) mod 2 = 1) \<and>
      (\<forall>L. L < length xs \<longrightarrow> (xs ! L) mod 2 = 1 \<longrightarrow> L \<in> l)\<close>


definition isasat_atms_ext_rel :: \<open>((nat list \<times> nat \<times> nat list) \<times> nat set) set\<close> where
  \<open>isasat_atms_ext_rel = {((xs, n, atms), l).
      init_valid_rep xs l \<and>
      n = Max (insert 0 l) \<and>
      length xs < uint_max \<and>
      (\<forall>s\<in>set xs. s \<le> uint64_max) \<and>
      finite l \<and>
      distinct atms \<and>
      set atms = l \<and>
      length xs \<noteq> 0
   }\<close>

abbreviation isasat_atms_ext_rel_assn where
  \<open>isasat_atms_ext_rel_assn \<equiv> array_assn uint64_nat_assn *a uint32_nat_assn *a
       arl_assn uint32_nat_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp isasat_atms_ext_rel_assn isasat_atms_ext_rel\<close>

definition in_map_atm_of :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>in_map_atm_of L N \<longleftrightarrow> L \<in> set N\<close>

definition (in -) init_next_size where
  \<open>init_next_size L = 2 * L\<close>

lemma (in -) [sepref_fr_rules]:
  \<open>(return o init_next_size, RETURN o init_next_size)
  \<in> [\<lambda>L. L \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  by (sepref_to_hoare)
   (sep_auto simp: init_next_size_def br_def uint32_nat_rel_def nat_of_uint32_add
      nat_of_uint32_distrib_mult2 uint_max_def)

lemma init_next_size: \<open>L \<noteq> 0 \<Longrightarrow> L + 1 \<le> uint_max \<Longrightarrow> L < init_next_size L \<close>
  by (auto simp: init_next_size_def uint32_max_uint32_def uint_max_def)

definition add_to_atms_ext where
  \<open>add_to_atms_ext = (\<lambda>i (xs, n, atms). do {
    ASSERT(i \<le> uint_max div 2);
    ASSERT(length xs \<le> uint_max);
    let n = max i n;
    (if i < length_u xs then do {
       ASSERT(xs!i \<le> uint64_max);
       let atms = (if xs!i AND one_uint64_nat = one_uint64_nat then atms else atms @ [i]);
       RETURN (xs[i := (sum_mod_uint64_max (xs ! i) 2) OR one_uint64_nat], n, atms)
     }
     else do {
        ASSERT(i + 1 \<le> uint_max);
        ASSERT(length_u xs \<noteq> 0);
        ASSERT(i < init_next_size i);
        RETURN ((list_grow xs (init_next_size i) zero_uint64_nat)[i := one_uint64_nat], n,
            atms @ [i])
     })
    })\<close>

lemma init_valid_rep_upd_OR:
  \<open>init_valid_rep (x1b[x1a := a OR one_uint64_nat]) x2 \<longleftrightarrow>
    init_valid_rep (x1b[x1a := one_uint64_nat]) x2 \<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then have
    1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := a OR one_uint64_nat])\<close> and
    2: \<open>\<forall>L\<in>x2. x1b[x1a := a OR one_uint64_nat] ! L mod 2 = 1\<close> and
    3: \<open>\<forall>L<length (x1b[x1a := a OR one_uint64_nat]).
        x1b[x1a := a OR one_uint64_nat] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := one_uint64_nat])\<close>
    using 1 by simp
  then have 2: \<open>\<forall>L\<in>x2. x1b[x1a := one_uint64_nat] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length (x1b[x1a := one_uint64_nat]).
        x1b[x1a := one_uint64_nat] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?B
    using 1 2 3
    unfolding init_valid_rep_def by fast+
next
  assume ?B
  then have
    1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := one_uint64_nat])\<close> and
    2: \<open>\<forall>L\<in>x2. x1b[x1a := one_uint64_nat] ! L mod 2 = 1\<close> and
    3: \<open>\<forall>L<length (x1b[x1a := one_uint64_nat]).
        x1b[x1a := one_uint64_nat] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a :=  a OR one_uint64_nat])\<close>
    using 1 by simp
  then have 2: \<open>\<forall>L\<in>x2. x1b[x1a := a OR one_uint64_nat] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update' bitOR_1_if_mod_2_nat)
  then have 3: \<open>\<forall>L<length (x1b[x1a :=  a OR one_uint64_nat]).
        x1b[x1a :=  a OR one_uint64_nat] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?A
    using 1 2 3
    unfolding init_valid_rep_def by fast+
qed

lemma init_valid_rep_insert:
  assumes val: \<open>init_valid_rep x1b x2\<close> and le: \<open>x1a < length x1b\<close>
  shows \<open>init_valid_rep (x1b[x1a := one_uint64_nat]) (insert x1a x2)\<close>
proof -
  have
    1: \<open>\<forall>L\<in>x2. L < length x1b\<close> and
    2: \<open>\<forall>L\<in>x2. x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length x1b \<Longrightarrow> x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    using val unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>insert x1a x2. L < length (x1b[x1a := one_uint64_nat])\<close>
    using 1 le by simp
  then have 2: \<open>\<forall>L\<in>insert x1a x2. x1b[x1a := one_uint64_nat] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length (x1b[x1a := one_uint64_nat]).
        x1b[x1a := one_uint64_nat] ! L mod 2 = 1 \<longrightarrow>
        L \<in> insert x1a x2\<close>
    using 3 le by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?thesis
    using 1 2 3
    unfolding init_valid_rep_def by fast+
qed

lemma init_valid_rep_extend:
  \<open>init_valid_rep (x1b @ replicate n 0) x2 \<longleftrightarrow> init_valid_rep (x1b) x2\<close>
   (is \<open>?A \<longleftrightarrow> ?B\<close> is \<open>init_valid_rep ?x1b _ \<longleftrightarrow> _\<close>)
proof
  assume ?A
  then have
    1: \<open>\<And>L. L\<in>x2 \<Longrightarrow> L < length ?x1b\<close> and
    2: \<open>\<And>L. L\<in>x2 \<Longrightarrow> ?x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length ?x1b \<Longrightarrow> ?x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>L\<in>x2 \<Longrightarrow> L < length x1b\<close> for L
    using 3[of L] 2[of L] 1[of L]
    by (auto simp: nth_append split: if_splits)
  then have 2: \<open>\<forall>L\<in>x2. x1b ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length x1b. x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?B
    using 1 2 3
    unfolding init_valid_rep_def by fast
next
  assume ?B
  then have
    1: \<open>\<And>L. L\<in>x2 \<Longrightarrow> L < length x1b\<close> and
    2: \<open>\<And>L. L\<in>x2 \<Longrightarrow> x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length x1b \<longrightarrow> x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 10: \<open>\<forall>L\<in>x2. L < length ?x1b\<close>
    using 1 by fastforce
  then have 20: \<open>L\<in>x2 \<Longrightarrow> ?x1b ! L mod 2 = 1\<close> for L
    using 1[of L] 2[of L] 3[of L] by (auto simp: nth_list_update' bitOR_1_if_mod_2_nat nth_append)
  then have 30: \<open>L<length ?x1b \<Longrightarrow> ?x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>for L
    using 1[of L] 2[of L] 3[of L]
    by (auto split: if_splits simp: bitOR_1_if_mod_2_nat nth_append)
  show ?A
    using 10 20 30
    unfolding init_valid_rep_def by fast+
qed

lemma init_valid_rep_in_set_iff:
  \<open>init_valid_rep x1b x2  \<Longrightarrow> x \<in> x2 \<longleftrightarrow> (x < length x1b \<and> (x1b!x) mod 2 = 1)\<close>
  unfolding init_valid_rep_def
  by auto

lemma add_to_atms_ext_op_set_insert:
  \<open>(uncurry add_to_atms_ext, uncurry (RETURN oo op_set_insert))
   \<in> [\<lambda>(n, l). n \<le> uint_max div 2]\<^sub>f nat_rel \<times>\<^sub>f isasat_atms_ext_rel \<rightarrow> \<langle>isasat_atms_ext_rel\<rangle>nres_rel\<close>
proof -
  have H: \<open>finite x2 \<Longrightarrow> Max (insert x1 (insert 0 x2)) = Max (insert x1 x2)\<close>
    \<open>finite x2 \<Longrightarrow> Max (insert 0 (insert x1 x2)) = Max (insert x1 x2)\<close>
    for x1 and x2 :: \<open>nat set\<close>
    by (subst insert_commute) auto
  have [simp]: \<open>(a OR Suc 0) mod 2 = Suc 0\<close> for a
    by (auto simp add: bitOR_1_if_mod_2_nat)
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding isasat_atms_ext_rel_def add_to_atms_ext_def uncurry_def
    apply (refine_vcg lhs_step_If)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 x2 x1a x2a x1b x2b
      unfolding comp_def
      apply (rule RETURN_refine)
      apply (subst in_pair_collect_simp)
      apply (subst prod.case)+
      apply (intro conjI impI allI)
      subgoal by (simp add: init_valid_rep_upd_OR init_valid_rep_insert
            del: one_uint64_nat_def)
      subgoal by (auto simp: H Max_insert[symmetric] simp del: Max_insert)
      subgoal by auto
      subgoal
        using sum_mod_uint64_max_le_uint64_max
        unfolding bitOR_1_if_mod_2_nat one_uint64_nat_def
        by (auto simp del: sum_mod_uint64_max_le_uint64_max simp: uint64_max_def
            sum_mod_uint64_max_def
            elim!: in_set_upd_cases)
      subgoal
        unfolding bitAND_1_mod_2 one_uint64_nat_def
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        unfolding bitAND_1_mod_2 one_uint64_nat_def
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        unfolding bitAND_1_mod_2 one_uint64_nat_def
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        by (auto simp add: init_valid_rep_in_set_iff)
      done
    subgoal by (auto simp: uint_max_def)
    subgoal by (auto simp: uint_max_def)
    subgoal by (auto simp: uint_max_def init_next_size_def elim: neq_NilE)
    subgoal
      unfolding comp_def list_grow_def
      apply (rule RETURN_refine)
      apply (subst in_pair_collect_simp)
      apply (subst prod.case)+
      apply (intro conjI impI allI)
      subgoal
        unfolding op_set_insert_def init_next_size_def
        apply (simp del: one_uint64_nat_def)
        apply (subst init_valid_rep_insert)
        apply (auto elim: neq_NilE)
        apply (subst init_valid_rep_extend)
        apply (auto elim: neq_NilE)
        done
      subgoal by (auto simp: H Max_insert[symmetric] simp del: Max_insert)
      subgoal by (auto simp: init_next_size_def uint_max_def)
      subgoal
        using sum_mod_uint64_max_le_uint64_max
        unfolding bitOR_1_if_mod_2_nat one_uint64_nat_def
        by (auto simp del: sum_mod_uint64_max_le_uint64_max simp: uint64_max_def
            sum_mod_uint64_max_def
            elim!: in_set_upd_cases)
      subgoal by (auto simp: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      done
    done
qed


sepref_definition nat_lit_lits_init_assn_assn_in
  is \<open>uncurry add_to_atms_ext\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a isasat_atms_ext_rel_assn\<^sup>d \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_to_atms_ext_def two_uint64_nat_def[symmetric] Suc_0_le_uint64_max[simp]
    heap_array_set_u_def[symmetric]
  by sepref

lemma [sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in,  uncurry (RETURN \<circ>\<circ> op_set_insert))
  \<in> [\<lambda>(a, b). a \<le> uint_max div 2]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  by (rule nat_lit_lits_init_assn_assn_in.refine[FCOMP add_to_atms_ext_op_set_insert])

definition extract_atms_cls :: \<open>'a clause_l \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = fold (\<lambda>L \<A>\<^sub>i\<^sub>n. insert (atm_of L) \<A>\<^sub>i\<^sub>n) C \<A>\<^sub>i\<^sub>n\<close>

definition extract_atms_cls_i :: \<open>nat clause_l \<Rightarrow> nat set \<Rightarrow> nat set nres\<close> where
  \<open>extract_atms_cls_i C \<A>\<^sub>i\<^sub>n = nfoldli C (\<lambda>_. True)
       (\<lambda>L \<A>\<^sub>i\<^sub>n. do {
         ASSERT(atm_of L \<le> uint_max div 2);
         RETURN(insert (atm_of L) \<A>\<^sub>i\<^sub>n)})
    \<A>\<^sub>i\<^sub>n\<close>

lemma fild_insert_insert_swap:
  \<open>fold (\<lambda>L. insert (f L)) C (insert a \<A>\<^sub>i\<^sub>n) = insert a (fold (\<lambda>L. insert (f L)) C \<A>\<^sub>i\<^sub>n)\<close>
  by (induction C arbitrary: a \<A>\<^sub>i\<^sub>n)  (auto simp: extract_atms_cls_def)

lemma extract_atms_cls_alt_def: \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n \<union> atm_of ` set C\<close>
  by (induction C)  (auto simp: extract_atms_cls_def fild_insert_insert_swap)

sepref_definition extract_atms_cls_imp
  is \<open>uncurry extract_atms_cls_i\<close>
  :: \<open>(list_assn unat_lit_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_cls_i_def
  by sepref

lemma extract_atms_cls_i_extract_atms_cls:
  \<open>(uncurry extract_atms_cls_i, uncurry (RETURN oo extract_atms_cls))
   \<in> [\<lambda>(C, \<A>\<^sub>i\<^sub>n). \<forall>L\<in>set C. nat_of_lit L \<le> uint_max]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H1: \<open>(x1a, x1) \<in> \<langle>{(L, L'). L = L' \<and> nat_of_lit L \<le> uint_max}\<rangle>list_rel\<close>
    if
      \<open>case y of (C, \<A>\<^sub>i\<^sub>n) \<Rightarrow>  \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close> and
      \<open>(x, y) \<in> \<langle>nat_lit_lit_rel\<rangle>list_rel \<times>\<^sub>f Id\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x :: \<open>nat literal list \<times>  nat set\<close> and y :: \<open>nat literal list \<times>  nat set\<close> and
      x1 :: \<open>nat literal list\<close> and x2 :: \<open>nat set\<close> and x1a :: \<open>nat literal list\<close> and x2a :: \<open>nat set\<close>
    using that by (auto simp: list_rel_def list_all2_conj list.rel_eq list_all2_conv_all_nth)

  have atm_le: \<open>nat_of_lit xa \<le> uint_max \<Longrightarrow> atm_of xa \<le> uint_max div 2\<close> for xa
    by (cases xa) (auto simp: uint_max_def)

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding extract_atms_cls_i_def extract_atms_cls_def uncurry_def comp_def
      fold_eq_nfoldli
    apply (intro frefI nres_relI)
    apply (refine_rcg H1)
           apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: atm_le)
    subgoal by auto
    done
qed

declare extract_atms_cls_imp.refine[sepref_fr_rules]

definition extract_atms_clss:: \<open>'a clause_l list \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>  where
  \<open>extract_atms_clss N \<A>\<^sub>i\<^sub>n = fold extract_atms_cls N \<A>\<^sub>i\<^sub>n\<close>

definition extract_atms_clss_i :: \<open>nat clause_l list \<Rightarrow> nat set \<Rightarrow> nat set nres\<close>  where
  \<open>extract_atms_clss_i N \<A>\<^sub>i\<^sub>n = nfoldli N (\<lambda>_. True) extract_atms_cls_i \<A>\<^sub>i\<^sub>n\<close>


lemma extract_atms_clss_i_extract_atms_clss:
  \<open>(uncurry extract_atms_clss_i, uncurry (RETURN oo extract_atms_clss))
   \<in> [\<lambda>(N, \<A>\<^sub>i\<^sub>n). \<forall>C\<in>set N. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H1: \<open>(x1a, x1) \<in> \<langle>{(C, C'). C = C' \<and> (\<forall>L\<in>set C. nat_of_lit L \<le> uint_max)}\<rangle>list_rel\<close>
    if
      \<open>case y of (N, \<A>\<^sub>i\<^sub>n) \<Rightarrow> \<forall>C\<in>set N. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close> and
      \<open>(x, y) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x :: \<open>nat literal list list \<times> nat set\<close> and y :: \<open>nat literal list list \<times> nat set\<close> and
      x1 :: \<open>nat literal list list\<close> and x2 :: \<open>nat set\<close> and x1a :: \<open>nat literal list list\<close>
      and x2a :: \<open>nat set\<close>
    using that by (auto simp: list_rel_def list_all2_conj list.rel_eq list_all2_conv_all_nth)

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding extract_atms_clss_i_def extract_atms_clss_def comp_def fold_eq_nfoldli uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg H1 extract_atms_cls_i_extract_atms_cls[THEN fref_to_Down_curry,
          unfolded comp_def])
          apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

sepref_definition extract_atms_clss_imp
  is \<open>uncurry extract_atms_clss_i\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_atms_clss_i_def
  by sepref

lemma extract_atms_clss_hnr[sepref_fr_rules]:
  \<open>(uncurry extract_atms_clss_imp, uncurry (RETURN \<circ>\<circ> extract_atms_clss))
    \<in> [\<lambda>(a, b). \<forall>C\<in>set a. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max]\<^sub>a
      (list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow> nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp.refine[FCOMP extract_atms_clss_i_extract_atms_clss] .

lemma fold_extract_atms_cls_union_swap:
  \<open>fold extract_atms_cls N (\<A>\<^sub>i\<^sub>n \<union> a) = fold extract_atms_cls N \<A>\<^sub>i\<^sub>n \<union> a\<close>
  by (induction N arbitrary: a \<A>\<^sub>i\<^sub>n)  (auto simp: extract_atms_cls_alt_def)

lemma extract_atms_clss_alt_def:
  \<open>extract_atms_clss N \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n \<union> ((\<Union>C\<in>set N. atm_of ` set C))\<close>
  by (induction N)
    (auto simp: extract_atms_clss_def extract_atms_cls_alt_def
      fold_extract_atms_cls_union_swap)

definition op_extract_list_empty where
  \<open>op_extract_list_empty = {}\<close>

(* TODO 1024 should be replace by a proper parameter given by the parser *)
definition extract_atms_clss_imp_empty_rel where
  \<open>extract_atms_clss_imp_empty_rel = (RETURN (op_array_replicate 1024 zero_uint64_nat, 0, []))\<close>

lemma extract_atms_clss_imp_empty_rel:
  \<open>(uncurry0 extract_atms_clss_imp_empty_rel, uncurry0 (RETURN op_extract_list_empty)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>isasat_atms_ext_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (simp add:  op_extract_list_empty_def uint_max_def
      isasat_atms_ext_rel_def init_valid_rep_def extract_atms_clss_imp_empty_rel_def
       del: replicate_numeral)

sepref_definition extract_atms_clss_imp_empty_assn
  is \<open>uncurry0 extract_atms_clss_imp_empty_rel\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a isasat_atms_ext_rel_assn\<close>
  unfolding extract_atms_clss_imp_empty_rel_def zero_uint32_nat_def[symmetric]
  supply [[goals_limit=1]]
  apply (rewrite at \<open>(_, _, \<hole>)\<close> arl.fold_custom_empty)
  by sepref

lemma extract_atms_clss_imp_empty_assn[sepref_fr_rules]:
  \<open>(uncurry0 extract_atms_clss_imp_empty_assn, uncurry0 (RETURN op_extract_list_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using extract_atms_clss_imp_empty_assn.refine[FCOMP extract_atms_clss_imp_empty_rel] .

declare atm_of_hnr[sepref_fr_rules]

lemma extract_atms_cls_Nil[simp]:
  \<open>extract_atms_cls [] \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n\<close>
  unfolding extract_atms_cls_def fold.simps by simp

lemma extract_atms_clss_Cons[simp]:
  \<open>extract_atms_clss (C # Cs) N = extract_atms_clss Cs (extract_atms_cls C N)\<close>
  by (simp add: extract_atms_clss_def)

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

(* lemma in_extract_atms_clsD:
  \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = atms_of_s (set C) \<union> \<A>\<^sub>i\<^sub>n\<close>
  by (simp add: extract_atms_cls_alt_def atms_of_s_def ac_simps)

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
 *)


context isasat_input_bounded
begin


subsubsection \<open>Creation of an initial state\<close>

text \<open>The difference between this definition and \<^term>\<open>correct_watching\<close> is not really important:
  \<^enum> the former talks about all literals that can appear in the problem, while the later talks about
    all literals that appear in the problem. This is only different during the initialisation.
  \<^enum> The watch list can only contain clauses that are in the problem.
\<close>
fun (in isasat_input_ops) correct_watching_init :: \<open>nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_init (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># all_lits_of_atms_m \<A>\<^sub>i\<^sub>n.
      (\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<and> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and> is_binary N (i, K, b)) \<and>
      {#i \<in># fst `# mset (W L). i \<in># dom_m N#} =
         clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>


definition (in isasat_input_ops) init_dt_wl_heur_spec
  :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> bool\<close>
where
  \<open>init_dt_wl_heur_spec CS T TOC \<longleftrightarrow>
    (\<exists>T' TOC'. (TOC, TOC') \<in> twl_st_heur_parsing_no_WL \<and> (T, T') \<in> twl_st_heur_parsing_no_WL \<and>
        init_dt_wl_spec CS T' TOC')\<close>

definition (in isasat_input_ops) init_state :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset\<close> where
  \<open>init_state N = (
    let _ = \<A>\<^sub>i\<^sub>n in
    ([]:: (nat, nat clause) ann_lits), (N :: nat clauses), ({#}::nat clauses),
      (None :: nat clause option))\<close>

definition (in isasat_input_ops) init_state_wl :: \<open>nat twl_st_wl_init'\<close> where
  \<open>init_state_wl = ([], fmempty, None, {#}, {#}, {#})\<close>

definition (in isasat_input_ops) init_state_wl_heur :: \<open>twl_st_wl_heur_init nres\<close> where
  \<open>init_state_wl_heur = do {
    D \<leftarrow> SPEC(\<lambda>D. (D, None) \<in> option_lookup_clause_rel);
    W \<leftarrow> SPEC (\<lambda>W. (W, empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0);
    vm \<leftarrow> RES (vmtf_init []);
    \<phi> \<leftarrow> SPEC phase_saving;
    cach \<leftarrow> SPEC cach_refinement_empty;
    let lbd = empty_lbd;
    let vdom = [];
    RETURN ([], [], D, zero_uint32_nat, W, vm, \<phi>, zero_uint32_nat, cach, lbd, vdom)}\<close>

definition (in isasat_input_ops) init_state_wl_heur_fast where
  \<open>init_state_wl_heur_fast = init_state_wl_heur\<close>


lemma (in isasat_input_ops) init_state_wl_heur_init_state_wl:
  \<open>(uncurry0 init_state_wl_heur, uncurry0 (RETURN init_state_wl)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL_wl\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: init_state_wl_heur_def init_state_wl_def
        RES_RETURN_RES bind_RES_RETURN_eq RES_RES_RETURN_RES RETURN_def
        twl_st_heur_parsing_no_WL_wl_def vdom_m_def empty_watched_def valid_arena_empty
        intro!: RES_refine)
(* 
lemma (in isasat_input_ops) get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur_parsing_no_WL_wl \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_parsing_no_WL_wl_def option_lookup_clause_rel_def
      get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_def
      split: option.splits) *)

(*
 lemma get_conflict_wl_is_None_init_wl_hnr[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_init_code, RETURN \<circ> get_conflict_wl_is_None)
    \<in> twl_st_init_wl_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_init_code_hnr[FCOMP get_conflict_wl_is_None_heur_get_conflict_wl_is_None]
  unfolding isasat_init_assn_def[symmetric]twl_st_init_wl_assn_def[symmetric]
  . *)

definition (in -)to_init_state :: \<open>nat twl_st_wl_init' \<Rightarrow> nat twl_st_wl_init\<close> where
  \<open>to_init_state S = (S, {#})\<close>

definition (in -) from_init_state :: \<open>nat twl_st_wl_init_full \<Rightarrow> nat twl_st_wl\<close> where
  \<open>from_init_state = fst\<close>

(* 
lemma (in isasat_input_ops) get_conflict_wl_is_None_heur_init_get_conflict_wl_is_None_init:
  \<open>(T, Ta) \<in> twl_st_heur_parsing_no_WL  \<Longrightarrow>
    get_conflict_wl_is_None_heur_init T \<longleftrightarrow> get_conflict_wl_is_None_init (from_init_state Ta)\<close>
  by (cases T; cases Ta) (auto simp: get_conflict_wl_is_None_heur_init_def twl_st_heur_parsing_no_WL_def
      get_conflict_wl_is_None_init_def from_init_state_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def
      split: option.splits) *)

lemma (in isasat_input_ops) id_to_init_state:
  \<open>(RETURN o id, RETURN o to_init_state) \<in> twl_st_heur_parsing_no_WL_wl \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL_wl_no_watched_full\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: to_init_state_def twl_st_heur_parsing_no_WL_wl_def twl_st_heur_parsing_no_WL_wl_no_watched_full_def
      twl_st_heur_parsing_no_WL_def)

definition (in -) to_init_state_code where
  \<open>to_init_state_code = id\<close>

lemma (in isasat_input_ops) to_init_state_code_hnr:
  \<open>(return o to_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding to_init_state_code_def
  by (rule id_ref)

(*
lemma (in isasat_input_ops) to_init_state_hnr[sepref_fr_rules]:
 \<open>(return \<circ> to_init_state_code, RETURN \<circ> to_init_state) \<in>
   twl_st_init_wl_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_assn\<close>
  using to_init_state_code_hnr[FCOMP id_to_init_state]
  unfolding twl_st_init_wl_assn_def twl_st_init_assn_def .


lemma (in isasat_input_ops) id_from_init_state:
  \<open>(RETURN o id, RETURN o from_init_state) \<in> twl_st_heur_parsing_no_WL_wl_full \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL_wl\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: from_init_state_def twl_st_heur_parsing_no_WL_wl_def
      twl_st_heur_parsing_no_WL_def twl_st_heur_parsing_no_WL_wl_full_def)
*)

definition from_init_state_code where
  \<open>from_init_state_code = id\<close>

(*
lemma (in isasat_input_ops) from_init_state_code_hnr:
  \<open>(return o from_init_state_code, RETURN o id) \<in> isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  unfolding from_init_state_code_def
  by (rule id_ref)

lemma (in isasat_input_ops) from_init_state_hnr[sepref_fr_rules]:
 \<open>(return \<circ> from_init_state_code, RETURN \<circ> from_init_state) \<in>
   twl_st_init_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_init_wl_assn\<close>
  using from_init_state_code_hnr[FCOMP id_from_init_state]
  unfolding twl_st_init_wl_assn_def twl_st_init_assn_def .
*)
definition  (in -) conflict_is_None_heur_wl where
  \<open>conflict_is_None_heur_wl = (\<lambda>(M, N, U, D, _). is_None D)\<close>

definition (in -) finalise_init where
  \<open>finalise_init = id\<close>


subsection \<open>Parsing\<close>

lemma (in isasat_input_bounded) init_dt_wl_heur_init_dt_wl:
  \<open>(uncurry init_dt_wl_heur, uncurry init_dt_wl) \<in>
    [\<lambda>(CS, S). (\<forall>C \<in> set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)) \<and> distinct_mset_set (mset ` set CS)]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f twl_st_heur_parsing_no_WL \<rightarrow> \<langle>twl_st_heur_parsing_no_WL\<rangle> nres_rel\<close>
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
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
    done
qed


subsection \<open>Rewatch\<close>

definition (in isasat_input_ops) rewatch_heur where
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        ASSERT(arena_lit_pre arena C);
        ASSERT(arena_lit_pre arena (C+1));
        let L1 = arena_lit arena C;
        let L2 = arena_lit arena (C + 1);
        ASSERT(L1 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
        ASSERT(nat_of_lit L1 < length W);
        ASSERT(arena_is_valid_clause_idx arena C);
        let b = (arena_length arena C = 2);
        let W = append_ll W (nat_of_lit L1) (to_watcher C L2 b);
        ASSERT(L2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
        ASSERT(nat_of_lit L2 < length W);
        let W = append_ll W (nat_of_lit L2) (to_watcher C L1 b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>


lemma rewatch_heur_rewatch:
  assumes
    \<open>valid_arena arena N vdom\<close> and \<open>set xs \<subseteq> vdom\<close> and \<open>distinct xs\<close> and \<open>set_mset (dom_m N) \<subseteq> set xs\<close> and
    \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and lall: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf N)\<close> and
    \<open>vdom_m W' N \<subseteq> set_mset (dom_m N)\<close>
  shows
    \<open>rewatch_heur xs arena W \<le> \<Down> ({(W, W'). (W, W') \<in>\<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and> vdom_m W' N \<subseteq> set_mset (dom_m N)}) (rewatch N W')\<close>
proof -
  have [refine0]: \<open>(xs, xsa) \<in> Id \<Longrightarrow>
     ([0..<length xs], [0..<length xsa]) \<in> \<langle>{(x, x'). x = x' \<and> xs!x \<in> vdom}\<rangle>list_rel\<close>
    for xsa
    using assms unfolding list_rel_def 
    by (auto simp: list_all2_same)
  show ?thesis
    unfolding rewatch_heur_def rewatch_def
    apply (subst (2) nfoldli_nfoldli_list_nth)
    apply (refine_vcg)
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal by fast
    subgoal
      using assms
      unfolding arena_is_valid_clause_vdom_def
      by blast
    subgoal
      using assms
      by (auto simp: arena_dom_status_iff)
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (rule_tac j=\<open>xs ! xi\<close> in bex_leI)
        (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (rule_tac j=\<open>xs ! xi\<close> in bex_leI)
        (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of \<open>xs ! xi\<close> 0] assms
      by (auto simp flip: length_greater_0_conv simp: arena_lifting)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      unfolding arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def
      by (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1] assms
      by (auto simp flip: length_greater_0_conv simp: arena_lifting)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    done
qed

sepref_register rewatch_heur

sepref_thm rewatch_heur_code
  is \<open>uncurry2 (PR_CONST rewatch_heur)\<close>
  :: \<open>vdom_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a watchlist_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
  by sepref

concrete_definition (in -) rewatch_heur_code
  uses "isasat_input_bounded.rewatch_heur_code.refine_raw"
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) rewatch_heur_code_def

lemmas rewatch_heur_hnr[sepref_fr_rules] =
  rewatch_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


definition (in isasat_input_ops) rewatch_heur_st
 :: \<open>twl_st_wl_heur_init_full \<Rightarrow> twl_st_wl_heur_init_full nres\<close>
where
\<open>rewatch_heur_st = (\<lambda>(M', N', D', j, W, vm, \<phi>, clvls, cach, lbd, vdom). do {
  W \<leftarrow> rewatch_heur vdom N' W;
  RETURN (M', N', D', j, W, vm, \<phi>, clvls, cach, lbd, vdom)
  })\<close>

sepref_thm rewatch_heur_st_code
  is \<open>(PR_CONST rewatch_heur_st)\<close>
  :: \<open>isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def
    isasat_init_assn_def
  by sepref


concrete_definition (in -) rewatch_heur_st_code
  uses "isasat_input_bounded.rewatch_heur_st_code.refine_raw"
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) rewatch_heur_st_code_def

lemmas rewatch_heur_st_hnr[sepref_fr_rules] =
  rewatch_heur_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma (in isasat_input_bounded) rewatch_heur_st_correct_watching:
  assumes
    \<open>(S, T) \<in> twl_st_heur_parsing_no_WL\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf (get_clauses_init_wl T))\<close> and
    \<open>\<And>x. x \<in># dom_m (get_clauses_init_wl T) \<Longrightarrow> distinct (get_clauses_init_wl T \<propto> x) \<and>
        2 \<le> length (get_clauses_init_wl T \<propto> x)\<close>
  shows \<open>rewatch_heur_st S \<le> \<Down> twl_st_heur_parsing (SPEC (\<lambda>((M,N, D, NE, UE, Q, W), OC). T = ((M,N,D,NE,UE,Q), OC)\<and>
    correct_watching (M, N, D, NE, UE, Q, W)))\<close>
proof -
  obtain M N D NE UE Q OC where
    T: \<open>T = ((M,N, D, NE, UE, Q), OC)\<close>
    by (cases T) auto

  obtain M' N' D' j W vm \<phi> clvls cach lbd vdom where
    S: \<open>S = (M', N', D', j, W, vm, \<phi>, clvls, cach, lbd, vdom)\<close>
    by (cases S) auto

  have valid: \<open>valid_arena N' N (set vdom)\<close> and
    dist: \<open>distinct vdom\<close> and
    dom_m_vdom: \<open>set_mset (dom_m N) \<subseteq> set vdom\<close> and
    W: \<open>(W, empty_watched) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf N)\<close>
    using assms distinct_mset_dom[of N] apply (auto simp: twl_st_heur_parsing_no_WL_def S T
      simp flip: distinct_mset_mset_distinct)
    by (metis distinct_mset_set_mset_ident set_mset_mset subset_mset.eq_iff)
  have H: \<open>RES ({(W, W').
          (W, W') \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and> vdom_m W' N \<subseteq> set_mset (dom_m N)}\<inverse> ``
         {W. Watched_Literals_Watch_List_Initialisation.correct_watching_init
              (M, N, D, NE, UE, Q, W)})
    \<le> RES ({(W, W').
          (W, W') \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and> vdom_m W' N \<subseteq> set_mset (dom_m N)}\<inverse> ``
         {W. Watched_Literals_Watch_List_Initialisation.correct_watching_init
              (M, N, D, NE, UE, Q, W)})\<close>
    for W'
    by (rule order.refl)
  have eq: \<open>Watched_Literals_Watch_List_Initialisation.correct_watching_init
        (M, N, None, NE, UE, {#}, xa) \<Longrightarrow>
       vdom_m xa N = set_mset (dom_m N)\<close> for xa
    by (auto 5 5 simp: Watched_Literals_Watch_List_Initialisation.correct_watching_init.simps
      vdom_m_def)
  show ?thesis
    supply [[goals_limit=1]]
    using assms
    unfolding rewatch_heur_st_def T S
    apply clarify
    apply (rule bind_refine_res)
    prefer 2
    apply (rule order.trans)
    apply (rule rewatch_heur_rewatch[OF valid _ dist dom_m_vdom W lits])
    apply (solves simp)
    apply (solves simp)
    apply (rule order_trans[OF conc_fun_mono])
    apply (rule rewatch_correctness)
    apply (rule empty_watched_alt_def)
    subgoal
      using assms
      by (auto simp: twl_st_heur_parsing_no_WL_def)
    apply (subst conc_fun_RES)
    apply (rule H)
    apply (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      intro!: exI[of _ N] exI[of _ D]
      intro!: RETURN_RES_refine)
    apply (rule_tac x=W' in exI)
    apply (auto simp: eq correct_watching_init_correct_watching)
    done
qed



subsubsection \<open>Full Initialisation\<close>

definition (in isasat_input_ops) init_dt_wl_heur_full
  :: \<open>_ \<Rightarrow> twl_st_wl_heur_init_full \<Rightarrow> twl_st_wl_heur_init_full nres\<close>
where
\<open>init_dt_wl_heur_full CS S = do {
    S \<leftarrow> init_dt_wl_heur CS S;
    rewatch_heur_st S
  }\<close>

lemma init_dt_wl_heur_full_init_dt_wl_full:
  assumes 
    \<open>init_dt_wl_pre CS T\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close> and
    \<open>distinct_mset_set (mset ` set CS)\<close> and
    \<open>(S, T) \<in> twl_st_heur_parsing_no_WL\<close>
  shows \<open>init_dt_wl_heur_full CS S
         \<le> \<Down> twl_st_heur_parsing (init_dt_wl_full CS T)\<close>
proof -
  have H: \<open>valid_arena x1g x1b (set (x2o))\<close> \<open>set x2o \<subseteq> set x2o\<close> \<open>set_mset (dom_m x1b) \<subseteq> set x2o\<close>
    \<open>distinct x2o\<close> \<open>(x1j, \<lambda>_. []) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close>
    if 
      xx': \<open>(x, x') \<in> twl_st_heur_parsing_no_WL\<close> and
      st: \<open>x2c = (x1e, x2d)\<close>
        \<open>x2b = (x1d, x2c)\<close>
        \<open>x2a = (x1c, x2b)\<close>
        \<open>x2 = (x1b, x2a)\<close>
        \<open>x1 = (x1a, x2)\<close>
        \<open>x' = (x1, x2e)\<close>
        \<open>x2n = (x1o, x2o)\<close>
        \<open>x2m = (x1n, x2n)\<close>
        \<open>x2l = (x1m, x2m)\<close>
        \<open>x2k = (x1l, x2l)\<close>
        \<open>x2j = (x1k, x2k)\<close>
        \<open>x2i = (x1j, x2j)\<close>
        \<open>x2h = (x1i, x2i)\<close>
        \<open>x2g = (x1h, x2h)\<close>
        \<open>x2f = (x1g, x2g)\<close>
        \<open>x = (x1f, x2f)\<close>
    for x x' x1 x1a x2 x1b x2a x1c x2b x1d x2c x1e x2d x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o
  proof -
    show \<open>valid_arena x1g x1b (set (x2o))\<close> \<open>set x2o \<subseteq> set x2o\<close> \<open>set_mset (dom_m x1b) \<subseteq> set x2o\<close>
      \<open>distinct x2o\<close> \<open>(x1j, \<lambda>_. []) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0\<close>
    using xx' distinct_mset_dom[of x1b] unfolding st
      by (auto simp: twl_st_heur_parsing_no_WL_def empty_watched_alt_def
        simp flip: set_mset_mset distinct_mset_mset_distinct)
  qed

  show ?thesis
    unfolding init_dt_wl_heur_full_def init_dt_wl_full_def rewatch_heur_st_def
    apply (refine_rcg rewatch_heur_rewatch
      init_dt_wl_heur_init_dt_wl[THEN fref_to_Down_curry])
    subgoal using assms by fast
    subgoal using assms by fast
    subgoal using assms by auto
    apply ((rule H; assumption)+)[5]
    subgoal
      by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_of_mm_union)
    subgoal by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      empty_watched_alt_def[symmetric])
    subgoal by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      empty_watched_alt_def[symmetric])
    done
qed


lemma init_dt_wl_heur_full_init_dt_wl_spec_full:
  assumes 
    \<open>init_dt_wl_pre CS T\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close> and
    \<open>distinct_mset_set (mset ` set CS)\<close> and
    \<open>(S, T) \<in> twl_st_heur_parsing_no_WL\<close>
  shows \<open>init_dt_wl_heur_full CS S
      \<le>  \<Down> twl_st_heur_parsing (SPEC (init_dt_wl_spec_full CS T))\<close>
  apply (rule order.trans)
  apply (rule init_dt_wl_heur_full_init_dt_wl_full[OF assms])
  apply (rule conc_fun_mono)
  apply (rule init_dt_wl_full_init_dt_wl_spec_full[OF assms(1)])
  done

sepref_register rewatch_heur_st init_dt_step_wl_heur

sepref_thm init_dt_wl_heur_code
  is \<open>uncurry (PR_CONST init_dt_wl_heur)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_def PR_CONST_def
  by sepref

concrete_definition (in -) init_dt_wl_heur_code
  uses "isasat_input_bounded.init_dt_wl_heur_code.refine_raw"
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) init_dt_wl_heur_code_def


lemmas init_dt_wl_heur_hnr[sepref_fr_rules] =
  init_dt_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm init_dt_wl_heur_full_code
  is \<open>uncurry (PR_CONST init_dt_wl_heur_full)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_init_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_wl_heur_full_def PR_CONST_def
  by sepref

concrete_definition (in -) init_dt_wl_heur_full_code
  uses "isasat_input_bounded.init_dt_wl_heur_full_code.refine_raw"
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) init_dt_wl_heur_full_code_def

lemmas init_dt_wl_heur_full_hnr[sepref_fr_rules] =
  init_dt_wl_heur_full_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

end


subsection \<open>Conversion to normal state\<close>

context isasat_input_bounded
begin


(* sepref_thm init_dt_wl_fast_code
  is \<open>uncurry (PR_CONST init_dt_wl_heur_fast)\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>d *\<^sub>a isasat_init_fast_assn\<^sup>d \<rightarrow>\<^sub>a
       isasat_init_fast_assn\<close>
  unfolding init_dt_wl_heur_fast_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) init_dt_wl_fast_code
  uses "isasat_input_bounded.init_dt_wl_fast_code.refine_raw"
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) init_dt_wl_fast_code_def

thm init_dt_wl_heur_code_def
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

prepare_code_thms (in -) init_dt_wl_code_def *)
end

definition (in -)insert_sort_inner_nth2 :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_inner_nth2 ns = insert_sort_inner (>) (\<lambda>remove n. ns ! (remove ! n))\<close>

definition (in -)insert_sort_nth2 :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  [code del]: \<open>insert_sort_nth2 = (\<lambda>ns. insert_sort (>) (\<lambda>remove n. ns ! (remove ! n)))\<close>

sepref_definition (in -) insert_sort_inner_nth_code
   is \<open>uncurry2 insert_sort_inner_nth2\<close>
   :: \<open>[\<lambda>((xs, vars), n). (\<forall>x\<in>#mset vars. x < length xs) \<and> n < length vars]\<^sub>a
  (array_assn uint64_nat_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
  arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_inner_nth2_def insert_sort_inner_def fast_minus_def[symmetric]
    short_circuit_conv
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest] insert_sort_inner_nth_code_helper[intro]
    if_splits[split]
  by sepref


declare insert_sort_inner_nth_code.refine[sepref_fr_rules]

sepref_definition (in -) insert_sort_nth_code
   is \<open>uncurry insert_sort_nth2\<close>
   :: \<open>[\<lambda>(xs, vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      (array_assn uint64_nat_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_nth2_def insert_sort_def insert_sort_inner_nth2_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare insert_sort_nth_code.refine[sepref_fr_rules]

declare insert_sort_nth2_def[unfolded insert_sort_def insert_sort_inner_def, code]

definition extract_lits_sorted where
  \<open>extract_lits_sorted = (\<lambda>(xs, n, vars). do {
    vars \<leftarrow> \<comment>\<open>insert\_sort\_nth2 xs\<close>
         RETURN vars;
    RETURN (vars, n)})\<close>

definition lits_with_max_rel where
  \<open>lits_with_max_rel = {((xs, n), \<A>\<^sub>i\<^sub>n). mset xs = \<A>\<^sub>i\<^sub>n \<and> n = Max (insert 0 (set xs)) \<and>
    length xs < uint32_max}\<close>

lemma extract_lits_sorted_mset_set:
  \<open>(extract_lits_sorted, RETURN o mset_set)
   \<in> isasat_atms_ext_rel \<rightarrow>\<^sub>f \<langle>lits_with_max_rel\<rangle>nres_rel\<close>
proof -
  have K: \<open>RETURN o mset_set = (\<lambda>v. do {v' \<leftarrow> SPEC(\<lambda>v'. v' = mset_set v); RETURN v'})\<close>
    by auto
  have H: \<open>ba < length aa \<Longrightarrow> insert_sort_inner (\<lambda>x y. y < x) f aa ba \<le> SPEC (\<lambda>m'. mset m' = mset aa)\<close>
    for ba aa f
    using insert_sort_inner[unfolded fref_def nres_rel_def reorder_remove_def, simplified, rule_format]
    by fast
  have K': \<open>length x2a < uint32_max\<close> if \<open>distinct b\<close> \<open>init_valid_rep x1 (set b)\<close>
    \<open>length x1 < uint_max\<close> \<open>mset x2a = mset b\<close>for x1 x2a b
  proof -
    have \<open>distinct x2a\<close>
      by (simp add: same_mset_distinct_iff that(1) that(4))
    have \<open>length x2a = length b\<close> \<open>set x2a = set b\<close>
      using \<open>mset x2a = mset b\<close> apply (metis size_mset)
       using \<open>mset x2a = mset b\<close> by (rule mset_eq_setD)
    then have \<open>set x2a \<subseteq> {0..<uint_max - 1}\<close>
      using that by (auto simp: init_valid_rep_def)
    from card_mono[OF _ this] show ?thesis
      using \<open>distinct x2a\<close> by (auto simp: uint_max_def distinct_card)
  qed
  have H_simple: \<open>RETURN x2a
      \<le> \<Down> (list_mset_rel \<inter> {(v, v'). length v < uint_max})
          (SPEC (\<lambda>v'. v' = mset_set y))\<close>
    if
      \<open>(x, y) \<in> isasat_atms_ext_rel\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x = (x1, x2)\<close>
    for x :: \<open>nat list \<times> nat \<times> nat list\<close> and y :: \<open>nat set\<close> and x1 :: \<open>nat list\<close> and
      x2 :: \<open>nat \<times> nat list\<close> and x1a :: \<open>nat\<close> and x2a :: \<open>nat list\<close>
    unfolding insert_sort_nth2_def insert_sort_def conc_fun_SPEC
    apply (refine_vcg)
    using that mset_eq_length by (auto simp: isasat_atms_ext_rel_def list_mset_rel_def br_def
          mset_set_set intro: K' dest: mset_eq_length)
  have H': \<open>insert_sort_nth2 x1 x2a
      \<le> \<Down> (list_mset_rel \<inter> {(v, v'). length v < uint_max})
          (SPEC (\<lambda>v'. v' = mset_set y))\<close>
    if
      \<open>(x, y) \<in> isasat_atms_ext_rel\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x = (x1, x2)\<close>
    for x :: \<open>nat list \<times> nat \<times> nat list\<close> and y :: \<open>nat set\<close> and x1 :: \<open>nat list\<close> and
      x2 :: \<open>nat \<times> nat list\<close> and x1a :: \<open>nat\<close> and x2a :: \<open>nat list\<close>
    unfolding insert_sort_nth2_def insert_sort_def conc_fun_SPEC
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, ys). length ys - i)\<close>] H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using mset_eq_length by force
    subgoal by auto
    subgoal using mset_eq_length by force
    subgoal using that mset_eq_length
      by (auto simp: isasat_atms_ext_rel_def list_mset_rel_def br_def
          mset_set_set intro: K' dest: mset_eq_length)
    done
  show ?thesis
    unfolding extract_lits_sorted_def reorder_remove_def K
    apply (intro frefI nres_relI)
    apply (refine_vcg H_simple H')
       apply assumption+
    by (auto simp: lits_with_max_rel_def isasat_atms_ext_rel_def mset_set_set list_mset_rel_def
        br_def dest!: mset_eq_setD)
qed

sepref_definition (in -) extract_lits_sorted_code
   is \<open>extract_lits_sorted\<close>
   :: \<open>[\<lambda>(xs, n, vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      isasat_atms_ext_rel_assn\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn *a uint32_nat_assn\<close>
  unfolding extract_lits_sorted_def
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare extract_lits_sorted_code.refine[sepref_fr_rules]

abbreviation lits_with_max_assn where
  \<open>lits_with_max_assn \<equiv> hr_comp (arl_assn uint32_nat_assn *a uint32_nat_assn) lits_with_max_rel\<close>

lemma extract_lits_sorted_hnr[sepref_fr_rules]:
  \<open>(extract_lits_sorted_code, RETURN \<circ> mset_set) \<in> nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a lits_with_max_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE isasat_atms_ext_rel (\<lambda>_. True)
         (\<lambda>_ (xs, n, vars). \<forall>x\<in>#mset vars. x < length xs) (\<lambda>_. True)]\<^sub>a
       hrp_comp (isasat_atms_ext_rel_assn\<^sup>d) isasat_atms_ext_rel \<rightarrow> lits_with_max_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_lits_sorted_code.refine
    extract_lits_sorted_mset_set] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def isasat_atms_ext_rel_def init_valid_rep_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by simp
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    using pre ..
qed

text \<open>TODO Move\<close>

text \<open>The value 160 is random (but larger than the default 16 for array lists).\<close>
definition finalise_init_code :: \<open>opts \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>finalise_init_code opts =
    (\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls, cach,
       lbd, vdom). do {
     ASSERT(lst_As \<noteq> None \<and> fst_As \<noteq> None);
     let init_stats = (0::uint64, 0::uint64, 0::uint64, 0::uint64, 0::uint64);
     let fema = ema_fast_init;
     let sema = ema_slow_init;
     let ccount = restart_info_init;
     let lcount = 0;
    RETURN (M', N', D', Q', W', ((ns, m, the fst_As, the lst_As, next_search), to_remove), \<phi>,
       clvls, cach, lbd, take1(replicate 160 (Pos zero_uint32_nat)), init_stats,
        fema, sema, ccount, vdom, [], lcount, opts)
     })\<close>

lemma (in isasat_input_ops)finalise_init_finalise_init:
  \<open>(uncurry finalise_init_code, uncurry (RETURN oo (\<lambda>_. finalise_init))) \<in>
   [\<lambda>(_, S::nat twl_st_wl). get_conflict_wl S = None \<and> \<A>\<^sub>i\<^sub>n \<noteq> {#} \<and>
      size (learned_clss_l (get_clauses_wl S)) = 0]\<^sub>f Id \<times>\<^sub>r
      twl_st_heur_post_parsing_wl \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: finalise_init_def twl_st_heur_def twl_st_heur_parsing_no_WL_def twl_st_heur_parsing_no_WL_wl_def
      finalise_init_code_def vmtf_init_def out_learned_def take1_def
      twl_st_heur_post_parsing_wl_def
      intro!: ASSERT_leI)

sepref_thm (in isasat_input_ops) finalise_init_code'
  is \<open>uncurry finalise_init_code\<close>
  :: \<open>opts_assn\<^sup>d *\<^sub>a isasat_init_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply zero_uin64_hnr[sepref_fr_rules] [[goals_limit=1]]
    Pos_unat_lit_assn'[sepref_fr_rules] uint_max_def[simp] op_arl_replicate_def[simp]
  unfolding finalise_init_code_def isasat_init_assn_def isasat_unbounded_assn_def
    arl.fold_custom_empty arl_fold_custom_replicate two_uint32_def[symmetric]
  by sepref

concrete_definition (in -) finalise_init_code'
   uses isasat_input_ops.finalise_init_code'.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) finalise_init_code'_def

lemmas (in isasat_input_ops)finalise_init_hnr[sepref_fr_rules] =
   finalise_init_code'.refine[of \<A>\<^sub>i\<^sub>n]

(*
sepref_thm (in isasat_input_ops) finalise_init_fast_code'
  is \<open>finalise_init_code\<close>
  :: \<open>isasat_init_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply zero_uin64_hnr[sepref_fr_rules] [[goals_limit=1]]
    Pos_unat_lit_assn'[sepref_fr_rules] uint_max_def[simp] op_arl_replicate_def[simp]
  unfolding finalise_init_code_def isasat_init_fast_assn_def isasat_bounded_assn_def
    arl.fold_custom_empty arl_fold_custom_replicate two_uint32_def[symmetric]
  by sepref

concrete_definition (in -) finalise_init_fast_code'
   uses isasat_input_ops.finalise_init_fast_code'.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) finalise_init_fast_code'_def

lemmas (in isasat_input_ops)finalise_init_fast_hnr[sepref_fr_rules] =
   finalise_init_fast_code'.refine[of \<A>\<^sub>i\<^sub>n] *)

definition (in -) init_rll :: \<open>nat \<Rightarrow> (nat, 'v clause_l \<times> bool) fmap\<close> where
  \<open>init_rll n = fmempty\<close>

definition (in -) init_aa :: \<open>nat \<Rightarrow> 'v list\<close> where
  \<open>init_aa n = []\<close>


lemma (in -)arrayO_raa_empty_sz_empty_list[sepref_fr_rules]:
  \<open>(arrayO_raa_empty_sz, RETURN o init_aa) \<in>
    nat_assn\<^sup>k \<rightarrow>\<^sub>a (arlO_assn clause_ll_assn)\<close>
  by sepref_to_hoare (sep_auto simp: init_rll_def hr_comp_def clauses_ll_assn_def init_aa_def)

definition (in -) init_aa' :: \<open>nat \<Rightarrow> (clause_status \<times> nat \<times> nat) list\<close> where
  \<open>init_aa' n = []\<close>

lemma init_aa'_alt_def: \<open>RETURN o init_aa' = (\<lambda>n. RETURN op_arl_empty)\<close>
  by (auto simp: init_aa'_def op_arl_empty_def)

sepref_definition init_aa'_code
  is \<open>RETURN o init_aa'\<close>
  :: \<open>nat_assn\<^sup>k \<rightarrow>\<^sub>a arl_assn (clause_status_assn *a uint32_nat_assn *a uint32_nat_assn)\<close>
  unfolding init_aa'_alt_def
  by sepref

declare init_aa'_code.refine[sepref_fr_rules]


definition init_trail_D :: \<open>uint32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> trail_pol nres\<close> where
  \<open>init_trail_D \<A>\<^sub>i\<^sub>n n m = do {
     let M0 = [];
     let cs = [];
     let M = replicate m UNSET;
     let M' = replicate n zero_uint32_nat;
     let M'' = replicate n 1;
     RETURN ((M0, M, M', M'', zero_uint32_nat, cs))
  }\<close>

sepref_register initialise_VMTF


sepref_definition init_trail_D_code
  is \<open>uncurry2 init_trail_D\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding init_trail_D_def PR_CONST_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_code.refine[sepref_fr_rules]


definition init_trail_D_fast where
  \<open>init_trail_D_fast = init_trail_D\<close>

sepref_definition init_trail_D_fast_code
  is \<open>uncurry2 init_trail_D_fast\<close>
  :: \<open>(arl_assn uint32_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_fast_assn\<close>
  unfolding init_trail_D_def PR_CONST_def init_trail_D_fast_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> arl.fold_custom_empty)
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>array_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> array_fold_custom_replicate)
  apply (rewrite in \<open>let _ = op_array_replicate _ \<hole> in _\<close> one_uint64_nat_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare init_trail_D_fast_code.refine[sepref_fr_rules]

definition (in isasat_input_ops) init_state_wl_D' :: \<open>uint32 list \<times> uint32 \<Rightarrow>  (trail_pol \<times> _ \<times> _) nres\<close> where
  \<open>init_state_wl_D' = (\<lambda>(\<A>\<^sub>i\<^sub>n, n). do {
     let n = Suc (nat_of_uint32 n);
     let m = 2 * n;
     ASSERT(\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < n);
     M \<leftarrow> init_trail_D \<A>\<^sub>i\<^sub>n n m;
     let N = [];
     let D = (True, zero_uint32_nat, replicate n NOTIN);
     let WS = init_lrl m;
     vm \<leftarrow> initialise_VMTF \<A>\<^sub>i\<^sub>n n;
     let \<phi> = replicate n False;
     let cach = (replicate n SEEN_UNKNOWN, []);
     let lbd = empty_lbd;
     let vdom = op_arl_empty;
     RETURN (M, N, D, zero_uint32_nat, WS, vm, \<phi>, zero_uint32_nat, cach, lbd, vdom)
  })\<close>

sepref_thm (in isasat_input_ops) init_state_wl_D'_code
  is \<open>PR_CONST init_state_wl_D'\<close>
  :: \<open>(arl_assn uint32_assn *a uint32_assn)\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn *a arena_assn *a
    conflict_option_rel_assn *a
    uint32_nat_assn *a
    (arrayO_assn (arl_assn watcher_assn)) *a
    vmtf_remove_conc_option_fst_As *a
    phase_saver_conc *a uint32_nat_assn *a
    cach_refinement_l_assn *a lbd_assn *a vdom_assn\<close>
  unfolding init_state_wl_D'_def PR_CONST_def
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> arl.fold_custom_empty)
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in let _ = (True, _, _) in _\<close> arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_assn\<close>])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>(arrayO_assn (arl_assn watcher_assn))\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) init_state_wl_D'_code
   uses isasat_input_ops.init_state_wl_D'_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) init_state_wl_D'_code_def

lemmas (in isasat_input_ops)init_state_wl_D'_hnr[sepref_fr_rules] =
   init_state_wl_D'_code.refine[of \<A>\<^sub>i\<^sub>n] 

sepref_thm (in isasat_input_ops) init_state_wl_D'_fast_code
  is \<open>PR_CONST init_state_wl_D'\<close>
  :: \<open>(arl_assn uint32_assn *a uint32_assn)\<^sup>d \<rightarrow>\<^sub>a trail_pol_fast_assn *a arena_assn *a
    conflict_option_rel_assn *a
    uint32_nat_assn *a
    (arrayO_assn (arl_assn (watcher_fast_assn))) *a
    vmtf_remove_conc_option_fst_As *a
    phase_saver_conc *a uint32_nat_assn *a
    cach_refinement_l_assn *a lbd_assn *a vdom_assn\<close>
  unfolding init_state_wl_D'_def init_trail_D_fast_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>let _ = (_, \<hole>) in _\<close> arl.fold_custom_empty)
  unfolding array_fold_custom_replicate
  apply (rewrite at \<open>let _ = \<hole> in let _ = (True, _, _) in _\<close> arl.fold_custom_empty)
  apply (rewrite at \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arena_assn\<close>])
  apply (rewrite at \<open>let _= _; _= \<hole> in _\<close> annotate_assn[where A=\<open>(arrayO_assn (arl_assn watcher_fast_assn))\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) init_state_wl_D'_fast_code
   uses isasat_input_ops.init_state_wl_D'_fast_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) init_state_wl_D'_fast_code_def

lemmas (in isasat_input_ops)init_state_wl_D'_fast_hnr[sepref_fr_rules] =
   init_state_wl_D'_fast_code.refine[of \<A>\<^sub>i\<^sub>n] 


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
    subgoal
      by (auto simp: zero_uint32_def shiftr1_def
        nat_shiftr_div2 nat_of_uint32_shiftr isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def isasat_input_ops.trail_pol_def K atms_of_def
        isasat_input_ops.phase_saving_def list_rel_mset_rel_def
        list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        isasat_input_ops.ann_lits_split_reasons_def control_stack.empty
      list_mset_rel_def Collect_eq_comp)
    done
qed

abbreviation (in -)lits_with_max_assn_clss where
  \<open>lits_with_max_assn_clss \<equiv> hr_comp lits_with_max_assn (\<langle>nat_rel\<rangle>mset_rel)\<close>

lemma init_state_wl_D':
  \<open>(isasat_input_ops.init_state_wl_D' \<A>\<^sub>i\<^sub>n, isasat_input_ops.init_state_wl_heur) \<in>
    [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>f
      lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>mset_rel \<rightarrow>
      \<langle>isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n \<times>\<^sub>r Id \<times>\<^sub>r
         Id \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>r
           Id \<times>\<^sub>r \<langle>bool_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r isasat_input_ops.cach_refinement \<A>\<^sub>i\<^sub>n \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  (is \<open>?C \<in> [?Pre]\<^sub>f ?arg \<rightarrow> \<langle>?im\<rangle>nres_rel\<close>)
proof -
  have init_state_wl_heur_alt_def: \<open>isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n = do {
    let M = [];
    N \<leftarrow> RETURN [];
    D \<leftarrow> SPEC (\<lambda>D. (D, None) \<in> isasat_input_ops.option_lookup_clause_rel \<A>\<^sub>i\<^sub>n);
    W \<leftarrow> SPEC (\<lambda>W. (W, isasat_input_ops.empty_watched \<A>\<^sub>i\<^sub>n ) \<in> \<langle>Id\<rangle>map_fun_rel (isasat_input_ops.D\<^sub>0 \<A>\<^sub>i\<^sub>n));
    vm \<leftarrow> RES (isasat_input_ops.vmtf_init \<A>\<^sub>i\<^sub>n []);
    \<phi> \<leftarrow> SPEC (isasat_input_ops.phase_saving \<A>\<^sub>i\<^sub>n);
    cach \<leftarrow> SPEC (isasat_input_ops.cach_refinement_empty \<A>\<^sub>i\<^sub>n);
    let lbd = empty_lbd;
    let vdom = [];
    RETURN (M, N, D, 0, W, vm, \<phi>, zero_uint32_nat, cach, lbd, vdom)}\<close> for \<A>\<^sub>i\<^sub>n
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
  have [simp]: \<open>\<And>a \<A>\<^sub>i\<^sub>n. (a, \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>mset_rel \<longleftrightarrow> \<A>\<^sub>i\<^sub>n = nat_of_uint32 `# a\<close>
    by (auto simp: uint32_nat_rel_def br_def in_mset_rel_eq_f_iff list_rel_mset_rel_def)
  have [simp]: \<open>(a, nat_of_uint32 `# mset a) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel\<close> for a
    unfolding list_rel_mset_rel_def
    by (rule relcompI [of _ \<open>map nat_of_uint32 a\<close>])
       (auto simp: list_rel_def uint32_nat_rel_def br_def list_all2_op_eq_map_right_iff'
        list_mset_rel_def)
  have init: \<open>init_trail_D x1 (Suc (nat_of_uint32 x2))
          (2 * Suc (nat_of_uint32 x2)) \<le>
     SPEC (\<lambda>c. (c, []) \<in> P \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>distinct_mset \<A>\<^sub>i\<^sub>n\<close> and x: \<open>(\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> ?arg\<close> and
      \<open>\<A>\<^sub>i\<^sub>n' = (x1, x2)\<close>
    for \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n' x1 x2
    unfolding x P
    by (rule tr[unfolded conc_fun_RETURN])
      (use that in \<open>auto simp: lits_with_max_rel_def dest: in_N0\<close>)

  have H:
  \<open>(init_lrl (2 * Suc (nat_of_uint32 b)), isasat_input_ops.empty_watched \<A>\<^sub>i\<^sub>n)
      \<in> \<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))\<close>
   if \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> ?arg\<close> and
     \<open>x = (a, b)\<close>
    for \<A>\<^sub>i\<^sub>n x a b
    using that unfolding map_fun_rel_def
    by (auto simp: isasat_input_ops.empty_watched_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
        lits_with_max_rel_def init_lrl_def
        intro!: nth_replicate dest!: in_N0
        simp del: replicate.simps)
  have initialise_VMTF: \<open>(\<forall>L\<in>#aa. L < b) \<and> distinct_mset aa \<and> (a, aa) \<in>
          \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<and> size aa < uint32_max \<Longrightarrow>
        initialise_VMTF a b \<le> RES (isasat_input_ops.vmtf_init aa [])\<close>
    for aa b a
    using initialise_VMTF[unfolded fref_def nres_rel_def] by auto
  have [simp]: \<open>(x, y) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow> L \<in># y \<Longrightarrow>
     L < Suc (nat_of_uint32 (Max (insert 0 (set x))))\<close>
    for x y L
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def uint32_nat_rel_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def dest: in_N0)

  have initialise_VMTF: \<open>initialise_VMTF a (Suc (nat_of_uint32 b)) \<le>
       \<Down> Id (RES (isasat_input_ops.vmtf_init y []))\<close>
    if \<open>(x, y) \<in> ?arg\<close> and \<open>distinct_mset y\<close> and \<open>length a < uint_max\<close> and \<open>x = (a, b)\<close> for x y a b
    using that
    by (auto simp: P_def lits_with_max_rel_def intro!: initialise_VMTF in_N0)
  have K[simp]: \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> \<langle>uint32_nat_rel\<rangle>list_rel_mset_rel \<Longrightarrow>
         L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow> L < Suc (nat_of_uint32 (Max (insert 0 (set x))))\<close>
    for x L \<A>\<^sub>i\<^sub>n
    unfolding isasat_input_ops.atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def uint32_nat_rel_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def)
  have cach: \<open>RETURN (replicate (Suc (nat_of_uint32 b)) SEEN_UNKNOWN, [])
      \<le> \<Down> (isasat_input_ops.cach_refinement \<A>\<^sub>i\<^sub>n)
          (SPEC (isasat_input_ops.cach_refinement_empty y))\<close>
    if
      \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n\<close> and
      \<open>(x, y) \<in> ?arg\<close> and
      \<open>x = (a, b)\<close>
    for M W vm vma \<phi> x y a b
  proof -
    show ?thesis
      unfolding isasat_input_ops.cach_refinement_empty_def RETURN_RES_refine_iff
        isasat_input_ops.cach_refinement_alt_def Bex_def
      by (rule exI[of _ \<open>\<lambda>_. SEEN_UNKNOWN\<close>]) (use that in
          \<open>auto simp: map_fun_rel_def isasat_input_ops.empty_watched_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
             list_mset_rel_def lits_with_max_rel_def
            simp del: replicate_Suc
            dest!: in_N0 intro: K\<close>)
  qed
  have conflict: \<open>RETURN (True, zero_uint32_nat, replicate (Suc (nat_of_uint32 b)) NOTIN)
      \<le> SPEC (\<lambda>D. (D, None) \<in> isasat_input_ops.option_lookup_clause_rel \<A>\<^sub>i\<^sub>n)\<close>
  if
    \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n\<close> and
    \<open>((a, b), \<A>\<^sub>i\<^sub>n) \<in> lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>mset_rel\<close> and
    \<open>x = (a, b)\<close>
  for a b x y
  proof -
    have \<open>L \<in> atms_of (isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow>
        L < Suc (nat_of_uint32 b)\<close> for L
      using that in_N0 by (auto simp: isasat_input_ops.atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
          lits_with_max_rel_def)
    then show ?thesis
      by (auto simp: isasat_input_ops.option_lookup_clause_rel_def
      isasat_input_ops.lookup_clause_rel_def simp del: replicate_Suc
      intro: mset_as_position.intros)
  qed

  show ?thesis
    apply (intro frefI nres_relI)
    subgoal for x y
    unfolding init_state_wl_heur_alt_def isasat_input_ops.init_state_wl_D'_def
    apply (rewrite in \<open>let _ = Suc _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = 2 * _in _\<close> Let_def)
    apply (cases x; simp only: prod.case)
    apply (refine_rcg init[of y x] initialise_VMTF cach)
    subgoal by (auto intro!: K[of _ \<A>\<^sub>i\<^sub>n] simp: isasat_input_ops.in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
     lits_with_max_rel_def isasat_input_ops.atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by (rule conflict)
    subgoal by (rule RETURN_rule) (rule H; simp only:)
         apply assumption
    subgoal by fast
    subgoal by (auto simp: lits_with_max_rel_def P_def)
    subgoal by simp
    subgoal unfolding isasat_input_ops.phase_saving_def lits_with_max_rel_def by (auto intro!: K)
    subgoal by fast
    subgoal by fast
      apply assumption
    apply (rule refl)
    subgoal by (auto simp: P_def init_rll_def isasat_input_ops.option_lookup_clause_rel_def
          isasat_input_ops.lookup_clause_rel_def lits_with_max_rel_def op_arl_empty_def
          simp del: replicate.simps
          intro!: mset_as_position.intros K)
    done
  done
qed

lemma init_state_wl_heur_hnr:
  \<open>(init_state_wl_D'_code, isasat_input_ops.init_state_wl_heur)
    \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
      lits_with_max_assn\<^sup>d \<rightarrow>
      isasat_input_ops.isasat_init_assn \<A>\<^sub>i\<^sub>n\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
     (* and
 init_state_wl_heur_fast_hnr:
  \<open>(init_state_wl_D'_fast_code, isasat_input_ops.init_state_wl_heur_fast)
    \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
      lits_with_max_assn\<^sup>d \<rightarrow>
      isasat_input_ops.isasat_init_fast_assn \<A>\<^sub>i\<^sub>n\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?im \<rightarrow> ?ffast\<close>) *)
proof -
  have H: \<open>?c \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and>
        distinct_mset
         \<A>\<^sub>i\<^sub>n]\<^sub>a (hr_comp (arl_assn uint32_assn *a uint32_assn)
                    (lits_with_max_rel O
                     \<langle>uint32_nat_rel\<rangle>mset_rel))\<^sup>d \<rightarrow> hr_comp
         (out_learned_assn *a
          array_assn tri_bool_assn *a
          array_assn uint32_nat_assn *a
          array_assn nat_assn *a uint32_nat_assn *a arl_assn uint32_nat_assn)
         (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) *a
        arl_assn (pure (uint32_nat_rel O arena_el_rel)) *a
        conflict_option_rel_assn *a
        uint32_nat_assn *a
        hr_comp watchlist_assn (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel) *a
        isasat_input_ops.vmtf_remove_conc_option_fst_As \<A>\<^sub>i\<^sub>n *a
        hr_comp phase_saver_conc (\<langle>bool_rel\<rangle>list_rel) *a
        uint32_nat_assn *a
        hr_comp cach_refinement_l_assn (isasat_input_ops.cach_refinement \<A>\<^sub>i\<^sub>n) *a
        lbd_assn *a vdom_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using isasat_input_ops.init_state_wl_D'_hnr[unfolded PR_CONST_def, 
      FCOMP init_state_wl_D', of \<A>\<^sub>i\<^sub>n,
      unfolded PR_CONST_def]
    unfolding isasat_input_ops.cach_refinement_assn_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def by fast
  have 1: \<open>uint32_nat_assn = hr_comp uint32_assn uint32_nat_rel\<close>
    by auto
  have [simp]: \<open>Max (insert 0 (nat_of_uint32 ` aa)) = nat_of_uint32 (Max (insert 0 aa))\<close>
    if \<open>finite aa\<close> for aa
    apply (subst (4) mono_Max_commute)
    subgoal by (auto simp: mono_def nat_of_uint32_le_iff)
    subgoal using that by auto
    subgoal by auto
    by auto

  have 2: \<open>{(l, l'). l' = map nat_of_uint32 l} \<times>\<^sub>f {(c, a). a = nat_of_uint32 c} =
       {(c, a). a = (\<lambda>(a, b). (map nat_of_uint32 a, nat_of_uint32 b)) c}\<close>
    by auto
  have 3: \<open>(\<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>f uint32_nat_rel) O lits_with_max_rel =
       lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>mset_rel\<close>
    by (auto simp: lits_with_max_rel_def lits_with_max_rel_def in_mset_rel_eq_f_iff
        uint32_nat_rel_def br_def in_mset_rel_eq_f_iff_set Collect_eq_comp_right
        list_rel_def list_all2_op_eq_map_right_iff' 2)

  have \<open>hr_comp (arl_assn uint32_nat_assn *a hr_comp uint32_assn uint32_nat_rel) lits_with_max_rel =
          hr_comp (hr_comp (arl_assn uint32_assn) (\<langle>uint32_nat_rel\<rangle>list_rel) *a hr_comp uint32_assn uint32_nat_rel) lits_with_max_rel\<close>
    by (simp add: arl_assn_comp)
  also have \<open>\<dots> = hr_comp (hr_comp (arl_assn uint32_assn *a uint32_assn)
       (\<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>f uint32_nat_rel))
       lits_with_max_rel\<close>
    by simp
  also have
     \<open>\<dots> = hr_comp (arl_assn uint32_assn *a uint32_assn)
          ((\<langle>uint32_nat_rel\<rangle>list_rel \<times>\<^sub>f uint32_nat_rel) O lits_with_max_rel)\<close>
    unfolding hr_comp_assoc ..
  finally have 4: \<open>hr_comp (arl_assn uint32_nat_assn *a hr_comp uint32_assn uint32_nat_rel) lits_with_max_rel =
  hr_comp (arl_assn uint32_assn *a uint32_assn) (lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>mset_rel)\<close>
    unfolding 3 .

  have im: \<open>?im' = ?im\<close>
    apply (subst (2) 1)
    apply (subst 4)
    unfolding prod_hrp_comp hrp_comp_dest[symmetric] hrp_comp_keep[symmetric]
      prod_assn_id_assn_destroy ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep isasat_input_ops.isasat_init_assn_def
      isasat_input_ops.option_lookup_clause_assn_def[symmetric]
      isasat_input_ops.cach_refinement_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def list_assn_list_mset_rel_eq_list_mset_assn
       arena_el_assn_alt_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre ..
  (* have H: \<open>?cfast \<in> [\<lambda>x. x = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n]\<^sub>a
      hrp_comp ((arl_assn uint32_assn)\<^sup>d *\<^sub>a uint32_assn\<^sup>d) (lits_with_max_rel O \<langle>uint32_nat_rel\<rangle>mset_rel) \<rightarrow>
      hr_comp trail_pol_fast_assn (isasat_input_ops.trail_pol \<A>\<^sub>i\<^sub>n) *a
   clauses_ll_assn *a
   hr_comp conflict_option_rel_assn (isasat_input_ops.option_lookup_clause_rel \<A>\<^sub>i\<^sub>n) *a
   hr_comp (list_assn unat_lit_assn) list_mset_rel *a
   hr_comp (arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn))) (\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel) *a
   vmtf_remove_conc_option_fst_As *a
   hr_comp IsaSAT_Setup.phase_saver_conc (\<langle>bool_rel\<rangle>list_rel) *a
   uint32_nat_assn *a
   isasat_input_ops.cach_refinement_assn \<A>\<^sub>i\<^sub>n *a lbd_assn *a vdom_assn\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using init_state_wl_D'_fast_code.refine[FCOMP init_state_wl_D', of \<A>\<^sub>i\<^sub>n]
    unfolding isasat_input_ops.cach_refinement_assn_def isasat_input_ops.init_state_wl_heur_fast_def
    .
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep isasat_input_ops.isasat_init_fast_assn_def
      isasat_input_ops.option_lookup_clause_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def list_assn_list_mset_rel_eq_list_mset_assn)
  show ?fast
    unfolding isasat_input_ops.init_state_wl_heur_def
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding f im apply assumption
    using pre .. *)
qed

lemma init_state_wl_heur_init_state_wl:
  \<open>(isasat_input_ops.init_state_wl_heur, RETURN o (\<lambda>_. isasat_input_ops.init_state_wl))
  \<in> [\<lambda>N. N = \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<rightarrow> \<langle>isasat_input_ops.twl_st_heur_parsing_no_WL_wl \<A>\<^sub>i\<^sub>n\<rangle>nres_rel\<close>
  using isasat_input_ops.init_state_wl_heur_init_state_wl
  unfolding fref_def nres_rel_def
  by auto


end
