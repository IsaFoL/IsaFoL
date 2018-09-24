theory IsaSAT_VMTF
imports IsaSAT_Setup
begin

subsection \<open>Code generation for the VMTF decision heuristic and the trail\<close>
(* TODO used? *)
definition size_conflict_wl :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>

lemma size_conflict_code_refine_raw:
  \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_conflict_int) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: size_conflict_int_def)

concrete_definition (in -) size_conflict_code
   uses size_conflict_code_refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_code_def

lemmas size_conflict_code_hnr[sepref_fr_rules] = size_conflict_code.refine

lemma VMTF_Node_ref[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo VMTF_Node), uncurry2 (RETURN ooo VMTF_Node)) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a
    vmtf_node_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: vmtf_node_rel_def uint32_nat_rel_def br_def option_assn_alt_def
     split: option.splits)

lemma stamp_ref[sepref_fr_rules]:
  \<open>(return o stamp, RETURN o stamp) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare
    (auto simp: ex_assn_move_out(2)[symmetric] return_cons_rule ent_ex_up_swap vmtf_node_rel_def
      simp del: ex_assn_move_out)

lemma get_next_ref[sepref_fr_rules]:
  \<open>(return o get_next, RETURN o get_next) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)

lemma get_prev_ref[sepref_fr_rules]:
  \<open>(return o get_prev, RETURN o get_prev) \<in> vmtf_node_assn\<^sup>k \<rightarrow>\<^sub>a
   option_assn uint32_nat_assn\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: return_cons_rule vmtf_node_rel_def)

definition update_next_search where
  \<open>update_next_search L = (\<lambda>((ns, m, fst_As, lst_As, next_search), to_remove). ((ns, m, fst_As, lst_As, L), to_remove))\<close>

lemma (in isasat_input_ops) update_next_search_ref[sepref_fr_rules]:
  \<open>(uncurry (return oo update_next_search), uncurry (RETURN oo update_next_search)) \<in>
      (option_assn uint32_nat_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  unfolding option_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: update_next_search_def)

sepref_definition (in -)ns_vmtf_dequeue_code
   is \<open>uncurry (RETURN oo ns_vmtf_dequeue)\<close>
   :: \<open>[vmtf_dequeue_pre]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a (array_assn vmtf_node_assn)\<^sup>d \<rightarrow> array_assn vmtf_node_assn\<close>
  supply [[goals_limit = 1]]
  supply option.splits[split]
  unfolding ns_vmtf_dequeue_def vmtf_dequeue_pre_alt_def
  by sepref

declare ns_vmtf_dequeue_code.refine[sepref_fr_rules]

abbreviation vmtf_conc_option_fst_As where
  \<open>vmtf_conc_option_fst_As \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a option_assn uint32_nat_assn
    *a option_assn uint32_nat_assn
    *a option_assn uint32_nat_assn)\<close>

sepref_definition vmtf_dequeue_code
   is \<open>uncurry (RETURN oo vmtf_dequeue)\<close>
   :: \<open>[\<lambda>(L,(ns,m,fst_As,next_search)). L < length ns \<and> vmtf_dequeue_pre (L, ns)]\<^sub>a
        uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc_option_fst_As\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_dequeue_def
  by sepref

declare vmtf_dequeue_code.refine[sepref_fr_rules]


context isasat_input_bounded_nempty
begin

definition (in isasat_input_ops) vmtf_enqueue_pre where
  \<open>vmtf_enqueue_pre =
     (\<lambda>((M, L),(ns,m,fst_As,lst_As, next_search)). L < length ns \<and> Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       (fst_As \<noteq> None \<longrightarrow> the fst_As < length ns) \<and>
       (fst_As \<noteq> None \<longrightarrow> lst_As \<noteq> None) \<and>
       m+1 \<le> uint64_max)\<close>

sepref_thm vmtf_enqueue_code
   is \<open>uncurry2 (RETURN ooo vmtf_enqueue)\<close>
   :: \<open>[vmtf_enqueue_pre]\<^sub>a
        trail_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc_option_fst_As\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_enqueue_def vmtf_enqueue_pre_def defined_atm_def[symmetric]
   one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) vmtf_enqueue_code
   uses isasat_input_bounded_nempty.vmtf_enqueue_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_enqueue_code_def

lemmas vmtf_enqueue_code_hnr[sepref_fr_rules] =
   vmtf_enqueue_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm vmtf_enqueue_fast_code
   is \<open>uncurry2 (RETURN ooo vmtf_enqueue)\<close>
   :: \<open>[vmtf_enqueue_pre]\<^sub>a
        trail_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc_option_fst_As\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  unfolding vmtf_enqueue_def vmtf_enqueue_pre_def defined_atm_def[symmetric]
   one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) vmtf_enqueue_fast_code
   uses isasat_input_bounded_nempty.vmtf_enqueue_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_enqueue_fast_code_def

lemmas vmtf_enqueue_fast_code_hnr[sepref_fr_rules] =
   vmtf_enqueue_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

end



definition (in -) insert_sort_inner_nth :: \<open>nat_vmtf_node list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_inner_nth ns = insert_sort_inner (<) (\<lambda>remove n. stamp (ns ! (remove ! n)))\<close>

definition (in -) insert_sort_nth :: \<open>nat_vmtf_node list \<times> 'c \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_nth = (\<lambda>(ns, _). insert_sort (<) (\<lambda>remove n. stamp (ns ! (remove ! n))))\<close>


lemma (in -) insert_sort_inner_nth_code_helper:
  assumes \<open>\<forall>x\<in>set ba. x < length a\<close>  and
      \<open>b < length ba\<close> and
     mset: \<open>mset ba = mset a2'\<close>  and
      \<open>a1' < length a2'\<close>
  shows \<open>a2' ! b < length a\<close>
  using nth_mem[of b a2'] mset_eq_setD[OF mset] mset_eq_length[OF mset] assms
  by (auto simp del: nth_mem)


sepref_definition (in -) insert_sort_inner_nth_code
   is \<open>uncurry2 insert_sort_inner_nth\<close>
   :: \<open>[\<lambda>((xs, remove), n). (\<forall>x\<in>#mset remove. x < length xs) \<and> n < length remove \<and>
        length remove \<le> uint32_max]\<^sub>a
  (array_assn vmtf_node_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
  arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_inner_nth_def insert_sort_inner_def fast_minus_def[symmetric]
    short_circuit_conv zero_uint32_nat_def[symmetric] one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]  insert_sort_inner_nth_code_helper[intro]
    if_splits[split]
  by sepref

declare insert_sort_inner_nth_code.refine[sepref_fr_rules]

sepref_definition (in -) insert_sort_nth_code
   is \<open>uncurry insert_sort_nth\<close>
   :: \<open>[\<lambda>(vm, remove). (\<forall>x\<in>#mset remove. x < length (fst vm)) \<and> length remove \<le> uint32_max]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_nth_def insert_sort_def insert_sort_inner_nth_def[symmetric]
    length_u_def[symmetric] one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare insert_sort_nth_code.refine[sepref_fr_rules]


context isasat_input_bounded_nempty
begin

lemma vmtf_en_dequeue_pre_vmtf_enqueue_pre:
   \<open>vmtf_en_dequeue_pre ((M, L), a, st, fst_As, lst_As, next_search) \<Longrightarrow>
       vmtf_enqueue_pre ((M, L), vmtf_dequeue L (a, st, fst_As, lst_As, next_search))\<close>
  unfolding vmtf_enqueue_pre_def
  apply clarify
  apply (intro conjI)
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        ns_vmtf_dequeue_def Let_def vmtf_en_dequeue_pre_def split: option.splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
          vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  subgoal
    by (auto simp: vmtf_dequeue_pre_def vmtf_enqueue_pre_def vmtf_dequeue_def
        Let_def vmtf_en_dequeue_pre_def split: option.splits if_splits)[]
  done

lemma vmtf_en_dequeue_preD:
  assumes \<open>vmtf_en_dequeue_pre ((M, ah), a, aa, ab, ac, b)\<close>
  shows \<open>ah < length a\<close> and \<open>vmtf_dequeue_pre (ah, a)\<close>
  using assms by (auto simp: vmtf_en_dequeue_pre_def)

sepref_thm vmtf_en_dequeue_code
   is \<open>uncurry2 (RETURN ooo vmtf_en_dequeue)\<close>
   :: \<open>[vmtf_en_dequeue_pre]\<^sub>a
        trail_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_preD[dest] vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]
  unfolding vmtf_en_dequeue_def
  by sepref


concrete_definition (in -) vmtf_en_dequeue_code
   uses isasat_input_bounded_nempty.vmtf_en_dequeue_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_en_dequeue_code_def

lemmas vmtf_en_dequeue_hnr[sepref_fr_rules] =
   vmtf_en_dequeue_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm vmtf_en_dequeue_fast_code
   is \<open>uncurry2 (RETURN ooo vmtf_en_dequeue)\<close>
   :: \<open>[vmtf_en_dequeue_pre]\<^sub>a
        trail_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_conc\<^sup>d \<rightarrow> vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_preD[dest] vmtf_en_dequeue_pre_vmtf_enqueue_pre[dest]
  unfolding vmtf_en_dequeue_def
  by sepref

concrete_definition (in -) vmtf_en_dequeue_fast_code
   uses isasat_input_bounded_nempty.vmtf_en_dequeue_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_en_dequeue_fast_code_def

lemmas vmtf_en_dequeue_fast_hnr[sepref_fr_rules] =
   vmtf_en_dequeue_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma (in -) insert_sort_nth_reorder:
   \<open>(uncurry insert_sort_nth, uncurry reorder_remove) \<in>
      Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  using insert_sort_reorder_remove[unfolded fref_def nres_rel_def]
  by (intro frefI nres_relI) (fastforce simp: insert_sort_nth_def)

lemma (in -) insert_sort_nth_code_reorder_remove[sepref_fr_rules]:
   \<open>(uncurry insert_sort_nth_code, uncurry reorder_remove) \<in>
      [\<lambda>((a, _), b). (\<forall>x\<in>set b. x < length a) \<and> length b \<le> uint32_max]\<^sub>a
      vmtf_conc\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d \<rightarrow> arl_assn uint32_nat_assn\<close>
      supply [[show_types]]
  using insert_sort_nth_code.refine[FCOMP insert_sort_nth_reorder]
  by auto

definition (in -) atoms_hash_del where
\<open>atoms_hash_del i xs =  do {ASSERT(i < length xs); RETURN (xs[i := False])}
\<close>

lemma atoms_hash_del_op_set_delete:
  \<open>(uncurry atoms_hash_del,
    uncurry (RETURN oo op_set_delete)) \<in>
     [\<lambda>(i, xs). i \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f
     nat_rel \<times>\<^sub>r atoms_hash_rel \<rightarrow> \<langle>atoms_hash_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: atoms_hash_del_def atoms_hash_rel_def)

sepref_definition (in -) atoms_hash_del_code
  is \<open>uncurry atoms_hash_del\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a (array_assn bool_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn bool_assn\<close>
  unfolding atoms_hash_del_def
  by sepref

lemmas atoms_hash_del_hnr[sepref_fr_rules] =
   atoms_hash_del_code.refine[FCOMP atoms_hash_del_op_set_delete, unfolded atoms_hash_assn_def[symmetric]]

definition (in -) current_stamp where
  \<open>current_stamp vm  = fst (snd vm)\<close>

lemma (in -)current_stamp_alt_def:
  \<open>current_stamp = (\<lambda>(_, m, _). m)\<close>
  by (auto simp: current_stamp_def intro!: ext)

lemma (in -) current_stamp_hnr[sepref_fr_rules]:
  \<open>(return o current_stamp, RETURN o current_stamp) \<in> vmtf_conc\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: vmtf_node_rel_def current_stamp_alt_def)

lemma vmtf_rescale_alt_def:
\<open>vmtf_rescale = (\<lambda>(ns, m, fst_As, lst_As :: nat, next_search). do {
  (ns, m, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
     (\<lambda>(ns, n, lst_As). lst_As \<noteq>None)
     (\<lambda>(ns, n, a). do {
       ASSERT(a \<noteq> None);
       ASSERT(n+1 \<le> uint32_max);
       ASSERT(the a < length ns);
       let m = the a;
       let c = ns ! m;
       let nc = get_next c;
       let pc = get_prev c;
       RETURN (ns[m := VMTF_Node n pc nc], n + 1, pc)
     })
     (ns, 0, Some lst_As);
  RETURN ((ns, m, fst_As, lst_As, next_search))
  })
\<close>
  unfolding update_stamp.simps Let_def vmtf_rescale_def by auto

sepref_register vmtf_rescale
sepref_thm vmtf_rescale_code
   is \<open>(PR_CONST vmtf_rescale)\<close>
   :: \<open>vmtf_conc\<^sup>d \<rightarrow>\<^sub>a
        vmtf_conc\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] vmtf_insert_sort_nth_code_preD[dest] le_uint32_max_le_uint64_max[intro]
  unfolding vmtf_rescale_alt_def zero_uint64_nat_def[symmetric] PR_CONST_def update_stamp.simps
    one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) vmtf_rescale_code
   uses isasat_input_bounded_nempty.vmtf_rescale_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescale_code_def

lemmas vmtf_rescale_hnr[sepref_fr_rules] =
   vmtf_rescale_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]


sepref_thm vmtf_flush_code
   is \<open>uncurry (PR_CONST vmtf_flush_int)\<close>
   :: \<open>trail_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] vmtf_insert_sort_nth_code_preD[dest] le_uint32_max_le_uint64_max[intro]
  unfolding vmtf_flush_def PR_CONST_def vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>\<lambda>(i, vm, h). _ < \<hole>\<close> length_u_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_flush_code
   uses isasat_input_bounded_nempty.vmtf_flush_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_code_def

lemmas trail_dump_code_refine[sepref_fr_rules] =
   vmtf_flush_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def,
     FCOMP vmtf_change_to_remove_order', unfolded distinct_atoms_assn_def[symmetric]]


sepref_thm vmtf_flush_fast_code
   is \<open>uncurry (PR_CONST vmtf_flush_int)\<close>
   :: \<open>trail_fast_assn\<^sup>k *\<^sub>a (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<^sup>d \<rightarrow>\<^sub>a
        (vmtf_conc *a (arl_assn uint32_nat_assn *a atoms_hash_assn))\<close>
  supply [[goals_limit = 1]]
  supply vmtf_en_dequeue_pre_def[simp] vmtf_insert_sort_nth_code_preD[dest] le_uint32_max_le_uint64_max[intro]
  unfolding vmtf_flush_def PR_CONST_def vmtf_flush_int_def zero_uint32_nat_def[symmetric]
    current_stamp_def[symmetric] one_uint32_nat_def[symmetric]
  apply (rewrite at \<open>\<lambda>(i, vm, h). _ < \<hole>\<close> length_u_def[symmetric])
  apply (rewrite at \<open>length _ + \<hole>\<close> nat_of_uint64_conv_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_flush_fast_code
   uses isasat_input_bounded_nempty.vmtf_flush_fast_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_fast_code_def

lemmas trail_dump_code_fast_refine[sepref_fr_rules] =
   vmtf_flush_fast_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def,
     FCOMP vmtf_change_to_remove_order', unfolded distinct_atoms_assn_def[symmetric]]

definition (in isasat_input_ops) vmtf_mark_to_rescore_and_unset_pre where
  \<open>vmtf_mark_to_rescore_and_unset_pre = (\<lambda>(L, ((ns, m, fst_As, lst_As, next_search), tor)).
      L < length ns \<and> L \<in># \<A>\<^sub>i\<^sub>n \<and> (next_search \<noteq> None \<longrightarrow> the next_search < length ns))\<close>

definition (in -) atoms_hash_insert where
\<open>atoms_hash_insert i xs =  do {ASSERT(i < length xs); RETURN (xs[i := True])}
\<close>

lemma atoms_hash_del_op_set_insert:
  \<open>(uncurry atoms_hash_insert,
    uncurry (RETURN oo op_set_insert)) \<in>
     [\<lambda>(i, xs). i \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f
     nat_rel \<times>\<^sub>r atoms_hash_rel \<rightarrow> \<langle>atoms_hash_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: atoms_hash_insert_def atoms_hash_rel_def)

sepref_definition (in -) atoms_hash_insert_code
  is \<open>uncurry atoms_hash_insert\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a (array_assn bool_assn)\<^sup>d \<rightarrow>\<^sub>a array_assn bool_assn\<close>
  unfolding atoms_hash_insert_def
  by sepref

lemmas atoms_hash_insert_hnr[sepref_fr_rules] =
   atoms_hash_insert_code.refine[FCOMP atoms_hash_del_op_set_insert,
      unfolded atoms_hash_assn_def[symmetric]]


definition (in -) atoms_hash_set_member where
\<open>atoms_hash_set_member i xs =  do {ASSERT(i < length xs); RETURN (xs ! i)}
\<close>

lemma atoms_hash_set_member:
  \<open>(uncurry atoms_hash_set_member,
    uncurry (RETURN oo op_set_member)) \<in>
     [\<lambda>(i, xs). i \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f
     nat_rel \<times>\<^sub>r atoms_hash_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: atoms_hash_set_member_def atoms_hash_rel_def)

sepref_definition (in -) atoms_hash_set_member_code
  is \<open>uncurry atoms_hash_set_member\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a (array_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding atoms_hash_set_member_def
  by sepref

lemmas atoms_hash_set_member_hnr[sepref_fr_rules] =
   atoms_hash_set_member_code.refine[FCOMP atoms_hash_set_member,
      unfolded atoms_hash_assn_def[symmetric]]


definition (in -) distinct_atoms_insert where
\<open>distinct_atoms_insert i = (\<lambda>(D, C). do {
    if i \<in> C
    then RETURN (D, C)
    else RETURN( D @ [i], insert i C)
  })\<close>


lemma distinct_atoms_insert:
  \<open>(uncurry distinct_atoms_insert,
    uncurry (RETURN oo op_set_insert)) \<in>
     [\<lambda>(i, xs). i \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f
     nat_rel \<times>\<^sub>r distinct_atoms_rel \<rightarrow> \<langle>distinct_atoms_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: distinct_atoms_insert_def distinct_atoms_rel_def)

sepref_thm distinct_atoms_insert_code
  is \<open>uncurry distinct_atoms_insert\<close>
  :: \<open>[\<lambda>(i, _). i \<in># \<A>\<^sub>i\<^sub>n]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn *a atoms_hash_assn)\<^sup>d \<rightarrow> (arl_assn uint32_nat_assn *a atoms_hash_assn)\<close>
  unfolding distinct_atoms_insert_def
  by sepref

concrete_definition (in -) distinct_atoms_insert_code
  uses isasat_input_bounded_nempty.distinct_atoms_insert_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) distinct_atoms_insert_code_def

lemmas distinct_atoms_insert_hnr[sepref_fr_rules] =
   distinct_atoms_insert_code.refine[OF isasat_input_bounded_nempty_axioms,
     FCOMP distinct_atoms_insert,
     unfolded distinct_atoms_assn_def[symmetric]]

(* distinct_atoms_assn *)
sepref_thm vmtf_mark_to_rescore_and_unset_code
  is \<open>uncurry (RETURN oo vmtf_mark_to_rescore_and_unset)\<close>
  :: \<open>[vmtf_mark_to_rescore_and_unset_pre]\<^sub>a
      uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def
   vmtf_unset_def save_phase_def vmtf_mark_to_rescore_and_unset_pre_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_and_unset_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_and_unset_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_and_unset_code_def

lemmas vmtf_mark_to_rescore_and_unset_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_and_unset_code.refine[OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) vmtf_unset_pre where
  \<open>vmtf_unset_pre = (\<lambda>(L, vm). \<exists>M. L = atm_of(lit_of (hd M)) \<and> vm \<in> vmtf M \<and> M \<noteq> [] \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M))\<close>

sepref_thm vmtf_unset_code
  is \<open>uncurry (RETURN oo vmtf_unset)\<close>
  :: \<open>[vmtf_unset_pre]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] option.splits[split] vmtf_def[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    neq_NilE[elim!] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  unfolding vmtf_unset_def vmtf_unset_pre_def
  apply (rewrite in \<open>If (_ \<or> _)\<close> short_circuit_conv)
  by sepref

concrete_definition (in -) vmtf_unset_code
   uses isasat_input_bounded_nempty.vmtf_unset_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) vmtf_unset_code_def

lemmas vmtf_unset_code_code[sepref_fr_rules] =
   vmtf_unset_code.refine[OF isasat_input_bounded_nempty_axioms]


definition get_pos_of_level_in_trail where
  \<open>get_pos_of_level_in_trail M\<^sub>0 lev =
     SPEC(\<lambda>i. i < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0!i) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0!i)) = lev+1)\<close>

definition (in -) get_pos_of_level_in_trail_imp where
  \<open>get_pos_of_level_in_trail_imp = (\<lambda>(M', xs, lvls, reasons, k, cs) lev. do {
      ASSERT(lev < length cs);
      RETURN (cs ! lev)
   })\<close>

lemma control_stack_is_decided:
  \<open>control_stack cs M \<Longrightarrow> c\<in>set cs \<Longrightarrow> is_decided ((rev M)!c)\<close>
  by (induction arbitrary: c rule: control_stack.induct) (auto simp: nth_append
      dest: control_stack_le_length_M)


lemma control_stack_distinct:
  \<open>control_stack cs M \<Longrightarrow> distinct cs\<close>
  by (induction rule: control_stack.induct) (auto simp: nth_append
      dest: control_stack_le_length_M)

lemma control_stack_level_control_stack:
  assumes
    cs: \<open>control_stack cs M\<close> and
    n_d: \<open>no_dup M\<close> and
    i: \<open>i < length cs\<close>
  shows  \<open>get_level M (lit_of (rev M ! (cs ! i))) = Suc i\<close>
proof -
  define L where \<open>L = rev M ! (cs ! i)\<close>
  have csi: \<open>cs ! i < length M\<close>
    using cs i by (auto intro: control_stack_le_length_M)
  then have L_M: \<open>L \<in> set M\<close>
    using nth_mem[of \<open>cs !i\<close> \<open>rev M\<close>] unfolding L_def by (auto simp del: nth_mem)
  have dec_L: \<open>is_decided L\<close>
    using control_stack_is_decided[OF cs] i unfolding L_def by auto
  then have \<open>rev M!(cs ! (get_level M (lit_of L) - 1)) = L\<close>
    using control_stack_rev_get_lev[OF cs n_d L_M] by auto
  moreover have \<open>distinct M\<close>
    using no_dup_distinct[OF n_d] unfolding mset_map[symmetric] distinct_mset_mset_distinct
    by (rule distinct_mapI)

  moreover have lev0:  \<open>get_level M (lit_of L) \<ge> 1\<close>
    using split_list[OF L_M] n_d dec_L by (auto simp: get_level_append_if)
  moreover have \<open>cs ! (get_level M (lit_of (rev M ! (cs ! i))) - Suc 0) < length M\<close>
    using control_stack_le_length_M[OF cs,
         of \<open>cs ! (get_level M (lit_of (rev M ! (cs ! i))) - Suc 0)\<close>, OF nth_mem]
      control_stack_length_count_dec[OF cs] count_decided_ge_get_level[of M
          \<open>lit_of (rev M ! (cs ! i))\<close>] lev0
    by (auto simp: L_def)
  ultimately have \<open>cs ! (get_level M (lit_of L) - 1) = cs ! i\<close>
    using nth_eq_iff_index_eq[of \<open>rev M\<close>] csi unfolding L_def by auto
  then have \<open>i = get_level M (lit_of L) - 1\<close>
    using nth_eq_iff_index_eq[OF control_stack_distinct[OF cs], of i \<open>get_level M (lit_of L) - 1\<close>]
      i lev0 count_decided_ge_get_level[of M \<open>lit_of (rev M ! (cs ! i))\<close>]
    control_stack_length_count_dec[OF cs]
    by (auto simp: L_def)
  then show ?thesis using lev0 unfolding L_def[symmetric] by auto
qed

lemma get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail:
   \<open>(uncurry get_pos_of_level_in_trail_imp, uncurry get_pos_of_level_in_trail) \<in>
    [\<lambda>(M, lev). lev < count_decided M]\<^sub>f trail_pol_no_CS \<times>\<^sub>f nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  unfolding get_pos_of_level_in_trail_imp_def uncurry_def get_pos_of_level_in_trail_def
  apply clarify
  apply (rule ASSERT_leI)
  subgoal
    by (auto simp: trail_pol_no_CS_def dest!: control_stack_length_count_dec)
  subgoal for a aa ab ac ad b ba ae bb
    by (auto simp: trail_pol_no_CS_def control_stack_length_count_dec in_set_take_conv_nth
        intro!: control_stack_le_length_M control_stack_is_decided
        dest: control_stack_level_control_stack)
  done

sepref_definition (in -) get_pos_of_level_in_trail_imp_fast_code
  is \<open>uncurry get_pos_of_level_in_trail_imp\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_pos_of_level_in_trail_imp_def
  by sepref


sepref_definition (in -) get_pos_of_level_in_trail_imp_code
  is \<open>uncurry get_pos_of_level_in_trail_imp\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding get_pos_of_level_in_trail_imp_def
  by sepref

lemma get_pos_of_level_in_trail_fast_hnr[sepref_fr_rules]:
   \<open>(uncurry get_pos_of_level_in_trail_imp_fast_code, uncurry get_pos_of_level_in_trail)
     \<in> [\<lambda>(a, b). b < count_decided a]\<^sub>a (hr_comp trail_pol_fast_assn' trail_pol_no_CS)\<^sup>k *\<^sub>a
                 uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using get_pos_of_level_in_trail_imp_fast_code.refine[FCOMP
      get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail] .

lemma get_pos_of_level_in_trail_hnr[sepref_fr_rules]:
   \<open>(uncurry get_pos_of_level_in_trail_imp_code, uncurry get_pos_of_level_in_trail)
     \<in> [\<lambda>(a, b). b < count_decided a]\<^sub>a (hr_comp trail_pol_assn' trail_pol_no_CS)\<^sup>k *\<^sub>a
                 uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using get_pos_of_level_in_trail_imp_code.refine[FCOMP
      get_pos_of_level_in_trail_imp_get_pos_of_level_in_trail] .


definition (in -) length_trail_imp where
  \<open>length_trail_imp = (\<lambda>(M', xs, lvls, reasons, k, cs). do {
      ASSERT(length M' \<le> uint32_max);
      RETURN (length_u M')
   })\<close>

lemma length_trail_imp_length:
   \<open>(length_trail_imp, RETURN o op_list_length) \<in> trail_pol_no_CS \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  unfolding length_trail_imp_def uncurry_def
  apply clarify
  apply (rule ASSERT_leI)
  subgoal
    by (auto simp: trail_pol_no_CS_def ann_lits_split_reasons_def dest!: length_trail_uint_max)
  subgoal
    by (auto simp: trail_pol_no_CS_def
        ann_lits_split_reasons_def dest!: length_trail_uint_max)
  done


sepref_definition (in -) length_trail_imp_code
  is \<open>length_trail_imp\<close>
  :: \<open>trail_pol_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding length_trail_imp_def
  by sepref

lemma length_trail_imp_code[sepref_fr_rules]:
  \<open>(length_trail_imp_code, RETURN \<circ> op_list_length)
    \<in> (hr_comp trail_pol_assn'
     trail_pol_no_CS)\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using length_trail_imp_code.refine[FCOMP length_trail_imp_length] .


sepref_definition (in -) length_trail_imp_fast_code
  is \<open>length_trail_imp\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding length_trail_imp_def
  by sepref

lemma length_trail_imp_fast_code[sepref_fr_rules]:
  \<open>(length_trail_imp_fast_code, RETURN \<circ> op_list_length)
\<in> (hr_comp trail_pol_fast_assn'
     trail_pol_no_CS)\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using length_trail_imp_fast_code.refine[FCOMP length_trail_imp_length] .


lemma lit_of_last_trail_pol_lit_of_last_trail_no_CS:
   \<open>(RETURN o lit_of_last_trail_pol, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trail_pol_no_CS \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_def trail_pol_no_CS_def lit_of_last_trail_pol_def
     ann_lits_split_reasons_def hd_map rev_map[symmetric]
      intro!: frefI nres_relI)

theorem
  lit_of_last_trail_code_lit_of_last_trail_no_CS[sepref_fr_rules]:
  \<open>(lit_of_last_trail_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_no_CS_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is ?slow is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  lit_of_last_trail_fast_code_lit_of_last_trail_no_CS[sepref_fr_rules]:
  \<open>(lit_of_last_trail_fast_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_no_CS_fast_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is ?fast is \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE trail_pol_no_CS (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k)
                     trail_pol_no_CS \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_last_trail_code.refine
      lit_of_last_trail_pol_lit_of_last_trail_no_CS] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def trail_pol_no_CS_def
       ann_lits_split_reasons_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
  have H: \<open>?cfast
    \<in> [comp_PRE trail_pol_no_CS (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>k) trail_pol_no_CS \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_last_trail_fast_code.refine
      lit_of_last_trail_pol_lit_of_last_trail_no_CS] .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep ..
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_lookup_clause_rel \<rightarrow>
     \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

lemma size_conflict_hnr[sepref_fr_rules]:
  \<open>(size_conflict_code, RETURN \<circ> size_conflict) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a option_lookup_clause_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using size_conflict_code_hnr[FCOMP size_conflict_int_size_conflict]
  unfolding option_lookup_clause_assn_def[symmetric]
  by simp

definition (in isasat_input_ops) rescore_clause
  :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>rescore_clause C M vm \<phi> = SPEC (\<lambda>(vm', \<phi>' :: bool list). vm' \<in> vmtf M \<and> phase_saving \<phi>')\<close>

(* TODO ded-uplicate definitions *)
definition (in isasat_input_ops) find_decomp_w_ns_pre where
  \<open>find_decomp_w_ns_pre = (\<lambda>((M, highest), vm).
       no_dup M \<and>
       highest < count_decided M \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n_trail M \<and>
       vm \<in> vmtf M)\<close>

definition  (in isasat_input_ops) find_decomp_wl_pre
   :: \<open>nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
   \<open>find_decomp_wl_pre =  (\<lambda>(highest, T).
       find_decomp_w_ns_pre ((get_trail_wl_heur T, highest), get_vmtf_heur T))\<close>


definition find_decomp_wl_imp
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> vmtf_remove_int \<Rightarrow>
       ((nat, nat) ann_lits \<times> vmtf_remove_int) nres\<close>
where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 lev vm. do {
    let k = count_decided M\<^sub>0;
    let M\<^sub>0 = trail_conv_to_no_CS M\<^sub>0;
    let n = (length M\<^sub>0);
    pos \<leftarrow> get_pos_of_level_in_trail M\<^sub>0 lev;
    ASSERT((n - pos) \<le> uint32_max);
    let target = n - pos;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j \<le> target \<and>
           M = drop j M\<^sub>0 \<and> target \<le> length M\<^sub>0 \<and>
           vm' \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j < target)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            ASSERT(Suc j \<le> uint32_max);
            let L = atm_of (lit_of_hd_trail M) in RETURN (j + one_uint32_nat, tl M, vmtf_unset L vm)
         })
         (zero_uint32_nat, M\<^sub>0, vm);
    ASSERT(lev = count_decided M);
    let M = trail_conv_back lev M;
    RETURN (M, vm')
  })\<close>

definition find_decomp_wl_imp_pre where
  \<open>find_decomp_wl_imp_pre = (\<lambda>(((M, D), L), vm). M \<noteq> [] \<and> D \<noteq> None \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> -L \<in># the D \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> vm \<in> vmtf M)\<close>

sepref_register find_decomp_wl_imp
sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry2 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). lev < count_decided M]\<^sub>a trail_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_assn *a vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp] trail_conv_to_no_CS_def[simp]
    lit_of_last_trail_code_lit_of_last_trail[sepref_fr_rules del] lit_of_hd_trail_def[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm find_decomp_wl_imp_fast_code
  is \<open>uncurry2 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>((M, lev), vm). lev < count_decided M]\<^sub>a trail_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_fast_assn *a vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def
  supply trail_conv_to_no_CS_def[simp] lit_of_hd_trail_def[simp]
  supply [[goals_limit=1]] literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules] vmtf_unset_pre_def[simp]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_fast_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_fast_code_def

lemmas find_decomp_wl_imp_fast_code[sepref_fr_rules] =
   find_decomp_wl_imp_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) find_decomp_w_ns where
  \<open>find_decomp_w_ns =
     (\<lambda>(M::(nat, nat) ann_lits) highest _.
        SPEC(\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest \<and> vm \<in> vmtf M1))\<close>


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, D, oth)
  })\<close>


definition (in isasat_input_ops) find_decomp_wl_st_int :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>highest (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do{
     (M', vm) \<leftarrow> find_decomp_w_ns M highest vm;
     RETURN (M', N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats)
  })\<close>


definition (in isasat_input_ops) vmtf_rescore_body
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (nat \<times> vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore_body C _ vm \<phi> = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm, \<phi>). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length \<phi> \<and> atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm, \<phi>). i < length C)
           (\<lambda>(i, vm, \<phi>). do {
               ASSERT(i < length C);
               ASSERT(atm_of (C!i) \<in># \<A>\<^sub>i\<^sub>n);
               let vm' = vmtf_mark_to_rescore (atm_of (C!i)) vm;
               RETURN(i+1, vm', \<phi>)
             })
           (0, vm, \<phi>)
    }\<close>

definition (in isasat_input_ops) vmtf_rescore
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
       (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore C M vm \<phi> = do {
      (_, vm, \<phi>) \<leftarrow> vmtf_rescore_body C M vm \<phi>;
      RETURN (vm, \<phi>)
    }\<close>

sepref_thm vmtf_rescore_code
  is \<open>uncurry3 (PR_CONST vmtf_rescore)\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding vmtf_rescore_def vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def vmtf_unset_def
  vmtf_rescore_body_def PR_CONST_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_code
   uses isasat_input_bounded_nempty.vmtf_rescore_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_code_def

lemmas vmtf_rescore_code_refine[sepref_fr_rules] =
   vmtf_rescore_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm vmtf_rescore_fast_code
  is \<open>uncurry3 (PR_CONST vmtf_rescore)\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *a phase_saver_conc\<close>
  unfolding vmtf_rescore_def vmtf_mark_to_rescore_and_unset_def vmtf_mark_to_rescore_def vmtf_unset_def
  vmtf_rescore_body_def PR_CONST_def
  supply [[goals_limit = 1]] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_fast_code
   uses isasat_input_bounded_nempty.vmtf_rescore_fast_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_fast_code_def

lemmas vmtf_rescore_fast_code_refine[sepref_fr_rules] =
   vmtf_rescore_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma vmtf_rescore_score_clause:
  \<open>(uncurry3 vmtf_rescore, uncurry3 rescore_clause) \<in>
     [\<lambda>(((C, M), vm), \<phi>). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body C M vm \<phi> \<le>
        SPEC (\<lambda>(n :: nat, vm', \<phi>' :: bool list). phase_saving \<phi>' \<and> vm' \<in> vmtf M)\<close>
    if M: \<open>vm \<in> vmtf M\<close>\<open>phase_saving \<phi>\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def vmtf_mark_to_rescore_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm', \<phi>'). phase_saving \<phi>' \<and> vm' \<in> vmtf M\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using M by auto
    subgoal by auto
    subgoal using C by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal using C unfolding phase_saving_def by auto
    subgoal unfolding phase_saving_def by auto
    subgoal using C unfolding phase_saving_def by auto
    subgoal using C by (auto simp: vmtf_append_remove_iff')
    subgoal by auto
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
     apply (rule H; auto)
    subgoal
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    done
qed

lemma
  vmtf_rescore_code_rescore_clause[sepref_fr_rules]:
    \<open>(uncurry3 vmtf_rescore_code, uncurry3 (PR_CONST rescore_clause))
     \<in> [\<lambda>(((b, a), c), d). literals_are_in_\<L>\<^sub>i\<^sub>n (mset b) \<and> c \<in> vmtf a \<and>
         phase_saving d]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>
        vmtf_remove_conc *a phase_saver_conc\<close> and
  vmtf_rescore_fast_code_rescore_clause[sepref_fr_rules]:
    \<open>(uncurry3 vmtf_rescore_fast_code, uncurry3 (PR_CONST rescore_clause))
     \<in> [\<lambda>(((b, a), c), d). literals_are_in_\<L>\<^sub>i\<^sub>n (mset b) \<and> c \<in> vmtf a \<and>
         phase_saving d]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>
        vmtf_remove_conc *a phase_saver_conc\<close>
  using vmtf_rescore_code_refine[unfolded PR_CONST_def, FCOMP vmtf_rescore_score_clause]
  using vmtf_rescore_fast_code_refine[unfolded PR_CONST_def, FCOMP vmtf_rescore_score_clause]
  by auto

lemma
  assumes
    vm: \<open>vm \<in> vmtf M\<^sub>0\<close> and
    lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail M\<^sub>0\<close> and
    target: \<open>highest < count_decided M\<^sub>0\<close> and
    n_d: \<open>no_dup M\<^sub>0\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp M\<^sub>0 highest vm \<le> find_decomp_w_ns M\<^sub>0 highest vm\<close>
     (is ?decomp)
proof -
  have length_M0:  \<open>length M\<^sub>0 \<le> uint32_max div 2 + 1\<close>
    using length_trail_uint_max_div2[of M\<^sub>0] n_d literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l[OF lits]
    by (auto simp: lits_of_def)
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>(nat, nat) ann_lits\<close>
    by (rule exI[of _ \<open>M' @ (if x2g = [] then [] else [hd x2g])\<close>]) auto
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

  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have Lin_drop_tl: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (drop b M\<^sub>0)) \<Longrightarrow>
      literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (tl (drop b M\<^sub>0)))\<close> for b
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono)
     apply assumption
    by (cases \<open>drop b M\<^sub>0\<close>)  auto

  have highest: \<open>highest = count_decided M\<close> and
     ex_decomp: \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf M\<close>
    if
      pos: \<open>pos < length M\<^sub>0 \<and> is_decided (rev M\<^sub>0 ! pos) \<and> get_level M\<^sub>0 (lit_of (rev M\<^sub>0 ! pos)) =
         highest + 1\<close> and
      \<open>length M\<^sub>0 - pos \<le> uint_max\<close> and
      inv: \<open>case s of (j, M, vm') \<Rightarrow>
         j \<le> length M\<^sub>0 - pos \<and>
         M = drop j M\<^sub>0 \<and>
         length M\<^sub>0 - pos \<le> length M\<^sub>0 \<and>
         vm' \<in> vmtf M \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<close> and
      cond: \<open>\<not> (case s of
         (j, M, vm) \<Rightarrow> j < length M\<^sub>0 - pos)\<close> and
      s: \<open>s = (j, s')\<close> \<open>s' = (M, vm)\<close>
    for pos s j s' M vm
  proof -
    have
      \<open>j = length M\<^sub>0 - pos\<close> and
      M: \<open>M = drop (length M\<^sub>0 - pos) M\<^sub>0\<close> and
      vm: \<open>vm \<in> vmtf (drop (length M\<^sub>0 - pos) M\<^sub>0)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n
        (lit_of `# mset (drop (length M\<^sub>0 - pos) M\<^sub>0))\<close>
      using cond inv unfolding s
      by auto
    define M2 and L where \<open>M2 = take (length M\<^sub>0 - Suc pos) M\<^sub>0\<close> and \<open>L = rev M\<^sub>0 ! pos\<close>
    have le_Suc_pos: \<open>length M\<^sub>0 - pos = Suc (length M\<^sub>0 - Suc pos)\<close>
      using pos by auto
    have 1: \<open>take (length M\<^sub>0 - pos) M\<^sub>0 = take (length M\<^sub>0 - Suc pos) M\<^sub>0 @ [rev M\<^sub>0 ! pos]\<close>
      unfolding le_Suc_pos
      apply (subst take_Suc_conv_app_nth)
      using pos by (auto simp: rev_nth)
    have M\<^sub>0: \<open>M\<^sub>0 = M2 @ L # M\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>length M\<^sub>0 - pos\<close>])
      unfolding M L_def M2_def 1
      by auto
    have L': \<open>Decided (lit_of L) = L\<close>
      using pos unfolding L_def[symmetric] by (cases L) auto
    then have M\<^sub>0': \<open>M\<^sub>0 = M2 @ Decided (lit_of L) # M\<close>
      unfolding M\<^sub>0 by auto

    have \<open>highest = count_decided M\<close> and \<open>get_level M\<^sub>0 (lit_of L) = Suc highest\<close> and \<open>is_decided L\<close>
      using n_d pos unfolding L_def[symmetric] unfolding M\<^sub>0
      by (auto simp: get_level_append_if split: if_splits)
    then show
     \<open>\<exists>K M2.
       (Decided K # M, M2)
       \<in> set (get_all_ann_decomposition M\<^sub>0) \<and>
       get_level M\<^sub>0 K = Suc highest \<and> vm \<in> vmtf M\<close>
      using get_all_ann_decomposition_ex[of \<open>lit_of L\<close> M M2] vm unfolding M\<^sub>0'[symmetric] M[symmetric]
      by blast
    show \<open>highest = count_decided M\<close>
      using  \<open>highest = count_decided M\<close> .
  qed
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_w_ns_def trail_conv_to_no_CS_def
      get_pos_of_level_in_trail_def trail_conv_back_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal by auto
    subgoal using target by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by auto
    subgoal by auto
    subgoal using vm by auto
    subgoal using lits unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_lit_of_mset by auto
    subgoal for target s j b M vm by simp
    subgoal using length_M0 unfolding uint32_max_def by simp
    subgoal by auto
    subgoal by (auto simp: drop_Suc drop_tl)
    subgoal by auto
    subgoal for s a b aa ba vm x2 x1a x2a
      by (cases vm)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N drop_tl simp: lit_of_hd_trail_def)
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (auto intro: Lin_drop_tl)
    subgoal by auto
    subgoal by (rule highest)
    subgoal by (rule ex_decomp) (assumption+, auto)
    done
qed


lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry2 find_decomp_wl_imp, uncurry2 find_decomp_w_ns) \<in>
    [find_decomp_w_ns_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_decomp_w_ns_pre_def simp del: twl_st_of_wl.simps
       intro!: find_decomp_wl_imp_le_find_decomp_wl')

sepref_register find_decomp_w_ns

lemma find_decomp_wl_imp_code_conbine_cond:
  \<open>(\<lambda>((b, a), c). find_decomp_w_ns_pre ((b, a), c) \<and> a < count_decided b) = (\<lambda>((b, a), c).
         find_decomp_w_ns_pre ((b, a), c))\<close>
  by (auto intro!: ext simp: find_decomp_w_ns_pre_def)

lemma find_decomp_wl_imp_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry2 find_decomp_wl_imp_code, uncurry2 (PR_CONST find_decomp_w_ns))
     \<in> [\<lambda>((b, a), c). find_decomp_w_ns_pre ((b, a), c)]\<^sub>a
     trail_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_assn *a vmtf_remove_conc\<close>
  using find_decomp_wl_imp_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def find_decomp_wl_imp_code_conbine_cond
  .

lemma find_decomp_wl_imp_fast_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry2 find_decomp_wl_imp_fast_code, uncurry2 (PR_CONST find_decomp_w_ns))
     \<in> [\<lambda>((b, a), c). find_decomp_w_ns_pre ((b, a), c)]\<^sub>a
     trail_fast_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_fast_assn *a vmtf_remove_conc\<close>
  using find_decomp_wl_imp_fast_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def find_decomp_wl_imp_code_conbine_cond
  .

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(highest, (M', N, D, W, Q, vm, \<phi>)).
         find_decomp_w_ns_pre ((M', highest), vm)]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d  \<rightarrow> isasat_unbounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def

lemmas find_decomp_wl_imp'_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


sepref_thm find_decomp_wl_imp'_fast_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(highest, (M', N, D, W, Q, vm, \<phi>)).
         find_decomp_w_ns_pre ((M', highest), vm)]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d  \<rightarrow>
        isasat_bounded_assn\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_fast_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp'_fast_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_fast_code_def

lemmas find_decomp_wl_imp'_fast_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

abbreviation (in isasat_input_ops) find_decomp_wl_nlit_prop where
  \<open>find_decomp_wl_nlit_prop \<equiv>
    (\<lambda>highest (M, N, D, Q', W', _, \<phi>, clvls, cach, _, outl, stats) S.
    (\<exists>K M2 M1 vm lbd. S = (M1, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats) \<and> vm \<in> vmtf M1 \<and>
        (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = Suc highest))\<close>

definition (in isasat_input_ops) find_decomp_wl_nlit
:: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_nlit highest S =
    SPEC(find_decomp_wl_nlit_prop highest S)\<close>

lemma find_decomp_wl_st_int_find_decomp_wl_nlit:
  \<open>(uncurry find_decomp_wl_st_int, uncurry find_decomp_wl_nlit) \<in>
      [\<lambda>(highest, S). True]\<^sub>f
      Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have [simp]: \<open>(Decided K # aq, M2) \<in> set (get_all_ann_decomposition ba) \<Longrightarrow> no_dup ba \<Longrightarrow>
       no_dup aq\<close> for ba K aq M2
    by (auto dest!: get_all_ann_decomposition_exists_prepend dest: no_dup_appendD)
  show ?thesis
  unfolding find_decomp_wl_nlit_def
    find_decomp_wl_st_int_def find_decomp_w_ns_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S')
      (auto 5 5 intro!: SPEC_rule
        simp: find_decomp_wl_st_def find_decomp_wl'_def find_decomp_wl_def lbd_empty_def
        RES_RETURN_RES2 conc_fun_SPEC find_decomp_w_ns_def)
  done
qed

sepref_register find_decomp_wl_nlit
lemma
  fixes M :: \<open>(nat, nat) ann_lits\<close>
  shows
    find_decomp_wl_imp'_code_find_decomp_wl[sepref_fr_rules]:
      \<open>(uncurry find_decomp_wl_imp'_code, uncurry (PR_CONST find_decomp_wl_nlit)) \<in>
        [find_decomp_wl_pre]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
      (is ?slow is  \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
    find_decomp_wl_imp'_fast_code_find_decomp_wl[sepref_fr_rules]:
      \<open>(uncurry find_decomp_wl_imp'_fast_code, uncurry (PR_CONST find_decomp_wl_nlit)) \<in>
        [find_decomp_wl_pre]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
      (is ?fast is  \<open>?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  define L where L: \<open>L \<equiv> -lit_of (hd M)\<close>
  have H: \<open>?c
       \<in> [comp_PRE (nat_rel \<times>\<^sub>f Id) (\<lambda>(highest, S). True)
     (\<lambda>_ (highest, M', N, D, W, Q, vm, \<phi>).
         find_decomp_w_ns_pre ((M', highest), vm))
     (\<lambda>_. True)]\<^sub>a hrp_comp (uint32_nat_assn\<^sup>k *\<^sub>a isasat_unbounded_assn\<^sup>d)
                    (nat_rel \<times>\<^sub>f Id) \<rightarrow> hr_comp isasat_unbounded_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_decomp_wl_imp'_code_hnr[unfolded PR_CONST_def]
         find_decomp_wl_st_int_find_decomp_wl_nlit]
    unfolding PR_CONST_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def find_decomp_wl_pre_def find_decomp_w_ns_pre_def highest_lit_def
    by (fastforce simp del: twl_st_of_wl.simps)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
       hr_comp_prod_conv hr_comp_Id2 ..
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..

  have H: \<open>?cfast
       \<in> [comp_PRE (nat_rel \<times>\<^sub>f Id) (\<lambda>(highest, S). True)
     (\<lambda>_ (highest, M', N, D, W, Q, vm, \<phi>).
         find_decomp_w_ns_pre ((M', highest), vm))
     (\<lambda>_. True)]\<^sub>a hrp_comp (uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d)
                    (nat_rel \<times>\<^sub>f Id) \<rightarrow> hr_comp isasat_bounded_assn Id\<close>
    (is \<open>_ \<in> [_]\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_decomp_wl_imp'_fast_code_hnr[unfolded PR_CONST_def]
         find_decomp_wl_st_int_find_decomp_wl_nlit]
    unfolding PR_CONST_def
    .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by simp
  have f: \<open>?f' = ?ffast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
       hr_comp_prod_conv hr_comp_Id2 ..
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register rescore_clause vmtf_flush

(* TODO use in vmtf_mark_to_rescore_and_unset *)
sepref_register vmtf_mark_to_rescore
sepref_thm vmtf_mark_to_rescore_code
  is \<open>uncurry (RETURN oo vmtf_mark_to_rescore)\<close>
  :: \<open>[\<lambda>(a, vm). a \<in># \<A>\<^sub>i\<^sub>n]\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_def
   vmtf_unset_def save_phase_def
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_code_def

lemmas vmtf_mark_to_rescore_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_code.refine[OF isasat_input_bounded_nempty_axioms]


definition (in isasat_input_ops) vmtf_mark_to_rescore_clause where
\<open>vmtf_mark_to_rescore_clause arena C vm = do {
    ASSERT(arena_is_valid_clause_idx arena C);
    nfoldli
      ([C..<C + nat_of_uint64_conv (arena_length arena C)])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(arena_lit_pre arena i);
        ASSERT(atm_of (arena_lit arena i) \<in># \<A>\<^sub>i\<^sub>n);
        RETURN (vmtf_mark_to_rescore (atm_of (arena_lit arena i)) vm)
      })
      vm
  }\<close>

(* TODO Move *)
text \<open>This lemmma is only useful if \<^term>\<open>set xs\<close> can be simplified (which also means that this
  simp-rule should not be used...)\<close>
lemma (in -) in_list_in_setD: \<open>xs = it @ x # \<sigma> \<Longrightarrow> x \<in> set xs\<close>
  by auto

lemma vmtf_mark_to_rescore_clause_spec:
  \<open>vm \<in> vmtf M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow> C \<in># dom_m N \<Longrightarrow>
   (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<Longrightarrow>
    vmtf_mark_to_rescore_clause arena C vm \<le> RES (vmtf M)\<close>
  unfolding vmtf_mark_to_rescore_clause_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> vmtf M\<close>])
  subgoal
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_def
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting)
    done
  subgoal for x it \<sigma>
    unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
    apply (rule exI[of _ C])
    apply (intro conjI)
    apply (solves \<open>auto dest: in_list_in_setD\<close>)
    apply (rule exI[of _ N])
    apply (rule exI[of _ vdom])
    apply (fastforce simp: arena_lifting dest: in_list_in_setD)
    done
  subgoal for x it \<sigma>
    by (fastforce simp add: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
  subgoal for x it _ \<sigma>
    by (cases \<sigma>)
      (auto intro!: vmtf_mark_to_rescore simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       dest: in_list_in_setD)
  done

definition (in isasat_input_ops) vmtf_mark_to_rescore_also_reasons
  :: \<open>(nat, nat) ann_lits \<Rightarrow> arena \<Rightarrow> nat literal list \<Rightarrow> _ \<Rightarrow>_\<close> where
\<open>vmtf_mark_to_rescore_also_reasons M arena outl vm = do {
    nfoldli
      ([0..<length outl])
      (\<lambda>_. True)
      (\<lambda>i vm. do {
        ASSERT(i < length outl);
        ASSERT(-outl ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
        C \<leftarrow> get_the_propagation_reason M (-(outl ! i));
        case C of
          None \<Rightarrow> RETURN (vmtf_mark_to_rescore (atm_of (outl ! i)) vm)
        | Some C \<Rightarrow> if C = 0 then RETURN vm else vmtf_mark_to_rescore_clause arena C vm
      })
      vm
  }\<close>

sepref_register vmtf_mark_to_rescore_clause
sepref_thm vmtf_mark_to_rescore_clause_code
  is \<open>uncurry2 (PR_CONST vmtf_mark_to_rescore_clause)\<close>
  :: \<open>arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_clause_def PR_CONST_def
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_clause_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_clause_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_clause_code_def

lemmas vmtf_mark_to_rescore_clause_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_clause_code.refine[OF isasat_input_bounded_nempty_axioms]

sepref_register vmtf_mark_to_rescore_also_reasons get_the_propagation_reason
sepref_thm vmtf_mark_to_rescore_also_reasons_code
  is \<open>uncurry3 (PR_CONST vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>trail_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_also_reasons_def PR_CONST_def
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_also_reasons_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_also_reasons_code.refine_raw
  is \<open>(uncurry3 ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_also_reasons_code_def

sepref_register vmtf_mark_to_rescore_also_reasons get_the_propagation_reason
sepref_thm vmtf_mark_to_rescore_also_reasons_fast_code
  is \<open>uncurry3 (PR_CONST vmtf_mark_to_rescore_also_reasons)\<close>
  :: \<open>[\<lambda>(((_, N), _), _). length N \<le> uint64_max]\<^sub>a 
      trail_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a (arl_assn unat_lit_assn)\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
      vmtf_remove_conc\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n[simp]
  supply [[goals_limit=1]]
  unfolding vmtf_mark_to_rescore_also_reasons_def PR_CONST_def 
  apply (rewrite at \<open>If (_ = \<hole>)\<close> zero_uint64_nat_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_mark_to_rescore_also_reasons_fast_code
  uses isasat_input_bounded_nempty.vmtf_mark_to_rescore_also_reasons_fast_code.refine_raw
  is \<open>(uncurry3 ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_mark_to_rescore_also_reasons_fast_code_def

lemmas vmtf_mark_to_rescore_also_reasons_fast_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_also_reasons_fast_code.refine[OF isasat_input_bounded_nempty_axioms]


lemma vmtf_mark_to_rescore':
 \<open>L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> vm \<in> vmtf M \<Longrightarrow> vmtf_mark_to_rescore L vm \<in> vmtf M\<close>
  by (cases vm) (auto intro: vmtf_mark_to_rescore)

lemmas vmtf_mark_to_rescore_also_reasons_hnr[sepref_fr_rules] =
   vmtf_mark_to_rescore_also_reasons_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma vmtf_mark_to_rescore_also_reasons_spec:
  \<open>vm \<in> vmtf M \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
   (\<forall>L \<in> set outl. L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<Longrightarrow>
   (\<forall>L \<in> set outl. \<forall>C. (Propagated (-L) C \<in> set M \<longrightarrow> C \<noteq> 0 \<longrightarrow> (C \<in># dom_m N \<and>
       (\<forall>C \<in> set [C..<C + arena_length arena C]. arena_lit arena C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)))) \<Longrightarrow>
    vmtf_mark_to_rescore_also_reasons M arena outl vm \<le> RES (vmtf M)\<close>
  unfolding vmtf_mark_to_rescore_also_reasons_def
  apply (subst RES_SPEC_conv)
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ vm. vm \<in> vmtf M\<close>])
  subgoal by (auto dest: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding all_set_conv_nth
    by (auto simp: uminus_\<A>\<^sub>i\<^sub>n_iff dest!: in_list_in_setD)
  subgoal for x l1 l2 \<sigma>
    unfolding get_the_propagation_reason_def
    apply (rule SPEC_rule)
    apply (rename_tac reason, case_tac reason; simp only: option.simps RES_SPEC_conv[symmetric])
    subgoal
      by (auto simp: vmtf_mark_to_rescore'
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric])
    apply (rename_tac D, case_tac \<open>D = 0\<close>; simp)
    subgoal
      by (rule vmtf_mark_to_rescore_clause_spec, assumption, assumption)
       fastforce+
    done
  done

end

end
