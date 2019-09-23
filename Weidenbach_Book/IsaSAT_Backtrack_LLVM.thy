theory IsaSAT_Backtrack_LLVM
  imports IsaSAT_Backtrack IsaSAT_VMTF_LLVM IsaSAT_Lookup_Conflict_LLVM
begin

lemma isa_empty_conflict_and_extract_clause_heur_alt_def:
    \<open>isa_empty_conflict_and_extract_clause_heur M D outl = do {
     let C = replicate (length outl) (outl!0);
     (D, C, _) \<leftarrow> WHILE\<^sub>T
         (\<lambda>(D, C, i). i < length_uint32_nat outl)
         (\<lambda>(D, C, i). do {
           ASSERT(i < length outl);
           ASSERT(i < length C);
           ASSERT(lookup_conflict_remove1_pre (outl ! i, D));
           let D = lookup_conflict_remove1 (outl ! i) D;
           let C = C[i := outl ! i];
	   ASSERT(get_level_pol_pre (M, C!i));
	   ASSERT(get_level_pol_pre (M, C!1));
	   ASSERT(1 < length C);
           let L1 = C!i;
           let L2 = C!1;
           let C = (if get_level_pol M L1 > get_level_pol M L2 then swap C 1 i else C);
           ASSERT(i+1 \<le> uint32_max);
           RETURN (D, C, i+1)
         })
        (D, C, 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow> length C > 1);
     ASSERT(length outl \<noteq> 1 \<longrightarrow>  get_level_pol_pre (M, C!1));
     RETURN ((True, D), C, if length outl = 1 then 0 else get_level_pol M (C!1))
  }\<close>
  unfolding isa_empty_conflict_and_extract_clause_heur_def (*WB_More_Refinement_List.swap_def
    swap_def[symmetric]*)
  by auto

sepref_def empty_conflict_and_extract_clause_heur_fast_code
  is \<open>uncurry2 (isa_empty_conflict_and_extract_clause_heur)\<close>
  :: \<open>[\<lambda>((M, D), outl). outl \<noteq> [] \<and> length outl \<le> uint32_max]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a lookup_clause_rel_assn\<^sup>d *\<^sub>a out_learned_assn\<^sup>k \<rightarrow>
       (conflict_option_rel_assn) *a clause_ll_assn *a uint32_nat_assn\<close>
  supply [[goals_limit=1]] image_image[simp]
  supply [simp] = max_snat_def uint32_max_def
  unfolding isa_empty_conflict_and_extract_clause_heur_alt_def
    larray_fold_custom_replicate length_uint32_nat_def conflict_option_rel_assn_def
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !1\<close> snat_const_fold[where 'a=64])+
  apply (rewrite at \<open>\<hole>\<close> in \<open>_ !0\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>swap _ \<hole> _\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, _ + 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>(_, _, 1)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>\<hole>\<close> in \<open>If (length _ = \<hole>)\<close> snat_const_fold[where 'a=64])
  apply (annot_unat_const "TYPE(32)")
  unfolding gen_swap convert_swap
  by sepref


lemma emptied_list_alt_def: \<open>emptied_list xs = take 0 xs\<close>
  by (auto simp: emptied_list_def)
  
sepref_def empty_cach_code
  is \<open>empty_cach_ref_set\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_cach_ref_set_def comp_def cach_refinement_l_assn_def emptied_list_alt_def
  apply (annot_snat_const "TYPE(64)")
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> value_of_atm_def[symmetric])
  apply (rewrite at \<open>_[\<hole> := SEEN_UNKNOWN]\<close> index_of_atm_def[symmetric])
  by sepref



theorem empty_cach_code_empty_cach_ref[sepref_fr_rules]:
  \<open>(empty_cach_code, RETURN \<circ> empty_cach_ref)
    \<in> [empty_cach_ref_pre]\<^sub>a
    cach_refinement_l_assn\<^sup>d \<rightarrow> cach_refinement_l_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in>[comp_PRE Id
     (\<lambda>(cach, supp).
         (\<forall>L\<in>set supp. L < length cach) \<and>
         length supp \<le> Suc (uint32_max div 2) \<and>
         (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set supp))
     (\<lambda>x y. True)
     (\<lambda>x. nofail ((RETURN \<circ> empty_cach_ref) x))]\<^sub>a
      hrp_comp (cach_refinement_l_assn\<^sup>d)
                     Id \<rightarrow> hr_comp cach_refinement_l_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE[OF empty_cach_code.refine[unfolded PR_CONST_def convert_fref]
        empty_cach_ref_set_empty_cach_ref[unfolded convert_fref]] by simp
  have pre: \<open>?pre' h x\<close> if \<open>?pre x\<close> for x h
    using that by (auto simp: comp_PRE_def trail_pol_def
        ann_lits_split_reasons_def empty_cach_ref_pre_def)
  have im: \<open>?im' = ?im\<close>
    by simp
  have f: \<open>?f' = ?f\<close>
    by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register fm_add_new_fast

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> Suc (length (get_clauses_wl_heur S)) < max_snat 64\<close>
  by (cases S) (auto simp: isasat_fast_def max_snat_def sint64_max_def)

  
find_in_thms isa_vmtf_flush_int in sepref_fr_rules

thm append_ll_def
  
thm mop_list_list_push_back_def

thm isasat_fast_length_leD


definition "rescore' \<equiv> \<lambda>C (M, N, D, Q, W, vm, \<phi>, rest). doN {
    (vm, \<phi>) \<leftarrow> isa_vmtf_rescore C M vm \<phi>;
    RETURN (M, N, D, Q, W, vm, \<phi>, rest)
}"

definition "get_LBD' \<equiv> \<lambda>(M, N, D, Q, W, vm, \<phi>, y, cach, lbd, rest). get_LBD lbd"

definition "fm_add_new_fast' \<equiv> \<lambda>b C (M, N, rest). doN {
  ASSERT (append_and_length_fast_code_pre ((b, C), N));
  (N, i) \<leftarrow> fm_add_new_fast b C N;
  RETURN (i,(M, N, rest))
}"

definition "update_lbd' \<equiv> \<lambda>i glue (M, N, rest). doN {
  ASSERT(update_lbd_pre ((i, glue), N));
  RETURN (M,update_lbd i glue N,rest)
}"

definition "pushWL \<equiv> \<lambda>L C i (M, N, D, Q, W, rest). doN {
  ASSERT(length C > 1);
  let L' = C!1;
  let b' = (length C = 2);
  
  ASSERT(length_ll W (nat_of_lit (-L)) < sint64_max);
  W \<leftarrow> mop_list_list_push_back W (nat_of_lit (- L)) (i, L', b');    
     
  ASSERT(length_ll W (nat_of_lit L') < sint64_max);
  W \<leftarrow> mop_list_list_push_back W (nat_of_lit L') (i, -L, b');    

  RETURN (M, N, D, Q, W, rest)
}"

definition "empty_lbd' \<equiv> \<lambda>(M, N, D, Q, W, vm, \<phi>, y, cach, lbd, rest). doN {
  lbd \<leftarrow> lbd_empty lbd;
  RETURN (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, rest)
}"

definition "set_len_trail' \<equiv> \<lambda>(M, N, D, Q, rest). doN {
  ASSERT(isa_length_trail_pre M);
  let Q = isa_length_trail M;
  RETURN (M, N, D, Q, rest)
}"

definition "cons_trail_Propagated' \<equiv> \<lambda>L i (M,rest). doN {
  ASSERT(cons_trail_Propagated_tr_pre ((-L, i), M));
  M \<leftarrow> cons_trail_Propagated_tr (- L) i M;
  RETURN (M,rest)
}"

definition "isa_vmtf_flush_int' \<equiv> \<lambda>(M, N, D, Q, W, vm, rest). doN {
  vm \<leftarrow> isa_vmtf_flush_int M vm;
  RETURN (M, N, D, Q, W, vm, rest)
}"

definition "save_phase' \<equiv> \<lambda>L (M, N, D, Q, W, vm, \<phi>, rest). doN {
  ASSERT(atm_of L < length \<phi>);
  let \<phi> = save_phase (-L) \<phi>;
  RETURN (M, N, D, Q, W, vm, \<phi>, rest)
}"


definition "upd_stats' \<equiv> \<lambda>glue (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, rest). doN {
  let stats = add_lbd (of_nat glue) stats;
  RETURN (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, rest)
}"

definition "upd_ema' \<equiv> \<lambda>glue (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, (fema, sema, ccount), rest). doN {
  let fema = ema_update glue fema;
  let sema = ema_update glue sema;
  RETURN (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, (fema, sema, ccount), rest)
}"

definition "upd_res_info' \<equiv> \<lambda>(M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, (fema, sema,
      res_info),rest). doN {
        let res_info = incr_conflict_count_since_last_restart res_info;
        RETURN (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, (fema, sema,
      res_info),rest)
      }"

definition "upd_dom' \<equiv> \<lambda>i (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, heur, vdom, avdom, rest). doN {
        ASSERT (length vdom + 1 < max_snat 64);
        vdom \<leftarrow> mop_list_append vdom i;
        ASSERT (length avdom + 1 < max_snat 64);
        avdom \<leftarrow> mop_list_append avdom i;
        RETURN (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, heur, vdom, avdom, rest)
      }"      

definition "incr_lcount' \<equiv> \<lambda>(M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, heur, vdom, avdom, lcount, opts). doN {
    ASSERT (lcount + 1 < max_snat 64);
    let lcount = lcount + 1;
    RETURN (M, N, D, Q, W, vm, \<phi>, 0, cach, lbd, outl, stats,heur, vdom, avdom, lcount, opts)
  }"      
            
definition "upd_etc' \<equiv> \<lambda>i glue (M, N, D, Q, W, vm, \<phi>, y, cach, lbd, outl, stats, (fema, sema,
         res_info), vdom, avdom, lcount, opts). doN {
      let stats = add_lbd (of_nat glue) stats;
      let fema = ema_update glue fema;
      let sema = ema_update glue sema;
      let res_info = incr_conflict_count_since_last_restart res_info;
      ASSERT (length vdom + 1 < max_snat 64);
      ASSERT (length avdom + 1 < max_snat 64);
      vdom \<leftarrow> mop_list_append vdom i;
      avdom \<leftarrow> mop_list_append avdom i;
      ASSERT (lcount + 1 < max_snat 64);
      let lcount = lcount + 1;
      RETURN (M, N, D, Q, W, vm, \<phi>, 0,
         cach, lbd, outl, stats, (fema, sema,
          res_info), vdom,
          avdom,
          lcount, opts)
    }
"

lemma upd_etc'_alt: "upd_etc' = (\<lambda>i glue S. doN {
      S \<leftarrow> upd_stats' glue S;
      S \<leftarrow> upd_ema' glue S;
      S \<leftarrow> upd_res_info' S;
      S \<leftarrow> upd_dom' i S;
      S \<leftarrow> incr_lcount' S;
      RETURN S
    })"
  unfolding upd_etc'_def
  unfolding upd_stats'_def upd_ema'_def upd_res_info'_def upd_dom'_def incr_lcount'_def
  apply (auto split!: prod.split simp: fun_eq_iff)
  done
  

lemma cnv_aux1: "doN { x \<leftarrow> m; s \<leftarrow> (case x of (a,b) \<Rightarrow> f a b); mm s } = doN { (a,b) \<leftarrow> m; s\<leftarrow>f a b; mm s }" 
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma propagate_bt_wl_D_heur_alt_def':
  \<open>uncurry2 (\<lambda>L C S. doN {
      S \<leftarrow> rescore' C S;
      glue \<leftarrow> get_LBD' S;
      let b = False;
      (i,S) \<leftarrow> fm_add_new_fast' b C S;
      
      S \<leftarrow> update_lbd' i glue S;
      S \<leftarrow> pushWL L C i S;
           
      S \<leftarrow> empty_lbd' S;
         
      S \<leftarrow> set_len_trail' S;
      
      S \<leftarrow> cons_trail_Propagated' L i S;

      S \<leftarrow> isa_vmtf_flush_int' S;

      S \<leftarrow> save_phase' L S;
                  
      S \<leftarrow> upd_etc' i glue S;

      RETURN S      
    }) lcs
  \<le> uncurry2 propagate_bt_wl_D_heur lcs 
    \<close> if "case lcs of ((l,c),s) \<Rightarrow> isasat_fast s"
  proof -
    obtain l c s where LCS: "lcs=((l,c),s)" by (cases lcs) fast
    obtain
      M N0 D Q W0 vm0 \<phi>0 y cach lbd outl stats fema sema res_info vdom avdom
      lcount opts
      where S: "s=(M, N0, D, Q, W0, vm0, \<phi>0, y, cach, lbd, outl, stats, (fema, sema, res_info), vdom, avdom,
      lcount, opts)"
    by (cases s)  auto
    
    thm mop_list_list_push_back_def
    have U1: "doN {xs \<leftarrow> mop_list_list_push_back xs i x; m xs} = doN {
      ASSERT (pre_list_list_push_back ((xs, i), x)); let xs = op_list_list_push_back xs i x; m xs}" 
      for xs i x m by auto
    
      
    show ?thesis using that
      unfolding S LCS propagate_bt_wl_D_heur_def uncurry_def 
        rescore'_def get_LBD'_def fm_add_new_fast'_def update_lbd'_def
        pushWL_def empty_lbd'_def set_len_trail'_def
        cons_trail_Propagated'_def isa_vmtf_flush_int'_def
        save_phase'_def upd_etc'_def
      apply (simp only: split)
      apply (simp only: U1 Let_def nres_monad_laws cnv_aux1 split)
      apply (rule refine_IdD)
      apply refine_rcg
      apply refine_dref_type
      apply (simp_all add: append_and_length_fast_code_pre_def max_snat_def sint64_max_def)
      done
      
  qed



sepref_register rescore'
sepref_def rescore'_impl is "uncurry rescore'" :: "clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding rescore'_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register fm_add_new_fast'
sepref_def fm_add_new_fast'_impl is "uncurry2 fm_add_new_fast'" ::  
  "bool1_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a sint64_nat_assn *a isasat_bounded_assn"
  unfolding fm_add_new_fast'_def isasat_bounded_assn_def fold_tuple_optimizations   
  supply [[goals_limit = 1]]
  by sepref  
  
sepref_register get_LBD'
sepref_def get_LBD'_impl is "get_LBD'" :: "isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn" 
  unfolding get_LBD'_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref
  
sepref_register update_lbd'    
sepref_def update_lbd'_impl is "uncurry2 update_lbd'" 
  :: "sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"  
  unfolding update_lbd'_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref
  
sepref_register pushWL  
sepref_def pushWL_impl is "uncurry3 pushWL" 
  :: "unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"  
  unfolding pushWL_def 
  unfolding length_ll_def isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  apply (annot_snat_const "TYPE(64)")
  by sepref  
  
  
sepref_register empty_lbd'
sepref_def empty_lbd'_impl is "empty_lbd'" :: "isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding empty_lbd'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register set_len_trail' cons_trail_Propagated_tr
sepref_def set_len_trail'_impl is "set_len_trail'" :: "isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding set_len_trail'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref


sepref_register cons_trail_Propagated'
sepref_def cons_trail_Propagated'_impl is "uncurry2 cons_trail_Propagated'"
  :: "unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  supply [[goals_limit=1]] 
  unfolding cons_trail_Propagated'_def
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register isa_vmtf_flush_int'
sepref_def isa_vmtf_flush_int'_impl is "isa_vmtf_flush_int'" :: "isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding isa_vmtf_flush_int'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register save_phase'
sepref_def save_phase'_def is "uncurry save_phase'" :: "unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding save_phase'_def save_phase_def
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

  

sepref_register upd_stats' upd_ema' upd_res_info' upd_dom' incr_lcount'
    
sepref_def upd_stats'_impl is "uncurry upd_stats'" :: "uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding upd_stats'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  apply (rewrite in \<open>add_lbd (of_nat \<hole>) _\<close> annot_unat_unat_upcast[where 'l=64])
  by sepref
(*

sepref_def upd_ema'_impl is "uncurry upd_ema'" :: "uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding upd_ema'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
apply sepref_dbg_keep
apply sepref_dbg_trans_keep
apply sepref_dbg_trans_step_keep
apply sepref_dbg_side_unfold
oops

  
sepref_def upd_res_info'_impl is "upd_res_info'" :: "isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding upd_res_info'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def upd_dom'_impl is "uncurry upd_dom'" :: "sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding upd_dom'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def incr_lcount'_impl is "incr_lcount'" :: "isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"
  unfolding incr_lcount'_def 
  unfolding isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  apply (rewrite at "0" fold_unat[where 'a=32])
  apply (annot_unat_const "TYPE(64)")
  by sepref  
      
    
sepref_register upd_etc'    
sepref_def upd_etc'_impl is "uncurry2 upd_etc'" 
  :: "sint64_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn"  
  unfolding upd_etc'_alt
  by sepref
  
        
sepref_def propagate_bt_wl_D_fast_code
  is \<open>uncurry2 propagate_bt_wl_D_heur\<close>
  :: \<open>[\<lambda>((L, C), S). isasat_fast S]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  apply (rule hfref_refine_with_pre[OF propagate_bt_wl_D_heur_alt_def'])
  subgoal by auto    
  supply [[goals_limit = 1]]
  by sepref  
  *)
term heuristic_assn
sepref_def propagate_bt_wl_D_fast_codeXX
  is \<open>uncurry2 propagate_bt_wl_D_heur\<close>
  :: \<open>[\<lambda>((L, C), S). isasat_fast S]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>

  supply [[goals_limit = 1]] append_ll_def[simp] isasat_fast_length_leD[dest]
    propagate_bt_wl_D_fast_code_isasat_fastI2[intro] length_ll_def[simp]
    propagate_bt_wl_D_fast_code_isasat_fastI3[intro]
  unfolding propagate_bt_wl_D_heur_alt_def
    isasat_bounded_assn_def heuristic_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    PR_CONST_def save_phase_def
  apply (rewrite in \<open>add_lbd (of_nat \<hole>) _\<close> annot_unat_unat_upcast[where 'l=64])
  apply (rewrite in \<open>(_ + \<hole>, _)\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_ [_ := _], \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const "TYPE(64)")
  unfolding fold_tuple_optimizations
  apply (rewrite in \<open>isasat_fast \<hole>\<close> fold_tuple_optimizations[symmetric])+
  apply sepref
  done
  
sepref_def propagate_unit_bt_wl_D_fast_code
  is \<open>uncurry propagate_unit_bt_wl_D_int\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit = 1]] vmtf_flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propagate_unit_bt_wl_D_int_def isasat_bounded_assn_def
    PR_CONST_def heuristic_assn_def
  unfolding fold_tuple_optimizations
  apply (annot_snat_const "TYPE(64)")
  by sepref


lemma extract_shorter_conflict_list_heur_st_alt_def:
    \<open>extract_shorter_conflict_list_heur_st = (\<lambda>(M, N, (bD), Q', W', vm, \<phi>, clvls, cach, lbd, outl,
       stats, ccont, vdom). do {
     let D =  the_lookup_conflict bD;
     ASSERT(fst M \<noteq> []);
     let K = lit_of_last_trail_pol M;
     ASSERT(0 < length outl);
     ASSERT(lookup_conflict_remove1_pre (-K, D));
     let D = lookup_conflict_remove1 (-K) D;
     let outl = outl[0 := -K];
     vm \<leftarrow> isa_vmtf_mark_to_rescore_also_reasons M N outl vm;
     (D, cach, outl) \<leftarrow> isa_minimize_and_extract_highest_lookup_conflict M N D cach lbd outl;
     ASSERT(empty_cach_ref_pre cach);
     let cach = empty_cach_ref cach;
     ASSERT(outl \<noteq> [] \<and> length outl \<le> uint32_max);
     (D, C, n) \<leftarrow> isa_empty_conflict_and_extract_clause_heur M D outl;
     RETURN ((M, N, D, Q', W', vm, \<phi>, clvls, cach, lbd, take 1 outl, stats, ccont, vdom), n, C)
  })\<close>
  unfolding extract_shorter_conflict_list_heur_st_def
  by (auto simp: the_lookup_conflict_def Let_def intro!: ext)

sepref_register isa_minimize_and_extract_highest_lookup_conflict
  empty_conflict_and_extract_clause_heur

sepref_def extract_shorter_conflict_list_heur_st_fast
  is \<open>extract_shorter_conflict_list_heur_st\<close>
  :: \<open>[\<lambda>S. length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
        isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn *a uint32_nat_assn *a clause_ll_assn\<close>
  supply [[goals_limit=1]] empty_conflict_and_extract_clause_pre_def[simp]
  unfolding extract_shorter_conflict_list_heur_st_alt_def PR_CONST_def isasat_bounded_assn_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    fold_tuple_optimizations
  apply (annot_snat_const "TYPE(64)")
  by sepref


sepref_register find_lit_of_max_level_wl
  extract_shorter_conflict_list_heur_st lit_of_hd_trail_st_heur propagate_bt_wl_D_heur
  propagate_unit_bt_wl_D_int
sepref_register backtrack_wl

sepref_def lit_of_hd_trail_st_heur_fast_code
  is \<open>lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>S. True]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_def backtrack_wl_D_fast_code
  is \<open>backtrack_wl_D_nlit_heur\<close>
  :: \<open>[isasat_fast]\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
    size_conflict_wl_def[simp] isasat_fast_length_leD[intro] isasat_fast_def[simp]
  unfolding backtrack_wl_D_nlit_heur_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric]
    size_conflict_wl_def[symmetric]
  unfolding fold_tuple_optimizations
  apply (annot_snat_const "TYPE(64)")
  by sepref

(* TODO: Move *)
lemmas [llvm_inline] = add_lbd_def

experiment
begin

  export_llvm
    empty_conflict_and_extract_clause_heur_fast_code
    empty_cach_code
    propagate_bt_wl_D_fast_codeXX
    propagate_unit_bt_wl_D_fast_code
    extract_shorter_conflict_list_heur_st_fast
    lit_of_hd_trail_st_heur_fast_code
    backtrack_wl_D_fast_code
  

end  
  
  
end
