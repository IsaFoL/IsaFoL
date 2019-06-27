theory IsaSAT_Trail_LLVM
imports IsaSAT_Literals_LLVM IsaSAT_Trail   
begin


type_synonym tri_bool_assn = "8 word"

definition "tri_bool_rel_aux \<equiv> { (0::nat,None), (2,Some True), (3,Some False) }"
definition "tri_bool_rel \<equiv> unat_rel' TYPE(8) O tri_bool_rel_aux"
abbreviation "tri_bool_assn \<equiv> pure tri_bool_rel"
lemmas [fcomp_norm_unfold] = tri_bool_rel_def[symmetric]

lemma tri_bool_UNSET_refine_aux: "(0,UNSET)\<in>tri_bool_rel_aux"
  and tri_bool_SET_TRUE_refine_aux: "(2,SET_TRUE)\<in>tri_bool_rel_aux"
  and tri_bool_SET_FALSE_refine_aux: "(3,SET_FALSE)\<in>tri_bool_rel_aux"
  and tri_bool_eq_refine_aux: "((=),tri_bool_eq) \<in> tri_bool_rel_aux\<rightarrow>tri_bool_rel_aux\<rightarrow>bool_rel"
  by (auto simp: tri_bool_rel_aux_def tri_bool_eq_def)

sepref_definition tri_bool_UNSET_impl is "uncurry0 (RETURN 0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(8)"
  apply (annot_unat_const "TYPE(8)")
  by sepref

sepref_definition tri_bool_SET_TRUE_impl is "uncurry0 (RETURN 2)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(8)"
  apply (annot_unat_const "TYPE(8)")
  supply [simp] = max_unat_def
  by sepref

sepref_definition tri_bool_SET_FALSE_impl is "uncurry0 (RETURN 3)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn' TYPE(8)"
  apply (annot_unat_const "TYPE(8)")
  supply [simp] = max_unat_def
  by sepref

sepref_definition tri_bool_eq_impl is "uncurry (RETURN oo (=))" :: "(unat_assn' TYPE(8))\<^sup>k *\<^sub>a (unat_assn' TYPE(8))\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  by sepref
  
lemmas [sepref_fr_rules] = 
  tri_bool_UNSET_impl.refine[FCOMP tri_bool_UNSET_refine_aux]
  tri_bool_SET_TRUE_impl.refine[FCOMP tri_bool_SET_TRUE_refine_aux]
  tri_bool_SET_FALSE_impl.refine[FCOMP tri_bool_SET_FALSE_refine_aux]
  tri_bool_eq_impl.refine[FCOMP tri_bool_eq_refine_aux]

type_synonym trail_pol_fast_assn =
   \<open>32 word array_list64 \<times> tri_bool_assn larray64 \<times> 32 word larray64 \<times>
     64 word larray64 \<times> 32 word \<times>
     32 word array_list64\<close>

sepref_definition DECISION_REASON_impl is "uncurry0 (RETURN DECISION_REASON)" 
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn"
  unfolding DECISION_REASON_def apply (annot_snat_const "TYPE(64)") by sepref
lemmas [sepref_fr_rules] = DECISION_REASON_impl.refine  
     

abbreviation trail_pol_fast_assn :: \<open>trail_pol \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_fast_assn \<equiv>
    arl64_assn unat_lit_assn *a larray64_assn (tri_bool_assn) *a
    larray64_assn uint32_nat_assn *a
    larray64_assn sint64_nat_assn *a uint32_nat_assn *a
    arl64_assn uint32_nat_assn\<close>


paragraph \<open>Code generation\<close>

subparagraph \<open>Conversion between incomplete and complete mode\<close>

lemma count_decided_pol_workaround: \<open>RETURN o count_decided_pol = (\<lambda>(_, _, _, _, k, _). RETURN k)\<close>
  unfolding count_decided_pol_def by auto
  

sepref_definition count_decided_pol_impl is "RETURN o count_decided_pol" :: "trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding count_decided_pol_workaround
  by sepref
lemmas [sepref_fr_rules] = count_decided_pol_impl.refine


(*
lemma "RETURN
 ((\<lambda>(_::nat literal list, _::bool option list, _::nat list, _::nat list, k::nat,
      _::nat list). k)
   (uu::nat literal list \<times> bool option list \<times> nat list \<times> nat list \<times> nat \<times> nat list)) \<equiv>
RETURN $
(case_prod $
 (\<lambda>_::nat literal list.
     PROTECT2
      (case_prod $
       (\<lambda>_::bool option list.
           PROTECT2
            (case_prod $
             (\<lambda>_::nat list.
                 PROTECT2
                  (case_prod $
                   (\<lambda>_::nat list.
                       PROTECT2
                        (case_prod $
                         (\<lambda>k::nat. PROTECT2 (\<lambda>_::nat list. PROTECT2 k DUMMY) DUMMY))
                        DUMMY))
                  DUMMY))
            DUMMY))
      DUMMY) $
 uu) 
"



sepref_definition count_decided_pol_impl is "RETURN o count_decided_pol" :: "trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding count_decided_pol_def
  apply sepref_dbg_keep
  apply (rule ID_init)
  supply [[trace_f_tac_conv]] [[show_types,show_sorts]]
  apply (tactic \<open>let 
    val ctxt = @{context} 
    
    fun f_tac_conv ctxt f tac ct = let
      val t = Thm.term_of ct
      val t' = f t
      val goal = Logic.mk_equals (t,t')
      val _ = tracing (Syntax.string_of_term ctxt goal)

      val goal = Thm.cterm_of ctxt goal handle e => raise (@{print} e)

      val thm = Goal.prove_internal ctxt [] goal (K tac)
    in
      thm
    end
    
    
    fun protect_conv ctxt = f_tac_conv ctxt
      (Id_Op.protect []) 
      (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms PROTECT2_def APP_def}) 1)
      
      (*
      (((K (print_tac ctxt "FOO")) THEN' simp_tac 
        (put_simpset HOL_basic_ss ctxt addsimps @{thms PROTECT2_def APP_def})) 1)
      *)
    
    
  in
    (CONVERSION Thm.eta_conversion
    THEN' CONVERSION (
        Refine_Util.HOL_concl_conv (fn ctxt => (Id_Op.id_a_conv (protect_conv ctxt))) 
          ctxt
      )

    ) 1
    end
  \<close>)
  
  apply sepref_dbg_id_init

*)  

sepref_definition get_level_atm_fast_code [llvm_code]
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[get_level_atm_pol_pre]\<^sub>a
  trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] 
     get_level_atm_pol_pre_def
  supply [[eta_contract = false, show_abbrevs=false]]   
  apply (rewrite at "nth _" eta_expand)   
  apply (rewrite in "nth _ \<hole>" annot_unat_snat_upcast[where 'l="64"])
  supply [[goals_limit = 1]]
  by sepref

declare get_level_atm_fast_code.refine[sepref_fr_rules]


sepref_definition get_level_fast_code [llvm_code]
  is \<open>uncurry (RETURN oo get_level_pol)\<close>
  :: \<open>[get_level_pol_pre]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric]
  get_level_pol_pre_def get_level_pol_def
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    get_level_atm_pol_pre_def[simp]
  by sepref

declare get_level_fast_code.refine[sepref_fr_rules]

sepref_definition polarity_pol_fast_code [llvm_code]
  is \<open>uncurry (RETURN oo polarity_pol)\<close>
  :: \<open>[uncurry polarity_pol_pre]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_pol_def option.case_eq_if polarity_pol_pre_def
  supply [[goals_limit = 1]]
  (*apply (rewrite in "nth _ \<hole>" annot_unat_snat_upcast[where 'l="64"])*)
  by sepref

declare polarity_pol_fast_code.refine[sepref_fr_rules]

sepref_definition isa_length_trail_fast_code [llvm_code]
  is \<open>RETURN o isa_length_trail\<close>
  :: \<open>[\<lambda>_. True]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> snat_assn' TYPE(64)\<close>
  unfolding isa_length_trail_def isa_length_trail_pre_def length_uint32_nat_def
  by sepref

declare isa_length_trail_fast_code.refine[sepref_fr_rules]


sepref_definition cons_trail_Propagated_tr_fast_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[cons_trail_Propagated_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Propagated_tr_pre_def
  unfolding ins_idx_upcast64[where i="atm_of _"]  
  (*unfolding ins_idx_upcast64  *)
  supply [[goals_limit = 1]]
  supply [simp] = max_snat_def uint32_max_def
  by sepref

declare cons_trail_Propagated_tr_fast_code.refine[sepref_fr_rules]

(*
sepref_definition (in -)last_trail_fast_code
  is \<open>RETURN o last_trail_pol\<close>
  :: \<open>[last_trail_pol_pre]\<^sub>a
       trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn *a option_assn uint64_nat_assn\<close>
  unfolding last_trail_pol_def nth_u_def[symmetric] zero_uint64_nat_def[symmetric]
    last_trail_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare last_trail_fast_code.refine[sepref_fr_rules]
*)


sepref_definition tl_trail_tr_fast_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[tl_trailt_tr_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split] 
  unfolding tl_trailt_tr_def UNSET_def[symmetric] tl_trailt_tr_pre_def
  unfolding ins_idx_upcast64[where i="atm_of _"]  
  apply (annot_unat_const "TYPE(32)")
  (*apply (rewrite at \<open>_ - one_uint32_nat\<close> fast_minus_def[symmetric])*)
  supply [[goals_limit = 1]]
  by sepref
  
  
declare tl_trail_tr_fast_code.refine[sepref_fr_rules]

sepref_definition tl_trail_proped_tr_fast_code
  is \<open>RETURN o tl_trail_propedt_tr\<close>
  :: \<open>[tl_trail_propedt_tr_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trail_propedt_tr_def UNSET_def[symmetric]
    tl_trail_propedt_tr_pre_def
  unfolding ins_idx_upcast64[where i="atm_of _"]  
  apply (annot_unat_const "TYPE(32)")
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_proped_tr_fast_code.refine[sepref_fr_rules]

sepref_definition (in -) lit_of_last_trail_fast_code
  is \<open>RETURN o lit_of_last_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_last_trail_pol_def
  by sepref

declare lit_of_last_trail_fast_code.refine[sepref_fr_rules]

sepref_definition cons_trail_Decided_tr_fast_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[cons_trail_Decided_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Decided_tr_pre_def
  unfolding ins_idx_upcast64[where i="atm_of _"]  
  apply (annot_unat_const "TYPE(32)")
  apply (rewrite at "_@[\<hole>]" in "(_,\<hole>)" annot_snat_unat_downcast[where 'l="32"])
  supply [[goals_limit = 1]]
  supply [simp] = max_unat_def uint32_max_def max_snat_def
  by sepref

declare cons_trail_Decided_tr_fast_code.refine[sepref_fr_rules]

sepref_definition defined_atm_fast_code
  is \<open>uncurry (RETURN oo defined_atm_pol)\<close>
  :: \<open>[uncurry defined_atm_pol_pre]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  unfolding defined_atm_pol_def UNSET_def[symmetric] tri_bool_eq_def[symmetric]
    defined_atm_pol_pre_def
  unfolding ins_idx_upcast64  
  supply [simp] = max_unat_def uint32_max_def max_snat_def
  apply (annot_unat_const "TYPE(32)")
  supply UNSET_def[simp del] 
  by sepref

declare defined_atm_fast_code.refine[sepref_fr_rules]

sepref_register get_propagation_reason_raw_pol
sepref_definition get_propagation_reason_fast_code
  is \<open>uncurry get_propagation_reason_raw_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding get_propagation_reason_raw_pol_def
  apply (rewrite at "_! \<hole>" annot_unat_snat_upcast[where 'l="64"])
  by sepref

declare get_propagation_reason_fast_code.refine[sepref_fr_rules]

(*
sepref_definition get_propagation_reason_fast_code
  is \<open>uncurry get_propagation_reason_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  unfolding get_propagation_reason_pol_def
   zero_uint64_nat_def[symmetric]
  by sepref

declare get_propagation_reason_fast_code.refine[sepref_fr_rules]
  get_propagation_reason_code.refine[sepref_fr_rules]
  

sepref_definition get_the_propagation_reason_code
  is \<open>uncurry get_the_propagation_reason_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  unfolding get_the_propagation_reason_pol_def
    tri_bool_eq_def[symmetric]
  by sepref

sepref_definition (in -) get_the_propagation_reason_fast_code
  is \<open>uncurry get_the_propagation_reason_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  unfolding get_the_propagation_reason_pol_def
    tri_bool_eq_def[symmetric]
  by sepref

declare get_the_propagation_reason_fast_code.refine[sepref_fr_rules]
  get_the_propagation_reason_code.refine[sepref_fr_rules]
*)

sepref_definition isa_trail_nth_fast_code
  is \<open>uncurry isa_trail_nth\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  unfolding isa_trail_nth_def
  unfolding ins_idx_upcast64  
  by sepref

declare isa_trail_nth_fast_code.refine[sepref_fr_rules]

sepref_definition tl_trail_tr_no_CS_fast_code
  is \<open>RETURN o tl_trailt_tr_no_CS\<close>
  :: \<open>[tl_trailt_tr_no_CS_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_no_CS_def UNSET_def[symmetric] tl_trailt_tr_no_CS_pre_def
  unfolding ins_idx_upcast64[where i="atm_of _"]  
  apply (annot_unat_const "TYPE(32)")
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_tr_no_CS_fast_code.refine[sepref_fr_rules]  
  
abbreviation (in -) trail_pol_fast_assn' :: \<open>trail_pol \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_fast_assn' \<equiv>
      arl64_assn unat_lit_assn *a larray64_assn (tri_bool_assn) *a
      larray64_assn uint32_nat_assn *a
      larray64_assn uint64_nat_assn *a uint32_nat_assn *a arl64_assn uint32_nat_assn\<close>

sepref_definition (in -) trail_conv_back_imp_fast_code
  is \<open>uncurry trail_conv_back_imp\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn'\<^sup>d \<rightarrow>\<^sub>a trail_pol_fast_assn'\<close>
  supply [[goals_limit=1]]
  unfolding trail_conv_back_imp_def 
  apply (rewrite at "take \<hole>" annot_unat_snat_upcast[where 'l=64])
  by sepref_dbg_keep
  

declare trail_conv_back_imp_fast_code.refine[sepref_fr_rules]


end
