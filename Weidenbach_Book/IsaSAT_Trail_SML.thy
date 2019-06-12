theory IsaSAT_Trail_SML
imports IsaSAT_Trail Refine_Imperative_HOL.IICF
begin
sepref_definition trail_pol_slow_of_fast_code
  is \<open>RETURN o trail_pol_slow_of_fast\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn\<close>
  unfolding trail_pol_slow_of_fast_def
  by sepref

declare trail_pol_slow_of_fast_code.refine[sepref_fr_rules]

sepref_definition trail_pol_fast_of_slow_code
  is \<open>RETURN o trail_pol_fast_of_slow\<close>
  :: \<open>[\<lambda>(M, val, lvls, reason, k). \<forall>i\<in>set reason. i < uint64_max]\<^sub>a
      trail_pol_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding trail_pol_fast_of_slow_def
  by sepref

declare trail_pol_fast_of_slow_code.refine[sepref_fr_rules]

sepref_definition get_level_atm_code
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[get_level_atm_pol_pre]\<^sub>a
  trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
    get_level_atm_pol_pre_def nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare get_level_atm_code.refine[sepref_fr_rules]


sepref_definition get_level_atm_fast_code
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[get_level_atm_pol_pre]\<^sub>a
  trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
    nth_u_def[symmetric] get_level_atm_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare get_level_atm_fast_code.refine[sepref_fr_rules]

sepref_definition get_level_code
  is \<open>uncurry (RETURN oo get_level_pol)\<close>
  :: \<open>[get_level_pol_pre]\<^sub>a
      trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric] get_level_pol_pre_def get_level_pol_def
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    get_level_atm_pol_pre_def[simp]
  by sepref

declare get_level_code.refine[sepref_fr_rules]

sepref_definition get_level_fast_code
  is \<open>uncurry (RETURN oo get_level_pol)\<close>
  :: \<open>[get_level_pol_pre]\<^sub>a
      trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric] get_level_pol_pre_def get_level_pol_def
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
    get_level_atm_pol_pre_def[simp]
  by sepref

declare get_level_fast_code.refine[sepref_fr_rules]

sepref_definition polarity_pol_code
  is \<open>uncurry (RETURN oo polarity_pol)\<close>
  :: \<open>[uncurry polarity_pol_pre]\<^sub>a trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_pol_def option.case_eq_if polarity_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_pol_code.refine[sepref_fr_rules]

sepref_definition polarity_pol_fast_code
  is \<open>uncurry (RETURN oo polarity_pol)\<close>
  :: \<open>[uncurry polarity_pol_pre]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_pol_def option.case_eq_if polarity_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_pol_fast_code.refine[sepref_fr_rules]

sepref_definition isa_length_trail_code
  is \<open>RETURN o isa_length_trail\<close>
  :: \<open>[isa_length_trail_pre]\<^sub>a trail_pol_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isa_length_trail_def isa_length_trail_pre_def
  by sepref

sepref_definition isa_length_trail_fast_code
  is \<open>RETURN o isa_length_trail\<close>
  :: \<open>[isa_length_trail_pre]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isa_length_trail_def isa_length_trail_pre_def
  by sepref

declare isa_length_trail_code.refine[sepref_fr_rules]
  isa_length_trail_fast_code.refine[sepref_fr_rules]

sepref_definition cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[cons_trail_Propagated_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Propagated_tr_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare cons_trail_Propagated_tr_code.refine[sepref_fr_rules]

sepref_definition cons_trail_Propagated_tr_fast_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[cons_trail_Propagated_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Propagated_tr_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare cons_trail_Propagated_tr_fast_code.refine[sepref_fr_rules]

sepref_definition (in -)last_trail_code
  is \<open>RETURN o last_trail_pol\<close>
  :: \<open>[last_trail_pol_pre]\<^sub>a
       trail_pol_assn\<^sup>k \<rightarrow> unat_lit_assn *a option_assn nat_assn\<close>
  unfolding last_trail_pol_def nth_u_def[symmetric] last_trail_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare last_trail_code.refine[sepref_fr_rules]

sepref_definition (in -)last_trail_fast_code
  is \<open>RETURN o last_trail_pol\<close>
  :: \<open>[last_trail_pol_pre]\<^sub>a
       trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn *a option_assn uint64_nat_assn\<close>
  supply DECISION_REASON_uint64[sepref_fr_rules]
  unfolding last_trail_pol_def nth_u_def[symmetric] zero_uint64_nat_def[symmetric]
    last_trail_pol_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare last_trail_fast_code.refine[sepref_fr_rules]

sepref_definition tl_trail_tr_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[tl_trailt_tr_pre]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_def UNSET_def[symmetric] butlast_nonresizing_def[symmetric]
    tl_trailt_tr_pre_def
  apply (rewrite at \<open>_ - one_uint32_nat\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_tr_code.refine[sepref_fr_rules]

sepref_definition tl_trail_tr_fast_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[tl_trailt_tr_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split] DECISION_REASON_uint64[sepref_fr_rules]
  unfolding tl_trailt_tr_def UNSET_def[symmetric] zero_uint64_nat_def[symmetric]
     butlast_nonresizing_def[symmetric] tl_trailt_tr_pre_def
  apply (rewrite at \<open>_ - one_uint32_nat\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_tr_fast_code.refine[sepref_fr_rules]

sepref_definition tl_trail_proped_tr_code
  is \<open>RETURN o tl_trail_propedt_tr\<close>
  :: \<open>[tl_trail_propedt_tr_pre]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trail_propedt_tr_def UNSET_def[symmetric]
     butlast_nonresizing_def[symmetric] tl_trail_propedt_tr_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_proped_tr_code.refine[sepref_fr_rules]


sepref_definition tl_trail_proped_tr_fast_code
  is \<open>RETURN o tl_trail_propedt_tr\<close>
  :: \<open>[tl_trail_propedt_tr_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trail_propedt_tr_def UNSET_def[symmetric]
    butlast_nonresizing_def[symmetric] tl_trail_propedt_tr_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare tl_trail_proped_tr_fast_code.refine[sepref_fr_rules]

sepref_definition (in -) lit_of_last_trail_code
  is \<open>RETURN o lit_of_last_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_last_trail_pol_def
  by sepref

sepref_definition (in -) lit_of_last_trail_fast_code
  is \<open>RETURN o lit_of_last_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_last_trail_pol_def
  by sepref

declare lit_of_last_trail_code.refine[sepref_fr_rules]
declare lit_of_last_trail_fast_code.refine[sepref_fr_rules]

sepref_definition cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[cons_trail_Decided_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def one_uint32_nat_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Decided_tr_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare cons_trail_Decided_tr_code.refine[sepref_fr_rules]

sepref_definition cons_trail_Decided_tr_fast_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[cons_trail_Decided_tr_pre]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def one_uint32_nat_def[symmetric]
    SET_TRUE_def[symmetric] SET_FALSE_def[symmetric] cons_trail_Decided_tr_pre_def
    zero_uint64_nat_def[symmetric]
  supply [[goals_limit = 1]] DECISION_REASON_uint64[sepref_fr_rules]
  by sepref

declare cons_trail_Decided_tr_fast_code.refine[sepref_fr_rules]

sepref_definition defined_atm_code
  is \<open>uncurry (RETURN oo defined_atm_pol)\<close>
  :: \<open>[uncurry defined_atm_pol_pre]\<^sub>a trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding defined_atm_pol_def UNSET_def[symmetric] tri_bool_eq_def[symmetric]
    defined_atm_pol_pre_def
  supply UNSET_def[simp del] uint32_nat_assn_mult[sepref_fr_rules]
  by sepref

declare defined_atm_code.refine[sepref_fr_rules]

sepref_definition defined_atm_fast_code
  is \<open>uncurry (RETURN oo defined_atm_pol)\<close>
  :: \<open>[uncurry defined_atm_pol_pre]\<^sub>a trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding defined_atm_pol_def UNSET_def[symmetric] tri_bool_eq_def[symmetric]
    defined_atm_pol_pre_def
  supply UNSET_def[simp del] uint32_nat_assn_mult[sepref_fr_rules]
  by sepref

declare defined_atm_code.refine[sepref_fr_rules]
   defined_atm_fast_code.refine[sepref_fr_rules]

sepref_definition get_propagation_reason_code
  is \<open>uncurry get_propagation_reason_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn\<close>
  unfolding get_propagation_reason_pol_def
  by sepref

sepref_definition get_propagation_reason_fast_code
  is \<open>uncurry get_propagation_reason_pol\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn uint64_nat_assn\<close>
  supply DECISION_REASON_uint64[sepref_fr_rules]
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
  supply DECISION_REASON_uint64[sepref_fr_rules]
  unfolding get_the_propagation_reason_pol_def
    tri_bool_eq_def[symmetric]
  by sepref

declare get_the_propagation_reason_fast_code.refine[sepref_fr_rules]
  get_the_propagation_reason_code.refine[sepref_fr_rules]

sepref_definition isa_trail_nth_code
  is \<open>uncurry isa_trail_nth\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  unfolding isa_trail_nth_def
  by sepref

sepref_definition isa_trail_nth_fast_code
  is \<open>uncurry isa_trail_nth\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a unat_lit_assn\<close>
  unfolding isa_trail_nth_def
  by sepref

declare isa_trail_nth_code.refine[sepref_fr_rules]
  isa_trail_nth_fast_code.refine[sepref_fr_rules]

sepref_definition tl_trail_tr_no_CS_code
  is \<open>RETURN o tl_trailt_tr_no_CS\<close>
  :: \<open>[tl_trailt_tr_no_CS_pre]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_no_CS_def UNSET_def[symmetric] tl_trailt_tr_no_CS_pre_def
    butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition tl_trail_tr_no_CS_fast_code
  is \<open>RETURN o tl_trailt_tr_no_CS\<close>
  :: \<open>[tl_trailt_tr_no_CS_pre]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_no_CS_def UNSET_def[symmetric] tl_trailt_tr_no_CS_pre_def
    butlast_nonresizing_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

sepref_definition (in -) trail_conv_back_imp_code
  is \<open>uncurry trail_conv_back_imp\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_assn'\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn'\<close>
  supply [[goals_limit=1]] nat_of_uint32_conv_def[simp]
  unfolding trail_conv_back_imp_def
  by sepref

declare trail_conv_back_imp_code.refine[sepref_fr_rules]

sepref_definition (in -) trail_conv_back_imp_fast_code
  is \<open>uncurry trail_conv_back_imp\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn'\<^sup>d \<rightarrow>\<^sub>a trail_pol_fast_assn'\<close>
  supply [[goals_limit=1]]
  unfolding trail_conv_back_imp_def
  by sepref

declare trail_conv_back_imp_fast_code.refine[sepref_fr_rules]

end
