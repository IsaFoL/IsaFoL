theory IsaSAT_Literals_LLVM
  imports WB_More_Word IsaSAT_Literals Watched_Literals.WB_More_IICF_LLVM
begin

lemma convert_fref:
  "WB_More_Refinement.fref = Sepref_Rules.frefnd"
  "WB_More_Refinement.freft = Sepref_Rules.freftnd"
  unfolding WB_More_Refinement.fref_def Sepref_Rules.fref_def
  by auto
 
no_notation WB_More_Refinement.fref ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60)
no_notation WB_More_Refinement.freft ("_ \<rightarrow>\<^sub>f _" [60,60] 60)
    
(* TODO: Move *)

abbreviation "uint32_nat_assn \<equiv> unat_assn' TYPE(32)"
abbreviation "uint64_nat_assn \<equiv> unat_assn' TYPE(64)"

abbreviation "sint32_nat_assn \<equiv> snat_assn' TYPE(32)"
abbreviation "sint64_nat_assn \<equiv> snat_assn' TYPE(64)"


lemma is_up'_32_64[simp,intro!]: "is_up' UCAST(32 \<rightarrow> 64)" by (simp add: is_up')
lemma is_down'_64_32[simp,intro!]: "is_down' UCAST(64 \<rightarrow> 32)"  by (simp add: is_down')

lemma ins_idx_upcast64: 
  "l[i:=y] = op_list_set l (op_unat_snat_upcast TYPE(64) i) y"
  "l!i = op_list_get l (op_unat_snat_upcast TYPE(64) i)" 
  by simp_all

type_synonym 'a array_list32 = "('a,32)array_list"
type_synonym 'a array_list64 = "('a,64)array_list"
  
abbreviation "arl32_assn \<equiv> al_assn' TYPE(32)"
abbreviation "arl64_assn \<equiv> al_assn' TYPE(64)"


type_synonym 'a larray32 = "('a,32) larray"
type_synonym 'a larray64 = "('a,64) larray"

abbreviation "larray32_assn \<equiv> larray_assn' TYPE(32)"
abbreviation "larray64_assn \<equiv> larray_assn' TYPE(64)"
  


definition "unat_lit_rel == unat_rel' TYPE(32) O nat_lit_rel"  
lemmas [fcomp_norm_unfold] = unat_lit_rel_def[symmetric]
  
abbreviation unat_lit_assn :: \<open>nat literal \<Rightarrow> 32 word \<Rightarrow> assn\<close> where
  \<open>unat_lit_assn \<equiv> pure unat_lit_rel\<close>

subsection \<open>Atom-Of\<close>  
  
sepref_decl_op atm_of: \<open>atm_of :: nat literal \<Rightarrow> nat\<close> ::
  \<open>(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat \<times> _) set)\<close> .

lemma [def_pat_rules]:
  \<open>atm_of \<equiv> op_atm_of\<close>
  by auto

lemma atm_of_refine: "(\<lambda>x. x div 2 , op_atm_of) \<in> nat_lit_rel \<rightarrow> nat_rel"  
  by (auto simp: nat_lit_rel_def in_br_conv)
  
sepref_definition atm_of_impl is "RETURN o (\<lambda>x::nat. x div 2)" 
  :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  supply [simp] = max_unat_def
  apply (annot_unat_const "TYPE(32)")
  by sepref
  
sepref_decl_impl atm_of_impl.refine[FCOMP atm_of_refine] .

lemma nat_of_lit_refine_aux: "((\<lambda>x. x), nat_of_lit) \<in> nat_lit_rel \<rightarrow> nat_rel"
  by (auto simp: nat_lit_rel_def in_br_conv)

sepref_definition nat_of_lit_rel_impl is "RETURN o (\<lambda>x::nat. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn"
  apply (rewrite annot_unat_snat_upcast[where 'l=64])
  by sepref
lemmas [sepref_fr_rules] = nat_of_lit_rel_impl.refine[FCOMP nat_of_lit_refine_aux]
  
  
lemma uminus_refine_aux: "(\<lambda>x. x XOR 1, uminus) \<in> nat_lit_rel \<rightarrow> nat_lit_rel"
  apply (auto simp: nat_lit_rel_def in_br_conv bitXOR_1_if_mod_2[simplified])
  subgoal by linarith
  subgoal by (metis dvd_minus_mod even_Suc_div_two odd_Suc_minus_one)
  done

sepref_definition uminus_impl is "RETURN o (\<lambda>x::nat. x XOR 1)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
  supply [simp] = max_unat_def
  apply (annot_unat_const "TYPE(32)")
  by sepref

lemmas [sepref_fr_rules] = uminus_impl.refine[FCOMP uminus_refine_aux]
  
lemma lit_eq_refine_aux: "( (=), (=) ) \<in> nat_lit_rel \<rightarrow> nat_lit_rel \<rightarrow> bool_rel"
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits; auto?; presburger)

sepref_definition lit_eq_impl is "uncurry (RETURN oo (=))" :: "uint32_nat_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  by sepref

lemmas [sepref_fr_rules] = lit_eq_impl.refine[FCOMP lit_eq_refine_aux]

lemma is_pos_refine_aux: "(\<lambda>x. x AND 1 = 0, is_pos) \<in> nat_lit_rel \<rightarrow> bool_rel"
  by (auto simp: nat_lit_rel_def in_br_conv bitAND_1_mod_2[simplified] split: if_splits)
  
sepref_definition is_pos_impl is "RETURN o (\<lambda>x. x AND 1 = 0)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  apply (annot_unat_const "TYPE(32)")
  by sepref
  
lemmas [sepref_fr_rules] = is_pos_impl.refine[FCOMP is_pos_refine_aux]


lemma Pos_refine_aux: "(\<lambda>x. 2*x,Pos)\<in>nat_rel \<rightarrow> nat_lit_rel"
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)
  
lemma Neg_refine_aux: "(\<lambda>x. 2*x + 1,Neg)\<in>nat_rel \<rightarrow> nat_lit_rel"
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)

sepref_definition Pos_impl is "RETURN o (\<lambda>x. 2*x)" :: "[\<lambda>x. x \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn"
  apply (annot_unat_const "TYPE(32)")
  supply [simp] = max_unat_def uint32_max_def
  by sepref
  
sepref_definition Neg_impl is "RETURN o (\<lambda>x. 2*x+1)" :: "[\<lambda>x. x \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn"
  apply (annot_unat_const "TYPE(32)")
  supply [simp] = max_unat_def uint32_max_def
  by sepref
  
lemmas [sepref_fr_rules] = 
  Pos_impl.refine[FCOMP Pos_refine_aux]
  Neg_impl.refine[FCOMP Neg_refine_aux]
  
  



(*lemma propagated_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo propagated), uncurry (RETURN oo Propagated)) \<in>
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def propagated_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

lemma decided_hnr[sepref_fr_rules]:
  \<open>(return o decided, RETURN o Decided) \<in>
     unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a pair_nat_ann_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_ann_lit_rel_def decided_def case_prod_beta p2rel_def
      br_def uint32_nat_rel_def unat_lit_rel_def nat_lit_rel_def
      split: option.splits)

*)      
      
(*
type_synonym clause_wl = \<open>(32 word,64) larray\<close>
abbreviation clause_ll_assn :: \<open>nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn\<close> where
  \<open>clause_ll_assn \<equiv> larray_assn unat_lit_assn\<close>
*)  
  
end
