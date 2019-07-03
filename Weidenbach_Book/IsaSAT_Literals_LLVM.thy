theory IsaSAT_Literals_LLVM
  imports WB_More_Word IsaSAT_Literals Watched_Literals.WB_More_IICF_LLVM
begin

(*
(* TODO: Also for max_unat, and move to default simpset of Sepref! *)    
lemma max_snat_numeral[simp]:
  "0 < max_snat n"  
  "1 < max_snat n \<longleftrightarrow> n>1"
  "numeral x < max_snat n \<longleftrightarrow> (numeral x ::nat) < 2^(n-1)"
  subgoal by (auto simp: max_snat_def) []
  subgoal unfolding max_snat_def by (metis nat_neq_iff nat_power_eq_Suc_0_iff nat_zero_less_power_iff not_less_eq numerals(2) power_0 zero_less_Suc zero_less_diff)
  subgoal by (auto simp: max_snat_def) []
  done

lemma max_unat_numeral[simp]:
  "0 < max_unat n"  
  "1 < max_unat n \<longleftrightarrow> n>0"
  "numeral x < max_unat n \<longleftrightarrow> (numeral x ::nat) < 2^n"
  subgoal by (auto simp: max_unat_def) []
  subgoal unfolding max_unat_def by (metis nat_neq_iff nat_power_eq_Suc_0_iff nat_zero_less_power_iff not_less_eq numerals(2) power_0 zero_less_Suc)
  subgoal by (auto simp: max_unat_def) []
  done
*)

(* TODO: Move! 
  TODO: General max functions!
  TODO: Name should be snatN_max
 
*)
lemma sint64_max_refine[sepref_import_param]: "(0x7FFFFFFFFFFFFFFF, sint64_max)\<in>snat_rel' TYPE(64)"
  apply (auto simp: snat_rel_def snat.rel_def in_br_conv sint64_max_def snat_invar_def)
  apply (auto simp: snat_def)
  done

lemma sint32_max_refine[sepref_import_param]: "(0x7FFFFFFF, sint32_max)\<in>snat_rel' TYPE(32)"
  apply (auto simp: snat_rel_def snat.rel_def in_br_conv sint32_max_def snat_invar_def)
  apply (auto simp: snat_def)
  done
  
lemma uint64_max_refine[sepref_import_param]: "(0xFFFFFFFFFFFFFFFF, uint64_max)\<in>unat_rel' TYPE(64)"
  apply (auto simp: unat_rel_def unat.rel_def in_br_conv uint64_max_def)
  done

lemma uint32_max_refine[sepref_import_param]: "(0xFFFFFFFF, uint32_max)\<in>unat_rel' TYPE(32)"
  apply (auto simp: unat_rel_def unat.rel_def in_br_conv uint32_max_def)
  done
  

  


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


lemmas [sepref_bounds_simps] = 
  uint32_max_def sint32_max_def
  uint64_max_def sint64_max_def


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
  
type_synonym atom_assn = "32 word"

definition "atom_rel \<equiv> b_rel (unat_rel' TYPE(32)) (\<lambda>x. x<2^31)"
abbreviation "atom_assn \<equiv> pure atom_rel"

lemma atom_rel_alt: "atom_rel = unat_rel' TYPE(32) O nbn_rel (2^31)"
  by (auto simp: atom_rel_def)
  
interpretation atom: dflt_pure_option_private "2^32-1" atom_assn "ll_icmp_eq (2^32-1)"
  apply unfold_locales
  subgoal 
    unfolding atom_rel_def 
    apply (simp add: pure_def fun_eq_iff pred_lift_extract_simps)
    apply (auto simp: unat_rel_def unat.rel_def in_br_conv unat_minus_one_word)
    done
  subgoal proof goal_cases
    case 1
      interpret llvm_prim_arith_setup .
      show ?case unfolding bool.assn_def by vcg'
    qed
  subgoal by simp
  done  


lemma atm_of_refine: "(\<lambda>x. x div 2 , atm_of) \<in> nat_lit_rel \<rightarrow> nat_rel"  
  by (auto simp: nat_lit_rel_def in_br_conv)

  
sepref_definition atm_of_impl is "RETURN o (\<lambda>x::nat. x div 2)" 
  :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn"
  unfolding atom_rel_def b_assn_pure_conv[symmetric]
  apply (rule hfref_bassn_resI)
  subgoal by sepref_bounds
  apply (annot_unat_const "TYPE(32)")
  by sepref
  
lemmas [sepref_fr_rules] = atm_of_impl.refine[FCOMP atm_of_refine]
  

definition Pos_rel :: \<open>nat \<Rightarrow> nat\<close> where
 [simp]: \<open>Pos_rel n = 2 * n\<close>

lemma Pos_refine_aux: "(Pos_rel,Pos)\<in>nat_rel \<rightarrow> nat_lit_rel"
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)
  
lemma Neg_refine_aux: "(\<lambda>x. 2*x + 1,Neg)\<in>nat_rel \<rightarrow> nat_lit_rel"
  by (auto simp: nat_lit_rel_def in_br_conv split: if_splits)

sepref_definition Pos_impl is "RETURN o Pos_rel" :: "atom_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding atom_rel_def Pos_rel_def
  apply (annot_unat_const "TYPE(32)")
  by sepref
  
sepref_definition Neg_impl is "RETURN o (\<lambda>x. 2*x+1)" :: "atom_assn\<^sup>d \<rightarrow>\<^sub>a uint32_nat_assn"
  unfolding atom_rel_def
  apply (annot_unat_const "TYPE(32)")
  by sepref
  
(*sepref_definition Neg_impl is "RETURN o (\<lambda>x. 2*x+1)" :: "[\<lambda>x. x \<le> uint32_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn"
  apply (annot_unat_const "TYPE(32)")
  by sepref
*)  
  
lemmas [sepref_fr_rules] = 
  Pos_impl.refine[FCOMP Pos_refine_aux]
  Neg_impl.refine[FCOMP Neg_refine_aux]

sepref_definition atom_eq_impl is "uncurry (RETURN oo (=))" :: "atom_assn\<^sup>d *\<^sub>a atom_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn"
  unfolding atom_rel_def
  by sepref

lemmas [sepref_fr_rules] = atom_eq_impl.refine

  
  
definition value_of_atm :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>value_of_atm A = A\<close>

lemma value_of_atm_rel: \<open>(\<lambda>x. x, value_of_atm) \<in> nat_rel \<rightarrow> nat_rel\<close>
  by (auto)

sepref_definition value_of_atm_impl
  is \<open>RETURN o (\<lambda>x. x)\<close>
  :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a unat_assn' TYPE(32)\<close>
  unfolding value_of_atm_def atom_rel_def
  by sepref

lemmas [sepref_fr_rules] = value_of_atm_impl.refine[FCOMP value_of_atm_rel]

definition index_of_atm :: \<open>nat \<Rightarrow> nat\<close> where
[simp]: \<open>index_of_atm A = value_of_atm A\<close>

lemma index_of_atm_rel: \<open>(\<lambda>x. value_of_atm x, index_of_atm) \<in> nat_rel \<rightarrow> nat_rel\<close>
  by (auto)


sepref_definition index_of_atm_impl 
  is \<open>RETURN o (\<lambda>x. value_of_atm x)\<close>
  :: \<open>atom_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding index_of_atm_def
  apply (rewrite at "_" eta_expand)
  apply (subst annot_unat_snat_upcast[where 'l=64])
  by sepref

lemmas [sepref_fr_rules] = index_of_atm_impl.refine[FCOMP index_of_atm_rel]

lemma annot_index_of_atm: \<open>xs ! x = xs ! index_of_atm x\<close>
   \<open>xs [x := a] = xs [index_of_atm x := a]\<close>
  by auto

definition index_atm_of where
[simp]: \<open>index_atm_of L = index_of_atm (atm_of L)\<close>

(* TODO: Use at more places! *)
context fixes x y :: nat assumes "NO_MATCH (index_of_atm y) x" begin
  lemmas annot_index_of_atm' = annot_index_of_atm[where x=x]
end  

method_setup annot_all_atm_idxs = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' 
    let 
      val ctxt = put_simpset HOL_basic_ss ctxt 
      val ctxt = ctxt addsimps @{thms annot_index_of_atm'}
      val ctxt = ctxt addsimprocs [@{simproc NO_MATCH}]
    in
      simp_tac ctxt
    end  
  )\<close>

lemma annot_index_atm_of[def_pat_rules]:
  \<open>nth$xs$(atm_of$x) \<equiv> nth$xs$(index_atm_of$x)\<close>
  \<open>list_update$xs$(atm_of$x)$a \<equiv> list_update$xs$(index_atm_of$x)$a\<close>
  by auto

  
sepref_definition index_atm_of_impl 
  is \<open>RETURN o index_atm_of\<close>
  :: \<open>unat_lit_assn\<^sup>d \<rightarrow>\<^sub>a snat_assn' TYPE(64)\<close>
  unfolding index_atm_of_def
  by sepref

declare index_atm_of_impl.refine [sepref_fr_rules]




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
