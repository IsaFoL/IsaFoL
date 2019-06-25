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

lemma upcast_no_msb[simp]: "LENGTH('small::len) < LENGTH('big::len) \<Longrightarrow> \<not>msb (UCAST('small \<rightarrow> 'big) x)" 
  apply (clarsimp simp: ucast_def msb_word_of_int)
  apply transfer
  using nth_bintr by auto
  
  
context begin
  interpretation llvm_prim_arith_setup .

    
  definition [llvm_inline]: "unat_snat_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  definition [llvm_inline]: "snat_unat_downcast TYPE('a::len) x \<equiv> ll_trunc x TYPE('a word)"
    
  lemma unat_snat_upcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>unat.assn n (ni::'small::len word)) 
      (unat_snat_upcast TYPE('big::len2) ni) 
      (\<lambda>r. \<upharpoonleft>snat.assn n r)"
    unfolding unat.assn_def snat.assn_def unat_snat_upcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) unat_ucast_upcast)
    done

  lemma snat_unat_downcast_rule[vcg_rules]:
    "llvm_htriple 
      (\<up>(is_down' UCAST('big \<rightarrow> 'small)) ** \<upharpoonleft>snat.assn n (ni::'big::len2 word) ** \<up>(n<max_unat LENGTH('small))) 
      (snat_unat_downcast TYPE('small::len) ni) 
      (\<lambda>r. \<upharpoonleft>unat.assn n r)"
    unfolding unat.assn_def snat.assn_def snat_unat_downcast_def
    apply vcg'
    apply (auto simp: snat_invar_def snat_eq_unat(2) max_unat_def)
    by (metis ucast_nat_def unat_of_nat_eq)
    
      
  context fixes T :: "'a::len2 itself" begin
    definition [simp]: "unat_snat_upcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"
  
    sepref_decl_op unat_snat_upcast: "unat_snat_upcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
  end  

  context fixes T :: "'a::len itself" begin
    definition [simp]: "snat_unat_downcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"
  
    sepref_decl_op snat_unat_downcast: "snat_unat_downcast_aux" :: "nat_rel \<rightarrow> nat_rel" .
  end  

  lemma annot_unat_snat_upcast: "x = op_unat_snat_upcast TYPE('l::len2) x" by simp 
  lemma annot_snat_unat_downcast: "x = op_snat_unat_downcast TYPE('l::len) x" by simp 
    
  
  lemma in_unat_rel_conv_assn: "\<up>((xi, x) \<in> unat_rel) = \<upharpoonleft>unat.assn x xi"
    by (auto simp: unat_rel_def unat.assn_is_rel pure_app_eq)
  
  lemma in_snat_rel_conv_assn: "\<up>((xi, x) \<in> snat_rel) = \<upharpoonleft>snat.assn x xi"
    by (auto simp: snat_rel_def snat.assn_is_rel pure_app_eq)
  
  context fixes BIG :: "'big::len2" and SMALL :: "'small::len" begin  
    lemma unat_snat_upcast_refine: 
      "(unat_snat_upcast TYPE('big::len2), PR_CONST (mop_unat_snat_upcast TYPE('big::len2))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (unat_assn' TYPE('small::len))\<^sup>k \<rightarrow> snat_assn"
      supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
      apply sepref_to_hoare
      apply simp
      by vcg'
    
    sepref_decl_impl (ismop) unat_snat_upcast_refine fixes 'big 'small by simp
    
    
    lemma snat_unat_downcast_refine: 
      "(snat_unat_downcast TYPE('small), PR_CONST (mop_snat_unat_downcast TYPE('small))) 
        \<in> [\<lambda>x. is_down' UCAST('big \<rightarrow> 'small) \<and> x<max_unat LENGTH('small)]\<^sub>a (snat_assn' TYPE('big))\<^sup>k \<rightarrow> unat_assn"
      supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
      apply sepref_to_hoare
      apply simp
      by vcg'
    
    sepref_decl_impl (ismop) snat_unat_downcast_refine fixes 'big 'small by simp
  end
      
  definition unat_snat_conv :: "'l::len2 word \<Rightarrow> 'l word llM" 
    where "unat_snat_conv x \<equiv> return x"  
    
  lemma unat_snat_conv_rule[vcg_rules]: 
    "llvm_htriple (\<upharpoonleft>unat.assn x (xi::'l::len2 word) ** \<up>(x<max_snat LENGTH('l))) (unat_snat_conv xi) (\<lambda>r. \<upharpoonleft>snat.assn x r)"
    unfolding unat_snat_conv_def unat.assn_def snat.assn_def
    apply vcg'
    by (force simp: max_snat_def snat_invar_alt snat_eq_unat(1))
  
  sepref_decl_op unat_snat_conv: "id::nat\<Rightarrow>_" :: "nat_rel \<rightarrow> nat_rel" .
  
  context fixes T::"'l::len2" begin
    lemma unat_snat_conv_refine: "(\<lambda>x. x, op_unat_snat_conv) 
      \<in> [\<lambda>x. x<max_snat LENGTH('l::len2)]\<^sub>f unat_rel' TYPE('l) \<rightarrow> snat_rel' TYPE('l)"
      by (force 
        intro!: frefI 
        simp: snat_rel_def unat_rel_def snat.rel_def unat.rel_def
        simp: in_br_conv max_snat_def snat_invar_alt
        simp: snat_eq_unat(1)
        )
        
    thm unat_snat_conv_refine[sepref_param]    
        
    sepref_decl_impl unat_snat_conv_refine[sepref_param] fixes 'l by auto
  end   
  
  lemma annot_unat_snat_conv: "x = op_unat_snat_conv x" by simp 
      
end
  

(*
oops
xxx, ctd here: Define unat_snat_cast, with same length, if source is small enough!
*)


abbreviation "uint32_nat_assn \<equiv> unat_assn' TYPE(32)"
abbreviation "uint64_nat_assn \<equiv> unat_assn' TYPE(64)"


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

sepref_definition nat_of_lit_rel_impl is "RETURN o (\<lambda>x::nat. x)" :: "uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn"
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
