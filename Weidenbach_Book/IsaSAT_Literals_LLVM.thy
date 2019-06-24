theory IsaSAT_Literals_LLVM
  imports WB_More_Word IsaSAT_Literals Watched_Literals.WB_More_IICF_LLVM
begin


(* TODO: Move to larray-impl thy *)
type_synonym ('x,'l) larray = "'l word \<times> 'x ptr"


(* TODO: Move *)
hide_const (open) Separation_Algebra.pure
term pure

lemma convert_fref:
  "WB_More_Refinement.fref = Sepref_Rules.frefnd"
  "WB_More_Refinement.freft = Sepref_Rules.freftnd"
  unfolding WB_More_Refinement.fref_def Sepref_Rules.fref_def
  by auto
(* TODO: Move *)

definition unat_rel :: "('a::len word \<times> nat) set" where "unat_rel \<equiv> unat.rel"
abbreviation "unat_assn \<equiv> pure unat_rel"  

abbreviation (input) "unat_rel' TYPE('a::len) \<equiv> unat_rel :: ('a word \<times> _) set"
abbreviation (input) "unat_assn' TYPE('a::len) \<equiv> unat_assn :: _ \<Rightarrow> 'a word \<Rightarrow> _"


lemma unat_or: "unat (x OR y) = unat x OR unat y"
  unfolding unat_def
  by (simp add: uint_or bitOR_nat_def)

lemma unat_and: "unat (x AND y) = unat x AND unat y"
  unfolding unat_def
  by (simp add: uint_and bitAND_nat_def)
  
lemma unat_xor: "unat (x XOR y) = unat x XOR unat y"
  unfolding unat_def
  by (simp add: uint_xor bitXOR_nat_def)

context begin                                             

interpretation llvm_prim_arith_setup .

lemma unat_bin_ops_bitwise:
  "unat.is_bin_op (\<lambda>_ _ _. True) ll_and (AND) (AND)" 
  "unat.is_bin_op (\<lambda>_ _ _. True) ll_or (OR) (OR)" 
  "unat.is_bin_op (\<lambda>_ _ _. True) ll_xor (XOR) (XOR)" 
  by (all \<open>prove_unat_op simp: unat_and unat_or unat_xor\<close>)
  
end



definition [simp]: "unat_const TYPE('a::len) c \<equiv> (c::nat)"
context fixes c::nat begin
  sepref_register "unat_const TYPE('a::len) c" :: "nat"
end

lemma fold_unat:
  "0 = unat_const TYPE('a::len) 0"  
  "1 = unat_const TYPE('a::len) 1"  
  "numeral n \<equiv> (unat_const TYPE('a::len) (numeral n))"
  by simp_all

  
lemma hn_unat_0[sepref_fr_rules]:
  "hn_refine \<box> (return 0) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 0))"
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  supply [simp] = snat_invar_0
  apply vcg
  done
  
lemma hn_unat_1[sepref_fr_rules]:
  "hn_refine \<box> (return 1) \<box> (unat_assn' TYPE('a::len)) (RETURN$PR_CONST (unat_const TYPE('a) 1))"
  apply sepref_to_hoare
  unfolding unat_rel_def unat.rel_def in_br_conv
  supply [simp] = snat_invar_1
  apply vcg
  done
  
  
lemma hn_unat_numeral[sepref_fr_rules]:
  "\<lbrakk>numeral n \<in> unats LENGTH('a)\<rbrakk> \<Longrightarrow> 
    hn_refine \<box> (return (numeral n)) \<box> (unat_assn' TYPE('a::len)) (RETURN$(PR_CONST (unat_const TYPE('a) (numeral n))))"
  apply sepref_to_hoare unfolding unat_rel_def unat.rel_def in_br_conv 
  apply vcg'
  by (metis in_unats_conv int_nat_eq of_nat_numeral uint_nonnegative unat_bintrunc unat_def word_of_int_numeral word_uint.Rep_inverse' word_unat.Rep_cases)

(* TODO: Setup for int seems to be missing to! *)  
sepref_register    
  and_word: "(AND):: nat \<Rightarrow> _"  
  or_word: "(OR):: nat \<Rightarrow> _"  
  xor_word: "(XOR):: nat \<Rightarrow> _"  
  
  
lemma hn_unat_ops[sepref_fr_rules]:
  "(uncurry ll_add, uncurry (RETURN \<circ>\<circ> (+))) \<in> [\<lambda>(a, b). a + b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(uncurry ll_sub, uncurry (RETURN \<circ>\<circ> (-))) \<in> [\<lambda>(a, b). b \<le> a]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_mul, uncurry (RETURN \<circ>\<circ> (*))) \<in> [\<lambda>(a, b). a * b < max_unat LENGTH('a)]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn' TYPE('a::len)"
  "(uncurry ll_udiv, uncurry (RETURN \<circ>\<circ> (div))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  "(uncurry ll_urem, uncurry (RETURN \<circ>\<circ> (mod))) \<in> [\<lambda>(a, b). b \<noteq> 0]\<^sub>a unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow> unat_assn"
  
  "(uncurry ll_and, uncurry (RETURN \<circ>\<circ> (AND))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_or, uncurry (RETURN \<circ>\<circ> (OR))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  "(uncurry ll_xor, uncurry (RETURN \<circ>\<circ> (XOR))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a unat_assn"
  
  "(uncurry ll_icmp_eq, uncurry (RETURN \<circ>\<circ> (=))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ne, uncurry (RETURN \<circ>\<circ> (op_neq))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ule, uncurry (RETURN \<circ>\<circ> (\<le>))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
  "(uncurry ll_icmp_ult, uncurry (RETURN \<circ>\<circ> (<))) \<in> unat_assn\<^sup>k *\<^sub>a unat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"  
  unfolding op_neq_def
  
  using unat_bin_ops[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_bin_ops_bitwise[THEN unat.hn_bin_op, folded unat_rel_def]
    and unat_cmp_ops[THEN unat.hn_cmp_op, folded unat_rel_def bool1_rel_def]
  by (simp_all add: prod_casesK)
  
definition [simp]: "unat_init TYPE('a::len) \<equiv> 0::nat"

lemma is_init_unat[sepref_gen_algo_rules]:
  "GEN_ALGO (unat_init TYPE('a::len)) (is_init (unat_assn' TYPE('a)))"
  unfolding GEN_ALGO_def unat_init_def is_init_def
  unfolding unat_rel_def unat.rel_def
  by (simp add: in_br_conv)
  
lemma is_init_unat0[sepref_gen_algo_rules]: 
  "GEN_ALGO (unat_const TYPE('a::len2) 0) (is_init (unat_assn' TYPE('a)))"
  using is_init_unat[where 'a='a]
  by simp
  
  
subsubsection \<open>Ad-Hoc Method to Annotate Number Constructors\<close>  
(* TODO: Use same set of cong-=lemmas in all annot-methods, to avoid double-annot *)
lemma annot_num_const_cong_unat: 
  "\<And>a b. unat_const a b = unat_const a b" 
  by simp_all
  
lemma unat_const_fold: 
  "0 = unat_const TYPE('a::len) 0"
  "1 = unat_const TYPE('a::len) 1"
  "numeral n = unat_const TYPE('a::len) (numeral n)"
  by simp_all
    
method annot_unat_const for T::"'a::len itself" = 
  (simp only: unat_const_fold[where 'a='a] cong: annot_num_const_cong annot_num_const_cong_unat)


lemma upcast_no_msb[simp]: "LENGTH('small::len) < LENGTH('big::len) \<Longrightarrow> \<not>msb (UCAST('small \<rightarrow> 'big) x)" 
  apply (clarsimp simp: ucast_def msb_word_of_int)
  apply transfer
  using nth_bintr by auto
context begin
  interpretation llvm_prim_arith_setup .

  
definition [llvm_inline]: "unat_snat_upcast TYPE('a::len2) x \<equiv> ll_zext x TYPE('a word)"
  
lemma unat_snat_upcast_rule[vcg_rules]:
  "llvm_htriple 
    (\<up>(is_up' UCAST('small \<rightarrow> 'big)) ** \<upharpoonleft>unat.assn n (ni::'small::len word)) 
    (unat_snat_upcast TYPE('big::len2) ni) 
    (\<lambda>r. \<upharpoonleft>snat.assn n r)"
  unfolding unat.assn_def snat.assn_def unat_snat_upcast_def
  apply vcg'
  apply (auto simp: snat_invar_def snat_eq_unat(2) unat_ucast_upcast)
  done

context fixes T :: "'a::len2 itself" begin
  definition [simp]: "unat_snat_upcast_aux \<equiv> let _=TYPE('a) in id::nat\<Rightarrow>nat"

  sepref_decl_op unat_snat_upcast: "unat_snat_upcast_aux" :: "nat_rel \<rightarrow> nat_rel"
   .
end  

term mop_unat_snat_upcast

lemma in_unat_rel_conv_assn: "\<up>((xi, x) \<in> unat_rel) = \<upharpoonleft>unat.assn x xi"
  by (auto simp: unat_rel_def unat.assn_is_rel pure_app_eq)

lemma in_snat_rel_conv_assn: "\<up>((xi, x) \<in> snat_rel) = \<upharpoonleft>snat.assn x xi"
  by (auto simp: snat_rel_def snat.assn_is_rel pure_app_eq)

lemma unat_snat_upcast_rl[sepref_fr_rules]: 
  "(unat_snat_upcast TYPE('big::len2), PR_CONST (mop_unat_snat_upcast TYPE('big::len2))) \<in> [\<lambda>_. is_up' UCAST('small \<rightarrow> 'big)]\<^sub>a (unat_assn' TYPE('small::len))\<^sup>k \<rightarrow> snat_assn"
  supply [simp] = in_unat_rel_conv_assn in_snat_rel_conv_assn
  apply sepref_to_hoare
  apply simp
  by vcg'


end

xxx, ctd here: Define unat_snat_cast, with same length, if source is small enough!



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
