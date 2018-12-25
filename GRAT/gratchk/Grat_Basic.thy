section \<open>Basic Notions for the GRAT Format\<close>
theory Grat_Basic
imports 
  Unit_Propagation
  "Refine_Imperative_HOL.Sepref_ICF_Bindings" 
  Exc_Nres_Monad
  DRAT_Misc
  Synth_Definition
  Dynamic_Array 
  Array_Map_Default 
  Parser_Iterator
  DRAT_Misc
  "Automatic_Refinement.Misc"
begin

hide_const (open) Word.slice

(*

(* TODO: Move, patch Imperative/HOL! 
  This patch makes Imperative/HOL array translation also work for index types other than IntInf.
  Note that the toInt-operations are required to raise an Overflow exception on overflow, such that
  creating an array of too big size is safe, and also indexing an array out of bounds will be 
  correctly caught.
*)
code_printing constant Array.new' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ (IntInf.toInt _,/ (_)))"
code_printing constant Array.make' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ (IntInf.toInt _,/ _ o IntInf.fromInt))"
code_printing constant Array.len' \<rightharpoonup> (SML) "(fn/ ()/ =>/ IntInf.fromInt (Array.length/ _))"
code_printing constant Array.nth' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ IntInf.toInt _))"
code_printing constant Array.upd' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ IntInf.toInt _,/ (_)))"
  
  
(*
  TODO: Patch that belongs to array_blit.thy. 
  Already in Lammich's local AFP copy!
*)  
code_printing code_module "array_blit" \<rightharpoonup> (SML)
  {*
  (* Locally patched version  *)
  fun array_blit src si dst di len = (
    src=dst andalso raise Fail ("array_blit: Same arrays");
    ArraySlice.copy {
      di = IntInf.toInt di,
      src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
      dst = dst})

  fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
  fun array_upd_oo f i x a () = 
    (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

  *}

  (* TODO: Export to other languages: OCaml, Haskell, Scala *)
code_printing constant blit' \<rightharpoonup>
  (SML) "(fn/ ()/ => /array'_blit _ _ _ _ _)"
  and (Scala) "{ ('_: Unit)/=>/
    def safecopy(src: Array['_], srci: Int, dst: Array['_], dsti: Int, len: Int) = {
      if (src eq dst)
        sys.error(\"array'_blit: Same arrays\")
      else
        System.arraycopy(src, srci, dst, dsti, len)
    }
    safecopy(_.array,_.toInt,_.array,_.toInt,_.toInt)
  }"
  
  
  
  
*)  
  
  
(* TODO: Move *)
lemma list_set_assn_finite[simp, intro]: 
  "\<lbrakk>rdomp (list_set_assn (pure R)) s; single_valued R\<rbrakk> \<Longrightarrow> finite s"
  by (auto simp: rdomp_def list_set_assn_def elim!: finite_set_rel_transfer)
  
    
(* TODO: Move, and give a name to the rule "GEN_ALGO (return) (IS_TO_SORTED_LIST (\<lambda>_ _. True) (pure (\<langle>A\<rangle>list_set_rel)) (pure A))" *)
lemma list_set_assn_IS_TO_SORTED_LIST_GA'[sepref_gen_algo_rules]: 
  "\<lbrakk>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; 
    CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A \<rbrakk>
  \<Longrightarrow> GEN_ALGO (return) (IS_TO_SORTED_LIST (\<lambda>_ _. True) (list_set_assn A) A)"
  apply (clarsimp simp: is_pure_conv list_set_assn_def 
      list_assn_pure_conv IS_PURE_def list_set_rel_compp)
  apply (rule sepref_gen_algo_rules) (* FIXME: Using unnamed rule that happens to be in this set! *)
  done

subsection \<open>Input Parser\<close>    
       
locale input_pre =   
  iterator it_invar' it_next it_peek 
    for it_invar' it_next and it_peek :: "'it::linorder \<Rightarrow> int" +
  fixes
    it_end :: 'it
    
begin
  definition "it_invar it \<equiv> itran it it_end"
  lemma it_invar_imp'[simp, intro]: "it_invar it \<Longrightarrow> it_invar' it" 
    unfolding it_invar_def by auto
  lemma it_invar_imp_ran[simp, intro]: "it_invar it \<Longrightarrow> itran it it_end" 
    unfolding it_invar_def by auto
  lemma itran_invarD: "itran it it_end \<Longrightarrow> it_invar it" 
    unfolding it_invar_def by auto
  lemma itran_invarI: "\<lbrakk>itran it it'; it_invar it'\<rbrakk> \<Longrightarrow> it_invar it"    
    unfolding it_invar_def by (blast intro: itran_trans)
      
      
end
    
type_synonym 'it error = "String.literal \<times> int option \<times> 'it option"
  
  
locale input = input_pre it_invar' it_next it_peek it_end 
  for it_invar'::"'it::linorder \<Rightarrow> _" and it_next it_peek it_end +
  assumes    
    it_end_invar[simp, intro!]: "it_invar it_end"
begin    
  
  definition "WF \<equiv> { (it_next it, it) | it. it_invar it \<and> it \<noteq> it_end}"
  lemma wf_WF[simp, intro!]: "wf WF"  
    apply (rule wf_subset[of "measure (\<lambda>it. length (the_seg it it_end))"])
    unfolding it_invar_def WF_def  
    by (auto)
  
  lemmas wf_WF_trancl[simp, intro!] = wf_trancl[OF wf_WF]    
      
  lemma it_next_invar[simp, intro!]: 
    "\<lbrakk> it_invar it; it \<noteq> it_end \<rbrakk> \<Longrightarrow> it_invar (it_next it)"  
    unfolding it_invar_def by auto  
    
  lemma it_next_wf[simp, intro]: 
    "\<lbrakk> it_invar it; it \<noteq> it_end \<rbrakk> \<Longrightarrow> (it_next it, it) \<in> WF"
    unfolding WF_def by auto
    
  lemma seg_wf[simp, intro]: "\<lbrakk>seg it l it'; it_invar it'\<rbrakk> \<Longrightarrow> (it',it)\<in>WF\<^sup>*"
    apply (induction l arbitrary: it)
    apply auto
    by (metis it_invar_def it_next_wf itran_antisym itran_def itran_next 
        itran_trans rtrancl.intros(1) rtrancl.intros(2))
      
  lemma lz_string_wf[simp, intro]: 
    "\<lbrakk>lz_string 0 it l ita; it_invar ita\<rbrakk> \<Longrightarrow> (ita, it) \<in> WF\<^sup>+" 
    unfolding lz_string_def
    apply auto  
    by (metis input_pre.it_invar_def input_pre_axioms it_next_wf itran_def 
        itran_next rtrancl_into_trancl2 seg_invar2 seg_no_cyc seg_wf)
      
  text \<open>Some abbreviations to conveniently construct error messages. \<close>    
  abbreviation mk_err :: "String.literal \<Rightarrow> 'it error" 
    where "mk_err msg \<equiv> (msg, None, None)"
  abbreviation mk_errN :: "String.literal \<Rightarrow> _ \<Rightarrow> 'it error" 
    where "mk_errN msg n \<equiv> (msg, Some (int n), None)"
  abbreviation mk_errI :: "_ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errI msg i \<equiv> (msg, Some i, None)"
  abbreviation mk_errit :: "_ \<Rightarrow> _ \<Rightarrow> 'it error" 
    where "mk_errit msg it \<equiv> (msg, None, Some it)"
  abbreviation mk_errNit :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errNit msg n it \<equiv> (msg, Some (int n), Some it)"
  abbreviation mk_errIit :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errIit msg i it \<equiv> (msg, Some i, Some it)"
  
  
      
  text \<open>Check that iterator has not reached the end.\<close>    
  definition "check_not_end it 
    \<equiv> CHECK (it \<noteq> it_end) (mk_err STR ''Parsed beyond end'')"
    
  lemma check_not_end_correct[THEN ESPEC_trans, refine_vcg]: 
    "it_invar it \<Longrightarrow> check_not_end it \<le> ESPEC (\<lambda>_. True) (\<lambda>_. it \<noteq> it_end)"
    unfolding check_not_end_def by (refine_vcg; auto)
  
  text \<open>Skip one element.\<close>    
  definition "skip it \<equiv> doE {
    EASSERT (it_invar it); 
    check_not_end it; 
    ERETURN (it_next it)
  }"
    
  text \<open>Read a literal\<close>  
  definition "parse_literal it \<equiv> doE {
    EASSERT(it_invar it \<and> it \<noteq> it_end \<and> it_peek it \<noteq> litZ ); 
    ERETURN (lit_\<alpha> (it_peek it), it_next it)
  }"
    
  text \<open>Read an integer\<close>  
  definition "parse_int it \<equiv> doE {
    EASSERT (it_invar it); 
    check_not_end it; 
    ERETURN (it_peek it, it_next it)
  }"
    
  text \<open>Read a natural number\<close>    
  definition "parse_nat it\<^sub>0 \<equiv> doE {
    (x,it) \<leftarrow> parse_int it\<^sub>0;
    CHECK (x\<ge>0) (mk_errIit STR ''Invalid nat'' x it\<^sub>0);
    ERETURN (nat x,it)
  }"  
    
  lemma parse_literal_spec[THEN ESPEC_trans,refine_vcg]: 
    "\<lbrakk>it_invar it; it \<noteq> it_end; it_peek it \<noteq> litZ\<rbrakk> 
    \<Longrightarrow> parse_literal it 
      \<le> ESPEC (\<lambda>_. True) (\<lambda>(l,it'). it_invar it' \<and> (it',it)\<in>WF\<^sup>+)"
    unfolding parse_literal_def 
    by refine_vcg auto  

  lemma skip_spec[THEN ESPEC_trans,refine_vcg]: 
    "\<lbrakk>it_invar it\<rbrakk> 
    \<Longrightarrow> skip it \<le> ESPEC (\<lambda>_. True) (\<lambda>it'. it_invar it' \<and> (it',it)\<in>WF\<^sup>+)"
    unfolding skip_def 
    by refine_vcg auto  
      
  lemma parse_int_spec[THEN ESPEC_trans,refine_vcg]: 
    "\<lbrakk>it_invar it\<rbrakk> 
    \<Longrightarrow> parse_int it \<le> ESPEC (\<lambda>_. True) (\<lambda>(x,it'). it_invar it' \<and> (it',it)\<in>WF\<^sup>+)"
    unfolding parse_int_def 
    by refine_vcg auto  

  lemma parse_nat_spec[THEN ESPEC_trans,refine_vcg]: 
    "\<lbrakk>it_invar it\<rbrakk> 
    \<Longrightarrow> parse_nat it \<le> ESPEC (\<lambda>_. True) (\<lambda>(x,it'). it_invar it' \<and> (it',it)\<in>WF\<^sup>+)"
    unfolding parse_nat_def 
    by refine_vcg auto  

      
  text \<open>We inline many of the specifications on breaking down the exception monad\<close>    
  lemmas [enres_inline] = check_not_end_def skip_def parse_literal_def 
    parse_int_def parse_nat_def
      
end  
  
  
subsection \<open>Implementation\<close>  
subsubsection \<open>Literals\<close>  
definition "lit_rel \<equiv> br lit_\<alpha> lit_invar"
abbreviation "lit_assn \<equiv> pure lit_rel"

    
    

interpretation lit_dflt_option: dflt_option "pure lit_rel" 0 "return oo (=)"
  apply standard
  subgoal by (auto simp: lit_rel_def in_br_conv lit_invar_def)
  subgoal
    apply sepref_to_hoare
    apply (sep_auto simp: lit_rel_def lit_\<alpha>_def in_br_conv)
    done
  applyS sep_auto
  done

lemma neg_lit_refine[sepref_import_param]: 
  "(uminus, neg_lit) \<in> lit_rel \<rightarrow> lit_rel"
  by (auto simp: lit_rel_def in_br_conv lit_\<alpha>_def lit_invar_def)

lemma lit_\<alpha>_refine[sepref_import_param]: 
  "(\<lambda>x. x, lit_\<alpha>) \<in> [\<lambda>x. x\<noteq>0]\<^sub>f int_rel \<rightarrow> lit_rel"    
  by (auto simp: lit_rel_def lit_invar_def in_br_conv intro!: frefI)
  
  
subsubsection \<open>Assignment\<close>

definition "vv_rel \<equiv> {(1::nat, False), (2, True)}"

definition "assignment_assn \<equiv> amd_assn 0 id_assn (pure vv_rel)"
lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "assignment_assn"]
type_synonym i_assignment = "(nat,bool) i_map"

lemmas [intf_of_assn] 
  = intf_of_assnI[where R="assignment_assn" and 'a="(nat,bool) i_map"]

sepref_decl_op lit_is_true: "\<lambda>(l::nat literal) A. sem_lit' l A = Some True" 
  :: "(Id::(nat literal\<times>_) set) \<rightarrow> \<langle>nat_rel,bool_rel\<rangle>map_rel \<rightarrow> bool_rel" .   
  (* TODO: Should we really declare map_rel here. This only causes trouble later. *)

sepref_decl_op lit_is_false: "\<lambda>(l::nat literal) A. sem_lit' l A = Some False" 
  :: "(Id::(nat literal\<times>_) set) \<rightarrow> \<langle>nat_rel,bool_rel\<rangle>map_rel \<rightarrow> bool_rel" .

sepref_decl_op (no_def) 
  "assign_lit :: _ \<Rightarrow> nat literal \<Rightarrow> _" 
  :: "\<langle>nat_rel,bool_rel\<rangle>map_rel \<rightarrow> (Id::(nat literal\<times>_) set) 
      \<rightarrow> \<langle>nat_rel,bool_rel\<rangle>map_rel" .

sepref_decl_op 
  unset_lit: "\<lambda>(A::nat\<rightharpoonup>bool) l. A(var_of_lit l := None) " 
  :: "\<langle>nat_rel,bool_rel\<rangle>map_rel \<rightarrow> (Id::(nat literal\<times>_) set) 
      \<rightarrow> \<langle>nat_rel,bool_rel\<rangle>map_rel" .

lemma [def_pat_rules]:
  "(=)$(sem_lit'$l$A)$(Some$True) \<equiv> op_lit_is_true$l$A"
  "(=)$(sem_lit'$l$A)$(Some$False) \<equiv> op_lit_is_false$l$A"
  by auto

lemma lit_eq_impl[sepref_import_param]: 
  "((=),(=)) \<in> lit_rel \<rightarrow> lit_rel \<rightarrow> bool_rel"
  by (auto 
        simp: lit_rel_def in_br_conv lit_\<alpha>_def lit_invar_def 
        split: if_split_asm)

lemma var_of_lit_refine[sepref_import_param]: 
  "(nat o abs,var_of_lit) \<in> lit_rel \<rightarrow> nat_rel"
  by (auto simp: lit_rel_def lit_\<alpha>_def in_br_conv)

lemma is_pos_refine[sepref_import_param]: 
  "(\<lambda>x. x>0, is_pos) \<in> lit_rel \<rightarrow> bool_rel"
  by (auto 
        simp: lit_rel_def lit_\<alpha>_def in_br_conv lit_invar_def 
        split: if_split_asm)

lemma op_lit_is_true_alt: "op_lit_is_true l A = (let
    x = A (var_of_lit l);
    p = is_pos l
  in 
    if x = None then False
    else (p \<and> the x = True \<or> \<not>p \<and> the x = False)
  )"
  apply (cases l)
  by (auto split: option.split simp: Let_def)

lemma op_lit_is_false_alt: "op_lit_is_false l A = (let
    x = A (var_of_lit l);
    p = is_pos l
  in 
    if x = None then False
    else (p \<and> the x = False \<or> \<not>p \<and> the x = True)
  )"
  apply (cases l)
  by (auto split: option.split simp: Let_def)


definition [simp,code_unfold]: "vv_eq_bool x y \<equiv> y\<longleftrightarrow>x=2"

lemma [sepref_opt_simps]: 
  "vv_eq_bool x True \<longleftrightarrow> x=2" 
  "vv_eq_bool x False \<longleftrightarrow> x\<noteq>2" 
  by simp_all

lemma vv_bool_eq_refine[sepref_import_param]: 
  "(vv_eq_bool, (=)) \<in> vv_rel \<rightarrow> bool_rel \<rightarrow> bool_rel"
  by (auto simp: vv_rel_def)

sepref_definition op_lit_is_true_impl is "uncurry (RETURN oo op_lit_is_true)" 
  :: "(pure lit_rel)\<^sup>k *\<^sub>a assignment_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding op_lit_is_true_alt assignment_assn_def
  supply option.splits[split]
  by sepref

sepref_definition op_lit_is_false_impl is "uncurry (RETURN oo op_lit_is_false)" 
  :: "(pure lit_rel)\<^sup>k *\<^sub>a assignment_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding op_lit_is_false_alt assignment_assn_def
  supply option.splits[split]
  by sepref

definition [simp]: "b2vv_conv b \<equiv> b"
definition [code_unfold]: "b2vv_conv_impl b \<equiv> if b then 2 else 1::nat"

lemma b2vv_conv_impl_refine[sepref_import_param]: 
  "(b2vv_conv_impl,b2vv_conv) \<in> bool_rel \<rightarrow> vv_rel"
  by (auto simp: vv_rel_def b2vv_conv_impl_def split: if_split_asm)

lemma vv_unused0[safe_constraint_rules]: "(is_unused_elem 0) (pure vv_rel)"
  by (auto simp: vv_rel_def)


sepref_definition assign_lit_impl 
  is "uncurry (RETURN oo assign_lit)" 
      :: "assignment_assn\<^sup>d *\<^sub>a (pure lit_rel)\<^sup>k \<rightarrow>\<^sub>a assignment_assn"
  unfolding assign_lit_def assignment_assn_def
  apply (rewrite at "is_pos _" b2vv_conv_def[symmetric])
  by sepref  

term op_unset_lit
sepref_definition unset_lit_impl 
  is "uncurry (RETURN oo op_unset_lit)" 
      :: "assignment_assn\<^sup>d *\<^sub>a (pure lit_rel)\<^sup>k \<rightarrow>\<^sub>a assignment_assn"
  unfolding op_unset_lit_def assignment_assn_def
  by sepref  

sepref_definition unset_var_impl 
  is "uncurry (RETURN oo op_map_delete)" 
      :: "(pure nat_rel)\<^sup>k *\<^sub>a assignment_assn\<^sup>d \<rightarrow>\<^sub>a assignment_assn"
  unfolding assignment_assn_def
  by sepref  

sepref_definition assignment_empty_impl is "uncurry0 (RETURN op_map_empty)"  
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a assignment_assn"
  unfolding assignment_assn_def
  apply (rewrite amd.fold_custom_empty)  
  by sepref  
    
lemma assignment_assn_id_map_rel_fold: 
  "hr_comp assignment_assn (\<langle>nat_rel, bool_rel\<rangle>map_rel) = assignment_assn" 
  by simp

context
  notes [fcomp_norm_unfold] = assignment_assn_id_map_rel_fold
begin
  sepref_decl_impl op_lit_is_true_impl.refine .
  sepref_decl_impl op_lit_is_false_impl.refine .
  sepref_decl_impl assign_lit_impl.refine .
  sepref_decl_impl unset_lit_impl.refine .
  sepref_decl_impl unset_var_impl.refine 
    uses op_map_delete.fref[where K=Id and V=Id] .
  sepref_decl_impl (no_register) assignment_empty: assignment_empty_impl.refine 
    uses op_map_empty.fref[where K=Id and V=Id] .
end

definition [simp]: "op_assignment_empty \<equiv> op_map_empty"
interpretation assignment: map_custom_empty op_assignment_empty 
  by unfold_locales simp
lemmas [sepref_fr_rules] = assignment_empty_hnr[folded op_assignment_empty_def]
  
subsubsection \<open>Clause Database\<close>
type_synonym clausedb2 = "int list"

locale DB2_def_loc =   
  fixes DB :: clausedb2
  fixes frml_end :: nat
begin
  lemmas amtx_pats[pat_rules del] (* Get this out of the way for better id-op-debugging! *)
  sublocale liti: array_iterator DB .
  
  lemmas liti.a_assn_rdompD[dest!]
      
  abbreviation "error_assn 
    \<equiv> id_assn \<times>\<^sub>a option_assn int_assn \<times>\<^sub>a option_assn liti.it_assn"
  
end  

locale DB2_loc = DB2_def_loc +  
  assumes DB_not_Nil[simp]: "DB \<noteq> []"
begin
  sublocale input_pre liti.I liti.next liti.peek liti.end
    by unfold_locales

  sublocale input liti.I liti.next liti.peek liti.end   
    apply unfold_locales
    unfolding it_invar_def liti.itran_alt 
    apply (auto simp: ait_begin_def ait_end_def)  
    done
  
end  
  
  
  
subsubsection \<open>Clausemap\<close>  

definition (in -) abs_cr_register 
:: "'a literal \<Rightarrow> 'id \<Rightarrow> ('a literal \<rightharpoonup> 'id list) \<Rightarrow> ('a literal \<rightharpoonup> 'id list)" 
where "abs_cr_register l cid cr \<equiv> case cr l of 
  None \<Rightarrow> cr | Some s \<Rightarrow> cr(l \<mapsto> mbhd_insert cid s)"



(* Hacking 'a literal \<rightharpoonup> 'id list by hand \<dots> 
  Operations:
    empty
    initialize l m = m(l\<mapsto>[])
    add l c m = if l\<in>dom m then m( l \<mapsto> insert c (m l))

    get l m = m l
*)

type_synonym creg = "(nat list option) array"

term int_encode term int_decode
term map_option


definition is_creg :: "(nat literal \<rightharpoonup> nat list) \<Rightarrow> creg \<Rightarrow> assn" where
  "is_creg cr a \<equiv> \<exists>\<^sub>Af. is_nff None f a 
  * \<up>(cr = f o int_encode o lit_\<gamma>)"

lemmas [intf_of_assn] 
  = intf_of_assnI[where R=is_creg and 'a="(nat literal,nat list) i_map"]
  
definition "creg_dflt_size \<equiv> 16::nat"
definition creg_empty :: "creg Heap" 
  where "creg_empty \<equiv> dyn_array_new_sz None creg_dflt_size"

lemma creg_empty_rule[sep_heap_rules]: "<emp> creg_empty <is_creg Map.empty>"
  unfolding creg_empty_def by (sep_auto simp: is_creg_def)
    
definition [simp]: "op_creg_empty \<equiv> op_map_empty :: nat literal \<rightharpoonup> nat list"
interpretation creg: map_custom_empty op_creg_empty by unfold_locales simp    
lemma creg_empty_hnr[sepref_fr_rules]: 
  "(uncurry0 creg_empty, uncurry0 (RETURN op_creg_empty)) 
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_creg"
  apply sepref_to_hoare
  apply sep_auto
  done  
    
definition creg_initialize :: "int \<Rightarrow> creg \<Rightarrow> creg Heap" where
  "creg_initialize l cr = do {
    cr \<leftarrow> array_set_dyn None cr (int_encode l) (Some []);
    return cr
  }"
  
lemma creg_initialize_rule[sep_heap_rules]: 
  "\<lbrakk> (i,l)\<in>lit_rel \<rbrakk> 
  \<Longrightarrow> <is_creg cr a> creg_initialize i a <\<lambda>r. is_creg (cr(l \<mapsto> [])) r>\<^sub>t"
  unfolding creg_initialize_def is_creg_def
  by (sep_auto intro!: ext simp: lit_rel_def in_br_conv int_encode_eq)

definition "creg_register l cid cr \<equiv> do {
  x \<leftarrow> array_get_dyn None cr (int_encode l);
  case x of
    None \<Rightarrow> return cr
  | Some s \<Rightarrow> array_set_dyn None cr (int_encode l) (Some (mbhd_insert cid s))
}"

lemma creg_register_rule[sep_heap_rules]: 
  "\<lbrakk> (i,l) \<in> lit_rel \<rbrakk> 
  \<Longrightarrow> <is_creg cr a> 
        creg_register i cid a 
      <is_creg (abs_cr_register l cid cr)>\<^sub>t"
  unfolding creg_register_def is_creg_def abs_cr_register_def
  by (sep_auto intro!: ext simp: lit_rel_def in_br_conv int_encode_eq)

lemma creg_register_hnr[sepref_fr_rules]: 
  "(uncurry2 creg_register, uncurry2 (RETURN ooo abs_cr_register)) 
    \<in> (pure lit_rel)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a is_creg\<^sup>d \<rightarrow>\<^sub>a is_creg"
  unfolding list_assn_pure_conv option_assn_pure_conv
  apply sepref_to_hoare
  apply sep_auto
  done

definition op_creg_initialize :: "nat literal \<Rightarrow> (nat literal \<rightharpoonup> nat list) \<Rightarrow> _"
  where [simp]: "op_creg_initialize l cr \<equiv> cr(l \<mapsto> [])"
    
lemma creg_initialize_hnr[sepref_fr_rules]: 
  "(uncurry creg_initialize, uncurry (RETURN oo op_creg_initialize)) 
  \<in> (pure lit_rel)\<^sup>k *\<^sub>a is_creg\<^sup>d \<rightarrow>\<^sub>a is_creg"
  apply sepref_to_hoare
  apply sep_auto
  done
    
sepref_register op_creg_initialize 
  :: "nat literal \<Rightarrow> (nat literal,nat list) i_map 
      \<Rightarrow> (nat literal,nat list) i_map"
    
sepref_register "abs_cr_register :: nat literal \<Rightarrow> nat \<Rightarrow> _" 
  :: "nat literal \<Rightarrow> nat \<Rightarrow> (nat literal,nat list) i_map 
      \<Rightarrow> (nat literal,nat list) i_map"
    
term op_map_lookup
definition "op_creg_lookup i a \<equiv> array_get_dyn None a (int_encode i)"


lemma creg_lookup_rule[sep_heap_rules]:
  "\<lbrakk> (i,l) \<in> lit_rel \<rbrakk> 
  \<Longrightarrow> <is_creg cr a> op_creg_lookup i a <\<lambda>r. is_creg cr a * \<up>( r = cr l)>"
  unfolding is_creg_def op_creg_lookup_def
  by (sep_auto intro!: ext simp: lit_rel_def in_br_conv)

lemma creg_lookup_hnr[sepref_fr_rules]: 
  "(uncurry op_creg_lookup, uncurry (RETURN oo op_map_lookup)) 
  \<in> (pure lit_rel)\<^sup>k *\<^sub>a is_creg\<^sup>k \<rightarrow>\<^sub>a option_assn (list_assn id_assn)"
  unfolding list_assn_pure_conv option_assn_pure_conv
  apply sepref_to_hoare
  apply sep_auto
  done

    
subsubsection \<open>Clause Database\<close>

context   
  fixes DB :: clausedb2
  fixes frml_end :: nat
begin
  definition "item_next it \<equiv> 
    let sz = DB!(it-1) in
    if sz > 0 \<and> nat (sz) + 1 < it then
      Some (it - nat (sz) - 1)
    else 
      None
  "
  
  definition "at_item_end it \<equiv> it \<le> frml_end"

  definition "peek_int it \<equiv> DB!it"
end
  
context DB2_def_loc
begin
  abbreviation "cm_assn \<equiv> prod_assn (amd_assn 0 nat_assn liti.it_assn) is_creg"
  type_synonym i_cm = "(nat,nat) i_map \<times> (nat literal, nat list) i_map"
      
  abbreviation "state_assn \<equiv> nat_assn \<times>\<^sub>a cm_assn \<times>\<^sub>a assignment_assn"
  type_synonym i_state = "nat \<times> i_cm \<times> i_assignment"  
   
    
  definition "item_next_impl a it \<equiv> do {
    sz \<leftarrow> Array.nth a (it-1);
    if sz > 0 \<and> nat (sz) + 1 < it then
      return (it - nat (sz) - 1)
    else 
      return 0
  }"
      
  lemma item_next_hnr[sepref_fr_rules]: 
    "(uncurry item_next_impl, uncurry (RETURN oo item_next)) 
    \<in> liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k \<rightarrow>\<^sub>a dflt_option_assn 0 liti.it_assn"  
    unfolding liti.it_assn_def liti.a_assn_def dflt_option_assn_def
    apply (simp add: b_assn_pure_conv)  
    apply (sepref_to_hoare)
    unfolding item_next_impl_def
    by (sep_auto simp: liti.I_def item_next_def dflt_option_rel_aux_def)  

  lemma at_item_end_hnr[sepref_fr_rules]: 
    "(uncurry (return oo at_item_end), uncurry (RETURN oo at_item_end)) 
    \<in> nat_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding liti.it_assn_def liti.a_assn_def dflt_option_assn_def
    apply (simp add: b_assn_pure_conv)  
    apply (sepref_to_hoare)
    apply sep_auto
    done  
    
      
    
end  

  
subsection \<open>Common GRAT Stuff\<close>  
datatype item_type = 
    INVALID 
  | UNIT_PROP 
  | DELETION 
  | RUP_LEMMA 
  | RAT_LEMMA 
  | CONFLICT 
  | RAT_COUNTS
  
type_synonym id = nat
  
subsubsection \<open>Clause Map\<close>
(* TODO: Add more common stuff from Unsat_Check and Unsat_Check_Split *)  
  
  
subsubsection \<open>Correctness\<close>  
text \<open>
  The input to the verified part of the checker is an array of integers @{term DB}
  and an index @{term F_end}, such that the range from index @{term 1} (inclusive) 
  to index @{term F_end} (exclusive) contains the formula in DIMACs format.
  
  The array is represented as a list here.
  
  We phrase an invariant that expressed a valid formula, and a characterization
  whether the represented formula is satisfiable. 
\<close>  

definition "clause_DB_valid DB F_end \<equiv> 
    1 \<le> F_end \<and> F_end \<le> length DB
  \<and> F_invar (tl (take F_end DB))"

definition "clause_DB_sat DB F_end \<equiv> sat (F_\<alpha> (tl (take F_end DB)))"

definition "verify_sat_spec DB F_end 
  \<equiv> clause_DB_valid DB F_end \<and> clause_DB_sat DB F_end"
    
definition "verify_unsat_spec DB F_end 
  \<equiv> clause_DB_valid DB F_end \<and> \<not>clause_DB_sat DB F_end"
  
lemma "verify_sat_spec DB F_end \<longleftrightarrow> 1 \<le> F_end \<and> F_end \<le> length DB \<and>
  (let lst = tl (take F_end DB) in F_invar lst \<and> sat (F_\<alpha> lst))"
  unfolding verify_sat_spec_def clause_DB_valid_def clause_DB_sat_def Let_def
  by auto
  
lemma "verify_unsat_spec DB F_end \<longleftrightarrow> 1 \<le> F_end \<and> F_end \<le> length DB \<and>
  (let lst = tl (take F_end DB) in F_invar lst \<and> \<not>sat (F_\<alpha> lst))"
  unfolding verify_unsat_spec_def clause_DB_valid_def clause_DB_sat_def Let_def
  by auto

text \<open>Concise version only using elementary list operations\<close>
lemma clause_DB_valid_concise: "clause_DB_valid DB F_end \<equiv> 
    1 \<le> F_end \<and> F_end \<le> length DB
  \<and> (let lst=tl (take F_end DB) in lst \<noteq>[] \<longrightarrow> last lst = 0)"
  apply (rule eq_reflection)
  unfolding clause_DB_valid_def F_invar_def
  by auto
  
lemma clause_DB_sat_concise:
  "clause_DB_sat DB F_end \<equiv> \<exists>\<sigma>. assn_consistent \<sigma> 
    \<and> (\<forall>C\<in>set ` set (tokenize 0 (tl (take F_end DB))). \<exists>l\<in>C. \<sigma> l)"
  using clause_DB_sat_def
  unfolding direct_sat_iff_sat[symmetric] direct_sat_def parse_direct_def
  by auto


text \<open>
  The input describes a satisfiable formula, iff @{term F_end} is in range,
  the described DIMACS string is empty or ends with zero,
  and there exists a consistent assignment such that each clause contains a
  literal assigned to true. 
\<close>    
lemma verify_sat_spec_concise:
  shows "verify_sat_spec DB F_end \<equiv> 1\<le>F_end \<and> F_end \<le> length DB \<and> (
    let lst = tl (take F_end DB) in 
      (lst\<noteq>[] \<longrightarrow> last lst = 0)
    \<and> (\<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set (tokenize 0 lst). \<exists>l\<in>set C. \<sigma> l)))"
  unfolding verify_sat_spec_def clause_DB_sat_concise clause_DB_valid_concise
  by (simp add: Let_def)

text \<open>
  The input describes an unsatisfiable formula, iff @{term F_end} is in range
  and does not describe the empty DIMACS string, the DIMACS string ends 
  with zero, and there exists no consistent assignment such that every clause
  contains at least one literal assigned to true.
\<close>    
lemma verify_unsat_spec_concise:
  "verify_unsat_spec DB F_end \<equiv> 1 < F_end \<and> F_end \<le> length DB \<and> (
    let lst = tl (take F_end DB) in 
       last lst = 0
    \<and> (\<nexists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set (tokenize 0 lst). \<exists>l\<in>set C. \<sigma> l)))"
  unfolding verify_unsat_spec_def clause_DB_sat_concise clause_DB_valid_concise
  apply (rule eq_reflection)
  apply (cases "F_end = 1")
  apply (auto simp add: Let_def tl_take)
  done
  
  
  
(*
text \<open>The first specification uses the abstraction function @{const F_\<alpha>}, 
  which, in turn, uses @{const tokenize} to read the list as list of 
  zero-terminated lists.
  It also specifies that the input list is either empty, or ends with 
  a zero.
\<close>  
definition "formula_unsat_spec DB F_end \<equiv> let lst = tl (take F_end DB) in
      F_end \<le> length DB \<and> F_end \<ge> 1
    \<and> (F_end > 1 \<longrightarrow> last lst = 0)
    \<and> \<not>sat (F_\<alpha> lst)"
  
text \<open>The second specification specifies that the input can be obtained 
  by mapping the literals to integers, and then concatenating the clauses, 
  appending a zero to each clause. It also specifies that the literals do not 
  contain a zero variable.
\<close>
definition "formula_unsat_spec' DB F_end \<equiv> 
  \<exists>lst. 
      F_end \<le> length DB \<and> F_end \<ge> 1 \<and> 0 \<notin> var_of_lit ` set (concat lst)
    \<and> concat_sep 0 (map (map lit_\<gamma>) lst) = tl (take F_end DB) 
    \<and> \<not>sat (set (map set lst))"

text \<open>We show both specifications to be equivalent\<close>  
lemma formula_unsat_spec_equiv: 
  "formula_unsat_spec' DB F_end \<longleftrightarrow> formula_unsat_spec DB F_end"
proof -
  {
    fix ll l
    assume EQ: "concat_sep 0 (map (map lit_\<gamma>) ll) = l"
    assume NZ: "0 \<notin> var_of_lit ` (\<Union>x\<in>set ll. set x)"
    have "set ` set ll = F_\<alpha> l"
    proof -    
      from NZ have 1: "0 \<notin> \<Union>set (map set (map (map lit_\<gamma>) ll))"
        apply (clarsimp simp: lit_\<gamma>_def var_of_lit_alt split: literal.splits)
        apply force+  
        done  
      
      show ?thesis
        unfolding EQ[symmetric] F_\<alpha>_def 
        apply (rewrite tokenize_concat_id[OF 1])
        unfolding clause_\<alpha>_def 
        proof (safe; clarsimp)
          fix lc
          assume A: "lc \<in> set ll"  
          
          from A have [simp]: "\<forall>l\<in>set lc. var_of_lit l \<noteq> 0" using NZ by auto
              
          have [simp]: "lit_\<alpha> ` lit_\<gamma> ` set lc = set lc"    
            by (force)
            
          from A have "((\<lambda>l. lit_\<alpha> ` set l) \<circ>\<circ> map) lit_\<gamma> lc 
            \<in> ((\<lambda>l. lit_\<alpha> ` set l) \<circ>\<circ> map) lit_\<gamma> ` set ll" 
            by blast
          also have "((\<lambda>l. lit_\<alpha> ` set l) \<circ>\<circ> map) lit_\<gamma> lc = set lc" by auto
          finally show "set lc \<in> ((\<lambda>l. lit_\<alpha> ` set l) \<circ>\<circ> map) lit_\<gamma> ` set ll" .
          from A show "lit_\<alpha> ` lit_\<gamma> ` set lc \<in> set ` set ll" by auto
        qed
    qed      
  } note AUX = this
    
  show ?thesis  
    unfolding formula_unsat_spec'_def formula_unsat_spec_def
    apply (rule iffI)
    subgoal by (auto simp: Let_def AUX intro: concat_sep_last_sep)  
    subgoal    
      apply (rule exI[
              where x="(map (map lit_\<alpha>)) (tokenize litZ (tl (take F_end DB)))"])
      apply (clarsimp simp: Let_def tl_take; intro conjI)  
      subgoal using tokenize_complete_set by fastforce  
      subgoal 
        by (simp 
              add: map_map_lit_\<gamma>_\<alpha>_eq[OF tokenize_complete] concat_tokenize_id)  
      subgoal by (auto simp: F_\<alpha>_def clause_\<alpha>_def[abs_def] set_oo_map_alt)  
      done    
    done
qed    

subsubsection \<open>Alternative Correctness Statement\<close>  
text \<open>We also specify a correctness statement that uses only elementary
  concepts, in order to reduce the dependencies of the correctness statement.
\<close>  

(* TODO: Remove, when moved to DIMACS-Format *)

type_synonym assn = "int \<Rightarrow> bool"
definition assn_consistent :: "assn \<Rightarrow> bool" 
  where "assn_consistent \<sigma> = (\<forall>x. x\<noteq>0 \<longrightarrow> \<not> \<sigma> (-x) = \<sigma> x)"
definition "alt_sat F \<equiv> \<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set F. \<exists>l\<in>set C. \<sigma> l)"
  
lemma alt_sat_Nil[simp]: "alt_sat []" 
  unfolding alt_sat_def 
  apply (rule exI[where x = "\<lambda>x::int. x>0"])  
  unfolding assn_consistent_def 
  by auto  
    
    
  
(* TODO: Move *)  
lemma lit_\<alpha>_uminus_conv[simp]: "x\<noteq>0 \<Longrightarrow> lit_\<alpha> (-x) = neg_lit (lit_\<alpha> x)" 
  unfolding lit_\<alpha>_def by auto
  
lemma tl_take_Suc[simp]: "tl (take (Suc 0) l) = []" by (cases l) auto   
    
lemma alt_sat_sat_eq:
  assumes "0 \<notin>\<Union>set (map set F)"  
  shows "sat (clause_\<alpha> ` set F) \<longleftrightarrow> alt_sat F"
  unfolding sat_def alt_sat_def sem_cnf_def
proof (safe; clarsimp)
  fix \<sigma>
  assume A: "\<forall>C\<in>set F. sem_clause (clause_\<alpha> C) \<sigma>"  
  let ?a = "\<lambda>i. sem_lit (lit_\<alpha> i) \<sigma>"
    
  have "assn_consistent ?a"  
    unfolding assn_consistent_def by auto  
  moreover have "\<forall>C\<in>set F. \<exists>l\<in>set C. ?a l"
    using A by (auto simp: sem_clause_def clause_\<alpha>_def)
  ultimately show "\<exists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set F. \<exists>l\<in>set C. \<sigma> l)" by blast
next
  fix a
  assume CONS: "assn_consistent a" and SAT: "\<forall>C\<in>set F. \<exists>l\<in>set C. a l"  

  let ?\<sigma> = "a o int"  
    
  have [simp]: "sem_lit (lit_\<alpha> x) (a \<circ> int) = a x" for x using CONS
    unfolding lit_\<alpha>_def assn_consistent_def by auto
    
  from SAT have "\<forall>C\<in>set F. sem_clause (clause_\<alpha> C) ?\<sigma>"
    by (auto simp: sem_clause_def clause_\<alpha>_def)
  thus "\<exists>\<sigma>. \<forall>C\<in>set F. sem_clause (clause_\<alpha> C) \<sigma>" by blast
qed    
  
lemma formula_unsat_spec_alt: 
  "formula_unsat_spec DB F_end \<longleftrightarrow> (let lst = tl (take F_end DB) in
    1 < F_end \<and> F_end \<le> length DB \<and> last lst = 0 \<and> \<not>alt_sat (tokenize 0 lst))"  
  unfolding formula_unsat_spec_def
  by (cases "F_end = Suc 0") 
     (auto simp: Let_def F_\<alpha>_def alt_sat_sat_eq[OF tokenize_complete]) 
  
lemma formula_unsat_spec_alt': "formula_unsat_spec DB F_end \<longleftrightarrow> (
  let lst = tl (take F_end DB) in
    1 < F_end \<and> F_end \<le> length DB \<and> last lst = 0 
    \<and> (\<nexists>\<sigma>. assn_consistent \<sigma> \<and> (\<forall>C\<in>set (tokenize 0 lst). \<exists>l\<in>set C. \<sigma> l)))"
  unfolding formula_unsat_spec_alt 
  unfolding alt_sat_def 
  by auto  
  
*)  
  
end
