section \<open>Basic Notions for the GRAT Format\<close>
theory Grat_Basic
imports 
  Unit_Propagation 
  DRAT_Misc 
  "$AFP/Refine_Imperative_HOL/Sepref_ICF_Bindings" 
  Exc_Nres_Monad
  Synth_Definition 
  Dynamic_Array 
  Array_Map_Default 
  Parser_Iterator_New
begin

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

subsection \<open>Encoding of Literals and Clauses\<close>  
type_synonym var = nat  
  
abbreviation (input) litZ :: int where "litZ \<equiv> 0"
  
definition lit_\<alpha> :: "int \<Rightarrow> nat literal" 
  where "lit_\<alpha> l \<equiv> if l<0 then Neg (nat (-l)) else Pos (nat l)"
definition lit_invar :: "int \<Rightarrow> bool" 
  where "lit_invar l \<equiv> l\<noteq>0"
    
definition "clause_\<alpha> l \<equiv> lit_\<alpha>`set l"
  
lemma clause_\<alpha>_empty[simp]: "clause_\<alpha> [] = {}" 
  unfolding clause_\<alpha>_def by auto
lemma clause_\<alpha>_cons[simp]: "clause_\<alpha> (x#l) = insert (lit_\<alpha> x) (clause_\<alpha> l)" 
  unfolding clause_\<alpha>_def by auto
lemma clause_\<alpha>_conc[simp]: "clause_\<alpha> (l1@l2) = clause_\<alpha> l1 \<union> clause_\<alpha> l2" 
  unfolding clause_\<alpha>_def by auto

definition "F_\<alpha> lst \<equiv> set (map clause_\<alpha> (tokenize litZ lst))"
definition "F_invar lst \<equiv> lst\<noteq>[] \<longrightarrow> last lst = litZ"

lemma F_\<alpha>_empty[simp]: "F_\<alpha> [] = {}" unfolding F_\<alpha>_def by auto
    
definition "lit_\<gamma> l \<equiv> case l of Pos l \<Rightarrow> int l | Neg l \<Rightarrow> - int l"

lemma lit_\<gamma>_\<alpha>_inv[simp]: "lit_\<gamma> (lit_\<alpha> i) = i"
  unfolding lit_\<gamma>_def lit_\<alpha>_def by auto

lemma lit_\<alpha>_\<gamma>_inv[simp]: "lit_invar (lit_\<gamma> l) \<Longrightarrow> lit_\<alpha> (lit_\<gamma> l) = l"
  unfolding lit_\<gamma>_def lit_\<alpha>_def lit_invar_def 
  by (cases l) auto

lemma map_lit_\<gamma>_\<alpha>_eq[simp]: "0\<notin>set l \<Longrightarrow> map (lit_\<gamma> \<circ> lit_\<alpha>) l = l"
  by (induction l) auto

lemma map_map_lit_\<gamma>_\<alpha>_eq[simp]: 
  "0 \<notin> \<Union>set (map set l) \<Longrightarrow> map (map (lit_\<gamma> \<circ> lit_\<alpha>)) l = l"
  by (induction l) auto  
    
lemma lit_invar_\<gamma>_iff[simp]: "lit_invar (lit_\<gamma> l) \<longleftrightarrow> var_of_lit l \<noteq> 0"
  by (cases l) (auto simp: lit_invar_def lit_\<gamma>_def)
  
lemma var_of_lit_\<alpha>_Z_iff[simp]: "var_of_lit (lit_\<alpha> x) = 0 \<longleftrightarrow> x=0"  
  unfolding var_of_lit_alt lit_\<alpha>_def by auto
    
    
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
  abbreviation mk_err :: "_ \<Rightarrow> 'it error" 
    where "mk_err msg \<equiv> (STR msg, None, None)"
  abbreviation mk_errN :: "_ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errN msg n \<equiv> (STR msg, Some (int n), None)"
  abbreviation mk_errI :: "_ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errI msg i \<equiv> (STR msg, Some i, None)"
  abbreviation mk_errit :: "_ \<Rightarrow> _ \<Rightarrow> 'it error" 
    where "mk_errit msg it \<equiv> (STR msg, None, Some it)"
  abbreviation mk_errNit :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errNit msg n it \<equiv> (STR msg, Some (int n), Some it)"
  abbreviation mk_errIit :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> 'it error" 
    where "mk_errIit msg i it \<equiv> (STR msg, Some i, Some it)"
  
  
      
  text \<open>Check that iterator has not reached the end.\<close>    
  definition "check_not_end it 
    \<equiv> CHECK (it \<noteq> it_end) (mk_err ''Parsed beyond end'')"
    
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
    CHECK (x\<ge>0) (mk_errIit ''Invalid nat'' x it\<^sub>0);
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

    
    

interpretation lit_dflt_option: dflt_option "pure lit_rel" 0 "return oo op ="
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
  "op=$(sem_lit'$l$A)$(Some$True) \<equiv> op_lit_is_true$l$A"
  "op=$(sem_lit'$l$A)$(Some$False) \<equiv> op_lit_is_false$l$A"
  by auto

lemma lit_eq_impl[sepref_import_param]: 
  "(op=,op=) \<in> lit_rel \<rightarrow> lit_rel \<rightarrow> bool_rel"
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
  "(vv_eq_bool, op =) \<in> vv_rel \<rightarrow> bool_rel \<rightarrow> bool_rel"
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
  
  
  

end
