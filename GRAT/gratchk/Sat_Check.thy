section \<open>Satisfiability Check\<close>
theory Sat_Check
imports Grat_Basic
begin
  (*
    For SAT-check, we first read an assignment, and then read and check the formula.
  *)

  subsection \<open>Abstract Specification\<close>
  locale sat_input = input it_invar' it_next it_peek it_end for it_invar' :: "'it::linorder \<Rightarrow> bool" 
    and it_next it_peek it_end   
    
  context sat_input begin
    
    definition "read_assignment it \<equiv> doE {
      let A = Map.empty;
      check_not_end it;
      (A,_) \<leftarrow> EWHILEIT (\<lambda>(_,it). it_invar it \<and> it\<noteq>it_end) (\<lambda>(_,it). it_peek it \<noteq> litZ) (\<lambda>(A,it). doE {
        (l,it) \<leftarrow> parse_literal it;
        check_not_end it;
        CHECK (sem_lit' l A \<noteq> Some False) (mk_errit STR ''Contradictory assignment'' it);
        let A = assign_lit A l;
        ERETURN (A,it)
      }) (A,it);
      ERETURN A
    }"

    text \<open>We merely specify that this does not fail, i.e. termination and assertions. \<close>
    lemma read_assignment_correct[THEN ESPEC_trans, refine_vcg]: 
      "it_invar it \<Longrightarrow> read_assignment it \<le> ESPEC (\<lambda>_. True) (\<lambda>_. True)"
      unfolding read_assignment_def
      apply (refine_vcg EWHILEIT_rule[where R="inv_image (WF\<^sup>+) snd"])
      apply vc_solve
      done  
      
    definition "read_clause_check_sat itE it A \<equiv> doE {
      EASSERT (it_invar it \<and> it_invar itE \<and> itran itE it_end);
      parse_lz
        (mk_errit STR ''Parsed beyond end'' it)   
        litZ itE it (\<lambda>_. True) (\<lambda>x r. doE {
          let l = lit_\<alpha> x;
          ERETURN (r \<or> (sem_lit' l A = Some True))
        }) False
    }"

    lemma read_clause_check_sat_correct[THEN ESPEC_trans, refine_vcg]: 
      "\<lbrakk>itran it itE; it_invar itE\<rbrakk> \<Longrightarrow> 
      read_clause_check_sat itE it A 
      \<le> ESPEC 
          (\<lambda>_. True) 
          (\<lambda>(it',r). \<exists>l. lz_string litZ it l it' \<and> itran it' itE 
                      \<and> (r \<longleftrightarrow> sem_clause' (clause_\<alpha> l) A = Some True))"  
      unfolding read_clause_check_sat_def
      apply (refine_vcg parse_lz_rule[
              where \<Phi> = "\<lambda>l r. r \<longleftrightarrow> sem_clause' (clause_\<alpha> l) A = Some True"
            ] )
      apply (vc_solve simp: itran_invarI)
      subgoal by (auto simp: sem_clause'_true_conv)  
      subgoal by auto
      done    
          
      
    definition "check_sat it itE A \<equiv> doE {
      tok_fold itE it (\<lambda>it _. doE {
        (it',r) \<leftarrow> read_clause_check_sat itE it A;
        CHECK (r) (mk_errit STR ''Clause not satisfied by given assignment'' it);
        ERETURN (it',())
      }) ()
    }"
      
    term sem_cnf  
      
    (* TODO: Move *)  
    lemma obtain_compat_assignment: obtains \<sigma> where "compat_assignment A \<sigma>"
    proof  
      show "compat_assignment A (\<lambda>x. A x = Some True)" unfolding compat_assignment_def by auto
    qed      
      
    lemma check_sat_correct[THEN ESPEC_trans, refine_vcg]: 
      "\<lbrakk>seg it lst itE; it_invar itE\<rbrakk> \<Longrightarrow> check_sat it itE A 
      \<le> ESPEC (\<lambda>_. True) (\<lambda>_. F_invar lst \<and> sat (F_\<alpha> lst))"  
      unfolding check_sat_def
      apply (refine_vcg tok_fold_rule[where 
              \<Phi> = "\<lambda>lst _. \<forall>C\<in>set (map clause_\<alpha> lst). sem_clause' C A = Some True" and Z=litZ and l=lst
            ]
          )  
      apply (vc_solve simp: F_invar_def)
      subgoal
        apply (rule obtain_compat_assignment[of A])
        apply (auto simp: F_\<alpha>_def sat_def sem_cnf_def dest: compat_clause)
        done
      done
      
    definition "verify_sat F_begin F_end it \<equiv> doE {
      A \<leftarrow> read_assignment it;
      check_sat F_begin F_end A
    }"    
      
    lemma verify_sat_correct[THEN ESPEC_trans, refine_vcg]: 
      "\<lbrakk>seg F_begin lst F_end; it_invar F_end; it_invar it\<rbrakk> 
        \<Longrightarrow> verify_sat F_begin F_end it \<le> ESPEC (\<lambda>_. True) (\<lambda>_. F_invar lst \<and> sat (F_\<alpha> lst))"  
      unfolding verify_sat_def  
      apply refine_vcg  
      apply assumption  
      by auto  
        
  end  


  subsection \<open>Implementation\<close>

    
  context sat_input begin  
    subsubsection \<open>Getting Out of Exception Monad\<close>
    synth_definition read_assignment_bd is [enres_unfolds]: "read_assignment it = \<hole>"  
      apply (rule CNV_eqD)
      unfolding read_assignment_def
      apply opt_enres_unfold
      apply (rule CNV_I)
      done
    
    synth_definition read_clause_check_sat_bd is [enres_unfolds]: "read_clause_check_sat itE it A = \<hole>"
      apply (rule CNV_eqD)
      unfolding read_clause_check_sat_def
      apply opt_enres_unfold
      apply (rule CNV_I)
      done
      
    synth_definition check_sat_bd is [enres_unfolds]: "check_sat it itE = \<hole>"
      apply (rule CNV_eqD)
      unfolding check_sat_def
      apply opt_enres_unfold
      apply (rule CNV_I)
      done
    
    synth_definition verify_sat_bd is [enres_unfolds]: "verify_sat F_begin F_end it = \<hole>"
      apply (rule CNV_eqD)
      unfolding verify_sat_def
      apply opt_enres_unfold
      apply (rule CNV_I)
      done
    
  end  
    
  subsection \<open>Extraction from Locales\<close>  
  named_theorems extrloc_unfolds  
    
  context DB2_loc begin
    sublocale sat_input liti.I liti.next liti.peek liti.end
      by unfold_locales
  end  

  concrete_definition (in DB2_loc) read_assignment2_loc 
    uses read_assignment_bd_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) read_assignment2_loc.refine[extrloc_unfolds]
  concrete_definition read_assignment2 uses DB2_loc.read_assignment2_loc_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) read_assignment2.refine[OF DB2_loc_axioms, extrloc_unfolds]

  concrete_definition (in DB2_loc) read_clause_check_sat2_loc 
    uses read_clause_check_sat_bd_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) read_clause_check_sat2_loc.refine[extrloc_unfolds]
  concrete_definition read_clause_check_sat2 uses DB2_loc.read_clause_check_sat2_loc_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) read_clause_check_sat2.refine[OF DB2_loc_axioms, extrloc_unfolds]
    
  concrete_definition (in DB2_loc) check_sat2_loc 
    uses check_sat_bd_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) check_sat2_loc.refine[extrloc_unfolds]
  concrete_definition check_sat2 uses DB2_loc.check_sat2_loc_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) check_sat2.refine[OF DB2_loc_axioms, extrloc_unfolds]

  concrete_definition (in DB2_loc) verify_sat2_loc 
    uses verify_sat_bd_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) verify_sat2_loc.refine[extrloc_unfolds]
  concrete_definition verify_sat2 uses DB2_loc.verify_sat2_loc_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) verify_sat2.refine[OF DB2_loc_axioms, extrloc_unfolds]
    
(*  
  concrete_definition (in DB2_loc) XXX2_loc 
    uses XXX_bd_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) XXX2_loc.refine[extrloc_unfolds]
  concrete_definition XXX2 uses DB2_loc.XXX2_loc_def[unfolded extrloc_unfolds]
  declare (in DB2_loc) XXX2.refine[OF DB2_loc_axioms, extrloc_unfolds]
*)  
    
    
subsubsection \<open>Synthesis of Imperative Code\<close>  
  
context
  fixes DB :: clausedb2
  fixes frml_end :: nat
begin
  interpretation DB2_def_loc DB frml_end .
    
  term read_assignment2 
      
  sepref_definition read_assignment3 is "uncurry read_assignment2"    
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k \<rightarrow>\<^sub>a error_assn +\<^sub>a assignment_assn"
    unfolding read_assignment2_def
    apply (rewrite in "Let Map.empty" assignment.fold_custom_empty)  
    by sepref  

  sepref_register read_assignment2 :: "int list \<Rightarrow> nat \<Rightarrow> (nat error + i_assignment) nres"    
  lemmas [sepref_fr_rules] = read_assignment3.refine  
      
  term read_clause_check_sat2
  sepref_definition read_clause_check_sat3 is "uncurry3 read_clause_check_sat2"
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>k \<rightarrow>\<^sub>a error_assn +\<^sub>a liti.it_assn \<times>\<^sub>a bool_assn"
    unfolding read_clause_check_sat2_def
    supply [[goals_limit = 1]]  
    supply liti.itran_antisym[simp]  (* TODO: Use bundle for all this setup!?*)
    supply sum.splits[split]  
    by sepref  
  sepref_register read_clause_check_sat2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> i_assignment \<Rightarrow> (nat error + nat\<times>bool) nres"
  lemmas [sepref_fr_rules] = read_clause_check_sat3.refine  
    
  term check_sat2  
  sepref_definition check_sat3 is "uncurry3 check_sat2"
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>k \<rightarrow>\<^sub>a error_assn +\<^sub>a unit_assn"  
    unfolding check_sat2_def  
    by sepref  
  sepref_register check_sat2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> i_assignment \<Rightarrow> (nat error + unit) nres"    
  lemmas [sepref_fr_rules] = check_sat3.refine  
    
  term verify_sat2
  sepref_definition verify_sat3 is "uncurry3 verify_sat2"
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k \<rightarrow>\<^sub>a error_assn +\<^sub>a unit_assn"  
    unfolding verify_sat2_def
    by sepref  
  sepref_register verify_sat2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat error + unit) nres"  
  lemmas [sepref_fr_rules] = verify_sat3.refine  
      
end    
    
definition "verify_sat_impl_wrapper DBi F_end \<equiv> do {
  lenDBi \<leftarrow> Array.len DBi;
  if (0<F_end \<and> F_end \<le> lenDBi) then
    verify_sat3 DBi 1 F_end F_end
  else
    return (Inl (STR ''Invalid arguments'',None,None))

}"
  
export_code verify_sat_impl_wrapper checking SML_imp
  
subsection \<open>Correctness Theorem\<close>  
  
context DB2_loc begin  
  lemma verify_sat3_correct:
    assumes SEG: "liti.seg F_begin lst F_end" 
    assumes itI[simp]: "it_invar F_end" "it_invar it"
    shows "<DBi \<mapsto>\<^sub>a DB> verify_sat3 DBi F_begin F_end it <\<lambda>r. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl r \<longrightarrow> F_invar lst \<and> sat (F_\<alpha> lst)) >\<^sub>t"  
  proof -
    note verify_sat2.refine[of DB F_begin F_end it, OF DB2_loc_axioms,symmetric,THEN meta_eq_to_obj_eq]
    also note verify_sat2_loc.refine[symmetric,THEN meta_eq_to_obj_eq]
    also note verify_sat_bd.refine[symmetric]  
    also note verify_sat_correct[OF SEG itI order_refl]
    finally have C1: "verify_sat2 DB F_begin F_end it \<le> ESPEC (\<lambda>_. True) (\<lambda>_. F_invar lst \<and> sat (F_\<alpha> lst))" .
        
    from C1 have NF: "nofail (verify_sat2 DB F_begin F_end it)" 
      by (auto simp: pw_ele_iff refine_pw_simps)
    
    note A = verify_sat3.refine[of DB, to_hnr, of it it F_end F_end F_begin F_begin, unfolded autoref_tag_defs]
    note A = A[THEN hn_refineD]
    note A = A[OF NF]
    note A = A[
        unfolded hn_ctxt_def liti.it_assn_def liti.a_assn_def
          b_assn_pure_conv list_assn_pure_conv sum_assn_pure_conv option_assn_pure_conv prod_assn_pure_conv,
        unfolded pure_def,
        simplified, rule_format
      ]  
  
    from C1 have 1: "RETURN x \<le> verify_sat2 DB F_begin F_end it \<Longrightarrow> \<not>isl x \<longrightarrow> F_invar lst \<and> sat (F_\<alpha> lst)" for x
      unfolding enres_unfolds
      apply (cases x)  
      apply (auto simp: pw_le_iff refine_pw_simps)  
      done  
      
    from SEG have I_begin: "liti.I F_begin" by auto
        
    show ?thesis  
      apply (rule cons_rule[OF _ _ A])
      applyS sep_auto
      applyS (sep_auto dest!: 1 simp: sum.disc_eq_case split: sum.splits)
      applyS (simp add: I_begin)  
      done
  qed  
    
end  
  
theorem verify_sat_impl_wrapper_correct[sep_heap_rules]:
  shows "
    <DBi \<mapsto>\<^sub>a DB> 
      verify_sat_impl_wrapper DBi F_end
    <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> verify_sat_spec DB F_end)>\<^sub>t "
proof -
  {
    assume A: "1 \<le> F_end" "F_end \<le> length DB"
    
    then interpret DB2_loc DB F_end 
      apply unfold_locales by auto
      
    have SEG: "liti.seg 1 (slice 1 F_end DB) F_end"
      using \<open>1 \<le> F_end\<close> \<open>F_end \<le> length DB\<close>
      by (simp add: liti.seg_sliceI)
     
    have INV: "it_invar F_end" 
      subgoal 
        by (meson SEG it_end_invar it_invar_imp_ran 
            itran_invarD liti.itran_alt liti.itran_refl liti.seg_invar2)
      done    
      
    have U1: "slice 1 F_end DB = tl (take F_end DB)"
      unfolding slice_def
      by (metis Misc.slice_def One_nat_def drop_0 drop_Suc_Cons drop_take list.sel(3) tl_drop)
        
    have U2: "F_invar (tl (take F_end DB)) \<and> sat (F_\<alpha> (tl (take F_end DB))) 
      \<longleftrightarrow> verify_sat_spec DB F_end"    
      unfolding verify_sat_spec_def clause_DB_valid_def clause_DB_sat_def using A
      by simp
        
    note verify_sat3_correct[OF SEG INV INV, unfolded U1 U2]
  } note [sep_heap_rules] = this
  
  show ?thesis
    unfolding verify_sat_impl_wrapper_def
    by sep_auto
    
qed
    
end
