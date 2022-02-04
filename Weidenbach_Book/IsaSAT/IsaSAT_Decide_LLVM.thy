theory IsaSAT_Decide_LLVM
  imports IsaSAT_Decide IsaSAT_VMTF_State_LLVM IsaSAT_Setup_LLVM IsaSAT_Rephase_State_LLVM
begin


sepref_def decide_lit_wl_fast_code
  is \<open>uncurry decide_lit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding decide_lit_wl_heur_def isasat_bounded_assn_def
  (*supply hn_case_prod'[sepref_comb_rules del]*)
  unfolding fold_tuple_optimizations
  by sepref


sepref_register find_unassigned_lit_wl_D_heur decide_lit_wl_heur

sepref_register isa_vmtf_find_next_undef

sepref_def isa_vmtf_find_next_undef_code is
  \<open>uncurry isa_vmtf_find_next_undef\<close> :: \<open>vmtf_remove_assn\<^sup>k *\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_def vmtf_remove_assn_def
  unfolding atom.fold_option
  apply (rewrite in \<open>WHILEIT _ \<hole>\<close> short_circuit_conv)
  supply [[goals_limit = 1]]
  apply annot_all_atm_idxs
  by sepref

sepref_register update_next_search
sepref_def update_next_search_code is
  \<open>uncurry (RETURN oo update_next_search)\<close> :: \<open>atom.option_assn\<^sup>k *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  unfolding update_next_search_def vmtf_remove_assn_def
  by sepref

sepref_register isa_vmtf_find_next_undef_upd  mop_get_saved_phase_heur get_next_phase_st
sepref_def isa_vmtf_find_next_undef_upd_code is
  \<open>uncurry isa_vmtf_find_next_undef_upd\<close>
    :: \<open>trail_pol_fast_assn\<^sup>d *\<^sub>a vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a (trail_pol_fast_assn \<times>\<^sub>a vmtf_remove_assn) \<times>\<^sub>a atom.option_assn\<close>
  unfolding isa_vmtf_find_next_undef_upd_def
  by sepref

sepref_register find_unassigned_lit_wl_D_heur2
sepref_def find_unassigned_lit_wl_D_heur_impl
  is \<open>find_unassigned_lit_wl_D_heur2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn \<times>\<^sub>a atom.option_assn\<close>
  unfolding find_unassigned_lit_wl_D_heur2_def isasat_bounded_assn_def
    fold_tuple_optimizations
  by sepref

sepref_def get_next_phase_st_impl
  is \<open>uncurry2 get_next_phase_st\<close>
  :: \<open>bool1_assn\<^sup>k *\<^sub>a atom_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding get_next_phase_st_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref
ML \<open>Sepref_Translate.gen_trans_step_tac\<close>
thm sepref_fr_rules
ML \<open>(Sepref_Translate.sepref_fr_rules.get @{context}) \<close>
ML \<open>(Sepref_Translate.sepref_fr_rules.get @{context}) |> Tactic.build_net\<close>
ML \<open>
fun print start ctxt str _ = (print_tac ctxt (str ^ " " ^ (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start))))))

    type phases_ctrl = {
      trace: bool,            
      trace_goals: bool,
      int_res: bool,          
      start: string option,   
      stop: string option     
    }
    type phase = (unit -> string) * (Proof.context -> tactic') * int

    local
      fun ph_range (phases : phase list) start stop = let
        fun find_phase name = let
          val i = find_index (fn (n,_,_) => n()=name) phases
          val _ = if i<0 then error ("No such phase: " ^ name) else ()
        in
          i
        end

        val i = case start of NONE => 0 | SOME n => find_phase n
        val j = case stop of NONE => length phases - 1 | SOME n => find_phase n

        val phases = take (j+1) phases |> drop i

        val _ = case phases of [] => error "No phases selected, range is empty" | _ => ()
      in
        phases
      end
    in  
  
      fun PHASES' start phases (ctrl : phases_ctrl) ctxt = let
        val phases = ph_range phases (#start ctrl) (#stop ctrl)
        val phases = map (fn (n,tac,d) => (n,tac ctxt,d)) phases
  
        fun r [] _ st = Seq.single st
          | r ((name,tac,d)::tacs) i st = let
              val n = Thm.nprems_of st
              val bailout_tac = if #int_res ctrl then all_tac else no_tac
              fun trace_tac msg st = (if #trace ctrl then tracing msg else (); Seq.single st)
              
              val trace_goal_tac = if #trace_goals ctrl then print_tac ctxt "Proof state" else all_tac
              
              val trace_start_tac = trace_tac ("Phase " ^ (name ()))
            in
              K trace_goal_tac THEN' K trace_start_tac THEN' IF_EXGOAL (tac)
              THEN_ELSE' (
                fn i => fn st => 
                  (* Bail out if a phase does not solve/create exactly the expected subgoals *)
                  if Thm.nprems_of st = n+d then
                    ((trace_tac ("  Done" ^ @{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))) THEN r tacs i) st)
                  else
                    (trace_tac "*** Wrong number of produced goals" THEN bailout_tac) st
                
              , 
                K (trace_tac "*** Phase tactic failed" THEN bailout_tac))
            end i st
  
      in
        r phases
      end


    end


    fun gen_trans_op_tac start dbg ctxt = let
val _ = @{print} ("gen_trans_op_tac/start" ^ " " ^ 
  (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))))
      val fr_rl_net = Sepref_Translate.sepref_fr_rules.get ctxt |> Tactic.build_net
      val fr_rl_tac = 
        print start ctxt "fr_rl_tac/0" THEN'
        resolve_from_net_tac ctxt fr_rl_net (* Try direct match *)
        THEN' print start ctxt "fr_rl_tac/10"
        ORELSE' (
          Sepref_Frame.norm_goal_pre_tac ctxt (* Normalize precondition *) 
        THEN' print start ctxt "fr_rl_tac/20"
          THEN' (
            resolve_from_net_tac ctxt fr_rl_net
            THEN' print start ctxt "fr_rl_tac/30"
            ORELSE' (
              resolve_tac ctxt @{thms cons_pre_rule} (* Finally, generate a frame condition *)
              THEN_ALL_NEW_LIST [
                print start ctxt "fr_rl_tac/final/1" THEN'
                SOLVED' (REPEAT_ALL_NEW_FWD (DETERM o resolve_tac ctxt @{thms CPR_TAG_rules})),
                print start ctxt "fr_rl_tac/final/10" THEN'
                K all_tac,  (* Frame remains unchanged as first goal, even if fr_rl creates side-conditions *)
                print start ctxt "fr_rl_tac/final/20" THEN'
                resolve_from_net_tac ctxt fr_rl_net
              ]
            )
          )  
        )
      
  (***** Side Condition Solving *)
  local
    open Sepref_Basic
  in
  
    fun side_unfold_tac ctxt = let
      (*val ctxt = put_simpset HOL_basic_ss ctxt
        addsimps sepref_prep_side_simps.get ctxt*)
    in
      CONVERSION (Id_Op.unprotect_conv ctxt)
      THEN' SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms bind_ref_tag_def})
      THEN' TRY o (hyp_subst_tac ctxt)
      (*THEN' asm_full_simp_tac ctxt*)
    end
  
    (* TODO: Not accessible as single ML function? *)
    fun linarith_tac ctxt = 
      Method.insert_tac ctxt (rev (Named_Theorems.get ctxt \<^named_theorems>\<open>arith\<close>))
      THEN' Lin_Arith.tac ctxt
    
    fun bounds_tac ctxt = let
      val ctxt = ctxt 
        addSDs Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_bounds_dest}
        addsimps Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_bounds_simps}
    in
      TRADE (fn ctxt => 
        SELECT_GOAL (auto_tac ctxt)
        THEN_ALL_NEW TRY o linarith_tac ctxt
      ) ctxt
    end
    
    fun side_fallback_tac ctxt = 
      side_unfold_tac ctxt 
      THEN' (
print start ctxt "side_fallback_tac/auto" THEN'
        TRADE (SELECT_GOAL o auto_tac) ctxt
        THEN_ALL_NEW (print start ctxt "side_fallback_tac/auto/end" THEN' TRY o SOLVED' (bounds_tac ctxt))
THEN' print start ctxt "side_fallback_tac/end"
      )
  
    val side_frame_tac = Sepref_Frame.frame_tac side_fallback_tac
    val side_merge_tac = Sepref_Frame.merge_tac side_fallback_tac
    val side_free_tac = Sepref_Frame.free_tac side_fallback_tac
    
    
    fun side_constraint_tac ctxt = Sepref_Constraints.constraint_tac ctxt
    
    val pf_mono_tac = Subgoal.FOCUS_PREMS (fn {context=ctxt,...} => CHANGED (ALLGOALS (Partial_Function.mono_tac ctxt)))
    
    fun side_mono_tac ctxt = side_unfold_tac ctxt THEN' TRADE pf_mono_tac ctxt
  
    fun side_gen_algo_tac ctxt = 
      side_unfold_tac ctxt
      THEN' resolve_tac ctxt (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_gen_algo_rules})
  
    fun side_pref_def_tac ctxt = 
      side_unfold_tac ctxt THEN' 
      TRADE (fn ctxt => 
        resolve_tac ctxt @{thms PREFER_tagI DEFER_tagI} 
        THEN' (Sepref_Debugging.warning_tac' "Obsolete PREFER/DEFER side condition" ctxt THEN' Tagged_Solver.solve_tac ctxt)
      ) ctxt


    fun side_rprem_tac ctxt = 
      resolve_tac ctxt @{thms RPREMI} THEN' Refine_Util.rprems_tac ctxt
      THEN' (K (smash_new_rule ctxt))

    (*
      Solve side condition, or invoke hnr_tac on hn_refine goal.

      In debug mode, side-condition solvers are allowed to not completely solve 
      the side condition, but must change the goal.
    *)  
    fun side_cond_dispatch_tac start dbg hnr_tac ctxt = let
      fun MK tac = if dbg then CHANGED o tac ctxt else SOLVED' (tac ctxt)

      val t_merge = MK side_merge_tac
      val t_frame = MK side_frame_tac
      val t_free = MK side_free_tac
      val t_indep = MK Indep_Vars.indep_tac
      val t_constraint = MK side_constraint_tac
      val t_mono = MK side_mono_tac
      val t_pref_def = MK side_pref_def_tac
      val t_rprem = MK side_rprem_tac
      val t_gen_algo = side_gen_algo_tac ctxt
      val t_cp_cond = MK (apply_method_noargs @{method cp_solve_cond})
      val t_cp_simplify = MK (apply_method_noargs @{method cp_simplify})
      
      val t_fallback = MK side_fallback_tac
      fun AROUND txt tac = print start ctxt ("start " ^ txt) THEN' tac THEN' print start ctxt ("end " ^ txt)
    in
      WITH_concl 
        (fn @{mpat "Trueprop ?t"} => (case t of
              @{mpat "MERGE _ _ _ _ _"} => AROUND "t_merge" t_merge
            | @{mpat "MK_FREE _ _"} => AROUND "t_free" t_free
            | @{mpat "_ \<turnstile> _"} => AROUND "t_frame" t_frame
            | @{mpat "INDEP _"} => AROUND "indep" t_indep     (* TODO: Get rid of this!? *)
            | @{mpat "CONSTRAINT _ _"} => AROUND "CONSTRAINT"  t_constraint
            | @{mpat "M.mono_body _"} => AROUND "mono" t_mono
            | @{mpat "PREFER_tag _"} => AROUND "pref" t_pref_def
            | @{mpat "DEFER_tag _"} => AROUND "deref" t_pref_def
            | @{mpat "RPREM _"} => AROUND "rprem" t_rprem
            | @{mpat "GEN_ALGO _ _"} => AROUND "gen" t_gen_algo
            | @{mpat "CP_cond _"} => AROUND "cond" t_cp_cond           
            | @{mpat "CP_simplify _ _"} => AROUND "simplify" t_cp_simplify
            | @{mpat "hn_refine _ _ _ _ _ _"} => AROUND "refine" hnr_tac 
            | _ => AROUND "fallback" t_fallback
          )
        | _ => K no_tac  
      )
    end

  end  
      val side_tac = print start ctxt "side_tac/inner" THEN' REPEAT_ALL_NEW_FWD 
(print start ctxt "side_tac/REPEAT_ALL_NEW_FWD" THEN' side_cond_dispatch_tac start false (K no_tac) ctxt)

      val fr_tac = 
 (*        if dbg then (* Present all possibilities with (partially resolved) side conditions *)
          fr_rl_tac THEN_ALL_NEW_FWD (TRY o side_tac)
        else (* Choose first rule that solves all side conditions *) *)
          DETERM o SOLVED' (print start ctxt "fr_tac" THEN' fr_rl_tac THEN_ALL_NEW_FWD (print start ctxt "side_tac" THEN' SOLVED' side_tac))

    in
      PHASES' start [
        (fn () => "Align goal" ^ " " ^ (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))),Sepref_Frame.align_goal_tac, 0),
        (fn () => "Frame rule" ^ " " ^ (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))),fn ctxt => resolve_tac ctxt @{thms trans_frame_rule}, 1),
        (* RECOVER_PURE goal *)
        (fn () => "Recover pure" ^ " " ^ (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))),Sepref_Frame.recover_pure_tac, ~1),
        (* hn-refine goal with stripped precondition *)
        (fn () => "Apply rule" ^ " " ^ (@{make_string} (Time.toMilliseconds (#elapsed (Timing.result start)))),K fr_tac,~1)
      ] (Sepref_Basic.flag_phases_ctrl ctxt dbg) ctxt
    end

      
fun gen_trans_step_tac start dbg ctxt = Sepref_Translate.side_cond_dispatch_tac dbg
      ( Sepref_Frame.norm_goal_pre_tac ctxt 
        THEN' print start ctxt "THEN'"
        THEN' ((print start ctxt "THEN'/1 start" 
                 THEN' Sepref_Frame.align_goal_tac ctxt
                 THEN' print start ctxt "THEN'/1 5"
                 THEN' Sepref_Translate.trans_comb_tac ctxt THEN' print start ctxt "THEN'/1 end")
              ORELSE' (print start ctxt "THEN'/2 start"
                 THEN' gen_trans_op_tac start dbg ctxt THEN' print start ctxt "THEN'/2 end")))
      ctxt\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

  method handle_CP_SEQ =  
    drule CP_HANDLED,
    erule CP_SEQE,
    (elim conjE)?,
    (*cp_sels_to_vars?,
    cp_vars_to_sels?,*)
    solves cp_resolve_tag | (cp_explode_prod?, cp_resolve_tag)

sepref_def decide_wl_or_skip_D_fast_code
  is \<open>decide_wl_or_skip_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a bool1_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply[[goals_limit=1]]
  apply (rule hfref_refine_with_pre[OF decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur, unfolded Down_id_eq])
  unfolding decide_wl_or_skip_D_heur'_def
  unfolding fold_tuple_optimizations option.case_eq_if atom.fold_option
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
  apply sepref_dbg_trans_step
apply (tactic \<open> (REPEAT_DETERM_N 50 ( Sepref_Translate.trans_step_tac @{context} 1))\<close>)
                      apply (tactic \<open> (REPEAT_DETERM_N 35 ( Sepref_Translate.trans_step_tac @{context} 1))\<close>)
  supply [cp_solve_cond_pre] = CP_simps 
  apply (rule CP_simplifyI)
            apply (determ \<open>((thin_tac "_")+)?\<close>)
            apply (rule impI)
    apply ( (simp only: CP_simps cong: CP_tag_cong)?)
            apply (determ \<open>cp_normalize_step\<close>)
            apply (determ \<open>cp_normalize_step\<close>)
               apply (determ \<open>cp_normalize_step\<close>)
  apply (handle_CP_SEQ)
  apply (drule CP_HANDLED,
    erule CP_EXE)
              apply ((elim conjE)?)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
  apply (subst (asm) prod_eq_iff)
              supply [[simp_trace=false]]
               apply ((simp only: (* prod_eq_iff *)  prod.inject cnv_conj_to_meta (* fst_conv snd_conv *)  cong: CP_tag_cong))
               apply (cp_resolve_tag)

  thm prod_eq_iff
              apply (drule CP_monos[THEN CP_HANDLEI] | handle_plain_eqs
       |handle_CP_SEQ|handle_CP_EX(*handle_CP_EX32
      |handle_CP_JOIN|handle_CP_RPT *)
    
)
  unfolding CP_simps
  apply (rule CP_simp_join_triv)
  apply (tactic \<open>HEADGOAL (gen_trans_step_tac (Timing.start ()) true @{context})\<close>)
apply (tactic \<open> (REPEAT_DETERM_N 50 ( Sepref_Translate.trans_step_tac @{context} 1))\<close>)
  oops
apply (tactic \<open> (REPEAT_DETERM_N 1 ( Sepref_Translate.trans_step_tac @{context} 1))\<close>)
(*
supply [[simp_trace]]
apply sepref_dbg_trans_step
  *)
  oops
apply (tactic \<open> (REPEAT_DETERM_N 1 ( Sepref_Translate.trans_step_tac @{context} 1))\<close>)
oops
  ML \<open>Sepref_Translate.trans_step_tac\<close>
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints
  by sepref


experiment begin

export_llvm
  decide_lit_wl_fast_code
  isa_vmtf_find_next_undef_code
  update_next_search_code
  isa_vmtf_find_next_undef_upd_code
  decide_wl_or_skip_D_fast_code

end


end
