theory CDCL_Two_Watched_Literals_Simple_Implementation_List_Refinement
imports CDCL_Two_Watched_Literals_Simple_Implementation_Algorithm
begin

section \<open>Second Refinement: Indexed Lists\<close>

type_synonym 'v working_queue_list = "('v literal \<times> 'v literal list twl_clause) multiset"
type_synonym 'v lit_queue_list = "'v literal list"

type_synonym 'v clause_list = "'v literal list"
type_synonym 'v clauses_list = "'v literal list"

type_synonym 'v twl_st_list =
  "('v, 'v clause) ann_lits \<times> 'v literal list twl_clause multiset \<times> 'v clause_list twl_clause multiset \<times>
    'v clause_list option \<times> 'v clauses \<times> 'v clauses \<times> 'v working_queue_list \<times> 'v lit_queue"

fun twl_clause_of where
  \<open>twl_clause_of (TWL_Clause W UW) = TWL_Clause (mset W) (mset UW)\<close>

fun twl_st_of :: \<open>'v twl_st_list  \<Rightarrow> 'v twl_st\<close>where
\<open>twl_st_of (M, N, U, C, NP, UP, WS, Q) =
(M, twl_clause_of `# N, twl_clause_of `# U, map_option mset C, NP, UP,
  (\<lambda>(a, b). (a, twl_clause_of b)) `# WS, Q)
\<close>
  
fun get_clauses_list :: "'v twl_st_list \<Rightarrow> 'v literal list twl_clause multiset" where
  \<open>get_clauses_list (M, N, U, D, NP, UP, WS, Q) = N + U\<close>

definition valued where
  \<open>valued M L =
     RETURN (if undefined_lit M L then None else if L \<in> lits_of_l M then Some True else Some False)\<close>

lemma valued_spec:
  assumes \<open>no_dup M\<close>
  shows 
  \<open>valued M L \<le> SPEC(\<lambda>v. (v = None \<longleftrightarrow> undefined_lit M L) \<and>
    (v = Some True \<longleftrightarrow> L \<in> lits_of_l M) \<and> (v = Some False \<longleftrightarrow> -L \<in> lits_of_l M))\<close>
  unfolding valued_def
  by (refine_vcg) 
    (use assms in \<open>auto simp: defined_lit_map lits_of_def atm_of_eq_atm_of uminus_lit_swap
      no_dup_cannot_not_lit_and_uminus
      split: option.splits\<close>)

definition find_unwatched where
\<open>find_unwatched M C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<le> length C \<and> (\<forall>j<i. -(C!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M (C!i) \<and> i < length C)) \<and>
    (found = Some True \<longrightarrow> (C!i \<in> lits_of_l M \<and> i < length C)) \<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      v \<leftarrow> valued M (C!i);
      case v of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some True \<Rightarrow> do { RETURN (Some True, i)}
      | Some False \<Rightarrow> do { RETURN (None, i+1)}
      }
    )
    (None, 0::nat)
  }
\<close>

lemma (in transfer) transfer_bool[refine_transfer]:
  assumes "\<alpha> fa \<le> Fa"
  assumes "\<alpha> fb \<le> Fb"
  shows "\<alpha> (case_bool fa fb x) \<le> case_bool Fa Fb x"
  using assms by (auto split: bool.split)

(* Example of code generation *)
schematic_goal find_unwatched_impl: "RETURN ?c \<le> find_unwatched M C"
  unfolding find_unwatched_def valued_def
  apply (refine_transfer)
  done

concrete_definition find_unwatched_impl uses find_unwatched_impl
prepare_code_thms find_unwatched_impl_def
export_code find_unwatched_impl in SML
(* End of code generation *)

lemma find_unwatched:
  assumes \<open>no_dup M\<close>
  shows \<open>find_unwatched M C \<le> SPEC (\<lambda>(found, i).
      (found = None \<longleftrightarrow> (\<forall>L\<in>set C. -L \<in> lits_of_l M)) \<and>
      (found = Some False \<longleftrightarrow> (i < length C \<and> undefined_lit M (C!i))) \<and>
      (found = Some True \<longleftrightarrow> (i < length C \<and> C!i \<in> lits_of_l M)))\<close>
  unfolding find_unwatched_def
  apply (rule WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
     apply simp_all[2]

  subgoal for s unfolding valued_def
    apply refine_vcg
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l dest: less_SucE
        split: bool.split if_splits)
    done
  subgoal for s using distinct_consistent_interp[OF assms]
    apply (cases s, cases \<open>fst s\<close>)
     by (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth)
  done

fun update_clause_list where
"update_clause_list (TWL_Clause W UW) i j =
  TWL_Clause (list_update W i (UW!j)) (list_update UW j (W!i))"

fun update_clauses_list ::
    "'a list twl_clause multiset \<times> 'a list twl_clause multiset \<Rightarrow>
    'a list twl_clause \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    'a list twl_clause multiset \<times> 'a list twl_clause multiset" where
"update_clauses_list (N, U) D i j =
  (if D \<in># N then (add_mset (update_clause_list D i j) (remove1_mset D N), U)
       else (N, add_mset (update_clause_list D i j) (remove1_mset D U)))"

lemma update_clauses_list_spec:
  assumes \<open>C \<in># N + U\<close> and \<open>i < length (watched C)\<close> and \<open>j < length (unwatched C)\<close>
  shows
  \<open>RETURN (update_clauses_list (N, U) C i j)  \<le> \<Down> {((N, U), (N', U')). twl_clause_of `# N = N' \<and> twl_clause_of `# U = U'}
    (SPEC (\<lambda>(N', U').
              update_clauses (twl_clause_of `# N, twl_clause_of `# U) (twl_clause_of C)
               (watched C ! i) (unwatched C ! j) (N', U')))\<close>
  unfolding update_clauses_list.simps update_clause_list.simps
  apply (rule RETURN_SPEC_refine)
  apply (cases C)
  using assms by (auto simp: update_clauses.simps image_mset_remove1_mset_if mset_update rev_image_eqI)
  
definition unit_propagation_inner_loop_body_list :: "nat \<times> 'v literal list twl_clause \<Rightarrow>
  'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>unit_propagation_inner_loop_body_list C' S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    let (i, C) = C';
    let L = (watched C) ! i;
    let L' = (watched C) ! (1 - i);
    ASSERT(L' \<in># mset (watched C) - {#L#});
    ASSERT (mset (watched C) = {#L, L'#});
    val_L' \<leftarrow> valued M L';
    ASSERT(val_L' = Some True \<longleftrightarrow> L' \<in> lits_of_l M);
    ASSERT(val_L' = Some False \<longleftrightarrow> -L' \<in> lits_of_l M);
    ASSERT(val_L' = None \<longleftrightarrow> undefined_lit M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (unwatched C);
      ASSERT (fst f = None \<longleftrightarrow> (\<forall>L\<in>#mset (unwatched C). - L \<in> lits_of_l M));
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some ((watched C) @ (unwatched C)), NP, UP, {#}, {#})}
        else do {RETURN (Propagated L' (mset (watched C) + mset (unwatched C)) # M, N, U, D, NP, UP, WS, add_mset (-L') Q)}
      else do {
        let K = unwatched C ! (snd f);
        let (N', U') = update_clauses_list (N, U) C i (snd f);
        RETURN (M, N', U', D, NP, UP, WS, Q)
      }
    }
   }
\<close>


lemma distinct_mset_distinct_twl_clause_of:
  \<open>distinct_mset (clause `# twl_clause_of `# N) \<Longrightarrow> distinct_mset N\<close>
  by (induction N) auto


lemma unit_propagation_inner_loop_body_list:
  \<open>(uncurry unit_propagation_inner_loop_body_list, uncurry unit_propagation_inner_loop_body) \<in>
    {(((i, C), S), ((L', C'), S')). L' = watched C ! i \<and> C' = twl_clause_of C \<and> (i = 0 \<or> i = 1) \<and>
    S' = twl_st_of S \<and> twl_struct_invs S' \<and> (L', C') \<in># working_queue S' \<and> C \<in># get_clauses_list S} \<rightarrow>
    \<langle>{(S, S'). S' = twl_st_of S}\<rangle> nres_rel\<close>
proof -
  {
    fix i :: nat and C :: \<open>'a literal list twl_clause\<close> and S' :: \<open>'a twl_st\<close> and S :: \<open>'a twl_st_list\<close>
    let ?L = \<open>watched C ! i\<close>
    let ?L' = \<open>watched C ! (Suc 0 - i)\<close>
    let ?C' = \<open>twl_clause_of C\<close>
    obtain M N U D NP UP WS Q where S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
      by (cases S) auto
    have S'_S: \<open>twl_st_of S = (M, twl_clause_of `# N, twl_clause_of `# U, map_option mset D,
      NP, UP, (\<lambda>(a, b). (a, twl_clause_of b)) `# WS, Q)\<close>
      unfolding S by auto
    assume
      WS: \<open>(?L, ?C') \<in># working_queue S'\<close> and
      S': \<open>S' = twl_st_of S\<close> and
      i: \<open>i = 0 \<or> i = 1\<close> and
      invs: \<open>twl_struct_invs (twl_st_of S)\<close> and
      C_N_U: \<open>C \<in># get_clauses_list S\<close>

    have inv: \<open>twl_st_inv (twl_st_of S)\<close> and valid: \<open>valid_annotation (twl_st_of S)\<close> and
      cdcl_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (twl_st_of S))\<close> and
      valid: \<open>valid_annotation (twl_st_of S)\<close>
      using invs WS apply (auto simp: twl_struct_invs_def)
      done

    have n_d: \<open>no_dup M\<close>
      using cdcl_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def S by (auto simp: trail.simps)
    then have consistent: \<open>- L \<notin> lits_of_l M\<close> if \<open>L \<in> lits_of_l M\<close> for L
      using consistent_interp_def distinct_consistent_interp that by blast

    have cons_M: \<open>consistent_interp (lits_of_l M)\<close>
      using n_d distinct_consistent_interp by fast

    have C'_N_U: \<open>?C' \<in># twl_clause_of `# (N + U)\<close> and 
      uL_M: \<open>-?L \<in> lits_of_l M\<close>
      using WS valid S' by (auto simp: S twl_struct_invs_def split: prod.splits)
    then have struct: \<open>struct_wf_twl_cls ?C'\<close>
      using inv S' by (auto simp: twl_st_inv.simps S)

    have watched_C': \<open>watched ?C' = {#?L, ?L'#}\<close>
      using struct i by (cases C) (auto simp: length_list_2)
    then have mset_watched_C: \<open>mset (watched C) = {#watched C ! i, watched C ! (Suc 0 - i)#}\<close>
      by (cases C) auto
    have unwatched_twl_clause_of[simp]: \<open>set_mset (unwatched (twl_clause_of C)) = set (unwatched C)\<close>
      by (cases C) auto
    have in_set_unwatched_conv: \<open>(\<forall>j<length (unwatched C). defined_lit M (unwatched C ! j)) \<longleftrightarrow>
       (\<forall>L \<in># mset (unwatched C). defined_lit M L)\<close>
       for C :: \<open>'b literal list twl_clause\<close> and M :: \<open>('b, 'c) ann_lit list\<close>
      unfolding set_mset_mset by (metis in_set_conv_nth)
    have twl_clause_of_update_C[simp]: \<open>twl_clause_of (update_clause_list C i j) = update_clause (twl_clause_of C) ?L (unwatched C ! j)\<close>
      if \<open>j < length (unwatched C)\<close> for j
      by (cases C) (use i that struct in \<open>auto simp: mset_eq_size_2 length_list_2 mset_update\<close>)
    have update_clause[simp]: \<open>add_mset ?L (add_mset ?L' (mset (unwatched C))) = clause (twl_clause_of C)\<close>
      using watched_C' by (cases C) simp

(*     have dist: \<open>distinct_mset (clause `# twl_clause_of `# (N + U) + NP + UP)\<close>
      using invs unfolding twl_struct_invs_def S
      by (simp add: clauses_def ac_simps)
    then have dist: \<open>distinct_mset (clause `# twl_clause_of `# (N + U))\<close>
      using distinct_mset_add by blast *)
(*     have distinct_cls_N: \<open>C' = C \<and> C' \<in># N\<close> if \<open>twl_clause_of C' = twl_clause_of C\<close> and \<open>C' \<in># N\<close> for C'
      by (metis (no_types, lifting) C_N_U S UnCI dist
          distinct_mset_add_mset distinct_mset_distinct_twl_clause_of that set_mset_union
          get_clauses_list.simps image_mset_add_mset in_remove1_mset_neq insert_DiffM)

    have distinct_cls_U: \<open>C' = C \<and> C' \<in># U\<close> if \<open>twl_clause_of C' = twl_clause_of C\<close> and \<open>C' \<in># U\<close> for C'
      by (metis (no_types, lifting) C_N_U S UnCI dist
          distinct_mset_add_mset distinct_mset_distinct_twl_clause_of that set_mset_union
          get_clauses_list.simps image_mset_add_mset in_remove1_mset_neq insert_DiffM) *)
    have C_N_N: \<open>twl_clause_of `# remove1_mset C N = remove1_mset (twl_clause_of C) (twl_clause_of `# N)\<close>
      if \<open>C \<in># N\<close>
      by (auto simp: that image_mset_remove1_mset_if)
    have C_U_U: \<open>twl_clause_of `# remove1_mset C U = remove1_mset (twl_clause_of C) (twl_clause_of `# U)\<close>
      if \<open>C \<notin># N\<close>
      using that C'_N_U C_N_U by (auto simp: image_mset_remove1_mset_if remove_1_mset_id_iff_notin
          id_remove_1_mset_iff_notin S)
(*     have \<open>(b < length (unwatched C) \<longrightarrow>
        unwatched C ! b \<in> lits_of_l M \<or> - unwatched C ! b \<in> lits_of_l M) \<longleftrightarrow>
        
        \<close> *)
    have \<open>unit_propagation_inner_loop_body_list (i, C) S \<le>
      \<Down> {(S, S'). S' = twl_st_of S} (unit_propagation_inner_loop_body
      (?L, twl_clause_of C) (twl_st_of S))\<close>
      unfolding unit_propagation_inner_loop_body_list_def unit_propagation_inner_loop_body_def S
        S'_S[unfolded S]
      using n_d
      apply (rewrite at \<open>let _ = watched _ ! _ in _\<close> Let_def)
      supply [[goals_limit = 6]]
      apply (refine_rcg bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched[(* THEN order_trans *)]]
          bind_refine_spec[where M' = \<open>valued _ _\<close>, OF _ valued_spec[]]
          update_clauses_list_spec[THEN order_trans]
          case_prod_bind[of _ \<open>If _ _\<close>])
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
           
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
      
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
      using Decided_Propagated_in_iff_in_lits_of_l consistent nth_mem apply blast
         apply remove_dummy_vars
      using C_N_U S apply simp[]
         apply remove_dummy_vars
      apply simp
      sorry
      oops         
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          consistent split: option.splits bool.splits)[]
thm bind_refine_spec[where M' = \<open>find_unwatched _ _\<close>, OF _ find_unwatched[(* THEN order_trans *)]]
          bind_refine_spec[where M' = \<open>valued _ _\<close>, OF _ valued_spec[]]
          sorry
      qed
        
    sorry
(*       subgoal for L'
      proof -
        have \<open>case_option (undefined_lit M (watched C ! (1 - i)))
                 (case_bool (watched C ! (1 - i) \<in> lits_of_l M)
                   (- watched C ! (1 - i) \<in> lits_of_l M)) = (\<lambda>_. False)\<close>
          apply (intro ext)
    apply clarify
    apply auto[]
                  prefer 6
      subgoal
        apply (rule iffI)
         apply (auto dest: nth_mem simp: Decided_Propagated_in_iff_in_lits_of_l consistent; fail)[]
        apply (rule ccontr)
        apply (use cons_M in \<open>auto simp: Decided_Propagated_in_iff_in_lits_of_l
            consistent_interp_def dest: nth_mem; fail\<close>)[]
        done
                prefer 10
      subgoal
        apply clarsimp
        apply (auto simp add: consistent Decided_Propagated_in_iff_in_lits_of_l)[]
        done
               prefer 10
      subgoal
        apply (clarsimp)
        apply (auto simp add: consistent Decided_Propagated_in_iff_in_lits_of_l C_N_N C_N_U
            C_U_U
            dest!: sym[of \<open>twl_clause_of C\<close>] (* distinct_cls_N *)
            split: if_splits)[]
        sorry
        apply (vc_solve simp: mset_watched_C watched_C' in_set_unwatched_conv
          Decided_Propagated_in_iff_in_lits_of_l
          consistent split: option.splits bool.splits)
      term case_option *)
      sorry
  }

  then show ?thesis
    apply (auto simp add: fun_rel_def_internal nres_rel_def_internal nres_rel_def
        simp del: twl_st_of.simps) done
qed

end