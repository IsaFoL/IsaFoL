theory CDCL_W_Partial_Optimal_Model
  imports CDCL_W_Partial_Encoding
begin


lemma (in conflict_driven_clause_learning\<^sub>W_optimal_weight)
   conflict_opt_state_eq_compatible:
  \<open>conflict_opt S T \<Longrightarrow> S \<sim> S' \<Longrightarrow> T \<sim> T' \<Longrightarrow> conflict_opt S' T'\<close>
  using state_eq_trans[of T' T
    \<open>update_conflicting (Some (negate_ann_lits (trail S'))) S\<close>]
  using state_eq_trans[of T
    \<open>update_conflicting (Some (negate_ann_lits (trail S'))) S\<close>
    \<open>update_conflicting (Some (negate_ann_lits (trail S'))) S'\<close>]
  update_conflicting_state_eq[of S S' \<open>Some {#}\<close>]
  apply (auto simp: conflict_opt.simps state_eq_sym)
  using reduce_trail_to_state_eq state_eq_trans update_conflicting_state_eq by blast

context optimal_encoding
begin

fun normalize_lit :: \<open>'v literal \<Rightarrow> 'v literal\<close> where
  \<open>normalize_lit (Pos L) =
    (if L \<in> replacement_neg ` \<Delta>\<Sigma> then Neg (replacement_pos (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K)))
     else Pos L)\<close> |
  \<open>normalize_lit (Neg L) =
    (if L \<in> replacement_neg ` \<Delta>\<Sigma> then Pos (replacement_pos (SOME K. K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K))
     else Neg L)\<close>

abbreviation normalize_clause :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
\<open>normalize_clause C \<equiv> normalize_lit `# C\<close>

lemma normalize_lit_Some_simp[simp]: \<open>(SOME K. K \<in> \<Delta>\<Sigma> \<and> (L\<^sup>\<mapsto>\<^sup>0 = K\<^sup>\<mapsto>\<^sup>0)) = L\<close> if \<open>L \<in> \<Delta>\<Sigma>\<close> for K
  by (rule some1_equality) (use that in auto)

lemma normalize_lit[simp]:
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Pos L) = (Pos L)\<close>
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Neg L) = (Neg L)\<close>
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Pos (replacement_neg L)) = Neg (replacement_pos L)\<close>
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Neg (replacement_neg L)) = Pos (replacement_pos L)\<close>
  by auto


interpretation enc_weight_opt: conflict_driven_clause_learning\<^sub>W_optimal_weight where
  state_eq = state_eq and
  state = state and
  trail = trail and
  init_clss = init_clss and
  learned_clss = learned_clss and
  conflicting = conflicting and
  cons_trail = cons_trail and
  tl_trail = tl_trail and
  add_learned_cls = add_learned_cls and
  remove_cls = remove_cls and
  update_conflicting = update_conflicting and
  init_state = init_state and
  \<rho> = \<rho>\<^sub>e and
  update_additional_info = update_additional_info
  apply unfold_locales
  subgoal by (rule \<rho>\<^sub>e_mono)
  subgoal using update_additional_info by fast
  subgoal using weight_init_state by fast
  done


context
  fixes S :: 'st and N :: \<open>'v clauses\<close>
  assumes S_\<Sigma>: \<open>init_clss S = penc N\<close>
begin

lemma
  assumes
    \<open>enc_weight_opt.cdcl_bnb_stgy S T\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    dist: \<open>distinct_mset (normalize_clause `# learned_clss S)\<close>
  shows \<open>distinct_mset (normalize_clause `# learned_clss T)\<close>
  using assms(1)
proof (cases)
  case cdcl_bnb_conflict
  then show ?thesis using dist by (auto elim!: rulesE)
next
  case cdcl_bnb_propagate
  then show ?thesis using dist by (auto elim!: rulesE)
next
  case cdcl_bnb_improve
  then show ?thesis using dist by (auto elim!: enc_weight_opt.improveE)
next
  case cdcl_bnb_conflict_opt
  then show ?thesis using dist by (auto elim!: enc_weight_opt.conflict_optE)
next
  case cdcl_bnb_other'
  then show ?thesis
  proof cases
    case decide
    then show ?thesis using dist by (auto elim!: rulesE)
  next
    case bj
    then show ?thesis
    proof cases
      case skip
      then show ?thesis using dist by (auto elim!: rulesE)
    next
      case resolve
      then show ?thesis using dist by (auto elim!: rulesE)
    next
      case backtrack
      then obtain M1 M2 :: \<open>('v, 'v clause) ann_lits\<close> and K L :: \<open>'v literal\<close> and
          D D' :: \<open>'v clause\<close> where
	confl: \<open>conflicting S = Some (add_mset L D)\<close> and
	\<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
	\<open>get_maximum_level (trail S) (add_mset L D') = local.backtrack_lvl S\<close> and
	\<open>get_level (trail S) L = local.backtrack_lvl S\<close> and
	\<open>get_level (trail S) K = Suc (get_maximum_level (trail S) D')\<close> and
	D'_D: \<open>D' \<subseteq># D\<close> and
	\<open>set_mset (clauses S) \<union> set_mset (enc_weight_opt.conflicting_clss S) \<Turnstile>p
	 add_mset L D'\<close> and
	T: \<open>T \<sim>
	   cons_trail (Propagated L (add_mset L D'))
	    (reduce_trail_to M1
	      (add_learned_cls (add_mset L D') (update_conflicting None S)))\<close>
        by (auto simp: enc_weight_opt.obacktrack.simps)
      have
        tr_D: \<open>trail S \<Turnstile>as CNot (add_mset L D)\<close> and
        \<open>distinct_mset (add_mset L D)\<close> and
	\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close>
        using struct confl
	unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
	by auto
      have tr_D': \<open>trail S \<Turnstile>as CNot (add_mset L D')\<close>
        using D'_D tr_D
	by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      have \<open>-normalize_lit L2 \<in> lits_of_l (trail S) \<longleftrightarrow> -L2 \<in> lits_of_l (trail S)\<close>
        if \<open>L2 \<in># D\<close>
	for L2
	using multi_member_split[OF that] tr_D
	apply (cases L2)
	apply (use that in auto)
	oops
(*
	sorry
      have False
	if
	  C: \<open>add_mset (normalize_lit L) (normalize_clause D') = normalize_clause C\<close> and
	  \<open>C \<in># learned_clss S\<close>
	for C
      proof -
        obtain L' C' where
	  C_L'_C'[simp]: \<open>C = add_mset L' C'\<close> and
	  \<open>normalize_clause C' = normalize_clause D'\<close> and
	  [simp]: \<open>normalize_lit L' = normalize_lit L\<close>
	  using C msed_map_invR[of \<open>normalize_lit\<close> C \<open>normalize_lit L\<close> \<open>normalize_clause D'\<close>]
	  by auto
	have \<open>trail S \<Turnstile>as CNot C'\<close>
	  unfolding true_annots_true_cls_def_iff_negation_in_model
	proof
	  fix A
	  assume \<open>A \<in># C'\<close>
	  then obtain A' where
	    \<open>A' \<in># D'\<close> and
	    \<open>normalize_lit A' = normalize_lit A\<close>
	    using \<open>normalize_clause C' = normalize_clause D'\<close>[symmetric]
	    by (force dest!: msed_map_invR multi_member_split)
	  then have \<open>- A' \<in> lits_of_l (trail S)\<close>
	    using tr_D' by (auto dest: multi_member_split)
	  then have \<open>-normalize_lit A' \<in> lits_of_l (trail S)\<close>
	    apply (cases A')
	    apply auto
	    sorry
	  then show \<open>- A \<in> lits_of_l (trail S)\<close>
	    sorry
	qed
        show False sorry
      qed
      then show ?thesis
        using dist T
        by (auto simp: enc_weight_opt.obacktrack.simps)
    qed
  qed
qed
*)

end

end

end