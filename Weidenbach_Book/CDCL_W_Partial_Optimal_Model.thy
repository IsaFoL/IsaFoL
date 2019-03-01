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

inductive simple_backtrack_conflict_opt :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  \<open>simple_backtrack_conflict_opt S T\<close>
  if
    \<open>backtrack_split (trail S) = (M2, Decided K # M1)\<close> and
    \<open>negate_ann_lits (trail S) \<in># enc_weight_opt.conflicting_clss S\<close> and
    \<open>conflicting S = None\<close> and
    \<open>T \<sim> cons_trail (Propagated (-K) (DECO_clause (trail S)))
      (add_learned_cls (DECO_clause (trail S)) (reduce_trail_to M1 S))\<close>

inductive_cases simple_backtrack_conflict_optE: \<open>simple_backtrack_conflict_opt S T\<close>

lemma simple_backtrack_conflict_opt_conflict_analysis:
  assumes \<open>simple_backtrack_conflict_opt S U\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>\<exists>T T'. enc_weight_opt.conflict_opt S T \<and> resolve\<^sup>*\<^sup>* T T'
    \<and> enc_weight_opt.obacktrack T' U\<close>
  using assms
proof (cases rule: simple_backtrack_conflict_opt.cases)
  case (1 M2 K M1)
  have tr: \<open>trail S = M2 @ Decided K # M1\<close>
    using 1 backtrack_split_list_eq[of \<open>trail S\<close>]
    by auto
  let ?S = \<open>update_conflicting (Some (negate_ann_lits (trail S))) S\<close>
  have \<open>enc_weight_opt.conflict_opt S ?S\<close>
    by (rule enc_weight_opt.conflict_opt.intros[OF 1(2,3)]) auto

  let ?T = \<open>\<lambda>n. update_conflicting
    (Some (negate_ann_lits (drop n (trail S))))
    (reduce_trail_to (drop n (trail S)) S)\<close>
  have proped_M2: \<open>is_proped (M2 ! n)\<close> if \<open>n < length M2\<close> for n
    using that 1(1) nth_length_takeWhile[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    length_takeWhile_le[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    unfolding backtrack_split_takeWhile_dropWhile
    apply auto
    by (metis annotated_lit.exhaust_disc comp_apply nth_mem set_takeWhileD)
  have is_dec_M2[simp]: \<open>filter_mset is_decided (mset M2) = {#}\<close>
    using 1(1) nth_length_takeWhile[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    length_takeWhile_le[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    unfolding backtrack_split_takeWhile_dropWhile
    apply (auto simp: filter_mset_empty_conv)
    by (metis annotated_lit.exhaust_disc comp_apply nth_mem set_takeWhileD)
  have n_d: \<open>no_dup (trail S)\<close> and
    le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (enc_weight_opt.abs_state S)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (enc_weight_opt.abs_state S)\<close> and
    decomp_imp: \<open>all_decomposition_implies_m (clauses S + (enc_weight_opt.conflicting_clss S))
      (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (enc_weight_opt.abs_state S)\<close>
    using inv
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  then have [simp]: \<open>K \<noteq> lit_of (M2 ! n)\<close> if \<open>n < length M2\<close> for n
    using that unfolding tr
    by (auto simp: defined_lit_nth)
  have n_d_n: \<open>no_dup (drop n M2 @ Decided K # M1)\<close> for n
    using n_d unfolding tr
    by (subst (asm) append_take_drop_id[symmetric, of _ n])
      (auto simp del: append_take_drop_id dest: no_dup_appendD)
  have mark_dist: \<open>distinct_mset (mark_of (M2!n))\<close> if \<open>n < length M2\<close> for n
    using dist that proped_M2[OF that] nth_mem[OF that]
    unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def tr
    by (cases \<open>M2!n\<close>) (auto simp: tr)

  have [simp]: \<open>undefined_lit (drop n M2) K\<close> for n
    using n_d defined_lit_mono[of \<open>drop n M2\<close> K M2]
    unfolding tr
    by (auto simp: set_drop_subset)
  from this[of 0] have [simp]: \<open>undefined_lit M2 K\<close>
    by auto
  have [simp]: \<open>count_decided (drop n M2) = 0\<close> for n
    apply (subst count_decided_0_iff)
    using 1(1) nth_length_takeWhile[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    length_takeWhile_le[of \<open>Not \<circ> is_decided\<close> \<open>trail S\<close>]
    unfolding backtrack_split_takeWhile_dropWhile
    by (auto simp: dest!: in_set_dropD set_takeWhileD)
  from this[of 0] have [simp]: \<open>count_decided M2 = 0\<close> by simp
  have proped: \<open>\<And>L mark a b.
      a @ Propagated L mark # b = trail S \<longrightarrow>
      b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
    using le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by auto
  have mark: \<open>drop (Suc n) M2 @ Decided K # M1 \<Turnstile>as
      CNot (mark_of (M2 ! n) - unmark (M2 ! n)) \<and>
      lit_of (M2 ! n) \<in># mark_of (M2 ! n)\<close>
    if \<open>n < length M2\<close> for n
    using proped_M2[OF that] that
      append_take_drop_id[of n M2, unfolded Cons_nth_drop_Suc[OF that, symmetric]]
      proped[of \<open>take n M2\<close> \<open>lit_of (M2 ! n)\<close> \<open>mark_of (M2 ! n)\<close>
    \<open>drop (Suc n) M2 @ Decided K # M1\<close>]
    unfolding tr by (cases \<open>M2!n\<close>) auto
  have confl: \<open>enc_weight_opt.conflict_opt S ?S\<close>
    by (rule enc_weight_opt.conflict_opt.intros) (use 1 in auto)
  have res: \<open>resolve\<^sup>*\<^sup>* ?S (?T n)\<close> if \<open>n \<le> length M2\<close> for n
    using that unfolding tr
  proof (induction n)
    case 0
    then show ?case
      using get_all_ann_decomposition_backtrack_split[THEN iffD1, OF 1(1)]
        1
      by (cases \<open>get_all_ann_decomposition (trail S)\<close>) (auto simp: tr)
  next
    case (Suc n)
    have [simp]: \<open>\<not> Suc (length M2 - Suc n) < length M2 \<longleftrightarrow> n = 0\<close>
      using Suc(2) by auto
    have [simp]: \<open>reduce_trail_to (drop (Suc 0) M2 @ Decided K # M1) S = tl_trail S\<close>
      apply (subst reduce_trail_to.simps)
      using Suc by (auto simp: tr )
    have [simp]: \<open>reduce_trail_to (M2 ! 0 # drop (Suc 0) M2 @ Decided K # M1) S = S\<close>
      apply (subst reduce_trail_to.simps)
      using Suc by (auto simp: tr )
    have [simp]: \<open>(Suc (length M1) -
          (length M2 - n + (Suc (length M1) - (n - length M2)))) = 0\<close>
      \<open>(Suc (length M2 + length M1) -
          (length M2 - n + (Suc (length M1) - (n - length M2)))) =n\<close>
      \<open>length M2 - n + (Suc (length M1) - (n - length M2)) = Suc (length M2 + length M1) - n\<close>
      using Suc by auto
    have [symmetric,simp]: \<open>M2 ! n = Propagated (lit_of (M2 ! n)) (mark_of (M2 ! n))\<close>
      using Suc proped_M2[of n]
      by (cases \<open>M2 ! n\<close>)  (auto simp: tr trail_reduce_trail_to_drop hd_drop_conv_nth
        intro!: resolve.intros)
    have \<open>- lit_of (M2 ! n) \<in># negate_ann_lits (drop n M2 @ Decided K # M1)\<close>
      using Suc in_set_dropI[of \<open>n\<close> \<open>map (uminus o lit_of) M2\<close> n]
      by (simp add: negate_ann_lits_def comp_def drop_map
         del: nth_mem)
    moreover have \<open>get_maximum_level (drop n M2 @ Decided K # M1)
       (remove1_mset (- lit_of (M2 ! n)) (negate_ann_lits (drop n M2 @ Decided K # M1))) =
      Suc (count_decided M1)\<close>
      using Suc(2) count_decided_ge_get_maximum_level[of \<open>drop n M2 @ Decided K # M1\<close>
        \<open>(remove1_mset (- lit_of (M2 ! n)) (negate_ann_lits (drop n M2 @ Decided K # M1)))\<close>]
      by (auto simp: negate_ann_lits_def tr max_def ac_simps
        remove1_mset_add_mset_If get_maximum_level_add_mset
	split: if_splits)
    moreover have \<open>lit_of (M2 ! n) \<in># mark_of (M2 ! n)\<close>
      using mark[of n] Suc by auto
    moreover have \<open>(remove1_mset (- lit_of (M2 ! n))
         (negate_ann_lits (drop n M2 @ Decided K # M1)) \<union>#
        (mark_of (M2 ! n) - unmark (M2 ! n))) = negate_ann_lits (drop (Suc n) (trail S))\<close>
      apply (rule distinct_set_mset_eq)
      using n_d_n[of n] n_d_n[of \<open>Suc n\<close>] no_dup_distinct_mset[OF n_d_n[of n]] Suc
        mark[of n] mark_dist[of n]
      by (auto simp: tr Cons_nth_drop_Suc[symmetric, of n]
          entails_CNot_negate_ann_lits
        dest: in_diffD intro: distinct_mset_minus)
    moreover  { have 1: \<open>(tl_trail
       (reduce_trail_to (drop n M2 @ Decided K # M1) S)) \<sim>
	 (reduce_trail_to (drop (Suc n) M2 @ Decided K # M1) S)\<close>
      apply (subst Cons_nth_drop_Suc[symmetric, of n M2])
      subgoal using Suc by (auto simp: tl_trail_update_conflicting)
      subgoal
        apply (rule state_eq_trans)
	apply simp
	apply (cases \<open>length (M2 ! n # drop (Suc n) M2 @ Decided K # M1) < length (trail S)\<close>)
	apply (auto simp: tl_trail_reduce_trail_to_cons tr)
	done
      done
    have \<open>update_conflicting
     (Some (negate_ann_lits (drop (Suc n) M2 @ Decided K # M1)))
     (reduce_trail_to (drop (Suc n) M2 @ Decided K # M1) S) \<sim>
    update_conflicting
     (Some (negate_ann_lits (drop (Suc n) M2 @ Decided K # M1)))
     (tl_trail
       (update_conflicting (Some (negate_ann_lits (drop n M2 @ Decided K # M1)))
         (reduce_trail_to (drop n M2 @ Decided K # M1) S)))\<close>
       apply (rule state_eq_trans)
       prefer 2
       apply (rule update_conflicting_state_eq)
       apply (rule tl_trail_update_conflicting[THEN state_eq_sym[THEN iffD1]])
       apply (subst state_eq_sym)
       apply (subst update_conflicting_update_conflicting)
       apply (rule 1)
       by fast }
    ultimately have \<open>resolve (?T n) (?T (n+1))\<close> apply -
      apply (rule resolve.intros[of _ \<open>lit_of (M2 ! n)\<close> \<open>mark_of (M2 ! n)\<close>])
      using Suc
        get_all_ann_decomposition_backtrack_split[THEN iffD1, OF 1(1)] 
         in_get_all_ann_decomposition_trail_update_trail[of \<open>Decided K\<close> M1 \<open>M2\<close> \<open>S\<close>]
      by (auto simp: tr trail_reduce_trail_to_drop hd_drop_conv_nth
        intro!: resolve.intros intro: update_conflicting_state_eq)
    then show ?case
      using Suc by (auto simp add: tr)
  qed

  have \<open>get_maximum_level (Decided K # M1) (DECO_clause M1) = get_maximum_level M1 (DECO_clause M1)\<close>
    by (rule get_maximum_level_cong)
      (use n_d in \<open>auto simp: tr get_level_cons_if atm_of_eq_atm_of
      DECO_clause_def Decided_Propagated_in_iff_in_lits_of_l lits_of_def\<close>)
  also have \<open>... = count_decided M1\<close>
    using n_d unfolding tr apply -
    apply (induction M1 rule: ann_lit_list_induct)
    subgoal by auto
    subgoal for L M1'
      apply (subgoal_tac \<open>\<forall>La\<in>#DECO_clause M1'. get_level (Decided L # M1') La = get_level M1' La\<close>)
      subgoal
        using count_decided_ge_get_maximum_level[of \<open>M1'\<close> \<open>DECO_clause M1'\<close>]
        get_maximum_level_cong[of \<open>DECO_clause M1'\<close> \<open>Decided L # M1'\<close> \<open>M1'\<close>]
       by (auto simp: get_maximum_level_add_mset tr atm_of_eq_atm_of
        max_def)
      subgoal
        by (auto simp: DECO_clause_def
          get_level_cons_if atm_of_eq_atm_of Decided_Propagated_in_iff_in_lits_of_l
          lits_of_def)
       done
   subgoal for L C M1'
      apply (subgoal_tac \<open>\<forall>La\<in>#DECO_clause M1'. get_level (Propagated L C # M1') La = get_level M1' La\<close>)
      subgoal
        using count_decided_ge_get_maximum_level[of \<open>M1'\<close> \<open>DECO_clause M1'\<close>]
        get_maximum_level_cong[of \<open>DECO_clause M1'\<close> \<open>Propagated L C # M1'\<close> \<open>M1'\<close>]
       by (auto simp: get_maximum_level_add_mset tr atm_of_eq_atm_of
        max_def)
      subgoal
        by (auto simp: DECO_clause_def
          get_level_cons_if atm_of_eq_atm_of Decided_Propagated_in_iff_in_lits_of_l
          lits_of_def)
      done
    done
  finally have max: \<open>get_maximum_level (Decided K # M1) (DECO_clause M1) = count_decided M1\<close> .
  have \<open>trail S \<Turnstile>as CNot (negate_ann_lits (trail S))\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model
      negate_ann_lits_def lits_of_def)
  then have \<open>clauses S + (enc_weight_opt.conflicting_clss S) \<Turnstile>pm DECO_clause (trail S)\<close>
     unfolding DECO_clause_def apply -
    apply (rule all_decomposition_implies_conflict_DECO_clause[OF decomp_imp,
      of \<open>negate_ann_lits (trail S)\<close>])
    using 1
    by auto

  have neg: \<open>trail S \<Turnstile>as CNot (mset (map (uminus o lit_of) (trail S)))\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model
      lits_of_def)
  have ent: \<open>clauses S + enc_weight_opt.conflicting_clss S \<Turnstile>pm DECO_clause (trail S)\<close>
    unfolding DECO_clause_def
    by (rule all_decomposition_implies_conflict_DECO_clause[OF decomp_imp,
         of \<open>mset (map (uminus o lit_of) (trail S))\<close>])
      (use neg 1 in \<open>auto simp: negate_ann_lits_def\<close>)
  have deco: \<open>DECO_clause (M2 @ Decided K # M1) = add_mset (- K) (DECO_clause M1)\<close>
    by (auto simp: DECO_clause_def)
  have eg: \<open>reduce_trail_to M1 (reduce_trail_to (Decided K # M1) S) \<sim>
    reduce_trail_to M1 S\<close>
    apply (subst reduce_trail_to_compow_tl_trail_le)
    apply (solves \<open>auto simp: tr\<close>)
    apply (subst (3)reduce_trail_to_compow_tl_trail_le)
    apply (solves \<open>auto simp: tr\<close>)
    apply (auto simp: tr)
    apply (cases \<open>M2 = []\<close>)
    apply (auto simp: reduce_trail_to_compow_tl_trail_le reduce_trail_to_compow_tl_trail_eq tr)
    done

  have U: \<open>cons_trail (Propagated (- K) (DECO_clause (M2 @ Decided K # M1)))
     (add_learned_cls (DECO_clause (M2 @ Decided K # M1))
       (reduce_trail_to M1 S)) \<sim>
    cons_trail (Propagated (- K) (add_mset (- K) (DECO_clause M1)))
     (reduce_trail_to M1
       (add_learned_cls (add_mset (- K) (DECO_clause M1))
         (update_conflicting None
           (update_conflicting (Some (add_mset (- K) (negate_ann_lits M1)))
             (reduce_trail_to (Decided K # M1) S)))))\<close>
    unfolding deco
    apply (rule cons_trail_state_eq)
    apply (rule state_eq_trans)
    prefer 2
    apply (rule state_eq_sym[THEN iffD1])
    apply (rule reduce_trail_to_add_learned_cls_state_eq)
    apply (solves \<open>auto simp: tr\<close>)
    apply (rule add_learned_cls_state_eq)
    apply (rule state_eq_trans)
    prefer 2
    apply (rule state_eq_sym[THEN iffD1])
    apply (rule reduce_trail_to_update_conflicting_state_eq)
    apply (solves \<open>auto simp: tr\<close>)
    apply (rule state_eq_trans)
    prefer 2
    apply (rule state_eq_sym[THEN iffD1])
    apply (rule update_conflicting_state_eq)
    apply (rule reduce_trail_to_update_conflicting_state_eq)
    apply (solves \<open>auto simp: tr\<close>)
    apply (rule state_eq_trans)
    prefer 2
    apply (rule state_eq_sym[THEN iffD1])
    apply (rule update_conflicting_update_conflicting)
    apply (rule eg)
    apply (rule state_eq_trans)
    prefer 2
    apply (rule state_eq_sym[THEN iffD1])
    apply (rule update_conflicting_itself)
    by (use 1 in auto)

  have bt: \<open>enc_weight_opt.obacktrack (?T (length M2)) U\<close>
    apply (rule enc_weight_opt.obacktrack.intros[of _ \<open>-K\<close> \<open>negate_ann_lits M1\<close> K M1 \<open>[]\<close>
      \<open>DECO_clause M1\<close> \<open>count_decided M1\<close>])
    subgoal by (auto simp: tr)
    subgoal by (auto simp: tr)
    subgoal by (auto simp: tr)
    subgoal
      using count_decided_ge_get_maximum_level[of \<open>Decided K # M1\<close> \<open>DECO_clause M1\<close>]
      by (auto simp: tr get_maximum_level_add_mset max_def)
    subgoal using max by (auto simp: tr)
    subgoal by (auto simp: tr)
    subgoal by (auto simp: DECO_clause_def negate_ann_lits_def
      image_mset_subseteq_mono)
    subgoal using ent by (auto simp: tr DECO_clause_def)
    subgoal
      apply (rule state_eq_trans [OF 1(4)])
      using 1(4) U by (auto simp: tr)
    done

  show ?thesis
    using confl res[of \<open>length M2\<close>, simplified] bt
    by blast
qed

inductive conflict_opt0 :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  \<open>conflict_opt0 S T\<close>
  if
    \<open>count_decided (trail S) = 0\<close> and
    \<open>negate_ann_lits (trail S) \<in># enc_weight_opt.conflicting_clss S\<close> and
    \<open>conflicting S = None\<close> and
    \<open>T \<sim> update_conflicting (Some {#}) (reduce_trail_to ([] :: ('v, 'v clause) ann_lits) S)\<close>

inductive_cases conflict_opt0E: \<open>conflict_opt0 S T\<close>

inductive cdcl_dpll_bnb_r :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_conflict: "conflict S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'" |
  cdcl_propagate: "propagate S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'" |
  cdcl_improve: "enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'" |
  cdcl_conflict_opt0: "conflict_opt0 S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'" |
  cdcl_simple_backtrack_conflict_opt:
    \<open>simple_backtrack_conflict_opt S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'\<close> |
  cdcl_o': "ocdcl\<^sub>W_o_r S S' \<Longrightarrow> cdcl_dpll_bnb_r S S'"

inductive cdcl_dpll_bnb_r_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S :: 'st where
  cdcl_dpll_bnb_r_conflict: "conflict S S' \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'" |
  cdcl_dpll_bnb_r_propagate: "propagate S S' \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'" |
  cdcl_dpll_bnb_r_improve: "enc_weight_opt.improvep S S' \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'" |
  cdcl_dpll_bnb_r_conflict_opt0: "conflict_opt0 S S' \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'" |
  cdcl_dpll_bnb_r_simple_backtrack_conflict_opt:
    \<open>simple_backtrack_conflict_opt S S' \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'\<close> |
  cdcl_dpll_bnb_r_other': "ocdcl\<^sub>W_o_r S S' \<Longrightarrow> no_confl_prop_impr S \<Longrightarrow> cdcl_dpll_bnb_r_stgy S S'"

lemma no_dup_dropI:
  \<open>no_dup M \<Longrightarrow> no_dup (drop n M)\<close>
  by (cases \<open>n < length M\<close>)  (auto simp: no_dup_def drop_map[symmetric])

lemma tranclp_resolve_state_eq_compatible:
  \<open>resolve\<^sup>+\<^sup>+ S T \<Longrightarrow>T \<sim> T' \<Longrightarrow> resolve\<^sup>+\<^sup>+ S T'\<close>
  apply (induction arbitrary: T' rule: tranclp_induct)
  apply (auto dest: resolve_state_eq_compatible)
  by (metis resolve_state_eq_compatible state_eq_ref tranclp_into_rtranclp tranclp_unfold_end)

lemma conflict_opt0_state_eq_compatible:
  \<open>conflict_opt0 S T \<Longrightarrow> S \<sim> S' \<Longrightarrow> T \<sim> T' \<Longrightarrow> conflict_opt0 S' T'\<close>
  using state_eq_trans[of T' T
    \<open>update_conflicting (Some {#}) (reduce_trail_to ([]::('v,'v clause) ann_lits) S)\<close>]
  using state_eq_trans[of T
    \<open>update_conflicting (Some {#}) (reduce_trail_to ([]::('v,'v clause) ann_lits) S)\<close>
    \<open>update_conflicting (Some {#}) (reduce_trail_to ([]::('v,'v clause) ann_lits) S')\<close>]
  update_conflicting_state_eq[of S S' \<open>Some {#}\<close>]
  apply (auto simp: conflict_opt0.simps state_eq_sym)
  using reduce_trail_to_state_eq state_eq_trans update_conflicting_state_eq by blast


lemma conflict_opt0_conflict_opt:
  assumes \<open>conflict_opt0 S U\<close> and
    inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>\<exists>T. enc_weight_opt.conflict_opt S T \<and> resolve\<^sup>*\<^sup>* T U\<close>
proof -
  have
    1: \<open>count_decided (trail S) = 0\<close> and
    neg: \<open>negate_ann_lits (trail S) \<in># enc_weight_opt.conflicting_clss S\<close> and
    confl: \<open>conflicting S = None\<close> and
    U: \<open>U \<sim> update_conflicting (Some {#}) (reduce_trail_to ([]::('v,'v clause)ann_lits) S)\<close>
    using assms by (auto elim: conflict_opt0E)
  let ?T = \<open>update_conflicting (Some (negate_ann_lits (trail S))) S\<close>
  have confl: \<open>enc_weight_opt.conflict_opt S ?T\<close>
    using neg confl
    by (auto simp: enc_weight_opt.conflict_opt.simps)
  let ?T = \<open>\<lambda>n. update_conflicting
    (Some (negate_ann_lits (drop n (trail S))))
    (reduce_trail_to (drop n (trail S)) S)\<close>

  have proped_M2: \<open>is_proped (trail S ! n)\<close> if \<open>n < length (trail S)\<close> for n
    using 1 that by (auto simp: count_decided_0_iff is_decided_no_proped_iff)
  have n_d: \<open>no_dup (trail S)\<close> and
    le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (enc_weight_opt.abs_state S)\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (enc_weight_opt.abs_state S)\<close> and
    decomp_imp: \<open>all_decomposition_implies_m (clauses S + (enc_weight_opt.conflicting_clss S))
      (get_all_ann_decomposition (trail S))\<close> and
    learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (enc_weight_opt.abs_state S)\<close>
    using inv
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  have proped: \<open>\<And>L mark a b.
      a @ Propagated L mark # b = trail S \<longrightarrow>
      b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
    using le
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by auto
  have [simp]: \<open>count_decided (drop n (trail S)) = 0\<close> for n
    using 1 unfolding count_decided_0_iff
    by (cases \<open>n < length (trail S)\<close>) (auto dest: in_set_dropD)
  have [simp]: \<open>get_maximum_level (drop n (trail S)) C = 0\<close> for n C
    using count_decided_ge_get_maximum_level[of \<open>drop n (trail S)\<close> C]
    by auto
  have mark_dist: \<open>distinct_mset (mark_of (trail S!n))\<close> if \<open>n < length (trail S)\<close> for n
    using dist that proped_M2[OF that] nth_mem[OF that]
    unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (cases \<open>trail S!n\<close>) auto

  have res: \<open>resolve (?T n) (?T (Suc n))\<close> if \<open>n < length (trail S)\<close> for n
  proof -
    define L and E where
      \<open>L = lit_of (trail S ! n)\<close> and
      \<open>E = mark_of (trail S ! n)\<close>
    have \<open>hd (drop n (trail S)) = Propagated L E\<close> and
      tr_Sn: \<open>trail S ! n = Propagated L E\<close>
      using proped_M2[OF that]
      by (cases \<open>trail S ! n\<close>; auto simp: that hd_drop_conv_nth L_def E_def; fail)+
    have \<open>L \<in># E\<close> and
      ent_E: \<open>drop (Suc n) (trail S) \<Turnstile>as CNot (remove1_mset L E)\<close>
      using proped[of \<open>take n (trail S)\<close> L E \<open>drop (Suc n) (trail S)\<close>]
        that unfolding tr_Sn[symmetric]
      by (auto simp: Cons_nth_drop_Suc)
    have 1: \<open>negate_ann_lits (drop (Suc n) (trail S)) =
       (remove1_mset (- L) (negate_ann_lits (drop n (trail S))) \<union>#
        remove1_mset L E)\<close>
      apply (subst distinct_set_mset_eq_iff[symmetric])
      subgoal
        using n_d by (auto simp: no_dup_dropI)
      subgoal
        using n_d mark_dist[OF that] unfolding tr_Sn
        by (auto intro: distinct_mset_mono no_dup_dropI
	  intro!: distinct_mset_minus)
      subgoal
        using ent_E unfolding tr_Sn[symmetric]
        by (auto simp: negate_ann_lits_def that
  	    Cons_nth_drop_Suc[symmetric] L_def lits_of_def
  	    true_annots_true_cls_def_iff_negation_in_model
	    uminus_lit_swap
	  dest!: multi_member_split)
       done
    have \<open>update_conflicting (Some (negate_ann_lits (drop (Suc n) (trail S))))
     (reduce_trail_to (drop (Suc n) (trail S)) S) \<sim>
    update_conflicting
     (Some
       (remove1_mset (- L) (negate_ann_lits (drop n (trail S))) \<union>#
        remove1_mset L E))
     (tl_trail
       (update_conflicting (Some (negate_ann_lits (drop n (trail S))))
         (reduce_trail_to (drop n (trail S)) S)))\<close>
      unfolding 1[symmetric]
      apply (rule state_eq_trans)
      prefer 2
      apply (rule state_eq_sym[THEN iffD1])
      apply (rule update_conflicting_state_eq)
      apply (rule tl_trail_update_conflicting)
      apply (rule state_eq_trans)
      prefer 2
      apply (rule state_eq_sym[THEN iffD1])
      apply (rule update_conflicting_update_conflicting)
      apply (rule state_eq_ref)
      apply (rule update_conflicting_state_eq)
      using that
      by (auto simp: reduce_trail_to_compow_tl_trail funpow_swap1)
    moreover have \<open>L \<in># E\<close>
      using proped[of \<open>take n (trail S)\<close> L E \<open>drop (Suc n) (trail S)\<close>]
        that unfolding tr_Sn[symmetric]
      by (auto simp: Cons_nth_drop_Suc)
    moreover have \<open>- L \<in># negate_ann_lits (drop n (trail S))\<close>
      by (auto simp: negate_ann_lits_def L_def
        in_set_dropI that)
      term \<open>get_maximum_level (drop n (trail S))\<close>
    ultimately show ?thesis apply -
      by (rule resolve.intros[of _ L E])
        (use that in \<open>auto simp: trail_reduce_trail_to_drop
	  \<open>hd (drop n (trail S)) = Propagated L E\<close>\<close>)
  qed
  have \<open>resolve\<^sup>*\<^sup>* (?T 0) (?T n)\<close> if \<open>n \<le> length (trail S)\<close> for n
    using that
    apply (induction n)
    subgoal by auto
    subgoal for n
      using res[of n] by auto
    done
  from this[of \<open>length (trail S)\<close>] have \<open>resolve\<^sup>*\<^sup>* (?T 0) (?T (length (trail S)))\<close>
    by auto
  moreover have \<open>?T (length (trail S)) \<sim> U\<close>
    apply (rule state_eq_trans)
    prefer 2 apply (rule state_eq_sym[THEN iffD1], rule U)
    by auto
  moreover have False if \<open>(?T 0) = (?T (length (trail S)))\<close> and \<open>length (trail S) > 0\<close>
    using arg_cong[OF that(1), of conflicting] that(2)
    by (auto simp: negate_ann_lits_def)
  ultimately have \<open>length (trail S) > 0 \<longrightarrow> resolve\<^sup>*\<^sup>* (?T 0) U\<close>
    using tranclp_resolve_state_eq_compatible[of \<open>?T 0\<close>
      \<open>?T (length (trail S))\<close> U] apply (subst (asm) rtranclp_unfold)
    by (auto simp: )
  then have ?thesis if \<open>length (trail S) > 0\<close>
    using confl that by auto
  moreover have ?thesis if \<open>length (trail S) = 0\<close>
    using that confl U 
      enc_weight_opt.conflict_opt_state_eq_compatible[of S \<open>(update_conflicting (Some {#}) S)\<close> S U]
    by (auto simp: state_eq_sym)
  ultimately show ?thesis
    by blast
qed


lemma backtrack_split_some_is_decided_then_snd_has_hd2:
  \<open>\<exists>l\<in>set M. is_decided l \<Longrightarrow> \<exists>M' L' M''. backtrack_split M = (M'', Decided L' # M')\<close>
  by (metis backtrack_split_snd_hd_decided backtrack_split_some_is_decided_then_snd_has_hd
    is_decided_def list.distinct(1) list.sel(1) snd_conv)

lemma no_step_conflict_opt0_simple_backtrack_conflict_opt:
  \<open>no_step conflict_opt0 S \<Longrightarrow> no_step simple_backtrack_conflict_opt S \<Longrightarrow>
  no_step enc_weight_opt.conflict_opt S\<close>
  using backtrack_split_some_is_decided_then_snd_has_hd2[of \<open>trail S\<close>]
    count_decided_0_iff[of \<open>trail S\<close>]
  by (fastforce simp: conflict_opt0.simps simple_backtrack_conflict_opt.simps
    enc_weight_opt.conflict_opt.simps
    annotated_lit.is_decided_def)

lemma no_step_cdcl_dpll_bnb_r_cdcl_bnb_r:
  assumes \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows
    \<open>no_step cdcl_dpll_bnb_r S \<longleftrightarrow> no_step cdcl_bnb_r S\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  show ?B
    using \<open>?A\<close> no_step_conflict_opt0_simple_backtrack_conflict_opt[of S]
    by (auto simp: cdcl_bnb_r.simps
      cdcl_dpll_bnb_r.simps all_conj_distrib)
next
  assume ?B
  show ?A
    using \<open>?B\<close> simple_backtrack_conflict_opt_conflict_analysis[OF _ assms]
    by (auto simp: cdcl_bnb_r.simps cdcl_dpll_bnb_r.simps all_conj_distrib assms
      dest!: conflict_opt0_conflict_opt)
qed

lemma cdcl_dpll_bnb_r_cdcl_bnb_r:
  assumes \<open>cdcl_dpll_bnb_r S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>cdcl_bnb_r\<^sup>*\<^sup>* S T\<close>
  using assms
proof (cases rule: cdcl_dpll_bnb_r.cases)
  case cdcl_simple_backtrack_conflict_opt
  then obtain S1 S2 where
    \<open>enc_weight_opt.conflict_opt S S1\<close>
    \<open>resolve\<^sup>*\<^sup>* S1 S2\<close> and
    \<open>enc_weight_opt.obacktrack S2 T\<close>
    using simple_backtrack_conflict_opt_conflict_analysis[OF _ assms(2), of T]
    by auto
  then have \<open>cdcl_bnb_r S S1\<close>
    \<open>cdcl_bnb_r\<^sup>*\<^sup>* S1 S2\<close>
    \<open>cdcl_bnb_r S2 T\<close>
    using  mono_rtranclp[of resolve enc_weight_opt.cdcl_bnb_bj]
    mono_rtranclp[of enc_weight_opt.cdcl_bnb_bj ocdcl\<^sub>W_o_r]
    mono_rtranclp[of ocdcl\<^sub>W_o_r cdcl_bnb_r]
    ocdcl\<^sub>W_o_r.intros enc_weight_opt.cdcl_bnb_bj.resolve
    cdcl_bnb_r.intros
    enc_weight_opt.cdcl_bnb_bj.intros
    by (auto 5 4 dest: cdcl_bnb_r.intros conflict_opt0_conflict_opt)
  then show ?thesis
    by auto
next
  case cdcl_conflict_opt0
  then obtain S1 where
    \<open>enc_weight_opt.conflict_opt S S1\<close>
    \<open>resolve\<^sup>*\<^sup>* S1 T\<close>
    using conflict_opt0_conflict_opt[OF _ assms(2), of T]
    by auto
  then have \<open>cdcl_bnb_r S S1\<close>
    \<open>cdcl_bnb_r\<^sup>*\<^sup>* S1 T\<close>
    using  mono_rtranclp[of resolve enc_weight_opt.cdcl_bnb_bj]
    mono_rtranclp[of enc_weight_opt.cdcl_bnb_bj ocdcl\<^sub>W_o_r]
    mono_rtranclp[of ocdcl\<^sub>W_o_r cdcl_bnb_r]
    ocdcl\<^sub>W_o_r.intros enc_weight_opt.cdcl_bnb_bj.resolve
    cdcl_bnb_r.intros
    enc_weight_opt.cdcl_bnb_bj.intros
    by (auto 5 4 dest: cdcl_bnb_r.intros conflict_opt0_conflict_opt)
  then show ?thesis
    by auto
qed (auto 5 4 dest: cdcl_bnb_r.intros conflict_opt0_conflict_opt simp: assms)

lemma resolve_no_prop_confl: \<open>resolve S T \<Longrightarrow> no_step propagate S \<and> no_step conflict S\<close>
  by (auto elim!: rulesE )
lemma cdcl_bnb_r_stgy_res:
  \<open>resolve S T \<Longrightarrow> cdcl_bnb_r_stgy S T\<close>
    using enc_weight_opt.cdcl_bnb_bj.resolve[of S T]
    ocdcl\<^sub>W_o_r.intros[of S T]
    cdcl_bnb_r_stgy.intros[of S T]
    resolve_no_prop_confl[of S T]
  by (auto 5 4 dest: cdcl_bnb_r_stgy.intros conflict_opt0_conflict_opt)

lemma rtranclp_cdcl_bnb_r_stgy_res:
  \<open>resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T\<close>
    using mono_rtranclp[of resolve cdcl_bnb_r_stgy]
    cdcl_bnb_r_stgy_res
  by (auto)

lemma obacktrack_no_prop_confl: \<open>enc_weight_opt.obacktrack S T \<Longrightarrow> no_step propagate S \<and> no_step conflict S\<close>
  by (auto elim!: rulesE enc_weight_opt.obacktrackE)

lemma cdcl_bnb_r_stgy_bt:
  \<open>enc_weight_opt.obacktrack S T \<Longrightarrow> cdcl_bnb_r_stgy S T\<close>
    using enc_weight_opt.cdcl_bnb_bj.backtrack[of S T]
    ocdcl\<^sub>W_o_r.intros[of S T]
    cdcl_bnb_r_stgy.intros[of S T]
    obacktrack_no_prop_confl[of S T]
  by (auto 5 4 dest: cdcl_bnb_r_stgy.intros conflict_opt0_conflict_opt)

lemma cdcl_dpll_bnb_r_stgy_cdcl_bnb_r_stgy:
  assumes \<open>cdcl_dpll_bnb_r_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T\<close>
  using assms
proof (cases rule: cdcl_dpll_bnb_r_stgy.cases)
  case cdcl_dpll_bnb_r_simple_backtrack_conflict_opt
  then obtain S1 S2 where
    \<open>enc_weight_opt.conflict_opt S S1\<close>
    \<open>resolve\<^sup>*\<^sup>* S1 S2\<close> and
    \<open>enc_weight_opt.obacktrack S2 T\<close>
    using simple_backtrack_conflict_opt_conflict_analysis[OF _ assms(2), of T]
    by auto
  then have \<open>cdcl_bnb_r_stgy S S1\<close>
    \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S1 S2\<close>
    \<open>cdcl_bnb_r_stgy S2 T\<close>
    using enc_weight_opt.cdcl_bnb_bj.resolve
    by (auto dest: cdcl_bnb_r_stgy.intros conflict_opt0_conflict_opt
      rtranclp_cdcl_bnb_r_stgy_res cdcl_bnb_r_stgy_bt)
  then show ?thesis
    by auto
next
  case cdcl_dpll_bnb_r_conflict_opt0
  then obtain S1 where
    \<open>enc_weight_opt.conflict_opt S S1\<close>
    \<open>resolve\<^sup>*\<^sup>* S1 T\<close>
    using conflict_opt0_conflict_opt[OF _ assms(2), of T]
    by auto
  then have \<open>cdcl_bnb_r_stgy S S1\<close>
    \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S1 T\<close>
    using enc_weight_opt.cdcl_bnb_bj.resolve
    by (auto dest: cdcl_bnb_r_stgy.intros conflict_opt0_conflict_opt
      rtranclp_cdcl_bnb_r_stgy_res cdcl_bnb_r_stgy_bt)
  then show ?thesis
    by auto
qed (auto 5 4 dest: cdcl_bnb_r_stgy.intros conflict_opt0_conflict_opt)

lemma cdcl_bnb_r_stgy_cdcl_bnb_r:
  \<open>cdcl_bnb_r_stgy S T \<Longrightarrow> cdcl_bnb_r S T\<close>
  by (auto simp: cdcl_bnb_r_stgy.simps cdcl_bnb_r.simps)

lemma rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r:
  \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_bnb_r\<^sup>*\<^sup>* S T\<close>
  by (induction rule: rtranclp_induct)
   (auto dest: cdcl_bnb_r_stgy_cdcl_bnb_r)

context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin
lemma cdcl_dpll_bnb_r_stgy_all_struct_inv:
  \<open>cdcl_dpll_bnb_r_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
  using cdcl_dpll_bnb_r_stgy_cdcl_bnb_r_stgy[of S T]
    rtranclp_cdcl_bnb_r_all_struct_inv[OF S_\<Sigma>]
    rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r[of S T]
  by auto

end

lemma cdcl_bnb_r_stgy_cdcl_dpll_bnb_r_stgy:
  \<open>cdcl_bnb_r_stgy S T \<Longrightarrow> \<exists>T. cdcl_dpll_bnb_r_stgy S T\<close>
  by (meson cdcl_bnb_r_stgy.simps cdcl_dpll_bnb_r_conflict cdcl_dpll_bnb_r_conflict_opt0
    cdcl_dpll_bnb_r_other' cdcl_dpll_bnb_r_propagate cdcl_dpll_bnb_r_simple_backtrack_conflict_opt
    cdcl_dpll_bnb_r_stgy.intros(3) no_step_conflict_opt0_simple_backtrack_conflict_opt)

context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> \<union> additional_atm ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>
     \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin

lemma rtranclp_cdcl_dpll_bnb_r_stgy_cdcl_bnb_r:
  assumes \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T\<close>
  using assms
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using cdcl_dpll_bnb_r_stgy_cdcl_bnb_r_stgy[of T U]
      rtranclp_cdcl_bnb_r_all_struct_inv[OF S_\<Sigma>, of T]
      rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r[of S T]
    by auto
  done

lemma rtranclp_cdcl_dpll_bnb_r_stgy_all_struct_inv:
  \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
  using rtranclp_cdcl_dpll_bnb_r_stgy_cdcl_bnb_r[of T]
    rtranclp_cdcl_bnb_r_all_struct_inv[OF S_\<Sigma>, of T]
    rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r[of S T]
  by auto

lemma full_cdcl_dpll_bnb_r_stgy_full_cdcl_bnb_r_stgy:
  assumes \<open>full cdcl_dpll_bnb_r_stgy S T\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close>
  shows \<open>full cdcl_bnb_r_stgy S T\<close>
  using no_step_cdcl_dpll_bnb_r_cdcl_bnb_r[of T]
    rtranclp_cdcl_dpll_bnb_r_stgy_cdcl_bnb_r[of T]
    rtranclp_cdcl_dpll_bnb_r_stgy_all_struct_inv[of T] assms
      rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r[of S T]
  by (auto simp: full_def
    dest: cdcl_bnb_r_stgy_cdcl_bnb_r cdcl_bnb_r_stgy_cdcl_dpll_bnb_r_stgy)

end

definition lonely_lit_in_add_only :: \<open>'st \<Rightarrow> bool\<close> where
\<open>lonely_lit_in_add_only S \<longleftrightarrow>
  (\<forall>L C. L \<in> \<Delta>\<Sigma> \<longrightarrow> C \<in># clauses S \<longrightarrow> L \<in> atms_of C \<longrightarrow> C \<in># additional_constraint L) \<and>
  (\<forall>L. L \<in> \<Delta>\<Sigma> \<longrightarrow> conflicting S \<noteq> None \<longrightarrow> L \<in> atms_of (the (conflicting S)) \<longrightarrow>
    the (conflicting S) \<in># additional_constraint L)\<close>

definition lonely_not_decided :: \<open>'st \<Rightarrow> bool\<close> where
\<open>lonely_not_decided S \<longleftrightarrow>
  (\<forall>L. atm_of L \<in> \<Delta>\<Sigma> \<longrightarrow> Decided L \<notin> set (trail S))\<close>

(*TODO Move*)
lemma backtrack_split_get_all_ann_decompositionD:
  \<open>backtrack_split M = (a, b) \<Longrightarrow> (b, a) \<in> set (get_all_ann_decomposition M)\<close>
  using get_all_ann_decomposition_backtrack_split[of M a b]
  by (cases \<open>get_all_ann_decomposition M\<close>) auto

lemma cdcl_dpll_bnb_r_lonely_not_decided:
  assumes \<open>cdcl_dpll_bnb_r S T\<close> and
    \<open>lonely_not_decided S\<close>
  shows \<open>lonely_not_decided T\<close>
  using assms
  by (induction)
    (auto simp: conflict.simps lonely_not_decided_def
       ocdcl\<^sub>W_o_r.simps enc_weight_opt.cdcl_bnb_bj.simps
     elim!: rulesE enc_weight_opt.improveE conflict_opt0E
       simple_backtrack_conflict_optE odecideE
       enc_weight_opt.obacktrackE
     dest!: backtrack_split_get_all_ann_decompositionD in_set_tlD)

lemma
  assumes
    \<open>cdcl_dpll_bnb_r S T\<close> and
    lone: \<open>lonely_lit_in_add_only S\<close> and
    ndec: \<open>lonely_not_decided S\<close>
  shows \<open>lonely_lit_in_add_only T\<close>
  using assms(1)
proof (cases)
  case (cdcl_conflict)
  then show ?thesis
    using lone ndec by (auto simp: lonely_lit_in_add_only_def
    conflict.simps)
next
  case (cdcl_propagate)
  then show ?thesis
    using lone ndec by (auto simp: lonely_lit_in_add_only_def
    propagate.simps)
next
  case (cdcl_improve)
  then show ?thesis
    using lone ndec by (auto simp: enc_weight_opt.improvep.simps
      lonely_lit_in_add_only_def)
next
  case (cdcl_conflict_opt0)
  then show ?thesis
    using lone ndec by (auto simp: conflict_opt0.simps
      lonely_lit_in_add_only_def)
next
  case cdcl_simple_backtrack_conflict_opt
  then show ?thesis
    using lone ndec by (auto simp: lonely_lit_in_add_only_def
      DECO_clause_def atms_of_def annotated_lit.is_decided_def
      simple_backtrack_conflict_opt.simps lonely_not_decided_def)
next
  case cdcl_o'
  then show ?thesis
  proof cases
    case decide
    then show ?thesis
    using lone ndec by (auto simp: lonely_lit_in_add_only_def
      DECO_clause_def atms_of_def annotated_lit.is_decided_def
      odecide.simps lonely_not_decided_def)
  next
    case bj
    then show ?thesis
    proof cases
      case skip
      then show ?thesis
        using lone ndec by (auto simp: lonely_lit_in_add_only_def
          DECO_clause_def atms_of_def annotated_lit.is_decided_def
          skip.simps lonely_not_decided_def)
    next
      case backtrack
      then obtain D L K i M1 M2 D' where
	conf: "conflicting S = Some (add_mset L D)" and
	decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
	lev: "get_level (trail S) L = backtrack_lvl S" and
	max: "get_level (trail S) L = get_maximum_level (trail S) (add_mset L D')" and
	max_D: "get_maximum_level (trail S) D' \<equiv> i" and
	lev_K: "get_level (trail S) K = Suc i" and
	D'_D: \<open>D' \<subseteq># D\<close> and
	NU_DL: \<open>clauses S + enc_weight_opt.conflicting_clss S \<Turnstile>pm add_mset L D'\<close> and
	T: "T \<sim> cons_trail (Propagated L (add_mset L D'))
		    (reduce_trail_to M1
		      (add_learned_cls (add_mset L D')
			(update_conflicting None S)))"
	by (elim enc_weight_opt.obacktrackE) auto
      show ?thesis
        unfolding lonely_lit_in_add_only_def
      proof (intro conjI allI impI)
	fix K :: \<open>'v\<close> and C :: \<open>'v literal multiset\<close>
	assume
	  \<open>K \<in> \<Delta>\<Sigma>\<close> and
	  \<open>C \<in># clauses T\<close> and
	  \<open>K \<in> atms_of C\<close>
(*	then show \<open>C \<in># additional_constraint K\<close>
          using lone ndec T conf apply (auto simp: lonely_lit_in_add_only_def
            DECO_clause_def atms_of_def annotated_lit.is_decided_def
            enc_weight_opt.obacktrack.simps lonely_not_decided_def)
	    sorry
      next
	fix K :: \<open>'v\<close>
	assume
	  \<open>K \<in> \<Delta>\<Sigma>\<close> and
	  \<open>conflicting T \<noteq> None\<close> and
	  \<open>K \<in> atms_of (the (conflicting T))\<close>
	show \<open>the (conflicting T) \<in># additional_constraint K\<close> sorry
      qed
    next
      case resolve
      then show ?thesis
        using lone ndec by (auto simp: lonely_lit_in_add_only_def
          DECO_clause_def atms_of_def annotated_lit.is_decided_def
          resolve.simps lonely_not_decided_def)
    qed
    sorry
  qed*)
oops

end

end
