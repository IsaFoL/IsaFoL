theory CDCL_W_Partial_Optimal_Model
  imports CDCL_W_Partial_Encoding
begin

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

lemma
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
    apply (auto simp: )
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
    apply -
    apply (rule all_decomposition_implies_conflict_DECO_clause[OF decomp_imp,
      of \<open>negate_ann_lits (trail S)\<close>])
    using 1
    by auto

  have neg: \<open>trail S \<Turnstile>as CNot (mset (map (uminus o lit_of) (trail S)))\<close>
    by (auto simp: true_annots_true_cls_def_iff_negation_in_model
      lits_of_def)
  have ent: \<open>clauses S + enc_weight_opt.conflicting_clss S \<Turnstile>pm DECO_clause (trail S)\<close>
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

end

end
