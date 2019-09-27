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

definition base_atm :: \<open>'v \<Rightarrow> 'v\<close> where
  \<open>base_atm L = (if L \<in> \<Sigma> - \<Delta>\<Sigma> then L else
    if L \<in> replacement_neg ` \<Delta>\<Sigma> then (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K))
    else (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_pos K)))\<close>

lemma normalize_lit_Some_simp[simp]: \<open>(SOME K. K \<in> \<Delta>\<Sigma> \<and> (L\<^sup>\<mapsto>\<^sup>0 = K\<^sup>\<mapsto>\<^sup>0)) = L\<close> if \<open>L \<in> \<Delta>\<Sigma>\<close> for K
  by (rule some1_equality) (use that in auto)

lemma base_atm_simps1[simp]:
  \<open>L \<in> \<Sigma> \<Longrightarrow> L \<notin> \<Delta>\<Sigma> \<Longrightarrow> base_atm L = L\<close>
  by (auto simp: base_atm_def)

lemma base_atm_simps2[simp]:
  \<open>L \<in> (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<Longrightarrow>
    K \<in> \<Sigma> \<Longrightarrow> K \<notin> \<Delta>\<Sigma> \<Longrightarrow> L \<in> \<Sigma> \<Longrightarrow> K = base_atm L \<longleftrightarrow> L = K\<close>
  by (auto simp: base_atm_def)

lemma base_atm_simps3[simp]:
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> base_atm L \<in> \<Sigma>\<close>
  \<open>L \<in> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<Longrightarrow> base_atm L \<in> \<Delta>\<Sigma>\<close>
  apply (auto simp: base_atm_def)
  by (metis (mono_tags, lifting) tfl_some)

fun normalize_lit :: \<open>'v literal \<Rightarrow> 'v literal\<close> where
  \<open>normalize_lit (Pos L) =
    (if L \<in> replacement_neg ` \<Delta>\<Sigma> then Neg (replacement_pos (SOME K. (K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K)))
     else Pos L)\<close> |
  \<open>normalize_lit (Neg L) =
    (if L \<in> replacement_neg ` \<Delta>\<Sigma> then Pos (replacement_pos (SOME K. K \<in> \<Delta>\<Sigma> \<and> L = replacement_neg K))
     else Neg L)\<close>

abbreviation normalize_clause :: \<open>'v clause \<Rightarrow> 'v clause\<close> where
\<open>normalize_clause C \<equiv> normalize_lit `# C\<close>


lemma normalize_lit[simp]:
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Pos L) = (Pos L)\<close>
  \<open>L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Neg L) = (Neg L)\<close>
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Pos (replacement_neg L)) = Neg (replacement_pos L)\<close>
  \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> normalize_lit (Neg (replacement_neg L)) = Pos (replacement_pos L)\<close>
  by auto

definition all_clauses_literals :: \<open>'v list\<close> where
  \<open>all_clauses_literals = (SOME xs. mset xs = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>))\<close>


context
  assumes [simp]: \<open>finite \<Sigma>\<close>
begin

lemma all_clauses_literals:
  \<open>mset all_clauses_literals = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
  \<open>distinct all_clauses_literals\<close>
  \<open>set all_clauses_literals = ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
proof -
  show 1: \<open>mset all_clauses_literals = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
    using someI[of \<open>\<lambda>xs. mset xs = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>]
      finite_\<Sigma> ex_mset[of \<open>mset_set (\<Sigma> - \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>]
    unfolding all_clauses_literals_def[symmetric]
    by metis
  show 2: \<open>distinct all_clauses_literals\<close>
    using someI[of \<open>\<lambda>xs. mset xs = mset_set ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>]
      finite_\<Sigma> ex_mset[of \<open>mset_set (\<Sigma> - \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>]
    unfolding all_clauses_literals_def[symmetric]
    by (metis distinct_mset_mset_set distinct_mset_mset_distinct)
  show 3: \<open>set all_clauses_literals = ((\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>)\<close>
    using arg_cong[OF 1, of set_mset] finite_\<Sigma>
    by simp
qed

definition complete_trail :: \<open>('v, 'v clause) ann_lits \<Rightarrow> ('v, 'v clause) ann_lits\<close> where
\<open>complete_trail M = M @ map (Decided o Pos) (filter (\<lambda>L. undefined_lit M (Pos L)) all_clauses_literals)\<close>

lemma no_dup_complete_trail[simp]:
  \<open>no_dup (complete_trail M) \<longleftrightarrow> no_dup M\<close>
  by (auto simp: complete_trail_def no_dup_def comp_def all_clauses_literals(1,2)
    undefined_notin)

lemma tautology_complete_trail[simp]:
  \<open>tautology (lit_of `# mset (complete_trail M)) \<longleftrightarrow> tautology (lit_of `# mset M)\<close>
  by (auto simp: complete_trail_def tautology_decomp' comp_def all_clauses_literals
          undefined_notin uminus_lit_swap defined_lit_Neg_Pos_iff
       simp flip: defined_lit_Neg_Pos_iff)

lemma atms_of_complete_trail:
  \<open>atms_of (lit_of `# mset (complete_trail M)) =
     atms_of (lit_of `# mset M) \<union> (\<Sigma> - \<Delta>\<Sigma>) \<union> replacement_neg ` \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma>\<close>
  by (auto simp add: complete_trail_def all_clauses_literals
    image_image image_Un atms_of_def defined_lit_map)

fun remove_dup_information :: \<open>('v, _) ann_lits \<Rightarrow> ('v, _) ann_lits\<close> where
  \<open>remove_dup_information [] = []\<close> |
  \<open>remove_dup_information (Decided K # M) = Decided K # remove_dup_information M\<close> |
  \<open>remove_dup_information (Propagated L C # M) =
    (if atm_of L \<in> \<Sigma> - \<Delta>\<Sigma> then Propagated L C # remove_dup_information M
     else if defined_lit M (Pos (replacement_pos (base_atm (atm_of L)))) \<or> defined_lit M (Pos (replacement_neg (base_atm (atm_of L))))
     then remove_dup_information M else Propagated L C # remove_dup_information M)\<close>

lemma length_complete_trail[simp]: \<open>length (complete_trail []) = length all_clauses_literals\<close>
  unfolding complete_trail_def
  by auto

lemma distinct_count_list_if: \<open>distinct xs \<Longrightarrow> count_list xs x = (if x \<in> set xs then 1 else 0)\<close>
  by (induction xs) auto


lemma isabelle_should_do_that_automatically: \<open>Suc (a - Suc 0) = a \<longleftrightarrow> a \<ge> 1\<close>
  by auto

lemma length_complete_trail_Cons:
  \<open>no_dup (K # M) \<Longrightarrow> length (complete_trail (K # M)) = (if atm_of (lit_of K) \<in> set all_clauses_literals then 0 else 1) + length (complete_trail M)\<close>
  unfolding complete_trail_def apply auto
  apply (subst conj_commute)
  apply (auto simp: complete_trail_def length_removeAll_count_list distinct_count_list_if 
    all_clauses_literals(2) isabelle_should_do_that_automatically simp flip: filter_filter removeAll_filter_not_eq)
  by (meson defined_lit_Pos_atm_iff filter_empty_conv le_0_eq length_0_conv not_less_eq_eq)

lemma length_complete_trail_eq:
  \<open>no_dup M \<Longrightarrow> atm_of ` (lits_of_l M) \<subseteq> set all_clauses_literals \<Longrightarrow> length (complete_trail M) = length all_clauses_literals\<close>
  by (induction M rule: ann_lit_list_induct) (auto simp: length_complete_trail_Cons)

lemma in_set_all_clauses_literals_simp[simp]:
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma> \<Longrightarrow> atm_of L \<in> set all_clauses_literals\<close>
  \<open>K \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_pos K \<in> set all_clauses_literals\<close>
  \<open>K \<in> \<Delta>\<Sigma> \<Longrightarrow> replacement_neg K \<in> set all_clauses_literals\<close>
  by (auto simp: all_clauses_literals)

lemma atm_of_remove_dup_information:
  \<open>atm_of ` (lits_of_l M) \<subseteq> set all_clauses_literals \<Longrightarrow> atm_of ` (lits_of_l (remove_dup_information M)) \<subseteq> set all_clauses_literals\<close>
  apply (induction M rule: ann_lit_list_induct)
  apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def image_image)
  done

lemma remove_dup_information_subset: \<open>mset (remove_dup_information M) \<subseteq># mset M\<close>
  apply (induction M rule: ann_lit_list_induct) apply auto
  apply (metis add_mset_remove_trivial diff_subset_eq_self subset_mset.dual_order.trans)+
  done

(*TODO Move*)
lemma no_dup_subsetD: \<open>no_dup M \<Longrightarrow> mset M' \<subseteq># mset M \<Longrightarrow> no_dup M'\<close>
  unfolding no_dup_def distinct_mset_mset_distinct[symmetric] mset_map
  apply (drule image_mset_subseteq_mono[of _ _ \<open>atm_of o lit_of\<close>])
  apply (drule distinct_mset_mono)
  apply auto
  done

lemma no_dup_remove_dup_information:
  \<open>no_dup M \<Longrightarrow> no_dup (remove_dup_information M)\<close>
  using no_dup_subsetD[OF _ remove_dup_information_subset] by blast

lemma atm_of_complete_trail:
  \<open>atm_of ` (lits_of_l M) \<subseteq> set all_clauses_literals \<Longrightarrow> atm_of ` (lits_of_l (complete_trail M)) = set all_clauses_literals\<close>
  unfolding complete_trail_def by (auto simp: lits_of_def image_image image_Un defined_lit_map)

lemma atm_of_complete_trail_remove_dup_information:
  \<open>no_dup M \<Longrightarrow> atm_of ` (lits_of_l M) \<subseteq> set all_clauses_literals \<Longrightarrow> atm_of ` (lits_of_l (complete_trail (remove_dup_information M))) = set all_clauses_literals\<close>
  by (simp_all add: atm_of_complete_trail atm_of_remove_dup_information)

text \<open>TODO:
  \<^item> complete_trail is doing the wrong thing (or it should be done before @{term \<open>remove_dup_information\<close>}).
  \<^item> is the measure really the simplest thing we can do?
\<close>


fun ocdcl_score_rev :: \<open>('v, 'b) ann_lits \<Rightarrow> ('v, 'b) ann_lits \<Rightarrow> nat\<close> where
  \<open>ocdcl_score_rev _ [] = 0\<close> |
  \<open>ocdcl_score_rev M' (Propagated K C # M) = ocdcl_score_rev (M' @ [Propagated K C]) M\<close> |
  \<open>ocdcl_score_rev M' (Decided K # M) = ocdcl_score_rev (M' @ [Decided K]) M +
     (if atm_of K \<in> \<Sigma> - \<Delta>\<Sigma> then 1
     else if Decided (base_atm (atm_of K)) \<in> set (map (map_annotated_lit (base_atm o atm_of) id id) M')
         then 2 else 1) * 3^card (base_atm ` atms_of (lit_of `# mset M))\<close>

abbreviation ocdcl_score:: \<open>('v, 'b) ann_lits \<Rightarrow> ('v, 'b) ann_lits \<Rightarrow> nat\<close> where
  \<open>ocdcl_score M M' \<equiv> ocdcl_score_rev M (rev M')\<close>

lemma ocdcl_score_rev_induct_internal:
  fixes xs ys :: \<open>('v, 'b) ann_lits\<close>
  assumes
    \<open>ys @ xs = M0\<close>
    \<open>P M0 []\<close>
    \<open>\<And>L C M M'. M0 = M' @ Propagated L C # M  \<Longrightarrow> P (M' @ [Propagated L C]) M \<Longrightarrow> P M' (Propagated L C # M)\<close>
    \<open>\<And>L M M'. M0 = M' @ Decided L # M\<Longrightarrow> P (M' @ [Decided L]) M \<Longrightarrow> P M' (Decided L # M)\<close>
  shows \<open>P ys xs \<and> ys @ xs = M0\<close>
  using assms(1)
  apply (induction ys xs rule: ocdcl_score_rev.induct)
  subgoal using assms(1,2) by auto
  subgoal for M L C M'
    using assms(3) by auto
  subgoal for M L M'
    using assms(4) by auto
  done

lemma ocdcl_score_rev_induct2:
  fixes xs ys :: \<open>('v, 'b) ann_lits\<close>
  assumes
    \<open>P (ys @ xs) []\<close>
    \<open>\<And>L C M M'. ys @ xs = M' @ Propagated L C # M  \<Longrightarrow> P (M' @ [Propagated L C]) M \<Longrightarrow> P M' (Propagated L C # M)\<close>
    \<open>\<And>L M M'. ys @ xs = M' @ Decided L # M \<Longrightarrow> P (M' @ [Decided L]) M \<Longrightarrow> P M' (Decided L # M) \<close>
  shows \<open>P ys xs\<close>
  using ocdcl_score_rev_induct_internal[of ys xs \<open>ys @ xs\<close> P] assms by auto

lemma ocdcl_score_rev_induct:
  fixes xs ys :: \<open>('v, 'b) ann_lits\<close>
  assumes
    \<open>P xs []\<close>
    \<open>\<And>L C M M'. xs = M' @ Propagated L C # M  \<Longrightarrow> P (M' @ [Propagated L C]) M \<Longrightarrow> P M' (Propagated L C # M)\<close>
    \<open>\<And>L M M'. xs = M' @ Decided L # M \<Longrightarrow> P (M' @ [Decided L]) M \<Longrightarrow> P M' (Decided L # M) \<close>
  shows \<open>P [] xs\<close>
  using ocdcl_score_rev_induct_internal[of \<open>[]\<close> xs xs P] assms by auto

lemma Decided_map_annotated_lit_iff[simp]:
  \<open>Decided L = map_annotated_lit f g h x \<longleftrightarrow> (\<exists>x'. x = Decided x' \<and> L = f x')\<close>
  by (cases x) auto

lemma
  \<open>atm_of ` (lits_of_l (M' @ M)) \<subseteq> \<Sigma> \<Longrightarrow> no_dup (M' @ M) \<Longrightarrow>
     ocdcl_score_rev M' M \<le> 3 ^ (card ((base_atm o atm_of) ` lits_of_l M))\<close>
  apply (induction M' M rule: ocdcl_score_rev_induct2)
  subgoal by auto
  subgoal for L M' M
    by (cases \<open>atm_of L \<in> \<Sigma>\<close>) (auto simp: card_insert_if)
  subgoal for L Ma M'a
    using \<Delta>\<Sigma>_\<Sigma>
    apply (auto simp: card_insert_if atm_of_eq_atm_of lits_of_def image_image
      atms_of_def image_Un dest!: split_list[of _ M'a])
  oops

end


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
  by (cases \<open>n < length M\<close>) (auto simp: no_dup_def drop_map[symmetric])

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
      \<open>?T (length (trail S))\<close> U] by (subst (asm) rtranclp_unfold) auto
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
  by (auto elim!: rulesE)

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
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin
lemma cdcl_dpll_bnb_r_stgy_all_struct_inv:
  \<open>cdcl_dpll_bnb_r_stgy S T \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
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
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
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
  \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow>
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S) \<Longrightarrow>
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


text \<open>TODO: \<^term>\<open>Pos (replacement_pos A) \<notin># C\<close> should be \<^term>\<open>Pos (replacement_pos A) \<notin># C\<close>
  but only for learned clauses.\<close>
definition additional_lit_notin :: \<open>'st \<Rightarrow> bool\<close> where
  \<open>additional_lit_notin S \<longleftrightarrow>
    ((\<forall>A\<in>\<Delta>\<Sigma>. Decided (Neg (replacement_pos A)) \<notin> set (trail S)) \<and>
     (\<forall>A\<in>\<Delta>\<Sigma>. Decided (Neg (replacement_neg A)) \<notin> set (trail S)) \<and>
     (\<forall>A\<in>\<Delta>\<Sigma>. \<forall>C \<in># clauses S. Pos (replacement_pos A) \<notin># C) \<and>
     (\<forall>A\<in>\<Delta>\<Sigma>. \<forall>C \<in># clauses S. Pos (replacement_neg A) \<notin># C) \<and>
     (\<forall>A\<in>\<Delta>\<Sigma>. conflicting S \<noteq> None \<longrightarrow> Pos (replacement_pos A) \<notin># the (conflicting S)) \<and>
     (\<forall>A\<in>\<Delta>\<Sigma>. conflicting S \<noteq> None \<longrightarrow> Pos (replacement_neg A) \<notin># the (conflicting S)))\<close>

(*TODO Move*)
lemma backtrack_split_reduce_trail_to[simp]:
  \<open>backtrack_split (trail S) = (M2, Decided K # M1) \<Longrightarrow> trail (reduce_trail_to M1 S) = M1\<close>
  using get_all_ann_decomposition_backtrack_split get_all_ann_decomposition_decomp reduce_trail_to_trail_tl_trail_decomp by blast

lemma backtrack_split_trailD:
  \<open>backtrack_split (trail S) = (M2, Decided K # M1) \<Longrightarrow> trail S = M2 @ Decided K # M1\<close>
  by (metis backtrack_split_list_eq fst_conv snd_conv)

lemma cdcl_dpll_bnb_r_stgy_reasons_in_clauses:
  \<open>cdcl_dpll_bnb_r_stgy S T \<Longrightarrow> reasons_in_clauses S \<Longrightarrow> reasons_in_clauses T\<close>
  by (auto 5 5 simp: cdcl_dpll_bnb_r_stgy.simps reasons_in_clauses_def ocdcl\<^sub>W_o_r.simps
      enc_weight_opt.cdcl_bnb_bj.simps neq_Nil_conv
    elim!: rulesE enc_weight_opt.improveE conflict_opt0E odecideE
      simple_backtrack_conflict_optE enc_weight_opt.obacktrackE
    dest!: backtrack_split_trailD get_all_ann_decomposition_exists_prepend)

lemma rtranclp_cdcl_dpll_bnb_r_stgy_reasons_in_clauses:
  \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> reasons_in_clauses S \<Longrightarrow> reasons_in_clauses T\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: cdcl_dpll_bnb_r_stgy_reasons_in_clauses)


lemma cdcl_dpll_bnb_r_stgy_additional_lit_notin:
  assumes \<open>cdcl_dpll_bnb_r_stgy S T\<close> and \<open>additional_lit_notin S\<close> and
    struct: \<open>reasons_in_clauses S\<close>
  shows \<open>additional_lit_notin T\<close>
  using assms(1,2)
  apply (cases)
  subgoal
    by (auto simp: additional_lit_notin_def elim!: rulesE)
  subgoal
    by (auto simp: additional_lit_notin_def elim!: rulesE)
  subgoal
    by (auto simp: additional_lit_notin_def elim!: rulesE enc_weight_opt.improveE)
  subgoal
    by (clarsimp simp: additional_lit_notin_def
      elim!: rulesE conflict_opt0E)
  subgoal
    apply (clarsimp simp: additional_lit_notin_def
      elim!: rulesE odecideE simple_backtrack_conflict_optE is_decided_ex_Decided
      dest: backtrack_split_trailD)
      apply (auto dest: backtrack_split_trailD
        simp: DECO_clause_def uminus_lit_swap
	  eq_commute[of \<open>Pos _\<close>]
      elim: is_decided_ex_Decided)
    done
  subgoal
    apply (cases rule: ocdcl\<^sub>W_o_r.cases, assumption)
    subgoal
      by (auto simp: additional_lit_notin_def
        elim!: rulesE odecideE)
    subgoal
      apply (cases rule: enc_weight_opt.cdcl_bnb_bj.cases, assumption)
      subgoal
        by (auto elim!: rulesE odecideE  enc_weight_opt.obacktrackE
	   simp: additional_lit_notin_def)
      subgoal
        using struct unfolding reasons_in_clauses_def
	by (cases \<open>trail S\<close>)
          (auto elim!: rulesE odecideE  enc_weight_opt.obacktrackE
	   dest!: in_diffD
	   simp: additional_lit_notin_def)
      subgoal
        by (auto elim!: rulesE odecideE  enc_weight_opt.obacktrackE
	   simp: additional_lit_notin_def mset_subset_eq_exists_conv)
      done
    done
  done

definition additional_lit_notin_both :: \<open>'st \<Rightarrow> bool\<close> where
  \<open>additional_lit_notin_both S \<longleftrightarrow>
     (\<forall>A\<in>\<Delta>\<Sigma>. \<forall>C \<in># learned_clss S. Neg (replacement_pos A) \<in># C \<longrightarrow> Neg (replacement_neg A) \<in># C \<longrightarrow> False)\<close>

lemma replace_pos_neg_not_both_decided:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    dec0: \<open>Decided (Pos (A\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail S)\<close> and
    dec1: \<open>Decided (Pos (A\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail S)\<close> and
    add: \<open>additional_constraints \<subseteq># init_clss S\<close> and
    [simp]: \<open>A \<in> \<Delta>\<Sigma>\<close>
  shows False
proof -
  have add: \<open>additional_constraint A \<subseteq># init_clss S\<close>
    using add multi_member_split[of A \<open>mset_set \<Delta>\<Sigma>\<close>] by (auto simp: additional_constraints_def
      subset_mset.dual_order.trans)
  have n_d: \<open>no_dup (trail S)\<close>
    using struct unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  have H: \<open>\<And>M K M' D L.
     trail S = M' @ Decided K # M \<Longrightarrow>
     D + {#L#} \<in># additional_constraint A \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close>
    using smaller_propa add unfolding no_smaller_propa_def clauses_def by auto
  consider
    M1 M2 M3 where \<open>trail S = M3 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>0)) # M2 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>1)) # M1\<close> |
    M1 M2 M3 where \<open>trail S = M3 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>1)) # M2 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>0)) # M1\<close>
    using in_set_conv_decomp[THEN iffD1, OF dec0] dec1 by (auto 5 5 dest: in_set_conv_decomp[THEN iffD1])
  then show ?thesis
  proof cases
    case (1 M1 M2 M3)
    then show ?thesis
      using H[of \<open> M3\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>0)\<close> \<open>M2 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>1)) # M1\<close> \<open>{#Neg (A\<^sup>\<mapsto>\<^sup>1)#}\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>0)\<close>] n_d
      by (auto simp: additional_constraint_def defined_lit_map)
  next
    case 2
    then show ?thesis
      using H[of \<open>M3\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>1)\<close> \<open>M2 @ Decided (Pos (A\<^sup>\<mapsto>\<^sup>0)) # M1\<close> \<open>{#Neg (A\<^sup>\<mapsto>\<^sup>0)#}\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>1)\<close>] n_d
      by (auto simp: additional_constraint_def defined_lit_map)
  qed
qed

lemma replace_pos_neg_not_both_decided_highest_lvl:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>no_smaller_confl S\<close> and
    dec0: \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l (trail S)\<close> and
    dec1: \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l (trail S)\<close> and
    add: \<open>additional_constraints \<subseteq># init_clss S\<close> and
    [simp]: \<open>A \<in> \<Delta>\<Sigma>\<close>
  shows \<open>get_level (trail S) (Pos (A\<^sup>\<mapsto>\<^sup>0)) = backtrack_lvl S \<and>
     get_level (trail S) (Pos (A\<^sup>\<mapsto>\<^sup>1)) = backtrack_lvl S\<close>
proof (rule ccontr)
  assume neg: \<open>\<not>?thesis\<close>
  let ?L0 = \<open>get_level (trail S) (Pos (A\<^sup>\<mapsto>\<^sup>0))\<close>
  let ?L1 = \<open>get_level (trail S) (Pos (A\<^sup>\<mapsto>\<^sup>1))\<close>
  define KL where \<open>KL = (if ?L0 > ?L1 then (Pos (A\<^sup>\<mapsto>\<^sup>1)) else (Pos (A\<^sup>\<mapsto>\<^sup>0)))\<close>
  define KL' where \<open>KL' = (if ?L0 > ?L1 then (Pos (A\<^sup>\<mapsto>\<^sup>0)) else (Pos (A\<^sup>\<mapsto>\<^sup>1)))\<close>
  then have \<open>get_level (trail S) KL < backtrack_lvl S\<close> and
    le: \<open>?L0 < backtrack_lvl S \<or> ?L1 < backtrack_lvl S\<close>
      \<open>?L0 \<le> backtrack_lvl S \<and> ?L1 \<le> backtrack_lvl S\<close>
    using neg count_decided_ge_get_level[of \<open>trail S\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>0)\<close>]
      count_decided_ge_get_level[of \<open>trail S\<close> \<open>Pos (A\<^sup>\<mapsto>\<^sup>1)\<close>]
    unfolding KL_def
    by force+

  have \<open>KL \<in> lits_of_l (trail S)\<close>
    using dec1 dec0 by (auto simp: KL_def)
  have add: \<open>additional_constraint A \<subseteq># init_clss S\<close>
    using add multi_member_split[of A \<open>mset_set \<Delta>\<Sigma>\<close>] by (auto simp: additional_constraints_def
      subset_mset.dual_order.trans)
  have n_d: \<open>no_dup (trail S)\<close>
    using struct unfolding  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  have H: \<open>\<And>M K M' D L.
     trail S = M' @ Decided K # M \<Longrightarrow>
     D + {#L#} \<in># additional_constraint A \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close> and
    H': \<open>\<And>M K M' D L.
     trail S = M' @ Decided K # M \<Longrightarrow>
     D \<in># additional_constraint A \<Longrightarrow>  \<not> M \<Turnstile>as CNot D\<close>
    using smaller_propa add smaller_confl unfolding no_smaller_propa_def no_smaller_confl_def clauses_def
    by auto

  have L1_L0: \<open>?L1 = ?L0\<close>
  proof (rule ccontr)
    assume neq: \<open>?L1 \<noteq> ?L0\<close>
    define i where \<open>i \<equiv> min ?L1 ?L0\<close>
    obtain K M1 M2 where
      decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
      \<open>get_level (trail S) K = Suc i\<close>
      using backtrack_ex_decomp[OF n_d, of i] neq le
      by (cases \<open>?L1 < ?L0\<close>) (auto simp: min_def i_def)
    have \<open>get_level (trail S) KL \<le> i\<close> and \<open>get_level (trail S) KL' > i\<close>
      using neg neq le by (auto simp: KL_def KL'_def i_def)
    then have \<open>undefined_lit M1 KL'\<close>
      using n_d decomp \<open>get_level (trail S) K = Suc i\<close>
         count_decided_ge_get_level[of \<open>M1\<close> KL']
      by (force  dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if atm_of_eq_atm_of
	dest: defined_lit_no_dupD
	split: if_splits)
    moreover have \<open>{#-KL', -KL#} \<in># additional_constraint A\<close>
      using neq by (auto simp: additional_constraint_def KL_def KL'_def)
    moreover have \<open>KL \<in> lits_of_l M1\<close>
      using \<open>get_level (trail S) KL \<le> i\<close> \<open>get_level (trail S) K = Suc i\<close>
       n_d decomp \<open>KL \<in> lits_of_l (trail S)\<close>
         count_decided_ge_get_level[of \<open>M1\<close> KL]
      by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: get_level_append_if get_level_cons_if atm_of_eq_atm_of
	dest: defined_lit_no_dupD in_lits_of_l_defined_litD
	split: if_splits)
    ultimately show False
      using H[of _ K M1 \<open>{#-KL#}\<close> \<open>-KL'\<close>] decomp
      by force
  qed

  obtain K M1 M2 where
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
    lev_K: \<open>get_level (trail S) K = Suc ?L1\<close>
    using backtrack_ex_decomp[OF n_d, of ?L1] le
    by (cases \<open>?L1 < ?L0\<close>) (auto simp: min_def L1_L0)
  then obtain M3 where
    M3: \<open>trail S = M3 @ Decided K # M1\<close>
    by auto
  then have [simp]: \<open>undefined_lit M3 (Pos (A\<^sup>\<mapsto>\<^sup>1))\<close>  \<open>undefined_lit M3 (Pos (A\<^sup>\<mapsto>\<^sup>0))\<close>
    by (solves \<open>use n_d L1_L0 lev_K M3 in auto\<close>)
      (solves \<open>use n_d L1_L0[symmetric] lev_K M3 in auto\<close>)
  then have [simp]: \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<notin> lits_of_l M3\<close>  \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<notin> lits_of_l M3\<close>
    using Decided_Propagated_in_iff_in_lits_of_l by blast+
  have \<open>Pos (A\<^sup>\<mapsto>\<^sup>1) \<in> lits_of_l M1\<close>  \<open>Pos (A\<^sup>\<mapsto>\<^sup>0) \<in> lits_of_l M1\<close>
    using n_d L1_L0 lev_K dec0 dec1 Decided_Propagated_in_iff_in_lits_of_l
    by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: M3 get_level_cons_if
	split: if_splits)
  then show False
    using H'[of M3 K M1 \<open>{#Neg (A\<^sup>\<mapsto>\<^sup>0), Neg (A\<^sup>\<mapsto>\<^sup>1)#}\<close>]
    by (auto simp: additional_constraint_def M3)
qed

lemma cdcl_dpll_bnb_r_stgy_additional_lit_notin_both:
  assumes \<open>cdcl_dpll_bnb_r_stgy S T\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>no_smaller_confl S\<close> and
    notin: \<open>additional_lit_notin S\<close> and
    reasons: \<open>reasons_in_clauses S\<close> and
    notin_both: \<open>additional_lit_notin_both S\<close> and
    add: \<open>additional_constraints \<subseteq># init_clss S\<close>
  shows \<open>additional_lit_notin_both T\<close>
  using assms(1)
proof cases
  case cdcl_dpll_bnb_r_conflict
  then show ?thesis using notin_both by (auto elim!: rulesE simp: additional_lit_notin_both_def)
next
  case cdcl_dpll_bnb_r_propagate
  then show ?thesis using notin_both by (auto elim!: rulesE simp: additional_lit_notin_both_def)
next
  case cdcl_dpll_bnb_r_improve
  then show ?thesis using notin_both by (auto elim!: enc_weight_opt.improveE simp: additional_lit_notin_both_def)
next
  case cdcl_dpll_bnb_r_conflict_opt0
  then show ?thesis using notin_both by (auto elim!: conflict_opt0E simp: additional_lit_notin_both_def)
next
  case cdcl_dpll_bnb_r_simple_backtrack_conflict_opt
  then show ?thesis
    using notin_both notin replace_pos_neg_not_both_decided[of S, OF struct smaller_propa _ _ add]
    by (fastforce elim!: simple_backtrack_conflict_optE
      simp: additional_lit_notin_both_def additional_lit_notin_def DECO_clause_def
        eq_commute[of \<open>Neg _\<close>] uminus_lit_swap additional_constraints_def
      elim!: is_decided_ex_Decided)
next
  case cdcl_dpll_bnb_r_other'
  then show ?thesis
  proof cases
    case decide
    then show ?thesis using notin_both by (auto elim!: odecideE simp: additional_lit_notin_both_def)
  next
    case bj
    then show ?thesis
    proof cases
      case skip
      then show ?thesis using notin_both by (auto elim!: rulesE simp: additional_lit_notin_both_def)
    next
      case resolve
      then show ?thesis using notin_both by (auto elim!: rulesE simp: additional_lit_notin_both_def)
    next
      case backtrack
      then obtain M1 M2 :: \<open>('v, 'v clause) ann_lits\<close> and K L :: \<open>'v literal\<close> and
          D D' :: \<open>'v clause\<close> where
	confl: \<open>conflicting S = Some (add_mset L D)\<close> and
	decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
	max: \<open>get_maximum_level (trail S) (add_mset L D') = local.backtrack_lvl S\<close> and
	lev_L: \<open>get_level (trail S) L = local.backtrack_lvl S\<close> and
	max_le: \<open>get_level (trail S) K = Suc (get_maximum_level (trail S) D')\<close> and
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
	n_d: \<open>no_dup (trail S)\<close>
        using struct confl
	unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
	by auto
      have tr_D': \<open>trail S \<Turnstile>as CNot (add_mset L D')\<close>
        using tr_D D'_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      define D'' where \<open>D'' \<equiv> add_mset L D'\<close>
      then have D'_D'': \<open>D' = remove1_mset L D''\<close> \<open>L \<in># D''\<close>
        by auto
      have \<open>get_level (trail S) K \<le> count_decided (trail S)\<close>
        using decomp n_d
	by (auto dest!: get_all_ann_decomposition_exists_prepend
	  dest: defined_lit_no_dupD in_lits_of_l_defined_litD)
      then have False if
         \<open>A \<in> \<Delta>\<Sigma>\<close> \<open>Neg (A\<^sup>\<mapsto>\<^sup>1) \<in># add_mset L D'\<close>\<open>Neg (A\<^sup>\<mapsto>\<^sup>0) \<in># add_mset L D'\<close> for A
        using tr_D' that(1,3) multi_member_split[OF that(2)]  multi_member_split[OF that(3)]
         replace_pos_neg_not_both_decided_highest_lvl[OF struct smaller_propa smaller_confl
        _ _ add, of A] tr_D' notin_both max_le lev_L
	count_decided_ge_get_maximum_level[of \<open>trail S\<close> \<open>D'\<close>]
	unfolding D''_def[symmetric] unfolding D'_D''
	by (auto dest!: simp: add_mset_eq_add_mset get_maximum_level_add_mset
	  get_level_Neg_Pos max_def remove1_mset_add_mset_If split: if_splits)
      then show ?thesis
        using T notin_both
        by (auto simp: additional_lit_notin_both_def
	  dest!: enc_weight_opt.obacktrackE)
    qed
  qed
qed

lemma cdcl_dpll_bnb_r_stgy_clauses_mono:
  \<open>cdcl_dpll_bnb_r_stgy S T \<Longrightarrow> clauses S \<subseteq># clauses T\<close>
  by (cases rule: cdcl_dpll_bnb_r_stgy.cases, assumption)
    (auto elim!: rulesE obacktrackE enc_weight_opt.improveE
         conflict_opt0E simple_backtrack_conflict_optE odecideE
	 enc_weight_opt.obacktrackE
      simp: ocdcl\<^sub>W_o_r.simps  enc_weight_opt.cdcl_bnb_bj.simps)

lemma rtranclp_cdcl_dpll_bnb_r_stgy_clauses_mono:
  \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> clauses S \<subseteq># clauses T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: cdcl_dpll_bnb_r_stgy_clauses_mono)

lemma cdcl_dpll_bnb_r_stgy_init_clss_eq:
  \<open>cdcl_dpll_bnb_r_stgy S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by (cases rule: cdcl_dpll_bnb_r_stgy.cases, assumption)
    (auto elim!: rulesE obacktrackE enc_weight_opt.improveE
         conflict_opt0E simple_backtrack_conflict_optE odecideE
	 enc_weight_opt.obacktrackE
      simp: ocdcl\<^sub>W_o_r.simps  enc_weight_opt.cdcl_bnb_bj.simps)

lemma rtranclp_cdcl_dpll_bnb_r_stgy_init_clss_eq:
  \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> init_clss S = init_clss T\<close>
  by (induction rule: rtranclp_induct) (auto dest!: cdcl_dpll_bnb_r_stgy_init_clss_eq)


context
  fixes S :: 'st
  assumes S_\<Sigma>: \<open>atms_of_mm (init_clss S) = \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
begin

lemma rtranclp_cdcl_dpll_bnb_r_stgy_additional_lit_notin_both:
  assumes \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* S T\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>cdcl_bnb_stgy_inv S\<close> and
    notin: \<open>additional_lit_notin S\<close> and
    reasons: \<open>reasons_in_clauses S\<close> and
    notin_both: \<open>additional_lit_notin_both S\<close> and
    add: \<open>additional_constraints \<subseteq># init_clss S\<close> and
    confl_false_lev: \<open>conflict_is_false_with_level S\<close>
  shows \<open>additional_lit_notin T \<and> additional_lit_notin_both T\<close>
  using assms(1)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using assms by auto
next
  case (step T U) note st = this(1) and step = this(2) and IH = this(3)
  have st': \<open>cdcl_bnb_r_stgy\<^sup>*\<^sup>* S T\<close>
    using rtranclp_cdcl_dpll_bnb_r_stgy_cdcl_bnb_r[OF S_\<Sigma> st struct] .
  have st'': \<open>enc_weight_opt.cdcl_bnb_stgy\<^sup>*\<^sup>* S T\<close>
    using rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_stgy[OF S_\<Sigma> st'] .
  from rtranclp_cdcl_bnb_r_stgy_cdcl_bnb_r[OF st'] have st': \<open>cdcl_bnb_r\<^sup>*\<^sup>* S T\<close> .
  have stgy_inv: \<open>cdcl_bnb_stgy_inv T\<close>
    using enc_weight_opt.rtranclp_cdcl_bnb_stgy_stgy_inv[OF st'' struct smaller_confl] .
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state T)\<close>
    using rtranclp_cdcl_bnb_r_all_struct_inv[OF S_\<Sigma> st' struct] .
  moreover have \<open>no_smaller_propa T\<close>
    using enc_weight_opt.rtranclp_cdcl_bnb_stgy_no_smaller_propa[OF st'' struct smaller_propa] .
  moreover have \<open>no_smaller_confl T\<close>
    using stgy_inv unfolding cdcl_bnb_stgy_inv_def by blast
  moreover have \<open>reasons_in_clauses T\<close>
    using rtranclp_cdcl_dpll_bnb_r_stgy_reasons_in_clauses[OF st reasons] .
  moreover have \<open>additional_constraints \<subseteq># init_clss T\<close>
    using rtranclp_cdcl_dpll_bnb_r_stgy_init_clss_eq[OF st] add by auto
  ultimately show ?case
    using cdcl_dpll_bnb_r_stgy_additional_lit_notin_both[of T U] step IH
      cdcl_dpll_bnb_r_stgy_additional_lit_notin[of T U]
    by auto
qed

end

lemma rtranclp_cdcl_dpll_bnb_r_stgy_additional_lit_notin_both_init_state:
  assumes \<open>cdcl_dpll_bnb_r_stgy\<^sup>*\<^sup>* (init_state (penc N)) T\<close> and
    atm: \<open>atms_of_mm N = \<Sigma>\<close> \<open>\<Delta>\<Sigma> \<subseteq> atms_of_mm N\<close> and
    [simp]: \<open>distinct_mset_mset (penc N)\<close>
  shows \<open>additional_lit_notin T \<and> additional_lit_notin_both T\<close>
  apply (rule rtranclp_cdcl_dpll_bnb_r_stgy_additional_lit_notin_both[of \<open>init_state (penc N)\<close>])
  subgoal
    using atm atms_of_mm_penc_subset2[of N]
    by auto
  subgoal
    using assms(1) .
  subgoal
    by (auto simp: all_struct_init_state_distinct_iff)
  subgoal
    by (auto simp: no_smaller_propa_def)
  subgoal
    by (auto simp: enc_weight_opt.cdcl_bnb_stgy_inv_def
      conflict_is_false_with_level_def)
  subgoal
    apply (auto simp: additional_lit_notin_def)
(*    sorry
  subgoal
    by (auto simp: reasons_in_clauses_def)
  subgoal
    by (auto simp: additional_lit_notin_both_def penc_def encode_clauses_def
      additional_constraints_def additional_constraint_def)
  subgoal
    by (auto simp: additional_lit_notin_both_def penc_def encode_clauses_def
      additional_constraints_def additional_constraint_def)
  subgoal
    by (auto simp: conflict_is_false_with_level_def)
  done
*)
oops

context
  fixes S :: 'st and N :: \<open>'v clauses\<close>
  assumes S_\<Sigma>: \<open>init_clss S = penc N\<close>
begin

lemma replacement_pos_neg_defined_same_lvl:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    A: \<open>A \<in> \<Delta>\<Sigma>\<close> and
    lev: \<open>get_level (trail S) (Pos (replacement_pos A)) < backtrack_lvl S\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>cdcl_bnb_stgy_inv S\<close>
  shows
    \<open>Pos (replacement_pos A) \<in> lits_of_l (trail S) \<Longrightarrow>
      Neg (replacement_neg A) \<in> lits_of_l (trail S)\<close>
proof -
  have n_d: \<open>no_dup (trail S)\<close>
    using struct
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
    have H: \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D + {#L#} \<in># additional_constraint A \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close> and
      H': \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D \<in># additional_constraint A \<Longrightarrow>  \<not> M \<Turnstile>as CNot D\<close>
    using smaller_propa S_\<Sigma> A smaller_confl unfolding no_smaller_propa_def clauses_def penc_def
      additional_constraints_def cdcl_bnb_stgy_inv_def no_smaller_confl_def by fastforce+

  show \<open>Neg (replacement_neg A) \<in> lits_of_l (trail S)\<close>
    if Pos: \<open>Pos (replacement_pos A) \<in> lits_of_l (trail S)\<close>
  proof -
    obtain M1 M2 K where
      \<open>trail S = M2 @ Decided K # M1\<close> and
      \<open>Pos (replacement_pos A) \<in> lits_of_l M1\<close>
      using lev n_d Pos by (force dest!: split_list elim!: is_decided_ex_Decided
        simp: lits_of_def count_decided_def filter_empty_conv)
    then show \<open>Neg (replacement_neg A) \<in> lits_of_l (trail S)\<close>
      using H[of M2 K M1 \<open>{#Neg (replacement_pos A)#}\<close> \<open>Neg (replacement_neg A)\<close>]
        H'[of M2 K M1 \<open>{#Neg (replacement_pos A), Neg (replacement_neg A)#}\<close>]
	by (auto simp: additional_constraint_def Decided_Propagated_in_iff_in_lits_of_l)
  qed
qed


lemma replacement_pos_neg_defined_same_lvl':
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    A: \<open>A \<in> \<Delta>\<Sigma>\<close> and
    lev: \<open>get_level (trail S) (Pos (replacement_neg A)) < backtrack_lvl S\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>cdcl_bnb_stgy_inv S\<close>
  shows
    \<open>Pos (replacement_neg A) \<in> lits_of_l (trail S) \<Longrightarrow>
      Neg (replacement_pos A) \<in> lits_of_l (trail S)\<close>
proof -
  have n_d: \<open>no_dup (trail S)\<close>
    using struct
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
    have H: \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D + {#L#} \<in># additional_constraint A \<Longrightarrow> undefined_lit M L \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close> and
      H': \<open>\<And>M K M' D L.
        trail S = M' @ Decided K # M \<Longrightarrow>
        D \<in># additional_constraint A \<Longrightarrow>  \<not> M \<Turnstile>as CNot D\<close>
    using smaller_propa S_\<Sigma> A smaller_confl unfolding no_smaller_propa_def clauses_def penc_def
      additional_constraints_def cdcl_bnb_stgy_inv_def no_smaller_confl_def by fastforce+

  show \<open>Neg (replacement_pos A) \<in> lits_of_l (trail S)\<close>
    if Pos: \<open>Pos (replacement_neg A) \<in> lits_of_l (trail S)\<close>
  proof -
    obtain M1 M2 K where
      \<open>trail S = M2 @ Decided K # M1\<close> and
      \<open>Pos (replacement_neg A) \<in> lits_of_l M1\<close>
      using lev n_d Pos by (force dest!: split_list elim!: is_decided_ex_Decided
        simp: lits_of_def count_decided_def filter_empty_conv)
    then show \<open>Neg (replacement_pos A) \<in> lits_of_l (trail S)\<close>
      using H[of M2 K M1 \<open>{#Neg (replacement_neg A)#}\<close> \<open>Neg (replacement_pos A)\<close>]
        H'[of M2 K M1 \<open>{#Neg (replacement_neg A), Neg (replacement_pos A)#}\<close>]
	by (auto simp: additional_constraint_def Decided_Propagated_in_iff_in_lits_of_l)
  qed
qed

lemma
  assumes
    \<open>enc_weight_opt.cdcl_bnb_stgy S T\<close> and
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (enc_weight_opt.abs_state S)\<close> and
    dist: \<open>distinct_mset (normalize_clause `# learned_clss S)\<close> and
    smaller_propa: \<open>no_smaller_propa S\<close> and
    smaller_confl: \<open>cdcl_bnb_stgy_inv S\<close>
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
	decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))\<close> and
	\<open>get_maximum_level (trail S) (add_mset L D') = local.backtrack_lvl S\<close> and
	\<open>get_level (trail S) L = local.backtrack_lvl S\<close> and
	lev_K: \<open>get_level (trail S) K = Suc (get_maximum_level (trail S) D')\<close> and
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
	\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (abs_state S)\<close> and
	n_d: \<open>no_dup (trail S)\<close>
        using struct confl
	unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
	  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
	  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
	by auto
      have tr_D': \<open>trail S \<Turnstile>as CNot (add_mset L D')\<close>
        using D'_D tr_D
	by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
      have \<open>normalize_lit L2 \<in> lits_of_l (trail S) \<longleftrightarrow> L2 \<in> lits_of_l (trail S)\<close>
        if \<open>L2 \<in># D'\<close>
	for L2
      proof -
        have \<open>get_level (trail S) L2 < backtrack_lvl S\<close>
	  using multi_member_split[OF that(1)] tr_D lev_K
	    count_decided_ge_get_level[of \<open>trail S\<close> K]
	  by (auto simp: get_maximum_level_add_mset max_def
	    split: if_splits)
	moreover have \<open>-L2 \<in> lits_of_l (trail S)\<close>
	  using tr_D that D'_D
	  by (auto dest!: multi_member_split
	    simp: subset_mset.le_iff_add)
	ultimately show ?thesis
	  using replacement_pos_neg_defined_same_lvl[OF struct _ _ smaller_propa
	      smaller_confl]
	    replacement_pos_neg_defined_same_lvl'[OF struct _ _ smaller_propa
	    smaller_confl]
	  apply (cases L2)
	  apply (auto simp: get_level_Neg_Pos)
	  prefer 2
	oops
	find_theorems get_level Pos Neg
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