(*  Title: Invariants of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Two Watched-Literals with invariant\<close>

theory CDCL_Two_Watched_Literals_Invariant
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
begin

subsubsection \<open>Interpretation for @{term conflict_driven_clause_learning\<^sub>W.cdcl\<^sub>W_restart}\<close>

text \<open>We define here the 2-WL with the invariant of well-foundedness and show the role of the
  candidates by defining an equivalent CDCL procedure using the candidates given by the
  datastructure.\<close>
context abstract_twl
begin

paragraph \<open>Direct Interpretation\<close>
lemma mset_map_removeAll_cond:
  "mset (map clause
    (removeAll_cond (\<lambda>D. clause D = clause C) N))
  = mset (removeAll (clause C) (map clause N))"
  by (induction N) auto

lemma raw_clss_l_raw_init_clss_conc_init_clss[simp]:
  "raw_clss_l (raw_init_clss S) = twl.conc_init_clss S"
  by (cases S) auto

lemma mset_raw_init_clss_init_state:
  "raw_clss_l (raw_init_clss (init_state (map raw_clause N))) = raw_clss_l N"
  unfolding raw_clss_l_raw_init_clss_conc_init_clss
  by (metis (full_types) clause_def comp_def init_clss_init_state map_eq_conv map_map)

fun reduce_trail_to where
"reduce_trail_to M1 S =
  (case S of
    (TWL_State M N U k C) \<Rightarrow> TWL_State (drop (length M - length M1) M) N U k C)"

abbreviation resolve_conflicting where
"resolve_conflicting L D S \<equiv>
  update_conflicting
  (Some (union_mset_list (remove1 (-L) (the (raw_conflicting S))) (remove1 L (raw_clause D))))
  S"

(* interpretation twl: abs_state\<^sub>W_ops where
    cls_lit = "\<lambda>_ L. L" and
    in_cls = "\<lambda>L C. L \<in> set (raw_clause C)" and
    mset_cls = clause and
   
    clss_cls = "\<lambda>_ C. C" and
    in_clss = "\<lambda>C Cs. C \<in> set Cs" and
    mset_clss = mset and

    mset_ccls = mset and

    conc_trail = trail and  
    hd_raw_conc_trail = "\<lambda>S. hd (raw_trail S)" and
    conc_backtrack_lvl = backtrack_lvl and
    raw_conc_conflicting = raw_conflicting and
    conc_learned_clss = conc_learned_clss and

    cons_conc_trail = cons_trail and 
    tl_conc_trail = tl_trail and 
    add_conc_confl_to_learned_cls = 
      "\<lambda>S. update_conflicting None (add_learned_cls (the (raw_conflicting S)) S)" and
    remove_cls = "\<lambda>C. remove_cls (raw_clause C)" and
    update_conc_backtrack_lvl = update_backtrack_lvl and
    mark_conflicting = "\<lambda>C. update_conflicting (Some (raw_clause C))" and 
    reduce_conc_trail_to = reduce_trail_to and 
    resolve_conflicting = resolve_conflicting and
    conc_init_state = "\<lambda>N. init_state (map raw_clause N)" and 
    restart_state = restart'
  rewrites
    "twl.mmset_of_mlit S = mmset_of_mlit"
proof goal_cases
  case 1
  show H: ?case by unfold_locales

  case 2
  show ?case
    apply (rule ext)
    apply (rename_tac x)
    apply (case_tac x)
    apply (simp_all add: abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF H] raw_clause_def clause_def)
  done
qed *)

lemma raw_clss_l_twl_clauses_of_clss[simp]:
  "raw_clss_l = twl.clauses_of_clss"
  by (rule ext) (metis twl.clauses_of_clss_def twl.raw_clss_l_raw_clss)

interpretation twl: abs_state\<^sub>W where
    cls_lit = "\<lambda>_ L. L" and
    in_cls = "\<lambda>L C. L \<in> set (raw_clause C)" and
    mset_cls = clause and
   
    clss_cls = "\<lambda>_ C. C" and
    in_clss = "\<lambda>C Cs. C \<in> set Cs" and
    mset_clss = mset and

    mset_ccls = mset and

    conc_trail = trail and  
    hd_raw_conc_trail = "\<lambda>S. hd (raw_trail S)" and
    conc_backtrack_lvl = backtrack_lvl and
    raw_conc_conflicting = raw_conflicting and
    conc_learned_clss = conc_learned_clss and
    raw_clauses = raw_clauses and

    cons_conc_trail = cons_trail and 
    tl_conc_trail = tl_trail and 
    add_conc_confl_to_learned_cls = 
      "\<lambda>S. update_conflicting None (add_learned_cls (the (raw_conflicting S)) S)" and
    remove_cls = "\<lambda>C. remove_cls (raw_clause C)" and
    update_conc_backtrack_lvl = update_backtrack_lvl and
    mark_conflicting = "\<lambda>C. update_conflicting (Some (raw_clause C))" and 
    reduce_conc_trail_to = reduce_trail_to and 
    resolve_conflicting = resolve_conflicting and
    conc_init_state = "\<lambda>N. init_state (map raw_clause N)" and 
    restart_state = restart'
proof goal_cases
  case 1
  have [simp]: "\<And>S (L :: ('v, 'v twl_clause) ann_lit). abs_state\<^sub>W_ops.mmset_of_mlit clause 
    (\<lambda>(_::'v twl_clause list) C::'v twl_clause. C) (S ::'v twl_clause list) L =
    mmset_of_mlit L"
    by (case_tac L) 
    (auto simp: abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF twl.abs_state\<^sub>W_ops_axioms]
      clause_def raw_clause_def)
 
  have [simp]: "\<And>S. raw_clss_l (restart_learned S) \<subseteq># conc_learned_clss S"
    using image_mset_subseteq_mono[OF restart_learned] unfolding mset_map
     by blast
  have [simp]: "conc_learned_clss S \<subseteq># twl.conc_clauses S" for S
    by (metis (mono_tags, lifting) map_append mset_append mset_le_add_right twl.conc_clauses_def
      twl.raw_clss_l_raw_clss)
  have [simp]: "mset (removeAll (clause C) (map clause (raw_init_clss st))) =
       removeAll_mset (clause C) (twl.conc_init_clss st)" for st C
    unfolding mset_removeAll[symmetric] by (auto simp: twl.conc_init_clss_def)
  thm abs_state\<^sub>W_ops.state_def[OF twl.abs_state\<^sub>W_ops_axioms]
  have H: "\<And>M2 M1 x1. M2 @ M1 = map mmset_of_mlit x1 \<Longrightarrow>
       map mmset_of_mlit (drop (length x1 - length M1) x1) = M1"
    by (metis add_diff_cancel_right' append_eq_conv_conj drop_map length_append length_map)
  show H: ?case
    apply unfold_locales
    apply (case_tac "raw_trail st"; case_tac "hd (raw_trail st)")
    unfolding abs_state\<^sub>W_ops.state_def[OF twl.abs_state\<^sub>W_ops_axioms]
    raw_clss_l_twl_clauses_of_clss[symmetric] 
    by (auto simp add: add_init_cls_def add_learned_cls_def clause_rewatch clause_watch
      cons_trail_def remove_cls_def restart'_def tl_trail_def map_tl comp_def
      ac_simps mset_map_removeAll_cond mset_raw_init_clss_init_state twl.state_def
      clause_def[symmetric] H union_mset_list[symmetric] split: twl_state.splits)
qed

interpretation rough_cdcl: abs_conflict_driven_clause_learning\<^sub>W where
    cls_lit = "\<lambda>_ L. L" and
    in_cls = "\<lambda>L C. L \<in> set (raw_clause C)" and
    mset_cls = clause and
   
    clss_cls = "\<lambda>_ C. C" and
    in_clss = "\<lambda>C Cs. C \<in> set Cs" and
    mset_clss = mset and

    mset_ccls = mset and

    conc_trail = trail and  
    hd_raw_conc_trail = "\<lambda>S. hd (raw_trail S)" and
    conc_backtrack_lvl = backtrack_lvl and
    raw_conc_conflicting = raw_conflicting and
    conc_learned_clss = conc_learned_clss and
    raw_clauses = raw_clauses and

    cons_conc_trail = cons_trail and 
    tl_conc_trail = tl_trail and 
    add_conc_confl_to_learned_cls = 
      "\<lambda>S. update_conflicting None (add_learned_cls (the (raw_conflicting S)) S)" and
    remove_cls = "\<lambda>C. remove_cls (raw_clause C)" and
    update_conc_backtrack_lvl = update_backtrack_lvl and
    mark_conflicting = "\<lambda>C. update_conflicting (Some (raw_clause C))" and 
    reduce_conc_trail_to = reduce_trail_to and 
    resolve_conflicting = resolve_conflicting and
    conc_init_state = "\<lambda>N. init_state (map raw_clause N)" and 
    restart_state = restart'
  by unfold_locales

paragraph \<open>Opaque Type with Invariant\<close>

declare twl.state_simp[simp del]

definition cons_trail_twl :: "('v, 'v twl_clause) ann_lit \<Rightarrow> 'v wf_twl \<Rightarrow> 'v wf_twl"
  where
"cons_trail_twl L S = twl_of_rough_state (cons_trail L (rough_state_of_twl S))"

lemma wf_twl_state_cons_trail:
  assumes
    undef: "undefined_lit (raw_trail S) (lit_of L)" and
    wf: "wf_twl_state S"
  shows "wf_twl_state (cons_trail L S)"
  using undef wf wf_rewatch[of S ] unfolding wf_twl_state_def Ball_def
  by (auto simp: cons_trail_def defined_lit_map comp_def image_def
    twl.conc_clauses_init_learned)

lemma rough_state_of_twl_cons_trail:
  "undefined_lit (raw_trail_twl S) (lit_of L) \<Longrightarrow>
    rough_state_of_twl (cons_trail_twl L S) = cons_trail L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_cons_trail
  unfolding cons_trail_twl_def by blast

abbreviation add_init_cls_twl where
"add_init_cls_twl C S \<equiv> twl_of_rough_state (add_init_cls C (rough_state_of_twl S))"

lemma wf_twl_add_init_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_init_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_init_cls_def comp_def
    twl.conc_clauses_init_learned
    split: if_split_asm)

lemma rough_state_of_twl_add_init_cls:
  "rough_state_of_twl (add_init_cls_twl L S) = add_init_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_init_cls by blast

abbreviation add_learned_cls_twl where
"add_learned_cls_twl C S \<equiv> twl_of_rough_state (add_learned_cls C (rough_state_of_twl S))"

lemma wf_twl_add_learned_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_learned_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_learned_cls_def
    twl.conc_clauses_init_learned
    split: if_split_asm)

lemma rough_state_of_twl_add_learned_cls:
  "rough_state_of_twl (add_learned_cls_twl L S) = add_learned_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_learned_cls by blast

abbreviation remove_cls_twl where
"remove_cls_twl C S \<equiv> twl_of_rough_state (remove_cls C (rough_state_of_twl S))"

lemma set_removeAll_condD: "x \<in> set (removeAll_cond f xs) \<Longrightarrow> x \<in> set xs"
  by (induction xs) (auto split: if_split_asm)

lemma wf_twl_remove_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (remove_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch remove_cls_def
    comp_def split: if_split_asm dest: set_removeAll_condD)

lemma rough_state_of_twl_remove_cls:
  "rough_state_of_twl (remove_cls_twl L S) = remove_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_remove_cls by blast

abbreviation init_state_twl where
"init_state_twl N \<equiv> twl_of_rough_state (init_state N)"

lemma wf_twl_state_wf_twl_state_fold_add_init_cls:
  assumes "wf_twl_state S"
  shows "wf_twl_state (fold add_init_cls N S)"
  using assms apply (induction N arbitrary: S)
   apply (auto simp: wf_twl_state_def)[]
  by (simp add: wf_twl_add_init_cls)

lemma wf_twl_state_epsilon_state[simp]:
  "wf_twl_state (TWL_State [] [] [] 0 None)"
  by (auto simp: wf_twl_state_def)

lemma wf_twl_init_state: "wf_twl_state (init_state N)"
  unfolding init_state_def by (auto intro!: wf_twl_state_wf_twl_state_fold_add_init_cls)

lemma rough_state_of_twl_init_state:
  "rough_state_of_twl (init_state_twl N) = init_state N"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state)

abbreviation tl_trail_twl where
"tl_trail_twl S \<equiv> twl_of_rough_state (tl_trail (rough_state_of_twl S))"

lemma wf_twl_state_tl_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (tl_trail S)"
  by (auto simp add: twl_of_rough_state_inverse wf_twl_init_state wf_twl_cls_wf_twl_cls_tl
    tl_trail_def wf_twl_state_def distinct_tl map_tl comp_def)

lemma rough_state_of_twl_tl_trail:
  "rough_state_of_twl (tl_trail_twl S) = tl_trail (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_tl_trail by blast

abbreviation update_backtrack_lvl_twl where
"update_backtrack_lvl_twl k S \<equiv> twl_of_rough_state (update_backtrack_lvl k (rough_state_of_twl S))"

lemma wf_twl_state_update_backtrack_lvl:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_backtrack_lvl k S)"
  unfolding wf_twl_state_def by (auto simp: comp_def)

lemma rough_state_of_twl_update_backtrack_lvl:
  "rough_state_of_twl (update_backtrack_lvl_twl k S) = update_backtrack_lvl k
    (rough_state_of_twl S)"
  using rough_state_of_twl
    twl_of_rough_state_inverse[of "update_backtrack_lvl k (rough_state_of_twl S)"]
    wf_twl_state_update_backtrack_lvl[of "rough_state_of_twl S" k] by fast

abbreviation update_conflicting_twl where
"update_conflicting_twl k S \<equiv> twl_of_rough_state (update_conflicting k (rough_state_of_twl S))"

lemma wf_twl_state_update_conflicting:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_conflicting k S)"
  unfolding wf_twl_state_def by (auto simp: comp_def)

lemma rough_state_of_twl_update_add_learned_cls:
  "rough_state_of_twl (update_conflicting_twl None (add_learned_cls_twl C S)) =
    update_conflicting None (add_learned_cls C (rough_state_of_twl S))"
    (is "rough_state_of_twl ?upd = update_conflicting None ?le")
  using rough_state_of_twl[of ?upd] twl_of_rough_state_inverse
    wf_twl_add_learned_cls[of "rough_state_of_twl S" C]
   wf_twl_state_update_conflicting[of ?le None]
  by fastforce

abbreviation reduce_trail_to_twl where
"reduce_trail_to_twl M1 S \<equiv> twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl S))"

abbreviation resolve_conflicting_twl where
"resolve_conflicting_twl L D S \<equiv>
  twl_of_rough_state (resolve_conflicting L D (rough_state_of_twl S))"

lemma rough_state_of_twl_update_conflicting:
  "rough_state_of_twl (update_conflicting_twl k S) = update_conflicting k
    (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_update_conflicting by fast

abbreviation raw_clauses_twl where
"raw_clauses_twl S \<equiv> raw_clauses (rough_state_of_twl S)"

abbreviation restart_twl where
"restart_twl S \<equiv> twl_of_rough_state (restart' (rough_state_of_twl S))"
lemma mset_union_mset_setD:
  "mset A \<subseteq># mset B \<Longrightarrow> set A \<subseteq> set B"
  by auto

lemma wf_wf_restart': "wf_twl_state S \<Longrightarrow> wf_twl_state (restart' S)"
  unfolding restart'_def wf_twl_state_def apply standard
   apply clarify
   apply (rename_tac x)
   apply (subgoal_tac "wf_twl_cls (raw_trail S) x")
    apply (case_tac x)
  using restart_learned by (auto simp: comp_def dest: mset_union_mset_setD)

lemma rough_state_of_twl_restart_twl:
  "rough_state_of_twl (restart_twl S) = restart' (rough_state_of_twl S)"
  by (simp add: twl_of_rough_state_inverse wf_wf_restart')

lemma undefined_lit_trail_twl_raw_trail[iff]:
  "undefined_lit (trail_twl S) L \<longleftrightarrow> undefined_lit (raw_trail_twl S) L"
  by (auto simp: defined_lit_map image_image)


lemma wf_twl_reduce_trail_to:
  assumes "trail S = M2 @ M1" and wf: "wf_twl_state S"
  shows "wf_twl_state (reduce_trail_to M1 S)"
proof -
  obtain M N U k C where S: "S = TWL_State M N U k C"
    by (cases S)
  have n_d: "no_dup M"
    using wf by (auto simp: S comp_def wf_twl_state_def)
  have M: "M = take (length M - length M1) M @ drop (length M - length M1) M"
    by auto
  have [simp]: "no_dup (drop (length M - length M1) M)"
    using n_d by (metis distinct_drop drop_map)
  have "\<And>C. C \<in> set (raw_clauses S) \<Longrightarrow> wf_twl_cls (raw_trail S) C"
    using wf by (auto simp: S comp_def wf_twl_state_def)
  then show ?thesis
    unfolding wf_twl_state_def S
    using wf_twl_cls_append[of "take (length M - length M1) M" "drop (length M - length M1) M",
      unfolded M[symmetric]]
    by (simp_all add: n_d)
qed

lemma trail_twl_twl_rough_state_reduce_trail_to:
  assumes "trail_twl st = M2 @ M1"
  shows "trail_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st))) = M1"
proof -
  have "wf_twl_state (reduce_trail_to M1 (rough_state_of_twl st))"
    using wf_twl_reduce_trail_to assms by fastforce
  moreover
    have "length (trail_twl st) - length M1 = length M2"
      unfolding assms by auto
    then have "trail (reduce_trail_to M1 (rough_state_of_twl st)) = M1"
      apply (cases "rough_state_of_twl st")
      using assms by (auto simp: drop_map[symmetric])
  ultimately show ?thesis
    using twl_of_rough_state_inverse[of "reduce_trail_to M1 (rough_state_of_twl st)"]
    rough_state_of_twl[of st]
    by (auto simp add: assms)
qed

lemma twl_of_rough_state_reduce_trail_to:
  assumes "trail_twl st = M2 @ M1" and
    S: "twl.state (rough_state_of_twl st) = (M, S)"
  shows
    "twl.state
      (rough_state_of_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))) =
      (M1, S)" (is "?st") and
    "raw_init_clss_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = raw_init_clss_twl st" (is "?A") and
    "raw_learned_clss_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = raw_learned_clss_twl st" (is "?B") and
    "backtrack_lvl_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = backtrack_lvl_twl st" (is "?C") and
    "twl.conc_conflicting (rough_state_of_twl (twl_of_rough_state
         (reduce_trail_to M1 (rough_state_of_twl st))))
      = twl.conc_conflicting (rough_state_of_twl st)"  (is "?D")
proof -

  have "wf_twl_state (reduce_trail_to M1 (rough_state_of_twl st))"
    using wf_twl_reduce_trail_to assms by fastforce
  moreover
    have "length (trail_twl st) - length M1 = length M2"
      unfolding assms by auto
    then have
      "raw_init_clss (reduce_trail_to M1 (rough_state_of_twl st)) = raw_init_clss_twl st"
      "raw_learned_clss (reduce_trail_to M1 (rough_state_of_twl st)) = raw_learned_clss_twl st"
      "backtrack_lvl (reduce_trail_to M1 (rough_state_of_twl st)) = backtrack_lvl_twl st"
      "twl.conc_conflicting (reduce_trail_to M1 (rough_state_of_twl st)) =
        twl.conc_conflicting (rough_state_of_twl st)"
      using assms by (cases "rough_state_of_twl st", auto simp: drop_map[symmetric])+
  ultimately show ?A ?B ?C ?D
    using twl_of_rough_state_inverse[of "reduce_trail_to M1 (rough_state_of_twl st)"]
    rough_state_of_twl[of st]
    by (auto simp add: assms)
  moreover have "trail_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st))) = M1"
    using trail_twl_twl_rough_state_reduce_trail_to[OF assms(1)] .
  ultimately show ?st using S unfolding twl.state_def
    by (metis (no_types) prod.inject twl.raw_clss_l_raw_init_clss_conc_init_clss)
qed

lemma add_learned_cls_rough_state_of_twl_simp:
  assumes "raw_conflicting_twl st = Some z"
  shows
    "trail (add_learned_cls z (rough_state_of_twl st)) = trail_twl st"
    "twl.conc_init_clss (add_learned_cls z (rough_state_of_twl st)) =
      twl.conc_init_clss (rough_state_of_twl st)"
    "conc_learned_clss (local.add_learned_cls z (rough_state_of_twl st)) =
      {#mset z#} + conc_learned_clss (rough_state_of_twl st)"
    "backtrack_lvl (add_learned_cls z (rough_state_of_twl st)) = backtrack_lvl_twl st"
  using assms wf_twl_state_rough_state_of_twl[of st]
  unfolding wf_twl_state_def apply
  (auto simp: wf_watch add_learned_cls_def comp_def local.clause_watch
    ac_simps
    split: if_split_asm)
  done

sublocale wf_twl: abs_state\<^sub>W_ops where
    cls_lit = "\<lambda>_ L. L" and
    in_cls = "\<lambda>L C. L \<in> set (raw_clause C)" and
    mset_cls = clause and
   
    clss_cls = "\<lambda>_ C. C" and
    in_clss = "\<lambda>C Cs. C \<in> set Cs" and
    mset_clss = mset and

    mset_ccls = mset and

    conc_trail = trail_twl and  
    hd_raw_conc_trail = "\<lambda>S. hd (raw_trail_twl S)" and
    conc_backtrack_lvl = backtrack_lvl_twl and
    raw_conc_conflicting = raw_conflicting_twl and
    conc_learned_clss = conc_learned_clss_twl and
    raw_clauses = raw_clauses_twl and

    cons_conc_trail = cons_trail_twl and 
    tl_conc_trail = tl_trail_twl and 
    add_conc_confl_to_learned_cls = 
      "\<lambda>S. update_conflicting_twl None (add_learned_cls_twl (the (raw_conflicting_twl S)) S)" and
    remove_cls = "\<lambda>C. remove_cls_twl (raw_clause C)" and
    update_conc_backtrack_lvl = update_backtrack_lvl_twl and
    mark_conflicting = "\<lambda>C. update_conflicting_twl (Some (raw_clause C))" and 
    reduce_conc_trail_to = reduce_trail_to_twl and 
    resolve_conflicting = resolve_conflicting_twl and
    conc_init_state = "\<lambda>N. init_state_twl (map raw_clause N)" and 
    restart_state = restart_twl
  rewrites
    "wf_twl.valid_annotation st L = local.twl.valid_annotation (rough_state_of_twl st) L"
proof goal_cases
  case 1 show H: ?case by unfold_locales
  case 2 show ?case
    by (cases L) (auto simp: abs_state\<^sub>W_ops.valid_annotation.simps[OF H])
qed  
  
lemma wf_twl_conc_init_clss_restart_twl[simp]:
  "wf_twl.conc_init_clss (restart_twl S) = wf_twl.conc_init_clss S"
proof -
  have "raw_clss_l (raw_init_clss (restart' (rough_state_of_twl S))) = 
    raw_clss_l (raw_init_clss_twl S)"
    by auto
  then show ?thesis
    by (simp add: local.twl.conc_clauses_def local.twl.conc_init_clss_def 
      rough_state_of_twl_restart_twl twl.wf_twl.conc_init_clss_def wf_twl.conc_clauses_def)
qed

sublocale wf_twl: abs_state\<^sub>W where
    cls_lit = "\<lambda>_ L. L" and
    in_cls = "\<lambda>L C. L \<in> set (raw_clause C)" and
    mset_cls = clause and
   
    clss_cls = "\<lambda>_ C. C" and
    in_clss = "\<lambda>C Cs. C \<in> set Cs" and
    mset_clss = mset and

    mset_ccls = mset and

    conc_trail = trail_twl and  
    hd_raw_conc_trail = "\<lambda>S. hd (raw_trail_twl S)" and
    conc_backtrack_lvl = backtrack_lvl_twl and
    raw_conc_conflicting = raw_conflicting_twl and
    conc_learned_clss = conc_learned_clss_twl and
    raw_clauses = raw_clauses_twl and

    cons_conc_trail = cons_trail_twl and 
    tl_conc_trail = tl_trail_twl and 
    add_conc_confl_to_learned_cls = 
      "\<lambda>S. update_conflicting_twl None (add_learned_cls_twl (the (raw_conflicting_twl S)) S)" and
    remove_cls = "\<lambda>C. remove_cls_twl (raw_clause C)" and
    update_conc_backtrack_lvl = update_backtrack_lvl_twl and
    mark_conflicting = "\<lambda>C. update_conflicting_twl (Some (raw_clause C))" and 
    reduce_conc_trail_to = reduce_trail_to_twl and 
    resolve_conflicting = resolve_conflicting_twl and
    conc_init_state = "\<lambda>N. init_state_twl (map raw_clause N)" and 
    restart_state = restart_twl
proof goal_cases
  case 1
  thm abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF  wf_twl.abs_state\<^sub>W_ops_axioms]
(*   have ugly[simp]: "abs_state\<^sub>W_ops.mmset_of_mlit clause Q Q' = mmset_of_mlit" for Q Q'
    apply (rule ext, rename_tac L, case_tac L)
    by (auto simp: abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF  wf_twl.abs_state\<^sub>W_ops_axioms] clause_def
    raw_clause_def) *)
  have [simp]: "\<And>S. raw_clss_l (restart_learned S) \<subseteq># conc_learned_clss S"
    using image_mset_subseteq_mono[OF restart_learned] unfolding mset_map
     by blast
(*   interpret abs_state\<^sub>W_ops  clause
    raw_clss_l
    "\<lambda>L C. L \<in> set C" "op #"
    mset

    "\<lambda>C. raw_clause C" "\<lambda>C. TWL_Clause [] C"
    by unfold_locales
  have abs: "\<And>S. abs_state\<^sub>W_ops.state raw_clss_l mset trail_twl raw_clauses_twl
    backtrack_lvl_twl raw_conflicting_twl conc_learned_clss_twl S =
    twl.state (rough_state_of_twl S)"
    using wf_twl.conc_init_clss_def unfolding abs_state\<^sub>W_ops.state_def[OF stupid_locales] by auto
 *)
   have locales_are_weird[simp]:
     "abs_state\<^sub>W_ops.valid_annotation (\<lambda>C Cs. C \<in> set Cs) CDCL_Two_Watched_Literals.raw_clauses_twl
        st L = 
     local.twl.valid_annotation (rough_state_of_twl st) L" for st L
     by (cases L) (auto simp: abs_state\<^sub>W_ops.valid_annotation.simps[OF wf_twl.abs_state\<^sub>W_ops_axioms])
   have abs: True by simp
   show ?case
     apply unfold_locales
               using twl.hd_raw_conc_trail apply blast
             apply (auto simp add: rough_state_of_twl_cons_trail wf_twl.state_def)[]
             apply (case_tac "rough_state_of_twl st") apply (auto simp: cons_trail_twl_def)[]
             using wf_twl.conc_init_clss_cons_trail
apply (metis (mono_tags, lifting) local.twl.conc_clauses_def local.twl.conc_init_clss_def
  rough_state_of_twl_cons_trail twl.conc_init_clss_cons_conc_trail
  twl.undefined_lit_trail_twl_raw_trail twl.wf_twl.conc_clauses_def
  twl.wf_twl.conc_init_clss_def)
            apply (auto simp add: rough_state_of_twl_tl_trail wf_twl.state_def abs)[]
            
            
            oops
           apply (auto simp add: rough_state_of_twl_remove_cls
             rough_state_of_twl_update_backtrack_lvl twl.state_def abs; fail)[]
         apply (auto simp add: rough_state_of_twl_update_add_learned_cls twl.state_def
           add_learned_cls_rough_state_of_twl_simp
           abs; fail)[]
        apply (auto simp add:  rough_state_of_twl_update_backtrack_lvl
           rough_state_of_twl_update_conflicting twl.state_def abs; fail)[]
       apply (auto simp add: rough_state_of_twl_update_add_learned_cls twl.state_def
           add_learned_cls_rough_state_of_twl_simp
           rough_state_of_twl_update_conflicting abs; fail)[]
      apply (auto simp add: rough_state_of_twl_update_add_learned_cls twl.state_def
           rough_state_of_twl_update_conflicting abs; fail)[]
     using twl_of_rough_state_reduce_trail_to(1) unfolding abs
     using twl.conc_init_clss_restart_state twl.conc_learned_clss_restart_state
     apply (simp add: twl.resolve_conflicting twl.rough_state_of_twl_update_conflicting;
       fail)
  using twl_of_rough_state_reduce_trail_to(1) unfolding abs
  using twl.conc_init_clss_restart_state twl.conc_learned_clss_restart_state
  by (auto simp: rough_state_of_twl_restart_twl abs
    twl.state_def rough_state_of_twl_init_state comp_def)[8]
  qed


sublocale wf_twl: abs_conflict_driven_clause_learning\<^sub>W
  clause
  raw_clss_l
  "\<lambda>L C. L \<in> set C" "op #"

  mset

  "\<lambda>C. raw_clause C" "\<lambda>C. TWL_Clause [] C"
  trail_twl "\<lambda>S. hd (raw_trail_twl S)"
  raw_clauses_twl
  backtrack_lvl_twl
  raw_conflicting_twl
  conc_learned_clss_twl

  cons_trail_twl
  tl_trail_twl
  "\<lambda>S. update_conflicting_twl None (add_learned_cls_twl (the (raw_conflicting_twl S)) S)"
  "\<lambda>C. remove_cls_twl (raw_clause C)"
  update_backtrack_lvl_twl
  "\<lambda>C. update_conflicting_twl (Some C)"
  reduce_trail_to_twl
  resolve_conflicting_twl
  "\<lambda>N. init_state_twl (map raw_clause N)"
  restart_twl
  by unfold_locales

declare local.twl.mset_ccls_ccls_of_cls[simp del]
abbreviation state_eq_twl (infix "\<sim>TWL" 51) where
"state_eq_twl S S' \<equiv> twl.state_eq (rough_state_of_twl S) (rough_state_of_twl S')"
notation wf_twl.state_eq (infix "\<sim>" 51)

text \<open>To avoid ambiguities:\<close>
no_notation state_eq_twl (infix "\<sim>" 51)

paragraph \<open>Alternative Definition of CDCL using the candidates of 2-WL\<close>
inductive propagate_twl :: "'v wf_twl \<Rightarrow> 'v wf_twl \<Rightarrow> bool" where
propagate_twl_rule: "(L, C) \<in> candidates_propagate_twl S \<Longrightarrow>
  S' \<sim> cons_trail_twl (Propagated L C) S \<Longrightarrow>
  raw_conflicting_twl S = None \<Longrightarrow>
  propagate_twl S S'"

lemma cdcl\<^sub>W_all_struct_inv_clause_distinct_mset:
  "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (wf_twl.state S) \<Longrightarrow>
    C \<in> set (CDCL_Two_Watched_Literals.raw_clauses_twl S) \<Longrightarrow> distinct (raw_clause C)"
  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
     distinct_mset_set_def wf_twl.conc_clauses_init_learned
  by (metis (no_types, lifting) distinct_mset_distinct in_clss_mset_clss union_iff
    wf_twl.conc_clauses_init_learned wf_twl.init_clss_state_conc_init_clss
    wf_twl.learned_clss_state_conc_learned_clss wf_twl.mset_ccls_ccls_of_cls)

inductive_cases propagate_twlE: "propagate_twl S T"
lemma propagate_twl_iff_propagate:
  assumes inv: "cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (wf_twl.state S)"
  shows "wf_twl.propagate_abs S T \<longleftrightarrow> propagate_twl S T" (is "?P \<longleftrightarrow> ?T")
proof
  assume ?P
  then obtain L E where
    "raw_conflicting_twl S = None" and
    CL_Clauses: "E \<in> set (raw_clauses_twl S)" and
    LE: "L \<in># clause E" and
    tr_CNot: "trail_twl S \<Turnstile>as CNot (remove1_mset L (clause E))" and
    undef_lot[simp]: "undefined_lit (trail_twl S) L" and
    "T \<sim> cons_trail_twl (Propagated L E) S"
    by (blast elim: wf_twl.propagate_absE)
  have "distinct (raw_clause E)"
    using inv CL_Clauses cdcl\<^sub>W_all_struct_inv_clause_distinct_mset by blast
  then have X: "remove1_mset L (mset (raw_clause E)) = mset_set (set (raw_clause E) - {L})"
    by (auto simp: multiset_eq_iff raw_clause_def count_mset distinct_filter_eq_if)
  have "(L, E) \<in> candidates_propagate_twl S"
    apply (rule wf_candidates_propagate_complete)
         using rough_state_of_twl apply (auto; fail)[]
        using CL_Clauses apply (auto; fail)[]
       using LE apply (simp add: clause_def; fail)
      using tr_CNot X apply (simp add: clause_def; fail)
     using undef_lot apply blast
     done
  show ?T
    apply (rule propagate_twl_rule)
       apply (rule \<open>(L, E) \<in> candidates_propagate_twl S\<close>)
      using \<open>T \<sim> cons_trail_twl (Propagated L E) S\<close>
      apply (auto simp: \<open>raw_conflicting_twl S = None\<close> cdcl\<^sub>W_restart_mset.state_eq_def)
    done
next
  assume ?T
  then obtain L C where
    LC: "(L, C) \<in> candidates_propagate_twl S" and
    T: "T \<sim> cons_trail_twl (Propagated L C) S" and
    confl: "raw_conflicting_twl S = None"
    by (auto elim: propagate_twlE)
  have
    C'S: "C \<in> set (raw_clauses_twl S)" and
    L: "set (watched C) - uminus ` lits_of_l (trail_twl S) = {L}" and
    undef: "undefined_lit (trail_twl S) L"
    using LC unfolding candidates_propagate_def by auto
  have dist: "distinct (raw_clause C)"
    using inv C'S cdcl\<^sub>W_all_struct_inv_clause_distinct_mset by blast
  then have C_L_L: "mset_set (set (raw_clause C) - {L}) = clause C - {#L#}"
    by (metis distinct_mset_distinct distinct_mset_minus distinct_mset_set_mset_ident mset_remove1
      set_mset_mset set_remove1_eq clause_def)

  show ?P
    apply (rule wf_twl.propagate_abs_rule[of S C L])
        using confl apply (auto; fail)[]
       using C'S apply (simp; fail)
       using L unfolding candidates_propagate_def
       apply (auto simp: raw_clause_def clause_def; fail)[]
      using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl dist
      apply (simp add: distinct_mset_remove1_All true_annots_true_cls clause_def; fail)
     using undef apply (simp; fail)
    using T undef unfolding cdcl\<^sub>W_restart_mset.state_eq_def by auto
qed

no_notation twl.state_eq_twl (infix "\<sim>TWL" 51)

inductive conflict_twl where
conflict_twl_rule:
"C \<in> candidates_conflict_twl S \<Longrightarrow>
  S' \<sim> update_conflicting_twl (Some (raw_clause C)) S \<Longrightarrow>
  raw_conflicting_twl S = None \<Longrightarrow>
  conflict_twl S S'"

inductive_cases conflict_twlE: "conflict_twl S T"

lemma conflict_twl_iff_conflict:
  shows "wf_twl.conflict_abs S T \<longleftrightarrow> conflict_twl S T" (is "?C \<longleftrightarrow> ?T")
proof
  assume ?C
  then obtain D where
    S: "raw_conflicting_twl S = None" and
    D: "D \<in> set (raw_clauses_twl S)" and
    MD: "trail_twl S \<Turnstile>as CNot (clause D)" and
    T: "T \<sim> update_conflicting_twl (Some (raw_clause D)) S"
    by (elim wf_twl.conflict_absE)

  have "D \<in> candidates_conflict_twl S"
    apply (rule wf_candidates_conflict_complete)
       apply simp
      using D apply (auto; fail)[]
    using MD S by auto
  moreover have "T \<sim> twl_of_rough_state (update_conflicting (Some (raw_clause D))
  (rough_state_of_twl S))"
    using T unfolding cdcl\<^sub>W_restart_mset.state_eq_def by auto
  ultimately show ?T
    using S by (auto intro: conflict_twl_rule)
next
  assume ?T
  then obtain C where
    C: "C \<in> candidates_conflict_twl S" and
    T: "T \<sim> update_conflicting_twl (Some (raw_clause C)) S" and
    confl: "raw_conflicting_twl S = None"
    by (auto elim: conflict_twlE)
  have
    "C \<in> set (raw_clauses_twl S)"
    using C unfolding candidates_conflict_def by auto
 moreover have "trail_twl S \<Turnstile>as CNot (clause C)"
    using wf_candidates_conflict_sound[OF _ C] by auto
 ultimately show ?C apply -
   apply (rule wf_twl.conflict_abs_rule[of _ C])
   using confl T unfolding cdcl\<^sub>W_restart_mset.state_eq_def by (auto simp del: map_map)
qed

text \<open>We have shown that we we can use @{term conflict_twl} and @{term propagate_twl} in a CDCL
  calculus.\<close>
end

end