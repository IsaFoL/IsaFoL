(*  Title: Implementation of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Implementation for 2 Watched-Literals\<close>

theory CDCL_Two_Watched_Literals_Implementation
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
begin

subsection \<open>Interpretation for @{term conflict_driven_clause_learning\<^sub>W.cdcl\<^sub>W}\<close>

context abstract_twl
begin

subsubsection \<open>Direct Interpretation\<close>
lemma mset_map_removeAll_cond:
  "mset (map (\<lambda>x. mset (raw_clause x))
    (removeAll_cond (\<lambda>D. mset (raw_clause D) = mset (raw_clause C)) N))
  = mset (removeAll (mset (raw_clause C)) (map (\<lambda>x. mset (raw_clause x)) N))"
  by (induction N) auto

lemma mset_raw_init_clss_init_state:
  "mset (map (\<lambda>x. mset (raw_clause x)) (raw_init_clss (init_state (map raw_clause N))))
  = mset (map (\<lambda>x. mset (raw_clause x)) N)"
  by (metis (no_types, lifting) init_clss_init_state map_eq_conv map_map o_def)

interpretation rough_cdcl: state\<^sub>W
  "\<lambda>C. mset (raw_clause C)"
    (* does not matter if the invariants do not hold *)
  "\<lambda>L C. TWL_Clause (watched C) (L # unwatched C)"
  "\<lambda>L C. TWL_Clause [] (remove1 L (watched C @ unwatched C))"
  "\<lambda>C. clauses_of_l (map raw_clause C)" "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. mset (raw_clause D) = mset (raw_clause C))"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  "op #" remove1

  "\<lambda>C. watched C @ unwatched C" "\<lambda>C. TWL_Clause [] C"
  trail "\<lambda>S. hd (raw_trail S)"
  raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
  cons_trail tl_trail "\<lambda>C. add_init_cls (raw_clause C)" "\<lambda>C. add_learned_cls (raw_clause C)"
  "\<lambda>C. remove_cls (raw_clause C)"
  update_backtrack_lvl
  update_conflicting "\<lambda>N. init_state (map raw_clause N)" restart'
  apply unfold_locales
  apply (case_tac "raw_trail S")
  apply (simp_all add: add_init_cls_def add_learned_cls_def clause_rewatch clause_watch
    cons_trail_def remove_cls_def restart'_def tl_trail_def map_tl comp_def
    ac_simps mset_map_removeAll_cond mset_raw_init_clss_init_state)

  apply (auto simp: mset_map image_mset_subseteq_mono[OF restart_learned] )
  done

interpretation rough_cdcl: conflict_driven_clause_learning\<^sub>W
  "\<lambda>C. mset (raw_clause C)"
    (* does not matter if the invariants do not hold *)
  "\<lambda>L C. TWL_Clause (watched C) (L # unwatched C)"
  "\<lambda>L C. TWL_Clause [] (remove1 L (watched C @ unwatched C))"
  "\<lambda>C. clauses_of_l (map raw_clause C)" "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. mset (raw_clause D) = mset (raw_clause C))"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  "op #" remove1

  "\<lambda>C. watched C @ unwatched C" "\<lambda>C. TWL_Clause [] C"
  trail "\<lambda>S. hd (raw_trail S)"
  raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
  cons_trail tl_trail "\<lambda>C. add_init_cls (raw_clause C)" "\<lambda>C. add_learned_cls (raw_clause C)"
  "\<lambda>C. remove_cls (raw_clause C)"
  update_backtrack_lvl
  update_conflicting "\<lambda>N. init_state (map raw_clause N)" restart'
  by unfold_locales

(* interpretation cdcl\<^sub>N\<^sub>O\<^sub>T: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops
  "\<lambda>S. convert_trail_from_W (trail S)"
  rough_cdcl.clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate S"
  "\<lambda>_ S. conflicting S = None"
  "\<lambda>C C' L' S. C \<in> candidates_conflict S \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  by unfold_locales
 *)
subsubsection \<open>Opaque Type with Invariant\<close>

declare rough_cdcl.state_simp[simp del]

definition cons_trail_twl :: "('v, nat, 'v twl_clause) marked_lit \<Rightarrow> 'v wf_twl \<Rightarrow> 'v wf_twl"
  where
"cons_trail_twl L S \<equiv> twl_of_rough_state (cons_trail L (rough_state_of_twl S))"

lemma wf_twl_state_cons_trail:
  assumes
    undef: "undefined_lit (trail S) (lit_of L)" and
    wf: "wf_twl_state S"
  shows "wf_twl_state (cons_trail L S)"
  using undef wf wf_rewatch[of S "mmset_of_mlit' L"] unfolding wf_twl_state_def Ball_def
  by (auto simp: cons_trail_def defined_lit_map comp_def image_def raw_clauses_def)

lemma rough_state_of_twl_cons_trail:
  "undefined_lit (trail_twl S) (lit_of L) \<Longrightarrow>
    rough_state_of_twl (cons_trail_twl L S) = cons_trail L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_cons_trail
  unfolding cons_trail_twl_def by blast

abbreviation add_init_cls_twl where
"add_init_cls_twl C S \<equiv> twl_of_rough_state (add_init_cls C (rough_state_of_twl S))"

lemma wf_twl_add_init_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_init_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_init_cls_def comp_def raw_clauses_def
    split: if_split_asm)

lemma rough_state_of_twl_add_init_cls:
  "rough_state_of_twl (add_init_cls_twl L S) = add_init_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_init_cls by blast

abbreviation add_learned_cls_twl where
"add_learned_cls_twl C S \<equiv> twl_of_rough_state (add_learned_cls C (rough_state_of_twl S))"

lemma wf_twl_add_learned_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_learned_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_learned_cls_def raw_clauses_def
    split: if_split_asm)

lemma rough_state_of_twl_add_learned_cls:
  "rough_state_of_twl (add_learned_cls_twl L S) = add_learned_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_learned_cls by blast

abbreviation remove_cls_twl where
"remove_cls_twl C S \<equiv> twl_of_rough_state (remove_cls C (rough_state_of_twl S))"

lemma set_removeAll_condD: "x \<in> set (removeAll_cond f xs) \<Longrightarrow> x \<in> set xs"
  by (induction xs) (auto split: if_split_asm)

lemma wf_twl_remove_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (remove_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch remove_cls_def raw_clauses_def comp_def
    split: if_split_asm dest: set_removeAll_condD)  

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
  by (auto simp: wf_twl_state_def raw_clauses_def)

lemma wf_twl_init_state: "wf_twl_state (init_state N)"
  unfolding init_state_def by (auto intro!: wf_twl_state_wf_twl_state_fold_add_init_cls)

lemma rough_state_of_twl_init_state:
  "rough_state_of_twl (init_state_twl N) = init_state N"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state)

abbreviation tl_trail_twl where
"tl_trail_twl S \<equiv> twl_of_rough_state (tl_trail (rough_state_of_twl S))"

lemma wf_twl_state_tl_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (tl_trail S)"
  by (auto simp add: twl_of_rough_state_inverse wf_twl_init_state wf_twl_cls_wf_twl_cls_tl
    tl_trail_def wf_twl_state_def distinct_tl map_tl comp_def raw_clauses_def)

lemma rough_state_of_twl_tl_trail:
  "rough_state_of_twl (tl_trail_twl S) = tl_trail (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_tl_trail by blast

abbreviation update_backtrack_lvl_twl where
"update_backtrack_lvl_twl k S \<equiv> twl_of_rough_state (update_backtrack_lvl k (rough_state_of_twl S))"

lemma wf_twl_state_update_backtrack_lvl:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_backtrack_lvl k S)"
  unfolding wf_twl_state_def by (auto simp: comp_def raw_clauses_def)

lemma rough_state_of_twl_update_backtrack_lvl:
  "rough_state_of_twl (update_backtrack_lvl_twl k S) = update_backtrack_lvl k
    (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_update_backtrack_lvl by fast

abbreviation update_conflicting_twl where
"update_conflicting_twl k S \<equiv> twl_of_rough_state (update_conflicting k (rough_state_of_twl S))"

lemma wf_twl_state_update_conflicting:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_conflicting k S)"
  unfolding wf_twl_state_def by (auto simp: raw_clauses_def comp_def)

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
   apply (subgoal_tac "wf_twl_cls (trail S) x")
    apply (case_tac x)
  using restart_learned by (auto simp: raw_clauses_def comp_def dest: mset_union_mset_setD)

lemma rough_state_of_twl_restart_twl:
  "rough_state_of_twl (restart_twl S) = restart' (rough_state_of_twl S)"
  by (simp add: twl_of_rough_state_inverse wf_wf_restart')

(* Sledgehammer is awesome! *)
interpretation cdcl\<^sub>W_twl_NOT: dpll_state
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  raw_clauses_twl
  "\<lambda>L S. cons_trail_twl (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail_twl S"
  "\<lambda>C S. add_learned_cls_twl C S"
  "\<lambda>C S. remove_cls_twl C S"
  apply unfold_locales
         apply (simp add: rough_state_of_twl_cons_trail)
        apply (metis rough_state_of_twl_tl_trail rough_cdcl.tl_trail)
       apply (metis rough_state_of_twl_add_learned_cls rough_cdcl.trail_add_cls\<^sub>N\<^sub>O\<^sub>T)
      apply (metis rough_state_of_twl_remove_cls rough_cdcl.trail_remove_cls)
     apply (simp add: rough_state_of_twl_cons_trail)
    apply (simp add: rough_state_of_twl_tl_trail)
   using rough_cdcl.clauses_add_cls\<^sub>N\<^sub>O\<^sub>T rough_cdcl.clauses_def rough_state_of_twl_add_learned_cls
   apply auto[1]
  using rough_cdcl.clauses_def rough_cdcl.clauses_remove_cls rough_state_of_twl_remove_cls by auto

interpretation cdcl\<^sub>W_twl: state\<^sub>W
  trail_twl
  init_clss_twl
  learned_clss_twl
  backtrack_lvl_twl
  conflicting_twl
  cons_trail_twl
  tl_trail_twl
  add_init_cls_twl
  add_learned_cls_twl
  remove_cls_twl
  update_backtrack_lvl_twl
  update_conflicting_twl
  init_state_twl
  restart_twl
  apply unfold_locales
  by (simp_all add: rough_state_of_twl_cons_trail rough_state_of_twl_tl_trail
    rough_state_of_twl_add_init_cls rough_state_of_twl_add_learned_cls rough_state_of_twl_remove_cls
    rough_state_of_twl_update_backtrack_lvl rough_state_of_twl_update_conflicting
    rough_state_of_twl_init_state rough_state_of_twl_restart_twl
    rough_cdcl.learned_clss_restart_state)

interpretation cdcl\<^sub>W_twl: cdcl\<^sub>W
  trail_twl
  init_clss_twl
  learned_clss_twl
  backtrack_lvl_twl
  conflicting_twl
  cons_trail_twl
  tl_trail_twl
  add_init_cls_twl
  add_learned_cls_twl
  remove_cls_twl
  update_backtrack_lvl_twl
  update_conflicting_twl
  init_state_twl
  restart_twl
  by unfold_locales

sublocale cdcl\<^sub>W
  trail_twl
  init_clss_twl
  learned_clss_twl
  backtrack_lvl_twl
  conflicting_twl
  cons_trail_twl
  tl_trail_twl
  add_init_cls_twl
  add_learned_cls_twl
  remove_cls_twl
  update_backtrack_lvl_twl
  update_conflicting_twl
  init_state_twl
  restart_twl
  by (rule cdcl\<^sub>W_twl.cdcl\<^sub>W_axioms)

abbreviation state_eq_twl (infix "\<sim>TWL" 51) where
"state_eq_twl S S' \<equiv> rough_cdcl.state_eq (rough_state_of_twl S) (rough_state_of_twl S')"
notation cdcl\<^sub>W_twl.state_eq (infix "\<sim>" 51)
declare cdcl\<^sub>W_twl.state_simp[simp del]
  cdcl\<^sub>W_twl_NOT.state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]

text \<open>To avoid ambiguities:\<close>
no_notation state_eq_twl (infix "\<sim>" 51)

definition propagate_twl where
"propagate_twl S S' \<longleftrightarrow>
  (\<exists>L C. (L, C) \<in> candidates_propagate_twl S
  \<and> S' \<sim> cons_trail_twl (Propagated L C) S
  \<and> conflicting_twl S = None)"

lemma propagate_twl_iff_propagate:
  assumes inv: "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl.propagate S T \<longleftrightarrow> propagate_twl S T" (is "?P \<longleftrightarrow> ?T")
proof
  assume ?P
  then obtain C L where
    "conflicting (rough_state_of_twl S) = None" and
    CL_Clauses: "C + {#L#} \<in># cdcl\<^sub>W_twl.clauses S" and
    tr_CNot: "trail_twl S \<Turnstile>as CNot C" and
    undef_lot: "undefined_lit (trail_twl S) L" and
    "T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S"
    unfolding cdcl\<^sub>W_twl.propagate.simps by blast
  have "distinct_mset (C + {#L#})"
    using inv CL_Clauses unfolding cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_twl.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_twl.clauses_def distinct_mset_set_def
    by auto
  then have C_L_L: "mset_set (set_mset (C + {#L#}) - {L}) = C"
    by (metis Un_insert_right add_diff_cancel_left' add_diff_cancel_right'
      distinct_mset_set_mset_ident finite_set_mset insert_absorb2 mset_set.insert_remove
      set_mset_single set_mset_union)
  have "(L, C+{#L#}) \<in> candidates_propagate_twl S"
    apply (rule wf_candidates_propagate_complete)
         using rough_state_of_twl apply auto[]
        using CL_Clauses unfolding cdcl\<^sub>W_twl.clauses_def apply auto[]
       apply simp
      using C_L_L tr_CNot apply simp
     using undef_lot apply blast
     done
  show ?T unfolding propagate_twl_def
    apply (rule exI[of _ "L"], rule exI[of _ "C+{#L#}"])
    apply (auto simp: \<open>(L, C+{#L#}) \<in> candidates_propagate_twl S\<close>
      \<open>conflicting (rough_state_of_twl S) = None\<close> )
    using \<open>T \<sim> cons_trail_twl (Propagated L (C + {#L#})) S\<close> cdcl\<^sub>W_twl.state_eq_backtrack_lvl
    cdcl\<^sub>W_twl.state_eq_conflicting cdcl\<^sub>W_twl.state_eq_init_clss
    cdcl\<^sub>W_twl.state_eq_learned_clss cdcl\<^sub>W_twl.state_eq_trail rough_cdcl.state_eq_def by blast
next
  assume ?T
  then obtain L C where
    LC: "(L, C) \<in> candidates_propagate_twl S" and
    T: "T \<sim> cons_trail_twl (Propagated L C) S" and
    confl: "conflicting (rough_state_of_twl S) = None"
    unfolding propagate_twl_def by auto
  have [simp]: "C - {#L#} + {#L#} = C"
    using LC unfolding candidates_propagate_def
    by clarify (metis Multiset.diff_le_self insert_DiffM2 mset_leD multi_member_last union_iff)
  have "C \<in># raw_clauses_twl S"
    using LC unfolding candidates_propagate_def rough_cdcl.clauses_def by auto
  then have "distinct_mset C"
    using inv unfolding cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_twl.distinct_cdcl\<^sub>W_state_def
    cdcl\<^sub>W_twl.clauses_def distinct_mset_set_def rough_cdcl.clauses_def by auto
  then have C_L_L: "mset_set (set_mset C - {L}) = C - {#L#}"
    by (metis \<open>C - {#L#} + {#L#} = C\<close> add_left_imp_eq diff_single_trivial
      distinct_mset_set_mset_ident finite_set_mset mset_set.remove
      multi_self_add_other_not_self union_commute)

  show ?P
    apply (rule cdcl\<^sub>W_twl.propagate.intros[of _ "trail_twl S" "init_clss_twl S"
      "learned_clss_twl S" "backtrack_lvl_twl S" "C-{#L#}" L])
        using confl apply auto[]
       using LC unfolding candidates_propagate_def apply (auto simp: cdcl\<^sub>W_twl.clauses_def)[]
      using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply (simp add: C_L_L)
     using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl apply simp
    using T unfolding cdcl\<^sub>W_twl.state_eq_def rough_cdcl.state_eq_def by auto
qed
no_notation CDCL_Two_Watched_Literals.twl.state_eq_twl (infix "\<sim>TWL" 51)
definition conflict_twl where
"conflict_twl S S' \<longleftrightarrow>
  (\<exists>C. C \<in> candidates_conflict_twl S
  \<and> S' \<sim> update_conflicting_twl (Some C) S
  \<and> conflicting_twl S = None)"

lemma conflict_twl_iff_conflict:
  shows "cdcl\<^sub>W_twl.conflict S T \<longleftrightarrow> conflict_twl S T" (is "?C \<longleftrightarrow> ?T")
proof
  assume ?C
  then obtain M N U k C where
    S: "rough_cdcl.state (rough_state_of_twl S) = (M, N, U, k, None)" and
    C: "C \<in># cdcl\<^sub>W_twl.clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    T: "T \<sim> update_conflicting_twl (Some C) S"
    by auto
  have "C \<in> candidates_conflict_twl S"
    apply (rule wf_candidates_conflict_complete)
       apply simp
      using C apply (auto simp: cdcl\<^sub>W_twl.clauses_def)[]
    using M_C S by auto
  moreover have "T \<sim> twl_of_rough_state (update_conflicting (Some C) (rough_state_of_twl S))"
    using T unfolding rough_cdcl.state_eq_def cdcl\<^sub>W_twl.state_eq_def by auto
  ultimately show ?T
    using S unfolding conflict_twl_def by auto
next
  assume ?T
  then obtain C where
    C: "C \<in> candidates_conflict_twl S" and
    T: "T \<sim> update_conflicting_twl (Some C) S" and
    confl: "conflicting_twl S = None"
    unfolding conflict_twl_def by auto
  have "C \<in># cdcl\<^sub>W_twl.clauses S"
    using C unfolding candidates_conflict_def cdcl\<^sub>W_twl.clauses_def by auto
 moreover have "trail_twl S \<Turnstile>as CNot C"
    using wf_candidates_conflict_sound[OF _ C] by auto
 ultimately show ?C apply -
   apply (rule cdcl\<^sub>W_twl.conflict.conflict_rule[of _ _ _ _ _ C])
   using confl T unfolding rough_cdcl.state_eq_def cdcl\<^sub>W_twl.state_eq_def by auto
qed

inductive cdcl\<^sub>W_twl :: "'v wf_twl \<Rightarrow> 'v wf_twl \<Rightarrow> bool" for S :: "'v wf_twl" where
propagate: "propagate_twl S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'" |
conflict: "conflict_twl S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'" |
other: "cdcl\<^sub>W_twl.cdcl\<^sub>W_o S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'"|
rf: "cdcl\<^sub>W_twl.cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_twl S S'"

lemma cdcl\<^sub>W_twl_iff_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl S T \<longleftrightarrow> cdcl\<^sub>W_twl.cdcl\<^sub>W S T"
  by (simp add: assms cdcl\<^sub>W_twl.cdcl\<^sub>W.simps cdcl\<^sub>W_twl.simps conflict_twl_iff_conflict
    propagate_twl_iff_propagate)

lemma rtranclp_cdcl\<^sub>W_twl_all_struct_inv_inv:
  assumes "cdcl\<^sub>W_twl\<^sup>*\<^sup>* S T" and "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv T"
  using assms by (induction rule: rtranclp_induct)
  (simp_all add: cdcl\<^sub>W_twl_iff_cdcl\<^sub>W cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv_inv)

lemma rtranclp_cdcl\<^sub>W_twl_iff_rtranclp_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_twl.cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_twl\<^sup>*\<^sup>* S T \<longleftrightarrow> cdcl\<^sub>W_twl.cdcl\<^sub>W\<^sup>*\<^sup>* S T" (is "?T \<longleftrightarrow> ?W")
proof
  assume ?W
  then show ?T
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case by simp
    next
      case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
      have "cdcl\<^sub>W_twl T U"
        using assms st cdcl cdcl\<^sub>W_twl.rtranclp_cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_twl_iff_cdcl\<^sub>W
        by blast
      then show ?case using IH by auto
    qed
next
  assume ?T
  then show ?W
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case by simp
    next
      case (step T U) note st = this(1) and cdcl = this(2) and IH = this(3)
      have "cdcl\<^sub>W_twl.cdcl\<^sub>W T U"
        using assms st cdcl rtranclp_cdcl\<^sub>W_twl_all_struct_inv_inv cdcl\<^sub>W_twl_iff_cdcl\<^sub>W
        by blast
      then show ?case using IH by auto
    qed
qed

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: backjumping_ops
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L (S:: 'v wf_twl).
    cons_trail_twl
      (convert_marked_lit_from_NOT L) (S:: 'v wf_twl)"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* bj conditions *) "\<lambda>C _ _ (S:: 'v wf_twl) _. C \<in> candidates_conflict_twl S"
  by unfold_locales

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning_twl:
  assumes "trail_twl S = convert_trail_from_NOT (F' @ F)"
  shows "trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = convert_trail_from_NOT F"
  using assms by (induction F' arbitrary: S) auto

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_trail_tl_trail_twl_decomp[simp]:
  "trail_twl S = convert_trail_from_NOT (F' @ Marked K () # F) \<Longrightarrow>
     trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail_twl S)) = convert_trail_from_NOT F"
  apply (rule reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning_twl[of _ "tl (F' @ Marked K () # [])"])
  by (cases F') (auto simp add:tl_append rough_cdcl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning)

lemma trail_twl_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop:
  "trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) =
    (if length (trail_twl S) \<ge> length F
    then drop (length (trail_twl S) - length F) (trail_twl S)
    else [])"
  apply (induction F S rule: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (rename_tac F S)
  apply (case_tac "trail_twl S")
   apply auto[]
  apply (rename_tac list)
  apply (case_tac "Suc (length list) > length F")
   prefer 2 apply simp
  apply (subgoal_tac "Suc (length list) - length F = Suc (length list - length F)")
   apply simp
  apply simp
  done

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: dpll_with_backjumping_ops
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L S.
    cons_trail_twl
      (convert_marked_lit_from_NOT L) S"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate_twl S"
  (* state invariant *)"\<lambda>S. no_dup (trail_twl S)"
  (* backjump conditions *)"\<lambda>C _ _ S _. C \<in> candidates_conflict_twl S"
proof (unfold_locales, goal_cases)
  case (1 C' S C F' K F L) note n_d = this(1) and n_d' = this(2) and undef = this(6)
  let ?T' = "(cons_trail (Propagated L {#}) (rough_state_of_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)))"
  let ?T = "(cons_trail_twl (Propagated L {#}) (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
  have tr_F_S: "map lit_of (trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)) =
    map lit_of (convert_trail_from_NOT F)"
    apply (subst trail_twl_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop[of F S])
    using 1(1) arg_cong[OF 1(3), of length] arg_cong[OF 1(3), of "map lit_of"]
    by (auto simp: o_def drop_map[symmetric])

  have "no_dup (trail_twl S)"
    using "1"(1) by blast
  have "wf_twl_state (rough_state_of_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
    using wf_twl_state_rough_state_of_twl by blast
  moreover have undef': "undefined_lit (trail_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)) L"
    using undef arg_cong[OF tr_F_S, of "map atm_of"] unfolding defined_lit_map image_set
    by (simp add:  o_def)
  ultimately have "wf_twl_state ?T'"
    by (simp_all add: wf_twl_state_cons_trail)
  then have "init_clss_twl ?T = init_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"
      using 1(6) by (simp add: undef')
  then have [simp]: "init_clss_twl ?T = init_clss_twl S"
     by (simp add: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)

  have "learned_clss_twl ?T = learned_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)"
    by (smt "1"(3) "1"(6) append_assoc cdcl\<^sub>W_twl.learned_clss_cons_trail
      cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq_length cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_nil
      cdcl\<^sub>W_twl_NOT.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_skip_beginning comp_apply defined_lit_convert_trail_from_W
      list.sel(3) marked_lit.sel(2) rev.simps(2) rev_append rev_eq_Cons_iff
      cons_trail_twl_def)
  moreover have "learned_clss_twl (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S)
    = learned_clss_twl S"
    by (simp add: cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)
  ultimately have [simp]: "learned_clss_twl ?T = learned_clss_twl S"
    by simp
  have tr_L_F_S: "map lit_of (trail_twl ?T)
    = map lit_of (Propagated L {#} # convert_trail_from_NOT F)"
    using undef' tr_F_S by (simp add: o_def)
  have C_confl_cand: "C \<in> candidates_conflict_twl S"
    apply(rule wf_candidates_twl_conflict_complete)
     using 1(1,4) apply (simp add: rough_cdcl.clauses_def)
    using 1(5) by (simp add: tr_L_F_S true_annots_true_cls lits_of_l_convert_trail_from_NOT)

  have "cdcl\<^sub>N\<^sub>O\<^sub>T_twl.backjump S
    (cons_trail_twl (convert_marked_lit_from_NOT (Propagated L ()))
      (cdcl\<^sub>W_twl.reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S))"
    apply (rule cdcl\<^sub>N\<^sub>O\<^sub>T_twl.backjump.intros[of S F' K F _ L C, OF 1(3) _ 1(4-6) _ 1(8-9)])
      unfolding cdcl\<^sub>W_twl_NOT.state_eq\<^sub>N\<^sub>O\<^sub>T_def apply (metis convert_marked_lit_from_NOT.simps(1))
     using 1(7) 1(3) apply presburger
    using C_confl_cand by simp
  then show ?case
    by blast
qed

interpretation cdcl\<^sub>N\<^sub>O\<^sub>T_twl: dpll_with_backjumping
  "\<lambda>S. convert_trail_from_W (trail_twl S)"
  abstract_twl.raw_clauses_twl
  "\<lambda>L (S:: 'v wf_twl).
    cons_trail_twl
      (convert_marked_lit_from_NOT L) (S:: 'v wf_twl)"
  tl_trail_twl
  add_learned_cls_twl
  remove_cls_twl
  (* propagate conditions: *)"\<lambda>L S. lit_of L \<in> fst ` candidates_propagate_twl S"
  (* state invariant *)"\<lambda>S. no_dup (trail_twl S)"
  (* backjump conditions *)"\<lambda>C _ _ (S:: 'v wf_twl) _. C \<in> candidates_conflict_twl S"
  apply unfold_locales
  using cdcl\<^sub>N\<^sub>O\<^sub>T_twl.dpll_bj_no_dup by (simp add: o_def)
end

end
