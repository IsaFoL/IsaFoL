(*  Title: Invariants of CDCL with Two Watched Literals
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

subsection \<open>Two Watched-Literals with invariant\<close>

theory CDCL_Two_Watched_Literals_Invariant
imports CDCL_Two_Watched_Literals DPLL_CDCL_W_Implementation
begin

subsubsection \<open>Interpretation for @{term conflict_driven_clause_learning\<^sub>W.cdcl\<^sub>W}\<close>

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

lemma mset_raw_init_clss_init_state:
  "mset (map clause (raw_init_clss (init_state (map raw_clause N))))
  = mset (map clause N)"
  by (metis (no_types, lifting) init_clss_init_state map_eq_conv map_map o_def clause_def)

fun reduce_trail_to where
"reduce_trail_to M1 S =
  (case S of
    (TWL_State M N U k C) \<Rightarrow> TWL_State (drop (length M - length M1) M) N U k C)"

interpretation rough_cdcl: abs_state\<^sub>W_ops
    clause
    raw_clss_l "op @"
    "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

    mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
    remove1

    raw_clause "\<lambda>C. TWL_Clause [] C"
    trail "\<lambda>S. hd (raw_trail S)"
    raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
    cons_trail tl_trail "\<lambda>C. add_learned_cls (raw_clause C)"
    "\<lambda>C. remove_cls (raw_clause C)"
    update_backtrack_lvl
    update_conflicting reduce_trail_to "\<lambda>N. init_state (map raw_clause N)" restart'
  rewrites
    "rough_cdcl.mmset_of_mlit = mmset_of_mlit"
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
qed

interpretation rough_cdcl: abs_state\<^sub>W
    clause
    raw_clss_l "op @"
    "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

    mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
    remove1

    raw_clause "\<lambda>C. TWL_Clause [] C"
    trail "\<lambda>S. hd (raw_trail S)"
    raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
    cons_trail tl_trail "\<lambda>C. add_learned_cls (raw_clause C)"
    "\<lambda>C. remove_cls (raw_clause C)"
    update_backtrack_lvl
    update_conflicting reduce_trail_to "\<lambda>N. init_state (map raw_clause N)" restart'
proof goal_cases
  case 1
  have stupid_locales: "abs_state\<^sub>W_ops clause raw_clss_l op @ (\<lambda>L C. L \<in> set C) op #
    (\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)) mset union_mset_list remove1 raw_clause
    (TWL_Clause [])"
    by unfold_locales
  have [simp]: "abs_state\<^sub>W_ops.mmset_of_mlit clause = mmset_of_mlit"
    apply (rule ext, rename_tac L, case_tac L)
    by (auto simp: abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF stupid_locales] clause_def
    raw_clause_def)
  have [simp]: "\<And>S. raw_clss_l (restart_learned S) \<subseteq># rough_cdcl.conc_learned_clss S"
    using image_mset_subseteq_mono[OF restart_learned] unfolding mset_map
     by blast
  have H: "\<And>M2 M1 x1. M2 @ M1 = map mmset_of_mlit x1 \<Longrightarrow>
       map mmset_of_mlit (drop (length x1 - length M1) x1) = M1"
    by (metis add_diff_cancel_right' append_eq_conv_conj drop_map length_append length_map)
  show H: ?case
    apply unfold_locales
    apply (case_tac "raw_trail S"; case_tac "hd (raw_trail S)")
    by (auto simp add: add_init_cls_def add_learned_cls_def clause_rewatch clause_watch
      cons_trail_def remove_cls_def restart'_def tl_trail_def map_tl comp_def
      ac_simps mset_map_removeAll_cond mset_raw_init_clss_init_state rough_cdcl.state_def
      clause_def[symmetric] H split: twl_state.splits)
qed

interpretation rough_cdcl: abs_conflict_driven_clause_learning\<^sub>W
  clause
  raw_clss_l "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  remove1

  "\<lambda>C. raw_clause C" "\<lambda>C. TWL_Clause [] C"
  trail "\<lambda>S. hd (raw_trail S)"
  raw_init_clss raw_learned_clss backtrack_lvl raw_conflicting
  cons_trail tl_trail "\<lambda>C. add_learned_cls (raw_clause C)"
  "\<lambda>C. remove_cls (raw_clause C)"
  update_backtrack_lvl
  update_conflicting reduce_trail_to "\<lambda>N. init_state (map raw_clause N)" restart'
  by unfold_locales

declare local.rough_cdcl.mset_ccls_ccls_of_cls[simp del]

paragraph \<open>Opaque Type with Invariant\<close>

declare rough_cdcl.state_simp[simp del]

definition cons_trail_twl :: "('v, 'v twl_clause) ann_lit \<Rightarrow> 'v wf_twl \<Rightarrow> 'v wf_twl"
  where
"cons_trail_twl L S \<equiv> twl_of_rough_state (cons_trail L (rough_state_of_twl S))"

lemma wf_twl_state_cons_trail:
  assumes
    undef: "undefined_lit (raw_trail S) (lit_of L)" and
    wf: "wf_twl_state S"
  shows "wf_twl_state (cons_trail L S)"
  using undef wf wf_rewatch[of S ] unfolding wf_twl_state_def Ball_def
  by (auto simp: cons_trail_def defined_lit_map comp_def image_def twl.raw_clauses_def)

lemma rough_state_of_twl_cons_trail:
  "undefined_lit (raw_trail_twl S) (lit_of L) \<Longrightarrow>
    rough_state_of_twl (cons_trail_twl L S) = cons_trail L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_cons_trail
  unfolding cons_trail_twl_def by blast

abbreviation add_init_cls_twl where
"add_init_cls_twl C S \<equiv> twl_of_rough_state (add_init_cls C (rough_state_of_twl S))"

lemma wf_twl_add_init_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_init_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_init_cls_def comp_def twl.raw_clauses_def
    split: if_split_asm)

lemma rough_state_of_twl_add_init_cls:
  "rough_state_of_twl (add_init_cls_twl L S) = add_init_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_init_cls by blast

abbreviation add_learned_cls_twl where
"add_learned_cls_twl C S \<equiv> twl_of_rough_state (add_learned_cls C (rough_state_of_twl S))"

lemma wf_twl_add_learned_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (add_learned_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch add_learned_cls_def twl.raw_clauses_def
    split: if_split_asm)

lemma rough_state_of_twl_add_learned_cls:
  "rough_state_of_twl (add_learned_cls_twl L S) = add_learned_cls L (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_add_learned_cls by blast

abbreviation remove_cls_twl where
"remove_cls_twl C S \<equiv> twl_of_rough_state (remove_cls C (rough_state_of_twl S))"

lemma set_removeAll_condD: "x \<in> set (removeAll_cond f xs) \<Longrightarrow> x \<in> set xs"
  by (induction xs) (auto split: if_split_asm)

lemma wf_twl_remove_cls: "wf_twl_state S \<Longrightarrow> wf_twl_state (remove_cls L S)"
  unfolding wf_twl_state_def by (auto simp: wf_watch remove_cls_def twl.raw_clauses_def comp_def
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
  by (auto simp: wf_twl_state_def twl.raw_clauses_def)

lemma wf_twl_init_state: "wf_twl_state (init_state N)"
  unfolding init_state_def by (auto intro!: wf_twl_state_wf_twl_state_fold_add_init_cls)

lemma rough_state_of_twl_init_state:
  "rough_state_of_twl (init_state_twl N) = init_state N"
  by (simp add: twl_of_rough_state_inverse wf_twl_init_state)

abbreviation tl_trail_twl where
"tl_trail_twl S \<equiv> twl_of_rough_state (tl_trail (rough_state_of_twl S))"

lemma wf_twl_state_tl_trail: "wf_twl_state S \<Longrightarrow> wf_twl_state (tl_trail S)"
  by (auto simp add: twl_of_rough_state_inverse wf_twl_init_state wf_twl_cls_wf_twl_cls_tl
    tl_trail_def wf_twl_state_def distinct_tl map_tl comp_def twl.raw_clauses_def)

lemma rough_state_of_twl_tl_trail:
  "rough_state_of_twl (tl_trail_twl S) = tl_trail (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_tl_trail by blast

abbreviation update_backtrack_lvl_twl where
"update_backtrack_lvl_twl k S \<equiv> twl_of_rough_state (update_backtrack_lvl k (rough_state_of_twl S))"

lemma wf_twl_state_update_backtrack_lvl:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_backtrack_lvl k S)"
  unfolding wf_twl_state_def by (auto simp: comp_def twl.raw_clauses_def)

lemma rough_state_of_twl_update_backtrack_lvl:
  "rough_state_of_twl (update_backtrack_lvl_twl k S) = update_backtrack_lvl k
    (rough_state_of_twl S)"
  using rough_state_of_twl[of S] (* TODO remove explicit instantiation *)
    twl_of_rough_state_inverse[of "update_backtrack_lvl k (rough_state_of_twl S)"]
    wf_twl_state_update_backtrack_lvl[of "rough_state_of_twl S" k] by fast

abbreviation update_conflicting_twl where
"update_conflicting_twl k S \<equiv> twl_of_rough_state (update_conflicting k (rough_state_of_twl S))"

abbreviation reduce_trail_to_twl where
"reduce_trail_to_twl M1 S \<equiv> twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl S))"

lemma wf_twl_state_update_conflicting:
  "wf_twl_state S \<Longrightarrow> wf_twl_state (update_conflicting k S)"
  unfolding wf_twl_state_def by (auto simp: twl.raw_clauses_def comp_def)

lemma rough_state_of_twl_update_conflicting:
  "rough_state_of_twl (update_conflicting_twl k S) = update_conflicting k
    (rough_state_of_twl S)"
  using rough_state_of_twl twl_of_rough_state_inverse wf_twl_state_update_conflicting by fast

abbreviation raw_clauses_twl where
"raw_clauses_twl S \<equiv> twl.raw_clauses (rough_state_of_twl S)"

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
  using restart_learned by (auto simp: twl.raw_clauses_def comp_def dest: mset_union_mset_setD)

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
  have "\<And>C. C \<in> set (twl.raw_clauses S) \<Longrightarrow> wf_twl_cls (raw_trail S) C"
    using wf by (auto simp: S comp_def wf_twl_state_def)
  then show ?thesis
    unfolding wf_twl_state_def S
    using wf_twl_cls_append[of "take (length M - length M1) M" "drop (length M - length M1) M",
      unfolded M[symmetric]]
    by (simp_all add: n_d twl.raw_clauses_def)
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
    S: "rough_cdcl.state (rough_state_of_twl st) = (M, S)"
  shows
    "rough_cdcl.state
      (rough_state_of_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))) =
      (M1, S)" (is "?st") and
    "raw_init_clss_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = raw_init_clss_twl st" (is "?A") and
    "raw_learned_clss_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = raw_learned_clss_twl st" (is "?B") and
    "backtrack_lvl_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st)))
      = backtrack_lvl_twl st" (is "?C") and
    "rough_cdcl.conc_conflicting (rough_state_of_twl (twl_of_rough_state
         (reduce_trail_to M1 (rough_state_of_twl st))))
      = rough_cdcl.conc_conflicting (rough_state_of_twl st)"  (is "?D")
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
      "rough_cdcl.conc_conflicting (reduce_trail_to M1 (rough_state_of_twl st)) =
        rough_cdcl.conc_conflicting (rough_state_of_twl st)"
      using assms by (cases "rough_state_of_twl st", auto simp: drop_map[symmetric])+
  ultimately show ?A ?B ?C ?D
    using twl_of_rough_state_inverse[of "reduce_trail_to M1 (rough_state_of_twl st)"]
    rough_state_of_twl[of st]
    by (auto simp add: assms)
  moreover have "trail_twl (twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl st))) = M1"
    using trail_twl_twl_rough_state_reduce_trail_to[OF assms(1)] .
  ultimately show ?st using S unfolding rough_cdcl.state_def by auto
qed

sublocale wf_twl: abs_conflict_driven_clause_learning\<^sub>W
  clause
  raw_clss_l "op @"
  "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

  mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
  remove1

  "\<lambda>C. raw_clause C" "\<lambda>C. TWL_Clause [] C"
  trail_twl "\<lambda>S. hd (raw_trail_twl S)"
  raw_init_clss_twl
  raw_learned_clss_twl
  backtrack_lvl_twl
  raw_conflicting_twl
  cons_trail_twl
  tl_trail_twl
  "\<lambda>C. add_learned_cls_twl (raw_clause C)"
  "\<lambda>C. remove_cls_twl (raw_clause C)"
  update_backtrack_lvl_twl
  update_conflicting_twl
  reduce_trail_to_twl
  "\<lambda>N. init_state_twl (map raw_clause N)"
  restart_twl
proof goal_cases
  case 1
  have stupid_locales: "abs_state\<^sub>W_ops clause raw_clss_l op @ (\<lambda>L C. L \<in> set C) op #
    (\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)) mset union_mset_list remove1 raw_clause
    (TWL_Clause [])"
    by unfold_locales
  have ugly[simp]: "abs_state\<^sub>W_ops.mmset_of_mlit clause = mmset_of_mlit"
    apply (rule ext, rename_tac L, case_tac L)
    by (auto simp: abs_state\<^sub>W_ops.mmset_of_mlit.simps[OF stupid_locales] clause_def
    raw_clause_def)
  have [simp]: "\<And>S. raw_clss_l (restart_learned S) \<subseteq># rough_cdcl.conc_learned_clss S"
    using image_mset_subseteq_mono[OF restart_learned] unfolding mset_map
     by blast
  interpret abs_state\<^sub>W_ops  clause
    raw_clss_l "op @"
    "\<lambda>L C. L \<in> set C" "op #" "\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)"

    mset "\<lambda>xs ys. case_prod append (fold (\<lambda>x (ys, zs). (remove1 x ys, x # zs)) xs (ys, []))"
    remove1

    "\<lambda>C. raw_clause C" "\<lambda>C. TWL_Clause [] C"
    by unfold_locales
  have abs: "\<And>S. abs_state\<^sub>W_ops.state raw_clss_l mset trail_twl raw_init_clss_twl
    raw_learned_clss_twl backtrack_lvl_twl raw_conflicting_twl S =
    rough_cdcl.state (rough_state_of_twl S)"
    unfolding abs_state\<^sub>W_ops.state_def[OF stupid_locales] ..

  have "abs_state\<^sub>W clause raw_clss_l op @ (\<lambda>L C. L \<in> set C) op # (\<lambda>C. remove1_cond (\<lambda>D. clause D = clause C)) mset union_mset_list remove1 raw_clause (TWL_Clause []) trail_twl (\<lambda>S. hd (raw_trail_twl S)) raw_init_clss_twl raw_learned_clss_twl
     backtrack_lvl_twl raw_conflicting_twl cons_trail_twl (\<lambda>S. twl_of_rough_state (CDCL_Two_Watched_Literals.tl_trail (rough_state_of_twl S))) (\<lambda>C. add_learned_cls_twl (raw_clause C)) (\<lambda>C. remove_cls_twl (raw_clause C))
     (\<lambda>k S. twl_of_rough_state (CDCL_Two_Watched_Literals.update_backtrack_lvl k (rough_state_of_twl S))) (\<lambda>k S. twl_of_rough_state (CDCL_Two_Watched_Literals.update_conflicting k (rough_state_of_twl S)))
     (\<lambda>M1 S. twl_of_rough_state (reduce_trail_to M1 (rough_state_of_twl S))) (\<lambda>N. init_state_twl (map raw_clause N)) restart_twl"
    apply unfold_locales
           using rough_cdcl.hd_raw_conc_trail unfolding ugly apply blast
         apply (auto simp add: rough_state_of_twl_cons_trail rough_state_of_twl_tl_trail
           rough_state_of_twl_add_init_cls rough_state_of_twl_add_learned_cls
           rough_state_of_twl_remove_cls rough_state_of_twl_update_backtrack_lvl
           rough_state_of_twl_update_conflicting rough_cdcl.state_def
           abs)[7]
         defer
  using rough_cdcl.conc_init_clss_restart_state rough_cdcl.conc_learned_clss_restart_state
  apply (auto simp: rough_state_of_twl_restart_twl abs)[5]
  using twl_of_rough_state_reduce_trail_to(1) unfolding abs apply fast
  using init_clss_init_state


  apply (auto simp add:
       rough_cdcl.state_def rough_state_of_twl_init_state comp_def)
  done

  then show H: ?case
    apply intro_locales
    unfolding abs_state\<^sub>W_def by simp
qed

declare local.rough_cdcl.mset_ccls_ccls_of_cls[simp del]
abbreviation state_eq_twl (infix "\<sim>TWL" 51) where
"state_eq_twl S S' \<equiv> rough_cdcl.state_eq (rough_state_of_twl S) (rough_state_of_twl S')"
notation wf_twl.state_eq (infix "\<sim>" 51)

text \<open>To avoid ambiguities:\<close>
no_notation state_eq_twl (infix "\<sim>" 51)

paragraph \<open>Alternative Definition of CDCL using the candidates of 2-WL\<close>
inductive propagate_twl :: "'v wf_twl \<Rightarrow> 'v wf_twl \<Rightarrow> bool" where
propagate_twl_rule: "(L, C) \<in> candidates_propagate_twl S \<Longrightarrow>
  S' \<sim> cons_trail_twl (Propagated L C) S \<Longrightarrow>
  raw_conflicting_twl S = None \<Longrightarrow>
  propagate_twl S S'"

inductive_cases propagate_twlE: "propagate_twl S T"
lemma propagate_twl_iff_propagate:
  assumes inv: "cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv (wf_twl.state S)"
  shows "wf_twl.propagate_abs S T \<longleftrightarrow> propagate_twl S T" (is "?P \<longleftrightarrow> ?T")
proof
  assume ?P
  then obtain L E where
    "raw_conflicting_twl S = None" and
    CL_Clauses: "E \<in> set (wf_twl.raw_clauses S)" and
    LE: "L \<in># clause E" and
    tr_CNot: "trail_twl S \<Turnstile>as CNot (remove1_mset L (clause E))" and
    undef_lot[simp]: "undefined_lit (trail_twl S) L" and
    "T \<sim> cons_trail_twl (Propagated L E) S"
    by (blast elim: wf_twl.propagate_absE)
  have "distinct (raw_clause E)"
    using inv CL_Clauses unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def distinct_mset_set_def
    cdcl\<^sub>W_mset.distinct_cdcl\<^sub>W_state_def wf_twl.raw_clauses_def by (auto simp: clause_def)
  then have X: "remove1_mset L (mset (raw_clause E)) = mset_set (set (raw_clause E) - {L})"
    by (auto simp: multiset_eq_iff raw_clause_def count_mset distinct_filter_eq_if)
  have "(L, E) \<in> candidates_propagate_twl S"
    apply (rule wf_candidates_propagate_complete)
         using rough_state_of_twl apply auto[]
        using CL_Clauses unfolding wf_twl.raw_clauses_def twl.raw_clauses_def
        apply auto[]
       using LE apply (simp add: clause_def)
      using tr_CNot X apply (simp add: clause_def)
     using undef_lot apply blast
     done
  show ?T
    apply (rule propagate_twl_rule)
       apply (rule \<open>(L, E) \<in> candidates_propagate_twl S\<close>)
      using \<open>T \<sim> cons_trail_twl (Propagated L E) S\<close>
      apply (auto simp: \<open>raw_conflicting_twl S = None\<close> cdcl\<^sub>W_mset.state_eq_def)
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
    using LC unfolding candidates_propagate_def wf_twl.raw_clauses_def by auto
  have dist: "distinct (raw_clause C)"
    using inv C'S unfolding cdcl\<^sub>W_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_mset.distinct_cdcl\<^sub>W_state_def
     distinct_mset_set_def twl.raw_clauses_def by (fastforce simp: clause_def)
  then have C_L_L: "mset_set (set (raw_clause C) - {L}) = clause C - {#L#}"
    by (metis distinct_mset_distinct distinct_mset_minus distinct_mset_set_mset_ident mset_remove1
      set_mset_mset set_remove1_eq clause_def)

  show ?P
    apply (rule wf_twl.propagate_abs_rule[of S C L])
        using confl apply auto[]
       using C'S unfolding twl.raw_clauses_def apply (simp add: wf_twl.raw_clauses_def)
       using L unfolding candidates_propagate_def apply (auto simp: raw_clause_def clause_def)[]
      using wf_candidates_propagate_sound[OF _ LC] rough_state_of_twl dist
      apply (simp add: distinct_mset_remove1_All true_annots_true_cls clause_def)
     using undef apply simp
    using T undef unfolding cdcl\<^sub>W_mset.state_eq_def by auto
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
    D: "D \<in> set (wf_twl.raw_clauses S)" and
    MD: "trail_twl S \<Turnstile>as CNot (clause D)" and
    T: "T \<sim> update_conflicting_twl (Some (raw_clause D)) S"
    by (elim wf_twl.conflict_absE)

  have "D \<in> candidates_conflict_twl S"
    apply (rule wf_candidates_conflict_complete)
       apply simp
      using D apply (auto simp: wf_twl.raw_clauses_def twl.raw_clauses_def)[]
    using MD S by auto
  moreover have "T \<sim> twl_of_rough_state (update_conflicting (Some (raw_clause D))
  (rough_state_of_twl S))"
    using T unfolding cdcl\<^sub>W_mset.state_eq_def by auto
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
    "C \<in> set (wf_twl.raw_clauses S)"
    using C unfolding candidates_conflict_def wf_twl.raw_clauses_def twl.raw_clauses_def by auto
 moreover have "trail_twl S \<Turnstile>as CNot (clause C)"
    using wf_candidates_conflict_sound[OF _ C] by auto
 ultimately show ?C apply -
   apply (rule wf_twl.conflict_abs_rule[of _ C])
   using confl T unfolding cdcl\<^sub>W_mset.state_eq_def by (auto simp del: map_map)
qed

text \<open>We have shown that we we can use @{term conflict_twl} and @{term propagate_twl} in a CDCL
  calculus.\<close>
end

end