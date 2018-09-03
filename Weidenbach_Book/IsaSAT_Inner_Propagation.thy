theory IsaSAT_Inner_Propagation
  imports IsaSAT_Setup
     IsaSAT_Clauses "../lib/Explorer"
begin

subsection \<open>Propagations Step\<close>
context isasat_input_bounded
begin

lemma unit_prop_body_wl_D_invD:
  assumes \<open>unit_prop_body_wl_D_inv S j w L\<close>
  shows
    \<open>w < length (watched_by S L)\<close> and
    \<open>j \<le> w\<close> and
    \<open>fst (snd (watched_by_app S L w)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S)\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> get_clauses_wl S \<propto> fst (watched_by_app S L w) \<noteq> []\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> Suc 0 < length (get_clauses_wl S \<propto> fst (watched_by_app S L w))\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> get_clauses_wl S \<propto> fst (watched_by_app S L w) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> get_clauses_wl S \<propto> fst (watched_by_app S L w) ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> fst (watched_by_app S L w) > 0\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> get_conflict_wl S = None\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> fst (watched_by_app S L w)))\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> distinct (get_clauses_wl S \<propto> fst (watched_by_app S L w))\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close> and
    \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S) \<Longrightarrow> length (get_clauses_wl S \<propto> fst (watched_by_app S L w)) \<le> uint64_max\<close>
proof -
  let ?C = \<open>fst (watched_by_app S L w)\<close>
  show \<open>w < length (watched_by S L)\<close> and \<open>j \<le> w\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      unit_propagation_inner_loop_body_l_inv_def by fast+
  have \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close> and \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      unit_propagation_inner_loop_body_l_inv_def literals_are_\<L>\<^sub>i\<^sub>n_def by fast+
  then show \<open>fst (snd (watched_by_app S L w)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using \<open>w < length (watched_by S L)\<close> and \<open>j \<le> w\<close> nth_mem[of \<open>w\<close> \<open>watched_by S L\<close>]
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
    by (fastforce simp: watched_by_app_def image_image dest: multi_member_split
      simp del: nth_mem)
  assume C_dom: \<open>fst (watched_by_app S L w) \<in># dom_m (get_clauses_wl S)\<close>
  obtain T T' where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    S_T: \<open>(S, T) \<in> state_wl_l (Some (L, w))\<close> and
    \<open>L \<in># all_lits_of_mm
           (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close> and
    T_T': \<open>(set_clauses_to_update_l
       (clauses_to_update_l (remove_one_lit_from_wq (?C) T) +
        {#?C#})
       (remove_one_lit_from_wq (?C) T),
      T')
     \<in> twl_st_l (Some L)\<close> and
    \<open>correct_watching_except j w L S\<close> and
    struct: \<open>twl_struct_invs T'\<close> and
    \<open>w < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    stgy: \<open>twl_stgy_invs T'\<close> and
    \<open>?C
     \<in># dom_m
         (get_clauses_l (remove_one_lit_from_wq (?C) T))\<close> and
    watched_ge_0: \<open>0 < ?C\<close> and
    \<open>0 < length
          (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
           (?C))\<close> and
    \<open>no_dup (get_trail_l (remove_one_lit_from_wq (?C) T))\<close> and
    i_le: \<open>(if get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C) !
         0 =
         L
      then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C))\<close> and
    ui_le: \<open>1 - (if get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
             (?C) !
             0 =
             L
          then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C))\<close> and
    \<open>L \<in> set (watched_l
               (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
                (?C)))\<close> and
    \<open>get_conflict_l (remove_one_lit_from_wq (?C) T) = None\<close>
    using assms C_dom unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_alt_def
      watched_by_app_def unit_propagation_inner_loop_body_l_inv_def
    apply - apply normalize_goal+
    by blast
  show S_L_W_le_S: \<open>?C \<in># dom_m (get_clauses_wl S)\<close>
    using C_dom unfolding watched_by_app_def by auto
  show
    \<open>get_clauses_wl S \<propto> ?C \<noteq> []\<close> and
    le: \<open>Suc 0 < length (get_clauses_wl S \<propto> ?C)\<close>
    using ui_le i_le S_T
    unfolding watched_by_app_def
    by (auto simp: twl_st_wl)
  have S_L_w_ge_0: \<open>0 < ?C\<close>
    using watched_ge_0 unfolding watched_by_app_def by auto
  obtain M N D NE UE W Q where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> ?C))\<close>
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of ])
    apply (rule S_L_W_le_S)
    using lits by auto
  then show \<open>get_clauses_wl S \<propto> ?C ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using le apply (cases \<open>get_clauses_wl S \<propto> ?C\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show \<open>get_clauses_wl S \<propto> ?C ! Suc 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using lits_N le apply (cases \<open>get_clauses_wl S \<propto> ?C\<close>;
        cases \<open>tl (get_clauses_wl S \<propto> ?C)\<close>;
        cases \<open>tl (tl (get_clauses_wl S \<propto> ?C))\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show S_L_W_ge_0: \<open>?C > 0\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>get_conflict_wl S = None\<close>
    using confl watched_ge_0 lits unfolding watched_by_app_def
    by fast+
  have all_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of T')\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of T'). \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of T')\<close>
    using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>\<forall>D\<in>mset ` set_mset (ran_mf (get_clauses_wl S)). distinct_mset D\<close>
    using dist
    using S_T T_T'
    unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: clauses_def twl_st_wl twl_st_l twl_st
        watched_by_app_def Ball_def Collect_conv_if
        distinct_mset_set_def conj_disj_distribR Collect_disj_eq image_mset_union
      dest!: multi_member_split
      split: if_splits)
  then show \<open>distinct (get_clauses_wl S \<propto> ?C)\<close>
    using S_L_W_le_S S_L_W_ge_0
    by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct
         clauses_def mset_take_mset_drop_mset watched_by_app_def)
  show \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using  \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>  .
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T')\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have N: \<open>atm_of ` lits_of_l (trail (state\<^sub>W_of T')) \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of T'))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases S)
       (auto simp: cdcl\<^sub>W_restart_mset_state mset_take_mset_drop_mset')
  then have N: \<open>atm_of ` lits_of_l (trail (state\<^sub>W_of T')) \<subseteq> atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of T'))\<close>
    by (auto simp: cdcl\<^sub>W_restart_mset.clauses_def)
  then show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close>
    using in_all_lits_of_m_ain_atms_of_iff S_T T_T' lits
    unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def in_all_lits_of_mm_ain_atms_of_iff image_subset_iff
    by (auto 5 5  simp:  trail.simps in_all_lits_of_mm_ain_atms_of_iff
      lits_of_def image_image init_clss.simps mset_take_mset_drop_mset'  literals_are_\<L>\<^sub>i\<^sub>n_def
      convert_lits_l_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
      twl_st_l twl_st_wl twl_st get_unit_clauses_wl_alt_def)
  show \<open>length (get_clauses_wl S \<propto> ?C) \<le> uint64_max\<close>
    using clss_size_uint64_max[of \<open>mset (get_clauses_wl S \<propto> ?C)\<close>,
        OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> ?C))\<close>]
      \<open>distinct (get_clauses_wl S \<propto> ?C)\<close> by auto
qed


definition (in -) find_unwatched_wl_st  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, D, NE, UE, Q, W) i. do {
    find_unwatched_l M (N \<propto> i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto> C) = find_unwatched_wl_st S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_st_def)

definition (in isasat_input_ops) find_non_false_literal_between where
  \<open>find_non_false_literal_between M a b C =
     find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) a b C\<close>

(* TODO change to return the iterator (i) instead of the position in the clause *)
definition (in isasat_input_ops) isa_find_unwatched_between
 :: \<open>_ \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close> where
\<open>isa_find_unwatched_between P NU a b C = do {
  ASSERT(C+a \<le> length NU);
  ASSERT(C+b \<le> length NU);
  (x, _) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). True\<^esup>
    (\<lambda>(found, i). found = None \<and> i < C + b)
    (\<lambda>(_, i). do {
      ASSERT(i < C + nat_of_uint64_conv (arena_length NU C));
      ASSERT(arena_lit NU i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
      ASSERT(i \<ge> C);
      ASSERT(i < C + b);
      ASSERT(arena_lit_pre NU i);
      if P (arena_lit NU i) then RETURN (Some (i - C), i) else RETURN (None, i+1)
    })
    (None, C+a);
  RETURN x
}
\<close>


lemma (in isasat_input_ops) isa_find_unwatched_between_find_in_list_between_spec:
  assumes \<open>a \<le> length (N \<propto> C)\<close> and \<open>b \<le> length (N \<propto> C)\<close> and \<open>a \<le> b\<close> and \<open>valid_arena arena N vdom\<close>
    and \<open>C \<in># dom_m N\<close> and eq: \<open>a' = a\<close> \<open>b' = b\<close> \<open>P' = P\<close> \<open>C' = C\<close>
  assumes lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> C))\<close>
  shows
    \<open>isa_find_unwatched_between P' arena a' b' C' \<le> \<Down> Id (find_in_list_between P a b (N \<propto> C))\<close>
proof -
  have [refine0]: \<open>((None, x2m + a), None, a) \<in> \<langle>Id\<rangle>option_rel \<times>\<^sub>r {(n', n). n' = x2m + n}\<close>
    for x2m
    by auto
  have [simp]: \<open>arena_lit arena (C + x2) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> if \<open>x2 < length (N \<propto> C)\<close> for x2
    using that lits assms by (auto simp: arena_lifting
       dest!: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of _ x2])
  have arena_lit_pre: \<open>arena_lit_pre arena x2a\<close>
    if
      \<open>(x, x') \<in> \<langle>nat_rel\<rangle>option_rel \<times>\<^sub>f {(n', n). n' = C + n}\<close> and
      \<open>case x of (found, i) \<Rightarrow> found = None \<and> i < C + b\<close> and
      \<open>case x' of (found, i) \<Rightarrow> found = None \<and> i < b\<close> and
      \<open>case x of (found, i) \<Rightarrow> True\<close> and
      \<open>case x' of
      (found, i) \<Rightarrow>
        a \<le> i \<and>
        i \<le> length (N \<propto> C) \<and>
        i \<le> b \<and>
        (\<forall>j\<in>{a..<i}. \<not> P (N \<propto> C ! j)) \<and>
        (\<forall>j. found = Some j \<longrightarrow> i = j \<and> P (N \<propto> C ! j) \<and> j < b \<and> a \<le> j)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>x2 < length (N \<propto> C)\<close> and
      \<open>x2a < C + nat_of_uint64_conv (arena_length arena C)\<close> and
      \<open>arena_lit arena x2a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
      \<open>C \<le> x2a\<close>
    for x x' x1 x2 x1a x2a
  proof -
    show ?thesis
      unfolding arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      apply (rule bex_leI[of _ C])
      apply (rule exI[of _ N])
      apply (rule exI[of _ vdom])
      using assms that by auto
  qed

  show ?thesis
    unfolding isa_find_unwatched_between_def find_in_list_between_def eq
    apply refine_vcg
    subgoal using assms by (auto dest!: arena_lifting(10))
    subgoal using assms by (auto dest!: arena_lifting(10))
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by (rule arena_lit_pre)
    subgoal using assms by (auto simp: arena_lifting)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition (in isasat_input_ops) isa_find_non_false_literal_between where
  \<open>isa_find_non_false_literal_between M arena a b C =
     isa_find_unwatched_between (\<lambda>L. polarity M L \<noteq> Some False) arena a b C\<close>

definition (in isasat_input_ops) find_unwatched
  :: \<open>(nat literal \<Rightarrow> bool) \<Rightarrow> nat clause_l \<Rightarrow> (nat option) nres\<close> where
\<open>find_unwatched M C = do {
    b \<leftarrow> SPEC(\<lambda>b::bool. True); \<comment> \<open>non-deterministic between full iteration (used in minisat),
      or starting in the middle (use in cadical)\<close>
    if b then find_in_list_between M 2 (length C) C
    else do {
      pos \<leftarrow> SPEC (\<lambda>i. i \<le> length C \<and> i \<ge> 2);
      n \<leftarrow> find_in_list_between M pos (length C) C;
      if n = None then find_in_list_between M 2 pos C
      else RETURN n
    }
  }
\<close>

definition (in isasat_input_ops) find_unwatched_wl_st_heur_pre where
  \<open>find_unwatched_wl_st_heur_pre =
     (\<lambda>(S, i). arena_is_valid_clause_idx (get_clauses_wl_heur S) i)\<close>

definition (in isasat_input_ops) find_unwatched_wl_st
  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, D, Q, W, vm, \<phi>) i. do {
    find_unwatched (\<lambda>L. polarity M L \<noteq> Some False) (N \<propto> i)
  })\<close>


(* TODO change to return the iterator (i) instead of the position in the clause *)
definition (in isasat_input_ops) isa_find_unwatched
  :: \<open>(nat literal \<Rightarrow> bool) \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> (nat option) nres\<close>
where
\<open>isa_find_unwatched P arena C = do {
    let l = nat_of_uint64_conv (arena_length arena C);
    b \<leftarrow> RETURN(arena_length arena C \<le> 5);
    if b then isa_find_unwatched_between P arena 2 l C
    else do {
      ASSERT(get_saved_pos_pre arena C);
      pos \<leftarrow> RETURN (nat_of_uint64_conv (arena_pos arena C));
      n \<leftarrow> isa_find_unwatched_between P arena pos l C;
      if n = None then isa_find_unwatched_between P arena 2 pos C
      else RETURN n
    }
  }
\<close>

lemma isa_find_unwatched_find_unwatched:
  assumes valid: \<open>valid_arena arena N vdom\<close> and
     \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> C))\<close> and
     ge2: \<open>2 \<le> length (N \<propto> C)\<close> and
     C: \<open>C \<in># dom_m N\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> C))\<close>
  shows \<open>isa_find_unwatched P arena C \<le> \<Down> Id (find_unwatched P (N \<propto> C))\<close>
proof -
  have [refine0]:
    \<open>RETURN(arena_length arena C \<le> 5) \<le>
      \<Down> {(b,b'). b = b' \<and> (b \<longleftrightarrow> is_short_clause (N\<propto>C))}
        (SPEC (\<lambda>_. True))\<close>
    using assms
    by (auto simp: RETURN_RES_refine_iff is_short_clause_def arena_lifting)
  show ?thesis
    unfolding isa_find_unwatched_def find_unwatched_def nat_of_uint64_conv_def Let_def
    apply (refine_vcg isa_find_unwatched_between_find_in_list_between_spec[of _ _ _ _ _ vdom])
    subgoal by auto
    subgoal using ge2 .
    subgoal by auto
    subgoal using ge2 .
    subgoal using valid .
    subgoal using C .
    subgoal using assms by auto
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal using assms by auto
    subgoal using assms unfolding get_saved_pos_pre_def   arena_is_valid_clause_idx_def
      by (auto simp: arena_lifting)
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal by (auto simp: arena_pos_def)
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal using assms by auto
    subgoal using assms by (auto simp: arena_lifting)
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms arena_lifting[OF valid C] by auto
    subgoal by (auto simp: arena_pos_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    done
qed

definition (in isasat_input_ops) isa_find_unwatched_wl_st_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>isa_find_unwatched_wl_st_heur = (\<lambda>(M, N, D, Q, W, vm, \<phi>) i. do {
    isa_find_unwatched (\<lambda>L. polarity M L \<noteq> Some False) N i
  })\<close>



lemma (in isasat_input_ops) find_unwatched:
  assumes n_d: \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close> and \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)\<close>
  shows \<open>find_unwatched (\<lambda>L. polarity M L \<noteq> Some False) C \<le> \<Down> Id (find_unwatched_l M C)\<close>
proof -
  have [refine0]: \<open>find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) 2 (length C) C
        \<le> SPEC
          (\<lambda>found.
              (found = None) = (\<forall>L\<in>set (unwatched_l C). - L \<in> lits_of_l M) \<and>
              (\<forall>j. found = Some j \<longrightarrow>
                    j < length C \<and>
                    (undefined_lit M (C ! j) \<or> C ! j \<in> lits_of_l M) \<and> 2 \<le> j))\<close>
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule find_in_list_between_spec)
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal
        using n_d
        by (auto simp add: polarity_def in_set_drop_conv_nth Ball_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
      done
  qed
  have [refine0]: \<open>find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) xa (length C) C
        \<le> SPEC
          (\<lambda>n. (if n = None
                then find_in_list_between (\<lambda>L. polarity M L \<noteq> Some False) 2 xa C
                else RETURN n)
                \<le> SPEC
                  (\<lambda>found.
                      (found = None) =
                      (\<forall>L\<in>set (unwatched_l C). - L \<in> lits_of_l M) \<and>
                      (\<forall>j. found = Some j \<longrightarrow>
                            j < length C \<and>
                            (undefined_lit M (C ! j) \<or> C ! j \<in> lits_of_l M) \<and>
                            2 \<le> j)))\<close>
    if
      \<open>xa \<le> length C \<and> 2 \<le> xa\<close>
    for xa
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule find_in_list_between_spec)
      subgoal using that by auto
      subgoal using assms by auto
      subgoal using that by auto
      subgoal
        apply (rule SPEC_rule)
        subgoal for x
          apply (cases \<open>x = None\<close>; simp only: if_True if_False refl)
        subgoal
          apply (rule order_trans)
          apply (rule find_in_list_between_spec)
          subgoal using that by auto
          subgoal using that by auto
          subgoal using that by auto
          subgoal
            apply (rule SPEC_rule)
            apply (intro impI conjI iffI ballI)
            unfolding in_set_drop_conv_nth Ball_def
            apply normalize_goal
            subgoal for x L xaa
              apply (cases \<open>xaa \<ge> xa\<close>)
              subgoal
                using n_d
                by (auto simp add: polarity_def  Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
              subgoal
                using n_d
                by (auto simp add: polarity_def  Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
              done
            subgoal for x  (* TODO Proof *)
              using n_d that assms
              by (auto simp add: polarity_def  Ball_def all_conj_distrib
              Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD,
                force)
               (metis diff_is_0_eq' le_neq_implies_less le_trans less_imp_le_nat
                no_dup_consistentD zero_less_diff)
            subgoal
              using n_d assms that
              by (auto simp add: polarity_def Ball_def all_conj_distrib
                Decided_Propagated_in_iff_in_lits_of_l
                  split: if_splits dest: no_dup_consistentD)
            done
          done
        subgoal (* TODO Proof *)
          using n_d that assms le_trans
          by (auto simp add: polarity_def  Ball_def all_conj_distrib in_set_drop_conv_nth
               Decided_Propagated_in_iff_in_lits_of_l split: if_splits dest: no_dup_consistentD)
            (use le_trans no_dup_consistentD in blast)+
        done
      done
    done
  qed

  show ?thesis
    unfolding find_unwatched_def find_unwatched_l_def
    apply (refine_vcg)
    subgoal by blast
    subgoal by blast
    done
qed

definition (in isasat_input_ops) find_unwatched_wl_st_pre where
  \<open>find_unwatched_wl_st_pre =  (\<lambda>(S, i).
    i \<in># dom_m (get_clauses_wl S) \<and>
    literals_are_\<L>\<^sub>i\<^sub>n S \<and> 2 \<le> length (get_clauses_wl S \<propto> i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> i))
    )\<close>

theorem find_unwatched_wl_st_heur_find_unwatched_wl_s:
  \<open>(uncurry isa_find_unwatched_wl_st_heur, uncurry find_unwatched_wl_st)
    \<in> [find_unwatched_wl_st_pre]\<^sub>f
      twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have [refine0]: \<open>((None, x2m + 2), None, 2) \<in> \<langle>Id\<rangle>option_rel \<times>\<^sub>r {(n', n). n' = x2m + n}\<close>
    for x2m
    by auto
  have [refine0]:
    \<open>(polarity M (arena_lit arena i'), polarity M' (N \<propto> C' ! j))
    \<in> \<langle>Id\<rangle>option_rel\<close>
    if \<open>\<exists>vdom. valid_arena arena N vdom\<close> and
      \<open>C' \<in># dom_m N\<close> and
      \<open>i' = C' + j \<and> j < length (N \<propto> C')\<close> and
       \<open>M = M'\<close>
    for M arena i i' N j M' C'
    using that by (auto simp: arena_lifting)
  have [refine0]: \<open>RETURN (arena_pos arena C) \<le> \<Down> {(pos, pos'). pos = pos' \<and> pos \<ge> 2 \<and> pos \<le> length (N \<propto> C)}
         (SPEC (\<lambda>i. i \<le> length (N \<propto> C') \<and> 2 \<le> i))\<close>
    if valid: \<open>valid_arena arena N vdom\<close> and C: \<open>C \<in># dom_m N\<close> and \<open>C = C'\<close> and
       \<open>is_long_clause (N \<propto> C')\<close>
    for arena N vdom C C'
    using that arena_lifting[OF valid C] by (auto simp: RETURN_RES_refine_iff
      arena_pos_def)
  have [refine0]:
    \<open>RETURN (arena_length arena C \<le> 5) \<le> \<Down> {(b, b'). b = b' \<and> (b \<longleftrightarrow> is_short_clause (N \<propto> C))}
     (SPEC(\<lambda>_. True))\<close>
    if valid: \<open>valid_arena arena N vdom\<close> and C: \<open>C \<in># dom_m N\<close>
    for arena N vdom C
    using that arena_lifting[OF valid C] by (auto simp: RETURN_RES_refine_iff is_short_clause_def)

  have H: \<open>isa_find_unwatched M arena C \<le> \<Down> Id (find_unwatched M' (N \<propto> C'))\<close>
    if \<open>valid_arena arena N vdom\<close> and \<open>C \<in># dom_m N\<close> and \<open>M = M'\<close> and \<open>C = C'\<close> and
      \<open>2 \<le> length (N \<propto> C')\<close> and \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N \<propto> C'))\<close>
    for arena M N C vdom M' C'
    unfolding isa_find_unwatched_def find_unwatched_def nat_of_uint64_conv_def Let_def
    apply (refine_vcg isa_find_unwatched_between_find_in_list_between_spec[of _ _ _ _ _ vdom])
    using that apply - apply assumption
    using that apply - apply assumption
    subgoal by auto
    subgoal using that by (simp add: arena_lifting)
    subgoal using that by auto
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting get_saved_pos_pre_def
       arena_is_valid_clause_idx_def)
    using that apply - apply assumption
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    subgoal using that by (auto simp: arena_lifting)
    done

  show ?thesis
    unfolding isa_find_unwatched_wl_st_heur_def find_unwatched_wl_st_def
       uncurry_def twl_st_heur_def
      find_unwatched_wl_st_pre_def
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal for x y by (rule H[of _ _ \<open>set (get_vdom (fst x))\<close>]) auto
    done
qed

definition (in isasat_input_ops) isa_save_pos :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>isa_save_pos C i = (\<lambda>(M, N, oth). do {
      ASSERT(arena_is_valid_clause_idx N C);
      if arena_length N C > MAX_LENGTH_SHORT_CLAUSE then do {
        ASSERT(isa_update_pos_pre ((C, i), N));
        RETURN (M, arena_update_pos C i N, oth)
      } else RETURN (M, N, oth)
    })
  \<close>

sepref_register isa_save_pos
sepref_thm isa_save_pos_code
  is \<open>uncurry2 (PR_CONST isa_save_pos)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp]
  unfolding isa_save_pos_def PR_CONST_def isasat_assn_def
  by sepref

concrete_definition (in -) isa_save_pos_code
   uses isasat_input_bounded.isa_save_pos_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) isa_save_pos_code_def

lemmas isa_save_pos_code_hnr[sepref_fr_rules] =
   isa_save_pos_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms, unfolded PR_CONST_def]

lemma (in isasat_input_ops) isa_save_pos_is_Id:
  assumes
     \<open>(S, T) \<in> twl_st_heur\<close>
     \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
     \<open>is_long_clause (get_clauses_wl T \<propto> C)\<close> and
     \<open>i \<le> length (get_clauses_wl T \<propto> C)\<close> and
     \<open>i \<ge> 2\<close>
  shows \<open>isa_save_pos C i S \<le> \<Down> twl_st_heur (RETURN T)\<close>
proof -
  have  \<open>isa_update_pos_pre ((C, i), get_clauses_wl_heur S)\<close>
    unfolding isa_update_pos_pre_def
    using assms
    by (cases S; cases T)
      (auto simp: isa_save_pos_def twl_st_heur_def arena_update_pos_alt_def
          isa_update_pos_pre_def arena_is_valid_clause_idx_def arena_lifting
          is_short_clause_def)
  then show ?thesis
    using assms
    by (cases S; cases T)
      (auto simp: isa_save_pos_def twl_st_heur_def arena_update_pos_alt_def
          isa_update_pos_pre_def arena_is_valid_clause_idx_def arena_lifting
          intro!: valid_arena_update_pos)
qed

lemmas unit_prop_body_wl_D_invD' =
  unit_prop_body_wl_D_invD[of \<open>(M, N, D, NE, UE, WS, Q)\<close> for M N D NE UE WS Q,
   unfolded watched_by_app_def,
    simplified] unit_prop_body_wl_D_invD(7)


definition (in isasat_input_ops) set_conflict_wl' :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl' =
      (\<lambda>C (M, N, D, NE, UE, Q, W). (M, N, Some (mset (N\<propto>C)), NE, UE, {#}, W))\<close>

lemma set_conflict_wl'_alt_def:
  \<open>set_conflict_wl' i S = set_conflict_wl (get_clauses_wl S \<propto> i) S\<close>
  by (cases S) (auto simp: set_conflict_wl'_def set_conflict_wl_def)

definition (in isasat_input_ops) set_conflict_wl_heur_pre where
  \<open>set_conflict_wl_heur_pre =
     (\<lambda>(C, S).
        literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S) \<and>
        no_dup (get_trail_wl_heur S)
       )\<close>

definition (in isasat_input_ops) set_conflict_wl_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>set_conflict_wl_heur = (\<lambda>C (M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats, fema, sema). do {
    let n = zero_uint32_nat;
    ASSERT(curry6 isa_set_lookup_conflict_aa_pre M N C D n lbd outl);
    (D, clvls, lbd, outl) \<leftarrow> isa_set_lookup_conflict_aa M N C D n lbd outl;
    RETURN (M, N, D, length_u M, W, vmtf, \<phi>, clvls, cach, lbd, outl, incr_conflict stats, fema, sema)})\<close>


definition (in isasat_input_ops) update_clause_wl_code_pre where
  \<open>update_clause_wl_code_pre = (\<lambda>(((((((L, C), b), j), w), i), f), S).
      arena_is_valid_clause_idx_and_access (get_clauses_wl_heur S) C f \<and>
      nat_of_lit L < length (get_watched_wl_heur S) \<and>
      nat_of_lit (arena_lit (get_clauses_wl_heur S)  (C + f))  < length (get_watched_wl_heur S) \<and>
      w < length (get_watched_wl_heur S ! nat_of_lit L) \<and>
      j \<le> w)\<close>

definition (in isasat_input_ops) update_clause_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) C b j w i f (M, N, D, Q, W, vm). do {
     ASSERT(arena_lit_pre N (C+f));
     let K' = arena_lit N (C + f);
     ASSERT(swap_lits_pre C i f N);
     let N' = swap_lits C i f N;
     let W = W[nat_of_lit K':= W ! (nat_of_lit K') @ [to_watcher C L b]];
     RETURN (j, w+1, (M, N', D, Q, W, vm))
  })\<close>

definition (in isasat_input_ops) update_clause_wl_pre where
  \<open>update_clause_wl_pre = (\<lambda>(((((((L, C), b), j), w), i), f), S). C \<in># dom_m(get_clauses_wl S) \<and>
     L\<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> i < length (get_clauses_wl S \<propto> C) \<and> f < length (get_clauses_wl S \<propto> C))\<close>

lemma update_clause_wl_heur_update_clause_wl:
  \<open>(uncurry7 update_clause_wl_heur, uncurry7 (update_clause_wl)) \<in>
   [update_clause_wl_pre]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>
  \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (auto 0 0 simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def twl_st_heur'_def update_clause_wl_pre_def arena_lifting arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def swap_lits_pre_def
    intro!: ASSERT_refine_left valid_arena_swap_lits
    intro!: bex_leI exI)
  by (auto 0 0 simp add: arena_lifting)

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) \<propto> i ! j\<close>

definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j).
           arena_lit_pre (get_clauses_wl_heur S) (i+j))\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = arena_lit (get_clauses_wl_heur S) (i + j)\<close>

lemma access_lit_in_clauses_heur_alt_def:
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j.  arena_lit N (i + j))\<close>
  by (auto simp: access_lit_in_clauses_heur_def intro!: ext)

lemma twl_st_heur_get_clauses_access_lit[simp]:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
    i < length (get_clauses_wl T \<propto> C) \<Longrightarrow>
    get_clauses_wl T \<propto> C ! i = access_lit_in_clauses_heur S C i\<close>
    for S T C i
    by (cases S; cases T)
      (auto simp: arena_lifting twl_st_heur_def access_lit_in_clauses_heur_def)

definition (in isasat_input_ops) clause_not_marked_to_delete where
  \<open>clause_not_marked_to_delete S C \<longleftrightarrow> C \<in># dom_m (get_clauses_wl S)\<close>

definition (in isasat_input_ops) clause_not_marked_to_delete_pre where
  \<open>clause_not_marked_to_delete_pre = (\<lambda>(S, C). C \<in> vdom_m (get_watched_wl S) (get_clauses_wl S))\<close>

definition (in isasat_input_ops) clause_not_marked_to_delete_heur_pre where
  \<open>clause_not_marked_to_delete_heur_pre =
     (\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C)\<close>

definition (in isasat_input_ops) clause_not_marked_to_delete_heur :: "_ \<Rightarrow> nat \<Rightarrow> bool"
where
  \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> arena_status (get_clauses_wl_heur S) C \<noteq> DELETED\<close>

lemma clause_not_marked_to_delete_rel:
  \<open>(uncurry (RETURN oo clause_not_marked_to_delete_heur),
    uncurry (RETURN oo clause_not_marked_to_delete)) \<in>
    [clause_not_marked_to_delete_pre]\<^sub>f
     twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (use arena_dom_status_iff in_dom_in_vdom in
      \<open>auto 5 5 simp: clause_not_marked_to_delete_def twl_st_heur_def
        clause_not_marked_to_delete_heur_def arena_dom_status_iff
        clause_not_marked_to_delete_pre_def\<close>)

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S \<propto> fst (watched_by_app S L C)))\<close>
    (is ?tauto is \<open>\<not>tautology ?D\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (fst (watched_by_app S L C)) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S j C L\<close> and
    val: \<open>polarity_st S (get_clauses_wl S \<propto> fst (watched_by_app S L C) !
         (1 - (if access_lit_in_clauses S (fst (watched_by_app S L C)) 0 = L then 0 else 1))) =
          Some False\<close>
      (is \<open>polarity_st _ (_ \<propto> _ ! ?i) = Some False\<close>) and
    dom: \<open>fst (watched_by S L ! C) \<in># dom_m (get_clauses_wl S)\<close>
  for S C xj L
proof  -
  obtain M N D NE UE WS Q where
    S: \<open>S = (M, N, D, NE, UE, WS, Q)\<close>
    by (cases S)
  let ?C = \<open>fst (watched_by S L ! C)\<close>
  obtain T T' where
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
     \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
     S_T: \<open>(S, T) \<in> state_wl_l (Some (L, C))\<close> and
    \<open>L \<in># all_lits_of_mm
                  (mset `# init_clss_lf (get_clauses_wl S) + get_unit_clauses_wl S)\<close> and
    T_T': \<open>(set_clauses_to_update_l
       (clauses_to_update_l (remove_one_lit_from_wq (?C) T) +
        {#?C#})
       (remove_one_lit_from_wq (?C) T),
      T')
     \<in> twl_st_l (Some L)\<close> and
    inv: \<open>twl_struct_invs T'\<close> and
    C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    stgy_invs: \<open>twl_stgy_invs T'\<close> and
    \<open>?C \<in># dom_m
         (get_clauses_l (remove_one_lit_from_wq (?C) T))\<close> and
    \<open>0 < ?C\<close> and
    \<open>0 < length
          (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
           (?C))\<close> and
    \<open>no_dup (get_trail_l (remove_one_lit_from_wq (?C) T))\<close> and
    i_le: \<open>(if get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C) !
         0 =
         L
      then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C))\<close> and
    ui_le: \<open>1 - (if get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
             (?C) !
             0 =
             L
          then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
         (?C))\<close> and
    \<open>L \<in> set (watched_l
               (get_clauses_l (remove_one_lit_from_wq (?C) T) \<propto>
                (?C)))\<close> and
    \<open>get_conflict_l (remove_one_lit_from_wq (?C) T) = None\<close>
  using inv dom unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_alt_def
  unit_propagation_inner_loop_body_l_inv_def watched_by_app_def
  apply (simp only: dom simp_thms)
  apply normalize_goal+
  by blast

  have L_WS: \<open>(L, twl_clause_of (get_clauses_wl S \<propto> ?C)) \<in># clauses_to_update T'\<close>
    using S_T T_T' confl by (cases T') (auto simp: twl_st_l_def state_wl_l_def S)
  have \<open>consistent_interp (lits_of_l (trail (state\<^sub>W_of T')))\<close> and
    n_d: \<open>no_dup (trail (state\<^sub>W_of T'))\<close> and
    valid: \<open>valid_enqueued T'\<close> and
    n_d_q: \<open>no_duplicate_queued T'\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    using S_T T_T' by (auto simp: twl_st_l twl_st twl_st_wl)

  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S \<propto> (?C))).
         - L \<in> lits_of_l (get_trail_wl S)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def watched_by_app_def
    by auto
  moreover {
    have \<open>add_mset L (literals_to_update T') \<subseteq>#
       {#- lit_of x. x \<in># mset (get_trail T')#}\<close>
      using n_d_q S_T T_T' L_WS
      by (cases \<open>clauses_to_update T'\<close>)
        (auto simp add: no_duplicate_queued_alt_def twl_st_wl twl_st_l twl_st)
    note mset_subset_eq_insertD[OF this]
    moreover have \<open>xa \<in> set x \<Longrightarrow>
       (M, x) \<in> convert_lits_l N (NE + UE) \<Longrightarrow>
       lit_of xa \<in> lit_of ` set M\<close> for xa x
      using imageI[of xa \<open>set x\<close> lit_of]
      by (auto simp: twl_st_wl twl_st_l twl_st S state_wl_l_def twl_st_l_def lits_of_def
          dest: imageI[of _ \<open>set _\<close> \<open>lit_of\<close>])
    ultimately have \<open>- L \<in> lits_of_l M\<close>
      using S_T T_T'
      by (auto simp: twl_st_wl twl_st_l twl_st S state_wl_l_def twl_st_l_def lits_of_def
          dest: imageI[of _ \<open>set _\<close> \<open>lit_of\<close>])
  }
  moreover have \<open>- get_clauses_wl S \<propto> ?C ! ?i \<in> lits_of_l M\<close>
    using val by (auto simp: S polarity_st_def watched_by_app_def polarity_def
        access_lit_in_clauses_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  moreover have length_C: \<open>length (get_clauses_wl S \<propto> ?C) \<ge> 2\<close>
    using i_le ui_le S_T T_T'
    by (auto simp: watched_by_app_def twl_st_wl twl_st_l twl_st S)
  moreover {
    have QL: \<open>Q L ! C = hd (drop C (Q L))\<close>
      using confl C_le length_C by (auto simp: S hd_drop_conv_nth split: )
    have \<open>L \<in># mset (watched_l (get_clauses_wl S \<propto> ?C))\<close>
      using valid confl C_le length_C S_T T_T' by (auto simp: QL S take_2_if watched_by_app_def
          twl_st_wl twl_st_l twl_st S)
    then have \<open>N \<propto> (fst (Q L ! C)) ! 0 = L \<or> N \<propto> (fst (Q L ! C)) ! 1 = L\<close>
      using confl C_le length_C by (auto simp: S take_2_if watched_by_app_def QL split: if_splits)
  }
  ultimately have Not: \<open>lits_of_l (get_trail_wl S) \<Turnstile>s CNot ?D\<close>
    unfolding true_clss_def_iff_negation_in_model polarity_def polarity_st_def
    unfolding mset_append watched_by_app_def access_lit_in_clauses_def
    by (subst (1) append_take_drop_id[symmetric, of _ 2])
      (auto simp: S take_2_if hd_conv_nth uminus_lit_swap
        twl_st_wl twl_st_l twl_st S split: if_splits)
  show ?thesis
    using consistent_CNot_not_tautology[OF cons Not] .
qed

definition (in isasat_input_ops) propagate_lit_wl_heur_pre where
  \<open>propagate_lit_wl_heur_pre =
     (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
        i \<le> 1 \<and> C \<noteq> DECISION_REASON)\<close>

definition (in isasat_input_ops) propagate_lit_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>propagate_lit_wl_heur = (\<lambda>L' C i (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats,
    fema, sema). do {
      ASSERT(swap_lits_pre C 0 (fast_minus 1 i) N);
      let N' = swap_lits C 0 (fast_minus 1 i) N in
      RETURN (Propagated L' C # M, N', D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
         incr_propagation stats, fema, sema)
  })\<close>

definition propagate_lit_wl_pre where
  \<open>propagate_lit_wl_pre = (\<lambda>(((L, C), i), S).
     undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None \<and>
     C \<in># dom_m (get_clauses_wl S) \<and>
    1 - i < length (get_clauses_wl S \<propto> C) \<and>
    0 < length (get_clauses_wl S \<propto> C))\<close>


lemma propagate_lit_wl_heur_propagate_lit_wl:
  \<open>(uncurry3 propagate_lit_wl_heur, uncurry3 (RETURN oooo propagate_lit_wl)) \<in>
  [propagate_lit_wl_pre]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D>\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  supply [[show_types]]
  by (auto simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
      vmtf_consD twl_st_heur'_def propagate_lit_wl_pre_def swap_lits_pre_def
      valid_arena_swap_lits arena_lifting
      intro!: ASSERT_refine_left)

lemma undefined_lit_polarity_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow>
      polarity_st S L \<noteq> Some True \<and> polarity_st S L \<noteq> Some False\<close>
  by (auto simp: polarity_st_def polarity_def)

(* TODO deduplicate def *)
lemma find_unwatched_le_length:
  \<open>xj < length (get_clauses_wl S \<propto> fst (watched_by_app S L C))\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le>
       IsaSAT_Inner_Propagation.find_unwatched_wl_st S (fst (watched_by_app S L C))\<close>
  for S L C xj
  using that unfolding find_unwatched_wl_st_def IsaSAT_Inner_Propagation.find_unwatched_wl_st_def
    find_unwatched_l_def
  by (cases S) auto

lemma find_unwatched_in_D\<^sub>0: \<open>get_clauses_wl S \<propto> fst (watched_by_app S L C) ! xj \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> IsaSAT_Inner_Propagation.find_unwatched_wl_st S (fst (watched_by_app S L C))\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S j C L\<close> and
    dom: \<open>fst (watched_by_app S L C) \<in># dom_m (get_clauses_wl S)\<close>
  for S C xj L
proof -
  let ?C= \<open>fst (watched_by_app S L C)\<close>
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv dom by (blast intro: unit_prop_body_wl_D_invD)
  moreover {
    have xj: \<open>xj < length (get_clauses_wl S \<propto> ?C)\<close>
      using find_unw by (cases S) (auto simp: IsaSAT_Inner_Propagation.find_unwatched_wl_st_def
         find_unwatched_l_def)
    have \<open>?C > 0\<close>
      using inv dom by (blast intro: unit_prop_body_wl_D_invD)+
    then have \<open>get_clauses_wl S \<propto> ?C ! xj \<in>#
      all_lits_of_mm (mset `# ran_mf (get_clauses_wl S))\<close>
      using xj dom
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset
          in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def nth_in_set_tl
          intro!: bexI[of _ \<open>the (fmlookup (get_clauses_wl S)(?C))\<close>])
    then have \<open>get_clauses_wl S \<propto> ?C ! xj \<in>#
      all_lits_of_mm (mset `# ran_mf (get_clauses_wl S))\<close>
      unfolding mset_append
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset'
          all_lits_of_mm_union drop_Suc) }
  ultimately show ?thesis
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def literals_are_\<L>\<^sub>i\<^sub>n_def
    by (auto simp: all_lits_of_mm_union)
qed

definition (in isasat_input_ops) unit_prop_body_wl_heur_inv where
  \<open>unit_prop_body_wl_heur_inv S j w L \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_inv S' j w L)\<close>

definition (in isasat_input_ops) unit_prop_body_wl_D_find_unwatched_heur_inv where
  \<open>unit_prop_body_wl_D_find_unwatched_heur_inv f C S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_find_unwatched_inv f C S')\<close>

definition (in isasat_input_ops) keep_watch_heur where
  \<open>keep_watch_heur = (\<lambda>L i j (M, N,  D, Q, W, vm). do {
     ASSERT(nat_of_lit L < length W);
     ASSERT(i < length (W ! nat_of_lit L));
     ASSERT(j < length (W ! nat_of_lit L));
     RETURN (M, N, D, Q, W[nat_of_lit L := (W!(nat_of_lit L))[i := W ! (nat_of_lit L) ! j]], vm)
   })\<close>

definition (in isasat_input_ops) update_blit_wl_heur :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> nat \<times> twl_st_wl_heur) nres\<close> where
  \<open>update_blit_wl_heur = (\<lambda>(L::nat literal) C b j w K (M, N,  D, Q, W, vm). do {
     ASSERT(nat_of_lit L < length W);
     ASSERT(j < length (W ! nat_of_lit L));
     RETURN (j+1, w+1, (M, N, D, Q, W[nat_of_lit L := (W!nat_of_lit L)[j:=to_watcher C K b]], vm))
  })\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur_inv0 where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv0 L =
   (\<lambda>(j, w, S'). \<exists>S. (S', S) \<in> twl_st_heur \<and> unit_propagation_inner_loop_wl_loop_D_inv L (j, w, S))\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_body_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> nat \<times> twl_st_wl_heur) nres\<close>
   where
  \<open>unit_propagation_inner_loop_body_wl_heur L j w (S :: twl_st_wl_heur) = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_D_heur_inv0 L (j, w, S));
      ASSERT(watched_by_app_heur_pre ((S, L), w));
      let (C, K, b) = watcher_of (watched_by_app_heur S L w);
      S \<leftarrow> keep_watch_heur L j w S;
      ASSERT(unit_prop_body_wl_heur_inv S j w L);
      ASSERT(polarity_st_pre (S, K));
      let val_K = polarity_st_heur S K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        ASSERT(clause_not_marked_to_delete_heur_pre (S, C));
        if \<not>clause_not_marked_to_delete_heur S C
        then RETURN (j, w+1, S)
        else do {
          ASSERT(access_lit_in_clauses_heur_pre ((S, C), 0));
          let i = (if access_lit_in_clauses_heur S C 0 = L then 0 else 1);
          ASSERT(access_lit_in_clauses_heur_pre ((S, C), 1 - i));
          let L' = access_lit_in_clauses_heur S C (1 - i);
          ASSERT(polarity_st_pre (S, L'));
          let val_L' = polarity_st_heur S L';
          if val_L' = Some True
          then update_blit_wl_heur L C b j w L' S
          else do {
            ASSERT(find_unwatched_wl_st_heur_pre (S, C));
            f \<leftarrow> isa_find_unwatched_wl_st_heur S C;
            ASSERT (unit_prop_body_wl_D_find_unwatched_heur_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {
                  ASSERT(set_conflict_wl_heur_pre (C, S));
                  S \<leftarrow> set_conflict_wl_heur C S;
                  RETURN (j+1, w+1, S)}
                else do {
                  ASSERT(propagate_lit_wl_heur_pre (((L', C), i), S));
                  S \<leftarrow> propagate_lit_wl_heur L' C i S;
                  RETURN (j+1, w+1, S)}
              }
            | Some f \<Rightarrow> do {
                S \<leftarrow> isa_save_pos C f S;
                ASSERT(access_lit_in_clauses_heur_pre ((S, C), f));
                let K = access_lit_in_clauses_heur S C f;
                ASSERT(polarity_st_pre (S, K));
                let val_L' = polarity_st_heur S K;
                if val_L' = Some True
                then update_blit_wl_heur L C b j w K S
                else do {
                  ASSERT(update_clause_wl_code_pre (((((((L, C), b), j), w), i), f), S));
                  update_clause_wl_heur L C b j w i f S
                }
              }
          }
        }
      }
   }\<close>

lemma set_conflict_wl'_alt_def2:
  \<open>RETURN oo set_conflict_wl' =
    (\<lambda>C (M, N, D, NE, UE, Q, W). do {
      let D = Some (mset (N \<propto> C));
      RETURN (M, N, D, NE, UE, {#}, W) })
  \<close>
  unfolding set_conflict_wl'_def
  by (auto intro!: ext)

declare RETURN_as_SPEC_refine[refine2 del]

definition (in isasat_input_ops) set_conflict_wl'_pre where
  \<open>set_conflict_wl'_pre i S \<longleftrightarrow>
    get_conflict_wl S = None \<and> i \<in># dom_m (get_clauses_wl S) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf (get_clauses_wl S)) \<and>
    \<not> tautology (mset (get_clauses_wl S \<propto> i)) \<and>
    distinct (get_clauses_wl S \<propto> i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close>

lemma set_conflict_wl_heur_set_conflict_wl':
  \<open>(uncurry set_conflict_wl_heur, uncurry (RETURN oo set_conflict_wl')) \<in>
    [uncurry set_conflict_wl'_pre]\<^sub>f
    nat_rel \<times>\<^sub>r twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D>\<rangle>nres_rel\<close>
proof -
  have H:
    \<open>isa_set_lookup_conflict_aa x y z a b c d
        \<le> \<Down> (option_lookup_clause_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f (Id \<times>\<^sub>f Id)))
           (set_conflict_m x' y' z' a' b' c' d')\<close>
    if
      \<open>(((((((x, y), z), a), b), c), d), (((((x', y'), z'), a'), b'), c'), d')
      \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f {(arena, N). valid_arena arena N vdom} \<times>\<^sub>f
        nat_rel \<times>\<^sub>f
        option_lookup_clause_rel \<times>\<^sub>f
        nat_rel \<times>\<^sub>f
        Id \<times>\<^sub>f
        Id\<close> and
        \<open>z' \<in># dom_m y' \<and> a' = None \<and> distinct (y' \<propto> z') \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf y') \<and>
         \<not> tautology (mset (y' \<propto> z')) \<and> b' = 0 \<and> out_learned x' None d' \<and> no_dup x'\<close>
      for x x' y y' z z' a a' b b' c c' d d' vdom
    by (rule isa_set_lookup_conflict[THEN fref_to_Down_curry6,
      unfolded prod.case, OF that(2,1)])
  have [refine0]: \<open>isa_set_lookup_conflict_aa x1h x1i x1g x1j zero_uint32_nat x1q x1r
        \<le> \<Down> {((C, n, lbd, outl), D). (C, D) \<in> option_lookup_clause_rel \<and> n = card_max_lvl x1h (the D) \<and>
                out_learned x1h D outl}
          (RETURN (Some (mset (x1b \<propto> x1))))\<close>
    if
      \<open>(x, y) \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x2s = (x1t, x2t)\<close> and
      \<open>x2r = (x1s, x2s)\<close> and
      \<open>x2q = (x1r, x2r)\<close> and
      \<open>x2p = (x1q, x2q)\<close> and
      \<open>x2o = (x1p, x2p)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>x2m = (x1n, x2n)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>x2k = (x1l, x2l)\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x2i = (x1j, x2j)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x = (x1g, x2g)\<close> and
      \<open>case y of (x, xa) \<Rightarrow> set_conflict_wl'_pre x xa\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q
       x1r x2r x1s x2s x1t x2t
  proof -
    show ?thesis
      apply (rule order_trans)
      apply (rule H[of _ _ _ _ _ _ _ x1a x1b x1g x1c zero_uint32_nat x1q x1r \<open>set (get_vdom (snd x))\<close>])
      subgoal
        using that
        by (auto simp: twl_st_heur'_def twl_st_heur_def)
      subgoal
        using that
        by (auto simp: twl_st_heur'_def twl_st_heur_def set_conflict_wl'_pre_def)
      subgoal
        using that
        by (auto simp: RETURN_def conc_fun_RES set_conflict_m_def twl_st_heur'_def
          twl_st_heur_def)
      done
  qed
  have isa_set_lookup_conflict_aa_pre:
   \<open>curry6 isa_set_lookup_conflict_aa_pre x1h x1i x1g x1j zero_uint32_nat x1q x1r\<close>
    if
      \<open>case y of (x, xa) \<Rightarrow> set_conflict_wl'_pre x xa\<close> and
      \<open>(x, y) \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      \<open>x2e = (x1f, x2f)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x2c = (x1d, x2d)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x2a = (x1b, x2b)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x2s = (x1t, x2t)\<close> and
      \<open>x2r = (x1s, x2s)\<close> and
      \<open>x2q = (x1r, x2r)\<close> and
      \<open>x2p = (x1q, x2q)\<close> and
      \<open>x2o = (x1p, x2p)\<close> and
      \<open>x2n = (x1o, x2o)\<close> and
      \<open>x2m = (x1n, x2n)\<close> and
      \<open>x2l = (x1m, x2m)\<close> and
      \<open>x2k = (x1l, x2l)\<close> and
      \<open>x2j = (x1k, x2k)\<close> and
      \<open>x2i = (x1j, x2j)\<close> and
      \<open>x2h = (x1i, x2i)\<close> and
      \<open>x2g = (x1h, x2h)\<close> and
      \<open>x = (x1g, x2g)\<close>
    for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p x1q x2q
       x1r x2r x1s x2s x1t x2t
  proof -
    show ?thesis
     using that unfolding isa_set_lookup_conflict_aa_pre_def set_conflict_wl'_pre_def
     twl_st_heur'_def twl_st_heur_def
     by (auto simp: arena_lifting)
  qed

  show ?thesis
    apply (intro nres_relI frefI)
    unfolding uncurry_def RES_RETURN_RES4 set_conflict_wl'_alt_def2 set_conflict_wl_heur_def
    apply (rewrite at \<open>let _ = zero_uint32_nat in _\<close> Let_def)
    apply (refine_vcg)
    subgoal by (rule isa_set_lookup_conflict_aa_pre)
    apply assumption+
    subgoal by (auto simp: twl_st_heur'_def twl_st_heur_def counts_maximum_level_def)
    done
qed

lemma in_Id_in_Id_option_rel[refine]:
  \<open>(f, f') \<in> Id \<Longrightarrow> (f, f') \<in> \<langle>Id\<rangle> option_rel\<close>
  by auto

text \<open>The assumption that that accessed clause is active has not been checked at this point!\<close>
definition (in isasat_input_ops) keep_watch_heur_pre where
  \<open>keep_watch_heur_pre =
     (\<lambda>(((L, j), w), S). j < length (watched_by S L) \<and> w < length (watched_by S L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       literals_are_\<L>\<^sub>i\<^sub>n S)\<close>

lemma (in isasat_input_ops) keep_watch_heur_pre_alt_def:
  \<open>keep_watch_heur_pre (((L, j), w), S) \<longleftrightarrow>
    j < length (watched_by S L) \<and> w < length (watched_by S L) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
      literals_are_\<L>\<^sub>i\<^sub>n S \<and> fst (snd (watched_by S L ! w))  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?B
  then show ?A
    unfolding keep_watch_heur_pre_def by auto
next
  assume ?A
  then have
    j: \<open>j < length (watched_by S L)\<close> and
    w: \<open>w < length (watched_by S L)\<close> and
    L: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    unfolding keep_watch_heur_pre_def by auto
  have \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
    using lits unfolding literals_are_\<L>\<^sub>i\<^sub>n_def by fast
  then have \<open>fst (snd (watched_by S L ! w)) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    using w L nth_mem[OF w]
    unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
    by (cases \<open>watched_by S L ! w\<close>)
      (auto dest!: multi_member_split[of L] simp del: nth_mem)
  then show ?B
    using j w L lits
    unfolding keep_watch_heur_pre_def by auto
qed


lemma (in isasat_input_ops) vdom_m_update_subset':
  \<open>fst C \<in> vdom_m bh N \<Longrightarrow> vdom_m (bh(ap := bh ap[bf := C])) N \<subseteq> vdom_m bh N\<close>
  unfolding vdom_m_def
  by (fastforce split: if_splits elim!: in_set_upd_cases)

lemma (in isasat_input_ops) vdom_m_update_subset:
  \<open>bg < length (bh ap) \<Longrightarrow> vdom_m (bh(ap := bh ap[bf := bh ap ! bg])) N \<subseteq> vdom_m bh N\<close>
  unfolding vdom_m_def
  by (fastforce split: if_splits elim!: in_set_upd_cases)



lemma (in isasat_input_ops) keep_watch_heur_keep_watch:
  \<open>(uncurry3 keep_watch_heur, uncurry3 (RETURN oooo keep_watch)) \<in>
      [keep_watch_heur_pre]\<^sub>f
       Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D>\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto 4 5 simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_alt_def
      twl_st_heur_def map_fun_rel_def
      dest: vdom_m_update_subset)

text \<open>This is a slightly stronger version that the previous lemma:\<close>
lemma (in isasat_input_ops) keep_watch_heur_keep_watch':
  \<open>keep_watch_heur_pre (((L, j), w), S) \<Longrightarrow>
    ((((L', j'), w'), S'), ((L, j), w), S)
       \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<Longrightarrow>
  keep_watch_heur L' j' w' S' \<le> \<Down> {(T, T'). get_vdom T = get_vdom S' \<and> (T, T') \<in> twl_st_heur' \<D>}
     (RETURN (keep_watch L j w S))\<close>
  by (force simp: keep_watch_heur_def keep_watch_def twl_st_heur'_def keep_watch_heur_pre_alt_def
    twl_st_heur_def map_fun_rel_def dest: vdom_m_update_subset)

definition (in isasat_input_ops) update_blit_wl_heur_pre where
  \<open>update_blit_wl_heur_pre = (\<lambda>((((((L, C), b), j), w), K), S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> w < length (watched_by S L)
     \<and> j < length (watched_by S L) \<and> C \<in> vdom_m (get_watched_wl S) (get_clauses_wl S))\<close>

 lemma (in isasat_input_ops) update_blit_wl_heur_update_blit_wl:
  \<open>(uncurry6 update_blit_wl_heur, uncurry6 update_blit_wl) \<in>
      [update_blit_wl_heur_pre]\<^sub>f
       nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>
       \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI) \<comment> \<open>TODO proof\<close>
  apply (auto simp: update_blit_wl_heur_def update_blit_wl_def twl_st_heur'_def keep_watch_heur_pre_alt_def
       twl_st_heur_def map_fun_rel_def update_blit_wl_heur_pre_def
      simp: vdom_m_update_subset)
  subgoal for aa ab ac ad bd ae af ag ah ai aj be bf ak al am ao av aw bl bi bj bk  ay az
       bp x
    apply (subgoal_tac \<open>vdom_m (az(av := az av[bi := (aw, bk, bl)])) ay \<subseteq> vdom_m az ay\<close>)
    apply fast
    apply (rule vdom_m_update_subset')
    apply auto
    done
  subgoal for aa ab ac ad bd ae af ag ah ai aj be bf ak al am ao av aw bi bj bk bl bm ay az
       bp x
    apply (subgoal_tac \<open>vdom_m (bp(aw := bp aw[bk := (bi, bm, bj)])) ay \<subseteq> vdom_m bp ay\<close>)
    apply fast
    apply (rule vdom_m_update_subset')
    apply auto
    done
  done

lemma (in isasat_input_ops) unit_propagation_inner_loop_body_wl_D_alt_def:
  \<open>unit_propagation_inner_loop_body_wl_D L j w S = do {
      ASSERT(unit_propagation_inner_loop_wl_loop_D_pre L (j, w, S));
      let (C, K, b) = (watched_by S L) ! w;
      let S = keep_watch L j w S;
      ASSERT(unit_prop_body_wl_D_inv S j w L);
      let val_K = polarity (get_trail_wl S) K;
      if val_K = Some True
      then RETURN (j+1, w+1, S)
      else do { \<comment>\<open>Now the costly operations:\<close>
        if C \<notin># dom_m (get_clauses_wl S)
        then RETURN (j, w+1, S)
        else do {
          let i = (if ((get_clauses_wl S)\<propto>C) ! 0 = L then 0 else 1);
          let L' = ((get_clauses_wl S)\<propto>C) ! (1 - i);
          let val_L' = polarity (get_trail_wl S) L';
          if val_L' = Some True
          then update_blit_wl L C b j w L' S
          else do {
            f \<leftarrow> find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto> C);
            ASSERT (unit_prop_body_wl_D_find_unwatched_inv f C S);
            case f of
              None \<Rightarrow> do {
                if val_L' = Some False
                then do {
                  let S = set_conflict_wl (get_clauses_wl S \<propto> C) S;
                  RETURN (j+1, w+1, S)
                }
                else do {
                  S \<leftarrow> RETURN (propagate_lit_wl L' C i S);
                  RETURN (j+1, w+1, S)
                }
              }
            | Some f \<Rightarrow> do {
                S \<leftarrow> RETURN S;
                let K = get_clauses_wl S \<propto> C ! f;
                let val_L' = polarity (get_trail_wl S) K;
                if val_L' = Some True
                then update_blit_wl L C b j w K S
                else update_clause_wl L C b j w i f S
              }
          }
        }
      }
   }\<close>
  unfolding unit_propagation_inner_loop_body_wl_D_def let_to_bind_conv[symmetric] Let_def
  by auto

lemma (in isasat_input_ops) in_vdom_m_upd:
  \<open>x1f \<in> vdom_m (g(x1e := g x1e[x2 := (x1f, x2f)])) b\<close>
  if \<open>x2 < length (g x1e)\<close> and \<open>x1e \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for x1f x1e x2 g b x2f
  using that
  unfolding vdom_m_def
  by (auto dest!: multi_member_split intro!: set_update_memI img_fst)


text \<open>The lemmas below are used in the refinement proof of \<^term>\<open>unit_propagation_inner_loop_body_wl_D\<close>.
None of them makes sense in any other context. However having like below allows to share
intermediate steps in a much easier fashion that in an Isar proof.\<close>
context
  fixes x y x1a L x2 x2a x1 S x1c x2d L' x1d x2c T \<D>
  assumes
    xy: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
    pre: \<open>unit_propagation_inner_loop_wl_loop_D_pre L (x2, x2a, T)\<close> and
    pre_inv0: \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv0 L' (x2c, x2d, S)\<close> and
    st:
      \<open>x1a = (L, x2)\<close>
      \<open>x1 = (x1a, x2a)\<close>
      \<open>y = (x1, T)\<close>
      \<open>x1d = (L', x2c)\<close>
      \<open>x1c = (x1d, x2d)\<close>
      \<open>x = (x1c, S)\<close>
begin

private lemma state_simp_ST:
  \<open>x1a = (L, x2)\<close>
  \<open>x1 = ((L, x2), x2a)\<close>
  \<open>y = (((L, x2), x2a), T)\<close>
  \<open>x1d = (L, x2)\<close>
  \<open>x1c = ((L, x2), x2a)\<close>
  \<open>x = (((L, x2), x2a), S)\<close>
  \<open>L' = L\<close>
  \<open>x2c = x2\<close>
  \<open>x2d = x2a\<close> and
  st: \<open>(S, T) \<in> twl_st_heur\<close>
  using xy st unfolding twl_st_heur'_def by auto

private lemma
  x1b: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>  and
  x2b: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and
  loop_inv_T: \<open>unit_propagation_inner_loop_wl_loop_inv L (x2, x2a, T)\<close>
  using pre unfolding unit_propagation_inner_loop_wl_loop_D_pre_def
    unit_propagation_inner_loop_wl_loop_D_inv_def prod.simps image_image
  by simp_all

private lemma x2d_le: \<open>x2d < length (watched_by_int S L)\<close> and
  x1e_le: \<open>nat_of_lit L < length (get_watched_wl_heur S)\<close> and
  x2_x2a: \<open>x2 \<le> x2a\<close> and
  x2a_le: \<open>x2a < length (watched_by T L)\<close> and
  valid: \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
  using pre pre_inv0 st
  unfolding watched_by_app_heur_pre_def prod.simps
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv0_def
    twl_st_heur'_def
    unit_propagation_inner_loop_wl_loop_D_pre_def twl_st_heur_def map_fun_rel_def
    unit_propagation_inner_loop_wl_loop_pre_def prod.simps
  by (auto simp: state_simp_ST x1b x2b)

lemma watched_by_app_heur_pre: \<open>watched_by_app_heur_pre ((S, L'), x2d)\<close>
  using pre pre_inv0 st x2d_le x1e_le
  unfolding watched_by_app_heur_pre_def prod.simps
  by (simp add: state_simp_ST)

lemma keep_watch_heur_pre: \<open>keep_watch_heur_pre (((L, x2), x2a), T)\<close>
  using x2_x2a x2a_le unfolding keep_watch_heur_pre_def
  by (auto simp: x1b x2b)


context \<comment> \<open>Now we copy the watch literals\<close>
  notes _[simp]= state_simp_ST x1b x2b
  fixes x1f x2f x1g x2g U x2e x2g' x2h x2f' x2f''
  assumes
    xf: \<open>watched_by T L ! x2a = (x1f, x2f')\<close> and
    xg: \<open>watched_by_int S L' ! x2d = (x1g, x2g')\<close> and
    x2g': \<open>x2g' = (x2g, x2h)\<close> and
    x2f': \<open>x2f' = (x2f, x2f'')\<close> and
    U: \<open>(U, keep_watch L x2 x2a T)
      \<in> {(T, T'). get_vdom T = get_vdom x2e \<and> (T, T') \<in> twl_st_heur' \<D>}\<close> and
    prop_inv: \<open>unit_prop_body_wl_D_inv (keep_watch L x2 x2a T) x2 x2a L\<close> and
    prop_heur_inv: \<open>unit_prop_body_wl_heur_inv U x2c x2d L'\<close>
begin

private lemma U': \<open>(U, keep_watch L x2 x2a T) \<in> twl_st_heur\<close>
  using U unfolding twl_st_heur'_def by auto

private lemma eq: \<open>watched_by T L = watched_by_int S L\<close> \<open>x1f = x1g\<close> \<open>x2f' = x2g'\<close> \<open>x2f = x2g\<close>
    \<open>x2f'' = x2h\<close>
  using xf xg st x2f' x2g' xf
  by (auto simp: twl_st_heur_state_simp_watched)

lemma xg_S: \<open>watched_by_int S L ! x2a = (x1g, x2g')\<close>
  using xg by auto

lemma xg_T: \<open>watched_by T L ! x2a = (x1g, x2g')\<close>
  using U eq xf xg by (cases T)
    (auto simp add: image_image
        twl_st_heur_state_simp_watched twl_st_heur'_def
         twl_st_heur_def keep_watch_def)

context
  notes _[simp]= eq xg_S xg_T x2g'
begin

lemma in_D0:
  shows \<open>polarity_st_pre (U, x2g)\<close>
  using unit_prop_body_wl_D_invD[OF prop_inv]
  unfolding find_unwatched_wl_st_heur_pre_def watched_by_app_def polarity_st_pre_def
  by (auto simp add: image_image
      twl_st_heur_state_simp_watched twl_st_heur'_def)


lemma polarity_eq:
  \<open>(polarity (get_trail_wl_heur U) x2g = Some True) \<longleftrightarrow>
    (polarity (get_trail_wl (keep_watch L x2 x2a T)) x2f = Some True)\<close>
  using U' by (auto simp add: twl_st_heur_state_simp
     simp del: keep_watch_st_wl)

lemma
  valid_UT:
    \<open>valid_arena (get_clauses_wl_heur U) (get_clauses_wl T) (set (get_vdom U))\<close> and
  vdom_m_UT:
    \<open>vdom_m (get_watched_wl (keep_watch L x2 x2a T)) (get_clauses_wl T) \<subseteq> set (get_vdom U)\<close>
  using U' apply (cases T; auto simp: twl_st_heur_def keep_watch_def; fail)
  using U' by (cases T; auto simp: twl_st_heur_def keep_watch_def)

private lemma x1g_vdom: \<open>x1f \<in> vdom_m (get_watched_wl (keep_watch L x2 x2a T))
    (get_clauses_wl (keep_watch L x2 x2a T))\<close>
  using in_vdom_m_upd[of x2 \<open>get_watched_wl T\<close> L x1g x2g'] x2_x2a x2a_le eq
  by (cases T)
    (auto simp: keep_watch_def simp del: eq)

lemma clause_not_marked_to_delete_heur_pre:
  \<open>clause_not_marked_to_delete_heur_pre (U, x1g)\<close>
  using x1g_vdom valid_UT vdom_m_UT
  unfolding clause_not_marked_to_delete_heur_pre_def prod.simps arena_is_valid_clause_vdom_def
  by auto

private lemma clause_not_marked_to_delete_pre:
  \<open>clause_not_marked_to_delete_pre (keep_watch L x2 x2a T, x1f)\<close>
  using x1g_vdom
  unfolding clause_not_marked_to_delete_pre_def prod.case by auto

lemma clause_not_marked_to_delete_heur_clause_not_marked_to_delete_iff:
  \<open>(\<not> clause_not_marked_to_delete_heur U x1g) \<longleftrightarrow>
      (\<not> clause_not_marked_to_delete (keep_watch L x2 x2a T) x1f)\<close>
  apply (subst Not_eq_iff)
  apply (rule clause_not_marked_to_delete_rel[THEN fref_to_Down_unRET_uncurry_Id])
  apply (rule clause_not_marked_to_delete_pre)
  using U by (auto simp: twl_st_heur'_def)

context  \<comment> \<open>Now we know that the clause has not been deleted\<close>
  assumes not_del: \<open>\<not> \<not> clause_not_marked_to_delete (keep_watch L x2 x2a T) x1f\<close>
begin

private lemma x1g:
  \<open>x1g \<in># dom_m (get_clauses_wl T)\<close>
  using not_del unfolding clause_not_marked_to_delete_def
  by auto

private lemma Tx1g_le2:
  \<open>length (get_clauses_wl T \<propto> x1g) \<ge> 2\<close>
  using arena_lifting[OF valid_UT, of x1g]
  by (auto simp: x1g)

lemma access_lit_in_clauses_heur_pre0:
  \<open>access_lit_in_clauses_heur_pre ((U, x1g), 0)\<close>
  unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
    arena_is_valid_clause_idx_and_access_def
  by (rule bex_leI[of _ x1g], rule exI[of _ \<open>get_clauses_wl T\<close>],
     rule exI[of _ \<open>set (get_vdom U)\<close>])
   (use valid_UT Tx1g_le2 x1g in auto)


private definition i :: nat where
  \<open>i = ((if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L then 0 else 1))\<close>

lemma i_alt_def_L':
  \<open>i = ((if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1))\<close>
  unfolding i_def by auto

lemma access_lit_in_clauses_heur_pre1i:
  \<open>access_lit_in_clauses_heur_pre ((U, x1g), 1 - ((if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1)))\<close>
  unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
    arena_is_valid_clause_idx_and_access_def i_def
  by (rule bex_leI[of _ x1g], rule exI[of _ \<open>get_clauses_wl T\<close>],
     rule exI[of _ \<open>set (get_vdom U)\<close>])
   (use valid_UT Tx1g_le2 x1g in auto)


lemma polarity_st_pre1i:
  \<open>polarity_st_pre (U, arena_lit (get_clauses_wl_heur U)
          (x1g + (1 - (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1))))\<close>
  unfolding polarity_st_pre_def prod.case
  using unit_prop_body_wl_D_invD[OF prop_inv] arena_lifting[OF valid_UT x1g]
  unfolding find_unwatched_wl_st_heur_pre_def watched_by_app_def polarity_st_pre_def
  by (auto simp add: x1g image_image
      twl_st_heur_state_simp_watched twl_st_heur'_def i_def
      split: if_splits)

private lemma
  access_x1g:
    \<open>arena_lit (get_clauses_wl_heur U) (x1g + 0) =
     get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0\<close> and
  access_x1g1i:
    \<open>arena_lit (get_clauses_wl_heur U) (x1g + (1 - i)) =
       get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! (1 - i)\<close> and
  i_alt_def:
    \<open>i = (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1)\<close>
  using arena_lifting[OF valid_UT x1g]
  unfolding i_def
  by auto

lemma polarity_other_watched_lit:
  \<open>(polarity (get_trail_wl_heur U) (arena_lit (get_clauses_wl_heur U) (x1g +
         (1 - (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1)))) =
     Some True) =
    (polarity (get_trail_wl (keep_watch L x2 x2a T)) (get_clauses_wl (keep_watch L x2 x2a T) \<propto>
       x1f ! (1 - (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1))) =
     Some True)\<close>
  using U'
  unfolding i_def[symmetric] i_alt_def[symmetric] i_alt_def_L'[symmetric]
  unfolding access_x1g access_x1g1i
  by (auto simp: twl_st_heur_state_simp)

lemma update_blit_wl_heur_pre:
  \<open>update_blit_wl_heur_pre ((((((L, x1f), x1f''), x2), x2a), get_clauses_wl (keep_watch L x2 x2a T) \<propto>
       x1f ! (1 - (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1))),
      keep_watch L x2 x2a T)\<close>
  using x2_x2a x2a_le x1g
  unfolding i_def[symmetric] i_alt_def[symmetric] update_blit_wl_heur_pre_def prod.simps
  by auto

lemma update_blit_wl_rel:
  \<open>(((((((L', x1g), x2h), x2c), x2d),
       arena_lit (get_clauses_wl_heur U)
        (x1g + (1 - (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L'
           then 0 else 1)))), U),
     (((((L, x1f), x2f''), x2), x2a),
      get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! (1 -
         (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L
        then 0 else 1))),
     keep_watch L x2 x2a T)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f
       nat_rel \<times>\<^sub>f
       nat_rel \<times>\<^sub>f
       nat_lit_lit_rel \<times>\<^sub>f
       twl_st_heur' \<D>\<close>
  using U
  unfolding i_def[symmetric] i_alt_def[symmetric] i_alt_def_L'[symmetric]
  unfolding access_x1g access_x1g1i
  by auto


lemma find_unwatched_wl_st_pre:
  \<open>find_unwatched_wl_st_pre (keep_watch L x2 x2a T, x1f)\<close>
  using x2_x2a x2a_le Tx1g_le2 unit_prop_body_wl_D_invD[OF prop_inv]
  unfolding find_unwatched_wl_st_pre_def prod.simps
  unfolding access_x1g access_x1g1i
  by (auto simp: xf xg x1g watched_by_app_def)

lemma find_unwatched_wl_st_heur_pre:
  \<open>find_unwatched_wl_st_heur_pre (U, x1g)\<close>
  unfolding find_unwatched_wl_st_heur_pre_def access_lit_in_clauses_heur_pre_def
  arena_is_valid_clause_idx_def arena_lit_pre_def prod.simps
  by (rule exI[of _ \<open>get_clauses_wl T\<close>],
     rule exI[of _ \<open>set (get_vdom U)\<close>])
   (use valid_UT Tx1g_le2 x1g in auto)

lemma isa_find_unwatched_wl_st_heur_pre:
    \<open>((U, x1g), keep_watch L x2 x2a T, x1f) \<in> twl_st_heur \<times>\<^sub>f nat_rel\<close> and
  isa_find_unwatched_wl_st_heur_lits:
    \<open>literals_are_\<L>\<^sub>i\<^sub>n (keep_watch L x2 x2a T)\<close>
  using U' x2_x2a x2a_le by auto


context \<comment> \<open>Now we try to find another literal to watch\<close>
  notes _ [simp] = x1g
  fixes f f'
  assumes ff: \<open>(f, f') \<in> Id\<close> and
    find_unw_pre: \<open>unit_prop_body_wl_D_find_unwatched_inv f' x1f (keep_watch L x2 x2a T)\<close>
begin

private lemma ff: \<open>f = f'\<close>
  using ff by auto

lemma unit_prop_body_wl_D_find_unwatched_heur_inv:
  \<open>unit_prop_body_wl_D_find_unwatched_heur_inv f x1g U\<close>
  using U' find_unw_pre
  unfolding
    unit_prop_body_wl_D_find_unwatched_heur_inv_def
  apply -
  by (rule exI[of _ \<open>keep_watch L x2 x2a T\<close>]) (auto simp: ff)

context \<comment> \<open>No replacement found\<close>
  notes _[simp] = ff
  assumes
    f: \<open>f = None\<close> and
    f'[simp]: \<open>f' = None\<close>
begin

lemma pol_other_lit_false:
  \<open>(polarity (get_trail_wl_heur U)
      (arena_lit (get_clauses_wl_heur U)
        (x1g +
         (1 -
          (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
           else 1)))) =
     Some False) =
    (polarity (get_trail_wl (keep_watch L x2 x2a T))
      (get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
       (1 -
        (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
         else 1))) =
     Some False)\<close>
  unfolding i_def[symmetric] i_alt_def[symmetric] i_alt_def_L'[symmetric]  access_x1g1i
  using U' by (auto simp: twl_st_heur_state_simp)


private lemma lits_in_trail:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl T)\<close> and
  no_dup_T: \<open>no_dup (get_trail_wl T)\<close>
proof -
  obtain x xa where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n T\<close> and
    \<open>(U, keep_watch L x2 x2a T) \<in> twl_st_heur\<close> and
    Tx: \<open>(T, x) \<in> state_wl_l (Some (L, x2a))\<close> and
    \<open>x2 \<le> x2a\<close> and
    \<open>correct_watching_except x2 x2a L T\<close> and
    \<open>x2a \<le> length (watched_by T L)\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l (Some L)\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    \<open>twl_stgy_invs xa\<close> and
    \<open>twl_list_invs x\<close> and
    clss: \<open>clauses_to_update xa \<noteq> {#} \<or> 0 < remaining_nondom_wl x2a L T \<longrightarrow>
                 get_conflict xa = None\<close>
    using x2b
    U' loop_inv_T unfolding unit_propagation_inner_loop_wl_loop_inv_def prod.simps
    unit_propagation_inner_loop_l_inv_def
    by metis
  from Tx struct xxa lits
  show \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl T)\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail)
  have \<open>no_dup (trail (state\<^sub>W_of xa))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast
  then show \<open>no_dup (get_trail_wl T)\<close>
    using Tx xxa by (auto simp: twl_st)
qed

private lemma confl_T: \<open>get_conflict_wl T = None\<close> and
  dist_Tx1g: \<open>distinct (get_clauses_wl T \<propto> x1g)\<close>
  using unit_prop_body_wl_D_invD[OF prop_inv]
  by (auto simp: eq watched_by_app_def)


lemma set_conflict_wl_heur_pre: \<open>set_conflict_wl_heur_pre (x1g, U)\<close>
  using lits_in_trail U' no_dup_T
  unfolding set_conflict_wl_heur_pre_def prod.simps
  by (auto simp: twl_st_heur_state_simp)

lemma i_alt_def2:
  \<open>i = (if access_lit_in_clauses (keep_watch L x2 x2a T) x1f 0 = L then 0
        else 1)\<close>
  using U' access_x1g access_x1g1i unfolding i_def
  by (auto simp: twl_st_heur_state_simp access_lit_in_clauses_def)

lemma x2da_eq: \<open>(x2d, x2a) \<in> nat_rel\<close>
  by auto

context
  assumes \<open>polarity (get_trail_wl_heur U)
     (arena_lit (get_clauses_wl_heur U)
       (x1g +
        (1 -
         (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
          else 1)))) =
    Some False\<close> and
    pol_false: \<open>polarity (get_trail_wl (keep_watch L x2 x2a T))
     (get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
      (1 -
       (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
        else 1))) =
    Some False\<close>
begin

lemma unc_set_conflict_wl'_pre: \<open>uncurry set_conflict_wl'_pre (x1f, keep_watch L x2 x2a T)\<close>
proof -
  have x2b': \<open>x1f = fst (watched_by_app (keep_watch L x2 x2a T) L x2a)\<close>
    using x2_x2a x2a_le
    by (auto simp: watched_by_app_def)
 have not_tauto: \<open>\<not> tautology (mset (get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f))\<close>
    apply (subst x2b')
    apply (rule find_unwatched_not_tauto[of _ _ _ x2])
    subgoal using find_unw_pre unfolding f' x2b' watched_by_app_def by auto
    subgoal using prop_inv .
    subgoal
      using pol_false
      unfolding x2b'[symmetric] i_def[symmetric] i_alt_def2[symmetric] i_alt_def[symmetric]
      polarity_st_def by blast
    subgoal unfolding watched_by_app_def[symmetric] x2b'[symmetric]
      by auto
    done
  have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm  (mset `# ran_mf (get_clauses_wl (keep_watch L x2 x2a T)))\<close>
    using x2b unfolding literals_are_\<L>\<^sub>i\<^sub>n_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (simp add: all_lits_of_mm_union)
  show ?thesis
    using not_tauto confl_T dist_Tx1g lits lits_in_trail
    unfolding set_conflict_wl'_pre_def uncurry_def prod.simps
    by auto
qed

lemma set_conflict_keep_watch_rel:
  \<open>((x1g, U), x1f, keep_watch L x2 x2a T) \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close>
  using U by auto

lemma set_conflict_keep_watch_rel2:
 \<open>(W, W') \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<Longrightarrow>
    ((x2c + 1, W), x2 + 1, W') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f twl_st_heur' \<D>)\<close>
  by auto

end

context
  assumes \<open>polarity (get_trail_wl_heur U)
     (arena_lit (get_clauses_wl_heur U)
       (x1g +
        (1 -
         (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
          else 1)))) \<noteq>
    Some False\<close> and
    pol_False: \<open>polarity (get_trail_wl (keep_watch L x2 x2a T))
     (get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
      (1 -
       (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
        else 1))) \<noteq>
    Some False\<close> and
  \<open>polarity (get_trail_wl_heur U)
     (arena_lit (get_clauses_wl_heur U)
       (x1g +
        (1 -
         (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
          else 1)))) \<noteq>
    Some True\<close> and
  pol_True: \<open>polarity (get_trail_wl (keep_watch L x2 x2a T))
     (get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
      (1 -
       (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
        else 1))) \<noteq>
    Some True\<close>
begin

private lemma undef_lit1i:
  \<open>undefined_lit (get_trail_wl T) (get_clauses_wl T \<propto> x1g ! (Suc 0 - i))\<close>
   \<open>undefined_lit (get_trail_wl_heur U) (get_clauses_wl T \<propto> x1g ! (1 - i))\<close>
  using pol_True pol_False U'
  unfolding i_def[symmetric] i_alt_def_L'[symmetric]
    i_alt_def[symmetric] watched_by_app_def
  by (auto simp: polarity_def twl_st_heur_state_simp split: if_splits)

lemma propagate_lit_wl_heur_pre:
  \<open>propagate_lit_wl_heur_pre
    (((arena_lit (get_clauses_wl_heur U)
        (x1g +
        (1 -
          (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
          else 1))),
      x1g),
      if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else (1:: nat)),
    U)\<close> (is ?A)
proof -
  have \<open>i = 0 \<or> i = 1\<close>
    unfolding i_def by auto
  moreover have \<open>x1g \<noteq> DECISION_REASON\<close>
    using arena_lifting(1)[OF valid x1g]
    by (auto simp: header_size_def DECISION_REASON_def split: if_splits)
  ultimately show ?A
    using unit_prop_body_wl_D_invD[OF prop_inv] undef_lit1i
    unfolding propagate_lit_wl_heur_pre_def prod.simps i_def[symmetric] i_alt_def_L'[symmetric]
      i_alt_def[symmetric] watched_by_app_def
    unfolding access_x1g1i access_x1g
    by (auto simp: image_image)
qed

lemma propagate_lit_wl_pre: \<open>propagate_lit_wl_pre
     (((get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
        (1 -
         (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
          else 1)),
        x1f),
       if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1),
      keep_watch L x2 x2a T)\<close>
  using unit_prop_body_wl_D_invD[OF prop_inv] undef_lit1i
  unfolding propagate_lit_wl_pre_def prod.simps i_def[symmetric] i_alt_def_L'[symmetric]
    i_alt_def[symmetric] watched_by_app_def
  unfolding access_x1g1i access_x1g
  by (auto simp: image_image twl_st_heur_state_simp)

lemma propagate_lit_wl_rel:
  \<open>((((arena_lit (get_clauses_wl_heur U)
         (x1g +
          (1 -
           (if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0
            else 1))),
        x1g),
       if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1),
      U),
     ((get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f !
       (1 -
        (if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0
         else 1)),
       x1f),
      if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1),
     keep_watch L x2 x2a T)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close>
  using unit_prop_body_wl_D_invD[OF prop_inv] undef_lit1i U
  unfolding propagate_lit_wl_pre_def prod.simps i_def[symmetric] i_alt_def_L'[symmetric]
    i_alt_def[symmetric] watched_by_app_def
  unfolding access_x1g1i access_x1g
  by (auto simp: image_image twl_st_heur_state_simp)


end

end

context \<comment> \<open>No replacement found\<close>
  fixes i j
  assumes
    f: \<open>f = Some i\<close> and
    f'[simp]: \<open>f' = Some j\<close>
begin

private lemma ij: \<open>i = j\<close>
  using ff unfolding f f' by auto

private lemma
    \<open>unit_prop_body_wl_find_unwatched_inv (Some j) x1g
      (keep_watch L x2 x2a T)\<close> and
    j_ge2: \<open>2 \<le> j\<close> and
    j_le: \<open>j < length (get_clauses_wl T \<propto> x1g)\<close> and
    \<open>get_clauses_wl T \<propto> x1g ! j \<noteq> get_clauses_wl T \<propto> x1g ! 0\<close> and
    \<open>get_clauses_wl T \<propto> x1g ! j \<noteq> get_clauses_wl T \<propto> x1g ! Suc 0\<close>
  using find_unw_pre unfolding unit_prop_body_wl_D_find_unwatched_inv_def f'
  by auto

private lemma isa_update_pos_pre:
  \<open>5 < arena_length (get_clauses_wl_heur U) x1g \<Longrightarrow> isa_update_pos_pre ((x1g, j), get_clauses_wl_heur U)\<close>
  using j_ge2 valid_UT j_le
  unfolding isa_update_pos_pre_def access_lit_in_clauses_heur_pre_def
    arena_lit_pre_def arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def
  by (auto simp: arena_lifting)

private abbreviation isa_save_pos_rel where
  \<open>isa_save_pos_rel \<equiv> {(V, V'). get_vdom V = get_vdom x2e \<and> (V, V') \<in> twl_st_heur' \<D> \<and>
        V' = keep_watch L x2 x2a T \<and> get_trail_wl_heur V = get_trail_wl_heur U \<and>
        get_vdom V = get_vdom U \<and> get_watched_wl_heur V = get_watched_wl_heur U} \<close>

lemma isa_save_pos:
  \<open>isa_save_pos x1g i U \<le> \<Down> isa_save_pos_rel
      (RETURN (keep_watch L x2 x2a T))\<close>
    using j_ge2 isa_update_pos_pre U x1g j_le
    by (cases U; cases T)
      (auto simp: isa_save_pos_def twl_st_heur_def keep_watch_def twl_st_heur'_def
      arena_update_pos_alt_def arena_lifting ij arena_is_valid_clause_idx_def
      intro!: ASSERT_leI valid_arena_update_pos)

context
  notes _[simp] = ij
  fixes V V'
  assumes VV': \<open>(V, V') \<in> isa_save_pos_rel\<close>
begin

private lemma
    \<open>get_vdom U = get_vdom x2e\<close> and
    V_T_rel: \<open>(V, keep_watch L x2 x2a T) \<in> twl_st_heur' \<D>\<close> and
    valid_VT: \<open>valid_arena (get_clauses_wl_heur V) (get_clauses_wl T) (set (get_vdom U))\<close> and
    VV':
      \<open>V' = keep_watch L x2 x2a T\<close>
      \<open>get_trail_wl_heur V = get_trail_wl_heur U\<close>
      \<open>get_vdom V = get_vdom x2e\<close>
      \<open>get_watched_wl_heur V = get_watched_wl_heur U\<close>
  using VV'
  apply (auto simp: twl_st_heur'_def twl_st_heur_def keep_watch_def)
  apply (cases T; auto; fail)+
  done

lemma access_lit_in_clauses_heur_pre3: \<open>access_lit_in_clauses_heur_pre ((V, x1g), i)\<close>
  unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
     arena_is_valid_clause_idx_and_access_def
  by (rule bex_leI[of _ x1g], rule exI[of _ \<open>get_clauses_wl V'\<close>],
     rule exI[of _ \<open>set (get_vdom U)\<close>])
    (use valid_VT j_le in \<open>auto simp: VV'\<close>)


private lemma arena_lit_x1g_j:
  \<open>arena_lit (get_clauses_wl_heur V) (x1g + j) = get_clauses_wl T \<propto> x1g ! j\<close>
  using arena_lifting[OF valid_VT, of x1g] j_le
  by auto

lemma polarity_st_pre_unwatched: \<open>polarity_st_pre (V, arena_lit (get_clauses_wl_heur V) (x1g + i))\<close>
  unfolding polarity_st_pre_def arena_lit_x1g_j
  by (simp add: image_iff j_le literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l literals_are_in_\<L>\<^sub>i\<^sub>n_nth
    arena_lit_x1g_j)

lemma polarity_eq_unwatched: \<open>(polarity (get_trail_wl_heur V)
      (arena_lit (get_clauses_wl_heur V) (x1g + i)) =
     Some True) =
    (polarity (get_trail_wl V')
      (get_clauses_wl V' \<propto> x1f ! j) =
     Some True)\<close>
  using U' unfolding arena_lit_x1g_j
  by (auto simp: twl_st_heur_state_simp VV' arena_lit_x1g_j)

context
  notes _[simp] =  VV' arena_lit_x1g_j
  assumes \<open>polarity (get_trail_wl V') (get_clauses_wl V' \<propto> x1f ! j) = Some True\<close>
begin

lemma update_blit_wl_heur_pre_unw: \<open>update_blit_wl_heur_pre
     ((((((L, x1f), x1f''), x2), x2a), get_clauses_wl V' \<propto> x1f ! j), V')\<close>
  using x2_x2a x2a_le
  unfolding update_blit_wl_heur_pre_def
  by auto

lemma update_blit_unw_rel:
   \<open>(((((((L', x1g), x2h), x2c), x2d), arena_lit (get_clauses_wl_heur V) (x1g + i)),
      V),
     (((((L, x1f), x2f''), x2), x2a), get_clauses_wl V' \<propto> x1f ! j), V')
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
      nat_lit_lit_rel \<times>\<^sub>f
      twl_st_heur' \<D>\<close>
  using U V_T_rel by auto

end


context
  notes _ [simp] =  VV'
  assumes \<open>polarity (get_trail_wl V') (get_clauses_wl V' \<propto> x1f ! j) \<noteq> Some True\<close>
begin

private lemma arena_is_valid_clause_idx_and_access_x1g_j:
 \<open>arena_is_valid_clause_idx_and_access (get_clauses_wl_heur V) x1g j\<close>
  unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
     arena_is_valid_clause_idx_and_access_def
  by (rule exI[of _ \<open>get_clauses_wl T\<close>],
     rule exI[of _ \<open>set (get_vdom U)\<close>])
    (use valid_VT j_le in auto)

private lemma j_Lall: \<open>get_clauses_wl V' \<propto> x1g ! j \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  by (simp add: image_iff j_le literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l literals_are_in_\<L>\<^sub>i\<^sub>n_nth)

private lemma L_le:
  \<open>nat_of_lit L < length (get_watched_wl_heur V)\<close>
  \<open>nat_of_lit (get_clauses_wl V' \<propto> x1g ! j) < length (get_watched_wl_heur V)\<close>
  using U' j_Lall
  by (cases T; cases U; auto simp: twl_st_heur_def keep_watch_def map_fun_rel_def; fail)+

private lemma length_get_watched_wl_heur_U_T:
  \<open>length (get_watched_wl_heur U ! nat_of_lit L) = length (get_watched_wl T L)\<close>
  using U' j_Lall
  by (cases T; cases U; auto simp: twl_st_heur_def keep_watch_def map_fun_rel_def; fail)+

private lemma length_get_watched_wl_heur_S_T:
  \<open>length (watched_by_int S L) = length (get_watched_wl T L)\<close>
  using st j_Lall
  by (cases T; auto simp: twl_st_heur_def keep_watch_def map_fun_rel_def; fail)+

lemma update_clause_wl_code_pre_unw: \<open>update_clause_wl_code_pre
     (((((((L', x1g), x2h), x2c), x2d),
        if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1),
       i),
      V)\<close>
  using x2a_le x2_x2a arena_is_valid_clause_idx_and_access_x1g_j x1e_le U' x1b L_le
  length_get_watched_wl_heur_U_T length_get_watched_wl_heur_S_T valid_VT j_le
  unfolding update_clause_wl_code_pre_def
  by (auto simp: arena_lifting)

lemma update_clause_wl_pre_unw: \<open>update_clause_wl_pre
     (((((((L, x1f), x1f''), x2), x2a),
        if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1),
       j),
      V')\<close>
  using Tx1g_le2 j_le
  unfolding update_clause_wl_pre_def
  by auto

lemma update_watched_unw_rel:
  \<open>((((((((L', x1g), x2h), x2c), x2d),
        if arena_lit (get_clauses_wl_heur U) (x1g + 0) = L' then 0 else 1),
       i),
      V),
     ((((((L, x1f), x2f''), x2), x2a),
       if get_clauses_wl (keep_watch L x2 x2a T) \<propto> x1f ! 0 = L then 0 else 1),
      j),
     V')
    \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close>
  using U V_T_rel unfolding access_x1g1i access_x1g by auto

end

end

end

end

end

end

end

end

lemma unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry3 unit_propagation_inner_loop_body_wl_heur,
    uncurry3 unit_propagation_inner_loop_body_wl_D)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f
     \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>unit_prop_body_wl_D_inv T i C L \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for T i L C
    unfolding unit_prop_body_wl_D_inv_def image_image by auto
  have pol_undef: \<open>polarity M L \<noteq> Some True \<Longrightarrow> polarity M L \<noteq> Some False \<Longrightarrow> defined_lit M L \<Longrightarrow>
     False\<close>
    for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (auto simp: polarity_def split: if_splits)
  have 1: \<open>RETURN (w + 1, f S') = do {S \<leftarrow> RETURN (f S'); RETURN (w + 1, S)}\<close>
    for w :: nat and S' and f
    by auto
  have keep_watch_skip: \<open>((x2d + 1, U), x2a + 1, keep_watch L x2 x2a T)
      \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close>
    if \<open>(x2d + 1, x2a + 1) \<in> nat_rel\<close> and
      \<open>(U, keep_watch L x2 x2a T) \<in>  twl_st_heur' \<D>\<close>
    for x2d U x2a x2 L T
    using that
    by auto

  have isa_find_unwatched_wl_st_heur_find_unwatched_wl_st:
     \<open>isa_find_unwatched_wl_st_heur x' y'
        \<le> \<Down> Id (IsaSAT_Inner_Propagation.find_unwatched_wl_st x y)\<close>
    if
      find_unw: \<open>find_unwatched_wl_st_pre (x, y)\<close> and
      xy: \<open>((x', y'), x, y) \<in> twl_st_heur \<times>\<^sub>f nat_rel\<close> and
      lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x\<close>
      for x y x' y'
  proof -
    have n_d: \<open>no_dup (get_trail_wl x)\<close>
      using xy unfolding twl_st_heur_def
      by auto
    have lits_xy: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl x \<propto> y))\<close>
      apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth)
      subgoal
        using find_unw unfolding find_unwatched_wl_st_pre_def prod.simps
        by auto
      subgoal using lits .
      done

    have K: \<open>local.find_unwatched_wl_st x y \<le> IsaSAT_Inner_Propagation.find_unwatched_wl_st x y\<close>
      unfolding local.find_unwatched_wl_st_def IsaSAT_Inner_Propagation.find_unwatched_wl_st_def
      apply (cases x)
      apply clarify
      apply (rule order_trans)
      apply (rule find_unwatched)
      subgoal
        using n_d by simp
      subgoal
        using find_unw unfolding find_unwatched_wl_st_pre_def prod.simps
        by auto
      subgoal
        using lits_xy by simp
      subgoal by auto
      done
    show ?thesis
      apply (rule order_trans)
        apply (rule find_unwatched_wl_st_heur_find_unwatched_wl_s[THEN fref_to_Down_curry,
          OF that(1,2)])
      by (simp add: K)
  qed

  have set_conflict_wl'_rel:
   \<open>(V, set_conflict_wl' x1f (keep_watch L x2 x2a T)) \<in> twl_st_heur' \<D> \<Longrightarrow>
     (x2d, x2a) \<in> nat_rel \<Longrightarrow>
    ((x2d + 1, V), x2a + 1, set_conflict_wl' x1f (keep_watch L x2 x2a T))
    \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close>
    for V x1f L x2 x2a T x2d
    by auto

  have propagate_lit_wl_heur_final_rel: \<open>(Sa, Sb) \<in> twl_st_heur' \<D> \<Longrightarrow>  (x2d, x2a) \<in> nat_rel \<Longrightarrow>
    ((x2d + 1, Sa), x2a + 1, Sb) \<in> nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<close>
    for V x1f L x2 x2a T x2d U x1g L' Sa Sb
    by auto

  note find_unw = find_unwatched_wl_st_heur_find_unwatched_wl_s[THEN fref_to_Down_curry]
      set_conflict_wl_heur_set_conflict_wl'[of \<D>, THEN fref_to_Down_curry, unfolded comp_def]
      propagate_lit_wl_heur_propagate_lit_wl[of \<D>, THEN fref_to_Down_curry3, unfolded comp_def]
      update_clause_wl_heur_update_clause_wl[of \<D>, THEN fref_to_Down_curry7]
      keep_watch_heur_keep_watch'[of _ _ _ _ _ _ _ _ \<D>]
      update_blit_wl_heur_update_blit_wl[of \<D>, THEN fref_to_Down_curry6]
      clause_not_marked_to_delete_rel[THEN fref_to_Down_curry]
      keep_watch_skip
      isa_find_unwatched_wl_st_heur_find_unwatched_wl_st
      set_conflict_wl'_rel propagate_lit_wl_heur_final_rel
      (*  update_conflict_twl_st_heur2 propagate_lit_wl_heur_step *)
  thm set_conflict_wl_heur_set_conflict_wl'[of \<D>, THEN fref_to_Down_curry]
      propagate_lit_wl_heur_propagate_lit_wl[of \<D>, THEN fref_to_Down_curry3]
  show ?thesis
    supply [[goals_limit=1]] twl_st_heur'_def[simp]
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (intro frefI nres_relI)
    unfolding unit_propagation_inner_loop_body_wl_heur_def
      unit_propagation_inner_loop_body_wl_D_alt_def
      uncurry_def find_unwatched_l_find_unwatched_wl_s 1 polarity_st_heur_def
      watched_by_app_heur_def access_lit_in_clauses_heur_def
    unfolding set_conflict_wl'_alt_def[symmetric]
      clause_not_marked_to_delete_def[symmetric]
      to_watcher_def watcher_of_def id_def

    apply (refine_rcg find_unw isa_save_pos)
    subgoal unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv0_def twl_st_heur'_def
      unit_propagation_inner_loop_wl_loop_D_pre_def
      by fastforce
    subgoal for x y x1 x1a x1b x2 x2a x2b x1c x1d x1e x2c x2d x2e
      by (rule watched_by_app_heur_pre)
    subgoal by (rule keep_watch_heur_pre)
    subgoal by (auto simp del: keep_watch_st_wl simp: twl_st_heur_state_simp)
    subgoal unfolding unit_prop_body_wl_heur_inv_def by fastforce
    subgoal
      by (rule in_D0)
    subgoal
      by (rule polarity_eq)
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by simp
    subgoal
      by (rule clause_not_marked_to_delete_heur_pre)
    subgoal
      by (rule clause_not_marked_to_delete_heur_clause_not_marked_to_delete_iff)
    subgoal by auto
    subgoal
      by (rule access_lit_in_clauses_heur_pre0)
    subgoal
      by (rule access_lit_in_clauses_heur_pre1i)
    subgoal
      by (rule polarity_st_pre1i)
    subgoal
      by (rule polarity_other_watched_lit)
    subgoal
      by (rule update_blit_wl_heur_pre)
    subgoal
      by (rule update_blit_wl_rel)
    subgoal
      by (rule find_unwatched_wl_st_heur_pre)
    subgoal
      by (rule find_unwatched_wl_st_pre)
    subgoal
      by (rule isa_find_unwatched_wl_st_heur_pre)
    subgoal
      by (rule isa_find_unwatched_wl_st_heur_lits)
    subgoal
      by (rule unit_prop_body_wl_D_find_unwatched_heur_inv)
    subgoal
      by (rule pol_other_lit_false)
    subgoal
      by (rule set_conflict_wl_heur_pre)
    subgoal
      by (rule unc_set_conflict_wl'_pre)
    subgoal
      by (rule set_conflict_keep_watch_rel)
    subgoal
      by (rule x2da_eq)
    subgoal
      by (rule set_conflict_keep_watch_rel2)
    subgoal by (rule propagate_lit_wl_heur_pre)
    subgoal by (rule propagate_lit_wl_pre)
    subgoal by (rule propagate_lit_wl_rel)
    subgoal
      by (rule x2da_eq)
    subgoal
      by force
    apply assumption+
    subgoal by (rule access_lit_in_clauses_heur_pre3)
    subgoal
      by (rule polarity_st_pre_unwatched)
    subgoal
      by (rule polarity_eq_unwatched)
    subgoal
      by (rule update_blit_wl_heur_pre_unw)
    subgoal
      by (rule update_blit_unw_rel)
    subgoal
      by (rule update_clause_wl_code_pre_unw)
    subgoal
      by (rule update_clause_wl_pre_unw)
    subgoal
      by (rule update_watched_unw_rel)
    done
qed


definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur_inv where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L =
   (\<lambda>(j, w, S'). \<exists>S\<^sub>0' S. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (S', S) \<in> twl_st_heur \<and> unit_propagation_inner_loop_wl_loop_D_inv L (j, w, S) \<and>
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> dom_m (get_clauses_wl S) = dom_m (get_clauses_wl S\<^sub>0'))\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(j, w, S). w < length (watched_by_int S L) \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_heur L j w S
      })
      (0, 0, S\<^sub>0)
  }\<close>


lemma unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D:
  \<open>(uncurry unit_propagation_inner_loop_wl_loop_D_heur,
       uncurry unit_propagation_inner_loop_wl_loop_D)
   \<in> Id \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<rangle>nres_rel\<close>
proof -
  have unit_propagation_inner_loop_wl_loop_D_heur_inv:
    \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv x2a x1a xa\<close>
    if
      \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<close> and
      H: \<open>unit_propagation_inner_loop_wl_loop_D_inv x1 x'\<close>
    for x y x1 x2 x1a x2a xa x'
  proof -
    obtain w S w' S' j j' where
      xa: \<open>xa = (j, w, S)\<close> and x': \<open>x' = (j', w', S')\<close>
      by (cases xa; cases x') auto
    show ?thesis
      unfolding xa unit_propagation_inner_loop_wl_loop_D_heur_inv_def prod.case
      apply (rule exI[of _ x2])
      apply (rule exI[of _ S'])
      using that xa x' that
      unfolding unit_propagation_inner_loop_wl_loop_D_inv_def twl_st_heur'_def
      by auto
  qed
  have cond_eq: \<open>(x1c < length (watched_by_int x2c x1a) \<and>
        get_conflict_wl_is_None_heur x2c) =
        (x1e < length (watched_by x2e x1) \<and> get_conflict_wl x2e = None)\<close>
    if
      \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f twl_st_heur' \<D>)\<close> and
      \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv x2a x1a xa\<close> and
      inv: \<open>unit_propagation_inner_loop_wl_loop_D_inv x1 x'\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>xa = (x1b, x2b)\<close> and
      \<open>x2d = (x1e, x2e)\<close> and
      \<open>x' = (x1d, x2d)\<close>
    for x y x1 x2 x1a x2a xa x' x1b x2b x1c x2c x1d x2d x1e x2e
  proof -

    have H:
      \<open>x1e < length (watched_by x2e x1) \<longleftrightarrow> x1c < length (watched_by_int x2c x1a)\<close>
      if \<open>(x2c, x2e) \<in> twl_st_heur' \<D>\<close> and
      \<open>(x1c, x1e) \<in> nat_rel\<close> and
      \<open>(x1, x1a) \<in> Id\<close> and
      \<open>x1a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      for x1e x2e x1 x1c x1a
      using that
      by (cases x2e)
        (auto simp add: twl_st_heur'_def twl_st_heur_def map_fun_rel_def
            dest!: multi_member_split)
    have \<open>get_conflict_wl_is_None_heur x2c \<longleftrightarrow> get_conflict_wl_is_None x2e\<close>
      apply (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None[THEN fref_to_Down_unRET_Id,
        of x2c x2e])
      subgoal by auto
      subgoal using that unfolding twl_st_heur'_def by auto
      subgoal by auto
      done
    moreover have \<open>x1e < length (watched_by x2e x1) \<longleftrightarrow> x1c < length (watched_by_int x2c x1a)\<close>
      apply (subst H[of _ x1e _ _ x1])
      subgoal using that by auto
      subgoal by auto
      subgoal by auto
      subgoal using that unfolding unit_propagation_inner_loop_wl_loop_D_inv_def
        by auto
      subgoal using that by auto
      done
    ultimately show ?thesis
      unfolding get_conflict_wl_is_None by blast
  qed

  note H[refine] = unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D
     [THEN fref_to_Down_curry3]
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_heur_def
      unit_propagation_inner_loop_wl_loop_D_def uncurry_def
      unit_propagation_inner_loop_wl_loop_D_inv_def[symmetric]
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal by auto
    subgoal by (rule unit_propagation_inner_loop_wl_loop_D_heur_inv)
    subgoal
     by (rule cond_eq)
    subgoal by auto
    done
qed


definition (in isasat_input_ops) cut_watch_list_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>cut_watch_list_heur j w L =(\<lambda>(M, N, D, Q, W, oth). do {
      ASSERT(j \<le> length (W!nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
         w \<le> length (W ! (nat_of_lit L)));
      RETURN (M, N, D, Q, W[nat_of_lit L := take j (W!(nat_of_lit L)) @ drop w (W!(nat_of_lit L))], oth)
    })\<close>


definition (in isasat_input_ops) cut_watch_list_heur2
 :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>cut_watch_list_heur2 = (\<lambda>j w L (M, N, D, Q, W, oth). do {
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
     w \<le> length (W ! (nat_of_lit L)));
  (j, w, W) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(j, w, W). j \<le> w \<and> nat_of_lit L < length W\<^esup>
    (\<lambda>(j, w, W). w < length (W!(nat_of_lit L)))
    (\<lambda>(j, w, W). do {
      ASSERT(w < length (W!(nat_of_lit L)));
      RETURN (j+1, w+1, W[nat_of_lit L := (W!(nat_of_lit L))[j := W!(nat_of_lit L)!w]])
    })
    (j, w, W);
  ASSERT(j \<le> length (W ! nat_of_lit L) \<and> nat_of_lit L < length W);
  let W = W[nat_of_lit L := take j (W ! nat_of_lit L)];
  RETURN (M, N, D, Q, W, oth)
})\<close>

lemma cut_watch_list_heur2_cut_watch_list_heur:
  shows
    \<open>cut_watch_list_heur2 j w L S \<le> \<Down> Id (cut_watch_list_heur j w L S)\<close>
proof -
  obtain M N D Q W oth where S: \<open>S = (M, N, D, Q, W, oth)\<close>
    by (cases S)
  let ?R = \<open>measure (\<lambda>(j'::nat, w' :: nat, _ :: (nat \<times> nat literal \<times> bool) list list). length (W!nat_of_lit L) - w')\<close>
  define I' where
    \<open>I' \<equiv> \<lambda>(j', w', W'). length (W' ! (nat_of_lit L)) = length (W ! (nat_of_lit L)) \<and> j' \<le> w' \<and> w' \<ge> w \<and>
        w' - w = j' - j \<and> j' \<ge> j \<and>
        drop w' (W' ! (nat_of_lit L)) = drop w' (W ! (nat_of_lit L)) \<and>
        w' \<le> length (W' ! (nat_of_lit L)) \<and>
        W'[nat_of_lit L := take (j + w' - w) (W' ! nat_of_lit L)] =
        W[nat_of_lit L := take (j + w' - w) ((take j (W!(nat_of_lit L)) @ drop w (W!(nat_of_lit L))))]\<close>

  have cut_watch_list_heur_alt_def:
  \<open>cut_watch_list_heur j w L =(\<lambda>(M, N, D, Q, W, oth). do {
      ASSERT(j \<le> length (W!nat_of_lit L) \<and> j \<le> w  \<and> nat_of_lit L < length W \<and>
         w \<le> length (W ! (nat_of_lit L)));
      let W = W[nat_of_lit L := take j (W!(nat_of_lit L)) @ drop w (W!(nat_of_lit L))];
      RETURN (M, N, D, Q, W, oth)
    })\<close>
    unfolding cut_watch_list_heur_def by auto
  have REC: \<open>ASSERT (x1k < length (x2k ! nat_of_lit L)) \<bind>
      (\<lambda>_. RETURN (x1j + 1, x1k + 1, x2k [nat_of_lit L := (x2k ! nat_of_lit L) [x1j :=
                    x2k ! nat_of_lit L !
                    x1k]]))
      \<le> SPEC (\<lambda>s'. \<forall>x1 x2 x1a x2a. x2 = (x1a, x2a) \<longrightarrow> s' = (x1, x2) \<longrightarrow>
          (x1 \<le> x1a \<and> nat_of_lit L < length x2a) \<and> I' s' \<and>
          (s', s) \<in> measure (\<lambda>(j', w', _). length (W ! nat_of_lit L) - w'))\<close>
    if
      \<open>j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
          w \<le> length (W ! nat_of_lit L)\<close> and
      pre: \<open>j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
          w \<le> length (W ! nat_of_lit L)\<close> and
      I: \<open>case s of (j, w, W) \<Rightarrow> j \<le> w \<and> nat_of_lit L < length W\<close> and
      I': \<open>I' s\<close> and
      cond: \<open>case s of (j, w, W) \<Rightarrow> w < length (W ! nat_of_lit L)\<close> and
      [simp]: \<open>x2 = (x1k, x2k)\<close> and
      [simp]: \<open>s = (x1j, x2)\<close>
    for s x1j x2 x1k x2k
  proof -
      have [simp]: \<open>x1k < length (x2k ! nat_of_lit L)\<close> and
        \<open>length (W ! nat_of_lit L) - Suc x1k < length (W ! nat_of_lit L) - x1k\<close>
        using cond I I' unfolding I'_def by auto
      moreover have \<open>x1j \<le> x1k\<close> \<open>nat_of_lit L < length x2k\<close>
        using I I' unfolding I'_def by auto
      moreover have \<open>I' (Suc x1j, Suc x1k, x2k
        [nat_of_lit L := (x2k ! nat_of_lit L)[x1j := x2k ! nat_of_lit L ! x1k]])\<close>
      proof -
        have ball_leI:  \<open>(\<And>x. x < A \<Longrightarrow> P x) \<Longrightarrow> (\<forall>x < A. P x)\<close> for A P
          by auto
        have H: \<open>\<And>i. x2k[nat_of_lit L := take (j + x1k - w) (x2k ! nat_of_lit L)] ! i = W
    [nat_of_lit L :=
       take (min (j + x1k - w) j) (W ! nat_of_lit L) @
       take (j + x1k - (w + min (length (W ! nat_of_lit L)) j))
        (drop w (W ! nat_of_lit L))] ! i\<close> and
          H': \<open>x2k[nat_of_lit L := take (j + x1k - w) (x2k ! nat_of_lit L)] = W
          [nat_of_lit L :=
       take (min (j + x1k - w) j) (W ! nat_of_lit L) @
       take (j + x1k - (w + min (length (W ! nat_of_lit L)) j))
        (drop w (W ! nat_of_lit L))]\<close> and
          \<open>j < length (W ! nat_of_lit L)\<close> and
          \<open>(length (W ! nat_of_lit L) - w) \<ge> (Suc x1k - w)\<close> and
          \<open>x1k \<ge> w\<close>
          \<open>nat_of_lit L < length W\<close> and
          \<open>j + x1k - w = x1j\<close> and
          \<open>x1j - j = x1k - w\<close> and
          \<open>x1j < length (W ! nat_of_lit L)\<close> and
          \<open>length (x2k ! nat_of_lit L) = length (W ! nat_of_lit L)\<close> and
          \<open>drop x1k (x2k ! (nat_of_lit L)) = drop x1k (W ! (nat_of_lit L))\<close>
          \<open>x1j \<ge> j\<close>  and
          \<open>w + x1j - j = x1k\<close>
          using I I' pre cond unfolding I'_def by auto
        have
          [simp]: \<open>min x1j j = j\<close>
          using \<open>x1j \<ge> j\<close> unfolding min_def by auto
        have \<open>x2k[nat_of_lit L := take (Suc (j + x1k) - w) (x2k[nat_of_lit L := (x2k ! nat_of_lit L)
                  [x1j := x2k ! nat_of_lit L ! x1k]] ! nat_of_lit L)] =
           W[nat_of_lit L := take j (W ! nat_of_lit L) @ take (Suc (j + x1k) - (w + min (length (W ! nat_of_lit L)) j))
               (drop w (W ! nat_of_lit L))]\<close>
          using cond I \<open>j < length (W ! nat_of_lit L)\<close> and
           \<open>(length (W ! nat_of_lit L) - w) \<ge> (Suc x1k - w)\<close> and
            \<open>x1k \<ge> w\<close>
            \<open>nat_of_lit L < length W\<close>
            \<open>j + x1k - w = x1j\<close> \<open>x1j < length (W ! nat_of_lit L)\<close>
          apply (subst list_eq_iff_nth_eq)
          apply -
          apply (intro conjI ball_leI)
          subgoal using arg_cong[OF H', of length] by auto
          subgoal for k
            apply (cases \<open>k \<noteq> nat_of_lit L\<close>)
            subgoal using H[of k] by auto
            subgoal
              using H[of k] \<open>x1j < length (W ! nat_of_lit L)\<close>
                \<open>length (x2k ! nat_of_lit L) = length (W ! nat_of_lit L)\<close>
                arg_cong[OF \<open>drop x1k (x2k ! (nat_of_lit L)) = drop x1k (W ! (nat_of_lit L))\<close>,
                   of \<open>\<lambda>xs. xs ! 0\<close>] \<open>x1j \<ge> j\<close>
              apply (cases \<open>Suc x1j = length (W ! nat_of_lit L)\<close>)
              apply (auto simp add: Suc_diff_le take_Suc_conv_app_nth \<open>j + x1k - w = x1j\<close>
                 \<open>x1j - j = x1k - w\<close>[symmetric] \<open>w + x1j - j = x1k\<close>)
                 apply (metis append.assoc le_neq_implies_less list_update_id nat_in_between_eq(1)
                   not_less_eq take_Suc_conv_app_nth take_all)
                by (metis (no_types, lifting) \<open>x1j < length (W ! nat_of_lit L)\<close> append.assoc
                  take_Suc_conv_app_nth take_update_last)
            done
          done
        then show ?thesis
          unfolding I'_def prod.case
          using I I' cond unfolding I'_def by (auto simp: Cons_nth_drop_Suc[symmetric])
      qed
      ultimately show ?thesis
        by auto
    qed

    have step: \<open>(s, W[nat_of_lit L := take j (W ! nat_of_lit L) @ drop w (W ! nat_of_lit L)])
      \<in>  {((i, j, W'), W). (W'[nat_of_lit L := take i (W' ! nat_of_lit L)], W) \<in> Id \<and>
         i \<le> length (W' ! nat_of_lit L) \<and> nat_of_lit L < length W'}\<close>
      if
        pre: \<open>j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
     w \<le> length (W ! nat_of_lit L)\<close> and
        \<open>j \<le> length (W ! nat_of_lit L) \<and> j \<le> w \<and> nat_of_lit L < length W \<and>
     w \<le> length (W ! nat_of_lit L)\<close> and
        \<open>case s of (j, w, W) \<Rightarrow> j \<le> w \<and> nat_of_lit L < length W\<close> and
        \<open>I' s\<close> and
        \<open>\<not> (case s of (j, w, W) \<Rightarrow> w < length (W ! nat_of_lit L))\<close>
      for s
    proof -
      obtain j' w' W' where s: \<open>s = (j', w', W')\<close> by (cases s)
      have
        \<open>\<not> w' < length (W' ! nat_of_lit L)\<close> and
        \<open>j \<le> length (W ! nat_of_lit L)\<close> and
        \<open>j' \<le> w'\<close> and
        \<open>nat_of_lit L < length W'\<close> and
        [simp]: \<open>length (W' ! nat_of_lit L) = length (W ! nat_of_lit L)\<close> and
        \<open>j \<le> w\<close> and
        \<open>j' \<le> w'\<close> and
        \<open>nat_of_lit L < length W\<close> and
        \<open>w \<le> length (W ! nat_of_lit L)\<close> and
        \<open>w \<le> w'\<close> and
        \<open>w' - w = j' - j\<close> and
        \<open>j \<le> j'\<close> and
        \<open>drop w' (W' ! nat_of_lit L) = drop w' (W ! nat_of_lit L)\<close> and
        \<open>w' \<le> length (W' ! nat_of_lit L)\<close> and
        L_le_W: \<open>nat_of_lit L < length W\<close> and
        eq: \<open>W'[nat_of_lit L := take (j + w' - w) (W' ! nat_of_lit L)] =
            W[nat_of_lit L := take (j + w' - w) (take j (W ! nat_of_lit L) @ drop w (W ! nat_of_lit L))]\<close>
        using that unfolding I'_def that prod.case s
        by blast+
      then have
        j_j': \<open>j + w' - w = j'\<close> and
        j_le: \<open>j + w' - w = length (take j (W ! nat_of_lit L) @ drop w (W ! nat_of_lit L))\<close> and
        w': \<open>w' = length (W ! nat_of_lit L)\<close>
        by auto
      have [simp]: \<open>length W = length W'\<close>
        using arg_cong[OF eq, of length] by auto
      show ?thesis
        using eq \<open>j \<le> w\<close> \<open>w \<le> length (W ! nat_of_lit L)\<close> \<open>j \<le> j'\<close> \<open>w' - w = j' - j\<close>
          \<open>w \<le> w'\<close> w' L_le_W
        unfolding j_j' j_le s
        by (auto simp: min_def split: if_splits)
  qed

  have HHH[refine0]: \<open>X \<le> RES (R\<inverse> `` {S}) \<Longrightarrow> X \<le> \<Down> R (RETURN S)\<close> for X S R
    by (auto simp: RETURN_def conc_fun_RES)

  show ?thesis
    unfolding cut_watch_list_heur2_def cut_watch_list_heur_alt_def prod.case S
    apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where R = ?R and
      I' = I' and \<Phi> = \<open>{((i, j, W'), W). (W'[nat_of_lit L := take i (W' ! nat_of_lit L)], W) \<in> Id \<and>
         i \<le> length (W' ! nat_of_lit L) \<and> nat_of_lit L < length W'}\<inverse> `` _\<close>] HHH)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by auto
    subgoal unfolding I'_def by auto
    subgoal using REC by auto
    subgoal unfolding I'_def by auto
    subgoal using step unfolding I'_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma (in isasat_input_ops) vdom_m_cut_watch_list:
  \<open>set xs \<subseteq> set (W L) \<Longrightarrow> vdom_m (W(L := xs)) d \<subseteq> vdom_m W d\<close>
  by (cases \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>)
    (force simp: vdom_m_def split: if_splits)+

text \<open>The following order allows the rule to be used as a destruction rule, make it more
useful for refinement proofs.\<close>
lemma (in isasat_input_ops) vdom_m_cut_watch_listD:
  \<open>x \<in> vdom_m (W(L := xs)) d \<Longrightarrow> set xs \<subseteq> set (W L) \<Longrightarrow> x \<in> vdom_m W d\<close>
  using vdom_m_cut_watch_list[of xs W L] by auto

lemma cut_watch_list_heur_cut_watch_list_heur:
  \<open>(uncurry3 cut_watch_list_heur, uncurry3 cut_watch_list) \<in>
  [\<lambda>(((j, w), L), S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> j \<le> length (watched_by S L)]\<^sub>f
  nat_rel  \<times>\<^sub>f nat_rel  \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D>\<rangle>nres_rel\<close>
    unfolding cut_watch_list_heur_def cut_watch_list_def uncurry_def
  apply (intro frefI nres_relI)
  apply refine_vcg
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def)
  subgoal
    by (auto simp: cut_watch_list_heur_def cut_watch_list_def twl_st_heur'_def
      twl_st_heur_def map_fun_rel_def vdom_m_cut_watch_list set_take_subset
        set_drop_subset dest!: vdom_m_cut_watch_listD
        dest!: in_set_dropD in_set_takeD)
  done

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>unit_propagation_inner_loop_wl_D_heur L S\<^sub>0 = do {
     (j, w, S) \<leftarrow> unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0;
     S \<leftarrow> cut_watch_list_heur2 j w L S;
     RETURN S
  }\<close>

lemma unit_propagation_inner_loop_wl_D_heur_unit_propagation_inner_loop_wl_D:
  \<open>(uncurry unit_propagation_inner_loop_wl_D_heur, uncurry unit_propagation_inner_loop_wl_D) \<in>
    nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle> nres_rel\<close>
  unfolding unit_propagation_inner_loop_wl_D_heur_def
    unit_propagation_inner_loop_wl_D_def uncurry_def
    apply (intro frefI nres_relI)
  apply (refine_vcg cut_watch_list_heur_cut_watch_list_heur[of \<D>, THEN fref_to_Down_curry3]
      unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D[of \<D>, THEN fref_to_Down_curry])
  subgoal by auto
  apply (rule order.trans)
  apply (rule cut_watch_list_heur2_cut_watch_list_heur)
  apply (subst Down_id_eq)
  apply (rule cut_watch_list_heur_cut_watch_list_heur[of \<D>, THEN fref_to_Down_curry3])
  by auto

definition (in isasat_input_ops) select_and_remove_from_literals_to_update_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal) nres\<close>
where
  \<open>select_and_remove_from_literals_to_update_wl_heur S = do {
    ASSERT(literals_to_update_wl_heur S < length (get_trail_wl_heur S));
    ASSERT(literals_to_update_wl_heur S + 1 \<le> uint32_max);
    RETURN (set_literals_to_update_wl_heur (literals_to_update_wl_heur S + 1) S,
     -lit_of (rev (get_trail_wl_heur S) ! (literals_to_update_wl_heur S)))
  }\<close>


definition (in isasat_input_ops) unit_propagation_outer_loop_wl_D_heur_inv
 :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 S' \<longleftrightarrow>
     (\<exists>S\<^sub>0' S. (S\<^sub>0, S\<^sub>0') \<in> twl_st_heur \<and> (S', S) \<in> twl_st_heur \<and> unit_propagation_outer_loop_wl_D_inv S \<and>
       dom_m (get_clauses_wl S) = dom_m (get_clauses_wl S\<^sub>0'))\<close>

definition (in isasat_input_ops) unit_propagation_outer_loop_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>unit_propagation_outer_loop_wl_D_heur S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0\<^esup>
      (\<lambda>S. literals_to_update_wl_heur S < length (get_trail_wl_heur S))
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl_heur S < length (get_trail_wl_heur S));
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl_heur S;
        unit_propagation_inner_loop_wl_D_heur L S'
      })
      S\<^sub>0\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(select_and_remove_from_literals_to_update_wl_heur, select_and_remove_from_literals_to_update_wl) \<in>
  [\<lambda>S. literals_to_update_wl S \<noteq> {#} \<and>
     length (get_trail_wl S) < uint32_max]\<^sub>f
   twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D> \<times>\<^sub>f nat_lit_lit_rel\<rangle> nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
    select_and_remove_from_literals_to_update_wl_def
  by (intro frefI nres_relI)
    (auto simp: Cons_nth_drop_Suc[symmetric] intro!: ASSERT_leI
      simp: twl_st_heur_def twl_st_heur'_def RETURN_RES_refine_iff)

lemma unit_propagation_outer_loop_wl_D_heur_inv_length_trail_le:
  assumes
    \<open>(S, T) \<in> twl_st_heur' \<D>\<close>
    \<open>(U, V) \<in> twl_st_heur' \<D>\<close> and
    \<open>literals_to_update_wl_heur U < length (get_trail_wl_heur U)\<close> and
    \<open>literals_to_update_wl V \<noteq> {#}\<close> and
    \<open>unit_propagation_outer_loop_wl_D_heur_inv S U\<close> and
    \<open>unit_propagation_outer_loop_wl_D_inv V\<close> and
    \<open>literals_to_update_wl V \<noteq> {#}\<close> and
    \<open>literals_to_update_wl_heur U < length (get_trail_wl_heur U)\<close>
   shows \<open>length (get_trail_wl V) < uint_max\<close>
proof -
  obtain T U b b' where
    VT: \<open>(V, T) \<in> state_wl_l b\<close> and
    struct: \<open>twl_struct_invs U\<close> and
    TU: \<open>(T, U) \<in> twl_st_l b'\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n V\<close>
    using assms
    unfolding unit_propagation_outer_loop_wl_D_inv_def unit_propagation_outer_loop_wl_D_heur_inv_def
    unit_propagation_outer_loop_wl_inv_def
    unit_propagation_outer_loop_l_inv_def apply -
    apply normalize_goal+
    by blast
  then have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl V)\<close>
    by (rule literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail)
  moreover have \<open>no_dup (get_trail_wl V)\<close>
    using VT TU struct
    unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: twl_st)
  ultimately show ?thesis
    using literals_are_in_\<L>\<^sub>i\<^sub>n_trail_length_le_uint32_max[of \<open>get_trail_wl V\<close>]
    by (auto simp: uint32_max_def)
qed
theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D':
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl_D) \<in>
    twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle> nres_rel\<close>
  unfolding unit_propagation_outer_loop_wl_D_heur_def
    unit_propagation_outer_loop_wl_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_inner_loop_wl_D_heur_unit_propagation_inner_loop_wl_D[THEN fref_to_Down_curry]
      select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl
          [of \<D>, THEN fref_to_Down])
  subgoal unfolding unit_propagation_outer_loop_wl_D_heur_inv_def twl_st_heur'_def by blast
  subgoal by (auto simp: twl_st_heur_state_simp twl_st_heur'_def)
  subgoal by (rule unit_propagation_outer_loop_wl_D_heur_inv_length_trail_le)
  subgoal by (auto simp: twl_st_heur'_def)
  done

lemma twl_st_heur'D_twl_st_heurD:
  assumes H: \<open>(\<And>\<D>. f \<in> twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    using assms unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur' (dom_m (get_clauses_wl y))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed

theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D:
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>
  using twl_st_heur'D_twl_st_heurD[OF
     unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D']
  .

end


context isasat_input_bounded
begin

lemma watched_by_app_watched_by_app_heur:
  \<open>(uncurry2 (RETURN ooo watched_by_app_heur), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_heur_def watched_by_app_def twl_st_heur_def map_fun_rel_def)

sepref_thm watched_by_app_heur_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> watcher_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp]
  unfolding watched_by_app_heur_alt_def isasat_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  by sepref

concrete_definition (in -) watched_by_app_heur_code
   uses isasat_input_bounded.watched_by_app_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_code_def

lemmas watched_by_app_heur_code_refine[sepref_fr_rules] =
   watched_by_app_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

(* TODO it is not clear how to prove that. We probably need a stonger propery on our WL for that.
sepref_thm watched_by_app_heur_fast_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[watched_by_app_heur_pre]\<^sub>a
        isasat_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a unat_lit_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp]
  unfolding watched_by_app_heur_alt_def isasat_fast_assn_def nth_rll_def[symmetric]
   watched_by_app_heur_pre_def
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
           apply sepref_dbg_side_unfold apply (auto simp: )[]

  by sepref

concrete_definition (in -) watched_by_app_heur_fast_code
   uses isasat_input_bounded.watched_by_app_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_fast_code_def

lemmas watched_by_app_heur_fast_code_refine[sepref_fr_rules] =
   watched_by_app_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]
 *)

sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]]
  unfolding isasat_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma access_lit_in_clauses_heur_fast_pre:
  \<open>arena_lit_pre (get_clauses_wl_heur a) (ba + b) \<Longrightarrow>
       isasat_fast a \<Longrightarrow>
       a = (a1', a2') \<Longrightarrow>
       a2' = (a1'a, a2'a) \<Longrightarrow>
       ba + b \<le> uint64_max\<close>
  by (auto simp: arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      dest!: arena_lifting(10)
      dest!: isasat_fast_length_leD)[]


sepref_thm access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
        isasat_fast S]\<^sub>a
      isasat_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]] access_lit_in_clauses_heur_fast_pre[intro!]
  unfolding isasat_fast_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_fast_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_fast_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_fast_code_def

lemmas access_lit_in_clauses_heur_fast_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

end


lemma case_tri_bool_If:
  \<open>(case a of
       None \<Rightarrow> f1
     | Some v \<Rightarrow>
        (if v then f2 else f3)) =
   (let b = a in if b = UNSET
    then f1
    else if b = SET_TRUE then f2 else f3)\<close>
  by (auto split: option.splits)


context isasat_input_bounded_nempty
begin

definition isa_find_unset_lit :: \<open>(nat, nat) ann_lits \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
  \<open>isa_find_unset_lit M = isa_find_unwatched_between (\<lambda>L. polarity M L \<noteq> Some False)\<close>

(* TODO most of the unfolding should move to the definition *)
sepref_register isa_find_unwatched_wl_st_heur isa_find_unwatched_between isa_find_unset_lit

sepref_thm isa_find_unwatched_between_code
  is \<open>uncurry4 (PR_CONST isa_find_unset_lit)\<close>
  :: \<open>trail_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a
       option_assn nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isa_find_unset_lit_def isa_find_unwatched_between_def SET_FALSE_def[symmetric]
    PR_CONST_def
  apply (rewrite in \<open>(None, _)\<close> annotate_assn[where A = \<open>option_assn nat_assn\<close>])
  apply (rewrite in \<open>(None, _)\<close> annotate_assn[where A = \<open>option_assn nat_assn\<close>])
  apply (rewrite in \<open>if \<hole> then _ else _\<close>  tri_bool_eq_def[symmetric])
  by sepref


concrete_definition (in -) isa_find_unwatched_between_code
   uses isasat_input_bounded_nempty.isa_find_unwatched_between_code.refine_raw
   is \<open>(uncurry4 ?f, _)\<in>_\<close>

prepare_code_thms (in -) isa_find_unwatched_between_code_def

lemmas isa_find_unwatched_between_code_hnr[sepref_fr_rules] =
   isa_find_unwatched_between_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm find_unwatched_wl_st_heur_code
  is \<open>uncurry ((PR_CONST isa_find_unwatched_wl_st_heur))\<close>
  :: \<open>[find_unwatched_wl_st_heur_pre]\<^sub>a
         isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]]
    fmap_length_rll_def[simp] fmap_length_rll_u64_def[simp]
    get_saved_pos_code[sepref_fr_rules]
  unfolding isa_find_unwatched_wl_st_heur_def isasat_assn_def PR_CONST_def
  find_unwatched_def fmap_rll_def[symmetric]
  length_u_def[symmetric] isa_find_unwatched_def
  case_tri_bool_If find_unwatched_wl_st_heur_pre_def
  fmap_rll_u64_def[symmetric]
  MAX_LENGTH_SHORT_CLAUSE_def[symmetric]
  isa_find_unset_lit_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm isa_find_unwatched_between_fast_code
  is \<open>uncurry4 (PR_CONST isa_find_unset_lit)\<close>
  :: \<open>[\<lambda>((((M, N), _), _), _). length N \<le> uint64_max - (uint32_max + 5)]\<^sub>a
     trail_fast_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>
       option_assn uint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding isa_find_unset_lit_def isa_find_unwatched_between_def SET_FALSE_def[symmetric]
    PR_CONST_def one_uint64_nat_def[symmetric]
  apply (rewrite in \<open>(None, _)\<close> annotate_assn[where A = \<open>option_assn uint64_nat_assn\<close>])
  apply (rewrite in \<open>(None, _)\<close> annotate_assn[where A = \<open>option_assn uint64_nat_assn\<close>])
  apply (rewrite in \<open>if \<hole> then _ else _\<close>  tri_bool_eq_def[symmetric])
  by sepref


concrete_definition (in -) isa_find_unwatched_between_fast_code
   uses isasat_input_bounded_nempty.isa_find_unwatched_between_fast_code.refine_raw
   is \<open>(uncurry4 ?f, _)\<in>_\<close>

prepare_code_thms (in -) isa_find_unwatched_between_fast_code_def

lemmas isa_find_unwatched_between_fast_code_hnr[sepref_fr_rules] =
   isa_find_unwatched_between_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

declare get_saved_pos_code[sepref_fr_rules]


sepref_thm find_unwatched_wl_st_heur_fast_code
  is \<open>uncurry ((PR_CONST isa_find_unwatched_wl_st_heur))\<close>
  :: \<open>[(\<lambda>(S, C). find_unwatched_wl_st_heur_pre (S, C) \<and> isasat_fast S)]\<^sub>a
         isasat_fast_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> option_assn uint64_nat_assn\<close>
  supply [[goals_limit = 1]]
    fmap_length_rll_def[simp] fmap_length_rll_u64_def[simp]
    uint64_of_uint32_conv_hnr[sepref_fr_rules] isasat_fast_def[simp]
  unfolding isa_find_unwatched_wl_st_heur_def PR_CONST_def
    find_unwatched_def fmap_rll_def[symmetric] isasat_fast_assn_def
    length_u_def[symmetric] isa_find_unwatched_def
    case_tri_bool_If find_unwatched_wl_st_heur_pre_def
    fmap_rll_u64_def[symmetric]
    MAX_LENGTH_SHORT_CLAUSE_def[symmetric]
    isa_find_unset_lit_def[symmetric]
    two_uint64_nat_def[symmetric]
    nat_of_uint64_conv_def
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_fast_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_fast_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_fast_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_fast_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma update_clause_wl_heur_pre_le_uint64:
  assumes
    \<open>arena_is_valid_clause_idx_and_access a1'a bf baa\<close> and
    \<open>isasat_fast
      (a1', a1'a, (da, db, dc), a1'c, a1'd, ((eu, ev, ew, ex, ey), ez), fa, fb,
       fc, fd, fe, (ff, fg, fh, fi), fj, fk, fl, fm, fn)\<close> and
    \<open>arena_lit_pre a1'a (bf + baa)\<close>
  shows \<open>bf + baa \<le> uint64_max\<close>
       \<open>length a1'a \<le> uint64_max\<close>
  using assms
  by (auto simp: arena_is_valid_clause_idx_and_access_def isasat_fast_def
    dest!: arena_lifting(10))

sepref_register update_clause_wl_heur
sepref_thm update_clause_wl_code
  is \<open>uncurry7 (PR_CONST update_clause_wl_heur)\<close>
  :: \<open>[update_clause_wl_code_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k
        *\<^sub>a isasat_assn\<^sup>d \<rightarrow> nat_assn *a nat_assn *a isasat_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
    update_clause_wl_heur_pre_le_uint64[intro!]
  unfolding update_clause_wl_heur_def isasat_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry7 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

sepref_thm update_clause_wl_fast_code
  is \<open>uncurry7 (PR_CONST update_clause_wl_heur)\<close>
  :: \<open>[\<lambda>(((((((L, C), b), j), w), i), f), S). update_clause_wl_code_pre (((((((L, C), b), j), w), i), f), S) \<and>
        isasat_fast S]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k
        *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> nat_assn *a nat_assn *a isasat_fast_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
    update_clause_wl_heur_pre_le_uint64[intro!]
  unfolding update_clause_wl_heur_def isasat_fast_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    fmap_swap_ll_def[symmetric]
    PR_CONST_def
  by sepref


concrete_definition (in -) update_clause_wl_fast_code
  uses isasat_input_bounded_nempty.update_clause_wl_fast_code.refine_raw
  is \<open>(uncurry7 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_fast_code_def

lemmas update_clause_wl_fast_code[sepref_fr_rules] =
  update_clause_wl_fast_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]
(*
thm update_clause_wl_code_pre_def
sepref_thm update_clause_wl_fast_code
  is \<open>uncurry6 update_clause_wl_heur\<close>
  :: \<open>[\<lambda>((((((L, C), j), w), i), f), S). update_clause_wl_code_pre ((((((L, C), j), w), i), f), S) \<and>
      w < uint64_max]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow>
       uint64_nat_assn *a uint64_nat_assn *a isasat_fast_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_fast_assn_def Array_List_Array.swap_ll_def[symmetric]
    fmap_rll_def[symmetric] delete_index_and_swap_update_def[symmetric]
    delete_index_and_swap_ll_def[symmetric] fmap_swap_ll_def[symmetric]
    append_ll_def[symmetric] update_clause_wl_code_pre_def
    fmap_rll_u64_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    one_uint64_nat_def[symmetric]
  by sepref

concrete_definition (in -) update_clause_wl_fast_code
  uses isasat_input_bounded_nempty.update_clause_wl_fast_code.refine_raw
  is \<open>(uncurry6 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_fast_code_def

lemmas update_clause_wl_fast_code[sepref_fr_rules] =
  update_clause_wl_fast_code.refine[OF isasat_input_bounded_nempty_axioms] *)

sepref_register propagate_lit_wl_heur
sepref_thm propagate_lit_wl_code
  is \<open>uncurry3 (PR_CONST propagate_lit_wl_heur)\<close>
  :: \<open>[propagate_lit_wl_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
  by sepref


concrete_definition (in -) propagate_lit_wl_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_code_def

lemmas propagate_lit_wl_code[sepref_fr_rules] =
  propagate_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

(* sepref_thm propagate_lit_wl_fast_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propagate_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(((L', C), w), S). propagate_lit_wl_heur_pre (((L', C), w), S) \<and>
        w + 1 \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  unfolding PR_CONST_def propagate_lit_wl_heur_def isasat_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def isasat_fast_assn_def
    propagate_lit_wl_heur_pre_def fmap_swap_ll_def[symmetric]
    fmap_swap_ll_u64_def[symmetric]
    zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric]
  by sepref


concrete_definition (in -) propagate_lit_wl_fast_code
  uses isasat_input_bounded_nempty.propagate_lit_wl_fast_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propagate_lit_wl_fast_code_def

lemmas propagate_lit_wl_fast_code[sepref_fr_rules] =
  propagate_lit_wl_fast_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def] *)

lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN \<circ>\<circ> clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C.
     RETURN (arena_status arena C \<noteq> DELETED))\<close>
  unfolding clause_not_marked_to_delete_heur_def by (auto intro!: ext)


sepref_thm clause_not_marked_to_delete_heur_code
  is \<open>uncurry (RETURN oo clause_not_marked_to_delete_heur)\<close>
  :: \<open>[clause_not_marked_to_delete_heur_pre]\<^sub>a isasat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding clause_not_marked_to_delete_heur_alt_def isasat_assn_def
     clause_not_marked_to_delete_heur_pre_def
  by sepref

concrete_definition (in -) clause_not_marked_to_delete_heur_code
   uses isasat_input_bounded_nempty.clause_not_marked_to_delete_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) clause_not_marked_to_delete_heur_code_def

lemmas clause_not_marked_to_delete_heur_refine[sepref_fr_rules] =
   clause_not_marked_to_delete_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_thm update_blit_wl_heur_code
  is \<open>uncurry6 update_blit_wl_heur\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a
     nat_assn *a nat_assn *a isasat_assn\<close>
  supply [[goals_limit=1]] length_ll_def[simp]
  unfolding update_blit_wl_heur_def isasat_assn_def update_ll_def[symmetric]
  by sepref

concrete_definition (in -) update_blit_wl_heur_code
   uses isasat_input_bounded_nempty.update_blit_wl_heur_code.refine_raw
   is \<open>(uncurry6 ?f, _) \<in> _\<close>

prepare_code_thms (in -) update_blit_wl_heur_code_def

lemmas update_blit_wl_heur_heur_refine[sepref_fr_rules] =
   update_blit_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

sepref_register keep_watch_heur
sepref_thm keep_watch_heur
  is \<open>uncurry3 (PR_CONST keep_watch_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp] length_ll_def[simp]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
    update_raa_hnr[sepref_fr_rules]
  unfolding keep_watch_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric] isasat_assn_def
  unfolding fast_minus_def[symmetric]
    nth_rll_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
    update_ll_def[symmetric]
  by sepref

concrete_definition (in -) keep_watch_heur_code
  uses isasat_input_bounded_nempty.keep_watch_heur.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) keep_watch_heur_code_def

lemmas keep_watch_heur_code[sepref_fr_rules] =
  keep_watch_heur_code.refine[OF isasat_input_bounded_nempty_axioms, unfolded PR_CONST_def]

sepref_register isa_set_lookup_conflict_aa set_conflict_wl_heur
sepref_thm set_conflict_wl_heur_code
  is \<open>uncurry (PR_CONST set_conflict_wl_heur)\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow> isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_assn_def IICF_List_Mset.lms_fold_custom_empty
    set_conflict_wl_heur_pre_def PR_CONST_def
  by sepref

concrete_definition (in -) set_conflict_wl_heur_code
  uses isasat_input_bounded_nempty.set_conflict_wl_heur_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl_heur_code_def

lemmas set_conflict_wl_heur_code[sepref_fr_rules] =
  set_conflict_wl_heur_code.refine[OF isasat_input_bounded_nempty_axioms]


(* sepref_thm set_conflict_wl_heur_fast_code
  is \<open>uncurry set_conflict_wl_heur\<close>
  :: \<open>[set_conflict_wl_heur_pre]\<^sub>a
    uint32_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow> isasat_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding set_conflict_wl_heur_def isasat_fast_assn_def IICF_List_Mset.lms_fold_custom_empty
    set_conflict_wl_heur_pre_def
  by sepref

concrete_definition (in -) set_conflict_wl_heur_fast_code
  uses isasat_input_bounded_nempty.set_conflict_wl_heur_fast_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl_heur_fast_code_def

lemmas set_conflict_wl_heur_fast_code[sepref_fr_rules] =
  set_conflict_wl_heur_fast_code.refine[OF isasat_input_bounded_nempty_axioms] *)

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context isasat_input_bounded_nempty
begin

context
begin

sepref_register update_blit_wl_heur clause_not_marked_to_delete_heur
sepref_thm unit_propagation_inner_loop_body_wl_heur
  is \<open>uncurry3 (PR_CONST unit_propagation_inner_loop_body_wl_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *a nat_assn *a isasat_assn\<close>
  supply
    [[goals_limit=1]]
    if_splits[split]
    length_rll_def[simp]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp]
    unit_propagation_inner_loop_wl_loop_D_heur_inv0_def[simp]
    unit_propagation_inner_loop_wl_loop_D_inv_def[simp]
    image_image[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric] tri_bool_eq_def[symmetric]
  by sepref

(* sepref_thm unit_propagation_inner_loop_body_wl_fast_heur
  is \<open>uncurry3 (PR_CONST unit_propagation_inner_loop_body_wl_heur)\<close>
  :: \<open>[\<lambda>((L, w), S). w+1 \<le> uint64_max]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a isasat_fast_assn\<^sup>d \<rightarrow>
      uint64_nat_assn *a uint64_nat_assn *a isasat_fast_assn\<close>
  supply
    if_splits[split]
    length_rll_def[simp]
    watched_by_app_heur_code_refine[sepref_fr_rules]
  supply undefined_lit_polarity_st_iff[iff]
    unit_prop_body_wl_D_find_unwatched_heur_inv_def[simp] uint64_max_def[simp]
  unfolding unit_propagation_inner_loop_body_wl_heur_def length_rll_def[symmetric] PR_CONST_def
  unfolding fmap_rll_def[symmetric]
  unfolding fast_minus_def[symmetric]
    SET_FALSE_def[symmetric] SET_TRUE_def[symmetric]
  apply (rewrite in \<open>let _ = \<hole> in _\<close> zero_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>let _ = \<hole> in _\<close> one_uint64_nat_def[symmetric])+
  apply (rewrite in \<open>RETURN (_ + _, _)\<close> one_uint64_nat_def[symmetric])+
  by sepref *)

end


sepref_register unit_propagation_inner_loop_body_wl_D

concrete_definition (in -) unit_propagation_inner_loop_body_wl_heur_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_heur.refine_raw
   is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_heur_code_def

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
(*
concrete_definition (in -) unit_propagation_inner_loop_body_wl_heur_fast_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_fast_heur.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_heur_fast_code_def

lemmas unit_propagation_inner_loop_body_wl_D_fast_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_heur_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms] *)

end

end