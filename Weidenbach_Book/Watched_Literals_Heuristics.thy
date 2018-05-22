theory Watched_Literals_Heuristics
  imports Watched_Literals_Watch_List_Code_Common IsaSAT_Setup IsaSAT_Clauses
begin

subsection \<open>Getters\<close>

fun watched_by_int :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, W, _) = W\<close>

fun literals_to_update_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat lit_queue_wl\<close> where
  \<open>literals_to_update_wl_heur (M, N, D, Q, W, _, _)  = Q\<close>

fun set_literals_to_update_wl_heur :: \<open>nat lit_queue_wl \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>set_literals_to_update_wl_heur Q (M, N, D, _, W') = (M, N, D, Q, W')\<close>

definition watched_by_app_heur_pre where
  \<open>watched_by_app_heur_pre = (\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L))\<close>

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

lemma watched_by_app_heur_alt_def:
  \<open>watched_by_app_heur = (\<lambda>(M, N, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>
  by (auto simp: watched_by_app_heur_def intro!: ext)

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> vmtf_remove_int\<close> where
  \<open>get_vmtf_heur (M, N, D, WS, W, cvmtf, _) = cvmtf\<close>


subsection \<open>Propagations\<close>

(* TODO Move *)

context isasat_input_bounded
begin

lemma unit_prop_body_wl_D_invD:
  assumes \<open>unit_prop_body_wl_D_inv S w L\<close>
  shows
    \<open>w < length (watched_by S L)\<close> and
    \<open>watched_by_app S L w \<in># dom_m (get_clauses_wl S)\<close> and
    \<open>get_clauses_wl S \<propto> watched_by_app S L w \<noteq> []\<close> and
    \<open>Suc 0 < length (get_clauses_wl S \<propto> watched_by_app S L w)\<close> and
    \<open>get_clauses_wl S \<propto> watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>get_clauses_wl S \<propto> watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    \<open>watched_by_app S L w > 0\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>get_conflict_wl S = None\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> watched_by_app S L w))\<close> and
    \<open>distinct (get_clauses_wl S \<propto> watched_by_app S L w)\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl S)\<close> and
    \<open>length (get_clauses_wl S \<propto> watched_by_app S L w) \<le> uint64_max\<close>
proof -
  obtain T T' where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    S_T: \<open>(S, T) \<in> state_wl_l (Some (L, w))\<close> and
    \<open>L \<in># all_lits_of_mm
           (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close> and
    T_T': \<open>(set_clauses_to_update_l
       (clauses_to_update_l (remove_one_lit_from_wq (watched_by S L ! w) T) +
        {#watched_by S L ! w#})
       (remove_one_lit_from_wq (watched_by S L ! w) T),
      T')
     \<in> twl_st_l (Some L)\<close> and
    \<open>correct_watching S\<close> and
    struct: \<open>twl_struct_invs T'\<close> and
    \<open>w < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    stgy: \<open>twl_stgy_invs T'\<close> and
    \<open>watched_by S L ! w
     \<in># dom_m
         (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T))\<close> and
    watched_ge_0: \<open>0 < watched_by S L ! w\<close> and
    \<open>0 < length
          (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
           (watched_by S L ! w))\<close> and
    \<open>no_dup (get_trail_l (remove_one_lit_from_wq (watched_by S L ! w) T))\<close> and
    i_le: \<open>(if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
         (watched_by S L ! w) !
         0 =
         L
      then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
         (watched_by S L ! w))\<close> and
    ui_le: \<open>1 - (if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
             (watched_by S L ! w) !
             0 =
             L
          then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
         (watched_by S L ! w))\<close> and
    \<open>L \<in> set (watched_l
               (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! w) T) \<propto>
                (watched_by S L ! w)))\<close> and
    \<open>get_conflict_l (remove_one_lit_from_wq (watched_by S L ! w) T) = None\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      unit_propagation_inner_loop_body_l_inv_def
    apply - apply normalize_goal+
    by blast

  show \<open>w < length (watched_by S L)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by fast
  show S_L_W_le_S: \<open>watched_by_app S L w \<in># dom_m (get_clauses_wl S)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      unit_propagation_inner_loop_body_l_inv_def
    apply - by normalize_goal+ simp
  show
    \<open>get_clauses_wl S \<propto> watched_by_app S L w \<noteq> []\<close> and
    le: \<open>Suc 0 < length (get_clauses_wl S \<propto> watched_by_app S L w)\<close>
    using ui_le i_le S_T
    unfolding watched_by_app_def
    by (auto simp: twl_st_wl)
  have S_L_w_ge_0: \<open>0 < watched_by_app S L w\<close>
    using watched_ge_0 unfolding watched_by_app_def by auto
  obtain M N D NE UE W Q where
    S: \<open>S = (M, N, D, NE, UE, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> watched_by_app S L w))\<close>
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of ])
    apply (rule S_L_W_le_S)
    using lits by auto
  then show \<open>get_clauses_wl S \<propto> watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close>
    using le apply (cases \<open>get_clauses_wl S \<propto> watched_by_app S L w\<close>;
        cases \<open>get_clauses_wl S \<propto> watched_by_app S L w\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show \<open>get_clauses_wl S \<propto> watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close>
    using lits_N le apply (cases \<open>get_clauses_wl S \<propto> watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S \<propto> watched_by_app S L w)\<close>;
        cases \<open>tl (tl (get_clauses_wl S \<propto> watched_by_app S L w))\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show S_L_W_ge_0: \<open>watched_by_app S L w > 0\<close> and
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
  then show \<open>distinct (get_clauses_wl S \<propto> watched_by_app S L w)\<close>
    using S_L_W_le_S S_L_W_ge_0
    by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct
         clauses_def mset_take_mset_drop_mset watched_by_app_def)
  show \<open>L \<in> snd ` D\<^sub>0\<close>
    using  \<open>L \<in> snd ` D\<^sub>0\<close>  .
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
      lits_of_def image_image init_clss.simps mset_take_mset_drop_mset'
      convert_lits_l_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
      twl_st_l twl_st_wl twl_st get_unit_clauses_wl_alt_def)
  show \<open>length (get_clauses_wl S \<propto> watched_by_app S L w) \<le> uint64_max\<close>
    using clss_size_uint64_max[of \<open>mset (get_clauses_wl S \<propto> watched_by_app S L w)\<close>,
        OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S \<propto> watched_by_app S L w))\<close>]
      \<open>distinct (get_clauses_wl S \<propto> watched_by_app S L w)\<close> by auto
qed


definition (in -) find_unwatched_wl_st  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, D, NE, UE, Q, W) i. do {
    find_unwatched_l M (N \<propto> i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S \<propto> C) = find_unwatched_wl_st S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_st_def)

definition (in -) find_unwatched :: \<open>('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (nat option) nres\<close> where
\<open>find_unwatched M C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
      (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and>
       j < length C \<and> j \<ge> 2))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      ASSERT(i < length C);
      case polarity M (C!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
    })
    (None, 2::nat);
  RETURN (fst S)
  }
\<close>

definition (in isasat_input_ops) find_unwatched_wl_st_heur_pre where
  \<open>find_unwatched_wl_st_heur_pre =
     (\<lambda>(S, i). i \<in># dom_m (get_clauses_wl_heur S) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S \<and>
        length (get_clauses_wl_heur S \<propto> i) \<ge> 2 \<and> length (get_clauses_wl_heur S \<propto> i) < uint64_max)\<close>

definition (in isasat_input_ops) find_unwatched_wl_st_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st_heur = (\<lambda>(M, N, D, Q, W, vm, \<phi>) i. do {
    find_unwatched M (N \<propto> i)
  })\<close>


lemma (in -) find_unwatched:
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> \<Down> Id (find_unwatched_l M C)\<close>
  unfolding find_unwatched_def find_unwatched_l_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using distinct_consistent_interp[OF assms(1)]
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth
       polarity_def split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
    by (metis atLeastLessThan_iff less_antisym)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using no_dup_consistentD[OF assms(1)]
    by (cases s, cases \<open>fst s\<close>)
      (auto simp: Decided_Propagated_in_iff_in_lits_of_l all_set_conv_nth
        intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal by auto
  subgoal for s j by auto
  subgoal by auto
  done

definition (in isasat_input_ops) find_unwatched_wl_st_pre where
  \<open>find_unwatched_wl_st_pre =  (\<lambda>(S, i).
    i \<in># dom_m (get_clauses_wl S) \<and>
    literals_are_\<L>\<^sub>i\<^sub>n S \<and> 2 \<le> length (get_clauses_wl S \<propto> i) \<and>
    length (get_clauses_wl S \<propto> i) < uint64_max)\<close>

theorem find_unwatched_wl_st_heur_find_unwatched_wl_s:
  \<open>(uncurry find_unwatched_wl_st_heur, uncurry find_unwatched_wl_st)
    \<in> [find_unwatched_wl_st_pre]\<^sub>f
      twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_unwatched_wl_st_def find_unwatched_wl_st_heur_def twl_st_heur_def
    find_unwatched[simplified] find_unwatched_wl_st_pre_def)


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
     (\<lambda>(C, S). get_conflict_wl_heur S = None \<and> C \<in># dom_m (get_clauses_wl_heur S) \<and>
        distinct (get_clauses_wl_heur S \<propto> C) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl_heur S \<propto> C)) \<and>
        \<not> tautology (mset (get_clauses_wl_heur S \<propto> C)) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n_trail (get_trail_wl_heur S) \<and>
        no_dup (get_trail_wl_heur S) \<and>
       out_learned (get_trail_wl_heur S) (get_conflict_wl_heur S) (get_outlearned_heur S))\<close>

definition (in isasat_input_ops) set_conflict_wl_heur
  :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>set_conflict_wl_heur = (\<lambda>C (M, N, D, Q, W, vmtf, \<phi>, clvls, cach, lbd, outl, stats). do {
    let n = zero_uint32_nat;
    (D, clvls, lbd, outl) \<leftarrow> set_conflict_m M N C D n lbd outl;
    RETURN (M, N, D, {#}, W, vmtf, \<phi>, clvls, cach, lbd, outl, incr_conflict stats)})\<close>


definition (in isasat_input_ops) update_clause_wl_code_pre where
  \<open>update_clause_wl_code_pre = (\<lambda>(((((L, C), w), i), f), S).
      C \<in># dom_m (get_clauses_wl_heur S) \<and>
      f < length (get_clauses_wl_heur S \<propto> C) \<and>
      i < length (get_clauses_wl_heur S \<propto> C) \<and>
      nat_of_lit L < length (get_watched_wl_heur S) \<and>
      nat_of_lit ((get_clauses_wl_heur S \<propto> C) ! f)  < length (get_watched_wl_heur S) \<and>
      w < length (get_watched_wl_heur S ! nat_of_lit L))\<close>

definition (in isasat_input_ops) update_clause_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) C w i f (M, N, D, Q, W, vm). do {
     let K' = (N\<propto>C) ! f;
     let N' = N( C \<hookrightarrow> (swap (N\<propto>C) i f));
     let W = W[nat_of_lit L := delete_index_and_swap (W ! nat_of_lit L) w];
     RETURN (w, (M, N', D, Q,
            W[nat_of_lit K':= W ! nat_of_lit K' @ [C]],
            vm))
  })\<close>

lemma update_clause_wl_heur_update_clause_wl:
  \<open>(uncurry5 update_clause_wl_heur, uncurry5 (update_clause_wl)) \<in>
   [\<lambda>(((((L, C), w), i), f), S). C \<in># dom_m(get_clauses_wl S) \<and> (get_clauses_wl S \<propto> C) ! f \<noteq> L]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>
  \<langle>nat_rel \<times>\<^sub>r twl_st_heur' \<D>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def twl_st_heur'_def)

text \<open>TODO MOVE\<close>
lemma (in -)length_delete_index_and_swap_ll[simp]:
  \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)
text \<open>END MOVE\<close>

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) \<propto> i ! j\<close>

definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j). i \<in># dom_m (get_clauses_wl_heur S) \<and>
           j < length (get_clauses_wl_heur S \<propto> i) \<and>
           length (get_clauses_wl_heur S \<propto> i) \<le> uint64_max)\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = get_clauses_wl_heur S \<propto> i ! j\<close>

lemma access_lit_in_clauses_heur_alt_def:
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j.  N \<propto> i ! j)\<close>
  by (auto simp: access_lit_in_clauses_heur_def intro!: ext)

(* TODO Move *)
lemma literals_to_update_l_remove_one_lit_from_wq[simp]:
  \<open>literals_to_update_l (remove_one_lit_from_wq L T) = literals_to_update_l T\<close>
  by (cases T) auto

lemma clauses_to_update_l_remove_one_lit_from_wq[simp]:
  \<open>clauses_to_update_l (remove_one_lit_from_wq L T) = remove1_mset L (clauses_to_update_l T)\<close>
  by (cases T) auto

lemma lit_of_l_convert_lits_l[simp]:
  assumes \<open>(M, M') \<in> convert_lits_l N E\<close>
  shows
      \<open>lit_of ` set M' = lit_of ` set M\<close>
  using assms apply -
  apply (drule list_of_l_convert_lits_l)
  by (auto simp: lits_of_def)
(* End Move *)

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S \<propto> watched_by_app S L C))\<close>
    (is ?tauto is \<open>\<not>tautology ?D\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (watched_by_app S L C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    val: \<open>polarity_st S (get_clauses_wl S \<propto> watched_by_app S L C !
         (1 - (if access_lit_in_clauses S (watched_by_app S L C) 0 = L then 0 else 1))) =
          Some False\<close>
      (is \<open>polarity_st _ (_ \<propto> _ ! ?i) = Some False\<close>)
  for S C xj L
proof  -
  obtain M N D NE UE WS Q where
    S: \<open>S = (M, N, D, NE, UE, WS, Q)\<close>
    by (cases S)
  obtain T T' where
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    S_T: \<open>(S, T) \<in> state_wl_l (Some (L, C))\<close> and
    \<open>L \<in># all_lits_of_mm  (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close> and
    T_T': \<open>(set_clauses_to_update_l
       (clauses_to_update_l (remove_one_lit_from_wq (watched_by S L ! C) T) +
        {#watched_by S L ! C#})
       (remove_one_lit_from_wq (watched_by S L ! C) T),
      T')
     \<in> twl_st_l (Some L)\<close> and
    \<open>correct_watching S\<close> and
    inv: \<open>twl_struct_invs T'\<close> and
    C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    stgy_invs: \<open>twl_stgy_invs T'\<close> and
    \<open>watched_by S L ! C \<in># dom_m
         (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T))\<close> and
    \<open>0 < watched_by S L ! C\<close> and
    \<open>0 < length
          (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
           (watched_by S L ! C))\<close> and
    \<open>no_dup (get_trail_l (remove_one_lit_from_wq (watched_by S L ! C) T))\<close> and
    i_le: \<open>(if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C) !
         0 =
         L
      then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C))\<close> and
    ui_le: \<open>1 - (if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
             (watched_by S L ! C) !
             0 =
             L
          then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C))\<close> and
    \<open>L \<in> set (watched_l
               (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
                (watched_by S L ! C)))\<close> and
    \<open>get_conflict_l (remove_one_lit_from_wq (watched_by S L ! C) T) = None\<close>
  using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
  unit_propagation_inner_loop_body_l_inv_def
   apply -
  apply normalize_goal+
  by blast

 have L_WS: \<open>(L, twl_clause_of (get_clauses_wl S \<propto> (watched_by S L ! C))) \<in># clauses_to_update T'\<close>
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

  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S \<propto> (watched_by S L ! C))).
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
  moreover have \<open>- ?C ! ?i \<in> lits_of_l M\<close>
    using val by (auto simp: S polarity_st_def watched_by_app_def polarity_def
        access_lit_in_clauses_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  moreover have length_C: \<open>length ?C \<ge> 2\<close>
   using i_le ui_le S_T T_T'
    by (auto simp: watched_by_app_def twl_st_wl twl_st_l twl_st S)
  moreover {
    have QL: \<open>Q L ! C = hd (drop C (Q L))\<close>
      using confl C_le length_C by (auto simp: S hd_drop_conv_nth split: )
    have \<open>L \<in># mset (watched_l ?C)\<close>
      using valid confl C_le length_C S_T T_T' by (auto simp: QL S take_2_if watched_by_app_def
         twl_st_wl twl_st_l twl_st S)
    then have \<open>N \<propto> (Q L ! C) ! 0 = L \<or> N \<propto> (Q L ! C) ! 1 = L\<close>
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

lemma
  find_unwatched_get_clause_neq_L:
    \<open>False\<close> (is ?neq)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv (Some xj) (watched_by S L ! C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    eq: \<open>get_clauses_wl S \<propto> watched_by_app S L C ! xj = L\<close>
  for S C xj L
proof -
  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm A) \<longleftrightarrow> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = atms_of_mm A\<close> for A
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def by metis

  let ?C = \<open>get_clauses_wl S \<propto> watched_by_app S L C\<close>
  let ?L = \<open>get_clauses_wl S \<propto> watched_by_app S L C ! xj\<close>

  obtain T T' where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    S_T: \<open>(S, T) \<in> state_wl_l (Some (L, C))\<close> and
    \<open>L \<in># all_lits_of_mm  (mset `# init_clss_lf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close> and
    T_T': \<open>(set_clauses_to_update_l
       (clauses_to_update_l (remove_one_lit_from_wq (watched_by S L ! C) T) +
        {#watched_by S L ! C#})
       (remove_one_lit_from_wq (watched_by S L ! C) T),
      T')
     \<in> twl_st_l (Some L)\<close> and
    corr: \<open>correct_watching S\<close> and
    struct_inv: \<open>twl_struct_invs T'\<close> and
    C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and
    stgy_invs: \<open>twl_stgy_invs T'\<close> and
    in_dom: \<open>watched_by S L ! C \<in># dom_m
         (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T))\<close> and
    watched_by_ge: \<open>0 < watched_by S L ! C\<close> and
    \<open>0 < length
          (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
           (watched_by S L ! C))\<close> and
    \<open>no_dup (get_trail_l (remove_one_lit_from_wq (watched_by S L ! C) T))\<close> and
    i_le: \<open>(if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C) !
         0 =
         L
      then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C))\<close> and
    ui_le: \<open>1 - (if get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
             (watched_by S L ! C) !
             0 =
             L
          then 0 else 1)
     < length
        (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
         (watched_by S L ! C))\<close> and
    \<open>L \<in> set (watched_l
               (get_clauses_l (remove_one_lit_from_wq (watched_by S L ! C) T) \<propto>
                (watched_by S L ! C)))\<close> and
    \<open>get_conflict_l (remove_one_lit_from_wq (watched_by S L ! C) T) = None\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
      unit_propagation_inner_loop_body_l_inv_def
    apply -
    apply normalize_goal+
    by blast

  have
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of T')\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of T')\<close>
    using struct_inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    unfolding correct_watching.simps twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have in_watched: \<open>watched_by_app S L C \<in># mset (watched_by S L)\<close>
    using C_le by (auto simp: watched_by_app_def)

  have
    \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_clauses_wl S)\<close>
    using alien \<open>L \<in> snd ` D\<^sub>0\<close> lits
    by (auto simp: clauses_def mset_take_mset_drop_mset drop_Suc get_unit_clauses_wl_alt_def
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  then have
    \<open>L \<in># all_lits_of_mm (mset `# ran_mf (get_clauses_wl S) + get_unit_init_clss_wl S)\<close>
    using alien \<open>L \<in> snd ` D\<^sub>0\<close> lits S_T T_T'
    unfolding all_clss_lf_ran_m[symmetric] image_mset_union
    by (auto simp: clauses_def mset_take_mset_drop_mset drop_Suc get_unit_clauses_wl_alt_def
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        twl_st_wl twl_st_l twl_st)
  then have H: \<open>mset (watched_by S L) =
       {#x \<in># dom_m (get_clauses_wl S).
         L \<in> set (watched_l (get_clauses_wl S \<propto> x))#}\<close>
      using corr by (cases S)
          (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
         all_lits_of_mm_union)
  have L_in_watched: \<open>L \<in> set (watched_l ?C)\<close>
    using in_watched unfolding H
    by (cases S)
        (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def)
  have \<open>xj \<ge> 2\<close> and \<open>xj < length (get_clauses_wl S \<propto> watched_by_app S L C)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def
    by (cases S; auto simp: watched_by_app_def)+

  then have L_in_unwatched: \<open>L \<in> set (unwatched_l ?C)\<close>
    using eq by (auto simp: in_set_drop_conv_nth intro!: exI[of _ xj])
  have \<open>distinct_mset_mset (mset `# ran_mf (get_clauses_wl S))\<close>
    using dist S_T T_T' unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def set_append
      all_clss_lf_ran_m[symmetric] image_mset_union
    by (auto simp: mset_take_mset_drop_mset image_Un drop_Suc twl_st_wl twl_st_l twl_st)
  then have dist_C: \<open>distinct ?C\<close>
    using unit_prop_body_wl_D_invD[OF inv] by (auto simp: )
  then show False
    using L_in_watched L_in_unwatched by (cases ?C; cases \<open>tl ?C\<close>; cases \<open>tl (tl ?C)\<close>) auto
qed


definition (in isasat_input_ops) propagate_lit_wl_heur_pre where
  \<open>propagate_lit_wl_heur_pre =
     (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
       1 - i < length (get_clauses_wl_heur S \<propto> C) \<and> i \<le> 1 \<and>
       C \<in># dom_m (get_clauses_wl_heur S))\<close>

definition (in isasat_input_ops) propagate_lit_wl_heur
  :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>
where
  \<open>propagate_lit_wl_heur = (\<lambda>L' C i (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats).
      let N' = N(C \<hookrightarrow> swap (N\<propto>C) 0 (fast_minus 1 i)) in
      (Propagated L' C # M, N', D, add_mset (-L') Q, W, vm, \<phi>, clvls, cach, lbd, outl,
         incr_propagation stats))\<close>

lemma propagate_lit_wl_heur_propagate_lit_wl:
  \<open>(uncurry3 (RETURN oooo propagate_lit_wl_heur), uncurry3 (RETURN oooo propagate_lit_wl)) \<in>
  [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None \<and>
     C \<in># dom_m (get_clauses_wl S)]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow> \<langle>twl_st_heur' \<D>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def propagate_lit_wl_heur_def propagate_lit_wl_def
      vmtf_consD twl_st_heur'_def)


lemma undefined_lit_polarity_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow>
      polarity_st S L \<noteq> Some True \<and> polarity_st S L \<noteq> Some False\<close>
  by (auto simp: polarity_st_def polarity_def)

lemma find_unwatched_le_length:
  \<open>xj < length (get_clauses_wl S \<propto> watched_by_app S L C)\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close>
  for S L C xj
  using that unfolding find_unwatched_wl_st_def find_unwatched_l_def
  by (cases S) auto

lemma find_unwatched_in_D\<^sub>0: \<open>get_clauses_wl S \<propto> watched_by_app S L C ! xj \<in> snd ` D\<^sub>0\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof -
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover {
    have xj: \<open>xj < length (get_clauses_wl S \<propto> watched_by_app S L C)\<close>
      using find_unw by (cases S) (auto simp: find_unwatched_wl_st_def find_unwatched_l_def)
    have \<open>watched_by_app S L C \<in># dom_m (get_clauses_wl S)\<close> \<open>watched_by_app S L C > 0\<close>
      using inv by (blast intro: unit_prop_body_wl_D_invD)+
    then have \<open>get_clauses_wl S \<propto> watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (mset `# ran_mf (get_clauses_wl S))\<close>
      using xj
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset
          in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def nth_in_set_tl
          intro!: bexI[of _ \<open>the (fmlookup (get_clauses_wl S)(watched_by_app S L C))\<close>])
    then have \<open>get_clauses_wl S \<propto> watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (mset `# ran_mf (get_clauses_wl S))\<close>
      unfolding mset_append
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset'
          all_lits_of_mm_union drop_Suc) }
  ultimately show ?thesis
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
    by (auto simp: all_lits_of_mm_union)
qed

definition (in isasat_input_ops) unit_prop_body_wl_heur_inv where
  \<open>unit_prop_body_wl_heur_inv S w L \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_inv S' w L)\<close>

definition (in isasat_input_ops) unit_prop_body_wl_D_find_unwatched_heur_inv where
  \<open>unit_prop_body_wl_D_find_unwatched_heur_inv f C S \<longleftrightarrow>
     (\<exists>S'. (S, S') \<in> twl_st_heur \<and> unit_prop_body_wl_D_find_unwatched_inv f C S')\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_body_wl_heur
   :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>unit_propagation_inner_loop_body_wl_heur L w S = do {
      ASSERT(unit_prop_body_wl_heur_inv S w L);
      ASSERT(watched_by_app_heur_pre ((S, L), w));
      let C = watched_by_app_heur S L w;
      ASSERT(access_lit_in_clauses_heur_pre ((S, C), 0));
      let i = (if access_lit_in_clauses_heur S C 0 = L then 0 else 1);
      ASSERT(access_lit_in_clauses_heur_pre ((S, C), 1 - i));
      let L' = access_lit_in_clauses_heur S C (1 - i);
      ASSERT(polarity_st_pre (S, L'));
      let val_L' = polarity_st_heur S L';
      if val_L' = Some True
      then RETURN (w+1, S)
      else do {
        ASSERT(find_unwatched_wl_st_heur_pre (S, C));
        f \<leftarrow> find_unwatched_wl_st_heur S C;
        ASSERT (unit_prop_body_wl_D_find_unwatched_heur_inv f C S);
        case f of
          None \<Rightarrow>
            if val_L' = Some False
            then do {
              ASSERT(set_conflict_wl_heur_pre (C, S));
              S \<leftarrow> set_conflict_wl_heur C S;
              RETURN (w+1, S)}
            else do {
              ASSERT(propagate_lit_wl_heur_pre (((L', C), i), S));
              let S = propagate_lit_wl_heur L' C i S;
              RETURN (w+1, S)}
        | Some f \<Rightarrow> do {
            ASSERT(update_clause_wl_code_pre (((((L, C), w), i), f), S));
            update_clause_wl_heur L C w i f S
          }
      }
   }\<close>

lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>get_clauses_wl_heur S = get_clauses_wl S'\<close>
     \<open>get_trail_wl_heur S = get_trail_wl S'\<close> and
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> watched_by_int S C = watched_by S' C\<close> and
     \<open>get_conflict_wl_heur S = get_conflict_wl S'\<close> and
     \<open>literals_to_update_wl_heur S = literals_to_update_wl S'\<close>
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def)

lemma twl_st_heur_literals_are_in_\<L>\<^sub>i\<^sub>n_heur:
  assumes lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S'\<close> and SS': \<open>(S, S') \<in> twl_st_heur\<close>
  shows
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S\<close>
  using SS' unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_def
   literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def
   lits[unfolded is_\<L>\<^sub>a\<^sub>l\<^sub>l_def]
  by (auto simp: twl_st_heur_state_simp all_lits_of_mm_union
    simp del: twl_st_of_wl.simps)

ML \<open>
signature MORE_REFINEMENT = sig
  val down_converse: Proof.context -> thm -> thm
end

structure More_Refinement: MORE_REFINEMENT = struct
  val unfold_refine = (fn context => Local_Defs.unfold (context)
   @{thms refine_rel_defs nres_rel_def in_pair_collect_simp fref_def})
  val unfold_Ball = (fn context => Local_Defs.unfold (context)
    @{thms Ball2_split_def all_to_meta})
  val replace_ALL_by_meta = (fn context => fn thm => Object_Logic.rulify context thm)
  val down_converse = (fn context =>
    replace_ALL_by_meta context o (unfold_Ball context) o (unfold_refine context))
end
\<close>
attribute_setup "to_\<Down>" = \<open>
    Scan.succeed (Thm.rule_attribute [] (More_Refinement.down_converse o Context.proof_of))
  \<close> "convert theorem from @{text \<rightarrow>}-form to @{text \<Down>}-form."

method "to_\<Down>" =
   (unfold refine_rel_defs nres_rel_def in_pair_collect_simp fref_def uncurry_def;
   unfold Ball2_split_def all_to_meta fref_def uncurry_def;
   intro allI impI)



lemma set_conflict_wl_heur_set_conflict_wl':
  \<open>(uncurry set_conflict_wl_heur, uncurry (RETURN oo set_conflict_wl')) \<in>
    nat_rel \<times>\<^sub>r twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  unfolding set_conflict_wl_heur_def uncurry_def Let_def set_conflict_m_def RES_RETURN_RES4
  by (auto simp: twl_st_heur_def set_conflict_wl_heur_def set_conflict_wl'_def
        RETURN_def counts_maximum_level_def twl_st_heur'_def
      intro!: RES_refine)

lemma in_Id_in_Id_option_rel[refine]:
  \<open>(f, f') \<in> Id \<Longrightarrow> (f, f') \<in> \<langle>Id\<rangle> option_rel\<close>
  by auto

lemma unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D:
  \<open>(uncurry2 unit_propagation_inner_loop_body_wl_heur, uncurry2 unit_propagation_inner_loop_body_wl_D)
   \<in> Id \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>unit_prop_body_wl_D_inv T i L \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> for T i L
    unfolding unit_prop_body_wl_D_inv_def by auto
  have pol_undef: \<open>polarity M L \<noteq> Some True \<Longrightarrow> polarity M L \<noteq> Some False \<Longrightarrow> defined_lit M L \<Longrightarrow>
     False\<close>
    for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (auto simp: polarity_def split: if_splits)
  have 1: \<open>RETURN (w + 1, f S') = do {S \<leftarrow> RETURN (f S'); RETURN (w + 1, S)}\<close>
    for w :: nat and S' and f
    by auto
  have watched_by_app_heur_pre: \<open>unit_prop_body_wl_heur_inv x2c x2b x1c \<Longrightarrow>
      watched_by_app_heur_pre ((x2c, x1c), x2b)\<close>
    for x2c x2b x1c
    by (auto simp: unit_prop_body_wl_heur_inv_def watched_by_app_heur_pre_def
        unit_prop_body_wl_D_inv_def twl_st_heur_def unit_prop_body_wl_inv_def
        map_fun_rel_def)
  have access_lit_in_clauses_heur_pre: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D> \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    y = (x1, x2a) \<Longrightarrow>
    x1b = (x1c, x2b) \<Longrightarrow>
    x = (x1b, x2c) \<Longrightarrow>
    unit_prop_body_wl_D_inv x2a x2 x1a \<Longrightarrow>
       access_lit_in_clauses_heur_pre ((x2c, watched_by_int x2c x1c ! x2b), 0)\<close>
    for x2c x2b x1c x y x1 x1a x2 x2a x1b
    using unit_prop_body_wl_D_invD[of x2a x2 x1a]
    by (auto simp:  access_lit_in_clauses_heur_pre_def twl_st_heur'_def
        twl_st_heur_state_simp length_rll_def watched_by_app_def)
  have access_lit_in_clauses_heur_pre2: \<open>(x, y)
    \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
       twl_st_heur' \<D> \<Longrightarrow>
    x1 = (x1a, x2) \<Longrightarrow>
    y = (x1, x2a) \<Longrightarrow>
    x1b = (x1c, x2b) \<Longrightarrow>
    x = (x1b, x2c) \<Longrightarrow>
    unit_prop_body_wl_D_inv x2a x2 x1a \<Longrightarrow>
    access_lit_in_clauses_heur_pre ((x2c, watched_by_int x2c x1c ! x2b),
      1 - (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 = x1c then 0 else 1))\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c
    using unit_prop_body_wl_D_invD[of x2a x2 x1a]
    by (auto simp:  access_lit_in_clauses_heur_pre_def twl_st_heur'_def
        twl_st_heur_state_simp length_rll_def watched_by_app_def)
  have in_D0: \<open>x2d \<in> snd ` D\<^sub>0\<close>
  if
    \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
    \<open>x1 = (x1a, x2)\<close> and
    \<open>y = (x1, x2a)\<close> and
    \<open>x1b = (x1c, x2b)\<close> and
    \<open>x = (x1b, x2c)\<close> and
    inv': \<open>unit_prop_body_wl_D_inv x2a x2 x1a\<close> and
    \<open>unit_prop_body_wl_heur_inv x2c x2b x1c\<close> and
    \<open>(x2c,
      get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
      (1 - (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 =
               x1c
            then 0 else 1))) =
     (x1d, x2d)\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c x1d x2d
    using unit_prop_body_wl_D_invD(5-6)[OF inv'] that
    by (auto simp: image_image twl_st_heur_def map_fun_rel_def watched_by_app_def
        twl_st_heur'_def)

  have find_unwatched_wl_st_heur_pre:
    \<open>find_unwatched_wl_st_heur_pre (x2c, watched_by_int x2c x1c ! x2b)\<close>
  if
    xy: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
    st:
      \<open>x1 = (x1a, x2)\<close>
      \<open>y = (x1, x2a)\<close>
      \<open>x1b = (x1c, x2b)\<close>
      \<open>x = (x1b, x2c)\<close> and
    inv': \<open>unit_prop_body_wl_D_inv x2a x2 x1a\<close>
  for x y x1 x1a x2 x2a x1b x1c x2b x2c
  proof -
    have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur x2c\<close> and
       heur: \<open>(x2c, x2a) \<in> twl_st_heur\<close>
      apply (rule twl_st_heur_literals_are_in_\<L>\<^sub>i\<^sub>n_heur[of x2a])
      using inv' xy unfolding st twl_st_heur'_def
      by (auto simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        simp del: twl_st_of_wl.simps)
    with clss_size_uint64_max[of \<open>mset (get_clauses_wl x2a \<propto> (watched_by x2a x1a ! x2))\<close>]
    show ?thesis
      using unit_prop_body_wl_D_invD[OF inv'] that heur
      unfolding find_unwatched_wl_st_heur_pre_def watched_by_app_def
      by (simp add: twl_st_heur_state_simp image_image
          twl_st_heur_state_simp_watched[OF heur])
  qed
  have set_conflict_wl_heur_pre: \<open>set_conflict_wl_heur_pre (watched_by_int x2c x1c ! x2b, x2c)\<close>
    if
      xy: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      st:
      \<open>x1 = (x1a, x2)\<close>
      \<open>y = (x1, x2a)\<close>
      \<open>x1b = (x1c, x2b)\<close>
      \<open>x = (x1b, x2c)\<close> and
      inv': \<open>unit_prop_body_wl_D_inv x2a x2 x1a\<close> and
      \<open>unit_prop_body_wl_heur_inv x2c x2b x1c\<close> and
      find_unw: \<open>find_unwatched_wl_st_heur_pre (x2c, watched_by_int x2c x1c ! x2b)\<close> and
      \<open>(f, fa) \<in> Id\<close> and
      find_unw': \<open>unit_prop_body_wl_D_find_unwatched_inv fa (watched_by x2a x1a ! x2)
      x2a\<close> and
      f: \<open>f = None\<close> \<open>fa = None\<close> and
      pol: \<open>polarity (get_trail_wl_heur x2c)
      (get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
       (1 - (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 =
                x1c
             then 0 else 1))) =
     Some False\<close>
      \<open>polarity (get_trail_wl x2a)
      (get_clauses_wl x2a \<propto> (watched_by x2a x1a ! x2) !
       (1 - (if get_clauses_wl x2a \<propto> (watched_by x2a x1a ! x2) ! 0 = x1a then 0
             else 1))) =
     Some False\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c f fa
  proof -
    have [simp]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur x2c\<close> and
       heur: \<open>(x2c, x2a) \<in> twl_st_heur\<close> and
       lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x2a\<close>
      apply (rule twl_st_heur_literals_are_in_\<L>\<^sub>i\<^sub>n_heur[of x2a])
      using inv' xy unfolding st twl_st_heur'_def
      by (auto simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        simp del: twl_st_of_wl.simps)
    have [simp]: \<open>x1c \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and \<open>get_conflict_wl x2a = None\<close>
      using inv' xy unfolding st
      by (auto simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        simp del: twl_st_of_wl.simps)
    have \<open>\<not> tautology (mset (get_clauses_wl x2a \<propto> watched_by_app x2a x1a x2))\<close>
      apply (rule find_unwatched_not_tauto[OF _ inv'])
      using that by (auto simp: twl_st_heur_state_simp_watched[OF heur]
        watched_by_app_def access_lit_in_clauses_def polarity_st_def split: if_splits)
    moreover have \<open>no_dup (get_trail_wl x2a)\<close>
      using xy by (auto simp: st twl_st_heur_def twl_st_heur'_def)
    moreover have \<open>out_learned (get_trail_wl x2a) None (get_outlearned_heur x2c)\<close>
      using heur \<open>get_conflict_wl x2a = None\<close> unfolding twl_st_heur_def by auto
    ultimately show ?thesis
      using unit_prop_body_wl_D_invD[OF inv']  that
      unfolding set_conflict_wl_heur_pre_def find_unwatched_wl_st_heur_pre_def
      by (auto simp: twl_st_heur_state_simp twl_st_heur_state_simp_watched[OF heur]
        watched_by_app_def twl_st_heur'_def)
  qed
  have propagate_lit_wl_heur_pre: \<open>propagate_lit_wl_heur_pre
       (((get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
          (1 - (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 = x1c
             then 0 else 1)), watched_by_int x2c x1c ! x2b),
         if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 = x1c then 0 else 1), x2c)\<close>
    if
      xy: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      st: \<open>x1 = (x1a, x2)\<close>
        \<open>y = (x1, x2a)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x = (x1b, x2c)\<close> and
      inv': \<open>unit_prop_body_wl_D_inv x2a x2 x1a\<close> and
      \<open>polarity_st_pre (x2c,
       get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
       (1 -
        (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
            0 =
            x1c
         then 0 else 1)))\<close> and
      \<open>polarity (get_trail_wl_heur x2c)
      (get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
       (1 -
        (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
            0 =
            x1c
         then 0 else 1))) \<noteq>
     Some True\<close> and
    \<open>polarity (get_trail_wl_heur x2c)
      (get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
       (1 -
        (if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) !
            0 =
            x1c
         then 0 else 1))) \<noteq>
     Some False\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c
    using unit_prop_body_wl_D_invD[OF inv'] that
    unfolding propagate_lit_wl_heur_pre_def
    by (auto simp: twl_st_heur_state_simp twl_st_heur_state_simp_watched[OF ]
        watched_by_app_def polarity_def twl_st_heur'_def split: if_splits)

  have update_clause_wl_code_pre:
     \<open>update_clause_wl_code_pre (((((x1c, watched_by_int x2c x1c ! x2b), x2b),
        if get_clauses_wl_heur x2c \<propto> (watched_by_int x2c x1c ! x2b) ! 0 = x1c
          then 0 else 1), k), x2c)\<close>
    if
      xy: \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      st:
        \<open>x1 = (x1a, x2)\<close>
        \<open>y = (x1, x2a)\<close>
        \<open>x1b = (x1c, x2b)\<close>
        \<open>x = (x1b, x2c)\<close> and
      inv': \<open>unit_prop_body_wl_D_inv x2a x2 x1a\<close> and
      \<open>(f, fa) \<in> Id\<close> and
      unw: \<open>unit_prop_body_wl_D_find_unwatched_inv fa (watched_by x2a x1a ! x2) x2a\<close> and
      f: \<open>f = Some k\<close> \<open>fa = Some k'\<close>
    for x y x1 x1a x2 x2a x1b x1c x2b x2c f fa k k'
  proof -
    have [intro!]: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> nat_of_lit L < length (get_watched_wl_heur x2c)\<close> for L
      using unit_prop_body_wl_D_invD[OF inv'] xy unfolding st twl_st_heur'_def
      by (auto simp: twl_st_heur_def map_fun_rel_def watched_by_app_def)
    have [simp]: \<open>x2 < length (get_watched_wl_heur x2c ! nat_of_lit x1a)\<close>
      using unit_prop_body_wl_D_invD(1,7)[OF inv'] xy unfolding st twl_st_heur'_def
      by (auto simp: twl_st_heur_def map_fun_rel_def)
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl x2a \<propto> (watched_by x2a x1a ! x2)))\<close>
      using unit_prop_body_wl_D_invD(11)[OF inv'] unfolding watched_by_app_def .
    then have [simp]: \<open>get_clauses_wl x2a \<propto> (watched_by x2a x1a ! x2) ! k' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
      using unw f
      unfolding update_clause_wl_code_pre_def unit_prop_body_wl_D_find_unwatched_inv_def
      by (auto simp: twl_st_heur_state_simp twl_st_heur_state_simp_watched
        watched_by_app_def)
    show ?thesis
      using unit_prop_body_wl_D_invD[OF inv'] that
      unfolding update_clause_wl_code_pre_def unit_prop_body_wl_D_find_unwatched_inv_def
      by (auto simp: twl_st_heur_state_simp watched_by_app_def twl_st_heur'_def)
  qed
  note find_unw = find_unwatched_wl_st_heur_find_unwatched_wl_s[THEN fref_to_Down_curry]
      set_conflict_wl_heur_set_conflict_wl'[of \<D>, THEN fref_to_Down_curry, unfolded comp_def]
      propagate_lit_wl_heur_propagate_lit_wl[of \<D>, THEN fref_to_Down_curry3, unfolded comp_def]
      update_clause_wl_heur_update_clause_wl[of \<D>, THEN fref_to_Down_curry5, unfolded comp_def]
  show ?thesis
    supply [[goals_limit=1]] twl_st_heur'_def[simp]
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (intro frefI nres_relI)
    unfolding unit_propagation_inner_loop_body_wl_heur_def unit_propagation_inner_loop_body_wl_D_def
      uncurry_def find_unwatched_l_find_unwatched_wl_s 1 polarity_st_heur_def
      watched_by_app_heur_def access_lit_in_clauses_heur_def
    unfolding set_conflict_wl'_alt_def[symmetric]
    apply (refine_rcg find_unw)
    subgoal unfolding unit_prop_body_wl_heur_inv_def twl_st_heur'_def by fastforce
    subgoal by (rule watched_by_app_heur_pre)
    subgoal by (rule access_lit_in_clauses_heur_pre)
    subgoal by (rule access_lit_in_clauses_heur_pre2)
    subgoal by (rule in_D0)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by auto
    subgoal by (rule find_unwatched_wl_st_heur_pre)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          find_unwatched_wl_st_heur_pre_def
          find_unwatched_wl_st_pre_def)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal for x y x1 x1a x2 x2a x1b x1c x2b x2c f fa
      unfolding unit_prop_body_wl_D_find_unwatched_heur_inv_def
      by (rule exI[of _ x2a])
         (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (rule set_conflict_wl_heur_pre)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (rule propagate_lit_wl_heur_pre)
    subgoal by (auto simp: twl_st_heur_state_simp split: if_splits dest!: pol_undef)
    subgoal by (auto simp: twl_st_heur_state_simp unit_prop_body_wl_D_inv_def
          unit_prop_body_wl_inv_def)
    subgoal by (auto simp: twl_st_heur_state_simp access_lit_in_clauses_heur_pre_def)
    subgoal by (auto simp: twl_st_heur_state_simp)
    subgoal by (auto simp: twl_st_heur_state_simp watched_by_app_def
          intro!: find_unwatched_get_clause_neq_L)
    subgoal by (rule update_clause_wl_code_pre)
    subgoal by (auto simp: twl_st_heur_state_simp access_lit_in_clauses_heur_pre_def)
    subgoal by (auto simp: twl_st_heur_state_simp watched_by_app_def
           intro!: find_unwatched_get_clause_neq_L)
    subgoal by (auto simp: twl_st_heur_state_simp)
    done
qed

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur_inv where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L =
   (\<lambda>(w, S'). \<exists>S. (S', S) \<in> twl_st_heur \<and> unit_propagation_inner_loop_wl_loop_D_inv L (w, S) \<and>
        L \<in> snd ` D\<^sub>0 \<and> dom_m (get_clauses_wl_heur S') = dom_m (get_clauses_wl_heur S\<^sub>0))\<close>

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_loop_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (nat \<times> twl_st_wl_heur) nres\<close>
where
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(w, S). w < length (watched_by_int S L) \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(w, S). do {
        unit_propagation_inner_loop_body_wl_heur L w S
      })
      (0, S\<^sub>0)
  }\<close>

(* TODO Move *)
lemma get_conflict_wl_is_None_heur_alt_def:
   \<open>get_conflict_wl_is_None_heur S = (get_conflict_wl_heur S = None)\<close>
  by (auto simp: get_conflict_wl_is_None_heur_def split: option.splits)
(* End Move *)

lemma unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D:
  \<open>(uncurry unit_propagation_inner_loop_wl_loop_D_heur,
       uncurry unit_propagation_inner_loop_wl_loop_D)
   \<in> Id \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<rangle>nres_rel\<close>
proof -
  have unit_propagation_inner_loop_wl_loop_D_heur_inv:
   \<open>unit_propagation_inner_loop_wl_loop_D_heur_inv x2a x1a xa\<close>
    if
      \<open>(x, y) \<in> nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close> and
      \<open>(xa, x') \<in> nat_rel \<times>\<^sub>f twl_st_heur' \<D>\<close> and
      H: \<open>unit_propagation_inner_loop_wl_loop_D_inv x1 x'\<close>
    for x y x1 x2 x1a x2a xa x'
  proof -
    obtain w S w' S' where
      xa: \<open>xa = (w, S)\<close> and x': \<open>x' = (w', S')\<close>
      by (cases xa; cases x') auto
    show ?thesis
      unfolding xa unit_propagation_inner_loop_wl_loop_D_heur_inv_def prod.case
      apply (rule exI[of _ S'])
      using that xa x' that
      unfolding unit_propagation_inner_loop_wl_loop_D_inv_def twl_st_heur'_def
      by auto
  qed
  note H[refine] = unit_propagation_inner_loop_body_wl_heur_unit_propagation_inner_loop_body_wl_D
     [THEN fref_to_Down_curry2']
  show ?thesis
    unfolding unit_propagation_inner_loop_wl_loop_D_heur_def
      unit_propagation_inner_loop_wl_loop_D_def uncurry_def
      unit_propagation_inner_loop_wl_loop_D_inv_def[symmetric]
    apply (intro frefI nres_relI)
    apply (refine_vcg)
    subgoal by auto
    subgoal by (rule unit_propagation_inner_loop_wl_loop_D_heur_inv)
    subgoal by (auto simp: get_conflict_wl_is_None_heur_alt_def twl_st_heur'_def
          twl_st_heur_state_simp unit_propagation_inner_loop_wl_loop_D_inv_def
          split: option.splits)
    subgoal by auto
    done
qed

definition (in isasat_input_ops) unit_propagation_inner_loop_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>unit_propagation_inner_loop_wl_D_heur L S\<^sub>0 = do {
     wS \<leftarrow> unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0;
     RETURN (snd wS)
  }\<close>

lemma unit_propagation_inner_loop_wl_D_heur_unit_propagation_inner_loop_wl_D:
  \<open>(uncurry unit_propagation_inner_loop_wl_D_heur, uncurry unit_propagation_inner_loop_wl_D) \<in>
    nat_lit_lit_rel \<times>\<^sub>f twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D>\<rangle> nres_rel\<close>
  unfolding unit_propagation_inner_loop_wl_D_heur_def
    unit_propagation_inner_loop_wl_D_def uncurry_def
    apply (intro frefI nres_relI)
  apply (refine_vcg
      unit_propagation_inner_loop_wl_loop_D_heur_unit_propagation_inner_loop_wl_loop_D[THEN fref_to_Down_curry])
  by auto

definition (in isasat_input_ops)  select_and_remove_from_literals_to_update_wl_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal) nres\<close>
where
  \<open>select_and_remove_from_literals_to_update_wl_heur S = SPEC(\<lambda>(S', L).
        L \<in># literals_to_update_wl_heur S \<and>
     S' = set_literals_to_update_wl_heur (literals_to_update_wl_heur S - {#L#}) S)\<close>

definition (in isasat_input_ops) unit_propagation_outer_loop_wl_D_heur_inv
 :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0 S' \<longleftrightarrow>
     (\<exists>S. (S', S) \<in> twl_st_heur \<and> unit_propagation_outer_loop_wl_D_inv S \<and>
       dom_m (get_clauses_wl_heur S') = dom_m (get_clauses_wl_heur S\<^sub>0))\<close>

definition (in isasat_input_ops) unit_propagation_outer_loop_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>unit_propagation_outer_loop_wl_D_heur S\<^sub>0 =
    WHILE\<^sub>T\<^bsup>unit_propagation_outer_loop_wl_D_heur_inv S\<^sub>0\<^esup>
      (\<lambda>S. literals_to_update_wl_heur S \<noteq> {#})
      (\<lambda>S. do {
        ASSERT(literals_to_update_wl_heur S \<noteq> {#});
        (S', L) \<leftarrow> select_and_remove_from_literals_to_update_wl_heur S;
        unit_propagation_inner_loop_wl_D_heur L S'
      })
      S\<^sub>0\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(select_and_remove_from_literals_to_update_wl_heur, select_and_remove_from_literals_to_update_wl) \<in>
   twl_st_heur' \<D> \<rightarrow>\<^sub>f \<langle>twl_st_heur' \<D> \<times>\<^sub>f nat_lit_lit_rel\<rangle> nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
    select_and_remove_from_literals_to_update_wl_def
  by (intro frefI nres_relI)
    (auto intro!: RES_refine simp: twl_st_heur_def twl_st_heur'_def)

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
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur' (dom_m (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed

theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D:
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl_D) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>
  using twl_st_heur'D_twl_st_heurD[OF unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D']
  .
end

end
