theory IsaSAT_LBD
  imports IsaSAT_Setup
begin

definition mark_lbd_from_clause_heur :: \<open>trail_pol \<Rightarrow> arena \<Rightarrow> nat \<Rightarrow> lbd \<Rightarrow> lbd nres\<close> where
  \<open>mark_lbd_from_clause_heur M N C lbd = do {
  n \<leftarrow> mop_arena_length N C;
  nfoldli [1..<n] (\<lambda>_. True)
    (\<lambda>i lbd. do {
       L \<leftarrow> mop_arena_lit2 N C i;
       ASSERT(get_level_pol_pre (M, L));
       let lev = get_level_pol M L;
       ASSERT(lev \<le> Suc (unat32_max div 2));
       RETURN (if lev = 0 then lbd else lbd_write lbd lev)})
    lbd}\<close>

lemma count_decided_le_length: \<open>count_decided M \<le> length M\<close>
  unfolding count_decided_def by (rule length_filter_le)

lemma mark_lbd_from_clause_heur_correctness:
  assumes \<open>(M, M') \<in> trail_pol \<A>\<close> and \<open>valid_arena N N' vdom\<close> \<open>C \<in># dom_m N'\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N' \<propto> C))\<close>
  shows \<open>mark_lbd_from_clause_heur M N C lbd \<le> \<Down> Id (SPEC(\<lambda>_::bool list. True))\<close>
  using assms
  unfolding mark_lbd_from_clause_heur_def
  apply (refine_vcg mop_arena_length[THEN fref_to_Down_curry, THEN order_trans, of N' C _ _ vdom]
        nfoldli_rule[where I = \<open> \<lambda>_ _ _. True\<close>])
  subgoal by auto
  subgoal by auto
  unfolding Down_id_eq comp_def
  apply (refine_vcg mop_arena_length[THEN fref_to_Down_curry, THEN order_trans, of N' C _ _ vdom]
        nfoldli_rule[where I = \<open> \<lambda>_ _ _. True\<close>] mop_arena_lit[THEN order_trans])
  subgoal by auto
  apply assumption+
  subgoal by simp
  apply auto[]
  subgoal H
    by (metis append_cons_eq_upt(2) eq_upt_Cons_conv)
  subgoal for x l1 l2 \<sigma> xa using H[of l1 x l2] apply -
    by (auto intro!: get_level_pol_pre  literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
  subgoal for x l1 l2 \<sigma> xa using H[of l1 x l2] apply -
    using count_decided_ge_get_level[of M' xa] count_decided_le_length[of M']
    by (auto simp: trail_pol_alt_def literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l simp flip: get_level_get_level_pol)
  done

definition calculate_LBD_st :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clauses_l nres\<close> where
  \<open>calculate_LBD_st = (\<lambda>M N C. RETURN N)\<close>

abbreviation TIER_TWO_MAXIMUM where
  \<open>TIER_TWO_MAXIMUM \<equiv> 6\<close>

abbreviation TIER_ONE_MAXIMUM where
  \<open>TIER_ONE_MAXIMUM \<equiv> 2\<close>

definition calculate_LBD_heur_st :: \<open>_ \<Rightarrow> arena \<Rightarrow> lbd \<Rightarrow> nat \<Rightarrow> (arena \<times> lbd) nres\<close> where
  \<open>calculate_LBD_heur_st = (\<lambda>M N lbd C. do{
     old_glue \<leftarrow> mop_arena_lbd N C;
     st \<leftarrow> mop_arena_status N C;
     if st = IRRED then RETURN (N, lbd)
     else if old_glue < TIER_TWO_MAXIMUM then do {
       N \<leftarrow> mop_arena_mark_used2 N C;
       RETURN (N, lbd)
     }
     else do {
       lbd \<leftarrow> mark_lbd_from_clause_heur M N C lbd;
       glue \<leftarrow> get_LBD lbd;
       lbd \<leftarrow> lbd_empty lbd;
       N \<leftarrow> (if glue < old_glue then mop_arena_update_lbd C glue N else RETURN N);
       N \<leftarrow> (if glue < TIER_TWO_MAXIMUM \<or> old_glue < TIER_TWO_MAXIMUM then mop_arena_mark_used2 N C else mop_arena_mark_used N C);
       RETURN (N, lbd)
    }})\<close>


lemma calculate_LBD_st_alt_def:
  \<open>calculate_LBD_st = (\<lambda>M N C. do {
      old_glue :: nat \<leftarrow> SPEC(\<lambda>_ . True);
      st :: clause_status \<leftarrow> SPEC(\<lambda>_ . True);
      if st = IRRED then RETURN N
      else if old_glue < 6 then  do {
         _ \<leftarrow> RETURN N;
         RETURN N
      }
      else do {
       lbd::bool list \<leftarrow> SPEC(\<lambda>_. True);
       glue::nat \<leftarrow> get_LBD lbd;
       _::bool list \<leftarrow> lbd_empty lbd;
       _ \<leftarrow> RETURN N;
       _ \<leftarrow> RETURN N;
      RETURN N
    }})\<close> (is \<open>?A = ?B\<close>)
  unfolding calculate_LBD_st_def get_LBD_def lbd_empty_def
  by (auto intro!: ext rhs_step_bind_RES split: if_splits cong: if_cong)


(* TODO Move *)
lemma RF_COME_ON: \<open>(x, y) \<in> Id \<Longrightarrow> f x \<le> \<Down> Id (f y)\<close>
  by auto

lemma mop_arena_update_lbd:
  \<open>C \<in># dom_m N \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
     mop_arena_update_lbd C glue arena \<le> SPEC(\<lambda>c. (c, N) \<in> {(c, N'). N'=N \<and> valid_arena c N vdom \<and>
       length c = length arena})\<close>
  unfolding mop_arena_update_lbd_def
  by (auto simp: update_lbd_pre_def arena_is_valid_clause_idx_def
    intro!: ASSERT_leI valid_arena_update_lbd)

lemma mop_arena_mark_used_valid:
  \<open>C \<in># dom_m N \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
     mop_arena_mark_used arena C \<le> SPEC(\<lambda>c. (c, N) \<in> {(c, N'). N'=N \<and> valid_arena c N vdom \<and>
       length c = length arena})\<close>
  unfolding mop_arena_mark_used_def
  by (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def
    intro!: ASSERT_leI valid_arena_mark_used)

lemma mop_arena_mark_used2_valid:
  \<open>C \<in># dom_m N \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
     mop_arena_mark_used2 arena C \<le> SPEC(\<lambda>c. (c, N) \<in> {(c, N'). N'=N \<and> valid_arena c N vdom \<and>
       length c = length arena})\<close>
  unfolding mop_arena_mark_used2_def
  by (auto simp: arena_act_pre_def arena_is_valid_clause_idx_def
    intro!: ASSERT_leI valid_arena_mark_used2)

abbreviation twl_st_heur_conflict_ana'
  :: \<open>nat \<Rightarrow> clss_size \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
  \<open>twl_st_heur_conflict_ana' r lcount \<equiv> {(S, T). (S, T) \<in> twl_st_heur_conflict_ana \<and>
     length (get_clauses_wl_heur S) = r \<and> get_learned_count S = lcount}\<close>

lemma calculate_LBD_heur_st_calculate_LBD_st:
  assumes \<open>valid_arena arena N vdom\<close>
    \<open>(M, M') \<in> trail_pol \<A>\<close>
    \<open>C \<in># dom_m N\<close>
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (N \<propto> C))\<close> \<open>(C, C') \<in> nat_rel\<close>
  shows \<open>calculate_LBD_heur_st M arena lbd C \<le>
     \<Down>{((arena', lbd), N'). valid_arena arena' N' vdom \<and> N = N' \<and> length arena = length arena'}
       (calculate_LBD_st M' N C')\<close>
proof -
  have WTF: \<open>(a, b) \<in> R \<Longrightarrow>  b=b' \<Longrightarrow> (a, b') \<in> R\<close> for a a' b b' R
    by auto
  show ?thesis
    using assms
    unfolding calculate_LBD_heur_st_def calculate_LBD_st_alt_def
    apply (refine_vcg mark_lbd_from_clause_heur_correctness[of _ M'
       \<A> _ N vdom]
      mop_arena_update_lbd[of _ _ _ vdom]
      mop_arena_mark_used_valid[of _ N _ vdom]
      mop_arena_mark_used2_valid[of _ N _ vdom])
    subgoal
      unfolding twl_st_heur_conflict_ana_def
      by (auto simp: mop_arena_lbd_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
        intro!: ASSERT_leI exI[of _ N] exI[of _ vdom])
    subgoal
      unfolding twl_st_heur_conflict_ana_def
      by (auto simp: mop_arena_status_def arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
        intro!: ASSERT_leI exI[of _ N] exI[of _ vdom])
    subgoal
      by (auto simp: twl_st_heur_conflict_ana_def RETURN_RES_refine_iff)
    subgoal
      by (auto simp: twl_st_heur_conflict_ana_def RETURN_RES_refine_iff)
    subgoal
      by (auto simp: twl_st_heur_conflict_ana_def RETURN_RES_refine_iff)
    subgoal
      by (force simp: twl_st_heur_conflict_ana_def)
    apply (rule RF_COME_ON)
    subgoal
      by auto
    apply (rule RF_COME_ON)
    subgoal
      by auto
    subgoal
      unfolding twl_st_heur_conflict_ana_def
      by (auto simp: mop_arena_lbd_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
        intro!: ASSERT_leI exI[of _ \<open>get_clauses_wl (fst y)\<close>] exI[of _ \<open>set (get_vdom (fst x))\<close>])
    subgoal
      by (force simp: twl_st_heur_conflict_ana_def)
    subgoal
      by (force simp: twl_st_heur_conflict_ana_def)
    subgoal
      by (force simp: twl_st_heur_conflict_ana_def)
   done
qed


definition mark_lbd_from_list :: \<open>_\<close> where
  \<open>mark_lbd_from_list M C lbd = do {
    nfoldli (drop 1 C) (\<lambda>_. True)
      (\<lambda>L lbd. RETURN (lbd_write lbd (get_level M L))) lbd
  }\<close>

definition mark_lbd_from_list_heur :: \<open>trail_pol \<Rightarrow> nat clause_l \<Rightarrow> lbd \<Rightarrow> lbd nres\<close> where
  \<open>mark_lbd_from_list_heur M C lbd = do {
  let n = length C;
  nfoldli [1..<n] (\<lambda>_. True)
    (\<lambda>i lbd. do {
       ASSERT(i < length C);
       let L = C ! i;
       ASSERT(get_level_pol_pre (M, L));
       let lev = get_level_pol M L;
       ASSERT(lev \<le> Suc (unat32_max div 2));
       RETURN (if lev = 0 then lbd else lbd_write lbd lev)})
    lbd}\<close>

definition mark_lbd_from_conflict :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_lbd_from_conflict = (\<lambda>S. do{
     lbd \<leftarrow> mark_lbd_from_list_heur (get_trail_wl_heur S) (get_outlearned_heur S) (get_lbd S);
     RETURN (set_lbd_wl_heur lbd S)
    })\<close>


lemma mark_lbd_from_list_heur_correctness:
  assumes \<open>(M, M') \<in> trail_pol \<A>\<close> and \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset (tl C))\<close>
  shows \<open>mark_lbd_from_list_heur M C lbd \<le> \<Down> Id (SPEC(\<lambda>_::bool list. True))\<close>
  using assms
  unfolding mark_lbd_from_list_heur_def
  apply (refine_vcg nfoldli_rule[where I = \<open>\<lambda>_ _ _. True\<close>])
  subgoal by auto
  subgoal
    by (auto simp: upt_eq_lel_conv nth_tl)
  subgoal for x l1 l2 \<sigma>
    using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>tl C\<close> \<open>x - 1\<close>]
    by (auto intro!: get_level_pol_pre  simp: upt_eq_lel_conv nth_tl)
  subgoal for x l1 l2 \<sigma>
    using count_decided_ge_get_level[of M' \<open>C ! x\<close>] count_decided_le_length[of M']
    using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<A> \<open>tl C\<close> \<open>x - 1\<close>]
    by (auto simp: upt_eq_lel_conv nth_tl simp flip: get_level_get_level_pol)
      (auto simp: trail_pol_alt_def)
  done


definition mark_LBD_st :: \<open>'v twl_st_wl \<Rightarrow> ('v twl_st_wl) nres\<close> where
  \<open>mark_LBD_st = (\<lambda>S. SPEC (\<lambda>(T). S = T))\<close>

lemma mark_LBD_st_alt_def:
   \<open>mark_LBD_st S = do {n :: bool list \<leftarrow> SPEC (\<lambda>_. True); SPEC (\<lambda>(T). S = T)}\<close>
  unfolding mark_LBD_st_def
  by auto

lemma mark_lbd_from_conflict_mark_LBD_st:
  \<open>(mark_lbd_from_conflict, mark_LBD_st) \<in>
    [\<lambda>S. get_conflict_wl S \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (all_atms_st S) (the (get_conflict_wl S))]\<^sub>f
     twl_st_heur_conflict_ana \<rightarrow> \<langle>twl_st_heur_conflict_ana\<rangle>nres_rel\<close>
  unfolding mark_lbd_from_conflict_def mark_LBD_st_alt_def
  apply (intro frefI nres_relI)
  subgoal for x y
    apply (refine_rcg mark_lbd_from_list_heur_correctness[of _ \<open>get_trail_wl y\<close> \<open>all_atms_st y\<close>,
      THEN order_trans])
    subgoal
      by (force simp: twl_st_heur_conflict_ana_def)
    subgoal
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of _ \<open>(the (get_conflict_wl y))\<close>])
        (auto simp: twl_st_heur_conflict_ana_def out_learned_def)
    subgoal by auto
    subgoal by (auto simp: twl_st_heur_conflict_ana_def RETURN_RES_refine_iff)
    done
  done

definition update_lbd_and_mark_used where
  \<open>update_lbd_and_mark_used i glue N = 
    (let N = update_lbd i glue N in
    (if glue \<le> TIER_TWO_MAXIMUM then mark_used2 N i else mark_used N i))\<close>

lemma length_update_lbd_and_mark_used[simp]: \<open>length (update_lbd_and_mark_used i glue N) = length N\<close>
  by (auto simp: update_lbd_and_mark_used_def Let_def split: if_splits)

text \<open>CaDiCaL sets the used flags of clauses only as 1, not as two.\<close>
definition update_lbd_shrunk_clause where
  \<open>update_lbd_shrunk_clause C N = do {
     old_glue \<leftarrow> mop_arena_lbd N C;
     st \<leftarrow> mop_arena_status N C;
     le \<leftarrow> mop_arena_length N C;
     ASSERT (le \<ge> 2);
     if st = IRRED then RETURN N
     else do {
       let new_glue = (if le - 1 \<ge> old_glue then old_glue else le - 1);
       ASSERT (update_lbd_pre ((C, new_glue), N));
       RETURN (update_lbd C new_glue N)
    }
}\<close>


lemma update_lbd_shrunk_clause_valid:
  \<open>C \<in># dom_m N \<Longrightarrow> valid_arena arena N vdom \<Longrightarrow>
     update_lbd_shrunk_clause C arena \<le> SPEC(\<lambda>c. (c, N) \<in> {(c, N'). N'=N \<and> valid_arena c N vdom \<and>
       length c = length arena})\<close>
  unfolding update_lbd_shrunk_clause_def mop_arena_lbd_def nres_monad3 mop_arena_status_def
    mop_arena_length_def update_lbd_def
  apply refine_vcg
  subgoal
    unfolding get_clause_LBD_pre_def arena_is_valid_clause_idx_def
    by auto
  subgoal
    unfolding arena_is_valid_clause_vdom_def
    by auto
  subgoal
    unfolding arena_is_valid_clause_idx_def
    by auto
  subgoal
    by (rule arena_lifting(18))
  subgoal by auto
  subgoal by (auto simp: update_lbd_pre_def)
  subgoal by (auto simp: Let_def intro!: valid_arena_mark_used2 valid_arena_mark_used
    valid_arena_update_lbd)
  done

end
