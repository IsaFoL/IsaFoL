theory IsaSAT_Simplify_Binaries_Defs
  imports IsaSAT_Setup
    IsaSAT_Restart_Defs
    IsaSAT_Simplify_Units_Defs
begin

type_synonym 'a ahm = \<open>'a list \<times> nat list\<close>

definition ahm_get_marked :: \<open>'a::zero ahm \<Rightarrow> nat literal \<Rightarrow> _\<close> where
  \<open>ahm_get_marked = (\<lambda>(C,stamp) L. do {
     ASSERT(nat_of_lit L < length C);
     RETURN (C!nat_of_lit L)
  })\<close>


definition get_marked :: \<open>(nat literal \<Rightarrow> 'a option) \<times> nat \<Rightarrow> nat literal \<Rightarrow> _\<close>   where
  \<open>get_marked C L = do {
     ASSERT(nat_of_lit L < snd C \<and> fst C L \<noteq> None);
     RETURN (the (fst C L))
  }\<close>


definition array_hash_map_rel :: \<open>('a :: zero \<times> 'b) set \<Rightarrow> ('a ahm \<times> _) set\<close> where
  \<open>array_hash_map_rel R = {((xs, support), (ys, m)). m = length xs \<and>
      (set support =nat_of_lit ` dom ys) \<and>
      (\<forall>i\<in>set support. i < m) \<and> distinct support \<and>
      (\<forall>L. nat_of_lit L < m \<longrightarrow> (ys L = None \<longleftrightarrow> xs ! nat_of_lit L = 0)) \<and>
     (\<forall>L. nat_of_lit L < m \<longrightarrow> (\<forall>a. ys L = Some a \<longrightarrow> xs ! nat_of_lit L \<noteq> 0 \<and> (xs ! nat_of_lit L, a) \<in> R))}\<close>


definition ahm_is_marked :: \<open>'a::zero ahm \<Rightarrow> nat literal \<Rightarrow> _\<close> where
  \<open>ahm_is_marked = (\<lambda>(C,stamp) L. do {
     ASSERT(nat_of_lit L < length C);
     RETURN (C!nat_of_lit L \<noteq> 0)
  })\<close>
definition is_marked :: \<open>(nat literal \<Rightarrow> 'a option) \<times> nat \<Rightarrow> nat literal \<Rightarrow> _\<close>   where
  \<open>is_marked C L =  do {
     ASSERT(nat_of_lit L < snd C);
     RETURN (fst C L \<noteq> None)
  }\<close>

definition update_marked :: \<open>(nat literal \<Rightarrow> _ option) \<times> nat \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>
  ((nat literal \<Rightarrow> _ option) \<times> nat) nres\<close> where
  \<open>update_marked C L v = do {
     ASSERT (nat_of_lit L < snd C \<and> (fst C)L \<noteq> None);
     RETURN ((fst C)(L := Some v), snd C)
  }\<close>

definition set_marked :: \<open>(nat literal \<Rightarrow> _ option) \<times> nat \<Rightarrow> nat literal \<Rightarrow> _ \<Rightarrow>
  ((nat literal \<Rightarrow> _ option) \<times> nat) nres\<close> where
  \<open>set_marked C L v = do {
     ASSERT (nat_of_lit L < snd C \<and> (fst C)L = None);
     RETURN ((fst C)(L := Some v), snd C)
  }\<close>


(*TODO rename*)
definition empty :: \<open>(nat literal \<Rightarrow> 'b option) \<times> nat \<Rightarrow> ((nat literal \<Rightarrow> 'b option) \<times> nat) nres\<close>   where
  \<open>empty = (\<lambda>(_, n). do {
     RETURN (\<lambda>_. None, n)
  })\<close>

lemma ahm_is_marked_is_marked:
   \<open>(uncurry ahm_is_marked, uncurry is_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  unfolding ahm_is_marked_def is_marked_def uncurry_def
  apply (intro frefI nres_relI fun_relI)
  apply refine_vcg
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  apply simp
  by (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)




lemma ahm_get_marked_get_marked:
   \<open>(uncurry ahm_get_marked, uncurry get_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<rightarrow> \<langle>R\<rangle>nres_rel\<close>
  unfolding ahm_get_marked_def get_marked_def uncurry_def
  apply (intro frefI nres_relI fun_relI)
  apply refine_vcg
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  apply clarsimp
  apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]
  done


definition ahm_set_marked :: \<open>'a :: zero ahm \<Rightarrow> nat literal \<Rightarrow> _\<close> where
  \<open>ahm_set_marked= (\<lambda>(C,stamp) L v. do {
     ASSERT(nat_of_lit L < length C \<and> Suc (length stamp) \<le> length C);
     RETURN (C[nat_of_lit L := v], stamp @ [nat_of_lit L])
  })\<close>


lemma ahm_set_marked_set_marked:
  assumes [simp]: \<open>\<And>a. (0, a) \<notin> R\<close>
  shows \<open>(uncurry2 ahm_set_marked, uncurry2 set_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f R \<rightarrow>\<^sub>f \<langle>array_hash_map_rel R\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>Suc (length x2b) \<le> length x1d\<close>
    if
      \<open>nat_of_lit x2 < length x1d\<close> and
      \<open>x1d ! nat_of_lit x2 = 0\<close> and
      \<open>set x2b = nat_of_lit ` {a. \<exists>y. ac a = Some y}\<close> and
      \<open>\<forall>i. (\<exists>y. ac i = Some y) \<longrightarrow> nat_of_lit i < length x1d\<close> and
      dist: \<open>distinct x2b\<close> and
      \<open>\<forall>L. nat_of_lit L < length x1d \<longrightarrow> (ac L = None) = (x1d ! nat_of_lit L = 0)\<close> 
    for ac :: \<open>nat literal \<Rightarrow> 'a option\<close> and x2 :: \<open>nat literal\<close> and x2a :: 'a and x1d :: \<open>'b list\<close> and x2b :: \<open>nat list\<close> and x2d :: 'b
  proof -
    have \<open>(set x2b) \<subseteq> nat_of_lit ` (dom ac) \<inter> {0..<length x1d}\<close>
      using that by (auto simp add: dom_def)
    moreover have \<open>nat_of_lit x2 \<in>  {0..<length x1d}\<close>  and notin: \<open>nat_of_lit x2 \<notin> set x2b\<close>
      using that by auto
    ultimately have H: \<open>insert (nat_of_lit x2) (set x2b) \<subseteq> {0..<length x1d}\<close>
      by blast
    show ?thesis
      using card_mono[OF _ H] notin dist
      by (auto simp: distinct_card)
  qed
  show ?thesis
    unfolding ahm_set_marked_def set_marked_def uncurry_def
    apply (intro frefI fun_relI nres_relI)
    apply refine_vcg
    apply (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def dom_def
      intro!: ASSERT_leI)
   done
qed


definition ahm_update_marked :: \<open>'a :: zero ahm \<Rightarrow> nat literal \<Rightarrow> _\<close> where
  \<open>ahm_update_marked= (\<lambda>(C,stamp) L v. do {
     ASSERT(nat_of_lit L < length C);
     RETURN (C[nat_of_lit L := v], stamp)
  })\<close>


lemma ahm_update_marked_update_marked:
  assumes [simp]: \<open>\<And>a. (0, a) \<notin> R\<close>
  shows \<open>(uncurry2 ahm_update_marked, uncurry2 update_marked)
    \<in>  (array_hash_map_rel R) \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f R \<rightarrow>\<^sub>f \<langle>array_hash_map_rel R\<rangle>nres_rel\<close>
  unfolding ahm_update_marked_def update_marked_def uncurry_def
  apply (intro frefI nres_relI)
  by refine_vcg
   (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def dom_def
    intro!: ASSERT_leI)

definition ahm_create :: \<open>nat \<Rightarrow> 'a::zero ahm nres\<close> where
  \<open>ahm_create m = do {
     RETURN (replicate m 0, [])
  }\<close>


definition create :: \<open>nat \<Rightarrow> _\<close>   where
  \<open>create m = do {
     RETURN (\<lambda>_. None, m)
  }\<close>

lemma ahm_create_create:
   \<open>(ahm_create, create) \<in> nat_rel \<rightarrow> \<langle>array_hash_map_rel R\<rangle>nres_rel\<close>
  unfolding ahm_create_def create_def uncurry_def
  by refine_vcg
    (auto simp: array_hash_map_rel_def ahm_is_marked_def is_marked_def
    intro!: ASSERT_leI)[]


definition ahm_empty :: \<open>'a::zero ahm \<Rightarrow> 'a ahm nres\<close> where
  \<open>ahm_empty = (\<lambda>(CS, support). do {
    let n = length support;
    (_, CS) \<leftarrow> WHILE\<^sub>T
      (\<lambda>(i, CS). i < n)
      (\<lambda>(i, CS). do {ASSERT (i < length support \<and> support ! i < length CS); RETURN (i+1, CS[support ! i := 0])})
      (0, CS);
    RETURN (CS, take 0 support)
  })\<close>


lemma ahm_empty_empty:
  \<open>(ahm_empty, empty) \<in> (array_hash_map_rel R) \<rightarrow> \<langle>array_hash_map_rel R\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>dom (\<lambda>aa. if nat_of_lit aa \<in> xs then None else m aa) =
    dom m - {a. nat_of_lit a \<in> xs}\<close> for xs m
    by (auto split: if_splits)
  have [simp]: \<open>nat_of_lit ` dom x1 = set x2a \<Longrightarrow> distinct x2a \<Longrightarrow>
    nat_of_lit ` (dom x1 - {aa. nat_of_lit aa \<in> set (take a x2a)}) = set (drop a x2a)\<close> for x2a a x1
    apply (drule eq_commute[of _ "set x2a", THEN iffD1])
    apply (auto simp: dom_def)
    apply (metis (mono_tags, lifting) Reversed_Bit_Lists.atd_lem UnE image_subset_iff mem_Collect_eq set_append set_mset_mono set_mset_mset subset_mset.dual_order.refl)
    apply (frule in_set_dropD)
    apply simp
    by (smt (verit, ccfv_threshold) DiffI IntI Reversed_Bit_Lists.atd_lem distinct_append empty_iff image_iff mem_Collect_eq)

  show ?thesis
    unfolding ahm_empty_def empty_def uncurry_def fref_param1
    apply (intro ext frefI nres_relI)
    subgoal for x y
      apply (refine_vcg WHILET_rule[where I = \<open>\<lambda>(i, CS).  ((CS, drop i (snd x)), (\<lambda>a. if nat_of_lit a \<in> set (take i (snd x)) then None else fst y a, snd y)) \<in>array_hash_map_rel R\<close> and
        R = \<open>measure (\<lambda>(i,_). length (snd x) -i)\<close>])
      subgoal by auto
      subgoal by auto
      subgoal by (clarsimp simp: array_hash_map_rel_def)
      subgoal by (auto simp: array_hash_map_rel_def)
      subgoal premises p for x1 x2 x1a x2a s a b x1b x2b
        using p
        by (clarsimp simp: array_hash_map_rel_def less_Suc_eq  eq_commute[of _ \<open>nat_of_lit ` dom _\<close>]
          simp flip: Cons_nth_drop_Suc)
          (auto simp: take_Suc_conv_app_nth)
      subgoal by (auto simp: nth_list_update' less_Suc_eq array_hash_map_rel_def)
      subgoal for x1 x2 x1a x2a s a b
        apply (auto simp: array_hash_map_rel_def)
        apply (drule_tac x=L in spec)
        apply (auto split: if_splits)
        done
      done
    done
qed

definition isa_clause_remove_duplicate_clause_wl :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_clause_remove_duplicate_clause_wl C S = (do{
    _ \<leftarrow> log_del_clause_heur S C;
    let N' = get_clauses_wl_heur S;
    st \<leftarrow> mop_arena_status N' C;
    let st = st = IRRED;
    ASSERT (mark_garbage_pre (N', C) \<and> arena_is_valid_clause_vdom (N') C);
    let N' = extra_information_mark_to_delete (N') C;
    let lcount = get_learned_count S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else (clss_size_decr_lcount lcount));
    let stats = get_stats_heur S;
    let stats = (incr_binary_red_removed (if st then decr_irred_clss stats else stats));
    let S = set_clauses_wl_heur N' S;
    let S = set_learned_count_wl_heur lcount S;
    let S = set_stats_wl_heur stats S;
    RETURN S
   })\<close>

definition isa_binary_clause_subres_lits_wl_pre :: \<open>_\<close> where
  \<open>isa_binary_clause_subres_lits_wl_pre C L L' S \<longleftrightarrow>
    (\<exists>T r u. (S, T)\<in> twl_st_heur_restart_ana' r u \<and>  binary_clause_subres_lits_wl_pre C L L' T)\<close>

definition isa_binary_clause_subres_wl :: \<open>_\<close> where
  \<open>isa_binary_clause_subres_wl C L L' S = do {
      ASSERT (isa_binary_clause_subres_lits_wl_pre C L L' S);
      let _ = log_del_binary_clause L (-L');
      let M = get_trail_wl_heur S;
      M \<leftarrow> cons_trail_Propagated_tr L 0 M;
      let lcount = get_learned_count S;
      let N' = get_clauses_wl_heur S;
      st \<leftarrow> mop_arena_status N' C;
      let st = st = IRRED;
      ASSERT (mark_garbage_pre (N', C) \<and> arena_is_valid_clause_vdom (N') C);
      let N' = extra_information_mark_to_delete (N') C;
      ASSERT(\<not>st \<longrightarrow> (clss_size_lcount lcount \<ge> 1 \<and> clss_size_lcountUEk (clss_size_decr_lcount lcount) < learned_clss_count S));
      let lcount = (if st then lcount else (clss_size_incr_lcountUEk (clss_size_decr_lcount lcount)));
      let stats = get_stats_heur S;
      let stats = incr_binary_unit_derived (if st then decr_irred_clss stats else stats);
      let stats = incr_units_since_last_GC (incr_uset stats);
      let S = set_trail_wl_heur M S;
      let S = set_clauses_wl_heur N' S;
      let S = set_learned_count_wl_heur lcount S;
      let S = set_stats_wl_heur stats S;
      RETURN S
  }\<close>

definition isa_deduplicate_binary_clauses_wl :: \<open>nat literal \<Rightarrow> _ \<Rightarrow> isasat \<Rightarrow> (_ \<times> isasat) nres\<close> where
\<open>isa_deduplicate_binary_clauses_wl L CS S\<^sub>0 = do {
    let CS = CS;
    l \<leftarrow> mop_length_watched_by_int S\<^sub>0 L;
    ASSERT (l \<le> length (get_clauses_wl_heur S\<^sub>0) - 2);
    val \<leftarrow> mop_polarity_pol (get_trail_wl_heur S\<^sub>0) L;
    (_, _, CS, S) \<leftarrow> WHILE\<^sub>T(\<lambda>(abort, i, CS, S). \<not>abort \<and> i < l \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(abort, i, CS, S).
      do {
         ASSERT (i < l);
         ASSERT (length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S\<^sub>0));
         ASSERT (learned_clss_count S \<le> learned_clss_count S\<^sub>0);
         (C,L', b) \<leftarrow> mop_watched_by_app_heur S L i;
         ASSERT (C > 0 \<and> C < length (get_clauses_wl_heur S));
         st \<leftarrow> mop_arena_status (get_clauses_wl_heur S) C;
         if st = DELETED \<or> \<not>b then
           RETURN (abort, i+1, CS, S)
         else do {
           val \<leftarrow> mop_polarity_pol (get_trail_wl_heur S) L';
           if val \<noteq> UNSET then do {
             S \<leftarrow> isa_simplify_clause_with_unit_st2 C S;
             val \<leftarrow> mop_polarity_pol (get_trail_wl_heur S) L;
             RETURN (val \<noteq> UNSET, i+1, CS, S)
           }
           else do {
             m \<leftarrow> is_marked CS (L');
             n \<leftarrow> (if m then get_marked CS L' else RETURN (1, True));
             if m then do {
               let C' = (if \<not>snd n \<longrightarrow> st = LEARNED then C else fst n);
               CS \<leftarrow> (if \<not>snd n \<longrightarrow> st = LEARNED then RETURN CS else update_marked CS (L') (C, st = IRRED));
               S \<leftarrow> isa_clause_remove_duplicate_clause_wl C' S;
               RETURN (abort, i+1, CS, S)
             } else do {
               m \<leftarrow> is_marked CS (-L') ;
               if m then do {
                 S \<leftarrow> isa_binary_clause_subres_wl C L (-L') S;
                 RETURN (True, i+1, CS, S)
               }
               else do {
                 CS \<leftarrow> set_marked CS (L') (C, st = IRRED);
                 RETURN (abort, i+1, CS, S)
             }
            }
          }
        }
      })
      (val \<noteq> UNSET, 0, CS, S\<^sub>0);
   CS \<leftarrow> empty CS;
   RETURN (CS, S)
}\<close>

definition mark_duplicated_binary_clauses_as_garbage_pre_wl_heur :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S \<longleftrightarrow>
  (\<exists>S' r u. (S, S') \<in> twl_st_heur_restart_ana' r u \<and>
    mark_duplicated_binary_clauses_as_garbage_pre_wl S')\<close>

definition isa_mark_duplicated_binary_clauses_as_garbage_wl :: \<open>isasat \<Rightarrow> _ nres\<close> where
  \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl S\<^sub>0 = (do {
     let ns = (get_vmtf_heur_array S\<^sub>0);
     ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<^sub>0);
     skip \<leftarrow> RETURN (should_eliminate_pure_st S\<^sub>0);
     CS \<leftarrow> create (length (get_watched_wl_heur S\<^sub>0));
     (_, CS, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(n,CS,S). ns = (get_vmtf_heur_array S)\<^esup>(\<lambda>(n, CS,S). n \<noteq> None \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(n, CS, S). do {
        ASSERT (n \<noteq> None);
        let A = the n;
        ASSERT (A < length ns);
        ASSERT (A \<le> unat32_max div 2);
        S \<leftarrow> do {ASSERT (ns = (get_vmtf_heur_array S));
        skip_lit \<leftarrow> mop_is_marked_added_heur_st S A;
        if \<not>skip \<or> \<not>skip_lit then RETURN (CS, S)
        else do {
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Pos A) CS S;
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Neg A) CS S;
          ASSERT (ns = (get_vmtf_heur_array S));
          RETURN (CS, S)
        }};
        RETURN (get_next (ns ! A), S)
     })
     (Some (get_vmtf_heur_fst S\<^sub>0), CS, S\<^sub>0);
    RETURN S
  })\<close>


definition isa_mark_duplicated_binary_clauses_as_garbage_wl2 :: \<open>isasat \<Rightarrow> _ nres\<close> where
  \<open>isa_mark_duplicated_binary_clauses_as_garbage_wl2 S\<^sub>0 = (do {
    let ns = get_vmtf_heur_array S\<^sub>0;
    ASSERT (mark_duplicated_binary_clauses_as_garbage_pre_wl_heur S\<^sub>0);
    dedup \<leftarrow> RETURN (should_eliminate_pure_st S\<^sub>0);
    CS \<leftarrow> create (length (get_watched_wl_heur S\<^sub>0));
    (_, CS, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(n,CS, S). get_vmtf_heur_array S\<^sub>0 = (get_vmtf_heur_array S)\<^esup>(\<lambda>(n, CS, S). n \<noteq> None \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(n, CS, S). do {
        ASSERT (n \<noteq> None);
        let A = the n;
        ASSERT (A < length (get_vmtf_heur_array S));
        ASSERT (A \<le> unat32_max div 2);
        (CS, S) \<leftarrow> do {
        added_lit \<leftarrow> mop_is_marked_added_heur_st S A;
        if \<not>dedup \<or> \<not>added_lit then RETURN (CS, S)
        else do {
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Pos A) CS S;
          ASSERT (length (get_clauses_wl_heur S) \<le> length (get_clauses_wl_heur S\<^sub>0) \<and> learned_clss_count S \<le> learned_clss_count S\<^sub>0);
          (CS, S) \<leftarrow> isa_deduplicate_binary_clauses_wl (Neg A) CS S;
          ASSERT (ns = get_vmtf_heur_array S);
          RETURN (CS, S)
        }};
        RETURN (get_next (get_vmtf_heur_array S ! A), CS, S)
     })
     (Some (get_vmtf_heur_fst S\<^sub>0), CS, S\<^sub>0);
    RETURN S
 })\<close>

end