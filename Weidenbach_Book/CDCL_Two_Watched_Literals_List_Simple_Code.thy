theory CDCL_Two_Watched_Literals_List_Simple_Code
  imports CDCL_Two_Watched_Literals_List DPLL_CDCL_W_Implementation
begin

definition backtrack_list' :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres" where
  \<open>backtrack_list' S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1);
        let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
        let M1 = tl (the (bt_cut j M));

        if length (the D) > 1
        then do {
          let L' = the (find (\<lambda>L'.  get_level M L' = get_maximum_level M (mset (the D) - {#-L#})) (the D));
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, {#L#})
        }
      }
    }
  \<close>

lemma Let_assignI: \<open>\<Phi> = {L'} \<Longrightarrow> P L' = Q L' \<Longrightarrow>  (do {let L = L'; P L}) = (do {L \<leftarrow> RES \<Phi>; Q L})\<close>
  by (simp add: RES_sng_eq_RETURN)

lemma bt_cut_not_none2:
  assumes "no_dup M"  and "i < count_decided M"
  shows "bt_cut i M \<noteq> None"
proof -
  obtain K M1 M2 where
    \<open>M = M2 @ Decided K # M1\<close> and \<open>get_level M K = Suc i\<close>
      using le_count_decided_decomp[OF assms(1)] assms(2) by auto
    then show ?thesis
      using bt_cut_not_none[OF assms(1), of M2 K M1 i] by auto
qed

lemma backtrack_list'_spec:
  assumes
    confl1: \<open>get_conflict_list S \<noteq> None\<close> and
    confl2: \<open>get_conflict_list S \<noteq> Some []\<close> and
    \<open>working_queue_list S = {#}\<close> and
    \<open>pending_list S = {#}\<close> and
    \<open>additional_WS_invs S\<close> and
    ns: \<open>no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of S))\<close> and
    \<open>no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of S))\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of S)\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of S)\<close> (* and
    SS: \<open>S' = S\<close> *)
  shows \<open>backtrack_list' S \<le> \<Down> Id (backtrack_list S)\<close>
proof-
  show ?thesis
    unfolding backtrack_list_def backtrack_list'_def (* SS *)
    apply (rewrite at \<open>let _ = snd _ in _\<close> Let_def)
    apply (refine_rcg; remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal premises p for M N U C NP UP WS Q L
    proof -
      note S = p(1) and L = p(4) and M_not_empty = p(2) and ex_decomp = p(8)
      have n_d: \<open>no_dup M\<close>
        using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (simp add: cdcl\<^sub>W_restart_mset_state S)
      obtain C' where [simp]: \<open>C = Some C'\<close>
        using confl1 S by auto
      have lev_L: \<open>get_level M L = count_decided M\<close>
        using M_not_empty L by (cases M) auto
      have uhd_C: \<open>- lit_of (hd (convert_lits_l N M)) \<in> set C'\<close>
        using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
            \<open>convert_to_state (twl_st_of (M, N, U, C, NP, UP, WS, Q))\<close>]
        confl2 ns struct_invs stgy_invs unfolding S
        by (auto simp: twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset_state)
      obtain M1'' M2'' K'' where
        decomp_K'': \<open>(Decided K'' # M1'', M2'') \<in> set (get_all_ann_decomposition M)\<close>
        \<open>get_level M K'' = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C')))\<close>
        using ex_decomp by auto
      then have lev_max: \<open>get_maximum_level M (mset (remove1 (-L) C')) < count_decided M\<close>
        using count_decided_ge_get_level[of M K''] L by auto
      have \<open>-L \<in># mset C'\<close>
        using uhd_C L M_not_empty by (cases M) simp_all
      with multi_member_split[OF this]
      have False if \<open>find_level_decomp M (the C) [] (count_decided M) = None\<close>
        using find_level_decomp_none[OF that, of \<open>-L\<close> \<open>remove1 (-L) C'\<close>] lev_max
        unfolding S by (auto dest!: simp: lev_L)
      then obtain K j where
        Kj: \<open>find_level_decomp M C' [] (count_decided M) = Some (K, j)\<close>
        by (cases \<open>find_level_decomp M (the C) [] (count_decided M)\<close>) auto
      then have
        \<open>K \<in> set C'\<close> and
        j: \<open>get_maximum_level M (mset (remove1 K C')) = j\<close> and
        \<open>get_level M K = count_decided M\<close>
        using find_level_decomp_some[OF Kj] by simp_all
      have KL: \<open>K = -L\<close>
        by (metis \<open>K \<in> set C'\<close> \<open>\<exists>A. mset C' = add_mset (- L) A\<close> \<open>get_level M K = count_decided M\<close>
            add_mset_remove_trivial get_maximum_level_ge_get_level leD lev_max member_add_mset
            mset_remove1 set_mset_mset)
      have j_le_M: \<open>j < count_decided M\<close>
          unfolding j[symmetric] KL using lev_max by simp
      have \<open>bt_cut j M \<noteq> None\<close>
        apply (rule bt_cut_not_none2[of ])
        using n_d apply (simp; fail)
        using j_le_M by simp
      then obtain M2 M1 K''' M' where
        \<open>M = M2 @ M'\<close> and M': \<open>M' = Decided K''' # M1\<close> and lev_K: \<open>get_level M K''' = j + 1\<close> and
        bt_cut: \<open>bt_cut j M = Some M'\<close>
        using bt_cut_some_decomp[of M j \<open>the (bt_cut j M)\<close>] n_d by auto
      show ?thesis
        using lev_K j bt_cut_in_get_all_ann_decomposition[OF n_d bt_cut] by (auto simp: Kj bt_cut M' KL)
    qed
    subgoal premises p for M N U C NP UP WS Q L M1
    proof -
      note S = p(1) and L_hd = p(4) and len_C = p(11)
      obtain C' where [simp]: \<open>C = Some C'\<close>
        using confl1 S by auto

      have \<open>find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (- L) (mset (the C)))) (the C) \<noteq> None\<close>
      proof (rule ccontr)
        assume H: \<open>\<not>?thesis\<close>
        have \<open>remove1_mset (- lit_of (hd M)) (mset (the C)) \<noteq> {#}\<close>
          using len_C by (cases C'; cases \<open>tl C'\<close>) (auto simp: Diff_eq_empty_iff_mset)
        then show False
          using get_maximum_level_exists_lit_of_max_level[of
              \<open>remove1_mset (- lit_of (hd M)) (mset (the C))\<close> M]
          using L_hd H by (auto simp: find_None_iff dest: in_diffD)
      qed
      then show ?thesis
        using p by (auto dest: find_SomeD)
    qed
    subgoal by simp
    subgoal by simp
    done
qed

definition cdcl_twl_o_prog_list' :: "'v twl_st_list \<Rightarrow> (bool \<times> 'v twl_st_list) nres"  where
  \<open>cdcl_twl_o_prog_list' S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      do {
        if D = None
        then
          if (\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))
          then do {S \<leftarrow> decide_list S; RETURN (False, S)}
          else do {RETURN (True, S)}
        else do {
          T \<leftarrow> skip_and_resolve_loop_list S;
          if get_conflict_list T \<noteq> Some []
          then do {U \<leftarrow> backtrack_list' T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

lemma TT:
  assumes \<open>(f, g) \<in> {(S, S'). S' = h S \<and> P S} \<rightarrow> \<langle>{(T, T'). T' = h' T \<and> Q T}\<rangle>nres_rel\<close> and
    \<open>P S\<close> and \<open>\<And>S. P S \<Longrightarrow> nofail (g (h S))\<close>
  shows \<open>f S \<le> \<Down> {(T', T). T = T' \<and> Q T} (f S)\<close>
  using assms unfolding fun_rel_def nres_rel_def
  by (auto simp add: pw_conc_inres pw_conc_nofail pw_ords_iff(1))

lemma TT':
  assumes \<open>f \<le> \<Down> R g\<close> and \<open>g \<le> \<Down> R' h\<close>
  shows \<open>f \<le> \<Down> (R O R') h\<close>
  by (metis (full_types) assms(1) assms(2) conc_fun_chain ref_two_step)

thm TT'[OF backtrack_list'_spec backtrack_list_spec[THEN refine_pair_to_SPEC]]

lemma cdcl_twl_o_prog_list_spec:
  \<open>(cdcl_twl_o_prog_list', cdcl_twl_o_prog) \<in>
    {(S, S'). S' = twl_st_of S \<and>
       working_queue_list S = {#} \<and> pending_list S = {#} \<and> no_step cdcl_twl_cp (twl_st_of S) \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S) \<and> additional_WS_invs S} \<rightarrow>
    \<langle>{((brk, T), (brk', T')). T' = twl_st_of T \<and> brk = brk' \<and> additional_WS_invs T \<and>
    (get_conflict_list T \<noteq> None \<longrightarrow> get_conflict_list T = Some [])\<and>
       twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and> working_queue_list T = {#} (* \<and>
       (\<not>brk \<longrightarrow> pending_list T \<noteq> {#}) *)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have twl_prog:
    \<open>(cdcl_twl_o_prog_list', cdcl_twl_o_prog) \<in> ?R \<rightarrow>
      \<langle>{(S, S').
         (fst S' = (fst S) \<and> snd S' = twl_st_of (snd S)) \<and> additional_WS_invs (snd S)}\<rangle> nres_rel\<close>
    apply clarify
    unfolding cdcl_twl_o_prog_list'_def cdcl_twl_o_prog_def
    apply (refine_vcg decide_list_spec[THEN refine_pair_to_SPEC]
        skip_and_resolve_loop_list_spec[THEN refine_pair_to_SPEC]
        TT'[OF backtrack_list'_spec backtrack_list_spec[THEN refine_pair_to_SPEC]];
        remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (auto simp add: get_conflict_list_Some_nil_iff)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T T'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: get_conflict_list_get_conflict)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: (* additional_WS_invs_def *))
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by simp
    subgoal by simp
    done
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::bool \<times> 'a twl_st_list. True)\<close>
  let ?J' = \<open>{(U, U').
       (fst U' = id (fst U) \<and> snd U' = twl_st_of (snd U)) \<and> additional_WS_invs (snd U) \<and>
        (get_conflict (twl_st_of (snd U)) \<noteq> None \<longrightarrow> get_conflict (twl_st_of (snd U)) = Some {#}) \<and>
         twl_struct_invs (twl_st_of (snd U)) \<and>
         twl_stgy_invs (twl_st_of (snd U)) \<and>
         working_queue (twl_st_of (snd U)) = {#} (* \<and>
         (\<not>fst U \<longrightarrow> pending (twl_st_of (snd U)) \<noteq> {#}) *)}\<close>

  have J: \<open>?J = ?J'\<close>
    by auto
  show bt': ?thesis
    unfolding J
    apply (rule refine_add_inv_pair)
    subgoal
      using twl_prog by (auto simp:)
    subgoal for S
      apply (rule weaken_SPEC[OF cdcl_twl_o_prog_spec[of \<open>twl_st_of S\<close>]])
      apply (auto simp: KK(3))[5]
      apply auto
      done
    done
qed


definition cdcl_twl_stgy_prog_list' :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>cdcl_twl_stgy_prog_list' S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of T) \<and> twl_stgy_invs (twl_st_of T) \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of T)) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of S\<^sub>0) (twl_st_of T) \<and>
        working_queue_list T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict_list T = None)\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_list S;
          cdcl_twl_o_prog_list' T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>


lemma cdcl_twl_stgy_prog_list'_spec:
  \<open>(cdcl_twl_stgy_prog_list', cdcl_twl_stgy_prog) \<in>
    {(S, S'). S' = twl_st_of S \<and> additional_WS_invs S \<and>
       working_queue_list S = {#} \<and>
       twl_struct_invs (twl_st_of S) \<and> twl_stgy_invs (twl_st_of S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of T \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> ((False, a), (False, b)) \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> ?R}\<close>
    for a b by auto
  have KK:
    \<open>get_conflict_list T = None \<longleftrightarrow> get_conflict (twl_st_of T) = None\<close>
    \<open>working_queue_list T = {#} \<longleftrightarrow> working_queue (twl_st_of T) = {#}\<close>
    \<open>pending_list T = {#} \<longleftrightarrow> pending (twl_st_of T) = {#}\<close>
    for T
    by (cases T; auto)+
  show ?thesis
    unfolding cdcl_twl_stgy_prog_list'_def cdcl_twl_stgy_prog_def
    apply (refine_rcg R cdcl_twl_o_prog_list_spec[THEN refine_pair_to_SPEC2]
        unit_propagation_outer_loop_list_spec[THEN refine_pair_to_SPEC]; remove_dummy_vars)
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by fastforce
    subgoal unfolding KK by fastforce
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: additional_WS_invs_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal by (auto simp: pending_list_pending)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma cdcl_twl_stgy_prog_list'_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of S)\<close> and \<open>twl_stgy_invs (twl_st_of S)\<close> and
    \<open>working_queue_list S = {#}\<close> and
    \<open>get_conflict_list S = None\<close> and \<open>additional_WS_invs S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_list' S \<le> SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of S) (twl_st_of T))\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_list'_spec[THEN refine_pair_to_SPEC,
          of S \<open>twl_st_of S\<close>]])
  using assms apply auto[2]
  apply (rule order_trans)
   apply (rule ref_two_step[OF _ cdcl_twl_stgy_prog_spec[of \<open>twl_st_of S\<close>],
        of _ \<open>{(S, S'). S' = twl_st_of S \<and> True}\<close>])
  using assms by (auto simp: full_def pending_list_pending get_conflict_list_get_conflict
      pw_conc_inres pw_conc_nofail pw_ords_iff(1))


schematic_goal valued_impl: "RETURN ?c \<le> valued M L"
  unfolding unit_propagation_inner_loop_body_list_def valued_def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

concrete_definition valued_impl uses valued_impl

prepare_code_thms valued_impl_def
export_code valued_impl in SML

declare  find_unwatched_impl[refine_transfer] valued_impl[refine_transfer]
schematic_goal unit_propagation_inner_loop_body_list: "RETURN ?c \<le> unit_propagation_inner_loop_body_list C S"
  unfolding unit_propagation_inner_loop_body_list_def
  apply (refine_transfer)
  done

(*
To generate code, remove assertions!
concrete_definition backtrack_list''_impl uses
  backtrack_list'_def
prepare_code_thms backtrack_list''_impl_def
thm backtrack_list''_impl_def
export_code backtrack_list''_impl in Haskell *)


sepref_definition find_unwatched_impl is 
  "uncurry (find_unwatched :: (nat, nat) ann_lits \<Rightarrow> nat clause_list \<Rightarrow> (bool option \<times> nat) nres)" :: 
 (*  "(asmtx_assn N id_assn)\<^sup>d *\<^sub>a (prod_assn id_assn id_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a asmtx_assn N id_assn" *)
 " (list_assn nat_ann_lit_assn)\<^sup>k *\<^sub>a (list_assn nat_lit_assn)\<^sup>k
      \<rightarrow>\<^sub>a     
   (prod_assn (option_assn bool_assn) nat_assn)"
unfolding find_unwatched_def
apply sepref
oops
end