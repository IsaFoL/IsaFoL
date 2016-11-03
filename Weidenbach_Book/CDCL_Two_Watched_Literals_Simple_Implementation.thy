theory CDCL_Two_Watched_Literals_Simple_Implementation
imports CDCL_Two_Watched_Literals_List
begin

type_synonym working_queue_list = "(nat \<times> nat) list"
type_synonym 'v lit_queue_list = "'v literal list"
type_synonym 'v twl_st_ll =
  "('v, nat) ann_lits \<times> 'v clause_list list \<times> nat \<times>
    'v clause_list option \<times> 'v clauses \<times> 'v clauses \<times> working_queue_list \<times> 'v lit_queue_list"

fun working_queue_ll :: "'v twl_st_ll \<Rightarrow> working_queue_list" where
  \<open>working_queue_ll (_, _, _, _, _, _, WS, _) = WS\<close>

fun get_trail_ll :: "'v twl_st_ll \<Rightarrow> ('v, nat) ann_lits" where
  \<open>get_trail_ll (M, _, _, _, _, _, _, _) = M\<close>

fun set_working_queue_ll :: "working_queue_list \<Rightarrow> 'v twl_st_ll \<Rightarrow>
  'v twl_st_ll" where
  \<open>set_working_queue_ll WS (M, N, U, D, NP, UP, _, Q) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun pending_ll :: "'v twl_st_ll \<Rightarrow> 'v literal list" where
  \<open>pending_ll (_, _, _, _, _, _, _, Q) = Q\<close>

fun set_pending_ll :: "'v literal list \<Rightarrow> 'v twl_st_ll \<Rightarrow> 'v twl_st_ll" where
  \<open>set_pending_ll Q (M, N, U, D, NP, UP, WS, _) = (M, N, U, D, NP, UP, WS, Q)\<close>

fun get_conflict_ll :: "'v twl_st_ll \<Rightarrow> 'v clause_list option" where
  \<open>get_conflict_ll (_, _, _, D, _, _, _, _) = D\<close>

lemma count_decided_ge_1_mark_of_gt_1:
  fixes S
  defines M[simp]: \<open>M \<equiv> get_trail_list S\<close>
  defines L[simp]: \<open>L \<equiv> hd M\<close>
  assumes struct_invs: \<open>twl_struct_invs (twl_st_of S)\<close> and 
    dec: \<open>count_decided M \<ge> 1\<close> and
    proped: \<open>is_proped L\<close>
  shows \<open>mark_of L \<noteq> 0\<close>
proof -
  obtain M N U D NP UP WS Q where 
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S) auto
  have 
    \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa (convert_to_state (twl_st_of S))\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (convert_to_state (twl_st_of S))\<close>
    using struct_invs unfolding twl_struct_invs_def by fast+
  moreover have \<open>Suc 0 \<le> backtrack_lvl (convert_to_state (twl_st_of S))\<close>
    using dec unfolding M S by (auto simp: cdcl\<^sub>W_restart_mset_state)
  ultimately show ?thesis
    using cdcl\<^sub>W_restart_mset.hd_trail_level_ge_1_length_gt_1[of \<open>convert_to_state (twl_st_of S)\<close>]
    proped
    by (cases M; cases \<open>hd M\<close>) (auto simp add: S cdcl\<^sub>W_restart_mset_state split: if_splits)
qed

definition skip_and_resolve_loop_ll :: "'v twl_st_list \<Rightarrow> 'v twl_st_list nres"  where
  \<open>skip_and_resolve_loop_ll S\<^sub>0 =
    do {
      (_, S) \<leftarrow>
        WHILE\<^sub>T\<^bsup>\<lambda>(brk, S). skip_and_resolve_loop_inv (twl_st_of S\<^sub>0) (brk, twl_st_of S) \<and>
         additional_WS_invs S \<and> count_decided (get_trail_list S) \<ge> 1\<^esup>
        (\<lambda>(brk, S). \<not>brk \<and> \<not>is_decided (hd (get_trail_list S)))
        (\<lambda>(_, S).
          let (M, N, U, D, NP, UP, WS, Q) = S in
          do {
            ASSERT(M \<noteq> []);
            let D' = the (get_conflict_list S);
            (L, C) \<leftarrow> SPEC(\<lambda>(L, C). Propagated L C = hd (get_trail_list S));
            if -L \<notin># mset D' then
              do {RETURN (False, (tl M, N, U, D, NP, UP, WS, Q))}
            else
              if get_maximum_level M (remove1_mset (-L) (mset D')) = count_decided M
              then
                do {RETURN (resolve_cls_list L D' (N!C) = [],
                   (tl M, N, U, Some (resolve_cls_list L D' (N!C)),
                     NP, UP, WS, Q))}
              else
                do {RETURN (True, S)}
          }
        )
        (False, S\<^sub>0);
      RETURN S
    }
  \<close>

definition skip_and_resolve_and_backtrack_list where
\<open>skip_and_resolve_and_backtrack_list S = do {
     T \<leftarrow> skip_and_resolve_loop_list S;
     if get_conflict_list T \<noteq> Some []
     then do {U \<leftarrow> backtrack_list T; RETURN (False, U)}
     else do {RETURN (True, T)}
  }
  \<close>

definition skip_and_resolve_and_backtrack_ll :: "'v twl_st_list \<Rightarrow> (bool \<times> 'v twl_st_list) nres"  where
  \<open>skip_and_resolve_and_backtrack_ll S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      if count_decided M = 0 
      then 
        RETURN (True, ([], N, U, Some [], NP, UP, WS, Q))
      else do {
        T \<leftarrow> skip_and_resolve_loop_list S;
        U \<leftarrow> backtrack_list T;
        RETURN (False, U)
        }
    }
  \<close>
end