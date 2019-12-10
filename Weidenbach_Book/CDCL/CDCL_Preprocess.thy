theory CDCL_Preprocess
  imports CDCL.CDCL_W_Abstract_State Refine_Imperative_HOL.IICF
    Watched_Literals.Watched_Literals_Watch_List "../lib/Explorer"
begin

inductive preprocess :: \<open>'v multiset \<Rightarrow> 'v clause \<Rightarrow> 'v clauses \<Rightarrow>
   'v multiset \<Rightarrow> 'v clause \<Rightarrow>'v clauses \<Rightarrow> bool\<close>where
rem_dups_lits:
  \<open>preprocess tauto_lits pure_lits (add_mset (add_mset L (add_mset L C)) N)
              tauto_lits pure_lits  (add_mset (add_mset L C) N)\<close> |
rem_dups_cls:
  \<open>preprocess tauto_lits pure_lits (add_mset C (add_mset C N))
              tauto_lits pure_lits (add_mset C N)\<close> |
rem_tautology:
  \<open>preprocess tauto_lits pure_lits (add_mset (add_mset L (add_mset (-L) C)) N)
    (add_mset (atm_of L) tauto_lits) pure_lits N\<close>  |
pure_literal_deletion: \<open>\<forall>D \<in># add_mset (add_mset L C) N. -L \<notin># D  \<Longrightarrow>
    preprocess tauto_lits pure_lits (add_mset (add_mset L C) N)
       tauto_lits (add_mset L pure_lits)  N\<close>

definition patch_model_preprocess :: \<open>'v multiset \<Rightarrow> 'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v clause\<close> where
  \<open>patch_model_preprocess tauto_lits pure_lits I =
     (I - image_mset uminus pure_lits) + pure_lits +
        image_mset Pos {#L\<in>#tauto_lits. Pos L \<notin># I \<and> Neg L \<notin>#I#}\<close>

definition preprocess_inv :: \<open>'v clauses \<Rightarrow> 'v clause \<Rightarrow> bool\<close> where
  \<open>preprocess_inv N pure_lits \<longleftrightarrow> (\<forall>L\<in># pure_lits. \<forall>C\<in>#N. -L \<notin># C)\<close>

lemma preprocess_preprocess_inv:
  \<open>preprocess tauto_lits pure_lits C tauto_lits' pure_lits' D \<Longrightarrow>
    preprocess_inv C pure_lits \<Longrightarrow> preprocess_inv D pure_lits'\<close>
  by (induction rule: preprocess.induct) (auto simp: preprocess_inv_def)

lemma true_cls_mset_add_mset[simp]: \<open>I \<Turnstile>m add_mset C CC \<longleftrightarrow> I \<Turnstile> C \<and> I \<Turnstile>m CC\<close>
  by (auto simp: true_cls_mset_def)

lemma patch_model_preprocess_tautology_add_mset:
  \<open>set_mset (patch_model_preprocess (add_mset L tauto_lits) pure_lits I) =
    (set_mset (patch_model_preprocess tauto_lits pure_lits I)) \<union>
    (if Pos L \<in># I \<or> Neg L \<in># I then {} else {Pos L})\<close>
  unfolding patch_model_preprocess_def by auto

lemma true_cls_mono_left:
  "I \<subseteq> J \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> J \<Turnstile>m CC"
  unfolding true_cls_mset_def
  using true_cls_mono_set_mset_l by blast

lemma true_cls_mono_insert:
  "I \<Turnstile>m CC \<Longrightarrow> insert a I \<Turnstile>m CC"
  unfolding true_cls_mset_def by fastforce


lemma in_patch_model_preprocessD:
   \<open>L \<in># I \<Longrightarrow> L \<in># patch_model_preprocess tauto_lits pure_lits I \<or>
    - L \<in># patch_model_preprocess tauto_lits pure_lits I\<close>
  unfolding patch_model_preprocess_def apply (cases L) apply auto
   apply (metis (no_types, lifting) in_image_uminus_uminus in_multiset_minus_notin_snd
      multiset.set_map uminus_Pos)
   apply (metis (no_types, lifting) in_image_uminus_uminus in_multiset_minus_notin_snd
      multiset.set_map uminus_Neg)
  done

(*
lemma
  \<open>preprocess tauto_lits pure_lits C tauto_lits' pure_lits' D \<Longrightarrow>
    preprocess_inv C pure_lits \<Longrightarrow>
   set_mset (patch_model_preprocess tauto_lits pure_lits I) \<Turnstile>m C \<longleftrightarrow>
  set_mset (patch_model_preprocess tauto_lits' pure_lits' I) \<Turnstile>m D\<close>
  apply (induction rule: preprocess.induct)
  subgoal by (auto simp: preprocess_inv_def)
  subgoal by (auto simp: preprocess_inv_def)
  subgoal for tauto_lits pure_lits L C N
    apply (cases L)
    apply (auto intro:  simp: patch_model_preprocess_tautology_add_mset true_cls_mono_insert
        dest: in_patch_model_preprocessD)
    sorry
  subgoal for L C N tauto_lits pure_lits
    apply (auto intro:  simp: patch_model_preprocess_tautology_add_mset true_cls_mono_insert
        dest: in_patch_model_preprocessD)
 *)

lemma preprocess_less:
  \<open>preprocess tauto_lits pure_lits C tauto_lits' pure_lits' D \<Longrightarrow> D < C\<close>
  by (induction rule: preprocess.induct) auto

lemma preprocess_satisfiable_imp:
  \<open>preprocess tauto_lits pure_lits C tauto_lits pure_lits D \<Longrightarrow> satisfiable (set_mset C) \<Longrightarrow> satisfiable (set_mset D)\<close>
  by (induction rule: preprocess.induct) (auto simp: satisfiable_def)

lemma preprocess_satisfiable_rev:
  \<open>preprocess tauto_lits pure_lits C tauto_lits' pure_lits' D \<Longrightarrow> satisfiable (set_mset D) \<Longrightarrow> satisfiable (set_mset C)\<close>
proof (induction rule: preprocess.induct)
  case (rem_dups_lits tauto_lits pure_lits L C N)
  then show ?case by (auto simp: satisfiable_def)
next
  case (rem_dups_cls tauto_lits pure_lits C N)
  then show ?case by (auto simp: satisfiable_def)
next
  case (rem_tautology tauto_lits pure_lits L C N)
  then obtain I where
    I: \<open>(I \<Turnstile>sm N \<and> consistent_interp I) \<and> total_over_m I (set_mset N)\<close> (is \<open>?P I N \<and> total_over_m _ _\<close>)
    unfolding satisfiable_def by auto
  let ?I = \<open>if L \<in> I \<or> - L \<in> I then I else insert L I\<close>
  have \<open>?P ?I (add_mset (add_mset L (add_mset (- L) C)) N)\<close>
    using I true_cls_mset_increasing_r[of _ _ \<open>{L}\<close>] by auto
  then show ?case
    using satisfiable_carac' by blast
next
  case (pure_literal_deletion L C N)
  then obtain I where
    I: \<open>(I \<Turnstile>sm N \<and> consistent_interp I) \<and> total_over_m I (set_mset N)\<close> (is \<open>?P I N \<and> total_over_m _ _\<close>)
    unfolding satisfiable_def by auto
  have I_N: \<open>I - {- L} \<Turnstile>m N\<close>
    using pure_literal_deletion(1) I by (auto simp: true_cls_mset_def true_cls_def)
  let ?I = \<open>insert L (I - {-L})\<close>
  have I_C: \<open>?I \<Turnstile> add_mset L C\<close>
    by (auto dest: multi_member_split)
  have cons: \<open>consistent_interp (insert L (I - {- L}))\<close>
    using I by (metis Diff_empty Diff_iff Diff_insert0 consistent_interp_insert_iff insert_Diff
        singletonI)
  have \<open>?P ?I (add_mset (add_mset L C) N)\<close>
    using I true_cls_mset_increasing_r[of _ _ \<open>{L}\<close>] I_N I_C cons by auto
  then show ?case
    using satisfiable_carac' by blast
qed

definition nth_if_possible where
  \<open>nth_if_possible def xs i =
    (if i < length xs then (xs, xs ! i) else (xs, def))\<close>

definition condense_clause_loop_inv where
  \<open>condense_clause_loop_inv C =
     (\<lambda>(i, E, D, failed). E = mset (take i D) \<and> (failed \<longrightarrow> tautology (mset D)) \<and> set D = set C)\<close>

definition condense_clause where
  \<open>condense_clause C E =
     WHILE\<^sub>T\<^bsup>condense_clause_loop_inv C\<^esup>
       (\<lambda>(i, E, C, failed). \<not>failed \<and> i < length C)
       (\<lambda>(i, E, C, failed). do {
          ASSERT(i < length C);
          if C!i \<in># E
          then RETURN (i, E, delete_index_and_swap C i, False)
          else if -C!i \<in># E
          then RETURN (i, E, C, True)
          else RETURN (i+1, add_mset (C!i) E, C, False)
       })
     (0, E, C, False)\<close>

lemma
  \<open>condense_clause C {#} \<le> SPEC(\<lambda>(i, E, C, failed).
    (failed \<longrightarrow> tautology (mset C) \<and>
    (\<not>failed \<longrightarrow> (C = remdups C
     ))))\<close>
proof -
  have init: \<open>condense_clause_loop_inv C (0, {#}, C, False)\<close>
    unfolding condense_clause_loop_inv_def by auto
  have step: \<open>condense_clause_loop_inv C
       (i, E, delete_index_and_swap D i, False)\<close>
    if
      inv: \<open>condense_clause_loop_inv C s\<close> and
      \<open>case s of (i, E, C, failed) \<Rightarrow> \<not> failed \<and> i < length C\<close> and
      s: \<open>s = (i, s')\<close> \<open>s' = (E, s'')\<close> \<open>s'' = (D, failed)\<close> and
      i_C: \<open>i < length D\<close> and
      C_E: \<open>D ! i \<in># E\<close>
    for s i s' E s'' failed and D :: \<open>'a clause_l\<close>
  proof -
    have E: \<open>E = mset (take i D)\<close> and \<open>failed \<longrightarrow> tautology (mset D)\<close> and D_C: \<open>set D = set C\<close>
      using inv unfolding condense_clause_loop_inv_def s by auto
    have C1: \<open>D = take i D @ D ! i  # drop (Suc i) D\<close>
      by (simp add: Cons_nth_drop_Suc i_C)
    have C2: \<open>delete_index_and_swap D i = take i D @ butlast (last D  # drop (Suc i) D)\<close>
      using i_C apply (subst C1)
      apply (auto simp add: butlast_update'[symmetric])
      by (metis C1 WB_List_More.butlast_list_update butlast.simps(2) butlast_update' drop_eq_Nil i_C)

    have C: \<open>set (delete_index_and_swap D i) = set D\<close>
      apply (subst (2)C1)
      apply (subst C2)
      using i_C E C_E
      apply (auto dest!: in_set_butlastD simp: last_in_set not_less)
       apply (metis List.last_in_set drop_eq_Nil last_drop not_less)
      by (smt Cons_nth_drop_Suc append_butlast_last_id butlast.simps(2) drop_eq_Nil
          i_C in_set_conv_nth last.simps last_drop length_Cons length_butlast length_tl less_Suc_eq
          list.sel(3) nth_append_length nth_butlast)
    show ?thesis
      using C E i_C D_C unfolding condense_clause_loop_inv_def by (clarsimp simp: take_butlast)
  qed
  have step_tauto: \<open>condense_clause_loop_inv C (i, E, D, True)\<close>
    if
      inv: \<open>condense_clause_loop_inv C s\<close> and
      \<open>case s of (i, E, C, failed) \<Rightarrow> \<not> failed \<and> i < length C\<close> and
      s: \<open>s = (i, s')\<close> \<open>s' = (E, s'')\<close> \<open>s'' = (D, failed)\<close> and
      i_D: \<open>i < length D\<close> and
      \<open>D ! i \<notin># E\<close> and
      ui_E: \<open>- D ! i \<in># E\<close>
    for s i s' E s'' D failed
  proof -
    have E: \<open>E = mset (take i D)\<close> and \<open>failed \<longrightarrow> tautology (mset D)\<close> and D_C: \<open>set D = set C\<close>
      using inv unfolding condense_clause_loop_inv_def s by auto
    have \<open>- D ! i \<in> set D\<close> and \<open>D ! i \<in> set D\<close>
      using ui_E E i_D by (auto dest: in_set_takeD)
    then have \<open>tautology (mset D)\<close>
      unfolding tautology_decomp' by auto
    then show ?thesis
      unfolding condense_clause_loop_inv_def by (clarsimp simp: take_butlast E D_C)
  qed
  have inv_add: \<open>condense_clause_loop_inv C
       (i + 1, add_mset (D ! i) E, D, False)\<close>
    if
      inv: \<open>condense_clause_loop_inv C s\<close> and
      \<open>case s of (i, E, C, failed) \<Rightarrow> \<not> failed \<and> i < length C\<close> and
      s: \<open>s = (i, s')\<close> \<open>s' = (E, s'')\<close> \<open>s'' = (D, failed)\<close> and
      i_D: \<open>i < length D\<close> and
      \<open>D ! i \<notin># E\<close> and
      \<open>- D ! i \<notin># E\<close>
    for s i s' E s'' D failed
  proof -
    have E: \<open>E = mset (take i D)\<close> and \<open>failed \<longrightarrow> tautology (mset D)\<close> and D_C: \<open>set D = set C\<close>
      using inv unfolding condense_clause_loop_inv_def s by auto
    show ?thesis
      using i_D unfolding condense_clause_loop_inv_def by (auto simp: take_butlast E D_C take_Suc_conv_app_nth)
  qed
  show ?thesis
    unfolding condense_clause_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, E, C, failed). Suc (length C - i - If failed 1 0))\<close>])
    subgoal by auto
    subgoal by (rule init)
    subgoal by auto
    subgoal by (rule step)
    subgoal by auto
    subgoal by (rule step_tauto)
    subgoal by auto
    subgoal by (rule inv_add)
    subgoal by simp
    subgoal unfolding condense_clause_loop_inv_def by auto
    subgoal by auto
    done
qed


definition empty_clause_helper where
  \<open>empty_clause_helper C E max_index =
     WHILE\<^sub>T
       (\<lambda>(i, E). i < max_index)
       (\<lambda>(i, E). RETURN (i+1, remove1_mset (C!i) E) )
     (0, E)\<close>


end
