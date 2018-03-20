theory Watched_Literals_Algorithm_Enumeration
  imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Enumeration
begin

definition cdcl_twl_enum_inv where
  \<open>cdcl_twl_enum_inv S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S\<close>

definition equisatisfiable :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>equisatisfiable N N' \<longleftrightarrow> (\<forall>M. M \<Turnstile>sm N \<longleftrightarrow> M \<Turnstile>sm N')\<close>

definition enum_equisatisfiable_st_clss :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_equisatisfiable_st_clss = {(S, (M, N)). equisatisfiable (clauses (get_clauses S)) N}\<close>

definition enum_model_st :: \<open>('v twl_st \<times> ('v literal list option \<times> 'v clauses)) set\<close> where
  \<open>enum_model_st = {(S, (M, N)).
         equisatisfiable (add_mset (DECO_clause (get_trail S)) (clauses (get_clauses S))) N \<and>
         (get_conflict S \<noteq> None \<longrightarrow> M \<noteq> None \<and> lits_of_l (get_trail S) = set (the M)) \<and>
         (get_conflict S = None \<longrightarrow> M = None)}\<close>


fun add_to_init_cls :: \<open>'v twl_cls \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st\<close> where
  \<open>add_to_init_cls C (M, N, U, D, NE, UE, WS, Q) = (M, add_mset C N, U, D, NE, UE, WS, Q)\<close>

context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

definition cdcl_twl_enum :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>cdcl_twl_enum S = do {
     S \<leftarrow> conclusive_TWL_run S;
     WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S \<noteq> None \<and> P (lits_of_l (get_trail S)))
       (\<lambda>S. do {
             S \<leftarrow> SPEC (negate_model_and_add S);
             conclusive_TWL_run S
           })
       S
    }\<close>

definition next_model_filtered_nres where
  \<open>next_model_filtered_nres N = 
    SPEC (\<lambda>M. full (next_model_filtered P) N M)\<close>

lemma
  \<open>(cdcl_twl_enum, next_model_filtered_nres) \<in> 
    enum_equisatisfiable_st_clss \<rightarrow>\<^sub>f \<langle>enum_model_st\<rangle>nres_rel\<close>
proof -
  define model_if_exists where
    \<open>model_if_exists S \<equiv> \<lambda>M. 
      (if no_step (next_model_filtered P) S then M=S else next_model_filtered P S M)\<close>
      for S :: \<open>_ \<times> 'v clauses\<close>
  have \<open>full (next_model_filtered P) S U \<longleftrightarrow>  
         (\<exists>T. model_if_exists S T \<and> full (next_model_filtered P) T U)\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
    for S U
  proof
    assume ?A
    then consider
      (nss) \<open>no_step (next_model_filtered P) S\<close> |
      (s1) T where \<open>(next_model_filtered P) S T\<close> and \<open>full (next_model_filtered P) T U\<close>
      unfolding full_def
      by (metis converse_rtranclpE)
    then show ?B
    proof cases
      case nss
      then have \<open>model_if_exists S S\<close>
        unfolding model_if_exists_def by simp
      then show ?B
        using \<open>?A\<close> by blast
    next
      case (s1 T)
      then have \<open>model_if_exists S T\<close>
        unfolding model_if_exists_def
        by meson
      then show ?B
        using s1 by blast
    qed
  next
    assume ?B
    then show ?A
      by (auto simp: model_if_exists_def full1_is_full full_fullI split: if_splits)
  qed
  then have next_model_filtered_nres_alt_def: \<open>next_model_filtered_nres  = (\<lambda>S. do {
         S \<leftarrow> SPEC (model_if_exists S);
         SPEC (\<lambda>T. full (next_model_filtered P) S T)
       })\<close>
    apply (intro ext)
    unfolding next_model_filtered_nres_def (* model_if_exists_def *) RES_RES_RETURN_RES
    by fast
  have \<open>conclusive_TWL_run S
      \<le> \<Down> enum_model_st
          (SPEC (model_if_exists MN))\<close>
    if
      \<open>(S, MN) \<in> {(S, M, y). equisatisfiable (clauses (get_clauses S)) y}\<close>
    for S MN
  proof -
    show ?thesis
      unfolding conclusive_TWL_run_def
      apply (auto simp: enum_model_st_def RES_refine
          intro!: RES_refine)
      sorry
  qed
  show ?thesis
    unfolding cdcl_twl_enum_def enum_equisatisfiable_st_clss_def  next_model_filtered_nres_alt_def
    apply (intro frefI nres_relI)
    apply refine_vcg
    subgoal for S MN
      explore_have
  oops

end

end