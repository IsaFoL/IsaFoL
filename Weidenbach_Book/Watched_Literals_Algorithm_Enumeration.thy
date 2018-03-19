theory Watched_Literals_Algorithm_Enumeration
  imports Watched_Literals_Algorithm Watched_Literals_Transition_System_Enumeration
begin

definition cdcl_twl_enum_inv where
  \<open>cdcl_twl_enum_inv S \<longleftrightarrow> twl_struct_invs S \<and> twl_stgy_invs S\<close>

definition equisatisfiable :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
\<open>equisatisfiable N N' \<longleftrightarrow> (\<forall>M. M \<Turnstile>sm N \<longleftrightarrow> M \<Turnstile>sm N')\<close>

definition enum_equisatisfiable_st_clss :: \<open>('v twl_st \<times> 'v clauses) set\<close> where
  \<open>enum_equisatisfiable_st_clss = {(S, N). equisatisfiable (clauses (get_clauses S)) N}\<close>

definition enum_model_st :: \<open>('v twl_st \<times> 'v literal list option) set\<close> where
  \<open>enum_model_st = {(S, M).
         (get_conflict S \<noteq> None \<longrightarrow> M \<noteq> None \<and> lits_of_l (get_trail S) = set (the M)) \<and>
         (get_conflict S = None \<longrightarrow> M = None)}\<close>


context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

definition cdcl_twl_enum :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close>where
  \<open>cdcl_twl_enum S = do {
     S \<leftarrow> conclusive_TWL_run S;
     WHILE\<^sub>T\<^bsup>cdcl_twl_enum_inv\<^esup>
       (\<lambda>S. get_conflict S \<noteq> None \<and> P (lits_of_l (get_trail S)))
       (\<lambda>S. conclusive_TWL_run S)
       S
    }\<close>

lemma enumerate_model_unless_alt_def:
  \<open>RETURN (enumerate_model_unless P N) = do {
     let MN = (N, get_option_model N);
     (N, M) \<leftarrow> WHILE\<^sub>T (\<lambda>(N, M). M \<noteq> None \<and> \<not>P (set (the M)))
       (\<lambda>(N, M). do {
          let C = (image_mset uminus (mset (the M)));
          RETURN (add_mset C N, get_option_model (add_mset C N))
        })
       MN;
     RETURN M
   }\<close>
  apply (induction P N rule: enumerate_model_unless.induct)
  apply (subst enumerate_model_unless.simps)
  apply (subst WHILET_unfold)
  apply (auto split: option.splits)
  done

lemma
  \<open>(cdcl_twl_enum, RETURN o (enumerate_model_unless P)) \<in> 
    enum_equisatisfiable_st_clss \<rightarrow>\<^sub>f \<langle>enum_model_st\<rangle>nres_rel\<close>
  unfolding cdcl_twl_enum_def enum_equisatisfiable_st_clss_def
  apply (intro frefI nres_relI)
  apply simp
  apply (subst enumerate_model_unless_alt_def[abs_def])
  apply clarify
  apply refine_vcg
  oops

end

end