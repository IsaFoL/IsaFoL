theory IsaSAT_Proofs
  imports IsaSAT_Setup
begin
section \<open>DRAT proof generation\<close>

text \<open>We do not prove anything about the proof we generate. In particular, it could be incorrect,
because some clauses is not printed.\<close>

definition log_literal :: \<open>nat literal \<Rightarrow> unit\<close> where
  \<open>log_literal _ = ()\<close>

definition log_start_new_clause :: \<open>nat \<Rightarrow> unit\<close> where
  \<open>log_start_new_clause _ = ()\<close>

definition log_start_del_clause :: \<open>nat \<Rightarrow> unit\<close> where
  \<open>log_start_del_clause _ = ()\<close>

definition log_end_clause :: \<open>nat \<Rightarrow> unit\<close> where
  \<open>log_end_clause _ = ()\<close>

definition log_clause_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> unit nres\<close> where
  \<open>log_clause_heur S C = do {
     i \<leftarrow> mop_arena_length_st S C;
     ASSERT (i \<le> length (get_clauses_wl_heur S));
     _ \<leftarrow> WHILE\<^sub>T (\<lambda>j. j < i)
       (\<lambda>j. do{ ASSERT (j<i);
               L \<leftarrow> mop_access_lit_in_clauses_heur S C j;
               let _ = log_literal L;
               RETURN (j+1)
        })
      0;
    RETURN ()
}\<close>

definition log_clause2 :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> unit nres\<close> where
  \<open>log_clause2 S C = do {
     ASSERT (C \<in># dom_m (get_clauses_wl S));
     let i = length (get_clauses_wl S \<propto> C);
     _ \<leftarrow> WHILE\<^sub>T (\<lambda>j. j < i)
       (\<lambda>j. do{
            ASSERT (j < i);
            let L = get_clauses_wl S \<propto> C ! j;
            let _ = log_literal L;
            RETURN (j+1)
        })
      0;
    RETURN ()
}\<close>

definition log_clause :: \<open>'v twl_st_wl \<Rightarrow> nat \<Rightarrow> unit\<close> where \<open>log_clause S _ = ()\<close>

lemma log_clause2_log_clause:
  \<open>(uncurry log_clause2, uncurry (RETURN oo log_clause)) \<in>
  [\<lambda>(S,C). C \<in># dom_m (get_clauses_wl S)]\<^sub>f Id \<times>\<^sub>r nat_rel \<rightarrow> \<langle>unit_rel\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding log_clause_def log_clause2_def comp_def uncurry_def mop_arena_length_st_def
    apply (intro frefI nres_relI)
    subgoal for x y
    apply (refine_vcg WHILET_rule[where I = \<open>\<lambda>_. True\<close> and R = \<open>measure (\<lambda>i. length (get_clauses_wl (fst y) \<propto> snd y) - i)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  done
qed

lemma log_clause_heur_log_clause2:
  assumes \<open>(S,T) \<in> twl_st_heur\<close> \<open>(C,C') \<in> nat_rel\<close>
  shows \<open>log_clause_heur S C \<le>\<Down>unit_rel (log_clause2 T C')\<close>
proof -
  have [refine0]: \<open>(0,0)\<in>nat_rel\<close>
    by auto
  have length: \<open>\<Down> nat_rel ((RETURN \<circ> (\<lambda>c. length (get_clauses_wl T \<propto> c))) C') \<le> SPEC (\<lambda>c. (c, length (get_clauses_wl T \<propto> C')) \<in> {(a,b). a=b \<and> a = length (get_clauses_wl T \<propto> C)})\<close>
    by (use assms in auto)
  show ?thesis
    unfolding log_clause_heur_def log_clause2_def comp_def uncurry_def mop_arena_length_st_def
      mop_access_lit_in_clauses_heur_def
    apply (refine_vcg mop_arena_lit[where vdom = \<open>set (get_vdom S)\<close> and N = \<open>get_clauses_wl T\<close>, THEN order_trans] 
      mop_arena_length[where vdom = \<open>set (get_vdom S)\<close>, THEN fref_to_Down_curry, THEN order_trans, unfolded prod.simps])
    apply assumption
    subgoal using assms by (auto simp: twl_st_heur_def)
    apply (rule length)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_def dest: arena_lifting(10)\<close>)
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_def)
    apply assumption
    subgoal by (use assms in auto)
    apply (rule refl)
    subgoal by auto
    by auto
qed


definition log_new_clause_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> unit nres\<close> where
  \<open>log_new_clause_heur S C = do {
    let _ = log_start_new_clause 0;
    log_clause_heur S C;
    let _ = log_end_clause 0;
    RETURN ()
  }\<close>

lemma log_new_clause_heur_alt_def:
  \<open>log_new_clause_heur = log_clause_heur\<close>
  by (auto intro!: ext simp: log_new_clause_heur_def log_clause_heur_def)

definition log_del_clause_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> unit nres\<close> where
  \<open>log_del_clause_heur S C = do {
    let _ = log_start_del_clause 0;
    log_clause_heur S C;
    let _ = log_end_clause 0;
    RETURN ()
  }\<close>

lemma log_del_clause_heur_alt_def:
  \<open>log_del_clause_heur = log_clause_heur\<close>
  by (auto intro!: ext simp: log_del_clause_heur_def log_clause_heur_def)

lemma log_new_clause_heur_log_clause:
  assumes \<open>(S,T) \<in> twl_st_heur\<close> \<open>(C,C') \<in> nat_rel\<close> \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>log_new_clause_heur S C \<le> SPEC (\<lambda>c. (c, log_clause T C') \<in> unit_rel)\<close>
    unfolding log_new_clause_heur_alt_def
    apply (rule log_clause_heur_log_clause2[THEN order_trans, OF assms(1,2)])
    apply (rule order_trans)
    apply (rule ref_two_step')
    apply (rule log_clause2_log_clause[THEN fref_to_Down_curry])
    using assms by auto

definition log_unit_clause where
  \<open>log_unit_clause L =
    (let _ = log_start_new_clause 0;
      _ = log_literal L;
      _ = log_end_clause 0 in
     ()
  )\<close>

text \<open>For removing unit literals, we cheat as usual: we signal to the C side which literals are in
and flush the clause if need be (without effect on the Isabelle side, because we neither want nor care
about the proofs).\<close>

definition mark_literal_for_unit_deletion :: \<open>nat literal \<Rightarrow> unit\<close> where
  \<open>mark_literal_for_unit_deletion _ = ()\<close>

definition mark_clause_for_unit_as_unchanged :: \<open>nat \<Rightarrow> unit\<close> where
  \<open>mark_clause_for_unit_as_unchanged _ = ()\<close>

definition mark_clause_for_unit_as_changed :: \<open>nat \<Rightarrow> unit\<close> where
  \<open>mark_clause_for_unit_as_changed _ = ()\<close>

end