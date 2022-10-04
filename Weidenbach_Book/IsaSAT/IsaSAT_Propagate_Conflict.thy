theory IsaSAT_Propagate_Conflict
  imports IsaSAT_Setup IsaSAT_Inner_Propagation IsaSAT_Propagate_Conflict_Defs
begin


chapter \<open>Propagation Loop And Conflict\<close>

section \<open>Unit Propagation, Inner Loop\<close>

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur S L = length (watched_by_int S L)\<close>


lemma unit_propagation_inner_loop_wl_loop_D_heur_fast:
  \<open>length (get_clauses_wl_heur b) \<le> uint64_max \<Longrightarrow>
    unit_propagation_inner_loop_wl_loop_D_heur_inv b a (a1', a1'a, a2'a) \<Longrightarrow>
     length (get_clauses_wl_heur a2'a) \<le> uint64_max\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_inv_def
  by auto

lemma unit_propagation_inner_loop_wl_loop_D_heur_alt_def:
  \<open>unit_propagation_inner_loop_wl_loop_D_heur L S\<^sub>0 = do {
    ASSERT (length (watched_by_int S\<^sub>0 L) \<le> length (get_clauses_wl_heur S\<^sub>0));
    n \<leftarrow> mop_length_watched_by_int S\<^sub>0 L;
    let b = (0, 0, S\<^sub>0);
    WHILE\<^sub>T\<^bsup>unit_propagation_inner_loop_wl_loop_D_heur_inv S\<^sub>0 L\<^esup>
      (\<lambda>(j, w, S). w < n \<and> get_conflict_wl_is_None_heur S)
      (\<lambda>(j, w, S). do {
        unit_propagation_inner_loop_body_wl_heur L j w S
      })
      b
  }\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_heur_def Let_def
    IsaSAT_Profile.start_def IsaSAT_Profile.stop_def  ..


section \<open>Unit propagation, Outer Loop\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_alt_def:
  \<open>select_and_remove_from_literals_to_update_wl_heur =
   (\<lambda>S. do {
      let j = literals_to_update_wl_heur S;
      ASSERT(j < length (fst (get_trail_wl_heur S)));
      ASSERT(j + 1 \<le> uint32_max);
      L \<leftarrow> isa_trail_nth (get_trail_wl_heur S) j;
      RETURN (set_literals_to_update_wl_heur (j+1) S, -L)
     })
    \<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  apply (intro ext)
  apply (rename_tac S; case_tac S)
  by (auto intro!: ext simp: rev_trail_nth_def Let_def)

lemma unit_propagation_outer_loop_wl_D_heur_fast:
  \<open>length (get_clauses_wl_heur x) \<le> uint64_max \<Longrightarrow>
       unit_propagation_outer_loop_wl_D_heur_inv x s' \<Longrightarrow>
       length (get_clauses_wl_heur a1') =
       length (get_clauses_wl_heur s') \<Longrightarrow>
       length (get_clauses_wl_heur s') \<le> uint64_max\<close>
  by (auto simp: unit_propagation_outer_loop_wl_D_heur_inv_def)

theorem unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D:
  \<open>(unit_propagation_outer_loop_wl_D_heur, unit_propagation_outer_loop_wl) \<in>
    {(S, T). (S, T) \<in> twl_st_heur \<and> get_learned_count S = lcount} \<rightarrow>\<^sub>f
       \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> get_learned_count S = lcount}\<rangle> nres_rel\<close>
  using twl_st_heur''D_twl_st_heurD[OF
     unit_propagation_outer_loop_wl_D_heur_unit_propagation_outer_loop_wl_D']
  .

end
