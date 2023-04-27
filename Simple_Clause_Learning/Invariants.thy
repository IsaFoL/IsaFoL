theory Invariants
  imports SCL_FOL
begin

text \<open>The following lemma restate existing invariants in a compact, paper-friendly way.\<close>

lemma (in scl_fol_calculus) scl_state_invariants:
  shows
    inv_trail_lits_ground:
      "trail_lits_ground initial_state"
      "scl N \<beta> S S' \<Longrightarrow> trail_lits_ground S \<Longrightarrow> trail_lits_ground S'" and
    inv_trail_atoms_lt:
      "trail_atoms_lt \<beta> initial_state"
      "scl N \<beta> S S' \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> trail_atoms_lt \<beta> S'" and
    inv_undefined_trail_lits:
      "\<forall>\<Gamma>' Ln \<Gamma>''. state_trail initial_state = \<Gamma>'' @ Ln # \<Gamma>' \<longrightarrow> \<not> trail_defined_lit \<Gamma>' (fst Ln)"
      "scl N \<beta> S S' \<Longrightarrow>
        (\<forall>\<Gamma>' Ln \<Gamma>''. state_trail S = \<Gamma>'' @ Ln # \<Gamma>' \<longrightarrow> \<not> trail_defined_lit \<Gamma>' (fst Ln)) \<Longrightarrow>
        (\<forall>\<Gamma>' Ln \<Gamma>''. state_trail S' = \<Gamma>'' @ Ln # \<Gamma>' \<longrightarrow> \<not> trail_defined_lit \<Gamma>' (fst Ln))" and
    inv_ground_closures:
      "ground_closures initial_state"
      "scl N \<beta> S S' \<Longrightarrow> ground_closures S \<Longrightarrow> ground_closures S'" and
    inv_ground_false_closures:
      "ground_false_closures initial_state"
      "scl N \<beta> S S' \<Longrightarrow> ground_false_closures S \<Longrightarrow> ground_false_closures S'" and
    inv_trail_propagated_lits_wf:
      "\<forall>\<K>\<in>set (state_trail initial_state). \<forall>D K \<gamma>. snd \<K> = Some (D, K, \<gamma>) \<longrightarrow> fst \<K> = K \<cdot>l \<gamma>"
      "scl N \<beta> S S' \<Longrightarrow>
        (\<forall>\<K>\<in>set (state_trail S). \<forall>D K \<gamma>. snd \<K> = Some (D, K, \<gamma>) \<longrightarrow> fst \<K> = K \<cdot>l \<gamma>) \<Longrightarrow>
        (\<forall>\<K>\<in>set (state_trail S'). \<forall>D K \<gamma>. snd \<K> = Some (D, K, \<gamma>) \<longrightarrow> fst \<K> = K \<cdot>l \<gamma>)" and
    inv_trail_resolved_lits_pol:
      "trail_resolved_lits_pol initial_state"
      "scl N \<beta> S S' \<Longrightarrow> trail_resolved_lits_pol S \<Longrightarrow> trail_resolved_lits_pol S'" and
    inv_initial_lits_generalize_learned_trail_conflict:
      "initial_lits_generalize_learned_trail_conflict N initial_state"
      "scl N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S'" and
    inv_trail_lits_from_clauses:
      "trail_lits_from_clauses N initial_state"
      "scl N \<beta> S S' \<Longrightarrow> trail_lits_from_clauses N S \<Longrightarrow> trail_lits_from_clauses N S'" and
    inv_sound_state:
      "sound_state N \<beta> initial_state"
      "scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  using trail_lits_ground_initial_state scl_preserves_trail_lits_ground
  using trail_atoms_lt_initial_state scl_preserves_trail_atoms_lt
  using trail_lits_consistent_initial_state[unfolded trail_lits_consistent_def trail_consistent_iff]
    scl_preserves_trail_lits_consistent[unfolded trail_lits_consistent_def trail_consistent_iff]
  using ground_closures_initial_state scl_preserves_ground_closures
  using ground_false_closures_initial_state scl_preserves_ground_false_closures
  using trail_propagated_lit_wf_initial_state scl_preserves_trail_propagated_lit_wf
  using trail_resolved_lits_pol_initial_state scl_preserves_trail_resolved_lits_pol
  using initial_lits_generalize_learned_trail_conflict_initial_state
    scl_preserves_initial_lits_generalize_learned_trail_conflict
  using trail_lits_from_clauses_initial_state scl_preserves_trail_lits_from_clauses
  using sound_initial_state scl_preserves_sound_state
  by metis+

end