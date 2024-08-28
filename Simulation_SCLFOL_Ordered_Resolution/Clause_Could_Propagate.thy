theory Clause_Could_Propagate
  imports
    Background
    Implicit_Exhaustive_Factorization
begin

context simulation_SCLFOL_ground_ordered_resolution begin

definition clause_could_propagate where
  "clause_could_propagate \<Gamma> C L \<longleftrightarrow> \<not> trail_defined_lit \<Gamma> L \<and>
    linorder_lit.is_maximal_in_mset C L \<and> trail_false_cls \<Gamma> {#K \<in># C. K \<noteq> L#}"

lemma trail_false_if_could_have_propagatated:
  "clause_could_propagate \<Gamma> C L \<Longrightarrow> trail_false_cls ((- L, n) # \<Gamma>) C"
  unfolding clause_could_propagate_def trail_false_cls_def trail_false_lit_def by auto

lemma atoms_of_trail_lt_atom_of_propagatable_literal:
  assumes
    \<Gamma>_lower: "linorder_trm.is_lower_set (fset (trail_atms \<Gamma>)) \<A>" and
    C_prop: "clause_could_propagate \<Gamma> C L" and
    "atm_of L \<in> \<A>"
  shows "\<forall>A |\<in>| trail_atms \<Gamma>. A \<prec>\<^sub>t atm_of L"
proof -
  have "atm_of L |\<notin>| trail_atms \<Gamma>"
    using C_prop
    unfolding clause_could_propagate_def trail_defined_lit_iff_trail_defined_atm
    by argo

  then show ?thesis
    using \<Gamma>_lower \<open>atm_of L \<in> \<A>\<close>
    by (metis linorder_trm.is_lower_set_iff linorder_trm.neqE)
qed

lemma trail_false_cls_filter_mset_iff:
  "trail_false_cls \<Gamma> {#Ka \<in># C. Ka \<noteq> K#} \<longleftrightarrow> (\<forall>L\<in>#C. L \<noteq> K \<longrightarrow> trail_false_lit \<Gamma> L)"
  unfolding trail_false_cls_def by auto

lemma clause_could_propagate_iff: "clause_could_propagate \<Gamma> C K \<longleftrightarrow>
  \<not> trail_defined_lit \<Gamma> K \<and> ord_res.is_maximal_lit K C \<and> (\<forall>L\<in>#C. L \<noteq> K \<longrightarrow> trail_false_lit \<Gamma> L)"
  unfolding clause_could_propagate_def trail_false_cls_filter_mset_iff ..

lemma clause_could_propagate_efac: "clause_could_propagate \<Gamma> (efac C) = clause_could_propagate \<Gamma> C"
proof (rule ext)
  fix L
  show "clause_could_propagate \<Gamma> (efac C) L \<longleftrightarrow> clause_could_propagate \<Gamma> C L"
    unfolding clause_could_propagate_def
    by (metis (mono_tags, lifting) ex1_efac_eq_factoring_chain mem_Collect_eq
        ord_res.ground_factorings_preserves_maximal_literal set_mset_efac set_mset_filter
        trail_false_cls_def)
qed

lemma bex_clause_could_propagate_simp:
  fixes \<F> N \<Gamma> L
  shows "fBex (iefac \<F> |`| N) (\<lambda>C. clause_could_propagate \<Gamma> C L) \<longleftrightarrow>
    fBex N (\<lambda>C. clause_could_propagate \<Gamma> C L)"
  sketch (rule iffI; elim bexE)
proof (rule iffI ; elim bexE)
  fix C :: "'f gclause"
  assume "C |\<in>| iefac \<F> |`| N" and "clause_could_propagate \<Gamma> C L"
  thus "\<exists>C |\<in>| N. clause_could_propagate \<Gamma> C L"
    by (metis clause_could_propagate_efac fimageE iefac_def)
next
  fix C :: "'f gclause"
  assume "C |\<in>| N" and "clause_could_propagate \<Gamma> C L"
  thus "\<exists>C|\<in>|iefac \<F> |`| N. clause_could_propagate \<Gamma> C L"
    by (metis clause_could_propagate_efac fimageI iefac_def)
qed

end

end