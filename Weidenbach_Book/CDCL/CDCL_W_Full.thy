theory CDCL_W_Full
imports CDCL_W_Termination CDCL_WNOT
begin

context conflict_driven_clause_learning\<^sub>W
begin
lemma rtranclp_cdcl\<^sub>W_merge_stgy_distinct_mset_clauses:
  assumes
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    st: "cdcl\<^sub>W_s'\<^sup>*\<^sup>* R S" and
    smaller: \<open>no_smaller_propa R\<close> and
    dist: "distinct_mset (clauses R)"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF _ invR dist smaller]
  invR st rtranclp_mono[of cdcl\<^sub>W_s' "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*"] cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy
  by (auto dest!: cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy)
end

end
