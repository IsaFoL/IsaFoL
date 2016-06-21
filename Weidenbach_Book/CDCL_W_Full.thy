theory CDCL_W_Full
imports CDCL_W_Termination CDCL_WNOT
begin

context conflict_driven_clause_learning\<^sub>W
begin
lemma rtranclp_cdcl\<^sub>W_merge_stgy_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv R" and
  st: "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and
  dist: "distinct_mset (clauses R)" and
  R: "trail R = []"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF invR _ dist R]
  invR st rtranclp_mono[of cdcl\<^sub>W_s' "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*"] cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy
  by (auto dest!: cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_s')
end

end