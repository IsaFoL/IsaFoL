theory DPLL_W_Partial_Encoding
imports
  DPLL_W_Optimal_Model
  CDCL_W_Partial_Encoding
begin

locale dpll_optimal_encoding_opt =
  dpll\<^sub>W_state_optimal_weight trail clauses
    tl_trail cons_trail state_eq state   \<rho> update_additional_info +
  optimal_encoding_opt_ops \<Sigma> \<Delta>\<Sigma> new_vars 
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin

end


locale dpll_optimal_encoding =
  dpll_optimal_encoding_opt trail clauses
    tl_trail cons_trail state_eq state
    update_additional_info \<Sigma> \<Delta>\<Sigma> \<rho> new_vars  +
  optimal_encoding_ops
    \<Sigma> \<Delta>\<Sigma>
    new_vars \<rho>
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin


end

end