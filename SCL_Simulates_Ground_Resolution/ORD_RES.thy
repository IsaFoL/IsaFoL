theory ORD_RES
  imports Background
begin

section \<open>ORD-RES\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

lemma "ex_false_clause N \<longleftrightarrow> \<not> (\<forall>C \<in> N. ord_res_Interp N C \<TTurnstile> C)"
  unfolding ex_false_clause_def by metis

lemma "\<not> ex_false_clause N \<longleftrightarrow> (\<forall>C \<in> N. ord_res_Interp N C \<TTurnstile> C)"
  unfolding ex_false_clause_def by metis

definition ord_res_final where
  "ord_res_final N \<longleftrightarrow> {#} |\<in>| N \<or> \<not> ex_false_clause (fset N)"

inductive ord_res where
  factoring: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    \<comment> \<open>Maybe write \<^term>\<open>\<not> ord_res_final N\<close> instead?\<close>
    P |\<in>| N \<Longrightarrow> ord_res.ground_factoring P C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'" |

  resolution: "{#} |\<notin>| N \<Longrightarrow> ex_false_clause (fset N) \<Longrightarrow>
    P1 |\<in>| N \<Longrightarrow> P2 |\<in>| N \<Longrightarrow> ord_res.ground_resolution P1 P2 C \<Longrightarrow>
    N' = finsert C N \<Longrightarrow>
    ord_res N N'"

inductive ord_res_load where
  "N \<noteq> {||} \<Longrightarrow> ord_res_load N N"

sublocale ord_res_semantics: semantics where
  step = ord_res and
  final = ord_res_final
proof unfold_locales
  fix N :: "'f gterm clause fset"
  assume "ord_res_final N"
  thus "finished ord_res N"
    unfolding ord_res_final_def
  proof (elim disjE)
    show "{#} |\<in>| N \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  next
    show "\<not> ex_false_clause (fset N) \<Longrightarrow> finished ord_res N"
      by (simp add: finished_def ord_res.simps)
  qed
qed

sublocale ord_res_language: language where
  step = ord_res and
  final = ord_res_final and
  load = ord_res_load
  by unfold_locales

end

end