(*  Title:       An Executable Simple Ordered Resolution Prover for First-Order Clauses
    Author:      Dmitriy Traytel <TODO>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Executable Simple Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
TODO.
\<close>

theory Executable_FO_Ordered_Resolution_Prover
  imports Deterministic_FO_Ordered_Resolution_Prover IsaFoR_IsaFoR_Term
begin

global_interpretation deterministic_FO_resolution_prover where
  S = "\<lambda>_. {#}" and
  subst_atm = "op \<cdot>" and
  id_subst = "Var :: _ \<Rightarrow> ('f :: weighted, nat) term" and
  comp_subst = "op \<circ>\<^sub>s" and
  renamings_apart = renamings_apart and
  atm_of_atms = "Fun undefined" and
  mgu = mgu_sets and
  lessatm = less_kbo and
  size_atm = size and
  generation_factor = 1 and
  size_factor = 1
  by (unfold_locales)
    (auto simp: less_kbo_subst is_ground_atm_ground less_kbo_less intro: ground_less_less_kbo)

print_theorems

end
