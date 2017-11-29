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
thm deterministic_FO_resolution_prover
global_interpretation deterministic_FO_resolution_prover "\<lambda>_. {#}"
  "op \<cdot>" "Var :: _ \<Rightarrow> ('f :: wellorder, nat) term" "op \<circ>\<^sub>s" renamings_apart "Fun undefined" mgu_sets
  apply (intro_locales)

end
