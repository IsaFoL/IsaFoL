(*  Title:       Dynamic_Completeness_Lifting
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Lifting a Single-Clause-Set Proving Process to a Given-Clause Prover\<close>

subsection \<open>Application to Bachmair and Ganzinger's Resolution Prover\<close>

theory Given_Clause_Prover_Lifting
  imports
    Dynamic_Completeness_Lifting
    Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
    "../lib/Explorer"
begin

context FO_resolution_prover
begin

end

end

