(*<*)
section \<open>Importing all Theories\<close>

theory Weidenbach_Book
imports
  Normalisation.Prop_Normalisation
  Normalisation.Prop_Logic_Multiset

  Resolution_Superposition.Prop_Resolution

  Resolution_Superposition.Prop_Superposition

  CDCL.DPLL_W
  CDCL.CDCL_W_Level
  CDCL.CDCL_W
  CDCL.CDCL_W_Termination
  CDCL.CDCL_W_Merge
  CDCL.CDCL_NOT
  CDCL.CDCL_WNOT
  CDCL.CDCL_W_Restart
  CDCL.CDCL_W_Incremental
  CDCL.DPLL_CDCL_W_Implementation
  CDCL.DPLL_W_Implementation
  CDCL.CDCL_W_Implementation
  CDCL.CDCL_W_Optimal_Model

  IsaSAT.IsaSAT
begin
text \<open>This theory imports all the other theories (and is not needed in the documentation,
just as a sanity check that everything works).\<close>

end
(*>*)
