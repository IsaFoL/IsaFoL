(*<*)
section \<open>Importing all Theories\<close>

theory Weidenbach_Book
imports
  Prop_Normalisation Prop_Logic_Multiset

  Prop_Resolution

  Prop_Superposition

  DPLL_W
  CDCL_W_Level
  CDCL_W
  CDCL_W_Termination
  CDCL_W_Merge
  CDCL_NOT
  CDCL_WNOT
  CDCL_W_Restart
  CDCL_W_Incremental
  CDCL_W_Optimal_Model
  DPLL_CDCL_W_Implementation
  DPLL_W_Implementation
  CDCL_W_Implementation

begin
text \<open>This theory imports all the other theories (and is not needed in the documentation).\<close>

end
(*>*)