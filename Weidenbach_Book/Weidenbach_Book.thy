section \<open>Importing all Theories\<close>

theory Weidenbach_Book
imports
  Prop_Normalisation Prop_Logic_Multiset

  Prop_Resolution

  Prop_Superposition

  CDCL_NOT DPLL_NOT DPLL_W_Implementation CDCL_W_Incremental
  CDCL_WNOT

begin
text \<open>This theory imports all the other theories\<close>
end
