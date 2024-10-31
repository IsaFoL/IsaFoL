theory Isabelle_2024_Compatibility
  imports
    Main
    "HOL-Library.Multiset"
begin

(*
lemmas wfP_def = wfp_def
lemmas wfP_if_convertible_to_wfP = wfp_if_convertible_to_wfp
lemmas wfP_imp_asymp = wfp_imp_asymp
lemmas wfP_induct_rule = wfp_induct_rule
lemmas wfP_multp = wfp_multp
*)

lemmas wfp_def = wfP_def
lemmas wfp_if_convertible_to_wfp = wfP_if_convertible_to_wfP
lemmas wfp_imp_asymp = wfP_imp_asymp
lemmas wfp_induct_rule = wfP_induct_rule
lemmas wfp_multp = wfP_multp
lemmas wfp_subset_mset = wfP_subset_mset

end
