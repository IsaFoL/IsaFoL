theory CDCL_Watched_Literals_IsaFoR
imports
  CeTA.Ceta
  Watched_Literals.CDCL_Watched_Literals_IsaSAT
begin

export_code certify_proof Certified Unsupported Error Inl Inr sumbot version
(* remove, after defining an XML format: *)
  Yes No Terminating Upperbound Nonterminating Confluent Nonconfluent Completed Anything nat_of_integer
  in Haskell module_name Ceta file "../../generated/Haskell/"

end

