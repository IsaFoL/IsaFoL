theory Ceta_SAT_Code
  imports CeTA_SAT.Ceta_SAT
begin

lemma [code del]: "mset xs - mset ys = mset (fold remove1 ys xs)"
  by (rule sym, induct ys arbitrary: xs) (simp_all add: diff_add diff_right_commute diff_diff_add)

export_code certify_proof
Certified Unsupported Error Inl Inr sumbot
(* remove, after defining an XML format: *)
  Yes No Terminating Upperbound Nonterminating Confluent Nonconfluent Completed Anything 
  nat_of_integer
  in Haskell module_name Ceta

term certify_proof

export_code certify_proof
  in SML_imp module_name Ceta

end