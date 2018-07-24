theory Splitting_Calculus
  imports "Ordered_Resolution_Prover.Proving_Process"
begin

datatype ('a, 'b) aclause =
  AClause (clause_of: "'a clause") (asserts_of: "'b literal set")

datatype ('a, 'b) ainference =
  AInfer (aside_prems_of: "('a, 'b) aclause multiset") (amain_prem_of: "('a, 'b) aclause")
    (araw_concl_of: "'a clause")

abbreviation aprems_of :: "('a, 'b) ainference \<Rightarrow> ('a, 'b) aclause multiset" where
  "aprems_of \<gamma> \<equiv> aside_prems_of \<gamma> + {#amain_prem_of \<gamma>#}"

definition aconcl_of where
  "aconcl_of \<gamma> = AClause (araw_concl_of \<gamma>) (\<Union>a \<in> set_mset (aprems_of \<gamma>). asserts_of a)"

abbreviation aconcls_of :: "('a, 'b) ainference set \<Rightarrow> ('a, 'b) aclause set" where
  "aconcls_of \<Gamma> \<equiv> aconcl_of ` \<Gamma>"

abbreviation ainfer_from :: "('a, 'b) aclause set \<Rightarrow> ('a, 'b) ainference \<Rightarrow> bool" where
  "ainfer_from CC \<gamma> \<equiv> set_mset (aprems_of \<gamma>) \<subseteq> CC"

fun infer_of_ainfer :: "('a, 'b) ainference \<Rightarrow> 'a inference"  where
  "infer_of_ainfer (AInfer CC D E) = Infer (image_mset clause_of CC) (clause_of D) E"

locale splitting_calculus = redundancy_criterion +
  fixes quote :: "'a clause \<Rightarrow> 'b literal"
  (* assumes properties of quote *)
begin

definition a\<Gamma> :: "('a, 'b) ainference set" where
  "a\<Gamma> = {\<gamma>. infer_of_ainfer \<gamma> \<in> \<Gamma> (* \<and> check that assertions are consistent *)}"


(*
lemma sound_preserve: 

lemma refute_complete_preserve:
*)

end

end
