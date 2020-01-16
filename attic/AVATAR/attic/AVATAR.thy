theory AVATAR
  imports
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    Ordered_Resolution_Prover.Inference_System
begin

type_synonym assertion = nat

datatype 'a aclause =
  AClause (clause_of: "'a clause") (asserts_of: "assertion set")

datatype 'a ainference =
  AInfer (aside_prems_of: "'a aclause multiset") (amain_prem_of: "'a aclause")
    (araw_concl_of: "'a clause")

abbreviation aprems_of :: "'a ainference \<Rightarrow> 'a aclause multiset" where
  "aprems_of \<gamma> \<equiv> aside_prems_of \<gamma> + {#amain_prem_of \<gamma>#}"

definition aconcl_of where
  "aconcl_of \<gamma> = AClause (araw_concl_of \<gamma>) (\<Union>a \<in> set_mset (aprems_of \<gamma>). asserts_of a)"

abbreviation aconcls_of :: "'a ainference set \<Rightarrow> 'a aclause set" where
  "aconcls_of \<Gamma> \<equiv> aconcl_of ` \<Gamma>"

abbreviation ainfer_from :: "'a aclause set \<Rightarrow> 'a ainference \<Rightarrow> bool" where
  "ainfer_from CC \<gamma> \<equiv> set_mset (aprems_of \<gamma>) \<subseteq> CC"

fun infer_of_ainfer :: "'a ainference \<Rightarrow> 'a inference"  where
  "infer_of_ainfer (AInfer CC D E) = Infer (image_mset clause_of CC) (clause_of D) E"

type_synonym ('a, 'b) astate =
  "'a aclause multiset option \<times> 'a aclause multiset \<times> 'a aclause multiset
   \<times> ('a \<Rightarrow> 'a aclause multiset) \<times> 'b aclause multiset \<times> 'b interp"

locale avatar = substitution subst_atm
    for subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" +
  fixes
    \<Gamma> :: "'a inference set" and
    abstract :: "'a aclause \<Rightarrow> 'b" and
    base_solver :: "'b multiset \<Rightarrow> 'b interp option"
begin

definition a\<Gamma> :: "'a ainference set" where
  "a\<Gamma> = {\<gamma>. infer_of_ainfer \<gamma> \<in> \<Gamma>}"

definition ainferences_from :: "'a aclause set \<Rightarrow> 'a ainference set" where
  "ainferences_from CC = {\<gamma>. \<gamma> \<in> a\<Gamma> \<and> ainfer_from CC \<gamma>}"

definition ainferences_between :: "'a aclause set \<Rightarrow> 'a aclause \<Rightarrow> 'a ainference set" where
  "ainferences_between CC C = {\<gamma>. \<gamma> \<in> a\<Gamma> \<and> ainfer_from (CC \<union> {C}) \<gamma> \<and> C \<in># aprems_of \<gamma>}"

inductive AV :: "('a, 'b) astate \<Rightarrow> ('a, 'b) astate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>a" 50) where
  inference_computation: "N' = mset_set (aconcls_of (ainferences_between (set_mset Q) C)) \<Longrightarrow>
    (Some N, P + {#C#}, Q, L, X, M) \<leadsto>\<^sub>a (Some (N + N'), P, Q + {#C#}, L, X, M)"
| forward_subsumption: "D \<in># P + Q \<Longrightarrow> subsumes (clause_of D) (clause_of C) \<Longrightarrow> 
    (Some (N + {#C#}), P, Q, L, X, M) \<leadsto>\<^sub>a (Some N, P, Q, L, X, M)"

end

end
