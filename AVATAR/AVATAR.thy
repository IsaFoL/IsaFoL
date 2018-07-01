theory AVATAR
  imports
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    Ordered_Resolution_Prover.Inference_System
begin

(* FIXME: suboptimal for SMT *)
type_synonym assertion = nat

datatype 'a aclause =
  AClause "'a clause" "assertion set"

datatype 'a ainference =
  AInfer (aside_prems_of: "'a aclause multiset") (amain_prem_of: "'a aclause")
    (aconcl_of: "'a aclause")

abbreviation aprems_of :: "'a ainference \<Rightarrow> 'a aclause multiset" where
  "aprems_of \<gamma> \<equiv> aside_prems_of \<gamma> + {#amain_prem_of \<gamma>#}"

abbreviation aconcls_of :: "'a ainference set \<Rightarrow> 'a aclause set" where
  "aconcls_of \<Gamma> \<equiv> aconcl_of ` \<Gamma>"

abbreviation ainfer_from :: "'a aclause set \<Rightarrow> 'a ainference \<Rightarrow> bool" where
  "ainfer_from CC \<gamma> \<equiv> set_mset (aprems_of \<gamma>) \<subseteq> CC"

type_synonym ('a, 'b) astate =
  "'a aclause multiset option \<times> 'a aclause multiset \<times> 'a aclause multiset
   \<times> ('a \<Rightarrow> 'a aclause multiset) \<times> 'b aclause multiset \<times> 'b interp"

locale avatar = substitution subst_atm
    for subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" +
  fixes
    \<Gamma> :: "'a ainference set" and
    abstract :: "'a aclause \<Rightarrow> 'b" and
    base_solver :: "'b multiset \<Rightarrow> 'b interp option"
begin

definition ainferences_from :: "'a aclause set \<Rightarrow> 'a ainference set" where
  "ainferences_from CC = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> ainfer_from CC \<gamma>}"

definition ainferences_between :: "'a aclause set \<Rightarrow> 'a aclause \<Rightarrow> 'a ainference set" where
  "ainferences_between CC C = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> ainfer_from (CC \<union> {C}) \<gamma> \<and> C \<in># aprems_of \<gamma>}"

inductive AV (infix "\<leadsto>\<^sub>a" 50) where
  "N' = mset_set (ainferences_between (set_mset Q) C) \<Longrightarrow>
   (Some N, P + {#C#}, Q, L, X, M) \<leadsto>\<^sub>a (Some (N + N'), P, Q + {#C#}, L, X, M)"

end

end
