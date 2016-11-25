theory New2_FO_Resolution_Prover 
imports New2_Ordered_Ground_Resolution Standard_Redundancy Substitution Clauses 
begin

type_synonym 'a state = "'a clause set \<times> 'a clause set \<times> 'a clause set"

locale FO_resolution =
  unification subst_atm id_subst comp_subst mgu
  for
    subst_atm :: "'a :: wellorder \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s => 's => 's" and
    mgu :: "'a set set \<Rightarrow> 's option" +
  fixes
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    less_atm_iff: "less_atm A B \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> A \<cdot>a \<sigma> < B \<cdot>a \<sigma>)"
begin

definition less_eq_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "less_eq_atm A B \<longleftrightarrow> less_atm A B \<or> A = B"

lemma ground_less_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_atm A B \<longleftrightarrow> A < B"
  unfolding is_ground_atm_def less_atm_iff by (auto intro: ex_ground_subst)

lemma ground_less_eq_atm_iff: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_eq_atm A B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_atm_def ground_less_atm_iff by fastforce

definition subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsumes C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> \<le># D)"

definition properly_subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "properly_subsumes C D \<longleftrightarrow> subsumes C D \<and> \<not> subsumes D C"

definition variants :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "variants C D \<longleftrightarrow> subsumes C D \<and> subsumes D C"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = (case St of (N, P, Q) \<Rightarrow> N \<union> P \<union> Q)"

abbreviation grounding_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "grounding_of_state St \<equiv> grounding_of_clss (clss_of_state St)"

text {*
\begin{nit}
$A_{ii}$ vs.\ $A_i$
\end{nit}
*}

context
  fixes S :: "'a clause \<Rightarrow> 'a clause"
begin

(* Move to substitution maybe:*)
definition subst_atm_list :: "'a list \<Rightarrow> 's \<Rightarrow> 'a list" (infixl "\<cdot>al" 67) where
  "As \<cdot>al \<sigma> = map (\<lambda>A. A \<cdot>a \<sigma>) As"
  
lemma subst_atm_lst_id_subst[simp]: "As \<cdot>al id_subst = As"
  unfolding subst_atm_list_def by auto

definition subst_mcls :: "'a main_clause \<Rightarrow> 's \<Rightarrow> 'a main_clause" (infixl "\<cdot>amc" 67) where
  "DAs \<cdot>amc \<sigma> = (get_C DAs \<cdot> \<sigma>, get_As DAs \<cdot>al \<sigma>)"
  
lemma subst_mcl_id_subst[simp]: "DAs \<cdot>amc id_subst = DAs"
  unfolding subst_mcls_def by auto

definition subst_scls :: "'a side_clause \<Rightarrow> 's \<Rightarrow> 'a side_clause" (infixl "\<cdot>sc" 67) where
  "CAs \<cdot>sc \<sigma> = (get_C CAs \<cdot> \<sigma>, get_As CAs \<cdot>am \<sigma>)"
  
lemma subst_scl_id_subst[simp]: "CAs \<cdot>sc id_subst = CAs"
  unfolding subst_scls_def by auto
  
abbreviation "maximal_in A DAs \<equiv> (\<forall>B \<in> atms_of DAs. \<not> less_atm A B)"
  (* This definition is a bit inconsistent compared to the ground case since 
     there it was defined as THE maximum instead of SOME upper bound. *)
abbreviation "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of CAis. \<not> less_eq_atm A B)"

(* Inspiration from supercalc *)
inductive eligible :: "'s \<Rightarrow> 'a main_clause \<Rightarrow> bool" where
  eligible:
  "S (main_clause (D,As)) = negs (mset As) 
   \<or> 
   (
     S (main_clause (D,As)) = {#} 
     \<and> length As = 1 
     \<and> maximal_in ((As ! 0) \<cdot>a \<sigma>) (main_clause (D,As) \<cdot> \<sigma>)
   )
   \<Longrightarrow> eligible \<sigma> (D,As)"
  
abbreviation(output) "Union_Cs CAs \<equiv> \<Union># (mset (map get_C CAs))"

inductive ord_resolve :: "'a side_clause list \<Rightarrow> 'a main_clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "length CAs = length As \<Longrightarrow> 
   CAs \<noteq> [] \<Longrightarrow> 
   As \<noteq> [] \<Longrightarrow>
   \<forall>i. i < length CAs \<longrightarrow> get_As (CAs ! i) \<noteq> {#} \<Longrightarrow>
   \<forall>i. i < length CAs \<longrightarrow> (\<forall>Ai \<in># get_As (CAs ! i). Ai \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>) \<Longrightarrow>
   eligible \<sigma> (D,As) \<Longrightarrow>
   \<forall>i. i < length CAs \<longrightarrow> str_maximal_in (As ! i \<cdot>a \<sigma>) (get_C (CAs ! i) \<cdot> \<sigma>) \<Longrightarrow>
     (* Alternative to \<^sup> is to quantify over the As in each CAs ! i, but they will
        unify to (As ! i) \<cdot> \<sigma> anyways... *)
   \<forall>C \<in> set CAs. S (side_clause C) = {#} \<Longrightarrow>
   ord_resolve CAs (D,As) ((Union_Cs CAs + D) \<cdot> \<sigma>)"

inductive ord_resolve_rename :: "'a side_clause list \<Rightarrow> 'a main_clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_rename:
  "is_renaming \<rho> \<Longrightarrow>
   (\<forall>\<rho> \<in> set P. is_renaming \<rho>) \<Longrightarrow>
   length P = length CAs \<Longrightarrow>
   ord_resolve (map (\<lambda>(C,\<rho>). C \<cdot>sc \<rho>) (zip CAs P)) (DAs \<cdot>amc \<rho>) E \<Longrightarrow>
   ord_resolve_rename CAs DAs E"
  (* In this definition, P, \<sigma> and \<rho>, are not part of the signature. 
     A bit different from ord_resolve... *)
  
lemma ord_resolve_raw_imp_ord_resolve: "ord_resolve CAs D E \<Longrightarrow> ord_resolve_rename CAs D E"
  apply (rule ord_resolve_rename[of id_subst "replicate (length CAs) id_subst"])
  apply auto
proof -
  assume asm: "ord_resolve CAs D E"
  moreover
  have "CAs = (map (\<lambda>(x, y). x \<cdot>sc y) (zip CAs (replicate (length CAs) id_subst)))"
    by auto
  ultimately
  show "ord_resolve (map (\<lambda>(x, y). x \<cdot>sc y) (zip CAs (replicate (length CAs) id_subst))) D E"
    by metis
qed



lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_cls_mset (side_clauses CAs)" and
    gr_d: "is_ground_cls (main_clause DAs)" and
    res_e: "ord_resolve_rename CAs DAs E"
  shows "ord_resolve CAs DAs E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have "(map (\<lambda>(x, y). x \<cdot>sc y) (zip CAs P)) = CAs"
    apply (rule nth_equalityI)
    using ord_resolve_rename(3) apply auto[]
    apply auto
    using gr_cc 
    using is_ground_cls_mset_def[of "side_clauses CAs"]
    using lol[of CAs "is_ground_cls "]
    sorry (* I should make a is_ground for side_clause *)
    
  then show ?thesis sorry
qed
  

(* lifting lemma:
I think a better tactic is to use ord_resolve in the conclusion
and then I can probably remove the renaming assumption on M
*)
  

end