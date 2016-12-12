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
   ord_resolve (CAs \<cdot>\<cdot>scl P) (DAs \<cdot>mc \<rho>) E \<Longrightarrow>
   ord_resolve_rename CAs DAs E"
  (* In this definition, P, \<sigma> and \<rho>, are not part of the signature. 
     A bit different from ord_resolve... *)
  
lemma ord_resolve_raw_imp_ord_resolve: "ord_resolve CAs D E \<Longrightarrow> ord_resolve_rename CAs D E"
  apply (rule ord_resolve_rename[of id_subst "replicate (length CAs) id_subst"])
  apply auto
  done



lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_scls_list CAs" and
    gr_d: "is_ground_mcls DAs" and
    res_e_re: "ord_resolve_rename CAs DAs E"
  shows "ord_resolve CAs DAs E"
  using res_e_re proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>" using ord_resolve_rename(2) .
  have len: "length P = length CAs" using ord_resolve_rename(3) .
  have res_e: "ord_resolve (CAs \<cdot>\<cdot>scl P) (DAs \<cdot>mc \<rho>) E" using ord_resolve_rename(4) .
  
  have "CAs \<cdot>\<cdot>scl P = CAs" using len gr_cc by auto
  moreover
  have "DAs \<cdot>mc \<rho> = DAs" using gr_d by auto
  ultimately show ?thesis using res_e by auto
qed

inductive true_fo_cls :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>fo" 50) where
  true_fo_cls:
  "(\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> (C \<cdot> \<sigma>)) \<Longrightarrow> I \<Turnstile>fo C"
  
lemma true_fo_cls_inst: "I \<Turnstile>fo C \<Longrightarrow> is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> (C \<cdot> \<sigma>)"
  using true_fo_cls.induct .

inductive true_fo_cls_mset :: "'a interp \<Rightarrow> 'a clause multiset \<Rightarrow> bool" (infix "\<Turnstile>fom" 50) where
  true_fo_cls_mset:
  "(\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (CC \<cdot>cm \<sigma>)) \<Longrightarrow> I \<Turnstile>fom CC"
  
lemma true_fo_cls_mset_inst: "I \<Turnstile>fom C \<Longrightarrow> is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (C \<cdot>cm \<sigma>)"
  using true_fo_cls_mset.induct .
  
lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAs DAs E" and
    cc_d_true: "I \<Turnstile>fom (side_clauses CAs + {#main_clause DAs#})"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve As \<tau> D)
  have d: "DAs = (D, As)" using ord_resolve(1) .
  have e: "E = ((Union_Cs CAs) + D) \<cdot> \<tau>" using ord_resolve(2) .
  have len: "length CAs = length As" using ord_resolve(3) .
  have unif: "\<forall>i<length CAs. \<forall>Ai\<in>#get_As (CAs ! i). Ai \<cdot>a \<tau> = As ! i \<cdot>a \<tau>" using ord_resolve(7) .
  have "is_ground_subst (\<tau> \<odot> \<sigma>)"
    using ground_subst_\<sigma> by (rule is_ground_comp_subst)
  hence cc_true: "I \<Turnstile>m (side_clauses CAs) \<cdot>cm \<tau> \<cdot>cm \<sigma>" and d_true: "I \<Turnstile> (main_clause DAs) \<cdot> \<tau> \<cdot> \<sigma>"
    using true_fo_cls_mset_inst[OF cc_d_true, of "\<tau> \<odot> \<sigma>"] by auto 
  then show "\<forall>C\<in>set CAs. S (side_clause C) = {#} \<Longrightarrow> I \<Turnstile> E \<cdot> \<sigma>"
  proof (cases "\<forall>A \<in> set As. A \<cdot>a \<tau> \<cdot>a \<sigma> \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs (mset (get_As DAs)) \<cdot> \<tau> \<cdot> \<sigma>"
      unfolding true_cls_def d by auto
    hence "I \<Turnstile> D \<cdot> \<tau> \<cdot> \<sigma>"
      using d_true unfolding d unfolding main_clause_def by auto
    thus ?thesis
      unfolding e by simp
  next
    case False
    then obtain i where a_in_aa: "i < length CAs" and a_false: "(As ! i) \<cdot>a \<tau> \<cdot>a \<sigma> \<notin> I"
      using d len by (metis in_set_conv_nth) 
    define C' where "C' \<equiv> get_C (CAs ! i)"
    define BB where "BB \<equiv> get_As (CAs ! i)"
    have c_cf': "C' \<subseteq># Union_Cs CAs"
      unfolding C'_def using a_in_aa by auto
    have c_in_cc: "C' + poss BB \<in># side_clauses CAs"
      using C'_def BB_def using a_in_aa by (simp add: get_C_get_As_side_clauses)
    { fix B
      assume "B \<in># BB"
      then have "B \<cdot>a \<tau> = (As ! i) \<cdot>a \<tau>" using unif a_in_aa unfolding BB_def by auto
    }
    hence "\<not> I \<Turnstile> poss BB \<cdot> \<tau> \<cdot> \<sigma>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C' + poss BB) \<cdot> \<tau> \<cdot> \<sigma>"
      using c_in_cc cc_true unfolding true_cls_mset_def by force
    ultimately have "I \<Turnstile> C' \<cdot> \<tau> \<cdot> \<sigma>"
      by simp
    thus ?thesis
      unfolding e subst_cls_union using c_cf' by (blast intro: true_cls_mono intro!: subst_cls_mono)
  qed
qed

lemma rename_sound:
  assumes "is_renaming \<rho>"
  assumes "I \<Turnstile>fo C"
  shows "I \<Turnstile>fo (C \<cdot> \<rho>)"
using assms
  by (metis is_ground_comp_subst subst_cls_comp_subst true_fo_cls true_fo_cls_inst) 

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CC D E" and
    cc_d_true: "I \<Turnstile>fom ((side_clauses CC) + {#main_clause D#})"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using res_e proof (cases rule: ord_resolve_rename.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve_rename \<rho> P)
  
  then show "I \<Turnstile> E \<cdot> \<sigma>"
    thm ord_resolve_sound
    sorry
qed
  

(* lifting lemma:
I think a better tactic is to use ord_resolve in the conclusion
and then I can probably remove the renaming assumption on M
*)
  

end