theory New3_FO_Resolution_Prover 
imports New3_Ordered_Ground_Resolution Standard_Redundancy Substitution Clauses 
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
  "length (CAi :: 'a clause list) = n \<Longrightarrow>
   length (Ci  :: 'a clause list) = n \<Longrightarrow>
   length (Aij :: 'a multiset list) = n \<Longrightarrow>
   length (Ai  :: 'a list) = n \<Longrightarrow>
   length CAs = length As \<Longrightarrow> 
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

lemma true_fo_cls_mset_def2: "I \<Turnstile>fom CC \<longleftrightarrow> (\<forall>C \<in># CC. I \<Turnstile>fo C)"
  by (metis Melem_subst_cls_mset true_cls_mset_def true_fo_cls true_fo_cls_inst true_fo_cls_mset true_fo_cls_mset.cases)
  
  
lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAs DAs E" and
    cc_d_true: "I \<Turnstile>fom (side_clauses CAs + {#main_clause DAs#})"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve CAi n As \<tau> D)
  have d: "DAs = (D, As)" using ord_resolve(1) .
  have e: "E = ((Union_Cs CAs) + D) \<cdot> \<tau>" using ord_resolve(2) .
  have len: "length CAs = length As" using ord_resolve(4) .
  have unif: "\<forall>i<length CAs. \<forall>Ai\<in>#get_As (CAs ! i). Ai \<cdot>a \<tau> = As ! i \<cdot>a \<tau>" using ord_resolve(8) .
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

lemma rename_sound_scl:
  assumes len: "length P = length CAs"
  assumes ren: "\<forall>\<rho> \<in> set P. is_renaming \<rho>"
  assumes true_cas: "I \<Turnstile>fom side_clauses CAs"
  shows "I \<Turnstile>fom side_clauses (CAs \<cdot>\<cdot>scl P)"
proof -
  from true_cas have "\<forall>C. C\<in>#(side_clauses CAs) \<longrightarrow> (I \<Turnstile>fo C)" 
    using true_fo_cls_mset_def2 by auto
  then have "\<forall>C. C \<in> set CAs \<longrightarrow> (I \<Turnstile>fo side_clause C)" unfolding side_clauses_def by auto
  then have "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo side_clause (CAs ! i))"
    using in_set_conv_nth[of _ CAs] by blast
  then have "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo side_clause (CAs ! i) \<cdot> P ! i)"
    using ren rename_sound len by (auto simp del: subst_mc_side_clause)
  then have true_cp: "\<forall>i. i < length CAs \<longrightarrow> (I \<Turnstile>fo side_clause (CAs ! i \<cdot>sc P ! i))" 
    by auto
  show ?thesis unfolding true_fo_cls_mset_def2
  proof
    fix x
    assume "x \<in># side_clauses (CAs \<cdot>\<cdot>scl P)"
    then have "x \<in> set_mset (mset (map side_clause (CAs \<cdot>\<cdot>scl P)))" unfolding side_clauses_def .
    then have "x \<in> set (map side_clause (CAs \<cdot>\<cdot>scl P))" by auto
    then obtain i where i_x: "i < length (map side_clause (CAs \<cdot>\<cdot>scl P)) \<and> x = map side_clause (CAs \<cdot>\<cdot>scl P) ! i"
      using in_set_conv_nth by metis
    then show "I \<Turnstile>fo x" using i_x subst_scls_lists_def true_cp by auto
  qed
qed
  

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAs DA E" and
    cc_d_true: "I \<Turnstile>fom ((side_clauses CAs) + {#main_clause DA#})"
  shows "I \<Turnstile>fo E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have ren: "is_renaming \<rho>" using ord_resolve_rename(1) .
  have rens: "Ball (set P) is_renaming" using ord_resolve_rename(2) .
  have len: "length P = length CAs" using ord_resolve_rename(3) .
  have res: "ord_resolve (CAs \<cdot>\<cdot>scl P) (DA \<cdot>mc \<rho>) E" using ord_resolve_rename(4) .
  have "I \<Turnstile>fom side_clauses (CAs \<cdot>\<cdot>scl P) + {#main_clause (DA \<cdot>mc \<rho>)#}"
    using rename_sound_scl[OF len rens , of I] rename_sound[OF ren, of I "main_clause DA"]
    cc_d_true by (simp add: true_fo_cls_mset_def2)
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAs \<cdot>\<cdot>scl P" "(DA \<cdot>mc \<rho>)" "E" I, OF res]
    by simp
qed

context
  fixes M :: "'a clause set"
  assumes select: "selection S"
begin

interpretation selection
  by (rule select)

definition S_M :: "'a literal multiset \<Rightarrow> 'a literal multiset" where
  "S_M C = (if C \<in> grounding_of_clss M
    then (SOME C'. \<exists>D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>) else S C)"

lemma S_M_grounding_of_clss:
  assumes "C \<in> grounding_of_clss M"
  obtains D \<sigma> where "D \<in> M \<and> C = D \<cdot> \<sigma> \<and> S_M C = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
proof (atomize_elim, unfold S_M_def eqTrueI[OF assms] if_True, rule someI_ex)
  from assms show "\<exists>C' D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    by (auto simp: grounding_of_clss_def grounding_of_cls_def)
qed

lemma S_M_not_grounding_of_clss:
  assumes "C \<notin> grounding_of_clss M"
  shows "S_M C = S C"
  using assms unfolding S_M_def by simp

lemma S_M_selects_subseteq: "S_M C \<le># C"
proof cases
  assume "C \<in> grounding_of_clss M"
  then obtain D \<sigma> where "C = D \<cdot> \<sigma>" "S_M C = S D \<cdot> \<sigma>"
    using S_M_grounding_of_clss by metis
  then show ?thesis
    using S_selects_subseteq by (auto intro: subst_cls_mono_mset)
qed (simp add: S_M_not_grounding_of_clss S_selects_subseteq)

lemma S_M_selects_neg_lits:
  assumes "L \<in># S_M C"
  shows "is_neg L"
using assms proof cases
  assume "C \<in> grounding_of_clss M"
  then obtain D \<sigma> where "C = D \<cdot> \<sigma>" "S_M C = S D \<cdot> \<sigma>"
    using S_M_grounding_of_clss by metis
  then show ?thesis
    using assms S_selects_neg_lits by auto
qed (simp add: S_M_not_grounding_of_clss S_selects_neg_lits)


interpretation gd: ground_resolution_with_selection S_M
  by unfold_locales (auto simp: S_M_selects_subseteq S_M_selects_neg_lits)

(*"grounding_of_clss N0"*)

interpretation src: standard_redundancy_criterion gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_M"
  by unfold_locales
(*
find_theorems name: src
thm src.saturated_upto_refute_complete
*)

(*TODO change*)
definition "gd_ord_\<Gamma>' = gd.ord_\<Gamma>"

lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gd.ord_\<Gamma> \<subseteq> gd_ord_\<Gamma>'"
  unfolding gd_ord_\<Gamma>'_def by simp

interpretation src_ext:
  redundancy_criterion "gd_ord_\<Gamma>'" "src.Rf" "(\<lambda>N. src.Ri N \<union> (gd_ord_\<Gamma>' - gd.ord_\<Gamma>))"
  by (rule standard_redundancy_criterion_extension[OF gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion])
(*find_theorems name: src_ext*)

end

end

text {*
The following corresponds to Lemma 4.12:
*}

lemma (in linorder) set_sorted_list_of_multiset[simp]:
  "set (sorted_list_of_multiset M) = set_mset M"
  by (induct M) (simp_all add: local.set_insort_key)

lemma (in linorder) multiset_mset_sorted_list_of_multiset[simp]:
  "mset (sorted_list_of_multiset M) = M"
  by (induct M) (simp_all add: ac_simps)

lemma ord_resolve_lifting:
  assumes resolve: "ord_resolve_rename (S_M S M) CC D E"
  and select: "selection S"
  and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
  and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
  and grounding: "{main_clause D, E} \<union> (set_mset (side_clauses CC)) \<subseteq> grounding_of_clss M"
    (* try to get rid of set_mset *)
  obtains \<sigma> CC' D' E' where
    "is_ground_subst \<sigma>"
    "ord_resolve_rename S CC' D' E'" (* maybe without rename *)
    "CC = CC' \<cdot>scl \<sigma>" "D = D' \<cdot>mc \<sigma>" "E = E' \<cdot> \<sigma>"
    "{main_clause D', E'} \<union> (set_mset (side_clauses CC')) \<subseteq> M"
      (* try to get rid of set_mset *)
  sorry

end

(* lifting lemma:
I think a better tactic is to use ord_resolve in the conclusion
and then I can probably remove the renaming assumption on M
*)

  

end