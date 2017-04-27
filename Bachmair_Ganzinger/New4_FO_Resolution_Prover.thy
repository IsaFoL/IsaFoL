(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull
*)

theory New4_FO_Resolution_Prover 
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
  
definition "maximal_in A DAs \<equiv> (\<forall>B \<in> atms_of DAs. \<not> less_atm A B)"
  (* This definition is a bit inconsistent compared to the ground case since 
     there it was defined as THE maximum instead of SOME upper bound. *)
abbreviation "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of CAis. \<not> less_eq_atm A B)"

(* Inspiration from supercalc *)
inductive eligible :: "'s \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
  "S DA = negs (mset Ai) 
   \<or> 
   (
     S DA = {#} 
     \<and> length Ai = 1 
     \<and> maximal_in ((Ai ! 0) \<cdot>a \<sigma>) (DA \<cdot> \<sigma>)
   )
   \<Longrightarrow> eligible \<sigma> Ai DA"
  
lemma eligible_simp:
  " eligible \<sigma> Ai DA \<longleftrightarrow> (S DA = negs (mset Ai) 
   \<or> 
   (
     S DA = {#} 
     \<and> length Ai = 1 
     \<and> maximal_in ((Ai ! 0) \<cdot>a \<sigma>) (DA \<cdot> \<sigma>)
   ))"
  using eligible.simps by blast

inductive ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "length (CAi :: 'a clause list) = n \<Longrightarrow>
   length (Ci  :: 'a clause list) = n \<Longrightarrow>
   length (Aij :: 'a multiset list) = n \<Longrightarrow> (* Skal det vaere en clause istedet?*)
   length (Ai  :: 'a list) = n \<Longrightarrow>
   n \<noteq> 0 \<Longrightarrow>
   \<forall>i < n. (CAi ! i) = (Ci ! i + (poss (Aij ! i))) \<Longrightarrow>
   \<forall>i < n. Aij ! i \<noteq> {#} \<Longrightarrow>
   Some \<sigma> = mgu (set_mset ` (set (map2 add_mset Ai Aij))) \<Longrightarrow> (* This states \<sigma> is a unifier, but! it should be an mgu! *)
   eligible \<sigma> Ai (D + negs (mset Ai)) \<Longrightarrow>
   \<forall>i. i < n \<longrightarrow> str_maximal_in (Ai ! i \<cdot>a \<sigma>) ((Ci ! i) \<cdot> \<sigma>) \<Longrightarrow>
   \<forall>i < n. S (CAi ! i) = {#} \<Longrightarrow> (* Use the ! style instead maybe, or maybe us the \<forall>\<in>. style above *)
   ord_resolve CAi (D + negs (mset Ai)) (((\<Union># (mset Ci)) + D) \<cdot> \<sigma>)"    
  
lemma mgu_unifier:
  assumes ailen: "length Ai = n"
  assumes aijlen: "length Aij = n"
  assumes mgu: "Some \<sigma> = mgu (set_mset ` (set (map2 add_mset Ai Aij)))"
  shows "\<forall>i < n. (\<forall>A \<in># Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>)"
proof -
  from mgu have "is_mgu \<sigma> (set_mset ` (set (map2 add_mset Ai Aij)))" using mgu_sound by auto
  then have uni: "is_unifiers \<sigma> (set_mset ` (set (map2 add_mset Ai Aij)))" unfolding is_mgu_def by auto
  
  show "\<forall>i < n. (\<forall>A \<in># Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>)" 
  proof (rule allI; rule impI)
    fix i
    assume i: "i < n"
    then have "is_unifier \<sigma> (set_mset (add_mset (Ai ! i) (Aij ! i)))"
      using ailen aijlen uni  unfolding is_unifiers_def
      by (auto simp del: map2_nth simp add: map2_nth[symmetric]) 
    then show "\<forall>A\<in>#Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>" using ailen aijlen i
      by (metis finite_set_mset insertCI is_unifier_subst_atm_eqI set_mset_add_mset_insert)
  qed
qed
    
   
inductive ord_resolve_rename :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_rename:
  "is_renaming \<rho> \<Longrightarrow>
   (\<forall>\<rho> \<in> set P. is_renaming \<rho>) \<Longrightarrow>
   length P = length CAi \<Longrightarrow>
   ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) E \<Longrightarrow>
   ord_resolve_rename CAi DA E"
  
lemma ord_resolve_raw_imp_ord_resolve: "ord_resolve CAs D E \<Longrightarrow> ord_resolve_rename CAs D E"
  apply (rule ord_resolve_rename[of id_subst "replicate (length CAs) id_subst"])
  apply auto
  done

lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_cls_list CAi" and
    gr_d: "is_ground_cls DA" and
    res_e_re: "ord_resolve_rename CAi DA E"
  shows "ord_resolve CAi DA E"
  using res_e_re proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>" using ord_resolve_rename(2) .
  have len: "length P = length CAi" using ord_resolve_rename(3) .
  have res_e: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) E" using ord_resolve_rename(4) .
  
  have "CAi \<cdot>\<cdot>cl P = CAi" using len gr_cc by auto
  moreover
  have "DA \<cdot> \<rho> = DA" using gr_d by auto
  ultimately show ?thesis using res_e by auto
qed

inductive true_fo_cls :: "'a interp \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<Turnstile>fo" 50) where
  true_fo_cls:
  "(\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> C \<cdot> \<sigma>) \<Longrightarrow> I \<Turnstile>fo C"
  
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
    res_e: "ord_resolve CAi DA E" and
    cc_d_true: "I \<Turnstile>fom mset CAi + {#DA#}"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve n Ci Aij Ai \<tau> D)
  have DA: "DA = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = (\<Union>#mset Ci + D) \<cdot> \<tau>" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have aij_len: "length Aij = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i)" using ord_resolve by -
  have mgu: "Some \<tau> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
  have len: "length CAi = length Ai" using ai_len cai_len by auto
  have "is_ground_subst (\<tau> \<odot> \<sigma>)"
    using ground_subst_\<sigma> by (rule is_ground_comp_subst)
  hence cc_true: "I \<Turnstile>m (mset CAi) \<cdot>cm \<tau> \<cdot>cm \<sigma>" and d_true: "I \<Turnstile> DA \<cdot> \<tau> \<cdot> \<sigma>"
    using true_fo_cls_mset_inst[OF cc_d_true, of "\<tau> \<odot> \<sigma>"] by auto 
      
  from mgu have unif: "\<forall>i<n. \<forall>A\<in>#Aij ! i. A \<cdot>a \<tau> = Ai ! i \<cdot>a \<tau>" 
    using mgu_unifier using ai_len aij_len by blast
      
  show "\<forall>i<n. S (CAi ! i) = {#} \<Longrightarrow> I \<Turnstile> E \<cdot> \<sigma>"
  proof (cases "\<forall>A \<in> set Ai. A \<cdot>a \<tau> \<cdot>a \<sigma> \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs (mset Ai) \<cdot> \<tau> \<cdot> \<sigma>"
      unfolding true_cls_def by auto
    hence "I \<Turnstile> D \<cdot> \<tau> \<cdot> \<sigma>"
      using d_true DA by auto
    thus ?thesis
      unfolding e by simp
  next
    case False
    then obtain i where a_in_aa: "i < length CAi" and a_false: "(Ai ! i) \<cdot>a \<tau> \<cdot>a \<sigma> \<notin> I"
      using DA len by (metis in_set_conv_nth) 
    define C' where "C' \<equiv> Ci ! i"
    define BB where "BB \<equiv> Aij ! i"
    have c_cf': "C' \<subseteq># \<Union># mset CAi"
      unfolding C'_def using a_in_aa
      by (metis cai_len cai nth_mem set_mset_mset subset_mset.bot.extremum subset_mset.le_add_same_cancel1 subset_mset.order.trans sum_mset.remove) 
    have c_in_cc: "C' + poss BB \<in># mset CAi"
      using C'_def BB_def using a_in_aa
      using cai_len in_set_conv_nth cai by fastforce
    { fix B
      assume "B \<in># BB"
      then have "B \<cdot>a \<tau> = (Ai ! i) \<cdot>a \<tau>" using unif a_in_aa cai_len unfolding BB_def by auto
    }
    hence "\<not> I \<Turnstile> poss BB \<cdot> \<tau> \<cdot> \<sigma>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C' + poss BB) \<cdot> \<tau> \<cdot> \<sigma>"
      using c_in_cc cc_true unfolding true_cls_mset_def by force
    ultimately have "I \<Turnstile> C' \<cdot> \<tau> \<cdot> \<sigma>"
      by simp
    thus ?thesis
      unfolding e subst_cls_union using c_cf'
      using true_cls_mono subst_cls_mono
      by (metis (no_types, lifting) C'_def a_in_aa cai_len ci_len mset_subset_eq_add_left nth_mem_mset set_mset_mono sum_mset.remove)
  qed
qed

lemma subst_sound:
  assumes "I \<Turnstile>fo C"
  shows "I \<Turnstile>fo (C \<cdot> \<rho>)"
using assms
  by (metis is_ground_comp_subst subst_cls_comp_subst true_fo_cls true_fo_cls_inst)

lemma subst_sound_scl:
  assumes len: "length P = length CAi"
  assumes true_cas: "I \<Turnstile>fom mset CAi"
  shows "I \<Turnstile>fom mset (CAi \<cdot>\<cdot>cl P)"
proof -
  from true_cas have "\<forall>C. C\<in># mset CAi \<longrightarrow> (I \<Turnstile>fo C)" 
    using true_fo_cls_mset_def2 by auto
  then have "\<forall>C. C \<in> set CAi \<longrightarrow> (I \<Turnstile>fo C)" unfolding side_clauses_def by auto
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i))"
    using in_set_conv_nth[of _ CAi] by blast
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i) \<cdot> P ! i)"
    using subst_sound len by auto
  then have true_cp: "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo (CAi ! i \<cdot> P ! i))" 
    by auto
  show ?thesis unfolding true_fo_cls_mset_def2
  proof
    fix x
    assume "x \<in># mset (CAi \<cdot>\<cdot>cl P)"
    then have "x \<in> set_mset (mset ((CAi \<cdot>\<cdot>cl P)))" by -
    then have "x \<in> set (CAi \<cdot>\<cdot>cl P)" by auto
    then obtain i where i_x: "i < length (CAi \<cdot>\<cdot>cl P) \<and> x = (CAi \<cdot>\<cdot>cl P) ! i"
      using in_set_conv_nth by metis
    then show "I \<Turnstile>fo x" using true_cp unfolding subst_cls_lists_def
      by (simp add: len)
        
  qed
qed
  

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAi DA E" and
    cc_d_true: "I \<Turnstile>fom (mset CAi) + {#DA#}"
  shows "I \<Turnstile>fo E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have len: "length P = length CAi" using ord_resolve_rename by -
  have res: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) E" using ord_resolve_rename by -
  have "I \<Turnstile>fom (mset (CAi \<cdot>\<cdot>cl P)) + {#DA \<cdot> \<rho>#}"
    using subst_sound_scl[OF len , of I] subst_sound[of I DA]
    cc_d_true by (simp add: true_fo_cls_mset_def2)
    
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAi \<cdot>\<cdot>cl P" "DA \<cdot> \<rho>" E I, OF res]
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

lemma inv_ren_ren: "is_renaming s \<Longrightarrow> is_renaming (inv_ren s)"
  sorry    
    
lemma var_disjoint_def_2:
  "var_disjoint Cs = 
    (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> 
      (\<exists>\<tau>. 
        (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>)
      )
    )"
  sorry
    
lemma make_ground_subst2: 
  "is_ground_cls_list (CC \<cdot>cl \<sigma>) \<Longrightarrow>
       \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i < length CC. \<forall>S. S \<subseteq># CC ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)"
  sorry
    
lemma grounding_ground: "C \<in> grounding_of_clss M \<Longrightarrow> is_ground_cls C"
   by (smt ground_subst_ground_cls grounding_of_clss_def image_iff mem_Collect_eq mem_simps(9) substitution_ops.grounding_of_cls_def)
  (* There is also an Isar proof. *)
    
lemma ord_resolve_lifting: 
  fixes CAi
  assumes resolve: "ord_resolve (S_M S M) CAi DA E" 
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" 
    and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
    and grounding: "{DA} \<union> (set CAi) \<subseteq> grounding_of_clss M"
  obtains \<eta> \<eta>2 CAi' DA' E' where
    "is_ground_subst \<eta>"
    "is_ground_subst \<eta>2"
    "ord_resolve S CAi' DA' E'" 
    "CAi = CAi' \<cdot>cl \<eta>" "DA = DA' \<cdot> \<eta>" "E = E' \<cdot> \<eta>2" 
    "{DA'} \<union> set CAi' \<subseteq> M"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
  
  note n = \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
  
  interpret S: selection S by (rule select)
    
  obtain DA'' \<eta>'' CAi'' \<eta>s'' where clauses'':
    "length CAi'' = n"
    "length \<eta>s'' = n"
    
    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi''. CA \<in> M"
    "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
    "map (S_M S M) CAi = (map S CAi'') \<cdot>\<cdot>cl \<eta>s''"
  proof -
    have uuu: "\<forall>CA \<in> set CAi. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> CA = CA'' \<cdot> \<eta>c'' \<and> S CA'' \<cdot> \<eta>c'' = S_M S M CA"
      using grounding using grounding S_M_grounding_of_clss select
      by (metis le_supE subset_iff)    
    hence "\<forall>i < n. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> (CAi ! i) = CA'' \<cdot> \<eta>c'' \<and> S CA'' \<cdot> \<eta>c'' = S_M S M ( (CAi ! i)) "
      using ord_resolve(3) by auto
    then have "\<exists>\<eta>s''f CAi''f. \<forall>i < n. CAi''f i \<in> M \<and> (CAi ! i) = (CAi''f i) \<cdot> (\<eta>s''f i) \<and> S (CAi''f i) \<cdot> (\<eta>s''f i) = S_M S M (CAi ! i)"
      by metis
    then obtain \<eta>s''f CAi''f where f_p: "\<forall>i < n. CAi''f i \<in> M \<and> (CAi ! i) = (CAi''f i) \<cdot> (\<eta>s''f i) \<and> S (CAi''f i)  \<cdot> (\<eta>s''f i) = S_M S M  (CAi ! i)"
      by auto
        
    define \<eta>s'' where "\<eta>s'' = map \<eta>s''f [0 ..<n]"
    define CAi'' where "CAi'' = map CAi''f [0 ..<n]"
      
    have "length \<eta>s'' = n" "length CAi'' = n"
      unfolding \<eta>s''_def CAi''_def by auto
    note n = \<open>length \<eta>s'' = n\<close> \<open>length CAi'' = n\<close> n
      
    have \<eta>s''_ff: "\<forall>i < n. \<eta>s'' ! i = \<eta>s''f i"
      unfolding \<eta>s''_def apply (induction n) apply auto
      by (metis add.left_neutral diff_is_0_eq diff_zero length_map length_upt less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_map_upt)
    have CAi''_ff: "\<forall>i < n. CAi'' ! i = CAi''f i"
      unfolding CAi''_def apply (induction n) apply auto
      by (metis add.left_neutral diff_is_0_eq diff_zero length_map length_upt less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_map_upt)
    have COOL: "\<forall>i < n. CAi'' ! i \<in> M \<and> (CAi ! i) = (CAi'' ! i) \<cdot> (\<eta>s'' ! i) \<and> S (CAi'' ! i) \<cdot> (\<eta>s'' ! i) = S_M S M (CAi ! i)"
      using f_p \<eta>s''_ff CAi''_ff by auto
        
        (* The properties we need of CAi'' *)
    have CAi''_in_M: "\<forall>i < n. CAi'' ! i \<in> M" using COOL by auto
    have cai''_to_cai: "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" using COOL
      by (simp add: n)
    have selelele: "(\<forall>i < n. S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> (\<eta>s'' ! i))"
      using COOL by auto
        
    have "\<exists>DA'' \<eta>''. DA'' \<in> M \<and> (DA) = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA"
      using grounding S_M_grounding_of_clss select
      by (metis le_supE singletonI subsetCE)
    then obtain DA'' \<eta>'' where COOL2: "DA'' \<in> M \<and> DA = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA"
      by auto
        (* The properties we need of DA'' *)
    have DA''_in_M: "DA'' \<in> M" using COOL2 by auto
    have DA''_to_DA: "DA'' \<cdot> \<eta>'' = DA" using COOL2 by auto
    have selelele_d: "S DA'' \<cdot> \<eta>'' = S_M S M DA" using COOL2 by auto
        
    have "\<forall>CA \<in> set CAi''. CA \<in> M"
      by (metis CAi''_in_M in_set_conv_nth n(2))
      
    have "map (S_M S M) CAi = (map S CAi'') \<cdot>\<cdot>cl \<eta>s''"
    proof -
      have "\<forall>i<n. S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> \<eta>s'' ! i" using selelele by -
      then have "\<forall>i<n. (map (S_M S M) CAi) ! i = ((map S CAi'') ! i) \<cdot> \<eta>s'' ! i"
        using n by auto
      then show "map (S_M S M) CAi = (map S CAi'') \<cdot>\<cdot>cl \<eta>s''"
        using n by auto
    qed    
    
    show ?thesis
      using
      that
      \<open>DA'' \<in> M\<close> 
      \<open>DA'' \<cdot> \<eta>'' = DA\<close>
      \<open>S DA'' \<cdot> \<eta>'' = S_M S M DA\<close>
      \<open>\<forall>CA \<in> set CAi''. CA \<in> M\<close>
      \<open>CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi\<close>
      \<open>map (S_M S M) CAi = (map S CAi'') \<cdot>\<cdot>cl \<eta>s''\<close>
      n
      by blast
  qed
    
  note n = \<open>length CAi'' = n\<close> \<open>length \<eta>s'' = n\<close> n
    
  obtain DA' \<eta>' CAi' \<eta>s' where clauses':
    "length CAi' = n"
    "length \<eta>s' = n"
    
    "DA' \<in> M"
    "DA' \<cdot> \<eta>' = DA"
    "S DA' \<cdot> \<eta>' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    "map (S_M S M) CAi = (map S CAi') \<cdot>\<cdot>cl \<eta>s'"
    
    "var_disjoint (DA' # CAi')"
  proof -
    obtain \<rho>\<rho>s where \<rho>\<rho>s_p: "length \<rho>\<rho>s = length (DA'' # CAi'') \<and> (\<forall>\<rho>i \<in> set \<rho>\<rho>s. is_renaming \<rho>i) \<and> var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl \<rho>\<rho>s)"
      using make_var_disjoint[of "DA'' # CAi''"] by auto
    define \<rho> where "\<rho> = hd \<rho>\<rho>s"
    define \<rho>s where "\<rho>s = tl \<rho>\<rho>s"
      
    have "length \<rho>\<rho>s = Suc n" "length \<rho>s = n" 
      using \<rho>\<rho>s_p n \<rho>s_def
       apply auto done
    note n = \<open>length \<rho>\<rho>s = Suc n\<close> \<open>length \<rho>s = n\<close> n
      
    have vv: "var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl \<rho>\<rho>s)"
      using \<rho>\<rho>s_p by blast
        
    have \<rho>_ren: "is_renaming \<rho>"
      using \<rho>\<rho>s_p unfolding \<rho>_def
      by (metis hd_Cons_tl length_greater_0_conv list.simps(3) nth_Cons_0 nth_mem)
    have \<rho>s_ren: "\<forall>\<rho>i \<in> set \<rho>s. is_renaming \<rho>i"
      using \<rho>\<rho>s_p unfolding \<rho>s_def
      by (metis list.sel(2) list.set_sel(2))
    have "var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl (\<rho> # \<rho>s))"
      using \<rho>\<rho>s_p unfolding \<rho>_def \<rho>s_def
      by (metis length_greater_0_conv list.exhaust_sel list.simps(3))
        
    define \<rho>_inv where \<rho>_inv_p: "\<rho>_inv = inv_ren \<rho>" 
    define \<rho>s_inv where "\<rho>s_inv = map inv_ren \<rho>s"
      
    have "length \<rho>s_inv = n" 
      using \<rho>s_inv_def n by auto
        
    note n = \<open>length \<rho>s_inv = n\<close> n
      
    define CAi' where "CAi' = CAi'' \<cdot>\<cdot>cl \<rho>s"
    define DA' where "DA' = DA'' \<cdot> \<rho>"
      
    have "length CAi' = n" 
      unfolding CAi'_def using n by auto
        
    define \<eta>' where "\<eta>' = \<rho>_inv \<odot> \<eta>''"
    define \<eta>s' where "\<eta>s' = \<rho>s_inv \<odot>s \<eta>s''"
      
    have "length \<eta>s' = n"
      unfolding \<eta>s'_def using n by auto
        
    note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
      
    have \<rho>_i_inv_id: "\<forall>i<n. \<rho>s ! i \<odot> \<rho>s_inv ! i = id_subst"
      using n \<rho>s_inv_def \<rho>s_ren by auto
        
    have CAi'_in_M: "\<forall>i < n. CAi' ! i \<in> M" 
      unfolding CAi'_def using \<rho>s_ren M_renaming_invariant
        n
      by (simp add: \<open>\<forall>CA \<in> set CAi''. CA \<in> M\<close>)
    have cai'_cai: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    proof -
      have asdf: "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
        using \<open>CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi\<close> by auto
      have "CAi'' \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl \<rho>s_inv \<cdot>\<cdot>cl \<eta>s'' = CAi"
      proof -
        have lenlenlen: "length \<eta>s'' = n"
          by (simp add: \<open>length \<eta>s'' = n\<close>)
            
        have "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" using asdf by auto
        then have "\<forall>i < n. (CAi'' \<cdot>\<cdot>cl \<eta>s'') ! i = CAi ! i" 
          by simp
        then have "\<forall>i < n. (CAi''  ! i \<cdot> \<eta>s'' ! i) = CAi ! i" 
          using subst_cls_lists_nth asdf n by auto 
        then have "\<forall>i < n. (CAi''  ! i \<cdot> \<rho>s ! i \<cdot> \<rho>s_inv ! i \<cdot> \<eta>s'' ! i) = CAi ! i"
          using \<rho>_i_inv_id subst_cls_comp_subst comp_subst_assoc
          apply (auto simp del: subst_cls_comp_subst
              simp add: subst_cls_comp_subst[symmetric])
          done
        then have "\<forall>i < n. (CAi'' \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl \<rho>s_inv \<cdot>\<cdot>cl \<eta>s'') ! i = CAi ! i"
          using n by auto
        then show "CAi'' \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl \<rho>s_inv \<cdot>\<cdot>cl \<eta>s'' = CAi" using n by auto
      qed
      then have "CAi'' \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl (\<rho>s_inv \<odot>s \<eta>s'') = CAi" using n by auto
      then show ?thesis
        unfolding CAi'_def \<eta>s'_def by auto
    qed
    then have cai'_cai2: "\<forall>i<n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = CAi ! i"
      using n by auto
    have sel_cai'_cai: "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>s' ! i"
    proof (rule, rule)
      have selelele: "(\<forall>i < n. S_M S M (CAi ! i) = (S (CAi'' ! i)) \<cdot> (\<eta>s'' ! i))"
      proof -
        have "\<forall>i<n. map (S_M S M) CAi ! i = ((map S CAi'') \<cdot>\<cdot>cl \<eta>s'') ! i"
          using \<open>map (S_M S M) CAi = (map S CAi'') \<cdot>\<cdot>cl \<eta>s''\<close> n by auto
        then have "\<forall>i<n. S_M S M (CAi ! i) = ((map S CAi'') \<cdot>\<cdot>cl \<eta>s'') ! i"
          using n
          by (simp add: \<open>length \<eta>s'' = n\<close>) 
        then show selelele: "(\<forall>i < n. S_M S M (CAi ! i) = (S (CAi'' ! i)) \<cdot> (\<eta>s'' ! i))"
          using n by auto
      qed
          
      fix i
      assume a: "i < n"
      then have "S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> \<eta>s'' ! i" 
        using \<open>(\<forall>i < n. S_M S M (CAi ! i) = (S (CAi'' ! i)) \<cdot> (\<eta>s'' ! i))\<close> by auto
      also have "... = S (((CAi'' ! i) \<cdot> (\<rho>s ! i)) \<cdot> (\<rho>s_inv ! i)) \<cdot> \<eta>s'' ! i"
        using \<rho>_i_inv_id using a
        apply (auto simp del: subst_cls_comp_subst
            simp add: subst_cls_comp_subst[symmetric]) done
      also have "... = S (((CAi'' ! i) \<cdot> (\<rho>s ! i))) \<cdot> (\<rho>s_inv ! i) \<cdot> \<eta>s'' ! i"
        using inv_ren_ren
          (* since (\<rho>s_inv ! i) is a renaming. *) 
        using selection_renaming_invariant
        using \<rho>s_ren unfolding \<rho>s_inv_def
        by (simp add: a n) 
      also have "... = S (CAi' ! i) \<cdot> \<eta>s' ! i"
        unfolding CAi'_def \<eta>s'_def
        using n a by auto
      finally show "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>s' ! i" by auto
    qed
      
    have DA'_in_M: "DA' \<in> M"
      using M_renaming_invariant unfolding DA'_def using \<rho>_ren clauses'' by auto
    have DA'_DA: "DA' \<cdot> \<eta>' = DA"
      using DA'_def \<eta>'_def \<open>DA'' \<cdot> \<eta>'' = DA\<close> subst_cls_id_subst
      by (metis \<rho>_inv_p \<rho>_ren inv_ren_cancel_r subst_cls_comp_subst)
    have sel_DA'_DA: "S_M S M DA = S DA' \<cdot> \<eta>'"
    proof -
      have "S_M S M DA = S DA'' \<cdot> \<eta>''"
        by (simp add: clauses'') 
      also have "... = S (((DA'') \<cdot> (\<rho>)) \<cdot> (\<rho>_inv)) \<cdot> \<eta>''"
        using \<rho>_inv_p
        by (metis \<rho>_ren inv_ren_cancel_r subst_cls_comp_subst subst_cls_id_subst)
          
      also have "... = S (((DA'') \<cdot> (\<rho>))) \<cdot> (\<rho>_inv) \<cdot> \<eta>''"
        using inv_ren_ren
          (* since (\<rho>s_inv ! i) is a renaming. *) 
        using selection_renaming_invariant
        using \<rho>_ren using \<rho>_inv_p
        by auto
          
      also have "... = S DA' \<cdot> \<eta>'"
        unfolding DA'_def \<eta>'_def
        by auto
      finally show "S_M S M DA = S DA' \<cdot> \<eta>'" by auto
    qed
      
    have "\<forall>CA \<in> set CAi'. CA \<in> M"
      using CAi'_in_M n
      by (metis in_set_conv_nth) 
    have "map (S_M S M) CAi = (map S CAi') \<cdot>\<cdot>cl \<eta>s'"
      using sel_cai'_cai n
      by auto
        
    have "var_disjoint (DA' # CAi')"
      using DA'_def \<open>CAi' \<equiv> CAi'' \<cdot>\<cdot>cl \<rho>s\<close> \<open>var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl (\<rho> # \<rho>s))\<close> by auto
      
      
    show ?thesis
      using that
            \<open>length CAi' = n\<close>
    \<open>length \<eta>s' = n\<close>
    
    \<open>DA' \<in> M\<close>
    \<open>DA' \<cdot> \<eta>' = DA\<close>
    \<open>S_M S M DA = S DA' \<cdot> \<eta>'\<close>
    
    \<open>\<forall>CA \<in> set CAi'. CA \<in> M\<close>
    \<open>CAi' \<cdot>\<cdot>cl \<eta>s' = CAi\<close>
    \<open>map (S_M S M) CAi = (map S CAi') \<cdot>\<cdot>cl \<eta>s'\<close>
    
    \<open>var_disjoint (DA' # CAi')\<close>
    by metis
  qed
  
      
  note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
      
  obtain \<eta>_fo where clauses': (* Overwriting the old clauses' *)
    "DA' \<in> M"
    "DA' \<cdot> \<eta>_fo = DA"
    "S DA' \<cdot> \<eta>_fo = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>cl \<eta>_fo = CAi"
    "map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>_fo"
    
    "var_disjoint (DA' # CAi')"
  proof -
    from clauses' have "var_disjoint ((DA' # CAi'))"
      by auto
    then obtain \<eta>_fo where \<eta>_p: "(\<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> (\<eta>' # \<eta>s') ! i = S \<cdot> \<eta>_fo)" unfolding var_disjoint_def_2
      using n by force
    then have DA'_\<eta>_fo_sel: "\<forall>S. S \<subseteq># DA' \<longrightarrow> S \<cdot> \<eta>' = S \<cdot> \<eta>_fo" 
      by auto
    then have DA'_\<eta>: "DA' \<cdot> \<eta>' = DA' \<cdot> \<eta>_fo" by auto
        
    from \<eta>_p have cai'_\<eta>_fo_sel: "\<forall>i<n. \<forall>S. S \<subseteq># (CAi') ! i \<longrightarrow> S \<cdot> \<eta>s' ! i = S \<cdot> \<eta>_fo" 
      by auto
    then have cai'_\<eta>_fo: "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = (CAi'! i) \<cdot> \<eta>_fo"
      by auto
        
    have "\<forall>i < n. CAi' ! i \<in> M" using clauses' by auto
    have "CAi = CAi' \<cdot>cl \<eta>_fo"
    proof -
      {
        fix i
        assume "i<n"
        then have "CAi ! i = (CAi' \<cdot>cl \<eta>_fo) ! i" using n clauses' cai'_\<eta>_fo by auto
      }
      then show ?thesis using n by auto
    qed
    have "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>_fo"
    proof (rule, rule)
      fix i
      assume "i < n"
      have "S_M S M (CAi ! i) = (S (CAi' ! i)) \<cdot> (\<eta>s' ! i)"
      proof -
        have "(map (S_M S M) CAi) ! i  = ((map S CAi') \<cdot>\<cdot>cl \<eta>s') ! i"
          using clauses' by auto
        then show "S_M S M (CAi ! i)  = (S (CAi' ! i)) \<cdot> (\<eta>s' ! i)"
          using n \<open>i < n\<close> by auto
      qed
        
      also have "... = (S (CAi' ! i)) \<cdot> \<eta>_fo"
        using S.S_selects_subseteq cai'_\<eta>_fo_sel \<open>i<n\<close> by auto
      finally show "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>_fo"
        by auto
    qed
      
    have "DA' \<in> M" using clauses' by auto
    have "DA = DA' \<cdot> \<eta>_fo" using  DA'_\<eta>
      using clauses' by blast 
    have "S_M S M DA = S DA' \<cdot> \<eta>_fo"
    proof -
      have "S_M S M DA = S DA' \<cdot> \<eta>'"
        using clauses' by auto
      also have "... = S DA' \<cdot> \<eta>_fo"
        using S.S_selects_subseteq DA'_\<eta>_fo_sel by auto
      finally show ?thesis by auto
    qed
     
    have "map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>_fo"
    proof -
      have "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>_fo"
        using \<open>\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>_fo\<close> by -
      then have "\<forall>i < n. (map (S_M S M) CAi) ! i = ((map S CAi') \<cdot>cl \<eta>_fo) ! i"
        using n by auto
      then show "map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>_fo" using n by auto
    qed    
          
        
      
    show ?thesis
      using that
            \<open>DA' \<in> M\<close>
    \<open>DA = DA' \<cdot> \<eta>_fo\<close>
    \<open>S_M S M DA = S DA' \<cdot> \<eta>_fo\<close>
    
    \<open>\<forall>CA \<in> set CAi'. CA \<in> M\<close>
    \<open>CAi = CAi' \<cdot>cl \<eta>_fo\<close>
    \<open>map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>_fo\<close>
    
    \<open>var_disjoint (DA' # CAi')\<close>
    by auto  
  qed
      
  obtain \<eta> where
    "DA' \<in> M"
    "DA' \<cdot> \<eta> = DA"
    "S DA' \<cdot> \<eta> = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>cl \<eta> = CAi"
    "map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>"
    
    "is_ground_subst \<eta>"
    "var_disjoint (DA' # CAi')"
  proof -
    obtain \<eta> where \<eta>_p: "is_ground_subst \<eta> \<and> (\<forall>i<length (DA' # CAi'). \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> \<eta>_fo = S \<cdot> \<eta>)"
      using make_ground_subst2[of "DA' # CAi'" \<eta>_fo] grounding \<open>CAi' \<cdot>cl \<eta>_fo = CAi\<close> \<open>DA' \<cdot> \<eta>_fo = DA\<close> grounding_ground
      by (metis Un_insert_left is_ground_cls_list_def list.simps(15) subsetCE subst_cls_list_Cons sup_bot.left_neutral) 
        
        
    have "\<forall>i < n. CAi' ! i \<in> M" using clauses' n by auto
    have "CAi = CAi' \<cdot>cl \<eta>"
    proof -
      {
        fix i
        assume "i<n"
        then have "CAi ! i = (CAi' \<cdot>cl \<eta>_fo) ! i" using \<open>CAi' \<cdot>cl \<eta>_fo = CAi\<close> by auto
        then have "CAi ! i = (CAi' \<cdot>cl \<eta>) ! i" using n \<eta>_p \<open>i<n\<close> by auto
      }
      then show ?thesis using n by auto
    qed
    have "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>"
    proof -
      {
        fix i
        assume "i<n"
        have "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>_fo"
        proof -
          have "map (S_M S M) CAi = map S CAi' \<cdot>cl \<eta>_fo" using clauses' by auto
          then have "(map (S_M S M) CAi) ! i = (map S CAi' \<cdot>cl \<eta>_fo) ! i" by auto
          then have "S_M S M (CAi ! i) = ((map S CAi') \<cdot>cl \<eta>_fo) ! i" using n \<open>i<n\<close> by auto
          then show "S_M S M (CAi ! i) = (S (CAi' ! i)) \<cdot> \<eta>_fo" using n \<open>i<n\<close> by auto
        qed
        then have "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>" using n \<eta>_p \<open>i<n\<close> S.S_selects_subseteq by auto
      }
      then show ?thesis using n by auto
    qed
      
    have "DA' \<in> M" using clauses' by auto
    have "DA = DA' \<cdot> \<eta>" using \<open>DA' \<cdot> \<eta>_fo = DA\<close> \<eta>_p by auto
    have "S_M S M DA = S DA' \<cdot> \<eta>"
      using \<open>S DA' \<cdot> \<eta>_fo = S_M S M DA\<close> using \<eta>_p S.S_selects_subseteq by auto
    have prime_clauses_10: "is_ground_subst \<eta>" using \<eta>_p by auto
       
    have "map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>"
      using \<open>\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>\<close>
        n by auto
        
    show ?thesis using that 
    \<open>DA' \<in> M\<close>
    \<open>DA = DA' \<cdot> \<eta>\<close>
    \<open>S_M S M DA = S DA' \<cdot> \<eta>\<close>
    
    \<open>\<forall>CA \<in> set CAi'. CA \<in> M\<close>
    \<open>CAi = CAi' \<cdot>cl \<eta>\<close>
    \<open>map (S_M S M) CAi = (map S CAi') \<cdot>cl \<eta>\<close>
    
    \<open>is_ground_subst \<eta>\<close>
    \<open>var_disjoint (DA' # CAi')\<close>
    by auto 
  qed
      
  show ?thesis sorry
qed


end

(* lifting lemma:
I think a better tactic is to use ord_resolve in the conclusion
and then I can probably remove the renaming assumption on M
*)

  

end