(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull
*)

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
  
definition "maximal_in A DAs \<equiv> (\<forall>B \<in> atms_of DAs. \<not> less_atm A B)"
  (* This definition is a bit inconsistent compared to the ground case since 
     there it was defined as THE maximum instead of SOME upper bound. *)
abbreviation "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of CAis. \<not> less_eq_atm A B)"

(* Inspiration from supercalc *)
inductive eligible :: "'s \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
  "S DAi = negs (mset Ai) 
   \<or> 
   (
     S DAi = {#} 
     \<and> length Ai = 1 
     \<and> maximal_in ((Ai ! 0) \<cdot>a \<sigma>) (DAi \<cdot> \<sigma>)
   )
   \<Longrightarrow> eligible \<sigma> Ai DAi"
  
lemma eligible_simp:
  " eligible \<sigma> Ai DAi \<longleftrightarrow> (S DAi = negs (mset Ai) 
   \<or> 
   (
     S DAi = {#} 
     \<and> length Ai = 1 
     \<and> maximal_in ((Ai ! 0) \<cdot>a \<sigma>) (DAi \<cdot> \<sigma>)
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
   ord_resolve (CAi \<cdot>\<cdot>cl P) (DAi \<cdot> \<rho>) E \<Longrightarrow>
   ord_resolve_rename CAi DAi E"
  
lemma ord_resolve_raw_imp_ord_resolve: "ord_resolve CAs D E \<Longrightarrow> ord_resolve_rename CAs D E"
  apply (rule ord_resolve_rename[of id_subst "replicate (length CAs) id_subst"])
  apply auto
  done

lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_cls_list CAi" and
    gr_d: "is_ground_cls DAi" and
    res_e_re: "ord_resolve_rename CAi DAi E"
  shows "ord_resolve CAi DAi E"
  using res_e_re proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>" using ord_resolve_rename(2) .
  have len: "length P = length CAi" using ord_resolve_rename(3) .
  have res_e: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DAi \<cdot> \<rho>) E" using ord_resolve_rename(4) .
  
  have "CAi \<cdot>\<cdot>cl P = CAi" using len gr_cc by auto
  moreover
  have "DAi \<cdot> \<rho> = DAi" using gr_d by auto
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
    res_e: "ord_resolve CAi DAi E" and
    cc_d_true: "I \<Turnstile>fom mset CAi + {#DAi#}"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve n Ci Aij Ai \<tau> D)
  have dai: "DAi = D + negs (mset Ai)" using ord_resolve by -
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
  hence cc_true: "I \<Turnstile>m (mset CAi) \<cdot>cm \<tau> \<cdot>cm \<sigma>" and d_true: "I \<Turnstile> DAi \<cdot> \<tau> \<cdot> \<sigma>"
    using true_fo_cls_mset_inst[OF cc_d_true, of "\<tau> \<odot> \<sigma>"] by auto 
      
  from mgu have unif: "\<forall>i<n. \<forall>A\<in>#Aij ! i. A \<cdot>a \<tau> = Ai ! i \<cdot>a \<tau>" 
    using mgu_unifier using ai_len aij_len by blast
      
  show "\<forall>i<n. S (CAi ! i) = {#} \<Longrightarrow> I \<Turnstile> E \<cdot> \<sigma>"
  proof (cases "\<forall>A \<in> set Ai. A \<cdot>a \<tau> \<cdot>a \<sigma> \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs (mset Ai) \<cdot> \<tau> \<cdot> \<sigma>"
      unfolding true_cls_def by auto
    hence "I \<Turnstile> D \<cdot> \<tau> \<cdot> \<sigma>"
      using d_true dai by auto
    thus ?thesis
      unfolding e by simp
  next
    case False
    then obtain i where a_in_aa: "i < length CAi" and a_false: "(Ai ! i) \<cdot>a \<tau> \<cdot>a \<sigma> \<notin> I"
      using dai len by (metis in_set_conv_nth) 
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
    res_e: "ord_resolve_rename CAi DAi E" and
    cc_d_true: "I \<Turnstile>fom (mset CAi) + {#DAi#}"
  shows "I \<Turnstile>fo E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have len: "length P = length CAi" using ord_resolve_rename by -
  have res: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DAi \<cdot> \<rho>) E" using ord_resolve_rename by -
  have "I \<Turnstile>fom (mset (CAi \<cdot>\<cdot>cl P)) + {#DAi \<cdot> \<rho>#}"
    using subst_sound_scl[OF len , of I] subst_sound[of I DAi]
    cc_d_true by (simp add: true_fo_cls_mset_def2)
    
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAi \<cdot>\<cdot>cl P" "DAi \<cdot> \<rho>" E I, OF res]
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

lemma maximal_in_gen:
  assumes "maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "maximal_in A C"
proof -
  from assms have "maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)" by -
  hence "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_atm (A \<cdot>a \<sigma>) B" unfolding maximal_in_def by -
  hence ll: "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>'))" unfolding less_atm_iff by -
  have "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>'))"
  proof (* This proof should ideally not be necessary *)
    fix B
    assume "B \<in> atms_of C"
    then have "B \<cdot>a \<sigma> \<in> (atms_of C) \<cdot>as \<sigma>" unfolding subst_atms_def by auto (* this should be automatic *)
    then have "B \<cdot>a \<sigma> \<in> atms_of (C \<cdot> \<sigma>)" unfolding subst_cls_def subst_lit_def subst_atms_def atms_of_def
      apply auto
      by (metis (mono_tags, lifting) imageI literal.map_sel(1) literal.map_sel(2))
    then show "\<not> (\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < (B \<cdot>a \<sigma>) \<cdot>a \<sigma>')" using ll by auto 
  qed 
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>'))"
    using is_ground_comp_subst by fastforce
  hence "\<forall>B\<in>atms_of C. \<not> (less_atm A B)" unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def maximal_in_def by auto
qed
    
  
lemma another_swap: "atms_of (C \<cdot> \<sigma>) = atms_of C \<cdot>as \<sigma>"
  unfolding subst_cls_def subst_atms_def subst_lit_def 
  apply auto
   apply (smt atms_of_def image_iff literal.map_sel(1) literal.map_sel(2) set_image_mset)+
  done
    
  
  
lemma str_maximal_in_gen: (* a better proof might reuse the lemma maximal_in_gen *)
  assumes "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "str_maximal_in A C"
proof -
  from assms have "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)" by -
  hence "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_eq_atm (A \<cdot>a \<sigma>) B" by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> (less_atm (A \<cdot>a \<sigma>) B \<or> A \<cdot>a \<sigma> = B)" unfolding less_eq_atm_def by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B)" unfolding less_atm_iff by -
  hence "\<forall>B\<in>atms_of (C) \<cdot>as \<sigma>. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B)" using another_swap by auto
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)" 
    unfolding subst_atms_def by auto
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A = B)"
    using is_ground_comp_subst by fastforce
  hence "\<forall>B\<in>atms_of C. \<not> (less_atm A B \<or> A = B)" unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def by auto
qed
  
lemma mk_ground_subst:
  assumes "is_ground_cls C"
  assumes "C' \<cdot> \<sigma> = C"
  obtains \<tau> where
    "is_ground_subst \<tau>"
    "C' \<cdot> \<tau> = C"
using assms
  by (metis ex_ground_subst is_ground_comp_subst is_ground_subst_cls subst_cls_comp_subst) (* I'm very impressed sledgehammer managed to do this... *)
    
lemma lololol:
  assumes "length Ci = n"
  assumes "length CAi = n"
  assumes "\<forall>i<n.  Ci ! i \<subseteq># CAi ! i "
  shows "\<Union>#mset Ci \<subseteq># \<Union>#(mset CAi)"
  using assms proof (induction n arbitrary: Ci CAi)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc have "\<forall>i<n. tl Ci ! i \<subseteq># tl CAi ! i"
    by (simp add: nth_tl) 
  hence "\<Union>#mset (tl Ci) \<subseteq># \<Union>#mset (tl CAi)" using Suc by auto
  moreover
  have "hd Ci \<subseteq># hd CAi" using Suc
    by (metis Nitpick.size_list_simp(2) hd_conv_nth nat.simps(3) zero_less_Suc) 
  ultimately
  show "\<Union>#mset Ci \<subseteq># \<Union>#mset CAi"
    apply auto
    by (metis (no_types, hide_lams) One_nat_def Suc_pred Suc(2) Suc(3) length_tl list.exhaust list.sel(1) list.sel(2) list.sel(3) n_not_Suc_n subset_mset.add_mono sum_list.Cons zero_less_Suc)
qed
    
lemma ground_resolvent_subset:
  assumes gr_c: "is_ground_cls_list CAi"
  assumes gr_d: "is_ground_cls DAi"
  assumes resolve: "ord_resolve SSS CAi DAi E"
  shows "E \<subseteq># (\<Union>#(mset CAi)) + DAi"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
  hence "\<forall>i<n.  Ci ! i \<subseteq># CAi ! i " by auto
  hence cisucai: "\<Union>#mset Ci \<subseteq># \<Union>#(mset CAi)"
    using lololol ord_resolve(3) ord_resolve(4) by force
  hence gr_ci: "is_ground_cls_list Ci" using gr_c
    by (metis is_ground_cls_Union_mset is_ground_cls_list_def is_ground_cls_mono is_ground_cls_mset_def set_mset_mset)
  have dsudai :"D \<subseteq># DAi" by (simp add: local.ord_resolve(1)) 
  hence gr_di: "is_ground_cls D"
    using gr_d is_ground_cls_mono by auto     
  
  have "is_ground_cls (\<Union>#mset Ci + D)" using gr_ci gr_di
    unfolding is_ground_cls_def is_ground_cls_list_def
    by (metis in_Union_mset_iff set_mset_mset union_iff)
  then have fffff: "(\<Union>#mset Ci + D) = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by auto
  from this ord_resolve have "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by -
  hence "E = (\<Union>#mset Ci + D)" using fffff by auto
  then show ?thesis using cisucai dsudai by (auto simp add: subset_mset.add_mono)
qed
    
lemma ground_resolvent_ground: (* This proof should be more automatic I think... *)
  assumes "is_ground_cls_list CAi"
  assumes "is_ground_cls DAi"
  assumes "ord_resolve SSS CAi DAi E"
  shows "is_ground_cls E"
proof -
  from assms have "E \<subseteq># (\<Union>#(mset CAi)) + DAi" using ground_resolvent_subset by auto
  then have "\<forall>e \<in># E. e \<in># \<Union>#(mset CAi) \<or> e \<in># DAi" by auto
  then show "is_ground_cls E" unfolding is_ground_cls_def
    apply auto
    using assms(1) unfolding is_ground_cls_list_def is_ground_cls_def
    by (metis assms(2) in_mset_sum_list2 is_ground_cls_def)    
qed
  
lemma empty_subst_for_atoms: "A \<cdot>am \<eta> = {#} \<longleftrightarrow> A = {#}"  
  unfolding subst_atm_mset_def by auto
    
lemma empty_subst_for_atoms_right: "A \<cdot>am \<eta> = {#} \<Longrightarrow> A = {#}"  
  unfolding subst_atm_mset_def by auto
    

lemma empty_subst: "C \<cdot> \<eta> = {#} \<longleftrightarrow> C = {#}"
unfolding subst_cls_def by auto
  
  
(* really just a reformulation of S_M_grounding_of_clss *)
lemma uw2: "selection S \<longrightarrow> (\<forall>C\<sigma>. C\<sigma> \<in> grounding_of_clss M \<longrightarrow> (\<exists>D \<sigma>. D \<in> M \<and> C\<sigma> = D \<cdot> \<sigma> \<and> (S D) \<cdot> \<sigma> = (S_M S M C\<sigma>)))"
   using S_M_grounding_of_clss by metis

(* A lemma that states that a list of clauses can be standardized apart. *)
thm make_var_disjoint

lemma mset_equals_size:
  assumes "X \<subseteq># Y"
  assumes "size (X) = size (Y)"
  shows "X = Y"
    using assms
    using mset_subset_size subset_mset_def by fastforce 
      
      
lemma swapii: "i < length Aij' \<Longrightarrow> (Aij' \<cdot>aml \<eta>) ! i = (Aij'  ! i)  \<cdot>am \<eta>"
  unfolding subst_atm_mset_list_def
    by auto
      
lemma something_intersection:
  assumes "X \<subseteq># D' + T"
  assumes "\<And>L2. count L2 D' + count L2 T = count L2 (D' + T)"
  shows "X \<subseteq># T"
  using assms
  oops
    
lemma image_mset_Diff':
 "Y \<in># X \<Longrightarrow> image_mset f (X - {#Y#}) = (image_mset f X) - {#f Y#}"
  by (simp add: image_mset_Diff)
    
lemma map2_add_mset_map:
  assumes "length Aij' = n"
  assumes "length Ai' = n"
  shows "(map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) = (map2 add_mset Ai' Aij' \<cdot>aml \<eta>)"
  using assms proof (induction n arbitrary: Aij' Ai')
  case (Suc n)
  then have "map2 add_mset (tl Ai' \<cdot>al \<eta>) (tl Aij' \<cdot>aml \<eta>) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>"
    by simp
  then have "map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>)) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>"
    unfolding subst_atm_list_def subst_atm_mset_list_def
    by (simp add: map_tl)
      
  moreover 
  have Succ: "length (Ai' \<cdot>al \<eta>) = Suc n" "length (Aij' \<cdot>aml \<eta>) = Suc n"
     apply -
    using Suc(3) apply auto[]
    using Suc(2) unfolding subst_atm_mset_list_def apply auto[] (* unfolding should not be necessary  *)
    done
  then have "length (tl (Ai' \<cdot>al \<eta>)) = n" "length (tl (Aij' \<cdot>aml \<eta>)) = n"
     apply -
     apply auto
      done
  then have "length (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) = n" 
    "length (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) = n"
     apply -
     apply auto[]
    using Suc(3) Suc (2)
    unfolding subst_atm_mset_list_def
    apply auto
      done
  ultimately
  have "\<forall>i < n. (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) ! i = (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) ! i"
    by auto
  then have "\<forall>i < n. tl (map2 add_mset ( (Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) ! i = tl (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! i"
    using  Suc(2) Suc(3) Succ
    by (simp add: map2_tl map_tl subst_atm_mset_list_def) 

  moreover have nn: "length (map2 add_mset ((Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) = Suc n"
    "length (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) = Suc n"
     apply -
    using Succ apply auto
      using Suc unfolding subst_atm_mset_list_def by auto (* I should not have to unfold *)
  ultimately have "\<forall>i. i < Suc n \<longrightarrow> i > 0 \<longrightarrow> (map2 add_mset ((Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) ! i = (map2 add_mset ( Ai') (Aij') \<cdot>aml \<eta>) ! i"
    apply auto
    by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Succ(1) Succ(2) \<open>length (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) = n\<close> 
         \<open>map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>)) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>\<close> less_Suc_eq_0_disj map2_tl map_tl neq0_conv nth_tl subst_atm_mset_list_def)
      moreover
  have "add_mset (hd Ai' \<cdot>a \<eta>) (hd Aij' \<cdot>am \<eta>) = add_mset (hd Ai') (hd Aij') \<cdot>am \<eta>"
    unfolding subst_atm_mset_def by auto
  then have "(map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) ! 0  = (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! 0"
    using Suc
    by (simp add: Succ(2) substitution_ops.subst_atm_mset_def swapii) 
  ultimately
  have "\<forall>i < Suc n. (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) ! i  = (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! i"
    using Suc by auto
  then show ?case 
    using nn list_eq_iff_nth_eq by metis
next
  case 0 then show ?case 
    apply auto
    unfolding subst_atm_mset_list_def
    apply auto
    done
qed
  
theorem is_unifiers_comp: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset Ai' Aij') \<cdot>ass \<eta>) \<longleftrightarrow> is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset Ai' Aij'))"
  unfolding is_unifiers_def is_unifier_def subst_atmss_def
  by auto
    
theorem var_disjoint_Cons: (* Not used. Still kind of nice, I guess *)
  assumes "var_disjoint (C#Cs)"
  shows "var_disjoint Cs"
  unfolding var_disjoint_def proof (rule, rule)
  fix \<sigma>s :: "'s list"
  assume "length \<sigma>s = length Cs"
  then have "length (undefined # \<sigma>s) = length (C # Cs)" by auto
  then obtain \<tau> where "(C # Cs) \<cdot>\<cdot>cl (undefined # \<sigma>s) = (C # Cs) \<cdot>cl \<tau>" using assms unfolding var_disjoint_def by blast
  then have "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    by simp
  then show "\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>" by blast  
qed

theorem tl_subst: "length Cs = length \<rho>s \<Longrightarrow> tl (Cs \<cdot>\<cdot>cl \<rho>s) = (tl Cs) \<cdot>\<cdot>cl (tl \<rho>s)"
  apply (induction Cs arbitrary: \<rho>s)
   apply auto
  unfolding subst_cls_lists_def
    unfolding map2_def
  by (metis (no_types, lifting) list.exhaust_sel list.sel(3) list.size(3) map_tl nat.simps(3) zip_Cons_Cons)


lemma inv_ren_ren: "is_renaming s \<Longrightarrow> is_renaming (inv_ren s)"
  sorry    
  
lemma usf: "mset (map f (list_of_mset M)) = image_mset f M"
  by auto
  
lemma uuu: "set (list_of_mset S) = set_mset S"
  by (metis (full_types) ex_mset list_of_mset_def set_mset_mset someI_ex)
    
thm var_disjoint_def
      
(* A more useful definition of variable disjointness *)
definition var_disjoint_2 :: "'a clause list \<Rightarrow> bool" where
  "var_disjoint_2 Cs = 
    (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> 
      (\<exists>\<tau>. 
        (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>)
      )
    )"
 
lemma var_var2: "var_disjoint Cs \<Longrightarrow> var_disjoint_2 Cs"
  sorry
    
lemma make_ground_subst2: 
  "is_ground_cls_list (CC \<cdot>cl \<sigma>) \<Longrightarrow>
       \<exists>\<tau>. (\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma> = S \<cdot> \<tau>)"
  sorry
    
term is_ground_cls
  
lemma very_specific_lemma:
  assumes "negs (mset Ai) = SDAi' \<cdot> \<eta>"
  assumes "\<forall>L \<in># SDAi'. is_neg L"
  shows "\<exists>Ai'. negs (mset Ai') = SDAi' \<and> Ai' \<cdot>al \<eta> = Ai"
using assms proof (induction Ai arbitrary: SDAi')
  case Nil
  then have "negs (mset []) = SDAi' \<and> [] \<cdot>al \<eta> = []"
    by (simp add: empty_subst) 
  then show ?case by blast
next
  case (Cons a Ai)
  then have "\<exists>aa. aa \<in># SDAi' \<and> (atm_of aa) \<cdot>a \<eta> = a"
    by (metis (no_types, lifting) add_mset_remove_trivial add_mset_remove_trivial_eq another_swap atms_of_def atms_of_negg imageE mset.simps(2) subst_atms_def)
  then obtain aa where aa_p: "aa \<in># SDAi' \<and> (atm_of aa) \<cdot>a \<eta> = a" 
    by blast
  then have aa_p2: "aa = Neg ((atm_of aa))" using Cons by auto
  
  have "negs (mset (a # Ai)) = SDAi' \<cdot> \<eta>"
    using Cons by auto
  then have "(negs (mset (a # Ai))) - {# Neg a#} = (SDAi' \<cdot> \<eta> ) - {# Neg a#}"
    by metis
  then have "(negs (mset (Ai))) = (SDAi' \<cdot> \<eta> ) - {# Neg a#}"
    by auto
  then have "(negs (mset (Ai))) = (SDAi' \<cdot> \<eta> ) - {# Neg ((atm_of aa) \<cdot>a \<eta>)#}"
    using aa_p by auto
  then have "(negs (mset (Ai))) = (SDAi' \<cdot> \<eta> ) - {# Neg ((atm_of aa))#} \<cdot> \<eta>"
    by (metis image_mset_single subst_atm_mset_single subst_cls_negs)
  then have "(negs (mset (Ai))) = ((SDAi') - {# Neg ((atm_of aa))#}) \<cdot> \<eta>"
    using aa_p aa_p2
    by (metis (mono_tags, lifting) image_mset_Diff' image_mset_single subst_cls_def)
  then have "\<exists>Ai'. negs (mset Ai') = remove1_mset (Neg (atm_of aa)) SDAi' \<and> Ai' \<cdot>al \<eta> = Ai" using Cons(1)[of "((SDAi') - {# Neg ((atm_of aa))#})"]
    using Cons(3)
    by (meson in_diffD)
  then obtain Ai' where "negs (mset Ai') = remove1_mset (Neg (atm_of aa)) SDAi' \<and> Ai' \<cdot>al \<eta> = Ai"
    by blast
  then have "negs (mset (atm_of aa#Ai')) = SDAi' \<and> (atm_of aa#Ai') \<cdot>al \<eta> = a # Ai"
    using aa_p aa_p2 by auto
  then show ?case by blast
qed
  
lemma atomlist_to_negs_equality:
  assumes "Ai' \<cdot>al \<eta> = Ai"
  shows "negs (mset Ai') \<cdot> \<eta> = negs (mset Ai)"
proof -
  from assms have "map Neg (Ai' \<cdot>al \<eta>) = map Neg Ai" by auto
  then have "mset (map Neg (Ai' \<cdot>al \<eta>)) = mset (map Neg Ai)" by auto
  then show ?thesis
    by simp
qed

lemma nice_theorem_about_msets_and_lists: (* The proof looks suspiciously like very_specific_lemma *)
  assumes "mset lC = C"
  assumes "image_mset \<eta> C' = C"
  shows "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
using assms proof (induction lC arbitrary: C C')
  case Nil
  then show ?case by auto
next
  case (Cons a lC)
  from Cons have "mset lC = C - {# a #}" by auto 
  moreover
  from Cons obtain aa where aa_p: "aa \<in># C' \<and> \<eta> aa = a"
    by (metis msed_map_invR mset.simps(2) union_single_eq_member)
  from Cons this have "image_mset \<eta> (C' - {# aa #}) = C - {# a #}"
    by (simp add: image_mset_Diff')
  ultimately
  have "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C' - {# aa #}" 
    using Cons(1) by simp
  then obtain qC' where "map \<eta> qC' = lC \<and> mset qC' = C' - {# aa #}"
    by blast
  then have "map \<eta> (aa # qC') = a # lC \<and> mset (aa # qC') = C'"
    using aa_p Cons(2) by auto
  then show ?case
    by metis    
qed
  
lemma obviously: 
  assumes "image_mset \<eta> C' = C"
  assumes "A \<subseteq># C"
  shows "\<exists>A'. image_mset \<eta> A' = A \<and> A' \<subseteq># C'"
  using assms
proof -
  define lA where "lA = list_of_mset A"
  define lD where "lD = list_of_mset (C-A)"
  define lC where "lC = lA @ lD"
    
  have "mset lC = C"
    using assms(2) unfolding lD_def lC_def lA_def by auto
  then have "\<exists>qC'. map \<eta> qC' = lC \<and> mset qC' = C'"
    using assms(1) nice_theorem_about_msets_and_lists[of lC C \<eta> C'] by blast
  then obtain qC' where qC'_p: "map \<eta> qC' = lC \<and> mset qC' = C'"
    by auto
  let ?lA' = "take (length lA) qC'"
  have m: "map \<eta> ?lA' = lA"
    using qC'_p lC_def
    by (metis append_eq_conv_conj take_map)
  let ?A' = "mset ?lA'"    
  
  have "image_mset \<eta> ?A' = A"
    using m using lA_def
    by (metis (full_types) ex_mset list_of_mset_def mset_map someI_ex)
  moreover
  have "?A' \<subseteq># C'"  
    using qC'_p  assms(2) unfolding lA_def
    using mset_take_subseteq by blast
  ultimately show ?thesis by blast
qed
    
lemma ord_resolve_lifting: 
  fixes CAi
  assumes resolve: "ord_resolve (S_M S M) CAi DAi E" 
    (* Isn't the definition of S_M kind of weird? It seems odd that we let hilbert make choices about our selection function. This is probably not how a prover works. He probably make the choice
       him self, clever or not. *)
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" 
      (* Here I could use a weaker invariant, namely that if nothing is selected then still nothing is selected. That is how it is done in supercalc. *)
    and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
    and grounding: "{DAi} \<union> (set CAi) \<subseteq> grounding_of_clss M" (* I'm not sure E should be here. I think not. *)
  obtains \<eta> \<eta>2 CAi' DAi' E' where
    "is_ground_subst \<eta>"
    "is_ground_subst \<eta>2"
    "ord_resolve S CAi' DAi' E'" 
    "CAi = CAi' \<cdot>cl \<eta>" "DAi = DAi' \<cdot> \<eta>" "E = E' \<cdot> \<eta>2" 
      (* In the chapter, \<eta> and \<eta>2 are the same since they can ensure E' automatically variable disjoint from CAi' DAi', 
         our calculus differs in this respect. *)
    "{DAi'} \<union> set CAi' \<subseteq> M" (* I'm not sure E' should be here. I think not *)
  using resolve proof ((*atomize_elim, *)cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
    
  note n = \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  interpret S: selection S by (rule select)
      
      (* Choose the D'' and the C'', i.e. the first-order clauses before being standardized apart *)
      
  have uuu: "\<forall>CA \<in> set CAi. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> (CA) = CA'' \<cdot> \<eta>c'' \<and> S (CA'') \<cdot> \<eta>c'' = S_M S M CA "
    using grounding uw2 select by auto
      
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
      
  have lcai'': "length CAi'' = n" unfolding CAi''_def by auto
  have "length \<eta>s'' = n" unfolding \<eta>s''_def by auto
  have "\<forall>i < n. CAi'' ! i \<in> M" using COOL by auto
  have cai''_to_cai: "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" using COOL
    by (simp add: \<open>length CAi'' = n\<close> \<open>length \<eta>s'' = n\<close> local.ord_resolve(3)) 
  have selelele: "(\<forall>i < n. S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> (\<eta>s'' ! i))"
    using COOL by auto
      
  have "\<exists>DAi'' \<eta>''. DAi'' \<in> M \<and> (DAi) = DAi'' \<cdot> \<eta>'' \<and> S (DAi'') \<cdot> \<eta>'' = S_M S M DAi"
    using grounding uw2 select by auto
  then obtain DAi'' \<eta>'' where COOL2: " DAi'' \<in> M \<and> (DAi) = DAi'' \<cdot> \<eta>'' \<and> S (DAi'') \<cdot> \<eta>'' = S_M S M DAi"
    by auto
      
  have "DAi'' \<in> M" using COOL2 by auto
  have "DAi'' \<cdot> \<eta>'' = DAi" using COOL2 by auto
  have "S (DAi'') \<cdot> \<eta>'' = S_M S M DAi" using COOL2 by auto
      
      (* Choose the D' and the C', i.e. the first-order clauses standardized apart *)
  obtain \<rho>s'' where \<rho>s''_p: "length \<rho>s'' = length (DAi'' # CAi'') \<and> Ball (set \<rho>s'') is_renaming \<and> var_disjoint ((DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'')"
    using make_var_disjoint[of "DAi'' # CAi''"] by auto (* TODO remove Ball noatation *)
  define \<rho> where "\<rho> = hd \<rho>s''"
  define \<rho>s where "\<rho>s = tl \<rho>s''"
    
  have "length \<rho>s'' = Suc n" "length \<rho>s = n" 
    using \<rho>s''_p n \<rho>s_def
      apply auto done
  
  note n = \<open>length \<rho>s'' = Suc n\<close> \<open>length \<rho>s = n\<close> n
    
  have l\<rho>s: "length \<rho>s = length CAi''"
    using \<rho>s''_p unfolding \<rho>s_def apply auto done
  have \<rho>_ren: "is_renaming \<rho>"
    using \<rho>s''_p unfolding \<rho>_def
    by (metis hd_Cons_tl length_greater_0_conv list.simps(3) nth_Cons_0 nth_mem)
  have \<rho>s_ren: "\<forall>\<rho>i \<in> set \<rho>s. is_renaming \<rho>i"
    using \<rho>s''_p unfolding \<rho>s_def
    by (metis list.sel(2) list.set_sel(2))
  have "var_disjoint ((DAi'' # CAi'') \<cdot>\<cdot>cl (\<rho> # \<rho>s))"
    using \<rho>s''_p unfolding \<rho>_def \<rho>s_def
    by (metis length_greater_0_conv list.exhaust_sel list.simps(3))
      
  define \<rho>_inv where \<rho>_inv_p: "\<rho>_inv = inv_ren \<rho>" 
         
  define \<rho>s_inv where "\<rho>s_inv = map inv_ren \<rho>s"
    
  have "length \<rho>s_inv = n" 
    using \<rho>s_inv_def n by auto
      
  define CAi' where "CAi' = CAi'' \<cdot>\<cdot>cl \<rho>s"
  define DAi' where "DAi' = DAi'' \<cdot> \<rho>"
    
  have "length CAi' = n" 
    unfolding CAi'_def using n by auto
    
  define \<eta>' where "\<eta>' = \<rho>_inv \<odot> \<eta>''"
  define \<eta>s' where "\<eta>s' = \<rho>s_inv \<odot>s \<eta>s''"
    
  have "length \<eta>s' = n"
    unfolding \<eta>s'_def using n sorry
  
  note n = \<open>length \<rho>s_inv = n\<close> \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
    
  have \<rho>_i_inv_id: "\<forall>i<n.  \<rho>s!i \<odot> \<rho>s_inv !i = id_subst"
    using n \<rho>s_inv_def \<rho>s_ren by auto
    
  have lenlen: "length CAi' = n"
    by (simp add: \<open>CAi' \<equiv> CAi'' \<cdot>\<cdot>cl \<rho>s\<close> l\<rho>s lcai'')  
  have "\<forall>i < n. CAi' ! i \<in> M" 
    unfolding CAi'_def using \<rho>s_ren M_renaming_invariant
      lcai'' l\<rho>s
    by (simp add: \<open>\<forall>i<n. CAi'' ! i \<in> M\<close>)
  have cai'_cai: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
  proof -
    have asdf: "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
      using cai''_to_cai by auto
    have "CAi'' \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl \<rho>s_inv \<cdot>\<cdot>cl \<eta>s'' = CAi"
    proof -
      have lenlenlen: "length \<eta>s'' = n"
        by (simp add: \<open>length \<eta>s'' = n\<close>)
      
      have "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" using asdf by auto
      then have "\<forall>i < n. (CAi'' \<cdot>\<cdot>cl \<eta>s'') ! i = CAi ! i" 
        by simp
      then have "\<forall>i < n. (CAi''  ! i \<cdot> \<eta>s'' ! i) = CAi ! i" 
        using subst_cls_lists_nth asdf lcai'' n by auto 
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
    fix i
    assume a: "i < n"
    then have "S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> \<eta>s'' ! i" using selelele by auto
    also have "... = S (((CAi'' ! i) \<cdot> (\<rho>s ! i)) \<cdot> (\<rho>s_inv ! i)) \<cdot> \<eta>s'' ! i"
      using \<rho>_i_inv_id using a
        apply (auto simp del: subst_cls_comp_subst
            simp add: subst_cls_comp_subst[symmetric]) done
    also have "... = S (((CAi'' ! i) \<cdot> (\<rho>s ! i))) \<cdot> (\<rho>s_inv ! i) \<cdot> \<eta>s'' ! i"
      using inv_ren_ren
      (* since (\<rho>s_inv ! i) is a renaming. *) 
      using selection_renaming_invariant
      using \<rho>s_ren unfolding \<rho>s_inv_def
      by (simp add: a n(5)) 
    also have "... = S (CAi' ! i) \<cdot> \<eta>s' ! i"
      unfolding CAi'_def \<eta>s'_def
      using n a by auto
    finally show "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>s' ! i" by auto
  qed
    
  have dai'_dai: "DAi' \<cdot> \<eta>' = DAi"
    using DAi'_def \<eta>'_def \<open>DAi'' \<cdot> \<eta>'' = DAi\<close> subst_cls_id_subst
    by (metis \<rho>_inv_p \<rho>_ren inv_ren_cancel_r subst_cls_comp_subst) 
    
  have sel_dai'_dai: "S_M S M DAi = S DAi' \<cdot> \<eta>'"
  proof -
    have "S_M S M DAi = S DAi'' \<cdot> \<eta>''"
      by (simp add: COOL2) 
    also have "... = S (((DAi'') \<cdot> (\<rho>)) \<cdot> (\<rho>_inv)) \<cdot> \<eta>''"
       using \<rho>_inv_p
       by (metis \<rho>_ren inv_ren_cancel_r subst_cls_comp_subst subst_cls_id_subst)
        
    also have "... = S (((DAi'') \<cdot> (\<rho>))) \<cdot> (\<rho>_inv) \<cdot> \<eta>''"
      using inv_ren_ren
      (* since (\<rho>s_inv ! i) is a renaming. *) 
      using selection_renaming_invariant
      using \<rho>_ren using \<rho>_inv_p
      by auto
       
    also have "... = S DAi' \<cdot> \<eta>'"
      unfolding DAi'_def \<eta>'_def
      by auto
    finally show "S_M S M (DAi) = S (DAi') \<cdot> \<eta>'" by auto
   qed
    
    
  (* Now I just need to replace the (\<eta>s' ! i) and (\<rho>') with a single substitution... *)
  have vv: "var_disjoint ((DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'')"
    using \<rho>s''_p by blast
  {
    (* Old track of replacing. Did not work for the selections.  *)
    then have "\<forall>\<sigma>s. length \<sigma>s = length ((DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'') \<longrightarrow>
       (\<exists>\<tau>. (DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'' \<cdot>\<cdot>cl \<sigma>s = (DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'' \<cdot>cl \<tau>)"
      unfolding var_disjoint_def by auto
    then have "\<exists>\<eta>. (DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'' \<cdot>\<cdot>cl (\<eta>' # \<eta>s') = (DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'' \<cdot>cl \<eta>"
      using n by auto
    then have "\<exists>\<eta>. (DAi' # CAi') \<cdot>\<cdot>cl (\<eta>' # \<eta>s') = (DAi' # CAi') \<cdot>cl \<eta>"
      unfolding DAi'_def CAi'_def \<rho>s_def \<rho>_def
      using n
      by (metis length_greater_0_conv list.exhaust_sel subst_cls_lists_Cons zero_less_Suc)
    then have "\<exists>\<eta>. DAi' \<cdot> \<eta>' = DAi' \<cdot> \<eta> \<and> CAi' \<cdot>\<cdot>cl \<eta>s' = CAi' \<cdot>cl \<eta>"
      by auto
    then obtain \<eta> where \<eta>_p: "DAi' \<cdot> \<eta>' = DAi' \<cdot> \<eta> \<and> CAi' \<cdot>\<cdot>cl \<eta>s' = CAi' \<cdot>cl \<eta>"
      by auto
    then have "\<forall>i < n. (CAi' \<cdot>\<cdot>cl \<eta>s') ! i = (CAi' \<cdot>cl \<eta>) ! i "
      by auto
    then have "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = (CAi'! i) \<cdot> \<eta>"
      using n by auto
    then have "True" by simp
  }
  
  (* New track of replacing *)
  from vv have "var_disjoint_2 ((DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'')"
    using var_var2 by auto
  then obtain \<eta> where "(\<forall>i<Suc n. \<forall>S. S \<subseteq># ((DAi'' # CAi'') \<cdot>\<cdot>cl \<rho>s'') ! i \<longrightarrow> S \<cdot> (\<eta>' # \<eta>s') ! i = S \<cdot> \<eta>)" unfolding var_disjoint_2_def
    using n by force
  then have \<eta>_p: "(\<forall>i<Suc n. \<forall>S. S \<subseteq># ((DAi'' \<cdot> \<rho>) # (CAi'' \<cdot>\<cdot>cl \<rho>s)) ! i \<longrightarrow> S \<cdot> (\<eta>' # \<eta>s') ! i = S \<cdot> \<eta>)" unfolding var_disjoint_2_def
    by (metis \<rho>_def \<rho>s_def gr_implies_not0 list.exhaust_sel list.size(3) n(4) subst_cls_lists_Cons)
  then have "\<forall>S. S \<subseteq># (DAi'' \<cdot> \<rho>) \<longrightarrow> S \<cdot> \<eta>' = S \<cdot> \<eta>" 
    by auto
  then have s_dai'_\<eta>: "\<forall>S. S \<subseteq># DAi' \<longrightarrow> S \<cdot> \<eta>' = S \<cdot> \<eta>" 
    unfolding DAi'_def by auto
  then have dai'_\<eta>: "DAi' \<cdot> \<eta>' = DAi' \<cdot> \<eta>" by auto
      
  from \<eta>_p have "(\<forall>i<n. \<forall>S. S \<subseteq># (CAi'' \<cdot>\<cdot>cl \<rho>s) ! i \<longrightarrow> S \<cdot> \<eta>s' ! i = S \<cdot> \<eta>)" 
    by auto
  then have s_cai'_\<eta>: "(\<forall>i<n. \<forall>S. S \<subseteq># CAi' ! i \<longrightarrow> S \<cdot> \<eta>s' ! i = S \<cdot> \<eta>)" 
    unfolding CAi'_def by auto
  then have cai'_\<eta>: "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = (CAi'! i) \<cdot> \<eta>"
    by auto
      
  
      
  have "DAi = DAi' \<cdot> \<eta>" using dai'_dai dai'_\<eta> by auto
  have "S_M S M DAi = S (DAi') \<cdot> \<eta>"
  proof -
    have "S_M S M DAi = S (DAi'' \<cdot> \<rho>) \<cdot> \<rho>_inv \<cdot> \<eta>''"
      using sel_dai'_dai unfolding DAi'_def \<eta>'_def by auto
    also have "... = S (DAi'' \<cdot> \<rho>) \<cdot> \<eta>"
      using s_dai'_\<eta> unfolding DAi'_def \<eta>'_def
      by (simp add: S.S_selects_subseteq)
    also have "... = S (DAi') \<cdot> \<eta>"
      unfolding DAi'_def by auto
    finally show ?thesis by auto
  qed
    
  have "CAi = CAi' \<cdot>cl \<eta>"
  proof -
    {
      fix i
      assume "i<n"
      then have "CAi ! i = (CAi' \<cdot>cl \<eta>) ! i" using n cai'_cai2 cai'_\<eta> by auto
    }
    then show ?thesis using n by auto
  qed
  have "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>"
  proof (rule, rule)
    fix i
    assume "i < n"
    then have "S_M S M (CAi ! i) = S (CAi'' ! i \<cdot> \<rho>s ! i) \<cdot> (\<rho>s_inv ! i) \<cdot> \<eta>s'' ! i"
      using sel_cai'_cai unfolding CAi'_def \<eta>s'_def
      using n by simp
    also have "... = S (CAi'' ! i \<cdot> \<rho>s ! i) \<cdot> \<eta>"
      using s_cai'_\<eta> unfolding CAi'_def \<eta>s'_def
       S.S_selects_subseteq
      by (metis \<open>i < n\<close> calculation empty_subst ord_resolve(13)) (* There must be a better, more local proof *)
    also have "... = S (CAi' ! i) \<cdot> \<eta>"
      unfolding CAi'_def
      by (simp add: \<open>i < n\<close> n) 
    finally show "S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>"
      by auto
  qed
      
  have prime_clauses_1: "length CAi' = n"
    using n by auto
  have prime_clauses_2: "\<forall>i < n. CAi' ! i \<in> M"
    using n
    using \<open>\<forall>i<n. CAi' ! i \<in> M\<close> by blast 
  have prime_clauses_3: "CAi' \<cdot>cl \<eta> = CAi"
    using \<open>CAi = CAi' \<cdot>cl \<eta> \<close> by auto
  have prime_clauses_4: "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>"
    using \<open>\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>\<close> by auto
  have prime_clauses_5: "DAi' \<in> M"
    using DAi'_def M_renaming_invariant \<open>DAi'' \<in> M\<close> \<rho>_ren by blast
    
  have prime_clauses_6: "DAi = DAi' \<cdot> \<eta>"
    using \<open>DAi = DAi' \<cdot> \<eta>\<close> by auto
  have prime_clauses_7: "S_M S M (DAi) = S (DAi') \<cdot> \<eta>"
    using \<open>S_M S M (DAi) = S (DAi') \<cdot> \<eta>\<close> by auto
    
  have prime_clauses_8: "var_disjoint (DAi'#CAi')"
    using CAi'_def DAi'_def \<open>var_disjoint ((DAi'' # CAi'') \<cdot>\<cdot>cl (\<rho> # \<rho>s))\<close> by auto
    
  have prime_clauses_9: "{DAi'} \<union> set CAi' \<subseteq> M"
    apply auto
    apply (auto simp add: \<open>DAi' \<in> M\<close>)
    using n \<open>\<forall>i<n. CAi' ! i \<in> M\<close>
    by (metis in_set_conv_nth) 
    
  have prime_clauses_10: "is_ground_subst \<eta>" sorry
      
  note prime_clauses = prime_clauses_1 prime_clauses_2 prime_clauses_3 prime_clauses_4
    prime_clauses_5 prime_clauses_6 prime_clauses_7 prime_clauses_8 prime_clauses_9 prime_clauses_10 

  (* Now I need to find all these Ci' Aij' D' Ai' *)

  from ord_resolve(11) have "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> (negs (mset Ai')) \<subseteq># DAi' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DAi')"
    unfolding eligible_simp
    proof
      assume a: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
      then have "length Ai = 1" by auto
      then have "mset Ai = {# Ai ! 0 #}" by auto
      then have "negs (mset Ai) = {# Neg (Ai ! 0) #}"
        by (simp add: \<open>mset Ai = {#Ai ! 0#}\<close>)
      then have "DAi = D + {#Neg (Ai ! 0)#}" using ord_resolve(1) by auto
      then obtain L where "L \<in># DAi' \<and> L \<cdot>l \<eta> = Neg (Ai ! 0)" using prime_clauses(6)
        by (metis Melem_subst_cls mset_subset_eq_add_right single_subset_iff)
      then have "Neg (atm_of L) \<in># DAi' \<and> Neg (atm_of L) \<cdot>l \<eta> = Neg (Ai ! 0) "
        by (metis Neg_atm_of_iff literal.sel(2) subst_lit_is_pos)
      then have "[atm_of L] \<cdot>al \<eta> = Ai \<and> negs (mset [atm_of L]) \<subseteq># DAi'"
        using \<open>mset Ai = {#Ai ! 0#}\<close> subst_lit_def by auto
      then show "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> negs (mset Ai') \<subseteq># DAi' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DAi')" using a by blast
    next
      assume "S_M S M (D + negs (mset Ai)) = negs (mset Ai)" 
      then have "negs (mset Ai) = S DAi' \<cdot> \<eta>" using prime_clauses(7) ord_resolve(1) by auto
      then have "\<exists>Ai'. negs (mset Ai') = S DAi' \<and> Ai' \<cdot>al \<eta> = Ai"
        using very_specific_lemma[of Ai "S DAi'" \<eta>] using S.S_selects_neg_lits by auto
      then show "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> negs (mset Ai') \<subseteq># DAi'  \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DAi')" using S.S_selects_subseteq by auto
  qed
  then obtain Ai' where Ai'_p: "Ai' \<cdot>al \<eta> = Ai \<and> (negs (mset Ai')) \<subseteq># DAi' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DAi')" by blast
  then have "length Ai' = n"
    using local.ord_resolve(6) by auto
  note n = n \<open>length Ai' = n\<close>
    
  have useful: "negs (mset Ai') \<cdot> \<eta> = negs (mset Ai)"
    using Ai'_p 
      using atomlist_to_negs_equality by auto
      
  define D' where "D' = DAi' - (negs (mset Ai'))"
  then have "DAi' = D' +  (negs (mset Ai'))" using Ai'_p by auto
    
  then have "D' \<cdot> \<eta> = D" using \<open>DAi = DAi' \<cdot> \<eta>\<close> ord_resolve(1) useful
    by auto
      
  have "\<forall>i<n. \<exists>Aiji'. Aiji' \<cdot>am \<eta> = Aij ! i \<and> (poss (Aiji')) \<subseteq># CAi' ! i"
  proof (rule, rule)
    fix i
    assume "i<n"
    have "CAi' ! i \<cdot> \<eta> = CAi ! i"
      using \<open>i < n\<close> cai'_\<eta> cai'_cai2 by auto
    moreover
    have "poss (Aij ! i) \<subseteq># CAi !i"
      using \<open>i<n\<close> ord_resolve(8) by auto
    ultimately
    have "\<exists>NAiji'.  NAiji' \<cdot> \<eta> = poss (Aij ! i) \<and> NAiji' \<subseteq># CAi' ! i"
      using obviously unfolding subst_cls_def by auto
    then obtain NAiji' where nn: "NAiji' \<cdot> \<eta> = poss (Aij ! i) \<and> NAiji' \<subseteq># CAi' ! i"
      by auto
    have l: "\<forall>L \<in># NAiji'. is_pos L"
    proof
      fix L
      assume LL: "L \<in># NAiji'"
      have asdfasdf: "\<forall>L' \<in># poss (Aij ! i). is_pos L'"
        by auto
      then have "\<exists>L' \<in># poss (Aij ! i). L  \<cdot>l \<eta> = L'"
        using nn LL
        by (metis Melem_subst_cls) 
      then have "\<exists>L'. is_pos L' \<and> L  \<cdot>l \<eta> = L'"
        using asdfasdf by metis
      then show "is_pos L"
        by auto
    qed
    define Aiji' where "Aiji' = image_mset atm_of NAiji'"
    have na: "poss Aiji' = NAiji'"
      using l unfolding Aiji'_def by auto
    then have "Aiji' \<cdot>am \<eta> = Aij ! i" using nn
      by (metis literal.inject(1) multiset.inj_map_strong subst_cls_poss)
    moreover
    have "poss Aiji' \<subseteq># CAi' ! i"
      using na nn by auto
    ultimately
    show "\<exists>Aiji'. Aiji' \<cdot>am \<eta> = Aij ! i \<and> poss Aiji' \<subseteq># CAi' ! i" 
      by blast 
  qed

  then obtain Aij'f where Aij'f_p: "\<forall>i<n. Aij'f i \<cdot>am \<eta> = Aij ! i \<and> (poss (Aij'f i)) \<subseteq># CAi' ! i"
    by metis
  define Aij' where "Aij' = map Aij'f [0 ..<n]"
    
  then have "length Aij' = n" by auto
    note n = n \<open>length Aij' = n\<close>
    
  from Aij'_def have tdddd: "\<forall>i<n. Aij' ! i \<cdot>am \<eta> = Aij ! i \<and> (poss (Aij' ! i)) \<subseteq># CAi' ! i"
    using Aij'f_p by auto
  then have "\<forall>i<n. Aij' ! i \<cdot>am \<eta> = Aij ! i"
    by auto
  then have "\<forall>i<n. (Aij' \<cdot>aml  \<eta>) ! i = Aij ! i"
    by (simp add: n swapii)
  then have "Aij' \<cdot>aml \<eta> = Aij"
    using n(10) n(13) unfolding subst_atm_mset_list_def by auto (* unfolding should not be necessary *)
    
      
  have pay11: "\<forall>i<n. (poss (Aij' ! i)) \<subseteq># CAi' ! i"
    using tdddd by auto
 
  
    
  define Ci' where "Ci' = map2 (op -) CAi' (map poss Aij')"
    
  have "length Ci' = n"
    using Ci'_def n by auto
  note n = n \<open>length Ci' = n\<close>
    
  have rtsts: "\<forall>i<n. Ci' ! i =  CAi' ! i - (poss (Aij' ! i))"
    using Ci'_def n by auto
    
  have "\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)"
  proof (rule, rule)
    fix i 
    assume "i < n"
    then show "CAi' ! i = Ci' ! i + poss (Aij' ! i)"
      using rtsts pay11 by auto
  qed
    
  have "Ci' \<cdot>cl \<eta> = Ci"
  proof -
    thm \<open>Aij' \<cdot>aml \<eta> = Aij\<close> Ci'_def prime_clauses(3) ord_resolve(8)
    {
      fix i 
      assume a: "i<n"
      have "(poss ((Aij' !i) )) \<cdot> \<eta> = poss (Aij ! i)"
        by (simp add: \<open>\<forall>i<n. Aij' ! i \<cdot>am \<eta> = Aij ! i\<close> a)
      moreover
      have "CAi ! i = Ci ! i + poss (Aij ! i)"
        using ord_resolve(8) a by auto
      moreover
      have "CAi' ! i = Ci' ! i + poss (Aij' ! i)"
        using \<open>\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)\<close>
          using a by auto
      ultimately
      have "(Ci' ! i) \<cdot> \<eta> = Ci ! i"
        using a cai'_\<eta> cai'_cai2 by auto
      then have "(Ci' \<cdot>cl \<eta>) ! i = Ci ! i"
        using a n by auto
    }
    then show ?thesis using n by auto
  qed
      
  have prime_clauses2:
    "length Ci' = n"
    "length Aij' = n"
    "length Ai' = n"
    "Ci' \<cdot>cl \<eta> = Ci"
    "Aij' \<cdot>aml \<eta> = Aij"
    "D' \<cdot> \<eta> = D"
    "Ai' \<cdot>al \<eta> = Ai"
    "DAi' = D' +  (negs (mset Ai'))"
    "\<forall>i<n. CAi' ! i = Ci' ! i + poss (Aij' ! i)"
    "True"
             apply auto
    using n apply simp
    using n apply simp
    using n apply simp
    using \<open>Ci' \<cdot>cl \<eta> = Ci\<close> apply simp
    using \<open>Aij' \<cdot>aml \<eta> = Aij\<close> apply simp
    using \<open>D' \<cdot> \<eta> = D\<close> apply simp
    using Ai'_p apply simp
    using \<open>DAi' = D' + negs (mset Ai')\<close> apply simp
    using \<open>\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)\<close> apply simp
    done
        
      
      
      
  have "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
  hence uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)))" using mgu_sound is_mgu_def unfolding prime_clauses2(5) prime_clauses2(7) by auto
  have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset Ai' Aij'))"
  proof -
    have eq: "(set_mset ` set (map2 add_mset Ai' Aij' \<cdot>aml \<eta>)) = (set_mset ` set (map2 add_mset Ai' Aij') \<cdot>ass \<eta>)"
      unfolding subst_atmss_def
        subst_atm_mset_list_def
      using subst_atm_mset_def subst_atms_def by auto
    have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)))" using uu by -
    then have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset Ai' Aij') \<cdot>aml \<eta>))" using prime_clauses2(2) prime_clauses2(3) map2_add_mset_map by auto
    then have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset Ai' Aij')) \<cdot>ass \<eta>)" using eq by auto
    then show ?thesis 
      using is_unifiers_comp by auto
  qed
  then obtain \<tau> where \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset Ai' Aij'))" using mgu_complete
    by (metis (mono_tags, hide_lams) finite_imageI finite_set_mset image_iff set_mset_mset) (* should be simpler? *) 
  then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
    by (metis (mono_tags, hide_lams) List.finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff mgu_sound set_mset_mset substitution_ops.is_mgu_def that) (* should be simpler *)
      
  define E' where "E' = ((\<Union># (mset Ci')) + D') \<cdot> \<tau>"
    
  have "E' \<cdot> \<phi> = ((\<Union># (mset Ci')) + D') \<cdot> (\<tau> \<odot> \<phi>)" unfolding E'_def by auto
  also have "... = ((\<Union># (mset Ci')) + D') \<cdot> (\<eta> \<odot> \<sigma>)" using \<phi>_p by auto
  also have "... = ((\<Union># (mset (Ci' \<cdot>cl \<eta>))) + (D' \<cdot> \<eta>)) \<cdot> \<sigma>" by simp
  also have "... = ((\<Union># (mset Ci)) + D) \<cdot> \<sigma>" using prime_clauses2(4) prime_clauses2(6) by auto
  also have "... = E" using ord_resolve by auto
  finally have e'\<phi>e: "E' \<cdot> \<phi> = E" .
      
  have a: "(D' + negs (mset Ai')) = DAi'" using prime_clauses2(8) by auto
  moreover
  have b: "\<forall>i<n. CAi' ! i = Ci' ! i + poss (Aij' ! i)" using prime_clauses2(9) by auto
  moreover
  have c: "\<forall>i<n. Aij' ! i \<noteq> {#}"
    apply (rule allI)
    apply rule
    using prime_clauses2(2) ord_resolve(9) ord_resolve(5) unfolding prime_clauses2(5)[symmetric]
    using empty_subst_for_atoms using swapii by metis
  moreover
    (* Lifting  *)
  have "eligible (S_M S M) \<sigma> Ai (D + negs (mset Ai))" using ord_resolve unfolding eligible_simp by -
  hence "S_M S M (D + negs (mset Ai)) = negs (mset Ai) \<or>
    S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" 
    unfolding eligible_simp by -
  hence "eligible S \<tau> Ai' (D' + negs (mset Ai'))"
  proof
    assume as: "S_M S M (D + negs (mset Ai)) = negs (mset Ai)"
    then have "S_M S M (D + negs (mset Ai)) \<noteq> {#}"
      using n ord_resolve(7) by force
    then have "negs (mset Ai') = S DAi'" using Ai'_p by auto
    hence "S (D'  + negs (mset Ai')) = negs (mset Ai')" using a by auto
    thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible_simp by auto
  next
    assume asm: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
    let ?A = "Ai ! 0"
    from asm have "S_M S M (D + negs (mset Ai)) = {#}" by auto
    hence "S (D' + negs (mset Ai')) = {#}" using prime_clauses2(6)[symmetric] prime_clauses2(7)[symmetric] prime_clauses(7)
      using ord_resolve(1) 
      apply auto
      using a empty_subst by blast   
    moreover
    from asm have l: "length Ai = 1" by auto
    hence l': "length Ai' = 1" using prime_clauses2(7)[symmetric] by auto
    moreover
    from asm have "maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" by auto
    hence "maximal_in (Ai' ! 0 \<cdot>a (\<eta> \<odot> \<sigma>)) ((D' + negs (mset Ai')) \<cdot> (\<eta> \<odot> \<sigma>))" unfolding prime_clauses2(7)[symmetric] prime_clauses2(6)[symmetric]
      using l' by auto  
    hence "maximal_in (Ai' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D' + negs (mset Ai')) \<cdot> (\<tau> \<odot> \<phi>))" unfolding prime_clauses2(7)[symmetric] prime_clauses2(6)[symmetric]
      using \<phi>_p by auto
    hence "maximal_in (Ai' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D' + negs (mset Ai')) \<cdot> \<tau> \<cdot> \<phi>)" 
      by auto
    hence "maximal_in (Ai' ! 0 \<cdot>a \<tau>) ((D' + negs (mset Ai')) \<cdot> \<tau>)" using maximal_in_gen by blast
    ultimately show "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible_simp by auto 
  qed
  moreover
  from ord_resolve have "\<forall>i<n. str_maximal_in (Ai ! i \<cdot>a \<sigma>) (Ci ! i \<cdot> \<sigma>)" by -
  hence "\<forall>i<n. str_maximal_in ((Ai' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Ci' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)" using prime_clauses2 by simp
  hence "\<forall>i<n. str_maximal_in ((Ai' ! i) \<cdot>a (\<eta> \<odot> \<sigma>)) ((Ci' ! i) \<cdot> (\<eta> \<odot> \<sigma>))" using prime_clauses2 by auto
  hence "\<forall>i<n. str_maximal_in ((Ai' ! i) \<cdot>a (\<tau> \<odot> \<phi>)) ((Ci' ! i) \<cdot> (\<tau> \<odot> \<phi>))" using \<phi>_p by auto
  hence "\<forall>i<n. str_maximal_in ((Ai' ! i \<cdot>a \<tau>) \<cdot>a \<phi>) ((Ci' ! i \<cdot> \<tau>) \<cdot> \<phi>)" by auto
  hence e: "\<forall>i<n. str_maximal_in (Ai' ! i \<cdot>a \<tau>) (Ci' ! i \<cdot> \<tau>)" using str_maximal_in_gen \<phi>_p by blast
  moreover
  from ord_resolve have "\<forall>i < n. (S_M S M) (CAi ! i) = {#}" by -
  hence "\<forall>i < n. S (CAi' ! i)  \<cdot> \<eta> = {#}" using prime_clauses(3) prime_clauses(4) ord_resolve(3) by auto 
  hence ff: "\<forall>i < n. S (CAi' ! i) = {#}" using empty_subst by blast
  ultimately
  have res_e': "ord_resolve S CAi' DAi' E'" 
    using ord_resolve.intros[of CAi' n Ci' Aij' Ai' \<tau> S D', OF prime_clauses(1) prime_clauses2(1) prime_clauses2(2) prime_clauses2(3) ord_resolve(7) b c \<tau>_p] \<tau>_p 
    unfolding E'_def by auto
      
  have "is_ground_cls_list CAi" "is_ground_cls DAi"
    using prime_clauses(3) prime_clauses(6) prime_clauses(10) by auto 
  hence "is_ground_cls E" using resolve ground_resolvent_ground by auto
  then obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E" using e'\<phi>e mk_ground_subst by blast
      
  have instsC: "CAi = CAi' \<cdot>cl \<eta>" using prime_clauses(3) by auto
  have instsD: "DAi = DAi' \<cdot> \<eta>"  using prime_clauses(6) by auto
  have instsE: "E = E' \<cdot> \<eta>2" using ground_\<eta>2 by auto
      
      
  hence inM: "{DAi'} \<union> set CAi' \<subseteq> M" using prime_clauses(9) by auto
      
  from res_e' instsC instsD instsE inM e'\<phi>e prime_clauses(10) ground_\<eta>2 show ?thesis
    using that[of \<eta> \<eta>2 CAi' DAi' E'] by blast
qed
  
  
end

(* lifting lemma:
I think a better tactic is to use ord_resolve in the conclusion
and then I can probably remove the renaming assumption on M
*)

  

end