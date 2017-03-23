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
      by (auto simp add: map2_nth[symmetric]) 
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

lemma rename_sound:
  assumes "is_renaming \<rho>"
  assumes "I \<Turnstile>fo C"
  shows "I \<Turnstile>fo (C \<cdot> \<rho>)"
using assms
  by (metis is_ground_comp_subst subst_cls_comp_subst true_fo_cls true_fo_cls_inst)

lemma rename_sound_scl:
  assumes len: "length P = length CAi"
  assumes ren: "\<forall>\<rho> \<in> set P. is_renaming \<rho>"
  assumes true_cas: "I \<Turnstile>fom mset CAi"
  shows "I \<Turnstile>fom mset (CAi \<cdot>\<cdot>cl P)"
proof -
  from true_cas have "\<forall>C. C\<in># mset CAi \<longrightarrow> (I \<Turnstile>fo C)" 
    using true_fo_cls_mset_def2 by auto
  then have "\<forall>C. C \<in> set CAi \<longrightarrow> (I \<Turnstile>fo C)" unfolding side_clauses_def by auto
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i))"
    using in_set_conv_nth[of _ CAi] by blast
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i) \<cdot> P ! i)"
    using ren rename_sound len by auto
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
    then show "I \<Turnstile>fo x" using true_cp unfolding subst_cls_lists_def by auto
  qed
qed
  

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAi DAi E" and
    cc_d_true: "I \<Turnstile>fom (mset CAi) + {#DAi#}"
  shows "I \<Turnstile>fo E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  have ren: "is_renaming \<rho>" using ord_resolve_rename by -
  have rens: "Ball (set P) is_renaming" using ord_resolve_rename by -
  have len: "length P = length CAi" using ord_resolve_rename by -
  have res: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DAi \<cdot> \<rho>) E" using ord_resolve_rename by -
  have "I \<Turnstile>fom (mset (CAi \<cdot>\<cdot>cl P)) + {#DAi \<cdot> \<rho>#}"
    using rename_sound_scl[OF len rens , of I] rename_sound[OF ren, of I DAi]
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
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>'))" unfolding less_atm_iff by -
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>'))" sorry
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>'))"
    using is_ground_comp_subst by fastforce
  hence "\<forall>B\<in>atms_of C. \<not> (less_atm A B)" unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def maximal_in_def by auto
qed
    
lemma str_maximal_in_gen: (* a better proof might reuse the lemma maximal_in_gen *)
  assumes "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "str_maximal_in A C"
proof -
  from assms have "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)" by -
  hence "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_eq_atm (A \<cdot>a \<sigma>) B" by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> (less_atm (A \<cdot>a \<sigma>) B \<or> A \<cdot>a \<sigma> = B)" unfolding less_eq_atm_def by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B)" unfolding less_atm_iff by -
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)" sorry
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
    
lemma ground_resolvent_subset:
  assumes gr_c: "is_ground_cls_list CAi"
  assumes gr_d: "is_ground_cls DAi"
  assumes resolve: "ord_resolve SSS CAi DAi E"
  shows "E \<subseteq># (\<Union>#(mset CAi)) + DAi"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
    
  have cisucai: "\<Union>#mset Ci \<subseteq># \<Union>#(mset CAi)" sorry
  hence gr_ci: "is_ground_cls_list Ci" sorry
  have dsudai :"D \<subseteq># DAi" by (simp add: local.ord_resolve(1)) 
  then have gr_di: "is_ground_cls D" sorry    
      
  from ord_resolve have "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by -
  hence "E = (\<Union>#mset Ci + D)" using gr_ci gr_di sorry
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
  
lemma empty_subst: "C \<cdot> \<eta> = {#} \<Longrightarrow> C = {#}"
unfolding subst_cls_def by auto
  
(*
lemma uw: "\<forall>C\<sigma>. C\<sigma> \<in> grounding_of_clss M \<longrightarrow> (\<exists>D \<sigma>. D \<in> M \<and> C\<sigma> = D \<cdot> \<sigma> \<and> (\<forall>x. S_M S M D = x \<longrightarrow> S C\<sigma> = x \<cdot> \<sigma>))"
  sorry
*)  
  
lemma uw2: "\<forall>C\<sigma>. C\<sigma> \<in> grounding_of_clss M \<longrightarrow> (\<exists>D \<sigma>. D \<in> M \<and> C\<sigma> = D \<cdot> \<sigma> \<and> (S D) \<cdot> \<sigma> = (S_M S M C\<sigma>))"
  sorry

(* A lemma that states that a list of clauses can be standardized apart. *)
 thm make_var_disjoint
    
lemma ord_resolve_lifting: 
  fixes CAi
  assumes resolve: "ord_resolve (S_M S M) CAi DAi E" (* UHM (S_M S M) is FO, while S is GROUND. SO ITS BACKWARDS.. *)
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
    
  interpret S: selection S by (rule select)
      
      (* 2. Choose the D' and the C' *)
      
      have uuu: "\<forall>CA \<in> set CAi. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> (CA) = CA'' \<cdot> \<eta>c'' \<and> S (CA'') \<cdot> \<eta>c'' = S_M S M CA "
        using grounding uw2 by auto
        
      hence "\<forall>i < n. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> (CAi ! i) = CA'' \<cdot> \<eta>c'' \<and> S CA'' \<cdot> \<eta>c'' = S_M S M ( (CAi ! i)) "
        using ord_resolve(3) by auto
          
      then have "\<exists>\<eta>s''f CAi''f. \<forall>i < n. CAi''f i \<in> M \<and> (CAi ! i) = (CAi''f i) \<cdot> (\<eta>s''f i) \<and> S (CAi''f i) \<cdot> (\<eta>s''f i) = S_M S M (CAi ! i)"
        by metis
          
      then obtain \<eta>s''f CAi''f where f_p: "\<forall>i < n. CAi''f i \<in> M \<and> (CAi ! i) = (CAi''f i) \<cdot> (\<eta>s''f i) \<and> S (CAi''f i)  \<cdot> (\<eta>s''f i) = S_M S M  (CAi ! i)"
        by auto
          
      define \<eta>s'' where "\<eta>s'' = map \<eta>s''f [0 ..<n]"
      define CAi'' where "CAi'' = map CAi''f [0 ..<n]"
        
      have \<eta>s''_ff: "\<forall>i < n. \<eta>s'' ! i = \<eta>s''f i"
        unfolding \<eta>s''_def apply (induction n) apply auto
        by (metis add.left_neutral diff_is_0_eq diff_zero length_map length_upt less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_map_upt)
          
      have CAi''_ff: "\<forall>i < n. CAi'' ! i = CAi''f i"
        unfolding CAi''_def apply (induction n) apply auto
        by (metis add.left_neutral diff_is_0_eq diff_zero length_map length_upt less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_map_upt)
        
      have COOL: "\<forall>i < n. CAi'' ! i \<in> M \<and> (CAi ! i) = (CAi'' ! i) \<cdot> (\<eta>s'' ! i) \<and> S (CAi'' ! i) \<cdot> (\<eta>s'' ! i) = S_M S M (CAi ! i)"
        using f_p \<eta>s''_ff CAi''_ff by auto
      
  have "length CAi'' = n" unfolding CAi''_def by auto
  have "length \<eta>s'' = n" unfolding \<eta>s''_def by auto
  have "\<forall>i < n. CAi'' ! i \<in> M" using COOL by auto
  have "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" using COOL
    by (simp add: \<open>length CAi'' = n\<close> \<open>length \<eta>s'' = n\<close> local.ord_resolve(3)) 
  have "(\<forall>i < n. S_M S M (CAi ! i) = S (CAi'' ! i) \<cdot> (\<eta>s'' ! i))"
    using COOL by auto
      
     
    
      
(*    "DAi'' \<in> M" 
    "DAi'' \<cdot> \<eta>d'' = DAi"
    "\<And>x. S_M S M DAi = x \<cdot> \<eta>d'' \<Longrightarrow> S DAi'' = x"*)
    using uw uw2 grounding
      sorry
      
  obtain CAi' DAi' \<eta> where prime_clauses: (* I need some lemma telling that these standardized apart clauses exist *) 
    "length CAi' = n" 
    "\<forall>i < n. CAi' ! i \<in> M" 
    "CAi' \<cdot>cl \<eta> = CAi"
    "\<forall>i < n. S_M S M (CAi ! i) = S (CAi' ! i) \<cdot> \<eta>" 
      (* should this even be here? Probably not, but I'm not sure. I think it could instead look more like the weaker invariant hinted at in the assumptions of this lemma *)
      (* Meh, I'm not even sure about that. I think maybe we need the strong assumption, but this should be more like the below one for DAi and DAi' *)
    
    "DAi' \<in> M" 
    "DAi = DAi' \<cdot> \<eta>" 
    "\<And>x. S_M S M DAi = x \<cdot> \<eta> \<Longrightarrow> S DAi' = x" (* I think now that this is the (or at least one) correct way to formalize S_M, kind of at least *)
    
    "var_disjoint (DAi'#CAi')"
    "{DAi'} \<union> set CAi' \<subseteq> M"
    
    "is_ground_subst \<eta>"
    sorry

  obtain Ci' Aij' D' Ai' where prime_clauses2:
    "length Ci' = n"
    "length Aij' = n"
    "length Ai' = n"
    "Ci' \<cdot>cl \<eta> = Ci"
    "Aij' \<cdot>aml \<eta> = Aij"
    "D' \<cdot> \<eta> = D"
    "Ai' \<cdot>al \<eta> = Ai"
    sorry
    
  have "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
  hence "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)))" using mgu_sound is_mgu_def unfolding prime_clauses2 by auto
  hence \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset Ai' Aij'))" sorry (* I guess it makes sense *)
  then obtain \<tau> where \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset Ai' Aij'))" using mgu_complete
    by (metis (mono_tags, hide_lams) finite_imageI finite_set_mset image_iff set_mset_mset) (* should be simpler? *) 
  then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
    by (metis (mono_tags, hide_lams) List.finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff mgu_sound set_mset_mset substitution_ops.is_mgu_def that) (* should be simpler *)
      
  define E' where "E' = ((\<Union># (mset Ci')) + D') \<cdot> \<tau>"
    
  have "E' \<cdot> \<phi> = ((\<Union># (mset Ci')) + D') \<cdot> (\<tau> \<odot> \<phi>)" unfolding E'_def by auto
  also have "... = ((\<Union># (mset Ci')) + D') \<cdot> (\<eta> \<odot> \<sigma>)" using \<phi>_p by auto
  also have "... = ((\<Union># (mset (Ci' \<cdot>cl \<eta>))) + (D' \<cdot> \<eta>)) \<cdot> \<sigma>" by simp
  also have "... = ((\<Union># (mset Ci)) + D) \<cdot> \<sigma>" using prime_clauses2 by auto
  also have "... = E" using ord_resolve by auto
  finally have e'\<phi>e: "E' \<cdot> \<phi> = E" .
  
  have a: "(D' + negs (mset Ai')) = DAi'" sorry (* Believable *)
  moreover
  have b: "\<forall>i<n. CAi' ! i = Ci' ! i + poss (Aij' ! i)" sorry (* Believable *)
  moreover
  have c: "\<forall>i<n. Aij' ! i \<noteq> {#}" sorry (* Believable *)
  moreover
  (* Lifting  *)
  have "eligible (S_M S M) \<sigma> Ai (D + negs (mset Ai))" using ord_resolve unfolding eligible_simp by -
  hence "S_M S M (D + negs (mset Ai)) = negs (mset Ai) \<or>
    S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" 
      unfolding eligible_simp by -
  hence "eligible S \<tau> Ai' (D' + negs (mset Ai'))"
  proof
    assume "S_M S M (D + negs (mset Ai)) = negs (mset Ai)"
    hence "S_M S M (D' \<cdot> \<eta> + negs (mset (Ai' \<cdot>al \<eta>))) = negs (mset (Ai' \<cdot>al \<eta>))"
      using prime_clauses2(6) prime_clauses2(7) by blast 
    hence "S_M S M (D' \<cdot> \<eta> + negs (mset (Ai' \<cdot>al \<eta>))) = (negs (mset (Ai'))) \<cdot> \<eta>" sorry (* believable *)
    hence "S_M S M (DAi) = (negs (mset (Ai'))) \<cdot> \<eta>" sorry (* believable *)
    hence "S (D'  + negs (mset Ai')) = negs (mset Ai')"
      using prime_clauses(7)[of ] unfolding a[symmetric] ord_resolve(1) prime_clauses2(6)[symmetric] prime_clauses2(7)[symmetric]
       by auto
    thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible_simp by auto
  next
    assume asm: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
    let ?A = "Ai ! 0"
    from asm have "S_M S M (D + negs (mset Ai)) = {#}" by auto
    hence "S (D' + negs (mset Ai')) = {#}" using prime_clauses2(6)[symmetric] prime_clauses2(7)[symmetric] prime_clauses(7)
        sorry (* believable *)
    moreover
    from asm have l: "length Ai = 1" by auto
    hence "length Ai' = 1" using prime_clauses2(7)[symmetric] by auto
    moreover
    from asm have "maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" by auto
    hence "maximal_in (Ai' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D' + negs (mset Ai')) \<cdot> \<tau> \<cdot> \<phi>)" 
      using  prime_clauses2(3) l \<phi>_p unfolding prime_clauses2(7)[symmetric] prime_clauses2(6)[symmetric] sorry (* believable *)
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
    using ord_resolve.intros[of CAi' n Ci' Aij' Ai' \<tau> S D', OF prime_clauses(1) prime_clauses2(1) prime_clauses2(2) prime_clauses2(3) ord_resolve(7) b c \<tau>_p] prime_clauses \<tau>_p 
    unfolding E'_def by auto
  
  have "is_ground_cls_list CAi" "is_ground_cls DAi"
    using prime_clauses prime_clauses by auto 
  hence "is_ground_cls E" using resolve ground_resolvent_ground by auto
  then obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E" using e'\<phi>e mk_ground_subst by blast
  
  have instsC: "CAi = CAi' \<cdot>cl \<eta>" using prime_clauses by auto
  have instsD: "DAi = DAi' \<cdot> \<eta>"  using prime_clauses by auto
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