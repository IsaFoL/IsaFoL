(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull
*)

theory New5_FO_Resolution_Prover 
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
  "subsumes C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> \<subseteq># D)"

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
   \<forall>i < n. (CAi ! i) = (Ci ! i + (poss (Aij ! i))) \<Longrightarrow> (* could be written with map *)
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

definition mk_var_dis where "mk_var_dis Cs = (SOME \<rho>s. length \<rho>s = length Cs \<and> (\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>) \<and>
       var_disjoint (Cs \<cdot>\<cdot>cl \<rho>s))"
  
lemma mk_var_dis_jaja: "length (mk_var_dis Cs) = length Cs \<and> (\<forall>\<rho> \<in> set (mk_var_dis Cs). is_renaming \<rho>) \<and>
       var_disjoint (Cs \<cdot>\<cdot>cl (mk_var_dis Cs))"
proof -
  define Q where "Q = (\<lambda>\<rho>s. length \<rho>s = length Cs \<and> (\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>) \<and>
       var_disjoint (Cs \<cdot>\<cdot>cl \<rho>s))" 
  have "mk_var_dis Cs = (SOME \<rho>s. Q \<rho>s)"
    unfolding mk_var_dis_def Q_def by auto
  moreover
  have "\<exists>\<rho>s. Q \<rho>s"
    using make_var_disjoint unfolding Q_def by metis
  ultimately
  have "Q (mk_var_dis Cs)" using someI by metis
  then show ?thesis unfolding Q_def by auto
qed  
 
inductive ord_resolve_rename :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_rename:
  "\<rho> = hd (mk_var_dis (DA#CAi)) \<Longrightarrow>
   \<rho>s = tl (mk_var_dis (DA#CAi)) \<Longrightarrow>
   ord_resolve (CAi \<cdot>\<cdot>cl \<rho>s) (DA \<cdot> \<rho>) E \<Longrightarrow>
   ord_resolve_rename CAi DA E"
  


lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_cls_list CAi" and
    gr_d: "is_ground_cls DA" and
    res_e_re: "ord_resolve_rename CAi DA E"
  shows "ord_resolve CAi DA E"
  using res_e_re proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  then have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>" using mk_var_dis_jaja
    by (metis list.sel(2) list.set_sel(2)) 
  from ord_resolve_rename have len: "length P = length CAi" using mk_var_dis_jaja by auto
  have res_e: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) E" using ord_resolve_rename by auto
  
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
  then have len: "length P = length CAi" using ord_resolve_rename mk_var_dis_jaja by auto
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

definition "gd_ord_\<Gamma> = gd.ord_\<Gamma>" (* Hack to expose *)
  
lemma gd_ord_\<Gamma>_gd_ord_\<Gamma>: "P gd_ord_\<Gamma> \<longleftrightarrow> P gd.ord_\<Gamma>" (* One more hack *)
  unfolding gd_ord_\<Gamma>_def by auto
  
  
(* A huge extension like Uwe suggested. *)
definition "gd_ord_\<Gamma>' = {Infer a b c | a b c. (\<exists>I. I \<Turnstile>m a \<and> I \<Turnstile> b) \<longrightarrow> (\<exists>I. I \<Turnstile> c)}" 

lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gd.ord_\<Gamma> \<subseteq> gd_ord_\<Gamma>'"
  unfolding gd_ord_\<Gamma>'_def
  using gd.ord_\<Gamma>_def gd.ord_resolve_sound by fastforce 

interpretation src_ext:
  redundancy_criterion "gd_ord_\<Gamma>'" "src.Rf" "(\<lambda>N. src.Ri N \<union> (gd_ord_\<Gamma>' - gd.ord_\<Gamma>))"
  by (rule standard_redundancy_criterion_extension[OF gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion])
(*find_theorems name: src_ext*)

definition "src_ext_derive \<equiv> src_ext.derive" (* Hack to expose *)
lemma src_ext_derive_src_ext_derive: "P src_ext_derive \<longleftrightarrow> P src_ext.derive" (* One more hack *)
  unfolding src_ext_derive_def by auto
    
definition "src_Rf \<equiv> src.Rf" (* Hack to expose *)
lemma src_Rf_src_Rf: "P src_Rf \<longleftrightarrow> P src.Rf" (* One more hack *)
  unfolding src_Rf_def by auto
  
  
definition "src_derive \<equiv> src.derive" (* Hack to expose src.derive such that I can later reach in to this context *)
  
lemma src_derive_src_derive: "P src_derive \<longleftrightarrow> P src.derive" (* One more hack *)
  unfolding src_derive_def by auto

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
    
lemma grounding_ground: "C \<in> grounding_of_clss M \<Longrightarrow> is_ground_cls C"
   by (smt ground_subst_ground_cls grounding_of_clss_def image_iff mem_Collect_eq mem_simps(9) substitution_ops.grounding_of_cls_def)
  (* There is also an Isar proof. *)
     
lemma eql_map_neg_lit_eql_atm:
  assumes "map (\<lambda>x. x \<cdot>l \<eta>) (map Neg Ai') = map Neg Ai"
  shows "Ai' \<cdot>al \<eta> = Ai"
  using assms 
by (induction Ai' arbitrary: Ai) auto
  
lemma instance_list:
  assumes "negs (mset Ai) = SDA' \<cdot> \<eta>"
  shows "\<exists>Ai'. negs (mset Ai') = SDA' \<and> Ai' \<cdot>al \<eta> = Ai"
proof - 
  from assms(1) have negL: "\<forall>L \<in># SDA'. is_neg L"
    by (metis image_iff literal.disc(2) set_image_mset subst_lit_is_pos substitution_ops.subst_cls_def)
    
  from assms(1) have "{#x \<cdot>l \<eta>. x \<in># SDA'#} = mset (map Neg Ai)"
    using subst_cls_def by auto
  then have "\<exists>NAi'. map (\<lambda>x. x \<cdot>l \<eta>) NAi' = map Neg Ai \<and> mset NAi' = SDA'"  
   using image_mset_of_subset_list[of "\<lambda>x. x \<cdot>l \<eta>" SDA' "map Neg Ai"]
   by auto
  then obtain Ai' where Ai'_p:
    "map (\<lambda>x. x \<cdot>l \<eta>) (map Neg Ai') = map Neg Ai \<and> mset (map Neg Ai') = SDA'"
    by (metis (no_types, lifting) Neg_atm_of_iff negL ex_map_conv set_mset_mset)
  
  have "negs (mset Ai') = SDA'" 
    using Ai'_p by auto
  moreover
  have "map (\<lambda>x. x \<cdot>l \<eta>) (map Neg Ai') = map Neg Ai"
    using Ai'_p by auto
  then have "Ai' \<cdot>al \<eta> = Ai"
    using eql_map_neg_lit_eql_atm by auto
  ultimately
  show ?thesis by auto
qed

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
    using Suc(3) using Suc(2) unfolding subst_atm_mset_list_def by auto (* unfolding should not be necessary  *)
  then have "length (tl (Ai' \<cdot>al \<eta>)) = n" "length (tl (Aij' \<cdot>aml \<eta>)) = n"
    by auto
  then have "length (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) = n" 
    "length (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) = n"
    using Suc(3) Suc(2) unfolding subst_atm_mset_list_def by auto
  ultimately
  have "\<forall>i < n. (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) ! i = (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) ! i"
    by auto
  then have "\<forall>i < n. tl (map2 add_mset ( (Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) ! i = tl (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! i"
    using Suc(2) Suc(3) Succ by (simp add: map2_tl map_tl subst_atm_mset_list_def)
  moreover 
  have nn: "length (map2 add_mset ((Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) = Suc n"
    "length (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) = Suc n"
    using Succ using Suc unfolding subst_atm_mset_list_def by auto (* I should not have to unfold *)
  ultimately 
  have "\<forall>i. i < Suc n \<longrightarrow> i > 0 \<longrightarrow> (map2 add_mset ((Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) ! i = (map2 add_mset ( Ai') (Aij') \<cdot>aml \<eta>) ! i"
    by (metis (no_types, lifting) Suc.prems(1) Suc.prems(2) Succ(1) Succ(2) \<open>length (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) = n\<close> 
         \<open>map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>)) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>\<close> less_Suc_eq_0_disj map2_tl map_tl neq0_conv nth_tl subst_atm_mset_list_def)
  moreover
  have "add_mset (hd Ai' \<cdot>a \<eta>) (hd Aij' \<cdot>am \<eta>) = add_mset (hd Ai') (hd Aij') \<cdot>am \<eta>"
    unfolding subst_atm_mset_def by auto
  then have "(map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) ! 0  = (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! 0"
    using Suc
    by (simp add: Succ(2) subst_atm_mset_def) 
  ultimately
  have "\<forall>i < Suc n. (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) ! i  = (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! i"
    using Suc by auto
  then show ?case 
    using nn list_eq_iff_nth_eq by metis
next
  case 0 then show ?case
    by auto
qed
  
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
    
  
    
  
  
lemma str_maximal_in_gen: (* a better proof might reuse the lemma maximal_in_gen *)
  assumes "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "str_maximal_in A C"
proof -
  from assms have "str_maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)" by -
  hence "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_eq_atm (A \<cdot>a \<sigma>) B" by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> (less_atm (A \<cdot>a \<sigma>) B \<or> A \<cdot>a \<sigma> = B)" unfolding less_eq_atm_def by -
  hence "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B)" unfolding less_atm_iff by -
  hence "\<forall>B\<in>atms_of (C) \<cdot>as \<sigma>. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B)" using atms_of_subst_atms by auto
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>') \<or> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)" 
    unfolding subst_atms_def by auto
  hence "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma>' < B \<cdot>a \<sigma>') \<or> A = B)"
    using is_ground_comp_subst by fastforce
  hence "\<forall>B\<in>atms_of C. \<not> (less_atm A B \<or> A = B)" unfolding less_atm_iff by -
  then show ?thesis unfolding less_eq_atm_def by auto
qed
  
lemma ground_resolvent_subset:
  assumes gr_c: "is_ground_cls_list CAi"
  assumes gr_d: "is_ground_cls DA"
  assumes resolve: "ord_resolve SSS CAi DA E"
  shows "E \<subseteq># (\<Union>#(mset CAi)) + DA"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
  hence "\<forall>i<n.  Ci ! i \<subseteq># CAi ! i " by auto
  hence cisucai: "\<Union>#mset Ci \<subseteq># \<Union>#(mset CAi)"
    using subseteq_list_Union_mset ord_resolve(3) ord_resolve(4) by force
  hence gr_ci: "is_ground_cls_list Ci" using gr_c
    by (metis is_ground_cls_Union_mset is_ground_cls_list_def is_ground_cls_mono is_ground_cls_mset_def set_mset_mset)
  have dsuDA :"D \<subseteq># DA" by (simp add: local.ord_resolve(1)) 
  hence gr_di: "is_ground_cls D"
    using gr_d is_ground_cls_mono by auto     
  
  have "is_ground_cls (\<Union>#mset Ci + D)" using gr_ci gr_di
    unfolding is_ground_cls_def is_ground_cls_list_def
    by (metis in_Union_mset_iff set_mset_mset union_iff)
  then have fffff: "(\<Union>#mset Ci + D) = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by auto
  from this ord_resolve have "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by -
  hence "E = (\<Union>#mset Ci + D)" using fffff by auto
  then show ?thesis using cisucai dsuDA by (auto simp add: subset_mset.add_mono)
qed
  
lemma ground_resolvent_ground: (* This proof should be more automatic I think... *)
  assumes "is_ground_cls_list CAi"
  assumes "is_ground_cls DA"
  assumes "ord_resolve SSS CAi DA E"
  shows "is_ground_cls E"
proof -
  from assms have "E \<subseteq># (\<Union>#(mset CAi)) + DA" using ground_resolvent_subset by auto
  then have "\<forall>e \<in># E. e \<in># \<Union>#(mset CAi) \<or> e \<in># DA" by auto
  then show "is_ground_cls E" unfolding is_ground_cls_def
    apply auto
    using assms(1) unfolding is_ground_cls_list_def is_ground_cls_def
    by (metis assms(2) in_mset_sum_list2 is_ground_cls_def)    
qed
  
lemma ord_resolve_obtain_clauses: 
  assumes resolve: "ord_resolve (S_M S M) CAi DA E" 
    and select: "selection S"
    and grounding: "{DA} \<union> (set CAi) \<subseteq> grounding_of_clss M"
    and n: "length CAi = n"
  obtains DA'' \<eta>'' CAi'' \<eta>s'' where
    "length CAi'' = n"
    "length \<eta>s'' = n"
    
    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi''. CA \<in> M" (* Could also use subseteq *)
    "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
    "(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve nn Ci Aij Ai \<sigma> D)
  then have "nn = n"
    using n by auto
  then have "n \<noteq> 0" "length Ci = n" "length Aij = n" "length Ai = n" using ord_resolve by auto
  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  interpret S: selection S by (rule select)
      
    (* Obtain CAi'' *)
  have "\<forall>CA \<in> set CAi. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> CA'' \<cdot> \<eta>c'' = CA \<and> S CA'' \<cdot> \<eta>c'' = S_M S M CA"
    using grounding using grounding S_M_grounding_of_clss select by (metis le_supE subset_iff)    
  hence "\<forall>i < n. \<exists>CA'' \<eta>c''. CA'' \<in> M \<and> CA'' \<cdot> \<eta>c'' = (CAi ! i) \<and> S CA'' \<cdot> \<eta>c'' = S_M S M (CAi ! i)"
    using n by auto
  then obtain \<eta>s''f CAi''f where f_p: 
    "\<forall>i < n. CAi''f i \<in> M" 
    "\<forall>i < n. (CAi''f i) \<cdot> (\<eta>s''f i) = (CAi ! i)"
    "\<forall>i < n. S (CAi''f i)  \<cdot> (\<eta>s''f i) = S_M S M (CAi ! i)"
    using n by metis
      
  define \<eta>s'' where "\<eta>s'' = map \<eta>s''f [0 ..<n]"
  define CAi'' where "CAi'' = map CAi''f [0 ..<n]"
    
  have "length \<eta>s'' = n" "length CAi'' = n"
    unfolding \<eta>s''_def CAi''_def by auto
  note n = \<open>length \<eta>s'' = n\<close> \<open>length CAi'' = n\<close> n
    
    (* The properties we need of CAi'' *)
  have CAi''_in_M: "\<forall>CA'' \<in> set CAi''. CA'' \<in> M" 
    unfolding CAi''_def using f_p(1) by auto
  have CAi''_to_CAi: "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi" 
    unfolding CAi''_def \<eta>s''_def using f_p(2) by (simp add: n)
  have SCAi''_to_SMCAi: "(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi"
   unfolding CAi''_def \<eta>s''_def using f_p(3) n by auto
      
    (* Obtain DA''  *) 
  have "\<exists>DA'' \<eta>''. DA'' \<in> M \<and> DA = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA"
    using grounding S_M_grounding_of_clss select by (metis le_supE singletonI subsetCE)
  then obtain DA'' \<eta>'' where DA''_\<eta>''_p: "DA'' \<in> M \<and> DA = DA'' \<cdot> \<eta>'' \<and> S DA'' \<cdot> \<eta>'' = S_M S M DA"
    by auto
      (* The properties we need of DA'' *)
  have DA''_in_M: "DA'' \<in> M" 
    using DA''_\<eta>''_p by auto
  have DA''_to_DA: "DA'' \<cdot> \<eta>'' = DA" 
    using DA''_\<eta>''_p by auto
  have SDA''_to_SMDA: "S DA'' \<cdot> \<eta>'' = S_M S M DA" 
    using DA''_\<eta>''_p by auto  
    
  show ?thesis
    using that DA''_in_M DA''_to_DA SDA''_to_SMDA CAi''_in_M CAi''_to_CAi SCAi''_to_SMCAi n by blast
qed
  
  
lemma ord_resolve_obtain_clauses_std_apart':
  assumes resolve: "ord_resolve (S_M S M) CAi DA E" 
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" 
    and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
    and grounding: "{DA} \<union> (set CAi) \<subseteq> grounding_of_clss M"
    and n: "length CAi = n"
  obtains CAi' \<eta>s' DA' \<eta>' where
    "length CAi' = n"
    "length \<eta>s' = n"
    
    "DA' \<in> M"
    "DA' \<cdot> \<eta>' = DA"
    "S DA' \<cdot> \<eta>' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    
    "var_disjoint (DA' # CAi')"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve nn Ci Aij Ai \<sigma> D)
  then have "nn = n"
    using n by auto
  then have "n \<noteq> 0" "length Ci = n" "length Aij = n" "length Ai = n" using ord_resolve by auto
  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  have selection_renaming_list_invariant: "\<And>\<rho>s Ci. length \<rho>s = length Ci \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Ci \<cdot>\<cdot>cl \<rho>s) = (map S Ci) \<cdot>\<cdot>cl \<rho>s"
    apply (rule nth_equalityI)
    using selection_renaming_invariant unfolding is_renaming_list_def apply auto
    done
      
    
  interpret S: selection S by (rule select)
      
      (* Obtain FO clauses *)
  obtain DA'' \<eta>'' CAi'' \<eta>s'' where clauses'':
    "length CAi'' = n"
    "length \<eta>s'' = n"
    
    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi''. CA \<in> M"
    "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
    "(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi"
    using resolve grounding select ord_resolve_obtain_clauses n by metis
      
  note n = \<open>length CAi'' = n\<close> \<open>length \<eta>s'' = n\<close> \<open>length CAi = n\<close> n
    
     (* Obtain renamings to standardize apart *)
  obtain \<rho>\<rho>s where \<rho>\<rho>s_p: "length \<rho>\<rho>s = length (DA'' # CAi'') \<and> (\<forall>\<rho>i \<in> set \<rho>\<rho>s. is_renaming \<rho>i) \<and> var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl \<rho>\<rho>s)"
    using make_var_disjoint[of "DA'' # CAi''"] by auto
  define \<rho> where "\<rho> = hd \<rho>\<rho>s"
  define \<rho>s where "\<rho>s = tl \<rho>\<rho>s"
    
  have "length \<rho>\<rho>s = Suc n" "length \<rho>s = n" 
    using \<rho>\<rho>s_p n \<rho>s_def by auto
  note n = \<open>length \<rho>\<rho>s = Suc n\<close> \<open>length \<rho>s = n\<close> n

  have \<rho>_ren: "is_renaming \<rho>"
    using \<rho>\<rho>s_p n unfolding \<rho>_def by (metis Suc_length_conv list.sel(1) list.set_intros(1)) 
  have \<rho>s_ren: "is_renaming_list \<rho>s"
    unfolding is_renaming_list_def using \<rho>\<rho>s_p unfolding \<rho>s_def by (metis list.sel(2) list.set_sel(2))
  have var_disj_DA''_CAi''_\<rho>_\<rho>s: "var_disjoint ((DA'' # CAi'') \<cdot>\<cdot>cl (\<rho> # \<rho>s))"
    using \<rho>\<rho>s_p unfolding \<rho>_def \<rho>s_def by (metis length_greater_0_conv list.exhaust_sel list.simps(3))
      
  define \<rho>_inv where "\<rho>_inv = inv_ren \<rho>" 
  define \<rho>s_inv where "\<rho>s_inv = map inv_ren \<rho>s"
    
  have "length \<rho>s_inv = n" 
    using \<rho>s_inv_def n by auto
  note n = \<open>length \<rho>s_inv = n\<close> n
    
    (* Define new FO clauses *)
  define CAi' where "CAi' = CAi'' \<cdot>\<cdot>cl \<rho>s"
  define DA' where "DA' = DA'' \<cdot> \<rho>"
    
  have "length CAi' = n" 
    unfolding CAi'_def using n by auto

    (* Define new ground instantiating clauses *)      
  define \<eta>' where "\<eta>' = \<rho>_inv \<odot> \<eta>''"
  define \<eta>s' where "\<eta>s' = \<rho>s_inv \<odot>s \<eta>s''"
    
  have "length \<eta>s' = n"
    unfolding \<eta>s'_def using n by auto
  note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
    
  have \<rho>_i_inv_id': "\<forall>i<n. \<rho>s ! i \<odot> \<rho>s_inv ! i = id_subst"
    using n \<rho>s_inv_def \<rho>s_ren unfolding is_renaming_list_def by auto
  then have \<rho>_i_inv_id: "\<rho>s \<odot>s \<rho>s_inv = replicate n id_subst"
    using n \<rho>s_inv_def \<rho>s_ren by auto
  
  
      
  have CAi'_in_M: "\<forall>i < n. CAi' ! i \<in> M" (* TODO: For some reason this is not easy to change to \<forall>\<in>set *)
    unfolding CAi'_def using \<rho>s_ren M_renaming_invariant clauses''(6) n unfolding is_renaming_list_def by simp
  then have CAi'_in_M: "\<forall>CA' \<in> set CAi'. CA' \<in> M"
    using n by (metis in_set_conv_nth)
  have CAi'_CAi: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    unfolding CAi'_def \<eta>s'_def \<rho>s_inv_def using \<rho>s_ren \<open>CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi\<close> n by simp
        
  have SCAi'_\<eta>s'_SMCAi: "(map S) CAi' \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    using \<open>(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi\<close> unfolding CAi'_def \<eta>s'_def
    using inv_ren_is_renaming_list selection_renaming_list_invariant \<rho>s_ren n unfolding \<rho>s_inv_def 
    by auto
    
  have DA'_in_M: "DA' \<in> M"
    using M_renaming_invariant unfolding DA'_def using \<rho>_ren clauses'' by auto
  have DA'_DA: "DA' \<cdot> \<eta>' = DA"
    using DA'_def \<eta>'_def \<open>DA'' \<cdot> \<eta>'' = DA\<close> subst_cls_id_subst
    by (metis \<rho>_inv_def \<rho>_ren inv_ren_cancel_r subst_cls_comp_subst)
  have SDA'_SMDA: "S DA' \<cdot> \<eta>' = S_M S M DA"
    using \<open>(S DA'') \<cdot> \<eta>'' = (S_M S M) DA\<close> unfolding DA'_def \<eta>'_def
    using inv_ren_is_renaming selection_renaming_invariant \<rho>_ren n unfolding \<rho>_inv_def 
    by auto
    
  have CAi'_in_M: "\<forall>CA \<in> set CAi'. CA \<in> M"
    using CAi'_in_M n by metis 
  have SCAi'_SMCAi: "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    using SCAi'_\<eta>s'_SMCAi n by auto
      
  have var_disj_DA'_CAi': "var_disjoint (DA' # CAi')"
    using DA'_def CAi'_def var_disj_DA''_CAi''_\<rho>_\<rho>s by auto
      
  show ?thesis
    using that
      n DA'_in_M DA'_DA SDA'_SMDA CAi'_in_M CAi'_CAi SCAi'_SMCAi var_disj_DA'_CAi'
    by metis
qed
  
lemma ord_resolve_obtain_clauses_std_apart:
  assumes resolve: "ord_resolve (S_M S M) CAi DA E" 
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" 
    and M_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<in> M \<longleftrightarrow> C \<in> M"
    and grounding: "{DA} \<union> (set CAi) \<subseteq> grounding_of_clss M"
    and n: "length CAi = n"
  obtains CAi' DA' \<eta> where (* Overwriting the old clauses' *)
    "length CAi' = n"
    
    "DA' \<in> M"
    "DA' \<cdot> \<eta> = DA"
    "S DA' \<cdot> \<eta> = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>cl \<eta> = CAi"
    "(map S CAi') \<cdot>cl \<eta> = map (S_M S M) CAi"
    
    "is_ground_subst \<eta>"
    "var_disjoint (DA' # CAi')"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve nn Ci Aij Ai \<sigma> D)
  then have "nn = n"
    using n by auto
  then have"n \<noteq> 0" "length Ci = n" "length Aij = n" "length Ai = n" using ord_resolve by auto
      
  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  interpret S: selection S by (rule select)
      
      (* Obtain FO clauses *)
  obtain DA' \<eta>' CAi' \<eta>s' where clauses':
    "length CAi' = n"
    "length \<eta>s' = n"
    
    "DA' \<in> M"
    "DA' \<cdot> \<eta>' = DA"
    "S DA' \<cdot> \<eta>' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    
    "var_disjoint (DA' # CAi')"
    using selection_renaming_invariant M_renaming_invariant resolve grounding select ord_resolve_obtain_clauses_std_apart'[of S M] n by blast
      
  note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
    
    (* Obtain FO substitution that replaces (\<eta>' # \<eta>s') *)
  from clauses' have var_disj_DA'_CAi': "var_disjoint ((DA' # CAi'))"
    by auto
  then obtain \<eta>_fo where \<eta>_p: "(\<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> (\<eta>' # \<eta>s') ! i = S \<cdot> \<eta>_fo)" unfolding var_disjoint_def
    using n by (metis length_Cons) 
  from \<eta>_p have DA'_\<eta>_fo_sel: "(S DA') \<cdot> \<eta>' = (S DA') \<cdot> \<eta>_fo" 
    using S.S_selects_subseteq by auto
  from \<eta>_p have DA'_\<eta>: "DA' \<cdot> \<eta>' = DA' \<cdot> \<eta>_fo" 
    by auto
      
  from \<eta>_p have "\<forall>i<n. (S ((CAi') ! i)) \<cdot> \<eta>s' ! i = (S ((CAi') ! i)) \<cdot> \<eta>_fo" 
    using S.S_selects_subseteq by auto
  then have cai'_\<eta>_fo_sel: "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = (map S CAi') \<cdot>cl \<eta>_fo"
    using n by auto
  from \<eta>_p have "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = (CAi'! i) \<cdot> \<eta>_fo"
    by auto
  then have cai'_\<eta>_fo: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi' \<cdot>cl \<eta>_fo"
    using n by auto
      
  have CAi'_in_M: "\<forall>i < n. CAi' ! i \<in> M" using clauses' by auto
  have CAi'_\<eta>_fo_CAi: "CAi' \<cdot>cl \<eta>_fo = CAi"
    using clauses' cai'_\<eta>_fo by auto
  
  have SCAi'_\<eta>_fo_SMCAi: "(map S CAi') \<cdot>cl \<eta>_fo = map (S_M S M) CAi"
    using cai'_\<eta>_fo_sel clauses' by auto
    
  have "DA' \<in> M" using clauses' by auto
  have "DA' \<cdot> \<eta>_fo = DA" using DA'_\<eta>
    using clauses' by auto 
  have "S DA' \<cdot> \<eta>_fo = S_M S M DA"
   using clauses' DA'_\<eta>_fo_sel by auto
    
    (* Obtain ground substitution *)
    
  obtain \<eta> where \<eta>_p: "is_ground_subst \<eta> \<and> (\<forall>i<length (DA' # CAi'). \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> \<eta>_fo = S \<cdot> \<eta>)"
    using make_ground_subst[of "DA' # CAi'" \<eta>_fo] grounding \<open>CAi' \<cdot>cl \<eta>_fo = CAi\<close> \<open>DA' \<cdot> \<eta>_fo = DA\<close> grounding_ground by metis
      
  from \<eta>_p have DA'_\<eta>_fo_sel: "(S DA') \<cdot> \<eta>_fo = (S DA') \<cdot> \<eta>" 
    using S.S_selects_subseteq by auto
  from \<eta>_p have DA'_\<eta>: "DA' \<cdot> \<eta>_fo = DA' \<cdot> \<eta>" 
    by auto
      
  from \<eta>_p have "\<forall>i<n. (S ((CAi') ! i)) \<cdot> \<eta>_fo = (S ((CAi') ! i)) \<cdot> \<eta>" 
    using n S.S_selects_subseteq by auto
  then have cai'_\<eta>_fo_sel: "(map S CAi') \<cdot>cl \<eta>_fo = (map S CAi') \<cdot>cl \<eta>"
    using n by auto
  from \<eta>_p have "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>_fo) = (CAi'! i) \<cdot> \<eta>"
    using n by auto
  then have cai'_\<eta>_fo: "CAi' \<cdot>cl \<eta>_fo = CAi' \<cdot>cl \<eta>"
    using n by auto
      
  have "\<forall>i < n. CAi' ! i \<in> M" using clauses' n by auto
  have CAi'_CAi: "CAi' \<cdot>cl \<eta> = CAi"
    using cai'_\<eta>_fo CAi'_\<eta>_fo_CAi by simp
      
  have SCAi'_SMCAi: "map S (CAi') \<cdot>cl \<eta> = map (S_M S M) CAi"
    using cai'_\<eta>_fo_sel SCAi'_\<eta>_fo_SMCAi by auto
    
  have DA'_in_M: "DA' \<in> M" using clauses' by auto
  have DA'_DA: "DA' \<cdot> \<eta> = DA" using \<open>DA' \<cdot> \<eta>_fo = DA\<close> \<eta>_p by auto
  have SDA'_SMDA: "S DA' \<cdot> \<eta> = S_M S M DA"
    using \<open>S DA' \<cdot> \<eta>_fo = S_M S M DA\<close> using \<eta>_p S.S_selects_subseteq by auto

  show ?thesis using that
      DA'_in_M  DA'_DA SDA'_SMDA clauses' CAi'_CAi SCAi'_SMCAi \<eta>_p var_disj_DA'_CAi' n by auto  
qed
  
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
    "CAi' \<cdot>cl \<eta> = CAi" "DA' \<cdot> \<eta> = DA" "E' \<cdot> \<eta>2 = E" (* In the previous proofs I have CAi and DA on lfs of equality... *)
    "{DA'} \<union> set CAi' \<subseteq> M"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai \<sigma> D)
    
  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  interpret S: selection S by (rule select)
      
  obtain \<eta> DA' CAi' where clauses': (* Overwriting the old clauses' *)
    "length CAi' = n"
    
    "DA' \<in> M"
    "DA' \<cdot> \<eta> = DA"
    "S DA' \<cdot> \<eta> = S_M S M DA"
    
    "\<forall>CA \<in> set CAi'. CA \<in> M"
    "CAi' \<cdot>cl \<eta> = CAi"
    "(map S CAi') \<cdot>cl \<eta> = map (S_M S M) CAi"
    
    "is_ground_subst \<eta>"
    "var_disjoint (DA' # CAi')"
    using ord_resolve_obtain_clauses_std_apart[of S M CAi DA E n] assms n by blast
      
  note n = \<open>length CAi' = n\<close> n 
    
    (* Split in to D's and A's *)
  obtain Ai' D' where ai':
    "length Ai' = n"
    
    "Ai' \<cdot>al \<eta> = Ai"
    "D' \<cdot> \<eta> = D"
    "DA' = D' + (negs (mset Ai'))"
    "S_M S M (D + negs (mset Ai)) \<noteq> {#} \<Longrightarrow> negs (mset Ai') = S DA'"
  proof -
    from ord_resolve(11) have "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> (negs (mset Ai')) \<subseteq># DA' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DA')"
      unfolding eligible_simp
    proof
      assume a: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
      then have "mset Ai = {# Ai ! 0 #}" 
        by auto
      then have "negs (mset Ai) = {# Neg (Ai ! 0) #}"
        by (simp add: \<open>mset Ai = {# Ai ! 0 #}\<close>)
      then have "DA = D + {#Neg (Ai ! 0)#}" 
        using ord_resolve(1) by auto
      then obtain L where "L \<in># DA' \<and> L \<cdot>l \<eta> = Neg (Ai ! 0)" 
        using \<open>DA' \<cdot> \<eta> = DA\<close> by (metis Melem_subst_cls mset_subset_eq_add_right single_subset_iff)
      then have "Neg (atm_of L) \<in># DA' \<and> Neg (atm_of L) \<cdot>l \<eta> = Neg (Ai ! 0)"
        by (metis Neg_atm_of_iff literal.sel(2) subst_lit_is_pos)
      then have "[atm_of L] \<cdot>al \<eta> = Ai \<and> negs (mset [atm_of L]) \<subseteq># DA'"
        using \<open>mset Ai = {#Ai ! 0#}\<close> subst_lit_def by auto
      then show "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> negs (mset Ai') \<subseteq># DA' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DA')" 
        using a by blast
    next
      assume "S_M S M (D + negs (mset Ai)) = negs (mset Ai)" 
      then have "negs (mset Ai) = S DA' \<cdot> \<eta>" 
        using ord_resolve(1) \<open>S DA' \<cdot> \<eta> = S_M S M DA\<close> by auto
      then have "\<exists>Ai'. negs (mset Ai') = S DA' \<and> Ai' \<cdot>al \<eta> = Ai"
        using instance_list[of Ai "S DA'" \<eta>] using S.S_selects_neg_lits by auto
      then show "\<exists>Ai'. Ai' \<cdot>al \<eta> = Ai \<and> negs (mset Ai') \<subseteq># DA'  \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DA')" 
        using S.S_selects_subseteq by auto
    qed
    then obtain Ai' where Ai'_p: "Ai' \<cdot>al \<eta> = Ai \<and> (negs (mset Ai')) \<subseteq># DA' \<and> (S_M S M (D + negs (mset Ai)) \<noteq> {#} \<longrightarrow> negs (mset Ai') = S DA')" 
      by blast
    then have "length Ai' = n"
      using local.ord_resolve(6) by auto
    note n = n \<open>length Ai' = n\<close>
      
    have "Ai' \<cdot>al \<eta> = Ai" using Ai'_p by auto
        
    define D' where "D' = DA' - (negs (mset Ai'))"
    then have DA'_u: "DA' = D' +  (negs (mset Ai'))" using Ai'_p by auto
        
    have "D' \<cdot> \<eta> = D" 
      using \<open>DA' \<cdot> \<eta> = DA\<close> ord_resolve(1) DA'_u Ai'_p by auto
        
    have "S_M S M (D + negs (mset Ai)) \<noteq> {#} \<Longrightarrow> negs (mset Ai') = S DA'"
      using Ai'_p by blast
        
        
    show ?thesis using that
        \<open>Ai' \<cdot>al \<eta> = Ai\<close>
        \<open>D' \<cdot> \<eta> = D\<close>
        \<open>DA' = D' +  (negs (mset Ai'))\<close>
        \<open>S_M S M (D + negs (mset Ai)) \<noteq> {#} \<Longrightarrow> negs (mset Ai') = S DA'\<close>
        \<open>length Ai' = n\<close>
      by metis
  qed
    
  note n = n \<open>length Ai' = n\<close>
    
    (* Split in to C's and A's *)
  obtain Aij' Ci'  where Aij'_Ci'_p:
    "length Aij' = n"
    "length Ci' = n"
    
    "Aij' \<cdot>aml \<eta> = Aij"
    "Ci' \<cdot>cl \<eta> = Ci"
    "\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)" (* Write in list notation? *)
  proof -
    have "\<forall>i<n. \<exists>Aiji'. Aiji' \<cdot>am \<eta> = Aij ! i \<and> (poss Aiji') \<subseteq># CAi' ! i"
    proof (rule, rule)
      fix i
      assume "i<n"
      have "CAi' ! i \<cdot> \<eta> = CAi ! i"
        using \<open>i < n\<close> clauses'(1,6) n by auto
      moreover
      have "poss (Aij ! i) \<subseteq># CAi !i"
        using \<open>i<n\<close> ord_resolve(8) by auto
      ultimately
      obtain NAiji' where nn: "NAiji' \<cdot> \<eta> = poss (Aij ! i) \<and> NAiji' \<subseteq># CAi' ! i"
        using clauses' ord_resolve(8) image_mset_of_subset unfolding subst_cls_def by metis
      then have l: "\<forall>L \<in># NAiji'. is_pos L"
        unfolding subst_cls_def by (metis Melem_subst_cls imageE literal.disc(1) literal.map_disc_iff set_image_mset subst_cls_def subst_lit_def) 
      define Aiji' where "Aiji' = image_mset atm_of NAiji'"
      have na: "poss Aiji' = NAiji'"
        using l unfolding Aiji'_def by auto
      then have "Aiji' \<cdot>am \<eta> = Aij ! i"
        using nn by (metis literal.inject(1) multiset.inj_map_strong subst_cls_poss)
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

    from Aij'_def have "\<forall>i<n. Aij' ! i \<cdot>am \<eta> = Aij ! i"
      using Aij'f_p by auto
    then have Aij'_Aij: "Aij' \<cdot>aml \<eta> = Aij"
      using n unfolding subst_atm_mset_list_def by auto (* unfolding should not be necessary *)
        
    from Aij'_def have Aij'_in_CAi': "\<forall>i<n. (poss (Aij' ! i)) \<subseteq># CAi' ! i"
      using Aij'f_p by auto
        
    define Ci' where "Ci' = map2 (op -) CAi' (map poss Aij')"
      
    have "length Ci' = n"
      using Ci'_def n by auto
    note n = n \<open>length Ci' = n\<close>

    have "\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)"
     using Aij'_in_CAi' using Ci'_def n by auto
    then have "Ci' \<cdot>cl \<eta> = Ci"
      using nth_equalityI clauses' n Aij'_Aij ord_resolve(8) by auto
      
    show ?thesis using that 
        \<open>Aij' \<cdot>aml \<eta> = Aij\<close>
        \<open>Ci' \<cdot>cl \<eta> = Ci\<close>
        \<open>\<forall>i < n. CAi' ! i = Ci' ! i + poss (Aij' ! i)\<close>
        \<open>length Aij' = n\<close>
        \<open>length Ci' = n\<close>
      by blast
  qed
    
  note n = n \<open>length Aij' = n\<close> \<open>length Ci' = n\<close>
    
    (* Obtain mgu and substitution *)
  obtain \<tau>  \<phi> where \<tau>\<phi>:
    "Some \<tau> = mgu (set_mset ` set (map2 add_mset Ai' Aij'))"
    "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
  proof -
    have "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
    hence uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)))"
      using mgu_sound is_mgu_def unfolding \<open>Aij' \<cdot>aml \<eta> = Aij\<close> using ai' by auto
    have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset Ai' Aij'))"
    proof -
      have eq: "(set_mset ` set (map2 add_mset Ai' Aij' \<cdot>aml \<eta>)) = (set_mset ` set (map2 add_mset Ai' Aij') \<cdot>ass \<eta>)"
        unfolding subst_atmss_def
          subst_atm_mset_list_def
        using subst_atm_mset_def subst_atms_def by auto
      have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)))" using uu by -
      then have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset Ai' Aij') \<cdot>aml \<eta>))" using n map2_add_mset_map by auto
      then have "is_unifiers \<sigma> (set_mset ` set ((map2 add_mset Ai' Aij')) \<cdot>ass \<eta>)" using eq by auto
      then show ?thesis 
        using is_unifiers_comp by auto
    qed
    then obtain \<tau> where \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset Ai' Aij'))" using mgu_complete
      by (metis (mono_tags, hide_lams) finite_imageI finite_set_mset image_iff set_mset_mset) (* should be simpler? *) 
    moreover
    then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
      by (metis (mono_tags, hide_lams) List.finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff mgu_sound set_mset_mset substitution_ops.is_mgu_def that) (* should be simpler *)
    ultimately show ?thesis using that by auto 
  qed
    
    
    (* Lifting eligibility *)
  have eligibility: "eligible S \<tau> Ai' (D' + negs (mset Ai'))" 
  proof -
    have "eligible (S_M S M) \<sigma> Ai (D + negs (mset Ai))" using ord_resolve unfolding eligible_simp by -
    hence "S_M S M (D + negs (mset Ai)) = negs (mset Ai) \<or>
    S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" 
      unfolding eligible_simp by -
    thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))"
    proof
      assume as: "S_M S M (D + negs (mset Ai)) = negs (mset Ai)"
      then have "S_M S M (D + negs (mset Ai)) \<noteq> {#}"
        using n ord_resolve(7) by force
      then have "negs (mset Ai') = S DA'" using ai' by auto
      hence "S (D'  + negs (mset Ai')) = negs (mset Ai')" using ai' by auto
      thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible_simp by auto
    next
      assume asm: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
      let ?A = "Ai ! 0"
      from asm have "S_M S M (D + negs (mset Ai)) = {#}" by auto
      hence "S (D' + negs (mset Ai')) = {#}" using \<open>D' \<cdot> \<eta> = D\<close>[symmetric] \<open>Ai' \<cdot>al \<eta> = Ai\<close>[symmetric] \<open>S (DA') \<cdot> \<eta> = S_M S M (DA)\<close>
        using ord_resolve(1) 
        using ai' subst_cls_empty_iff by metis   
      moreover
      from asm have l: "length Ai = 1" by auto
      hence l': "length Ai' = 1" using \<open>Ai' \<cdot>al \<eta> = Ai\<close>[symmetric] by auto
      moreover
      from asm have "maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)" by auto
      hence "maximal_in (Ai' ! 0 \<cdot>a (\<eta> \<odot> \<sigma>)) ((D' + negs (mset Ai')) \<cdot> (\<eta> \<odot> \<sigma>))" unfolding \<open>Ai' \<cdot>al \<eta> = Ai\<close>[symmetric] \<open>D' \<cdot> \<eta> = D\<close>[symmetric]
        using l' by auto  
      hence "maximal_in (Ai' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D' + negs (mset Ai')) \<cdot> (\<tau> \<odot> \<phi>))" unfolding \<open>Ai' \<cdot>al \<eta> = Ai\<close>[symmetric] \<open>D' \<cdot> \<eta> = D\<close>[symmetric]
        using \<tau>\<phi> by auto
      hence "maximal_in (Ai' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D' + negs (mset Ai')) \<cdot> \<tau> \<cdot> \<phi>)" 
        by auto
      hence "maximal_in (Ai' ! 0 \<cdot>a \<tau>) ((D' + negs (mset Ai')) \<cdot> \<tau>)" using maximal_in_gen by blast
      ultimately show "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible_simp by auto 
    qed
  qed
    
    (* Lifting maximality *)
  have maximality: "\<forall>i<n. str_maximal_in (Ai' ! i \<cdot>a \<tau>) (Ci' ! i \<cdot> \<tau>)" 
    (* Reformulate in list notation? *)
  proof -
    from ord_resolve have "\<forall>i<n. str_maximal_in (Ai ! i \<cdot>a \<sigma>) (Ci ! i \<cdot> \<sigma>)" by -
    hence "\<forall>i<n. str_maximal_in ((Ai' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Ci' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)" using \<open>Ai' \<cdot>al \<eta> = Ai\<close>  \<open>Ci' \<cdot>cl \<eta> = Ci\<close> by simp
    hence "\<forall>i<n. str_maximal_in ((Ai' ! i) \<cdot>a (\<eta> \<odot> \<sigma>)) ((Ci' ! i) \<cdot> (\<eta> \<odot> \<sigma>))" using n by auto
    hence "\<forall>i<n. str_maximal_in ((Ai' ! i) \<cdot>a (\<tau> \<odot> \<phi>)) ((Ci' ! i) \<cdot> (\<tau> \<odot> \<phi>))" using \<tau>\<phi> by auto
    hence "\<forall>i<n. str_maximal_in ((Ai' ! i \<cdot>a \<tau>) \<cdot>a \<phi>) ((Ci' ! i \<cdot> \<tau>) \<cdot> \<phi>)" by auto
    then show e: "\<forall>i<n. str_maximal_in (Ai' ! i \<cdot>a \<tau>) (Ci' ! i \<cdot> \<tau>)" using str_maximal_in_gen \<tau>\<phi> by blast
  qed
    
    (* Lifting nothing selected *)
  have nothing_selected: "\<forall>i < n. S (CAi' ! i) = {#}"
  proof -
    have "\<forall>i < n. (map S CAi' \<cdot>cl \<eta>) ! i = (map (S_M S M) CAi) ! i"
      using clauses'(7) by auto
    then have "\<forall>i < n. S (CAi' ! i) \<cdot> \<eta> = S_M S M (CAi ! i)"
      using n by auto
    hence "\<forall>i < n. S (CAi' ! i)  \<cdot> \<eta> = {#}" using ord_resolve(13) \<open>\<forall>i < n.  S (CAi' ! i) \<cdot> \<eta> = S_M S M (CAi ! i)\<close> by auto 
    then show "\<forall>i < n. S (CAi' ! i) = {#}" using subst_cls_empty_iff by blast
  qed
    
    (* Lifting Aij's non-empty *)
  have "\<forall>i<n. Aij' ! i \<noteq> {#}"
    using n ord_resolve(9) \<open>Aij' \<cdot>aml \<eta> = Aij\<close> by auto
      
    (* Resolve the lifted clauses *)
  define E' where "E' = ((\<Union># (mset Ci')) + D') \<cdot> \<tau>"   
    
  have res_e: "ord_resolve S CAi' DA' E'" 
    using ord_resolve.intros[of CAi' n Ci' Aij' Ai' \<tau> S D', 
        OF 
        _ _ _ _
        _
        _
        \<open>\<forall>i<n. Aij' ! i \<noteq> {#}\<close> 
        \<tau>\<phi>(1)
        eligibility
        \<open>\<forall>i<n. str_maximal_in (Ai' ! i \<cdot>a \<tau>) (Ci' ! i \<cdot> \<tau>)\<close>
        \<open>\<forall>i<n. S (CAi' ! i) = {#}\<close>
        ] 
    unfolding E'_def using ai' n Aij'_Ci'_p
    by blast
      
      
      (* Prove resolvent instantiates to ground resolvent *)
  have e'\<phi>e: "E' \<cdot> \<phi> = E" 
  proof -
    have "E' \<cdot> \<phi> = ((\<Union># (mset Ci')) + D') \<cdot> (\<tau> \<odot> \<phi>)" unfolding E'_def by auto
    also have "... = ((\<Union># (mset Ci')) + D') \<cdot> (\<eta> \<odot> \<sigma>)" using \<tau>\<phi> by auto
    also have "... = ((\<Union># (mset (Ci' \<cdot>cl \<eta>))) + (D' \<cdot> \<eta>)) \<cdot> \<sigma>" by simp
    also have "... = ((\<Union># (mset Ci)) + D) \<cdot> \<sigma>" using  \<open>Ci' \<cdot>cl \<eta> = Ci\<close> \<open>D' \<cdot> \<eta> = D\<close> by auto
    also have "... = E" using ord_resolve by auto
    finally show e'\<phi>e: "E' \<cdot> \<phi> = E" .
  qed
    
    (* Replace \<eta> with ground substitution *)
  obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E"
  proof -
    have "is_ground_cls_list CAi" "is_ground_cls DA"
      using grounding grounding_ground unfolding is_ground_cls_list_def by auto 
    hence "is_ground_cls E" using resolve ground_resolvent_ground by auto
    then obtain \<eta>2 where ground_\<eta>2: "is_ground_subst \<eta>2" "E' \<cdot> \<eta>2 = E" using e'\<phi>e make_single_ground_subst by blast
    then show ?thesis using that by auto
  qed

  show ?thesis using that
      ground_\<eta>2 res_e clauses' by blast
qed
  
end
  
locale FO_resolution_with_selection =
  FO_resolution subst_atm id_subst comp_subst mgu less_atm +
  selection S
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s => 's => 's" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    N0 :: "'a clause set"
  assumes
    finite_N0: "finite N0"
begin

interpretation ground_resolution_with_S: ground_resolution_with_selection S
  by unfold_locales

definition ord_FO_\<Gamma> :: "'a inference set" where
  "ord_FO_\<Gamma> = {Infer CC D E | CC D E Cl. ord_resolve S Cl D E \<and> mset Cl = CC}"

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

inductive subsume_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsume_resolve (D + {#L#}) (C + (D + {#- L#}) \<cdot> \<sigma>) (C + D \<cdot> \<sigma>)"

text {*
@{text O} denotes relation composition in Isabelle, so the formalization uses @{text Q} instead.
*}
  
inductive resolution_prover :: "('a clause set \<times> 'a clause set \<times> 'a clause set) \<Rightarrow> ('a clause set \<times> 'a clause set \<times> 'a clause set) \<Rightarrow> bool" (infix "\<leadsto>" 50)  where
 tautology_deletion: "(\<forall>I. I \<Turnstile> C) \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| forward_subsumption: "(\<exists>D \<in> P \<union> Q. subsumes D C) \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_P: "(\<exists>D \<in> N. properly_subsumes D C) \<Longrightarrow> (N, P \<union> {C}, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_Q: "(\<exists>D \<in> N. properly_subsumes D C) \<Longrightarrow> (N, P, Q \<union> {C}) \<leadsto> (N, P, Q)"
| forward_reduction: "(\<exists>D L'. D + {#L'#} \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N \<union> {C + {#L#}}, P, Q) \<leadsto> (N \<union> {C}, P, Q)"
| backward_reduction_P: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P \<union> {C + {#L#}}, Q) \<leadsto> (N, P \<union> {C}, Q)"
| backward_reduction_Q: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P, Q \<union> {C + {#L#}}) \<leadsto> (N, P \<union> {C}, Q)"
| clause_processing: "(N \<union> {C}, P, Q) \<leadsto> (N, P \<union> {C}, Q)"
| inference_computation:
    "N = concls_of (ord_FO_resolution.inferences_from (Q \<union> {C})) \<Longrightarrow>
     ({}, P \<union> {C}, Q) \<leadsto> (N, P, Q \<union> {C})"

definition limit_state ::
  "('a state) llist \<Rightarrow> 'a state"
where
  "limit_state Sts = (llimit (lmap (\<lambda>(N, _, _). N) Sts), llimit (lmap (\<lambda>(_, P, _). P) Sts),
     llimit (lmap (\<lambda>(_, _, Q). Q) Sts))"

definition fair_state_seq where
  "fair_state_seq Sts = (let (N, P, _) = limit_state Sts in N = {} \<and> P = {})"

text {*
The following corresponds to Lemma 4.10:
*}
  
term "ground_resolution_with_S.ord_resolve"
term rtrancl
term src_derive
term "src_derive S" (* Should this constant really take an S? I don't think so when looking in the book.  *)
  (* The thing is. This deriv is based on Os and std redundancy. BUT what I need for 4.10 is a deriv based on
     an extension of Os and the standard extension of std redundancy wrt the extension of Os. *)
term "src_ext_derive"
  
thm src_derive_src_derive
(* That src derive up there seems rather strange. Let's do it down here. MAybe... *)
(* Actually, the whole file is structured a bit strange I think. *)
(* Another thing that is kind of weird is S_M. I mean: We start by having a selection function S for FOL.
   This selection function will also choose selections for the ground clauses.
   Then we create the modified S_M.
   It is a redefinition of S that gives another result for the ground_clauses, namely the same selection as
   on some first-order clause of which it is an instance.
   But why not just assume that S has this property to begin with instead of modifying it?
 *)
term gd_ord_\<Gamma> 
thm gd_ord_\<Gamma>_gd_ord_\<Gamma>
  

  
(* The extension of ordered resolution mentioned in 4.10. Following Uwe's recommendation I make it enormous, 
   i.e. consisting of all satisfiability preserving rules *)
  
context (* In order to do lemma 4.10 I introduce an arbitrary M and an arbitrary S because the theorem is independent of this choice *)
  fixes M_arb :: "'a clause set"
  fixes S_arb :: "'a literal multiset \<Rightarrow> 'a literal multiset"
  assumes select: "selection S_arb"
begin
  
(* I need to interpret derive with \<Gamma>' and R as the standard extension wrt Os of standard redundancy *)
  
lemma resolution_prover_rtc_deriv:
  assumes "St \<leadsto> St'"
  shows "rtranclp src_ext_derive (grounding_of_state St) (grounding_of_state St')"
using assms proof (induction rule: resolution_prover.induct)
  case (tautology_deletion C N P Q)
  then show ?case sorry
next
  case (forward_subsumption P Q C N)
  then obtain D where D_p: "D\<in>P \<union> Q \<and> subsumes D C"
    by auto
  let ?S = "(N \<union> {C}, P, Q)"
  let ?S' = "(N, P, Q)"
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def) 
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then show ?case sorry
  next
    assume "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src_Rf (grounding_of_cls D)"
      apply rule
      unfolding grounding_of_cls_def
      unfolding src_Rf_def[of S_arb, OF select] 
      using standard_redundancy_criterion.Rf_def
        (* Look at this weird stuff... Probably you should be doing all this stuff in a context where those things are avaiable
           I.e. up where src.ext_derive was defined. Or maybe put its definition and the relevant interpretations down here.
           That might actually make more sense. Yes. Even pull the lifting lemma down here. And then don't assume that you have
           that finite N0. Instead put N0 on the prover as an argument. And when you do a lemma where you need that N0 is finite
           then just assume it there.
         *)
        sorry
    then show ?case
      sorry
  qed
next
  case (backward_subsumption_P N C P Q)
  then show ?case sorry
next
  case (backward_subsumption_Q N C P Q)
  then show ?case sorry
next
  case (forward_reduction P Q L \<sigma> C N)
  then show ?case sorry
next
  case (backward_reduction_P N L \<sigma> C P Q)
  then show ?case sorry
next
  case (backward_reduction_Q N L \<sigma> C P Q)
  then show ?case sorry
next
  case (clause_processing N C P Q)
  then show ?case sorry
next
  case (inference_computation N Q C P)
  then show ?case sorry
oops
  

end

text {*
The following corresponds to (one direction of) Theorem 4.13:
*}

theorem completeness:
  assumes
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    unsat: "\<not> satisfiable (grounding_of_state (limit_state Sts))"
  shows "{#} \<in> clss_of_state (limit_state Sts)"
proof -
  let ?N = "\<lambda>i. grounding_of_state (lnth Sts i)"
  define \<Gamma>x :: "'a inference set" where "\<Gamma>x = undefined"
  define Rf :: "'a literal multiset set \<Rightarrow> 'a literal multiset set" where "Rf = standard_redundancy_criterion.Rf"
  define derive where "derive = redundancy_criterion.derive \<Gamma>x Rf"
    
    
oops
  
end
  
end