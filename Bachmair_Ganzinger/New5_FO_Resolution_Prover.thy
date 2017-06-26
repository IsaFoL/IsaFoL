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
  
fun getN :: "'a state \<Rightarrow> 'a clause set" where
  "getN (N,P,Q) = N"
  
fun getP :: "'a state \<Rightarrow> 'a clause set" where
  "getP (N,P,Q) = P"
  
fun getQ :: "'a state \<Rightarrow> 'a clause set" where
  "getQ (N,P,Q) = Q"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = getN St \<union> getP St \<union> getQ St"

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

inductive ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "length (CAi :: 'a clause list) = n \<Longrightarrow>
   length (Ci  :: 'a clause list) = n \<Longrightarrow>
   length (Aij :: 'a multiset list) = n \<Longrightarrow> (* Skal det vaere en clause istedet?*)
   length (Ai  :: 'a list) = n \<Longrightarrow>
   n \<noteq> 0 \<Longrightarrow>
   \<forall>i < n. (CAi ! i) = (Ci ! i + (poss (Aij ! i))) \<Longrightarrow> (* could be written with map *)
   \<forall>i < n. Aij ! i \<noteq> {#} \<Longrightarrow>
   Some \<sigma> = mgu (set_mset ` (set (map2 add_mset Ai Aij))) \<Longrightarrow> 
   eligible \<sigma> Ai (D + negs (mset Ai)) \<Longrightarrow>
   \<forall>i. i < n \<longrightarrow> str_maximal_in (Ai ! i \<cdot>a \<sigma>) ((Ci ! i) \<cdot> \<sigma>) \<Longrightarrow>
   \<forall>i < n. S (CAi ! i) = {#} \<Longrightarrow> (* Use the ! style instead maybe, or maybe us the \<forall>\<in>. style above *)
   ord_resolve CAi (D + negs (mset Ai)) \<sigma> (((\<Union># (mset Ci)) + D) \<cdot> \<sigma>)"    
  
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
 
inductive ord_resolve_rename :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve_rename:
  "\<rho> = hd (mk_var_dis (DA#CAi)) \<Longrightarrow>
   \<rho>s = tl (mk_var_dis (DA#CAi)) \<Longrightarrow>
   ord_resolve (CAi \<cdot>\<cdot>cl \<rho>s) (DA \<cdot> \<rho>) \<sigma> E \<Longrightarrow>
   ord_resolve_rename CAi DA \<sigma> E"
  


lemma ground_prems_ord_resolve_rename_imp_ord_resolve:
  assumes 
    gr_cc: "is_ground_cls_list CAi" and
    gr_d: "is_ground_cls DA" and
    res_e_re: "ord_resolve_rename CAi DA \<sigma> E"
  shows "ord_resolve CAi DA \<sigma> E"
  using res_e_re proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  then have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>" using mk_var_dis_jaja
    by (metis list.sel(2) list.set_sel(2)) 
  from ord_resolve_rename have len: "length P = length CAi" using mk_var_dis_jaja by auto
  have res_e: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) \<sigma> E" using ord_resolve_rename by auto
  
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
    res_e: "ord_resolve CAi DA \<tau> E" and
    cc_d_true: "I \<Turnstile>fom mset CAi + {#DA#}"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<sigma>
  assume ground_subst_\<sigma>: "is_ground_subst \<sigma>"
  case (ord_resolve n Ci Aij Ai D)
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
    res_e: "ord_resolve_rename CAi DA \<sigma> E" and
    cc_d_true: "I \<Turnstile>fom (mset CAi) + {#DA#}"
  shows "I \<Turnstile>fo E"
  using res_e proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  then have len: "length P = length CAi" using ord_resolve_rename mk_var_dis_jaja by auto
  have res: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) \<sigma> E" using ord_resolve_rename by -
  have "I \<Turnstile>fom (mset (CAi \<cdot>\<cdot>cl P)) + {#DA \<cdot> \<rho>#}"
    using subst_sound_scl[OF len , of I] subst_sound[of I DA]
    cc_d_true by (simp add: true_fo_cls_mset_def2)
    
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAi \<cdot>\<cdot>cl P" "DA \<cdot> \<rho>" \<sigma> E I, OF res]
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
  assumes resolve: "ord_resolve SSS CAi DA \<sigma> E"
  shows "E \<subseteq># (\<Union>#(mset CAi)) + DA"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
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
  assumes "ord_resolve SSS CAi DA \<sigma> E"
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
  assumes resolve: "ord_resolve (S_M S M) CAi DA \<sigma> E" 
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
    
    "is_ground_subst \<eta>''"
    "is_ground_subst_list \<eta>s''"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve nn Ci Aij Ai D)
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
      
    (* Obtain ground substitutions *)
      
  have "is_ground_cls_list (CAi'' \<cdot>\<cdot>cl \<eta>s'')"
    using CAi''_to_CAi grounding grounding_ground is_ground_cls_list_def by auto 
  then obtain \<eta>s''g where \<eta>s''g_p:
    "is_ground_subst_list \<eta>s''g"
    "length \<eta>s''g = n"
    "\<forall>i<n. \<forall>S. S \<subseteq># CAi'' ! i \<longrightarrow> S \<cdot> \<eta>s'' ! i = S \<cdot> \<eta>s''g ! i"
    using make_ground_subst_list_clauses[of CAi'' \<eta>s''] using n by metis
      
  note n = \<open>length \<eta>s''g = n\<close> n
    
  from \<eta>s''g_p have CAi''_to_CAi: "CAi'' \<cdot>\<cdot>cl \<eta>s''g = CAi" 
    using CAi''_to_CAi using  n by auto
  {
    fix i
    assume a: "i<n"
    then have "(map S CAi'' \<cdot>\<cdot>cl \<eta>s'') ! i = (map (S_M S M) CAi) ! i"
      using SCAi''_to_SMCAi by simp      
    then have "((map S CAi'') \<cdot>\<cdot>cl \<eta>s''g) ! i = (map (S_M S M) CAi) ! i"
      using \<eta>s''g_p S.S_selects_subseteq using a n by auto
  }
  then have SCAi''_to_SMCAi: "(map S CAi'') \<cdot>\<cdot>cl \<eta>s''g = map (S_M S M) CAi"
    using n by auto
      
  
  have "is_ground_cls (DA'' \<cdot> \<eta>'')"
    using DA''_to_DA grounding grounding_ground by auto
  then obtain \<eta>''g where \<eta>''g_p:
    "is_ground_subst \<eta>''g"
    "\<forall>S. S \<subseteq># DA'' \<longrightarrow> S \<cdot> \<eta>'' = S \<cdot> \<eta>''g"
    using DA''_to_DA make_single_ground_subst by metis
      
  have DA''_to_DA: "DA'' \<cdot> \<eta>''g = DA" 
    using DA''_\<eta>''_p \<eta>''g_p by auto
  have SDA''_to_SMDA: "S DA'' \<cdot> \<eta>''g = S_M S M DA" 
    using SDA''_to_SMDA \<eta>''g_p S.S_selects_subseteq by auto
    
  show ?thesis
    using that DA''_in_M DA''_to_DA SDA''_to_SMDA CAi''_in_M CAi''_to_CAi SCAi''_to_SMCAi n 
      \<eta>''g_p \<eta>s''g_p
    by auto
qed
  
  
  
lemma ord_resolve_rename_lifting: 
  fixes CAi
  assumes resolve: "ord_resolve (S_M S M) CAi DA \<sigma> E" 
    and select: "selection S"
    and selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" 
    and grounding: "{DA} \<union> (set CAi) \<subseteq> grounding_of_clss M"
  obtains \<eta>s \<eta> \<eta>2 CAi'' DA'' E'' \<tau> where
    "is_ground_subst \<eta>"
    "is_ground_subst_list \<eta>s"
    "is_ground_subst \<eta>2"
    "ord_resolve_rename S CAi'' DA'' \<tau> E''"
    "CAi'' \<cdot>\<cdot>cl \<eta>s = CAi" "DA'' \<cdot> \<eta> = DA" "E'' \<cdot> \<eta>2 = E" (* In the previous proofs I have CAi and DA on lfs of equality... *)
    "{DA''} \<union> set CAi'' \<subseteq> M"
  using resolve proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
    
  have selection_renaming_list_invariant: "\<And>\<rho>s Ci. length \<rho>s = length Ci \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Ci \<cdot>\<cdot>cl \<rho>s) = (map S Ci) \<cdot>\<cdot>cl \<rho>s"
    apply (rule nth_equalityI)
    using selection_renaming_invariant unfolding is_renaming_list_def apply auto
    done
    
  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>
    
  interpret S: selection S by (rule select)
   
  obtain DA'' \<eta>'' CAi'' \<eta>s'' where ff:
    "length CAi'' = n"
    "length \<eta>s'' = n"
    
    "DA'' \<in> M"
    "DA'' \<cdot> \<eta>'' = DA"
    "S DA'' \<cdot> \<eta>'' = S_M S M DA"
    
    "\<forall>CA \<in> set CAi''. CA \<in> M" (* Could also use subseteq *)
    "CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi"
    "(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi"
    
    "is_ground_subst \<eta>''"
    "is_ground_subst_list \<eta>s''"
    using resolve grounding select ord_resolve_obtain_clauses[of S M CAi DA] n 
      by metis
  
  note n = \<open>length CAi'' = n\<close> \<open>length \<eta>s'' = n\<close> n
      
  have "length (mk_var_dis (DA''#CAi'')) = Suc n"
    using n mk_var_dis_jaja by auto
      
  note n = \<open>length (mk_var_dis (DA''#CAi'')) = Suc n\<close> n
    
  define DA' where "DA' = DA'' \<cdot> hd (mk_var_dis (DA''#CAi''))"
  define CAi' where "CAi' = CAi'' \<cdot>\<cdot>cl tl (mk_var_dis (DA''#CAi''))"
  define \<eta>' where "\<eta>' = (inv_ren (hd (mk_var_dis (DA''#CAi'')))) \<odot> \<eta>''"
  define \<eta>s' where "\<eta>s' = (map inv_ren (tl (mk_var_dis (DA''#CAi'')))) \<odot>s \<eta>s''"
    
  (* Try to reprove below lines nicer. I think maybe even sledgehammer could do that for good reasons. *)
  have "length CAi' = n"
    using ff(1) n unfolding CAi'_def by auto
  have "length \<eta>s' = n"
    using ff(2) n unfolding \<eta>s'_def by auto   
  note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n
  have DA'_DA: "DA' \<cdot> \<eta>' = DA"
    using ff(4) unfolding \<eta>'_def DA'_def using mk_var_dis_jaja n
    by (metis inv_ren_cancel_r length_greater_0_conv list.exhaust_sel list.set_intros(1) subst_cls_comp_subst subst_cls_id_subst zero_less_Suc) 
  have "S DA' \<cdot> \<eta>' = S_M S M DA" 
    using ff(5) using ff(4) unfolding \<eta>'_def DA'_def using mk_var_dis_jaja n
    by (smt inv_ren_cancel_r length_greater_0_conv list.exhaust_sel list.set_intros(1) selection_renaming_invariant subst_cls_comp_subst subst_cls_id_subst zero_less_Suc)
    (* There is also a sledgehammer proof *)
  have CAi'_CAi: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    using ff(7) selection_renaming_list_invariant unfolding CAi'_def \<eta>s'_def using n unfolding is_renaming_list_def
      using mk_var_dis_jaja
      by (metis drdrdrdrdrdrdrdrdrdrdrdr is_renaming_list_def length_greater_0_conv length_tl list.sel(3) list.set_sel(2) subst_cls_lists_comp_substs zero_less_Suc) 
  have "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    using ff(8) unfolding CAi'_def \<eta>s'_def using selection_renaming_list_invariant using n
    by (smt drdrdrdrdrdrdrdrdrdrdrdr inv_ren_is_renaming_list is_renaming_list_def length_greater_0_conv length_map length_tl list.sel(3) list.set_sel(2) mk_var_dis_jaja subst_cls_lists_comp_substs zero_less_Suc)
     (* no isar proof :-0 *) 
      
  have vd: "var_disjoint (DA' # CAi')" unfolding DA'_def CAi'_def
    using mk_var_dis_jaja[of "DA'' # CAi''"]
    by (metis length_greater_0_conv list.exhaust_sel n(3) substitution.subst_cls_lists_Cons substitution_axioms zero_less_Suc)
      
      
  (* Introduce \<eta> *)
  from vd DA'_DA CAi'_CAi have "\<exists>\<eta>. \<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> (\<eta>'#\<eta>s') ! i = S \<cdot> \<eta>" unfolding var_disjoint_def
    using n by auto
  then obtain \<eta> where \<eta>_p: "\<forall>i<Suc n. \<forall>S. S \<subseteq># (DA' # CAi') ! i \<longrightarrow> S \<cdot> (\<eta>'#\<eta>s') ! i = S \<cdot> \<eta>" 
    by auto
      
  have DA'_DA: "DA' \<cdot> \<eta> = DA"
    using DA'_DA \<eta>_p by auto
  have "S DA' \<cdot> \<eta> = S_M S M DA" 
    using \<open>S DA' \<cdot> \<eta>' = S_M S M DA\<close> \<eta>_p S.S_selects_subseteq by auto
      
  from \<eta>_p have "\<forall>i < n. (CAi' ! i) \<cdot> (\<eta>s' ! i) = (CAi'! i) \<cdot> \<eta>"
    using n
    by auto
  then have cai'_\<eta>_fo: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi' \<cdot>cl \<eta>"
    using n by auto
  then have CAi'_\<eta>_fo_CAi: "CAi' \<cdot>cl \<eta> = CAi"
    using CAi'_CAi \<eta>_p n by auto
      
  from \<eta>_p have "\<forall>i<n. (S ((CAi') ! i)) \<cdot> \<eta>s' ! i = (S ((CAi') ! i)) \<cdot> \<eta>" 
    using S.S_selects_subseteq n by auto
  then have cai'_\<eta>_fo_sel: "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = (map S CAi') \<cdot>cl \<eta>"
    using n by auto
  then have SCAi'_\<eta>_fo_SMCAi: "(map S CAi') \<cdot>cl \<eta> = map (S_M S M) CAi"
    using \<open>(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi\<close> by auto
    
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
        using \<open>i < n\<close> \<open>CAi' \<cdot>cl \<eta> = CAi\<close> n by auto
      moreover
      have "poss (Aij ! i) \<subseteq># CAi !i"
        using \<open>i<n\<close> ord_resolve(8) by auto
      ultimately
      obtain NAiji' where nn: "NAiji' \<cdot> \<eta> = poss (Aij ! i) \<and> NAiji' \<subseteq># CAi' ! i"
        using ord_resolve(8) image_mset_of_subset unfolding subst_cls_def by metis
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
      using \<open>CAi' \<cdot>cl \<eta> = CAi\<close> Aij'_Aij ord_resolve(8) using n by auto
      
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
      by (simp add: \<open>map S CAi' \<cdot>cl \<eta> = map (S_M S M) CAi\<close>)
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
    
  have res_e: "ord_resolve S CAi' DA' \<tau> E'" 
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
    
  have res_r_e: "ord_resolve_rename S CAi'' DA'' \<tau> E'"
    using ord_resolve_rename[of "hd (mk_var_dis (DA''#CAi''))" DA'' CAi'' "tl (mk_var_dis (DA''#CAi''))" S]
    res_e unfolding CAi'_def DA'_def by auto
      
  show ?thesis using that[of \<eta>'' \<eta>s'' \<eta>2 CAi'' DA'']
      \<open>is_ground_subst \<eta>''\<close>
      \<open>is_ground_subst_list \<eta>s''\<close>
      \<open>is_ground_subst \<eta>2\<close> 
      res_r_e
      \<open> CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi\<close>
      \<open>DA'' \<cdot> \<eta>'' = DA\<close>
      \<open>E' \<cdot> \<eta>2 = E\<close>      
      
      \<open>DA'' \<in> M\<close>
      \<open>\<forall>CA\<in>set CAi''. CA \<in> M\<close>
    by blast
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

interpretation gd: ground_resolution_with_selection S
  by unfold_locales

(*"grounding_of_clss N0"*)

interpretation src: standard_redundancy_criterion gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S"
  by unfold_locales
(*
find_theorems name: src
thm src.saturated_upto_refute_complete
*)


(* The extension of ordered resolution mentioned in 4.10. Following Uwe's recommendation I make it enormous, 
   i.e. consisting of all satisfiability preserving rules *)
(* A huge extension like Uwe suggested. *)
(* Uwe suggested the set of sound rules, and later the set of consistency preserving rules. 
   But we need the whole set to be consistency preserving, and that does not follow from the rules being consistency preserving.
   It does follow from soundness however, so lets just go with that.
 *)
definition gd_ord_\<Gamma>':: "'a inference set" where 
  "gd_ord_\<Gamma>' = {Infer a b c | a b c. (\<forall>I. I \<Turnstile>m a \<longrightarrow>  I \<Turnstile> b \<longrightarrow> I \<Turnstile> c)}" 

(* This corresponds to the part of 4.10 that claims we are extending resolution *)
lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gd.ord_\<Gamma> \<subseteq> gd_ord_\<Gamma>'"
  unfolding gd_ord_\<Gamma>'_def
  using gd.ord_\<Gamma>_def gd.ord_resolve_sound by fastforce 

lemma nice: "sat_preserving_inference_system gd_ord_\<Gamma>'" (* Altough maybe it would be nice to prove it was a sound_inference_system *)
  unfolding sat_preserving_inference_system_def gd_ord_\<Gamma>'_def
  apply auto
  subgoal for N I
    unfolding inference_system.inferences_from_def
    unfolding infer_from_def
    unfolding true_clss_def
    apply (rule_tac x=I in exI)
    apply auto
    apply (simp add: set_rev_mp true_cls_mset_def) 
    done
  done
    
interpretation src_ext:
  sat_preserving_redundancy_criterion "gd_ord_\<Gamma>'" "src.Rf" "(\<lambda>N. src.Ri N \<union> (gd_ord_\<Gamma>' - gd.ord_\<Gamma>))"
  unfolding sat_preserving_redundancy_criterion_def
  apply(rule conjI)
  using nice apply simp
  by (rule standard_redundancy_criterion_extension[OF gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion])

definition ord_FO_\<Gamma> :: "'a inference set" where
  "ord_FO_\<Gamma> = {Infer CC D E | CC D E Cl \<sigma>. ord_resolve_rename S Cl D \<sigma> E \<and> mset Cl = CC}"

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

inductive subsume_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsume_resolve (D + {#L#}) (C + (D + {#- L#}) \<cdot> \<sigma>) (C + D \<cdot> \<sigma>)"

text {*
@{text O} denotes relation composition in Isabelle, so the formalization uses @{text Q} instead.
*}
  
inductive resolution_prover :: "('a clause set \<times> 'a clause set \<times> 'a clause set) \<Rightarrow> ('a clause set \<times> 'a clause set \<times> 'a clause set) \<Rightarrow> bool" (infix "\<leadsto>" 50)  where
 tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
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
    "N = concls_of (ord_FO_resolution.inferences_between Q C) \<Longrightarrow>
     ({}, P \<union> {C}, Q) \<leadsto> (N, P, Q \<union> {C})"


    
definition limit_state ::
  "('a state) llist \<Rightarrow> 'a state"
where
  "limit_state Sts = (llimit (lmap getN Sts), llimit (lmap getP Sts),
     llimit (lmap getQ Sts))"

definition fair_state_seq where
  "fair_state_seq Sts \<longleftrightarrow> getN (limit_state Sts) = {} \<and> getP (limit_state Sts) = {}"

text {*
The following corresponds to Lemma 4.10:
*}
  
term "gd.ord_resolve"
term rtrancl
term src_derive
term "src_derive S" (* Should this constant really take an S? I don't think so when looking in the book.  *)
  (* The thing is. This deriv is based on Os and std redundancy. BUT what I need for 4.10 is a deriv based on
     an extension of Os and the standard extension of std redundancy wrt the extension of Os. *)
term "src_ext_derive"
  
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
  

lemma subst_subset_mono: "D \<subset># C \<Longrightarrow> D \<cdot> \<sigma> \<subset># C \<cdot> \<sigma>"
  unfolding subst_cls_def
  by (simp add: image_mset_subset_mono) 

fun subst_inf :: "'a inference \<Rightarrow> 's \<Rightarrow> 'a inference" (infixl "\<cdot>i" 67) where
  "(Infer CC C E) \<cdot>i \<sigma> = Infer (CC \<cdot>cm \<sigma>) (C \<cdot> \<sigma>) (E \<cdot> \<sigma>)"
  
lemma ord_FO_\<Gamma>_gd_ord_\<Gamma>': (* I have my doubts about this... *)
  assumes "\<gamma> \<in> ord_FO_\<Gamma>"
  assumes "is_ground_subst \<eta>"
  shows "\<gamma> \<cdot>i \<eta> \<in> gd_ord_\<Gamma>'"
proof -
  from assms obtain CC D E Cl \<sigma> where "\<gamma> = Infer CC D E \<and> ord_resolve_rename S Cl D \<sigma> E \<and> mset Cl = CC" unfolding ord_FO_\<Gamma>_def by auto
  then have "\<forall>I. I \<Turnstile>fom CC + {#D#} \<longrightarrow> I \<Turnstile>fo E" using ord_resolve_rename_sound[of S _ ] by auto
  then have "\<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>m ((CC + {#D#}) \<cdot>cm \<sigma>)) \<longrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile> E \<cdot> \<sigma>)"
    using true_fo_cls.cases
    by (meson true_fo_cls_mset) 
  then show ?thesis
    sorry
qed
  
lemma somethingIneed: (* Probably better than the above... *)
  assumes resolve_ren: "ord_resolve_rename S CAi DA \<sigma> E"
  assumes "\<rho> = hd (mk_var_dis (DA#CAi))"
  assumes "\<rho>s = tl (mk_var_dis (DA#CAi))"
  assumes "is_ground_subst \<eta>"
  shows "\<forall>I. I \<Turnstile>m (mset ((CAi \<cdot>\<cdot>cl \<rho>s) \<cdot>cl \<sigma> \<cdot>cl \<eta>)) \<longrightarrow> I \<Turnstile> (DA \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<eta>) \<longrightarrow> I \<Turnstile> E \<cdot> \<sigma> \<cdot> \<eta>"
using resolve_ren proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> \<rho>s)
  note resolve = \<open>ord_resolve S (CAi \<cdot>\<cdot>cl \<rho>s) (DA \<cdot> \<rho>) \<sigma> E\<close>
  show ?thesis
    using resolve proof (cases rule:ord_resolve.cases)
    case (ord_resolve n Ci Aij Ai D)
    then show ?thesis sorry
  qed
qed

(* Somehow it seems more tempting to show that we can do unordered ground resolution... 
   And then use soundness of that... 
   
*)
    
lemma eee: "(prems_of (\<gamma> \<cdot>i \<mu>)) = ((prems_of \<gamma>) \<cdot>cm \<mu>)"
  apply auto
  apply (induction \<gamma>)
  apply auto
  done
    
    
lemma fff: "set_mset (X \<cdot>cm \<mu>) = (set_mset X)  \<cdot>cs \<mu>"
  by (simp add: subst_cls_mset_def subst_clss_def)
  
    
lemma ggg: "infer_from x y \<Longrightarrow> z \<supseteq> x \<Longrightarrow> infer_from z y"
  by (meson infer_from_def lfp.leq_trans)
  
    

text {*
The following corresponds to Lemma 4.10:
*}
    
lemma resolution_prover_rtc_deriv:
  assumes "St \<leadsto> St'"
  shows "src_ext.derive (grounding_of_state St) (grounding_of_state St')"
using assms proof (induction rule: resolution_prover.induct)
  case (tautology_deletion A C N P Q)
  {
    fix C\<sigma>
    assume "C\<sigma> \<in> grounding_of_cls C"
    then obtain \<sigma> where "C\<sigma> = C \<cdot> \<sigma>"
      unfolding grounding_of_cls_def by auto
    then have "Neg (A \<cdot>a \<sigma>) \<in># C\<sigma> \<and> Pos (A \<cdot>a \<sigma>) \<in># C\<sigma>" 
      using tautology_deletion
      by (metis Melem_subst_cls eql_neg_lit_eql_atm eql_pos_lit_eql_atm) (* seems a bit complicated... *)
    then have "C\<sigma> \<in> src.Rf (grounding_of_state (N, P, Q))"
      using src.tautology_redundant by auto
  }
  then have "grounding_of_state (N \<union> {C}, P, Q) - grounding_of_state (N, P, Q) \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover
  have "grounding_of_state (N, P, Q) - grounding_of_state (N \<union> {C}, P, Q) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case 
    using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      by auto
next
  case (forward_subsumption P Q C N)
  then obtain D where D_p: "D\<in>P \<union> Q \<and> subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def) 
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      unfolding grounding_of_cls_def
      by (smt Collect_mono is_ground_comp_subst subst_cls_comp_subst) 
    have "grounding_of_state (N \<union> {C}, P, Q) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N \<union> {C}, P, Q)"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N \<union> {C}, P, Q)"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed  
    then show ?case 
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"] 
        by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_cls D)"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
        unfolding true_cls_def by blast
      moreover
      have "C \<cdot> \<mu> > D \<cdot> \<sigma> \<cdot> \<mu>"
        using D\<sigma>\<mu>C\<mu>
        by (simp add: subset_imp_less_mset) 
      moreover
      have "D \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls D"
        by (metis (mono_tags, lifting) \<mu>_p is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst substitution_ops.grounding_of_cls_def)        
      ultimately
      have "set_mset {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<subseteq> grounding_of_cls D \<and> (\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>) \<and> (\<forall>D'. D' \<in># {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> D' < C \<cdot> \<mu>)"
        by auto
      then have "C \<cdot> \<mu> \<in> src.Rf (grounding_of_cls D)"
        using src.Rf_def[of "grounding_of_cls D"] by blast
      then show "C\<mu> \<in> src.Rf (grounding_of_cls D)"
        using \<mu>_p by auto
    qed
    moreover 
    have "(grounding_of_cls D) \<subseteq> (grounding_of_state (N, P, Q))"
      using D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "src.Rf (grounding_of_cls D) \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      using src_ext.Rf_mono by auto
    ultimately
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      by auto
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (backward_subsumption_P N C P Q) (* Adapted from previous proof *) (* Arguably I should extract some lemma that says: if subsumed then redundant... *)
   then obtain D where D_p: "D\<in>N \<and> properly_subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding properly_subsumes_def subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def) 
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      unfolding grounding_of_cls_def
      by (smt Collect_mono is_ground_comp_subst subst_cls_comp_subst) 
    have "grounding_of_state (N, P \<union> {C}, Q) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N, P \<union> {C}, Q)"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N, P  \<union> {C}, Q)"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed  
    then show ?case 
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"] 
        by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_cls D)"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
        unfolding true_cls_def by blast
      moreover
      have "C \<cdot> \<mu> > D \<cdot> \<sigma> \<cdot> \<mu>"
        using D\<sigma>\<mu>C\<mu>
        by (simp add: subset_imp_less_mset) 
      moreover
      have "D \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls D"
        by (metis (mono_tags, lifting) \<mu>_p is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst substitution_ops.grounding_of_cls_def)        
      ultimately
      have "set_mset {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<subseteq> grounding_of_cls D \<and> (\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>) \<and> (\<forall>D'. D' \<in># {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> D' < C \<cdot> \<mu>)"
        by auto
      then have "C \<cdot> \<mu> \<in> src.Rf (grounding_of_cls D)"
        using src.Rf_def[of "grounding_of_cls D"] by blast
      then show "C\<mu> \<in> src.Rf (grounding_of_cls D)"
        using \<mu>_p by auto
    qed
    moreover 
    have "(grounding_of_cls D) \<subseteq> (grounding_of_state (N, P, Q))"
      using D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "src.Rf (grounding_of_cls D) \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      using src_ext.Rf_mono by auto
    ultimately
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      by auto
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P \<union> {C}, Q)"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (backward_subsumption_Q N C P Q) (* Adapted from previous proof *)
     then obtain D where D_p: "D\<in>N \<and> properly_subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding properly_subsumes_def subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def) 
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      unfolding grounding_of_cls_def
      by (smt Collect_mono is_ground_comp_subst subst_cls_comp_subst) 
    have "grounding_of_state (N, P, Q \<union> {C}) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N, P, Q \<union> {C})"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N, P, Q  \<union> {C})"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed  
    then show ?case 
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"] 
        by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_cls D)"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
        unfolding true_cls_def by blast
      moreover
      have "C \<cdot> \<mu> > D \<cdot> \<sigma> \<cdot> \<mu>"
        using D\<sigma>\<mu>C\<mu>
        by (simp add: subset_imp_less_mset) 
      moreover
      have "D \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls D"
        by (metis (mono_tags, lifting) \<mu>_p is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst substitution_ops.grounding_of_cls_def)        
      ultimately
      have "set_mset {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<subseteq> grounding_of_cls D \<and> (\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>) \<and> (\<forall>D'. D' \<in># {#D \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> D' < C \<cdot> \<mu>)"
        by auto
      then have "C \<cdot> \<mu> \<in> src.Rf (grounding_of_cls D)"
        using src.Rf_def[of "grounding_of_cls D"] by blast
      then show "C\<mu> \<in> src.Rf (grounding_of_cls D)"
        using \<mu>_p by auto
    qed
    moreover 
    have "(grounding_of_cls D) \<subseteq> (grounding_of_state (N, P, Q))"
      using D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "src.Rf (grounding_of_cls D) \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      using src_ext.Rf_mono by auto
    ultimately
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
      by auto
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q \<union> {C})"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (forward_reduction P Q L \<sigma> C N)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
        
    define \<gamma> where "\<gamma> = Infer {# (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> #} ((C + {#L#})\<cdot> \<mu>) (C \<cdot> \<mu>)"
        
    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N \<union> {C + {#L#}}, P, Q)"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def 
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N \<union> {C + {#L#}}, P, Q)"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus) 
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "(\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>)"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by auto
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N \<union> {C}, P, Q) - grounding_of_state (N \<union> {C + {#L#}}, P, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  { (*This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "\<forall>I. I \<Turnstile> C \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>"
      unfolding true_cls_def by auto
    moreover
    from C\<mu>_CL\<mu> have "(C + {#L#}) \<cdot> \<mu> > C \<cdot> \<mu>"
      by simp
    moreover
    have "C \<cdot> \<mu> \<in> grounding_of_cls C"
      using \<mu>_def substitution_ops.grounding_of_cls_def by auto
    ultimately
    have "set_mset {# C \<cdot> \<mu> #} \<subseteq> grounding_of_cls C \<and> (\<forall>I. I \<Turnstile>m {# C \<cdot> \<mu> #} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>) \<and> (\<forall>D. D \<in># {# C \<cdot> \<mu> #} \<longrightarrow> D < (C + {#L#}) \<cdot> \<mu>)"
      by simp
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_cls C)"
      using src.Rf_def[of "grounding_of_cls C"] by blast
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
      using src_ext.Rf_mono[of "grounding_of_cls C"] unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N \<union> {C + {#L#}}, P, Q) - grounding_of_state (N \<union> {C}, P, Q) \<subseteq> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N \<union> {C}, P, Q)" "grounding_of_state (N \<union> {C + {#L#}}, P, Q)"]
    by auto
next
  case (backward_reduction_P N L \<sigma> C P Q) (* Adapted from previous proof *)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
        
    define \<gamma> where "\<gamma> = Infer {# (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> #} ((C + {#L#})\<cdot> \<mu>) (C \<cdot> \<mu>)"
        
    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N, P \<union> {C + {#L#}}, Q)"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def 
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N, P \<union> {C + {#L#}}, Q)"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus) 
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow>  I \<Turnstile> C \<cdot> \<mu>"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by simp      
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N, P \<union> {C}, Q) - grounding_of_state (N, P \<union> {C + {#L#}}, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  {
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "\<forall>I. I \<Turnstile> C \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>"
      unfolding true_cls_def by auto
    moreover
    from C\<mu>_CL\<mu> have "(C + {#L#}) \<cdot> \<mu> > C \<cdot> \<mu>"
      by simp
    moreover
    have "C \<cdot> \<mu> \<in> grounding_of_cls C"
      using \<mu>_def substitution_ops.grounding_of_cls_def by auto
    ultimately
    have "set_mset {# C \<cdot> \<mu> #} \<subseteq> grounding_of_cls C \<and> (\<forall>I. I \<Turnstile>m {# C \<cdot> \<mu> #} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>) \<and> (\<forall>D. D \<in># {# C \<cdot> \<mu> #} \<longrightarrow> D < (C + {#L#}) \<cdot> \<mu>)"
      by simp
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_cls C)"
      using src.Rf_def[of "grounding_of_cls C"] by blast
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using src_ext.Rf_mono[of "grounding_of_cls C"] unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N, P  \<union> {C + {#L#}}, Q) - grounding_of_state (N, P  \<union> {C}, Q) \<subseteq> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N, P \<union> {C}, Q)" "grounding_of_state (N, P \<union> {C + {#L#}}, Q)"]
    by auto
next
  case (backward_reduction_Q N L \<sigma> C P Q) (* Adapted from previous proof *)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
        
    define \<gamma> where "\<gamma> = Infer {# (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> #} ((C + {#L#})\<cdot> \<mu>) (C \<cdot> \<mu>)"
        
    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N, P, Q \<union> {C + {#L#}})"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def 
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N, P, Q \<union> {C + {#L#}})"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus) 
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}}))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by simp      
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N, P \<union> {C}, Q) - grounding_of_state (N, P, Q \<union> {C + {#L#}}) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  {
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "\<forall>I. I \<Turnstile> C \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>"
      unfolding true_cls_def by auto
    moreover
    from C\<mu>_CL\<mu> have "(C + {#L#}) \<cdot> \<mu> > C \<cdot> \<mu>"
      by simp
    moreover
    have "C \<cdot> \<mu> \<in> grounding_of_cls C"
      using \<mu>_def substitution_ops.grounding_of_cls_def by auto
    ultimately
    have "set_mset {# C \<cdot> \<mu> #} \<subseteq> grounding_of_cls C \<and> (\<forall>I. I \<Turnstile>m {# C \<cdot> \<mu> #} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu>) \<and> (\<forall>D. D \<in># {# C \<cdot> \<mu> #} \<longrightarrow> D < (C + {#L#}) \<cdot> \<mu>)"
      by simp
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_cls C)"
      using src.Rf_def[of "grounding_of_cls C"] by blast
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using src_ext.Rf_mono[of "grounding_of_cls C"] unfolding clss_of_state_def grounding_of_clss_def by auto
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N, P , Q \<union> {C + {#L#}}) - grounding_of_state (N, P  \<union> {C}, Q) \<subseteq> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N, P \<union> {C}, Q)" "grounding_of_state (N, P, Q \<union> {C + {#L#}})"]
    by auto
next
  case (clause_processing N C P Q)
  then show ?case
    unfolding clss_of_state_def  using src_ext.derive.intros by auto
next
  case (inference_computation N Q C P)
  {
    fix E\<mu>
    assume "E\<mu> \<in> grounding_of_clss N"
    then obtain \<mu> E where E_\<mu>_p: "E\<mu> = E \<cdot> \<mu> \<and> E \<in> N \<and> is_ground_subst \<mu>"
      unfolding grounding_of_clss_def grounding_of_cls_def by auto
    then have E_concl: "E \<in> concls_of (ord_FO_resolution.inferences_between Q C)" 
      using inference_computation by auto
    then obtain \<gamma> where \<gamma>_p: "\<gamma> \<in> ord_FO_\<Gamma> \<and> infer_from (Q \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma> \<and> concl_of \<gamma> = E"
      unfolding ord_FO_resolution.inferences_between_def by auto
    have tt: "\<gamma> \<cdot>i \<mu> \<in> gd_ord_\<Gamma>' \<and> infer_from ((Q \<union> {C}) \<cdot>cs \<mu>) (\<gamma> \<cdot>i \<mu>) \<and> concl_of (\<gamma> \<cdot>i \<mu>) = E \<cdot> \<mu>"
      apply (rule conjI)
       defer
       apply (rule conjI)
        prefer 3
      using ord_FO_\<Gamma>_gd_ord_\<Gamma>' \<gamma>_p E_\<mu>_p apply simp
       defer
      using \<gamma>_p
       apply (metis inference.collapse inference.simps(1) subst_inf.simps)
      using \<gamma>_p
      unfolding infer_from_def
      using eee fff
      by (metis subset_Un_eq subst_clss_union)
    have "\<gamma> \<cdot>i \<mu> \<in> gd_ord_\<Gamma>' \<and> infer_from (grounding_of_state ({}, P \<union> {C}, Q)) (\<gamma> \<cdot>i \<mu>) \<and> concl_of (\<gamma> \<cdot>i \<mu>) = E \<cdot> \<mu>"
      apply (rule conjI)
      using tt apply simp
      apply (rule conjI)
      defer
      using tt apply simp
      apply (subgoal_tac "(Q \<union> {C}) \<cdot>cs \<mu> \<subseteq> grounding_of_state ({}, P \<union> {C}, Q)")
      using ggg[of "((Q \<union> {C}) \<cdot>cs \<mu>)" " (\<gamma> \<cdot>i \<mu>) " "grounding_of_state ({}, P \<union> {C}, Q)"] tt
       apply simp
        using E_\<mu>_p
        unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def
        using subst_clss_def by auto
    then have "E \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      unfolding src_ext.inferences_from_def 
      by (metis (no_types, lifting) image_eqI mem_Collect_eq)
        
    then have "E\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      using E_\<mu>_p by auto
  }
  then have "grounding_of_state (N, P, Q \<union> {C}) - grounding_of_state ({}, P \<union> {C}, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover
  have "grounding_of_state ({}, P \<union> {C}, Q) - grounding_of_state (N, P, Q \<union> {C}) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "(grounding_of_state (N, P, Q \<union> {C}))" "(grounding_of_state ({}, P \<union> {C}, Q))"] by auto
qed
  
text {*
Another formulation of the last part of lemma 4.10
 *}
  
lemma derivation_sim:
  assumes "R x y \<Longrightarrow> R' (P x) (P y)"
  assumes "derivation R Sts"
  shows "derivation R' (lmap P Sts)"
    sorry
  
lemma four_ten:
  assumes "derivation op \<leadsto> Sts"
  shows "derivation src_ext.derive (lmap grounding_of_state Sts)"
  sorry
  
text {*
The following corresponds to Lemma 4.11:
*}
  

  
definition is_least :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_least P n \<longleftrightarrow> P n \<and> (\<forall>n' < n. \<not>P n')"
  
lemma least_yesyes: 
  assumes "P n"
  shows "\<exists>n. is_least P n"
    using assms  exists_least_iff unfolding is_least_def by auto
   

lemma in_lSup_in_nth:
  assumes "C \<in> lSup Ns"
  shows "\<exists>j. enat j < llength Ns \<and> C \<in> lnth Ns j"
  using assms unfolding lSup_def by auto
    
lemma lSup_grounding_of_state_ground:
  assumes "C \<in> lSup (lmap grounding_of_state Sts)"
  shows "is_ground_cls C"
proof -
  from assms have "\<exists>j. enat j < llength (lmap grounding_of_state Sts) \<and> (C \<in> (lnth (lmap grounding_of_state Sts) j))"
    using in_lSup_in_nth by metis
  then obtain j where
    "enat j < llength (lmap grounding_of_state Sts)"
    "C \<in> lnth (lmap grounding_of_state Sts) j"
    by blast
  then have "C \<in> grounding_of_state (lnth Sts j)"
    by auto
  then show ?thesis unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def
    by auto
qed
  
lemma llimit_grounding_of_state_ground:
  assumes "C \<in> llimit (lmap grounding_of_state Sts)"
  shows "is_ground_cls C"
proof -
  from assms have "C \<in> lSup (lmap grounding_of_state Sts)" 
    using llimit_subset_lSup[of "lmap grounding_of_state Sts"] by blast
  then show ?thesis using lSup_grounding_of_state_ground by auto
qed 
 
lemma llimit_eventually_always:
  assumes "C \<in> llimit Ns"
  shows "\<exists>i. enat i < llength Ns \<and>(\<forall>j\<ge>i. enat j < llength Ns \<longrightarrow> C \<in> lnth Ns j)"
proof -
  have "\<exists>i. enat i < llength Ns \<and> C \<in> INTER {j. i \<le> j \<and> enat j < llength Ns} (lnth Ns)" using assms unfolding llimit_def by auto
  then show ?thesis
    by auto
qed
 
lemma hmm:
  assumes C_in: "C \<in> lnth (lmap grounding_of_state Sts) i"
  assumes i_p: "enat i < llength (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  from C_in have "C \<in> grounding_of_state (lnth Sts i)" using i_p by auto
  then show ?thesis unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
qed
    
lemma jajajajadxgetN:
  "getN (limit_state Sts) = llimit (lmap getN Sts)"
  unfolding limit_state_def by auto
    
lemma getN_subset:
 assumes "enat l < llength Sts"
 shows "getN (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
  using assms unfolding clss_of_state_def by auto  
    
lemma getP_subset:
 assumes "enat l < llength Sts"
 shows "getP (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
   using assms unfolding clss_of_state_def by auto
  
lemma getQ_subset:
 assumes "enat l < llength Sts"
 shows "getQ (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
  using assms unfolding clss_of_state_def by auto
    
lemma grounding_of_clss_mono: "X \<subseteq> Y \<Longrightarrow> grounding_of_clss X \<subseteq> grounding_of_clss Y"
  unfolding grounding_of_clss_def by auto
    
lemma grounding_of_clss_mono2: "X \<in> Y \<Longrightarrow> grounding_of_cls X \<subseteq> grounding_of_clss Y"
  using grounding_of_clss_def grounding_of_cls_def by auto
  
  
lemma eventually_deleted:
  assumes "D \<in> getN (lnth Sts i)"
  assumes fair: "fair_state_seq Sts"
  assumes i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume "\<nexists>l. D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> getN (lnth Sts l)"
    apply -
    apply auto
    subgoal for ll
      apply (induction ll)
       apply auto
      using assms(1) apply blast
      by (metis Suc_ile_eq assms(1) le_SucE less_imp_le| blast)
    done
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> (lnth (lmap getN Sts) l)"
    by auto
  then have "D \<in> llimit (lmap getN Sts) "
    unfolding llimit_def apply auto
    using i_Sts by blast
  then show False using fair unfolding fair_state_seq_def 
    by (simp add: jajajajadxgetN)
qed
  
lemma fair_imp_limit_minus_Rf_subset_ground_limit_state:
  assumes
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "llimit Ns - src.Rf (llimit Ns) \<subseteq> grounding_of_state (limit_state Sts)"
proof
  let ?Ns = "\<lambda>i. getN (lnth Sts i)"
  let ?Ps = "\<lambda>i. getP (lnth Sts i)"
  let ?Qs = "\<lambda>i. getQ (lnth Sts i)"
  fix C
  assume C_p: "C \<in> llimit Ns - src.Rf (llimit Ns)"
  then have "is_ground_cls C" 
    using ns using llimit_grounding_of_state_ground by auto
  from C_p have no_taut: "\<not>(\<exists>A. Pos A \<in># C \<and> Neg A \<in># C)" 
    using src.tautology_redundant by auto
      
  from deriv have four_ten: "derivation src_ext.derive Ns" 
    using four_ten ns by auto
   
  obtain i where i_p: "enat i < llength Ns \<and> (\<forall>j. j \<ge> i \<longrightarrow> enat j < llength Ns \<longrightarrow> C \<in> lnth Ns j)"
    using C_p llimit_eventually_always by fastforce
  then have "C \<in> lnth Ns i" 
    by auto
  then obtain D \<sigma> where D_p: "D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using i_p unfolding ns using hmm by blast
  then have "D \<in> ?Ns i \<or> D \<in> ?Ps i \<or> D \<in> ?Qs i"
    unfolding clss_of_state_def by auto
  moreover
  {
    assume "D \<in> ?Ns i"
    then have "\<exists>l. D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
      using fair using i_p eventually_deleted[of D Sts i] unfolding ns by auto
    then obtain l where l_p: "D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts" 
      by blast
    then have l_Ns: "enat (Suc l) < llength Ns " unfolding ns by auto
    from l_p have D_in_out: "D \<in> ?Ns l \<and> D \<notin> ?Ns (Suc l)" 
       by auto
    have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
      using deriv l_p using derivation_lnth_rel by auto
    then have "\<exists>l D' \<tau>. l \<ge> i \<and> C = D' \<cdot> \<tau> \<and> D' \<in> (?Ps l \<union> ?Qs l)"
    proof (induction rule: resolution_prover.cases)
      case (tautology_deletion A D_twin N P Q)
      then have "D_twin = D" 
        using D_in_out by auto
      then have "Pos (A \<cdot>a \<sigma>) \<in># C \<and> Neg (A \<cdot>a \<sigma>) \<in># C"
        using tautology_deletion(3,4) D_p
        by (metis Melem_subst_cls eql_neg_lit_eql_atm eql_pos_lit_eql_atm) 
      then have False 
        using no_taut by metis
      then show ?case
        by blast
    next
      case (forward_subsumption P Q D_twin N)
      then have twins: "D_twin = D" "?Ps (Suc l) = P" "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q" 
        using D_in_out by auto
      then obtain \<tau> D' where \<tau>_D'_p: "D' \<cdot> \<tau> \<subseteq># D \<and> D' \<in> P \<union> Q"
        using forward_subsumption unfolding subsumes_def by auto
      then have "D = D' \<cdot> \<tau> \<or> D' \<cdot> \<tau> \<subset># D"
        using subset_mset_def by auto
      then show ?case 
      proof
        assume "D = D' \<cdot> \<tau>"
        then have "D' \<cdot> (\<tau> \<odot> \<sigma>) = C"
          using D_p
          by auto
        then show ?case
          using twins \<tau>_D'_p l_p unfolding is_least_def
            by metis
      next
        assume "D' \<cdot> \<tau> \<subset># D"
        then have "D' \<cdot> \<tau> \<cdot> \<sigma> \<subset># D \<cdot> \<sigma>"
          by (simp add: subst_subset_mono)
        then have D'_C: "D' \<cdot> \<tau> \<cdot> \<sigma> \<subset># C"
          using D_p by auto
        then have "(\<forall>I. I \<Turnstile> D' \<cdot> \<tau> \<cdot> \<sigma> \<longrightarrow> I \<Turnstile> C)"
          by (meson set_mset_mono subset_mset.less_imp_le true_cls_mono)
        moreover
        from D'_C have "C > D' \<cdot> \<tau> \<cdot> \<sigma>"
          by (simp add: subset_imp_less_mset)
        moreover
        have "D' \<cdot> \<tau> \<cdot> \<sigma> \<in> grounding_of_cls D'"
          using D_p unfolding grounding_of_cls_def
          by (metis (mono_tags, lifting) is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst) 
        ultimately
        have "C \<in> src.Rf (grounding_of_cls D')"
          unfolding src.Rf_def 
          apply simp
          apply (rule_tac x="{#D' \<cdot> \<tau> \<cdot> \<sigma>#}" in exI)
            by simp
        then have "C \<in> src.Rf (grounding_of_state (lnth Sts (Suc l)))"
          using \<tau>_D'_p  src.Rf_mono 
          unfolding twins(2)[symmetric] twins(4)[symmetric] 
          using getP_subset[of "Suc l" Sts] getQ_subset[of "Suc l" Sts] l_p grounding_of_clss_mono grounding_of_clss_mono2[of D']
          by (metis Un_iff subset_Un_eq)
        then have "C \<in> src.Rf (lnth Ns (Suc l))"
           using l_p unfolding ns by auto
        then have "C \<in> src.Rf (lSup Ns)" 
          using src.Rf_mono[of "(lnth Ns (Suc l))" "lSup Ns"] l_Ns by (auto simp add: lnth_subset_lSup)
        then have "C \<in> src.Rf (llimit Ns)" using four_ten src_ext.derivation_supremum_llimit_satisfiable(1)[of Ns]
          by auto
        then have "False" 
          using C_p by auto
        then show ?case
          by auto
      qed
    next
      case (backward_subsumption_P N D_twin P Q)
      then show ?case sorry
    next
      case (backward_subsumption_Q N D_twin P Q)
      then show ?case sorry
    next
      case (forward_reduction P Q L \<sigma> D_twin N)
      then show ?case sorry
    next
      case (backward_reduction_P N L \<sigma> D_twin P Q)
      then show ?case sorry
    next
      case (backward_reduction_Q N L \<sigma> D_twin P Q)
      then show ?case sorry
    next
      case (clause_processing N D_twin P Q)
      then show ?case sorry
    next
      case (inference_computation N Q D_twin P)
      then show ?case sorry
    qed
  }
  moreover
  {
    assume "D \<in> ?Ps i"
    have "\<exists>l D' \<tau>. l \<ge> i \<and> C = D' \<cdot> \<tau> \<and> D' \<in> ?Qs i"
      sorry
  }
  moreover
  {
    assume "D \<in> ?Qs i"
    have "\<exists>l D' \<tau>. l \<ge> i \<and> C = D' \<cdot> \<tau> \<and> D' \<in> ?Qs i"
      sorry
  }
  ultimately
  have "\<exists>l D' \<tau>. l \<ge> i \<and> C = D' \<cdot> \<tau> \<and> D' \<in> ?Qs i"
    sorry
      
  show "C \<in> grounding_of_state (limit_state Sts)"
    sorry
qed

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
