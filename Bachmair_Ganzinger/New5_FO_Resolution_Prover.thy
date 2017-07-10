(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull
*)

theory New5_FO_Resolution_Prover 
imports New3_Ordered_Ground_Resolution Standard_Redundancy Substitution Clauses 
begin

(* locale_deps *)

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


lemma ord_resolve_ground_inst_sound: (* This theorem can be used to prove FO soundness. And it will also be used in 4.10. *)
  assumes 
    res_e: "ord_resolve CAi DA \<sigma> E"
  assumes
    cc_inst_true: "I \<Turnstile>m (mset CAi) \<cdot>cm \<sigma> \<cdot>cm \<eta>"
  assumes
    d_inst_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
  assumes ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Ci Aij Ai D)
  have DA: "DA = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have aij_len: "length Aij = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i)" using ord_resolve by -
  have mgu: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
  have len: "length CAi = length Ai" using ai_len cai_len by auto
  have "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  hence cc_true: "I \<Turnstile>m (mset CAi) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and d_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using cc_inst_true d_inst_true by auto

    from mgu have unif: "\<forall>i<n. \<forall>A\<in>#Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>" 
    using mgu_unifier using ai_len aij_len by blast
      
  show "I \<Turnstile> E \<cdot> \<eta>"
  proof (cases "\<forall>A \<in> set Ai. A \<cdot>a \<sigma> \<cdot>a \<eta> \<in> I")
    case True
    hence "\<not> I \<Turnstile> negs (mset Ai) \<cdot> \<sigma> \<cdot> \<eta>"
      unfolding true_cls_def by auto
    hence "I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<eta>"
      using d_true DA by auto
    thus ?thesis
      unfolding e by simp
  next
    case False
    then obtain i where a_in_aa: "i < length CAi" and a_false: "(Ai ! i) \<cdot>a \<sigma> \<cdot>a \<eta> \<notin> I"
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
      then have "B \<cdot>a \<sigma> = (Ai ! i) \<cdot>a \<sigma>" using unif a_in_aa cai_len unfolding BB_def by auto
    }
    hence "\<not> I \<Turnstile> poss BB \<cdot> \<sigma> \<cdot> \<eta>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C' + poss BB) \<cdot> \<sigma> \<cdot> \<eta>"
      using c_in_cc cc_true unfolding true_cls_mset_def by force
    ultimately have "I \<Turnstile> C' \<cdot> \<sigma> \<cdot> \<eta>"
      by simp
    thus ?thesis
      unfolding e subst_cls_union using c_cf'
      using true_cls_mono subst_cls_mono
      by (metis (no_types, lifting) C'_def a_in_aa cai_len ci_len mset_subset_eq_add_left nth_mem_mset set_mset_mono sum_mset.remove)
  qed
qed
  
lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAi DA \<sigma> E" and
    cc_d_true: "I \<Turnstile>fom mset CAi + {#DA#}"
  shows "I \<Turnstile>fo E"
  apply (rule true_fo_cls) using assms proof (cases rule: ord_resolve.cases)
  fix \<eta>
  assume ground_subst_\<eta>: "is_ground_subst \<eta>"
  case (ord_resolve n Ci Aij Ai D)
  have DA: "DA = D + negs (mset Ai)" using ord_resolve by -
  have e: "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have aij_len: "length Aij = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have cai: "\<forall>i<n. CAi ! i = Ci ! i + poss (Aij ! i)" using ord_resolve by -
  have mgu: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))" using ord_resolve by -
  have len: "length CAi = length Ai" using ai_len cai_len by auto
  have "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  hence cc_true: "I \<Turnstile>m (mset CAi) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and d_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using true_fo_cls_mset_inst[OF cc_d_true, of "\<sigma> \<odot> \<eta>"] by auto 
  show "I \<Turnstile> E \<cdot> \<eta>" using ord_resolve_ground_inst_sound[OF res_e cc_true d_true ] using ground_subst_\<eta> by auto
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

lemma ord_resolve_rename_ground_inst_sound: (* This theorem will be used in 4.11. *)
  assumes
    res_e: "ord_resolve_rename CAi DA \<sigma> E"
  assumes
    \<rho>s: "\<rho>s = tl (mk_var_dis (DA # CAi))"
  assumes
    \<rho>: "\<rho> = hd (mk_var_dis (DA # CAi))"
  assumes
    cc_inst_true: "I \<Turnstile>m (mset (CAi \<cdot>\<cdot>cl \<rho>s)) \<cdot>cm \<sigma> \<cdot>cm \<eta>"
  assumes
    d_inst_true: "I \<Turnstile> DA \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<eta>"
  assumes ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho>_twin \<rho>s_twin)
  then show ?thesis
    using ord_resolve_ground_inst_sound[of _ _ \<sigma> E I \<eta>] \<rho>s \<rho> cc_inst_true d_inst_true ground_subst_\<eta> by simp
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
  then have "n \<noteq> 0" "length Ci = n" "length Aij = n" "length Ai = n" using ord_resolve by force+
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
        using \<open>i < n\<close> \<open>CAi' \<cdot>cl \<eta> = CAi\<close> n by force
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


interpretation gd_unord: ground_resolution_without_selection
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

thm ord_resolve_rename_lifting

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

inductive subsume_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where (* This is never used. *)
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


(* I could also prove that state is a distributive lattice and define sup_state directly as lSup *)
definition sup_state :: 
  "('a state) llist \<Rightarrow> 'a state"
where
  "sup_state Sts = (lSup (lmap getN Sts), lSup (lmap getP Sts),
     lSup (lmap getQ Sts))"

(*
definition limit_N :: "('a state) llist \<Rightarrow> 'a clause set" where 
  "limit_N Sts = llimit (lmap getN Sts)"

definition limit_P :: "('a state) llist \<Rightarrow> 'a clause set" where 
  "limit_P Sts = llimit (lmap getP Sts)"

definition limit_Q :: "('a state) llist \<Rightarrow> 'a clause set" where 
  "limit_Q Sts = llimit (lmap getQ Sts)"
*)
    
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
  
thm ord_resolve_rename_ground_inst_sound
    
lemma prems_of_subst_inf_subst_cls_mset: "(prems_of (\<gamma> \<cdot>i \<mu>)) = ((prems_of \<gamma>) \<cdot>cm \<mu>)"
  apply auto
  apply (induction \<gamma>)
  apply auto
  done
    
    
lemma set_mset_subst_cls_mset_subst_clss: "set_mset (X \<cdot>cm \<mu>) = (set_mset X)  \<cdot>cs \<mu>"
  by (simp add: subst_cls_mset_def subst_clss_def)
  
    
lemma infer_from_superset: "infer_from x y \<Longrightarrow> z \<supseteq> x \<Longrightarrow> infer_from z y"
  by (meson infer_from_def lfp.leq_trans)
  
lemma strict_subsumption_redundant_clause:
  assumes "D \<cdot> \<sigma> \<subset># C"
  assumes "is_ground_subst \<sigma>"
  shows "C \<in> src.Rf (grounding_of_cls D)"
proof -
  from assms(1) have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<longrightarrow> I \<Turnstile> C"
    unfolding true_cls_def by blast
  moreover
  have "C > D \<cdot> \<sigma>"
    using assms(1)
    by (simp add: subset_imp_less_mset) 
  moreover
  have "D \<cdot> \<sigma> \<in> grounding_of_cls D"
    by (metis (mono_tags, lifting) assms(2) mem_Collect_eq substitution_ops.grounding_of_cls_def)        
  ultimately
  have "set_mset {#D \<cdot> \<sigma>#} \<subseteq> grounding_of_cls D \<and> (\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma>#} \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D'. D' \<in># {#D \<cdot> \<sigma>#} \<longrightarrow> D' < C)"
    by auto
  then have "C \<in> src.Rf (grounding_of_cls D)"
    using src.Rf_def[of "grounding_of_cls D"] by blast
  then show "C \<in> src.Rf (grounding_of_cls D)"
    by auto
qed

lemma strict_subsumption_redundant_state:
  assumes "D \<cdot> \<sigma> \<subset># C"
  assumes "is_ground_subst \<sigma>"
  assumes "D \<in> clss_of_state St"
  shows "C \<in> src.Rf (grounding_of_state St)"
proof -
  from assms have "C \<in> src.Rf (grounding_of_cls D)"
    using strict_subsumption_redundant_clause by auto
  then show "C \<in> src.Rf (grounding_of_state St)"
    using assms(3) unfolding clss_of_state_def grounding_of_clss_def using src.Rf_mono 
    apply (induction St)
    apply auto
      apply (metis SUP_absorb contra_subsetD le_sup_iff order_refl)+
    done
qed

lemma grounding_of_clss_mono:
  assumes "X \<subseteq> Y"
  shows "grounding_of_clss X \<subseteq> grounding_of_clss Y"
  using assms
  using grounding_of_clss_def by auto

text {*
The following corresponds to Lemma 4.10:
*}

lemma subsubsubsubxx: "(mset Cl) \<cdot>cm \<sigma> = mset (Cl  \<cdot>cl \<sigma>)"
  unfolding subst_cls_mset_def subst_cls_list_def by auto
     
lemma resolution_prover_ground_derive:
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
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
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
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
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
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
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
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N \<union> {C}, P, Q)"] \<mu>_def unfolding clss_of_state_def by force
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
  { (*This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P\<union> {C}, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N, P \<union> {C}, Q)"] \<mu>_def unfolding clss_of_state_def by force
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
  { (*This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P\<union> {C}, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N, P \<union> {C}, Q)"] \<mu>_def unfolding clss_of_state_def by force
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
    unfolding clss_of_state_def using src_ext.derive.intros by auto
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
    then obtain CC D Cl \<sigma> where \<gamma>_p2: "\<gamma> = Infer CC D E \<and> ord_resolve_rename S Cl D \<sigma> E \<and> mset Cl = CC" 
      unfolding ord_FO_\<Gamma>_def by auto
    define \<rho> where "\<rho> = hd (mk_var_dis (D # Cl))"
    define \<rho>s where "\<rho>s = tl (mk_var_dis (D # Cl))"
    define \<gamma>_ground where "\<gamma>_ground = Infer (mset (Cl \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu>) (D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu>) (E \<cdot> \<mu>)"
    have "\<forall>I. I \<Turnstile>m mset (Cl \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> E \<cdot> \<mu>"
      using ord_resolve_rename_ground_inst_sound[of S Cl D \<sigma> E _ _ _ \<mu>] \<rho>_def \<rho>s_def E_\<mu>_p \<gamma>_p2 by auto
    then have "\<gamma>_ground \<in> {Infer a b c |a b c. \<forall>I. I \<Turnstile>m a \<longrightarrow> I \<Turnstile> b \<longrightarrow> I \<Turnstile> c}"
      unfolding \<gamma>_ground_def by auto
    moreover
    have "set_mset (prems_of \<gamma>_ground) \<subseteq> grounding_of_state ({}, P \<union> {C}, Q)"
      unfolding \<gamma>_ground_def using E_\<mu>_p \<gamma>_p2 \<gamma>_p unfolding infer_from_def
      unfolding clss_of_state_def grounding_of_clss_def
      apply simp
      apply (rule conjI)
      unfolding grounding_of_cls_def
       apply simp
       apply (subgoal_tac "(C = D \<or> C \<in># CC)")
        prefer 2
        apply simp
       apply (cases "C = D")
        apply (rule disjI1)
        apply (rule_tac x="\<rho> \<odot> \<sigma> \<odot> \<mu>" in exI)
        apply (rule conjI)
         apply (auto;fail)
        apply (auto;fail)
       apply (subgoal_tac "C \<in># CC")
        prefer 2
        apply (auto;fail)
       apply (rule disjI2)
       apply (rule disjI2)
       apply (subgoal_tac "D \<in> Q")
        prefer 2
        apply (auto;fail)
       apply (rule_tac x=D in bexI)
        prefer 2
        apply (auto;fail)
       apply (rule_tac x="\<rho> \<odot> \<sigma> \<odot> \<mu>" in exI)
       apply (auto;fail)
      apply (subgoal_tac "set_mset (mset (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>)) \<subseteq> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
      using subsubsubsubxx apply auto[]
      apply (subgoal_tac "\<forall>x \<in># (mset (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>)). x \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
      subgoal
        apply (auto;fail)
        done
      apply (subgoal_tac "\<forall>i < length (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>). ((Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i) \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
      subgoal
        apply (metis (no_types, lifting) in_set_conv_nth set_mset_mset)
        done
      apply rule
      apply rule
      subgoal for i
        apply simp
        apply (subgoal_tac "Cl ! i \<in> {C} \<union> Q")
         apply (cases "Cl ! i = C")
          apply (rule disjI1)
          apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
          apply (rule conjI)
           apply (subgoal_tac "length \<rho>s = length Cl")
        subgoal
          apply (auto;fail)
          done
           defer
           apply (auto;fail)
          apply (subgoal_tac "Cl ! i \<in> Q")
           prefer 2
        subgoal
          apply (auto;fail)
          done
          apply (rule disjI2)
          apply (rule disjI2)
          apply (rule_tac x="Cl ! i " in bexI)
           prefer 2
           apply auto[]
          apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
          apply (rule conjI)
           apply (subgoal_tac "length \<rho>s = length Cl")
        subgoal
          apply (auto;fail)
          done
           defer
           apply (auto;fail)
          apply (metis UnI1 UnI2 insertE nth_mem_mset singletonI subsetCE)
        using \<rho>s_def using mk_var_dis_jaja apply auto
        done
      done
    ultimately
    have "E \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      unfolding src_ext.inferences_from_def inference_system.inferences_from_def gd_ord_\<Gamma>'_def infer_from_def
      using \<gamma>_ground_def
      by (smt image_iff inference.sel(3) mem_Collect_eq)
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

lemma derivation_derivation_lmap: (* move this theorem *)
  assumes "\<forall>x y. R x y \<longrightarrow> T (G x) (G y)"
  assumes "derivation R Sts"
  shows "derivation T (lmap G Sts)"
  using assms proof (coinduction arbitrary: Sts)
  case derivation
  then have "(\<exists>N. Sts = LCons N LNil) \<or> (\<exists>Ns M. Sts = LCons M Ns \<and> derivation R Ns \<and> R M (lhd Ns))" 
    using derivation.simps[of R Sts] by auto
  then show ?case
  proof 
    assume "\<exists>N. Sts = LCons N LNil"
    then have "\<exists>N. lmap G Sts = LCons N LNil"
      by auto
    then show "(\<exists>N. lmap G Sts = LCons N LNil) \<or> (\<exists>Ns M. lmap G Sts = LCons M Ns \<and> ((\<exists>Sts. Ns = lmap G Sts \<and> (\<forall>x y. R x y \<longrightarrow> T (G x) (G y)) \<and> derivation R Sts) \<or> derivation T Ns) \<and> T M (lhd Ns))"
      by auto
  next
    assume "\<exists>Ns M. Sts = LCons M Ns \<and> derivation R Ns \<and> R M (lhd Ns)"
    then have "\<exists>Ns M. lmap G Sts = LCons M Ns \<and> ((\<exists>Sts. Ns = lmap G Sts \<and> (\<forall>x y. R x y \<longrightarrow> T (G x) (G y)) \<and> derivation R Sts) \<or> derivation T Ns) \<and> T M (lhd Ns)"
      using derivation
      by (metis (no_types, lifting) lhd_LCons llist.distinct(1) llist.exhaust_sel llist.map_sel(1) lmap_eq_LNil lnull_derivation ltl_lmap ltl_simps(2)) 
    then show "(\<exists>N. lmap G Sts = LCons N LNil) \<or> (\<exists>Ns M. lmap G Sts = LCons M Ns \<and> ((\<exists>Sts. Ns = lmap G Sts \<and> (\<forall>x y. R x y \<longrightarrow> T (G x) (G y)) \<and> derivation R Sts) \<or> derivation T Ns) \<and> T M (lhd Ns))"
      by auto
  qed
qed

lemma resolution_prover_ground_derivation:
  assumes "derivation op \<leadsto> Sts"
  shows "derivation src_ext.derive (lmap grounding_of_state Sts)"
  using assms resolution_prover_ground_derive derivation_derivation_lmap[of "op \<leadsto>"] by metis
  
text {*
The following is used prove to Lemma 4.11:
*}
  
definition is_least :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_least P n \<longleftrightarrow> P n \<and> (\<forall>n' < n. \<not>P n')"
  
lemma least_exists: 
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
 
lemma in_lnth_grounding_in_lnth:
  assumes C_in: "C \<in> lnth (lmap grounding_of_state Sts) i"
  assumes i_p: "enat i < llength (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  from C_in have "C \<in> grounding_of_state (lnth Sts i)" using i_p by auto
  then show ?thesis unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
qed

lemma in_lSup_in_sup_state:
  assumes "C \<in> lSup (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  from assms obtain i where i_p: "enat i < llength Sts \<and> C \<in> lnth (lmap grounding_of_state Sts) i"
    using in_lSup_in_nth by fastforce
  then obtain D \<sigma> where "D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using in_lnth_grounding_in_lnth by force
  then have "D \<in> clss_of_state (sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using i_p unfolding sup_state_def clss_of_state_def
    by (metis (no_types, lifting) UnCI UnE contra_subsetD getN.simps getP.simps getQ.simps llength_lmap lnth_lmap lnth_subset_lSup)
  then show ?thesis by auto
qed
    
lemma getN_limit_state_llimit_getN:
  "getN (limit_state Sts) = llimit (lmap getN Sts)"
  unfolding limit_state_def by auto

lemma getP_limit_state_llimit_getP:
  "getP (limit_state Sts) = llimit (lmap getP Sts)"
  unfolding limit_state_def by auto

lemma getQ_limit_state_llimit_getQ:
  "getQ (limit_state Sts) = llimit (lmap getQ Sts)"
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
      by (metis Suc_ile_eq assms(1) le_SucE less_imp_le)
    done
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> (lnth (lmap getN Sts) l)"
    by auto
  then have "D \<in> llimit (lmap getN Sts) "
    unfolding llimit_def apply auto
    using i_Sts by blast
  then show False using fair unfolding fair_state_seq_def 
    by (simp add: getN_limit_state_llimit_getN)
qed

lemma eventually_deleted_P:
  assumes "D \<in> getP (lnth Sts i)"
  assumes fair: "fair_state_seq Sts"
  assumes i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> getP (lnth Sts l) \<and> D \<notin> getP (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume "\<nexists>l. D \<in> getP (lnth Sts l) \<and> D \<notin> getP (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> getP (lnth Sts l)"
    apply -
    apply auto
    subgoal for ll
      apply (induction ll)
       apply auto
      using assms(1) apply blast
      by (metis Suc_ile_eq assms(1) le_SucE less_imp_le)
    done
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> (lnth (lmap getP Sts) l)"
    by auto
  then have "D \<in> llimit (lmap getP Sts) "
    unfolding llimit_def apply auto
    using i_Sts by blast
  then show False using fair unfolding fair_state_seq_def 
    by (simp add: getP_limit_state_llimit_getP)
qed

lemma size_subst: "size (D \<cdot> \<sigma>) = size D"
  unfolding subst_cls_def by auto

lemma subset_subst_properly_subsumes:
  assumes "C \<cdot> \<eta> \<subset># D"
  shows "properly_subsumes C D"
proof -
  have "\<nexists>\<sigma>. D \<cdot> \<sigma> \<subseteq># C"
  proof 
    assume "\<exists>\<sigma>. D \<cdot> \<sigma> \<subseteq># C"
    then obtain \<sigma> where "D \<cdot> \<sigma> \<subseteq># C"
      by blast
    then have "size (D \<cdot> \<sigma>) \<le> size C"
      by (simp add: mset_subseteq_size)
    then have "size D \<le> size C"
      using size_subst by auto
    moreover
    from assms have "size (C \<cdot> \<eta>) < size D"
      by (simp add: mset_subset_size)
    then have "size C < size D"
      using size_subst by auto
    ultimately
    show False 
      by auto
  qed
  moreover
  from assms have "C \<cdot> \<eta> \<subseteq># D"
    by auto
  ultimately
  show ?thesis
    unfolding properly_subsumes_def subsumes_def by auto
qed

lemma subsumes_trans:
  assumes "subsumes C D"
  assumes "subsumes D E"
  shows "subsumes C E"
  using assms unfolding subsumes_def
  by (metis subset_mset.dual_order.trans subst_cls_comp_subst subst_cls_mono_mset)

lemma proper_subsumes_trans:
  assumes "properly_subsumes C D"
  assumes "properly_subsumes D E"
  shows "properly_subsumes C E"
  using assms properly_subsumes_def subsumes_trans by blast


lemma subset_properly_subsumes:
  assumes "C \<subset># D"
  shows "properly_subsumes C D"
  using assms subset_subst_properly_subsumes[of C id_subst] by auto

lemma proper_neq:
  assumes "properly_subsumes D' D"
  shows "D' \<noteq> D \<cdot> \<sigma>"
proof
  assume "D'=D \<cdot> \<sigma>"
  then have "D \<cdot> (\<sigma> \<odot> id_subst) \<subseteq># D'"
    by auto
  then show False 
    using assms  unfolding properly_subsumes_def unfolding subsumes_def by metis
qed


lemma least_exists':
  assumes "N \<noteq> {}"
  shows "\<exists>(m :: nat) \<in> N. (\<forall>n \<in> N. m \<le> n)"
proof -
  obtain y where "y \<in> N"
    using assms by auto
  then obtain m where m_p: "m \<in> N \<and> (\<forall>n'<m. n' \<notin> N)" using least_exists[of "\<lambda>x. x \<in> N" y] unfolding is_least_def by auto
  then have "\<forall>n'. n' < m \<longrightarrow> n' \<notin> N" by auto
  then have "\<forall>n'. n' \<in> N \<longrightarrow> \<not> n' <  m"
    by metis
  then have "\<forall>n'. n' \<in> N \<longrightarrow>  n' \<ge>  m"
    by auto
  then show ?thesis
    using m_p by auto
qed

lemma aa_lemma:
  fixes f :: "nat \<Rightarrow> nat"
  assumes leq: "\<forall>i. f (Suc i) \<le> f i"
  shows "\<exists>l. \<forall>l'\<ge>l. f l' = f (Suc l')"
proof (rule ccontr)
  assume "\<nexists>l. \<forall>l'\<ge>l. f l' = f (Suc l')"
  then have ll': "\<forall>l. \<exists>l'\<ge> l. f l' \<noteq> f (Suc l')"
    by metis
  have "\<forall>l. \<exists>l'\<ge> l. f l' > f (Suc l')"
  proof 
    fix l
    obtain l' where l'_p: "l'\<ge> l \<and> f l' \<noteq> f (Suc l')"
      using ll' by auto
    moreover
    have "f (Suc l') \<le> f l'"
      using leq by auto
    ultimately
    have "f l' > f (Suc l')"
      by auto
    then show "\<exists>l'\<ge> l. f l' > f (Suc l')"
      using l'_p by metis
  qed
  then have iii: "\<forall>l. \<exists>l'>l. f l' < f l"
    sorry
  obtain m where m_p: "m \<in> range f \<and> (\<forall>n \<in> range f. m \<le> n)"
    using least_exists'[of "range f"] by auto
  then obtain i where i_p: "f i = m"
    by auto
  then obtain j where "j > i \<and> f j < f i"
    using iii by blast
  then show False
    using m_p i_p
    by (simp add: leD) 
qed

lemma properly_subsumes_well_founded:
  shows True
  sorry

lemma properly_subsumes_has_minimum:
  assumes "CC \<noteq> {}"
  shows "\<exists>C \<in> CC. \<forall>D \<in> CC. \<not>properly_subsumes D C"
proof (rule ccontr)
  assume "\<not>(\<exists>C\<in>CC. \<forall>D\<in>CC. \<not> properly_subsumes D C)"
  then have "\<forall>C\<in>CC. \<exists>D\<in>CC. properly_subsumes D C"
    by blast
  then obtain f where f_p: "\<forall>C \<in> CC. f C \<in> CC \<and> properly_subsumes (f C) C"
    by metis
  from assms obtain C where C_p: "C \<in> CC"
    by auto
  define c where "c = (\<lambda>n. compow n f C)"
  have incc: "\<forall>i. c i \<in> CC"
    apply rule
    subgoal for i
      apply (induction i)
      unfolding c_def
      using f_p C_p
       apply auto
      done
    done
  have ps: "\<forall>i. properly_subsumes (c (Suc i)) (c i)"
    using incc
    unfolding c_def
    using f_p 
    by auto

  have "\<forall>i. size (c i) \<ge> size (c (Suc i))"
    using ps unfolding properly_subsumes_def subsumes_def
    by (metis mset_subseteq_size size_subst)
  then have lte: "\<forall>i. (size o c) i \<ge> (size o c) (Suc i)"
    unfolding comp_def .
  then have "\<exists>l. \<forall>l' \<ge> l. (size o c) l' = (size o c) (Suc l')"
    using aa_lemma by auto (* make a lemma *)
  then have "\<exists>l. \<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    unfolding comp_def by auto
  then obtain l where l_p: "\<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    by metis
  have "\<forall>l' \<ge> l. \<exists>\<sigma>. (c l') = (c (Suc l')) \<cdot> \<sigma>"
  proof (rule, rule)
    fix l'
    assume "l' \<ge> l"
    then have siz: "size (c l') = size (c (Suc l'))"
      using l_p by metis
    have "properly_subsumes (c (Suc l')) (c l')"
      using ps by auto
    then have "subsumes (c (Suc l')) (c l')"
      unfolding properly_subsumes_def by auto
    then obtain \<sigma> where "c (Suc l') \<cdot> \<sigma> \<subseteq># c l'" unfolding subsumes_def by auto
    then have "c (Suc l') \<cdot> \<sigma> = c l'"
      using siz sorry
    then show "\<exists>\<sigma>. c l' = c (Suc l') \<cdot> \<sigma>"
      by metis
  qed
  moreover
  have "\<forall>l' \<ge> l. \<not>(\<exists>\<sigma>. (c l')  \<cdot> \<sigma> = (c (Suc l')))"
  proof (rule, rule)
    fix l'
    assume "l' \<ge> l"
    then have siz: "size (c l') = size (c (Suc l'))"
      using l_p by metis
    have "properly_subsumes (c (Suc l')) (c l')"
      using ps by auto
    then have "\<not> subsumes (c l') (c (Suc l'))"
      unfolding properly_subsumes_def by auto
    then have "\<nexists>\<sigma>. c l' \<cdot> \<sigma> \<subseteq># c (Suc l')"
      unfolding subsumes_def by auto
    then show "\<nexists>\<sigma>. c l' \<cdot> \<sigma> = c (Suc l')"
      by (metis subset_mset.dual_order.refl)
  qed  
  ultimately
  show False (* We have an infinite chain of proper generalizing clauses. That is impossible since proper generalization is well founded. *)
    sorry
qed

lemma from_Q_to_Q_inf:
  assumes 
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and

    c: "C \<in> llimit Ns - src.Rf (llimit Ns)" and
    d: "D \<in> getQ (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D"
  shows "D \<in> getQ (limit_state Sts)"
proof -
  let ?Ns = "\<lambda>i. getN (lnth Sts i)"
  let ?Ps = "\<lambda>i. getP (lnth Sts i)"
  let ?Qs = "\<lambda>i. getQ (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using llimit_grounding_of_state_ground ns by auto 

  have derivns: "derivation src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C" 
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C
        by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl) 
      ultimately
      have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover
      have "is_ground_subst \<tau>" using \<tau>_p by auto
      moreover 
      have "D \<in> clss_of_state (lnth Sts i)" 
        using d getQ_subset by auto
      ultimately
      have "C \<in> src.Rf (grounding_of_state (lnth Sts i))" 
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"]
        by auto
      then have "C \<in> src.Rf (Lazy_List_Limit.lSup Ns)" 
        using d ns
        by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_lSup src.Rf_mono) 
      then have "C \<in> src.Rf (llimit Ns)" 
        unfolding ns using local.src_ext.Rf_lSup_subset_Rf_llimit derivns ns by auto
      then show False using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>" 
      using ground_C
      by (metis make_single_ground_subst subset_mset.order_refl) 
    then show ?thesis by auto
  qed
  then obtain \<sigma> where \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from deriv have four_ten: "derivation src_ext.derive Ns" 
    using resolution_prover_ground_derivation ns by auto

  have in_Sts_in_Sts_Suc: 
    "\<forall>l \<ge> i. enat (Suc l) < llength Sts \<longrightarrow> D \<in> getQ (lnth Sts l) \<longrightarrow> D \<in> getQ (lnth Sts (Suc l))"
  proof (rule, rule, rule, rule)
    fix l 
    assume len: "i \<le> l" 
    assume llen: "enat (Suc l) < llength Sts"
    assume d_in_q: "D \<in> getQ (lnth Sts l)"
    have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
      using llen deriv
      using derivation_lnth_rel by blast 
    then show "D \<in> getQ (lnth Sts (Suc l))"
    proof (induction rule: resolution_prover.cases)
      case (tautology_deletion A C N P Q)
      then show ?case using d_in_q by auto
    next
      case (forward_subsumption P Q C N)
      then show ?case using d_in_q by auto
    next
      case (backward_subsumption_P N C P Q)
      then show ?case using d_in_q by auto
    next
      case (backward_subsumption_Q N D_removed P Q)
      moreover
      {
        assume "D_removed = D"
        then obtain D_subsumes where D_subsumes_p: "D_subsumes \<in> N \<and> properly_subsumes D_subsumes D" 
          using backward_subsumption_Q by auto
        moreover
        from D_subsumes_p have "subsumes D_subsumes C"
          using d subsumes_trans unfolding properly_subsumes_def by auto
        moreover
        from backward_subsumption_Q have "D_subsumes \<in> clss_of_state (sup_state Sts)"
          using D_subsumes_p llen
          by (metis (no_types, lifting) UnI1 clss_of_state_def getN.simps llength_lmap lnth_lmap lnth_subset_lSup rev_subsetD sup_state_def) 
        ultimately 
        have False
          using d_least unfolding subsumes_def by auto
      }
      ultimately
      show ?case 
        using d_in_q by auto
    next
      case (forward_reduction P Q L \<sigma> C N)
      then show ?case using d_in_q by auto
    next
      case (backward_reduction_P N L \<sigma> C P Q)
      then show ?case using d_in_q by auto
    next
      case (backward_reduction_Q N L \<sigma> D' P Q)
      {
        assume "D' + {#L#} = D"
        then have D'_p: "properly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
          using subset_properly_subsumes[of D' D] backward_reduction_Q by auto
        then have subc: "subsumes D' C"
          using d(3) subsumes_trans unfolding properly_subsumes_def by auto
        from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
          using llen
          by (metis (no_types, lifting) UnI1 clss_of_state_def getP.simps llength_lmap lnth_lmap lnth_subset_lSup subsetCE sup_ge2 sup_state_def)
        then have False using d_least D'_p subc by auto
      }
      then show ?case
        using backward_reduction_Q d_in_q by auto
    next
      case (clause_processing N C P Q)
      then show ?case using d_in_q by auto
    next
      case (inference_computation N Q C P)
      then show ?case using d_in_q by auto
    qed
  qed
  have D_in_Sts: "D \<in> getQ (lnth Sts l)" and D_in_Sts_Suc: "D \<in> getQ (lnth Sts (Suc l))"
    if l_i: \<open>l \<ge> i\<close> and enat: \<open>enat (Suc l) < llength Sts\<close>
    for l
  proof -
    show \<open>D \<in> getQ (lnth Sts l)\<close>
      using that
      apply (induction "l-i" arbitrary: l)
      subgoal using d by auto
      subgoal using d(1) in_Sts_in_Sts_Suc
        by (metis (no_types, lifting) Suc_ile_eq add_Suc_right add_diff_cancel_left' le_SucE
            le_Suc_ex less_imp_le)
      done
    then show "D \<in> getQ (lnth Sts (Suc l))"
      using that in_Sts_in_Sts_Suc by blast
  qed
  have "i \<le> x \<Longrightarrow> enat x < llength Sts \<Longrightarrow> D \<in> getQ (lnth Sts x)" for x
    apply (cases x)
    subgoal using d(1) by (auto intro!: exI[of _ i] simp: less_Suc_eq)
    subgoal for x'
      using d(1) D_in_Sts_Suc[of x'] by (cases \<open>i \<le> x'\<close>) (auto simp: not_less_eq_eq)
    done
  then have "D \<in> llimit (lmap getQ Sts)"
    unfolding llimit_def
    by (auto intro!: exI[of _ i] simp: d)
  then show ?thesis  
    unfolding limit_state_def by auto
qed

    
lemma from_P_to_Q:
  assumes 
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and

    c: "C \<in> llimit Ns - src.Rf (llimit Ns)" and
    d: "D \<in> getP (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D"
  shows "\<exists>l. D \<in> getQ (lnth Sts l) \<and> enat l < llength Sts"
proof -
  let ?Ns = "\<lambda>i. getN (lnth Sts i)"
  let ?Ps = "\<lambda>i. getP (lnth Sts i)"
  let ?Qs = "\<lambda>i. getQ (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using llimit_grounding_of_state_ground ns by auto 

  have derivns: "derivation src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C" 
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C
        by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl) 
      ultimately
      have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover
      have "is_ground_subst \<tau>" using \<tau>_p by auto
      moreover 
      have "D \<in> clss_of_state (lnth Sts i)" 
        using d getP_subset by auto
      ultimately
      have "C \<in> src.Rf (grounding_of_state (lnth Sts i))" 
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"]
        by auto
      then have "C \<in> src.Rf (Lazy_List_Limit.lSup Ns)" 
        using d ns
        by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_lSup src.Rf_mono) 
      then have "C \<in> src.Rf (llimit Ns)" 
        unfolding ns using local.src_ext.Rf_lSup_subset_Rf_llimit derivns ns by auto
      then show False using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>" 
      using ground_C
      by (metis make_single_ground_subst subset_mset.order_refl) 
    then show ?thesis by auto
  qed
  then obtain \<sigma> where \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from deriv have four_ten: "derivation src_ext.derive Ns" 
    using resolution_prover_ground_derivation ns by auto

  have "\<exists>l. D \<in> getP (lnth Sts l) \<and> D \<notin> getP (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_deleted_P[of D Sts i] d unfolding ns by auto
  then obtain l where l_p: "D \<in> getP (lnth Sts l) \<and> D \<notin> getP (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    by auto
  then have l_Ns: "enat (Suc l) < llength Ns"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using derivation_lnth_rel by auto
  then show ?thesis
  proof (induction rule: resolution_prover.cases)
    case (tautology_deletion A D_twin N P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (forward_subsumption P Q D_twin N)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (backward_subsumption_P N D_twin P Q)
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P" "?Ps l = P \<union> {D_twin}" "?Qs (Suc l) = Q" "?Qs l = Q" 
      using l_p by auto
    then obtain D' where D'_p: "properly_subsumes D' D \<and> D' \<in> N"
      using backward_subsumption_P by auto
    then have subc: "subsumes D' C"
      unfolding properly_subsumes_def subsumes_def using \<sigma>
      by (metis subst_cls_comp_subst subst_cls_mono_mset) 
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
      unfolding twins(2)[symmetric] using l_p
      by (metis (no_types, lifting) UnI1 clss_of_state_def getN.simps llength_lmap lnth_lmap lnth_subset_lSup subsetCE sup_state_def) 
    then have False using d_least D'_p subc by auto
    then show ?case 
      by auto
  next
    case (backward_subsumption_Q N D_twin P Q)    
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (forward_reduction P Q L \<sigma> D_twin N)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (backward_reduction_P N L \<sigma> D' P Q)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P \<union> {D'}" "?Ps l = P \<union> {D' + {#L#}}" "?Qs (Suc l) = Q" "?Qs l = Q" 
      using l_p by auto
    then have D'_p: "properly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
      using subset_properly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding properly_subsumes_def by auto
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
       using l_p
       by (metis (no_types, lifting) UnI1 clss_of_state_def getP.simps llength_lmap lnth_lmap lnth_subset_lSup subsetCE sup_ge2 sup_state_def) 
    then have False using d_least D'_p subc by auto 
    then show ?case 
      by auto
  next
    case (backward_reduction_Q N L \<sigma> D_twin P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (clause_processing N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (inference_computation N Q D_twin P)
    then have twins: "D_twin = D" "?Ps (Suc l) = P" "?Ps l = P \<union> {D_twin}" "?Qs (Suc l) = Q \<union> {D_twin}" "?Qs l = Q" 
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p by auto
  qed
qed

lemma from_N_to_P_or_Q:
  assumes 
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and

    c: "C \<in> llimit Ns - src.Rf (llimit Ns)" and
    d: "D \<in> getN (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D"
  shows "\<exists>l D' \<sigma>'. D' \<in> getP (lnth Sts l) \<union> getQ (lnth Sts l) \<and> enat l < llength Sts \<and> (\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D') \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>' \<and> subsumes D' C"
proof -
  let ?Ns = "\<lambda>i. getN (lnth Sts i)"
  let ?Ps = "\<lambda>i. getP (lnth Sts i)"
  let ?Qs = "\<lambda>i. getQ (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using llimit_grounding_of_state_ground ns by auto 

  have derivns: "derivation src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C" 
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C
        by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl) 
      ultimately
      have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover
      have "is_ground_subst \<tau>" using \<tau>_p by auto
      moreover 
      have "D \<in> clss_of_state (lnth Sts i)" 
        using d getN_subset by auto
      ultimately
      have "C \<in> src.Rf (grounding_of_state (lnth Sts i))" 
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"]
        by auto
      then have "C \<in> src.Rf (Lazy_List_Limit.lSup Ns)" 
        using d ns
        by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_lSup src.Rf_mono) 
      then have "C \<in> src.Rf (llimit Ns)" 
        unfolding ns using local.src_ext.Rf_lSup_subset_Rf_llimit derivns ns by auto
      then show False using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>" 
      using ground_C
      by (metis make_single_ground_subst subset_mset.order_refl) 
    then show ?thesis by auto
  qed
  then obtain \<sigma> where \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from c have no_taut: "\<not>(\<exists>A. Pos A \<in># C \<and> Neg A \<in># C)" 
    using src.tautology_redundant by auto

  from deriv have four_ten: "derivation src_ext.derive Ns" 
    using resolution_prover_ground_derivation ns by auto

  have "\<exists>l. D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_deleted[of D Sts i] d unfolding ns by auto
  then obtain l where l_p: "D \<in> getN (lnth Sts l) \<and> D \<notin> getN (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    by auto
  then have l_Ns: "enat (Suc l) < llength Ns"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using derivation_lnth_rel by auto
  then show ?thesis
  proof (induction rule: resolution_prover.cases)
    case (tautology_deletion A D_twin N P Q)
    then have "D_twin = D" 
      using l_p by auto
    then have "Pos (A \<cdot>a \<sigma>) \<in># C \<and> Neg (A \<cdot>a \<sigma>) \<in># C"
      using tautology_deletion(3,4) \<sigma>
      by (metis Melem_subst_cls eql_neg_lit_eql_atm eql_pos_lit_eql_atm) 
    then have False 
      using no_taut by metis
    then show ?case
      by blast 
  next
    case (forward_subsumption P Q D_twin N) 
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D_twin}"  "?Ps (Suc l) = P " "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q" 
      using l_p by auto
    from forward_subsumption obtain D' where D'_p: "D' \<in> P \<union> Q \<and> subsumes D' D"
      using twins by auto
    then have subs: "subsumes D' C"
      using d(3) subsumes_trans by auto
    moreover
    have "D' \<in> clss_of_state (sup_state Sts)"
      using twins D'_p l_p unfolding clss_of_state_def sup_state_def apply simp
      by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_lSup) 
    ultimately
    have "\<not>properly_subsumes D' D"
      using d_least by auto
    then have "subsumes D D'"
      unfolding properly_subsumes_def using D'_p by auto
    then have mini: "\<forall>E\<in>{E \<in> clss_of_state (sup_state Sts). subsumes E C}. \<not> properly_subsumes E D'" 
      using d_least sorry (* I think it's something like this. Maybe. Well if nothing else the argument is that D and D' must simply be renamings of each other. *)

    obtain \<sigma>' where \<sigma>'_p: "D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      sorry (* Well if nothing else the argument is that D and D' must simply be renamings of each other. *)

    show ?case
      using D'_p twins l_p subs mini \<sigma>'_p
      apply auto
      done
  next
    case (backward_subsumption_P N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (backward_subsumption_Q N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  next
    case (forward_reduction P Q L \<sigma> D' N)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N \<union> {D'}" "?Ns l = N \<union> {D' + {#L#}}"  "?Ps (Suc l) = P " "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q" 
      using l_p by auto
    then have D'_p: "properly_subsumes D' D \<and> D' \<in> ?Ns (Suc l)"
      using subset_properly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding properly_subsumes_def by auto
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
       using l_p
       by (metis (no_types, lifting) UnI1 clss_of_state_def getN.simps llength_lmap lnth_lmap lnth_subset_lSup subsetCE sup_state_def) 
    then have False using d_least D'_p subc by auto
    then show ?case 
      by auto
  next
    case (backward_reduction_P N L \<sigma> D' P Q)
    then have False 
      using l_p by auto
    then show ?case 
      by auto
  next
    case (backward_reduction_Q N L \<sigma> C P Q)
    then have False
      using l_p by auto
    then show ?case 
      by auto 
  next
    case (clause_processing N D_twin P Q)
    then have twins:  "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D}"  "?Ps (Suc l) = P \<union> {D}" "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q" 
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p
      using d_least by blast
  next
    case (inference_computation N Q C P)
    then have False
      using l_p by auto
    then show ?case 
      by auto
  qed 
qed
 

text {*
The following corresponds to Lemma 4.11:
*}

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
  then have "C \<in> lSup Ns"
    using llimit_subset_lSup[of Ns] by blast
  then obtain D_proto where "D_proto \<in> clss_of_state (sup_state Sts) \<and> subsumes D_proto C"
    unfolding ns using in_lSup_in_sup_state unfolding subsumes_def
    by blast
  then obtain D where D_p: "D \<in> clss_of_state (sup_state Sts)" "subsumes D C" "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D"
    using properly_subsumes_has_minimum[of "{E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}"]
    by auto

  from D_p(1) obtain i where i_p: "i < llength Sts" "D \<in> ?Ns i \<or> D \<in> ?Ps i \<or> D \<in> ?Qs i"
    unfolding clss_of_state_def unfolding sup_state_def 
    apply auto
      apply (metis in_lSup_in_nth llength_lmap lnth_lmap)+ 
    done

  have ground_C: "is_ground_cls C"
    using C_p using llimit_grounding_of_state_ground ns by auto 

  have derivns: "derivation src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof - (* copy paste *)
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C" 
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from D_p obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C
        by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl) 
      ultimately
      have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover
      have "is_ground_subst \<tau>" using \<tau>_p by auto
      moreover 
      have "D \<in> clss_of_state (lnth Sts i)" 
        using D_p getN_subset by (meson contra_subsetD getP_subset getQ_subset i_p(1) i_p(2)) 
      ultimately
      have "C \<in> src.Rf (grounding_of_state (lnth Sts i))" 
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"]
        by auto
      then have "C \<in> src.Rf (Lazy_List_Limit.lSup Ns)" 
        using D_p ns src.Rf_mono
        by (metis (no_types, lifting) i_p(1) contra_subsetD llength_lmap lnth_lmap lnth_subset_lSup) 
      then have "C \<in> src.Rf (llimit Ns)" 
        unfolding ns using local.src_ext.Rf_lSup_subset_Rf_llimit derivns ns by auto
      then show False using C_p by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>" 
      using ground_C
      by (metis make_single_ground_subst subset_mset.order_refl) 
    then show ?thesis by auto
  qed
  then obtain \<sigma> where \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by blast

  note i_p
  moreover
  {
    assume a: "D \<in> ?Ns i"
    then obtain D' \<sigma>' l where D'_p: 
      "D' \<in> ?Ps l \<union> ?Qs l" 
      "D' \<cdot> \<sigma>' = C" 
      "enat l < llength Sts" 
      "is_ground_subst \<sigma>'" (* Do I also need that l is later than i? Probably not. *)
      "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not>properly_subsumes E D'"
      "subsumes D' C"
      using from_N_to_P_or_Q[OF deriv fair ns C_p a i_p(1) D_p(2) D_p(3)] by blast
    then obtain l' where l'_p: "D' \<in> ?Qs l'" "l' < llength Sts" (* Do I also need that l is later than l'? Probably not*)
      using from_P_to_Q[OF deriv fair ns C_p _ D'_p(3) D'_p(6) D'_p(5)] by blast
    then have "D' \<in> getQ (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns C_p _ l'_p(2)] D'_p by auto
    then have "\<exists>D' \<sigma>'. D' \<in> getQ (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D'_p by auto
  }
  moreover
  {
    assume a: "D \<in> ?Ps i"
    then obtain l' where l'_p: "D \<in> ?Qs l'" "l' < llength Sts" (* Do I also need that l is later than l'? Probably not*)
      using from_P_to_Q[OF deriv fair ns C_p a i_p(1) D_p(2) D_p(3) ] by auto
    then have "D \<in> getQ (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns C_p l'_p(1) l'_p(2)] D_p(3) \<sigma>(1) \<sigma>(2) D_p(2) by auto
    then have "\<exists>D' \<sigma>'. D' \<in> getQ (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D_p \<sigma> by auto
  }
  moreover
  {
    assume a: "D \<in> ?Qs i"
    then have "D \<in> getQ (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns C_p a i_p(1)] \<sigma> D_p(2) D_p(3) by auto
    then have "\<exists>D' \<sigma>'. D' \<in> getQ (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D_p \<sigma> by auto
  }
  ultimately
  have "\<exists>D' \<sigma>'. D' \<in> getQ (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    by auto
  then obtain D' \<sigma>' where D'_p: "D' \<in> getQ (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    by blast
  then have "D' \<in> clss_of_state (limit_state Sts)"
    by (simp add: clss_of_state_def)
  then show "C \<in> grounding_of_state (limit_state Sts)"
    unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def using D'_p by auto
qed



text {*
The following corresponds to (one direction of) Theorem 4.13:
*}

theorem completeness:
  assumes
    deriv: "derivation (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    unsat: "\<not> satisfiable (grounding_of_state (limit_state Sts))" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "{#} \<in> clss_of_state (limit_state Sts)"
proof -
  let ?N = "\<lambda>i. grounding_of_state (lnth Sts i)"
  define \<Gamma>x :: "'a inference set" where "\<Gamma>x = undefined"
  define Rf :: "'a literal multiset set \<Rightarrow> 'a literal multiset set" where "Rf = standard_redundancy_criterion.Rf"
  define derive where "derive = redundancy_criterion.derive \<Gamma>x Rf"

  from fair deriv have "llimit Ns - src.Rf (llimit Ns) \<subseteq> grounding_of_state (limit_state Sts)" using fair_imp_limit_minus_Rf_subset_ground_limit_state ns by blast

  have derivns: "derivation src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  {
    fix \<gamma> :: "'a inference"
    assume "\<gamma> \<in> undefined"
    let ?Cs = "side_prems_of \<gamma>"
    let ?D = "main_prem_of \<gamma>"
    let ?E = "concl_of \<gamma>"
    assume "set_mset ?Cs \<union> {?D} \<subseteq> grounding_of_state (limit_state Sts) - src.Rf (grounding_of_state (limit_state Sts))"

    thm ord_resolve_rename_lifting

    then obtain Y where True sorry
  }
    
oops
  
end
  
end
