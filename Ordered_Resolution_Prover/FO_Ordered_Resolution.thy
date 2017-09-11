(*  Title:       A Simple Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull, 2017
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull
*)

theory FO_Ordered_Resolution
imports Ordered_Ground_Resolution Standard_Redundancy Substitution
begin

(* FIXME: Avoid such global changes to the intro/etc. sets *)
declare nth_equalityI [intro]

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

fun N_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "N_of_state (N, P, Q) = N"

fun P_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "P_of_state (N, P, Q) = P"

fun Q_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "Q_of_state (N, P, Q) = Q"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = N_of_state St \<union> P_of_state St \<union> Q_of_state St"

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

definition maximal_in :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where (* Would "'a \<Rightarrow> 'a set \<Rightarrow> bool" be cleaner?  *)
   "maximal_in A DAs \<equiv> (\<forall>B \<in> atms_of DAs. \<not> less_atm A B)"
  
abbreviation str_maximal_in :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where (* Would "'a \<Rightarrow> 'a set \<Rightarrow> bool" be cleaner?  *)
  "str_maximal_in A CAis \<equiv> (\<forall>B \<in> atms_of CAis. \<not> less_eq_atm A B)"

inductive eligible :: "'s \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
    "S DA = negs (mset Ai) \<or> (S DA = {#} \<and> length Ai = 1 \<and> maximal_in ((Ai ! 0) \<cdot>a \<sigma>) (DA \<cdot> \<sigma>)) \<Longrightarrow>
     eligible \<sigma> Ai DA"

inductive ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool" where
  ord_resolve:
  "length CAi = n \<Longrightarrow>
   length Ci = n \<Longrightarrow>
   length Aij = n \<Longrightarrow>
   length Ai = n \<Longrightarrow>
   n \<noteq> 0 \<Longrightarrow>
   \<forall>i < n. (CAi ! i) = (Ci ! i + (poss (Aij ! i))) \<Longrightarrow> (* could be written with map *)
   \<forall>i < n. Aij ! i \<noteq> {#} \<Longrightarrow>
   Some \<sigma> = mgu (set_mset ` (set (map2 add_mset Ai Aij))) \<Longrightarrow>
   eligible \<sigma> Ai (D + negs (mset Ai)) \<Longrightarrow>
   \<forall>i. i < n \<longrightarrow> str_maximal_in (Ai ! i \<cdot>a \<sigma>) ((Ci ! i) \<cdot> \<sigma>) \<Longrightarrow>
   \<forall>i < n. S (CAi ! i) = {#} \<Longrightarrow> (* Use the ! style instead maybe, or maybe us the \<forall>\<in>. style above *)
   ord_resolve CAi (D + negs (mset Ai)) \<sigma> (((\<Union># (mset Ci)) + D) \<cdot> \<sigma>)"

lemma is_mgu_is_unifiers: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<sigma> AAA"
  using is_mgu_def by blast

lemma is_mgu_is_more_general: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<tau> AAA \<Longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>)"
  using is_mgu_def by blast

lemma is_unifiers_is_unifier: "is_unifiers \<sigma> AAA \<Longrightarrow> AA \<in> AAA \<Longrightarrow> is_unifier \<sigma> AA"
  using is_unifiers_def by auto

lemma mgu_unifier:
  assumes ailen: "length Ai = n"
  assumes aijlen: "length Aij = n"
  assumes mgu: "Some \<sigma> = mgu (set_mset ` (set (map2 add_mset Ai Aij)))"
  shows "\<forall>i < n. (\<forall>A \<in># Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>)"
proof -
  from mgu have "is_mgu \<sigma> (set_mset ` (set (map2 add_mset Ai Aij)))"
    using mgu_sound by auto
  then have uni: "is_unifiers \<sigma> (set_mset ` (set (map2 add_mset Ai Aij)))"
    using is_mgu_is_unifiers by auto
  show "\<forall>i < n. (\<forall>A \<in># Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>)"
  proof (rule allI; rule impI)
    fix i
    assume i: "i < n"
    then have "is_unifier \<sigma> (set_mset (add_mset (Ai ! i) (Aij ! i)))"
      using ailen aijlen uni is_unifiers_is_unifier
      by (auto simp del: map2_nth simp add: map2_nth[symmetric])
    then show "\<forall>A\<in>#Aij ! i. A \<cdot>a \<sigma> = Ai ! i \<cdot>a \<sigma>"
      using ailen aijlen i is_unifier_subst_atm_eqI by (metis finite_set_mset insertCI set_mset_add_mset_insert)
  qed
qed

definition mk_var_dis :: "'a literal multiset list \<Rightarrow> 's list" where
  "mk_var_dis Cs = (SOME \<rho>s. length \<rho>s = length Cs \<and> (\<forall>\<rho> \<in> set \<rho>s. is_renaming \<rho>) \<and>
     var_disjoint (Cs \<cdot>\<cdot>cl \<rho>s))"

lemma mk_var_dis_p:
  "length (mk_var_dis Cs) = length Cs \<and> (\<forall>\<rho> \<in> set (mk_var_dis Cs). is_renaming \<rho>) \<and>
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
  "\<rho> = hd (mk_var_dis (DA # CAi)) \<Longrightarrow>
   \<rho>s = tl (mk_var_dis (DA # CAi)) \<Longrightarrow>
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
  then have rename_P: "\<forall>\<rho> \<in> set P. is_renaming \<rho>"
    using mk_var_dis_p by (metis list.sel(2) list.set_sel(2))
  from ord_resolve_rename have len: "length P = length CAi"
    using mk_var_dis_p by auto
  have res_e: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) \<sigma> E"
    using ord_resolve_rename by auto
  have "CAi \<cdot>\<cdot>cl P = CAi"
    using len gr_cc by auto
  moreover
  have "DA \<cdot> \<rho> = DA"
    using gr_d by auto
  ultimately show ?thesis
    using res_e by auto
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
  unfolding true_fo_cls_mset.simps true_fo_cls.simps true_cls_mset_def by auto

lemma true_cls_mset_true_cls: "I \<Turnstile>m CC \<Longrightarrow> C \<in># CC \<Longrightarrow> I \<Turnstile> C" using true_cls_mset_def by auto

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
  have e: "E = (\<Union># mset Ci + D) \<cdot> \<sigma>" using ord_resolve by -
  have ci_len: "length Ci = n" using ord_resolve by -
  have cai_len: "length CAi = n" using ord_resolve by -
  have aij_len: "length Aij = n" using ord_resolve by -
  have ai_len: "length Ai = n" using ord_resolve by -
  have cai: "\<forall>i < n. CAi ! i = Ci ! i + poss (Aij ! i)" using ord_resolve by -
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
      unfolding true_cls_def[of I] by auto
    hence "I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<eta>"
      using d_true DA by auto
    thus ?thesis
      unfolding e by auto
  next
    case False
    then obtain i where a_in_aa: "i < length CAi" and a_false: "(Ai ! i) \<cdot>a \<sigma> \<cdot>a \<eta> \<notin> I"
      using DA len by (metis in_set_conv_nth)
    define C' where "C' \<equiv> Ci ! i"
    define BB where "BB \<equiv> Aij ! i"
    have c_cf': "C' \<subseteq># \<Union># mset CAi"
      unfolding C'_def using a_in_aa cai cai_len
      by (metis less_subset_eq_Union_mset mset_subset_eq_add_left subset_mset.order.trans)
    have c_in_cc: "C' + poss BB \<in># mset CAi"
      using C'_def BB_def using a_in_aa
      using cai_len in_set_conv_nth cai by fastforce
    {
      fix B
      assume "B \<in># BB"
      then have "B \<cdot>a \<sigma> = (Ai ! i) \<cdot>a \<sigma>" using unif a_in_aa cai_len unfolding BB_def by auto
    }
    hence "\<not> I \<Turnstile> poss BB \<cdot> \<sigma> \<cdot> \<eta>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C' + poss BB) \<cdot> \<sigma> \<cdot> \<eta>"
      using c_in_cc cc_true true_cls_mset_true_cls[of I "mset CAi \<cdot>cm \<sigma> \<cdot>cm \<eta>"] by force
    ultimately have "I \<Turnstile> C' \<cdot> \<sigma> \<cdot> \<eta>"
      by simp
    thus ?thesis
      unfolding e subst_cls_union using c_cf' C'_def a_in_aa cai_len ci_len
      by (metis (no_types, lifting) mset_subset_eq_add_left nth_mem_mset set_mset_mono sum_mset.remove true_cls_mono subst_cls_mono)
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

lemma true_fo_cls_mset_true_fo_cls: "(I \<Turnstile>fom CC) \<Longrightarrow> C \<in># CC \<Longrightarrow> I \<Turnstile>fo C"
  using true_fo_cls_mset_def2 by auto

lemma subst_sound_scl:
  assumes len: "length P = length CAi"
  assumes true_cas: "I \<Turnstile>fom mset CAi"
  shows "I \<Turnstile>fom mset (CAi \<cdot>\<cdot>cl P)"
proof -
  from true_cas have "\<forall>C. C\<in># mset CAi \<longrightarrow> (I \<Turnstile>fo C)"
    using true_fo_cls_mset_true_fo_cls by auto
  then have "\<forall>C. C \<in> set CAi \<longrightarrow> (I \<Turnstile>fo C)" by auto
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i))"
    using in_set_conv_nth[of _ CAi] by blast
  then have "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo  (CAi ! i) \<cdot> P ! i)"
    using subst_sound len by auto
  then have true_cp: "\<forall>i. i < length CAi \<longrightarrow> (I \<Turnstile>fo (CAi ! i \<cdot> P ! i))"
    by auto
  {
    fix x
    assume "x \<in># mset (CAi \<cdot>\<cdot>cl P)"
    then have "x \<in> set_mset (mset ((CAi \<cdot>\<cdot>cl P)))" by -
    then have "x \<in> set (CAi \<cdot>\<cdot>cl P)" by auto
    then obtain i where i_x: "i < length (CAi \<cdot>\<cdot>cl P) \<and> x = (CAi \<cdot>\<cdot>cl P) ! i"
      using in_set_conv_nth by metis
    then have "I \<Turnstile>fo x" using true_cp unfolding subst_cls_lists_def
      by (simp add: len)
  }
  then show ?thesis unfolding true_fo_cls_mset_def2 by auto
qed

lemma ord_resolve_rename_ground_inst_sound: (* This theorem will be used in 4.11. *)
  assumes
    res_e: "ord_resolve_rename CAi DA \<sigma> E" and
    \<rho>s: "\<rho>s = tl (mk_var_dis (DA # CAi))" and
    \<rho>: "\<rho> = hd (mk_var_dis (DA # CAi))" and
    cc_inst_true: "I \<Turnstile>m (mset (CAi \<cdot>\<cdot>cl \<rho>s)) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and
    d_inst_true: "I \<Turnstile> DA \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<eta>" and
     ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho>_twin \<rho>s_twin)
  then show ?thesis
    using ord_resolve_ground_inst_sound[of _ _ \<sigma> E I \<eta>] \<rho>s \<rho> cc_inst_true d_inst_true ground_subst_\<eta>
    by simp
qed

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAi DA \<sigma> E" and
    cc_d_true: "I \<Turnstile>fom (mset CAi) + {#DA#}"
  shows "I \<Turnstile>fo E"
  using res_e
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename \<rho> P)
  then have len: "length P = length CAi" 
    using ord_resolve_rename mk_var_dis_p by auto
  have res: "ord_resolve (CAi \<cdot>\<cdot>cl P) (DA \<cdot> \<rho>) \<sigma> E"
    using ord_resolve_rename by -
  have "I \<Turnstile>fom (mset (CAi \<cdot>\<cdot>cl P)) + {#DA \<cdot> \<rho>#}"
    using subst_sound_scl[OF len, of I] subst_sound[of I DA] cc_d_true
    by (simp add: true_fo_cls_mset_def2)
  then show "I \<Turnstile>fo E"
    using ord_resolve_sound[of "CAi \<cdot>\<cdot>cl P" "DA \<cdot> \<rho>" \<sigma> E I, OF res] by simp
qed

context
  fixes M :: "'a clause set"
  assumes select: "selection S"
begin

interpretation selection
  by (rule select)

definition S_M :: "'a literal multiset \<Rightarrow> 'a literal multiset" where
  "S_M C =
   (if C \<in> grounding_of_clss M then
      (SOME C'. \<exists>D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>)
    else
      S C)"

lemma S_M_grounding_of_clss:
  assumes "C \<in> grounding_of_clss M"
  obtains D \<sigma> where "D \<in> M \<and> C = D \<cdot> \<sigma> \<and> S_M C = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
proof (atomize_elim, unfold S_M_def eqTrueI[OF assms] if_True, rule someI_ex)
  from assms show "\<exists>C' D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    by (auto simp: grounding_of_clss_def grounding_of_cls_def)
qed

lemma S_M_not_grounding_of_clss: "C \<notin> grounding_of_clss M \<Longrightarrow> S_M C = S C"
  unfolding S_M_def by simp

lemma S_M_selects_subseteq: "S_M C \<le># C"
  by (metis S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_subseteq subst_cls_mono_mset)

lemma S_M_selects_neg_lits: "L \<in># S_M C \<Longrightarrow> is_neg L"
  by (metis Melem_subst_cls S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_neg_lits
      subst_lit_is_neg)

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
  unfolding grounding_of_clss_def grounding_of_cls_def by auto

lemma eql_map_neg_lit_eql_atm:
  assumes "map (\<lambda>x. x \<cdot>l \<eta>) (map Neg Ai') = map Neg Ai"
  shows "Ai' \<cdot>al \<eta> = Ai"
  using assms
by (induction Ai' arbitrary: Ai) auto

lemma instance_list:
  assumes "negs (mset Ai) = SDA' \<cdot> \<eta>"
  shows "\<exists>Ai'. negs (mset Ai') = SDA' \<and> Ai' \<cdot>al \<eta> = Ai"
proof -
  from assms have negL: "\<forall>L \<in># SDA'. is_neg L"
    using Melem_subst_cls subst_lit_in_negs_is_neg by metis

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

lemma length_subst_atm_mset_list[simp]: "length (Aij' \<cdot>aml \<eta>) = length Aij'"
  unfolding subst_atm_mset_list_def by auto

lemma map2_add_mset_map:
  assumes "length Aij' = n"
  assumes "length Ai' = n"
  shows "(map2 add_mset (Ai' \<cdot>al \<eta>) (Aij' \<cdot>aml \<eta>)) = (map2 add_mset Ai' Aij' \<cdot>aml \<eta>)"
  using assms proof (induction n arbitrary: Aij' Ai')
  case (Suc n)
  then have "map2 add_mset (tl Ai' \<cdot>al \<eta>) (tl Aij' \<cdot>aml \<eta>) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>"
    by simp
  then have "map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>)) = map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>"
    by simp
  moreover
  have Succ: "length (Ai' \<cdot>al \<eta>) = Suc n" "length (Aij' \<cdot>aml \<eta>) = Suc n"
    using Suc(3) Suc(2) by auto 
  then have "length (tl (Ai' \<cdot>al \<eta>)) = n" "length (tl (Aij' \<cdot>aml \<eta>)) = n"
    by auto
  then have "length (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) = n"
    "length (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) = n"
    using Suc(3) Suc(2) by auto
  ultimately
  have "\<forall>i < n. (map2 add_mset (tl (Ai' \<cdot>al \<eta>)) (tl (Aij' \<cdot>aml \<eta>))) ! i = (map2 add_mset (tl Ai') (tl Aij') \<cdot>aml \<eta>) ! i"
    by auto
  then have "\<forall>i < n. tl (map2 add_mset ( (Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) ! i = tl (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) ! i"
    using Suc(2) Suc(3) Succ by (simp add: map2_tl map_tl subst_atm_mset_list_def del: subst_atm_list_tl)
  moreover
  have nn: "length (map2 add_mset ((Ai' \<cdot>al \<eta>)) ((Aij' \<cdot>aml \<eta>))) = Suc n"
    "length (map2 add_mset (Ai') (Aij') \<cdot>aml \<eta>) = Suc n"
    using Succ using Suc by auto
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

lemma in_atms_of_subst[simp]: "B \<in> atms_of C \<Longrightarrow> B \<cdot>a \<sigma> \<in> atms_of (C \<cdot> \<sigma>)"
  by (metis atms_of_subst_atms image_iff subst_atms_def)

lemma maximal_in_gen:
  assumes "maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
  shows "maximal_in A C"
proof -
  from assms have "maximal_in (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)" by -
  hence "\<forall>B \<in> atms_of (C \<cdot> \<sigma>). \<not> less_atm (A \<cdot>a \<sigma>) B" unfolding maximal_in_def by -
  hence ll: "\<forall>B\<in>atms_of (C \<cdot> \<sigma>). \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma>'))" unfolding less_atm_iff by -
  have "\<forall>B\<in>atms_of C. \<not> ((\<forall>\<sigma>'. is_ground_subst \<sigma>' \<longrightarrow> A \<cdot>a \<sigma> \<cdot>a \<sigma>' < B \<cdot>a \<sigma> \<cdot>a \<sigma>'))"
     using ll by auto
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


lemma sum_list_subseteq_mset_is_ground_cls_list[simp]: 
  "sum_list Ci \<subseteq># sum_list CAi \<Longrightarrow> is_ground_cls_list CAi \<Longrightarrow> is_ground_cls_list Ci"
  by (metis is_ground_cls_Union_mset is_ground_cls_list_def is_ground_cls_mono is_ground_cls_mset_def set_mset_mset sum_mset_sum_list)

lemma is_ground_cls_list_is_ground_cls_sum_list[simp]: 
  "is_ground_cls_list Ci \<Longrightarrow> is_ground_cls (sum_list Ci)"
  by (meson in_mset_sum_list2 is_ground_cls_def is_ground_cls_list_def)

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
    by simp
  have dsuDA :"D \<subseteq># DA" by (simp add: local.ord_resolve(1))
  hence gr_di: "is_ground_cls D"
    using gr_d is_ground_cls_mono by auto

  have "is_ground_cls (\<Union>#mset Ci + D)" using gr_ci gr_di
    by auto
  then have Ci_D_\<sigma>: "(\<Union>#mset Ci + D) = (\<Union>#mset Ci + D) \<cdot> \<sigma>" by auto
  then have "E = (\<Union>#mset Ci + D) \<cdot> \<sigma>" using ord_resolve by -
  then have "E = (\<Union>#mset Ci + D)" using Ci_D_\<sigma> by auto
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
    unfolding CAi''_def \<eta>s''_def using f_p(2) by (auto simp: n)
  have SCAi''_to_SMCAi: "(map S CAi'') \<cdot>\<cdot>cl \<eta>s'' = map (S_M S M) CAi"
   unfolding CAi''_def \<eta>s''_def using f_p(3) n by force

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
    using selection_renaming_invariant unfolding is_renaming_list_def by auto

  note n = \<open>n \<noteq> 0\<close> \<open>length CAi = n\<close> \<open>length Ci = n\<close> \<open>length Aij = n\<close> \<open>length Ai = n\<close>

  interpret S: selection S by (rule select)

  obtain DA'' \<eta>'' CAi'' \<eta>s'' where ai'':
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
    using n mk_var_dis_p by auto

  note n = \<open>length (mk_var_dis (DA''#CAi'')) = Suc n\<close> n

  define DA' where "DA' = DA'' \<cdot> hd (mk_var_dis (DA''#CAi''))"
  define CAi' where "CAi' = CAi'' \<cdot>\<cdot>cl tl (mk_var_dis (DA''#CAi''))"
  define \<eta>' where "\<eta>' = (inv_ren (hd (mk_var_dis (DA''#CAi'')))) \<odot> \<eta>''"
  define \<eta>s' where "\<eta>s' = (map inv_ren (tl (mk_var_dis (DA''#CAi'')))) \<odot>s \<eta>s''"

  have iiir: "is_renaming (hd (mk_var_dis (DA''#CAi'')))"
    using mk_var_dis_p[of "DA'' # CAi''"]
    by (metis length_greater_0_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  have iiiiiir: "is_renaming_list (tl (mk_var_dis (DA''#CAi'')))"
    using mk_var_dis_p[of "DA'' # CAi''"]
    by (metis is_renaming_list_def length_greater_0_conv list.set_sel(2) list.simps(3))


  have "length CAi' = n"
    using ai''(1) n unfolding CAi'_def by auto
  have "length \<eta>s' = n"
    using ai''(2) n unfolding \<eta>s'_def by auto
  note n = \<open>length CAi' = n\<close> \<open>length \<eta>s' = n\<close> n

  have DA'_DA: "DA' \<cdot> \<eta>' = DA"
    using ai''(4) unfolding \<eta>'_def DA'_def using iiir by auto
  have "S DA' \<cdot> \<eta>' = S_M S M DA"
    using ai''(5) unfolding \<eta>'_def DA'_def using iiir selection_renaming_invariant
    by auto
  have CAi'_CAi: "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi"
    using ai''(7)  unfolding CAi'_def \<eta>s'_def using n(3)
    using mk_var_dis_p using iiiiiir
    by auto
  have "(map S CAi') \<cdot>\<cdot>cl \<eta>s' = map (S_M S M) CAi"
    unfolding CAi'_def \<eta>s'_def using ai''(8) n(3,4) iiiiiir selection_renaming_list_invariant by auto
  have vd: "var_disjoint (DA' # CAi')" unfolding DA'_def CAi'_def
    using mk_var_dis_p[of "DA'' # CAi''"]
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
      unfolding eligible.simps[simplified]
    proof
      assume a: "S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = (Suc 0) \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
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
      assume "i < n"
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
    have "eligible (S_M S M) \<sigma> Ai (D + negs (mset Ai))" using ord_resolve unfolding eligible.simps[simplified] by -
    hence "S_M S M (D + negs (mset Ai)) = negs (mset Ai) \<or>
    S_M S M (D + negs (mset Ai)) = {#} \<and> length Ai = 1 \<and> maximal_in (Ai ! 0 \<cdot>a \<sigma>) ((D + negs (mset Ai)) \<cdot> \<sigma>)"
      unfolding eligible.simps[simplified] by auto
    thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))"
    proof
      assume as: "S_M S M (D + negs (mset Ai)) = negs (mset Ai)"
      then have "S_M S M (D + negs (mset Ai)) \<noteq> {#}"
        using n ord_resolve(7) by force
      then have "negs (mset Ai') = S DA'" using ai' by auto
      hence "S (D'  + negs (mset Ai')) = negs (mset Ai')" using ai' by auto
      thus "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible.simps[simplified]  by auto
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
      ultimately show "eligible S \<tau> Ai' (D' + negs (mset Ai'))" unfolding eligible.simps[simplified]  by auto
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
      \<open>CAi'' \<cdot>\<cdot>cl \<eta>s'' = CAi\<close>
      \<open>DA'' \<cdot> \<eta>'' = DA\<close>
      \<open>E' \<cdot> \<eta>2 = E\<close>
      \<open>DA'' \<in> M\<close>
      \<open>\<forall>CA\<in>set CAi''. CA \<in> M\<close>
    by blast
qed

end

end
