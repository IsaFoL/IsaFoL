(*  Title:       Theorem Proving Processes
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2014
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull 2017
*)

section {* Theorem Proving Processes *}

theory Proving_Process
imports Unordered_Ground_Resolution Lazy_List_Limit
begin

text {*
This material corresponds to Section 4.1 (``Theorem Proving Processes'') of Bachmair and Ganzinger's
chapter.
*}


subsection {* Derivations *}

coinductive derivation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool"
	  for R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
	  singleton: "derivation R (LCons N LNil)"
	| cons: "derivation R Ns \<Longrightarrow> R M (lhd Ns) \<Longrightarrow> derivation R (LCons M Ns)"

lemma
  derivation_LNil[simp]: "\<not> derivation R LNil" and
  lnull_derivation: "lnull Ns \<Longrightarrow> \<not> derivation R Ns"
  by (auto elim: derivation.cases)

lemma derivation_ldropn:
  assumes "derivation R Ns" and "enat n < llength Ns"
  shows "derivation R (ldropn n Ns)"
using assms
proof (induct n arbitrary: Ns)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  from Suc.prems(2) have len: "enat n < llength Ns"
    using Suc_ile_eq less_imp_le by blast
  hence "derivation R (ldropn n Ns)"
    using Suc.hyps Suc.prems(1) by blast
  hence "derivation R (LCons (lnth Ns n) (ldropn (Suc n) Ns))"
    using len by (simp add: ldropn_Suc_conv_ldropn)
  thus ?case
    using Suc.prems(2) by (auto elim: derivation.cases simp: ldropn_eq_LNil)
qed

lemma derivation_lnth_rel:
  assumes
    deriv: "derivation R Ns" and
    len: "enat (Suc j) < llength Ns"
  shows "R (lnth Ns j) (lnth Ns (Suc j))"
proof -
  define Ms where "Ms = ldropn j Ns"
  have "llength Ms > 1"
    unfolding Ms_def using len
    by (metis eSuc_enat funpow_swap1 ldropn_0 ldropn_def ldropn_ltl lnull_ldropn not_less one_eSuc
      zero_enat_def)
  obtain M0 M1 Ms' where ms: "Ms = LCons M0 (LCons M1 Ms')"
    unfolding Ms_def by (metis Suc_ile_eq ldropn_Suc_conv_ldropn len less_imp_not_less not_less)
  have "derivation R Ms"
  unfolding Ms_def
  proof -
    have "Ms \<noteq> LNil" and "lhd Ms = M0"
      unfolding ms by simp_all
    thus "derivation R (ldropn j Ns)"
      unfolding Ms_def using deriv derivation_ldropn ldropn_all not_less by blast
  qed
  hence "R M0 M1"
    unfolding ms by (auto elim: derivation.cases)
  thus ?thesis
    using Ms_def unfolding ms by (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject)
qed


subsection {* Processes *}

text {*
The locale assumptions below capture conditions R1 to R3 of Definition 4.1.
@{text Rf} denotes $\mathcal{R}_{\mathcal{F}}$; @{text Ri} denotes $\mathcal{R}_{\mathcal{I}}$.
*}

locale redundancy_criterion = inference_system +
  fixes
    Rf :: "'a clause set \<Rightarrow> 'a clause set" and
    Ri :: "'a clause set \<Rightarrow> 'a inference set"
  assumes
    Ri_subset_\<Gamma>: "Ri N \<subseteq> \<Gamma>" and
    Rf_mono: "N \<subseteq> N' \<Longrightarrow> Rf N \<subseteq> Rf N'" and
    Ri_mono: "N \<subseteq> N' \<Longrightarrow> Ri N \<subseteq> Ri N'" and
    Rf_indep: "N' \<subseteq> Rf N \<Longrightarrow> Rf N \<subseteq> Rf (N - N')" and
    Ri_indep: "N' \<subseteq> Rf N \<Longrightarrow> Ri N \<subseteq> Ri (N - N')" and
    Rf_sat: "satisfiable (N - Rf N) \<Longrightarrow> satisfiable N"
begin

definition saturated_upto :: "'a clause set \<Rightarrow> bool" where
  "saturated_upto N \<longleftrightarrow> inferences_from (N - Rf N) \<subseteq> Ri N"

inductive "derive" :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<triangleright>" 50) where
  deduction_deletion: "M - N \<subseteq> concls_of (inferences_from N) \<Longrightarrow> N - M \<subseteq> Rf M \<Longrightarrow> N \<triangleright> M"
  
inductive "derive2" :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<triangleright>\<triangleright>" 50) where
  deduction: "M \<subseteq> concls_of (inferences_from N) \<Longrightarrow> N \<triangleright>\<triangleright> N \<union> M"
| deletion: "M \<subseteq> Rf N \<Longrightarrow> N \<union> M \<triangleright>\<triangleright> N"

lemma derive_subset: "M \<triangleright> N \<Longrightarrow> N \<subseteq> M \<union> concls_of (inferences_from M)"
  by (cases rule: derive.cases) auto
    
lemma derive_derive2: "rtranclp derive N1 N2 \<Longrightarrow> rtranclp derive2 N1 N2"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  from \<open>y \<triangleright> z\<close> step show ?case
    proof (induction rule: derive.induct)
      case (deduction_deletion M N)
      moreover
      from deduction_deletion have "N \<triangleright>\<triangleright> N \<union> (M - N)"
        using derive2.intros(1)[of "M - N" N] by auto
      moreover
      from deduction_deletion have "N \<union> (M - N) \<triangleright>\<triangleright> M"
        using derive2.intros(2)[of _ _]
        by (metis Un_Diff_cancel2 sup_commute) 
      ultimately
      show ?case using deduction_deletion by auto
    qed
  qed
    
lemma derive2_derive: "rtranclp derive2 N1 N2 \<Longrightarrow> rtranclp derive N1 N2"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)
  from \<open>y \<triangleright>\<triangleright> z\<close> step show ?case
    proof (induction rule: derive2.induct)
      case (deduction M N)
      then have "N \<triangleright> N \<union> M"
        using derive.intros[of "N \<union> M" N] by blast
      then show ?case 
        using deduction by auto 
    next
      case (deletion M N)
      then have "N \<union> M \<triangleright> N"
        using derive.intros[of N] by blast
      then show ?case using deletion 
        by auto
    qed
  qed
    
lemma "rtranclp derive = rtranclp derive2"
  apply (rule, rule)
  using derive_derive2 derive2_derive 
    by auto

end

text {*
\begin{nit}
Section 4.1 requires soundness, even though it is claimed in Section 2.4 that only
consistency-preserving inference systems will be considered. It turns out that consistency
preservation is enough.
\end{nit}
*}

locale sat_preserving_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" + redundancy_criterion
begin

lemma deriv_sat_preserving:
  assumes
    deriv: "derivation (op \<triangleright>) Ns" and
    sat_n0: "satisfiable (lhd Ns)"
  shows "satisfiable (lSup Ns)"
proof -
  have ns0: "lnth Ns 0 = lhd Ns"
    using deriv by (metis lnull_derivation lhd_conv_lnth)
  have len_ns: "llength Ns > enat 0"
    using deriv by (case_tac Ns) auto
  { fix DD
    assume fin: "finite DD" and sset_lun: "DD \<subseteq> lSup Ns"
    then obtain k where dd_sset: "DD \<subseteq> lSup_upto Ns k"
      using finite_lSup_imp_lSup_upto by blast
    have "satisfiable (lSup_upto Ns k)"
    proof (induct k)
      case 0
      thus ?case
        using len_ns ns0 sat_n0 unfolding lSup_upto_def true_clss_def by auto
    next
      case (Suc k)
      show ?case
      proof (cases "llength Ns \<le> enat (Suc k)")
        case True
        hence "lSup_upto Ns k = lSup_upto Ns (Suc k)"
          unfolding lSup_upto_def using le_Suc_eq not_less by blast
        thus ?thesis
          using Suc by simp
      next
        case False
        have sat: "satisfiable (lSup_upto Ns k \<union> concls_of (inferences_from (lSup_upto Ns k)))"
          using Suc \<Gamma>_sat_preserving unfolding sat_preserving_inference_system_def by simp
        have rel: "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using False deriv by (auto simp: derivation_lnth_rel)
        hence suc_k_subs: "lnth Ns (Suc k) \<subseteq> lnth Ns k \<union> concls_of (inferences_from (lnth Ns k))"
          by (rule derive_subset)
        have k_subs: "lnth Ns k \<subseteq> lSup_upto Ns k"
          unfolding lSup_upto_def using False Suc_ile_eq linear by blast
        hence "\<And>M. lnth Ns (Suc k) \<subseteq> lSup_upto Ns k \<union> (M \<union> concls_of (inferences_from (lnth Ns k)))"
          using suc_k_subs by force
        hence suc_k_subs':
          "lnth Ns (Suc k) \<subseteq> lSup_upto Ns k \<union> concls_of (inferences_from (lSup_upto Ns k))"
          using k_subs suc_k_subs
          by clarsimp (metis UnCI UnE image_Un inferences_from_mono le_iff_sup)
        have upto: "lSup_upto Ns (Suc k) = lSup_upto Ns k \<union> lnth Ns (Suc k)"
        proof
          show "lSup_upto Ns (Suc k) \<subseteq> lSup_upto Ns k \<union> lnth Ns (Suc k)"
            unfolding lSup_upto_def by (auto elim: le_SucE)
        next
          show "lSup_upto Ns k \<union> lnth Ns (Suc k) \<subseteq> lSup_upto Ns (Suc k)"
            unfolding lSup_upto_def using False by force
        qed
        show ?thesis
          unfolding upto true_clss_union using suc_k_subs' sat by (metis sup_ge1 true_clss_mono)
      qed
    qed
    hence "satisfiable DD"
      using dd_sset unfolding lSup_upto_def by (blast intro: true_clss_mono) }
  thus ?thesis
    using ground_resolution_without_selection.clausal_logic_compact[THEN iffD1] by metis
qed

text {*
This corresponds to Lemma 4.2:
*}

lemma derivation_supremum_llimit_satisfiable:
  assumes deriv: "derivation (op \<triangleright>) Ns"
  shows
    Rf_lSup_subset_Rf_llimit: "Rf (lSup Ns) \<subseteq> Rf (llimit Ns)" and
    Ri_lSup_subset_Ri_llimit: "Ri (lSup Ns) \<subseteq> Ri (llimit Ns)" and
    satisfiable_llimit_iff: "satisfiable (llimit Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
proof -
  { fix C i j
    assume
      c_in: "C \<in> lnth Ns i" and
      c_ni: "C \<notin> Rf (lSup Ns)" and
      j: "j \<ge> i" and
      j': "enat j < llength Ns"
    from c_ni have c_ni': "\<And>i. enat i < llength Ns \<Longrightarrow> C \<notin> Rf (lnth Ns i)"
      using Rf_mono lnth_subset_lSup lSup_def by (blast dest: contra_subsetD)
    have "C \<in> lnth Ns j"
    using j j'
    proof (induct j)
      case 0
      thus ?case
        using c_in by blast
    next
      case (Suc k)
      thus ?case
      proof (cases "i < Suc k")
        case True
        have "i \<le> k"
          using True by linarith
        moreover have "enat k < llength Ns"
          using Suc.prems(2) Suc_ile_eq by (blast intro: dual_order.strict_implies_order)
        ultimately have c_in_k: "C \<in> lnth Ns k"
          using Suc.hyps by blast
        have rel: "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using Suc.prems deriv by (auto simp: derivation_lnth_rel)
        thus ?thesis
          using c_in_k c_ni' Suc.prems(2) by cases auto
      next
        case False
        thus ?thesis
          using Suc c_in by auto
      qed
    qed  
  }
  hence lu_ll: "lSup Ns - Rf (lSup Ns) \<subseteq> llimit Ns"
    unfolding lSup_def llimit_def by blast
  have rf: "Rf (lSup Ns - Rf (lSup Ns)) \<subseteq> Rf (llimit Ns)"
    using lu_ll Rf_mono by simp
  have ri: "Ri (lSup Ns - Rf (lSup Ns)) \<subseteq> Ri (llimit Ns)"
    using lu_ll Ri_mono by simp
  show "Rf (lSup Ns) \<subseteq> Rf (llimit Ns)"
    using rf Rf_indep by blast
  show "Ri (lSup Ns) \<subseteq> Ri (llimit Ns)"
    using ri Ri_indep by blast

  show "satisfiable (llimit Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
  proof
    assume "satisfiable (lhd Ns)"
    hence "satisfiable (lSup Ns)"
      using deriv deriv_sat_preserving by simp
    thus "satisfiable (llimit Ns)"
      using true_clss_mono[OF llimit_subset_lSup] by blast
  next
    assume "satisfiable (llimit Ns)"
    hence "satisfiable (lSup Ns - Rf (lSup Ns))"
      using true_clss_mono[OF lu_ll] by blast
    hence "satisfiable (lSup Ns)"
      using Rf_sat by blast
    thus "satisfiable (lhd Ns)"
      using deriv true_clss_mono lhd_subset_lSup lnull_derivation by metis
  qed
qed

end

text {*
The assumption below corresponds to condition R4 of Definition 4.1.
*}

locale effective_redundancy_criterion = redundancy_criterion +
  assumes Ri_effective: "\<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> \<in> N \<union> Rf N \<Longrightarrow> \<gamma> \<in> Ri N"
begin

definition fair_clss_seq :: "'a clause set llist \<Rightarrow> bool" where
  "fair_clss_seq Ns \<longleftrightarrow> (let N' = llimit Ns - Rf (llimit Ns) in
     concls_of (inferences_from N' - Ri N') \<subseteq> lSup Ns \<union> Rf (lSup Ns))"

end

locale sat_preserving_effective_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" +
  effective_redundancy_criterion
begin

sublocale sat_preserving_redundancy_criterion ..

text {*
The result below corresponds to Theorem 4.3.

\begin{nit}
The case where $\gamma \in \mathcal{R}_{\mathcal{I}}(N_\infty \backslash
\mathcal{R}_{\mathcal{F}}(N_\infty))$ is not covered by the proof.
\end{nit}
*}

theorem fair_derive_saturated:
  assumes
    deriv: "derivation (op \<triangleright>) Ns" and
    fair: "fair_clss_seq Ns"
  shows "saturated_upto (llimit Ns)"
unfolding saturated_upto_def
proof
  fix \<gamma>
  let ?N' = "llimit Ns - Rf (llimit Ns)"
  assume \<gamma>: "\<gamma> \<in> inferences_from ?N'"
  show "\<gamma> \<in> Ri (llimit Ns)"
  proof (cases "\<gamma> \<in> Ri ?N'")
    case True
    thus ?thesis
      using Ri_mono by blast
  next
    case False
    have "concls_of (inferences_from ?N' - Ri ?N') \<subseteq> lSup Ns \<union> Rf (lSup Ns)"
      using fair unfolding fair_clss_seq_def Let_def .
    hence "concl_of \<gamma> \<in> lSup Ns \<union> Rf (lSup Ns)"
      using False \<gamma> by auto
    moreover
    { assume "concl_of \<gamma> \<in> lSup Ns"
      hence "\<gamma> \<in> Ri (lSup Ns)"
        using \<gamma> Ri_effective inferences_from_def by blast
      hence "\<gamma> \<in> Ri (llimit Ns)"
        using deriv Ri_lSup_subset_Ri_llimit by fast }
    moreover
    { assume "concl_of \<gamma> \<in> Rf (lSup Ns)"
      hence "concl_of \<gamma> \<in> Rf (llimit Ns)"
        using deriv Rf_lSup_subset_Rf_llimit by blast
      hence "\<gamma> \<in> Ri (llimit Ns)"
        using \<gamma> Ri_effective inferences_from_def by auto }
    ultimately show "\<gamma> \<in> Ri (llimit Ns)"
      by blast
  qed
qed

end

text {*
The following are minor results scattered through Section 4.1.
*}

locale trivial_redundancy_criterion = inference_system
begin

definition Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf _ = {}"

definition Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri N = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> concl_of \<gamma> \<in> N}"

sublocale effective_redundancy_criterion \<Gamma> Rf Ri
  by standard (auto simp: Rf_def Ri_def)

lemma saturated_upto_iff: "saturated_upto N \<longleftrightarrow> concls_of (inferences_from N) \<subseteq> N"
  unfolding saturated_upto_def inferences_from_def Rf_def Ri_def by auto

end

(* Some material from 4.1 page 38 *)

lemma standard_redundancy_criterion_extension:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms unfolding redundancy_criterion_def
  by (intro conjI) ((auto simp: rev_subsetD)[5], satx)

lemma standard_redundancy_criterion_extension_effective:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms unfolding effective_redundancy_criterion_def
  using standard_redundancy_criterion_extension[of \<Gamma>] 
  unfolding effective_redundancy_criterion_axioms_def
  by auto

lemma standard_redundancy_criterion_extension_fair_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and  "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion.fair_clss_seq \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) Ns \<longleftrightarrow> effective_redundancy_criterion.fair_clss_seq \<Gamma> Rf Ri Ns"
  using assms standard_redundancy_criterion_extension_effective[of \<Gamma> \<Gamma>' Rf Ri] assms(1) assms(2)
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma> Rf Ri Ns] 
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma>' Rf "(\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))" Ns]
  unfolding inference_system.inferences_from_def Let_def by auto

lemma standard_redundancy_criterion_extension_saturated_up_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion.saturated_upto \<Gamma> Rf Ri M \<longleftrightarrow> redundancy_criterion.saturated_upto \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) M"
  using assms redundancy_criterion.saturated_upto_def redundancy_criterion.saturated_upto_def standard_redundancy_criterion_extension
  unfolding inference_system.inferences_from_def
  by blast

end
