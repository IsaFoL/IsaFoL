(*  Title:       Given Clause Procedure
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2019
*)

section "Given Clause Procedure"

theory Given_Clause
  imports Redundancy_Criterion_Family_Extensions
begin

locale Given_Clause_Proc = labeled_lifting_equiv Bot_F Inf_F Bot_G Q entails_q Inf_G Red_Inf_q
  Red_F_q \<G>_F_q \<G>_Inf_q l Inf_FL
  for
    Bot_F :: "'f set"
    and Inf_F :: "'f inference set"
    and Bot_G :: "'g set"
    and Q :: "'q set"
    and entails_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set \<Rightarrow> bool)"
    and Inf_G :: \<open>'g inference set\<close>
    and Red_Inf_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g inference set)"
    and Red_F_q :: "'q \<Rightarrow> ('g set \<Rightarrow> 'g set)"
    and \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" 
    and \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set"
    and l :: "'l itself"
    and Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  + fixes
    Equiv_F :: "('f \<times> 'f) set" and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<lless>" 50) and (* In the report, the symbol used points in the opposite direction *)
    Prec_l :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<sqsubset>l" 50)
  assumes
    equiv_F_is_equiv_rel: "equiv UNIV Equiv_F" and
    wf_prec_F: "minimal_element (Prec_F) UNIV" and
    wf_prec_l: "minimal_element (Prec_l) UNIV" and
    compat_equiv_prec: "(C1,D1) \<in> equiv_F \<Longrightarrow> (C2,D2) \<in> equiv_F \<Longrightarrow> C1 \<lless> C2 \<Longrightarrow> D1 \<lless> D2" and
    equiv_F_grounding: "q \<in> Q \<Longrightarrow> (C1,C2) \<in> equiv_F \<Longrightarrow> \<G>_F_q q C1 = \<G>_F_q q C2" and
    prec_F_grounding: "q \<in> Q \<Longrightarrow> C1 \<lless> C2 \<Longrightarrow> \<G>_F_q q C1 \<subseteq> \<G>_F_q q C2" and
    static_ref_comp: "static_refutational_complete_calculus Bot_F Inf_F (\<Turnstile>\<inter>)
      no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q
      no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q"
begin

definition equiv_F_fun :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) where
  "equiv_F_fun C D \<equiv> (C,D) \<in> Equiv_F"

definition Prec_eq_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<lless>\<doteq>" 50) where
  "Prec_eq_F C D \<equiv> ((C,D) \<in> Equiv_F \<or> C \<lless> D)"

definition Prec_FL :: "('f \<times> 'l) \<Rightarrow> ('f \<times> 'l) \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "Prec_FL Cl1 Cl2 \<equiv> (fst Cl1 \<lless> fst Cl2) \<or> (fst Cl1 \<doteq> fst Cl2 \<and> snd Cl1 \<sqsubset>l snd Cl2)"

lemma wf_prec_FL: "minimal_element (\<sqsubset>) UNIV"
proof
  show "po_on (\<sqsubset>) UNIV" unfolding po_on_def
  proof
    show "irreflp_on (\<sqsubset>) UNIV" unfolding irreflp_on_def Prec_FL_def
    proof
      fix a
      assume a_in: "a \<in> (UNIV::('f \<times> 'l) set)"
      have "\<not> (fst a \<lless> fst a)" using wf_prec_F minimal_element.min_elt_ex by force
      moreover have "\<not> (snd a \<sqsubset>l snd a)" using wf_prec_l minimal_element.min_elt_ex by force
      ultimately show "\<not> (fst a \<lless> fst a \<or> fst a \<doteq> fst a \<and> snd a \<sqsubset>l snd a)" by blast
    qed
  next
    show "transp_on (\<sqsubset>) UNIV" unfolding transp_on_def Prec_FL_def
    proof (simp, intro allI impI)
      fix a1 b1 a2 b2 a3 b3
      assume trans_hyp:"(a1 \<lless> a2 \<or> a1 \<doteq> a2 \<and> b1 \<sqsubset>l b2) \<and> (a2 \<lless> a3 \<or> a2 \<doteq> a3 \<and> b2 \<sqsubset>l b3)"
      have "a1 \<lless> a2 \<Longrightarrow> a2 \<lless> a3 \<Longrightarrow> a1 \<lless> a3" using wf_prec_F compat_equiv_prec by blast
      moreover have "a1 \<lless> a2 \<Longrightarrow> a2 \<doteq> a3 \<Longrightarrow> a1 \<lless> a3" using wf_prec_F compat_equiv_prec by blast
      moreover have "a1 \<doteq> a2 \<Longrightarrow> a2 \<lless> a3 \<Longrightarrow> a1 \<lless> a3" using wf_prec_F compat_equiv_prec by blast
      moreover have "b1 \<sqsubset>l b2 \<Longrightarrow> b2 \<sqsubset>l b3 \<Longrightarrow> b1 \<sqsubset>l b3"
        using wf_prec_l unfolding minimal_element_def po_on_def transp_on_def by (meson UNIV_I)
      moreover have "a1 \<doteq> a2 \<Longrightarrow> a2 \<doteq> a3 \<Longrightarrow> a1 \<doteq> a3"
        using equiv_F_is_equiv_rel equiv_class_eq unfolding equiv_F_fun_def by fastforce
      ultimately show "(a1 \<lless> a3 \<or> a1 \<doteq> a3 \<and> b1 \<sqsubset>l b3)" using trans_hyp by blast
    qed
  qed
next
  show "wfp_on (\<sqsubset>) UNIV" unfolding wfp_on_def 
  proof
    assume contra: "\<exists>f. \<forall>i. f i \<in> UNIV \<and> f (Suc i) \<sqsubset> f i"
    then obtain f where f_in: "\<forall>i. f i \<in> UNIV" and f_suc: "\<forall>i. f (Suc i) \<sqsubset> f i" by blast
    define f_F where "f_F = (\<lambda>i. fst (f i))"
    define f_L where "f_L = (\<lambda>i. snd (f i))"
    have uni_F: "\<forall>i. f_F i \<in> UNIV" using f_in by simp
    have uni_L: "\<forall>i. f_L i \<in> UNIV" using f_in by simp
    have decomp: "\<forall>i. f_F (Suc i) \<lless> f_F i \<or> f_L (Suc i) \<sqsubset>l f_L i"
      using f_suc unfolding Prec_FL_def f_F_def f_L_def by blast
    define I_F where "I_F = { i |i. f_F (Suc i) \<lless> f_F i}"
    define I_L where "I_L = { i |i. f_L (Suc i) \<sqsubset>l f_L i}"
    have "I_F \<union> I_L = UNIV" using decomp unfolding I_F_def I_L_def by blast
    then have "finite I_F \<Longrightarrow> \<not> finite I_L" by (metis finite_UnI infinite_UNIV_nat)
    moreover have "infinite I_F \<Longrightarrow> \<exists>f. \<forall>i. f i \<in> UNIV \<and> f (Suc i) \<lless> f i"
      using uni_F unfolding I_F_def by (meson compat_equiv_prec iso_tuple_UNIV_I not_finite_existsD)
    moreover have "infinite I_L \<Longrightarrow> \<exists>f. \<forall>i. f i \<in> UNIV \<and> f (Suc i) \<sqsubset>l f i"
      using uni_L unfolding I_L_def
      by (metis UNIV_I compat_equiv_prec decomp minimal_element_def wf_prec_F wfp_on_def)
    ultimately show False using wf_prec_F wf_prec_l by (metis minimal_element_def wfp_on_def)
  qed
qed

lemma labeled_static_ref_comp:
  "static_refutational_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<inter>L) with_labels.Red_Inf_Q with_labels.Red_F_Q"
  using labeled_static_ref[OF static_ref_comp] .

lemma standard_labeled_lifting_family: "q \<in> Q \<Longrightarrow> lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G (entails_q q) Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q) (\<lambda>g. Prec_FL)"
proof -
  fix q
  assume q_in: "q \<in> Q"
  have "lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G (entails_q q) Inf_G
    (Red_Inf_q q) (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q) (\<lambda>g. Labeled_Empty_Order)"
    using ord_fam_lifted_q[OF q_in] .
  then have "standard_lifting Bot_FL Inf_FL Bot_G Inf_G (entails_q q) (Red_Inf_q q) (Red_F_q q)
    (\<G>_F_L_q q) (\<G>_Inf_L_q q)"
    using lifted_q q_in by blast
  then show "lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G (entails_q q) Inf_G (Red_Inf_q q) (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q) (\<lambda>g. Prec_FL)"
    using wf_prec_FL
    by (simp add: lifting_with_wf_ordering_family.intro lifting_with_wf_ordering_family_axioms.intro)
qed

sublocale labeled_ord_red_crit_fam: lifting_equivalence_with_red_crit_family Inf_FL Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q
  Bot_FL \<G>_F_L_q \<G>_Inf_L_q "\<lambda>g. Prec_FL"
  using standard_labeled_lifting_family no_labels.Q_not_empty
    no_labels.Ground_family.calculus_with_red_crit_family_axioms
  by (simp add: lifting_equivalence_with_red_crit_family.intro lifting_equivalence_with_red_crit_family_axioms.intro)

lemma entail_equiv: "labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.entails_Q N1 N2 = (N1 \<Turnstile>\<inter>L N2)"
  unfolding labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.entails_Q_def
    entails_\<G>_L_Q_def entails_\<G>_L_q_def labeled_ord_red_crit_fam.entails_\<G>_q_def
     labeled_ord_red_crit_fam.\<G>_set_q_def \<G>_set_L_q_def
  by simp 

lemma entail_equiv2: "labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.entails_Q = (\<Turnstile>\<inter>L)"
  using entail_equiv by auto

lemma red_inf_equiv: "labeled_ord_red_crit_fam.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N = with_labels.Red_Inf_Q N"
  unfolding labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_Inf_Q_def
    with_labels.Red_Inf_Q_def labeled_ord_red_crit_fam.Red_Inf_\<G>_q_def Red_Inf_\<G>_L_q_def
    labeled_ord_red_crit_fam.\<G>_set_q_def \<G>_set_L_q_def
  by simp

lemma red_inf_equiv2: "labeled_ord_red_crit_fam.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q =
  with_labels.Red_Inf_Q"
  using red_inf_equiv by auto

lemma empty_red_f_equiv: "labeled_ord_red_crit_fam.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N =
  with_labels.Red_F_Q N"
  unfolding labeled_ord_red_crit_fam.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q_def
    with_labels.Red_F_Q_def labeled_ord_red_crit_fam.Red_F_\<G>_empty_q_def Red_F_\<G>_empty_L_q_def
    labeled_ord_red_crit_fam.\<G>_set_q_def \<G>_set_L_q_def Empty_Order_def Labeled_Empty_Order_def
  by simp

lemma empty_red_f_equiv2: "labeled_ord_red_crit_fam.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q = with_labels.Red_F_Q"
  using empty_red_f_equiv by auto

lemma labeled_ordered_static_ref_comp: "static_refutational_complete_calculus Bot_FL Inf_FL labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.entails_Q labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_Inf_Q labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_F_Q"
  using labeled_ord_red_crit_fam.static_empty_ord_inter_equiv_static_inter empty_red_f_equiv2 red_inf_equiv2
    entail_equiv2 labeled_static_ref_comp
  by argo 

end

end

