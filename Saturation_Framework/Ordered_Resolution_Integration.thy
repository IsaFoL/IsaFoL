(*  Title:       Ordered_Resolution_Integration
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Application of the saturation framework to Bachmair and Ganzinger's RP\<close>

theory Ordered_Resolution_Integration
  imports
    Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
    Saturation_Framework.Prover_Architectures
    Clausal_Inference_Systems
    Soundness_Related
begin


subsection \<open>Setup\<close>

no_notation true_lit (infix "|\<approx>\<approx>l" 50)
no_notation true_cls (infix "|\<approx>\<approx>" 50)
no_notation true_clss (infix "|\<approx>\<approx>s" 50)
no_notation true_cls_mset (infix "|\<approx>\<approx>m" 50)

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of
  Inference_System.concls_of Inference_System.infer_from

type_synonym 'a inference_RP = "'a Inference_System.inference"

abbreviation Infer_RP  :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a inference_RP" where
  "Infer_RP \<equiv> Inference_System.Infer"

abbreviation side_prems_of_RP :: "'a inference_RP \<Rightarrow> 'a clause multiset" where
  "side_prems_of_RP \<equiv> Inference_System.side_prems_of"

abbreviation main_prem_of_RP :: "'a inference_RP \<Rightarrow> 'a clause" where
  "main_prem_of_RP \<equiv> Inference_System.main_prem_of"

abbreviation concl_of_RP :: "'a inference_RP \<Rightarrow> 'a clause" where
  "concl_of_RP \<equiv> Inference_System.concl_of"

abbreviation prems_of_RP :: "'a inference_RP \<Rightarrow> 'a clause multiset" where
  "prems_of_RP \<equiv> Inference_System.prems_of"

abbreviation concls_of_RP :: "'a inference_RP set \<Rightarrow> 'a clause set" where
  "concls_of_RP \<equiv> Inference_System.concls_of"

abbreviation infer_from_RP :: "'a clause set \<Rightarrow> 'a inference_RP \<Rightarrow> bool" where
  "infer_from_RP \<equiv> Inference_System.infer_from"


subsection \<open>Library\<close>

lemma po_on_Empty_Order[simp]: "po_on Empty_Order UNIV"
  unfolding po_on_def irreflp_on_def transp_on_def by auto

lemma wfp_on_Empty_Order: "wfp_on Empty_Order UNIV"
  by simp

(* FIXME: needed? *)
lemma (in substitution) union_grounding_of_cls_ground: "is_ground_clss (\<Union> (grounding_of_cls ` N))"
  by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)


subsection \<open>Ground Layer\<close>

context FO_resolution_prover
begin

interpretation gr: ground_resolution_with_selection "S_M S M"
  using selection_axioms by unfold_locales (fact S_M_selects_subseteq S_M_selects_neg_lits)+

definition Inf_G :: "'a clause set \<Rightarrow> 'a clause inference set" where
  "Inf_G M = {Infer (CAs @ [DA]) E | CAs DA AAs As E. gr.ord_resolve M CAs DA AAs As E}"

lemma Inf_G_have_prems: "\<iota> \<in> Inf_G M \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_G_def by auto

lemma Inf_G_reductive: "\<iota> \<in> Inf_G M \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
  unfolding Inf_G_def by (auto dest: gr.ord_resolve_reductive)

interpretation G: sound_inference_system "Inf_G M" "{{#}}" "(|\<approx>\<approx>)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_G M"
  moreover
  {
    fix I
    assume I_ent_prems: "I |\<approx>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve M CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_G_def by auto
    then have "I |\<approx> concl_of \<iota>"
      using gr.ord_resolve_sound[of M CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_ent_prems Inf_G_have_prems i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) |\<approx>\<approx> {concl_of \<iota>}"
    by simp
qed

interpretation G: clausal_cex_red_inference_system "Inf_G M" "gr.INTERP M"
proof
  fix N D
  assume
    "{#} \<notin> N" and
    "D \<in> N" and
    "\<not> gr.INTERP M N |\<approx> D" and
    "\<And>C. C \<in> N \<Longrightarrow> \<not> gr.INTERP M N |\<approx> C \<Longrightarrow> D \<le> C"
  then obtain CAs AAs As E where
    "set CAs \<subseteq> N" and
    "gr.INTERP M N |\<approx>m mset CAs" and
    "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production M N CA \<noteq> {}" and
    "gr.ord_resolve M CAs D AAs As E" and
    "\<not> gr.INTERP M N |\<approx> E" and
    "E < D"
    using gr.ord_resolve_counterex_reducing by blast
  then show "\<exists>Cs E. set Cs \<subseteq> N \<and> gr.INTERP M N |\<approx>s set Cs \<and> Infer (Cs @ [D]) E \<in> Inf_G M
    \<and> \<not> gr.INTERP M N |\<approx> E \<and> E < D"
    unfolding Inf_G_def
    by (metis (mono_tags, lifting) gr.ex_min_counterex gr.productive_imp_INTERP mem_Collect_eq)
qed

interpretation G: clausal_cex_red_calculus_with_std_red_crit "Inf_G M" "gr.INTERP M"
  apply unfold_locales
  by (unfold_locales, fact Inf_G_have_prems, fact Inf_G_reductive)

interpretation G: static_refutational_complete_calculus "{{#}}" "Inf_G M" "(|\<approx>\<approx>)" "G.Red_Inf M"
  G.Red_F
  by unfold_locales (use G.clausal_saturated_complete in blast)


subsection \<open>First-Order Layer\<close>

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

lemmas \<G>_F = grounding_of_cls_def

definition \<G>_Inf :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf M \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G M}\<close>

definition Inf_F :: "'a clause inference set" where
  "Inf_F = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma Inf_F_have_prems: "\<iota> \<in> Inf_F \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_F_def by force

interpretation F: standard_lifting_with_red_crit_family Inf_F "{{#}}" UNIV Inf_G "\<lambda>N. (|\<approx>\<approx>)"
  G.Red_Inf "\<lambda>N. G.Red_F" "{{#}}" "\<lambda>N. \<G>_F" \<G>_Inf "\<lambda>D. Empty_Order"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation {{#}} (|\<approx>\<approx>)"
    by (fact consequence_relation_axioms)
next
  show "\<And>M. calculus_with_red_crit {{#}} (Inf_G M) (|\<approx>\<approx>) (G.Red_Inf M) G.Red_F"
    by (fact G.calculus_with_red_crit_axioms)
next
  show "\<And>M. lifting_with_wf_ordering_family {{#}} Inf_F {{#}} (|\<approx>\<approx>) (Inf_G M) (G.Red_Inf M) G.Red_F \<G>_F
    (\<G>_Inf M) (\<lambda>D. Empty_Order)"
    unfolding lifting_with_wf_ordering_family_def standard_lifting_def standard_lifting_axioms_def
  proof (intro allI impI conjI)
    show "\<And>M. calculus_with_red_crit {{#}} (Inf_G M) (|\<approx>\<approx>) (G.Red_Inf M) G.Red_F"
      by (fact G.calculus_with_red_crit_axioms)
  next
    show "{{#}} \<noteq> {}"
      by auto
  next
    fix B :: "'a clause"
    assume "B \<in> {{#}}"
    then show "\<G>_F B \<noteq> {}"
      unfolding \<G>_F by (simp add: ex_ground_subst)
  next
    fix B :: "'a clause"
    assume "B \<in> {{#}}"
    then show "\<G>_F B \<subseteq> {{#}}"
      unfolding \<G>_F using is_ground_cls_empty is_ground_subst_cls by blast
  next
    fix C
    assume "\<G>_F C \<inter> {{#}} \<noteq> {}"
    then show "C \<in> {{#}}"
      unfolding \<G>_F by auto
  next
    fix M \<iota>
    assume
      \<iota>_in: "\<iota> \<in> Inf_F" and
      g_inf_some: "\<G>_Inf M \<iota> \<noteq> None"

    show "the (\<G>_Inf M \<iota>) \<subseteq> G.Red_Inf M (\<G>_F (concl_of \<iota>))"
      unfolding \<G>_Inf_def G.Red_Inf_def G.redundant_infer_def
      apply clarsimp
      apply (rule_tac x = "{concl_of \<iota> \<cdot> \<rho>}" in exI)
      unfolding \<G>_F
      apply auto
      using Inf_G_reductive by fastforce
  next
    show "lifting_with_wf_ordering_family_axioms (\<lambda>D. Empty_Order)"
      unfolding lifting_with_wf_ordering_family_axioms_def minimal_element_def by simp
  qed
qed

notation F.entails_\<G>_Q (infix "|\<approx>\<approx>\<G>" 50)

lemma entails_\<G>_iff_Union_grounding_of_cls:
  "N1 |\<approx>\<approx>\<G> N2 \<longleftrightarrow> \<Union> (grounding_of_cls ` N1) |\<approx>\<approx> \<Union> (grounding_of_cls ` N2)"
  unfolding F.entails_\<G>_Q_def F.entails_\<G>_q_def F.\<G>_set_q_def image_def \<G>_F
  by (auto simp: true_clss_def)

lemma true_Union_grounding_of_cls_iff_true_all_interps_ground_substs:
  "I |\<approx>s (\<Union>C \<in> N. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N \<cdot>cs \<sigma>)"
  unfolding true_clss_def subst_clss_def by blast

lemma entails_\<G>_iff_all_interps_ground_substs:
  "N1 |\<approx>\<approx>\<G> N2 \<longleftrightarrow>
  (\<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N1 \<cdot>cs \<sigma>) \<longrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N2 \<cdot>cs \<sigma>))"
  unfolding F.entails_\<G>_Q_def F.entails_\<G>_q_def F.\<G>_set_q_def \<G>_F
    true_Union_grounding_of_cls_iff_true_all_interps_ground_substs by blast

interpretation F: sound_inference_system Inf_F "{{#}}" "(|\<approx>\<approx>\<G>)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_F"
  moreover
  {
    fix I \<eta>
    assume
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s set (prems_of \<iota>) \<cdot>cs \<sigma>" and
      \<eta>_gr: "is_ground_subst \<eta>"
    obtain CAs AAs As \<sigma> where
      the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>) AAs As \<sigma> (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_F_def by auto
    have prems: "mset (prems_of \<iota>) = mset (side_prems_of \<iota>) + {#main_prem_of \<iota>#}"
      by (metis Inf_F_have_prems[OF i_in] add.right_neutral append_Cons append_Nil2
          append_butlast_last_id mset.simps(2) mset_rev mset_single_iff_right rev_append
          rev_is_Nil_conv union_mset_add_mset_right)
    have "I |\<approx> concl_of \<iota> \<cdot> \<eta>"
      using ord_resolve_rename_sound[OF the_inf, of I \<eta>, OF _ \<eta>_gr]
      unfolding CAs prems[symmetric] using I_entails_prems
      by (metis set_mset_mset set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) |\<approx>\<approx>\<G> {concl_of \<iota>}"
    using entails_\<G>_iff_all_interps_ground_substs by auto
qed

lemma G_Inf_from_imp_F_Inf_from:
  "\<iota>\<^sub>0 \<in> G.Inf_from M (\<Union> (\<G>_F ` M)) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> F.Non_ground.Inf_from M \<and> \<iota>\<^sub>0 \<in> the (\<G>_Inf M \<iota>)"
proof -
  assume \<iota>\<^sub>0_in: "\<iota>\<^sub>0 \<in> G.Inf_from M (\<Union> (\<G>_F ` M))"
  have prems_\<iota>\<^sub>0_in: "set (prems_of \<iota>\<^sub>0) \<subseteq> \<Union> (\<G>_F ` M)"
    using \<iota>\<^sub>0_in unfolding G.Inf_from_def by simp
  have \<iota>\<^sub>0_Inf_G: \<open>\<iota>\<^sub>0 \<in> Inf_G M\<close>
    using \<iota>\<^sub>0_in unfolding G.Inf_from_def inference_system.Inf_from_def by blast
  then obtain CAs DA AAs As E where
    gr_res: \<open>gr.ord_resolve M CAs DA AAs As E\<close> and
    \<iota>\<^sub>0_is: \<open>\<iota>\<^sub>0 = Infer (CAs @ [DA]) E\<close>
    unfolding Inf_G_def by auto

  have CAs_in: \<open>set CAs \<subseteq> set (prems_of \<iota>\<^sub>0)\<close>
    by (simp add: \<iota>\<^sub>0_is subsetI)
  then have ground_CAs: \<open>is_ground_cls_list CAs\<close>
    using prems_\<iota>\<^sub>0_in union_grounding_of_cls_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_in: \<open>DA \<in> set (prems_of \<iota>\<^sub>0)\<close>
    using \<iota>\<^sub>0_is by simp
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_\<iota>\<^sub>0_in union_grounding_of_cls_ground is_ground_clss_def by auto
  obtain \<sigma> where
    grounded_res: \<open>ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
    using ground_ord_resolve_imp_ord_resolve[OF ground_DA ground_CAs
        gr.ground_resolution_with_selection_axioms gr_res] by auto
  have prems_ground: \<open>{DA} \<union> set CAs \<subseteq> grounding_of_clss M\<close>
    using prems_\<iota>\<^sub>0_in CAs_in DA_in unfolding grounding_of_clss_def by fast

  obtain \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    ground_n: "is_ground_subst \<eta>" and
    ground_ns: "is_ground_subst_list \<eta>s" and
    ground_n2: "is_ground_subst \<eta>2" and
    ngr_res: "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0" and
    CAs0_is: "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" and
    DA0_is: "DA0 \<cdot> \<eta> = DA" and
    E0_is: "E0 \<cdot> \<eta>2 = E"  and
    prems_in: "{DA0} \<union> set CAs0 \<subseteq> M" and
    len_CAs0: "length CAs0 = length CAs" and
    len_ns: "length \<eta>s = length CAs"
    using ord_resolve_rename_lifting[OF _ grounded_res selection_axioms prems_ground] sel_stable
    by smt

  have "length CAs0 = length \<eta>s"
    using len_CAs0 len_ns by simp
  then have \<iota>\<^sub>0_is': "\<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl (\<eta>s @ [\<eta>])) (E0 \<cdot> \<eta>2)"
    unfolding \<iota>\<^sub>0_is by (auto simp: CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric])

  define \<iota> :: "'a clause inference" where
    "\<iota> = Infer (CAs0 @ [DA0]) E0"

  have i_Inf_F: \<open>\<iota> \<in> Inf_F\<close>
    unfolding \<iota>_def Inf_F_def using ngr_res by auto

  have "\<exists>\<rho> \<rho>s. \<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>) \<and> is_ground_subst_list \<rho>s
    \<and> is_ground_subst \<rho> \<and> Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>) \<in> Inf_G M"
    by (rule exI[of _ \<eta>2], rule exI[of _ "\<eta>s @ [\<eta>]"], use ground_ns in
        \<open>auto intro: ground_n ground_n2 \<iota>\<^sub>0_Inf_G[unfolded \<iota>\<^sub>0_is']
           simp: \<iota>\<^sub>0_is' is_ground_subst_list_def\<close>)
  then have \<open>\<iota>\<^sub>0 \<in> the (\<G>_Inf M \<iota>)\<close>
    unfolding \<G>_Inf_def \<iota>_def CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric] by simp
  moreover have \<open>\<iota> \<in> F.Non_ground.Inf_from M\<close>
    using prems_in i_Inf_F unfolding F.Non_ground.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation F: static_refutational_complete_calculus "{{#}}" Inf_F "(|\<approx>\<approx>\<G>)" F.Red_Inf_\<G>_Q
  F.Red_F_\<G>_empty
proof (rule F.stat_ref_comp_to_non_ground_fam_inter; clarsimp)
  show "\<And>M. static_refutational_complete_calculus {{#}} (Inf_G M) (|\<approx>\<approx>) (G.Red_Inf M) G.Red_F"
    by (fact G.static_refutational_complete_calculus_axioms)
next
  fix M
  assume "F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated M"
  show "\<exists>q. F.Ground_family.Inf_from_q q (F.\<G>_set_q q M)
    \<subseteq> {\<iota>. \<exists>\<iota>' \<in> F.Non_ground.Inf_from M. (\<exists>y. \<G>_Inf q \<iota>' = Some y) \<and> \<iota> \<in> the (\<G>_Inf q \<iota>')} \<union>
                G.Red_Inf q (F.\<G>_set_q q M)"
    using G_Inf_from_imp_F_Inf_from
    apply auto
    apply (rule exI[of _ M])
    apply auto
    using F.Ground_family.Inf_from_q_def F.\<G>_set_q_def \<G>_Inf_def by fastforce
qed


subsection \<open>Given Clause Layer\<close>

datatype label =
  New
| Processed
| Old

definition Infer_FL_of :: "'a clause inference \<Rightarrow> ('a clause \<times> label) inference set" where
  "Infer_FL_of \<iota> = {Infer Cls (D, New) |Cls D. \<iota> = Infer (map fst Cls) D}"

definition Inf_FL :: "('a clause \<times> label) inference set" where
  "Inf_FL = (\<Union>\<iota> \<in> Inf_F. Infer_FL_of \<iota>)"

definition infer_of_FL :: "('a clause \<times> label) inference \<Rightarrow> 'a clause inference" where
  "infer_of_FL \<iota> = Infer (map fst (prems_of \<iota>)) (fst (concl_of \<iota>))"

abbreviation Equiv_F :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<doteq>" 50) where
  "C \<doteq> D \<equiv> generalizes C D \<and> generalizes D C"

abbreviation Prec_F :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) where
  "C \<prec>\<cdot> D \<equiv> strictly_generalizes C D"

fun Prec_l :: "label \<Rightarrow> label \<Rightarrow> bool" (infix "\<sqsubset>l" 50) where
  "Old \<sqsubset>l l \<longleftrightarrow> l \<noteq> Old"
| "Processed \<sqsubset>l l \<longleftrightarrow> l = New"
| "New \<sqsubset>l l \<longleftrightarrow> False"

lemma irrefl_Prec_l: "\<not> l \<sqsubset>l l"
  by (cases l) auto

lemma trans_Prec_l: "l1 \<sqsubset>l l2 \<Longrightarrow> l2 \<sqsubset>l l3 \<Longrightarrow> l1 \<sqsubset>l l3"
  by (cases l1; cases l2; cases l3) auto

lemma wf_Prec_l: "wfP (\<sqsubset>l)"
  by (metis Prec_l.elims(2) Prec_l.simps(3) not_accp_down wfP_accp_iff)

interpretation GC: Given_Clause "{{#}}" Inf_F "{{#}}" UNIV "\<lambda>N. (|\<approx>\<approx>)" Inf_G G.Red_Inf
  "\<lambda>N. G.Red_F" "\<lambda>N. \<G>_F" \<G>_Inf Inf_FL "(\<doteq>)" "(\<prec>\<cdot>)" "(\<sqsubset>l)" Old
proof (unfold_locales; (intro ballI)?)
  fix \<iota> and ls :: "label list"
  assume
    "\<iota> \<in> Inf_F"
    "length ls = length (prems_of \<iota>)"
  then show "\<exists>l. Infer (zip (prems_of \<iota>) ls) (concl_of \<iota>, l) \<in> Inf_FL"
    unfolding Inf_FL_def Infer_FL_of_def by force
next
  fix \<iota>
  assume "\<iota> \<in> Inf_FL"
  then show "Infer (map fst (prems_of \<iota>)) (fst (concl_of \<iota>)) \<in> Inf_F"
    unfolding Inf_FL_def Infer_FL_of_def by auto
next
  show "equivp (\<doteq>)"
    unfolding equivp_def by (meson generalizes_refl generalizes_trans)
next
  show "po_on (\<prec>\<cdot>) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def
    using strictly_generalizes_irrefl strictly_generalizes_trans by auto
next
  show "wfp_on (\<prec>\<cdot>) UNIV"
    unfolding wfp_on_UNIV by (metis wf_strictly_generalizes)
next
  show "po_on (\<sqsubset>l) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def using irrefl_Prec_l trans_Prec_l by blast
next
  show "wfp_on (\<sqsubset>l) UNIV"
    unfolding wfp_on_UNIV by (rule wf_Prec_l)
next
  fix C1 D1 C2 D2
  assume
    "C1 \<doteq> D1"
    "C2 \<doteq> D2"
    "C1 \<prec>\<cdot> C2"
  then show "D1 \<prec>\<cdot> D2"
    by (smt antisym size_mset_mono size_subst strictly_generalizes_def generalizes_def generalizes_trans)
next
  fix N C1 C2
  assume "C1 \<doteq> C2"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding generalizes_def \<G>_F
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_generalizes_def generalizes_def \<G>_F
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N
  show "F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N \<subseteq> Inf_F"
    using F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_to_Inf by blast
next
  fix B N
  assume
    "B \<in> {{#}}"
    "N |\<approx>\<approx>\<G> {B}"
  then show "N - F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N |\<approx>\<approx>\<G> {B}"
    by (metis (no_types, lifting) F.Red_F_\<G>_empty_def
        F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q_def
        F.inter_calc calculus_with_red_crit.Red_F_Bot)
next
  fix N N' :: "'a clause set"
  assume "N \<subseteq> N'"
  then show "F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N
    \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N'"
    by (simp add: F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_F_of_subset)
next
  fix N N' :: "'a clause set"
  assume "N \<subseteq> N'"
  then show "F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N
    \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N'"
    by (simp add: F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_of_subset)
next
  fix N' N
  assume "N' \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N"
  then show "F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N
    \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q (N - N')"
    by (simp add: F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_F_of_Red_F_subset)
next
  fix N' N
  assume "N' \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N"
  then show "F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N
    \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q (N - N')"
    by (simp add: F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_of_Red_F_subset)
next
  fix \<iota> N
  assume
    "\<iota> \<in> Inf_F"
    "concl_of \<iota> \<in> N"
  then show "\<iota> \<in> F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N"
    by (simp add: F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_of_Inf_to_N)
next
  fix B N
  assume
    bot: "B \<in> {{#}}" and
    satur: "F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N" and
    unsat: "N |\<approx>\<approx>\<G> {B}"
  show "\<exists>B' \<in> {{#}}. B' \<in> N"
    (* FIXME: Clean up. *)
    apply (rule F.static_refutational_complete[OF bot _ unsat])
    unfolding F.lifted_calc_w_red_crit.saturated_def
    using satur unfolding F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated_def
      F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q_def F.Red_Inf_\<G>_Q_def by blast
next
  fix \<iota>
  assume "\<iota> \<in> Inf_F"
  then show "prems_of \<iota> \<noteq> []"
    by (simp add: Inf_F_have_prems)
next
  fix l
  assume "l \<noteq> Old"
  then show "Prec_l Old l"
    by simp
next
  show "\<exists>l. Prec_l Old l"
    using Prec_l.simps(1) by blast
next
  fix \<iota>
  assume "\<iota> \<in> Inf_FL"
  then show "snd (concl_of \<iota>) \<noteq> Old"
    unfolding Inf_FL_def Infer_FL_of_def by auto
qed

notation GC.Prec_FL (infix "\<sqsubset>" 50)
notation GC.step (infix "\<Longrightarrow>GC" 50)

abbreviation derive_GC (infix "\<rhd>RedFL" 50) where
  "Nl1 \<rhd>RedFL Nl2 \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.derive Nl1 Nl2"

abbreviation saturated_GC :: "('a clause \<times> label) set \<Rightarrow> bool" where
  "saturated_GC \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.saturated"

abbreviation Red_Inf_Q_GC :: "('a clause \<times> label) set \<Rightarrow> ('a clause \<times> label) inference set" where
  "Red_Inf_Q_GC \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_Inf_Q"

abbreviation Red_F_Q_GC :: "('a clause \<times> label) set \<Rightarrow> ('a clause \<times> label) set" where
  "Red_F_Q_GC \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_F_Q"

lemmas derive_GC_simps = GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.derive.simps
lemmas saturated_GC_def = GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.saturated_def
lemmas Red_Inf_Q_GC_def = GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_Inf_Q_def
lemmas Red_F_Q_GC_def = GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_F_Q_def

lemma Red_F_Q_GC_eq:
  "Red_F_Q_GC N =
   {C. \<forall>D \<in> \<G>_F (fst C).
      D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N)) \<or> (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F (fst E))}"
  unfolding GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_F_Q_def
    GC.labeled_ord_red_crit_fam.Red_F_\<G>_q_g_def GC.labeled_ord_red_crit_fam.\<G>_set_q_def
    GC.\<G>_F_L_q_def
  by auto

lemma mem_Red_F_Q_GC_because_G_Red_F:
  "(\<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N))) \<Longrightarrow> Cl \<in> Red_F_Q_GC N"
  unfolding Red_F_Q_GC_eq by auto

lemma mem_Red_F_Q_GC_because_Prec_FL:
  "(\<forall>D \<in> \<G>_F (fst Cl). \<exists>El \<in> N. El \<sqsubset> Cl \<and> D \<in> \<G>_F (fst El)) \<Longrightarrow> Cl \<in> Red_F_Q_GC N"
  unfolding Red_F_Q_GC_eq by auto

lemma F_Red_Inf_\<G>_Q_eq:
  "F.Red_Inf_\<G>_Q N =
   {\<iota> \<in> Inf_F. \<forall>M.
      \<G>_Inf M \<iota> \<noteq> None \<and> the (\<G>_Inf M \<iota>) \<subseteq> G.Red_Inf M (\<Union> (\<G>_F ` N))
      \<or> \<G>_Inf M \<iota> = None \<and> \<G>_F (concl_of \<iota>) \<subseteq> \<Union> (\<G>_F ` N) \<union> G.Red_F (\<Union> (\<G>_F ` N))}"
  unfolding F.Red_Inf_\<G>_Q_def F.Red_Inf_\<G>_q_def F.\<G>_set_q_def by auto

lemma mem_F_Red_Inf_\<G>_Q_eq_because_G_Red_Inf:
  "\<iota> \<in> Inf_F \<Longrightarrow>
  (\<forall>M. \<G>_Inf M \<iota> \<noteq> None \<and> the (\<G>_Inf M \<iota>) \<subseteq> G.Red_Inf M (\<Union> (\<G>_F ` N))) \<Longrightarrow>
  \<iota> \<in> F.Red_Inf_\<G>_Q N"
  unfolding F_Red_Inf_\<G>_Q_eq by auto


subsection \<open>RP Layer\<close>

interpretation sq: selection "S_Q Sts"
  unfolding S_Q_def using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gd: ground_resolution_with_selection "S_Q Sts"
  by unfold_locales

interpretation src: standard_redundancy_criterion_reductive "gd.ord_\<Gamma> Sts"
  by unfold_locales

interpretation src: standard_redundancy_criterion_counterex_reducing "gd.ord_\<Gamma> Sts"
  "ground_resolution_with_selection.INTERP (S_Q Sts)"
  by unfold_locales

definition lclss_of_state :: "'a state \<Rightarrow> ('a clause \<times> label) set" where
  "lclss_of_state St \<equiv>
   (\<lambda>C. (C, New)) ` N_of_state St \<union> (\<lambda>C. (C, Processed)) ` P_of_state St
   \<union> (\<lambda>C. (C, Old)) ` Q_of_state St"

lemma insert_lclss_of_state[simp]:
  "insert (C, New) (lclss_of_state (N, P, Q)) = lclss_of_state (N \<union> {C}, P, Q)"
  "insert (C, Processed) (lclss_of_state (N, P, Q)) = lclss_of_state (N, P \<union> {C}, Q)"
  "insert (C, Old) (lclss_of_state (N, P, Q)) = lclss_of_state (N, P, Q \<union> {C})"
  unfolding lclss_of_state_def image_def by auto

lemma union_lclss_of_state[simp]:
  "lclss_of_state (N1, P1, Q1) \<union> lclss_of_state (N2, P2, Q2) =
   lclss_of_state (N1 \<union> N2, P1 \<union> P2, Q1 \<union> Q2)"
  unfolding lclss_of_state_def by auto

lemma mem_lclss_of_state[simp]:
  "(C, New) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> N"
  "(C, Processed) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> P"
  "(C, Old) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> Q"
  unfolding lclss_of_state_def image_def by auto

definition RP_infer_of :: "'a clause inference \<Rightarrow> 'a inference_RP" where
  "RP_infer_of \<iota> = Infer_RP (mset (side_prems_of \<iota>)) (main_prem_of \<iota>) (concl_of \<iota>)"

definition infer_of_RP :: "'a inference_RP \<Rightarrow> 'a clause inference" where
  "infer_of_RP \<iota> = Infer (list_of_mset (side_prems_of_RP \<iota>) @ [main_prem_of_RP \<iota>]) (concl_of_RP \<iota>)"

lemma gc_subsumption_step:
  assumes
    d_in: "Dl \<in> N" and
    d_sub_c: "strictly_subsumes (fst Dl) (fst Cl) \<or> subsumes (fst Dl) (fst Cl) \<and> snd Dl \<sqsubset>l snd Cl"
  shows "N \<union> {Cl} \<Longrightarrow>GC N"
proof -
  have d_sub'_c: "Cl \<in> Red_F_Q_GC {Dl} \<or> Dl \<sqsubset> Cl"
  proof (cases "size (fst Dl) = size (fst Cl)")
    case True
    then have "Dl \<sqsubset> Cl"
      apply (unfold GC.Prec_FL_def Prover_Architecture_Basis.Prec_FL_def)
      apply (unfold generalizes_def strictly_generalizes_def)
      using d_sub_c
      apply (unfold strictly_subsumes_def subsumes_def)
      by (metis size_subst subset_mset.order_refl subseteq_mset_size_eql)
    then show ?thesis
      by (rule disjI2)
  next
    case False
    then have d_ssub_c: "strictly_subsumes (fst Dl) (fst Cl)"
      using d_sub_c
      apply (unfold strictly_subsumes_def subsumes_def)
      by (metis size_subst strict_subset_subst_strictly_subsumes strictly_subsumes_antisym subset_mset.antisym_conv2)
    have "Cl \<in> Red_F_Q_GC {Dl}"
      apply (rule mem_Red_F_Q_GC_because_G_Red_F)
      apply (unfold G.Red_F_def)
      apply clarsimp
      using d_ssub_c
      apply (unfold strictly_subsumes_def subsumes_def)
      apply clarsimp
      unfolding \<G>_F
      apply clarsimp
      apply (rule_tac x = "{fst Dl \<cdot> \<sigma> \<cdot> \<sigma>'}" in exI)
      apply auto
      apply (metis is_ground_comp_subst subst_cls_comp_subst)
      unfolding true_clss_def true_cls_def
      apply clarsimp
      apply (meson Melem_subst_cls mset_subset_eqD)
      by (metis False size_subst subset_imp_less_mset subset_mset.le_less subst_subset_mono)
    then show ?thesis
      by (rule disjI1)
  qed
  show ?thesis
    apply (rule GC.step.process[of _ N "{Cl}" _ "{}"])
       apply auto
    using d_sub'_c unfolding Red_F_Q_GC_eq
     apply auto
    apply (metis (no_types, lifting) G.Red_F_of_subset SUP_upper d_in subset_iff)
      apply (smt GC.Prec_FL_def GC.equiv_F_grounding GC.prec_F_grounding UNIV_witness d_in in_mono)
    by (simp add: GC.active_subset_def)+
qed

lemma gc_reduction_step:
  assumes
    passiv: "snd Dl \<noteq> Old" and
    d_sub_c: "fst Dl \<subset># fst Cl"
  shows "N \<union> {Cl} \<Longrightarrow>GC N \<union> {Dl}"
proof (rule GC.step.process[of _ N "{Cl}" _ "{Dl}"])
  have "Cl \<in> Red_F_Q_GC {Dl}"
    apply (rule mem_Red_F_Q_GC_because_G_Red_F)
    apply (unfold G.Red_F_def)
    apply clarsimp
    unfolding \<G>_F
    apply clarsimp
    apply (rule_tac x = "{fst Dl \<cdot> \<sigma>}" in exI)
    apply auto
    using subst_subset_mono[OF d_sub_c]
    using true_clss_subclause
     apply fast
    using subst_subset_mono[OF d_sub_c]
    by (simp add: subset_imp_less_mset)
  then show "{Cl} \<subseteq> Red_F_Q_GC (N \<union> {Dl})"
    using GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_F_of_subset by blast
qed (auto simp: GC.active_subset_def passiv)

lemma gc_processing_step: "N \<union> {(C, New)} \<Longrightarrow>GC N \<union> {(C, Processed)}"
proof (rule GC.step.process[of _ N "{(C, New)}" _ "{(C, Processed)}"])
  have "(C, New) \<in> Red_F_Q_GC {(C, Processed)}"
    apply (rule mem_Red_F_Q_GC_because_Prec_FL)
    unfolding GC.Prec_FL_def
    apply auto
    by (simp add: generalizes_refl)
  then show "{(C, New)} \<subseteq> Red_F_Q_GC (N \<union> {(C, Processed)})"
    using GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_F_of_subset by blast
qed (auto simp: GC.active_subset_def)

lemma RP_inferences_between_eq_F_Inf_from2:
  "concl_of_RP ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C =
   concl_of ` F.Non_ground.Inf_from2 N {C}" (is "?rp = ?f")
proof (intro set_eqI iffI)
  fix E
  assume e_in: "E \<in> concl_of_RP ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C"

  obtain CAs DA AAs As \<sigma> where
    e_res: "ord_resolve_rename S CAs DA AAs As \<sigma> E" and
    cd_sub: "set CAs \<union> {DA} \<subseteq> N \<union> {C}" and
    c_in: "C \<in> set CAs \<union> {DA}"
    using e_in
    unfolding inference_system.inferences_between_def infer_from_def ord_FO_\<Gamma>_def
    apply auto
    done

  show "E \<in> concl_of ` F.Non_ground.Inf_from2 N {C}"
    unfolding F.Non_ground.Inf_from2_alt F.Non_ground.Inf_from_def Inf_F_def
      inference_system.Inf_from2_alt inference_system.Inf_from_def
    apply (auto simp: image_def Bex_def)
    apply (rule_tac x = "Infer (CAs @ [DA]) E" in exI)
    apply auto
    using e_res cd_sub c_in apply auto done
next
  fix E
  assume e_in: "E \<in> concl_of ` F.Non_ground.Inf_from2 N {C}"

  obtain CAs DA AAs As \<sigma> where
    e_res: "ord_resolve_rename S CAs DA AAs As \<sigma> E" and
    cd_sub: "set CAs \<union> {DA} \<subseteq> N \<union> {C}" and
    c_in: "C \<in> set CAs \<union> {DA}"
    using e_in
    unfolding F.Non_ground.Inf_from2_alt F.Non_ground.Inf_from_def Inf_F_def
      inference_system.Inf_from2_alt inference_system.Inf_from_def
    apply (auto simp: image_def Bex_def)
    done

  show "E \<in> concl_of_RP ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C"
    unfolding inference_system.inferences_between_def infer_from_def ord_FO_\<Gamma>_def
    using e_res cd_sub c_in
    apply (clarsimp simp: image_def Bex_def)
    apply (rule_tac x = "Infer_RP (mset CAs) DA E" in exI)
    apply auto
    done
qed

lemma gc_inference_step:
  assumes
    l_ne: "l \<noteq> Old" and
    m_passiv: "GC.active_subset M = {}" and
    m_sup: "fst ` M \<supseteq> concl_of_RP ` inference_system.inferences_between (ord_FO_\<Gamma> S)
      (fst ` GC.active_subset N) C"
  shows "N \<union> {(C, l)} \<Longrightarrow>GC N \<union> {(C, Old)} \<union> M"
proof (rule GC.step.infer[of _ N C l _ M])
  have m_sup': "fst ` M \<supseteq> concl_of ` F.Non_ground.Inf_from2 (fst ` GC.active_subset N) {C}"
    using m_sup unfolding RP_inferences_between_eq_F_Inf_from2 .

  show "F.Non_ground.Inf_from2 (fst ` GC.active_subset N) {C}
    \<subseteq> F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q (fst ` (N \<union> {(C, Old)} \<union> M))"
    unfolding F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q_def F.Red_Inf_\<G>_Q_def[symmetric]
  proof
    fix \<iota>
    assume \<iota>_in_if2: "\<iota> \<in> F.Non_ground.Inf_from2 (fst ` GC.active_subset N) {C}"

    have \<iota>_in: "\<iota> \<in> Inf_F"
      using \<iota>_in_if2 unfolding F.Non_ground.Inf_from2_def F.Non_ground.Inf_from_def by auto

    have "concl_of \<iota> \<in> fst ` M"
      using m_sup'
      apply (auto simp: image_def Collect_mono_iff F.Non_ground.Inf_from2_alt)
      using \<iota>_in_if2 m_sup' by auto
    then have "concl_of \<iota> \<in> fst ` (N \<union> {(C, Old)} \<union> M)"
      by auto
    then show "\<iota> \<in> F.Red_Inf_\<G>_Q (fst ` (N \<union> {(C, Old)} \<union> M))"
      by (rule F.Red_Inf_of_Inf_to_N[OF \<iota>_in])
  qed
qed (use l_ne m_passiv in auto)

lemma step_RP_imp_GC_step: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<Longrightarrow>GC lclss_of_state St'"
proof (induction rule: RP.induct)
  case (tautology_deletion A C N P Q)
  note tauto = this

  have c\<theta>_red:
    "C\<theta> \<in> G.Red_F (\<Union>D \<in> N'. \<G>_F (fst D))" if in_g: "C\<theta> \<in> \<G>_F C"
    for N' :: "('a clause \<times> label) set" and C\<theta>
  proof -
    obtain \<theta> where
      "C\<theta> = C \<cdot> \<theta>"
       using in_g unfolding \<G>_F by blast
    then have compl_lits:
      "Neg (A \<cdot>a \<theta>) \<in># C\<theta>"
      "Pos (A \<cdot>a \<theta>) \<in># C\<theta>"
      using tauto Neg_Melem_subst_atm_subst_cls Pos_Melem_subst_atm_subst_cls by auto
    then have "{} |\<approx>\<approx> {C\<theta>}"
      unfolding true_clss_def true_cls_def true_lit_def if_distrib_fun
      by (metis (full_types) literal.disc(1,2) literal.sel(1,2) singletonD)
    then show ?thesis
      unfolding G.Red_F_def
      apply clarsimp
      apply (rule exI[of _ "{}"])
      apply clarsimp
      done
  qed

  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, New)}" _ "{}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    apply (rule mem_Red_F_Q_GC_because_G_Red_F)
    apply (unfold image_Un image_comp[of fst])
    apply (unfold image_Un[symmetric])
    apply simp
    using c\<theta>_red[of _ "lclss_of_state (N, P, Q)"] unfolding lclss_of_state_def
    by auto
next
  case (forward_subsumption D P Q C N)
  note d_in = this(1) and d_sub_c = this(2)
  show ?case
  proof (cases "D \<in> P")
    case True
    then show ?thesis
      using gc_subsumption_step[of "(D, Processed)" "lclss_of_state (N, P, Q)" "(C, New)"] d_sub_c
      by auto
  next
    case False
    then have "D \<in> Q"
      using d_in by simp
    then show ?thesis
      using gc_subsumption_step[of "(D, Old)" "lclss_of_state (N, P, Q)" "(C, New)"] d_sub_c by auto
  qed
next
  case (backward_subsumption_P D N C P Q)
  note d_in = this(1) and d_ssub_c = this(2)
  then show ?case
    using gc_subsumption_step[of "(D, New)" "lclss_of_state (N, P, Q)" "(C, Processed)"] d_ssub_c
    by auto
next
  case (backward_subsumption_Q D N C P Q)
  note d_in = this(1) and d_ssub_c = this(2)
  then show ?case
    using gc_subsumption_step[of "(D, New)" "lclss_of_state (N, P, Q)" "(C, Old)"] d_ssub_c by auto
next
  case (forward_reduction D L' P Q L \<sigma> C N)
  show ?case
    using gc_reduction_step[of "(C, New)" "(C + {#L#}, New)" "lclss_of_state (N, P, Q)"] by auto
next
  case (backward_reduction_P D L' N L \<sigma> C P Q)
  show ?case
    using gc_reduction_step[of "(C, Processed)" "(C + {#L#}, Processed)" "lclss_of_state (N, P, Q)"]
    by auto
next
  case (backward_reduction_Q D L' N L \<sigma> C P Q)
  show ?case
    using gc_reduction_step[of "(C, Processed)" "(C + {#L#}, Old)" "lclss_of_state (N, P, Q)"]
    by auto
next
  case (clause_processing N C P Q)
  show ?case
    using gc_processing_step[of "lclss_of_state (N, P, Q)" C] by auto
next
  case (inference_computation N Q C P)
  note n = this(1)
  show ?case
    apply (auto simp: GC.active_subset_def)
    apply (rule gc_inference_step[of Processed "lclss_of_state (N, {}, {})" "lclss_of_state ({}, P, Q)" C,
        simplified])
    unfolding n apply (auto simp: GC.active_subset_def)
    unfolding inference_system.inferences_between_def image_def mem_Collect_eq lclss_of_state_def
      infer_from_def
    apply auto
    done
qed                                               

lemma step_RP_imp_step: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<rhd>RedFL lclss_of_state St'"
  by (rule GC.one_step_equiv) (rule step_RP_imp_GC_step)

lemma derivation_RP_imp_derivation: "chain (\<leadsto>) Sts \<Longrightarrow> chain (\<rhd>RedFL) (lmap lclss_of_state Sts)"
  using chain_lmap step_RP_imp_step by blast


lemma lclss_Liminf_commute:
  "lclss_of_state (Liminf_state Sts) = Liminf_llist (lmap lclss_of_state Sts)"
  unfolding Liminf_state_def lclss_of_state_def Liminf_llist_def image_def
  apply auto
  sorry




lemma fair_RP_imp_fair:
  assumes
    nnul: "\<not> lnull Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows
    "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}" and
    "GC.non_active_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
proof -
  show "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}"
    using empty_Q0 unfolding GC.active_subset_def
    using nnul
    apply (cases Sts)
    apply auto
    done
next
  show "GC.non_active_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
    using fair unfolding fair_state_seq_def GC.non_active_subset_def
    apply auto
    unfolding lclss_Liminf_commute[symmetric]
    by (metis (no_types, lifting) Liminf_state_def N_of_state_Liminf P_of_state_Liminf empty_iff
        label.exhaust mem_lclss_of_state(1) mem_lclss_of_state(2))
qed

lemma saturated_GC_imp_saturated_F:
  assumes "saturated_GC Nl"
  shows "F.saturated (fst ` Nl)"
  sorry
(*
proof
  assume gc_satur: "saturated_GC Nl"

  show "F.saturated (fst ` Nl)"
    unfolding F.saturated_def
  proof
    fix \<iota>
    assume "\<iota> \<in> F.Non_ground.Inf_from (fst ` Nl)"

    have "\<iota> \<in> infer_of_FL ` GC.with_labels.Inf_from Nl"
      sorry
    then have "\<iota> \<in> infer_of_FL ` GC.labeled_ord_red_crit_fam.Red_Inf_\<G>_Q Nl"
      using gc_satur unfolding saturated_GC_def by auto
    then show "\<iota> \<in> F.Red_Inf_\<G>_Q (fst ` Nl)"
      unfolding GC.labeled_ord_red_crit_fam.Red_Inf_\<G>_Q_def
        GC.labeled_ord_red_crit_fam.Red_Inf_\<G>_q_def F.Red_Inf_\<G>_Q_def
      sorry
  qed
next
  assume f_satur: "F.saturated (fst ` Nl)"
  show "saturated_GC Nl"
    unfolding GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.saturated_def
  proof
    fix \<iota>
    assume "\<iota> \<in> GC.with_labels.Inf_from Nl"
    show "\<iota> \<in> GC.labeled_ord_red_crit_fam.Red_Inf_\<G>_Q Nl"
      sorry
  qed
qed
*)

(*
  unfolding GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.saturated_def
    GC.with_labels.Inf_from_def
    F.saturated_def
    F.Non_ground.Inf_from_def
  apply (subst Inf_FL_def)
  apply (subst Inf_F_def)
  apply clarsimp
  sorry
*)

lemma saturated_imp_saturated_RP:
  assumes satur_gc: "saturated_GC (Liminf_llist (lmap lclss_of_state Sts))"
  shows "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  unfolding src.saturated_upto_def
proof -
  fix \<iota>

  define Nls where
    "Nls = lmap lclss_of_state Sts"
  define Ns where
    "Ns = lmap clss_of_state Sts"
  define gSts where
    "gSts = lmap grounding_of_state Sts"

  have lmap_fst_nls: "lmap ((`) fst) Nls = Ns"
    unfolding Nls_def Ns_def lclss_of_state_def by (simp add: llist.map_comp image_Un image_comp)

  have satur_f: "F.saturated (Liminf_llist Ns)"
    sorry
(*
    by (rule saturated_F_mono[OF image_Liminf_llist_subset, of fst Nls, unfolded lmap_fst_nls])
      (rule saturated_GC_imp_saturated_F[OF satur_gc, folded Nls_def])
*)

  have "F.Non_ground.Inf_from (Liminf_llist Ns) \<subseteq> F.Red_Inf_\<G>_Q (Liminf_llist Ns)"
    sorry

  term "src.Ri Sts (Liminf_llist gSts)"


  show "gd.inferences_from Sts (Liminf_llist gSts - src.Rf (Liminf_llist gSts))
    \<subseteq> src.Ri Sts (Liminf_llist gSts)"

    sorry
qed

theorem RP_sound_w_satur_frmwk:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "\<not> satisfiable (grounding_of_state (lhd Sts))"
  sorry
(*
proof -
  from assms have "{#} \<in> grounding_of_state (Liminf_state Sts)"
    unfolding grounding_of_clss_def by (force intro: ex_ground_subst)
  then have "{#} \<in> Liminf_llist (lmap grounding_of_state Sts)"
    using grounding_of_state_Liminf_state_subseteq by auto
  then have "\<not> satisfiable (Liminf_llist (lmap grounding_of_state Sts))"
    using true_clss_def by auto
  then have "\<not> satisfiable (lhd (lmap grounding_of_state Sts))"
    using sr_ext.sat_limit_iff ground_derive_chain deriv by blast
  then show ?thesis
    using chain_not_lnull deriv by fastforce
qed
*)

theorem RP_saturated_if_fair_w_satur_frmwk:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  apply (rule saturated_imp_saturated_RP)
  apply (rule GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit.fair_implies_Liminf_saturated)
  apply (rule derivation_RP_imp_derivation[OF deriv])
  using fair_RP_imp_fair[OF chain_not_lnull[OF deriv] fair empty_Q0]
  using GC.gc_fair step_RP_imp_GC_step chain_lmap deriv by blast

corollary RP_complete_if_fair_w_satur_frmwk:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}" and
    unsat: "\<not> satisfiable (grounding_of_state (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof -
  have "\<not> satisfiable (Liminf_llist (lmap grounding_of_state Sts))"
    sorry
  moreover have "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
    sorry
  ultimately have "{#} \<in> Liminf_llist (lmap grounding_of_state Sts)"
    sorry
  then show ?thesis
    using empty_clause_in_Q_of_Liminf_state[OF deriv fair] by auto
qed

end
