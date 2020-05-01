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


subsection \<open>Library\<close>

lemma po_on_Empty_Order[simp]: "po_on Empty_Order UNIV"
  unfolding po_on_def irreflp_on_def transp_on_def by auto

lemma wfp_on_Empty_Order: "wfp_on Empty_Order UNIV"
  by simp

(* FIXME: needed? *)
lemma (in substitution) union_grounding_of_cls_ground: "is_ground_clss (\<Union> (grounding_of_cls ` N))"
  by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)


subsection \<open>Setup\<close>

no_notation true_lit (infix "\<Turnstile>l" 50)
no_notation true_cls (infix "\<Turnstile>" 50)
no_notation true_clss (infix "\<Turnstile>s" 50)
no_notation true_cls_mset (infix "\<Turnstile>m" 50)

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of


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

abbreviation Bot :: "'a clause set" where
  "Bot \<equiv> {{#}}"

definition entails_G (infix "\<Turnstile>" 50) where
  "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>I. I |\<approx>s N1 \<longrightarrow> I |\<approx>s N2)"

interpretation G: clausal_consequence_relation Bot "(\<Turnstile>)"
  by unfold_locales (auto simp: entails_G_def)

interpretation G: sound_inference_system "Inf_G M" Bot "(\<Turnstile>)"
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
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile> {concl_of \<iota>}"
    unfolding entails_G_def by simp
qed

interpretation G: clausal_cex_red_inference_system "(\<Turnstile>)" Bot "Inf_G M" "gr.INTERP M"
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

interpretation G: clausal_cex_red_calculus_with_std_red_crit Bot "(\<Turnstile>)" "Inf_G M" "gr.INTERP M"
  by (unfold_locales, fact Inf_G_have_prems, fact Inf_G_reductive)

interpretation G: static_refutational_complete_calculus Bot "Inf_G M" "(\<Turnstile>)" "G.Red_Inf M" G.Red_F
  by unfold_locales (use G.clausal_saturated_complete entails_G_def in blast)


subsection \<open>First-Order Layer\<close>

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

definition \<G>_Inf :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf M \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G M}\<close>

definition Inf_F :: "'a clause inference set" where
  "Inf_F = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma Inf_F_have_prems: "\<iota> \<in> Inf_F \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_F_def by force

interpretation F: standard_lifting_with_red_crit_family Inf_F Bot UNIV Inf_G "\<lambda>N. (\<Turnstile>)" G.Red_Inf
  "\<lambda>N. G.Red_F" Bot "\<lambda>N. \<G>_F" \<G>_Inf "\<lambda>D. Empty_Order"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation Bot (\<Turnstile>)"
    by (fact G.consequence_relation_axioms)
next
  show "\<And>M. calculus_with_red_crit Bot (Inf_G M) (\<Turnstile>) (G.Red_Inf M) G.Red_F"
    by (fact G.calculus_with_red_crit_axioms)
next
  show "\<And>M. lifting_with_wf_ordering_family Bot Inf_F Bot (\<Turnstile>) (Inf_G M) (G.Red_Inf M) G.Red_F \<G>_F
    (\<G>_Inf M) (\<lambda>D. Empty_Order)"
    unfolding lifting_with_wf_ordering_family_def standard_lifting_def standard_lifting_axioms_def
  proof (intro allI impI conjI)
    show "\<And>M. calculus_with_red_crit Bot (Inf_G M) (\<Turnstile>) (G.Red_Inf M) G.Red_F"
      by (fact G.calculus_with_red_crit_axioms)
  next
    show "Bot \<noteq> {}"
      by auto
  next
    fix B
    assume "B \<in> Bot"
    then show "\<G>_F B \<noteq> {}"
      unfolding grounding_of_cls_def by (simp add: ex_ground_subst)
  next
    fix B
    assume "B \<in> Bot"
    then show "\<G>_F B \<subseteq> Bot"
      unfolding grounding_of_cls_def using is_ground_cls_empty is_ground_subst_cls by blast
  next
    fix C
    assume "\<G>_F C \<inter> Bot \<noteq> {}"
    then show "C \<in> Bot"
      unfolding grounding_of_cls_def by auto
  next
    fix M \<iota>
    assume
      \<iota>_in: "\<iota> \<in> Inf_F" and
      g_inf_some: "\<G>_Inf M \<iota> \<noteq> None"

    (* FIXME: Clean up *)
    show "the (\<G>_Inf M \<iota>) \<subseteq> G.Red_Inf M (\<G>_F (concl_of \<iota>))"
      unfolding \<G>_Inf_def G.Red_Inf_def G.redundant_infer_def
      apply clarsimp
      apply (rule_tac x = "{concl_of \<iota> \<cdot> \<rho>}" in exI)
      unfolding grounding_of_cls_def
      apply auto
       apply (simp add: G.subset_entailed)
      using Inf_G_reductive by fastforce
  next
    show "lifting_with_wf_ordering_family_axioms (\<lambda>D. Empty_Order)"
      unfolding lifting_with_wf_ordering_family_axioms_def minimal_element_def by simp
  qed
qed

notation F.entails_\<G>_Q (infix "\<Turnstile>\<G>" 50)

lemma entails_\<G>_iff_Union_grounding_of_cls:
  "N1 \<Turnstile>\<G> N2 \<longleftrightarrow> \<Union> (grounding_of_cls ` N1) \<Turnstile> \<Union> (grounding_of_cls ` N2)"
  unfolding F.entails_\<G>_Q_def F.entails_\<G>_q_def F.\<G>_set_q_def entails_G_def image_def
    grounding_of_cls_def
  by (auto simp: true_clss_def)

lemma true_Union_grounding_of_cls_iff_true_all_interps_ground_substs:
  "I |\<approx>s (\<Union>C \<in> N. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N \<cdot>cs \<sigma>)"
  unfolding true_clss_def subst_clss_def by blast

lemma entails_\<G>_iff_all_interps_ground_substs:
  "N1 \<Turnstile>\<G> N2 \<longleftrightarrow>
  (\<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N1 \<cdot>cs \<sigma>) \<longrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N2 \<cdot>cs \<sigma>))"
  unfolding F.entails_\<G>_Q_def F.entails_\<G>_q_def F.\<G>_set_q_def entails_G_def
    grounding_of_cls_def true_Union_grounding_of_cls_iff_true_all_interps_ground_substs by blast

interpretation F: sound_inference_system Inf_F Bot "(\<Turnstile>\<G>)"
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
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile>\<G> {concl_of \<iota>}"
    using entails_\<G>_iff_all_interps_ground_substs by auto
qed

(* FIXME: Needed below? *)
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

interpretation F: static_refutational_complete_calculus Bot Inf_F "(\<Turnstile>\<G>)" F.Red_Inf_\<G>_Q
  F.Red_F_\<G>_empty
proof (rule F.stat_ref_comp_to_non_ground_fam_inter; clarsimp)
  show "\<And>M. static_refutational_complete_calculus Bot (Inf_G M) (\<Turnstile>) (G.Red_Inf M) G.Red_F"
    by (fact G.static_refutational_complete_calculus_axioms)
next
  fix M
  assume "F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated M"
  show "\<exists>q. F.Ground_family.Inf_from_q q (F.\<G>_set_q q M)
    \<subseteq> {\<iota>. \<exists>\<iota>' \<in> F.Non_ground.Inf_from M. (\<exists>y. \<G>_Inf q \<iota>' = Some y) \<and> \<iota> \<in> the (\<G>_Inf q \<iota>')} \<union>
                G.Red_Inf q (F.\<G>_set_q q M)"
    using G_Inf_from_imp_F_Inf_from
    (* FIXME: Clean up proof. *)
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

definition Inf_FL :: "('a clause \<times> label) inference set" where
  "Inf_FL = {Infer (zip Cs Ls) (D, New) |Cs D Ls. Infer Cs D \<in> Inf_F \<and> length Ls = length Cs}"

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

interpretation FL: labeled_lifting_with_red_crit_family Bot Inf_F Bot UNIV
  "\<lambda>N. (\<Turnstile>)" Inf_G G.Red_Inf "\<lambda>N. G.Red_F" "\<lambda>N. \<G>_F" \<G>_Inf Inf_FL
proof
  fix \<iota> and ls :: "label list"
  assume
    "\<iota> \<in> Inf_F"
    "length ls = length (prems_of \<iota>)"
  then show "\<exists>l. Infer (zip (prems_of \<iota>) ls) (concl_of \<iota>, l) \<in> Inf_FL"
    unfolding Inf_FL_def by force
next
  fix \<iota>
  assume "\<iota> \<in> Inf_FL"
  then show "Infer (map fst (prems_of \<iota>)) (fst (concl_of \<iota>)) \<in> Inf_F"
    unfolding Inf_FL_def by auto
qed

notation FL.entails_\<G>_L_Q (infix "\<Turnstile>\<G>L" 50)
notation FL.with_labels.inter_red_crit_calculus.derive (infix "\<rhd>RedFL" 50)

abbreviation saturated_FL :: "('a clause \<times> label) set \<Rightarrow> bool" where
  "saturated_FL \<equiv> FL.with_labels.inter_red_crit_calculus.saturated"

abbreviation fair_FL :: "('a clause \<times> label) set llist \<Rightarrow> bool" where
  "fair_FL \<equiv> FL.with_labels.inter_red_crit_calculus.fair"

interpretation GC: Given_Clause Bot Inf_F Bot UNIV "\<lambda>N. (\<Turnstile>)" Inf_G G.Red_Inf "\<lambda>N. G.Red_F"
  "\<lambda>N. \<G>_F" \<G>_Inf Inf_FL "(\<doteq>)" "(\<prec>\<cdot>)" "(\<sqsubset>l)" Old
proof (unfold_locales; (intro ballI)?)
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
    unfolding generalizes_def grounding_of_cls_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_generalizes_def generalizes_def grounding_of_cls_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N
  show "F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N \<subseteq> Inf_F"
    using F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_to_Inf by blast
next
  fix B N
  assume
    "B \<in> Bot"
    "N \<Turnstile>\<G> {B}"
  then show "N - F.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q N \<Turnstile>\<G> {B}"
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
    bot: "B \<in> Bot" and
    satur: "F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N" and
    unsat: "N \<Turnstile>\<G> {B}"
  show "\<exists>B' \<in> Bot. B' \<in> N"
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
    unfolding Inf_FL_def by auto
qed

notation GC.step (infix "\<Longrightarrow>GC" 50)

abbreviation Red_Inf_Q_GC :: "('a clause \<times> label) set \<Rightarrow> ('a clause \<times> label) inference set" where
  "Red_Inf_Q_GC \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_Inf_Q"

abbreviation Red_F_Q_GC :: "('a clause \<times> label) set \<Rightarrow> ('a clause \<times> label) set" where
  "Red_F_Q_GC \<equiv> GC.labeled_ord_red_crit_fam.lifted_calc_w_red_crit_family.Red_F_Q"


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

lemma RP_step_imp_GC_step: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<Longrightarrow>GC lclss_of_state St'"
proof (induction rule: RP.induct)
  case (tautology_deletion A C N P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, New)}" _ "{}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (forward_subsumption D P Q C N)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, New)}" _ "{}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (backward_subsumption_P D N C P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, Processed)}" _ "{}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (backward_subsumption_Q D N C P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, Old)}" _ "{}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (forward_reduction D L' P Q L \<sigma> C N)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C + {#L#}, New)}" _ "{(C, New)}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (backward_reduction_P D L' N L \<sigma> C P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C + {#L#}, Processed)}" _ "{(C, Processed)}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (backward_reduction_Q D L' N L \<sigma> C P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C + {#L#}, Old)}" _ "{(C, Processed)}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (clause_processing N C P Q)
  show ?case
    apply (rule GC.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, New)}" _ "{(C, Processed)}"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
next
  case (inference_computation N Q C P)
  show ?case
    apply (rule GC.step.infer[of _ "lclss_of_state ({}, P, Q)" C Processed _ "lclss_of_state (N, {}, {})"])
    apply (auto simp: lclss_of_state_def GC.active_subset_def)
    sorry
qed

lemma RP_step_imp_LF_step: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<rhd>RedFL lclss_of_state St'"
  sorry

lemma RP_derivation_imp_LF_derivation: "chain (\<leadsto>) Sts \<Longrightarrow> chain (\<rhd>RedFL) (lmap lclss_of_state Sts)"
  using chain_lmap RP_step_imp_LF_step by blast

lemma RP_fair_imp_LF_fair:
  assumes
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows "fair_FL (lmap lclss_of_state Sts)"
  sorry

lemma GC_saturated_imp_LF_saturated:
  "saturated_FL (Liminf_llist (lmap lclss_of_state Sts)) \<Longrightarrow>
   src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  sorry

theorem RP_saturated_if_fair_w_satur_frmwk:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  by (rule GC_saturated_imp_LF_saturated)
    (intro FL.with_labels.inter_red_crit_calculus.fair_implies_Liminf_saturated
      RP_derivation_imp_LF_derivation[OF deriv]
      RP_fair_imp_LF_fair[OF fair empty_Q0])

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
