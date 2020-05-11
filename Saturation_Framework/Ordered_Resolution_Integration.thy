(*  Title:       Ordered_Resolution_Integration
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Application of the saturation framework to Bachmair and Ganzinger's RP\<close>

theory Ordered_Resolution_Integration
  imports
    Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
    Saturation_Framework.Prover_Architectures
    Clausal_Inference_Systems
    Soundness
begin


subsection \<open>Setup\<close>

no_notation true_lit (infix "\<Turnstile>l" 50)
no_notation true_cls (infix "\<Turnstile>" 50)
no_notation true_clss (infix "\<Turnstile>s" 50)
no_notation true_cls_mset (infix "\<Turnstile>m" 50)

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of
  Inference_System.concls_of Inference_System.infer_from

type_synonym 'a inference_RP = "'a Inference_System.inference"

abbreviation Infer_RP :: "'a clause multiset \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a inference_RP" where
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

lemma po_on_empty_rel[simp]: "po_on (\<lambda>_ _. False) UNIV"
  unfolding po_on_def irreflp_on_def transp_on_def by auto

(* FIXME: needed? *)
lemma (in substitution) union_grounding_of_cls_ground: "is_ground_clss (\<Union> (grounding_of_cls ` N))"
  by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)


subsection \<open>Ground Layer\<close>

context FO_resolution_prover
begin

interpretation gr: ground_resolution_with_selection "S_M S M"
  using selection_axioms by unfold_locales (fact S_M_selects_subseteq S_M_selects_neg_lits)+

definition Inf_G :: "'a clause set \<Rightarrow> 'a clause inference set" where
  "Inf_G M = {Infer (CAs @ [DA]) E |CAs DA AAs As E. gr.ord_resolve M CAs DA AAs As E}"

lemma Inf_G_have_prems: "\<iota> \<in> Inf_G M \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_G_def by auto

lemma Inf_G_reductive: "\<iota> \<in> Inf_G M \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
  unfolding Inf_G_def by (auto dest: gr.ord_resolve_reductive)

interpretation G: sound_inference_system "Inf_G M" "{{#}}" "(\<TTurnstile>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_G M"
  moreover
  {
    fix I
    assume I_ent_prems: "I \<TTurnstile>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve M CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_G_def by auto
    then have "I \<TTurnstile> concl_of \<iota>"
      using gr.ord_resolve_sound[of M CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_ent_prems Inf_G_have_prems i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
    by simp
qed

interpretation G: clausal_cex_red_inference_system "Inf_G M" "gr.INTERP M"
proof
  fix N D
  assume
    "{#} \<notin> N" and
    "D \<in> N" and
    "\<not> gr.INTERP M N \<TTurnstile> D" and
    "\<And>C. C \<in> N \<Longrightarrow> \<not> gr.INTERP M N \<TTurnstile> C \<Longrightarrow> D \<le> C"
  then obtain CAs AAs As E where
    "set CAs \<subseteq> N" and
    "gr.INTERP M N \<TTurnstile>m mset CAs" and
    "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production M N CA \<noteq> {}" and
    "gr.ord_resolve M CAs D AAs As E" and
    "\<not> gr.INTERP M N \<TTurnstile> E" and
    "E < D"
    using gr.ord_resolve_counterex_reducing by blast
  then show "\<exists>Cs E. set Cs \<subseteq> N \<and> gr.INTERP M N \<TTurnstile>s set Cs \<and> Infer (Cs @ [D]) E \<in> Inf_G M
    \<and> \<not> gr.INTERP M N \<TTurnstile> E \<and> E < D"
    unfolding Inf_G_def
    by (metis (mono_tags, lifting) gr.ex_min_counterex gr.productive_imp_INTERP mem_Collect_eq)
qed

interpretation G: clausal_cex_red_calculus_with_std_red_crit "Inf_G M" "gr.INTERP M"
  by (unfold_locales, fact Inf_G_have_prems, fact Inf_G_reductive)

abbreviation derive_G (infix "\<rhd>RedG" 50) where
  "(\<rhd>RedG) \<equiv> G.derive"

interpretation G: static_refutational_complete_calculus "{{#}}" "Inf_G M" "(\<TTurnstile>e)" "G.Red_Inf M"
  G.Red_F
  by unfold_locales (use G.clausal_saturated_complete in blast)


subsection \<open>First-Order Layer\<close>

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

lemmas \<G>_F_def = grounding_of_cls_def

definition \<G>_Inf :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf M \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G M}\<close>

definition Inf_F :: "'a clause inference set" where
  "Inf_F = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma Inf_F_have_prems: "\<iota> \<in> Inf_F \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_F_def by force

interpretation F: standard_lifting_with_red_crit_family Inf_F "{{#}}" UNIV Inf_G "\<lambda>N. (\<TTurnstile>e)"
  G.Red_Inf "\<lambda>N. G.Red_F" "{{#}}" "\<lambda>N. \<G>_F" \<G>_Inf "\<lambda>D C C'. False"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation {{#}} (\<TTurnstile>e)"
    by (fact consequence_relation_axioms)
next
  show "\<And>M. calculus_with_red_crit {{#}} (Inf_G M) (\<TTurnstile>e) (G.Red_Inf M) G.Red_F"
    by (fact G.calculus_with_red_crit_axioms)
next
  show "\<And>M. lifting_with_wf_ordering_family {{#}} Inf_F {{#}} (\<TTurnstile>e) (Inf_G M) (G.Red_Inf M)
    G.Red_F \<G>_F (\<G>_Inf M) (\<lambda>D C C'. False)"
    unfolding lifting_with_wf_ordering_family_def standard_lifting_def standard_lifting_axioms_def
  proof (intro allI impI conjI)
    show "\<And>M. calculus_with_red_crit {{#}} (Inf_G M) (\<TTurnstile>e) (G.Red_Inf M) G.Red_F"
      by (fact G.calculus_with_red_crit_axioms)
  next
    show "{{#}} \<noteq> {}"
      by auto
  next
    fix B :: "'a clause"
    assume "B \<in> {{#}}"
    then show "\<G>_F B \<noteq> {}"
      unfolding \<G>_F_def by (simp add: ex_ground_subst)
  next
    fix B :: "'a clause"
    assume "B \<in> {{#}}"
    then show "\<G>_F B \<subseteq> {{#}}"
      unfolding \<G>_F_def using is_ground_cls_empty is_ground_subst_cls by blast
  next
    fix C
    assume "\<G>_F C \<inter> {{#}} \<noteq> {}"
    then show "C \<in> {{#}}"
      unfolding \<G>_F_def by auto
  next
    fix M \<iota>
    assume
      \<iota>_in: "\<iota> \<in> Inf_F" and
      g_inf_some: "\<G>_Inf M \<iota> \<noteq> None"

    show "the (\<G>_Inf M \<iota>) \<subseteq> G.Red_Inf M (\<G>_F (concl_of \<iota>))"
      unfolding \<G>_Inf_def G.Red_Inf_def G.redundant_infer_def
      apply clarsimp
      apply (rule_tac x = "{concl_of \<iota> \<cdot> \<rho>}" in exI)
      unfolding \<G>_F_def
      apply auto
      using Inf_G_reductive by fastforce
  next
    show "lifting_with_wf_ordering_family_axioms (\<lambda>D C C'. False)"
      unfolding lifting_with_wf_ordering_family_axioms_def minimal_element_def by simp
  qed
qed

notation F.entails_\<G>_Q (infix "\<TTurnstile>\<G>e" 50)

lemma F_entails_\<G>_Q_iff: "N1 \<TTurnstile>\<G>e N2 \<longleftrightarrow> \<Union> (\<G>_F ` N1) \<TTurnstile>e \<Union> (\<G>_F ` N2)"
  unfolding F.entails_\<G>_Q_def by simp

lemma true_Union_grounding_of_cls_iff_true_all_interps_ground_substs:
  "I \<TTurnstile>s (\<Union>C \<in> N. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s N \<cdot>cs \<sigma>)"
  unfolding true_clss_def subst_clss_def by blast

interpretation F: sound_inference_system Inf_F "{{#}}" "(\<TTurnstile>\<G>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_F"
  moreover
  {
    fix I \<eta>
    assume
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s set (prems_of \<iota>) \<cdot>cs \<sigma>" and
      \<eta>_gr: "is_ground_subst \<eta>"
    obtain CAs AAs As \<sigma> where
      the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>) AAs As \<sigma> (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_F_def by auto
    have prems: "mset (prems_of \<iota>) = mset (side_prems_of \<iota>) + {#main_prem_of \<iota>#}"
      by (metis (no_types) Inf_F_have_prems[OF i_in] add.right_neutral append_Cons append_Nil2
          append_butlast_last_id mset.simps(2) mset_rev mset_single_iff_right rev_append
          rev_is_Nil_conv union_mset_add_mset_right)
    have "I \<TTurnstile> concl_of \<iota> \<cdot> \<eta>"
      using ord_resolve_rename_sound[OF the_inf, of I \<eta>, OF _ \<eta>_gr]
      unfolding CAs prems[symmetric] using I_entails_prems
      by (metis set_mset_mset set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>\<G>e {concl_of \<iota>}"
    unfolding F.entails_\<G>_Q_def \<G>_F_def
      true_Union_grounding_of_cls_iff_true_all_interps_ground_substs
    by auto
qed

lemma G_Inf_from_imp_F_Inf_from:
  "\<iota>\<^sub>0 \<in> G.Inf_from M (\<Union> (\<G>_F ` M)) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> F.Inf_from M \<and> \<iota>\<^sub>0 \<in> the (\<G>_Inf M \<iota>)"
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
  moreover have \<open>\<iota> \<in> F.Inf_from M\<close>
    using prems_in i_Inf_F unfolding F.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation F: static_refutational_complete_calculus "{{#}}" Inf_F "(\<TTurnstile>\<G>e)" F.Red_Inf_\<G>_Q
  F.Red_F_\<G>_empty
proof (rule F.stat_ref_comp_to_non_ground_fam_inter; clarsimp)
  show "\<And>M. static_refutational_complete_calculus {{#}} (Inf_G M) (\<TTurnstile>e) (G.Red_Inf M) G.Red_F"
    by (fact G.static_refutational_complete_calculus_axioms)
next
  fix M
  assume "F.saturated M"
  show "\<exists>q. F.ground.Inf_from_q q (F.\<G>_set_q q M)
    \<subseteq> {\<iota>. \<exists>\<iota>' \<in> F.Inf_from M. (\<exists>y. \<G>_Inf q \<iota>' = Some y) \<and> \<iota> \<in> the (\<G>_Inf q \<iota>')}
      \<union> G.Red_Inf q (F.\<G>_set_q q M)"
    using G_Inf_from_imp_F_Inf_from
    apply auto
    apply (rule exI[of _ M])
    apply auto
    using F.ground.Inf_from_q_def \<G>_Inf_def by fastforce
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

(* TODO: Break down *)
interpretation GC: Given_Clause "{{#}}" Inf_F "{{#}}" UNIV "\<lambda>N. (\<TTurnstile>e)" Inf_G G.Red_Inf
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
    unfolding generalizes_def \<G>_F_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_generalizes_def generalizes_def \<G>_F_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
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
notation GC.entails_\<G>_L_Q (infix "\<TTurnstile>\<G>Le" 50)
notation GC.step (infix "\<Longrightarrow>GC" 50)

lemmas GC_entails_\<G>_L_Q_iff = GC.labeled_entailment_lifting

abbreviation derive_GC (infix "\<rhd>RedFL" 50) where
  "(\<rhd>RedFL) \<equiv> GC.derive"

lemma GC_Red_F_Q_eq:
  "GC.Red_F_Q N =
   {C. \<forall>D \<in> \<G>_F (fst C).
      D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N)) \<or> (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F (fst E))}"
  unfolding GC.Red_F_Q_def GC.Red_F_\<G>_q_g_def by auto

lemma mem_GC_Red_F_Q_because_G_Red_F:
  "(\<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N))) \<Longrightarrow> Cl \<in> GC.Red_F_Q N"
  unfolding GC_Red_F_Q_eq by auto

lemma mem_GC_Red_F_Q_because_Prec_FL:
  "(\<forall>D \<in> \<G>_F (fst Cl). \<exists>El \<in> N. El \<sqsubset> Cl \<and> D \<in> \<G>_F (fst El)) \<Longrightarrow> Cl \<in> GC.Red_F_Q N"
  unfolding GC_Red_F_Q_eq by auto

interpretation GC: refute_compact_consequence_relation GC.Bot_FL "(\<TTurnstile>\<G>Le)"
proof
  fix CCl
  assume unsat: "CCl \<TTurnstile>\<G>Le GC.Bot_FL"

  let ?bot = "({#}, undefined)"

  have "CCl \<TTurnstile>\<G>Le {?bot}"
    using unsat
    apply (subst (asm) GC.entail_set_all_formulas)
    by auto
  then have "\<not> satisfiable (\<Union>CL \<in> CCl. \<G>_F (fst CL))"
    unfolding GC_entails_\<G>_L_Q_iff F_entails_\<G>_Q_iff by auto
  then obtain DD where
    d_sub: "DD \<subseteq> (\<Union>Cl \<in> CCl. \<G>_F (fst Cl))" and
    d_fin: "finite DD" and
    d_unsat: "\<forall>I. \<not> I \<TTurnstile>s DD"
    unfolding clausal_logic_compact[of "\<Union>CL \<in> CCl. \<G>_F (fst CL)"] by blast

  define CCl' :: "('a clause \<times> label) set" where
    "CCl' = {SOME Cl. Cl \<in> CCl \<and> D \<in> \<G>_F (fst Cl) |D. D \<in> DD}"

  have ex_in_cl: "\<exists>Cl. Cl \<in> CCl \<and> D \<in> \<G>_F (fst Cl)" if "D \<in> DD" for D
    using that d_sub by blast
  then have "DD \<subseteq> (\<Union>Cl \<in> CCl'. \<G>_F (fst Cl))"
    using ex_in_cl unfolding CCl'_def
    apply auto
    by (metis (no_types, lifting) eq_fst_iff ex_in_cl someI_ex)
  have "CCl' \<subseteq> CCl"
    unfolding CCl'_def
    apply clarsimp
    using someI_ex[OF ex_in_cl]
    by blast
  moreover have "finite CCl'"
    unfolding CCl'_def using d_fin by simp
  moreover have "CCl' \<TTurnstile>\<G>Le GC.Bot_FL"
    unfolding CCl'_def using d_unsat ex_in_cl
    by (metis (no_types, lifting) CCl'_def GC.entails_\<G>_L_Q_def \<open>DD \<subseteq> (\<Union>Cl\<in>CCl'. \<G>_F (fst Cl))\<close> subsetD true_clss_def)
  ultimately show "\<exists>CCl' \<subseteq> CCl. finite CCl' \<and> CCl' \<TTurnstile>\<G>Le GC.Bot_FL"
    by blast
qed

interpretation GC: refute_compact_calculus_with_red_crit GC.Bot_FL Inf_FL "(\<TTurnstile>\<G>Le)" GC.Red_Inf_Q
  GC.Red_F_Q
  ..

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
  "lclss_of_state St =
   (\<lambda>C. (C, New)) ` N_of_state St \<union> (\<lambda>C. (C, Processed)) ` P_of_state St
   \<union> (\<lambda>C. (C, Old)) ` Q_of_state St"

lemma image_fst_lclss_of_state[simp]: "fst ` lclss_of_state St = clss_of_state St"
  unfolding lclss_of_state_def by (auto simp: image_Un image_comp)

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

lemma lclss_Liminf_commute:
  "Liminf_llist (lmap lclss_of_state Sts) = lclss_of_state (Liminf_state Sts)"
  apply (rule sym)
  apply (subst (2) lclss_of_state_def[abs_def])
  apply (subst Liminf_llist_lmap_union)
  defer
  apply (subst Liminf_llist_lmap_union)
  defer
  apply (subst (1 2 3) Liminf_llist_lmap_image)
       defer
       defer
       defer
  unfolding lclss_of_state_def Liminf_state_def
  apply auto
  apply (meson Pair_inject inj_onI)+
  done

definition infer_RP_of :: "'a clause inference \<Rightarrow> 'a inference_RP" where
  "infer_RP_of \<iota> = Infer_RP (mset (side_prems_of \<iota>)) (main_prem_of \<iota>) (concl_of \<iota>)"

(* FIXME: list_of_mset hyperresolution
definition infer_of_RP :: "'a inference_RP \<Rightarrow> 'a clause inference" where
  "infer_of_RP \<iota> = Infer (list_of_mset (side_prems_of_RP \<iota>) @ [main_prem_of_RP \<iota>]) (concl_of_RP \<iota>)"
*)

lemma gc_subsumption_step:
  assumes
    d_in: "Dl \<in> N" and
    d_sub_c: "strictly_subsumes (fst Dl) (fst Cl) \<or> subsumes (fst Dl) (fst Cl) \<and> snd Dl \<sqsubset>l snd Cl"
  shows "N \<union> {Cl} \<Longrightarrow>GC N"
proof -
  have d_sub'_c: "Cl \<in> GC.Red_F_Q {Dl} \<or> Dl \<sqsubset> Cl"
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
    have "Cl \<in> GC.Red_F_Q {Dl}"
      apply (rule mem_GC_Red_F_Q_because_G_Red_F)
      apply (unfold G.Red_F_def)
      apply clarsimp
      using d_ssub_c
      apply (unfold strictly_subsumes_def subsumes_def)
      apply clarsimp
      unfolding \<G>_F_def
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
    using d_sub'_c unfolding GC_Red_F_Q_eq
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
  have "Cl \<in> GC.Red_F_Q {Dl}"
    apply (rule mem_GC_Red_F_Q_because_G_Red_F)
    apply (unfold G.Red_F_def)
    apply clarsimp
    unfolding \<G>_F_def
    apply clarsimp
    apply (rule_tac x = "{fst Dl \<cdot> \<sigma>}" in exI)
    apply auto
    using subst_subset_mono[OF d_sub_c]
    using true_clss_subclause
     apply fast
    using subst_subset_mono[OF d_sub_c]
    by (simp add: subset_imp_less_mset)
  then show "{Cl} \<subseteq> GC.Red_F_Q (N \<union> {Dl})"
    using GC.Red_F_of_subset by blast
qed (auto simp: GC.active_subset_def passiv)

lemma gc_processing_step: "N \<union> {(C, New)} \<Longrightarrow>GC N \<union> {(C, Processed)}"
proof (rule GC.step.process[of _ N "{(C, New)}" _ "{(C, Processed)}"])
  have "(C, New) \<in> GC.Red_F_Q {(C, Processed)}"
    apply (rule mem_GC_Red_F_Q_because_Prec_FL)
    unfolding GC.Prec_FL_def
    apply auto
    by (simp add: generalizes_refl)
  then show "{(C, New)} \<subseteq> GC.Red_F_Q (N \<union> {(C, Processed)})"
    using GC.Red_F_of_subset by blast
qed (auto simp: GC.active_subset_def)

lemma RP_inferences_between_eq_F_Inf_from2:
  "concl_of_RP ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C =
   concl_of ` F.Inf_from2 N {C}" (is "?rp = ?f")
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

  show "E \<in> concl_of ` F.Inf_from2 N {C}"
    unfolding F.Inf_from2_alt F.Inf_from_def Inf_F_def inference_system.Inf_from2_alt
      inference_system.Inf_from_def
    apply (auto simp: image_def Bex_def)
    apply (rule_tac x = "Infer (CAs @ [DA]) E" in exI)
    apply auto
    using e_res cd_sub c_in apply auto done
next
  fix E
  assume e_in: "E \<in> concl_of ` F.Inf_from2 N {C}"

  obtain CAs DA AAs As \<sigma> where
    e_res: "ord_resolve_rename S CAs DA AAs As \<sigma> E" and
    cd_sub: "set CAs \<union> {DA} \<subseteq> N \<union> {C}" and
    c_in: "C \<in> set CAs \<union> {DA}"
    using e_in
    unfolding F.Inf_from2_alt F.Inf_from_def Inf_F_def inference_system.Inf_from2_alt
      inference_system.Inf_from_def
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
  have m_sup': "fst ` M \<supseteq> concl_of ` F.Inf_from2 (fst ` GC.active_subset N) {C}"
    using m_sup unfolding RP_inferences_between_eq_F_Inf_from2 .

  show "F.Inf_from2 (fst ` GC.active_subset N) {C} \<subseteq> F.Red_Inf_Q (fst ` (N \<union> {(C, Old)} \<union> M))"
  proof
    fix \<iota>
    assume \<iota>_in_if2: "\<iota> \<in> F.Inf_from2 (fst ` GC.active_subset N) {C}"

    have \<iota>_in: "\<iota> \<in> Inf_F"
      using \<iota>_in_if2 unfolding F.Inf_from2_def F.Inf_from_def by auto

    have "concl_of \<iota> \<in> fst ` M"
      using m_sup'
      apply (auto simp: image_def Collect_mono_iff F.Inf_from2_alt)
      using \<iota>_in_if2 m_sup' by auto
    then have "concl_of \<iota> \<in> fst ` (N \<union> {(C, Old)} \<union> M)"
      by auto
    then show "\<iota> \<in> F.Red_Inf_\<G>_Q (fst ` (N \<union> {(C, Old)} \<union> M))"
      by (rule F.Red_Inf_of_Inf_to_N[OF \<iota>_in])
  qed
qed (use l_ne m_passiv in auto)

lemma step_RP_imp_step_GC: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<Longrightarrow>GC lclss_of_state St'"
proof (induction rule: RP.induct)
  case (tautology_deletion A C N P Q)
  note tauto = this

  have c\<theta>_red:
    "C\<theta> \<in> G.Red_F (\<Union>D \<in> N'. \<G>_F (fst D))" if in_g: "C\<theta> \<in> \<G>_F C"
    for N' :: "('a clause \<times> label) set" and C\<theta>
  proof -
    obtain \<theta> where
      "C\<theta> = C \<cdot> \<theta>"
       using in_g unfolding \<G>_F_def by blast
    then have compl_lits:
      "Neg (A \<cdot>a \<theta>) \<in># C\<theta>"
      "Pos (A \<cdot>a \<theta>) \<in># C\<theta>"
      using tauto Neg_Melem_subst_atm_subst_cls Pos_Melem_subst_atm_subst_cls by auto
    then have "{} \<TTurnstile>e {C\<theta>}"
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
    apply (rule mem_GC_Red_F_Q_because_G_Red_F)
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

lemma derivation_RP_imp_derivation_GC: "chain (\<leadsto>) Sts \<Longrightarrow> chain (\<Longrightarrow>GC) (lmap lclss_of_state Sts)"
  using chain_lmap step_RP_imp_step_GC by blast

lemma step_RP_imp_step: "St \<leadsto> St' \<Longrightarrow> lclss_of_state St \<rhd>RedFL lclss_of_state St'"
  by (rule GC.one_step_equiv) (rule step_RP_imp_step_GC)

lemma derivation_RP_imp_derivation_RedFL: "chain (\<leadsto>) Sts \<Longrightarrow> chain (\<rhd>RedFL) (lmap lclss_of_state Sts)"
  using chain_lmap step_RP_imp_step by blast

theorem RP_sound_new_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    bot_in: "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "grounding_of_state (lhd Sts) \<TTurnstile>e {{#}}"
proof -
  have "clss_of_state (Liminf_state Sts) \<TTurnstile>\<G>e {{#}}"
    using F.subset_entailed bot_in by auto
  then have "fst ` Liminf_llist (lmap lclss_of_state Sts) \<TTurnstile>\<G>e {{#}}"
    by (metis image_fst_lclss_of_state lclss_Liminf_commute)
  then have "Liminf_llist (lmap lclss_of_state Sts) \<TTurnstile>\<G>Le GC.Bot_FL"
    using GC.labeled_entailment_lifting by simp
  then have "lhd (lmap lclss_of_state Sts) \<TTurnstile>\<G>Le GC.Bot_FL"
    apply -
    apply (subst (asm) GC.unsat_limit_iff)
    using deriv derivation_RP_imp_derivation_RedFL apply auto[1]
    defer
    apply blast
    by (smt F_entails_\<G>_Q_iff GC_entails_\<G>_L_Q_iff RP_model chain_lmap deriv grounding_of_clss_def
        image_fst_lclss_of_state)
  then have "lclss_of_state (lhd Sts) \<TTurnstile>\<G>Le GC.Bot_FL"
    using chain_not_lnull deriv by fastforce
  then have "clss_of_state (lhd Sts) \<TTurnstile>\<G>e {{#}}"
    unfolding GC.entails_\<G>_L_Q_def F.entails_\<G>_Q_def lclss_of_state_def by auto
  then show ?thesis
    using F_entails_\<G>_Q_iff grounding_of_clss_def by auto
qed

theorem RP_saturated_if_fair_new_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    init: "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}" and
    final: "GC.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
  shows "GC.saturated (Liminf_llist (lmap lclss_of_state Sts))"
proof -
  have gc_deriv: "chain (\<Longrightarrow>GC) (lmap lclss_of_state Sts)"
    by (rule derivation_RP_imp_derivation_GC[OF deriv])
  show ?thesis
    by (rule GC.fair_implies_Liminf_saturated[OF GC.gc_to_red[OF gc_deriv]
          GC.gc_fair[OF gc_deriv init final]])
qed

corollary RP_complete_if_fair_new_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    init: "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}" and
    final: "GC.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}" and
    unsat: "grounding_of_state (lhd Sts) \<TTurnstile>e {{#}}"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof -
  have gc_deriv: "chain (\<Longrightarrow>GC) (lmap lclss_of_state Sts)"
    by (rule derivation_RP_imp_derivation_GC[OF deriv])
  have fst_unsat: "fst ` lnth (lmap lclss_of_state Sts) 0 \<TTurnstile>\<G>e {{#}}"
  proof -
    have len: "llength Sts > 0"
      by (rule chain_length_pos[OF deriv])
    have fst_lcls: "fst ` lnth (lmap lclss_of_state Sts) 0 = lnth (lmap clss_of_state Sts) 0"
      using len zero_enat_def by auto
    show ?thesis
      unfolding fst_lcls
      using unsat
      unfolding F_entails_\<G>_Q_iff
      apply auto
      unfolding lnth_lmap[OF len[unfolded zero_enat_def]]
      apply (simp add: lnth_0_conv_lhd[OF chain_not_lnull[OF deriv]])
      unfolding true_clss_def
      apply auto
      apply (erule_tac x = I in allE)
      apply (erule bexE)
      unfolding grounding_of_clss_def
      by (metis UN_E)
  qed
  have "\<exists>BL \<in> {{#}} \<times> UNIV. BL \<in> Liminf_llist (lmap lclss_of_state Sts)"
    using GC.gc_complete_Liminf[OF gc_deriv init final _ fst_unsat] by blast
  then show ?thesis
    unfolding lclss_Liminf_commute
    unfolding lclss_of_state_def
    using final[unfolded GC.passive_subset_def]
    apply auto
    using Liminf_state_def lclss_Liminf_commute apply fastforce
    using Liminf_state_def lclss_Liminf_commute by fastforce
qed


subsection \<open>Alternative Derivation of Previous RP Results\<close>

lemma fair_RP_imp_fair:
  assumes
    nnul: "\<not> lnull Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows
    "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}" and
    "GC.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
proof -
  show "GC.active_subset (lnth (lmap lclss_of_state Sts) 0) = {}"
    using empty_Q0 unfolding GC.active_subset_def
    using nnul
    apply (cases Sts)
    apply auto
    done
next
  show "GC.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
    using fair unfolding fair_state_seq_def GC.passive_subset_def
    apply auto
    unfolding lclss_Liminf_commute
    by (metis (no_types, lifting) Liminf_state_def N_of_state_Liminf P_of_state_Liminf empty_iff
        label.exhaust mem_lclss_of_state(1) mem_lclss_of_state(2))
qed

lemma redundant_infer_RP_alt:
  "src.redundant_infer N \<gamma> \<longleftrightarrow>
   (\<exists>DD. DD \<subseteq> N \<and> DD \<union> set_mset (side_prems_of_RP \<gamma>) \<TTurnstile>e {concl_of_RP \<gamma>}
      \<and> (\<forall>D \<in> DD. D < main_prem_of_RP \<gamma>))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding src.redundant_infer_def by auto
next
  assume ?rhs
  then obtain DD0 where
    "DD0 \<subseteq> N" and
    "DD0 \<union> set_mset (side_prems_of_RP \<gamma>) \<TTurnstile>e {concl_of_RP \<gamma>}" and
    "\<forall>D \<in> DD0. D < main_prem_of_RP \<gamma>"
    by blast
  then obtain DD where
    "finite DD" and
    "DD \<subseteq> N" and
    "DD \<union> set_mset (side_prems_of_RP \<gamma>) \<TTurnstile>e {concl_of_RP \<gamma>}" and
    "\<forall>D \<in> DD. D < main_prem_of_RP \<gamma>"
    using entails_compact_union[of "{concl_of_RP \<gamma>}" DD0 "set_mset (side_prems_of_RP \<gamma>)"] by fast
  then show ?lhs
    unfolding src.redundant_infer_def
    apply -
    apply (rule exI[of _ "mset_set DD"])
    apply auto
    done
qed

(* FIXME
lemma "G.redundant_infer (\<Union>Cl \<in> Liminf_llist Nls. \<G>_F (fst Cl)) \<Longrightarrow> src.redundant_infer (Liminf_llist gSts)"

  thm image_Liminf_llist_subset
*)

lemma saturated_imp_saturated_RP:
  assumes satur_gc: "GC.saturated (Liminf_llist (lmap lclss_of_state Sts))"
  shows "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  unfolding src.saturated_upto_def
proof
  fix \<gamma> :: "'a inference_RP"

  define Nls where
    "Nls = lmap lclss_of_state Sts"
  define Ns where
    "Ns = lmap clss_of_state Sts"
  define gSts where
    "gSts = lmap grounding_of_state Sts"

  (* FIXME: needed? *)
  have lmap_fst_nls: "lmap ((`) fst) Nls = Ns"
    unfolding Nls_def Ns_def lclss_of_state_def by (simp add: llist.map_comp image_Un image_comp)

  assume \<gamma>_in_inf_rp: "\<gamma> \<in> gd.inferences_from Sts (Liminf_llist gSts - src.Rf (Liminf_llist gSts))"

  have \<gamma>_in_inf_gc: "\<gamma> \<in> infer_RP_of ` infer_of_FL ` GC.Inf_from (Liminf_llist Nls)"
    sorry
  then have \<gamma>_in_red_gc: "\<gamma> \<in> infer_RP_of ` infer_of_FL ` GC.Red_Inf_\<G>_Q (Liminf_llist Nls)"
    using satur_gc[unfolded GC.saturated_def]
    unfolding image_def
    using Nls_def by blast



  then show "\<gamma> \<in> src.Ri Sts (Liminf_llist gSts)"
    unfolding GC.Red_Inf_\<G>_Q_def GC.Red_Inf_\<G>_q_def \<G>_Inf_def
    apply auto
    unfolding infer_of_FL_def infer_RP_of_def GC.to_F_def
    apply auto
    unfolding Inf_FL_def Inf_F_def Infer_FL_of_def G.Red_Inf_def
    apply (subst (asm) Inf_G_def)
    apply auto
    apply (subst (asm) Inf_G_def)
    apply auto
    unfolding src.Ri_def
    unfolding redundant_infer_RP_alt
(*
    apply auto
    using \<gamma>_in_inf_rp gd.inferences_from_def apply auto[1]
*)
    sorry
qed

theorem RP_sound_old_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    bot_in: "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "\<not> satisfiable (grounding_of_state (lhd Sts))"
  using RP_sound_new_statement[OF deriv bot_in] unfolding F_entails_\<G>_Q_iff by simp

theorem RP_saturated_if_fair_old_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows "src.saturated_upto Sts (Liminf_llist (lmap grounding_of_state Sts))"
  apply (rule saturated_imp_saturated_RP)
  apply (rule RP_saturated_if_fair_new_statement)
  apply (rule deriv)
  using fair_RP_imp_fair[OF chain_not_lnull[OF deriv] fair empty_Q0] .

corollary RP_complete_if_fair_old_statement:
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}" and
    unsat: "\<not> satisfiable (grounding_of_state (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
  apply (rule RP_complete_if_fair_new_statement)
  apply (rule deriv)
  apply (rule fair_RP_imp_fair[OF chain_not_lnull[OF deriv] fair empty_Q0])+
  using unsat unfolding F_entails_\<G>_Q_iff by auto

end
