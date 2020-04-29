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

context
  fixes M :: "'a clause set"
begin

interpretation gr: selection "S_M S M"
  using selection_axioms by unfold_locales (fact S_M_selects_subseteq S_M_selects_neg_lits)+

interpretation gr: ground_resolution_with_selection "S_M S M"
  by unfold_locales

definition Inf_G :: "'a clause inference set" where
  "Inf_G = {Infer (CAs @ [DA]) E | CAs DA AAs As E. gr.ord_resolve CAs DA AAs As E}"

lemma Inf_G_have_prems: "\<iota> \<in> Inf_G \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_G_def by auto

lemma Inf_G_reductive: "\<iota> \<in> Inf_G \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
  unfolding Inf_G_def by (auto dest: gr.ord_resolve_reductive)

abbreviation Bot_G :: "'a clause set" where
  "Bot_G \<equiv> {{#}}"

definition entails_G (infix "\<Turnstile>" 50) where
  "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>I. I |\<approx>s N1 \<longrightarrow> I |\<approx>s N2)"

interpretation G: clausal_consequence_relation Bot_G "(\<Turnstile>)"
  by unfold_locales (auto simp: entails_G_def)

interpretation G: sound_inference_system Inf_G Bot_G "(\<Turnstile>)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_G"
  moreover
  {
    fix I
    assume I_ent_prems: "I |\<approx>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_G_def by auto
    then have "I |\<approx> concl_of \<iota>"
      using gr.ord_resolve_sound[of CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_ent_prems Inf_G_have_prems i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile> {concl_of \<iota>}"
    unfolding entails_G_def by simp
qed

interpretation G: clausal_cex_red_inference_system "(\<Turnstile>)" Bot_G Inf_G gr.INTERP
proof
  fix N D
  assume
    "{#} \<notin> N" and
    "D \<in> N" and
    "\<not> gr.INTERP N |\<approx> D" and
    "\<And>C. C \<in> N \<Longrightarrow> \<not> gr.INTERP N |\<approx> C \<Longrightarrow> D \<le> C"
  then obtain CAs AAs As E where
    "set CAs \<subseteq> N" and
    "gr.INTERP N |\<approx>m mset CAs" and
    "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production N CA \<noteq> {}" and
    "gr.ord_resolve CAs D AAs As E" and
    "\<not> gr.INTERP N |\<approx> E" and
    "E < D"
    using gr.ord_resolve_counterex_reducing by blast
  then show "\<exists>Cs E. set Cs \<subseteq> N \<and> gr.INTERP N |\<approx>s set Cs \<and> Infer (Cs @ [D]) E \<in> Inf_G
    \<and> \<not> gr.INTERP N |\<approx> E \<and> E < D"
    unfolding Inf_G_def
    by (metis (mono_tags, lifting) gr.ex_min_counterex gr.productive_imp_INTERP mem_Collect_eq)
qed

interpretation G: clausal_cex_red_calculus_with_std_red_crit Bot_G "(\<Turnstile>)" Inf_G gr.INTERP
  by (unfold_locales, fact Inf_G_have_prems, fact Inf_G_reductive)

definition Red_Inf_G :: "'a clause set \<Rightarrow> 'a clause inference set" where
  "Red_Inf_G = G.Red_Inf"

definition Red_F_G :: "'a clause set \<Rightarrow> 'a clause set" where
  "Red_F_G = G.Red_F"

interpretation G: static_refutational_complete_calculus Bot_G Inf_G "(\<Turnstile>)" G.Red_Inf G.Red_F
  by unfold_locales (use G.clausal_saturated_complete entails_G_def in blast)

end


subsection \<open>First-Order Layer\<close>

abbreviation Bot_F :: "'a clause set" where
  "Bot_F \<equiv> {{#}}"

definition entails_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>F" 50) where
  "N1 \<Turnstile>F N2 \<longleftrightarrow>
  (\<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N1 \<cdot>cs \<sigma>) \<longrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I |\<approx>s N2 \<cdot>cs \<sigma>))"

definition Inf_F :: "'a clause inference set" where
  "Inf_F = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma Inf_F_have_prems: "\<iota> \<in> Inf_F \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_F_def by force

interpretation F: consequence_relation Bot_F "(\<Turnstile>F)"
proof
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 \<Turnstile>F N2"
    unfolding entails_F_def by (metis subst_clss_union sup.orderE true_clss_union)
next
  fix N2 N1 :: "'a clause set"
  assume "\<forall>C \<in> N2. N1 \<Turnstile>F {C}"
  then show "N1 \<Turnstile>F N2"
    unfolding entails_F_def by (simp add: subst_clss_def true_clss_def)
qed (auto simp: entails_F_def)

interpretation F: sound_inference_system Inf_F Bot_F "(\<Turnstile>F)"
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
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}"
    unfolding entails_F_def by simp
qed

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

definition \<G>_Inf :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf N \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G N}\<close>

datatype label =
  New
| Processed
| Active

definition Inf_FL :: "('a clause \<times> label) inference set" where
  "Inf_FL = {Infer (zip Cs Ls) (D, New) |Cs D Ls. Infer Cs D \<in> Inf_F \<and> length Ls = length Cs}"

abbreviation Equiv_F :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<doteq>" 50) where
  "C \<doteq> D \<equiv> subsumes C D \<and> subsumes D C"

abbreviation Prec_F :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) where
  "Prec_F \<equiv> strictly_subsumes"

fun Prec_l :: "label \<Rightarrow> label \<Rightarrow> bool" (infix "\<sqsubset>l" 50) where
  "Active \<sqsubset>l l \<longleftrightarrow> l \<noteq> Active"
| "Processed \<sqsubset>l l \<longleftrightarrow> l = New"
| "New \<sqsubset>l l \<longleftrightarrow> False"

lemma irrefl_Prec_l: "\<not> l \<sqsubset>l l"
  by (cases l) auto

lemma trans_Prec_l: "l1 \<sqsubset>l l2 \<Longrightarrow> l2 \<sqsubset>l l3 \<Longrightarrow> l1 \<sqsubset>l l3"
  by (cases l1; cases l2; cases l3) auto

lemma wf_Prec_l: "wfP (\<sqsubset>l)"
  by (metis Prec_l.elims(2) Prec_l.simps(3) not_accp_down wfP_accp_iff)

interpretation F: standard_lifting_with_red_crit_family Inf_F Bot_G UNIV Inf_G "\<lambda>N. (\<Turnstile>F)" Red_Inf_G
    "\<lambda>N. Red_F_G" Bot_F "\<lambda>N. \<G>_F" \<G>_Inf "\<lambda>C. (\<prec>\<cdot>)"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation Bot_F (\<Turnstile>F)"
    by (fact F.consequence_relation_axioms)
next
  fix N
  show "calculus_with_red_crit Bot_F (Inf_G N) (\<Turnstile>F) (Red_Inf_G N) Red_F_G"
    sorry
next
  fix N
  show "lifting_with_wf_ordering_family Bot_F Inf_F Bot_F (\<Turnstile>F) (Inf_G N) (Red_Inf_G N) Red_F_G \<G>_F
    (\<G>_Inf N) (\<lambda>C. (\<prec>\<cdot>))"
    sorry
qed

abbreviation entails_\<G>_Q_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>\<G>" 50) where
  "(\<Turnstile>\<G>) \<equiv> F.entails_\<G>_Q"

interpretation F: consequence_relation Bot_F "(\<Turnstile>\<G>)"
proof
  show "Bot_F \<noteq> {}"
    by (rule F.bot_not_empty)
next
  fix B N1
  assume "B \<in> Bot_F"
  then show "{B} \<Turnstile>\<G> N1"
    unfolding F.entails_\<G>_Q_def
    using F.lifted_calc_w_red_crit_family.entails_Q_def
      F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.bot_entails_all by blast
next
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 \<Turnstile>\<G> N2"
    unfolding F.entails_\<G>_Q_def
    using F.lifted_calc_w_red_crit_family.entails_Q_def
      F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.subset_entailed by blast
next
  fix N2 N1
  assume "\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}"
  then show "N1 \<Turnstile>\<G> N2"
    unfolding F.entails_\<G>_Q_def
    using F.lifted_calc_w_red_crit_family.q_cons_rel consequence_relation.entail_set_all_formulas
    by blast
next
  fix N1 N2 N3
  assume
    "N1 \<Turnstile>\<G> N2"
    "N2 \<Turnstile>\<G> N3"
  then show "N1 \<Turnstile>\<G> N3"
    unfolding F.entails_\<G>_Q_def F.entails_\<G>_q_def using F.entails_trans by blast
qed

(* FIXME:
proof
  fix C
  show \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_G\<close>
    by (simp add: grounding_of_cls_def)
next
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    g_def: \<open>\<G>_Inf \<iota> \<noteq> None\<close>
  show \<open>the (\<G>_Inf \<iota>) \<subseteq> G.Red_Inf (\<G>_F (concl_of \<iota>))\<close>
  proof
    fix \<iota>'
    assume i'_in: \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
    then have i'_in2: \<open>\<iota>' \<in> Inf_G\<close>
      unfolding \<G>_Inf_def g_def by auto
    have concl_in: \<open>concl_of \<iota>' \<in> \<G>_F (concl_of \<iota>)\<close>
      using i'_in unfolding \<G>_Inf_def grounding_of_cls_def by auto
    show \<open>\<iota>' \<in> G.Red_Inf (\<G>_F (concl_of \<iota>))\<close>
      using standard_lifting.inf_map i'_in2 concl_in by (simp add: G.Red_Inf_of_Inf_to_N)
  qed
qed auto
*)

interpretation GC: Given_Clause Bot_F Inf_F Bot_G UNIV "\<lambda>N. (\<Turnstile>F)" Inf_G Red_Inf_G "\<lambda>N. Red_F_G"
  "\<lambda>N. \<G>_F" \<G>_Inf Inf_FL "(\<doteq>)" "(\<prec>\<cdot>)" "(\<sqsubset>l)" Active
proof (unfold_locales; (intro ballI)?)
  fix N :: "'a clause set"
  show "lifting_with_wf_ordering_family Bot_F Inf_F Bot_F (\<Turnstile>F) (Inf_G N) (Red_Inf_G N) Red_F_G \<G>_F
    (\<G>_Inf N) (\<lambda>g. Empty_Order)"
    sorry
next
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
next
  show "equivp (\<doteq>)"
    unfolding equivp_def by (meson subsumes_refl subsumes_trans)
next
  show "po_on (\<prec>\<cdot>) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def
    using strictly_subsumes_irrefl strictly_subsumes_trans by blast
next
  show "wfp_on (\<prec>\<cdot>) UNIV"
    unfolding wfp_on_UNIV by (simp add: wf_strictly_subsumes)
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
    by (meson strictly_subsumes_def subsumes_trans)
next
  fix N C1 C2
  assume "C1 \<doteq> C2"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding subsumes_def grounding_of_cls_def
    by clarsimp (metis is_ground_comp_subst strict_subset_subst_strictly_subsumes
        strictly_subsumes_neq strictly_subsumes_trans subset_mset.antisym_conv2 subst_cls_comp_subst
        subst_cls_id_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_subsumes_def subsumes_def grounding_of_cls_def
    apply clarsimp
    sorry
next
  fix N
  show "F.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q N \<subseteq> Inf_F"
    using F.lifted_calc_w_red_crit_family.inter_red_crit_calculus.Red_Inf_to_Inf by blast
next
  fix B N
  assume
    "B \<in> Bot_F"
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
    "B \<in> Bot_F"
    "F.empty_ord_lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N"
    "N \<Turnstile>\<G> {B}"
  show "\<exists>B' \<in> Bot_F. B' \<in> N"
    sorry
next
  fix \<iota>
  assume "\<iota> \<in> Inf_F"
  then show "prems_of \<iota> \<noteq> []"
    by (simp add: Inf_F_have_prems)
next
  fix l
  assume "l \<noteq> Active"
  then show "Prec_l Active l"
    by simp
next
  show "\<exists>l. Prec_l Active l"
    using Prec_l.simps(1) by blast
next
  fix \<iota>
  assume "\<iota> \<in> Inf_FL"
  then show "snd (concl_of \<iota>) \<noteq> Active"
    unfolding Inf_FL_def by auto
qed





















abbreviation entails_\<G>_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>\<G>" 50) where
  "N1 \<Turnstile>\<G> N2 \<equiv> F.entails_\<G> N1 N2"

lemma union_\<G>_F_ground: \<open>is_ground_clss (\<Union> (\<G>_F ` N))\<close>
  by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)

lemma lifting_in_framework:
  \<open>\<iota>\<^sub>0 \<in> G.Inf_from (\<Union> (\<G>_F ` M)) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> F.Inf_from M \<and> \<iota>\<^sub>0 \<in> the (\<G>_Inf \<iota>)\<close>
proof -
  assume \<iota>\<^sub>0_in: \<open>\<iota>\<^sub>0 \<in> G.Inf_from (\<Union> (\<G>_F ` M))\<close>
  have prems_\<iota>\<^sub>0_in: \<open>set (prems_of \<iota>\<^sub>0) \<subseteq> \<Union> (\<G>_F ` M)\<close>
    using \<iota>\<^sub>0_in unfolding G.Inf_from_def by blast
  have \<iota>\<^sub>0_Inf_G: \<open>\<iota>\<^sub>0 \<in> Inf_G\<close>
    using \<iota>\<^sub>0_in unfolding G.Inf_from_def by blast
  then obtain CAs DA AAs As E where
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close> and
    \<iota>\<^sub>0_is: \<open>\<iota>\<^sub>0 = Infer (CAs @ [DA]) E\<close>
    unfolding Inf_G_def by auto

  have CAs_in: \<open>set CAs \<subseteq> set (prems_of \<iota>\<^sub>0)\<close>
    by (simp add: \<iota>\<^sub>0_is subsetI)
  then have ground_CAs: \<open>is_ground_cls_list CAs\<close>
    using prems_\<iota>\<^sub>0_in union_\<G>_F_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_in: \<open>DA \<in> set (prems_of \<iota>\<^sub>0)\<close>
    using \<iota>\<^sub>0_is by simp
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_\<iota>\<^sub>0_in union_\<G>_F_ground is_ground_clss_def by auto
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
    using ord_resolve_rename_lifting_with_length[OF sel_stable grounded_res selection_axioms
        prems_ground] by metis

  have "length CAs0 = length \<eta>s"
    using len_CAs0 len_ns by simp
  then have \<iota>\<^sub>0_is': "\<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl (\<eta>s @ [\<eta>])) (E0 \<cdot> \<eta>2)"
    unfolding \<iota>\<^sub>0_is by (auto simp: CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric])

  define \<iota> :: "'a clause inference" where
    "\<iota> = Infer (CAs0 @ [DA0]) E0"

  have i_Inf_F: \<open>\<iota> \<in> Inf_F\<close>
    unfolding \<iota>_def Inf_F_def using ngr_res by auto

  have "\<exists>\<rho> \<rho>s. \<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>)
    \<and> is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho> \<and> Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>) \<in> Inf_G"
    by (rule exI[of _ \<eta>2], rule exI[of _ "\<eta>s @ [\<eta>]"], use ground_ns in
        \<open>auto intro: ground_n ground_n2 \<iota>\<^sub>0_Inf_G[unfolded \<iota>\<^sub>0_is']
           simp: \<iota>\<^sub>0_is' is_ground_subst_list_def\<close>)
  then have \<open>\<iota>\<^sub>0 \<in> the (\<G>_Inf \<iota>)\<close>
    unfolding \<G>_Inf_def \<iota>_def CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric] by simp
  moreover have \<open>\<iota> \<in> F.Inf_from M\<close>
    using prems_in i_Inf_F unfolding F.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation F: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G "(\<Turnstile>G)" Inf_G G.Red_Inf
  G.Red_F \<G>_F \<G>_Inf "\<lambda>g. strictly_subsumes"
proof
  show "po_on strictly_subsumes UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def
    using strictly_subsumes_irrefl strictly_subsumes_trans by blast
next
  show "wfp_on strictly_subsumes UNIV"
    using wf_iff_no_infinite_down_chain[THEN iffD1, OF wf_strictly_subsumes[unfolded wfP_def]]
    unfolding wfp_on_def by simp
qed

lemma inf_F_to_inf_G: \<open>\<iota> \<in> Inf_F \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Inf_G\<close>
  unfolding \<G>_Inf_def by auto

lemma inf_G_in_inf_F: \<open>Inf_G \<subseteq> Inf_F\<close>
  unfolding Inf_G_def Inf_F_def
  apply auto
  sorry

interpretation F: static_refutational_complete_calculus Bot_F Inf_F "(\<Turnstile>\<G>)" F.Red_Inf_\<G> F.Red_F_\<G>
proof
  fix B N
  assume
    b_in: \<open>B \<in> Bot_G\<close> and
    n_sat: \<open>F.lifted_calculus_with_red_crit.saturated N\<close> and
    ent_b: \<open>N \<Turnstile>\<G> {B}\<close>

  have \<open>B = {#}\<close>
    using b_in by simp
  have gn_sat: \<open>G.saturated (F.\<G>_set N)\<close>
    unfolding G.saturated_def
  proof
    fix \<iota>
    assume \<iota>_in: \<open>\<iota> \<in> G.Inf_from (\<Union> (\<G>_F ` N))\<close>

    obtain \<iota>' where
      "\<iota>' \<in> F.Inf_from M"
      "\<iota> \<in> the (\<G>_Inf \<iota>')"
      using \<iota>_in lifting_in_framework
      oops

(*
    show "\<iota> \<in> G.Red_Inf (\<Union> (\<G>_F ` N))"
      sorry

    fix \<iota>'
    assume i_in: \<open>\<iota>' \<in> F.Inf_from (F.\<G>_set N)\<close>
    obtain \<iota> where \<open>\<iota> \<in> F.Inf_from N\<close> \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close> using i_in lifting_in_framework sorry
    show \<open>\<iota>' \<in> G.Red_Inf (F.\<G>_set N)\<close> using i_in n_sat unfolding src.lifted_calculus_with_red_crit.saturated_def sorry
    oops


  show "\<exists>B' \<in> Bot. B' \<in> N"
    sorry
*)

(*
definition entails_all_\<G>  :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<longleftrightarrow> \<Union> (grounding_of_cls ` N1) \<Turnstile> \<Union> (grounding_of_cls ` N2)\<close>
*)

(* definition Red_Inf_all_\<G> :: "'a clause set \<Rightarrow> 'a clause inference set" where
  \<open>Red_Inf_all_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> G.Red_Inf (\<G>_set N)}\<close> *)




end

end
