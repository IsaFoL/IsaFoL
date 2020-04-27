(*  Title:       Ordered_Resolution_Integration_Refactor
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Application of the saturation framework to Bachmair and Ganzinger's RP\<close>

theory Ordered_Resolution_Integration_Refactor
  imports
    Ordered_Resolution_Integration_Refactor_Utils
    Saturation_Framework.Prover_Architectures
    Standard_Redundancy_Criterion
    Soundness_Related
begin


subsection \<open>Setup\<close>

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of


subsection \<open>Core Development\<close>

context FO_resolution_prover
begin

abbreviation Bot_F :: "'a clause set" where
  "Bot_F \<equiv> {{#}}"

definition entails_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>F" 50) where
  "N1 \<Turnstile>F N2 \<longleftrightarrow>
  (\<forall>I \<eta>. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>) \<longrightarrow> is_ground_subst \<eta> \<longrightarrow> I \<Turnstile>s N2 \<cdot>cs \<eta>)"

definition Inf_F :: "'a clause inference set" where
  "Inf_F = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma Inf_F_has_prem: "\<iota> \<in> Inf_F \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_F_def by force

interpretation F: consequence_relation Bot_F entails_F
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

interpretation F: sound_inference_system Inf_F Bot_F entails_F
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_F"
  moreover
  {
    fix I \<eta>
    assume
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (prems_of \<iota>) \<cdot>cs \<sigma>" and
      \<eta>_gr: "is_ground_subst \<eta>"
    obtain CAs AAs As \<sigma> where
      the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>) AAs As \<sigma> (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_F_def by auto
    have prems: "mset (prems_of \<iota>) = mset (side_prems_of \<iota>) + {#main_prem_of \<iota>#}"
      by (metis Inf_F_has_prem[OF i_in] add.right_neutral append_Cons append_Nil2
          append_butlast_last_id mset.simps(2) mset_rev mset_single_iff_right rev_append
          rev_is_Nil_conv union_mset_add_mset_right)
    have "I \<Turnstile> concl_of \<iota> \<cdot> \<eta>"
      using ord_resolve_rename_sound[OF the_inf, of I \<eta>, OF _ \<eta>_gr]
      unfolding CAs prems[symmetric] using I_entails_prems
      by (metis set_mset_mset set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile>F {concl_of \<iota>}"
    unfolding entails_F_def by simp
qed

abbreviation Bot_G :: "'a clause set" where
  "Bot_G \<equiv> {{#}}"

context
  fixes M :: "'a clause set"
  assumes sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
begin

interpretation gr: selection "S_M S M"
  using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gr: ground_resolution_with_selection "S_M S M"
  by unfold_locales

definition Inf_G :: "'a clause inference set" where
  "Inf_G = {Infer (CAs @ [DA]) E | CAs DA AAs As E. gr.ord_resolve CAs DA AAs As E}"

lemma Inf_G_has_prem: "\<iota> \<in> Inf_G \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding Inf_G_def by auto

lemma Inf_G_reductive: "\<iota> \<in> Inf_G \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
  unfolding Inf_G_def by (auto dest: gr.ord_resolve_reductive)

definition entails_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>G" 50) where
  "N1 \<Turnstile>G N2 \<longleftrightarrow> (\<forall>I. I \<Turnstile>s N1 \<longrightarrow> I \<Turnstile>s N2)"

interpretation G: consequence_relation Bot_G entails_G
proof
  fix N2 N1 :: "'a clause set"
  assume "N2 \<subseteq> N1"
  then show "N1 \<Turnstile>G N2"
    unfolding entails_G_def using true_clss_mono by blast
next
  fix N2 N1 :: "'a clause set"
  assume "\<forall>C \<in> N2. N1 \<Turnstile>G {C}"
  then show "N1 \<Turnstile>G N2"
    unfolding entails_G_def by (meson gr.ex_min_counterex true_clss_singleton)
qed (auto simp: entails_G_def)

interpretation G: sound_inference_system Inf_G Bot_G entails_G
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_G"
  moreover
  {
    fix I
    assume I_entails_prems: "I \<Turnstile>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding Inf_G_def by auto
    then have "I \<Turnstile> concl_of \<iota>"
      using gr.ord_resolve_sound[of CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_entails_prems Inf_G_has_prem i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<Turnstile>G {concl_of \<iota>}"
    unfolding entails_G_def by simp
qed

definition clss_of_interp :: "'b set \<Rightarrow> 'b literal multiset set" where
  "clss_of_interp I = {{#(if A \<in> I then Pos else Neg) A#} |A. True}"

lemma true_clss_of_interp_iff_equal[simp]: "J \<Turnstile>s clss_of_interp I \<longleftrightarrow> J = I"
  unfolding clss_of_interp_def true_clss_def true_cls_def true_lit_def by force

lemma entails_G_iff_models[simp]: "clss_of_interp I \<Turnstile>G CC \<longleftrightarrow> I \<Turnstile>s CC"
  unfolding entails_G_def by simp

lemma Inf_G_cex_reducing:
  assumes
    bot_ni_n: "N \<inter> Bot_G = {}" and
    d_in_n: "D \<in> N" and
    n_ent_d: "\<not> clss_of_interp (gr.INTERP N) \<Turnstile>G {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> clss_of_interp (gr.INTERP N) \<Turnstile>G {C} \<Longrightarrow> D \<le> C"
  shows "\<exists>\<iota> \<in> Inf_G.
    main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N
    \<and> clss_of_interp (gr.INTERP N) \<Turnstile>G set (side_prems_of \<iota>)
    \<and> \<not> clss_of_interp (gr.INTERP N) \<Turnstile>G {concl_of \<iota>}
    \<and> concl_of \<iota> < D"
proof -
  have "{#} \<notin> N"
    using bot_ni_n by blast
  moreover have "\<not> gr.INTERP N \<Turnstile> D"
    using n_ent_d by simp
  moreover have "C \<in> N \<Longrightarrow> \<not> gr.INTERP N \<Turnstile> C \<Longrightarrow> D \<le> C" for C
    using d_min[of C] by simp
  ultimately obtain CAs AAs As E where
    cas_sub: "set CAs \<subseteq> N" and
    cas_true: "gr.INTERP N \<Turnstile>m mset CAs" and
    cas_prod: "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production N CA \<noteq> {}" and
    res: "gr.ord_resolve CAs D AAs As E" and
    e_false: "\<not> gr.INTERP N \<Turnstile> E" and
    e_lt_d: "E < D"
    using d_in_n gr.ord_resolve_counterex_reducing by blast

  define \<iota> where
    "\<iota> = Infer (CAs @ [D]) E"

  have i_in: "\<iota> \<in> Inf_G"
    unfolding Inf_G_def \<iota>_def using res by blast
  have "main_prem_of \<iota> = D"
    unfolding \<iota>_def by simp
  moreover have "set (side_prems_of \<iota>) \<subseteq> N"
    unfolding \<iota>_def using cas_sub by simp
  moreover have "clss_of_interp (gr.INTERP N) \<Turnstile>G set (side_prems_of \<iota>)"
    unfolding \<iota>_def using cas_true by (simp add: true_clss_def true_cls_mset_def)
  moreover have "\<not> clss_of_interp (gr.INTERP N) \<Turnstile>G {inference.concl_of \<iota>}"
    unfolding \<iota>_def using e_false by simp
  moreover have "inference.concl_of \<iota> < D"
    unfolding \<iota>_def using e_lt_d by simp
  ultimately show ?thesis
    by (auto intro: bexI[OF _ i_in])
qed

interpretation G: cex_red_calculus_with_std_red_crit Bot_G entails_G
  "\<lambda>N. clss_of_interp (gr.INTERP N)" Inf_G
  by (unfold_locales, fact Inf_G_has_prem, fact Inf_G_reductive, fact Inf_G_cex_reducing)

interpretation G: static_refutational_complete_calculus Bot_G Inf_G entails_G G.Red_Inf
  G.Red_F
proof
  fix B N
  assume
    B_in: \<open>B \<in> Bot_G\<close> and
    N_sat: \<open>G.saturated N\<close> and
    N_unsat: \<open>N \<Turnstile>G {B}\<close>
  have \<open>B = {#}\<close>
    using B_in by simp
  then have \<open>{#} \<in> N\<close>
    using G.saturated_complete_if[OF N_sat] N_unsat unfolding entails_G_def by force
  then show \<open>\<exists>B' \<in> Bot_G. B' \<in> N\<close>
    by simp
qed

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

definition \<G>_Inf :: \<open>'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G}\<close>

interpretation F: standard_lifting Bot_F Inf_F Bot_G Inf_G entails_G G.Red_Inf G.Red_F \<G>_F \<G>_Inf
proof
  show \<open>Bot_G \<noteq> {}\<close>
    by simp
next
  fix B
  assume \<open>B \<in> Bot_G\<close>
  then show \<open>\<G>_F B \<noteq> {}\<close> by simp
next
  fix B
  assume \<open>B \<in> Bot_G\<close>
  then show \<open>\<G>_F B \<subseteq> Bot_G\<close> by simp
next
  fix C
  show \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_G\<close>
  proof (intro impI)
    assume \<open>\<G>_F C \<inter> Bot_G \<noteq> {}\<close>
    then show \<open>C \<in> Bot_G\<close> by (simp add: grounding_of_cls_def)
  qed
next
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    g_def: \<open>\<G>_Inf \<iota> \<noteq> None\<close>
  show \<open>the (\<G>_Inf \<iota>) \<subseteq> G.Red_Inf (\<G>_F (concl_of \<iota>))\<close>
  proof
    fix \<iota>'
    assume i'_in: \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
    then have i'_in2: \<open>\<iota>' \<in> Inf_G\<close> unfolding \<G>_Inf_def g_def by auto
    have concl_in: \<open>concl_of \<iota>' \<in> \<G>_F (concl_of \<iota>)\<close>
      using i'_in unfolding \<G>_Inf_def grounding_of_cls_def by auto
    show \<open>\<iota>' \<in> G.Red_Inf (\<G>_F (concl_of \<iota>))\<close>
      using standard_lifting.inf_map i'_in2 concl_in by (simp add: G.Red_Inf_of_Inf_to_N)
  qed
qed

text \<open>This proof is based on part of the proof of
@{thm FO_Ordered_Resolution_Prover.FO_resolution_prover.RP_saturated_if_fair}.\<close>

lemma gr_ord_resolve_imp_ord_resolve:
  assumes
    ground_DA: \<open>is_ground_cls DA\<close> and
    ground_CAs: \<open>is_ground_cls_list CAs\<close> and
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close>
  shows \<open>\<exists>\<sigma>. ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
proof -
  have ground_E: "is_ground_cls E"
  proof -
    {
      fix L :: "'a literal"
      assume "L \<in># E"
      then have "atm_of L \<in> atms_of E"
        by (meson atm_of_lit_in_atms_of)
      moreover have "atms_of E \<subseteq> (\<Union>CA \<in> set CAs. atms_of CA) \<union> atms_of DA"
        using gr.ord_resolve_atms_of_concl_subset[of CAs DA _ _ E] gr_res by auto
      ultimately have "is_ground_atm (atm_of L)"
        using ground_CAs ground_DA is_ground_cls_imp_is_ground_atm is_ground_cls_list_def by auto
    }
    then show ?thesis
      unfolding is_ground_cls_def is_ground_lit_def by simp
  qed

  show "\<exists>\<sigma>. ord_resolve (S_M S M) CAs DA AAs As \<sigma> E"
    using gr_res
  proof (cases rule: gr.ord_resolve.cases)
    case (ord_resolve n Cs D)
      note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
        aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and
        aas_not_empt = this(9) and as_aas = this(10) and eligibility = this(11) and
        str_max = this(12) and sel_empt = this(13)

      have len_aas_len_as: "length AAs = length As"
        using aas_len as_len by auto

      from as_aas have "\<forall>i<n. \<forall>A \<in># add_mset (As ! i) (AAs ! i). A = As ! i"
        using ord_resolve by simp
      then have "\<forall>i < n. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
        using all_the_same by metis
      then have "\<forall>i < length AAs. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
        using aas_len by auto
      then have "\<forall>AA \<in> set (map2 add_mset As AAs). card (set_mset AA) \<le> Suc 0"
        using set_map2_ex[of AAs As add_mset, OF len_aas_len_as] by auto
      then have "is_unifiers id_subst (set_mset ` set (map2 add_mset As AAs))"
        unfolding is_unifiers_def is_unifier_def by auto
      moreover have "finite (set_mset ` set (map2 add_mset As AAs))"
        by auto
      moreover have "\<forall>AA \<in> set_mset ` set (map2 add_mset As AAs). finite AA"
        by auto
      ultimately obtain \<sigma> where
        \<sigma>_p: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))"
        using mgu_complete by metis

      have ground_elig: "gr.eligible As (D + negs (mset As))"
        using ord_resolve by simp
      have ground_cs: "\<forall>i < n. is_ground_cls (Cs ! i)"
        using ord_resolve(8) ord_resolve(3,4) ground_CAs
        unfolding is_ground_cls_list_def by (metis in_set_conv_nth is_ground_cls_union)
      have ground_set_as: "is_ground_atms (set As)"
        using ord_resolve(1) ground_DA
        by (metis atms_of_negs is_ground_cls_union set_mset_mset
            is_ground_cls_is_ground_atms_atms_of)
      then have ground_mset_as: "is_ground_atm_mset (mset As)"
        unfolding is_ground_atm_mset_def is_ground_atms_def by auto
      have ground_as: "is_ground_atm_list As"
        using ground_set_as is_ground_atm_list_def is_ground_atms_def by auto
      have ground_d: "is_ground_cls D"
        using ground_DA ord_resolve by simp

      from as_len nz have "atms_of D \<union> set As \<noteq> {}" "finite (atms_of D \<union> set As)"
        by auto
      then have "Max (atms_of D \<union> set As) \<in> atms_of D \<union> set As"
        using Max_in by metis
      then have is_ground_Max: "is_ground_atm (Max (atms_of D \<union> set As))"
        using ground_d ground_mset_as is_ground_cls_imp_is_ground_atm
        unfolding is_ground_atm_mset_def by auto
      then have Max\<sigma>_is_Max: "\<forall>\<sigma>. Max (atms_of D \<union> set As) \<cdot>a \<sigma> = Max (atms_of D \<union> set As)"
        by auto

      have ann1: "maximal_wrt (Max (atms_of D \<union> set As)) (D + negs (mset As))"
        unfolding maximal_wrt_def
        by clarsimp (metis Max_less_iff UnCI \<open>atms_of D \<union> set As \<noteq> {}\<close>
            \<open>finite (atms_of D \<union> set As)\<close> ground_d ground_set_as infinite_growing is_ground_Max
            is_ground_atms_def is_ground_cls_imp_is_ground_atm less_atm_ground)

      from ground_elig have ann2:
        "Max (atms_of D \<union> set As) \<cdot>a \<sigma> = Max (atms_of D \<union> set As)"
        "D \<cdot> \<sigma> + negs (mset As \<cdot>am \<sigma>) = D + negs (mset As)"
        using is_ground_Max ground_mset_as ground_d by auto

      from ground_elig have fo_elig:
        "eligible (S_M S M) \<sigma> As (D + negs (mset As))"
        unfolding gr.eligible.simps eligible.simps gr.maximal_wrt_def using ann1 ann2
        by auto

      have l: "\<forall>i < n. gr.strictly_maximal_wrt (As ! i) (Cs ! i)"
        using ord_resolve by simp
      then have "\<forall>i < n. strictly_maximal_wrt (As ! i) (Cs ! i)"
        unfolding gr.strictly_maximal_wrt_def strictly_maximal_wrt_def
        using ground_as[unfolded is_ground_atm_list_def] ground_cs as_len less_atm_ground
        by clarsimp (fastforce simp: is_ground_cls_as_atms)+

      then have ll: "\<forall>i < n. strictly_maximal_wrt (As ! i \<cdot>a \<sigma>) (Cs ! i \<cdot> \<sigma>)"
        by (simp add: ground_as ground_cs as_len)

      have m: "\<forall>i < n. S_M S M (CAs ! i) = {#}"
        using ord_resolve by simp

      have ground_e: "is_ground_cls (\<Union># (mset Cs) + D)"
        using ground_d ground_cs ground_E e by simp
      show ?thesis
        using m DA e ground_e
          ord_resolve.intros[OF cas_len cs_len aas_len as_len nz cas aas_not_empt \<sigma>_p fo_elig ll]
        by auto
    qed
qed

lemma union_G_F_ground: \<open>is_ground_clss (\<Union> (\<G>_F ` M))\<close>
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
    using prems_\<iota>\<^sub>0_in union_G_F_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_in: \<open>DA \<in> set (prems_of \<iota>\<^sub>0)\<close>
    using \<iota>\<^sub>0_is by simp
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_\<iota>\<^sub>0_in union_G_F_ground is_ground_clss_def by auto
  obtain \<sigma> where
    grounded_res: \<open>ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
    using gr_ord_resolve_imp_ord_resolve[OF ground_DA ground_CAs gr_res] by auto
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
  then have \<open>\<iota>\<^sub>0 \<in> the (\<G>_Inf \<iota>)\<close>
    unfolding \<G>_Inf_def \<iota>_def CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric]
    apply (auto simp: \<iota>_def)
    apply (rule_tac x = \<eta>2 in exI)
    apply (rule_tac x = "\<eta>s @ [\<eta>]" in exI)
    apply (auto simp:is_ground_subst_list_def)
    apply (rule \<iota>\<^sub>0_is')
    apply (rule ground_n)
    using ground_ns is_ground_subst_list_def apply blast
    apply (rule ground_n2)
    apply (unfold \<iota>\<^sub>0_is'[symmetric])
    apply (rule \<iota>\<^sub>0_Inf_G)
    done
  moreover have \<open>\<iota> \<in> F.Inf_from M\<close>
    using prems_in i_Inf_F unfolding F.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation F: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G G.Red_Inf
  G.Red_F \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
proof
  show "po_on Empty_Order UNIV" unfolding po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Empty_Order UNIV" unfolding wfp_on_def by simp
qed

lemma inf_F_to_inf_G: \<open>\<iota> \<in> Inf_F \<Longrightarrow> the (\<G>_Inf \<iota>) \<subseteq> Inf_G\<close> for \<iota>
proof
  fix \<iota>'
  assume
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    i'_in: \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
  have g_some: \<open>\<G>_Inf \<iota> \<noteq> None\<close> unfolding \<G>_Inf_def by simp
  then show \<open>\<iota>' \<in> Inf_G\<close>
    using i_in i'_in unfolding \<G>_Inf_def by auto
qed

lemma inf_G_in_inf_F: \<open>Inf_G \<subseteq> Inf_F\<close>
  unfolding Inf_G_def Inf_F_def
  apply auto
  sorry

interpretation F: static_refutational_complete_calculus Bot_F Inf_F F.entails_\<G> F.Red_Inf_\<G>
  F.Red_F_\<G>
proof
  fix B N
  assume
    b_in: \<open>B \<in> Bot_F\<close> and
    n_sat: \<open>src.lifted_calculus_with_red_crit.saturated N\<close> and
    ent_b: \<open>F.entails_\<G> N {B}\<close>
  have \<open>B = {#}\<close> using b_in by simp
  have gn_sat: \<open>G.saturated (F.\<G>_set N)\<close>
    unfolding G.saturated_def
  proof
    fix \<iota>'
    assume i_in: \<open>\<iota>' \<in> F.Inf_from (F.\<G>_set N)\<close>
    obtain \<iota> where \<open>\<iota> \<in> F.Inf_from N\<close> \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close> using i_in lifting_in_framework sorry
    show \<open>\<iota>' \<in> G.Red_Inf (F.\<G>_set N)\<close> using i_in n_sat unfolding src.lifted_calculus_with_red_crit.saturated_def sorry
    oops

find_theorems name: G

end

definition entails_all_\<G>  :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<longleftrightarrow> \<Union> (grounding_of_cls ` N1) \<Turnstile>G \<Union> (grounding_of_cls ` N2)\<close>

(* definition Red_Inf_all_\<G> :: "'a clause set \<Rightarrow> 'a clause inference set" where
  \<open>Red_Inf_all_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> G.Red_Inf (\<G>_set N)}\<close> *)

end

end
