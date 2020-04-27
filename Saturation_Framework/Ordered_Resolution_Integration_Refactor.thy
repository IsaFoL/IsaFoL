(*  Title:       Ordered_Resolution_Integration
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

subsection \<open>Application of the saturation framework to Bachmair and Ganzinger's Resolution Prover, as formalize in the Ordered_Resolution_Prover theory in the AFP.\<close>

theory Ordered_Resolution_Integration_Refactor
imports
  Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
  Saturation_Framework.Prover_Architectures
  Standard_Redundancy_Criterion
  Soundness_Related
begin

section \<open>Setup\<close>

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of


section \<open>Library\<close>

context substitution
begin

lemma subst_cls_lists_append[simp]:
  "length Cs = length \<sigma>s \<Longrightarrow> length Cs' = length \<sigma>s' \<Longrightarrow>
   (Cs @ Cs') \<cdot>\<cdot>cl (\<sigma>s @ \<sigma>s') = Cs \<cdot>\<cdot>cl \<sigma>s @ Cs' \<cdot>\<cdot>cl \<sigma>s'"
  unfolding subst_cls_lists_def by auto

end


section \<open>Core Development\<close>

context FO_resolution_prover
begin
  
abbreviation Bot_F :: "'a clause set" where
  "Bot_F \<equiv> {{#}}"

definition entails_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>F" 50) where
  "S1 \<Turnstile>F S2 \<longleftrightarrow>
  (\<forall>I \<eta>. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s S1 \<cdot>cs \<sigma>) \<longrightarrow>
     is_ground_subst \<eta> \<longrightarrow> I \<Turnstile>s S2 \<cdot>cs \<eta>)"

definition (in -) list_mset :: "'b multiset \<Rightarrow> 'b list" where
  "list_mset M = (SOME L. mset L = M)"

lemma (in -) mset_list_mset [simp]: "mset (list_mset M) = M"
  using someI[of "\<lambda>x. mset x = M"] ex_mset[of M] unfolding list_mset_def by auto

lemma (in -) set_list_mset_set_mset [simp]: "set (list_mset M) = set_mset M"
  by (metis mset_list_mset set_mset_mset)

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
  { fix I \<eta>
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
    then have "I \<Turnstile> concl_of \<iota> \<cdot> \<eta>"
      by blast
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

interpretation sq: selection "S_M S M"
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
  "entails_G S1 S2 \<longleftrightarrow> (\<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2)"

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
    then have I_entails_concl: "I \<Turnstile> concl_of \<iota>"
      using gr.ord_resolve_sound[of CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_entails_prems Inf_G_has_prem i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
    then have "I \<Turnstile> concl_of \<iota>"
      by auto
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
  "\<lambda>N. clss_of_interp (ground_resolution_with_selection.INTERP (S_M S M) N)" Inf_G
  by (unfold_locales, fact Inf_G_has_prem, fact Inf_G_reductive, fact Inf_G_cex_reducing)

interpretation G: static_refutational_complete_calculus Bot_G Inf_G entails_G G.Red_Inf
  G.Red_F
proof
  fix B N
  assume
    B_in: \<open>B \<in> Bot_G\<close> and
    N_sat: \<open>G.saturated N\<close> and
    N_unsat: \<open>N \<Turnstile>G {B}\<close>
  have B_is: \<open>B = {#}\<close>
    using B_in by simp
  have \<open>{#} \<in> N\<close>
    using G.saturated_complete_if[OF N_sat] N_unsat unfolding B_is entails_G_def by force
  then show \<open>\<exists>B'\<in>Bot_G. B' \<in> N\<close>
    by simp
qed

definition \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F C = grounding_of_cls C\<close>

definition subst_inf :: \<open>'a clause inference \<Rightarrow> 's \<Rightarrow> 'a clause inference\<close> (infixl "\<cdot>i" 67) where
  \<open>\<iota> \<cdot>i \<sigma> = Infer (map (\<lambda>A. A \<cdot> \<sigma>) (prems_of \<iota>)) (concl_of \<iota> \<cdot> \<sigma>)\<close>

definition \<G>_Inf :: \<open>'a clause inference \<Rightarrow> 'a clause inference set option\<close> where
  \<open>\<G>_Inf \<iota> = Some {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)|\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> Inf_G}\<close>

interpretation \<G>_standard_lifting: standard_lifting Bot_F Inf_F Bot_G Inf_G entails_G G.Red_Inf
  G.Red_F \<G>_F \<G>_Inf
proof
  show \<open>Bot_G \<noteq> {}\<close>
    by simp
next
  fix B
  assume \<open>B \<in> Bot_G\<close>
  then have \<open>B = {#}\<close> by simp
  then have \<open>\<G>_F B = {{#}}\<close> unfolding \<G>_F_def by (simp add: ex_ground_subst)
  then show \<open>\<G>_F B \<noteq> {}\<close> by simp
next
  fix B
  assume \<open>B \<in> Bot_G\<close>
  then have \<open>B = {#}\<close> by simp
  then have \<open>\<G>_F B = {{#}}\<close> unfolding \<G>_F_def by (simp add: ex_ground_subst)
  then show \<open>\<G>_F B \<subseteq> Bot_G\<close> by simp
next
  fix C
  show \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_G\<close>
  proof (intro impI)
    assume \<open>\<G>_F C \<inter> Bot_G \<noteq> {}\<close>
    then have \<open>{#} \<in> \<G>_F C\<close> by blast
    then have \<open>C = {#}\<close> unfolding \<G>_F_def by (simp add: substitution_ops.grounding_of_cls_def)
    then show \<open>C \<in> Bot_G\<close> by simp
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
      using i'_in subst_inf_def unfolding \<G>_Inf_def \<G>_F_def grounding_of_cls_def by auto
    show \<open>\<iota>' \<in> G.Red_Inf (\<G>_F (concl_of \<iota>))\<close>
      using standard_lifting.inf_map i'_in2 concl_in by (simp add: G.Red_Inf_of_Inf_to_N)
  qed
qed

text \<open>This proof is based on part of the proof of @{thm RP_saturated_if_fair}.\<close>

lemma gr_ord_resolve_imp_ord_resolve:
  \<open>is_ground_cls DA \<Longrightarrow> is_ground_cls_list CAs \<Longrightarrow> gr.ord_resolve CAs DA AAs As E \<Longrightarrow>
  \<exists>\<sigma>. ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
proof -
  assume
    ground_DA: \<open>is_ground_cls DA\<close> and
    ground_CAs: \<open>is_ground_cls_list CAs\<close> and
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close>
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
  unfolding \<G>_F_def by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)

(* TODO: Starting with Isabelle2021, this will correspond to
   "FO_Ordered_Resolution.ord_resolve_rename_lifting". Use that instead. *)
lemma ord_resolve_rename_lifting_with_length:
  assumes
    sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" and
    res_e: "ord_resolve (S_M S M) CAs DA AAs As \<sigma> E" and
    select: "selection S" and
    grounding: "{DA} \<union> set CAs \<subseteq> grounding_of_clss M"
  obtains \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    "is_ground_subst \<eta>"
    "is_ground_subst_list \<eta>s"
    "is_ground_subst \<eta>2"
    "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0"
    "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" "DA0 \<cdot> \<eta> = DA" "E0 \<cdot> \<eta>2 = E" 
    "{DA0} \<union> set CAs0 \<subseteq> M"
    "length CAs0 = length CAs"
    "length \<eta>s = length CAs"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and
    aas_not_empt = this(9) and mgu = this(10) and eligible = this(11) and str_max = this(12) and
    sel_empt = this(13)

  have sel_ren_list_inv:
    "\<And>\<rho>s Cs. length \<rho>s = length Cs \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Cs \<cdot>\<cdot>cl \<rho>s) = map S Cs \<cdot>\<cdot>cl \<rho>s"
    using sel_stable unfolding is_renaming_list_def by (auto intro: nth_equalityI)

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  obtain DA0 \<eta>0 CAs0 \<eta>s0 As0 AAs0 D0 Cs0 where as0:
    "length CAs0 = n"
    "length \<eta>s0 = n"
    "DA0 \<in> M"
    "DA0 \<cdot> \<eta>0 = DA"
    "S DA0 \<cdot> \<eta>0 = S_M S M DA"
    "\<forall>CA0 \<in> set CAs0. CA0 \<in> M"
    "CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs"
    "map S CAs0 \<cdot>\<cdot>cl \<eta>s0 = map (S_M S M) CAs"
    "is_ground_subst \<eta>0"
    "is_ground_subst_list \<eta>s0"
    "As0 \<cdot>al \<eta>0 = As"
    "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs"
    "length As0 = n"
    "D0 \<cdot> \<eta>0 = D"
    "DA0 = D0 + (negs (mset As0))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
    "length Cs0 = n"
    "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
    "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)"
    "length AAs0 = n"
    using ord_resolve_obtain_clauses[of S M CAs DA, OF res_e select grounding n(2)
      \<open>DA = D + negs (mset As)\<close> \<open>\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)\<close> \<open>length Cs = n\<close>
      \<open>length AAs = n\<close>, of thesis] by blast

  note n = \<open>length CAs0 = n\<close> \<open>length \<eta>s0 = n\<close> \<open>length As0 = n\<close> \<open>length AAs0 = n\<close> \<open>length Cs0 = n\<close> n

  have "length (renamings_apart (DA0 # CAs0)) = Suc n"
    using n renamings_apart_length by auto

  note n = this n

  define \<rho> where
    "\<rho> = hd (renamings_apart (DA0 # CAs0))"
  define \<rho>s where
    "\<rho>s = tl (renamings_apart (DA0 # CAs0))"
  define DA0' where
    "DA0' = DA0 \<cdot> \<rho>"
  define D0' where
    "D0' = D0 \<cdot> \<rho>"
  define As0' where
    "As0' = As0 \<cdot>al \<rho>"
  define CAs0' where
    "CAs0' = CAs0 \<cdot>\<cdot>cl \<rho>s"
  define Cs0' where
    "Cs0' = Cs0 \<cdot>\<cdot>cl \<rho>s"
  define AAs0' where
    "AAs0' = AAs0 \<cdot>\<cdot>aml \<rho>s"
  define \<eta>0' where
    "\<eta>0' = inv_renaming \<rho> \<odot> \<eta>0"
  define \<eta>s0' where
    "\<eta>s0' = map inv_renaming \<rho>s \<odot>s \<eta>s0"

  have renames_DA0: "is_renaming \<rho>"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>_def
    by (metis length_greater_0_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  have renames_CAs0: "is_renaming_list \<rho>s"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>s_def
    by (metis is_renaming_list_def length_greater_0_conv list.set_sel(2) list.simps(3))

  have "length \<rho>s = n"
    unfolding \<rho>s_def using n by auto
  note n = n \<open>length \<rho>s = n\<close>
  have "length As0' = n"
    unfolding As0'_def using n by auto
  have "length CAs0' = n"
    using as0(1) n unfolding CAs0'_def by auto
  have "length Cs0' = n"
    unfolding Cs0'_def using n by auto
  have "length AAs0' = n"
    unfolding AAs0'_def using n by auto
  have "length \<eta>s0' = n"
    using as0(2) n unfolding \<eta>s0'_def by auto
  note n = \<open>length CAs0' = n\<close> \<open>length \<eta>s0' = n\<close> \<open>length As0' = n\<close> \<open>length AAs0' = n\<close> \<open>length Cs0' = n\<close> n

  have DA0'_DA: "DA0' \<cdot> \<eta>0' = DA"
    using as0(4) unfolding \<eta>0'_def DA0'_def using renames_DA0 by simp
  have D0'_D: "D0' \<cdot> \<eta>0' = D"
    using as0(14) unfolding \<eta>0'_def D0'_def using renames_DA0 by simp
  have As0'_As: "As0' \<cdot>al \<eta>0' = As"
    using as0(11) unfolding \<eta>0'_def As0'_def using renames_DA0 by auto
  have "S DA0' \<cdot> \<eta>0' = S_M S M DA"
    using as0(5) unfolding \<eta>0'_def DA0'_def using renames_DA0 sel_stable by auto
  have CAs0'_CAs: "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs"
    using as0(7) unfolding CAs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have Cs0'_Cs: "Cs0' \<cdot>\<cdot>cl \<eta>s0' = Cs"
    using as0(18) unfolding Cs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have AAs0'_AAs: "AAs0' \<cdot>\<cdot>aml \<eta>s0' = AAs"
    using as0(12) unfolding \<eta>s0'_def AAs0'_def using renames_CAs0 using n by auto
  have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs"
    unfolding CAs0'_def \<eta>s0'_def using as0(8) n renames_CAs0 sel_ren_list_inv by auto

  have DA0'_split: "DA0' = D0' + negs (mset As0')"
    using as0(15) DA0'_def D0'_def As0'_def by auto
  then have D0'_subset_DA0': "D0' \<subseteq># DA0'"
    by auto
  from DA0'_split have negs_As0'_subset_DA0': "negs (mset As0') \<subseteq># DA0'"
    by auto

  have CAs0'_split: "\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)"
    using as0(19) CAs0'_def Cs0'_def AAs0'_def n by auto
  then have "\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i"
    by auto
  from CAs0'_split have poss_AAs0'_subset_CAs0': "\<forall>i<n. poss (AAs0' ! i) \<subseteq># CAs0' ! i"
    by auto
  then have AAs0'_in_atms_of_CAs0': "\<forall>i < n. \<forall>A\<in>#AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
    by (auto simp add: atm_iff_pos_or_neg_lit)

  have as0':
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0') = S DA0'"
  proof -
    assume a: "S_M S M (D + negs (mset As)) \<noteq> {#}"
    then have "negs (mset As0) \<cdot> \<rho> = S DA0 \<cdot> \<rho>"
      using as0(16) unfolding \<rho>_def by metis
    then show "negs (mset As0') = S DA0'"
      using  As0'_def DA0'_def using sel_stable[of \<rho> DA0] renames_DA0 by auto
  qed

  have vd: "var_disjoint (DA0' # CAs0')"
    unfolding DA0'_def CAs0'_def using renamings_apart_var_disjoint
    unfolding \<rho>_def \<rho>s_def
    by (metis length_greater_0_conv list.exhaust_sel n(6) substitution.subst_cls_lists_Cons
        substitution_axioms zero_less_Suc)

  \<comment> \<open>Introduce ground substitution\<close>
  from vd DA0'_DA CAs0'_CAs have "\<exists>\<eta>. \<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    unfolding var_disjoint_def using n by auto
  then obtain \<eta> where \<eta>_p: "\<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    by auto
  have \<eta>_p_lit: "\<forall>i < Suc n. \<forall>L. L \<in># (DA0' # CAs0') ! i \<longrightarrow> L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and L :: "'a literal"
    assume a:
      "i < Suc n"
      "L \<in># (DA0' # CAs0') ! i"
    then have "\<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0' # \<eta>s0') ! i = S \<cdot> \<eta>"
      using \<eta>_p by auto
    then have "{# L #} \<cdot> (\<eta>0' # \<eta>s0') ! i = {# L #} \<cdot> \<eta>"
      using a by (meson single_subset_iff)
    then show "L \<cdot>l (\<eta>0' # \<eta>s0') ! i = L \<cdot>l \<eta>" by auto
  qed
  have \<eta>_p_atm: "\<forall>i < Suc n. \<forall>A. A \<in> atms_of ((DA0' # CAs0') ! i) \<longrightarrow> A \<cdot>a (\<eta>0'#\<eta>s0') ! i = A \<cdot>a \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and A :: "'a"
    assume a:
      "i < Suc n"
      "A \<in> atms_of ((DA0' # CAs0') ! i)"
    then obtain L where L_p: "atm_of L = A \<and> L \<in># (DA0' # CAs0') ! i"
      unfolding atms_of_def by auto
    then have "L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
      using \<eta>_p_lit a by auto
    then show "A \<cdot>a (\<eta>0' # \<eta>s0') ! i = A \<cdot>a \<eta>"
      using L_p unfolding subst_lit_def by (cases L) auto
  qed

  have DA0'_DA: "DA0' \<cdot> \<eta> = DA"
    using DA0'_DA \<eta>_p by auto
  have "D0' \<cdot> \<eta> = D" using \<eta>_p D0'_D n D0'_subset_DA0' by auto
  have "As0' \<cdot>al \<eta> = As"
  proof (rule nth_equalityI)
    show "length (As0' \<cdot>al \<eta>) = length As"
      using n by auto
  next
    fix i
    show "i<length (As0' \<cdot>al \<eta>) \<Longrightarrow> (As0' \<cdot>al \<eta>) ! i = As ! i"
    proof - 
      assume a: "i < length (As0' \<cdot>al \<eta>)"
      have A_eq: "\<forall>A. A \<in> atms_of DA0' \<longrightarrow> A \<cdot>a \<eta>0' = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      have "As0' ! i \<in> atms_of DA0'"
        using negs_As0'_subset_DA0' unfolding atms_of_def
        using a n by force
      then have "As0' ! i \<cdot>a \<eta>0' = As0' ! i \<cdot>a \<eta>"
         using A_eq by simp
      then show "(As0' \<cdot>al \<eta>) ! i = As ! i"
        using As0'_As \<open>length As0' = n\<close> a by auto
    qed
  qed

  interpret selection
    by (rule select)

  have "S DA0' \<cdot> \<eta> = S_M S M DA"
    using \<open>S DA0' \<cdot> \<eta>0' = S_M S M DA\<close> \<eta>_p S_selects_subseteq by auto

  from \<eta>_p have \<eta>_p_CAs0': "\<forall>i < n. (CAs0' ! i) \<cdot> (\<eta>s0' ! i) = (CAs0'! i) \<cdot> \<eta>"
    using n by auto
  then have "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have CAs0'_\<eta>_fo_CAs: "CAs0' \<cdot>cl \<eta> = CAs"
    using CAs0'_CAs \<eta>_p n by auto

  from \<eta>_p have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta>s0' ! i = S (CAs0' ! i) \<cdot> \<eta>"
    using S_selects_subseteq n by auto
  then have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map S CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have SCAs0'_\<eta>_fo_SMCAs: "map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs"
    using \<open>map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs\<close> by auto

  have "Cs0' \<cdot>cl \<eta> = Cs"
  proof (rule nth_equalityI)
    show "length (Cs0' \<cdot>cl \<eta>) = length Cs"
      using n by auto
  next
    fix i
    show "i<length (Cs0' \<cdot>cl \<eta>) \<Longrightarrow> (Cs0' \<cdot>cl \<eta>) ! i = Cs ! i"
    proof -
      assume "i < length (Cs0' \<cdot>cl \<eta>)"
      then have a: "i < n"
        using n by force
      have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = Cs ! i"
        using Cs0'_Cs a n by force
      moreover
      have \<eta>_p_CAs0': "\<forall>S. S \<subseteq># CAs0' ! i \<longrightarrow> S \<cdot> \<eta>s0' ! i = S \<cdot> \<eta>"
        using \<eta>_p a by force
      have "Cs0' ! i \<cdot> \<eta>s0' ! i = (Cs0' \<cdot>cl \<eta>) ! i"
        using \<eta>_p_CAs0' \<open>\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i\<close> a n by force
      then have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = (Cs0' \<cdot>cl \<eta>) ! i "
        using a n by force
      ultimately show "(Cs0' \<cdot>cl \<eta>) ! i = Cs ! i"
        by auto
    qed
  qed

  have AAs0'_AAs: "AAs0' \<cdot>aml \<eta> = AAs"
  proof (rule nth_equalityI)
    show "length (AAs0' \<cdot>aml \<eta>) = length AAs"
      using n by auto
  next
    fix i
    show "i<length (AAs0' \<cdot>aml \<eta>) \<Longrightarrow> (AAs0' \<cdot>aml \<eta>) ! i = AAs ! i"
    proof -
      assume a: "i < length (AAs0' \<cdot>aml \<eta>)"
      then have "i < n"
        using n by force
      then have "\<forall>A. A \<in> atms_of ((DA0' # CAs0') ! Suc i) \<longrightarrow> A \<cdot>a (\<eta>0' # \<eta>s0') ! Suc i = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      then have A_eq: "\<forall>A. A \<in> atms_of (CAs0' ! i) \<longrightarrow> A \<cdot>a \<eta>s0' ! i = A \<cdot>a \<eta>"
        by auto
      have AAs_CAs0': "\<forall>A \<in># AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
        using AAs0'_in_atms_of_CAs0' unfolding atms_of_def
        using a n by force
      then have "AAs0' ! i \<cdot>am  \<eta>s0' ! i = AAs0' ! i \<cdot>am \<eta>"
        unfolding subst_atm_mset_def using A_eq unfolding subst_atm_mset_def by auto
      then show "(AAs0' \<cdot>aml \<eta>) ! i = AAs ! i"
         using AAs0'_AAs \<open>length AAs0' = n\<close> \<open>length \<eta>s0' = n\<close> a by auto
    qed
  qed

  \<comment> \<open>Obtain MGU and substitution\<close>
  obtain \<tau> \<phi> where \<tau>\<phi>:
    "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
    "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
  proof -
    have uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (As0' \<cdot>al \<eta>) (AAs0' \<cdot>aml \<eta>)))"
      using mgu mgu_sound is_mgu_def unfolding \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
    have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As0' AAs0'))"
    proof -
      have "set_mset ` set (map2 add_mset As0' AAs0' \<cdot>aml \<eta>) =
        set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>"
        unfolding subst_atmss_def subst_atm_mset_list_def using subst_atm_mset_def subst_atms_def
        by (simp add: image_image subst_atm_mset_def subst_atms_def)
      then have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>)"
        using uu by (auto simp: n map2_add_mset_map)
      then show ?thesis
        using is_unifiers_comp by auto
    qed
    then obtain \<tau> where
      \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
      using mgu_complete
      by (metis (mono_tags, hide_lams) List.finite_set finite_imageI finite_set_mset image_iff)
    moreover then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
      by (metis (mono_tags, hide_lams) finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff
          mgu_sound set_mset_mset substitution_ops.is_mgu_def) (* should be simpler *)
    ultimately show thesis
      using that by auto
  qed

  \<comment> \<open>Lifting eligibility\<close>
  have eligible0': "eligible S \<tau> As0' (D0' + negs (mset As0'))"
  proof -
    have "S_M S M (D + negs (mset As)) = negs (mset As) \<or> S_M S M (D + negs (mset As)) = {#} \<and>
      length As = 1 \<and> maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      using eligible unfolding eligible.simps by auto
    then show ?thesis
    proof
      assume "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "S_M S M (D + negs (mset As)) \<noteq> {#}"
        using n by force
      then have "S (D0' + negs (mset As0')) = negs (mset As0')"
        using as0' DA0'_split by auto
      then show ?thesis
        unfolding eligible.simps[simplified]  by auto
    next
      assume asm: "S_M S M (D + negs (mset As)) = {#} \<and> length As = 1 \<and>
        maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      then have "S (D0' + negs (mset As0')) = {#}"
        using \<open>D0' \<cdot> \<eta> = D\<close>[symmetric] \<open>As0' \<cdot>al \<eta> = As\<close>[symmetric] \<open>S (DA0') \<cdot> \<eta> = S_M S M (DA)\<close>
          da DA0'_split subst_cls_empty_iff by metis
      moreover from asm have l: "length As0' = 1"
        using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
      moreover from asm have "maximal_wrt (As0' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D0' + negs (mset As0')) \<cdot> (\<tau> \<odot> \<phi>))"
        using \<open>As0' \<cdot>al \<eta> = As\<close> \<open>D0' \<cdot> \<eta> = D\<close> using l \<tau>\<phi> by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D0' + negs (mset As0')) \<cdot> \<tau> \<cdot> \<phi>)"
        by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau>) ((D0' + negs (mset As0')) \<cdot> \<tau>)"
        using maximal_wrt_subst by blast
      ultimately show ?thesis
        unfolding eligible.simps[simplified] by auto
    qed
  qed

  \<comment> \<open>Lifting maximality\<close>
  have maximality: "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
    (* Reformulate in list notation? *)
  proof -
    from str_max have "\<forall>i < n. strictly_maximal_wrt ((As0' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Cs0' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)"
      using \<open>As0' \<cdot>al \<eta> = As\<close>  \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a (\<tau> \<odot> \<phi>)) (Cs0' ! i \<cdot> (\<tau> \<odot> \<phi>))"
      using n \<tau>\<phi> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau> \<cdot>a \<phi>) (Cs0' ! i \<cdot> \<tau> \<cdot> \<phi>)"
      by auto
    then show "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
      using strictly_maximal_wrt_subst \<tau>\<phi> by blast
  qed

  \<comment> \<open>Lifting nothing being selected\<close>
  have nothing_selected: "\<forall>i < n. S (CAs0' ! i) = {#}"
  proof -
    have "\<forall>i < n. (map S CAs0' \<cdot>cl \<eta>) ! i = map (S_M S M) CAs ! i"
      by (simp add: \<open>map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs\<close>)
    then have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)"
      using n by auto
    then have "\<forall>i < n. S (CAs0' ! i)  \<cdot> \<eta> = {#}"
      using sel_empt \<open>\<forall>i < n.  S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)\<close> by auto
    then show "\<forall>i < n. S (CAs0' ! i) = {#}"
      using subst_cls_empty_iff by blast
  qed

  \<comment> \<open>Lifting AAs0's non-emptiness\<close>
  have "\<forall>i < n. AAs0' ! i \<noteq> {#}"
    using n aas_not_empt \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> by auto

  \<comment> \<open>Resolve the lifted clauses\<close>
  define E0' where
    "E0' = ((\<Union># (mset Cs0')) + D0') \<cdot> \<tau>"

  have res_e0': "ord_resolve S CAs0' DA0' AAs0' As0' \<tau> E0'"
    using ord_resolve.intros[of CAs0' n Cs0' AAs0' As0' \<tau> S D0',
      OF _ _ _ _ _ _ \<open>\<forall>i < n. AAs0' ! i \<noteq> {#}\<close> \<tau>\<phi>(1) eligible0'
        \<open>\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)\<close> \<open>\<forall>i < n. S (CAs0' ! i) = {#}\<close>]
    unfolding E0'_def using DA0'_split n \<open>\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)\<close> by blast

  \<comment> \<open>Prove resolvent instantiates to ground resolvent\<close>
  have e0'\<phi>e: "E0' \<cdot> \<phi> = E"
  proof -
    have "E0' \<cdot> \<phi> = ((\<Union># (mset Cs0')) + D0') \<cdot> (\<tau> \<odot> \<phi>)"
      unfolding E0'_def by auto
    also have "\<dots> = (\<Union># (mset Cs0') + D0') \<cdot> (\<eta> \<odot> \<sigma>)"
      using \<tau>\<phi> by auto
    also have "\<dots> = (\<Union># (mset Cs) + D) \<cdot> \<sigma>"
      using \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> \<open>D0' \<cdot> \<eta> = D\<close> by auto
    also have "\<dots> = E"
      using e by auto
    finally show e0'\<phi>e: "E0' \<cdot> \<phi> = E"
      .
  qed

  \<comment> \<open>Replace @{term \<phi>} with a true ground substitution\<close>
  obtain \<eta>2 where
    ground_\<eta>2: "is_ground_subst \<eta>2" "E0' \<cdot> \<eta>2 = E"
  proof -
    have "is_ground_cls_list CAs" "is_ground_cls DA"
      using grounding grounding_ground unfolding is_ground_cls_list_def by auto
    then have "is_ground_cls E"
      using res_e ground_resolvent_subset by (force intro: is_ground_cls_mono)
    then show thesis
      using that e0'\<phi>e make_ground_subst by auto
  qed

  have \<open>length CAs0 = length CAs\<close>
    using n by simp

  have \<open>length \<eta>s0 = length CAs\<close>
    using n by simp

  \<comment> \<open>Wrap up the proof\<close>
  have "ord_resolve S (CAs0 \<cdot>\<cdot>cl \<rho>s) (DA0 \<cdot> \<rho>) (AAs0 \<cdot>\<cdot>aml \<rho>s) (As0 \<cdot>al \<rho>) \<tau> E0'"
    using res_e0' As0'_def \<rho>_def AAs0'_def \<rho>s_def DA0'_def \<rho>_def CAs0'_def \<rho>s_def by simp
  moreover have "\<forall>i<n. poss (AAs0 ! i) \<subseteq># CAs0 ! i"
    using as0(19) by auto
  moreover have "negs (mset As0) \<subseteq># DA0"
    using local.as0(15) by auto
  ultimately have "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0'"
    using ord_resolve_rename[of CAs0 n AAs0 As0 DA0 \<rho> \<rho>s S \<tau> E0'] \<rho>_def \<rho>s_def n by auto
  then show thesis
    using that[of \<eta>0 \<eta>s0 \<eta>2 CAs0 DA0] \<open>is_ground_subst \<eta>0\<close> \<open>is_ground_subst_list \<eta>s0\<close>
      \<open>is_ground_subst \<eta>2\<close> \<open>CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs\<close> \<open>DA0 \<cdot> \<eta>0 = DA\<close> \<open>E0' \<cdot> \<eta>2 = E\<close> \<open>DA0 \<in> M\<close>
      \<open>\<forall>CA \<in> set CAs0. CA \<in> M\<close> \<open>length CAs0 = length CAs\<close> \<open>length \<eta>s0 = length CAs\<close>
  by blast
qed

(* TODO: Move to @{thy Abstract_Substitution}. *)
lemma subst_of_nth[simp]: \<open>i < length (Cs \<cdot>\<cdot>cl \<sigma>s) \<Longrightarrow> (Cs \<cdot>\<cdot>cl \<sigma>s) ! i = (Cs ! i) \<cdot> (\<sigma>s ! i)\<close>
  unfolding subst_cls_lists_def by auto

(* TODO: Move to @{thy Abstract_Substitution}. *)
lemma subst_Cons_nth:
  \<open>i < length ((C \<cdot> \<sigma>) # (Cs \<cdot>\<cdot>cl \<sigma>s)) \<Longrightarrow>
   ((C # Cs) ! i) \<cdot> ((\<sigma> # \<sigma>s) ! i) = ((C \<cdot> \<sigma>) # (Cs \<cdot>\<cdot>cl \<sigma>s)) ! i\<close>
by (auto simp: nth_Cons' simp del: subst_cls_lists_length)

lemma lifting_in_framework:
  \<open>\<iota>\<^sub>0 \<in> G.Inf_from (\<Union> (\<G>_F ` M)) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> F.Inf_from M \<and> \<iota>\<^sub>0 \<in> the (\<G>_Inf \<iota>)\<close>
proof -
  assume i\<^sub>0_in: \<open>\<iota>\<^sub>0 \<in> G.Inf_from (\<Union> (\<G>_F ` M))\<close>
  have prems_i\<^sub>0_in: \<open>set (prems_of \<iota>\<^sub>0) \<subseteq> \<Union> (\<G>_F ` M)\<close>
    using i\<^sub>0_in unfolding G.Inf_from_def by blast
  have i\<^sub>0_Inf_G: \<open>\<iota>\<^sub>0 \<in> Inf_G\<close>
    using i\<^sub>0_in unfolding G.Inf_from_def by blast
  then obtain CAs DA AAs As E where
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close> and
    i\<^sub>0: \<open>\<iota>\<^sub>0 = Infer (CAs @ [DA]) E\<close>
    unfolding Inf_G_def by auto

  have CAs_is: \<open>side_prems_of \<iota>\<^sub>0 = CAs\<close>
    using i\<^sub>0 unfolding side_prems_of_def by simp
  then have CAs_in: \<open>set CAs \<subseteq> set (prems_of \<iota>\<^sub>0)\<close>
    by (simp add: i\<^sub>0 subsetI)
  then have ground_CAs: \<open>is_ground_cls_list CAs\<close>
    using prems_i\<^sub>0_in union_G_F_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_is: \<open>main_prem_of \<iota>\<^sub>0 = DA\<close>
    using i\<^sub>0 unfolding main_prem_of_def by simp
  then have DA_in: \<open>DA \<in> set (prems_of \<iota>\<^sub>0)\<close>
    using i\<^sub>0 by simp
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_i\<^sub>0_in union_G_F_ground is_ground_clss_def by auto
  obtain \<sigma> where grounded_res: \<open>ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
    using gr_ord_resolve_imp_ord_resolve[OF ground_DA ground_CAs gr_res] by auto
  have prems_ground: \<open>{DA} \<union> set CAs \<subseteq> grounding_of_clss M\<close>
    using prems_i\<^sub>0_in CAs_in DA_in unfolding grounding_of_clss_def \<G>_F_def by fast
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

  have len_CAs0': "length CAs0 = length \<eta>s"
    using len_CAs0 len_ns by simp
  have \<iota>\<^sub>0': "\<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl (\<eta>s @ [\<eta>])) (E0 \<cdot> \<eta>2)"
    unfolding i\<^sub>0 by (auto simp: len_CAs0' CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric])

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
    apply (rule \<iota>\<^sub>0')
    apply (rule ground_n)
    using ground_ns is_ground_subst_list_def apply blast
    apply (rule ground_n2)
    apply (unfold \<iota>\<^sub>0'[symmetric])
    apply (rule i\<^sub>0_Inf_G)
    done
  moreover have \<open>\<iota> \<in> F.Inf_from M\<close>
    using prems_in i_Inf_F unfolding F.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation src: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G G.Red_Inf G.Red_F \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
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
proof
  fix \<iota>
  assume i_in: \<open>\<iota> \<in> Inf_G\<close>
  obtain \<iota>_RP where i_RP_in: \<open>\<iota>_RP \<in> gr.ord_\<Gamma>\<close> and i_i_RP: \<open>same_inf \<iota>_RP \<iota>\<close> using i_in unfolding Inf_G_def by blast
  have \<open>\<iota>_RP \<in> ord_FO_\<Gamma> S\<close> using i_RP_in unfolding gr.ord_\<Gamma>_def ord_FO_\<Gamma>_def sorry
  show \<open>\<iota> \<in> Inf_F\<close> unfolding Inf_F_def gr.ord_resolve.simps ord_resolve_rename.simps
  apply auto
  sorry
  oops

find_theorems  gr.ord_\<Gamma>

interpretation static_refutational_complete_calculus Bot_F Inf_F \<G>_standard_lifting.entails_\<G> src.Red_Inf_\<G> src.Red_F_\<G>
proof
  fix B N
  assume
    b_in: \<open>B \<in> Bot_F\<close> and
    n_sat: \<open>src.lifted_calculus_with_red_crit.saturated N\<close> and
    ent_b: \<open>\<G>_standard_lifting.entails_\<G> N {B}\<close>
  have \<open>B = {#}\<close> using b_in by simp
  have gn_sat: \<open>G.saturated (\<G>_standard_lifting.\<G>_set N)\<close>
    unfolding G.saturated_def
  proof
    fix \<iota>'
    assume i_in: \<open>\<iota>' \<in> Inf_from (\<G>_standard_lifting.\<G>_set N)\<close>
    obtain \<iota> where \<open>\<iota> \<in> F.Inf_from N\<close> \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close> using i_in lifting_in_framework sorry
    show \<open>\<iota>' \<in> G.Red_Inf (\<G>_standard_lifting.\<G>_set N)\<close> using i_in n_sat unfolding src.lifted_calculus_with_red_crit.saturated_def sorry
    oops

find_theorems name: G

end

definition entails_all_\<G>  :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<equiv> \<Union> (grounding_of_cls ` N1) \<Turnstile>G \<Union> (grounding_of_cls ` N2)\<close>

(* definition Red_Inf_all_\<G> :: "'a clause set \<Rightarrow> 'a clause inference set" where
  \<open>Red_Inf_all_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> G.Red_Inf (\<G>_set N)}\<close> *)
  
end

end
