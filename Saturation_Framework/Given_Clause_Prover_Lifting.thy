(*  Title:       Dynamic_Completeness_Lifting
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Lifting a Single-Clause-Set Proving Process to a Given-Clause Prover\<close>

subsection \<open>Application to Bachmair and Ganzinger's Resolution Prover\<close>

theory Given_Clause_Prover_Lifting
  imports
    Dynamic_Completeness_Lifting
    Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
    "../lib/Explorer"
begin

text \<open>This part corresponds to section 5.2 in the technical report\<close> 
context FO_resolution_prover
begin

abbreviation Bot_F :: "'a clause set" where "Bot_F \<equiv> {{#}}"

definition entails_sound_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>F" 50)  where
  "S1 |\<approx>F S2 \<equiv> (\<forall>I \<eta>. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s S1 \<cdot>cs \<sigma>)  \<longrightarrow> is_ground_subst \<eta>  \<longrightarrow> I \<Turnstile>s S2 \<cdot>cs \<eta>)" (*\<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"*)

definition (in -) list_mset :: "'b multiset \<Rightarrow> 'b list" where
  "list_mset M = (SOME L. mset L = M)"

lemma (in -) mset_list_mset [simp]: "mset (list_mset M) = M"
  using someI[of "\<lambda>x. mset x = M"] ex_mset[of M] unfolding list_mset_def by auto

lemma (in -) set_list_mset_set_mset [simp]: "set (list_mset M) = set_mset M"
  by (metis mset_list_mset set_mset_mset)

definition conv_inf :: "'a inference \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference" where
  "conv_inf \<iota> = Saturation_Framework_Preliminaries.inference.Infer (list_mset (side_prems_of \<iota>)) (main_prem_of \<iota>) (concl_of \<iota>)"

definition Inf_F :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_F = conv_inf ` (ord_FO_\<Gamma> S)"

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_F entails_sound_F Inf_F 
proof -
  { text \<open>proof of @{locale Saturation_Framework_Preliminaries.consequence_relation}, \<open>subset_entailed\<close> assumption\<close>
    fix N1 N2 I \<eta>
    assume
      incl: "N2 \<subseteq> N1" and
      ground_subst: "is_ground_subst \<eta>" and
      entails: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>"
    have incl_subst: "N2 \<cdot>cs \<eta> \<subseteq> N1 \<cdot>cs \<eta>" using incl unfolding subst_clss_def by blast
    have "I \<Turnstile>s N2 \<cdot>cs \<eta>"
      using entails ground_subst true_clss_mono[OF incl_subst, of I] by blast 
  }
  moreover
  { text \<open>proof of @{locale Saturation_Framework_Preliminaries.consequence_relation},
      \<open>all_formulas_entailed\<close> assumption\<close>
    fix N1 N2 I \<eta>
    assume
      all_clss_entailed: "\<forall>C\<in>N2.
        \<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>) \<longrightarrow> (\<forall>\<eta>. is_ground_subst \<eta> \<longrightarrow> I \<Turnstile> C \<cdot> \<eta>)" and
      ground_subst: "is_ground_subst \<eta>" and
      entails: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>"
    then have "I \<Turnstile>s N2 \<cdot>cs \<eta>" by (simp add: subst_clss_def true_clss_def)
  }
  moreover
  { text \<open>proof of @{locale Saturation_Framework_Preliminaries.sound_inference_system}, soundness assumption\<close>
    fix \<iota> I \<eta>
    assume
      i_in: "\<iota> \<in> Inf_F" and
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (Saturation_Framework_Preliminaries.prems_of \<iota>) \<cdot>cs \<sigma>" and
      ground_subst: "is_ground_subst \<eta>"
    obtain \<iota>_RP where i_RP_in: "\<iota>_RP \<in> (ord_FO_\<Gamma> S)" and i_i_RP: "conv_inf \<iota>_RP = \<iota>"
      using i_in unfolding Inf_F_def by blast
    obtain CAs AAs As \<sigma> where the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>_RP) AAs As \<sigma> (concl_of \<iota>_RP)"
      and mset_CAs: "mset CAs = side_prems_of \<iota>_RP" using i_RP_in unfolding ord_FO_\<Gamma>_def by auto
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_i_RP unfolding conv_inf_def by fastforce
    have prems: "set (Saturation_Framework_Preliminaries.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_i_RP unfolding conv_inf_def prems_of_def by fastforce
    have I_entails_prems_RP: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set_mset (prems_of \<iota>_RP) \<cdot>cs \<sigma>"
      using prems I_entails_prems by presburger
    have I_entails_concl_RP: "I \<Turnstile> (concl_of \<iota>_RP) \<cdot> \<eta>"
      using ground_subst I_entails_prems_RP ord_resolve_rename_sound[OF the_inf, of I \<eta>]
      by (metis mset_CAs set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
    then have "I \<Turnstile> (Saturation_Framework_Preliminaries.inference.concl_of \<iota>) \<cdot> \<eta>" 
      using concl by simp
  }
  ultimately show "Saturation_Framework_Preliminaries.sound_inference_system Bot_F (|\<approx>F) Inf_F"
    unfolding Saturation_Framework_Preliminaries.sound_inference_system_def
      consequence_relation_def entails_sound_F_def
      Saturation_Framework_Preliminaries.sound_inference_system_axioms_def
    by auto \<comment> \<open>the other assumptions to prove are handled by auto\<close>
qed

abbreviation Bot_G :: "'a clause set" where "Bot_G \<equiv> {{#}}"

interpretation gr: ground_resolution_with_selection S
  by unfold_locales

(* Not yet too sure about which version to select. Is this one even correct? *)
definition Inf_G :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_G \<equiv> conv_inf ` gr.ord_\<Gamma>"

(*definition Inf_G :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_G = {\<iota> \<in> Inf_F. filter (\<lambda>C. \<not> (is_ground_cls C))
  (Saturation_Framework_Preliminaries.inference.prems_of \<iota>) = []}"*)

(*definition ground_subset :: "'a clause set \<Rightarrow> 'a clause set" where
  "ground_subset S' = {C \<in> S'. is_ground_cls C}"*)

(* lemma Bot_G_ground [simp]: "ground_subset Bot_G = Bot_G" unfolding ground_subset_def by fastforce

definition entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> \<forall>I. I \<Turnstile>s ground_subset S1 \<longrightarrow> I \<Turnstile>s ground_subset S2"*)

definition entails_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool"  where
  "entails_G S1 S2 \<equiv> \<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"

abbreviation entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> entails_G S1 S2"

(*lemma ground_subst_on_ground_subset: "is_ground_subst \<sigma> \<Longrightarrow> (ground_subset N) \<cdot>cs \<sigma> = (ground_subset N)"
  by (simp add: ground_subset_def is_ground_cls_def is_ground_clss_def is_ground_lit_def) *)

(*lemma Inf_G_ground_concl: "\<iota> \<in> Inf_G \<Longrightarrow>
  is_ground_cls (Saturation_Framework_Preliminaries.inference.concl_of \<iota>)" 
proof -
  fix \<iota>
  assume
    i_in: "\<iota> \<in> Inf_G"
  have "filter (\<lambda>C. \<not> is_ground_cls C) (inference.prems_of \<iota>) = []"
    using i_in unfolding Inf_G_def Inf_F_def conv_inf_def by auto 
  then have "C \<in> set (Saturation_Framework_Preliminaries.inference.prems_of \<iota>) \<Longrightarrow> is_ground_cls C"
  explore
    oops*)

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_G entails_sound_G Inf_G
proof -
  {
    (*fix N1 N2 I
    assume
      incl: "N2 \<subseteq> N1" and
      entails: "I \<Turnstile>s ground_subset N1"
    have ground_incl: "ground_subset N2 \<subseteq> ground_subset N1" using incl unfolding ground_subset_def by fast
    have "I \<Turnstile>s ground_subset N2" using true_clss_mono[OF ground_incl entails] . *)
    fix N1 N2 I
    assume
      incl: "N2 \<subseteq> N1" and
      entails: "I \<Turnstile>s N1"
    have "I \<Turnstile>s N2" using true_clss_mono[OF incl entails] . 
  }
  moreover
  {
    (*fix N1 N2 I
    assume
      all_clss_entailed: "\<forall>C\<in>N2. \<forall>I. I \<Turnstile>s ground_subset N1 \<longrightarrow> I \<Turnstile>s ground_subset {C}" and
      entails: "I \<Turnstile>s ground_subset N1"
    then have "I \<Turnstile>s ground_subset N2" by (simp add: all_clss_entailed entails true_clss_def ground_subset_def)*)
    fix N1 N2 I
    assume
      all_clss_entailed: "\<forall>C\<in>N2. \<forall>I. I \<Turnstile>s N1 \<longrightarrow> I \<Turnstile> C" and
      entails: "I \<Turnstile>s N1"
    then have "I \<Turnstile>s N2" by (simp add: all_clss_entailed entails true_clss_def)
  }
  moreover
  {
    fix \<iota> I
    assume
      i_in: "\<iota> \<in> Inf_G" and
      I_entails_prems: "I \<Turnstile>s (set (Saturation_Framework_Preliminaries.prems_of \<iota>))"
    obtain \<iota>_RP where i_equal: "\<iota> = conv_inf \<iota>_RP" and i_RP_in: "\<iota>_RP \<in> gr.ord_\<Gamma>" (*"\<iota>_RP \<in> (ord_FO_\<Gamma> S)" *)
      using i_in unfolding Inf_G_def by blast
    obtain CAs AAs As
      where the_inf: "ground_resolution_with_selection.ord_resolve S CAs (main_prem_of \<iota>_RP) AAs As (concl_of \<iota>_RP)"
      and mset_CAs: "side_prems_of \<iota>_RP = mset CAs" using i_RP_in unfolding gr.ord_\<Gamma>_def by force
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_equal unfolding conv_inf_def by fastforce
    have prems: "set (Saturation_Framework_Preliminaries.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_equal unfolding conv_inf_def prems_of_def by simp
    have I_entails_prems_RP: "I \<Turnstile>s set_mset (prems_of \<iota>_RP)" using prems I_entails_prems by argo
    then have I_entails_concl_RP: "I \<Turnstile> concl_of \<iota>_RP"
      using ground_resolution_with_selection.ord_resolve_sound[of S CAs "main_prem_of \<iota>_RP" AAs As "concl_of \<iota>_RP" I]
        the_inf mset_CAs gr.ground_resolution_with_selection_axioms by fastforce
    then have "I \<Turnstile> Saturation_Framework_Preliminaries.inference.concl_of \<iota>" using concl by auto
  }
  ultimately show "Saturation_Framework_Preliminaries.sound_inference_system Bot_G (|\<approx>G) Inf_G"
    unfolding Saturation_Framework_Preliminaries.sound_inference_system_def
      consequence_relation_def entails_G_def
      Saturation_Framework_Preliminaries.sound_inference_system_axioms_def
    by auto
qed

abbreviation entails_comp_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>G" 50) where
  "S1 \<Turnstile>G S2 \<equiv> entails_G S1 S2"

interpretation Saturation_Framework_Preliminaries.consequence_relation Bot_G entails_comp_G
  by (rule consequence_relation_axioms)

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_G entails_comp_G Inf_G
  by (rule sound_inference_system_axioms)

interpretation sr: standard_redundancy_criterion_reductive gr.ord_\<Gamma>
  by unfold_locales

definition Red_Inf_G :: "'a clause set \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference set" where
  "Red_Inf_G S1 \<equiv> (\<lambda>x. (conv_inf ` (sr.Ri x))) S1"

definition Red_F_G :: "'a clause set \<Rightarrow> 'a clause set" where
  "Red_F_G S1 \<equiv> sr.Rf S1"

interpretation gr_calc: Saturation_Framework_Preliminaries.calculus Bot_G entails_sound_G Inf_G
  entails_comp_G Red_Inf_G Red_F_G
  unfolding calculus_def
proof (intro conjI)
  show \<open>Saturation_Framework_Preliminaries.sound_inference_system Bot_G (\<Turnstile>G) Inf_G\<close>
    by (rule sound_inference_system_axioms)
next
  show \<open>consequence_relation Bot_G (\<Turnstile>G)\<close> by (rule consequence_relation_axioms)
next
  show \<open>calculus_axioms Bot_G Inf_G (\<Turnstile>G) Red_Inf_G Red_F_G\<close> unfolding calculus_axioms_def
  proof (intro conjI allI impI)
    fix N
    show \<open>Red_Inf_G N \<subseteq> Inf_G\<close> unfolding Inf_G_def Red_Inf_G_def using sr.Ri_subset_\<Gamma> by fastforce
  next
    fix B N
    assume
      B_in: \<open>B \<in> Bot_G\<close> and
      N_unsat: \<open>N \<Turnstile>G {B}\<close>
    then show \<open>N - Red_F_G N \<Turnstile>G {B}\<close>
      unfolding Red_F_G_def entails_G_def using standard_redundancy_criterion.Rf_model by force
  next
    fix N N' :: "'a clause set"
    assume \<open>N \<subseteq> N'\<close>
    then show \<open>Red_F_G N \<subseteq> Red_F_G N'\<close> by (simp add: Red_F_G_def sr.Rf_mono)
  next
    fix N N' :: "'a clause set"
    assume \<open>N \<subseteq> N'\<close>
    then show \<open>Red_Inf_G N \<subseteq> Red_Inf_G N'\<close> by (simp add: Red_Inf_G_def image_mono sr.Ri_mono)
  next
    fix N N' :: "'a clause set"
    assume \<open>N' \<subseteq> Red_F_G N\<close>
    then show \<open>Red_F_G N \<subseteq> Red_F_G (N - N')\<close> by (simp add: Red_F_G_def sr.Rf_indep)
  next
    fix N N' :: "'a clause set"
    assume \<open>N' \<subseteq> Red_F_G N\<close>
    then show \<open>Red_Inf_G N \<subseteq> Red_Inf_G (N - N')\<close> by (simp add: Red_F_G_def Red_Inf_G_def image_mono sr.Ri_indep)
  next
    fix \<iota> N
    assume
      i_in: \<open>\<iota> \<in> Inf_G\<close> and
      concl_in: \<open>Saturation_Framework_Preliminaries.inference.concl_of \<iota> \<in> N\<close>
    obtain \<iota>_RP where i_equal: "\<iota> = conv_inf \<iota>_RP" and i_RP_in: "\<iota>_RP \<in> gr.ord_\<Gamma>"
      using i_in unfolding Inf_G_def by blast
    then have \<open>concl_of \<iota>_RP \<in> N\<close> using concl_in by (simp add: conv_inf_def)
    then have \<open>\<iota>_RP \<in> sr.Ri N\<close> using i_RP_in by (simp add: sr.Ri_effective)
    then show \<open>\<iota> \<in> Red_Inf_G N\<close> unfolding Red_Inf_G_def Inf_G_def using i_equal by simp 
  qed
qed

lemma conv_inf_inf_from_commute: \<open>conv_inf ` gr.inferences_from (N - sr.Rf N) \<subseteq> gr_calc.Inf_from N\<close> 
proof
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> conv_inf ` gr.inferences_from (N - sr.Rf N)\<close>
  have \<open>\<iota> \<in> conv_inf ` gr.inferences_from N\<close>
  proof - (* rebuild by sledgehammer *)
    have "gr.inferences_from (N - sr.Rf N) \<subseteq> gr.inferences_from N"
      by (simp add: Diff_subset gr.inferences_from_mono)
    then show ?thesis
      using i_in by blast
  qed
  then obtain \<iota>_RP where i_RP_from: \<open>\<iota>_RP \<in> gr.inferences_from N\<close> and i_to_i_RP: \<open>\<iota> = conv_inf \<iota>_RP\<close> by fast
  have \<open>set_mset (prems_of \<iota>_RP) \<subseteq> N\<close> using i_RP_from unfolding gr.inferences_from_def infer_from_def by fast
  then have i_from: \<open>set (Saturation_Framework_Preliminaries.prems_of \<iota>) \<subseteq> N\<close> using i_to_i_RP unfolding conv_inf_def prems_of_def by auto
  have \<open>\<iota> \<in> Inf_G\<close> using i_RP_from i_to_i_RP unfolding gr.inferences_from_def Inf_G_def by blast
  then show \<open>\<iota> \<in> gr_calc.Inf_from N\<close> using i_from unfolding gr_calc.Inf_from_def by fast
qed

term gr.ord_\<Gamma>

find_theorems "main_prem_of _ = main_prem_of _"

lemma \<open>\<iota> \<in> gr.ord_\<Gamma> \<Longrightarrow> \<iota>' \<in> gr.ord_\<Gamma> \<Longrightarrow> prems_of \<iota> = prems_of \<iota>' \<Longrightarrow> concl_of \<iota> = concl_of \<iota>' \<Longrightarrow> main_prem_of \<iota> = main_prem_of \<iota>'\<close>
proof (rule ccontr)
  fix \<iota> \<iota>'
  assume
    i_in: \<open>\<iota> \<in> gr.ord_\<Gamma>\<close> and
    i'_in: \<open>\<iota>' \<in> gr.ord_\<Gamma>\<close> and
    prems_eq: \<open>prems_of \<iota> = prems_of \<iota>'\<close> and
    concl_eq: \<open>concl_of \<iota> = concl_of \<iota>'\<close> and
    contra: \<open>main_prem_of \<iota> \<noteq> main_prem_of \<iota>'\<close>
  obtain CC AAs As where i_inf: \<open>gr.ord_resolve CC (main_prem_of \<iota>) AAs As (concl_of \<iota>)\<close> and
    \<open>mset CC = side_prems_of \<iota>\<close>
    using i_in unfolding gr.ord_\<Gamma>_def by force
  obtain CC' AAs' As' where i'_inf: \<open>gr.ord_resolve CC' (main_prem_of \<iota>') AAs' As' (concl_of \<iota>')\<close> and
    \<open>mset CC' = side_prems_of \<iota>'\<close>
    using i'_in unfolding gr.ord_\<Gamma>_def by force
  have "AAs = AAs'" using i_inf i'_inf prems_eq concl_eq sorry 
oops

lemma
  assumes \<open>gr_calc.saturated N\<close>
  shows \<open>sr.saturated_upto N\<close>
    using assms unfolding sr.saturated_upto_def gr_calc.saturated_def apply -
proof (rule ccontr) (* contradiction proof attempt *)
  assume \<open>\<not> gr.inferences_from (N - sr.Rf N) \<subseteq> sr.Ri N\<close>
  then obtain \<iota>_RP where i_not_in: \<open>\<iota>_RP \<notin> sr.Ri N\<close> and i_in: \<open>\<iota>_RP \<in> gr.inferences_from (N - sr.Rf N)\<close> by blast
  have \<open>conv_inf \<iota>_RP \<in> gr_calc.Inf_from N\<close> using i_in conv_inf_inf_from_commute by fast
  have \<open>conv_inf \<iota>_RP \<notin> Red_Inf_G N\<close> using i_not_in unfolding Red_Inf_G_def sorry

  show \<open>False\<close>
  (* direct proof attempt
  fix \<iota>_RP
  assume
    sat: \<open>gr_calc.Inf_from N \<subseteq> Red_Inf_G N\<close> and
    i_RP_from: \<open>\<iota>_RP \<in> gr.inferences_from (N - sr.Rf N)\<close>
  have \<open>conv_inf \<iota>_RP \<in> gr_calc.Inf_from N\<close> using conv_inf_inf_from_commute[of N] i_RP_from by blast
  then have \<open>conv_inf \<iota>_RP \<in> Red_Inf_G N\<close> using sat by blast
  have \<open>\<And>\<iota>_RP2. prems_of \<iota>_RP2 = prems_of \<iota>_RP \<Longrightarrow> conv_inf \<iota>_RP2 \<in> Red_Inf_G N \<Longrightarrow> \<iota>_RP2 \<in> sr.Ri N\<close>
    using i_RP_from unfolding Red_Inf_G_def gr.inferences_from_def unfolding infer_from_def sr.Ri_def
*)
(* another direct proof attempt
  then obtain \<iota>_RP2 where i_RP2_in: \<open>\<iota>_RP2 \<in> sr.Ri N\<close> and prems: \<open>prems_of \<iota>_RP2 = prems_of \<iota>_RP\<close> and
    concl: \<open>concl_of \<iota>_RP2 = concl_of \<iota>_RP\<close> unfolding Red_Inf_G_def conv_inf_def
    by (metis (mono_tags, lifting) Saturation_Framework_Preliminaries.inference.sel(1)
      Saturation_Framework_Preliminaries.inference.sel(2) image_iff mset_list_mset)
  have \<open>\<iota>_RP2 \<in> gr.inferences_from (N - sr.Rf N)\<close> using prems concl i_RP_from
    by (metis (no_types, lifting) i_RP2_in gr.inferences_from_def infer_from_def mem_Collect_eq
      standard_redundancy_criterion.Ri_subset_\<Gamma> subsetCE)
      *)
  (* then show \<open>\<iota>_RP \<in> sr.Ri N\<close> unfolding sr.Ri_def *)
oops



interpretation Saturation_Framework_Preliminaries.static_refutational_complete_calculus Bot_G
  entails_sound_G Inf_G entails_comp_G Red_Inf_G Red_F_G
  proof
    fix B N
    assume
      B_in: \<open>B \<in> Bot_G\<close> and
      N_sat: \<open>gr_calc.saturated N\<close> and
      \<open>N \<Turnstile>G {B}\<close>
    have \<open>B = {#}\<close> using B_in by simp
    have \<open>sr.saturated_upto N\<close> unfolding sr.saturated_upto_def
    proof
      fix \<iota>_RP
      assume
        i_RP_from: \<open>\<iota>_RP \<in> gr.inferences_from (N - sr.Rf N)\<close>
      define \<iota> where \<open>\<iota> = conv_inf \<iota>_RP\<close>
      then have \<open>\<iota> \<in> gr_calc.Inf_from N\<close> using i_RP_from sorry
      then show \<open>\<iota>_RP \<in> sr.Ri N\<close> unfolding gr.inferences_from_def sorry
    qed
    show \<open>\<exists>B'\<in>Bot_G. B' \<in> N\<close>
      unfolding gr_calc.saturated_def sorry
oops

end

end

