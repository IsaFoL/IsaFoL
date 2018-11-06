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


context FO_resolution_prover
begin

(* This part corresponds to section 5.2 step (1) in the technical report*)
abbreviation Bot_F :: "'a clause set" where "Bot_F \<equiv> {{#}}"

definition entails_sound_F :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>F" 50)  where
  "S1 |\<approx>F S2 \<equiv> \<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"

definition (in -) list_mset :: "'b multiset \<Rightarrow> 'b list" where
  "list_mset M = (SOME L. mset L = M)"

lemma (in -) mset_list_mset [simp]: "mset (list_mset M) = M"
  using someI[of "\<lambda>x. mset x = M"] ex_mset[of M] unfolding list_mset_def by auto

lemma (in -) set_list_mset_set_mset [simp]: "set (list_mset M) = set_mset M"
  by (metis mset_list_mset set_mset_mset)

definition conv_inf :: "'a inference \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference" where
  "conv_inf \<iota> = Saturation_Framework_Preliminaries.inference.Infer (list_mset (prems_of \<iota>)) (concl_of \<iota>)"

definition Inf_F :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_F = conv_inf ` (ord_FO_\<Gamma> S)"

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_F entails_sound_F Inf_F 
  unfolding Saturation_Framework_Preliminaries.sound_inference_system_def
    consequence_relation_def entails_sound_F_def
    Saturation_Framework_Preliminaries.sound_inference_system_axioms_def
proof auto
  fix N1 N2 I
  assume
    incl: "N2 \<subseteq> N1" and
    entails: "I \<Turnstile>s N1"
  show "I \<Turnstile>s N2" using true_clss_mono[OF incl entails] by simp
next
  fix N1 N2 I
  assume
    "\<forall>C\<in>N2. \<forall>I. I \<Turnstile>s N1 \<longrightarrow> I \<Turnstile> C" and
    "I \<Turnstile>s N1"
  then show "I \<Turnstile>s N2" by (simp add: true_clss_def)
next
  fix \<iota> I
  assume
    i_in: "\<iota> \<in> Inf_F" and
    I_entails_prems: "I \<Turnstile>s set (inference.prems_of \<iota>)"
  obtain \<iota>_RP where i_RP_in: "\<iota>_RP \<in> (ord_FO_\<Gamma> S)" and i_i_RP: "conv_inf \<iota>_RP = \<iota>"
    using i_in unfolding Inf_F_def by blast
  have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
    using i_i_RP unfolding conv_inf_def by fastforce
  have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
    using i_i_RP unfolding conv_inf_def by fastforce
  have I_entails_prems_RP: "I \<Turnstile>s set_mset (prems_of \<iota>_RP)" using prems I_entails_prems by argo
  have I_entails_concl_RP: "I \<Turnstile> concl_of \<iota>_RP"
    using I_entails_prems_RP sound_inference_system.\<Gamma>_sound[of "ord_FO_\<Gamma> S" "side_prems_of \<iota>_RP"
      "main_prem_of \<iota>_RP" "concl_of \<iota>_RP" I] i_RP_in apply auto sorry
  then show "I \<Turnstile> Saturation_Framework_Preliminaries.inference.concl_of \<iota>" 

oops


abbreviation Bot_G :: "'a clause set" where "Bot_G \<equiv> {{#}}"

definition Inf_G :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_G = {\<iota> \<in> Inf_F. filter (\<lambda>C. \<not> (is_ground_cls C)) (Saturation_Framework_Preliminaries.inference.prems_of \<iota>) = []}"

(* This part corresponds to section 5.2 step (2) in the technical report*)

definition ground_subset :: "'a clause set \<Rightarrow> 'a clause set" where
  "ground_subset S' = {C \<in> S'. is_ground_cls C}"

definition entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> \<forall>I. I \<Turnstile>s ground_subset S1 \<longrightarrow> I \<Turnstile>s ground_subset S2"

definition entails_comp_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>G" 50) where
  "S1 \<Turnstile>G S2 \<equiv> \<forall>C2 \<in> ground_subset S2. \<exists>C1 \<in> ground_subset S1. \<forall>I. I \<Turnstile> C1 \<longrightarrow> I \<Turnstile> C2"

end

end

