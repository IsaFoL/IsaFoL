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

(* This part corresponds to section 5.2 in the technical report*)
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
  "conv_inf \<iota> = Saturation_Framework_Preliminaries.inference.Infer (list_mset (prems_of \<iota>)) (concl_of \<iota>)"

definition Inf_F :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_F = conv_inf ` (ord_FO_\<Gamma> S)"

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_F entails_sound_F Inf_F 
proof - 
  { (*Saturation_Framework_Preliminaries.consequence_relation, subset_entailed assumption*)
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
  { (* Saturation_Framework_Preliminaries.consequence_relation, all_formulas_entailed assumption *)
    fix N1 N2 I \<eta>
    assume
      all_clss_entailed: "\<forall>C\<in>N2.
        \<forall>I. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>) \<longrightarrow> (\<forall>\<eta>. is_ground_subst \<eta> \<longrightarrow> I \<Turnstile> C \<cdot> \<eta>)" and
      ground_subst: "is_ground_subst \<eta>" and
      entails: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s N1 \<cdot>cs \<sigma>"
    then have "I \<Turnstile>s N2 \<cdot>cs \<eta>" by (simp add: subst_clss_def true_clss_def)
  }
  moreover
  { (* Saturation_Framework_Preliminaries.sound_inference_system, soundness assumption *)
    fix \<iota> I \<eta>
    assume
      i_in: "\<iota> \<in> Inf_F" and
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (inference.prems_of \<iota>) \<cdot>cs \<sigma>" and
      ground_subst: "is_ground_subst \<eta>"
    obtain \<iota>_RP where i_RP_in: "\<iota>_RP \<in> (ord_FO_\<Gamma> S)" and i_i_RP: "conv_inf \<iota>_RP = \<iota>"
      using i_in unfolding Inf_F_def by blast
    obtain CAs AAs As \<sigma> where the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>_RP) AAs As \<sigma> (concl_of \<iota>_RP)"
      and mset_CAs: "mset CAs = side_prems_of \<iota>_RP" using i_RP_in unfolding ord_FO_\<Gamma>_def by auto
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_i_RP unfolding conv_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_i_RP unfolding conv_inf_def by fastforce
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
    by auto (* the other assumptions to prove are handled by auto *)
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

definition ground_subset :: "'a clause set \<Rightarrow> 'a clause set" where
  "ground_subset S' = {C \<in> S'. is_ground_cls C}"

(* lemma Bot_G_ground [simp]: "ground_subset Bot_G = Bot_G" unfolding ground_subset_def by fastforce

definition entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> \<forall>I. I \<Turnstile>s ground_subset S1 \<longrightarrow> I \<Turnstile>s ground_subset S2"*)

definition entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> \<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"
  
lemma ground_subst_on_ground_subset: "is_ground_subst \<sigma> \<Longrightarrow> (ground_subset N) \<cdot>cs \<sigma> = (ground_subset N)"
  by (simp add: ground_subset_def is_ground_cls_def is_ground_clss_def is_ground_lit_def) 

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
      I_entails_prems: "I \<Turnstile>s (set (inference.prems_of \<iota>))"
    obtain \<iota>_RP where i_equal: "\<iota> = conv_inf \<iota>_RP" and i_RP_in: "\<iota>_RP \<in> gr.ord_\<Gamma>" (*"\<iota>_RP \<in> (ord_FO_\<Gamma> S)" *)
      using i_in unfolding Inf_G_def by blast
    obtain CAs AAs As
      where the_inf: "ground_resolution_with_selection.ord_resolve S CAs (main_prem_of \<iota>_RP) AAs As (concl_of \<iota>_RP)"
      and mset_CAs: "side_prems_of \<iota>_RP = mset CAs" using i_RP_in unfolding gr.ord_\<Gamma>_def by force
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_equal unfolding conv_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_equal unfolding conv_inf_def by simp
    have I_entails_prems_RP: "I \<Turnstile>s set_mset (prems_of \<iota>_RP)" using prems I_entails_prems by argo
    then have I_entails_concl_RP: "I \<Turnstile> concl_of \<iota>_RP"
      using ground_resolution_with_selection.ord_resolve_sound[of S CAs "main_prem_of \<iota>_RP" AAs As "concl_of \<iota>_RP" I]
        the_inf mset_CAs gr.ground_resolution_with_selection_axioms by fastforce
    then have "I \<Turnstile> Saturation_Framework_Preliminaries.inference.concl_of \<iota>" using concl by auto
  }
  ultimately show "Saturation_Framework_Preliminaries.sound_inference_system Bot_G (|\<approx>G) Inf_G"
    unfolding Saturation_Framework_Preliminaries.sound_inference_system_def
      consequence_relation_def entails_sound_G_def
      Saturation_Framework_Preliminaries.sound_inference_system_axioms_def
    by auto
qed
(*
    have i_in': "\<iota> \<in> Inf_F" using i_in unfolding Inf_G_def by fast
    have ground_prems: "set (inference.prems_of \<iota>) = ground_subset (set (inference.prems_of \<iota>))"
      using i_in unfolding Inf_G_def
      by (smt Collect_cong Collect_mem_eq filter_empty_conv ground_subset_def mem_Collect_eq)
    then have ground_concl: "{Saturation_Framework_Preliminaries.inference.concl_of \<iota>} = ground_subset {Saturation_Framework_Preliminaries.inference.concl_of \<iota>}" sorry
    have non_ground_sound: "\<And>I \<eta>. (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (inference.prems_of \<iota>) \<cdot>cs \<sigma>) \<longrightarrow>
      is_ground_subst \<eta> \<longrightarrow> I \<Turnstile>s {Saturation_Framework_Preliminaries.inference.concl_of \<iota>} \<cdot>cs \<eta>"
      using soundness[OF i_in'] unfolding entails_sound_F_def sorry
    have "I \<Turnstile> Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using subst_atm_id_subst sorry 
    note sound = soundness[OF i_in'] 
*)

end

end

