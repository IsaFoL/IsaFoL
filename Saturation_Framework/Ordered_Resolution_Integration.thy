(*  Title:       Dynamic_Completeness_Lifting
Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

subsection \<open>Application of the saturation framework to Bachmair and Ganzinger's Resolution Prover, as formalize in the Ordered_Resolution_Prover theory in the AFP.\<close>

theory Ordered_Resolution_Integration
imports
  Saturation_Framework.Prover_Architectures
  Soundness_Related
  Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
begin

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

definition conv_inf :: "'a inference \<Rightarrow> 'a clause Consequence_Relations_and_Inference_Systems.inference" where
"conv_inf \<iota> = Consequence_Relations_and_Inference_Systems.inference.Infer (list_mset (prems_of \<iota>)) (concl_of \<iota>)"

definition same_inf ::
  "'a inference \<Rightarrow> 'a clause Consequence_Relations_and_Inference_Systems.inference \<Rightarrow> bool" where
  "same_inf \<iota>_RP \<iota> \<equiv>
    prems_of \<iota>_RP = mset (Consequence_Relations_and_Inference_Systems.prems_of \<iota>) \<and>
    concl_of \<iota>_RP = Consequence_Relations_and_Inference_Systems.concl_of \<iota>"

definition Inf_F :: "'a clause Consequence_Relations_and_Inference_Systems.inference set" where
  "Inf_F = {\<iota>. \<exists>\<iota>_RP \<in> (ord_FO_\<Gamma> S). same_inf \<iota>_RP \<iota>}"

lemma conv_inf_in_Inf_F: \<open>conv_inf ` (ord_FO_\<Gamma> S) \<subseteq> Inf_F\<close>
  unfolding conv_inf_def Inf_F_def same_inf_def by auto

interpretation sound_F: Soundness_Related.sound_inference_system Inf_F Bot_F entails_sound_F 
proof -
  { text \<open>proof of @{locale Consequence_Relations_and_Inference_Systems.consequence_relation}, \<open>subset_entailed\<close> assumption\<close>
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
  { text \<open>proof of @{locale Consequence_Relations_and_Inference_Systems.consequence_relation},
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
  { text \<open>proof of @{locale Soundness_Related.sound_inference_system}, soundness assumption\<close>
    fix \<iota> I \<eta>
    assume
      i_in: "\<iota> \<in> Inf_F" and
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (inference.prems_of \<iota>) \<cdot>cs \<sigma>" and
      ground_subst: "is_ground_subst \<eta>"
    obtain \<iota>_RP where i_RP_in: "\<iota>_RP \<in> (ord_FO_\<Gamma> S)" and i_i_RP: "same_inf \<iota>_RP \<iota>"
      using i_in unfolding Inf_F_def same_inf_def by force 
    obtain CAs AAs As \<sigma> where the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>_RP) AAs As \<sigma> (concl_of \<iota>_RP)"
      and mset_CAs: "mset CAs = side_prems_of \<iota>_RP" using i_RP_in unfolding ord_FO_\<Gamma>_def by auto
    have concl: "concl_of \<iota>_RP = Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>"
      using i_i_RP unfolding same_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_i_RP unfolding same_inf_def by fastforce
    have I_entails_prems_RP: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set_mset (prems_of \<iota>_RP) \<cdot>cs \<sigma>"
      using prems I_entails_prems by presburger
    have I_entails_concl_RP: "I \<Turnstile> (concl_of \<iota>_RP) \<cdot> \<eta>"
      using ground_subst I_entails_prems_RP ord_resolve_rename_sound[OF the_inf, of I \<eta>]
      by (metis mset_CAs set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
    then have "I \<Turnstile> (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>) \<cdot> \<eta>" 
      using concl by simp
  }
  ultimately show "Soundness_Related.sound_inference_system Inf_F Bot_F (|\<approx>F)"
    unfolding Soundness_Related.sound_inference_system_def
      consequence_relation_def entails_sound_F_def
      Soundness_Related.sound_inference_system_axioms_def
    apply (intro conjI)
    subgoal by simp
    subgoal by (metis singletonD subst_cls_empty subst_clss_single true_cls_empty true_clss_singleton)
    subgoal by auto
    subgoal by (simp add: substitution_ops.subst_clss_def true_clss_def)
    subgoal by auto
    subgoal by auto
    done
qed

abbreviation Bot_G :: "'a clause set" where "Bot_G \<equiv> {{#}}"

context
  fixes M :: "'a clause set"
  assumes sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>"
begin

interpretation sq: selection "S_M S M"
  using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gr: ground_resolution_with_selection "S_M S M"
  by unfold_locales

(* Not yet too sure about which version to select. Is this one even correct? *)
definition Inf_G :: "'a clause Consequence_Relations_and_Inference_Systems.inference set" where
  "Inf_G = {\<iota>. \<exists>\<iota>_RP \<in> (gr.ord_\<Gamma>). same_inf \<iota>_RP \<iota>}"

definition entails_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool"  where
  "entails_G S1 S2 \<equiv> \<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"

abbreviation entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> entails_G S1 S2"

interpretation Soundness_Related.sound_inference_system Inf_G Bot_G entails_sound_G
proof -
  {
    fix N1 N2 I
    assume
      incl: "N2 \<subseteq> N1" and
      entails: "I \<Turnstile>s N1"
    have "I \<Turnstile>s N2" using true_clss_mono[OF incl entails] . 
  }
  moreover
  {
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
    obtain \<iota>_RP where i_equal: "same_inf \<iota>_RP \<iota>" and i_RP_in: "\<iota>_RP \<in> gr.ord_\<Gamma>" (*"\<iota>_RP \<in> (ord_FO_\<Gamma> S)" *)
      using i_in unfolding Inf_G_def same_inf_def by auto
    obtain CAs AAs As
      where the_inf: "ground_resolution_with_selection.ord_resolve (S_M S M) CAs (main_prem_of \<iota>_RP) AAs As (concl_of \<iota>_RP)"
      and mset_CAs: "side_prems_of \<iota>_RP = mset CAs"
        using i_RP_in unfolding gr.ord_\<Gamma>_def by force
    have concl: "concl_of \<iota>_RP = Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>"
      using i_equal unfolding same_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_equal unfolding same_inf_def by simp
    have I_entails_prems_RP: "I \<Turnstile>s set_mset (prems_of \<iota>_RP)" using prems I_entails_prems by argo
    then have I_entails_concl_RP: "I \<Turnstile> concl_of \<iota>_RP"
      using ground_resolution_with_selection.ord_resolve_sound[of "S_M S M" CAs "main_prem_of \<iota>_RP" AAs As "concl_of \<iota>_RP" I]
        the_inf mset_CAs gr.ground_resolution_with_selection_axioms by fastforce
    then have "I \<Turnstile> Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>" using concl by auto
  }
  ultimately show "Soundness_Related.sound_inference_system Inf_G Bot_G (|\<approx>G)"
    unfolding Soundness_Related.sound_inference_system_def
      consequence_relation_def entails_G_def
      Soundness_Related.sound_inference_system_axioms_def
    by auto
qed

abbreviation entails_comp_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<Turnstile>G" 50) where
  "S1 \<Turnstile>G S2 \<equiv> entails_G S1 S2"

interpretation Consequence_Relations_and_Inference_Systems.consequence_relation Bot_G entails_comp_G
  by (rule consequence_relation_axioms)

interpretation Soundness_Related.sound_inference_system Inf_G Bot_G entails_comp_G
  by (rule sound_inference_system_axioms)

interpretation sr: standard_redundancy_criterion_reductive gr.ord_\<Gamma>
  by unfold_locales

interpretation sr: standard_redundancy_criterion_counterex_reducing gr.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP (S_M S M)"
  by unfold_locales

definition Red_Inf_G :: "'a clause set \<Rightarrow> 'a clause Consequence_Relations_and_Inference_Systems.inference set" where
  "Red_Inf_G S1 \<equiv> {\<iota>. \<exists>\<iota>_RP \<in> sr.Ri S1. same_inf \<iota>_RP \<iota>}"

definition Red_F_G :: "'a clause set \<Rightarrow> 'a clause set" where
  "Red_F_G S1 \<equiv> sr.Rf S1"

interpretation gr_calc: calculus_with_red_crit Bot_G Inf_G entails_comp_G Red_Inf_G Red_F_G
  unfolding calculus_with_red_crit_def
proof (intro conjI)
  show \<open>consequence_relation Bot_G (\<Turnstile>G)\<close> by (rule consequence_relation_axioms)
next
  show \<open>calculus_with_red_crit_axioms Bot_G Inf_G (\<Turnstile>G) Red_Inf_G Red_F_G\<close>
    unfolding calculus_with_red_crit_axioms_def
  proof (intro conjI allI impI)
    fix N
    show \<open>Red_Inf_G N \<subseteq> Inf_G\<close> unfolding Inf_G_def Red_Inf_G_def same_inf_def using sr.Ri_subset_\<Gamma> by force
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
    then show \<open>Red_Inf_G N \<subseteq> Red_Inf_G N'\<close>
      unfolding Red_Inf_G_def same_inf_def by (smt mem_Collect_eq sr.Ri_mono subset_iff)
  next
    fix N N' :: "'a clause set"
    assume \<open>N' \<subseteq> Red_F_G N\<close>
    then show \<open>Red_F_G N \<subseteq> Red_F_G (N - N')\<close> by (simp add: Red_F_G_def sr.Rf_indep)
  next
    fix N N' :: "'a clause set"
    assume \<open>N' \<subseteq> Red_F_G N\<close>
    then show \<open>Red_Inf_G N \<subseteq> Red_Inf_G (N - N')\<close>
      unfolding Red_Inf_G_def same_inf_def by (smt Red_F_G_def mem_Collect_eq sr.Ri_indep subset_eq)
  next
    fix \<iota> N
    assume
      i_in: \<open>\<iota> \<in> Inf_G\<close> and
      concl_in: \<open>Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota> \<in> N\<close>
    obtain \<iota>_RP where i_equal: "same_inf \<iota>_RP \<iota>" and i_RP_in: "\<iota>_RP \<in> gr.ord_\<Gamma>"
      using i_in unfolding Inf_G_def same_inf_def by auto
    then have \<open>concl_of \<iota>_RP \<in> N\<close> using concl_in by (simp add: same_inf_def)
    then have \<open>\<iota>_RP \<in> sr.Ri N\<close> using i_RP_in by (simp add: sr.Ri_effective)
    then show \<open>\<iota> \<in> Red_Inf_G N\<close> using i_equal unfolding Red_Inf_G_def Inf_G_def same_inf_def by blast
  qed
qed

lemma inf_from_subs: "gr.inferences_from (N - sr.Rf N) \<subseteq> gr.inferences_from N"
  by (simp add: Diff_subset gr.inferences_from_mono)

lemma same_inf_inf_from_subs:
  \<open>{\<iota>. \<exists> \<iota>_RP \<in> gr.inferences_from (N - sr Rf N). same_inf \<iota>_RP \<iota>} \<subseteq> Inf_from N\<close> (is "?sI \<subseteq> _")
proof
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> ?sI\<close>
  obtain \<iota>_RP where i_RP_from: \<open>\<iota>_RP \<in> gr.inferences_from N\<close> and i_to_i_RP: \<open>same_inf \<iota>_RP \<iota>\<close>
    using inf_from_subs i_in by (smt Diff_subset gr.inferences_from_mono mem_Collect_eq subsetCE)
  have \<open>set_mset (prems_of \<iota>_RP) \<subseteq> N\<close> using i_RP_from unfolding gr.inferences_from_def infer_from_def by fast
  then have i_from: \<open>set (Consequence_Relations_and_Inference_Systems.prems_of \<iota>) \<subseteq> N\<close>
    using i_to_i_RP unfolding same_inf_def by fastforce
  have \<open>\<iota> \<in> Inf_G\<close>
    using i_RP_from i_to_i_RP unfolding gr.inferences_from_def Inf_G_def same_inf_def by force
  then show \<open>\<iota> \<in> Inf_from N\<close> using i_from unfolding Inf_from_def by fast
qed

(*lemma conv_inf_inf_from_commute: \<open>conv_inf ` gr.inferences_from (N - sr.Rf N) \<subseteq> Inf_from N\<close> 
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
  then have i_from: \<open>set (Consequence_Relations_and_Inference_Systems.prems_of \<iota>) \<subseteq> N\<close> using i_to_i_RP unfolding conv_inf_def by auto
  have \<open>\<iota> \<in> Inf_G\<close> using i_RP_from i_to_i_RP unfolding gr.inferences_from_def Inf_G_def by blast
  then show \<open>\<iota> \<in> Inf_from N\<close> using i_from unfolding Inf_from_def by fast
qed
*)

lemma \<open>gr.eligible As D \<Longrightarrow> mset As = mset As' \<Longrightarrow> gr.eligible As' D\<close>
  unfolding gr.eligible.simps
  by (cases As; cases As')
    (auto simp: add_mset_eq_add_mset eq_commute[of "add_mset _ _" "mset _"] image_mset_remove1_mset_if)

(* taken from AFP: Automatic_Refinement/Lib/Misc.thy *)
lemma in_set_drop_conv_nth: "x\<in>set (drop n l) \<longleftrightarrow> (\<exists>i. n\<le>i \<and> i<length l \<and> x = l!i)"
  apply (clarsimp simp: in_set_conv_nth)
  apply safe
  apply simp
  apply (metis le_add2 less_diff_conv add.commute)
  apply (rule_tac x="i-n" in exI)
  apply auto []
  done

(* taken from Mathias Fleury's isafol/Weidenbach_Book/WB_List_More.thy *)
lemma take_map_nth_alt_def: \<open>take n xs = map ((!) xs) [0..<min n (length xs)]\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs) note IH = this
  show ?case
  proof (cases \<open>n < length (xs @ [x])\<close>)
    case True
    then show ?thesis
      using IH by (auto simp: min_def nth_append)
  next
    case False
    have [simp]:
      \<open>map (\<lambda>a. if a < length xs then xs ! a else [x] ! (a - length xs)) [0..<length xs] =
       map (\<lambda>a. xs ! a) [0..<length xs]\<close> for xs and x :: 'b
      by (rule map_cong) auto
    show ?thesis
      using IH False by (auto simp: nth_append min_def)
  qed
qed

(* taken from Mathias Fleury's isafol/Weidenbach_Book/WB_List_More.thy *)
lemma inj_on_image_mset_eq_iff:
  assumes inj: \<open>inj_on f (set_mset (K + K'))\<close>
  shows \<open>image_mset f K' = image_mset f K \<longleftrightarrow> K' = K\<close> (is \<open>?A = ?B\<close>)
proof
  assume ?B
  then show ?A by auto
next
  assume ?A
  then show ?B
    using inj
  proof(induction K arbitrary: K')
    case empty
    then show ?case by auto
  next
    case (add x K) note IH = this(1) and H = this(2) and inj = this(3)

    obtain K1 x' where
      K': \<open>K' = add_mset x' K1\<close> and
      f_xx': \<open>f x' = f x\<close> and
      K1_K: \<open>image_mset f K1 = image_mset f K\<close>
      using H by (auto dest!: msed_map_invR)
    moreover have \<open>K1 = K\<close>
      apply (rule IH[OF K1_K])
      using inj by (auto simp: K')
    moreover have \<open>x = x'\<close>
      using inj f_xx' by (auto simp: K')
    ultimately show ?case by fast
  qed
qed


lemma dist: \<open>distinct_mset (mset_set {0..<n})\<close> for n :: nat
  apply (subst atLeastLessThan_upt, subst mset_set_set)
  apply auto[]
  apply (subst distinct_mset_mset_distinct)
  apply auto
done

(* Move to Multiset_More.thy *)
lemma in_distinct_mset_diff_iff:
  \<open>distinct_mset K \<Longrightarrow>  x \<in># K - N \<longleftrightarrow> x \<notin># N \<and> x \<in># K\<close>
  using distinct_mem_diff_mset[of K x N]
  by (auto dest: in_diffD multi_member_split)

lemma shuffle_ord_resolve_side_prems:
  assumes
    res: \<open>gr.ord_resolve CAs D AAs As E\<close> and
    mset_CAs: \<open>mset CAs = mset CAs'\<close>
  shows
    \<open>(\<exists>AAs' As'. mset AAs = mset AAs' \<and> mset As = mset As' \<and>
     gr.ord_resolve CAs' D AAs' As' E)\<close>
  using assms
proof -
  obtain Cs Da n where
    D_eq: \<open>D = Da + negs (mset As)\<close> and
    E_eq: \<open>E = \<Union>#(mset Cs) + Da\<close> and
    len_CAs: \<open>length CAs = n\<close> and
    len_Cs: \<open>length Cs = n\<close> and
    len_AAs: \<open>length AAs = n\<close> and
    len_As: \<open>length As = n\<close> and
    not_null: \<open>n \<noteq> 0\<close> and
    CAs_eq: \<open>\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)\<close> and
    AAs_nempty: \<open>\<forall>i<n. AAs ! i \<noteq> {#}\<close> and
    in_AAs: \<open>\<forall>i<n. \<forall>A\<in>#AAs ! i. A = As ! i\<close> and
    eligible: \<open>gr.eligible As (Da + negs (mset As))\<close> and
    max: \<open>\<forall>i<n. gr.strictly_maximal_wrt (As ! i) (Cs ! i)\<close> and
    S_empty: \<open>\<forall>i<n. (S_M S M) (CAs ! i) = {#}\<close>
    using res unfolding gr.ord_resolve.simps by auto
  have x_in_equiv: \<open>x \<in># mset CAs' \<Longrightarrow> x \<in># mset CAs\<close> for x using mset_CAs by simp
  have len_CAs': \<open>length CAs' = n\<close> using len_CAs mset_CAs using mset_eq_length by fastforce
  have exist_map: \<open>\<exists>map_i. (\<forall>i. i < n \<longrightarrow> CAs'!i = CAs!(map_i i)) \<and> inj_on map_i {0..<n} \<and>
          map_i ` {0..<n} \<subseteq> {0..<length CAs'}\<close> if \<open>n \<le> length CAs'\<close>
    using that
  proof (induct n)
    case 0
    then show ?case by auto
  next
    case (Suc m) note _ = this(1) and small_enough = this(2)
    then obtain map_i where [simp]:\<open>(\<And>i. i < m \<Longrightarrow> CAs'!i = CAs!(map_i i))\<close> and
        inj: \<open>inj_on map_i {0..<m}\<close> and
        im_incl: \<open>map_i ` {0..<m} \<subseteq> {0..<n}\<close> 
       by (force simp: len_CAs')
    define j where \<open>j \<equiv> SOME i. i < length CAs' \<and> CAs'!m = CAs!i \<and> i \<notin> map_i ` {0..<m}\<close>
    have cut_n_m: \<open>mset_set {0..<n} = mset_set (map_i ` {0..<m}) + (mset_set {0..<n} - mset_set (map_i ` {0..<m}))\<close>
      by (subst subset_mset.add_diff_inverse)
       (use im_incl in \<open>auto simp: image_iff\<close>)
    have \<open>CAs'!m \<in># mset CAs' - mset (take m CAs')\<close>
      apply (subst(2) append_take_drop_id[symmetric,of _ m])
      apply (subst mset_append)
      by (use small_enough in \<open>auto simp: in_set_drop_conv_nth\<close>)
    also have \<open>mset CAs' - mset (take m CAs') = mset CAs - mset (map (\<lambda>i. CAs!(map_i i)) [0..<m])\<close>
      apply (subst map_cong[OF refl, of _ _ "\<lambda>i. CAs'!i"])
      using small_enough by (auto simp: min_def mset_CAs take_map_nth_alt_def)
    finally have \<open>\<exists>i. i < length CAs' \<and> CAs'!m = CAs!i \<and> i \<notin> map_i ` {0..<m}\<close>
      apply (subst (asm)(2) map_nth[symmetric])
      unfolding mset_map mset_upt len_CAs apply (subst (asm) cut_n_m)
      by (auto simp: image_mset_mset_set[symmetric] inj in_distinct_mset_diff_iff dist len_CAs'
        dest!: distinct_mem_diff_mset) 
    then have \<open>CAs'!m = CAs!j\<close> and j_notin: \<open>j \<notin> map_i ` {0..<m}\<close> and \<open>j < length CAs'\<close>
      using someI[of \<open>\<lambda>i. i < length CAs' \<and> CAs'!m = CAs!i \<and> i \<notin> map_i ` {0..<m}\<close>]
      unfolding j_def[symmetric]
      by blast+
    moreover have \<open>inj_on (map_i(m := j)) {0..<Suc m}\<close>
      unfolding inj_on_def
      apply (intro ballI)
      subgoal for x y
        using inj_onD[OF inj, of x y] j_notin by auto
      done
    ultimately show ?case
      apply -
      apply (rule exI[of _ \<open>map_i (m:=j)\<close>])
      using inj im_incl by (auto simp flip: fun_upd_def simp: len_CAs' less_Suc_eq image_subset_iff)
  qed
  then obtain map_i where map_i_def: \<open>i < n \<Longrightarrow> CAs'!i = CAs!(map_i i)\<close> and len_map_i: \<open>i < n \<Longrightarrow> (map_i i) < n\<close> and
     inj: \<open>inj_on map_i {0..<n}\<close> for i
    unfolding len_CAs' by fastforce
  have [simp]: \<open>map_i ` {0..<n} = {0..<n}\<close>
    apply (rule endo_inj_surj) using len_map_i inj by auto
  have eq: \<open>mset_set {0..<length AAs} = image_mset map_i (mset_set {0..<length AAs})\<close>
    apply (rule distinct_set_mset_eq)
    by (use inj len_map_i in \<open>auto simp: len_AAs len_CAs len_CAs' dist distinct_image_mset_inj\<close>)
  obtain AAs' where len_AAs': \<open>length AAs' = n\<close> and AAs'_def: \<open>i < n \<Longrightarrow> AAs'!i = AAs!(map_i i)\<close> for i
    apply (rule that[of \<open>map (\<lambda>i. AAs!(map_i i)) [0..<n]\<close>])
    by (auto simp: len_AAs)
  then have [simp]: \<open>mset AAs' = mset AAs\<close> using map_i_def mset_CAs len_CAs
    apply (subst map_nth[symmetric], subst (5) map_nth[symmetric])
    unfolding mset_map mset_upt
    apply (subst eq)
    apply (auto intro!: image_mset_cong simp: len_AAs len_AAs' len_CAs len_CAs')
    done
  obtain As' where len_As': \<open>length As' = n\<close> and As'_def: \<open>i < n \<Longrightarrow> As'!i = As!(map_i i)\<close> for i  
    apply (rule that[of \<open>map (\<lambda>i. As!(map_i i)) [0..<n]\<close>])
    by (auto simp: len_As)
  then have [simp]: \<open>mset As' = mset As\<close> using map_i_def mset_CAs len_CAs
    apply (subst map_nth[symmetric], subst (5) map_nth[symmetric])
    unfolding mset_map mset_upt len_AAs len_As
    apply (subst eq[unfolded len_AAs])
    apply (auto intro!: image_mset_cong simp: len_AAs len_AAs' len_CAs len_CAs')
    done
  obtain Cs' where len_Cs': \<open>length Cs' = n\<close> and Cs'_def: \<open>i < n \<Longrightarrow> Cs'!i = Cs!(map_i i)\<close> for i  
    apply (rule that[of \<open>map (\<lambda>i. Cs!(map_i i)) [0..<n]\<close>])
    by (auto simp: len_Cs)
  then have [simp]: \<open>mset Cs' = mset Cs\<close> using map_i_def mset_CAs len_CAs
    apply (subst map_nth[symmetric], subst (5) map_nth[symmetric])
    unfolding mset_map mset_upt len_AAs len_Cs
    apply (subst eq[unfolded len_AAs])
    apply (auto intro!: image_mset_cong simp: len_AAs len_Cs' len_CAs len_Cs)
    done
  have eligible': \<open>gr.eligible As' (Da + negs (mset As))\<close>
    using len_map_i As'_def eligible unfolding gr.eligible.simps by (auto simp: len_As len_As')
  have \<open>gr.ord_resolve CAs' D AAs' As' E\<close>
    apply (unfold gr.ord_resolve.simps, rule exI[of _ CAs'], rule exI[of _ n], rule exI[of _ Cs'],
      rule exI[of _ AAs'], rule exI[of _ As'], rule exI[of _ Da])
    using CAs_eq AAs_nempty in_AAs eligible' max S_empty As'_def AAs'_def map_i_def len_map_i Cs'_def
    by (auto simp: len_CAs' len_AAs' len_As' len_Cs not_null D_eq E_eq len_Cs')
  then show ?thesis 
    apply -
    apply (rule exI[of _ AAs'], rule exI[of _ As'])
    by (auto)
qed

lemma negs_eq: \<open>negs A = negs B \<Longrightarrow> A = B\<close> by (metis literal.inject(2) multiset.inj_map_strong)

lemma shift_indices: \<open>(\<forall>i\<in>{Suc 0..<Suc (length list)}. list ! (i - Suc 0) = lista ! (i - Suc 0)) \<Longrightarrow> \<forall>i\<in>{0..<length list}. list!i  = lista!i\<close> by force

lemma pos_not_in_negs: \<open>Pos x \<in># X \<Longrightarrow> X = Y + negs Z \<Longrightarrow> Pos x \<in># Y\<close> by fastforce
lemma neg_not_in_poss: \<open>Neg x \<in># X \<Longrightarrow> X = Y + poss Z \<Longrightarrow> Neg x \<in># Y\<close> by fastforce

lemma main_prem_eq_or_tauto:
  assumes
    i_in: \<open>\<iota> \<in> gr.ord_\<Gamma>\<close> and
    i'_in: \<open>\<iota>' \<in> gr.ord_\<Gamma>\<close> and
    prems_eq: \<open>prems_of \<iota> = prems_of \<iota>'\<close> and
    concl_eq: \<open>concl_of \<iota> = concl_of \<iota>'\<close>
  shows
    \<open>main_prem_of \<iota> = main_prem_of \<iota>' \<or> (\<exists>A. Pos A \<in># concl_of \<iota> \<and> Neg A \<in># concl_of \<iota>)\<close> (is \<open>?A \<or> ?B\<close>)
proof (intro disj_imp[THEN iffD2] impI)
  assume
    contra: \<open>\<not> ?A\<close>
  then have \<open>\<iota> \<noteq> \<iota>'\<close> by blast
  obtain CAs1 AAs1 As1 where i_inf: \<open>gr.ord_resolve CAs1 (main_prem_of \<iota>) AAs1 As1 (concl_of \<iota>)\<close> and
    CAs1_i: \<open>mset CAs1 = side_prems_of \<iota>\<close> using i_in unfolding gr.ord_\<Gamma>_def by force
  obtain CAs2 AAs2 As2 where i'_inf: \<open>gr.ord_resolve CAs2 (main_prem_of \<iota>') AAs2 As2 (concl_of \<iota>')\<close> and
    CAs2_i': \<open>mset CAs2 = side_prems_of \<iota>'\<close> using i'_in unfolding gr.ord_\<Gamma>_def by force
  obtain CAm where CAm_i: \<open>CAm + {#main_prem_of \<iota>#} = mset CAs2\<close> and CAm_i': \<open>CAm + {#main_prem_of \<iota>'#} = mset CAs1\<close>
    using CAs1_i CAs2_i' prems_eq unfolding prems_of_def side_prems_of_def
    by (smt add.commute add_right_imp_eq contra insert_DiffM2 multi_member_this remove1_mset_add_mset_If
      union_mset_add_mset_right)
  obtain CAs where CAs_is: \<open>mset CAs = CAm\<close> by (metis list_of_mset_exi)
  obtain AAs3 As3 where A3_is: \<open>gr.ord_resolve (main_prem_of \<iota>' # CAs) (main_prem_of \<iota>) AAs3 As3 (concl_of \<iota>)\<close>
    using shuffle_ord_resolve_side_prems i_inf CAm_i' CAs_is by (metis add_mset_add_single mset.simps(2))
  obtain AAs4 As4 where A4_is: \<open>gr.ord_resolve (main_prem_of \<iota> # CAs) (main_prem_of \<iota>') AAs4 As4 (concl_of \<iota>')\<close>  
    using shuffle_ord_resolve_side_prems i'_inf CAm_i CAs_is by (metis add_mset_add_single mset.simps(2))
  have len_AAs_eq: \<open>length AAs3 = length AAs4\<close>
    using A3_is A4_is CAs_is CAm_i CAm_i' CAs1_i CAs2_i' unfolding gr.ord_resolve.simps by force
  then have len_As_eq: \<open>length As3 = length As4\<close>
    using A3_is A4_is unfolding gr.ord_resolve.simps by force
  define n where n_is: \<open>n = length AAs3\<close>
  then have len_AAs4: \<open>n = length AAs4\<close> using len_AAs_eq by simp
  then have len_As4: \<open>n = length As4\<close> using A4_is unfolding gr.ord_resolve.simps by force
  then have len_As3: \<open>n = length As3\<close> using len_As_eq by simp
  then have n_not_null: \<open>n \<noteq> 0\<close> using A3_is unfolding gr.ord_resolve.simps by force
  obtain D3 Cs3 where
    main3: \<open>main_prem_of \<iota> = D3 + negs (mset As3)\<close> and
    concl_i_is: \<open>concl_of \<iota> = \<Union># (mset Cs3) + D3\<close> and
    len_Cs3: \<open>length Cs3 = n\<close> and
    CAs_i3: \<open>\<forall>i<n. (main_prem_of \<iota>' # CAs) ! i = Cs3 ! i + poss (AAs3 ! i)\<close> and
    AAs3_nempty: \<open>\<forall>i<n. AAs3 ! i \<noteq> {#}\<close> and
    AAs3_i: \<open>\<forall>i<n. \<forall>A\<in>#AAs3 ! i. A = As3 ! i\<close> and
    eligible3: \<open>gr.eligible As3 (D3 + negs (mset As3))\<close> and
    max3: \<open>\<forall>i<n. gr.strictly_maximal_wrt (As3 ! i) (Cs3 ! i)\<close> and
    sel_empty3: \<open>\<forall>i<n. (S_M S M) (Cs3 ! i + poss (AAs3 ! i)) = {#}\<close>
    using A3_is n_is unfolding gr.ord_resolve.simps by auto
  obtain D4 Cs4 where
    main4: \<open>main_prem_of \<iota>' = D4 + negs (mset As4)\<close> and
    concl_i'_is: \<open>concl_of \<iota>' = \<Union># (mset Cs4) + D4\<close> and
    len_Cs4: \<open>length Cs4 = n\<close> and
    CAs_i4: \<open>\<forall>i<n. (main_prem_of \<iota> # CAs) ! i = Cs4 ! i + poss (AAs4 ! i)\<close> and
    AAs4_nempty: \<open>\<forall>i<n. AAs4 ! i \<noteq> {#}\<close> and
    AAs4_i: \<open>\<forall>i<n. \<forall>A\<in>#AAs4 ! i. A = As4 ! i\<close> and
    eligible4: \<open>gr.eligible As4 (D4 + negs (mset As4))\<close> and
    max4: \<open>\<forall>i<n. gr.strictly_maximal_wrt (As4 ! i) (Cs4 ! i)\<close> and
    sel_empty4: \<open>\<forall>i<n. (S_M S M) (Cs4 ! i + poss (AAs4 ! i)) = {#}\<close>
    using A4_is len_AAs4 unfolding gr.ord_resolve.simps by auto
  have As_eq: \<open>\<forall>i \<in> {1..<n}. As3!i = As4!i\<close>
    using main3 eligible3 sel_empty4 CAs_i3 CAs_i4 AAs3_i AAs4_i max3 max4 unfolding gr.strictly_maximal_wrt_def
    by (metis atLeastLessThan_iff empty_iff gr.eligible.cases image_mset_is_empty_iff len_As3 len_As_eq
      length_greater_0_conv linorder_not_le nth_Cons_0 nth_mem_mset set_mset_empty)
  then have AAs_eq: \<open>\<forall>i \<in> {1..<n}. AAs3!i = AAs4!i\<close>
    using main3 eligible3 sel_empty4 CAs_i3 CAs_i4 AAs3_i AAs4_i max3 max4 unfolding gr.strictly_maximal_wrt_def
    by (metis atLeastLessThan_iff empty_iff gr.eligible.cases image_mset_is_empty_iff in_mset_conv_nth len_AAs4
      len_AAs_eq len_As3 len_As_eq length_greater_0_conv linorder_not_le nth_Cons_0 set_mset_empty)
  then have Cs_eq: \<open>\<forall>i \<in> {1..<n}. Cs3!i = Cs4!i\<close>
    using CAs_i3 CAs_i4 by fastforce
  then have \<open>\<Union># (mset Cs3) - Cs3!0 = \<Union># (mset Cs4) - Cs4!0\<close> using Cs_eq len_Cs3 len_Cs4
    apply (cases Cs3; cases Cs4)
    by (force intro!: arg_cong[of _ _ sum_list] list_eq_iff_nth_eq[THEN iffD2])+
  then have CsD_eq: \<open>Cs3!0 + D3 = Cs4!0 + D4\<close> using concl_i_is concl_i'_is concl_eq len_Cs3 len_Cs4
    apply (cases Cs3; cases Cs4)
    by force+
  have \<open>tl As3 = tl As4\<close> using len_As3 len_As4 As_eq by (auto simp: nth_tl intro!:list_eq_iff_nth_eq[THEN iffD2])
  then have \<open>negs (mset As3) - negs {# As3!0 #} = negs (mset As4) - negs {# As4!0 #}\<close>
    apply (cases As3; cases As4)
    using len_As3 len_As4 n_not_null As_eq negs_eq by auto
  then have \<open>negs {#As3!0#} + D3 \<noteq> negs {# As4!0 #} + D4\<close>
    using contra len_As3 len_As4 unfolding main3 main4 
    apply (cases As3; cases As4)
    by auto
  have main_i: \<open>D3 + negs (mset As3) = Cs4!0 + poss (AAs4!0)\<close> using main3 CAs_i4 n_not_null by force
  have main_i': \<open>D4 + negs (mset As4) = Cs3!0 + poss (AAs3!0)\<close> using main4 CAs_i3 n_not_null by force
  have pos4_in_poss: \<open>Pos (As4!0) \<in># poss (AAs4!0)\<close>
    apply (cases AAs4)
    using n_not_null len_AAs4 apply blast
    using AAs4_i AAs4_nempty len_AAs4 by fastforce
  have neg4_in_negs: \<open>Neg (As4!0) \<in># negs (mset As4)\<close> using len_As4 n_not_null by auto
  have eq_imply_B: \<open>D3 = D4 \<Longrightarrow> ?B\<close>
  proof -
    assume \<open>D3 = D4\<close>
    then have Cs_hd_eq: \<open>Cs3!0 = Cs4!0\<close> using CsD_eq by simp
    have \<open>Pos (As4!0) \<in># D3\<close> using pos4_in_poss main_i pos_not_in_negs by (metis union_iff)
    then have pos4: \<open>Pos (As4!0) \<in># concl_of \<iota>\<close> using concl_i_is by simp
    have \<open>Neg (As4!0) \<in># Cs3!0\<close> using neg4_in_negs neg_not_in_poss main_i' Cs_hd_eq by (metis union_iff)
    then have neg4: \<open>Neg (As4!0) \<in># concl_of \<iota>\<close>
      unfolding concl_i_is apply (cases Cs3)
      using n_not_null len_Cs3 by auto
    show \<open>?B\<close> using pos4 neg4 concl_i_is
      apply (rule_tac x="As4!0" in exI) by auto
  qed
  have neq_imply_B: \<open>\<not> D3 = D4 \<Longrightarrow> ?B\<close>
  proof -
    assume \<open>\<not> D3 = D4\<close>
    define D where D_is: \<open>D = D3 \<inter># D4\<close>
    define D3' where D3'_is: \<open>D3' = D3 - D4\<close>
    define D4' where D4'_is: \<open>D4' = D4 - D3\<close>
    have inter_D: \<open>D3' \<inter># D4' = {#}\<close>
      using diff_intersect_sym_diff[of D3 D4] D3'_is D4'_is by force
    have D3_div: \<open>D + D3' = D3\<close>
      by (auto simp: D_is D3'_is multiset_inter_def)
    have D4_div: \<open>D + D4' = D4\<close>
      apply (auto simp: D_is D4'_is multiset_inter_def)
      by (metis D3'_is D_is D3_div add_diff_cancel_left' subset_mset.add_diff_assoc2 subset_mset.inf_le1
        sup_subset_mset_def union_diff_inter_eq_sup)
    have CsD_eq2: \<open>Cs3!0 + D3' = Cs4!0 + D4'\<close>
      using CsD_eq by (auto simp: D3_div[THEN sym] D4_div[THEN sym])
    then have D3'_subs: \<open>D3' \<subseteq># Cs4!0\<close>
      using inter_D
      by (metis CsD_eq D3'_is mset_subset_eq_add_right subset_eq_diff_conv)
    have D4'_subs: \<open>D4' \<subseteq># Cs3!0\<close>
      using inter_D
      by (metis CsD_eq D4'_is mset_subset_eq_add_right subset_eq_diff_conv)
    define C3 where C3_is: \<open>C3 = Cs3!0 - D4'\<close>
    define C4 where C4_is: \<open>C4 = Cs4!0 - D3'\<close>
    have C_eq: \<open>C3 = C4\<close>
      apply (simp add: C3_is C4_is)
      using CsD_eq2 by (metis add_diff_cancel_right' cancel_ab_semigroup_add_class.diff_right_commute)
    have Cs30_div: \<open>Cs3!0 = C3 + D4'\<close> using C3_is D4'_subs by simp 
    have Cs40_div: \<open>Cs4!0 = C3 + D3'\<close> using C4_is D3'_subs by (simp add: C_eq)
    have \<open>D3 + negs (mset As3) +  D4 + negs (mset As4) = Cs4 ! 0 + poss (AAs4 ! 0) + Cs3 ! 0 + poss (AAs3 ! 0)\<close>
      using main_i main_i' by simp
    then have sum_concl_eq: \<open>D + D + negs (mset As3) + negs (mset As4) = C3 + C3 + poss (AAs3!0) + poss (AAs4!0)\<close>
      unfolding D3_div[THEN sym] D4_div[THEN sym] Cs30_div Cs40_div
      by (smt C_eq ab_semigroup_add_class.add_ac(1) add.commute add.left_commute add_right_imp_eq
        multi_union_self_other_eq union_assoc union_commute union_lcomm)
    then have \<open>Pos (As4!0) \<in># D\<close> using pos4_in_poss pos_not_in_negs by (metis union_iff)
    then have pos4': \<open>Pos (As4!0) \<in># concl_of \<iota>\<close> using concl_i_is by (simp add: D3_div[THEN sym])
    have \<open>Neg (As4!0) \<in># C3\<close> using sum_concl_eq neg4_in_negs neg_not_in_poss by (metis union_iff)
    then have \<open>Neg (As4!0) \<in># Cs3!0\<close> using C3_is by (simp add: C_eq Cs30_div)
    then have neg4': \<open>Neg (As4!0) \<in># concl_of \<iota>\<close>
      unfolding concl_i_is apply (cases Cs3)
      using n_not_null len_Cs3 by auto
    show \<open>?B\<close> using pos4' neg4' concl_i_is
      apply (rule_tac x="As4!0" in exI)
      by auto
  qed
  show ?B
    apply (rule_tac P="D3 = D4" in case_split)
    using eq_imply_B neq_imply_B by auto
qed

(* TODO: Starting with Isabelle2021, this will corresponds to
   "Standard_Redundancy.tautology_redundant_infer". Use that instead. *)
lemma tauto_concl_redundant:
  assumes
    pos: \<open>Pos A \<in># concl_of \<iota>\<close> and
    neg: \<open>Neg A \<in># concl_of \<iota>\<close>
  shows \<open>sr.redundant_infer N \<iota>\<close>
proof -
  have \<open>set_mset {#} \<subseteq> N\<close> by simp
  moreover have \<open>I \<Turnstile>m {#} + side_prems_of \<iota> \<longrightarrow> I \<Turnstile> inference.concl_of \<iota>\<close> using pos neg by blast
  moreover have \<open>D \<in># {#} \<longrightarrow> D < main_prem_of \<iota>\<close> by force
  ultimately show \<open>sr.redundant_infer N \<iota>\<close>
    by (metis empty_iff neg neg_literal_notin_imp_true_cls pos pos_literal_in_imp_true_cls set_mset_empty)
qed

lemma conv_saturation:
  assumes \<open>gr_calc.saturated N\<close>
  shows \<open>sr.saturated_upto N\<close>
    using assms unfolding sr.saturated_upto_def gr_calc.saturated_def apply -
  proof (rule ccontr)
    assume
      sat: \<open>Inf_from N \<subseteq> Red_Inf_G N\<close> and
      contra: \<open>\<not> gr.inferences_from (N - sr.Rf N) \<subseteq> sr.Ri N\<close>
    then obtain \<iota>_RP where i_not_in: \<open>\<iota>_RP \<notin> sr.Ri N\<close> and i_in: \<open>\<iota>_RP \<in> gr.inferences_from (N - sr.Rf N)\<close> by blast
    obtain \<iota> where i_is: \<open>same_inf \<iota>_RP \<iota>\<close>
      unfolding same_inf_def by (metis Consequence_Relations_and_Inference_Systems.inference.sel(1)
        Consequence_Relations_and_Inference_Systems.inference.sel(2) list_of_mset_exi)
    have \<open>\<iota> \<in> Inf_from N\<close> using i_in i_is same_inf_inf_from_subs by fast
    then have \<open>\<iota> \<in>  Red_Inf_G N\<close> using sat by fast
    moreover have \<open>\<iota> \<notin> Red_Inf_G N\<close>
    proof -
      {
        fix \<iota>_RP2
        assume
          same_i_RP: \<open>same_inf \<iota>_RP2 \<iota>\<close> and
          i_RP2_in: \<open>\<iota>_RP2 \<in> sr.Ri N\<close>
        have concl_eq: \<open>concl_of \<iota>_RP = concl_of \<iota>_RP2\<close>
          using same_i_RP i_is unfolding same_inf_def by simp
        have prems_eq: \<open>prems_of \<iota>_RP = prems_of \<iota>_RP2\<close>
          using i_is same_i_RP unfolding same_inf_def by simp
        consider
          (main_prem_eq) \<open>main_prem_of \<iota>_RP = main_prem_of \<iota>_RP2\<close> |
          (tauto) \<open>(\<exists>A. Pos A \<in># concl_of \<iota>_RP \<and> Neg A \<in># concl_of \<iota>_RP)\<close> 
        using main_prem_eq_or_tauto[OF _ _ prems_eq concl_eq] i_RP2_in i_in
        unfolding sr.Ri_def gr.inferences_from_def by blast
      then have \<open>\<iota>_RP \<in> sr.Ri N\<close>
      proof cases
        case main_prem_eq
        then show ?thesis
          using same_i_RP concl_eq i_RP2_in Inference_System.inference.expand prems_eq by auto
      next
        case tauto
        then show ?thesis
          using tauto_concl_redundant i_in unfolding sr.Ri_def gr.inferences_from_def by auto
      qed
      then have \<open>False\<close> using i_not_in by simp
    }
    then show \<open>\<iota> \<notin> Red_Inf_G N\<close>
      using i_not_in unfolding same_inf_def Red_Inf_G_def by fastforce  
  qed
  ultimately show \<open>False\<close> by simp
qed

interpretation calc_G: static_refutational_complete_calculus Bot_G Inf_G entails_comp_G Red_Inf_G
  Red_F_G
  proof
  fix B N
  assume
    B_in: \<open>B \<in> Bot_G\<close> and
    N_sat: \<open>gr_calc.saturated N\<close> and
    N_unsat: \<open>N \<Turnstile>G {B}\<close>
  have B_is: \<open>B = {#}\<close> using B_in by simp
  moreover have \<open>sr.saturated_upto N\<close> using N_sat by (simp add: conv_saturation)
  ultimately have \<open>{#} \<in> N\<close>
    using sr.saturated_upto_complete_if[of N] N_unsat by (simp add: entails_G_def)
  then show \<open>\<exists>B'\<in>Bot_G. B' \<in> N\<close> by simp
qed

definition \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F C = grounding_of_cls C\<close>

definition subst_inf :: \<open>'a clause Consequence_Relations_and_Inference_Systems.inference \<Rightarrow> 's
                          \<Rightarrow> 'a clause Consequence_Relations_and_Inference_Systems.inference\<close> (infixl "\<cdot>inf" 67) where
  \<open>\<iota> \<cdot>inf \<sigma> = Consequence_Relations_and_Inference_Systems.Infer
    (map (\<lambda> A. A \<cdot> \<sigma>) (Consequence_Relations_and_Inference_Systems.prems_of \<iota>))
    ((Consequence_Relations_and_Inference_Systems.concl_of \<iota>) \<cdot> \<sigma>)\<close>

definition \<G>_Inf :: \<open>'a clause Consequence_Relations_and_Inference_Systems.inference
                      \<Rightarrow> 'a clause Consequence_Relations_and_Inference_Systems.inference set option\<close> where
  \<open>\<G>_Inf \<iota> = Some {Consequence_Relations_and_Inference_Systems.inference.Infer
    ((inference.prems_of \<iota>) \<cdot>\<cdot>cl \<rho>s) ((Consequence_Relations_and_Inference_Systems.concl_of \<iota>) \<cdot> \<rho>)
    |\<rho> \<rho>s. is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho> \<and>
    Consequence_Relations_and_Inference_Systems.inference.Infer ((inference.prems_of \<iota>) \<cdot>\<cdot>cl \<rho>s)
    ((Consequence_Relations_and_Inference_Systems.concl_of \<iota>) \<cdot> \<rho>)  \<in> Inf_G }\<close>

interpretation \<G>_standard_lifting: standard_lifting Bot_F Inf_F Bot_G Inf_G entails_comp_G Red_Inf_G
  Red_F_G \<G>_F \<G>_Inf
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
  show \<open>the (\<G>_Inf \<iota>) \<subseteq> Red_Inf_G (\<G>_F (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>))\<close>
  proof
    fix \<iota>'
    assume i'_in: \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
    then have i'_in2: \<open>\<iota>' \<in> Inf_G\<close> unfolding \<G>_Inf_def g_def by auto 
    have concl_in: \<open>Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>' \<in>
      \<G>_F (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>)\<close>
      using i'_in subst_inf_def unfolding \<G>_Inf_def \<G>_F_def grounding_of_cls_def by auto
    show \<open>\<iota>' \<in> Red_Inf_G (\<G>_F (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota>))\<close>
      using standard_lifting.inf_map i'_in2 concl_in
      by (simp add: gr_calc.Red_Inf_of_Inf_to_N)
  qed
qed

lemma ground_subclauses_no_ctxt:
  assumes
    "\<forall>i < length CAs. CAs ! i = Cs ! i + poss (AAs ! i)" and
    "length Cs = length CAs" and
    "is_ground_cls_list CAs"
  shows "is_ground_cls_list Cs"
  unfolding is_ground_cls_list_def
  by (metis assms in_set_conv_nth is_ground_cls_list_def is_ground_cls_union)

lemma ground_ord_resolve_ground_no_ctxt: 
  assumes 
    CAs_p: "gr.ord_resolve CAs DA AAs As E" and
    ground_cas: "is_ground_cls_list CAs" and
    ground_da: "is_ground_cls DA"
  shows "is_ground_cls E"
proof -
  have a1: "atms_of E \<subseteq> (\<Union>CA \<in> set CAs. atms_of CA) \<union> atms_of DA"
    using gr.ord_resolve_atms_of_concl_subset[of CAs DA _ _ E] CAs_p by auto
  {
    fix L :: "'a literal"
    assume "L \<in># E"
    then have "atm_of L \<in> atms_of E"
      by (meson atm_of_lit_in_atms_of)
    then have "is_ground_atm (atm_of L)"
      using a1 ground_cas ground_da is_ground_cls_imp_is_ground_atm is_ground_cls_list_def
      by auto
  }
  then show ?thesis
    unfolding is_ground_cls_def is_ground_lit_def by simp
qed

lemma gr_res_is_res:
  \<open>is_ground_cls DA \<Longrightarrow> is_ground_cls_list CAs \<Longrightarrow> gr.ord_resolve CAs DA AAs As E \<Longrightarrow>
    \<exists>\<sigma>. ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
proof -
  assume
    ground_DA: \<open>is_ground_cls DA\<close> and
    ground_CAs: \<open>is_ground_cls_list CAs\<close> and
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close>
  have ground_E: "is_ground_cls E"
      using ground_ord_resolve_ground_no_ctxt gr_res ground_DA ground_CAs
      by auto
  show "\<exists>\<sigma>. ord_resolve (S_M S M) CAs DA AAs As \<sigma> E" using gr_res
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
        using ground_subclauses_no_ctxt[of CAs Cs AAs] unfolding is_ground_cls_list_def by auto
      have ground_set_as: "is_ground_atms (set As)"
        using ord_resolve(1) ground_DA
        by (metis atms_of_negs is_ground_cls_union set_mset_mset is_ground_cls_is_ground_atms_atms_of)
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

lemma union_G_F_ground: \<open>is_ground_clss (UNION M \<G>_F)\<close>
  unfolding \<G>_F_def by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)

lemma mset_upto_length_list: \<open>{# L ! x. x \<in># mset_set {0..<(length L)}#} = mset L\<close>
apply (subst eq_commute)
apply (induction L rule: rev_induct)
apply (auto simp: atLeast0_lessThan_Suc nth_append intro!: image_mset_cong)
done

(* TODO: Starting with Isabelle2021, this will corresponds to
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
    (* In the previous proofs we have CAs and DA on lhs of equality... which is better? *)
    "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" "DA0 \<cdot> \<eta> = DA" "E0 \<cdot> \<eta>2 = E" 
    "{DA0} \<union> set CAs0 \<subseteq> M"
    "length CAs0 = length CAs"
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
    using ord_resolve_obtain_clauses[of S M CAs DA, OF res_e select grounding n(2) \<open>DA = D + negs (mset As)\<close>
      \<open>\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close>, of thesis] by blast

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

  have \<open>length CAs0 = length CAs\<close> using n by simp

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
      \<open>\<forall>CA \<in> set CAs0. CA \<in> M\<close> \<open>length CAs0 = length CAs\<close>
  by blast
qed

lemma inf_eq: \<open>Consequence_Relations_and_Inference_Systems.prems_of \<iota> = Consequence_Relations_and_Inference_Systems.prems_of \<iota>' \<Longrightarrow>
  Consequence_Relations_and_Inference_Systems.concl_of \<iota> = Consequence_Relations_and_Inference_Systems.concl_of \<iota>' \<Longrightarrow>
  \<iota> = \<iota>'\<close> for \<iota> \<iota>'
proof -
  fix \<iota> \<iota>'
  assume
    prems: \<open>Consequence_Relations_and_Inference_Systems.prems_of \<iota> = Consequence_Relations_and_Inference_Systems.prems_of \<iota>'\<close> and
    concl: \<open>Consequence_Relations_and_Inference_Systems.concl_of \<iota> = Consequence_Relations_and_Inference_Systems.concl_of \<iota>'\<close>
  obtain Pi Ci where i_is: \<open>\<iota> = Consequence_Relations_and_Inference_Systems.Infer Pi Ci\<close>
    using Consequence_Relations_and_Inference_Systems.inference.exhaust by auto
  obtain Pi' Ci' where i'_is: \<open>\<iota>' = Consequence_Relations_and_Inference_Systems.Infer Pi' Ci'\<close>
    using Consequence_Relations_and_Inference_Systems.inference.exhaust by auto
  have prems_eq: \<open>Pi = Pi'\<close> using prems unfolding prems_of_def i_is i'_is by simp
  have concl_eq: \<open>Ci = Ci'\<close> using concl unfolding Consequence_Relations_and_Inference_Systems.concl_of_def i_is i'_is by simp  
  show \<open>\<iota> = \<iota>'\<close> using i_is i'_is prems_eq concl_eq by simp
qed

lemma subst_of_nth [simp]: \<open>i < length (Cs \<cdot>\<cdot>cl \<sigma>s) \<Longrightarrow> (Cs \<cdot>\<cdot>cl \<sigma>s) ! i = (Cs ! i) \<cdot> (\<sigma>s ! i)\<close>
proof auto
  fix i
  assume
    len_cs: \<open>i < length Cs\<close> and
    len_ss: \<open>i < length \<sigma>s\<close>
  show \<open>(Cs \<cdot>\<cdot>cl \<sigma>s) ! i = Cs ! i \<cdot> \<sigma>s! i\<close>
    using len_cs len_ss unfolding subst_cls_lists_def by auto
qed

lemma subst_Cons_nth: \<open>i < length ((C \<cdot> \<sigma>) # (Cs \<cdot>\<cdot>cl \<sigma>s)) \<Longrightarrow> ((C # Cs) ! i) \<cdot> ((\<sigma> # \<sigma>s) ! i) = ((C \<cdot> \<sigma>) # (Cs \<cdot>\<cdot>cl \<sigma>s)) ! i\<close>
by (auto simp: nth_Cons' simp del: subst_cls_lists_length)

lemma lifting_in_framework: \<open>\<iota>' \<in> Inf_from (UNION M \<G>_F) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> sound_F.Inf_from M \<and> \<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
proof -
  assume i'_in: \<open>\<iota>' \<in> Inf_from (UNION M \<G>_F)\<close>
  have prems_i'_in: \<open>set (inference.prems_of \<iota>') \<subseteq> UNION M \<G>_F\<close> using i'_in unfolding Inf_from_def by blast
  have i'_Inf_G: \<open>\<iota>' \<in> Inf_G\<close> using i'_in unfolding Inf_from_def by blast
  then obtain \<iota>'_RP where i'_RP_is: \<open>same_inf \<iota>'_RP \<iota>'\<close> and i'_RP_in: \<open>\<iota>'_RP \<in> gr.ord_\<Gamma>\<close>
    unfolding Inf_G_def same_inf_def by force
  then obtain CAs DA AAs As E where
    gr_res: \<open>gr.ord_resolve CAs DA AAs As E\<close> and
    is_inf: \<open>\<iota>'_RP = Inference_System.inference.Infer (mset CAs) DA E\<close>
    unfolding gr.ord_\<Gamma>_def by blast
  have CAs_is: \<open>side_prems_of \<iota>'_RP = mset CAs\<close> using is_inf unfolding side_prems_of_def by simp
  then have CAs_in: \<open>set CAs \<subseteq> set (inference.prems_of \<iota>')\<close>
    using i'_RP_is unfolding same_inf_def side_prems_of_def prems_of_def
    by (metis add_mset_add_single insertCI set_mset_add_mset_insert set_mset_mset subsetI)
  then have ground_CAs: \<open>is_ground_cls_list CAs\<close>
    using prems_i'_in union_G_F_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_is: \<open>main_prem_of \<iota>'_RP = DA\<close> using is_inf unfolding main_prem_of_def by simp
  then have DA_in: \<open>DA \<in> set (inference.prems_of \<iota>')\<close>
    using i'_RP_is unfolding same_inf_def by (metis add.commute multi_member_this set_mset_mset)
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_i'_in union_G_F_ground is_ground_clss_def by auto
  obtain \<sigma> where grounded_res: \<open>ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
    using gr_res_is_res[OF ground_DA ground_CAs gr_res] by auto
  have prems_ground: \<open>{DA} \<union> set CAs \<subseteq> grounding_of_clss M\<close>
    using prems_i'_in CAs_in DA_in unfolding grounding_of_clss_def \<G>_F_def by fast
  obtain \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    ground_n: "is_ground_subst \<eta>" and
    ground_ns: "is_ground_subst_list \<eta>s" and
    ground_ns2: "is_ground_subst \<eta>2" and
    ngr_res: "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0" and
    CAs0_is: "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" and
    DA0_is: "DA0 \<cdot> \<eta> = DA" and
    E0_is: "E0 \<cdot> \<eta>2 = E"  and
    prems_in: "{DA0} \<union> set CAs0 \<subseteq> M" and
    len_CAs0: "length CAs0 = length CAs"
    using ord_resolve_rename_lifting_with_length[OF sel_stable grounded_res selection_axioms prems_ground] by metis
  define \<iota>_RP where \<open>\<iota>_RP = Infer (mset CAs0) DA0 E0\<close>
  then have i_RP_in: \<open>\<iota>_RP \<in> ord_FO_\<Gamma> S\<close> using ngr_res unfolding ord_FO_\<Gamma>_def by blast
  define PAs where \<open>PAs = inference.prems_of \<iota>'\<close>
  then have mset_PAs_is: \<open>mset PAs = mset CAs + {# DA #}\<close>
    using i'_RP_is is_inf unfolding same_inf_def by simp
  define PAs' where \<open>PAs' = DA # CAs\<close>
  then have mset_PAs': \<open>mset PAs' = mset PAs\<close> using mset_PAs_is by simp
  then have len_PAs: \<open>length PAs = length PAs'\<close> by (metis size_mset)
  define n where \<open>n = length PAs\<close>
  then have len_ns: \<open>length \<eta>s >= n - 1\<close> using CAs0_is PAs'_def len_PAs by fastforce
  have len_PAs': \<open>length PAs' = n\<close> using n_def len_PAs by simp
  (*then have len_DA0_CAs0: \<open>length (DA0 # CAs0) = n\<close> using DA0_is CAs0_is unfolding PAs'_def sledgehammer*)
  have exist_map: \<open>\<exists>map_i. (\<forall>i. i < n \<longrightarrow> PAs!i = PAs'!(map_i i)) \<and> inj_on map_i {0..<n} \<and>
          map_i ` {0..<n} \<subseteq> {0..<length PAs}\<close> if \<open>n \<le> length PAs\<close>
    using that
  proof (induct n)
    case 0
    then show ?case by auto
  next
    case (Suc m) note _ = this(1) and small_enough = this(2)
    then obtain map_i where [simp]:\<open>(\<And>i. i < m \<Longrightarrow> PAs!i = PAs'!(map_i i))\<close> and
        inj: \<open>inj_on map_i {0..<m}\<close> and
        im_incl: \<open>map_i ` {0..<m} \<subseteq> {0..<n}\<close> 
        by (force simp: n_def len_PAs)
    define j where \<open>j \<equiv> SOME i. i < length PAs \<and> PAs!m = PAs'!i \<and> i \<notin> map_i ` {0..<m}\<close>
    have cut_n_m: \<open>mset_set {0..<n} = mset_set (map_i ` {0..<m}) + (mset_set {0..<n} - mset_set (map_i ` {0..<m}))\<close>
      by (subst subset_mset.add_diff_inverse)
       (use im_incl in \<open>auto simp: image_iff\<close>)
    have \<open>PAs!m \<in># mset PAs - mset (take m PAs)\<close>
      apply (subst(2) append_take_drop_id[symmetric,of _ m])
      apply (subst mset_append)
      by (use small_enough in \<open>auto simp: in_set_drop_conv_nth\<close>)
    also have \<open>mset PAs - mset (take m PAs) = mset PAs' - mset (map (\<lambda>i. PAs'!(map_i i)) [0..<m])\<close>
      apply (subst map_cong[OF refl, of _ _ "\<lambda>i. PAs!i"])
      using small_enough
      by (auto simp: min_def mset_PAs' take_map_nth_alt_def)
    finally have \<open>\<exists>i. i < length PAs \<and> PAs!m = PAs'!i \<and> i \<notin> map_i ` {0..<m}\<close>
      apply (subst (asm)(2) map_nth[symmetric])
      unfolding mset_map mset_upt len_PAs' apply (subst (asm) cut_n_m)
      by (auto simp: image_mset_mset_set[symmetric] inj in_distinct_mset_diff_iff dist len_PAs n_def
        dest!: distinct_mem_diff_mset) 
    then have \<open>PAs!m = PAs'!j\<close> and j_notin: \<open>j \<notin> map_i ` {0..<m}\<close> and \<open>j < length PAs\<close>
      using someI[of \<open>\<lambda>i. i < length PAs \<and> PAs!m = PAs'!i \<and> i \<notin> map_i ` {0..<m}\<close>]
      unfolding j_def[symmetric]
      by blast+
    moreover have \<open>inj_on (map_i(m := j)) {0..<Suc m}\<close>
      unfolding inj_on_def
      apply (intro ballI)
      subgoal for x y
        using inj_onD[OF inj, of x y] j_notin by auto
      done
    ultimately show ?case
      apply -
      apply (rule exI[of _ \<open>map_i (m:=j)\<close>])
      using inj im_incl by (auto simp flip: fun_upd_def simp: len_PAs n_def less_Suc_eq image_subset_iff)
  qed
  then obtain map_i where map_i_def: \<open>i < n \<Longrightarrow> PAs!i = PAs'!(map_i i)\<close> and len_map_i: \<open>i < n \<Longrightarrow> (map_i i) < n\<close> and
     inj: \<open>inj_on map_i {0..<n}\<close> for i
    unfolding len_PAs n_def by fastforce
  have [simp]: \<open>map_i ` {0..<n} = {0..<n}\<close>
    apply (rule endo_inj_surj) using len_map_i inj by auto
  have ground_n_ns: \<open>is_ground_subst_list (\<eta> # \<eta>s)\<close>
    using ground_n ground_ns unfolding is_ground_subst_list_def by simp
  obtain \<rho>s where len_rs: \<open>length \<rho>s = n\<close> and rs_def: \<open>i < n \<Longrightarrow> \<rho>s!i = (\<eta> # \<eta>s)!(map_i i)\<close> for i  
    apply (rule that[of \<open>map (\<lambda>i. (\<eta> # \<eta>s)!(map_i i)) [0..<n]\<close>])
    by (auto simp: n_def)
  have \<open>i < n \<Longrightarrow> is_ground_subst (\<rho>s!i)\<close> for i using rs_def ground_n_ns unfolding is_ground_subst_list_def
  proof (cases "map_i i = 0")
    assume
      i_smaller_n: \<open>i < n\<close> and
      rs_def2: \<open>\<And>i. i < n \<Longrightarrow> \<rho>s ! i = (\<eta> # \<eta>s) ! map_i i\<close> and
      gr_subst_list_def: \<open>Ball (set (\<eta> # \<eta>s)) is_ground_subst\<close> and
      i_maps_to: \<open>map_i i = 0\<close>
    have \<open>\<rho>s ! i = \<eta>\<close> by (simp add: i_smaller_n i_maps_to rs_def2)
    then show \<open>is_ground_subst (\<rho>s ! i)\<close> using ground_n by simp
  next
    assume
      i_smaller_n: \<open>i < n\<close> and
      rs_def2: \<open>\<And>i. i < n \<Longrightarrow> \<rho>s ! i = (\<eta> # \<eta>s) ! map_i i\<close> and
      gr_subst_list_def: \<open>Ball (set (\<eta> # \<eta>s)) is_ground_subst\<close> and
      i_nmaps_to: \<open>map_i i \<noteq> 0\<close>
    have rs_nth: \<open>\<rho>s ! i = \<eta>s ! (map_i i - 1)\<close>
      using i_smaller_n i_nmaps_to rs_def2 by simp
    define j where \<open>j = map_i i - 1\<close>
    have \<open>j \<in> {0..<(n-1)}\<close> using j_def i_nmaps_to i_smaller_n len_map_i by force
    then have \<open>is_ground_subst (\<eta>s ! j)\<close> using ground_ns len_ns unfolding is_ground_subst_list_def by fastforce
    then show \<open>is_ground_subst (\<rho>s ! i)\<close> using rs_nth j_def unfolding is_ground_subst_list_def by simp
  qed
  then have ground_rs: \<open>is_ground_subst_list \<rho>s\<close> using len_rs unfolding is_ground_subst_list_def set_conv_nth by auto
  have mset_list_map_i: \<open>add_mset DA0 (mset CAs0) = {#(DA0 # CAs0) ! map_i x. x \<in># mset_set {0..<n}#}\<close> (is "?A = ?B")
  proof -
    have len_DA0_CAs0: \<open>length (DA0 # CAs0) = n\<close> using len_CAs0 len_PAs' unfolding PAs'_def by simp 
    have map_i_surj: \<open>mset_set {0..<n} = image_mset map_i (mset_set {0..<n})\<close>
      using image_mset_mset_set[OF inj] by simp
    have \<open>?B = {#(DA0 # CAs0) ! x. x \<in># image_mset map_i (mset_set {0..<n})#}\<close> by simp
    then have \<open>?B = {#(DA0 # CAs0) ! x. x \<in># mset_set {0..<n}#}\<close> by (simp add: map_i_surj[symmetric])
    then have \<open>?B = mset (DA0 # CAs0)\<close> using mset_upto_length_list[of "DA0 # CAs0"] len_DA0_CAs0 by auto
    then show ?thesis by simp
  qed
  obtain \<iota> where len_prems_i: \<open>length (inference.prems_of \<iota>) = n\<close> and
    i_is: \<open>same_inf \<iota>_RP \<iota>\<close> and
    i_prems_order: \<open>\<And>i. i < n \<Longrightarrow> (inference.prems_of \<iota>)!i = (DA0 # CAs0)!(map_i i)\<close>
    apply (rule that[of \<open>Consequence_Relations_and_Inference_Systems.Infer (map (\<lambda>i. (DA0 # CAs0)!(map_i i)) [0..<n]) E0\<close>])
    using \<iota>_RP_def mset_list_map_i unfolding same_inf_def by auto
  then have i_Inf_F: \<open>\<iota> \<in> Inf_F\<close> using i_RP_in conv_inf_in_Inf_F unfolding Inf_F_def by blast
  have inf_from_cond: \<open>set (inference.prems_of \<iota>) \<subseteq> {DA0} \<union> set CAs0\<close>
    using i_is \<iota>_RP_def unfolding same_inf_def prems_of_def
    by (metis Inference_System.inference.sel(1) Inference_System.inference.sel(2) Un_insert_left
      add_mset_add_single equalityE set_mset_add_mset_insert set_mset_mset sup_bot.left_neutral)
  then have prems_of_i_in_M: \<open>set (inference.prems_of \<iota>) \<subseteq> M\<close> using prems_in by blast
  have \<open>Consequence_Relations_and_Inference_Systems.inference.prems_of \<iota>' =
    Consequence_Relations_and_Inference_Systems.inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s\<close>
  proof (rule nth_equalityI)
    show \<open>length (inference.prems_of \<iota>') = length (inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)\<close>
      using len_prems_i len_rs unfolding n_def PAs_def subst_cls_lists_def by simp
  next
    fix i
    have len_eq: \<open>length (inference.prems_of \<iota>') = length (inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)\<close>
      using len_prems_i len_rs unfolding n_def PAs_def subst_cls_lists_def by simp
    then have \<open>\<forall>i<length (inference.prems_of \<iota>'). (inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) ! i =
      ((inference.prems_of \<iota>) ! i) \<cdot> (\<rho>s ! i)\<close>
      using subst_of_nth by auto   
    then have \<open>\<forall>i<length (inference.prems_of \<iota>'). (inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) ! i =
       ((DA0 # CAs0) ! (map_i i)) \<cdot> ((\<eta> # \<eta>s) ! (map_i i))\<close>
       using i_prems_order rs_def unfolding n_def PAs_def by presburger 
    show \<open>i<length (inference.prems_of \<iota>') \<Longrightarrow> inference.prems_of \<iota>' ! i = (inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) ! i\<close>
      using len_map_i len_prems_i i_prems_order map_i_def DA0_is CAs0_is rs_def len_rs
        arg_cong[OF mset_PAs_is, of size]  unfolding PAs'_def n_def PAs_def by (auto simp: subst_Cons_nth)
  qed
  then have \<open>\<iota>' = Consequence_Relations_and_Inference_Systems.inference.Infer
    (Consequence_Relations_and_Inference_Systems.inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)
    (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota> \<cdot> \<eta>2) \<close>
    using inf_eq[of \<iota>' "Consequence_Relations_and_Inference_Systems.inference.Infer
      (Consequence_Relations_and_Inference_Systems.inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)
      (Consequence_Relations_and_Inference_Systems.inference.concl_of \<iota> \<cdot> \<eta>2)"] i_is E0_is \<iota>_RP_def is_inf i'_RP_is
    unfolding same_inf_def concl_of_def Consequence_Relations_and_Inference_Systems.inference.concl_of_def by auto
  then have \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close>
    unfolding \<G>_Inf_def using prems_of_i_in_M i'_Inf_G is_inf i_is ground_ns2 CAs0_is DA0_is E0_is
    i'_RP_is \<iota>_RP_def ground_rs
    by auto 
  then have \<open>\<iota> \<in> sound_F.Inf_from M \<and> \<iota>' \<in> the (\<G>_Inf \<iota>)\<close> unfolding sound_F.Inf_from_def
    using inf_from_cond prems_in i_Inf_F by auto
  then show \<open> \<exists>\<iota>. \<iota> \<in> sound_F.Inf_from M \<and> \<iota>' \<in> the (\<G>_Inf \<iota>)\<close> by blast
qed

interpretation src: lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_comp_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf "\<lambda>g. Empty_Order"
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
  have gn_sat: \<open>gr_calc.saturated (\<G>_standard_lifting.\<G>_set N)\<close>
    unfolding gr_calc.saturated_def
  proof
    fix \<iota>'
    assume i_in: \<open>\<iota>' \<in> Inf_from (\<G>_standard_lifting.\<G>_set N)\<close>
    obtain \<iota> where \<open>\<iota> \<in> sound_F.Inf_from N\<close> \<open>\<iota>' \<in> the (\<G>_Inf \<iota>)\<close> using i_in lifting_in_framework sorry
    show \<open>\<iota>' \<in> Red_Inf_G (\<G>_standard_lifting.\<G>_set N)\<close> using i_in n_sat unfolding src.lifted_calculus_with_red_crit.saturated_def sorry
    oops

find_theorems name: calc_G

end

definition entails_all_\<G>  :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<equiv> UNION N1 grounding_of_cls \<Turnstile>G UNION N2 grounding_of_cls\<close>

(* definition Red_Inf_all_\<G> :: "'a clause set \<Rightarrow> 'a clause inference set" where
  \<open>Red_Inf_all_\<G> N = {\<iota> \<in> Inf_F. \<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_set N)}\<close> *)
  
end

end
