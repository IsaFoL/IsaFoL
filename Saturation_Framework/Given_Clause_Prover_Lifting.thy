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
  "conv_inf \<iota> = Saturation_Framework_Preliminaries.inference.Infer (list_mset (prems_of \<iota>)) (concl_of \<iota>)"

definition same_inf ::
  "'a inference \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference \<Rightarrow> bool" where
  "same_inf \<iota>_RP \<iota> \<equiv>
    prems_of \<iota>_RP = mset (Saturation_Framework_Preliminaries.prems_of \<iota>) \<and>
    concl_of \<iota>_RP = Saturation_Framework_Preliminaries.concl_of \<iota>"

definition Inf_F :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_F = {\<iota>. \<exists>\<iota>_RP \<in> (ord_FO_\<Gamma> S). same_inf \<iota>_RP \<iota>}"

lemma conv_inf_in_Inf_F: \<open>conv_inf ` (ord_FO_\<Gamma> S) \<subseteq> Inf_F\<close>
  unfolding conv_inf_def Inf_F_def same_inf_def by auto

interpretation sound_F: Saturation_Framework_Preliminaries.sound_inference_system Bot_F entails_sound_F Inf_F 
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
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile>s set (inference.prems_of \<iota>) \<cdot>cs \<sigma>" and
      ground_subst: "is_ground_subst \<eta>"
    obtain \<iota>_RP where i_RP_in: "\<iota>_RP \<in> (ord_FO_\<Gamma> S)" and i_i_RP: "same_inf \<iota>_RP \<iota>"
      using i_in unfolding Inf_F_def same_inf_def by force 
    obtain CAs AAs As \<sigma> where the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>_RP) AAs As \<sigma> (concl_of \<iota>_RP)"
      and mset_CAs: "mset CAs = side_prems_of \<iota>_RP" using i_RP_in unfolding ord_FO_\<Gamma>_def by auto
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_i_RP unfolding same_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_i_RP unfolding same_inf_def by fastforce
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
    apply (intro conjI)
    subgoal by simp
    subgoal by blast
    subgoal by auto
    subgoal by blast
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
definition Inf_G :: "'a clause Saturation_Framework_Preliminaries.inference set" where
  "Inf_G = {\<iota>. \<exists>\<iota>_RP \<in> (gr.ord_\<Gamma>). same_inf \<iota>_RP \<iota>}"

definition entails_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool"  where
  "entails_G S1 S2 \<equiv> \<forall>I. I \<Turnstile>s S1 \<longrightarrow> I \<Turnstile>s S2"

abbreviation entails_sound_G :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "|\<approx>G" 50)  where
  "S1 |\<approx>G S2 \<equiv> entails_G S1 S2"

interpretation Saturation_Framework_Preliminaries.sound_inference_system Bot_G entails_sound_G Inf_G
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
    have concl: "concl_of \<iota>_RP = Saturation_Framework_Preliminaries.inference.concl_of \<iota>"
      using i_equal unfolding same_inf_def by fastforce
    have prems: "set (inference.prems_of \<iota>) = set_mset (prems_of \<iota>_RP)"
      using i_equal unfolding same_inf_def by simp
    have I_entails_prems_RP: "I \<Turnstile>s set_mset (prems_of \<iota>_RP)" using prems I_entails_prems by argo
    then have I_entails_concl_RP: "I \<Turnstile> concl_of \<iota>_RP"
      using ground_resolution_with_selection.ord_resolve_sound[of "S_M S M" CAs "main_prem_of \<iota>_RP" AAs As "concl_of \<iota>_RP" I]
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

interpretation sr: standard_redundancy_criterion_counterex_reducing gr.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP (S_M S M)"
  by unfold_locales

definition Red_Inf_G :: "'a clause set \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference set" where
  "Red_Inf_G S1 \<equiv> {\<iota>. \<exists>\<iota>_RP \<in> sr.Ri S1. same_inf \<iota>_RP \<iota>}"

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
      concl_in: \<open>Saturation_Framework_Preliminaries.inference.concl_of \<iota> \<in> N\<close>
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
  then have i_from: \<open>set (Saturation_Framework_Preliminaries.prems_of \<iota>) \<subseteq> N\<close>
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
  then have i_from: \<open>set (Saturation_Framework_Preliminaries.prems_of \<iota>) \<subseteq> N\<close> using i_to_i_RP unfolding conv_inf_def by auto
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
    E_eq: \<open>E = \<Union>#mset Cs + Da\<close> and
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
    concl_i_is: \<open>concl_of \<iota> = \<Union># mset Cs3 + D3\<close> and
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
    concl_i'_is: \<open>concl_of \<iota>' = \<Union># mset Cs4 + D4\<close> and
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
  then have \<open>\<Union># mset Cs3 - Cs3!0 = \<Union># mset Cs4 - Cs4!0\<close> using Cs_eq len_Cs3 len_Cs4
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

(* TODO: move in Standard_Redundancy.thy in AFP Ordered_Resolution_Prover *)
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
      unfolding same_inf_def by (metis Saturation_Framework_Preliminaries.inference.sel(1)
        Saturation_Framework_Preliminaries.inference.sel(2) list_of_mset_exi)
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

interpretation calc_G: Saturation_Framework_Preliminaries.static_refutational_complete_calculus Bot_G
  entails_sound_G Inf_G entails_comp_G Red_Inf_G Red_F_G
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

definition subst_inf :: \<open>'a clause Saturation_Framework_Preliminaries.inference \<Rightarrow> 's
                          \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference\<close> (infixl "\<cdot>inf" 67) where
  \<open>\<iota> \<cdot>inf \<sigma> = Saturation_Framework_Preliminaries.Infer
    (map (\<lambda> A. A \<cdot> \<sigma>) (Saturation_Framework_Preliminaries.prems_of \<iota>))
    ((Saturation_Framework_Preliminaries.concl_of \<iota>) \<cdot> \<sigma>)\<close>

definition \<G>_Inf :: \<open>'a clause Saturation_Framework_Preliminaries.inference
                      \<Rightarrow> 'a clause Saturation_Framework_Preliminaries.inference set\<close> where
  \<open>\<G>_Inf \<iota> = {Saturation_Framework_Preliminaries.inference.Infer
    ((inference.prems_of \<iota>) \<cdot>\<cdot>cl \<rho>s) ((Saturation_Framework_Preliminaries.concl_of \<iota>) \<cdot> \<rho>)
    |\<rho> \<rho>s. is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho> \<and>
    Saturation_Framework_Preliminaries.inference.Infer ((inference.prems_of \<iota>) \<cdot>\<cdot>cl \<rho>s)
    ((Saturation_Framework_Preliminaries.concl_of \<iota>) \<cdot> \<rho>)  \<in> Inf_G }\<close>

interpretation \<G>: grounding_function Bot_F entails_sound_F Inf_F Bot_G entails_sound_G Inf_G
  entails_comp_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf
proof
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
  assume i_in: \<open>\<iota> \<in> Inf_F\<close>
  show \<open>\<G>_Inf \<iota> \<subseteq> Red_Inf_G (\<G>_F (Saturation_Framework_Preliminaries.inference.concl_of \<iota>))\<close>
  proof
    fix \<iota>'
    assume i'_in: \<open>\<iota>' \<in> \<G>_Inf \<iota>\<close>
    then have i'_in2: \<open>\<iota>' \<in> Inf_G\<close>unfolding \<G>_Inf_def by blast
    have concl_in: \<open>Saturation_Framework_Preliminaries.inference.concl_of \<iota>' \<in>
      \<G>_F (Saturation_Framework_Preliminaries.inference.concl_of \<iota>)\<close>
      using i'_in subst_inf_def unfolding \<G>_Inf_def \<G>_F_def grounding_of_cls_def by auto
    show \<open>\<iota>' \<in> Red_Inf_G (\<G>_F (Saturation_Framework_Preliminaries.inference.concl_of \<iota>))\<close>
      using Saturation_Framework_Preliminaries.grounding_function.inf_map i'_in2 concl_in
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
 
      have ground_e: "is_ground_cls (\<Union>#mset Cs + D)"
        using ground_d ground_cs ground_E e by simp
      show ?thesis
        using m DA e ground_e
          ord_resolve.intros[OF cas_len cs_len aas_len as_len nz cas aas_not_empt \<sigma>_p fo_elig ll]
        by auto
    qed
qed

lemma union_G_F_ground: \<open>is_ground_clss (UNION M \<G>_F)\<close>
  unfolding \<G>_F_def by (simp add: grounding_ground grounding_of_clss_def is_ground_clss_def)

lemma \<open>\<iota>' \<in> Inf_from (UNION M \<G>_F) \<Longrightarrow> \<exists>\<iota>. \<iota> \<in> sound_F.Inf_from M \<and> \<iota>' \<in> \<G>_Inf \<iota>\<close>
proof
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
    prems_in: "{DA0} \<union> set CAs0 \<subseteq> M"
    using ord_resolve_rename_lifting[OF sel_stable grounded_res selection_axioms prems_ground] by metis
  define \<iota>_RP where \<open>\<iota>_RP = Infer (mset CAs0) DA0 E0\<close>
  then have i_RP_in: \<open>\<iota>_RP \<in> ord_FO_\<Gamma> S\<close> using ngr_res unfolding ord_FO_\<Gamma>_def by blast
  define \<iota> where \<open>\<iota> = conv_inf \<iota>_RP\<close>
  then have \<open>\<iota> \<in> Inf_F\<close> using i_RP_in conv_inf_in_Inf_F unfolding Inf_F_def by blast
  have \<open>{DA0} \<union> set CAs0 = set (inference.prems_of \<iota>)\<close> using \<iota>_def \<iota>_RP_def unfolding conv_inf_def by simp
  then have \<open>set (inference.prems_of \<iota>) \<subseteq> M\<close> using prems_in by simp
  define PAs where \<open>PAs = inference.prems_of \<iota>'\<close>
  then have mset_PAs_is: \<open>mset PAs = mset CAs + {# DA #}\<close>
    using i'_RP_is is_inf unfolding same_inf_def by simp
  define PAs' where \<open>PAs' = DA # CAs\<close>
  then have mset_PAs': \<open>mset PAs' = mset PAs\<close> using mset_PAs_is by simp
  then have len_PAs: \<open>length PAs = length PAs'\<close> by (metis size_mset)
  define n where \<open>n = length PAs\<close>
  then have len_ns: \<open>length \<eta>s >= n - 1\<close> using CAs0_is PAs'_def len_PAs by fastforce
  have len_PAs': \<open>length PAs' = n\<close> using n_def len_PAs by simp
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
  have \<open>\<iota>' = Saturation_Framework_Preliminaries.inference.Infer
    (Saturation_Framework_Preliminaries.inference.prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)
    (Saturation_Framework_Preliminaries.inference.concl_of \<iota> \<cdot> \<eta>2) \<close>
  sorry
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
  then have \<open>is_ground_subst_list \<rho>s\<close> using len_rs unfolding is_ground_subst_list_def set_conv_nth by auto
  then have \<open>\<iota>' \<in> \<G>_Inf \<iota>\<close> unfolding \<G>_Inf_def using i'_Inf_G is_inf \<iota>_def ground_ns2 CAs0_is DA0_is E0_is i'_RP_is \<iota>_RP_def 
oops

thm conv_inf_def


end

end

end
