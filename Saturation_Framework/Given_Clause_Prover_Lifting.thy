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
  then have i_from: \<open>set (Saturation_Framework_Preliminaries.prems_of \<iota>) \<subseteq> N\<close> using i_to_i_RP unfolding conv_inf_def by auto
  have \<open>\<iota> \<in> Inf_G\<close> using i_RP_from i_to_i_RP unfolding gr.inferences_from_def Inf_G_def by blast
  then show \<open>\<iota> \<in> gr_calc.Inf_from N\<close> using i_from unfolding gr_calc.Inf_from_def by fast
qed

lemma \<open>gr.eligible As D \<Longrightarrow> mset As = mset As' \<Longrightarrow> gr.eligible As' D\<close>
  unfolding gr.eligible.simps
  by (cases As; cases As')
    (auto simp: add_mset_eq_add_mset eq_commute[of "add_mset _ _" "mset _"] image_mset_remove1_mset_if)

find_theorems "_ \<in> set (drop _ _)"

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
  assumes inj: \<open>inj_on f (set_mset (M + M'))\<close>
  shows \<open>image_mset f M' = image_mset f M \<longleftrightarrow> M' = M\<close> (is \<open>?A = ?B\<close>)
proof
  assume ?B
  then show ?A by auto
next
  assume ?A
  then show ?B
    using inj
  proof(induction M arbitrary: M')
    case empty
    then show ?case by auto
  next
    case (add x M) note IH = this(1) and H = this(2) and inj = this(3)

    obtain M1 x' where
      M': \<open>M' = add_mset x' M1\<close> and
      f_xx': \<open>f x' = f x\<close> and
      M1_M: \<open>image_mset f M1 = image_mset f M\<close>
      using H by (auto dest!: msed_map_invR)
    moreover have \<open>M1 = M\<close>
      apply (rule IH[OF M1_M])
      using inj by (auto simp: M')
    moreover have \<open>x = x'\<close>
      using inj f_xx' by (auto simp: M')
    ultimately show ?case by fast
  qed
qed

(* Move to Multiset_More.thy *)
lemma in_distinct_mset_diff_iff:
  \<open>distinct_mset M \<Longrightarrow>  x \<in># M - N \<longleftrightarrow> x \<notin># N \<and> x \<in># M\<close>
  using distinct_mem_diff_mset[of M x N]
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
    S_empty: \<open>\<forall>i<n. S (CAs ! i) = {#}\<close>
 using res unfolding gr.ord_resolve.simps by auto
  have x_in_equiv: \<open>x \<in># mset CAs' \<Longrightarrow> x \<in># mset CAs\<close> for x using mset_CAs by simp
  have len_CAs': \<open>length CAs' = n\<close> using len_CAs mset_CAs using mset_eq_length by fastforce
  have dist: \<open>distinct_mset (mset_set {0..<n})\<close> for n :: nat
    apply (subst atLeastLessThan_upt, subst mset_set_set)
     apply auto[]
    apply (subst distinct_mset_mset_distinct)
    apply auto
    done
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
      using dist by (auto simp: image_mset_mset_set[symmetric] inj in_distinct_mset_diff_iff dist
          len_CAs'
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
  obtain D3 Cs3 where
    \<open>main_prem_of \<iota> = D3 + negs (mset As3)\<close> and
    concl_i_is: \<open>concl_of \<iota> = \<Union># mset Cs3 + D3\<close> and
    len_Cs3: \<open>length Cs3 = n\<close> and
    CAs_i3: \<open>\<forall>i<n. (main_prem_of \<iota>' # CAs) ! i = Cs3 ! i + poss (AAs3 ! i)\<close> and
    \<open>\<forall>i<n. AAs3 ! i \<noteq> {#}\<close> and
    AAs3_i: \<open>\<forall>i<n. \<forall>A\<in>#AAs3 ! i. A = As3 ! i\<close> and
    \<open>gr.eligible As3 (D3 + negs (mset As3))\<close> and
    max3: \<open>\<forall>i<n. gr.strictly_maximal_wrt (As3 ! i) (Cs3 ! i)\<close> and
    \<open>\<forall>i<n. S (Cs3 ! i + poss (AAs3 ! i)) = {#}\<close>
    using A3_is n_is unfolding gr.ord_resolve.simps by auto
  obtain D4 Cs4 where
    \<open>main_prem_of \<iota>' = D4 + negs (mset As4)\<close> and
    concl_i'_is: \<open>concl_of \<iota>' = \<Union># mset Cs4 + D4\<close> and
    len_Cs4: \<open>length Cs4 = n\<close> and
    CAs_i4: \<open>\<forall>i<n. (main_prem_of \<iota> # CAs) ! i = Cs4 ! i + poss (AAs4 ! i)\<close> and
    \<open>\<forall>i<n. AAs4 ! i \<noteq> {#}\<close> and
    AAs4_i: \<open>\<forall>i<n. \<forall>A\<in>#AAs4 ! i. A = As4 ! i\<close> and
    \<open>gr.eligible As4 (D4 + negs (mset As4))\<close> and
    max4: \<open>\<forall>i<n. gr.strictly_maximal_wrt (As4 ! i) (Cs4 ! i)\<close> and
    \<open>\<forall>i<n. S (Cs4 ! i + poss (AAs4 ! i)) = {#}\<close>
    using A4_is len_AAs4 unfolding gr.ord_resolve.simps by auto
  have As_eq: \<open>\<forall>i \<in> {1..<n}. As3!i = As4!i\<close>
    using CAs_i3 CAs_i4 AAs3_i AAs4_i max3 max4 unfolding gr.strictly_maximal_wrt_def
    by (metis
      \<open>\<And>thesis. (\<And>D3 Cs3. \<lbrakk>main_prem_of \<iota> = D3 + negs (mset As3);
        Inference_System.inference.concl_of \<iota> = \<Union>#mset Cs3 + D3;
        length Cs3 = n;
        \<forall>i<n. (main_prem_of \<iota>' # CAs) ! i = Cs3 ! i + poss (AAs3 ! i);
        \<forall>i<n. AAs3 ! i \<noteq> {#};
        \<forall>i<n. \<forall>A\<in>#AAs3 ! i. A = As3 ! i;
        gr.eligible As3 (D3 + negs (mset As3));
        \<forall>i<n. gr.strictly_maximal_wrt (As3 ! i) (Cs3 ! i);
        \<forall>i<n. S (Cs3 ! i + poss (AAs3 ! i)) = {#}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      \<open>\<And>thesis. (\<And>D4 Cs4. \<lbrakk>main_prem_of \<iota>' = D4 + negs (mset As4);
        Inference_System.inference.concl_of \<iota>' = \<Union>#mset Cs4 + D4;
        length Cs4 = n;
        \<forall>i<n. (main_prem_of \<iota> # CAs) ! i = Cs4 ! i + poss (AAs4 ! i);
        \<forall>i<n. AAs4 ! i \<noteq> {#}; \<forall>i<n. \<forall>A\<in>#AAs4 ! i. A = As4 ! i;
        gr.eligible As4 (D4 + negs (mset As4));
        \<forall>i<n. gr.strictly_maximal_wrt (As4 ! i) (Cs4 ! i);
        \<forall>i<n. S (Cs4 ! i + poss (AAs4 ! i)) = {#}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      atLeastLessThan_iff empty_iff gr.eligible.cases image_mset_is_empty_iff len_As3 len_As_eq
      length_greater_0_conv linorder_not_le nth_Cons_0 nth_mem_mset set_mset_empty)
  then have AAs_eq: \<open>\<forall>i \<in> {1..<n}. AAs3!i = AAs4!i\<close>
    using CAs_i3 CAs_i4 AAs3_i AAs4_i max3 max4 unfolding gr.strictly_maximal_wrt_def
    by (metis
      \<open>\<And>thesis. (\<And>D3 Cs3. \<lbrakk>main_prem_of \<iota> = D3 + negs (mset As3);
        Inference_System.inference.concl_of \<iota> = \<Union>#mset Cs3 + D3;
        length Cs3 = n;
        \<forall>i<n. (main_prem_of \<iota>' # CAs) ! i = Cs3 ! i + poss (AAs3 ! i);
        \<forall>i<n. AAs3 ! i \<noteq> {#};
        \<forall>i<n. \<forall>A\<in>#AAs3 ! i. A = As3 ! i;
        gr.eligible As3 (D3 + negs (mset As3));
        \<forall>i<n. gr.strictly_maximal_wrt (As3 ! i) (Cs3 ! i);
        \<forall>i<n. S (Cs3 ! i + poss (AAs3 ! i)) = {#}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      \<open>\<And>thesis. (\<And>D4 Cs4. \<lbrakk>main_prem_of \<iota>' = D4 + negs (mset As4);
        Inference_System.inference.concl_of \<iota>' = \<Union>#mset Cs4 + D4;
        length Cs4 = n;
        \<forall>i<n. (main_prem_of \<iota> # CAs) ! i = Cs4 ! i + poss (AAs4 ! i);
        \<forall>i<n. AAs4 ! i \<noteq> {#}; \<forall>i<n. \<forall>A\<in>#AAs4 ! i. A = As4 ! i;
        gr.eligible As4 (D4 + negs (mset As4));
        \<forall>i<n. gr.strictly_maximal_wrt (As4 ! i) (Cs4 ! i);
        \<forall>i<n. S (Cs4 ! i + poss (AAs4 ! i)) = {#}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      atLeastLessThan_iff empty_iff gr.eligible.cases image_mset_is_empty_iff in_mset_conv_nth len_AAs4
      len_AAs_eq len_As3 len_As_eq length_greater_0_conv linorder_not_le nth_Cons_0 set_mset_empty)
    then have Cs_eq: \<open>\<forall>i \<in> {1..<n}. Cs3!i = Cs4!i\<close>
      using CAs_i3 CAs_i4 by fastforce
    then have \<open>Cs3!0 + D3 = Cs4!0 + D4\<close> using concl_i_is concl_i'_is concl_eq len_Cs3 len_Cs4
    (* trouver un lemme qui supprime des éléments/sous-ensemble égaux de multisets egaux*) sorry
  show ?B
  sorry
qed
term list_mset
term gr.ord_resolve
 (* fix \<iota> \<iota>'
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
*)

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

