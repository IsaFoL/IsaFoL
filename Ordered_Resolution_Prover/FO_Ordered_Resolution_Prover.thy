(*  Title:       A Simple Ordered Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Simple Ordered Resolution Prover for First-Order Clauses\<close>

theory FO_Ordered_Resolution_Prover
  imports FO_Ordered_Resolution
begin

type_synonym 'a state = "'a clause set \<times> 'a clause set \<times> 'a clause set"

locale FO_resolution_with_selection =
  FO_resolution subst_atm id_subst comp_subst mk_var_dis mgu less_atm +
  selection S
  for
    S :: "('a :: wellorder) clause \<Rightarrow> _" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s => 's => 's" and
    mk_var_dis :: "'a literal multiset list \<Rightarrow> 's list" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

fun N_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "N_of_state (N, P, Q) = N"

fun P_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "P_of_state (N, P, Q) = P"

fun Q_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "Q_of_state (N, P, Q) = Q"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = N_of_state St \<union> P_of_state St \<union> Q_of_state St"

abbreviation grounding_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "grounding_of_state St \<equiv> grounding_of_clss (clss_of_state St)"

definition ord_FO_\<Gamma> :: "'a inference set" where
  "ord_FO_\<Gamma> = {Infer CC D E | CC D E Cl \<sigma>. ord_resolve_rename S Cl D \<sigma> E \<and> mset Cl = CC}"

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

inductive subsume_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where (* This is never used. *)
  "subsume_resolve (D + {#L#}) (C + (D + {#- L#}) \<cdot> \<sigma>) (C + D \<cdot> \<sigma>)"

text \<open>
@{text O} denotes relation composition in Isabelle, so the formalization uses @{text Q} instead.
\<close>

inductive resolution_prover :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infix "\<leadsto>" 50)  where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| forward_subsumption: "(\<exists>D \<in> P \<union> Q. subsumes D C) \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_P: "(\<exists>D \<in> N. strictly_subsumes D C) \<Longrightarrow> (N, P \<union> {C}, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_Q: "(\<exists>D \<in> N. strictly_subsumes D C) \<Longrightarrow> (N, P, Q \<union> {C}) \<leadsto> (N, P, Q)"
| forward_reduction: "(\<exists>D L'. D + {#L'#} \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N \<union> {C + {#L#}}, P, Q) \<leadsto> (N \<union> {C}, P, Q)"
| backward_reduction_P: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P \<union> {C + {#L#}}, Q) \<leadsto> (N, P \<union> {C}, Q)"
| backward_reduction_Q: "(\<exists>D L'. D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<le># C) \<Longrightarrow>
    (N, P, Q \<union> {C + {#L#}}) \<leadsto> (N, P \<union> {C}, Q)"
| clause_processing: "(N \<union> {C}, P, Q) \<leadsto> (N, P \<union> {C}, Q)"
| inference_computation:
    "N = concls_of (ord_FO_resolution.inferences_between Q C) \<Longrightarrow>
     ({}, P \<union> {C}, Q) \<leadsto> (N, P, Q \<union> {C})"

(* I could also have proved that state is a distributive lattice and define sup_state directly as Sup_llist *)
definition sup_state :: "('a state) llist \<Rightarrow> 'a state" where
  "sup_state Sts = (Sup_llist (lmap N_of_state Sts), Sup_llist (lmap P_of_state Sts), Sup_llist (lmap Q_of_state Sts))"

definition limit_state :: "('a state) llist \<Rightarrow> 'a state" where
  "limit_state Sts =
   (limit_llist (lmap N_of_state Sts), limit_llist (lmap P_of_state Sts), limit_llist (lmap Q_of_state Sts))"

definition fair_state_seq where
  "fair_state_seq Sts \<longleftrightarrow> N_of_state (limit_state Sts) = {} \<and> P_of_state (limit_state Sts) = {}"

context
  fixes
    Sts :: "('a state) llist"
  assumes
    finite_Sts0: "finite (clss_of_state (lnth Sts 0))" and
    empty_P0: "P_of_state (lnth Sts 0) = {}" and
    empty_Q0: "Q_of_state (lnth Sts 0) = {}" and
    deriv: "chain (op \<leadsto>) Sts"
begin

definition S_Q :: "'a clause \<Rightarrow> 'a clause" where
  "S_Q = S_M S (Q_of_state (limit_state Sts))"

interpretation sq: selection S_Q
  apply unfold_locales
  unfolding S_Q_def
  using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms by auto

interpretation gd: ground_resolution_with_selection "S_Q"
  by unfold_locales

interpretation src: standard_redundancy_criterion gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_Q"
  by unfold_locales

text \<open>
The extension of ordered resolution mentioned in 4.10. We let it consist of all sound rules.
\<close>

definition gd_ord_\<Gamma>':: "'a inference set" where
  "gd_ord_\<Gamma>' = {Infer CC D E | CC D E. (\<forall>I. I \<Turnstile>m CC \<longrightarrow>  I \<Turnstile> D \<longrightarrow> I \<Turnstile> E)}"

lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gd.ord_\<Gamma> \<subseteq> gd_ord_\<Gamma>'"
  unfolding gd_ord_\<Gamma>'_def
  using gd.ord_\<Gamma>_def gd.ord_resolve_sound by fastforce

lemma sound_gd_ord_\<Gamma>': "sound_inference_system gd_ord_\<Gamma>'"
  unfolding sound_inference_system_def gd_ord_\<Gamma>'_def
  by auto

lemma sat_preserving_gd_ord_\<Gamma>': "sat_preserving_inference_system gd_ord_\<Gamma>'"
  using sound_gd_ord_\<Gamma>' sat_preserving_inference_system.intro sound_inference_system.\<Gamma>_sat_preserving by blast

definition src_ext_Ri where
  "src_ext_Ri = (\<lambda>N. src.Ri N \<union> (gd_ord_\<Gamma>' - gd.ord_\<Gamma>))"

interpretation src_ext:
  sat_preserving_redundancy_criterion "gd_ord_\<Gamma>'" "src.Rf" "src_ext_Ri"
  unfolding sat_preserving_redundancy_criterion_def src_ext_Ri_def
  using sat_preserving_gd_ord_\<Gamma>' using standard_redundancy_criterion_extension gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion by auto

text \<open>
The following corresponds to Lemma 4.10:
\<close>

fun subst_inf :: "'a inference \<Rightarrow> 's \<Rightarrow> 'a inference" (infixl "\<cdot>i" 67) where
  "(Infer CC D E) \<cdot>i \<sigma> = Infer (CC \<cdot>cm \<sigma>) (D \<cdot> \<sigma>) (E \<cdot> \<sigma>)"

lemma prems_of_subst_inf_subst_cls_mset: "(prems_of (\<gamma> \<cdot>i \<mu>)) = ((prems_of \<gamma>) \<cdot>cm \<mu>)"
  by (induction \<gamma>) auto

lemma infer_from_superset: "infer_from x y \<Longrightarrow> z \<supseteq> x \<Longrightarrow> infer_from z y"
  by (meson infer_from_def lfp.leq_trans)

lemma strict_subsumption_redundant_clause:
  assumes "D \<cdot> \<sigma> \<subset># C" and "is_ground_subst \<sigma>"
  shows "C \<in> src.Rf (grounding_of_cls D)"
proof -
  from assms(1) have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<longrightarrow> I \<Turnstile> C"
    unfolding true_cls_def by blast
  moreover
  have "C > D \<cdot> \<sigma>"
    using assms(1)
    by (simp add: subset_imp_less_mset)
  moreover
  have "D \<cdot> \<sigma> \<in> grounding_of_cls D"
    by (metis (mono_tags, lifting) assms(2) mem_Collect_eq substitution_ops.grounding_of_cls_def)
  ultimately
  have "set_mset {#D \<cdot> \<sigma>#} \<subseteq> grounding_of_cls D \<and> (\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma>#} \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D'. D' \<in># {#D \<cdot> \<sigma>#} \<longrightarrow> D' < C)"
    by auto
  then have "C \<in> src.Rf (grounding_of_cls D)"
    using src.Rf_def[of "grounding_of_cls D"] by blast
  then show "C \<in> src.Rf (grounding_of_cls D)"
    by auto
qed

lemma strict_subsumption_redundant_state:
  assumes
    "D \<cdot> \<sigma> \<subset># C" and
    "is_ground_subst \<sigma>" and
    "D \<in> clss_of_state St"
  shows "C \<in> src.Rf (grounding_of_state St)"
proof -
  from assms have "C \<in> src.Rf (grounding_of_cls D)"
    using strict_subsumption_redundant_clause by auto
  then show "C \<in> src.Rf (grounding_of_state St)"
    using assms(3) unfolding clss_of_state_def grounding_of_clss_def using src.Rf_mono
    apply (induction St)
    apply auto
      apply (metis SUP_absorb contra_subsetD le_sup_iff order_refl)+
    done
qed

text \<open>
The following corresponds to Lemma 4.10:
\<close>

lemma subst_cls_eq_grounding_of_cls_subset_eq: "D \<cdot> \<sigma> = C \<Longrightarrow> grounding_of_cls C \<subseteq> grounding_of_cls D"
  unfolding grounding_of_cls_def
  apply auto
  apply (rule_tac x="\<sigma> \<odot> \<sigma>'" in exI)
  apply auto
  done

lemma resolution_prover_ground_derive:
  "St \<leadsto> St' \<Longrightarrow> src_ext.derive (grounding_of_state St) (grounding_of_state St')"
proof (induction rule: resolution_prover.induct)
  case (tautology_deletion A C N P Q)
  {
    fix C\<sigma>
    assume "C\<sigma> \<in> grounding_of_cls C"
    then obtain \<sigma> where "C\<sigma> = C \<cdot> \<sigma>"
      unfolding grounding_of_cls_def by auto
    then have "Neg (A \<cdot>a \<sigma>) \<in># C\<sigma> \<and> Pos (A \<cdot>a \<sigma>) \<in># C\<sigma>"
      using tautology_deletion Neg_Melem_subst_atm_subst_cls Pos_Melem_subst_atm_subst_cls by auto

    then have "C\<sigma> \<in> src.Rf (grounding_of_state (N, P, Q))"
      using src.tautology_redundant by auto
  }
  then have "grounding_of_state (N \<union> {C}, P, Q) - grounding_of_state (N, P, Q) \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover
  have "grounding_of_state (N, P, Q) - grounding_of_state (N \<union> {C}, P, Q) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      by auto
next
  case (forward_subsumption P Q C N)
  then obtain D where D_p: "D\<in>P \<union> Q \<and> subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def)
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      using subst_cls_eq_grounding_of_cls_subset_eq by simp
    have "grounding_of_state (N \<union> {C}, P, Q) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N \<union> {C}, P, Q)"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N \<union> {C}, P, Q)"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"]
        by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (backward_subsumption_P N C P Q) (* Adapted from previous proof *) (* Arguably I should extract some lemma that says: if subsumed then redundant... *)
  then obtain D where D_p: "D\<in>N \<and> strictly_subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding strictly_subsumes_def subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def)
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      using subst_cls_eq_grounding_of_cls_subset_eq by simp
    have "grounding_of_state (N, P \<union> {C}, Q) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N, P \<union> {C}, Q)"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N, P  \<union> {C}, Q)"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"]
      by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (backward_subsumption_Q N C P Q) (* Adapted from previous proof *)
  then obtain D where D_p: "D\<in>N \<and> strictly_subsumes D C"
    by auto
  from D_p obtain \<sigma> where \<sigma>_p: "D \<cdot> \<sigma> \<subseteq># C" unfolding strictly_subsumes_def subsumes_def by auto
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def)
  then show ?case
  proof
    assume "D \<cdot> \<sigma> = C"
    then have gC_gD: "grounding_of_cls C \<subseteq> grounding_of_cls D"
      using subst_cls_eq_grounding_of_cls_subset_eq by simp
    have "grounding_of_state (N, P, Q \<union> {C}) = grounding_of_state (N, P, Q)"
    proof (rule; rule)
      fix x
      assume "x \<in> grounding_of_state (N, P, Q \<union> {C})"
      then show "x \<in> grounding_of_state (N, P, Q)"
        using gC_gD D_p unfolding clss_of_state_def grounding_of_clss_def by auto
    next
      fix x
      assume "x \<in> grounding_of_state (N, P, Q)"
      then show "x \<in> grounding_of_state (N, P, Q  \<union> {C})"
        unfolding clss_of_state_def grounding_of_clss_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N, P, Q)"]
        by auto
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    have "grounding_of_cls C \<subseteq> src.Rf (grounding_of_state (N, P, Q))"
    proof
      fix C\<mu>
      assume "C\<mu> \<in> grounding_of_cls C"
      then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
        unfolding grounding_of_cls_def by auto
      have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
        using a subst_subset_mono by auto
      then show "C\<mu> \<in> src.Rf (grounding_of_state (N, P, Q))"
        using \<mu>_p strict_subsumption_redundant_state[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>" "(N, P, Q)"] D_p unfolding clss_of_state_def by auto
    qed
    then show ?case
      using src_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
      unfolding clss_of_state_def grounding_of_clss_def by force
  qed
next
  case (forward_reduction P Q L \<sigma> C N)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> P \<union> Q \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto

    define \<gamma> where "\<gamma> = Infer {#(C + {#L#})\<cdot> \<mu>#} ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>) (C \<cdot> \<mu>)"

    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N \<union> {C + {#L#}}, P, Q)"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N \<union> {C + {#L#}}, P, Q)"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus)
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "(\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>)"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by auto
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N \<union> {C}, P, Q) - grounding_of_state (N \<union> {C + {#L#}}, P, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N \<union> {C + {#L#}}, P, Q)))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  { (* This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N \<union> {C}, P, Q)"] \<mu>_def unfolding clss_of_state_def by force
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N \<union> {C + {#L#}}, P, Q) - grounding_of_state (N \<union> {C}, P, Q) \<subseteq> src.Rf (grounding_of_state (N \<union> {C}, P, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N \<union> {C}, P, Q)" "grounding_of_state (N \<union> {C + {#L#}}, P, Q)"]
    by auto
next
  case (backward_reduction_P N L \<sigma> C P Q) (* Adapted from previous proof *)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto

    define \<gamma> where "\<gamma> = Infer {#(C + {#L#})\<cdot> \<mu>#} ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>) (C \<cdot> \<mu>)"

    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N, P \<union> {C + {#L#}}, Q)"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N, P \<union> {C + {#L#}}, Q)"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus)
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow>  I \<Turnstile> C \<cdot> \<mu>"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by simp
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N, P \<union> {C}, Q) - grounding_of_state (N, P \<union> {C + {#L#}}, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N, P \<union> {C + {#L#}}, Q)))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  { (* This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P\<union> {C}, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N, P \<union> {C}, Q)"] \<mu>_def unfolding clss_of_state_def by force
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N, P  \<union> {C + {#L#}}, Q) - grounding_of_state (N, P  \<union> {C}, Q) \<subseteq> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N, P \<union> {C}, Q)" "grounding_of_state (N, P \<union> {C + {#L#}}, Q)"]
    by auto
next
  case (backward_reduction_Q N L \<sigma> C P Q) (* Adapted from previous proof *)
  then obtain D L' where DL'_p: "D + {#L'#} \<in> N \<and> - L = L' \<cdot>l \<sigma> \<and> D \<cdot> \<sigma> \<subseteq># C"
    by auto
  {
    fix C\<mu>
    assume "C\<mu> \<in> grounding_of_cls C"
    then obtain \<mu> where \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto

    define \<gamma> where "\<gamma> = Infer {#(C + {#L#})\<cdot> \<mu>#} ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>) (C \<cdot> \<mu>)"

    have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_state (N, P, Q \<union> {C + {#L#}})"
      using DL'_p \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def
      apply simp
      by (metis is_ground_comp_subst subst_cls_add_mset subst_cls_comp_subst)
    moreover
    have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_state (N, P, Q \<union> {C + {#L#}})"
      using \<mu>_p unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    moreover
    have "\<forall>I. I \<Turnstile> ((D \<cdot> \<sigma> \<cdot> \<mu>) + ({#- (L  \<cdot>l \<mu>)#})) \<longrightarrow> I \<Turnstile> ((C  \<cdot> \<mu>) + ({#L  \<cdot>l \<mu>#})) \<longrightarrow> I \<Turnstile> (D \<cdot> \<sigma> \<cdot> \<mu>) + (C \<cdot> \<mu>)"
        by auto
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
      using DL'_p
      by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus)
    then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      using DL'_p by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
    then have "\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
      by (meson true_cls_mset_singleton)
    ultimately
    have "\<gamma> \<in> src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}}))"
      unfolding src_ext.inferences_from_def unfolding gd_ord_\<Gamma>'_def infer_from_def \<gamma>_def by simp
    then have "C \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
      using image_iff unfolding \<gamma>_def by fastforce
    then have "C\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
      using \<mu>_p by auto
  }
  then have "grounding_of_state (N, P \<union> {C}, Q) - grounding_of_state (N, P, Q \<union> {C + {#L#}}) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state (N, P, Q \<union> {C + {#L#}})))"
    unfolding grounding_of_clss_def clss_of_state_def by auto
  moreover
  { (* This part is adapted from previous proof *)
    fix CL\<mu>
    assume "CL\<mu> \<in> grounding_of_cls (C + {#L#})"
    then obtain \<mu> where \<mu>_def: "CL\<mu> = (C + {#L#}) \<cdot> \<mu> \<and> is_ground_subst \<mu>"
      unfolding grounding_of_cls_def by auto
    have C\<mu>_CL\<mu>: "C \<cdot> \<mu> \<subset># (C + {#L#}) \<cdot> \<mu>"
      by auto
    then have "(C + {#L#}) \<cdot> \<mu> \<in> src.Rf (grounding_of_state (N, P\<union> {C}, Q))"
      using src.Rf_def[of "grounding_of_cls C"] using strict_subsumption_redundant_state[of C \<mu> "(C + {#L#}) \<cdot> \<mu>" "(N, P \<union> {C}, Q)"] \<mu>_def unfolding clss_of_state_def by force
    then have "CL\<mu> \<in> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
      using \<mu>_def by auto
  }
  then have "grounding_of_state (N, P , Q \<union> {C + {#L#}}) - grounding_of_state (N, P  \<union> {C}, Q) \<subseteq> src.Rf (grounding_of_state (N, P \<union> {C}, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "grounding_of_state (N, P \<union> {C}, Q)" "grounding_of_state (N, P, Q \<union> {C + {#L#}})"]
    by auto
next
  case (clause_processing N C P Q)
  then show ?case
    unfolding clss_of_state_def using src_ext.derive.intros by auto
next
  case (inference_computation N Q C P)
  {
    fix E\<mu>
    assume "E\<mu> \<in> grounding_of_clss N"
    then obtain \<mu> E where E_\<mu>_p: "E\<mu> = E \<cdot> \<mu> \<and> E \<in> N \<and> is_ground_subst \<mu>"
      unfolding grounding_of_clss_def grounding_of_cls_def by auto
    then have E_concl: "E \<in> concls_of (ord_FO_resolution.inferences_between Q C)"
      using inference_computation by auto
    then obtain \<gamma> where \<gamma>_p: "\<gamma> \<in> ord_FO_\<Gamma> \<and> infer_from (Q \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma> \<and> concl_of \<gamma> = E"
      unfolding ord_FO_resolution.inferences_between_def by auto
    then obtain CC D Cl \<sigma> where \<gamma>_p2: "\<gamma> = Infer CC D E \<and> ord_resolve_rename S Cl D \<sigma> E \<and> mset Cl = CC"
      unfolding ord_FO_\<Gamma>_def by auto
    define \<rho> where "\<rho> = hd (mk_var_dis (D # Cl))"
    define \<rho>s where "\<rho>s = tl (mk_var_dis (D # Cl))"
    define \<gamma>_ground where "\<gamma>_ground = Infer (mset (Cl \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu>) (D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu>) (E \<cdot> \<mu>)"
    have "\<forall>I. I \<Turnstile>m mset (Cl \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> E \<cdot> \<mu>"
      using ord_resolve_rename_ground_inst_sound[of S Cl D \<sigma> E _ _ _ \<mu>] \<rho>_def \<rho>s_def E_\<mu>_p \<gamma>_p2 by auto
    then have "\<gamma>_ground \<in> {Infer cc d e |cc d e. \<forall>I. I \<Turnstile>m cc \<longrightarrow> I \<Turnstile> d \<longrightarrow> I \<Turnstile> e}"
      unfolding \<gamma>_ground_def by auto
    moreover
    have "set_mset (prems_of \<gamma>_ground) \<subseteq> grounding_of_state ({}, P \<union> {C}, Q)"
      unfolding \<gamma>_ground_def using E_\<mu>_p \<gamma>_p2 \<gamma>_p unfolding infer_from_def
      unfolding clss_of_state_def grounding_of_clss_def
      apply simp
      apply (rule conjI)
      unfolding grounding_of_cls_def
      subgoal
        apply simp
        apply (metis is_ground_comp_subst subst_cls_comp_subst)
        done
      subgoal
        apply (subgoal_tac "set_mset (mset (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>)) \<subseteq> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
        subgoal
          using mset_subst_cls_list_subst_cls_mset apply auto[]
          done
        subgoal
          apply (subgoal_tac "\<forall>x \<in># (mset (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>)). x \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
          subgoal
            apply (auto;fail)
            done
          subgoal
            apply (subgoal_tac "\<forall>i < length (Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>). ((Cl \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i) \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> ((\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))")
            subgoal
              apply (metis (no_types, lifting) in_set_conv_nth set_mset_mset)
              done
            subgoal
              apply rule
              apply rule
              subgoal for i
                apply simp
                apply (subgoal_tac "Cl ! i \<in> {C} \<union> Q")
                subgoal
                  apply (cases "Cl ! i = C")
                  subgoal
                    apply (rule disjI1)
                    apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
                    using \<rho>s_def using mk_var_dis_p apply (auto;fail)
                    done
                  subgoal
                    apply (subgoal_tac "Cl ! i \<in> Q")
                    subgoal
                      apply (rule disjI2)
                      apply (rule disjI2)
                      apply (rule_tac x="Cl ! i " in bexI)
                      subgoal
                        apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
                        using \<rho>s_def using mk_var_dis_p apply (auto;fail)
                        done
                      subgoal
                        apply auto[]
                        done
                      done
                    subgoal
                      apply (auto;fail)
                      done
                    done
                  done
                subgoal
                  apply (metis UnI1 UnI2 insertE nth_mem_mset singletonI subsetCE)
                  done
                done
              done
            done
          done
        done
      done
    ultimately
    have "E \<cdot> \<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      unfolding src_ext.inferences_from_def inference_system.inferences_from_def gd_ord_\<Gamma>'_def infer_from_def
      using \<gamma>_ground_def by (metis (no_types, lifting) imageI inference.sel(3) mem_Collect_eq)
    then have "E\<mu> \<in> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      using E_\<mu>_p by auto
  }
  then have "grounding_of_state (N, P, Q \<union> {C}) - grounding_of_state ({}, P \<union> {C}, Q) \<subseteq> concls_of (src_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover
  have "grounding_of_state ({}, P \<union> {C}, Q) - grounding_of_state (N, P, Q \<union> {C}) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately
  show ?case
    using src_ext.derive.intros[of "(grounding_of_state (N, P, Q \<union> {C}))" "(grounding_of_state ({}, P \<union> {C}, Q))"] by auto
qed

text \<open>
Another formulation of the last part of lemma 4.10
\<close>

lemma resolution_prover_ground_derivation:
  "chain (op \<leadsto>) Sts \<Longrightarrow> chain src_ext.derive (lmap grounding_of_state Sts)"
  using resolution_prover_ground_derive by (simp add: chain_lmap[of "op \<leadsto>"])

text \<open>
The following is used prove to Lemma 4.11:
\<close>

(* FIXME: Used only once, really -- inline? *)
definition is_least :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_least P n \<longleftrightarrow> P n \<and> (\<forall>n' < n. \<not> P n')"

lemma least_exists: "P n \<Longrightarrow> \<exists>n. is_least P n"
  using exists_least_iff unfolding is_least_def by auto

lemma in_Sup_llist_in_nth: "C \<in> Sup_llist Ns \<Longrightarrow> \<exists>j. enat j < llength Ns \<and> C \<in> lnth Ns j"
  unfolding Sup_llist_def by auto

lemma Sup_llist_grounding_of_state_ground:
  assumes "C \<in> Sup_llist (lmap grounding_of_state Sts)"
  shows "is_ground_cls C"
proof -
  have "\<exists>j. enat j < llength (lmap grounding_of_state Sts) \<and> (C \<in> (lnth (lmap grounding_of_state Sts) j))"
    using assms in_Sup_llist_in_nth by metis
  then obtain j where
    "enat j < llength (lmap grounding_of_state Sts)"
    "C \<in> lnth (lmap grounding_of_state Sts) j"
    by blast
  then show ?thesis
    unfolding grounding_of_clss_def grounding_of_cls_def by auto
qed

lemma limit_llist_grounding_of_state_ground:
  assumes "C \<in> limit_llist (lmap grounding_of_state Sts)"
  shows "is_ground_cls C"
  using assms limit_llist_subset_Sup_llist[of "lmap grounding_of_state Sts"]
    Sup_llist_grounding_of_state_ground
  by blast

lemma limit_llist_eventually_always:
  assumes "C \<in> limit_llist Ns"
  shows "\<exists>i. enat i < llength Ns \<and> (\<forall>j \<ge> i. enat j < llength Ns \<longrightarrow> C \<in> lnth Ns j)"
  using assms unfolding limit_llist_def by fast

lemma in_lnth_grounding_in_lnth:
  assumes
    "C \<in> lnth (lmap grounding_of_state Sts) i" and
    "enat i < llength (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  using assms clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto

lemma in_Sup_llist_in_sup_state:
  assumes "C \<in> Sup_llist (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  from assms obtain i where i_p: "enat i < llength Sts \<and> C \<in> lnth (lmap grounding_of_state Sts) i"
    using in_Sup_llist_in_nth by fastforce
  then obtain D \<sigma> where "D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using in_lnth_grounding_in_lnth by force
  then have "D \<in> clss_of_state (sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using i_p unfolding sup_state_def clss_of_state_def
    by (metis (no_types, lifting) UnCI UnE contra_subsetD N_of_state.simps P_of_state.simps
        Q_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist)
  then show ?thesis
    by auto
qed

lemma N_of_state_limit_state_limit_llist_N_of_state:
  "N_of_state (limit_state Sts) = limit_llist (lmap N_of_state Sts)"
  unfolding limit_state_def by auto

lemma P_of_state_limit_state_limit_llist_P_of_state:
  "P_of_state (limit_state Sts) = limit_llist (lmap P_of_state Sts)"
  unfolding limit_state_def by auto

lemma Q_of_state_limit_state_limit_llist_Q_of_state:
  "Q_of_state (limit_state Sts) = limit_llist (lmap Q_of_state Sts)"
  unfolding limit_state_def by auto

lemma N_of_state_subset:
  assumes "enat l < llength Sts"
  shows "N_of_state (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
  using assms unfolding clss_of_state_def by auto

lemma P_of_state_subset:
  assumes "enat l < llength Sts"
  shows "P_of_state (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
  using assms unfolding clss_of_state_def by auto

lemma Q_of_state_subset:
  assumes "enat l < llength Sts"
  shows "Q_of_state (lnth Sts l) \<subseteq> clss_of_state (lnth Sts l)"
  using assms unfolding clss_of_state_def by auto

lemma grounding_of_clss_mono2: "C \<in> CC \<Longrightarrow> grounding_of_cls C \<subseteq> grounding_of_clss CC"
  using grounding_of_clss_def grounding_of_cls_def by auto

lemma eventually_deleted:
  assumes "D \<in> N_of_state (lnth Sts i)"
  assumes fair: "fair_state_seq Sts"
  assumes i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume a: "\<nexists>l. D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
  have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> N_of_state (lnth Sts l)"
  proof (rule; rule; rule)
    fix l :: "nat"
    assume
      "i \<le> l" and
      "enat l < llength Sts"
    then show "D \<in> N_of_state (lnth Sts l)"
    proof (induction l)
      case 0
      then show ?case using assms(1) by blast
    next
      case (Suc l)
      then show ?case using a by (metis Suc_ile_eq assms(1) le_SucE less_imp_le)
    qed
  qed
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> (lnth (lmap N_of_state Sts) l)"
    by auto
  then have "D \<in> limit_llist (lmap N_of_state Sts) "
    unfolding limit_llist_def using i_Sts by auto
  then show False using fair unfolding fair_state_seq_def
    by (simp add: N_of_state_limit_state_limit_llist_N_of_state)
qed

lemma eventually_deleted_P:
  assumes "D \<in> P_of_state (lnth Sts i)"
  assumes fair: "fair_state_seq Sts"
  assumes i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume a: "\<nexists>l. D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
  have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> P_of_state (lnth Sts l)"
    proof (rule; rule; rule)
    fix l :: "nat"
    assume
      "i \<le> l" and
      "enat l < llength Sts"
    then show "D \<in> P_of_state (lnth Sts l)"
    proof (induction l)
      case 0
      then show ?case using assms(1) by blast
    next
      case (Suc l)
      then show ?case using a by (metis Suc_ile_eq assms(1) le_SucE less_imp_le)
    qed
  qed
  then have "\<forall>l. i \<le> l \<longrightarrow> enat l < llength Sts \<longrightarrow> D \<in> (lnth (lmap P_of_state Sts) l)"
    by auto
  then have "D \<in> limit_llist (lmap P_of_state Sts) "
    unfolding limit_llist_def using i_Sts by auto
  then show False using fair unfolding fair_state_seq_def
    by (simp add: P_of_state_limit_state_limit_llist_P_of_state)
qed

lemma size_subst: "size (D \<cdot> \<sigma>) = size D"
  unfolding subst_cls_def by auto

lemma subset_subst_strictly_subsumes:
  assumes "C \<cdot> \<eta> \<subset># D"
  shows "strictly_subsumes C D"
proof -
  have "\<nexists>\<sigma>. D \<cdot> \<sigma> \<subseteq># C"
  proof
    assume "\<exists>\<sigma>. D \<cdot> \<sigma> \<subseteq># C"
    then obtain \<sigma> where "D \<cdot> \<sigma> \<subseteq># C"
      by blast
    then have "size (D \<cdot> \<sigma>) \<le> size C"
      by (simp add: size_mset_mono)
    then have "size D \<le> size C"
      using size_subst by auto
    moreover
    from assms have "size (C \<cdot> \<eta>) < size D"
      by (simp add: mset_subset_size)
    then have "size C < size D"
      using size_subst by auto
    ultimately
    show False
      by auto
  qed
  moreover
  from assms have "C \<cdot> \<eta> \<subseteq># D"
    by auto
  ultimately
  show ?thesis
    unfolding strictly_subsumes_def subsumes_def by auto
qed

lemma subsumes_trans:
  assumes "subsumes C D" and "subsumes D E"
  shows "subsumes C E"
  using assms unfolding subsumes_def
  by (metis subset_mset.dual_order.trans subst_cls_comp_subst subst_cls_mono_mset)

lemma proper_subsumes_trans:
  assumes "strictly_subsumes C D" and "strictly_subsumes D E"
  shows "strictly_subsumes C E"
  using assms strictly_subsumes_def subsumes_trans by blast

lemma subset_strictly_subsumes: "C \<subset># D \<Longrightarrow> strictly_subsumes C D"
  using subset_subst_strictly_subsumes[of C id_subst] by auto

lemma proper_neq: "strictly_subsumes D' D \<Longrightarrow> D' \<noteq> D \<cdot> \<sigma>"
  unfolding strictly_subsumes_def subsumes_def by blast

lemma least_exists':
  assumes "N \<noteq> {}"
  shows "\<exists>(m :: nat) \<in> N. (\<forall>n \<in> N. m \<le> n)"
proof -
  obtain y where "y \<in> N"
    using assms by auto
  then obtain m where
    m_p: "m \<in> N \<and> (\<forall>n' < m. n' \<notin> N)"
    using least_exists[of "\<lambda>x. x \<in> N" y] unfolding is_least_def by auto
  then have "\<forall>n'. n' \<in> N \<longrightarrow> \<not> n' <  m"
    by metis
  then have "\<forall>n'. n' \<in> N \<longrightarrow> n' \<ge>  m"
    by auto
  then show ?thesis
    using m_p by auto
qed

lemma f_Suc_decr_f_decr:
  fixes f :: "nat \<Rightarrow> nat"
  assumes
    f_decr: "\<forall>i. f (Suc i) \<le> f i" and
    i_le: "i \<le> l'"
  shows "f l' \<le> f i"
  using i_le by (induction "l' - i" arbitrary: i l') (simp_all add: f_decr lift_Suc_antimono_le)

lemma f_Suc_decr_eventually_const:
  fixes f :: "nat \<Rightarrow> nat"
  assumes leq: "\<forall>i. f (Suc i) \<le> f i"
  shows "\<exists>l. \<forall>l' \<ge> l. f l' = f (Suc l')"
proof (rule ccontr)
  assume a: "\<nexists>l. \<forall>l' \<ge> l. f l' = f (Suc l')"
  have "\<forall>i. \<exists>i'. i' > i \<and> f i' < f i"
  proof
    fix i
    from a have "\<not> (\<forall>l' \<ge> i. f l' = f (Suc l'))"
      by auto
    then have "\<exists>l' \<ge> i. f l' \<noteq> f (Suc l')"
      by auto
    then obtain l' where
      l'_p: "l' \<ge> i \<and> f l' \<noteq> f (Suc l')"
      by metis
    then have "f l' > f (Suc l')"
      using leq le_eq_less_or_eq by auto
    moreover have "f i \<ge> f l'"
      using leq l'_p f_Suc_decr_f_decr by (induction l' arbitrary: i) auto
    ultimately show "\<exists>i' > i. f i' < f i"
      using l'_p less_le_trans by blast
  qed
  then obtain g_sm :: "nat \<Rightarrow> nat" where
    g_sm_p: "\<forall>i. g_sm i > i \<and> f (g_sm i) < f i"
    by metis

  define c :: "nat \<Rightarrow> nat" where
    "\<And>n. c n = compow n g_sm 0"

  have "f (c i) > f (c (Suc i))" for i
    by (induction i) (auto simp: c_def g_sm_p)
  then have "\<forall>i. (f \<circ> c) i > (f \<circ> c) (Suc i)"
    by auto
  then have "\<exists>fc :: nat \<Rightarrow> nat. \<forall>i. fc i > fc (Suc i)"
    by metis
  then show False
    using wf_less_than by (simp add: wf_iff_no_infinite_down_chain)
qed

(* FIXME: move to Multiset_More *)
lemma subseteq_mset_size_eql: "X \<subseteq># Y \<Longrightarrow> size Y = size X \<Longrightarrow> X = Y"
  using mset_subset_size subset_mset_def by fastforce

lemma strictly_subsumes_has_minimum:
  assumes "CC \<noteq> {}"
  shows "\<exists>C \<in> CC. \<forall>D \<in> CC. \<not> strictly_subsumes D C"
proof (rule ccontr)
  assume "\<not> (\<exists>C \<in> CC. \<forall>D\<in>CC. \<not> strictly_subsumes D C)"
  then have "\<forall>C \<in> CC. \<exists>D \<in> CC. strictly_subsumes D C"
    by blast
  then obtain f where f_p: "\<forall>C \<in> CC. f C \<in> CC \<and> strictly_subsumes (f C) C"
    by metis
  from assms obtain C where C_p: "C \<in> CC"
    by auto

  define c :: "nat \<Rightarrow> 'a clause" where
    "\<And>n. c n = compow n f C"

  have incc: "c i \<in> CC" for i
    by (induction i) (auto simp: c_def f_p C_p)
  have ps: "\<forall>i. strictly_subsumes (c (Suc i)) (c i)"
    using incc f_p unfolding c_def by auto
  have "\<forall>i. size (c i) \<ge> size (c (Suc i))"
    using ps unfolding strictly_subsumes_def subsumes_def by (metis size_mset_mono size_subst)
  then have lte: "\<forall>i. (size o c) i \<ge> (size o c) (Suc i)"
    unfolding comp_def .
  then have "\<exists>l. \<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    using f_Suc_decr_eventually_const comp_def by auto
  then obtain l where l_p: "\<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    by metis
  then have "\<forall>l' \<ge> l. proper_instance_of  (c (Suc l')) (c l')"
    using ps unfolding proper_instance_of_def instance_of_def
    by (metis size_subst strictly_subsumes_def subseteq_mset_size_eql subsumes_def proper_neq)
  then have "\<forall>i. proper_instance_of (c (Suc i + l)) (c (i + l))"
    unfolding proper_instance_of_def instance_of_def by auto
  then have "\<exists>f. \<forall>i. proper_instance_of (f (Suc i)) (f i)"
    by meson
  then show False
    using proper_instance_of_wf wf_iff_no_infinite_down_chain[of "{(x,y). proper_instance_of x y}"]
    unfolding wfP_def by auto
qed

lemma strictly_subsumes_well_founded: "wfP strictly_subsumes"
  using strictly_subsumes_has_minimum by (metis empty_iff wfP_eq_minimal)

lemma from_Q_to_Q_inf:
  assumes
    deriv: "chain (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and
    c: "C \<in> limit_llist Ns - src.Rf (limit_llist Ns)" and
    d: "D \<in> Q_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "D \<in> Q_of_state (limit_state Sts)"
proof -
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using limit_llist_grounding_of_state_ground ns by auto

  have derivns: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C"
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl)
      ultimately have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover have "is_ground_subst \<tau>"
        using \<tau>_p by auto
      moreover have "D \<in> clss_of_state (lnth Sts i)"
        using d Q_of_state_subset by auto
      ultimately have "C \<in> src.Rf (grounding_of_state (lnth Sts i))"
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"] by auto
      then have "C \<in> src.Rf (Sup_llist Ns)"
        using d ns by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist src.Rf_mono)
      then have "C \<in> src.Rf (limit_llist Ns)"
        unfolding ns using local.src_ext.Rf_Sup_llist_subset_Rf_limit_llist derivns ns by auto
      then show False
        using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
      using ground_C by (metis make_single_ground_subst subset_mset.order_refl)
    then show ?thesis
      by auto
  qed
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from deriv have four_ten: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation ns by auto

  have in_Sts_in_Sts_Suc:
    "\<forall>l \<ge> i. enat (Suc l) < llength Sts \<longrightarrow> D \<in> Q_of_state (lnth Sts l) \<longrightarrow> D \<in> Q_of_state (lnth Sts (Suc l))"
  proof (rule, rule, rule, rule)
    fix l
    assume len: "i \<le> l"
    assume llen: "enat (Suc l) < llength Sts"
    assume d_in_q: "D \<in> Q_of_state (lnth Sts l)"

    have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
      using llen deriv chain_lnth_rel by blast
    then show "D \<in> Q_of_state (lnth Sts (Suc l))"
    proof (induction rule: resolution_prover.cases)
      case (backward_subsumption_Q N D_removed P Q)
      moreover
      {
        assume "D_removed = D"
        then obtain D_subsumes where D_subsumes_p: "D_subsumes \<in> N \<and> strictly_subsumes D_subsumes D"
          using backward_subsumption_Q by auto
        moreover
        from D_subsumes_p have "subsumes D_subsumes C"
          using d subsumes_trans unfolding strictly_subsumes_def by blast
        moreover
        from backward_subsumption_Q have "D_subsumes \<in> clss_of_state (sup_state Sts)"
          using D_subsumes_p llen
          by (metis (no_types) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist rev_subsetD sup_state_def)
        ultimately
        have False
          using d_least unfolding subsumes_def by auto
      }
      ultimately show ?case
        using d_in_q by auto
    next
      case (backward_reduction_Q N L \<sigma> D' P Q)
      {
        assume "D' + {#L#} = D"
        then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
          using subset_strictly_subsumes[of D' D] backward_reduction_Q by auto
        then have subc: "subsumes D' C"
          using d(3) subsumes_trans unfolding strictly_subsumes_def by auto
        from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
          using llen
          by (metis (no_types, lifting) UnI1 clss_of_state_def P_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist subsetCE sup_ge2 sup_state_def)
        then have False using d_least D'_p subc by auto
      }
      then show ?case
        using backward_reduction_Q d_in_q by auto
    qed (use d_in_q in auto)
  qed
  have D_in_Sts: "D \<in> Q_of_state (lnth Sts l)" and D_in_Sts_Suc: "D \<in> Q_of_state (lnth Sts (Suc l))"
    if l_i: \<open>l \<ge> i\<close> and enat: \<open>enat (Suc l) < llength Sts\<close> for l
  proof -
    show \<open>D \<in> Q_of_state (lnth Sts l)\<close>
      using that
      apply (induction "l-i" arbitrary: l)
      subgoal using d by auto
      subgoal using d(1) in_Sts_in_Sts_Suc
        by (metis (no_types, lifting) Suc_ile_eq add_Suc_right add_diff_cancel_left' le_SucE
            le_Suc_ex less_imp_le)
      done
    then show "D \<in> Q_of_state (lnth Sts (Suc l))"
      using that in_Sts_in_Sts_Suc by blast
  qed
  have "i \<le> x \<Longrightarrow> enat x < llength Sts \<Longrightarrow> D \<in> Q_of_state (lnth Sts x)" for x
    apply (cases x)
    subgoal using d(1) by (auto intro!: exI[of _ i] simp: less_Suc_eq)
    subgoal for x'
      using d(1) D_in_Sts_Suc[of x'] by (cases \<open>i \<le> x'\<close>) (auto simp: not_less_eq_eq)
    done
  then have "D \<in> limit_llist (lmap Q_of_state Sts)"
    unfolding limit_llist_def by (auto intro!: exI[of _ i] simp: d)
  then show ?thesis
    unfolding limit_state_def by auto
qed

lemma from_P_to_Q:
  assumes
    deriv: "chain (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and
    c: "C \<in> limit_llist Ns - src.Rf (limit_llist Ns)" and
    d: "D \<in> P_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "\<exists>l. D \<in> Q_of_state (lnth Sts l) \<and> enat l < llength Sts"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using limit_llist_grounding_of_state_ground ns by auto

  have derivns: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C"
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C
        by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl)
      ultimately
      have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover
      have "is_ground_subst \<tau>" using \<tau>_p by auto
      moreover
      have "D \<in> clss_of_state (lnth Sts i)"
        using d P_of_state_subset by auto
      ultimately
      have "C \<in> src.Rf (grounding_of_state (lnth Sts i))"
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"]
        by auto
      then have "C \<in> src.Rf (Sup_llist Ns)"
        using d ns
        by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist src.Rf_mono)
      then have "C \<in> src.Rf (limit_llist Ns)"
        unfolding ns using local.src_ext.Rf_Sup_llist_subset_Rf_limit_llist derivns ns by auto
      then show False using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
      using ground_C
      by (metis make_single_ground_subst subset_mset.order_refl)
    then show ?thesis by auto
  qed
  then obtain \<sigma> where \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from deriv have four_ten: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation ns by auto

  have "\<exists>l. D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_deleted_P d unfolding ns by auto
  then obtain l where l_p: "D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    by auto
  then have l_Ns: "enat (Suc l) < llength Ns"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using chain_lnth_rel by auto
  then show ?thesis
  proof (induction rule: resolution_prover.cases)
    case (tautology_deletion A D_twin N P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (forward_subsumption P Q D_twin N)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (backward_subsumption_P N D_twin P Q)
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P" "?Ps l = P \<union> {D_twin}" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then obtain D' where D'_p: "strictly_subsumes D' D \<and> D' \<in> N"
      using backward_subsumption_P by auto
    then have subc: "subsumes D' C"
      unfolding strictly_subsumes_def subsumes_def using \<sigma>
      by (metis subst_cls_comp_subst subst_cls_mono_mset)
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
      unfolding twins(2)[symmetric] using l_p
      by (metis (no_types, lifting) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist subsetCE sup_state_def)
    then have False using d_least D'_p subc by auto
    then show ?case
      by auto
  next
    case (backward_subsumption_Q N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (forward_reduction P Q L \<sigma> D_twin N)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (backward_reduction_P N L \<sigma> D' P Q)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P \<union> {D'}" "?Ps l = P \<union> {D' + {#L#}}" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
      using subset_strictly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding strictly_subsumes_def by auto
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
       using l_p
       by (metis (no_types, lifting) UnI1 clss_of_state_def P_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist subsetCE sup_ge2 sup_state_def)
    then have False using d_least D'_p subc by auto
    then show ?case
      by auto
  next
    case (backward_reduction_Q N L \<sigma> D_twin P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (clause_processing N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (inference_computation N Q D_twin P)
    then have twins: "D_twin = D" "?Ps (Suc l) = P" "?Ps l = P \<union> {D_twin}" "?Qs (Suc l) = Q \<union> {D_twin}" "?Qs l = Q"
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p by auto
  qed
qed

lemma variants_sym: "variants D D' \<longleftrightarrow> variants D' D"
  unfolding variants_def by auto

lemma variants_size: "variants D D' \<Longrightarrow> size D = size D'"
  by (metis strictly_subsumes_def size_subst subset_mset_def subset_subst_strictly_subsumes
      subsumes_def variants_def)

lemma variants_eql_mod_two_subtitution: "variants D D' \<Longrightarrow> (\<exists>\<sigma>. D \<cdot> \<sigma> = D') \<and> (\<exists>\<sigma>'. D' \<cdot> \<sigma>' = D)"
  unfolding variants_def subsumes_def
  by (meson strictly_subsumes_def subset_mset_def subset_subst_strictly_subsumes subsumes_def)

lemma properly_subsume_variants:
  assumes "strictly_subsumes E D"
  assumes "variants D D'"
  shows "strictly_subsumes E D'"
proof -
  from assms obtain \<sigma> \<sigma>' where
    \<sigma>_\<sigma>'_p: "D \<cdot> \<sigma> = D' \<and> D' \<cdot> \<sigma>' = D"
    using variants_eql_mod_two_subtitution by metis

  from assms obtain \<sigma>'' where
    "E \<cdot> \<sigma>'' \<subseteq># D"
    unfolding strictly_subsumes_def subsumes_def by auto
  then have "E \<cdot> \<sigma>'' \<cdot> \<sigma> \<subseteq># D \<cdot> \<sigma>"
    using subst_cls_mono_mset by blast
  then have "E \<cdot> (\<sigma>'' \<odot> \<sigma>)  \<subseteq># D'"
    using \<sigma>_\<sigma>'_p by auto
  moreover from assms have n: "(\<nexists>\<sigma>. D \<cdot> \<sigma> \<subseteq># E)"
    unfolding strictly_subsumes_def subsumes_def by auto
  have "(\<nexists>\<sigma>. D' \<cdot> \<sigma> \<subseteq># E)"
  proof
    assume "\<exists>\<sigma>'''. D' \<cdot> \<sigma>''' \<subseteq># E"
    then obtain \<sigma>''' where "D' \<cdot> \<sigma>''' \<subseteq># E"
      by auto
    then have "D \<cdot> \<sigma> \<cdot> \<sigma>''' \<subseteq># E"
      using \<sigma>_\<sigma>'_p by auto
    then have "D \<cdot> (\<sigma> \<odot> \<sigma>''') \<subseteq># E"
      by auto
    then show False
      using n by metis
  qed
  ultimately show ?thesis
    unfolding strictly_subsumes_def subsumes_def by metis
qed

lemma neg_properly_subsume_variants:
  assumes "\<not> strictly_subsumes E D" and "variants D D'"
  shows "\<not> strictly_subsumes E D'"
  using assms properly_subsume_variants variants_sym by auto

lemma from_N_to_P_or_Q:
  assumes
    deriv: "chain (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts" and
    c: "C \<in> limit_llist Ns - src.Rf (limit_llist Ns)" and
    d: "D \<in> N_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "\<exists>l D' \<sigma>'. D' \<in> P_of_state (lnth Sts l) \<union> Q_of_state (lnth Sts l) \<and> enat l < llength Sts \<and> (\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D') \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>' \<and> subsumes D' C"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using limit_llist_grounding_of_state_ground ns by auto

  have derivns: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof -
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C"
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover
      from d(3) obtain \<tau>_proto where "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
        by blast
      then obtain \<tau> where \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl)
      ultimately have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover have "is_ground_subst \<tau>"
        using \<tau>_p by auto
      moreover have "D \<in> clss_of_state (lnth Sts i)"
        using d N_of_state_subset by auto
      ultimately have "C \<in> src.Rf (grounding_of_state (lnth Sts i))"
        using strict_subsumption_redundant_state[of D \<tau> C "lnth Sts i"] by auto
      then have "C \<in> src.Rf (Sup_llist Ns)"
        using d ns
        by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist src.Rf_mono)
      then have "C \<in> src.Rf (limit_llist Ns)"
        unfolding ns using local.src_ext.Rf_Sup_llist_subset_Rf_limit_llist derivns ns by auto
      then show False
        using c by auto
    qed
    then obtain \<sigma> where
      "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
      using ground_C by (metis make_single_ground_subst subset_mset.order_refl)
    then show ?thesis
      by auto
  qed
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from c have no_taut: "\<not> (\<exists>A. Pos A \<in># C \<and> Neg A \<in># C)"
    using src.tautology_redundant by auto

  from deriv have four_ten: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation ns by auto

  have "\<exists>l. D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_deleted d unfolding ns by auto
  then obtain l where
    l_p: "D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    by auto
  then have l_Ns: "enat (Suc l) < llength Ns"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using chain_lnth_rel by auto
  then show ?thesis
  proof (induction rule: resolution_prover.cases)
    case (tautology_deletion A D_twin N P Q)
    then have "D_twin = D"
      using l_p by auto
    then have "Pos (A \<cdot>a \<sigma>) \<in># C \<and> Neg (A \<cdot>a \<sigma>) \<in># C"
      using tautology_deletion(3,4) \<sigma>
      by (metis Melem_subst_cls eql_neg_lit_eql_atm eql_pos_lit_eql_atm)
    then have False
      using no_taut by metis
    then show ?case
      by blast
  next
    case (forward_subsumption P Q D_twin N)
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D_twin}"  "?Ps (Suc l) = P " "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    from forward_subsumption obtain D' where D'_p: "D' \<in> P \<union> Q \<and> subsumes D' D"
      using twins by auto
    then have subs: "subsumes D' C"
      using d(3) subsumes_trans by auto
    moreover have "D' \<in> clss_of_state (sup_state Sts)"
      using twins D'_p l_p unfolding clss_of_state_def sup_state_def
      by simp (metis (no_types) contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist)
    ultimately have "\<not> strictly_subsumes D' D"
      using d_least by auto
    then have "subsumes D D'"
      unfolding strictly_subsumes_def using D'_p by auto
    then have v: "variants D D'"
      using D'_p unfolding variants_def by auto
    then have mini: "\<forall>E \<in> {E \<in> clss_of_state (sup_state Sts). subsumes E C}. \<not> strictly_subsumes E D'"
      using d_least D'_p neg_properly_subsume_variants[of _ D D'] by auto

    from v have "\<exists>\<sigma>'. D' \<cdot> \<sigma>' = C"
      using \<sigma> variants_eql_mod_two_subtitution[of D D'] by simp (metis subst_cls_comp_subst)
    then have "\<exists>\<sigma>'. D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using ground_C by (meson make_single_ground_subst subset_mset.dual_order.refl)
    then obtain \<sigma>' where \<sigma>'_p: "D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      by metis

    show ?case
      using D'_p twins l_p subs mini \<sigma>'_p by auto
  next
    case (backward_subsumption_P N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (backward_subsumption_Q N D_twin P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (forward_reduction P Q L \<sigma> D' N)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N \<union> {D'}" "?Ns l = N \<union> {D' + {#L#}}"  "?Ps (Suc l) = P " "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ns (Suc l)"
      using subset_strictly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding strictly_subsumes_def by blast
    from D'_p have "D' \<in> clss_of_state (sup_state Sts)"
       using l_p
       by (metis (no_types, lifting) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist subsetCE sup_state_def)
    then have False
      using d_least D'_p subc by auto
    then show ?case
      by auto
  next
    case (backward_reduction_P N L \<sigma> D' P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (backward_reduction_Q N L \<sigma> C P Q)
    then have False
      using l_p by auto
    then show ?case
      by auto
  next
    case (clause_processing N D_twin P Q)
    then have twins:  "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D}"  "?Ps (Suc l) = P \<union> {D}" "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p d_least by blast
  next
    case (inference_computation N Q C P)
    then have False
      using l_p by auto
    then show ?case
      by auto
  qed
qed

lemma eventually_in_Qinf:
  assumes
    D_p: "D \<in> clss_of_state (sup_state Sts)"
      "subsumes D C" "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D" and
    fair: "fair_state_seq Sts" and
    (* We could also, we guess, in this proof obtain a D with property D_p(3) from one with only properties D_p(2,3). *)
    ns: "Ns = lmap grounding_of_state Sts" and
    c: "C \<in> limit_llist Ns - src.Rf (limit_llist Ns)" and
    ground_C: "is_ground_cls C"
  shows "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  from D_p obtain i where
    i_p: "i < llength Sts" "D \<in> ?Ns i \<or> D \<in> ?Ps i \<or> D \<in> ?Qs i"
    unfolding clss_of_state_def sup_state_def
    by simp_all (metis (no_types) in_Sup_llist_in_nth llength_lmap lnth_lmap)

  have derivns: "chain src_ext.derive Ns" using resolution_prover_ground_derivation deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
  proof - (* copy paste *)
    have "\<exists>\<sigma>. D \<cdot> \<sigma> = C"
    proof (rule ccontr)
      assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
      moreover from D_p obtain \<tau>_proto where
        "D \<cdot> \<tau>_proto \<subseteq># C"
        unfolding subsumes_def by blast
      then obtain \<tau> where
        \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
        using ground_C by (metis is_ground_cls_mono make_single_ground_subst subset_mset.order_refl)
      ultimately have subsub: "D \<cdot> \<tau> \<subset># C"
        using subset_mset.le_imp_less_or_eq by auto
      moreover have "is_ground_subst \<tau>"
        using \<tau>_p by auto
      moreover have "D \<in> clss_of_state (lnth Sts i)"
        using D_p N_of_state_subset
        by (meson contra_subsetD P_of_state_subset Q_of_state_subset i_p)
      ultimately have "C \<in> src.Rf (grounding_of_state (lnth Sts i))"
        using strict_subsumption_redundant_state by auto
      then have "C \<in> src.Rf (Sup_llist Ns)"
        using D_p ns src.Rf_mono
        by (metis (lifting) i_p(1) contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist)
      then have "C \<in> src.Rf (limit_llist Ns)"
        unfolding ns using local.src_ext.Rf_Sup_llist_subset_Rf_limit_llist derivns ns by auto
      then show False
        using c by auto
    qed
    then obtain \<sigma> where "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
      using ground_C by (metis make_single_ground_subst subset_mset.order_refl)
    then show ?thesis
      by auto
  qed
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by blast

  note i_p
  moreover
  {
    assume a: "D \<in> ?Ns i"
    then obtain D' \<sigma>' l where D'_p:
      "D' \<in> ?Ps l \<union> ?Qs l"
      "D' \<cdot> \<sigma>' = C"
      "enat l < llength Sts"
      "is_ground_subst \<sigma>'" (* Do I also need that l is later than i? Probably not. *)
      "\<forall>E \<in> {E. E \<in> (clss_of_state (sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D'"
      "subsumes D' C"
      using from_N_to_P_or_Q deriv fair ns c i_p(1) D_p(2) D_p(3) by blast
    then obtain l' where l'_p: "D' \<in> ?Qs l'" "l' < llength Sts" (* Do I also need that l is later than l'? Probably not*)
      using from_P_to_Q[OF deriv fair ns c _ D'_p(3) D'_p(6) D'_p(5)] by blast
    then have "D' \<in> Q_of_state (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns c _ l'_p(2)] D'_p by auto
    then have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D'_p by auto
  }
  moreover
  {
    assume a: "D \<in> ?Ps i"
    then obtain l' where l'_p: "D \<in> ?Qs l'" "l' < llength Sts" (* Do I also need that l is later than l'? Probably not*)
      using from_P_to_Q[OF deriv fair ns c a i_p(1) D_p(2) D_p(3) ] by auto
    then have "D \<in> Q_of_state (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns c l'_p(1) l'_p(2)] D_p(3) \<sigma>(1) \<sigma>(2) D_p(2) by auto
    then have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D_p \<sigma> by auto
  }
  moreover
  {
    assume a: "D \<in> ?Qs i"
    then have "D \<in> Q_of_state (limit_state Sts)"
      using from_Q_to_Q_inf[OF deriv fair ns c a i_p(1)] \<sigma> D_p(2,3) by auto
    then have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using D_p \<sigma> by auto
  }
  ultimately show "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    by auto
qed

text \<open>
The following corresponds to Lemma 4.11:
\<close>

lemma fair_imp_limit_minus_Rf_subset_ground_limit_state:
  assumes
    deriv: "chain (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "limit_llist Ns - src.Rf (limit_llist Ns) \<subseteq> grounding_of_state (limit_state Sts)"
proof
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  fix C
  assume C_p: "C \<in> limit_llist Ns - src.Rf (limit_llist Ns)"
  then have "C \<in> Sup_llist Ns"
    using limit_llist_subset_Sup_llist[of Ns] by blast
  then obtain D_proto where "D_proto \<in> clss_of_state (sup_state Sts) \<and> subsumes D_proto C"
    using in_Sup_llist_in_sup_state unfolding ns subsumes_def by blast
  then obtain D where
    D_p: "D \<in> clss_of_state (sup_state Sts)"
    "subsumes D C"
    "\<forall>E \<in> {E. E \<in> clss_of_state (sup_state Sts) \<and> subsumes E C}. \<not> strictly_subsumes E D"
    using strictly_subsumes_has_minimum[of "{E. E \<in> clss_of_state (sup_state Sts) \<and> subsumes E C}"]
    by auto

  have ground_C: "is_ground_cls C"
    using C_p using limit_llist_grounding_of_state_ground ns by auto

  have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    using eventually_in_Qinf[of D C Ns] using D_p(1) D_p(2) D_p(3) fair ns C_p ground_C by auto
  then obtain D' \<sigma>' where
    D'_p: "D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    by blast
  then have "D' \<in> clss_of_state (limit_state Sts)"
    by (simp add: clss_of_state_def)
  then show "C \<in> grounding_of_state (limit_state Sts)"
    unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def using D'_p by auto
qed

text \<open>
The following corresponds to (one direction of) Theorem 4.13:
\<close>

(* FIXME: move me *)
lemma ground_max_ground: "AA \<noteq> {} \<Longrightarrow> finite AA \<Longrightarrow> is_ground_atms AA \<Longrightarrow> is_ground_atm (Max AA)"
  unfolding is_ground_atms_def by auto

lemma ground_subclauses:
  assumes
    "\<forall>i < length CAi1. CAi1 ! i = Ci ! i + poss (Aij ! i)" and
    "length Ci = length CAi1" and
    "is_ground_cls_list CAi1"
  shows "is_ground_cls_list Ci"
  unfolding is_ground_cls_list_def
  by (metis assms in_set_conv_nth is_ground_cls_list_def is_ground_cls_union)

lemma subseteq_limit_state_eventually_always:
  fixes CC
  assumes
    "finite CC" and
    "CC \<noteq> {}" and
    "CC \<subseteq> Q_of_state (limit_state Sts)"
  shows "\<exists>j. enat j < llength Sts \<and> (\<forall>j' \<ge> enat j. j' < llength Sts \<longrightarrow> CC \<subseteq> Q_of_state (lnth Sts j'))"
proof -
  from assms(3) have "\<forall>C \<in> CC. \<exists>j. enat j < llength Sts \<and> (\<forall>j' \<ge> enat j. j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j'))"
    unfolding limit_state_def limit_llist_def by force
  then obtain f where f_p: "\<forall>C \<in> CC. f C < llength Sts \<and> (\<forall>j' \<ge> enat (f C). j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j')) "
    by moura

  define j :: nat where
    "j = Max (f ` CC)"

  have "enat j < llength Sts"
    unfolding j_def using f_p assms(1) apply auto
    by (metis (mono_tags, lifting) Max_in assms(2) finite_imageI imageE image_is_empty)
  moreover
  have "\<forall>C j'. C \<in> CC \<longrightarrow> enat j \<le> j' \<longrightarrow> j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j')"
  proof (intro allI impI)
    fix C :: "'a clause" and j' :: "nat"
    assume a: "C \<in> CC" "enat j \<le> enat j'" "enat j' < llength Sts"
    then have "f C \<le> j'"
      unfolding j_def using assms(1) Max.bounded_iff by auto
    then have "enat (f C) \<le> enat j'"
      by auto
    then show "C \<in> Q_of_state (lnth Sts j')"
      using f_p a by auto
  qed
  ultimately have "enat j < llength Sts \<and> (\<forall>j' \<ge> enat j. j' < llength Sts \<longrightarrow> CC \<subseteq> Q_of_state (lnth Sts j'))"
    by auto
  then show ?thesis
    by auto
qed

lemma empty_in_limit_state:
  assumes
    empty_in: "{#} \<in> limit_llist (lmap grounding_of_state Sts)" and
    fair: "fair_state_seq Sts" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "{#} \<in> clss_of_state (limit_state Sts)"
proof -
  from empty_in have in_limit_not_Rf: "{#} \<in> limit_llist Ns - src.Rf (limit_llist Ns)"
    unfolding ns src.Rf_def by auto

  from assms obtain i where
    i_p: "enat i < llength (lmap grounding_of_state Sts)"
    "{#} \<in> lnth (lmap grounding_of_state Sts) i"
    unfolding limit_llist_def by force
  then have "{#} \<in> grounding_of_state (lnth Sts i)"
    by auto
  then have "{#} \<in> clss_of_state (lnth Sts i)"
    unfolding grounding_of_clss_def grounding_of_cls_def by auto
  then have in_sup_state: "{#} \<in> clss_of_state (sup_state Sts)"
    using i_p(1) unfolding sup_state_def clss_of_state_def
    by simp (metis llength_lmap lnth_lmap lnth_subset_Sup_llist set_mp)
  then have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (limit_state Sts) \<and> D' \<cdot> \<sigma>' = {#} \<and> is_ground_subst \<sigma>'"
    using eventually_in_Qinf[of "{#}" "{#}" Ns, OF in_sup_state _ _ fair ns in_limit_not_Rf]
    unfolding is_ground_cls_def strictly_subsumes_def subsumes_def by simp
  then have "{#} \<in> Q_of_state (limit_state Sts)"
    by simp
  then show ?thesis
    unfolding limit_state_def clss_of_state_def by simp
qed

theorem completeness:
  assumes
    selection_renaming_invariant: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" and
    deriv: "chain (op \<leadsto>) Sts" and
    fair: "fair_state_seq Sts" and
    unsat: "\<not> satisfiable (grounding_of_state (limit_state Sts))" and
    ns: "Ns = lmap grounding_of_state Sts"
  shows "{#} \<in> clss_of_state (limit_state Sts)"
proof -
  let ?N = "\<lambda>i. grounding_of_state (lnth Sts i)"

  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  define \<Gamma>x :: "'a inference set" where
    "\<Gamma>x = undefined"
  define Rf :: "'a clause set \<Rightarrow> 'a clause set" where
    "Rf = standard_redundancy_criterion.Rf"
  define derive :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" where
    "derive = redundancy_criterion.derive \<Gamma>x Rf"

  have SQinf: "clss_of_state (limit_state Sts) = limit_llist (lmap Q_of_state Sts)"
    using fair unfolding fair_state_seq_def limit_state_def clss_of_state_def by auto

  from fair deriv have "limit_llist Ns - src.Rf (limit_llist Ns) \<subseteq> grounding_of_state (limit_state Sts)"
    using fair_imp_limit_minus_Rf_subset_ground_limit_state ns by blast

  have derivns: "chain src_ext.derive Ns"
    using resolution_prover_ground_derivation deriv ns by auto

  {
    fix \<gamma> :: "'a inference"
    assume \<gamma>_p: "\<gamma> \<in> gd.ord_\<Gamma>"
    let ?Cs = "side_prems_of \<gamma>"
    let ?D = "main_prem_of \<gamma>"
    let ?E = "concl_of \<gamma>"
    assume a: "set_mset ?Cs \<union> {?D} \<subseteq> limit_llist (lmap grounding_of_state Sts) - src.Rf (limit_llist (lmap grounding_of_state Sts))"

    have ground_ground_limit: "is_ground_clss (limit_llist (lmap grounding_of_state Sts))"
      using limit_llist_grounding_of_state_ground unfolding is_ground_clss_def by auto (* TODO: instead of is_ground_clss_def MAKE a lemma like limit_llist_grounding_of_state_ground *)

    have gc: "is_ground_cls_mset ?Cs"
      using a ground_ground_limit is_ground_cls_mset_def is_ground_clss_def by auto

    have gd: "is_ground_cls ?D"
      using a grounding_ground singletonI ground_ground_limit
      by (simp add: limit_llist_grounding_of_state_ground)

    from \<gamma>_p obtain CAi1 where
      CAi1_p: "gd.ord_resolve CAi1 ?D ?E \<and> mset CAi1 = ?Cs"
      unfolding gd.ord_\<Gamma>_def by auto

    have DCAi1_in_ground_limit: "{?D} \<union> set CAi1 \<subseteq> grounding_of_clss (Q_of_state (limit_state Sts))"
      using a CAi1_p unfolding clss_of_state_def using fair unfolding fair_state_seq_def
      by (metis (no_types, lifting) Un_empty_left \<open>limit_llist Ns - src.Rf (limit_llist Ns) \<subseteq> grounding_of_state (limit_state Sts)\<close> a clss_of_state_def ns set_mset_mset subset_trans sup_commute)

    then have gc1: "is_ground_cls_list CAi1"
      using CAi1_p unfolding is_ground_cls_list_def by auto

    have ge: "is_ground_cls ?E"
    proof - (* turn in to a LEMMA? *)
      have a1: "atms_of ?E \<subseteq> (\<Union>C \<in> set CAi1. atms_of C) \<union> atms_of ?D"
        using \<gamma>_p gc gd gd.ord_resolve_atms_of_concl_subset[of "CAi1" "?D" "?E"] CAi1_p by auto
      {
        fix L :: "'a literal"
        assume "L \<in># concl_of \<gamma>"
        then have "atm_of L \<in> atms_of (concl_of \<gamma>)"
          by (meson atm_of_lit_in_atms_of)
        then have "is_ground_atm (atm_of L)"
          using a1 gc1 gd is_ground_cls_imp_is_ground_atm is_ground_cls_list_def by auto
      }
      then show ?thesis
        unfolding is_ground_cls_def is_ground_lit_def by simp
    qed

    from CAi1_p have "\<exists>\<sigma>. ord_resolve (S_M S (Q_of_state (limit_state Sts))) CAi1 ?D \<sigma> ?E"
    proof
      assume "gd.ord_resolve CAi1 ?D ?E"
      then show "\<exists>\<sigma>. ord_resolve (S_M S (Q_of_state (limit_state Sts))) CAi1 ?D \<sigma> ?E"
      proof (cases rule: gd.ord_resolve.cases)
        case (ord_resolve n Ci Aij Ai D)
        have a: "?D = D + negs (mset Ai)"
          using ord_resolve by simp
        have b: "?E = \<Union>#mset Ci + D"
          using ord_resolve by simp
        have c: "length CAi1 = n"
          using ord_resolve by simp
        have d: "length Ci = n"
          using ord_resolve by simp
        have e: "length Aij = n"
          using ord_resolve by simp
        have f: "length Ai = n"
          using ord_resolve by simp
        have g: "n \<noteq> 0"
          using ord_resolve by simp
        have h: "\<forall>i<n. CAi1 ! i = Ci ! i + poss (Aij ! i)"
          using ord_resolve by simp
        have i: "\<forall>i<n. Aij ! i \<noteq> {#}"
          using ord_resolve by simp

        have "length Aij = length Ai"
          using e f by auto
        have j: "\<forall>i<n. \<forall>A\<in>#Aij ! i. A = Ai ! i"
          using ord_resolve by simp
        then have "\<forall>i<n. \<forall>A\<in>#add_mset (Ai ! i) (Aij ! i). A = Ai ! i"
          using ord_resolve by simp
        then have "\<forall>i<n. card (set_mset (add_mset (Ai ! i) (Aij ! i))) \<le> Suc 0"
          using all_the_same by metis
        then have "\<forall>i<length Aij. card (set_mset (add_mset (Ai ! i) (Aij ! i))) \<le> Suc 0"
          using e by auto
        then have "\<forall>AA \<in> set (map2 add_mset Ai Aij). card (set_mset AA) \<le> Suc 0"
          using set_map2_ex[of Aij Ai add_mset, OF \<open>length Aij = length Ai\<close>]
          by auto
        then have "is_unifiers id_subst (set_mset ` set (map2 add_mset Ai Aij))"
          unfolding is_unifiers_def is_unifier_def
          by auto
        moreover have "finite (set_mset ` set (map2 add_mset Ai Aij))"
          by auto
        moreover have "\<forall>AA \<in> set_mset ` set (map2 add_mset Ai Aij). finite AA"
          by auto
        ultimately obtain \<sigma> where jj: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset Ai Aij))"
          using mgu_complete by metis

        have k: "gd.eligible Ai (D + negs (mset Ai))"
          using ord_resolve by simp
        have gci: "\<forall>i<n. is_ground_cls (Ci ! i)"
          using ord_resolve(8) ord_resolve(3,4) gc1
          using ground_subclauses[of CAi1 Ci Aij] unfolding is_ground_cls_list_def by auto
        have gai: "is_ground_atms (set Ai)"
          using ord_resolve(1) gd
          by (metis atms_of_negg is_ground_cls_union set_mset_mset is_ground_cls_is_ground_atms_atms_of)
        then have gai2: "is_ground_atm_mset (mset Ai)"
          unfolding is_ground_atm_mset_def is_ground_atms_def by auto
        have gai3: "is_ground_atm_list Ai"
          using gai is_ground_atm_list_def is_ground_atms_def by auto
        have gD: "is_ground_cls D"
          using gd ord_resolve by simp

        from f g have "atms_of D \<union> set Ai \<noteq> {}" "finite (atms_of D \<union> set Ai)"
          by auto
        then have "Max (atms_of D \<union> set Ai) \<in> atms_of D \<union> set Ai"
          using Max_in by metis
        then have is_ground_Max: "is_ground_atm (Max (atms_of D \<union> set Ai))"
          using gD gai2 is_ground_cls_imp_is_ground_atm unfolding is_ground_atm_mset_def by auto
        then have Max\<sigma>_is_Max: "\<forall>\<sigma>. Max (atms_of D \<union> set Ai) \<cdot>a \<sigma> = Max (atms_of D \<union> set Ai)"
          by auto

        from k have
          ann2: "(Max (atms_of D \<union> set Ai) \<cdot>a \<sigma>) =
            Max (atms_of D \<union> set Ai) \<and> (D \<cdot> \<sigma> + negs (mset Ai \<cdot>am \<sigma>)) = (D + negs (mset Ai))"
          unfolding gd.eligible.simps[simplified] using is_ground_Max using gai2 gD by auto

        have ann1: "maximal_in (Max (atms_of D \<union> set Ai)) (D + negs (mset Ai))"
          unfolding gd.eligible.simps[simplified] ann2
          unfolding maximal_in_def
          unfolding less_atm_iff
          using Max\<sigma>_is_Max
          using gai gD
          using ex_ground_subst
          apply simp
          apply clarify
          subgoal for B \<sigma>
            apply(rule_tac x = \<sigma> in exI)
            apply auto
             apply (metis Max_less_iff UnCI \<open>finite (atms_of D \<union> set Ai)\<close> equals0D infinite_growing is_ground_cls_imp_is_ground_atm is_ground_subst_atm)
            by (metis Max_less_iff UnCI \<open>finite (atms_of D \<union> set Ai)\<close> all_not_in_conv infinite_growing is_ground_atms_def is_ground_subst_atm)
          done
        from k have kk: "eligible (S_M S (Q_of_state (limit_state Sts))) \<sigma> Ai (D + negs (mset Ai))"
          unfolding gd.eligible.simps eligible.simps using ann1 ann2 by (auto simp: S_Q_def)

        have l: "\<forall>i<n. gd.str_maximal_in (Ai ! i) (Ci ! i)"
          using ord_resolve by simp
        then have ll: "\<forall>i<n. str_maximal_in (Ai ! i \<cdot>a \<sigma>) (Ci ! i \<cdot> \<sigma>)"
          unfolding gd.str_maximal_in_def
          using  gci gai gai2 g f e c d gai3 apply simp unfolding less_eq_atm_def less_atm_iff apply simp
          using ex_ground_subst
          apply clarify
          apply rule
          subgoal for \<sigma> i B
            apply(rule_tac x = \<sigma> in exI)
            apply (subgoal_tac "B \<cdot>a \<sigma> = B") (* This should have happened by itself. *)
             apply force
            using gci
            using is_ground_cls_imp_is_ground_atm is_ground_subst_atm apply blast
            done
          apply force
          done

        have m: "\<forall>i<n. S_Q (CAi1 ! i) = {#}"
          using ord_resolve by simp

        have gg: "is_ground_cls (\<Union>#mset Ci + D)"
          using gD gci b ge by auto
        show ?thesis
          using ord_resolve.intros[OF c d e f g h i jj kk ll _  ]  m a b gg
          unfolding S_Q_def
           by auto
      qed
    qed
    then obtain \<sigma> where sisisgma: "ord_resolve (S_M S (Q_of_state (limit_state Sts))) CAi1 ?D \<sigma> ?E"
      by auto
    then obtain \<eta>s' \<eta>' \<eta>2' CAi' DA' E' \<tau>' where s_p:
      "is_ground_subst \<eta>'"
      "is_ground_subst_list \<eta>s'"
      "is_ground_subst \<eta>2'"
      "ord_resolve_rename S CAi' DA' \<tau>' E'"
      "CAi' \<cdot>\<cdot>cl \<eta>s' = CAi1"
      "DA' \<cdot> \<eta>' = ?D"
      "E' \<cdot> \<eta>2' = ?E"
      "{DA'} \<union> set CAi' \<subseteq> Q_of_state (limit_state Sts)"
      using selection_renaming_invariant ord_resolve_rename_lifting[of S "Q_of_state (limit_state Sts)" CAi1 "?D" _ "?E", OF sisisgma selection_axioms _ DCAi1_in_ground_limit]
      by smt
    from this(8) have "\<exists>j. enat j < llength Sts \<and> ((set CAi') \<union> {DA'} \<subseteq> ?Qs j)"
      unfolding limit_llist_def
      using subseteq_limit_state_eventually_always[of "{DA'} \<union> set CAi'"]
      by auto
    then obtain j where j_p: "is_least (\<lambda>j. enat j < llength Sts \<and> ((set CAi') \<union> {DA'} \<subseteq> ?Qs j)) j"
      using least_exists[of "(\<lambda>j. enat j < llength Sts \<and> ((set CAi') \<union> {DA'} \<subseteq> ?Qs j))"] by force
    then have j_p': "enat j < llength Sts" "(set CAi') \<union> {DA'} \<subseteq> ?Qs j"
      unfolding is_least_def by auto
    then have jn0: "j \<noteq> 0" (* Since there are initially no clauses in Q *)
      using empty_Q0 using insert_subset by fastforce
    then have j_adds_CAi': "\<not> set CAi' \<union> {DA'} \<subseteq> ?Qs (j - 1)" "set CAi' \<union> {DA'} \<subseteq> ?Qs j"
      using j_p unfolding is_least_def
       apply (metis (no_types, hide_lams) One_nat_def Suc_diff_Suc Suc_ile_eq diff_diff_cancel diff_zero less_imp_le less_one neq0_conv zero_less_diff)
      using j_p'(2) by blast
    have "lnth Sts (j - 1) \<leadsto> lnth Sts j"
      using j_p'(1) jn0  deriv chain_lnth_rel[of _ _ "j - 1"] by force
    then obtain C' where C'_p:
      "?Ns (j - 1) = {}"
      "?Ps (j - 1) = ?Ps j \<union> {C'}"
      "?Qs j = ?Qs (j - 1) \<union> {C'}"
      "?Ns j = concls_of (ord_FO_resolution.inferences_between (?Qs (j - 1)) C')"
      "C' \<in> set CAi' \<union> {DA'}"
      "C' \<notin> ?Qs (j - 1)"
      using j_adds_CAi' by (induction rule: resolution_prover.cases) auto
    then have ihih: "(set CAi' \<union> {DA'}) - {C'} \<subseteq> ?Qs (j - 1)"
      using j_adds_CAi' by auto
    have "E' \<in> ?Ns j"
    proof -
      have "E' \<in> concls_of (ord_FO_resolution.inferences_between (Q_of_state (lnth Sts (j - 1))) C')"
        apply auto unfolding  infer_from_def ord_FO_\<Gamma>_def unfolding inference_system.inferences_between_def
        apply auto
        apply (rule_tac x = "Infer (mset CAi') DA' E'" in image_eqI)
         apply auto
        using s_p(4)
          apply auto[]
        unfolding infer_from_def apply auto[]
        using C'_p(3) j_p'(2) apply (metis (no_types, hide_lams)  One_nat_def Un_insert_left insert_iff insert_subset  sup.commute sup_bot.left_neutral)
        using j_adds_CAi'(2) C'_p apply auto
        done
      then show "E' \<in> ?Ns j"
        using C'_p(4) by auto
    qed
    then have "E' \<in> clss_of_state (lnth Sts j)"
      using N_of_state_subset j_p' by auto
    then have "?E \<in> grounding_of_state (lnth Sts j)"
      using s_p(7) s_p(3) unfolding grounding_of_clss_def grounding_of_cls_def by force
    then have "\<gamma> \<in> src.Ri (grounding_of_state (lnth Sts j))" (* Here I could also just use R4.  *)
      unfolding src_ext_Ri_def src.Ri_def
      using \<gamma>_p using gd.\<Gamma>_reductive
       apply simp
      apply (rule_tac x="{#?E#}" in exI)
       apply simp
      done
    then have "\<gamma> \<in> src_ext_Ri (?N j)"
      unfolding src_ext_Ri_def by auto
    then have "\<gamma> \<in> src_ext_Ri (Sup_llist (lmap grounding_of_state Sts))"
      using j_p' contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist src_ext.Ri_mono by metis
    then have "\<gamma> \<in> src_ext_Ri (limit_llist (lmap grounding_of_state Sts))"
      using src_ext.derivation_supremum_limit_llist_satisfiable[of Ns] derivns ns by blast
  }
  then have "src_ext.saturated_upto (limit_llist (lmap grounding_of_state Sts))"
    unfolding src_ext.saturated_upto_def src_ext.inferences_from_def
    using gd_ord_\<Gamma>_ngd_ord_\<Gamma>
    unfolding src_ext.saturated_upto_def src_ext.inferences_from_def infer_from_def src_ext_Ri_def
    by auto
  note continue_from_this = this

  have "limit_llist (lmap grounding_of_state Sts) \<supseteq> grounding_of_state (limit_state Sts)"
  proof
    fix C :: "'a clause"
    assume "C \<in> grounding_of_state (limit_state Sts)"
    then obtain D \<sigma> where D_\<sigma>_p: "D \<in> clss_of_state (limit_state Sts)" "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
      unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
    then have ii: "D \<in> limit_llist (lmap N_of_state Sts) \<or> D \<in> limit_llist (lmap P_of_state Sts) \<or> D \<in> limit_llist (lmap Q_of_state Sts)"
      unfolding clss_of_state_def  limit_state_def by simp
    then have "C \<in> limit_llist (lmap grounding_of_clss (lmap N_of_state Sts)) \<or>
      C \<in> limit_llist (lmap grounding_of_clss (lmap P_of_state Sts)) \<or>
      C \<in> limit_llist (lmap grounding_of_clss (lmap Q_of_state Sts))"
      apply -
      unfolding limit_llist_def grounding_of_clss_def grounding_of_cls_def
      apply (erule HOL.disjE)
      subgoal
        apply (rule disjI1)
        using D_\<sigma>_p apply auto
        done
      subgoal
        apply (erule HOL.disjE)
        subgoal
          apply (rule disjI2)
          apply (rule disjI1)
          using D_\<sigma>_p apply auto
          done
        subgoal
          apply (rule disjI2)
          apply (rule disjI2)
          using D_\<sigma>_p apply auto
          done
        done
      done
    then show "C \<in> limit_llist (lmap grounding_of_state Sts)"
      unfolding limit_llist_def clss_of_state_def grounding_of_clss_def by auto
  qed

  then have unsat2: "\<not> satisfiable (limit_llist (lmap grounding_of_state Sts))"
    using unsat unfolding true_clss_def by auto blast

  from continue_from_this have "src.saturated_upto (limit_llist (lmap grounding_of_state Sts))"
    using gd_ord_\<Gamma>_ngd_ord_\<Gamma> src.redudancy_criterion
      standard_redundancy_criterion_extension_saturated_up_iff[of gd.ord_\<Gamma>]
    unfolding src_ext_Ri_def by auto
  then have "{#} \<in> limit_llist (lmap grounding_of_state Sts)"
    using src.saturated_upto_refute_complete unsat2 by auto
  then show "{#} \<in> clss_of_state (limit_state Sts)"
    using empty_in_limit_state fair ns by auto
qed

end

end

end
