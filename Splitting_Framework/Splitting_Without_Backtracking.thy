(* Title:        Applications of the Splitting Framework to other architectures
 *               (Splitting without Backtracking)
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023 *)

theory Splitting_Without_Backtracking
  imports
    Main
    Splitting_Calculi
    Saturation_Framework_Extensions.FO_Ordered_Resolution_Prover_Revisited
    Saturation_Framework_Extensions.Clausal_Calculus
begin

subsection \<open>Splitting without Backtracking\<close>

text \<open>
  In this section, we show that \<open>O\<^sub>\<bbbP>\<close>, an ordered resolution calculus with parallel selection,
  is closely related to \<open>LA\<close>, an instance of our Splitting Framework @{locale splitting_calculus}
  augmented with the following simplification rule:

  \[ \mprset{fraction={===}
     \inferrule{\<open>C \<or> D \<leftarrow> A\<close>}{\<open>C \<leftarrow> A \<union> {a}\<close> \\ \<open>D \<leftarrow> A \<union> {\<not> a}\<close>}
     \;\textsc{BinSplit} 
  \]
  Note that this simplification rule is applicable only if \<open>a \<in> asn(C)\<close> and if \<open>C \<or> D\<close> is splittable
  into \<open>C, D\<close>. 

  Throughout this section, we will show that \<open>LA\<close> and \<open>O\<^sub>\<bbbP>\<close> basically share the same notion of
  entailment, that the redundancy criterion used in \<open>O\<^sub>\<bbbP>\<close> is stronger than the one used in \<open>LA\<close>, and
  that saturation w.r.t. \<open>LA\<close> implies saturation w.r.t. \<open>O\<^sub>\<bbbP>\<close>.
\<close>

text \<open>
  We start by defining \<open>LA\<close> as an instance of our locale @{locale splitting_calculus}.
\<close>

(* Quick comment here:
 * For our purpose, we need to add \<open>asn\<close> and \<open>fml\<close> as abstract bindings in the locale.
 * However, we also need to put the axioms of \<open>asn\<close> in the locale's assumptions, which needs
 * a disjunctive entailment.
 * Because we would like to use a disjunctive version of the one in @{locale FO_resolution_prover}
 * (specifically the first order one), we have to define this temporary locale, which contains
 * this entailment.
 * We will use it later in @{locale LA_calculus}, in the assumptions. *)
locale FO_resolution_prover' = FO_resolution_prover S subst_atm id_subst comp_subst renaming_aparts
  atm_of_atms mgu less_atm 
  for
    S :: \<open>('a :: wellorder) clause \<Rightarrow> 'a clause\<close> and 
    subst_atm :: \<open>'a \<Rightarrow> 's \<Rightarrow> 'a\<close> and 
    id_subst :: \<open>'s\<close> and 
    comp_subst :: \<open>'s \<Rightarrow> 's \<Rightarrow> 's\<close> and 
    renaming_aparts :: \<open>'a clause list \<Rightarrow> 's list\<close> and 
    atm_of_atms :: \<open>'a list \<Rightarrow> 'a\<close> and 
    mgu :: \<open>'a set set \<Rightarrow> 's option\<close> and 
    less_atm :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
begin

no_notation entails_clss (infix \<open>\<TTurnstile>e\<close> 50) 
notation entails_clss (infix \<open>\<TTurnstile>\<inter>e\<close> 50)

(* All this is taken from the file \<open>FO_Ordered_Resolution_Prover_Revisited.thy\<close>.
 * I don't like it, but I don't have a choice as I need access to these interpretations. *)
interpretation gr: ground_resolution_with_selection "S_M S M"
  using selection_axioms by unfold_locales (fact S_M_selects_subseteq S_M_selects_neg_lits)+

interpretation G: Soundness.sound_inference_system "G_Inf M" "{{#}}" "(\<TTurnstile>\<inter>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> G_Inf M"
  moreover
  {
    fix I
    assume I_ent_prems: "I \<TTurnstile>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve M CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding G_Inf_def by auto
    then have "I \<TTurnstile> concl_of \<iota>"
      using gr.ord_resolve_sound[of M CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_ent_prems G_Inf_have_prems i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>\<inter>e {concl_of \<iota>}"
    by simp
qed

interpretation G: clausal_counterex_reducing_inference_system "G_Inf M" "gr.INTERP M"
proof
  fix N D
  assume
    "{#} \<notin> N" and
    "D \<in> N" and
    "\<not> gr.INTERP M N \<TTurnstile> D" and
    "\<And>C. C \<in> N \<Longrightarrow> \<not> gr.INTERP M N \<TTurnstile> C \<Longrightarrow> D \<le> C"
  then obtain CAs AAs As E where
    cas_in: "set CAs \<subseteq> N" and
    n_mod_cas: "gr.INTERP M N \<TTurnstile>m mset CAs" and
    ca_prod: "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production M N CA \<noteq> {}" and
    e_res: "gr.ord_resolve M CAs D AAs As E" and
    n_nmod_e: "\<not> gr.INTERP M N \<TTurnstile> E" and
    e_lt_d: "E < D"
    using gr.ord_resolve_counterex_reducing by blast
  define \<iota> where
    "\<iota> = Infer (CAs @ [D]) E"

  have "\<iota> \<in> G_Inf M"
    unfolding \<iota>_def G_Inf_def using e_res by auto
  moreover have "prems_of \<iota> \<noteq> []"
    unfolding \<iota>_def by simp
  moreover have "main_prem_of \<iota> = D"
    unfolding \<iota>_def by simp
  moreover have "set (side_prems_of \<iota>) \<subseteq> N"
    unfolding \<iota>_def using cas_in by simp
  moreover have "gr.INTERP M N \<TTurnstile>s set (side_prems_of \<iota>)"
    unfolding \<iota>_def using n_mod_cas ca_prod by (simp add: gr.productive_imp_INTERP true_clss_def)
  moreover have "\<not> gr.INTERP M N \<TTurnstile> concl_of \<iota>"
    unfolding \<iota>_def using n_nmod_e by simp
  moreover have "concl_of \<iota> < D"
    unfolding \<iota>_def using e_lt_d by simp
  ultimately show "\<exists>\<iota> \<in> G_Inf M. prems_of \<iota> \<noteq> [] \<and> main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N \<and>
    gr.INTERP M N \<TTurnstile>s set (side_prems_of \<iota>) \<and> \<not> gr.INTERP M N \<TTurnstile> concl_of \<iota> \<and> concl_of \<iota> < D"
    by blast
qed

interpretation G: clausal_counterex_reducing_calculus_with_standard_redundancy "G_Inf M"
  "gr.INTERP M"
  using G_Inf_have_prems G_Inf_reductive
  by (unfold_locales) simp_all

interpretation G: Calculus.statically_complete_calculus "{{#}}" "G_Inf M" "(\<TTurnstile>\<inter>e)" "G.Red_I M" G.Red_F
  by unfold_locales (use G.clausal_saturated_complete in blast)

sublocale F: lifting_intersection F_Inf "{{#}}" UNIV G_Inf "\<lambda>N. (\<TTurnstile>\<inter>e)" G.Red_I "\<lambda>N. G.Red_F"
  "{{#}}" "\<lambda>N. \<G>_F" \<G>_I_opt "\<lambda>D C C'. False"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "Calculus.consequence_relation {{#}} (\<TTurnstile>\<inter>e)"
    by (fact consequence_relation_axioms)
next
  show "\<And>M. tiebreaker_lifting {{#}} F_Inf {{#}} (\<TTurnstile>\<inter>e) (G_Inf M) (G.Red_I M) G.Red_F \<G>_F (\<G>_I_opt M)
    (\<lambda>D C C'. False)"
  proof
    fix M \<iota>
    show "the (\<G>_I_opt M \<iota>) \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
      unfolding option.sel
    proof
      fix \<iota>'
      assume "\<iota>' \<in> \<G>_I M \<iota>"
      then obtain \<rho> \<rho>s where
        \<iota>': "\<iota>' = Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)" and
        \<rho>_gr: "is_ground_subst \<rho>" and
        \<rho>_infer: "Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> G_Inf M"
        unfolding \<G>_I_def by blast

      show "\<iota>' \<in> G.Red_I M (\<G>_F (concl_of \<iota>))"
        unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq using \<iota>' \<rho>_gr \<rho>_infer
        by (metis Calculus.inference.sel(2) G_Inf_reductive empty_iff ground_subst_ground_cls
            grounding_of_cls_ground insert_iff subst_cls_eq_grounding_of_cls_subset_eq
            true_clss_union)
    qed
  qed (auto simp: \<G>_F_def ex_ground_subst)
qed

notation F.entails_\<G> (infix "\<TTurnstile>\<inter>\<G>e" 50)

lemma F_entails_\<G>_iff: "N1 \<TTurnstile>\<inter>\<G>e N2 \<longleftrightarrow> \<Union> (\<G>_F ` N1) \<TTurnstile>\<inter>e \<Union> (\<G>_F ` N2)"
  unfolding F.entails_\<G>_def by simp

lemma true_Union_grounding_of_cls_iff:
  "I \<TTurnstile>s (\<Union>C \<in> N. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s N \<cdot>cs \<sigma>)"
  unfolding true_clss_def subst_clss_def by blast

sublocale F: sound_inference_system F_Inf "{{#}}" "(\<TTurnstile>\<inter>\<G>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> F_Inf"
  moreover
  {
    fix I \<eta>
    assume
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s set (prems_of \<iota>) \<cdot>cs \<sigma>" and
      \<eta>_gr: "is_ground_subst \<eta>"
    obtain CAs AAs As \<sigma> where
      the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>) AAs As \<sigma> (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding F_Inf_def by auto
    have prems: "mset (prems_of \<iota>) = mset (side_prems_of \<iota>) + {#main_prem_of \<iota>#}"
      by (metis (no_types) F_Inf_have_prems[OF i_in] add.right_neutral append_Cons append_Nil2
          append_butlast_last_id mset.simps(2) mset_rev mset_single_iff_right rev_append
          rev_is_Nil_conv union_mset_add_mset_right)
    have "I \<TTurnstile> concl_of \<iota> \<cdot> \<eta>"
      using ord_resolve_rename_sound[OF the_inf, of I \<eta>, OF _ \<eta>_gr]
      unfolding CAs prems[symmetric] using I_entails_prems
      by (metis set_mset_mset set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>\<inter>\<G>e {concl_of \<iota>}"
    unfolding F.entails_\<G>_def \<G>_F_def true_Union_grounding_of_cls_iff by auto
qed

interpretation F: Calculus.statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>\<inter>\<G>e)" F.Red_I_\<G>
  F.Red_F_\<G>_empty
proof (rule F.stat_ref_comp_to_non_ground_fam_inter; clarsimp; (intro exI)?)
  show "\<And>M. Calculus.statically_complete_calculus {{#}} (G_Inf M) (\<TTurnstile>\<inter>e) (G.Red_I M) G.Red_F"
    by (fact G.statically_complete_calculus_axioms)
next
  fix N
  assume "F.saturated N"
  show "F.ground.Inf_from_q N (\<Union> (\<G>_F ` N)) \<subseteq> {\<iota>. \<exists>\<iota>' \<in> F.Inf_from N. \<iota> \<in> \<G>_I N \<iota>'}
    \<union> G.Red_I N (\<Union> (\<G>_F ` N))"
    using G_Inf_overapprox_F_Inf unfolding F.ground.Inf_from_q_def \<G>_I_def by fastforce
qed

(********************************************************)
(****************** End of copy pasta *******************)
(********************************************************)  

(*<*)
lemma clause_union_entails_one: \<open>{C \<union># D} \<TTurnstile>\<inter>\<G>e {C} \<or> {C \<union># D} \<TTurnstile>\<inter>\<G>e {D}\<close>
  unfolding F.entails_\<G>_def \<G>_F_def
proof simp
  let ?subst = \<open>\<lambda> S. {S \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close>

  show \<open>?subst (C \<union># D) \<TTurnstile>\<inter>e ?subst C \<or> ?subst (C \<union># D) \<TTurnstile>\<inter>e ?subst D\<close>
    (* TODO: find how to prove that (holding back Th14) *) 
    sorry 
qed

lemma unsat_equiv2: \<open>\<not> satisfiable M \<longleftrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}}\<close>
proof -
  have \<open>\<forall> I. (\<forall> C \<in> M. I \<TTurnstile>s {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> I \<TTurnstile>s M\<close>
  proof (intro allI iffI ballI)
    fix I
    assume \<open>\<forall> C \<in> M. I \<TTurnstile>s {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close>
    then show \<open>I \<TTurnstile>s M\<close>
      sorry
  next
    fix I C
    assume \<open>I \<TTurnstile>s M\<close> and
           \<open>C \<in> M\<close> 
    then show \<open>I \<TTurnstile>s {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close>
      sorry
  qed
  then have
    \<open>(\<forall> I. (\<forall> C \<in> M. I \<TTurnstile>s {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}) \<longrightarrow> I \<TTurnstile>s {{#}}) \<longleftrightarrow> (\<forall> I. \<not> I \<TTurnstile>s M)\<close>
    by blast 
  then show ?thesis
    unfolding F.entails_\<G>_def \<G>_F_def
    using ex_ground_subst
    by simp 
qed

lemma unsat_equiv3: \<open>\<not> satisfiable (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  unfolding F.entails_\<G>_def \<G>_F_def
  using grounding_of_cls_def grounding_of_cls_empty
  by force

(*>*)

text \<open>
  @{const \<open>F.entails_\<G>\<close>} is a conjunctive entailment, meaning that for @{term \<open>M \<TTurnstile>\<inter>\<G>e N\<close>} to hold,
  each clause in \<open>N\<close> must be entailed by \<open>M\<close>.
  Unfortunately, this clashes with requirement (D3) @{thm consequence_relation.entails_subsets} of
  a splitting calculus.

  Therefore, we define a disjunctive version of this entailment by stating that \<open>M \<TTurnstile>\<union>\<G>e N\<close> iff
  there is some \<open>C \<in> N\<close> such that \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>.
  This definition is not quite enough because it does not capture (D1)
  @{thm consequence_relation.bot_entails_empty}.
  More specifically, if \<open>N\<close> is empty, then there does not exist a \<open>C \<in> N\<close>! But we know that
  \<open>M \<Turnstile>\<union>\<G>e {}\<close> if \<open>M\<close> is unsatisfiable.
  Hence \<open>M \<TTurnstile>\<union>\<G>e N\<close> if \<open>M\<close> is unsatisfiable, or there exists some \<open>C \<in> N\<close> such that \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>.

  Also note that @{abbrev \<open>entails_clss\<close>} is also a conjunctive entailment, so we also need to
  \<closedblquote>transform\<opendblquote> it to a disjunctive entailment using the same principle.
\<close>
(* There are a few ways to introduce unsatisfiability of a set of clauses:
 * - Use \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close>
 * - Use \<open>\<not> satisfiable M\<close>
 *
 * The first one makes it easy to prove that entailments coincide (see below). 
 * However, they should all be equivalent (as shown by @{thm unsat_equiv1} and @{thm unsat_equiv2}.
 * *)
definition entails_\<G>_disj :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix \<open>\<TTurnstile>\<union>\<G>e\<close> 50) where
  \<open>M \<TTurnstile>\<union>\<G>e N \<longleftrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}} \<or> (\<exists> C \<in> N. M \<TTurnstile>\<inter>\<G>e {C})\<close> 

text \<open>
  This is our own requirement: the two entailments must coincide on singleton sets.
  \<close> 

lemma entails_conj_is_entails_disj_on_singleton: \<open>M \<TTurnstile>\<inter>\<G>e {C} \<longleftrightarrow> M \<TTurnstile>\<union>\<G>e {C}\<close>
  using F.entails_def entails_\<G>_disj_def
  by force

(*<*)
lemma unsat_supsets: \<open>M \<TTurnstile>\<inter>\<G>e {{#}} \<Longrightarrow> M \<union> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  using F.entails_trans F.subset_entailed
  by blast

lemma entails_\<G>_disj_subsets: \<open>M' \<subseteq> M \<Longrightarrow> N' \<subseteq> N \<Longrightarrow> M' \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<TTurnstile>\<union>\<G>e N\<close>
  by (meson F.entails_trans F.subset_entailed entails_\<G>_disj_def subsetD true_clss_mono) 


lemma entails_\<G>_disj_cut: \<open>M \<TTurnstile>\<union>\<G>e N \<union> {C} \<Longrightarrow> M' \<union> {C} \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<union> M' \<TTurnstile>\<union>\<G>e N \<union> N'\<close>
proof -
  assume M_entails_N_u_C: \<open>M \<TTurnstile>\<union>\<G>e N \<union> {C}\<close> and
         M'_u_C_entails_N': \<open>M' \<union> {C} \<TTurnstile>\<union>\<G>e N'\<close>
  then consider
    (M_unsat) \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close> |
    (M'_u_C_unsat) \<open>M' \<union> {C} \<TTurnstile>\<inter>\<G>e {{#}}\<close> |
    (c) \<open>(\<exists> C' \<in> N \<union> {C}. M \<TTurnstile>\<inter>\<G>e {C'}) \<and> (\<exists> C' \<in> N'. M' \<union> {C} \<TTurnstile>\<inter>\<G>e {C'})\<close> 
    using entails_\<G>_disj_def
    by auto
  then show \<open>M \<union> M' \<TTurnstile>\<union>\<G>e N \<union> N'\<close>
  proof cases
    case M_unsat
    then show ?thesis
      using entails_\<G>_disj_def unsat_supsets
      by blast 
  next
    case M'_u_C_unsat
    then show ?thesis
      by (smt (z3) F_entails_\<G>_iff M_entails_N_u_C UN_Un Un_insert_right entails_\<G>_disj_def
          entails_\<G>_disj_subsets insert_iff sup_bot.right_neutral sup_ge1 true_clss_union) 
  next
    case c
    then obtain C1 and C2 where
      C1_in_N_u_C: \<open>C1 \<in> N \<union> {C}\<close> and
      M_entails_C1: \<open>M \<TTurnstile>\<inter>\<G>e {C1}\<close> and
      C2_in_N': \<open>C2 \<in> N'\<close> and
      M'_u_C_entails_C2: \<open>M' \<union> {C} \<TTurnstile>\<inter>\<G>e {C2}\<close>
      by blast 
    then show ?thesis
    proof (cases \<open>C1 = C\<close>) 
      case True
      then have \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>
        using M_entails_C1
        by blast
      then have \<open>M' \<union> M \<TTurnstile>\<inter>\<G>e M' \<union> {C}\<close>
        by (metis (no_types, lifting) F.entail_union F.entails_trans F.subset_entailed
            Un_upper1 Un_upper2)
      then have \<open>M \<union> M' \<TTurnstile>\<inter>\<G>e {C2}\<close>
        using F_entails_\<G>_iff M'_u_C_entails_C2
        by auto
      then show ?thesis
        using C2_in_N' entails_\<G>_disj_def
        by auto
    next
      case False
      then show ?thesis
        by (meson C1_in_N_u_C M_entails_C1 UnE entails_\<G>_disj_def entails_\<G>_disj_subsets equals0D
            insertE sup.cobounded1) 
    qed
  qed
qed 

lemma entails_\<G>_conj_compactness:
  \<open>M \<TTurnstile>\<inter>\<G>e N \<Longrightarrow> \<exists> M' N'. M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and> M' \<TTurnstile>\<inter>\<G>e N'\<close>
  using F.subset_entailed
  by blast

lemma entails_\<G>_disj_compactness:
  \<open>M \<TTurnstile>\<union>\<G>e N \<Longrightarrow> \<exists> M' N'. M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and> M' \<TTurnstile>\<union>\<G>e N'\<close>
  (* TODO: this is hard *)
proof -
  assume M_entails_N: \<open>M \<TTurnstile>\<union>\<G>e N\<close>
  then consider
    (M_unsat) \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close> |
    (b) \<open>\<exists> C \<in> N. M \<TTurnstile>\<inter>\<G>e {C}\<close>
    using entails_\<G>_disj_def
    by blast
  then show ?thesis
  proof cases 
    case M_unsat
    then have \<open>\<not> satisfiable (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
      using unsat_equiv3
      by presburger
    then have \<open>\<exists> M' \<subseteq> (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}). finite M' \<and> \<not> satisfiable M'\<close>
      by (meson gr.ord_\<Gamma>_sound_counterex_reducing.clausal_logic_compact)
    then obtain M' where
      M'_subset_of: \<open>M' \<subseteq> (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close> and
      finite_M': \<open>finite M'\<close> and
      M'_unsat: \<open>\<not> satisfiable M'\<close>
      by blast
    then have \<open>\<exists> M'' \<subseteq> M. finite M'' \<and> M'' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
      (* How? *) 
      sorry
    then show ?thesis
      using entails_\<G>_disj_def
      by auto
  next
    case b
    then obtain C where
      C_in_N: \<open>C \<in> N\<close> and
      M_entails_C: \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>
      by blast
    then have \<open>\<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e {C}\<close>
      (* How? *)
      unfolding F.entails_\<G>_def \<G>_F_def
      apply simp
       
      sorry 
    then show ?thesis
      by (metis (no_types, lifting) C_in_N empty_subsetI entails_conj_is_entails_disj_on_singleton
          finite.emptyI finite.insertI insert_subset) 
  qed
qed

lemma entails_\<G>_disj_cons_rel_ext: \<open>consequence_relation {#} (\<TTurnstile>\<union>\<G>e)\<close>
proof (standard)
  show \<open>{{#}} \<TTurnstile>\<union>\<G>e {}\<close>
    using F.subset_entailed entails_\<G>_disj_def
    by blast
  show \<open>\<And> C. {C} \<TTurnstile>\<union>\<G>e {C}\<close>
    by (meson F.subset_entailed dual_order.refl entails_conj_is_entails_disj_on_singleton)
  show \<open>\<And> M' M N' N. M' \<subseteq> M \<Longrightarrow> N' \<subseteq> N \<Longrightarrow> M' \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<TTurnstile>\<union>\<G>e N\<close>
    by (rule entails_\<G>_disj_subsets)
  show \<open>\<And> M N C M' N'. M \<TTurnstile>\<union>\<G>e N \<union> {C} \<Longrightarrow> M' \<union> {C} \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<union> M' \<TTurnstile>\<union>\<G>e N \<union> N'\<close>
    by (rule entails_\<G>_disj_cut)
  show \<open>\<And> M N. M \<TTurnstile>\<union>\<G>e N \<Longrightarrow> \<exists> M' N'. M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and> M' \<TTurnstile>\<union>\<G>e N'\<close>
    by (rule entails_\<G>_disj_compactness)
qed

sublocale entails_\<G>_disj_cons_rel: consequence_relation \<open>{#}\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  by (rule entails_\<G>_disj_cons_rel_ext)

notation entails_\<G>_disj_cons_rel.entails_neg (infix \<open>\<TTurnstile>\<union>\<G>e\<^sub>\<sim>\<close> 50) 

end (* locale FO_resolution_prover' *)



(* Since the set \<open>\<bbbP>\<close> is left unspecified, we cannot define \<open>fml\<close> nor \<open>asn\<close>.
 * Therefore, we keep them abstract and leave it to anybody instanciating this locale
 * to specify them. *)

locale LA_calculus = FO_resolution_prover' S subst_atm id_subst comp_subst renaming_aparts
  atm_of_atms mgu less_atm
  for
    S :: \<open>('a :: wellorder) clause \<Rightarrow> 'a clause\<close> and 
    subst_atm :: \<open>'a \<Rightarrow> 's \<Rightarrow> 'a\<close> and 
    id_subst :: \<open>'s\<close> and 
    comp_subst :: \<open>'s \<Rightarrow> 's \<Rightarrow> 's\<close> and 
    renaming_aparts :: \<open>'a clause list \<Rightarrow> 's list\<close> and 
    atm_of_atms :: \<open>'a list \<Rightarrow> 'a\<close> and 
    mgu :: \<open>'a set set \<Rightarrow> 's option\<close> and 
    less_atm :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> 
  + fixes
    asn :: \<open>'a clause sign \<Rightarrow> ('v :: countable) sign set\<close> and
    fml :: \<open>'v \<Rightarrow> 'a clause\<close>
  assumes
    asn_not_empty: \<open>asn C \<noteq> {}\<close> and
    fml_entails_C: \<open>a \<in> asn C \<Longrightarrow> {map_sign fml a} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C}\<close> and
    C_entails_fml: \<open>a \<in> asn C \<Longrightarrow> {C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {map_sign fml a}\<close> 
begin

interpretation entails_\<G>_disj_sound_inf_system:
  Preliminaries_With_Zorn.sound_inference_system F_Inf \<open>{#}\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
proof standard
  have \<open>\<And> \<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<inter>\<G>e {concl_of \<iota>}\<close>
    using F.sound
    by blast
  then show \<open>\<And> \<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<union>\<G>e {concl_of \<iota>}\<close>
    using entails_conj_is_entails_disj_on_singleton
    by blast
qed

interpretation LA_is_sound_calculus: sound_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.Red_I_\<G> F.Red_F_\<G>_empty
proof standard 
  show \<open>\<And> N. F.Red_I_\<G> N \<subseteq> F_Inf\<close>
    using F.Red_I_to_Inf
    by blast
  show \<open>\<And> N. N \<TTurnstile>\<union>\<G>e {{#}} \<Longrightarrow> N - F.Red_F_\<G>_empty N \<TTurnstile>\<union>\<G>e {{#}}\<close>
    using F.empty_ord.Red_F_Bot entails_conj_is_entails_disj_on_singleton
    by blast
  show \<open>\<And> N N'. N \<subseteq> N' \<Longrightarrow> F.Red_F_\<G>_empty N \<subseteq> F.Red_F_\<G>_empty N'\<close>
    using F.empty_ord.Red_F_of_subset
    by presburger
  show \<open>\<And> N N'. N \<subseteq> N' \<Longrightarrow> F.Red_I_\<G> N \<subseteq> F.Red_I_\<G> N'\<close> 
    using F.Red_I_of_subset
    by presburger
  show \<open>\<And> N' N. N' \<subseteq> F.Red_F_\<G>_empty N \<Longrightarrow> F.Red_F_\<G>_empty N \<subseteq> F.Red_F_\<G>_empty (N - N')\<close>
    using F.empty_ord.Red_F_of_Red_F_subset
    by blast
  show \<open>\<And> N' N. N' \<subseteq> F.Red_F_\<G>_empty N \<Longrightarrow> F.Red_I_\<G> N \<subseteq> F.Red_I_\<G> (N - N')\<close>
    using F.empty_ord.Red_I_of_Red_F_subset
    by presburger
  show \<open>\<And> \<iota> N. \<iota> \<in> F_Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> F.Red_I_\<G> N\<close>
    using F.Red_I_of_Inf_to_N
    by blast
qed

interpretation LA_is_AF_calculus: AF_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close> F.Red_I_\<G>
  F.Red_F_\<G>_empty fml asn
proof standard
  show \<open>\<And> M N. M \<TTurnstile>\<union>\<G>e N \<Longrightarrow> \<exists> M' \<subseteq> M. \<exists> N' \<subseteq> N. finite M' \<and> finite N' \<and> M' \<TTurnstile>\<union>\<G>e N'\<close>
    using entails_\<G>_disj_compactness
    by presburger
  show \<open>\<And> C. \<forall> a \<in> asn C. {map_sign fml a} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C}\<close>
    using fml_entails_C
    by blast
  show \<open>\<And> C. \<forall> a \<in> asn C. {C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {map_sign fml a}\<close>
    using C_entails_fml
    by blast
  show \<open>\<And> C. asn C \<noteq> {}\<close>
    by (rule asn_not_empty) 
qed

(*<*)
lemma empty_not_unsat: \<open>\<not> {} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  using unsat_equiv2
  by blast
(*>*)

sublocale splitting_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.Red_I_\<G> F.Red_F_\<G>_empty fml asn 
proof standard
  show \<open>\<not> {} \<TTurnstile>\<union>\<G>e {}\<close>
    unfolding entails_\<G>_disj_def 
    using empty_not_unsat
    by blast 
  show \<open>\<And> N. inference_system.Inf_between F_Inf UNIV (F.Red_F_\<G>_empty N) \<subseteq> F.Red_I_\<G> N\<close>
    unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def F.Red_I_\<G>_def F.Red_I_\<G>_q_def
    using F.Inf_if_Inf_between
    apply (auto, unfold \<G>_I_def \<G>_F_def)
    apply auto
    sorry
  show \<open>\<And> N. {#} \<notin> F.Red_F_\<G>_empty N\<close>
    unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def \<G>_F_def
    apply (auto simp add: ex_ground_subst)
    sorry 
  show \<open>\<And> \<C>. \<C> \<noteq> {#} \<Longrightarrow> \<C> \<in> F.Red_F_\<G>_empty {{#}}\<close>
    unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def \<G>_F_def
    apply (auto simp add: ex_ground_subst) 
    sorry
qed

notation LA_is_AF_calculus.AF_entails_sound (infix \<open>\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F\<close> 50)



text \<open>
  Then we define the \textsc{BinSplit} simplification rule, and show that it is indeed a
  simplification rule in a similar fashion to
  @{thm splitting_calculus_with_simps.simplification_to_redundant}.
  We also show that it is sound, as in
  @{thm splitting_calculus_with_simps.SInf_with_simps_sound_wrt_entails_sound}.
\<close> 

(* This is taken from \<open>Splitting_Calculi.thy\<close>. Perhaps we should make it available everywhere? *)
definition splittable :: \<open>'a clause \<Rightarrow> 'a clause fset \<Rightarrow> bool\<close> where
  \<open>splittable C Cs \<longleftrightarrow> C \<noteq> {#} \<and> fcard Cs \<ge> 2
     \<and> {C} \<TTurnstile>\<union>\<G>e fset Cs \<and> (\<forall> C'. C' |\<in>| Cs \<longrightarrow> C \<in> F.Red_F_\<G>_empty {C'})\<close>

definition mk_bin_split
  :: \<open>'a clause \<Rightarrow> 'a clause \<Rightarrow> 'v sign fset \<Rightarrow> ('a clause, 'v) AF set\<close> where
  \<open>splittable (C \<union># D) {| C, D |} \<Longrightarrow> mk_bin_split C D A \<equiv>
    let a = (SOME a. a \<in> asn (sign.Pos C)) in
    { AF.Pair C (finsert a A), AF.Pair D (finsert (neg a) A) }\<close> 

(* We use the same naming convention as used in @{locale splitting_calculus_with_simps}, where
 * $X\_pre$ is the condition which must hold for the rule to be applicable, and $X\_simp$ is
 * the simplification rule itself. *)

abbreviation bin_split_pre :: \<open>'a clause \<Rightarrow> 'a clause \<Rightarrow> 'v sign fset \<Rightarrow>
  ('a clause, 'v) AF set \<Rightarrow> bool\<close> where
  \<open>bin_split_pre C D A B \<equiv> splittable (C \<union># D) {| C, D |} \<and> mk_bin_split C D A = B\<close>

abbreviation bin_split_simp :: \<open>'a clause \<Rightarrow> 'a clause \<Rightarrow> 'v sign fset \<Rightarrow> ('a clause, 'v) AF set \<Rightarrow>
  ('a clause, 'v) AF simplification\<close> where
  \<open>bin_split_simp C D A B \<equiv> Simplify {AF.Pair (C \<union># D) A} B\<close> 

inductive_set Simps :: \<open>('a clause, 'v) AF simplification set\<close> where
  bin_split: \<open>bin_split_pre C D A B \<Longrightarrow> bin_split_simp C D A B \<in> Simps\<close> 



(*<*)
lemma map_sign_neg_is_neg_map_sign: \<open>map_sign f (neg x) = neg (map_sign f x)\<close>
  by (smt (verit) neg.simps(1) neg.simps(2) sign.simps(10) sign.simps(9) to_V.elims) 

lemma subst_if_equi_entails:
  \<open>{C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {D} \<Longrightarrow> {D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C} \<Longrightarrow> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N \<Longrightarrow> M - {C} \<union> {D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
proof -
  assume C_entails_D: \<open>{C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {D}\<close> and
         D_entails_C: \<open>{D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C}\<close> and
         M_entails_N: \<open>M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
  then show ?thesis 
  proof (cases \<open>C \<in> M\<close>) 
    case True
    then obtain M' where
      M'_u_C_entails_N: \<open>M' \<union> {C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close> and
      M'_is: \<open>M' = M - {C}\<close> 
      using M_entails_N
      using insert_absorb
      by fastforce
    then have \<open>M' \<union> {C} \<union> {D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
      by (meson consequence_relation.entails_subsets dual_order.refl
          entails_\<G>_disj_cons_rel.ext_cons_rel sup_ge1)
    then have \<open>M' \<union> {D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
    proof -
      assume M'_u_C_u_D_entails_N: \<open>M' \<union> {C} \<union> {D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>

      have \<open>{D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C} \<union> {D}\<close>
        by (metis (no_types, lifting) Un_commute Un_upper2 consequence_relation.entails_reflexive
            consequence_relation.entails_subsets entails_\<G>_disj_cons_rel.ext_cons_rel insert_is_Un) 
      then show ?thesis
        using M'_u_C_u_D_entails_N
        by (smt (verit, ccfv_threshold) D_entails_C M'_u_C_entails_N Un_commute
            consequence_relation.entails_cut entails_\<G>_disj_cons_rel.ext_cons_rel sup_bot_left) 
    qed
    then show ?thesis
      using M'_is
      by force
  next
    case False
    then show ?thesis
      by (smt (verit, ccfv_SIG) Diff_empty Diff_insert0 M_entails_N
          consequence_relation.entails_subsets consequence_relation.entails_supsets
          entails_\<G>_disj_cons_rel.ext_cons_rel le_sup_iff)
  qed
qed

lemma neg_C_in_fml_J: \<open>neg a \<in> total_strip J \<Longrightarrow> a \<in> asn C \<Longrightarrow>
  map_sign fml ` total_strip J \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N \<longleftrightarrow> map_sign fml ` total_strip J \<union> {neg C} \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
proof (intro iffI)
  assume \<open>neg a \<in> total_strip J\<close> and
         \<open>a \<in> asn C\<close> and
         \<open>map_sign fml ` total_strip J \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
  then show \<open>map_sign fml ` total_strip J \<union> {neg C} \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
    using consequence_relation.entails_reflexive entails_\<G>_disj_cons_rel.ext_cons_rel
          subst_if_equi_entails
    by fastforce
next
  assume neg_a_in_J: \<open>neg a \<in> total_strip J\<close> and
         a_in_asn_C: \<open>a \<in> asn C\<close> and
         J_u_neg_C_entails_M: \<open>map_sign fml ` total_strip J \<union> {neg C} \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>

  have \<open>{map_sign fml a} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {C}\<close> and
       \<open>{C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {map_sign fml a}\<close>
    using a_in_asn_C fml_entails_C C_entails_fml
    by blast+
  then have \<open>{map_sign fml (neg a)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {neg C}\<close> and
            \<open>{neg C} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {map_sign fml (neg a)}\<close>
    by (simp add: entails_\<G>_disj_cons_rel.swap_neg_in_entails_neg map_sign_neg_is_neg_map_sign)+ 
  then have \<open>map_sign fml ` total_strip J \<union> {map_sign fml (neg a)} \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
    using subst_if_equi_entails[OF _ _ J_u_neg_C_entails_M]
    by (smt (verit, ccfv_threshold) Diff_insert_absorb Un_Diff_cancel2 Un_commute
        consequence_relation.entails_reflexive entails_\<G>_disj_cons_rel.ext_cons_rel
        insert_absorb insert_is_Un sup_assoc) 
  then show \<open>map_sign fml ` total_strip J \<union> M \<TTurnstile>\<union>\<G>e\<^sub>\<sim> N\<close>
    using neg_a_in_J
    by (metis Un_empty_right Un_insert_right insert_image) 
qed

lemma insert_in_left_Pos:
  \<open>{sign.Neg C} \<union> {sign.Pos D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D} \<Longrightarrow>
   {sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
proof -
  assume \<open>{sign.Neg C} \<union> {sign.Pos D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
  then have \<open>{D} \<TTurnstile>\<union>\<G>e {C, D}\<close>
    unfolding entails_\<G>_disj_cons_rel.entails_neg_def
    by simp
  then have \<open>{D} \<TTurnstile>\<inter>\<G>e {{#}} \<or> (\<exists> E \<in> {C, D}. {D} \<TTurnstile>\<inter>\<G>e {E})\<close>
    using entails_\<G>_disj_def
    by blast
  then have \<open>\<exists> E \<in> {C, D}. {C \<union># D} \<TTurnstile>\<inter>\<G>e {E}\<close>
  proof (elim disjE)
    assume \<open>{D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
    then have \<open>{C \<union># D} \<TTurnstile>\<inter>\<G>e {C}\<close>
      by (metis (mono_tags, lifting) F.entails_trans clause_union_entails_one entails_\<G>_disj_def
          entails_conj_is_entails_disj_on_singleton)
    then show ?thesis
      by blast 
  next
    assume \<open>\<exists> E \<in> {C, D}. {D} \<TTurnstile>\<inter>\<G>e {E}\<close>
    then obtain E where
      \<open>E = C \<or> E = D\<close> and
      \<open>{D} \<TTurnstile>\<inter>\<G>e {E}\<close>
      by blast 
    then show ?thesis
    proof (elim disjE)
      assume \<open>E = C\<close>
      then show ?thesis
        using clause_union_entails_one
        by fastforce
    next
      assume \<open>E = D\<close>
      then show ?thesis
        using clause_union_entails_one
        by auto
    qed
  qed
  then have \<open>{C \<union># D} \<TTurnstile>\<union>\<G>e {C, D}\<close>
    using entails_\<G>_disj_def
    by blast
  then have \<open>{sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
    unfolding entails_\<G>_disj_cons_rel.entails_neg_def
    by simp 
  then show ?thesis
    by blast 
qed 
(*>*)


(* Report theorem 14 for the case BinSplit *) 
theorem Simps_are_sound: \<open>\<iota> \<in> Simps \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {\<C>}\<close>
proof (intro ballI)
  fix \<C>
  assume \<open>\<iota> \<in> Simps\<close> and 
         \<C>_in_concl: \<open>\<C> \<in> S_to \<iota>\<close>
  then show \<open>S_from \<iota> \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {\<C>}\<close>
  proof (cases \<iota> rule: Simps.cases) 
    case (bin_split C D A B)
    then have C_u_D_splittable: \<open>splittable (C \<union># D) {| C, D |}\<close> and
              make_split: \<open>mk_bin_split C D A = B\<close>
      by blast+

    have \<open>\<C> \<in> (let a = SOME a. a \<in> asn (sign.Pos C)
      in {AF.Pair C (finsert a A), AF.Pair D (finsert (neg a) A)})\<close>
      using \<C>_in_concl local.bin_split(1) local.bin_split(2) mk_bin_split_def
      by auto
    then obtain a where
      a_in_asn_pos_C: \<open>a \<in> asn (sign.Pos C)\<close> and
      \<C>_is: \<open>\<C> = AF.Pair C (finsert a A) \<or> \<C> = AF.Pair D (finsert (neg a) A)\<close>
      by (metis asn_not_empty insert_iff singletonD some_in_eq)  

    show ?thesis
      using bin_split(1) \<C>_is
    proof auto
      have \<open>\<forall> J. fset (finsert a A) \<subseteq> total_strip J \<longrightarrow>
        map_sign fml ` total_strip J \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos C}\<close>
        using a_in_asn_pos_C
        by (smt (verit) Un_upper2 consequence_relation.entails_subsets
            entails_\<G>_disj_cons_rel.ext_cons_rel finsert.rep_eq fml_entails_C image_eqI
            insert_subset subset_iff sup_ge1) 
      then have \<open>\<forall> J. fset (finsert a A) \<subseteq> total_strip J \<longrightarrow>
        map_sign fml ` total_strip J \<union> sign.Pos ` ({AF.Pair (C \<union># D) A} proj\<^sub>J J) \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos C}\<close>
        unfolding LA_is_AF_calculus.enabled_projection_def LA_is_AF_calculus.enabled_def
        by simp 
      then show \<open>{AF.Pair (C \<union># D) A} \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {AF.Pair C (finsert a A)}\<close>
        unfolding LA_is_AF_calculus.AF_entails_sound_def LA_is_AF_calculus.enabled_set_def
                  LA_is_AF_calculus.enabled_def
        using LA_is_AF_calculus.fml_ext_is_mapping
        by auto 
    next
      let ?fml = \<open>\<lambda> J. map_sign fml ` total_strip J\<close> 

      have \<open>{sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
      proof -
        have \<open>{sign.Pos D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
          by (meson consequence_relation.entails_reflexive entails_\<G>_disj_cons_rel.ext_cons_rel) 
        then have \<open>{sign.Pos D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D} \<union> {sign.Pos C}\<close>
          by (metis (no_types, lifting) Un_absorb consequence_relation.entails_subsets
            entails_\<G>_disj_cons_rel.ext_cons_rel inf_sup_ord(3))
        then have \<open>{sign.Neg C} \<union> {sign.Pos D} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
          by (metis (no_types, opaque_lifting) Un_upper2 consequence_relation.entails_reflexive
            consequence_relation.entails_subsets dual_order.refl entails_\<G>_disj_cons_rel.ext_cons_rel)
        then show \<open>{sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
          using insert_in_left_Pos
          by blast
      qed
      then have \<open>\<forall> J. fset (finsert (neg a) A) \<subseteq> total_strip J \<longrightarrow>
        ?fml J \<union> {sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
        by (smt (verit, best) Un_upper2 consequence_relation.entails_subsets
            entails_\<G>_disj_cons_rel.ext_cons_rel insert_is_Un sup_assoc sup_ge1)
      then have \<open>\<forall> J. fset (finsert (neg a) A) \<subseteq> total_strip J \<longrightarrow>
        ?fml J \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
        using neg_C_in_fml_J a_in_asn_pos_C
        by (metis finsert.rep_eq insert_subset neg.simps(1))  
      then have \<open>\<forall> J. fset (finsert (neg a) A) \<subseteq> total_strip J \<longrightarrow>
        ?fml J \<union> sign.Pos ` ({AF.Pair (C \<union># D) A} proj\<^sub>J J) \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
        unfolding LA_is_AF_calculus.enabled_projection_def LA_is_AF_calculus.enabled_def
        by simp 
      then show \<open>{AF.Pair (C \<union># D) A} \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {AF.Pair D (finsert (neg a) A)}\<close>
        unfolding LA_is_AF_calculus.AF_entails_sound_def LA_is_AF_calculus.enabled_set_def
                  LA_is_AF_calculus.enabled_def 
        using LA_is_AF_calculus.fml_ext_is_mapping
        by auto 
    qed 
  qed
qed



interpretation SInf_sound:
  Preliminaries_With_Zorn.sound_inference_system SInf \<open>to_AF {#}\<close> \<open>(\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F)\<close>
  by (meson LA_is_AF_calculus.AF_ext_sound_cons_rel SInf_sound_wrt_entails_sound
      Preliminaries_With_Zorn.sound_inference_system.intro
      Preliminaries_With_Zorn.sound_inference_system_axioms.intro) 

interpretation Simps_simplifies: sound_simplification_rules \<open>to_AF {#}\<close> SInf \<open>(\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F)\<close> Simps
  by (standard, auto simp add: Simps_are_sound)



(* Report theorem 19 for the case BinSplit *)
theorem Simps_are_simplification_rules:
  \<open>bin_split_pre C D A B \<Longrightarrow> AF.Pair (C \<union># D) A \<in> SRed\<^sub>F B\<close>
proof -
  assume \<open>bin_split_pre C D A B\<close>
  then have splittable_C_u_D: \<open>splittable (C \<union># D) {| C, D |}\<close> and
            B_is: \<open>mk_bin_split C D A = B\<close>
    by blast+
  then have
    \<open>{C \<union># D} \<TTurnstile>\<union>\<G>e fset {|C, D|}\<close> and
    C_D_make_C_u_D_redundant: \<open>\<forall> C'. C' |\<in>| {|C, D|} \<longrightarrow> C \<union># D \<in> F.Red_F_\<G>_empty {C'}\<close> and
    B_is: \<open>\<exists> a \<in> asn (sign.Pos C). B =
      { AF.Pair C (finsert a A), AF.Pair D (finsert (neg a) A) }\<close> 
  proof -
    show \<open>{C \<union># D} \<TTurnstile>\<union>\<G>e fset {|C, D|}\<close>
      using splittable_C_u_D splittable_def
      by blast
    show \<open>\<forall> C'. C' |\<in>| {| C, D |} \<longrightarrow> C \<union># D \<in> F.Red_F_\<G>_empty {C'}\<close>
      using splittable_C_u_D splittable_def
      by blast
    show \<open>\<exists> a \<in> asn (sign.Pos C). B = { AF.Pair C (finsert a A), AF.Pair D (finsert (neg a) A) }\<close>
      using B_is mk_bin_split_def[OF splittable_C_u_D]
      by (metis asn_not_empty some_in_eq) 
  qed
  then obtain a where
    a_in_asn_C: \<open>a \<in> asn (sign.Pos C)\<close> and
    B_is: \<open>B = { AF.Pair C (finsert a A), AF.Pair D (finsert (neg a) A) }\<close>
    by blast 
  then show \<open>AF.Pair (C \<union># D) A \<in> SRed\<^sub>F B\<close>
  proof -
    have \<open>\<forall>\<J>. fset A \<subseteq> total_strip \<J> \<longrightarrow> C \<union># D \<in> F.Red_F_\<G>_empty (B proj\<^sub>J \<J>)\<close>
    proof (intro allI impI)
      fix \<J>
      assume A_in_\<J>: \<open>fset A \<subseteq> total_strip \<J>\<close>
      then have a_or_neg_a_in_\<J>: \<open>a \<in> total_strip \<J> \<or> neg a \<in> total_strip \<J>\<close>
        by simp
      then have a_or_neg_a_in_\<J>:
        \<open>fset (finsert a A) \<subseteq> total_strip \<J> \<or> fset (finsert (neg a) A) \<subseteq> total_strip \<J>\<close>
        by (simp add: A_in_\<J>) 

      have \<open>B proj\<^sub>J \<J> \<subseteq> {C, D}\<close>
        using B_is LA_is_AF_calculus.enabled_projection_def
        by auto
      moreover have \<open>B proj\<^sub>J \<J> \<noteq> {}\<close>
        unfolding LA_is_AF_calculus.enabled_projection_def
        using a_or_neg_a_in_\<J> B_is
        by (metis (mono_tags, lifting) AF.sel(2) LA_is_AF_calculus.enabled_def empty_iff insertCI
            mem_Collect_eq) 
      ultimately show \<open>C \<union># D \<in> F.Red_F_\<G>_empty (B proj\<^sub>J \<J>)\<close>
        using C_D_make_C_u_D_redundant
        by (smt (verit, del_insts) LA_is_sound_calculus.Red_F_of_subset all_not_in_conv empty_subsetI
            finsertCI insert_iff insert_subset subsetD) 
    qed
    then show ?thesis
      unfolding SRed\<^sub>F_def
      by simp
  qed
qed



end (* locale LA_calculus *)
















(* Ignore everything under this comment, for now *)




text \<open>
  Note that similarly to \<open>LA\<close>, \<open>O\<^sub>\<bbbP>\<close> is defined as the pair of an inference system \<open>FPInf\<close> and a
  redundancy criterion \<open>FPRed\<close> (which itself is a pair \<open>(FPRed\<^sub>I, FPRed\<^sub>F)\<close>).
  Since we will be comparing \<open>LA\<close> and \<open>O\<^sub>\<bbbP>\<close>, we will fix \<open>\<bbbP> = V\<close> (although we won't call \<open>O\<^sub>\<bbbP>\<close> \<open>O\<^sub>V\<close>
  to avoid confusion) and \<open>\<Sigma> = F\<close>.

  Entailment for \<open>LA\<close> will be denoted as in the locale @{locale splitting_calculus} by the symbols
  \<open>\<Turnstile>\<close> and \<open>\<Turnstile>s\<close> (\<open>\<Turnstile>\<^sub>A\<^sub>F\<close> and \<open>\<Turnstile>s\<^sub>A\<^sub>F\<close> when lifted to A-formulas) and entailment for \<open>O\<^sub>\<bbbP>\<close> will be denoted
  by the symbols \<open>\<Turnstile>\<^sub>O\<close> and \<open>\<Turnstile>s\<^sub>O\<close> in order to avoid any name clash.
  The entailment for \<open>O\<^sub>\<bbbP>\<close> works on \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses.
\<close>
(* NOTE: the AFP entry \<^url>\<open>https://www.isa-afp.org/entries/Ordered_Resolution_Prover.html\<close> uses
 * a datatype @{typ Clausal_Logic.literal} to represent positive or negative atoms.
 * 
 * In the Splitting Framework, we use a similar datatype @{typ Preliminaries_With_Zorn.sign} to
 * represent signedness. Fortunately, both are parameterized by an abstract formula type, so it
 * should be easy to connect both of them through a bijective mapping.
 *
 * The most critical part for the remainder of this file is to find how to actually extract the
 * \<closedblquote>head\<opendblquote> of a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause, i.e. extract \<open>C\<close> from \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close> (which we will need for
 * the definition of \<open>\<alpha>(\<cdot>)\<close> and for \<open>\<lfloor>\<cdot>\<rfloor>\<close>). *)
(* FIXME: I can already see a problem here:
 * \<^item> the Splitting Framework (specifically the @{locale AF_calculus}) uses the datatype @{typ AF},
 *   which is parameterized by two type variables:
 *   \<^item> \<open>'f\<close> for the formulas appearing on the left of the clause's arrow;
 *   \<^item> \<open>'v\<close> for the variables appearing on the right of the clause's arrow.
 * \<^item> the datatype @{typ clause} is parameterized by a single type variable representing the nullary
 *   predicates present in the clauses.
 *   @{typ clause}s are written \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close> in the paper, where \<open>C\<close> supposed to be some type
 *   of clause without \<open>\<bbbP>\<close>-literals (which one though?) and each \<open>L\<^sub>i\<close> is a literal (a positive
 *   or negative nullary predicate).
 *   As noted in the paper, \<open>C\<close> is only a \<open>\<Sigma>\<close>-clause, not a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause.
 *
 * This leads me to think that \<open>\<Sigma>\<^sub>\<bbbP>\<close> is actually \<^emph>\<open>not\<close> defined in @{theory Clausal_Logic} (only
 * \<open>\<Sigma>\<close>-clauses are through the datatype @{typ clause}) and that we need to define \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses
 * ourselves.
 * This needs some more investigation, because the \<open>\<G>\<close> functions are defined on @{typ clauses}s.
 *
 *
 * 
 * UPDATE: the more I read this section of the paper (the first few paragraphs of the subsection,
 * until \textsc{BinSplit}), the more I'm starting to believe that we actually need to define
 * \<open>O\<^sub>\<bbbP>\<close> ourselves, using a custom clause datatype along the lines of \<open>
     datatype ('f, 'v) \<Sigma>\<^sub>\<bbbP>_clause =
       Or (\<Sigma>_of: \<open>'f\<close>) \<open>'v clause\<close> (infix \<open>\<or>\<^sub>\<bbbP>\<close> 60)
   \<close>, which defines what a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause is.
 * Hence, a \<open>\<bbbP>\<close>-clause may just be represented by the type @{typ clause}.
 * There is a catch: how do we define \<open>O\<^sub>\<bbbP>\<close> from \<open>O = (FInf, FRed)\<close>?
 * Moreover, we need to define the parallel selection function, which selects maximal \<bbbP>-literals
 * in pure \<open>\<bbbP>\<close>-clauses and falls back to the original selection function.
 * I guess what \<closedblquote>pure\<opendblquote> means in this context is that \<open>C = \<bottom>\<close> in a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause \<open>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<close>?
 *
 * Also note that we need that all \<open>\<bbbP>\<close>-literals be smaller than all \<open>\<Sigma>\<close>-literals.
 * This is required for the proof of lemma 80.
 *
 *
 *
 * For all the properties on \<open>O\<^sub>\<bbbP>\<close>, I guess we will need to instantiate (or extend) the locale
 * @{locale FO_resolution_prover}:
 * \<^item> \<open>S\<close> is the selection function (returns a set of selected literals);
 * \<^item> \<open>subst_atm\<close> is the application of a substitution to an atom;
 * \<^item> \<open>subst_id\<close> is the empty substitution, which is the identity of the composition
     operator \<open>comp_subst\<close>;
 * \<^item> \<open>comp_subst\<close> is the substitution composition operator;
 * \<^item> \<open>renamings_apart\<close> ?;
 * \<^item> \<open>atm_of_atms\<close> ?;
 * \<^item> \<open>mgu\<close> is a function finding the most general unifier between atoms;
 * \<^item> \<open>less_atm\<close> is a strict partial ordering on atoms.
 *
 * If we are extending this locale, then we can use \<open>S\<close> as the \<closedblquote>original selection function\<closedblquote>
 * (although we have to provide a correct mapping from \<open>\<bbbP>\<close>-clauses to clauses), and extend \<open>less_atm\<close>
 * so that all \<open>'v\<close> atoms are smaller than any \<open>'f\<close> (\<open>\<Sigma>\<close>-)clause.
 *
 * Do we also need to lift the \<closedblquote>\<open>\<G>\<close> functions\<opendblquote> to \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses? The paper says that they are defined
 * on \<open>\<Sigma>\<close> clauses, but later in lemmas 80 and 81, they are used on (inferences over) \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses.
 * So if we do, how do we do it?
 *
 * Together with \<open>\<Sigma>\<^sub>\<bbbP>\<close>, lemma 78 uses the notion of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-model, which is basically a pair \<open>\<K> \<union> \<J>\<close>.
 * I guess we also need to define that, given @{const \<open>(\<TTurnstile>s)\<close>} (modelhood on \<open>\<bbbP>\<close>-clauses).
 * However, we need a notion of \<open>\<Sigma>\<close>-modelhood, which we would have to define on \<open>'f\<close>.
 * What does that mean?
 * \<^item> \<open>\<bbbP>\<close>-interpretation are easy: they are, in our case, instances of
 *   @{typ \<open>'v total_interpretation\<close>}, which is what we have already been using in the splitting
 *   calculus.
 * \<^item> \<open>\<Sigma>\<close>-interpretation are more tricky though, because they would need to be models of \<open>'f\<close> formulas
 *   which we don't know what they are.
 *   From the proof of lemma 81, it seems that these are @{typ \<open>'v total_interpretation\<close>}s too.
 *   This seems to be in accordance with the notation.
 *   However, in what way does an @{typ \<open>'v total_interpretation\<close>} qualify as a model of a \<open>'f\<close>
 *   formula? *)









text \<open>
  We also define the bijective mapping \<alpha>(\<cdot>), symbolising the natural correspondence between
  A-clauses and \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses.
  Formally, \<open>\<alpha>(C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n) \<equiv> C \<leftarrow> {\<not>L\<^sub>1, \<dots>, \<not>L\<^sub>n}\<close>.
  We also prove that it is indeed bijective:
  \<^item> \<open>\<alpha>(\<cdot>)\<close> is \<^emph>\<open>injective\<close>, meaning \<open>\<alpha>(D\<^sub>1) = \<alpha>(D\<^sub>2)\<close> implies \<open>D\<^sub>1 = D\<^sub>2\<close>;
  \<^item> \<open>\<alpha>(\<cdot>)\<close> is \<^emph>\<open>surjective\<close>, meaning that for all \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause \<open>C\<close> there exists an A-clause \<open>D\<close> such
    that \<open>\<alpha>(D) = C\<close>;
  \<^item> \<open>\<alpha>(\<cdot>)\<close> maps its entire domain to A-formulas.
    This property is true of all total functions.

  We also define \<open>\<iota>\<alpha>(\<cdot>)\<close> on inferences such that \<open>\<iota>\<alpha>((C\<^sub>n, \<dots>, C\<^sub>1, C\<^sub>0)) \<equiv> (\<alpha>(C\<^sub>n), \<dots>, \<alpha>(C\<^sub>1), \<alpha>(C\<^sub>0))\<close>.
  As usual, we also lift \<open>\<alpha>(\<cdot>)\<close> to sets such that \<open>\<alpha>_set(N) \<equiv> \<alpha> ` N\<close>.
\<close>
(* NOTE: to prove the bijectivity of \<open>\<alpha>(\<cdot>)\<close> we can use the predicates @{const inj}, @{const surj}
 * and @{const bij} from the theory @{theory Fun}.
 * @{term \<open>bij \<alpha>\<close>} should basically follow from @{term \<open>inj \<alpha>\<close>} and @{term \<open>surj \<alpha>\<close>}. *)
(* FIXME: we need to be careful when defining this function, as a \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clause contains a finite
 * \<^emph>\<open>multiset\<close> of literals, but @{typ \<open>('f, 'v) AF\<close>} only maps finite sets of V-literals.
 * This may hurt injectivity\<dots>
 * 
 * For example, consider \<open>D\<^sub>1 \<equiv> C \<or> L\<^sub>1 \<or> L\<^sub>1\<close> and \<open>D\<^sub>2 \<equiv> C \<or> L\<^sub>1\<close>. Turns out that \<open>\<alpha>(D\<^sub>1) = \<alpha>(D\<^sub>2)\<close>.
 * But \<open>D\<^sub>1 \<noteq> D\<^sub>2\<close> because \<open>{# L\<^sub>1, L\<^sub>1 #} \<noteq> {# L\<^sub>1 #}\<close>.
 * This means that \<open>\<alpha>(\<cdot>)\<close> is \<^emph>\<open>NOT\<close> bijective in this state!
 * Can we solve this? *)



text \<open>
  We also define a version of @{const F_of} on \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, as
  \<open>\<lfloor>C \<or> L\<^sub>1 \<or> \<dots> \<or> L\<^sub>n\<rfloor> = \<lfloor>C \<leftarrow> {\<not>L\<^sub>1, \<dots>, \<not>L\<^sub>n}\<rfloor> = C\<close>. 
\<close>

(* NOTE: The \<open>\<G>\<close> functions mentioned in the article are defined in the AFP entry
 * \<^url>\<open>https://www.isa-afp.org/theories/saturation_framework_extensions/#FO_Ordered_Resolution_Prover_Revisited.html#offset_5058..5061\<close>
 * (* Sorry for the 100 characters restriction, I can't shorten nor linebreak the link\<dots> :( *)
 *
 * The function of interest are @{const \<G>_F}, @{const \<G>_Fset} and @{const \<G>_I}.
 *)










text \<open>
  Lemma 78 proves that both entailments \<open>\<Turnstile>\<^sub>A\<^sub>F\<close> and \<open>\<Turnstile>\<^sub>O\<close> are equivalent up to \<alpha>-correspondence. 
\<close>
(* Report lemma 78 *)

(* FIXME: the notation \<open>\<K> \<Turnstile> \<lfloor>C\<rfloor>\<close> does not make sens here, if \<open>\<K>\<close> is an interpretation. In fact, it
 * is not defined in the article (only \<open>\<J> \<Turnstile> C\<^sub>\<bottom>\<close> is defined, note the propositional projection).
 * I guess this does not mean the same thing (the propositional projection is a bit too restricte
 * I think) hence we need to see what it \<^emph>\<open>really\<close> means. *)








text \<open>
  Lemma 79 states that if we have some \<open>\<alpha>(\<iota>)\<close> which is a \textsc{Base} inference, and that \<open>\<iota>\<close> only
  contains \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses, then \<open>\<iota>\<close> is actually an inference in \<open>FPInf\<close>. 
\<close>
(* Report lemma 79 *)

(* I think that this proof may not be as simple as described in the paper, but I'll see.
 *
 * Specifically, the fact that all \<open>\<lfloor>C\<^sub>i\<rfloor>\<close> (for \<open>i \<in> {1 ,\<dots>, n}\<close>) are not \<open>\<bottom>\<close> is blurry.
 * We know that \<open>\<alpha>(\<iota>)\<close> is a \textsc{Base} inference, hence that \<open>(\<alpha>(C\<^sub>n), \<dots>, \<alpha>(C\<^sub>1), D) \<in> FInf\<close> for 
 * some \<open>D\<close>. However, the inference \<open>(\<bottom>, \<bottom>)\<close> is a valid \<open>FInf\<close>-inference.
 * Hence \<open>(\<bottom> \<leftarrow> A, \<bottom> \<leftarrow> A)\<close> is a valid \<open>SInf\<close>-inference.
 * Given that \<open>\<alpha>(\<bottom> \<or> A) \<equiv> \<bottom> \<leftarrow> A\<close>, it is possible for some \<open>\<lfloor>C\<^sub>i\<rfloor>\<close> to be \<open>\<bottom>\<close> because \<open>\<lfloor>\<bottom> \<or> A\<rfloor> = \<bottom>\<close>.
 * So there is something that I'm missing in this proof.
 * 
 * Same goes for using the selection function with selected literals: how do we know that the
 * function will select those exactly? In fact, which literals in the premises are selected?
 *
 * Unfortunately, we cannot drop this lemma as it is used in the proof for lemma 81.
 * So either we find another way of doing things, or we understand how to do things.
 * I guess the better solution is the second one, although either this will take a lot of time or
 * I'll have to resort to try understanding this with Sophie. My best guess is that I don't know
 * what definition they are talking about, and I can't seem to find it in the source of the
 * formalization.
 *
 * I just don't get it. *)











text \<open>
  Lemma 80 is used to prove that the redundancy criterion in \<open>O\<^sub>\<bbbP>\<close> is stronger than the redundancy
  criterion used in \<open>LA\<close>.
  In other words, this means that the set of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses \<open>C\<close> such that \<open>\<alpha>(C)\<close> is redundant according
  to \<open>SRed\<^sub>F(\<alpha>(N))\<close> is included within the set of \<open>\<Sigma>\<^sub>\<bbbP>\<close>-clauses which are redundant according to
  \<open>FPRed\<^sub>F(N)\<close>.
  The same also holds for \<open>SRed\<^sub>I(\<alpha>(N))\<close> and \<open>FPRed\<^sub>I(N)\<close>. 
\<close>
(* NOTE: We can write those lemmas in two equivalent ways (in fact, the second is what needs to be
 * proven when applying \<open>intro subsetI\<close> to the first):
 * \<^item> \<open>{ C. \<alpha>(C) \<in> SRed\<^sub>F(\<alpha>(N)) } \<subseteq> { C \<in> FPRed\<^sub>F(N) }\<close>
 * \<^item> \<open>\<forall> C. \<alpha>(C) \<in> SRed\<^sub>F(\<alpha>(N)) \<longrightarrow> C \<in> FPRed\<^sub>F(N)\<close>
 * The same goes for \<open>SRed\<^sub>I\<close> and \<open>FPRed\<^sub>I\<close>:
 * \<^item> \<open>{ \<iota>. \<iota>\<alpha>(\<iota>) \<in> SRed\<^sub>I(\<alpha>(N)) } \<subseteq> { \<iota> \<in> FPRed\<^sub>I(N) }\<close>
 * \<^item> \<open>\<forall> \<iota>. \<iota>\<alpha>(\<iota>) \<in> SRed\<^sub>I(\<alpha>(N)) \<longrightarrow> \<iota> \<in> FPRed\<^sub>I(N)\<close>
 *
 * The second one is closer to what is proposed in the paper, so I think I'll go with that. *)
(* Report lemma 80 *)










text \<open>
  Lemma 81 shows that the notion of saturation is stronger in \<open>LA\<close>.
  If \<open>N\<close> is saturated w.r.t. \<open>O\<^sub>\<bbbP>\<close>, then \<open>\<alpha>(N)\<close> is saturated w.r.t. \<open>LA\<close>. 
\<close>
(* Report lemma 81 only for SInf (without BinSplit) *)
























text \<open>
  We now augment the earlier calculus \<open>LA\<close> with the simplification rule \textsc{BinSplit}
  (which we show to be sound and to make its premises redundant,
  Theorem @{thm splitting_calculus_with_simps.SInf_with_simps_sound_wrt_entails_sound}
  and Theorem @{thm splitting_calculus_with_simps.simplification_to_redundant} respectively).

  By Theorem @{thm splitting_calculus.S_calculus_statically_complete}, we can show that \<open>LA\<close> is
  statically complete, and therefore dynamically complete by Theorem
  @{thm splitting_calculus.S_calculus_dynamically_complete}.

  For completeness' sake, we also show that Lemma 81 holds of the SInf inference system augmented
  with \textsc{BinSplit}.
\<close> 

text \<open>
  The definition of simplification rules follows what we have been doing in
  @{locale splitting_calculus_with_simps}, i.e. $X\_simp$ indicates the simplification rule itself,
  while $X\_pre$ contains the precondition which must hold for the simplification rule to be
  applicable.
\<close> 




(* Report theorem 14 for the case BinSplit *)





(* Report theorem 19 for the case BinSplit *) 





(* Report theorem 21 for the full calculus *)





(* Report corollary 22 for the full calculus *)





(* Report lemma 81 for the full calculus with BinSplit *)







end (* theory Splitting_Without_Backtracking *)