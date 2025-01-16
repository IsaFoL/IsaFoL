(* Title:        Applications of the Splitting Framework to other architectures
 *               (Splitting without Backtracking)
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023
 *               Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Modular_Lightweight_Avatar
  imports
    Main
    Modular_Splitting_Calculi
    Saturation_Framework_Extensions.FO_Ordered_Resolution_Prover_Revisited
    "HOL-ex.Sketch_and_Explore" 
begin

(*commit_ignore_start*)
(*sledgehammer_params[provers="cvc4 cvc5 verit z3 e leo2 leo3 satallax spass vampire
  zipperposition"]*)
(*commit_ignore_end*)



subsection \<open>Ordered Resolution with a Disjunctive Consequence Relation\<close>

(* Quick comment here:
 * For our purpose, we need to add \<open>asn\<close> and \<open>fml\<close> as abstract bindings in the locale.
 * However, we also need to put the axioms of \<open>asn\<close> in the locale's assumptions, which needs
 * a disjunctive entailment.
 * Because we would like to use a disjunctive version of the one in @{locale FO_resolution_prover}
 * (specifically the first order one), we have to define this temporary locale, which contains
 * this entailment.
 * We will use it later in @{locale LA_calculus}, in the assumptions. *)
locale FO_resolution_prover_disjunctive = FO_resolution_prover S subst_atm id_subst comp_subst 
  renaming_aparts atm_of_atms mgu less_atm 
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
no_notation Sema.entailment (\<open>(_ \<TTurnstile>/ _)\<close> [53, 53] 53)
no_notation Linear_Temporal_Logic_on_Streams.HLD_nxt (infixr "\<cdot>" 65)
(* These two cause ambiguities in a few places. *)
notation entails_clss (infix \<open>\<TTurnstile>\<inter>e\<close> 50)

(* All this is taken from the file \<^file>\<open>FO_Ordered_Resolution_Prover_Revisited.thy\<close>.
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

(*** This one is not a copy-pasta! *)
interpretation G: calculus_with_standard_redundancy \<open>G_Inf M\<close> \<open>{{#}}\<close> \<open>(\<TTurnstile>\<inter>e)\<close>
  \<open>(<) :: 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool\<close>
  using G_Inf_have_prems G_Inf_reductive
  by (unfold_locales) simp_all 

(*** This one has been modified too! *)
interpretation G: clausal_counterex_reducing_calculus_with_standard_redundancy "G_Inf M"
  "gr.INTERP M"
  by (unfold_locales)

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

lemma F_stat_comp_calc: \<open>Calculus.statically_complete_calculus {{#}} F_Inf (\<TTurnstile>\<inter>\<G>e) F.Red_I_\<G>
   F.Red_F_\<G>_empty\<close>
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

sublocale F: Calculus.statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>\<inter>\<G>e)" F.Red_I_\<G>
  F.Red_F_\<G>_empty
  using F_stat_comp_calc by blast

sublocale F': Calculus.statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>\<inter>\<G>e)" F.empty_ord.Red_Red_I
  F.Red_F_\<G>_empty
  using F.empty_ord.reduced_calc_is_calc F.empty_ord.stat_is_stat_red F_stat_comp_calc
  by blast

(********************************************************)
(****************** End of copy pasta *******************)
(********************************************************)

(*<*)
interpretation F': Calculus.dynamically_complete_calculus \<open>{{#}}\<close> F_Inf \<open>(\<TTurnstile>\<inter>\<G>e)\<close> 
  F.empty_ord.Red_Red_I F.Red_F_\<G>_empty
  using F'.dynamically_complete_calculus_axioms .

lemma entails_bot_iff_unsatisfiable: \<open>M \<TTurnstile>\<inter>e {{#}} \<longleftrightarrow> \<not> satisfiable M\<close>
  by blast 

lemma entails_conj_compactness':
  \<open>M \<TTurnstile>\<inter>e N \<longleftrightarrow> (\<forall> I. (\<forall> M' \<subseteq> M. finite M' \<longrightarrow> I \<TTurnstile>s M') \<longrightarrow>
    (\<forall> N' \<subseteq> N. finite N' \<longrightarrow> I \<TTurnstile>s N'))\<close>
  by (meson empty_subsetI finite.emptyI finite_insert insert_subset true_clss_def true_clss_mono
      true_clss_singleton) 

lemma entails_\<G>_conj_compactness': 
  \<open>M \<TTurnstile>\<inter>\<G>e N \<longleftrightarrow> (\<forall> I. (\<forall> M' \<subseteq> \<G>_Fset M. finite M' \<longrightarrow> I \<TTurnstile>s M') \<longrightarrow>
     (\<forall> N' \<subseteq> \<G>_Fset N. finite N' \<longrightarrow> I \<TTurnstile>s N'))\<close>
  unfolding F.entails_\<G>_def \<G>_F_def using entails_conj_compactness'[of \<open>\<G>_Fset M\<close> \<open>\<G>_Fset N\<close>]
  unfolding \<G>_Fset_def \<G>_F_def by (meson UNIV_I) 

lemma entails_\<G>_iff_unsatisfiable:
  \<open>M \<TTurnstile>\<inter>\<G>e N \<longleftrightarrow> (\<forall> C \<in> \<G>_Fset N. \<not> satisfiable (\<G>_Fset M \<union> {{# -L #} | L. L \<in># C}))\<close>
  unfolding F.entails_\<G>_def \<G>_Fset_def \<G>_F_def
  using entails_iff_unsatisfiable
  by (smt (verit, ccfv_threshold) UNIV_I)

lemma list_all3_eq_map2:
  \<open>length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow>
    list_all3 (\<lambda> x y z. z = F x y) xs ys zs \<longleftrightarrow> map2 F xs ys = zs\<close>
proof (intro iffI)
  assume \<open>list_all3 (\<lambda> x y z. z = F x y) xs ys zs\<close> (is \<open>list_all3 ?P xs ys zs\<close>)
  then show \<open>map2 F xs ys = zs\<close>
    by (induction ?P xs ys zs rule: list_all3.induct, auto)
next
  assume
    \<open>length xs = length ys\<close> and
    \<open>length ys = length zs\<close> and
    \<open>map2 F xs ys = zs\<close>
  then show \<open>list_all3 (\<lambda> x y z. z = F x y) xs ys zs\<close>
  proof (induction \<open>zip xs ys\<close> arbitrary: xs ys zs) 
    case Nil
    then show ?case
      by auto 
  next
    case (Cons a as)

    obtain x y where
      \<open>a = (x, y)\<close>
      by fastforce
    then obtain z zs' xs' ys' where
      zs_eq: \<open>zs = z # zs'\<close> and
      xs_eq: \<open>xs = x # xs'\<close> and
      ys_eq: \<open>ys = y # ys'\<close> and
      z_is: \<open>z = F x y\<close>
      (* /!\ Very slow /!\ *)
      by (smt (verit, ccfv_threshold) Cons.hyps(2) Cons.prems(2) Cons.prems(3) Pair_inject
          list.inject map_eq_Cons_conv old.prod.case zip_eq_ConsE)
    then have
      \<open>as = zip xs' ys'\<close> and
      \<open>length xs' = length ys'\<close> and
      \<open>length ys' = length zs'\<close>
      using Cons.prems(1, 2) Cons.hyps(2)
      by auto 
    then show ?case
      using Cons.hyps Cons.prems(3) z_is zs_eq xs_eq ys_eq
      by auto
  qed
qed

lemma ex_finite_subset_M_if_ex_finite_subset_\<G>_F_M:
  \<open>M\<sigma> \<subseteq> \<G>_Fset M \<Longrightarrow> finite M\<sigma> \<Longrightarrow> M\<sigma> \<TTurnstile>\<inter>e {{#}} \<Longrightarrow>
    \<exists> M' \<subseteq> M. finite M' \<and> \<G>_Fset M' \<TTurnstile>\<inter>e {{#}}\<close>
proof -
  assume
    M\<sigma>_subset: \<open>M\<sigma> \<subseteq> \<G>_Fset M\<close> and
    finite_M\<sigma>: \<open>finite M\<sigma>\<close> and
    M\<sigma>_entails_bot: \<open>M\<sigma> \<TTurnstile>\<inter>e {{#}}\<close>

  have \<open>M\<sigma> \<subseteq> (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
    using M\<sigma>_subset
    unfolding \<G>_Fset_def \<G>_F_def
    by blast      
  then have \<open>\<forall> C \<in> M\<sigma>. \<exists> C' \<in> M. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> C = C' \<cdot> \<sigma>\<close>
    by blast
  moreover have \<open>M\<sigma> \<noteq> {}\<close>
    using M\<sigma>_entails_bot
    by blast 
  then obtain M\<sigma>' where
    M\<sigma>'_is: \<open>set M\<sigma>' = M\<sigma>\<close> and
    \<open>M\<sigma>' \<noteq> []\<close> 
    using finite_M\<sigma> finite_list
    by (meson sorted_list_of_set.set_sorted_key_list_of_set
        sorted_list_of_set.sorted_key_list_of_set_eq_Nil_iff) 
  ultimately have \<open>list.list_all (\<lambda> C. \<exists> C' \<in> M. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> C = C' \<cdot> \<sigma>) M\<sigma>'\<close>
    by (simp add: list.pred_set) 
  then obtain Cs where
    Cs_in_M: \<open>set Cs \<subseteq> M\<close> and
    \<open>list_all2 (\<lambda> C C'. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> C = C' \<cdot> \<sigma>) M\<sigma>' Cs\<close>
    using list_all_bex_ex_list_all2_conv[of M _ M\<sigma>']
    by blast 
  then obtain \<sigma>s where
    sigs_is: \<open>list_all3 (\<lambda> C C' \<sigma>. is_ground_subst \<sigma> \<and> C = C' \<cdot> \<sigma>) M\<sigma>' Cs \<sigma>s\<close>
    using list_all2_ex_to_ex_list_all3[of _ M\<sigma>' Cs]
    by blast 
  then have 
    all_grounding_in_\<sigma>s: \<open>list.list_all is_ground_subst \<sigma>s\<close>
    proof -
      have "\<And>p ms msa ss. \<not> list_all3 p ms msa ss \<or>
        list_all2 (\<lambda>m s. \<exists>ma. p (m::'a literal multiset) (ma::'a literal multiset) (s::'s)) ms ss"
        by (metis (no_types) list_all2_ex_to_ex_list_all3 list_all3_reorder)
      then have f1: "list_all2 (\<lambda>m s. \<exists>ma. is_ground_subst s \<and> m = ma \<cdot> s) M\<sigma>' \<sigma>s"
        using sigs_is by blast
      have "\<forall>ss p. \<exists>n. (list.list_all p ss \<or> n < length ss) \<and> 
        (\<not> p (ss ! n::'s) \<or> list.list_all p ss)"
        using list_all_length by blast
      then show ?thesis
        using f1 by (metis (lifting) list_all2_conv_all_nth)
    qed
    have
    \<open>list_all3 (\<lambda> C C' \<sigma>. C = C' \<cdot> \<sigma>) M\<sigma>' Cs \<sigma>s\<close>
    using list_all3_conj_distrib[of _ _ M\<sigma>' Cs \<sigma>s] list_all3_conv_list_all_3 sigs_is
    by fastforce
  then have M\<sigma>'_eq_map2: \<open>map2 (\<cdot>) Cs \<sigma>s = M\<sigma>'\<close>
    using list_all3_reorder2[of _ M\<sigma>' Cs \<sigma>s] list_all3_eq_map2[of Cs \<sigma>s M\<sigma>']
          list_all3_length_eq1[of _ M\<sigma>' Cs \<sigma>s] list_all3_length_eq2[of _ M\<sigma>' Cs \<sigma>s]
    by fastforce
  then have \<open>set M\<sigma>' \<subseteq> \<G>_Fset (set Cs)\<close>
    unfolding \<G>_Fset_def \<G>_F_def
    using all_grounding_in_\<sigma>s
    by auto (metis list.pred_set set_zip_leftD set_zip_rightD) 
  then have \<open>\<G>_Fset (set Cs) \<TTurnstile>\<inter>e {{#}}\<close>
    using M\<sigma>_entails_bot M\<sigma>'_is
    by (meson true_clss_mono) 
  then show \<open>\<exists> M' \<subseteq> M. finite M' \<and> \<G>_Fset M' \<TTurnstile>\<inter>e {{#}}\<close>
    using Cs_in_M
    by blast 
qed

lemma unsat_\<G>_compact: \<open>M \<TTurnstile>\<inter>\<G>e {{#}} \<Longrightarrow> \<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close> 
proof -
  assume M_entails_bot: \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e {{#}}\<close>
    using F_entails_\<G>_iff grounding_of_clss_def
    by fastforce
  then have \<open>\<exists> M' \<subseteq> \<G>_Fset M. finite M' \<and> M' \<TTurnstile>\<inter>e {{#}}\<close>
    using Unordered_Ground_Resolution.clausal_logic_compact
    by auto
  then have \<open>\<exists> M' \<subseteq> M. finite M' \<and> \<G>_Fset M' \<TTurnstile>\<inter>e {{#}}\<close>
    by (elim exE conjE, blast intro: ex_finite_subset_M_if_ex_finite_subset_\<G>_F_M)
  then show \<open>\<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
    using F_entails_\<G>_iff grounding_of_clss_def
    by auto
qed

lemma sat_\<G>_compact: \<open>\<not> M \<TTurnstile>\<inter>\<G>e {{#}} \<Longrightarrow> \<forall> M' \<subseteq> M. finite M' \<longrightarrow> \<not> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  using unsat_\<G>_compact F.entails_trans F.subset_entailed
  by blast

lemma neg_of_\<G>_F_lits_is_\<G>_F_of_neg_lits:
  \<open>\<Union> {{{# -L #} | L. L \<in># D' } | D'. D' \<in> \<G>_F D} = \<Union> (\<G>_F ` {{# -L #} | L. L \<in># D})\<close>
proof -
  have \<open>\<Union> {{{# -L #} | L. L \<in># D'} | D'. D' \<in> \<G>_F D} =
    \<Union> {{{# -L #} | L. L \<in># D \<cdot> \<sigma>} | \<sigma>. is_ground_subst \<sigma>}\<close>
    unfolding \<G>_F_def
    by blast 
  also have \<open>... = \<Union> {{{# -(L \<cdot>l \<sigma>) #} | L. L \<in># D} | \<sigma>. is_ground_subst \<sigma>}\<close>
    unfolding subst_cls_def
    by blast
  also have \<open>... = \<Union> {{{# -L \<cdot>l \<sigma> #} | L. L \<in># D} | \<sigma>. is_ground_subst \<sigma>}\<close>
    by simp 
  also have \<open>... = \<Union> {{{# -L #} \<cdot> \<sigma> | L. L \<in># D} | \<sigma>. is_ground_subst \<sigma>}\<close>
    unfolding subst_cls_def
    by simp
  also have \<open>... = (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
    by blast
  also have \<open>... = \<Union> (\<G>_F ` {{# -L #} | L. L \<in># D})\<close>
    unfolding \<G>_F_def
    by blast 
  finally show ?thesis .  
qed 

lemma entails_bot_neg_if_entails_\<G>_single: \<open>M \<TTurnstile>\<inter>\<G>e {D} \<Longrightarrow> M \<union> {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
proof -
  assume \<open>M \<TTurnstile>\<inter>\<G>e {D}\<close>
  then have unsat: \<open>\<forall> D' \<in> \<G>_F D. \<not> satisfiable (\<G>_Fset M \<union> {{# -L #} | L. L \<in># D'})\<close> 
    unfolding entails_\<G>_iff_unsatisfiable
    by (simp add: grounding_of_clss_def)
  then have \<open>\<not> satisfiable (\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D. {{# -L #} | L. L \<in># D'}))\<close>
    using ex_ground_subst substitution_ops.grounding_of_cls_def
    by fastforce
  then have \<open>\<not> satisfiable (\<G>_Fset M \<union> (\<Union> {{{# -L #} | L. L \<in># D'} | D'. D' \<in> \<G>_F D}))\<close>
    by fast 
  then have \<open>\<not> satisfiable (\<G>_Fset M \<union> (\<Union> (\<G>_F ` {{# -L #} | L. L \<in># D})))\<close>
    using neg_of_\<G>_F_lits_is_\<G>_F_of_neg_lits
    by auto 
  then have \<open>\<G>_Fset M \<union> (\<Union> (\<G>_F ` {{# -L #} | L. L \<in># D})) \<TTurnstile>\<inter>e {{#}}\<close>
    by presburger 
  then show \<open>M \<union> {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
    unfolding F_entails_\<G>_iff \<G>_F_def \<G>_Fset_def
    by force
qed

lemma minus_\<G>_Fset_to_\<G>_Fset_minus: \<open>C \<in> \<G>_Fset M - \<G>_Fset N \<Longrightarrow> C \<in> \<G>_Fset (M - N)\<close>
  unfolding \<G>_Fset_def \<G>_F_def
  by blast

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
  In addition, it is necessary to modify this definition to capture (D5) the compactness property
  of disjunctive entailment.
\<close>
definition entails_\<G>_disj :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix \<open>\<TTurnstile>\<union>\<G>e\<close> 50) where
  \<open>M \<TTurnstile>\<union>\<G>e N \<longleftrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}} \<or> (\<exists> M' \<subseteq> M. finite M' \<and> (\<exists> C \<in> N. M' \<TTurnstile>\<inter>\<G>e {C}))\<close> 


(*<*)
lemma unsat_supsets: \<open>M \<TTurnstile>\<inter>\<G>e {{#}} \<Longrightarrow> M \<union> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  using F.entails_trans F.subset_entailed
  by blast
(*>*)

(* Property (D3) *) 
lemma entails_\<G>_disj_subsets: \<open>M' \<subseteq> M \<Longrightarrow> N' \<subseteq> N \<Longrightarrow> M' \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<TTurnstile>\<union>\<G>e N\<close>
  by (smt (verit, del_insts) F.entails_trans F.subset_entailed entails_\<G>_disj_def order_trans subsetD) 

(* Property (D5) *)
lemma entails_\<G>_disj_compactness:
  \<open>M \<TTurnstile>\<union>\<G>e N \<Longrightarrow> \<exists> M' N'. M' \<subseteq> M \<and> N' \<subseteq> N \<and> finite M' \<and> finite N' \<and>
     M' \<TTurnstile>\<union>\<G>e N'\<close>
proof -
  assume \<open>M \<TTurnstile>\<union>\<G>e N\<close>
  then consider
    (M_unsat) \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close> |
    (b) \<open>\<exists> M' \<subseteq> M. finite M' \<and> (\<exists> C \<in> N. M' \<TTurnstile>\<inter>\<G>e {C})\<close>
    unfolding entails_\<G>_disj_def
    by blast 
  then show ?thesis
  proof cases
    case M_unsat
    then show ?thesis
      using unsat_\<G>_compact[of M]
      unfolding entails_\<G>_disj_def
      by blast 
  next
    case b
    then show ?thesis
      unfolding entails_\<G>_disj_def
      by (meson empty_subsetI finite.emptyI finite.insertI insert_subset subset_refl) 
  qed
qed

(* Property (D4) *) 
lemma entails_\<G>_disj_cut: \<open>M \<TTurnstile>\<union>\<G>e N \<union> {C} \<Longrightarrow> M' \<union> {C} \<TTurnstile>\<union>\<G>e N' \<Longrightarrow> M \<union> M' \<TTurnstile>\<union>\<G>e N \<union> N'\<close>
proof -
  assume M_entails_N_u_C: \<open>M \<TTurnstile>\<union>\<G>e N \<union> {C}\<close> and
         M'_u_C_entails_N': \<open>M' \<union> {C} \<TTurnstile>\<union>\<G>e N'\<close>
  then obtain P P' where
    P_subset_M: \<open>P \<subseteq> M\<close> and
    finite_P: \<open>finite P\<close> and
    P_entails_N_u_C: \<open>P \<TTurnstile>\<union>\<G>e N \<union> {C}\<close> and
    P'_subset_M'_u_C: \<open>P' \<subseteq> M' \<union> {C}\<close> and
    finite_P': \<open>finite P'\<close> and
    P'_entails_N': \<open>P' \<TTurnstile>\<union>\<G>e N'\<close>
    using entails_\<G>_disj_compactness[OF M_entails_N_u_C]
          entails_\<G>_disj_compactness[OF M'_u_C_entails_N'] entails_\<G>_disj_subsets
    by blast 

  have P_subset_M_u_M': \<open>P \<subseteq> M \<union> M'\<close>
    using P_subset_M
    by blast 

  show ?thesis
  proof (cases \<open>C \<in> P'\<close>) 
    case C_in_P': True

    define P'' where
      \<open>P'' = P' - {C}\<close>

    have P''_subset_M': \<open>P'' \<subseteq> M'\<close>
      using P'_subset_M'_u_C P''_def
      by blast

    have finite_P'': \<open>finite P''\<close>
      using finite_P' P''_def
      by blast 

    consider
      (M_unsat) \<open>P \<TTurnstile>\<inter>\<G>e {{#}}\<close>
    | (M'_u_C_unsat) \<open>P' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
    | (c) \<open>(\<exists> C' \<in> N \<union> {C}. P \<TTurnstile>\<inter>\<G>e {C'}) \<and> (\<exists> C' \<in> N'. P' \<TTurnstile>\<inter>\<G>e {C'})\<close>
      using P_entails_N_u_C P'_entails_N' finite_P finite_P'
      unfolding entails_\<G>_disj_def
      by (metis (no_types, lifting) F.entails_trans F.subset_entailed) 
    then show ?thesis
    proof cases 
      case M_unsat
      then have \<open>P \<TTurnstile>\<union>\<G>e N \<union> N'\<close>
        using entails_\<G>_disj_def
        by blast 
      then show ?thesis
        using entails_\<G>_disj_subsets[of P \<open>M \<union> M'\<close> \<open>N \<union> N'\<close> \<open>N \<union> N'\<close>, OF P_subset_M_u_M']
        by blast 
    next
      case M'_u_C_unsat
      then show ?thesis 
        (* /!\ Slow /!\ *)
        by (smt (z3) F.subset_entailed F_entails_\<G>_iff M_entails_N_u_C P'_subset_M'_u_C UN_Un
            Un_insert_right entails_\<G>_disj_def entails_\<G>_disj_subsets insert_iff
            sup_bot.right_neutral sup_ge1 true_clss_union) 
    next
      case c
      then obtain C1 C2 where
        C1_in_N_u_C: \<open>C1 \<in> N \<union> {C}\<close> and
        P_entails_C1: \<open>P \<TTurnstile>\<inter>\<G>e {C1}\<close> and
        C2_in_N': \<open>C2 \<in> N'\<close> and
        P'_entails_C2: \<open>P' \<TTurnstile>\<inter>\<G>e {C2}\<close>
        by blast
      then show ?thesis
      proof (cases \<open>C1 = C\<close>) 
        case C1_is_C: True

        show ?thesis   
        proof (cases \<open>C2 = C\<close>)
          case True
          then have \<open>N \<union> {C} \<union> N' = N \<union> N'\<close>
            using C2_in_N'
            by blast 
          moreover have \<open>P \<TTurnstile>\<union>\<G>e N \<union> {C}\<close>
            using P_entails_C1 C1_in_N_u_C finite_P
            unfolding entails_\<G>_disj_def
            by blast 
          ultimately show ?thesis
            using entails_\<G>_disj_subsets[OF P_subset_M_u_M', of \<open>N \<union> {C}\<close> \<open>N \<union> N'\<close>]
            by blast 
        next
          case C2_not_C: False
          then have \<open>P \<union> P'' \<TTurnstile>\<inter>\<G>e {C2}\<close>
            by (smt (verit, del_insts) C1_is_C F.entail_union F.entails_trans F.subset_entailed
                P''_def P'_entails_C2 P_entails_C1 Un_commute Un_insert_left insert_Diff_single
                sup_ge2) 
          then have \<open>M \<union> M' \<TTurnstile>\<union>\<G>e N'\<close>
            using C2_in_N' P''_subset_M' P_subset_M finite_UnI[OF finite_P finite_P'']
            by (smt (verit, ccfv_SIG) P_subset_M_u_M' Un_subset_iff Un_upper2 entails_\<G>_disj_def
                order_trans)
          then show ?thesis
            by (meson entails_\<G>_disj_subsets equalityE sup_ge2)  
        qed
      next
        case False
        then have \<open>C1 \<in> N\<close>
          using C1_in_N_u_C
          by blast 
        then have \<open>P \<TTurnstile>\<union>\<G>e N\<close>
          unfolding entails_\<G>_disj_def
          using P_entails_C1 finite_P
          by blast 
        then show ?thesis
          using entails_\<G>_disj_subsets[OF P_subset_M_u_M']
          by blast 
      qed
    qed
  next
    case False
    then have \<open>P' \<subseteq> M'\<close>
      using P'_subset_M'_u_C
      by blast 
    then have \<open>M' \<TTurnstile>\<union>\<G>e N'\<close>
      using P'_entails_N' entails_\<G>_disj_subsets
      by blast 
    then show ?thesis
      using entails_\<G>_disj_subsets[of M' \<open>M \<union> M'\<close> N' \<open>N \<union> N'\<close>] 
      by blast 
  qed
qed

lemma entails_\<G>_disj_cons_rel_ext: \<open>consequence_relation {#} (\<TTurnstile>\<union>\<G>e)\<close>
proof (standard)
  show \<open>{{#}} \<TTurnstile>\<union>\<G>e {}\<close>
    using F.subset_entailed entails_\<G>_disj_def
    by blast
  show \<open>\<And> C. {C} \<TTurnstile>\<union>\<G>e {C}\<close>
    by (meson F.subset_entailed entails_\<G>_disj_def finite.emptyI finite.insertI singletonI
        subset_refl)
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

lemma all_redundant_to_bottom: \<open>\<C> \<noteq> {#} \<Longrightarrow> \<C> \<in> F.Red_F_\<G>_empty {{#}}\<close>
  unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def G.Red_F_def
proof clarsimp
  fix D :: \<open>'a clause\<close>

  assume \<open>\<C> \<noteq> {#}\<close> and \<open>D \<in> \<G>_F \<C>\<close>
  then have \<open>D \<noteq> {#}\<close>
    unfolding \<G>_F_def by force 
  then have \<open>{#} < D\<close>
    by auto 
  moreover have \<open>\<forall> I. I \<TTurnstile>s {{#}} \<longrightarrow> I \<TTurnstile> D\<close>
    by blast
  ultimately show \<open>\<exists> E \<subseteq> {{#}}. (\<forall>I. I \<TTurnstile>s E \<longrightarrow> I \<TTurnstile> D) \<and> (\<forall> C \<in> E. C < D)\<close>
    by blast 
qed 

lemma bottom_never_redundant: \<open>{#} \<notin> F.Red_F_\<G>_empty N\<close>
  unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def G.Red_F_def
  by auto

lemma \<open>F.Inf_between UNIV (F.Red_F_\<G>_empty N) \<subseteq> F.empty_ord.Red_Red_I N\<close>
  using F.empty_ord.inf_subs_reduced_red_inf .

end (* locale FO_resolution_prover' *)


subsection \<open>Lightweight Avatar without BinSplit\<close>

text \<open> Since the set \<open>\<bbbP>\<close> of nullary predicates is left unspecified, we cannot define \<open>fml\<close> nor \<open>asn\<close>.
 Therefore, we keep them abstract and leave it to anybody instanciating this locale
 to specify them. \<close>

locale LA_calculus = FO_resolution_prover_disjunctive S subst_atm id_subst comp_subst renaming_aparts
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
  Calculi_And_Annotations.sound_inference_system F_Inf \<open>{#}\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
proof standard
  have \<open>\<And> \<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<inter>\<G>e {concl_of \<iota>}\<close>
    using F.sound
    by blast
  then show \<open>\<And> \<iota>. \<iota> \<in> F_Inf \<Longrightarrow> set (prems_of \<iota>) \<TTurnstile>\<union>\<G>e {concl_of \<iota>}\<close>
    using entails_\<G>_disj_def by blast

qed

interpretation LA_is_calculus: calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> F.empty_ord.Red_Red_I F.Red_F_\<G>_empty
proof standard 
  show \<open>\<And> N. F.empty_ord.Red_Red_I N \<subseteq> F_Inf\<close>
    using F'.Red_I_to_Inf
    by blast
  show \<open>\<And> N. N \<TTurnstile>\<union>\<G>e {{#}} \<Longrightarrow> N - F.Red_F_\<G>_empty N \<TTurnstile>\<union>\<G>e {{#}}\<close>
    using F.empty_ord.Red_F_Bot
    by (metis (no_types, lifting) entails_\<G>_disj_def sat_\<G>_compact singleton_iff)
  show \<open>\<And> N N'. N \<subseteq> N' \<Longrightarrow> F.Red_F_\<G>_empty N \<subseteq> F.Red_F_\<G>_empty N'\<close>
    using F.empty_ord.Red_F_of_subset
    by presburger
  show \<open>\<And> N N'. N \<subseteq> N' \<Longrightarrow> F.empty_ord.Red_Red_I N \<subseteq> F.empty_ord.Red_Red_I N'\<close> 
    using F'.Red_I_of_subset
    by presburger
  show \<open>\<And> N' N. N' \<subseteq> F.Red_F_\<G>_empty N \<Longrightarrow> F.Red_F_\<G>_empty N \<subseteq> F.Red_F_\<G>_empty (N - N')\<close>
    using F.empty_ord.Red_F_of_Red_F_subset
    by blast
  show \<open>\<And> N' N. N' \<subseteq> F.Red_F_\<G>_empty N \<Longrightarrow> F.empty_ord.Red_Red_I N \<subseteq> F.empty_ord.Red_Red_I (N - N')\<close>
    using F'.Red_I_of_Red_F_subset
    by presburger
  show \<open>\<And> \<iota> N. \<iota> \<in> F_Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> F.empty_ord.Red_Red_I N\<close>
    using F'.Red_I_of_Inf_to_N
    by blast
qed

lemma F_disj_complete: \<open>statically_complete_calculus {#} F_Inf (\<TTurnstile>\<union>\<G>e) F.empty_ord.Red_Red_I
  F.Red_F_\<G>_empty\<close>
proof
  show \<open>\<And> N. LA_is_calculus.saturated N \<Longrightarrow> N \<TTurnstile>\<union>\<G>e {{#}} \<Longrightarrow> {#} \<in> N\<close>
    unfolding LA_is_calculus.saturated_def using F'.saturated_def F'.statically_complete
    by (smt (verit, ccfv_SIG) entails_\<G>_disj_def insertI1 sat_\<G>_compact singletonD)
qed

sublocale statically_complete_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> F.empty_ord.Red_Red_I
  F.Red_F_\<G>_empty
  using F_disj_complete .

sublocale LA_is_sound_calculus: sound_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.empty_ord.Red_Red_I F.Red_F_\<G>_empty 
  using LA_is_calculus.Red_I_to_Inf LA_is_calculus.Red_F_Bot  LA_is_calculus.Red_F_of_subset 
        LA_is_calculus.Red_I_of_subset  LA_is_calculus.Red_F_of_Red_F_subset
        LA_is_calculus.Red_I_of_Red_F_subset LA_is_calculus.Red_I_of_Inf_to_N
  by (unfold_locales, presburger+) 

sublocale LA_is_AF_calculus: AF_calculus_lifting \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.empty_ord.Red_Red_I F.Red_F_\<G>_empty fml asn
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
  using unsat_equiv3
  by blast
(*>*)

sublocale core_LA_calculus: splitting_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.empty_ord.Red_Red_I F.Red_F_\<G>_empty fml asn 
proof standard
  show \<open>\<not> {} \<TTurnstile>\<union>\<G>e {}\<close>
    unfolding entails_\<G>_disj_def using empty_not_unsat by blast
  show \<open>\<And> N. F.Inf_between UNIV (F.Red_F_\<G>_empty N) \<subseteq> F.empty_ord.Red_Red_I N\<close>
    using F.empty_ord.inf_subs_reduced_red_inf by blast
  show \<open>\<And> N. {#} \<notin> F.Red_F_\<G>_empty N\<close>
    using nobot_in_Red by blast 
  show \<open>\<And> \<C>. \<C> \<noteq> {#} \<Longrightarrow> \<C> \<in> F.Red_F_\<G>_empty {{#}}\<close>
    using all_redundant_to_bottom by blast
qed

notation LA_is_AF_calculus.AF_entails_sound (infix \<open>\<TTurnstile>s\<union>\<G>e\<^sub>A\<^sub>F\<close> 50)
notation LA_is_AF_calculus.AF_entails (infix \<open>\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F\<close> 50)

sublocale AF_calculus_with_sound_simps_and_opt_infs \<open>to_AF {#}\<close> 
  core_LA_calculus.core.SInf \<open>(\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F)\<close> \<open>(\<TTurnstile>s\<union>\<G>e\<^sub>A\<^sub>F)\<close> core_LA_calculus.core.SRed\<^sub>I 
  core_LA_calculus.core.SRed\<^sub>F "{}" "{}"
  using core_LA_calculus.empty_simps.AF_calculus_with_sound_simps_and_opt_infs_axioms .

text \<open>
   By Theorem @{thm core_splitting_calculus.S_calculus_statically_complete}, we can show that \<open>LA\<close> is
  statically complete, and therefore dynamically complete by Theorem
  @{thm core_splitting_calculus.S_calculus_dynamically_complete}.
\<close>

(* Local static completeness (as other forms of completeness, global, dynamic...)
   follows from static completeness of the base calculus *)
theorem \<open>core_LA_calculus.core.locally_saturated \<N> \<Longrightarrow> \<N> \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {to_AF {#}} \<Longrightarrow> to_AF {#} \<in> \<N>\<close>
  using core_LA_calculus.core.S_calculus_strong_statically_complete[OF F_disj_complete] .

subsection \<open>Lightweight Avatar\<close>

text \<open>
  We now augment the earlier calculus into \<open>LA\<close> with the simplification rule \textsc{BinSplit}.
\<close> 

interpretation with_BinSplit: AF_calculus_with_binsplit \<open>to_AF {#}\<close> core_LA_calculus.core.SInf
  LA_is_AF_calculus.AF_entails LA_is_AF_calculus.AF_entails_sound core_LA_calculus.core.SRed\<^sub>I 
  core_LA_calculus.core.SRed\<^sub>F \<open>{}\<close> \<open>{}\<close> core_LA_calculus.bin_splittable
  using core_LA_calculus.extend_simps_with_binsplit[OF 
      core_LA_calculus.empty_simps.AF_calculus_with_sound_simps_and_opt_infs_axioms] .

sublocale LA: AF_calculus_with_sound_simps_and_opt_infs \<open>to_AF {#}\<close> 
  core_LA_calculus.core.SInf LA_is_AF_calculus.AF_entails LA_is_AF_calculus.AF_entails_sound 
  core_LA_calculus.core.SRed\<^sub>I core_LA_calculus.core.SRed\<^sub>F with_BinSplit.Simps_with_BinSplit \<open>{}\<close>
  using with_BinSplit.AF_calc_ext.AF_calculus_with_sound_simps_and_opt_infs_axioms .

end (* locale LA_calculus *)

end (* theory Modular Lightweight_Avatar *)