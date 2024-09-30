(* Title:        Applications of the Splitting Framework to other architectures
 *               (Splitting without Backtracking)
 * Author:       Ghilain Bergeron <ghilain.bergeron at inria.fr>, 2023
 *               Sophie Tourret <sophie.tourret at inria.fr, 2024 *)

theory Splitting_Without_Backtracking
  imports
    Main
    Splitting_Calculi
    Saturation_Framework_Extensions.FO_Ordered_Resolution_Prover_Revisited
    "HOL-ex.Sketch_and_Explore"
    (* Saturation_Framework_Extensions.Clausal_Calculus *) 
begin

(*commit_ignore_start*)
(*sledgehammer_params[provers="cvc4 cvc5 verit z3 e iprover leo2 leo3 satallax spass vampire
  zipperposition"]*)
(*commit_ignore_end*)

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

(*<*)
(*! All these should belong in the \<open>List\<close> theory, although these definitions lack a few lemmas
 *  which aren't useful in our case.
 *  Note that it would be better to remove calls to the \<open>smt\<close> method as these take a bit long. *)
primrec zip3 :: \<open>'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> ('a \<times> 'b \<times> 'c) list\<close> where
  \<open>zip3 xs ys [] = []\<close>
  | \<open>zip3 xs ys (z # zs) =
  (case xs of [] \<Rightarrow> [] | x # xs \<Rightarrow>
  (case ys of [] \<Rightarrow> [] | y # ys \<Rightarrow> (x, y, z) # zip3 xs ys zs))\<close>

abbreviation map3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'd list\<close> where
  \<open>map3 f xs ys zs \<equiv> map (\<lambda>(x, y, z). f x y z) (zip3 xs ys zs)\<close> 

fun list_all3 :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> bool\<close> where
  \<open>list_all3 p [] [] [] = HOL.True\<close>
| \<open>list_all3 p (x # xs) (y # ys) (z # zs) = (p x y z \<and> list_all3 p xs ys zs)\<close>
| \<open>list_all3 _ _ _ _ = False\<close> 

lemma list_all3_length_eq1: \<open>list_all3 P xs ys zs \<Longrightarrow> length xs = length ys\<close>
  by (induction P xs ys zs rule: list_all3.induct, auto)

lemma list_all3_length_eq2: \<open>list_all3 P xs ys zs \<Longrightarrow> length ys = length zs\<close>
  by (induction P xs ys zs rule: list_all3.induct, auto) 

lemma list_all3_length_eq3: \<open>list_all3 P xs ys zs \<Longrightarrow> length xs = length zs\<close>
  using list_all3_length_eq1 list_all3_length_eq2
  by fastforce 

lemma list_all2_ex_to_ex_list_all3:
  \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys \<longleftrightarrow> (\<exists> zs. list_all3 P xs ys zs)\<close>
proof (intro iffI)
  assume \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys\<close>
  then show \<open>\<exists> zs. list_all3 P xs ys zs\<close>
    by (induct xs ys; metis list_all3.simps(1) list_all3.simps(2))
next
  assume \<open>\<exists> zs. list_all3 P xs ys zs\<close>
  then obtain zs where
    all3_xs_ys_zs: \<open>list_all3 P xs ys zs\<close> 
    by blast
  then show \<open>list_all2 (\<lambda> x y. \<exists> z. P x y z) xs ys\<close>
    using all3_xs_ys_zs
    by (induction P xs ys zs rule: list_all3.induct, auto)
qed 

lemma list_all3_conj_distrib: \<open>list_all3 (\<lambda> x y z. P x y z \<and> Q x y z) xs ys zs \<longleftrightarrow>
  list_all3 P xs ys zs \<and> list_all3 Q xs ys zs\<close>
  by (induction \<open>\<lambda> x y z. P x y z \<and> Q x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all3_conv_list_all_3: \<open>list_all3 (\<lambda> x y z. P z) xs ys zs \<Longrightarrow> list_all P zs\<close>
proof -
  assume \<open>list_all3 (\<lambda> x y z. P z) xs ys zs\<close> (is \<open>list_all3 ?P xs ys zs\<close>)
  then show \<open>list_all P zs\<close> 
    by (induction ?P xs ys zs rule: list_all3.induct, auto)
qed

lemma list_all3_reorder:
  \<open>list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> x z y. P x y z) xs zs ys\<close>
  by (induction \<open>\<lambda> x y z. P x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all3_reorder2:
  \<open>list_all3 (\<lambda> x y z. P x y z) xs ys zs \<longleftrightarrow> list_all3 (\<lambda> y z x. P x y z) ys zs xs\<close>
  by (induction \<open>\<lambda> x y z. P x y z\<close> xs ys zs rule: list_all3.induct, auto)

lemma list_all2_conj_distrib:
  \<open>list_all2 (\<lambda> x y. P x y \<and> Q x y) A B \<longleftrightarrow> list_all2 P A B \<and> list_all2 Q A B\<close>
  by (smt (verit, ccfv_SIG) list_all2_conv_all_nth)

lemma list_all_bex_ex_list_all2_conv:
  \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs \<longleftrightarrow> (\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys')\<close>
proof (intro iffI)
  assume \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs\<close>
  then have \<open>list.list_all (\<lambda> x. \<exists> y. y \<in> ys \<and> P x y) xs\<close>
    by meson 
  then have \<open>\<exists> ys'. list_all2 (\<lambda> x y. y \<in> ys \<and> P x y) xs ys'\<close>
    by (induct xs, auto)
  then have \<open>\<exists> ys'. list_all2 (\<lambda> x y. y \<in> ys) xs ys' \<and> list_all2 (\<lambda> x y. P x y) xs ys'\<close>
    using list_all2_conj_distrib
    by blast
  then have \<open>\<exists> ys'. list.list_all (\<lambda> y. y \<in> ys) ys' \<and> list_all2 P xs ys'\<close>
    by (metis list_all2_conv_all_nth list_all_length)
  then show \<open>\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys'\<close>
    by (metis list.pred_set subsetI)
next
  assume \<open>\<exists> ys'. set ys' \<subseteq> ys \<and> list_all2 P xs ys'\<close>
  then show \<open>list.list_all (\<lambda> x. \<exists> y \<in> ys. P x y) xs\<close>
    (* /!\ A bit slow /!\ *)
    by (smt (verit, del_insts) list.pred_set list_all2_find_element subsetD) 
qed 
(*>*)

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

(* NOT NEEDED... I think *)
(*
interpretation FL: given_clause "{{#}}" F_Inf "{{#}}" UNIV "\<lambda>N. (\<TTurnstile>\<inter>e)" G_Inf G.Red_I
  "\<lambda>N. G.Red_F" "\<lambda>N. \<G>_F" \<G>_I_opt "(\<doteq>)" "(\<prec>\<cdot>)" "(\<sqsubset>l)" Old
proof (unfold_locales; (intro ballI)?)
  show "equivp (\<doteq>)" 
    unfolding equivp_def by (meson generalizes_refl generalizes_trans)
next
  show "po_on (\<prec>\<cdot>) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def
    using strictly_generalizes_irrefl strictly_generalizes_trans by auto
next
  show "wfp_on (\<prec>\<cdot>) UNIV"
    unfolding wfp_on_UNIV by (metis wf_strictly_generalizes)
next
  show "po_on (\<sqsubset>l) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def using irrefl_L_Prec trans_L_Prec by blast
next
  show "wfp_on (\<sqsubset>l) UNIV"
    unfolding wfp_on_UNIV by (rule wf_L_Prec)
next
  fix C1 D1 C2 D2
  assume
    "C1 \<doteq> D1"
    "C2 \<doteq> D2"
    "C1 \<prec>\<cdot> C2"
  then show "D1 \<prec>\<cdot> D2"
    by (smt antisym size_mset_mono size_subst strictly_generalizes_def generalizes_def
        generalizes_trans)
next
  fix N C1 C2
  assume "C1 \<doteq> C2"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding generalizes_def \<G>_F_def by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_generalizes_def generalizes_def \<G>_F_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  show "\<exists>l. L_Prec Old l"
    using L_Prec.simps(1) by blast
qed (auto simp: F_Inf_have_prems)

notation FL.Prec_FL (infix "\<sqsubset>" 50)
notation FL.entails_\<G>_L (infix "\<TTurnstile>\<inter>\<G>Le" 50)
notation FL.derive (infix "\<rhd>L" 50)
notation FL.step (infix "\<leadsto>GC" 50)
*)
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

(*
lemma \<open>finite N \<Longrightarrow> M \<TTurnstile>\<inter>e N \<Longrightarrow> \<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>e N\<close>
  sorry
*) 

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

(* lemma entails_\<G>_conj_compact: \<open>M \<TTurnstile>\<inter>\<G>e N \<Longrightarrow> \<forall> M' \<subseteq> M. finite M' \<longrightarrow> M' \<TTurnstile>\<inter>\<G>e N\<close>
proof (intro allI impI)
  fix M'
  assume
    M_entails_N: \<open>M \<TTurnstile>\<inter>\<G>e N\<close> and
    M'_subset_M: \<open>M' \<subseteq> M\<close> and
    finite_M': \<open>finite M'\<close> 
  then show \<open>M' \<TTurnstile>\<inter>\<G>e N\<close>
  proof (cases \<open>M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>)
    case True
    then show ?thesis
      using F.bot_entails_all F.entails_trans
      by blast
  next
    case False
    then have \<open>\<forall> M'' \<subseteq> M'. finite M'' \<longrightarrow> \<not> M'' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
      using unsat_\<G>_compact[of M'] F.entails_trans F.subset_entailed
      by blast
    then have \<open>\<not> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
      using finite_M'
      by blast 
    then show ?thesis
       
       oops *)
(*       sorry
  qed
qed
*) 


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

(*
lemma not_model_of_negation_is_model: \<open>\<not> I \<TTurnstile>s {{# -L #} | L. L \<in># C} \<longleftrightarrow> I \<TTurnstile>s {C}\<close>
  (is \<open>\<not> I \<TTurnstile>s ?negC \<longleftrightarrow> _\<close>)
proof (intro iffI notI)
  assume I_not_model_of_neg_C: \<open>\<not> I \<TTurnstile>s ?negC\<close>

  obtain Ls where
    Ls_def: \<open>Ls \<equiv> \<Union> C' \<in> ?negC. set_mset C'\<close>
    by blast 
  then have \<open>\<exists> C' \<in> ?negC. \<forall> L \<in># C'. \<not> I \<TTurnstile>l L\<close>
    using I_not_model_of_neg_C
    unfolding true_clss_def
    by (meson true_cls_def) 
  then have \<open>\<exists> L \<in> Ls. \<not> I \<TTurnstile>l L\<close> 
    using Ls_def
    by auto 
  then have \<open>\<exists> L \<in># C. \<not> I \<TTurnstile>l -L\<close>
    using Ls_def
    by force
  then have \<open>\<exists> L \<in># C. I \<TTurnstile>l L\<close>
    by (metis true_lit_def true_lit_iff uminus_literal_def) 
  then show \<open>I \<TTurnstile>s {C}\<close>
    unfolding true_clss_singleton true_cls_def
    by blast 
next
  assume
    I_model_of_C: \<open>I \<TTurnstile>s {C}\<close> and
    I_model_of_neg_C: \<open>I \<TTurnstile>s ?negC\<close>

  have \<open>\<exists> L \<in># C. I \<TTurnstile>l L\<close>
    using I_model_of_C true_cls_def
    by blast
  moreover have I_model_of_neg_C_def: \<open>\<forall> C' \<in> ?negC. \<exists> L \<in># C'. I \<TTurnstile>l L\<close>
    using I_model_of_neg_C
    by (meson true_cls_def true_clss_def)
  then obtain Ls where
    Ls_def: \<open>Ls \<equiv> \<Union> C' \<in> ?negC. set_mset C'\<close>
    by blast 
  then have \<open>\<forall> L \<in> Ls. I \<TTurnstile>l L\<close>
    by (smt (verit, ccfv_SIG) UN_iff I_model_of_neg_C_def add_mset_eq_single mem_Collect_eq
        multi_member_split)
  ultimately have \<open>\<exists> L \<in># C. I \<TTurnstile>l L \<and> I \<TTurnstile>l -L\<close>
    using Ls_def
    by fastforce 
  then show \<open>False\<close> 
    by auto 
qed

lemma Union_distrib_union: \<open>B \<noteq> {} \<Longrightarrow> A \<union> (\<Union> x \<in> B. f x) = (\<Union> x \<in> B. A \<union> f x)\<close>
  by blast 

lemma \<G>_F_not_empty: \<open>\<G>_F D \<noteq> {}\<close>
  unfolding \<G>_F_def
  using ex_ground_subst
  by blast

lemma interp_of_negation_not_interp: \<open>I \<TTurnstile>s \<G>_Fset {{# -L #} | L. L \<in># D} \<longleftrightarrow> \<not> I \<TTurnstile>s \<G>_F D\<close>
  unfolding \<G>_Fset_def \<G>_F_def
proof (intro iffI notI)
  assume
    I_model_of_neg_D: \<open>I \<TTurnstile>s (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close> and
    I_model_of_D: \<open>I \<TTurnstile>s {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close>

  have \<open>\<forall> C \<in> (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}). I \<TTurnstile> C\<close>
    using I_model_of_neg_D
    unfolding true_clss_def
    by blast 
  then have \<open>\<forall> L \<in># D. \<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>l -L \<cdot>l \<sigma>\<close>
    by fastforce 
  then have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> (\<forall> L \<in># D. I \<TTurnstile>l -(L \<cdot>l \<sigma>))\<close>
    by auto 
  moreover have \<open>\<forall> C \<in> {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}. I \<TTurnstile> C\<close>
    using I_model_of_D
    unfolding true_clss_def
    by blast 
  then have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile> D \<cdot> \<sigma>\<close>
    by blast 
  then have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> (\<exists> L \<in># D. I \<TTurnstile>l L \<cdot>l \<sigma>)\<close>
    unfolding true_cls_def
    by force 
  then have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> \<not> (\<forall> L \<in># D. I \<TTurnstile>l -(L \<cdot>l \<sigma>))\<close>
    by fastforce 
  ultimately show \<open>False\<close>
    using ex_ground_subst
    by presburger
next
  assume \<open>\<not> I \<TTurnstile>s {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}\<close>
  then have \<open>\<not> (\<forall> C \<in> {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}. I \<TTurnstile> C)\<close>
    unfolding true_clss_def
    by blast 
  then have \<open>\<exists> C \<in> {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}. \<not> I \<TTurnstile> C\<close>
    by blast
  then have \<open>\<exists> \<sigma>. is_ground_subst \<sigma> \<and> \<not> I \<TTurnstile> D \<cdot> \<sigma>\<close>
    by blast 
  then have \<open>\<exists> \<sigma>. is_ground_subst \<sigma> \<and> (\<forall> L \<in># D \<cdot> \<sigma>. \<not> I \<TTurnstile>l L)\<close>
    by blast 
  then have \<open>\<exists> \<sigma>. is_ground_subst \<sigma> \<and> (\<forall> L \<in># D. \<not> I \<TTurnstile>l L \<cdot>l \<sigma>)\<close>
    by fastforce 
  then have I_not_model_of_some_neg_D: \<open>\<forall> L \<in># D. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> \<not> I \<TTurnstile>l L \<cdot>l \<sigma>\<close>
    by blast 

  show \<open>I \<TTurnstile>s (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
  proof (rule ccontr)
    assume \<open>\<not> I \<TTurnstile>s (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
    then have \<open>\<exists> C \<in> (\<Union> C \<in> {{# -L #} | L. L \<in># D}. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}). \<not> I \<TTurnstile> C\<close>
      unfolding true_clss_def
      by blast 
    then have \<open>\<exists> L \<in># D. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> \<not> I \<TTurnstile>l -L \<cdot>l \<sigma>\<close>
      by force
    then have \<open>\<exists> L \<in># D. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> \<not> I \<TTurnstile>l -(L \<cdot>l \<sigma>)\<close>
      by simp 
    then have \<open>\<exists> L \<in># D. \<exists> \<sigma>. is_ground_subst \<sigma> \<and> I \<TTurnstile>l L \<cdot>l \<sigma>\<close>
      by (smt (verit, ccfv_SIG) atm_of_uminus is_pos_neg_not_is_pos true_lit_def) 
    then obtain L where
      L_in_D: \<open>L \<in># D\<close> and
      I_model_of_some_neg_D_2: \<open>\<exists> \<sigma>. is_ground_subst \<sigma> \<and> I \<TTurnstile>l L \<cdot>l \<sigma>\<close>
      by blast
    then show \<open>False\<close>
      (* TODO *)
      sorry
  qed
qed

lemma entails_\<G>_iff_entails_bot_single: \<open>M \<TTurnstile>\<inter>\<G>e {D} \<longleftrightarrow> M \<union> {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
proof (intro iffI)
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
next
  assume \<open>M \<union> {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  then have \<open>\<forall> I. I \<TTurnstile>s \<G>_Fset M \<longrightarrow> I \<TTurnstile>s \<G>_Fset {{# -L #} | L. L \<in># D} \<longrightarrow> I \<TTurnstile>s {{#}}\<close>
    using F_entails_\<G>_iff grounding_of_clss_def
    by fastforce
  then have \<open>\<forall> I. I \<TTurnstile>s \<G>_Fset M \<longrightarrow> \<not> I \<TTurnstile>s \<G>_F D \<longrightarrow> I \<TTurnstile>s {{#}}\<close>
    using interp_of_negation_not_interp
    by blast
  then have \<open>\<forall> I. I \<TTurnstile>s \<G>_Fset M \<longrightarrow> I \<TTurnstile>s \<G>_F D\<close>
    by blast 
  then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e \<G>_F D\<close>
    by blast 
  then show \<open>M \<TTurnstile>\<inter>\<G>e {D}\<close>
    unfolding F_entails_\<G>_iff \<G>_Fset_def
    by blast 



  (* then have \<open>\<G>_Fset M \<union> \<G>_Fset {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>e {{#}}\<close>
   *   unfolding F_entails_\<G>_iff \<G>_Fset_def
   *   by simp
   * then have \<open>\<G>_Fset M \<union> (\<Union> {{{# -L #} | L. L \<in># D'} | D'. D' \<in> \<G>_F D}) \<TTurnstile>\<inter>e {{#}}\<close>
   *   using neg_of_\<G>_F_lits_is_\<G>_F_of_neg_lits \<G>_Fset_def
   *   by presburger  
   * then have \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D. {{# -L #} | L. L \<in># D'}) \<TTurnstile>\<inter>e {{#}}\<close>
   *   by fast
   * then have \<open>(\<Union> D' \<in> \<G>_F D. \<G>_Fset M \<union> {{# -L #} | L. L \<in># D'}) \<TTurnstile>\<inter>e {{#}}\<close>
   * proof -
   *   have \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D. {{# -L #} | L. L \<in># D'}) =
   *     (\<Union> D' \<in> \<G>_F D. \<G>_Fset M \<union> {{# -L #} | L. L \<in># D'})\<close>
   *     using \<G>_F_not_empty Union_distrib_union
   *     by simp 
   *   then show \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D. {{# -L #} | L. L \<in># D'}) \<TTurnstile>\<inter>e {{#}} \<Longrightarrow>
   *     ?thesis\<close>
   *     by presburger 
   * qed
   * (\* ... *\)
   * then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e \<G>_F D\<close>
   *    
   *   sorry
   * then show \<open>M \<TTurnstile>\<inter>\<G>e {D}\<close>
   *   unfolding F_entails_\<G>_iff \<G>_Fset_def
   *   by fast  *)


  (* obtain D'' where
    D''_in_\<G>_F_D: \<open>D'' \<in> \<G>_F D\<close>
    using ex_ground_subst grounding_of_cls_def
    by fastforce

  assume \<open>M \<union> {{# -L #} | L. L \<in># D} \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  then have \<open>\<G>_Fset M \<union> (\<Union> (\<G>_F ` {{# -L #} | L. L \<in># D})) \<TTurnstile>\<inter>e {{#}}\<close>
    using F_entails_\<G>_iff grounding_of_clss_def
    by fastforce
  then have \<open>\<G>_Fset M \<union> (\<Union> {{{# -L #} | L. L \<in># D'} | D'. D' \<in> \<G>_F D}) \<TTurnstile>\<inter>e {{#}}\<close>
    using neg_of_\<G>_F_lits_is_\<G>_F_of_neg_lits
    by presburger
  then have \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D. {{# -L #} | L. L \<in># D'}) \<TTurnstile>\<inter>e {{#}}\<close>
    by auto
  then have
    \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D - {D''}. {{# -L #} | L. L \<in># D'}) \<union>
      {{# -L #} | L. L \<in># D''} \<TTurnstile>\<inter>e {{#}}\<close>
    using D''_in_\<G>_F_D
    by fastforce 
  then have \<open>\<G>_Fset M \<union> (\<Union> D' \<in> \<G>_F D - {D''}. {{# -L #} | L. L \<in># D'}) \<TTurnstile>\<inter>e {D''}\<close>
    using entails_iff_unsatisfiable_single[of _ D'']
    by (meson entails_bot_iff_unsatisfiable) 
  then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e {D''} \<union> (\<G>_F D - {D''})\<close>
    using entails_neg_swap
    by fastforce
  then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e \<G>_F D\<close>
    by simp  *)

  (* then show \<open>M \<TTurnstile>\<inter>\<G>e {D}\<close>
   *   using F_entails_\<G>_iff grounding_of_clss_def
   *   sorry *)
qed

lemma entails_\<G>_iff_entails_bot:
  \<open>M \<TTurnstile>\<inter>\<G>e N \<longleftrightarrow> (\<forall> D \<in> N. \<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> M \<union> {{# -L #} | L. L \<in># D \<cdot> \<sigma>} \<TTurnstile>\<inter>\<G>e {{#}})\<close>
  (* by (metis (no_types, lifting) F.entail_set_all_formulas entails_\<G>_iff_entails_bot_single)  *)
  sorry 

lemma entails_\<G>_bot_mono: \<open>M \<subseteq> M' \<Longrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}} \<Longrightarrow> M' \<TTurnstile>\<inter>\<G>e {{#}}\<close>
  using F.entails_trans F.subset_entailed
  by blast *)

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

(*
lemma entails_\<G>_conj_singleton_compact:
  \<open>M \<TTurnstile>\<inter>\<G>e {C} \<Longrightarrow> \<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e {C}\<close> 
proof -
  assume \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>
  then have \<open>\<G>_Fset M \<TTurnstile>\<inter>e \<G>_Fset {C}\<close>
    unfolding F_entails_\<G>_iff \<G>_Fset_def .
  then have \<open>I \<TTurnstile>s \<G>_Fset M \<Longrightarrow> I \<TTurnstile>s \<G>_Fset {C}\<close> for I
    by blast
  then have \<open>I \<TTurnstile>s (\<Union> C \<in> M. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}) \<Longrightarrow>
    I \<TTurnstile>s (\<Union> D \<in> {C}. {D \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>})\<close>
    for I
    unfolding \<G>_Fset_def \<G>_F_def
    by fast 
  then have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s M \<cdot>cs \<sigma> \<Longrightarrow> is_ground_subst \<sigma> \<Longrightarrow> I \<TTurnstile>s {C} \<cdot>cs \<sigma>\<close>
    for I \<sigma>
    using true_Union_grounding_of_cls_iff
    by meson
  then have \<open>is_ground_subst \<sigma> \<Longrightarrow> \<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s M \<cdot>cs \<sigma> \<Longrightarrow> I \<TTurnstile>s {C} \<cdot>cs \<sigma>\<close>
    sorry 
  then show ?thesis
    sorry 
qed
*)

(*
interpretation entails_\<G>_compact: concl_compact_consequence_relation
  \<open>{{#}} :: ('a :: wellorder) clause set\<close> \<open>(\<TTurnstile>\<inter>\<G>e)\<close>
proof (standard)
  fix M N :: \<open>('a :: wellorder) clause set\<close> 

  assume
    N_finite: \<open>finite N\<close> and
    M_entails_N: \<open>M \<TTurnstile>\<inter>\<G>e N\<close>
  then have \<open>\<forall> C \<in> N. M \<TTurnstile>\<inter>\<G>e {C}\<close>
    using F.entail_set_all_formulas
    by blast
  then have \<open>\<forall> C \<in> N. \<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e {C}\<close>
    using entails_\<G>_conj_singleton_compact
    by blast
  then obtain M'_of where
    \<open>\<forall> C \<in> N. M'_of C \<subseteq> M \<and> finite (M'_of C) \<and> M'_of C \<TTurnstile>\<inter>\<G>e {C}\<close>
    by moura
  then have
    Union_M'_subset_M: \<open>(\<Union> C \<in> N. M'_of C) \<subseteq> M\<close> and
    finite_Union_M': \<open>finite (\<Union> C \<in> N. M'_of C)\<close> and
    \<open>\<forall> C \<in> N. (\<Union> C \<in> N. M'_of C) \<TTurnstile>\<inter>\<G>e {C}\<close>
    using N_finite F_entails_\<G>_iff
    by auto
  then have \<open>(\<Union> C \<in> N. M'_of C) \<TTurnstile>\<inter>\<G>e N\<close>
    using F.all_formulas_entailed
    by blast
  then show \<open>\<exists> M' \<subseteq> M. finite M' \<and> M' \<TTurnstile>\<inter>\<G>e N\<close>
    using Union_M'_subset_M finite_Union_M'
    by blast 
qed
*)

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
\<close>
definition entails_\<G>_disj :: \<open>'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool\<close> (infix \<open>\<TTurnstile>\<union>\<G>e\<close> 50) where
  \<open>M \<TTurnstile>\<union>\<G>e N \<longleftrightarrow> M \<TTurnstile>\<inter>\<G>e {{#}} \<or> (\<exists> M' \<subseteq> M. finite M' \<and> (\<exists> C \<in> N. M' \<TTurnstile>\<inter>\<G>e {C}))\<close> 

text \<open>
  This is our own requirement: the two entailments must coincide on singleton sets.
\<close> 

(*
lemma entails_conj_is_entails_disj_on_singleton: \<open>M \<TTurnstile>\<inter>\<G>e {C} \<longleftrightarrow> M \<TTurnstile>\<union>\<G>e {C}\<close>
proof (intro iffI)
  assume M_entails_C: \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>
  then have \<open>\<exists> M' \<subseteq> M. finite M' \<and> (\<exists> C' \<in> {C}. M' \<TTurnstile>\<inter>\<G>e {C'})\<close>
    using entails_\<G>_conj_singleton_compact
    by fastforce 
  then show \<open>M \<TTurnstile>\<union>\<G>e {C}\<close> 
    unfolding entails_\<G>_disj_def
    by (intro disjI2)
next
  assume \<open>M \<TTurnstile>\<union>\<G>e {C}\<close>
  then consider
    (M_unsat) \<open>M \<TTurnstile>\<inter>\<G>e {{#}}\<close> |
    (b) \<open>\<exists> M' \<subseteq> M. finite M' \<and> (\<exists> C' \<in> {C}. M' \<TTurnstile>\<inter>\<G>e {C'})\<close>
    unfolding entails_\<G>_disj_def
    by blast 
  then show \<open>M \<TTurnstile>\<inter>\<G>e {C}\<close>
  proof cases
    case M_unsat
    then show ?thesis
      using F.bot_entails_all F.entails_trans
      by blast
  next
    case b
    then obtain M' where
      \<open>M' \<subseteq> M\<close> and
      \<open>finite M'\<close> and
      \<open>M' \<TTurnstile>\<inter>\<G>e {C}\<close>
      by blast 
    then show ?thesis
      using F.entails_trans F.subset_entailed
      by blast
  qed
qed
*)

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

(*
sublocale F'': Calculus.statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>\<union>\<G>e)" F.empty_ord.Red_Red_I
  F.Red_F_\<G>_empty
  (*using F.empty_ord.reduced_calc_is_calc F.empty_ord.stat_is_stat_red F_stat_comp_calc*)
  apply unfold_locales
  apply simp
  using F.bot_entails_all entails_\<G>_disj_def apply blast
  sledgehammer
  sorry
*)

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

(*
lemma \<open>F.Inf_between UNIV (F.Red_F_\<G>_empty N) \<subseteq> F.Red_I_\<G> N\<close>
  sketch
proof
  fix \<iota> :: "'a literal multiset inference"
  assume inf_from_red: "\<iota> \<in> F.Inf_between UNIV (F.Red_F_\<G>_empty N)"
  then have \<open>\<exists>C \<in> set (prems_of \<iota>). C \<in> F.Red_F_\<G>_empty N\<close>
    by (simp add: F.Inf_between_alt disjoint_iff_not_equal)
  then obtain C where \<open>C \<in> set (prems_of \<iota>)\<close> and \<open>C \<in> F.Red_F_\<G>_empty N\<close>
    by blast
  have \<open>\<iota> \<in> F_Inf\<close>
    using inf_from_red unfolding F.Inf_between_def F.Inf_from_def by blast
  moreover have \<open>\<G>_I_opt q \<iota> \<noteq> None \<longrightarrow> the (\<G>_I_opt q \<iota>) \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N))\<close> for q
  proof
    assume "\<G>_I_opt q \<iota> \<noteq> None"
    show "the (\<G>_I_opt q \<iota>) \<subseteq> G.Red_I q (\<Union> (\<G>_F ` N))"
      unfolding \<G>_I_def G.Red_I_def G.redundant_infer_def
      sorry
  qed
  moreover have \<open>\<G>_I_opt q \<iota> = None \<longrightarrow> \<G>_F (concl_of \<iota>) \<subseteq> \<Union> (\<G>_F ` N) \<union> G.Red_F (\<Union> (\<G>_F ` N))\<close> for q
    sorry
  ultimately have \<open>\<forall>q. \<iota> \<in> F.Red_I_\<G>_q q N\<close>
    unfolding F.Red_I_\<G>_q_def by blast
  then show "\<iota> \<in> F.Red_I_\<G> N"
    unfolding F.Red_I_\<G>_def by blast
qed



(* TODO: finish that proof!!! *)
lemma Inf_from_Red_F_subset_Red_I: \<open>F.Inf_between UNIV (F.Red_F_\<G>_empty N) \<subseteq> F.Red_I_\<G> N\<close> 
proof -
  have \<open>\<G>_I M \<iota> \<subseteq> G.Red_I M (\<G>_Fset N)\<close>
    if
      D_in_prems_\<iota>: \<open>C \<in> set (prems_of \<iota>)\<close> and
      grounds_of_D_red_to_grounds_of_N: \<open>\<G>_F C \<subseteq> G.Red_F (\<G>_Fset N)\<close> and
      C_is_FInf: \<open>\<iota> \<in> F_Inf\<close>
    for \<iota> C M
  proof (intro subsetI)
    fix \<iota>\<^sub>G
    assume \<open>\<iota>\<^sub>G \<in> \<G>_I M \<iota>\<close>
    then obtain \<rho> \<rho>s where
      \<rho>s_groundings: \<open>is_ground_subst \<rho>\<close> \<open>is_ground_subst_list \<rho>s\<close> and
      \<iota>\<^sub>G_is: \<open>\<iota>\<^sub>G = Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)\<close> and
      \<iota>\<^sub>G_is_GInf: \<open>\<iota>\<^sub>G \<in> G_Inf M\<close>
      unfolding \<G>_I_def
      by blast 

    have \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> C \<cdot> \<sigma> \<in> G.Red_F (\<G>_Fset N)\<close>
      using grounds_of_D_red_to_grounds_of_N
      unfolding \<G>_F_def
      by blast
    then have C_always_red_to_grounds_N:
      \<open>\<forall> \<sigma>. is_ground_subst \<sigma> \<longrightarrow> (\<exists> DD \<subseteq> \<G>_Fset N. DD \<TTurnstile>\<inter>e {C \<cdot> \<sigma>} \<and> (\<forall> D \<in> DD. D < C \<cdot> \<sigma>))\<close>
      unfolding G.Red_F_def
      by blast 

    have \<open>G.redundant_infer (\<G>_Fset N) \<iota>\<^sub>G\<close>
      unfolding G.redundant_infer_def 
    proof (cases \<open>\<exists> \<rho>'. \<rho>' \<in> set \<rho>s \<and> C \<cdot> \<rho>' \<in> set (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)\<close>) 
      case True
      then obtain \<rho>' where
        \<open>is_ground_subst \<rho>'\<close> and
        \<open>C \<cdot> \<rho>' \<in> set (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)\<close>
        by (meson \<rho>s_groundings(2) substitution_ops.is_ground_subst_list_def) 
      then obtain DD where
        \<open>DD \<subseteq> \<G>_Fset N\<close> and
        \<open>DD \<TTurnstile>\<inter>e {C \<cdot> \<rho>'}\<close> and
        \<open>\<forall> D \<in> DD. D < C \<cdot> \<rho>'\<close>
        using C_always_red_to_grounds_N
        by metis 
      then show \<open>\<exists> DD \<subseteq> \<G>_Fset N. DD \<union> set (side_prems_of \<iota>\<^sub>G) \<TTurnstile>\<inter>e {concl_of \<iota>\<^sub>G} \<and>
        (\<forall>D\<in>DD. D < main_prem_of \<iota>\<^sub>G)\<close>
        sorry
    next
      case False
      then show \<open>\<exists> DD \<subseteq> \<G>_Fset N. DD \<union> set (side_prems_of \<iota>\<^sub>G) \<TTurnstile>\<inter>e {concl_of \<iota>\<^sub>G} \<and>
        (\<forall>D\<in>DD. D < main_prem_of \<iota>\<^sub>G)\<close>
        sorry
    qed
    then show \<open>\<iota>\<^sub>G \<in> G.Red_I M (\<G>_Fset N)\<close>
      unfolding G.Red_I_def
      using \<iota>\<^sub>G_is_GInf
      by blast
  qed
  then show ?thesis
    unfolding F.Inf_between_def F.Inf_from_def F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def \<G>_Fset_def
      F.Red_I_\<G>_def F.Red_I_\<G>_q_def
    by auto 
qed
*)



(* proof (intro subsetI)
  fix \<iota>
  assume \<iota>_in_Inf_between_univ_N: \<open>\<iota> \<in> F.Inf_between UNIV (F.Red_F_\<G>_empty N)\<close>

  have \<iota>_is_FInf: \<open>\<iota> \<in> F_Inf\<close>
    using F.Inf_if_Inf_between \<iota>_in_Inf_between_univ_N
    by blast

  have \<open>\<iota> \<in> F.Inf_from (UNIV \<union> F.Red_F_\<G>_empty N) - F.Inf_from (UNIV - F.Red_F_\<G>_empty N)\<close>
    using F.Inf_between_def \<iota>_in_Inf_between_univ_N
    by presburger
  then have \<open>\<iota> \<in> F.Inf_from UNIV - F.Inf_from (- F.Red_F_\<G>_empty N)\<close>
    by (simp add: Compl_eq_Diff_UNIV)
  then have \<open>\<iota> \<in> F_Inf - { \<iota> \<in> F_Inf. set (prems_of \<iota>) \<subseteq> - F.Red_F_\<G>_empty N }\<close>
    by (simp add: F.Inf_from_def)
  then have \<open>\<iota> \<in> { \<iota> \<in> F_Inf. \<not> set (prems_of \<iota>) \<subseteq> - F.Red_F_\<G>_empty N }\<close>
    by blast 
  then have \<open>\<not> set (prems_of \<iota>) \<subseteq> - (F.Red_F_\<G>_empty N)\<close>
    by blast
  then have \<open>\<exists> C \<in> set (prems_of \<iota>). C \<in> F.Red_F_\<G>_empty N\<close>
    by blast
  then obtain C where
    \<open>C \<in> set (prems_of \<iota>)\<close> and
    \<open>C \<in> F.Red_F_\<G>_empty N\<close>
    by blast
  then have \<open>(\<exists> \<sigma>. D = C \<cdot> \<sigma> \<and> is_ground_subst \<sigma>) \<Longrightarrow> (\<exists> DD \<subseteq> \<Union> C \<in> N. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}.
    (\<forall> I. I \<TTurnstile>s DD \<longrightarrow> I \<TTurnstile> D) \<and> (\<forall> Da \<in> DD. Da < D))\<close> for D
    unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def 
    unfolding F.Red_F_\<G>_empty_def F.Red_F_\<G>_empty_q_def \<G>_F_def G.Red_F_def
    by auto 

  then have \<open>\<exists> DD \<subseteq> \<Union> C \<in> N. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}.
    (\<forall> I. I \<TTurnstile>s DD \<and> I \<TTurnstile>s set (butlast (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s)) \<longrightarrow> I \<TTurnstile> concl_of \<iota> \<cdot> \<rho>) \<and>
    (\<forall> D \<in> DD. D < last (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s))\<close>
    for \<rho>s \<rho>
     
    sorry 
  then have \<open>G.redundant_infer (\<Union> (\<G>_F ` N)) (Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>))\<close> 
    if
      \<rho>s_groundings: \<open>is_ground_subst_list \<rho>s\<close> \<open>is_ground_subst \<rho>\<close> and
      ground_\<iota>_is_Inf: \<open>Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> G_Inf q\<close>
    for q \<rho> \<rho>s
    unfolding G.redundant_infer_def \<G>_F_def
    by auto 
  then have \<open>\<iota>' \<in> G.Red_I q (\<G>_Fset N)\<close> 
    if \<iota>'_grounding_of_\<iota>: \<open>\<iota>' \<in> \<G>_I q \<iota>\<close>
    for \<iota>' q
    using \<iota>'_grounding_of_\<iota>
    unfolding \<G>_I_def G.Red_I_def \<G>_Fset_def
    by auto 
  then show \<open>\<iota> \<in> F.Red_I_\<G> N\<close>
    unfolding F.Red_I_\<G>_def F.Red_I_\<G>_q_def \<G>_Fset_def 
    by (auto simp add: \<iota>_is_FInf)
qed *) 

end (* locale FO_resolution_prover' *)



(* Since the set \<open>\<bbbP>\<close> of nullary predicates is left unspecified, we cannot define \<open>fml\<close> nor \<open>asn\<close>.
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

interpretation statically_complete_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> F.empty_ord.Red_Red_I
  F.Red_F_\<G>_empty
  using F_disj_complete .

interpretation LA_is_sound_calculus: sound_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
  F.empty_ord.Red_Red_I F.Red_F_\<G>_empty 
  using LA_is_calculus.Red_I_to_Inf LA_is_calculus.Red_F_Bot  LA_is_calculus.Red_F_of_subset 
        LA_is_calculus.Red_I_of_subset  LA_is_calculus.Red_F_of_Red_F_subset
        LA_is_calculus.Red_I_of_Red_F_subset LA_is_calculus.Red_I_of_Inf_to_N
  by (unfold_locales, presburger+) 

interpretation LA_is_AF_calculus: AF_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
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

sublocale splitting_calculus \<open>{#}\<close> F_Inf \<open>(\<TTurnstile>\<union>\<G>e)\<close> \<open>(\<TTurnstile>\<union>\<G>e)\<close>
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

notation LA_is_AF_calculus.AF_entails_sound (infix \<open>\<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F\<close> 50)
notation LA_is_AF_calculus.AF_entails (infix \<open>\<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F\<close> 50)

(*
lemma \<open>LA_is_AF_calculus.enabled_set \<N> J \<Longrightarrow> 
  ((LA_is_AF_calculus.fml_ext ` total_strip J \<union> sign.Pos ` (\<M> proj\<^sub>J J) \<TTurnstile>\<union>\<G>e\<^sub>\<sim> sign.Pos ` F_of ` \<N>)
  = (\<M> proj\<^sub>J J \<TTurnstile>\<union>\<G>e F_of ` \<N>))\<close>
  sorry

lemma sound_entails_equiv_entails: \<open>\<M> \<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F \<N> = LA_is_AF_calculus.AF_entails \<M> \<N>\<close>
  unfolding LA_is_AF_calculus.AF_entails_sound_def LA_is_AF_calculus.AF_entails_def 
 (* entails_\<G>_disj_cons_rel.entails_neg_def *)
  sorry

find_theorems LA_is_AF_calculus.AF_entails_sound
*)

(* Local static completeness (as other forms of completeness, global, dynamic...)
   follows from static completeness of the base calculus *)
theorem \<open>locally_saturated \<N> \<Longrightarrow> \<N> \<Turnstile>\<union>\<G>e\<^sub>A\<^sub>F {to_AF {#}} \<Longrightarrow> to_AF {#} \<in> \<N>\<close>
  using S_calculus_strong_statically_complete[OF F_disj_complete] .


(* Right. So it is seems that using the lifted entailment \<open>(\<TTurnstile>\<inter>\<G>e)\<close> does not work for our purpose.
 * We cannot prove compactness of this entailment, which we absolutely need to finish our proofs.
 * Unfortunately, everything else would have worked.
 * This means that all the work above needs to be changed somehow.
 *
 * First, we have to change the definition of our disjunctive entailment to get rid of the lifted
 * conjunctive entailment.
 * Once this is done, maybe we can try and see if any of this can actually be reused.
 * I certainly hope so, otherwise here goes 3 weeks of work on this.
 *
 *
 * Anything underneath this comment does not depend on the definition of the disjunctive entailment
 * (as long as the interpretations are correctly defined).
 * So this should be easy to reuse, if our (potentially new) redundancy criterion is indeed a correct
 * one.
 * At most, we'll have to change the names here and there, but that's all. *)





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

text \<open>
  We use the same naming convention as used in @{locale splitting_calculus_with_simps}, where
  $X\_pre$ is the condition which must hold for the rule to be applicable, and $X\_simp$ is
  the simplification rule itself.
\<close>

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
(*>*)


(* Report theorem 14 for the case BinSplit *) 
theorem Simps_are_sound: \<open>\<iota> \<in> Simps \<Longrightarrow> \<forall> \<C> \<in> S_to \<iota>. S_from \<iota> \<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F {\<C>}\<close>
proof (intro ballI)
  fix \<C>
  assume \<open>\<iota> \<in> Simps\<close> and 
         \<C>_in_concl: \<open>\<C> \<in> S_to \<iota>\<close>
  then show \<open>S_from \<iota> \<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F {\<C>}\<close>
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
        (* /!\ Slow /!\ *)
        by (smt (verit) Un_upper2 consequence_relation.entails_subsets
            entails_\<G>_disj_cons_rel.ext_cons_rel finsert.rep_eq fml_entails_C image_eqI
            insert_subset subset_iff sup_ge1) 
      then have \<open>\<forall> J. fset (finsert a A) \<subseteq> total_strip J \<longrightarrow>
        map_sign fml ` total_strip J \<union> sign.Pos ` ({AF.Pair (C \<union># D) A} proj\<^sub>J J) \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos C}\<close>
        unfolding LA_is_AF_calculus.enabled_projection_def LA_is_AF_calculus.enabled_def
        by simp 
      then show \<open>{AF.Pair (C \<union># D) A} \<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F {AF.Pair C (finsert a A)}\<close>
        unfolding LA_is_AF_calculus.AF_entails_sound_def LA_is_AF_calculus.enabled_set_def
                  LA_is_AF_calculus.enabled_def
        using LA_is_AF_calculus.fml_ext_is_mapping
        by auto 
    next
      let ?fml = \<open>\<lambda> J. map_sign fml ` total_strip J\<close> 

      have \<open>{C \<union># D} \<TTurnstile>\<union>\<G>e {C, D}\<close>
        using C_u_D_splittable
        unfolding splittable_def 
        by auto 
      then have \<open>{sign.Neg C} \<union> {sign.Pos (C \<union># D)} \<TTurnstile>\<union>\<G>e\<^sub>\<sim> {sign.Pos D}\<close>
        unfolding entails_\<G>_disj_cons_rel.entails_neg_def
        by auto 
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
      then show \<open>{AF.Pair (C \<union># D) A} \<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F {AF.Pair D (finsert (neg a) A)}\<close>
        unfolding LA_is_AF_calculus.AF_entails_sound_def LA_is_AF_calculus.enabled_set_def
                  LA_is_AF_calculus.enabled_def 
        using LA_is_AF_calculus.fml_ext_is_mapping
        by auto 
    qed 
  qed
qed



interpretation SInf_sound:
  Preliminaries_With_Zorn.sound_inference_system SInf \<open>to_AF {#}\<close> \<open>(\<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F)\<close>
  by (meson LA_is_AF_calculus.AF_ext_sound_cons_rel SInf_sound_wrt_entails_sound
      Preliminaries_With_Zorn.sound_inference_system.intro
      Preliminaries_With_Zorn.sound_inference_system_axioms.intro) 

interpretation Simps_simplifies: sound_simplification_rules \<open>to_AF {#}\<close> SInf \<open>(\<TTurnstile>\<union>\<G>e\<^sub>A\<^sub>F)\<close> Simps
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















(* Ignore everything under this comment, for now. *)




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