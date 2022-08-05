(* Title:        Fair DISCOUNT Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Fair DISCOUNT Loop\<close>

theory Fair_DISCOUNT_Loop
  imports
    DISCOUNT_Loop
    Passive_Set
    Weighted_Path_Order.Multiset_Extension_Pair
begin


subsection \<open>Setup and Utility\<close>

hide_const (open) Seq.chain

lemma finite_imp_set_eq:
  assumes fin: "finite A"
  shows "\<exists>xs. set xs = A"
  using fin
proof (induct A rule: finite_induct)
  case empty
  then show ?case
    by auto
next
  case (insert x B)
  then obtain xs :: "'a list" where
    "set xs = B"
    by blast
  then have "set (x # xs) = insert x B"
    by auto
  then show ?case
    by blast
qed


section \<open>Locale\<close>

type_synonym ('p, 'f) fair_DL_state = "'p \<times> 'f option \<times> 'f fset"

datatype 'f passive_elem =
  Passive_Inference "'f inference"
| Passive_Formula 'f

locale fair_discount_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  fair_passive_set empty select add remove felems
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Inf_G_q :: "'q \<Rightarrow> 'g inference set" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<doteq>\<close> 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<prec>\<cdot>\<close> 50) and
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f passive_elem" and
    add :: "'f passive_elem \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f passive_elem \<Rightarrow> 'p \<Rightarrow> 'p" and
    felems :: "'p \<Rightarrow> 'f passive_elem fset" +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_Prec_S: "minimal_element (\<prec>S) UNIV" and
    transp_Prec_S: "transp (\<prec>S)" and
    finite_Inf_between: "finite A \<Longrightarrow> finite (no_labels.Inf_between A {C})"
begin

lemma trans_Prec_S: "trans {(x, y). x \<prec>S y}"
  using transp_Prec_S transp_trans by blast

lemma irreflp_Prec_S: "irreflp (\<prec>S)"
  using minimal_element.wf wfP_imp_irreflp wf_Prec_S wfp_on_UNIV by blast

lemma irrefl_Prec_S: "irrefl {(x, y). x \<prec>S y}"
  by (metis CollectD case_prod_conv irrefl_def irreflp_Prec_S irreflp_def)


subsection \<open>Definition and Lemmas\<close>

abbreviation passive_of :: "('p, 'f) fair_DL_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst St"
abbreviation yy_of :: "('p, 'f) fair_DL_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd St)"
abbreviation active_of :: "('p, 'f) fair_DL_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd St)"

definition passive_inferences_of :: "'p \<Rightarrow> 'f inference set" where
  "passive_inferences_of P = {\<iota>. Passive_Inference \<iota> \<in> elems P}"
definition passive_formulas_of :: "'p \<Rightarrow> 'f set" where
  "passive_formulas_of P = {C. Passive_Formula C \<in> elems P}"

abbreviation all_formulas_of :: "('p, 'f) fair_DL_state \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> passive_formulas_of (passive_of St) \<union> set_option (yy_of St) \<union>
     fset (active_of St)"

lemma passive_inferences_of_empty[simp]: "passive_inferences_of empty = {}"
  unfolding passive_inferences_of_def by simp

lemma passive_inferences_of_add_Passive_Inference[simp]:
  "passive_inferences_of (add (Passive_Inference \<iota>) P) = {\<iota>} \<union> passive_inferences_of P"
  unfolding passive_inferences_of_def by auto

lemma passive_inferences_of_add_Passive_Formula[simp]:
  "passive_inferences_of (add (Passive_Formula C) P) = passive_inferences_of P"
  unfolding passive_inferences_of_def by auto

lemma passive_inferences_of_fold_add_Passive_Inference[simp]:
  "passive_inferences_of (fold (add \<circ> Passive_Inference) \<iota>s P) = passive_inferences_of P \<union> set \<iota>s"
  by (induct \<iota>s arbitrary: P) auto

lemma passive_inferences_of_fold_add_Passive_Formula[simp]:
  "passive_inferences_of (fold (add \<circ> Passive_Formula) Cs P) = passive_inferences_of P"
  by (induct Cs arbitrary: P) auto

lemma passive_inferences_of_remove_Passive_Inference[simp]:
  "passive_inferences_of (remove (Passive_Inference \<iota>) P) = passive_inferences_of P - {\<iota>}"
  unfolding passive_inferences_of_def by auto

lemma passive_inferences_of_remove_Passive_Formula[simp]:
  "passive_inferences_of (remove (Passive_Formula C) P) = passive_inferences_of P"
  unfolding passive_inferences_of_def by auto

lemma passive_inferences_of_fold_remove_Passive_Inference[simp]:
  "passive_inferences_of (fold (remove \<circ> Passive_Inference) \<iota>s P) = passive_inferences_of P - set \<iota>s"
  by (induct \<iota>s arbitrary: P) auto

lemma passive_inferences_of_fold_remove_Passive_Formula[simp]:
  "passive_inferences_of (fold (remove \<circ> Passive_Formula) Cs P) = passive_inferences_of P"
  by (induct Cs arbitrary: P) auto

lemma passive_formulas_of_empty[simp]: "passive_formulas_of empty = {}"
  unfolding passive_formulas_of_def by simp

lemma passive_formulas_of_add_Passive_Inference[simp]:
  "passive_formulas_of (add (Passive_Inference \<iota>) P) = passive_formulas_of P"
  unfolding passive_formulas_of_def by auto

lemma passive_formulas_of_add_Passive_Formula[simp]:
  "passive_formulas_of (add (Passive_Formula C) P) = {C} \<union> passive_formulas_of P"
  unfolding passive_formulas_of_def by auto

lemma passive_formulas_of_fold_add_Passive_Inference[simp]:
  "passive_formulas_of (fold (add \<circ> Passive_Inference) \<iota>s P) = passive_formulas_of P"
  by (induct \<iota>s arbitrary: P) auto

lemma passive_formulas_of_fold_add_Passive_Formula[simp]:
  "passive_formulas_of (fold (add \<circ> Passive_Formula) Cs P) = passive_formulas_of P \<union> set Cs"
  by (induct Cs arbitrary: P) auto

lemma passive_formulas_of_remove_Passive_Inference[simp]:
  "passive_formulas_of (remove (Passive_Inference \<iota>) P) = passive_formulas_of P"
  unfolding passive_formulas_of_def by auto

lemma passive_formulas_of_remove_Passive_Formula[simp]:
  "passive_formulas_of (remove (Passive_Formula C) P) = passive_formulas_of P - {C}"
  unfolding passive_formulas_of_def by auto

lemma passive_formulas_of_fold_remove_Passive_Inference[simp]:
  "passive_formulas_of (fold (remove \<circ> Passive_Inference) \<iota>s P) = passive_formulas_of P"
  by (induct \<iota>s arbitrary: P) auto

lemma passive_formulas_of_fold_remove_Passive_Formula[simp]:
  "passive_formulas_of (fold (remove \<circ> Passive_Formula) Cs P) = passive_formulas_of P - set Cs"
  by (induct Cs arbitrary: P) auto

fun fstate :: "'p \<times> 'f option \<times> 'f fset \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set" where
  "fstate (P, Y, A) = state (passive_inferences_of P, passive_formulas_of P, set_option Y, fset A)"

lemma fstate_alt_def:
  "fstate St = state (passive_inferences_of (fst St), passive_formulas_of (fst St),
     set_option (fst (snd St)), fset (snd (snd St)))"
  by (cases St) auto

definition
  Liminf_fstate :: "('p, 'f) fair_DL_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_fstate Sts =
   (Liminf_llist (lmap (passive_formulas_of \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap (fset \<circ> active_of) Sts))"

lemma Liminf_fstate_commute:
  "Liminf_llist (lmap (snd \<circ> fstate) Sts) = labeled_formulas_of (Liminf_fstate Sts)"
proof -
  have "Liminf_llist (lmap (snd \<circ> fstate) Sts) =
    (\<lambda>C. (C, Passive)) ` Liminf_llist (lmap (passive_formulas_of \<circ> passive_of) Sts) \<union>
    (\<lambda>C. (C, YY)) ` Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<union>
    (\<lambda>C. (C, Active)) ` Liminf_llist (lmap (fset \<circ> active_of) Sts)"
    unfolding fstate_alt_def state_alt_def
    apply simp
    apply (subst Liminf_llist_lmap_union, fast)+
    apply (subst Liminf_llist_lmap_image, simp add: inj_on_convol_ident)+
    by auto
 thus ?thesis
   unfolding Liminf_fstate_def by fastforce
qed

fun formulas_union :: "'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f set" where
  "formulas_union (P, Y, A) = P \<union> Y \<union> A"

inductive
  fair_DL :: "('p, 'f) fair_DL_state \<Rightarrow> ('p, 'f) fair_DL_state \<Rightarrow> bool" (infix "\<leadsto>DLf" 50)
where
  compute_infer: "P \<noteq> empty \<Longrightarrow> select P = Passive_Inference \<iota> \<Longrightarrow>
    \<iota> \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| choose_p: "P \<noteq> empty \<Longrightarrow> select P = Passive_Formula C \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, Some C', A)"
| delete_bwd: "C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (P, Some C, A)"
| simplify_bwd: "C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (add (Passive_Formula C'') P, Some C, A)"
| schedule_infer: "set \<iota>s = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (fold (add \<circ> Passive_Inference) \<iota>s P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<noteq> [] \<Longrightarrow> set \<iota>s \<subseteq> passive_inferences_of P \<Longrightarrow>
    set \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (P, Y, A) \<leadsto>DLf (fold (remove \<circ> Passive_Inference) \<iota>s P, Y, A)"


subsection \<open>Initial State\<close>

inductive is_initial_fair_DL_state :: "('p, 'f) fair_DL_state \<Rightarrow> bool" where
  "passive_inferences_of P = {\<iota> \<in> Inf_F. prems_of \<iota> = []} \<Longrightarrow>
   is_initial_fair_DL_state (P, None, {||})"


subsection \<open>Invariant\<close>

inductive fair_DL_invariant :: "('p, 'f) fair_DL_state \<Rightarrow> bool" where
  "passive_inferences_of P \<subseteq> Inf_F \<Longrightarrow> fair_DL_invariant (P, Y, A)"

lemma initial_fair_DL_invariant: "is_initial_fair_DL_state St \<Longrightarrow> fair_DL_invariant St"
  unfolding is_initial_fair_DL_state.simps fair_DL_invariant.simps by auto

lemma step_fair_DL_invariant:
  assumes
    inv: "fair_DL_invariant St" and
    step: "St \<leadsto>DLf St'"
  shows "fair_DL_invariant St'"
  using step inv
proof cases
  case (schedule_infer \<iota>s A C P)
  note defs = this(1,2) and \<iota>s_inf_betw = this(3)
  have \<iota>s_inf: "set \<iota>s \<subseteq> Inf_F"
    using \<iota>s_inf_betw unfolding no_labels.Inf_between_def no_labels.Inf_from_def by auto
  show ?thesis
    using inv \<iota>s_inf unfolding defs
    by (auto simp: fair_DL_invariant.simps passive_inferences_of_def fold_map[symmetric])
qed (auto simp: fair_DL_invariant.simps passive_inferences_of_def fold_map[symmetric])

lemma chain_fair_DL_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>DLf) Sts" and
    fair_hd: "fair_DL_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "fair_DL_invariant (lnth Sts i)"
  using i_lt
proof (induct i)
  case 0
  thus ?case
    using fair_hd lhd_conv_lnth zero_enat_def by fastforce
next
  case (Suc i)
  note ih = this(1) and si_lt = this(2)

  have "enat i < llength Sts"
    using si_lt Suc_ile_eq nless_le by blast
  hence inv_i: "fair_DL_invariant (lnth Sts i)"
    by (rule ih)
  have step: "lnth Sts i \<leadsto>DLf lnth Sts (Suc i)"
    using chain chain_lnth_rel si_lt by blast

  show ?case
    by (rule step_fair_DL_invariant[OF inv_i step])
qed

lemma chain_fair_DL_invariant_llast:
  assumes
    chain: "chain (\<leadsto>DLf) Sts" and
    fair_hd: "fair_DL_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "fair_DL_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    using i by (metis chain chain_length_pos diff_less enat_ord_simps(2) less_numeral_extra(1)
        zero_enat_def)

  show ?thesis
    using chain_fair_DL_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

inductive is_final_fair_DL_state :: "('p, 'f) fair_DL_state \<Rightarrow> bool" where
  "is_final_fair_DL_state (empty, None, A)"

lemma is_final_fair_DL_state_iff_no_DLf_step:
  assumes inv: "fair_DL_invariant St"
  shows "is_final_fair_DL_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>DLf St')"
proof
  assume "is_final_fair_DL_state St"
  then obtain A :: "'f fset" where
    st: "St = (empty, None, A)"
    by (auto simp: is_final_fair_DL_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>DLf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "(empty, None, A) \<leadsto>DLf St'"
    thus False
      by cases auto
  qed
next
  assume no_step: "\<forall>St'. \<not> St \<leadsto>DLf St'"
  show "is_final_fair_DL_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_fair_DL_state St"

    obtain P :: 'p and Y :: "'f option" and A :: "'f fset" where
      st: "St = (P, Y, A)"
      by (cases St)

    have "P \<noteq> empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_fair_DL_state.simps by auto
    moreover {
      assume
        p: "P \<noteq> empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>DLf St'"
      proof (cases "select P")
        case sel: (Passive_Inference \<iota>)
        hence \<iota>_inf: "\<iota> \<in> Inf_F"
          using inv p unfolding st by (metis fair_DL_invariant.cases fst_conv mem_Collect_eq
              passive_inferences_of_def select_in_elems subset_iff)
        have \<iota>_red: "\<iota> \<in> no_labels.Red_I_\<G> (fset A \<union> {concl_of \<iota>})"
          using \<iota>_inf no_labels.empty_ord.Red_I_of_Inf_to_N by auto
        show ?thesis
          using fair_DL.compute_infer[OF p sel \<iota>_red] unfolding st p y by blast
      next
        case (Passive_Formula C)
        then show ?thesis
          using fair_DL.choose_p[OF p] unfolding st p y by fast
      qed
    } moreover {
      assume "Y \<noteq> None"
      then obtain C :: 'f where
        y: "Y = Some C"
        by blast

      have fin: "finite (no_labels.Inf_between (fset A) {C})"
        by (rule finite_Inf_between[of "fset A", simplified])
      obtain \<iota>s :: "'f inference list" where
        \<iota>s: "set \<iota>s = no_labels.Inf_between (fset A) {C}"
        using finite_imp_set_eq[OF fin] by blast

      have "\<exists>St'. St \<leadsto>DLf St'"
        using fair_DL.schedule_infer[OF \<iota>s] unfolding st y by fast
    } ultimately show False
      using no_step by force
  qed
qed


subsection \<open>Refinement\<close>

lemma fair_DL_step_imp_DL_step:
  assumes dlf: "(P, Y, A) \<leadsto>DLf (P', Y', A')"
  shows "fstate (P, Y, A) \<leadsto>DL fstate (P', Y', A')"
  using dlf
proof cases
  case (compute_infer \<iota> C)
  note defs = this(1-4) and p_nemp = this(5) and sel = this(6) and \<iota>_red = this(7)

  have pas_min_\<iota>_uni_\<iota>: "passive_inferences_of P - {\<iota>} \<union> {\<iota>} = passive_inferences_of P"
    by (metis Un_insert_right insert_Diff_single insert_absorb mem_Collect_eq p_nemp
        passive_inferences_of_def sel select_in_elems sup_bot.right_neutral)

  show ?thesis
    unfolding defs fstate_alt_def
    using DL.compute_infer[OF \<iota>_red,
        of "passive_inferences_of (remove (select P) P)" "passive_formulas_of P"]
    unfolding sel
    by (simp only: prod.sel option.set passive_inferences_of_remove_Passive_Inference
        passive_formulas_of_remove_Passive_Inference pas_min_\<iota>_uni_\<iota>)
next
  case (choose_p C)
  note defs = this(1-4) and p_nemp = this(5) and sel = this(6)

  have pas_min_c_uni_c: "passive_formulas_of P - {C} \<union> {C} = passive_formulas_of P"
    by (metis Un_insert_right insert_Diff mem_Collect_eq p_nemp passive_formulas_of_def sel
        select_in_elems sup_bot.right_neutral)

  show ?thesis
    unfolding defs fstate_alt_def
    using DL.choose_p[of "passive_inferences_of P" "passive_formulas_of (remove (select P) P)" C
        "fset A"]
    unfolding sel by (simp only: prod.sel option.set passive_formulas_of_remove_Passive_Formula
        passive_inferences_of_remove_Passive_Formula pas_min_c_uni_c)
next
  case (delete_fwd C)
  note defs = this(1-4) and c_in = this(5)
  show ?thesis
    unfolding defs fstate_alt_def using DL.delete_fwd[OF c_in] by simp
next
  case (simplify_fwd C' C)
  note defs = this(1-4) and c_in = this(6)
  show ?thesis
    unfolding defs fstate_alt_def using DL.simplify_fwd[OF c_in] by simp
next
  case (delete_bwd C' C)
  note defs = this(1-4) and c_in = this(5)
  show ?thesis
    unfolding defs fstate_alt_def using DL.delete_bwd[OF c_in] by simp
next
  case (simplify_bwd C'' C' C)
  note defs = this(1-4) and c_in = this(6)
  show ?thesis
    unfolding defs fstate_alt_def using DL.simplify_bwd[OF c_in] by simp
next
  case (schedule_infer \<iota>s C)
  note defs = this(1-4) and \<iota>s = this(5)
  show ?thesis
    unfolding defs fstate_alt_def
    using DL.schedule_infer[OF \<iota>s, of "passive_inferences_of P" "passive_formulas_of P"] by simp
next
  case (delete_orphan_infers \<iota>s)
  note defs = this(1-3) and \<iota>s_ne = this(4) and \<iota>s_pas = this(5) and inter = this(6)

  have pas_min_\<iota>s_uni_\<iota>s: "passive_inferences_of P - set \<iota>s \<union> set \<iota>s = passive_inferences_of P"
    by (simp add: \<iota>s_pas set_eq_subset)

  show ?thesis
    unfolding defs fstate_alt_def
    using DL.delete_orphan_infers[OF inter,
        of "passive_inferences_of (fold (remove \<circ> Passive_Inference) \<iota>s P)"
        "passive_formulas_of P" "set_option Y"]
    by (simp only: prod.sel passive_inferences_of_fold_remove_Passive_Inference
        passive_formulas_of_fold_remove_Passive_Inference pas_min_\<iota>s_uni_\<iota>s)
qed

lemma fair_DL_step_imp_GC_step:
  "(P, Y, A) \<leadsto>DLf (P', Y', A') \<Longrightarrow> fstate (P, Y, A) \<leadsto>LGC fstate (P', Y', A')"
  by (rule DL_step_imp_LGC_step[OF fair_DL_step_imp_DL_step])


subsection \<open>Completeness\<close>

theorem
  assumes
    full: "full_chain (\<leadsto>DLf) Sts" and
    init: "is_initial_fair_DL_state (lhd Sts)" and
    bot: "B \<in> Bot_F" and
    unsat: "concl_of ` passive_inferences_of (passive_of (lhd Sts)) \<union>
      passive_formulas_of (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"
  shows
    DL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> formulas_union (Liminf_fstate Sts)" and
    DL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
proof -
  have chain: "chain (\<leadsto>DLf) Sts"
    by (rule full_chain_imp_chain[OF full])
  have lgc_chain: "chain (\<leadsto>LGC) (lmap fstate Sts)"
    using chain fair_DL_step_imp_GC_step chain_lmap by (smt (verit) fstate.cases)

  have inv: "fair_DL_invariant (lhd Sts)"
    using init unfolding is_initial_fair_DL_state.simps fair_DL_invariant.simps by fast

  have nnul: "\<not> lnull Sts"
    using chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_fair_DL_state.cases init snd_conv)
  hence act: "active_subset (snd (lhd (lmap fstate Sts))) = {}"
    unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas_fml: "passive_subset (Liminf_llist (lmap (snd \<circ> fstate) Sts)) = {}"
    sorry
(*
  proof (cases "lfinite Sts")
    case fin: True

    have lim: "Liminf_llist (lmap fstate Sts) = fstate (llast Sts)"
      using lfinite_Liminf_llist fin nnul
      by (metis chain_not_lnull gc_chain lfinite_lmap llast_lmap)

    have last_inv: "fair_DL_invariant (llast Sts)"
      by (rule chain_fair_DL_invariant_llast[OF chain inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>DLf St'"
      using full_chain_lnth_not_rel[OF full] by (metis fin full_chain_iff_chain full)
    hence "is_final_fair_DL_state (llast Sts)"
      unfolding is_final_fair_DL_state_iff_no_DLf_step[OF last_inv] .
    then obtain A :: "'f fset" where
      at_l: "llast Sts = ({||}, None, empty, None, A)"
      unfolding is_final_fair_DL_state.simps by blast
    show ?thesis
      unfolding is_final_fair_DL_state.simps passive_subset_def lim at_l by auto
  next
    case False
    hence len: "llength Sts = \<infinity>"
      by (simp add: not_lfinite_llength)
    show ?thesis
      unfolding Liminf_fstate_commute passive_subset_def Liminf_fstate_def
      using fair_DL_Liminf_new_empty[OF len full inv]
        fair_DL_Liminf_xx_empty[OF len full inv]
        fair_DL_Liminf_passive_empty[OF len full init]
        fair_DL_Liminf_yy_empty[OF full inv]
      by simp
  qed
*)

  have no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd (lmap fstate Sts))"
    sorry
  thm lgc_complete_Liminf

  have pas_inf: "Liminf_llist (lmap (fst \<circ> fstate) Sts) = {}"
    sorry

  have unsat': "fst ` snd (lhd (lmap fstate Sts)) \<Turnstile>\<inter>\<G> {B}"
    sorry
(*
    using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)
*)

  have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap (snd \<circ> fstate) Sts)"
    by (rule lgc_complete_Liminf[of "lmap fstate Sts", unfolded llist.map_comp,
          OF lgc_chain act pas_fml no_prems_init pas_inf bot unsat'])
  thus "\<exists>B \<in> Bot_F. B \<in> formulas_union (Liminf_fstate Sts)"
    unfolding Liminf_fstate_def Liminf_fstate_commute by auto
  thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
    unfolding Liminf_fstate_def Liminf_llist_def by auto
qed

end


subsection \<open>Specialization with FIFO Queue\<close>

text \<open>As a proof of concept, we specialize the passive set to use a FIFO queue,
thereby eliminating the locale assumptions about the passive set.\<close>

locale fifo_discount_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Inf_G_q :: "'q \<Rightarrow> 'g inference set" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<doteq>\<close> 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<prec>\<cdot>\<close> 50) +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_Prec_S: "minimal_element (\<prec>S) UNIV" and
    transp_Prec_S: "transp (\<prec>S)" and
    finite_Inf_between: "finite A \<Longrightarrow> finite (no_labels.Inf_between A {C})"
begin

sublocale fifo_passive_set
  .

sublocale fair_discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F "[]" hd "\<lambda>y xs. xs @ [y]" removeAll fset_of_list Prec_S
proof unfold_locales
  show "po_on (\<prec>S) UNIV"
    using wf_Prec_S minimal_element.po by blast
next
  show "wfp_on (\<prec>S) UNIV"
    using wf_Prec_S minimal_element.wf by blast
next
  show "transp (\<prec>S)"
    by (rule transp_Prec_S)
next
  show "\<And>A C. finite A \<Longrightarrow> finite (no_labels.Inf_between A {C})"
    by (fact finite_Inf_between)
qed

end

end
