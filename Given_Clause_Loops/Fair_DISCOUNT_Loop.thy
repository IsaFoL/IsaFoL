(* Title:        Fair DISCOUNT Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Fair DISCOUNT Loop\<close>

text \<open>The fair DISCOUNT loop assumes that the passive queue is fair and
ensures (dynamic) refutational completeness under that assumption.\<close>

theory Fair_DISCOUNT_Loop
  imports
    Given_Clause_Loops_Util
    DISCOUNT_Loop
    Prover_Queue
begin


subsection \<open>Locale\<close>

type_synonym ('p, 'f) DLf_state = "'p \<times> 'f option \<times> 'f fset"

datatype 'f passive_elem =
  is_passive_inference: Passive_Inference (passive_inference: "'f inference")
| is_passive_formula: Passive_Formula (passive_formula: 'f)

lemma passive_inference_filter:
  "passive_inference ` Set.filter is_passive_inference N = {\<iota>. Passive_Inference \<iota> \<in> N}"
  by force

lemma passive_formula_filter:
  "passive_formula ` Set.filter is_passive_formula N = {C. Passive_Formula C \<in> N}"
  by force

locale fair_discount_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  fair_prover_queue empty select add remove felems
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
    empty :: 'p and
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


subsection \<open>Basic Definitions and Lemmas\<close>

abbreviation passive_of :: "('p, 'f) DLf_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst St"
abbreviation yy_of :: "('p, 'f) DLf_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd St)"
abbreviation active_of :: "('p, 'f) DLf_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd St)"

definition passive_inferences_of :: "'p \<Rightarrow> 'f inference set" where
  "passive_inferences_of P = {\<iota>. Passive_Inference \<iota> \<in> elems P}"
definition passive_formulas_of :: "'p \<Rightarrow> 'f set" where
  "passive_formulas_of P = {C. Passive_Formula C \<in> elems P}"

lemma finite_passive_inferences_of: "finite (passive_inferences_of P)"
proof -
  have inj_pi: "inj Passive_Inference"
    unfolding inj_on_def by auto
  show ?thesis
    unfolding passive_inferences_of_def by (auto intro: finite_inverse_image[OF _ inj_pi])
qed

lemma finite_passive_formulas_of: "finite (passive_formulas_of P)"
proof -
  have inj_pi: "inj Passive_Formula"
    unfolding inj_on_def by auto
  show ?thesis
    unfolding passive_formulas_of_def by (auto intro: finite_inverse_image[OF _ inj_pi])
qed

abbreviation all_formulas_of :: "('p, 'f) DLf_state \<Rightarrow> 'f set" where
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

fun fstate :: "('p, 'f) DLf_state \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set" where
  "fstate (P, Y, A) = state (passive_inferences_of P, passive_formulas_of P, set_option Y, fset A)"

lemma fstate_alt_def:
  "fstate St = state (passive_inferences_of (fst St), passive_formulas_of (fst St),
     set_option (fst (snd St)), fset (snd (snd St)))"
  by (cases St) auto

definition Liminf_fstate :: "('p, 'f) DLf_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set" where
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

inductive fair_DL :: "('p, 'f) DLf_state \<Rightarrow> ('p, 'f) DLf_state \<Rightarrow> bool" (infix "\<leadsto>DLf" 50) where
  compute_infer: "P \<noteq> empty \<Longrightarrow> select P = Passive_Inference \<iota> \<Longrightarrow>
    \<iota> \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| choose_p: "P \<noteq> empty \<Longrightarrow> select P = Passive_Formula C \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, Some C', A)"
| delete_bwd: "C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (P, Some C, A)"
| simplify_bwd: "C' |\<notin>| A \<Longrightarrow> C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (add (Passive_Formula C'') P, Some C, A)"
| schedule_infer: "set \<iota>s = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (fold (add \<circ> Passive_Inference) \<iota>s P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<noteq> [] \<Longrightarrow> set \<iota>s \<subseteq> passive_inferences_of P \<Longrightarrow>
    set \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (P, Y, A) \<leadsto>DLf (fold (remove \<circ> Passive_Inference) \<iota>s P, Y, A)"


subsection \<open>Initial State and Invariant\<close>

inductive is_initial_DLf_state :: "('p, 'f) DLf_state \<Rightarrow> bool" where
  "is_initial_DLf_state (empty, None, {||})"

inductive DLf_invariant :: "('p, 'f) DLf_state \<Rightarrow> bool" where
  "passive_inferences_of P \<subseteq> Inf_F \<Longrightarrow> DLf_invariant (P, Y, A)"

lemma initial_DLf_invariant: "is_initial_DLf_state St \<Longrightarrow> DLf_invariant St"
  unfolding is_initial_DLf_state.simps DLf_invariant.simps by auto

lemma step_DLf_invariant:
  assumes
    inv: "DLf_invariant St" and
    step: "St \<leadsto>DLf St'"
  shows "DLf_invariant St'"
  using step inv
proof cases
  case (schedule_infer \<iota>s A C P)
  note defs = this(1,2) and \<iota>s_inf_betw = this(3)
  have "set \<iota>s \<subseteq> Inf_F"
    using \<iota>s_inf_betw unfolding no_labels.Inf_between_def no_labels.Inf_from_def by auto
  thus ?thesis
    using inv unfolding defs
    by (auto simp: DLf_invariant.simps passive_inferences_of_def fold_map[symmetric])
qed (auto simp: DLf_invariant.simps passive_inferences_of_def fold_map[symmetric])

lemma chain_DLf_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>DLf) Sts" and
    fair_hd: "DLf_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "DLf_invariant (lnth Sts i)"
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
  hence inv_i: "DLf_invariant (lnth Sts i)"
    by (rule ih)
  have step: "lnth Sts i \<leadsto>DLf lnth Sts (Suc i)"
    using chain chain_lnth_rel si_lt by blast

  show ?case
    by (rule step_DLf_invariant[OF inv_i step])
qed

lemma chain_DLf_invariant_llast:
  assumes
    chain: "chain (\<leadsto>DLf) Sts" and
    fair_hd: "DLf_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "DLf_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    by (metis chain chain_length_pos diff_less enat_ord_simps(2) i zero_enat_def zero_less_one)

  show ?thesis
    using chain_DLf_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

inductive is_final_DLf_state :: "('p, 'f) DLf_state \<Rightarrow> bool" where
  "is_final_DLf_state (empty, None, A)"

lemma is_final_DLf_state_iff_no_DLf_step:
  assumes inv: "DLf_invariant St"
  shows "is_final_DLf_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>DLf St')"
proof
  assume "is_final_DLf_state St"
  then obtain A :: "'f fset" where
    st: "St = (empty, None, A)"
    by (auto simp: is_final_DLf_state.simps)
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
  show "is_final_DLf_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_DLf_state St"

    obtain P :: 'p and Y :: "'f option" and A :: "'f fset" where
      st: "St = (P, Y, A)"
      by (cases St)

    have "P \<noteq> empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_DLf_state.simps by auto
    moreover {
      assume
        p: "P \<noteq> empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>DLf St'"
      proof (cases "select P")
        case sel: (Passive_Inference \<iota>)
        hence \<iota>_inf: "\<iota> \<in> Inf_F"
          using inv p unfolding st by (metis DLf_invariant.cases fst_conv mem_Collect_eq
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
    by (simp only: sel prod.sel option.set passive_inferences_of_remove_Passive_Inference
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
  note defs = this(1-4) and c_red = this(5)
  show ?thesis
    unfolding defs fstate_alt_def using DL.delete_fwd[OF c_red] by simp
next
  case (simplify_fwd C' C)
  note defs = this(1-4) and c_red = this(6)
  show ?thesis
    unfolding defs fstate_alt_def using DL.simplify_fwd[OF c_red] by simp
next
  case (delete_bwd C' C)
  note defs = this(1-4) and c'_red = this(6)
  show ?thesis
    unfolding defs fstate_alt_def using DL.delete_bwd[OF c'_red] by simp
next
  case (simplify_bwd C'' C' C)
  note defs = this(1-4) and c''_red = this(7)
  show ?thesis
    unfolding defs fstate_alt_def using DL.simplify_bwd[OF c''_red] by simp
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

fun mset_of_fstate :: "('p, 'f) DLf_state \<Rightarrow> 'f multiset" where
  "mset_of_fstate (P, Y, A) =
   image_mset concl_of (mset_set (passive_inferences_of P)) + mset_set (passive_formulas_of P) +
   mset_set (set_option Y) + mset_set (fset A)"

abbreviation Precprec_S :: "'f multiset \<Rightarrow> 'f multiset \<Rightarrow> bool" (infix "\<prec>\<prec>S" 50) where
  "(\<prec>\<prec>S) \<equiv> multp (\<prec>S)"

lemma wfP_Precprec_S: "wfP (\<prec>\<prec>S)"
  using minimal_element_def wfP_multp wf_Prec_S wfp_on_UNIV by blast

definition Less_state :: "('p, 'f) DLf_state \<Rightarrow> ('p, 'f) DLf_state \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "St' \<sqsubset> St \<longleftrightarrow>
   (yy_of St' = None \<and> yy_of St \<noteq> None)
   \<or> ((yy_of St' = None \<longleftrightarrow> yy_of St = None) \<and> mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St)"

lemma wfP_Less_state: "wfP (\<sqsubset>)"
proof -
  let ?boolset = "{(b', b :: bool). b' < b}"
  let ?msetset = "{(M', M). M' \<prec>\<prec>S M}"
  let ?pair_of = "\<lambda>St. (yy_of St \<noteq> None, mset_of_fstate St)"

  have wf_boolset: "wf ?boolset"
    by (rule Wellfounded.wellorder_class.wf)
  have wf_msetset: "wf ?msetset"
    using wfP_Precprec_S wfP_def by auto
  have wf_lex_prod: "wf (?boolset <*lex*> ?msetset)"
    by (rule wf_lex_prod[OF wf_boolset wf_msetset])

  have Less_state_alt_def:
    "\<And>St' St. St' \<sqsubset> St \<longleftrightarrow> (?pair_of St', ?pair_of St) \<in> ?boolset <*lex*> ?msetset"
    unfolding Less_state_def by auto

  show ?thesis
    unfolding wfP_def Less_state_alt_def using wf_app[of _ ?pair_of] wf_lex_prod by blast
qed

lemma non_compute_infer_choose_p_DLf_step_imp_Less_state:
  assumes
    step: "St \<leadsto>DLf St'" and
    yy: "yy_of St \<noteq> None \<or> yy_of St' = None"
  shows "St' \<sqsubset> St"
  using step
proof cases
  case (compute_infer P \<iota> A C)
  note defs = this(1,2)
  have False
    using step yy unfolding defs by simp
  thus ?thesis
    by blast
next
  case (choose_p P C A)
  note defs = this(1,2)
  have False
    using step yy unfolding defs by simp
  thus ?thesis
    by blast
next
  case (delete_fwd C A P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs Less_state_def by (auto intro!: subset_implies_multp)
next
  case (simplify_fwd C' C A P)
  note defs = this(1,2) and prec = this(3)

  let ?new_bef = "image_mset concl_of (mset_set (passive_inferences_of P)) +
    mset_set (passive_formulas_of P) + mset_set (fset A) + {#C#}"
  let ?new_aft = "image_mset concl_of (mset_set (passive_inferences_of P)) +
    mset_set (passive_formulas_of P) + mset_set (fset A) + {#C'#}"

  have lt_new: "?new_aft \<prec>\<prec>S ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "{#C'#} \<prec>\<prec>S {#C#}"
      unfolding multp_def using prec by (auto intro: singletons_in_mult)
  qed
  thus ?thesis
    unfolding defs Less_state_def by simp
next
  case (delete_bwd C' A C P)
  note defs = this(1,2) and c_ni = this(3)
  show ?thesis
    unfolding defs Less_state_def using c_ni
    by (auto simp: fmember.rep_eq intro!: subset_implies_multp)
next
  case (simplify_bwd C' A C'' C P)
  note defs = this(1,2) and c'_ni = this(3) and prec = this(4)

  show ?thesis
  proof (cases "C'' \<in> passive_formulas_of P")
    case c''_in: True
    show ?thesis
      unfolding defs Less_state_def using c'_ni
      by (auto simp: fmember.rep_eq insert_absorb[OF c''_in] intro!: subset_implies_multp)
  next
    case c''_ni: False

    have bef: "add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
        mset_set (passive_formulas_of P) + mset_set (insert C' (fset A))) =
      add_mset C
        (image_mset concl_of (mset_set (passive_inferences_of P)) +
         mset_set (passive_formulas_of P) + mset_set (fset A)) + {#C'#}" (is "?old_bef = ?new_bef")
      using c'_ni[simplified fmember.rep_eq] by auto
    have aft: "add_mset C
        (image_mset concl_of (mset_set (passive_inferences_of P)) +
         mset_set (insert C'' (passive_formulas_of P)) + mset_set (fset A)) =
      add_mset C
        (image_mset concl_of (mset_set (passive_inferences_of P)) +
         mset_set (passive_formulas_of P) + mset_set (fset A)) + {#C''#}" (is "?old_aft = ?new_aft")
      using c''_ni by (simp add: finite_passive_formulas_of)

    have lt_new: "?new_aft \<prec>\<prec>S ?new_bef"
      unfolding multp_def
    proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
      show "{#C''#} \<prec>\<prec>S {#C'#}"
        unfolding multp_def using prec by (auto intro: singletons_in_mult)
    qed
    show ?thesis
      unfolding defs Less_state_def by simp (simp only: bef aft lt_new)
  qed
next
  case (schedule_infer \<iota>s A C P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs Less_state_def by auto
next
  case (delete_orphan_infers \<iota>s P A Y)
  note defs = this(1,2) and \<iota>s_nnil = this(3) and \<iota>s_sub = this(4) and \<iota>s_inter = this(5)
  have "image_mset concl_of (mset_set (passive_inferences_of P - set \<iota>s)) \<subset>#
    image_mset concl_of (mset_set (passive_inferences_of P))"
    by (metis Diff_empty Diff_subset \<iota>s_nnil \<iota>s_sub double_diff empty_subsetI
        finite_passive_inferences_of finite_subset image_mset_subset_mono mset_set_eq_iff set_empty
        subset_imp_msubset_mset_set subset_mset.nless_le)
  thus ?thesis
    unfolding defs Less_state_def by (auto intro!: subset_implies_multp)
qed

lemma yy_nonempty_DLf_step_imp_Less_state:
  assumes
    step: "St \<leadsto>DLf St'" and
    yy: "yy_of St \<noteq> None" and
    yy': "yy_of St' \<noteq> None"
  shows "St' \<sqsubset> St"
proof -
  have "yy_of St \<noteq> None \<or> yy_of St' = None"
    using yy by blast
  thus ?thesis
    using non_compute_infer_choose_p_DLf_step_imp_Less_state[OF step] by blast
qed

lemma fair_DL_Liminf_yy_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>DLf) Sts" and
    inv: "DLf_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) = {}"
proof (rule ccontr)
  assume lim_nemp: "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<noteq> {}"

  obtain i :: nat where
    i_lt: "enat i < llength Sts" and
    inter_nemp: "\<Inter> ((set_option \<circ> yy_of \<circ> lnth Sts) ` {j. i \<le> j \<and> enat j < llength Sts}) \<noteq> {}"
    using lim_nemp unfolding Liminf_llist_def by auto

  from inter_nemp obtain C :: 'f where
    c_in: "\<forall>P \<in> lnth Sts ` {j. i \<le> j \<and> enat j < llength Sts}. C \<in> set_option (yy_of P)"
    by auto
  hence c_in': "\<forall>j \<ge> i. enat j < llength Sts \<longrightarrow> C \<in> set_option (yy_of (lnth Sts j))"
    by auto

  have si_lt: "enat (Suc i) < llength Sts"
    unfolding len by auto

  have yy_j: "yy_of (lnth Sts j) \<noteq> None" if j_ge: "j \<ge> i" for j
    using c_in' len j_ge by auto
  hence yy_sj: "yy_of (lnth Sts (Suc j)) \<noteq> None" if j_ge: "j \<ge> i" for j
    using le_Suc_eq that by presburger
  have step: "lnth Sts j \<leadsto>DLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
    using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
    by blast

  have "lnth Sts (Suc j) \<sqsubset> lnth Sts j" if j_ge: "j \<ge> i" for j
    using yy_nonempty_DLf_step_imp_Less_state by (meson step j_ge yy_j yy_sj)
  hence "(\<sqsubset>)\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain (\<sqsubset>)\<inverse>\<inverse> (ldropn i Sts)"
    by (simp add: chain_ldropnI si_lt)

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using len by (simp add: llength_eq_infty_conv_lfinite)

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<sqsubset>)"] wfP_Less_state
    by metis
qed

lemma DLf_step_imp_queue_step:
  assumes "St \<leadsto>DLf St'"
  shows "queue_step (passive_of St) (passive_of St')"
  using assms
  by cases (auto simp: fold_map[symmetric] intro: queue_step_idleI queue_step_addI
      queue_step_removeI queue_step_fold_addI queue_step_fold_removeI)

lemma fair_DL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>DLf) Sts" and
    init: "is_initial_DLf_state (lhd Sts)"
  shows "Liminf_llist (lmap (elems \<circ> passive_of) Sts) = {}"
proof -
  have chain_step: "chain queue_step (lmap passive_of Sts)"
    using DLf_step_imp_queue_step chain_lmap full_chain_imp_chain[OF full]
    by (metis (no_types, lifting))

  have inf_oft: "infinitely_often select_queue_step (lmap passive_of Sts)"
  proof
    assume "finitely_often select_queue_step (lmap passive_of Sts)"
    then obtain i :: nat where
      no_sel:
        "\<forall>j \<ge> i. \<not> select_queue_step (passive_of (lnth Sts j)) (passive_of (lnth Sts (Suc j)))"
      by (metis (no_types, lifting) enat_ord_code(4) finitely_often_def len llength_lmap lnth_lmap)

    have si_lt: "enat (Suc i) < llength Sts"
      unfolding len by auto

    have step: "lnth Sts j \<leadsto>DLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
      using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
      by blast

    have yy: "yy_of (lnth Sts j) \<noteq> None \<or> yy_of (lnth Sts (Suc j)) = None" if j_ge: "j \<ge> i" for j
      using step[OF j_ge]
    proof cases
      case (compute_infer P \<iota> A C)
      note defs = this(1,2) and p_ne = this(3)
      have False
        using no_sel defs p_ne select_queue_stepI that by fastforce
      thus ?thesis
        by blast
    next
      case (choose_p P C A)
      note defs = this(1,2) and p_ne = this(3)
      have False
        using no_sel defs p_ne select_queue_stepI that by fastforce
      thus ?thesis
        by blast
    qed auto

    have "lnth Sts (Suc j) \<sqsubset> lnth Sts j" if j_ge: "j \<ge> i" for j
      by (rule non_compute_infer_choose_p_DLf_step_imp_Less_state[OF step[OF j_ge] yy[OF j_ge]])
    hence "(\<sqsubset>)\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using j_ge by blast
    hence inf_down_chain: "chain (\<sqsubset>)\<inverse>\<inverse> (ldropn i Sts)"
      using chain_ldropn_lmapI[OF _ si_lt, of _ id, simplified llist.map_id] by simp

    have inf_i: "\<not> lfinite (ldropn i Sts)"
      using len lfinite_ldropn llength_eq_infty_conv_lfinite by blast

    show False
      using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<sqsubset>)"] wfP_Less_state
      by blast
  qed

  have hd_emp: "lhd (lmap passive_of Sts) = empty"
    using init full full_chain_not_lnull unfolding is_initial_DLf_state.simps by fastforce

  have "Liminf_llist (lmap elems (lmap passive_of Sts)) = {}"
    by (rule fair[of "lmap passive_of Sts", OF chain_step inf_oft hd_emp])
  thus ?thesis
    by (simp add: llist.map_comp)
qed

lemma fair_DL_Liminf_passive_formulas_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>DLf) Sts" and
    init: "is_initial_DLf_state (lhd Sts)"
  shows "Liminf_llist (lmap (passive_formulas_of \<circ> passive_of) Sts) = {}"
proof -
  have lim_filt: "Liminf_llist (lmap (Set.filter is_passive_formula \<circ> elems \<circ> passive_of) Sts) = {}"
    using fair_DL_Liminf_passive_empty Liminf_llist_subset
    by (metis (no_types) empty_iff full init len llength_lmap llist.map_comp lnth_lmap member_filter
        subsetI subset_antisym)

  let ?g = "Set.filter is_passive_formula \<circ> elems \<circ> passive_of"

  have "inj_on passive_formula (Set.filter is_passive_formula (UNIV :: 'f passive_elem set))"
    unfolding inj_on_def by (metis member_filter passive_elem.collapse(2))
  moreover have "Sup_llist (lmap ?g Sts) \<subseteq> Set.filter is_passive_formula UNIV"
    unfolding Sup_llist_def by auto
  ultimately have inj_pi: "inj_on passive_formula (Sup_llist (lmap ?g Sts))"
    using inj_on_subset by blast

  have lim_pass: "Liminf_llist (lmap (\<lambda>x. passive_formula `
    (Set.filter is_passive_formula \<circ> elems \<circ> passive_of) x) Sts) = {}"
    using Liminf_llist_lmap_image[OF inj_pi] lim_filt by simp

  have "Liminf_llist (lmap (\<lambda>St. {C. Passive_Formula C \<in> elems (passive_of St)}) Sts) = {}"
    using lim_pass passive_formula_filter by (smt (verit) Collect_cong comp_apply llist.map_cong)
  thus ?thesis
    unfolding passive_formulas_of_def comp_apply .
qed

lemma fair_DL_Liminf_passive_inferences_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>DLf) Sts" and
    init: "is_initial_DLf_state (lhd Sts)"
  shows "Liminf_llist (lmap (passive_inferences_of \<circ> passive_of) Sts) = {}"
proof -
  have lim_filt: "Liminf_llist (lmap (Set.filter is_passive_inference \<circ> elems \<circ> passive_of) Sts) = {}"
    using fair_DL_Liminf_passive_empty Liminf_llist_subset
    by (metis (no_types) empty_iff full init len llength_lmap llist.map_comp lnth_lmap member_filter
        subsetI subset_antisym)

  let ?g = "Set.filter is_passive_inference \<circ> elems \<circ> passive_of"

  have "inj_on passive_inference (Set.filter is_passive_inference (UNIV :: 'f passive_elem set))"
    unfolding inj_on_def by (metis member_filter passive_elem.collapse(1))
  moreover have "Sup_llist (lmap ?g Sts) \<subseteq> Set.filter is_passive_inference UNIV"
    unfolding Sup_llist_def by auto
  ultimately have inj_pi: "inj_on passive_inference (Sup_llist (lmap ?g Sts))"
    using inj_on_subset by blast

  have lim_pass: "Liminf_llist (lmap (\<lambda>x. passive_inference `
    (Set.filter is_passive_inference \<circ> elems \<circ> passive_of) x) Sts) = {}"
    using Liminf_llist_lmap_image[OF inj_pi] lim_filt by simp

  have "Liminf_llist (lmap (\<lambda>St. {\<iota>. Passive_Inference \<iota> \<in> elems (passive_of St)}) Sts) = {}"
    using lim_pass passive_inference_filter by (smt (verit) Collect_cong comp_apply llist.map_cong)
  thus ?thesis
    unfolding passive_inferences_of_def comp_apply .
qed

theorem
  assumes
    full: "full_chain (\<leadsto>DLf) Sts" and
    init: "is_initial_DLf_state (lhd Sts)"
  shows
    fair_DL_Liminf_saturated: "saturated (labeled_formulas_of (Liminf_fstate Sts))" and
    fair_DL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> passive_formulas_of (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_fstate Sts)" and
    fair_DL_complete: "B \<in> Bot_F \<Longrightarrow> passive_formulas_of (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
proof -
  have chain: "chain (\<leadsto>DLf) Sts"
    by (rule full_chain_imp_chain[OF full])
  hence dl_chain: "chain (\<leadsto>DL) (lmap fstate Sts)"
    by (smt (verit, del_insts) chain_lmap fair_DL_step_imp_DL_step mset_of_fstate.cases)

  have inv: "DLf_invariant (lhd Sts)"
    using init initial_DLf_invariant by auto

  have nnul: "\<not> lnull Sts"
    using chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_DLf_state.cases init snd_conv)
  hence act: "active_subset (snd (lhd (lmap fstate Sts))) = {}"
    unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas_fml_and_t_inf: "passive_subset (Liminf_llist (lmap (snd \<circ> fstate) Sts)) = {} \<and>
    Liminf_llist (lmap (fst \<circ> fstate) Sts) = {}" (is "?pas_fml \<and> ?t_inf")
  proof (cases "lfinite Sts")
    case fin: True

    have lim_fst: "Liminf_llist (lmap (fst \<circ> fstate) Sts) = fst (fstate (llast Sts))" and
      lim_snd: "Liminf_llist (lmap (snd \<circ> fstate) Sts) = snd (fstate (llast Sts))"
      using lfinite_Liminf_llist fin nnul
      by (metis comp_eq_dest_lhs lfinite_lmap llast_lmap llist.map_disc_iff)+

    have last_inv: "DLf_invariant (llast Sts)"
      by (rule chain_DLf_invariant_llast[OF chain inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>DLf St'"
      using full_chain_lnth_not_rel[OF full] by (metis fin full_chain_iff_chain full)
    hence "is_final_DLf_state (llast Sts)"
      unfolding is_final_DLf_state_iff_no_DLf_step[OF last_inv] .
    then obtain A :: "'f fset" where
      at_l: "llast Sts = (empty, None, A)"
      unfolding is_final_DLf_state.simps by blast

    have ?pas_fml
      unfolding passive_subset_def lim_snd at_l by auto
    moreover have ?t_inf
      unfolding lim_fst at_l by simp
    ultimately show ?thesis
      by blast
  next
    case False
    hence len: "llength Sts = \<infinity>"
      by (simp add: not_lfinite_llength)

    have ?pas_fml
      unfolding Liminf_fstate_commute passive_subset_def Liminf_fstate_def
      using fair_DL_Liminf_passive_formulas_empty[OF len full init]
        fair_DL_Liminf_yy_empty[OF len full inv]
      by simp
    moreover have ?t_inf
      unfolding fstate_alt_def using fair_DL_Liminf_passive_inferences_empty[OF len full init]
      by simp
    ultimately show ?thesis
      by blast
  qed
  note pas_fml = pas_fml_and_t_inf[THEN conjunct1] and
    t_inf = pas_fml_and_t_inf[THEN conjunct2]

  have pas_fml': "passive_subset (Liminf_llist (lmap snd (lmap fstate Sts))) = {}"
    using pas_fml by (simp add: llist.map_comp)
  have t_inf': "Liminf_llist (lmap fst (lmap fstate Sts)) = {}"
    using t_inf by (simp add: llist.map_comp)

  have no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd (lmap fstate Sts))"
    using inf_have_prems by blast

  show "saturated (labeled_formulas_of (Liminf_fstate Sts))"
    using DL_Liminf_saturated[OF dl_chain act pas_fml' no_prems_init t_inf']
    unfolding Liminf_fstate_commute[folded llist.map_comp] .

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "passive_formulas_of (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"

    have unsat': "fst ` snd (lhd (lmap fstate Sts)) \<Turnstile>\<inter>\<G> {B}"
      using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

    show "\<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_fstate Sts)"
      using DL_complete_Liminf[OF dl_chain act pas_fml' no_prems_init t_inf' bot unsat']
      unfolding Liminf_fstate_commute[folded llist.map_comp]
      by (cases "Liminf_fstate Sts") auto
    thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
      unfolding Liminf_fstate_def Liminf_llist_def by auto
  }
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

sublocale fifo_prover_queue
  .

sublocale fair_discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list Prec_S
proof
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
