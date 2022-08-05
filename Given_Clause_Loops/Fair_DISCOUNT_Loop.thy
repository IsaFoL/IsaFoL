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


subsection \<open>Setup\<close>

hide_const (open) Seq.chain


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

lemma passive_inferences_of[simp]: "passive_inferences_of empty = {}"
  unfolding passive_inferences_of_def by simp

lemma passive_formulas_of[simp]: "passive_formulas_of empty = {}"
  unfolding passive_formulas_of_def by simp

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
  "Liminf_llist (lmap (snd \<circ> fstate) Sts) = formulas_of (Liminf_fstate Sts)"
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
| delete_orphan_formulas: "\<iota>s \<noteq> [] \<Longrightarrow> set \<iota>s \<subseteq> passive_inferences_of P \<Longrightarrow>
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
  using step inv apply cases
  apply (simp_all add: fair_DL_invariant.intros)

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
  thus ?case
    using chain step_fair_DL_invariant
    by (metis dual_order.refl fair_DL_invariant.intros fstate.cases)
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

      have n: "N = {||}" and
        x: "X = None"
        using y inv' by blast+

      let ?M = "concl_of ` no_labels.Inf_between (fset A) {C}"

      have fin: "finite ?M"
        by (simp add: finite_Inf_between)
      have fset_abs_m: "fset (Abs_fset ?M) = ?M"
        by (rule Abs_fset_inverse[simplified, OF fin])

      have inf_red: "no_labels.Inf_between (fset A) {C}
        \<subseteq> no_labels.Red_I_\<G> (fset A \<union> {C} \<union> fset (Abs_fset ?M))"
        by (simp add: fset_abs_m no_labels.Inf_if_Inf_between no_labels.empty_ord.Red_I_of_Inf_to_N
            subsetI)

      have "\<exists>St'. St \<leadsto>DLf St'"
        using fair_DL.infer[OF inf_red] unfolding st n x y by fast
    } ultimately show False
      using no_step by force
  qed
qed



end

end
