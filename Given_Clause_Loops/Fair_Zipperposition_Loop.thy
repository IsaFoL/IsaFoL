(* Title:        Fair Zipperposition Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Fair Zipperposition Loop\<close>

theory Fair_Zipperposition_Loop
  imports
    Given_Clause_Loops_Util
    Zipperposition_Loop
    Passive_Set
begin


subsection \<open>Locale\<close>

type_synonym ('t, 'p, 'f) fair_ZL_state = "'t \<times> 'p \<times> 'f option \<times> 'f fset"

locale fair_discount_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  todo: fair_passive_set t_empty t_select t_add t_remove t_felems +
  passive: fair_passive_set p_empty p_select p_add p_remove p_felems
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
    t_empty :: "'t" and
    t_select :: "'t \<Rightarrow> 'f inference llist" and
    t_add :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_remove :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_felems :: "'t \<Rightarrow> 'f inference llist fset" and
    p_empty :: "'p" and
    p_select :: "'p \<Rightarrow> 'f" and
    p_add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    p_felems :: "'p \<Rightarrow> 'f fset" +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_Prec_S: "minimal_element (\<prec>S) UNIV" and
    transp_Prec_S: "transp (\<prec>S)"
begin

lemma trans_Prec_S: "trans {(x, y). x \<prec>S y}"
  using transp_Prec_S transp_trans by blast

lemma irreflp_Prec_S: "irreflp (\<prec>S)"
  using minimal_element.wf wfP_imp_irreflp wf_Prec_S wfp_on_UNIV by blast

lemma irrefl_Prec_S: "irrefl {(x, y). x \<prec>S y}"
  by (metis CollectD case_prod_conv irrefl_def irreflp_Prec_S irreflp_def)


subsection \<open>Definition and Lemmas\<close>

abbreviation todo_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 't" where
  "todo_of St \<equiv> fst St"
abbreviation passive_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd St)"
abbreviation yy_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd St))"
abbreviation active_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd (snd St))"

abbreviation formulas_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f set" where
  "formulas_of St \<equiv> passive.elems (passive_of St) \<union> set_option (yy_of St) \<union> fset (active_of St)"

fun zl_fstate :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set" where
  "zl_fstate (T, P, Y, A) = zl_state (todo.elems T, passive.elems P, set_option Y, fset A)"

lemma zl_fstate_alt_def:
  "zl_fstate St = zl_state (todo.elems (fst St), passive.elems (fst (snd St)),
     set_option (fst (snd (snd St))), fset (snd (snd (snd St))))"
  by (cases St) auto

definition
  Liminf_zl_fstate :: "('t, 'p, 'f) fair_ZL_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_zl_fstate Sts =
   (Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap (fset \<circ> active_of) Sts))"

lemma Liminf_fstate_commute:
  "Liminf_llist (lmap (snd \<circ> zl_fstate) Sts) = labeled_formulas_of (Liminf_zl_fstate Sts)"
proof -
  have "Liminf_llist (lmap (snd \<circ> zl_fstate) Sts) =
    (\<lambda>C. (C, Passive)) ` Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts) \<union>
    (\<lambda>C. (C, YY)) ` Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<union>
    (\<lambda>C. (C, Active)) ` Liminf_llist (lmap (fset \<circ> active_of) Sts)"
    unfolding zl_fstate_alt_def zl_state_alt_def
    apply simp
    apply (subst Liminf_llist_lmap_union, fast)+
    apply (subst Liminf_llist_lmap_image, simp add: inj_on_convol_ident)+
    by auto
 thus ?thesis
   unfolding Liminf_zl_fstate_def by fastforce
qed

fun formulas_union :: "'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f set" where
  "formulas_union (P, Y, A) = P \<union> Y \<union> A"

inductive
  fair_ZL :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> ('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool"
  (infix "\<leadsto>ZLf" 50)
where
  compute_infer: "T \<noteq> t_empty \<Longrightarrow> t_select T = LCons \<iota>0 \<iota>s \<Longrightarrow>
    \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (T, P, None, A) \<leadsto>ZLf (t_add \<iota>s (t_remove (t_select T) T), p_add C P, None, A)"
| choose_p: "P \<noteq> p_empty \<Longrightarrow>
    (T, P, None, A) \<leadsto>ZLf (T, p_remove (p_select P) P, Some (p_select P), A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLf (T, P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLf (T, P, Some C', A)"
| delete_bwd: "C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (T, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLf (T, P, Some C, A)"
| simplify_bwd: "C' |\<notin>| A \<Longrightarrow> C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (T, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLf (T, p_add C'' P, Some C, A)"
| schedule_infer: "flat_inferences_of (set \<iota>ss) = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (T, P, Some C, A) \<leadsto>ZLf (fold t_add \<iota>ss T, P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<in> todo.elems T \<Longrightarrow> lset \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (T, P, Y, A) \<leadsto>ZLf (t_remove \<iota>s T, P, Y, A)"


subsection \<open>Initial State and Invariant\<close>

inductive is_initial_fair_ZL_state :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool" where
  "flat_inferences_of (set \<iota>ss) = no_labels.Inf_from {} \<Longrightarrow>
   is_initial_fair_ZL_state (fold t_add \<iota>ss t_empty, p_empty, None, {||})"

inductive fair_ZL_invariant :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool" where
  "flat_inferences_of (todo.elems T) \<subseteq> Inf_F \<Longrightarrow> fair_ZL_invariant (T, P, Y, A)"

lemma initial_fair_ZL_invariant:
  assumes "is_initial_fair_ZL_state St"
  shows "fair_ZL_invariant St"
  using assms
proof
  fix \<iota>ss
  assume
    st: "St = (fold t_add \<iota>ss t_empty, p_empty, None, {||})" and
    \<iota>ss: "flat_inferences_of (set \<iota>ss) = no_labels.Inf_from {}"

  have "flat_inferences_of (todo.elems (fold t_add \<iota>ss t_empty)) \<subseteq> Inf_F"
    using \<iota>ss no_labels.Inf_if_Inf_from by force
  thus "fair_ZL_invariant St"
    unfolding st by (rule fair_ZL_invariant.intros)
qed

lemma step_fair_ZL_invariant:
  assumes
    inv: "fair_ZL_invariant St" and
    step: "St \<leadsto>ZLf St'"
  shows "fair_ZL_invariant St'"
  using step inv
proof cases
  case (compute_infer T \<iota>0 \<iota>s A C P)
  note defs = this(1,2) and t'_ne = this(3) and sel = this(4)

  have "flat_inferences_of (todo.elems (t_add \<iota>s (t_remove (t_select T) T))) \<subseteq>
    flat_inferences_of (todo.elems (t_add \<iota>s T))"
    by auto
  also have "... \<subseteq> flat_inferences_of (todo.elems T)"
    by (metis (no_types) Un_iff distr_flat_inferences_of_wrt_union flat_inferences_of_LCons sel
        subsetI t'_ne todo.add_again todo.elems_add todo.select_in_felems)
  finally have "flat_inferences_of (todo.elems (t_add \<iota>s (t_remove (t_select T) T))) \<subseteq>
    flat_inferences_of (todo.elems T)"
    by auto
  thus ?thesis
    using inv unfolding defs fair_ZL_invariant.simps by force
next
  case (schedule_infer \<iota>ss A C T P)
  note defs = this(1,2) and \<iota>ss_inf_betw = this(3)
  have "flat_inferences_of (set \<iota>ss) \<subseteq> Inf_F"
    using \<iota>ss_inf_betw unfolding no_labels.Inf_between_def no_labels.Inf_from_def by auto
  thus ?thesis
    using inv distr_flat_inferences_of_wrt_union unfolding defs fair_ZL_invariant.simps by auto
qed (auto simp: fair_ZL_invariant.simps)

lemma chain_fair_ZL_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>ZLf) Sts" and
    fair_hd: "fair_ZL_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "fair_ZL_invariant (lnth Sts i)"
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
  hence inv_i: "fair_ZL_invariant (lnth Sts i)"
    by (rule ih)
  have step: "lnth Sts i \<leadsto>ZLf lnth Sts (Suc i)"
    using chain chain_lnth_rel si_lt by blast

  show ?case
    by (rule step_fair_ZL_invariant[OF inv_i step])
qed

lemma chain_fair_ZL_invariant_llast:
  assumes
    chain: "chain (\<leadsto>ZLf) Sts" and
    fair_hd: "fair_ZL_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "fair_ZL_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    using i by (metis chain chain_length_pos diff_less enat_ord_simps(2) less_numeral_extra(1)
        zero_enat_def)

  show ?thesis
    using chain_fair_ZL_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed

end

end
