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

locale fair_zipperposition_loop =
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
    transp_Prec_S: "transp (\<prec>S)" and
    countable_Inf_between: "finite A \<Longrightarrow> countable (no_labels.Inf_between A {C})"
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

abbreviation all_formulas_of :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> passive.elems (passive_of St) \<union> set_option (yy_of St) \<union> fset (active_of St)"

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

lemma Liminf_zl_fstate_commute:
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

inductive
  compute_infer_step :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> ('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool"
where
  "T \<noteq> t_empty \<Longrightarrow> t_select T = LCons \<iota>0 \<iota>s \<Longrightarrow> \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
   compute_infer_step (T, P, None, A) (t_add \<iota>s (t_remove (t_select T) T), p_add C P, None, A)"

inductive
  choose_p_step :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> ('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool"
where
  "P \<noteq> p_empty \<Longrightarrow> choose_p_step (T, P, None, A) (T, p_remove (p_select P) P, Some (p_select P), A)"


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


subsection \<open>Final State\<close>

inductive is_final_fair_ZL_state :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool" where
  "is_final_fair_ZL_state (t_empty, p_empty, None, A)"

lemma is_final_fair_ZL_state_iff_no_ZLf_step:
  assumes inv: "fair_ZL_invariant St"
  shows "is_final_fair_ZL_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>ZLf St')"
proof
  assume "is_final_fair_ZL_state St"
  then obtain A :: "'f fset" where
    st: "St = (t_empty, p_empty, None, A)"
    by (auto simp: is_final_fair_ZL_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>ZLf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "(t_empty, p_empty, None, A) \<leadsto>ZLf St'"
    thus False
      by cases auto
  qed
next
  assume no_step: "\<forall>St'. \<not> St \<leadsto>ZLf St'"
  show "is_final_fair_ZL_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_fair_ZL_state St"

    obtain T :: 't and P :: 'p and Y :: "'f option" and A :: "'f fset" where
      st: "St = (T, P, Y, A)"
      by (cases St)

    have "T \<noteq> t_empty \<or> P \<noteq> p_empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_fair_ZL_state.simps by auto
    moreover {
      assume
        t: "T \<noteq> t_empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>ZLf St'"
      proof (cases "t_select T")
        case LNil

        have nil_in: "LNil \<in> todo.elems T"
          by (metis local.LNil t todo.select_in_elems)
        have nil_inter: "lset LNil \<inter> no_labels.Inf_from (fset A) = {}"
          by simp

        show ?thesis
          using fair_ZL.delete_orphan_infers[OF nil_in nil_inter] unfolding st t y by fast
      next
        case sel: (LCons \<iota>0 \<iota>s)

        have \<iota>_inf: "\<iota>0 \<in> Inf_F"
          using inv t unfolding st
          by (metis (no_types, lifting) Un_iff distr_flat_inferences_of_wrt_union
              fair_ZL_invariant.cases flat_inferences_of_LCons fst_conv insert_iff sel subset_iff
              todo.add_again todo.elems_add todo.select_in_felems)
        have \<iota>_red: "\<iota>0 \<in> no_labels.Red_I_\<G> (fset A \<union> {concl_of \<iota>0})"
          using \<iota>_inf no_labels.empty_ord.Red_I_of_Inf_to_N by auto

        show ?thesis
          using fair_ZL.compute_infer[OF t sel \<iota>_red] unfolding st y by blast
      qed
    } moreover {
      assume
        p: "P \<noteq> p_empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>ZLf St'"
        using fair_ZL.choose_p[OF p] unfolding st p y by fast
    } moreover {
      assume "Y \<noteq> None"
      then obtain C :: 'f where
        y: "Y = Some C"
        by blast

      obtain \<iota>s :: "'f inference llist" where
        \<iota>ss: "flat_inferences_of (set [\<iota>s]) = no_labels.Inf_between (fset A) {C}"
        using countable_imp_lset[OF countable_Inf_between[OF finite_fset]] by force

      have "\<exists>St'. St \<leadsto>ZLf St'"
        using fair_ZL.schedule_infer[OF \<iota>ss] unfolding st y by fast
    } ultimately show False
      using no_step by force
  qed
qed


subsection \<open>Refinement\<close>

lemma fair_ZL_step_imp_ZL_step:
  assumes zlf: "(T, P, Y, A) \<leadsto>ZLf (T', P', Y', A')"
  shows "zl_fstate (T, P, Y, A) \<leadsto>ZL zl_fstate (T', P', Y', A')"
  using zlf
proof cases
  case (compute_infer \<iota>0 \<iota>s C)
  note defs = this(1-5) and t_nemp = this(6) and sel = this(7) and \<iota>_red = this(8)

  have todo_min_\<iota>_uni_\<iota>: "todo.elems T - {LCons \<iota>0 \<iota>s} \<union> {LCons \<iota>0 \<iota>s} = todo.elems T"
    by (metis Un_Diff_cancel Un_commute sel t_nemp todo.add_again todo.elems_add
        todo.select_in_felems)

  show ?thesis
    unfolding defs zl_fstate_alt_def sel prod.sel option.set
    using ZL.compute_infer[OF \<iota>_red, of "todo.elems T - {LCons \<iota>0 \<iota>s}" \<iota>s "passive.elems P"]
    by (metis todo_min_\<iota>_uni_\<iota> Un_commute passive.elems_add todo.elems_add todo.elems_remove)
next
  case choose_p
  note defs = this(1-5) and p_nemp = this(6)

  have elems_rem_sel_uni_sel:
    "passive.elems (p_remove (p_select P) P) \<union> {p_select P} = passive.elems P"
    using p_nemp by force

  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set
    using ZL.choose_p[of "todo.elems T" "passive.elems (p_remove (p_select P) P)" "p_select P"
        "fset A"]
    by (metis elems_rem_sel_uni_sel)
next
  case (delete_fwd C)
  note defs = this(1-5) and c_red = this(6)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.delete_fwd[OF c_red] by simp
next
  case (simplify_fwd C' C)
  note defs = this(1-5) and c_red = this(7)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.simplify_fwd[OF c_red] by simp
next
  case (delete_bwd C' C)
  note defs = this(1-5) and c'_red = this(7)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.delete_bwd[OF c'_red] by simp
next
  case (simplify_bwd C' C'' C)
  note defs = this(1-5) and c''_red = this(8)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.simplify_bwd[OF c''_red] by simp
next
  case (schedule_infer \<iota>ss C)
  note defs = this(1-5) and \<iota>ss = this(6)
  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set
    using ZL.schedule_infer[OF \<iota>ss, of "todo.elems T" "passive.elems P"]
    by (simp add: Un_commute)
next
  case (delete_orphan_infers \<iota>s)
  note defs = this(1-4) and \<iota>s_todo = this(5) and inter = this(6)

  have elems_rem_\<iota>s_uni_\<iota>s: "todo.elems (t_remove \<iota>s T) \<union> {\<iota>s} = todo.elems T"
    using \<iota>s_todo by auto

  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set
    using ZL.delete_orphan_infers[OF inter, of "todo.elems (t_remove \<iota>s T)" "passive.elems P"
        "set_option Y"]
    by (metis elems_rem_\<iota>s_uni_\<iota>s)
qed

lemma fair_ZL_step_imp_GC_step:
  "(T, P, Y, A) \<leadsto>ZLf (T', P', Y', A') \<Longrightarrow> zl_fstate (T, P, Y, A) \<leadsto>LGC zl_fstate (T', P', Y', A')"
  by (rule ZL_step_imp_LGC_step[OF fair_ZL_step_imp_ZL_step])


subsection \<open>Completeness\<close>

fun mset_of_zl_fstate :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> 'f multiset" where
  "mset_of_zl_fstate (T, P, Y, A) =
   mset_set (passive.elems P) + mset_set (set_option Y) + mset_set (fset A)"

abbreviation \<mu>1 :: "'f multiset \<Rightarrow> 'f multiset \<Rightarrow> bool" where
  "\<mu>1 \<equiv> multp (\<prec>S)"

lemma wfP_\<mu>1: "wfP \<mu>1"
  using minimal_element_def wfP_multp wf_Prec_S wfp_on_UNIV by blast

definition \<mu>2 :: "('t, 'p, 'f) fair_ZL_state \<Rightarrow> ('t, 'p, 'f) fair_ZL_state \<Rightarrow> bool" where
  "\<mu>2 St' St \<equiv>
   (yy_of St' = None \<and> yy_of St \<noteq> None)
   \<or> ((yy_of St' = None \<longleftrightarrow> yy_of St = None)
      \<and> (\<mu>1 (mset_of_zl_fstate St') (mset_of_zl_fstate St)
         \<or> (mset_of_zl_fstate St' = mset_of_zl_fstate St
            \<and> fcard (t_felems (todo_of St')) < fcard (t_felems (todo_of St)))))"

lemma wfP_\<mu>2: "wfP \<mu>2"
proof -
  let ?boolset = "{(b', b :: bool). b' < b}"
  let ?\<mu>1set = "{(M', M). \<mu>1 M' M}"
  let ?natset = "{(n', n :: nat). n' < n}"
  let ?triple_of = "\<lambda>St. (yy_of St \<noteq> None, mset_of_zl_fstate St, fcard (t_felems (todo_of St)))"

  have wf_boolset: "wf ?boolset"
    by (rule Wellfounded.wellorder_class.wf)
  have wf_\<mu>1set: "wf ?\<mu>1set"
    using wfP_\<mu>1 wfP_def by auto
  have wf_natset: "wf ?natset"
    by (rule Wellfounded.wellorder_class.wf)
  have wf_lex_prod: "wf (?boolset <*lex*> ?\<mu>1set <*lex*> ?natset)"
    by (rule wf_lex_prod[OF wf_boolset wf_lex_prod[OF wf_\<mu>1set wf_natset]])

  have \<mu>2_alt_def: "\<And>St' St. \<mu>2 St' St \<longleftrightarrow>
    (?triple_of St', ?triple_of St) \<in> ?boolset <*lex*> ?\<mu>1set <*lex*> ?natset"
    unfolding \<mu>2_def by auto

  show ?thesis
    unfolding wfP_def \<mu>2_alt_def using wf_app[of _ ?triple_of] wf_lex_prod by blast
qed


lemma yy_nonempty_ZLf_step_imp_\<mu>1:
  assumes
    step: "St \<leadsto>ZLf St'" and
    yy: "yy_of St \<noteq> None" and
    yy': "yy_of St' \<noteq> None"
  shows "\<mu>1 (mset_of_zl_fstate St') (mset_of_zl_fstate St)"
  using step
  sorry
(* FIXME
proof cases
  case (simplify_fwd C' C A P)
  note defs = this(1,2) and prec = this(3)

  have bef: "add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
      mset_set (passive_formulas_of P) + mset_set (fset A)) =
    image_mset concl_of (mset_set (passive_inferences_of P)) + mset_set (passive_formulas_of P) +
      mset_set (fset A) + {#C#}" (is "?old_bef = ?new_bef")
    by simp
  have aft: "add_mset C' (image_mset concl_of (mset_set (passive_inferences_of P)) +
      mset_set (passive_formulas_of P) + mset_set (fset A)) =
    image_mset concl_of (mset_set (passive_inferences_of P)) + mset_set (passive_formulas_of P) +
      mset_set (fset A) + {#C'#}" (is "?old_aft = ?new_aft")
    by simp

  have "\<mu>1 ?new_aft ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "\<mu>1 {#C'#} {#C#}"
      unfolding multp_def using prec by (auto intro: singletons_in_mult)
  qed
  thus ?thesis
    unfolding defs by simp
next
  case (delete_bwd C' A C P)
  note defs = this(1,2) and c'_ni = this(3)
  show ?thesis
    unfolding defs using c'_ni by (auto simp: notin_fset intro!: subset_implies_multp)
next
  case (simplify_bwd C' A C'' C P)
  note defs = this(1,2) and c'_ni = this(3) and prec = this(4)

  show ?thesis
  proof (cases "C'' \<in> passive_formulas_of P")
    case c''_in: True
    show ?thesis
      unfolding defs using c'_ni
      by (auto simp: notin_fset insert_absorb[OF c''_in] intro!: subset_implies_multp)
  next
    case c''_in: False

    have bef: "add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
        mset_set (passive_formulas_of P) + mset_set (insert C' (fset A))) =
      add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
        mset_set (passive_formulas_of P) + mset_set (fset A)) + {#C'#}" (is "?old_bef = ?new_bef")
      using c'_ni by (simp add: notin_fset)
    have aft: "add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
        mset_set (insert C'' (passive_formulas_of P)) + mset_set (fset A)) =
      add_mset C (image_mset concl_of (mset_set (passive_inferences_of P)) +
        mset_set (passive_formulas_of P) + mset_set (fset A)) + {#C''#}" (is "?old_aft = ?new_aft")
      using c''_in finite_passive_formulas_of by auto

    have \<mu>1_new: "\<mu>1 ?new_aft ?new_bef"
      unfolding multp_def
    proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
      show "\<mu>1 {#C''#} {#C'#}"
        unfolding multp_def using prec by (auto intro: singletons_in_mult)
    qed
    show ?thesis
      unfolding defs by simp (auto simp only: bef aft intro: \<mu>1_new)
  qed
next
  case (delete_orphan_infers \<iota>s P A Y)
  note defs = this(1,2) and \<iota>s_nemp = this(3) and \<iota>s_sub = this(4)

  have "passive_inferences_of P - set \<iota>s \<subset> passive_inferences_of P"
    by (metis Diff_cancel Diff_subset \<iota>s_nemp \<iota>s_sub double_diff psubsetI set_empty)
  hence "mset_set (passive_inferences_of P - set \<iota>s) \<subset># mset_set (passive_inferences_of P)"
    using finite_passive_inferences_of by (simp add: subset_mset.less_le)
  thus ?thesis
    unfolding defs by (auto intro!: subset_implies_multp image_mset_subset_mono)
qed (use yy yy' in auto)
*)

lemma fair_ZL_Liminf_yy_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ZLf) Sts" and
    inv: "fair_ZL_invariant (lhd Sts)"
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
  have step: "lnth Sts j \<leadsto>ZLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
    using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
    by blast

  have "\<mu>1 (mset_of_zl_fstate (lnth Sts (Suc j))) (mset_of_zl_fstate (lnth Sts j))"
    if j_ge: "j \<ge> i" for j
    using yy_nonempty_ZLf_step_imp_\<mu>1 by (meson step j_ge yy_j yy_sj)
  hence "\<mu>1\<inverse>\<inverse> (mset_of_zl_fstate (lnth Sts j)) (mset_of_zl_fstate (lnth Sts (Suc j)))"
    if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain \<mu>1\<inverse>\<inverse> (ldropn i (lmap mset_of_zl_fstate Sts))"
    using chain_ldropn_lmapI[OF _ si_lt] by blast

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using len by (simp add: llength_eq_infty_conv_lfinite)

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "\<mu>1"]
      wfP_\<mu>1
    by (metis lfinite_ldropn lfinite_lmap)
qed

lemma non_compute_infer_choose_p_ZLf_step_imp_\<mu>2:
  assumes
    step: "St \<leadsto>ZLf St'" and
    non_ci: "\<not> compute_infer_step St St'" and
    non_cp: "\<not> choose_p_step St St'"
  shows "\<mu>2 St' St"
  using step
proof cases
  case (compute_infer T \<iota>0 \<iota>s A C P)
  hence False
    using non_ci[unfolded compute_infer_step.simps] by blast
  thus ?thesis
    by blast
next
  case (choose_p P T A)
  hence False
    using non_cp[unfolded choose_p_step.simps] by blast
  thus ?thesis
    by blast
next
  case (delete_fwd C A T P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs \<mu>2_def by (auto intro!: subset_implies_multp)
next
  case (simplify_fwd C' C A T P)
  note defs = this(1,2) and prec = this(3)

  let ?new_bef = "mset_set (passive.elems P) + mset_set (fset A) + {#C#}"
  let ?new_aft = "mset_set (passive.elems P) + mset_set (fset A) + {#C'#}"

  have "\<mu>1 ?new_aft ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "\<mu>1 {#C'#} {#C#}"
      unfolding multp_def using prec by (auto intro: singletons_in_mult)
  qed
  thus ?thesis
    unfolding defs \<mu>2_def by simp
next
  case (delete_bwd C' A C T P)
  note defs = this(1,2) and c_ni = this(3)
  show ?thesis
    unfolding defs \<mu>2_def using c_ni by (auto simp: fmember.rep_eq intro!: subset_implies_multp)
next
  case (simplify_bwd C' A C'' C T P)
  note defs = this(1,2) and c'_ni = this(3) and prec = this(4)

  show ?thesis
  proof (cases "C'' \<in> passive.elems P")
    case c''_in: True
    show ?thesis
      unfolding defs \<mu>2_def using c'_ni
      by (auto simp: fmember.rep_eq insert_absorb[OF c''_in] intro!: subset_implies_multp)
  next
    case c''_ni: False

    have bef: "add_mset C (mset_set (passive.elems P) + mset_set (insert C' (fset A))) =
      add_mset C (mset_set (passive.elems P) + mset_set (fset A)) + {#C'#}"
      (is "?old_bef = ?new_bef")
      using c'_ni[simplified fmember.rep_eq] by auto
    have aft: "add_mset C (mset_set (insert C'' (passive.elems P)) + mset_set (fset A)) =
      add_mset C (mset_set (passive.elems P) + mset_set (fset A)) + {#C''#}"
      (is "?old_aft = ?new_aft")
      using c''_ni by simp

    have \<mu>1_new: "\<mu>1 ?new_aft ?new_bef"
      unfolding multp_def
    proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
      show "\<mu>1 {#C''#} {#C'#}"
        unfolding multp_def using prec by (auto intro: singletons_in_mult)
    qed
    show ?thesis
      unfolding defs \<mu>2_def by simp (simp only: bef aft \<mu>1_new)
  qed
next
  case (schedule_infer \<iota>ss A C T P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs \<mu>2_def by auto
next
  case (delete_orphan_infers \<iota>s T A P Y)
  note defs = this(1,2) and \<iota>s = this(3)
  have "fcard (t_felems T |-| {|\<iota>s|}) < fcard (t_felems T)"
    using \<iota>s by (meson fcard_fminus1_less notin_fset)
  thus ?thesis
    unfolding defs \<mu>2_def by simp
qed

lemma ZLf_step_imp_passive_step:
  assumes "St \<leadsto>ZLf St'"
  shows "passive.passive_step (passive_of St) (passive_of St')"
  using assms
  by cases (auto simp: fold_map[symmetric] intro: passive.passive_step_idleI
      passive.passive_step_addI passive.passive_step_removeI)

lemma choose_p_step_imp_select_passive_step:
  assumes "choose_p_step St St'"
  shows "passive.select_passive_step (passive_of St) (passive_of St')"
  using assms
proof cases
  case (1 P T A)
  note defs = this(1,2) and p_nemp = this(3)
  show ?thesis
    unfolding defs prod.sel by (rule passive.select_passive_stepI[OF p_nemp])
qed

lemma fair_ZL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ZLf) Sts" and
    init: "is_initial_fair_ZL_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<Longrightarrow> infinitely_often choose_p_step Sts"
  shows "Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts) = {}"
proof -
  have chain_step: "chain passive.passive_step (lmap passive_of Sts)"
    using ZLf_step_imp_passive_step chain_lmap full_chain_imp_chain[OF full]
    by (metis (no_types, lifting))

  have inf_oft: "infinitely_often passive.select_passive_step (lmap passive_of Sts)"
  proof
    assume "finitely_often passive.select_passive_step (lmap passive_of Sts)"
    hence fin_cp: "finitely_often choose_p_step Sts"
      unfolding finitely_often_def choose_p_step_imp_select_passive_step
      by (smt choose_p_step_imp_select_passive_step enat_ord_code(4) len llength_lmap lnth_lmap)
    hence fin_ci: "finitely_often compute_infer_step Sts"
      using fair by blast

    obtain i_ci :: nat where
      i_ci: "\<forall>j \<ge> i_ci. \<not> compute_infer_step (lnth Sts j) (lnth Sts (Suc j))"
      using fin_ci len unfolding finitely_often_def by auto
    obtain i_cp :: nat where
      i_cp: "\<forall>j \<ge> i_cp. \<not> choose_p_step (lnth Sts j) (lnth Sts (Suc j))"
      using fin_cp len unfolding finitely_often_def by auto
    define i :: nat where
      i: "i = max i_cp i_ci"

    have si_lt: "enat (Suc i) < llength Sts"
      unfolding len by auto

    have not_ci: "\<not> compute_infer_step (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using i i_ci j_ge by auto
    have not_cp: "\<not> choose_p_step (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using i i_cp j_ge by auto

    have step: "lnth Sts j \<leadsto>ZLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
      using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
      by blast

    have "\<mu>2 (lnth Sts (Suc j)) (lnth Sts j)" if j_ge: "j \<ge> i" for j
      by (rule non_compute_infer_choose_p_ZLf_step_imp_\<mu>2[OF step[OF j_ge] not_ci[OF j_ge]
            not_cp[OF j_ge]])
    hence "\<mu>2\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using j_ge by blast
    hence inf_down_chain: "chain \<mu>2\<inverse>\<inverse> (ldropn i Sts)"
      using chain_ldropn_lmapI[OF _ si_lt, of _ id, simplified llist.map_id] by simp
    have inf_i: "\<not> lfinite (ldropn i Sts)"
      using len lfinite_ldropn llength_eq_infty_conv_lfinite by blast
    show False
      using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of \<mu>2] wfP_\<mu>2 by blast
  qed

  have hd_emp: "lhd (lmap passive_of Sts) = p_empty"
    using init full full_chain_not_lnull unfolding is_initial_fair_ZL_state.simps by fastforce

  have "Liminf_llist (lmap passive.elems (lmap passive_of Sts)) = {}"
    by (rule passive.fair[of "lmap passive_of Sts", OF chain_step inf_oft hd_emp])
  thus ?thesis
    by (simp add: llist.map_comp)
qed

theorem
  assumes
    full: "full_chain (\<leadsto>ZLf) Sts" and
    init: "is_initial_fair_ZL_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<Longrightarrow> infinitely_often choose_p_step Sts" and
    bot: "B \<in> Bot_F" and
    unsat: "passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"
  shows
    ZL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> formulas_union (Liminf_zl_fstate Sts)" and
    ZL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
proof -
  have chain: "chain (\<leadsto>ZLf) Sts"
    by (rule full_chain_imp_chain[OF full])
  have lgc_chain: "chain (\<leadsto>LGC) (lmap zl_fstate Sts)"
    using chain fair_ZL_step_imp_GC_step chain_lmap by (smt (verit) zl_fstate.cases)

  have inv: "fair_ZL_invariant (lhd Sts)"
    using init initial_fair_ZL_invariant by auto

  have nnul: "\<not> lnull Sts"
    using chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_fair_ZL_state.cases init snd_conv)
  hence act: "active_subset (snd (lhd (lmap zl_fstate Sts))) = {}"
    unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas_fml_and_t_inf: "passive_subset (Liminf_llist (lmap (snd \<circ> zl_fstate) Sts)) = {} \<and>
    Liminf_llist (lmap (fst \<circ> zl_fstate) Sts) = {}" (is "?pas_fml \<and> ?t_inf")
  proof (cases "lfinite Sts")
    case fin: True

    have lim_fst: "Liminf_llist (lmap (fst \<circ> zl_fstate) Sts) = fst (zl_fstate (llast Sts))" and
      lim_snd: "Liminf_llist (lmap (snd \<circ> zl_fstate) Sts) = snd (zl_fstate (llast Sts))"
      using lfinite_Liminf_llist fin nnul
      by (metis comp_eq_dest_lhs lfinite_lmap llast_lmap llist.map_disc_iff)+

    have last_inv: "fair_ZL_invariant (llast Sts)"
      by (rule chain_fair_ZL_invariant_llast[OF chain inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>ZLf St'"
      using full_chain_lnth_not_rel[OF full] by (metis fin full_chain_iff_chain full)
    hence "is_final_fair_ZL_state (llast Sts)"
      unfolding is_final_fair_ZL_state_iff_no_ZLf_step[OF last_inv] .
    then obtain A :: "'f fset" where
      at_l: "llast Sts = (t_empty, p_empty, None, A)"
      unfolding is_final_fair_ZL_state.simps by blast

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
      unfolding Liminf_zl_fstate_commute passive_subset_def Liminf_zl_fstate_def
      using fair_ZL_Liminf_passive_empty[OF len full init fair]
        fair_ZL_Liminf_yy_empty[OF len full inv]
      by simp
    moreover have ?t_inf
      unfolding zl_fstate_alt_def
(*
      using fair_ZL_Liminf_passive_inferences_empty[OF len full init]
      by simp
*)
      sorry
    ultimately show ?thesis
      by blast
  qed
  note pas_fml = pas_fml_and_t_inf[THEN conjunct1] and
    t_inf = pas_fml_and_t_inf[THEN conjunct2]

  have no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd (lmap zl_fstate Sts))"
    using init[unfolded is_initial_fair_ZL_state.simps no_labels.Inf_from_empty]
    by (metis (no_types, lifting) bot_fset.rep_eq fst_conv lhd_lmap no_labels.Inf_from_empty
        premise_free_inf_always_from sup_bot.right_neutral todo.elems_fold_add todo.felems_empty
        zl_fstate.simps zl_state.simps)

  have unsat': "fst ` snd (lhd (lmap zl_fstate Sts)) \<Turnstile>\<inter>\<G> {B}"
    using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

  have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap (snd \<circ> zl_fstate) Sts)"
    by (rule lgc_complete_Liminf[of "lmap zl_fstate Sts", unfolded llist.map_comp,
          OF lgc_chain act pas_fml no_prems_init t_inf bot unsat'])
  thus "\<exists>B \<in> Bot_F. B \<in> formulas_union (Liminf_zl_fstate Sts)"
    unfolding Liminf_zl_fstate_def Liminf_zl_fstate_commute by auto
  thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_formulas_of (lnth Sts i))"
    unfolding Liminf_zl_fstate_def Liminf_llist_def by auto
qed

end


subsection \<open>Specialization with FIFO Queue\<close>

text \<open>As a proof of concept, we specialize the passive set to use a FIFO queue,
thereby eliminating the locale assumptions about the passive set.\<close>

locale fifo_zipperposition_loop =
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
    countable_Inf_between: "finite A \<Longrightarrow> countable (no_labels.Inf_between A {C})"
begin

sublocale fifo_passive_set
  .

sublocale fair_zipperposition_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q
  Equiv_F Prec_F "[]" hd "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list "[]" hd
  "\<lambda>y xs. if y \<in> set xs then xs else xs @ [y]" removeAll fset_of_list Prec_S
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
  show "\<And>A C. finite A \<Longrightarrow> countable (no_labels.Inf_between A {C})"
    by (fact countable_Inf_between)
qed

end

end
