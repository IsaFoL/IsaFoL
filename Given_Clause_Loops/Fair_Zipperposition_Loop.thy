(* Title:        Fair Zipperposition Loop with Ghosts
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Fair Zipperposition Loop with Ghosts\<close>

theory Fair_Zipperposition_Loop
  imports
    Given_Clause_Loops_Util
    Zipperposition_Loop
    Prover_Lazy_List_Queue
begin

text \<open>The fair Zipperposition loop makes assumptions about the scheduled
inference queue and the passive clause queue and ensures (dynamic) refutational
completeness under these assumptions. This version inherits the ghost state
component from the ``unfair'' version of the loop.\<close>

subsection \<open>Locale\<close>

type_synonym ('t, 'p, 'f) ZLf_state = "'t \<times> 'f inference set \<times> 'p \<times> 'f option \<times> 'f fset"

locale fair_zipperposition_loop =
  discount_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  todo: fair_prover_lazy_list_queue t_empty t_add_llist t_remove_llist t_pick_elem t_llists +
  passive: fair_prover_queue p_empty p_select p_add p_remove p_felems
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
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) and
    t_empty :: 't and
    t_add_llist :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_remove_llist :: "'f inference llist \<Rightarrow> 't \<Rightarrow> 't" and
    t_pick_elem :: "'t \<Rightarrow> 'f inference \<times> 't" and
    t_llists :: "'t \<Rightarrow> 'f inference llist multiset" and
    p_empty :: 'p and
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


subsection \<open>Basic Definitions and Lemmas\<close>

abbreviation todo_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 't" where
  "todo_of St \<equiv> fst St"
abbreviation done_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f inference set" where
  "done_of St \<equiv> fst (snd St)"
abbreviation passive_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd (snd St))"
abbreviation yy_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd (snd St)))"
abbreviation active_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd (snd (snd St)))"

abbreviation all_formulas_of :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> passive.elems (passive_of St) \<union> set_option (yy_of St) \<union> fset (active_of St)"

fun zl_fstate :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f inference set \<times> ('f \<times> DL_label) set" where
  "zl_fstate (T, D, P, Y, A) = zl_state (t_llists T, D, passive.elems P, set_option Y, fset A)"

lemma zl_fstate_alt_def:
  "zl_fstate St = zl_state (t_llists (fst St), fst (snd St), passive.elems (fst (snd (snd St))),
     set_option (fst (snd (snd (snd St)))), fset (snd (snd (snd (snd St)))))"
  by (cases St) auto

definition
  Liminf_zl_fstate :: "('t, 'p, 'f) ZLf_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set"
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
  fair_ZL :: "('t, 'p, 'f) ZLf_state \<Rightarrow> ('t, 'p, 'f) ZLf_state \<Rightarrow> bool" (infix "\<leadsto>ZLf" 50)
where
  compute_infer: "(\<exists>\<iota>s \<in># t_llists T. \<iota>s \<noteq> LNil) \<Longrightarrow> t_pick_elem T = (\<iota>0, T') \<Longrightarrow>
    \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (T, D, P, None, A) \<leadsto>ZLf (T', D \<union> {\<iota>0}, p_add C P, None, A)"
| choose_p: "P \<noteq> p_empty \<Longrightarrow>
    (T, D, P, None, A) \<leadsto>ZLf (T, D, p_remove (p_select P) P, Some (p_select P), A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (T, D, P, Some C, A) \<leadsto>ZLf (T, D, P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (T, D, P, Some C, A) \<leadsto>ZLf (T, D, P, Some C', A)"
| delete_bwd: "C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (T, D, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLf (T, D, P, Some C, A)"
| simplify_bwd: "C' |\<notin>| A \<Longrightarrow> C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (T, D, P, Some C, A |\<union>| {|C'|}) \<leadsto>ZLf (T, D, p_add C'' P, Some C, A)"
| schedule_infer: "flat_inferences_of (mset \<iota>ss) = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (T, D, P, Some C, A) \<leadsto>ZLf
    (fold t_add_llist \<iota>ss T, D - flat_inferences_of (mset \<iota>ss), P, None, A |\<union>| {|C|})"
| delete_orphan_infers: "\<iota>s \<in># t_llists T \<Longrightarrow> lset \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (T, D, P, Y, A) \<leadsto>ZLf (t_remove_llist \<iota>s T, D \<union> lset \<iota>s, P, Y, A)"

inductive compute_infer_step :: "('t, 'p, 'f) ZLf_state \<Rightarrow> ('t, 'p, 'f) ZLf_state \<Rightarrow> bool" where
  "(\<exists>\<iota>s \<in># t_llists T. \<iota>s \<noteq> LNil) \<Longrightarrow> t_pick_elem T = (\<iota>0, T') \<Longrightarrow>
   \<iota>0 \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
   compute_infer_step (T, D, P, None, A) (T', D \<union> {\<iota>0}, p_add C P, None, A)"

text \<open>The step below is slightly more general than the corresponding step in
@{const fair_ZL}, in the way it handles the @{text D} component. The extra
generality simplifies an argument later, when we erase the @{text D} ``ghost''
component of the state.\<close>

inductive choose_p_step :: "('t, 'p, 'f) ZLf_state \<Rightarrow> ('t, 'p, 'f) ZLf_state \<Rightarrow> bool" where
  "P \<noteq> p_empty \<Longrightarrow>
   choose_p_step (T, D, P, None, A) (T, D', p_remove (p_select P) P, Some (p_select P), A)"


subsection \<open>Initial State and Invariant\<close>

inductive is_initial_ZLf_state :: "('t, 'p, 'f) ZLf_state \<Rightarrow> bool" where
  "flat_inferences_of (mset \<iota>ss) = no_labels.Inf_from {} \<Longrightarrow>
   is_initial_ZLf_state (fold t_add_llist \<iota>ss t_empty, {}, p_empty, None, {||})"

inductive ZLf_invariant :: "('t, 'p, 'f) ZLf_state \<Rightarrow> bool" where
  "flat_inferences_of (t_llists T) \<subseteq> Inf_F \<Longrightarrow> ZLf_invariant (T, D, P, Y, A)"

lemma initial_ZLf_invariant:
  assumes "is_initial_ZLf_state St"
  shows "ZLf_invariant St"
  using assms
proof
  fix \<iota>ss
  assume
    st: "St = (fold t_add_llist \<iota>ss t_empty, {}, p_empty, None, {||})" and
    \<iota>ss: "flat_inferences_of (mset \<iota>ss) = no_labels.Inf_from {}"

  have "flat_inferences_of (t_llists (fold t_add_llist \<iota>ss t_empty)) \<subseteq> Inf_F"
    using \<iota>ss no_labels.Inf_if_Inf_from by force
  thus "ZLf_invariant St"
    unfolding st using ZLf_invariant.intros by blast
qed

lemma step_ZLf_invariant:
  assumes
    inv: "ZLf_invariant St" and
    step: "St \<leadsto>ZLf St'"
  shows "ZLf_invariant St'"
  using step inv
proof cases
  case (compute_infer T \<iota>0 T' A C D P)
  note defs = this(1,2) and has_el = this(3) and pick = this(4)

  have t': "T' = snd (t_pick_elem T)"
    using pick by simp

  obtain \<iota>s' where
    \<iota>0\<iota>s'_in: "LCons \<iota>0 \<iota>s' \<in># t_llists T" and
    lists_t': "t_llists T' = t_llists T - {#LCons \<iota>0 \<iota>s'#} + {#\<iota>s'#}"
    using todo.llists_pick_elem[OF has_el, folded t'] pick by auto

  let ?II = "{lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T}"
  let ?I = "\<Union> ?II"

  have "\<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T - {#LCons \<iota>0 \<iota>s'#} + {#\<iota>s'#}} =
    (\<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T - {#LCons \<iota>0 \<iota>s'#}}) \<union> lset \<iota>s'"
    by auto
  also have "... \<subseteq> (\<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T - {#LCons \<iota>0 \<iota>s'#}}) \<union> {\<iota>0} \<union> lset \<iota>s'"
    unfolding lists_t'
    by auto
  also have "... \<subseteq> ?I \<union> {\<iota>0} \<union> lset \<iota>s'"
  proof -
    have "\<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T - {#LCons \<iota>0 \<iota>s'#}} \<subseteq> \<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in># t_llists T}"
      using Union_Setcompr_member_mset_mono[of "t_llists T - {#LCons \<iota>0 \<iota>s'#}" "t_llists T" lset]
      by auto
    thus ?thesis
      by blast
  qed
  also have "... \<subseteq> ?I"
  proof -
    have "\<iota>0 \<in> ?I"
      using todo.llists_pick_elem[OF has_el, folded t'] pick by auto
    moreover have "lset \<iota>s' \<subseteq> ?I"
      using todo.llists_pick_elem[OF has_el, folded t'] pick \<iota>0\<iota>s'_in by auto
    ultimately show ?thesis
      by blast
  qed
  finally show ?thesis
    using inv unfolding defs ZLf_invariant.simps by (simp add: lists_t')
next
  case (schedule_infer \<iota>ss A C T D P)
  note defs = this(1,2) and \<iota>ss_inf_betw = this(3)
  have "\<Union> {lset \<iota> |\<iota>. \<iota> \<in> set \<iota>ss} \<subseteq> Inf_F"
    using \<iota>ss_inf_betw unfolding no_labels.Inf_between_def no_labels.Inf_from_def by auto
  thus ?thesis
    using inv unfolding defs ZLf_invariant.simps by simp blast
next
  case (delete_orphan_infers \<iota>s T A D P Y)
  note defs = this(1,2)
  have "\<Union> {lset \<iota> |\<iota>. \<iota> \<in># t_llists T - {#\<iota>s#}} \<subseteq> \<Union> {lset \<iota> |\<iota>. \<iota> \<in># t_llists T}"
    using Union_Setcompr_member_mset_mono[of "t_llists T - {#\<iota>s#}" "t_llists T" lset] by auto
  thus ?thesis
    using inv unfolding defs ZLf_invariant.simps by simp
qed (auto simp: ZLf_invariant.simps)

lemma chain_ZLf_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>ZLf) Sts" and
    fair_hd: "ZLf_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "ZLf_invariant (lnth Sts i)"
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
  hence inv_i: "ZLf_invariant (lnth Sts i)"
    by (rule ih)
  have step: "lnth Sts i \<leadsto>ZLf lnth Sts (Suc i)"
    using chain chain_lnth_rel si_lt by blast

  show ?case
    by (rule step_ZLf_invariant[OF inv_i step])
qed

lemma chain_ZLf_invariant_llast:
  assumes
    chain: "chain (\<leadsto>ZLf) Sts" and
    fair_hd: "ZLf_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "ZLf_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    using i by (metis chain chain_length_pos diff_less enat_ord_simps(2) less_numeral_extra(1)
        zero_enat_def)

  show ?thesis
    using chain_ZLf_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

inductive is_final_ZLf_state :: "('t, 'p, 'f) ZLf_state \<Rightarrow> bool" where
  "is_final_ZLf_state (t_empty, D, p_empty, None, A)"

lemma is_final_ZLf_state_iff_no_ZLf_step:
  assumes inv: "ZLf_invariant St"
  shows "is_final_ZLf_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>ZLf St')"
proof
  assume "is_final_ZLf_state St"
  then obtain D :: "'f inference set" and A :: "'f fset" where
    st: "St = (t_empty, D, p_empty, None, A)"
    by (auto simp: is_final_ZLf_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>ZLf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "(t_empty, D, p_empty, None, A) \<leadsto>ZLf St'"
    thus False
      by cases auto
  qed
next
  assume no_step: "\<forall>St'. \<not> St \<leadsto>ZLf St'"
  show "is_final_ZLf_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_ZLf_state St"

    obtain T :: 't and D :: "'f inference set" and P :: 'p and Y :: "'f option" and
      A :: "'f fset" where
      st: "St = (T, D, P, Y, A)"
      by (cases St)

    have "T \<noteq> t_empty \<or> P \<noteq> p_empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_ZLf_state.simps by auto
    moreover {
      assume
        t: "T \<noteq> t_empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>ZLf St'"
      proof (cases "todo.has_elem T")
        case has_el: True

        obtain \<iota>0 :: "'f inference" and T' :: 't where
          pick: "t_pick_elem T = (\<iota>0, T')"
          by fastforce

        obtain \<iota>s' where
          \<iota>0\<iota>s'_in: "LCons \<iota>0 \<iota>s' \<in># t_llists T" and
          lists_t': "t_llists T' = t_llists T - {#LCons \<iota>0 \<iota>s'#} + {#\<iota>s'#}"
          using todo.llists_pick_elem[OF has_el] pick by auto

        have "\<iota>0 \<in> \<Union> {lset \<iota> |\<iota>. \<iota> \<in># t_llists T}"
          using \<iota>0\<iota>s'_in by auto
        hence "\<iota>0 \<in> Inf_F"
          using inv t unfolding st ZLf_invariant.simps by auto
        hence \<iota>0_red: "\<iota>0 \<in> no_labels.Red_I_\<G> (fset A \<union> {concl_of \<iota>0})"
          by (simp add: no_labels.empty_ord.Red_I_of_Inf_to_N)

        show ?thesis
          using fair_ZL.compute_infer[OF has_el pick \<iota>0_red] unfolding st y by blast
      next
        case has_no_el: False

        have nil_in: "LNil \<in># t_llists T"
          by (metis has_no_el multiset_nonemptyE t todo.llists_not_empty)
        have nil_inter: "lset LNil \<inter> no_labels.Inf_from (fset A) = {}"
          by simp

        show ?thesis
          using fair_ZL.delete_orphan_infers[OF nil_in nil_inter] unfolding st t y by fast
      qed
    }
    moreover
    {
      assume
        p: "P \<noteq> p_empty" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>ZLf St'"
        using fair_ZL.choose_p[OF p] unfolding st p y by fast
    }
    moreover
    {
      assume "Y \<noteq> None"
      then obtain C :: 'f where
        y: "Y = Some C"
        by blast

      obtain \<iota>s :: "'f inference llist" where
        \<iota>ss: "flat_inferences_of (mset [\<iota>s]) = no_labels.Inf_between (fset A) {C}"
        using countable_imp_lset[OF countable_Inf_between[OF finite_fset]] by force

      have "\<exists>St'. St \<leadsto>ZLf St'"
        using fair_ZL.schedule_infer[OF \<iota>ss] unfolding st y by fast
    } ultimately show False
      using no_step by force
  qed
qed


subsection \<open>Refinement\<close>

lemma fair_ZL_step_imp_ZL_step:
  assumes zlf: "(T, D, P, Y, A) \<leadsto>ZLf (T', D', P', Y', A')"
  shows "zl_fstate (T, D, P, Y, A) \<leadsto>ZL zl_fstate (T', D', P', Y', A')"
  using zlf
proof cases
  case (compute_infer \<iota>0 C)
  note defs = this(1-5) and has_el = this(6) and pick = this(7) and \<iota>_red = this(8)

  obtain \<iota>s' where
    \<iota>0\<iota>s'_in: "LCons \<iota>0 \<iota>s' \<in># t_llists T" and
    lists_t': "t_llists T' = t_llists T - {#LCons \<iota>0 \<iota>s'#} + {#\<iota>s'#}"
    using todo.llists_pick_elem[OF has_el] pick by auto

  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set lists_t'
    using ZL.compute_infer[OF \<iota>_red, of "t_llists T - {#LCons \<iota>0 \<iota>s'#}" \<iota>s' D "passive.elems P"]
      \<iota>0\<iota>s'_in
    by auto
next
  case choose_p
  note defs = this(1-6) and p_nemp = this(7)

  have elems_rem_sel_uni_sel:
    "passive.elems (p_remove (p_select P) P) \<union> {p_select P} = passive.elems P"
    using p_nemp by force

  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set
    using ZL.choose_p[of "t_llists T" D "passive.elems (p_remove (p_select P) P)" "p_select P"
        "fset A"]
    by (metis elems_rem_sel_uni_sel)
next
  case (delete_fwd C)
  note defs = this(1-6) and c_red = this(7)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.delete_fwd[OF c_red] by simp
next
  case (simplify_fwd C' C)
  note defs = this(1-6) and c_red = this(8)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.simplify_fwd[OF c_red] by simp
next
  case (delete_bwd C' C)
  note defs = this(1-6) and c'_red = this(8)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.delete_bwd[OF c'_red] by simp
next
  case (simplify_bwd C' C'' C)
  note defs = this(1-6) and c''_red = this(9)
  show ?thesis
    unfolding defs zl_fstate_alt_def using ZL.simplify_bwd[OF c''_red] by simp
next
  case (schedule_infer \<iota>ss C)
  note defs = this(1-6) and \<iota>ss = this(7)
  show ?thesis
    unfolding defs zl_fstate_alt_def prod.sel option.set
    using ZL.schedule_infer[OF \<iota>ss, of "t_llists T" D "passive.elems P"]
    by (simp add: Un_commute)
next
  case (delete_orphan_infers \<iota>s)
  note defs = this(1-5) and \<iota>s_in = this(6) and inter = this(7)

  show ?thesis
    unfolding defs zl_fstate_alt_def todo.llist_remove prod.sel option.set
    using ZL.delete_orphan_infers[OF inter, of "t_llists T - {#\<iota>s#}" D "passive.elems P"
        "set_option Y"]
      \<iota>s_in
    by simp
qed

lemma fair_ZL_step_imp_GC_step:
  "(T, D, P, Y, A) \<leadsto>ZLf (T', D', P', Y', A') \<Longrightarrow>
   zl_fstate (T, D, P, Y, A) \<leadsto>LGC zl_fstate (T', D', P', Y', A')"
  by (rule ZL_step_imp_LGC_step[OF fair_ZL_step_imp_ZL_step])


subsection \<open>Completeness\<close>

fun mset_of_zl_fstate :: "('t, 'p, 'f) ZLf_state \<Rightarrow> 'f multiset" where
  "mset_of_zl_fstate (T, D, P, Y, A) =
   mset_set (passive.elems P) + mset_set (set_option Y) + mset_set (fset A)"

abbreviation Precprec_S :: "'f multiset \<Rightarrow> 'f multiset \<Rightarrow> bool" (infix "\<prec>\<prec>S" 50)  where
  "(\<prec>\<prec>S) \<equiv> multp (\<prec>S)"

lemma wfP_Precprec_S: "wfP (\<prec>\<prec>S)"
  using minimal_element_def wfP_multp wf_Prec_S wfp_on_UNIV by blast

definition Less_state :: "('t, 'p, 'f) ZLf_state \<Rightarrow> ('t, 'p, 'f) ZLf_state \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where
  "St' \<sqsubset> St \<longleftrightarrow>
   mset_of_zl_fstate St' \<prec>\<prec>S mset_of_zl_fstate St
   \<or> (mset_of_zl_fstate St' = mset_of_zl_fstate St
      \<and> (mset_set (passive.elems (passive_of St')) \<prec>\<prec>S mset_set (passive.elems (passive_of St))
         \<or> (passive.elems (passive_of St') = passive.elems (passive_of St)
            \<and> (mset_set (set_option (yy_of St')) \<prec>\<prec>S mset_set (set_option (yy_of St))
               \<or> (mset_set (set_option (yy_of St')) = mset_set (set_option (yy_of St))
                  \<and> size (t_llists (todo_of St')) < size (t_llists (todo_of St)))))))"

lemma wfP_Less_state: "wfP (\<sqsubset>)"
proof -
  let ?msetset = "{(M', M). M' \<prec>\<prec>S M}"
  let ?natset = "{(n', n :: nat). n' < n}"
  let ?quad_of = "\<lambda>St. (mset_of_zl_fstate St, mset_set (passive.elems (passive_of St)),
    mset_set (set_option (yy_of St)), size (t_llists (todo_of St)))"

  have wf_msetset: "wf ?msetset"
    using wfP_Precprec_S wfP_def by auto
  have wf_natset: "wf ?natset"
    by (rule Wellfounded.wellorder_class.wf)
  have wf_lex_prod: "wf (?msetset <*lex*> ?msetset <*lex*> ?msetset <*lex*> ?natset)"
    by (rule wf_lex_prod[OF wf_msetset wf_lex_prod[OF wf_msetset
        wf_lex_prod[OF wf_msetset wf_natset]]])

  have Less_state_alt_def: "\<And>St' St. St' \<sqsubset> St \<longleftrightarrow>
    (?quad_of St', ?quad_of St) \<in> ?msetset <*lex*> ?msetset <*lex*> ?msetset <*lex*> ?natset"
    unfolding Less_state_def by auto

  show ?thesis
    unfolding wfP_def Less_state_alt_def using wf_app[of _ ?quad_of] wf_lex_prod by blast
qed

lemma non_compute_infer_ZLf_step_imp_Less_state:
  assumes
    step: "St \<leadsto>ZLf St'" and
    non_ci: "\<not> compute_infer_step St St'"
  shows "St' \<sqsubset> St"
  using step
proof cases
  case (compute_infer T \<iota>0 \<iota>s A C D P)
  hence False
    using non_ci[unfolded compute_infer_step.simps] by blast
  thus ?thesis
    by blast
next
  case (choose_p P T D A)
  note defs = this(1,2)

  have all: "add_mset (p_select P) (mset_set (passive.elems P - {p_select P})) =
    mset_set (passive.elems P)"
    by (metis finite_fset local.choose_p(3) mset_set.remove passive.select_in_elems)
  have pas: "mset_set (passive.elems P - {p_select P}) \<prec>\<prec>S mset_set (passive.elems P)"
    by (metis all multi_psub_of_add_self subset_implies_multp)

  show ?thesis
    unfolding defs Less_state_def by (simp add: all pas)
next
  case (delete_fwd C A T D P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs Less_state_def by (auto intro!: subset_implies_multp)
next
  case (simplify_fwd C' C A T D P)
  note defs = this(1,2) and prec = this(3)

  let ?new_bef = "mset_set (passive.elems P) + mset_set (fset A) + {#C#}"
  let ?new_aft = "mset_set (passive.elems P) + mset_set (fset A) + {#C'#}"

  have "?new_aft \<prec>\<prec>S ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "{#C'#} \<prec>\<prec>S {#C#}"
      unfolding multp_def using prec by (auto intro: singletons_in_mult)
  qed
  thus ?thesis
    unfolding defs Less_state_def by simp
next
  case (delete_bwd C' A C T D P)
  note defs = this(1,2) and c_ni = this(3)
  show ?thesis
    unfolding defs Less_state_def using c_ni
    by (auto simp: fmember.rep_eq intro!: subset_implies_multp)
next
  case (simplify_bwd C' A C'' C T D P)
  note defs = this(1,2) and c'_ni = this(3) and prec = this(4)

  show ?thesis
  proof (cases "C'' \<in> passive.elems P")
    case c''_in: True
    show ?thesis
      unfolding defs Less_state_def using c'_ni
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

    have "?new_aft \<prec>\<prec>S ?new_bef"
      unfolding multp_def
    proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
      show "{#C''#} \<prec>\<prec>S {#C'#}"
        unfolding multp_def using prec by (auto intro: singletons_in_mult)
    qed
    thus ?thesis
      unfolding defs Less_state_def by (simp add: bef aft)
  qed
next
  case (schedule_infer \<iota>ss A C T D P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs Less_state_def
    by simp (metis finite_fset insert_absorb mset_set.insert multi_psub_of_add_self
        subset_implies_multp)
next
  case (delete_orphan_infers \<iota>s T A D P Y)
  note defs = this(1,2) and \<iota>s = this(3)
  have "size (t_llists T - {#\<iota>s#}) < size (t_llists T)"
    using \<iota>s by (simp add: size_Diff1_less)
  thus ?thesis
    unfolding defs Less_state_def by simp
qed

lemma yy_nonempty_ZLf_step_imp_Less_state:
  assumes
    step: "St \<leadsto>ZLf St'" and
    yy: "yy_of St \<noteq> None"
  shows "St' \<sqsubset> St"
proof -
  have "\<not> compute_infer_step St St'"
    using yy unfolding compute_infer_step.simps by auto
  thus ?thesis
    using non_compute_infer_ZLf_step_imp_Less_state[OF step] by blast
qed

lemma fair_ZL_Liminf_yy_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ZLf) Sts" and
    inv: "ZLf_invariant (lhd Sts)"
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
  have step: "lnth Sts j \<leadsto>ZLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
    using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
    by blast

  have "lnth Sts (Suc j) \<sqsubset> lnth Sts j" if j_ge: "j \<ge> i" for j
    using yy_nonempty_ZLf_step_imp_Less_state by (meson step j_ge yy_j)
  hence "(\<sqsubset>)\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))"
    if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain (\<sqsubset>)\<inverse>\<inverse> (ldropn i Sts)"
    by (simp add: chain_ldropnI si_lt)

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using len by (simp add: llength_eq_infty_conv_lfinite)

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<sqsubset>)"] wfP_Less_state
    by metis
qed

lemma ZLf_step_imp_passive_queue_step:
  assumes "St \<leadsto>ZLf St'"
  shows "passive.queue_step (passive_of St) (passive_of St')"
  using assms
  by cases (auto intro: passive.queue_step_idleI passive.queue_step_addI
      passive.queue_step_removeI)

lemma choose_p_step_imp_select_passive_queue_step:
  assumes "choose_p_step St St'"
  shows "passive.select_queue_step (passive_of St) (passive_of St')"
  using assms
proof cases
  case (1 P T D A)
  note defs = this(1,2) and p_nemp = this(3)
  show ?thesis
    unfolding defs prod.sel by (rule passive.select_queue_stepI[OF p_nemp])
qed

lemma fair_ZL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ZLf) Sts" and
    init: "is_initial_ZLf_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<longrightarrow> infinitely_often choose_p_step Sts"
  shows "Liminf_llist (lmap (passive.elems \<circ> passive_of) Sts) = {}"
proof -
  have chain_step: "chain passive.queue_step (lmap passive_of Sts)"
    using ZLf_step_imp_passive_queue_step chain_lmap full_chain_imp_chain[OF full]
    by (metis (no_types, lifting))

  have inf_oft: "infinitely_often passive.select_queue_step (lmap passive_of Sts)"
  proof
    assume "finitely_often passive.select_queue_step (lmap passive_of Sts)"
    hence fin_cp: "finitely_often choose_p_step Sts"
      unfolding finitely_often_def choose_p_step_imp_select_passive_queue_step
      by (smt choose_p_step_imp_select_passive_queue_step enat_ord_code(4) len llength_lmap
          lnth_lmap)
    hence fin_ci: "finitely_often compute_infer_step Sts"
      using fair by blast

    obtain i :: nat where
      i: "\<forall>j \<ge> i. \<not> compute_infer_step (lnth Sts j) (lnth Sts (Suc j))"
      using fin_ci len unfolding finitely_often_def by auto

    have si_lt: "enat (Suc i) < llength Sts"
      unfolding len by auto

    have not_ci: "\<not> compute_infer_step (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using i j_ge by auto

    have step: "lnth Sts j \<leadsto>ZLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
      by (simp add: full_chain_lnth_rel[OF full] len)

    have "lnth Sts (Suc j) \<sqsubset> lnth Sts j" if j_ge: "j \<ge> i" for j
      by (rule non_compute_infer_ZLf_step_imp_Less_state[OF step[OF j_ge] not_ci[OF j_ge]])
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

  have hd_emp: "lhd (lmap passive_of Sts) = p_empty"
    using init full full_chain_not_lnull unfolding is_initial_ZLf_state.simps by fastforce

  have "Liminf_llist (lmap passive.elems (lmap passive_of Sts)) = {}"
    by (rule passive.fair[OF chain_step inf_oft hd_emp])
  thus ?thesis
    by (simp add: llist.map_comp)
qed

lemma ZLf_step_imp_todo_queue_step:
  assumes "St \<leadsto>ZLf St'"
  shows "todo.lqueue_step (todo_of St, done_of St) (todo_of St', done_of St')"
  using assms
proof cases
  case (compute_infer T \<iota>0 T' A C D P)
  note defs = this(1,2) and has_el = this(3) and pick = this(4)
  have t': "T' = snd (t_pick_elem T)"
    using pick by simp
  show ?thesis
    unfolding defs prod.sel t' using todo.lqueue_step_pick_elemI[OF has_el] by (simp add: pick)
next
  case (schedule_infer \<iota>ss A C T D P)
  note defs = this(1,2) and betw = this(3)
  show ?thesis
    unfolding defs prod.sel using todo.lqueue_step_fold_add_llistI[of T D \<iota>ss] by simp
qed (auto intro: todo.lqueue_step_idleI todo.lqueue_step_fold_add_llistI
  todo.lqueue_step_remove_llistI)

lemma fair_ZL_Liminf_todo_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ZLf) Sts" and
    init: "is_initial_ZLf_state (lhd Sts)"
  shows "Liminf_llist (lmap (\<lambda>St. flat_inferences_of (t_llists (todo_of St)) - done_of St) Sts) =
    {}"
proof -
  define Infs where
    "Infs = lmap (\<lambda>St. flat_inferences_of (t_llists (todo_of St)) - done_of St) Sts"
  define flat_Ts where
    "flat_Ts = lmap (\<lambda>St. flat_inferences_of (t_llists (todo_of St))) Sts"
  define TDs where
    "TDs = lmap (\<lambda>St. (todo_of St, done_of St)) Sts"

  {
    fix i \<iota>
    assume \<iota>_in_infs: "\<iota> \<in> lnth Infs i"

    have lt_sts: "enat n < llength Sts" for n
      by (simp add: len)
    have lt_tds: "enat n < llength TDs" for n
      by (simp add: TDs_def len)

    have chain_ts: "chain todo.lqueue_step TDs"
    proof -
      have fst_tds: "lmap fst TDs = lmap todo_of Sts"
        unfolding TDs_def by (simp add: llist.map_comp)
      have snd_tds: "lmap snd TDs = lmap done_of Sts"
        unfolding TDs_def by (simp add: llist.map_comp)
      show ?thesis
        unfolding fst_tds
        using TDs_def ZLf_step_imp_todo_queue_step chain_lmap full full_chain_imp_chain
        by (metis (lifting))
    qed

    have inf_oft: "infinitely_often todo.pick_lqueue_step TDs"
    proof
      assume "finitely_often todo.pick_lqueue_step TDs"
      then obtain i :: nat where
        no_pick: "\<forall>j \<ge> i. \<not> todo.pick_lqueue_step (lnth TDs j) (lnth TDs (Suc j))"
        by (metis infinitely_often_alt_def lt_tds)

      have si_lt: "enat (Suc i) < llength Sts"
        unfolding len by auto

      have step: "lnth Sts j \<leadsto>ZLf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
        using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len
          llength_eq_infty_conv_lfinite
        by blast

      have non_ci: "\<not> compute_infer_step (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      proof -
        {
          assume "compute_infer_step (lnth Sts j) (lnth Sts (Suc j))"
          hence "\<exists>j \<ge> i. todo.pick_lqueue_step (lnth TDs j) (lnth TDs (Suc j))"
            using assms
          proof cases
            case (1 T \<iota>0 T' A C D P)
            note sts_at_j = this(1) and sts_at_sj = this(2) and has_el = this(3) and pick = this(4)

            obtain \<iota>0' :: "'f inference" and \<iota>s :: "'f inference llist" where
              cons_in0: "LCons \<iota>0' \<iota>s \<in># t_llists T" and
              fst0: "fst (t_pick_elem T) = \<iota>0'" and
              snd0: "t_llists (snd (t_pick_elem T)) = t_llists T - {#LCons \<iota>0' \<iota>s#} + {#\<iota>s#}"
              using todo.llists_pick_elem[OF has_el] by blast

            have \<iota>0': "\<iota>0' = \<iota>0"
              using pick fst0 by auto

            have
              cons_in: "LCons \<iota>0 \<iota>s \<in># t_llists T" and
              fst: "fst (t_pick_elem T) = \<iota>0" and
              snd: "t_llists (snd (t_pick_elem T)) = t_llists T - {#LCons \<iota>0 \<iota>s#} + {#\<iota>s#}"
              unfolding \<iota>0'[symmetric] by (auto simp: cons_in0 fst0 snd0)

            have td_at_j: "lnth TDs j = (T, D)"
              using sts_at_j TDs_def lt_tds by auto
            have td_at_sj: "lnth TDs (Suc j) = (snd (t_pick_elem T), insert \<iota>0 D)"
              using sts_at_sj TDs_def lt_tds pick by force

            have "todo.pick_lqueue_step (lnth TDs j) (lnth TDs (Suc j))"
              by (simp add: todo.pick_lqueue_step.simps todo.pick_lqueue_step_w_details.simps,
                  rule exI[of _ \<iota>s], rule exI[of _ T], rule exI[of _ D],
                  simp add: td_at_j td_at_sj cons_in fst snd)
            thus ?thesis
              using j_ge by blast
          qed
        }
        thus ?thesis
          using no_pick by blast
      qed

      have "lnth Sts (Suc j) \<sqsubset> lnth Sts j" if j_ge: "j \<ge> i" for j
        by (rule non_compute_infer_ZLf_step_imp_Less_state[OF step[OF j_ge] non_ci[OF j_ge]])
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

    have "\<iota> \<in> lnth flat_Ts i"
      using \<iota>_in_infs unfolding Infs_def flat_Ts_def by (simp add: lt_sts)
    then obtain \<iota>s :: "'f inference llist" where
      \<iota>s_in: "\<iota>s \<in># t_llists (fst (lnth TDs i))" and
      \<iota>_in_\<iota>s: "\<iota> \<in> lset \<iota>s"
      using lnth_lmap[OF lt_sts] unfolding flat_Ts_def TDs_def
      by (smt (verit, ccfv_SIG) Union_iff flat_inferences_of.simps fst_conv mem_Collect_eq)

    obtain k :: nat where
      k_lt: "enat k < llength \<iota>s" and
      at_k: "lnth \<iota>s k = \<iota>"
      using \<iota>_in_\<iota>s by (meson in_lset_conv_lnth)

    obtain j :: nat where
      j_ge: "j \<ge> i" and
      rem_or_pick_step: "(\<exists>k' \<le> k. \<exists>\<iota>ss.
          ldrop (enat k') \<iota>s \<in> set \<iota>ss \<and> todo.remove_lqueue_step_w_details (lnth TDs j) \<iota>ss
             (lnth TDs (Suc j)))
        \<or> todo.pick_lqueue_step_w_details (lnth TDs j) (lnth \<iota>s k) (ldrop (enat (Suc k)) \<iota>s)
          (lnth TDs (Suc j))"
      using todo.fair_strong[OF chain_ts inf_oft \<iota>s_in k_lt] by blast

    have "\<exists>j. j \<ge> i \<and> j < llength Sts \<and> \<iota> \<notin> lnth Infs j"
    proof (rule exI[of _ "Suc j"], intro conjI)
      {
        assume "\<exists>k' \<le> k. \<exists>\<iota>ss. ldrop (enat k') \<iota>s \<in> set \<iota>ss
          \<and> todo.remove_lqueue_step_w_details (lnth TDs j) \<iota>ss (lnth TDs (Suc j))"
        then obtain k' :: nat and \<iota>ss :: "'f inference llist list" where
          k'_le: "k' \<le> k" and
          in_\<iota>ss: "ldrop (enat k') \<iota>s \<in> set \<iota>ss" and
          rem_step: "todo.remove_lqueue_step_w_details (lnth TDs j) \<iota>ss (lnth TDs (Suc j))"
          by blast

        have "\<iota> \<notin> lnth Infs (Suc j)"
          using rem_step
        proof cases
          case (remove_lqueue_step_w_detailsI Q D)
          note at_j = this(1) and at_sj = this(2)

          have don: "done_of (lnth Sts (Suc j)) = D \<union> \<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in> set \<iota>ss}"
            unfolding at_sj using TDs_def at_sj len by auto

          have "\<iota> \<in> lset (ldrop (enat k') \<iota>s)"
          proof -
            have nth_drop: "lnth (ldrop (enat k') \<iota>s) (k - k') = \<iota>"
              by (simp add: at_k k'_le k_lt)
            thus ?thesis
              using at_k k'_le k_lt by (smt (verit, del_insts) enat.distinct(1)
                  enat_diff_cancel_left enat_minus_mono1 enat_ord_simps(1) idiff_enat_enat
                  in_lset_conv_lnth llength_ldrop nless_le order_le_less_subst2)
          qed
          hence "\<iota> \<in> \<Union> {lset \<iota>s |\<iota>s. \<iota>s \<in> set \<iota>ss}"
            using in_\<iota>ss by blast
          thus ?thesis
            unfolding Infs_def lnth_lmap[OF lt_sts] don by auto
        qed
      }
      moreover
      {
        assume "todo.pick_lqueue_step_w_details (lnth TDs j) (lnth \<iota>s k) (ldrop (enat (Suc k)) \<iota>s)
          (lnth TDs (Suc j))"
        hence "\<iota> \<notin> lnth Infs (Suc j)"
        proof cases
          case (pick_lqueue_step_w_detailsI Q D)
          note at_j = this(1) and at_sj = this(2)

          have don: "done_of (lnth Sts (Suc j)) = D \<union> {\<iota>}"
            using at_sj at_k by (simp add: TDs_def len)

          show ?thesis
            unfolding Infs_def lnth_lmap[OF lt_sts] don by auto
        qed
      }
      ultimately show "\<iota> \<notin> lnth Infs (Suc j)"
        using rem_or_pick_step by blast
    qed (use j_ge lt_sts in auto)
  }
  thus ?thesis
    unfolding Infs_def[symmetric] Liminf_llist_def
    by clarsimp (smt Infs_def Collect_empty_eq INT_iff Inf_set_def dual_order.refl llength_lmap
        mem_Collect_eq)
qed

theorem
  assumes
    full: "full_chain (\<leadsto>ZLf) Sts" and
    init: "is_initial_ZLf_state (lhd Sts)" and
    fair: "infinitely_often compute_infer_step Sts \<longrightarrow> infinitely_often choose_p_step Sts"
  shows
    fair_ZL_Liminf_saturated: "saturated (labeled_formulas_of (Liminf_zl_fstate Sts))" and
    fair_ZL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_zl_fstate Sts)" and
    fair_ZL_complete: "B \<in> Bot_F \<Longrightarrow> passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
proof -
  have chain: "chain (\<leadsto>ZLf) Sts"
    by (rule full_chain_imp_chain[OF full])
  have zl_chain: "chain (\<leadsto>ZL) (lmap zl_fstate Sts)"
    using chain fair_ZL_step_imp_ZL_step chain_lmap by (smt (verit) zl_fstate.cases)

  have inv: "ZLf_invariant (lhd Sts)"
    using init initial_ZLf_invariant by auto

  have nnul: "\<not> lnull Sts"
    using chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_ZLf_state.cases init snd_conv)
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

    have last_inv: "ZLf_invariant (llast Sts)"
      by (rule chain_ZLf_invariant_llast[OF chain inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>ZLf St'"
      using full_chain_lnth_not_rel[OF full] by (metis fin full_chain_iff_chain full)
    hence "is_final_ZLf_state (llast Sts)"
      unfolding is_final_ZLf_state_iff_no_ZLf_step[OF last_inv] .
    then obtain D :: "'f inference set" and A :: "'f fset" where
      at_l: "llast Sts = (t_empty, D, p_empty, None, A)"
      unfolding is_final_ZLf_state.simps by blast

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
      unfolding zl_fstate_alt_def comp_def zl_state.simps prod.sel
      using fair_ZL_Liminf_todo_empty[OF len full init] .
    ultimately show ?thesis
      by blast
  qed
  note pas_fml = pas_fml_and_t_inf[THEN conjunct1] and
    t_inf = pas_fml_and_t_inf[THEN conjunct2]

  obtain \<iota>ss :: "'f inference llist list" where
    hd: "lhd Sts = (fold t_add_llist \<iota>ss t_empty, {}, p_empty, None, {||})" and
    infs: "flat_inferences_of (mset \<iota>ss) = {\<iota> \<in> Inf_F. prems_of \<iota> = []}"
    using init[unfolded is_initial_ZLf_state.simps no_labels.Inf_from_empty] by blast

  have hd': "lhd (lmap zl_fstate Sts) =
    zl_fstate (fold t_add_llist \<iota>ss t_empty, {}, p_empty, None, {||})"
    using hd by (simp add: lhd_lmap)

  have no_prems_init: "\<forall>\<iota> \<in> Inf_F. prems_of \<iota> = [] \<longrightarrow> \<iota> \<in> fst (lhd (lmap zl_fstate Sts))"
    unfolding zl_fstate_alt_def hd' zl_state_alt_def prod.sel using infs by simp

  show "saturated (labeled_formulas_of (Liminf_zl_fstate Sts))"
    using ZL_Liminf_saturated[of "lmap zl_fstate Sts", unfolded llist.map_comp,
          OF zl_chain act pas_fml no_prems_init t_inf]
    unfolding Liminf_zl_fstate_commute .

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "passive.elems (passive_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"

    have unsat': "fst ` snd (lhd (lmap zl_fstate Sts)) \<Turnstile>\<inter>\<G> {B}"
      using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

    have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap (snd \<circ> zl_fstate) Sts)"
      using ZL_complete_Liminf[of "lmap zl_fstate Sts", unfolded llist.map_comp,
          OF zl_chain act pas_fml no_prems_init t_inf bot unsat'] .
    thus "\<exists>B' \<in> Bot_F. B' \<in> formulas_union (Liminf_zl_fstate Sts)"
      unfolding Liminf_zl_fstate_def Liminf_zl_fstate_commute by auto
    thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
      unfolding Liminf_zl_fstate_def Liminf_llist_def by auto
  }
qed

end

end
