(* Title:        Definition of Fair Otter Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Definition of Fair Otter Loop\<close>

text \<open>The fair Otter loop assumes that the passive queue is fair and ensures
(dynamic) refutational completeness under that assumption. This section contains
only the loop's definition.\<close>

theory Fair_Otter_Loop_Def
  imports
    Otter_Loop
    Prover_Queue
begin


subsection \<open>Locale\<close>

type_synonym ('p, 'f) OLf_state = "'f fset \<times> 'f option \<times> 'p \<times> 'f option \<times> 'f fset"

locale fair_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
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
    empty :: "'p" and
    select :: "'p \<Rightarrow> 'f" and
    add :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    remove :: "'f \<Rightarrow> 'p \<Rightarrow> 'p" and
    felems :: "'p \<Rightarrow> 'f fset" +
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

abbreviation new_of :: "('p, 'f) OLf_state \<Rightarrow> 'f fset" where
  "new_of St \<equiv> fst St"
abbreviation xx_of :: "('p, 'f) OLf_state \<Rightarrow> 'f option" where
  "xx_of St \<equiv> fst (snd St)"
abbreviation passive_of :: "('p, 'f) OLf_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd (snd St))"
abbreviation yy_of :: "('p, 'f) OLf_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd (snd St)))"
abbreviation active_of :: "('p, 'f) OLf_state \<Rightarrow> 'f fset" where
  "active_of St \<equiv> snd (snd (snd (snd St)))"

abbreviation all_formulas_of :: "('p, 'f) OLf_state \<Rightarrow> 'f set" where
  "all_formulas_of St \<equiv> fset (new_of St) \<union> set_option (xx_of St) \<union> elems (passive_of St) \<union>
     set_option (yy_of St) \<union> fset (active_of St)"

fun fstate :: "'f fset \<times> 'f option \<times> 'p \<times> 'f option \<times> 'f fset \<Rightarrow> ('f \<times> OL_label) set" where
  "fstate (N, X, P, Y, A) = state (fset N, set_option X, elems P, set_option Y, fset A)"

lemma fstate_alt_def:
  "fstate St =
   state (fset (fst St), set_option (fst (snd St)), elems (fst (snd (snd St))),
     set_option (fst (snd (snd (snd St)))), fset (snd (snd (snd (snd St)))))"
  by (cases St) auto

definition
  Liminf_fstate :: "('p, 'f) OLf_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_fstate Sts =
   (Liminf_llist (lmap (fset \<circ> new_of) Sts),
    Liminf_llist (lmap (set_option \<circ> xx_of) Sts),
    Liminf_llist (lmap (elems \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap (fset \<circ> active_of) Sts))"

lemma Liminf_fstate_commute: "Liminf_llist (lmap fstate Sts) = state (Liminf_fstate Sts)"
proof -
  have "Liminf_llist (lmap fstate Sts) =
    (\<lambda>C. (C, New)) ` Liminf_llist (lmap (fset \<circ> new_of) Sts) \<union>
    (\<lambda>C. (C, XX)) ` Liminf_llist (lmap (set_option \<circ> xx_of) Sts) \<union>
    (\<lambda>C. (C, Passive)) ` Liminf_llist (lmap (elems \<circ> passive_of) Sts) \<union>
    (\<lambda>C. (C, YY)) ` Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<union>
    (\<lambda>C. (C, Active)) ` Liminf_llist (lmap (fset \<circ> active_of) Sts)"
    unfolding fstate_alt_def state_alt_def
    apply (subst Liminf_llist_lmap_union, fast)+
    apply (subst Liminf_llist_lmap_image, simp add: inj_on_convol_ident)+
    by auto
 thus ?thesis
   unfolding Liminf_fstate_def by fastforce
qed

fun state_union :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f set" where
  "state_union (N, X, P, Y, A) = N \<union> X \<union> P \<union> Y \<union> A"

inductive fair_OL :: "('p, 'f) OLf_state \<Rightarrow> ('p, 'f) OLf_state \<Rightarrow> bool" (infix "\<leadsto>OLf" 50) where
  choose_n: "C |\<notin>| N \<Longrightarrow> (N |\<union>| {|C|}, None, P, None, A) \<leadsto>OLf (N, Some C, P, None, A)"
| delete_fwd: "C \<in> no_labels.Red_F (elems P \<union> fset A) \<or> (\<exists>C' \<in> elems P \<union> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, None, P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (elems P \<union> fset A \<union> {C'}) \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, Some C', P, None, A)"
| delete_bwd_p: "C' \<in> elems P \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, Some C, remove C' P, None, A)"
| simplify_bwd_p: "C'' \<prec>S C' \<Longrightarrow> C' \<in> elems P \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N |\<union>| {|C''|}, Some C, remove C' P, None, A)"
| delete_bwd_a: "C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, Some C, P, None, A |\<union>| {|C'|}) \<leadsto>OLf (N, Some C, P, None, A)"
| simplify_bwd_a: "C'' \<prec>S C' \<Longrightarrow> C' |\<notin>| A \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, Some C, P, None, A |\<union>| {|C'|}) \<leadsto>OLf (N |\<union>| {|C''|}, Some C, P, None, A)"
| transfer: "(N, Some C, P, None, A) \<leadsto>OLf (N, None, add C P, None, A)"
| choose_p: "P \<noteq> empty \<Longrightarrow>
    ({||}, None, P, None, A) \<leadsto>OLf ({||}, None, remove (select P) P, Some (select P), A)"
| infer: "no_labels.Inf_between (fset A) {C} \<subseteq> no_labels.Red_I (fset A \<union> {C} \<union> fset M) \<Longrightarrow>
    ({||}, None, P, Some C, A) \<leadsto>OLf (M, None, P, None, A |\<union>| {|C|})"


subsection \<open>Initial State and Invariant\<close>

inductive is_initial_OLf_state :: "('p, 'f) OLf_state \<Rightarrow> bool" where
  "is_initial_OLf_state (N, None, empty, None, {||})"

inductive OLf_invariant :: "('p, 'f) OLf_state \<Rightarrow> bool" where
  "(N = {||} \<and> X = None) \<or> Y = None \<Longrightarrow> OLf_invariant (N, X, P, Y, A)"

lemma initial_OLf_invariant: "is_initial_OLf_state St \<Longrightarrow> OLf_invariant St"
  unfolding is_initial_OLf_state.simps OLf_invariant.simps by auto

lemma step_OLf_invariant:
  assumes step: "St \<leadsto>OLf St'"
  shows "OLf_invariant St'"
  using step by cases (auto intro: OLf_invariant.intros)

lemma chain_OLf_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>OLf) Sts" and
    fair_hd: "OLf_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "OLf_invariant (lnth Sts i)"
  using i_lt
proof (induct i)
  case 0
  thus ?case
    using fair_hd lhd_conv_lnth zero_enat_def by fastforce
next
  case (Suc i)
  thus ?case
    using chain chain_lnth_rel step_OLf_invariant by blast
qed

lemma chain_OLf_invariant_llast:
  assumes
    chain: "chain (\<leadsto>OLf) Sts" and
    fair_hd: "OLf_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "OLf_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    using i by (metis chain chain_length_pos diff_less enat_ord_simps(2) less_numeral_extra(1)
        zero_enat_def)

  show ?thesis
    using chain_OLf_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

inductive is_final_OLf_state :: "('p, 'f) OLf_state \<Rightarrow> bool" where
  "is_final_OLf_state ({||}, None, empty, None, A)"

lemma is_final_OLf_state_iff_no_OLf_step:
  assumes inv: "OLf_invariant St"
  shows "is_final_OLf_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>OLf St')"
proof
  assume "is_final_OLf_state St"
  then obtain A :: "'f fset" where
    st: "St = ({||}, None, empty, None, A)"
    by (auto simp: is_final_OLf_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>OLf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "({||}, None, empty, None, A) \<leadsto>OLf St'"
    thus False
      by cases auto
  qed
next
  assume no_step: "\<forall>St'. \<not> St \<leadsto>OLf St'"
  show "is_final_OLf_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_OLf_state St"

    obtain N A :: "'f fset" and X Y :: "'f option" and P :: 'p where
      st: "St = (N, X, P, Y, A)"
      by (cases St)

    have inv': "(N = {||} \<and> X = None) \<or> Y = None"
      using inv st OLf_invariant.simps by simp

    have "N \<noteq> {||} \<or> X \<noteq> None \<or> P \<noteq> empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_OLf_state.simps by auto
    moreover {
      assume
        n: "N \<noteq> {||}" and
        x: "X = None"

      obtain N' :: "'f fset" and C :: 'f where
        n': "N = N' |\<union>| {|C|}" and
        c_ni: "C |\<notin>| N'"
        using n finsert_is_funion by blast
      have y: "Y = None"
        using n x inv' by meson

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.choose_n[OF c_ni] unfolding st n' x y by fast
    } moreover {
      assume "X \<noteq> None"
      then obtain C :: 'f where
        x: "X = Some C"
        by blast

      have y: "Y = None"
        using x inv' by auto

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.transfer unfolding st x y by fast
    } moreover {
      assume
        p: "P \<noteq> empty" and
        n: "N = {||}" and
        x: "X = None" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.choose_p[OF p] unfolding st n x y by fast
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

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.infer[OF inf_red] unfolding st n x y by fast
    } ultimately show False
      using no_step by force
  qed
qed


subsection \<open>Refinement\<close>

lemma fair_OL_step_imp_OL_step:
  assumes olf: "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A')"
  shows "fstate (N, X, P, Y, A) \<leadsto>OL fstate (N', X', P', Y', A')"
  using olf
proof cases
  case (choose_n C)
  note defs = this(1-7) and c_ni = this(8)
  show ?thesis
    unfolding defs fstate.simps option.set using OL.choose_n c_ni by (simp add: notin_fset)
next
  case (delete_fwd C)
  note defs = this(1-7) and c_red = this(8)
  show ?thesis
    unfolding defs fstate.simps option.set by (rule OL.delete_fwd[OF c_red])
next
  case (simplify_fwd C' C)
  note defs = this(1-7) and c_red = this(9)
  show ?thesis
    unfolding defs fstate.simps option.set by (rule OL.simplify_fwd[OF c_red])
next
  case (delete_bwd_p C' C)
  note defs = this(1-7) and c'_in_p = this(8) and c'_red = this(9)

  have p_rm_c'_uni_c': "elems (remove C' P) \<union> {C'} = elems P"
    unfolding felems_remove by (auto intro: c'_in_p)
  have p_mns_c': "elems P - {C'} = elems (remove C' P)"
    unfolding felems_remove by auto

  show ?thesis
    unfolding defs fstate.simps option.set
    by (rule OL.delete_bwd_p[OF c'_red, of _ "elems P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (simplify_bwd_p C'' C' C)
  note defs = this(1-7) and c'_in_p = this(9) and c'_red = this(10)

  have p_rm_c'_uni_c': "elems (remove C' P) \<union> {C'} = elems P"
    unfolding felems_remove by (auto intro: c'_in_p)
  have p_mns_c': "elems P - {C'} = elems (remove C' P)"
    unfolding felems_remove by auto

  show ?thesis
    unfolding defs fstate.simps option.set
    using OL.simplify_bwd_p[OF c'_red, of "fset N" "elems P - {C'}",
        unfolded p_rm_c'_uni_c' p_mns_c']
    by simp
next
  case (delete_bwd_a C' C)
  note defs = this(1-7) and c'_red = this(9)
  show ?thesis
    unfolding defs fstate.simps option.set using OL.delete_bwd_a[OF c'_red] by simp
next
  case (simplify_bwd_a C' C'' C)
  note defs = this(1-7) and c'_red = this(10)
  show ?thesis
    unfolding defs fstate.simps option.set using OL.simplify_bwd_a[OF c'_red] by simp
next
  case (transfer C)
  note defs = this(1-7)

  have p_uni_c: "elems P \<union> {C} = elems (add C P)"
    using felems_add by auto

  show ?thesis
    unfolding defs fstate.simps option.set
    by (rule OL.transfer[of _ C "elems P", unfolded p_uni_c])
next
  case choose_p
  note defs = this(1-8) and p_nemp = this(9)

  have sel_ni_rm: "select P \<notin> elems (remove (select P) P)"
    unfolding felems_remove by auto

  have rm_sel_uni_sel: "elems (remove (select P) P) \<union> {select P} = elems P"
    unfolding felems_remove using p_nemp select_in_felems
    by (metis Un_insert_right finsert.rep_eq finsert_fminus sup_bot_right)

  show ?thesis
    unfolding defs fstate.simps option.set
    using OL.choose_p[of "select P" "elems (remove (select P) P)", OF sel_ni_rm,
        unfolded rm_sel_uni_sel]
    by simp
next
  case (infer C)
  note defs = this(1-7) and infers = this(8)
  show ?thesis
    unfolding defs fstate.simps option.set using OL.infer[OF infers] by simp
qed

lemma fair_OL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A') \<Longrightarrow>
   fstate (N, X, P, Y, A) \<leadsto>GC fstate (N', X', P', Y', A')"
  by (rule OL_step_imp_GC_step[OF fair_OL_step_imp_OL_step])

end

end
