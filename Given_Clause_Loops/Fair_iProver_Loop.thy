(* Title:        Fairness of Otter Loop
   Authors:      Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
   Maintainer:   Jasmin Blancherte <j.c.blanchette at vu.nl>, 2022
*)

section \<open>Fairness of Otter Loop\<close>

theory Fair_iProver_Loop
  imports
    Fair_Otter_Loop
    iProver_Loop
begin


subsection \<open>Locale\<close>

locale fair_iprover_loop =
  fair_otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
    empty select add remove fformulas Prec_S
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
    fformulas :: "'p \<Rightarrow> 'f fset" and
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
begin


subsection \<open>Definition and Lemmas\<close>

thm IL.intros[no_vars]

inductive
  fair_IL :: "('p, 'f) fair_OL_state \<Rightarrow> ('p, 'f) fair_OL_state \<Rightarrow> bool" (infix "\<leadsto>ILf" 50)
where
  ol: "St \<leadsto>OLf St' \<Longrightarrow> St \<leadsto>ILf St'"
| red_by_children: "C \<in> no_labels.Red_F_\<G> (fset A \<union> fset M) \<or> fset M = {C'} \<and> C' \<prec>\<cdot> C \<Longrightarrow>
  ({||}, None, P, Some C, A) \<leadsto>ILf (M, None, P, None, A)"


subsection \<open>Invariant\<close>

lemma step_fair_IL_invariant:
  assumes "St \<leadsto>ILf St'"
  shows "fair_OL_invariant St'"
  using assms
proof cases
  case ol
  then show ?thesis
    using step_fair_OL_invariant by auto
next
  case (red_by_children C A M C' P)
  then show ?thesis
    using fair_OL_invariant.intros by presburger
qed

lemma chain_fair_IL_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>ILf) Sts" and
    fair_hd: "fair_OL_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "fair_OL_invariant (lnth Sts i)"
  using i_lt
proof (induct i)
  case 0
  thus ?case
    using fair_hd lhd_conv_lnth zero_enat_def by fastforce
next
  case (Suc i)
  thus ?case
    using chain chain_lnth_rel step_fair_IL_invariant by blast
qed

lemma chain_fair_IL_invariant_llast:
  assumes
    chain: "chain (\<leadsto>ILf) Sts" and
    fair_hd: "fair_OL_invariant (lhd Sts)" and
    fin: "lfinite Sts"
  shows "fair_OL_invariant (llast Sts)"
proof -
  obtain i :: nat where
    i: "llength Sts = enat i"
    using lfinite_llength_enat[OF fin] by blast

  have im1_lt: "enat (i - 1) < llength Sts"
    using i by (metis chain chain_length_pos diff_less enat_ord_simps(2) less_numeral_extra(1)
        zero_enat_def)

  show ?thesis
    using chain_fair_IL_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

lemma is_final_fair_OL_state_iff_no_IL_step:
  assumes inv: "fair_OL_invariant St"
  shows "is_final_fair_OL_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>ILf St')"
proof
  assume final: "is_final_fair_OL_state St"
  then obtain A :: "'f fset" where
    st: "St = ({||}, None, empty, None, A)"
    by (auto simp: is_final_fair_OL_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>ILf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "({||}, None, empty, None, A) \<leadsto>ILf St'"
    thus False
    proof cases
      case ol
      then show False
        using final st is_final_fair_OL_state_iff_no_OL_step[OF inv] by blast
    qed
  qed
next
  assume "\<forall>St'. \<not> St \<leadsto>ILf St'"
  hence "\<forall>St'. \<not> St \<leadsto>OLf St'"
    using fair_IL.ol by blast
  thus "is_final_fair_OL_state St"
    using inv is_final_fair_OL_state_iff_no_OL_step by blast
qed


subsection \<open>Refinement\<close>

lemma fair_IL_step_imp_IL_step:
  assumes ilf: "(N, X, P, Y, A) \<leadsto>ILf (N', X', P', Y', A')"
  shows "fstate (N, X, P, Y, A) \<leadsto>IL fstate (N', X', P', Y', A')"
  using ilf
proof cases
  case ol
  note olf = this(1)
  have ol: "fstate (N, X, P, Y, A) \<leadsto>OL fstate (N', X', P', Y', A')"
    by (rule fair_OL_step_imp_OL_step[OF olf])
  show ?thesis
    by (rule IL.ol[OF ol])
next
  case (red_by_children C C')
  note defs = this(1-7) and c_in = this(8)
  have il: "state ({}, {}, formulas P, {C}, fset A) \<leadsto>IL state (fset N', {}, formulas P, {}, fset A)"
    by (rule IL.red_by_children[OF c_in])
  show ?thesis
    unfolding defs using il by auto
qed

lemma fair_IL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>ILf (N', X', P', Y', A') \<Longrightarrow>
   fstate (N, X, P, Y, A) \<leadsto>GC fstate (N', X', P', Y', A')"
  by (rule IL_step_imp_GC_step[OF fair_IL_step_imp_IL_step])


subsection \<open>Completeness\<close>

lemma fair_IL_Liminf_yy_empty:
  assumes
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) = {}"
  sorry

lemma fair_IL_Liminf_xx_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (set_option \<circ> xx_of) Sts) = {}"
  sorry

lemma fair_IL_Liminf_new_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (fset \<circ> new_of) Sts) = {}"
  sorry

lemma fair_IL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    init: "is_initial_fair_OL_state (lhd Sts)"
  shows "Liminf_llist (lmap (formulas \<circ> passive_of) Sts) = {}"
  sorry

theorem
  assumes
    ilf_full: "full_chain (\<leadsto>ILf) Sts" and
    olf_init: "is_initial_fair_OL_state (lhd Sts)" and
    bot: "B \<in> Bot_F" and
    unsat: "fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"
  shows
    IL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> state_union (Liminf_fstate Sts)" and
    IL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
proof -
  have ilf_chain: "chain (\<leadsto>ILf) Sts"
    by (rule full_chain_imp_chain[OF ilf_full])
  have gc_chain: "chain (\<leadsto>GC) (lmap fstate Sts)"
    using ilf_chain fair_IL_step_imp_GC_step chain_lmap by (smt (verit) fstate.cases)

  have olf_inv: "fair_OL_invariant (lhd Sts)"
    using olf_init unfolding is_initial_fair_OL_state.simps fair_OL_invariant.simps by fast

  have nnul: "\<not> lnull Sts"
    using ilf_chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_fair_OL_state.cases olf_init snd_conv)
  hence act: "active_subset (lhd (lmap fstate Sts)) = {}"
    unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas: "passive_subset (Liminf_llist (lmap fstate Sts)) = {}"
  proof (cases "lfinite Sts")
    case fin: True

    have lim: "Liminf_llist (lmap fstate Sts) = fstate (llast Sts)"
      using lfinite_Liminf_llist fin nnul
      by (metis chain_not_lnull gc_chain lfinite_lmap llast_lmap)

    have last_inv: "fair_OL_invariant (llast Sts)"
      by (rule chain_fair_IL_invariant_llast[OF ilf_chain olf_inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>ILf St'"
      using full_chain_lnth_not_rel[OF ilf_full] by (metis fin full_chain_iff_chain ilf_full)
    hence "is_final_fair_OL_state (llast Sts)"
      unfolding is_final_fair_OL_state_iff_no_IL_step[OF last_inv] .
    then obtain A :: "'f fset" where
      at_l: "llast Sts = ({||}, None, empty, None, A)"
      unfolding is_final_fair_OL_state.simps by blast
    show ?thesis
      unfolding is_final_fair_OL_state.simps passive_subset_def lim at_l fstate.simps state.simps
      by (auto simp: fformulas_empty)
  next
    case False
    hence len: "llength Sts = \<infinity>"
      by (simp add: not_lfinite_llength)
    show ?thesis
      unfolding Liminf_fstate_commute passive_subset_def Liminf_fstate_def
      using fair_IL_Liminf_new_empty[OF len ilf_full olf_inv]
        fair_IL_Liminf_xx_empty[OF len ilf_full olf_inv]
        fair_IL_Liminf_passive_empty[OF len ilf_full olf_init]
        fair_IL_Liminf_yy_empty[OF ilf_full olf_inv]
      by simp
  qed

  have unsat': "fst ` lhd (lmap fstate Sts) \<Turnstile>\<inter>\<G> {B}"
    using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

  have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap fstate Sts)"
    by (rule gc_complete_Liminf[OF gc_chain act pas bot unsat'])
  thus "\<exists>B \<in> Bot_F. B \<in> state_union (Liminf_fstate Sts)"
    unfolding Liminf_fstate_def Liminf_fstate_commute by auto
  thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
    unfolding Liminf_fstate_def Liminf_llist_def by auto
qed

end


subsection \<open>Specialization with FIFO Queue\<close>

print_locale fair_otter_loop

locale fifo_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F
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

sublocale fair_otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F
  Prec_F "[]" hd "\<lambda>y xs. xs @ [y]" removeAll fset_of_list Prec_S
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
