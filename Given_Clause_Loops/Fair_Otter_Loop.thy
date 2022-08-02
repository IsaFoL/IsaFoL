theory Fair_Otter_Loop
  imports Otter_Loop Fair_Loop_Basis
begin

type_synonym ('p, 'f) fair_OL_state = "'f set \<times> 'f option \<times> 'p \<times> 'f option \<times> 'f set"

locale fair_otter_loop =
  otter_loop Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q Red_F_q \<G>_F_q \<G>_I_q Equiv_F Prec_F +
  fair_passive_set empty select add remove fformulas
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
    fformulas :: "'p \<Rightarrow> 'f fset" +
  fixes
    Prec_S :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>S" 50)
  assumes
    wf_prec_S: "minimal_element (\<prec>S) UNIV"
begin


subsection \<open>Definition and Lemmas\<close>

abbreviation new_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'f set" where
  "new_of St \<equiv> fst St"
abbreviation xx_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'f option" where
  "xx_of St \<equiv> fst (snd St)"
abbreviation passive_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'p" where
  "passive_of St \<equiv> fst (snd (snd St))"
abbreviation yy_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'f option" where
  "yy_of St \<equiv> fst (snd (snd (snd St)))"
abbreviation active_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'f set" where
  "active_of St \<equiv> snd (snd (snd (snd St)))"
abbreviation all_of :: "('p, 'f) fair_OL_state \<Rightarrow> 'f set" where
  "all_of St \<equiv> new_of St \<union> set_option (xx_of St) \<union> formulas (passive_of St) \<union>
     set_option (yy_of St) \<union> active_of St"

fun statef :: "'f set \<times> 'f option \<times> 'p \<times> 'f option \<times> 'f set \<Rightarrow> ('f \<times> OL_label) set" where
  "statef (N, X, P, Y, A) = state (N, set_option X, formulas P, set_option Y, A)"

lemma statef_alt_def:
  "statef St =
   state (fst St, set_option (fst (snd St)), formulas (fst (snd (snd St))),
     set_option (fst (snd (snd (snd St)))), snd (snd (snd (snd St))))"
  by (cases St) auto

definition
  Liminf_statef :: "('p, 'f) fair_OL_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_statef Sts =
   (Liminf_llist (lmap new_of Sts),
    Liminf_llist (lmap (set_option \<circ> xx_of) Sts),
    Liminf_llist (lmap (formulas \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap active_of Sts))"

lemma Liminf_statef_commute: "Liminf_llist (lmap statef Sts) = state (Liminf_statef Sts)"
proof -
  have "Liminf_llist (lmap statef Sts) =
    (\<lambda>C. (C, New)) ` Liminf_llist (lmap new_of Sts) \<union>
    (\<lambda>C. (C, XX)) ` Liminf_llist (lmap (set_option \<circ> xx_of) Sts) \<union>
    (\<lambda>C. (C, Passive)) ` Liminf_llist (lmap (formulas \<circ> passive_of) Sts) \<union>
    (\<lambda>C. (C, YY)) ` Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<union>
    (\<lambda>C. (C, Active)) ` Liminf_llist (lmap active_of Sts)"
    unfolding statef_alt_def state_alt_def
    apply (subst Liminf_llist_lmap_union, fast)+
    apply (subst Liminf_llist_lmap_image, simp add: inj_on_convol_ident)+
    by auto
 then show ?thesis
   unfolding Liminf_statef_def by fastforce
qed

fun statef_union :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f set" where
  "statef_union (N, X, P, Y, A) = N \<union> X \<union> P \<union> Y \<union> A"

inductive
  fair_OL :: "('p, 'f) fair_OL_state \<Rightarrow> ('p, 'f) fair_OL_state \<Rightarrow> bool" (infix "\<leadsto>OLf" 50)
where
  choose_n: "C \<notin> N \<Longrightarrow> (N \<union> {C}, None, P, None, A) \<leadsto>OLf (N, Some C, P, None, A)"
| delete_fwd: "C \<in> no_labels.Red_F (formulas P \<union> A) \<or> (\<exists>C' \<in> formulas P \<union> A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, None, P, None, A)"
| simplify_fwd: "C' \<prec>S S \<Longrightarrow> C \<in> no_labels.Red_F (formulas P \<union> A \<union> {C'}) \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, Some C', P, None, A)"
| delete_bwd_p: "C' \<in> formulas P \<Longrightarrow> C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N, Some C, remove C' P, None, A)"
| simplify_bwd_p: "C' \<prec>S S \<Longrightarrow> C' \<in> formulas P \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, Some C, P, None, A) \<leadsto>OLf (N \<union> {C''}, Some C, remove C' P, None, A)"
| delete_bwd_a: "C' \<in> no_labels.Red_F {C} \<or> C \<prec>\<cdot> C' \<Longrightarrow>
    (N, Some C, P, None, A \<union> {C'}) \<leadsto>OLf (N, Some C, P, None, A)"
| simplify_bwd_a: "C' \<prec>S S \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (N, Some C, P, None, A \<union> {C'}) \<leadsto>OLf (N \<union> {C''}, Some C, P, None, A)"
| transfer: "(N, Some C, P, None, A) \<leadsto>OLf (N, None, add C P, None, A)"
| choose_p: "fformulas P \<noteq> {||} \<Longrightarrow>
    ({}, None, P, None, A) \<leadsto>OLf ({}, None, remove (select P) P, Some (select P), A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    ({}, None, P, Some C, A) \<leadsto>OLf (M, None, P, None, A \<union> {C})"


subsection \<open>Refinement\<close>

lemma fair_OL_step_imp_OL_step:
  assumes olf: "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A')"
  shows "statef (N, X, P, Y, A) \<leadsto>OL statef (N', X', P', Y', A')"
  using olf
proof cases
  case (choose_n C)
  note unfolds = this(1-7) and c_ni = this(8)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.choose_n[OF c_ni])
next
  case (delete_fwd C)
  note unfolds = this(1-7) and c_red = this(8)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.delete_fwd[OF c_red])
next
  case (simplify_fwd C' S C)
  note unfolds = this(1-7) and c_red = this(9)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.simplify_fwd[OF c_red])
next
  case (delete_bwd_p C' C)
  note unfolds = this(1-7) and c'_in_p = this(8) and c'_red = this(9)

  have p_rm_c'_uni_c': "formulas (remove C' P) \<union> {C'} = formulas P"
    unfolding fformulas_remove by (auto intro: c'_in_p)
  have p_mns_c': "formulas P - {C'} = formulas (remove C' P)"
    unfolding fformulas_remove by auto

  show ?thesis
    unfolding unfolds statef.simps option.set
    by (rule OL.delete_bwd_p[OF c'_red, of _ "formulas P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (simplify_bwd_p C' S C C'')
  note unfolds = this(1-7) and c'_in_p = this(9) and c'_red = this(10)

  have p_rm_c'_uni_c': "formulas (remove C' P) \<union> {C'} = formulas P"
    unfolding fformulas_remove by (auto intro: c'_in_p)
  have p_mns_c': "formulas P - {C'} = formulas (remove C' P)"
    unfolding fformulas_remove by auto

  show ?thesis
    unfolding unfolds statef.simps option.set
    by (rule OL.simplify_bwd_p[OF c'_red, of _ "formulas P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (delete_bwd_a C' C)
  note unfolds = this(1-7) and c'_red = this(8)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.delete_bwd_a[OF c'_red])
next
  case (simplify_bwd_a C' S C C'')
  note unfolds = this(1-7) and c'_red = this(9)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.simplify_bwd_a[OF c'_red])
next
  case (transfer C)
  note unfolds = this(1-7)

  have p_uni_c: "formulas P \<union> {C} = formulas (add C P)"
    unfolding fformulas_add by auto

  show ?thesis
    unfolding unfolds statef.simps option.set
    by (rule OL.transfer[of _ C "formulas P", unfolded p_uni_c])
next
  case choose_p
  note unfolds = this(1-8) and p_nemp = this(9)

  have sel_ni_rm: "select P \<notin> formulas (remove (select P) P)"
    unfolding fformulas_remove by auto

  have rm_sel_uni_sel: "formulas (remove (select P) P) \<union> {select P} = formulas P"
    unfolding fformulas_remove using p_nemp select_in_fformulas
    by (metis Un_insert_right finsert.rep_eq finsert_fminus sup_bot_right)

  show ?thesis
    unfolding unfolds statef.simps option.set
    by (rule OL.choose_p[of "select P" "formulas (remove (select P) P)", OF sel_ni_rm,
          unfolded rm_sel_uni_sel])
next
  case (infer C)
  note unfolds = this(1-7) and infers = this(8)
  show ?thesis
    unfolding unfolds statef.simps option.set by (rule OL.infer[OF infers])
qed

lemma fair_OL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A') \<Longrightarrow>
   statef (N, X, P, Y, A) \<leadsto>GC statef (N', X', P', Y', A')"
  by (rule OL_step_imp_GC_step[OF fair_OL_step_imp_OL_step])


subsection \<open>Completeness\<close>

lemma no_labels_entails_mono_left: "M \<subseteq> N \<Longrightarrow> M \<Turnstile>\<inter>\<G> P \<Longrightarrow> N \<Turnstile>\<inter>\<G> P"
  using no_labels.entails_trans no_labels.subset_entailed by blast

lemma fair_OL_Liminf_new_empty:
  assumes "full_chain (\<leadsto>OLf) Sts"
  shows "Liminf_llist (lmap new_of Sts) = {}"
  sorry

lemma fair_OL_Liminf_xx_empty:
  assumes "full_chain (\<leadsto>OLf) Sts"
  shows "Liminf_llist (lmap (set_option \<circ> xx_of) Sts) = {}"
proof (rule ccontr)
  assume lim_nemp: "Liminf_llist (lmap (set_option \<circ> xx_of) Sts) \<noteq> {}"

  obtain i :: nat where
    i_lt: "enat i < llength Sts" and
    inter_nemp: "\<Inter> ((set_option \<circ> xx_of \<circ> lnth Sts) ` {j. i \<le> j \<and> enat j < llength Sts}) \<noteq> {}"
    using lim_nemp unfolding Liminf_llist_def by auto

  from inter_nemp obtain C :: 'f where
    c_in: "\<forall>P \<in> lnth Sts ` {j. i \<le> j \<and> enat j < llength Sts}. C \<in> set_option (xx_of P)"
    by auto
  hence c_in': "\<forall>j \<ge> i. enat j < llength Sts \<longrightarrow> C \<in> set_option (xx_of (lnth Sts j))"
    by auto

  have "lnth Sts i \<leadsto>OLf (new_of (lnth Sts i), xx_of (lnth Sts i), passive_of (lnth Sts i),
    yy_of (lnth Sts i), active_of (lnth Sts i))"
    sorry
  show False
    sorry
qed

lemma fair_OL_Liminf_passive_empty:
  assumes "full_chain (\<leadsto>OLf) Sts"
  shows "Liminf_llist (lmap (formulas \<circ> passive_of) Sts) = {}"
  sorry

lemma fair_OL_Liminf_yy_empty:
  assumes "full_chain (\<leadsto>OLf) Sts"
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

  have "\<exists>M. lnth Sts i \<leadsto>OLf (new_of (lnth Sts i), xx_of (lnth Sts i), passive_of (lnth Sts i),
    None, active_of (lnth Sts i) \<union> set_option (yy_of (lnth Sts i)) \<union> M)"
    sorry
  show False
    sorry
qed

theorem
  assumes
    olf_full: "full_chain (\<leadsto>OLf) Sts" and
    xx: "xx_of (lhd Sts) = None" and
    yy: "yy_of (lhd Sts) = None" and
    act: "active_of (lhd Sts) = {}" and
    bot: "B \<in> Bot_F" and
    unsat: "new_of (lhd Sts) \<Turnstile>\<inter>\<G> {B}"
  shows
    OL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> statef_union (Liminf_statef Sts)" and
    OL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
proof -
  have olf_chain: "chain (\<leadsto>OLf) Sts"
    by (rule full_chain_imp_chain[OF olf_full])
  have gc_chain: "chain (\<leadsto>GC) (lmap statef Sts)"
    using olf_chain fair_OL_step_imp_GC_step chain_lmap by (smt (verit) statef.cases)

  have "\<not> lnull Sts"
    using olf_chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))
  have act': "active_subset (lhd (lmap statef Sts)) = {}"
    using act unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas': "passive_subset (Liminf_llist (lmap statef Sts)) = {}"
    unfolding Liminf_statef_commute passive_subset_def Liminf_statef_def
    using fair_OL_Liminf_new_empty[OF olf_full] fair_OL_Liminf_xx_empty[OF olf_full]
      fair_OL_Liminf_passive_empty[OF olf_full] fair_OL_Liminf_yy_empty[OF olf_full]
    by simp

  have unsat': "fst ` lhd (lmap statef Sts) \<Turnstile>\<inter>\<G> {B}"
    using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

  have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap statef Sts)"
    by (rule gc_complete_Liminf[OF gc_chain act' pas' bot unsat'])
  then show "\<exists>B \<in> Bot_F. B \<in> statef_union (Liminf_statef Sts)"
    unfolding Liminf_statef_def Liminf_statef_commute by auto
  then show "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
    unfolding Liminf_statef_def Liminf_llist_def by auto
qed

end

end
