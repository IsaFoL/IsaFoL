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
  choose_p: "P \<noteq> empty \<Longrightarrow> select P = Passive_Formula C \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| delete_fwd: "C \<in> no_labels.Red_F (fset A) \<or> (\<exists>C' \<in> fset A. C' \<preceq>\<cdot> C) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, None, A)"
| simplify_fwd: "C' \<prec>S C \<Longrightarrow> C \<in> no_labels.Red_F (fset A \<union> {C'}) \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (P, Some C', A)"
| delete_bwd: "C' \<in> no_labels.Red_F {C} \<or> C' \<cdot>\<succ> C \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (P, Some C, A)"
| simplify_bwd: "C'' \<prec>S C' \<Longrightarrow> C' \<in> no_labels.Red_F {C, C''} \<Longrightarrow>
    (P, Some C, A |\<union>| {|C'|}) \<leadsto>DLf (add (Passive_Formula C'') P, Some C, A)"
| compute_infer: "P \<noteq> empty \<Longrightarrow> select P = Passive_Inference \<iota> \<Longrightarrow>
    \<iota> \<in> no_labels.Red_I (fset A \<union> {C}) \<Longrightarrow>
    (P, None, A) \<leadsto>DLf (remove (select P) P, Some C, A)"
| schedule_infer: "set \<iota>s = no_labels.Inf_between (fset A) {C} \<Longrightarrow>
    (P, Some C, A) \<leadsto>DLf (fold (add \<circ> Passive_Inference) \<iota>s P, None, A |\<union>| {|C|})"
| delete_orphan_formulas: "set \<iota>s \<inter> no_labels.Inf_from (fset A) = {} \<Longrightarrow>
    (P, Y, A) \<leadsto>DLf (fold (remove \<circ> Passive_Inference) \<iota>s P, Y, A)"

end

end
