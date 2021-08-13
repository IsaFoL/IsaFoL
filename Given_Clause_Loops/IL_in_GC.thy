(* Title:        iProver Loop
 * Author:       Qi Qiu, 2021
 * Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>iProver Loop\<close>

theory IL_in_GC
  imports 
    OL_in_GC
    Saturation_Framework.Given_Clause_Architectures
begin (* Theory begins*)

locale iProver_loop = GC? : Given_Clause_Architectures.given_clause 
  Bot_F Inf_F Bot_G Q entails_q Inf_G_q Red_I_q
  Red_F_q \<G>_F_q \<G>_I_q Inf_FL Equiv_F Prec_F Prec_L active
  for
    Bot_F :: "'f set" and 
    Inf_F :: "'f inference set" and 
    Bot_G :: "'g set" and 
    Q :: "'q set" and 
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and 
    Inf_G_q :: \<open>'q \<Rightarrow> 'g inference set\<close> and 
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and 
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and 
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and 
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and 
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close> and 
    Equiv_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<doteq>" 50) and 
    Prec_F :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) and 
    Prec_L :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "\<sqsubset>L" 50) and
    active :: "'l" +
  fixes new x passive y :: 'l
  assumes
    (* There are exactly 5 labels and there's an order on labels*)
    five_labels : "\<forall>l::'l. l \<in> {new, x, passive, y, active}" and
    order_on_labels : "active \<sqsubset>L y \<and> y \<sqsubset>L passive \<and> passive \<sqsubset>L x \<and> x \<sqsubset>L new" and
    order_on_labels_trans : "l1 \<sqsubset>L l2 \<Longrightarrow> l2 \<sqsubset>L l3 \<Longrightarrow> l1 \<sqsubset>L l3"

begin (* Locale otter_loop *)

  (* is sublocale of otter_loop *)
  (* for reusing proven lemmas *)
  sublocale OL_in_GC.otter_loop
  proof unfold_locales
    show "\<forall>l::'l. l \<in> {new, x, passive, y, active}" 
      using five_labels by auto
  next
    show "active \<sqsubset>L y \<and> y \<sqsubset>L passive \<and> passive \<sqsubset>L x \<and> x \<sqsubset>L new" 
      using order_on_labels by auto
  next 
    fix l1 l2 l3
    show " l1 \<sqsubset>L l2 \<Longrightarrow> l2 \<sqsubset>L l3 \<Longrightarrow> l1 \<sqsubset>L l3" 
      using order_on_labels_trans by auto
  qed
  
subsection \<open>definition, abbreviation, type and fun\<close>
 
  inductive iProver_loop :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>IL" 50) where
  choose_n : "state (N \<union> {C}, \<emptyset>, P, \<emptyset>, A) \<leadsto>IL state (N, {C}, P, \<emptyset>, A) "
  |delete_fwd : "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C'\<in> (P \<union> A). C' \<preceq>\<cdot> C) \<Longrightarrow>
                  state (N, {C}, P, \<emptyset>, A) \<leadsto>IL state (N, \<emptyset>, P, \<emptyset>, A) "
  |simplify_fwd : "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
                    state (N, {C}, P, \<emptyset>, A) \<leadsto>IL state (N, {C'}, P, \<emptyset>, A)"
  |delete_bwd_p : "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
                    state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>IL state(N, {C}, P, \<emptyset>, A)"
  |simplify_bwd_p : "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
                      state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>IL state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  |delete_bwd_a : "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
                    state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>IL state (N, {C}, P, \<emptyset>, A)"
  |simplify_bwd_a : "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow> 
                      state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>IL state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  |transfer : "state (N, {C}, P, \<emptyset>, A) \<leadsto>IL state (N, \<emptyset>, P \<union> {C}, \<emptyset>, A)"
  |choose_p : "state (\<emptyset>, \<emptyset>, P \<union> {C}, \<emptyset>, A) \<leadsto>IL state (\<emptyset>, \<emptyset>, P, {C}, A)"
  |infer : "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
              state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>IL state  (M, \<emptyset>, P, \<emptyset>, A \<union> {C})"
  |replace : "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = { C' } \<and> C' \<prec>\<cdot> C) \<Longrightarrow>
                state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>IL state (M, \<emptyset>, P, \<emptyset>, A)"

  lemma replace_in_GC : 
    assumes "C \<in> no_labels.Red_F (A \<union> M) \<or> (M = { C' } \<and> C' \<prec>\<cdot> C)"
    shows "state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>GC state (M, \<emptyset>, P, \<emptyset>, A)"
  proof-
    let ?\<N> = "state (\<emptyset>, \<emptyset>, P, \<emptyset>, A)"
    and ?\<M> = "{(C,y)}"
    and ?\<M>' = "{(x,new) |x. x\<in>M}"
  
    have "(C,y) \<in> Red_F (?\<N> \<union> ?\<M>')"
      using assms
    proof
      assume c_in : "C \<in> no_labels.Red_F (A \<union> M)"
      have "A \<union> M \<subseteq> A \<union> M \<union> P" by auto
      also have "fst ` (?\<N> \<union> ?\<M>') = A \<union> M \<union> P"
        by auto
      then have "C \<in> no_labels.Red_F (fst ` (?\<N> \<union> ?\<M>'))" 
        by (metis (no_types, lifting) c_in calculation in_mono no_labels.Red_F_of_subset)
      then show "(C,y) \<in> Red_F (?\<N> \<union> ?\<M>')"
        using lemma59point1 by blast
    next
      assume assm : "M = {C'} \<and> C' \<prec>\<cdot> C"
      then have "C' \<in> fst ` (?\<N> \<union> ?\<M>')" 
        by simp
      then show "(C,y) \<in> Red_F (?\<N> \<union> ?\<M>')" 
        by (metis (mono_tags, lifting) assm lemma59point2)
    qed
  
    then have \<M>_included_in : "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')"
      by auto
  
    have "new \<noteq> active"
      by (simp add: labels_distinct) 
    then have prj_of_active_subset_of_\<M>' : "fst ` (active_subset ?\<M>') = \<emptyset>" 
      by (simp add: active_subset_def)
  
    have "?\<N> \<union> ?\<M> \<leadsto>GC ?\<N> \<union> ?\<M>'" 
      using process[of _ "?\<N>" "?\<M>" _ "?\<M>'"] \<M>_included_in prj_of_active_subset_of_\<M>' by auto
    moreover have "?\<N> \<union> ?\<M> = state (\<emptyset>, \<emptyset>, P, {C}, A)" 
      by simp
    moreover have "?\<N> \<union> ?\<M>' = state (M, \<emptyset>, P, \<emptyset>, A)"
      by auto
    ultimately show "state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>GC state (M, \<emptyset>, P, \<emptyset>, A)"
      by simp
  qed

subsection \<open>Inclusion of IL in GC\<close>

  theorem inclusion_ol_in_gc : "M \<leadsto>IL M' \<Longrightarrow> M \<leadsto>GC M'"
  proof (induction rule : iProver_loop.induct)
    case (choose_n N C P A)
    then show ?case using chooseN_in_GC by auto
  next
    case (delete_fwd C P A N)
    then show ?case using deleteFwd_in_GC by auto 
  next
    case (simplify_fwd C P A C' N)
    then show ?case using simplifyFwd_in_GC by auto
  next
    case (delete_bwd_p C' C N P A)
    then show ?case using deleteBwdP_in_GC by auto
  next
    case (simplify_bwd_p C' C C'' N P A)
    then show ?case using simplifyBwdP_in_GC by auto
  next
    case (delete_bwd_a C' C N P A)
    then show ?case using deleteBwdA_in_GC by auto
  next
    case (simplify_bwd_a C' C N P A C'')
    then show ?case using simplifyBwdA_in_GC by blast
  next
    case (transfer N C P A)
    then show ?case using transfer_in_GC by auto
  next
    case (choose_p P C A)
    then show ?case using chooseP_in_GC by auto
  next
    case (infer A C M P)
    then show ?case using infer_in_GC by auto
  next 
    case (replace C A M C' P)
    then show ?case using replace_in_GC by auto
  qed

end (* Locale iProver loop*)

end (* Theory *)