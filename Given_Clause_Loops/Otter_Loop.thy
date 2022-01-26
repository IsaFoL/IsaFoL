(* Title:        Otter Loop
 * Author:       Qi Qiu, 2021
 * Maintainer:   Sophie Tourret <stourret at loria.fr>, 2021 *)

section \<open>Otter Loop\<close>

theory Otter_Loop
  imports 
    More_Given_Clause
    Saturation_Framework.Given_Clause_Architectures
begin (* Theory begins*)

locale otter_loop = GC? : Given_Clause_Architectures.given_clause 
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

subsection \<open>definition, abbreviation, type and fun\<close>
  
  fun state :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> ('f \<times> 'l) set" where
  " state (N, X, P, Y, A) = {(C, new)|C. C \<in> N} \<union> 
                           {(C, x)|C. C \<in> X} \<union>
                           {(C, passive)|C. C \<in> P} \<union>
                           {(C, y) |C. C \<in> Y} \<union>
                           {(C, active)|C. C \<in> A} "

  inductive OL :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<leadsto>OL" 50) where
  choose_n : "C \<notin> N \<Longrightarrow> state (N \<union> {C}, \<emptyset>, P, \<emptyset>, A) \<leadsto>OL state (N, {C}, P, \<emptyset>, A) "
  |delete_fwd : "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C'\<in> (P \<union> A). C' \<preceq>\<cdot> C) \<Longrightarrow>
                  state (N, {C}, P, \<emptyset>, A) \<leadsto>OL state (N, \<emptyset>, P, \<emptyset>, A) "
  |simplify_fwd : "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
                    state (N, {C}, P, \<emptyset>, A) \<leadsto>OL state (N, {C'}, P, \<emptyset>, A)"
  |delete_bwd_p : "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
                    state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>OL state(N, {C}, P, \<emptyset>, A)"
  |simplify_bwd_p : "C' \<in> no_labels.Red_F ({C, C''}) \<Longrightarrow>
                      state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>OL state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  |delete_bwd_a : "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'  \<Longrightarrow>
                    state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>OL state (N, {C}, P, \<emptyset>, A)"
  |simplify_bwd_a : "C' \<in> no_labels.Red_F ({C, C'' }) \<Longrightarrow> 
                      state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>OL state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  |transfer : "state (N, {C}, P, \<emptyset>, A) \<leadsto>OL state (N, \<emptyset>, P \<union> {C}, \<emptyset>, A)"
  |choose_p : "C \<notin> P \<Longrightarrow> state (\<emptyset>, \<emptyset>, P \<union> {C}, \<emptyset>, A) \<leadsto>OL state (\<emptyset>, \<emptyset>, P, {C}, A)"
  |infer : "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
              state (\<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>OL state  (M, \<emptyset>, P, \<emptyset>, A \<union> {C})"

  subsubsection \<open> Auxiliary Lemmas \<close>

  lemma labels_distinct : 
    assumes "l \<in> { x, y, passive, new }" 
    shows "l \<noteq> active"
  proof
    assume l_active : "l = active"
    then have "active \<sqsubset>L l" 
      by (metis assms empty_iff insert_iff order_on_labels order_on_labels_trans)
    then have "l \<sqsubset>L active" 
      using l_active by auto
    then show "False"
      by (metis UNIV_I l_active minimal_element.minimal wf_prec_L)
  qed 
 
  lemma prj_state_union_sets [simp]: "fst ` (state (N, X, P, Y, A)) = N \<union> X \<union> P \<union> Y \<union> A"
    using prj_fl_set_to_f_set_distr_union prj_labeledN_eq_N by auto

  lemma active_subset_of_setOfFormulasWithLabelDiffActive : 
    "l \<noteq> active \<Longrightarrow> active_subset {(C',l)} = \<emptyset>"
    using active_subset_def labels_distinct by auto

  lemma state_add_C_new : "state (N, X, P, Y, A) \<union> {(C, new)} = state (N \<union> {C}, X, P, Y, A)" 
    by auto

  lemma state_add_C_x : "state (N, X, P, Y, A) \<union> {(C, x)} = state (N, X \<union> {C}, P, Y, A)" 
    by auto

  lemma state_add_C_passive : 
    "state (N, X, P, Y, A) \<union> {(C, passive)} = state (N, X, P \<union> {C}, Y, A)" 
    by auto

  lemma state_add_C_y : "state (N, X, P, Y, A) \<union> {(C, y)} = state (N, X, P, Y \<union> {C}, A)" 
    by auto

  lemma state_add_C_active : "state (N, X, P, Y, A) \<union> {(C, active)} = state (N, X, P, Y, A \<union> {C})" 
    by auto

  lemma prj_activeSubset_of_state : "fst ` (active_subset (state ( N, X, P, Y, A))) = A"
  proof-
    have "active_subset {(C,new)|C. C \<in> N} = \<emptyset>" 
      using labels_distinct active_subset_def by auto
    moreover have "active_subset {(C, y)|C. C \<in> Y} = \<emptyset>"   
      using labels_distinct active_subset_def by auto
    moreover have "active_subset {(C, passive)|C. C \<in> P} = \<emptyset>"
      using labels_distinct active_subset_def by auto
    moreover have "active_subset {(C, x)|C. C \<in> X} = \<emptyset>" 
      using labels_distinct active_subset_def by auto
    moreover have "active_subset {(C, active)|C. C \<in> A} = {(C, active)|C. C \<in> A}"
      using active_subset_def by auto
    ultimately have "fst ` (active_subset (state (N,X,P,Y,A))) = fst ` { (C, active) | C. C \<in> A}"
      by auto 
    then show ?thesis 
      by simp
  qed

  subsection \<open> main lemmas \<close>

  lemma chooseN_in_GC : "state (N \<union> {C}, \<emptyset>, P, \<emptyset>, A) \<leadsto>GC state (N, {C}, P, \<emptyset>, A)"
  proof-
    have x_ls_new : "x \<sqsubset>L new" 
      using order_on_labels by auto
    moreover have x_neq_active : "x \<noteq> active" 
      using labels_distinct by simp
    ultimately have almost_thesis : "state (N, \<emptyset>, P, \<emptyset>, A) \<union> {(C, new)} \<leadsto>GC state (N, \<emptyset>, P, \<emptyset>, A) \<union> {(C, x)}" 
      using P5 by auto
    have rewrite_left : "state (N, \<emptyset>, P, \<emptyset>, A) \<union> {(C, new)} = state (N \<union> {C}, \<emptyset>, P, \<emptyset>, A)" 
      using state_add_C_new by blast
    moreover have rewrite_right : "state (N, \<emptyset>, P, \<emptyset>, A) \<union> {(C, x)} =  state (N, {C}, P, \<emptyset>, A)" 
      using state_add_C_x by auto
    ultimately show ?thesis 
      using almost_thesis rewrite_left rewrite_right by simp
  qed

  lemma deleteFwd_in_GC : 
    assumes "C \<in> no_labels.Red_F (P \<union> A) \<or> (\<exists>C'\<in> (P \<union> A). C' \<preceq>\<cdot> C)"
    shows "state (N, {C}, P, \<emptyset>, A) \<leadsto>GC state (N, \<emptyset>, P, \<emptyset>, A)"
    using assms
  proof
    assume c_in_redf_PA : "C \<in> no_labels.Red_F (P \<union> A)"
    have "P \<union> A \<subseteq> N \<union> \<emptyset> \<union> P \<union> \<emptyset> \<union> A" by auto
    then have "no_labels.Red_F (P \<union> A) \<subseteq> no_labels.Red_F (N \<union> \<emptyset> \<union> P \<union> \<emptyset> \<union> A)" 
      using no_labels.Red_F_of_subset by simp
    then have c_in_redf_NPA : "C \<in> no_labels.Red_F (N \<union> \<emptyset> \<union> P \<union> \<emptyset> \<union> A)"
      using c_in_redf_PA by auto
    have NPA_eq_prj_state_NPA : "N \<union> \<emptyset> \<union> P \<union> \<emptyset> \<union> A = fst` ( state (N, \<emptyset>, P, \<emptyset>, A) )" 
      using prj_state_union_sets by simp
    have "C \<in> no_labels.Red_F ( fst` ( state (N, \<emptyset>, P, \<emptyset>, A) ))"
      using c_in_redf_NPA NPA_eq_prj_state_NPA by fastforce
    then show ?thesis
      using P1 by auto
  next
    assume "\<exists>C'\<in>P \<union> A. C' \<preceq>\<cdot> C"
    then obtain C' where "C' \<in> P \<union> A" and c'_le_c : "C' \<preceq>\<cdot> C" 
      by auto
    then have "C' \<in> P \<or> C' \<in> A" 
      by blast
    then show ?thesis
    proof
      assume "C' \<in> P" 
      then have c'_passive_in : "(C',passive) \<in> state (N, \<emptyset>, P, \<emptyset>, A)" 
        by simp
      have "passive \<sqsubset>L x"
        using order_on_labels by simp
      then have "(state (N, \<emptyset>, P, \<emptyset>, A)) \<union> {(C,x)} \<leadsto>GC ( state (N, \<emptyset>, P, \<emptyset>, A) )" 
        using P4 c'_le_c c'_passive_in by blast
      then show ?thesis 
        by auto
    next
      assume "C' \<in> A" 
      then have c'_active_in_state_NPA : "(C',active) \<in> ( state (N, \<emptyset>, P, \<emptyset>, A) )" 
        by simp
      also have active_ls_x : "active \<sqsubset>L x"
        using active_minimal labels_distinct by simp
      then  have " state (N, \<emptyset>, P, \<emptyset>, A) \<union> {(C,x)} \<leadsto>GC state (N, \<emptyset>, P, \<emptyset>, A) " 
        using P4 c'_le_c active_ls_x c'_active_in_state_NPA by blast
      then show ?thesis
        by auto
    qed
  qed


  lemma simplifyFwd_in_GC : 
    "C \<in> no_labels.Red_F (P \<union> A \<union> {C'}) \<Longrightarrow>
     state (N, {C}, P, \<emptyset>, A) \<leadsto>GC state (N, {C'}, P, \<emptyset>, A)"
  proof-
    assume c_in : "C \<in> no_labels.Red_F (P \<union> A \<union> {C'})"    
    let ?\<N> = "state (N, \<emptyset>, P, \<emptyset>, A)"
    and ?\<M> = "{(C,x)}" and ?\<M>' = "{(C',x)}"
    
    have "P \<union> A \<union> {C'} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
      by auto
    then have "no_labels.Red_F (P \<union> A \<union> {C'}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
      using no_labels.Red_F_of_subset by auto
    then have "C \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
      using c_in by auto 
    then have c_x_in : "(C, x) \<in> Red_F (?\<N> \<union> ?\<M>')"
      using lemma59point1 by auto
    then have "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')" by auto
    also have "x \<noteq> active "
      using labels_distinct by auto
    then have active_subset_of_m' : "active_subset ?\<M>' = \<emptyset>" 
      using active_subset_of_setOfFormulasWithLabelDiffActive by auto
    show ?thesis
      using c_x_in active_subset_of_m' process[of _ _ "?\<M>" _ "?\<M>'"] by auto
  qed

  lemma deleteBwdP_in_GC :
    assumes "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C'"
    shows  "state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>GC state(N, {C}, P, \<emptyset>, A)"
    using assms
    proof
      let ?\<N> = "state (N, {C}, P, \<emptyset>, A)"
      assume c_ls_c' : " C \<prec>\<cdot> C' "

      have "(C, x) \<in> state (N, {C}, P, \<emptyset>, A)"
        by simp
      then have "?\<N> \<union> {(C', passive)} \<leadsto>GC ?\<N>" 
        using c_ls_c' P3 by blast
      also have "?\<N> \<union> {(C', passive)} = state (N, {C}, P \<union> {C'}, \<emptyset>, A)"
        by auto
      finally show ?thesis 
        by auto
    next
      let ?\<N> = "state (N, {C}, P, \<emptyset>, A)"
      assume c'_in_redf_c : " C' \<in> no_labels.Red_F_\<G> {C} "
      have " {C} \<subseteq> fst` ?\<N>" by auto
      then have " no_labels.Red_F {C} \<subseteq> no_labels.Red_F (fst` ?\<N>) " 
        using no_labels.Red_F_of_subset by auto
      then have " C' \<in> no_labels.Red_F (fst` ?\<N>) "
        using c'_in_redf_c by blast
      then have "?\<N> \<union> {(C',passive)} \<leadsto>GC ?\<N>"
        using P1 by blast
      then show ?thesis
        by (metis state_add_C_passive)
    qed

  lemma simplifyBwdP_in_GC :
    assumes "C' \<in> no_labels.Red_F ({C, C''})"
    shows "state (N, {C}, P \<union> {C'}, \<emptyset>, A) \<leadsto>GC state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  proof-
    let ?\<N> = "state (N, {C}, P, \<emptyset>, A)"
    and ?\<M> = "{(C',passive)}" 
    and ?\<M>' = "{(C'',new)}"
    
    have "{C,C''} \<subseteq> fst` (?\<N> \<union> ?\<M>')"
      by (smt (z3) Un_commute Un_empty_left Un_insert_right insert_absorb2
          subset_Un_eq state_add_C_new prj_state_union_sets)
    then have "no_labels.Red_F ({C, C''}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
      using no_labels.Red_F_of_subset by auto
    then have "C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>'))"
      using assms by auto
    then have "(C', passive) \<in> Red_F (?\<N> \<union> ?\<M>')"
      using lemma59point1 by auto
    then have \<M>_in_redf : "?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>')" by auto
    
    have "new \<noteq> active " 
      by (simp add: labels_distinct)
    then have active_subset_\<M>' : "active_subset ?\<M>' = \<emptyset>" 
      using active_subset_of_setOfFormulasWithLabelDiffActive by auto
   
    have "?\<N> \<union> ?\<M> \<leadsto>GC ?\<N> \<union> ?\<M>'" 
      using \<M>_in_redf active_subset_\<M>' process[of _ _ "?\<M>" _ "?\<M>'"] by auto
    also have "?\<N> \<union> {(C', passive)} = state (N, {C}, P \<union> {C'}, \<emptyset>, A)" 
      by force
    also have "?\<N> \<union> {(C'', new)} = state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
      using state_add_C_new by blast
    finally show ?thesis
      by auto  
  qed

  lemma deleteBwdA_in_GC :
    assumes "C' \<in> no_labels.Red_F ({C}) \<or> C \<prec>\<cdot> C' "
    shows "state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>GC state (N, {C}, P, \<emptyset>, A) "
    using assms
  proof
      let ?\<N> = "state (N, {C}, P, \<emptyset>, A)"
      assume c_ls_c' : " C \<prec>\<cdot> C' "

      have " (C, x) \<in> state (N, {C}, P, \<emptyset>, A) " 
        by simp
      then have "?\<N> \<union> {(C', active)} \<leadsto>GC ?\<N>" 
        using c_ls_c' P3 by blast
      also have "?\<N> \<union> {(C', active)} = state (N, {C}, P, \<emptyset>, A \<union> {C'})"
        by auto
      finally show "state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>GC state(N, {C}, P, \<emptyset>, A)" 
        by auto
  next
      let ?\<N> = "state (N, {C}, P, \<emptyset>, A)"
      assume c'_in_redf_c : " C' \<in> no_labels.Red_F_\<G> {C} "

      have " {C} \<subseteq> fst` ?\<N> "
        by (metis Un_commute Un_upper2 le_supI2 prj_state_union_sets)
      then have " no_labels.Red_F {C} \<subseteq> no_labels.Red_F (fst` ?\<N>) " 
        using no_labels.Red_F_of_subset by auto
      then have " C' \<in> no_labels.Red_F (fst` ?\<N>) "
        using c'_in_redf_c by blast
      then have "?\<N> \<union> {(C',active)} \<leadsto>GC ?\<N>" 
        using P1 by auto  
      then show ?thesis 
        by (metis state_add_C_active)
  qed

  lemma simplifyBwdA_in_GC : 
    assumes "C' \<in> no_labels.Red_F ({C, C''})"
    shows "state (N, {C}, P, \<emptyset>, A \<union> {C'}) \<leadsto>GC state (N \<union> {C''}, {C}, P, \<emptyset>, A)"
  proof-
    let ?\<N> = "state (N, {C}, P, \<emptyset>, A)" and ?\<M> = "{(C',active)}" and ?\<M>' = "{(C'',new)}"
    
    have " {C,C''} \<subseteq> fst` (?\<N> \<union> ?\<M>') "
      by simp
    then have " no_labels.Red_F ({C, C''}) \<subseteq> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
      using no_labels.Red_F_of_subset by auto
    then have " C' \<in> no_labels.Red_F (fst` (?\<N> \<union> ?\<M>')) "
      using assms by auto 
    then have " (C', active) \<in> Red_F (?\<N> \<union> ?\<M>') "
      using lemma59point1 by auto
    then have \<M>_included : " ?\<M> \<subseteq> Red_F (?\<N> \<union> ?\<M>') " 
      by auto
    
    have "new \<noteq> active" 
      by (simp add: labels_distinct)  
    then have "active_subset ?\<M>' = \<emptyset>" 
      using active_subset_of_setOfFormulasWithLabelDiffActive by auto  
    then have "state (N, {C}, P, \<emptyset>, A) \<union> {(C', active)} \<leadsto>GC state (N, {C}, P, \<emptyset>, A) \<union> {(C'', new)}" 
      using \<M>_included process[where ?M="?\<M>" and ?M'="?\<M>'"] by auto
   
    then show ?thesis
      by (metis state_add_C_new state_add_C_active)
  qed


  lemma transfer_in_GC : "state (N, {C}, P, \<emptyset>, A) \<leadsto>GC state  (N, \<emptyset>, P \<union> {C}, \<emptyset>, A)"
  proof-
    let ?\<N> = "state (N, \<emptyset>, P, \<emptyset>, A)"

    have "passive \<sqsubset>L x"
      by (simp add: order_on_labels)    
    moreover have "passive \<noteq> active"
      by (simp add: labels_distinct)
    ultimately have "?\<N> \<union> {(C, x)} \<leadsto>GC ?\<N> \<union> {(C, passive)}"
      using P5 by auto

    then show ?thesis 
      by (metis sup_bot_left state_add_C_x state_add_C_passive)
  qed

  lemma chooseP_in_GC : "state ( \<emptyset>, \<emptyset>, P \<union> {C}, \<emptyset>, A) \<leadsto>GC state  ( \<emptyset>, \<emptyset>, P, {C}, A)"
  proof-
    let ?\<N> = "state (\<emptyset>, \<emptyset>, P, \<emptyset>, A)"
    
    have "y \<sqsubset>L passive"
      by (simp add: order_on_labels)    
    moreover have "y \<noteq> active"
      by (simp add: labels_distinct)
    ultimately have "?\<N> \<union> {(C, passive)} \<leadsto>GC ?\<N> \<union> {(C, y)}"
      using P5 by auto 
    
    then show ?thesis
      by (metis sup_bot_left state_add_C_passive state_add_C_y)
  qed

  lemma infer_in_GC : 
    assumes "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M)"
    shows "state ( \<emptyset>, \<emptyset>, P, {C}, A) \<leadsto>GC state  ( M, \<emptyset>, P, \<emptyset>, A \<union> {C})"
  proof-
    let ?\<M> = "{(C', new)|C'. C' \<in> M}"
    let ?\<N> = "state ( \<emptyset>, \<emptyset>, P, \<emptyset>, A)" 
  
    have active_subset_of_\<M> : "active_subset ?\<M> = \<emptyset>"
      using labels_distinct active_subset_def by auto
  
    have "A \<union> {C} \<union> M \<subseteq> (fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>)"
      by fastforce
    then have "no_labels.Red_I (A \<union> {C} \<union> M) \<subseteq> no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
      using no_labels.empty_ord.Red_I_of_subset by auto
    moreover have "fst` (active_subset ?\<N>) = A" 
      using prj_activeSubset_of_state by blast    
    ultimately have "no_labels.Inf_between (fst` (active_subset ?\<N>)) {C} \<subseteq> 
                      no_labels.Red_I ((fst` ?\<N>) \<union> {C} \<union> (fst` ?\<M>))"
      using assms by auto
  
    then have "?\<N> \<union> {(C,y)} \<leadsto>GC ?\<N> \<union> {(C,active)} \<union> ?\<M>" 
      using labels_distinct active_subset_of_\<M> prj_fl_set_to_f_set_distr_union step.infer by force
    also have "?\<N> \<union> {(C,y)} =  state ( \<emptyset>, \<emptyset>, P, {C}, A)"
      by simp
    also have "?\<N> \<union> {(C,active)} \<union> ?\<M> = state  ( M, \<emptyset>, P, \<emptyset>, A \<union> {C})"
      by force
    finally show ?thesis 
      by simp
  qed

  subsection \<open>Theorem\<close>

  theorem inclusion_ol_in_gc : "M \<leadsto>OL M' \<Longrightarrow> M \<leadsto>GC M'"
  proof (induction rule : OL.induct)
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
  qed

definition choose_n_fun :: "'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow>
  ('f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set)" where
  \<open>choose_n_fun N X P Y A = (SOME s. s\<in>{(N', {C}, P, {}, A) | C N'. N = N' \<union> {C} \<and> X = {} \<and> Y = {}})\<close>

inductive choose_n_fun2 :: "'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow>
  ('f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set) \<Rightarrow> bool" where
\<open>choose_n_fun2 N {} P {} A (N-{C}, {C}, P, {}, A)\<close>
if \<open>C \<in> N\<close>

end (* Locale otter_loop*)

end (* Theory *)