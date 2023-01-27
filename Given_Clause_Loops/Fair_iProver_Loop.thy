(* Title:        Fair iProver Loop
   Authors:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2022-2023
   Maintainer:   Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Fair iProver Loop\<close>

text \<open>The fair iProver loop assumes that the passive queue is fair and ensures
(dynamic) refutational completeness under that assumption. From this
completeness proof, we also easily derive (in a separate section) the
completeness of the Otter loop.\<close>

theory Fair_iProver_Loop
  imports
    Given_Clause_Loops_Util
    Fair_Otter_Loop_Def
    iProver_Loop
begin


subsection \<open>Locale\<close>

context fair_otter_loop
begin


subsection \<open>Basic Definition\<close>

inductive fair_IL :: "('p, 'f) OLf_state \<Rightarrow> ('p, 'f) OLf_state \<Rightarrow> bool" (infix "\<leadsto>ILf" 50) where
  ol: "St \<leadsto>OLf St' \<Longrightarrow> St \<leadsto>ILf St'"
| red_by_children: "C \<in> no_labels.Red_F (fset A \<union> fset M) \<or> fset M = {C'} \<and> C' \<prec>\<cdot> C \<Longrightarrow>
  ({||}, None, P, Some C, A) \<leadsto>ILf (M, None, P, None, A)"


subsection \<open>Initial State and Invariant\<close>

lemma step_ILf_invariant:
  assumes "St \<leadsto>ILf St'"
  shows "OLf_invariant St'"
  using assms
proof cases
  case ol
  then show ?thesis
    using step_OLf_invariant by auto
next
  case (red_by_children C A M C' P)
  then show ?thesis
    using OLf_invariant.intros by presburger
qed

lemma chain_ILf_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>ILf) Sts" and
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
    using chain chain_lnth_rel step_ILf_invariant by blast
qed

lemma chain_ILf_invariant_llast:
  assumes
    chain: "chain (\<leadsto>ILf) Sts" and
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
    using chain_ILf_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

lemma is_final_OLf_state_iff_no_ILf_step:
  assumes inv: "OLf_invariant St"
  shows "is_final_OLf_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>ILf St')"
proof
  assume final: "is_final_OLf_state St"
  then obtain A :: "'f fset" where
    st: "St = ({||}, None, empty, None, A)"
    by (auto simp: is_final_OLf_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>ILf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "({||}, None, empty, None, A) \<leadsto>ILf St'"
    thus False
    proof cases
      case ol
      then show False
        using final st is_final_OLf_state_iff_no_OLf_step[OF inv] by blast
    qed
  qed
next
  assume "\<forall>St'. \<not> St \<leadsto>ILf St'"
  hence "\<forall>St'. \<not> St \<leadsto>OLf St'"
    using fair_IL.ol by blast
  thus "is_final_OLf_state St"
    using inv is_final_OLf_state_iff_no_OLf_step by blast
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
  have il: "state ({}, {}, elems P, {C}, fset A) \<leadsto>IL state (fset N', {}, elems P, {}, fset A)"
    by (rule IL.red_by_children[OF c_in])
  show ?thesis
    unfolding defs using il by auto
qed

lemma fair_IL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>ILf (N', X', P', Y', A') \<Longrightarrow>
   fstate (N, X, P, Y, A) \<leadsto>GC fstate (N', X', P', Y', A')"
  by (rule IL_step_imp_GC_step[OF fair_IL_step_imp_IL_step])


subsection \<open>Completeness\<close>

fun mset_of_fstate :: "('p, 'f) OLf_state \<Rightarrow> 'f multiset" where
  "mset_of_fstate (N, X, P, Y, A) =
   mset_set (fset N) + mset_set (set_option X) + mset_set (elems P) + mset_set (set_option Y) +
   mset_set (fset A)"

abbreviation Precprec_S :: "'f multiset \<Rightarrow> 'f multiset \<Rightarrow> bool" (infix "\<prec>\<prec>S" 50) where
  "(\<prec>\<prec>S) \<equiv> multp (\<prec>S)"

lemma wfP_Precprec_S: "wfP (\<prec>\<prec>S)"
  using minimal_element_def wfP_multp wf_Prec_S wfp_on_UNIV by blast

definition Less1_state :: "('p, 'f) OLf_state \<Rightarrow> ('p, 'f) OLf_state \<Rightarrow> bool" (infix "\<sqsubset>1" 50) where
  "St' \<sqsubset>1 St \<longleftrightarrow>
   mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St
   \<or> (mset_of_fstate St' = mset_of_fstate St
      \<and> (mset_set (fset (new_of St')) \<prec>\<prec>S mset_set (fset (new_of St))
         \<or> (mset_set (fset (new_of St')) = mset_set (fset (new_of St))
            \<and> mset_set (set_option (xx_of St')) \<prec>\<prec>S mset_set (set_option (xx_of St)))))"

lemma wfP_Less1_state: "wfP (\<sqsubset>1)"
proof -
  let ?msetset = "{(M', M). M' \<prec>\<prec>S M}"
  let ?triple_of =
    "\<lambda>St. (mset_of_fstate St, mset_set (fset (new_of St)), mset_set (set_option (xx_of St)))"

  have wf_msetset: "wf ?msetset"
    using wfP_Precprec_S wfP_def by auto
  have wf_lex_prod: "wf (?msetset <*lex*> ?msetset <*lex*> ?msetset)"
    by (rule wf_lex_prod[OF wf_msetset wf_lex_prod[OF wf_msetset wf_msetset]])

  have Less1_state_alt_def: "\<And>St' St. St' \<sqsubset>1 St \<longleftrightarrow>
    (?triple_of St', ?triple_of St) \<in> ?msetset <*lex*> ?msetset <*lex*> ?msetset"
    unfolding Less1_state_def by simp

  show ?thesis
    unfolding wfP_def Less1_state_alt_def using wf_app[of _ ?triple_of] wf_lex_prod by blast
qed

definition Less2_state :: "('p, 'f) OLf_state \<Rightarrow> ('p, 'f) OLf_state \<Rightarrow> bool" (infix "\<sqsubset>2" 50) where
  "St' \<sqsubset>2 St \<equiv>
   mset_set (set_option (yy_of St')) \<prec>\<prec>S mset_set (set_option (yy_of St))
   \<or> (mset_set (set_option (yy_of St')) = mset_set (set_option (yy_of St))
      \<and> St' \<sqsubset>1 St)"

lemma wfP_Less2_state: "wfP (\<sqsubset>2)"
proof -
  let ?msetset = "{(M', M). M' \<prec>\<prec>S M}"
  let ?stateset = "{(St', St). St' \<sqsubset>1 St}"
  let ?pair_of = "\<lambda>St. (mset_set (set_option (yy_of St)), St)"

  have wf_msetset: "wf ?msetset"
    using wfP_Precprec_S wfP_def by auto
  have wf_stateset: "wf ?stateset"
    using wfP_Less1_state wfP_def by auto
  have wf_lex_prod: "wf (?msetset <*lex*> ?stateset)"
    by (rule wf_lex_prod[OF wf_msetset wf_stateset])

  have Less2_state_alt_def:
    "\<And>St' St. St' \<sqsubset>2 St \<longleftrightarrow> (?pair_of St', ?pair_of St) \<in> ?msetset <*lex*> ?stateset"
    unfolding Less2_state_def by simp

  show ?thesis
    unfolding wfP_def Less2_state_alt_def using wf_app[of _ ?pair_of] wf_lex_prod by blast
qed

lemma fair_IL_Liminf_yy_empty:
  assumes
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "OLf_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) = {}"
proof (rule ccontr)
  assume lim_nemp: "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<noteq> {}"

  have chain: "chain (\<leadsto>ILf) Sts"
    by (rule full_chain_imp_chain[OF full])

  obtain i :: nat where
    i_lt: "enat i < llength Sts" and
    inter_nemp: "\<Inter> ((set_option \<circ> yy_of \<circ> lnth Sts) ` {j. i \<le> j \<and> enat j < llength Sts}) \<noteq> {}"
    using lim_nemp unfolding Liminf_llist_def by auto

  have inv_at_i: "OLf_invariant (lnth Sts i)"
    by (simp add: chain chain_ILf_invariant_lnth i_lt inv)

  from inter_nemp obtain C :: 'f where
    c_in: "\<forall>P \<in> lnth Sts ` {j. i \<le> j \<and> enat j < llength Sts}. C \<in> set_option (yy_of P)"
    by auto
  hence c_in': "\<forall>j \<ge> i. enat j < llength Sts \<longrightarrow> C \<in> set_option (yy_of (lnth Sts j))"
    by auto

  have yy_at_i: "yy_of (lnth Sts i) = Some C"
    using c_in' i_lt by blast
  have new_at_i: "new_of (lnth Sts i) = {||}" and
    xx_at_i: "new_of (lnth Sts i) = {||}"
    using yy_at_i chain_ILf_invariant_lnth[OF chain inv i_lt]
    by (force simp: OLf_invariant.simps)+

  have "\<exists>St'. lnth Sts i \<leadsto>ILf St'"
    using is_final_OLf_state_iff_no_ILf_step[OF inv_at_i]
    by (metis fst_conv is_final_OLf_state.cases option.simps(3) snd_conv yy_at_i)
  hence si_lt: "enat (Suc i) < llength Sts"
    by (metis Suc_ile_eq full full_chain_lnth_not_rel i_lt order_le_imp_less_or_eq)

  obtain P :: 'p and A :: "'f fset" where
    at_i: "lnth Sts i = ({||}, None, P, Some C, A)"
    using OLf_invariant.simps inv_at_i yy_at_i by auto

  have "lnth Sts i \<leadsto>ILf lnth Sts (Suc i)"
    by (simp add: chain chain_lnth_rel si_lt)
  hence "({||}, None, P, Some C, A) \<leadsto>ILf lnth Sts (Suc i)"
    unfolding at_i .
  hence "yy_of (lnth Sts (Suc i)) = None"
  proof cases
    case ol
    then show ?thesis
      by cases simp
  next
    case (red_by_children M C')
    then show ?thesis
      by simp
  qed
  thus False
    using c_in' si_lt by simp
qed

lemma xx_nonempty_OLf_step_imp_Precprec_S:
  assumes
    step: "St \<leadsto>OLf St'" and
    xx: "xx_of St \<noteq> None" and
    xx': "xx_of St' \<noteq> None"
  shows "mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St"
  using step
proof cases
  case (simplify_fwd C' C P A N)
  note defs = this(1,2) and prec = this(3)

  have aft: "add_mset C' (mset_set (fset N) + mset_set (elems P) + mset_set (fset A)) =
    mset_set (fset N) + mset_set (elems P) + mset_set (fset A) + {#C'#}"
    (is "?old_aft = ?new_aft")
    by auto
  have bef: "add_mset C (mset_set (fset N) + mset_set (elems P) + mset_set (fset A)) =
    mset_set (fset N) + mset_set (elems P) + mset_set (fset A) + {#C#}"
    (is "?old_bef = ?new_bef")
    by auto

  have "?new_aft \<prec>\<prec>S ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "{#C'#} \<prec>\<prec>S {#C#}"
      by (simp add: multp_def prec singletons_in_mult)
  qed
  hence "?old_aft \<prec>\<prec>S ?old_bef"
    unfolding bef aft .
  thus ?thesis
    unfolding defs by auto
next
  case (delete_bwd_p C' P C N A)
  note defs = this(1,2) and c'_in = this(3)
  have "mset_set (elems P - {C'}) \<subset># mset_set (elems P)"
    by (metis Diff_iff c'_in finite_fset finite_set_mset_mset_set elems_remove insertCI
        insert_Diff subset_imp_msubset_mset_set subset_insertI subset_mset.less_le)
  thus ?thesis
    unfolding defs using c'_in
    by (auto simp: elems_remove intro!: subset_implies_multp)
next
  case (simplify_bwd_p C'' C' P C N A)
  note defs = this(1,2) and prec = this(3) and c'_in = this(4)

  let ?old_aft = "add_mset C (mset_set (insert C'' (fset N)) + mset_set (elems (remove C' P)) +
    mset_set (fset A))"
  let ?old_bef = "add_mset C (mset_set (fset N) + mset_set (elems P) + mset_set (fset A))"

  have "?old_aft \<prec>\<prec>S ?old_bef"
  proof (cases "C'' \<in> fset N")
    case c''_in: True

    have "mset_set (elems P - {C'}) \<subset># mset_set (elems P)"
      by (metis c'_in finite_fset mset_set.remove multi_psub_of_add_self)
    thus ?thesis
      unfolding defs
      by (auto simp: elems_remove insert_absorb[OF c''_in] intro!: subset_implies_multp)
  next
    case c''_ni: False

    have aft: "?old_aft = add_mset C (mset_set (fset N) + mset_set (elems (remove C' P)) +
      mset_set (fset A)) + {#C''#}"
      (is "_ = ?new_aft")
      using c''_ni by auto
    have bef: "?old_bef = add_mset C (mset_set (fset N) + mset_set (elems (remove C' P)) +
      mset_set (fset A)) + {#C'#}"
      (is "_ = ?new_bef")
      using c'_in by (auto simp: elems_remove mset_set.remove)

    have "?new_aft \<prec>\<prec>S ?new_bef"
      unfolding multp_def
    proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
      show "{#C''#} \<prec>\<prec>S {#C'#}"
        unfolding multp_def using prec by (auto intro: singletons_in_mult)
    qed
    thus ?thesis
      unfolding bef aft .
  qed
  thus ?thesis
    unfolding defs by (auto simp: notin_fset)
next
  case (delete_bwd_a C' A C N P)
  note defs = this(1,2) and c'_ni = this(3)
  show ?thesis
    unfolding defs using c'_ni by (auto simp: notin_fset intro!: subset_implies_multp)
next
  case (simplify_bwd_a C'' C' A C N P)
  note defs = this(1,2) and prec = this(3) and c'_ni = this(4)

  have aft:
    "add_mset C (mset_set (insert C'' (fset N)) + mset_set (elems P) + mset_set (fset A)) =
     {#C#} + mset_set (elems P) + mset_set (fset A) + mset_set (insert C'' (fset N))"
    (is "?old_aft = ?new_aft")
    by auto
  have bef:
    "add_mset C' (add_mset C (mset_set (fset N) + mset_set (elems P) + mset_set (fset A))) =
     {#C#} + mset_set (elems P) + mset_set (fset A) + ({#C'#} + mset_set (fset N))"
    (is "?old_bef = ?new_bef")
    by auto

  have "?new_aft \<prec>\<prec>S ?new_bef"
    unfolding multp_def
  proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
    show "mset_set (insert C'' (fset N)) \<prec>\<prec>S {#C'#} + mset_set (fset N)"
    proof (cases "C'' \<in> fset N")
      case True
      hence ins: "insert C'' (fset N) = fset N"
        by blast
      show ?thesis
        unfolding ins by (auto intro!: subset_implies_multp)
    next
      case c''_ni: False

      have aft: "mset_set (insert C'' (fset N)) = mset_set (fset N) + {#C''#}"
        using c''_ni by auto
      have bef: "{#C'#} + mset_set (fset N) = mset_set (fset N) + {#C'#}"
        by auto

      show ?thesis
        unfolding aft bef multp_def
      proof (subst mult_cancelL[OF trans_Prec_S irrefl_Prec_S], fold multp_def)
        show "{#C''#} \<prec>\<prec>S {#C'#}"
          unfolding multp_def using prec by (auto intro: singletons_in_mult)
      qed
    qed
  qed
  hence "?old_aft \<prec>\<prec>S ?old_bef"
    unfolding bef aft .
  thus ?thesis
    unfolding defs using c'_ni by (auto simp: notin_fset)
qed (use xx xx' in auto)

lemma xx_nonempty_ILf_step_imp_Precprec_S:
  assumes
    step: "St \<leadsto>ILf St'" and
    xx: "xx_of St \<noteq> None" and
    xx': "xx_of St' \<noteq> None"
  shows "mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St"
  using step
proof cases
  case ol
  then show ?thesis
    using xx_nonempty_OLf_step_imp_Precprec_S[OF _ xx xx'] by blast
next
  case (red_by_children C A M C' P)
  note defs = this(1,2)
  have False
    using xx unfolding defs by simp
  thus ?thesis
    by blast
qed

lemma fair_IL_Liminf_xx_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "OLf_invariant (lhd Sts)"
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

  have si_lt: "enat (Suc i) < llength Sts"
    unfolding len by auto

  have xx_j: "xx_of (lnth Sts j) \<noteq> None" if j_ge: "j \<ge> i" for j
    using c_in' len j_ge by auto
  hence xx_sj: "xx_of (lnth Sts (Suc j)) \<noteq> None" if j_ge: "j \<ge> i" for j
    using le_Suc_eq that by presburger
  have step: "lnth Sts j \<leadsto>ILf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
    using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
    by blast

  have "mset_of_fstate (lnth Sts (Suc j)) \<prec>\<prec>S mset_of_fstate (lnth Sts j)" if j_ge: "j \<ge> i" for j
    using xx_nonempty_ILf_step_imp_Precprec_S by (meson step j_ge xx_j xx_sj)
  hence "(\<prec>\<prec>S)\<inverse>\<inverse> (mset_of_fstate (lnth Sts j)) (mset_of_fstate (lnth Sts (Suc j)))"
    if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain (\<prec>\<prec>S)\<inverse>\<inverse> (ldropn i (lmap mset_of_fstate Sts))"
    using chain_ldropn_lmapI[OF _ si_lt] by blast

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using len by (simp add: llength_eq_infty_conv_lfinite)

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<prec>\<prec>S)"] wfP_Precprec_S
    by (metis lfinite_ldropn lfinite_lmap)
qed

lemma xx_nonempty_OLf_step_imp_Less1_state:
  assumes step: "(N, Some C, P, Y, A) \<leadsto>OLf (N', Some C', P', Y', A')" (is "?bef \<leadsto>OLf ?aft")
  shows "?aft \<sqsubset>1 ?bef"
proof -
  have "mset_of_fstate ?aft \<prec>\<prec>S mset_of_fstate ?bef"
    using xx_nonempty_OLf_step_imp_Precprec_S
    by (metis fst_conv local.step option.distinct(1) snd_conv)
  thus ?thesis
    unfolding Less1_state_def by blast
qed

lemma yy_empty_OLf_step_imp_Less1_state:
  assumes
    step: "St \<leadsto>OLf St'" and
    yy: "yy_of St = None" and
    yy': "yy_of St' = None"
  shows "St' \<sqsubset>1 St"
  using step
proof cases
  case (choose_n C N P A)
  note defs = this(1,2) and c_ni = this(3)

  have mset_eq: "mset_of_fstate St' = mset_of_fstate St"
    unfolding defs using c_ni by (fastforce simp: fmember.rep_eq)
  have new_lt: "mset_set (fset (new_of St')) \<prec>\<prec>S mset_set (fset (new_of St))"
    unfolding defs using c_ni[unfolded fmember.rep_eq]
    by (auto intro!: subset_implies_multp)

  show ?thesis
    unfolding Less1_state_def using mset_eq new_lt by blast
next
  case (delete_fwd C P A N)
  note defs = this(1,2)
  have "mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St"
    unfolding defs by (auto intro: subset_implies_multp)
  thus ?thesis
    unfolding Less1_state_def by blast
next
  case (simplify_fwd C' C P A N)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule xx_nonempty_OLf_step_imp_Less1_state[OF step[unfolded defs]])
next
  case (delete_bwd_p C' P C N A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule xx_nonempty_OLf_step_imp_Less1_state[OF step[unfolded defs]])
next
  case (simplify_bwd_p C'' C' P C N A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule xx_nonempty_OLf_step_imp_Less1_state[OF step[unfolded defs]])
next
  case (delete_bwd_a C' A C N P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule xx_nonempty_OLf_step_imp_Less1_state[OF step[unfolded defs]])
next
  case (simplify_bwd_a C'' C' A C N P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule xx_nonempty_OLf_step_imp_Less1_state[OF step[unfolded defs]])
next
  case (transfer N C P A)
  note defs = this(1,2)
  show ?thesis
  proof (cases "C \<in> elems P")
    case c_in: True
    have "mset_of_fstate St' \<prec>\<prec>S mset_of_fstate St"
      unfolding defs using c_in add_again
      by (auto simp: fmember.rep_eq intro!: subset_implies_multp)
    thus ?thesis
      unfolding Less1_state_def by blast
  next
    case c_ni: False

    have mset_eq: "mset_of_fstate St' = mset_of_fstate St"
      unfolding defs using c_ni by (auto simp: elems_add)
    have new_mset_eq: "mset_set (fset (new_of St')) = mset_set (fset (new_of St))"
      unfolding defs using c_ni by auto
    have xx_lt: "mset_set (set_option (xx_of St')) \<prec>\<prec>S mset_set (set_option (xx_of St))"
      unfolding defs using c_ni[unfolded fmember.rep_eq] by (auto intro!: subset_implies_multp)

    show ?thesis
      unfolding Less1_state_def using mset_eq new_mset_eq xx_lt by blast
  qed
qed (use yy yy' in auto)

lemma yy_empty_ILf_step_imp_Less1_state:
  assumes
    step: "St \<leadsto>ILf St'" and
    yy: "yy_of St = None" and
    yy': "yy_of St' = None"
  shows "St' \<sqsubset>1 St"
  using step
proof cases
  case ol
  then show ?thesis
    using yy_empty_OLf_step_imp_Less1_state[OF _ yy yy'] by blast
next
  case (red_by_children C A M C' P)
  note defs = this(1,2)
  have False
    using yy unfolding defs by simp
  then show ?thesis
    by blast
qed

lemma fair_IL_Liminf_new_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    inv: "OLf_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (fset \<circ> new_of) Sts) = {}"
proof (rule ccontr)
  assume lim_nemp: "Liminf_llist (lmap (fset \<circ> new_of) Sts) \<noteq> {}"

  obtain i :: nat where
    i_lt: "enat i < llength Sts" and
    inter_nemp: "\<Inter> ((fset \<circ> new_of \<circ> lnth Sts) ` {j. i \<le> j \<and> enat j < llength Sts}) \<noteq> {}"
    using lim_nemp unfolding Liminf_llist_def by auto

  from inter_nemp obtain C :: 'f where
    c_in: "\<forall>P \<in> lnth Sts ` {j. i \<le> j \<and> enat j < llength Sts}. C \<in> fset (new_of P)"
    by auto
  hence c_in': "\<forall>j \<ge> i. enat j < llength Sts \<longrightarrow> C \<in> fset (new_of (lnth Sts j))"
    by auto

  have si_lt: "enat (Suc i) < llength Sts"
    by (simp add: len)

  have new_j: "new_of (lnth Sts j) \<noteq> {||}" if j_ge: "j \<ge> i" for j
    using c_in' len that by fastforce

  have yy: "yy_of (lnth Sts j) = None" if j_ge: "j \<ge> i" for j
    by (smt (z3) chain_ILf_invariant_lnth enat_ord_code(4) OLf_invariant.cases fst_conv full
        full_chain_imp_chain inv len new_j snd_conv j_ge)
  hence yy': "yy_of (lnth Sts (Suc j)) = None" if j_ge: "j \<ge> i" for j
    using j_ge by auto
  have step: "lnth Sts j \<leadsto>ILf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
    using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
    by blast

  have "lnth Sts (Suc j) \<sqsubset>1 lnth Sts j" if j_ge: "j \<ge> i" for j
    by (rule yy_empty_ILf_step_imp_Less1_state[OF step[OF j_ge] yy[OF j_ge] yy'[OF j_ge]])
  hence "(\<sqsubset>1)\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain (\<sqsubset>1)\<inverse>\<inverse> (ldropn i Sts)"
    using chain_ldropn_lmapI[OF _ si_lt, of _ id, simplified llist.map_id] by simp

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using len lfinite_ldropn llength_eq_infty_conv_lfinite by blast

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<sqsubset>1)"] wfP_Less1_state
    by blast
qed

lemma yy_empty_OLf_step_imp_Less2_state:
  assumes step: "(N, X, P, None, A) \<leadsto>OLf (N', X', P', None, A')" (is "?bef \<leadsto>OLf ?aft")
  shows "?aft \<sqsubset>2 ?bef"
proof -
  have "?aft \<sqsubset>1 ?bef"
    using yy_empty_OLf_step_imp_Less1_state by (simp add: step)
  thus ?thesis
    unfolding Less2_state_def by force
qed

lemma non_choose_p_OLf_step_imp_Less2_state:
  assumes
    step: "St \<leadsto>OLf St'" and
    yy: "yy_of St' = None"
  shows "St' \<sqsubset>2 St"
  using step
proof cases
  case (choose_n C N P A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (delete_fwd C P A N)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (simplify_fwd C' C P A N)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (delete_bwd_p C' P C N A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (simplify_bwd_p C'' C' P C N A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (delete_bwd_a C' A C N P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (simplify_bwd_a C'' C' A C N P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (transfer N C P A)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (rule yy_empty_OLf_step_imp_Less2_state[OF step[unfolded defs]])
next
  case (choose_p P A)
  note defs = this(1,2)
  have False
    using step yy unfolding defs by simp
  thus ?thesis
    by blast
next
  case (infer A C M P)
  note defs = this(1,2)
  have "mset_set (set_option (yy_of St')) \<prec>\<prec>S mset_set (set_option (yy_of St))"
    unfolding defs by (auto intro!: subset_implies_multp)
  thus ?thesis
    unfolding Less2_state_def by blast
qed

lemma non_choose_p_ILf_step_imp_Less2_state:
  assumes
    step: "St \<leadsto>ILf St'" and
    yy: "yy_of St' = None"
  shows "St' \<sqsubset>2 St"
  using step
proof cases
  case ol
  then show ?thesis
    using non_choose_p_OLf_step_imp_Less2_state[OF _ yy] by blast
next
  case (red_by_children C A M C' P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs Less2_state_def by (simp add: subset_implies_multp)
qed

lemma OLf_step_imp_queue_step:
  assumes "St \<leadsto>OLf St'"
  shows "queue_step (passive_of St) (passive_of St')"
  using assms by cases (auto intro: queue_step_idleI queue_step_addI queue_step_removeI)

lemma ILf_step_imp_queue_step:
  assumes step: "St \<leadsto>ILf St'"
  shows "queue_step (passive_of St) (passive_of St')"
  using step
proof cases
  case ol
  then show ?thesis
    using OLf_step_imp_queue_step by blast
next
  case (red_by_children C A M C' P)
  note defs = this(1,2)
  show ?thesis
    unfolding defs by (auto intro: queue_step_idleI)
qed

lemma fair_IL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>ILf) Sts" and
    init: "is_initial_OLf_state (lhd Sts)"
  shows "Liminf_llist (lmap (elems \<circ> passive_of) Sts) = {}"
proof -
  have chain_step: "chain queue_step (lmap passive_of Sts)"
    using ILf_step_imp_queue_step chain_lmap full_chain_imp_chain[OF full]
    by (metis (no_types, lifting))

  have inf_oft: "infinitely_often select_queue_step (lmap passive_of Sts)"
  proof
    assume "finitely_often select_queue_step (lmap passive_of Sts)"
    then obtain i :: nat where
      no_sel:
        "\<forall>j \<ge> i. \<not> select_queue_step (passive_of (lnth Sts j)) (passive_of (lnth Sts (Suc j)))"
      by (metis (no_types, lifting) enat_ord_code(4) finitely_often_def len llength_lmap lnth_lmap)

    have si_lt: "enat (Suc i) < llength Sts"
      unfolding len by auto

    have step: "lnth Sts j \<leadsto>ILf lnth Sts (Suc j)" if j_ge: "j \<ge> i" for j
      using full_chain_imp_chain[OF full] infinite_chain_lnth_rel len llength_eq_infty_conv_lfinite
      by blast

    have yy: "yy_of (lnth Sts (Suc j)) = None" if j_ge: "j \<ge> i" for j
      using step[OF j_ge]
    proof cases
      case ol
      then show ?thesis
      proof cases
        case (choose_p P A)
        note defs = this(1,2) and p_ne = this(3)
        have False
          using no_sel defs p_ne select_queue_stepI that by fastforce
        thus ?thesis
          by blast
      qed auto
    next
      case (red_by_children C A M C' P)
      then show ?thesis
        by simp
    qed

    have "lnth Sts (Suc j) \<sqsubset>2 lnth Sts j" if j_ge: "j \<ge> i" for j
      by (rule non_choose_p_ILf_step_imp_Less2_state[OF step[OF j_ge] yy[OF j_ge]])
    hence "(\<sqsubset>2)\<inverse>\<inverse> (lnth Sts j) (lnth Sts (Suc j))" if j_ge: "j \<ge> i" for j
      using j_ge by blast
    hence inf_down_chain: "chain (\<sqsubset>2)\<inverse>\<inverse> (ldropn i Sts)"
      using chain_ldropn_lmapI[OF _ si_lt, of _ id, simplified llist.map_id] by simp

    have inf_i: "\<not> lfinite (ldropn i Sts)"
      using len lfinite_ldropn llength_eq_infty_conv_lfinite by blast

    show False
      using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "(\<sqsubset>2)"] wfP_Less2_state
      by blast
  qed

  have hd_emp: "lhd (lmap passive_of Sts) = empty"
    using init full full_chain_not_lnull unfolding is_initial_OLf_state.simps by fastforce

  thm fair

  have "Liminf_llist (lmap elems (lmap passive_of Sts)) = {}"
    by (rule fair[of "lmap passive_of Sts", OF chain_step inf_oft hd_emp])
  thus ?thesis
    by (simp add: llist.map_comp)
qed

theorem
  assumes
    full: "full_chain (\<leadsto>ILf) Sts" and
    init: "is_initial_OLf_state (lhd Sts)"
  shows
    fair_IL_Liminf_saturated: "saturated (state (Liminf_fstate Sts))" and
    fair_IL_complete_Liminf: "B \<in> Bot_F \<Longrightarrow> fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>B' \<in> Bot_F. B' \<in> state_union (Liminf_fstate Sts)" and
    fair_IL_complete: "B \<in> Bot_F \<Longrightarrow> fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B} \<Longrightarrow>
      \<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
proof -
  have chain: "chain (\<leadsto>ILf) Sts"
    by (rule full_chain_imp_chain[OF full])
  have il_chain: "chain (\<leadsto>IL) (lmap fstate Sts)"
    by (rule chain_lmap[OF _ chain]) (use fair_IL_step_imp_IL_step in force)

  have inv: "OLf_invariant (lhd Sts)"
    using init initial_OLf_invariant by blast

  have nnul: "\<not> lnull Sts"
    using chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))

  have "active_of (lhd Sts) = {||}"
    by (metis is_initial_OLf_state.cases init snd_conv)
  hence act: "active_subset (lhd (lmap fstate Sts)) = {}"
    unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas: "passive_subset (Liminf_llist (lmap fstate Sts)) = {}"
  proof (cases "lfinite Sts")
    case fin: True

    have lim: "Liminf_llist (lmap fstate Sts) = fstate (llast Sts)"
      using lfinite_Liminf_llist fin nnul
      by (metis chain_not_lnull il_chain lfinite_lmap llast_lmap)

    have last_inv: "OLf_invariant (llast Sts)"
      by (rule chain_ILf_invariant_llast[OF chain inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>ILf St'"
      using full_chain_lnth_not_rel[OF full] by (metis fin full_chain_iff_chain full)
    hence "is_final_OLf_state (llast Sts)"
      unfolding is_final_OLf_state_iff_no_ILf_step[OF last_inv] .
    then obtain A :: "'f fset" where
      at_l: "llast Sts = ({||}, None, empty, None, A)"
      unfolding is_final_OLf_state.simps by blast
    show ?thesis
      unfolding is_final_OLf_state.simps passive_subset_def lim at_l by auto
  next
    case False
    hence len: "llength Sts = \<infinity>"
      by (simp add: not_lfinite_llength)
    show ?thesis
      unfolding Liminf_fstate_commute passive_subset_def Liminf_fstate_def
      using fair_IL_Liminf_new_empty[OF len full inv]
        fair_IL_Liminf_xx_empty[OF len full inv]
        fair_IL_Liminf_passive_empty[OF len full init]
        fair_IL_Liminf_yy_empty[OF full inv]
      by simp
  qed

  show "saturated (state (Liminf_fstate Sts))"
    using IL_Liminf_saturated act Liminf_fstate_commute il_chain pas by fastforce

  {
    assume
      bot: "B \<in> Bot_F" and
      unsat: "fset (new_of (lhd Sts)) \<Turnstile>\<inter>\<G> {B}"

    have unsat': "fst ` lhd (lmap fstate Sts) \<Turnstile>\<inter>\<G> {B}"
      using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

    have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap fstate Sts)"
      using IL_complete_Liminf[OF il_chain act pas bot unsat'] .
    thus "\<exists>B' \<in> Bot_F. B' \<in> state_union (Liminf_fstate Sts)"
      unfolding Liminf_fstate_def Liminf_fstate_commute by auto
    thus "\<exists>i. enat i < llength Sts \<and> (\<exists>B' \<in> Bot_F. B' \<in> all_formulas_of (lnth Sts i))"
      unfolding Liminf_fstate_def Liminf_llist_def by auto
  }
qed

end

end
