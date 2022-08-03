theory Fair_Otter_Loop
  imports Otter_Loop Fair_Loop_Basis
begin

subsection \<open>Utilities\<close>

lemma chain_ldropnI:
  assumes
    rel: "\<forall>j. j \<ge> i \<longrightarrow> enat (Suc j) < llength xs \<longrightarrow> R (lnth xs j) (lnth xs (Suc j))" and
    si_lt: "enat (Suc i) < llength xs"
  shows "chain R (ldropn i xs)"
proof (rule lnth_rel_chain)
  show "\<not> lnull (ldropn i xs)"
    using si_lt by (simp add: Suc_ile_eq less_le_not_le)
next
  show "\<forall>j. enat (j + 1) < llength (ldropn i xs) \<longrightarrow>
    R (lnth (ldropn i xs) j) (lnth (ldropn i xs) (j + 1))"
    using rel by (smt (z3) One_nat_def Suc_ile_eq add.commute add.right_neutral add_Suc_right
        add_le_cancel_right ldropn_eq_LNil ldropn_ldropn less_le_not_le linorder_not_less
        lnth_ldropn not_less_zero)
qed

lemma chain_ldropn_lmapI:
  assumes
    rel: "\<forall>j. j \<ge> i \<longrightarrow> enat (Suc j) < llength xs \<longrightarrow> R (f (lnth xs j)) (f (lnth xs (Suc j)))" and
    si_lt: "enat (Suc i) < llength xs"
  shows "chain R (ldropn i (lmap f xs))"
proof -
  have "chain R (lmap f (ldropn i xs))"
    using chain_lmap[of "\<lambda>x y. R (f x) (f y)" R f, of "ldropn i xs"] chain_ldropnI[OF rel si_lt]
    by auto
  thus ?thesis
    by auto
qed


subsection \<open>Locale\<close>

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

fun fstate :: "'f set \<times> 'f option \<times> 'p \<times> 'f option \<times> 'f set \<Rightarrow> ('f \<times> OL_label) set" where
  "fstate (N, X, P, Y, A) = state (N, set_option X, formulas P, set_option Y, A)"

lemma fstate_alt_def:
  "fstate St =
   state (fst St, set_option (fst (snd St)), formulas (fst (snd (snd St))),
     set_option (fst (snd (snd (snd St)))), snd (snd (snd (snd St))))"
  by (cases St) auto

definition
  Liminf_fstate :: "('p, 'f) fair_OL_state llist \<Rightarrow> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set"
where
  "Liminf_fstate Sts =
   (Liminf_llist (lmap new_of Sts),
    Liminf_llist (lmap (set_option \<circ> xx_of) Sts),
    Liminf_llist (lmap (formulas \<circ> passive_of) Sts),
    Liminf_llist (lmap (set_option \<circ> yy_of) Sts),
    Liminf_llist (lmap active_of Sts))"

lemma Liminf_fstate_commute: "Liminf_llist (lmap fstate Sts) = state (Liminf_fstate Sts)"
proof -
  have "Liminf_llist (lmap fstate Sts) =
    (\<lambda>C. (C, New)) ` Liminf_llist (lmap new_of Sts) \<union>
    (\<lambda>C. (C, XX)) ` Liminf_llist (lmap (set_option \<circ> xx_of) Sts) \<union>
    (\<lambda>C. (C, Passive)) ` Liminf_llist (lmap (formulas \<circ> passive_of) Sts) \<union>
    (\<lambda>C. (C, YY)) ` Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<union>
    (\<lambda>C. (C, Active)) ` Liminf_llist (lmap active_of Sts)"
    unfolding fstate_alt_def state_alt_def
    apply (subst Liminf_llist_lmap_union, fast)+
    apply (subst Liminf_llist_lmap_image, simp add: inj_on_convol_ident)+
    by auto
 then show ?thesis
   unfolding Liminf_fstate_def by fastforce
qed

fun state_union :: "'f set \<times> 'f set \<times> 'f set \<times> 'f set \<times> 'f set \<Rightarrow> 'f set" where
  "state_union (N, X, P, Y, A) = N \<union> X \<union> P \<union> Y \<union> A"

fun fstate_union :: "('p, 'f) fair_OL_state \<Rightarrow> 'f set" where
  "fstate_union (N, X, P, Y, A) = state_union (N, set_option X, formulas P, set_option Y, A)"

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
| transfer:
    "(N, Some C, P, None, A) \<leadsto>OLf (N, None, if C \<in> formulas P then P else add C P, None, A)"
| choose_p: "P \<noteq> empty \<Longrightarrow>
    ({}, None, P, None, A) \<leadsto>OLf ({}, None, remove (select P) P, Some (select P), A)"
| infer: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I (A \<union> {C} \<union> M) \<Longrightarrow>
    ({}, None, P, Some C, A) \<leadsto>OLf (M, None, P, None, A \<union> {C})"


subsection \<open>Initial State\<close>

inductive is_initial_fair_OL_state :: "('p, 'f) fair_OL_state \<Rightarrow> bool" where
  "is_initial_fair_OL_state (N, None, empty, None, {})"


subsection \<open>Invariant\<close>

inductive fair_OL_invariant :: "('p, 'f) fair_OL_state \<Rightarrow> bool" where
  "(N = {} \<and> X = None) \<or> Y = None \<Longrightarrow> fair_OL_invariant (N, X, P, Y, A)"

lemma initial_fair_OL_invariant:
  "is_initial_fair_OL_state St \<Longrightarrow> fair_OL_invariant St"
  unfolding is_initial_fair_OL_state.simps fair_OL_invariant.simps by auto

lemma step_fair_OL_invariant:
  assumes "St \<leadsto>OLf St'"
  shows "fair_OL_invariant St'"
  using assms by cases (simp_all add: fair_OL_invariant.intros)

lemma chain_fair_OL_invariant_lnth:
  assumes
    chain: "chain (\<leadsto>OLf) Sts" and
    fair_hd: "fair_OL_invariant (lhd Sts)" and
    i_lt: "enat i < llength Sts"
  shows "fair_OL_invariant (lnth Sts i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using fair_hd lhd_conv_lnth zero_enat_def by fastforce
next
  case (Suc i)
  then show ?case
    using chain chain_lnth_rel step_fair_OL_invariant by blast
qed

lemma chain_fair_OL_invariant_llast:
  assumes
    chain: "chain (\<leadsto>OLf) Sts" and
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
    using chain_fair_OL_invariant_lnth[OF chain fair_hd im1_lt]
    by (metis Suc_diff_1 chain chain_length_pos eSuc_enat enat_ord_simps(2) i llast_conv_lnth
        zero_enat_def)
qed


subsection \<open>Final State\<close>

inductive is_final_fair_OL_state :: "('p, 'f) fair_OL_state \<Rightarrow> bool" where
  "is_final_fair_OL_state ({}, None, empty, None, A)"

lemma is_final_fair_OL_state_iff_no_trans:
  assumes inv: "fair_OL_invariant St"
  shows "is_final_fair_OL_state St \<longleftrightarrow> (\<forall>St'. \<not> St \<leadsto>OLf St')"
proof
  assume "is_final_fair_OL_state St"
  then obtain A :: "'f set" where
    st: "St = ({}, None, empty, None, A)"
    by (auto simp: is_final_fair_OL_state.simps)
  show "\<forall>St'. \<not> St \<leadsto>OLf St'"
    unfolding st
  proof (intro allI notI)
    fix St'
    assume "({}, None, empty, None, A) \<leadsto>OLf St'"
    then show False
      by cases (auto simp: fformulas_empty)
  qed
next
  assume no_trans: "\<forall>St'. \<not> St \<leadsto>OLf St'"
  show "is_final_fair_OL_state St"
  proof (rule ccontr)
    assume not_fin: "\<not> is_final_fair_OL_state St"

    obtain N A :: "'f set" and X Y :: "'f option" and P :: 'p where
      st: "St = (N, X, P, Y, A)"
      by (cases St)

    have inv': "(N = {} \<and> X = None) \<or> Y = None"
      using inv st fair_OL_invariant.simps by simp

    have "N \<noteq> {} \<or> X \<noteq> None \<or> P \<noteq> empty \<or> Y \<noteq> None"
      using not_fin unfolding st is_final_fair_OL_state.simps by auto
    moreover {
      assume
        n: "N \<noteq> {}" and
        x: "X = None"

      obtain N' :: "'f set" and C :: 'f where
        n': "N = N' \<union> {C}" and
        c_ni: "C \<notin> N'"
        using n by (metis Set.set_insert ex_in_conv insert_is_Un sup_commute)
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
        n: "N = {}" and
        x: "X = None" and
        y: "Y = None"

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.choose_p[OF p] unfolding st n x y by fast
    } moreover {
      assume "Y \<noteq> None"
      then obtain C :: 'f where
        y: "Y = Some C"
        by blast

      have n: "N = {}" and
        x: "X = None"
        using y inv' by blast+

      let ?M = "concl_of ` no_labels.Inf_between A {C}"

      have inf_red: "no_labels.Inf_between A {C} \<subseteq> no_labels.Red_I_\<G> (A \<union> {C} \<union> ?M)"
        by (simp add: no_labels.Inf_if_Inf_between no_labels.empty_ord.Red_I_of_Inf_to_N subsetI)

      have "\<exists>St'. St \<leadsto>OLf St'"
        using fair_OL.infer[OF inf_red] unfolding st n x y by fast
    } ultimately show False
      using no_trans by force
  qed
qed


subsection \<open>Refinement\<close>

lemma fair_OL_step_imp_OL_step:
  assumes olf: "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A')"
  shows "fstate (N, X, P, Y, A) \<leadsto>OL fstate (N', X', P', Y', A')"
  using olf
proof cases
  case (choose_n C)
  note unfolds = this(1-7) and c_ni = this(8)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.choose_n[OF c_ni])
next
  case (delete_fwd C)
  note unfolds = this(1-7) and c_red = this(8)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.delete_fwd[OF c_red])
next
  case (simplify_fwd C' S C)
  note unfolds = this(1-7) and c_red = this(9)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.simplify_fwd[OF c_red])
next
  case (delete_bwd_p C' C)
  note unfolds = this(1-7) and c'_in_p = this(8) and c'_red = this(9)

  have p_rm_c'_uni_c': "formulas (remove C' P) \<union> {C'} = formulas P"
    unfolding fformulas_remove by (auto intro: c'_in_p)
  have p_mns_c': "formulas P - {C'} = formulas (remove C' P)"
    unfolding fformulas_remove by auto

  show ?thesis
    unfolding unfolds fstate.simps option.set
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
    unfolding unfolds fstate.simps option.set
    by (rule OL.simplify_bwd_p[OF c'_red, of _ "formulas P - {C'}",
          unfolded p_rm_c'_uni_c' p_mns_c'])
next
  case (delete_bwd_a C' C)
  note unfolds = this(1-7) and c'_red = this(8)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.delete_bwd_a[OF c'_red])
next
  case (simplify_bwd_a C' S C C'')
  note unfolds = this(1-7) and c'_red = this(9)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.simplify_bwd_a[OF c'_red])
next
  case (transfer C)
  note unfolds = this(1-7)

  have p_uni_c: "formulas P \<union> {C} = formulas (if C \<in> formulas P then P else add C P)"
    using fformulas_add by auto

  show ?thesis
    unfolding unfolds fstate.simps option.set
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
    unfolding unfolds fstate.simps option.set
    by (rule OL.choose_p[of "select P" "formulas (remove (select P) P)", OF sel_ni_rm,
          unfolded rm_sel_uni_sel])
next
  case (infer C)
  note unfolds = this(1-7) and infers = this(8)
  show ?thesis
    unfolding unfolds fstate.simps option.set by (rule OL.infer[OF infers])
qed

lemma fair_OL_step_imp_GC_step:
  "(N, X, P, Y, A) \<leadsto>OLf (N', X', P', Y', A') \<Longrightarrow>
   fstate (N, X, P, Y, A) \<leadsto>GC fstate (N', X', P', Y', A')"
  by (rule OL_step_imp_GC_step[OF fair_OL_step_imp_OL_step])


subsection \<open>Completeness\<close>

lemma no_labels_entails_mono_left: "M \<subseteq> N \<Longrightarrow> M \<Turnstile>\<inter>\<G> P \<Longrightarrow> N \<Turnstile>\<inter>\<G> P"
  using no_labels.entails_trans no_labels.subset_entailed by blast

lemma wfP_multp_Prec_S: "wfP (multp (\<prec>S))"
  using minimal_element_def wfP_multp wf_prec_S wfp_on_UNIV by blast

fun mset_of_fstate :: "('p, 'f) fair_OL_state \<Rightarrow> 'f multiset" where
  "mset_of_fstate St = mset_set (fstate_union St)"

lemma fair_OL_Liminf_new_empty:
  assumes
    full: "full_chain (\<leadsto>OLf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
  shows "Liminf_llist (lmap new_of Sts) = {}"
proof (rule ccontr)
  assume "Liminf_llist (lmap new_of Sts) \<noteq> {}"

  show False
    sorry
qed

lemma fair_OL_Liminf_xx_empty:
  assumes
    full: "full_chain (\<leadsto>OLf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
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

  have nfin: "\<not> lfinite Sts"
  proof
    assume "lfinite Sts"
    then obtain k :: nat where
      k: "enat (Suc k) = llength Sts"
      by (metis lessE enat_ord_simps(2) i_lt lfinite_llength_enat)
    then have k_lt: "enat k < llength Sts"
      by (metis enat_ord_simps(2) lessI)
    have inv_at_i: "fair_OL_invariant (lnth Sts k)"
      by (rule chain_fair_OL_invariant_lnth[OF full_chain_imp_chain[OF full] inv k_lt])

    have "\<exists>St'. lnth Sts k \<leadsto>OLf St'"
      using is_final_fair_OL_state_iff_no_trans[OF inv_at_i]
      by (metis c_in' elem_set enat_ord_simps(2) fair_otter_loop.is_final_fair_OL_state.cases
          fair_otter_loop_axioms fst_conv i_lt k le_Suc_eq le_eq_less_or_eq lessI less_irrefl_nat
          option.simps(3) snd_conv)
    thus False
      using full_chain_lnth_not_rel[OF full k] by simp
  qed
  hence si_lt: "enat (Suc i) < llength Sts"
    by (simp add: not_lfinite_llength)

  have "multp (\<prec>S) (mset_of_fstate (lnth Sts (Suc j))) (mset_of_fstate (lnth Sts j))"
    if j_ge: "j \<ge> i" for j
    sorry
  hence "(multp (\<prec>S))\<inverse>\<inverse> (mset_of_fstate (lnth Sts j)) (mset_of_fstate (lnth Sts (Suc j)))"
    if j_ge: "j \<ge> i" for j
    using j_ge by blast
  hence inf_down_chain: "chain (multp (\<prec>S))\<inverse>\<inverse> (ldropn i (lmap mset_of_fstate Sts))"
    using chain_ldropn_lmapI[OF _ si_lt] by blast

  have inf_i: "\<not> lfinite (ldropn i Sts)"
    using nfin by simp

  show False
    using inf_i inf_down_chain wfP_iff_no_infinite_down_chain_llist[of "multp (\<prec>S)"]
      wfP_multp_Prec_S
    by (metis lfinite_ldropn lfinite_lmap)
qed

lemma OLf_step_imp_passive_step:
  assumes olf_step: "St \<leadsto>OLf St'"
  shows "passive_step (passive_of St) (passive_of St')"
  using olf_step
proof cases
  case (choose_n C N P A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
next
  case (delete_fwd C P A N)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
next
  case (simplify_fwd C' S C P A N)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
next
  case (delete_bwd_p C' P C N A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = remove C' P"
    unfolding unfolds by simp
  show ?thesis
    unfolding unfolds pas by (auto intro: passive_step_removeI)
next
  case (simplify_bwd_p C' S P C C'' N A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = remove C' P"
    unfolding unfolds by simp
  show ?thesis
    unfolding unfolds pas by (auto intro: passive_step_removeI)
next
  case (delete_bwd_a C' C N P A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
next
  case (simplify_bwd_a C' S C C'' N P A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
next
  case (transfer N C P A)
  note unfolds = this(1,2)
  show ?thesis
  proof (cases "C \<in> formulas P")
    case c_in: True
    show ?thesis
      unfolding unfolds by (auto simp: c_in intro: passive_step_idleI)
  next
    case c_ni: False
    show ?thesis
      unfolding unfolds by (auto simp: c_ni intro: passive_step_addI)
  qed
next
  case (choose_p P A)
  note unfolds = this(1,2)
  have pas: "passive_of St' = remove (select P) P"
    unfolding unfolds by simp
  show ?thesis
    unfolding unfolds pas by (auto intro: passive_step_removeI)
next
  case (infer A C M P)
  note unfolds = this(1,2)
  have pas: "passive_of St' = passive_of St"
    unfolding unfolds by simp
  show ?thesis
    unfolding pas by (rule passive_step_idleI)
qed

lemma fair_OL_Liminf_passive_empty:
  assumes
    len: "llength Sts = \<infinity>" and
    full: "full_chain (\<leadsto>OLf) Sts" and
    init: "is_initial_fair_OL_state (lhd Sts)"
  shows "Liminf_llist (lmap (formulas \<circ> passive_of) Sts) = {}"
proof -
  have chain_step: "chain passive_step (lmap passive_of Sts)"
    using OLf_step_imp_passive_step chain_lmap full_chain_imp_chain[OF full]
    by (metis (no_types, lifting))

  have inf_oft: "infinitely_often select_passive_step (lmap passive_of Sts)"
    (* TODO: Exploit well-foundedness of simplification *)
    sorry

  have hd_emp: "lhd (lmap passive_of Sts) = empty"
    using init full full_chain_not_lnull unfolding is_initial_fair_OL_state.simps by fastforce

  have "Liminf_llist (lmap formulas (lmap passive_of Sts)) = {}"
    by (rule fair[of "lmap passive_of Sts", OF chain_step inf_oft hd_emp])
  then show ?thesis
    by (simp add: llist.map_comp)
qed

lemma fair_OL_Liminf_yy_empty:
  assumes
    full: "full_chain (\<leadsto>OLf) Sts" and
    inv: "fair_OL_invariant (lhd Sts)"
  shows "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) = {}"
proof (rule ccontr)
  assume lim_nemp: "Liminf_llist (lmap (set_option \<circ> yy_of) Sts) \<noteq> {}"

  have chain: "chain (\<leadsto>OLf) Sts"
    by (rule full_chain_imp_chain[OF full])

  obtain i :: nat where
    i_lt: "enat i < llength Sts" and
    inter_nemp: "\<Inter> ((set_option \<circ> yy_of \<circ> lnth Sts) ` {j. i \<le> j \<and> enat j < llength Sts}) \<noteq> {}"
    using lim_nemp unfolding Liminf_llist_def by auto

  have inv_at_i: "fair_OL_invariant (lnth Sts i)"
    by (simp add: chain chain_fair_OL_invariant_lnth i_lt inv)

  from inter_nemp obtain C :: 'f where
    c_in: "\<forall>P \<in> lnth Sts ` {j. i \<le> j \<and> enat j < llength Sts}. C \<in> set_option (yy_of P)"
    by auto
  hence c_in': "\<forall>j \<ge> i. enat j < llength Sts \<longrightarrow> C \<in> set_option (yy_of (lnth Sts j))"
    by auto

  have yy_at_i: "yy_of (lnth Sts i) = Some C"
    using c_in' i_lt by blast
  have new_at_i: "new_of (lnth Sts i) = {}" and
    xx_at_i: "new_of (lnth Sts i) = {}"
    using yy_at_i chain_fair_OL_invariant_lnth[OF chain inv i_lt]
    by (force simp: fair_OL_invariant.simps)+

  have "\<exists>St'. lnth Sts i \<leadsto>OLf St'"
    using is_final_fair_OL_state_iff_no_trans[OF inv_at_i]
    by (metis fst_conv is_final_fair_OL_state.cases option.simps(3) snd_conv yy_at_i)
  hence si_lt: "enat (Suc i) < llength Sts"
    by (metis Suc_ile_eq full full_chain_lnth_not_rel i_lt order_le_imp_less_or_eq)

  obtain P :: 'p and A :: "'f set" where
    at_i: "lnth Sts i = ({}, None, P, Some C, A)"
    using fair_OL_invariant.simps inv_at_i yy_at_i by auto

  have "lnth Sts i \<leadsto>OLf lnth Sts (Suc i)"
    by (simp add: chain chain_lnth_rel si_lt)
  then have "({}, None, P, Some C, A) \<leadsto>OLf lnth Sts (Suc i)"
    unfolding at_i .
  then have "yy_of (lnth Sts (Suc i)) = None"
    by cases simp
  then show False
    using c_in' si_lt by simp
qed

theorem
  assumes
    olf_full: "full_chain (\<leadsto>OLf) Sts" and
    olf_init: "is_initial_fair_OL_state (lhd Sts)" and
    xx: "xx_of (lhd Sts) = None" and
    yy: "yy_of (lhd Sts) = None" and
    act: "active_of (lhd Sts) = {}" and
    bot: "B \<in> Bot_F" and
    unsat: "new_of (lhd Sts) \<Turnstile>\<inter>\<G> {B}"
  shows
    OL_complete_Liminf: "\<exists>B \<in> Bot_F. B \<in> state_union (Liminf_fstate Sts)" and
    OL_complete: "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
proof -
  have olf_chain: "chain (\<leadsto>OLf) Sts"
    by (rule full_chain_imp_chain[OF olf_full])
  have gc_chain: "chain (\<leadsto>GC) (lmap fstate Sts)"
    using olf_chain fair_OL_step_imp_GC_step chain_lmap by (smt (verit) fstate.cases)

  have olf_inv: "fair_OL_invariant (lhd Sts)"
    using olf_init unfolding is_initial_fair_OL_state.simps fair_OL_invariant.simps by fast

  have nnul: "\<not> lnull Sts"
    using olf_chain chain_not_lnull by blast
  hence lhd_lmap: "\<And>f. lhd (lmap f Sts) = f (lhd Sts)"
    by (rule llist.map_sel(1))
  have act': "active_subset (lhd (lmap fstate Sts)) = {}"
    using act unfolding active_subset_def lhd_lmap by (cases "lhd Sts") auto

  have pas': "passive_subset (Liminf_llist (lmap fstate Sts)) = {}"
  proof (cases "lfinite Sts")
    case fin: True

    have lim: "Liminf_llist (lmap fstate Sts) = fstate (llast Sts)"
      using lfinite_Liminf_llist fin nnul
      by (metis chain_not_lnull gc_chain lfinite_lmap llast_lmap)

    have last_inv: "fair_OL_invariant (llast Sts)"
      by (rule chain_fair_OL_invariant_llast[OF olf_chain olf_inv fin])

    have "\<forall>St'. \<not> llast Sts \<leadsto>OLf St'"
      using full_chain_lnth_not_rel[OF olf_full] by (metis fin full_chain_iff_chain olf_full)
    then have "is_final_fair_OL_state (llast Sts)"
      unfolding is_final_fair_OL_state_iff_no_trans[OF last_inv] .
    then obtain A :: "'f set" where
      at_l: "llast Sts = ({}, None, empty, None, A)"
      unfolding is_final_fair_OL_state.simps by blast
    show ?thesis
      unfolding is_final_fair_OL_state.simps passive_subset_def lim at_l fstate.simps state.simps
      by (auto simp: fformulas_empty)
  next
    case False
    then have len: "llength Sts = \<infinity>"
      by (simp add: not_lfinite_llength)
    show ?thesis
      unfolding Liminf_fstate_commute passive_subset_def Liminf_fstate_def
      using fair_OL_Liminf_new_empty[OF olf_full olf_inv]
        fair_OL_Liminf_xx_empty[OF olf_full olf_inv]
        fair_OL_Liminf_passive_empty[OF len olf_full olf_init]
        fair_OL_Liminf_yy_empty[OF olf_full olf_inv]
      by simp
  qed

  have unsat': "fst ` lhd (lmap fstate Sts) \<Turnstile>\<inter>\<G> {B}"
    using unsat unfolding lhd_lmap by (cases "lhd Sts") (auto intro: no_labels_entails_mono_left)

  have "\<exists>BL \<in> Bot_FL. BL \<in> Liminf_llist (lmap fstate Sts)"
    by (rule gc_complete_Liminf[OF gc_chain act' pas' bot unsat'])
  then show "\<exists>B \<in> Bot_F. B \<in> state_union (Liminf_fstate Sts)"
    unfolding Liminf_fstate_def Liminf_fstate_commute by auto
  then show "\<exists>i. enat i < llength Sts \<and> (\<exists>B \<in> Bot_F. B \<in> all_of (lnth Sts i))"
    unfolding Liminf_fstate_def Liminf_llist_def by auto
qed

end

end
