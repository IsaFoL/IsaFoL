theory DPLL_W
imports
  Entailment_Definition.Partial_Herbrand_Interpretation
  Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
  Weidenbach_Book_Base.Wellfounded_More
begin

section \<open>Weidenbach's DPLL\<close>

subsection \<open>Rules\<close>

type_synonym 'a dpll\<^sub>W_ann_lit = "('a, unit) ann_lit"
type_synonym 'a dpll\<^sub>W_ann_lits = "('a, unit) ann_lits"
type_synonym 'v dpll\<^sub>W_state = "'v dpll\<^sub>W_ann_lits \<times> 'v clauses"

abbreviation trail :: "'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_ann_lits" where
"trail \<equiv> fst"
abbreviation clauses :: "'v dpll\<^sub>W_state \<Rightarrow> 'v clauses" where
"clauses \<equiv> snd"

inductive dpll\<^sub>W :: "'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> bool" where
propagate: "add_mset L C \<in># clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit (trail S) L
  \<Longrightarrow> dpll\<^sub>W S (Propagated L () # trail S, clauses S)" |
decided: "undefined_lit (trail S) L \<Longrightarrow> atm_of L \<in> atms_of_mm (clauses S)
  \<Longrightarrow> dpll\<^sub>W S (Decided L # trail S, clauses S)" |
backtrack: "backtrack_split (trail S) = (M', L # M) \<Longrightarrow> is_decided L \<Longrightarrow> D \<in># clauses S
  \<Longrightarrow> trail S \<Turnstile>as CNot D \<Longrightarrow> dpll\<^sub>W S (Propagated (- (lit_of L)) () # M, clauses S)"


subsection \<open>Invariants\<close>

lemma dpll\<^sub>W_distinct_inv:
  assumes "dpll\<^sub>W S S'"
  and "no_dup (trail S)"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: dpll\<^sub>W.induct)
  case (decided L S)
  then show ?case using defined_lit_map by force
next
  case (propagate C L S)
  then show ?case using defined_lit_map by force
next
  case (backtrack S M' L M D) note extracted = this(1) and no_dup = this(5)
  show ?case
    using no_dup backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted
    by (auto dest: no_dup_appendD)
qed

lemma dpll\<^sub>W_consistent_interp_inv:
  assumes "dpll\<^sub>W S S'"
  and "consistent_interp (lits_of_l (trail S))"
  and "no_dup (trail S)"
  shows "consistent_interp (lits_of_l (trail S'))"
  using assms
proof (induct rule: dpll\<^sub>W.induct)
  case (backtrack S M' L M D) note extracted = this(1) and decided = this(2) and D = this(4) and
    cons = this(5) and no_dup = this(6)
  have no_dup': "no_dup M"
    by (metis (no_types) backtrack_split_list_eq distinct.simps(2) distinct_append extracted
      list.simps(9) map_append no_dup snd_conv no_dup_def)
  then have "insert (lit_of L) (lits_of_l M) \<subseteq> lits_of_l (trail S)"
    using backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted by auto
  then have cons: "consistent_interp (insert (lit_of L) (lits_of_l M))"
    using consistent_interp_subset cons by blast
  moreover have undef: "undefined_lit M (lit_of L)"
      using no_dup backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted by force
  moreover have "lit_of L \<notin> lits_of_l M"
      using undef by (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  ultimately show ?case by simp
qed (auto intro: consistent_add_undefined_lit_consistent)

lemma dpll\<^sub>W_vars_in_snd_inv:
  assumes "dpll\<^sub>W S S'"
  and "atm_of ` (lits_of_l (trail S)) \<subseteq> atms_of_mm (clauses S)"
  shows "atm_of ` (lits_of_l (trail S')) \<subseteq> atms_of_mm (clauses S')"
  using assms
proof (induct rule: dpll\<^sub>W.induct)
  case (backtrack S M' L M D)
  then have "atm_of (lit_of L) \<in> atms_of_mm (clauses S)"
    using backtrack_split_list_eq[of "trail S", symmetric] by auto
  moreover
    have "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)"
      using backtrack(5)  by simp
    then have "\<And>xb. xb \<in> set M \<Longrightarrow> atm_of (lit_of xb) \<in> atms_of_mm (clauses S)"
      using backtrack_split_list_eq[symmetric, of "trail S"] backtrack.hyps(1)
      unfolding lits_of_def by auto
  ultimately show ?case by (auto simp : lits_of_def)
qed (auto simp: in_plus_implies_atm_of_on_atms_of_ms)

lemma atms_of_ms_lit_of_atms_of: "atms_of_ms (unmark ` c) = atm_of ` lit_of ` c"
  unfolding atms_of_ms_def using image_iff by force

text \<open>\cwref{dpll:sound:model}{theorem 2.8.2 page 73}\<close>
lemma dpll\<^sub>W_propagate_is_conclusion:
  assumes "dpll\<^sub>W S S'"
  and "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))"
  and "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)"
  shows "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
  using assms
proof (induct rule: dpll\<^sub>W.induct)
  case (decided L S)
  then show ?case unfolding all_decomposition_implies_def by simp
next
  case (propagate L C S) note inS = this(1) and cnot = this(2) and IH = this(4) and undef = this(3) and atms_incl = this(5)
  let ?I = "set (map unmark (trail S)) \<union> set_mset (clauses S)"
  have "?I \<Turnstile>p add_mset L C" by (auto simp add: inS)
  moreover have "?I \<Turnstile>ps CNot C" using true_annots_true_clss_cls cnot by fastforce
  ultimately have "?I \<Turnstile>p {#L#}" using true_clss_cls_plus_CNot[of ?I L C] inS by blast
  {
    assume "get_all_ann_decomposition (trail S) = []"
    then have ?case by blast
  }
  moreover {
    assume n: "get_all_ann_decomposition (trail S) \<noteq> []"
    have 1: "\<And>a b. (a, b) \<in> set (tl (get_all_ann_decomposition (trail S)))
      \<Longrightarrow> (unmark_l a \<union> set_mset (clauses S)) \<Turnstile>ps unmark_l b"
      using IH unfolding all_decomposition_implies_def by (fastforce simp add: list.set_sel(2) n)
    moreover have 2: "\<And>a c. hd (get_all_ann_decomposition (trail S)) = (a, c)
      \<Longrightarrow> (unmark_l a \<union> set_mset (clauses S)) \<Turnstile>ps (unmark_l c)"
      by (metis IH all_decomposition_implies_cons_pair all_decomposition_implies_single
        list.collapse n)
    moreover have 3: "\<And>a c. hd (get_all_ann_decomposition (trail S)) = (a, c)
      \<Longrightarrow> (unmark_l a \<union> set_mset (clauses S)) \<Turnstile>p {#L#}"
      proof -
        fix a c
        assume h: "hd (get_all_ann_decomposition (trail S)) = (a, c)"
        have h': "trail S = c @ a" using get_all_ann_decomposition_decomp h by blast
        have I: "set (map unmark a) \<union> set_mset (clauses S)
          \<union> unmark_l c \<Turnstile>ps CNot C"
          using \<open>?I \<Turnstile>ps CNot C\<close> unfolding h' by (simp add: Un_commute Un_left_commute)
        have
          "atms_of_ms (CNot C) \<subseteq> atms_of_ms (set (map unmark a) \<union> set_mset (clauses S))"
            and
          "atms_of_ms (unmark_l c) \<subseteq> atms_of_ms (set (map unmark a)
            \<union> set_mset (clauses S))"
           using atms_incl cnot
           apply (auto simp: atms_of_def dest!: true_annots_CNot_all_atms_defined; fail)[]
          using inS atms_of_atms_of_ms_mono atms_incl by (fastforce simp: h')

        then have "unmark_l a \<union> set_mset (clauses S) \<Turnstile>ps CNot C"
          using true_clss_clss_left_right[OF _ I] h "2" by auto
        then show "unmark_l a \<union> set_mset (clauses S) \<Turnstile>p {#L#}"
          using inS true_clss_cls_plus_CNot true_clss_clss_in_imp_true_clss_cls union_trus_clss_clss
          by blast
      qed
    ultimately have ?case
      by (cases "hd (get_all_ann_decomposition (trail S))")
         (auto simp: all_decomposition_implies_def)
  }
  ultimately show ?case by auto
next
  case (backtrack S M' L M D) note extracted = this(1) and decided = this(2) and D = this(3) and
    cnot = this(4) and cons = this(4) and IH = this(5) and atms_incl = this(6)
  have S: "trail S = M' @ L # M"
    using backtrack_split_list_eq[of "trail S"] unfolding extracted by auto
  have M': "\<forall>l \<in> set M'. \<not>is_decided l"
    using extracted backtrack_split_fst_not_decided[of _ "trail S"] by simp
  have n: "get_all_ann_decomposition (trail S) \<noteq> []" by auto
  then have "all_decomposition_implies_m (clauses S) ((L # M, M')
           # tl (get_all_ann_decomposition (trail S)))"
    by (metis (no_types) IH extracted get_all_ann_decomposition_backtrack_split list.exhaust_sel)
  then have 1: "unmark_l (L # M) \<union> set_mset (clauses S) \<Turnstile>ps(\<lambda>a.{#lit_of a#}) ` set M'"
    by simp
  moreover
    have "unmark_l (L # M) \<union> unmark_l M' \<Turnstile>ps CNot D"
      by (metis (mono_tags, lifting) S Un_commute cons image_Un set_append
        true_annots_true_clss_clss)
    then have 2: "unmark_l (L # M) \<union> set_mset (clauses S) \<union> unmark_l M'
        \<Turnstile>ps CNot D"
      by (metis (no_types, lifting) Un_assoc Un_left_commute true_clss_clss_union_l_r)
  ultimately
    have "set (map unmark (L # M)) \<union> set_mset (clauses S) \<Turnstile>ps CNot D"
      using true_clss_clss_left_right by fastforce
    then have "set (map unmark (L # M)) \<union> set_mset (clauses S) \<Turnstile>p {#}"
      by (metis (mono_tags, lifting) D Un_def mem_Collect_eq
        true_clss_clss_contradiction_true_clss_cls_false)
    then have IL: "unmark_l M \<union> set_mset (clauses S) \<Turnstile>p {#-lit_of L#}"
      using true_clss_clss_false_left_right by auto
  show ?case unfolding S all_decomposition_implies_def
    proof
      fix x P level
      assume x: "x \<in> set (get_all_ann_decomposition
        (fst (Propagated (- lit_of L) P # M, clauses S)))"
      let ?M' = "Propagated (- lit_of L) P # M"
      let ?hd = "hd (get_all_ann_decomposition ?M')"
      let ?tl = "tl (get_all_ann_decomposition ?M')"
      have "x = ?hd \<or> x \<in> set ?tl"
        using x
        by (cases "get_all_ann_decomposition ?M'")
           auto
      moreover {
        assume x': "x \<in> set ?tl"
        have L': "Decided (lit_of L) = L" using decided by (cases L, auto)
        have "x \<in> set (get_all_ann_decomposition (M' @ L # M))"
          using x' get_all_ann_decomposition_except_last_choice_equal[of M' "lit_of L" P M]
          L' by (metis (no_types) M' list.set_sel(2) tl_Nil)
        then have "case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> set_mset (clauses S)
          \<Turnstile>ps unmark_l seen"
          using decided IH by (cases L) (auto simp add: S all_decomposition_implies_def)
      }
      moreover {
        assume x': "x = ?hd"
        have tl: "tl (get_all_ann_decomposition (M' @ L # M)) \<noteq> []"
        proof -
          have f1: "\<And>ms. length (get_all_ann_decomposition (M' @ ms))
              = length (get_all_ann_decomposition ms)"
            by (simp add: M' get_all_ann_decomposition_remove_undecided_length)
          have "Suc (length (get_all_ann_decomposition M)) \<noteq> Suc 0"
            by blast
          then show ?thesis
            using f1[of \<open>L # M\<close>] decided by (cases \<open>get_all_ann_decomposition
               (M' @ L # M)\<close>; cases L) auto
        qed
        obtain M0' M0 where
          L0: "hd (tl (get_all_ann_decomposition (M' @ L # M))) = (M0, M0')"
          by (cases "hd (tl (get_all_ann_decomposition (M' @ L # M)))")
        have x'': "x = (M0, Propagated (-lit_of L) P # M0')"
          unfolding x' using get_all_ann_decomposition_last_choice tl M' L0
          by (smt is_decided_ex_Decided lit_of.simps(1) local.decided old.unit.exhaust)
        obtain l_get_all_ann_decomposition where
          "get_all_ann_decomposition (trail S) = (L # M, M') # (M0, M0') #
            l_get_all_ann_decomposition"
          using get_all_ann_decomposition_backtrack_split extracted by (metis (no_types) L0 S
            hd_Cons_tl n tl)
        then have "M = M0' @ M0" using get_all_ann_decomposition_hd_hd by fastforce
        then have IL':  "unmark_l M0 \<union> set_mset (clauses S)
          \<union> unmark_l M0' \<Turnstile>ps {{#- lit_of L#}}"
          using IL by (simp add: Un_commute Un_left_commute image_Un)
        moreover have H: "unmark_l M0 \<union> set_mset (clauses S)
          \<Turnstile>ps unmark_l M0'"
          using IH x'' unfolding all_decomposition_implies_def by (metis (no_types, lifting) L0 S
            list.set_sel(1) list.set_sel(2) old.prod.case tl tl_Nil)
        ultimately have "case x of (Ls, seen) \<Rightarrow> unmark_l Ls \<union> set_mset (clauses S)
          \<Turnstile>ps unmark_l seen"
          using true_clss_clss_left_right unfolding x'' by auto
      }
      ultimately show "case x of (Ls, seen) \<Rightarrow>
        unmark_l Ls \<union> set_mset (snd (?M', clauses S))
          \<Turnstile>ps unmark_l seen"
        unfolding snd_conv by blast
    qed
qed

text \<open>\cwref{dpll:sound:propLits:valuation}{theorem 2.8.3 page 73}\<close>
theorem dpll\<^sub>W_propagate_is_conclusion_of_decided:
  assumes "dpll\<^sub>W S S'"
  and "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))"
  and "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)"
  shows "set_mset (clauses S') \<union> {{#lit_of L#} |L. is_decided L \<and> L \<in> set (trail S')}
    \<Turnstile>ps unmark ` \<Union>(set ` snd ` set (get_all_ann_decomposition (trail S')))"
  using all_decomposition_implies_trail_is_implied[OF dpll\<^sub>W_propagate_is_conclusion[OF assms]] .

text \<open>\cwref{dpll:sound:propLits:unsat}{theorem 2.8.4 page 73}\<close>
lemma only_propagated_vars_unsat:
  assumes decided: "\<forall>x \<in> set M. \<not> is_decided x"
  and DN: "D \<in> N" and D: "M \<Turnstile>as CNot D"
  and inv: "all_decomposition_implies N (get_all_ann_decomposition M)"
  and atm_incl: "atm_of ` lits_of_l M \<subseteq> atms_of_ms N"
  shows "unsatisfiable N"
proof (rule ccontr)
  assume "\<not> unsatisfiable N"
  then obtain I where
    I: "I \<Turnstile>s N" and
    cons: "consistent_interp I" and
    tot: "total_over_m I N"
    unfolding satisfiable_def by auto
  then have I_D: "I \<Turnstile> D"
    using DN unfolding true_clss_def by auto

  have l0: "{{#lit_of L#} |L. is_decided L \<and> L \<in> set M} = {}" using decided by auto
  have "atms_of_ms (N \<union> unmark_l M) = atms_of_ms N"
    using atm_incl unfolding atms_of_ms_def lits_of_def by auto

  then have "total_over_m I (N \<union> unmark ` (set M))"
    using tot unfolding total_over_m_def by auto
  then have "I \<Turnstile>s unmark ` (set M)"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  then have IM: "I \<Turnstile>s unmark_l M" by auto
  {
    fix K
    assume "K \<in># D"
    then have "-K \<in> lits_of_l M"
      by (auto split: if_split_asm
        intro: allE[OF D[unfolded true_annots_def Ball_def], of "{#-K#}"])
    then have "-K \<in> I" using IM true_clss_singleton_lit_of_implies_incl by fastforce
  }
  then have "\<not> I \<Turnstile> D" using cons unfolding true_cls_def consistent_interp_def by auto
  then show False using I_D by blast
qed

lemma dpll\<^sub>W_same_clauses:
  assumes "dpll\<^sub>W S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: dpll\<^sub>W.induct, auto)

lemma rtranclp_dpll\<^sub>W_inv:
  assumes "rtranclp dpll\<^sub>W S S'"
  and inv: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))"
  and atm_incl: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)"
  and "consistent_interp (lits_of_l (trail S))"
  and "no_dup (trail S)"
  shows "all_decomposition_implies_m (clauses S') (get_all_ann_decomposition (trail S'))"
  and "atm_of ` lits_of_l (trail S')  \<subseteq> atms_of_mm (clauses S')"
  and "clauses S = clauses S'"
  and "consistent_interp (lits_of_l (trail S'))"
  and "no_dup (trail S')"
  using assms
proof (induct rule: rtranclp_induct)
  case base
  show
    "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
    "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)" and
    "clauses S = clauses S" and
    "consistent_interp (lits_of_l (trail S))" and
    "no_dup (trail S)" using assms by auto
next
  case (step S' S'') note dpll\<^sub>WStar = this(1) and IH = this(3,4,5,6,7) and
    dpll\<^sub>W = this(2)
  moreover
    assume
      inv: "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))" and
      atm_incl: "atm_of ` lits_of_l (trail S)  \<subseteq> atms_of_mm (clauses S)" and
      cons: "consistent_interp (lits_of_l (trail S))" and
      "no_dup (trail S)"
  ultimately have decomp: "all_decomposition_implies_m (clauses S')
    (get_all_ann_decomposition (trail S'))" and
    atm_incl': "atm_of ` lits_of_l (trail S') \<subseteq> atms_of_mm (clauses S')" and
    snd: "clauses S = clauses S'" and
    cons': "consistent_interp (lits_of_l (trail S'))" and
    no_dup': "no_dup (trail S')" by blast+
  show "clauses S = clauses S''" using dpll\<^sub>W_same_clauses[OF dpll\<^sub>W] snd by metis

  show "all_decomposition_implies_m (clauses S'') (get_all_ann_decomposition (trail S''))"
    using dpll\<^sub>W_propagate_is_conclusion[OF dpll\<^sub>W] decomp atm_incl' by auto
  show "atm_of ` lits_of_l (trail S'') \<subseteq> atms_of_mm (clauses S'')"
    using dpll\<^sub>W_vars_in_snd_inv[OF dpll\<^sub>W]  atm_incl atm_incl' by auto
  show "no_dup (trail S'')" using dpll\<^sub>W_distinct_inv[OF dpll\<^sub>W] no_dup' dpll\<^sub>W by auto
  show "consistent_interp (lits_of_l (trail S''))"
    using cons' no_dup' dpll\<^sub>W_consistent_interp_inv[OF dpll\<^sub>W] by auto
qed

definition "dpll\<^sub>W_all_inv S \<equiv>
  (all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))
  \<and> atm_of ` lits_of_l (trail S)  \<subseteq> atms_of_mm (clauses S)
  \<and> consistent_interp (lits_of_l (trail S))
  \<and> no_dup (trail S))"

lemma dpll\<^sub>W_all_inv_dest[dest]:
  assumes "dpll\<^sub>W_all_inv S"
  shows "all_decomposition_implies_m (clauses S) (get_all_ann_decomposition (trail S))"
  and "atm_of ` lits_of_l (trail S)  \<subseteq> atms_of_mm (clauses S)"
  and "consistent_interp (lits_of_l (trail S)) \<and> no_dup (trail S)"
  using assms unfolding dpll\<^sub>W_all_inv_def lits_of_def by auto

lemma rtranclp_dpll\<^sub>W_all_inv:
  assumes "rtranclp dpll\<^sub>W S S'"
  and "dpll\<^sub>W_all_inv S"
  shows "dpll\<^sub>W_all_inv S'"
  using assms rtranclp_dpll\<^sub>W_inv[OF assms(1)] unfolding dpll\<^sub>W_all_inv_def lits_of_def by blast

lemma dpll\<^sub>W_all_inv:
  assumes "dpll\<^sub>W S S'"
  and "dpll\<^sub>W_all_inv S"
  shows "dpll\<^sub>W_all_inv S'"
  using assms rtranclp_dpll\<^sub>W_all_inv by blast

lemma rtranclp_dpll\<^sub>W_inv_starting_from_0:
  assumes "rtranclp dpll\<^sub>W S S'"
  and inv: "trail S = []"
  shows "dpll\<^sub>W_all_inv S'"
proof -
  have "dpll\<^sub>W_all_inv S"
    using assms unfolding all_decomposition_implies_def dpll\<^sub>W_all_inv_def by auto
  then show ?thesis using rtranclp_dpll\<^sub>W_all_inv[OF assms(1)] by blast
qed

lemma dpll\<^sub>W_can_do_step:
  assumes "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_mm N"
  shows "rtranclp dpll\<^sub>W ([], N) (map Decided M, N)"
  using assms
proof (induct M)
  case Nil
  then show ?case by auto
next
  case (Cons L M)
  then have "undefined_lit (map Decided M) L"
    unfolding defined_lit_def consistent_interp_def by auto
  moreover have "atm_of L \<in> atms_of_mm N" using Cons.prems(3) by auto
  ultimately have "dpll\<^sub>W (map Decided M, N) (map Decided (L # M), N)"
    using dpll\<^sub>W.decided by auto
  moreover have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_mm N"
    using Cons.prems unfolding consistent_interp_def by auto
  ultimately show ?case using Cons.hyps by auto
qed

definition "conclusive_dpll\<^sub>W_state (S:: 'v dpll\<^sub>W_state) \<longleftrightarrow>
  (trail S \<Turnstile>asm clauses S \<or> ((\<forall>L \<in> set (trail S). \<not>is_decided L)
  \<and> (\<exists>C \<in># clauses S. trail S \<Turnstile>as CNot C)))"

text \<open>\cwref{prop:prop:dpllcomplete}{theorem 2.8.6 page 74}\<close>
lemma dpll\<^sub>W_strong_completeness:
  assumes "set M \<Turnstile>sm N"
  and "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_mm N"
  shows "dpll\<^sub>W\<^sup>*\<^sup>* ([], N) (map Decided M, N)"
  and "conclusive_dpll\<^sub>W_state (map Decided M, N)"
proof -
  show "rtranclp dpll\<^sub>W ([], N) (map Decided M, N)" using dpll\<^sub>W_can_do_step assms by auto
  have "map Decided M \<Turnstile>asm N" using assms(1) true_annots_decided_true_cls by auto
  then show "conclusive_dpll\<^sub>W_state (map Decided M, N)"
    unfolding conclusive_dpll\<^sub>W_state_def by auto
qed

text \<open>\cwref{prop:prop:dpllsound}{theorem 2.8.5 page 73}\<close>
lemma dpll\<^sub>W_sound:
  assumes
    "rtranclp dpll\<^sub>W ([], N) (M, N)" and
    "\<forall>S. \<not>dpll\<^sub>W (M, N) S"
  shows "M \<Turnstile>asm N \<longleftrightarrow> satisfiable (set_mset N)" (is "?A \<longleftrightarrow> ?B")
proof
  let ?M'= "lits_of_l M"
  assume ?A
  then have "?M' \<Turnstile>sm N" by (simp add: true_annots_true_cls)
  moreover have "consistent_interp ?M'"
    using rtranclp_dpll\<^sub>W_inv_starting_from_0[OF assms(1)] by auto
  ultimately show ?B by auto
next
  assume ?B
  show ?A
    proof (rule ccontr)
      assume n: "\<not> ?A"
      have "(\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm N) \<or> (\<exists>D\<in>#N. M \<Turnstile>as CNot D)"
        proof -
          obtain D :: "'a clause" where D: "D \<in># N" and "\<not> M \<Turnstile>a D"
            using n unfolding true_annots_def Ball_def by auto
          then have "(\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of D) \<or> M \<Turnstile>as CNot D"
             unfolding true_annots_def Ball_def CNot_def true_annot_def
             using atm_of_lit_in_atms_of true_annot_iff_decided_or_true_lit true_cls_def
             by (smt mem_Collect_eq union_single_eq_member)
          then show ?thesis
            by (metis Bex_def D atms_of_atms_of_ms_mono rev_subsetD)
        qed
      moreover {
        assume "\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm N"
        then have False using assms(2) decided by fastforce
      }
      moreover {
        assume "\<exists>D\<in>#N. M \<Turnstile>as CNot D"
        then obtain D where DN: "D \<in># N" and MD: "M \<Turnstile>as CNot D" by auto
        {
          assume "\<forall>l \<in> set M. \<not> is_decided l"
          moreover have "dpll\<^sub>W_all_inv ([], N)"
            using assms unfolding all_decomposition_implies_def dpll\<^sub>W_all_inv_def by auto
          ultimately have "unsatisfiable (set_mset N)"
            using only_propagated_vars_unsat[of M D "set_mset N"] DN MD
            rtranclp_dpll\<^sub>W_all_inv[OF assms(1)] by force
          then have False using \<open>?B\<close> by blast
        }
        moreover {
          assume l: "\<exists>l \<in> set M. is_decided l"
          then have False
            using backtrack[of "(M, N)" _ _ _ D ] DN MD assms(2)
              backtrack_split_some_is_decided_then_snd_has_hd[OF l]
            by (metis backtrack_split_snd_hd_decided fst_conv list.distinct(1) list.sel(1) snd_conv)
        }
        ultimately have False by blast
      }
      ultimately show False by blast
     qed
qed


subsection \<open>Termination\<close>

definition "dpll\<^sub>W_mes M n =
  map (\<lambda>l. if is_decided l then 2 else (1::nat)) (rev M) @ replicate (n - length M) 3"

lemma length_dpll\<^sub>W_mes:
  assumes "length M \<le> n"
  shows "length (dpll\<^sub>W_mes M n) = n"
  using assms unfolding dpll\<^sub>W_mes_def by auto

lemma distinctcard_atm_of_lit_of_eq_length:
  assumes "no_dup S"
  shows "card (atm_of ` lits_of_l S) = length S"
  using assms by (induct S) (auto simp add: image_image lits_of_def no_dup_def)

lemma Cons_lexn_iff:
  shows \<open>(x # xs, y # ys) \<in> lexn R n \<longleftrightarrow> (length (x # xs) = n \<and> length (y # ys) = n \<and>
         ((x,y) \<in> R \<or> (x = y \<and> (xs, ys) \<in> lexn R (n - 1))))\<close>
  unfolding lexn_conv apply (rule iffI; clarify)
  subgoal for xys xa ya xs' ys'
    by (cases xys) (auto simp: lexn_conv)
  subgoal by (auto 5 5 simp: lexn_conv simp del: append_Cons simp: append_Cons[symmetric])
  done
declare append_same_lexn[simp] prepend_same_lexn[simp] Cons_lexn_iff[simp]
declare lexn.simps(2)[simp del]

lemma dpll\<^sub>W_card_decrease:
  assumes
    dpll: "dpll\<^sub>W S S'" and
    [simp]: "length (trail S') \<le> card vars" and
    "length (trail S) \<le> card vars"
  shows
    "(dpll\<^sub>W_mes (trail S') (card vars), dpll\<^sub>W_mes (trail S) (card vars)) \<in> lexn less_than (card vars)"
  using assms
proof (induct rule: dpll\<^sub>W.induct)
  case (propagate C L S)
  then have m: "card vars - length (trail S) = Suc (card vars - Suc (length (trail S)))"
    by fastforce
  then show \<open>(dpll\<^sub>W_mes (trail (Propagated C () # trail S, clauses S)) (card vars),
         dpll\<^sub>W_mes (trail S) (card vars)) \<in> lexn less_than (card vars)\<close>
     unfolding dpll\<^sub>W_mes_def by auto
next
  case (decided S L)
  have m: "card vars - length (trail S) = Suc (card vars - Suc (length (trail S)))"
    using decided.prems[simplified] using Suc_diff_le by fastforce
  then show \<open>(dpll\<^sub>W_mes (trail (Decided L # trail S, clauses S)) (card vars),
         dpll\<^sub>W_mes (trail S) (card vars)) \<in> lexn less_than (card vars)\<close>
     unfolding dpll\<^sub>W_mes_def by auto
next
  case (backtrack S M' L M D)
  moreover have S: "trail S = M' @ L # M"
    using backtrack.hyps(1) backtrack_split_list_eq[of "trail S"] by auto
  ultimately show \<open>(dpll\<^sub>W_mes (trail (Propagated (- lit_of L) () # M, clauses S)) (card vars),
         dpll\<^sub>W_mes (trail S) (card vars)) \<in> lexn less_than (card vars)\<close>
    using backtrack_split_list_eq[of "trail S"] unfolding dpll\<^sub>W_mes_def by fastforce
qed

text \<open>\cwref{prop:prop:dpllterminating}{theorem 2.8.7 page 74}\<close>
lemma dpll\<^sub>W_card_decrease':
  assumes dpll: "dpll\<^sub>W S S'"
  and atm_incl: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm (clauses S)"
  and no_dup: "no_dup (trail S)"
  shows "(dpll\<^sub>W_mes (trail S') (card (atms_of_mm (clauses S'))),
          dpll\<^sub>W_mes (trail S) (card (atms_of_mm (clauses S)))) \<in> lex less_than"
proof -
  have "finite (atms_of_mm (clauses S))" unfolding atms_of_ms_def by auto
  then have 1: "length (trail S) \<le> card (atms_of_mm (clauses S))"
    using distinctcard_atm_of_lit_of_eq_length[OF no_dup] atm_incl card_mono by metis

  moreover {
    have no_dup': "no_dup (trail S')" using dpll dpll\<^sub>W_distinct_inv no_dup by blast
    have SS': "clauses S' = clauses S" using dpll by (auto dest!: dpll\<^sub>W_same_clauses)
    have atm_incl': "atm_of ` lits_of_l (trail S') \<subseteq> atms_of_mm (clauses S')"
      using atm_incl dpll dpll\<^sub>W_vars_in_snd_inv[OF dpll] by force
    have "finite (atms_of_mm (clauses S'))"
      unfolding atms_of_ms_def by auto
    then have 2: "length (trail S') \<le> card (atms_of_mm (clauses S))"
      using distinctcard_atm_of_lit_of_eq_length[OF no_dup'] atm_incl' card_mono SS' by metis }

  ultimately have "(dpll\<^sub>W_mes (trail S') (card (atms_of_mm (clauses S))),
      dpll\<^sub>W_mes (trail S) (card (atms_of_mm (clauses S))))
    \<in> lexn less_than (card (atms_of_mm (clauses S)))"
    using dpll\<^sub>W_card_decrease[OF assms(1), of "atms_of_mm (clauses S)"] by blast
  then have "(dpll\<^sub>W_mes (trail S') (card (atms_of_mm (clauses S))),
          dpll\<^sub>W_mes (trail S) (card (atms_of_mm (clauses S)))) \<in> lex less_than"
    unfolding lex_def by auto
  then show "(dpll\<^sub>W_mes (trail S') (card (atms_of_mm (clauses S'))),
         dpll\<^sub>W_mes (trail S) (card (atms_of_mm (clauses S)))) \<in> lex less_than"
    using dpll\<^sub>W_same_clauses[OF assms(1)]  by auto
qed

lemma wf_lexn: "wf (lexn {(a, b). (a::nat) < b} (card (atms_of_mm (clauses S))))"
proof -
  have m: "{(a, b). a < b} = measure id" by auto
  show ?thesis apply (rule wf_lexn) unfolding m by auto
qed

lemma wf_dpll\<^sub>W:
  "wf {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}"
  apply (rule wf_wf_if_measure'[OF wf_lex_less, of _ _
          "\<lambda>S. dpll\<^sub>W_mes (trail S) (card (atms_of_mm (clauses S)))"])
  using dpll\<^sub>W_card_decrease' by fast


lemma dpll\<^sub>W_tranclp_star_commute:
  "{(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}\<^sup>+ = {(S', S). dpll\<^sub>W_all_inv S \<and> tranclp dpll\<^sub>W S S'}"
  (is "?A = ?B")
proof
  { fix S S'
    assume "(S, S') \<in> ?A"
    then have "(S, S') \<in> ?B"
      by (induct rule: trancl.induct, auto)
  }
  then show "?A \<subseteq> ?B" by blast
  { fix S S'
    assume "(S, S') \<in> ?B"
    then have "dpll\<^sub>W\<^sup>+\<^sup>+ S' S" and "dpll\<^sub>W_all_inv S'" by auto
    then have "(S, S') \<in> ?A"
    proof (induct rule: tranclp.induct)
      case r_into_trancl
      then show ?case by (simp_all add: r_into_trancl')
    next
      case (trancl_into_trancl S S' S'')
      then have "(S', S) \<in> {a. case a of (S', S) \<Rightarrow> dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}\<^sup>+" by blast
      moreover have "dpll\<^sub>W_all_inv S'"
        using rtranclp_dpll\<^sub>W_all_inv[OF tranclp_into_rtranclp[OF trancl_into_trancl.hyps(1)]]
          trancl_into_trancl.prems by auto
      ultimately have "(S'', S') \<in> {(pa, p). dpll\<^sub>W_all_inv p \<and> dpll\<^sub>W p pa}\<^sup>+"
        using \<open>dpll\<^sub>W_all_inv S'\<close> trancl_into_trancl.hyps(3) by blast
      then show ?case
        using \<open>(S', S) \<in> {a. case a of (S', S) \<Rightarrow> dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}\<^sup>+\<close> by auto
    qed
  }
  then show "?B \<subseteq> ?A" by blast
qed

lemma wf_dpll\<^sub>W_tranclp: "wf {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W\<^sup>+\<^sup>+ S S'}"
  unfolding dpll\<^sub>W_tranclp_star_commute[symmetric] by (simp add: wf_dpll\<^sub>W wf_trancl)

lemma wf_dpll\<^sub>W_plus:
  "wf {(S', ([], N))| S'. dpll\<^sub>W\<^sup>+\<^sup>+ ([], N) S'}" (is "wf ?P")
  apply (rule wf_subset[OF wf_dpll\<^sub>W_tranclp, of ?P])
  unfolding dpll\<^sub>W_all_inv_def by auto


subsection \<open>Final States\<close>

text \<open>Proposition 2.8.1: final states are the normal forms of @{term dpll\<^sub>W}\<close>
lemma dpll\<^sub>W_no_more_step_is_a_conclusive_state:
  assumes "\<forall>S'. \<not>dpll\<^sub>W S S'"
  shows "conclusive_dpll\<^sub>W_state S"
proof -
  have vars: "\<forall>s \<in> atms_of_mm (clauses S). s \<in> atm_of ` lits_of_l (trail S)"
    proof (rule ccontr)
      assume "\<not> (\<forall>s\<in>atms_of_mm (clauses S). s \<in> atm_of ` lits_of_l (trail S))"
      then obtain L where
        L_in_atms: "L \<in> atms_of_mm (clauses S)" and
        L_notin_trail: "L \<notin> atm_of ` lits_of_l (trail S)" by metis
      obtain L' where L': "atm_of L' = L" by (meson literal.sel(2))
      then have "undefined_lit (trail S) L'"
        unfolding Decided_Propagated_in_iff_in_lits_of_l by (metis L_notin_trail atm_of_uminus imageI)
      then show False using dpll\<^sub>W.decided assms(1) L_in_atms L' by blast
    qed
  show ?thesis
    proof (rule ccontr)
      assume not_final: "\<not> ?thesis"
      then have
        "\<not> trail S \<Turnstile>asm clauses S" and
        "(\<exists>L\<in>set (trail S). is_decided L) \<or> (\<forall>C\<in>#clauses S. \<not>trail S \<Turnstile>as CNot C)"
        unfolding conclusive_dpll\<^sub>W_state_def by auto
      moreover {
        assume "\<exists>L\<in>set (trail S). is_decided L"
        then obtain L M' M where L: "backtrack_split (trail S) = (M', L # M)"
          using backtrack_split_some_is_decided_then_snd_has_hd by blast
        obtain D where "D \<in># clauses S" and "\<not> trail S \<Turnstile>a D"
          using \<open>\<not> trail S \<Turnstile>asm clauses S\<close> unfolding true_annots_def by auto
        then have "\<forall>s\<in>atms_of_ms {D}. s \<in> atm_of ` lits_of_l (trail S)"
          using vars unfolding atms_of_ms_def by auto
        then have "trail S \<Turnstile>as CNot D"
          using all_variables_defined_not_imply_cnot[of D] \<open>\<not> trail S \<Turnstile>a D\<close> by auto
        moreover have "is_decided L"
          using L by (metis backtrack_split_snd_hd_decided list.distinct(1) list.sel(1) snd_conv)
        ultimately have False
          using assms(1) dpll\<^sub>W.backtrack L \<open>D \<in># clauses S\<close> \<open>trail S \<Turnstile>as CNot D\<close> by blast
      }
      moreover {
        assume tr: "\<forall>C\<in>#clauses S. \<not>trail S \<Turnstile>as CNot C"
        obtain C where C_in_cls: "C \<in># clauses S" and trC: "\<not> trail S \<Turnstile>a C"
          using \<open>\<not> trail S \<Turnstile>asm clauses S\<close> unfolding true_annots_def by auto
        have "\<forall>s\<in>atms_of_ms {C}. s \<in> atm_of ` lits_of_l (trail S)"
          using vars \<open>C \<in># clauses S\<close> unfolding atms_of_ms_def by auto
        then have "trail S \<Turnstile>as CNot C"
          by (meson C_in_cls tr trC all_variables_defined_not_imply_cnot)
        then have False using tr C_in_cls by auto
      }
      ultimately show False by blast
    qed
qed

lemma dpll\<^sub>W_conclusive_state_correct:
  assumes "dpll\<^sub>W\<^sup>*\<^sup>* ([], N) (M, N)" and "conclusive_dpll\<^sub>W_state (M, N)"
  shows "M \<Turnstile>asm N \<longleftrightarrow> satisfiable (set_mset N)" (is "?A \<longleftrightarrow> ?B")
proof
  let ?M'= "lits_of_l M"
  assume ?A
  then have "?M' \<Turnstile>sm N" by (simp add: true_annots_true_cls)
  moreover have "consistent_interp ?M'"
    using rtranclp_dpll\<^sub>W_inv_starting_from_0[OF assms(1)] by auto
  ultimately show ?B by auto
next
  assume ?B
  show ?A
  proof (rule ccontr)
    assume n: "\<not> ?A"
    have no_mark: "\<forall>L\<in>set M. \<not> is_decided L" "\<exists>C \<in># N. M \<Turnstile>as CNot C"
      using n assms(2) unfolding conclusive_dpll\<^sub>W_state_def by auto
    moreover obtain D where DN: "D \<in># N" and MD: "M \<Turnstile>as CNot D" using no_mark by auto
    ultimately have "unsatisfiable (set_mset N)"
      using only_propagated_vars_unsat rtranclp_dpll\<^sub>W_all_inv[OF assms(1)]
      unfolding dpll\<^sub>W_all_inv_def by force
    then show False using \<open>?B\<close> by blast
  qed
qed

end
