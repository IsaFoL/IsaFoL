theory Propo_DPLL
imports Main Partial_Clausal_Logic Partial_Annotated_Clausal_Logic List_More

begin

section \<open>DPLL\<close>
subsection \<open>Rules\<close>
datatype dpll_mark = Proped
lemma dpll_mark_only_one_element[simp]:
  "x = Proped" "Proped = x"
  by (case_tac x, simp)+

datatype dpll_marked_level = Level
lemma dpll_marked_level_only_one_element[simp]:
  "x = Level" "Level = x"
  by (case_tac x, simp)+

type_synonym 'a dpll_marked_lit = "('a, dpll_marked_level, dpll_mark) marked_lit"
type_synonym 'a dpll_annoted_lits = "('a, dpll_marked_level, dpll_mark) annoted_lits"
type_synonym 'v dpll_state = "'v dpll_annoted_lits \<times> 'v clauses"

abbreviation trail :: "'v dpll_state \<Rightarrow> 'v dpll_annoted_lits" where
  "trail \<equiv> fst"
abbreviation clauses :: "'v dpll_state \<Rightarrow> 'v clauses" where
 "clauses \<equiv> snd"

inductive dpll :: "'v dpll_state \<Rightarrow> 'v dpll_state \<Rightarrow> bool" where
propagate: "C + {#L#} \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (trail S) \<Longrightarrow> dpll S (Propagated L Proped # trail S, clauses S)" |
decided: "undefined_lit L (trail S) \<Longrightarrow> atm_of L \<in> atms_of_m (clauses S) \<Longrightarrow> dpll S (Marked L Level # trail S, clauses S)" |
backtrack: "backtrack_split (trail S)  = (M', L # M) \<Longrightarrow> is_marked L \<Longrightarrow> D \<in> clauses S \<Longrightarrow> trail S \<Turnstile>as CNot D \<Longrightarrow> dpll S (Propagated (- (lit_of L)) Proped # M, clauses S)"


subsection \<open>Invariants\<close>
lemma dpll_distinctinv:
  assumes "dpll S S'"
  and "no_dup (trail S)"
  shows "no_dup (trail S')"
  using assms
proof (induct rule: dpll.induct)
  case (decided L S)
  thus ?case using defined_lit_map by force
next
  case (propagate C L S)
  thus ?case using defined_lit_map by force
next
  case (backtrack S M' L M D) note extracted = this(1) and no_dup = this(5)
  show ?case
    using no_dup backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted by auto
qed

lemma dpll_consistent_interp_inv:
  assumes "dpll S S'"
  and "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  shows "consistent_interp (lits_of (trail S'))"
  using assms
proof (induct rule: dpll.induct)
  case (backtrack S M' L M D) note extracted = this(1) and marked = this(2) and D = this(4) and
    cons = this(5) and no_dup = this(6)
  have no_dup': "no_dup M"
    by (metis (no_types) backtrack_split_list_eq distinct.simps(2) distinct_append extracted
      list.simps(9) map_append no_dup snd_conv)
  hence "insert (lit_of L) (lits_of M) \<subseteq> lits_of (trail S)"
    using backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted by auto
  hence cons: "consistent_interp (insert (lit_of L) (lits_of M))"
    using consistent_interp_subset cons by blast
  moreover
    have "lit_of L \<notin> lits_of M"
      using no_dup backtrack_split_list_eq[of "trail S", symmetric] extracted
      unfolding lits_of_def by force
  moreover
    have "atm_of (-lit_of L) \<notin> (\<lambda>m. atm_of (lit_of m)) ` set M"
      using no_dup backtrack_split_list_eq[of "trail S", symmetric] unfolding extracted by force
    hence "-lit_of L \<notin> lit_of ` set M"
      by force
    hence "- lit_of L \<notin> (lits_of M)"
      using lits_of_def by blast
  ultimately show ?case by simp
qed (auto intro: consistent_add_undefined_lit_consistent)

lemma dpll_vars_in_snd_inv:
  assumes "dpll S S'"
  and "atm_of ` (set (map lit_of (trail S))) \<subseteq> atms_of_m (clauses S)"
  shows "atm_of ` (set (map lit_of (trail S'))) \<subseteq> atms_of_m (clauses S')"
  using assms
proof (induct rule: dpll.induct)
  case (backtrack S M' L M D)
  hence "atm_of (lit_of L) \<in> atms_of_m (clauses S)"
    using backtrack_split_list_eq[of "trail S", symmetric] by auto
  moreover
    have "atm_of ` lit_of ` set (trail S) \<subseteq> atms_of_m (clauses S)" using backtrack(5) by simp
    then have "\<And>xb. xb \<in> set M \<Longrightarrow> atm_of (lit_of xb) \<in> atms_of_m (clauses S)"
      using backtrack_split_list_eq[symmetric, of "trail S"] backtrack.hyps(1) by auto
  ultimately show ?case by auto
qed (auto simp add: union_commute dest: atms_of_atms_of_m_mono)

lemma atms_of_m_lit_of_atms_of: "atms_of_m ((\<lambda>a. {#lit_of a#}) ` c) = atm_of ` lit_of ` c"
  unfolding atms_of_m_def using image_iff by force

text \<open>Lemma 2.8.2\<close>
lemma dpll_propagate_is_conclusion:
  assumes "dpll S S'"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "atm_of ` lit_of ` set (trail S) \<subseteq> atms_of_m (clauses S)"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  using assms
proof (induct rule: dpll.induct)
  case (decided L S)
  thus ?case unfolding all_decomposition_implies_def by simp
next
  case (propagate C L S) note inS = this(1) and cnot = this(2) and IH = this(4) and undef = this(3) and atms_incl = this(5)
  let ?I = "set (map (\<lambda>a. {#lit_of a#}) (trail S)) \<union> (clauses S) "
  have "?I \<Turnstile>p C + {#L#}" by (auto simp add: inS)
  moreover have "?I \<Turnstile>ps CNot C" using true_annots_true_clss_cls cnot by fastforce
  ultimately have "?I \<Turnstile>p {#L#}" using true_clss_cls_plus_CNot[of ?I C L] inS by blast
  {
    assume "get_all_marked_decomposition (trail S) = []"
    hence ?case by blast
  }
  moreover {
    assume n: "get_all_marked_decomposition (trail S) \<noteq> []"
    have 1: "\<And>a b. (a, b) \<in> set (tl (get_all_marked_decomposition (trail S)))
      \<Longrightarrow> ((\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
      using IH unfolding all_decomposition_implies_def by (fastforce simp add: list.set_sel(2) n)
    moreover have 2: "\<And>a c. hd (get_all_marked_decomposition (trail S)) = (a, c)
      \<Longrightarrow> ((\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S) \<Turnstile>ps ((\<lambda>a. {#lit_of a#}) ` set c)"
      by (metis IH all_decomposition_implies_cons_pair all_decomposition_implies_single list.collapse n)
    moreover have 3: "\<And>a c. hd (get_all_marked_decomposition (trail S)) = (a, c)
      \<Longrightarrow> ((\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S) \<Turnstile>p {#L#}"
      proof -
        fix a c
        assume h: "hd (get_all_marked_decomposition (trail S)) = (a, c)"
        have h': "trail S = c @ a" using get_all_marked_decomposition_decomp h by blast
        have I: "set (map (\<lambda>a. {#lit_of a#})  a) \<union> clauses S \<union> (\<lambda>a. {#lit_of a#}) ` set c
          \<Turnstile>ps CNot C" using \<open>?I \<Turnstile>ps CNot C\<close> unfolding h' by (simp add: Un_commute Un_left_commute)
        have "atms_of_m (CNot C) \<subseteq> atms_of_m (set (map (\<lambda>a. {#lit_of a#}) a) \<union> clauses S)" and
          "atms_of_m ((\<lambda>a. {#lit_of a#}) ` set c) \<subseteq> atms_of_m (set (map (\<lambda>a. {#lit_of a#}) a)
            \<union> clauses S)"
          using inS atms_of_atms_of_m_mono atms_incl  by (fastforce simp add: h')+
        hence "(\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S \<Turnstile>ps CNot C"
          using true_clss_clss_left_right[OF _ I] h "2" by auto
        thus "((\<lambda>a. {#lit_of a#}) ` set a \<union> clauses S) \<Turnstile>p {#L#}"
          using Un_insert_right inS insertI1 mk_disjoint_insert
          by (blast intro: true_clss_cls_in true_clss_cls_plus_CNot)
      qed
    ultimately have ?case
      by (case_tac "hd (get_all_marked_decomposition (trail S))")
         (auto simp add: all_decomposition_implies_def)
  }
  ultimately show ?case by auto
next
  case (backtrack S M' L M D) note extracted = this(1) and marked = this(2) and D = this(3) and
    cnot = this(4) and cons = this(4) and IH = this(5) and atms_incl = this(6)
  have S: "trail S = M' @ L # M"
    using backtrack_split_list_eq[of "trail S"] unfolding extracted by auto
  have M': "\<forall>l \<in> set M'. \<not>is_marked l"
    using extracted backtrack_split_fst_not_marked[of _ "trail S"] by simp
  have n: "get_all_marked_decomposition (trail S) \<noteq> []" by auto
  hence "all_decomposition_implies (clauses S) ((L # M, M')
           # tl (get_all_marked_decomposition (trail S)))"
    by (metis (no_types) IH extracted get_all_marked_decomposition_backtrack_split list.exhaust_sel)
  hence 1: "(\<lambda>a. {#lit_of a#}) ` set (L # M) \<union> clauses S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M'"
    by simp
  moreover
    have "(\<lambda>a. {#lit_of a#}) ` set (L # M) \<union> (\<lambda>a. {#lit_of a#}) ` set M' \<Turnstile>ps CNot D"
      by (metis (mono_tags, lifting) S Un_commute cons image_Un set_append
        true_annots_true_clss_clss)
    hence 2: "(\<lambda>a. {#lit_of a#}) ` set (L # M) \<union> clauses S \<union> (\<lambda>a. {#lit_of a#}) ` set M'
        \<Turnstile>ps CNot D"
      by (metis (no_types, lifting) Un_assoc Un_left_commute true_clss_clss_union_l_r)
  ultimately
    have "set (map (\<lambda>a. {#lit_of a#}) (L # M)) \<union> clauses S \<Turnstile>ps CNot D"
      using true_clss_clss_left_right by fastforce
    hence "set (map (\<lambda>a. {#lit_of a#}) (L # M)) \<union> clauses S \<Turnstile>p {#}"
      using D  by (blast intro: true_clss_clss_contradiction_true_clss_cls_false)
    hence IL: "(\<lambda>a. {#lit_of a#}) ` set M \<union> clauses S \<Turnstile>p {#-lit_of L#}"
      using true_clss_clss_false_left_right by auto
  show ?case unfolding S all_decomposition_implies_def
    proof
      fix x P level
      assume x: "x \<in> set (get_all_marked_decomposition
        (fst (Propagated (- lit_of L) P # M, clauses S)))"
      let ?M' = "Propagated (- lit_of L) P # M"
      let ?hd = "hd (get_all_marked_decomposition ?M')"
      let ?tl = "tl (get_all_marked_decomposition ?M')"
      have "x = ?hd \<or> x \<in> set ?tl"
        using x
        by (cases "get_all_marked_decomposition ?M'")
           auto
      moreover {
        assume x': "x \<in> set ?tl"
        have L': "Marked (lit_of L) Level = L" using marked by (case_tac L, auto)
        have "x \<in> set (get_all_marked_decomposition (M' @ L # M))"
          using x' get_all_marked_decomposition_except_last_choice_equal[of M' "lit_of L" P M Level]
          L' by (metis (no_types) M' list.set_sel(2) tl_Nil)
        hence "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses S
          \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
          using marked IH by (case_tac L) (auto simp add: S all_decomposition_implies_def)
      }
      moreover {
        assume x': "x = ?hd"
        have tl: "tl (get_all_marked_decomposition (M' @ L # M)) \<noteq> []"
          proof -
            have f1: "\<And>ms. length (get_all_marked_decomposition (M' @ ms))
              = length (get_all_marked_decomposition ms)"
              by (simp add: M' get_all_marked_decomposition_remove_unmarked_length)
            have "Suc (length (get_all_marked_decomposition M)) \<noteq> Suc 0"
              by blast
            thus ?thesis
              using f1 marked by (metis (no_types) get_all_marked_decomposition.simps(1) length_tl
                list.sel(3) list.size(3) marked_lit.collapse(1))
          qed
        obtain M0' M0 where
          L0: "hd (tl (get_all_marked_decomposition (M' @ L # M))) = (M0, M0')"
          by (cases "hd (tl (get_all_marked_decomposition (M' @ L # M)))")
        have x'': "x = (M0, Propagated (-lit_of L) P # M0')"
          unfolding x' using get_all_marked_decomposition_last_choice tl M' L0
          by (metis marked marked_lit.collapse(1))
        obtain l_get_all_marked_decomposition where
          "get_all_marked_decomposition (trail S) = (L # M, M') # (M0, M0') # l_get_all_marked_decomposition"
          using get_all_marked_decomposition_backtrack_split extracted by (metis (no_types) L0 S
            hd_Cons_tl n tl)
        hence "M = M0' @ M0" using get_all_marked_decomposition_hd_hd by fastforce
        hence IL':  "(\<lambda>a. {#lit_of a#}) ` set M0 \<union> clauses S \<union> (\<lambda>a. {#lit_of a#}) ` set M0'
          \<Turnstile>ps {{#- lit_of L#}}"
          using IL by (simp add: Un_commute Un_left_commute image_Un)
        moreover have H: "(\<lambda>a. {#lit_of a#}) ` set M0 \<union> clauses S \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set M0'"
          using IH x'' unfolding all_decomposition_implies_def by (metis (no_types, lifting) L0 S
            list.set_sel(1) list.set_sel(2) old.prod.case tl tl_Nil)
        ultimately have "case x of (Ls, seen) \<Rightarrow> (\<lambda>a. {#lit_of a#}) ` set Ls \<union> clauses S
          \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
          using true_clss_clss_left_right unfolding x'' by auto
      }
      ultimately show "case x of (Ls, seen) \<Rightarrow>
        (\<lambda>a. {#lit_of a#}) ` set Ls \<union> snd (?M', clauses S) \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set seen"
        unfolding snd_conv by blast
    qed
qed

theorem dpll_propagate_is_conclusion_of_decided:
  assumes "dpll S S'"
  and "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "atm_of ` lit_of ` set (trail S) \<subseteq> atms_of_m (clauses S)"
  shows "clauses S' \<union> {{#lit_of L#} |L. is_marked L \<and> L \<in> set (trail S')}
    \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` \<Union>(set ` snd ` set (get_all_marked_decomposition (trail S')))"
  using all_decomposition_implies_trail_is_implied[OF dpll_propagate_is_conclusion[OF assms]] .

(*lemma 2.9.4*)
lemma only_propagated_vars_unsat:
  assumes marked: "\<forall>x \<in> set M. \<not> is_marked x"
  and DN: "D \<in> N" and D: "M \<Turnstile>as CNot D"
  and inv: "all_decomposition_implies N (get_all_marked_decomposition M)"
  and atm_incl: "atm_of ` lit_of ` set M  \<subseteq> atms_of_m N"
  shows "unsatisfiable N"
proof (rule ccontr)
  assume "\<not> unsatisfiable N"
  then obtain I where
    I: "I \<Turnstile>s N" and
    cons: "consistent_interp I" and
    tot: "total_over_m I N"
    unfolding satisfiable_def by auto
  hence I_D: "I \<Turnstile> D"
    using DN unfolding true_clss_def by auto

  have l0: "{{#lit_of L#} |L. is_marked L \<and> L \<in> set M} = {}" using marked by auto
  have "atms_of_m (N \<union> (\<lambda>a. {#lit_of a#}) ` set M) = atms_of_m N"
    using atm_incl unfolding atms_of_m_def by auto

  hence "total_over_m I (N \<union> (\<lambda>a. {#lit_of a#}) ` (set M))"
    using tot unfolding total_over_m_def by auto
  hence "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` (set M)"
    using all_decomposition_implies_propagated_lits_are_implied[OF inv] cons I
    unfolding true_clss_clss_def l0 by auto
  hence IM: "I \<Turnstile>s (\<lambda>a. {#lit_of a#}) ` set M" by auto
  {
    fix K
    assume "K \<in># D"
    hence "-K \<in> lits_of M"
      by (auto split: split_if_asm
        intro: allE[OF D[unfolded true_annots_def Ball_def], of "{#-K#}"])
    hence "-K \<in> I" using IM true_clss_singleton_lit_of_implies_incl by fastforce
  }
  hence "\<not> I \<Turnstile> D" using cons unfolding true_cls_def consistent_interp_def by auto
  thus False using I_D by blast
qed

lemma dpll_same_clauses:
  assumes "dpll S S'"
  shows "clauses S = clauses S'"
  using assms by (induct rule: dpll.induct, auto)

lemma dpll_finite_inv:
  assumes dpll: "dpll S S'"
  and fin: "finite (clauses S)"
  shows "finite (clauses S')"
  using assms by (induct rule: dpll.induct, auto)

lemma rtranclp_dpll_inv:
  assumes "rtranclp dpll S S'"
  and inv: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and atm_incl: "atm_of ` lit_of ` (set (trail S))  \<subseteq> atms_of_m (clauses S)"
  and "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "finite (clauses S)"
  shows "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
  and "atm_of ` lit_of ` (set (trail S'))  \<subseteq> atms_of_m (clauses S')"
  and "clauses S = clauses S'"
  and "consistent_interp (lits_of (trail S'))"
  and "no_dup (trail S')"
  and "finite (clauses S')"
  using assms
proof (induct rule: rtranclp.induct)
  case (rtrancl_refl)
  fix S :: "'a dpll_marked_lit list \<times> 'a literal multiset set"
  assume "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "atm_of ` lit_of ` (set (trail S))  \<subseteq> atms_of_m (clauses S)"
  and "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "finite (clauses S)"
  thus "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "atm_of ` lit_of ` set (trail S) \<subseteq> atms_of_m (clauses S)"
  and "clauses S = clauses S"
  and "finite (clauses S)"
  and "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)" by auto
next
  case (rtrancl_into_rtrancl S S' S'') note dpllStar = this(1) and IH = this(2,3,4,5,6,7) and
    dpll = this(8)
  moreover assume inv: "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and atm_incl: "atm_of ` lit_of ` (set (trail S))  \<subseteq> atms_of_m (clauses S)"
  and cons: "consistent_interp (lits_of (trail S))"
  and "no_dup (trail S)"
  and "finite (clauses S)"
  ultimately have decomp: "all_decomposition_implies (clauses S')
    (get_all_marked_decomposition (trail S') )"
  and atm_incl': "atm_of ` lit_of ` set (trail S') \<subseteq> atms_of_m (clauses S')"
  and snd: "clauses S = clauses S'"
  and cons': "consistent_interp (lits_of (trail S'))"
  and no_dup': "no_dup (trail S')"
  and finite': "finite (clauses S')" by blast+
  show "clauses S = clauses S''" using dpll_same_clauses[OF dpll] snd by metis

  show "all_decomposition_implies (clauses S'') (get_all_marked_decomposition (trail S''))"
    using dpll_propagate_is_conclusion[OF dpll] decomp atm_incl' by auto
  show "atm_of ` lit_of ` set (trail S'') \<subseteq> atms_of_m (clauses S'')"
    using dpll_vars_in_snd_inv[OF dpll]  atm_incl atm_incl' by auto
  show "no_dup (trail S'')" using dpll_distinctinv[OF dpll] no_dup' dpll by auto
  show "consistent_interp (lits_of (trail S''))"
    using cons' no_dup' dpll_consistent_interp_inv[OF dpll] by auto
  show "finite (clauses S'')" using dpll_finite_inv[OF dpll] finite' by auto
qed

definition "dpll_all_inv S \<equiv>
  (all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))
  \<and> atm_of ` lit_of ` (set (trail S))  \<subseteq> atms_of_m (clauses S)
  \<and> consistent_interp (lits_of (trail S)) \<and> no_dup (trail S) \<and> finite (clauses S))"

lemma dpll_all_inv_dest[dest]:
  assumes "dpll_all_inv S"
  shows "all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S))"
  and "atm_of ` lit_of ` (set (trail S))  \<subseteq> atms_of_m (clauses S)"
  and "consistent_interp (lits_of (trail S)) \<and> no_dup (trail S)"
  and "finite (clauses S)"
  using assms unfolding dpll_all_inv_def by auto

lemma rtranclp_dpll_all_inv:
  assumes "rtranclp dpll S S'"
  and "dpll_all_inv S"
  shows "dpll_all_inv S'"
  using assms rtranclp_dpll_inv[OF assms(1)] unfolding dpll_all_inv_def by blast

lemma dpll_all_inv:
  assumes "dpll S S'"
  and "dpll_all_inv S"
  shows "dpll_all_inv S'"
  using assms rtranclp_dpll_all_inv by blast

lemma rtranclp_dpll_inv_starting_from_0:
  assumes "rtranclp dpll S S'"
  and inv: "trail S = []"
  and "finite (clauses S)"
  shows "dpll_all_inv S'"
proof -
  have "dpll_all_inv S" using assms unfolding all_decomposition_implies_def dpll_all_inv_def by auto
  thus ?thesis using rtranclp_dpll_all_inv[OF assms(1)] by blast
qed

lemma dpll_can_do_step:
  assumes "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_m N"
  shows "rtranclp dpll ([], N) (map (\<lambda>M. Marked M Level) M, N)"
  using assms
proof (induct M)
  case Nil
  thus ?case by auto
next
  case (Cons L M)
  hence "undefined_lit L (map (\<lambda>M. Marked M Level) M)"
    unfolding defined_lit_def consistent_interp_def by auto
  moreover have "atm_of L \<in> atms_of_m N" using Cons.prems(3) by auto
  ultimately have "dpll (map (\<lambda>M. Marked M Level) M, N) (map (\<lambda>M. Marked M Level) (L # M), N)"
    using dpll.decided by auto
  moreover have "consistent_interp (set M)" and "distinct M" and "atm_of ` set M \<subseteq> atms_of_m N"
    using Cons.prems unfolding consistent_interp_def by auto
  ultimately show ?case using Cons.hyps by auto
qed

definition "final_dpll_state (S:: 'v dpll_state) \<longleftrightarrow>
  (trail S \<Turnstile>as clauses S \<or> ((\<forall>L \<in> set (trail S). \<not>is_marked L)
  \<and> (\<exists>C \<in> clauses S. trail S \<Turnstile>as CNot C)))"

(*Proposition 2.8.6*)
lemma dpll_strong_completeness:
  assumes "set M \<Turnstile>s N"
  and "consistent_interp (set M)"
  and "distinct M"
  and "atm_of ` (set M) \<subseteq> atms_of_m N"
  shows "rtranclp dpll ([], N) (map (\<lambda>M. Marked M Level) M, N)"
  and "final_dpll_state (map (\<lambda>M. Marked M Level) M, N)"
proof -
  show "rtranclp dpll ([], N) (map (\<lambda>M. Marked M Level) M, N)" using dpll_can_do_step assms by auto
  have "map (\<lambda>M. Marked M Level) M \<Turnstile>as N" using assms(1) true_annots_marked_true_cls by auto
  thus "final_dpll_state (map (\<lambda>M. Marked M Level) M, N)" unfolding final_dpll_state_def by auto
qed

(*Proposition 2.8.5*)
lemma dpll_completeness:
  assumes "rtranclp dpll ([], N) (M, N)"
  and "\<forall>S. \<not>dpll (M, N) S"
  and "finite N"
  shows "M \<Turnstile>as N \<longleftrightarrow> satisfiable N" (is "?A \<longleftrightarrow> ?B")
proof
  let ?M'= "lits_of M"
  assume ?A
  hence "?M' \<Turnstile>s N" by (simp add: true_annots_true_cls)
  moreover have "consistent_interp ?M'"
    using rtranclp_dpll_inv_starting_from_0[OF assms(1)] assms(3) by auto
  ultimately show ?B by auto
next
  assume ?B
  show ?A
    proof (rule ccontr)
      assume n: "\<not> ?A"
      have "(\<exists>L. undefined_lit L M \<and> atm_of L \<in> atms_of_m N) \<or> (\<exists>D\<in>N. M \<Turnstile>as CNot D)"
        proof -
          obtain D :: "'a clause" where D: "D \<in> N" and "\<not> M \<Turnstile>a D"
            using n unfolding true_annots_def Ball_def by metis
          hence "(\<exists>L. undefined_lit L M \<and> atm_of L \<in> atms_of D) \<or> M \<Turnstile>as CNot D"
             unfolding true_annots_def Ball_def CNot_def true_annot_def
             using atm_of_lit_in_atms_of true_annot_iff_marked_or_true_lit true_cls_def by blast
          thus ?thesis using D by auto (metis atms_of_atms_of_m_mono subsetCE)
        qed
      moreover {
        assume "\<exists>L. undefined_lit L M \<and> atm_of L \<in> atms_of_m N"
        hence False using assms(2) decided by fastforce
      }
      moreover {
        assume "\<exists>D\<in>N. M \<Turnstile>as CNot D"
        then obtain D where DN: "D \<in> N" and MD: "M \<Turnstile>as CNot D" by metis
        {
          assume "\<forall>l \<in> set M. \<not> is_marked l"
          moreover have "dpll_all_inv ([], N)"
            using assms unfolding all_decomposition_implies_def dpll_all_inv_def by auto
          ultimately have "unsatisfiable N"
            using only_propagated_vars_unsat[of M D N] DN MD rtranclp_dpll_all_inv[OF assms(1)]
            assms(3) by force
          hence False using \<open>?B\<close> by blast
        }
        moreover {
          assume l: "\<exists>l \<in> set M. is_marked l"
          hence False
            using backtrack[of "(M, N)" _ _ _ D ] DN MD assms(2)
              backtrack_split_some_is_marked_then_snd_has_hd[OF l]
            by (metis backtrack_split_snd_hd_marked fst_conv list.distinct(1) list.sel(1) snd_conv)
        }
        ultimately have False by blast
      }
      ultimately show False by blast
     qed
qed

subsection \<open>Termination\<close>
definition "dpll_mes M n =
  map (\<lambda>l. if is_marked l then 2 else (1::nat)) (rev M) @ replicate (n - length M) 3"

lemma length_dpll_mes:
  assumes "length M \<le> n"
  shows "length (dpll_mes M n) = n"
  using assms unfolding dpll_mes_def by auto

lemma distinctcard_atm_of_lit_of_eq_length:
  assumes "no_dup S"
  shows "card (atm_of ` lit_of ` (set S)) = length S"
  using assms by (induct S, auto simp add: image_image)

lemma dpll_card_decrease:
  assumes dpll: "dpll S S'" and "length (trail S') \<le> card vars"
  and "length (trail S) \<le> card vars"
  shows "(dpll_mes (trail S') (card vars), dpll_mes (trail S) (card vars))
    \<in> lexn {(a, b). a < b} (card vars)"
  using assms
proof (induct rule: dpll.induct)
  case (propagate C L S)
  have m: "map (\<lambda>l. if is_marked l then 2 else 1) (rev (trail S))
       @ replicate (card vars - length (trail S)) 3
     =  map (\<lambda>l. if is_marked l then 2 else 1) (rev (trail S)) @ 3
         # replicate (card vars - Suc (length (trail S))) 3"
     using propagate.prems[simplified] using Suc_diff_le by fastforce
  thus ?case
    using propagate.prems(1) unfolding dpll_mes_def by (fastforce simp add: lexn_conv assms(2))
next
  case (decided L S)
  have m: "map (\<lambda>l. if is_marked l then 2 else 1) (rev (trail S))
      @ replicate (card vars - length (trail S)) 3
    =  map (\<lambda>l. if is_marked l then 2 else 1) (rev (trail S)) @ 3
      # replicate (card vars - Suc (length (trail S))) 3"
    using decided.prems[simplified] using Suc_diff_le by fastforce
  thus ?case
    using decided.prems unfolding dpll_mes_def by (force simp add: lexn_conv assms(2))
next
  case (backtrack S M' L M D)
  have L: "is_marked L" using backtrack.hyps(2) by auto
  have S: "trail S = M' @ L # M"
    using backtrack.hyps(1) backtrack_split_list_eq[of "trail S"] by auto
  show ?case
    using backtrack.prems L unfolding dpll_mes_def S by (fastforce simp add: lexn_conv assms(2))
qed


lemma dpll_card_decrease':
  assumes dpll: "dpll S S'"
  and atm_incl: "atm_of ` lit_of ` (set (trail S)) \<subseteq> atms_of_m (clauses S)"
  and no_dup: "no_dup (trail S)"
  and fin: "finite (clauses S)"
  shows "(dpll_mes (trail S') (card (atms_of_m (clauses S'))),
          dpll_mes (trail S) (card (atms_of_m (clauses S)))) \<in> lex {(a, b). a < b}"
proof -
  have "finite (atms_of_m (clauses S))" using fin unfolding atms_of_m_def by auto
  hence 1: "length (trail S) \<le> card (atms_of_m (clauses S))"
    using distinctcard_atm_of_lit_of_eq_length[OF no_dup] atm_incl card_mono by metis

  moreover
    have no_dup': "no_dup (trail S')" using dpll dpll_distinctinv no_dup by blast
    have SS': "clauses S' = clauses S" using dpll dpll_same_clauses by blast
    have atm_incl': "atm_of ` lit_of ` (set (trail S'))  \<subseteq> atms_of_m (clauses S')"
      using atm_incl dpll dpll_vars_in_snd_inv[OF dpll] by force
    have "finite (atms_of_m (clauses S'))"
      using dpll_finite_inv[OF dpll] fin unfolding atms_of_m_def by auto
    hence 2: "length (trail S') \<le> card (atms_of_m (clauses S))"
      using distinctcard_atm_of_lit_of_eq_length[OF no_dup'] atm_incl' card_mono SS' by metis

  ultimately have "(dpll_mes (trail S') (card (atms_of_m (clauses S))),
      dpll_mes (trail S) (card (atms_of_m (clauses S))))
    \<in> lexn {(a, b). a < b} (card (atms_of_m (clauses S)))"
    using dpll_card_decrease[OF assms(1), of "atms_of_m (clauses S)"] by blast
  hence "(dpll_mes (trail S') (card (atms_of_m (clauses S))),
          dpll_mes (trail S) (card (atms_of_m (clauses S)))) \<in> lex {(a, b). a < b}"
    unfolding lex_def by auto
  thus "(dpll_mes (trail S') (card (atms_of_m (clauses S'))),
         dpll_mes (trail S) (card (atms_of_m (clauses S)))) \<in> lex {(a, b). a < b}"
    using dpll_same_clauses[OF assms(1)]  by auto
qed

lemma wf_lexn: "wf (lexn {(a, b). (a::nat) < b} (card (atms_of_m (clauses S))))"
proof -
  have m: "{(a, b). a < b} = measure id" by auto
  show ?thesis apply (rule wf_lexn) unfolding m by auto
qed

lemma dpll_wf:
  "wf {(S', S). dpll_all_inv S \<and> dpll S S'}"
  apply (rule wf_wf_if_measure'[OF wf_lex_less, of _ _
          "\<lambda>S. dpll_mes (trail S) (card (atms_of_m (clauses S)))"])
  using dpll_card_decrease' by fast


lemma dpll_tranclp_star_commute:
  "{(S', S). dpll_all_inv S \<and> dpll S S'}\<^sup>+ = {(S', S). dpll_all_inv S \<and> tranclp dpll S S'}"
    (is "?A = ?B")
proof
  { fix S S'
    assume "(S, S') \<in> ?A"
    hence "(S, S') \<in> ?B"
      by (induct rule: trancl.induct, auto)
  }
  thus "?A \<subseteq> ?B" by blast
  { fix S S'
    assume "(S, S') \<in> ?B"
    hence "dpll\<^sup>+\<^sup>+ S' S" and "dpll_all_inv S'" by auto
    hence "(S, S') \<in> ?A"
      proof (induct rule: tranclp.induct)
        case r_into_trancl
        thus ?case by (simp_all add: r_into_trancl')
      next
        case (trancl_into_trancl S S' S'')
        hence "(S', S) \<in> {a. case a of (S', S) \<Rightarrow> dpll_all_inv S \<and> dpll S S'}\<^sup>+" by blast
        moreover have "dpll_all_inv S'"
          using rtranclp_dpll_all_inv[OF tranclp_into_rtranclp[OF trancl_into_trancl.hyps(1)]]
          trancl_into_trancl.prems by auto
        ultimately have "(S'', S') \<in> {(pa, p). dpll_all_inv p \<and> dpll p pa}\<^sup>+"
          using \<open>dpll_all_inv S'\<close> trancl_into_trancl.hyps(3) by blast
        thus ?case
          using \<open>(S', S) \<in> {a. case a of (S', S) \<Rightarrow> dpll_all_inv S \<and> dpll S S'}\<^sup>+\<close> by auto
      qed
   }
  thus "?B \<subseteq> ?A" by blast
qed

lemma dpll_wf_tranclp: "wf {(S', S). dpll_all_inv S \<and> dpll\<^sup>+\<^sup>+ S S'}"
  unfolding dpll_tranclp_star_commute[symmetric] by (simp add: dpll_wf wf_trancl)

lemma dpll_wf_plus:
  assumes "finite N"
  shows "wf {(S', ([], N))| S'. dpll\<^sup>+\<^sup>+ ([], N) S'}"  (is "wf ?P")
  apply (rule wf_subset[OF dpll_wf_tranclp, of ?P])
  using assms unfolding dpll_all_inv_def by auto


subsection \<open>Final States\<close>
(*Proposition 2.8.1: final states are the normal forms of @{term dpll}*)
lemma dpll_no_more_step_is_a_final_state:
  assumes "\<forall>S'. \<not>dpll S S'"
  shows "final_dpll_state S"
proof -
  have vars: "\<forall>s \<in> atms_of_m (clauses S). s \<in> atm_of ` lit_of ` (set (trail S))"
    proof (rule ccontr)
      assume "\<not> (\<forall>s\<in>atms_of_m (clauses S). s \<in> atm_of ` lit_of ` set (trail S))"
      then obtain L where
        L_in_atms: "L \<in> atms_of_m (clauses S)" and
        L_notin_trail: "L \<notin> atm_of ` lit_of ` set (trail S)" by metis
      obtain L' where L': "atm_of L' = L" by (meson literal.sel(2))
      hence "undefined_lit L' (trail S)"
        unfolding Marked_Propagated_in_iff_in_lits_of lits_of_def
        by (metis L_notin_trail atm_of_uminus imageI)
      thus False using dpll.decided assms(1) L_in_atms L' by blast
    qed
  show ?thesis
    proof (rule ccontr)
      assume not_final: "\<not> ?thesis"
      hence
        "\<not> trail S \<Turnstile>as clauses S" and
        "(\<exists>L\<in>set (trail S). is_marked L) \<or> (\<forall>C\<in>clauses S. \<not>trail S \<Turnstile>as CNot C)"
        unfolding final_dpll_state_def by auto
      moreover {
        assume "(\<exists>L\<in>set (trail S). is_marked L)"
        then obtain L M' M where L: "backtrack_split (trail S) = (M', L # M)"
          using backtrack_split_some_is_marked_then_snd_has_hd by blast
        obtain D where "D \<in> clauses S" and "\<not> trail S \<Turnstile>a D"
          using \<open>\<not> trail S \<Turnstile>as clauses S\<close> unfolding true_annots_def by auto
        hence "\<forall>s\<in>atms_of_m {D}. s \<in> atm_of ` lit_of ` set (trail S)"
          using vars unfolding atms_of_m_def by blast
        hence "trail S \<Turnstile>as CNot D"
          using all_variables_defined_not_imply_cnot[of D] \<open>\<not> trail S \<Turnstile>a D\<close> by auto
        moreover have "is_marked L"
          using L by (metis backtrack_split_snd_hd_marked list.distinct(1) list.sel(1) snd_conv)
        ultimately have False
          using assms(1) dpll.backtrack L \<open>D \<in> clauses S\<close> \<open>trail S \<Turnstile>as CNot D\<close> by blast
      }
      moreover {
        assume tr: "\<forall>C\<in>clauses S. \<not>trail S \<Turnstile>as CNot C"
        obtain C where C_in_cls: "C \<in> clauses S" and trC: "\<not> trail S \<Turnstile>a C"
          using \<open>\<not> trail S \<Turnstile>as clauses S\<close> unfolding true_annots_def by blast
        have "\<forall>s\<in>atms_of_m {C}. s \<in> atm_of ` lit_of ` set (trail S)"
          using vars \<open>C \<in> clauses S\<close> unfolding atms_of_m_def by blast
        hence "trail S \<Turnstile>as CNot C"
          by (meson C_in_cls tr trC all_variables_defined_not_imply_cnot)
        hence False using tr C_in_cls by auto
      }
      ultimately show False by blast
    qed
qed

lemma dpll_completeness':
  assumes "rtranclp dpll ([], N) (M, N)"
  and "final_dpll_state (M, N)"
  and "finite N"
  shows "M \<Turnstile>as N \<longleftrightarrow> satisfiable N" (is "?A \<longleftrightarrow> ?B")
proof
  let ?M'= "lits_of M"
  assume ?A
  hence "?M' \<Turnstile>s N" by (simp add: true_annots_true_cls)
  moreover have "consistent_interp ?M'"
    using rtranclp_dpll_inv_starting_from_0[OF assms(1)] assms(3) by auto
  ultimately show ?B by auto
next
  assume ?B
  show ?A
    proof (rule ccontr)
      assume n: "\<not> ?A"
      have no_mark: "\<forall>L\<in>set M. \<not> is_marked L"  "\<exists>C \<in> N. M \<Turnstile>as CNot C"
        using n assms(2) unfolding final_dpll_state_def by auto
      moreover obtain D where DN: "D \<in> N" and MD: "M \<Turnstile>as CNot D" using no_mark by metis
      ultimately have "unsatisfiable N"
        using only_propagated_vars_unsat rtranclp_dpll_all_inv[OF assms(1)] assms(3)
        unfolding dpll_all_inv_def by force
      thus False using \<open>?B\<close> by blast
    qed
qed

end
