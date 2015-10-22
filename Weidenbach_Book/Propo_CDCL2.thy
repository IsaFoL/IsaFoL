theory Propo_CDCL2
imports Partial_Annotated_Clausal_Logic List_More "../Bachmair_Ganzinger/Lazy_List_Limit"

begin
sledgehammer_params[verbose] 

type_synonym ('v, 'lvl, 'mark) cdcl_state = "('v, 'lvl, 'mark) annoted_lits \<times> 'v clauses"

inductive propagate :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
propagate[intro]: "C + {#L#} \<in> N \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L M
  \<Longrightarrow> propagate (M, N) ((Propagated L mark) # M, N)"

inductive_cases propagateE[elim]: "propagate S T"
thm propagateE

inductive decide ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
decide[intro]: "undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N \<Longrightarrow> decide (M, N) (Marked L d # M, N)"

inductive_cases decideE[elim]: "decide S S'"

inductive backjump  ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
backjump: "C \<in> N \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C
  \<Longrightarrow> undefined_lit L (F' @ Marked K d # F) \<Longrightarrow> atm_of L \<in> atms_of_m N
  \<Longrightarrow> N \<Turnstile>p {#L#} + C'
  \<Longrightarrow> backjump (F' @ Marked K d # F, N) (Propagated L l #  F, N)"
inductive_cases backjumpE[elim]: "backjump S S'"

text \<open>We define dpll with backjumping:\<close>
inductive dpll :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
bj_decide:  "decide S S' \<Longrightarrow> dpll S S'" |
bj_propagate: "propagate S S' \<Longrightarrow> dpll S S'" |
bj_backjump:  "backjump S S' \<Longrightarrow> dpll S S'"

lemmas dpll_induct = dpll.induct[split_format(complete)]
lemma dpll_all_induct[consumes 1, case_names decide propagate backjump]:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits" and N ::" 'v clauses"
  assumes "dpll (M, N) (M', N')" and
  "\<And>L M N d. undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N \<Longrightarrow> P M N (Marked L d # M) N" and
  "\<And>C L N M mark. C + {#L#} \<in> N \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L M
    \<Longrightarrow> P M N ((Propagated L mark) # M) N" and
  "\<And>C N F' K d F L C' l. C \<in> N \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C
    \<Longrightarrow> undefined_lit L (F' @ Marked K d # F)
  \<Longrightarrow> atm_of L \<in> atms_of_m N
  \<Longrightarrow> N \<Turnstile>p {#L#} + C'
  \<Longrightarrow> P (F' @ Marked K d # F) N (Propagated L l #  F) N"
  shows "P M N M' N'"
  using assms(1) by (induction rule: dpll_induct) (auto dest!: assms(2,3,4))


inductive learn  ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
learn: "N \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m N \<Longrightarrow> learn (M, N) (M, insert C N)"
inductive_cases learnE[elim]: "learn S S'"

inductive forget :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
forget: "N - {C} \<Turnstile>p C \<Longrightarrow> C \<in> N \<Longrightarrow> forget (M, N) (M, N - {C})"
inductive_cases forgetE[elim]: "forget S S'"

inductive learn_or_forget:: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
lf_learn:  "learn S S' \<Longrightarrow> learn_or_forget S S'" |
lf_forget:  "forget S S' \<Longrightarrow> learn_or_forget S S'"
inductive_cases learn_or_forgetE[elim]: "learn_or_forget S S'"
declare learn_or_forget.intros[intro]

inductive cdcl:: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
c_dpll:  "dpll S S' \<Longrightarrow> cdcl S S'" |
c_learn:  "learn S S' \<Longrightarrow> cdcl S S'" |
c_forget:  "forget S S' \<Longrightarrow> cdcl S S'"

lemmas cdcl_induct = cdcl.induct[split_format(complete)]
lemma cdcl_all_induct[consumes 1, case_names dpll learn forget]:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits" and N ::" 'v clauses"
  assumes "cdcl (M, N) (M', N')" and
  "\<And>M N M' N'. dpll (M, N) (M', N') \<Longrightarrow> P M N M' N'" and
  learn: "\<And>M N C. N \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m N \<Longrightarrow>  P M N M (insert C N)" and
  "\<And>M N C. N - {C} \<Turnstile>p C \<Longrightarrow> C \<in> N \<Longrightarrow>  P M N M (N - {C})"
  shows "P M N M' N'"
  using assms(1) by (induction rule: cdcl_induct)
    (auto intro!: learn dest!: assms(2,3,4))



lemma dpll_no_dup:
  assumes "dpll (M, N) (M', N')"
  and "no_dup M"
  shows "no_dup M'"
  using assms by (induction rule: dpll_all_induct) (auto simp add: defined_lit_map)

lemma cdcl_no_dup:
  assumes "cdcl (M, N) (M', N')"
  and "no_dup M"
  shows "no_dup M'"
  using assms by (induction rule: cdcl_all_induct) (auto intro: dpll_no_dup)

lemma cdcl_consistent:
  assumes "cdcl (M, N) (M', N')"
  and "no_dup M"
  shows "consistent_interp (lits_of M')"
  using cdcl_no_dup[OF assms] distinctconsistent_interp by fast

lemma dpll_sat_iff:
  assumes "dpll (M, N) (M', N')"
  shows "I \<Turnstile>s N \<longleftrightarrow> I \<Turnstile>s N'"
  using assms by (induction rule: dpll_all_induct) auto

(*TODO Move*)
lemma total_over_set_in_total:
  "total_over_set I (atms_of_m N) \<Longrightarrow> C : N \<Longrightarrow> total_over_set I (atms_of C)"
  unfolding total_over_set_def atms_of_m_def by fastforce

lemma cdcl_sat_iff:
  assumes "cdcl (M, N) (M', N')"
  and "consistent_interp I" and "total_over_m I N"
  shows "I \<Turnstile>s N \<longleftrightarrow> I \<Turnstile>s N'"
  using assms apply (induction rule: cdcl_all_induct)
     using dpll_sat_iff apply blast
    unfolding true_clss_cls_def total_over_m_def apply (metis atms_of_m_singleton atms_of_m_union
      sup.orderE true_clss_insert)
  unfolding true_clss_insert atms_of_m_singleton atms_of_m_union by (metis atms_of_m_insert
    insert_Diff total_over_set_union true_clss_insert)


lemma dpll_atms_of_m_clauses_inv:
  assumes "dpll (M, N) (M', N')"
  shows "atms_of_m N = atms_of_m N'"
  using assms by (induction rule: dpll_all_induct) auto

lemma dpll_atms_of_m_clauses_decreasing:
  assumes "cdcl (M, N) (M', N')"
  shows "atms_of_m N' \<subseteq> atms_of_m N"
  using assms by (induction rule: cdcl_all_induct)
    (auto dest!: dpll_atms_of_m_clauses_inv simp add: atms_of_m_def)

lemma dpll_atms_in_trail:
  assumes "dpll (M, N) (M', N')"
  and "atm_of ` (lits_of M) \<subseteq> atms_of_m N"
  shows "atm_of ` (lits_of M') \<subseteq> atms_of_m N'"
  using assms by (induction rule: dpll_all_induct) auto

lemma dpll_atms_in_trail_in_set:
  assumes "dpll (M, N) (M', N')" and
  "atms_of_m N \<subseteq> A" and
  "atm_of ` (lits_of M) \<subseteq> A"
  shows "atm_of ` (lits_of M') \<subseteq> A"
  using assms by (induction rule: dpll_all_induct) auto

lemma cdcl_atms_in_trail:
  assumes "cdcl (M, N) (M', N')"
  and "atm_of ` (lits_of M) \<subseteq> atms_of_m N"
  shows "atm_of ` (lits_of M') \<subseteq> atms_of_m N"
  using assms
  by (induction rule: cdcl_all_induct)
     (simp_all add: dpll_atms_in_trail dpll_atms_of_m_clauses_inv)


lemma cdcl_atms_in_trail_in_set:
  assumes "cdcl (M, N) (M', N')" and
  "atms_of_m N \<subseteq> A" and
  "atm_of ` (lits_of M) \<subseteq> A"
  shows "atm_of ` (lits_of M') \<subseteq> A"
  using assms
  by (induction rule: cdcl_all_induct)
     (simp_all add: dpll_atms_in_trail_in_set dpll_atms_of_m_clauses_inv)

subsection \<open>Measure\<close>
subsection\<open>Adding the measure based on Nieuwenhuis et al.\<close>
text \<open>The idea is to measure the \<^emph>\<open>progress\<close> of the proof: we are measuring how many literals are
  unassigned, either locally (i.e. comparing the number of proagated literals between two decisions)
  or globally.\<close>
abbreviation unassigned_lit ::  "'b literal multiset set \<Rightarrow> 'a list \<Rightarrow> nat" where
  "unassigned_lit N M \<equiv> card (atms_of_m N) - length M"

abbreviation "trail_mes_l N M M' \<equiv> ((\<exists>M''. M = M' @ M'' \<and> unassigned_lit N M < unassigned_lit N M'))"

abbreviation "full_trail_mes N M M' \<equiv> (trail_mes_l N M M' \<or> trail_mes_l N M' M)"


lemma wf_distinct_bounded_list_length_decreasing:
  assumes "\<And>M. P M \<Longrightarrow> distinct M \<and> set M \<subseteq> A"
  and "finite A"
  shows "wf {(M', M). length M' > length M \<and> P M \<and> P M'}"
  by (rule wf_bounded_measure[of _ "\<lambda>_. card A" length])
     (metis (mono_tags, lifting) card_mono distinct_card assms mem_Collect_eq order_refl case_prodD)


lemma all_bounded_list_finite:
  "finite {U::nat list. length U < p \<and> (\<forall>n\<in>set U. n < m)}" (is "finite ?U")
proof (induction p)
  case 0
  thus ?case by auto
next
  case (Suc p) note IH = this
  have U: "{U. length U < Suc p \<and> (\<forall>na\<in>set U. na < m)}
    \<subseteq> {n # U| n U. length U < p \<and> (\<forall>na\<in>set (n # U). na < m)}
    \<union> {[]}" (is "?U \<subseteq> ?U1 \<union> ?U2")
    proof
      fix U
      assume "U \<in> ?U"
      hence dist: "length U < Suc p" and u: "\<forall>na\<in>set U. na < m" by auto
      show "U \<in> ?U1 \<union> ?U2"
        proof (cases U)
          case Nil
          thus ?thesis by auto
        next
          case (Cons n Y) note U = this(1)
          show ?thesis
            using dist u unfolding U by auto
        qed
    qed
  have "?U1 \<subseteq> (case_prod Cons) ` ({n. n < m} \<times> {U. length U < p \<and> (\<forall>na\<in>set U. na < m)})" by auto
  moreover
    have "finite {n. n < m}" and
      "finite {U. length U < p \<and> (\<forall>na\<in>set U. na < m)}" using IH by auto
  ultimately have "finite ?U1" by (simp add: finite_subset)
  thus ?case using U IH by (simp add: finite_subset)
qed

abbreviation all_bounded_list :: "nat \<Rightarrow> nat \<Rightarrow> (nat list \<times> nat list) set" where
"all_bounded_list m p \<equiv>
  {(T, S). ((length S < p \<and> (\<forall>n \<in> set S. n < m)) \<and> (length T < p \<and> (\<forall>n \<in> set T. n < m)))
    \<and> (T, S) \<in> lexord less_than}"

lemma wf_bounded_distinct_lexord:
  "wf(all_bounded_list m p)"
  by (rule lexord_on_finite_set_is_wf[of _ "{U::nat list. length U < p \<and> (\<forall>n\<in>set U. n < m)}"])
     (auto simp add: all_bounded_list_finite)


definition all_bounded_list_different :: "nat \<Rightarrow> nat \<Rightarrow> ((nat list \<times> 'a) \<times> nat list \<times> 'b) set" where
"all_bounded_list_different m p \<equiv>
  {((T, u), (S, y)). ((length S \<le> p \<and> (\<forall>n \<in> set S. n \<le> m)) \<and> (length T \<le> p \<and> (\<forall>n \<in> set T. n \<le> m)))
     \<and> \<not>(\<exists>S'. T = S @ S') \<and> (T, S) \<in> lexord less_than}"

definition fst_same_beginning_snd_decreasing ::
  "'c::ord \<Rightarrow> nat \<Rightarrow> (('c list \<times> nat) \<times> ('c list \<times> nat)) set" where
"fst_same_beginning_snd_decreasing m p \<equiv>
  {((a, b),(c, d)). ((length a \<le> p \<and> (\<forall>n \<in> set a. n \<le> m)) \<and> (length c \<le> p \<and> (\<forall>n \<in> set c. n \<le> m)))
     \<and> b < d \<and> a = c @ [m]}"

lemma all_bounded_list_different_increasing:
  "p' \<ge> p \<Longrightarrow> m' \<ge> m \<Longrightarrow> all_bounded_list_different p m \<subseteq> all_bounded_list_different p' m'"
  by (auto simp add: all_bounded_list_different_def)

lemma wf_bounded_distinct_different_lexord:
  "wf (all_bounded_list_different m p)"
  unfolding all_bounded_list_different_def
  apply (rule wf_fst_wf_pair)
  by (rule wf_subset[OF wf_bounded_distinct_lexord[of "Suc p" "Suc m"]]) auto

lemma wf_trail_mes_l_bounded:
  assumes H: "\<And>M. P M \<Longrightarrow> distinct M \<and> set M \<subseteq> A"
  shows "wf {(M', M). trail_mes_l A M' M \<and> P M \<and> P M'}"
  by (insert wf_measure[of "unassigned_lit A"])
     (auto dest!: assms intro: wf_subset simp add: measure_def inv_image_def less_than_def less_eq)

lemma wf_fst_same_beginning_snd_decreasing:
  "wf (fst_same_beginning_snd_decreasing p m)"
proof -
  have "wf {((a, b::nat),(c, d)). b < d}"
    by (rule wf_snd_wf_pair) (rule Wellfounded.wf_less)
  thus ?thesis
    by (rule wf_subset) (auto simp add: fst_same_beginning_snd_decreasing_def)
qed
(*
lemma fst_same_beginning_snd_decreasing_all_bounded_list_different_disj:
  "fst_same_beginning_snd_decreasing r s \<inter> all_bounded_list_different m p = {}"
  by auto
 *)
thm wf_union_compatible
text \<open>

  \<^item>@{thm wf_union_compatible} \<^emph>\<open>cannot\<close> be applied: @{term "R O S \<subseteq> R"} does not hold.

  For a decide @{term "[]"} to @{term "Marked K 1"} and propagate @{term "[Marked K 1]"} to
  @{term "Propagated L P # Marked K 1 # []"},  but the composition is not in the lexicographic
  ordering.


  \<^item> @{thm wf_Un} \<^emph>\<open>cannot\<close> be applied because the domain are not disjoint.
  \<close>
lemma "wf (fst_same_beginning_snd_decreasing n p \<union> all_bounded_list_different n p)" (is "wf (?F\<union>?B)")
oops

fun trail_mes ::  "'v literal multiset set \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> nat list" where
"trail_mes A (M, N) =
  (map (unassigned_lit A o snd) (rev (get_all_marked_decomposition M)))"

lemma length_get_all_marked_decomposition_append_Marked:
  "length (get_all_marked_decomposition (F' @ Marked K d # F)) =
    length (get_all_marked_decomposition F')
    + length (get_all_marked_decomposition (Marked K d # F))
    - 1"
    by (induction F' rule: marked_lit_list_induct) auto

lemma take_length_get_all_marked_decomposition_marked_sandwich:
  "take (length (get_all_marked_decomposition F))
      (map (f o snd) (rev (get_all_marked_decomposition (F' @ Marked K d # F))))
      =
     map (f o snd) (rev (get_all_marked_decomposition F))
    "
proof (induction F' rule: marked_lit_list_induct)
  case nil
  thus ?case by auto
next
  case (marked K)
  thus ?case by (simp add: length_get_all_marked_decomposition_append_Marked)
next
  case (proped L m F') note IH = this(1)
  obtain a b l where F': "get_all_marked_decomposition (F' @ Marked K d # F) = (a, b) # l"
    by (cases "get_all_marked_decomposition (F' @ Marked K d # F)") auto
  have "length (get_all_marked_decomposition F) - length l = 0"
    using length_get_all_marked_decomposition_append_Marked[of F' K d F]
    unfolding F' by (cases "get_all_marked_decomposition F'") auto
  thus ?case
    using IH by (simp add: F')
qed

lemma length_get_all_marked_decomposition_length:
  "length (get_all_marked_decomposition M) \<le> 1 + length M"
  by (induction M rule: marked_lit_list_induct) auto

lemma tl_get_all_marked_append_marked_not_nil:
  "tl (get_all_marked_decomposition (xs @ [Marked K d])) \<noteq> []"
  by (induction xs rule: marked_lit_list_induct) auto

lemma last_tl_get_all_marked_decomposition_propagated_tl:
  "last (tl (get_all_marked_decomposition (xs @ [Marked K d]))) =
    last (get_all_marked_decomposition (xs @ [Marked K d]))"
  by (induction xs rule: marked_lit_list_induct)
     (simp_all add: tl_get_all_marked_append_marked_not_nil)

lemma last_get_all_marked_decomposition_propagated_empty:
  "last (get_all_marked_decomposition (xs @ [Marked K d])) = ([], [])"
  by (induction xs rule: marked_lit_list_induct)
     (auto simp add: tl_get_all_marked_append_marked_not_nil
       last_tl_get_all_marked_decomposition_propagated_tl)

lemma "tl (map snd (butlast (get_all_marked_decomposition (xs @ [Marked K d]))))
  = map snd (butlast (tl (get_all_marked_decomposition (xs @ [Marked K d])))) "
  by (cases "get_all_marked_decomposition (xs @ [Marked K d])") auto

lemma butlast_get_all_marked_decomposition_append_marked[simp]:
  "butlast (get_all_marked_decomposition (F' @ [Marked K d])) \<noteq> []"
  by (metis append_Nil get_all_marked_decomposition_never_empty list.sel(3) snoc_eq_iff_butlast
    tl_get_all_marked_append_marked_not_nil)


lemma map_snd_get_all_marked_decomposition_marked:
  "map snd (get_all_marked_decomposition (F' @ Marked K d # F))  =
    map snd (butlast (get_all_marked_decomposition (F' @ [Marked K d]) )
    @ (get_all_marked_decomposition F))"
proof (induction F' rule: marked_lit_list_induct)
  case nil thus ?case by simp
next
  case marked
  thus ?case by simp
next
  case (proped L m F') note IH = this(1)
  have [simp]: "map snd (butlast (tl (get_all_marked_decomposition (F' @ [Marked K d]))))
    = tl (map snd (butlast (get_all_marked_decomposition (F' @ [Marked K d]))))"
    by (cases "get_all_marked_decomposition (F' @ [Marked K d])") auto
  have [simp]: "snd (hd (get_all_marked_decomposition (F' @ Marked K d # F)))
    = snd (hd (get_all_marked_decomposition (F' @ [Marked K d])))"
    by (smt append_butlast_last_id append_is_Nil_conv append_self_conv2
      get_all_marked_decomposition_never_empty hd_append list.collapse list.inject list.map_sel(1)
      proped.IH tl_get_all_marked_append_marked_not_nil)

  obtain a b l where F: "get_all_marked_decomposition (F' @ Marked K d # F) = (a, b) # l"
    by (cases "get_all_marked_decomposition (F' @ Marked K d # F)") auto
  thus ?case unfolding F
    by (auto simp add: map_tl tl_get_all_marked_append_marked_not_nil IH arg_cong[OF IH, of tl]
      tl_append dest!: arg_cong[of "_#_" _ hd] split: list.split)
qed

lemma map_unassigned_lit_pair_map_unassigned_lit_map_snd:
  "map (unassigned_lit A o snd) l = map (unassigned_lit A) (map snd l)"
 by (fastforce simp: o_def )

abbreviation cut_to_shortest :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'a list \<times> 'b list" where
"cut_to_shortest l l' \<equiv>
  (take (min (length l) (length l')) l, take (min (length l) (length l')) l')"
lemma take_to_drop: "take a l = l' \<Longrightarrow> l = l' @ drop a l"
  by auto

abbreviation trail_mes_build where
"trail_mes_build \<equiv> \<lambda>A (M, N) (M', N').
  (let (a, b) = cut_to_shortest (trail_mes A (M, N)) (trail_mes A (M', N)) in
    ((a, unassigned_lit A M),  (b, unassigned_lit A M')))"

lemma dpll_trail_mes_decreasing:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits " and N :: "'v clauses"
  assumes "dpll (M, N) (M', N')" and
  "atms_of_m N \<subseteq> atms_of_m A" and
  "atm_of ` lits_of M \<subseteq> atms_of_m A" and
  "no_dup M" and
  finite: "finite A"
  shows "trail_mes_build A (M', N') (M, N) \<in> lexord less_than <*lex*> less_than"
  using assms
proof (induction rule: dpll_all_induct)
  case (propagate C L N M d) note CLN = this(1) and MC =this(2) and undef_L = this(3) and
    A = this(4) and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L d # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_propagate propagate.propagate[OF propagate.hyps] A MA
    by blast

  have no_dup: "no_dup (Propagated L d # M)"
    using defined_lit_map propagate.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Propagated L d # M) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by force
  thus ?case
    by (auto simp: lexord_def lex_conv latm M)
next
  case (decide L M N lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4)
    and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Marked L lv # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_decide decide.decide[OF decide.hyps] A MA  NA by blast

  have no_dup: "no_dup (Marked L lv # M)"
    using defined_lit_map decide.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Marked L lv # M) \<le> card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A M = Suc (unassigned_lit A (Marked L lv # M))"
    using b_le_M by force
  show ?case by (auto simp add: latm)
next
  case (backjump C N F' K d F L _ lv) note undef_L = this(1) and MC =this(2) and NA = this(3)
    and A = this(4) and MA = this(5) and nd = this(8)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L lv # F) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set backjump.hyps(4) backjump.prems(1) backjump.prems(2) by auto

  have no_dup: "no_dup (Propagated L lv # F)"
    using bj_backjump backjump.backjump[OF backjump.hyps] dpll_no_dup nd by blast
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence F_le_A: "length (Propagated L lv # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)

  have min: "min ((length (get_all_marked_decomposition F)))
                 (length (get_all_marked_decomposition (F' @ Marked K d # F)))
             = length (get_all_marked_decomposition F)"
    unfolding length_get_all_marked_decomposition_append_Marked by (simp add: min_def)

  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
   by (cases "get_all_marked_decomposition F") auto

  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L lv # F" a "Propagated L lv # b"]
      by simp
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L lv # b))"
     using F_le_A by simp
  show ?case
    apply (simp add: min)
    using take_length_get_all_marked_decomposition_marked_sandwich[of F "unassigned_lit A" F' K d]
    by (auto simp add: F latm lexord_def lex_conv)
qed

subsection \<open>A slightly different presentation of the invariant: we complete the list instead of 
  taking only some of the elements\<close>
abbreviation complete_list_to_size where
"complete_list_to_size s n l \<equiv> l @ replicate (s - length l) n"

lemma dpll_trail_mes_decreasing2:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits " and N :: "'v clauses"
  assumes "dpll (M, N) (M', N')" and
  "atms_of_m N \<subseteq> atms_of_m A" and
  "atm_of ` lits_of M \<subseteq> atms_of_m A" and
  "no_dup M" and
  finite: "finite A"
  shows "(complete_list_to_size (2 + card (atms_of_m A)) (card (atms_of_m A)) (trail_mes A (M', N'))
            @ [unassigned_lit A M'],
          complete_list_to_size (2 + card (atms_of_m A)) (card (atms_of_m A)) (trail_mes A (M, N))
            @ [unassigned_lit A M])
          \<in> lexord less_than"
  using assms
proof (induction rule: dpll_all_induct)
  case (propagate C L N M d) note CLN = this(1) and MC =this(2) and undef_L = this(3) and
    A = this(4) and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L d # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_propagate propagate.propagate[OF propagate.hyps] A MA
    by blast

  have no_dup: "no_dup (Propagated L d # M)"
    using defined_lit_map propagate.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Propagated L d # M) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by force
  thus ?case
    by (auto simp: lexord_def lex_conv latm M)
next
  case (decide L M N lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4)
    and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Marked L lv # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_decide decide.decide[OF decide.hyps] A MA  NA by blast

  have no_dup: "no_dup (Marked L lv # M)"
    using defined_lit_map decide.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence length_M_A: "length (Marked L lv # M) \<le> card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A M = Suc (unassigned_lit A (Marked L lv # M))"
    using b_le_M by force
  have rep: "replicate (Suc (Suc (card (atms_of_m A))) - length (get_all_marked_decomposition M)) 
                  (card (atms_of_m A)) =
        card (atms_of_m A) # replicate (Suc (card (atms_of_m A)) - length (get_all_marked_decomposition M)) 
                  (card (atms_of_m A))"
    using length_get_all_marked_decomposition_length[of M] length_M_A
    by (cases "Suc (Suc (card (atms_of_m A))) - length (get_all_marked_decomposition M)") auto
  hence c: "complete_list_to_size (2 + card (atms_of_m A)) (card (atms_of_m A)) (trail_mes A (Marked L lv # M, N)) 
    = complete_list_to_size (2 + card (atms_of_m A)) (card (atms_of_m A)) (trail_mes A (M, N))" 
      by (auto simp add: rep)
  show ?case unfolding latm lexord_def c by blast
next
  case (backjump C N F' K d F L _ lv) note undef_L = this(1) and MC =this(2) and NA = this(3)
    and A = this(4) and MA = this(5) and nd = this(8)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L lv # F) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set backjump.hyps(4) backjump.prems(1) backjump.prems(2) by auto

  have no_dup: "no_dup (Propagated L lv # F)"
    using bj_backjump backjump.backjump[OF backjump.hyps] dpll_no_dup nd by blast
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence F_le_A: "length (Propagated L lv # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)

  have min: "min ((length (get_all_marked_decomposition F)))
                 (length (get_all_marked_decomposition (F' @ Marked K d # F)))
             = length (get_all_marked_decomposition F)"
    unfolding length_get_all_marked_decomposition_append_Marked by (simp add: min_def)

  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
   by (cases "get_all_marked_decomposition F") auto

  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L lv # F" a "Propagated L lv # b"]
      by simp
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L lv # b))"
     using F_le_A by simp
  obtain rem where
    rem:"(map (unassigned_lit A \<circ> snd) (rev (get_all_marked_decomposition (F' @ Marked K d # F)))) 
    = map (unassigned_lit A \<circ> snd) (rev (get_all_marked_decomposition F)) @ rem"
    using take_length_get_all_marked_decomposition_marked_sandwich[of F "unassigned_lit A" F' K d]
    by (metis append_take_drop_id)
  show ?case
    by (auto simp add: min rem F latm lexord_def lex_conv)
qed
lemma length_complete_list_to_size:
  "length (complete_list_to_size s n a) = max s (length a)"
  by auto
  
definition all_bounded_list_different2 :: "nat \<Rightarrow> nat \<Rightarrow> ((nat list \<times> 'a) \<times> nat list \<times> 'b) set" where
"all_bounded_list_different2 m p \<equiv>
  {((T, u), (S, y)). ((length S \<le> p \<and> (\<forall>n \<in> set S. n \<le> m)) \<and> (length T \<le> p \<and> (\<forall>n \<in> set T. n \<le> m)))
     \<and>(T, S) \<in> lexord less_than}"

lemma all_bounded_list_different2_increasing:
  "p' \<ge> p \<Longrightarrow> m' \<ge> m \<Longrightarrow> all_bounded_list_different2 p m \<subseteq> all_bounded_list_different2 p' m'"
  by (auto simp add: all_bounded_list_different2_def)

lemma wf_bounded_distinct_different2_lexord:
  "wf (all_bounded_list_different2 m p)"
  unfolding all_bounded_list_different2_def
  apply (rule wf_fst_wf_pair)
  by (rule wf_subset[OF wf_bounded_distinct_lexord[of "Suc p" "Suc m"]]) auto
  
subsection \<open>Using a proper measure\<close>  
definition \<mu>\<^sub>C  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
"\<mu>\<^sub>C s b M \<equiv> (\<Sum> i =0..<length M. M!i * b^ (s +i - length M))"

lemma \<mu>\<^sub>C_nil[simp]:
  "\<mu>\<^sub>C s b [] = 0"
  unfolding \<mu>\<^sub>C_def by auto
  
lemma \<mu>\<^sub>C_single[simp]:
  "\<mu>\<^sub>C s b [L] = L * b ^ (s - Suc 0)"
  unfolding \<mu>\<^sub>C_def by auto
  
lemma set_sum_atLeastLessThan_add:
  "(\<Sum>i=k..<k+(b::nat). f i) = (\<Sum>i=0..<b. f (k+ i))"
  by (induction b) auto

lemma set_sum_atLeastLessThan_Suc:
  "(\<Sum>i=1..<Suc j. f i) = (\<Sum>i=0..<j. f (Suc i))"
  using set_sum_atLeastLessThan_add[of _ 1 j] by auto

lemma \<mu>\<^sub>C_cons:
  "\<mu>\<^sub>C s b (L # M) = L * b ^ (s - 1 - length M) + \<mu>\<^sub>C s b M"
proof -
  have "\<mu>\<^sub>C s b (L # M) = (\<Sum> i =0..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
    unfolding \<mu>\<^sub>C_def by blast
  also have "\<dots> = (\<Sum> i =0..<1. (L#M)!i * b^ (s +i - length (L#M)))
                 + (\<Sum> i =1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
     by (smt Nat.le_iff_add One_nat_def add.commute le0 list.size(4) setsum_add_nat_ivl)
  finally have "\<mu>\<^sub>C s b (L # M)= L * b ^ (s - 1 - length M) 
                  + (\<Sum> i = 1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M)))"
     by auto
  moreover {
    have "(\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M))) =
           (\<Sum>i=0..<length (M). (L#M)!(Suc i) * b^ (s + (Suc i) - length (L#M)))"
     unfolding length_Cons set_sum_atLeastLessThan_Suc by blast
    also have " \<dots> = (\<Sum>i=0..<length (M). M!i * b^ (s + i - length M))"
      by auto
    finally have "(\<Sum>i=1..<length (L#M). (L#M)!i * b^ (s +i - length (L#M))) = \<mu>\<^sub>C s b M"
      unfolding \<mu>\<^sub>C_def .
    }
  ultimately show ?thesis by presburger
qed    


lemma \<mu>\<^sub>C_append:
  assumes "s \<ge> length (M @ M')"
  shows "\<mu>\<^sub>C s b (M @ M') = \<mu>\<^sub>C (s - length M') b M + \<mu>\<^sub>C s b M'"
proof -
  have "\<mu>\<^sub>C s b (M @ M') = (\<Sum> i =0..<length (M @ M'). (M @ M')!i * b^ (s +i - length (M @ M')))"
    unfolding \<mu>\<^sub>C_def by blast
  moreover hence "\<dots> = (\<Sum>i =0..< length M. (M @ M')!i * b^ (s +i - length (M @ M')))
                 + (\<Sum>i =length M..<length (M @ M'). (M @ M')!i * b^ (s +i - length (M @ M')))"
    unfolding length_append by (smt Nat.le_iff_add One_nat_def add.commute le0 list.size(4)
      setsum_add_nat_ivl)
  moreover 
    have "\<forall>i\<in>{0..< length M}. (M @ M')!i * b^ (s +i - length (M @ M')) = M ! i * b ^ (s - length M'
      + i - length M)"
      using \<open>s \<ge> length (M @ M')\<close> by (auto simp add: nth_append ac_simps)
    hence "\<mu>\<^sub>C (s - length M') b M = (\<Sum>i=0..< length M. (M @ M')!i * b^ (s +i - length (M @ M')))"  
      unfolding \<mu>\<^sub>C_def by auto
  ultimately have "\<mu>\<^sub>C s b (M @ M')= \<mu>\<^sub>C (s - length M') b M
                  + (\<Sum> i =length M..<length (M @ M'). (M @ M')!i * b^ (s +i - length (M @ M')))"
     by auto
  moreover {
    have "(\<Sum>i =length M..<length (M @ M'). (M @ M')!i * b^ (s +i - length (M @ M'))) =
           (\<Sum>i=0..<length M'. M'!i * b^ (s + i - length M'))"
     unfolding length_append set_sum_atLeastLessThan_add by auto
    hence "(\<Sum>i =length M..<length (M @ M'). (M @ M')!i * b^ (s +i - length (M @ M'))) = \<mu>\<^sub>C s b M'"
      unfolding \<mu>\<^sub>C_def .
    }
  ultimately show ?thesis by presburger
qed    

lemma \<mu>\<^sub>C_cons_non_empty_inf:
  assumes M_ge_1: "\<forall>i\<in>set M. i \<ge> 1" and M: "M \<noteq> []"
  shows "\<mu>\<^sub>C s b M \<ge> b ^  (s - length M)"
  using assms by (cases M) (auto simp: mult_eq_if \<mu>\<^sub>C_cons)

text \<open>Duplicate of "~~/src/HOL/ex/NatSum.thy"\<close>
lemma sum_of_powers: "0 < k \<Longrightarrow> (k - 1) * (\<Sum>i=0..<n. k^i) = k^n - (1::nat)"
 by (induct n) (auto simp add: Nat.nat_distrib)

text \<open>We add 1 to count the marked literal\<close>
abbreviation \<nu> where
"\<nu> M \<equiv> map ((\<lambda>l. 1 + length l) o snd) (get_all_marked_decomposition M)"

text \<open>In the degenerated cases, we only have the large inequality holds. In the other cases, the 
  following strict inequality holds:\<close>
lemma \<mu>\<^sub>C_bounded_non_degenerated:
  fixes b ::nat
  assumes
    "b > 0" and
    "M \<noteq> []" and
    M_le: "\<forall>i < length M. M!i < b" and
    "s \<ge> length M"
  shows "\<mu>\<^sub>C s b M < b^s"
proof -
  consider (b1) "b= 1" | (b) "b>1" using \<open>b>0\<close> by (cases b) auto
  thus ?thesis
    proof cases
      case b1
      hence "\<forall>i < length M. M!i = 0" using M_le by auto
      hence "\<mu>\<^sub>C s b M = 0" unfolding \<mu>\<^sub>C_def by auto
      thus ?thesis using \<open>b > 0\<close> by auto
    next
      case b
      have "\<forall> i \<in> {0..<length M}. M!i * b^ (s +i - length M) \<le> (b-1) * b^ (s +i - length M)"
        using M_le \<open>b > 1\<close> by auto
      hence "\<mu>\<^sub>C s b M \<le>  (\<Sum> i =0..<length M. (b-1) * b^ (s +i - length M))"
         using \<open>M\<noteq>[]\<close> \<open>b>0\<close> unfolding \<mu>\<^sub>C_def by (auto intro: setsum_mono)
      also 
        have "\<forall> i \<in> {0..<length M}. (b-1) * b^ (s +i - length M) = (b-1) * b^ i * b^(s - length M)"
          by (metis Nat.add_diff_assoc2 add.commute assms(4) mult.assoc power_add)
        hence "(\<Sum>i =0..<length M. (b-1) * b^ (s +i - length M)) 
          = (\<Sum>i =0..<length M. (b-1)* b^ i * b^(s - length M))"
          by (auto simp add: ac_simps)
      also have "\<dots> = (\<Sum>i =0..<length M. b^ i) * b^(s - length M) * (b-1)"
         by (simp add: setsum_left_distrib setsum_right_distrib ac_simps)
      finally have "\<mu>\<^sub>C s b M \<le> (\<Sum>i =0..<length M. b^ i) * (b-1) * b^(s - length M)" 
        by (simp add: ac_simps)
        
      also
        have "(\<Sum>i =0..<length M. b^ i)* (b-1) = b ^ (length M) - 1"
          using sum_of_powers[of b "length M"] \<open>b>1\<close>
          by (auto simp add: ac_simps)
      finally have "\<mu>\<^sub>C s b M \<le> (b ^ (length M) - 1) * b ^ (s - length M)"
        by auto
      also have "\<dots> < b ^ (length M) * b ^ (s - length M)"
        using \<open>b>1\<close> by auto
      also have "\<dots> = b ^ s"
        by (metis assms(4) le_add_diff_inverse power_add)
      finally show ?thesis unfolding \<mu>\<^sub>C_def by (auto simp add: ac_simps)
    qed   
qed

text \<open> In the degenerate case @{term "b=0"}, the list @{term M} is empty (since the list cannot 
  contain any element).\<close>
lemma \<mu>\<^sub>C_bounded:
  fixes b ::nat
  assumes
    M_le: "\<forall>i < length M. M!i < b" and
    "s \<ge> length M"
    "b > 0"
  shows "\<mu>\<^sub>C s b M < b ^ s"
proof -
  consider (M0) "M = []" | (M) "b > 0" and "M \<noteq> []"
    using M_le by (cases b, cases M) auto
  thus ?thesis
    proof cases
      case M0
      thus ?thesis using M_le \<open>b > 0\<close> by auto
    next
      case M
      show ?thesis using \<mu>\<^sub>C_bounded_non_degenerated[OF M assms(1,2)] by arith
    qed
qed
lemma \<mu>\<^sub>C_base_is_0:
  "(\<Sum>i = 0..<n. M ! i * (0::nat) ^ i) \<le> M ! 0"
  unfolding \<mu>\<^sub>C_def apply (induction n rule: nat_induct)
  apply simp
  apply (case_tac n, auto)
  done
lemma 
  assumes "length M \<le> s"
  shows "\<mu>\<^sub>C s 0 M \<le> M!0"  
proof -
  {
    assume "s = length M"
    moreover {
      fix n
      have "(\<Sum>i = 0..<n. M ! i * (0::nat) ^ i) \<le> M ! 0"
        apply (induction n rule: nat_induct)
        apply simp
        apply (case_tac n, auto)
        done
    }
    ultimately have ?thesis unfolding \<mu>\<^sub>C_def by auto
  }
  moreover 
  {
    assume "length M < s"
    hence "\<mu>\<^sub>C s 0 M = 0" unfolding \<mu>\<^sub>C_def by auto}
  ultimately show ?thesis using assms unfolding \<mu>\<^sub>C_def by linarith
qed
lemma length_in_get_all_marked_decomposition_bounded:
  assumes i:"i \<in> set (\<nu> M)"
  shows "i \<le> Suc (length M)"
proof -
  obtain a b where 
    "(a, b) \<in> set (get_all_marked_decomposition M)" and
    ib: "i = Suc (length b)"
    using i by auto
  then obtain c where "M = c @ b @ a" using get_all_marked_decomposition_exists_prepend' by metis
  from arg_cong[OF this, of length] show ?thesis using i ib by auto
qed
  
lemma list_access_to_all_iff_set:
  "(\<forall>i<length l. P (l ! i)) \<longleftrightarrow> (\<forall>a \<in> set l. P a)" 
  by (metis in_set_conv_nth)

value "int (\<mu>\<^sub>C 3 10 [1,2])"
thm \<mu>\<^sub>C_append[of "M" "[L]" "3" "10", simplified] \<mu>\<^sub>C_bounded_non_degenerated[of 10 M 2, simplified]

lemma dpll_trail_mes_decreasing_prop:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits " and N :: "'v clauses"
  assumes "dpll (M, N) (M', N')" and
  "atms_of_m N \<subseteq> atms_of_m A" and
  "atm_of ` lits_of M \<subseteq> atms_of_m A" and
  "no_dup M" and
  finite: "finite A" and
  at_least_one_lit[simp]: "0 < card (atms_of_m A)"
  shows "\<mu>\<^sub>C (1+card (atms_of_m A)) (2+card (atms_of_m A)) (\<nu> M') > \<mu>\<^sub>C (1+card (atms_of_m A)) 
    (2+card (atms_of_m A)) (\<nu> M)"
  using assms
proof (induction rule: dpll_all_induct)
  case (propagate C L N M d) note CLN = this(1) and MC =this(2) and undef_L = this(3) and
    A = this(4) and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L d # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_propagate propagate.propagate[OF propagate.hyps] A MA
    by blast

  have no_dup: "no_dup (Propagated L d # M)"
    using defined_lit_map propagate.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Propagated L d # M) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L d # b))"
    using b_le_M by force
  thus ?case by (auto simp: latm M \<mu>\<^sub>C_cons)
next
  case (decide L M N lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4)
    and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Marked L lv # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_decide decide.decide[OF decide.hyps] A MA  NA by blast

  have no_dup: "no_dup (Marked L lv # M)"
    using defined_lit_map decide.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence "length (Marked L lv # M) \<le> card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)
  hence latm: "unassigned_lit A M = Suc (unassigned_lit A (Marked L lv # M))"
    using b_le_M by force
  show ?case by (simp add: latm \<mu>\<^sub>C_cons)
next
  case (backjump C N F' K d F L _ lv) note undef_L = this(1) and MC =this(2) and NA = this(3)
    and A = this(4) and MA = this(5) and nd = this(8)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L lv # F) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set backjump.hyps(4) backjump.prems(1) backjump.prems(2) by auto

  have no_dup: "no_dup (Propagated L lv # F)"
    using bj_backjump backjump.backjump[OF backjump.hyps] dpll_no_dup nd by blast
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp

  hence F_le_A: "length (Propagated L lv # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup]
    by (simp add: card_mono)

  have min: "min ((length (get_all_marked_decomposition F)))
                 (length (get_all_marked_decomposition (F' @ Marked K d # F)))
             = length (get_all_marked_decomposition F)"
    unfolding length_get_all_marked_decomposition_append_Marked by (simp add: min_def)

  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
    by (cases "get_all_marked_decomposition F") auto

  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L lv # F" a "Propagated L lv # b"]
      by simp
  hence latm: "unassigned_lit A b = Suc (unassigned_lit A (Propagated L lv # b))"
     using F_le_A by simp
  obtain rem where
    rem:"(map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition (F' @ Marked K d # F)))) 
    = map (\<lambda>a. Suc (length (snd a))) (rev (get_all_marked_decomposition F)) @ rem"
    using take_length_get_all_marked_decomposition_marked_sandwich[of F "\<lambda>a. Suc (length a)" F' K d]
    unfolding o_def
    by (metis append_take_drop_id)    
  hence rem: "map (\<lambda>a. Suc (length (snd a))) ((get_all_marked_decomposition (F' @ Marked K d # F))) 
    = rev rem @ map (\<lambda>a. Suc (length (snd a))) ((get_all_marked_decomposition F))"
    by (simp add: rev_map[symmetric] rev_swap)
  have "length (rev rem @ map (\<lambda>a. Suc (length (snd a))) (get_all_marked_decomposition F)) 
          \<le> Suc (card (atms_of_m A))"
    by (smt One_nat_def `finite (atms_of_m A)` add_Suc backjump.prems(2) card_mono 
      distinctlength_eq_card_atm_of_lits_of dual_order.trans le_imp_less_Suc 
      length_get_all_marked_decomposition_length length_map less_eq_Suc_le nd plus_nat.add_0 rem)
  moreover have A: "length (Suc (Suc (length (snd (hd (get_all_marked_decomposition F))))) 
                      # map (\<lambda>a. Suc (length (snd a))) (tl (get_all_marked_decomposition F))) 
                    \<le> Suc (card (atms_of_m A))" 
    by (metis F F_le_A One_nat_def add_Suc dual_order.trans le_SucI length_Cons 
      length_get_all_marked_decomposition_length length_map list.sel(3) plus_nat.add_0)
  moreover have "length (rev rem) \<le> unassigned_lit A l"
    using F calculation(1) by auto
  moreover 
    { fix i ::nat and  xs :: "'a list"
      have "i < length xs \<Longrightarrow> length xs - Suc i < length xs"
        by auto
      hence H: "i<length xs \<Longrightarrow> rev xs ! i \<in> set xs"
        using rev_nth[of i xs] unfolding in_set_conv_nth  by (force simp add: in_set_conv_nth)
    } note H = this
    have "length (F' @ Marked K d # F)\<le> card (atms_of_m A)"
      by (metis `finite (atms_of_m A)` backjump.prems(2) distinctlength_eq_card_atm_of_lits_of nd
        card_mono)
    hence "\<forall>i<length rem. rev rem ! i < card (atms_of_m A) + 2"
      using length_in_get_all_marked_decomposition_bounded[of _ "F' @ Marked K d # F"] 
      by (force simp add: o_def rem dest!: H intro: length_get_all_marked_decomposition_length) 
  ultimately show ?case
    using \<mu>\<^sub>C_bounded[of "rev rem" "card (atms_of_m A)+2" "unassigned_lit A l"]
    by (simp add: min rem \<mu>\<^sub>C_append \<mu>\<^sub>C_cons F)
qed
end