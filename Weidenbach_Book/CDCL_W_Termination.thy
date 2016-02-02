theory CDCL_W_Termination
imports CDCL_W
begin

context cdcl\<^sub>W_ops
begin
subsection \<open>Termination\<close>
text \<open>The condition that no learned clause is a tautology is overkill (in the sense that the
  no-duplicate condition is enough), but we can reuse @{term build_all_simple_clss}.

  The invariant contains all the structural invariants that holds,\<close>
definition cdcl\<^sub>W_all_struct_inv where
  "cdcl\<^sub>W_all_struct_inv S =
    (no_strange_atm S \<and> cdcl\<^sub>W_M_level_inv S
    \<and> (\<forall>s \<in># learned_clss S. \<not>tautology s)
    \<and> distinct_cdcl\<^sub>W_state S \<and> cdcl\<^sub>W_conflicting S
    \<and> all_decomposition_implies_m (init_clss S) (get_all_marked_decomposition (trail S))
    \<and> cdcl\<^sub>W_learned_clause S)"

lemma cdcl\<^sub>W_all_struct_inv_inv:
  assumes "cdcl\<^sub>W S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_all_struct_inv S'"
  unfolding cdcl\<^sub>W_all_struct_inv_def
proof (intro HOL.conjI)
  show "no_strange_atm S'"
    using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  show "cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "distinct_cdcl\<^sub>W_state S'"
     using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "cdcl\<^sub>W_conflicting S'"
     using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "all_decomposition_implies_m (init_clss S') (get_all_marked_decomposition (trail S'))"
     using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast
  show "cdcl\<^sub>W_learned_clause S'"
     using cdcl\<^sub>W_all_inv[OF assms(1)] assms(2) unfolding cdcl\<^sub>W_all_struct_inv_def by fast

  show "\<forall>s\<in>#learned_clss S'. \<not> tautology s"
    using assms(1)[THEN learned_clss_are_not_tautologies] assms(2)
    unfolding cdcl\<^sub>W_all_struct_inv_def by fast
qed

lemma rtranclp_cdcl\<^sub>W_all_struct_inv_inv:
  assumes "cdcl\<^sub>W\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_all_struct_inv S'"
  using assms by induction (auto intro: cdcl\<^sub>W_all_struct_inv_inv)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv:
  "cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> cdcl\<^sub>W_all_struct_inv T"
  by (meson cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_unfold)

lemma rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> cdcl\<^sub>W_all_struct_inv T"
  by (induction rule: rtranclp_induct) (auto intro: cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)

(* TODO Move *)
lemma cdcl\<^sub>W_o_learned_clause_increasing:
  "cdcl\<^sub>W_o S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  by (induction rule: cdcl\<^sub>W_o_induct) auto

lemma cdcl\<^sub>W_cp_learned_clause_increasing:
  "cdcl\<^sub>W_cp S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  by (induction rule: cdcl\<^sub>W_cp.induct) auto

lemma rtranclp_cdcl\<^sub>W_cp_learned_clause_increasing:
  "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  by (induction rule: rtranclp.induct) (auto dest: cdcl\<^sub>W_cp_learned_clause_increasing)

lemma full1_cdcl\<^sub>W_cp_learned_clause_increasing:
  "full1 cdcl\<^sub>W_cp S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  "full cdcl\<^sub>W_cp S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  unfolding full1_def full_def
  by (simp_all add: rtranclp_cdcl\<^sub>W_cp_learned_clause_increasing rtranclp_unfold)

lemma cdcl\<^sub>W_stgy_learned_clause_increasing:
  "cdcl\<^sub>W_stgy S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  by (induction rule: cdcl\<^sub>W_stgy.induct)
     (auto dest!: full1_cdcl\<^sub>W_cp_learned_clause_increasing cdcl\<^sub>W_o_learned_clause_increasing)

lemma rtranclp_cdcl\<^sub>W_stgy_learned_clause_increasing:
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<Longrightarrow> learned_clss S \<subseteq># learned_clss S'"
  by (induction rule: rtranclp.induct)
     (auto dest!: cdcl\<^sub>W_stgy_learned_clause_increasing)

subsection \<open>No Relearning of a clause\<close>
lemma cdcl\<^sub>W_o_new_clause_learned_is_backtrack_step:
  assumes learned: "D \<in># learned_clss T" and
  new: "D \<notin># learned_clss S" and
  cdcl\<^sub>W: "cdcl\<^sub>W_o S T"
  shows "backtrack S T \<and> conflicting S = C_Clause D"
  using cdcl\<^sub>W learned new
proof (induction rule: cdcl\<^sub>W_o_induct)
  case (backtrack K i M1 M2 L C T) note T = this(6) and D_T = this(7) and D_S = this(8)
  then have "D = C + {#L#}" using not_gr0 by fastforce
  then show ?case
    using T backtrack.hyps(1-5) backtrack.intros by auto
qed auto

lemma cdcl\<^sub>W_cp_new_clause_learned_has_backtrack_step:
  assumes learned: "D \<in># learned_clss T" and
  new: "D \<notin># learned_clss S" and
  cdcl\<^sub>W: "cdcl\<^sub>W_stgy S T"
  shows "\<exists>S'. backtrack S S' \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' T \<and> conflicting S = C_Clause D"
  using cdcl\<^sub>W learned new
proof (induction rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S S')
  thus ?case
    unfolding full1_def by (metis (mono_tags, lifting) rtranclp_cdcl\<^sub>W_cp_learned_clause_inv
      tranclp_into_rtranclp)
next
  case (other' S S' S'')
  hence "D \<in># learned_clss S'"
    unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_cp_learned_clause_inv)
  thus ?case
    using  cdcl\<^sub>W_o_new_clause_learned_is_backtrack_step[OF _ \<open>D \<notin># learned_clss S\<close> \<open>cdcl\<^sub>W_o S S'\<close>]
    \<open>full cdcl\<^sub>W_cp S' S''\<close> by (metis cdcl\<^sub>W_stgy.conflict' full_unfold r_into_rtranclp
      rtranclp.rtrancl_refl)
qed

lemma rtranclp_cdcl\<^sub>W_cp_new_clause_learned_has_backtrack_step:
  assumes learned: "D \<in># learned_clss T" and
  new: "D \<notin># learned_clss S" and
  cdcl\<^sub>W: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
  shows "\<exists>S' S''. cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S' \<and> backtrack S' S'' \<and> conflicting S' = C_Clause D \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T"
  using cdcl\<^sub>W learned new
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl S)
  thus ?case
    using cdcl\<^sub>W_cp_new_clause_learned_has_backtrack_step by blast
next
  case (rtrancl_into_rtrancl S T U) note st =this(1) and o = this(2) and IH = this(3) and
    D_U = this(4) and D_S = this(5)
  show ?case
    proof (cases "D \<in># learned_clss T")
      case True
      then obtain S' S'' where
        st': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and
        bt: "backtrack S' S''" and
        confl: "conflicting S' = C_Clause D" and
        st'': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T"
        using IH D_S by metis
      thus ?thesis using o by (meson rtranclp.simps)
    next
      case False
      obtain S' where
        bt: "backtrack T S'" and
        st': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U" and
        confl: "conflicting T = C_Clause D"
        using cdcl\<^sub>W_cp_new_clause_learned_has_backtrack_step[OF D_U False o] by metis
      hence "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T" and
        "backtrack T S'" and
        "conflicting T = C_Clause D" and
        "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U"
        using o st by auto
      thus ?thesis by blast
    qed
qed

lemma propagate_no_more_Marked_lit:
  assumes "propagate S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms by auto

lemma conflict_no_more_Marked_lit:
  assumes "conflict S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms by auto

lemma cdcl\<^sub>W_cp_no_more_Marked_lit:
  assumes "cdcl\<^sub>W_cp S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms apply (induct rule: cdcl\<^sub>W_cp.induct)
  using conflict_no_more_Marked_lit propagate_no_more_Marked_lit by auto

lemma rtranclp_cdcl\<^sub>W_cp_no_more_Marked_lit:
  assumes "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms apply (induct rule: rtranclp.induct)
  using cdcl\<^sub>W_cp_no_more_Marked_lit by blast+

lemma cdcl\<^sub>W_o_no_more_Marked_lit:
  assumes "cdcl\<^sub>W_o S S'" and "\<not>decide S S'"
  shows "Marked K i \<in> set (trail S') \<longrightarrow> Marked K i \<in> set (trail S)"
  using assms
proof (induct rule: cdcl\<^sub>W_o_induct)
  case backtrack note T =this(6)
  have H: "\<And>A M M1. M = A @ M1 \<Longrightarrow>  Marked K i \<in> set M1 \<Longrightarrow> Marked K i \<in> set M"  by auto
  show ?case
    using backtrack(1) T by (auto dest: H)
next
  case (decide L T)
  then show ?case by blast
qed auto

lemma cdcl\<^sub>W_new_marked_at_beginning_is_decide:
  assumes "cdcl\<^sub>W_stgy S S'" and
  "no_dup (trail S')" and
  "trail S' = M' @ Marked L i # M" and
  "trail S = M"
  shows "\<exists>T. decide S T \<and> no_step cdcl\<^sub>W_cp S"
  using assms
proof (induct rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' S S') note st =this(1) and no_dup = this(2) and S' = this(3) and S = this(4)
  have "Marked L i \<in> set (trail S')" and "Marked L i \<notin> set (trail S)"
    using no_dup unfolding S S' by (auto simp add: rev_image_eqI)
  hence False
    using st rtranclp_cdcl\<^sub>W_cp_no_more_Marked_lit[of S S']
    unfolding full1_def rtranclp_unfold by blast
  thus ?case by fast
next
  case (other' S T U) note o =this(1) and ns = this(2) and st = this(3) and no_dup = this(4) and
    S' = this(5) and S = this(6)
  have "Marked L i \<in> set (trail U)" and "Marked L i \<notin> set (trail S)"
    using no_dup unfolding S S' by (auto simp add: rev_image_eqI)
  hence "Marked L i \<in> set (trail T)"
    using st rtranclp_cdcl\<^sub>W_cp_no_more_Marked_lit unfolding full_def by blast
  thus ?case using cdcl\<^sub>W_o_no_more_Marked_lit[OF o] \<open>Marked L i \<notin> set (trail S)\<close> ns by meson
qed

lemma cdcl\<^sub>W_o_is_decide:
  assumes "cdcl\<^sub>W_o S' T" and
  "trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M"and
  "\<not> (\<exists>M'. trail S' = M' @ Marked L i # H @ M)"
  shows "decide S' T"
      using assms
proof (induction rule:cdcl\<^sub>W_o_induct)
  case (backtrack K i M1 M2 L D)
  then obtain c where "trail S' = c @ M2 @ Marked K (Suc i) # M1"
    by auto
  thus ?case
    using backtrack
    by (cases "drop (length M\<^sub>0) M'") auto
next
  case decide
  show ?case using decide_rule[of S'] decide(1-4) by auto
qed auto

lemma rtranclp_cdcl\<^sub>W_new_marked_at_beginning_is_decide:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Marked L i # H @ M" and
  "trail R = M" and
  "cdcl\<^sub>W_M_level_inv R"
  shows
    "\<exists>S T T'. cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S \<and> decide S T \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S U \<and> no_step cdcl\<^sub>W_cp S \<and>
      trail T = Marked L i # H @ M \<and> trail S = H @ M \<and> cdcl\<^sub>W_stgy S T' \<and>
      cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T' U"
  using assms
proof (induct arbitrary: M H M' i rule: rtranclp.induct)
  case (rtrancl_refl a)
  thus ?case by auto
next
  case (rtrancl_into_rtrancl S T U) note st = this(1) and IH = this(2) and s = this(3) and
    U = this(4) and S = this(5) and lev = this(6)
  show ?case
    proof (cases "\<exists>M'. trail T = M' @ Marked L i # H @ M")
      case False
      with s show ?thesis using U s st S
        proof induction
          case (conflict' V W) note cp = this(1) and  nd = this(2) and W = this(3)
          then obtain M\<^sub>0 where "trail W = M\<^sub>0 @ trail V" and nmarked: "\<forall>l\<in>set M\<^sub>0. \<not> is_marked l"
            using rtranclp_cdcl\<^sub>W_cp_dropWhile_trail unfolding full1_def rtranclp_unfold by meson
          hence MV: "M' @ Marked L i # H @ M = M\<^sub>0 @ trail V" unfolding W by simp
          hence V: "trail V = drop (length M\<^sub>0) (M' @ Marked L i # H @ M)"
            by auto
          have "takeWhile (Not o is_marked) M' = M\<^sub>0  @ takeWhile (Not \<circ> is_marked) (trail V)"
            using arg_cong[OF MV, of "takeWhile (Not o is_marked)"] nmarked
            by (simp add: takeWhile_tail)
          from arg_cong[OF this, of length] have "length M\<^sub>0 \<le> length M'"
            unfolding length_append by (metis (no_types, lifting) Nat.le_trans le_add1
              length_takeWhile_le)
          hence False using nd V by auto
          thus ?case by fast
        next
          case (other' S' T U) note o = this(1) and ns =this(2) and cp = this(3) and nd = this(4)
            and U = this(5) and st = this(6)
          obtain M\<^sub>0 where "trail U = M\<^sub>0 @ trail T" and nmarked: "\<forall>l\<in>set M\<^sub>0. \<not> is_marked l"
            using rtranclp_cdcl\<^sub>W_cp_dropWhile_trail cp unfolding full_def by meson
          hence MV: "M' @ Marked L i # H @ M = M\<^sub>0 @ trail T" unfolding U by simp
          hence V: "trail T = drop (length M\<^sub>0) (M' @ Marked L i # H @ M)"
            by auto
          have "takeWhile (Not o is_marked) M' = M\<^sub>0  @ takeWhile (Not \<circ> is_marked) (trail T)"
            using arg_cong[OF MV, of "takeWhile (Not o is_marked)"] nmarked
            by (simp add: takeWhile_tail)
          from arg_cong[OF this, of length]  have "length M\<^sub>0 \<le> length M'"
            unfolding length_append by (metis (no_types, lifting) Nat.le_trans le_add1
              length_takeWhile_le)
          hence tr_T: "trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M" using V by auto
          hence LT: "Marked L i \<in> set (trail T)" by auto
          moreover
            have "decide S' T" using o nd tr_T cdcl\<^sub>W_o_is_decide by metis
          ultimately  have "decide S' T" using cdcl\<^sub>W_o_no_more_Marked_lit[OF o] by blast
          then have 1: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and 2: "decide S' T" and 3: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U"
            using st other'.prems(4)
            by (metis cdcl\<^sub>W_stgy.conflict' cp full_unfold r_into_rtranclp rtranclp.rtrancl_refl)+
          have [simp]: "drop (length M\<^sub>0) M' = []"
            using \<open>decide S' T\<close> \<open>Marked L i \<in> set (trail T)\<close>  nd tr_T
            by (auto simp add: Cons_eq_append_conv)
          have T: "drop (length M\<^sub>0) M' @ Marked L i # H @ M = Marked L i # trail S'"
            using \<open>decide S' T\<close> \<open>Marked L i \<in> set (trail T)\<close>  nd tr_T
            by auto
          have "trail T = Marked L i # trail S'"
            using \<open>decide S' T\<close> \<open>Marked L i \<in> set (trail T)\<close> tr_T
            by auto
          hence 5: "trail T = Marked L i # H @ M"
              using append.simps(1) list.sel(3) local.other'(5) tl_append2 by (simp add: tr_T)
          have 6: "trail S' = H @ M"
            by (metis (no_types) \<open>trail T = Marked L i # trail S'\<close>
              \<open>trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M\<close> append_Nil list.sel(3) nd
              tl_append2)
          have 7: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U" using other'.prems(4) st by auto
          have 8: "cdcl\<^sub>W_stgy S' U" "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* U U"
            using cdcl\<^sub>W_stgy.other'[OF other'(1-3)] by simp_all
          show ?case apply (rule exI[of _ S'], rule exI[of _ T], rule exI[of _ U])
            using ns 1 2 3 5 6 7 8 by fast
        qed
    next
      case True
      then obtain M' where T: "trail T = M' @ Marked L i # H @ M" by metis
      from IH[OF this S lev] obtain S' S'' S''' where
        1: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'" and
        2: "decide S' S''" and
        3: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T " and
        4: "no_step cdcl\<^sub>W_cp S'" and
        6: "trail S'' = Marked L i # H @ M" and
        7: "trail S' = H @ M" and
        8: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' T" and
        9: "cdcl\<^sub>W_stgy S' S'''" and
        10: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S''' T"
           by blast
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' U" using s \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T \<close> by auto
      moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U" using "8" s by auto
      moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S''' U" using 10 s by auto
      ultimately show ?thesis apply - apply (rule exI[of _ S'], rule exI[of _ S''])
        using 1 2 4 6 7 8 9  by blast
    qed
qed

lemma rtranclp_cdcl\<^sub>W_new_marked_at_beginning_is_decide':
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Marked L i # H @ M" and
  "trail R = M" and
  "cdcl\<^sub>W_M_level_inv R"
  shows "\<exists>y y'. cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R y \<and> cdcl\<^sub>W_stgy y y' \<and> \<not> (\<exists>c. trail y = c @ Marked L i # H @ M)
    \<and> (\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* y' U"
proof -
  fix T'
  obtain S' T T' where
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S'" and
    "decide S' T" and
    TU: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U" and
    "no_step cdcl\<^sub>W_cp S'" and
    trT: "trail T = Marked L i # H @ M" and
    trS': "trail S' = H @ M" and
    S'U: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U" and
    S'T': "cdcl\<^sub>W_stgy S' T'" and
    T'U: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T' U"
    using rtranclp_cdcl\<^sub>W_new_marked_at_beginning_is_decide[OF assms] by blast
  have n: "\<not> (\<exists>c. trail S' = c @ Marked L i # H @ M)" using trS' by auto
  show ?thesis
    using rtranclp_trans[OF st] rtranclp_exists_last_with_prop[of cdcl\<^sub>W_stgy S' T' _
        "\<lambda>a _. \<not>(\<exists>c. trail a = c @ Marked L i # H @ M)", OF S'T' T'U n]
      by meson
qed

lemma beginning_not_marked_invert:
  assumes A: "M @ A = M' @ Marked K i # H" and
  nm: "\<forall>m\<in>set M. \<not>is_marked m"
  shows "\<exists>M. A = M @ Marked K i # H"
proof -
  have "A = drop (length M) (M' @ Marked K i # H)"
    using arg_cong[OF A, of "drop (length M)"] by auto
  moreover have "drop (length M) (M' @ Marked K i # H) = drop (length M) M' @ Marked K i # H"
    using nm by (metis (no_types, lifting) A drop_Cons' drop_append marked_lit.disc(1) not_gr0
      nth_append nth_append_length nth_mem zero_less_diff)
  finally show ?thesis by fast
qed

lemma cdcl\<^sub>W_stgy_trail_has_new_marked_is_decide_step:
  assumes "cdcl\<^sub>W_stgy S T"
  "\<not> (\<exists>c. trail S = c @ Marked L i # H @ M)" and
  "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* T U" and
  "\<exists>M'. trail U = M' @ Marked L i # H @ M" and
  "no_dup (trail S)"
  shows "\<exists>S'. decide S S' \<and> full cdcl\<^sub>W_cp S' T \<and> no_step cdcl\<^sub>W_cp S"
  using assms(3,1,2,4,5)
proof induction
  case (step T U)
  thus ?case by fastforce
next
  case base
  thus ?case
    proof (induction rule: cdcl\<^sub>W_stgy.induct)
      case (conflict' S T) note cp = this(1) and nd = this(2) and M' =this(3) and no_dup = this(3)
      then obtain M' where M': "trail T = M' @ Marked L i # H @ M" by metis
      obtain M'' where M'': "trail T = M'' @ trail S" and nm: "\<forall>m\<in> set M''. \<not>is_marked m"
        using cp unfolding full1_def
        by (metis rtranclp_cdcl\<^sub>W_cp_dropWhile_trail' tranclp_into_rtranclp)
      have False
        using beginning_not_marked_invert[of M'' "trail S" M' L i "H @ M"] M' nm nd unfolding M''
        by fast
      thus ?case by fast
    next
      case (other' S T U') note o = this(1) and ns = this(2) and cp = this(3) and nd = this(4)
        and trU' = this(5)
      have "cdcl\<^sub>W_cp\<^sup>*\<^sup>* T U'" using cp unfolding full_def by blast
      from rtranclp_cdcl\<^sub>W_cp_dropWhile_trail[OF this]
      have "\<exists>M'. trail T = M' @ Marked L i # H @ M"
        using  trU' beginning_not_marked_invert[of _ "trail T" _ L i "H @ M"] by metis
      then obtain M' where "trail T = M' @ Marked L i # H @ M"
        by auto
      with o nd cp ns
      show ?case
        proof (induction rule: cdcl\<^sub>W_o_induct)
          case (decide L) note dec = this(1) and cp = this(5) and ns = this(4)
          hence "decide S (cons_trail (Marked L (backtrack_lvl S +1)) (incr_lvl S))"
            using decide.hyps decide.intros[of S] by force
          thus ?case using cp decide.prems by (meson decide_state_eq_compatible ns state_eq_ref
            state_eq_sym)
        next
          case (backtrack K j M1 M2 L' D T) note decomp = this(1) and nd = this(7) and cp = this(3)
            and T = this(6) and trT = this(10) and ns = this(4)
          obtain MS3 where MS3: "trail S = MS3 @ M2 @ Marked K (Suc j) # M1"
            using get_all_marked_decomposition_exists_prepend[OF decomp] by metis
          have "tl (M' @ Marked L i # H @ M) = tl M' @ Marked L i # H @ M"
            using trT T by (cases M') auto
          hence M'': "M1 = tl M' @ Marked L i # H @ M"
            using arg_cong[OF trT[simplified], of tl] T decomp by simp
          have False using nd MS3 T unfolding M'' by auto
          thus ?case by fast
        qed auto
      qed
qed

lemma rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end:
  assumes "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* T U" and
  "\<exists>M'. trail U = M' @ Marked L i # H @ M"
  shows "\<exists>M'. trail T = M' @ Marked L i # H @ M"
  using assms by (induction rule: rtranclp.induct) auto

lemma cdcl\<^sub>W_o_cannot_learn:
  assumes "cdcl\<^sub>W_o y z" and
  "cdcl\<^sub>W_M_level_inv y " and
  "trail y = c @ Marked Kh i # H" and
  "D + {#L#} \<notin># learned_clss y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<forall>T. conflicting y = C_Clause T \<longrightarrow> trail y \<Turnstile>as CNot T" and
  "trail z = c' @ Marked Kh i # H"
  shows "D + {#L#} \<notin># learned_clss z"
  using assms(1-4,7,8)
proof (induction rule: cdcl\<^sub>W_o_induct)
  case (backtrack K j M1 M2 L' D' T) note decomp = this(1) and confl = this(3) and levD = this(5)
    and T =this(6) and lev =this(7) and trM = this(8) and DL = this(9) and learned = this(10) and
    z = this(11)
  obtain M3 where M3: "trail y = M3 @ M2 @ Marked K (Suc j) # M1"
    using decomp get_all_marked_decomposition_exists_prepend by metis
  have M: "trail y = c @ Marked Kh i # H" using trM by simp
  have H: "get_all_levels_of_marked (trail y) = rev [1..<1 + backtrack_lvl y]"
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  obtain d where d: "M1 = d @ Marked Kh i # H"
    using z T unfolding M3 by (smt M3 append_assoc list.inject list.sel(3) marked_lit.distinct(1)
      self_append_conv2 state_eq_trail tl_append2 trail_cons_trail trail_update_backtrack_lvl
      trail_update_conflicting reduce_trail_to_add_learned_cls
      reduce_trail_to_trail_tl_trail_decomp)
  have "i \<in> set (get_all_levels_of_marked (M3 @ M2 @ Marked K (Suc j) # d @ Marked Kh i # H))"
    by auto
  hence "i > 0" unfolding H[unfolded M3 d] by auto
  show ?case
    proof
      assume "D + {#L#} \<in># learned_clss T"
      hence DLD': "D + {#L#} = D' + {#L'#}" using DL T neq0_conv by fastforce
      have L_cKh: "atm_of L \<in> atm_of `lits_of (c @ [Marked Kh i])"
        using LH learned  M DLD'[symmetric] confl by (fastforce simp add: image_iff)
      have "get_all_levels_of_marked (M3 @ M2 @ Marked K (j + 1) # M1)
        = rev [1..<1 + backtrack_lvl y]"
        using lev unfolding cdcl\<^sub>W_M_level_inv_def M3 by auto
      from arg_cong[OF this, of "\<lambda>a. (Suc j) \<in> set a"] have "backtrack_lvl y \<ge> j" by auto

      have DD'[simp]: "D = D'"
        proof (rule ccontr)
          assume "D \<noteq> D'"
          hence "L' \<in>#  D" using DLD' by (metis add.left_neutral count_single count_union
            diff_union_cancelR neq0_conv union_single_eq_member)
          hence "get_level L' (trail y) \<le> get_maximum_level D (trail y)"
            using get_maximum_level_ge_get_level by blast
          moreover {
            have "get_maximum_level D (trail y) = get_maximum_level D H"
              using DH unfolding M by (simp add: get_maximum_level_skip_beginning)
            moreover
              have "get_all_levels_of_marked (trail y) = rev [1..<1 + backtrack_lvl y]"
                using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
              hence "get_all_levels_of_marked H = rev [1..< i]"
                unfolding M by (auto dest: append_cons_eq_upt_length_i
                  simp add: rev_swap[symmetric])
              hence "get_maximum_possible_level H < i"
                using get_maximum_possible_level_max_get_all_levels_of_marked[of H] \<open>i > 0\<close> by auto
            ultimately have "get_maximum_level D (trail y) < i"
              by (metis (full_types) dual_order.strict_trans nat_neq_iff not_le
                get_maximum_possible_level_ge_get_maximum_level) }
          moreover
            have "L \<in># D'"
              by (metis DLD' \<open>D \<noteq> D'\<close> add.left_neutral count_single count_union diff_union_cancelR
                neq0_conv union_single_eq_member)
            hence "get_maximum_level D' (trail y) \<ge> get_level L (trail y)"
              using get_maximum_level_ge_get_level by blast
          moreover {
            have "get_all_levels_of_marked (c @ [Marked Kh i]) = rev [i..< backtrack_lvl y+1]"
              using append_cons_eq_upt_length_i_end[of " rev (get_all_levels_of_marked H)" i
                "rev (get_all_levels_of_marked c)" "Suc 0" "Suc (backtrack_lvl y)"] H
              unfolding M apply (auto simp add: rev_swap[symmetric])
                by (metis (no_types, hide_lams) Nil_is_append_conv Suc_le_eq less_Suc_eq list.sel(1)
                  rev.simps(2) rev_rev_ident upt_Suc upt_rec)
            have "get_level L (trail y)  = get_level L (c @ [Marked Kh i])"
              using L_cKh LH unfolding M by simp
            have "get_level L (c @ [Marked Kh i]) \<ge> i"
              using L_cKh
                \<open>get_all_levels_of_marked (c @ [Marked Kh i]) = rev [i..<backtrack_lvl y + 1]\<close>
              backtrack.hyps(2) calculation(1,2) by auto
            hence "get_level L (trail y) \<ge> i"
              using M \<open>get_level L (trail y) = get_level L (c @ [Marked Kh i])\<close> by auto }
          moreover have "get_maximum_level D' (trail y) < get_level L' (trail y)"
            using \<open>j \<le> backtrack_lvl y\<close> backtrack.hyps(2,5) calculation(1-4) by linarith
          ultimately show False using backtrack.hyps(4) by linarith
        qed
      hence LL': "L = L'" using DLD' by auto
      have nd: "no_dup (trail y)" using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto

      { assume D: "D' = {#}"
        hence j: "j = 0" using levD by auto
        have "\<forall>m \<in> set M1. \<not>is_marked m"
          using H unfolding M3 j
          by (auto simp add: rev_swap[symmetric] get_all_levels_of_marked_no_marked
            dest!: append_cons_eq_upt_length_i)
        hence False using d by auto
      }
      moreover {
        assume D[simp]: "D' \<noteq> {#}"
        have "i \<le> j"
          using H unfolding M3 d by (auto simp add: rev_swap[symmetric]
            dest: upt_decomp_lt)
        have "j > 0" apply (rule ccontr)
          using H \<open> i > 0\<close> unfolding M3 d
          by (auto simp add: rev_swap[symmetric] dest!: upt_decomp_lt)
        obtain L'' where
          "L''\<in>#D'" and
          L''D': "get_level L'' (trail y) = get_maximum_level D' (trail y)"
          using get_maximum_level_exists_lit_of_max_level[OF D, of "trail y"] by auto
        have L''M: "atm_of L'' \<in> atm_of ` lits_of (trail y)"
          using get_rev_level_ge_0_atm_of_in[of 0 L'' "rev (trail y)"] \<open>j>0\<close> levD L''D' by auto
        hence "L'' \<in> lits_of  (Marked Kh i # d)"
          proof -
            {
              assume L''H: "atm_of L'' \<in> atm_of ` lits_of H"
              have "get_all_levels_of_marked H = rev [1..<i]"
                using H unfolding M
                by (auto simp add: rev_swap[symmetric] dest!: append_cons_eq_upt_length_i)
              moreover have "get_level L'' (trail y) = get_level L'' H"
                using L''H unfolding M by simp
              ultimately have False
                using levD \<open>j>0\<close> get_rev_level_in_levels_of_marked[of L'' 0 "rev H"] \<open>i \<le> j\<close>
                unfolding L''D'[symmetric] nd by auto
            }
            then show ?thesis
              using DD' DH \<open>L'' \<in># D'\<close> atm_of_lit_in_atms_of contra_subsetD by metis
          qed
        hence False
          using DH \<open>L''\<in>#D'\<close> nd unfolding M3 d
          by (auto simp add: atms_of_def image_iff image_subset_iff lits_of_def)
      }
      ultimately show False by blast
    qed
qed auto

lemma cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned:
  assumes "cdcl\<^sub>W_stgy y z" and
  "cdcl\<^sub>W_M_level_inv y" and
  "trail y = c @ Marked Kh i # H" and
  "D + {#L#} \<notin># learned_clss y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<forall>T. conflicting y = C_Clause T \<longrightarrow> trail y \<Turnstile>as CNot T" and
  "trail z = c' @ Marked Kh i # H"
  shows "D + {#L#} \<notin># learned_clss z"
  using assms
proof induction
  case conflict'
  thus ?case
    unfolding full1_def using tranclp_cdcl\<^sub>W_cp_learned_clause_inv by auto
next
  case (other' S T U) note o = this(1) and cp = this(3) and lev = this(4) and trS = this(5) and
    notin = this(6) and DH = this(7) and LH = this(8) and confl = this(9) and trU = this(10)
  obtain c' where c': "trail T = c' @ Marked Kh i # H"
    using cp beginning_not_marked_invert[of _ "trail T" c' Kh i H]
      rtranclp_cdcl\<^sub>W_cp_dropWhile_trail[of T U] unfolding trU full_def by fastforce
  show ?case
    using cdcl\<^sub>W_o_cannot_learn[OF o lev trS notin DH LH  confl c']
      rtranclp_cdcl\<^sub>W_cp_learned_clause_inv cp unfolding full_def by auto
qed

lemma rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned:
  assumes "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Marked K i # H @ []))\<^sup>*\<^sup>* y z" and
  "cdcl\<^sub>W_all_struct_inv y" and
  "trail y = c @ Marked K i # H" and
  "D + {#L#} \<notin># learned_clss y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<exists>c'. trail z = c' @ Marked K i # H"
  shows "D + {#L#} \<notin># learned_clss z"
  using assms(1-4,7)
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by auto[1]
next
  case (rtrancl_into_rtrancl S T U) note st = this(1) and s = this(2) and IH = this(3)[OF this(4-6)]
    and lev = this(4) and trS = this(5) and DL_S = this(6) and trU = this(7)
  obtain c where c: "trail T = c @ Marked K i # H" using s by auto
  obtain c' where c': "trail U = c' @ Marked K i # H" using trU by blast
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
    proof -
      have "\<forall>p pa. \<exists>s sa. \<forall>sb sc sd se. (\<not> p\<^sup>*\<^sup>* (sb::'st) sc \<or> p s sa \<or> pa\<^sup>*\<^sup>* sb sc)
        \<and> (\<not> pa s sa \<or> \<not> p\<^sup>*\<^sup>* sd se \<or> pa\<^sup>*\<^sup>* sd se)"
        by (metis (no_types) mono_rtranclp)
      then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
        using st by blast
      then show ?thesis
        using rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W by blast
    qed
  hence lev': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of S T] lev by auto
  hence confl': "\<forall>Ta. conflicting T = C_Clause Ta \<longrightarrow> trail T \<Turnstile>as CNot Ta"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by blast
  show ?case
    apply (rule cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned[OF _ _ c _ DH LH confl' c'])
    using s lev' IH c unfolding cdcl\<^sub>W_all_struct_inv_def by blast+
qed

lemma cdcl\<^sub>W_stgy_new_learned_clause:
  assumes "cdcl\<^sub>W_stgy S T" and
  "E \<notin># learned_clss S" and
  "E \<in># learned_clss T"
  shows "\<exists>S'. backtrack S S' \<and> conflicting S = C_Clause E \<and> full cdcl\<^sub>W_cp S' T"
  using assms
proof induction
  case conflict'
  thus ?case unfolding full1_def by (auto dest: tranclp_cdcl\<^sub>W_cp_learned_clause_inv)
next
  case (other' S T U) note o = this(1) and cp = this(3) and not_yet = this(4) and learned = this(5)
  have "E \<in># learned_clss T"
    using learned cp rtranclp_cdcl\<^sub>W_cp_learned_clause_inv unfolding full_def by auto
  hence "backtrack S T" and "conflicting S = C_Clause E"
    using cdcl\<^sub>W_o_new_clause_learned_is_backtrack_step[OF _ not_yet o] by blast+
  thus ?case using cp by blast
qed

lemma cdcl\<^sub>W_W_stgy_no_relearned_clause:
  assumes invR: "cdcl\<^sub>W_all_struct_inv R" and
  st': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
  bt: "backtrack S T" and
  confl: "conflicting S = C_Clause E" and
  already_learned: "E \<in># clauses S" and
  R: "trail R = []"
  shows False
proof -
  have M_lev: "cdcl\<^sub>W_M_level_inv R"
    using invR unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  obtain D L M1 M2_loc K i where
     T: "T \<sim> cons_trail (Propagated L ((D + {#L#})))
       (reduce_trail_to M1 (add_learned_cls (D + {#L#})
      (update_backtrack_lvl (get_maximum_level D (trail S)) (update_conflicting C_True S))))"
      and
    decomp: "(Marked K (Suc (get_maximum_level D (trail S))) # M1, M2_loc) \<in>
                set (get_all_marked_decomposition (trail S))" and
    k: "get_level L (trail S) = backtrack_lvl S" and
    level: "get_level L (trail S) = get_maximum_level (D+{#L#}) (trail S)" and
    confl_S: "conflicting S = C_Clause (D + {#L#})" and
    i: "i = get_maximum_level D (trail S)"
    using backtrackE[OF bt] by metis
  obtain M2 where
    M: "trail S = M2 @ Marked K (Suc i) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] unfolding i by (metis append_assoc)

  have invS: "cdcl\<^sub>W_all_struct_inv S"
    using invR rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W st' by blast
  hence conf: "cdcl\<^sub>W_conflicting S" unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have "trail S \<Turnstile>as CNot (D + {#L#})" unfolding cdcl\<^sub>W_conflicting_def confl_S by auto
  hence MD: "trail S \<Turnstile>as CNot D" by auto

  have lev': "cdcl\<^sub>W_M_level_inv S" using invS  unfolding cdcl\<^sub>W_all_struct_inv_def by blast

  have get_lvls_M: "get_all_levels_of_marked (trail S) = rev [1..<Suc (backtrack_lvl S)]"
    using lev' unfolding cdcl\<^sub>W_M_level_inv_def by auto

  have lev: "cdcl\<^sub>W_M_level_inv R" using invR unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  hence vars_of_D: "atms_of D \<subseteq> atm_of ` lits_of M1"
    using backtrack_atms_of_D_in_M1[OF _ T _ lev'] confl_S bt conf T decomp
    unfolding cdcl\<^sub>W_conflicting_def by auto
  have "no_dup (trail S)" using lev' by auto
  have vars_in_M1:
    "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lits_of (M2 @ [Marked K (get_maximum_level D (trail S) + 1)])"
      apply (rule vars_of_D distinct_atms_of_incl_not_in_other[of
      "M2 @ Marked K (get_maximum_level D (trail S) + 1) # []" M1 D])
      using \<open>no_dup (trail S)\<close> M vars_of_D by simp_all
  have M1_D: "M1 \<Turnstile>as CNot D"
    using vars_in_M1 true_annots_remove_if_notin_vars[of "M2 @ Marked K (i + 1) # []" M1 "CNot D"]
    \<open>trail S \<Turnstile>as CNot D\<close> M by simp

  have get_lvls_M: "get_all_levels_of_marked (trail S) = rev [1..<Suc (backtrack_lvl S)]"
    using lev' unfolding cdcl\<^sub>W_M_level_inv_def by auto
  hence "backtrack_lvl S > 0" unfolding M by (auto split: split_if_asm simp add: upt.simps(2))

  obtain M1' K' Ls where
    M': "trail S = Ls @ Marked K' (backtrack_lvl S) # M1'" and
    Ls: "\<forall>l \<in> set Ls. \<not> is_marked l" and
    "set M1 \<subseteq> set M1'"
    proof -
      let ?Ls = "takeWhile (Not o is_marked) (trail S)"
      have MLs: "trail S = ?Ls @ dropWhile (Not o is_marked) (trail S)"
        by auto
      have "dropWhile (Not o is_marked) (trail S) \<noteq> []" unfolding M by auto
      moreover from hd_dropWhile[OF this] have "is_marked(hd (dropWhile (Not o is_marked) (trail S)))"
        by simp
      ultimately obtain K' K'k where
        K'k: "dropWhile (Not o is_marked) (trail S)
          = Marked K' K'k # tl (dropWhile (Not o is_marked) (trail S))"
        by (cases "dropWhile (Not \<circ> is_marked) (trail S)";
            cases "hd (dropWhile (Not \<circ> is_marked) (trail S))")
          simp_all
      moreover have "\<forall>l \<in> set ?Ls. \<not>is_marked l" using set_takeWhileD by force
      moreover
        have "get_all_levels_of_marked (trail S)
                = K'k # get_all_levels_of_marked(tl (dropWhile (Not \<circ> is_marked) (trail S)))"
          apply (subst MLs, subst K'k)
          using calculation(2) by (auto simp add: get_all_levels_of_marked_no_marked)
        hence "K'k =  backtrack_lvl S"
        using calculation(2) by (auto split: split_if_asm simp add: get_lvls_M upt.simps(2))
      moreover have "set M1 \<subseteq> set (tl (dropWhile (Not o is_marked) (trail S)))"
        unfolding M by (induction M2) auto
      ultimately show ?thesis using that MLs by metis
    qed

  have get_lvls_M: "get_all_levels_of_marked (trail S) = rev [1..<Suc (backtrack_lvl S)]"
    using lev' unfolding cdcl\<^sub>W_M_level_inv_def by auto
  hence "backtrack_lvl S > 0" unfolding M by (auto split: split_if_asm simp add: upt.simps(2) i)

  have M1'_D: "M1' \<Turnstile>as CNot D" using M1_D \<open>set M1 \<subseteq> set M1'\<close> by (auto intro: true_annots_mono)
  have "-L \<in> lits_of (trail S)" using conf confl_S unfolding cdcl\<^sub>W_conflicting_def by auto
  have lvls_M1': "get_all_levels_of_marked M1' = rev [1..<backtrack_lvl S]"
    using get_lvls_M Ls by (auto simp add: get_all_levels_of_marked_no_marked M'
      split: split_if_asm simp add: upt.simps(2))
  have L_notin: "atm_of L \<in> atm_of ` lits_of Ls \<or> atm_of L = atm_of K'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "atm_of L \<notin> atm_of ` lits_of (Marked K' (backtrack_lvl S) # rev Ls)" by simp
      hence "get_level L (trail S) = get_level L M1'"
        unfolding M' by auto
      thus False using get_level_in_levels_of_marked[of L M1'] \<open>backtrack_lvl S > 0\<close>
      unfolding k lvls_M1' by auto
    qed
  obtain Y Z where
    RY: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R Y" and
    YZ: "cdcl\<^sub>W_stgy Y Z" and
    nt: "\<not> (\<exists>c. trail Y = c @ Marked K' (backtrack_lvl S) # M1' @ [])" and
    Z: "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Marked K' (backtrack_lvl S) # M1' @ []))\<^sup>*\<^sup>*
                Z S"
    using rtranclp_cdcl\<^sub>W_new_marked_at_beginning_is_decide'[OF  st' _ _ lev, of Ls K'
      "backtrack_lvl S" M1' "[]"]
    unfolding R M' by auto

  obtain M' where trZ: "trail Z = M' @ Marked K' (backtrack_lvl S) # M1'"
    using rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end[OF Z] M' by auto
  have "no_dup (trail Y)" using RY lev rtranclp_cdcl\<^sub>W_stgy_consistent_inv by blast
  then obtain Y' where
    dec: "decide Y Y'" and
    Y'Z: "full cdcl\<^sub>W_cp Y' Z" and
    "no_step cdcl\<^sub>W_cp Y"
    using cdcl\<^sub>W_stgy_trail_has_new_marked_is_decide_step[OF YZ nt Z] M' by auto
  have trY: "trail Y = M1'"
    proof -
      obtain M' where M: "trail Z = M' @ Marked K' (backtrack_lvl S) # M1'"
        using rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end[OF Z] M' by auto
      obtain M'' where M'': "trail Z = M'' @ trail Y'" and "\<forall>m\<in>set M''. \<not>is_marked m"
        using Y'Z rtranclp_cdcl\<^sub>W_cp_dropWhile_trail' unfolding full_def by blast
      obtain M''' where "trail Y' = M''' @ Marked K' (backtrack_lvl S) # M1'"
        using M'' unfolding M
        by (metis (no_types, lifting) \<open>\<forall>m\<in>set M''. \<not> is_marked m\<close> beginning_not_marked_invert)
      thus ?thesis using dec nt  by (induction M''') auto
    qed
  have Y_CT: "conflicting Y = C_True" using \<open>decide Y Y'\<close> by auto
  have "cdcl\<^sub>W\<^sup>*\<^sup>* R Y" by (simp add: RY rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W)
  hence "init_clss Y = init_clss R" using rtranclp_cdcl\<^sub>W_init_clss[of R Y] by auto
  { assume DL: "D + {#L#} \<in># clauses Y"
    have "atm_of L \<notin> atm_of ` lits_of M1"
      apply (rule backtrack_lit_skiped[of _ S])
      using decomp i k lev' unfolding cdcl\<^sub>W_M_level_inv_def by auto
    hence LM1: "undefined_lit M1 L"
      by (metis Marked_Propagated_in_iff_in_lits_of atm_of_uminus image_eqI)
    have L_trY: "undefined_lit (trail Y) L"
      using  L_notin \<open>no_dup (trail S)\<close> unfolding defined_lit_map trY M'
      by (auto simp add: image_iff lits_of_def)
    have "\<exists> Y'. propagate Y Y'"
      using propagate_rule[of Y] DL M1'_D L_trY Y_CT trY DL by (metis state_eq_ref)
    hence False using \<open>no_step cdcl\<^sub>W_cp Y\<close>  propagate' by blast
  }
  moreover {
    assume DL: "D + {#L#} \<notin># clauses Y"
    have lY_lZ: "learned_clss Y = learned_clss Z"
      using dec Y'Z rtranclp_cdcl\<^sub>W_cp_learned_clause_inv[of Y' Z] unfolding full_def
      by auto
    have invZ: "cdcl\<^sub>W_all_struct_inv Z"
      by (meson RY YZ invR r_into_rtranclp rtranclp_cdcl\<^sub>W_all_struct_inv_inv
        rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W)
    have "D + {#L#} \<notin>#learned_clss S"
      apply (rule rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned[OF Z invZ trZ])
         using DL lY_lZ unfolding clauses_def apply simp
        apply (metis (no_types, lifting) \<open>set M1 \<subseteq> set M1'\<close> image_mono order_trans
          vars_of_D lits_of_def)
       using L_notin \<open>no_dup (trail S)\<close> unfolding M' by (auto simp add: image_iff lits_of_def)
    hence False
      using already_learned DL confl  st' unfolding M'
      by (simp add: \<open>init_clss Y = init_clss R\<close> clauses_def confl_S
        rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
  }
  ultimately show False by blast
qed

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv R" and
  st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
  dist: "distinct_mset (clauses R)" and
  R: "trail R = []"
  shows "distinct_mset (clauses S)"
  using st
proof (induction)
  case base
  then show ?case using dist by simp
next
  case (step S T) note st = this(1) and s = this(2) and IH = this(3)
  from s show ?case
    proof (cases rule: cdcl\<^sub>W_stgy.cases)
      case conflict'
      then show ?thesis using IH unfolding full1_def by (auto dest: tranclp_cdcl\<^sub>W_cp_no_more_clauses)
    next
      case (other' S') note o = this(1) and full = this(3)
      have [simp]: "clauses T = clauses S'"
        using full unfolding full_def by (auto dest: rtranclp_cdcl\<^sub>W_cp_no_more_clauses)
      show ?thesis
        using o IH
        proof (cases rule: cdcl\<^sub>W_o_rule_cases)
          case backtrack
          then obtain E where
            "conflicting S = C_Clause E" and
            cls_S': "clauses S' = {#E#} + clauses S"
            by auto
          then have "E \<notin># clauses S"
            using cdcl\<^sub>W_W_stgy_no_relearned_clause R invR local.backtrack st by blast
          then show ?thesis using IH by (simp add: distinct_mset_add_single cls_S')
        qed auto
    qed
qed

lemma cdcl\<^sub>W_W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S" and
    no_duplicate_clause: "distinct_mset N" and
    no_duplicate_in_clause: "distinct_mset_mset N"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF _ st] assms
  by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def)

subsection \<open>Decrease of a measure\<close>
fun cdcl\<^sub>W_measure where
"cdcl\<^sub>W_measure S =
  [(3::nat) ^ (card (atms_of_mu (init_clss S))) - card (set_mset (learned_clss S)),
    if conflicting S = C_True then 1 else 0,
    if conflicting S = C_True then card (atms_of_mu (init_clss S)) - length (trail S)
    else length (trail S)
    ]"

lemma length_model_le_vars_all_inv:
  assumes "cdcl\<^sub>W_all_struct_inv S"
  shows "length (trail S) \<le> card (atms_of_mu (init_clss S))"
  using assms length_model_le_vars[of S] unfolding cdcl\<^sub>W_all_struct_inv_def by auto
end

locale cdcl\<^sub>W_termination =
   cdcl\<^sub>W_ops trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
   add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for
    trail :: "'st::equal \<Rightarrow> ('v::linorder, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

lemma learned_clss_less_upper_bound:
  fixes S :: "'st"
  assumes
    "distinct_cdcl\<^sub>W_state S" and
    "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "card(set_mset (learned_clss S)) \<le> 3 ^ card (atms_of_mu (learned_clss S))"
proof -
  have "set_mset (learned_clss S) \<subseteq> build_all_simple_clss (atms_of_mu (learned_clss S))"
    apply (rule simplified_in_build_all)
    using assms unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have "card(set_mset (learned_clss S))
    \<le> card (build_all_simple_clss (atms_of_mu (learned_clss S)))"
    by (simp add: build_all_simple_clss_finite card_mono)
  then show ?thesis
    by (meson atms_of_m_finite build_all_simple_clss_card finite_set_mset order_trans)
qed

lemma lexn3[intro!, simp]:
  "a < a' \<or> (a = a' \<and> b < b') \<or> (a = a' \<and> b = b' \<and> c < c')
    \<Longrightarrow> ([a::nat, b, c], [a', b', c']) \<in> lexn {(x, y). x < y} 3"
  apply auto
  unfolding lexn_conv apply fastforce
  unfolding lexn_conv apply auto
  apply (metis append.simps(1) append.simps(2))+
  done

lemma cdcl\<^sub>W_measure_decreasing:
  fixes S :: "'st"
  assumes
    "cdcl\<^sub>W S S'" and
    no_restart:
      "\<not>(learned_clss S \<subseteq># learned_clss S' \<and> [] = trail S' \<and> conflicting S' = C_True)"
    (*no restart*) and
    "learned_clss S \<subseteq># learned_clss S'" (*no forget*) and
    no_relearn: "\<And>S'. backtrack S S' \<Longrightarrow> \<forall>T. conflicting S = C_Clause T \<longrightarrow> T \<notin># learned_clss S"
      and
    alien: "no_strange_atm S" and
    M_level: "cdcl\<^sub>W_M_level_inv S" and
    no_taut: "\<forall>s \<in># learned_clss S. \<not>tautology s" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms(1-3)
proof (induct rule: cdcl\<^sub>W_all_induct)
  case (propagate C L) note T = this(4) and conf = this(5)
  have propa: "propagate S (cons_trail (Propagated L (C + {#L#})) S)"
    using propagate_rule[OF _ propagate.hyps(1,2)] propagate.hyps by auto
  hence no_dup': "no_dup (Propagated L ( (C + {#L#})) # trail S)"
    by (metis cdcl\<^sub>W_M_level_inv_decomp(2) cdcl\<^sub>W_cp.simps cdcl\<^sub>W_cp_consistent_inv trail_cons_trail
      M_level)

  let ?N = "init_clss S"
  have "no_strange_atm (cons_trail (Propagated L (C + {#L#})) S)"
    using alien cdcl\<^sub>W.propagate cdcl\<^sub>W_no_strange_atm_inv propa by blast
  then have  "atm_of ` lits_of (Propagated L ( (C + {#L#})) # trail S)
    \<subseteq> atms_of_mu (init_clss S)"
    unfolding no_strange_atm_def by auto
  hence "card (atm_of ` lits_of (Propagated L ( (C + {#L#})) # trail S))
    \<le> card (atms_of_mu (init_clss S))"
    by (meson atms_of_m_finite card_mono finite_set_mset)
  hence "length (Propagated L ( (C + {#L#})) # trail S) \<le> card (atms_of_mu ?N)"
    using no_dup_length_eq_card_atm_of_lits_of no_dup' by fastforce
  hence H: "card (atms_of_mu (init_clss S)) - length (trail S)
    = Suc (card (atms_of_mu (init_clss S)) - Suc (length (trail S)))"
    by simp
  show ?case using conf T by (auto simp: H)
next
  case (decide L) note conf = this(1) and T = this(4)
  moreover
    have dec: "decide S (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      using decide.intros decide.hyps by force
    hence cdcl\<^sub>W:"cdcl\<^sub>W S (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      using cdcl\<^sub>W.simps by blast
  moreover
    have no_dup: "no_dup (Marked L (backtrack_lvl S + 1) # trail S)"
      using cdcl\<^sub>W M_level cdcl\<^sub>W_consistent_inv[OF cdcl\<^sub>W] unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "no_strange_atm (cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S))"
      using calculation cdcl\<^sub>W_no_strange_atm_inv alien by blast
    hence "length (Marked L ((backtrack_lvl S) + 1) # (trail S)) \<le> card (atms_of_mu (init_clss S))"
      using no_dup clauses_def
      length_model_le_vars[of "cons_trail (Marked L (backtrack_lvl S + 1)) (incr_lvl S)"]
      by fastforce
  ultimately show ?case using conf by auto
next
  case (skip L C' M D) note tr = this(1) and conf = this(2) and T = this(5)
  show ?case using conf T unfolding clauses_def by (simp add: tr)
next
  case conflict
  thus ?case by simp
next
  case resolve
  thus ?case using finite unfolding clauses_def by simp
next
  case (backtrack K i M1 M2 L D T) note S = this(1) and conf = this(3) and T =this(6)
  let ?S' = "T"
  have bt: "backtrack S ?S'"
    using backtrack.hyps backtrack.intros[of S _ _ _ _ D L K i] by auto
  have "D + {#L#} \<notin># learned_clss S"
    using no_relearn conf bt by auto
  hence card_T:
    "card (set_mset ({#D + {#L#}#} + learned_clss S)) = Suc (card (set_mset (learned_clss S)))"
    by (simp add:)
  have "distinct_cdcl\<^sub>W_state ?S'"
    using bt by (meson bj cdcl\<^sub>W_bj.backtrack distinct_cdcl\<^sub>W_state_inv no_dup other)
  moreover have "\<forall>s\<in>#learned_clss ?S'. \<not> tautology s"
    using learned_clss_are_not_tautologies[OF cdcl\<^sub>W.other[OF cdcl\<^sub>W_o.bj[OF cdcl\<^sub>W_bj.backtrack[OF bt]]]]
    M_level no_taut confl by auto
  ultimately have "card (set_mset (learned_clss T)) \<le> 3 ^ card (atms_of_mu (learned_clss T))"
      by (auto simp: clauses_def learned_clss_less_upper_bound)
    then have H: "card (set_mset ({#D + {#L#}#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mu ({#D + {#L#}#} + learned_clss S))"
      using T by auto
  moreover
    have "atms_of_mu ({#D + {#L#}#} + learned_clss S) \<subseteq> atms_of_mu (init_clss S)"
      using alien conf unfolding no_strange_atm_def by auto
    hence card_f: "card (atms_of_mu ({#D + {#L#}#} + learned_clss S))
      \<le> card (atms_of_mu (init_clss S))"
      by (meson atms_of_m_finite card_mono finite_set_mset)
    hence "(3::nat) ^ card (atms_of_mu ({#D + {#L#}#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mu (init_clss S))" by simp
  ultimately have "(3::nat) ^ card (atms_of_mu (init_clss S))
    \<ge> card (set_mset ({#D + {#L#}#} + learned_clss S))"
    using le_trans by blast
  thus ?case using S
    using diff_less_mono2 card_T T by auto
next
  case restart
  thus ?case using alien by (auto simp: state_eq_def simp del: state_simp)
next
  case (forget C T)
  then have "C \<in># learned_clss S" and "C \<notin># learned_clss T"
    by auto
  then show ?case using forget(8) by (simp add: mset_leD)
qed

lemma propagate_measure_decreasing:
  fixes S :: "'st"
  assumes "propagate S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl\<^sub>W_measure_decreasing)
  using assms(1) propagate apply blast
           using assms(1) apply (auto simp add: propagate.simps)[3]
        using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
  done

lemma conflict_measure_decreasing:
  fixes S :: "'st"
  assumes "conflict S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl\<^sub>W_measure_decreasing)
  using assms(1) conflict apply blast
            using assms(1) apply (auto simp add: propagate.simps)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
  done

lemma decide_measure_decreasing:
  fixes S :: "'st"
  assumes "decide S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl\<^sub>W_measure_decreasing)
  using assms(1) decide other apply blast
            using assms(1) apply (auto simp add: propagate.simps)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
  done

lemma trans_le:
  "trans {(a, (b::nat)). a < b}"
  unfolding trans_def by auto

lemma cdcl\<^sub>W_cp_measure_decreasing:
  fixes S :: "'st"
  assumes "cdcl\<^sub>W_cp S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms
proof induction
  case conflict'
  thus ?case using conflict_measure_decreasing by blast
next
  case propagate'
  thus ?case using propagate_measure_decreasing by blast
qed

lemma tranclp_cdcl\<^sub>W_cp_measure_decreasing:
  fixes S :: "'st"
  assumes "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_measure S', cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms
proof induction
  case base
  thus ?case using cdcl\<^sub>W_cp_measure_decreasing by blast
next
  case (step T U) note st = this(1) and step = this(2) and IH =this(3) and inv = this(4)
  hence "(cdcl\<^sub>W_measure T, cdcl\<^sub>W_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3" by blast

  moreover have "(cdcl\<^sub>W_measure U, cdcl\<^sub>W_measure T) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3"
    using cdcl\<^sub>W_cp_measure_decreasing[OF step] rtranclp_cdcl\<^sub>W_all_struct_inv_inv inv
    tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W[OF st]
    unfolding trans_def rtranclp_unfold
    by blast
  ultimately show ?case using lexn_transI[OF trans_le] unfolding trans_def by blast
qed

lemma cdcl\<^sub>W_stgy_step_decreasing:
  fixes R S T :: "'st"
  assumes "cdcl\<^sub>W_stgy S T" and
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S"
  "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_measure T, cdcl\<^sub>W_measure S) \<in> lexn {(a, b). a < b} 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv S"
    using assms
    by (metis rtranclp_unfold rtranclp_cdcl\<^sub>W_all_struct_inv_inv tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W)
  with assms show ?thesis
    proof induction
      case (conflict' U V) note cp = this(1) and inv = this(5)
      show ?case
         using tranclp_cdcl\<^sub>W_cp_measure_decreasing[OF HOL.conjunct1[OF cp[unfolded full1_def]] inv]
         .
    next
      case (other' S T U) note H= this(1,4,5,6,7) and cp = this(3)
      have "cdcl\<^sub>W_all_struct_inv T"
        using cdcl\<^sub>W_all_struct_inv_inv other other'.hyps(1) other'.prems(4) by blast
      from tranclp_cdcl\<^sub>W_cp_measure_decreasing[OF _ this]
      have le_or_eq: "(cdcl\<^sub>W_measure U, cdcl\<^sub>W_measure T) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3 \<or>
        cdcl\<^sub>W_measure U = cdcl\<^sub>W_measure T"
        using cp unfolding full_def rtranclp_unfold by blast
      moreover
        from H have "(cdcl\<^sub>W_measure T, cdcl\<^sub>W_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3"
        proof (induction rule:cdcl\<^sub>W_o.induct)
          case (decide S T)
          thus ?case using decide_measure_decreasing by blast
        next
          case (bj S T) note bt = this(1) and st = this(2) and R = this(3)
            and invR = this(4) and inv = this(5)
          thus ?case
            proof cases
              case (backtrack) note bt = this(1)
                have no_relearn: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> T \<notin># learned_clss S"
                  using cdcl\<^sub>W_W_stgy_no_relearned_clause[OF invR st] invR st bt R cdcl\<^sub>W_all_struct_inv_def
                  clauses_def by auto
                show ?thesis
                  apply (rule cdcl\<^sub>W_measure_decreasing)
                          using bt cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj other apply simp
                         using bt apply auto[]
                        using bt apply auto[]
                       using bt no_relearn apply auto[]
                      using inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
                     using inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
                    using inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
                   using inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
                  using inv unfolding cdcl\<^sub>W_all_struct_inv_def by simp
            next
              case skip
              then show ?thesis by (elim skipE) force
              (* the elim is not needed, but make the proof a lot faster *)
            next
              case resolve
              then show ?thesis by (elim resolveE) force
              (* the elim is not needed, but make the proof a lot faster *)
            qed
        qed
      ultimately show ?case
         proof -
           have "cdcl\<^sub>W_measure U = cdcl\<^sub>W_measure T \<longrightarrow> (cdcl\<^sub>W_measure U, cdcl\<^sub>W_measure S)
             \<in> lexn {p. case p of (n, na) \<Rightarrow> n < na} 3"
             using \<open>(cdcl\<^sub>W_measure T, cdcl\<^sub>W_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3\<close>
             by presburger
           thus ?thesis
             using lexn_transI[OF trans_le, of 3] \<open>(cdcl\<^sub>W_measure T, cdcl\<^sub>W_measure S)
               \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3\<close> le_or_eq unfolding trans_def by blast
         qed
    qed
qed

lemma tranclp_cdcl\<^sub>W_stgy_decreasing:
  fixes R S T :: 'st
  assumes "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ R S"
  "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_measure S, cdcl\<^sub>W_measure R) \<in> lexn {(a, b). a < b} 3"
  using assms
  apply induction
   using cdcl\<^sub>W_stgy_step_decreasing[of R _ R] apply blast
  using cdcl\<^sub>W_stgy_step_decreasing[of _ _ R]  tranclp_into_rtranclp[of cdcl\<^sub>W_stgy R]
  lexn_transI[OF trans_le, of 3] unfolding trans_def by blast

lemma tranclp_cdcl\<^sub>W_stgy_S0_decreasing:
  fixes R S T :: 'st
  assumes pl: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S" and
  no_dup: "distinct_mset_mset N"
  shows "(cdcl\<^sub>W_measure S, cdcl\<^sub>W_measure (init_state N)) \<in> lexn {(a, b). a < b} 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_dup unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  thus ?thesis using pl tranclp_cdcl\<^sub>W_stgy_decreasing init_state_trail by blast
qed

lemma wf_tranclp_cdcl\<^sub>W_stgy:
  "wf {(S::'st, init_state N)| S N. distinct_mset_mset N \<and> cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S}"
  apply (rule wf_wf_if_measure'_notation2[of "lexn {(a, b). a < b} 3" _ _ cdcl\<^sub>W_measure])
   apply (simp add: wf wf_lexn)
  using tranclp_cdcl\<^sub>W_stgy_S0_decreasing by blast
end

end
