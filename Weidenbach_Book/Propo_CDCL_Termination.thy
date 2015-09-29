theory Propo_CDCL_Termination
imports Propo_CDCL
begin

definition cdcl_all_inv_mes where
  "cdcl_all_inv_mes S =
    (no_strange_atm S \<and> cdcl_M_level_inv S \<and>  finite (atms_of_m (clauses S))
    \<and>  finite (learned_clauses S) \<and>  (\<forall>s \<in> learned_clauses S. \<not>tautology s)
    \<and>  distinct_cdcl_state S \<and> cdcl_conflicting S \<and> all_decomposition_implies (clauses S) (get_all_marked_decomposition (trail S)) \<and> cdcl_learned_clause S)"

lemma cdcl_all_inv_mes_inv:
  assumes "cdcl S S'" and "cdcl_all_inv_mes S"
  shows "cdcl_all_inv_mes S'"
  unfolding cdcl_all_inv_mes_def
proof (intro HOL.conjI)
  show "no_strange_atm S'"
    using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast
  show "cdcl_M_level_inv S'"
    using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast
  show "distinct_cdcl_state S'"
     using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast
  show "cdcl_conflicting S'"
     using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast
  show "all_decomposition_implies (clauses S') (get_all_marked_decomposition (trail S'))"
     using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast
  show "cdcl_learned_clause S'"
     using cdcl_all_inv[OF assms(1)] assms(2) unfolding cdcl_all_inv_mes_def by fast

  have "finite (atms_of_m (clauses S))" using assms(2) unfolding cdcl_all_inv_mes_def by auto
  with assms(1) show "finite (atms_of_m (clauses S'))" by (induction rule: cdcl_all_induct) auto

  have "finite (learned_clauses S)" using assms(2) unfolding cdcl_all_inv_mes_def by auto
  with assms(1) show "finite (learned_clauses S')" by (induction rule: cdcl_all_induct) auto

  show "\<forall>s\<in>learned_clauses S'. \<not> tautology s"
    using assms(1)[THEN learned_clauses_are_not_tautologies] assms(2)
    unfolding cdcl_all_inv_mes_def by fast
qed

lemma rtranclp_cdcl_all_inv_mes_inv:
  assumes "cdcl\<^sup>*\<^sup>* S S'" and "cdcl_all_inv_mes S"
  shows "cdcl_all_inv_mes S'"
  using assms by induction (auto intro: cdcl_all_inv_mes_inv)


lemma cdcl_o_learned_clause_increasing:
  "cdcl_o S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  by (induction rule: cdcl_o_induct) auto

lemma cdcl_cp_learned_clause_increasing:
  "cdcl_cp S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  by (induction rule: cdcl_cp.induct) auto

lemma rtranclp_cdcl_cp_learned_clause_increasing:
  "cdcl_cp\<^sup>*\<^sup>* S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  by (induction rule: rtranclp.induct) (auto dest: cdcl_cp_learned_clause_increasing)

lemma full_cdcl_cp_learned_clause_increasing:
  "full cdcl_cp S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  "full0 cdcl_cp S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  unfolding full_def full0_def
  by (simp_all add: rtranclp_cdcl_cp_learned_clause_increasing rtranclp_unfold)

lemma cdcl_s_learned_clause_increasing:
  "cdcl_s S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  by (induction rule: cdcl_s.induct)
     (auto dest!: full_cdcl_cp_learned_clause_increasing cdcl_o_learned_clause_increasing)

lemma rtranclp_cdcl_s_learned_clause_increasing:
  "cdcl_s\<^sup>*\<^sup>* S S' \<Longrightarrow> learned_clauses S \<subseteq> learned_clauses S'"
  by (induction rule: rtranclp.induct)
     (auto dest!: cdcl_s_learned_clause_increasing)

section \<open>decreasing of the measure\<close>
lemma cdcl_o_new_clause_learned_is_backtrack_step:
  assumes learned: "D \<in> learned_clauses T" and
  new: "D \<notin> learned_clauses S" and
  cdcl: "cdcl_o S T"
  shows "backtrack S T \<and> conflicting S = C_Clause D"
  using cdcl learned new by (induction rule: cdcl_o.induct) auto

lemma cdcl_cp_new_clause_learned_has_backtrack_step:
  assumes learned: "D \<in> learned_clauses T" and
  new: "D \<notin> learned_clauses S" and
  cdcl: "cdcl_s S T"
  shows "\<exists>S'. backtrack S S' \<and> cdcl_s\<^sup>*\<^sup>* S' T \<and> conflicting S = C_Clause D"
  using cdcl learned new
proof (induction rule: cdcl_s.induct)
  case (conflict' S S')
  thus ?case
    unfolding full_def by (metis (mono_tags, lifting) rtranclp_cdcl_cp_learned_clause_inv
      tranclp_into_rtranclp)
next
  case (other' S S' S'')
  hence "D \<in> learned_clauses S'"
    unfolding full0_def by (auto dest: rtranclp_cdcl_cp_learned_clause_inv)
  thus ?case
    using  cdcl_o_new_clause_learned_is_backtrack_step[OF _ `D \<notin> learned_clauses S` `cdcl_o S S'`]
    `full0 cdcl_cp S' S''` by (metis cdcl_s.conflict' full0_unfold r_into_rtranclp
      rtranclp.rtrancl_refl)
qed

lemma rtranclp_cdcl_cp_new_clause_learned_has_backtrack_step:
  assumes learned: "D \<in> learned_clauses T" and
  new: "D \<notin> learned_clauses S" and
  cdcl: "cdcl_s\<^sup>*\<^sup>* S T"
  shows "\<exists>S' S''. cdcl_s\<^sup>*\<^sup>* S S' \<and> backtrack S' S'' \<and> conflicting S' = C_Clause D \<and> cdcl_s\<^sup>*\<^sup>* S'' T"
  using cdcl learned new
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl S)
  thus ?case
    using cdcl_cp_new_clause_learned_has_backtrack_step by blast
next
  case (rtrancl_into_rtrancl S T U) note st =this(1) and o = this(2) and IH = this(3) and
    D_U = this(4) and D_S = this(5)
  show ?case
    proof (cases "D \<in> learned_clauses T")
      case True
      then obtain S' S'' where
        st': "cdcl_s\<^sup>*\<^sup>* S S'" and
        bt: "backtrack S' S''" and
        confl: "conflicting S' = C_Clause D" and
        st'': "cdcl_s\<^sup>*\<^sup>* S'' T"
        using IH D_S by metis
      thus ?thesis using o by (meson rtranclp.simps)
    next
      case False
      obtain S' where
        bt: "backtrack T S'" and
        st': "cdcl_s\<^sup>*\<^sup>* S' U" and
        confl: "conflicting T = C_Clause D"
        using cdcl_cp_new_clause_learned_has_backtrack_step[OF D_U False o] by metis
      hence "cdcl_s\<^sup>*\<^sup>* S T" and 
        "backtrack T S'" and 
        "conflicting T = C_Clause D" and 
        "cdcl_s\<^sup>*\<^sup>* S' U"
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

lemma cdcl_cp_no_more_Marked_lit:
  assumes "cdcl_cp S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms apply (induct rule: cdcl_cp.induct)
  using conflict_no_more_Marked_lit propagate_no_more_Marked_lit by blast+

lemma rtranclp_cdcl_cp_no_more_Marked_lit:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "Marked K i \<in> set (trail S) \<longleftrightarrow> Marked K i \<in> set (trail S')"
  using assms apply (induct rule: rtranclp.induct)
  using cdcl_cp_no_more_Marked_lit by blast+

lemma cdcl_o_no_more_Marked_lit:
  assumes "cdcl_o S S'" and "\<not> decided S S'"
  shows "Marked K i \<in> set (trail S') \<longrightarrow> Marked K i \<in> set (trail S)"
  using assms
proof (induct rule: cdcl_o.induct)
  case backtrack
  have H: "\<And>A M M1. M = A @ M1 \<Longrightarrow>  Marked K i \<in> set M1 \<Longrightarrow> Marked K i \<in> set M"  by auto
  show ?case
    using backtrack(1) by (auto dest!: H get_all_marked_decomposition_exists_prepend)
qed (fastforce dest!: get_all_marked_decomposition_exists_prepend)+

lemma cdcl_new_marked_at_beginning_is_decided:
  assumes "cdcl_s S S'" and
  "no_dup (trail S')" and
  "trail S' = M' @ Marked L i # M" and
  "trail S = M"
  shows "\<exists>T. decided S T \<and> no_step propagate S \<and> no_step conflict S"
  using assms
proof (induct rule: cdcl_s.induct)
  case (conflict' S S') note st =this(1) and no_dup = this(2) and S' = this(3) and S = this(4)
  have "Marked L i \<in> set (trail S')" and "Marked L i \<notin> set (trail S)"
    using no_dup unfolding S S' by (auto simp add: rev_image_eqI)
  hence False
    using st rtranclp_cdcl_cp_no_more_Marked_lit[of S S']
    unfolding full_def rtranclp_unfold by blast
  thus ?case by fast
next
  case (other' S T U) note o =this(1) and ns = this(2,3) and st = this(4) and no_dup = this(5) and S' = this(6) and S = this(7)
  have "Marked L i \<in> set (trail U)" and "Marked L i \<notin> set (trail S)"
    using no_dup unfolding S S' by (auto simp add: rev_image_eqI)
  hence "Marked L i \<in> set (trail T)"
    using st rtranclp_cdcl_cp_no_more_Marked_lit unfolding full0_def by blast
  thus ?case using cdcl_o_no_more_Marked_lit[OF o] `Marked L i \<notin> set (trail S)` ns by blast
qed

lemma cdcl_cp_dropWhile_trail':
  assumes "cdcl_cp S S'"
  obtains M where "trail S' = M @ trail S" and " (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) fastforce+

lemma rtranclp_cdcl_cp_dropWhile_trail':
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  obtains M :: "('a, nat, 'a literal multiset) marked_lit list" where
    "trail S' = M @ trail S" and "\<forall>l \<in> set M. \<not>is_marked l"
  using assms by (induction) (fastforce dest!: cdcl_cp_dropWhile_trail')+

lemma cdcl_cp_dropWhile_trail:
  assumes "cdcl_cp S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) fastforce+

lemma rtranclp_cdcl_cp_dropWhile_trail:
  assumes "cdcl_cp\<^sup>*\<^sup>* S S'"
  shows "\<exists>M. trail S' = M @ trail S \<and> (\<forall>l \<in> set M. \<not>is_marked l)"
  using assms by (induction) (fastforce dest: cdcl_cp_dropWhile_trail)+

lemma cdcl_o_is_decided:
  assumes "cdcl_o S' T" and
  "trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M"and
  "\<not> (\<exists>M'. trail S' = M' @ Marked L i # H @ M)"
  shows "decided S' T"
      using assms
proof (induction rule:cdcl_o_induct)
  case (backtrack M N U k D L K i M1 M2)
  then obtain c where " M = c @ M2 @ Marked K (Suc (get_maximum_level D M)) # M1"
    by (auto dest!: get_all_marked_decomposition_exists_prepend)
  thus ?case
    using backtrack
    by (cases "drop (length M\<^sub>0) M'") auto
next
  case (decided)
  show ?case using deciding[OF _ decided(1,2)] by auto
qed auto

lemma rtranclp_cdcl_new_marked_at_beginning_is_decided:
  assumes "cdcl_s\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Marked L i # H @ M" and
  "trail R = M" and
  "cdcl_M_level_inv R"
  shows
    "\<exists>S T T'. cdcl_s\<^sup>*\<^sup>* R S \<and> decided S T \<and> cdcl_s\<^sup>*\<^sup>* T U \<and> cdcl_s\<^sup>*\<^sup>* S U \<and> no_step propagate S \<and>
      no_step conflict S \<and> trail T = Marked L i # H @ M \<and> trail S = H @ M \<and> cdcl_s S T' \<and>
      cdcl_s\<^sup>*\<^sup>* T' U"
  using assms
proof (induct arbitrary: M H M' i rule: rtranclp.induct)
  case (rtrancl_refl a)
  thus ?case by auto
next
  case (rtrancl_into_rtrancl S T U) note st = this(1) and IH = this(2) and s = this(3) and U = this(4) and S = this(5) and lev = this(6)
  show ?case
    proof (cases "\<exists>M'. trail T = M' @ Marked L i # H @ M")
      case False
      with s show ?thesis using U s st S
        proof (induction)
          case (conflict' V W) note cp = this(1) and  nd = this(2) and W = this(3)
          then obtain M\<^sub>0 where "trail W = M\<^sub>0 @ trail V" and nmarked: "\<forall>l\<in>set M\<^sub>0. \<not> is_marked l"
            using rtranclp_cdcl_cp_dropWhile_trail unfolding full_def rtranclp_unfold by blast
          hence MV: "M' @ Marked L i # H @ M = M\<^sub>0 @ trail V" unfolding W by simp
          hence V: "trail V = drop (length M\<^sub>0) (M' @ Marked L i # H @ M)"
            by auto
          have "takeWhile (Not o is_marked) M' = M\<^sub>0  @ takeWhile (Not \<circ> is_marked) (trail V)"
            using arg_cong[OF MV, of "takeWhile (Not o is_marked)"] nmarked
            by (simp add: takeWhile_tail)
          from arg_cong[OF this, of length] have "length M\<^sub>0 \<le> length M'"
            unfolding length_append by (metis (no_types, lifting) Nat.le_trans le_add1 length_takeWhile_le)
          hence False using nd V by (cases V) auto
          thus ?case by fast
        next
          case (other' S' T U) note o = this(1) and ns =this(2,3) and cp = this(4) and nd = this(5) and U = this(6) and st = this(7)
          obtain M\<^sub>0 where "trail U = M\<^sub>0 @ trail T" and nmarked: "\<forall>l\<in>set M\<^sub>0. \<not> is_marked l"
            using rtranclp_cdcl_cp_dropWhile_trail cp unfolding full0_def by blast
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
            have "decided S' T" using o nd tr_T cdcl_o_is_decided by blast
          ultimately  have "decided S' T" using cdcl_o_no_more_Marked_lit[OF o] by blast
          then have 1: "cdcl_s\<^sup>*\<^sup>* S S'" and 2: "decided S' T" and 3: "cdcl_s\<^sup>*\<^sup>* T U"
            using st other'.prems(4)
            by (metis cdcl_s.conflict' cp full0_unfold r_into_rtranclp rtranclp.rtrancl_refl)+
          have [simp]: "drop (length M\<^sub>0) M' = []"
            using `decided S' T` `Marked L i \<in> set (trail T)`  nd tr_T
            by (auto simp add: Cons_eq_append_conv)
          have T: "drop (length M\<^sub>0) M' @ Marked L i # H @ M = Marked L i # trail S'"
            using `decided S' T` `Marked L i \<in> set (trail T)`  nd tr_T
            by auto
          have "trail T = Marked L i # trail S'"
            using `decided S' T` `Marked L i \<in> set (trail T)` tr_T
            by auto
          hence 5: "trail T = Marked L i # H @ M"and 6: "trail S' = H @ M"
            proof -
              show "trail S' = H @ M"
                by (metis (no_types) `trail T = Marked L i # trail S'` `trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M` append_Nil list.sel(3) nd tl_append2) (* 414 ms *)
            next
              show "trail T = Marked L i # H @ M"
                using append.simps(1) list.sel(3) local.other'(5) tl_append2 by (metis (no_types) `trail T = Marked L i # trail S'` `trail T = drop (length M\<^sub>0) M' @ Marked L i # H @ M` )
            qed
          have 7: "cdcl_s\<^sup>*\<^sup>* S' U" using other'.prems(4) st by auto
          have 8: "cdcl_s S' U" "cdcl_s\<^sup>*\<^sup>* U U"
            using cdcl_s.other'[OF other'(1-4)] by simp_all
          show ?case apply (rule exI[of _ S'], rule exI[of _ T], rule exI[of _ U])
            using ns 1 2 3 5 6 7 8 by fast

        qed
    next
      case True
      then obtain M' where T: "trail T = M' @ Marked L i # H @ M" by metis
      from IH[OF this S lev] obtain S' S'' S''' where
        1: "cdcl_s\<^sup>*\<^sup>* S S'" and
        2: "decided S' S''" and
        3: "cdcl_s\<^sup>*\<^sup>* S'' T " and
        4: "no_step propagate S'" and
        5: "no_step conflict S'" and
        6: "trail S'' = Marked L i # H @ M" and
        7: "trail S' = H @ M" and
        8: "cdcl_s\<^sup>*\<^sup>* S' T" and
        9: "cdcl_s S' S'''" and
        10: "cdcl_s\<^sup>*\<^sup>* S''' T"
           by blast
      have "cdcl_s\<^sup>*\<^sup>* S'' U" using s `cdcl_s\<^sup>*\<^sup>* S'' T ` by auto
      moreover have "cdcl_s\<^sup>*\<^sup>* S' U" using "8" s by auto
      moreover have "cdcl_s\<^sup>*\<^sup>* S''' U" using 10 s by auto
      ultimately show ?thesis apply - apply (rule exI[of _ S'], rule exI[of _ S''])
        using 1 2 4 5 6 7 8 9  by blast
    qed
qed

lemma rtranclp_exists_last_with_prop:
  assumes "R x z"
  and "R\<^sup>*\<^sup>* z z'" and "P x z"
  shows "\<exists>y y'. R\<^sup>*\<^sup>* x y \<and> R y y' \<and> P y y' \<and> (\<lambda>a b. R a b \<and> \<not>P a b)\<^sup>*\<^sup>* y' z'"
  using assms(2,1,3)
proof (induction arbitrary: )
  case base
  thus ?case by auto
next
  case (step z' z'') note z = this(2) and IH =this(3)[OF this(4-5)]
  show ?case
    apply (cases "P z' z''")
      apply (rule exI[of _ z'], rule exI[of _ z''])
      using z assms(1) step.hyps(1) step.prems(2) apply auto[1]
    using IH z  rtranclp.rtrancl_into_rtrancl by fastforce
qed

lemma rtranclp_cdcl_new_marked_at_beginning_is_decided':
  assumes "cdcl_s\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Marked L i # H @ M" and
  "trail R = M" and
  "cdcl_M_level_inv R"
  shows "\<exists>y y'. cdcl_s\<^sup>*\<^sup>* R y \<and> cdcl_s y y' \<and> \<not> (\<exists>c. trail y = c @ Marked L i # H @ M) \<and> (\<lambda>a b. cdcl_s a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* y' U"
proof -
  fix T'
  obtain S' T T' where
    st: "cdcl_s\<^sup>*\<^sup>* R S'" and
    "decided S' T" and
    TU: "cdcl_s\<^sup>*\<^sup>* T U" and
    "no_step propagate S'" and
    "no_step conflict S'" and
    trT: "trail T = Marked L i # H @ M" and
    trS': "trail S' = H @ M" and
    S'U: "cdcl_s\<^sup>*\<^sup>* S' U" and
    S'T': "cdcl_s S' T'" and
    T'U: "cdcl_s\<^sup>*\<^sup>* T' U"
    using rtranclp_cdcl_new_marked_at_beginning_is_decided[OF assms] by blast
  have n: "\<not> (\<exists>c. trail S' = c @ Marked L i # H @ M)" using trS' by auto
  show ?thesis
    using rtranclp_trans[OF st] rtranclp_exists_last_with_prop[of cdcl_s S' T' _
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

lemma cdcl_s_trail_has_new_marked_is_decide_step:
  assumes "cdcl_s S T"
  "\<not> (\<exists>c. trail S = c @ Marked L i # H @ M)" and
  "(\<lambda>a b. cdcl_s a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* T U" and
  "\<exists>M'. trail U = M' @ Marked L i # H @ M" and
  "no_dup (trail S)"
  shows "\<exists>S'. decided S S' \<and> full0 cdcl_cp S' T \<and> no_step propagate S \<and> no_step conflict S"
  using assms(3,1,2,4,5)
proof induction
  case (step T U)
  thus ?case by fastforce
next
  case base
  thus ?case
    proof (induction rule: cdcl_s.induct)
      case (conflict' S T) note cp = this(1) and nd = this(2) and M' =this(3) and no_dup = this(3)
      then obtain M' where M': "trail T = M' @ Marked L i # H @ M" by metis
      obtain M'' where M'': "trail T = M'' @ trail S" and nm: "\<forall>m\<in> set M''. \<not>is_marked m"
        using cp unfolding full_def
        by (metis rtranclp_cdcl_cp_dropWhile_trail' tranclp_into_rtranclp)
      have False
        using beginning_not_marked_invert[of M'' "trail S" M' L i "H @ M"] M' nm nd unfolding M''
        by fast
      thus ?case by fast
    next
      case (other' S T U') note o = this(1) and ns = this(2,3) and cp = this(4) and nd = this(5) and trU' = this(6)
      have "cdcl_cp\<^sup>*\<^sup>* T U'" using cp unfolding full0_def by blast
      from rtranclp_cdcl_cp_dropWhile_trail[OF this]
      have "\<exists>M'. trail T = M' @ Marked L i # H @ M"
        using  trU' beginning_not_marked_invert[of _ "trail T" _ L i "H @ M"] by metis
      then obtain M' where "trail T = M' @ Marked L i # H @ M"
        by auto
      with o nd cp ns
      show ?case
        proof (induction rule: cdcl_o.induct)
          case (decided X Y) note dec = this(1) and cp = this(3) and ns = this(4,5)
          show ?case using dec cp ns by blast
        next
          case (backtrack S T) note bt = this(1) and nd = this(2) and cp = this(3) and trT = this(6) and ns = this(4,5)
          obtain MS N U D LS K MS1 MS2 j where
            S: "S = (MS, N, U, get_maximum_level (D + {#LS#}) MS, C_Clause (D + {#LS#}))" and
            T: "T = (Propagated LS (D + {#LS#}) # MS1, N, insert (D + {#LS#}) U,
                 get_maximum_level D MS, C_True)" and
            "j = Suc (get_maximum_level D MS)" and
            decomp: "(Marked K j # MS1, MS2) \<in>
              set (get_all_marked_decomposition MS)" and
            "get_level LS MS = get_maximum_level (D + {#LS#}) MS "
            using backtrackE[OF bt] by metis
          obtain MS3 where MS3: "MS = MS3 @ MS2 @ Marked K j # MS1"
            using get_all_marked_decomposition_exists_prepend[OF decomp] by metis
          obtain M'' where M'': "MS1 = M'' @ Marked L i # H @ M"
            using trT unfolding T trail_conv by (cases M') auto
          have False using nd MS3 unfolding S M'' by auto
          thus ?case by fast
        qed (auto elim!: skipE resolveE)
      qed
qed

lemma rtranclp_cdcl_s_with_trail_end_has_trail_end:
  assumes "(\<lambda>a b. cdcl_s a b \<and> (\<exists>c. trail a = c @ Marked L i # H @ M))\<^sup>*\<^sup>* T U" and
  "\<exists>M'. trail U = M' @ Marked L i # H @ M"
  shows "\<exists>M'. trail T = M' @ Marked L i # H @ M"
  using assms by (induction rule: rtranclp.induct) auto

lemma cdcl_o_cannot_learn:
  assumes "cdcl_o y z" and
  "cdcl_M_level_inv y " and
  "trail y = c @ Marked Kh i # H" and
  "D + {#L#} \<notin> learned_clauses y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<forall>T. conflicting y = C_Clause T \<longrightarrow> trail y \<Turnstile>as CNot T" and
  "trail z = c' @ Marked Kh i # H"
  shows "D + {#L#} \<notin> learned_clauses z"
  using assms(1-4,7,8)
proof (induction rule: cdcl_o_induct)
  case (backtrack M N U k D' L' K j M1 M2) note decomp = this(1) and levD = this(4) and lev =this(5) and trM = this(6) and DL = this(7) and learned = this(8) and z = this(9)
  obtain M3 where M3: "M = M3 @ M2 @ Marked K (j + 1) # M1"
    using decomp get_all_marked_decomposition_exists_prepend by metis
  have M: "M = c @ Marked Kh i # H" using trM by simp
  have H: "get_all_levels_of_marked M = rev [1..<1 + k]"
    using lev unfolding cdcl_M_level_inv_def by auto
  obtain d where d: "M1 = d @ Marked Kh i # H"
    using z unfolding M3 trail_conv
    by (metis (no_types, lifting) append_eq_Cons_conv list.inject marked_lit.distinct(1))
  have "i \<in> set (get_all_levels_of_marked (M3 @ M2 @ Marked K (j + 1) # d @ Marked Kh i # H))"
    by auto
  hence "i > 0" unfolding H[unfolded M3 d] by auto
  show ?case
    proof
      assume "D + {#L#} \<in> learned_clauses (Propagated L' (D' + {#L'#}) # M1, N, U \<union> {D' + {#L'#}}, j, C_True)"
      hence DLD': "D + {#L#} = D' + {#L'#}" using DL by auto
      have L_cKh: "atm_of L \<in> atm_of `lits_of (c @ [Marked Kh i])"
        using LH learned unfolding M DLD'[symmetric] by (fastforce simp add: image_iff)
      have "get_all_levels_of_marked (M3 @ M2 @ Marked K (j + 1) # M1) = rev [1..<1 + k]"
        using lev unfolding cdcl_M_level_inv_def M3 by auto
      from arg_cong[OF this, of "\<lambda>a. (Suc j) \<in> set a"] have "k \<ge> j" by auto

      have DD'[simp]: "D = D'"
        proof (rule ccontr)
          assume "D \<noteq> D'"
          hence "L' \<in>#  D" using DLD' by (metis add.left_neutral count_single count_union diff_union_cancelR neq0_conv union_single_eq_member)
          hence "get_level L' M \<le> get_maximum_level D M"
            using get_maximum_level_ge_get_level by blast
          moreover {
            have "get_maximum_level D M = get_maximum_level D H"
              using DH unfolding M by (simp add: get_maximum_level_skip_beginning)
            moreover
              have "get_all_levels_of_marked M = rev [1..<1 + k]"
                using lev unfolding cdcl_M_level_inv_def by auto
              hence "get_all_levels_of_marked H = rev [1..< i]"
                unfolding M by (auto dest: append_cons_eq_upt_length_i
                  simp add: rev_swap[symmetric])
              hence "get_maximum_possible_level H < i"
                using get_maximum_possible_level_max_get_all_levels_of_marked[of H] `i > 0` by auto
            ultimately have "get_maximum_level D M < i"
              by (metis (full_types) dual_order.strict_trans nat_neq_iff not_le
                get_maximum_possible_level_ge_get_maximum_level) }
          moreover
            have "L \<in># D'"
              by (metis DLD' `D \<noteq> D'` add.left_neutral count_single count_union diff_union_cancelR neq0_conv union_single_eq_member)
            hence "get_maximum_level D' M \<ge> get_level L M"
              using get_maximum_level_ge_get_level by blast
          moreover {
            have "get_all_levels_of_marked (c @ [Marked Kh i]) = rev [i..< k+1]"
              using append_cons_eq_upt_length_i_end[of " rev (get_all_levels_of_marked H)" i "rev (get_all_levels_of_marked c)" "Suc 0" "Suc k"] H
              unfolding M apply (auto simp add: rev_swap[symmetric])
                by (metis (no_types, hide_lams) Nil_is_append_conv Suc_le_eq less_Suc_eq list.sel(1) rev.simps(2) rev_rev_ident upt_Suc upt_rec)
            have "get_level L M  = get_level L (c @ [Marked Kh i])"
              using L_cKh LH unfolding M lits_of_def by simp
            have "get_level L (c @ [Marked Kh i]) \<ge> i"
              using L_cKh `get_all_levels_of_marked (c @ [Marked Kh i]) = rev [i..<k + 1]` backtrack.hyps(2) calculation(1,2) by auto
            hence "get_level L M \<ge> i"
              using M `get_level L M = get_level L (c @ [Marked Kh i])` by auto }
          moreover have "get_maximum_level D' M < get_level L' M"
            using `j \<le> k` backtrack.hyps(2,4) calculation(1-4) by linarith
          ultimately show False using backtrack.hyps(4) by linarith
        qed
      hence LL': "L = L'" using DLD' by auto
      have nd: "no_dup M" using lev unfolding cdcl_M_level_inv_def by auto

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
          using H ` i > 0` unfolding M3 d
          by (auto simp add: rev_swap[symmetric] dest!: upt_decomp_lt)
        obtain L'' where "L''\<in>#D'" and L''D': "get_level L'' M = get_maximum_level D' M"
          using get_maximum_level_exists_lit_of_max_level[OF D, of M] by auto
        have L''M: "atm_of L'' \<in> atm_of ` lit_of `set M"
          using get_rev_level_ge_0_atm_of_in[of 0 L'' "rev M"] `j>0` levD L''D' by auto
        hence "L'' \<in> lits_of  (Marked Kh i # d)"
          proof -
            {
              assume L''H: "atm_of L'' \<in> atm_of ` lit_of ` set H"
              have "get_all_levels_of_marked H = rev [1..<i]"
                using H unfolding M
                by (auto simp add: rev_swap[symmetric] dest!: append_cons_eq_upt_length_i)
              moreover have "get_level L'' M = get_level L'' H"
                using L''H unfolding M by simp
              ultimately have False
                using levD `j>0` get_rev_level_in_levels_of_marked[of L'' 0 "rev H"] `i \<le> j`
                unfolding L''D'[symmetric] nd by auto
            }
            then show ?thesis
              using DD' DH `L'' \<in># D'` atm_of_lit_in_atms_of contra_subsetD lits_of_def by metis
          qed
        hence False
          using DH `L''\<in>#D'` nd unfolding M3 d
          by (auto simp add: lits_of_def atms_of_def image_iff image_subset_iff)
      }
      ultimately show False by blast
    qed
qed auto

lemma cdcl_s_with_trail_end_has_not_been_learned:
  assumes "cdcl_s y z" and
  "cdcl_M_level_inv y" and
  "trail y = c @ Marked Kh i # H" and
  "D + {#L#} \<notin> learned_clauses y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<forall>T. conflicting y = C_Clause T \<longrightarrow> trail y \<Turnstile>as CNot T" and
  "trail z = c' @ Marked Kh i # H"
  shows "D + {#L#} \<notin> learned_clauses z"
  using assms
proof induction
  case conflict'
  thus ?case
    unfolding full_def using tranclp_cdcl_cp_learned_clause_inv by blast
next
  case (other' S T U) note o = this(1) and cp = this(4) and lev = this(5) and trS = this(6) and
    notin = this(7) and DH = this(8) and LH = this(9) and confl = this(10) and trU = this(11)
  obtain c' where c': "trail T = c' @ Marked Kh i # H"
    using cp beginning_not_marked_invert[of _ "trail T" c' Kh i H]
      rtranclp_cdcl_cp_dropWhile_trail[of T U] unfolding trU full0_def by fastforce
  show ?case
    using cdcl_o_cannot_learn[OF o lev trS notin DH LH  confl c']
      rtranclp_cdcl_cp_learned_clause_inv cp unfolding full0_def by blast
qed

lemma rtranclp_cdcl_s_with_trail_end_has_not_been_learned:
  assumes "(\<lambda>a b. cdcl_s a b \<and> (\<exists>c. trail a = c @ Marked K i # H @ []))\<^sup>*\<^sup>* y z" and
  "cdcl_all_inv_mes y" and
  "trail y = c @ Marked K i # H" and
  "D + {#L#} \<notin> learned_clauses y" and
  DH: "atms_of D \<subseteq> atm_of `lits_of H" and
  LH: "atm_of L \<notin> atm_of `lits_of H" and
  "\<exists>c'. trail z = c' @ Marked K i # H"
  shows "D + {#L#} \<notin> learned_clauses z"
  using assms(1-4,7)
proof (induction rule: rtranclp.induct)
  case rtrancl_refl
  thus ?case by auto[1]
next
  case (rtrancl_into_rtrancl S T U) note st = this(1) and s = this(2) and IH = this(3)[OF this(4-6)] and lev = this(4) and trS = this(5) and DL_S = this(6) and trU = this(7)
  obtain c where c: "trail T = c @ Marked K i # H" using s by auto
  obtain c' where c': "trail U = c' @ Marked K i # H" using trU by blast
  have lev': "cdcl_all_inv_mes T"
    by (metis (no_types, lifting) lev mono_rtranclp rtranclp_cdcl_all_inv_mes_inv rtranclp_cdcl_s_rtranclp_cdcl st)
  hence confl': "\<forall>Ta. conflicting T = C_Clause Ta \<longrightarrow> trail T \<Turnstile>as CNot Ta"
    unfolding cdcl_all_inv_mes_def cdcl_learned_clause_def by blast
  show ?case
    apply (rule cdcl_s_with_trail_end_has_not_been_learned[OF _ _ c _ DH LH confl' c'])
    using s lev' IH c unfolding cdcl_all_inv_mes_def by blast+
qed

lemma cdcl_s_new_learned_clause:
  assumes "cdcl_s S T" and
  "E \<notin> learned_clauses S" and
  "E \<in> learned_clauses T"
  shows "\<exists>S'. backtrack S S' \<and> conflicting S = C_Clause E \<and> full0 cdcl_cp S' T"
  using assms
proof induction
  case conflict'
  thus ?case unfolding full_def by (auto dest: tranclp_cdcl_cp_learned_clause_inv)
next
  case (other' S T U) note o = this(1) and cp = this(4) and not_yet = this(5) and learned = this(6)
  have "E \<in> learned_clauses T"
    using learned cp rtranclp_cdcl_cp_learned_clause_inv unfolding full0_def by blast
  hence "backtrack S T" and "conflicting S = C_Clause E"
    using cdcl_o_new_clause_learned_is_backtrack_step[OF _ not_yet o] by blast+
  thus ?case using cp by blast
qed

lemma no_relearned_clause:
  assumes invR: "cdcl_all_inv_mes R" and
  st': "cdcl_s\<^sup>*\<^sup>* R S" and
  bt: "backtrack S T" and
  confl: "conflicting S = C_Clause E" and
  M_lev: "cdcl_M_level_inv R" and
  already_learned: "E \<in> learned_clauses S \<union> clauses S" and
  R: "trail R = []"
  shows False
proof -
  obtain M N U k D L i M1 M2_loc K where
    S: "S = (M, N, U, k, C_Clause (D + {#L#}))"  and
    T: "T = (Propagated L (D + {#L#}) # M1, N, insert (D + {#L#}) U, get_maximum_level D M, C_True)" and
    decomp: "(Marked K (Suc (get_maximum_level D M)) # M1, M2_loc) \<in> set (get_all_marked_decomposition M)" and
    k: "get_level L M = k" and
    level: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "get_maximum_level D M = i"
    using  backtrackE[OF bt] by metis
  obtain M2 where
    M: "M = M2 @ Marked K (i+1) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] i by (metis Suc_eq_plus1 append_assoc)

  have invS: "cdcl_all_inv_mes S"
    using invR rtranclp_cdcl_all_inv_mes_inv rtranclp_cdcl_s_rtranclp_cdcl st' by blast
  hence conf: "cdcl_conflicting S" unfolding cdcl_all_inv_mes_def by blast
  then have "M \<Turnstile>as CNot (D + {#L#})" unfolding S by auto
  hence MD: "M \<Turnstile>as CNot D" by auto

  have lev': "cdcl_M_level_inv S" using invS  unfolding cdcl_all_inv_mes_def by blast

  have get_lvls_M: "get_all_levels_of_marked M = rev [1..<Suc k]"
    using lev' unfolding S cdcl_M_level_inv_def by auto
  hence "k > 0" unfolding M by (auto split: split_if_asm simp add: upt.simps(2))

  have lev: "cdcl_M_level_inv R" using invR unfolding cdcl_all_inv_mes_def by blast
  hence vars_of_D: "atms_of D \<subseteq> atm_of ` lit_of ` set M1"
    using backtrack_atms_of_D_in_M1[OF _ _ lev', of L D M1 N U i] bt conf S unfolding T i by force
  have "no_dup M" using lev' unfolding S by auto
  hence vars_in_M1: "\<forall>x \<in> atms_of D. x \<notin> atm_of ` lit_of ` set (M2 @ Marked K (i + 1) # [])"
    using vars_of_D distinct_atms_of_incl_not_in_other[of "M2 @ Marked K (i + 1) # []" M1]
    unfolding M by auto
  have M1_D: "M1 \<Turnstile>as CNot D"
    using vars_in_M1 true_annots_remove_if_notin_vars[of "M2 @ Marked K (i + 1) # []" M1 "CNot D"] `M \<Turnstile>as CNot D` unfolding M lits_of_def by simp

  have get_lvls_M: "get_all_levels_of_marked M = rev [1..<Suc k]"
    using lev' unfolding S cdcl_M_level_inv_def by auto

  obtain M1' K Ls where
    M': "M = Ls @ Marked K k # M1'" and
    Ls: "\<forall>l \<in> set Ls. \<not> is_marked l" and
    "set M1 \<subseteq> set M1'"
    proof -
      let ?Ls = "takeWhile (Not o is_marked) M"
      have MLs: "M = ?Ls @ dropWhile (Not o is_marked) M"
        by auto
      have "dropWhile (Not o is_marked) M \<noteq> []" unfolding M by auto
      moreover from hd_dropWhile[OF this] have "is_marked(hd (dropWhile (Not o is_marked) M))"
        by simp
      ultimately obtain K Kk where
        Kk: "dropWhile (Not o is_marked) M = Marked K Kk # tl (dropWhile (Not o is_marked) M)"
        by (cases "dropWhile (Not \<circ> is_marked) M"; cases "hd (dropWhile (Not \<circ> is_marked) M)")
          simp_all
      moreover have "\<forall>l \<in> set ?Ls. \<not>is_marked l" using set_takeWhileD by force
      moreover
        have "get_all_levels_of_marked M = Kk # get_all_levels_of_marked(tl (dropWhile (Not \<circ> is_marked) M))"
          apply (subst MLs, subst Kk)
          using calculation(2) by (auto simp add: get_all_levels_of_marked_no_marked)
        hence "Kk =  k"
        using calculation(2) unfolding get_lvls_M by (auto split: split_if_asm simp add: upt.simps(2))
      moreover have "set M1 \<subseteq> set (tl (dropWhile (Not o is_marked) M))"
        unfolding M by (induction M2) auto
      ultimately show ?thesis using that MLs by metis
    qed

  have M1'_D: "M1' \<Turnstile>as CNot D" using M1_D `set M1 \<subseteq> set M1'` by (auto intro: true_annots_mono)

  have "-L \<in> lits_of M" using conf unfolding S by auto
  have lvls_M1': "get_all_levels_of_marked M1' = rev [1..<k]"
    using get_lvls_M Ls by (auto simp add: get_all_levels_of_marked_no_marked M'
      split: split_if_asm simp add: upt.simps(2))
  have L_notin: "atm_of L \<in> atm_of ` lits_of Ls \<or> atm_of L = atm_of K"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "atm_of L \<notin> atm_of ` lit_of ` set (Marked K k # rev Ls)" by (simp add: lits_of_def)
      hence "get_level L M = get_level L M1'"
        unfolding M' by auto
      thus False using get_level_in_levels_of_marked[of L M1'] `k > 0` unfolding k lvls_M1' by auto
    qed
  obtain Y Z where
    RY: "cdcl_s\<^sup>*\<^sup>* R Y" and
    YZ: "cdcl_s Y Z" and
    nt: "\<not> (\<exists>c. trail Y = c @ Marked K k # M1' @ [])" and
    Z: "(\<lambda>a b. cdcl_s a b \<and> (\<exists>c. trail a = c @ Marked K k # M1' @ []))\<^sup>*\<^sup>* Z (Ls @ Marked K k # M1', N, U, k, C_Clause (D + {#L#}))"
    using rtranclp_cdcl_new_marked_at_beginning_is_decided'[OF  st' _ _ lev, of Ls K k M1' "[]"]
    unfolding R M' S by auto

  obtain M' where trZ: "trail Z = M' @ Marked K k # M1'"
    using rtranclp_cdcl_s_with_trail_end_has_trail_end[OF Z] by auto
  have "no_dup (trail Y)" using RY lev rtranclp_cdcl_s_consistent_inv by blast
  then obtain Y' where
    dec: "decided Y Y'" and
    Y'Z: "full0 cdcl_cp Y' Z" and
    "no_step propagate Y" and
    "no_step conflict Y"
    using cdcl_s_trail_has_new_marked_is_decide_step[OF YZ nt Z] unfolding trail_conv by auto
  have trY: "trail Y = M1'"
    proof -
      obtain M' where M: "trail Z = M' @ Marked K k # M1'" using rtranclp_cdcl_s_with_trail_end_has_trail_end[OF Z] by auto
      obtain M'' where M'': "trail Z = M'' @ trail Y'" and "\<forall>m\<in>set M''. \<not>is_marked m"
        using Y'Z rtranclp_cdcl_cp_dropWhile_trail' unfolding full0_def by blast
      obtain M''' where "trail Y' = M''' @ Marked K k # M1'"
        using M'' unfolding M
        by (metis (no_types, lifting) `\<forall>m\<in>set M''. \<not> is_marked m` beginning_not_marked_invert)
      thus ?thesis using dec nt  by (induction M''') auto
    qed
  have Y_CT: "conflicting Y = C_True" using `decided Y Y'` by auto
  have "clauses Y = clauses R" using rtranclp_cdcl_s_no_more_clauses[OF RY] ..
  { assume DL: "D + {#L#} \<in> clauses Y \<union> learned_clauses Y"
    have "atm_of L \<notin> atm_of ` lits_of M1"
      apply (rule backtrack_lit_skiped[of _ S])
      using decomp i k lev' unfolding S cdcl_M_level_inv_def by auto
    hence LM1: "undefined_lit L M1"
      by (metis Marked_Propagated_in_iff_in_lits_of atm_of_uminus image_eqI)
    have L_trY: "undefined_lit L (trail Y)"
      using  L_notin `no_dup M` unfolding defined_lit_map trY M'
      by (auto simp add: lits_of_def image_iff)
    have "\<exists> Y'. propagate Y Y'"
      using propagate_rule[OF _ DL M1'_D L_trY] Y_CT trY DL by fast
    hence False using `no_step propagate Y` by blast
  }
  moreover {
    assume DL: "D + {#L#} \<notin> clauses Y \<union> learned_clauses Y"
    have lY_lZ: "learned_clauses Y = learned_clauses Z"
      using dec Y'Z rtranclp_cdcl_cp_learned_clause_inv[of Y' Z] unfolding full0_def
      by auto
    have invZ: "cdcl_all_inv_mes Z"
      by (meson RY YZ invR r_into_rtranclp rtranclp_cdcl_all_inv_mes_inv rtranclp_cdcl_s_rtranclp_cdcl)
    have "D + {#L#} \<notin> learned_clauses (Ls @ Marked K k # M1', N, U, k, C_Clause (D + {#L#}))"
      apply (rule rtranclp_cdcl_s_with_trail_end_has_not_been_learned[OF Z invZ trZ])
         using DL lY_lZ apply simp
        apply (metis (no_types, lifting) `set M1 \<subseteq> set M1'` image_mono lits_of_def order_trans vars_of_D)
       using L_notin `no_dup M` unfolding M' by (auto simp add: image_iff lits_of_def)
    hence False
      using already_learned DL confl rtranclp_cdcl_s_no_more_clauses st'
      unfolding S M' `clauses Y = clauses R` by fastforce
  }
  ultimately show False by blast
qed


subsection \<open>Decrease of a measure\<close>
lemma distinctlength_eq_card_atm_of_lits_of:
  assumes "no_dup M"
  shows "length M  = card (atm_of ` lits_of M)"
  using assms unfolding lits_of_def by (induct M) (auto simp add: image_image)

fun cdcl_measure where
"cdcl_measure (M, N, U, k, C_True) = [(3::nat) ^(card (atms_of_m N)) - card U, 1, card (atms_of_m N) - length M]" |
"cdcl_measure (M, N, U, k, _) = [3 ^(card (atms_of_m N)) - card U, 0, length M]"

lemma length_model_le_vars:
  assumes "no_strange_atm S"
  and no_d: "no_dup (trail S)"
  and "finite (atms_of_m (clauses S))"
  shows "length (trail S) \<le> card (atms_of_m (clauses S))"
proof -
  obtain M N U k D where S: "S = (M, N, U, k, D)" by (case_tac S, auto)
  have "finite (atm_of ` lits_of (trail S))" using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of (trail S))"
    using distinctlength_eq_card_atm_of_lits_of no_d by blast
  thus ?thesis using assms(1) by (auto simp add: assms(3) card_mono)
qed

lemma learned_clauses_less_upper_bound:
  fixes S :: "'v ::linorder cdcl_state"
  assumes "distinct_cdcl_state S"
  and "\<forall>s \<in> learned_clauses S. \<not>tautology s"
  and "finite (learned_clauses S)"
  shows "card (learned_clauses S) \<le> 3 ^ card (atms_of_m (learned_clauses S))"
proof -
  have "learned_clauses S \<subseteq> build_all_simple_clss (atms_of_m (learned_clauses S))"
    using assms simplified_in_build_all unfolding distinct_cdcl_state_def by auto
  hence "card (learned_clauses S) \<le> card (build_all_simple_clss (atms_of_m (learned_clauses S)))"
    by (simp add: build_all_simple_clss_finite card_mono)
  moreover have "finite (atms_of_m (learned_clauses S))" using assms(3) by fastforce
  ultimately show ?thesis by (meson build_all_simple_clss_card le_less_trans not_less)
qed

lemma lexn3[simp]:
  "a < a' \<or> (a = a' \<and> b < b') \<or> (a = a' \<and> b = b' \<and> c < c') \<Longrightarrow> ([a::nat, b, c], [a', b', c']) \<in> lexn {(x, y). x < y} 3 "
  apply auto
  unfolding lexn_conv apply fastforce
  unfolding lexn_conv apply auto
  apply (metis append.simps(1) append.simps(2))+
  done

lemma cdcl_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "cdcl S S'"
  and "\<not>(learned_clauses S = learned_clauses S' \<and> [] = trail S' \<and> conflicting S' = C_True)" (*no restart*)
  and "learned_clauses S \<subseteq> learned_clauses S'" (*no forget*)
  and "backtrack S S' \<Longrightarrow> \<forall>T. conflicting S = C_Clause T \<longrightarrow> T \<notin> learned_clauses S" (*replace 2.10.5-8 we will prove later*)
  and "no_strange_atm S"
  and "cdcl_M_level_inv S"
  and "finite (atms_of_m (clauses S))"
  and "finite (learned_clauses S)"
  and "\<forall>s \<in> learned_clauses S. \<not>tautology s"
  and "distinct_cdcl_state S"
  and "cdcl_conflicting S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms
proof (induct rule: cdcl_all_induct)
  case (propagate M N U k C L) note alien = this(7) and M_level = this(8) and no_dup = this(12) and confl = this(13)
  have propa: "propagate (M, N, U, k, C_True) (Propagated L (C + {#L#}) # M, N, U, k, C_True)" using propagate_rule[OF _ propagate.hyps(1,2)] propagate.hyps(3) by auto
  hence no_dup': "no_dup (Propagated L (C + {#L#}) # M)"
    unfolding cdcl_M_level_inv_def by (metis M_level cdcl.simps cdcl_M_level_inv_decomp(2) cdcl_consistent_inv trail_conv)

  have "no_strange_atm (Propagated L (C + {#L#}) # M, N, U, k, C_True)"
    using alien cdcl.propagate cdcl_no_strange_atm_inv propa by blast
  hence  "atm_of ` lits_of (Propagated L (C + {#L#}) # M) \<subseteq> (atms_of_m N)"
    unfolding no_strange_atm_def by auto
  hence "card (atm_of ` lits_of (Propagated L (C + {#L#}) # M)) \<le> card (atms_of_m N)"
    using card_mono propagate.prems(6) by fastforce
  hence "length (Propagated L (C + {#L#}) # M) \<le> card (atms_of_m N)"
    using distinctlength_eq_card_atm_of_lits_of no_dup' by fastforce
  thus ?case by simp
next
  case (decided M N U k L) note p = this(5,6,7)
  moreover
    have no_dup: "no_dup (Marked L (k + 1) # M)"
      using decided(7) other[OF cdcl_o.decided[OF deciding[OF _ decided.hyps]]] cdcl_consistent_inv
      unfolding cdcl_M_level_inv_def by fast
    have "no_strange_atm (Marked L (k + 1) # M, N, U, k + 1, C_True)"
      by (meson decided.intros[OF _ decided.hyps(1,2)] cdcl_no_strange_atm_inv cdcl_o.decided other p(2)   cdcl_no_strange_atm_inv cdcl_o.decided other)
    hence "length (Marked L (k + 1) # M) \<le> card (atms_of_m N)"
      using no_dup decided(8) length_model_le_vars[of "(Marked L (k + 1) # M, N, U, k + 1, C_True)"] by fastforce
  ultimately show ?case unfolding decided.hyps(1) by force
next
  case (skip M N L C' D k U) note  p = this(5,6,7)
  moreover
    have  "atm_of ` lits_of (Propagated L C' # M) \<subseteq> (atms_of_m N)"
      using skip.prems(4) unfolding no_strange_atm_def by auto
    hence "card (atm_of ` lits_of (Propagated L C' # M)) \<le> card (atms_of_m N)"
      using card_mono skip.prems(6) by fastforce
    hence "length (Propagated L C' # M) \<le> card (atms_of_m N)"
      using distinctlength_eq_card_atm_of_lits_of skip.prems(5) by fastforce
  ultimately show  ?case by simp
next
  case (conflict M N U k D)
  show ?case by simp
next
  case (resolve M N L C' D k U)
  thus ?case by simp
next
  case (backtrack M N U k D L K i M1 M2) note S = this(1)
  let ?S' = "(Propagated L (D + {#L#}) # M1, N, U \<union> {D + {#L#}}, i, C_True)"
  have "finite U" using backtrack.prems(7) unfolding S by auto
  have "D + {#L#} \<notin> U"
    using backtrack.prems(3) backtracking[OF _ backtrack.hyps(1-4)] unfolding S by auto
  hence "card (insert (D + {#L#}) U) = Suc (card U)" by (simp add: `finite U`)
  have "distinct_cdcl_state ?S'" using backtrack.prems(9) cdcl_o.backtrack[OF backtracking[OF _ backtrack.hyps]] distinct_cdcl_state_inv cdcl.other by blast
  moreover have "\<forall>s\<in>learned_clauses ?S'. \<not> tautology s" using learned_clauses_are_not_tautologies[OF cdcl.other[OF cdcl_o.backtrack[OF backtracking[OF _ backtrack.hyps]]]] backtrack.prems(5,8,10) by auto
  moreover have "finite (learned_clauses ?S')" using `finite U` by auto
  moreover have "card (atms_of_m (learned_clauses (M, N, U, k, C_Clause (D + {#L#})))) \<le> card (atms_of_m N)" using backtrack.prems(4,6) card_mono[OF backtrack.prems(6)] local.backtrack(1) unfolding no_strange_atm_def by auto
  ultimately have "card (U \<union> {D + {#L#}}) \<le> 3 ^ card (atms_of_m (U \<union> {D + {#L#}}))" using learned_clauses_less_upper_bound[of ?S'] by auto
  moreover
    have "atms_of_m (U \<union> {D + {#L#}}) \<subseteq> atms_of_m N" using backtrack.prems(4) local.backtrack(1) unfolding no_strange_atm_def by auto
    hence "card (atms_of_m (U \<union> {D + {#L#}})) \<le> card (atms_of_m N)" using card_mono backtrack.prems(6) unfolding S by fastforce
    hence "(3::nat) ^ card (atms_of_m (U \<union> {D + {#L#}})) \<le> 3 ^ card (atms_of_m N)" by simp
  ultimately have "(3::nat) ^ card (atms_of_m N) \<ge> card (U \<union> {D + {#L#}})" using le_trans by blast
  thus ?case using backtrack.prems(3) unfolding S by (auto simp add: `finite U` `D + {#L#} \<notin> U`)
next
  case (restart M N U k)
  thus ?case by simp
next
  case (forget M N U C k)
  thus ?case by auto
qed


lemma propagate_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "propagate S S'" and "cdcl_all_inv_mes S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl_measure_decreasing)
  using assms(1) propagate apply blast
  using assms(1) apply (auto simp add: propagate.simps)[3]
  using assms(2) apply (auto simp add: cdcl_all_inv_mes_def)
  done

lemma conflict_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "conflict S S'" and "cdcl_all_inv_mes S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl_measure_decreasing)
  using assms(1) conflict apply blast
  using assms(1) apply (auto simp add: propagate.simps)[3]
  using assms(2) apply (auto simp add: cdcl_all_inv_mes_def)
  done

lemma decided_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "decided S S'" and "cdcl_all_inv_mes S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  apply (rule cdcl_measure_decreasing)
  using assms(1) decided other apply blast
  using assms(1) apply (auto simp add: propagate.simps)[3]
  using assms(2) apply (auto simp add: cdcl_all_inv_mes_def)
  done

lemma trans_le:
  "trans {(a, (b::nat)). a < b}"
  unfolding trans_def by auto

lemma cdcl_cp_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "cdcl_cp S S'" and "cdcl_all_inv_mes S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms
proof induction
  case conflict'
  thus ?case using conflict_measure_decreasing by blast
next
  case propagate_no_conf'
  thus ?case using propagate_measure_decreasing by blast
next
  case (propagate_conf' S S' S'') note propa = this(1) and confl = this(3) and inv = this(4)
  show ?case
    using propagate_measure_decreasing[OF propa inv] conflict_measure_decreasing[OF confl]
    cdcl_all_inv_mes_inv[OF propagate[OF propa] inv] trans_le[THEN lexn_trans]
    unfolding trans_def by blast
qed

lemma tranclp_cdcl_cp_measure_decreasing:
  fixes S :: "'v::linorder cdcl_state"
  assumes "cdcl_cp\<^sup>+\<^sup>+ S S'" and "cdcl_all_inv_mes S"
  shows "(cdcl_measure S', cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
  using assms
proof induction
  case base
  thus ?case using cdcl_cp_measure_decreasing by blast
next
  case (step T U) note st = this(1) and step = this(2) and IH =this(3) and inv = this(4)
  hence "(cdcl_measure T, cdcl_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3" by blast

  moreover have "(cdcl_measure U, cdcl_measure T) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3"
    using cdcl_cp_measure_decreasing[OF step] rtranclp_cdcl_all_inv_mes_inv inv
    tranclp_cdcl_cp_tranclp_cdcl[OF st]
    unfolding trans_def rtranclp_unfold
    by blast
  ultimately show ?case using lexn_trans[OF trans_le] unfolding trans_def by blast
qed


lemma cdcl_s_step_decreasing:
  fixes R S T :: "'v::linorder cdcl_state"
  assumes "cdcl_s S T" and
  "cdcl_s\<^sup>*\<^sup>* R S"
  "trail R = []" and
  "cdcl_all_inv_mes R"
  shows "(cdcl_measure T, cdcl_measure S) \<in> lexn {(a, b). a < b} 3"
proof -
  have "cdcl_all_inv_mes S"
  using assms
    by (metis rtranclp_unfold rtranclp_cdcl_all_inv_mes_inv tranclp_cdcl_s_tranclp_cdcl)
  with assms show ?thesis
    proof (induction)
      case (conflict' U V) note cp = this(1) and inv = this(5)
      show ?case
         using tranclp_cdcl_cp_measure_decreasing[OF HOL.conjunct1[OF cp[unfolded full_def]] inv] .
    next
      case (other' S T U) note H= this(1,5,6,7,8) and cp = this(4)
      have "cdcl_all_inv_mes T"
        using cdcl_all_inv_mes_inv other other'.hyps(1) other'.prems(4) by blast
      from tranclp_cdcl_cp_measure_decreasing[OF _ this]
      have "(cdcl_measure U, cdcl_measure T) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3 \<or>
        cdcl_measure U = cdcl_measure T"
        using cp unfolding full0_def rtranclp_unfold by blast
      moreover
        from H have "(cdcl_measure T, cdcl_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3"
        proof (induction)
          case (decided S T)
          thus ?case using decided_measure_decreasing by blast
        next
          case (skip S T)
          thus ?case by auto
        next
          case (resolve)
          thus ?case by auto
        next
          case (backtrack S T) note bt = this(1) and st = this(2) and R = this(3) and invR = this(4) and inv = this(5)
          have no_relearn: "\<forall>T. conflicting S = C_Clause T \<longrightarrow> T \<notin> learned_clauses S"
            using no_relearned_clause[OF invR st bt] R by (meson Un_iff cdcl_all_inv_mes_def invR)
          show ?case
            apply (rule cdcl_measure_decreasing)
            using bt cdcl_o.backtrack other apply blast
            using bt inv no_relearn apply (auto simp add: cdcl_all_inv_mes_def)
            done
        qed
      ultimately show ?case
         proof -
           have "cdcl_measure U = cdcl_measure T \<longrightarrow> (cdcl_measure U, cdcl_measure S) \<in> lexn {p. case p of (n, na) \<Rightarrow> n < na} 3"
             using `(cdcl_measure T, cdcl_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3` by presburger
           thus ?thesis
             using lexn_trans[OF trans_le, of 3] `(cdcl_measure T, cdcl_measure S) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3` `(cdcl_measure U, cdcl_measure T) \<in> lexn {a. case a of (a, b) \<Rightarrow> a < b} 3 \<or> cdcl_measure U = cdcl_measure T` unfolding trans_def by blast
         qed
    qed
qed

lemma tranclp_cdcl_s_decreasing:
  fixes R S T :: "'v::linorder cdcl_state"
  assumes "cdcl_s\<^sup>+\<^sup>+ R S"
  "trail R = []" and
  "cdcl_all_inv_mes R"
  shows "(cdcl_measure S, cdcl_measure R) \<in> lexn {(a, b). a < b} 3"
  using assms
  apply (induction)
   using cdcl_s_step_decreasing[of R _ R] apply blast
  using cdcl_s_step_decreasing[of _ _ R]  tranclp_into_rtranclp[of cdcl_s R]
  lexn_trans[OF trans_le, of 3] unfolding trans_def by blast

lemma tranclp_cdcl_s_S0_decreasing:
  fixes R S T :: "'v::linorder cdcl_state"
  assumes pl: "cdcl_s\<^sup>+\<^sup>+ (S0_cdcl N) S" and
  fin: "finite (atms_of_m N)" and
  no_dup: "distinct_mset_set N"
  shows "(cdcl_measure S, cdcl_measure (S0_cdcl N)) \<in> lexn {(a, b). a < b} 3"
proof -
  have "cdcl_all_inv_mes (S0_cdcl N)"
    using fin no_dup unfolding cdcl_all_inv_mes_def by auto
  thus ?thesis using pl tranclp_cdcl_s_decreasing by fast
qed

lemma wf_if_measure_f_notation2:
assumes "wf r"
shows "wf {(b, h a)|b a. (f b, f (h a)) \<in> r}"
apply (rule wf_subset)
using wf_if_measure_f[OF assms, of f] by auto

lemma wf_wf_if_measure'_notation2:
assumes "wf r" and H: "(\<And>x y. P x \<Longrightarrow> g x y \<Longrightarrow> (f y, f (h x)) \<in> r)"
shows " wf {(y,h x)| y x. P x \<and> g x y}"
proof -
  have "wf {(b, h a)|b a. (f b, f (h a)) \<in> r}" using assms(1) wf_if_measure_f_notation2 by auto
  hence "wf {(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}" using wf_subset[of _ "{(b, h a)| b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r}"] by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r} \<subseteq> {(b, h a)|b a. (f b, f (h a)) \<in> r}" by auto
  moreover have "{(b, h a)|b a. P a \<and> g a b \<and> (f b, f (h a)) \<in> r} = {(b, h a)|b a. P a \<and> g a b}" using H by auto
  ultimately show ?thesis using wf_subset by simp
qed

lemma tranclp_cdcl_s_wf:
  "wf {(S::'v::linorder cdcl_state, S0_cdcl N)| S N. (finite (atms_of_m N) \<and> distinct_mset_set N) \<and> cdcl_s\<^sup>+\<^sup>+ (S0_cdcl N) S}"
  apply (rule wf_wf_if_measure'_notation2[of "lexn {(a, b). a < b} 3" _ _ cdcl_measure])
   apply (simp add: wf wf_lexn)
  using tranclp_cdcl_s_S0_decreasing by blast

end
