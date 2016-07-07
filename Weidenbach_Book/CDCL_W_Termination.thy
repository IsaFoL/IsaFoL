theory CDCL_W_Termination
imports CDCL_W
begin

context conflict_driven_clause_learning\<^sub>W
begin
subsection \<open>Termination\<close>

subsubsection \<open>No Relearning of a clause\<close>
lemma propagate_no_more_Decided_lit:
  assumes "propagate S S'"
  shows "Decided K \<in> set (trail S) \<longleftrightarrow> Decided K \<in> set (trail S')"
  using assms by (auto elim: propagateE)

lemma conflict_no_more_Decided_lit:
  assumes "conflict S S'"
  shows "Decided K \<in> set (trail S) \<longleftrightarrow> Decided K \<in> set (trail S')"
  using assms by (auto elim: conflictE)

lemma cdcl\<^sub>W_o_no_more_Decided_lit:
  assumes "cdcl\<^sub>W_o S S'" and lev: "cdcl\<^sub>W_M_level_inv S" and "\<not>decide S S'"
  shows "Decided K \<in> set (trail S') \<longrightarrow> Decided K \<in> set (trail S)"
  using assms
proof (induct rule: cdcl\<^sub>W_o_induct)
  case backtrack note decomp = this(3) and undef = this(8) and T = this(9)
  then show ?case using lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case (decide L T)
  then show ?case using decide_rule[OF decide.hyps] by blast
qed auto

lemma cdcl\<^sub>W_o_is_decide:
  assumes "cdcl\<^sub>W_o S T" and lev: "cdcl\<^sub>W_M_level_inv S"
  "trail T = M' @ Decided L # H @ M" and
  "\<not> (\<exists>M'. trail S = M' @ Decided L # H @ M)"
  shows "decide S T"
  using assms
proof (induction rule:cdcl\<^sub>W_o_induct)
  case (backtrack L D K i M1 M2 T)
  then obtain c where "trail S = c @ M2 @ Decided K # M1"
    by auto
  show ?case
    using backtrack lev
    apply (cases M')
     apply (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
    using \<open>trail S = c @ M2 @ Decided K # M1\<close>
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
next
  case decide
  show ?case using decide_rule[of S] decide(1-4) by auto
qed auto

lemma rtranclp_cdcl\<^sub>W_restart_new_decided_at_beginning_is_decide:
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Decided L # H @ M" and
  "trail R = M" and
  "cdcl\<^sub>W_M_level_inv R"
  shows
    "\<exists>S T. cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S \<and> decide S T \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U \<and> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S U \<and>
      no_step conflict_or_propagate S \<and> trail T = Decided L # H @ M \<and> trail S = H @ M"
  using assms
proof (induct arbitrary: M H M' rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step T U) note st = this(1) and IH = this(3) and s = this(2) and
    U = this(4) and S = this(5) and lev = this(6)
  show ?case
    proof (cases "\<exists>M'. trail T = M' @ Decided L # H @ M")
      case False
      with s show ?thesis using U s st S
        proof induction
          case (propagate' W) note propa = this(1) and nd = this(2) and W = this(3)
          obtain La E where "trail W = Propagated La E # trail T"
             using propa by (auto elim!: propagateE)
          then have "trail T = tl M' @ Decided L # H @ M"
            unfolding W by (cases M') auto
          then show ?case using nd by (auto elim!: propagateE)
        next
          case (conflict' W) note cp = this(1) and nd = this(2) and W = this(3)
          then have False using nd by (auto elim: conflictE)
          then show ?case by fast
        next
          case (other' U) note n_s = this(1,2) and o = this(3) and nd = this(4)
            and U = this(5) and TU = this(6) and st = this(7) and tr_R = this(8)
          then have MV: "M' @ Decided L # H @ M = trail U" unfolding U by simp
          have LT': "Decided L \<in> set (trail U)" unfolding U by auto
          have "cdcl\<^sub>W_M_level_inv T"
            using lev rtranclp_cdcl\<^sub>W_stgy_consistent_inv step.hyps(1) by blast
          then have dec: "decide T U" using MV o nd cdcl\<^sub>W_o_is_decide by metis
          have 1: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R T" and 2: "decide T U" and 3: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* U U"
            using st other'.prems(4) dec by auto
          moreover have [simp]: "M' = []" and tr_T_U: "trail T = tl (trail U)"
              using 2 nd U by (auto elim!: decideE simp add: Cons_eq_append_conv)
          moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U"
            using cdcl\<^sub>W_stgy.other'[of T] n_s dec by (auto dest!: cdcl\<^sub>W_o.intros)
          ultimately show ?case apply - apply (rule exI[of _ T], rule exI[of _ U])
            using n_s U by auto
        qed
    next
      case True
      then obtain M' where T: "trail T = M' @ Decided L # H @ M" by metis
      from IH[OF this S lev] obtain S' S'' where
        1: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S'" and
        2: "decide S' S''" and
        3: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T " and
        4: "no_step conflict_or_propagate S'" and
        6: "trail S'' = Decided L # H @ M" and
        7: "trail S' = H @ M" and
        8: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' T"
          by blast
      have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' U" using s \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S'' T \<close> by auto
      moreover have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U" using 8 s by auto
      ultimately show ?thesis apply - apply (rule exI[of _ S'], rule exI[of _ S''])
        using 1 2 4 6 7 8 by blast
    qed
qed

lemma rtranclp_cdcl\<^sub>W_restart_new_decided_at_beginning_is_decide':
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R U" and
  "trail U = M' @ Decided L # H @ M" and
  "trail R = M" and
  "cdcl\<^sub>W_M_level_inv R"
  shows "\<exists>y y'. cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R y \<and> cdcl\<^sub>W_stgy y y' \<and> \<not> (\<exists>c. trail y = c @ Decided L # H @ M)
    \<and> (\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Decided L # H @ M))\<^sup>*\<^sup>* y' U"
proof -
  fix T'
  obtain S' T where
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S'" and
    dec: "decide S' T" and
    TU: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T U" and
    n_s: "no_step conflict_or_propagate S'" and
    trT: "trail T = Decided L # H @ M" and
    trS': "trail S' = H @ M" and
    S'U: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S' U"
    using rtranclp_cdcl\<^sub>W_restart_new_decided_at_beginning_is_decide[OF assms] by blast
  have n: "\<not> (\<exists>c. trail S' = c @ Decided L # H @ M)" using trS' by auto
  have "cdcl\<^sub>W_stgy S' T"
    using cdcl\<^sub>W_stgy.other'[of S' T] n_s dec by (auto dest!: cdcl\<^sub>W_o.intros)
  then show ?thesis
    using rtranclp_trans[OF st] rtranclp_exists_last_with_prop[of cdcl\<^sub>W_stgy S' T _
        "\<lambda>a _. \<not>(\<exists>c. trail a = c @ Decided L # H @ M)", OF _ _ n] TU S'U 
    by meson
qed

lemma cdcl\<^sub>W_stgy_trail_has_new_decided_is_decide_step:
  assumes
    "cdcl\<^sub>W_stgy S T"
    "\<not> (\<exists>c. trail S = c @ Decided L # H @ M)" and
    "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Decided L # H @ M))\<^sup>*\<^sup>* T U" and
    "\<exists>M'. trail U = M' @ Decided L # H @ M" and
    lev: "cdcl\<^sub>W_M_level_inv S"
  shows "decide S T \<and> no_step conflict_or_propagate S"
  using assms(3,1,2,4,5)
proof induction
  case (step T U)
  then show ?case by fastforce
next
  case base
  then show ?case
    proof (cases rule: cdcl\<^sub>W_stgy.cases)
      case conflict'
      then show ?thesis
        using base by (auto elim!: conflictE)
    next
      case propagate'
      then obtain L C where
        "Propagated L C # trail S = trail T"
        using base propagate.simps by moura
      then show ?thesis
        using base by (metis (no_types) ann_lit.disc(2) ann_lit.discI(1) append_eq_Cons_conv
          list.inject)
    next
      case (other')
      then show ?thesis 
        using base.prems(2,3) cdcl\<^sub>W_o_is_decide conflict_or_propagate_def lev by blast
    qed
qed

lemma rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end:
  assumes "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Decided L # H @ M))\<^sup>*\<^sup>* T U" and
  "\<exists>M'. trail U = M' @ Decided L # H @ M"
  shows "\<exists>M'. trail T = M' @ Decided L # H @ M"
  using assms by (induction rule: rtranclp_induct) auto

lemma remove1_mset_eq_remove1_mset_same:
  "remove1_mset L D = remove1_mset L' D \<Longrightarrow> L \<in># D \<Longrightarrow> L = L'"
  by (metis diff_single_trivial insert_DiffM multi_drop_mem_not_eq single_eq_single
    union_right_cancel)

lemma cdcl\<^sub>W_o_cannot_learn:
  assumes
    "cdcl\<^sub>W_o y z" and
    lev: "cdcl\<^sub>W_M_level_inv y" and
    M: "trail y = c @ Decided Kh # H" and
    DL: "D \<notin># learned_clss y" and
    LD: "L \<in># D" and
    DH: "atms_of (remove1_mset L D) \<subseteq> atm_of ` lits_of_l H" and
    LH: "atm_of L \<notin> atm_of ` lits_of_l H" and
    learned: "\<forall>T. conflicting y = Some T \<longrightarrow> trail y \<Turnstile>as CNot T" and
    z: "trail z = c' @ Decided Kh # H"
  shows "D \<notin># learned_clss z"
  using assms(1-2) M DL DH LH learned z
proof (induction rule: cdcl\<^sub>W_o_induct)
  case (backtrack L' D' K j M1 M2 T) note confl = this(1) and LD' = this(2) and decomp = this(3)
    and levL = this(4) and levD = this(5) and j = this(6) and lev_K = this(7) and T = this(8) and
    z = this(15)
  define i where i_def: "i = get_level (trail T) Kh"
  have levT: "cdcl\<^sub>W_M_level_inv T"
    using backtrack_rule[OF confl LD' decomp levL levD _ _ T] lev_K j lev
    by (metis Suc_eq_plus1 cdcl\<^sub>W_restart.simps cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_consistent_inv cdcl\<^sub>W_o.simps)
  obtain M3 where M3: "trail y = M3 @ M2 @ Decided K # M1"
    using decomp get_all_ann_decomposition_exists_prepend by metis
  have "c' @ Decided Kh # H = Propagated L' D' # trail (reduce_trail_to M1 y)"
    using z decomp T lev by (force simp: cdcl\<^sub>W_M_level_inv_def)
  then obtain d where d: "M1 = d @ Decided Kh # H"
    by (metis (no_types) decomp in_get_all_ann_decomposition_trail_update_trail list.inject
      list.sel(3) ann_lit.distinct(1) self_append_conv2 tl_append2)

  have "atm_of Kh \<notin> atm_of ` lits_of_l c'"
    using levT unfolding cdcl\<^sub>W_M_level_inv_def z
    by (auto simp: atm_lit_of_set_lits_of_l)
  then have count_H: "count_decided H = i - 1" "i > 0"
    unfolding z i_def by auto
  have n_d_y: "no_dup (trail y)" and bt_y: "backtrack_lvl y = count_decided (trail y)"
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  have tr_T: "trail T = Propagated L' D' # M1"
    using decomp T n_d_y by auto

  show ?case
    proof
      assume "D \<in># learned_clss T"
      then have DLD': "D = D'"
        using DL T neq0_conv decomp n_d_y by fastforce
      have L_cKh: "atm_of L \<in> atm_of ` lits_of_l (c @ [Decided Kh])"
        using LH learned M DLD'[symmetric] confl LD' LD
        (* TODO Tune proof *)
        apply (auto simp add: image_iff dest!: in_CNot_implies_uminus)
        apply (metis atm_of_uminus)+ done
      then consider (Lc) "atm_of L \<in> atm_of ` lits_of_l c" and "atm_of L \<noteq> atm_of Kh" |
        (LKh) "atm_of L = atm_of Kh" and "atm_of L \<notin> atm_of ` lits_of_l c"
        using n_d_y M by (auto simp: atm_lit_of_set_lits_of_l)
      then have lev_L_c_Kh: "get_level (c @ [Decided Kh]) L \<ge> 1"
        by cases auto
      have "get_level (trail y) L = get_level (c @ [Decided Kh]) L + count_decided H"
        using get_rev_level_skip_end[OF L_cKh, of H] unfolding M by simp
      then have "get_level (trail y) L \<ge> i"
        using count_H lev_L_c_Kh by linarith
      then have i_le_bt_y: "i \<le> backtrack_lvl y"
        using cdcl\<^sub>W_M_level_inv_get_level_le_backtrack_lvl[OF lev, of L] by linarith
      have DD'[simp]: "remove1_mset L D = D' - {#L'#}"
        proof (rule ccontr)
          assume DD': "\<not> ?thesis"
          then have "L' \<in># remove1_mset L D" using DLD' LD by (metis LD' in_remove1_mset_neq)
          then have "get_level (trail y) L' \<le> get_maximum_level (trail y) (remove1_mset L D)"
            using get_maximum_level_ge_get_level by blast
          moreover
          have "\<forall>x \<in> atms_of (remove1_mset L D). x \<notin> atm_of ` lits_of_l (c @ Decided Kh # [])"
            using DH n_d_y unfolding M by (auto simp: atm_lit_of_set_lits_of_l)
          from get_maximum_level_skip_beginning[OF this, of H]
            have "get_maximum_level (trail y) (remove1_mset L D) =
            get_maximum_level H (remove1_mset L D)"
            unfolding M by (simp add: get_maximum_level_skip_beginning)
          moreover
            have "atm_of Kh \<notin> atm_of ` lits_of_l c'"
              using levT unfolding cdcl\<^sub>W_M_level_inv_def z
              by (auto simp: atm_lit_of_set_lits_of_l)
            then have "count_decided H < i"
              unfolding i_def z by auto
            then have "0 < i - count_decided H"
              by presburger
          ultimately have "get_maximum_level (trail y) (remove1_mset L D) < i"
            by (metis (no_types) count_decided_ge_get_maximum_level diff_is_0_eq diff_le_mono2
              not_le)
          moreover
            have "L \<in># remove1_mset L' D'"
              using DLD'[symmetric] DD' LD by (metis in_remove1_mset_neq)
            then have "get_maximum_level (trail y) (remove1_mset L' D') \<ge>
              get_level (trail y) L"
              using get_maximum_level_ge_get_level by blast
          moreover
            have "get_maximum_level (trail y) (remove1_mset L' D')
              < get_level (trail y) L"
              using \<open>get_level (trail y) L' \<le> get_maximum_level (trail y) (remove1_mset L D)\<close>
              calculation(1) i_le_bt_y levL by linarith
          ultimately show False using backtrack.hyps(4) by linarith
        qed
      then have LL': "L = L'"
        using LD LD' remove1_mset_eq_remove1_mset_same unfolding DLD'[symmetric] by fast

      have [simp]: "atm_of K \<notin> atm_of ` lits_of_l M2" and
        [simp]: "atm_of K \<notin> atm_of ` lits_of_l M3"
        using lev unfolding M3 cdcl\<^sub>W_M_level_inv_def by (auto simp: atm_lit_of_set_lits_of_l)
      { assume D: "remove1_mset L D' = {#}"
        then have j0: "j = 0" using levD j by (simp add: LL')
        have "\<forall>m \<in> set M1. \<not>is_decided m"
          using lev_K unfolding j0 M3 by (auto simp: atm_lit_of_set_lits_of_l image_Un
            filter_empty_conv)
        then have False using d by auto
      }
      moreover {
        assume D[simp]: "remove1_mset L D' \<noteq> {#}"
        have "i \<le> j"
          using lev count_H lev_K unfolding M3 d cdcl\<^sub>W_M_level_inv_def by (auto simp add:
            atm_lit_of_set_lits_of_l)
        have "j > 0" apply (rule ccontr)
          using \<open>i > 0\<close> lev_K unfolding M3 d
          by (auto simp add: rev_swap[symmetric] dest!: upt_decomp_lt)
        obtain L'' where
          "L''\<in># remove1_mset L D'" and
          L''D': "get_level (trail y) L'' = get_maximum_level (trail y)
            (remove1_mset L D')"
          using get_maximum_level_exists_lit_of_max_level[OF D, of "trail y"] by auto
        have L''M: "atm_of L'' \<in> atm_of ` lits_of_l (trail y)"
          using get_level_ge_0_atm_of_in[of 0 L'' "trail y" ] \<open>j>0\<close> levD L''D'
          i_le_bt_y levL by (simp add: LL' j)
        then have "L'' \<in> lits_of_l (Decided Kh # d)"
          proof -
            {
              assume L''H: "atm_of L'' \<in> atm_of ` lits_of_l H"
              then have "atm_of L'' \<notin> atm_of ` lits_of_l (c @ [Decided Kh])"
                using n_d_y unfolding M by (auto simp: lits_of_def atm_of_eq_atm_of)
              then have "get_level (trail y) L'' = get_level H L''"
                using L''H unfolding M by auto
              moreover have "get_level H L'' \<le> count_decided H"
                by auto
              ultimately have False
                using \<open>j>0\<close> \<open>i \<le> j\<close> L''D' LL' \<open>get_level H L'' \<le> count_decided H\<close> count_H(1) j
                unfolding count_H by presburger
            }
            moreover
              have "atm_of L'' \<in> atm_of ` lits_of_l H"
                using DD' DH \<open>L'' \<in># remove1_mset L D'\<close> atm_of_lit_in_atms_of LL' LD
                LD' by fastforce
            ultimately show ?thesis
              using DD' DH \<open>L'' \<in># remove1_mset L D'\<close> atm_of_lit_in_atms_of
              by auto
          qed
        moreover
          have "atm_of L'' \<in> atms_of (remove1_mset L D')"
            using \<open>L''\<in># remove1_mset L D'\<close> by (auto simp: atms_of_def)

          then have "atm_of L'' \<in> atm_of ` lits_of_l H"
            using DH unfolding DD' unfolding LL' by blast
        ultimately have False
          using n_d_y unfolding M3 d LL' by (auto simp: lits_of_def)
      }
      ultimately show False by blast
    qed
qed auto

lemma cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned:
  assumes
    "cdcl\<^sub>W_stgy y z" and
    "cdcl\<^sub>W_M_level_inv y" and
    "trail y = c @ Decided Kh # H" and
    "D \<notin># learned_clss y" and
    LD: "L \<in># D" and
    DH: "atms_of (remove1_mset L D) \<subseteq> atm_of ` lits_of_l H" and
    LH: "atm_of L \<notin> atm_of ` lits_of_l H" and
    "\<forall>T. conflicting y = Some T \<longrightarrow> trail y \<Turnstile>as CNot T" and
    "trail z = c' @ Decided Kh # H"
  shows "D \<notin># learned_clss z"
  using assms
proof induction
  case propagate'
  then show ?case
    by (auto elim: propagateE)
next
  case conflict'
  then show ?case
    by (auto elim: conflictE)
next
  case (other' T) note ns = this(1,2) and o = this(3) and lev = this(4) and trY = this(5) and
    notin = this(6) and LD = this(7) and DH = this(8) and LH = this(9) and confl = this(10) and
    trU = this(11)
  show ?case
    using cdcl\<^sub>W_o_cannot_learn[OF o lev trY notin LD DH LH confl ] trU by auto
qed

lemma rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned:
  assumes
    "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Decided K# H @ []))\<^sup>*\<^sup>* S z" and
    "cdcl\<^sub>W_all_struct_inv S" and
    "trail S = c @ Decided K # H" and
    "D \<notin># learned_clss S" and
    LD: "L \<in># D" and
    DH: "atms_of (remove1_mset L D) \<subseteq> atm_of ` lits_of_l H" and
    LH: "atm_of L \<notin> atm_of ` lits_of_l H" and
    "\<exists>c'. trail z = c' @ Decided K # H"
  shows "D \<notin># learned_clss z"
  using assms(1-4,8)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto[1]
next
  case (step T U) note st = this(1) and s = this(2) and IH = this(3)[OF this(4-6)]
    and lev = this(4) and trS = this(5) and DL_S = this(6) and trU = this(7)
  obtain c where c: "trail T = c @ Decided K # H" using s by auto
  obtain c' where c': "trail U = c' @ Decided K # H" using trU by blast
  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
    proof -
      have "\<forall>p pa. \<exists>s sa. \<forall>sb sc sd se. (\<not> p\<^sup>*\<^sup>* (sb::'st) sc \<or> p s sa \<or> pa\<^sup>*\<^sup>* sb sc)
        \<and> (\<not> pa s sa \<or> \<not> p\<^sup>*\<^sup>* sd se \<or> pa\<^sup>*\<^sup>* sd se)"
        by (metis (no_types) mono_rtranclp)
      then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
        using st by blast
      then show ?thesis
        using rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
    qed
  then have lev': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv[of S T] lev by auto
  then have confl': "\<forall>Ta. conflicting T = Some Ta \<longrightarrow> trail T \<Turnstile>as CNot Ta"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by blast
  show ?case
    apply (rule cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned[OF _ _ c _ LD DH LH confl' c'])
    using s lev' IH c unfolding cdcl\<^sub>W_all_struct_inv_def by blast+
qed

text \<open>\cwref{lem:prop:cdclredundancy}{theorem 2.9.7 page 83}\<close>
lemma cdcl\<^sub>W_stgy_no_relearned_clause:
  assumes
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    st': "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    bt: "backtrack S T" and
    confl: "conflicting S = Some E" and
    already_learned: "E \<in># clauses S" and
    R: "trail R = []"
  shows False
proof -
  have M_lev: "cdcl\<^sub>W_M_level_inv R"
    using invR unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have "cdcl\<^sub>W_M_level_inv S"
    using M_lev assms(2) rtranclp_cdcl\<^sub>W_stgy_consistent_inv by blast
  with bt obtain L K :: "'v literal" and M1 M2_loc :: "('v, 'v clause) ann_lits"
    and i :: nat where
     T: "T \<sim> cons_trail (Propagated L E)
       (reduce_trail_to M1 (add_learned_cls E
         (update_backtrack_lvl i (update_conflicting None S))))"
      and
    decomp: "(Decided K # M1, M2_loc) \<in>
                set (get_all_ann_decomposition (trail S))" and
    LD: "L \<in># E" and
    k: "get_level (trail S) L = backtrack_lvl S" and
    level: "get_level (trail S) L = get_maximum_level (trail S) E" and
    confl_S: "conflicting S = Some E" and
    i: "i = get_maximum_level (trail S) (remove1_mset L E)" and
    lev_K: "get_level (trail S) K = Suc i"
    using confl apply (induction rule: backtrack.induct)
      apply (simp del: state_simp)
      by blast
  obtain M2 where
    M: "trail S = M2 @ Decided K # M1"
    using get_all_ann_decomposition_exists_prepend[OF decomp] unfolding i by (metis append_assoc)
  let ?E' = "remove1_mset L E"
  have invS: "cdcl\<^sub>W_all_struct_inv S"
    using invR rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart st' by blast
  then have conf: "cdcl\<^sub>W_conflicting S" unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have "trail S \<Turnstile>as CNot E" unfolding cdcl\<^sub>W_conflicting_def confl_S by auto
  then have MD: "trail S \<Turnstile>as CNot E" by auto
  then have MD': "trail S \<Turnstile>as CNot ?E'" using true_annot_CNot_diff by blast
  have lev': "cdcl\<^sub>W_M_level_inv S" using invS unfolding cdcl\<^sub>W_all_struct_inv_def by blast

  have lev: "cdcl\<^sub>W_M_level_inv R" using invR unfolding cdcl\<^sub>W_all_struct_inv_def by blast
  then have vars_of_D: "atms_of ?E' \<subseteq> atm_of ` lits_of_l M1"
    using backtrack_atms_of_D_in_M1[OF lev' _ decomp _ _ _, of E _ i T] confl_S conf T decomp k
    level lev' lev_K unfolding i cdcl\<^sub>W_conflicting_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have "no_dup (trail S)" using lev' by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have vars_in_M1:
    "\<forall>x \<in> atms_of ?E'. x \<notin> atm_of ` lits_of_l (M2 @ [Decided K])"
    unfolding Set.Ball_def apply (intro impI allI)
      apply (rule vars_of_D distinct_atms_of_incl_not_in_other[of
      "M2 @ Decided K # []" M1 ?E'])
      using \<open>no_dup (trail S)\<close> M vars_of_D by simp_all
  have M1_D: "M1 \<Turnstile>as CNot ?E'"
    using vars_in_M1 true_annots_remove_if_notin_vars[of "M2 @ Decided K # []" M1 "CNot ?E'"]
    MD' M by simp

  have "backtrack_lvl S > 0" using lev' unfolding cdcl\<^sub>W_M_level_inv_def M by auto

  obtain M1' K' Ls where
    M': "trail S = Ls @ Decided K' # M1'" and
    Ls: "\<forall>l \<in> set Ls. \<not> is_decided l" and
    "set M1 \<subseteq> set M1'"
    proof -
      let ?Ls = "takeWhile (Not o is_decided) (trail S)"
      have MLs: "trail S = ?Ls @ dropWhile (Not o is_decided) (trail S)"
        by auto
      have "dropWhile (Not o is_decided) (trail S) \<noteq> []" unfolding M by auto
      moreover
        from hd_dropWhile[OF this] have "is_decided(hd (dropWhile (Not o is_decided) (trail S)))"
          by simp
      ultimately
        obtain K' where
          K'k: "dropWhile (Not o is_decided) (trail S)
            = Decided K' # tl (dropWhile (Not o is_decided) (trail S))"
          by (cases "dropWhile (Not \<circ> is_decided) (trail S)";
              cases "hd (dropWhile (Not \<circ> is_decided) (trail S))")
            simp_all
      moreover have "\<forall>l \<in> set ?Ls. \<not>is_decided l" using set_takeWhileD by force
      moreover have "set M1 \<subseteq> set (tl (dropWhile (Not o is_decided) (trail S)))"
        unfolding M by (induction M2) auto
      ultimately show ?thesis using that[of "takeWhile (Not \<circ> is_decided) (trail S)"
        K' "tl (dropWhile (Not o is_decided) (trail S))"] MLs by simp
    qed

  have M1'_D: "M1' \<Turnstile>as CNot ?E'" using M1_D \<open>set M1 \<subseteq> set M1'\<close> by (auto intro: true_annots_mono)
  have "-L \<in> lits_of_l (trail S)" using conf confl_S LD unfolding cdcl\<^sub>W_conflicting_def
    by (auto simp: in_CNot_implies_uminus)
  have L_notin: "atm_of L \<in> atm_of ` lits_of_l Ls \<or> atm_of L = atm_of K'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "atm_of L \<notin> atm_of ` lits_of_l (Decided K' # rev Ls)" by simp
      then have "get_level (trail S) L = get_level M1' L"
        unfolding M' by auto
      moreover
        have "get_level M1' L \<le> count_decided M1'"
          by auto
        then have "get_level M1' L < backtrack_lvl S"
          using lev' unfolding cdcl\<^sub>W_M_level_inv_def M'
          by (auto simp del: count_decided_ge_get_level)
      ultimately show False using k by linarith
    qed
  obtain Y Z where
    RY: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R Y" and
    YZ: "cdcl\<^sub>W_stgy Y Z" and
    nt: "\<not> (\<exists>c. trail Y = c @ Decided K' # M1' @ [])" and
    Z: "(\<lambda>a b. cdcl\<^sub>W_stgy a b \<and> (\<exists>c. trail a = c @ Decided K' # M1' @ []))\<^sup>*\<^sup>* Z S"
    using rtranclp_cdcl\<^sub>W_restart_new_decided_at_beginning_is_decide'[OF st' _ _ lev, of Ls K'
      M1' "[]"] unfolding R M' by auto
  have [simp]: "cdcl\<^sub>W_M_level_inv Y"
    using RY lev rtranclp_cdcl\<^sub>W_stgy_consistent_inv by blast
  obtain M' where trZ: "trail Z = M' @ Decided K' # M1'"
    using rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end[OF Z] M' by auto
  have "no_dup (trail Y)"
    using RY lev rtranclp_cdcl\<^sub>W_stgy_consistent_inv unfolding cdcl\<^sub>W_M_level_inv_def by blast
  then have
    dec: "decide Y Z" and
    n_s: "no_step conflict_or_propagate Y"
    using cdcl\<^sub>W_stgy_trail_has_new_decided_is_decide_step[OF YZ nt Z] M' by auto
  have trY: "trail Y = M1'"
    proof -
      obtain M' where M: "trail Z = M' @ Decided K' # M1'"
        using rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_trail_end[OF Z] M' by auto
      then show ?thesis using dec nt by (cases M') (auto elim: decideE)
    qed
  have Y_CT: "conflicting Y = None" using dec by (auto elim: decideE)
  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* R Y" by (simp add: RY rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  then have "init_clss Y = init_clss R" using rtranclp_cdcl\<^sub>W_restart_init_clss[of R Y] M_lev by auto
  { assume DL: "E \<in># clauses Y"
    have "atm_of L \<notin> atm_of ` lits_of_l M1"
      apply (rule backtrack_lit_skiped[of _ S])
      using decomp i k lev' lev_K unfolding cdcl\<^sub>W_M_level_inv_def by auto
    then have LM1: "undefined_lit M1 L"
      by (metis Decided_Propagated_in_iff_in_lits_of_l atm_of_uminus image_eqI)
    have L_trY: "undefined_lit (trail Y) L"
      using L_notin \<open>no_dup (trail S)\<close> unfolding defined_lit_map trY M'
      by (auto simp add: image_iff lits_of_def)
    have "Ex (propagate Y)"
      using propagate_rule[of Y E L] DL M1'_D L_trY Y_CT trY LD by auto
    then have False using n_s propagate' by auto
  }
  moreover {
    assume DL: "E \<notin># clauses Y"
    have lY_lZ: "learned_clss Y = learned_clss Z"
      using dec by (auto elim: decideE)
    have invZ: "cdcl\<^sub>W_all_struct_inv Z"
      by (meson RY YZ invR r_into_rtranclp rtranclp_cdcl\<^sub>W_all_struct_inv_inv
        rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
    have n: "E \<notin># learned_clss Z"
       using DL lY_lZ YZ unfolding clauses_def by auto
    have "E \<notin>#learned_clss S"
      apply (rule rtranclp_cdcl\<^sub>W_stgy_with_trail_end_has_not_been_learned[OF Z invZ trZ])
          apply (simp add: n)
         using LD apply simp
        apply (metis (no_types, lifting) \<open>set M1 \<subseteq> set M1'\<close> image_mono order_trans
          vars_of_D lits_of_def)
       using L_notin \<open>no_dup (trail S)\<close> unfolding M' by (auto simp add: image_iff lits_of_def)
    then have False
      using already_learned DL confl st' M_lev rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss[of R S]
      unfolding M'
      by (simp add: \<open>init_clss Y = init_clss R\<close> clauses_def confl_S
        rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss)
  }
  ultimately show False by blast
qed

lemma rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    invR: "cdcl\<^sub>W_all_struct_inv R" and
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S" and
    dist: "distinct_mset (clauses R)" and
    R: "trail R = []"
  shows "distinct_mset (clauses S)"
  using st
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using dist by simp
next
  case (step S T) note st = this(1) and s = this(2) and IH = this(3)
  from s show ?case
    proof (cases rule: cdcl\<^sub>W_stgy.cases)
      case conflict'
      then show ?thesis
        using IH  by (auto elim: conflictE)
    next
      case propagate'
      then show ?thesis
        using IH  by (auto elim: propagateE)
    next
      case other' note ns = this(1,2) and o = this(3)
      show ?thesis
        using o IH
        proof (cases rule: cdcl\<^sub>W_o_rule_cases)
          case backtrack
          moreover
            have "cdcl\<^sub>W_all_struct_inv S"
              using invR rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv st by blast
            then have "cdcl\<^sub>W_M_level_inv S"
              unfolding cdcl\<^sub>W_all_struct_inv_def by auto
          ultimately obtain E where
            E: "conflicting S = Some E" and
            cls_S': "clauses T = {#E#} + clauses S"
            by (auto simp: cdcl\<^sub>W_M_level_inv_decomp elim!: backtrackE)
          then have "E \<notin># clauses S"
            using cdcl\<^sub>W_stgy_no_relearned_clause R invR local.backtrack st by blast
          then show ?thesis using IH E cls_S' by (simp add: distinct_mset_add_single)
        qed (auto elim: decideE skipE resolveE)
    qed
qed

lemma cdcl\<^sub>W_stgy_distinct_mset_clauses:
  assumes
    st: "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state N) S" and
    no_duplicate_clause: "distinct_mset N" and
    no_duplicate_in_clause: "distinct_mset_mset N"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF _ st] assms
  by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def)

subsubsection \<open>Decrease of a Measure\<close>
fun cdcl\<^sub>W_restart_measure where
"cdcl\<^sub>W_restart_measure S =
  [(3::nat) ^ (card (atms_of_mm (init_clss S))) - card (set_mset (learned_clss S)),
    if conflicting S = None then 1 else 0,
    if conflicting S = None then card (atms_of_mm (init_clss S)) - length (trail S)
    else length (trail S)
    ]"

lemma length_model_le_vars:
  assumes
    "no_strange_atm S" and
    no_d: "no_dup (trail S)" and
    "finite (atms_of_mm (init_clss S))"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
proof -
  obtain M N U k D where S: "state S = (M, N, U, k, D)" by (cases "state S", auto)
  have "finite (atm_of ` lits_of_l (trail S))"
    using assms(1,3) unfolding S by (auto simp add: finite_subset)
  have "length (trail S) = card (atm_of ` lits_of_l (trail S))"
    using no_dup_length_eq_card_atm_of_lits_of_l no_d by blast
  then show ?thesis using assms(1) unfolding no_strange_atm_def
  by (auto simp add: assms(3) card_mono)
qed

lemma length_model_le_vars_all_inv:
  assumes "cdcl\<^sub>W_all_struct_inv S"
  shows "length (trail S) \<le> card (atms_of_mm (init_clss S))"
  using assms length_model_le_vars[of S] unfolding cdcl\<^sub>W_all_struct_inv_def
  by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)

lemma learned_clss_less_upper_bound:
  fixes S :: 'st
  assumes
    "distinct_cdcl\<^sub>W_state S" and
    "\<forall>s \<in># learned_clss S. \<not>tautology s"
  shows "card(set_mset (learned_clss S)) \<le> 3 ^ card (atms_of_mm (learned_clss S))"
proof -
  have "set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (learned_clss S))"
    apply (rule simplified_in_simple_clss)
    using assms unfolding distinct_cdcl\<^sub>W_state_def by auto
  then have "card(set_mset (learned_clss S))
    \<le> card (simple_clss (atms_of_mm (learned_clss S)))"
    by (simp add: simple_clss_finite card_mono)
  then show ?thesis
    by (meson atms_of_ms_finite simple_clss_card finite_set_mset order_trans)
qed


lemma cdcl\<^sub>W_restart_measure_decreasing:
  fixes S :: 'st
  assumes
    "cdcl\<^sub>W_restart S S'" and
    no_restart:
      "\<not>(learned_clss S \<subseteq># learned_clss S' \<and> [] = trail S' \<and> conflicting S' = None)"
    (*no restart*) and
    no_forget: "learned_clss S \<subseteq># learned_clss S'" (*no forget*) and
    no_relearn: "\<And>S'. backtrack S S' \<Longrightarrow> \<forall>T. conflicting S = Some T \<longrightarrow> T \<notin># learned_clss S"
      and
    alien: "no_strange_atm S" and
    M_level: "cdcl\<^sub>W_M_level_inv S" and
    no_taut: "\<forall>s \<in># learned_clss S. \<not>tautology s" and
    no_dup: "distinct_cdcl\<^sub>W_state S" and
    confl: "cdcl\<^sub>W_conflicting S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  using assms(1) M_level assms(2,3)
proof (induct rule: cdcl\<^sub>W_restart_all_induct)
  case (propagate C L) note conf = this(1) and undef = this(5) and T = this(6)
  have propa: "propagate S (cons_trail (Propagated L C) S)"
    using propagate_rule[OF propagate.hyps(1,2)] propagate.hyps by auto
  then have no_dup': "no_dup (Propagated L C # trail S)"
    using M_level cdcl\<^sub>W_M_level_inv_decomp(2) undef defined_lit_map by auto

  let ?N = "init_clss S"
  have "no_strange_atm (cons_trail (Propagated L C) S)"
    using alien cdcl\<^sub>W_restart.propagate cdcl\<^sub>W_restart_no_strange_atm_inv propa M_level by blast
  then have "atm_of ` lits_of_l (Propagated L C # trail S)
    \<subseteq> atms_of_mm (init_clss S)"
    using undef unfolding no_strange_atm_def by auto
  then have "card (atm_of ` lits_of_l (Propagated L C # trail S))
    \<le> card (atms_of_mm (init_clss S))"
    by (meson atms_of_ms_finite card_mono finite_set_mset)
  then have "length (Propagated L C # trail S) \<le> card (atms_of_mm ?N)"
    using no_dup_length_eq_card_atm_of_lits_of_l no_dup' by fastforce
  then have H: "card (atms_of_mm (init_clss S)) - length (trail S)
    = Suc (card (atms_of_mm (init_clss S)) - Suc (length (trail S)))"
    by simp
  show ?case using conf T undef by (auto simp: H lexn3_conv)
next
  case (decide L) note conf = this(1) and undef = this(2) and T = this(4)
  moreover
    have dec: "decide S (cons_trail (Decided L) (incr_lvl S))"
      using decide_rule decide.hyps by force
    then have cdcl\<^sub>W_restart:"cdcl\<^sub>W_restart S (cons_trail (Decided L) (incr_lvl S))"
      using cdcl\<^sub>W_restart.simps cdcl\<^sub>W_o.intros by blast
  moreover
    have lev: "cdcl\<^sub>W_M_level_inv (cons_trail (Decided L) (incr_lvl S))"
      using cdcl\<^sub>W_restart M_level cdcl\<^sub>W_restart_consistent_inv[OF cdcl\<^sub>W_restart] by auto
    then have no_dup: "no_dup (Decided L # trail S)"
      using undef unfolding cdcl\<^sub>W_M_level_inv_def by auto
    have "no_strange_atm (cons_trail (Decided L) (incr_lvl S))"
      using M_level alien calculation(4) cdcl\<^sub>W_restart_no_strange_atm_inv by blast
    then have "length (Decided L # (trail S))
      \<le> card (atms_of_mm (init_clss S))"
      using no_dup undef
      length_model_le_vars[of "cons_trail (Decided L) (incr_lvl S)"]
      by fastforce
  ultimately show ?case using conf by (simp add: lexn3_conv)
next
  case (skip L C' M D) note tr = this(1) and conf = this(2) and T = this(5)
  show ?case using conf T by (simp add: tr lexn3_conv)
next
  case conflict
  then show ?case by (simp add: lexn3_conv)
next
  case resolve
  then show ?case using finite by (simp add: lexn3_conv)
next
  case (backtrack L D K i M1 M2 T) note conf = this(1) and decomp = this(3) and T = this(8) and
  lev = this(9)
  have bt: "backtrack S T"
    using backtrack_rule[OF backtrack.hyps] by auto
  have "D \<notin># learned_clss S"
    using no_relearn conf bt by auto
  then have card_T:
    "card (set_mset ({#D#} + learned_clss S)) = Suc (card (set_mset (learned_clss S)))"
    by simp
  have "distinct_cdcl\<^sub>W_state T"
    using bt M_level distinct_cdcl\<^sub>W_state_inv no_dup other cdcl\<^sub>W_o.intros cdcl\<^sub>W_bj.intros by blast
  moreover have "\<forall>s\<in>#learned_clss T. \<not> tautology s"
    using learned_clss_are_not_tautologies[OF cdcl\<^sub>W_restart.other[OF cdcl\<^sub>W_o.bj[OF
      cdcl\<^sub>W_bj.backtrack[OF bt]]]] M_level no_taut confl by auto
  ultimately have "card (set_mset (learned_clss T)) \<le> 3 ^ card (atms_of_mm (learned_clss T))"
      by (auto simp: learned_clss_less_upper_bound)
    then have H: "card (set_mset ({#D#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm ({#D#} + learned_clss S))"
      using T decomp M_level by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
  moreover
    have "atms_of_mm ({#D#} + learned_clss S) \<subseteq> atms_of_mm (init_clss S)"
      using alien conf unfolding no_strange_atm_def by auto
    then have card_f: "card (atms_of_mm ({#D#} + learned_clss S))
      \<le> card (atms_of_mm (init_clss S))"
      by (meson atms_of_ms_finite card_mono finite_set_mset)
    then have "(3::nat) ^ card (atms_of_mm ({#D#} + learned_clss S))
      \<le> 3 ^ card (atms_of_mm (init_clss S))" by simp
  ultimately have "(3::nat) ^ card (atms_of_mm (init_clss S))
    \<ge> card (set_mset ({#D#} + learned_clss S))"
    using le_trans by blast
  then show ?case using decomp diff_less_mono2 card_T T M_level
    by (auto simp: cdcl\<^sub>W_M_level_inv_decomp lexn3_conv)
next
  case restart
  then show ?case using alien by (auto simp: state_eq_def simp del: state_simp)
next
  case (forget C T) note no_forget = this(9)
  then have "C \<in># learned_clss S" and "C \<notin># learned_clss T"
    using forget.hyps by auto
  then have "\<not> learned_clss S \<subseteq># learned_clss T"
     by (auto simp add: mset_subset_eqD)
  then show ?case using no_forget by blast
qed

lemma propagate_measure_decreasing:
  fixes S :: 'st
  assumes "propagate S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) propagate apply blast
           using assms(1) apply (auto simp add: propagate.simps)[3]
        using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def)
  done

lemma conflict_measure_decreasing:
  fixes S :: 'st
  assumes "conflict S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) conflict apply blast
            using assms(1) apply (auto simp: state_eq_def simp del: state_simp elim!: conflictE)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def elim: conflictE)
  done

lemma decide_measure_decreasing:
  fixes S :: 'st
  assumes "decide S S'" and "cdcl\<^sub>W_all_struct_inv S"
  shows "(cdcl\<^sub>W_restart_measure S', cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
  apply (rule cdcl\<^sub>W_restart_measure_decreasing)
  using assms(1) decide other apply blast
            using assms(1) apply (auto simp: state_eq_def simp del: state_simp elim!: decideE)[3]
         using assms(2) apply (auto simp add: cdcl\<^sub>W_all_struct_inv_def elim: decideE)
  done

lemma cdcl\<^sub>W_stgy_step_decreasing:
  fixes R S T :: 'st
  assumes "cdcl\<^sub>W_stgy S T" and
  "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* R S"
  "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_restart_measure T, cdcl\<^sub>W_restart_measure S) \<in> lexn less_than 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv S"
    using assms
    by (metis rtranclp_unfold rtranclp_cdcl\<^sub>W_all_struct_inv_inv 
      tranclp_cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart)
  with assms show ?thesis
    proof induction
      case (conflict' V) note cp = this(1) and inv = this(5)
      show ?case
        using \<open>cdcl\<^sub>W_all_struct_inv S\<close> conflict_measure_decreasing cp by blast
    next
      case (propagate' V) note cp = this(1) and inv = this(5)
      show ?case
        using \<open>cdcl\<^sub>W_all_struct_inv S\<close> propagate_measure_decreasing cp by blast
    next
      case (other' T) note n_s =this(1,2) and o = this(3) and H = this(4,5,6,7) and
        struct_inv = this(7)
      have inv: "cdcl\<^sub>W_M_level_inv S"
        using cdcl\<^sub>W_all_struct_inv_def other'.prems(4) by blast
      with o show ?case
      proof (cases rule:cdcl\<^sub>W_o_rule_cases)
        case (decide)
        then show ?thesis using decide_measure_decreasing H by blast
      next
        case backtrack note bt = this(1)
        then have no_relearn: "\<forall>T. conflicting S = Some T \<longrightarrow> T \<notin># learned_clss S"
          using cdcl\<^sub>W_stgy_no_relearned_clause[of R S T] H
          unfolding cdcl\<^sub>W_all_struct_inv_def clauses_def by auto
        show ?thesis
          apply (rule cdcl\<^sub>W_restart_measure_decreasing)
                  using bt cdcl\<^sub>W_bj.backtrack cdcl\<^sub>W_o.bj other apply (simp; fail)
                 using bt inv unfolding cdcl\<^sub>W_all_struct_inv_def
                 cdcl\<^sub>W_M_level_inv_def apply (auto elim: backtrackE; fail)[]
                using bt inv unfolding cdcl\<^sub>W_all_struct_inv_def
                 cdcl\<^sub>W_M_level_inv_def apply (auto elim: backtrackE; fail)[]
               using bt no_relearn apply auto[]
              using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
             using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def apply simp
            using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
           using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def apply simp
          using struct_inv unfolding cdcl\<^sub>W_all_struct_inv_def by simp
      next
        case skip
        then show ?thesis by (auto simp: lexn3_conv elim!: skipE)
      next
        case resolve
        then show ?thesis by (auto simp: lexn3_conv elim!: resolveE)
      qed
    qed
qed

text \<open>Roughly corresponds to \cwref{theo:prop:cdcltermlc}{theorem 2.9.15 page 86}
  (using a different bound)\<close>
lemma tranclp_cdcl\<^sub>W_stgy_decreasing:
  fixes R S T :: 'st
  assumes "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ R S"
  "trail R = []" and
  "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure R) \<in> lexn less_than 3"
  using assms
  apply induction
   using cdcl\<^sub>W_stgy_step_decreasing[of R _ R] apply blast
  using cdcl\<^sub>W_stgy_step_decreasing[of _ _ R] tranclp_into_rtranclp[of cdcl\<^sub>W_stgy R]
  lexn_transI[OF trans_less_than, of 3] unfolding trans_def by blast

lemma tranclp_cdcl\<^sub>W_stgy_S0_decreasing:
  fixes R S T :: 'st
  assumes
    pl: "cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S" and
    no_dup: "distinct_mset_mset N"
  shows "(cdcl\<^sub>W_restart_measure S, cdcl\<^sub>W_restart_measure (init_state N)) \<in> lexn less_than 3"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_dup unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then show ?thesis using pl tranclp_cdcl\<^sub>W_stgy_decreasing init_state_trail by blast
qed

lemma wf_tranclp_cdcl\<^sub>W_stgy:
  "wf {(S::'st, init_state N)| S N. distinct_mset_mset N \<and> cdcl\<^sub>W_stgy\<^sup>+\<^sup>+ (init_state N) S}"
  apply (rule wf_wf_if_measure'_notation2[of "lexn less_than 3" _ _ cdcl\<^sub>W_restart_measure])
   apply (simp add: wf wf_lexn)
  using tranclp_cdcl\<^sub>W_stgy_S0_decreasing by blast

end

end
