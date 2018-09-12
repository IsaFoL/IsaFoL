theory Watched_Literals_Watch_List_Initialisation
  imports Watched_Literals_Watch_List Watched_Literals_Initialisation
begin


subsection \<open>Initialisation\<close>

type_synonym 'v twl_st_wl_init = \<open>'v twl_st_wl \<times> 'v clauses\<close>

fun get_trail_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_init_wl ((M, _, _, _, _, _, _), _) = M\<close>

fun get_conflict_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_init_wl ((_, _, D, _, _, _, _), _) = D\<close>

fun literals_to_update_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_init_wl ((_, _, _, _, _, Q, _), _) = Q\<close>

fun other_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_init_wl ((_, _, _, _, _, _, _), OC) = OC\<close>

fun add_empty_conflict_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  add_empty_conflict_init_wl_def[simp del]:
   \<open>add_empty_conflict_init_wl ((M, N, D, NE, UE, Q, W), OC) =
       ((M, N, Some {#}, NE, UE, {#}, W), add_mset {#} OC)\<close>

fun propagate_unit_init_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  propagate_unit_init_wl_def[simp del]:
   \<open>propagate_unit_init_wl L ((M, N, D, NE, UE, Q, W), OC) =
       ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, add_mset (-L) Q, W), OC)\<close>


fun already_propagated_unit_init_wl :: \<open>'v clause \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  already_propagated_unit_init_wl_def[simp del]:
   \<open>already_propagated_unit_init_wl C ((M, N, D, NE, UE, Q, W), OC) =
       ((M, N, D, add_mset C NE, UE, Q, W), OC)\<close>


fun set_conflict_init_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  set_conflict_init_wl_def[simp del]:
   \<open>set_conflict_init_wl L ((M, N, _, NE, UE, Q, W), OC) =
       ((M, N, Some {#L#}, add_mset {#L#} NE, UE, {#}, W), OC)\<close>


fun add_to_clauses_init_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  add_to_clauses_init_wl_def[simp del]:
   \<open>add_to_clauses_init_wl C ((M, N, D, NE, UE, Q, W), OC) = do {
        i \<leftarrow> get_fresh_index N;
        let b = (length C = 2);
        let W = W((C!0) := W (C!0) @ [(i, C!1, b)], (C!1) := W (C!1) @ [(i, C ! 0, b)]);
        RETURN ((M, fmupd i (C, True) N, D, NE, UE, Q, W), OC)
    }\<close>


definition init_dt_step_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  \<open>init_dt_step_wl C S =
  (case get_conflict_init_wl S of
    None \<Rightarrow>
    if length C = 0
    then RETURN (add_empty_conflict_init_wl S)
    else if length C = 1
    then
      let L = hd C in
      if undefined_lit (get_trail_init_wl S) L
      then RETURN (propagate_unit_init_wl L S)
      else if L \<in> lits_of_l (get_trail_init_wl S)
      then RETURN (already_propagated_unit_init_wl (mset C) S)
      else RETURN (set_conflict_init_wl L S)
    else
        add_to_clauses_init_wl C S
  | Some D \<Rightarrow>
      RETURN (add_to_other_init C S))\<close>

definition init_dt_wl :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  \<open>init_dt_wl CS = nfoldli CS (\<lambda>_. True) init_dt_step_wl\<close>

definition state_wl_l_init :: \<open>('v twl_st_wl_init \<times> 'v twl_st_l_init) set\<close> where
  \<open>state_wl_l_init = {(S, S'). (fst S, fst S') \<in> state_wl_l None \<and>
      other_clauses_init_wl S = other_clauses_l_init S'}\<close>


fun all_blits_are_in_problem_init where
  [simp del]: \<open>all_blits_are_in_problem_init (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
      (\<forall>L. (\<forall>(i, K, b)\<in>#mset (W L). K \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))))\<close>

text \<open>We assume that no clause has been deleted during initialisation. The definition is
  slightly redundant since \<^term>\<open>i \<in># dom_m N\<close> is already entailed by
  \<^term>\<open>fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#})\<close>.\<close>
fun correct_watching_init :: \<open>'v twl_st_wl_init \<Rightarrow> bool\<close> where
  [simp del]: \<open>correct_watching_init ((M, N, D, NE, UE, Q, W), _) \<longleftrightarrow>
    all_blits_are_in_problem_init (M, N, D, NE, UE, Q, W) \<and>
    (\<forall>L.
        (\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<and> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
           is_binary N (i, K, b)) \<and>
        fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

named_theorems twl_st_wl_init

lemma [twl_st_wl_init]:
  assumes \<open>(S, S') \<in> state_wl_l_init\<close>
  shows
    \<open>get_conflict_l_init S' = get_conflict_init_wl S\<close>
    \<open>get_trail_l_init S' = get_trail_init_wl S\<close>
    \<open>other_clauses_l_init S' = other_clauses_init_wl S\<close>
    \<open>count_decided (get_trail_l_init S') = count_decided (get_trail_init_wl S)\<close>
  using assms
  by (solves \<open>cases S; cases S'; auto simp: state_wl_l_init_def state_wl_l_def\<close>)+

lemma [twl_st_wl_init]:
  \<open>get_trail_wl (fst T) = get_trail_init_wl T\<close>
  \<open>get_conflict_wl (fst T) = get_conflict_init_wl T\<close>
  by (cases T; auto simp: correct_watching.simps correct_watching_init.simps; fail)+

lemma in_clause_to_update_in_dom_mD:
  \<open>bb \<in># clause_to_update L (a, aa, ab, ac, ad, {#}, {#}) \<Longrightarrow> bb \<in># dom_m aa\<close>
  unfolding clause_to_update_def
  by force
lemma correct_watching_init_correct_watching:
  \<open>correct_watching_init T \<Longrightarrow> correct_watching (fst T)\<close>
  by (cases T)
    (fastforce simp: correct_watching.simps correct_watching_init.simps filter_mset_eq_conv
      all_blits_are_in_problem.simps all_blits_are_in_problem_init.simps
      in_clause_to_update_in_dom_mD)

lemma image_mset_Suc: \<open>Suc `# {#C \<in># M. P C#} = {#C \<in># Suc `# M. P (C-1)#}\<close>
  by (induction M) auto

lemma correct_watching_init_add_unit:
  assumes \<open>correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  shows \<open>correct_watching_init ((M, N, D, add_mset C NE, UE, Q, W), OC)\<close>
proof -
  have [intro!]: \<open>(a, x) \<in> set (W L) \<Longrightarrow> a \<in># dom_m N \<Longrightarrow> b \<in> set (N \<propto>a)  \<Longrightarrow>
       b \<notin># all_lits_of_mm {#mset (fst x). x \<in># ran_m N#} \<Longrightarrow> b \<in># all_lits_of_mm NE\<close>
    for x b F a L
    unfolding ran_m_def
    by (auto dest!: multi_member_split simp: all_lits_of_mm_add_mset in_clause_in_all_lits_of_m)

  show ?thesis
    using assms
    unfolding correct_watching_init.simps clause_to_update_def Ball_def
    by (fastforce simp: correct_watching.simps all_lits_of_mm_add_mset
        all_lits_of_m_add_mset Ball_def all_conj_distrib clause_to_update_def
        all_blits_are_in_problem_init.simps all_lits_of_mm_union
        dest!: )
qed

lemma correct_watching_init_propagate:
  \<open>correct_watching_init ((L # M, N, D, NE, UE, Q, W), OC) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  \<open>correct_watching_init ((M, N, D, NE, UE, add_mset C Q, W), OC) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  unfolding correct_watching_init.simps clause_to_update_def Ball_def
  by (auto simp: correct_watching.simps all_lits_of_mm_add_mset
      all_lits_of_m_add_mset Ball_def all_conj_distrib clause_to_update_def
      all_blits_are_in_problem_init.simps)

lemma all_blits_are_in_problem_cons[simp]:
  \<open>all_blits_are_in_problem_init (Propagated L i # a, aa, ab, ac, ad, ae, b) \<longleftrightarrow>
     all_blits_are_in_problem_init (a, aa, ab, ac, ad, ae, b)\<close>
  \<open>all_blits_are_in_problem_init (Decided L # a, aa, ab, ac, ad, ae, b) \<longleftrightarrow>
     all_blits_are_in_problem_init (a, aa, ab, ac, ad, ae, b)\<close>
  \<open>all_blits_are_in_problem_init (a, aa, ab, ac, ad, add_mset L ae, b) \<longleftrightarrow>
     all_blits_are_in_problem_init (a, aa, ab, ac, ad, ae, b)\<close>
  \<open>NO_MATCH None y \<Longrightarrow> all_blits_are_in_problem_init (a, aa, y, ac, ad, ae, b) \<longleftrightarrow>
     all_blits_are_in_problem_init (a, aa, None, ac, ad, ae, b)\<close>
  \<open>NO_MATCH {#} ae \<Longrightarrow> all_blits_are_in_problem_init (a, aa, y, ac, ad, ae, b) \<longleftrightarrow>
     all_blits_are_in_problem_init (a, aa, y, ac, ad, {#}, b)\<close>
  by (auto simp: all_blits_are_in_problem_init.simps)

lemma correct_watching_init_cons[simp]:
  \<open>NO_MATCH None y \<Longrightarrow> correct_watching_init ((a, aa, y, ac, ad, ae, b), OC) \<longleftrightarrow>
     correct_watching_init ((a, aa, None, ac, ad, ae, b), OC)\<close>
  \<open>NO_MATCH {#} ae \<Longrightarrow> correct_watching_init ((a, aa, y, ac, ad, ae, b), OC) \<longleftrightarrow>
     correct_watching_init ((a, aa, y, ac, ad, {#}, b), OC)\<close>
     apply (auto simp: correct_watching_init.simps clause_to_update_def)
   apply (subst (asm) all_blits_are_in_problem_cons(4))
  apply auto
   apply (subst all_blits_are_in_problem_cons(4))
  apply auto
   apply (subst (asm) all_blits_are_in_problem_cons(5))
  apply auto
   apply (subst all_blits_are_in_problem_cons(5))
  apply auto
  done


lemma clause_to_update_mapsto_upd_notin:
  assumes
    i: \<open>i \<notin># dom_m N\<close>
  shows
  \<open>clause_to_update L (M, N(i \<hookrightarrow> C'), C, NE, UE, WS, Q) =
    (if L \<in> set (watched_l C')
     then add_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q))
     else (clause_to_update L (M, N, C, NE, UE, WS, Q)))\<close>
  \<open>clause_to_update L (M, fmupd i (C', b) N, C, NE, UE, WS, Q) =
    (if L \<in> set (watched_l C')
     then add_mset i (clause_to_update L (M, N, C, NE, UE, WS, Q))
     else (clause_to_update L (M, N, C, NE, UE, WS, Q)))\<close>
  using assms
  by (auto simp: clause_to_update_def intro!: filter_mset_cong)

lemma correct_watching_init_add_clause:
  assumes
    corr: \<open>correct_watching_init ((a, aa, None, ac, ad, Q, b), baa)\<close> and
    leC: \<open>2 \<le> length C\<close> and
    [simp]: \<open>i \<notin># dom_m aa\<close> and
    dist[iff]: \<open>C ! 0 \<noteq> C ! Suc 0\<close>
  shows \<open>correct_watching_init
          ((a, fmupd i (C, red) aa, None, ac, ad, Q, b
            (C ! 0 := b (C ! 0) @ [(i, C ! Suc 0, length C = 2)],
             C ! Suc 0 := b (C ! Suc 0) @ [(i, C ! 0, length C = 2)])),
           baa)\<close>
proof -
  have [iff]: \<open>C ! Suc 0 \<noteq> C ! 0\<close>
    using  \<open>C ! 0 \<noteq> C ! Suc 0\<close> by argo
  have [iff]: \<open>C ! Suc 0 \<in># all_lits_of_m (mset C)\<close> \<open>C ! 0 \<in># all_lits_of_m (mset C)\<close>
    \<open> C ! Suc 0 \<in> set C\<close> \<open> C ! 0 \<in> set C\<close> \<open>C ! 0 \<in> set (watched_l C)\<close> \<open>C ! Suc 0 \<in> set (watched_l C)\<close>
    using leC by (force intro!: in_clause_in_all_lits_of_m nth_mem simp: in_set_conv_iff
        intro: exI[of _ 0] exI[of _ \<open>Suc 0\<close>])+
  have [dest!]: \<open>\<And>L. L \<noteq> C ! 0 \<Longrightarrow> L \<noteq> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l C) \<Longrightarrow> False\<close>
     by (cases C; cases \<open>tl C\<close>; auto)+
  show ?thesis
    using corr
    by (force simp: correct_watching_init.simps all_blits_are_in_problem_init.simps ran_m_mapsto_upd_notin
        all_lits_of_mm_add_mset all_lits_of_mm_union clause_to_update_mapsto_upd_notin is_binary.simps
        split: if_splits)
qed

lemma init_dt_step_wl_init_dt_step:
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and corr: \<open>correct_watching_init S\<close> and
    dist: \<open>distinct C\<close>
  shows \<open>init_dt_step_wl C S \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l_init \<and> correct_watching_init S}
          (init_dt_step C S')\<close>
   (is \<open>_ \<le> \<Down> ?A _\<close>)
proof -
  have confl: \<open>(get_conflict_init_wl S, get_conflict_l_init S') \<in> \<langle>Id\<rangle>option_rel\<close>
    using S_S' by (auto simp: twl_st_wl_init)
  have false: \<open>(add_empty_conflict_init_wl S, add_empty_conflict_init_l S') \<in> ?A\<close>
    using S_S' corr
    apply (cases S; cases S')
    apply (auto simp: add_empty_conflict_init_wl_def add_empty_conflict_init_l_def
        correct_watching_init.simps all_blits_are_in_problem_init.simps
        state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def)
    done
  have propa_unit:
    \<open>(propagate_unit_init_wl (hd C) S, propagate_unit_init_l (hd C) S') \<in> ?A\<close>
    using S_S' corr apply (cases S; cases S')
    apply (auto simp: propagate_unit_init_l_def propagate_unit_init_wl_def correct_watching_init_propagate
        state_wl_l_init_def state_wl_l_def clause_to_update_def correct_watching_init_add_unit
        all_lits_of_mm_add_mset all_lits_of_m_add_mset all_lits_of_mm_union)
    done
  have already_propa:
    \<open>(already_propagated_unit_init_wl (mset C) S, already_propagated_unit_init_l (mset C) S') \<in> ?A\<close>
    using S_S' corr
    by (cases S; cases S')
       (auto simp: already_propagated_unit_init_wl_def already_propagated_unit_init_l_def
        state_wl_l_init_def state_wl_l_def clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset correct_watching_init_add_unit)
  have set_conflict: \<open>(set_conflict_init_wl (hd C) S, set_conflict_init_l C S') \<in> ?A\<close>
    if \<open>C = [hd C]\<close>
    using S_S' corr that
    by (cases S; cases S')
       (auto simp: set_conflict_init_wl_def set_conflict_init_l_def
        state_wl_l_init_def state_wl_l_def clause_to_update_def correct_watching_init_propagate
        all_lits_of_mm_add_mset all_lits_of_m_add_mset
        intro!: correct_watching_init_add_unit)
  have add_to_clauses_init_wl: \<open>add_to_clauses_init_wl C S
          \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l_init \<and> correct_watching_init S}
               (add_to_clauses_init_l C S')\<close>
    if C: \<open>length C \<ge> 2\<close> and conf: \<open>get_conflict_l_init S' = None\<close>
  proof -
    have [iff]: \<open>C ! Suc 0 \<notin> set (watched_l C) \<longleftrightarrow> False\<close>
      \<open>C ! 0 \<notin> set (watched_l C) \<longleftrightarrow> False\<close> and
      [dest!]: \<open>\<And>L. L \<noteq> C ! 0 \<Longrightarrow> L \<noteq> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l C) \<Longrightarrow> False\<close>
      using C by (cases C; cases \<open>tl C\<close>; auto)+
    have [dest!]: \<open>C ! 0 = C ! Suc 0 \<Longrightarrow> False\<close>
      using C dist by (cases C; cases \<open>tl C\<close>; auto)+
    show ?thesis
      using S_S' corr conf C
      by (cases S; cases S')
        (auto 5 5 simp: add_to_clauses_init_wl_def add_to_clauses_init_l_def get_fresh_index_def
          state_wl_l_init_def state_wl_l_def clause_to_update_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset
          RES_RETURN_RES Let_def
          intro!: RES_refine filter_mset_cong2 correct_watching_init_add_clause)
  qed
  have add_to_other_init:
    \<open>(add_to_other_init C S, add_to_other_init C S') \<in> ?A\<close>
    using S_S' corr
    by (cases S; cases S')
       (auto simp: state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset correct_watching_init.simps)
  show ?thesis
    unfolding init_dt_step_wl_def init_dt_step_def
    apply (refine_vcg confl false propa_unit already_propa set_conflict
        add_to_clauses_init_wl add_to_other_init)
    subgoal by simp
    subgoal by simp
    subgoal using S_S' by (simp add: twl_st_wl_init)
    subgoal using S_S' by (simp add: twl_st_wl_init)
    subgoal using S_S' by (cases C) simp_all
    subgoal by linarith
    done
qed

lemma init_dt_wl_init_dt:
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and corr: \<open>correct_watching_init S\<close> and
    dist: \<open>\<forall>C\<in>set C. distinct C\<close>
  shows \<open>init_dt_wl C S \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l_init \<and> correct_watching_init S}
          (init_dt C S')\<close>
proof -
  have C: \<open>(C, C) \<in>  \<langle>{(C, C'). (C, C') \<in> Id \<and> distinct C}\<rangle>list_rel\<close>
    using dist
    by (auto simp: list_rel_def list.rel_refl_strong)
  show ?thesis
    unfolding init_dt_wl_def init_dt_def
    apply (refine_vcg C S_S')
    subgoal using S_S' corr by fast
    subgoal by simp
    subgoal by (auto intro!: init_dt_step_wl_init_dt_step)
    done
qed

definition init_dt_wl_pre where
  \<open>init_dt_wl_pre C S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l_init \<and> correct_watching_init S \<and>
      init_dt_pre C S')\<close>


definition init_dt_wl_spec where
  \<open>init_dt_wl_spec C S T \<longleftrightarrow>
    (\<exists>S' T'. (S, S') \<in> state_wl_l_init \<and> correct_watching_init S \<and> (T, T') \<in> state_wl_l_init \<and>
      correct_watching_init T \<and> init_dt_spec C S' T')\<close>

lemma init_dt_wl_init_dt_wl_spec:
  assumes \<open>init_dt_wl_pre CS S\<close>
  shows \<open>init_dt_wl CS S \<le> SPEC (init_dt_wl_spec CS S)\<close>
proof -
  obtain S' where
     SS': \<open>(S, S') \<in> state_wl_l_init\<close> and
     corr: \<open>correct_watching_init S\<close> and
     pre: \<open>init_dt_pre CS S'\<close>
    using assms unfolding init_dt_wl_pre_def by blast
  have dist: \<open>\<forall>C\<in>set CS. distinct C\<close>
    using pre unfolding init_dt_pre_def by blast
  show ?thesis
    apply (rule order.trans)
     apply (rule init_dt_wl_init_dt[OF SS' corr dist])
    apply (rule order.trans)
     apply (rule ref_two_step')
     apply (rule init_dt_full[OF pre])
    apply (unfold conc_fun_SPEC)
    apply (rule SPEC_rule)
    apply normalize_goal+
    using SS' corr pre unfolding init_dt_wl_spec_def
    by blast
qed

definition rewatch
  :: \<open>'v clauses_l \<Rightarrow> ('v literal \<Rightarrow> 'v watched) \<Rightarrow> ('v literal \<Rightarrow> 'v watched) nres\<close>
where
\<open>rewatch N W = do {
  xs \<leftarrow> SPEC(\<lambda>xs. set_mset (dom_m N) \<subseteq> set xs \<and> distinct xs);
  nfoldli
    xs
    (\<lambda>_. True)
    (\<lambda>i W. do {
      if i \<in># dom_m N
      then do {
        let L1 = N \<propto> i ! 0;
        let L2 = N \<propto> i ! 1;
        let b = (length (N \<propto> i) = 2);
        let W = W(L1 := W L1 @ [(i, L2, b)]);
        let W = W(L2 := W L2 @ [(i, L1, b)]);
        RETURN W
      }
      else RETURN W
    })
    W
  }\<close>

lemma rewatch_correctness:
  assumes [simp]: \<open>W = (\<lambda>_. [])\<close> and
    H[dest]: \<open>\<And>x. x \<in># dom_m N \<Longrightarrow> distinct (N \<propto> x) \<and> length (N \<propto> x) \<ge> 2\<close>
  shows
    \<open>rewatch N W \<le> SPEC(\<lambda>W. correct_watching_init ((M, N, C, NE, UE, Q, W), OC))\<close>
proof -
  define I where
    \<open>I \<equiv> \<lambda>(a :: nat list) (b :: nat list) W.
        correct_watching_init ((M, fmrestrict_set (set a) N, C, NE, UE, Q, W), OC)\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x \<Longrightarrow> I [] x W\<close> for x
    unfolding I_def by (auto simp: correct_watching_init.simps
       all_blits_are_in_problem_init.simps clause_to_update_def)

  show ?thesis
    unfolding rewatch_def
    apply (refine_vcg
      nfoldli_rule[where I = \<open>I\<close>])
    subgoal by (rule I0)
    subgoal for x xa l1 l2 \<sigma>
      unfolding I_def
      apply (cases \<open>the (fmlookup N xa)\<close>)
      apply auto
      defer
       apply (rule correct_watching_init_add_clause)
          apply (auto simp: dom_m_fmrestrict_set')
      apply (auto dest!: H simp: nth_eq_iff_index_eq)
      apply (subst (asm) nth_eq_iff_index_eq)
      apply simp
      apply simp
       apply auto[]
      by fast
    subgoal
      unfolding I_def
      by auto
    subgoal by auto
    subgoal unfolding I_def
      by (auto simp: fmlookup_restrict_set_id')
    done
qed

end
