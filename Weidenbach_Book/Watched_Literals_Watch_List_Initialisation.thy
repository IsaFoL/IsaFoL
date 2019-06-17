theory Watched_Literals_Watch_List_Initialisation
  imports Watched_Literals_Watch_List Watched_Literals_Initialisation
begin


subsection \<open>Initialisation\<close>


type_synonym 'v twl_st_wl_init' = \<open>(('v, nat) ann_lits \<times> 'v clauses_l \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl)\<close>

type_synonym 'v twl_st_wl_init = \<open>'v twl_st_wl_init' \<times> 'v clauses\<close>
type_synonym 'v twl_st_wl_init_full = \<open>'v twl_st_wl \<times> 'v clauses\<close>

fun get_trail_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> ('v, nat) ann_lit list\<close> where
  \<open>get_trail_init_wl ((M, _, _, _, _, _), _) = M\<close>

fun get_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses_l\<close> where
  \<open>get_clauses_init_wl ((_, N, _, _, _, _), OC) = N\<close>

fun get_conflict_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v cconflict\<close> where
  \<open>get_conflict_init_wl ((_, _, D, _, _, _), _) = D\<close>

fun literals_to_update_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clause\<close> where
  \<open>literals_to_update_init_wl ((_, _, _, _, _, Q), _) = Q\<close>

fun other_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses\<close> where
  \<open>other_clauses_init_wl ((_, _, _, _, _, _), OC) = OC\<close>

fun add_empty_conflict_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  add_empty_conflict_init_wl_def[simp del]:
   \<open>add_empty_conflict_init_wl ((M, N, D, NE, UE, Q), OC) =
       ((M, N, Some {#}, NE, UE, {#}), add_mset {#} OC)\<close>

fun propagate_unit_init_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  propagate_unit_init_wl_def[simp del]:
   \<open>propagate_unit_init_wl L ((M, N, D, NE, UE, Q), OC) =
       ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, add_mset (-L) Q), OC)\<close>


fun already_propagated_unit_init_wl :: \<open>'v clause \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  already_propagated_unit_init_wl_def[simp del]:
   \<open>already_propagated_unit_init_wl C ((M, N, D, NE, UE, Q), OC) =
       ((M, N, D, add_mset C NE, UE, Q), OC)\<close>


fun set_conflict_init_wl :: \<open>'v literal \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  set_conflict_init_wl_def[simp del]:
   \<open>set_conflict_init_wl L ((M, N, _, NE, UE, Q), OC) =
       ((M, N, Some {#L#}, add_mset {#L#} NE, UE, {#}), OC)\<close>


fun add_to_clauses_init_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  add_to_clauses_init_wl_def[simp del]:
   \<open>add_to_clauses_init_wl C ((M, N, D, NE, UE, Q), OC) = do {
        i \<leftarrow> get_fresh_index N;
        let b = (length C = 2);
        RETURN ((M, fmupd i (C, True) N, D, NE, UE, Q), OC)
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

fun st_l_of_wl_init :: \<open>'v twl_st_wl_init' \<Rightarrow> 'v twl_st_l\<close> where
  \<open>st_l_of_wl_init (M, N, D, NE, UE, Q) = (M, N, D, NE, UE, {#}, Q)\<close>

definition state_wl_l_init' where
  \<open>state_wl_l_init' = {(S ,S'). S' = st_l_of_wl_init S}\<close>

definition init_dt_wl :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  \<open>init_dt_wl CS = nfoldli CS (\<lambda>_. True) init_dt_step_wl\<close>

definition state_wl_l_init :: \<open>('v twl_st_wl_init \<times> 'v twl_st_l_init) set\<close> where
  \<open>state_wl_l_init = {(S, S'). (fst S, fst S') \<in> state_wl_l_init' \<and>
      other_clauses_init_wl S = other_clauses_l_init S'}\<close>


fun all_blits_are_in_problem_init where
  [simp del]: \<open>all_blits_are_in_problem_init (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
      (\<forall>L. (\<forall>(i, K, b)\<in>#mset (W L). K \<in># all_lits_of_mm (mset `# ran_mf N + (NE + UE))))\<close>

text \<open>We assume that no clause has been deleted during initialisation. The definition is
  slightly redundant since \<^term>\<open>i \<in># dom_m N\<close> is already entailed by
  \<^term>\<open>fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#})\<close>.\<close>

named_theorems twl_st_wl_init

lemma [twl_st_wl_init]:
  assumes \<open>(S, S') \<in> state_wl_l_init\<close>
  shows
    \<open>get_conflict_l_init S' = get_conflict_init_wl S\<close>
    \<open>get_trail_l_init S' = get_trail_init_wl S\<close>
    \<open>other_clauses_l_init S' = other_clauses_init_wl S\<close>
    \<open>count_decided (get_trail_l_init S') = count_decided (get_trail_init_wl S)\<close>
  using assms
  by (solves \<open>cases S; cases S'; auto simp: state_wl_l_init_def state_wl_l_def
      state_wl_l_init'_def\<close>)+
(*
lemma [twl_st_wl_init]:
  \<open>get_trail_wl (fst T) = get_trail_init_wl T\<close>
  \<open>get_conflict_wl (fst T) = get_conflict_init_wl T\<close>
  by (cases T; auto simp: correct_watching.simps correct_watching_init.simps; fail)+
 *)
lemma in_clause_to_update_in_dom_mD:
  \<open>bb \<in># clause_to_update L (a, aa, ab, ac, ad, {#}, {#}) \<Longrightarrow> bb \<in># dom_m aa\<close>
  unfolding clause_to_update_def
  by force

lemma init_dt_step_wl_init_dt_step:
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and
    dist: \<open>distinct C\<close>
  shows \<open>init_dt_step_wl C S \<le> \<Down> state_wl_l_init
          (init_dt_step C S')\<close>
   (is \<open>_ \<le> \<Down> ?A _\<close>)
proof -
  have confl: \<open>(get_conflict_init_wl S, get_conflict_l_init S') \<in> \<langle>Id\<rangle>option_rel\<close>
    using S_S' by (auto simp: twl_st_wl_init)
  have false: \<open>(add_empty_conflict_init_wl S, add_empty_conflict_init_l S') \<in> ?A\<close>
    using S_S'
    apply (cases S; cases S')
    apply (auto simp: add_empty_conflict_init_wl_def add_empty_conflict_init_l_def
         all_blits_are_in_problem_init.simps state_wl_l_init'_def
        state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def)
    done
  have propa_unit:
    \<open>(propagate_unit_init_wl (hd C) S, propagate_unit_init_l (hd C) S') \<in> ?A\<close>
    using S_S' apply (cases S; cases S')
    apply (auto simp: propagate_unit_init_l_def propagate_unit_init_wl_def  state_wl_l_init'_def
        state_wl_l_init_def state_wl_l_def clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset all_lits_of_mm_union)
    done
  have already_propa:
    \<open>(already_propagated_unit_init_wl (mset C) S, already_propagated_unit_init_l (mset C) S') \<in> ?A\<close>
    using S_S'
    by (cases S; cases S')
       (auto simp: already_propagated_unit_init_wl_def already_propagated_unit_init_l_def
        state_wl_l_init_def state_wl_l_def clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset  state_wl_l_init'_def)
  have set_conflict: \<open>(set_conflict_init_wl (hd C) S, set_conflict_init_l C S') \<in> ?A\<close>
    if \<open>C = [hd C]\<close>
    using S_S' that
    by (cases S; cases S')
       (auto simp: set_conflict_init_wl_def set_conflict_init_l_def
        state_wl_l_init_def state_wl_l_def clause_to_update_def  state_wl_l_init'_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset)
  have add_to_clauses_init_wl: \<open>add_to_clauses_init_wl C S
          \<le> \<Down> state_wl_l_init
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
      using S_S' conf C
      by (cases S; cases S')
        (auto 5 5 simp: add_to_clauses_init_wl_def add_to_clauses_init_l_def get_fresh_index_def
          state_wl_l_init_def state_wl_l_def clause_to_update_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset  state_wl_l_init'_def
          RES_RETURN_RES Let_def
          intro!: RES_refine filter_mset_cong2)
  qed
  have add_to_other_init:
    \<open>(add_to_other_init C S, add_to_other_init C S') \<in> ?A\<close>
    using S_S'
    by (cases S; cases S')
       (auto simp: state_wl_l_init_def state_wl_l_def clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset  state_wl_l_init'_def)
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
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and
    dist: \<open>\<forall>C\<in>set C. distinct C\<close>
  shows \<open>init_dt_wl C S \<le> \<Down> state_wl_l_init
          (init_dt C S')\<close>
proof -
  have C: \<open>(C, C) \<in>  \<langle>{(C, C'). (C, C') \<in> Id \<and> distinct C}\<rangle>list_rel\<close>
    using dist
    by (auto simp: list_rel_def list.rel_refl_strong)
  show ?thesis
    unfolding init_dt_wl_def init_dt_def
    apply (refine_vcg C S_S')
    subgoal using S_S' by fast
    subgoal by (auto intro!: init_dt_step_wl_init_dt_step)
    done
qed

definition init_dt_wl_pre where
  \<open>init_dt_wl_pre C S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> state_wl_l_init \<and>
      init_dt_pre C S')\<close>


definition init_dt_wl_spec where
  \<open>init_dt_wl_spec C S T \<longleftrightarrow>
    (\<exists>S' T'. (S, S') \<in> state_wl_l_init \<and> (T, T') \<in> state_wl_l_init \<and>
      init_dt_spec C S' T')\<close>

lemma init_dt_wl_init_dt_wl_spec:
  assumes \<open>init_dt_wl_pre CS S\<close>
  shows \<open>init_dt_wl CS S \<le> SPEC (init_dt_wl_spec CS S)\<close>
proof -
  obtain S' where
     SS': \<open>(S, S') \<in> state_wl_l_init\<close> and
     pre: \<open>init_dt_pre CS S'\<close>
    using assms unfolding init_dt_wl_pre_def by blast
  have dist: \<open>\<forall>C\<in>set CS. distinct C\<close>
    using pre unfolding init_dt_pre_def by blast
  show ?thesis
    apply (rule order.trans)
     apply (rule init_dt_wl_init_dt[OF SS' dist])
    apply (rule order.trans)
     apply (rule ref_two_step')
     apply (rule init_dt_full[OF pre])
    apply (unfold conc_fun_SPEC)
    apply (rule SPEC_rule)
    apply normalize_goal+
    using SS' pre unfolding init_dt_wl_spec_def
    by blast
qed


fun correct_watching_init :: \<open>'v twl_st_wl \<Rightarrow> bool\<close> where
  [simp del]: \<open>correct_watching_init (M, N, D, NE, UE, Q, W) \<longleftrightarrow>
    all_blits_are_in_problem_init (M, N, D, NE, UE, Q, W) \<and>
    (\<forall>L.
        distinct_watched (W L) \<and>
        (\<forall>(i, K, b)\<in>#mset (W L). i \<in># dom_m N \<and> K \<in> set (N \<propto> i) \<and> K \<noteq> L \<and>
           correctly_marked_as_binary N (i, K, b)) \<and>
        fst `# mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#}))\<close>

lemma correct_watching_init_correct_watching:
  \<open>correct_watching_init T \<Longrightarrow> correct_watching T\<close>
  by (cases T)
    (fastforce simp: correct_watching.simps correct_watching_init.simps filter_mset_eq_conv
      all_blits_are_in_problem_init.simps
      in_clause_to_update_in_dom_mD)

lemma image_mset_Suc: \<open>Suc `# {#C \<in># M. P C#} = {#C \<in># Suc `# M. P (C-1)#}\<close>
  by (induction M) auto

lemma correct_watching_init_add_unit:
  assumes \<open>correct_watching_init (M, N, D, NE, UE, Q, W)\<close>
  shows \<open>correct_watching_init (M, N, D, add_mset C NE, UE, Q, W)\<close>
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
  \<open>correct_watching_init ((L # M, N, D, NE, UE, Q, W)) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W))\<close>
  \<open>correct_watching_init ((M, N, D, NE, UE, add_mset C Q, W)) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W))\<close>
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
  \<open>NO_MATCH None y \<Longrightarrow> correct_watching_init ((a, aa, y, ac, ad, ae, b)) \<longleftrightarrow>
     correct_watching_init ((a, aa, None, ac, ad, ae, b))\<close>
  \<open>NO_MATCH {#} ae \<Longrightarrow> correct_watching_init ((a, aa, y, ac, ad, ae, b)) \<longleftrightarrow>
     correct_watching_init ((a, aa, y, ac, ad, {#}, b))\<close>
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
    corr: \<open>correct_watching_init ((a, aa, None, ac, ad, Q, b))\<close> and
    leC: \<open>2 \<le> length C\<close> and
    i_notin[simp]: \<open>i \<notin># dom_m aa\<close> and
    dist[iff]: \<open>C ! 0 \<noteq> C ! Suc 0\<close>
  shows \<open>correct_watching_init
          ((a, fmupd i (C, red) aa, None, ac, ad, Q, b
            (C ! 0 := b (C ! 0) @ [(i, C ! Suc 0, length C = 2)],
             C ! Suc 0 := b (C ! Suc 0) @ [(i, C ! 0, length C = 2)])))\<close>
proof -
  have [iff]: \<open>C ! Suc 0 \<noteq> C ! 0\<close>
    using  \<open>C ! 0 \<noteq> C ! Suc 0\<close> by argo
  have [iff]: \<open>C ! Suc 0 \<in># all_lits_of_m (mset C)\<close> \<open>C ! 0 \<in># all_lits_of_m (mset C)\<close>
    \<open>C ! Suc 0 \<in> set C\<close> \<open> C ! 0 \<in> set C\<close> \<open>C ! 0 \<in> set (watched_l C)\<close> \<open>C ! Suc 0 \<in> set (watched_l C)\<close>
    using leC by (force intro!: in_clause_in_all_lits_of_m nth_mem simp: in_set_conv_iff
        intro: exI[of _ 0] exI[of _ \<open>Suc 0\<close>])+
  have [dest!]: \<open>\<And>L. L \<noteq> C ! 0 \<Longrightarrow> L \<noteq> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l C) \<Longrightarrow> False\<close>
     by (cases C; cases \<open>tl C\<close>; auto)+
  have i: \<open>i \<notin> fst ` set (b L)\<close> for L
    using corr i_notin  unfolding correct_watching_init.simps
    by force
  have [iff]: \<open>(i,c, d) \<notin> set (b L)\<close> for L c d
    using i[of L] by (auto simp: image_iff)
  then show ?thesis
    using corr
    by (force simp: correct_watching_init.simps all_blits_are_in_problem_init.simps ran_m_mapsto_upd_notin
        all_lits_of_mm_add_mset all_lits_of_mm_union clause_to_update_mapsto_upd_notin correctly_marked_as_binary.simps
        split: if_splits)
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
        ASSERT(i \<in># dom_m N);
        ASSERT(length (N \<propto> i) \<ge> 2);
        let L1 = N \<propto> i ! 0;
        let L2 = N \<propto> i ! 1;
        let b = (length (N \<propto> i) = 2);
        ASSERT(L1 \<noteq> L2);
        ASSERT(length (W L1) < size (dom_m N));
        let W = W(L1 := W L1 @ [(i, L2, b)]);
        ASSERT(length (W L2) < size (dom_m N));
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
    \<open>rewatch N W \<le> SPEC(\<lambda>W. correct_watching_init (M, N, C, NE, UE, Q, W))\<close>
proof -
  define I where
    \<open>I \<equiv> \<lambda>(a :: nat list) (b :: nat list) W.
        correct_watching_init ((M, fmrestrict_set (set a) N, C, NE, UE, Q, W))\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x \<Longrightarrow> I [] x W\<close> for x
    unfolding I_def by (auto simp: correct_watching_init.simps
       all_blits_are_in_problem_init.simps clause_to_update_def)
  have le: \<open>length (\<sigma> L) < size (dom_m N)\<close>
     if \<open>correct_watching_init (M, fmrestrict_set (set l1) N, C, NE, UE, Q, \<sigma>)\<close> and
      \<open>set_mset (dom_m N) \<subseteq> set x \<and> distinct x\<close> and
     \<open>x = l1 @ xa # l2\<close> \<open>xa \<in># dom_m N\<close>
     for L l1 \<sigma> xa l2 x
  proof -
    have 1: \<open>card (set l1) \<le> length l1\<close>
      by (auto simp: card_length)
    have \<open>distinct_watched (\<sigma> L)\<close> and \<open>fst ` set (\<sigma> L) \<subseteq> set l1 \<inter> set_mset (dom_m N)\<close>
      using that by (fastforce simp: correct_watching_init.simps dom_m_fmrestrict_set')+
    then have \<open>length (map fst (\<sigma> L)) \<le> card (set l1 \<inter> set_mset (dom_m N))\<close>
      using 1 by (subst distinct_card[symmetric])
       (auto simp: distinct_watched_alt_def intro!: card_mono intro: order_trans)
    also have \<open>... < card (set_mset (dom_m N))\<close>
      using that by (auto intro!: psubset_card_mono)
    also have \<open>... = size (dom_m N)\<close>
      by (simp add: distinct_mset_dom distinct_mset_size_eq_card)
    finally show ?thesis by simp
  qed
  show ?thesis
    unfolding rewatch_def
    apply (refine_vcg
      nfoldli_rule[where I = \<open>I\<close>])
    subgoal by (rule I0)
    subgoal using assms unfolding I_def by auto
    subgoal for x xa l1 l2 \<sigma>  using H[of xa] unfolding I_def apply -
      by (rule, subst (asm)nth_eq_iff_index_eq)
        linarith+
    subgoal for x xa l1 l2 \<sigma> unfolding I_def by (rule le)
    subgoal for x xa l1 l2 \<sigma> unfolding I_def by (drule le[where L = \<open>N \<propto> xa ! 1\<close>]) (auto simp: I_def dest!: le)
    subgoal for x xa l1 l2 \<sigma>
      unfolding I_def
      by (cases \<open>the (fmlookup N xa)\<close>)
        (auto simp: dom_m_fmrestrict_set' intro!: correct_watching_init_add_clause)
    subgoal
      unfolding I_def by auto
    subgoal by auto
    subgoal unfolding I_def
      by (auto simp: fmlookup_restrict_set_id')
    done
qed

definition state_wl_l_init_full :: \<open>('v twl_st_wl_init_full \<times> 'v twl_st_l_init) set\<close> where
  \<open>state_wl_l_init_full = {(S, S'). (fst S, fst S') \<in> state_wl_l None \<and>
      snd S = snd S'}\<close>

definition added_only_watched  :: \<open>('v twl_st_wl_init_full \<times> 'v twl_st_wl_init) set\<close> where
  \<open>added_only_watched = {(((M, N, D, NE, UE, Q, W), OC), ((M', N', D', NE', UE', Q'), OC')).
        (M, N, D, NE, UE, Q) = (M', N', D', NE', UE', Q') \<and> OC = OC'}\<close>

definition init_dt_wl_spec_full
  :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init_full \<Rightarrow> bool\<close>
where
  \<open>init_dt_wl_spec_full C S T'' \<longleftrightarrow>
    (\<exists>S' T T'. (S, S') \<in> state_wl_l_init \<and> (T :: 'v twl_st_wl_init, T') \<in> state_wl_l_init \<and>
      init_dt_spec C S' T' \<and> correct_watching_init (fst T'') \<and> (T'', T) \<in> added_only_watched)\<close>

definition init_dt_wl_full :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init_full nres\<close> where
  \<open>init_dt_wl_full CS S = do{
     ((M, N, D, NE, UE, Q), OC) \<leftarrow> init_dt_wl CS S;
     W \<leftarrow> rewatch N (\<lambda>_. []);
     RETURN ((M, N, D, NE, UE, Q, W), OC)
  }\<close>

lemma init_dt_wl_spec_rewatch_pre:
  assumes \<open>init_dt_wl_spec CS S T\<close> and \<open>N = get_clauses_init_wl T\<close> and \<open>C \<in># dom_m N\<close>
  shows \<open>distinct (N \<propto> C) \<and> length (N \<propto> C) \<ge> 2\<close>
proof -
  obtain x xa xb where
    \<open>N = get_clauses_init_wl T\<close> and
    Sx: \<open>(S, x) \<in> state_wl_l_init\<close> and
    Txa: \<open>(T, xa) \<in> state_wl_l_init\<close> and
    xa_xb: \<open>(xa, xb) \<in> twl_st_l_init\<close> and
    struct_invs: \<open>twl_struct_invs_init xb\<close> and
    \<open>clauses_to_update_l_init xa = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l_init xa). \<not> is_decided s\<close> and
    \<open>get_conflict_l_init xa = None \<longrightarrow>
     literals_to_update_l_init xa = uminus `# lit_of `# mset (get_trail_l_init xa)\<close> and
    \<open>mset `# mset CS + mset `# ran_mf (get_clauses_l_init x) + other_clauses_l_init x +
     get_unit_clauses_l_init x =
     mset `# ran_mf (get_clauses_l_init xa) + other_clauses_l_init xa +
     get_unit_clauses_l_init xa\<close> and
    \<open>learned_clss_lf (get_clauses_l_init x) =
     learned_clss_lf (get_clauses_l_init xa)\<close> and
    \<open>get_learned_unit_clauses_l_init xa = get_learned_unit_clauses_l_init x\<close> and
    \<open>twl_list_invs (fst xa)\<close> and
    \<open>twl_stgy_invs (fst xb)\<close> and
    \<open>other_clauses_l_init xa \<noteq> {#} \<longrightarrow> get_conflict_l_init xa \<noteq> None\<close> and
    \<open>{#} \<in># mset `# mset CS \<longrightarrow> get_conflict_l_init xa \<noteq> None\<close> and
    \<open>get_conflict_l_init x \<noteq> None \<longrightarrow> get_conflict_l_init x = get_conflict_l_init xa\<close>
    using assms
    unfolding init_dt_wl_spec_def init_dt_spec_def apply -
    by normalize_goal+ presburger

  have \<open>twl_st_inv (fst xb)\<close>
    using struct_invs unfolding twl_struct_invs_init_def by fast
  then have \<open>Multiset.Ball (get_clauses (fst xb)) struct_wf_twl_cls\<close>
    by (cases xb) (auto simp: twl_st_inv.simps)
  with \<open>C \<in># dom_m N\<close> show ?thesis
    using Txa xa_xb assms by (cases T; cases \<open>fmlookup N C\<close>; cases \<open>snd (the(fmlookup N C))\<close>)
         (auto simp: state_wl_l_init_def twl_st_l_init_def conj_disj_distribR Collect_disj_eq
        Collect_conv_if mset_take_mset_drop_mset'
        state_wl_l_init'_def ran_m_def dest!: multi_member_split)
qed

lemma init_dt_wl_full_init_dt_wl_spec_full:
  assumes \<open>init_dt_wl_pre CS S\<close>
  shows \<open>init_dt_wl_full CS S \<le> SPEC (init_dt_wl_spec_full CS S)\<close>
proof -
  show ?thesis
    unfolding init_dt_wl_full_def
    apply (rule specify_left)
    apply (rule init_dt_wl_init_dt_wl_spec)
    subgoal by (rule assms)
    apply clarify
    apply (rule specify_left)
    apply (rule_tac M =a and N=aa and C=ab and NE=ac and UE=ad and Q=b in
        rewatch_correctness[OF _ init_dt_wl_spec_rewatch_pre])
    subgoal by rule
       apply assumption
    subgoal by simp
    subgoal by simp
    subgoal for a aa ab ac ad b ba W
      using assms
      unfolding init_dt_wl_spec_full_def init_dt_wl_pre_def init_dt_wl_spec_def
      by (auto simp: added_only_watched_def state_wl_l_init_def state_wl_l_init'_def)
    done
qed

end
