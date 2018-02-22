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


fun set_conflict_init_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init\<close> where
  set_conflict_init_wl_def[simp del]:
   \<open>set_conflict_init_wl C ((M, N, _, NE, UE, Q, W), OC) =
       ((M, N, Some (mset C), add_mset (mset C) NE, UE, {#}, W), OC)\<close>


fun add_to_clauses_init_wl :: \<open>'v clause_l \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  add_to_clauses_init_wl_def[simp del]:
   \<open>add_to_clauses_init_wl C ((M, N, _, NE, UE, Q, W), OC) = do {
        i \<leftarrow> get_fresh_index N;
        let W = W((C!0) := W (C!0) @ [i], (C!1) := W (C!1) @ [i]);
        RETURN ((M, fmupd i (C, True) N, None, NE, UE, Q, W), OC)
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
      else RETURN (set_conflict_init_wl C S)
    else
        add_to_clauses_init_wl C S
  | Some D \<Rightarrow>
      RETURN (add_to_other_init C S))\<close>

definition init_dt_wl :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init nres\<close> where
  \<open>init_dt_wl CS = nfoldli CS (\<lambda>_. True) init_dt_step_wl\<close>

definition state_wl_l_init :: \<open>('v twl_st_wl_init \<times> 'v twl_st_l_init) set\<close> where
  \<open>state_wl_l_init = {(S, S'). (fst S, fst S') \<in> state_wl_l None \<and>
      other_clauses_init_wl S = other_clauses_l_init S'}\<close>

fun correct_watching_init :: \<open>'v twl_st_wl_init \<Rightarrow> bool\<close> where
  [simp del]: \<open>correct_watching_init ((M, N, D, NE, UE, Q, W), _) \<longleftrightarrow>
    ((\<forall>L. mset (W L) = clause_to_update L (M, N, D, NE, UE, {#}, {#})))\<close>

named_theorems twl_st_wl_init

lemma [twl_st_wl_init]:
  assumes \<open>(S, S') \<in> state_wl_l_init\<close>
  shows
    \<open>get_conflict_l_init S' = get_conflict_init_wl S\<close>
    \<open>get_trail_l_init S' = get_trail_init_wl S\<close>
  using assms
  by (cases S; cases S'; auto simp: state_wl_l_init_def state_wl_l_def)+


lemma image_mset_Suc: \<open>Suc `# {#C \<in># M. P C#} = {#C \<in># Suc `# M. P (C-1)#}\<close>
  by (induction M) auto

lemma correct_watching_init_add_unit:
  \<open>correct_watching_init ((M, N, D, add_mset C NE, UE, Q, W), OC) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  unfolding correct_watching_init.simps clause_to_update_def Ball_def
  by (auto simp: correct_watching.simps all_lits_of_mm_add_mset
      all_lits_of_m_add_mset Ball_def all_conj_distrib clause_to_update_def)

lemma correct_watching_init_propagate:
  \<open>correct_watching_init ((L # M, N, D, NE, UE, Q, W), OC) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  \<open>correct_watching_init ((M, N, D, NE, UE, add_mset C Q, W), OC) \<longleftrightarrow>
         correct_watching_init ((M, N, D, NE, UE, Q, W), OC)\<close>
  unfolding correct_watching_init.simps clause_to_update_def Ball_def
  by (auto simp: correct_watching.simps all_lits_of_mm_add_mset
      all_lits_of_m_add_mset Ball_def all_conj_distrib clause_to_update_def)


lemma init_dt_step_wl_init_dt_step:
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and corr: \<open>correct_watching_init S\<close>
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
        correct_watching_init.simps
        state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def)
    done
  have propa_unit:
    \<open>(propagate_unit_init_wl (hd C) S, propagate_unit_init_l (hd C) S') \<in> ?A\<close>

    using S_S' corr apply (cases S; cases S')
    apply (auto simp: propagate_unit_init_l_def propagate_unit_init_wl_def
        state_wl_l_init_def state_wl_l_def correct_watching_init.simps clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset all_lits_of_mm_union)
    done
  have already_propa:
    \<open>(already_propagated_unit_init_wl (mset C) S, already_propagated_unit_init_l (mset C) S') \<in> ?A\<close>
    using S_S' corr
    by (cases S; cases S')
       (auto simp: already_propagated_unit_init_wl_def already_propagated_unit_init_l_def
        state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset correct_watching_init.simps)
  have set_conflict: \<open>(set_conflict_init_wl C S, set_conflict_init_l C S') \<in> ?A\<close>
    using S_S' corr
    by (cases S; cases S')
       (auto simp: set_conflict_init_wl_def set_conflict_init_l_def
        state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def
        all_lits_of_mm_add_mset all_lits_of_m_add_mset correct_watching_init.simps)
  have add_to_clauses_init_wl: \<open>add_to_clauses_init_wl C S
          \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l_init \<and> correct_watching_init S}
               (add_to_clauses_init_l C S')\<close>
    if C: \<open>length C \<ge> 2\<close>
  proof -
    have [iff]: \<open>C ! Suc 0 \<notin> set (watched_l C) \<longleftrightarrow> False\<close>
      \<open>C ! 0 \<notin> set (watched_l C) \<longleftrightarrow> False\<close> and
      [dest!]: \<open>\<And>L. L \<noteq> C ! 0 \<Longrightarrow> L \<noteq> C ! Suc 0 \<Longrightarrow> L \<in> set (watched_l C) \<Longrightarrow> False\<close>
      using C by (cases C; cases \<open>tl C\<close>; auto)+
    show ?thesis
      using S_S' corr
      by (cases S; cases S')
        (auto 5 5 simp: add_to_clauses_init_wl_def add_to_clauses_init_l_def get_fresh_index_def
          state_wl_l_init_def state_wl_l_def correct_watching.simps clause_to_update_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset correct_watching_init.simps
          RES_RETURN_RES
          intro!: RES_refine filter_mset_cong2)
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
    subgoal by linarith
    done
qed

lemma init_dt_wl_init_dt:
  assumes S_S': \<open>(S, S') \<in> state_wl_l_init\<close> and corr: \<open>correct_watching_init S\<close>
  shows \<open>init_dt_wl C S \<le> \<Down> {(S, S'). (S, S') \<in> state_wl_l_init \<and> correct_watching_init S}
          (init_dt C S')\<close>
proof -
  have C: \<open>(C, C) \<in> \<langle>Id\<rangle>list_rel\<close>
    by simp
  show ?thesis
    unfolding init_dt_wl_def init_dt_def
    apply (refine_vcg C S_S' )
    subgoal using S_S' corr by fast
    subgoal by simp
    subgoal by (auto intro!: init_dt_step_wl_init_dt_step)
    done
qed

(* TODO Kill?

subsection \<open>Final Theorem with Initialisation\<close>

fun init_wl_of :: \<open>'v twl_st_l\<Rightarrow> 'v twl_st_wl\<close> where
  \<open>init_wl_of (M, N, U, D, NE, UE, _, Q) =
       ((M, N, U, D, NE, UE, Q, calculate_correct_watching (tl N) (\<lambda>_. []) 1))\<close>


theorem init_dt_wl:
  fixes CS S
  defines S\<^sub>0: \<open>S\<^sub>0 \<equiv> (([], [[]], 0, None, {#}, {#}, {#}, {#}), {#})\<close>
  defines S: \<open>S \<equiv>  init_wl_of (fst (init_dt CS S\<^sub>0))\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    no_confl: \<open>get_conflict_wl S = None\<close> and
    snd_init: \<open>snd (init_dt CS S\<^sub>0) = {#}\<close>
  shows
    \<open>cdcl_twl_stgy_prog_wl S \<le> SPEC (\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
             (state\<^sub>W_of (twl_st_of_wl None S))
             (state\<^sub>W_of (twl_st_of_wl None T)))\<close>
proof -
  obtain M N U D NE UE WS Q OC where
    init: \<open>init_dt CS S\<^sub>0 = ((M, N, U, D, NE, UE, WS, Q), OC)\<close>
    by (cases \<open>init_dt CS S\<^sub>0\<close>) auto
  have \<open>N \<noteq> []\<close>
    using clauses_init_dt_not_Nil[of CS \<open>snd S\<^sub>0\<close>] init unfolding S\<^sub>0 by auto
  then have corr_w: \<open>correct_watching S\<close>
    unfolding S init
    by (auto simp: correct_watching.simps
        calculate_correct_watching[of _ _ _ M \<open>hd N\<close> U D NE UE])
  have
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)) = mset `# mset CS\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>twl_list_invs (st_l_of_wl None S)\<close>
    unfolding S S\<^sub>0
    subgoal
      using init_dt(1)[OF dist] snd_init
        by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 twl_struct_invs_init_twl_struct_invs)
    subgoal
      using init_dt(2)[OF dist] snd_init
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def)
    subgoal
      using init_dt(3)[OF dist] snd_init
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def)
    subgoal
      using init_dt(5)[OF dist]
      by (cases \<open>init_dt CS S\<^sub>0\<close>) (auto simp: S\<^sub>0 clauses_def twl_list_invs_def)
    don
  from cdcl_twl_stgy_prog_wl_spec_final2[OF this(1,3) no_confl this(4) corr_w]
  show ?thesis
    .
qed

*)
end
