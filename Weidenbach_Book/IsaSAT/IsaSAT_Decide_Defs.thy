theory IsaSAT_Decide_Defs
  imports IsaSAT_Setup IsaSAT_VMTF IsaSAT_Bump_Heuristics
begin


chapter \<open>Decide\<close>

definition isa_bump_find_next_undef where \<open>
  isa_bump_find_next_undef x M = (case x of Bump_Heuristics hstable focused foc tobmp \<Rightarrow>
  if foc then do {
    L \<leftarrow> isa_vmtf_find_next_undef focused M;
    RETURN (L, Bump_Heuristics hstable (update_next_search L focused) foc tobmp)
    } else  do {
    (L, hstable) \<leftarrow> isa_acids_find_next_undef hstable M;
    RETURN (L, Bump_Heuristics hstable focused foc tobmp)
  })\<close>

definition isa_vmtf_find_next_undef_upd
  :: \<open>trail_pol \<Rightarrow> bump_heuristics \<Rightarrow>
        ((trail_pol \<times> bump_heuristics) \<times> nat option)nres\<close>
where
  \<open>isa_vmtf_find_next_undef_upd = (\<lambda>M vm. do{
      (L, vm) \<leftarrow> isa_bump_find_next_undef vm M;
      RETURN ((M, vm), L)
  })\<close>

definition get_saved_phase_option_heur_pre :: \<open>nat option \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>get_saved_phase_option_heur_pre L = (\<lambda>heur.
       L \<noteq> None \<longrightarrow> get_next_phase_heur_pre_stats True (the L) heur)\<close>

definition lit_of_found_atm where
\<open>lit_of_found_atm \<phi> L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

definition find_unassigned_lit_wl_D_heur
  :: \<open>isasat \<Rightarrow> (isasat \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>S. do {
      let M = get_trail_wl_heur S;
      let vm = get_vmtf_heur S;
      let heur = get_heur S;
      let heur = set_fully_propagated_heur heur;
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd M vm;
      ASSERT(get_saved_phase_option_heur_pre (L) (get_content heur));
        L \<leftarrow> lit_of_found_atm heur L;
      let S = set_trail_wl_heur M S;
      let S = set_vmtf_wl_heur vm S;
      let S = set_heur_wl_heur heur S;
      RETURN (S, L)
    })\<close>

definition decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' S. do {
      let M = get_trail_wl_heur S;
      let stats = get_stats_heur S;
      ASSERT(isa_length_trail_pre M);
      let j = isa_length_trail M;
      let S = set_literals_to_update_wl_heur j S;
      ASSERT(cons_trail_Decided_tr_pre (L', M));
      let M = cons_trail_Decided_tr L' M;
      let S = set_trail_wl_heur M S;
      let stats = incr_decision stats;
      let S = set_stats_wl_heur stats S;
      RETURN S})\<close>

definition mop_get_saved_phase_heur_st :: \<open>nat \<Rightarrow> isasat \<Rightarrow> bool nres\<close> where
   \<open>mop_get_saved_phase_heur_st = (\<lambda>L S. mop_get_saved_phase_heur L (get_heur S))\<close>

definition decide_wl_or_skip_D_heur
  :: \<open>isasat \<Rightarrow> (bool \<times> isasat) nres\<close>
where
  \<open>decide_wl_or_skip_D_heur S = (do {
    (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur S;
    case L of
      None \<Rightarrow> RETURN (True, S)
    | Some L \<Rightarrow> do {
        T \<leftarrow> decide_lit_wl_heur L S;
        RETURN (False, T)}
  })
\<close>

definition get_next_phase_st :: \<open>bool \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> (bool) nres\<close> where
  \<open>get_next_phase_st = (\<lambda>b L S.
     (get_next_phase_heur b L (get_heur S)))\<close>

definition find_unassigned_lit_wl_D_heur2
  :: \<open>isasat \<Rightarrow> (isasat \<times> nat option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur2 = (\<lambda>S. do {
      ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd (get_trail_wl_heur S) (get_vmtf_heur S);
      RETURN (set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_trail_wl_heur M (set_vmtf_wl_heur vm S)), L)
    })\<close>

definition decide_wl_or_skip_D_heur' where
  \<open>decide_wl_or_skip_D_heur' = (\<lambda>S. do {
      (S, L) \<leftarrow> find_unassigned_lit_wl_D_heur2 S;
      ASSERT(get_saved_phase_option_heur_pre L (get_restart_heuristics (get_heur S)));
      case L of
       None \<Rightarrow> RETURN (True, S)
     | Some L \<Rightarrow> do {
        L \<leftarrow> do {
            b \<leftarrow> get_next_phase_st (get_target_opts S = TARGET_ALWAYS \<or>
                   (get_target_opts S = TARGET_STABLE_ONLY \<and> get_restart_phase S = STABLE_MODE)) L S;
              RETURN (if b then Pos L else Neg L)};
        T \<leftarrow> decide_lit_wl_heur L S;
        RETURN (False, T)
      }
    })
\<close>


lemma decide_wl_or_skip_D_heur'_decide_wl_or_skip_D_heur:
  \<open>decide_wl_or_skip_D_heur' S \<le> \<Down>Id (decide_wl_or_skip_D_heur S)\<close>
proof -
  have [iff]:
    \<open>{K. (\<exists>y. K = Some y) \<and> atm_of (the K) = x2d} = {Some (Pos x2d), Some (Neg x2d)}\<close> for x2d
    apply (auto simp: atm_of_eq_atm_of)
    apply (case_tac y)
    apply auto
    done
  have H: \<open>do {
    L \<leftarrow>do {ASSERT \<phi>; P};
    Q L} =
    do {ASSERT \<phi>; L \<leftarrow> P; Q L} \<close> for P Q \<phi>
    by auto
  have H: \<open>A \<le> \<Down>Id B \<Longrightarrow> B \<le> \<Down>Id A \<Longrightarrow>A = B\<close> for A B
    by auto
  have K: \<open>RES {Some (Pos x2), Some (Neg x2)} \<le> \<Down> {(x, y). x = Some y} (RES {Pos x2, Neg x2})\<close>
    \<open>RES {(Pos x2), (Neg x2)} \<le> \<Down> {(y, x). x = Some y} (RES {Some (Pos x2), Some (Neg x2)})\<close>  for x2
    by (auto intro!: RES_refine)
  have [simp]: \<open>IsaSAT_Decide_Defs.get_saved_phase_option_heur_pre a (get_restart_heuristics (set_fully_propagated_heur (S))) =
    IsaSAT_Decide_Defs.get_saved_phase_option_heur_pre a (get_restart_heuristics (S))\<close> for S a
    by (cases S)(auto simp: IsaSAT_Decide_Defs.get_saved_phase_option_heur_pre_def get_next_phase_heur_pre_stats_def
      get_next_phase_pre_def set_fully_propagated_heur_def set_fully_propagated_heur_stats_def)
  have S: \<open>decide_wl_or_skip_D_heur S =
       (do {
                   ((M, vm), L) \<leftarrow> isa_vmtf_find_next_undef_upd (get_trail_wl_heur S) (get_vmtf_heur S);
                   ASSERT (IsaSAT_Decide_Defs.get_saved_phase_option_heur_pre L (get_restart_heuristics (get_heur S)));
                   case L of None \<Rightarrow> RETURN (True, set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_vmtf_wl_heur vm (set_trail_wl_heur M S)))
                     | Some L \<Rightarrow> do {
                       _ \<leftarrow> SPEC (\<lambda>_::bool. True);
                       L \<leftarrow>RES {Pos L, Neg L};
                      T \<leftarrow> decide_lit_wl_heur L (set_heur_wl_heur (set_fully_propagated_heur (get_heur S)) (set_vmtf_wl_heur vm (set_trail_wl_heur M S)));
                      RETURN (False, T)
                     }})\<close> for S a b c d e f g h i  j k l m n p q r
     unfolding decide_wl_or_skip_D_heur_def find_unassigned_lit_wl_D_heur_def Let_def
     apply (auto intro!: bind_cong[OF refl] simp: lit_of_found_atm_def split: option.splits)
     apply (rule H)
     subgoal
       apply (refine_rcg K)
       apply auto
       done
     subgoal
       apply (refine_rcg K)
       apply auto
       done
     done
  have [refine]: \<open>get_saved_phase_option_heur_pre x2c (get_restart_heuristics XX) \<Longrightarrow>
     x2c = Some x'a \<Longrightarrow> XX=YY \<Longrightarrow>
    get_next_phase_heur b x'a YY \<le> (SPEC (\<lambda>_::bool. True))\<close> for x'a x1d x1e x1f x1g x2g b XX x2c YY
    by (auto simp: get_next_phase_heur_def get_saved_phase_option_heur_pre_def get_next_phase_pre_def
      get_next_phase_heur_stats_def get_next_phase_stats_def get_next_phase_heur_pre_stats_def
      split: prod.splits)
  have [refine]: \<open>xa =  x'a \<Longrightarrow> RETURN (if xb then Pos xa else Neg xa)
       \<le> \<Down> Id (RES {Pos x'a, Neg x'a})\<close> for xb x'a xa
    by auto
  have [refine]: \<open>decide_lit_wl_heur L S
    \<le> \<Down> Id
        (decide_lit_wl_heur La Sa)\<close> if \<open>(L, La) \<in> Id\<close> \<open>(S, Sa) \<in> Id\<close> for L La S Sa
    using that by auto
  have [intro!]: \<open>get_saved_phase_option_heur_pre (snd pa) (get_restart_heuristics l) \<Longrightarrow>
    get_saved_phase_option_heur_pre (snd pa) (get_restart_heuristics (set_fully_propagated_heur l))\<close> for pa l
    by (cases l; cases pa) (auto simp: get_saved_phase_option_heur_pre_def get_next_phase_heur_pre_stats_def
      get_next_phase_pre_def set_fully_propagated_heur_stats_def
      set_fully_propagated_heur_def)
  show ?thesis
    apply (cases S, simp only: S)
    unfolding find_unassigned_lit_wl_D_heur_def
      nres_monad3 prod.case find_unassigned_lit_wl_D_heur_def
      prod.case decide_wl_or_skip_D_heur'_def get_next_phase_st_def
      find_unassigned_lit_wl_D_heur2_def
      case_prod_beta snd_conv fst_conv bind_to_let_conv
    apply (subst Let_def)
    apply (refine_vcg
      same_in_Id_option_rel)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply assumption back
    subgoal by auto
    subgoal by (auto simp: set_fully_propagated_heur_def split: prod.splits)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end