theory IsaSAT_Setup
  imports
    Watched_Literals_VMTF
    Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Lookup_Conflict
    IsaSAT_Clauses IsaSAT_Arena IsaSAT_Watch_List LBD
    IsaSAT_Options
    IsaSAT_Rephase
    IsaSAT_EMA
    IsaSAT_Stats
    IsaSAT_Profile
begin

chapter \<open>Complete state\<close>

text \<open>We here define the last step of our refinement: the step with all the heuristics and fully
  deterministic code.

  After the result of benchmarking, we concluded that the use of \<^typ>\<open>nat\<close> leads to worse performance
  than using \<open>sint64\<close>. As, however, the later is not complete, we do so with a switch: as long
  as it fits, we use the faster (called 'bounded') version. After that we switch to the 'unbounded'
  version (which is still bounded by memory anyhow) if we generate Standard ML code.

  We have successfully killed all natural numbers when generating LLVM. However, the LLVM binding
  does not have a binding to GMP integers.
\<close>


section \<open>VMTF\<close>

type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>

type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym vdom = \<open>nat list\<close>


subsection \<open>Conflict\<close>

definition size_conflict_wl :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>


section \<open>Full state\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>

paragraph \<open>Definition\<close>
(* TODO rename to isasat *)
type_synonym twl_st_wl_heur =
  \<open>trail_pol \<times> arena \<times>
    conflict_option_rel \<times> nat \<times> (nat watcher) list list \<times> isa_vmtf_remove_int \<times>
    nat \<times> conflict_min_cach_l \<times> lbd \<times> out_learned \<times> stats \<times> restart_heuristics \<times>
    vdom \<times> vdom \<times> clss_size \<times> opts \<times> arena\<close>


paragraph \<open>Accessors\<close>

fun get_clauses_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> arena\<close> where
  \<open>get_clauses_wl_heur (M, N, D, _) = N\<close>

fun get_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> trail_pol\<close> where
  \<open>get_trail_wl_heur (M, N, D, _) = M\<close>

fun get_conflict_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> conflict_option_rel\<close> where
  \<open>get_conflict_wl_heur (_, _, D, _) = D\<close>

fun watched_by_int :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat watched\<close> where
  \<open>watched_by_int (M, N, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat watcher) list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, W, _) = W\<close>

fun literals_to_update_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>literals_to_update_wl_heur (M, N, D, Q, W, _, _)  = Q\<close>

fun set_literals_to_update_wl_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>set_literals_to_update_wl_heur i (M, N, D, _, W') = (M, N, D, i, W')\<close>

definition watched_by_app_heur_pre where
  \<open>watched_by_app_heur_pre = (\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L))\<close>

definition watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

definition mop_watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher nres\<close> where
  \<open>mop_watched_by_app_heur S L K = do {
     ASSERT(K < length (watched_by_int S L));
     ASSERT(nat_of_lit L < length (get_watched_wl_heur S));
     RETURN (watched_by_int S L ! K)}\<close>

lemma watched_by_app_heur_alt_def:
  \<open>watched_by_app_heur = (\<lambda>(M, N, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>
  by (auto simp: watched_by_app_heur_def intro!: ext)

definition watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> isa_vmtf_remove_int\<close> where
  \<open>get_vmtf_heur (_, _, _, _, _, vm, _) = vm\<close>

fun get_count_max_lvls_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_count_max_lvls_heur (_, _, _, _, _, _, clvls, _) = clvls\<close>

fun get_conflict_cach:: \<open>twl_st_wl_heur \<Rightarrow> conflict_min_cach_l\<close> where
  \<open>get_conflict_cach (_, _, _, _, _, _, _, cach, _) = cach\<close>

fun get_lbd :: \<open>twl_st_wl_heur \<Rightarrow> lbd\<close> where
  \<open>get_lbd (_, _, _, _, _, _, _, _, lbd, _) = lbd\<close>

fun get_outlearned_heur :: \<open>twl_st_wl_heur \<Rightarrow> out_learned\<close> where
  \<open>get_outlearned_heur (_, _, _, _, _, _, _, _, _, out, _) = out\<close>

fun get_stats_heur :: \<open>twl_st_wl_heur \<Rightarrow> stats\<close> where
  \<open>get_stats_heur (_, _, _, _, _, _, _, _, _, _, stats, _, _) = stats\<close>

fun get_fast_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_fast_ema_heur (_, _, _, _, _, _, _, _, _, _, _, heur, _) = fast_ema_of heur\<close>

fun get_slow_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_slow_ema_heur (_, _, _, _, _, _, _, _, _, _, _,  heur, _) = slow_ema_of heur\<close>

fun get_conflict_count_heur :: \<open>twl_st_wl_heur \<Rightarrow> restart_info\<close> where
  \<open>get_conflict_count_heur (_, _, _, _, _, _, _, _, _, _, _, heur, _) = restart_info_of heur\<close>

fun get_vdom :: \<open>twl_st_wl_heur \<Rightarrow> nat list\<close> where
  \<open>get_vdom (_, _, _, _, _, _, _, _, _, _, _, _, vdom, _) = vdom\<close>

fun get_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat list\<close> where
  \<open>get_avdom (_, _, _, _, _, _, _, _, _, _, _, _, _, vdom, _) = vdom\<close>

fun get_learned_count :: \<open>twl_st_wl_heur \<Rightarrow> clss_size\<close> where
  \<open>get_learned_count (_, _, _, _, _, _, _, _, _, _, _, _, _, _, lcount, _) = lcount\<close>

fun get_learned_count_number :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_learned_count_number (_, _, _, _, _, _, _, _, _, _, _, _, _, _, lcount, _) = clss_size_lcount lcount\<close>

fun get_opts :: \<open>twl_st_wl_heur \<Rightarrow> opts\<close> where
  \<open>get_opts (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, opts, _) = opts\<close>

fun get_old_arena :: \<open>twl_st_wl_heur \<Rightarrow> arena\<close> where
  \<open>get_old_arena (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, old_arena) = old_arena\<close>

definition get_restart_phase :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>get_restart_phase = (\<lambda>(_, _, _, _, _, _, _, _, _, _, _, heur, _).
     current_restart_phase heur)\<close>

definition cach_refinement_empty where
  \<open>cach_refinement_empty \<A> cach \<longleftrightarrow>
       (cach, \<lambda>_. SEEN_UNKNOWN) \<in> cach_refinement \<A>\<close>


paragraph \<open>VMTF\<close>

definition isa_vmtf where
  \<open>isa_vmtf \<A> M =
    ((Id \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r nat_rel \<times>\<^sub>r \<langle>nat_rel\<rangle>option_rel) \<times>\<^sub>f distinct_atoms_rel \<A>)\<inverse>
      `` vmtf \<A> M\<close>

lemma isa_vmtfI:
  \<open>(vm, to_remove') \<in> vmtf \<A> M \<Longrightarrow> (to_remove, to_remove') \<in> distinct_atoms_rel \<A> \<Longrightarrow>
    (vm, to_remove) \<in> isa_vmtf \<A> M\<close>
  by (auto simp: isa_vmtf_def Image_iff intro!: bexI[of _ \<open>(vm, to_remove')\<close>])

lemma isa_vmtf_consD:
  \<open>((ns, m, fst_As, lst_As, next_search), remove) \<in> isa_vmtf \<A> M \<Longrightarrow>
     ((ns, m, fst_As, lst_As, next_search), remove) \<in> isa_vmtf \<A> (L # M)\<close>
  by (auto simp: isa_vmtf_def dest: vmtf_consD)

lemma isa_vmtf_consD2:
  \<open>f \<in> isa_vmtf \<A> M \<Longrightarrow>
     f \<in> isa_vmtf \<A> (L # M)\<close>
  by (auto simp: isa_vmtf_def dest: vmtf_consD)

text \<open>\<^term>\<open>vdom\<close> is an upper bound on all the address of the clauses that are used in the
state. \<^term>\<open>avdom\<close> includes the active clauses.
\<close>
definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena),
     (M, N, D, NE, UE, NS, US, N0, U0, Q, W)).
    (M', M) \<in> trail_pol (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W))) \<and>
    vm \<in> isa_vmtf (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr N NE UE NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W))  W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    isasat_input_nempty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) heur
  }\<close>

lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       watched_by_int S C = watched_by S' C\<close> and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close> and
     twl_st_heur_state_simp_watched2: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       nat_of_lit C < length(get_watched_wl_heur S)\<close>
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def ac_simps all_atms_st_def)

definition learned_clss_count :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>learned_clss_count S = clss_size_lcount (get_learned_count S) +
    clss_size_lcountUE (get_learned_count S) + clss_size_lcountUS (get_learned_count S) +
    clss_size_lcountU0 (get_learned_count S)\<close>

lemma get_learned_count_learned_clss_countD:
  \<open>get_learned_count S = clss_size_resetUS (get_learned_count T) \<Longrightarrow>
       learned_clss_count S \<le> learned_clss_count T\<close>
  by (cases S; cases T) (auto simp: learned_clss_count_def)

lemma get_learned_count_learned_clss_countD2:
  \<open>get_learned_count S = (get_learned_count T) \<Longrightarrow>
       learned_clss_count S = learned_clss_count T\<close>
  by (cases S; cases T) (auto simp: learned_clss_count_def)

abbreviation twl_st_heur'''
   :: \<open>nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur''''u
   :: \<open>nat \<Rightarrow> nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''''u r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r \<and>
           learned_clss_count S \<le> u}\<close>

definition twl_st_heur' :: \<open>nat multiset \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur' N = {(S, S'). (S, S') \<in> twl_st_heur \<and> dom_m (get_clauses_wl S') = N}\<close>

definition twl_st_heur_conflict_ana
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_conflict_ana =
  {((M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
       avdom, lcount, opts, old_arena),
      (M, N, D, NE, UE, NS, US, N0, U0, Q, W)).
    (M', M) \<in> trail_pol (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W))) \<and>
    vm \<in> isa_vmtf (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr N NE UE NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    isasat_input_nempty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) heur
  }\<close>

lemma twl_st_heur_twl_st_heur_conflict_ana:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_conflict_ana\<close>
  by (auto simp: twl_st_heur_def twl_st_heur_conflict_ana_def ac_simps all_atms_st_def)

lemma twl_st_heur_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_conflict_ana\<close>
  shows
    \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
    \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_conflict_ana_def by (auto simp: map_fun_rel_def ac_simps
    all_atms_st_def)

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a
separate array.\<close>
definition twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom, lcount, opts,
       old_arena),
     (M, N, D, NE, UE, NS, US, N0, U0, Q, W)).
    (M', M) \<in> trail_pol (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', None) \<in> option_lookup_clause_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W))) \<and>
    vm \<in> isa_vmtf (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) cach \<and>
    out_learned M None outl \<and>
    clss_size_corr N NE UE NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    isasat_input_nempty (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st (M, N, D, NE, UE, NS, US, N0, U0, Q, W)) heur
  }\<close>


text \<open>
  The difference between \<^term>\<open>isasat_unbounded_assn\<close> and \<^term>\<open>isasat_bounded_assn\<close> corresponds to the
  following condition:
\<close>
definition isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<longleftrightarrow> (length (get_clauses_wl_heur S) \<le> sint64_max - (uint32_max div 2 + MAX_HEADER_SIZE+1) \<and>
  learned_clss_count S < uint64_max)\<close>

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> length (get_clauses_wl_heur S) \<le> sint64_max\<close> and
  isasat_fast_countD:
    \<open>isasat_fast S \<Longrightarrow> clss_size_lcount (get_learned_count S) < uint64_max\<close>
    \<open>isasat_fast S \<Longrightarrow> clss_size_lcountUS (get_learned_count S) < uint64_max\<close>
    \<open>isasat_fast S \<Longrightarrow> clss_size_lcountUE (get_learned_count S) < uint64_max\<close>
    \<open>isasat_fast S \<Longrightarrow> clss_size_lcountU0 (get_learned_count S) < uint64_max\<close>
  by (solves \<open>cases S; auto simp: isasat_fast_def clss_size_lcountUS_def
    clss_size_lcountUE_def clss_size_lcount_def clss_size_lcountU0_def
    clss_size_allcount_def learned_clss_count_def\<close>)+


section \<open>Lift Operations to State\<close>

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur = (\<lambda>(M, N, (b, _), Q, W, _). b)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro WB_More_Refinement.frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def
     split: option.splits)


lemma get_conflict_wl_is_None_heur_alt_def:
    \<open>RETURN o get_conflict_wl_is_None_heur = (\<lambda>(M, N, (b, _), Q, W, _). RETURN b)\<close>
  unfolding get_conflict_wl_is_None_heur_def
  by auto

definition count_decided_st :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

definition isa_count_decided_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>isa_count_decided_st = (\<lambda>(M, _). count_decided_pol M)\<close>

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o isa_count_decided_st, RETURN o count_decided_st) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro WB_More_Refinement.frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_heur_def isa_count_decided_st_def
       count_decided_trail_ref[THEN fref_to_Down_unRET_Id])


lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition atm_is_in_conflict_st_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool nres\<close> where
  \<open>atm_is_in_conflict_st_heur L = (\<lambda>(M, N, (_, D), _). do {
     ASSERT (atm_in_conflict_lookup_pre (atm_of L) D); RETURN (\<not>atm_in_conflict_lookup (atm_of L) D) })\<close>

lemma atm_is_in_conflict_st_heur_alt_def:
  \<open>atm_is_in_conflict_st_heur = (\<lambda>L (M, N, (_, (_, D)), _). do {ASSERT ((atm_of L) < length D); RETURN (D ! (atm_of L) = None)})\<close>
  unfolding atm_is_in_conflict_st_heur_def by (auto intro!: ext simp: atm_in_conflict_lookup_def atm_in_conflict_lookup_pre_def)

lemma atm_of_in_atms_of_iff: \<open>atm_of x \<in> atms_of D \<longleftrightarrow> x \<in># D \<or> -x \<in># D\<close>
  by (cases x) (auto simp: atms_of_def dest!: multi_member_split)


lemma all_lits_st_alt_def: \<open>set_mset (all_lits_st S) =  set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S))\<close>
  by (auto simp: all_lits_st_def all_lits_def all_lits_of_mm_union
    in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n all_atms_st_def
    all_atms_def)

lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (atm_is_in_conflict_st_heur), uncurry (mop_lit_notin_conflict_wl)) \<in>
   [\<lambda>(L, S). True]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have 1: \<open>aaa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l A \<Longrightarrow> atm_of aaa  \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l A)\<close> for aaa A
    by (auto simp: atms_of_def)
  show ?thesis
  unfolding atm_is_in_conflict_st_heur_def twl_st_heur_def option_lookup_clause_rel_def uncurry_def comp_def
    mop_lit_notin_conflict_wl_def all_lits_st_alt_def
  apply (intro frefI nres_relI)
  apply refine_rcg
find_theorems all_atms_st \<L>\<^sub>a\<^sub>l\<^sub>l
  apply clarsimp
  subgoal
     by (rule atm_in_conflict_lookup_pre)
  subgoal for x y x1 x2 x1a x2a x1b x2b x1c x2c x1d x1e x2d x2e
    apply (subst atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id, of \<open>all_atms_st x2\<close>  \<open>atm_of x1\<close> \<open>the (get_conflict_wl (snd y))\<close>])
    apply (simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def)[]
    apply (auto simp add: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def option_lookup_clause_rel_def
      ac_simps)[]
    apply (simp add: atm_in_conflict_def atm_of_in_atms_of_iff)
    done
  done
qed


abbreviation nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>


section \<open>More theorems\<close>

lemma valid_arena_DECISION_REASON:
  \<open>valid_arena arena NU vdom \<Longrightarrow> DECISION_REASON \<notin># dom_m NU\<close>
  using arena_lifting[of arena NU vdom DECISION_REASON]
  by (auto simp: DECISION_REASON_def SHIFTS_def)

definition count_decided_st_heur :: \<open>_ \<Rightarrow> _\<close> where
  \<open>count_decided_st_heur = (\<lambda>((_,_,_,_,n, _), _). n)\<close>

lemma twl_st_heur_count_decided_st_alt_def:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_def trail_pol_def
  by (cases S) (auto simp: count_decided_st_heur_def)

lemma twl_st_heur_isa_length_trail_get_trail_wl:
  fixes S :: twl_st_wl_heur
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> isa_length_trail (get_trail_wl_heur S) = length (get_trail_wl T)\<close>
  unfolding isa_length_trail_def twl_st_heur_def trail_pol_def
  by (cases S) (auto dest: ann_lits_split_reasons_map_lit_of)

lemma trail_pol_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> trail_pol \<A> \<Longrightarrow> L \<in> trail_pol \<B>\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: trail_pol_def ann_lits_split_reasons_def)

lemma distinct_atoms_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> distinct_atoms_rel \<A> \<Longrightarrow> L \<in> distinct_atoms_rel \<B>\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def distinct_atoms_rel_def distinct_hash_atoms_rel_def
    atoms_hash_rel_def
  by (auto simp: )

lemma phase_save_heur_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> phase_save_heur_rel \<A> heur \<Longrightarrow> phase_save_heur_rel \<B> heur\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: phase_save_heur_rel_def phase_saving_def)

lemma heuristic_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<B> heur\<close>
  using phase_save_heur_rel_cong[of \<A> \<B> \<open>(\<lambda>(_, _, _, _, a, _). a) heur\<close>]
  by (auto simp: heuristic_rel_def)

lemma vmtf_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> vmtf \<A> M \<Longrightarrow> L \<in> vmtf \<B> M\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by auto

lemma isa_vmtf_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> isa_vmtf \<A> M \<Longrightarrow> L \<in> isa_vmtf \<B> M\<close>
  using vmtf_cong[of \<A> \<B>]  distinct_atoms_rel_cong[of \<A> \<B>]
  apply (subst (asm) isa_vmtf_def)
  apply (cases L)
  by (auto intro!: isa_vmtfI)


lemma option_lookup_clause_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> option_lookup_clause_rel \<A> \<Longrightarrow> L \<in> option_lookup_clause_rel \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding option_lookup_clause_rel_def lookup_clause_rel_def
  apply (cases L)
  by (auto intro!: isa_vmtfI)


lemma D\<^sub>0_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> D\<^sub>0 \<A> = D\<^sub>0 \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by auto

lemma phase_saving_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> phase_saving \<A> = phase_saving \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: phase_saving_def)

lemma cach_refinement_empty_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> cach_refinement_empty \<A> = cach_refinement_empty \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (force simp: cach_refinement_empty_def cach_refinement_alt_def
    distinct_subseteq_iff[symmetric] intro!: ext)

lemma vdom_m_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> vdom_m \<A> x y = vdom_m \<B> x y\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: vdom_m_def intro!: ext)


lemma isasat_input_bounded_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> isasat_input_bounded \<A> = isasat_input_bounded \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: intro!: ext)

lemma isasat_input_nempty_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> isasat_input_nempty \<A> = isasat_input_nempty \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: intro!: ext)


section \<open>Shared Code Equations\<close>

definition clause_not_marked_to_delete where
  \<open>clause_not_marked_to_delete S C \<longleftrightarrow> C \<in># dom_m (get_clauses_wl S)\<close>

definition clause_not_marked_to_delete_pre where
  \<open>clause_not_marked_to_delete_pre =
    (\<lambda>(S, C). C \<in> vdom_m (all_atms_st S) (get_watched_wl S) (get_clauses_wl S))\<close>

definition clause_not_marked_to_delete_heur_pre where
  \<open>clause_not_marked_to_delete_heur_pre =
     (\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C)\<close>

definition clause_not_marked_to_delete_heur :: \<open>_ \<Rightarrow> nat \<Rightarrow> bool\<close>
where
  \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow>
    arena_status (get_clauses_wl_heur S) C \<noteq> DELETED\<close>

lemma clause_not_marked_to_delete_rel:
  \<open>(uncurry (RETURN oo clause_not_marked_to_delete_heur),
    uncurry (RETURN oo clause_not_marked_to_delete)) \<in>
    [clause_not_marked_to_delete_pre]\<^sub>f
     twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro WB_More_Refinement.frefI nres_relI)
    (use arena_dom_status_iff in_dom_in_vdom in
      \<open>auto 5 5 simp: clause_not_marked_to_delete_def twl_st_heur_def
        clause_not_marked_to_delete_heur_def arena_dom_status_iff
        clause_not_marked_to_delete_pre_def ac_simps\<close>)


definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j).
           arena_lit_pre (get_clauses_wl_heur S) (i+j))\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = arena_lit (get_clauses_wl_heur S) (i + j)\<close>

lemma access_lit_in_clauses_heur_alt_def:
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j. arena_lit N (i + j))\<close>
  by (auto simp: access_lit_in_clauses_heur_def intro!: ext)

definition (in -) mop_access_lit_in_clauses_heur where
  \<open>mop_access_lit_in_clauses_heur S i j = mop_arena_lit2 (get_clauses_wl_heur S) i j\<close>

lemma mop_access_lit_in_clauses_heur_alt_def:
  \<open>mop_access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j. mop_arena_lit2 N i j)\<close>
  by (auto simp: mop_access_lit_in_clauses_heur_def intro!: ext)

lemma access_lit_in_clauses_heur_fast_pre:
  \<open>arena_lit_pre (get_clauses_wl_heur a) (ba + b) \<Longrightarrow>
    isasat_fast a \<Longrightarrow> ba + b \<le> sint64_max\<close>
  by (auto simp: arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      dest!: arena_lifting(10)
      dest!: isasat_fast_length_leD)[]

(*TODO Move*)
lemma \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (add_mset L C)) = insert (Pos L) (insert (Neg L) (set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l C)))\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

(*END Move*)


lemma correct_watching_dom_watched:
  assumes \<open>correct_watching S\<close> and \<open>\<And>C. C \<in># ran_mf (get_clauses_wl S) \<Longrightarrow> C \<noteq> []\<close>
  shows \<open>set_mset (dom_m (get_clauses_wl S)) \<subseteq>
     \<Union>(((`) fst) ` set ` (get_watched_wl S) ` set_mset (all_lits_st S))\<close>
    (is \<open>?A \<subseteq> ?B\<close>)
proof
  fix C
  assume \<open>C \<in> ?A\<close>
  then obtain D where
    D: \<open>D \<in># ran_mf (get_clauses_wl S)\<close> and
    D': \<open>D = get_clauses_wl S \<propto> C\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    by auto
  have \<open>(hd D) \<in># all_lits_st S\<close>
    using D D' assms(2)[of D]
    by (cases S; cases D)
      (auto simp: all_lits_def all_lits_st_def all_lits_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset
        dest!: multi_member_split)
  then show \<open>C \<in> ?B\<close>
    using assms(1) assms(2)[of D] D D'
      multi_member_split[OF C]
    by (cases S; cases \<open>get_clauses_wl S \<propto> C\<close>;
         cases \<open>hd (get_clauses_wl S \<propto> C)\<close>)
     (auto dest!: multi_member_split simp: \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset correct_watching.simps clause_to_update_def
	  eq_commute[of \<open>_ # _\<close>] atm_of_eq_atm_of
      split: if_splits
	dest!: arg_cong[of \<open>filter_mset _ _\<close> \<open>add_mset _ _\<close> set_mset] eq_insertD)
qed


lemma arena_lit_pre_le_sint64_max:
 \<open>length ba \<le> sint64_max \<Longrightarrow>
       arena_lit_pre ba a \<Longrightarrow> a \<le> sint64_max\<close>
  using arena_lifting(10)[of ba _ _]
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def)

definition rewatch_heur_st
 :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>rewatch_heur_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, ccount, lcount). do {
  ASSERT(length vdom \<le> length N0);
  W \<leftarrow> rewatch_heur vdom N0 W;
  RETURN (M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, ccount, lcount)
  })\<close>

definition rewatch_heur_st_fast where
  \<open>rewatch_heur_st_fast = rewatch_heur_st\<close>

definition rewatch_heur_st_fast_pre where
  \<open>rewatch_heur_st_fast_pre S =
     ((\<forall>x \<in> set (get_vdom S). x \<le> sint64_max) \<and> length (get_clauses_wl_heur S) \<le> sint64_max)\<close>

definition rewatch_st :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>rewatch_st S = do{
     (M, N, D, NE, UE, NS, US, N0, U0, Q, W) \<leftarrow> RETURN S;
     W \<leftarrow> rewatch N W;
     RETURN ((M, N, D, NE, UE, NS, US, N0, U0, Q, W))
  }\<close>


fun remove_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>remove_watched_wl (M, N, D, NE, UE, NS, US, N0, U0, Q, _) = (M, N, D, NE, UE, NS, US, N0, U0, Q)\<close>

lemma rewatch_st_correctness:
  assumes \<open>get_watched_wl S = (\<lambda>_. [])\<close> and
    \<open>\<And>x. x \<in># dom_m (get_clauses_wl S) \<Longrightarrow>
      distinct ((get_clauses_wl S) \<propto> x) \<and> 2 \<le> length ((get_clauses_wl S) \<propto> x)\<close>
  shows \<open>rewatch_st S \<le> SPEC (\<lambda>T. remove_watched_wl S = remove_watched_wl T \<and>
     correct_watching_init T)\<close>
  apply (rule SPEC_rule_conjI)
  subgoal
    using rewatch_correctness[OF assms]
    unfolding rewatch_st_def
    apply (cases S, case_tac \<open>rewatch (get_clauses_wl S) (get_watched_wl S)\<close>)
    by (auto simp: RES_RETURN_RES)
  subgoal
    using rewatch_correctness[OF assms]
    unfolding rewatch_st_def
    apply (cases S, case_tac \<open>rewatch (get_clauses_wl S) (get_watched_wl S)\<close>)
    by (force simp: RES_RETURN_RES)+
  done


section \<open>Fast to slow conversion\<close>

text \<open>Setup to convert a list from \<^typ>\<open>64 word\<close> to \<^typ>\<open>nat\<close>.\<close>
definition convert_wlists_to_nat_conv :: \<open>'a list list \<Rightarrow> 'a list list\<close> where
  \<open>convert_wlists_to_nat_conv = id\<close>

abbreviation twl_st_heur''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> clss_size \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur'' \<D> r lcount \<equiv> {(S, T). (S, T) \<in> twl_st_heur' \<D> \<and>
           length (get_clauses_wl_heur S) = r \<and> get_learned_count S = lcount}\<close>

abbreviation twl_st_heur_up''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> clss_size \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
  \<open>twl_st_heur_up'' \<D> r s L lcount \<equiv> {(S, T). (S, T) \<in> twl_st_heur'' \<D> r lcount \<and>
     length (watched_by T L) = s \<and> s \<le> r}\<close>

lemma length_watched_le:
  assumes
    prop_inv: \<open>correct_watching x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur'' \<D>1 r lcount\<close> and
    x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - MIN_HEADER_SIZE\<close>
proof -
  have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using prop_inv x2 unfolding all_atms_def all_lits_def
    by (cases x1; auto simp: correct_watching.simps ac_simps all_lits_st_alt_def[symmetric])
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
    using x2 xb_x'a unfolding all_atms_def
    by auto

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur'_def twl_st_heur_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def ac_simps)

  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - MIN_HEADER_SIZE\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

lemma length_watched_le2:
  assumes
    prop_inv: \<open>correct_watching_except i j L x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur'' \<D>1 r lcount\<close> and
    x2: \<open>x2 \<in># all_lits_st x1\<close> and diff: \<open>L \<noteq> x2\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - MIN_HEADER_SIZE\<close>
proof -
  from prop_inv diff have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using x2 unfolding all_atms_def all_lits_def
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching_except.simps ac_simps)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def)

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur'_def twl_st_heur_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def ac_simps simp flip: all_atms_def)
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def all_lits_st_alt_def[symmetric]
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def ac_simps simp flip: all_atms_def all_lits_alt_def2
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {MIN_HEADER_SIZE..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - MIN_HEADER_SIZE\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

lemma atm_of_all_lits_of_m: \<open>atm_of `# (all_lits_of_m C) = atm_of `# C + atm_of `# C\<close>
   \<open>atm_of ` set_mset (all_lits_of_m C) = atm_of `set_mset C \<close>
  by (induction C; auto simp: all_lits_of_m_add_mset)+

find_theorems \<L>\<^sub>a\<^sub>l\<^sub>l all_lits_st
(* TODO Move in this buffer *)
lemma mop_watched_by_app_heur_mop_watched_by_at:
   \<open>(uncurry2 mop_watched_by_app_heur, uncurry2 mop_watched_by_at) \<in>
    twl_st_heur \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding mop_watched_by_app_heur_def mop_watched_by_at_def uncurry_def all_lits_def[symmetric]
    all_lits_alt_def[symmetric]
  by (intro frefI nres_relI, refine_rcg)
    (auto simp: twl_st_heur_def map_fun_rel_def all_lits_st_alt_def[symmetric])

lemma mop_watched_by_app_heur_mop_watched_by_at'':
   \<open>(uncurry2 mop_watched_by_app_heur, uncurry2 mop_watched_by_at) \<in>
    twl_st_heur_up'' \<D> r s K lcount \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (rule fref_mono[THEN set_mp, OF _ _ _ mop_watched_by_app_heur_mop_watched_by_at])
    (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits twl_st_heur'_def map_fun_rel_def)

definition polarity_st_pre :: \<open>nat twl_st_wl \<times> nat literal \<Rightarrow> bool\<close> where
  \<open>polarity_st_pre \<equiv> \<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>

definition mop_polarity_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
\<open>mop_polarity_st_heur S L = do {
    mop_polarity_pol (get_trail_wl_heur S) L
  }\<close>

lemma mop_polarity_st_heur_alt_def: \<open>mop_polarity_st_heur = (\<lambda>(M, _) L. do {
    mop_polarity_pol M L
  })\<close>
  by (auto simp: mop_polarity_st_heur_def intro!: ext)

lemma mop_polarity_st_heur_mop_polarity_wl:
   \<open>(uncurry mop_polarity_st_heur, uncurry mop_polarity_wl) \<in>
   [\<lambda>_. True]\<^sub>f twl_st_heur \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding mop_polarity_wl_def mop_polarity_st_heur_def uncurry_def mop_polarity_pol_def
  apply (intro frefI nres_relI)
  apply (refine_rcg polarity_pol_polarity[of \<open>all_atms_st _\<close>, THEN fref_to_Down_unRET_uncurry])
  apply (auto simp: twl_st_heur_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits ac_simps all_lits_st_alt_def[symmetric]
    intro!: polarity_pol_pre simp flip: all_atms_def)
  done

lemma mop_polarity_st_heur_mop_polarity_wl'':
   \<open>(uncurry mop_polarity_st_heur, uncurry mop_polarity_wl) \<in>
   [\<lambda>_. True]\<^sub>f twl_st_heur_up'' \<D> r s K lcount \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  by (rule fref_mono[THEN set_mp, OF _ _ _ mop_polarity_st_heur_mop_polarity_wl])
    (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits twl_st_heur'_def map_fun_rel_def)

(* TODO Kill lhs*)
lemma [simp,iff]: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<longleftrightarrow> blits_in_\<L>\<^sub>i\<^sub>n S\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits all_lits_st_alt_def[symmetric]
  by auto


definition length_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>length_avdom S = length (get_avdom S)\<close>

lemma length_avdom_alt_def:
  \<open>length_avdom = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
    vdom, avdom, lcount). length avdom)\<close>
  by (intro ext) (auto simp: length_avdom_def)


definition clause_is_learned_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool\<close>
where
  \<open>clause_is_learned_heur S C \<longleftrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED\<close>

lemma clause_is_learned_heur_alt_def:
  \<open>clause_is_learned_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats,
     heur, vdom, lcount) C . arena_status N' C = LEARNED)\<close>
  by (intro ext) (auto simp: clause_is_learned_heur_def)

definition get_the_propagation_reason_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close>
where
  \<open>get_the_propagation_reason_heur S = get_the_propagation_reason_pol (get_trail_wl_heur S)\<close>

lemma get_the_propagation_reason_heur_alt_def:
  \<open>get_the_propagation_reason_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats,
     heur, vdom, lcount) L . get_the_propagation_reason_pol M' L)\<close>
  by (intro ext) (auto simp: get_the_propagation_reason_heur_def)



(* TODO deduplicate arena_lbd = get_clause_LBD *)
definition clause_lbd_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>clause_lbd_heur S C = arena_lbd (get_clauses_wl_heur S) C\<close>

definition (in -) access_length_heur where
  \<open>access_length_heur S i = arena_length (get_clauses_wl_heur S) i\<close>

lemma access_length_heur_alt_def:
  \<open>access_length_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
    lcount) C. arena_length N' C)\<close>
  by (intro ext) (auto simp: access_length_heur_def arena_lbd_def)


definition marked_as_used_st where
  \<open>marked_as_used_st T C =
    marked_as_used (get_clauses_wl_heur T) C\<close>

lemma marked_as_used_st_alt_def:
  \<open>marked_as_used_st = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
      lcount) C.
     marked_as_used N' C)\<close>
  by (intro ext) (auto simp: marked_as_used_st_def)


definition access_vdom_at :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_vdom_at S i = get_avdom S ! i\<close>

lemma access_vdom_at_alt_def:
  \<open>access_vdom_at = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom, lcount) i. avdom ! i)\<close>
  by (intro ext) (auto simp: access_vdom_at_def)

definition access_vdom_at_pre where
  \<open>access_vdom_at_pre S i \<longleftrightarrow> i < length (get_avdom S)\<close>

(*TODO check which of theses variants are used!*)
definition mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, delete_index_and_swap avdom i, clss_size_decr_lcount lcount, opts, old_arena))\<close>

definition mark_garbage_heur2 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mark_garbage_heur2 C = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts). do{
    let st = arena_status N' C = IRRED;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, if st then lcount else clss_size_decr_lcount lcount, opts) })\<close>

definition mark_garbage_heur3 :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur3 C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, delete_index_and_swap avdom i, clss_size_resetUS (clss_size_decr_lcount lcount), opts, old_arena))\<close>
definition mark_garbage_heur4 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mark_garbage_heur4 C = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts). do{
    let st = arena_status N' C = IRRED;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
      vdom, avdom,
      if st then clss_size_resetUS lcount else
        clss_size_resetUS (clss_size_incr_lcountUE (clss_size_decr_lcount lcount)), opts) })\<close>

definition delete_index_vdom_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>where
  \<open>delete_index_vdom_heur = (\<lambda>i (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom, lcount).
     (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom, delete_index_and_swap avdom i, lcount))\<close>

lemma arena_act_pre_mark_used:
  \<open>arena_act_pre arena C \<Longrightarrow>
  arena_act_pre (mark_unused arena C) C\<close>
  unfolding arena_act_pre_def arena_is_valid_clause_idx_def
  apply clarify
  apply (rule_tac x=N in exI)
  apply (rule_tac x=vdom in exI)
  by (auto simp: arena_act_pre_def
    simp: valid_arena_mark_unused)

definition mop_mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mop_mark_garbage_heur C i = (\<lambda>S. do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur S, C) \<and> clss_size_lcount (get_learned_count S) \<ge> 1 \<and> i < length (get_avdom S));
    RETURN (mark_garbage_heur C i S)
  })\<close>

definition mop_mark_garbage_heur3 :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mop_mark_garbage_heur3 C i = (\<lambda>S. do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur S, C) \<and> clss_size_lcount (get_learned_count S) \<ge> 1 \<and> i < length (get_avdom S));
    RETURN (mark_garbage_heur3 C i S)
  })\<close>

definition mark_unused_st_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_unused_st_heur C = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl,
      stats, heur, vdom, avdom, lcount, opts).
    (M', mark_unused N' C, D', j, W', vm, clvls, cach,
      lbd, outl, stats, heur,
      vdom, avdom, lcount, opts))\<close>


definition mop_mark_unused_st_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mop_mark_unused_st_heur C T = do {
     ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
     RETURN (mark_unused_st_heur C T)
  }\<close>

lemma mop_mark_garbage_heur_alt_def:
  \<open>mop_mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur (M', N', D', j, W', vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, old_arena), C) \<and> clss_size_lcount lcount \<ge> 1 \<and> i < length avdom);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl,
      stats, heur,
       vdom, delete_index_and_swap avdom i, clss_size_decr_lcount lcount, opts, old_arena)
   })\<close>
  unfolding mop_mark_garbage_heur_def mark_garbage_heur_def
  by (auto intro!: ext)

lemma mark_unused_st_heur_simp[simp]:
  \<open>get_avdom (mark_unused_st_heur C T) = get_avdom T\<close>
  \<open>get_vdom (mark_unused_st_heur C T) = get_vdom T\<close>
  by (cases T; auto simp: mark_unused_st_heur_def; fail)+


lemma get_slow_ema_heur_alt_def:
   \<open>RETURN o get_slow_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, (fema, sema,  _), lcount). RETURN sema)\<close>
  by auto


lemma get_fast_ema_heur_alt_def:
   \<open>RETURN o get_fast_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, (fema, sema, ccount), lcount). RETURN fema)\<close>
  by auto


fun get_conflict_count_since_last_restart_heur :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count_since_last_restart_heur (_, _, _, _, _, _, _, _, _, _, _,
    (_, _, (ccount, _), _), _)
      = ccount\<close>

lemma (in -) get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_since_last_restart_heur = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd,
       outl, stats, (_, _, (ccount, _), _), lcount). RETURN ccount)\<close>
  by auto

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, _, vdom, avdom, lcount, opts). RETURN lcount)\<close>
  by auto

definition get_global_conflict_count where
  \<open>get_global_conflict_count S = stats_conflicts (get_stats_heur S)\<close>

lemma (in -) get_global_conflict_count_alt_def:
   \<open>RETURN o get_global_conflict_count = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd,
       outl, (stats), _, lcount). RETURN (stats_conflicts stats))\<close>
  by (auto simp: get_global_conflict_count_def)


text \<open>
  I also played with \<^term>\<open>ema_reinit fast_ema\<close> and \<^term>\<open>ema_reinit slow_ema\<close>. Currently removed,
  to test the performance, I remove it.
\<close>
definition incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
       res_info, wasted, \<phi>, relu), vdom, avdom, lcount, opts, old_arena). do{
     RETURN (M, N, D, Q, W, vm, clvls, cach, lbd, outl, incr_restart stats,
       (fast_ema, slow_ema,
       restart_info_restart_done res_info, wasted, \<phi>, reluctant_untrigger relu), vdom, avdom,
       clss_size_resetUS lcount, opts, old_arena)
  })\<close>

definition incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
     res_info, wasted, \<phi>, relu), vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, clvls, cach, lbd, outl, incr_lrestart stats,
       (fast_ema, slow_ema, restart_info_restart_done res_info, wasted, \<phi>, reluctant_untrigger relu),
       vdom, avdom, lcount)
  })\<close>

definition incr_wasted_st :: \<open>64 word \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>incr_wasted_st = (\<lambda>waste (M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
     res_info, wasted, \<phi>), vdom, avdom, lcount). do{
     (M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats,
       (fast_ema, slow_ema, res_info, wasted+waste, \<phi>),
       vdom, avdom, lcount)
  })\<close>


definition wasted_bytes_st :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>wasted_bytes_st = (\<lambda>(M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
     res_info, wasted, \<phi>), vdom, avdom, lcount).
     wasted)\<close>


definition opts_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_restart_st = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, _). (opts_restart opts))\<close>

definition opts_reduction_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, _). (opts_reduce opts))\<close>

definition opts_unbounded_mode_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_unbounded_mode_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, _). (opts_unbounded_mode opts))\<close>

definition opts_minimum_between_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>opts_minimum_between_restart_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, _). (opts_minimum_between_restart opts))\<close>

definition opts_restart_coeff1_st :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>opts_restart_coeff1_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, _). (opts_restart_coeff1 opts))\<close>

definition opts_restart_coeff2_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>opts_restart_coeff2_st = (\<lambda>(M, N0, D, Q, W, vm, clvls, cach, lbd, outl,
       stats, heur, vdom, avdom, lcount, opts, _). (opts_restart_coeff2 opts))\<close>

definition isasat_length_trail_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>isasat_length_trail_st S = isa_length_trail (get_trail_wl_heur S)\<close>

lemma isasat_length_trail_st_alt_def:
  \<open>isasat_length_trail_st = (\<lambda>(M, _). isa_length_trail M)\<close>
  by (auto simp: isasat_length_trail_st_def intro!: ext)

definition mop_isasat_length_trail_st :: \<open>twl_st_wl_heur \<Rightarrow> nat nres\<close> where
  \<open>mop_isasat_length_trail_st S = do {
    ASSERT(isa_length_trail_pre (get_trail_wl_heur S));
    RETURN (isa_length_trail (get_trail_wl_heur S))
  }\<close>

lemma mop_isasat_length_trail_st_alt_def:
  \<open>mop_isasat_length_trail_st = (\<lambda>(M, _). do {
    ASSERT(isa_length_trail_pre M);
    RETURN (isa_length_trail M)
  })\<close>
  by (auto simp: mop_isasat_length_trail_st_def intro!: ext)


definition get_pos_of_level_in_trail_imp_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
\<open>get_pos_of_level_in_trail_imp_st S = get_pos_of_level_in_trail_imp (get_trail_wl_heur S)\<close>

lemma get_pos_of_level_in_trail_imp_alt_def:
  \<open>get_pos_of_level_in_trail_imp_st = (\<lambda>(M, _) L.  do {k \<leftarrow> get_pos_of_level_in_trail_imp M L; RETURN k})\<close>
  by (auto simp: get_pos_of_level_in_trail_imp_st_def intro!: ext)


definition mop_clause_not_marked_to_delete_heur :: \<open>_ \<Rightarrow> nat \<Rightarrow> bool nres\<close>
where
  \<open>mop_clause_not_marked_to_delete_heur S C = do {
    ASSERT(clause_not_marked_to_delete_heur_pre (S, C));
    RETURN (clause_not_marked_to_delete_heur S C)
  }\<close>

definition mop_arena_lbd_st where
  \<open>mop_arena_lbd_st S =
    mop_arena_lbd (get_clauses_wl_heur S)\<close>

lemma mop_arena_lbd_st_alt_def:
  \<open>mop_arena_lbd_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) C. do {
       ASSERT(get_clause_LBD_pre arena C);
      RETURN(arena_lbd arena C)
   })\<close>
  unfolding mop_arena_lbd_st_def mop_arena_lbd_def
  by (auto intro!: ext)

definition mop_arena_status_st where
  \<open>mop_arena_status_st S =
    mop_arena_status (get_clauses_wl_heur S)\<close>

lemma mop_arena_status_st_alt_def:
  \<open>mop_arena_status_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) C. do {
       ASSERT(arena_is_valid_clause_vdom arena C);
      RETURN(arena_status arena C)
   })\<close>
  unfolding mop_arena_status_st_def mop_arena_status_def
  by (auto intro!: ext)


definition mop_marked_as_used_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_marked_as_used_st S =
    mop_marked_as_used (get_clauses_wl_heur S)\<close>

lemma mop_marked_as_used_st_alt_def:
  \<open>mop_marked_as_used_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) C. do {
       ASSERT(marked_as_used_pre arena C);
      RETURN(marked_as_used arena C)
   })\<close>
  unfolding mop_marked_as_used_st_def mop_marked_as_used_def
  by (auto intro!: ext)

definition mop_arena_length_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_arena_length_st S =
    mop_arena_length (get_clauses_wl_heur S)\<close>

lemma mop_arena_length_st_alt_def:
  \<open>mop_arena_length_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena) C. do {
      ASSERT(arena_is_valid_clause_idx arena C);
      RETURN (arena_length arena C)
   })\<close>
  unfolding mop_arena_length_st_def mop_arena_length_def
  by (auto intro!: ext)

definition full_arena_length_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>full_arena_length_st = (\<lambda>(M', arena, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena). length arena)\<close>

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) \<propto> i ! j\<close>

lemma twl_st_heur_get_clauses_access_lit[simp]:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
    i < length (get_clauses_wl T \<propto> C) \<Longrightarrow>
    get_clauses_wl T \<propto> C ! i = access_lit_in_clauses_heur S C i\<close>
    for S T C i
    by (cases S; cases T)
      (auto simp: arena_lifting twl_st_heur_def access_lit_in_clauses_heur_def)

text \<open>In an attempt to avoid using @{thm ac_simps} everywhere.\<close>
lemma all_lits_simps[simp]:
  \<open>all_lits N ((NE + UE) + (NS + US)) = all_lits N (NE + UE + NS + US)\<close>
  \<open>all_atms N ((NE + UE) + (NS + US)) = all_atms N (NE + UE + NS + US)\<close>
  by (auto simp: ac_simps)

lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN \<circ>\<circ> clause_not_marked_to_delete_heur = (\<lambda>(M, arena, D, oth) C.
     RETURN (arena_status arena C \<noteq> DELETED))\<close>
  unfolding clause_not_marked_to_delete_heur_def by (auto intro!: ext)


lemma learned_clss_count_twl_st_heur: \<open>(T, Ta) \<in> twl_st_heur \<Longrightarrow>
                      learned_clss_count T \<le>
                      size (get_learned_clss_wl Ta) +
                      size (get_unit_learned_clss_wl Ta) +
                     size (get_subsumed_learned_clauses_wl Ta) +
                     size (get_learned_clauses0_wl Ta)\<close>
  by (auto simp: twl_st_heur_def clss_size_def learned_clss_count_def clss_size_corr_def
    clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def
    get_learned_clss_wl_def clss_size_lcountU0_def)


lemma clss_size_allcount_alt_def:
  \<open>clss_size_allcount S = clss_size_lcountUS S + clss_size_lcountU0 S + clss_size_lcountUE S + 
    clss_size_lcount S\<close>
  by (cases S) (auto simp: clss_size_allcount_def clss_size_lcountUS_def
    clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountU0_def)

definition isasat_trail_nth_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat literal nres\<close> where
\<open>isasat_trail_nth_st S i = isa_trail_nth (get_trail_wl_heur S) i\<close>

lemma isasat_trail_nth_st_alt_def:
  \<open>isasat_trail_nth_st = (\<lambda>(M, _) i.  isa_trail_nth M i)\<close>
  by (auto simp: isasat_trail_nth_st_def intro!: ext)

definition get_the_propagation_reason_pol_st :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
\<open>get_the_propagation_reason_pol_st S i = get_the_propagation_reason_pol (get_trail_wl_heur S) i\<close>

lemma get_the_propagation_reason_pol_st_alt_def:
  \<open>get_the_propagation_reason_pol_st = (\<lambda>(M, _) i.  get_the_propagation_reason_pol M i)\<close>
  by (auto simp: get_the_propagation_reason_pol_st_def intro!: ext)

definition empty_US_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>empty_US_heur = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena).
  (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, clss_size_resetUS lcount, opts, old_arena)
  )\<close>

definition empty_Q_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_Q_wl = (\<lambda>(M', N, D, NE, UE, NS, US, N0, U0, _, W). (M', N, D, NE, UE, NS, {#}, N0, U0, {#}, W))\<close>

definition empty_Q_wl2  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_Q_wl2 = (\<lambda>(M', N, D, NE, UE, NS, US, N0, U0, _, W). (M', N, D, NE, UE, NS, US, N0, U0, {#}, W))\<close>

definition empty_US_heur_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_US_heur_wl = (\<lambda>(M', N, D, NE, UE, NS, US, N0, U0, Q, W). (M', N, D, NE, UE, NS, {#}, N0, U0, Q, W))\<close>

lemma incr_wasted_st_twl_st[simp]:
  \<open>get_avdom (incr_wasted_st w T) = get_avdom T\<close>
  \<open>get_vdom (incr_wasted_st w T) = get_vdom T\<close>
  \<open>get_trail_wl_heur (incr_wasted_st w T) = get_trail_wl_heur T\<close>
  \<open>get_clauses_wl_heur (incr_wasted_st C T) = get_clauses_wl_heur T\<close>
  \<open>get_conflict_wl_heur (incr_wasted_st C T) = get_conflict_wl_heur T\<close>
  \<open>get_learned_count (incr_wasted_st C T) = get_learned_count T\<close>
  \<open>get_conflict_count_heur (incr_wasted_st C T) = get_conflict_count_heur T\<close>
  by (cases T; auto simp: incr_wasted_st_def; fail)+

definition heuristic_reluctant_triggered2_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>heuristic_reluctant_triggered2_st = (\<lambda> (_, _, _, _, _, _, _, _, _, _, _, heur, _). heuristic_reluctant_triggered2 heur)\<close>

definition heuristic_reluctant_untrigger_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>heuristic_reluctant_untrigger_st = (\<lambda> (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
  vdom, avdom, lcount, opts, old_arena).
  (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heuristic_reluctant_untrigger heur,
       vdom, avdom, lcount, opts, old_arena))\<close>
lemma twl_st_heur''D_twl_st_heurD:
  assumes H: \<open>(\<And>\<D> r. f \<in> twl_st_heur'' \<D> r lcount \<rightarrow>\<^sub>f \<langle>twl_st_heur'' \<D> r lcount\<rangle> nres_rel)\<close>
  shows \<open>f \<in> {(S, T). (S, T) \<in> twl_st_heur \<and> get_learned_count S = lcount} \<rightarrow>\<^sub>f
        \<langle>{(S, T). (S, T) \<in> twl_st_heur \<and> get_learned_count S = lcount}\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>dom_m (get_clauses_wl y)\<close>  \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur'' (dom_m (get_clauses_wl y))
        (length (get_clauses_wl_heur x)) lcount\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed


lemma twl_st_heur'''D_twl_st_heurD:
  assumes H: \<open>(\<And>r. f \<in> twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>twl_st_heur''' r\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>twl_st_heur''' (length (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed


lemma twl_st_heur'''D_twl_st_heurD_prod:
  assumes H: \<open>(\<And>r. f \<in> twl_st_heur''' r \<rightarrow>\<^sub>f \<langle>A \<times>\<^sub>r twl_st_heur''' r\<rangle> nres_rel)\<close>
  shows \<open>f \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>A \<times>\<^sub>r twl_st_heur\<rangle> nres_rel\<close>  (is \<open>_ \<in> ?A B\<close>)
proof -
  obtain f1 f2 where f: \<open>f = (f1, f2)\<close>
    by (cases f) auto
  show ?thesis
    unfolding f
    apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
    apply (intro conjI impI allI)
    subgoal for x y
      using assms[of \<open>length (get_clauses_wl_heur x)\<close>,
        unfolded twl_st_heur'_def nres_rel_def in_pair_collect_simp f,
        rule_format] unfolding f
      apply (simp only: fref_def twl_st_heur'_def nres_rel_def in_pair_collect_simp)
      apply (drule spec[of _ x])
      apply (drule spec[of _ y])
      apply simp
      apply (rule "weaken_\<Down>'"[of _ \<open>A \<times>\<^sub>r twl_st_heur''' (length (get_clauses_wl_heur x))\<close>])
      apply (fastforce simp: twl_st_heur'_def)+
      done
    done
qed

definition (in -) lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal nres\<close> where
  \<open>lit_of_hd_trail_st_heur S = do {
     ASSERT (fst (get_trail_wl_heur S) \<noteq> []);
     RETURN (lit_of_last_trail_pol (get_trail_wl_heur S))
  }\<close>

lemma lit_of_hd_trail_st_heur_alt_def:
  \<open>lit_of_hd_trail_st_heur = (\<lambda>(M, N, D, Q, W, vm, \<phi>). do {ASSERT (fst M \<noteq> []); RETURN (lit_of_last_trail_pol M)})\<close>
  by (auto simp: lit_of_hd_trail_st_heur_def lit_of_hd_trail_def intro!: ext)


subsection \<open>Lifting of Options\<close>

definition get_target_opts :: \<open>twl_st_wl_heur \<Rightarrow> opts_target\<close> where
  \<open>get_target_opts S = opts_target (get_opts S)\<close>

definition get_GC_units_opt :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>get_GC_units_opt S = opts_GC_units_lim (get_opts S)\<close>

definition units_since_last_GC_st :: \<open>twl_st_wl_heur \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC_st S = units_since_last_GC (get_stats_heur S)\<close>

definition reset_units_since_last_GC_st :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>reset_units_since_last_GC_st = (\<lambda> (M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
  vdom, avdom, lcount, opts, old_arena).
  (M', N', D', j, W', vm, clvls, cach, lbd, outl, reset_units_since_last_GC stats, heur,
       vdom, avdom, lcount, opts, old_arena))\<close>
end
