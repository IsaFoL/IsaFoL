theory IsaSAT_Setup
  imports
    Tuple16
    Watched_Literals_VMTF
    Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Lookup_Conflict
    IsaSAT_Clauses IsaSAT_Arena IsaSAT_Watch_List LBD
    IsaSAT_Options
    IsaSAT_Rephase
    IsaSAT_EMA
    IsaSAT_Stats
    IsaSAT_Profile
    IsaSAT_VDom
begin

chapter \<open>Complete state\<close>

hide_const (open) IsaSAT_VDom.get_aivdom

text \<open>We here define the last step of our refinement: the step with all the heuristics and fully
  deterministic code.

  After the result of benchmarking, we concluded that the use of \<^typ>\<open>nat\<close> leads to worse performance
  than using \<open>sint64\<close>. As, however, the later is not complete, we do so with a switch: as long
  as it fits, we use the faster (called 'bounded') version. After that we switch to the 'unbounded'
  version (which is still bounded by memory anyhow) if we generate Standard ML code.

  We have successfully killed all natural numbers when generating LLVM. However, the LLVM binding
  does not have a binding to GMP integers.
\<close>
(*TODO Move*)
fun get_unkept_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unkept_unit_init_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NE\<close>

fun get_unkept_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_unkept_unit_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = UE\<close>

fun get_kept_unit_init_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_kept_unit_init_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = NEk\<close>

fun get_kept_unit_learned_clss_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v clauses\<close> where
  \<open>get_kept_unit_learned_clss_wl (M, N, D, NE, UE, NEk, UEk, NS, US, Q, W) = UEk\<close>

lemma get_unit_init_clss_wl_alt_def:
  \<open>get_unit_init_clss_wl T = get_unkept_unit_init_clss_wl T + get_kept_unit_init_clss_wl T\<close>
  by (cases T) auto

lemma get_unit_learned_clss_wl_alt_def:
  \<open>get_unit_learned_clss_wl T = get_unkept_unit_learned_clss_wl T + get_kept_unit_learned_clss_wl T\<close>
  by (cases T) auto


section \<open>VMTF\<close>

type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>

type_synonym out_learned = \<open>nat clause_l\<close>


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



type_synonym isasat = \<open>(trail_pol, arena,
      conflict_option_rel, nat, (nat watcher) list list, isa_vmtf_remove_int,
      nat, conflict_min_cach_l, lbd, out_learned, isasat_stats, isasat_restart_heuristics, 
     isasat_aivdom, clss_size, opts, arena) isasat_int\<close>

abbreviation IsaSAT where
  \<open>IsaSAT a b c d e f g h i j k l m n xo p \<equiv> IsaSAT_int a b c d e f g h i j k l m n xo p :: isasat\<close>

abbreviation get_trail_wl_heur :: \<open>isasat \<Rightarrow> trail_pol\<close> where
  \<open>get_trail_wl_heur \<equiv> Tuple16_get_a\<close>

abbreviation get_clauses_wl_heur :: \<open>isasat \<Rightarrow> arena\<close> where
  \<open>get_clauses_wl_heur \<equiv> Tuple16_get_b\<close>

abbreviation get_conflict_wl_heur :: \<open>isasat \<Rightarrow> conflict_option_rel\<close> where
  \<open>get_conflict_wl_heur \<equiv> Tuple16_get_c\<close>

abbreviation literals_to_update_wl_heur :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>literals_to_update_wl_heur \<equiv> Tuple16_get_d\<close>

abbreviation get_watched_wl_heur :: \<open>isasat \<Rightarrow> (nat watcher) list list\<close> where
  \<open>get_watched_wl_heur \<equiv> Tuple16_get_e\<close>

abbreviation get_vmtf_heur :: \<open>isasat \<Rightarrow> isa_vmtf_remove_int\<close> where
  \<open>get_vmtf_heur \<equiv> Tuple16_get_f\<close>

abbreviation get_count_max_lvls_heur :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>get_count_max_lvls_heur \<equiv> Tuple16_get_g\<close>

abbreviation get_conflict_cach :: \<open>isasat \<Rightarrow> conflict_min_cach_l\<close> where
  \<open>get_conflict_cach \<equiv> Tuple16_get_h\<close>

abbreviation get_lbd :: \<open>isasat \<Rightarrow> lbd\<close> where
  \<open>get_lbd \<equiv> Tuple16_get_i\<close>

abbreviation get_outlearned_heur :: \<open>isasat \<Rightarrow> out_learned\<close> where
  \<open>get_outlearned_heur \<equiv> Tuple16_get_j\<close>

abbreviation get_stats_heur :: \<open>isasat \<Rightarrow> isasat_stats\<close> where
  \<open>get_stats_heur \<equiv> Tuple16_get_k\<close>

abbreviation get_heur :: \<open>isasat \<Rightarrow> isasat_restart_heuristics\<close> where
  \<open>get_heur \<equiv> Tuple16_get_l\<close>

abbreviation get_aivdom :: \<open>isasat \<Rightarrow> isasat_aivdom\<close> where
  \<open>get_aivdom \<equiv> Tuple16_get_m\<close>

abbreviation get_learned_count :: \<open>isasat \<Rightarrow> clss_size\<close> where
  \<open>get_learned_count \<equiv> Tuple16_get_n\<close>

abbreviation get_opts :: \<open>isasat \<Rightarrow> opts\<close> where
  \<open>get_opts \<equiv> Tuple16_get_o\<close>

abbreviation get_old_arena :: \<open>isasat \<Rightarrow> arena\<close> where
  \<open>get_old_arena \<equiv> Tuple16_get_p\<close>

abbreviation set_trail_wl_heur :: \<open>trail_pol \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_trail_wl_heur \<equiv> Tuple16.set_a\<close>

abbreviation set_clauses_wl_heur :: \<open>arena \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_clauses_wl_heur \<equiv> Tuple16.set_b\<close>

abbreviation set_conflict_wl_heur :: \<open>conflict_option_rel \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_conflict_wl_heur \<equiv> Tuple16.set_c\<close>

abbreviation set_literals_to_update_wl_heur :: \<open>nat \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_literals_to_update_wl_heur \<equiv> Tuple16.set_d\<close>

abbreviation set_watched_wl_heur :: \<open>nat watcher list list \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_watched_wl_heur \<equiv> Tuple16.set_e\<close>

abbreviation set_vmtf_wl_heur :: \<open>isa_vmtf_remove_int \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_vmtf_wl_heur \<equiv> Tuple16.set_f\<close>

abbreviation set_count_max_wl_heur :: \<open>nat \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_count_max_wl_heur \<equiv> Tuple16.set_g\<close>

abbreviation set_ccach_max_wl_heur :: \<open>conflict_min_cach_l \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_ccach_max_wl_heur \<equiv> Tuple16.set_h\<close>

abbreviation set_lbd_wl_heur :: \<open>lbd \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_lbd_wl_heur \<equiv> Tuple16.set_i\<close>

abbreviation set_outl_wl_heur :: \<open>out_learned \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_outl_wl_heur \<equiv> Tuple16.set_j\<close>

abbreviation set_stats_wl_heur :: \<open>isasat_stats \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>set_stats_wl_heur \<equiv> Tuple16.set_k\<close>

abbreviation set_heur_wl_heur :: \<open>isasat_restart_heuristics \<Rightarrow>isasat \<Rightarrow> isasat\<close> where
  \<open>set_heur_wl_heur \<equiv> Tuple16.set_l\<close>

abbreviation set_aivdom_wl_heur :: \<open>isasat_aivdom \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_aivdom_wl_heur \<equiv> Tuple16.set_m\<close>

abbreviation set_learned_count_wl_heur :: \<open>clss_size \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_learned_count_wl_heur \<equiv> Tuple16.set_n\<close>

abbreviation set_opts_wl_heur :: \<open>opts \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_opts_wl_heur \<equiv> Tuple16.set_o\<close>

abbreviation set_old_arena_wl_heur :: \<open>arena \<Rightarrow>isasat \<Rightarrow> _\<close> where
  \<open>set_old_arena_wl_heur \<equiv> Tuple16.set_p\<close>

fun watched_by_int :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat watched\<close> where
  \<open>watched_by_int S L = get_watched_wl_heur S ! nat_of_lit L\<close>

definition watched_by_app_heur_pre where
  \<open>watched_by_app_heur_pre = (\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L))\<close>

definition watched_by_app_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

definition mop_watched_by_app_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher nres\<close> where
  \<open>mop_watched_by_app_heur S L K = do {
     ASSERT(K < length (watched_by_int S L));
     ASSERT(nat_of_lit L < length (get_watched_wl_heur S));
     RETURN (watched_by_int S L ! K)}\<close>

definition watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

fun get_fast_ema_heur :: \<open>isasat \<Rightarrow> ema\<close> where
  \<open>get_fast_ema_heur S = fast_ema_of (get_heur S)\<close>

fun get_slow_ema_heur :: \<open>isasat \<Rightarrow> ema\<close> where
  \<open>get_slow_ema_heur S = slow_ema_of (get_heur S)\<close>

fun get_conflict_count_heur :: \<open>isasat \<Rightarrow> restart_info\<close> where
  \<open>get_conflict_count_heur S = restart_info_of (get_heur S)\<close>

abbreviation get_vdom :: \<open>isasat \<Rightarrow> nat list\<close> where
  \<open>get_vdom S \<equiv> get_vdom_aivdom (get_aivdom S)\<close>

abbreviation get_avdom :: \<open>isasat \<Rightarrow> nat list\<close> where
  \<open>get_avdom S \<equiv> get_avdom_aivdom (get_aivdom S)\<close>

abbreviation get_ivdom :: \<open>isasat \<Rightarrow> nat list\<close> where
  \<open>get_ivdom S \<equiv> get_ivdom_aivdom (get_aivdom S)\<close>

abbreviation get_tvdom :: \<open>isasat \<Rightarrow> nat list\<close> where
  \<open>get_tvdom S \<equiv> get_tvdom_aivdom (get_aivdom S)\<close>

abbreviation get_learned_count_number :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>get_learned_count_number S \<equiv> clss_size_lcount (get_learned_count S)\<close>

definition get_restart_phase :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_restart_phase = (\<lambda>S.
     current_restart_phase (get_heur S))\<close>

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

definition twl_st_heur :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st T) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st T)) \<and>
    vm \<in> isa_vmtf (all_atms_st T) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st T) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st T) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_atms_st T) \<and>
    isasat_input_nempty (all_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st T) heur
  }\<close>


lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       watched_by_int S C = watched_by S' C\<close>
      \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       get_watched_wl_heur S ! (nat_of_lit C) =  get_watched_wl S' C\<close>and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close> and
     twl_st_heur_state_simp_watched2: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       nat_of_lit C < length(get_watched_wl_heur S)\<close>
  using assms unfolding twl_st_heur_def by (solves \<open>cases S; cases S'; auto simp add: Let_def map_fun_rel_def ac_simps all_atms_st_def\<close>)+

text \<open>
  This is the version of the invariants where some informations are already lost. For example,
  losing statistics does not matter if UNSAT was derived.
  \<close>
definition twl_st_heur_loop :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_loop =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st T) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st T)) \<and>
    vm \<in> isa_vmtf (all_atms_st T) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st T) cach \<and>
    out_learned M D outl \<and>
    (D = None \<longrightarrow> clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount) \<and>
    vdom_m (all_atms_st T)  W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_atms_st T) \<and>
    isasat_input_nempty (all_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st T) heur
  }\<close>

abbreviation learned_clss_count_lcount :: \<open>_\<close> where
  \<open>learned_clss_count_lcount S \<equiv> clss_size_lcount (S) +
  clss_size_lcountUE (S) + clss_size_lcountUEk (S) +
  clss_size_lcountUS (S) +
    clss_size_lcountU0 (S)\<close>

definition learned_clss_count :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>learned_clss_count S = learned_clss_count_lcount (get_learned_count S)\<close>

lemma get_learned_count_learned_clss_countD:
  \<open>get_learned_count S = clss_size_resetUS (get_learned_count T) \<Longrightarrow>
       learned_clss_count S \<le> learned_clss_count T\<close>
  \<open>get_learned_count S = clss_size_resetUS0 (get_learned_count T) \<Longrightarrow>
       learned_clss_count S \<le> learned_clss_count T\<close>
  by (cases S; cases T; auto simp: learned_clss_count_def; fail)+

lemma get_learned_count_learned_clss_countD2:
  \<open>get_learned_count S = (get_learned_count T) \<Longrightarrow>
       learned_clss_count S = learned_clss_count T\<close>
  by (cases S; cases T) (auto simp: learned_clss_count_def)

abbreviation twl_st_heur'''
   :: \<open>nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur''''u
   :: \<open>nat \<Rightarrow> nat \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''''u r u \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r \<and>
           learned_clss_count S \<le> u}\<close>

lemma twl_st_heur'''_twl_st_heur''''uD:
  \<open>(x, y) \<in> twl_st_heur''' r \<Longrightarrow>
  (x, y) \<in> twl_st_heur''''u r (learned_clss_count x)\<close>
  by auto

definition twl_st_heur' :: \<open>nat multiset \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur' N = {(S, S'). (S, S') \<in> twl_st_heur \<and> dom_m (get_clauses_wl S') = N}\<close>

definition twl_st_heur_conflict_ana
  :: \<open>(isasat \<times> nat twl_st_wl) set\<close>
where
[unfolded Let_def]: \<open>twl_st_heur_conflict_ana =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms_st T) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st T)) \<and>
    vm \<in> isa_vmtf (all_atms_st T) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms_st T) cach \<and>
    out_learned M D outl \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st T) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_atms_st T) \<and>
    isasat_input_nempty (all_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st T) heur
  }\<close>

lemma twl_st_heur_twl_st_heur_conflict_ana:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_conflict_ana\<close>
  by (cases S; cases T; auto simp: twl_st_heur_def twl_st_heur_conflict_ana_def Let_def ac_simps all_atms_st_def)

lemma twl_st_heur_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_conflict_ana\<close>
  shows
    \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
    \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_conflict_ana_def by (solves \<open>cases S; cases S'; auto simp: map_fun_rel_def ac_simps
    all_atms_st_def Let_def\<close>)+

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a
separate array.\<close>
definition twl_st_heur_bt :: \<open>(isasat \<times> nat twl_st_wl) set\<close> where
[unfolded Let_def]: \<open>twl_st_heur_bt =
  {(S, T).
  let M' = get_trail_wl_heur S; N' = get_clauses_wl_heur S; D' = get_conflict_wl_heur S;
    W' = get_watched_wl_heur S; j = literals_to_update_wl_heur S; outl = get_outlearned_heur S;
    cach = get_conflict_cach S; clvls = get_count_max_lvls_heur S;
    vm = get_vmtf_heur S;
    vdom = get_aivdom S; heur = get_heur S; old_arena = get_old_arena S;
    lcount = get_learned_count S in
    let M = get_trail_wl T; N = get_clauses_wl T;  D = get_conflict_wl T;
      Q = literals_to_update_wl T;
      W = get_watched_wl T; N0 = get_init_clauses0_wl T; U0 = get_learned_clauses0_wl T;
      NS = get_subsumed_init_clauses_wl T; US = get_subsumed_learned_clauses_wl T;
      NEk = get_kept_unit_init_clss_wl T; UEk = get_kept_unit_learned_clss_wl T;
      NE = get_unkept_unit_init_clss_wl T; UE = get_unkept_unit_learned_clss_wl T in
    (M', M) \<in> trail_pol (all_atms_st T) \<and>
    valid_arena N' N (set (get_vdom_aivdom vdom)) \<and>
    (D', None) \<in> option_lookup_clause_rel (all_atms_st T) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms_st T)) \<and>
    vm \<in> isa_vmtf (all_atms_st T) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty (all_atms_st T) cach \<and>
    out_learned M None outl \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    vdom_m (all_atms_st T) W N \<subseteq> set (get_vdom_aivdom vdom) \<and>
    aivdom_inv_dec vdom (dom_m N) \<and>
    isasat_input_bounded (all_atms_st T) \<and>
    isasat_input_nempty (all_atms_st T) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms_st T) heur
  }\<close>


text \<open>
  The difference between \<^term>\<open>isasat_unbounded_assn\<close> and \<^term>\<open>isasat_bounded_assn\<close> corresponds to the
  following condition:
\<close>
definition isasat_fast :: \<open>isasat \<Rightarrow> bool\<close> where
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

definition get_conflict_wl_is_None_heur :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur S = (\<lambda>(b, _). b) (get_conflict_wl_heur S)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def comp_def
  apply (intro WB_More_Refinement.frefI nres_relI) apply refine_rcg
  by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def Let_def
     split: option.splits prod.splits)

definition count_decided_st :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

definition isa_count_decided_st :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>isa_count_decided_st = count_decided_pol o get_trail_wl_heur\<close>

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o isa_count_decided_st, RETURN o count_decided_st) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro WB_More_Refinement.frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_heur_def isa_count_decided_st_def Let_def
       count_decided_trail_ref[THEN fref_to_Down_unRET_Id])


lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto

definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition atm_is_in_conflict_st_heur :: \<open>nat literal \<Rightarrow> isasat \<Rightarrow> bool nres\<close> where
  \<open>atm_is_in_conflict_st_heur L S = (\<lambda>(_, D). do {
     ASSERT (atm_in_conflict_lookup_pre (atm_of L) D); RETURN (\<not>atm_in_conflict_lookup (atm_of L) D) }) (get_conflict_wl_heur S)\<close>

lemma atm_is_in_conflict_st_heur_alt_def:
  \<open>atm_is_in_conflict_st_heur = (\<lambda>L S. case (get_conflict_wl_heur S) of (_, (_, D)) \<Rightarrow> do {ASSERT ((atm_of L) < length D); RETURN (D ! (atm_of L) = None)})\<close>
  unfolding atm_is_in_conflict_st_heur_def by (auto intro!: ext simp: atm_in_conflict_lookup_def atm_in_conflict_lookup_pre_def split:option.splits
    intro!: prod.case_cong)

(*TODO remove*)
lemmas atm_of_in_atms_of_iff = atm_of_in_atms_of

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
    mop_lit_notin_conflict_wl_def all_lits_st_alt_def Let_def
  apply (intro frefI nres_relI)
  apply refine_rcg
  apply clarsimp
  subgoal
     by (rule atm_in_conflict_lookup_pre)
  subgoal for x y x1 x2
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

definition count_decided_st_heur :: \<open>isasat \<Rightarrow> _\<close> where
   \<open>count_decided_st_heur S = count_decided_pol (get_trail_wl_heur S)\<close>

lemma twl_st_heur_count_decided_st_alt_def:
  fixes S :: isasat
  shows \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> count_decided_st_heur S = count_decided (get_trail_wl T)\<close>
  unfolding count_decided_st_def twl_st_heur_def trail_pol_def
  by (cases S) (auto simp: count_decided_st_heur_def count_decided_pol_def)

lemma twl_st_heur_isa_length_trail_get_trail_wl:
  fixes S :: isasat
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

lemma phase_saving_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> phase_saving \<A> heur \<Longrightarrow> phase_saving \<B> heur\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: phase_save_heur_rel_def phase_saving_def)

lemma phase_save_heur_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> phase_save_heur_rel \<A> heur \<Longrightarrow> phase_save_heur_rel \<B> heur\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (auto simp: phase_save_heur_rel_def phase_saving_def)

lemma heuristic_rel_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<B> heur\<close>
  using phase_save_heur_rel_cong[of \<A> \<B> \<open>(\<lambda>(_, _, _, _, a, _). a) (get_restart_heuristics heur)\<close>]
  using phase_saving_rel_cong[of \<A> \<B> \<open>(\<lambda>(_, _, _, _, _, _, _, a, _). a) (get_restart_heuristics heur)\<close>]
  by (auto simp: heuristic_rel_def heuristic_rel_stats_def)

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
      \<open>auto 5 5 simp: clause_not_marked_to_delete_def twl_st_heur_def Let_def
        clause_not_marked_to_delete_heur_def arena_dom_status_iff
        clause_not_marked_to_delete_pre_def ac_simps\<close>)


definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j).
           arena_lit_pre (get_clauses_wl_heur S) (i+j))\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = arena_lit (get_clauses_wl_heur S) (i + j)\<close>

definition (in -) mop_access_lit_in_clauses_heur where
  \<open>mop_access_lit_in_clauses_heur S i j = mop_arena_lit2 (get_clauses_wl_heur S) i j\<close>

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

definition rewatch_heur_vdom where
  \<open>rewatch_heur_vdom vdom = rewatch_heur (get_tvdom_aivdom vdom)\<close>

definition rewatch_heur_st
 :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>rewatch_heur_st = (\<lambda>S. do {
  ASSERT(length (get_tvdom_aivdom (get_aivdom S)) \<le> length (get_clauses_wl_heur S));
  W \<leftarrow> rewatch_heur (get_tvdom_aivdom (get_aivdom S)) (get_clauses_wl_heur S) (get_watched_wl_heur S);
  RETURN (set_watched_wl_heur W S)
  })\<close>

definition rewatch_heur_st_fast where
  \<open>rewatch_heur_st_fast = rewatch_heur_st\<close>

definition rewatch_heur_st_fast_pre where
  \<open>rewatch_heur_st_fast_pre S =
     ((\<forall>x \<in> set (get_tvdom S). x \<le> sint64_max) \<and> length (get_clauses_wl_heur S) \<le> sint64_max)\<close>

definition rewatch_st :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>rewatch_st S = do{
     (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) \<leftarrow> RETURN S;
     W \<leftarrow> rewatch N W;
     RETURN ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W))
  }\<close>

definition rewatch_heur_and_reorder_st
 :: \<open>isasat \<Rightarrow> isasat nres\<close>
where
\<open>rewatch_heur_and_reorder_st = (\<lambda>S. do {
  ASSERT(length (get_tvdom_aivdom (get_aivdom S)) \<le> length (get_clauses_wl_heur S));
  W \<leftarrow> rewatch_heur_and_reorder (get_tvdom_aivdom (get_aivdom S)) (get_clauses_wl_heur S) (get_watched_wl_heur S);
  RETURN (set_watched_wl_heur W S)
  })\<close>


fun remove_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>remove_watched_wl (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, _) = (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q)\<close>

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
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> clss_size \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur'' \<D> r lcount \<equiv> {(S, T). (S, T) \<in> twl_st_heur' \<D> \<and>
           length (get_clauses_wl_heur S) = r \<and> get_learned_count S = lcount}\<close>

abbreviation twl_st_heur_up''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> clss_size \<Rightarrow> (isasat \<times> nat twl_st_wl) set\<close>
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
      (auto simp: twl_st_heur_def twl_st_heur'_def aivdom_inv_dec_alt_def Let_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
    using x2 xb_x'a unfolding all_atms_def
    by auto

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur'_def twl_st_heur_def Let_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def ac_simps Let_def)

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
      (auto simp: twl_st_heur_def twl_st_heur'_def aivdom_inv_dec_alt_def)

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

definition mop_polarity_st_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
\<open>mop_polarity_st_heur S L = do {
    mop_polarity_pol (get_trail_wl_heur S) L
  }\<close>

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


definition length_avdom :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>length_avdom S = length (get_avdom S)\<close>

definition length_ivdom :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>length_ivdom S = length (get_ivdom S)\<close>

definition length_tvdom :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>length_tvdom S = length (get_tvdom S)\<close>

definition clause_is_learned_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> bool\<close>
where
  \<open>clause_is_learned_heur S C \<longleftrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED\<close>

definition get_the_propagation_reason_heur
 :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat option nres\<close>
where
  \<open>get_the_propagation_reason_heur S = get_the_propagation_reason_pol (get_trail_wl_heur S)\<close>

(* TODO deduplicate arena_lbd = get_clause_LBD *)
definition clause_lbd_heur :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat\<close>
where
  \<open>clause_lbd_heur S C = arena_lbd (get_clauses_wl_heur S) C\<close>

definition (in -) access_length_heur where
  \<open>access_length_heur S i = arena_length (get_clauses_wl_heur S) i\<close>

definition marked_as_used_st where
  \<open>marked_as_used_st T C =
    marked_as_used (get_clauses_wl_heur T) C\<close>

definition access_avdom_at :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_avdom_at S i = get_avdom S ! i\<close>

definition access_ivdom_at :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_ivdom_at S i = get_ivdom S ! i\<close>

definition access_tvdom_at :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_tvdom_at S i = get_tvdom S ! i\<close>

definition access_avdom_at_pre where
  \<open>access_avdom_at_pre S i \<longleftrightarrow> i < length (get_avdom S)\<close>

definition access_ivdom_at_pre where
  \<open>access_ivdom_at_pre S i \<longleftrightarrow> i < length (get_ivdom S)\<close>

definition access_tvdom_at_pre where
  \<open>access_tvdom_at_pre S i \<longleftrightarrow> i < length (get_tvdom S)\<close>

(*TODO check which of theses variants are used!*)
definition mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>S.
    let N' = extra_information_mark_to_delete (get_clauses_wl_heur S) C in
    let lcount = clss_size_decr_lcount (get_learned_count S) in
    let vdom = remove_inactive_aivdom i (get_aivdom S) in
    set_aivdom_wl_heur vdom (set_clauses_wl_heur N' (set_learned_count_wl_heur lcount S)))\<close>

definition mark_garbage_heur2 :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_garbage_heur2 C = (\<lambda>S. do{
    let N' = get_clauses_wl_heur S;
    let st = arena_status N' C = IRRED;
    let N' = extra_information_mark_to_delete N' C;
    let lcount = get_learned_count S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else clss_size_decr_lcount lcount);
    RETURN (set_clauses_wl_heur N' (set_learned_count_wl_heur lcount S))})\<close>

definition mark_garbage_heur3 :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>mark_garbage_heur3 C i = (\<lambda>S.
    let N' = get_clauses_wl_heur S in
    let N' = extra_information_mark_to_delete N' C in
    let lcount = get_learned_count S in
    let vdom = get_aivdom S in
    let vdom = remove_inactive_aivdom_tvdom i vdom in
    let lcount = clss_size_decr_lcount lcount in
    let S = set_clauses_wl_heur N' S in
    let S = set_learned_count_wl_heur lcount S in
    let S = set_aivdom_wl_heur vdom S in
    S)\<close>

definition mark_garbage_heur4 :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mark_garbage_heur4 C S = (do{
    let N' = get_clauses_wl_heur S;
    let st = arena_status N' C = IRRED;
    let N' = extra_information_mark_to_delete (N') C;
    let lcount = get_learned_count S;
    ASSERT(\<not>st \<longrightarrow> clss_size_lcount lcount \<ge> 1);
    let lcount = (if st then lcount else clss_size_incr_lcountUEk (clss_size_decr_lcount lcount));
    let stats = get_stats_heur S;
    let stats = (if st then decr_irred_clss stats else stats);
    let S = set_clauses_wl_heur N' S;
    let S = set_learned_count_wl_heur lcount S;
    let S = set_stats_wl_heur stats S;
    RETURN S
   })\<close>

definition delete_index_vdom_heur :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>delete_index_vdom_heur = (\<lambda>i S.
    let vdom = get_aivdom S in
    let vdom = remove_inactive_aivdom_tvdom i vdom in
    let S = set_aivdom_wl_heur vdom S in
    S)\<close>

lemma arena_act_pre_mark_used:
  \<open>arena_act_pre arena C \<Longrightarrow>
  arena_act_pre (mark_unused arena C) C\<close>
  unfolding arena_act_pre_def arena_is_valid_clause_idx_def
  apply clarify
  apply (rule_tac x=N in exI)
  apply (rule_tac x=vdom in exI)
  by (auto simp: arena_act_pre_def
    simp: valid_arena_mark_unused)

definition mop_mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mop_mark_garbage_heur C i = (\<lambda>S. do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur S, C) \<and> clss_size_lcount (get_learned_count S) \<ge> 1 \<and> i < length (get_avdom S));
    RETURN (mark_garbage_heur C i S)
  })\<close>

definition mop_mark_garbage_heur3 :: \<open>nat \<Rightarrow> nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mop_mark_garbage_heur3 C i = (\<lambda>S. do {
    ASSERT(mark_garbage_pre (get_clauses_wl_heur S, C) \<and> clss_size_lcount (get_learned_count S) \<ge> 1  \<and> i < length (get_tvdom S));
    RETURN (mark_garbage_heur3 C i S)
  })\<close>

definition mark_unused_st_heur :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>mark_unused_st_heur C = (\<lambda>S.
    let N' = mark_unused (get_clauses_wl_heur S) C in
    let S = set_clauses_wl_heur N' S in
    S)\<close>


definition mop_mark_unused_st_heur :: \<open>nat \<Rightarrow> isasat \<Rightarrow> isasat nres\<close> where
  \<open>mop_mark_unused_st_heur C T = do {
     ASSERT(arena_act_pre (get_clauses_wl_heur T) C);
     RETURN (mark_unused_st_heur C T)
  }\<close>

lemma mark_unused_st_heur_simp[simp]:
  \<open>get_avdom (mark_unused_st_heur C T) = get_avdom T\<close>
  \<open>get_vdom (mark_unused_st_heur C T) = get_vdom T\<close>
  \<open>get_ivdom (mark_unused_st_heur C T) = get_ivdom T\<close>
  \<open>get_tvdom (mark_unused_st_heur C T) = get_tvdom T\<close>
  by (cases T; auto simp: mark_unused_st_heur_def; fail)+

fun get_conflict_count_since_last_restart_heur :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_conflict_count_since_last_restart_heur S = get_conflict_count_since_last_restart (get_heur S)\<close>

definition get_global_conflict_count where
  \<open>get_global_conflict_count S = stats_conflicts (get_stats_heur S)\<close>

text \<open>
  I also played with \<^term>\<open>ema_reinit fast_ema\<close> and \<^term>\<open>ema_reinit slow_ema\<close>. Currently removed,
  to test the performance, I remove it.
\<close>
definition incr_restart_stat :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>incr_restart_stat = (\<lambda>S. do{
     let heur = get_heur S;
     let S = set_heur_wl_heur heur S;
     let stats = get_stats_heur S;
     let S = set_stats_wl_heur (incr_restart (stats)) S;
     RETURN S
  })\<close>

definition incr_lrestart_stat :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>S. do{
     let heur = get_heur S;
     let heur = heuristic_reluctant_untrigger (restart_info_restart_done_heur heur);
     let S = set_heur_wl_heur heur S;
     let stats = get_stats_heur S;
     let stats = incr_lrestart stats;
     let S = set_stats_wl_heur stats S;
     RETURN S
  })\<close>

definition incr_wasted_st :: \<open>64 word \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>incr_wasted_st = (\<lambda>waste S. do{
  let heur = get_heur S in
  let heur = incr_wasted waste heur in
  let S = set_heur_wl_heur heur S in S
  })\<close>


definition wasted_bytes_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>wasted_bytes_st S = wasted_of (get_heur S)\<close>


definition opts_restart_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>opts_restart_st S = opts_restart (get_opts S)\<close>

definition opts_reduction_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st S = opts_reduce (get_opts S)\<close>

definition opts_unbounded_mode_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>opts_unbounded_mode_st S = opts_unbounded_mode (get_opts S)\<close>

definition opts_minimum_between_restart_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>opts_minimum_between_restart_st S = opts_minimum_between_restart (get_opts S)\<close>

definition opts_restart_coeff1_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>opts_restart_coeff1_st S = opts_restart_coeff1 (get_opts S)\<close>

definition opts_restart_coeff2_st :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>opts_restart_coeff2_st S = opts_restart_coeff2 (get_opts S)\<close>

definition isasat_length_trail_st :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>isasat_length_trail_st S = isa_length_trail (get_trail_wl_heur S)\<close>

definition mop_isasat_length_trail_st :: \<open>isasat \<Rightarrow> nat nres\<close> where
  \<open>mop_isasat_length_trail_st S = do {
    ASSERT(isa_length_trail_pre (get_trail_wl_heur S));
    RETURN (isa_length_trail (get_trail_wl_heur S))
  }\<close>

definition get_pos_of_level_in_trail_imp_st :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
\<open>get_pos_of_level_in_trail_imp_st S = get_pos_of_level_in_trail_imp (get_trail_wl_heur S)\<close>

definition mop_clause_not_marked_to_delete_heur :: \<open>_ \<Rightarrow> nat \<Rightarrow> bool nres\<close>
where
  \<open>mop_clause_not_marked_to_delete_heur S C = do {
    ASSERT(clause_not_marked_to_delete_heur_pre (S, C));
    RETURN (clause_not_marked_to_delete_heur S C)
  }\<close>

definition mop_arena_lbd_st where
  \<open>mop_arena_lbd_st S =
    mop_arena_lbd (get_clauses_wl_heur S)\<close>

definition mop_arena_status_st :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>mop_arena_status_st S =
    mop_arena_status (get_clauses_wl_heur S)\<close>

definition mop_marked_as_used_st :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_marked_as_used_st S =
    mop_marked_as_used (get_clauses_wl_heur S)\<close>

definition mop_arena_length_st :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>mop_arena_length_st S =
    mop_arena_length (get_clauses_wl_heur S)\<close>

definition full_arena_length_st :: \<open>isasat \<Rightarrow> nat\<close> where
  \<open>full_arena_length_st S = length (get_clauses_wl_heur S)\<close>

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) \<propto> i ! j\<close>

lemma twl_st_heur_get_clauses_access_lit[simp]:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> C \<in># dom_m (get_clauses_wl T) \<Longrightarrow>
    i < length (get_clauses_wl T \<propto> C) \<Longrightarrow>
    get_clauses_wl T \<propto> C ! i = access_lit_in_clauses_heur S C i\<close>
    for S T C i
    by (cases S; cases T)
      (auto simp: arena_lifting twl_st_heur_def access_lit_in_clauses_heur_def)


abbreviation length_clauses_heur where
  \<open>length_clauses_heur \<equiv> full_arena_length_st\<close>

lemmas length_clauses_heur_def = full_arena_length_st_def

text \<open>In an attempt to avoid using @{thm ac_simps} everywhere.\<close>
lemma all_lits_simps[simp]:
  \<open>all_lits N ((NE + UE) + (NS + US)) = all_lits N (NE + UE + NS + US)\<close>
  \<open>all_atms N ((NE + UE) + (NS + US)) = all_atms N (NE + UE + NS + US)\<close>
  by (auto simp: ac_simps)

lemma learned_clss_count_twl_st_heur: \<open>(T, Ta) \<in> twl_st_heur \<Longrightarrow>
                      learned_clss_count T=
                      size (get_learned_clss_wl Ta) +
                      size (get_unit_learned_clss_wl Ta) +
                     size (get_subsumed_learned_clauses_wl Ta) +
                     size (get_learned_clauses0_wl Ta)\<close>
  by (auto simp: twl_st_heur_def clss_size_def learned_clss_count_def clss_size_corr_def
    clss_size_lcount_def clss_size_lcountUE_def clss_size_lcountUS_def clss_size_lcountUEk_def
    get_learned_clss_wl_def clss_size_lcountU0_def get_unit_learned_clss_wl_alt_def)

lemma clss_size_allcount_alt_def:
  \<open>clss_size_allcount S = clss_size_lcountUS S + clss_size_lcountU0 S + clss_size_lcountUE S + 
    clss_size_lcountUEk S + clss_size_lcount S\<close>
  by (cases S) (auto simp: clss_size_allcount_def clss_size_lcountUS_def
    clss_size_lcount_def clss_size_lcountUEk_def clss_size_lcountUE_def clss_size_lcountU0_def)

definition isasat_trail_nth_st :: \<open>isasat \<Rightarrow> nat \<Rightarrow> nat literal nres\<close> where
\<open>isasat_trail_nth_st S i = isa_trail_nth (get_trail_wl_heur S) i\<close>

definition get_the_propagation_reason_pol_st :: \<open>isasat\<Rightarrow> nat literal \<Rightarrow> nat option nres\<close> where
\<open>get_the_propagation_reason_pol_st S i = get_the_propagation_reason_pol (get_trail_wl_heur S) i\<close>

definition empty_US_heur :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>empty_US_heur S =
  (let lcount = get_learned_count S in
  let lcount = clss_size_resetUS0 lcount in
  let S = set_learned_count_wl_heur lcount S in S
  )\<close>

lemma get_clauses_wl_heur_empty_US[simp]:
    \<open>get_clauses_wl_heur (empty_US_heur xc) = get_clauses_wl_heur xc\<close> and
  get_vdom_empty_US[simp]:
    \<open>get_vdom (empty_US_heur xc) = get_vdom xc\<close>
    \<open>get_avdom (empty_US_heur xc) = get_avdom xc\<close>
    \<open>get_ivdom (empty_US_heur xc) = get_ivdom xc\<close>
    \<open>get_tvdom (empty_US_heur xc) = get_tvdom xc\<close>
  by (cases xc; auto simp: empty_US_heur_def; fail)+

definition empty_Q_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_Q_wl = (\<lambda>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, _, W). (M', N, D, NE, UE, NEk, UEk, NS, {#}, N0, {#}, {#}, W))\<close>

definition empty_Q_wl2  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_Q_wl2 = (\<lambda>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, _, W). (M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, {#}, W))\<close>

definition empty_US_heur_wl  :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
\<open>empty_US_heur_wl = (\<lambda>(M', N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W). (M', N, D, NE, UE, NEk, UEk, NS, {#}, N0, {#}, Q, W))\<close>

lemma restart_info_of_stats_simp [simp]: \<open>restart_info_of_stats (incr_wasted_stats C heur) = restart_info_of_stats heur\<close>
  by (cases heur; auto; fail)+

lemma incr_wasted_st_twl_st[simp]:
  \<open>get_aivdom (incr_wasted_st b T) = get_aivdom T\<close>
  \<open>get_avdom (incr_wasted_st w T) = get_avdom T\<close>
  \<open>get_vdom (incr_wasted_st w T) = get_vdom T\<close>
  \<open>get_ivdom (incr_wasted_st w T) = get_ivdom T\<close>
  \<open>get_tvdom (incr_wasted_st w T) = get_tvdom T\<close>
  \<open>get_trail_wl_heur (incr_wasted_st w T) = get_trail_wl_heur T\<close>
  \<open>get_clauses_wl_heur (incr_wasted_st C T) = get_clauses_wl_heur T\<close>
  \<open>get_conflict_wl_heur (incr_wasted_st C T) = get_conflict_wl_heur T\<close>
  \<open>get_learned_count (incr_wasted_st C T) = get_learned_count T\<close>
  \<open>get_conflict_count_heur (incr_wasted_st C T) = get_conflict_count_heur T\<close>
  \<open>literals_to_update_wl_heur (incr_wasted_st C T) = literals_to_update_wl_heur T\<close>
  \<open>get_watched_wl_heur (incr_wasted_st C T) = get_watched_wl_heur T\<close>
  \<open>get_vmtf_heur (incr_wasted_st C T) = get_vmtf_heur T\<close>
  \<open>get_count_max_lvls_heur (incr_wasted_st C T) = get_count_max_lvls_heur T\<close>
  \<open>get_conflict_cach (incr_wasted_st C T) = get_conflict_cach T\<close>
  \<open>get_lbd (incr_wasted_st C T) = get_lbd T\<close>
  \<open>get_outlearned_heur (incr_wasted_st C T) = get_outlearned_heur T\<close>
  \<open>get_aivdom (incr_wasted_st C T) = get_aivdom T\<close>
  \<open>get_learned_count (incr_wasted_st C T) = get_learned_count T\<close>
  \<open>get_opts (incr_wasted_st C T) = get_opts T\<close>
  \<open>get_old_arena (incr_wasted_st C T) = get_old_arena T\<close>
  by (cases T; auto simp: incr_wasted_st_def incr_wasted_def restart_info_of_def; fail)+

definition heuristic_reluctant_triggered2_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>heuristic_reluctant_triggered2_st S = heuristic_reluctant_triggered2 (get_heur S)\<close>

definition heuristic_reluctant_untrigger_st :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>heuristic_reluctant_untrigger_st S =
  (let heur = get_heur S;
    heur = heuristic_reluctant_untrigger heur;
    S = set_heur_wl_heur heur S in
  S)\<close>

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

definition (in -) lit_of_hd_trail_st_heur :: \<open>isasat \<Rightarrow> nat literal nres\<close> where
  \<open>lit_of_hd_trail_st_heur S = do {
     ASSERT (fst (get_trail_wl_heur S) \<noteq> []);
     RETURN (lit_of_last_trail_pol (get_trail_wl_heur S))
  }\<close>

subsection \<open>Lifting of Options\<close>

definition get_target_opts :: \<open>isasat \<Rightarrow> opts_target\<close> where
  \<open>get_target_opts S = opts_target (get_opts S)\<close>

definition get_GC_units_opt :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_GC_units_opt S = opts_GC_units_lim (get_opts S)\<close>

definition units_since_last_GC_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>units_since_last_GC_st S = units_since_last_GC (get_stats_heur S)\<close>

definition units_since_beginning_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>units_since_beginning_st S = units_since_beginning (get_stats_heur S)\<close>

definition reset_units_since_last_GC_st :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>reset_units_since_last_GC_st S =
  (let stats = get_stats_heur S in
  let stats = reset_units_since_last_GC stats in
  let S = set_stats_wl_heur stats S in S
  )\<close>

(*TODO identical to empty_US_heur*)
definition clss_size_resetUS0_st :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>clss_size_resetUS0_st S =
  (let lcount = get_learned_count S in
  let lcount = clss_size_resetUS0 lcount in
  let S = set_learned_count_wl_heur lcount S in S
  )\<close>

definition is_fully_propagated_heur_st :: \<open>isasat \<Rightarrow> bool\<close> where
  \<open>is_fully_propagated_heur_st S = is_fully_propagated_heur (get_heur S)\<close>

definition print_trail_st :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>print_trail_st = (\<lambda>S. print_trail (get_trail_wl_heur S))\<close>

definition print_trail_st2 where
  \<open>print_trail_st2 _ = ()\<close>

lemma print_trail_st_print_trail_st2:
  \<open>print_trail_st S \<le> \<Down>unit_rel (RETURN (print_trail_st2 S))\<close>
  unfolding print_trail_st2_def print_trail_st_def
    print_trail_def
  apply (refine_vcg WHILET_rule[where
       R = \<open>measure (\<lambda>i. Suc (length (fst (get_trail_wl_heur S))) - i)\<close> and
       I = \<open>\<lambda>i. i \<le> length (fst (get_trail_wl_heur S))\<close>])
  subgoal by auto
  subgoal by auto
  subgoal unfolding print_literal_of_trail_def by auto
  subgoal unfolding print_literal_of_trail_def by auto
  done

lemma print_trail_st_print_trail_st2_rel:
  \<open>(print_trail_st, RETURN o print_trail_st2) \<in> Id \<rightarrow>\<^sub>f (\<langle>unit_rel\<rangle>nres_rel)\<close>
  using print_trail_st_print_trail_st2 by (force intro!: frefI nres_relI)

named_theorems isasat_state_simp

lemma [isasat_state_simp]:
  \<open>learned_clss_count (Tuple16.set_p old_arena S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_o opts S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_n lcount S) = learned_clss_count_lcount lcount\<close>
  \<open>learned_clss_count (Tuple16.set_m aivdom S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_l heur S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_k stats S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_j outl S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_i lbd S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_h ccach S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_g count' S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_f vmtf' S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_e W S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_d j S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_c D S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_b N S) = learned_clss_count S\<close>
  \<open>learned_clss_count (Tuple16.set_a M S) = learned_clss_count S\<close>
  \<open>get_trail_wl_heur (set_learned_count_wl_heur lcount S) = get_trail_wl_heur S\<close>
  \<open>get_clauses_wl_heur (set_learned_count_wl_heur lcount S) = get_clauses_wl_heur S\<close>
  \<open>get_conflict_wl_heur (set_learned_count_wl_heur lcount S) = get_conflict_wl_heur S\<close>
  \<open>literals_to_update_wl_heur (set_learned_count_wl_heur lcount S) = literals_to_update_wl_heur S\<close>
  \<open>get_watched_wl_heur (set_learned_count_wl_heur lcount S) = get_watched_wl_heur S\<close>
  \<open>get_vmtf_heur (set_learned_count_wl_heur lcount S) = get_vmtf_heur S\<close>
  \<open>get_count_max_lvls_heur (set_learned_count_wl_heur lcount S) = get_count_max_lvls_heur S\<close>
  \<open>get_conflict_cach (set_learned_count_wl_heur lcount S) = get_conflict_cach S\<close>
  \<open>get_lbd (set_learned_count_wl_heur lcount S) = get_lbd S\<close>
  \<open>get_outlearned_heur (set_learned_count_wl_heur lcount S) = get_outlearned_heur S\<close>
  \<open>get_stats_heur (set_learned_count_wl_heur lcount S) = get_stats_heur S\<close>
  \<open>get_aivdom (set_learned_count_wl_heur lcount S) = get_aivdom S\<close>
  \<open>get_heur (set_learned_count_wl_heur lcount S) = get_heur S\<close>
  \<open>get_learned_count (set_learned_count_wl_heur lcount S) = lcount\<close>
  \<open>get_opts (set_learned_count_wl_heur lcount S) = get_opts S\<close>
  \<open>get_old_arena (set_learned_count_wl_heur lcount S) = get_old_arena S\<close>
  by (solves \<open>cases S; auto simp: learned_clss_count_def\<close>)+

lemmas [isasat_state_simp] = tuple16_state_simp
lemmas [simp] = isasat_state_simp


(*TODO Move*)
definition (in -) length_ll_fs_heur :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur S L = length (watched_by_int S L)\<close>

definition (in -) length_watchlist :: \<open>nat watcher list list \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_watchlist S L = length_ll S (nat_of_lit L)\<close>

definition mop_length_watched_by_int :: \<open>isasat \<Rightarrow> nat literal \<Rightarrow> nat nres\<close> where
  \<open>mop_length_watched_by_int S L = do {
     ASSERT(nat_of_lit L < length (get_watched_wl_heur S));
     RETURN (length (watched_by_int S L))
}\<close>

definition end_of_rephasing_phase_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>end_of_rephasing_phase_st = (\<lambda>S. end_of_rephasing_phase_heur (get_heur S))\<close>

definition end_of_restart_phase_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
 \<open>end_of_restart_phase_st = (\<lambda>S. end_of_restart_phase (get_heur S))\<close>


definition get_vmtf_heur_array where
  \<open>get_vmtf_heur_array S = fst (fst (get_vmtf_heur S))\<close>
definition get_vmtf_heur_fst where
  \<open>get_vmtf_heur_fst S = (fst o snd o snd) (fst (get_vmtf_heur S))\<close>

definition mop_mark_added_heur_st :: \<open>_\<close> where
  \<open>mop_mark_added_heur_st L S = do {
    let heur = get_heur S;
    heur \<leftarrow> mop_mark_added_heur L True heur;
    RETURN (set_heur_wl_heur heur S)
  } \<close>

definition mark_added_clause_heur2 where
  \<open>mark_added_clause_heur2 S C = do {
     i \<leftarrow> mop_arena_length_st S C;
     ASSERT (i \<le> length (get_clauses_wl_heur S));
     (_, S) \<leftarrow> WHILE\<^sub>T (\<lambda>(j, S). j < i)
       (\<lambda>(j, S). do {
          ASSERT (j<i);
          L \<leftarrow> mop_access_lit_in_clauses_heur S C j;
          S \<leftarrow> mop_mark_added_heur_st (atm_of L) S;
          RETURN (j+1, S)
        })
      (0, S);
    RETURN S
  }\<close>

definition mark_added_clause2 where
  \<open>mark_added_clause2 S C = do {
     i \<leftarrow> RETURN (length (get_clauses_wl S \<propto> C));
     (_, S) \<leftarrow> WHILE\<^sub>T\<^bsup> \<lambda>(j, T). j \<le> i \<and> T = S\<^esup> (\<lambda>(j, S). j < i)
       (\<lambda>(j, S). do {
          ASSERT (j<i);
          L \<leftarrow> mop_clauses_at (get_clauses_wl S) C j;
          ASSERT (L \<in> set (get_clauses_wl S \<propto> C));
          let S = S;
          RETURN (j+1, S)
        })
      (0, S);
    RETURN S
  }\<close>


lemma mop_mark_added_heur_st_it:
  assumes \<open>(S,T) \<in> twl_st_heur\<close> and \<open>A \<in># all_atms_st T\<close>
  shows \<open>mop_mark_added_heur_st A S \<le> SPEC (\<lambda>c. (c, T) \<in> {(U, V). (U, V) \<in> twl_st_heur \<and> (get_clauses_wl_heur U) = get_clauses_wl_heur S \<and>
       learned_clss_count U = learned_clss_count S})\<close>
proof -
  have heur: \<open>heuristic_rel (all_atms_st T) (get_heur S)\<close>
    using assms(1)
    by (auto simp: twl_st_heur_def)

  show ?thesis
    unfolding mop_mark_added_heur_st_def mop_mark_added_heur_def
    apply refine_vcg
    subgoal
      using heur assms(2)
      unfolding mark_added_heur_pre_def mark_added_heur_pre_stats_def
      by (auto simp: heuristic_rel_def heuristic_rel_stats_def
        phase_saving_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits atms_of_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
        dest!: multi_member_split)
    subgoal by (use assms in \<open>auto simp add: twl_st_heur_def\<close>)
    done
qed

lemma mark_added_clause_heur2_id:
  assumes \<open>(S,T) \<in> twl_st_heur\<close> and \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  shows \<open>mark_added_clause_heur2 S C
     \<le> \<Down>{(U, V). (U, V) \<in> twl_st_heur \<and> (get_clauses_wl_heur U) = get_clauses_wl_heur S \<and>
       learned_clss_count U = learned_clss_count S} (RETURN T)\<close> (is \<open>_ \<le>\<Down>?R _\<close>)
proof -
  have 1: \<open>mark_added_clause2 T C \<le> \<Down>Id (RETURN T)\<close>
    unfolding mark_added_clause2_def mop_clauses_at_def nres_monad3
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i,_). length (get_clauses_wl T \<propto> C) -i)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (use assms in auto)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  have [refine]: \<open>y' \<in># dom_m x' \<Longrightarrow>
    ((x, y), x', y') \<in> {(N, N'). valid_arena N N' (set (get_vdom S))} \<times>\<^sub>f nat_rel \<Longrightarrow>
    mop_arena_length x y \<le> SPEC (\<lambda>y. (y, length (x' \<propto> y')) \<in> {(a,b). (a,b)\<in>nat_rel \<and> a = length (x' \<propto> y')})\<close> for x y x' y'
    apply (rule mop_arena_length[THEN fref_to_Down_curry, of _ _ _ _ \<open>set (get_vdom S)\<close>, unfolded comp_def conc_fun_RETURN prod.simps, THEN order_trans])
    apply assumption
    apply assumption
    by auto
  have [refine]: \<open>((0, S), 0, T) \<in> nat_rel \<times>\<^sub>r ?R\<close>
    using assms by auto
  have 2: \<open>mark_added_clause_heur2 S C \<le> \<Down>?R (mark_added_clause2 T C)\<close>
    unfolding mark_added_clause_heur2_def mop_arena_length_st_def mop_access_lit_in_clauses_heur_def
      mark_added_clause2_def
    apply (refine_vcg mop_mark_added_heur_st_it)
    subgoal by (use assms in auto)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_def\<close>)
    subgoal using assms by (auto simp: twl_st_heur_def dest: arena_lifting(10))
    subgoal by auto
    subgoal by auto
    apply (rule_tac vdom = \<open>set (get_vdom (x2a))\<close> in mop_arena_lit2)
    subgoal by (use assms in \<open>auto simp: twl_st_heur_def\<close>)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (use assms in \<open>auto simp: all_atms_st_def all_atms_def all_lits_def ran_m_def
        all_lits_of_mm_add_mset image_Un atm_of_all_lits_of_m(2)
      dest!: multi_member_split\<close>)
    subgoal by auto
    subgoal by auto
    done
  show ?thesis
    unfolding mop_arena_length_st_def mop_access_lit_in_clauses_heur_def
    apply (rule order_trans[OF 2])
    apply (rule ref_two_step')
    apply (rule 1[unfolded Down_id_eq])
    done
qed

definition mop_is_marked_added_heur_st where
  \<open>mop_is_marked_added_heur_st S = mop_is_marked_added_heur (get_heur S)\<close>

lemma is_marked_added_heur_st_it:
  assumes \<open>(S,T) \<in> twl_st_heur\<close> and \<open>A \<in># all_atms_st T\<close>
  shows \<open>mop_is_marked_added_heur_st S A \<le> SPEC(\<lambda>c. (c, d) \<in> (UNIV :: (bool \<times> bool) set))\<close>
proof -
  have heur: \<open>heuristic_rel (all_atms_st T) (get_heur S)\<close>
    using assms(1)
    by (auto simp: twl_st_heur_def)
  then have \<open>is_marked_added_heur_pre (get_heur S) A\<close>
    using assms
    unfolding is_marked_added_heur_pre_def
    by (auto simp: heuristic_rel_def is_marked_added_heur_pre_stats_def
      heuristic_rel_stats_def phase_saving_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
  then show ?thesis
    unfolding mop_is_marked_added_heur_st_def mop_is_marked_added_heur_def
    by auto
qed

definition schedule_next_inprocessing_st :: \<open>isasat \<Rightarrow> isasat\<close> where
  \<open>schedule_next_inprocessing_st S = set_heur_wl_heur (schedule_next_inprocessing (get_heur S)) S\<close>

definition next_inprocessing_schedule_st :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>next_inprocessing_schedule_st S = next_inprocessing_schedule (get_heur S)\<close>

definition schedule_info_of_st :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>schedule_info_of_st S = schedule_info_of (get_heur S)\<close>

definition schedule_next_reduce_st :: \<open>64 word \<Rightarrow> isasat \<Rightarrow> isasat\<close> where
  \<open>schedule_next_reduce_st b S = set_heur_wl_heur (schedule_next_reduce b (get_heur S)) S\<close>

definition next_reduce_schedule_st :: \<open>isasat \<Rightarrow> _\<close> where
  \<open>next_reduce_schedule_st S = next_reduce_schedule (get_heur S)\<close>

(*TODO move/deduplicate*)
lemma avdom_delete_index_vdom_heur[simp]:
  \<open>get_avdom (delete_index_vdom_heur i S) =  (get_avdom S)\<close>
  \<open>get_tvdom (delete_index_vdom_heur i S) = delete_index_and_swap (get_tvdom S) i\<close>
  by (cases S; auto simp: delete_index_vdom_heur_def; fail)+
lemma [simp]:
  \<open>learned_clss_count (delete_index_vdom_heur C T) = learned_clss_count T\<close>
  \<open>learned_clss_count (mark_unused_st_heur C T) = learned_clss_count T\<close>
  by (cases T; auto simp: learned_clss_count_def delete_index_vdom_heur_def
    mark_unused_st_heur_def; fail)+

lemma get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C i S) = get_vdom S\<close>
  \<open>get_avdom (mark_garbage_heur C i S) = delete_index_and_swap (get_avdom S) i\<close>
  \<open>get_ivdom (mark_garbage_heur C i S) = get_ivdom S\<close>
  \<open>get_tvdom (mark_garbage_heur C i S) = get_tvdom S\<close>
  \<open>get_tvdom (mark_garbage_heur3 C i S) = delete_index_and_swap (get_tvdom S) i\<close>
  \<open>get_ivdom (mark_garbage_heur3 C i S) = get_ivdom S\<close>
  \<open>get_vdom (mark_garbage_heur3 C i S) = get_vdom S\<close>
  \<open>learned_clss_count (mark_garbage_heur3 C i (S)) \<le> learned_clss_count S\<close>
  \<open>learned_clss_count (mark_garbage_heur3 C i (incr_wasted_st b S)) \<le> learned_clss_count S\<close>
  by (cases S; auto simp: mark_garbage_heur_def mark_garbage_heur3_def
   learned_clss_count_def incr_wasted_st_def; fail)+

fun get_reductions_count :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_reductions_count S = get_lrestart_count (get_stats_heur S)\<close>

definition get_irredundant_count_st :: \<open>isasat \<Rightarrow> 64 word\<close> where
  \<open>get_irredundant_count_st S = get_irredundant_count (get_stats_heur S)\<close>

end
