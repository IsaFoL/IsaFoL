theory IsaSAT_Setup
  imports IsaSAT_Clauses IsaSAT_Arena
    Watched_Literals_VMTF IsaSAT_Lookup_Conflict LBD IsaSAT_Watch_List
    Watched_Literals.Watched_Literals_Watch_List_Initialisation
begin

text \<open>TODO Move and make sure to merge in the right order!\<close>
no_notation Ref.update ("_ := _" 62)


subsection \<open>Code Generation\<close>

text \<open>We here define the last step of our refinement: the step with all the heuristics and fully
  deterministic code.

  After the result of benchmarking, we concluded that the us of \<^typ>\<open>nat\<close> leads to worse performance
  than using \<^typ>\<open>uint64\<close>. As, however, the later is not complete, we do so with a switch: as long
  as it fits, we use the faster (called 'bounded') version. After that we switch to the 'unbounded'
  version (which is still bounded by memory anyhow).

  We do keep some natural numbers:
  \<^enum> to iterate over the watch list. Our invariant are currently not strong enough to prove that
    we do not need that.
  \<^enum> to keep the indices of all clauses. This mostly simplifies the code if we add inprocessing:
    We can be sure to never have to switch mode in the middle of an operation (which would nearly
    impossible to do).
\<close>

subsubsection \<open>Types and Refinement Relations\<close>

paragraph \<open>Statistics\<close>

text \<open>
We do some statistics on the run.

NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions, do some comparisons (e.g., to conclude that
we are propagating slower than the other solvers), or to test different option combination.
\<close>
type_synonym stats = \<open>uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64\<close>

abbreviation stats_assn :: \<open>stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_assn \<equiv> uint64_assn *a uint64_assn *a uint64_assn *a uint64_assn *a uint64_assn
     *a uint64_assn *a uint64_assn *a uint64_assn\<close>

definition incr_propagation :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_propagation = (\<lambda>(propa, confl, dec). (propa + 1, confl, dec))\<close>

definition incr_conflict :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_conflict = (\<lambda>(propa, confl, dec). (propa, confl + 1, dec))\<close>

definition incr_decision :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_decision = (\<lambda>(propa, confl, dec, res). (propa, confl, dec + 1, res))\<close>

definition incr_restart :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_restart = (\<lambda>(propa, confl, dec, res, lres). (propa, confl, dec, res + 1, lres))\<close>

definition incr_lrestart :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_lrestart = (\<lambda>(propa, confl, dec, res, lres, uset). (propa, confl, dec, res, lres + 1, uset))\<close>

definition incr_uset :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_uset = (\<lambda>(propa, confl, dec, res, lres, (uset, gcs)). (propa, confl, dec, res, lres, uset + 1, gcs))\<close>

definition incr_GC :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_GC = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, lbds). (propa, confl, dec, res, lres, uset, gcs + 1, lbds))\<close>

definition add_lbd :: \<open>uint64 \<Rightarrow> stats \<Rightarrow> stats\<close> where
  \<open>add_lbd lbd = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, lbds). (propa, confl, dec, res, lres, uset, gcs, lbd + lbds))\<close>

lemma incr_propagation_hnr[sepref_fr_rules]:
    \<open>(return o incr_propagation, RETURN o incr_propagation) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_propagation_def)

lemma incr_conflict_hnr[sepref_fr_rules]:
    \<open>(return o incr_conflict, RETURN o incr_conflict) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_conflict_def)

lemma incr_decision_hnr[sepref_fr_rules]:
    \<open>(return o incr_decision, RETURN o incr_decision) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_decision_def)

lemma incr_restart_hnr[sepref_fr_rules]:
    \<open>(return o incr_restart, RETURN o incr_restart) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_restart_def)

lemma incr_lrestart_hnr[sepref_fr_rules]:
    \<open>(return o incr_lrestart, RETURN o incr_lrestart) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_lrestart_def)

lemma incr_uset_hnr[sepref_fr_rules]:
    \<open>(return o incr_uset, RETURN o incr_uset) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_uset_def)

lemma incr_GC_hnr[sepref_fr_rules]:
    \<open>(return o incr_GC, RETURN o incr_GC) \<in> stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_GC_def)

lemma add_lbd_hnr[sepref_fr_rules]:
    \<open>(uncurry (return oo add_lbd), uncurry (RETURN oo add_lbd)) \<in> uint64_assn\<^sup>k *\<^sub>a stats_assn\<^sup>d \<rightarrow>\<^sub>a stats_assn\<close>
  by sepref_to_hoare (sep_auto simp: add_lbd_def)


paragraph \<open>Moving averages\<close>

text \<open>We use (at least hopefully) the variant of EMA-14 implemented in Cadical, but with fixed-point
calculation (\<^term>\<open>1 :: nat\<close> is \<^term>\<open>(1 :: nat) >> 32\<close>).

Remark that the coefficient \<^term>\<open>\<beta>\<close> already should not take care of the fixed-point conversion of the glue.
Otherwise, \<^term>\<open>value\<close> is wrongly updated.
\<close>
type_synonym ema = \<open>uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64\<close>

abbreviation ema_assn :: \<open>ema \<Rightarrow> ema \<Rightarrow> assn\<close> where
  \<open>ema_assn \<equiv> uint64_assn *a uint64_assn *a uint64_assn *a uint64_assn *a uint64_assn\<close>

definition ema_bitshifting where
  \<open>ema_bitshifting = (1 << 32)\<close>

sepref_register ema_bitshifting

lemma ema_bitshifting_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return 4294967296), uncurry0 (RETURN ema_bitshifting)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
proof -
  have [simp]: \<open>Suc 0 << 32 = 4294967296\<close>
    by eval
  show ?thesis
    unfolding ema_bitshifting_def
    by sepref_to_hoare
      (sep_auto simp: uint64_nat_rel_def br_def ema_bitshifting_def
         nat_of_uint64_1_32 uint32_max_def)
qed

lemma ema_bitshifting_hnr2[sepref_fr_rules]:
  \<open>(uncurry0 (return 4294967296), uncurry0 (RETURN ema_bitshifting)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
proof -
  have [simp]: \<open>(1::uint64) << 32 = 4294967296\<close>
    by eval
  show ?thesis
    unfolding ema_bitshifting_def
    by sepref_to_hoare
      (sep_auto simp: uint64_nat_rel_def br_def ema_bitshifting_def
         nat_of_uint64_1_32 uint32_max_def)
qed

definition (in -) ema_update :: \<open>nat \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = (uint64_of_nat lbd) * ema_bitshifting in
     let value = if lbd > value then value + (\<beta> * (lbd - value) >> 32) else value - (\<beta> * (value - lbd) >> 32) in
     if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait - 1, period)
     else
       let wait = 2 * period + 1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

definition (in -) ema_update_ref :: \<open>uint32 \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update_ref = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = (uint64_of_uint32 lbd) * ema_bitshifting in
     let value = if lbd > value then value + (\<beta> * (lbd - value) >> 32) else value - (\<beta> * (value - lbd) >> 32) in
     if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait - 1, period)
     else
       let wait = 2 * period + 1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

lemma (in -) ema_update_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo ema_update_ref), uncurry (RETURN oo ema_update)) \<in>
      uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_update_def ema_update_ref_def
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def uint64_of_uint32_def Let_def)

definition (in -) ema_init :: \<open>uint64 \<Rightarrow> ema\<close> where
  \<open>ema_init \<alpha> = (0, \<alpha>, ema_bitshifting, 0, 0)\<close>

fun ema_reinit where
  \<open>ema_reinit (value, \<alpha>, \<beta>, wait, period) = (value, \<alpha>, 1 << 32, 0, 0)\<close>

lemma ema_reinit_hnr[sepref_fr_rules]:
  \<open>(return o ema_reinit, RETURN o ema_reinit) \<in> ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  by sepref_to_hoare sep_auto

fun ema_get_value :: \<open>ema \<Rightarrow> uint64\<close> where
  \<open>ema_get_value (v, _) = v\<close>

lemma ema_get_value_hnr[sepref_fr_rules]:
  \<open>(return o ema_get_value, RETURN o ema_get_value) \<in> ema_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

lemma (in -) ema_init_coeff_hnr[sepref_fr_rules]:
  \<open>(return o ema_init, RETURN o ema_init) \<in> uint64_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: ema_init_def uint64_nat_rel_def br_def)


text \<open>We use the default values for Cadical: \<^term>\<open>(3 / 10 ^2)\<close> and  \<^term>\<open>(1 / 10 ^ 5)\<close>  in our fixed-point
  version.
\<close>

abbreviation ema_fast_init :: ema where
  \<open>ema_fast_init \<equiv> ema_init (128849010)\<close>

abbreviation ema_slow_init :: ema where
  \<open>ema_slow_init \<equiv> ema_init 429450\<close>


paragraph \<open>Information related to restarts\<close>

type_synonym restart_info = \<open>uint64 \<times> uint64\<close>

abbreviation restart_info_assn where
  \<open>restart_info_assn \<equiv> uint64_assn *a uint64_assn\<close>

definition incr_conflict_count_since_last_restart :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>incr_conflict_count_since_last_restart = (\<lambda>(ccount, ema_lvl). (ccount + 1, ema_lvl))\<close>

lemma incr_conflict_count_since_last_restart_hnr[sepref_fr_rules]:
    \<open>(return o incr_conflict_count_since_last_restart, RETURN o incr_conflict_count_since_last_restart)
       \<in> restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_conflict_count_since_last_restart_def)

definition restart_info_update_lvl_avg :: \<open>uint32 \<Rightarrow> restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_update_lvl_avg = (\<lambda>lvl (ccount, ema_lvl). (ccount, ema_lvl))\<close>

lemma restart_info_update_lvl_avg_hnr[sepref_fr_rules]:
    \<open>(uncurry (return oo restart_info_update_lvl_avg),
       uncurry (RETURN oo restart_info_update_lvl_avg))
       \<in> uint32_assn\<^sup>k *\<^sub>a restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_update_lvl_avg_def)

definition restart_info_init :: \<open>restart_info\<close> where
  \<open>restart_info_init = (0, 0)\<close>

lemma restart_info_init_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return restart_info_init),
       uncurry0 (RETURN restart_info_init))
       \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_init_def)


definition restart_info_restart_done :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_restart_done = (\<lambda>(ccount, lvl_avg). (0, lvl_avg))\<close>

lemma restart_info_restart_done_hnr[sepref_fr_rules]:
  \<open>(return o restart_info_restart_done, RETURN o restart_info_restart_done) \<in>
     restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_restart_done_def
    uint64_nat_rel_def br_def)


paragraph \<open>VMTF\<close>

type_synonym vmtf_assn = \<open>(uint32, uint64) vmtf_node array \<times> uint64 \<times> uint32 \<times> uint32 \<times> uint32 option\<close>
type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> (uint32 array_list \<times> bool array)\<close>

type_synonym phase_saver_assn = \<open>bool array\<close>

instance vmtf_node :: (heap, heap) heap
proof intro_classes
  let ?to_pair = \<open>\<lambda>x::('a, 'b) vmtf_node. (stamp x, get_prev x, get_next x)\<close>
  have inj': \<open>inj ?to_pair\<close>
    unfolding inj_def by (intro allI) (case_tac x; case_tac y; auto)
  obtain to_nat :: \<open>'b \<times> 'a option \<times> 'a option \<Rightarrow> nat\<close> where
    \<open>inj to_nat\<close>
    by blast
  then have \<open>inj (to_nat o ?to_pair)\<close>
    using inj' by (blast intro: inj_compose)
  then show \<open>\<exists>to_nat :: ('a, 'b) vmtf_node \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

definition (in -) vmtf_node_rel where
\<open>vmtf_node_rel = {(a', a). (stamp a', stamp a) \<in> uint64_nat_rel \<and>
   (get_prev a', get_prev a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel \<and>
   (get_next a', get_next a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel}\<close>

abbreviation (in -)vmtf_node_assn where
\<open>vmtf_node_assn \<equiv> pure vmtf_node_rel\<close>

abbreviation vmtf_conc where
  \<open>vmtf_conc \<equiv> (array_assn vmtf_node_assn *a uint64_nat_assn *a uint32_nat_assn *a uint32_nat_assn
    *a option_assn uint32_nat_assn)\<close>

abbreviation atoms_hash_assn :: \<open>bool list \<Rightarrow> bool array \<Rightarrow> assn\<close> where
  \<open>atoms_hash_assn \<equiv> array_assn bool_assn\<close>

abbreviation distinct_atoms_assn where
  \<open>distinct_atoms_assn \<equiv> arl_assn uint32_nat_assn *a atoms_hash_assn\<close>

type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>

abbreviation vmtf_remove_conc
  :: \<open>isa_vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc \<equiv> vmtf_conc *a distinct_atoms_assn\<close>


paragraph \<open>Options\<close>

type_synonym opts = \<open>bool \<times> bool \<times> bool\<close>

abbreviation opts_assn
  :: \<open>opts \<Rightarrow> opts \<Rightarrow> assn\<close>
where
  \<open>opts_assn \<equiv> bool_assn *a bool_assn *a bool_assn\<close>

definition opts_restart where
  \<open>opts_restart = (\<lambda>(a, b). a)\<close>

definition opts_reduce where
  \<open>opts_reduce = (\<lambda>(a, b, c). b)\<close>

definition opts_unbounded_mode where
  \<open>opts_unbounded_mode = (\<lambda>(a, b, c). c)\<close>

lemma opts_restart_hnr[sepref_fr_rules]:
  \<open>(return o opts_restart, RETURN o opts_restart) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma opts_reduce_hnr[sepref_fr_rules]:
  \<open>(return o opts_reduce, RETURN o opts_reduce) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma opts_unbounded_mode_hnr[sepref_fr_rules]:
  \<open>(return o opts_unbounded_mode, RETURN o opts_unbounded_mode) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto


paragraph \<open>Base state\<close>

type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array \<times> nat\<close>
type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym vdom = \<open>nat list\<close>

abbreviation vdom_assn :: \<open>vdom \<Rightarrow> nat array_list \<Rightarrow> assn\<close> where
  \<open>vdom_assn \<equiv> arl_assn nat_assn\<close>

type_synonym vdom_assn = \<open>nat array_list\<close>

type_synonym isasat_clauses_assn = \<open>uint32 array_list\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom_assn \<times> vdom_assn \<times> nat \<times> opts \<times> isasat_clauses_assn\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom_assn \<times> vdom_assn \<times> nat \<times> opts \<times> isasat_clauses_assn\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
(* TODO rename to isasat *)
type_synonym twl_st_wl_heur =
  \<open>trail_pol \<times> arena \<times>
    conflict_option_rel \<times> nat \<times> (nat watcher) list list \<times> isa_vmtf_remove_int \<times> bool list \<times>
    nat \<times> conflict_min_cach_l \<times> lbd \<times> out_learned \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom \<times> vdom \<times> nat \<times> opts \<times> arena\<close>

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

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

lemma watched_by_app_heur_alt_def:
  \<open>watched_by_app_heur = (\<lambda>(M, N, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>
  by (auto simp: watched_by_app_heur_def intro!: ext)

definition watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> isa_vmtf_remove_int\<close> where
  \<open>get_vmtf_heur (_, _, _, _, _, vm, _) = vm\<close>

fun get_phase_saver_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool list\<close> where
  \<open>get_phase_saver_heur (_, _, _, _, _, _, \<phi>, _) = \<phi>\<close>

fun get_count_max_lvls_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_count_max_lvls_heur (_, _, _, _, _, _, _, clvls, _) = clvls\<close>

fun get_conflict_cach:: \<open>twl_st_wl_heur \<Rightarrow> conflict_min_cach_l\<close> where
  \<open>get_conflict_cach (_, _, _, _, _, _, _, _, cach, _) = cach\<close>

fun get_lbd :: \<open>twl_st_wl_heur \<Rightarrow> lbd\<close> where
  \<open>get_lbd (_, _, _, _, _, _, _, _, _, lbd, _) = lbd\<close>

fun get_outlearned_heur :: \<open>twl_st_wl_heur \<Rightarrow> out_learned\<close> where
  \<open>get_outlearned_heur (_, _, _, _, _, _, _, _, _, _, out, _) = out\<close>

fun get_fast_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_fast_ema_heur (_, _, _, _, _, _, _, _, _, _, _, _, fast_ema, _) = fast_ema\<close>

fun get_slow_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_slow_ema_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, slow_ema, _) = slow_ema\<close>

fun get_conflict_count_heur :: \<open>twl_st_wl_heur \<Rightarrow> restart_info\<close> where
  \<open>get_conflict_count_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, ccount, _) = ccount\<close>

fun get_vdom :: \<open>twl_st_wl_heur \<Rightarrow> nat list\<close> where
  \<open>get_vdom (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vdom, _) = vdom\<close>

fun get_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat list\<close> where
  \<open>get_avdom (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vdom, _) = vdom\<close>

fun get_learned_count :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_learned_count (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lcount, _) = lcount\<close>

fun get_ops :: \<open>twl_st_wl_heur \<Rightarrow> opts\<close> where
  \<open>get_ops (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, opts, _) = opts\<close>

fun get_old_arena :: \<open>twl_st_wl_heur \<Rightarrow> arena\<close> where
  \<open>get_old_arena (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, old_arena) = old_arena\<close>

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>


text \<open>Setup to convert a list from \<^typ>\<open>uint64\<close> to \<^typ>\<open>nat\<close>.\<close>
definition arl_copy_to :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
\<open>arl_copy_to R xs = map R xs\<close>

definition op_map_to
  :: \<open>('b \<Rightarrow> 'a::default) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> 'a list list nres\<close>
where
  \<open>op_map_to R e xs W j = do {
    (_, zs) \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(i,W'). i \<le> length xs \<and> W'!j = W!j @ map R (take i xs) \<and>
         (\<forall>k. k \<noteq> j \<longrightarrow> k < length W \<longrightarrow> W'!k = W!k) \<and> length W' = length W\<^esup>
      (\<lambda>(i, W'). i < length xs)
      (\<lambda>(i, W'). do {
         ASSERT(i < length xs);
         let x = xs ! i;
         RETURN (i+1, append_ll W' j (R x))})
      (0, W);
    RETURN zs
     }\<close>

lemma op_map_to_map:
  \<open>j < length W' \<Longrightarrow> op_map_to R e xs W' j \<le> RETURN (W'[j := W'!j @ map R xs])\<close>
  unfolding op_map_to_def Let_def
  apply (refine_vcg WHILEIT_rule[where R=\<open>measure (\<lambda>(i,_). length xs - i)\<close>])
         apply (auto simp: hd_conv_nth take_Suc_conv_app_nth list_update_append
      append_ll_def split: nat.splits)
  by (simp add: list_eq_iff_nth_eq)

lemma op_map_to_map_rel:
  \<open>(uncurry2 (op_map_to R e), uncurry2 (RETURN ooo (\<lambda>xs W' j. W'[j := W'!j @ map R xs]))) \<in>
    [\<lambda>((xs, ys), j). j < length ys]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f
    \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
    \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: op_map_to_map)

definition convert_single_wl_to_nat where
\<open>convert_single_wl_to_nat W i W' j =
  op_map_to (\<lambda>(i, C). (nat_of_uint64_conv i, C)) (to_watcher 0 (Pos 0) False) (W!i) W' j\<close>

sepref_definition convert_single_wl_to_nat_code
  is \<open>uncurry3 convert_single_wl_to_nat\<close>
  :: \<open>[\<lambda>(((W, i), W'), j). i < length W \<and> j < length W']\<^sub>a
       (arrayO_assn (arl_assn (watcher_fast_assn)))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
       (arrayO_assn (arl_assn (watcher_assn)))\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
      arrayO_assn (arl_assn (watcher_assn))\<close>
  supply [[goals_limit=1]]
  unfolding convert_single_wl_to_nat_def op_map_to_def nth_ll_def[symmetric]
    length_ll_def[symmetric]
  by sepref

definition convert_single_wl_to_nat_conv where
\<open>convert_single_wl_to_nat_conv xs i W' j =
   W'[j :=  map (\<lambda>(i, C). (nat_of_uint64_conv i, C)) (xs!i)]\<close>

lemma convert_single_wl_to_nat:
  \<open>(uncurry3 convert_single_wl_to_nat,
    uncurry3 (RETURN oooo convert_single_wl_to_nat_conv)) \<in>
   [\<lambda>(((xs, i), ys), j). i < length xs \<and> j < length ys \<and> ys!j = []]\<^sub>f
   \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
     \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow>
     \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: convert_single_wl_to_nat_def convert_single_wl_to_nat_conv_def nat_of_uint64_conv_def
      dest: op_map_to_map[of _ _ id])

lemma convert_single_wl_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(uncurry3 convert_single_wl_to_nat_code,
     uncurry3 (RETURN \<circ>\<circ>\<circ> convert_single_wl_to_nat_conv))
  \<in> [\<lambda>(((a, b), ba), bb). b < length a \<and> bb < length ba \<and> ba ! bb = []]\<^sub>a
    (arrayO_assn (arl_assn watcher_fast_assn))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
    (arrayO_assn (arl_assn watcher_assn))\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    arrayO_assn (arl_assn watcher_assn)\<close>
  using convert_single_wl_to_nat_code.refine[FCOMP convert_single_wl_to_nat]
  by auto

definition convert_wlists_to_nat_conv where
  \<open>convert_wlists_to_nat_conv = id\<close>

definition convert_wlists_to_nat where
  \<open>convert_wlists_to_nat = op_map (map (\<lambda>(n, L, b). (nat_of_uint64_conv n, L, b))) []\<close>

lemma convert_wlists_to_nat_alt_def:
  \<open>convert_wlists_to_nat = op_map id []\<close>
proof -
  have [simp]: \<open>(\<lambda>(n, bL). (nat_of_uint64_conv n, bL)) = id\<close>
    by (auto intro!: ext simp: nat_of_uint64_conv_def)
  show ?thesis
    by (auto simp: convert_wlists_to_nat_def)
qed


abbreviation (in -) watchers_assn where
  \<open>watchers_assn \<equiv> arl_assn (watcher_assn)\<close>

abbreviation (in -) watchlist_assn where
  \<open>watchlist_assn \<equiv> arrayO_assn watchers_assn\<close>

abbreviation (in -) watchers_fast_assn where
  \<open>watchers_fast_assn \<equiv> arl_assn (watcher_fast_assn)\<close>

abbreviation (in -) watchlist_fast_assn where
  \<open>watchlist_fast_assn \<equiv> arrayO_assn watchers_fast_assn\<close>

lemma convert_single_wl_to_nat_conv_alt_def:
  \<open>convert_single_wl_to_nat_conv zs i xs i = xs[i := map (\<lambda>(i, y, y'). (nat_of_uint64_conv i, y, y')) (zs ! i)]\<close>
  unfolding convert_single_wl_to_nat_conv_def
  by auto

(* TODO n should also be used in the condition *)
lemma convert_wlists_to_nat_alt_def2:
  \<open>convert_wlists_to_nat xs = do {
    let n = length xs;
    let zs = init_lrl n;
    (uu, zs) \<leftarrow>
      WHILE\<^sub>T\<^bsup>\<lambda>(i, zs).
                 i \<le> length xs \<and>
                 take i zs =
                 map (map (\<lambda>(n, y, y'). (nat_of_uint64_conv n, y, y')))
                  (take i xs) \<and>
                 length zs = length xs \<and> (\<forall>k\<ge>i. k < length xs \<longrightarrow> zs ! k = [])\<^esup>
       (\<lambda>(i, zs). i < length zs)
       (\<lambda>(i, zs). do {
          ASSERT (i < length zs);
          RETURN
            (i + 1, convert_single_wl_to_nat_conv xs i zs i)
       })
       (0, zs);
    RETURN zs
  }\<close>
  unfolding convert_wlists_to_nat_def
    op_map_def[of \<open>map (\<lambda>(n, y, y'). (nat_of_uint64_conv n, y, y'))\<close> \<open>[]\<close>,
      unfolded convert_single_wl_to_nat_conv_alt_def[symmetric] init_lrl_def[symmetric]] Let_def
  by auto

sepref_register init_lrl

sepref_definition convert_wlists_to_nat_code
  is \<open>convert_wlists_to_nat\<close>
  :: \<open>watchlist_fast_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  supply length_a_hnr[sepref_fr_rules]
  unfolding convert_wlists_to_nat_alt_def2
  by sepref

lemma convert_wlists_to_nat_convert_wlists_to_nat_conv:
  \<open>(convert_wlists_to_nat, RETURN o convert_wlists_to_nat_conv) \<in>
     \<langle>\<langle>nat_rel \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>\<^sub>f
     \<langle>\<langle>\<langle>nat_rel \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: convert_wlists_to_nat_def nat_of_uint64_conv_def
       convert_wlists_to_nat_conv_def
      intro: order.trans op_map_map)

lemma convert_wlists_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(convert_wlists_to_nat_code, RETURN \<circ> convert_wlists_to_nat_conv)
    \<in> (arrayO_assn (arl_assn watcher_fast_assn))\<^sup>d \<rightarrow>\<^sub>a
      arrayO_assn (arl_assn watcher_assn)\<close>
  using convert_wlists_to_nat_code.refine[FCOMP convert_wlists_to_nat_convert_wlists_to_nat_conv]
  by simp


text \<open>The virtual domain is composed of the addressable (and accessible) elements, i.e.,
  the domain and all the deleted clauses that are still present in the watch lists.
\<close>
definition vdom_m :: \<open>nat multiset \<Rightarrow> (nat literal \<Rightarrow> (nat \<times> _) list) \<Rightarrow> (nat, 'b) fmap \<Rightarrow> nat set\<close> where
  \<open>vdom_m \<A> W N = \<Union>(((`) fst) ` set ` W ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)) \<union> set_mset (dom_m N)\<close>

lemma vdom_m_simps[simp]:
  \<open>bh \<in># dom_m N \<Longrightarrow> vdom_m \<A> W (N(bh \<hookrightarrow> C)) = vdom_m \<A> W N\<close>
  \<open>bh \<notin># dom_m N \<Longrightarrow> vdom_m \<A> W (N(bh \<hookrightarrow> C)) = insert bh (vdom_m \<A> W N)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps2[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow> vdom_m \<A> (W(L := W L @ [(i, C)])) N = vdom_m \<A> W N\<close>
  \<open>bi \<in># dom_m ax \<Longrightarrow> vdom_m \<A> (bp(L:= bp L @ [(bi, av')])) ax = vdom_m \<A> bp ax\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps3[simp]:
  \<open>fst biav' \<in># dom_m ax \<Longrightarrow> vdom_m \<A> (bp(L:= bp L @ [biav'])) ax = vdom_m \<A> bp ax\<close>
  by (cases biav'; auto simp: dest: multi_member_split[of L] split: if_splits)

text \<open>What is the difference with the next lemma?\<close>
lemma [simp]:
  \<open>bf \<in># dom_m ax \<Longrightarrow> vdom_m \<A> bj (ax(bf \<hookrightarrow> C')) = vdom_m \<A> bj (ax)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps4[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow>
     vdom_m \<A> (W (L1 := W L1 @ [(i, C1)], L2 := W L2 @ [(i, C2)])) N = vdom_m \<A> W N\<close>
 by (auto simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

text \<open>This is @{thm vdom_m_simps4} if the assumption of distinctness is not present in the context.\<close>
lemma vdom_m_simps4'[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow>
     vdom_m \<A> (W (L1 := W L1 @ [(i, C1), (i, C2)])) N = vdom_m \<A> W N\<close>
  by (auto simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

text \<open>We add a spurious dependency to the parameter of the locale:\<close>
definition empty_watched :: \<open>nat multiset \<Rightarrow> nat literal \<Rightarrow> (nat \<times> nat literal \<times> bool) list\<close> where
  \<open>empty_watched \<A> = (\<lambda>_. [])\<close>

lemma vdom_m_empty_watched[simp]:
  \<open>vdom_m \<A> (empty_watched \<A>') N = set_mset (dom_m N)\<close>
  by (auto simp: vdom_m_def empty_watched_def)

text \<open>The following rule makes the previous not applicable. Therefore, we do not mark this lemma as
simp.\<close>
lemma vdom_m_simps5:
  \<open>i \<notin># dom_m N \<Longrightarrow> vdom_m \<A> W (fmupd i C N) = insert i (vdom_m \<A> W N)\<close>
  by (force simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

lemma in_watch_list_in_vdom:
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>w < length (watched_by S L)\<close>
  shows \<open>fst (watched_by S L ! w) \<in> vdom_m \<A> (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)

lemma in_watch_list_in_vdom':
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close> and \<open>A \<in> set (watched_by S L)\<close>
  shows \<open>fst A \<in> vdom_m \<A> (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)

lemma in_dom_in_vdom[simp]:
  \<open>x \<in># dom_m N \<Longrightarrow> x \<in> vdom_m \<A> W N\<close>
  unfolding vdom_m_def
  by (auto dest: multi_member_split)

lemma in_vdom_m_upd:
  \<open>x1f \<in> vdom_m \<A> (g(x1e := (g x1e)[x2 := (x1f, x2f)])) b\<close>
  if \<open>x2 < length (g x1e)\<close> and \<open>x1e \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>
  using that
  unfolding vdom_m_def
  by (auto dest!: multi_member_split intro!: set_update_memI img_fst)


lemma in_vdom_m_fmdropD:
  \<open>x \<in> vdom_m \<A> ga (fmdrop C baa) \<Longrightarrow> x \<in> (vdom_m \<A> ga baa)\<close>
  unfolding vdom_m_def
  by (auto dest: in_diffD)

definition cach_refinement_empty where
  \<open>cach_refinement_empty \<A> cach \<longleftrightarrow>
       (cach, \<lambda>_. SEEN_UNKNOWN) \<in> cach_refinement \<A>\<close>

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
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts, old_arena),
     (M, N, D, NE, UE, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms N (NE + UE)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE)) M \<and>
    phase_saving (all_atms N (NE + UE)) \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms N (NE + UE)) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_atms N (NE + UE))  W N \<subseteq> set vdom \<and>
    set avdom \<subseteq> set vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE)) \<and>
    isasat_input_nempty (all_atms N (NE + UE)) \<and>
    old_arena = []
  }\<close>

lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow>
       watched_by_int S C = watched_by S' C\<close> and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close>
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def all_atms_def)

abbreviation twl_st_heur'''
   :: \<open>nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur''' r \<equiv> {(S, T). (S, T) \<in> twl_st_heur \<and>
           length (get_clauses_wl_heur S) = r}\<close>

definition twl_st_heur' :: \<open>nat multiset \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur' N = {(S, S'). (S, S') \<in> twl_st_heur \<and> dom_m (get_clauses_wl S') = N}\<close>

definition twl_st_heur_conflict_ana
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_conflict_ana =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount, vdom,
       avdom, lcount, opts, old_arena),
      (M, N, D, NE, UE, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms N (NE + UE)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE)) M \<and>
    phase_saving (all_atms N (NE + UE)) \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms N (NE + UE)) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_atms N (NE + UE)) W N \<subseteq> set vdom \<and>
    set avdom \<subseteq> set vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE)) \<and>
    isasat_input_nempty (all_atms N (NE + UE)) \<and>
    old_arena = []
  }\<close>

lemma twl_st_heur_twl_st_heur_conflict_ana:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_conflict_ana\<close>
  by (auto simp: twl_st_heur_def twl_st_heur_conflict_ana_def)

lemma twl_st_heur_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_conflict_ana\<close>
  shows
    \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
    \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_conflict_ana_def by (auto simp: map_fun_rel_def all_atms_def)

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a
separate array.\<close>
definition twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, _, _, _, vdom, avdom, lcount, opts,
       old_arena),
     (M, N, D, NE, UE, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', None) \<in> option_lookup_clause_rel (all_atms N (NE + UE)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE)) M \<and>
    phase_saving (all_atms N (NE + UE)) \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty (all_atms N (NE + UE)) cach \<and>
    out_learned M None outl \<and>
    lcount = size (learned_clss_l N) \<and>
    vdom_m (all_atms N (NE + UE)) W N \<subseteq> set vdom \<and>
    set avdom \<subseteq> set vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE)) \<and>
    isasat_input_nempty (all_atms N (NE + UE)) \<and>
    old_arena = []
  }\<close>


definition isasat_unbounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>isasat_unbounded_assn =
  trail_pol_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_assn *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  ema_assn *a
  ema_assn *a
  restart_info_assn *a
  vdom_assn *a
  vdom_assn *a
  nat_assn *a
  opts_assn *a arena_assn\<close>

definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_fast_assn *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_l_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  ema_assn *a
  ema_assn *a
  restart_info_assn *a
  vdom_assn *a
  vdom_assn *a
  nat_assn *a
  opts_assn *a arena_assn\<close>

text \<open>
  The difference between \<^term>\<open>isasat_unbounded_assn\<close> and \<^term>\<open>isasat_bounded_assn\<close> corresponds to the
  following condition:
\<close>
definition isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<longleftrightarrow> (length (get_clauses_wl_heur S) \<le> uint64_max - (uint32_max div 2 + 6))\<close>

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> length (get_clauses_wl_heur S) \<le> uint64_max\<close>
  by (cases S) (auto simp: isasat_fast_def)

definition isasat_fast_slow :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>isasat_fast_slow =
    (\<lambda>(M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount).
      RETURN (trail_pol_slow_of_fast M', N', D', Q', convert_wlists_to_nat_conv W', vm, \<phi>,
        clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount))\<close>

sepref_definition isasat_fast_slow_code
  is \<open>isasat_fast_slow\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_unbounded_assn_def isasat_fast_slow_def
  by sepref

declare isasat_fast_slow_code.refine[sepref_fr_rules]

definition (in -)isasat_fast_slow_wl_D where
  \<open>isasat_fast_slow_wl_D = id\<close>

lemma isasat_fast_slow_alt_def:
  \<open>isasat_fast_slow S = RETURN S\<close>
  by (cases S)
    (auto simp: isasat_fast_slow_def trail_slow_of_fast_def convert_wlists_to_nat_conv_def
      trail_pol_slow_of_fast_alt_def)

lemma isasat_fast_slow_isasat_fast_slow_wl_D:
  \<open>(isasat_fast_slow, RETURN o isasat_fast_slow_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
    (auto simp: isasat_fast_slow_alt_def isasat_fast_slow_wl_D_def)


subsubsection \<open>Lift Operations to State\<close>

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur = (\<lambda>(M, N, (b, _), Q, W, _). b)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
      option_lookup_clause_rel_def
     split: option.splits)

lemma get_conflict_wl_is_None_heur_alt_def:
    \<open>RETURN o get_conflict_wl_is_None_heur = (\<lambda>(M, N, (b, _), Q, W, _). RETURN b)\<close>
  unfolding get_conflict_wl_is_None_heur_def
  by auto

sepref_definition get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_unbounded_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare get_conflict_wl_is_None_code.refine[sepref_fr_rules]

sepref_definition get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_bounded_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

declare get_conflict_wl_is_None_fast_code.refine[sepref_fr_rules]

definition count_decided_st :: \<open>nat twl_st_wl \<Rightarrow> nat\<close> where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

definition isa_count_decided_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>isa_count_decided_st = (\<lambda>(M, _). count_decided_pol M)\<close>

sepref_definition isa_count_decided_st_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_unbounded_assn_def
  by sepref

declare isa_count_decided_st_code.refine[sepref_fr_rules]

sepref_definition isa_count_decided_st_fast_code
  is \<open>RETURN o isa_count_decided_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding isa_count_decided_st_def isasat_bounded_assn_def
  by sepref

declare isa_count_decided_st_fast_code.refine[sepref_fr_rules]

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o isa_count_decided_st, RETURN o count_decided_st) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_heur_def isa_count_decided_st_def
       count_decided_trail_ref[THEN fref_to_Down_unRET_Id])

lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition atm_is_in_conflict_st_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>atm_is_in_conflict_st_heur L = (\<lambda>(M, N, (_, D), _). atm_in_conflict_lookup (atm_of L) D)\<close>

lemma atm_is_in_conflict_st_heur_alt_def:
  \<open>RETURN oo atm_is_in_conflict_st_heur = (\<lambda>L (M, N, (_, (_, D)), _). RETURN (D ! (atm_of L) \<noteq> None))\<close>
  unfolding atm_is_in_conflict_st_heur_def by (auto intro!: ext simp: atm_in_conflict_lookup_def)

lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (RETURN oo atm_is_in_conflict_st_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   [\<lambda>(L, S). -L \<notin># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None \<and>
     L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have 1: \<open>aaa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l A \<Longrightarrow> atm_of aaa  \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l A)\<close> for aaa A
    by (auto simp: atms_of_def)
  show ?thesis
  unfolding atm_is_in_conflict_st_heur_def twl_st_heur_def option_lookup_clause_rel_def
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  apply clarsimp
  apply (subst atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id])
  unfolding prod.simps prod_rel_iff
    apply (rule 1; assumption)
   apply (auto simp: all_atms_def; fail)
  by (auto simp: is_in_conflict_st_def atm_in_conflict_def atms_of_def atm_of_eq_atm_of)
qed
lemma atm_is_in_conflict_st_heur_is_in_conflict_st_ana:
  \<open>(uncurry (RETURN oo atm_is_in_conflict_st_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   [\<lambda>(L, S). -L \<notin># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None \<and>
     L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_conflict_ana  \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have 1: \<open>aaa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l A \<Longrightarrow> atm_of aaa  \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l A)\<close> for aaa A
    by (auto simp: atms_of_def)
  show ?thesis
  unfolding atm_is_in_conflict_st_heur_def twl_st_heur_conflict_ana_def option_lookup_clause_rel_def
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  apply clarsimp
  apply (subst atm_in_conflict_lookup_atm_in_conflict[THEN fref_to_Down_unRET_uncurry_Id])
  unfolding prod.simps prod_rel_iff
    apply (rule 1; assumption)
   apply (auto simp: all_atms_def; fail)
  by (auto simp: is_in_conflict_st_def atm_in_conflict_def atms_of_def atm_of_eq_atm_of)
qed

definition polarity_st_heur
 :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option\<close>
where
  \<open>polarity_st_heur S =
    polarity_pol (get_trail_wl_heur S)\<close>

definition polarity_st_pre where
\<open>polarity_st_pre \<equiv> \<lambda>(S, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)\<close>

lemma polarity_st_heur_alt_def:
  \<open>polarity_st_heur = (\<lambda>(M, _). polarity_pol M)\<close>
  by (auto simp: polarity_st_heur_def)

definition polarity_st_heur_pre where
\<open>polarity_st_heur_pre \<equiv> \<lambda>(S, L). polarity_pol_pre (get_trail_wl_heur S) L\<close>

lemma polarity_st_heur_pre:
  \<open>(S', S) \<in> twl_st_heur \<Longrightarrow> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S) \<Longrightarrow> polarity_st_heur_pre (S', L)\<close>
  by (auto simp: twl_st_heur_def polarity_st_heur_pre_def all_atms_def[symmetric]
    intro!: polarity_st_heur_pre_def polarity_pol_pre)

sepref_definition polarity_st_heur_pol
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_heur_pre]\<^sub>a isasat_unbounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_unbounded_assn_def polarity_st_pre_def
    polarity_st_heur_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_st_heur_pol.refine[sepref_fr_rules]

sepref_definition polarity_st_heur_pol_fast
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_heur_pre]\<^sub>a isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_bounded_assn_def polarity_st_pre_def
    polarity_st_heur_pre_def
  supply [[goals_limit = 1]]
  by sepref

declare polarity_st_heur_pol_fast.refine[sepref_fr_rules]


abbreviation nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>


subsection \<open>More theorems\<close>

lemma valid_arena_DECISION_REASON:
  \<open>valid_arena arena NU vdom \<Longrightarrow> DECISION_REASON \<notin># dom_m NU\<close>
  using arena_lifting[of arena NU vdom DECISION_REASON]
  by (auto simp: DECISION_REASON_def SHIFTS_def)

definition count_decided_st_heur :: \<open>_ \<Rightarrow> _\<close> where
  \<open>count_decided_st_heur = (\<lambda>((_,_,_,_,n, _), _). n)\<close>

lemma count_decided_st_heur[sepref_fr_rules]:
  \<open>(return o count_decided_st_heur, RETURN o count_decided_st_heur) \<in>
      isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  \<open>(return o count_decided_st_heur, RETURN o count_decided_st_heur) \<in>
      isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding count_decided_st_heur_def isasat_bounded_assn_def isasat_unbounded_assn_def
  by (sepref_to_hoare; sep_auto)+

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

lemma vmtf_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> L \<in> vmtf \<A> M \<Longrightarrow> L \<in> vmtf \<B> M\<close>
  using \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  unfolding vmtf_def vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
  by (auto simp: )

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
  by (auto simp: cach_refinement_empty_def cach_refinement_alt_def intro!: ext)

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


subsection \<open>Shared Code Equations\<close>

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
  by (intro frefI nres_relI)
    (use arena_dom_status_iff in_dom_in_vdom in
      \<open>auto 5 5 simp: clause_not_marked_to_delete_def twl_st_heur_def
        clause_not_marked_to_delete_heur_def arena_dom_status_iff all_atms_def[symmetric]
        clause_not_marked_to_delete_pre_def\<close>)


definition (in -) access_lit_in_clauses_heur_pre where
  \<open>access_lit_in_clauses_heur_pre =
      (\<lambda>((S, i), j).
           arena_lit_pre (get_clauses_wl_heur S) (i+j))\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur S i j = arena_lit (get_clauses_wl_heur S) (i + j)\<close>

lemma access_lit_in_clauses_heur_alt_def:
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j. arena_lit N (i + j))\<close>
  by (auto simp: access_lit_in_clauses_heur_def intro!: ext)


sepref_definition access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[access_lit_in_clauses_heur_pre]\<^sub>a
      isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]]
  unfolding isasat_unbounded_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric]
  by sepref

declare access_lit_in_clauses_heur_code.refine[sepref_fr_rules]

lemma access_lit_in_clauses_heur_fast_pre:
  \<open>arena_lit_pre (get_clauses_wl_heur a) (ba + b) \<Longrightarrow>
    isasat_fast a \<Longrightarrow> ba + b \<le> uint64_max\<close>
  by (auto simp: arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      dest!: arena_lifting(10)
      dest!: isasat_fast_length_leD)[]

sepref_definition access_lit_in_clauses_heur_fast_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>((S, i), j). access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> uint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k  *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp] [[goals_limit=1]] arena_is_valid_clause_idx_le_uint64_max[intro]
  unfolding isasat_bounded_assn_def access_lit_in_clauses_heur_alt_def
    fmap_rll_def[symmetric] access_lit_in_clauses_heur_pre_def
    fmap_rll_u64_def[symmetric] arena_lit_pre_le[intro]
  by sepref

declare access_lit_in_clauses_heur_fast_code.refine[sepref_fr_rules]

lemma eq_insertD: \<open>A = insert a B \<Longrightarrow> a \<in> A \<and> B \<subseteq> A\<close>
  by auto

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (add_mset L C)) = insert (Pos L) (insert (Neg L) (set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l C)))\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma correct_watching_dom_watched:
  assumes \<open>correct_watching S\<close> and \<open>\<And>C. C \<in># ran_mf (get_clauses_wl S) \<Longrightarrow> C \<noteq> []\<close>
  shows \<open>set_mset (dom_m (get_clauses_wl S)) \<subseteq>
     \<Union>(((`) fst) ` set ` (get_watched_wl S) ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S)))\<close>
    (is \<open>?A \<subseteq> ?B\<close>)
proof
  fix C
  assume \<open>C \<in> ?A\<close>
  then obtain D where
    D: \<open>D \<in># ran_mf (get_clauses_wl S)\<close> and
    D': \<open>D = get_clauses_wl S \<propto> C\<close> and
    C: \<open>C \<in># dom_m (get_clauses_wl S)\<close>
    by auto
  have \<open>atm_of (hd D) \<in># atm_of `# all_lits_st S\<close>
    using D D' assms(2)[of D]
    by (cases S; cases D)
      (auto simp: all_lits_def
          all_lits_of_mm_add_mset all_lits_of_m_add_mset
        dest!: multi_member_split)
  then show \<open>C \<in> ?B\<close>
    using assms(1) assms(2)[of D] D D'
      multi_member_split[OF C]
    by (cases S; cases \<open>get_clauses_wl S \<propto> C\<close>;
         cases \<open>hd (get_clauses_wl S \<propto> C)\<close>)
       (auto simp: correct_watching.simps clause_to_update_def
           all_lits_of_mm_add_mset all_lits_of_m_add_mset
	  \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
	  eq_commute[of \<open>_ # _\<close>] atm_of_eq_atm_of
	dest!: multi_member_split eq_insertD
	dest!:  arg_cong[of \<open>filter_mset _ _\<close> \<open>add_mset _ _\<close> set_mset])
qed


subsection \<open>Rewatch\<close>


subsection \<open>Rewatch\<close>

definition rewatch_heur where
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        ASSERT(arena_lit_pre arena C);
        ASSERT(arena_lit_pre arena (C+1));
        let L1 = arena_lit arena C;
        let L2 = arena_lit arena (C + 1);
        ASSERT(nat_of_lit L1 < length W);
        ASSERT(arena_is_valid_clause_idx arena C);
        let b = (arena_length arena C = 2);
        let W = append_ll W (nat_of_lit L1) (to_watcher C L2 b);
        ASSERT(nat_of_lit L2 < length W);
        let W = append_ll W (nat_of_lit L2) (to_watcher C L1 b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>


lemma rewatch_heur_rewatch:
  assumes
    \<open>valid_arena arena N vdom\<close> and \<open>set xs \<subseteq> vdom\<close> and \<open>distinct xs\<close> and \<open>set_mset (dom_m N) \<subseteq> set xs\<close> and
    \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and lall: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    \<open>vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)\<close>
  shows
    \<open>rewatch_heur xs arena W \<le> \<Down> ({(W, W'). (W, W') \<in>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)}) (rewatch N W')\<close>
proof -
  have [refine0]: \<open>(xs, xsa) \<in> Id \<Longrightarrow>
     ([0..<length xs], [0..<length xsa]) \<in> \<langle>{(x, x'). x = x' \<and> xs!x \<in> vdom}\<rangle>list_rel\<close>
    for xsa
    using assms unfolding list_rel_def
    by (auto simp: list_all2_same)
  show ?thesis
    unfolding rewatch_heur_def rewatch_def
    apply (subst (2) nfoldli_nfoldli_list_nth)
    apply (refine_vcg)
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal by fast
    subgoal
      using assms
      unfolding arena_is_valid_clause_vdom_def
      by blast
    subgoal
      using assms
      by (auto simp: arena_dom_status_iff)
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (rule_tac j=\<open>xs ! xi\<close> in bex_leI)
        (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (rule_tac j=\<open>xs ! xi\<close> in bex_leI)
        (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of \<open>xs ! xi\<close> 0] assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      unfolding arena_is_valid_clause_idx_and_access_def arena_is_valid_clause_idx_def
      by (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1] assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    done
qed

sepref_register rewatch_heur

sepref_definition rewatch_heur_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>vdom_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a watchlist_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
  by sepref

declare rewatch_heur_code.refine[sepref_fr_rules]

lemma rewatch_heur_alt_def:
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        let C = uint64_of_nat_conv C;
        ASSERT(arena_lit_pre arena C);
        ASSERT(arena_lit_pre arena (C+1));
        let L1 = arena_lit arena C;
        let L2 = arena_lit arena (C + 1);
        ASSERT(nat_of_lit L1 < length W);
        ASSERT(arena_is_valid_clause_idx arena C);
        let b = (arena_length arena C = 2);
        let W = append_ll W (nat_of_lit L1) (to_watcher C L2 b);
        ASSERT(nat_of_lit L2 < length W);
        let W = append_ll W (nat_of_lit L2) (to_watcher C L1 b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>
  unfolding Let_def uint64_of_nat_conv_def rewatch_heur_def
  by auto

lemma arena_lit_pre_le_uint64_max:
 \<open>length ba \<le> uint64_max \<Longrightarrow>
       arena_lit_pre ba a \<Longrightarrow> a \<le> uint64_max\<close>
  using arena_lifting(10)[of ba _ _]
  by (fastforce simp: arena_lifting arena_is_valid_clause_idx_def arena_lit_pre_def
      arena_is_valid_clause_idx_and_access_def)

sepref_definition rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> uint64_max) \<and> length arena \<le> uint64_max]\<^sub>a
        vdom_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]] uint64_of_nat_conv_def[simp]
     arena_lit_pre_le_uint64_max[intro]
  unfolding rewatch_heur_alt_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
    one_uint64_nat_def[symmetric] to_watcher_fast_def[symmetric]
  by sepref

declare rewatch_heur_fast_code.refine[sepref_fr_rules]

definition rewatch_heur_st
 :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>rewatch_heur_st = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, t, vdom, avdom, ccount, lcount). do {
  W \<leftarrow> rewatch_heur vdom N0 W;
  RETURN (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, t, vdom, avdom, ccount, lcount)
  })\<close>

definition rewatch_heur_st_fast where
  \<open>rewatch_heur_st_fast = rewatch_heur_st\<close>

sepref_definition rewatch_heur_st_code
  is \<open>(rewatch_heur_st)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def
    isasat_unbounded_assn_def
  by sepref

definition rewatch_heur_st_fast_pre where
  \<open>rewatch_heur_st_fast_pre S =
     ((\<forall>x \<in> set (get_vdom S). x \<le> uint64_max) \<and> length (get_clauses_wl_heur S) \<le> uint64_max)\<close>

sepref_definition rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def rewatch_heur_st_fast_pre_def
    isasat_bounded_assn_def rewatch_heur_st_fast_def
  by sepref

declare rewatch_heur_st_code.refine[sepref_fr_rules]
  rewatch_heur_st_fast_code.refine[sepref_fr_rules]

definition rewatch_st :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>rewatch_st S = do{
     (M, N, D, NE, UE, Q, W) \<leftarrow> RETURN S;
     W \<leftarrow> rewatch N W;
     RETURN ((M, N, D, NE, UE, Q, W))
  }\<close>


fun remove_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>remove_watched_wl (M, N, D, NE, UE, Q, _) = (M, N, D, NE, UE, Q)\<close>

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
    apply (cases S, case_tac \<open>rewatch b g\<close>)
    by (auto simp: RES_RETURN_RES)
  subgoal
    using rewatch_correctness[OF assms]
    unfolding rewatch_st_def
    apply (cases S, case_tac \<open>rewatch b g\<close>)
    by (force simp: RES_RETURN_RES)+
  done

end
