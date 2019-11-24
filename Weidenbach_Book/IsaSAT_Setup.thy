theory IsaSAT_Setup
  imports
    Watched_Literals_VMTF
    Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Lookup_Conflict
    IsaSAT_Clauses IsaSAT_Arena IsaSAT_Watch_List LBD
begin

subsection \<open>Code Generation\<close>

text \<open>We here define the last step of our refinement: the step with all the heuristics and fully
  deterministic code.

  After the result of benchmarking, we concluded that the use of \<^typ>\<open>nat\<close> leads to worse performance
  than using \<open>sint64\<close>. As, however, the later is not complete, we do so with a switch: as long
  as it fits, we use the faster (called 'bounded') version. After that we switch to the 'unbounded'
  version (which is still bounded by memory anyhow) if we generate Standard ML code.

  We have successfully killed all natural numbers when generating LLVM. However, the LLVM binding
  does not have a binding to GMP integers.
\<close>

subsubsection \<open>Types and Refinement Relations\<close>

paragraph \<open>Statistics\<close>

text \<open>
We do some statistics on the run.

NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions, do some comparisons (e.g., to conclude that
we are propagating slower than the other solvers), or to test different option combination.
\<close>
type_synonym stats = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>


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

definition add_lbd :: \<open>64 word \<Rightarrow> stats \<Rightarrow> stats\<close> where
  \<open>add_lbd lbd = (\<lambda>(propa, confl, dec, res, lres, uset, gcs, lbds). (propa, confl, dec, res, lres, uset, gcs, lbd + lbds))\<close>


paragraph \<open>Moving averages\<close>

text \<open>We use (at least hopefully) the variant of EMA-14 implemented in Cadical, but with fixed-point
calculation (\<^term>\<open>1 :: nat\<close> is \<^term>\<open>(1 :: nat) >> 32\<close>).

Remark that the coefficient \<^term>\<open>\<beta>\<close> already should not take care of the fixed-point conversion of the glue.
Otherwise, \<^term>\<open>value\<close> is wrongly updated.
\<close>
type_synonym ema = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition ema_bitshifting where
  \<open>ema_bitshifting = (1 << 32)\<close>


definition (in -) ema_update :: \<open>nat \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = (of_nat lbd) * ema_bitshifting in
     let value = if lbd > value then value + (\<beta> * (lbd - value) >> 32) else value - (\<beta> * (value - lbd) >> 32) in
     if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait - 1, period)
     else
       let wait = 2 * period + 1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

definition (in -) ema_update_ref :: \<open>32 word \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update_ref = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = ucast lbd * ema_bitshifting in
     let value = if lbd > value then value + (\<beta> * (lbd - value) >> 32) else value - (\<beta> * (value - lbd) >> 32) in
     if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait - 1, period)
     else
       let wait = 2 * period + 1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

definition (in -) ema_init :: \<open>64 word \<Rightarrow> ema\<close> where
  \<open>ema_init \<alpha> = (0, \<alpha>, ema_bitshifting, 0, 0)\<close>

fun ema_reinit where
  \<open>ema_reinit (value, \<alpha>, \<beta>, wait, period) = (value, \<alpha>, 1 << 32, 0, 0)\<close>

fun ema_get_value :: \<open>ema \<Rightarrow> 64 word\<close> where
  \<open>ema_get_value (v, _) = v\<close>

text \<open>We use the default values for Cadical: \<^term>\<open>(3 / 10 ^2)\<close> and  \<^term>\<open>(1 / 10 ^ 5)\<close>  in our fixed-point
  version.
\<close>

abbreviation ema_fast_init :: ema where
  \<open>ema_fast_init \<equiv> ema_init (128849010)\<close>

abbreviation ema_slow_init :: ema where
  \<open>ema_slow_init \<equiv> ema_init 429450\<close>


paragraph \<open>Information related to restarts\<close>

definition NORMAL_PHASE :: \<open>64 word\<close> where
  \<open>NORMAL_PHASE = 0\<close>

definition QUIET_PHASE :: \<open>64 word\<close> where
  \<open>QUIET_PHASE = 1\<close>

definition DEFAULT_INIT_PHASE :: \<open>64 word\<close> where
  \<open>DEFAULT_INIT_PHASE = 10000\<close>


type_synonym restart_info = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition incr_conflict_count_since_last_restart :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>incr_conflict_count_since_last_restart = (\<lambda>(ccount, ema_lvl, restart_phase, end_of_phase).
    (ccount + 1, ema_lvl, restart_phase, end_of_phase))\<close>

definition restart_info_update_lvl_avg :: \<open>32 word \<Rightarrow> restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_update_lvl_avg = (\<lambda>lvl (ccount, ema_lvl). (ccount, ema_lvl))\<close>

definition restart_info_init :: \<open>restart_info\<close> where
  \<open>restart_info_init = (0, 0, NORMAL_PHASE, DEFAULT_INIT_PHASE)\<close>

definition restart_info_restart_done :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_restart_done = (\<lambda>(ccount, lvl_avg). (0, lvl_avg))\<close>

paragraph \<open>Phase saving\<close>

type_synonym phase_save_heur = \<open>phase_saver \<times> phase_saver \<times> phase_saver\<close>

definition phase_save_heur_rel :: \<open>nat multiset \<Rightarrow> phase_save_heur \<Rightarrow> bool\<close> where
\<open>phase_save_heur_rel \<A> = (\<lambda>(\<phi>, target, best). phase_saving \<A> \<phi> \<and>
  phase_saving \<A> target \<and> phase_saving \<A> best \<and> length \<phi> = length best \<and>
  length target = length best)\<close>


paragraph \<open>Heuristics\<close>

type_synonym restart_heuristics = \<open>ema \<times> ema \<times> restart_info \<times> 64 word \<times> phase_save_heur\<close>

fun fast_ema_of :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>fast_ema_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = fast_ema\<close>

fun slow_ema_of :: \<open>restart_heuristics \<Rightarrow> ema\<close> where
  \<open>slow_ema_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = slow_ema\<close>

fun restart_info_of :: \<open>restart_heuristics \<Rightarrow> restart_info\<close> where
  \<open>restart_info_of (fast_ema, slow_ema, restart_info, wasted, \<phi>) = restart_info\<close>

fun current_restart_phase :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>current_restart_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    restart_phase\<close>

fun incr_restart_phase :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_restart_phase (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase, end_of_phase), wasted, \<phi>) =
    (fast_ema, slow_ema, (ccount, ema_lvl, restart_phase XOR 1, end_of_phase), wasted, \<phi>)\<close>

fun incr_wasted :: \<open>64 word \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>incr_wasted waste (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, wasted + waste, \<phi>)\<close>

fun set_zero_wasted :: \<open>restart_heuristics \<Rightarrow> restart_heuristics\<close> where
  \<open>set_zero_wasted (fast_ema, slow_ema, res_info, wasted, \<phi>) =
    (fast_ema, slow_ema, res_info, 0, \<phi>)\<close>

fun wasted_of :: \<open>restart_heuristics \<Rightarrow> 64 word\<close> where
  \<open>wasted_of (fast_ema, slow_ema, res_info, wasted, \<phi>) = wasted\<close>

definition heuristic_rel :: \<open>nat multiset \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
  \<open>heuristic_rel \<A> = (\<lambda>(fast_ema, slow_ema, res_info, wasted, \<phi>). phase_save_heur_rel \<A> \<phi>)\<close>

definition save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics\<close> where
\<open>save_phase_heur L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, target, best)).
    (fast_ema, slow_ema, res_info, wasted, (\<phi>[L := b], target, best)))\<close>

definition save_phase_heur_pre :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>save_phase_heur_pre L b = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _)). L < length \<phi>)\<close>

definition mop_save_phase_heur :: \<open>nat \<Rightarrow> bool \<Rightarrow> restart_heuristics \<Rightarrow> restart_heuristics nres\<close> where
\<open>mop_save_phase_heur L b heur = do {
   ASSERT(save_phase_heur_pre L b heur);
   RETURN (save_phase_heur L b heur)
}\<close>

definition get_saved_phase_heur_pre :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur_pre L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _)). L < length \<phi>)\<close>

definition get_saved_phase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool\<close> where
\<open>get_saved_phase_heur L = (\<lambda>(fast_ema, slow_ema, res_info, wasted, (\<phi>, _)). \<phi>!L)\<close>

definition mop_get_saved_phase_heur :: \<open>nat \<Rightarrow> restart_heuristics \<Rightarrow> bool nres\<close> where
\<open>mop_get_saved_phase_heur L heur = do {
   ASSERT(get_saved_phase_heur_pre L heur);
   RETURN (get_saved_phase_heur L heur)
}\<close>

lemma heuristic_relI[intro!]:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_wasted wast heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (set_zero_wasted heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (incr_restart_phase heur)\<close>
  \<open>heuristic_rel \<A> heur \<Longrightarrow> heuristic_rel \<A> (save_phase_heur L b heur)\<close>
  by (auto simp: heuristic_rel_def save_phase_heur_def phase_save_heur_rel_def phase_saving_def)

lemma save_phase_heur_preI:
  \<open>heuristic_rel \<A> heur \<Longrightarrow> a \<in># \<A> \<Longrightarrow> save_phase_heur_pre a b heur\<close>
  by (auto simp: heuristic_rel_def phase_saving_def save_phase_heur_pre_def
     phase_save_heur_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)

paragraph \<open>Combining heuristics into a single component\<close>

paragraph \<open>VMTF\<close>

type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>

paragraph \<open>Options\<close>

type_synonym opts = \<open>bool \<times> bool \<times> bool\<close>


definition opts_restart where
  \<open>opts_restart = (\<lambda>(a, b, c). a)\<close>

definition opts_reduce where
  \<open>opts_reduce = (\<lambda>(a, b, c). b)\<close>

definition opts_unbounded_mode where
  \<open>opts_unbounded_mode = (\<lambda>(a, b, c). c)\<close>


paragraph \<open>Base state\<close>


type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym vdom = \<open>nat list\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>

(* TODO rename to isasat *)
type_synonym twl_st_wl_heur =
  \<open>trail_pol \<times> arena \<times>
    conflict_option_rel \<times> nat \<times> (nat watcher) list list \<times> isa_vmtf_remove_int \<times>
    nat \<times> conflict_min_cach_l \<times> lbd \<times> out_learned \<times> stats \<times> restart_heuristics \<times>
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

definition (in -) mop_watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher nres\<close> where
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

fun get_learned_count :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_learned_count (_, _, _, _, _, _, _, _, _, _, _, _, _, _, lcount, _) = lcount\<close>

fun get_ops :: \<open>twl_st_wl_heur \<Rightarrow> opts\<close> where
  \<open>get_ops (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, opts, _) = opts\<close>

fun get_old_arena :: \<open>twl_st_wl_heur \<Rightarrow> arena\<close> where
  \<open>get_old_arena (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, old_arena) = old_arena\<close>


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

text \<open>The following rule makes the previous one not applicable. Therefore, we do not mark this lemma as
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
  {((M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena),
     (M, N, D, NE, UE, NS, US, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE + NS + US)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms N (NE + UE + NS + US)) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE + NS + US))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE + NS + US)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms N (NE + UE + NS + US)) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_atms N (NE + UE + NS + US))  W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE + NS + US)) \<and>
    isasat_input_nempty (all_atms N (NE + UE + NS + US)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms N (NE + UE + NS + US)) heur
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
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def ac_simps)

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
  {((M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur, vdom,
       avdom, lcount, opts, old_arena),
      (M, N, D, NE, UE, NS, US, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE + NS + US)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms N (NE + UE + NS + US)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE + NS + US))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE + NS + US)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_atms N (NE + UE + NS + US)) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_atms N (NE + UE + NS + US)) W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE + NS + US)) \<and>
    isasat_input_nempty (all_atms N (NE + UE + NS + US)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms N (NE + UE + NS + US)) heur
  }\<close>

lemma twl_st_heur_twl_st_heur_conflict_ana:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_conflict_ana\<close>
  by (auto simp: twl_st_heur_def twl_st_heur_conflict_ana_def ac_simps)

lemma twl_st_heur_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_conflict_ana\<close>
  shows
    \<open>(get_trail_wl_heur S, get_trail_wl S') \<in> trail_pol (all_atms_st S')\<close> and
    \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st S') \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_conflict_ana_def by (auto simp: map_fun_rel_def ac_simps)

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a
separate array.\<close>
definition twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, clvls, cach, lbd, outl, stats, heur, vdom, avdom, lcount, opts,
       old_arena),
     (M, N, D, NE, UE, NS, US, Q, W)).
    (M', M) \<in> trail_pol (all_atms N (NE + UE + NS + US)) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', None) \<in> option_lookup_clause_rel (all_atms N (NE + UE + NS + US)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N (NE + UE + NS + US))) \<and>
    vm \<in> isa_vmtf (all_atms N (NE + UE + NS + US)) M \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty (all_atms N (NE + UE + NS + US)) cach \<and>
    out_learned M None outl \<and>
    lcount = size (learned_clss_l N) \<and>
    vdom_m (all_atms N (NE + UE + NS + US)) W N \<subseteq> set vdom \<and>
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE + NS + US)) \<and>
    isasat_input_nempty (all_atms N (NE + UE + NS + US)) \<and>
    old_arena = [] \<and>
    heuristic_rel (all_atms N (NE + UE + NS + US)) heur
  }\<close>


text \<open>
  The difference between \<^term>\<open>isasat_unbounded_assn\<close> and \<^term>\<open>isasat_bounded_assn\<close> corresponds to the
  following condition:
\<close>
definition isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<longleftrightarrow> (length (get_clauses_wl_heur S) \<le> sint64_max - (uint32_max div 2 + 6))\<close>

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> length (get_clauses_wl_heur S) \<le> sint64_max\<close>
  by (cases S) (auto simp: isasat_fast_def)


subsubsection \<open>Lift Operations to State\<close>

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

lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (atm_is_in_conflict_st_heur), uncurry (mop_lit_notin_conflict_wl)) \<in>
   [\<lambda>(L, S). True]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have 1: \<open>aaa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l A \<Longrightarrow> atm_of aaa  \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l A)\<close> for aaa A
    by (auto simp: atms_of_def)
  show ?thesis
  unfolding atm_is_in_conflict_st_heur_def twl_st_heur_def option_lookup_clause_rel_def uncurry_def comp_def
    mop_lit_notin_conflict_wl_def
  apply (intro frefI nres_relI)
  apply refine_rcg
  apply clarsimp
  subgoal
     apply (rule atm_in_conflict_lookup_pre)
     unfolding \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits[symmetric]
     apply assumption+
     apply (auto simp: ac_simps)
     done
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


subsection \<open>More theorems\<close>

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
  using phase_save_heur_rel_cong[of \<A> \<B> \<open>(\<lambda>(_, _, _, _, a). a) heur\<close>]
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

    (*TODO Move + replace distinct_subseteq_iff*)
lemma distinct_subseteq_iff2:
  assumes dist: "distinct_mset M"
  shows "set_mset M \<subseteq> set_mset N \<longleftrightarrow> M \<subseteq># N"
proof
  assume "set_mset M \<subseteq> set_mset N"
  then show "M \<subseteq># N"
    using dist by (metis distinct_mset_set_mset_ident mset_set_subset_iff)
next
  assume "M \<subseteq># N"
  then show "set_mset M \<subseteq> set_mset N"
    by (metis set_mset_mono)
qed

lemma cach_refinement_empty_cong:
  \<open>set_mset \<A> = set_mset \<B> \<Longrightarrow> cach_refinement_empty \<A> = cach_refinement_empty \<B>\<close>
  using  \<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_cong[of \<A> \<B>]
  by (force simp: cach_refinement_empty_def cach_refinement_alt_def
    distinct_subseteq_iff2[symmetric] intro!: ext)

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
lemma eq_insertD: \<open>A = insert a B \<Longrightarrow> a \<in> A \<and> B \<subseteq> A\<close>
  by auto

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset:
  \<open>set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (add_mset L C)) = insert (Pos L) (insert (Neg L) (set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l C)))\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

(*END Move*)


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
        simp flip: all_atms_def
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
      ASSERT(i < length vdom);
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        L1 \<leftarrow> mop_arena_lit2 arena C 0;
        L2 \<leftarrow> mop_arena_lit2 arena C 1;
        n \<leftarrow> mop_arena_length arena C;
        let b = (n = 2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        W \<leftarrow> mop_append_ll W L1 (C, L2, b);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
        W \<leftarrow> mop_append_ll W L2 (C, L1, b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>

lemma rewatch_heur_rewatch:
  assumes
    valid: \<open>valid_arena arena N vdom\<close> and \<open>set xs \<subseteq> vdom\<close> and \<open>distinct xs\<close> and \<open>set_mset (dom_m N) \<subseteq> set xs\<close> and
    \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and lall: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    \<open>vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)\<close>
  shows
    \<open>rewatch_heur xs arena W \<le> \<Down> ({(W, W'). (W, W') \<in>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)}) (rewatch N W')\<close>
proof -
  have [refine0]: \<open>(xs, xsa) \<in> Id \<Longrightarrow>
     ([0..<length xs], [0..<length xsa]) \<in> \<langle>{(x, x'). x = x' \<and> x < length xsa \<and> xs!x \<in> vdom}\<rangle>list_rel\<close>
    for xsa
    using assms unfolding list_rel_def
    by (auto simp: list_all2_same)
  show ?thesis
    unfolding rewatch_heur_def rewatch_def
    apply (subst (2) nfoldli_nfoldli_list_nth)
    apply (refine_vcg mop_arena_lit[OF valid] mop_append_ll[of \<A>, THEN fref_to_Down_curry2, unfolded comp_def]
       mop_arena_length[of vdom, THEN fref_to_Down_curry, unfolded comp_def])
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal by fast
    subgoal by auto
    subgoal
      using assms
      unfolding arena_is_valid_clause_vdom_def
      by blast
    subgoal
      using assms
      by (auto simp: arena_dom_status_iff)
    subgoal for xsa xi x si s
      using assms
      by auto
    subgoal by simp
    subgoal by linarith
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (auto)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for xsa xi x si s
      using assms
      unfolding arena_is_valid_clause_idx_and_access_def
        arena_is_valid_clause_idx_def
      by (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using valid_arena_size_dom_m_le_arena[OF assms(1)] assms
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 0]
      by (auto simp: map_fun_rel_def arena_lifting)
    subgoal for xsa xi x si s
      using valid_arena_size_dom_m_le_arena[OF assms(1)] assms
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 0]
      by (auto simp: map_fun_rel_def arena_lifting)
    subgoal using assms by (simp add: arena_lifting)
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1]
      assms valid_arena_size_dom_m_le_arena[OF assms(1)]
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1]
        assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    done
qed

lemma rewatch_heur_alt_def:
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      ASSERT(i < length vdom);
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        L1 \<leftarrow> mop_arena_lit2 arena C 0;
        L2 \<leftarrow> mop_arena_lit2 arena C 1;
        n \<leftarrow> mop_arena_length arena C;
        let b = (n = 2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        W \<leftarrow> mop_append_ll W L1 (C, L2, b);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
        W \<leftarrow> mop_append_ll W L2 (C, L1, b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>
  unfolding Let_def rewatch_heur_def
  by auto

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
     (M, N, D, NE, UE, NS, US, Q, W) \<leftarrow> RETURN S;
     W \<leftarrow> rewatch N W;
     RETURN ((M, N, D, NE, UE, NS, US, Q, W))
  }\<close>


fun remove_watched_wl :: \<open>'v twl_st_wl \<Rightarrow> _\<close> where
  \<open>remove_watched_wl (M, N, D, NE, UE, NS, US, Q, _) = (M, N, D, NE, UE, NS, US, Q)\<close>

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
    apply (cases S, case_tac \<open>rewatch b i\<close>)
    by (auto simp: RES_RETURN_RES)
  subgoal
    using rewatch_correctness[OF assms]
    unfolding rewatch_st_def
    apply (cases S, case_tac \<open>rewatch b i\<close>)
    by (force simp: RES_RETURN_RES)+
  done

subsection \<open>Fast to slow conversion\<close>
text \<open>Setup to convert a list from \<^typ>\<open>64 word\<close> to \<^typ>\<open>nat\<close>.\<close>
definition convert_wlists_to_nat_conv :: \<open>'a list list \<Rightarrow> 'a list list\<close> where
  \<open>convert_wlists_to_nat_conv = id\<close>

abbreviation twl_st_heur''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur'' \<D> r \<equiv> {(S, T). (S, T) \<in> twl_st_heur' \<D> \<and>
           length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_up''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
  \<open>twl_st_heur_up'' \<D> r s L \<equiv> {(S, T). (S, T) \<in> twl_st_heur'' \<D> r \<and>
     length (watched_by T L) = s \<and> s \<le> r}\<close>

lemma length_watched_le:
  assumes
    prop_inv: \<open>correct_watching x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur'' \<D>1 r\<close> and
    x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - 4\<close>
proof -
  have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using prop_inv x2 unfolding all_atms_def all_lits_def
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps ac_simps)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (get_clauses_wl x1)
      (get_unit_clauses_wl x1 + get_subsumed_clauses_wl x1))\<close>
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
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {4..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - 4\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

lemma length_watched_le2:
  assumes
    prop_inv: \<open>correct_watching_except i j L x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur'' \<D>1 r\<close> and
    x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close> and diff: \<open>L \<noteq> x2\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - 4\<close>
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
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (get_clauses_wl x1) (get_unit_clauses_wl x1 + get_subsumed_clauses_wl x1))\<close>
    using x2 xb_x'a
    by (auto simp flip: all_atms_def all_lits_alt_def2 simp: ac_simps)

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
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def ac_simps simp flip: all_atms_def all_lits_alt_def2
        dest!: multi_member_split)
  have watched_incl: \<open>mset (map fst (watched_by x1 x2)) \<subseteq># mset (get_vdom x1a)\<close>
    by (rule distinct_subseteq_iff[THEN iffD1])
      (use dist[unfolded distinct_watched_alt_def] dist_vdom subset in
         \<open>simp_all flip: distinct_mset_mset_distinct\<close>)
  have vdom_incl: \<open>set (get_vdom x1a) \<subseteq> {4..< length (get_clauses_wl_heur x1a)}\<close>
    using valid_arena_in_vdom_le_arena[OF valid] arena_dom_status_iff[OF valid] by auto

  have \<open>length (get_vdom x1a) \<le> length (get_clauses_wl_heur x1a) - 4\<close>
    by (subst distinct_card[OF dist_vdom, symmetric])
      (use card_mono[OF _ vdom_incl] in auto)
  then show ?thesis
    using size_mset_mono[OF watched_incl] xb_x'a
    by (auto intro!: order_trans[of \<open>length (watched_by x1 x2)\<close> \<open>length (get_vdom x1a)\<close>])
qed

lemma atm_of_all_lits_of_m: \<open>atm_of `# (all_lits_of_m C) = atm_of `# C + atm_of `# C\<close>
   \<open>atm_of ` set_mset (all_lits_of_m C) = atm_of `set_mset C \<close>
  by (induction C; auto simp: all_lits_of_m_add_mset)+


(* TODO Move in this buffer *)
lemma mop_watched_by_app_heur_mop_watched_by_at:
   \<open>(uncurry2 mop_watched_by_app_heur, uncurry2 mop_watched_by_at) \<in>
    twl_st_heur \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding mop_watched_by_app_heur_def mop_watched_by_at_def uncurry_def all_lits_def[symmetric] all_lits_alt_def[symmetric]
  by (intro frefI nres_relI, refine_rcg,
     auto simp: twl_st_heur_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits map_fun_rel_def
      simp flip: all_lits_alt_def2)
    (auto simp: add.assoc)

lemma mop_watched_by_app_heur_mop_watched_by_at'':
   \<open>(uncurry2 mop_watched_by_app_heur, uncurry2 mop_watched_by_at) \<in>
    twl_st_heur_up'' \<D> r s K \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  by (rule fref_mono[THEN set_mp, OF _ _ _ mop_watched_by_app_heur_mop_watched_by_at])
    (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits twl_st_heur'_def map_fun_rel_def)


definition mop_polarity_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>mop_polarity_pol = (\<lambda>M L. do {
    ASSERT(polarity_pol_pre M L);
    RETURN (polarity_pol M L)
  })\<close>

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
  apply (refine_rcg polarity_pol_polarity[of \<open>all_atms _ _\<close>, THEN fref_to_Down_unRET_uncurry])
  apply (auto simp: twl_st_heur_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits ac_simps
    intro!: polarity_pol_pre simp flip: all_atms_def)
  done

lemma mop_polarity_st_heur_mop_polarity_wl'':
   \<open>(uncurry mop_polarity_st_heur, uncurry mop_polarity_wl) \<in>
   [\<lambda>_. True]\<^sub>f twl_st_heur_up'' \<D> r s K \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  by (rule fref_mono[THEN set_mp, OF _ _ _ mop_polarity_st_heur_mop_polarity_wl])
    (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits twl_st_heur'_def map_fun_rel_def)

(* TODO Kill lhs*)
lemma [simp,iff]: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st S) S \<longleftrightarrow> blits_in_\<L>\<^sub>i\<^sub>n S\<close>
  unfolding literals_are_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def \<L>\<^sub>a\<^sub>l\<^sub>l_all_atms_all_lits
  by auto


definition length_avdom :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>length_avdom S = length (get_avdom S)\<close>

lemma length_avdom_alt_def:
  \<open>length_avdom = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
    vdom, avdom, lcount). length avdom)\<close>
  by (intro ext) (auto simp: length_avdom_def)


definition clause_is_learned_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool"
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
definition clause_lbd_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat"
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


definition mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts, old_arena).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts, old_arena))\<close>

definition mark_garbage_heur2 :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>mark_garbage_heur2 C = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, lcount, opts). do{
    let st = arena_status N' C = IRRED;
    ASSERT(\<not>st \<longrightarrow> lcount \<ge> 1);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl, stats, heur,
       vdom, avdom, if st then lcount else lcount - 1, opts) })\<close>

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
    ASSERT(mark_garbage_pre (get_clauses_wl_heur S, C) \<and> get_learned_count S \<ge> 1 \<and> i < length (get_avdom S));
    RETURN (mark_garbage_heur C i S)
  })\<close>

definition mark_unused_st_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_unused_st_heur C = (\<lambda>(M', N', D', j, W', vm, clvls, cach, lbd, outl,
      stats, heur, vdom, avdom, lcount, opts).
    (M', arena_decr_act (mark_unused N' C) C, D', j, W', vm, clvls, cach,
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
       stats, heur, vdom, avdom, lcount, opts, old_arena), C) \<and> lcount \<ge> 1 \<and> i < length avdom);
    RETURN (M', extra_information_mark_to_delete N' C, D', j, W', vm, clvls, cach, lbd, outl,
      stats, heur,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts, old_arena)
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

text \<open>
  I also played with \<^term>\<open>ema_reinit fast_ema\<close> and  \<^term>\<open>ema_reinit slow_ema\<close>. Currently removed,
  to test the performance, I remove it.
\<close>
definition incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
       res_info, wasted), vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, clvls, cach, lbd, outl, incr_restart stats,
       (fast_ema, slow_ema,
       restart_info_restart_done res_info, wasted), vdom, avdom, lcount)
  })\<close>

definition incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, clvls, cach, lbd, outl, stats, (fast_ema, slow_ema,
     res_info, wasted), vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, clvls, cach, lbd, outl, incr_lrestart stats,
       (fast_ema, slow_ema, restart_info_restart_done res_info, wasted),
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

definition isasat_length_trail_st :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>isasat_length_trail_st S = isa_length_trail (get_trail_wl_heur S)\<close>

lemma isasat_length_trail_st_alt_def:
  \<open>isasat_length_trail_st = (\<lambda>(M, _). isa_length_trail M)\<close>
  by (auto simp: isasat_length_trail_st_def intro!: ext)


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


definition mop_marked_as_used_st :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres\<close> where
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

text \<open>In an attempt to avoid using @{thm ac_simps} everywhere.\<close>
lemma all_lits_simps[simp]:
  \<open>all_lits N ((NE + UE) + (NS + US)) = all_lits N (NE + UE + NS + US)\<close>
  \<open>all_atms N ((NE + UE) + (NS + US)) = all_atms N (NE + UE + NS + US)\<close>
  by (auto simp: ac_simps)

end
