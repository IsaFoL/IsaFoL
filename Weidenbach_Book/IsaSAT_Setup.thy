theory IsaSAT_Setup
  imports
    Watched_Literals_VMTF
    Watched_Literals.Watched_Literals_Watch_List_Initialisation 
    IsaSAT_Lookup_Conflict 
    IsaSAT_Clauses IsaSAT_Arena IsaSAT_Watch_List LBD
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


paragraph \<open>Moving averages\<close>

text \<open>We use (at least hopefully) the variant of EMA-14 implemented in Cadical, but with fixed-point
calculation (\<^term>\<open>1 :: nat\<close> is \<^term>\<open>(1 :: nat) >> 32\<close>).

Remark that the coefficient \<^term>\<open>\<beta>\<close> already should not take care of the fixed-point conversion of the glue.
Otherwise, \<^term>\<open>value\<close> is wrongly updated.
\<close>
type_synonym ema = \<open>uint64 \<times> uint64 \<times> uint64 \<times> uint64 \<times> uint64\<close>

definition ema_bitshifting where
  \<open>ema_bitshifting = (1 << 32)\<close>


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

definition (in -) ema_init :: \<open>uint64 \<Rightarrow> ema\<close> where
  \<open>ema_init \<alpha> = (0, \<alpha>, ema_bitshifting, 0, 0)\<close>

fun ema_reinit where
  \<open>ema_reinit (value, \<alpha>, \<beta>, wait, period) = (value, \<alpha>, 1 << 32, 0, 0)\<close>

fun ema_get_value :: \<open>ema \<Rightarrow> uint64\<close> where
  \<open>ema_get_value (v, _) = v\<close>

text \<open>We use the default values for Cadical: \<^term>\<open>(3 / 10 ^2)\<close> and  \<^term>\<open>(1 / 10 ^ 5)\<close>  in our fixed-point
  version.
\<close>

abbreviation ema_fast_init :: ema where
  \<open>ema_fast_init \<equiv> ema_init (128849010)\<close>

abbreviation ema_slow_init :: ema where
  \<open>ema_slow_init \<equiv> ema_init 429450\<close>


paragraph \<open>Information related to restarts\<close>

type_synonym restart_info = \<open>uint64 \<times> uint64\<close>

definition incr_conflict_count_since_last_restart :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>incr_conflict_count_since_last_restart = (\<lambda>(ccount, ema_lvl). (ccount + 1, ema_lvl))\<close>

definition restart_info_update_lvl_avg :: \<open>uint32 \<Rightarrow> restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_update_lvl_avg = (\<lambda>lvl (ccount, ema_lvl). (ccount, ema_lvl))\<close>

definition restart_info_init :: \<open>restart_info\<close> where
  \<open>restart_info_init = (0, 0)\<close>

definition restart_info_restart_done :: \<open>restart_info \<Rightarrow> restart_info\<close> where
  \<open>restart_info_restart_done = (\<lambda>(ccount, lvl_avg). (0, lvl_avg))\<close>


paragraph \<open>VMTF\<close>

type_synonym vmtf_assn = \<open>(uint32, uint64) vmtf_node array \<times> uint64 \<times> uint32 \<times> uint32 \<times> uint32 option\<close>

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

type_synonym (in -) isa_vmtf_remove_int = \<open>vmtf \<times> (nat list \<times> bool list)\<close>


paragraph \<open>Options\<close>

type_synonym opts = \<open>bool \<times> bool \<times> bool\<close>


definition opts_restart where
  \<open>opts_restart = (\<lambda>(a, b). a)\<close>

definition opts_reduce where
  \<open>opts_reduce = (\<lambda>(a, b, c). b)\<close>

definition opts_unbounded_mode where
  \<open>opts_unbounded_mode = (\<lambda>(a, b, c). c)\<close>


paragraph \<open>Base state\<close>

type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array \<times> nat\<close>
type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym vdom = \<open>nat list\<close>

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


text \<open>Setup to convert a list from \<^typ>\<open>uint64\<close> to \<^typ>\<open>nat\<close>.\<close>
definition arl_copy_to :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
\<open>arl_copy_to R xs = map R xs\<close>

definition op_map_to
  :: \<open>('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list list \<Rightarrow> nat \<Rightarrow> 'a list list nres\<close>
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
    mset avdom \<subseteq># mset vdom \<and>
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
    mset avdom \<subseteq># mset vdom \<and>
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
    mset avdom \<subseteq># mset vdom \<and>
    distinct vdom \<and>
    isasat_input_bounded (all_atms N (NE + UE)) \<and>
    isasat_input_nempty (all_atms N (NE + UE)) \<and>
    old_arena = []
  }\<close>


text \<open>
  The difference between \<^term>\<open>isasat_unbounded_assn\<close> and \<^term>\<open>isasat_bounded_assn\<close> corresponds to the
  following condition:
\<close>
definition isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<longleftrightarrow> (length (get_clauses_wl_heur S) \<le> uint64_max - (uint32_max div 2 + 6))\<close>

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> length (get_clauses_wl_heur S) \<le> uint64_max\<close>
  by (cases S) (auto simp: isasat_fast_def)


subsubsection \<open>Lift Operations to State\<close>

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur = (\<lambda>(M, N, (b, _), Q, W, _). b)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
  \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro WB_More_Refinement.frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
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
  by (intro WB_More_Refinement.frefI nres_relI)
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

lemma access_lit_in_clauses_heur_fast_pre:
  \<open>arena_lit_pre (get_clauses_wl_heur a) (ba + b) \<Longrightarrow>
    isasat_fast a \<Longrightarrow> ba + b \<le> uint64_max\<close>
  by (auto simp: arena_lit_pre_def arena_is_valid_clause_idx_and_access_def
      dest!: arena_lifting(10)
      dest!: isasat_fast_length_leD)[]

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
        ASSERT(L1 \<noteq> L2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        let W = append_ll W (nat_of_lit L1) (to_watcher C L2 b);
        ASSERT(nat_of_lit L2 < length W);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
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
    subgoal using assms by (auto simp: arena_lifting)
    subgoal for xsa xi x si s using valid_arena_size_dom_m_le_arena[OF assms(1)]
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 0] assms by (auto simp: map_fun_rel_def arena_lifting)
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1] assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s using valid_arena_size_dom_m_le_arena[OF assms(1)]
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1] assms
      by (auto simp: map_fun_rel_def arena_lifting append_ll_def)
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
        ASSERT(L1 \<noteq> L2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        let W = append_ll W (nat_of_lit L1) (to_watcher C L2 b);
        ASSERT(nat_of_lit L2 < length W);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
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

definition rewatch_heur_st_fast_pre where
  \<open>rewatch_heur_st_fast_pre S =
     ((\<forall>x \<in> set (get_vdom S). x \<le> uint64_max) \<and> length (get_clauses_wl_heur S) \<le> uint64_max)\<close>

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

subsection \<open>Fast to slow conversion\<close>
text \<open>Setup to convert a list from \<^typ>\<open>uint64\<close> to \<^typ>\<open>nat\<close>.\<close>
definition convert_wlists_to_nat_conv :: \<open>'a list list \<Rightarrow> 'a list list\<close> where
  \<open>convert_wlists_to_nat_conv = id\<close>

definition isasat_fast_slow :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>isasat_fast_slow =
    (\<lambda>(M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, avdom, lcount, opts, old_arena).
      RETURN (trail_pol_slow_of_fast M', N', D', Q', convert_wlists_to_nat_conv W', vm, \<phi>,
        clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, avdom, nat_of_uint64_conv lcount, opts, old_arena))\<close>

definition (in -)isasat_fast_slow_wl_D where
  \<open>isasat_fast_slow_wl_D = id\<close>

lemma isasat_fast_slow_alt_def:
  \<open>isasat_fast_slow S = RETURN S\<close>
  by (cases S)
    (auto simp: isasat_fast_slow_def trail_slow_of_fast_def convert_wlists_to_nat_conv_def
      trail_pol_slow_of_fast_alt_def)

lemma isasat_fast_slow_isasat_fast_slow_wl_D:
  \<open>(isasat_fast_slow, RETURN o isasat_fast_slow_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI WB_More_Refinement.frefI)
    (auto simp: isasat_fast_slow_alt_def isasat_fast_slow_wl_D_def)


abbreviation twl_st_heur''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur'' \<D> r \<equiv> {(S, T). (S, T) \<in> twl_st_heur' \<D> \<and>
           length (get_clauses_wl_heur S) = r}\<close>

abbreviation twl_st_heur_up''
   :: \<open>nat multiset \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
  \<open>twl_st_heur_up'' \<D> r s L \<equiv> {(S, T). (S, T) \<in> twl_st_heur'' \<D> r \<and>
     length (watched_by T L) = s}\<close>

lemma length_watched_le:
  assumes
    prop_inv: \<open>correct_watching x1\<close> and
    xb_x'a: \<open>(x1a, x1) \<in> twl_st_heur'' \<D>1 r\<close> and
    x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1)\<close>
  shows \<open>length (watched_by x1 x2) \<le> r - 4\<close>
proof -
  have \<open>correct_watching x1\<close>
    using prop_inv unfolding unit_propagation_outer_loop_wl_D_inv_def
      unit_propagation_outer_loop_wl_inv_def
    by auto
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using x2 unfolding all_atms_def all_lits_def
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (get_clauses_wl x1) (get_unit_clauses_wl x1))\<close>
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
      (auto simp: twl_st_heur_def twl_st_heur'_def all_atms_def[symmetric])
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def simp flip: all_atms_def
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
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching_except.simps)
  then have dist: \<open>distinct_watched (watched_by x1 x2)\<close>
    using xb_x'a
    by (cases x1; auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm correct_watching.simps)
  have dist_vdom: \<open>distinct (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def)
  have x2: \<open>x2 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms (get_clauses_wl x1) (get_unit_clauses_wl x1))\<close>
    using x2 xb_x'a
    by (auto simp flip: all_atms_def)

  have
      valid: \<open>valid_arena (get_clauses_wl_heur x1a) (get_clauses_wl x1) (set (get_vdom x1a))\<close>
    using xb_x'a unfolding all_atms_def all_lits_def
    by (cases x1)
     (auto simp: twl_st_heur'_def twl_st_heur_def)

  have \<open>vdom_m (all_atms_st x1) (get_watched_wl x1) (get_clauses_wl x1) \<subseteq> set (get_vdom x1a)\<close>
    using xb_x'a
    by (cases x1)
      (auto simp: twl_st_heur_def twl_st_heur'_def simp flip: all_atms_def)
  then have subset: \<open>set (map fst (watched_by x1 x2)) \<subseteq> set (get_vdom x1a)\<close>
    using x2 unfolding vdom_m_def
    by (cases x1)
      (force simp: twl_st_heur'_def twl_st_heur_def simp flip: all_atms_def
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
end
