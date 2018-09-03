theory IsaSAT_Setup
  imports IsaSAT_Clauses IsaSAT_Arena
    Watched_Literals_VMTF IsaSAT_Lookup_Conflict LBD IsaSAT_Watch_List
begin

no_notation Ref.update ("_ := _" 62)

subsection \<open>Code Generation\<close>

subsubsection \<open>Types and Refinement Relations\<close>

paragraph \<open>Statistics\<close>

text \<open>
We do some statistics on the run. NB: the statistics are not proven correct (especially they might
overflow), there are just there to look for regressions and do some comparisons.
\<close>
type_synonym stats = \<open>uint64 \<times> uint64 \<times> uint64 \<times> uint64\<close>

abbreviation stats_assn where
  \<open>stats_assn \<equiv> uint64_assn *a uint64_assn *a uint64_assn *a uint64_assn\<close>

definition incr_propagation :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_propagation = (\<lambda>(propa, confl, dec). (propa + 1, confl, dec))\<close>

definition incr_conflict :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_conflict = (\<lambda>(propa, confl, dec). (propa, confl + 1, dec))\<close>

definition incr_decision :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_decision = (\<lambda>(propa, confl, dec, res). (propa, confl, dec + 1, res))\<close>

definition incr_restart :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_restart = (\<lambda>(propa, confl, dec, res). (propa, confl, dec, res + 1))\<close>

lemma one_uint64_hnr: \<open>(uncurry0 (return 1), uncurry0 (RETURN 1)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

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


paragraph \<open>Base state\<close>

type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array \<times> nat\<close>
type_synonym out_learned = \<open>nat clause_l\<close>
type_synonym ema = \<open>uint64\<close>
abbreviation ema_assn :: \<open>ema \<Rightarrow> ema \<Rightarrow> assn\<close> where
  \<open>ema_assn \<equiv> uint64_assn\<close>

type_synonym conflict_count = \<open>uint32\<close>
abbreviation conflict_count_assn :: \<open>conflict_count \<Rightarrow> conflict_count \<Rightarrow> assn\<close> where
  \<open>conflict_count_assn \<equiv> uint32_assn\<close>

type_synonym vdom = \<open>nat list\<close>

abbreviation vdom_assn :: \<open>vdom \<Rightarrow> nat array_list \<Rightarrow> assn\<close> where
  \<open>vdom_assn \<equiv> arl_assn nat_assn\<close>

type_synonym vdom_assn = \<open>nat array_list\<close>

type_synonym isasat_clauses_assn = \<open>uint32 array_list\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom_assn \<times> nat\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom_assn \<times> nat\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
(* TODO rename to isasat *)
type_synonym twl_st_wl_heur =
  \<open>(nat,nat)ann_lits \<times> arena \<times>
    conflict_option_rel \<times> nat \<times> (nat watcher) list list \<times> vmtf_remove_int \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom \<times> nat\<close>

fun get_clauses_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> arena\<close> where
  \<open>get_clauses_wl_heur (M, N, D, _) = N\<close>

fun get_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur (M, N, D, _) = M\<close>

fun get_conflict_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> conflict_option_rel\<close> where
  \<open>get_conflict_wl_heur (_, _, D, _) = D\<close>

fun watched_by_int :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat watched\<close> where
  \<open>watched_by_int (M, N, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat watcher) list list\<close> where
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

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> vmtf_remove_int\<close> where
  \<open>get_vmtf_heur (_, _, _, _, _, vm, _) = vm\<close>

fun get_phase_saver_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool list\<close> where
  \<open>get_phase_saver_heur (_, _, _, _, _, _, \<phi>, _) = \<phi>\<close>

fun get_count_max_lvls_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_count_max_lvls_heur (_, _, _, _, _, _, _, clvls, _) = clvls\<close>

fun get_conflict_cach:: \<open>twl_st_wl_heur \<Rightarrow> nat conflict_min_cach\<close> where
  \<open>get_conflict_cach (_, _, _, _, _, _, _, _, cach, _) = cach\<close>

fun get_lbd :: \<open>twl_st_wl_heur \<Rightarrow> lbd\<close> where
  \<open>get_lbd (_, _, _, _, _, _, _, _, _, lbd, _) = lbd\<close>

fun get_outlearned_heur :: \<open>twl_st_wl_heur \<Rightarrow> out_learned\<close> where
  \<open>get_outlearned_heur (_, _, _, _, _, _, _, _, _, _, out, _) = out\<close>

fun get_fast_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_fast_ema_heur (_, _, _, _, _, _, _, _, _, _, _, _, fast_ema, _) = fast_ema\<close>

fun get_slow_ema_heur :: \<open>twl_st_wl_heur \<Rightarrow> ema\<close> where
  \<open>get_slow_ema_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, slow_ema, _) = slow_ema\<close>

fun get_conflict_count_heur :: \<open>twl_st_wl_heur \<Rightarrow> uint32\<close> where
  \<open>get_conflict_count_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, ccount, _) = ccount\<close>

fun get_vdom :: \<open>twl_st_wl_heur \<Rightarrow> nat list\<close> where
  \<open>get_vdom (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, vdom, _) = vdom\<close>

fun get_learned_count :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_learned_count (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lcount) = lcount\<close>

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

(* TODO n should also be sued in the condition *)
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
             _ \<leftarrow> ASSERT (i < length zs);
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


context isasat_input_ops
begin

text \<open>The virtual domain is composed of the addressable (and accessible) elements, i.e.,
  the domain and all the deleted clauses that are still present in the watch lists.
\<close>
definition vdom_m :: \<open>(nat literal \<Rightarrow> (nat \<times> _) list) \<Rightarrow> (nat, 'b) fmap \<Rightarrow> nat set\<close> where
  \<open>vdom_m W N = \<Union>(((`) fst) ` set ` W ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l) \<union> set_mset (dom_m N)\<close>

lemma vdom_m_simps[simp]:
  \<open>bh \<in># dom_m N \<Longrightarrow> vdom_m W (N(bh \<hookrightarrow> C)) = vdom_m W N\<close>
  \<open>bh \<notin># dom_m N \<Longrightarrow> vdom_m W (N(bh \<hookrightarrow> C)) = insert bh (vdom_m W N)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps2[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow> vdom_m (W(L := W L @ [(i, C)])) N = vdom_m W N\<close>
  \<open>bi \<in># dom_m ax \<Longrightarrow> vdom_m (bp(L:= bp L @ [(bi, av')])) ax = vdom_m bp ax\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma vdom_m_simps3[simp]:
  \<open>fst biav' \<in># dom_m ax \<Longrightarrow> vdom_m (bp(L:= bp L @ [biav'])) ax = vdom_m bp ax\<close>
  by (cases biav'; auto simp: dest: multi_member_split[of L] split: if_splits)

text \<open>What is the difference with the next lemma?\<close>
lemma (in isasat_input_ops) [simp]:
  \<open>bf \<in># dom_m ax \<Longrightarrow>
       vdom_m bj (ax(bf \<hookrightarrow> C')) = vdom_m bj (ax)\<close>
  by (force simp: vdom_m_def split: if_splits)+

lemma (in isasat_input_ops) vdom_m_simps4[simp]:
  \<open>i \<in># dom_m N \<Longrightarrow>
     vdom_m (W (L1 := W L1 @ [(i, C1)], L2 := W L2 @ [(i, C2)])) N = vdom_m W N\<close>
 by (force simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)

text \<open>The following rule makes the previous not applicable. Therefore, we do not mark this lemma as
simp.\<close>
lemma (in isasat_input_ops) vdom_m_simps5:
  \<open>i \<notin># dom_m N \<Longrightarrow> vdom_m W (fmupd i C N) = insert i (vdom_m W N)\<close>
  by (force simp: vdom_m_def image_iff dest: multi_member_split split: if_splits)


lemma in_watch_list_in_vdom:
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and \<open>w < length (watched_by S L)\<close>
  shows \<open>fst (watched_by S L ! w) \<in> vdom_m (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)


lemma in_watch_list_in_vdom':
  assumes \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and \<open>A \<in> set (watched_by S L)\<close>
  shows \<open>fst A \<in> vdom_m (get_watched_wl S) (get_clauses_wl S)\<close>
  using assms
  unfolding vdom_m_def
  by (cases S) (auto dest: multi_member_split)

lemma in_dom_in_vdom[simp]:
  \<open>x \<in># dom_m N \<Longrightarrow> x \<in> vdom_m W N\<close>
  unfolding vdom_m_def
  by (auto dest: multi_member_split)

definition vdom_m_heur :: \<open>((nat \<times> _) list list) \<Rightarrow> (nat, 'b) fmap \<Rightarrow> nat set\<close> where
  \<open>vdom_m_heur W N = \<Union>(((`) fst) ` set ` (!) W ` nat_of_lit ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l) \<union> set_mset (dom_m N)\<close>

definition cach_refinement_empty where
  \<open>cach_refinement_empty cach \<longleftrightarrow>
     (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. cach L = SEEN_UNKNOWN)\<close>

text \<open>\<^term>\<open>vdom\<close> is an upper bound on all the address of the clauses that are used in the
state.\<close>
definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m W N \<subseteq> set vdom
  }\<close>

lemma twl_st_heur_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur\<close>
  shows
     \<open>get_trail_wl_heur S = get_trail_wl S'\<close> and
     twl_st_heur_state_simp_watched: \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> watched_by_int S C = watched_by S' C\<close> and
     \<open>literals_to_update_wl S' =
         uminus `# lit_of `# mset (drop (literals_to_update_wl_heur S) (rev (get_trail_wl S')))\<close>
  using assms unfolding twl_st_heur_def by (auto simp: map_fun_rel_def)

definition twl_st_heur' :: \<open>nat multiset \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur' N = {(S, S'). (S, S') \<in> twl_st_heur \<and> dom_m (get_clauses_wl S') = N}\<close>

definition (in isasat_input_ops) twl_st_heur_conflict_ana
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_conflict_ana =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount, vdom,
       lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and> valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m W N \<subseteq> set vdom
  }\<close>

lemma twl_st_heur_twl_st_heur_conflict_ana:
  \<open>(S, T) \<in> twl_st_heur \<Longrightarrow> (S, T) \<in> twl_st_heur_conflict_ana\<close>
  by (auto simp: twl_st_heur_def twl_st_heur_conflict_ana_def)

lemma twl_st_heur_ana_state_simp:
  assumes \<open>(S, S') \<in> twl_st_heur_conflict_ana\<close>
  shows
    \<open>get_trail_wl_heur S = get_trail_wl S'\<close> and
    \<open>C \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> watched_by_int S C = watched_by S' C\<close>
  using assms unfolding twl_st_heur_conflict_ana_def by (auto simp: map_fun_rel_def)

text \<open>This relations decouples the conflict that has been minimised and appears abstractly
from the refined state, where the conflict has been removed from the data structure to a
separate array.\<close>
definition (in isasat_input_ops) twl_st_heur_bt :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_bt =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, _, _, _, vdom, lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and>
    valid_arena N' N (set vdom) \<and>
    (D', None) \<in> option_lookup_clause_rel \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M None \<and>
    cach_refinement_empty cach \<and>
    out_learned M None outl \<and>
    lcount = size (learned_clss_l N) \<and>
    vdom_m W N \<subseteq> set vdom
  }\<close>


definition isasat_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>isasat_assn =
  trail_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_assn *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  ema_assn *a
  ema_assn *a
  conflict_count_assn *a
  vdom_assn *a
  nat_assn\<close>

definition isasat_fast_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_fast_assn =
  trail_fast_assn *a arena_assn *a
  isasat_conflict_assn *a
  uint32_nat_assn *a
  watchlist_fast_assn *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn *a
  ema_assn *a
  ema_assn *a
  conflict_count_assn *a
  vdom_assn *a
  nat_assn\<close>

text \<open>
  The difference between \<^term>\<open>isasat_assn\<close> and \<^term>\<open>isasat_fast_assn\<close> corresponds to the
  following condition:
\<close>
definition (in -) isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<longleftrightarrow> (length (get_clauses_wl_heur S) \<le> uint64_max - (uint32_max + 5))\<close>

lemma isasat_fast_length_leD: \<open>isasat_fast S \<Longrightarrow> length (get_clauses_wl_heur S) \<le> uint64_max\<close>
  by (cases S) (auto simp: isasat_fast_def)

definition isasat_fast_slow :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>isasat_fast_slow =
    (\<lambda>(M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount).
      RETURN (trail_slow_of_fast M', N', D', Q', convert_wlists_to_nat_conv W', vm, \<phi>,
        clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount))\<close>

sepref_thm isasat_fast_slow_code
  is \<open>isasat_fast_slow\<close>
  :: \<open>isasat_fast_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_fast_assn_def isasat_assn_def isasat_fast_slow_def
  by sepref

concrete_definition (in -) isasat_fast_slow_code
  uses isasat_input_ops.isasat_fast_slow_code.refine_raw
  is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) isasat_fast_slow_code_def

lemmas isasat_fast_slow_code[sepref_fr_rules] =
   isasat_fast_slow_code.refine

definition (in -)isasat_fast_slow_wl_D where
  \<open>isasat_fast_slow_wl_D = id\<close>

lemma isasat_fast_slow_alt_def:
  \<open>isasat_fast_slow S = RETURN S\<close>
  by (cases S)
    (auto simp: isasat_fast_slow_def trail_slow_of_fast_def convert_wlists_to_nat_conv_def)

lemma isasat_fast_slow_isasat_fast_slow_wl_D:
  \<open>(isasat_fast_slow, RETURN o isasat_fast_slow_wl_D) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
    (auto simp: isasat_fast_slow_alt_def isasat_fast_slow_wl_D_def)

end


subsubsection \<open>Lift Operations to State\<close>

context isasat_input_bounded
begin

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition (in -) get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
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

sepref_thm get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_code
   uses isasat_input_bounded.get_conflict_wl_is_None_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_code_def

lemmas get_conflict_wl_is_None_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm get_conflict_wl_is_None_fast_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_alt_def isasat_fast_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_fast_code
   uses isasat_input_bounded.get_conflict_wl_is_None_fast_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_fast_code_def

lemmas get_conflict_wl_is_None_fast_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) count_decided_st where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

sepref_thm count_decided_st_code
  is \<open>RETURN o count_decided_st\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding count_decided_st_def isasat_assn_def
  by sepref

concrete_definition (in -) count_decided_st_code
  uses isasat_input_bounded.count_decided_st_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) count_decided_st_code_def

lemmas count_decided_st_code_refine[sepref_fr_rules] =
   count_decided_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

sepref_thm count_decided_st_fast_code
  is \<open>RETURN o count_decided_st\<close>
  :: \<open>isasat_fast_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding count_decided_st_def isasat_fast_assn_def
  by sepref

concrete_definition (in -) count_decided_st_fast_code
  uses isasat_input_bounded.count_decided_st_fast_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) count_decided_st_fast_code_def

lemmas count_decided_st_fast_code_refine[sepref_fr_rules] =
   count_decided_st_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o count_decided_st, RETURN o count_decided_st) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_heur_def)

lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition (in isasat_input_ops) atm_is_in_conflict_st_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>atm_is_in_conflict_st_heur L = (\<lambda>(M, N, (_, (_, D)), _). D ! (atm_of L) \<noteq> None)\<close>

lemma atm_is_in_conflict_st_heur_alt_def:
  \<open>RETURN oo atm_is_in_conflict_st_heur = (\<lambda>L (M, N, (_, (_, D)), _). RETURN (D ! (atm_of L) \<noteq> None))\<close>
  unfolding atm_is_in_conflict_st_heur_def by (auto intro!: ext)

lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (RETURN oo atm_is_in_conflict_st_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   [\<lambda>(L, S). -L \<notin># the (get_conflict_wl S) \<and> get_conflict_wl S \<noteq> None \<and>
     L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  by (case_tac x, case_tac y)
    (auto simp: atm_is_in_conflict_st_heur_def is_in_conflict_st_def twl_st_heur_def
      atms_of_def atm_of_eq_atm_of option_lookup_clause_rel_def lookup_clause_rel_def
      mset_as_position_in_iff_nth is_pos_neg_not_is_pos mset_as_position_empty_iff)


definition (in isasat_input_ops) polarity_st_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option\<close>
where
  \<open>polarity_st_heur S = polarity (get_trail_wl_heur S)\<close>

definition (in isasat_input_ops) polarity_st_pre where
\<open>polarity_st_pre \<equiv> \<lambda>(M, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>

lemma polarity_st_heur_alt_def:
  \<open>polarity_st_heur = (\<lambda>(M, _). polarity M)\<close>
  by (auto simp: polarity_st_heur_def)

sepref_thm polarity_st_heur_pol
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_pre]\<^sub>a isasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_assn_def polarity_st_pre_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_pol_code
   uses isasat_input_bounded.polarity_st_heur_pol.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_pol_code_def

lemmas polarity_st_heur_pol_polarity_st_refine[sepref_fr_rules] =
  polarity_st_heur_pol_code.refine[OF isasat_input_bounded_axioms]


sepref_thm polarity_st_heur_pol_fast
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_pre]\<^sub>a isasat_fast_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_fast_assn_def polarity_st_pre_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_pol_fast_code
   uses isasat_input_bounded.polarity_st_heur_pol_fast.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_pol_fast_code_def

lemmas polarity_st_heur_pol_fast_polarity_st_refine[sepref_fr_rules] =
  polarity_st_heur_pol_fast_code.refine[OF isasat_input_bounded_axioms]

end

abbreviation (in -) nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>

end
