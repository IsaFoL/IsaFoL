theory IsaSAT_Setup_SML
  imports IsaSAT_Setup IsaSAT_Watch_List_SML IsaSAT_Lookup_Conflict_SML
    IsaSAT_Clauses_SML IsaSAT_Arena_SML LBD_SML Watched_Literals.IICF_Array_List32
begin


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


type_synonym vmtf_assn = \<open>(32 word, 64 word) vmtf_node array \<times> 64 word \<times> uint32 \<times> uint32 \<times> uint32 option\<close>

type_synonym phase_saver_assn = \<open>bool array\<close>

definition (in -) vmtf_node_rel where
\<open>vmtf_node_rel = {(a', a). (stamp a', stamp a) \<in> uint64_nat_rel \<and>
   (get_prev a', get_prev a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel \<and>
   (get_next a', get_next a) \<in> \<langle>uint32_nat_rel\<rangle>option_rel}\<close>


text \<open>Setup to convert a list from \<^typ>\<open>64 word\<close> to \<^typ>\<open>nat\<close>.\<close>
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

(*TODO Move*)
(*End Move*)
type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array_list32\<close>
abbreviation stats_assn :: \<open>stats \<Rightarrow> stats \<Rightarrow> assn\<close> where
  \<open>stats_assn \<equiv> uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn
     \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn\<close>

abbreviation ema_assn :: \<open>ema \<Rightarrow> ema \<Rightarrow> assn\<close> where
  \<open>ema_assn \<equiv> uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn \<times>\<^sub>a uint64_assn\<close>

lemma ema_get_value_hnr[sepref_fr_rules]:
  \<open>(return o ema_get_value, RETURN o ema_get_value) \<in> ema_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

sepref_register ema_bitshifting

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

lemma (in -) ema_update_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo ema_update_ref), uncurry (RETURN oo ema_update)) \<in>
      uint32_nat_assn\<^sup>k *\<^sub>a ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding ema_update_def ema_update_ref_def
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def uint64_of_uint32_def Let_def)

lemma ema_reinit_hnr[sepref_fr_rules]:
  \<open>(return o ema_reinit, RETURN o ema_reinit) \<in> ema_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  by sepref_to_hoare sep_auto

lemma (in -) ema_init_coeff_hnr[sepref_fr_rules]:
  \<open>(return o ema_init, RETURN o ema_init) \<in> uint64_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: ema_init_def uint64_nat_rel_def br_def)

abbreviation restart_info_assn where
  \<open>restart_info_assn \<equiv> uint64_assn \<times>\<^sub>a uint64_assn\<close>

lemma incr_conflict_count_since_last_restart_hnr[sepref_fr_rules]:
    \<open>(return o incr_conflict_count_since_last_restart, RETURN o incr_conflict_count_since_last_restart)
       \<in> restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: incr_conflict_count_since_last_restart_def)

lemma restart_info_update_lvl_avg_hnr[sepref_fr_rules]:
    \<open>(uncurry (return oo restart_info_update_lvl_avg),
       uncurry (RETURN oo restart_info_update_lvl_avg))
       \<in> uint32_assn\<^sup>k *\<^sub>a restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_update_lvl_avg_def)

lemma restart_info_init_hnr[sepref_fr_rules]:
    \<open>(uncurry0 (return restart_info_init),
       uncurry0 (RETURN restart_info_init))
       \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_init_def)

lemma restart_info_restart_done_hnr[sepref_fr_rules]:
  \<open>(return o restart_info_restart_done, RETURN o restart_info_restart_done) \<in>
     restart_info_assn\<^sup>d \<rightarrow>\<^sub>a restart_info_assn\<close>
  by sepref_to_hoare (sep_auto simp: restart_info_restart_done_def
    uint64_nat_rel_def br_def)

type_synonym vmtf_remove_assn = \<open>vmtf_assn \<times> (uint32 array_list32 \<times> bool array)\<close>

abbreviation (in -)vmtf_node_assn where
\<open>vmtf_node_assn \<equiv> pure vmtf_node_rel\<close>

abbreviation vmtf_conc where
  \<open>vmtf_conc \<equiv> (array_assn vmtf_node_assn \<times>\<^sub>a uint64_nat_assn \<times>\<^sub>a uint32_nat_assn \<times>\<^sub>a uint32_nat_assn
    \<times>\<^sub>a option_assn uint32_nat_assn)\<close>

abbreviation atoms_hash_assn :: \<open>bool list \<Rightarrow> bool array \<Rightarrow> assn\<close> where
  \<open>atoms_hash_assn \<equiv> array_assn bool_assn\<close>

abbreviation distinct_atoms_assn where
  \<open>distinct_atoms_assn \<equiv> arl32_assn uint32_nat_assn \<times>\<^sub>a atoms_hash_assn\<close>

abbreviation vmtf_remove_conc
  :: \<open>isa_vmtf_remove_int \<Rightarrow> vmtf_remove_assn \<Rightarrow> assn\<close>
where
  \<open>vmtf_remove_conc \<equiv> vmtf_conc \<times>\<^sub>a distinct_atoms_assn\<close>


paragraph \<open>Options\<close>

abbreviation opts_assn
  :: \<open>opts \<Rightarrow> opts \<Rightarrow> assn\<close>
where
  \<open>opts_assn \<equiv> bool_assn \<times>\<^sub>a bool_assn \<times>\<^sub>a bool_assn\<close>

lemma opts_restart_hnr[sepref_fr_rules]:
  \<open>(return o opts_restart, RETURN o opts_restart) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma opts_reduce_hnr[sepref_fr_rules]:
  \<open>(return o opts_reduce, RETURN o opts_reduce) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

lemma opts_unbounded_mode_hnr[sepref_fr_rules]:
  \<open>(return o opts_unbounded_mode, RETURN o opts_unbounded_mode) \<in> opts_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto

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

lemma convert_single_wl_to_nat_conv_alt_def:
  \<open>convert_single_wl_to_nat_conv zs i xs i = xs[i := map (\<lambda>(i, y, y'). (nat_of_uint64_conv i, y, y')) (zs ! i)]\<close>
  unfolding convert_single_wl_to_nat_conv_def
  by auto

lemma convert_wlists_to_nat_convert_wlists_to_nat_conv:
  \<open>(convert_wlists_to_nat, RETURN o convert_wlists_to_nat_conv) \<in>
     \<langle>\<langle>nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>\<^sub>f
     \<langle>\<langle>\<langle>nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro WB_More_Refinement.frefI nres_relI)
    (auto simp: convert_wlists_to_nat_def
       convert_wlists_to_nat_conv_def
      intro: order.trans op_map_map)

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


abbreviation (in -) watchers_assn where
  \<open>watchers_assn \<equiv> arl_assn (watcher_assn)\<close>

abbreviation (in -) watchlist_assn where
  \<open>watchlist_assn \<equiv> arrayO_assn watchers_assn\<close>

abbreviation (in -) watchers_fast_assn where
  \<open>watchers_fast_assn \<equiv> arl64_assn (watcher_fast_assn)\<close>

abbreviation (in -) watchlist_fast_assn where
  \<open>watchlist_fast_assn \<equiv> arrayO_assn watchers_fast_assn\<close>

sepref_definition convert_single_wl_to_nat_code
  is \<open>uncurry3 convert_single_wl_to_nat\<close>
  :: \<open>[\<lambda>(((W, i), W'), j). i < length W \<and> j < length W']\<^sub>a
       (watchlist_fast_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
       (watchlist_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
       watchlist_assn\<close>
  supply [[goals_limit=1]] length_aa64_hnr[sepref_fr_rules] nth_aa64_hnr[sepref_fr_rules]
    length_ll_def[simp]
  unfolding convert_single_wl_to_nat_def op_map_to_def nth_ll_def[symmetric]
    length_ll_def[symmetric]
  by sepref

sepref_register convert_single_wl_to_nat_conv
lemma convert_single_wl_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(uncurry3 convert_single_wl_to_nat_code,
     uncurry3 (RETURN \<circ>\<circ>\<circ> convert_single_wl_to_nat_conv))
  \<in> [\<lambda>(((a, b), ba), bb). b < length a \<and> bb < length ba \<and> ba ! bb = []]\<^sub>a
    (watchlist_fast_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
    (watchlist_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    watchlist_assn\<close>
  using convert_single_wl_to_nat_code.refine[FCOMP convert_single_wl_to_nat[unfolded convert_fref]]
  by auto

sepref_definition convert_wlists_to_nat_code
  is \<open>convert_wlists_to_nat\<close>
  :: \<open>watchlist_fast_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  supply length_a_hnr[sepref_fr_rules] [[goals_limit=1]] arrayO_raa_empty_sz_init_lrl[sepref_fr_rules del]
  unfolding convert_wlists_to_nat_alt_def2
  by sepref


lemma convert_wlists_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(convert_wlists_to_nat_code, RETURN \<circ> convert_wlists_to_nat_conv)
    \<in> (watchlist_fast_assn)\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  using convert_wlists_to_nat_code.refine[FCOMP convert_wlists_to_nat_convert_wlists_to_nat_conv[unfolded convert_fref]]
  by simp

abbreviation vdom_assn :: \<open>vdom \<Rightarrow> nat array_list \<Rightarrow> assn\<close> where
  \<open>vdom_assn \<equiv> arl_assn nat_assn\<close>

abbreviation vdom_fast_assn :: \<open>vdom \<Rightarrow> uint64 array_list64 \<Rightarrow> assn\<close> where
  \<open>vdom_fast_assn \<equiv> arl64_assn uint64_nat_assn\<close>

type_synonym vdom_assn = \<open>nat array_list\<close>
type_synonym vdom_fast_assn = \<open>uint64 array_list64\<close>

type_synonym isasat_clauses_assn = \<open>uint32 array_list\<close>
type_synonym isasat_clauses_fast_assn = \<open>uint32 array_list64\<close>

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom_assn \<times> vdom_assn \<times> nat \<times> opts \<times> isasat_clauses_assn\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_fast_assn \<times> option_lookup_clause_assn \<times>
    uint32 \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> restart_info \<times>
    vdom_fast_assn \<times> vdom_fast_assn \<times> uint64 \<times> opts \<times> isasat_clauses_fast_assn\<close>

definition isasat_unbounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>isasat_unbounded_assn =
  trail_pol_assn \<times>\<^sub>a arena_assn \<times>\<^sub>a
  isasat_conflict_assn \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  watchlist_assn \<times>\<^sub>a
  vmtf_remove_conc \<times>\<^sub>a phase_saver_conc \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  cach_refinement_l_assn \<times>\<^sub>a
  lbd_assn \<times>\<^sub>a
  out_learned_assn \<times>\<^sub>a
  stats_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  vdom_assn \<times>\<^sub>a
  vdom_assn \<times>\<^sub>a
  nat_assn \<times>\<^sub>a
  opts_assn \<times>\<^sub>a arena_assn\<close>

definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a
  isasat_conflict_assn \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  watchlist_fast_assn \<times>\<^sub>a
  vmtf_remove_conc \<times>\<^sub>a phase_saver_conc \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  cach_refinement_l_assn \<times>\<^sub>a
  lbd_assn \<times>\<^sub>a
  out_learned_assn \<times>\<^sub>a
  stats_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  ema_assn \<times>\<^sub>a
  restart_info_assn \<times>\<^sub>a
  vdom_fast_assn \<times>\<^sub>a
  vdom_fast_assn \<times>\<^sub>a
  uint64_nat_assn \<times>\<^sub>a
  opts_assn \<times>\<^sub>a arena_fast_assn\<close>


sepref_definition isasat_fast_slow_code
  is \<open>isasat_fast_slow\<close>
  :: \<open>[\<lambda>S. length(get_clauses_wl_heur S) \<le> uint64_max \<and>
        length (get_old_arena S) \<le> uint64_max]\<^sub>a
      isasat_bounded_assn\<^sup>d \<rightarrow> isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding isasat_bounded_assn_def isasat_unbounded_assn_def isasat_fast_slow_def
  apply (rewrite at \<open>(_, \<hole>, _)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite at \<open>(_, _, nat_of_uint64_conv _, _, \<hole>)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite at \<open>(_, \<hole>, nat_of_uint64_conv _, _)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite at \<open>(\<hole>, _, nat_of_uint64_conv _, _)\<close> arl64_to_arl_conv_def[symmetric])
  apply (rewrite in \<open>(_, \<hole>, nat_of_uint64_conv _, _)\<close> arl_nat_of_uint64_conv_def[symmetric])
  apply (rewrite in \<open>(\<hole>, _, nat_of_uint64_conv _, _)\<close> arl_nat_of_uint64_conv_def[symmetric])
  by sepref

declare isasat_fast_slow_code.refine[sepref_fr_rules]


subsubsection \<open>Lift Operations to State\<close>

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


subsection \<open>More theorems\<close>

lemma count_decided_st_heur[sepref_fr_rules]:
  \<open>(return o count_decided_st_heur, RETURN o count_decided_st_heur) \<in>
      isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  \<open>(return o count_decided_st_heur, RETURN o count_decided_st_heur) \<in>
      isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding count_decided_st_heur_def isasat_bounded_assn_def isasat_unbounded_assn_def
  by (sepref_to_hoare; sep_auto)+

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

sepref_register rewatch_heur
sepref_definition rewatch_heur_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>vdom_assn\<^sup>k *\<^sub>a arena_assn\<^sup>k *\<^sub>a watchlist_assn\<^sup>d \<rightarrow>\<^sub>a watchlist_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
  by sepref

declare rewatch_heur_code.refine[sepref_fr_rules]
find_theorems nfoldli WHILET
sepref_definition rewatch_heur_fast_code
  is \<open>uncurry2 (rewatch_heur)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set vdom. x \<le> uint64_max) \<and> length arena \<le> uint64_max \<and> length vdom \<le> uint64_max]\<^sub>a
        vdom_fast_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]] uint64_of_nat_conv_def[simp]
     arena_lit_pre_le_uint64_max[intro] append_aa64_hnr[sepref_fr_rules]
  unfolding rewatch_heur_alt_def Let_def two_uint64_nat_def[symmetric] PR_CONST_def
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding zero_uint64_nat_def[symmetric]
    one_uint64_nat_def[symmetric] to_watcher_fast_def[symmetric]
    FOREACH_cond_def FOREACH_body_def uint64_of_nat_conv_def
  by sepref

sepref_register append_ll

declare rewatch_heur_fast_code.refine[sepref_fr_rules]

sepref_definition rewatch_heur_st_code
  is \<open>(rewatch_heur_st)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_def PR_CONST_def
    isasat_unbounded_assn_def
  by sepref

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

end