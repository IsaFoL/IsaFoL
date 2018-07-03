theory IsaSAT_Setup
  imports IsaSAT_Trail CDCL_Conflict_Minimisation IsaSAT_Clauses
    Watched_Literals_VMTF IsaSAT_Lookup_Conflict LBD
begin

no_notation Ref.update ("_ := _" 62)

(* TODO Move *)
lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in>
    (option_assn bool_assn)\<^sup>k *\<^sub>a (option_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: option_assn_alt_def split:option.splits)

declare option_assn_eq[sepref_comb_rules del]

text \<open>This function does not change the size of the underlying array.\<close>
definition (in -) take1 where
  \<open>take1 xs = take 1 xs\<close>

lemma (in -) take1_hnr[sepref_fr_rules]:
  \<open>(return o (\<lambda>(a, _). (a, 1::nat)), RETURN o take1) \<in> [\<lambda>xs. xs \<noteq> []]\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arl_assn_def hr_comp_def take1_def list_rel_def
      is_array_list_def)
  apply (case_tac b; case_tac x; case_tac l')
   apply (auto)
  done
(* End Move *)

subsection \<open>Code Generation\<close>

subsubsection \<open>Types and Refinement Relations\<close>

paragraph \<open>Statistics\<close>

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

type_synonym isasat_clauses_assn =
  \<open>uint32 array array_list \<times> (clause_status \<times> uint32 \<times> uint32)array_list\<close>
type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom_assn \<times> nat\<close>

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> isasat_clauses_assn \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom_assn \<times> nat\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
type_synonym twl_st_wl_heur =
  \<open>(nat,nat)ann_lits \<times> nat clauses_l \<times>
    nat clause option \<times> nat lit_queue_wl \<times> (nat watcher) list list \<times> vmtf_remove_int \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times>
    vdom \<times> nat\<close>

type_synonym (in -) twl_st_wl_heur_W_list =
  \<open>(nat,nat) ann_lits \<times> nat clauses_l \<times>
    nat cconflict \<times> nat clause_l \<times> (nat watcher) list list \<times> vmtf_remove_int \<times> bool list \<times> nat \<times>
    nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats \<times> ema \<times> ema \<times> conflict_count \<times> vdom \<times> nat\<close>

fun get_clauses_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clauses_l\<close> where
  \<open>get_clauses_wl_heur (M, N, D, _) = N\<close>

fun get_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur (M, N, D, _) = M\<close>

fun get_conflict_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clause option\<close> where
  \<open>get_conflict_wl_heur (_, _, D, _) = D\<close>


fun watched_by_int :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat watched\<close> where
  \<open>watched_by_int (M, N, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat watcher) list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, W, _) = W\<close>

fun literals_to_update_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat lit_queue_wl\<close> where
  \<open>literals_to_update_wl_heur (M, N, D, Q, W, _, _)  = Q\<close>

fun set_literals_to_update_wl_heur :: \<open>nat lit_queue_wl \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>set_literals_to_update_wl_heur Q (M, N, D, _, W') = (M, N, D, Q, W')\<close>

definition watched_by_app_heur_pre where
  \<open>watched_by_app_heur_pre = (\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L))\<close>

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_app_heur S L K = watched_by_int S L ! K\<close>

lemma watched_by_app_heur_alt_def:
  \<open>watched_by_app_heur = (\<lambda>(M, N, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>
  by (auto simp: watched_by_app_heur_def intro!: ext)

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
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
      append_ll_def  split: nat.splits)
  by (simp add: list_eq_iff_nth_eq)

lemma op_map_to_map_rel:
  \<open>(uncurry2 (op_map_to R e), uncurry2 (RETURN ooo (\<lambda>xs W' j. W'[j := W'!j @ map R xs]))) \<in>
    [\<lambda>((xs, ys), j). j < length ys]\<^sub>f
   \<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: op_map_to_map)

definition convert_single_wl_to_nat where
\<open>convert_single_wl_to_nat W i W' j = op_map_to (\<lambda>(i, C). (nat_of_uint32_conv i, C)) (0, Pos 0) (W!i) W' j\<close>

sepref_definition convert_single_wl_to_nat_code
  is \<open>uncurry3 convert_single_wl_to_nat\<close>
  :: \<open>[\<lambda>(((W, i), W'), j). i < length W \<and> j < length W']\<^sub>a
       (arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn)))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
       (arrayO_assn (arl_assn (nat_assn *a unat_lit_assn)))\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
      arrayO_assn (arl_assn (nat_assn *a unat_lit_assn))\<close>
  supply [[goals_limit=1]]
  unfolding convert_single_wl_to_nat_def op_map_to_def nth_ll_def[symmetric]
    length_ll_def[symmetric]
  by sepref

definition convert_single_wl_to_nat_conv where
\<open>convert_single_wl_to_nat_conv xs i W' j =
   W'[j :=  map (\<lambda>(i, C). (nat_of_uint32_conv i, C)) (xs!i)]\<close>

lemma convert_single_wl_to_nat:
  \<open>(uncurry3 convert_single_wl_to_nat,
    uncurry3 (RETURN oooo convert_single_wl_to_nat_conv)) \<in>
   [\<lambda>(((xs, i), ys), j). i < length xs \<and> j < length ys \<and> ys!j = []]\<^sub>f
   \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<rightarrow> 
     \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: convert_single_wl_to_nat_def convert_single_wl_to_nat_conv_def
      dest!: op_map_to_map)

lemma convert_single_wl_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(uncurry3 convert_single_wl_to_nat_code,
     uncurry3 (RETURN \<circ>\<circ>\<circ> convert_single_wl_to_nat_conv))
  \<in> [\<lambda>(((a, b), ba), bb). b < length a \<and> bb < length ba \<and> ba ! bb = []]\<^sub>a
    (arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn)))\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
    (arrayO_assn (arl_assn (nat_assn *a unat_lit_assn)))\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    arrayO_assn (arl_assn (nat_assn *a unat_lit_assn))\<close>
  using convert_single_wl_to_nat_code.refine[FCOMP convert_single_wl_to_nat]
  by auto

definition convert_wlists_to_nat_conv where
  \<open>convert_wlists_to_nat_conv = id\<close>

definition convert_wlists_to_nat where
  \<open>convert_wlists_to_nat = op_map (map (\<lambda>(n, bL). (nat_of_uint32_conv n, bL))) []\<close>

lemma convert_wlists_to_nat_alt_def:
  \<open>convert_wlists_to_nat = op_map id []\<close>
proof -
  have [simp]: \<open>(\<lambda>(n, bL). (nat_of_uint32_conv n, bL)) = id\<close>
    by (auto intro!: ext simp: nat_of_uint32_conv_def)
  show ?thesis
    by (auto simp: convert_wlists_to_nat_def)
qed


(* TODO Move *)
lemma length_a_hnr[sepref_fr_rules]:
  \<open>(length_a, RETURN o op_list_length) \<in> (arrayO_assn R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare sep_auto
(* End Move *)

sepref_definition convert_wlists_to_nat_code
  is \<open>convert_wlists_to_nat\<close>
  :: \<open>(arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn)))\<^sup>d \<rightarrow>\<^sub>a
          arrayO_assn (arl_assn (nat_assn *a unat_lit_assn))\<close>
  unfolding convert_wlists_to_nat_def
    op_map_def[of \<open>map (\<lambda>(n, y). (nat_of_uint32_conv n, y))\<close> \<open>[]\<close>,
  unfolded convert_single_wl_to_nat_conv_def[symmetric] init_lrl_def[symmetric]]
  by sepref

lemma convert_wlists_to_nat_convert_wlists_to_nat_conv:
  \<open>(convert_wlists_to_nat, RETURN o convert_wlists_to_nat_conv) \<in>
     \<langle>\<langle>nat_rel \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>\<langle>nat_rel \<times>\<^sub>r Id\<rangle>list_rel\<rangle>list_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: convert_wlists_to_nat_def nat_of_uint32_conv_def convert_wlists_to_nat_conv_def
      nat_of_uint32_conv_def[abs_def]
      intro: order.trans op_map_map)

lemma convert_wlists_to_nat_conv_hnr[sepref_fr_rules]:
  \<open>(convert_wlists_to_nat_code, RETURN \<circ> convert_wlists_to_nat_conv)
   \<in> (arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn)))\<^sup>d \<rightarrow>\<^sub>a
      arrayO_assn (arl_assn (nat_assn *a unat_lit_assn))\<close>
  using convert_wlists_to_nat_code.refine[FCOMP convert_wlists_to_nat_convert_wlists_to_nat_conv]
  by simp

context isasat_input_ops
begin

text \<open>The virtual domain is composed of the addressable (and accessible) elements, i.e.,
  the domain and all the deleted clauses that are still present in the watch lists.

  With restarts, the property is \<^term>\<open>vdom_m W N \<subseteq># dom_m N\<close>.
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
       dom_m ax \<subseteq># mset au \<Longrightarrow>
       vdom_m bj (ax(bf \<hookrightarrow> C')) = vdom_m bj (ax)\<close>
  by (force simp: vdom_m_def split: if_splits)+

definition vdom_m_heur :: \<open>((nat \<times> _) list list) \<Rightarrow> (nat, 'b) fmap \<Rightarrow> nat set\<close> where
  \<open>vdom_m_heur W N = \<Union>(((`) fst) ` set ` (!) W ` nat_of_lit ` set_mset \<L>\<^sub>a\<^sub>l\<^sub>l) \<union> set_mset (dom_m N)\<close>


definition cach_refinement_empty where
  \<open>cach_refinement_empty cach \<longleftrightarrow>
     (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. cach L = SEEN_UNKNOWN)\<close>

definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and>
    D' = D \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach \<and>
    out_learned M D outl \<and>
    dom_m N \<subseteq># mset vdom \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m W N = set_mset (dom_m N)
  }\<close>

lemma vdom_m_heur_vdom_m: \<open>(S, S') \<in> twl_st_heur \<Longrightarrow> 
    vdom_m_heur (get_watched_wl_heur S) (get_clauses_wl_heur S) = vdom_m (get_watched_wl S') (get_clauses_wl S')\<close>
   by (auto simp: twl_st_heur_def vdom_m_heur_def
    vdom_m_def map_fun_rel_def
    dest!: multi_member_split[of _ \<L>\<^sub>a\<^sub>l\<^sub>l])

definition twl_st_heur' :: \<open>nat multiset \<Rightarrow> (twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur' N =
  {(S, S'). (S, S') \<in> twl_st_heur \<and> dom_m (get_clauses_wl_heur S) = N}\<close>

definition isasat_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>isasat_assn =
  trail_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn (nat_assn *a unat_lit_assn)) *a
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
  trail_fast_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn (uint32_nat_assn *a unat_lit_assn)) *a
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
abbreviation (in -) isasat_fast :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>isasat_fast S \<equiv> (\<forall>L \<in># dom_m (get_clauses_wl_heur S). L < uint32_max)\<close>

definition twl_st_heur_no_clvls
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_no_clvls =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount, vdom,
       lcount),
     (M, N, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and>
    D' = D \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    out_learned_confl M D outl \<and>
    dom_m N \<subseteq># mset vdom \<and>
    lcount = size (learned_clss_lf N)
  }\<close>

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

definition literals_are_in_\<L>\<^sub>i\<^sub>n_heur where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S = literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# ran_mf (get_clauses_wl_heur S))\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0:
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S\<close> and
    \<open>i \<in># dom_m (get_clauses_wl_heur S)\<close> and
    \<open>j < length (get_clauses_wl_heur S \<propto> i)\<close>
  shows \<open>get_clauses_wl_heur S \<propto> i ! j \<in> snd ` D\<^sub>0\<close>
  using assms literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>get_clauses_wl_heur S\<close> i j]
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def image_image nth_tl)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0':
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S\<close> and
    \<open>i \<in># dom_m (get_clauses_wl_heur S)\<close> and
    \<open>j < length (get_clauses_wl_heur S \<propto> i)\<close> and
    N: \<open>N = get_clauses_wl_heur S\<close>
  shows \<open>N \<propto> i ! j \<in> snd ` D\<^sub>0\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0[OF assms(1-3)] unfolding N .

end

lemma Pos_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. L \<le> uint_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  apply sepref_to_hoare
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2 uint_max_def)


subsubsection \<open>Lift Operations to State\<close>

context isasat_input_bounded
begin

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition (in -) get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur = (\<lambda>(M, N, D, Q, W, _). is_None D)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
    \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
     split: option.splits)

sepref_thm get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>isasat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_def isasat_assn_def length_ll_def[symmetric]
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
  unfolding get_conflict_wl_is_None_heur_def isasat_fast_assn_def length_ll_def[symmetric]
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
  \<open>atm_is_in_conflict_st_heur L S \<longleftrightarrow> atm_of L \<in> atms_of (the (get_conflict_wl_heur S))\<close>

lemma atm_is_in_conflict_st_heur_alt_def:
  \<open>atm_is_in_conflict_st_heur = (\<lambda>L (M, N, D, _). atm_of L \<in> atms_of (the D))\<close>
  unfolding atm_is_in_conflict_st_heur_def by (auto intro!: ext)

lemma atm_is_in_conflict_st_heur_is_in_conflict_st:
  \<open>(uncurry (RETURN oo atm_is_in_conflict_st_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   [\<lambda>(L, S). -L \<notin># the (get_conflict_wl S)]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (auto simp: atm_is_in_conflict_st_heur_def is_in_conflict_st_def twl_st_heur_def
      atms_of_def atm_of_eq_atm_of)

definition (in isasat_input_ops) polarity_st_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option\<close>
where
  \<open>polarity_st_heur S = polarity (get_trail_wl_heur S)\<close>

abbreviation (in isasat_input_ops) polarity_st_pre where
\<open>polarity_st_pre \<equiv> \<lambda>(M, L). L \<in> snd ` D\<^sub>0\<close>

lemma polarity_st_heur_alt_def:
  \<open>polarity_st_heur = (\<lambda>(M, _). polarity M)\<close>
  by (auto simp: polarity_st_heur_def)

sepref_thm polarity_st_heur_pol
  is \<open>uncurry (RETURN oo polarity_st_heur)\<close>
  :: \<open>[polarity_st_pre]\<^sub>a isasat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> tri_bool_assn\<close>
  unfolding polarity_st_heur_alt_def isasat_assn_def
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
  unfolding polarity_st_heur_alt_def isasat_fast_assn_def
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

text \<open>We here define a variant of the trail representation, where the the control stack is out of
  sync of the trail. This might make backtracking a little faster.
\<close>

context isasat_input_bounded
begin

definition (in isasat_input_ops) trail_pol_no_CS
  :: \<open>(trail_pol \<times> (nat, nat) ann_lits) set\<close>
where
  \<open>trail_pol_no_CS = {((M', xs, lvls, reasons, k, cs), M). ((M', reasons), M) \<in> ann_lits_split_reasons \<and>
    no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. nat_of_lit L < length xs \<and> xs ! (nat_of_lit L) = polarity M L) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<and>
    control_stack (take (count_decided M) cs) M}\<close>

definition (in isasat_input_ops) tl_trailt_tr_no_CS :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trailt_tr_no_CS = (\<lambda>(M', xs, lvls, reasons, k, cs).
    let L = last M' in
    (butlast M',
    let xs = xs[nat_of_lit L := None] in xs[nat_of_lit (-L) := None],
    lvls[atm_of L := zero_uint32_nat],
    reasons, k, cs))\<close>


sepref_thm tl_trail_tr_no_CS_code
  is \<open>RETURN o tl_trailt_tr_no_CS\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reason, k, cs). M \<noteq> [] \<and> nat_of_lit(last M) < length xs \<and>
        nat_of_lit(-last M) < length xs  \<and> atm_of (last M) < length lvls \<and>
        atm_of (last M) < length reason]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_no_CS_def UNSET_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) tl_trail_tr_no_CS_code
  uses isasat_input_bounded.tl_trail_tr_no_CS_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_no_CS_code_def

lemmas tl_trail_tr_no_CS_coded_refine[sepref_fr_rules] =
   tl_trail_tr_no_CS_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]


sepref_thm tl_trail_tr_no_CS_fast_code
  is \<open>RETURN o tl_trailt_tr_no_CS\<close>
  :: \<open>[\<lambda>(M, xs, lvls, reason, k, cs). M \<noteq> [] \<and> nat_of_lit(last M) < length xs \<and>
        nat_of_lit(-last M) < length xs  \<and> atm_of (last M) < length lvls \<and>
        atm_of (last M) < length reason]\<^sub>a
        trail_pol_fast_assn\<^sup>d \<rightarrow> trail_pol_fast_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_no_CS_def UNSET_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) tl_trail_tr_no_CS_fast_code
  uses isasat_input_bounded.tl_trail_tr_no_CS_fast_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_no_CS_fast_code_def

lemmas tl_trail_tr_no_CS_fast_coded_refine[sepref_fr_rules] =
   tl_trail_tr_no_CS_fast_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma (in -) control_stack_take_Suc_count_dec_unstack:
 \<open> control_stack (take (Suc (count_decided M's)) cs) (Decided x1 # M's) \<Longrightarrow>
    control_stack (take (count_decided M's) cs) M's\<close>
  using control_stack_length_count_dec[of \<open>take (Suc (count_decided M's)) cs\<close> \<open>Decided x1 # M's\<close>]
  by (auto simp: min_def take_Suc_conv_app_nth split: if_splits elim: control_stackE)

lemma tl_trail_tr_no_CS:
  \<open>((RETURN o tl_trailt_tr_no_CS), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol_no_CS \<rightarrow> \<langle>trail_pol_no_CS\<rangle>nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_no_CS_def Let_def
        tl_trailt_tr_no_CS_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal
        by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def
            ann_lits_split_reasons_def Let_def)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
      subgoal by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def)
      subgoal
        by (cases \<open>lit_of L\<close>)
          (auto simp: polarity_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l
            uminus_lit_swap Let_def
            dest: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def Let_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if Let_def
            dest!: ann_lits_split_reasons_map_lit_of)
      subgoal
        by (cases \<open>L\<close>)
          (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
            control_stack_dec_butlast
            dest: no_dup_consistentD)
      subgoal
        by (cases \<open>L\<close>)
          (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff ann_lits_split_reasons_def
            control_stack_dec_butlast control_stack_take_Suc_count_dec_unstack
            dest: no_dup_consistentD ann_lits_split_reasons_map_lit_of)
      done
    done
qed


abbreviation (in -) trail_pol_assn' :: \<open>trail_pol \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_assn' \<equiv>
      out_learned_assn *a array_assn (tri_bool_assn) *a
      array_assn uint32_nat_assn *a
      array_assn (option_assn nat_assn) *a uint32_nat_assn *a arl_assn uint32_nat_assn\<close>

abbreviation (in -) trail_pol_fast_assn' :: \<open>trail_pol \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_fast_assn' \<equiv>
      out_learned_assn *a array_assn (tri_bool_assn) *a
      array_assn uint32_nat_assn *a
      array_assn (option_assn uint32_nat_assn) *a uint32_nat_assn *a arl_assn uint32_nat_assn\<close>

abbreviation (in isasat_input_ops) trail_no_CS_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_no_CS_assn \<equiv> hr_comp trail_pol_assn' trail_pol_no_CS\<close>

abbreviation (in isasat_input_ops) trail_no_CS_fast_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_pol_fast_assn \<Rightarrow> assn\<close> where
  \<open>trail_no_CS_fast_assn \<equiv> hr_comp trail_pol_fast_assn' trail_pol_no_CS\<close>

lemma
  tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
    \<open>(tl_trail_tr_no_CS_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_no_CS_assn\<^sup>d \<rightarrow> trail_no_CS_assn\<close>
    (is ?slow is \<open>_?c\<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>) and
  tl_trail_tr_fast_code_op_list_tl[sepref_fr_rules]:
    \<open>(tl_trail_tr_no_CS_fast_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_no_CS_fast_assn\<^sup>d \<rightarrow> trail_no_CS_fast_assn\<close>
    (is ?fast is \<open>_?cfast \<in> [?pre]\<^sub>a ?imfast \<rightarrow> ?ffast\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, r, b), x) \<in> trail_pol \<Longrightarrow> a = map lit_of (rev x)\<close> for a aa ab b x r
    by (auto simp: trail_pol_def ann_lits_split_reasons_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (last x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x rule: rev_cases) auto
  have H: \<open>?c
      \<in>  [comp_PRE trail_pol_no_CS (\<lambda>M. M \<noteq> [])
         (\<lambda>_ (M, xs, lvls, reason, k, cs).
             M \<noteq> [] \<and> nat_of_lit (last M) < length xs \<and>
                       nat_of_lit (- last M) < length xs \<and> atm_of (last M) < length lvls \<and>
                       atm_of (last M) < length reason)
         (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>d) trail_pol_no_CS \<rightarrow> hr_comp trail_pol_assn trail_pol_no_CS\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_no_CS_coded_refine tl_trail_tr_no_CS]
    unfolding op_list_tl_def
    .
  thm tl_trail_tr_no_CS_coded_refine tl_trail_tr
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    apply (cases x; cases \<open>hd x\<close>)
    by (auto simp: comp_PRE_def trail_pol_no_CS_def ann_lits_split_reasons_def uminus_\<A>\<^sub>i\<^sub>n_iff
        rev_map[symmetric] hd_append hd_map simp del: rev_map
        intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?slow
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im apply assumption
    using pre ..
  have H: \<open>?cfast
      \<in>  [comp_PRE trail_pol_no_CS (\<lambda>M. M \<noteq> [])
     (\<lambda>_ (M, xs, lvls, reason, k, cs).
         M \<noteq> [] \<and>
         nat_of_lit (last M) < length xs \<and>
         nat_of_lit (-last M) < length xs \<and>
         atm_of (last M) < length lvls \<and>
         atm_of (last M) < length reason)
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_fast_assn\<^sup>d)
                    trail_pol_no_CS \<rightarrow> hr_comp trail_pol_fast_assn trail_pol_no_CS\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_no_CS_fast_coded_refine tl_trail_tr_no_CS]
    unfolding op_list_tl_def
    .
  have im: \<open>?im' = ?imfast\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?fast
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im apply assumption
    using pre ..
qed

definition trail_conv_to_no_CS :: \<open>(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_conv_to_no_CS M = M\<close>

lemma id_trail_conv_to_no_CS:
  \<open>(RETURN o id, RETURN o trail_conv_to_no_CS) \<in> trail_pol \<rightarrow>\<^sub>f \<langle>trail_pol_no_CS\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: trail_pol_no_CS_def trail_conv_to_no_CS_def hr_comp_def trail_pol_def
      control_stack_length_count_dec
      intro: ext )

lemma trail_no_CS_assn_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o trail_conv_to_no_CS) \<in> trail_assn\<^sup>d \<rightarrow>\<^sub>a trail_no_CS_assn\<close>
  using id_ref[FCOMP id_trail_conv_to_no_CS, of trail_pol_assn] .

lemma trail_no_CS_assn_fast_hnr[sepref_fr_rules]:
  \<open>(return o id, RETURN o trail_conv_to_no_CS) \<in> trail_fast_assn\<^sup>d \<rightarrow>\<^sub>a trail_no_CS_fast_assn\<close>
  using id_ref[FCOMP id_trail_conv_to_no_CS, of trail_pol_fast_assn] .

definition trail_conv_back :: \<open>nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>trail_conv_back j M = M\<close>

definition (in -) trail_conv_back_imp :: \<open>nat \<Rightarrow> trail_pol \<Rightarrow> trail_pol nres\<close> where
  \<open>trail_conv_back_imp j = (\<lambda>(M, xs, lvls, reason, _, cs). do {
     ASSERT(j \<le> length cs); RETURN (M, xs, lvls, reason, j, take (nat_of_uint32_conv j) cs)})\<close>

lemma trail_conv_back:
  \<open>(uncurry trail_conv_back_imp, uncurry (RETURN oo trail_conv_back))
      \<in> [\<lambda>(k, M). k = count_decided M]\<^sub>f nat_rel \<times>\<^sub>f trail_pol_no_CS \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (force simp: trail_pol_no_CS_def trail_conv_to_no_CS_def hr_comp_def trail_pol_def
      control_stack_length_count_dec trail_conv_back_def trail_conv_back_imp_def
      nat_of_uint32_conv_def
      intro: ext intro!: ASSERT_refine_left
      dest: control_stack_length_count_dec)

definition (in -)take_arl where
  \<open>take_arl = (\<lambda>i (xs, j). (xs, i))\<close>
lemma (in -) take_arl_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo take_arl), uncurry (RETURN oo take))
    \<in> [\<lambda>(j, xs). j \<le> length xs]\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: arl_assn_def hr_comp_def take_arl_def intro!: list_rel_take)
  apply (sep_auto simp: is_array_list_def list_rel_imp_same_length[symmetric] min_def
      split: if_splits)
  done

sepref_definition (in -) trail_conv_back_imp_code
  is \<open>uncurry trail_conv_back_imp\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_assn'\<^sup>d \<rightarrow>\<^sub>a trail_pol_assn'\<close>
  supply [[goals_limit=1]] nat_of_uint32_conv_def[simp]
  unfolding trail_conv_back_imp_def
  by sepref

lemma trail_conv_back_hnr[sepref_fr_rules]:
  \<open>(uncurry trail_conv_back_imp_code, uncurry (RETURN \<circ>\<circ> trail_conv_back))
    \<in> [\<lambda>(a, b). a = count_decided b]\<^sub>a
       uint32_nat_assn\<^sup>k *\<^sub>a (hr_comp trail_pol_assn' trail_pol_no_CS)\<^sup>d \<rightarrow>
       hr_comp trail_pol_assn' trail_pol\<close>
  using trail_conv_back_imp_code.refine[FCOMP trail_conv_back] .


sepref_definition (in -) trail_conv_back_imp_fast_code
  is \<open>uncurry trail_conv_back_imp\<close>
  :: \<open>uint32_nat_assn\<^sup>k *\<^sub>a trail_pol_fast_assn'\<^sup>d \<rightarrow>\<^sub>a trail_pol_fast_assn'\<close>
  supply [[goals_limit=1]] nat_of_uint32_conv_def[simp]
  unfolding trail_conv_back_imp_def
  by sepref

lemma trail_conv_back_fast_hnr[sepref_fr_rules]:
  \<open>(uncurry trail_conv_back_imp_fast_code, uncurry (RETURN \<circ>\<circ> trail_conv_back))
  \<in> [\<lambda>(a, b). a = count_decided b]\<^sub>a
     uint32_nat_assn\<^sup>k *\<^sub>a (hr_comp trail_pol_fast_assn' trail_pol_no_CS)\<^sup>d \<rightarrow>
    hr_comp trail_pol_fast_assn' trail_pol\<close>
  using trail_conv_back_imp_fast_code.refine[FCOMP trail_conv_back] .

end

end
