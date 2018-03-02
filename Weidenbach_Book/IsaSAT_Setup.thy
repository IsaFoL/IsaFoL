theory IsaSAT_Setup
  imports IsaSAT_Trail CDCL_Conflict_Minimisation IsaSAT_Clauses
    Watched_Literals_VMTF IsaSAT_Lookup_Conflict LBD
begin

no_notation Ref.update ("_ := _" 62)

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)
(* TODO Move *)
lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo (op =))) \<in>
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

type_synonym stats = \<open>uint64 \<times> uint64 \<times> uint64\<close>

abbreviation uint64_rel :: \<open>(uint64 \<times> uint64) set\<close> where
  \<open>uint64_rel \<equiv> Id\<close>

abbreviation uint64_assn :: \<open>uint64 \<Rightarrow> uint64 \<Rightarrow> assn\<close>where
  \<open>uint64_assn \<equiv> id_assn\<close>

abbreviation stats_assn where
  \<open>stats_assn \<equiv> uint64_assn *a uint64_assn *a uint64_assn\<close>

definition incr_propagation :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_propagation = (\<lambda>(propa, confl, dec). (propa + 1, confl, dec))\<close>

definition incr_conflict :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_conflict = (\<lambda>(propa, confl, dec). (propa, confl + 1, dec))\<close>

definition incr_decision :: \<open>stats \<Rightarrow> stats\<close> where
  \<open>incr_decision = (\<lambda>(propa, confl, dec). (propa, confl, dec + 1))\<close>

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


paragraph \<open>Base state\<close>

type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array \<times> nat\<close>
type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> clauses_wl \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
type_synonym twl_st_wl_heur =
  \<open>(nat,nat)ann_lits \<times> nat clauses_l \<times>
    nat clause option \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times>
    nat \<times> nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats\<close>

type_synonym twl_st_wl_heur_trail_ref =
  \<open>trail_pol \<times> nat clause_l list \<times> nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times>
   vmtf_remove_int \<times> bool list \<times> nat \<times> nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats\<close>

fun get_clauses_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clauses_l\<close> where
  \<open>get_clauses_wl_heur (M, N, D, _) = N\<close>

fun get_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur (M, N, D, _) = M\<close>

fun get_conflict_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clause option\<close> where
  \<open>get_conflict_wl_heur (_, _, D, _) = D\<close>

fun get_watched_list_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_list_heur (_, _, _, _, W, _) = W\<close>

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

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>


context isasat_input_ops
begin

definition cach_refinement_empty where
  \<open>cach_refinement_empty cach \<longleftrightarrow> (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. cach L = SEEN_UNKNOWN)\<close>

definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats), (M, N, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach \<and>
    out_learned M D outl
  }\<close>

definition isasat_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>isasat_assn =
  trail_assn *a clauses_ll_assn *a
  option_lookup_clause_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn *a
  lbd_assn *a
  out_learned_assn *a
  stats_assn\<close>

definition (in isasat_input_ops) twl_st_heur_no_clvls
  :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close>
where
\<open>twl_st_heur_no_clvls =
  {((M', N', D', Q', W', vm, \<phi>, clvls, cach, lbd, outl, stats), (M, N, D, NE, UE, Q, W)).
    M = M' \<and> N' = N \<and>
    D' = D \<and>
    Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty cach \<and>
    out_learned_confl M D outl
  }\<close>

type_synonym (in -) twl_st_wl_heur_W_list =
  \<open>(nat,nat) ann_lits \<times> nat clauses_l \<times>
    nat cconflict \<times> nat clause_l \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times> nat \<times>
    nat conflict_min_cach \<times> lbd \<times> out_learned \<times> stats\<close>


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

lemma count_decided_st_count_decided_st:
  \<open>(RETURN o count_decided_st, RETURN o count_decided_st) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: count_decided_st_def twl_st_heur_def)

lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition (in isasat_input_ops) literal_is_in_conflict_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict_heur L S \<longleftrightarrow> L \<in># the (get_conflict_wl_heur S)\<close>

lemma literal_is_in_conflict_heur_alt_def:
  \<open>literal_is_in_conflict_heur = (\<lambda>L (M, N, D, _). L \<in># the D)\<close>
  unfolding literal_is_in_conflict_heur_def by (auto intro!: ext)

lemma literal_is_in_conflict_heur_is_in_conflict_st:
  \<open>(uncurry (RETURN oo literal_is_in_conflict_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   Id \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (auto simp: literal_is_in_conflict_heur_def is_in_conflict_st_def twl_st_heur_def)

definition (in isasat_input_ops) literal_is_in_conflict_heur_pre where
  \<open>literal_is_in_conflict_heur_pre =
    (\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
        get_conflict_wl_heur S \<noteq> None)\<close>

sepref_thm literal_is_in_conflict_heur_code
  is \<open>uncurry (RETURN oo literal_is_in_conflict_heur)\<close>
  :: \<open>[literal_is_in_conflict_heur_pre]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a isasat_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding literal_is_in_conflict_heur_alt_def isasat_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def literal_is_in_conflict_heur_pre_def
  by sepref

concrete_definition (in -) literal_is_in_conflict_heur_code
   uses isasat_input_bounded.literal_is_in_conflict_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) literal_is_in_conflict_heur_code_def

lemmas literal_is_in_conflict_heur_code_refine[sepref_fr_rules] =
   literal_is_in_conflict_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in isasat_input_ops) polarity_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> bool option\<close> where
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

end

abbreviation (in -) nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>

end
