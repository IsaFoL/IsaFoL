theory IsaSAT_Setup
  imports IsaSAT_Trail CDCL_Conflict_Minimisation
    Two_Watched_Literals_VMTF IsaSAT_Lookup_Conflict
begin

no_notation Ref.update ("_ := _" 62)

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)
(* TODO Move *)
lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo (op =))) \<in>
    (option_assn bool_assn)\<^sup>k *\<^sub>a (option_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: option_assn_alt_def split:option.splits)

declare option_assn_eq[sepref_comb_rules del]
(* End Move *)

subsection \<open>Code Generation\<close>

subsubsection \<open>Types and Refinement Relations\<close>

type_synonym minimize_assn = \<open>minimize_status array \<times> uint32 array \<times> nat\<close>
type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32 \<times> minimize_assn\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
type_synonym twl_st_wl_heur =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat clause option \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times>
    nat \<times> nat conflict_min_cach\<close>

type_synonym twl_st_wl_heur_trail_ref =
  \<open>trail_pol \<times> nat clause_l list \<times> nat \<times> nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times>
   vmtf_remove_int \<times> bool list \<times> nat  \<times> nat conflict_min_cach\<close>

fun get_clauses_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clauses_l\<close> where
  \<open>get_clauses_wl_heur (M, N, U, D, _) = N\<close>

fun get_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur (M, N, U, D, _) = M\<close>

fun get_conflict_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat clause option\<close> where
  \<open>get_conflict_wl_heur (_, _, _, D, _) = D\<close>

fun get_watched_list_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_list_heur (_, _, _, _, _, W, _) = W\<close>

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> vmtf_remove_int\<close> where
  \<open>get_vmtf_heur (_, _, _, _, _, _, vm, _) = vm\<close>

fun get_phase_saver_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool list\<close> where
  \<open>get_phase_saver_heur (_, _, _, _, _, _, _, \<phi>, _) = \<phi>\<close>

fun get_count_max_lvls_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>get_count_max_lvls_heur (_, _, _, _, _, _, _, _, clvls, _) = clvls\<close>

fun get_conflict_cach:: \<open>twl_st_wl_heur \<Rightarrow> nat conflict_min_cach\<close> where
  \<open>get_conflict_cach (_, _, _, _, _, _, _, _, _, cach) = cach\<close>

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>


context isasat_input_ops
begin

definition cach_refinement_empty where
  \<open>cach_refinement_empty cach \<longleftrightarrow> (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. cach L = SEEN_UNKNOWN)\<close>

definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach
  }\<close>

definition twl_st_heur_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_heur_assn =
  trail_assn *a clauses_ll_assn *a nat_assn *a
  option_lookup_clause_assn *a
  clause_l_assn *a
  arrayO_assn (arl_assn nat_assn) *a
  vmtf_remove_conc *a phase_saver_conc *a
  uint32_nat_assn *a
  cach_refinement_assn\<close>

definition twl_st_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_assn = hr_comp twl_st_heur_assn twl_st_heur\<close>

type_synonym twl_st_heur_pol_no_clvls =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> option_lookup_clause_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times> uint32 \<times>
    minimize_assn\<close>

definition twl_st_heur_pol_assn
  :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> twl_st_heur_pol_no_clvls \<Rightarrow> assn\<close>
where
  \<open>twl_st_heur_pol_assn =
    trail_pol_assn *a clauses_ll_assn *a nat_assn *a
    option_lookup_clause_assn *a
    clause_l_assn *a
    arrayO_assn (arl_assn nat_assn) *a
    vmtf_remove_conc *a phase_saver_conc *a
    uint32_nat_assn *a
    cach_refinement_assn\<close>

definition (in isasat_input_ops) twl_st_heur_pol :: \<open>(twl_st_wl_heur_trail_ref \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_pol =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls, cach), (M, N, U, D, NP, UP, Q, W)).
    (M', M) \<in> trail_pol \<and> N' = N \<and> U' = U \<and> D = D' \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty cach
  }\<close>

lemma twl_st_heur_pol_alt_def:
  \<open>twl_st_heur_pol =
    (trail_pol \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O twl_st_heur\<close>
  by (force simp: twl_st_heur_pol_def twl_st_heur_def)

lemma twl_st_heur_pol_assn_twl_st_heur_assn:
  \<open>hr_comp twl_st_heur_pol_assn
    (trail_pol \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) =
     twl_st_heur_assn\<close>
  unfolding twl_st_heur_pol_assn_def twl_st_heur_assn_def
  by simp

lemma twl_st_heur_assn_assn:
  \<open>hr_comp twl_st_heur_pol_assn twl_st_heur_pol = twl_st_assn\<close>
  unfolding twl_st_assn_def twl_st_heur_pol_alt_def
  hr_comp_assoc[symmetric] twl_st_heur_pol_assn_twl_st_heur_assn
  ..

definition literals_are_in_\<L>\<^sub>i\<^sub>n_heur where
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S = literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl (get_clauses_wl_heur S)))\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0:
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S\<close> and
    \<open>i < length (get_clauses_wl_heur S)\<close> and
    \<open>j < length (get_clauses_wl_heur S ! i)\<close> and
    \<open>i > 0\<close>
  shows \<open>get_clauses_wl_heur S ! i ! j \<in> snd ` D\<^sub>0\<close>
  using assms literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>tl (get_clauses_wl_heur S)\<close> \<open>i - 1\<close> j]
  by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def image_image nth_tl)

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0':
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur S\<close> and
    \<open>i < length (get_clauses_wl_heur S)\<close> and
    \<open>j < length (get_clauses_wl_heur S ! i)\<close> and
    \<open>i > 0\<close> and N: \<open>N = get_clauses_wl_heur S\<close>
  shows \<open>N ! i ! j \<in> snd ` D\<^sub>0\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0[OF assms(1-4)] unfolding N .


type_synonym (in -) twl_st_wl_heur_lookup_conflict =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    (bool \<times> nat \<times> bool option list) \<times> nat literal multiset \<times> nat list list \<times> vmtf_remove_int \<times>
     bool list \<times> nat \<times> nat conflict_min_cach\<close>

definition twl_st_wl_heur_lookup_lookup_clause_rel
  :: \<open>(twl_st_wl_heur_lookup_conflict \<times> twl_st_wl_heur) set\<close>
where
  \<open>twl_st_wl_heur_lookup_lookup_clause_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     (option_lookup_clause_rel :: _ set) \<times>\<^sub>r
     (Id :: (nat lit_queue_wl \<times> _) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     Id\<close>

definition twl_st_heur_lookup_lookup_clause_assn
  :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close>
where
  \<open>twl_st_heur_lookup_lookup_clause_assn =
    trail_assn *a clauses_ll_assn *a nat_assn *a
    conflict_option_rel_assn *a
    clause_l_assn *a
    arrayO_assn (arl_assn nat_assn) *a
    vmtf_remove_conc *a phase_saver_conc *a uint32_nat_assn *a cach_refinement_assn
  \<close>

lemma twl_st_heur_assn_int_lookup_clause_assn:
  \<open>twl_st_heur_assn = hr_comp twl_st_heur_lookup_lookup_clause_assn twl_st_wl_heur_lookup_lookup_clause_rel\<close>
  unfolding twl_st_heur_assn_def twl_st_heur_lookup_lookup_clause_assn_def
    twl_st_wl_heur_lookup_lookup_clause_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn option_lookup_clause_assn_def)


lemma twl_st_assn_confl_assn:
  \<open>twl_st_assn = hr_comp twl_st_heur_lookup_lookup_clause_assn
    (twl_st_wl_heur_lookup_lookup_clause_rel O twl_st_heur)\<close>
  apply (subst hr_comp_assoc[symmetric])
  apply (subst twl_st_heur_assn_int_lookup_clause_assn[symmetric])
  unfolding twl_st_assn_def ..

end

lemma Pos_unat_lit_assn':
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. L \<le> uint_max div 2]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  apply sepref_to_hoare
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2 uint_max_def)


context isasat_input_bounded
begin

lemma Pos_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n), RETURN o Pos) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_N1_less_than_uint_max
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2)

lemma Neg_unat_lit_assn:
  \<open>(return o (\<lambda>n. two_uint32 * n +1), RETURN o Neg) \<in> [\<lambda>L. Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      unat_lit_assn\<close>
  apply sepref_to_hoare
  using in_N1_less_than_uint_max
  by (sep_auto simp: unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def Collect_eq_comp
      lit_of_natP_def nat_of_uint32_distrib_mult2_plus1 uint_max_def)

end


subsubsection \<open>Lift Operations to State\<close>

context isasat_input_bounded
begin

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition polarity_st_heur :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> _ \<Rightarrow> bool option nres\<close> where
  \<open>polarity_st_heur = (\<lambda>(M, _) L. polarity_pol M L)\<close>

sepref_thm polarity_st_heur_code
  is \<open>uncurry polarity_st_heur\<close>
  :: \<open>twl_st_heur_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding polarity_st_heur_def twl_st_heur_pol_assn_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_st_heur_code
   uses isasat_input_bounded.polarity_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_st_heur_code_def

lemmas polarity_st_heur_code_polarity_refine_code[sepref_fr_rules] =
   polarity_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma polarity_st_heur_code_polarity_st_refine[sepref_fr_rules]:
  \<open>(uncurry polarity_st_heur_code, uncurry (RETURN oo polarity_st)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>polarity_atm M (atm_of L) =
      (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: polarity_atm_def polarity_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry polarity_st_heur, uncurry (RETURN oo polarity_st)) \<in>
     [\<lambda>(_, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_heur_pol \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
       (auto simp: trail_pol_def polarity_st_def polarity_pol_def
        polarity_def polarity_st_heur_def twl_st_heur_pol_def)
  show ?thesis
    using polarity_st_heur_code.refine[FCOMP 2, OF isasat_input_bounded_axioms,
      unfolded twl_st_heur_assn_assn] .
qed


definition (in -) get_conflict_wl_is_None_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur = (\<lambda>(M, N, U, D, Q, W, _). is_None D)\<close>

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None:
    \<open>(RETURN o get_conflict_wl_is_None_heur,  RETURN o get_conflict_wl_is_None) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_def get_conflict_wl_is_None_heur_def get_conflict_wl_is_None_def
     split: option.splits)

sepref_thm get_conflict_wl_is_None_code
  is \<open>RETURN o get_conflict_wl_is_None_heur\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding get_conflict_wl_is_None_heur_def twl_st_heur_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) get_conflict_wl_is_None_code
   uses isasat_input_bounded.get_conflict_wl_is_None_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) get_conflict_wl_is_None_code_def

lemmas get_conflict_wl_is_None_code_refine[sepref_fr_rules] =
   get_conflict_wl_is_None_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma get_conflict_wl_is_None_code_get_conflict_wl_is_None[sepref_fr_rules]:
  \<open>(get_conflict_wl_is_None_code, RETURN o get_conflict_wl_is_None) \<in>
     twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wl_is_None_code_refine[FCOMP
      get_conflict_wl_is_None_heur_get_conflict_wl_is_None]
  unfolding twl_st_assn_def by fast


definition count_decided_st where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

sepref_thm count_decided_st_code
  is \<open>RETURN o count_decided_st\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding count_decided_st_def twl_st_heur_assn_def
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

lemma count_decided_refine[sepref_fr_rules]:
  \<open>(count_decided_st_code, RETURN \<circ> count_decided_st) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  using count_decided_st_code_refine[FCOMP count_decided_st_count_decided_st]
  unfolding twl_st_assn_def
  .

lemma count_decided_st_alt_def: \<open>count_decided_st S = count_decided (get_trail_wl S)\<close>
  unfolding count_decided_st_def
  by (cases S) auto


definition (in -) is_in_conflict_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>is_in_conflict_st L S \<longleftrightarrow> is_in_conflict L (get_conflict_wl S)\<close>

definition literal_is_in_conflict_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict_heur = (\<lambda>L (M, N, U, D, _). L \<in># the D)\<close>

lemma literal_is_in_conflict_heur_is_in_conflict_st:
  \<open>(uncurry (RETURN oo literal_is_in_conflict_heur), uncurry (RETURN oo is_in_conflict_st)) \<in>
   Id \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (auto simp: literal_is_in_conflict_heur_def is_in_conflict_st_def twl_st_heur_def)

sepref_thm literal_is_in_conflict_heur_code
  is \<open>uncurry (RETURN oo literal_is_in_conflict_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
        get_conflict_wl_heur S \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding literal_is_in_conflict_heur_def twl_st_heur_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def
  by sepref

concrete_definition (in -) literal_is_in_conflict_heur_code
   uses isasat_input_bounded.literal_is_in_conflict_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) literal_is_in_conflict_heur_code_def

lemmas literal_is_in_conflict_heur_code_refine[sepref_fr_rules] =
   literal_is_in_conflict_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma literal_is_in_conflict_heur_code_is_in_conflict_st[sepref_fr_rules]:
  \<open>(uncurry literal_is_in_conflict_heur_code,
     uncurry (RETURN oo is_in_conflict_st)) \<in>
    [\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
      get_conflict_wl S \<noteq> None]\<^sub>a
    unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f twl_st_heur) (\<lambda>_. True)
         (\<lambda>_ (L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
           get_conflict_wl_heur S \<noteq> None)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k) (Id \<times>\<^sub>f twl_st_heur) \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF literal_is_in_conflict_heur_code_refine
        literal_is_in_conflict_heur_is_in_conflict_st]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_lookup_clause_rel_def lookup_clause_rel_def
    by (auto simp: image_image twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

end

abbreviation (in -) nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>

datatype ('a ,'b) state = Small 'a | Big 'b

definition state_ref where
  \<open>state_ref = {(S', S). (length (get_clauses_wl S) \<le> uint64_max \<longrightarrow> S' = Small S) \<or> S' = Big S}\<close>


end