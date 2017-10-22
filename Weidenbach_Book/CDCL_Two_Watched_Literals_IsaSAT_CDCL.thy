theory CDCL_Two_Watched_Literals_IsaSAT_CDCL
  imports CDCL_Two_Watched_Literals_Watch_List_Code_Common
    CDCL_Two_Watched_Literals_VMTF
begin


no_notation Ref.update ("_ := _" 62)

notation prod_rel_syn (infixl "\<times>\<^sub>f" 70)
(* TODO Move *)
declare cdcl\<^sub>W_restart_mset_state[simp]
lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo (op =))) \<in>
    (option_assn bool_assn)\<^sup>k *\<^sub>a (option_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: option_assn_alt_def split:option.splits)

declare option_assn_eq[sepref_comb_rules del]
(* End Move *)

subsection \<open>Code Generation\<close>

subsubsection \<open>Types and Refinement Relations\<close>

type_synonym trail_pol = \<open>(nat, nat) ann_lits \<times> bool option list \<times> nat list \<times> nat\<close>
type_synonym trail_pol_assn = \<open>(uint32 \<times> nat option) list \<times> bool option array \<times> uint32 array \<times> uint32\<close>

type_synonym twl_st_wll_trail =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_option_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times>
    uint32\<close>

definition polarity_atm where
  \<open>polarity_atm M L =
    (if Pos L \<in> lits_of_l M then Some True
    else if Neg L \<in> lits_of_l M then Some False
    else None)\<close>

definition get_level_atm where
  \<open>get_level_atm M L = get_level M (Pos L)\<close>

context isasat_input_ops
begin

definition trail_pol :: \<open>(trail_pol \<times> (nat, nat) ann_lits) set\<close> where
  \<open>trail_pol = {((M', xs, lvls, k), M). M = M' \<and> no_dup M \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length xs \<and> xs ! (atm_of L) = polarity_atm M (atm_of L)) \<and>
    (\<forall>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length lvls \<and> lvls ! (atm_of L) = get_level M L) \<and>
    k = count_decided M \<and>
    (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)}\<close>

end

abbreviation trail_pol_assn :: \<open>trail_pol \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_pol_assn \<equiv> pair_nat_ann_lits_assn *assn array_assn (option_assn bool_assn) *assn
      array_assn uint32_nat_assn *assn uint32_nat_assn\<close>

abbreviation phase_saver_conc where
  \<open>phase_saver_conc \<equiv> array_assn bool_assn\<close>

text \<open>\<^emph>\<open>heur\<close> stands for heuristic.\<close>
type_synonym twl_st_wl_heur =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat clause option \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times>
    nat\<close>

type_synonym twl_st_wl_heur_trail_ref =
  \<open>trail_pol \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times> nat\<close>

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
  \<open>get_count_max_lvls_heur (_, _, _, _, _, _, _, _, clvls) = clvls\<close>

context isasat_input_ops
begin

abbreviation trail_assn :: \<open>(nat, nat) ann_lits \<Rightarrow> trail_pol_assn \<Rightarrow> assn\<close> where
  \<open>trail_assn \<equiv> hr_comp trail_pol_assn trail_pol\<close>

definition (in -) card_max_lvl where
  \<open>card_max_lvl M C \<equiv> size (filter_mset (\<lambda>L. get_level M L = count_decided M) C)\<close>

lemma card_max_lvl_add_mset: \<open>card_max_lvl M (add_mset L C) =
  (if get_level M L = count_decided M then 1 else 0) +
    card_max_lvl M C\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_empty[simp]: \<open>card_max_lvl M {#} = 0\<close>
  by (auto simp: card_max_lvl_def)

lemma card_max_lvl_all_poss:
   \<open>card_max_lvl M C = card_max_lvl M (poss (atm_of `# C))\<close>
  unfolding card_max_lvl_def
  apply (induction C)
  subgoal by auto
  subgoal for L C
    using get_level_uminus[of M L]
    by (cases L) (auto)
  done

lemma card_max_lvl_distinct_cong:
  assumes
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C) \<Longrightarrow> (L \<in> atms_of C')\<close> and
    \<open>\<And>L. get_level M (Pos L) = count_decided M \<Longrightarrow> (L \<in> atms_of C') \<Longrightarrow> (L \<in> atms_of C)\<close> and
    \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> and
    \<open>distinct_mset C'\<close> \<open>\<not>tautology C'\<close>
  shows \<open>card_max_lvl M C = card_max_lvl M C'\<close>
proof -
  have [simp]: \<open>NO_MATCH (Pos x) L \<Longrightarrow> get_level M L = get_level M (Pos (atm_of L))\<close> for x L
    by (simp add: get_level_def)
  have [simp]: \<open>atm_of L \<notin> atms_of C' \<longleftrightarrow> L \<notin># C' \<and> -L \<notin># C'\<close> for L C'
    by (cases L) (auto simp: atm_iff_pos_or_neg_lit)
  then have [iff]: \<open>atm_of L \<in> atms_of C' \<longleftrightarrow> L \<in># C' \<or> -L \<in># C'\<close> for L C'
    by blast
  have H: \<open>distinct_mset {#L \<in># poss (atm_of `# C). get_level M L = count_decided M#}\<close>
    if \<open>distinct_mset C\<close> \<open>\<not>tautology C\<close> for C
    using that by (induction C) (auto simp: tautology_add_mset atm_of_eq_atm_of)
  show ?thesis
    apply (subst card_max_lvl_all_poss)
    apply (subst (2) card_max_lvl_all_poss)
    unfolding card_max_lvl_def
    apply (rule arg_cong[of _ _ size])
    apply (rule distinct_set_mset_eq)
    subgoal by (rule H) (use assms in fast)+
    subgoal by (rule H) (use assms in fast)+
    subgoal using assms by (auto simp: atms_of_def imageI image_iff) blast+
    done
qed

definition counts_maximum_level where
  \<open>counts_maximum_level M C = {i. C \<noteq> None \<longrightarrow> i = card_max_lvl M (the C)}\<close>

lemma counts_maximum_level_None[simp]: \<open>counts_maximum_level M None = Collect (\<lambda>_. True)\<close>
  by (auto simp: counts_maximum_level_def)

definition twl_st_heur :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D
  }\<close>

definition twl_st_heur_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_heur_assn =
  trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc *assn
  uint32_nat_assn\<close>

definition twl_st_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_assn = hr_comp twl_st_heur_assn twl_st_heur\<close>

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


subsubsection \<open>Refining code\<close>

definition conflict_merge :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> nat clause option \<Rightarrow> nat \<Rightarrow>
  (nat clause option \<times> nat) nres\<close> where
\<open>conflict_merge M N i _ _ = RES{(Some (mset (N!i)), card_max_lvl M (mset (N!i)))}\<close>

definition add_to_lookup_conflict :: \<open>nat literal \<Rightarrow> conflict_rel \<Rightarrow> conflict_rel\<close> where
  \<open>add_to_lookup_conflict = (\<lambda>L (n, xs). (if xs ! atm_of L = None then n + 1 else n,
      xs[atm_of L := Some (is_pos L)]))\<close>

context isasat_input_bounded
begin

paragraph \<open>Unit propagation, body of the inner loop\<close>


lemma add_to_lookup_conflict_conflict_rel:
  assumes confl: \<open>((n, xs), C) \<in> conflict_rel\<close> and uL_C: \<open>-L \<notin># C\<close> and L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows \<open>(add_to_lookup_conflict L (n, xs), {#L#} \<union># C) \<in> conflict_rel\<close>
proof -
  have
    n: \<open>n = size C\<close> and
    mset: \<open>mset_as_position xs C\<close> and
    atm: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close>
    using confl unfolding conflict_rel_def by blast+
  have \<open>distinct_mset C\<close>
    using mset by (blast dest: mset_as_position_distinct_mset)
  have atm_L_xs: \<open>atm_of L < length xs\<close>
    using atm L_\<L>\<^sub>a\<^sub>l\<^sub>l by (auto simp: atms_of_def)
  then show ?thesis
  proof (cases \<open>L \<in># C\<close>)
    case True
    with mset have xs: \<open>xs ! atm_of L = Some (is_pos L)\<close> \<open>xs ! atm_of L \<noteq> None\<close>
      by (auto dest: mset_as_position_nth)
    moreover have \<open>{#L#} \<union># C = C\<close>
      using True by (simp add: subset_mset.sup.absorb2)
    ultimately show ?thesis
      using n mset atm True
      by (auto simp: conflict_rel_def add_to_lookup_conflict_def xs[symmetric])
  next
    case False
    with mset have \<open>xs ! atm_of L = None\<close>
      using mset_as_position_in_iff_nth[of xs C L]
       mset_as_position_in_iff_nth[of xs C \<open>-L\<close>]  atm_L_xs uL_C
      by (cases L; cases \<open>xs ! atm_of L\<close>) auto
    then show ?thesis
      using n mset atm False atm_L_xs uL_C
      by (auto simp: conflict_rel_def add_to_lookup_conflict_def
          intro!: mset_as_position.intros)
  qed
qed

definition is_in_lookup_conflict where
  \<open>is_in_lookup_conflict = (\<lambda>(n, xs) L. \<not>is_None (xs ! atm_of L))\<close>

sepref_thm is_in_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_conflict)\<close>
  :: \<open>[\<lambda>((n, xs), L). atm_of L < length xs]\<^sub>a
       conflict_rel_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> bool_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp] uint32_nat_assn_one[sepref_fr_rules]
  image_image[simp]
  unfolding is_in_lookup_conflict_def
  by sepref

concrete_definition (in -) is_in_conflict_code
   uses isasat_input_bounded.is_in_conflict_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) is_in_conflict_code_def

lemmas is_in_conflict_hnr[sepref_fr_rules] =
   is_in_conflict_code.refine[OF isasat_input_bounded_axioms]

definition lookup_conflict_merge
  :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause_l \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> (conflict_option_rel \<times> nat) nres\<close>
where
  \<open>lookup_conflict_merge M D  = (\<lambda>(b, xs) clvls. do {
     (_, clvls, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i::nat, clvls :: nat, zs). i \<le> length D \<and>
         length (snd zs) = length (snd xs) \<and>
             Suc i \<le> uint_max \<and> Suc (fst zs) \<le> uint_max \<and> Suc clvls \<le> uint_max\<^esup>
       (\<lambda>(i :: nat, clvls, zs). i < length D)
       (\<lambda>(i :: nat, clvls, zs). do{
           ASSERT(i < length D);
           ASSERT(Suc i \<le> uint_max);
            if get_level M (D!i) = count_decided M \<and> \<not>is_in_lookup_conflict zs (D!i) then
             RETURN(Suc i, clvls + 1, add_to_lookup_conflict (D!i) zs)
           else
             RETURN(Suc i, clvls, add_to_lookup_conflict (D!i) zs)
           })
       (0, clvls, xs);
     RETURN ((False, zs), clvls)
   })\<close>

definition lookup_conflict_merge_aa :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clauses_l \<Rightarrow> nat \<Rightarrow> conflict_option_rel \<Rightarrow> nat \<Rightarrow> (conflict_option_rel \<times> nat) nres\<close> where
  \<open>lookup_conflict_merge_aa M C i xs = lookup_conflict_merge M (C ! i) xs\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset xs)\<close> and
    i_xs: \<open>i < length xs\<close>
  shows \<open>xs ! i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
proof -
  have \<open>xs ! i \<in># mset xs\<close>
    using i_xs by auto
  then have \<open>xs ! i \<in> set_mset (all_lits_of_m (mset xs))\<close>
    by (auto simp: in_all_lits_of_m_ain_atms_of_iff)
  then show ?thesis
    using N1 unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_def by blast
qed

definition get_level_atm_pol :: \<open>trail_pol \<Rightarrow> uint32 \<Rightarrow> nat\<close> where
  \<open>get_level_atm_pol = (\<lambda>(M, xs, lvls, k) L. lvls ! (nat_of_uint32 L))\<close>

sepref_thm get_level_atm_code
  is \<open>uncurry (RETURN oo get_level_atm_pol)\<close>
  :: \<open>[\<lambda>((M, xs, lvls, k), L). nat_of_uint32 L < length lvls]\<^sub>a
  trail_pol_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_atm_pol_def nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) get_level_atm_code
   uses isasat_input_bounded.get_level_atm_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_atm_code_def

lemmas get_level_atm_code_hnr[sepref_fr_rules] =
   get_level_atm_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma get_level_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry get_level_atm_code, uncurry (RETURN oo get_level_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [simp]: \<open>(ba, bb) \<in> nat_lit_rel \<Longrightarrow> ba div 2 = atm_of bb\<close> for ba bb
    by (auto simp: p2rel_def lit_of_natP_def atm_of_lit_of_nat nat_lit_rel_def
        simp del: literal_of_nat.simps)

  have 1: \<open>(uncurry (RETURN oo get_level_atm_pol), uncurry (RETURN oo get_level_atm)) \<in>
     [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>f uint32_nat_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI, rename_tac x y, case_tac x)
      (auto 5 5 simp: image_image trail_pol_def get_level_atm_pol_def get_level_atm_def
        nat_shiftr_div2 shiftr1_def unat_lit_rel_def nat_lit_rel_def uint32_nat_rel_def br_def
        nat_of_uint32_shiftr get_level_def)

  have H: \<open>(uncurry get_level_atm_code, uncurry (RETURN \<circ>\<circ> get_level_atm))
  \<in> [comp_PRE (trail_pol \<times>\<^sub>f uint32_nat_rel)
       (\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0)
       (\<lambda>_ ((M, xs, lvls, k), L). nat_of_uint32 L < length lvls)
       (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k *\<^sub>a uint32_assn\<^sup>k)
                      (trail_pol \<times>\<^sub>f
                       uint32_nat_rel) \<rightarrow> hr_comp uint32_nat_assn
          nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF get_level_atm_code.refine 1, OF isasat_input_bounded_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto 5 5 simp: comp_PRE_def trail_pol_def unat_lit_rel_def nat_lit_rel_def
        uint32_nat_rel_def br_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f by simp
qed

lemma (in -) get_level_get_level_atm: \<open>get_level M L = get_level_atm M (atm_of L)\<close>
  unfolding get_level_atm_def
  by (cases L) (auto simp: get_level_Neg_Pos)

sepref_thm get_level_code
  is \<open>uncurry (RETURN oo get_level)\<close>
  :: \<open>[\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding get_level_get_level_atm nat_shiftr_div2[symmetric] nat_of_uint32_shiftr[symmetric]
  nth_u_def[symmetric]
  supply [[goals_limit = 1]] image_image[simp] in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[simp]
  by sepref

concrete_definition (in -) get_level_code
   uses isasat_input_bounded.get_level_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) get_level_code_def

lemmas get_level_code_get_level_code[sepref_fr_rules] =
   get_level_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

definition (in -) count_decided_pol where
  \<open>count_decided_pol = (\<lambda>(_, _, _, k). k)\<close>
lemma count_decided_trail_ref:
  \<open>(RETURN o count_decided_pol, RETURN o count_decided) \<in> trail_pol \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: trail_pol_def count_decided_pol_def)

lemma count_decided_trail:
   \<open>(return o count_decided_pol, RETURN o count_decided_pol) \<in> trail_pol_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  by sepref_to_hoare (sep_auto simp: count_decided_pol_def)

lemmas count_decided_trail_code[sepref_fr_rules] =
   count_decided_trail[FCOMP count_decided_trail_ref]

sepref_register lookup_conflict_merge_aa
sepref_thm lookup_conflict_merge_code
  is \<open>uncurry4 (PR_CONST lookup_conflict_merge_aa)\<close>
  :: \<open>[\<lambda>((((M, N), i), (_, xs)), _). i < length N \<and> (\<forall>j<length (N!i). atm_of (N!i!j) < length (snd xs)) \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i))]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
      conflict_option_rel_assn *assn uint32_nat_assn\<close>
  supply length_rll_def[simp] nth_rll_def[simp] uint_max_def[simp] uint32_nat_assn_one[sepref_fr_rules]
  image_image[simp] literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[simp]
  unfolding lookup_conflict_merge_aa_def lookup_conflict_merge_def add_to_lookup_conflict_def PR_CONST_def
  nth_rll_def[symmetric] length_rll_def[symmetric]
  apply (rewrite at \<open>_ + \<hole>\<close> annotate_assn[where A = \<open>uint32_nat_assn\<close>])
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) lookup_conflict_merge_code
   uses isasat_input_bounded.lookup_conflict_merge_code.refine_raw
   is \<open>(uncurry4 ?f, _) \<in> _\<close>

prepare_code_thms (in -) lookup_conflict_merge_code_def

lemmas lookup_conflict_merge_aa_hnr[sepref_fr_rules] =
   lookup_conflict_merge_code.refine[OF isasat_input_bounded_axioms]

definition lookup_conflict_merge'_step :: \<open>(nat, nat) ann_lits \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> conflict_rel \<Rightarrow> nat clause_l \<Rightarrow>
      nat clause \<Rightarrow> bool\<close> where
  \<open>lookup_conflict_merge'_step M i clvls zs D C = (
      let D' = mset (take i D);
          E = remdups_mset (D' + (C - D' - image_mset uminus D')) in
      ((False, zs), Some E) \<in> option_conflict_rel \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n E \<and> clvls = card_max_lvl M E)\<close>

lemma mset_as_position_remove:
  \<open>mset_as_position xs D \<Longrightarrow> L < length xs \<Longrightarrow> mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) D))\<close>
proof (induction rule: mset_as_position.induct)
  case (empty n)
  then have [simp]: \<open>replicate n None[L := None] = replicate n None\<close>
    using list_update_id[of \<open>replicate n None\<close> L] by auto
  show ?case by (auto intro: mset_as_position.intros)
next
  case (add xs P K xs')
  show ?case
  proof (cases \<open>L = atm_of K\<close>)
    case True
    then show ?thesis
      using add by (cases K) auto
  next
    case False
    have map: \<open>mset_as_position (xs[L := None]) (remove1_mset (Pos L) (remove1_mset (Neg L) P))\<close>
      using add by auto
    have \<open>K \<notin># P - {#Pos L, Neg L#}\<close> \<open>-K \<notin># P - {#Pos L, Neg L#}\<close>
      by (auto simp: add.hyps dest!: in_diffD)
    then show ?thesis
      using mset_as_position.add[OF map, of \<open>K\<close> \<open>xs[L := None, atm_of K := Some (is_pos K)]\<close>]
        add False list_update_swap[of \<open>atm_of K\<close> L xs] apply simp
      apply (subst diff_add_mset_swap)
      by auto
  qed
qed

lemma option_conflict_rel_update_None:
  assumes  \<open>((False, (n, xs)), Some D) \<in> option_conflict_rel\<close> and L_xs : \<open>L < length xs\<close>
  shows \<open>((False, (if xs!L = None then n else n - 1, xs[L := None])),
      Some (D - {# Pos L, Neg L #})) \<in> option_conflict_rel\<close>
proof -
  have [simp]: "L \<notin># A \<Longrightarrow> A - add_mset L' (add_mset L B) = A - add_mset L' B"
    for A B :: \<open>'a multiset\<close> and L L'
    by (metis add_mset_commute minus_notin_trivial)
  have "n = size D" and map: "mset_as_position xs D"
    using assms by (auto simp: option_conflict_rel_def conflict_rel_def)
  have xs_None_iff: "xs ! L = None \<longleftrightarrow> Pos L \<notin># D \<and> Neg L \<notin># D"
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  have 1: \<open>xs ! L = None \<Longrightarrow> D - {#Pos L, Neg L#} = D\<close>
    using assms by (auto simp: xs_None_iff minus_notin_trivial)
  have 2: \<open>xs ! L = None \<Longrightarrow> xs[L := None] = xs\<close>
   using map list_update_id[of xs L] by (auto simp: 1)
  have 3: \<open>xs ! L = Some y \<longleftrightarrow> (y \<and> Pos L \<in># D \<and> Neg L \<notin># D) \<or> (\<not>y \<and> Pos L \<notin># D \<and> Neg L \<in># D)\<close> for y
    using map L_xs mset_as_position_in_iff_nth[of xs D "Pos L"] mset_as_position_in_iff_nth[of xs D "Neg L"]
    by (cases \<open>xs ! L\<close>) auto

  show ?thesis
    using assms mset_as_position_remove[of xs D L]
    by (auto simp: option_conflict_rel_def conflict_rel_def 1 2 3 size_remove1_mset_If minus_notin_trivial
        mset_as_position_remove)
qed

lemma add_to_lookup_conflict_option_conflict_rel:
  assumes ocr: \<open>((False, (n, zs)), Some D) \<in> option_conflict_rel\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and L_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  shows
    \<open>((False, add_to_lookup_conflict L (n, zs)), Some (remdups_mset (remove1_mset (-L) (add_mset L D))))
        \<in> option_conflict_rel\<close>
proof -
  have minus_remove1_mset:  \<open>A - {#L, L'#} = remove1_mset L (remove1_mset L' A)\<close>
    for L L' and A :: \<open>'a multiset\<close>
    by (auto simp: ac_simps)
  have c_r: \<open>((n, zs), D) \<in> conflict_rel\<close>
    using ocr unfolding option_conflict_rel_def by auto
  then have L: \<open>atm_of L < length zs\<close>
    using L_\<L>\<^sub>a\<^sub>l\<^sub>l unfolding conflict_rel_def by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have [simp]: \<open>distinct_mset D\<close>
    using mset_as_position_distinct_mset[of zs D] c_r unfolding conflict_rel_def by auto
  then have uL_DLL: \<open>- L \<notin># D - {#L, - L#}\<close> and L_DLL: \<open>L \<notin># D - {#L, - L#}\<close>
    using distinct_mem_diff_mset by force+
  have [simp]: \<open>zs ! atm_of L \<noteq> None \<Longrightarrow> n > 0\<close>
    using mset_as_position_in_iff_nth[of zs D L] mset_as_position_in_iff_nth[of zs D \<open>-L\<close>] L c_r
    unfolding conflict_rel_def by (cases L) (auto dest: size_diff_se)
  have \<open>((False, (if zs!(atm_of L) = None then n else n - 1,
         zs[atm_of L := None])), Some (D - {#L, -L#})) \<in> option_conflict_rel\<close>
    using option_conflict_rel_update_None[OF ocr L]
    by (metis (no_types, lifting) add_mset_commute literal.exhaust_sel uminus_Neg uminus_Pos)
  then have \<open>((if zs ! atm_of L = None then n else n - 1, zs[atm_of L := None]), D - {#L, - L#})
     \<in> conflict_rel\<close>
    by (auto simp: option_conflict_rel_def)
  from add_to_lookup_conflict_conflict_rel[OF this _ L_\<L>\<^sub>a\<^sub>l\<^sub>l] have
    \<open>((False, (if zs!(atm_of L) = None then n+1 else n, zs[atm_of L := Some (is_pos L)])),
      Some (add_mset L (D - {#L, -L#}))) \<in> option_conflict_rel\<close>
    using uL_DLL L_DLL L by (auto simp: option_conflict_rel_def add_to_lookup_conflict_def)
  moreover have \<open>add_mset L (D - {#L, - L#}) = remdups_mset (remove1_mset (- L) (add_mset L D))\<close>
    using uL_DLL L_DLL unfolding minus_remove1_mset
    by (auto simp: minus_notin_trivial distinct_mset_remdups_mset_id simp del: diff_diff_add_mset
       dest: in_diffD)
  ultimately show ?thesis
    by (auto simp: add_to_lookup_conflict_def)
qed

lemma lookup_conflict_merge'_spec:
  assumes
      o: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close> and
      dist: \<open>distinct D\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> and
      tauto: \<open>\<not>tautology (mset D)\<close> and
      \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
      \<open>clvls = card_max_lvl M C\<close>
  shows \<open>lookup_conflict_merge M D (b, n, xs) clvls \<le> \<Down> (option_conflict_rel \<times>\<^sub>r Id)
             (RES {(Some (mset D \<union># (C - mset D - uminus `# mset D)),
              card_max_lvl M (mset D \<union># (C - mset D - uminus `# mset D)))})\<close>
proof -
  have le_D_le_upper[simp]: \<open>a < length D \<Longrightarrow> Suc (Suc a) \<le> uint_max\<close> for a
    using simple_clss_size_upper_div2[of \<open>mset D\<close>] assms by (auto simp: uint_max_def)
  have Suc_N_uint_max: \<open>Suc n \<le> uint_max\<close> and
     size_C_uint_max: \<open>size C \<le> 1 + uint_max div 2\<close> and
     clvls: \<open>clvls = card_max_lvl M C\<close> and
     tauto_C: \<open>\<not> tautology C\<close> and
     dist_C: \<open>distinct_mset C\<close> and
     atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
     map: \<open>mset_as_position xs C\<close>
    using assms simple_clss_size_upper_div2[of C] mset_as_position_distinct_mset[of xs C]
      conflict_rel_not_tautolgy[of n xs C]
    unfolding option_conflict_rel_def conflict_rel_def
    by (auto simp: uint_max_def)
  then have clvls_uint_max: \<open>clvls \<le> 1 + uint_max div 2\<close>
    using size_filter_mset_lesseq[of \<open>\<lambda>L. get_level M L = count_decided M\<close> C]
    unfolding uint_max_def card_max_lvl_def by linarith
  have [intro]: \<open>((b, a, ba), Some C) \<in> option_conflict_rel \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n C \<Longrightarrow>
        Suc (Suc a) \<le> uint_max\<close> for b a ba C
    using conflict_rel_size[of a ba C] by (auto simp: option_conflict_rel_def
        conflict_rel_def uint_max_def)
  have [simp]: \<open>remdups_mset C = C\<close>
    using o mset_as_position_distinct_mset[of xs C] by (auto simp: option_conflict_rel_def conflict_rel_def
        distinct_mset_remdups_mset_id)
  have \<open>\<not>tautology C\<close>
    using mset_as_position_tautology o by (auto simp: option_conflict_rel_def
        conflict_rel_def)
  have \<open>distinct_mset C\<close>
    using mset_as_position_distinct_mset[of _ C] o
    unfolding option_conflict_rel_def conflict_rel_def by auto
  let ?C' = \<open>\<lambda>a. mset (take a D) + (C - (mset (take a D) + uminus `# mset (take a D)))\<close>
  have tauto_C': \<open>\<not> tautology (?C' a)\<close> for a
    using tauto tauto_C dist dist_C unfolding tautology_decomp'
    by (auto dest: in_set_takeD in_diffD simp: distinct_mset_in_diff in_image_uminus_uminus)

  define I where
     \<open>I xs = (\<lambda>(i, clvls, zs :: conflict_rel).
                     i \<le> length D \<and>
                     length (snd zs) =
                     length (snd xs) \<and>
                     Suc i \<le> uint_max \<and>
                     Suc (fst zs) \<le> uint_max \<and>
                     Suc clvls \<le> uint_max)\<close>
   for xs :: conflict_rel
  define I' where \<open>I' = (\<lambda>(i, clvls, zs). lookup_conflict_merge'_step M i clvls zs D C)\<close>
  have
    if_True_I: \<open>I x2 (Suc a, aa + 1, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I) and
    if_true_I': \<open>I' (Suc a, aa + 1, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I')
    if
      I: \<open>I x2 s\<close> and
      I': \<open>I' s\<close> and
      \<open>case s of (i, clvls, zs) \<Rightarrow> i < length D\<close> and
      s: \<open>s = (a, ba)\<close> \<open>ba = (aa, baa)\<close> \<open>(b, n, xs) = (x1, x2)\<close> and
      a_le_D: \<open>a < length D\<close> and
      a_uint_max: \<open>Suc a \<le> uint_max\<close> and
      if_cond: \<open>get_level M (D ! a) = count_decided M \<and> \<not> is_in_lookup_conflict baa (D ! a)\<close>
    for x1 x2 s a ba aa baa
  proof -
    have [simp]:
      \<open>s = (a, aa, baa)\<close>
      \<open>ba = (aa, baa)\<close>
      \<open>x2 = (n, xs)\<close>
      using s by auto
    obtain ab b where baa[simp]: \<open>baa = (ab, b)\<close> by (cases baa)

    have aa: \<open>aa = card_max_lvl M (remdups_mset (?C' a))\<close> and
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_conflict_rel\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset (?C' a))\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map: \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def conflict_rel_def
      by auto

    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have [simp]: \<open>Suc (Suc aa) \<le> uint_max\<close>
      using size_C_uint_max lits
      simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close> and
      \<open>a \<le> length D\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      conflict_rel_not_tautolgy[OF cr] a_le_D lits mset_as_position_distinct_mset[OF map]
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint_max_def by auto
    show ?I
      using le_D_le_upper a_le_D ab_upper
      unfolding I_def add_to_lookup_conflict_def baa by auto
    have take_Suc_a[simp]: \<open>take (Suc a) D = take a D @ [D ! a]\<close>
      using take_Suc_conv_app_nth[OF a_le_D] .
    have [simp]: \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
      using dist tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>]; auto)
      using tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>])
      unfolding mset_append take_Suc_a by (auto simp: tautology_add_mset)
    have D_a_notin: \<open>D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])
    have uD_a_notin: \<open>-D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])

    have [simp]: \<open>D ! a \<notin># C\<close> \<open>-D ! a \<notin># C\<close> \<open>b ! atm_of (D ! a) = None\<close>
      using if_cond mset_as_position_nth[OF map, of \<open>D ! a\<close>]
        if_cond mset_as_position_nth[OF map, of \<open>-D ! a\<close>] D_a_notin uD_a_notin
      by (auto simp: is_in_lookup_conflict_def  split: option.splits bool.splits
          dest: in_diffD)
    have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

    have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
        \<in> option_conflict_rel\<close>
      using ocr D_a_notin uD_a_notin
      unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def
      by (auto dest: in_diffD simp: minus_notin_trivial
          intro!: mset_as_position.intros)

    show ?I'
      using D_a_notin uD_a_notin ocr lits if_cond
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          card_max_lvl_add_mset aa)
  qed
  have uL_C_if_L_C: \<open>-L \<notin># C\<close> if \<open>L \<in># C\<close> for L
    using tauto_C that unfolding tautology_decomp' by blast
  have
    if_False_I: \<open>I x2 (Suc a, aa, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I) and
    if_False_I': \<open>I' (Suc a, aa, add_to_lookup_conflict (D ! a) baa)\<close> (is ?I')
    if
      I: \<open>I x2 s\<close> and
      I': \<open>I' s\<close> and
      \<open>case s of (i, clvls, zs) \<Rightarrow> i < length D\<close> and
      s: \<open>s = (a, ba)\<close> \<open>ba = (aa, baa)\<close> \<open>(b, n, xs) = (x1, x2)\<close> and
      a_le_D: \<open>a < length D\<close> and
      a_uint_max: \<open>Suc a \<le> uint_max\<close> and
      if_cond: \<open>\<not>(get_level M (D ! a) = count_decided M \<and> \<not> is_in_lookup_conflict baa (D ! a))\<close>
    for x1 x2 s a ba aa baa
  proof -
    have [simp]:
      \<open>s = (a, aa, baa)\<close>
      \<open>ba = (aa, baa)\<close>
      \<open>x2 = (n, xs)\<close>
      using s by auto
    obtain ab b where baa[simp]: \<open>baa = (ab, b)\<close> by (cases baa)

    have aa: \<open>aa = card_max_lvl M (remdups_mset (?C' a))\<close> and
      ocr: \<open>((False, ab, b), Some (remdups_mset (?C' a))) \<in> option_conflict_rel\<close> and
      lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (remdups_mset (?C' a))\<close>
      using I'
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by auto
    have
      ab: \<open>ab = size (remdups_mset (?C' a))\<close> and
      map': \<open>mset_as_position b (remdups_mset (?C' a))\<close> and
      \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length b\<close> and
      cr: \<open>((ab, b), remdups_mset (?C' a)) \<in> conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def conflict_rel_def
      by auto

    have \<open>size (card_max_lvl M (remdups_mset (?C' a))) \<le> size (remdups_mset (?C' a))\<close>
      unfolding card_max_lvl_def
      by auto
    then have Suc_Suc_aa: \<open>Suc (Suc aa) \<le> uint_max\<close>
      using size_C_uint_max lits
      simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      unfolding uint_max_def aa[symmetric]
      by (auto simp: tauto_C')
    have [simp]: \<open>length b = length xs\<close> and
      \<open>a \<le> length D\<close>
      using I unfolding I_def by simp_all

    have ab_upper: \<open>Suc (Suc ab) \<le> uint_max\<close>
      using simple_clss_size_upper_div2[of \<open>remdups_mset (?C' a)\<close>]
      conflict_rel_not_tautolgy[OF cr] a_le_D lits mset_as_position_distinct_mset[OF map']
      unfolding ab literals_are_in_\<L>\<^sub>i\<^sub>n_remdups uint_max_def by auto
    show ?I
      using a_le_D ab_upper Suc_Suc_aa
      unfolding I_def add_to_lookup_conflict_def baa by auto
    have take_Suc_a[simp]: \<open>take (Suc a) D = take a D @ [D ! a]\<close>
      using take_Suc_conv_app_nth[OF a_le_D] .
    have Da_take[simp]: \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
      using dist tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>]; auto)
      using tauto apply (subst (asm) append_take_drop_id[symmetric, of _ \<open>Suc a\<close>])
      unfolding mset_append take_Suc_a by (auto simp: tautology_add_mset)
    have D_a_notin: \<open>D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])
    have uD_a_notin: \<open>-D ! a \<notin># (mset (take a D) + uminus `# mset (take a D))\<close>
      by (auto simp: uminus_lit_swap[symmetric])

    have atm_D_a_le_xs: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
      by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    have [simp]: \<open>D ! a \<notin># C - add_mset (- D ! a)
             (add_mset (D ! a)
               (mset (take a D) + uminus `# mset (take a D)))\<close>
      using dist_C in_diffD[of \<open>D ! a\<close> C \<open>add_mset (- D ! a)
               (mset (take a D) + uminus `# mset (take a D))\<close>,
          THEN multi_member_split]
      by (meson distinct_mem_diff_mset member_add_mset)

    consider
       (None) \<open>b ! atm_of (D ! a) = None\<close> |
       (SomeT) \<open>b ! atm_of (D ! a) = Some True\<close> |
       (SomeF) \<open>b ! atm_of (D ! a) = Some False\<close>
      by (cases \<open>b ! atm_of (D ! a)\<close>) auto
    then have ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a))))
      \<in> option_conflict_rel\<close>
    proof cases
      case [simp]: None
      have [simp]: \<open>D ! a \<notin># C\<close> \<open>-D ! a \<notin># C\<close>
        using if_cond mset_as_position_nth[OF map', of \<open>D ! a\<close>]
          if_cond mset_as_position_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin
        by (auto simp: is_in_lookup_conflict_def split: option.splits bool.splits
            dest: in_diffD)
      have [simp]: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)

      show ocr: \<open>((False, add_to_lookup_conflict (D ! a) (ab, b)), Some (remdups_mset (?C' (Suc a)))) \<in> option_conflict_rel\<close>
        using ocr D_a_notin uD_a_notin
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def
        by (auto dest: in_diffD simp: minus_notin_trivial
            intro!: mset_as_position.intros)
    next
      case SomeT
      have atm_Da_le: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      define Da where
        \<open>Da = Pos (atm_of (D ! a))\<close>
      have uDa_C:  \<open>-Da \<notin># C\<close> and DaC: \<open>Da \<in># C\<close>
        using if_cond mset_as_position_in_iff_nth[OF map', of \<open>D ! a\<close>] SomeT
          if_cond mset_as_position_in_iff_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin atm_Da_le
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have [simp]: \<open>add_mset (- D ! a) (add_mset (D ! a) E) =  add_mset (- Da) (add_mset (Da) E)\<close> for E
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have \<open>D ! a = Da \<or> D ! a = -Da\<close>
        by (cases \<open>D ! a\<close>) (auto simp: Da_def)
      obtain C' where C': \<open>C = add_mset Da C'\<close>
        using multi_member_split[OF DaC] by blast
      have [simp]: \<open>- Da \<notin># C'\<close> \<open>D ! a \<notin># C'\<close> \<open>Da \<notin># C'\<close> \<open>-D ! a \<notin># C'\<close>
        using uL_C_if_L_C[of \<open>D ! a\<close>] uL_C_if_L_C[of \<open>D ! a\<close>] C' dist_C unfolding Da_def
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>atm_of (D ! a) = atm_of Da\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have [simp]: \<open>Da \<notin> set (take a D)\<close> \<open>Da \<notin> uminus ` set (take a D)\<close>
        \<open>- Da \<notin> set (take a D) \<close> \<open>-Da \<notin>  uminus ` set (take a D)\<close>
        using D_a_notin uD_a_notin
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>{#Pos (atm_of Da), Neg (atm_of Da)#} = {#Da, - Da#}\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have map'': \<open>mset_as_position (b[atm_of Da := None])
          (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D)))))\<close>
        using mset_as_position_remove[of b _ \<open>atm_of Da\<close>, OF map'] atm_Da_le
        by (auto simp: C')

      have map'':\<open>mset_as_position (b[atm_of Da := Some (is_pos (D ! a))])
        (add_mset (D ! a) (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D))))))\<close>
        apply (rule mset_as_position.add[OF map''])
        subgoal using atm_Da_le by simp
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal by auto
        done
      show ?thesis
        using uDa_C SomeT dist_C  map'' atms_le_xs
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def ab Da_def[symmetric] C'
        by (auto dest:  simp: distinct_mset_in_diff minus_notin_trivial
            intro: mset_as_position.intros)
    next
      case SomeF
      have atm_Da_le: \<open>atm_of (D ! a) < length xs\<close> \<open>D ! a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
        using literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset D)\<close> a_le_D] atms_le_xs
        by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      define Da where
        \<open>Da = Neg (atm_of (D ! a))\<close>
      have uDa_C:  \<open>-Da \<notin># C\<close> and DaC: \<open>Da \<in># C\<close>
        using if_cond mset_as_position_in_iff_nth[OF map', of \<open>D ! a\<close>] SomeF
          if_cond mset_as_position_in_iff_nth[OF map', of \<open>-D ! a\<close>] D_a_notin uD_a_notin atm_Da_le
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have [simp]: \<open>add_mset (- D ! a) (add_mset (D ! a) E) =  add_mset (- Da) (add_mset (Da) E)\<close> for E
        by (cases \<open>D!a\<close>; auto simp: is_in_lookup_conflict_def is_pos_neg_not_is_pos Da_def
            split: option.splits bool.splits
            dest: in_diffD)+
      have \<open>D ! a = Da \<or> D ! a = -Da\<close>
        by (cases \<open>D ! a\<close>) (auto simp: Da_def)
      obtain C' where C': \<open>C = add_mset Da C'\<close>
        using multi_member_split[OF DaC] by blast
      have [simp]: \<open>- Da \<notin># C'\<close> \<open>D ! a \<notin># C'\<close> \<open>Da \<notin># C'\<close> \<open>-D ! a \<notin># C'\<close>
        using uL_C_if_L_C[of \<open>D ! a\<close>] uL_C_if_L_C[of \<open>D ! a\<close>] C' dist_C unfolding Da_def
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>atm_of (D ! a) = atm_of Da\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have [simp]: \<open>Da \<notin> set (take a D)\<close> \<open>Da \<notin> uminus ` set (take a D)\<close>
        \<open>- Da \<notin> set (take a D) \<close> \<open>-Da \<notin>  uminus ` set (take a D)\<close>
        using D_a_notin uD_a_notin
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+
      have [simp]: \<open>{#Pos (atm_of Da), Neg (atm_of Da)#} = {#Da, - Da#}\<close>
        by (cases \<open>D ! a\<close>; auto simp: Da_def)+

      have map'': \<open>mset_as_position (b[atm_of Da := None])
          (remdups_mset (mset (take a D) + (C' - (mset (take a D) + uminus `# mset (take a D)))))\<close>
        using mset_as_position_remove[of b _ \<open>atm_of Da\<close>, OF map'] atm_Da_le
        by (auto simp: C')

      have map'':\<open>mset_as_position (b[atm_of Da := Some (is_pos (D ! a))])
        (add_mset (D ! a) (remdups_mset (mset (take a D) +
          (C' - (mset (take a D) + uminus `# mset (take a D))))))\<close>
        apply (rule mset_as_position.add[OF map''])
        subgoal using atm_Da_le by simp
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal using dist_C by (auto simp: C' distinct_mset_in_diff)
        subgoal by auto
        done
      show ?thesis
        using uDa_C SomeF dist_C  map'' atms_le_xs
        unfolding option_conflict_rel_def conflict_rel_def add_to_lookup_conflict_def ab Da_def[symmetric] C'
        by (auto dest:  simp: distinct_mset_in_diff minus_notin_trivial
            intro: mset_as_position.intros)
    qed
    have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n
     ((mset (take a D) +
      (C -
       add_mset (- D ! a)
        (add_mset (D ! a)
          (mset (take a D) + uminus `# mset (take a D))))))\<close>
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF lits[unfolded literals_are_in_\<L>\<^sub>i\<^sub>n_remdups]])
         (auto simp: diff_le_mono2_mset)
    moreover {
      have K: \<open>D ! a = Neg L \<Longrightarrow>is_in_lookup_conflict (ab, b) (Neg L) \<Longrightarrow> L < length xs  \<Longrightarrow>
          Pos L \<notin># C \<Longrightarrow> Neg L \<notin># C \<Longrightarrow> False\<close>
        for L
      using  mset_as_position_in_iff_nth[OF map', of \<open>Pos L\<close>] that
        mset_as_position_in_iff_nth[OF map', of \<open>Neg L\<close>] Da_take
      by (cases \<open>D ! a\<close>)
       (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
          split: option.splits bool.splits
          dest: in_diffD)
      have K': \<open>D ! a = Pos L \<Longrightarrow>is_in_lookup_conflict (ab, b) (Pos L) \<Longrightarrow> L < length xs  \<Longrightarrow>
          Pos L \<notin># C \<Longrightarrow> Neg L \<notin># C \<Longrightarrow> False\<close>
        for L
      using  mset_as_position_in_iff_nth[OF map', of \<open>Pos L\<close>] that
        mset_as_position_in_iff_nth[OF map', of \<open>Neg L\<close>] Da_take
      by (cases \<open>D ! a\<close>)
       (auto simp: is_in_lookup_conflict_def dist_C distinct_mset_in_diff
          split: option.splits bool.splits
          dest: in_diffD)
      have \<open>card_max_lvl M (remdups_mset (?C' a)) = card_max_lvl M (remdups_mset (?C' (Suc a)))\<close>
      apply (rule card_max_lvl_distinct_cong)
      subgoal for L
        apply (cases \<open>D ! a\<close>)
        supply get_level_uminus[of M \<open>Pos L\<close>, simplified, simp]
        using if_cond \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
          get_level_uminus[of M \<open>Pos L\<close>, simplified]
        by (auto simp: distinct_mset_in_diff dist_C image_Un atm_of_notin_atms_of_iff
            atm_iff_pos_or_neg_lit uminus_lit_swap eq_commute[of \<open>Neg _\<close> \<open>- _\<close>]
             eq_commute[of \<open>Pos _\<close> \<open>- _\<close>])
      subgoal for L
        apply (cases \<open>D ! a\<close>)
        supply get_level_uminus[of M \<open>Pos L\<close>, simplified, simp]
        using if_cond \<open>D ! a \<notin> set (take a D)\<close> \<open>- D ! a \<notin> set (take a D)\<close>
          get_level_uminus[of M \<open>Pos L\<close>, simplified] atm_D_a_le_xs K[of L] K'[of L]
        apply (auto split: )
        apply (auto simp: distinct_mset_in_diff dist_C image_Un atm_of_notin_atms_of_iff
            atm_iff_pos_or_neg_lit uminus_lit_swap eq_commute[of \<open>Neg _\<close> \<open>- _\<close>]
             eq_commute[of \<open>Pos _\<close> \<open>- _\<close>])
        done
      subgoal by simp
      subgoal using map' mset_as_position_tautology by blast
      subgoal by simp
      subgoal using ocr unfolding option_conflict_rel_def conflict_rel_def
        by (auto dest!: mset_as_position_tautology)
      done }
    ultimately show ?I'
      using D_a_notin uD_a_notin ocr lits if_cond atm_D_a_le_xs
      unfolding I'_def lookup_conflict_merge'_step_def Let_def
      by (auto simp: minus_notin_trivial literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          card_max_lvl_add_mset aa)
  qed

  have dist_D: \<open>distinct_mset (mset D)\<close>
    using dist by auto
  have dist_CD: \<open>distinct_mset (C - mset D - uminus `# mset D)\<close>
    using \<open>distinct_mset C\<close> by auto
  have confl: \<open>lookup_conflict_merge M D (b, n, xs) clvls
    \<le> \<Down> (option_conflict_rel \<times>\<^sub>r Id)
       (RES {(Some (mset D \<union># (C - mset D - uminus `# mset D)),
              card_max_lvl M (mset D \<union># (C - mset D - uminus `# mset D)))})\<close>
    unfolding lookup_conflict_merge_aa_def lookup_conflict_merge_def PR_CONST_def
    distinct_mset_rempdups_union_mset[OF dist_D dist_CD] I_def[symmetric] conc_fun_SPEC
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(j, _). length D - j)\<close> and
          I' = I'])
    subgoal by auto
    subgoal using clvls_uint_max Suc_N_uint_max unfolding uint_max_def I_def by auto
    subgoal using assms
      unfolding lookup_conflict_merge'_step_def Let_def option_conflict_rel_def I'_def
      by (auto simp add: uint_max_def lookup_conflict_merge'_step_def option_conflict_rel_def)
    subgoal by auto
    subgoal unfolding I_def by fast
    subgoal by (rule if_True_I)
    subgoal by (rule if_true_I')
    subgoal for b' n' s j zs
      using dist lits tauto
      by (auto simp: option_conflict_rel_def take_Suc_conv_app_nth
          literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
    subgoal by (rule if_False_I)
    subgoal by (rule if_False_I')
    subgoal by auto
    subgoal using assms by (auto simp: option_conflict_rel_def lookup_conflict_merge'_step_def Let_def
          I_def I'_def)
    done
  have count_D: \<open>count (mset D) a = 1 \<or> count (mset D) a = 0\<close> for a
    using dist_D unfolding distinct_mset_def by auto
  have count_C: \<open>count C a = 1 \<or> count C a = 0\<close> for a
    using \<open>distinct_mset C\<close> unfolding distinct_mset_def by auto
  have \<open>mset D \<union># (C - mset D - image_mset uminus (mset D)) =
      mset D \<union># (C - image_mset uminus (mset D))\<close>
    apply (rule multiset_eqI)
    subgoal for a
      using count_D[of a] count_C[of a] by (auto simp: max_def)
    done
  then show ?thesis
    using confl by simp
qed

lemma lookup_conflict_merge_aa_set_conflict:
  \<open>(uncurry4 lookup_conflict_merge_aa, uncurry4 conflict_merge) \<in>
    [\<lambda>((((M, N), i), xs), clvls). i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and> \<not>tautology (mset (N ! i)) \<and> clvls = 0]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<times>\<^sub>f nat_rel \<rightarrow>
      \<langle>option_conflict_rel \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>\<not>tautology (mset C) \<Longrightarrow> j < length C \<Longrightarrow> -C ! j \<notin> set (take j C)\<close> for j C
    by (meson in_multiset_in_set in_set_takeD nth_mem_mset tautology_minus)
  have [simp]: \<open>distinct C \<Longrightarrow> j < length C \<Longrightarrow> C ! j \<notin> set (take j C)\<close> for j C
    by (simp add: index_nth_id index_take)
  have H: \<open>lookup_conflict_merge_aa M N i (b, n, xs) clvls \<le> \<Down> (option_conflict_rel \<times>\<^sub>r nat_rel)
      (conflict_merge M N i None clvls)\<close>
    if
      \<open>i < length N\<close> and
      ocr: \<open>((b, n, xs), None) \<in> option_conflict_rel\<close> and
     dist: \<open>distinct (N! i)\<close> and
     lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i))\<close> and
     tauto: \<open>\<not>tautology (mset (N ! i))\<close> and
     \<open>clvls = 0\<close>
    for b n xs N i M clvls
  proof -
    have [simp]: \<open>remdups_mset (mset (N ! i)) = mset (N!i)\<close>
      using distinct_mset_remdups_mset_id[of \<open>mset (N!i)\<close>] dist by auto
    have lookup_conflict_merge_normalise: \<open>lookup_conflict_merge M C (b, zs) = lookup_conflict_merge M C (False, zs)\<close>
      for M C zs
      unfolding lookup_conflict_merge_def by auto
    have T: \<open>((False, n, xs), Some {#}) \<in> option_conflict_rel\<close>
      using ocr unfolding option_conflict_rel_def by auto
    then show ?thesis unfolding lookup_conflict_merge_aa_def conflict_merge_def
      using lookup_conflict_merge'_spec[of False n xs \<open>{#}\<close> \<open>N!i\<close>] that dist
      by (auto simp: lookup_conflict_merge_normalise)
  qed
  show ?thesis
    unfolding lookup_conflict_merge_def uncurry_def
    by (intro nres_relI frefI) (auto simp: H)
qed

theorem lookup_conflict_merge_code_set_conflict[sepref_fr_rules]:
  \<open>(uncurry4 lookup_conflict_merge_code, uncurry4 conflict_merge) \<in>
  [\<lambda>((((M, N), i), xs), clvls). clvls = 0 \<and> i < length N \<and> xs = None \<and> distinct (N ! i) \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and> \<not> tautology (mset (N ! i))]\<^sub>a
  trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
    conflict_option_assn *assn uint32_nat_assn\<close>
   (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
   have H: \<open>?c
  \<in> [comp_PRE
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f
      option_conflict_rel \<times>\<^sub>f
      nat_rel)
     (\<lambda>((((M, N), i), xs), clvls).
         i < length N \<and>
         xs = None \<and>
         distinct (N ! i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and>
         \<not> tautology (mset (N ! i)) \<and> clvls = 0)
     (\<lambda>_ ((((M, N), i), _, xs), _).
         i < length N \<and>
         (\<forall>j<length (N ! i). atm_of (N ! i ! j) < length (snd xs)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a
                     clauses_ll_assn\<^sup>k *\<^sub>a
                     nat_assn\<^sup>k *\<^sub>a
                     conflict_option_rel_assn\<^sup>d *\<^sub>a
                     uint32_nat_assn\<^sup>k)
                    (\<langle>Id\<rangle>list_rel \<times>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel \<times>\<^sub>f
                     nat_rel \<times>\<^sub>f
                     option_conflict_rel \<times>\<^sub>f
                     nat_rel) \<rightarrow> hr_comp
                                  (conflict_option_rel_assn *assn
                                   uint32_nat_assn)
                                  (option_conflict_rel \<times>\<^sub>f nat_rel)\<close>
   (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
     using hfref_compI_PRE_aux[OF lookup_conflict_merge_code.refine[unfolded PR_CONST_def]
        lookup_conflict_merge_aa_set_conflict[unfolded PR_CONST_def], OF isasat_input_bounded_axioms]
     unfolding PR_CONST_def
     .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def in_br_conv list_mset_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        literals_to_update_wl_empty_def option_conflict_rel_def conflict_rel_def
        dest: literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp conflict_option_assn_def
    by (auto simp: prod_hrp_comp hrp_comp_def hr_comp_invalid)

  have post: \<open>?f' = ?f\<close>
    by (auto simp: twl_st_assn_def list_assn_list_mset_rel_eq_list_mset_assn
       conflict_option_assn_def)
  show ?thesis using H unfolding PR_CONST_def pre post im .
qed

lemma unit_prop_body_wl_invD:
  fixes S w K
  defines \<open>C \<equiv> (watched_by S K) ! w\<close>
  assumes inv: \<open>unit_prop_body_wl_inv S w K\<close>
  shows \<open>distinct((get_clauses_wl S)!C)\<close> and \<open>get_conflict_wl S = None\<close>
proof -
  obtain M N U D' NP UP Q W where
     S: \<open>S = (M, N, U, D', NP, UP, Q, W)\<close>
    by (cases S)
  have
     struct_invs: \<open>twl_struct_invs (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))\<close> and
     \<open>additional_WS_invs (st_l_of_wl (Some (K, w)) S)\<close> and
     corr: \<open>correct_watching S\<close> and
     \<open>w < length (watched_by S K)\<close> and
     confl: \<open>get_conflict_wl S = None\<close> and
     w_ge_0: \<open>0 < watched_by S K ! w\<close> and
     w_le_length: \<open>w < length (watched_by S K)\<close> and
     w_le_length_S: \<open>watched_by S K ! w < length (get_clauses_wl S)\<close>
    using inv unfolding unit_prop_body_wl_inv_def by fast+

  show \<open>get_conflict_wl S = None\<close>
    using confl .
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
       (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close> and
      \<open>\<forall>D\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S))).
      \<not> tautology D\<close>
      and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state
    (state\<^sub>W_of (twl_st_of (Some K) (st_l_of_wl (Some (K, w)) S)))\<close>
    using struct_invs unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have \<open>distinct_mset_set (mset ` set (tl N))\<close>
    apply (subst append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
    apply (subst set_append)
    apply (subst image_Un)
    apply (subst distinct_mset_set_union)
    using dist
    by (auto simp: C_def S cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
        mset_take_mset_drop_mset drop_Suc)
  moreover have NC: \<open>N!C \<in> set (tl N)\<close>
     using w_ge_0 w_le_length_S unfolding C_def S
     by (auto intro!: nth_in_set_tl)
  ultimately show \<open>distinct((get_clauses_wl S)!C)\<close>
     unfolding distinct_mset_set_def S by simp
qed

lemma (in -)[sepref_fr_rules]: \<open>(return o id, RETURN o nat_of_lit) \<in> unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: uint32_nat_rel_def br_def unat_lit_rel_def nat_lit_rel_def
      lit_of_natP_def)

fun watched_by_int:: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> watched\<close> where
  \<open>watched_by_int (M, N, U, D, Q, W, _) L = W ! nat_of_lit L\<close>

fun (in -) get_watched_wl :: \<open>nat twl_st_wl \<Rightarrow> (nat literal \<Rightarrow> nat list)\<close> where
  \<open>get_watched_wl (_, _, _, _, _, _, _, W) = W\<close>

fun (in -) get_watched_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat list list\<close> where
  \<open>get_watched_wl_heur (_, _, _, _, _, W, _) = W\<close>

definition (in -) watched_by_app_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app_heur = (\<lambda>(M, N, U, D, Q, W, _) L K. W ! nat_of_lit L ! K)\<close>

definition (in -) watched_by_app :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_app S L K = watched_by S L ! K\<close>

lemma watched_by_app_watched_by_app_heur:
  \<open>(uncurry2 (RETURN ooo watched_by_app_heur), uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L)]\<^sub>f
     twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: watched_by_app_heur_def watched_by_app_def twl_st_heur_def map_fun_rel_def)

sepref_thm watched_by_app_heur_code
  is \<open>uncurry2 (RETURN ooo watched_by_app_heur)\<close>
  :: \<open>[\<lambda>((S, L), K). nat_of_lit L < length (get_watched_wl_heur S) \<and> K < length (watched_by_int S L)]\<^sub>a
        twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  supply [[goals_limit=1]]
  unfolding watched_by_app_heur_def twl_st_heur_assn_def nth_rll_def[symmetric]
  by sepref

concrete_definition (in -) watched_by_app_heur_code
   uses isasat_input_bounded.watched_by_app_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) watched_by_app_heur_code_def

lemmas watched_by_app_heur_code_refine[sepref_fr_rules] =
   watched_by_app_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma watched_by_app_code_refine[sepref_fr_rules]:
  \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN ooo watched_by_app)) \<in>
    [\<lambda>((S, L), K).  L \<in> snd ` D\<^sub>0 \<and> K < length (watched_by S L)]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 watched_by_app_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_by_app))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel)
      (\<lambda>((S, L), K). L \<in> snd ` D\<^sub>0 \<and> K < length (get_watched_wl S L))
      (\<lambda>_ ((S, L), K).
          nat_of_lit L < length (get_watched_wl_heur S) \<and>
          K < length (watched_by_int S L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f Id \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF watched_by_app_heur_code_refine[unfolded PR_CONST_def]
        watched_by_app_watched_by_app_heur[unfolded PR_CONST_def]] .
  have pre: \<open>?pre' = ?pre\<close>
    by (intro ext) (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre f .
qed

(* TODO Move *)
lemma (in -) twl_struct_invs_length_clause_ge_2:
  assumes
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    i: \<open>i > 0\<close> \<open>i < length (get_clauses_wl S)\<close>
 shows \<open>length (get_clauses_wl S ! i) \<ge> 2\<close>
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)
  have \<open>twl_st_inv (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) (M, N, U, D, NP, UP, WS, Q)))\<close>
    using struct unfolding S twl_struct_invs_def by fast
  then have \<open>\<forall>x\<in>set (tl N). 2 \<le> length x \<and> distinct x\<close>
    by (auto simp: twl_st_inv.simps mset_take_mset_drop_mset')
  then show ?thesis
    using i by (auto simp: nth_in_set_tl S)
qed
(* End Move *)


lemma unit_prop_body_wl_D_invD:
  assumes \<open>unit_prop_body_wl_D_inv S w L\<close>
  shows
    \<open>w < length (watched_by S L)\<close> and
    \<open>watched_by_app S L w < length (get_clauses_wl S)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close> and
    \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and
    \<open>watched_by_app S L w > 0\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    \<open>get_conflict_wl S = None\<close> and
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! watched_by_app S L w))\<close> and
    \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
proof -
  show \<open>L \<in> snd ` D\<^sub>0\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def by fast
  show \<open>w < length (watched_by S L)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by fast
  show S_L_W_le_S: \<open>watched_by_app S L w < length (get_clauses_wl S)\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast
  show \<open>get_clauses_wl S ! watched_by_app S L w \<noteq> []\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      additional_WS_invs_def by force
  show le: \<open>Suc 0 < length (get_clauses_wl S ! watched_by_app S L w)\<close>
    using assms twl_struct_invs_length_clause_ge_2[of L w S \<open>watched_by S L ! w\<close>]
    unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
      additional_WS_invs_def by force
  have nempty: \<open>get_clauses_wl S \<noteq> []\<close> and S_L_w_ge_0: \<open>0 < watched_by_app S L w\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    additional_WS_invs_def watched_by_app_def by auto
  obtain M N U D NP UP W Q where
    S: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
    by (cases S)
  show lits_N: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! watched_by_app S L w))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def apply -
    apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth[of _ _ M U D NP UP Q W])
    apply (rule S_L_W_le_S)
    apply (rule S_L_w_ge_0)
    using S by (auto simp del: twl_st_of.simps)
  then show \<open>get_clauses_wl S ! watched_by_app S L w ! 0 \<in> snd ` D\<^sub>0\<close>
    using le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show \<open>get_clauses_wl S ! watched_by_app S L w ! Suc 0 \<in> snd ` D\<^sub>0\<close>
    using lits_N le apply (cases \<open>get_clauses_wl S ! watched_by_app S L w\<close>;
        cases \<open>tl (get_clauses_wl S ! watched_by_app S L w)\<close>;
        cases \<open>tl (tl (get_clauses_wl S ! watched_by_app S L w))\<close>)
    by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_add_mset)

  show S_L_W_ge_0: \<open>watched_by_app S L w > 0\<close> and \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and \<open>get_conflict_wl S = None\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    struct: \<open>twl_struct_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close> and
    stgy: \<open>twl_stgy_invs (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))\<close>
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def watched_by_app_def
    by fast+
  have
    all_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv
          (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding twl_struct_invs_def by fast+
  then have
     learned_tauto:
       \<open>\<forall>s\<in>#learned_clss (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, w)) S))). \<not> tautology s\<close> and
     dist:
        \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L)
            (st_l_of_wl (Some (L, w)) S)))\<close>
    using struct unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>\<forall>D\<in>mset ` set (tl (get_clauses_wl S)). distinct_mset D\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    unfolding set_append
    using dist
    apply (cases S)
    by (auto simp: drop_Suc clauses_def mset_take_mset_drop_mset
        watched_by_app_def cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct)
  then show \<open>distinct (get_clauses_wl S ! watched_by_app S L w)\<close>
    using S_L_W_le_S S_L_W_ge_0 nempty
    by (cases S; cases \<open>get_clauses_wl S\<close>)
       (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def distinct_mset_set_distinct
         clauses_def mset_take_mset_drop_mset watched_by_app_def)
qed

definition (in -) access_lit_in_clauses where
  \<open>access_lit_in_clauses S i j = (get_clauses_wl S) ! i ! j\<close>

definition (in -) access_lit_in_clauses_heur where
  \<open>access_lit_in_clauses_heur = (\<lambda>(M, N, _) i j.  N ! i ! j)\<close>


sepref_thm access_lit_in_clauses_heur_code
  is \<open>uncurry2 (RETURN ooo access_lit_in_clauses_heur)\<close>
  :: \<open>[\<lambda>(((_,N,_), i), j). i < length N \<and> j < length_rll N i]\<^sub>a
      twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply length_rll_def[simp]
  unfolding twl_st_heur_assn_def access_lit_in_clauses_heur_def
    nth_rll_def[symmetric]
  by sepref

concrete_definition (in -) access_lit_in_clauses_heur_code
   uses isasat_input_bounded.access_lit_in_clauses_heur_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) access_lit_in_clauses_heur_code_def

lemmas access_lit_in_clauses_heur_code_refine[sepref_fr_rules] =
   access_lit_in_clauses_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma access_lit_in_clauses_heur_access_lit_in_clauses:
  \<open>(uncurry2 (RETURN ooo access_lit_in_clauses_heur), uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
   twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: access_lit_in_clauses_heur_def twl_st_heur_def access_lit_in_clauses_def)

lemma access_lit_in_clauses_refine[sepref_fr_rules]:
  \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN ooo access_lit_in_clauses)) \<in>
    [\<lambda>((S, i), j). i < length (get_clauses_wl S) \<and> j < length_rll (get_clauses_wl S) i]\<^sub>a
       twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>
    unat_lit_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 access_lit_in_clauses_heur_code, uncurry2 (RETURN \<circ>\<circ>\<circ> access_lit_in_clauses))
  \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) (\<lambda>_. True)
      (\<lambda>_ (((_, N, _), i), j). i < length N \<and> j < length_rll N i) (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
             (twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel) \<rightarrow>
    hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF access_lit_in_clauses_heur_code_refine[unfolded PR_CONST_def]
        access_lit_in_clauses_heur_access_lit_in_clauses[unfolded PR_CONST_def]] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
          map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

definition (in -) find_unwatched_wl_st  :: \<open>nat twl_st_wl \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st = (\<lambda>(M, N, U, D, NP, UP, Q, W) i. do {
    find_unwatched_l M (N ! i)
  })\<close>

lemma find_unwatched_l_find_unwatched_wl_s:
  \<open>find_unwatched_l (get_trail_wl S) (get_clauses_wl S ! C) = find_unwatched_wl_st S C\<close>
  by (cases S) (auto simp: find_unwatched_wl_st_def)

definition (in -) find_unwatched :: "('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (nat option) nres" where
\<open>find_unwatched M C = do {
   S \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
    (\<forall>j. found = Some j \<longrightarrow> (i = j \<and> (undefined_lit M (C!j) \<or> C!j \<in> lits_of_l M) \<and> j < length C \<and> j \<ge> 2))\<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      ASSERT(i < length C);
      case polarity M (C!i) of
        None \<Rightarrow> do { RETURN (Some i, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some i, i)} else do { RETURN (None, i+1)})
    })
    (None, 2::nat);
  RETURN (fst S)
  }
\<close>

definition find_unwatched_wl_st_heur  :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat option nres\<close> where
\<open>find_unwatched_wl_st_heur = (\<lambda>(M, N, U, D, Q, W, vm, \<phi>) i. do {
    find_unwatched M (N ! i)
  })\<close>

paragraph \<open>Value of a literal\<close>

definition (in -) polarity_pol :: \<open>trail_pol \<Rightarrow> nat literal \<Rightarrow> bool option nres\<close> where
  \<open>polarity_pol = (\<lambda>(M, xs, lvls, k) L. do {
     ASSERT(atm_of L < length xs);
     (case xs ! (atm_of L) of
       None \<Rightarrow> RETURN None
     | Some v \<Rightarrow> if is_pos L then RETURN (Some v)
       else RETURN (Some (\<not>v)))
  })\<close>

sepref_thm polarity_pol_code
  is \<open>uncurry polarity_pol\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding polarity_pol_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) polarity_pol_code
   uses isasat_input_bounded.polarity_pol_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) polarity_pol_code_def

lemmas polarity_pol_code_polarity_refine_code[sepref_fr_rules] =
   polarity_pol_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_axioms]

lemma polarity_pol_code_polarity_refine[sepref_fr_rules]:
  \<open>(uncurry polarity_pol_code, uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>a trail_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
proof -
  have [simp]: \<open>polarity_atm M (atm_of L) = (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
    if \<open>no_dup M\<close>for M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close>
    by (cases L) (use no_dup_consistentD[of M \<open>Neg (atm_of L)\<close>] that in
        \<open>auto simp: polarity_atm_def polarity_def Decided_Propagated_in_iff_in_lits_of_l\<close>)
  have 2: \<open>(uncurry polarity_pol, uncurry (RETURN oo polarity)) \<in>
     [\<lambda>(M, L). L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>bool_rel\<rangle>option_rel\<rangle>nres_rel\<close>
    by (intro nres_relI frefI)
      (auto simp: trail_pol_def polarity_def polarity_pol_def
        split: if_splits option.splits)
  show ?thesis
    using polarity_pol_code.refine[FCOMP 2, OF isasat_input_bounded_axioms] .
qed

definition polarity_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st S = polarity (get_trail_wl S)\<close>

definition polarity_st_heur :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> _ \<Rightarrow> bool option nres\<close> where
  \<open>polarity_st_heur = (\<lambda>(M, _) L. polarity_pol M L)\<close>

(* TODO Move? *)
type_synonym twl_st_heur_pol_no_clvls =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_option_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times> uint32\<close>

definition twl_st_heur_pol_assn
  :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> twl_st_heur_pol_no_clvls \<Rightarrow> assn\<close>
where
  \<open>twl_st_heur_pol_assn =
    (trail_pol_assn *assn clauses_ll_assn *assn nat_assn *assn
    conflict_option_assn *assn
    clause_l_assn *assn
    arrayO_assn (arl_assn nat_assn) *assn
    vmtf_remove_conc *assn phase_saver_conc *assn
    uint32_nat_assn
    )\<close>

definition (in isasat_input_ops) twl_st_heur_pol :: \<open>(twl_st_wl_heur_trail_ref \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_pol =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls), (M, N, U, D, NP, UP, Q, W)).
    (M', M) \<in> trail_pol \<and> N' = N \<and> U' = U \<and> D = D' \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M \<and>
   clvls \<in> counts_maximum_level M D
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
  have [simp]: \<open>polarity_atm M (atm_of L) = (if is_pos L then polarity M L else map_option uminus (polarity M L))\<close>
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


definition cons_trail_Propagated :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Propagated L C M' = Propagated L C # M'\<close>

definition cons_trail_Propagated_tr :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>cons_trail_Propagated_tr = (\<lambda>L C (M', xs, lvls, k).
     (Propagated L C # M', xs[atm_of L := Some (is_pos L)],
      lvls[atm_of L := k], k))\<close>


lemma cons_trail_Propagated_tr:
  \<open>(uncurry2 (RETURN ooo cons_trail_Propagated_tr), uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
  [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst (fst x)\<close>)
    (auto simp: trail_pol_def polarity_atm_def cons_trail_Propagated_def uminus_lit_swap
        cons_trail_Propagated_tr_def Decided_Propagated_in_iff_in_lits_of_l nth_list_update')

lemma undefined_lit_count_decided_uint_max:
  assumes
    M_\<L>\<^sub>a\<^sub>l\<^sub>l: \<open>\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and n_d: \<open>no_dup M\<close> and
    \<open>L \<in> snd ` D\<^sub>0\<close> and \<open>undefined_lit M L\<close>
  shows \<open>Suc (count_decided M) \<le> uint_max\<close>
proof -
  have dist_atm_M: \<open>distinct_mset {#atm_of (lit_of x). x \<in># mset M#}\<close>
    using n_d by (metis distinct_mset_mset_distinct mset_map no_dup_def)
  have \<open>atm_of `# lit_of `# mset (Decided L # M) \<subseteq># remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using assms dist_atm_M
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l lits_of_def no_dup_distinct
        atm_of_eq_atm_of)
  from size_mset_mono[OF this] have 1: \<open>count_decided M + 1 \<le> size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    using length_filter_le[of is_decided M] unfolding uint_max_def count_decided_def
    by (auto simp del: length_filter_le)
  have inj_on: \<open>inj_on nat_of_lit (set_mset (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l))\<close>
    by (auto simp: inj_on_def)
  have H: \<open>xa \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<Longrightarrow> atm_of xa \<le> uint_max div 2\<close> for xa
    using in_N1_less_than_uint_max
    by (cases xa) (auto simp: uint_max_def)
  have \<open>remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l) \<subseteq># mset [0..< 1 + (uint_max div 2)]\<close>
    apply (subst distinct_subseteq_iff[THEN iffD1])
    using H distinct_image_mset_inj[OF inj_on]
    by (force simp del: literal_of_nat.simps simp: distinct_mset_mset_set
        dest: le_neq_implies_less)+
  note _ = size_mset_mono[OF this]
  moreover have \<open>size (nat_of_lit `# remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l) = size (remdups_mset \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>
    by simp
  ultimately have 2: \<open>size (remdups_mset (atm_of `# \<L>\<^sub>a\<^sub>l\<^sub>l)) \<le> 1 + uint_max div 2\<close>
    by auto

  show ?thesis
    using 1 2 by (auto simp: uint_max_def)
qed

sepref_thm cons_trail_Propagated_tr_code
  is \<open>uncurry2 (RETURN ooo cons_trail_Propagated_tr)\<close>
  :: \<open>[\<lambda>((L, C), (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Propagated_tr_def cons_trail_Propagated_tr_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cons_trail_Propagated_tr_code
  uses isasat_input_bounded.cons_trail_Propagated_tr_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Propagated_tr_code_def

lemmas cons_trail_Propagated_tr_code[sepref_fr_rules] =
  cons_trail_Propagated_tr_code.refine[OF isasat_input_bounded_axioms]

lemma cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]:
  \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN ooo cons_trail_Propagated)) \<in>
    [\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry2 cons_trail_Propagated_tr_code, uncurry2 (RETURN \<circ>\<circ>\<circ> cons_trail_Propagated))
    \<in> [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f trail_pol)
     (\<lambda>((L, C), M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ ((L, C), (M, xs, lvls, k)). atm_of L < length xs \<and> atm_of L < length lvls)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d)
                     (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                      trail_pol) \<rightarrow> hr_comp trail_pol_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Propagated_tr_code.refine cons_trail_Propagated_tr,
        OF isasat_input_bounded_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def trail_pol_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre .
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
  using get_conflict_wl_is_None_code_refine[FCOMP get_conflict_wl_is_None_heur_get_conflict_wl_is_None]
  unfolding twl_st_assn_def by fast

end


context isasat_input_bounded_nempty
begin

sepref_thm find_unwatched_wl_st_heur_code
  is \<open>uncurry ((PR_CONST find_unwatched_wl_st_heur))\<close>
  :: \<open>[\<lambda>(S, i). i < length (get_clauses_wl_heur S) \<and> i > 0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S]\<^sub>a
         twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  supply [[goals_limit = 1]] literals_are_in_\<L>\<^sub>i\<^sub>n_heur_in_D\<^sub>0'[intro] nth_rll_def[simp]
    length_rll_def[simp]
  unfolding find_unwatched_wl_st_heur_def twl_st_heur_assn_def PR_CONST_def
  find_unwatched_def nth_rll_def[symmetric] length_rll_def[symmetric]
  by sepref

concrete_definition (in -) find_unwatched_wl_st_heur_code
   uses isasat_input_bounded_nempty.find_unwatched_wl_st_heur_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) find_unwatched_wl_st_heur_code_def

lemmas find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[sepref_fr_rules] =
   find_unwatched_wl_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma (in -) find_unwatched:
  assumes \<open>no_dup M\<close> and \<open>length C \<ge> 2\<close>
  shows \<open>find_unwatched M C \<le> find_unwatched_l M C\<close>
  unfolding find_unwatched_def find_unwatched_l_def
  apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(found, i). Suc (length C) - i +
        If (found = None) 1 0)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal using assms by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal for s
    by (auto simp: Decided_Propagated_in_iff_in_lits_of_l not_less_less_Suc_eq polarity_def
        split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: polarity_def split: if_splits)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using distinct_consistent_interp[OF assms(1)]
    apply (auto simp: Decided_Propagated_in_iff_in_lits_of_l consistent_interp_def all_set_conv_nth
       polarity_def split: if_splits intro: exI[of _ \<open>snd s - 2\<close>])
    by (metis atLeastLessThan_iff less_antisym)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for s using no_dup_consistentD[OF assms(1)]
    by (cases s, cases \<open>fst s\<close>)
      (auto simp: Decided_Propagated_in_iff_in_lits_of_l all_set_conv_nth
        intro!: exI[of _ \<open>snd s - 2\<close>])
  subgoal by auto
  subgoal for s j by auto
  subgoal by auto
  done

theorem find_unwatched_wl_st_heur_find_unwatched_wl_s:
  \<open>(uncurry find_unwatched_wl_st_heur, uncurry find_unwatched_wl_st)
    \<in> [\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
      length (get_clauses_wl S ! i) \<ge> 2]\<^sub>f
      twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: find_unwatched_wl_st_def find_unwatched_wl_st_heur_def twl_st_heur_def
    find_unwatched)

theorem find_unwatched_wl_st_heur_code_find_unwatched_wl_s[sepref_fr_rules]:
  \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [\<lambda>(S, i). \<exists>w L. unit_prop_body_wl_D_inv S w L \<and> i = watched_by_app S L w]\<^sub>a
      twl_st_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> option_assn nat_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry find_unwatched_wl_st_heur_code, uncurry find_unwatched_wl_st)
    \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f nat_rel)
         (\<lambda>(S, i). i < length (get_clauses_wl S) \<and> 0 < i \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
            2 \<le> length (get_clauses_wl S ! i))
         (\<lambda>_ (S, i). i < length (get_clauses_wl_heur S) \<and> 0 < i \<and> literals_are_in_\<L>\<^sub>i\<^sub>n_heur S)
         (\<lambda>_. True)]\<^sub>a
       hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f nat_rel) \<rightarrow>
       hr_comp (option_assn nat_assn) Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unwatched_wl_st_heur_code_find_unwatched_wl_st_heur[unfolded PR_CONST_def]
    find_unwatched_wl_st_heur_find_unwatched_wl_s] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
  proof -
    have [simp]: \<open>mset `# mset (take ai (tl ah)) + ak + (mset `# mset (drop (Suc ai) ah) + al) =
      mset `# mset (tl ah) + ak + al\<close> for ai ah ak al
      apply (subst (6) append_take_drop_id[of ai, symmetric])
      unfolding mset_append drop_Suc
      by auto
    have [intro]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_heur T\<close> and \<open>get_clauses_wl_heur T = get_clauses_wl S\<close> if
       \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))))\<close> and
       \<open>(T, S) \<in> twl_st_heur\<close>
      for S and T
      using that apply (auto simp: twl_st_heur_def mset_take_mset_drop_mset
          mset_take_mset_drop_mset' clauses_def literals_are_in_\<L>\<^sub>i\<^sub>n_heur_def)
      apply (auto simp add: all_lits_of_mm_union literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
      done
    show ?thesis
      unfolding comp_PRE_def
      apply (intro ext impI conjI)
      subgoal
        using that by (auto dest: simp: unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
            unit_propagation_inner_loop_body_l_inv_def watched_by_app_def)
      subgoal
        by (use that in \<open>auto simp: comp_PRE_def unit_prop_body_wl_D_inv_def
            mset_take_mset_drop_mset clauses_def mset_take_mset_drop_mset' drop_Suc
            unit_prop_body_wl_inv_def watched_by_app_def
            unit_propagation_inner_loop_body_l_inv_def twl_st_heur_def
          simp del: twl_st_of.simps st_l_of_wl.simps\<close>)
      done
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma unit_prop_body_wl_D_invI:
  assumes \<open>unit_prop_body_wl_D_inv b ba a\<close>
  shows \<open>watched_by b a ! ba < length (get_clauses_wl b)\<close>
  subgoal
    using assms unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    by auto
  done

lemmas unit_prop_body_wl_D_invD' =
  unit_prop_body_wl_D_invD[of \<open>(M, N, U, D, NP, UP, WS, Q)\<close> for M N U D NP UP WS Q,
   unfolded watched_by_app_def,
    simplified] unit_prop_body_wl_D_invD(7)

definition set_conflict_wl' :: \<open>nat \<Rightarrow> 'v twl_st_wl \<Rightarrow> 'v twl_st_wl\<close> where
  \<open>set_conflict_wl' = (\<lambda>C (M, N, U, D, NP, UP, Q, W). (M, N, U, Some (mset (N!C)), NP, UP, {#}, W))\<close>

lemma set_conflict_wl'_alt_def:
  \<open>set_conflict_wl' i S = set_conflict_wl (get_clauses_wl S ! i) S\<close>
  by (cases S) (auto simp: set_conflict_wl'_def set_conflict_wl_def)

definition set_conflict_wl'_int :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>set_conflict_wl'_int = (\<lambda>C (M, N, U, D, Q, W, vmtf, \<phi>, clvls). do {
    let n = zero_uint32_nat;
    (D, clvls) \<leftarrow> conflict_merge M N C D n;
    RETURN (M, N, U, D, {#}, W, vmtf, \<phi>, clvls)})\<close>

sepref_thm set_conflict_wl'_int_code
  is \<open>uncurry set_conflict_wl'_int\<close>
  :: \<open>[\<lambda>(C, S). get_conflict_wl_heur S = None \<and> C < length (get_clauses_wl_heur S) \<and>
      distinct (get_clauses_wl_heur S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl_heur S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl_heur S ! C))]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]]
    lookup_conflict_merge_code_set_conflict[unfolded twl_st_heur_assn_def, sepref_fr_rules]
  unfolding set_conflict_wl'_int_def twl_st_heur_assn_def IICF_List_Mset.lms_fold_custom_empty
  by sepref

concrete_definition (in -) set_conflict_wl'_int_code
  uses isasat_input_bounded_nempty.set_conflict_wl'_int_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) set_conflict_wl'_int_code_def

lemmas set_conflict_wl'_int_code[sepref_fr_rules] =
  set_conflict_wl'_int_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma set_conflict_wl'_int_set_conflict_wl':
  \<open>(uncurry set_conflict_wl'_int, uncurry (RETURN oo set_conflict_wl')) \<in>
    nat_rel \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro nres_relI frefI)
     (auto simp: twl_st_heur_def set_conflict_wl'_int_def set_conflict_wl'_def
        conflict_merge_def bind_RES_RETURN2_eq RETURN_def[symmetric]
        counts_maximum_level_def)

lemma set_conflict_wl'_int_code_set_conflict_wl'[sepref_fr_rules]:
  \<open>(uncurry set_conflict_wl'_int_code, uncurry (RETURN oo set_conflict_wl')) \<in>
    [\<lambda>(C, S). get_conflict_wl S = None \<and> C < length (get_clauses_wl S) \<and>
      distinct (get_clauses_wl S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl S ! C)) \<and>
      \<not> tautology (mset (get_clauses_wl S ! C))]\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
    twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry set_conflict_wl'_int_code, uncurry (RETURN \<circ>\<circ> set_conflict_wl'))
  \<in> [comp_PRE (nat_rel \<times>\<^sub>f twl_st_heur) (\<lambda>_. True)
       (\<lambda>_ (C, S). get_conflict_wl_heur S = None \<and> C < length (get_clauses_wl_heur S) \<and>
           distinct (get_clauses_wl_heur S ! C) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (get_clauses_wl_heur S ! C)) \<and>
           \<not> tautology (mset (get_clauses_wl_heur S ! C)))
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d) (nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow>
     hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF set_conflict_wl'_int_code set_conflict_wl'_int_set_conflict_wl']
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def by auto
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition update_clause_wl_heur :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    (nat \<times> twl_st_wl_heur) nres\<close> where
  \<open>update_clause_wl_heur = (\<lambda>(L::nat literal) C w i f (M, N, U, D, Q, W, vm). do {
     let K' = (N!C) ! f;
     let N' = list_update N C (swap (N!C) i f);
     let W = W[nat_of_lit L := delete_index_and_swap (W ! nat_of_lit L) w];
     RETURN (w, (M, N', U, D, Q,
            W[nat_of_lit K':= W ! nat_of_lit K' @ [C]],
            vm))
  })\<close>

lemma update_clause_wl_heur_update_clause_wl:
  \<open>(uncurry5 update_clause_wl_heur, uncurry5 (update_clause_wl)) \<in>
   [\<lambda>(((((L, C), w), i), f), S). (get_clauses_wl S ! C) ! f \<noteq> L]\<^sub>f
   Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>nat_rel \<times>\<^sub>r twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: update_clause_wl_heur_def update_clause_wl_def twl_st_heur_def Let_def
      map_fun_rel_def)

lemma length_delete_index_and_swap_ll[simp]: \<open>length (delete_index_and_swap_ll s i j) = length s\<close>
  by (auto simp: delete_index_and_swap_ll_def)

sepref_thm update_clause_wl_code
  is \<open>uncurry5 update_clause_wl_heur\<close>
  :: \<open>
    [\<lambda>(((((L, C), w), i), f), S).
      C < length (get_clauses_wl_heur S) \<and>
      f < length (get_clauses_wl_heur S ! C) \<and>
      i < length (get_clauses_wl_heur S ! C) \<and>
      nat_of_lit L < length (get_watched_wl_heur S) \<and>
      nat_of_lit ((get_clauses_wl_heur S ! C) ! f)  < length (get_watched_wl_heur S) \<and>
      w < length (get_watched_wl_heur S ! nat_of_lit L)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow>
       nat_assn *assn twl_st_heur_assn\<close>
  supply [[goals_limit=1]] length_rll_def[simp] length_ll_def[simp]
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
    nth_rll_def[symmetric] delete_index_and_swap_update_def[symmetric] delete_index_and_swap_ll_def[symmetric]
   append_ll_def[symmetric]
  by sepref


concrete_definition (in -) update_clause_wl_code
  uses isasat_input_bounded_nempty.update_clause_wl_code.refine_raw
  is \<open>(uncurry5 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_clause_wl_code_def

lemmas update_clause_wl_code[sepref_fr_rules] =
  update_clause_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma
  find_unwatched_not_tauto:
    \<open>\<not>tautology(mset (get_clauses_wl S ! watched_by_app S L C))\<close>
    (is ?tauto is \<open>\<not>tautology (?D)\<close> is \<open>\<not>tautology (mset ?C)\<close>)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv None (watched_by_app S L C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close> and
    val: \<open>polarity_st S (get_clauses_wl S ! watched_by_app S L C !
         (1 - (if access_lit_in_clauses S (watched_by_app S L C) 0 = L then 0 else 1))) = Some False\<close>
      (is \<open>polarity_st _ (_ ! _ ! ?i) = Some False\<close>)
  for S C xj L
proof  -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, D, NP, UP, WS, Q)\<close>
    by (cases S)

  have \<open>consistent_interp (lits_of_l (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))))\<close>
    \<open>no_dup (trail (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))))\<close> and
    valid: \<open>valid_annotation (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by blast+
  then have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    by (cases S) (auto)

  have \<open>additional_WS_invs (st_l_of_wl (Some (L, C)) S)\<close> and C_le: \<open>C < length (watched_by S L)\<close> and
    confl: \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
  have \<open>\<forall>L\<in>#mset (unwatched_l (get_clauses_wl S ! (watched_by S L ! C))).
         - L \<in> lits_of_l (get_trail_wl S)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def
      unit_prop_body_wl_find_unwatched_inv_def watched_by_app_def
    by auto
  moreover {
    have \<open>additional_WS_invs (st_l_of_wl (Some (L, C)) S)\<close> and \<open>C < length (watched_by S L)\<close> and
      \<open>get_conflict_wl S = None\<close> and \<open>no_duplicate_queued (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S))\<close>
      using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def twl_struct_invs_def by fast+
    then have \<open>add_mset L WS \<subseteq># {#- lit_of x. x \<in># mset (convert_lits_l N M)#}\<close>
      apply (cases \<open>drop C (watched_by S L)\<close>)
      apply (simp add: S image_image split: if_splits)
      apply (simp add: S image_image split: if_splits)
      unfolding ex_disj_distrib
      by blast
    from mset_subset_eq_insertD[OF this] have \<open>- L \<in> lits_of_l (convert_lits_l N M)\<close>
      by (auto simp: lits_of_def)
  }
  moreover have \<open>- ?C ! ?i \<in> lits_of_l (convert_lits_l N M)\<close>
    using val by (auto simp: S polarity_st_def watched_by_app_def polarity_def
        access_lit_in_clauses_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  moreover have length_C: \<open>length ?C \<ge> 2\<close>
    apply (rule twl_struct_invs_length_clause_ge_2)
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def by (auto simp: watched_by_app_def)
  moreover {
    have QL: \<open>Q L ! C = hd (drop C (Q L))\<close>
      using confl C_le length_C by (auto simp: S hd_drop_conv_nth split: )
    have \<open>L \<in># mset (watched_l ?C)\<close>
      using valid confl C_le length_C by (auto simp: QL S take_2_if watched_by_app_def)
    then have \<open>N ! (Q L ! C) ! 0 = L \<or> N ! (Q L ! C) ! 1 = L\<close>
      using confl C_le length_C by (auto simp: S take_2_if watched_by_app_def QL split: if_splits)
  }
  ultimately have Not: \<open>lits_of_l (get_trail_wl S) \<Turnstile>s CNot ?D\<close>
    unfolding true_clss_def_iff_negation_in_model
    apply (subst (2) append_take_drop_id[symmetric, of _ 2])
    unfolding mset_append watched_by_app_def access_lit_in_clauses_def
    by (auto simp: S take_2_if hd_conv_nth split: if_splits)
  show ?thesis
    using consistent_CNot_not_tautology[OF cons Not] .
qed

lemma
  find_unwatched_get_clause_neq_L:
    \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<noteq> L\<close> (is ?neq)
  if
    find_unw: \<open>unit_prop_body_wl_D_find_unwatched_inv (Some xj) (watched_by S L ! C) S\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof (rule ccontr)
  have is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym: \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm A) \<longleftrightarrow> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l = atms_of_mm A\<close> for A
    unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def by metis
  assume eq[simplified, simp]: \<open>\<not> ?neq\<close>
  let ?C = \<open>get_clauses_wl S ! watched_by_app S L C\<close>
  let ?L = \<open>get_clauses_wl S ! watched_by_app S L C ! xj\<close>
  have corr: \<open>correct_watching S\<close> and
    alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of (Some L) (st_l_of_wl (Some (L, C)) S)))\<close>
    using inv unfolding unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
    unfolding correct_watching.simps twl_struct_invs_def  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
  moreover have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>watched_by_app S L C > 0\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  ultimately have in_watched: \<open>watched_by_app S L C \<in># mset (watched_by S L)\<close>
    using inv by (auto simp: watched_by_app_def dest: unit_prop_body_wl_D_invD)

  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover have \<open>L \<in> snd ` D\<^sub>0\<close>
    using inv by (auto intro: unit_prop_body_wl_D_invD)
  ultimately have \<open>L \<in># all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)) + get_unit_init_clss S)\<close>
    using alien
    by (cases S)
        (auto 5 5 simp: get_unit_init_clss_def clauses_def mset_take_mset_drop_mset drop_Suc
        mset_take_mset_drop_mset' cdcl\<^sub>W_restart_mset.no_strange_atm_def
        is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def_sym in_all_lits_of_mm_ain_atms_of_iff in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        dest: in_atms_of_mset_takeD)
    then have H: \<open>mset (watched_by S L) =
      mset_set {x. Suc 0 \<le> x \<and> x < length (get_clauses_wl S) \<and> L \<in> set (watched_l (get_clauses_wl S ! x))}\<close>
      using corr by (cases S)
          (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
          get_unit_init_clss_def)
  have L_in_watched: \<open>L \<in> set (watched_l ?C)\<close>
    using in_watched unfolding H
    by (cases S)
        (auto simp: correct_watching.simps watched_by_app_def clause_to_update_def
        get_unit_init_clss_def)
  have \<open>xj \<ge> 2\<close> and \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
    using find_unw unfolding unit_prop_body_wl_D_find_unwatched_inv_def unit_prop_body_wl_find_unwatched_inv_def
    by (cases S; auto simp: watched_by_app_def)+

  then have L_in_unwatched: \<open>L \<in> set (unwatched_l ?C)\<close>
    by (auto simp: in_set_drop_conv_nth intro!: exI[of _ xj])
  have \<open>distinct_mset_set (mset ` set (tl (get_clauses_wl S)))\<close>
    apply (subst append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
    using dist unfolding  cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def set_append
    by (cases S)
        (auto simp: mset_take_mset_drop_mset image_Un drop_Suc)
  then have dist_C: \<open>distinct ?C\<close>
    using inv by (auto simp: mset_take_mset_drop_mset intro: unit_prop_body_wl_D_invD)
  then show False
    using L_in_watched L_in_unwatched by (cases ?C; cases \<open>tl ?C\<close>; cases \<open>tl (tl ?C)\<close>) auto
qed

lemma update_clause_wl_code_update_clause_wl[sepref_fr_rules]:
  \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [\<lambda>(((((L, C), w), i), f), S).
      unit_prop_body_wl_D_inv S w L \<and>
      unit_prop_body_wl_D_find_unwatched_inv (Some f) C S \<and>
      C = watched_by S L ! w \<and>
      i = (if get_clauses_wl S ! C ! 0 = L then 0 else 1)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>
       nat_assn *assn twl_st_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>(uncurry5 update_clause_wl_code, uncurry5 update_clause_wl) \<in>
    [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((((L, C), w), i), f), S). get_clauses_wl S ! C ! f \<noteq> L)
       (\<lambda>_ (((((L, C), w), i), f), S).
           C < length (get_clauses_wl_heur S) \<and>
           f < length (get_clauses_wl_heur S ! C) \<and>
           i < length (get_clauses_wl_heur S ! C) \<and>
           nat_of_lit L < length (get_watched_wl_heur S) \<and>
           nat_of_lit (get_clauses_wl_heur S ! C ! f)
           < length (get_watched_wl_heur S) \<and>
           w < length (get_watched_wl_heur S ! nat_of_lit L)) (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a
        twl_st_heur_assn\<^sup>d)
      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow>
    hr_comp (nat_assn *assn twl_st_heur_assn) (nat_rel \<times>\<^sub>f twl_st_heur)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF update_clause_wl_code update_clause_wl_heur_update_clause_wl]
    .
  have [dest]: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
    if \<open>unit_prop_body_wl_D_inv S w L\<close>
    for S w L
  proof -
    have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
      using that unfolding twl_st_heur_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def by fast
    then  have \<open> set_mset (all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))) \<subseteq>
       set_mset \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
      apply (subst append_take_drop_id[symmetric, of _ \<open>get_learned_wl S\<close>])
      unfolding mset_append all_lits_of_mm_union
      apply (cases S)
      by (auto simp:  mset_take_mset_drop_mset' literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def clauses_def
           drop_Suc all_lits_of_mm_union is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    then show ?thesis
      unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def by blast
  qed
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    unfolding comp_PRE_def
    apply (cases x)
    apply (clarify)
    apply (intro conjI impI allI)
    subgoal for L C w i f M N U D NP UP Q W
      using that find_unwatched_get_clause_neq_L[of f \<open>(M, N, U, D, NP, UP, Q, W)\<close> L w]
      by (auto simp add: watched_by_app_def)
    subgoal for L C w i f M N U D NP UP Q W y
      apply (subgoal_tac \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl N))\<close>)
      subgoal
        using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>tl N\<close> \<open>(W L ! w - 1)\<close> f]
        using that unfolding comp_PRE_def twl_st_heur_def  map_fun_rel_def unit_prop_body_wl_D_find_unwatched_inv_def
        unit_prop_body_wl_find_unwatched_inv_def unit_prop_body_wl_D_inv_def unit_prop_body_wl_inv_def
        unit_propagation_inner_loop_body_l_inv_def
        by (auto dest: simp: nth_tl )[]
      subgoal
        using that by auto
      done
    done
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition propgate_lit_wl_heur :: \<open>nat literal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>propgate_lit_wl_heur = (\<lambda>L' C i (M, N, U, D, Q, W).
      let N' = list_update N C (swap (N!C) 0 (fast_minus 1 i)) in
      (Propagated L' C # M, N', U, D, add_mset (-L') Q, W))\<close>

lemma (in -) safe_minus_nat_assn:
  \<open>(uncurry (return oo fast_minus), uncurry (RETURN oo fast_minus)) \<in>
     [\<lambda>(m, n). m \<ge> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  by sepref_to_hoare
   (sep_auto simp: uint32_nat_rel_def br_def nat_of_uint32_le_minus
      nat_of_uint32_notle_minus nat_of_uint32_le_iff)

lemma propgate_lit_wl_heur_propgate_lit_wl:
  \<open>(uncurry3 (RETURN oooo propgate_lit_wl_heur), uncurry3 (RETURN oooo propgate_lit_wl)) \<in>
  [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None]\<^sub>f
  Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def propgate_lit_wl_heur_def propgate_lit_wl_def
      vmtf_consD)

sepref_thm propgate_lit_wl_code
  is \<open>uncurry3 (RETURN oooo (PR_CONST propgate_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and> 
       1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and>
       C < length (get_clauses_wl_heur S)]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  unfolding PR_CONST_def propgate_lit_wl_heur_def twl_st_heur_assn_def
    cons_trail_Propagated_def[symmetric]
  supply [[goals_limit=1]]length_rll_def[simp] length_ll_def[simp] safe_minus_nat_assn[sepref_fr_rules] 
  unfolding update_clause_wl_heur_def twl_st_heur_assn_def Array_List_Array.swap_ll_def[symmetric]
  by sepref


concrete_definition (in -) propgate_lit_wl_code
  uses isasat_input_bounded_nempty.propgate_lit_wl_code.refine_raw
  is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propgate_lit_wl_code_def

lemmas propgate_lit_wl_code[sepref_fr_rules] =
  propgate_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma propgate_lit_wl_code_propgate_lit_wl[sepref_fr_rules]:
  \<open>(uncurry3 propgate_lit_wl_code, uncurry3 (RETURN oooo propgate_lit_wl)) \<in>
    [\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> L \<in> snd ` D\<^sub>0 \<and> get_conflict_wl S = None \<and> 
          1 - i < length (get_clauses_wl S ! C) \<and> i \<le> 1 \<and> C < length (get_clauses_wl S)]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(((L, C), i), S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None)
       (\<lambda>_ (((L, C), i), S). undefined_lit (get_trail_wl_heur S) L \<and> L \<in> snd ` D\<^sub>0 \<and>
          1 - i < length (get_clauses_wl_heur S ! C) \<and> i \<le> 1 \<and> C < length (get_clauses_wl_heur S))
       (\<lambda>_. True)]\<^sub>a hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d)
                      (Id \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f twl_st_heur) \<rightarrow> hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propgate_lit_wl_code[unfolded PR_CONST_def]
       propgate_lit_wl_heur_propgate_lit_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma undefined_lit_polarity_st_iff:
   \<open>undefined_lit (get_trail_wl S) L \<longleftrightarrow> polarity_st S L \<noteq> Some True \<and> polarity_st S L \<noteq> Some False\<close>
  by (auto simp: polarity_st_def polarity_def)

lemma find_unwatched_le_length:
  \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close>
  for S L C xj
  using that unfolding find_unwatched_wl_st_def find_unwatched_l_def
  by (cases S) auto

lemma find_unwatched_in_D\<^sub>0: \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in> snd ` D\<^sub>0\<close>
  if
    find_unw: \<open>RETURN (Some xj) \<le> find_unwatched_wl_st S (watched_by_app S L C)\<close> and
    inv: \<open>unit_prop_body_wl_D_inv S C L\<close>
  for S C xj L
proof -
  have \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using inv by (blast intro: unit_prop_body_wl_D_invD)
  moreover {
    have xj: \<open>xj < length (get_clauses_wl S ! watched_by_app S L C)\<close>
      using find_unw by (cases S) (auto simp: find_unwatched_wl_st_def find_unwatched_l_def)
    have \<open>watched_by_app S L C < length (get_clauses_wl S)\<close> \<open>watched_by_app S L C > 0\<close>
      using inv by (blast intro: unit_prop_body_wl_D_invD)+
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (mset `# mset (tl (get_clauses_wl S)))\<close>
      using xj
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset
          in_all_lits_of_mm_ain_atms_of_iff atms_of_ms_def nth_in_set_tl
          intro!: bexI[of _ \<open>get_clauses_wl S ! watched_by_app S L C\<close>])
    then have \<open>get_clauses_wl S ! watched_by_app S L C ! xj \<in>#
      all_lits_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))\<close>
      apply (subst (asm)(3) append_take_drop_id[of \<open>get_learned_wl S\<close>, symmetric])
      unfolding mset_append
      by (cases S)
          (auto simp: clauses_def watched_by_app_def mset_take_mset_drop_mset'
          all_lits_of_mm_union drop_Suc) }
  ultimately show ?thesis
    by (auto simp: image_image is_\<L>\<^sub>a\<^sub>l\<^sub>l_def)
qed

end

text \<open>Find a less hack-like solution\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>

context isasat_input_bounded_nempty
begin

sepref_thm unit_propagation_inner_loop_body_wl_D
  is \<open>uncurry2 ((PR_CONST unit_propagation_inner_loop_body_wl_D) :: nat literal \<Rightarrow> nat \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  supply
    if_splits[split] unit_prop_body_wl_D_invD[intro,dest]
    watched_by_app_def[symmetric,simp]
    access_lit_in_clauses_def[simp] unit_prop_body_wl_D_invD'[intro]
    length_rll_def[simp] find_unwatched_not_tauto[dest]
  supply undefined_lit_polarity_st_iff[iff]
  unfolding unit_propagation_inner_loop_body_wl_D_def length_rll_def[symmetric] PR_CONST_def
  unfolding watched_by_app_def[symmetric] access_lit_in_clauses_def[symmetric]
    find_unwatched_l_find_unwatched_wl_s
  unfolding nth_rll_def[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
  find_unwatched_wl_st_heur_def[symmetric] polarity_st_def[symmetric]
  set_conflict_wl'_alt_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_body_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_body_wl_D.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_body_wl_D_code_def

sepref_register unit_propagation_inner_loop_body_wl_D

lemmas unit_propagation_inner_loop_body_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_body_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) length_ll_fs :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs = (\<lambda>(_, _, _, _, _, _, _, W) L. length (W L))\<close>

definition (in -) length_ll_fs_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>length_ll_fs_heur = (\<lambda>(M, N, U, D, Q, W, _) L. length (W ! nat_of_lit L))\<close>

lemma length_ll_fs_heur_length_ll_fs:
    \<open>(uncurry (RETURN oo length_ll_fs_heur), uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>f twl_st_heur \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: length_ll_fs_def length_ll_fs_heur_def twl_st_heur_def map_fun_rel_def)

lemma (in -) get_watched_wl_heur_def: \<open>get_watched_wl_heur = (\<lambda>(M, N, U, D, Q, W, _). W)\<close>
  by (intro ext, rename_tac x, case_tac x) (auto intro!: ext)

sepref_thm length_ll_fs_heur_code
  is \<open>uncurry (RETURN oo length_ll_fs_heur)\<close>
  :: \<open>[\<lambda>(S, L). nat_of_lit L < length (get_watched_wl_heur S)]\<^sub>a twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding length_ll_fs_heur_def get_watched_wl_heur_def twl_st_heur_assn_def length_ll_def[symmetric]
  supply [[goals_limit=1]]
  by sepref

concrete_definition (in -) length_ll_fs_heur_code
   uses isasat_input_bounded_nempty.length_ll_fs_heur_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) length_ll_fs_heur_code_def

lemmas length_ll_fs_heur_code_refine[sepref_fr_rules] =
   length_ll_fs_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma length_ll_fs_heur_code_length_ll_fs[sepref_fr_rules]:
  \<open>(uncurry length_ll_fs_heur_code, uncurry (RETURN oo length_ll_fs)) \<in>
    [\<lambda>(S, L). L \<in> snd ` D\<^sub>0]\<^sub>a
     twl_st_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
thm hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
  have H: \<open>?fun \<in> [comp_PRE (twl_st_heur \<times>\<^sub>f Id) (\<lambda>(S, L). L \<in> snd ` D\<^sub>0)
    (\<lambda>_ (S, L). nat_of_lit L < length (get_watched_wl_heur S))
    (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                   (twl_st_heur \<times>\<^sub>f Id) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF length_ll_fs_heur_code_refine length_ll_fs_heur_length_ll_fs]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def
    by (auto simp: image_image map_fun_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma length_ll_fs_alt_def: \<open>length_ll_fs S L = length_ll_f (watched_by S) L\<close>
  by (cases S) (auto simp: length_ll_fs_def length_ll_f_def)

sepref_register unit_propagation_inner_loop_wl_loop_D

sepref_thm unit_propagation_inner_loop_wl_loop_D
  is \<open>uncurry ((PR_CONST unit_propagation_inner_loop_wl_loop_D) :: nat literal \<Rightarrow>
           nat twl_st_wl \<Rightarrow> (nat \<times> nat twl_st_wl) nres)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn *assn twl_st_assn\<close>
  unfolding unit_propagation_inner_loop_wl_loop_D_def PR_CONST_def
  unfolding watched_by_nth_watched_app watched_app_def[symmetric]
    length_ll_f_def[symmetric] length_ll_fs_alt_def[symmetric]
  unfolding nth_ll_def[symmetric]
  unfolding swap_ll_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    is_None_def[symmetric] get_conflict_wl_is_None length_ll_fs_def[symmetric]
  supply [[goals_limit=1]]
  by sepref


concrete_definition (in -) unit_propagation_inner_loop_wl_loop_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_loop_D.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_loop_D_code_def

lemmas unit_propagation_inner_loop_wl_loop_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_loop_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

paragraph \<open>Unit propagation, inner loop\<close>

sepref_register unit_propagation_inner_loop_wl_D
sepref_thm unit_propagation_inner_loop_wl_D
  is \<open>uncurry (PR_CONST unit_propagation_inner_loop_wl_D)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  unfolding PR_CONST_def unit_propagation_inner_loop_wl_D_def
  by sepref

concrete_definition (in -) unit_propagation_inner_loop_wl_D_code
   uses isasat_input_bounded_nempty.unit_propagation_inner_loop_wl_D.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_inner_loop_wl_D_code_def

lemmas unit_propagation_inner_loop_wl_D_code_refine[sepref_fr_rules] =
   unit_propagation_inner_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


paragraph \<open>Unit propagation, outer loop\<close>

type_synonym (in -) twl_st_wl_heur_W_list =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat cconflict \<times> nat literal list \<times> nat list list \<times> vmtf_remove_int \<times> bool list \<times> nat\<close>

definition (in -) select_and_remove_from_literals_to_update_wl_heur
  :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wl_heur_W_list \<times> _\<close> where
  \<open>select_and_remove_from_literals_to_update_wl_heur =
     (\<lambda>(M, N, U, D, Q, W, other).  ((M, N, U, D, tl Q, W, other), hd Q))\<close>

definition twl_st_wl_heur_W_list_rel :: \<open>(twl_st_wl_heur_W_list \<times> twl_st_wl_heur) set\<close> where
  \<open>twl_st_wl_heur_W_list_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     (Id :: (nat cconflict \<times> _)set) \<times>\<^sub>r
     (list_mset_rel :: (nat literal list \<times> nat lit_queue_wl) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     nat_rel\<close>

definition twl_st_heur_W_list_assn :: \<open>twl_st_wl_heur_W_list \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_heur_W_list_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  (list_assn unat_lit_assn) *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc *assn uint32_nat_assn
  )\<close>

lemma twl_st_wl_heur_W_list_rel_twl_st_rel: \<open>twl_st_wl_heur_W_list_rel O twl_st_heur =
   {((M', N', U', D', Q', W', vm, \<phi>, clvls), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     D = D' \<and>
     (Q', Q) \<in> list_mset_rel \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M \<and> clvls \<in> counts_maximum_level M D}\<close>
  unfolding twl_st_heur_def twl_st_wl_heur_W_list_rel_def
  by force

lemma twl_st_heur_assn_W_list:
  \<open>twl_st_heur_assn = hr_comp twl_st_heur_W_list_assn twl_st_wl_heur_W_list_rel\<close>
  unfolding twl_st_heur_assn_def twl_st_heur_W_list_assn_def twl_st_wl_heur_W_list_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn)

lemma twl_st_assn_W_list:
  \<open>twl_st_assn = hr_comp twl_st_heur_W_list_assn (twl_st_wl_heur_W_list_rel O twl_st_heur)\<close>
  apply (subst hr_comp_assoc[symmetric])
  apply (subst twl_st_heur_assn_W_list[symmetric])
  unfolding twl_st_assn_def ..


definition get_literals_to_update_wl where
   \<open>get_literals_to_update_wl = (\<lambda>(M, N, U, D, NP, UP, Q, W). Q)\<close>

definition get_literals_to_update_wl_heur_W_list where
   \<open>get_literals_to_update_wl_heur_W_list = (\<lambda>(M, N, U, D, Q, W, _). Q)\<close>

definition literals_to_update_wl_empty_heur :: \<open>twl_st_wl_heur_W_list \<Rightarrow> bool\<close>  where
  \<open>literals_to_update_wl_empty_heur = (\<lambda>(M, N, U, D, Q, W, oth). Q = [])\<close>

lemma select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl:
  \<open>(RETURN o select_and_remove_from_literals_to_update_wl_heur,
    select_and_remove_from_literals_to_update_wl) \<in>
    [\<lambda>S. \<not>literals_to_update_wl_empty S]\<^sub>f
      (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
       \<langle>(twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>r Id\<rangle>nres_rel\<close>
  unfolding select_and_remove_from_literals_to_update_wl_heur_def
  select_and_remove_from_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  twl_st_wl_heur_W_list_rel_twl_st_rel get_literals_to_update_wl_def
  literals_to_update_wl_empty_def
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y,
      case_tac \<open>get_literals_to_update_wl_heur_W_list y\<close>)
  unfolding get_literals_to_update_wl_def get_literals_to_update_wl_heur_W_list_def
  by (auto intro!: RETURN_SPEC_refine simp: nempty_list_mset_rel_iff)

sepref_thm select_and_remove_from_literals_to_update_wl_code
  is \<open>RETURN o select_and_remove_from_literals_to_update_wl_heur\<close>
  :: \<open>[\<lambda>S. \<not>literals_to_update_wl_empty_heur S]\<^sub>a twl_st_heur_W_list_assn\<^sup>d \<rightarrow> twl_st_heur_W_list_assn *assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref


concrete_definition (in -) select_and_remove_from_literals_to_update_wl_code
   uses isasat_input_bounded_nempty.select_and_remove_from_literals_to_update_wl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) select_and_remove_from_literals_to_update_wl_code_def

lemmas select_and_remove_from_literals_to_update_wl_code_refine[sepref_fr_rules] =
   select_and_remove_from_literals_to_update_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem select_and_remove_from_literals_to_update_wl_code_select_and_remove_from_literals_to_update_wl
  [sepref_fr_rules]:
  \<open>(select_and_remove_from_literals_to_update_wl_code,
     select_and_remove_from_literals_to_update_wl)
    \<in> [\<lambda>S. \<not> literals_to_update_wl_empty S]\<^sub>a twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *assn
          unat_lit_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun
    \<in> [comp_PRE (twl_st_wl_heur_W_list_rel O twl_st_heur)
         (\<lambda>S. \<not> literals_to_update_wl_empty S)
         (\<lambda>_ S. \<not> literals_to_update_wl_empty_heur S)
         (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_heur_W_list_assn\<^sup>d) (twl_st_wl_heur_W_list_rel O twl_st_heur) \<rightarrow>
      hr_comp (twl_st_heur_W_list_assn *assn unat_lit_assn)
           ((twl_st_wl_heur_W_list_rel O twl_st_heur) \<times>\<^sub>f Id)\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF select_and_remove_from_literals_to_update_wl_code_refine
      select_and_remove_from_literals_to_update_wl_heur_select_and_remove_from_literals_to_update_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm literals_to_update_wl_empty_heur_code
  is \<open>RETURN o literals_to_update_wl_empty_heur\<close>
  :: \<open>twl_st_heur_W_list_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding select_and_remove_from_literals_to_update_wl_heur_def twl_st_heur_W_list_assn_def
    literals_to_update_wl_empty_heur_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) literals_to_update_wl_empty_heur_code
   uses isasat_input_bounded_nempty.literals_to_update_wl_empty_heur_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) literals_to_update_wl_empty_heur_code_def

lemmas literals_to_update_wl_empty_heur_code_refine[sepref_fr_rules] =
   literals_to_update_wl_empty_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma literals_to_update_wl_empty_heur_literals_to_update_wl_empty:
  \<open>(RETURN o literals_to_update_wl_empty_heur, RETURN o literals_to_update_wl_empty) \<in>
    twl_st_wl_heur_W_list_rel O twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  unfolding literals_to_update_wl_empty_heur_def literals_to_update_wl_empty_def
    twl_st_wl_heur_W_list_rel_twl_st_rel
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: Nil_list_mset_rel_iff empty_list_mset_rel_iff)

lemma literals_to_update_wl_empty_heur_code_literals_to_update_wl_empty[sepref_fr_rules]:
  \<open>(literals_to_update_wl_empty_heur_code, RETURN \<circ> literals_to_update_wl_empty)
     \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using literals_to_update_wl_empty_heur_code_refine[FCOMP literals_to_update_wl_empty_heur_literals_to_update_wl_empty]
  unfolding twl_st_assn_W_list[symmetric]
  .

sepref_register unit_propagation_outer_loop_wl_D
sepref_thm unit_propagation_outer_loop_wl_D
  is \<open>((PR_CONST unit_propagation_outer_loop_wl_D) :: nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres)\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding unit_propagation_outer_loop_wl_D_def
    literals_to_update_wl_literals_to_update_wl_empty
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) unit_propagation_outer_loop_wl_D
   uses isasat_input_bounded_nempty.unit_propagation_outer_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) unit_propagation_outer_loop_wl_D_def

lemmas unit_propagation_outer_loop_wl_D[sepref_fr_rules] =
   unit_propagation_outer_loop_wl_D.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

paragraph \<open>Skip and resolve\<close>

definition get_conflict_wll_is_Nil_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool nres\<close> where
  \<open>get_conflict_wll_is_Nil_heur = (\<lambda>(M, N, U, D, Q, W, _).
   do {
     if is_None D
     then RETURN False
     else do{ ASSERT(D \<noteq> None); RETURN (Multiset.is_empty (the D))}
   })\<close>

sepref_thm get_conflict_wll_is_Nil_code
  is \<open>(PR_CONST get_conflict_wll_is_Nil_heur)\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  apply (subst PR_CONST_def)
  unfolding get_conflict_wll_is_Nil_heur_def twl_st_heur_assn_def
    literals_to_update_wl_literals_to_update_wl_empty
    short_circuit_conv the_is_empty_def[symmetric]
  by sepref

concrete_definition (in -) get_conflict_wll_is_Nil_code
   uses isasat_input_bounded_nempty.get_conflict_wll_is_Nil_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) get_conflict_wll_is_Nil_code_def

lemmas get_conflict_wll_is_Nil_code[sepref_fr_rules] =
  get_conflict_wll_is_Nil_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil:
  \<open>(PR_CONST get_conflict_wll_is_Nil_heur, get_conflict_wll_is_Nil) \<in> twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: get_conflict_wll_is_Nil_heur_def get_conflict_wll_is_Nil_def twl_st_heur_def
      split: option.splits)

lemma get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, get_conflict_wll_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code[FCOMP get_conflict_wll_is_Nil_heur_get_conflict_wll_is_Nil]
  unfolding twl_st_assn_def[symmetric] .

lemma get_conflict_wll_is_Nil_code_get_conflict_wl_is_Nil[sepref_fr_rules]:
  \<open>(get_conflict_wll_is_Nil_code, RETURN \<circ> get_conflict_wl_is_Nil) \<in> twl_st_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using get_conflict_wll_is_Nil_code_get_conflict_wll_is_Nil[FCOMP
   get_conflict_wll_is_Nil_get_conflict_wl_is_Nil[unfolded PR_CONST_def]]
  by auto

lemma in_literals_are_in_\<L>\<^sub>i\<^sub>n_in_D\<^sub>0:
  assumes \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D\<close> and \<open>L \<in># D\<close>
  shows \<open>L \<in> snd ` D\<^sub>0\<close>
  using assms by (cases L) (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_def all_lits_of_m_def)


paragraph \<open>Level of a literal\<close>

lemma get_maximum_level_remove_count_max_lvls:
  assumes L: \<open>L = -lit_of (hd M)\<close> and LD: \<open>L \<in># D\<close> and M_nempty: \<open>M \<noteq> []\<close>
  shows \<open>get_maximum_level_remove M D L = count_decided M \<longleftrightarrow>
       (count_decided M = 0 \<or> card_max_lvl M D > 1)\<close>
  (is \<open>?max \<longleftrightarrow> ?count\<close>)
proof
  assume H: ?max
  let ?D = \<open>remove1_mset L D\<close>
  have [simp]: \<open>get_level M L = count_decided M\<close>
    using M_nempty L by (cases M) auto
  define MD where \<open>MD \<equiv> {#L \<in># D. get_level M L = count_decided M#}\<close>
  show ?count
  proof (cases \<open>?D = {#}\<close>)
    case True
    then show ?thesis
      using LD H by (auto dest!: multi_member_split simp: get_maximum_level_remove_def)
  next
    case False
    then obtain L' where
      \<open>get_level M L' = get_maximum_level_remove M D L\<close> and L'_D: \<open>L' \<in># ?D\<close>
      using get_maximum_level_exists_lit_of_max_level[of \<open>remove1_mset L D\<close>]
      unfolding get_maximum_level_remove_def by blast
    then have \<open>L' \<in># {#L \<in># D. get_level M L = count_decided M#}\<close>
      using H by (auto dest: in_diffD simp: get_maximum_level_remove_def)
    moreover have \<open>L \<in># {#L \<in># D. get_level M L = count_decided M#}\<close>
      using LD by auto
    ultimately have \<open>{#L, L'#} \<subseteq># MD\<close>
      using L'_D LD by (cases \<open>L = L'\<close>)
        (auto dest!: multi_member_split simp: MD_def add_mset_eq_add_mset)
    from size_mset_mono[OF this] show ?thesis
      unfolding card_max_lvl_def H MD_def[symmetric]
      by auto
  qed
next
  let ?D = \<open>remove1_mset L D\<close>
  have [simp]: \<open>get_level M L = count_decided M\<close>
    using M_nempty L by (cases M) auto
  define MD where \<open>MD \<equiv> {#L \<in># D. get_level M L = count_decided M#}\<close>
  have L_MD: \<open>L \<in># MD\<close>
    using LD unfolding MD_def by auto
  assume ?count
  then consider
    (lev_0) \<open>count_decided M = 0\<close> |
    (count) \<open>card_max_lvl M D > 1\<close>
    by (cases \<open>D \<noteq> {#L#}\<close>) auto
  then show ?max
  proof cases
    case lev_0
    then show ?thesis
      using count_decided_ge_get_maximum_level[of M ?D]
      by (auto simp: get_maximum_level_remove_def)
  next
    case count
    then obtain L' where
      \<open>L' \<in># MD\<close> and
      LL': \<open>{#L, L'#} \<subseteq># MD\<close>
      using L_MD
      unfolding get_maximum_level_remove_def card_max_lvl_def MD_def[symmetric]
      by (force simp: nonempty_has_size[symmetric]
          dest!: multi_member_split multi_nonempty_split)
    then have \<open>get_level M L' = count_decided M\<close>
      unfolding MD_def by auto
    moreover have \<open>L' \<in># remove1_mset L D\<close>
    proof -
      have "{#L, L'#} \<subseteq># D"
        using LL' unfolding MD_def
        by (meson multiset_filter_subset subset_mset.dual_order.trans)
      then show ?thesis
        by (metis (no_types) LD insert_DiffM mset_subset_eq_add_mset_cancel single_subset_iff)
    qed
    ultimately have \<open>get_maximum_level M (remove1_mset L D) \<ge> count_decided M\<close>
      using get_maximum_level_ge_get_level[of L' ?D M]
      by simp
    then show ?thesis
      using count_decided_ge_get_maximum_level[of M ?D]
      by (auto simp: get_maximum_level_remove_def)
  qed
qed


definition count_decided_st where
  \<open>count_decided_st = (\<lambda>(M, _). count_decided M)\<close>

sepref_thm count_decided_st_code
  is \<open>RETURN o count_decided_st\<close>
  :: \<open>twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=2]]
  unfolding count_decided_st_def twl_st_heur_assn_def
  by sepref

concrete_definition (in -) count_decided_st_code
  uses isasat_input_bounded_nempty.count_decided_st_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) count_decided_st_code_def

lemmas count_decided_st_code_refine[sepref_fr_rules] =
   count_decided_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

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

definition maximum_level_removed_eq_count_dec where
  \<open>maximum_level_removed_eq_count_dec L S \<longleftrightarrow>
      get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L =
       count_decided (get_trail_wl S)\<close>

definition maximum_level_removed_eq_count_dec_heur where
  \<open>maximum_level_removed_eq_count_dec_heur L S \<longleftrightarrow>
      count_decided_st S = zero_uint32_nat \<or> get_count_max_lvls_heur S > one_uint32_nat\<close>

lemma maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec:
  \<open>(uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur),
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> []]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur\<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using get_maximum_level_remove_count_max_lvls[of \<open>fst x\<close> \<open>get_trail_wl (snd y)\<close>
      \<open>the (get_conflict_wl (snd y))\<close>]
    by (cases x)
       (auto simp: count_decided_st_def counts_maximum_level_def twl_st_heur_def
     maximum_level_removed_eq_count_dec_heur_def maximum_level_removed_eq_count_dec_def)
  done

definition (in -) get_count_max_lvls_code where
  \<open>get_count_max_lvls_code = (\<lambda>(_, _, _, _, _, _, _, _, clvls). clvls)\<close>

(* TODO Peter: do I really need this elim! & co? *)
lemma get_count_max_lvls_heur_hnr[sepref_fr_rules]:
  \<open>(return o get_count_max_lvls_code, RETURN o get_count_max_lvls_heur) \<in>
     twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  apply sepref_to_hoare
  subgoal for x x'
    apply (cases x; cases x')
    apply (sep_auto simp: twl_st_heur_assn_def get_count_max_lvls_code_def
        elim!: mod_starE)
    apply (case_tac h2)
    apply sep_auto
    done
  done

sepref_thm maximum_level_removed_eq_count_dec_code
  is \<open>uncurry (RETURN oo maximum_level_removed_eq_count_dec_heur)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding maximum_level_removed_eq_count_dec_heur_def
  by sepref

concrete_definition (in -) maximum_level_removed_eq_count_dec_code
   uses isasat_input_bounded_nempty.maximum_level_removed_eq_count_dec_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) maximum_level_removed_eq_count_dec_code_def

lemmas maximum_level_removed_eq_count_dec_code_hnr[sepref_fr_rules] =
   maximum_level_removed_eq_count_dec_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma maximum_level_removed_eq_count_dec_hnr[sepref_fr_rules]:
  \<open>(uncurry maximum_level_removed_eq_count_dec_code,
      uncurry (RETURN oo maximum_level_removed_eq_count_dec)) \<in>
   [\<lambda>(L, S). L = -lit_of (hd (get_trail_wl S)) \<and> L \<in># the (get_conflict_wl S) \<and>
      get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> []]\<^sub>a
    unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f twl_st_heur)
     (\<lambda>(L, S).
         L = -lit_of (hd (get_trail_wl S)) \<and>
         L \<in># the (get_conflict_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [])
     (\<lambda>_ _. True)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k)
                    (Id \<times>\<^sub>f
                     twl_st_heur) \<rightarrow> hr_comp bool_assn bool_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF maximum_level_removed_eq_count_dec_code_hnr[unfolded PR_CONST_def]
      maximum_level_removed_eq_count_dec_heur_maximum_level_removed_eq_count_dec]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric] conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition is_decided_hd_trail_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>is_decided_hd_trail_wl_heur = (\<lambda>(M, _). is_decided (hd M))\<close>

lemma is_decided_hd_trail_wl_heur_is_decided_hd_trail_wl:
  \<open>(RETURN o is_decided_hd_trail_wl_heur, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: is_decided_hd_trail_wl_heur_def is_decided_hd_trail_wl_def twl_st_heur_def)

lemma get_trail_wl_heur_def: \<open>get_trail_wl_heur = (\<lambda>(M, S). M)\<close>
  by (intro ext, rename_tac S, case_tac S) auto

definition (in -) hd_trail_code :: \<open>trail_pol_assn \<Rightarrow> uint32 \<times> nat option\<close> where
  \<open>hd_trail_code = (\<lambda>(M, _). hd M)\<close>

lemma hd_trail_code_hd[sepref_fr_rules]:
  \<open>(return o hd_trail_code, RETURN o op_list_hd) \<in> [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>k \<rightarrow> pair_nat_ann_lit_assn\<close>
  unfolding hd_trail_code_def op_list_hd_def
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>fst (xi)\<close>)
  apply (sep_auto simp:  trail_pol_def hr_comp_def)+
  done

sepref_thm is_decided_hd_trail_wl_code
  is \<open>RETURN o is_decided_hd_trail_wl_heur\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur S \<noteq> []]\<^sub>a twl_st_heur_assn\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_decided_hd_trail_wl_heur_def twl_st_heur_assn_def
    supply get_trail_wl_heur_def[simp]
  by sepref


concrete_definition (in -) is_decided_hd_trail_wl_code
   uses isasat_input_bounded_nempty.is_decided_hd_trail_wl_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms is_decided_hd_trail_wl_code_def

lemmas is_decided_hd_trail_wl_code[sepref_fr_rules] =
   is_decided_hd_trail_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma is_decided_hd_trail_wl_code_is_decided_hd_trail_wl[sepref_fr_rules]:
  \<open>(is_decided_hd_trail_wl_code, RETURN o is_decided_hd_trail_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a twl_st_assn\<^sup>k \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur (\<lambda>S. get_trail_wl S \<noteq> []) (\<lambda>_ S. get_trail_wl_heur S \<noteq> [])
        (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>k)
                     twl_st_heur \<rightarrow> hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_decided_hd_trail_wl_code
      is_decided_hd_trail_wl_heur_is_decided_hd_trail_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def literals_to_update_wl_empty_heur_def
      literals_to_update_wl_empty_def twl_st_wl_heur_W_list_rel_def
    by (auto simp: image_image map_fun_rel_def Nil_list_mset_rel_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_W_list[symmetric] conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma get_trail_twl_st_of_wl_get_trail_wl_empty_iff:
  \<open>get_trail (twl_st_of None (st_l_of_wl None S)) = [] \<longleftrightarrow> get_trail_wl S = []\<close>
  by (cases S) auto

definition (in -) is_in_conflict :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> bool\<close> where
  \<open>is_in_conflict L C \<longleftrightarrow> L \<in># the C\<close>

definition (in -) is_in_lookup_option_conflict :: \<open>nat literal \<Rightarrow> (bool \<times> nat \<times> bool option list) \<Rightarrow> bool\<close> where
  \<open>is_in_lookup_option_conflict = (\<lambda>L (_, _, xs). xs ! atm_of L = Some (is_pos L))\<close>

lemma is_in_lookup_option_conflict_is_in_conflict:
  \<open>(uncurry (RETURN oo is_in_lookup_option_conflict), uncurry (RETURN oo is_in_conflict)) \<in>
     [\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>r option_conflict_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro nres_relI frefI)
  subgoal for Lxs LC
    using conflict_rel_atm_in_iff[of _ \<open>snd (snd (snd Lxs))\<close>]
    apply (cases Lxs)
    by (auto simp: is_in_lookup_option_conflict_def is_in_conflict_def option_conflict_rel_def)
  done

sepref_definition (in -) is_in_lookup_option_conflict_code
  is \<open>uncurry (RETURN oo is_in_lookup_option_conflict)\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a
        unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>k \<rightarrow> bool_assn\<close>
  unfolding is_in_lookup_option_conflict_def
  by sepref


lemma is_in_lookup_option_conflict_code_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry is_in_lookup_option_conflict_code,
     uncurry (RETURN oo is_in_conflict)) \<in>
    [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (Id \<times>\<^sub>f option_conflict_rel) (\<lambda>(L, C). C \<noteq> None \<and> L \<in> snd ` D\<^sub>0)
          (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>k) (Id \<times>\<^sub>f option_conflict_rel)
       \<rightarrow>
      hr_comp bool_assn bool_rel\<close>
     (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF is_in_lookup_option_conflict_code.refine is_in_lookup_option_conflict_is_in_conflict]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff conflict_rel_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] conflict_assn_def conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition (in -)literal_is_in_conflict :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict L S \<longleftrightarrow> L \<in># the (get_conflict_wl S)\<close>

definition literal_is_in_conflict_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>literal_is_in_conflict_heur = (\<lambda>L (M, N, U, D, _). L \<in># the D)\<close>

lemma literal_is_in_conflict_heur_literal_is_in_conflict:
  \<open>(uncurry (RETURN oo literal_is_in_conflict_heur), uncurry (RETURN oo literal_is_in_conflict)) \<in>
   Id \<times>\<^sub>r twl_st_heur \<rightarrow>\<^sub>f \<langle>Id\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac x, case_tac y)
  by (auto simp: literal_is_in_conflict_heur_def literal_is_in_conflict_def twl_st_heur_def)

sepref_thm literal_is_in_conflict_heur_code
  is \<open>uncurry (RETURN oo literal_is_in_conflict_heur)\<close>
  :: \<open>[\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and> get_conflict_wl_heur S \<noteq> None]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>k  \<rightarrow> bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding literal_is_in_conflict_heur_def twl_st_heur_assn_def is_in_conflict_def[symmetric]
  PR_CONST_def
  by sepref

concrete_definition (in -) literal_is_in_conflict_heur_code
   uses isasat_input_bounded_nempty.literal_is_in_conflict_heur_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) literal_is_in_conflict_heur_code_def

lemmas literal_is_in_conflict_heur_code_refine[sepref_fr_rules] =
   literal_is_in_conflict_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma literal_is_in_conflict_heur_code_literal_is_in_conflict[sepref_fr_rules]:
  \<open>(uncurry literal_is_in_conflict_heur_code,
     uncurry (RETURN oo literal_is_in_conflict)) \<in>
    [\<lambda>(L, S). L \<in> snd ` D\<^sub>0 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and> get_conflict_wl S \<noteq> None]\<^sub>a
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
    using  hfref_compI_PRE_aux[OF literal_is_in_conflict_heur_code_refine literal_is_in_conflict_heur_literal_is_in_conflict]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition lit_and_ann_of_propagated_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st S = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>

definition lit_and_ann_of_propagated_st_heur :: \<open>twl_st_wl_heur \<Rightarrow> nat literal \<times> nat\<close> where
  \<open>lit_and_ann_of_propagated_st_heur = (\<lambda>(M, _). (lit_of (hd M), mark_of (hd M)))\<close>

lemma mark_of_refine[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. the (snd C)), RETURN o mark_of) \<in> [\<lambda>C. is_proped C]\<^sub>a pair_nat_ann_lit_assn\<^sup>k \<rightarrow> nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x; case_tac xi; case_tac \<open>snd xi\<close>)
  by (sep_auto simp: nat_ann_lit_rel_def)+

sepref_thm lit_and_ann_of_propagated_st_heur_code
  is \<open>RETURN o lit_and_ann_of_propagated_st_heur\<close>
  :: \<open>[\<lambda>S. is_proped (hd (get_trail_wl_heur S)) \<and> get_trail_wl_heur S \<noteq> []]\<^sub>a
       twl_st_heur_assn\<^sup>k \<rightarrow> (unat_lit_assn *assn nat_assn)\<close>
  supply [[goals_limit=1]]
  supply get_trail_wl_heur_def[simp]
  unfolding lit_and_ann_of_propagated_st_heur_def twl_st_heur_assn_def
  by sepref

concrete_definition (in -) lit_and_ann_of_propagated_st_heur_code
   uses isasat_input_bounded_nempty.lit_and_ann_of_propagated_st_heur_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_and_ann_of_propagated_st_heur_code_def

lemmas lit_and_ann_of_propagated_st_heur_code_refine[sepref_fr_rules] =
   lit_and_ann_of_propagated_st_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st:
   \<open>(RETURN o lit_and_ann_of_propagated_st_heur, RETURN o lit_and_ann_of_propagated_st) \<in>
   [\<lambda>S. is_proped (hd (get_trail_wl S))]\<^sub>f twl_st_heur \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y; case_tac x; case_tac y; case_tac \<open>hd (fst x)\<close>)
  by (auto simp: twl_st_heur_def lit_and_ann_of_propagated_st_heur_def lit_and_ann_of_propagated_st_def)

lemma lit_and_ann_of_propagated_st_refine[sepref_fr_rules]:
  \<open>(lit_and_ann_of_propagated_st_heur_code,
     (RETURN o lit_and_ann_of_propagated_st)) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> is_proped (hd (get_trail_wl S))]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn *assn nat_assn \<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur (\<lambda>S. is_proped (hd (get_trail_wl S)))
         (\<lambda>_ S. is_proped (hd (get_trail_wl_heur S)) \<and> get_trail_wl_heur S \<noteq> [])
         (\<lambda>_. True)]\<^sub>a
    hrp_comp (twl_st_heur_assn\<^sup>k) twl_st_heur \<rightarrow>
    hr_comp (unat_lit_assn *assn nat_assn) (Id \<times>\<^sub>f nat_rel)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF lit_and_ann_of_propagated_st_heur_code_refine lit_and_ann_of_propagated_st_heur_lit_and_ann_of_propagated_st]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma skip_and_resolve_hd_in_D\<^sub>0:
  assumes
    L: "(L, a2'a) = lit_and_ann_of_propagated_st a2'" and
    is_proped: "is_proped (hd (get_trail_wl a2'))" and
    struct: "twl_struct_invs (twl_st_of None (st_l_of_wl None a2'))" and
    nempty: "get_trail_wl a2' \<noteq> []" and
    \<L>\<^sub>a\<^sub>l\<^sub>l: "is_\<L>\<^sub>a\<^sub>l\<^sub>l
      (all_lits_of_mm
        (cdcl\<^sub>W_restart_mset.clauses
          (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))))"
   shows "- L \<in> snd ` D\<^sub>0"
proof -
  obtain M' where
    M': \<open>get_trail_wl a2' = Propagated L a2'a # M'\<close>
    using is_proped L nempty by (cases \<open>get_trail_wl a2'\<close>; cases \<open>hd (get_trail_wl a2')\<close>)
      (auto simp: lit_and_ann_of_propagated_st_def)
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of None (st_l_of_wl None a2')))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
    using \<L>\<^sub>a\<^sub>l\<^sub>l M' unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def
    by (cases a2')
     (auto simp: image_image mset_take_mset_drop_mset'
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff clauses_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def)
qed


definition tl_state_wl_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>tl_state_wl_heur = (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>, clvls).
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of (lit_of (hd M))) vmtf, \<phi>, clvls))\<close>

lemma tl_state_wl_heur_alt_def:
    \<open>tl_state_wl_heur = (\<lambda>(M, N, U, D, WS, Q, vmtf, \<phi>, clvls).
      (let L = lit_of (hd M) in
       (tl M, N, U, D, WS, Q, vmtf_unset (atm_of L) vmtf, \<phi>, clvls)))\<close>
  by (auto simp: tl_state_wl_heur_def Let_def)

definition (in isasat_input_ops) tl_trailt_tr :: \<open>trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>tl_trailt_tr = (\<lambda>(M', xs, lvls, k). (tl M', xs[atm_of (lit_of (hd M')) := None], lvls[atm_of (lit_of (hd M')) := 0],
    if is_decided (hd M') then k-1 else k))\<close>

sepref_thm tl_trail_tr_code
  is \<open>RETURN o tl_trailt_tr\<close>
  :: \<open>[\<lambda>(M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs  \<and> atm_of (lit_of (hd M)) < length lvls \<and>
    (is_decided (hd M) \<longrightarrow> k \<ge> 1)]\<^sub>a
        trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  supply if_splits[split] option.splits[split]
  unfolding tl_trailt_tr_def
  apply (rewrite at \<open>_ - 1\<close> fast_minus_def[symmetric])
  supply [[goals_limit = 1]]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_zero[sepref_fr_rules]
  by sepref

concrete_definition (in -) tl_trail_tr_code
  uses isasat_input_bounded_nempty.tl_trail_tr_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_trail_tr_code_def

lemmas tl_trail_tr_coded_refine[sepref_fr_rules] =
   tl_trail_tr_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma tl_trail_tr:
  \<open>((RETURN o tl_trailt_tr), (RETURN o tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
proof -
  show ?thesis
    apply (intro frefI nres_relI, rename_tac x y, case_tac \<open>y\<close>)
    subgoal by fast
    subgoal for M M' L M's
      unfolding trail_pol_def comp_def RETURN_refine_iff trail_pol_def
      apply clarify
      apply (intro conjI; clarify?; (intro conjI)?)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
      subgoal by (auto simp: trail_pol_def polarity_atm_def tl_trailt_tr_def)
      subgoal by (auto simp: polarity_atm_def tl_trailt_tr_def)
      subgoal
        by (cases \<open>lit_of L\<close>)
            (auto simp: polarity_atm_def tl_trailt_tr_def Decided_Propagated_in_iff_in_lits_of_l)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: polarity_atm_def tl_trailt_tr_def
           atm_of_eq_atm_of get_level_cons_if)
      subgoal
        by (auto simp: tl_trailt_tr_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
            dest: no_dup_consistentD vmtf_unset_vmtf_tl)
      subgoal
        by (auto simp: tl_trailt_tr_def)
      done
    done
qed

lemma tl_trail_tr_code_op_list_tl[sepref_fr_rules]:
  \<open>(tl_trail_tr_code, (RETURN o op_list_tl)) \<in>
    [\<lambda>M. M \<noteq> []]\<^sub>a trail_assn\<^sup>d \<rightarrow> trail_assn\<close>
    (is \<open>_ \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have [dest]: \<open>((a, aa, ab, b), x) \<in> trail_pol \<Longrightarrow> x = a\<close> for a aa ab b x
    by (auto simp: trail_pol_def)
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> is_decided (hd x) \<Longrightarrow> Suc 0 \<le> count_decided x\<close> for x
    by (cases x) auto
  have H: \<open>(tl_trail_tr_code, RETURN \<circ> tl)
      \<in> [comp_PRE trail_pol (\<lambda>M. M \<noteq> [])
            (\<lambda>_ (M, xs, lvls, k). M \<noteq> [] \<and> atm_of (lit_of (hd M)) < length xs \<and>
             atm_of (lit_of (hd M)) < length lvls \<and> (is_decided (hd M) \<longrightarrow> 1 \<le> k))
            (\<lambda>_. True)]\<^sub>a
         hrp_comp (trail_pol_assn\<^sup>d) trail_pol \<rightarrow> hr_comp trail_pol_assn trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF tl_trail_tr_code.refine tl_trail_tr, OF isasat_input_bounded_nempty_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def phase_saving_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff vmtf_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre by simp
qed

fun get_vmtf_heur :: \<open>twl_st_wl_heur \<Rightarrow> _\<close> where
  \<open>get_vmtf_heur (M, N, U, D, WS, W, cvmtf, _) = cvmtf\<close>

end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin

lemma literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0:
  assumes
    \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    nil: \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0\<close>
proof -
  have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then show ?thesis
     using nil \<L>\<^sub>a\<^sub>l\<^sub>l by (cases S; cases \<open>get_trail_wl S\<close>)
        (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def
          in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff image_image mset_take_mset_drop_mset' clauses_def
          is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def)
qed

sepref_thm tl_state_wl_heur_code
  is \<open>RETURN o tl_state_wl_heur\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _). M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A)]\<^sub>a
      twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] option.splits[split] if_splits[split]
  option.splits[split]
  supply [[goals_limit=1]] option.splits[split] literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[intro]
  unfolding tl_state_wl_heur_alt_def[abs_def] twl_st_heur_assn_def get_trail_wl_heur_def[simp]
    vmtf_unset_def bind_ref_tag_def[simp]
    short_circuit_conv
  by sepref


concrete_definition (in -) tl_state_wl_heur_code
  uses isasat_input_bounded_nempty.tl_state_wl_heur_code.refine_raw
  is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) tl_state_wl_heur_code_def

lemmas tl_state_wl_heur_code_refine[sepref_fr_rules] =
   tl_state_wl_heur_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO: we need early breaks in skip_and_resolve! *)
lemma card_max_lvl_Cons:
  assumes \<open>no_dup (L # a)\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided L\<close>
  shows \<open>card_max_lvl (L # a) y =
    (if (lit_of L \<in># y \<or> -lit_of L \<in># y) \<and> count_decided a \<noteq> 0 then card_max_lvl a y + 1
    else card_max_lvl a y)\<close>
proof -
  have [simp]: \<open>count_decided a = 0 \<Longrightarrow> get_level a L = 0\<close> for L
    by (simp add: count_decided_0_iff)
  have [simp]: \<open>lit_of L \<notin># A \<Longrightarrow>
         - lit_of L \<notin># A \<Longrightarrow>
          {#La \<in># A. La \<noteq> lit_of L \<and> La \<noteq> - lit_of L \<longrightarrow> get_level a La = b#} =
          {#La \<in># A. get_level a La = b#}\<close> for A b
    apply (rule filter_mset_cong)
     apply (rule refl)
    by auto
  show ?thesis
    using assms by (auto simp: card_max_lvl_def get_level_cons_if tautology_add_mset
        atm_of_eq_atm_of
        dest!: multi_member_split)
qed

lemma card_max_lvl_tl:
  assumes \<open>a \<noteq> []\<close> \<open>distinct_mset y\<close>\<open>\<not>tautology y\<close> \<open>\<not>is_decided (hd a)\<close> \<open>no_dup a\<close>
  shows \<open>card_max_lvl (tl a) y =
      (if (lit_of(hd a) \<in># y \<or> -lit_of(hd a) \<in># y) \<and> count_decided a \<noteq> 0
       then card_max_lvl a y - 1 else card_max_lvl a y)\<close>
  using assms by (cases a) (auto simp: card_max_lvl_Cons)

lemma tl_state_wl_heur_tl_state_wl: \<open>(RETURN o tl_state_wl_heur, RETURN o tl_state_wl) \<in>
  [\<lambda>S. get_trail_wl S \<noteq> [] \<and> lit_of(hd (get_trail_wl S)) \<in> snd ` D\<^sub>0 \<and>
     (lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
     -(lit_of (hd (get_trail_wl S))) \<notin># the (get_conflict_wl S) \<and>
    \<not>tautology (the (get_conflict_wl S)) \<and>
    distinct_mset (the (get_conflict_wl S)) \<and>
    \<not>is_decided (hd (get_trail_wl S))
  ]\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: twl_st_heur_def tl_state_wl_heur_def tl_state_wl_def vmtf_unset_vmtf_tl
    in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def counts_maximum_level_def
    card_max_lvl_tl
    dest: no_dup_tlD)


lemma twl_struct_invs_confl:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close>
  shows
     \<open>\<not>tautology (the (get_conflict_wl S))\<close> and
     \<open>distinct_mset (the (get_conflict_wl S))\<close> and
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> -L \<in> lits_of_l (get_trail_wl S)\<close>
     \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> L \<notin> lits_of_l (get_trail_wl S)\<close>
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (M, N, U, Some D, NP, UP, W, Q)\<close>
    using confl by (cases S; cases \<open>get_conflict_wl S\<close>; cases \<open>hd (get_trail_wl S)\<close>;
        cases \<open>get_trail_wl S\<close>) auto
  have
     confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     M_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using assms unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def twl_struct_invs_def
    by auto
  have dist_D: \<open>distinct_mset D\<close>
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  then show \<open>distinct_mset (the (get_conflict_wl S))\<close>
    by (auto simp: S)

  have M_D: \<open>convert_lits_l N M \<Turnstile>as CNot D\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (auto simp: S true_annots_true_cls)

  have M_D': \<open>M \<Turnstile>as CNot D\<close>
    using M_D by (auto simp: true_annots_true_cls split: if_splits)

  have cons: \<open>consistent_interp (lits_of_l M)\<close> and n_d: \<open>no_dup M\<close>
    using M_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S)
  have tauto_D: \<open>\<not>tautology D\<close>
    using M_D' cons consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> D]
    by (auto dest!: distinct_consistent_interp simp: true_annots_true_cls)
  then show \<open> \<not> tautology (the (get_conflict_wl S))\<close>
    by (auto simp: S)

  show H: \<open>\<And>L. L \<in># the (get_conflict_wl S) \<Longrightarrow> -L \<in> lits_of_l (get_trail_wl S)\<close>
    using M_D' unfolding S true_annots_true_cls_def_iff_negation_in_model
    by auto
  show \<open>L \<in># the (get_conflict_wl S) \<Longrightarrow> L \<notin> lits_of_l (get_trail_wl S)\<close> for L
    using H[of L] n_d
    unfolding S true_annots_true_cls_def_iff_negation_in_model
    by (auto dest: no_dup_consistentD)
qed

lemma tl_state_wl_refine[sepref_fr_rules]:
  \<open>(tl_state_wl_heur_code, RETURN o tl_state_wl) \<in>
    [\<lambda>S. get_trail_wl S \<noteq> [] \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        twl_struct_invs (twl_st_of None (st_l_of_wl None S)) \<and>
        -lit_of (hd (get_trail_wl S)) \<notin># the (get_conflict_wl S) \<and>
        \<not>is_decided (hd (get_trail_wl S)) \<and>
         get_conflict_wl S \<noteq> None]\<^sub>a
      twl_st_assn\<^sup>d \<rightarrow> twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
   \<in> [comp_PRE twl_st_heur
     (\<lambda>S. get_trail_wl S \<noteq> [] \<and>
          lit_of (hd (get_trail_wl S)) \<in> snd ` D\<^sub>0 \<and>
          lit_of (hd (get_trail_wl S))
          \<notin># the (get_conflict_wl S) \<and>
          - lit_of (hd (get_trail_wl S))
          \<notin># the (get_conflict_wl S) \<and>
          \<not> tautology (the (get_conflict_wl S)) \<and>
          distinct_mset (the (get_conflict_wl S)) \<and>
          \<not> is_decided (hd (get_trail_wl S)))
     (\<lambda>_ (M, N, U, D, WS, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, _).
         M \<noteq> [] \<and>
         atm_of (lit_of (hd M)) < length \<phi> \<and>
         atm_of (lit_of (hd M)) < length A \<and>
         (next_search \<noteq> None \<longrightarrow> the next_search < length A))
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>d)
                    twl_st_heur \<rightarrow> hr_comp twl_st_heur_assn
    twl_st_heur\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF tl_state_wl_heur_code_refine tl_state_wl_heur_tl_state_wl]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_\<L>\<^sub>i\<^sub>n_hd_trail_in_D\<^sub>0[of x]
      twl_struct_invs_confl[of x]
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    apply (cases \<open>get_trail_wl x\<close>)
    by (auto simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    twl_st_assn_W_list[symmetric] twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    twl_st_assn_W_list[symmetric] hr_comp_prod_conv
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition (in -) get_max_lvl_st :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat\<close> where
  \<open>get_max_lvl_st S L = get_maximum_level_remove (get_trail_wl S) (the (get_conflict_wl S)) L\<close>

type_synonym (in -) twl_st_wl_heur_lookup_conflict =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    (bool \<times> nat \<times> bool option list) \<times> nat literal multiset \<times> nat list list \<times> vmtf_remove_int \<times>
     bool list \<times> nat\<close>

definition twl_st_wl_heur_lookup_conflict_rel :: \<open>(twl_st_wl_heur_lookup_conflict \<times> twl_st_wl_heur) set\<close> where
  \<open>twl_st_wl_heur_lookup_conflict_rel =
     (Id :: ((nat,nat) ann_lits \<times> _) set) \<times>\<^sub>r
     (Id :: (nat clauses_l  \<times> _) set) \<times>\<^sub>r
     nat_rel \<times>\<^sub>r
     (option_conflict_rel :: _ set) \<times>\<^sub>r
     (Id :: (nat lit_queue_wl \<times> _) set)  \<times>\<^sub>r
     (Id :: (nat list list \<times> _)set) \<times>\<^sub>r
     Id \<times>\<^sub>r
     Id \<times>\<^sub>r
     nat_rel\<close>

definition twl_st_heur_lookup_conflict_assn
  :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close>
where
  \<open>twl_st_heur_lookup_conflict_assn =
    trail_assn *assn clauses_ll_assn *assn nat_assn *assn
    conflict_option_rel_assn *assn
    clause_l_assn *assn
    arrayO_assn (arl_assn nat_assn) *assn
    vmtf_remove_conc *assn phase_saver_conc *assn uint32_nat_assn
  \<close>

lemma twl_st_wl_heur_lookup_conflict_rel_twl_st_rel:
  \<open>twl_st_wl_heur_lookup_conflict_rel O twl_st_heur =
     {((M', N', U', D', Q', W', vm, \<phi>, clvls), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M \<and> clvls \<in> counts_maximum_level M D}\<close>
  unfolding twl_st_heur_def twl_st_wl_heur_lookup_conflict_rel_def
  by force

lemma twl_st_heur_assn_int_conflict_assn:
  \<open>twl_st_heur_assn = hr_comp twl_st_heur_lookup_conflict_assn twl_st_wl_heur_lookup_conflict_rel\<close>
  unfolding twl_st_heur_assn_def twl_st_heur_lookup_conflict_assn_def
    twl_st_wl_heur_lookup_conflict_rel_def
  by (auto simp: list_assn_list_mset_rel_eq_list_mset_assn conflict_option_assn_def)


lemma twl_st_assn_confl_assn:
  \<open>twl_st_assn = hr_comp twl_st_heur_lookup_conflict_assn
    (twl_st_wl_heur_lookup_conflict_rel O twl_st_heur)\<close>
  apply (subst hr_comp_assoc[symmetric])
  apply (subst twl_st_heur_assn_int_conflict_assn[symmetric])
  unfolding twl_st_assn_def ..


definition (in -) lookup_conflict_remove1 :: \<open>nat literal \<Rightarrow> conflict_rel \<Rightarrow> conflict_rel\<close> where
  \<open>lookup_conflict_remove1 =
     (\<lambda>L (n,xs). if xs ! (atm_of L) = None then (n, xs) else (n-1, xs [atm_of L := None]))\<close>

lemma lookup_conflict_remove1:
  \<open>(uncurry (RETURN oo lookup_conflict_remove1), uncurry (RETURN oo remove1_mset)) \<in>
  [\<lambda>(L,C). L \<in># C \<and> -L \<notin># C \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f conflict_rel \<rightarrow> \<langle>conflict_rel\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (case_tac y; case_tac x)
  subgoal for x y a b aa ab c
    using mset_as_position_remove[of c b \<open>atm_of aa\<close>]
    by (cases \<open>aa\<close>)
       (auto simp: conflict_rel_def lookup_conflict_remove1_def  conflict_rel_atm_in_iff minus_notin_trivial2
      size_remove1_mset_If in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff minus_notin_trivial mset_as_position_in_iff_nth)
   done

sepref_thm conflict_remove1_code
  is \<open>uncurry (RETURN oo lookup_conflict_remove1)\<close>
  :: \<open>[\<lambda>(L, (n,xs)). n > 0 \<and> atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>d \<rightarrow>
     conflict_rel_assn\<close>
  supply [[goals_limit=2]] one_uint32_nat[sepref_fr_rules]
  unfolding lookup_conflict_remove1_def one_uint32_nat_def[symmetric] fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) conflict_remove1_code
  uses isasat_input_bounded_nempty.conflict_remove1_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) conflict_remove1_code_def

lemmas conflict_remove1_code_refine[sepref_fr_rules] =
   conflict_remove1_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma conflict_remove1_code_op_nset_delete[sepref_fr_rules]:
  \<open>(uncurry conflict_remove1_code, uncurry (RETURN \<circ>\<circ> op_mset_delete))
    \<in> [\<lambda>(L, C). L \<in> snd ` D\<^sub>0 \<and> L \<in># C \<and> -L \<notin># C]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a conflict_assn\<^sup>d \<rightarrow> conflict_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (Id \<times>\<^sub>f conflict_rel) (\<lambda>(L, C). L \<in># C \<and> - L \<notin># C \<and> L \<in> snd ` D\<^sub>0)
              (\<lambda>_ (L, n, xs). 0 < n \<and> atm_of L < length xs)
              (\<lambda>_. True)]\<^sub>a
    hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_rel_assn\<^sup>d) (Id \<times>\<^sub>f conflict_rel) \<rightarrow>
    hr_comp conflict_rel_assn conflict_rel\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF conflict_remove1_code_refine lookup_conflict_remove1]
    unfolding op_mset_delete_def
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that neq0_conv
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (fastforce simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma conflict_option_assn_the[sepref_fr_rules]:
  \<open>(return o snd, RETURN o the) \<in> [\<lambda>C. C \<noteq> None]\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> conflict_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_def conflict_option_assn_def conflict_rel_def hr_comp_def
    option_conflict_rel_def)

lemma conflict_option_assn_Some[sepref_fr_rules]:
  \<open>(return o (\<lambda>C. (False, C)), RETURN o Some) \<in> conflict_assn\<^sup>d \<rightarrow>\<^sub>a conflict_option_assn\<close>
  by sepref_to_hoare
     (sep_auto simp: conflict_assn_def conflict_option_assn_def conflict_rel_def hr_comp_def
    option_conflict_rel_def bool_assn_alt_def)

lemma resolve_cls_wl'_union_uminus_zero_index:
  assumes
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C = 0\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = remove1_mset (-L) (the (get_conflict_wl S))\<close>
  using assms by (auto simp: resolve_cls_wl'_def)


definition (in -) lookup_conflict_merge_abs_union'
  :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> nat \<Rightarrow> 'v cconflict\<close>
where
  \<open>lookup_conflict_merge_abs_union' M N i C _ =
      Some (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i))))\<close>

definition (in -) lookup_conflict_merge_abs_union
  :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> nat \<Rightarrow> 'v clause option \<Rightarrow> nat \<Rightarrow>
     ('v cconflict \<times> nat) nres\<close>
where
  \<open>lookup_conflict_merge_abs_union M N i C _ = RES {(Some (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i)))),
    card_max_lvl M (mset (N!i) \<union># (the C - (mset (N!i) + uminus `# mset (N!i)))))}\<close>

lemma lookup_conflict_merge_abs_union_alt_def:
  \<open>lookup_conflict_merge_abs_union M N i C clvls = RES {(lookup_conflict_merge_abs_union' M N i C clvls,
    card_max_lvl M (the (lookup_conflict_merge_abs_union' M N i C clvls)))}\<close>
  unfolding lookup_conflict_merge_abs_union_def lookup_conflict_merge_abs_union'_def by auto

lemma card_max_lvl_tl_remove_hd:
  assumes
    \<open>M \<noteq> []\<close> and
    \<open>distinct_mset C\<close> \<open>no_dup M\<close> \<open>distinct_mset C\<close>\<open>\<not>tautology C\<close> \<open>\<not>is_decided (hd M)\<close>
    \<open>lit_of (hd M) \<in># C\<close>
  shows \<open>card_max_lvl (tl M) (C - unmark (hd M)) =
         card_max_lvl M C - 1\<close>
  using assms
  by (cases M) (auto simp: card_max_lvl_Cons card_max_lvl_add_mset
      dest!: multi_member_split)

lemma (in -) tautology_union_add_iff[simp]:
  \<open>tautology (A \<union># B) \<longleftrightarrow> tautology (A + B)\<close>
  by (auto simp: tautology_decomp)
lemma (in -) tautology_add_mset_union_add_iff[simp]:
  \<open>tautology (add_mset L (A \<union># B)) \<longleftrightarrow> tautology (add_mset L (A + B))\<close>
  by (auto simp: tautology_decomp)

lemma
  fixes S and C clvls :: nat
  defines [simp]: \<open>E \<equiv> the (lookup_conflict_merge_abs_union' (get_trail_wl S)  (get_clauses_wl S) C (get_conflict_wl S) clvls)\<close>
  assumes invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    C: \<open>C < length (get_clauses_wl S)\<close> and
    L_confl: \<open>-L \<in># the (get_conflict_wl S)\<close> and
    tr: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close>
       \<open>is_proped (hd (get_trail_wl S))\<close> \<open>get_trail_wl S \<noteq> []\<close>
  shows
    resolve_cls_wl'_union_uminus_positive_index:
      \<open>C > 0 \<Longrightarrow> resolve_cls_wl' S C L =
          remove1_mset L E\<close>
       (is \<open>_ \<Longrightarrow> ?Res\<close>) and
    resolve_cls_wl'_not_tauto_confl: \<open>\<not>tautology (the (get_conflict_wl S))\<close> (is ?tauto) and
    resolve_cls_wl'_not_tauto_cls: \<open>C > 0 \<Longrightarrow> \<not>tautology (mset (get_clauses_wl S ! C))\<close>
      (is \<open>_ \<Longrightarrow> ?tauto_cls\<close>) and
    resolve_cls_wl'_L_in_cls: \<open>C > 0 \<Longrightarrow> L \<in> set (get_clauses_wl S ! C)\<close> (is \<open>_ \<Longrightarrow> ?L_in_cls\<close>) and
    resolve_cls_wl'_in:
      \<open>C > 0 \<Longrightarrow> L \<in># E\<close>
      (is \<open>_ \<Longrightarrow> ?L_in_union\<close>) and
    resolve_cls_wl'_notin:
      \<open>C > 0 \<Longrightarrow> -L \<notin># E\<close>
      (is \<open>_ \<Longrightarrow> ?L_notin_union\<close>) and
    resolve_cls_wl'_not_tauto: \<open>C > 0 \<Longrightarrow> \<not> tautology E\<close> and
    resolve_cls_wl'_card_max_lvl:
       \<open>C > 0 \<Longrightarrow> card_max_lvl (get_trail_wl S) E = card_max_lvl (tl (get_trail_wl S))
         (E - unmark (hd (get_trail_wl S))) + 1\<close>(is \<open>_ \<Longrightarrow> ?Max\<close>)
proof -
  obtain M N U D NP UP Q W where
    S: \<open>S = (Propagated L C # M, N, U, Some D, NP, UP, W, Q)\<close>
    using confl tr by (cases S; cases \<open>get_conflict_wl S\<close>; cases \<open>hd (get_trail_wl S)\<close>;
        cases \<open>get_trail_wl S\<close>) auto
  obtain D' where
    D: \<open>D = add_mset (-L) D'\<close>
    using L_confl by (auto simp: S dest: multi_member_split)
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding twl_struct_invs_def by fast
  then have
     confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     M_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
     dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close>
     unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have dist_D: \<open>distinct_mset D\<close>
    using dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  have undef_L: \<open>undefined_lit M L\<close> and n_d: \<open>no_dup M\<close>
    using M_inv unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S split: if_splits)
  have M_D: \<open>Propagated L (mset (N ! C)) # convert_lits_l N M \<Turnstile>as CNot D\<close>
    using confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases C) (auto simp: S true_annots_true_cls)

  have M_D': \<open>Propagated L C # M \<Turnstile>as CNot D\<close>
    using M_D by (auto simp: true_annots_true_cls split: if_splits)
  have tauto_D: \<open>\<not>tautology D\<close>
    using M_D' n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l (Propagated L C # M)\<close> D]
    by (auto dest!: distinct_consistent_interp simp: true_annots_true_cls)
  then show ?tauto
    by (auto simp: S)

  assume C': \<open>C > 0\<close>
  have \<open>L \<in># mset (N ! C)\<close> and
    M_C: \<open>M \<Turnstile>as CNot (mset (N!C) - {#L#})\<close>
    using C C' confl unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (fastforce simp: S)+
  from multi_member_split[OF this(1)] obtain C' where
    C'': \<open>mset (N ! C) = add_mset L C'\<close>
    by auto
  moreover have uL_C': \<open>-L \<notin># C'\<close>
    using M_C undef_L by (auto simp: C'' true_annots_true_cls_def_iff_negation_in_model
        Decided_Propagated_in_iff_in_lits_of_l)
  ultimately show tauto_C: ?tauto_cls
    using M_C n_d undef_L consistent_CNot_not_tautology[of \<open>lits_of_l M\<close> \<open>C'\<close>]
    by (auto 5 5 dest!: distinct_consistent_interp simp: tautology_add_mset true_annots_true_cls C' S)
  have get_clss_S: \<open>get_clauses_wl S = N\<close>
    by (auto simp: S)
  show ?L_in_cls
    unfolding in_multiset_in_set[symmetric] get_clss_S C'' by simp

  have n_d_L: \<open>L \<in> lits_of_l M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow> False\<close> for L
    using distinct_consistent_interp[OF n_d] by (auto simp: consistent_interp_def)
  have dist_C: \<open>distinct_mset (mset (N ! C))\<close>
    using C C' dist unfolding cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by (auto simp: S)
  have uL_C'': \<open>-L \<notin># C' - uminus `# D'\<close>
    using uL_C' by (auto dest!: in_diffD)
  moreover have D'C'D': \<open>D' - uminus `# C' = D'\<close>
    apply (rule minus_eq_id_forall_notin_mset[THEN iffD2])
    unfolding Ball_def
    apply (rule impI conjI allI)
    subgoal for L'
      using undef_L n_d M_D' M_C n_d_L[of L']
      by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)
    done

  moreover have \<open>L \<notin># D'\<close>
    using tauto_D by (auto simp: tautology_add_mset D S)
  moreover have [simp]: \<open>L \<notin># D' - add_mset L (C' + uminus `# C')\<close>
    using \<open>L \<notin># D'\<close> by (auto dest: in_diffD)
  moreover have [simp]: \<open>distinct_mset D'\<close> \<open>distinct_mset C'\<close>
    using dist_D dist_C unfolding D C'' C' by auto
  moreover have \<open>C' \<union># D' = C' \<union># (D' - (C' + uminus `# C'))\<close>
  proof -
    have \<open>D' - (C' + uminus `# C') = (D' -uminus `# C') - C'\<close>
      by (auto simp: ac_simps)
    also have \<open>\<dots> = D' - C'\<close>
      unfolding D'C'D' ..
    finally have A: \<open>C' \<union># (D' - (C' + uminus `# C')) = C' \<union># (D' - C')\<close> by simp
    show ?thesis
      unfolding A
      by (auto simp: ac_simps distinct_mset_rempdups_union_mset distinct_mset_in_diff
          intro!: distinct_set_mset_eq dest: in_diffD)
  qed
  ultimately show ?Res
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def minus_notin_trivial S)
  show ?L_in_union
    using C C' unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def S)
  show ?L_notin_union
    using C C' uL_C' uL_C'' dist_D unfolding S by (auto simp: C'' D resolve_cls_wl'_def ac_simps
        lookup_conflict_merge_abs_union'_def S dest: in_diffD)
  have [simp]: \<open>L \<notin># D'\<close>
    using undef_L n_d M_D' M_C
    by (auto 5 5 simp: C'' D true_annots_true_cls_def_iff_negation_in_model uminus_lit_swap
        Decided_Propagated_in_iff_in_lits_of_l)

   have \<open>D' - (C' + uminus `# C') = (D' -uminus `# C') - C'\<close>
      by (auto simp: ac_simps)
    also have \<open>\<dots> = D' - C'\<close>
      unfolding D'C'D' ..
    finally show \<open>\<not> tautology E\<close>
    using uL_C' dist_D tauto_C tauto_D
    apply (auto simp: S lookup_conflict_merge_abs_union'_def C'' tautology_add_mset
        distinct_mset_in_diff D minus_notin_trivial
       )
    unfolding tautology_decomp'
    apply (auto simp: distinct_mset_in_diff)
    apply (metis D'C'D' image_eqI minus_eq_id_forall_notin_mset set_image_mset)
    by (metis (mono_tags, lifting) D'C'D' image_mset_add_mset insert_DiffM
        minus_eq_id_forall_notin_mset uminus_of_uminus_id union_single_eq_member)
  then have \<open>card_max_lvl (Propagated L C # M)
     (add_mset L (C' \<union># (D' - add_mset L (C' + uminus `# C')))) =
    card_max_lvl M (C' \<union># (D' - add_mset L (C' + uminus `# C'))) + 1\<close>
    apply (subst card_max_lvl_Cons)
    using undef_L n_d tauto_C dist_C uL_C'
    by (auto simp: S C'' lookup_conflict_merge_abs_union'_def D
        card_max_lvl_add_mset)
  then show ?Max
    by (auto simp: S resolve_cls_wl'_def lookup_conflict_merge_abs_union'_def C'' D)
qed

lemma lookup_conflict_merge_aa_lookup_conflict_merge_abs_union_aa:
  \<open>(uncurry4 (lookup_conflict_merge_aa), uncurry4 lookup_conflict_merge_abs_union) \<in>
     [\<lambda>((((M, N), i), C), clvls). distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and>
          \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and>
         clvls = card_max_lvl M (the C)]\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<times>\<^sub>f nat_rel \<rightarrow> \<langle>option_conflict_rel \<times>\<^sub>r nat_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for M N i b j xs clvls M' N' i' _ clvls' C
    using lookup_conflict_merge'_spec[of b j xs C \<open>N' ! i'\<close> clvls M]
    unfolding lookup_conflict_merge_abs_union_def lookup_conflict_merge_aa_def
    by auto
  done

lemma lookup_conflict_merge_code_lookup_conflict_merge_abs_union[sepref_fr_rules]:
  \<open>(uncurry4 lookup_conflict_merge_code, uncurry4 lookup_conflict_merge_abs_union) \<in>
    [\<lambda>((((M, N), i), C), clvls). distinct (N!i) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N!i)) \<and> \<not> tautology (mset (N!i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> C \<noteq> None \<and> i < length N \<and> clvls = card_max_lvl M (the C)]\<^sub>a
    trail_assn\<^sup>k *\<^sub>a clauses_ll_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (conflict_option_assn)\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>
     conflict_option_assn *assn uint32_nat_assn \<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
     \<in> [comp_PRE
     (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f option_conflict_rel \<times>\<^sub>f
      nat_rel)
     (\<lambda>((((M, N), i), C), clvls).
         distinct (N ! i) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)) \<and>
         \<not> tautology (mset (N ! i)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
         C \<noteq> None \<and> clvls = card_max_lvl M (the C))
     (\<lambda>_ ((((M, N), i), _, xs), _).
         i < length N \<and>
         (\<forall>j<length (N ! i).
             atm_of (N ! i ! j) < length (snd xs)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i)))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                    ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a
                     clauses_ll_assn\<^sup>k *\<^sub>a
                     nat_assn\<^sup>k *\<^sub>a
                     conflict_option_rel_assn\<^sup>d *\<^sub>a
                     uint32_nat_assn\<^sup>k)
                    (Id \<times>\<^sub>f Id \<times>\<^sub>f nat_rel \<times>\<^sub>f
                     option_conflict_rel \<times>\<^sub>f
                     nat_rel) \<rightarrow> hr_comp
   (conflict_option_rel_assn *assn uint32_nat_assn)
   (option_conflict_rel \<times>\<^sub>f nat_rel)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lookup_conflict_merge_aa_hnr[unfolded PR_CONST_def]
      lookup_conflict_merge_aa_lookup_conflict_merge_abs_union_aa]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that literals_are_in_\<L>\<^sub>i\<^sub>n_in_\<L>\<^sub>a\<^sub>l\<^sub>l
    unfolding comp_PRE_def option_conflict_rel_def conflict_rel_def
    by (auto simp: image_image twl_st_heur_def phase_saving_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      vmtf_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep hr_comp_prod_conv conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition update_confl_tl_wl_heur
  :: \<open>nat \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> (bool \<times> twl_st_wl_heur) nres\<close>
where
  \<open>update_confl_tl_wl_heur = (\<lambda>C L (M, N, U, D, Q, W, vmtf, \<phi>, clvls).
     (if C = 0 then do {
         let D' = remove1_mset (-L) (the D);
         let L' = atm_of L;
         ASSERT (clvls \<ge> 1);
         RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf, save_phase L \<phi>,
            fast_minus clvls one_uint32_nat))
         }
      else do {
        let L' = atm_of L;
        (D', clvls) \<leftarrow> lookup_conflict_merge_abs_union M N C D clvls;
        let D' = remove1_mset L (the D');
        RETURN (D' = {#}, (tl M, N, U, Some D', Q, W, vmtf_mark_to_rescore_and_unset L' vmtf, save_phase L \<phi>,
           fast_minus clvls one_uint32_nat))
      }))\<close>

lemma card_max_lvl_remove1_mset_hd:
  \<open>-lit_of (hd M) \<in># y \<Longrightarrow> is_proped (hd M) \<Longrightarrow>
     card_max_lvl M (remove1_mset (-lit_of (hd M)) y) = card_max_lvl M y - 1\<close>
  by (cases M)  (auto dest!: multi_member_split simp: card_max_lvl_add_mset)


lemma resolve_cls_wl'_if_lookup_conflict_merge_abs_union:
  assumes
    \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>C < length (get_clauses_wl S)\<close> and
    \<open>- L \<in># the (get_conflict_wl S)\<close> and
    \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
    \<open>is_proped (hd (get_trail_wl S))\<close> and
    \<open>get_trail_wl S \<noteq> []\<close>
  shows \<open>resolve_cls_wl' S C L = (if C = 0 then remove1_mset (-L) (the (get_conflict_wl S))
               else remove1_mset L (the (lookup_conflict_merge_abs_union' (get_trail_wl S) (get_clauses_wl S) C (get_conflict_wl S) clvls)))\<close>
  using resolve_cls_wl'_union_uminus_positive_index[of \<open>S\<close> C L] assms
  unfolding lookup_conflict_merge_abs_union_def[symmetric]
  by (auto simp: resolve_cls_wl'_def)

lemma update_confl_tl_wl_heur_state_helper:
   \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<Longrightarrow> get_trail_wl S \<noteq> [] \<Longrightarrow>
    is_proped (hd (get_trail_wl S)) \<Longrightarrow> L = lit_of (hd (get_trail_wl S))\<close>
  by (cases S; cases \<open>hd (get_trail_wl S)\<close>) auto

lemma (in -) not_ge_Suc0: \<open>\<not>Suc 0 \<le> n \<longleftrightarrow> n = 0\<close> (* WTF *)
  by auto

lemma card_max_lvl_ge_1:
  assumes \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    \<open>get_conflict_wl S \<noteq> None\<close> and
    \<open>get_conflict_wl S \<noteq> Some {#}\<close>
  shows
   \<open>card_max_lvl (get_trail_wl S) (the (get_conflict_wl S)) \<ge> Suc 0\<close>
  using assms unfolding twl_stgy_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
     cdcl\<^sub>W_restart_mset.conflict_is_false_with_level_def
  by (cases S) (auto simp: card_max_lvl_def not_ge_Suc0 filter_mset_empty_conv)

lemma update_confl_tl_wl_heur_update_confl_tl_wl:
  \<open>(uncurry2 (update_confl_tl_wl_heur), uncurry2 (RETURN ooo update_confl_tl_wl)) \<in>
  [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
    twl_stgy_invs (twl_st_of_wl None S) \<and>
    C < length (get_clauses_wl S) \<and>
    get_conflict_wl S \<noteq> None \<and> get_trail_wl S \<noteq> [] \<and> - L \<in># the (get_conflict_wl S) \<and>
     (L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and> L \<in> snd ` D\<^sub>0 \<and>
    twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S))]\<^sub>f
   nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur \<rightarrow> \<langle>bool_rel \<times>\<^sub>f twl_st_heur\<rangle>nres_rel\<close>
  supply [[goals_limit = 2]]
  apply (intro frefI nres_relI)
  subgoal for CLS' CLS
    unfolding case_prod_beta uncurry_def update_confl_tl_wl_heur_def comp_def
    using resolve_cls_wl'_if_lookup_conflict_merge_abs_union[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>
      \<open>snd (fst CLS)\<close> \<open>get_count_max_lvls_heur (snd CLS')\<close>, symmetric]
      twl_struct_invs_confl[of \<open>snd CLS\<close>]
      update_confl_tl_wl_heur_state_helper[of \<open>snd (fst CLS)\<close> \<open>fst (fst CLS)\<close>  \<open>snd CLS\<close>]
      card_max_lvl_ge_1[of \<open>snd CLS\<close>]
      resolve_cls_wl'_card_max_lvl[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>]
      resolve_cls_wl'_not_tauto[of \<open>snd CLS\<close> \<open>fst (fst CLS)\<close>]
    by (cases \<open>CLS'\<close>; cases CLS)
       (auto simp: twl_st_heur_def update_confl_tl_wl_heur_def update_confl_tl_wl_def
        vmtf_unset_vmtf_tl Let_def save_phase_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff phase_saving_def vmtf_mark_to_rescore_unset
        lookup_conflict_merge_abs_union_alt_def
        RES_RETURN_RES RETURN_def no_dup_tlD counts_maximum_level_def
        RES_RES_RETURN_RES (* lookup_conflict_merge_abs_union'_def *)
        eq_commute[of \<open>remove1_mset _ _\<close> \<open>resolve_cls_wl' _ _ _\<close>]
        in_multiset_nempty card_max_lvl_tl
        distinct_mset_in_diff not_tautology_minus
          card_max_lvl_remove1_mset_hd is_decided_no_proped_iff
        intro!: RES_refine ASSERT_refine_left) (* slow *)
  done


lemma lookup_conflict_merge_abs_union_None: \<open>lookup_conflict_merge_abs_union' M a b c clvls \<noteq> None\<close>
  unfolding lookup_conflict_merge_abs_union'_def by auto


lemma conflict_assn_op_nset_is_emty[sepref_fr_rules]:
  \<open>(return o (\<lambda>(n, _). n = 0), RETURN o op_mset_is_empty) \<in> conflict_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi, case_tac xi)
  by (sep_auto simp: conflict_assn_def conflict_rel_def hr_comp_def
    uint32_nat_assn_0_eq uint32_nat_rel_def br_def pure_def nat_of_uint32_0_iff)+


sepref_thm update_confl_tl_wl_code
  is \<open>uncurry2 update_confl_tl_wl_heur\<close>
  :: \<open>[\<lambda>((i, L), (M, N, U, D, W, Q, ((A, m, fst_As, lst_As, next_search), _), \<phi>, clvls)).
      (i > 0 \<longrightarrow> distinct (N ! i)) \<and>
      (i > 0 \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N! i))) \<and>
      (i > 0 \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
      i < length N \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and>
      M \<noteq> [] \<and>
      L \<in> snd ` D\<^sub>0 \<and> -L \<in># the D \<and> L \<notin># the D \<and>
      (i > 0 \<longrightarrow> (L \<in> set (N ! i) \<and> -L \<notin> set (N ! i))) \<and>
      (i > 0 \<longrightarrow> (-L \<notin># the (lookup_conflict_merge_abs_union' M N i D clvls) \<and>
           L \<in># the (lookup_conflict_merge_abs_union' M N i D clvls))) \<and>
      (i > 0 \<longrightarrow> card_max_lvl M (the (lookup_conflict_merge_abs_union' M N i D clvls)) \<ge> 1) \<and>
      atm_of (lit_of (hd M)) < length \<phi> \<and>
      atm_of (lit_of (hd M)) < length A \<and> (next_search \<noteq> None \<longrightarrow>  the next_search < length A) \<and>
      L = lit_of (hd M) \<and>
      clvls = card_max_lvl M (the D)
         ]\<^sub>a
  nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> bool_assn *assn twl_st_heur_assn\<close>
  supply image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[iff] in_diffD[dest] option.splits[split]
  supply [[goals_limit=1]]
  supply lookup_conflict_merge_abs_union_None[simplified, simp]
  unfolding update_confl_tl_wl_heur_def twl_st_heur_assn_def save_phase_def
  supply lookup_conflict_merge_abs_union'_def[simp] lookup_conflict_merge_abs_union_def[simp]
  by sepref (* slow *)

concrete_definition (in -) update_confl_tl_wl_code
  uses isasat_input_bounded_nempty.update_confl_tl_wl_code.refine_raw
  is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) update_confl_tl_wl_code_def

lemmas update_confl_tl_wl_code_refine[sepref_fr_rules] =
   update_confl_tl_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma update_confl_tl_wl_code_update_confl_tl_wl[sepref_fr_rules]:
  \<open>(uncurry2 update_confl_tl_wl_code, uncurry2 (RETURN ooo update_confl_tl_wl))
    \<in> [\<lambda>((C, L), S). twl_struct_invs (twl_st_of_wl None S) \<and>
        twl_stgy_invs (twl_st_of_wl None S) \<and>
        get_conflict_wl S \<noteq> None \<and>
        get_trail_wl S \<noteq> [] \<and>
        - L \<in># the (get_conflict_wl S) \<and>
        (L, C) = lit_and_ann_of_propagated_st S \<and>
        literals_are_\<L>\<^sub>i\<^sub>n S \<and>
        twl_struct_invs (twl_st_of_wl None S) \<and> is_proped (hd (get_trail_wl S)) \<and>
        additional_WS_invs (st_l_of_wl None S)]\<^sub>a
       nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow> bool_assn *assn twl_st_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in> [comp_PRE (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur)
       (\<lambda>((C, L), S).
           twl_struct_invs (twl_st_of_wl None S) \<and>
           twl_stgy_invs (twl_st_of_wl None S) \<and>
           C < length (get_clauses_wl S) \<and>
           get_conflict_wl S \<noteq> None \<and>
           get_trail_wl S \<noteq> [] \<and>
           - L \<in># the (get_conflict_wl S) \<and>
           (L, C) =
           lit_and_ann_of_propagated (hd (get_trail_wl S)) \<and>
           L \<in> snd ` D\<^sub>0 \<and>
           twl_struct_invs (twl_st_of_wl None S) \<and>
           is_proped (hd (get_trail_wl S)))
       (\<lambda>_ ((i, L), M, N, U, D, W, Q, ((A, m, fst_As, lst_As,
           next_search), _), \<phi>, clvls).
           (0 < i \<longrightarrow> distinct (N ! i)) \<and>
           (0 < i \<longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! i))) \<and>
           (0 < i \<longrightarrow> \<not> tautology (mset (N ! i))) \<and>
           i < length N \<and>
           literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and>
           D \<noteq> None \<and>
           M \<noteq> [] \<and>
           L \<in> snd ` D\<^sub>0 \<and>
           - L \<in># the D \<and>
           L \<notin># the D \<and>
           (0 < i \<longrightarrow> L \<in> set (N ! i) \<and> - L \<notin> set (N ! i)) \<and>
           (0 < i \<longrightarrow>
            - L
            \<notin># the (lookup_conflict_merge_abs_union' M N i D
                      clvls) \<and>
            L \<in># the (lookup_conflict_merge_abs_union' M N i D
                        clvls)) \<and>
           (0 < i \<longrightarrow>
            1 \<le> card_max_lvl M
                  (the (lookup_conflict_merge_abs_union' M N i D
                         clvls))) \<and>
           atm_of (lit_of (hd M)) < length \<phi> \<and>
           atm_of (lit_of (hd M)) < length A \<and>
           (next_search \<noteq> None \<longrightarrow>
            the next_search < length A) \<and>
           L = lit_of (hd M) \<and>
           clvls = card_max_lvl M (the D))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                      (nat_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                       twl_st_heur_assn\<^sup>d)
                      (nat_rel \<times>\<^sub>f Id \<times>\<^sub>f
                       twl_st_heur) \<rightarrow> hr_comp
        (bool_assn *assn twl_st_heur_assn)
        (bool_rel \<times>\<^sub>f twl_st_heur)\<close>
      (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using  hfref_compI_PRE_aux[OF update_confl_tl_wl_code_refine
       update_confl_tl_wl_heur_update_confl_tl_wl]
    .
  have pre: \<open>?pre' x\<close> (is \<open>comp_PRE ?rel ?\<Phi> ?\<Psi> _ x\<close>) if pre: \<open>?pre x\<close> for x
  unfolding comp_PRE_def
  proof (intro allI impI conjI)
    obtain C L S where
      [simp]: \<open>x = ((C,L), S)\<close>
      by (cases x) auto
    obtain M N U D W Q NP UP where
      [simp]: \<open>S = (M, N, U, D, NP, UP, W, Q)\<close>
      by (cases S) auto
    have LC: \<open>(L, C) = lit_and_ann_of_propagated (hd (get_trail_wl S))\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
      struct_invs: \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
      trail_nempty: \<open>get_trail_wl S \<noteq> []\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
      proped: \<open>is_proped (hd (get_trail_wl S))\<close> and
      confl: \<open>get_conflict_wl S \<noteq> None\<close> and
      L_confl: \<open>-L \<in># the(get_conflict_wl S)\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)
    have lits_D: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
      by (rule literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n)
       (use lits_\<A>\<^sub>i\<^sub>n confl struct_invs in auto)
    have C_le: \<open>C < length (get_clauses_wl S)\<close>
      using trail_nempty LC proped add_invs trail_nempty unfolding additional_WS_invs_def
      by (cases M; cases \<open>hd M\<close>) auto
    moreover have L_D\<^sub>0: \<open>L \<in> snd ` D\<^sub>0\<close>
      using L_confl confl lits_D
      by (cases \<open>get_conflict_wl S\<close>)
        (auto simp: image_image literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
            dest: multi_member_split)
    ultimately show \<open>?\<Phi> x\<close>
      using that by (auto simp: lit_and_ann_of_propagated_st_def)

    fix x'
    assume x'x: \<open>(x', x) \<in> nat_rel \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur\<close>
    then obtain S' where
      [simp]: \<open>x' = ((C, L), S')\<close>
      by (cases x') auto
    obtain Q' A m fst_As lst_As next_search oth \<phi> clvls where
      [simp]: \<open>S' = (M, N, U, D, W, Q', ((A, m, fst_As, lst_As, next_search), oth), \<phi>, clvls)\<close>
      using x'x by (cases S') (auto simp: twl_st_heur_def)
    have in_atms_le: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length A\<close> and \<phi>: \<open>phase_saving \<phi>\<close> and
      vmtf: \<open>\<exists>xs' ys'. vmtf_ns (ys' @ xs') m A \<and> fst_As = hd (ys' @ xs') \<and>
           lst_As = last (ys' @ xs') \<and> next_search = option_hd xs'\<close> and
      clvls: \<open>clvls \<in> counts_maximum_level M D\<close>
      using x'x unfolding twl_st_heur_def vmtf_def by auto
    then have atm_L_le_A: \<open>atm_of L < length A\<close>
      using L_D\<^sub>0 by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    have atm_L_le_\<phi>: \<open>atm_of L < length \<phi>\<close>
      using L_D\<^sub>0 \<phi> unfolding phase_saving_def by (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    obtain xs' ys' where
      \<open>vmtf_ns (ys' @ xs') m A\<close> and \<open>fst_As = hd (ys' @ xs')\<close> and \<open>next_search = option_hd xs'\<close> and
      \<open>lst_As = last (ys' @ xs')\<close>
      using vmtf by blast
    then have next_search: \<open>the next_search < length A\<close> if \<open>next_search \<noteq> None\<close>
      apply - by (rule vmtf_ns_le_length[of \<open>ys' @ xs'\<close> m A]) (use that in auto)
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      using struct_invs unfolding twl_struct_invs_def by fast
    then have \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S)))\<close>
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
    then have \<open>distinct_mset_set (mset ` set (tl N))\<close>
      apply (subst append_take_drop_id[of U, symmetric])
      unfolding set_append image_Un
      by (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def mset_take_mset_drop_mset drop_Suc)
    then have dist_NC: \<open>distinct (N ! C)\<close> if \<open>C > 0\<close>
      using that C_le nth_in_set_tl[of C N] by (auto simp: distinct_mset_set_def)

    have lits_NC: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (mset (N ! C))\<close> if \<open>C > 0\<close>
      by (rule literals_are_in_\<L>\<^sub>i\<^sub>n_nth) (use C_le that lits_\<A>\<^sub>i\<^sub>n in auto)
    have L_hd_M: \<open>L = lit_of (hd M)\<close>
      by (cases M; cases \<open>hd M\<close>) (use trail_nempty LC proped in auto)

    have \<open>\<not> tautology (the (get_conflict_wl S))\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have L_notin_D: \<open>L \<notin># the D\<close>
      using resolve_cls_wl'_not_tauto_confl[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC by auto
    have tauto: \<open>\<not>tautology (mset (N ! C))\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_not_tauto_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that
      by auto
    have L_NC: \<open>L \<in> set (N ! C)\<close> if \<open>C > 0\<close>
      using resolve_cls_wl'_L_in_cls[of S C L] struct_invs confl L_confl C_le trail_nempty
      proped LC that by auto
    have L_NC': \<open>-L \<notin> set (N ! C)\<close> if \<open>C > 0\<close>
      using tauto that L_NC apply (auto simp: tautology_decomp)
      by (metis (full_types) nat_of_lit.cases uminus_Pos uminus_of_uminus_id)
    then have uL_lookup_conflict_merge: \<open>- L \<notin># the (lookup_conflict_merge_abs_union' M N C D clvls)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_notin[of S C L] struct_invs C_le LC proped
       trail_nempty
      by (auto simp: lookup_conflict_merge_abs_union'_def dest: in_diffD)
    then have L_lookup_conflict_merge: \<open>L \<in># the (lookup_conflict_merge_abs_union' M N C D clvls)\<close> if \<open>C > 0\<close>
      using confl L_notin_D that resolve_cls_wl'_in[of S C L] struct_invs C_le LC proped
       trail_nempty L_confl
      by (auto dest: in_diffD)
    have [simp]: \<open>Suc 0 \<le> card_max_lvl M (the (lookup_conflict_merge_abs_union' M N C D
                    (card_max_lvl M (the D))))\<close>
      if \<open>C > 0\<close>
      using resolve_cls_wl'_card_max_lvl[of S C L clvls] LC confl C_le L_D\<^sub>0 clvls that pre
      by (auto simp: counts_maximum_level_def)
    show \<open>?\<Psi> x x'\<close>
      using confl L_confl dist_NC lits_NC C_le trail_nempty L_D\<^sub>0 tauto lits_D L_notin_D L_NC
      uL_lookup_conflict_merge L_lookup_conflict_merge atm_L_le_A atm_L_le_\<phi> next_search clvls
      by (auto simp: L_hd_M[symmetric] counts_maximum_level_def)
  qed
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def hr_comp_prod_conv
      conflict_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n:
  assumes
    \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
  shows \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S))\<close> (is \<open>literals_are_in_\<L>\<^sub>i\<^sub>n ?M\<close>)
proof -
  have [simp]: \<open>lit_of ` set (convert_lits_l b a) =  lit_of ` set a\<close> for a b
    by (induction a) auto
  have alien: \<open>cdcl\<^sub>W_restart_mset.no_strange_atm (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast
  then have N: \<open>atms_of ?M \<subseteq> atms_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S)))\<close>
    unfolding cdcl\<^sub>W_restart_mset.no_strange_atm_def lits_of_def atms_of_def
    by (cases S)
      (auto simp: mset_take_mset_drop_mset')

  have \<open>is_\<L>\<^sub>a\<^sub>l\<^sub>l (all_lits_of_mm (init_clss (state\<^sub>W_of (twl_st_of_wl None S))))\<close>
    using twl_struct_invs_is_\<L>\<^sub>a\<^sub>l\<^sub>l_clauses_init_clss[OF struct] \<A>\<^sub>i\<^sub>n by fast
  then show ?thesis
    using N in_all_lits_of_m_ain_atms_of_iff in_all_lits_of_mm_ain_atms_of_iff
    by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_def is_\<L>\<^sub>a\<^sub>l\<^sub>l_def )
qed

lemma skip_and_resolde_hd_D\<^sub>0:
  assumes
    \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None S))\<close> and
    \<open>get_trail_wl S = Propagated x21 x22 # xs\<close> and
    \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
  shows \<open>- x21 \<in> snd ` D\<^sub>0\<close>
  using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[of S] assms
  by (cases S)
     (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset image_image
      uminus_\<A>\<^sub>i\<^sub>n_iff)

end


setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

sepref_register skip_and_resolve_loop_wl_D literal_is_in_conflict
sepref_thm skip_and_resolve_loop_wl_D
  is \<open>PR_CONST skip_and_resolve_loop_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] get_trail_twl_st_of_wl_get_trail_wl_empty_iff[simp] is_decided_hd_trail_wl_def[simp]
    is_decided_no_proped_iff[simp] skip_and_resolve_hd_in_D\<^sub>0[intro]
    literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[intro]
    get_conflict_l_st_l_of_wl[simp] literal_is_in_conflict_def[simp]  neq_NilE[elim!]
    annotated_lit.splits[split] lit_and_ann_of_propagated_st_def[simp]
    annotated_lit.disc_eq_case(2)[simp]
    skip_and_resolde_hd_D\<^sub>0[simp]
    not_None_eq[simp del] maximum_level_removed_eq_count_dec_def[simp]
  apply (subst PR_CONST_def)
  unfolding skip_and_resolve_loop_wl_D_def
  apply (rewrite at \<open>\<not>_ \<and> \<not> _\<close> short_circuit_conv)
  apply (rewrite at \<open>let _ = the _ in _\<close> Let_def)
  unfolding
    maximum_level_removed_eq_count_dec_def[unfolded get_maximum_level_remove_def, symmetric]
  unfolding
    literals_to_update_wl_literals_to_update_wl_empty
    get_conflict_wl.simps get_trail_wl.simps
    maximum_level_removed_eq_count_dec_def[symmetric]
    is_decided_hd_trail_wl_def[symmetric]
    skip_and_resolve_loop_inv_def
    Multiset.is_empty_def[symmetric]
    get_maximum_level_remove_def[symmetric]
    literal_is_in_conflict_def[symmetric]
    lit_and_ann_of_propagated_st_def[symmetric]
    get_max_lvl_st_def[symmetric]
    count_decided_st_alt_def[symmetric]
    get_conflict_wl_get_conflict_wl_is_Nil
  by sepref (* slow *)

concrete_definition (in -) skip_and_resolve_loop_wl_D_code
  uses isasat_input_bounded_nempty.skip_and_resolve_loop_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) skip_and_resolve_loop_wl_D_code_def

lemmas skip_and_resolve_loop_wl_D_code_refine[sepref_fr_rules] =
   skip_and_resolve_loop_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin
term twl_st_assn
definition (in -) lit_of_hd_trail_st :: \<open>'v twl_st_wl \<Rightarrow> 'v literal\<close> where
  \<open> lit_of_hd_trail_st S = lit_of (hd (get_trail_wl S))\<close>

definition lit_of_hd_trail_st_heur :: \<open>twl_st_wl_heur_trail_ref \<Rightarrow> nat literal\<close> where
  \<open>lit_of_hd_trail_st_heur = (\<lambda>((M, _), _). lit_of (hd M))\<close>

lemma lit_of_hd_trail_st_heur_lit_of_hd_trail_st:
   \<open>(RETURN o lit_of_hd_trail_st_heur, RETURN o lit_of_hd_trail_st) \<in>
       [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>f twl_st_heur_pol \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: lit_of_hd_trail_st_def twl_st_heur_pol_def trail_pol_def
       lit_of_hd_trail_st_heur_def
      intro!: frefI nres_relI)

sepref_thm lit_of_hd_trail_st_code
  is \<open>RETURN o lit_of_hd_trail_st_heur\<close>
  :: \<open>[\<lambda>((M, _), _). M \<noteq> []]\<^sub>a twl_st_heur_pol_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_st_heur_def twl_st_heur_pol_assn_def
  by sepref

concrete_definition (in -) lit_of_hd_trail_st_code
   uses isasat_input_bounded_nempty.lit_of_hd_trail_st_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) lit_of_hd_trail_st_code_def

lemmas lit_of_hd_trail_st_code_refine_code[sepref_fr_rules] =
   lit_of_hd_trail_st_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem lit_of_hd_trail_st_code_lit_of_hd_trail_st[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_st_code, RETURN o lit_of_hd_trail_st)
    \<in> [\<lambda>S. get_trail_wl S \<noteq> []]\<^sub>a
      twl_st_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE twl_st_heur_pol (\<lambda>S. get_trail_wl S \<noteq> [])
        (\<lambda>_ ((M, _), _). M \<noteq> []) (\<lambda>_. True)]\<^sub>a
      hrp_comp (twl_st_heur_pol_assn\<^sup>k) twl_st_heur_pol \<rightarrow>
      hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_st_code_refine_code
    lit_of_hd_trail_st_heur_lit_of_hd_trail_st] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_heur_assn_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


definition (in -) extract_shorter_conflict_l_trivial :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v cconflict \<Rightarrow> 'v cconflict\<close> where
  \<open>extract_shorter_conflict_l_trivial M D = Some (filter_mset (\<lambda>L. get_level M L > 0) (the D))\<close>

definition (in -) extract_shorter_conflict_st_trivial :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
\<open>extract_shorter_conflict_st_trivial = (\<lambda>(M, N, U, D, NP, UP, Q, W).
  RETURN (M, N, U, extract_shorter_conflict_l_trivial M D, NP, UP, Q, W))\<close>

definition extract_shorter_conflict_st_trivial_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
  where
\<open>extract_shorter_conflict_st_trivial_heur = (\<lambda>(M, N, U, D, oth).
  RETURN (M, N, U, extract_shorter_conflict_l_trivial M D, oth))\<close>

definition extract_shorter_conflict_list_removed :: \<open>(nat, nat) ann_lits \<Rightarrow> conflict_option_rel \<Rightarrow>
  (conflict_option_rel \<times> (nat literal \<times> nat) option) nres\<close> where
\<open>extract_shorter_conflict_list_removed = (\<lambda>M (_, (n, xs)). do {
   (_, _, m, zs, L) \<leftarrow>
     WHILE\<^sub>T\<^bsup>\<lambda>(i, m', m, xs, L). i \<le> length xs \<and> m \<le> n \<and> i + 1 \<le> uint_max \<and> m \<ge> m'\<^esup>
       (\<lambda>(i, m', _). m' > 0)
       (\<lambda>(i, m', m, zs, L). do {
          ASSERT(i < length zs);
          ASSERT(m' > 0);
          case zs ! i of
            None \<Rightarrow> RETURN (i+1, m', m, zs, L)
          | Some b \<Rightarrow>  do {
               ASSERT(Pos i \<in> snd ` D\<^sub>0);
               let k = get_level_atm M i in
               if k > 0 then (* Keep *)
                 (case L of
                   None \<Rightarrow> RETURN (i+1, m' - 1, m, zs, Some (if b then Pos i else Neg i, k))
                 | Some (_, k') \<Rightarrow>
                   if k > k' then
                     RETURN (i + 1, m' - 1, m, zs, Some (if b then Pos i else Neg i, k))
                   else
                     RETURN (i + 1, m' - 1, m, zs, L))
               else (* delete *)
                 RETURN (i + 1, m' - 1, m - 1, zs[i := None], L)
            }
        })
     (0, n, n, xs, None);
    RETURN ((False, (m, zs)), L)
  })\<close>

definition highest_lit where
  \<open>highest_lit M C L \<longleftrightarrow>
     (L = None \<longrightarrow> C = {#}) \<and>
     (L \<noteq> None \<longrightarrow> get_level M (fst (the L)) = snd (the L) \<and>
        snd (the L) = get_maximum_level M C \<and>
        fst (the L) \<in># C
        )\<close>

lemma extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial:
  shows \<open>(uncurry extract_shorter_conflict_list_removed,
          uncurry (RETURN oo extract_shorter_conflict_l_trivial)) \<in>
      [\<lambda>(M', D). literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M = M']\<^sub>f Id \<times>\<^sub>f option_conflict_rel \<rightarrow>
         \<langle>{((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and> highest_lit M (the C) L \<and>
           (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}\<rangle> nres_rel\<close>
  (is \<open>?C \<in> [?pre]\<^sub>f _ \<times>\<^sub>f _ \<rightarrow> \<langle>?post\<rangle> nres_rel\<close>)
proof -
  have H: \<open>extract_shorter_conflict_list_removed M (b, n, xs)
       \<le> \<Down> ?post (RETURN (extract_shorter_conflict_l_trivial M (Some C)))\<close>
    if lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and ocr: \<open>((b, n, xs), Some C) \<in> option_conflict_rel\<close>
    for C b n xs
  proof -
    let ?C = \<open>\<lambda>M i C. filter_mset (\<lambda>L. atm_of L < i \<longrightarrow> get_level M L \<noteq> 0) C\<close>
    let ?D = \<open>\<lambda>M i C. filter_mset (\<lambda>L. atm_of L < i \<and> get_level M L \<noteq> 0) C\<close>
    define I' where
      \<open>I' = (\<lambda>(i, m', m, zs, L). highest_lit M (?D M i C) L \<and>
              ((False, (m, zs)), Some (?C M i C))
        \<in> option_conflict_rel \<and> (i < length zs \<longrightarrow> zs ! i \<noteq> None \<longrightarrow> Pos i \<in> snd ` D\<^sub>0) \<and>
        i + m' \<le> length zs \<and> length xs = length zs \<and>
        m' = size (filter_mset (\<lambda>L. atm_of L \<ge> i) C) \<and>
        (m' > 0 \<longrightarrow> i + m' + count_list (drop i zs) None = length xs) \<and>
        (m' > 0 \<longrightarrow> i \<le> uint_max div 2))\<close>
    have [simp]: \<open>b = False\<close>
      using ocr unfolding option_conflict_rel_def by auto
    have n: \<open>n = size C\<close> and map: \<open>mset_as_position xs C\<close>
      using ocr by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def)
    have \<open>xs ! i = None \<longleftrightarrow> Pos i \<notin># C \<and> Neg i \<notin># C\<close> if \<open>i < length xs\<close> for i
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos i\<close>] that
        mset_as_position_in_iff_nth[OF map, of \<open>Neg i\<close>]
      by (cases \<open>xs ! i\<close>) auto
    have xs_Some:
       \<open>xs ! i = Some y \<longleftrightarrow> (y \<longrightarrow> Pos i \<in># C) \<and> (\<not>y \<longrightarrow> Neg i \<in># C)\<close> if \<open>i < length xs\<close> for i y
      using mset_as_position_in_iff_nth[OF map, of \<open>Pos i\<close>] that
        mset_as_position_in_iff_nth[OF map, of \<open>Neg i\<close>]
      by (cases \<open>xs ! i\<close>) auto
    have n_ge_uint_max: \<open>n > uint_max div 2 \<Longrightarrow> {#L \<in># C. n \<le> atm_of L#} = {#}\<close> for n
      using lits in_N1_less_than_uint_max
      by (auto simp: filter_mset_empty_conv literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset nat_of_lit_def uint_max_def
          dest!: multi_member_split split: if_splits)
    define I where
      \<open>I n = (\<lambda>(i :: nat, m'::nat, m :: nat, xs :: bool option list, L:: (nat literal \<times> nat) option).
         i \<le> length xs \<and> m \<le> n \<and> i + 1 \<le> uint_max \<and> m \<ge> m')\<close>
      for n :: nat
    have I'_mapD: \<open>I' (i, m, n, xs, L) \<Longrightarrow>
         mset_as_position xs {#L \<in># C. \<not> (atm_of L < i \<and> get_level M L = 0)#}\<close>
      for i m n xs L
      unfolding I'_def option_conflict_rel_def conflict_rel_def by auto
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open> distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
       n_size: \<open>n = size C\<close>
      using mset_as_position_length_not_None[of xs C] that  mset_as_position_distinct_mset[of xs C]
        mset_as_position_tautology[of xs C]
      by (auto simp: option_conflict_rel_def conflict_rel_def)
    have init_I: \<open>I n (0, n, n, xs, None)\<close>
      using ocr lits unfolding I_def
      by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def uint_max_def
          mset_as_position_length_not_None[OF map] xs_Some literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
          dest!: multi_member_split[of _ C])
    have \<open>length xs - count_list xs None + count_list xs None = length xs\<close>
      using count_le_length[of xs None] by auto
    then have init_I': \<open>I' (0, n, n, xs, None)\<close>
      using ocr lits unfolding I'_def
      by (auto simp: conflict_rel_def highest_lit_def option_conflict_rel_def
          mset_as_position_length_not_None[OF map] xs_Some literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
          image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff removeAll_filter_not_eq[symmetric]
          length_removeAll_count_list uint_max_def
          dest!: multi_member_split[of _ C])
    have notin_I': "I' (ab + 1, ac, ad, ae, be)"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)" and
        I: "I aa s" and
        I': "I' s" and
        m: "case s of (i, m', uu) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)" and
        None: "ae ! ab = None"
      for ab ac ad ae be a ba aa baa s bb bc bd
    proof -
      have ab_le: \<open>ab < length ae\<close>
        using s I I' m unfolding I'_def I_def by auto
      have map: \<open>mset_as_position ae {#L \<in># C. \<not> (atm_of L < ab \<and> get_level M L = 0)#}\<close>
        using I'_mapD[OF I'[unfolded s]] .
      have Pos: \<open>Pos ab \<notin># C\<close> and Neg: \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] ab_le None
        mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>] by auto
      have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. ab < atm_of L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab#} =  {#L \<in># C. atm_of L < ab#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have [simp]: \<open>{#L \<in># C. ab < atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        apply (rule filter_mset_cong)
         apply (rule refl)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        done
      have 3: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos (Suc ab)\<close>] ab_le None
        mset_as_position_in_iff_nth[OF map, of \<open>Neg (Suc ab)\<close>] lits
        by (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset image_image
            in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
      have [simp]: \<open>{#L \<in># C. atm_of L < Suc ab \<and> 0 < get_level M L#} = {#L \<in># C. atm_of L < ab \<and> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L
          using Pos Neg by (cases L) (auto intro!: filter_mset_cong le_neq_implies_less)
        subgoal ..
        done
      have 4: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> uint_max div 2\<close>
        using n_ge_uint_max[of \<open>Suc ab\<close>] by (cases \<open>uint_max div 2 \<le> ab\<close>; auto simp: uint_max_def)
      have \<open>ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop ab ae) None =
           length ae\<close>
        using that xs_Some unfolding I'_def I_def by (auto simp: 3)
      then have \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
         length ae \<close>
        using Cons_nth_drop_Suc[symmetric, of ab ae] ab_le None by auto
      then show ?thesis
        using that xs_Some m unfolding I'_def I_def by (auto simp: 3 4)
    qed
    have in_I'_no_found: "I' (ab + 1, ac - 1, ad, ae, Some (if x then Pos ab else Neg ab, get_level M (Pos ab)))"
      if
        "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = None"
      for a ba aa baa s ab bb ac bc ad bd ae be x
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some (?L, get_level M (Pos ab)))\<close>
        using shl unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto

      have ab_uint_max: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> uint_max div 2\<close>
        using n_ge_uint_max[of \<open>Suc ab\<close>] by (cases \<open>uint_max div 2 \<le> ab\<close>; auto simp: uint_max_def)
      then show ?thesis
        using ab_le Some shl' ab_\<L>\<^sub>a\<^sub>l\<^sub>l ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_uint_max cond
        unfolding I'_def by auto
    qed
    have in_I'_found_upd: "I' (ab + 1, ac - 1, ad, ae,
          Some (if x then Pos ab else Neg ab, get_level M (Pos ab)))"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
          "xa = (af, bf)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = Some xa" and
        lev_bf: "bf < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x xa af bf
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "xa = (af, bf)"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some (?L, get_level M (Pos ab)))\<close>
        using shl lev_bf unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto
      have ab_uint_max: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> uint_max div 2\<close>
        using n_ge_uint_max[of \<open>Suc ab\<close>] by (cases \<open>uint_max div 2 \<le> ab\<close>; auto simp: uint_max_def)
      show ?thesis
        using ab_le Some shl' ab_\<L>\<^sub>a\<^sub>l\<^sub>l ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_uint_max
        unfolding I'_def
        by auto
    qed
    have in_I'_found_no_upd: "I' (ab + 1, ac - 1, ad, ae, be)"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
          "xa = (af, bf)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "0 < get_level M (Pos ab)" and
        [simp]: "be = Some xa" and
        lev_bf: "\<not> bf < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x xa af bf
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "xa = (af, bf)"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      then have 1: \<open>(?D M (Suc ab) C) =  add_mset ?L (?D M ab C)\<close>
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> \<open>\<lambda>L. ab = atm_of L \<and> 0 < get_level M L\<close> C,
            symmetric]
        lev_ab
        unfolding less_Suc_eq_le order.order_iff_strict filter_union_or_split conj_disj_distribR
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)

      have shl': \<open>highest_lit M (?D M (Suc ab) C) (Some xa)\<close>
        using shl lev_bf unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for x
          using lev_ab by (cases x) (auto simp: less_Suc_eq_le get_level_Neg_Pos)
        subgoal by (rule refl)
        done
      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have ocr': \<open>((False, ad, ae), Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}) \<in>
          option_conflict_rel\<close>
        using ocr unfolding ocr_e by fast
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto
      have ab_uint_max: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> uint_max div 2\<close>
        using n_ge_uint_max[of \<open>Suc ab\<close>] by (cases \<open>uint_max div 2 \<le> ab\<close>; auto simp: uint_max_def)
      show ?thesis
        using ab_le Some shl' ab_\<L>\<^sub>a\<^sub>l\<^sub>l ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_uint_max
        unfolding I'_def by auto
    qed
    have I'_in_remove: "I' (ab + 1, ac - 1, ad - 1, ae[ab := None], be)"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "case s of (i, m', uu_) \<Rightarrow> 0 < m'" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        Some: "ae ! ab = Some x" and
        "Pos ab \<in> snd ` D\<^sub>0" and
        ab_le: "ab < length ae" and
        lev_ab: "\<not> 0 < get_level M (Pos ab)"
      for a ba aa baa s ab bb ac bc ad bd ae be x
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        using s by auto
      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        ab_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        [simp]: "length baa = length ae" and
        ab_drop_ae: "ab + size {#L \<in># C. ab \<le> atm_of L#} + count_list (drop ab ae) None = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' ab_le Some cond unfolding I'_def
        by auto
      let ?L = \<open>if x then Pos ab else Neg ab\<close>
      have [iff]: \<open>(atm_of L < ab \<longrightarrow>
           get_level M L = 0 \<or> \<not> get_level M L < count_decided M) \<and>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M \<longleftrightarrow>
          atm_of L = ab \<and>
          0 < get_level M L \<and> get_level M L < count_decided M\<close> for L and ab :: nat
        by auto
      have Suc_D\<^sub>0: \<open>Suc ab < length ae \<Longrightarrow> ae ! Suc ab = Some y \<Longrightarrow> Pos (Suc ab) \<in> snd ` D\<^sub>0\<close> for y
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>if y then Pos (Suc ab) else Neg (Suc ab)\<close>]
          lits
        by (cases y) (auto simp: image_image in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset
            dest: multi_member_split)
      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto

      have 1: \<open>(?D M (Suc ab) C) =  (?D M ab C)\<close>
        apply (rule filter_mset_cong2)
        subgoal for L
          using lev_ab by (cases L) (auto simp: less_Suc_eq_le order.order_iff_strict get_level_Neg_Pos)
        subgoal ..
        done
      have shl': \<open>highest_lit M (?D M (Suc ab) C) be\<close>
        using shl unfolding 1 highest_lit_def
        by (auto simp: get_level_Neg_Pos get_maximum_level_add_mset)

      have \<open>?L \<in># C\<close>
        using mset_as_position_in_iff_nth[OF I'_mapD[OF I'[unfolded s]], of \<open>?L\<close>]
        Some ab_le by auto
      have ocr_e: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = add_mset ?L {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        apply (subst distinct_mset_add_mset_filter)
        subgoal using dist_C .
        subgoal using \<open>?L \<in># C\<close> .
        subgoal using lev_ab by (auto simp: get_level_Neg_Pos)
        apply (rule filter_mset_cong2)
        subgoal for L
          using lev_ab \<open>?L \<in># C\<close> tauto_C by (cases L) (auto simp: less_Suc_eq_le)
        subgoal ..
        done

      have ac_0: \<open>ac > 0\<close>
        using cond by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} - {#Pos ab, Neg ab#} =
         {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#}\<close>
        using lev_ab unfolding ocr_e by (auto simp: get_level_Neg_Pos)

      have ocr': \<open>((False, ad - Suc 0, ae[ab := None]),
           Some {#L \<in># C. atm_of L < Suc ab \<longrightarrow> 0 < get_level M L#})
         \<in> option_conflict_rel\<close>
        using ocr ab_le \<open>?L \<in># C\<close> tauto_C
        mset_as_position_remove[OF I'_mapD[OF I'[unfolded s]], of \<open>atm_of ?L\<close>]
        unfolding option_conflict_rel_def conflict_rel_def ocr_e by (cases x) auto
      have ab_ac_0: \<open>Suc (ab + (ac - Suc 0)) \<le> length ae\<close>
        using ac_0 ab_drop_ae ac by auto
      have [iff]: \<open> ab \<noteq> atm_of L \<and> Suc ab \<le> atm_of L \<longleftrightarrow> Suc ab \<le> atm_of L \<close> for L
        by auto
      have le_Suc: \<open>a \<le> n \<longleftrightarrow> a = n \<or> Suc a \<le> n\<close> for a n :: nat
        by auto
      have 1: \<open>add_mset ?L  {#L \<in># C. Suc ab \<le> atm_of L#} =  {#L \<in># C. ab \<le> atm_of L#}\<close>
        apply (subst (2) le_Suc)
        unfolding filter_union_or_split conj_disj_distribR
        using dist_C tauto_C filter_mset_cong_inner_outer[of \<open>{#?L#}\<close>
            \<open>\<lambda>L. Suc ab = atm_of L\<close> \<open>\<lambda>L. Suc ab = atm_of L\<close> C,
            symmetric]
        lev_ab \<open>?L \<in># C\<close>
        by (auto split: if_splits dest!: multi_member_split
            simp: lev_ab tautology_add_mset filter_mset_empty_conv get_level_Neg_Pos)
      have ac_size: \<open>ac - Suc 0 = size {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ac_0 ac 1[symmetric] by auto
      have Suc_ab_drop_ae: \<open>Suc (ab + size {#L \<in># C. Suc ab \<le> atm_of L#} + count_list (drop (Suc ab) ae) None) =
        length ae\<close>
        using ab_drop_ae 1[symmetric] Cons_nth_drop_Suc[OF ab_le, symmetric] Some by auto

      have ab_uint_max: \<open>0 < size {#L \<in># C. Suc ab \<le> atm_of L#} \<Longrightarrow> Suc ab \<le> uint_max div 2\<close>
        using n_ge_uint_max[of \<open>Suc ab\<close>] by (cases \<open>uint_max div 2 \<le> ab\<close>; auto simp: uint_max_def)
      show ?thesis
        using ab_le Some shl' ab_\<L>\<^sub>a\<^sub>l\<^sub>l ocr' ab_ac_0 ac_size Suc_ab_drop_ae Suc_D\<^sub>0 ab_uint_max
        unfolding I'_def by auto
    qed
    have final: "(((False, ad, ae), be), Some {#L \<in># the (Some C). 0 < get_level M L#})
      \<in> {((D, L), C).
          (D, C) \<in> option_conflict_rel \<and>
          C \<noteq> None \<and> highest_lit M (the C) L \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}"
      if
        I: "I aa s" and
        I': "I' s" and
        cond: "\<not> (case s of (i, m', uu_) \<Rightarrow> 0 < m')" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "bd = (ae, be)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
      for a ba aa baa s ab bb ac bc ad bd ae be
    proof -
      have [simp]:
        "s = (ab, ac, ad, ae, be)"
        "bb = (ac, ad, ae, be)"
        "bc = (ad, ae, be)"
        "bd = (ae, be)"
        "ba = (aa, baa)"
        "\<not> a"
        "n = aa"
        "xs = baa"
        "ac = 0"
        using s cond by auto

      have
        shl: "highest_lit M (?D M ab C) be" and
        ocr: "((False, ad, ae), Some {#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#}) \<in> option_conflict_rel" and
        [simp]: "length baa = length ae" and
        ac: "ac = size {#L \<in># C. ab \<le> atm_of L#}"
        using I' unfolding I'_def
        by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<longrightarrow> 0 < get_level M L#} = {#L \<in># C. 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L using ac by (auto simp: filter_mset_empty_conv)
        subgoal by (rule refl)
        done
      have [simp]: \<open>{#L \<in># C. atm_of L < ab \<and> 0 < get_level M L#} = {#L \<in># C. 0 < get_level M L#}\<close>
        apply (rule filter_mset_cong2)
        subgoal for L using ac by (auto simp: filter_mset_empty_conv)
        subgoal by (rule refl)
        done
      have le_ae: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length ae\<close>
        using I I' ocr unfolding I'_def option_conflict_rel_def conflict_rel_def
        by auto
      show ?thesis
        using ocr shl le_ae by auto
    qed
    show ?thesis
      unfolding extract_shorter_conflict_list_removed_def extract_shorter_conflict_l_trivial_def
        I_def[symmetric]
      apply (refine_vcg
         WHILEIT_rule_stronger_inv[where R=\<open>measure (\<lambda>(i, _). Suc (length xs) - i)\<close> and
           I' = I'])
      subgoal by auto
      subgoal using init_I by auto
      subgoal using init_I' by auto
      subgoal unfolding I'_def I_def by auto
      subgoal by auto
      subgoal unfolding I'_def I_def uint_max_def by auto
      subgoal by (rule notin_I')
      subgoal unfolding I'_def by auto
      subgoal unfolding I'_def by auto
      subgoal by (auto simp: I'_def I_def uint_max_def)
      subgoal unfolding get_level_atm_def by (rule in_I'_no_found)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def uint_max_def I'_def by auto
      subgoal unfolding get_level_atm_def by (rule in_I'_found_upd)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def I'_def uint_max_def by auto
      subgoal unfolding get_level_atm_def by (rule in_I'_found_no_upd)
      subgoal unfolding I'_def by auto
      subgoal unfolding I_def I'_def uint_max_def by auto
      subgoal unfolding get_level_atm_def by (rule I'_in_remove)
      subgoal unfolding I'_def by auto
      subgoal by (rule final)
      done
  qed
  then show ?thesis
    unfolding uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply auto
    done
qed

definition extract_shorter_conflict_list where
  \<open>extract_shorter_conflict_list = (\<lambda>M C. do {
     let K = lit_of (hd M);
     let C = Some (remove1_mset (-K) (the C));
     let C = extract_shorter_conflict_l_trivial M C;
     RETURN (map_option (add_mset (-K)) C)
  })\<close>

definition extract_shorter_conflict_list_heur where
  \<open>extract_shorter_conflict_list_heur = (\<lambda>M (b, (n, xs)). do {
     let K = lit_of (hd M);
     ASSERT(atm_of K < length xs);
     ASSERT(n \<ge> 1);
     let xs = xs[atm_of K := None];
     ((b, (n, xs)), L) \<leftarrow> extract_shorter_conflict_list_removed M (b, (n - 1, xs));
     ASSERT(atm_of K < length xs);
     ASSERT(n + 1 \<le> uint_max);
     RETURN ((b, (n + 1, xs[atm_of K := Some (is_neg K)])), L)
  })\<close>


lemma extract_shorter_conflict_list_extract_shorter_conflict_l_trivial_spec:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and> (\<exists>y. ba = Some y) \<and> ((a, aa, b), ba) \<in> option_conflict_rel \<and> M = M' \<Longrightarrow>
    extract_shorter_conflict_list_removed M (a, aa, b) \<le> \<Down> {((D, L), C).
      (D, C) \<in> option_conflict_rel \<and> (\<exists>y. C = Some y) \<and> highest_lit M (the C) L \<and>
      (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}
    (RETURN (extract_shorter_conflict_l_trivial M' ba))\<close>
  apply simp
    apply (rule extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial[
        unfolded fref_def nres_rel_def, simplified, rule_format])
  by fast

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_sub:
  \<open>literals_are_in_\<L>\<^sub>i\<^sub>n y \<Longrightarrow> literals_are_in_\<L>\<^sub>i\<^sub>n (y - z)\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of y \<open>y - z\<close>] by auto

lemma extract_shorter_conflict_l_trivial_subset_msetD:
  \<open>extract_shorter_conflict_l_trivial M (Some (remove1_mset (- lit_of (hd M)) D)) = Some D' \<Longrightarrow> D' \<subseteq># D\<close>
  apply (auto simp: extract_shorter_conflict_l_trivial_def)
  by (metis Diff_eq_empty_iff_mset diff_le_mono2_mset diff_subset_eq_self diff_zero multiset_filter_subset)

lemma extract_shorter_conflict_list_heur_extract_shorter_conflict_list:
  \<open>(uncurry extract_shorter_conflict_list_heur, uncurry extract_shorter_conflict_list)
   \<in> [\<lambda>(M', D). literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>  - lit_of (hd M) \<in># the D \<and>
         lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and> get_level M (lit_of (hd M)) > 0 \<and>
          \<not>tautology (the D)]\<^sub>f
      Id \<times>\<^sub>f option_conflict_rel \<rightarrow>
       \<langle>{((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and>
          highest_lit M (remove1_mset (-lit_of (hd M)) (the C)) L \<and>
          (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}\<rangle>nres_rel\<close>
  supply extract_shorter_conflict_list_removed_extract_shorter_conflict_l_trivial[refine_vcg]
  unfolding extract_shorter_conflict_list_def extract_shorter_conflict_list_heur_def uncurry_def
  apply (intro frefI nres_relI)
  apply clarify
  apply refine_rcg
  subgoal
    by (cases M)
      (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
        literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        dest: multi_member_split)
  unfolding conc_fun_RETURN[symmetric]
   apply (rule extract_shorter_conflict_list_extract_shorter_conflict_l_trivial_spec)
  subgoal for a aa ab b ac ba y
    using mset_as_position_remove[of b y \<open>atm_of (- lit_of (hd M))\<close>]
    apply (cases \<open>lit_of (hd M)\<close>)
    apply (auto intro!: ASSERT_refine_left
        simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
        size_remove1_mset_If minus_notin_trivial2 minus_notin_trivial)
    done
  subgoal for M' b n zs ac ba D x' x1 x1a x2 x1b x2a L
    apply (auto intro!: ASSERT_refine_left)
    subgoal
      apply (cases M)
       apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
      done
    subgoal for D'
      using simple_clss_size_upper_div2[of D'] literals_are_in_\<L>\<^sub>i\<^sub>n_mono[of D D']
        distinct_mset_mono[of D' D] not_tautology_mono[of D' D]
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff uint_max_def
          dest!: extract_shorter_conflict_l_trivial_subset_msetD)
    subgoal
      by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_sub option_conflict_rel_def conflict_rel_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff is_pos_neg_not_is_pos
          extract_shorter_conflict_l_trivial_def
          intro!: mset_as_position.add
          dest!: multi_member_split[of _ D])
    done
  done

abbreviation extract_shorter_conflict_l_trivial_pre where
\<open>extract_shorter_conflict_l_trivial_pre \<equiv> \<lambda>(M, D). literals_are_in_\<L>\<^sub>i\<^sub>n (mset (fst D))\<close>

definition (in -) lit_of_hd_trail where
  \<open>lit_of_hd_trail M = lit_of (hd M)\<close>

definition (in -) lit_of_hd_trail_pol where
  \<open>lit_of_hd_trail_pol = (\<lambda>(M, _). lit_of (hd M))\<close>

lemma lit_of_hd_trail_pol_lit_of_hd_trail:
   \<open>(RETURN o lit_of_hd_trail_pol, RETURN o lit_of_hd_trail) \<in>
         [\<lambda>S. S \<noteq> []]\<^sub>f trail_pol \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
   by (auto simp: lit_of_hd_trail_def trail_pol_def lit_of_hd_trail_pol_def
      intro!: frefI nres_relI)

sepref_definition (in -) lit_of_hd_trail_code
  is \<open>RETURN o lit_of_hd_trail_pol\<close>
  :: \<open>[\<lambda>(M, _). M \<noteq> []]\<^sub>a trail_pol_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding lit_of_hd_trail_pol_def
  by sepref

theorem lit_of_hd_trail_code_lit_of_hd_trail[sepref_fr_rules]:
  \<open>(lit_of_hd_trail_code, RETURN o lit_of_hd_trail)
    \<in> [\<lambda>S. S \<noteq> []]\<^sub>a trail_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE trail_pol (\<lambda>S. S \<noteq> []) (\<lambda>_ (M, _). M \<noteq> [])
     (\<lambda>_. True)]\<^sub>a hrp_comp (trail_pol_assn\<^sup>k)
                     trail_pol \<rightarrow> hr_comp unat_lit_assn Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF lit_of_hd_trail_code.refine
      lit_of_hd_trail_pol_lit_of_hd_trail] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_heur_assn_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_register extract_shorter_conflict_list_removed
sepref_register extract_shorter_conflict_l_trivial

type_synonym (in -) conflict_rel_with_cls_with_highest =
  \<open>conflict_option_rel \<times> (nat literal \<times> nat)option\<close>

definition option_conflict_rel_with_cls_with_highest2
  :: \<open>nat literal \<Rightarrow> (nat, 'a) ann_lits \<Rightarrow> (conflict_rel_with_cls_with_highest \<times> nat clause option) set\<close> where
  \<open>option_conflict_rel_with_cls_with_highest2 K M = {(((b, xs), L), D).
     D \<noteq> None \<and> ((b, xs), D) \<in> option_conflict_rel \<and> highest_lit M (remove1_mset K (the D)) L \<and>
     (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd xs))}\<close>

abbreviation option_conflict_rel_with_cls_with_highest where
  \<open>option_conflict_rel_with_cls_with_highest M \<equiv> option_conflict_rel_with_cls_with_highest2 (-lit_of (hd M)) M\<close>

lemmas option_conflict_rel_with_cls_with_highest_def = option_conflict_rel_with_cls_with_highest2_def

type_synonym (in -) conflict_with_cls_with_highest_assn =
   \<open>conflict_option_assn \<times> (uint32 \<times> uint32) option\<close>

abbreviation conflict_with_cls_int_with_highest_assn
 :: \<open>conflict_rel_with_cls_with_highest \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_with_highest_assn \<equiv>
    (bool_assn *assn uint32_nat_assn *assn array_assn (option_assn bool_assn)) *assn option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>

definition conflict_with_cls_with_cls_with_highest_assn
  :: \<open>(nat, 'a) ann_lits \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_with_highest_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_with_cls_with_highest_assn M \<equiv>
    hr_comp conflict_with_cls_int_with_highest_assn (option_conflict_rel_with_cls_with_highest M)\<close>

lemma extract_shorter_conflict_list_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_list, uncurry (RETURN oo extract_shorter_conflict_l_trivial)) \<in>
  [\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> -lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M))]\<^sub>f
   Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: extract_shorter_conflict_list_def extract_shorter_conflict_l_trivial_def
      Let_def)

type_synonym (in -) twl_st_wl_confl_extracted_int =
  \<open>(nat,nat)ann_lits \<times> nat clause_l list \<times> nat \<times>
    conflict_rel_with_cls_with_highest \<times> nat lit_queue_wl \<times> nat list list \<times> vmtf_remove_int \<times>
    bool list \<times> nat\<close>

definition twl_st_heur_confl_extracted2
  :: \<open>nat literal \<Rightarrow> (twl_st_wl_confl_extracted_int \<times> twl_st_wl_heur) set\<close> where
\<open>twl_st_heur_confl_extracted2 L =
  {((M', N', U', D', Q', W', vm', \<phi>', clvls), (M, N, U, D, Q, W, vm, \<phi>, clvls')).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest2 L M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi> \<and>
    clvls' = clvls
  }\<close>

definition twl_st_heur_confl_extracted :: \<open>(twl_st_wl_confl_extracted_int \<times> twl_st_wl_heur) set\<close> where
\<open>twl_st_heur_confl_extracted =
  {((M', N', U', D', Q', W', vm', \<phi>', clvls'), (M, N, U, D, Q, W, vm, \<phi>, clvls)).
    M = M' \<and> N' = N \<and> U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
    W' = W \<and>
    vm = vm' \<and>
    \<phi>' = \<phi> \<and>
    clvls' = clvls
  }\<close>

type_synonym (in -) twl_st_wll_trail_confl_extracted =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_with_highest_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn \<times> uint32\<close>


definition twl_st_confl_extracted_int_assn
  :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close> where
\<open>twl_st_confl_extracted_int_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_with_cls_int_with_highest_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc *assn
  uint32_nat_assn
  )\<close>

definition (in isasat_input_ops) twl_st_heur_no_clvls :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_no_clvls =
  {((M', N', U', D', Q', W', vm, \<phi>, clvls), (M, N, U, D, NP, UP, Q, W)).
    M = M' \<and> N' = N \<and> U' = U \<and>
    D' = D \<and>
     Q' = Q \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
    vm \<in> vmtf M \<and>
    phase_saving \<phi> \<and>
    no_dup M
  }\<close>

definition twl_st_confl_extracted_assn
  :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_heur_confl_extracted O twl_st_heur_no_clvls)\<close>

definition twl_st_confl_extracted_assn2
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> twl_st_wll_trail_confl_extracted \<Rightarrow> assn\<close>
  where
\<open>twl_st_confl_extracted_assn2 L = hr_comp twl_st_confl_extracted_int_assn
  (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls)\<close>

lemma extract_shorter_conflict_st_trivial_heur_alt_def:
  \<open>extract_shorter_conflict_st_trivial_heur = (\<lambda>(M, N, U, D, oth).
  RETURN (M, N, U, ASSN_ANNOT (conflict_with_cls_with_cls_with_highest_assn M)
     (extract_shorter_conflict_l_trivial M D), oth))\<close>
  unfolding extract_shorter_conflict_st_trivial_heur_def ASSN_ANNOT_def ..

definition extract_shorter_conflict_list_st_int:: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> _ nres\<close> where
  \<open>extract_shorter_conflict_list_st_int = (\<lambda>(M, N, U, D, oth). do {
     D \<leftarrow> extract_shorter_conflict_list_heur M D;
     RETURN (M, N, U, D, oth)})
\<close>

definition extract_shorter_conflict_list_st where
  \<open>extract_shorter_conflict_list_st =
     (\<lambda>(M, N, U, D, oth). do {
        D \<leftarrow> extract_shorter_conflict_list M D;
        RETURN (M, N, U, D, oth)})\<close>

lemma extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial:
  \<open>(extract_shorter_conflict_list_st, extract_shorter_conflict_st_trivial) \<in>
     [\<lambda>S. get_trail_wl S \<noteq> [] \<and> -lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
         get_conflict_wl S \<noteq> None \<and> get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) > 0]\<^sub>f
     Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding extract_shorter_conflict_list_st_def extract_shorter_conflict_st_trivial_def
  extract_shorter_conflict_list_def
  by (intro frefI nres_relI)
    (auto simp: Let_def extract_shorter_conflict_l_trivial_def)

lemma extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_heur:
  \<open>(extract_shorter_conflict_list_st_int, extract_shorter_conflict_st_trivial_heur) \<in>
     [\<lambda>S. get_conflict_wl_heur S \<noteq> None \<and> get_trail_wl_heur S \<noteq> [] \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
         -lit_of (hd (get_trail_wl_heur S)) \<in># the (get_conflict_wl_heur S) \<and>
         0 < get_level (get_trail_wl_heur S) (lit_of (hd (get_trail_wl_heur S))) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl_heur S)) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
         distinct_mset (the (get_conflict_wl_heur S)) \<and> \<not>tautology (the (get_conflict_wl_heur S))]\<^sub>f
      (twl_st_wl_heur_lookup_conflict_rel) \<rightarrow> \<langle>twl_st_heur_confl_extracted\<rangle>nres_rel\<close>
proof -
  have H: \<open>a \<noteq> [] \<Longrightarrow>
   - lit_of (hd a) \<in># the ac \<Longrightarrow>
   (\<exists>y. ac = Some y) \<Longrightarrow> 0 < get_level a (lit_of (hd a)) \<Longrightarrow>
   extract_shorter_conflict_list_st (a, aa, ab, ac, ad, ae, af, b)
       \<le> \<Down> Id (RETURN (a, aa, ab, extract_shorter_conflict_l_trivial a ac, ad, ae, af, b))\<close>
    for a :: \<open>(nat, nat) ann_lits\<close> and aa :: \<open>nat clauses_l\<close> and
          ab :: nat and ac and ad ae :: \<open>nat clauses\<close> and af :: \<open>nat clause\<close> and
          b ::\<open>nat literal \<Rightarrow> nat list\<close>
    using extract_shorter_conflict_list_st_extract_shorter_conflict_st_trivial[unfolded fref_def
      extract_shorter_conflict_st_trivial_def nres_rel_def, simplified, rule_format,
      of a ac aa ab ad ae af b] by auto
  have H':
    \<open>M \<noteq> [] \<and>
     (\<exists>y. ba = Some y) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and>
     M \<noteq> [] \<and>
     literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
     - lit_of (hd M) \<in># the ba \<and>
     lit_of (hd M) \<notin># the ba \<and>
     distinct_mset (the ba) \<and>
     0 < get_level M (lit_of (hd M)) \<and>
     \<not> tautology (the ba) \<and>
     ((a, aa, b), ba) \<in> option_conflict_rel \<Longrightarrow>
     extract_shorter_conflict_list_heur M (a, aa, b)
     \<le> \<Down> {((D, L), C).
           (D, C) \<in> option_conflict_rel \<and>
           (\<exists>y. C = Some y) \<and>
           highest_lit M
            (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
           (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))}
         (RETURN (extract_shorter_conflict_l_trivial M ba))\<close> for a aa b ba M
    using extract_shorter_conflict_list_heur_extract_shorter_conflict_list
       [FCOMP extract_shorter_conflict_list_extract_shorter_conflict_l_trivial,
         unfolded fref_def
            extract_shorter_conflict_st_trivial_def nres_rel_def, of M] by auto
  show ?thesis
    apply (intro nres_relI frefI)
    subgoal for S' S
      apply (cases S; cases S')
      apply (auto simp: extract_shorter_conflict_list_st_int_def
          extract_shorter_conflict_st_trivial_heur_def twl_st_wl_heur_lookup_conflict_rel_def)
    apply (rule intro_bind_refine[OF H', of _ \<open>get_conflict_wl_heur S\<close>])
    subgoal by auto
    subgoal
      by (auto simp: twl_st_heur_confl_extracted_def option_conflict_rel_with_cls_with_highest_def)
    done
  done
qed


fun get_trail_wl_heur_conflict :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> (nat,nat) ann_lits\<close> where
  \<open>get_trail_wl_heur_conflict (M, N, U, D, _) = M\<close>

lemma extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl:
  \<open>(extract_shorter_conflict_st_trivial, extract_shorter_conflict_wl) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
      get_conflict_wl S \<noteq> None \<and> no_skip S \<and> no_resolve S \<and> get_conflict_wl S \<noteq> Some {#}]\<^sub>f
    Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>extract_shorter_conflict_st_trivial S \<le>  (extract_shorter_conflict_wl S)\<close>
    if
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close>
      (is \<open>twl_struct_invs ?S\<close>) and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
      D: \<open>get_conflict_wl S \<noteq> None\<close> \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
      n_s_s: \<open>no_skip S\<close> and
      n_s_r: \<open>no_resolve S\<close>
    for S
  proof -
    obtain M N U D NP UP Q W where
      [simp]: \<open>S = (M, N, U, D, NP, UP, Q, W)\<close>
      by (cases S)
    have
      learned: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of ?S)\<close> and
      confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of ?S)\<close>
      using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>M \<Turnstile>as CNot (the D)\<close>
      using confl D unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    then have M_nempty: \<open>M ~= []\<close>
      using D by auto
    have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) \<Turnstile>p the D\<close>
      using that(2-) learned
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    moreover have \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of ?S) \<Turnstile>pm
        filter_mset (\<lambda>L. get_level (trail (state\<^sub>W_of ?S)) L > 0) (the (conflicting (state\<^sub>W_of ?S)))\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(1))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto)
      subgoal using D by (auto)
      subgoal using M_nempty by (cases M, auto)
      done
    moreover have \<open>- lit_of (cdcl\<^sub>W_restart_mset.hd_trail (state\<^sub>W_of ?S)) \<in>#
      {#L \<in># the (conflicting (state\<^sub>W_of ?S)). 0 < get_level (trail (state\<^sub>W_of ?S)) L#}\<close>
      apply (rule cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2))
      subgoal using n_s_s unfolding no_skip_def by fast
      subgoal using n_s_r unfolding no_resolve_def by fast
      subgoal using stgy_invs unfolding twl_stgy_invs_def by fast
      subgoal using struct_invs unfolding twl_struct_invs_def by fast
      subgoal using D by (auto)
      subgoal using D by (auto)
      subgoal using M_nempty by (cases M, auto)
      done
    moreover have \<open>mset ` set (take U (tl N)) \<union> set_mset NP \<union>
        (mset ` set (drop (Suc U) N) \<union> set_mset UP) =
          mset ` set (tl N) \<union> set_mset NP \<union> set_mset UP\<close>
      apply (subst (2) append_take_drop_id[of U \<open>tl N\<close>, symmetric])
      unfolding set_append drop_Suc
      by auto
    ultimately show ?thesis
      using that(2-) D M_nempty
      by (auto simp: clauses_def mset_take_mset_drop_mset'
          extract_shorter_conflict_st_trivial_def extract_shorter_conflict_wl_def
          extract_shorter_conflict_l_trivial_def)
  qed
  show ?thesis
    by (intro frefI nres_relI) (auto intro!: H)
qed

definition find_decomp_wl_imp :: "(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> nat literal \<Rightarrow> vmtf_remove_int \<Rightarrow>
   ((nat, nat) ann_lits \<times> vmtf_remove_int) nres" where
  \<open>find_decomp_wl_imp = (\<lambda>M\<^sub>0 D L vm. do {
    let lev = get_maximum_level M\<^sub>0 (remove1_mset (-L) (the D));
    let k = count_decided M\<^sub>0;
    (_, M, vm') \<leftarrow>
       WHILE\<^sub>T\<^bsup>\<lambda>(j, M, vm'). j = count_decided M \<and> j \<ge> lev \<and>
           (M = [] \<longrightarrow> j = lev) \<and>
           (\<exists>M'. M\<^sub>0 = M' @ M \<and> (j = lev \<longrightarrow> M' \<noteq> [] \<and> is_decided (last M'))) \<and>
           vm' \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M)\<^esup>
         (\<lambda>(j, M, vm). j > lev)
         (\<lambda>(j, M, vm). do {
            ASSERT(M \<noteq> []);
            if is_decided (hd M)
            then let L = atm_of (lit_of (hd M)) in RETURN (j-1, tl M, vmtf_unset L vm)
            else let L = atm_of (lit_of (hd M)) in RETURN (j, tl M, vmtf_unset L vm)}
         )
         (k, M\<^sub>0, vm);
    RETURN (M, vm')
  })\<close>


definition find_decomp_wl_imp_pre where
  \<open>find_decomp_wl_imp_pre = (\<lambda>(((M, D), L), vm). M \<noteq> [] \<and> D \<noteq> None \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> -L \<in># the D \<and>
      literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> vm \<in> vmtf M)\<close>

definition (in -) get_maximum_level_remove_int :: \<open>(nat, 'a) ann_lits \<Rightarrow>
    conflict_rel_with_cls_with_highest \<Rightarrow> nat literal \<Rightarrow>  nat\<close> where
  \<open>get_maximum_level_remove_int = (\<lambda>_ (_, D) _.
    (case D of None \<Rightarrow> 0 | Some i \<Rightarrow> snd i))\<close>

sepref_thm get_maximum_level_remove_code
  is \<open>uncurry2 (RETURN ooo get_maximum_level_remove_int)\<close>
  :: \<open>trail_assn\<^sup>k  *\<^sub>a conflict_with_cls_int_with_highest_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a
       uint32_nat_assn\<close>
  supply uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
    snd_hnr_pure[sepref_fr_rules]
  unfolding get_maximum_level_remove_int_def zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) get_maximum_level_remove_code
   uses isasat_input_bounded_nempty.get_maximum_level_remove_code.refine_raw
   is \<open>(uncurry2 ?f,_)\<in>_\<close>

prepare_code_thms (in -) get_maximum_level_remove_code_def

lemmas get_maximum_level_remove_code_hnr[sepref_fr_rules] =
   get_maximum_level_remove_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in -) get_maximum_level_remove' where
  \<open>get_maximum_level_remove' M D L = get_maximum_level_remove M (the D) L\<close>

lemma (in -)get_maximum_level_remove_single_removed[simp]: \<open>get_maximum_level_remove M {#L#} L = 0\<close>
  unfolding get_maximum_level_remove_def by auto

lemma (in -) get_maximum_level_remove_empty[simp]: \<open>get_maximum_level_remove M {#} = (\<lambda>_. 0)\<close>
 unfolding get_maximum_level_remove_def by auto

lemma get_maximum_level_remove_int_get_maximum_level_remove':
  \<open>(uncurry2 (RETURN ooo get_maximum_level_remove_int), uncurry2 (RETURN ooo get_maximum_level_remove')) \<in>
     [\<lambda>((M', D), L). M' = M \<and> L = -lit_of (hd M) \<and> M' \<noteq> [] \<and> D \<noteq> None]\<^sub>f Id \<times>\<^sub>f (option_conflict_rel_with_cls_with_highest M) \<times>\<^sub>f Id \<rightarrow>
    \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: get_maximum_level_remove_int_def get_maximum_level_remove'_def
      option_conflict_rel_with_cls_with_highest_def highest_lit_def
      get_maximum_level_remove_def[symmetric] remove1_mset_empty_iff
      split: option.splits)

lemma get_maximum_level_remove'_hnr[sepref_fr_rules]:
  \<open>(uncurry2 get_maximum_level_remove_code, uncurry2 (RETURN \<circ>\<circ>\<circ> get_maximum_level_remove'))
     \<in> [\<lambda>((a, b), ba). a = M \<and> ba = - lit_of (hd M) \<and> a \<noteq> [] \<and> b \<noteq> None]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
   uint32_nat_assn\<close>
  using get_maximum_level_remove_code_hnr[FCOMP get_maximum_level_remove_int_get_maximum_level_remove']
  unfolding conflict_with_cls_with_cls_with_highest_assn_def[symmetric] by simp

sepref_register find_decomp_wl_imp
sepref_thm find_decomp_wl_imp_code
  is \<open>uncurry3 (PR_CONST find_decomp_wl_imp)\<close>
  :: \<open>[\<lambda>(((M', D), L), vm). M' = M \<and> L = lit_of (hd M') \<and> M' \<noteq> [] \<and> find_decomp_wl_imp_pre (((M', D), L), vm)]\<^sub>a
         trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d
    \<rightarrow> trail_assn *assn vmtf_remove_conc\<close>
  unfolding find_decomp_wl_imp_def get_maximum_level_remove_def[symmetric] PR_CONST_def
    find_decomp_wl_imp_pre_def get_maximum_level_remove'_def[symmetric]
  supply [[goals_limit=1]]   literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset[simp]
  supply uint32_nat_assn_one[sepref_fr_rules]
  supply uint32_nat_assn_minus[sepref_fr_rules]
  by sepref

concrete_definition (in -) find_decomp_wl_imp_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp_code.refine_raw
   is \<open>(uncurry3 ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp_code_def

lemmas find_decomp_wl_imp_code[sepref_fr_rules] =
   find_decomp_wl_imp_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

abbreviation (in -) nat_lit_lit_rel where
  \<open>nat_lit_lit_rel \<equiv> Id :: (nat literal \<times> _) set\<close>

definition find_decomp_wvmtf_ns  where
  \<open>find_decomp_wvmtf_ns =
     (\<lambda>(M::(nat, nat) ann_lits) (D::nat clause option) (L::nat literal) _.
        SPEC(\<lambda>(M1, vm). \<exists>K M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (the D - {#-L#}) + 1 \<and> vm \<in> vmtf M1))\<close>


definition (in -) find_decomp_wl_st :: \<open>nat literal \<Rightarrow> nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>find_decomp_wl_st = (\<lambda>L (M, N, U, D, oth).  do{
     M' \<leftarrow> find_decomp_wl' M (the D) L;
    RETURN (M', N, U, D, oth)
  })\<close>

definition find_decomp_wl_st_int :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow>
    twl_st_wl_heur nres\<close> where
  \<open>find_decomp_wl_st_int = (\<lambda>L (M, N, U, D, W, Q, vm, \<phi>).  do{
     (M', vm) \<leftarrow> find_decomp_wvmtf_ns M D L vm;
    RETURN (M', N, U, D, W, Q, vm, \<phi>)
  })\<close>


lemma
  assumes
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W))\<close> and
    D: \<open>D \<noteq> None\<close> \<open>E \<noteq> None\<close> \<open>the E \<noteq> {#}\<close> and M\<^sub>0: \<open>M\<^sub>0 \<noteq> []\<close> and ex_decomp: \<open>ex_decomp_of_max_lvl M\<^sub>0 D L\<close> and
    L: \<open>L = lit_of (hd M\<^sub>0)\<close> and
    E_D\<^sub>0: \<open>the E \<subseteq># the D\<close> and
    D\<^sub>0: \<open>D \<noteq> None\<close> and
   vm: \<open>vm \<in> vmtf M\<^sub>0\<close> and
   lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M\<^sub>0)\<close>
  shows
    find_decomp_wl_imp_le_find_decomp_wl':
      \<open>find_decomp_wl_imp M\<^sub>0 E L vm \<le> find_decomp_wvmtf_ns M\<^sub>0 E L vm\<close>
     (is ?decomp)
proof -
  have 1: \<open>((count_decided x1g, x1g), count_decided x1, x1) \<in> Id\<close>
    if \<open>x1g = x1\<close> for x1g x1 :: \<open>(nat, nat) ann_lits\<close>
    using that by auto
  have [simp]: \<open>\<exists>M'a. M' @ x2g = M'a @ tl x2g\<close> for M' x2g :: \<open>'a list\<close>
    by (metis append.assoc append_Cons append_Nil list.exhaust list.sel(3) tl_Nil)
  have butlast_nil_iff: \<open>butlast xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>a. xs = [a])\<close> for xs :: \<open>(nat, nat) ann_lits\<close>
    by (cases xs) auto
  have butlast1: \<open>tl x2g = drop (Suc (length x1) - length x2g) x1\<close> (is \<open>?G1\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that zero_le)
    show ?G1
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  have butlast2: \<open>tl x2g = drop (length x1 - (length x2g - Suc 0)) x1\<close> (is \<open>?G2\<close>)
    if \<open>x2g = drop (length x1 - length x2g) x1\<close> and x2g: \<open>x2g \<noteq> []\<close> for x2g x1 :: \<open>'a list\<close>
  proof -
    have [simp]: \<open>Suc (length x1 - length x2g) = Suc (length x1) - length x2g\<close>
      by (metis Suc_diff_le diff_le_mono2 diff_zero length_drop that(1) zero_le)
    have [simp]: \<open>Suc (length x1) - length x2g = length x1 - (length x2g - Suc 0)\<close>
      using x2g by auto
    show ?G2
      by (subst that) (auto simp: butlast_conv_take tl_drop_def)[]
  qed
  note butlast = butlast1 butlast2
  have [iff]: \<open>convert_lits_l N M = [] \<longleftrightarrow> M = []\<close> for M
    by (cases M) auto
  have
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M\<^sub>0, N, U, D, NP, UP, Q, W)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have \<open>distinct_mset (the D)\<close>
    using D\<^sub>0 dist by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)
  then have dist_D: \<open>distinct_mset (the E)\<close>
    using distinct_mset_mono[OF E_D\<^sub>0] by fast
  have \<open>M\<^sub>0 \<Turnstile>as CNot (the D)\<close>
    using D\<^sub>0 confl by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  then have M\<^sub>0_CNot_D: \<open>M\<^sub>0 \<Turnstile>as CNot (the E)\<close>
    using E_D\<^sub>0 by (simp add: mset_subset_eqD true_annots_true_cls_def_iff_negation_in_model)

  have n_d: \<open>no_dup M\<^sub>0\<close>
    using lev_inv by (auto simp: mset_take_mset_drop_mset'
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
  have \<open>atm_of L \<notin> atms_of (remove1_mset (- L) (the E))\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    moreover have \<open>-L \<notin># remove1_mset (- L) (the E)\<close>
      using dist_D by (meson distinct_mem_diff_mset multi_member_last)
    ultimately have \<open>L \<in># the E\<close>
      using D by (auto simp: atms_of_def atm_of_eq_atm_of dest: in_diffD)

    then have \<open>-L \<in> lits_of_l M\<^sub>0\<close>
      using M\<^sub>0_CNot_D by (auto simp: true_annots_true_cls_def_iff_negation_in_model)
    then show False
      using n_d L M\<^sub>0 by (cases M\<^sub>0) (auto simp: Decided_Propagated_in_iff_in_lits_of_l)
  qed
  moreover have \<open>L \<in> set (N!C)\<close> if \<open> hd M\<^sub>0 = Propagated L C\<close> and \<open>C > 0\<close> for C
    using confl D M\<^sub>0 L that
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by (cases M\<^sub>0; cases \<open>hd M\<^sub>0\<close>) (auto 5 5 split: if_splits)
  have count_decided_not_Nil[simp]:  \<open>0 < count_decided M \<Longrightarrow> M \<noteq> []\<close> for M :: \<open>(nat, nat) ann_lits\<close>
    by auto
  have get_lev_last: \<open>get_level (M' @ M) (lit_of (last M')) = Suc (count_decided M)\<close>
    if \<open>M\<^sub>0 = M' @ M\<close> and \<open>M' \<noteq> []\<close> and \<open>is_decided (last M')\<close> for M' M
    apply (cases M' rule: rev_cases)
    using that apply simp
    using n_d that by auto

  have atm_of_N:
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset aa) \<Longrightarrow> aa \<noteq> [] \<Longrightarrow> atm_of (lit_of (hd aa)) \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for aa
    by (cases aa) (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  thm WHILEIT_rule
  show ?decomp
    unfolding find_decomp_wl_imp_def Let_def find_decomp_wvmtf_ns_def
    apply (refine_vcg 1 WHILEIT_rule[where R=\<open>measure (\<lambda>(_, M, _). length M)\<close>])
    subgoal by simp
    subgoal by auto
    subgoal using M\<^sub>0 by (auto simp: count_decided_ge_get_maximum_level)
    subgoal by (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal
      using ex_decomp get_level_neq_Suc_count_decided E_D\<^sub>0 (*TODO Proof*)
      apply (auto simp: count_decided_butlast butlast_nil_iff eq_commute[of \<open>[_]\<close>] mset_le_subtract
          ex_decomp_of_max_lvl_def
          intro: butlast)
      using get_maximum_level_mono[of \<open>remove1_mset (-L) (the E)\<close> \<open>remove1_mset (-L) (the D)\<close>]
      by (metis E_D\<^sub>0 count_decided_ge_get_level mset_le_subtract
          not_less_eq_eq)
    subgoal using vm by auto
    subgoal using lits by auto
    subgoal using lits by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      using lits by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by (auto simp: count_decided_butlast count_decided_tl_if)[]
    subgoal for s a b aa ba x1 x2 x1a x2a by (cases aa) (auto simp: count_decided_ge_get_maximum_level)
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa) (auto intro: butlast count_decided_tl_if)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a
      by (cases aa) (auto simp: butlast_nil_iff count_decided_butlast
          eq_commute[of \<open>[_]\<close>] intro: butlast
          cong: if_cong split: if_splits)
    subgoal by auto
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases ba)
        (auto intro!: vmtf_unset_vmtf_tl atm_of_N)
    subgoal for s a b aa ba x1 x2 x1a x2a  by (cases aa)
        (auto  simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal by auto
    subgoal for s D M
      apply (auto simp: count_decided_ge_get_maximum_level ex_decomp_get_ann_decomposition_iff
          get_lev_last)
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append simp del: append_butlast_last_id)
        apply (metis append_butlast_last_id)
       defer
       apply (rule_tac x=\<open>lit_of (last M')\<close> in exI)
       apply auto
        apply (rule_tac x=\<open>butlast M'\<close> in exI)
        apply (case_tac \<open>last M'\<close>)
         apply (auto simp: nth_append snoc_eq_iff_butlast' count_decided_ge_get_maximum_level
          ex_decomp_get_ann_decomposition_iff get_lev_last)
      done
    done
qed


definition find_decomp_wvmtf_ns_pre where
  \<open>find_decomp_wvmtf_ns_pre = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
      vm \<in> vmtf M)\<close>

lemma find_decomp_wl_imp_find_decomp_wl':
  \<open>(uncurry3 find_decomp_wl_imp, uncurry3 find_decomp_wvmtf_ns) \<in>
    [find_decomp_wvmtf_ns_pre]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  by (auto simp: find_decomp_wvmtf_ns_pre_def simp del: twl_st_of_wl.simps
     intro!: find_decomp_wl_imp_le_find_decomp_wl')

definition find_decomp_wvmtf_ns_pre_full where
  \<open>find_decomp_wvmtf_ns_pre_full M' = (\<lambda>(((M, E), L), vm).
      \<exists>N U D NP UP Q W. twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, Q, W)) \<and>
       E \<noteq> None \<and> the E \<noteq> {#} \<and> L = lit_of (hd M) \<and>
       M \<noteq> [] \<and> ex_decomp_of_max_lvl M D L \<and>
       the E \<subseteq># the D \<and> D \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
      vm \<in> vmtf M \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the E) \<and> -L \<in># the E \<and> M = M')\<close>

lemma find_decomp_wl_pre_full_alt_def:
  \<open>find_decomp_wvmtf_ns_pre_full M = (\<lambda>(((b, a), c), d). find_decomp_wvmtf_ns_pre (((b, a), c), d) \<and>
         b = M \<and>
         c = lit_of (hd b) \<and>
         b \<noteq> [] \<and>
              find_decomp_wl_imp_pre (((b, a), c), d))\<close>
  apply (intro ext)
  unfolding find_decomp_wvmtf_ns_pre_def find_decomp_wl_imp_pre_def find_decomp_wvmtf_ns_pre_full_def
  by fastforce

sepref_register find_decomp_wvmtf_ns
lemma find_decomp_wl_imp_code_find_decomp_wl'[sepref_fr_rules]:
  \<open>(uncurry3 find_decomp_wl_imp_code, uncurry3 (PR_CONST find_decomp_wvmtf_ns))
     \<in> [find_decomp_wvmtf_ns_pre_full M]\<^sub>a
     trail_assn\<^sup>d *\<^sub>a (conflict_with_cls_with_cls_with_highest_assn M)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
    trail_assn *assn vmtf_remove_conc\<close>
  using find_decomp_wl_imp_code[unfolded PR_CONST_def, FCOMP find_decomp_wl_imp_find_decomp_wl']
  unfolding PR_CONST_def find_decomp_wl_pre_full_alt_def[symmetric]
  .

lemma get_all_ann_decomposition_get_level:
  assumes
    L': \<open>L' = lit_of (hd M')\<close> and
    nd: \<open>no_dup M'\<close> and
    decomp: \<open>(Decided K # a, M2) \<in> set (get_all_ann_decomposition M')\<close> and
    lev_K: \<open>get_level M' K = Suc (get_maximum_level M' (remove1_mset (- L') y))\<close> and
    L: \<open>L \<in># remove1_mset (- lit_of (hd M')) y\<close>
  shows \<open>get_level a L = get_level M' L\<close>
proof -
  obtain M3 where M3: \<open>M' = M3 @ M2 @ Decided K # a\<close>
    using decomp by blast
  from lev_K have lev_L: \<open>get_level M' L < get_level M' K\<close>
    using get_maximum_level_ge_get_level[OF L, of M'] unfolding L'[symmetric] by auto
  have [simp]: \<open>get_level (M3 @ M2 @ Decided K # a) K = Suc (count_decided a)\<close>
    using nd unfolding M3 by auto
  have undef:\<open>undefined_lit (M3 @ M2) L\<close>
    using lev_L get_level_skip_end[of \<open>M3 @ M2\<close> L \<open>Decided K # a\<close>] unfolding M3
    by auto
  then have \<open>atm_of L \<noteq> atm_of K\<close>
    using lev_L unfolding M3 by auto
  then show ?thesis
    using undef unfolding M3 by (auto simp: get_level_cons_if)

qed

lemma find_decomp_wl_st_int_find_decomp_wl_st:
  \<open>(uncurry find_decomp_wl_st_int, uncurry find_decomp_wl_st) \<in>
   [\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> get_trail_wl S = M \<and>
       no_dup (get_trail_wl S) \<and> L = lit_of(hd M)]\<^sub>f
   nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_no_clvls \<rightarrow>
   \<langle>{(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
     (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the (get_conflict_wl S)). get_level (get_trail_wl S) L = get_level M L)}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for L' M' N' U' D' K' W' Q' A' m'  _ _ _ _ \<phi> L M N U D NP UP W Q
    apply (auto simp: find_decomp_wl_st_int_def find_decomp_wl_st_def
        list_mset_rel_def br_def twl_st_heur_def twl_st_heur_no_clvls_def
        intro!: bind_refine[where R' =
          \<open>{((Ms', vm'), Ms). Ms = Ms' \<and> (\<exists>M''. M = M'' @ Ms) \<and> vm' \<in> vmtf Ms &
               (\<forall>L \<in># remove1_mset (-lit_of (hd M)) (the D). get_level Ms L = get_level M L)}\<close>]
          dest: no_dup_appendD)
    apply (auto simp: find_decomp_wvmtf_ns_def find_decomp_wl'_def intro:
        dest: no_dup_appendD)
    apply (rule RES_refine)
    apply (auto)
      apply (rule_tac x=K in exI; auto 5 5)
    by (auto intro: get_all_ann_decomposition_get_level)
  done

fun conflict_merge_wl where
  \<open>conflict_merge_wl D (M, N, U, _, oth) = (M, N, U, D, oth)\<close>

definition twl_st_confl_extracted_int_assn' where
 \<open>twl_st_confl_extracted_int_assn' M =
  (hr_comp trail_pol_assn trail_pol *assn
      clauses_ll_assn *assn
      nat_assn *assn
      conflict_with_cls_with_cls_with_highest_assn M *assn
      clause_l_assn *assn
      arrayO_assn (arl_assn nat_assn) *assn
      vmtf_remove_conc *assn phase_saver_conc *assn
      uint32_nat_assn)\<close>

sepref_thm find_decomp_wl_imp'_code
  is \<open>uncurry (PR_CONST find_decomp_wl_st_int)\<close>
  :: \<open>[\<lambda>(L, (M', N, U, D, W, Q, vm, \<phi>)). find_decomp_wvmtf_ns_pre_full M (((M', D), L), vm)]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a (twl_st_confl_extracted_int_assn' M)\<^sup>d \<rightarrow>
        (twl_st_confl_extracted_int_assn' M)\<close>
  unfolding find_decomp_wl_st_int_def PR_CONST_def twl_st_heur_assn_def twl_st_confl_extracted_int_assn'_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) find_decomp_wl_imp'_code
   uses isasat_input_bounded_nempty.find_decomp_wl_imp'_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) find_decomp_wl_imp'_code_def

lemmas find_decomp_wl_imp'_code_hnr[sepref_fr_rules] =
  find_decomp_wl_imp'_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


lemma find_decomp_wl_st_find_decomp_wl:
  \<open>(uncurry find_decomp_wl_st, uncurry find_decomp_wl) \<in> [\<lambda>_. True]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding no_resolve_def no_skip_def
  apply (intro frefI nres_relI)
  subgoal premises p for S S'
    using p
    by (cases S, cases S')
        (auto intro!: find_decomp_wl_imp_le_find_decomp_wl'
        simp: find_decomp_wl_st_def find_decomp_wl'_def find_decomp_wl_def
        RES_RETURN_RES)
  done


lemma twl_st_heur_confl_extracted_twl_st_heur:
  \<open>twl_st_heur_confl_extracted O twl_st_heur =
    {((M', N', U', D', Q', W', vm, \<phi>, clvls), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest M \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     clvls \<in> counts_maximum_level M D \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_heur_confl_extracted_def twl_st_heur_def
  by fast

lemma twl_st_heur_confl_extracted2_twl_st_heur:
  \<open>twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls =
    {((M', N', U', D', Q', W', vm, \<phi>, clvls), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel_with_cls_with_highest2 L M \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M}\<close>
  unfolding twl_st_heur_confl_extracted2_def twl_st_heur_no_clvls_def
  by fast

definition find_decomp_wl_pre where
   \<open>find_decomp_wl_pre M = (\<lambda>(L, S). \<exists>D\<^sub>0. get_conflict_wl S \<noteq> None \<and>
               the (get_conflict_wl S) \<noteq> {#} \<and>
               get_trail_wl S \<noteq> [] \<and>
               ex_decomp_of_max_lvl (get_trail_wl S) D\<^sub>0 L \<and>
               L = lit_of (hd (get_trail_wl S)) \<and>
               twl_struct_invs (twl_st_of_wl None (conflict_merge_wl D\<^sub>0 S)) \<and>
               the (get_conflict_wl S) \<subseteq># the D\<^sub>0 \<and> D\<^sub>0 \<noteq> None \<and> get_trail_wl S = M \<and> L = lit_of (hd M) \<and>
               literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and>
               -L \<in># the (get_conflict_wl S) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D\<^sub>0))\<close>

lemma find_decomp_wl_imp'_code_find_decomp_wl[sepref_fr_rules]:
  fixes M :: \<open>(nat, nat) ann_lits\<close>
  shows \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl) \<in>
    [find_decomp_wl_pre M]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a twl_st_confl_extracted_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn2 (-lit_of (hd M))\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  define L where L: \<open>L \<equiv> -lit_of (hd M)\<close>
  have H: \<open>?c
       \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f Id) (\<lambda>_. True)
            (\<lambda>_. comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
              (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and>
                  get_trail_wl S = M \<and> no_dup (get_trail_wl S) \<and> L = lit_of (hd M))
              (\<lambda>_ (L, M', N, U, D, W, Q, vm, \<phi>). find_decomp_wvmtf_ns_pre_full M (((M', D), L), vm))
              (\<lambda>_. True))
             (\<lambda>_. True)]\<^sub>a
        hrp_comp (hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a (twl_st_confl_extracted_int_assn' M)\<^sup>d)
                           (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls))
                 (nat_lit_lit_rel \<times>\<^sub>f Id) \<rightarrow>
        hr_comp (hr_comp (twl_st_confl_extracted_int_assn' M)
                                  {(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
                                     (\<forall>L\<in>#remove1_mset (- lit_of (hd M)) (the (get_conflict_wl S)).
                                       get_level (get_trail_wl S) L = get_level M L)})
               Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[
      OF hfref_compI_PRE_aux[OF find_decomp_wl_imp'_code_hnr[unfolded PR_CONST_def]
            find_decomp_wl_st_int_find_decomp_wl_st]
         find_decomp_wl_st_find_decomp_wl]

    .
  have HH: \<open>H = H' \<Longrightarrow> unat_lit_assn *assn H = unat_lit_assn *assn H'\<close> for H H'
    by auto
  have 2: \<open>(a *assn b *assn c *assn (hr_comp d d')*assn e *assn f*assn g) =
       hr_comp (a *assn b *assn c *assn d *assn e *assn f *assn g)
           (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r d' \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)\<close>
    for a :: \<open>'a \<Rightarrow> 'b \<Rightarrow> assn\<close> and  b c d d' e f g
    by auto

  define twl_st_heur' :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
    \<open>twl_st_heur' =
      {((M'', N', U', D', Q', W', vm, \<phi>, clvls), (M', N, U, D, NP, UP, Q, W)).
        M' = M'' \<and> M' = M \<and> N' = N \<and> U' = U \<and> D = D' \<and>
         Q' = Q \<and>
        (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
        vm \<in> vmtf M \<and>
        phase_saving \<phi> \<and>
        no_dup M
      }\<close>
  have decomp_1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_heur_no_clvls
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp (twl_st_confl_extracted_int_assn' M)
            (twl_st_heur')
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    by (auto simp: hr_comp_def twl_st_heur_no_clvls_def twl_st_heur'_def ex_assn_pair_split
        eq_commute[of ac] intro!: ext)
  have decomp_2: \<open>hr_comp twl_st_confl_extracted_int_assn
     (twl_st_heur_confl_extracted O twl_st_heur_no_clvls) (M, aa, ab, ac, ad, ae, af, b) =
       hr_comp twl_st_confl_extracted_int_assn
     (twl_st_heur_confl_extracted O twl_st_heur') (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
  proof -
    have [simp]: \<open>(a, M, X) \<in> twl_st_heur_confl_extracted O twl_st_heur_no_clvls \<longleftrightarrow>
          (a, M, X) \<in> twl_st_heur_confl_extracted O twl_st_heur'\<close> for X a
      unfolding twl_st_heur_confl_extracted_def twl_st_heur_no_clvls_def twl_st_heur'_def
      by fastforce
    show ?thesis
      by (auto simp: hr_comp_def intro!: ext)
  qed
  have decomp: \<open>((Id \<times>\<^sub>f (Id \<times>\<^sub>f (nat_rel \<times>\<^sub>f (option_conflict_rel_with_cls_with_highest M \<times>\<^sub>f
          (Id \<times>\<^sub>f (Id \<times>\<^sub>f Id)))))) O twl_st_heur') =
     (twl_st_heur_confl_extracted O twl_st_heur')\<close>
    apply (auto simp: twl_st_heur_confl_extracted_def twl_st_heur'_def)
     apply fast
    apply force
    done
  have 1: \<open>hr_comp (twl_st_confl_extracted_int_assn' M) twl_st_heur_no_clvls
        (M, aa, ab, ac, ad, ae, af, b) =
        hr_comp twl_st_confl_extracted_int_assn
         (twl_st_heur_confl_extracted O twl_st_heur_no_clvls)
       (M, aa, ab, ac, ad, ae, af, b)\<close> for aa ab ac ad ae af b
    apply (subst decomp_1)
    apply (subst decomp_2)

    unfolding twl_st_confl_extracted_int_assn'_def twl_st_heur_confl_extracted_twl_st_heur
    twl_st_confl_extracted_int_assn_def conflict_with_cls_with_cls_with_highest_assn_def
    apply (subst 2)
    apply (subst hr_comp_assoc)
    apply (subst decomp)
    ..
  have 0:
    \<open>twl_struct_invs
        (convert_lits_l aa M,
         {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (take ab (tl aa))#},
         {#TWL_Clause (mset (take 2 x)) (mset (drop 2 x)). x \<in># mset (drop (Suc ab) aa)#},
         Some ya, ad, ae, {#}, af) \<Longrightarrow>  no_dup M\<close> for aa ab ya ad ae af
    unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
     cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by simp
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def twl_st_heur_no_clvls_def find_decomp_wvmtf_ns_pre_full_def find_decomp_wl_pre_def
    apply (auto dest: 0)
    by (rule_tac x=aa in exI, rule_tac x=ab in exI, rule_tac x=\<open>Some ya\<close> in exI)
      (use literals_are_in_\<L>\<^sub>i\<^sub>n_mono in auto)

  have \<open>?c \<in> [?pre]\<^sub>a ?im' \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H apply assumption
    using pre ..
  then have \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f'\<close>
    apply (rule hfref_weaken_change_pre)
    subgoal
      unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
        twl_st_confl_extracted_assn_def hr_comp_assoc find_decomp_wl_pre_def
      by (auto simp: 1 intro!: ext)
    subgoal
      by auto
    done
  then have 3: \<open>(uncurry find_decomp_wl_imp'_code, uncurry find_decomp_wl)
    \<in> [?pre]\<^sub>a ?im \<rightarrow>
      hr_comp twl_st_confl_extracted_int_assn
         ((Id \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r option_conflict_rel_with_cls_with_highest M \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O
          {(S', S). (S', S) \<in> twl_st_heur_no_clvls \<and>
             (\<forall>L\<in>#remove1_mset (- lit_of (hd M)) (the (get_conflict_wl S)).
               get_level (get_trail_wl S) L = get_level M L)})\<close>
    (is \<open>?c \<in> [_]\<^sub>a _ \<rightarrow> hr_comp _ ?ref\<close>)
    unfolding twl_st_confl_extracted_int_assn'_def hr_comp_Id2
      conflict_with_cls_with_cls_with_highest_assn_def
      twl_st_confl_extracted_assn_def
    apply (subst (asm) 2)
    unfolding twl_st_confl_extracted_int_assn_def[symmetric] hr_comp_assoc
    .
  have get_maximum_level_eq:
    \<open>\<forall>L\<in>#remove1_mset (- lit_of (hd M)) y. get_level bk L = get_level M L \<Longrightarrow>
       get_maximum_level M (remove1_mset (- lit_of (hd M)) y) =
       get_maximum_level bk (remove1_mset (- lit_of (hd M)) y)\<close> for bk y
    unfolding get_maximum_level_def by auto
  have incl: \<open>?ref
         \<subseteq> twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls\<close>
    unfolding twl_st_heur_confl_extracted2_twl_st_heur
    by (auto  simp: twl_st_heur_no_clvls_def option_conflict_rel_with_cls_with_highest_def
        highest_lit_def L get_maximum_level_eq)

  show ?thesis
    unfolding twl_st_confl_extracted_assn2_def L
    apply (rule subsetD[OF hfref_imp_mono_result[OF incl, unfolded L]])
    apply (rule 3[unfolded L])
    done
qed

definition extract_shorter_conflict_wl_pre where
  \<open>extract_shorter_conflict_wl_pre S \<longleftrightarrow>
      twl_struct_invs (twl_st_of_wl None S) \<and>
            twl_stgy_invs (twl_st_of_wl None S) \<and>
            get_conflict_wl S \<noteq> None \<and> get_conflict_wl S \<noteq> Some {#} \<and> no_skip S \<and> no_resolve S \<and>
            literals_are_\<L>\<^sub>i\<^sub>n S\<close>

lemma backtrack_wl_D_invD:
  assumes \<open>backtrack_wl_D_inv S\<close>
  shows \<open>get_trail_wl S \<noteq> []\<close> \<open>extract_shorter_conflict_wl_pre S\<close>
  using assms unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl
  apply (cases S; auto)
  using assms literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[of S]
  unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def
  extract_shorter_conflict_wl_pre_def get_trail_l_st_l_of_wl get_conflict_l_st_l_of_wl
  no_skip_def no_resolve_def
  by (auto simp del: split_paired_All)


lemma (in -) backtrack_l_inv_alt_def:
  \<open>backtrack_l_inv (st_l_of_wl None S) \<longleftrightarrow> get_trail_wl S \<noteq> [] \<and>
      no_skip S \<and>
      no_resolve S \<and>
      get_conflict_wl S \<noteq> None \<and>
      twl_struct_invs (twl_st_of_wl2 None S) \<and>
      twl_stgy_invs (twl_st_of_wl2 None S) \<and>
      additional_WS_invs (st_l_of_wl None S) \<and>
      get_conflict_wl S \<noteq> Some {#}
  \<close>
  unfolding backtrack_l_inv_def no_skip_def no_resolve_def
  by (cases S) auto

lemma backtrack_wl_D_inv_find_decomp_wl_preD:
  assumes
    inv: \<open>backtrack_wl_D_inv x\<close> and
    ext_c: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close>
  shows \<open>find_decomp_wl_pre (get_trail_wl x) (lit_of_hd_trail_st x, xc)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close> by (cases x)
  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, U, D, NP, UP, W, Q)\<close> and
    \<open>correct_watching (M, N, U, D, NP, UP, W, Q)\<close> and
    \<open>no_skip (M, N, U, D, NP, UP, W, Q)\<close> and
    nr: \<open>no_resolve (M, N, U, D, NP, UP, W, Q)\<close> and
    D: \<open>D \<noteq> None\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>twl_stgy_invs (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>additional_WS_invs (st_l_of_wl None (M, N, U, D, NP, UP, W, Q))\<close> and
    \<open>D \<noteq> Some {#}\<close> and
    [simp]: \<open>M \<noteq> []\<close>
    using inv
    unfolding extract_shorter_conflict_wl_def find_decomp_wl_pre_def backtrack_wl_D_inv_def
      backtrack_wl_inv_def x backtrack_l_inv_alt_def
    by auto
  obtain D' where D': \<open>D = Some D'\<close>
    using D by auto
  obtain E where
     xc: \<open>xc = (M, N, U, Some E, NP, UP, W, Q)\<close> and
     E_D': \<open>E \<subseteq># D'\<close> and
     uL_E: \<open>- lit_of (hd M) \<in># E\<close>
    using ext_c unfolding x D' extract_shorter_conflict_wl_def by auto
  then have [simp]: \<open>E \<noteq> {#}\<close> by auto
  have
    lev: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close> and
    confl: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close>
    using struct unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  have uL_D: \<open>- lit_of (hd M) \<in># D'\<close>
    using uL_E E_D' by auto
  have max: \<open>get_maximum_level M (remove1_mset (- lit_of (hd M)) (the (Some D')))
      < backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, W, Q)))\<close>
  proof (cases \<open>is_proped (hd M)\<close>)
    case True
    then obtain K C M' where
       M: \<open>M = Propagated K C # M'\<close>
      by (cases M; cases \<open>hd M\<close>) auto
    have [simp]: \<open>get_maximum_level (Propagated K F # convert_lits_l N M') =
        get_maximum_level (Propagated K C # M')\<close> for F
      apply (rule ext)
      apply (rule get_maximum_level_cong)
      by (auto simp: get_level_cons_if)
    have \<open>0 < C \<Longrightarrow> K \<in> set (N ! C)\<close>
      using conf unfolding M by (auto 5 5 simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
    then show ?thesis
      using nr uL_D count_decided_ge_get_maximum_level[of M \<open>remove1_mset (- K) D'\<close>]
      unfolding no_resolve_def D' M
      by (fastforce simp:  cdcl\<^sub>W_restart_mset.resolve.simps elim!: convert_lit.elims)
  next
    case False
    then obtain K M' where
       M: \<open>M = Decided K # M'\<close>
      by (cases M; cases \<open>hd M\<close>) auto
    have tr: \<open>M \<Turnstile>as CNot D'\<close>
      using conf confl by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def D')
    have cons: \<open>consistent_interp (lits_of_l M)\<close>
      using lev  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
      by (auto dest!: distinct_consistent_interp)
    have tauto: \<open>\<not> tautology D'\<close>
      using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
    moreover have \<open>distinct_mset D'\<close>
      using dist unfolding D' cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def by auto
    ultimately have \<open>atm_of K \<notin> atms_of (remove1_mset (- K) D')\<close>
      using uL_D unfolding M
      by (auto simp: atms_of_def tautology_add_mset atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          add_mset_eq_add_mset dest!: multi_member_split)
    then show ?thesis
      unfolding M
      apply (subst get_maximum_level_skip_first)
      using count_decided_ge_get_maximum_level[of M' \<open>remove1_mset (- K) D'\<close>]
      by auto
  qed
  moreover have \<open>Decided K # M1 = convert_lits_l N a \<longleftrightarrow> (a \<noteq> [] \<and> is_decided (hd a) \<and>
     M1 = convert_lits_l N (tl a) \<and> hd a = Decided K)\<close> for K M1 a
    by(cases a; cases \<open>hd a\<close>)  auto
  ultimately have ex_decomp[simp]: \<open>ex_decomp_of_max_lvl M (Some D') (lit_of (hd M))\<close>
    using cdcl\<^sub>W_restart_mset.backtrack_ex_decomp[OF lev max]
    unfolding ex_decomp_of_max_lvl_def
    by (auto 5 5 simp: get_all_ann_decomposition_convert_lits_l
        elim!: neq_NilE convert_lit.elims)
  show ?thesis
    unfolding extract_shorter_conflict_wl_def find_decomp_wl_pre_def backtrack_wl_D_inv_def
      backtrack_wl_inv_def backtrack_l_inv_alt_def
    using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct]
      literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct]
      uL_E E_D' struct
    unfolding x D' xc
    by (auto 5 5 simp: extract_shorter_conflict_wl_def backtrack_wl_D_inv_def backtrack_wl_inv_def
        backtrack_l_inv_alt_def lit_of_hd_trail_st_def no_skip_def[symmetric]
        intro: exI[of _ \<open>Some D'\<close>])
qed

definition size_conflict_wl where
  \<open>size_conflict_wl S = size (the (get_conflict_wl S))\<close>

sepref_thm size_conflict_wl_code
  is \<open>RETURN o size_conflict_wl_heur\<close>
  :: \<open>twl_st_confl_extracted_int_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding size_conflict_wl_heur_def twl_st_confl_extracted_int_assn_def
  by sepref

concrete_definition (in -) size_conflict_wl_code
   uses isasat_input_bounded_nempty.size_conflict_wl_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_wl_code_def

lemmas size_conflict_wl_code_hnr[sepref_fr_rules] =
   size_conflict_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma size_conflict_wl_heur_size_conflict_wl:
  \<open>(RETURN o size_conflict_wl_heur, RETURN o size_conflict_wl) \<in>
   [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<rightarrow>
    \<langle>nat_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_wl_heur_def size_conflict_wl_def
      twl_st_heur_confl_extracted2_twl_st_heur size_lookup_conflict_def
      option_conflict_rel_with_cls_with_highest2_def option_conflict_rel_def
      conflict_rel_def)

theorem size_conflict_wl_hnr[sepref_fr_rules]:
  \<open>(size_conflict_wl_code, RETURN o size_conflict_wl)
    \<in> [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>a
      (twl_st_confl_extracted_assn2 L)\<^sup>k  \<rightarrow> uint32_nat_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls)
     (\<lambda>S. get_conflict_wl S \<noteq> None) (\<lambda>_ _. True)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_confl_extracted_int_assn\<^sup>k)
                    (twl_st_heur_confl_extracted2 L O
                     twl_st_heur_no_clvls) \<rightarrow> hr_comp uint32_nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF size_conflict_wl_code_hnr
    size_conflict_wl_heur_size_conflict_wl] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_confl_extracted_assn2_def ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma backtrack_get_conglit_wl_not_NoneD:
  \<open>RETURN xc \<le> extract_shorter_conflict_wl x \<Longrightarrow>
   RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc \<Longrightarrow>
   \<exists>y. get_conflict_wl xd = Some y\<close>
  by (cases xd; cases xc; cases x)
     (auto simp: find_decomp_wl_def extract_shorter_conflict_wl_def)

definition get_snd_highest_lit :: \<open>conflict_rel_with_cls_with_highest \<Rightarrow> nat literal\<close> where
  \<open>get_snd_highest_lit = (\<lambda>((_, _, _), L). fst (the L))\<close>

definition find_lit_of_max_level_wl_int :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> nat literal \<Rightarrow> nat literal\<close> where
  \<open>find_lit_of_max_level_wl_int = (\<lambda>(M, N, U, D, _, _, _, _) _. get_snd_highest_lit D)\<close>

lemma get_snd_highest_lit[sepref_fr_rules]:
   \<open>(return o (\<lambda>((_, _, _), L). (fst (the L))), RETURN o get_snd_highest_lit) \<in>
    [\<lambda>S. snd S \<noteq> None]\<^sub>a (conflict_option_rel_assn *assn
         option_assn (unat_lit_assn *assn uint32_nat_assn))\<^sup>k \<rightarrow> unat_lit_assn\<close>
  unfolding get_snd_highest_lit_def
  apply sep_auto
  apply sepref_to_hoare
  subgoal for x xi
    apply (cases x; cases xi; cases \<open>snd x\<close>; cases \<open>snd xi\<close>)
    apply sep_auto+
    done
  done

sepref_thm find_lit_of_max_level_wl_code
  is \<open>uncurry (RETURN oo find_lit_of_max_level_wl_int)\<close>
  :: \<open>[\<lambda>((M, N, U, (_, L), _), _). L \<noteq> None]\<^sub>a  twl_st_confl_extracted_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>
           unat_lit_assn\<close>
  unfolding find_lit_of_max_level_wl_int_def twl_st_confl_extracted_int_assn_def
  by sepref

concrete_definition (in -) find_lit_of_max_level_wl_code
   uses isasat_input_bounded_nempty.find_lit_of_max_level_wl_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) find_lit_of_max_level_wl_code_def

lemmas find_lit_of_max_level_wl_code_hnr[sepref_fr_rules] =
   find_lit_of_max_level_wl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma find_lit_of_max_level_wl_int_find_lit_of_max_level_wl:
  \<open>(uncurry (RETURN oo find_lit_of_max_level_wl_int), uncurry find_lit_of_max_level_wl) \<in>
    [\<lambda>(S, L'). L' = -L \<and> get_conflict_wl S \<noteq> None \<and> size (the (get_conflict_wl S)) > 1]\<^sub>f
     twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>r nat_lit_lit_rel \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: find_lit_of_max_level_wl_int_def find_lit_of_max_level_wl_def
      twl_st_heur_confl_extracted2_twl_st_heur get_snd_highest_lit_def
      option_conflict_rel_with_cls_with_highest2_def highest_lit_def
      remove1_mset_empty_iff)

theorem find_lit_of_max_level_wl_hnr[sepref_fr_rules]:
  \<open>(uncurry find_lit_of_max_level_wl_code, uncurry find_lit_of_max_level_wl)
    \<in> [\<lambda>(S, L'). L' = -L \<and> get_conflict_wl S \<noteq> None \<and> size (the (get_conflict_wl S)) > 1]\<^sub>a
      (twl_st_confl_extracted_assn2 L)\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k  \<rightarrow> unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>f nat_lit_lit_rel)
     (\<lambda>(S, L'). L' = - L \<and> get_conflict_wl S \<noteq> None \<and> 1 < size (the (get_conflict_wl S)))
     (\<lambda>_ ((M, N, U, (_, L), _), _). L \<noteq> None)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_confl_extracted_int_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k)
                    (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls \<times>\<^sub>f
                     nat_lit_lit_rel) \<rightarrow> hr_comp unat_lit_assn nat_lit_lit_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_lit_of_max_level_wl_code_hnr
    find_lit_of_max_level_wl_int_find_lit_of_max_level_wl] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def highest_lit_def remove1_mset_empty_iff
        twl_st_heur_confl_extracted2_def option_conflict_rel_with_cls_with_highest2_def
        option_conflict_rel_def conflict_rel_def twl_st_heur_no_clvls_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_confl_extracted_assn2_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

definition list_of_mset2_None where
  \<open>list_of_mset2_None L L' D = SPEC(\<lambda>(E, F). mset E = the D \<and> E!0 = L \<and> E!1 = L' \<and>
     F = None \<and> length E \<ge> 2)\<close>

lemma propgate_bt_wl_D_alt_def:
  \<open>propgate_bt_wl_D = (\<lambda>L L' (M, N, U, D, NP, UP, Q, W).
    list_of_mset2_None (- L) L' D \<bind>
    (\<lambda>(D'', E). RETURN
             (Propagated (- L) (length N) # M, N @ [D''], U, E, NP, UP, {#L#},
              W(- L := W (- L) @ [length N], L' := W L' @ [length N]))))\<close>
  unfolding propgate_bt_wl_D_def list_of_mset2_def list_of_mset2_None_def
  by (auto simp: RES_RETURN_RES RES_RETURN_RES2 uncurry_def intro!: ext)


lemma extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial:
  \<open>(extract_shorter_conflict_st_trivial_heur, extract_shorter_conflict_st_trivial) \<in>
    [\<lambda>S. get_conflict_wl S \<noteq> None]\<^sub>f twl_st_heur \<rightarrow> \<langle>twl_st_heur_no_clvls\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: extract_shorter_conflict_st_trivial_heur_def twl_st_heur_no_clvls_def
        extract_shorter_conflict_st_trivial_def twl_st_heur_def RETURN_def
     intro!: RES_refine)


type_synonym (in -) conflict_rel_with_cls = \<open>nat clause_l \<times> bool option list\<close>
type_synonym (in -) conflict_with_cls_assn = \<open>uint32 array \<times> bool option array\<close>

type_synonym twl_st_wll_confl_with_cls =
  \<open>trail_pol_assn \<times> clauses_wl \<times> nat \<times> conflict_with_cls_assn \<times>
    lit_queue_l \<times> watched_wl \<times> vmtf_remove_assn \<times> phase_saver_assn\<close>

definition option_conflict_rel_with_cls_removed
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (conflict_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_conflict_rel_with_cls_removed L L' = {((C, xs), D). D \<noteq> None \<and> (drop 2 C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>


definition option_conflict_rel_with_cls
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> (conflict_rel_with_cls \<times> nat clause option) set\<close>
where
  \<open>option_conflict_rel_with_cls L L' = {((C, xs), D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel \<and>
    mset_as_position xs {#} \<and> (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs) \<and> C!0 = L \<and> C!1 = L' \<and> length C \<ge> 2}\<close>

definition option_conflict_rel_with_cls_removed1 :: \<open>(nat clause_l \<times> nat clause option) set\<close> where
  \<open>option_conflict_rel_with_cls_removed1 = {(C, D). D \<noteq> None \<and> (C, the D) \<in> list_mset_rel}\<close>

abbreviation (in -) conflict_with_cls_int_assn :: \<open>conflict_rel_with_cls \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_int_assn \<equiv>
    (array_assn unat_lit_assn *assn array_assn (option_assn bool_assn))\<close>

definition conflict_with_cls_assn_removed
 :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow> conflict_with_cls_assn \<Rightarrow> assn\<close>
where
 \<open>conflict_with_cls_assn_removed L L' \<equiv>
   hr_comp conflict_with_cls_int_assn (option_conflict_rel_with_cls_removed L L')\<close>

definition conflict_with_cls_assn :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat clause option \<Rightarrow>
   conflict_with_cls_assn \<Rightarrow> assn\<close> where
 \<open>conflict_with_cls_assn L L' \<equiv> hr_comp conflict_with_cls_int_assn (option_conflict_rel_with_cls L L')\<close>

definition option_conflict_rel_removed :: \<open>_ set\<close> where
  \<open>option_conflict_rel_removed =
   {((b, n, xs), C). C \<noteq> None \<and> n \<ge> 2 \<and> n \<le> length xs \<and>
      ((b, n - 2, xs), C) \<in> option_conflict_rel}\<close>


type_synonym (in -) twl_st_wl_heur_W_confl_with_cls =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    conflict_rel_with_cls \<times> nat clause \<times> nat list list \<times> vmtf_remove_int \<times> bool list\<close>

text \<open>
  \<^item> We are filling D starting from the end (index \<^term>\<open>n\<close>)
  \<^item> We are changing position one and two.
\<close>
definition conflict_to_conflict_with_cls
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat literal list \<Rightarrow> conflict_option_rel \<Rightarrow> (nat literal list \<times> conflict_option_rel) nres\<close>
where
  \<open>conflict_to_conflict_with_cls = (\<lambda>_ _ D (_, n, xs). do {
     (_, _, C, zs) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, m, C, zs). i \<le> length zs \<and> length zs = length xs \<and>
          length C = n \<and> m \<le> length C \<and> C!0 = D!0 \<and> C!1 = D!1\<^esup>
       (\<lambda>(i, m, C, zs). m > 2)
       (\<lambda>(i, m, C, zs). do {
           ASSERT(i < length xs);
           ASSERT(i \<le> uint_max div 2);
           ASSERT(m > 2);
           ASSERT(zs ! i \<noteq> None \<longrightarrow> Pos i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l);
           case zs ! i of
             None \<Rightarrow> RETURN (i+1, m, C, zs)
           | Some b \<Rightarrow> RETURN (i+1, m-1, C[m-1 := (if b then Pos i else Neg i)], zs[i := None])
       })
       (0, n, D, xs);
     RETURN (C, (True, zero_uint32_nat, zs))
  }
  )\<close>

definition conflict_to_conflict_with_cls_spec where
  \<open>conflict_to_conflict_with_cls_spec _ D = D\<close>

definition list_of_mset2_None_droped where
  \<open>list_of_mset2_None_droped L L' _ D = SPEC(\<lambda>(E, F). mset (drop 2 E) = the D \<and> E!0 = L \<and> E!1 = L' \<and>
     F = None \<and> length E \<ge> 2)\<close>

lemma (in -) bind_rule_complete_RES: \<open>(M \<bind> f \<le> RES \<Phi>) = (M \<le> SPEC (\<lambda>x. f x \<le> RES \<Phi>))\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

lemma WHILEIT_rule_stronger_inv_RES:
  assumes
    \<open>wf R\<close> and
    \<open>I s\<close> and
    \<open>I' s\<close>
    \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> b s \<Longrightarrow> f s \<le> SPEC (\<lambda>s'. I s' \<and>  I' s' \<and> (s', s) \<in> R)\<close> and
   \<open>\<And>s. I s \<Longrightarrow> I' s \<Longrightarrow> \<not> b s \<Longrightarrow> s \<in> \<Phi>\<close>
 shows \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> RES \<Phi>\<close>
proof -
  have RES_SPEC: \<open>RES \<Phi> = SPEC(\<lambda>s. s \<in> \<Phi>)\<close>
    by auto
  have \<open>WHILE\<^sub>T\<^bsup>I\<^esup> b f s \<le> WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s\<close>
    by (metis (mono_tags, lifting) WHILEIT_weaken)
  also have \<open>WHILE\<^sub>T\<^bsup>\<lambda>s. I s \<and> I' s\<^esup> b f s \<le> RES \<Phi>\<close>
    unfolding RES_SPEC
    by (rule WHILEIT_rule) (use assms in \<open>auto simp: \<close>)
  finally show ?thesis .
qed

lemma conflict_to_conflict_with_cls_id:
  \<open>(uncurry3 conflict_to_conflict_with_cls, uncurry3 list_of_mset2_None_droped) \<in>
    [\<lambda>(((L, L'),D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> length D = size (the C) + 2 \<and>
      L = D!0 \<and> L' = D!1]\<^sub>f
      Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f option_conflict_rel_removed  \<rightarrow>
       \<langle>Id \<times>\<^sub>f option_conflict_rel\<rangle> nres_rel\<close>
   (is \<open>_ \<in> [_]\<^sub>f _ \<rightarrow> \<langle>?R\<rangle>nres_rel\<close>)
proof -
  have H: \<open>conflict_to_conflict_with_cls L L' D (b, n, xs) \<le> \<Down> ?R (list_of_mset2_None_droped L L' D (Some C))\<close>
    if
      ocr: \<open>((b, n, xs), Some C) \<in> option_conflict_rel_removed\<close> and
      lits_\<A>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n C\<close> and
      len_D: \<open>length D = size C + 2\<close> and
      [simp]: \<open>D!0 = L\<close>\<open>D!Suc 0 = L'\<close>
    for b n xs C D L L'
  proof -
    define I' where
      [simp]: \<open>I' = (\<lambda>(i, m, D, zs).
              ((b, m, zs), Some (filter_mset (\<lambda>L. atm_of L \<ge> i) C)) \<in> option_conflict_rel_removed \<and>
               m - 2 = length (filter (op \<noteq> None) zs) \<and>
               i + (m - 2) + length (filter (op = None) (drop i zs)) = length zs \<and> (\<forall>k < i. zs ! k = None) \<and>
               mset (drop m D) = filter_mset (\<lambda>L. atm_of L < i) C \<and>
               length D \<ge> 2 \<and>
               m \<ge> 2)\<close>
    let ?I' = I'
    let ?C = \<open>C\<close>
    let ?I = \<open>\<lambda>xs n (i, m, E, zs). i \<le> length zs \<and> length zs = length xs \<and> length E = n \<and>
          m \<le> length E \<and> E!0 = D!0 \<and> E!1 = D!1\<close>
    let ?cond = \<open>\<lambda>s. case s of (i, m, C, zs) \<Rightarrow> 2 < m\<close>
    have n_le: \<open>n \<le> length xs\<close> and b: \<open>b = False\<close> and
       dist_C: \<open>distinct_mset C\<close> and
       tauto_C: \<open>\<not> tautology C\<close> and
       atms_le_xs: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length xs\<close> and
       n_size: \<open>n = 2 + size C\<close> and
       map: \<open>mset_as_position xs C\<close>
      using mset_as_position_length_not_None[of xs ?C] that  mset_as_position_distinct_mset[of xs ?C]
        mset_as_position_tautology[of xs ?C] len_D
      by (auto simp: option_conflict_rel_def option_conflict_rel_removed_def conflict_rel_def
          tautology_add_mset)
    have size_C: \<open>size C \<le> 1 + uint_max div 2\<close>
      using simple_clss_size_upper_div2[OF lits_\<A>\<^sub>i\<^sub>n dist_C tauto_C] .

    have final: "\<not> (case s of (i, m, C, zs) \<Rightarrow> 2 < m) \<Longrightarrow>
    s \<in> {x. (case x of (_, _, C, zs) \<Rightarrow> RETURN (C, True, zero_uint32_nat, zs))
              \<le> RES ((Id \<times>\<^sub>f option_conflict_rel)\<inverse> ``
                      {(E, F).
                       mset (drop 2 E) = the (Some C) \<and>
                       E ! 0 = L \<and> E ! 1 = L' \<and> F = None \<and> 2 \<le> length E})}"
      if
        s0: "?I baa aa s" and
        s1: "?I' s" and
        s:
          "\<not> ?cond s"
(*           "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)" *)
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)"
      for a ba aa baa s (* ab bb ac bc ad bd *)
    proof -
      obtain ab bb ac bc ad bd where
        s': "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
        by (cases s) auto
      then have [simp]: \<open>ac = 2\<close> \<open>s = (ab, 2, ad, bd)\<close> \<open>bb = (2, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close>
        \<open>n = aa\<close>\<open>xs = baa\<close>
        using s s1 by auto
      have \<open>((b, 2, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close> and
         le_ad: \<open>length ad \<ge> 2\<close>
        using s1 by auto
      then have [simp]: \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close> and map': \<open>mset_as_position bd {#}\<close>
        unfolding option_conflict_rel_removed_def option_conflict_rel_def conflict_rel_def by auto
      have [simp]: \<open>length bd = length xs\<close>
        using s0 by auto
      have [iff]: \<open>\<not>x < ab \<longleftrightarrow> ab \<le> x\<close> for x
        by auto
      have \<open>{#L \<in># C. atm_of L < ab#} = C\<close>
        using multiset_partition[of C \<open>\<lambda>L. atm_of L < ab\<close>] by auto
      then have [simp]: \<open>mset (drop 2 ad) = C\<close>
        using s1 by auto
      have [simp]: \<open>ad ! 0 = L\<close> \<open>ad ! Suc 0 = L'\<close>
        using s0 unfolding s by auto
      show ?thesis
        using map' atms_le_xs le_ad by (auto simp: option_conflict_rel_with_cls_removed_def
            list_mset_rel_def br_def Image_iff option_conflict_rel_def conflict_rel_def)
    qed
    have init: "I' (0, aa, D, baa)"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)"
      for a ba aa baa
      using ocr that n_le n_size size_C len_D mset_as_position_length_not_None[OF map]
      sum_length_filter_compl[of \<open>op = None\<close> xs]
      by auto

    have in_\<L>\<^sub>a\<^sub>l\<^sub>l: "Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        cond: "?cond s" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_baa: "ab < length baa" and
        bd_ab: "bd ! ab \<noteq> None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_conflict_rel_removed_def option_conflict_rel_def conflict_rel_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' cond s unfolding I' by auto
      then have ab_in_C: \<open>Pos ab \<in># C \<or> Neg ab \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      then show ?thesis
        using lits_\<A>\<^sub>i\<^sub>n
        by (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
    qed
    have le_uint_max_div2: "ab \<le> uint_max div 2"
      if
        "(b, n, xs) = (a, ba)" and
        "ba = (aa, baa)" and
        "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)" and
        "ab < length baa"
      for a ba aa baa s ab bb ac bc ad bd
    proof (rule ccontr)
      assume le: \<open>\<not> ?thesis\<close>
      have \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close>
        using I' s unfolding I'_def by auto
      have \<open>L \<in># C \<Longrightarrow> atm_of L \<le> uint_max div 2\<close> for L
        using lits_\<A>\<^sub>i\<^sub>n in_N1_less_than_uint_max
        by (cases L)  (auto dest!: multi_member_split simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset uint_max_def)
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#}\<close>
        using le by (force simp: filter_mset_empty_conv)
      then show False
        using m s ocr unfolding option_conflict_rel_removed_def option_conflict_rel_def conflict_rel_def by auto
    qed
    have IH_I': "I' (ab + 1, ac, ad, bd)"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s: "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab \<le> uint_max div 2" and
        "2 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        bd_ab: "bd ! ab = None"
      for a ba aa baa s ab bb ac bc ad bd
    proof -
      have [simp]: \<open>s = (ab, ac, ad, bd)\<close> \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close>
        \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa \<close> \<open>length bd = length baa\<close>
        using s I by auto
      have
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close> and
        eq: \<open>ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop ab bd)) = length baa\<close> and
        le_ab_None: \<open>\<forall>k<ab. bd ! k = None\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close>
        using b unfolding option_conflict_rel_removed_def option_conflict_rel_def conflict_rel_def by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>Pos ab \<notin># C\<close> \<open>Neg ab \<notin># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab lits_\<A>\<^sub>i\<^sub>n by auto
      have [simp]: \<open>{#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        unfolding less_Suc_eq_le unfolding le_eq_less_or_eq
        using ab_in_C dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      then have mset_drop: \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using I' by auto

      have \<open>x \<in>#C \<Longrightarrow> atm_of x \<noteq> ab\<close> for x
        using bd_ab ocr
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> x]
        mset_as_position_nth[of bd \<open>{#L \<in># C. ab \<le> atm_of L#}\<close> \<open>-x\<close>]
        unfolding option_conflict_rel_def conflict_rel_def option_conflict_rel_removed_def
        by force
      then have \<open>{#L \<in># C. ab \<le> atm_of L#} = {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using s by (force intro!: filter_mset_cong2)
      then have ocr': \<open>((b, ac, bd), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close>
        using I' s by auto

      have
        x1a: \<open>ac - 2 = size {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>ac \<ge> 2\<close> and
        map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close>
        using ocr unfolding option_conflict_rel_def conflict_rel_def option_conflict_rel_removed_def
        by auto

      have [iff]: \<open>ab + length (filter (op \<noteq> None) x2b) = length x2b \<longleftrightarrow> ab = length (filter (op = None) x2b)\<close> for x2b
        using sum_length_filter_compl[of \<open>op \<noteq> None\<close> x2b] by auto
      have filter_take_ab: \<open>filter (op = None) (take ab bd) = take ab bd\<close>
        apply (rule filter_id_conv[THEN iffD2])
        using le_ab_None by (auto simp: nth_append take_set split: if_splits)
      have Suc_le_bd: \<open>Suc ab + length (filter (op \<noteq> None) bd) + length (filter (op = None) (drop (Suc ab )bd)) =
          length baa\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab by auto
      have le_Suc_None: \<open>k < Suc ab \<Longrightarrow> bd ! k = None\<close> for k
        using le_ab_None bd_ab  by (auto simp: less_Suc_eq)

      show ?thesis using le_ad mset_drop ocr' Suc_le_bd le_Suc_None ac ac2 unfolding I'_def by auto
    qed
    have IH_I'_notin: "I' (ab + 1, ac - 1, ad[ac - 1 := if x then Pos ab else Neg ab],
          bd[ab := None])"
      if
        I: "?I baa aa s" and
        I': "I' s" and
        m: "?cond s" and
        s:
          "s = (ab, bb)"
          "bb = (ac, bc)"
          "bc = (ad, bd)"
          "(b, n, xs) = (a, ba)"
          "ba = (aa, baa)" and
        ab_le: "ab < length baa" and
        "ab \<le> uint_max div 2" and
        "2 < ac" and
        "bd ! ab \<noteq> None \<longrightarrow> Pos ab \<in># \<L>\<^sub>a\<^sub>l\<^sub>l" and
        bd_ab_x: "bd ! ab = Some x"
      for a ba aa baa s ab bb ac bc ad bd x
    proof -
      have [simp]: \<open>bb = (ac, ad, bd)\<close> \<open>bc = (ad, bd)\<close> \<open>ba = (aa, baa)\<close> \<open>n = aa\<close> \<open>xs = baa\<close>
        \<open>s = (ab, (ac, (ad, bd)))\<close>
        \<open>length baa = length bd\<close>
        using I s by auto
      have \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close> and
        ac: \<open>ac - 2 = length (filter (op \<noteq> None) bd)\<close> and
        eq: \<open>ab + (ac - 2) + length (filter (op = None) (drop ab bd)) = length bd\<close> and
        ac2: \<open>ac \<ge> 2\<close> and
        le_ad: \<open>length ad \<ge> 2\<close>
        using I' unfolding I'_def s by auto
      then have map: \<open>mset_as_position bd {#L \<in># C. ab \<le> atm_of L#}\<close> and
        le_bd: \<open>\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length bd\<close> and
        ocr: \<open>((b, ac, bd), Some {#L \<in># C. ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close>
        using b unfolding option_conflict_rel_def conflict_rel_def option_conflict_rel_removed_def
        by auto
      have \<open>ab < length bd\<close>
        using I I' m by auto
      then have ab_in_C: \<open>(if x then Pos ab else Neg ab) \<in># C\<close>
        using mset_as_position_in_iff_nth[OF map, of \<open>Pos ab\<close>] mset_as_position_in_iff_nth[OF map, of \<open>Neg ab\<close>]
          bd_ab_x lits_\<A>\<^sub>i\<^sub>n by auto
      have \<open>distinct_mset {#L \<in># C. ab \<le> atm_of L#}\<close> \<open>\<not> tautology {#L \<in># C. ab \<le> atm_of L#}\<close>
        using mset_as_position_distinct_mset[OF map] mset_as_position_tautology[OF map] by fast+
      have [iff]: \<open>\<not> ab < atm_of a \<and> ab = atm_of a \<longleftrightarrow>  (ab = atm_of a)\<close> for a :: \<open>nat literal\<close> and ab
        by auto
      have H1: \<open>{#L \<in># C.  ab \<le> atm_of L#} = (if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv)
      have H2: \<open>{#L \<in># C. Suc ab \<le> atm_of L#} = remove1_mset (Pos ab) (remove1_mset (Neg ab) {#L \<in># C. ab \<le> atm_of L#})\<close>
        by (auto simp: H1)
      have map': \<open>mset_as_position (bd[ab := None]) {#L \<in># C. Suc ab \<le> atm_of L#}\<close>
        unfolding H2
        apply (rule mset_as_position_remove)
        using map ab_le by auto
      have c_r: \<open>((b, ac - Suc 0, bd[ab := None]), Some {#L \<in># C. Suc ab \<le> atm_of L#}) \<in> option_conflict_rel_removed\<close>
        using ocr b map' m ac by (cases x) (auto simp: option_conflict_rel_removed_def
            option_conflict_rel_def conflict_rel_def H1)
      have H3: \<open>(if x then add_mset (Pos ab) else add_mset (Neg ab)) {#L \<in># C. atm_of L < ab#} = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using ab_in_C unfolding Suc_le_eq unfolding le_eq_less_or_eq
        using dist_C tauto_C filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Neg ab#}\<close>]
          filter_mset_cong_inner_outer[of C \<open>\<lambda>L. ab = atm_of L\<close> \<open>\<lambda>L. ab = atm_of L\<close> \<open>{#Pos ab#}\<close>]
        by (auto dest!: multi_member_split
            simp: filter_union_or_split tautology_add_mset filter_mset_empty_conv less_Suc_eq_le
              order.order_iff_strict
            intro!: filter_mset_cong2)
      have ac_ge0: \<open>ac > 0\<close>
        using m by auto
      then have \<open>ac - Suc 0 < length ad\<close> and \<open>mset (drop ac ad) = {#L \<in># C. atm_of L < ab#}\<close>
        using I' I m by auto
      then have 3: \<open>mset (drop (ac - Suc 0) (ad[ac - Suc 0 := (if x then Pos ab else Neg ab)])) = {#L \<in># C. atm_of L < Suc ab#}\<close>
        using Cons_nth_drop_Suc[symmetric, of \<open>ac - 1\<close> \<open>ad\<close>] ac_ge0
        by (auto simp: drop_update_swap H3[symmetric])
      have ac_filter: \<open>ac - Suc (Suc (Suc 0)) = length (filter (op \<noteq> None) (bd[ab := None]))\<close>
        apply (subst length_filter_update_true)
        using ac bd_ab_x ab_le by auto
      have \<open>length (filter (op \<noteq> None) bd) \<ge> Suc 0\<close>
        using bd_ab_x ab_le nth_mem by (fastforce simp: filter_empty_conv)
      then have eq': \<open>Suc ab + length (filter (op \<noteq> None) (bd[ab := None])) + length (filter (op = None) (drop (Suc ab) bd)) = length bd\<close>
        using b ac Cons_nth_drop_Suc[of ab bd, symmetric] ab_le eq bd_ab_x ac2
        by (auto simp: length_filter_update_true)
      show ?thesis
        using b c_r that s ac_filter 3 eq' le_ad unfolding I'_def by auto
    qed
    show ?thesis
      supply WHILEIT_rule[refine_vcg del]
      unfolding conflict_to_conflict_with_cls_def Let_def list_of_mset2_None_droped_def conc_fun_RES
      apply refine_rcg
      unfolding bind_rule_complete_RES
      apply (refine_vcg WHILEIT_rule_stronger_inv_RES[where
            R = \<open>measure (\<lambda>(i :: nat, m :: nat, D :: nat clause_l, zs :: bool option list). length zs - i)\<close> and
            I' = \<open>I'\<close>] bind_rule_complete_RES)
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal using len_D n_size by auto
      subgoal using len_D n_size by auto
      subgoal by simp
      subgoal by simp
      subgoal by (rule init)
      subgoal using n_le by auto
      subgoal by (rule le_uint_max_div2)
      subgoal by auto
      subgoal by (rule in_\<L>\<^sub>a\<^sub>l\<^sub>l) assumption+
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I')
      subgoal by auto
      subgoal using b by (auto simp: less_Suc_eq)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (rule IH_I'_notin)
      subgoal by auto
      subgoal by (rule final) assumption+
      done
    qed

  show ?thesis
    apply (intro frefI nres_relI)
    apply clarify
    subgoal for a aa ab b ac ba y
      using H by (auto simp: conflict_to_conflict_with_cls_spec_def)
    done
qed


lemma conflict_to_conflict_with_cls_code_helper:
  \<open>a1'b \<le> uint_max div 2 \<Longrightarrow> Suc a1'b \<le> uint_max\<close>
  \<open> 0 < a1'c \<Longrightarrow> one_uint32_nat \<le> a1'c\<close>
  \<open>fast_minus a1'c one_uint32_nat  = a1'c - 1\<close>
  by (auto simp: uint_max_def)

sepref_register conflict_to_conflict_with_cls
sepref_thm conflict_to_conflict_with_cls_code
  is \<open>uncurry3 (PR_CONST conflict_to_conflict_with_cls)\<close>
  :: \<open>unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a(array_assn unat_lit_assn)\<^sup>d *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a
      array_assn unat_lit_assn *assn conflict_option_rel_assn\<close>
  supply uint32_nat_assn_zero_uint32_nat[sepref_fr_rules] [[goals_limit=1]]
   Pos_unat_lit_assn'[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
   conflict_to_conflict_with_cls_code_helper[simp] uint32_2_hnr[sepref_fr_rules]
  unfolding conflict_to_conflict_with_cls_def array_fold_custom_replicate
    fast_minus_def[of \<open>_ :: nat\<close>, symmetric] PR_CONST_def
  apply (rewrite at "\<hole> < length _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "_ ! \<hole> \<noteq> None" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at "\<hole> < _" two_uint32_nat_def[symmetric])
  apply (rewrite at "\<hole> < _" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>(\<hole>, _, _, _)\<close> zero_uint32_nat_def[symmetric])
  apply (rewrite at "(zero_uint32_nat, \<hole>, _, _)" annotate_assn[where A=uint32_nat_assn])
  apply (rewrite at \<open>_ + \<hole>\<close> one_uint32_nat_def[symmetric])+
  apply (rewrite at \<open>fast_minus _ \<hole>\<close> one_uint32_nat_def[symmetric])+
  by sepref

concrete_definition (in -) conflict_to_conflict_with_cls_code
   uses isasat_input_bounded_nempty.conflict_to_conflict_with_cls_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) conflict_to_conflict_with_cls_code_def

lemmas conflict_to_conflict_with_cls_code_refine[sepref_fr_rules] =
   conflict_to_conflict_with_cls_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma extract_shorter_conflict_with_cls_code_conflict_to_conflict_with_cls_spec[sepref_fr_rules]:
  \<open>(uncurry3 conflict_to_conflict_with_cls_code, uncurry3 list_of_mset2_None_droped)
    \<in> [\<lambda>(((L, L'), D), C). C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and>
           length D = size (the C) + 2 \<and> L = D ! 0 \<and> L' = D ! 1]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>d *\<^sub>a
     (hr_comp conflict_option_rel_assn option_conflict_rel_removed)\<^sup>d \<rightarrow>
     clause_ll_assn *assn conflict_option_assn\<close>
  using conflict_to_conflict_with_cls_code_refine[unfolded PR_CONST_def,
    FCOMP conflict_to_conflict_with_cls_id]
  unfolding conflict_option_assn_def
  by simp

definition remove2_from_conflict :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> nat cconflict \<Rightarrow> nat cconflict\<close> where
  \<open>remove2_from_conflict L L' C = Some (remove1_mset L (remove1_mset L' (the C)))\<close>

definition remove2_from_conflict_int
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> conflict_option_rel \<Rightarrow> conflict_option_rel\<close>
where
  \<open>remove2_from_conflict_int L L' = (\<lambda>(b, n, xs). (b, n, xs[atm_of L := None, atm_of L' := None]))\<close>

lemma remove2_from_conflict_int_remove2_from_conflict:
  \<open>(uncurry2 (RETURN ooo remove2_from_conflict_int), uncurry2 (RETURN ooo remove2_from_conflict)) \<in>
   [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>f
    Id \<times>\<^sub>f Id \<times>\<^sub>f option_conflict_rel \<rightarrow> \<langle>option_conflict_rel_removed\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for K K' b n xs L L' bc C
    using mset_as_position_length_not_None[of xs C] mset_as_position_tautology[of xs C]
      mset_as_position_remove[of xs C \<open>atm_of L\<close>]
      mset_as_position_remove[of \<open>xs[atm_of L := None]\<close> \<open>remove1_mset L C\<close> \<open>atm_of L'\<close>]
    apply (cases L; cases L')
    by (auto simp: remove2_from_conflict_int_def remove2_from_conflict_def
      option_conflict_rel_def conflict_rel_def option_conflict_rel_removed_def
      add_mset_eq_add_mset tautology_add_mset
      dest!: multi_member_split)
  done

sepref_thm remove2_from_conflict_code
  is \<open>uncurry2 (RETURN ooo remove2_from_conflict_int)\<close>
  :: \<open>[\<lambda>((L, L'), (b, n, xs)). atm_of L < length xs \<and> atm_of L' < length xs]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
      conflict_option_rel_assn\<close>
  unfolding remove2_from_conflict_int_def
  by sepref

concrete_definition (in -) remove2_from_conflict_code
   uses isasat_input_bounded_nempty.remove2_from_conflict_code.refine_raw
   is \<open>(uncurry2 ?f, _)\<in>_\<close>

prepare_code_thms (in -) remove2_from_conflict_code_def

lemmas remove2_from_conflict_code_hnr[sepref_fr_rules] =
   remove2_from_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem remove2_from_conflict_hnr[sepref_fr_rules]:
  \<open>(uncurry2 remove2_from_conflict_code, uncurry2 (RETURN ooo remove2_from_conflict))
    \<in> [\<lambda>((L, L'), C). L \<in># the C \<and> L' \<in># the C \<and> C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L']\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow>
      hr_comp conflict_option_rel_assn option_conflict_rel_removed\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
    \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_conflict_rel)
          (\<lambda>((L, L'), C).
              L \<in># the C \<and>
              L' \<in># the C \<and>
              C \<noteq> None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L \<noteq> L')
          (\<lambda>_ ((L, L'), b, n, xs).
              atm_of L < length xs \<and> atm_of L' < length xs)
          (\<lambda>_. True)]\<^sub>a
      hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f option_conflict_rel) \<rightarrow>
      hr_comp conflict_option_rel_assn option_conflict_rel_removed\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove2_from_conflict_code_hnr
    remove2_from_conflict_int_remove2_from_conflict] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_pol_def trail_pol_def option_conflict_rel_def
        conflict_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def by auto
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im PR_CONST_def apply assumption
    using pre ..
qed

definition list_of_mset2_None_int where
  \<open>list_of_mset2_None_int L L' C\<^sub>0 =  do {
     let n = size (the C\<^sub>0);
     ASSERT(n \<ge> 2);
     let D = replicate n L;
     let D = D[1 := L'];
     let C = remove2_from_conflict L L' C\<^sub>0;
     ASSERT(C \<noteq> None \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> size (the C\<^sub>0) = size (the C) + 2 \<and>
       D!0 = L \<and> D!1 = L');
(*      let D = ASSN_ANNOT (conflict_with_cls_assn_removed L L') (conflict_to_conflict_with_cls_spec D C); *)
(*      ASSERT(D \<noteq> None \<and> L \<notin># the D \<and> L' \<notin># the D); *)
(*      let D = add2_from_conflict L L' D;
     ASSERT(D \<noteq> None); *)
     list_of_mset2_None_droped L L' D C}\<close>

lemma (in -) list_length2E:
  \<open>length xs \<ge> 2 \<Longrightarrow> (\<And>x y zs. xs = x # y # zs \<Longrightarrow> zs = tl (tl xs) \<Longrightarrow> P) \<Longrightarrow> P\<close>
  by (cases xs; cases \<open>tl xs\<close>) auto

lemma list_of_mset2_None_int_list_of_mset2_None:
  \<open>(uncurry2 (list_of_mset2_None_int), uncurry2 list_of_mset2_None) \<in>
     [\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and>
        literals_are_in_\<L>\<^sub>i\<^sub>n (the C) \<and> distinct_mset (the C)]\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: list_of_mset2_None_int_def list_of_mset2_None_def
      list_of_mset2_def conflict_to_conflict_with_cls_spec_def
      remove2_from_conflict_def add_mset_eq_add_mset RES_RETURN_RES
      literals_are_in_\<L>\<^sub>i\<^sub>n_sub literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset list_of_mset2_None_droped_def
      dest!: multi_member_split
      elim!: list_length2E)

definition size_conflict :: \<open>nat clause option \<Rightarrow> nat\<close> where
  \<open>size_conflict D = size (the D)\<close>

definition size_conflict_int :: \<open>conflict_option_rel \<Rightarrow> nat\<close> where
  \<open>size_conflict_int = (\<lambda>(_, n, _). n)\<close>

lemma size_conflict_code_refine_raw:
  \<open>(return o (\<lambda>(_, n, _). n), RETURN o size_conflict_int) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare  (sep_auto simp: size_conflict_int_def)

concrete_definition (in -) size_conflict_code
   uses isasat_input_bounded_nempty.size_conflict_code_refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) size_conflict_code_def

lemmas size_conflict_code_hnr[sepref_fr_rules] =
   size_conflict_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma size_conflict_int_size_conflict:
  \<open>(RETURN o size_conflict_int, RETURN o size_conflict) \<in> [\<lambda>D. D \<noteq> None]\<^sub>f option_conflict_rel \<rightarrow>
     \<langle>Id\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: size_conflict_int_def size_conflict_def option_conflict_rel_def
      conflict_rel_def)

lemma size_conflict_hnr[sepref_fr_rules]:
  \<open>(size_conflict_code, RETURN \<circ> size_conflict) \<in> [\<lambda>x. x \<noteq> None]\<^sub>a conflict_option_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  using size_conflict_code_hnr[FCOMP size_conflict_int_size_conflict]
  unfolding conflict_option_assn_def[symmetric]
  by simp

lemma two_different_multiset_sizeD:
  assumes \<open>a \<in># y\<close> and \<open>ba \<in># y\<close> \<open>a \<noteq> ba\<close>
  shows \<open>Suc 0 < size y\<close> \<open>size y = Suc (Suc (size (y - {#a, ba#})))\<close>
  using assms by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
sepref_thm list_of_mset2_None_code
  is \<open>uncurry2 (PR_CONST list_of_mset2_None_int)\<close>
  :: \<open>[\<lambda>((L, L'), C). C \<noteq> None \<and> L \<in># the C \<and> L' \<in># the C \<and> L \<noteq> L' \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the C)]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
         conflict_option_assn\<^sup>d \<rightarrow> clause_ll_assn *assn conflict_option_assn\<close>
  supply [[goals_limit=1]] size_conflict_def[simp]
  unfolding list_of_mset2_None_int_def size_conflict_def[symmetric]
    array_fold_custom_replicate PR_CONST_def
  by sepref

concrete_definition (in -) list_of_mset2_None_code
   uses isasat_input_bounded_nempty.list_of_mset2_None_code.refine_raw
   is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) list_of_mset2_None_code_def

lemmas list_of_mset2_None_int_hnr[sepref_fr_rules] =
  list_of_mset2_None_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma list_of_mset2_None_hnr[sepref_fr_rules]:
  \<open>(uncurry2 list_of_mset2_None_code, uncurry2 list_of_mset2_None)
   \<in> [\<lambda>((a, b), ba). ba \<noteq> None \<and> a \<in># the ba \<and> b \<in># the ba \<and> a \<noteq> b \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the ba) \<and> distinct_mset (the ba) \<and> a \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> b \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
      unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow>
      clause_ll_assn *assn conflict_option_assn\<close>
  using list_of_mset2_None_int_hnr[unfolded PR_CONST_def, FCOMP list_of_mset2_None_int_list_of_mset2_None]
  by simp

sepref_thm extract_shorter_conflict_list_removed_code
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_removed)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *assn
       option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>
  supply [[goals_limit = 1]] uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
    Pos_unat_lit_assn[sepref_fr_rules]
    Neg_unat_lit_assn[sepref_fr_rules]
  unfolding extract_shorter_conflict_list_removed_def PR_CONST_def
  extract_shorter_conflict_list_heur_def
  lit_of_hd_trail_def[symmetric] Let_def
  zero_uint32_nat_def[symmetric]
  fast_minus_def[symmetric] one_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_removed_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_removed_code.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_removed_code_def

lemmas extract_shorter_conflict_list_removed_code_extract_shorter_conflict_list_removed[sepref_fr_rules] =
  extract_shorter_conflict_list_removed_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

sepref_thm extract_shorter_conflict_l_trivial'
  is \<open>uncurry (PR_CONST extract_shorter_conflict_list_heur)\<close>
  :: \<open>[\<lambda>(M, (b, n, xs)). M \<noteq> []]\<^sub>a
      trail_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow> conflict_option_rel_assn *assn
       option_assn (unat_lit_assn *assn uint32_nat_assn)\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_def PR_CONST_def
  extract_shorter_conflict_list_heur_def
  lit_of_hd_trail_def[symmetric] Let_def one_uint32_nat_def[symmetric]
  fast_minus_def[symmetric]
  by sepref

concrete_definition (in -) extract_shorter_conflict_l_trivial_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_l_trivial'.refine_raw
   is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_l_trivial_code_def

lemmas extract_shorter_conflict_l_trivial_code_wl_D[sepref_fr_rules] =
  extract_shorter_conflict_l_trivial_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

text \<open>
  This is the \<^emph>\<open>direct\<close> composition of the refinement theorems. Only the version lifted to
  state should be used (to get rid of the \<^term>\<open>M\<close> that appears in the refinement relation).
\<close>
lemma extract_shorter_conflict_l_trivial_code_extract_shorter_conflict_l_trivial:
  \<open>(uncurry extract_shorter_conflict_l_trivial_code,
     uncurry (RETURN \<circ>\<circ> extract_shorter_conflict_l_trivial))
    \<in> [\<lambda>(M', D). M' \<noteq> [] \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M' = M \<and>
         -lit_of (hd M) \<in># the D \<and>  0 < get_level M (lit_of (hd M)) \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and>
         distinct_mset (the D) \<and> \<not>tautology (the D)]\<^sub>a
       trail_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> (conflict_with_cls_with_cls_with_highest_assn M)\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel)
       (\<lambda>(M, D). M \<noteq> [] \<and> D \<noteq> None \<and> - lit_of (hd M) \<in># the D \<and> 0 < get_level M (lit_of (hd M)))
       (\<lambda>_. comp_PRE (Id \<times>\<^sub>f option_conflict_rel)
              (\<lambda>(M', D). literals_are_in_\<L>\<^sub>i\<^sub>n (the D) \<and> D \<noteq> None \<and> M = M' \<and> M \<noteq> [] \<and>
                  literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset M) \<and> - lit_of (hd M) \<in># the D \<and>
                  lit_of (hd M) \<notin># the D \<and> distinct_mset (the D) \<and>
                  0 < get_level M (lit_of (hd M)) \<and> \<not> tautology (the D))
              (\<lambda>_ (M, b, n, xs). M \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
    hrp_comp (hrp_comp ((hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a (bool_assn *assn conflict_rel_assn)\<^sup>d)
                       (Id \<times>\<^sub>f option_conflict_rel))
              (Id \<times>\<^sub>f \<langle>Id\<rangle>option_rel) \<rightarrow>
    hr_comp (hr_comp ((bool_assn *assn conflict_rel_assn) *assn
                        option_assn (unat_lit_assn *assn uint32_nat_assn))
                     {((D, L), C). (D, C) \<in> option_conflict_rel \<and> C \<noteq> None \<and>
                      highest_lit M (remove1_mset (- lit_of (hd M)) (the C)) L \<and>
                       (\<forall>L\<in>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l. L < length (snd (snd D)))})
             Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
       hfref_compI_PRE_aux[OF extract_shorter_conflict_l_trivial_code_wl_D[unfolded PR_CONST_def]
          extract_shorter_conflict_list_heur_extract_shorter_conflict_list, of M]
       extract_shorter_conflict_list_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def
    by (auto simp: comp_PRE_def option_conflict_rel_with_cls_def list_mset_rel_def br_def
        map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def[symmetric]
       conflict_with_cls_with_cls_with_highest_assn_def option_conflict_rel_with_cls_with_highest_def
       hr_comp_Id2
    apply (rule arg_cong[of _ _ \<open>hr_comp _\<close>])
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed


sepref_register extract_shorter_conflict_list_heur
sepref_thm extract_shorter_conflict_list_st_int_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>(M,_). M \<noteq> []]\<^sub>a
      twl_st_heur_lookup_conflict_assn\<^sup>d \<rightarrow>
        trail_assn *assn clauses_ll_assn *assn
       nat_assn *assn
       ((bool_assn *assn conflict_rel_assn) *assn option_assn (unat_lit_assn *assn uint32_nat_assn)) *assn
       clause_l_assn *assn
       arrayO_assn (arl_assn nat_assn) *assn
       vmtf_remove_conc *assn phase_saver_conc *assn uint32_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding extract_shorter_conflict_list_st_int_def twl_st_heur_lookup_conflict_assn_def
    PR_CONST_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_list_st_int_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_list_st_int_code.refine_raw
   is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) extract_shorter_conflict_list_st_int_code_def

lemmas extract_shorter_conflict_list_st_int_code[sepref_fr_rules] =
  extract_shorter_conflict_list_st_int_code.refine[of \<A>\<^sub>i\<^sub>n,
      OF isasat_input_bounded_nempty_axioms]

sepref_register extract_shorter_conflict_list_st_int
sepref_thm extract_shorter_conflict_st_trivial_code
  is \<open>PR_CONST extract_shorter_conflict_list_st_int\<close>
  :: \<open>[\<lambda>S. get_trail_wl_heur_conflict S \<noteq> []]\<^sub>a twl_st_heur_lookup_conflict_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding  twl_st_confl_extracted_int_assn_def PR_CONST_def
    extract_shorter_conflict_list_st_int_def twl_st_heur_lookup_conflict_assn_def
  by sepref

concrete_definition (in -) extract_shorter_conflict_st_trivial_code
   uses isasat_input_bounded_nempty.extract_shorter_conflict_st_trivial_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) extract_shorter_conflict_st_trivial_code_def

lemmas extract_shorter_conflict_st_code_refine[sepref_fr_rules] =
   extract_shorter_conflict_st_trivial_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition extract_shorter_conflict_st_trivial_pre where
  \<open>extract_shorter_conflict_st_trivial_pre S \<longleftrightarrow> (get_conflict_wl S \<noteq> None \<and>
          get_trail_wl S \<noteq> [] \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
          - lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S) \<and>
          0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S))) \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S)) \<and>
          literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
          distinct_mset (the (get_conflict_wl S)) \<and> \<not> tautology (the (get_conflict_wl S)))\<close>

lemma extract_shorter_conflict_st_trivial_hnr[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_st_trivial) \<in>
    [extract_shorter_conflict_st_trivial_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
       \<in> [comp_PRE twl_st_heur (\<lambda>S. get_conflict_wl S \<noteq> None)
               (\<lambda>_. comp_PRE twl_st_wl_heur_lookup_conflict_rel
                  (\<lambda>S. get_conflict_wl_heur S \<noteq> None \<and>
                     get_trail_wl_heur S \<noteq> [] \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
                     - lit_of (hd (get_trail_wl_heur S)) \<in># the (get_conflict_wl_heur S) \<and>
                     0 < get_level (get_trail_wl_heur S) (lit_of (hd (get_trail_wl_heur S))) \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl_heur S)) \<and>
                     literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and> distinct_mset (the (get_conflict_wl_heur S)) \<and> \<not> tautology (the (get_conflict_wl_heur S)))
                 (\<lambda>_ S. get_trail_wl_heur_conflict S \<noteq> [])
              (\<lambda>_. True))
       (\<lambda>_. True)]\<^sub>a
      hrp_comp (hrp_comp (twl_st_heur_lookup_conflict_assn\<^sup>d) twl_st_wl_heur_lookup_conflict_rel) twl_st_heur \<rightarrow>
     hr_comp (hr_comp twl_st_confl_extracted_int_assn twl_st_heur_confl_extracted) twl_st_heur_no_clvls\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF
        hfref_compI_PRE_aux[OF extract_shorter_conflict_st_code_refine[unfolded PR_CONST_def]
           extract_shorter_conflict_list_st_int_extract_shorter_conflict_st_trivial_heur]
         extract_shorter_conflict_l_trivial_int_extract_shorter_conflict_l_trivial] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def twl_st_wl_heur_lookup_conflict_rel_def extract_shorter_conflict_st_trivial_pre_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
      map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
       twl_st_confl_extracted_assn_def hr_comp_assoc twl_st_assn_confl_assn ..
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre:
  assumes \<open>extract_shorter_conflict_wl_pre S\<close>
  shows \<open>extract_shorter_conflict_st_trivial_pre S\<close>
proof -
  have
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    confl: \<open>get_conflict_wl S \<noteq> None\<close> and
    confl_nempty: \<open>get_conflict_wl S \<noteq> Some {#}\<close> and
    n_s: \<open>no_skip S\<close> and
    n_r: \<open>no_resolve S\<close> and
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n S\<close>
    using assms unfolding extract_shorter_conflict_wl_pre_def by fast+

  have invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using struct_invs unfolding twl_struct_invs_def by fast
  have
    conf: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None S))\<close> and
    lev_inv: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None S))\<close>
    using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def by fast+
  have lits_conf: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits confl struct_invs] .

  have trail: \<open>get_trail_wl S \<noteq> []\<close>
    using conf confl confl_nempty unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def apply (cases S)
    by auto
  have uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># {#L \<in># the (get_conflict_wl S).
         0 < get_level (get_trail_wl S) L#}\<close>
    using cdcl\<^sub>W_restart_mset.conflict_minimisation_level_0(2)[of \<open>state\<^sub>W_of (twl_st_of_wl None S)\<close>]
     n_s n_r confl invs stgy_invs trail confl_nempty unfolding no_skip_def no_resolve_def twl_stgy_invs_def
    by (cases S) simp
  have lev_L: \<open>0 < get_level (get_trail_wl S) (lit_of (hd (get_trail_wl S)))\<close> and
    uL_D: \<open>- lit_of (hd (get_trail_wl S)) \<in># the (get_conflict_wl S)\<close>
    using uL_D by auto

  have lits_trail: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n (lit_of `# mset (get_trail_wl S))\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] .
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl S))\<close>
    using dist confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def)

  have tr: \<open>get_trail_wl S \<Turnstile>as CNot (the (get_conflict_wl S))\<close>
    using conf confl by (cases S) (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def)
  have cons: \<open>consistent_interp (lits_of_l (get_trail_wl S))\<close>
    using lev_inv  unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (cases S) (auto dest!: distinct_consistent_interp)
  have tauto: \<open>\<not> tautology (the (get_conflict_wl S))\<close>
    using consistent_CNot_not_tautology[OF cons tr[unfolded true_annots_true_cls]] .
  show ?thesis
    using lits_conf confl trail lits_trail uL_D lev_L dist_confl tauto
    unfolding extract_shorter_conflict_st_trivial_pre_def
    by (intro conjI) fast+
qed

lemma extract_shorter_conflict_wl_code_extract_shorter_conflict_wl[sepref_fr_rules]:
  \<open>(extract_shorter_conflict_st_trivial_code, extract_shorter_conflict_wl)
    \<in> [extract_shorter_conflict_wl_pre]\<^sub>a
       twl_st_assn\<^sup>d \<rightarrow> twl_st_confl_extracted_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE Id
     (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
          twl_stgy_invs (twl_st_of_wl None S) \<and>
          get_conflict_wl S \<noteq> None \<and>
          no_skip S \<and>
          no_resolve S \<and> get_conflict_wl S \<noteq> Some {#})
     (\<lambda>_. extract_shorter_conflict_st_trivial_pre)
     (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_assn\<^sup>d)
                    Id \<rightarrow> hr_comp twl_st_confl_extracted_assn
                           Id\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF extract_shorter_conflict_st_trivial_hnr[unfolded PR_CONST_def]
        extract_shorter_conflict_st_trivial_extract_shorter_conflict_wl] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    using extract_shorter_conflict_wl_pre_extract_shorter_conflict_st_trivial_pre[of x]
    unfolding comp_PRE_def extract_shorter_conflict_wl_pre_def
    by (auto simp: comp_PRE_def twl_st_heur_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by auto
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep by auto

  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed


definition rescore_clause :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (vmtf_remove_int \<times> phase_saver) nres\<close> where
\<open>rescore_clause C M vm \<phi> = SPEC (\<lambda>(vm', \<phi>' :: bool list). vm' \<in> vmtf M \<and> phase_saving \<phi>')\<close>

definition (in isasat_input_ops) vmtf_rescore_body
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
    (nat \<times> vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore_body C _ vm \<phi> = do {
         WHILE\<^sub>T\<^bsup>\<lambda>(i, vm, \<phi>). i \<le> length C  \<and>
            (\<forall>c \<in> set C. atm_of c < length \<phi> \<and> atm_of c < length (fst (fst vm)))\<^esup>
           (\<lambda>(i, vm, \<phi>). i < length C)
           (\<lambda>(i, vm, \<phi>). do {
               ASSERT(i < length C);
               let vm' = vmtf_mark_to_rescore (atm_of (C!i)) vm;
               let \<phi>' = save_phase_inv (C!i) \<phi>;
               RETURN(i+1, vm', \<phi>')
             })
           (0, vm, \<phi>)
    }\<close>

definition (in isasat_input_ops) vmtf_rescore
 :: \<open>nat clause_l \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> phase_saver \<Rightarrow>
       (vmtf_remove_int \<times> phase_saver) nres\<close>
where
  \<open>vmtf_rescore C M vm \<phi> = do {
      (_, vm, \<phi>) \<leftarrow> vmtf_rescore_body C M vm \<phi>;
      RETURN (vm, \<phi>)
    }\<close>

sepref_thm vmtf_rescore_code
  is \<open>uncurry3 vmtf_rescore\<close>
  :: \<open>(array_assn unat_lit_assn)\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>\<^sub>a
       vmtf_remove_conc *assn phase_saver_conc\<close>
  unfolding vmtf_rescore_def vmtf_mark_to_rescore_and_unset_def save_phase_inv_def vmtf_mark_to_rescore_def vmtf_unset_def
  vmtf_rescore_body_def
  supply [[goals_limit = 1]] is_None_def[simp] fold_is_None[simp]
  by sepref

concrete_definition (in -) vmtf_rescore_code
   uses isasat_input_bounded_nempty.vmtf_rescore_code.refine_raw
   is \<open>(uncurry3 ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_rescore_code_def

lemmas vmtf_rescore_code_refine[sepref_fr_rules] =
   vmtf_rescore_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

(* TODO Move *)
lemma vmtf_append_remove_iff':
  \<open>(vm, b @ [L]) \<in> vmtf M \<longleftrightarrow>
     L \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l \<and> (vm, b) \<in> vmtf M\<close>
  by (cases vm) (auto simp: vmtf_append_remove_iff)
(* ENd Move *)
lemma vmtf_rescore_score_clause:
  \<open>(uncurry3 vmtf_rescore, uncurry3 rescore_clause) \<in>
     [\<lambda>(((C, M), vm), \<phi>). literals_are_in_\<L>\<^sub>i\<^sub>n (mset C) \<and> vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>f
     (\<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<times>\<^sub>f Id \<times>\<^sub>f Id) \<rightarrow> \<langle>Id \<times>\<^sub>f Id\<rangle> nres_rel\<close>
proof -
  have H: \<open>vmtf_rescore_body C M vm \<phi> \<le>
        SPEC (\<lambda>(n :: nat, vm', \<phi>' :: bool list). phase_saving \<phi>' \<and> vm' \<in> vmtf M)\<close>
    if M: \<open>vm \<in> vmtf M\<close>\<open>phase_saving \<phi>\<close> and C: \<open>\<forall>c\<in>set C. atm_of c \<in> atms_of \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
    for C vm \<phi> M
    unfolding vmtf_rescore_body_def vmtf_mark_to_rescore_def
    apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length C - i)\<close> and
       I' = \<open>\<lambda>(i, vm', \<phi>'). phase_saving \<phi>' \<and> vm' \<in> vmtf M\<close>])
    subgoal by auto
    subgoal by auto
    subgoal using C M by (auto simp: vmtf_def phase_saving_def)
    subgoal using C M by auto
    subgoal using M by auto
    subgoal by auto
    subgoal unfolding save_phase_inv_def by auto
    subgoal using C unfolding phase_saving_def save_phase_inv_def by auto
    subgoal unfolding save_phase_inv_def phase_saving_def by auto
    subgoal using C by (auto simp: vmtf_append_remove_iff')
    subgoal by auto
    done
  have K: \<open>((a, b),(a', b')) \<in> A \<times>\<^sub>f B \<longleftrightarrow> (a, a') \<in> A \<and> (b, b') \<in> B\<close> for a b a' b' A B
    by auto
  show ?thesis
    unfolding vmtf_rescore_def rescore_clause_def uncurry_def
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule bind_refine_spec)
     prefer 2
     apply (subst (asm) K)
     apply (rule H; auto)
    subgoal
      by (meson atm_of_lit_in_atms_of contra_subsetD in_all_lits_of_m_ain_atms_of_iff
          in_multiset_in_set literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    subgoal by auto
    done
qed

lemma vmtf_rescore_code_rescore_clause[sepref_fr_rules]:
  \<open>(uncurry3 vmtf_rescore_code, uncurry3 (PR_CONST rescore_clause))
     \<in> [\<lambda>(((b, a), c), d). literals_are_in_\<L>\<^sub>i\<^sub>n (mset b) \<and> c \<in> vmtf a \<and>
         phase_saving d]\<^sub>a
       clause_ll_assn\<^sup>k *\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d *\<^sub>a phase_saver_conc\<^sup>d \<rightarrow>
        vmtf_remove_conc *assn phase_saver_conc\<close>
  using vmtf_rescore_code_refine[FCOMP vmtf_rescore_score_clause]
  by auto

definition vmtf_flush' where
   \<open>vmtf_flush' _ = vmtf_flush\<close>

sepref_thm vmtf_flush_all_code
  is \<open>uncurry vmtf_flush'\<close>
  :: \<open>[\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
  supply [[goals_limit=1]] trail_dump_code_refine[sepref_fr_rules]
  unfolding vmtf_flush'_def
  by sepref

concrete_definition (in -) vmtf_flush_all_code
   uses isasat_input_bounded_nempty.vmtf_flush_all_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_flush_all_code_def

lemmas vmtf_flush_all_code_hnr[sepref_fr_rules] =
   vmtf_flush_all_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


definition flush :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow> vmtf_remove_int nres\<close> where
\<open>flush M _ = SPEC (\<lambda>vm'. vm' \<in> vmtf M)\<close>

lemma trail_bump_rescore:
  \<open>(uncurry vmtf_flush', uncurry flush) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f Id \<times>\<^sub>r Id  \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding vmtf_flush'_def flush_def
  apply (intro nres_relI frefI)
  apply clarify
  subgoal for a aa ab ac b ba ad ae af ag bb bc
    using vmtf_change_to_remove_order
    by auto
  done

lemma trail_dump_code_rescore[sepref_fr_rules]:
   \<open>(uncurry vmtf_flush_all_code, uncurry (PR_CONST flush)) \<in> [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>a
        trail_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow> vmtf_remove_conc\<close>
   (is \<open>_ \<in> [?cond]\<^sub>a ?pre \<rightarrow> ?im\<close>)
  using vmtf_flush_all_code_hnr[FCOMP trail_bump_rescore] by simp

definition st_remove_highest_lvl_from_confl :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
   \<open>st_remove_highest_lvl_from_confl S = S\<close>

definition st_remove_highest_lvl_from_confl_heur :: \<open>twl_st_wl_confl_extracted_int \<Rightarrow> twl_st_wl_heur_lookup_conflict\<close> where
  \<open>st_remove_highest_lvl_from_confl_heur = (\<lambda>(M, N, U, (D, _), oth). (M, N, U, D, oth))\<close>


type_synonym (in -) twl_st_wl_W_int =
  \<open>(nat,nat) ann_lits \<times> nat clause_l list \<times> nat \<times>
    nat clause option \<times> nat clauses \<times> nat clauses \<times> nat clause \<times> (nat literal \<Rightarrow> nat list)\<close>

definition twl_st_wl_W_conflict :: \<open>(twl_st_wl_heur_lookup_conflict \<times> twl_st_wl_W_int) set\<close>where
  \<open>twl_st_wl_W_conflict =
   {((M', N', U', D', Q', W', vm, \<phi>, clvls), M, N, U, D, NP, UP, Q, W).
     M = M' \<and>
     N' = N \<and>
     U' = U \<and>
     (D', D) \<in> option_conflict_rel \<and>
     Q' = Q \<and>
     (W', W) \<in> \<langle>Id\<rangle>map_fun_rel D\<^sub>0 \<and>
     vm \<in> vmtf M \<and> phase_saving \<phi> \<and> no_dup M}\<close>

lemma twl_st_wl_W_conflict_alt_def:
  \<open>twl_st_wl_W_conflict =
     (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r option_conflict_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) O twl_st_heur_no_clvls\<close>
  unfolding twl_st_wl_W_conflict_def twl_st_heur_no_clvls_def
  by force

definition twl_st_W_conflict_int_assn :: \<open>twl_st_wl_heur_lookup_conflict \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_W_conflict_int_assn =
  (trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_rel_assn *assn
  clause_l_assn *assn
  arrayO_assn (arl_assn nat_assn) *assn
  vmtf_remove_conc *assn phase_saver_conc *assn uint32_nat_assn
  )\<close>

lemma st_remove_highest_lvl_from_confl_heur_st_remove_highest_lvl_from_confl:
  \<open>(RETURN o st_remove_highest_lvl_from_confl_heur, RETURN o st_remove_highest_lvl_from_confl) \<in>
   (twl_st_heur_confl_extracted2 L O twl_st_heur_no_clvls) \<rightarrow>\<^sub>f \<langle>twl_st_wl_W_conflict\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: st_remove_highest_lvl_from_confl_heur_def st_remove_highest_lvl_from_confl_def
      twl_st_wl_W_conflict_def twl_st_heur_confl_extracted2_def twl_st_heur_no_clvls_def
      option_conflict_rel_with_cls_with_highest2_def)


sepref_thm st_remove_highest_lvl_from_confl_code
  is \<open>RETURN o st_remove_highest_lvl_from_confl_heur\<close>
  :: \<open>twl_st_confl_extracted_int_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_W_conflict_int_assn\<close>
  unfolding st_remove_highest_lvl_from_confl_heur_def twl_st_confl_extracted_int_assn_def
  twl_st_W_conflict_int_assn_def
  by sepref


concrete_definition (in -) st_remove_highest_lvl_from_confl_code
   uses isasat_input_bounded_nempty.st_remove_highest_lvl_from_confl_code.refine_raw
   is \<open>(?f, _)\<in>_\<close>

prepare_code_thms (in -) st_remove_highest_lvl_from_confl_code_def

lemmas st_remove_highest_lvl_from_confl_heur_hnr[sepref_fr_rules] =
   st_remove_highest_lvl_from_confl_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) twl_st_assn_no_clvls :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll_trail \<Rightarrow> assn\<close> where
\<open>twl_st_assn_no_clvls = hr_comp twl_st_heur_assn twl_st_heur_no_clvls\<close>

lemma twl_st_assn_twl_st_wl_W_conflict:
  \<open>twl_st_assn_no_clvls = hr_comp twl_st_W_conflict_int_assn twl_st_wl_W_conflict\<close>
  unfolding twl_st_assn_no_clvls_def twl_st_wl_W_conflict_alt_def twl_st_W_conflict_int_assn_def
    twl_st_heur_assn_def hr_comp_assoc[symmetric] conflict_option_assn_def
  by simp

lemma st_remove_highest_lvl_from_confl_hnr[sepref_fr_rules]:
  \<open>(st_remove_highest_lvl_from_confl_code, RETURN \<circ> st_remove_highest_lvl_from_confl)
   \<in> (twl_st_confl_extracted_assn2 L)\<^sup>d \<rightarrow>\<^sub>a twl_st_assn_no_clvls\<close>
  using st_remove_highest_lvl_from_confl_heur_hnr[FCOMP st_remove_highest_lvl_from_confl_heur_st_remove_highest_lvl_from_confl]
  unfolding twl_st_confl_extracted_assn2_def[symmetric] twl_st_assn_twl_st_wl_W_conflict[symmetric]
  by simp

definition propgate_bt_wl_D_heur
  :: \<open>nat literal \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propgate_bt_wl_D_heur = (\<lambda>L L' (M, N, U, D, Q, W, vm, \<phi>, _). do {
      (D'', C) \<leftarrow> list_of_mset2_None (- L) L' D;
      ASSERT(literals_are_in_\<L>\<^sub>i\<^sub>n (mset D''));
      (vm, \<phi>) \<leftarrow> rescore_clause D'' M vm \<phi>;
      vm \<leftarrow> flush M vm;
      let W = W[nat_of_lit (- L) := W ! nat_of_lit (- L) @ [length N]];
      let W = W[nat_of_lit L' := W!nat_of_lit L' @ [length N]];
      RETURN (Propagated (- L) (length N) # M, N @ [D''], U, C, {#L#}, W, vm, \<phi>, zero_uint32_nat)
    })\<close>

sepref_register list_of_mset2_None rescore_clause flush
sepref_thm propgate_bt_wl_D_code
  is \<open>uncurry2 (PR_CONST propgate_bt_wl_D_heur)\<close>
  :: \<open>[\<lambda>((L, L'), S). get_conflict_wl_heur S \<noteq> None \<and> -L \<in># the (get_conflict_wl_heur S) \<and>
         L' \<in># the (get_conflict_wl_heur S) \<and> -L \<noteq> L' \<and>
       literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
       distinct_mset (the (get_conflict_wl_heur S)) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
       undefined_lit (get_trail_wl_heur S) L \<and>
     nat_of_lit (-L) < length (get_watched_list_heur S) \<and>
     nat_of_lit L' < length (get_watched_list_heur S) \<and>
     get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S) \<and>
     phase_saving (get_phase_saver_heur S)]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] uminus_\<A>\<^sub>i\<^sub>n_iff[simp] image_image[simp] append_ll_def[simp]
  rescore_clause_def[simp] flush_def[simp]
  unfolding propgate_bt_wl_D_heur_def twl_st_heur_assn_def cons_trail_Propagated_def[symmetric]
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] append_ll_def[symmetric]
    cons_trail_Propagated_def[symmetric] PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propgate_bt_wl_D_code
  uses isasat_input_bounded_nempty.propgate_bt_wl_D_code.refine_raw
  is \<open>(uncurry2 ?f, _) \<in> _\<close>

prepare_code_thms (in -) propgate_bt_wl_D_code_def

lemmas propgate_bt_wl_D_heur_hnr[sepref_fr_rules] =
  propgate_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma propgate_bt_wl_D_heur_propgate_bt_wl_D:
  \<open>(uncurry2 propgate_bt_wl_D_heur, uncurry2 propgate_bt_wl_D) \<in>
     [\<lambda>((L, L'), S). get_conflict_wl S \<noteq> None \<and> -L \<noteq> L' \<and> undefined_lit (get_trail_wl S) L \<and>
    literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S))]\<^sub>f
     Id \<times>\<^sub>f Id \<times>\<^sub>f twl_st_heur_no_clvls \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding propgate_bt_wl_D_heur_def propgate_bt_wl_D_alt_def twl_st_heur_def list_of_mset2_None_def
    twl_st_heur_no_clvls_def uncurry_def
  apply clarify
  apply refine_vcg
  apply
    (auto simp: propgate_bt_wl_D_heur_def propgate_bt_wl_D_def Let_def
      list_of_mset2_def list_of_mset2_None_def RES_RETURN_RES2 RES_RETURN_RES twl_st_heur_def
      map_fun_rel_def rescore_clause_def flush_def
      intro!: RES_refine vmtf_consD)
  done

definition propgate_bt_wl_D_pre :: \<open>(nat literal \<times> nat literal) \<times> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>propgate_bt_wl_D_pre = (\<lambda>((L, L'), S).
         get_conflict_wl S \<noteq> None \<and>
         - L \<in># the (get_conflict_wl S) \<and>
         L' \<in># the (get_conflict_wl S) \<and>
         - L \<noteq> L' \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)) \<and>
         distinct_mset (the (get_conflict_wl S)) \<and>
         L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         undefined_lit (get_trail_wl S) L)\<close>

lemma propgate_bt_wl_D_hnr[sepref_fr_rules]:
  \<open>(uncurry2 propgate_bt_wl_D_code, uncurry2 propgate_bt_wl_D) \<in>
    [propgate_bt_wl_D_pre]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn_no_clvls\<^sup>d \<rightarrow>
        twl_st_assn\<close>
    (is \<open>?fun \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?fun \<in>
     [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
     (\<lambda>((L, L'), S).
         get_conflict_wl S \<noteq> None \<and>
         - L \<noteq> L' \<and>
         undefined_lit (get_trail_wl S) L \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl S)))
     (\<lambda>_ ((L, L'), S).
         get_conflict_wl_heur S \<noteq> None \<and>
         - L \<in># the (get_conflict_wl_heur S) \<and>
         L' \<in># the (get_conflict_wl_heur S) \<and>
         - L \<noteq> L' \<and>
         literals_are_in_\<L>\<^sub>i\<^sub>n (the (get_conflict_wl_heur S)) \<and>
         distinct_mset (the (get_conflict_wl_heur S)) \<and>
         L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         L' \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and>
         undefined_lit (get_trail_wl_heur S) L \<and>
         nat_of_lit (- L) < length (get_watched_list_heur S) \<and>
         nat_of_lit L' < length (get_watched_list_heur S) \<and>
         local.get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S) \<and>
         phase_saving (get_phase_saver_heur S))
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a
                      twl_st_heur_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f nat_lit_lit_rel \<times>\<^sub>f
                      twl_st_heur_no_clvls) \<rightarrow> hr_comp twl_st_heur_assn twl_st_heur
\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propgate_bt_wl_D_heur_hnr[unfolded PR_CONST_def]
       propgate_bt_wl_D_heur_propgate_bt_wl_D]
    .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that unfolding comp_PRE_def twl_st_heur_def map_fun_rel_def propgate_bt_wl_D_pre_def
    twl_st_heur_no_clvls_def
    by (auto simp: image_image uminus_\<A>\<^sub>i\<^sub>n_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    twl_st_assn_no_clvls_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed


lemma backtrack_wl_D_alt_def:
  \<open>backtrack_wl_D S =
    do {
      ASSERT(backtrack_wl_D_inv S);
      let L = lit_of (hd (get_trail_wl S));
      S \<leftarrow> extract_shorter_conflict_wl S;
      S \<leftarrow> find_decomp_wl L S;

      if size (the (get_conflict_wl S)) > 1
      then do {
        L' \<leftarrow> find_lit_of_max_level_wl S L;
        propgate_bt_wl_D L L' (st_remove_highest_lvl_from_confl S)
      }
      else do {
        let S = st_remove_highest_lvl_from_confl S;
        propgate_unit_bt_wl_D L S
     }
  }\<close>
  unfolding backtrack_wl_D_def st_remove_highest_lvl_from_confl_def
    st_remove_highest_lvl_from_confl_def Let_def
  by auto

lemma backtrack_wl_D_helper3:
  assumes
    invs: \<open>backtrack_wl_D_inv x\<close> and
    extract_shorter: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close> and
    decomp: \<open>RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc\<close> and
    \<open>Suc 0 < size (the (get_conflict_wl xd))\<close> and
    lit2: \<open>RETURN xf \<le> find_lit_of_max_level_wl xd (lit_of_hd_trail_st x)\<close> and
    \<open>(a, lit_of_hd_trail_st x) \<in> unat_lit_rel\<close> and
    \<open>(aa, xf) \<in> unat_lit_rel\<close>
  shows \<open>propgate_bt_wl_D_pre
          ((lit_of_hd_trail_st x, xf), xd)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close>
    by (cases x)
  obtain D' where
    xc: \<open>xc = (M, N, U, Some D', NP, UP, W, Q)\<close> and
    D'_D: \<open>D' \<subseteq># the D\<close> and
    \<open>clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D'\<close> and
    uM_D': \<open>- lit_of (hd M) \<in># D'\<close>
    using extract_shorter unfolding x extract_shorter_conflict_wl_def
    by (cases xc) (auto simp: x extract_shorter_conflict_wl_def)

  obtain K M1 M2 where
     xd: \<open>xd = (M1, N, U, Some D', NP, UP, W, Q)\<close> and
     decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
     \<open>get_level M K = get_maximum_level M (remove1_mset (- lit_of_hd_trail_st x) D') + 1\<close>
    using decomp unfolding xc find_decomp_wl_def by auto
  have
    xf: \<open>xf \<in># remove1_mset (- lit_of_hd_trail_st x) D'\<close> and
    lev_xf: \<open>get_level M1 xf = get_maximum_level M1 (remove1_mset (- lit_of_hd_trail_st x) D')\<close>
    using lit2 unfolding find_lit_of_max_level_wl_def xd by simp_all
  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x\<close> and
    D: \<open>D \<noteq> None\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x)\<close> and
    M_nempty: \<open>M \<noteq> []\<close>
    using invs unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def x
    by auto
  have lits_D': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct_invs] D
      literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF _ D'_D] unfolding xd x by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None x))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None x))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>no_dup M\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: x)
  then have undef: \<open>undefined_lit M1 (lit_of_hd_trail_st x)\<close>
    using decomp M_nempty unfolding x lit_of_hd_trail_st_def
    apply (cases M)
     apply (auto dest!: get_all_ann_decomposition_exists_prepend)
    apply (case_tac c; case_tac M2)
       apply auto
    done
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl xd))\<close>
    using dist D distinct_mset_mono[OF D'_D] unfolding x xd cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by auto
  then have diff: \<open>- lit_of_hd_trail_st x \<noteq> xf\<close>
    using lev_xf M_nempty uM_D' xf unfolding x lit_of_hd_trail_st_def xd
    by (cases M) (auto dest!: multi_member_split)
  show ?thesis
    unfolding propgate_bt_wl_D_pre_def
    apply clarify
    apply (intro conjI)
    subgoal
      unfolding xd by simp
    subgoal using uM_D' unfolding xd x lit_of_hd_trail_st_def by auto
    subgoal using xf by (auto simp: x xd dest!: in_diffD)
    subgoal using diff .
    subgoal using lits_D' unfolding xd by auto
    subgoal using dist_confl .
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] M_nempty
      unfolding x by (cases M) (auto simp: lit_of_hd_trail_st_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal
      using xf lits_D' by (auto dest!: multi_member_split in_diffD simp: literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    subgoal using undef unfolding x xd by auto
    done
qed

definition remove_last :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option nres\<close> where
  \<open>remove_last _ _  = SPEC(op = None)\<close>

definition propgate_unit_bt_wl_D_int :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>propgate_unit_bt_wl_D_int = (\<lambda>L (M, N, U, D, Q, W, vm, \<phi>). do {
      D \<leftarrow> remove_last L D;
      vm \<leftarrow> flush M vm;
      RETURN (Propagated (- L) 0 # M, N, U, D, {#L#}, W, vm, \<phi>)})\<close>

lemma propgate_unit_bt_wl_D_int_propgate_unit_bt_wl_D:
  \<open>(uncurry propgate_unit_bt_wl_D_int, uncurry propgate_unit_bt_wl_D) \<in>
     [\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
        size(the (get_conflict_wl S)) = 1]\<^sub>f
     Id \<times>\<^sub>f twl_st_heur_no_clvls \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: propgate_unit_bt_wl_D_int_def propgate_unit_bt_wl_D_def RES_RETURN_RES
      twl_st_heur_def flush_def RES_RES_RETURN_RES single_of_mset_def remove_last_def
      twl_st_heur_no_clvls_def
      intro!: RES_refine vmtf_consD size_1_singleton_mset)

definition remove_last_int :: \<open>nat literal \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>remove_last_int = (\<lambda>L (b, n, xs). (True, 0, xs[atm_of L := None]))\<close>

lemma remove_last_int_remove_last:
  \<open>(uncurry (RETURN oo remove_last_int), uncurry remove_last) \<in>
    [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>f Id \<times>\<^sub>r option_conflict_rel \<rightarrow>
      \<langle>option_conflict_rel\<rangle> nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (clarify dest!: size_1_singleton_mset)
  subgoal for a aa ab b ac ba y L
    using mset_as_position_remove[of b \<open>{#L#}\<close> \<open>atm_of L\<close>]
    by (cases L)
     (auto simp: remove_last_int_def remove_last_def option_conflict_rel_def
        RETURN_RES_refine_iff conflict_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       uminus_lit_swap)
  done

sepref_thm remove_last_code
  is \<open>uncurry (RETURN oo (PR_CONST remove_last_int))\<close>
  :: \<open>[\<lambda>(L, (b, n, xs)). atm_of L < length xs]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d \<rightarrow>
     conflict_option_rel_assn\<close>
  supply [[goals_limit=1]] uint32_nat_assn_zero_uint32_nat[sepref_fr_rules]
  unfolding remove_last_int_def PR_CONST_def zero_uint32_nat_def[symmetric]
  by sepref

concrete_definition (in -) remove_last_code
   uses isasat_input_bounded_nempty.remove_last_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) remove_last_code_def

lemmas remove_last_int_hnr[sepref_fr_rules] =
   remove_last_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

theorem remove_last_hnr[sepref_fr_rules]:
  \<open>(uncurry remove_last_code, uncurry remove_last)
    \<in> [\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a conflict_option_assn\<^sup>d \<rightarrow> conflict_option_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f option_conflict_rel)
       (\<lambda>(L, D). D \<noteq> None \<and> -L \<in># the D \<and> size (the D) = 1 \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)
       (\<lambda>_ (L, b, n, xs). atm_of L < length xs)
       (\<lambda>_. True)]\<^sub>a
     hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a conflict_option_rel_assn\<^sup>d)
              (nat_lit_lit_rel \<times>\<^sub>f option_conflict_rel) \<rightarrow>
    hr_comp conflict_option_rel_assn option_conflict_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF remove_last_int_hnr[unfolded PR_CONST_def]
    remove_last_int_remove_last] .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def option_conflict_rel_def conflict_rel_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep conflict_option_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

sepref_thm propgate_unit_bt_wl_D_code
  is \<open>uncurry (PR_CONST propgate_unit_bt_wl_D_int)\<close>
  :: \<open>[\<lambda>(L, S). get_conflict_wl_heur S \<noteq> None \<and> size (the (get_conflict_wl_heur S)) = 1 \<and>
        undefined_lit (get_trail_wl_heur S) L \<and>
         -L \<in># the (get_conflict_wl_heur S) \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S)]\<^sub>a
   unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit = 1]] flush_def[simp] image_image[simp] uminus_\<A>\<^sub>i\<^sub>n_iff[simp]
  unfolding propgate_unit_bt_wl_D_int_def cons_trail_Propagated_def[symmetric] twl_st_heur_assn_def
  PR_CONST_def
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) propgate_unit_bt_wl_D_code
  uses isasat_input_bounded_nempty.propgate_unit_bt_wl_D_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) propgate_unit_bt_wl_D_code_def

lemmas propgate_unit_bt_wl_D_int_hnr[sepref_fr_rules] =
  propgate_unit_bt_wl_D_code.refine[OF isasat_input_bounded_nempty_axioms]

definition propgate_unit_bt_wl_D_pre :: \<open>nat literal \<times> nat twl_st_wl \<Rightarrow> bool\<close> where
   \<open>propgate_unit_bt_wl_D_pre =
      (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
        size(the (get_conflict_wl S)) = 1 \<and> -L \<in># the (get_conflict_wl S) \<and>
        L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l)\<close>

theorem propgate_unit_bt_wl_D_hnr[sepref_fr_rules]:
  \<open>(uncurry propgate_unit_bt_wl_D_code, uncurry propgate_unit_bt_wl_D)
    \<in> [propgate_unit_bt_wl_D_pre]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn_no_clvls\<^sup>d \<rightarrow> twl_st_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in>
    [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls)
       (\<lambda>(L, S). get_conflict_wl S \<noteq> None \<and> undefined_lit (get_trail_wl S) L \<and>
           size (the (get_conflict_wl S)) = 1)
       (\<lambda>_ (L, S). get_conflict_wl_heur S \<noteq> None \<and> size (the (get_conflict_wl_heur S)) = 1 \<and>
           undefined_lit (get_trail_wl_heur S) L \<and> -L \<in># the (get_conflict_wl_heur S) \<and>
           L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<and> local.get_vmtf_heur S \<in> vmtf (get_trail_wl_heur S))
       (\<lambda>_. True)]\<^sub>a
   hrp_comp (unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d) (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur_no_clvls) \<rightarrow>
   hr_comp twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF propgate_unit_bt_wl_D_int_hnr[unfolded PR_CONST_def]
    propgate_unit_bt_wl_D_int_propgate_unit_bt_wl_D]  .
  have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
    using that by (auto simp: comp_PRE_def twl_st_heur_def  twl_st_heur_no_clvls_def
        in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff propgate_unit_bt_wl_D_pre_def)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def twl_st_assn_no_clvls_def
    by simp
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f PR_CONST_def apply assumption
    using pre ..
qed

lemma backtrack_wl_D_helper4[simp]:
  assumes
    invs: \<open>backtrack_wl_D_inv x\<close> and
    extract_shorter: \<open>RETURN xc \<le> extract_shorter_conflict_wl x\<close> and
    decomp: \<open>RETURN xd \<le> find_decomp_wl (lit_of_hd_trail_st x) xc\<close> and
    size: \<open>\<not> Suc 0 < size (the (get_conflict_wl xd))\<close>
  shows \<open>propgate_unit_bt_wl_D_pre
          (lit_of_hd_trail_st x, xd)\<close>
proof -
  obtain M N U D NP UP W Q where
    x: \<open>x = (M, N, U, D, NP, UP, W, Q)\<close>
    by (cases x)
  obtain D' where
    xc: \<open>xc = (M, N, U, Some D', NP, UP, W, Q)\<close> and
    D'_D: \<open>D' \<subseteq># the D\<close> and
    \<open>clause `# twl_clause_of `# mset (tl N) + NP + UP \<Turnstile>pm D'\<close> and
    uM_D': \<open>- lit_of (hd M) \<in># D'\<close>
    using extract_shorter unfolding x extract_shorter_conflict_wl_def
    by (cases xc) (auto simp: x extract_shorter_conflict_wl_def)

  obtain K M1 M2 where
     xd: \<open>xd = (M1, N, U, Some D', NP, UP, W, Q)\<close> and
     decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition M)\<close> and
     \<open>get_level M K = get_maximum_level M (remove1_mset (- lit_of_hd_trail_st x) D') + 1\<close>
    using decomp unfolding xc find_decomp_wl_def by auto

  have
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n x\<close> and
    D: \<open>D \<noteq> None\<close> \<open>D \<noteq> Some {#}\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of_wl None x)\<close> and
    M_nempty: \<open>M \<noteq> []\<close>
    using invs unfolding backtrack_wl_D_inv_def backtrack_wl_inv_def backtrack_l_inv_def x
    by auto
  have lits_D': \<open>literals_are_in_\<L>\<^sub>i\<^sub>n D'\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_conflict_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits _ struct_invs] D
      literals_are_in_\<L>\<^sub>i\<^sub>n_mono[OF _ D'_D] unfolding xd x by auto
  have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv (state\<^sub>W_of (twl_st_of_wl None x))\<close> and
    dist: \<open>cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state (state\<^sub>W_of (twl_st_of_wl None x))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
    by fast+
  then have \<open>no_dup M\<close>
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: x)
  then have undef: \<open>undefined_lit M1 (lit_of_hd_trail_st x)\<close>
    using decomp M_nempty unfolding x lit_of_hd_trail_st_def
    apply (cases M)
     apply (auto dest!: get_all_ann_decomposition_exists_prepend)
    apply (case_tac c; case_tac M2)
       apply auto
    done
  have dist_confl: \<open>distinct_mset (the (get_conflict_wl xd))\<close>
    using dist D distinct_mset_mono[OF D'_D] unfolding x xd cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def
    by auto
  show ?thesis
    unfolding propgate_unit_bt_wl_D_pre_def
    apply clarify
    apply (intro conjI)
    subgoal unfolding xd by simp
    subgoal using undef unfolding x xd by auto
    subgoal using size uM_D' by (cases D') (auto simp: x xd)
    subgoal using uM_D' unfolding xd by (auto simp: lit_of_hd_trail_st_def x)
    subgoal
      using literals_are_\<L>\<^sub>i\<^sub>n_trail_literals_are_in_\<L>\<^sub>i\<^sub>n[OF lits struct_invs] M_nempty
      unfolding x by (cases M) (auto simp: lit_of_hd_trail_st_def literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset)
    done
qed
end

setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close>

context isasat_input_bounded_nempty
begin

sepref_register find_lit_of_max_level_wl propgate_bt_wl_D propgate_unit_bt_wl_D
sepref_register backtrack_wl_D
sepref_thm backtrack_wl_D
  is \<open>PR_CONST backtrack_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  supply [[goals_limit=1]] backtrack_wl_D_invD[simp] backtrack_wl_D_inv_find_decomp_wl_preD[intro!, dest]
  backtrack_get_conglit_wl_not_NoneD[dest] lit_of_hd_trail_st_def[symmetric, simp]
  size_conflict_wl_def[simp] st_remove_highest_lvl_from_confl_def[simp]
  backtrack_wl_D_helper3[simp]
  unfolding backtrack_wl_D_alt_def PR_CONST_def
  unfolding delete_index_and_swap_update_def[symmetric] append_update_def[symmetric]
    append_ll_def[symmetric] lit_of_hd_trail_st_def[symmetric]
    cons_trail_Propagated_def[symmetric]
    size_conflict_wl_def[symmetric] one_uint32_nat_def[symmetric]
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
  text \<open>We need an \<^term>\<open>ASSN_ANNOT\<close> for type \<^typ>\<open>'a nres\<close>, but this does not exist and
   it is not clear how to do it.\<close>
           apply sepref_dbg_side_unfold apply (auto simp: )[]
          apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
                apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
               apply sepref_dbg_trans_step_keep
              apply sepref_dbg_trans_step_keep
             apply sepref_dbg_trans_step_keep
            apply sepref_dbg_trans_step_keep
           apply sepref_dbg_trans_step_keep
          apply sepref_dbg_trans_step_keep
         apply sepref_dbg_trans_step_keep
        apply sepref_dbg_trans_step_keep
       apply sepref_dbg_trans_step_keep
      apply sepref_dbg_trans_step_keep
     apply (solves \<open>simp\<close>)
    apply sepref_dbg_trans_step_keep
   apply sepref_dbg_trans_step_keep
  apply sepref_dbg_constraints
  done

concrete_definition (in -) backtrack_wl_D_code
   uses isasat_input_bounded_nempty.backtrack_wl_D.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) backtrack_wl_D_code_def

lemmas backtrack_wl_D_code_refine[sepref_fr_rules] =
   backtrack_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]
end


setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>

context isasat_input_bounded_nempty
begin
paragraph \<open>Decide\<close>

lemma (in -)not_is_None_not_None: \<open>\<not>is_None s \<Longrightarrow> s \<noteq> None\<close>
  by (auto split: option.splits)

definition (in -) defined_atm :: \<open>('v, nat) ann_lits \<Rightarrow> 'v \<Rightarrow> bool\<close> where
\<open>defined_atm M L = defined_lit M (Pos L)\<close>

definition (in -) defined_atm_pol where
  \<open>defined_atm_pol = (\<lambda>(M, xs, lvls, k) L. do {
      ASSERT(L < length xs);
      RETURN (xs!L \<noteq> None)
    })\<close>

sepref_thm defined_atm_code
  is \<open>uncurry defined_atm_pol\<close>
  :: \<open>(trail_pol_assn)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding defined_atm_pol_def
  by sepref

concrete_definition (in -) defined_atm_code
   uses isasat_input_bounded_nempty.defined_atm_code.refine_raw
   is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) defined_atm_code_def

lemmas undefined_atm_code_refine[sepref_fr_rules] =
   defined_atm_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma undefined_atm_code:
  \<open>(uncurry defined_atm_pol, uncurry (RETURN oo defined_atm)) \<in>
   [\<lambda>(M, L). Pos L \<in> snd ` D\<^sub>0]\<^sub>f trail_pol \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
proof -
  have H: \<open>L < length xs\<close> (is \<open>?length\<close>) and
    none: \<open>defined_atm M L \<longleftrightarrow> xs ! L \<noteq> None\<close> (is ?undef)
    if L_N: \<open>Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close> and  tr: \<open>((M', xs, lvls, k), M) \<in> trail_pol\<close>
    for M xs lvls k M' L
  proof -
    have
       \<open>M = M'\<close> and
       \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l. atm_of L < length xs \<and> xs ! atm_of L = polarity_atm M (atm_of L)\<close>
      using tr unfolding trail_pol_def by fast+
    then have L: \<open>L < length xs\<close> and xsL: \<open>xs ! L = polarity_atm M L\<close>
      using L_N by force+
    show ?length
      using L .
    show ?undef
      using xsL by (auto simp: polarity_atm_def defined_atm_def
          Decided_Propagated_in_iff_in_lits_of_l split: if_splits)
  qed
  show ?thesis
    unfolding defined_atm_pol_def
    by (intro frefI nres_relI) (auto 5 5 simp: none H intro!: ASSERT_leI)
qed

lemma undefined_atm_code_ref[sepref_fr_rules]:
  \<open>(uncurry defined_atm_code, uncurry (RETURN \<circ>\<circ> defined_atm)) \<in>
     [\<lambda>(a, b). Pos b \<in> snd ` D\<^sub>0]\<^sub>a (hr_comp trail_pol_assn trail_pol)\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> bool_assn\<close>
  using undefined_atm_code_refine[FCOMP undefined_atm_code] .

abbreviation (in -) undefined_atm where
  \<open>undefined_atm M L \<equiv> \<not>defined_atm M L\<close>

sepref_register vmtf_find_next_undef
sepref_thm vmtf_find_next_undef_code
  is \<open>uncurry (PR_CONST vmtf_find_next_undef)\<close>
  :: \<open>vmtf_remove_conc\<^sup>k *\<^sub>a (hr_comp trail_pol_assn trail_pol)\<^sup>k \<rightarrow>\<^sub>a option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_def PR_CONST_def
  apply (rewrite at \<open>WHILE\<^sub>T\<^bsup>_\<^esup> (\<lambda> _ . \<hole>) _ _\<close> short_circuit_conv)
  apply (rewrite in \<open>If _ \<hole> _\<close> defined_atm_def[symmetric])
  by sepref

concrete_definition (in -) vmtf_find_next_undef_code
  uses isasat_input_bounded_nempty.vmtf_find_next_undef_code.refine_raw
  is \<open>(uncurry ?f, _)\<in>_\<close>

prepare_code_thms (in -) vmtf_find_next_undef_code_def

lemmas vmtf_find_next_undef_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_code.refine[OF isasat_input_bounded_nempty_axioms]

definition (in isasat_input_ops) vmtf_find_next_undef_upd
  :: \<open>(nat, nat)ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
        (((nat, nat)ann_lits \<times> vmtf_remove_int) \<times> nat option)nres\<close> where
  \<open>vmtf_find_next_undef_upd = (\<lambda>M vm. do{
      L \<leftarrow>  vmtf_find_next_undef vm M;
      RETURN ((M, update_next_search L vm), L)
  })\<close>

definition trail_ref_except_ann_lits where
 \<open>trail_ref_except_ann_lits = {((M, ((A, m, fst_As, lst_As, next_search), removed)), M').
        M = M' \<and> ((A, m, fst_As, lst_As, next_search), removed) \<in> vmtf M}\<close>

definition phase_saver_ref where
  \<open>phase_saver_ref = {(M, M'). M = M' \<and> phase_saving M}\<close>

sepref_register vmtf_find_next_undef_upd
sepref_thm vmtf_find_next_undef_upd_code
  is \<open>uncurry (PR_CONST vmtf_find_next_undef_upd)\<close>
  :: \<open>trail_assn\<^sup>d *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>\<^sub>a
     (hr_comp trail_pol_assn trail_pol *assn vmtf_remove_conc) *assn
        option_assn uint32_nat_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp]
  unfolding vmtf_find_next_undef_upd_def PR_CONST_def
  by sepref

concrete_definition (in -) vmtf_find_next_undef_upd_code
  uses isasat_input_bounded_nempty.vmtf_find_next_undef_upd_code.refine_raw
  is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) vmtf_find_next_undef_upd_code_def

lemmas vmtf_find_next_undef_upd_code_ref[sepref_fr_rules] =
   vmtf_find_next_undef_upd_code.refine[OF isasat_input_bounded_nempty_axioms]


definition lit_of_found_atm where
\<open>lit_of_found_atm \<phi> L = SPEC (\<lambda>K. (L = None \<longrightarrow> K = None) \<and>
    (L \<noteq> None \<longrightarrow> K \<noteq> None \<and> atm_of (the K) = the L))\<close>

definition (in isasat_input_ops) find_undefined_atm
  :: \<open>(nat,nat) ann_lits \<Rightarrow> vmtf_remove_int \<Rightarrow>
       (((nat,nat) ann_lits \<times> vmtf_remove_int) \<times> nat option) nres\<close>
where
  \<open>find_undefined_atm M _ = SPEC(\<lambda>((M', vm), L). (L \<noteq> None \<longrightarrow> Pos (the L) \<in>snd ` D\<^sub>0 \<and> undefined_atm M (the L)) \<and>
     (L = None \<longrightarrow> (\<forall>K\<in>snd ` D\<^sub>0. defined_lit M K)) \<and> M = M' \<and> vm \<in> vmtf M)\<close>

definition find_unassigned_lit_wl_D_heur :: \<open>twl_st_wl_heur \<Rightarrow> (twl_st_wl_heur \<times> nat literal option) nres\<close>
where
  \<open>find_unassigned_lit_wl_D_heur = (\<lambda>(M, N, U, D, WS, Q, vm, \<phi>, clvls). do {
      ((M, vm), L) \<leftarrow> find_undefined_atm M vm;
      L \<leftarrow> lit_of_found_atm \<phi> L;
      RETURN ((M, N, U, D, WS, Q, vm, \<phi>, clvls), L)
    })\<close>

lemma find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D:
  \<open>(find_unassigned_lit_wl_D_heur, find_unassigned_lit_wl_D) \<in>
     [\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and> get_conflict_wl S = None]\<^sub>f
    twl_st_heur \<rightarrow> \<langle>twl_st_heur \<times>\<^sub>r \<langle>nat_lit_lit_rel\<rangle>option_rel\<rangle>nres_rel\<close>
proof -
  have [simp]: \<open>undefined_lit M (Pos (atm_of y)) = undefined_lit M y\<close> for M y
    by (auto simp: defined_lit_map)
  have [simp]: \<open>defined_atm M (atm_of y) = defined_lit M y\<close> for M y
    by (auto simp: defined_lit_map defined_atm_def)

  have ID_R: \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel = Id\<close>
    by auto
  have atms: \<open>atms_of \<L>\<^sub>a\<^sub>l\<^sub>l =
         atms_of_ms ((\<lambda>x. mset (take 2 x) + mset (drop 2 x)) ` set (take U (tl N))) \<union>
         atms_of_mm NP \<and> (\<forall>y. atm_of y \<in> atms_of_mm NP \<longrightarrow> defined_lit M y)\<close>
      if inv: \<open>twl_struct_invs (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close> and
        \<A>\<^sub>i\<^sub>n: \<open>literals_are_\<L>\<^sub>i\<^sub>n (M, N, U, D, NP, UP, WS, Q)\<close> and
        confl: \<open>get_conflict_wl (M, N, U, D, NP, UP, WS, Q) = None\<close>
      for M N U D NP UP WS Q
  proof -
    have \<open>cdcl\<^sub>W_restart_mset.no_strange_atm
            (state\<^sub>W_of (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q)))\<close> and
        unit: \<open>unit_clss_inv (twl_st_of_wl None (M, N, U, D, NP, UP, WS, Q))\<close>
      using inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    moreover have \<open>defined_lit M L\<close> if NP: \<open>atm_of L\<in> atms_of_mm NP\<close> for L
    proof -
      obtain C where C_NP: \<open>C \<in># NP\<close> and L_C: \<open>atm_of L \<in> atms_of C\<close>
         using NP unfolding atms_of_ms_def by auto
      have \<open>C\<in>set_mset NP \<Longrightarrow> \<exists>L. C = {#L#} \<and> get_level M L = 0 \<and> L \<in> lits_of_l M\<close> for C
         using unit confl by auto
      from this[of C] obtain L' where \<open>C = {#L'#}\<close> and \<open>L' \<in> lits_of_l M\<close>
         using C_NP by auto
      then show ?thesis
        using L_C by (auto simp: Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of)
    qed
    ultimately show ?thesis
      using \<A>\<^sub>i\<^sub>n unfolding is_\<L>\<^sub>a\<^sub>l\<^sub>l_alt_def
      by (auto simp: cdcl\<^sub>W_restart_mset.no_strange_atm_def
        mset_take_mset_drop_mset mset_take_mset_drop_mset' clauses_def simp del: unit_clss_inv.simps)
  qed
  show ?thesis
   unfolding find_unassigned_lit_wl_D_heur_def find_unassigned_lit_wl_D_def find_undefined_atm_def
    ID_R lit_of_found_atm_def
   apply (intro frefI nres_relI)
   apply clarify
   apply refine_vcg
   unfolding RETURN_RES_refine_iff
   by (auto simp: twl_st_heur_def atms in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def image_image
       simp del: twl_st_of_wl.simps dest!: atms)
qed


lemma vmtf_find_next_undef_upd:
  \<open>(uncurry vmtf_find_next_undef_upd, uncurry find_undefined_atm) \<in>
     [\<lambda>(M, vm). vm \<in> vmtf M]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id \<times>\<^sub>f Id \<times>\<^sub>f \<langle>nat_rel\<rangle>option_rel\<rangle>nres_rel\<close>
  unfolding vmtf_find_next_undef_upd_def trail_ref_except_ann_lits_def find_undefined_atm_def
    update_next_search_def uncurry_def
  apply (intro frefI nres_relI)
  apply (clarify)
  apply (rule bind_refine_spec)
   prefer 2
   apply (rule vmtf_find_next_undef_ref[simplified])
  by (auto intro!: RETURN_SPEC_refine simp: image_image defined_atm_def[symmetric])


lemma find_undefined_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry vmtf_find_next_undef_upd_code, uncurry (PR_CONST find_undefined_atm))
    \<in> [\<lambda>(b, a). a \<in> vmtf b]\<^sub>a trail_assn\<^sup>d *\<^sub>a vmtf_remove_conc\<^sup>d \<rightarrow>
   (trail_assn *assn vmtf_remove_conc) *assn option_assn uint32_nat_assn\<close>
  using vmtf_find_next_undef_upd_code_ref[unfolded PR_CONST_def, FCOMP vmtf_find_next_undef_upd]
  unfolding PR_CONST_def
  .

definition (in isasat_input_ops) lit_of_found_atm_D
  :: \<open>bool list \<Rightarrow> nat option \<Rightarrow> (nat literal option)nres\<close> where
  \<open>lit_of_found_atm_D = (\<lambda>(\<phi>::bool list) L. do{
      case L of
        None \<Rightarrow> RETURN None
      | Some L \<Rightarrow> do {
          if \<phi>!L then RETURN (Some (Pos L)) else RETURN (Some (Neg L))
        }
  })\<close>

definition (in isasat_input_ops) lit_of_found_atm_D_pre where
\<open>lit_of_found_atm_D_pre = (\<lambda>(\<phi>, L). L \<noteq> None \<longrightarrow> (Pos (the L) \<in> snd ` D\<^sub>0 \<and> the L < length \<phi>))\<close>

sepref_thm lit_of_found_atm_D_code
  is \<open>uncurry (PR_CONST lit_of_found_atm_D)\<close>
  :: \<open>[lit_of_found_atm_D_pre]\<^sub>a
      (array_assn bool_assn)\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
          option_assn unat_lit_assn\<close>
  supply [[goals_limit=1]]
  supply not_is_None_not_None[simp] Pos_unat_lit_assn[sepref_fr_rules] Neg_unat_lit_assn[sepref_fr_rules]
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_D_pre_def
  by sepref

concrete_definition (in -) lit_of_found_atm_D_code
   uses isasat_input_bounded_nempty.lit_of_found_atm_D_code.refine_raw
   is \<open>(uncurry ?f,_)\<in>_\<close>

prepare_code_thms (in -) lit_of_found_atm_D_code_def

lemmas lit_of_found_atm_D_hnr[sepref_fr_rules] =
   lit_of_found_atm_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

lemma lit_of_found_atm_D_lit_of_found_atm:
  \<open>(uncurry (PR_CONST lit_of_found_atm_D), uncurry lit_of_found_atm) \<in>
   [lit_of_found_atm_D_pre]\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding lit_of_found_atm_D_def PR_CONST_def lit_of_found_atm_def
  by (auto split: option.splits)


lemma lit_of_found_atm_hnr[sepref_fr_rules]:
  \<open>(uncurry lit_of_found_atm_D_code, uncurry lit_of_found_atm)
   \<in> [lit_of_found_atm_D_pre]\<^sub>a
     phase_saver_conc\<^sup>k *\<^sub>a (option_assn uint32_nat_assn)\<^sup>d \<rightarrow>
     option_assn unat_lit_assn\<close>
  using lit_of_found_atm_D_hnr[FCOMP lit_of_found_atm_D_lit_of_found_atm] by simp

lemma find_unassigned_lit_wl_D_code_helper:
  assumes
    \<open>RETURN ((a1'h, (db, dc, dd, de), df), a2'g) \<le> find_undefined_atm a1' ((cj, ck, cl, cm), cn)\<close> and
    \<open>phase_saving a2'f\<close>
  shows \<open>lit_of_found_atm_D_pre (a2'f, a2'g)\<close>
  using assms by (auto simp: find_undefined_atm_def lit_of_found_atm_D_pre_def phase_saving_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff)


sepref_register find_undefined_atm
sepref_thm find_unassigned_lit_wl_D_code
  is \<open>PR_CONST find_unassigned_lit_wl_D_heur\<close>
  :: \<open>[\<lambda>(M, N, U, D, WS, Q, vm, \<phi>, clvls). vm \<in> vmtf M \<and> phase_saving \<phi>]\<^sub>a
     twl_st_heur_assn\<^sup>d \<rightarrow> (twl_st_heur_assn *assn option_assn unat_lit_assn)\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding find_unassigned_lit_wl_D_heur_def twl_st_heur_assn_def PR_CONST_def
  by sepref

concrete_definition (in -) find_unassigned_lit_wl_D_code
   uses isasat_input_bounded_nempty.find_unassigned_lit_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) find_unassigned_lit_wl_D_code_def

lemmas find_unassigned_lit_wl_D_heur_hnr[sepref_fr_rules] =
   find_unassigned_lit_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]

definition find_unassigned_lit_wl_D_pre where
  \<open>find_unassigned_lit_wl_D_pre = (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and> literals_are_\<L>\<^sub>i\<^sub>n S \<and>
             get_conflict_wl S = None)\<close>

lemma find_unassigned_lit_wl_D_hnr[sepref_fr_rules]:
  \<open>(find_unassigned_lit_wl_D_code, PR_CONST find_unassigned_lit_wl_D)
  \<in> [find_unassigned_lit_wl_D_pre]\<^sub>a
    twl_st_assn\<^sup>d \<rightarrow> twl_st_assn *assn option_assn unat_lit_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE twl_st_heur
       (\<lambda>S. twl_struct_invs (twl_st_of_wl None S) \<and>
             literals_are_\<L>\<^sub>i\<^sub>n S \<and>
             get_conflict_wl S = None)
       (\<lambda>_ (M, N, U, D, WS, Q, vm, \<phi>, clvls).
           vm \<in> vmtf M \<and> phase_saving \<phi>)
       (\<lambda>_. True)]\<^sub>a hrp_comp (twl_st_heur_assn\<^sup>d)
                       twl_st_heur \<rightarrow> hr_comp
         (twl_st_heur_assn *assn option_assn unat_lit_assn)
         (twl_st_heur \<times>\<^sub>f \<langle>nat_lit_lit_rel\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF find_unassigned_lit_wl_D_heur_hnr[unfolded PR_CONST_def]
        find_unassigned_lit_wl_D'_find_unassigned_lit_wl_D[unfolded PR_CONST_def]]
    unfolding PR_CONST_def
    .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    unfolding comp_PRE_def find_unassigned_lit_wl_D_pre_def
      by (auto simp: comp_PRE_def twl_st_assn_def twl_st_heur_def
          map_fun_rel_def intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def[symmetric]
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

lemma decide_wl_or_skip_D_helper:
  assumes
    \<open>decide_wl_or_skip_D_pre
      (a, aa, ab, ac, ad, ae, af, b)\<close>
  shows \<open>find_unassigned_lit_wl_D_pre
          (a, aa, ab, ac, ad, ae, af, b)\<close> and
     \<open>get_conflict_wl (a, aa, ab, ac, ad, ae, af, b) = None\<close>
  using assms unfolding decide_wl_or_skip_D_pre_def find_unassigned_lit_wl_D_pre_def
  decide_wl_or_skip_pre_def decide_l_or_skip_pre_def
  by auto

definition decide_lit_wl_heur :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>decide_lit_wl_heur = (\<lambda>L' (M, N, U, D, Q, W).
      (Decided L' # M, N, U, D, {#- L'#}, W))\<close>

lemma decide_lit_wl_heur_decide_lit_wl:
  \<open>(uncurry (RETURN oo decide_lit_wl_heur), uncurry (RETURN oo decide_lit_wl)) \<in>
     [\<lambda>(L, S). undefined_lit (get_trail_wl S) L \<and> get_conflict_wl S = None]\<^sub>f nat_lit_lit_rel \<times>\<^sub>r twl_st_heur \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding decide_lit_wl_heur_def decide_lit_wl_def
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def intro: vmtf_consD)

definition cons_trail_Decided :: \<open>nat literal \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits\<close> where
  \<open>cons_trail_Decided L M' = Decided L # M'\<close>

definition cons_trail_Decided_tr :: \<open>nat literal \<Rightarrow> trail_pol \<Rightarrow> trail_pol\<close> where
  \<open>cons_trail_Decided_tr = (\<lambda>L (M', xs, lvls, k).
     (Decided L # M', xs[atm_of L := Some (is_pos L)],
      lvls[atm_of L := k+1], k+1))\<close>

lemma cons_trail_Decided_tr:
  \<open>(uncurry (RETURN oo cons_trail_Decided_tr), uncurry (RETURN oo cons_trail_Decided)) \<in>
  [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>f Id \<times>\<^sub>f trail_pol \<rightarrow> \<langle>trail_pol\<rangle>nres_rel\<close>
  by (intro frefI nres_relI, rename_tac x y, case_tac \<open>fst x\<close>)
     (auto simp: trail_pol_def polarity_atm_def cons_trail_Decided_def uminus_lit_swap
        trail_pol_def cons_trail_Decided_tr_def Decided_Propagated_in_iff_in_lits_of_l
        cons_trail_Decided_tr_def nth_list_update'
      intro: vmtf_consD)

sepref_thm cons_trail_Decided_tr_code
  is \<open>uncurry (RETURN oo cons_trail_Decided_tr)\<close>
  :: \<open>[\<lambda>(L, (M, xs, lvls, k)). undefined_lit M L \<and> atm_of L < length xs \<and> atm_of L < length lvls \<and>
     (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<and> no_dup M \<and> L \<in> snd ` D\<^sub>0 \<and> k = count_decided M]\<^sub>a
       unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d \<rightarrow> trail_pol_assn\<close>
  unfolding cons_trail_Decided_tr_def cons_trail_Decided_tr_def one_uint32_nat_def[symmetric]
  supply [[goals_limit = 1]] undefined_lit_count_decided_uint_max[dest!]
  by sepref

concrete_definition (in -) cons_trail_Decided_tr_code
  uses isasat_input_bounded_nempty.cons_trail_Decided_tr_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) cons_trail_Decided_tr_code_def

lemmas cons_trail_Decided_tr_code[sepref_fr_rules] =
  cons_trail_Decided_tr_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma cons_trail_Decided_tr_code_cons_trail_Decided_tr[sepref_fr_rules]:
  \<open>(uncurry cons_trail_Decided_tr_code, uncurry (RETURN oo cons_trail_Decided)) \<in>
    [\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a trail_assn\<^sup>d \<rightarrow>
    trail_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f trail_pol)
     (\<lambda>(L, M). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
     (\<lambda>_ (L, M, xs, lvls, k).
         undefined_lit M L \<and>
         atm_of L < length xs \<and>
         atm_of L < length lvls \<and>
         (\<forall>L\<in>set M. lit_of L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l) \<and>
         no_dup M \<and> L \<in> snd ` D\<^sub>0 \<and> k = count_decided M)
     (\<lambda>_. True)]\<^sub>a hrp_comp
                     (unat_lit_assn\<^sup>k *\<^sub>a trail_pol_assn\<^sup>d)
                     (nat_lit_lit_rel \<times>\<^sub>f
                      trail_pol) \<rightarrow> hr_comp trail_pol_assn
         trail_pol\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF cons_trail_Decided_tr_code.refine cons_trail_Decided_tr,
        OF isasat_input_bounded_nempty_axioms] .
  have pre: \<open>?pre' = ?pre\<close>
    by (auto simp: comp_PRE_def trail_pol_def trail_pol_def image_image intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    using H unfolding im pre .
qed

sepref_thm decide_lit_wl_code
  is \<open>uncurry (RETURN oo (PR_CONST decide_lit_wl_heur))\<close>
  :: \<open>[\<lambda>(L, (M, N, U, D, WS, Q, vm, \<phi>)). undefined_lit M L \<and> L \<in> snd ` D\<^sub>0]\<^sub>a
     unat_lit_assn\<^sup>k *\<^sub>a twl_st_heur_assn\<^sup>d \<rightarrow> twl_st_heur_assn\<close>
  supply [[goals_limit=1]] find_unassigned_lit_wl_D_code_helper[simp]
  unfolding decide_lit_wl_heur_def twl_st_heur_assn_def PR_CONST_def cons_trail_Decided_def[symmetric]
  apply (rewrite at \<open>(_, add_mset _ \<hole>, _)\<close> lms_fold_custom_empty)+
  by sepref

concrete_definition (in -) decide_lit_wl_code
  uses isasat_input_bounded_nempty.decide_lit_wl_code.refine_raw
  is \<open>(uncurry ?f, _) \<in> _\<close>

prepare_code_thms (in -) decide_lit_wl_code_def

lemmas decide_lit_wl_heur_hnr[sepref_fr_rules] =
  decide_lit_wl_code.refine[OF isasat_input_bounded_nempty_axioms]

lemma decide_lit_wl_hnr[sepref_fr_rules]:
  \<open>(uncurry decide_lit_wl_code, uncurry (RETURN \<circ>\<circ> decide_lit_wl))
  \<in> [\<lambda>(L, S). undefined_lit (get_trail_wl S) L  \<and> L \<in> snd ` D\<^sub>0 \<and>
      get_conflict_wl S = None]\<^sub>a unat_lit_assn\<^sup>k *\<^sub>a twl_st_assn\<^sup>d \<rightarrow>  twl_st_assn\<close>
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have H: \<open>?c
  \<in> [comp_PRE (nat_lit_lit_rel \<times>\<^sub>f twl_st_heur)
       (\<lambda>(L, S). undefined_lit (get_trail_wl S) L \<and>
           get_conflict_wl S = None)
       (\<lambda>_ (L, M, N, U, D, WS, Q, vm, \<phi>).
           undefined_lit M L \<and> L \<in> snd ` D\<^sub>0)
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       (unat_lit_assn\<^sup>k *\<^sub>a
                        twl_st_heur_assn\<^sup>d)
                       (nat_lit_lit_rel \<times>\<^sub>f
                        twl_st_heur) \<rightarrow> hr_comp
           twl_st_heur_assn twl_st_heur\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF decide_lit_wl_heur_hnr[unfolded PR_CONST_def]
        decide_lit_wl_heur_decide_lit_wl] .
  have pre: \<open>?pre x \<Longrightarrow> ?pre' x\<close> for x
    by (auto simp: comp_PRE_def twl_st_heur_def image_image intro!: ext)
  have im: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  have f: \<open>?f' = ?f\<close>
    unfolding prod_hrp_comp hrp_comp_dest hrp_comp_keep twl_st_assn_def
    by (auto simp: hrp_comp_def hr_comp_def)
  show ?thesis
    apply (rule hfref_weaken_pre[OF ])
     defer
    using H unfolding im f apply assumption
    using pre ..
qed

sepref_register decide_wl_or_skip_D find_unassigned_lit_wl_D
sepref_thm decide_wl_or_skip_D_code
  is \<open>PR_CONST decide_wl_or_skip_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_assn\<close>
  unfolding decide_wl_or_skip_D_def PR_CONST_def
  supply [[goals_limit = 1]] decide_wl_or_skip_D_helper[simp, intro] find_unassigned_lit_wl_D_def[simp]
    image_image[simp]
  by sepref

concrete_definition (in -) decide_wl_or_skip_D_code
  uses isasat_input_bounded_nempty.decide_wl_or_skip_D_code.refine_raw
  is \<open>(?f, _) \<in> _\<close>

prepare_code_thms (in -) decide_wl_or_skip_D_code_def

lemmas decide_wl_or_skip_D_hnr[sepref_fr_rules] =
  decide_wl_or_skip_D_code.refine[OF isasat_input_bounded_nempty_axioms]


subsubsection \<open>Combining Together: the Other Rules\<close>

sepref_register get_conflict_wl_is_None


sepref_register cdcl_twl_o_prog_wl_D
sepref_thm cdcl_twl_o_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_o_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_assn\<close>
  unfolding cdcl_twl_o_prog_wl_D_def PR_CONST_def
  unfolding get_conflict_wl_is_None get_conflict_wl_get_conflict_wl_is_Nil
    get_conflict_wl_is_None_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_o_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_o_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_o_prog_wl_D_code_def

lemmas cdcl_twl_o_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_o_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n, OF isasat_input_bounded_nempty_axioms]


subsubsection \<open>Combining Together: Full Strategy\<close>

sepref_register cdcl_twl_stgy_prog_wl_D
sepref_thm cdcl_twl_stgy_prog_wl_D_code
  is \<open>PR_CONST cdcl_twl_stgy_prog_wl_D\<close>
  :: \<open>twl_st_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_assn\<close>
  unfolding cdcl_twl_stgy_prog_wl_D_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

concrete_definition (in -) cdcl_twl_stgy_prog_wl_D_code
   uses isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_code.refine_raw
   is \<open>(?f,_)\<in>_\<close>

prepare_code_thms (in -) cdcl_twl_stgy_prog_wl_D_code_def

lemmas cdcl_twl_stgy_prog_wl_D_code[sepref_fr_rules] =
   cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n]

end

export_code cdcl_twl_stgy_prog_wl_D_code in SML_imp module_name SAT_Solver
  file "code/CDCL_Cached_Array_Trail.ML"

end