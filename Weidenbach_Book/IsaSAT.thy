theory IsaSAT
imports IsaSAT_Initialisation IsaSAT_CDCL
begin

lemma distinct_nat_of_uint32[iff]:
  \<open>distinct_mset (nat_of_uint32 `# A) \<longleftrightarrow> distinct_mset A\<close>
  \<open>distinct (map nat_of_uint32 xs) \<longleftrightarrow> distinct xs\<close>
  using distinct_image_mset_inj[of nat_of_uint32]
  by (auto simp: inj_on_def distinct_map)


declare isasat_input_bounded.append_el_aa_hnr[sepref_fr_rules]
declare isasat_input_bounded.polarity_pol_code_polarity_refine[sepref_fr_rules]
  isasat_input_bounded.cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]


text \<open>to get a full SAT:
  \<^item> either we fully apply \<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<close>
  \<^item> or we can stop early.
\<close>
definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T U \<or>
          (CS \<noteq> {#} \<and> conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
          unsatisfiable (set_mset CS)))
  }\<close>

definition (in -) SAT_wl :: \<open>nat clause_l list \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS [];
    let S = isasat_input_ops.init_state_wl (mset \<A>\<^sub>i\<^sub>n');
    T \<leftarrow> init_dt_wl (*mset \<A>\<^sub>i\<^sub>n'*) CS (to_init_state S);
    let T = from_init_state T;
    if get_conflict_wl T \<noteq> None
    then RETURN T
    else if CS = [] then RETURN (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined))
    else do {
       ASSERT (extract_atms_clss CS [] \<noteq> []);
       ASSERT(isasat_input_bounded_nempty (mset \<A>\<^sub>i\<^sub>n'));
       isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset \<A>\<^sub>i\<^sub>n') (finalise_init T)
    }
  }\<close>


definition extract_model_of_state where
  \<open>extract_model_of_state U = Some (map lit_of (get_trail_wl U))\<close>

definition extract_model_of_state_heur where
  \<open>extract_model_of_state_heur U = Some (map lit_of (get_trail_wl_heur U))\<close>

definition extract_stats where
  [simp]: \<open>extract_stats U = None\<close>

definition extract_stats_init where
  [simp]: \<open>extract_stats_init = None\<close>

(* TODO Kill *)
definition IsaSAT :: \<open>nat clause_l list \<Rightarrow> nat literal list option nres\<close> where
  \<open>IsaSAT CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset (extract_atms_clss CS []);
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let S = isasat_input_ops.init_state_wl \<A>\<^sub>i\<^sub>n';
    let S = to_init_state S;
    T \<leftarrow> init_dt_wl (*\<A>\<^sub>i\<^sub>n'*) CS S;
    let T = from_init_state T;
    if \<not>get_conflict_wl_is_None_init T
    then RETURN (None)
    else if CS = [] then RETURN (Some [])
    else do {
       ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
       ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
       let T = finalise_init T;
       U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D \<A>\<^sub>i\<^sub>n' T;
       RETURN (if get_conflict_wl U = None then extract_model_of_state U else extract_stats U)
    }
  }\<close>


definition extract_model_of_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_model_of_state_stat U =
     (Some (map lit_of (get_trail_wl_heur U)),
       (\<lambda>(M, _,  _, _, _ ,_ ,_ ,_, _, _, _, stat). stat) U)\<close>

definition extract_state_stat :: \<open>twl_st_wl_heur \<Rightarrow> nat literal list option \<times> stats\<close> where
  \<open>extract_state_stat U =
     (None,
       (\<lambda>(M, _, _, _, _ ,_ ,_ ,_, _, _, _, stat). stat) U)\<close>

definition empty_conflict :: \<open>nat literal list option\<close> where
  \<open>empty_conflict = Some []\<close>

definition empty_conflict_code :: \<open>_ list option \<times> stats\<close> where
  \<open>empty_conflict_code = (Some [], (0, 0, 0))\<close>

definition empty_init_code :: \<open>_ list option \<times> stats\<close> where
  \<open>empty_init_code = (None, (0, 0, 0))\<close>


abbreviation (in -) model_stat_assn where
  \<open>model_stat_assn \<equiv> option_assn (list_assn unat_lit_assn) *a stats_assn\<close>

lemma empty_conflict_code_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return empty_conflict_code), uncurry0 (RETURN empty_conflict_code)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  by sepref_to_hoare (sep_auto simp: empty_conflict_code_def empty_conflict_def
       hr_comp_def)

lemma empty_init_code_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return empty_init_code), uncurry0 (RETURN empty_init_code)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  by sepref_to_hoare (sep_auto simp: empty_conflict_code_def empty_conflict_def
       hr_comp_def empty_init_code_def)


definition IsaSAT_heur :: \<open>nat clause_l list \<Rightarrow> (nat literal list option \<times> stats) nres\<close> where
  \<open>IsaSAT_heur CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset (extract_atms_clss CS []);
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    S \<leftarrow> isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n';
    (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur \<A>\<^sub>i\<^sub>n' CS S;
    if \<not>get_conflict_wl_is_None_heur_init T
    then RETURN (empty_init_code)
    else if CS = [] then RETURN (empty_conflict_code)
    else do {
       ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
       ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
       ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
         lst_As \<noteq> None) T);
       T \<leftarrow> finalise_init_code (T::twl_st_wl_heur_init);
       U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D_heur \<A>\<^sub>i\<^sub>n' T;
       RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
         else extract_state_stat U)
     }
  }\<close>

lemma (in -)id_mset_list_assn_list_mset_assn:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(return o id, RETURN o mset) \<in> (list_assn R)\<^sup>d \<rightarrow>\<^sub>a list_mset_assn R\<close>
proof -
  obtain R' where R: \<open>R = pure R'\<close>
    using assms is_pure_conv unfolding CONSTRAINT_def by blast
  then have R': \<open>the_pure R = R'\<close>
    unfolding R by auto
  show ?thesis
    apply (subst R)
    apply (subst list_assn_pure_conv)
    apply sepref_to_hoare
    by (sep_auto simp: list_mset_assn_def R' pure_def list_mset_rel_def mset_rel_def
       p2rel_def rel2p_def[abs_def] rel_mset_def br_def Collect_eq_comp list_rel_def)
qed

(* TODO rename twl_st_heur_assn to isasat_assn*)
lemma cdcl_twl_stgy_prog_wl_D_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_prog_wl_D_code), uncurry isasat_input_ops.cdcl_twl_stgy_prog_wl_D_heur)
  \<in> [\<lambda>(N, _). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n]\<^sub>a
     (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.twl_st_heur_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.twl_st_heur_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    apply (cases a)
    by (sep_auto simp:
      dest!: frame_rule_left[of \<open>isasat_input_ops.twl_st_heur_assn _ _ _\<close> _ _
        \<open>list_mset_assn uint32_nat_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done

declare cdcl_twl_stgy_prog_wl_D_code_ref'[to_hnr, OF refl, sepref_fr_rules]

definition get_trail_wl_code :: \<open>twl_st_wll_trail \<Rightarrow> uint32 list option \<times> stats\<close> where
  \<open>get_trail_wl_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat). (Some M, stat))\<close>

definition get_stats_code :: \<open>twl_st_wll_trail \<Rightarrow> uint32 list option \<times> stats\<close> where
  \<open>get_stats_code = (\<lambda>((M, _), _, _, _, _ ,_ ,_ ,_, _, _, _, stat). (None, stat))\<close>


definition (in -) model_stat_rel where
  \<open>model_stat_rel = {((M', s), M). M = M'}\<close>

(* TODO Kill *)
definition (in -) model_assn where
  \<open>model_assn = hr_comp model_stat_assn model_stat_rel\<close>

context isasat_input_ops
begin

lemma extract_model_of_state_stat_hnr[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code, RETURN o extract_model_of_state_stat) \<in> twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def twl_st_heur_assn_def
        twl_st_heur_init_assn_def get_trail_wl_code_def
        extract_model_of_state_def extract_model_of_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed

lemma get_stats_code[sepref_fr_rules]:
  \<open>(return o get_stats_code, RETURN o extract_state_stat) \<in> twl_st_heur_assn\<^sup>d \<rightarrow>\<^sub>a
       model_stat_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  have [simp]: \<open>id_assn (an, ao, bb) (bs, bt, bu) = (id_assn an bs * id_assn ao bt * id_assn bb bu)\<close>
    for an ao bb bs bt bu :: uint64
    by (auto simp: pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_heur_def hr_comp_def trail_pol_def twl_st_heur_assn_def
        twl_st_heur_init_assn_def get_trail_wl_code_def get_stats_code_def
        extract_model_of_state_def extract_model_of_state_stat_def extract_state_stat_def
        dest!: ann_lits_split_reasons_map_lit_of
        elim!: mod_starE)
qed


end

declare isasat_input_ops.extract_model_of_state_stat_hnr[sepref_fr_rules]
declare isasat_input_ops.finalise_init_hnr[unfolded PR_CONST_def, sepref_fr_rules]
sepref_register to_init_state from_init_state get_conflict_wl_is_None_init extract_stats
  isasat_input_ops.init_dt_wl_heur
declare init_state_wl_heur_hnr[to_hnr, OF refl, sepref_fr_rules]
  init_dt_wl_code.refine[sepref_fr_rules]
 isasat_input_ops.get_stats_code[sepref_fr_rules]

sepref_definition IsaSAT_code
  is \<open>IsaSAT_heur\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a model_stat_assn\<close>
  unfolding IsaSAT_heur_def empty_conflict_def[symmetric]
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
    extract_stats_def[symmetric]
  supply get_conflict_wl_is_None_heur_init_def[simp]
  isasat_input_bounded.get_conflict_wl_is_None_code_refine[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_init_code_hnr[sepref_fr_rules]
  isasat_input_ops.to_init_state_hnr[sepref_fr_rules]
  isasat_input_ops.from_init_state_hnr[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_init_wl_hnr[
    unfolded get_conflict_wl_is_None_init_def[symmetric], sepref_fr_rules]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
   extract_stats_def[simp del]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  by sepref

code_printing constant nth_u_code \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt _))"

code_printing constant heap_array_set'_u \<rightharpoonup>
   (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"

code_printing constant length_u_code \<rightharpoonup> (SML_imp) "(fn/ ()/ =>/ Word32.fromInt (Array.length (_)))"

definition length_aa_u_code' where
  [symmetric, code]: \<open>length_aa_u_code' = length_aa_u_code\<close>
code_printing constant length_aa_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromInt (Array.length (Array.sub/ (fst (_),/ IntInf.toInt (integer'_of'_nat (_))))))"

(*
This equation makes no sense since a resizable array is represent by an array and an infinite
 integer: There is no obvious shortcut.
code_printing constant length_arl_u_code' \<rightharpoonup> (SML_imp)
   "(fn/ ()/ =>/ Word32.fromLargeInt (snd (_)))"  *)

export_code IsaSAT_code checking SML_imp
export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
  in SML_imp module_name SAT_Solver file "code/IsaSAT_solver.sml"

definition TWL_to_clauses_state_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset) set\<close> where
  \<open>TWL_to_clauses_state_conv = twl_st_of_wl None O {(S', S). S = state\<^sub>W_of S'}\<close>


lemma extract_atms_cls_empty_iff: \<open>extract_atms_cls Cs C0 = [] \<longleftrightarrow> (C0 = [] \<and> Cs = [])\<close>
  unfolding extract_atms_cls_def
  by (induction Cs arbitrary: C0) force+

lemma extract_atms_clss_empty_iff:
   \<open>extract_atms_clss CS C0  = [] \<longleftrightarrow> (C0 = [] \<and> (\<forall>C \<in> set CS. C = []))\<close>
proof -
  have \<open>fold extract_atms_cls Cs C0 = [] \<longleftrightarrow> (C0 = [] \<and> (\<forall>C \<in> set Cs. C = []))\<close> for Cs
    unfolding extract_atms_clss_def
    apply (induction Cs arbitrary: C0)
    subgoal by auto
    subgoal by (auto simp: extract_atms_cls_empty_iff)
    done
  then show ?thesis
    unfolding extract_atms_clss_def .
qed

(* TODO Move *)
lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state {#}) S \<longleftrightarrow> False\<close>
  unfolding rtranclp_unfold
  by (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state:
  \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding rtranclp_unfold
  by (subst tranclp_unfold_begin)
     (auto simp: cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step simp del: init_state.simps)
(* End Move *)

lemma conflict_of_level_unsatisfiable:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (init_clss S))\<close>
proof -
  obtain M N U D where S: \<open>S = (M, N, U, Some D)\<close>
    by (cases S) (use confl in auto)
  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition)
      (use dec in \<open>auto simp: count_decided_def filter_empty_conv S \<close>)
  have
    N_U: \<open>N \<Turnstile>psm U\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    N_U_M: \<open>set_mset N \<union> set_mset U \<Turnstile>ps unmark_l M\<close> and
    n_d: \<open>no_dup M\<close> and
    N_U_D: \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using assms
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def all_decomposition_implies_def
        S clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
  have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close>
    by (rule true_clss_clss_true_clss_cls_true_clss_clss[OF N_U_M M_D])
  then have \<open>set_mset N \<Turnstile>ps CNot D\<close> \<open>set_mset N \<Turnstile>p D\<close>
    using N_U N_U_D true_clss_clss_left_right by blast+
  then have \<open>unsatisfiable (set_mset N)\<close>
    by (rule true_clss_clss_CNot_true_clss_cls_unsatisfiable)

  then show ?thesis
    by (auto simp: S clauses_def dest: satisfiable_decreasing)
qed

(*
lemma twl_conflict_of_level_unsatisfiable_from_init:
  assumes
    \<open>(U, U') \<in> TWL_to_clauses_state_conv\<close> and
    invs: \<open>twl_struct_invs (twl_st_of_wl None U)\<close> and
    st: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state CS) (state\<^sub>W_of (twl_st_of_wl None U))\<close> and
    lev: \<open>count_decided (get_trail_wl U) = 0\<close> and
    confl: \<open>get_conflict_wl U \<noteq> None\<close> and
    \<open>satisfiable (set_mset CS)\<close>
  shows \<open>False\<close>
proof -
  have \<open>init_clss (state\<^sub>W_of (twl_st_of_wl None U)) = CS\<close>
    using cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_no_more_init_clss[OF st] by fastforce
  moreover have
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of (twl_st_of_wl None U))\<close>
    using invs unfolding twl_struct_invs_def by fast
  moreover have \<open>backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None U)) = 0\<close>
    using lev by (cases U) auto
  moreover have \<open>conflicting (state\<^sub>W_of (twl_st_of None (st_l_of_wl None U))) \<noteq> None\<close>
    using confl by (cases U) auto
  moreover have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init
         (state\<^sub>W_of (twl_st_of_wl None U))\<close>
    apply (rule cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_learned_clauses_entailed[of \<open>init_state CS\<close>])
    subgoal using st by (blast dest!: cdcl\<^sub>W_restart_mset.rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
    subgoal by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
    subgoal by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
    subgoal by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    done
  ultimately show ?thesis
    using conflict_of_level_unsatisfiable[of \<open>state\<^sub>W_of (twl_st_of_wl None U)\<close>] assms by auto
qed
*)

(* TODO Move *)
lemma [twl_st_wl_init]:
  \<open>get_trail_wl (fst T) = get_trail_init_wl T\<close>
  \<open>get_conflict_wl (fst T) = get_conflict_init_wl T\<close>
  by (cases T; auto; fail)+

lemma [twl_st_init]:
  \<open>trail (state\<^sub>W_of_init T) = get_trail_init T\<close>
  \<open>conflicting (state\<^sub>W_of_init T) = get_conflict_init T\<close>
  \<open>init_clss (state\<^sub>W_of_init T) = clauses (get_init_clauses_init T) + get_unit_init_clauses_init T
    + other_clauses_init T\<close>
  \<open>learned_clss (state\<^sub>W_of_init T) = clauses (get_learned_clauses_init T) +
     get_unit_learned_clauses_init T\<close>
  by (cases T; auto; fail)+

(* 
conflicting (state\<^sub>W_of_init W) = Some y \<Longrightarrow>
          init_clss (state\<^sub>W_of_init W) \<Turnstile>psm
          learned_clss (state\<^sub>W_of_init W)
 *)
(* End Move *)

lemma cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and>
        (\<forall>C \<in># CS. \<forall>L \<in># C. nat_of_lit L \<le> uint_max)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>TWL_to_clauses_state_conv\<rangle>nres_rel\<close>
proof -
  (* let ?init = \<open>state\<^sub>W_of (twl_st_of_wl None ([], fmempty, 0, None, {#}, {#}, {#}, \<lambda>_. []))\<close> *)
  have in_list_mset_rel: \<open>(CS', y) \<in> list_mset_rel \<longleftrightarrow> y = mset CS'\<close> for CS' y
    by (auto simp: list_mset_rel_def br_def)
  have in_list_mset_rel_mset_rel:
    \<open>(mset CS', CS) \<in> \<langle>list_mset_rel\<rangle>mset_rel \<longleftrightarrow> CS = mset `# mset CS'\<close> for CS CS'
    by (auto simp: list_mset_rel_def br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_op_eq_map_right_iff')
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)

  have \<L>\<^sub>a\<^sub>l\<^sub>l:
    \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))
       (all_lits_of_mm (mset `# mset CS'))\<close>
    for CS'
    by (auto simp add: isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
      all_lits_of_mm_add_mset in_extract_atms_clssD in_extract_atms_clsD
      all_lits_of_mm_def atms_of_s_def image_image image_Un)
  have extract_nempty: \<open>extract_atms_clss xs [] = [] \<longleftrightarrow> set xs = {[]}\<close>
  if
    H: \<open>Multiset.Ball ys distinct_mset \<and> (\<forall>C\<in>#ys. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
    rel: \<open>(xs, ys) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
    le_xs: \<open>length xs \<noteq> 0\<close>
  for xs ys
  proof -
    obtain x xs' where [simp]: \<open>xs = x # xs'\<close>
      using le_xs by (cases xs) auto
    obtain xy where
      xs_xy: \<open>(xs, xy) \<in> list_mset_rel\<close> and xy_ys: \<open>(xy, ys) \<in> \<langle>list_mset_rel\<rangle>mset_rel\<close>
      using rel by auto
    have xy[simp]: \<open>xy = mset xs\<close>
      using xs_xy by (auto simp: list_mset_rel_def br_def)
    have \<open>mset x \<in># ys\<close>
      using in_list_mset_rel_mset_rel[THEN iffD1, OF xy_ys[unfolded xy]]
      by auto
    show ?thesis
      by (auto simp: extract_atms_clss_empty_iff extract_atms_cls_empty_iff)
  qed
  have [simp]: \<open>isasat_input_bounded (mset (extract_atms_clss CS' []))\<close>
    if CS_p: \<open>\<forall>C\<in>set CS'. \<forall>L\<in>set C. nat_of_lit L \<le> uint_max\<close>
    for CS'
  unfolding isasat_input_bounded_def
      proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))\<close>
    then obtain C where
      L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
          isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
      using L CS_p by auto
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using L
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def)
  qed

  have conflict_during_init: \<open>RETURN (fst T)
      \<le> \<Down> TWL_to_clauses_state_conv
           (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                     CS \<noteq> {#} \<and> conflicting U \<noteq> None \<and>
                     backtrack_lvl U = 0 \<and>
                     unsatisfiable (set_mset CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. []), {#}) T\<close> and
      confl: \<open>get_conflict_wl (fst T) \<noteq> None\<close>
    for T CS CS'
  proof -
    obtain U V W where
      U: \<open>((([], fmempty, None, {#}, {#}, {#}, \<lambda>_. []), {#}), U) \<in> state_wl_l_init\<close> and
(*       \<open>correct_watching_init (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. []), {#})\<close> and  *)
      T_V: \<open>(T, V) \<in> state_wl_l_init\<close> and
      V_W: \<open>(V, W) \<in> twl_st_l_init\<close> and
      struct_invs: \<open>twl_struct_invs_init W\<close> and
      \<open>clauses_to_update_l_init V = {#}\<close> and
      count_dec: \<open>\<forall>s\<in>set (get_trail_l_init V). \<not> is_decided s\<close> and
      clss: \<open>mset `# mset CS' + mset `# ran_mf (get_clauses_l_init U) +
         other_clauses_l_init U + get_unit_clauses_l_init U =
       mset `# ran_mf (get_clauses_l_init V) + other_clauses_l_init V + 
         get_unit_clauses_l_init V\<close> and
      learned_UV: \<open>learned_clss_lf (get_clauses_l_init U) = learned_clss_lf (get_clauses_l_init V)\<close> and
      \<open>get_conflict_l_init V = None \<longrightarrow>
          literals_to_update_l_init V = uminus `# lit_of `# mset (get_trail_l_init V)\<close> and
      learned: \<open>get_learned_unit_clauses_l_init V = get_learned_unit_clauses_l_init U\<close> and
      add_invs: \<open>twl_list_invs (fst V)\<close> and
      \<open>twl_stgy_invs (fst W)\<close> and
      \<open>other_clauses_l_init V \<noteq> {#} \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_l_init V \<noteq> None\<close> and
      \<open>get_conflict_l_init U \<noteq> None \<longrightarrow>
       get_conflict_l_init U = get_conflict_l_init V\<close>
      using spec unfolding init_dt_wl_spec_def init_dt_spec_def apply -
      apply normalize_goal+
      by presburger
    have learned_U: \<open>learned_clss_lf (get_clauses_l_init U) = {#}\<close>
          \<open>get_clauses_l_init U = fmempty\<close>
          \<open>other_clauses_l_init U  = {#}\<close>
          \<open>get_unit_clauses_l_init U = {#}\<close>
      using U T_V V_W by (cases U; auto simp: state_wl_l_init_def state_wl_l_def; fail)+
    then have learned_W: \<open>get_learned_clauses_init W = {#}\<close> \<open>get_unit_learned_clauses_init W = {#}\<close>
      \<open>get_unit_init_clauses_init W = get_unit_clauses_l_init V\<close>
      using U T_V V_W learned learned_UV by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def; fail)+
    have
      \<open>clause `# (get_init_clauses_init W) = 
       mset `# (init_clss_lf (get_clauses_l_init V))\<close>
      using U T_V V_W learned learned_UV by (cases T; cases U; cases V;
         auto simp: state_wl_l_init_def state_wl_l_def twl_st_l_init_def
         mset_take_mset_drop_mset' mset_take_mset_drop_mset
         dest!: multi_member_split)
    from arg_cong[OF this, of set_mset]
    have init_clss_W_V: \<open>clause ` set_mset (get_init_clauses_init W) 
        = mset ` set_mset (init_clss_lf (get_clauses_l_init V))\<close>
      by auto
(*    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses ?init =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
        \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow>
            the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) = learned_clss ?init\<close>
      using spec unfolding init_dt_wl_spec_def
      by fast+*)
    have count_dec: \<open>count_decided (get_trail_wl (fst T)) = 0\<close>
      using count_dec T_V V_W unfolding count_decided_0_iff by (auto simp: twl_st_init
          twl_st_wl_init)
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)

    have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause (state\<^sub>W_of_init W)\<close> and
      all_struct_invs:
        \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init W)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
         cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast+
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of_init W)\<close>
      using struct_invs unfolding twl_struct_invs_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    have [simp]: \<open>CS' \<noteq> []\<close>
      using confl_in_clss confl by (cases T) auto
    have \<open>unsatisfiable (set_mset (mset `# mset (rev CS')))\<close>
      using conflict_of_level_unsatisfiable[OF all_struct_invs] count_dec confl learned clss T_V V_W
        learned_U init_clss_W_V learned_W
      by (auto simp: clauses_def mset_take_mset_drop_mset' twl_st_init twl_st_wl_init
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    then have [simp]: \<open>unsatisfiable (mset ` set CS')\<close>
      by auto

    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T)))\<close>])
      apply (intro conjI)
      subgoal
       by (cases T) (clarsimp_all simp: TWL_to_clauses_state_conv_def mset_take_mset_drop_mset'
            clauses_def in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal
        apply (rule disjI2)
        using \<L>\<^sub>a\<^sub>l\<^sub>l struct_invs learned count_dec U clss confl
        by (cases T) (clarsimp simp: CS)
      done
  qed
  have empty_clss:
   \<open>RETURN ([], fmempty, None, {#}, {#}, {#}, \<lambda>_. undefined)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                     CS \<noteq> {#} \<and>
                     conflicting U \<noteq> None \<and> backtrack_lvl U = 0 \<and> unsatisfiable (set_mset CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. []), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      [simp]: \<open>CS' = []\<close>
    for CS' CS T
  proof -
    have [simp]: \<open>CS = {#}\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have [simp]: \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ([], {#}, {#}, None) ([], {#}, {#}, None)\<close>
      using full_cdcl\<^sub>W_init_state[of \<open>([], {#}, {#}, None)\<close>] by auto
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      using spec confl
      unfolding init_dt_wl_spec_def
      by (cases T) (auto simp: clauses_def TWL_to_clauses_state_conv_def state_wl_l_init_def)
  qed
  have extract_atms_clss_not_nil: \<open>extract_atms_clss CS' [] \<noteq> []\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' (([], fmempty, None, {#}, {#}, {#}, \<lambda>_. []), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      [simp]: \<open>CS' \<noteq> []\<close>
    for CS' CS T
  proof -
    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses ?init =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
       \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow>
          the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) =
        learned_clss (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])))\<close>and
      snd_T_conflict: \<open>snd T \<noteq> {#} \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close> and
      false_in_conflict: \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close>
      using spec unfolding init_dt_wl_spec_def
      by fast+
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have \<open>snd T = {#}\<close>
      using snd_T_conflict confl by auto
    have \<open>\<exists>C\<in>set CS'. C \<noteq> []\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have E: \<open>\<forall>C\<in>set CS'. C = []\<close>
        by blast
      show False
        by (cases CS'; cases T) (use E false_in_conflict clss confl in \<open>auto simp: clauses_def CS\<close>)
    qed
    then show ?thesis
      unfolding extract_atms_clss_empty_iff by auto
  qed
  have CDCL_steps:
    \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) (fst T)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                     CS \<noteq> {#} \<and>
                     conflicting U \<noteq> None \<and>
                     backtrack_lvl U = 0 \<and> unsatisfiable (set_mset CS)))\<close>
    if
      CS_p: \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' (([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []), {#}) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      \<open>CS' \<noteq> []\<close> and
      \<open>extract_atms_clss CS' [] \<noteq> []\<close> and
      \<open>isasat_input_bounded_nempty (mset (extract_atms_clss CS' []))\<close>
    for CS' CS T
  proof -
    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None (fst T))\<close> and
      add_invs: \<open>twl_list_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses ?init =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
       \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow>
          the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) = learned_clss ?init\<close> and
      snd_T_conflict: \<open>snd T \<noteq> {#} \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close> and
      false_in_conflict: \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close> and
      no_decided: \<open>\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s\<close> and
      trail: \<open>(\<forall>L\<in>lits_of_l (get_trail_wl (fst T)). {#L#} \<in># get_unit_init_clss_wl (fst T))\<close>
        \<open>(\<forall>L\<in>set (get_trail_wl (fst T)). \<exists>K. L = Propagated K 0)\<close> and
      no_learned_unit: \<open>get_unit_learned_clss_wl (fst T) = {#}\<close> and
      corr_w: \<open>correct_watching (fst T)\<close>
      using spec unfolding init_dt_wl_spec_def
      by fast+
    have snd_T: \<open>snd T = {#}\<close>
      using confl snd_T_conflict by fast
    then have init_T: \<open>twl_st_of_wl_init T = (twl_st_of_wl None (fst T), {#})\<close>
      by (cases T) auto
    have
      struct_invs: \<open>twl_struct_invs (twl_st_of_wl None (fst T))\<close>
      using snd_T struct_invs by (subst (asm) twl_struct_invs_init_twl_struct_invs) (cases T; auto)+
    obtain M N NE Q W UE where
      S\<^sub>0: \<open>T = ((M, N, length N - 1, None, NE, UE, Q, W), {#})\<close>
      using U confl snd_T_conflict
      by (cases T) (auto simp: clauses_def mset_take_mset_drop_mset' get_unit_learned_clss_wl_def)
    have [simp]: \<open>UE = {#}\<close>
      using no_learned_unit unfolding S\<^sub>0 by (auto simp: get_unit_learned_clss_wl_def)

    have N_NE: \<open>mset `# mset (tl N) + NE = mset `# mset CS'\<close>
      using clss by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0)
    have trail_in_NE: \<open>\<forall>L\<in>lits_of_l M. {#L#} \<in># NE\<close>
      using trail unfolding S\<^sub>0 by (auto simp: get_unit_init_clss_wl_def)
    have n_d: \<open>no_dup M\<close>
      using struct_invs by (auto simp: twl_struct_invs_def S\<^sub>0 twl_struct_invs_init_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
    have prop_M: \<open>\<forall>L\<in> set M. \<exists>K. L = Propagated K 0\<close>
      using trail by (auto simp: S\<^sub>0)
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have 0: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], CS, {#}, None)
       (convert_lits_l N M, mset `# mset CS', {#}, None)\<close>
      using trail_in_NE prop_M n_d
      apply (induction M)
      subgoal by (auto simp: CS)
      subgoal for L M
        apply (rule rtranclp.rtrancl_into_rtrancl)
         apply (simp; fail)
        apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
         apply (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def CS
            N_NE[symmetric])
        done
      done
    then have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state CS)
       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T))))\<close>
      using 0 by (auto simp: S\<^sub>0 CS mset_take_mset_drop_mset' N_NE init_state.simps)
    have clss_CS':
       \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T)))) =
          mset `# mset CS'\<close>
      using snd_T clss by (cases T) (auto simp: clauses_def)
    have \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))
        (all_lits_of_mm (mset `# mset CS'))\<close>
      by (auto simp add: isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l_def isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def
        all_lits_of_mm_add_mset in_extract_atms_clssD in_extract_atms_clsD
        all_lits_of_mm_def atms_of_s_def image_image image_Un)
    have [simp]: \<open>isasat_input_bounded (mset (extract_atms_clss CS' []))\<close>
      unfolding isasat_input_bounded_def
    proof
      fix L
      assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' []))\<close>
      then obtain C where
        L: \<open>C\<in>set CS' \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
        by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
           isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
      have \<open>\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max\<close>
        using CS_p by auto
      then have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
        using L unfolding CS by auto
      then show \<open>nat_of_lit L \<le> uint_max\<close>
        using L
        by (cases L) (auto simp: CS in_extract_atms_clssD uint_max_def)
    qed
    have 2:\<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' []))
             (from_init_state T)
            \<le> \<Down> {(S, S'). S' = st_l_of_wl None S}
               (SPEC (\<lambda>Ta. cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of_wl None (from_init_state T))
                 (twl_st_of None Ta) \<and>
                final_twl_state (twl_st_of None Ta)))\<close>
      apply (rule isasat_input_bounded.cdcl_twl_stgy_prog_wl_D_spec_final2_Down
        [of \<open>(mset (extract_atms_clss CS' []))\<close>])
      using CS_p \<L>\<^sub>a\<^sub>l\<^sub>l
        struct_invs stgy_invs corr_w add_invs clss 1 confl clss clss_CS'
      by (auto simp: from_init_state_def)
    (* then have 2:
      \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' []))
         (from_init_state T)
       \<le> SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (from_init_state T))))
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None U))))\<close>
      using isasat_input_bounded.cdcl_twl_stgy_prog_wl_spec_final2[of
          \<open>mset (extract_atms_clss CS' [])\<close> \<open>(from_init_state T)\<close>] CS_p \<L>\<^sub>a\<^sub>l\<^sub>l
        struct_invs stgy_invs corr_w add_invs clss 1 confl clss clss_CS'
      by (auto simp: from_init_state_def) *)
    have RES_SPEC: \<open>RES ({(S', S). S = state\<^sub>W_of (twl_st_of_wl None S')}\<inverse> ``
            Collect (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS))) =
     SPEC (\<lambda>S'. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ([], CS, {#}, None)
                   (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S'))))\<close>
      by auto
    have [simp]: \<open>backtrack_lvl (state\<^sub>W_of (twl_st_of_wl None U)) = count_decided (get_trail_wl U)\<close> for U
      by (cases U) auto
    have [simp]: \<open>count_decided (get_trail (twl_st_of_wl None U)) = count_decided (get_trail_wl U)\<close> for U
      by (cases U) auto
    have [simp]: \<open>twl_st_of None (st_l_of_wl None U) = twl_st_of_wl None U\<close> for U
      by auto
    note twl_st_of_wl.simps[simp del]
    have ?thesis
      unfolding TWL_to_clauses_state_conv_def RES_SPEC from_init_state_def[symmetric]
      apply (rule order_trans)
      apply (rule 2)
      unfolding conc_fun_RES less_eq_nres.simps (* TODO refactor *)
      apply rule
      subgoal for U
        apply (subgoal_tac \<open>twl_struct_invs (twl_st_of None (st_l_of_wl None U))\<close>)
        subgoal
          using 1 struct_invs
          by (auto simp: conc_fun_RES final_twl_state_def from_init_state_def[symmetric] full_def
              cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state_empty_no_step cdcl\<^sub>W_stgy_cdcl\<^sub>W_init_state
              conflicting_twl_st_of_wl get_trail_l_st_l_of_wl
              intro!: twl_conflict_of_level_unsatisfiable_from_init
              simp del: twl_st_of.simps st_l_of_wl.simps split_paired_All
              init_state.simps
              dest: rtranclp_trans
              dest!: rtranclp_cdcl_twl_stgy_cdcl\<^sub>W_stgy no_step_cdcl_twl_stgy_no_step_cdcl\<^sub>W_stgy)
        subgoal
          using struct_invs
          by (auto intro: rtranclp_cdcl_twl_stgy_twl_struct_invs simp: from_init_state_def)
        done
      done
    then show ?thesis
      unfolding confl if_True
      by (auto intro: ref_two_step simp: from_init_state_def)
  qed
  show ?thesis
    unfolding SAT_wl_def SAT_def from_init_state_def to_init_state_def
     isasat_input_ops.empty_watched_alt_def finalise_init_def id_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      apply (rewrite at \<open>let _ = extract_atms_clss _ _ in _\<close> Let_def)
      apply (rewrite at \<open>let _ = isasat_input_ops.init_state_wl _ in _\<close> Let_def)
      apply (simp only: if_False isasat_input_ops.init_state_wl_def
          isasat_input_ops.empty_watched_alt_def)
      apply (refine_vcg bind_refine_spec (*isasat_input_bounded.init_dt_init_dt_l*) lhs_step_If
          init_dt_wl_init_dt_wl_spec)
      subgoal for T by (rule conflict_during_init)
      subgoal for T by (rule empty_clss)
      subgoal by (rule extract_atms_clss_not_nil)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel
         isasat_input_bounded_nempty_def isasat_input_bounded_nempty_axioms_def)
      subgoal by (rule CDCL_steps)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal using \<L>\<^sub>a\<^sub>l\<^sub>l by simp
      done
    done
qed

definition model_if_satisfiable :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>model_if_satisfiable CS = SPEC (\<lambda>M.
           if satisfiable (set_mset CS) then M \<noteq> None \<and> set (the M) \<Turnstile>sm CS else M = None)\<close>

definition SAT' :: \<open>nat clauses \<Rightarrow> nat literal list option nres\<close> where
  \<open>SAT' CS = do {
     T \<leftarrow> SAT CS;
     RETURN(if conflicting T = None then Some (map lit_of (trail T)) else None)
  }
\<close>


lemma SAT_model_if_satisfiable:
  \<open>(SAT', model_if_satisfiable) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C)]\<^sub>f Id\<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in>[\<lambda>CS. ?P CS]\<^sub>f Id \<rightarrow> _\<close>)
proof -
  have H: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (init_state CS)\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (init_state CS)\<close>
    if \<open>?P CS\<close> for CS
    using that by (auto simp:
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def twl_list_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def
        distinct_mset_set_def)
  show ?thesis
    unfolding SAT'_def model_if_satisfiable_def SAT_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      using H[of CS]
        cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>init_state CS\<close>]
      by (fastforce intro!: le_SPEC_bindI simp: RES_RETURN_RES clauses_def
          true_annots_true_cls lits_of_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
          dest: conflict_of_level_unsatisfiable)
    done
qed

lemma (in isasat_input_bounded) init_dt_wl_heur_init_dt_wl:
  \<open>(uncurry init_dt_wl_heur, uncurry init_dt_wl) \<in>
    [\<lambda>(CS, S). (\<forall>C \<in> set CS. literals_are_in_\<L>\<^sub>i\<^sub>n (mset C)) \<and> distinct_mset_set (mset ` set CS)]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f twl_st_heur_init \<rightarrow> \<langle>twl_st_heur_init\<rangle> nres_rel\<close>
  unfolding init_dt_wl_heur_def init_dt_wl_def uncurry_def
  apply (intro frefI nres_relI)
  apply (case_tac y rule: prod.exhaust)
  apply (case_tac x rule: prod.exhaust)
  apply (simp only: prod.case prod_rel_iff)
  apply (refine_vcg init_dt_step_wl_heur_init_dt_step_wl[THEN fref_to_Down_curry])
  apply normalize_goal+
  apply assumption
  subgoal by fast
  subgoal by simp
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn unat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have ex_remove_xs:
    \<open>(\<exists>xs. mset xs = mset x \<and> {#literal_of_nat (nat_of_uint32 x). x \<in># mset xs#} = y) \<longleftrightarrow>
       ({#literal_of_nat (nat_of_uint32 x). x \<in># mset x#} = y)\<close>
    for x y
    by auto

  show ?thesis
    unfolding list_assn_pure_conv list_mset_assn_pure_conv list_mset_assn_pure_conv
     list_rel_mset_rel_internal
    apply (auto simp: hr_comp_def)
    apply (auto simp: ent_ex_up_swap list_mset_assn_def pure_def)
    using ex_mset[of \<open>map (\<lambda>x. literal_of_nat (nat_of_uint32 x)) `# mset xs'\<close>]
    by (auto simp add: list_mset_rel_def br_def mset_rel_def unat_lit_rel_def
        uint32_nat_rel_def nat_lit_rel_def
        p2rel_def Collect_eq_comp rel2p_def lit_of_natP_def[abs_def]
        list_all2_op_eq_map_map_right_iff rel_mset_def rel2p_def[abs_def]
        list_all2_op_eq_map_right_iff' ex_remove_xs list_rel_def
        list_all2_op_eq_map_right_iff
        simp del: literal_of_nat.simps)
qed

(* TODO Move *)
lemma (in -)fref_to_Down_explode:
  \<open>(f a, g a) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' b. P x' \<Longrightarrow> (x, x') \<in> A \<Longrightarrow> b = a \<Longrightarrow> f a x \<le> \<Down> B (g b x'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto
(* End Move *)

lemma IsaSAT_heur_IsaSAT: \<open>(IsaSAT_heur, IsaSAT) \<in>
     [\<lambda>CS.  Multiset.Ball (mset CS) distinct]\<^sub>f
     Id \<rightarrow> \<langle>{((M, stat), M'). M = M'}\<rangle>nres_rel\<close>
proof -
  define f :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where \<open>f = RETURN\<close>
  have IsaSAT_heur_alt_def:
    \<open>IsaSAT_heur CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset (extract_atms_clss CS []);
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    S \<leftarrow> isasat_input_ops.init_state_wl_heur \<A>\<^sub>i\<^sub>n';
    S \<leftarrow> f S;
    (T::twl_st_wl_heur_init) \<leftarrow> isasat_input_ops.init_dt_wl_heur \<A>\<^sub>i\<^sub>n' CS S;
    T \<leftarrow> f T;
    if \<not>get_conflict_wl_is_None_heur_init T
    then RETURN (empty_init_code)
    else if CS = [] then RETURN (empty_conflict_code)
    else do {
       ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
       ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
       ASSERT((\<lambda>(M', N', D', Q', W', ((ns, m, fst_As, lst_As, next_search), to_remove), \<phi>, clvls). fst_As \<noteq> None \<and>
         lst_As \<noteq> None) T);
       T \<leftarrow> finalise_init_code (T::twl_st_wl_heur_init);
       U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D_heur \<A>\<^sub>i\<^sub>n' T;
       RETURN (if get_conflict_wl_is_None_heur U then extract_model_of_state_stat U
         else extract_state_stat U)
     }
  }\<close> for CS
    unfolding IsaSAT_heur_def f_def by auto

  have [refine]: \<open>(T, T') \<in> isasat_input_ops.twl_st_heur_init_wl N \<Longrightarrow>
    f T \<le> \<Down> {(T, (T', OS)). (T, T') \<in> isasat_input_ops.twl_st_heur_init_wl N}
        (RETURN (to_init_state T'))\<close>
    (is \<open>_ \<Longrightarrow> _ \<le> \<Down> ?init _\<close>)
    for T T' N
    by (auto simp: f_def to_init_state_def)
  have init: \<open>isasat_input_ops.init_dt_wl_heur (mset (extract_atms_clss CS [])) CS
       T'
      \<le> \<Down> (isasat_input_ops.twl_st_heur_init (mset (extract_atms_clss CS' [])))
          (isasat_input_ops.init_dt_wl (*mset (extract_atms_clss CS' [])*)
            CS' (to_init_state
                 (isasat_input_ops.init_state_wl
                   (mset (extract_atms_clss CS' [])))))\<close>
    if
      distinct: \<open>Multiset.Ball (mset CS') distinct\<close> and
      SS': \<open>(CS, CS') \<in> Id\<close> and
      bounded: \<open>isasat_input_bounded (mset (extract_atms_clss CS' []))\<close> and
      TT': \<open>inres (f T) T'\<close> and
      T': \<open>(T', to_init_state (isasat_input_ops.init_state_wl (mset (extract_atms_clss CS' []))))
     \<in> {(T, T', OS).
         (T, T')
         \<in> isasat_input_ops.twl_st_heur_init_wl
             (mset (extract_atms_clss CS' []))}\<close>
    for CS CS' T T'
  proof -
    have SS': \<open>CS = CS'\<close>
      using SS' by auto
    have [simp]: \<open>T = T'\<close>
      using TT' unfolding f_def by auto
    show ?thesis
      unfolding SS'
      apply (rule isasat_input_bounded.init_dt_wl_heur_init_dt_wl[THEN fref_to_Down_curry,
            unfolded comp_def])
      subgoal by (rule bounded)
      subgoal using T' by (auto simp: isasat_input_ops.twl_st_heur_init_def
            isasat_input_ops.twl_st_heur_init_wl_def)
      subgoal using T' by (auto simp: isasat_input_ops.twl_st_heur_init_def
            isasat_input_ops.twl_st_heur_init_wl_def)
      done
  qed
  have from_init_state: \<open>f T \<le> \<Down> (isasat_input_ops.twl_st_heur_init_wl (mset (extract_atms_clss CS' [])))
          (RETURN (from_init_state T'))\<close>
    if
      TT': \<open>(T, T')
     \<in> isasat_input_ops.twl_st_heur_init
         (mset (extract_atms_clss CS' []))\<close>
    for T T' CS CS'
  proof -
    show ?thesis
      using TT'
      unfolding f_def
      by (auto simp: isasat_input_ops.twl_st_heur_init_def from_init_state_def
         isasat_input_ops.twl_st_heur_init_wl_def)
  qed
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
  unfolding IsaSAT_heur_alt_def IsaSAT_def
    apply (intro frefI nres_relI bind_refine if_refine)
    apply (refine_vcg
           init_state_wl_heur_init_state_wl[THEN fref_to_Down, unfolded comp_def, OF refl]
           init
           from_init_state
           isasat_input_ops.finalise_init_finalise_init[THEN fref_to_Down, unfolded comp_def]
           isasat_input_bounded_nempty.cdcl_twl_stgy_prog_wl_D_heur_cdcl_twl_stgy_prog_wl_D
             [THEN fref_to_Down_explode, unfolded comp_def])
    subgoal by auto
    subgoal by auto
    subgoal by auto
                apply (assumption)+
    subgoal for CS CS' S S' T T'
      by (auto simp:  isasat_input_ops.twl_st_heur_init_wl_def
          get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_init_def
          get_conflict_wl_is_None_def)
    subgoal premises p
        by (auto simp: empty_init_code_def)
      subgoal for CS CS' S S' T T'
      by (auto simp:  isasat_input_ops.twl_st_heur_init_wl_def
          get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_init_def
          get_conflict_wl_is_None_def)
    subgoal premises p
      by (auto simp: empty_conflict_code_def)
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: isasat_input_ops.vmtf_init_def
          isasat_input_ops.twl_st_heur_init_wl_def)
    subgoal
      by (auto simp: isasat_input_ops.vmtf_init_def
          isasat_input_ops.twl_st_heur_init_wl_def)
    subgoal
      by (auto simp:  isasat_input_ops.twl_st_heur_init_wl_def
          get_conflict_wl_is_None_heur_init_def get_conflict_wl_is_None_init_def
          get_conflict_wl_is_None_def split: option.splits)
    apply assumption+
    subgoal ..
    subgoal by simp
    subgoal by simp
    subgoal premises p
      using p(25) (* only last assumption *)
      by (auto simp: extract_model_of_state_stat_def extract_model_of_state_def
         extract_stats_def isasat_input_ops.twl_st_heur_def get_conflict_wl_is_None_heur_def
          get_conflict_wl_is_None_heur_init_def extract_state_stat_def
          get_conflict_wl_is_None_def split: option.splits)
    done
qed

lemma IsaSAT_code: \<open>(IsaSAT_code, SAT')
    \<in> [\<lambda>x. Multiset.Ball x distinct_mset \<and> (\<forall>C\<in>#x. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>a
      clauses_l_assn\<^sup>k \<rightarrow> model_assn\<close>
proof -
  define empty_trail where
    \<open>empty_trail = Some ([] :: nat literal list)\<close>
  have IsaSAT: \<open>IsaSAT CS =
    do {
     ASSERT (isasat_input_bounded (mset (extract_atms_clss CS [])));
     ASSERT (distinct (extract_atms_clss CS []));
     T \<leftarrow> SAT_wl CS;
     RETURN (if get_conflict_wl T = None then extract_model_of_state T else None)
    }\<close> for CS
    unfolding IsaSAT_def SAT_wl_def Let_def get_conflict_wl_is_None_init_def
     finalise_init_def id_def get_conflict_wl_is_None[symmetric] empty_trail_def
    by (force cong: bind_cong simp: extract_model_of_state_def intro: bind_cong)

  have 2: \<open>Multiset.Ball y distinct_mset \<Longrightarrow>
       (x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<Longrightarrow>
        (\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max) \<Longrightarrow>
       SAT_wl x \<le> \<Down> TWL_to_clauses_state_conv (SAT y)\<close> for x y
    using cdcl_twl_stgy_prog_wl_spec_final2[unfolded fref_def nres_rel_def] by simp
  have [simp]: \<open>SAT {#} = SPEC (\<lambda>U. U = init_state {#})\<close>
    using full_cdcl\<^sub>W_init_state unfolding SAT_def Let_def
    by auto
  have SAT': \<open>SAT' CS =
       do {
          ASSERT(True);ASSERT(True);
          U \<leftarrow> SAT CS;
          RETURN(if conflicting U = None then Some (map lit_of (trail U)) else None)
      }\<close> for CS
    unfolding SAT'_def SAT_def empty_trail_def by (auto simp: RES_RETURN_RES)
  have 3:
    \<open>ASSERT (isasat_input_bounded (mset (extract_atms_clss x []))) \<le> \<Down> unit_rel (ASSERT True)\<close>
    if CS_p: \<open>(\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
       CS: \<open>(x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close>
       for x y
    apply (rule ASSERT_refine)
    unfolding isasat_input_bounded_def
  proof
    fix L
    assume L: \<open>L \<in># isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss x []))\<close>
    then obtain C where
      L: \<open>C\<in>set x \<and> (L \<in>set C \<or> - L \<in> set C)\<close>
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def nat_of_uint32_uint32_of_nat_id
         isasat_input_ops.\<L>\<^sub>a\<^sub>l\<^sub>l_def)
    have \<open>\<forall>C\<in>#y. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max\<close>
      using CS_p by auto
    then have \<open>nat_of_lit L \<le> uint_max \<or> nat_of_lit (-L) \<le> uint_max\<close>
      using L CS by (auto simp: list_mset_rel_def br_def mset_rel_def rel2p_def[abs_def] p2rel_def
        rel_mset_def list_all2_op_eq_map_right_iff')
    then show \<open>nat_of_lit L \<le> uint_max\<close>
      using L
      by (cases L) (auto simp: in_extract_atms_clssD uint_max_def)
  qed
  have 4: \<open>ASSERT (distinct (extract_atms_clss x [])) \<le> \<Down> unit_rel (ASSERT True)\<close> for x
    by (auto simp: distinct_extract_atms_clss)
  have IsaSAT_SAT: \<open>(IsaSAT, SAT') \<in>
     [\<lambda>CS. Multiset.Ball CS distinct_mset \<and>
      (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>f
     list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle> option_rel\<rangle>nres_rel\<close>
    unfolding SAT' IsaSAT
    apply (intro frefI nres_relI bind_refine if_refine)
         apply (rule 3; simp; fail)
        apply (rule 4; simp; fail)
     apply (rule 2)
    by (auto simp: TWL_to_clauses_state_conv_def convert_lits_l_def extract_model_of_state_def
        state_wl_l_def twl_st_l_def)
    have H: \<open>hr_comp model_stat_assn
        (Collect (case_prod (\<lambda>(M, stat). op = M))) = model_assn\<close>
      by (auto simp: model_assn_def hr_comp_def model_stat_rel_def ex_assn_pair_split eq_commute
          intro!: ext)
  have H: \<open>(IsaSAT_code, IsaSAT)
      \<in> [\<lambda>x. Ball (set x) distinct]\<^sub>a (list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow> model_assn\<close>
    using IsaSAT_code.refine[FCOMP IsaSAT_heur_IsaSAT]
    unfolding list_assn_list_mset_rel_clauses_l_assn H
    by auto
  thm hfref_compI_PRE[OF H IsaSAT_SAT]
  show ?thesis
    (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
  proof -
    have H: \<open>?c \<in>
       [comp_PRE
     (list_mset_rel O
      \<langle>list_mset_rel\<rangle>mset_rel)
     (\<lambda>CS. Multiset.Ball CS distinct_mset \<and>
           (\<forall>C\<in>#CS.
               \<forall>L\<in>#C.
                  nat_of_lit L \<le> uint_max))
     (\<lambda>x y. Ball (set y) distinct)
     (\<lambda>x. nofail
           (SAT'
             x))]\<^sub>a hrp_comp
                     ((list_assn
  (list_assn unat_lit_assn))\<^sup>k)
                     (list_mset_rel O
\<langle>list_mset_rel\<rangle>mset_rel) \<rightarrow> hr_comp
       model_assn
       (\<langle>\<langle>nat_lit_lit_rel\<rangle>list_rel\<rangle>option_rel)\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
      using hfref_compI_PRE[OF H IsaSAT_SAT] .
    have pre: \<open>?pre' x\<close> if \<open>?pre x\<close> for x
      using that by (auto simp: comp_PRE_def list_mset_rel_def br_def
          mset_rel_def p2rel_def rel2p_def[abs_def] rel_mset_def
          list_all2_op_eq_map_right_iff')
    have im: \<open>?im' = ?im\<close>
      unfolding  prod_hrp_comp hrp_comp_dest hrp_comp_keep
        list_assn_list_mset_rel_clauses_l_assn
      ..
    have f: \<open>?f' = ?f\<close>
      by auto
    show ?thesis
      apply (rule hfref_weaken_pre[OF ])
       defer
      using H unfolding im f apply assumption
      using pre ..
  qed
qed

text \<open>Final correctness theorem:\<close>
lemmas IsaSAT_code_full_correctness = IsaSAT_code[FCOMP SAT_model_if_satisfiable]

end
