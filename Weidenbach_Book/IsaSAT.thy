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
         (CS \<noteq> {#} \<and> learned_clss U = {#} \<and> conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
          unsatisfiable (set_mset CS)))
  }\<close>

definition (in -) SAT_wl :: \<open>nat clauses_l \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let \<A>\<^sub>i\<^sub>n' = extract_atms_clss CS [];
    let S = isasat_input_ops.init_state_wl (mset \<A>\<^sub>i\<^sub>n');
    T \<leftarrow> isasat_input_ops.init_dt_wl (mset \<A>\<^sub>i\<^sub>n') CS (to_init_state S);
    let T = from_init_state T;
    if get_conflict_wl T \<noteq> None
    then RETURN T
    else if CS = [] then RETURN (([], [], 0, None, {#}, {#}, {#}, \<lambda>_. undefined))
    else do {
       ASSERT (extract_atms_clss CS [] \<noteq> []);
       ASSERT(isasat_input_bounded_nempty (mset \<A>\<^sub>i\<^sub>n'));
       isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset \<A>\<^sub>i\<^sub>n') (finalise_init T)
    }
  }\<close>


definition extract_model_of_state where
  \<open>extract_model_of_state U = map lit_of (get_trail_wl U)\<close>

definition IsaSAT :: \<open>nat clauses_l \<Rightarrow> nat literal list option nres\<close> where
  \<open>IsaSAT CS = do{
    let \<A>\<^sub>i\<^sub>n' = mset (extract_atms_clss CS []);
    ASSERT(isasat_input_bounded \<A>\<^sub>i\<^sub>n');
    ASSERT(distinct_mset \<A>\<^sub>i\<^sub>n');
    let S = isasat_input_ops.init_state_wl \<A>\<^sub>i\<^sub>n';
    let S = to_init_state S;
    T \<leftarrow> isasat_input_ops.init_dt_wl \<A>\<^sub>i\<^sub>n' CS S;
    let T = from_init_state T;
    if \<not>get_conflict_wl_is_None_init T
    then RETURN None
    else if CS = [] then RETURN (Some [])
    else do {
       ASSERT(\<A>\<^sub>i\<^sub>n' \<noteq> {#});
       ASSERT(isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n');
       let T = finalise_init T;
       U \<leftarrow> isasat_input_ops.cdcl_twl_stgy_prog_wl_D \<A>\<^sub>i\<^sub>n' T;
       RETURN (if get_conflict_wl U = None then Some (extract_model_of_state U) else None)
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

lemma cdcl_twl_stgy_prog_wl_D_code_ref':
  \<open>(uncurry (\<lambda>_. cdcl_twl_stgy_prog_wl_D_code), uncurry isasat_input_ops.cdcl_twl_stgy_prog_wl_D)
  \<in> [\<lambda>(N, _). N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded_nempty \<A>\<^sub>i\<^sub>n]\<^sub>a
     (list_mset_assn uint32_nat_assn)\<^sup>k *\<^sub>a
    (isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n)\<^sup>d \<rightarrow> isasat_input_ops.twl_st_assn \<A>\<^sub>i\<^sub>n\<close>
  unfolding hfref_def hn_refine_def
  apply (subst in_pair_collect_simp)
  apply (intro allI impI)
  subgoal for a c
    using cdcl_twl_stgy_prog_wl_D_code.refine[of \<A>\<^sub>i\<^sub>n,
      unfolded in_pair_collect_simp hfref_def hn_refine_def PR_CONST_def,
      rule_format, of \<open>snd c\<close> \<open>snd a\<close>]
    apply (cases a)
    by (sep_auto
      dest!: frame_rule_left[of \<open>isasat_input_ops.twl_st_assn _ _ _\<close> _ _\<open>list_mset_assn uint32_nat_assn \<A>\<^sub>i\<^sub>n (fst a)\<close>])
  done

declare cdcl_twl_stgy_prog_wl_D_code_ref'[to_hnr, OF refl, sepref_fr_rules]

definition get_trail_wl_code :: \<open>twl_st_wll_trail \<Rightarrow> uint32 list\<close> where
  \<open>get_trail_wl_code = (\<lambda>((M, _), _). M)\<close>

lemma (in isasat_input_ops) get_trail_wl[sepref_fr_rules]:
  \<open>(return o get_trail_wl_code, RETURN o extract_model_of_state) \<in> twl_st_assn\<^sup>d \<rightarrow>\<^sub>a
       list_assn unat_lit_assn\<close>
proof -
  have [simp]: \<open>(\<lambda>a c. \<up> ((c, a) \<in> unat_lit_rel)) = unat_lit_assn\<close>
    by (auto simp: unat_lit_rel_def pure_def)
  show ?thesis
    by sepref_to_hoare
      (sep_auto simp: twl_st_assn_def twl_st_heur_def hr_comp_def trail_pol_def twl_st_heur_assn_def
        twl_st_heur_init_assn_def get_trail_wl_code_def
        extract_model_of_state_def
        dest!: ann_lits_split_reasons_map_lit_of)
qed

declare isasat_input_ops.get_trail_wl[sepref_fr_rules]
declare isasat_input_ops.finalise_init_code_hnr[unfolded PR_CONST_def, sepref_fr_rules]
sepref_register to_init_state from_init_state get_conflict_wl_is_None_init

sepref_definition IsaSAT_code
  is \<open>IsaSAT\<close>
  :: \<open>(list_assn (list_assn unat_lit_assn))\<^sup>k \<rightarrow>\<^sub>a option_assn (list_assn unat_lit_assn)\<close>
  unfolding IsaSAT_def
    get_conflict_wl_is_None extract_model_of_state_def[symmetric]
  supply get_conflict_wl_is_None_init_def[simp]
  isasat_input_bounded.get_conflict_wl_is_None_code_get_conflict_wl_is_None[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_code_get_conflict_wl_is_None_no_lvls[sepref_fr_rules]
  isasat_input_ops.to_init_state_hnr[sepref_fr_rules]
  isasat_input_ops.from_init_state_hnr[sepref_fr_rules]
  isasat_input_bounded.get_conflict_wl_is_None_init_wl_hnr[
    unfolded get_conflict_wl_is_None_init_def[symmetric], sepref_fr_rules]
  supply id_mset_list_assn_list_mset_assn[sepref_fr_rules] get_conflict_wl_is_None_def[simp]
   option.splits[split]
  apply (rewrite at \<open>extract_atms_clss _ \<hole>\<close> op_extract_list_empty_def[symmetric])
  apply (rewrite at \<open>Some \<hole>\<close> HOL_list.fold_custom_empty)
  supply [[goals_limit = 1]]
  by sepref

code_printing constant nth_u_code \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ Word32.toInt _))"

code_printing constant heap_array_set'_u \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (Word32.toInt (_)),/ (_)))"

code_printing constant two_uint32 \<rightharpoonup> (SML) "(Word32.fromInt 2)"

export_code IsaSAT_code checking SML_imp
export_code IsaSAT_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
    uint32_of_nat
  in SML_imp module_name SAT_Solver file "code/IsaSAT_solver.sml"

definition TWL_to_clauses_state_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset) set\<close> where
  \<open>TWL_to_clauses_state_conv = {(S', S). S = state\<^sub>W_of (twl_st_of_wl None S')}\<close>


lemma full_cdcl\<^sub>W_init_state:
  \<open>full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state {#}) S \<longleftrightarrow> S = init_state {#}\<close>
  unfolding full_def rtranclp_unfold
  by (subst tranclp_unfold_begin)
     (auto simp:  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps
      cdcl\<^sub>W_restart_mset.conflict.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps
       cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset.decide.simps
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps cdcl\<^sub>W_restart_mset.backtrack.simps
      cdcl\<^sub>W_restart_mset.skip.simps cdcl\<^sub>W_restart_mset.resolve.simps
      cdcl\<^sub>W_restart_mset_state clauses_def)

(* End Move *)
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

lemma conflict_of_level_unsatisfiable:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses S))\<close>
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

lemma cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and>
        (\<forall>C \<in># CS. \<forall>L \<in># C. nat_of_lit L \<le> uint_max)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>TWL_to_clauses_state_conv\<rangle>nres_rel\<close>
proof -
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

  have \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' [])) (all_lits_of_mm (mset `# mset CS'))\<close>
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
                     CS \<noteq> {#} \<and> learned_clss U = {#} \<and> conflicting U \<noteq> None \<and> backtrack_lvl U = 0 \<and>
                    unsatisfiable (set_mset CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []) T\<close> and
      confl: \<open>get_conflict_wl (fst T) \<noteq> None\<close>
    for T CS CS'
  proof -
    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []))) =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
       \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow> the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) =
        learned_clss (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])))\<close>
      using spec unfolding init_dt_wl_spec_def
      by fast+
    have count_dec: \<open>count_decided (get_trail_wl (fst T)) = 0\<close>
      using count_dec unfolding count_decided_0_iff by blast
    have CS: \<open>CS = mset `# mset CS'\<close>
      using CS'_CS by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    have le: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause
         (state\<^sub>W_of_init (twl_st_of_init (st_l_of_wl_init T)))\<close> and
      all_struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (state\<^sub>W_of_init (twl_st_of_init (st_l_of_wl_init T)))\<close>
      using struct_invs unfolding twl_struct_invs_init_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        twl_st_of_wl_init.simps twl_st_of_init.simps
      by fast+
    have \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting (state\<^sub>W_of_init (twl_st_of_wl_init T))\<close>
      using struct_invs unfolding twl_struct_invs_init_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      by fast
    have [simp]: \<open>CS' \<noteq> []\<close>
      using confl_in_clss confl by (cases T) auto
    have \<open>unsatisfiable (set_mset (mset `# mset (rev CS')))\<close>
      using conflict_of_level_unsatisfiable[OF all_struct_invs] count_dec confl learned clss
      by (cases T)
        (auto simp: clauses_def mset_take_mset_drop_mset'
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
    then have [simp]: \<open>unsatisfiable (mset ` set CS')\<close>
      by auto
    show ?thesis
      apply (rule RETURN_SPEC_refine)
      apply (rule exI[of _ \<open>state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T)))\<close>])
      apply (intro conjI)
      subgoal by (cases T) (clarsimp_all simp: TWL_to_clauses_state_conv_def mset_take_mset_drop_mset'
            clauses_def get_unit_learned_def in_list_mset_rel in_list_mset_rel_mset_rel)
      subgoal
        apply (rule disjI2)
        using \<L>\<^sub>a\<^sub>l\<^sub>l struct_invs learned count_dec U clss confl
        by (cases T) (clarsimp simp: CS)
      done
  qed
  have empty_clss:
   \<open>RETURN ([], [], 0, None, {#}, {#}, {#}, \<lambda>_. undefined)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                     CS \<noteq> {#} \<and>
                     learned_clss U = {#} \<and>
                     conflicting U \<noteq> None \<and> backtrack_lvl U = 0 \<and> unsatisfiable (set_mset CS)))\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []) T\<close> and
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
      by (cases T) (auto simp: clauses_def TWL_to_clauses_state_conv_def)
  qed
  have extract_atms_clss_not_nil: \<open>extract_atms_clss CS' [] \<noteq> []\<close>
    if
      \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      [simp]: \<open>CS' \<noteq> []\<close>
    for CS' CS T
  proof -
    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []))) =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
       \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow> the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) =
        learned_clss (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])))\<close> and
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
        by (cases CS'; cases T) (use E false_in_conflict clss  confl in \<open>auto simp: clauses_def CS\<close>)
    qed
    then show ?thesis
      unfolding extract_atms_clss_empty_iff by auto
  qed
  have CDCL_steps:  \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) (fst T)
      \<le> \<Down> TWL_to_clauses_state_conv
          (SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS) U \<or>
                     CS \<noteq> {#} \<and>
                     learned_clss U = {#} \<and>
                     conflicting U \<noteq> None \<and>
                     backtrack_lvl U = 0 \<and> unsatisfiable (set_mset CS)))\<close>
    if
      CS_p: \<open>Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)\<close> and
      CS'_CS: \<open>(CS', CS) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel\<close> and
      spec: \<open>init_dt_wl_spec CS' ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []) T\<close> and
      confl: \<open>\<not> get_conflict_wl (fst T) \<noteq> None\<close> and
      \<open>CS' \<noteq> []\<close> and
      \<open>extract_atms_clss CS' [] \<noteq> []\<close> and
      \<open>isasat_input_bounded_nempty (mset (extract_atms_clss CS' []))\<close>
    for CS' CS T
  proof -
    have
      struct_invs: \<open>twl_struct_invs_init (twl_st_of_wl_init T)\<close> and
      stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None (fst T))\<close> and
      add_invs: \<open>additional_WS_invs (st_l_of_wl None (fst T))\<close> and
      clss: \<open>mset `# mset (rev CS') + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. []))) =
        cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None (fst T))) + snd T\<close> and
      count_dec: \<open>(\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s)\<close> and
      U: \<open>get_learned_wl (fst T) = length (get_clauses_wl (fst T)) - 1\<close>  and
      confl_in_clss:
       \<open>get_conflict_wl (fst T) \<noteq> None \<longrightarrow> the (get_conflict_wl (fst T)) \<in># mset `# mset (rev CS')\<close> and
      learned: \<open>learned_clss (state\<^sub>W_of (twl_st_of_wl None (fst T))) =
        learned_clss (state\<^sub>W_of (twl_st_of_wl None ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])))\<close> and
      snd_T_conflict: \<open>snd T \<noteq> {#} \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close> and
      false_in_conflict: \<open>{#} \<in># mset `# mset CS' \<longrightarrow> get_conflict_wl (fst T) \<noteq> None\<close> and
      no_decided: \<open>\<forall>s\<in>set (get_trail_wl (fst T)). \<not> is_decided s\<close> and
      trail: \<open>(\<forall>L\<in>lits_of_l (get_trail_wl (fst T)). {#L#} \<in># get_unit_init_clss (fst T))\<close>
        \<open>(\<forall>L\<in>set (get_trail_wl (fst T)). \<exists>K. L = Propagated K 0)\<close> and
      no_learned_unit: \<open>get_unit_learned (fst T) = {#}\<close> and
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
    obtain M N NP Q W UP where
      S\<^sub>0: \<open>T = ((M, N, length N - 1, None, NP, UP, Q, W), {#})\<close>
      using U confl snd_T_conflict
      by (cases T) (auto simp: clauses_def mset_take_mset_drop_mset' get_unit_learned_def)
    have [simp]: \<open>UP = {#}\<close>
      using no_learned_unit unfolding S\<^sub>0 by (auto simp: get_unit_learned_def)

    have N_NP: \<open>mset `# mset (tl N) + NP = mset `# mset CS'\<close>
      using clss by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0)
    have trail_in_NP: \<open>\<forall>L\<in>lits_of_l M. {#L#} \<in># NP\<close>
      using trail unfolding S\<^sub>0 by (auto simp: get_unit_init_clss_def)
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
      using trail_in_NP prop_M n_d
      apply (induction M)
      subgoal by (auto simp: CS)
      subgoal for L M
        apply (rule rtranclp.rtrancl_into_rtrancl)
         apply (simp; fail)
        apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
         apply (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps clauses_def CS
            N_NP[symmetric])
        done
      done
    then have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state CS)
       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T))))\<close>
      using 0 by (auto simp: S\<^sub>0 CS mset_take_mset_drop_mset' N_NP init_state.simps)
    have clss_CS': \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (fst T))))
        = (mset `# mset CS')\<close>
      using snd_T clss by (cases T) (auto simp: clauses_def)
    have
      \<L>\<^sub>a\<^sub>l\<^sub>l: \<open>isasat_input_ops.is_\<L>\<^sub>a\<^sub>l\<^sub>l (mset (extract_atms_clss CS' [])) (all_lits_of_mm (mset `# mset CS'))\<close>
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
    then have 2: \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' [])) (from_init_state T)
       \<le> SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None (from_init_state T))))
                     (state\<^sub>W_of (twl_st_of None (st_l_of_wl None U))))\<close>
      using isasat_input_bounded.cdcl_twl_stgy_prog_wl_spec_final2[of
          \<open>mset (extract_atms_clss CS' [])\<close> \<open>(from_init_state T)\<close>] CS_p \<L>\<^sub>a\<^sub>l\<^sub>l
        struct_invs stgy_invs corr_w add_invs clss 1 confl clss clss_CS'
      by (auto simp: from_init_state_def)

    have RES_SPEC: \<open>RES ({(S', S). S = state\<^sub>W_of (twl_st_of_wl None S')}\<inverse> ``
            Collect (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS))) =
     SPEC (\<lambda>S'. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ([], CS, {#}, None)
                   (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S'))))\<close>
      by auto
    have \<open>isasat_input_ops.cdcl_twl_stgy_prog_wl_D (mset (extract_atms_clss CS' []))
         (from_init_state T)
      \<le> \<Down> TWL_to_clauses_state_conv
      (SPEC (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS)))\<close>
      unfolding TWL_to_clauses_state_conv_def conc_fun_RES RES_SPEC
      by (rule weaken_SPEC[OF SPEC_add_information[OF 1 2]])
       (auto simp: from_init_state_def intro: rtranclp_fullI)
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
      apply (refine_vcg bind_refine_spec isasat_input_bounded.init_dt_init_dt_l lhs_step_If)
      subgoal for T by (rule conflict_during_init)
      subgoal for T by (rule empty_clss)
      subgoal by (rule extract_atms_clss_not_nil)
      subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel isasat_input_bounded_nempty_def
            isasat_input_bounded_nempty_axioms_def)
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
        past_invs.simps clauses_def additional_WS_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def get_unit_learned_def
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

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn unat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have ex_remove_xs: \<open>(\<exists>xs. mset xs = mset x \<and> {#literal_of_nat (nat_of_uint32 x). x \<in># mset xs#} = y) \<longleftrightarrow>
       ({#literal_of_nat (nat_of_uint32 x). x \<in># mset x#} = y)\<close>
    for x y
    by auto

  show ?thesis
    unfolding list_assn_pure_conv list_mset_assn_pure_conv list_mset_assn_pure_conv list_rel_mset_rel_internal
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

lemma IsaSAT_code: \<open>(IsaSAT_code, SAT')
    \<in> [\<lambda>x. Multiset.Ball x distinct_mset \<and> (\<forall>C\<in>#x. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>a
      clauses_l_assn\<^sup>k \<rightarrow> option_assn (list_assn unat_lit_assn)\<close>
proof -
  define empty_trail where
     \<open>empty_trail = Some ([] :: nat literal list)\<close>
  have IsaSAT: \<open>IsaSAT CS =
    do {
     ASSERT (isasat_input_bounded (mset (extract_atms_clss CS [])));
     ASSERT (distinct (extract_atms_clss CS []));
     T \<leftarrow> SAT_wl CS;
     RETURN (if get_conflict_wl T = None then Some (extract_model_of_state T) else None)
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
  have 3: \<open>ASSERT (isasat_input_bounded (mset (extract_atms_clss x []))) \<le> \<Down> unit_rel (ASSERT True)\<close>
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
  have IsaSAT_SAT: \<open>(IsaSAT, SAT')\<in>
     [\<lambda>CS. Multiset.Ball CS distinct_mset \<and>
      (\<forall>C\<in>#CS. \<forall>L\<in>#C. nat_of_lit L \<le> uint_max)]\<^sub>f
     list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<rangle> option_rel\<rangle>nres_rel\<close>
    unfolding SAT' IsaSAT
    apply (intro frefI nres_relI bind_refine if_refine)
         apply (rule 3; simp; fail)
        apply (rule 4; simp; fail)
     apply (rule 2)
    by (auto simp: TWL_to_clauses_state_conv_def convert_lits_l_def extract_model_of_state_def)
  show ?thesis
    using IsaSAT_code.refine[FCOMP IsaSAT_SAT] unfolding list_assn_list_mset_rel_clauses_l_assn .
qed

text \<open>Final correctness theorem:\<close>
lemmas IsaSAT_code_full_correctness = IsaSAT_code[FCOMP SAT_model_if_satisfiable]

end