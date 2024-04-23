theory IsaSAT_Initialisation
  imports Watched_Literals.Watched_Literals_Watch_List_Initialisation
    IsaSAT_Setup IsaSAT_VMTF WB_More_Word
    IsaSAT_Mark Tuple15
    IsaSAT_Bump_Heuristics_Init_State
    Automatic_Refinement.Relators \<comment> \<open>for more lemmas\<close>
begin
lemma in_mset_rel_eq_f_iff:
  \<open>(a, b) \<in> \<langle>{(c, a). a = f c}\<rangle>mset_rel \<longleftrightarrow> b = f `# a\<close>
  using ex_mset[of a]
  by (auto simp: mset_rel_def br_def rel2p_def[abs_def] p2rel_def rel_mset_def
      list_all2_op_eq_map_right_iff' cong: ex_cong)

lemma in_mset_rel_eq_f_iff_set:
  \<open>\<langle>{(c, a). a = f c}\<rangle>mset_rel = {(b, a). a = f `# b}\<close>
  using in_mset_rel_eq_f_iff[of _ _ f] by blast


chapter \<open>Initialisation\<close>


section \<open>Code for the initialisation of the Data Structure\<close>

text \<open>The initialisation is done in three different steps:
  \<^enum> First, we extract all the atoms that appear in the problem and initialise the state with empty values.
    This part is called \<^emph>\<open>initialisation\<close> below.
  \<^enum> Then, we go over all clauses and insert them in our memory module. We call this phase \<^emph>\<open>parsing\<close>.
  \<^enum> Finally, we calculate the watch list.

Splitting the second from the third step makes it easier to add preprocessing and more important
to add a bounded mode.
\<close>

subsection \<open>Initialisation of the state\<close>

definition (in -) atoms_hash_empty where
 [simp]: \<open>atoms_hash_empty _ = {}\<close>


definition (in -) atoms_hash_int_empty where
  \<open>atoms_hash_int_empty n = RETURN (replicate n False)\<close>

lemma atoms_hash_int_empty_atoms_hash_empty:
  \<open>(atoms_hash_int_empty, RETURN o atoms_hash_empty) \<in>
   [\<lambda>n. (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. atm_of L < n)]\<^sub>f nat_rel \<rightarrow> \<langle>atoms_hash_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (use Max_less_iff in \<open>auto simp: atoms_hash_rel_def atoms_hash_int_empty_def atoms_hash_empty_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff Ball_def
      dest: spec[of _ \<open>Pos _\<close>]\<close>)



type_synonym (in -) twl_st_wl_heur_init =
  \<open>(trail_pol, arena, conflict_option_rel, nat,
    (nat \<times> nat literal \<times> bool) list list, bump_heuristics_init, bool list,
    nat, conflict_min_cach_l, lbd, vdom, vdom, bool, clss_size, lookup_clause_rel) tuple15\<close>

type_synonym (in -) twl_st_wl_heur_init_full =
  \<open>(trail_pol, arena, conflict_option_rel, nat,
    (nat \<times> nat literal \<times> bool) list list, bump_heuristics_init, bool list,
    nat, conflict_min_cach_l, lbd, vdom, vdom, bool, clss_size, lookup_clause_rel) tuple15\<close>

abbreviation get_trail_init_wl_heur :: \<open>twl_st_wl_heur_init \<Rightarrow> trail_pol\<close> where
  \<open>get_trail_init_wl_heur \<equiv> Tuple15_a\<close>

abbreviation set_trail_init_wl_heur :: \<open>trail_pol \<Rightarrow> _ \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>set_trail_init_wl_heur \<equiv> Tuple15.set_a\<close>

abbreviation get_clauses_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> arena\<close> where
  \<open>get_clauses_wl_heur_init \<equiv> Tuple15_b\<close>

abbreviation set_clauses_wl_heur_init :: \<open>arena \<Rightarrow> _ \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>set_clauses_wl_heur_init \<equiv> Tuple15.set_b\<close>

abbreviation get_conflict_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> conflict_option_rel\<close> where
  \<open>get_conflict_wl_heur_init \<equiv> Tuple15_c\<close>

abbreviation set_conflict_wl_heur_init :: \<open>conflict_option_rel \<Rightarrow> _ \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>set_conflict_wl_heur_init \<equiv> Tuple15.set_c\<close>

abbreviation get_literals_to_update_wl_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat\<close> where
  \<open>get_literals_to_update_wl_init \<equiv> Tuple15_d\<close>

abbreviation set_literals_to_update_wl_init :: \<open>nat \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>set_literals_to_update_wl_init \<equiv> Tuple15.set_d\<close>

abbreviation get_watchlist_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> (nat \<times> nat literal \<times> bool) list list\<close> where
  \<open>get_watchlist_wl_heur_init \<equiv> Tuple15_e\<close>

abbreviation set_watchlist_wl_heur_init :: \<open>(nat \<times> nat literal \<times> bool) list list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init\<close> where
  \<open>set_watchlist_wl_heur_init \<equiv> Tuple15.set_e\<close>

abbreviation get_vmtf_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bump_heuristics_init\<close> where
  \<open>get_vmtf_wl_heur_init \<equiv> Tuple15_f\<close>

abbreviation set_vmtf_wl_heur_init :: \<open>bump_heuristics_init \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_vmtf_wl_heur_init \<equiv> Tuple15.set_f\<close>

abbreviation get_phases_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool list\<close> where
  \<open>get_phases_wl_heur_init \<equiv> Tuple15_g\<close>

abbreviation set_phases_wl_heur_init :: \<open>bool list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_phases_wl_heur_init \<equiv> Tuple15.set_g\<close>

abbreviation get_clvls_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> nat\<close> where
  \<open>get_clvls_wl_heur_init \<equiv> Tuple15_h\<close>

abbreviation set_clvls_wl_heur_init :: \<open>nat \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_clvls_wl_heur_init \<equiv> Tuple15.set_h\<close>

abbreviation get_cach_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> conflict_min_cach_l\<close> where
  \<open>get_cach_wl_heur_init \<equiv> Tuple15_i\<close>

abbreviation set_cach_wl_heur_init :: \<open>conflict_min_cach_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_cach_wl_heur_init \<equiv> Tuple15.set_i\<close>

abbreviation get_lbd_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> lbd\<close> where
  \<open>get_lbd_wl_heur_init \<equiv> Tuple15_j\<close>

abbreviation set_lbd_wl_heur_init :: \<open>lbd \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_lbd_wl_heur_init \<equiv> Tuple15.set_j\<close>

abbreviation get_vdom_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> vdom\<close> where
  \<open>get_vdom_heur_init \<equiv> Tuple15_k\<close>

abbreviation set_vdom_heur_init :: \<open>vdom \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_vdom_heur_init \<equiv> Tuple15.set_k\<close>

abbreviation get_ivdom_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> vdom\<close> where
  \<open>get_ivdom_heur_init \<equiv> Tuple15_l\<close>

abbreviation set_ivdom_heur_init :: \<open>vdom \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_ivdom_heur_init \<equiv> Tuple15.set_l\<close>

abbreviation is_failed_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>is_failed_heur_init \<equiv> Tuple15_m\<close>

abbreviation set_failed_heur_init :: \<open>bool \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_failed_heur_init \<equiv> Tuple15.set_m\<close>

abbreviation get_learned_count_init :: \<open>twl_st_wl_heur_init \<Rightarrow> clss_size\<close> where
  \<open>get_learned_count_init \<equiv> Tuple15_n\<close>

abbreviation set_learned_count_init :: \<open>clss_size \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_learned_count_init \<equiv> Tuple15.set_n\<close>

abbreviation get_mark_wl_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> lookup_clause_rel\<close> where
  \<open>get_mark_wl_heur_init \<equiv> Tuple15_o\<close>

abbreviation set_mark_wl_heur_init :: \<open>lookup_clause_rel \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> _\<close> where
  \<open>set_mark_wl_heur_init \<equiv> Tuple15.set_o\<close>


text \<open>The initialisation relation is stricter in the sense that it already includes the relation
of atom inclusion.

Remark that we replace \<^term>\<open>(D = None \<longrightarrow> j \<le> length M)\<close> by \<^term>\<open>j \<le> length M\<close>: this simplifies the
proofs and does not make a difference in the generated code, since there are no conflict analysis
at that level anyway.
\<close>
text \<open>KILL duplicates below, but difference:
  vmtf vs vmtf\_init
  watch list vs no WL
  OC vs non-OC
  \<close>
(*(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, vdom, ivdom, failed, lcount, mark)*)
definition twl_st_heur_parsing_no_WL
  :: \<open>nat multiset \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur_init \<times> nat twl_st_wl_init) set\<close>
where
[unfolded Let_def]: \<open>twl_st_heur_parsing_no_WL \<A> unbdd =
  {(S,
    ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC)).
  let M' = get_trail_init_wl_heur S; N' = get_clauses_wl_heur_init S; failed = is_failed_heur_init S;
    vdom = get_vdom_heur_init S; ivdom = get_ivdom_heur_init S; D' = get_conflict_wl_heur_init S; vm = get_vmtf_wl_heur_init S;
    mark = get_mark_wl_heur_init S; lcount = get_learned_count_init S; W' = get_watchlist_wl_heur_init S;
    \<phi> = get_phases_wl_heur_init S; cach = get_cach_wl_heur_init S; lbd = get_lbd_wl_heur_init S;
    j = get_literals_to_update_wl_init S
    in
    (unbdd \<longrightarrow> \<not>failed) \<and>
    ((unbdd \<or> \<not>failed) \<longrightarrow>
     (valid_arena N' N (set vdom) \<and>
      set_mset
       (all_lits_of_mm
          ({#mset (fst x). x \<in># ran_m N#} + NE+NEk + UE + UEk + NS + US + N0 + U0)) \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
        mset vdom = dom_m N \<and> ivdom = vdom)) \<and>
    (M', M) \<in> trail_pol \<A> \<and>
    (D',  D) \<in> option_lookup_clause_rel \<A> \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> bump_heur_init \<A> M \<and>
    phase_saving \<A> \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty \<A> cach \<and>
    (W', empty_watched \<A>) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and>
    isasat_input_bounded \<A> \<and>
    distinct vdom \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
     (mark, {#}) \<in> lookup_clause_rel \<A>
  }\<close>


definition twl_st_heur_parsing
  :: \<open>nat multiset \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur_init \<times> (nat twl_st_wl \<times> nat clauses)) set\<close>
where
[unfolded Let_def]: \<open>twl_st_heur_parsing \<A>  unbdd =
  {(S,
  ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,Q, W), OC)).
  let M' = get_trail_init_wl_heur S; N' = get_clauses_wl_heur_init S; failed = is_failed_heur_init S;
    vdom = get_vdom_heur_init S; ivdom = get_ivdom_heur_init S; D' = get_conflict_wl_heur_init S; vm = get_vmtf_wl_heur_init S;
    mark = get_mark_wl_heur_init S; lcount = get_learned_count_init S; W' = get_watchlist_wl_heur_init S;
    \<phi> = get_phases_wl_heur_init S; cach = get_cach_wl_heur_init S; lbd = get_lbd_wl_heur_init S;
    j = get_literals_to_update_wl_init S
    in
    (unbdd \<longrightarrow> \<not>failed) \<and>
    ((unbdd \<or> \<not>failed) \<longrightarrow>
    ((M', M) \<in> trail_pol \<A> \<and>
    valid_arena N' N (set vdom) \<and>
    (D',  D) \<in> option_lookup_clause_rel \<A> \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> bump_heur_init \<A> M \<and>
    phase_saving \<A> \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty \<A> cach \<and>
    mset vdom = dom_m N \<and>
    vdom_m \<A> W N = set_mset (dom_m N) \<and>
    set_mset
     (all_lits_of_mm
       ({#mset (fst x). x \<in># ran_m N#} + (NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0  \<A>) \<and>
    isasat_input_bounded \<A> \<and>
    distinct vdom \<and>
    ivdom = vdom \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    (mark, {#}) \<in> lookup_clause_rel \<A>))
  }\<close>


definition twl_st_heur_parsing_no_WL_wl :: \<open>nat multiset \<Rightarrow> bool \<Rightarrow> (_ \<times> nat twl_st_wl_init') set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl \<A>  unbdd =
  {(S,
  (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,Q)).
  let M' = get_trail_init_wl_heur S; N' = get_clauses_wl_heur_init S; failed = is_failed_heur_init S;
    vdom = get_vdom_heur_init S; ivdom = get_ivdom_heur_init S; D' = get_conflict_wl_heur_init S; vm = get_vmtf_wl_heur_init S;
    mark = get_mark_wl_heur_init S; lcount = get_learned_count_init S; W' = get_watchlist_wl_heur_init S;
    \<phi> = get_phases_wl_heur_init S; cach = get_cach_wl_heur_init S; lbd = get_lbd_wl_heur_init S;
    j = get_literals_to_update_wl_init S
    in
    (unbdd \<longrightarrow> \<not>failed) \<and>
    ((unbdd \<or> \<not>failed) \<longrightarrow>
      (valid_arena N' N (set vdom) \<and> set_mset (dom_m N) \<subseteq> set vdom)) \<and>
    (M', M) \<in> trail_pol \<A> \<and>
    (D', D) \<in> option_lookup_clause_rel \<A> \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> bump_heur_init \<A> M \<and>
    phase_saving \<A> \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty \<A> cach \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE+NEk) + (UE+UEk) + NS + US + N0 + U0))
      \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    (W', empty_watched \<A>) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and>
    isasat_input_bounded \<A> \<and>
    distinct vdom \<and> ivdom = vdom \<and>
    clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
    (mark, {#}) \<in> lookup_clause_rel \<A>
  }\<close>

definition twl_st_heur_parsing_no_WL_wl_no_watched :: \<open>nat multiset \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur_init_full \<times> nat twl_st_wl_init) set\<close> where
\<open>twl_st_heur_parsing_no_WL_wl_no_watched \<A> unbdd =
  {(S,
    ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,Q), OC)).
  let M' = get_trail_init_wl_heur S; N' = get_clauses_wl_heur_init S; failed = is_failed_heur_init S;
    vdom = get_vdom_heur_init S; ivdom = get_ivdom_heur_init S; D' = get_conflict_wl_heur_init S; vm = get_vmtf_wl_heur_init S;
    mark = get_mark_wl_heur_init S; lcount = get_learned_count_init S; W' = get_watchlist_wl_heur_init S;
    \<phi> = get_phases_wl_heur_init S; cach = get_cach_wl_heur_init S; lbd = get_lbd_wl_heur_init S;
    j = get_literals_to_update_wl_init S
    in
    (unbdd \<longrightarrow> \<not>failed) \<and>
    ((unbdd \<or> \<not>failed) \<longrightarrow>
      (valid_arena N' N (set vdom) \<and> set_mset (dom_m N) \<subseteq> set vdom) \<and> ivdom = vdom) \<and> (M', M) \<in> trail_pol \<A> \<and>
    (D', D) \<in> option_lookup_clause_rel \<A> \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> bump_heur_init \<A> M \<and>
    phase_saving \<A> \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty \<A> cach \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE+NEk) + (UE+UEk) + NS + US + N0 + U0))
       \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>) \<and>
    (W', empty_watched \<A>) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and>
    isasat_input_bounded \<A> \<and>
    distinct vdom \<and>
  clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
  (mark, {#}) \<in> lookup_clause_rel \<A>
  }\<close>

definition twl_st_heur_post_parsing_wl :: \<open>bool \<Rightarrow> (twl_st_wl_heur_init_full \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_post_parsing_wl unbdd =
  {(S,
    (M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W)).
  let M' = get_trail_init_wl_heur S; N' = get_clauses_wl_heur_init S; failed = is_failed_heur_init S;
    vdom = get_vdom_heur_init S; ivdom = get_ivdom_heur_init S; D' = get_conflict_wl_heur_init S; vm = get_vmtf_wl_heur_init S;
    mark = get_mark_wl_heur_init S; lcount = get_learned_count_init S; W' = get_watchlist_wl_heur_init S;
    \<phi> = get_phases_wl_heur_init S; cach = get_cach_wl_heur_init S; lbd = get_lbd_wl_heur_init S;
    j = get_literals_to_update_wl_init S
    in
    (unbdd \<longrightarrow> \<not>failed) \<and>
    ((unbdd \<or> \<not>failed) \<longrightarrow>
     ((M', M) \<in> trail_pol (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) \<and>
      set_mset (dom_m N) \<subseteq> set vdom \<and>
      valid_arena N' N (set vdom) \<and> ivdom=vdom)) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) \<and>
    j \<le> length M \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    vm \<in> bump_heur_init (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) M \<and>
    phase_saving (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) \<phi> \<and>
    no_dup M \<and>
    cach_refinement_empty (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) cach \<and>
    vdom_m (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) W N \<subseteq> set vdom \<and>
    set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE+NEk) + (UE+UEk) + NS + US + N0 + U0))
      \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0))) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0))) \<and>
    isasat_input_bounded (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0)) \<and>
    distinct vdom \<and>
   clss_size_corr N NE UE NEk UEk NS US N0 U0 lcount \<and>
  (mark, {#}) \<in> lookup_clause_rel (all_atms N ((NE+NEk) + (UE+UEk) + NS + US + N0 + U0))
  }\<close>

subsection \<open>Parsing\<close>

definition propagate_unit_cls
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>propagate_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((Propagated L 0 # M, N, D, add_mset {#L#} NE, UE, Q), OC))\<close>

definition propagate_unit_cls_heur
 :: \<open>bool \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>propagate_unit_cls_heur = (\<lambda>unbdd L S.
     do {
        M \<leftarrow> cons_trail_Propagated_tr L 0 (get_trail_init_wl_heur S);
       RETURN (set_trail_init_wl_heur M S)
     })\<close>

fun get_unit_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_unit_clauses_init_wl ((M, N, D, NE, UE, Q), OC) = NE + UE\<close>

fun get_subsumed_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_clauses_init_wl ((M, N, D, NE, UE, NS, US, N0, U0,Q), OC) = NS + US\<close>

fun get_subsumed_init_clauses_init_wl :: \<open>'v twl_st_wl_init \<Rightarrow> 'v clauses\<close> where
  \<open>get_subsumed_init_clauses_init_wl ((M, N, D, NE, UE, NS, US, N0, U0,Q), OC) = NS\<close>


abbreviation all_lits_st_init :: \<open>'v twl_st_wl_init \<Rightarrow> 'v literal multiset\<close> where
  \<open>all_lits_st_init S \<equiv> all_lits (get_clauses_init_wl S)
    (get_unit_clauses_init_wl S + get_subsumed_init_clauses_init_wl S)\<close>

definition all_atms_init :: \<open>_ \<Rightarrow> _ \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms_init N NUE = atm_of `# all_lits N NUE\<close>

abbreviation all_atms_st_init :: \<open>'v twl_st_wl_init \<Rightarrow> 'v multiset\<close> where
  \<open>all_atms_st_init S \<equiv> atm_of `# all_lits_st_init S\<close>

lemma DECISION_REASON0[simp]: \<open>DECISION_REASON \<noteq> 0\<close>
  by (auto simp: DECISION_REASON_def)

lemma propagate_unit_cls_heur_propagate_unit_cls:
  \<open>(uncurry (propagate_unit_cls_heur unbdd), uncurry (propagate_unit_init_wl)) \<in>
   [\<lambda>(L, S). undefined_lit (get_trail_init_wl S) L \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f
    Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow> \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  unfolding  twl_st_heur_parsing_no_WL_def propagate_unit_cls_heur_def propagate_unit_init_wl_def
    nres_monad3
  apply (intro frefI nres_relI)
  apply (clarsimp simp add: propagate_unit_init_wl.simps cons_trail_Propagated_tr_def[symmetric] comp_def
    curry_def all_atms_def[symmetric] intro!: ASSERT_leI)
  apply (refine_rcg cons_trail_Propagated_tr2[where \<A> = \<A>])
  subgoal by auto
  subgoal by auto
  subgoal by  (auto intro!: bump_heur_init_consD'
    simp: all_lits_of_mm_add_mset all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff)
  done

definition already_propagated_unit_cls
   :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, Q), OC).
     ((M, N, D, add_mset {#L#} NE, UE, Q), OC))\<close>

definition already_propagated_unit_cls_heur
   :: \<open>bool \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_heur = (\<lambda>unbdd L S.
     RETURN S)\<close>

lemma already_propagated_unit_cls_heur_already_propagated_unit_cls:
  \<open>(uncurry (already_propagated_unit_cls_heur unbdd), uncurry (RETURN oo already_propagated_unit_init_wl)) \<in>
  [\<lambda>(C, S). literals_are_in_\<L>\<^sub>i\<^sub>n \<A> C]\<^sub>f
  list_mset_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow> \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_parsing_no_WL_def already_propagated_unit_cls_heur_def
     already_propagated_unit_init_wl_def all_lits_of_mm_add_mset all_lits_of_m_add_mset
     literals_are_in_\<L>\<^sub>i\<^sub>n_def)

definition (in -) set_conflict_unit :: \<open>nat literal \<Rightarrow> nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_unit L _ = Some {#L#}\<close>

definition set_conflict_unit_heur where
  \<open>set_conflict_unit_heur = (\<lambda> L (b, n, xs). RETURN (False, 1, xs[atm_of L := Some (is_pos L)]))\<close>

lemma set_conflict_unit_heur_set_conflict_unit:
  \<open>(uncurry set_conflict_unit_heur, uncurry (RETURN oo set_conflict_unit)) \<in>
    [\<lambda>(L, D). D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f Id \<times>\<^sub>f option_lookup_clause_rel \<A> \<rightarrow>
     \<langle>option_lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_def set_conflict_unit_heur_def set_conflict_unit_def
      option_lookup_clause_rel_def lookup_clause_rel_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
      intro!: mset_as_position.intros)

definition conflict_propagated_unit_cls
 :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>conflict_propagated_unit_cls = (\<lambda>L ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,Q), OC).
     ((M, N, set_conflict_unit L D, add_mset {#L#} NE, UE, NEk, UEk, NS, US, N0, U0,{#}), OC))\<close>

definition conflict_propagated_unit_cls_heur
  :: \<open>bool \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>conflict_propagated_unit_cls_heur = (\<lambda>unbdd L S. 
     do {
       ASSERT(atm_of L < length (snd (snd (get_conflict_wl_heur_init S))));
       D \<leftarrow> set_conflict_unit_heur L (get_conflict_wl_heur_init S);
       ASSERT(isa_length_trail_pre (get_trail_init_wl_heur S));
       let j = isa_length_trail (get_trail_init_wl_heur S);
       RETURN (set_literals_to_update_wl_init j (set_conflict_wl_heur_init D S))
   })\<close>

definition conflict_propagated_unit_cls_heur_b :: \<open>_\<close> where
  \<open>conflict_propagated_unit_cls_heur_b = conflict_propagated_unit_cls_heur False\<close>

lemma conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls:
  \<open>(uncurry (conflict_propagated_unit_cls_heur unbdd), uncurry (RETURN oo set_conflict_init_wl)) \<in>
   [\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> get_conflict_init_wl S = None]\<^sub>f
      nat_lit_lit_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow> \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
proof -
  have set_conflict_init_wl_alt_def:
    \<open>RETURN oo set_conflict_init_wl = (\<lambda>L ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0,Q), OC). do {
      D \<leftarrow> RETURN (set_conflict_unit L D);
      RETURN ((M, N, Some {#L#}, add_mset {#L#} NE, UE, NEk, UEk, NS, US, N0, U0,{#}), OC)
   })\<close>
    by (auto intro!: ext simp: set_conflict_init_wl_def)
  have [refine0]: \<open>D = None \<and> L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> (y, None) \<in> option_lookup_clause_rel \<A> \<Longrightarrow> L = L' \<Longrightarrow>
    set_conflict_unit_heur L' y \<le> \<Down> {(D, D'). (D, D') \<in> option_lookup_clause_rel \<A> \<and> D' = Some {#L#}}
       (RETURN (set_conflict_unit L D))\<close>
    for L D y L'
    apply (rule order_trans)
    apply (rule set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry,
      unfolded comp_def, of  \<A> L D L' y])
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      unfolding conc_fun_RETURN
      by (auto simp: set_conflict_unit_def)
    done
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding set_conflict_init_wl_alt_def conflict_propagated_unit_cls_heur_def uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_rcg lhs_step_If)
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def option_lookup_clause_rel_def
        lookup_clause_rel_def atms_of_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def conflict_propagated_unit_cls_heur_def conflict_propagated_unit_cls_def
        image_image set_conflict_unit_def
        intro!: set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry])
    subgoal
      by auto
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def conflict_propagated_unit_cls_heur_def
          conflict_propagated_unit_cls_def
        intro!: isa_length_trail_pre)
    subgoal
      by (auto simp: twl_st_heur_parsing_no_WL_def conflict_propagated_unit_cls_heur_def
        conflict_propagated_unit_cls_def
        image_image set_conflict_unit_def all_lits_of_mm_add_mset all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff
	isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
        intro!: set_conflict_unit_heur_set_conflict_unit[THEN fref_to_Down_curry]
	  isa_length_trail_pre)
    done
qed

definition add_init_cls_heur
  :: \<open>bool \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>  where
  \<open>add_init_cls_heur unbdd = (\<lambda>C S. do {
     let C = C;
     ASSERT(length C \<le> unat32_max + 2);
     ASSERT(length C \<ge> 2);
     let N = get_clauses_wl_heur_init S;
     let failed = is_failed_heur_init S;
     if unbdd \<or> (length N \<le> snat64_max - length C - 5 \<and> \<not>failed)
     then do {
       let vdom = get_vdom_heur_init S;
       let ivdom = get_ivdom_heur_init S;
       ASSERT(length vdom \<le> length N \<and> vdom = ivdom);
       (N, i) \<leftarrow> fm_add_new True C N;
       let vdom = vdom @ [i];
       let ivdom = ivdom @ [i];
       RETURN (set_clauses_wl_heur_init N (set_vdom_heur_init vdom (set_ivdom_heur_init ivdom S)))
     } else RETURN (set_failed_heur_init True S)})\<close>

definition add_init_cls_heur_unb :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
\<open>add_init_cls_heur_unb = add_init_cls_heur True\<close>

definition add_init_cls_heur_b :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
\<open>add_init_cls_heur_b = add_init_cls_heur False\<close>

definition add_init_cls_heur_b' :: \<open>nat literal list list \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
\<open>add_init_cls_heur_b' C i = add_init_cls_heur False (C!i)\<close>

lemma length_C_nempty_iff: \<open>length C \<ge> 2 \<longleftrightarrow> C \<noteq> [] \<and> tl C \<noteq> []\<close>
  by (cases C; cases \<open>tl C\<close>) auto


context
  fixes unbdd :: bool and \<A> :: \<open>nat multiset\<close> and
    CT :: \<open>nat clause_l \<times> twl_st_wl_heur_init\<close> and
    CSOC :: \<open>nat clause_l \<times> nat twl_st_wl_init\<close> and
    SOC :: \<open>nat twl_st_wl_init\<close> and
    C C' :: \<open>nat clause_l\<close> and
    S :: \<open>nat twl_st_wl_init'\<close> and x1a and N :: \<open>nat clauses_l\<close> and
    D :: \<open>nat cconflict\<close> and x2b and NE UE NS US N0 U0 NEk UEk :: \<open>nat clauses\<close> and
    M :: \<open>(nat,nat) ann_lits\<close> and
    a b c d e1 e2 e3 f m p q r s t u v w x y ua ub z y' and
    Q and
    x2e :: \<open>nat lit_queue_wl\<close> and OC :: \<open>nat clauses\<close> and
    T :: twl_st_wl_heur_init and
    M' :: \<open>trail_pol\<close> and N' :: arena and
    D' :: conflict_option_rel and
    j' :: nat and
    W' :: \<open>_\<close> and
    vm :: \<open>bump_heuristics_option_fst_As\<close> and
    clvls :: nat and
    cach :: conflict_min_cach_l and
    lbd :: lbd and
    ivdom vdom :: vdom and
    failed :: bool and
    lcount :: clss_size and
    \<phi> :: phase_saver and
    mark :: \<open>lookup_clause_rel\<close>
  assumes
    pre: \<open>case CSOC of
     (C, S) \<Rightarrow> 2 \<le> length C \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C) \<and> distinct C\<close> and
    xy: \<open>(CT, CSOC) \<in> Id \<times>\<^sub>f twl_st_heur_parsing_no_WL \<A> unbdd\<close> and
    st:
      \<open>CSOC = (C, SOC)\<close>
      \<open>SOC = (S, OC)\<close>
      \<open>S = (M, a)\<close>
      \<open>a = (N, b)\<close>
      \<open>b = (D, c)\<close>
      \<open>c = (NE, d)\<close>
      \<open>d = (UE, e1)\<close>
      \<open>e1 = (NEk, e2)\<close>
      \<open>e2 = (UEk, e3)\<close>
      \<open>e3 = (NS, f)\<close>
      \<open>f = (US, ua)\<close>
      \<open>ua = (N0, ub)\<close>
      \<open>ub = (U0, Q)\<close>
      \<open>CT = (C', T)\<close>
begin

lemma add_init_pre1: \<open>length C' \<le> unat32_max + 2\<close>
  using pre clss_size_unat32_max[of \<A> \<open>mset C\<close>] xy st
  by (auto simp: twl_st_heur_parsing_no_WL_def)

lemma add_init_pre2: \<open>2 \<le> length C'\<close>
  using pre xy st by (auto simp: )

private lemma
    x1g_x1: \<open>C' = C\<close> and
    \<open>(get_trail_init_wl_heur T, M) \<in> trail_pol \<A>\<close> and
   valid: \<open>valid_arena (get_clauses_wl_heur_init T) N (set (get_vdom_heur_init T))\<close> and
    \<open>(get_conflict_wl_heur_init T, D) \<in> option_lookup_clause_rel \<A>\<close> and
    \<open>get_literals_to_update_wl_init T \<le> length M\<close> and
    Q: \<open>Q = {#- lit_of x. x \<in># mset (drop (get_literals_to_update_wl_init T) (rev M))#}\<close> and
    \<open>get_vmtf_wl_heur_init T \<in> bump_heur_init \<A> M\<close> and
    \<open>phase_saving \<A> (get_phases_wl_heur_init T)\<close> and
    \<open>no_dup M\<close> and
    \<open>cach_refinement_empty \<A> (get_cach_wl_heur_init T)\<close> and
    vdom: \<open>mset (get_vdom_heur_init T) = dom_m N\<close> and
    ivdom: \<open>(get_ivdom_heur_init T) = (get_vdom_heur_init T)\<close> and
    var_incl:
     \<open>set_mset (all_lits_of_mm ({#mset (fst x). x \<in># ran_m N#} + (NE+NEk) + NS + (UE+UEk) + US + N0 + U0))
       \<subseteq> set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)\<close> and
    watched: \<open>(get_watchlist_wl_heur_init T, empty_watched \<A>) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<close> and
    dcount: \<open>clss_size_corr N NE UE NEk UEk NS US N0 U0 (get_learned_count_init T)\<close>
    if \<open>\<not>(is_failed_heur_init T)  \<or> unbdd\<close>
  using that xy unfolding st twl_st_heur_parsing_no_WL_def
  by (auto simp: ac_simps)

lemma init_fm_add_new:
  \<open>\<not>is_failed_heur_init T  \<or> unbdd \<Longrightarrow> fm_add_new True C' (get_clauses_wl_heur_init T)
       \<le> \<Down>  {((arena, i), (N'', i')). valid_arena arena N'' (insert i (set (get_vdom_heur_init T))) \<and> i = i' \<and>
              i \<notin># dom_m N \<and> i = length (get_clauses_wl_heur_init T) + header_size C \<and>
	      i \<notin> set (get_vdom_heur_init T)}
          (SPEC
            (\<lambda>(N', ia).
                0 < ia \<and> ia \<notin># dom_m N \<and> N' = fmupd ia (C, True) N))\<close>
  (is \<open>_ \<Longrightarrow> _ \<le> \<Down> ?qq _\<close>)
  unfolding x1g_x1
  apply (rule order_trans)
  apply (rule fm_add_new_append_clause)
  using valid vdom pre xy valid_arena_in_vdom_le_arena[OF valid] arena_lifting(2)[OF valid]
    valid unfolding st
  by (fastforce simp: x1g_x1 vdom_m_def
    intro!: RETURN_RES_refine valid_arena_append_clause)

lemma add_init_cls_final_rel:
  fixes nN'j' :: \<open>arena_el list \<times> nat\<close> and
    nNj :: \<open>(nat, nat literal list \<times> bool) fmap \<times> nat\<close> and
    nN :: \<open>_\<close> and
    k :: \<open>nat\<close> and nN' :: \<open>arena_el list\<close> and
    k' :: \<open>nat\<close>
  assumes
    \<open>(nN'j', nNj) \<in> {((arena, i), (N'', i')). valid_arena arena N'' (insert i (set (get_vdom_heur_init T))) \<and> i = i' \<and>
              i \<notin># dom_m N \<and> i = length (get_clauses_wl_heur_init T) + header_size C \<and>
	      i \<notin> set (get_vdom_heur_init T)}\<close> and
    \<open>nNj \<in> Collect  (\<lambda>(N', ia).
                0 < ia \<and> ia \<notin># dom_m N \<and> N' = fmupd ia (C, True) N)\<close>
    \<open>nN'j' = (nN', k')\<close> and
    \<open>nNj = (nN, k)\<close>
  shows \<open>((set_clauses_wl_heur_init nN' (set_vdom_heur_init (get_vdom_heur_init T @ [k']) (set_ivdom_heur_init (get_ivdom_heur_init T @ [k']) T))),
          (M, nN, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC)
         \<in> twl_st_heur_parsing_no_WL \<A> unbdd\<close>
proof -
  show ?thesis
  using assms xy pre unfolding st
    apply (auto simp: twl_st_heur_parsing_no_WL_def ac_simps
      intro!: )
    apply (auto simp: vdom_m_simps5 ran_m_mapsto_upd_notin all_lits_of_mm_add_mset
      literals_are_in_\<L>\<^sub>i\<^sub>n_def)
    done
qed
end


lemma learned_clss_l_fmupd_if_in:
  assumes \<open>C' \<in># dom_m new\<close>
  shows
    \<open>learned_clss_l (fmupd C' D new) = (if \<not>snd D then add_mset D else id)(if \<not>irred new C' then (remove1_mset (the (fmlookup new C')) (learned_clss_l new)) else learned_clss_l new)\<close>
proof -
  define new' where \<open>new' = fmdrop C' new\<close>
  define E where \<open>E = the (fmlookup new C')\<close>
  then have new: \<open>new = fmupd C' E new'\<close>  and [simp]: \<open>C' \<notin># dom_m new'\<close>
    using assms distinct_mset_dom[of new]
    by (auto simp: fmdrop_fmupd new'_def intro!: fmlookup_inject[THEN iffD1] ext
      dest: multi_member_split)
  show ?thesis
    unfolding new
    by (auto simp: learned_clss_l_mapsto_upd_irrel learned_clss_l_fmupd_if
       dest!: multi_member_split)
qed

lemma clss_size_new_irredI:
  \<open> clss_size_corr x1c x1e x1f x1g x1h x2h x2i x2j x2k (au, av, aw, ax, be) \<Longrightarrow>
  clss_size_corr (fmupd b (x1, True) x1c) x1e x1f x1g x1h x2h x2i x2j x2k (au, av, aw, ax, be) \<longleftrightarrow>
  b \<notin>#dom_m x1c \<or> irred x1c b
  \<close>
  apply (cases \<open>b \<in>#dom_m x1c\<close>)
  apply (rule iffI)
  apply (auto simp: clss_size_corr_def clss_size_def
    clss_size_def learned_clss_l_fmupd_if_in size_remove1_mset_If
    learned_clss_l_mapsto_upd_notin_irrelev dest: learned_clss_l_mapsto_upd learned_clss_l_update
    split: if_splits)
  using learned_clss_l_mapsto_upd learned_clss_l_update by fastforce


lemma add_init_cls_heur_add_init_cls:
  \<open>(uncurry (add_init_cls_heur unbdd), uncurry (add_to_clauses_init_wl)) \<in>
   [\<lambda>(C, S). length C \<ge> 2 \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C) \<and> distinct C]\<^sub>f
   Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd  \<rightarrow> \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
proof -
  have [iff]: \<open>(\<forall>b. b = 0 \<or> b \<in># dom_m x1c \<or> b \<in># dom_m x1c \<and> \<not> irred x1c b) \<longleftrightarrow> False\<close> for x1c
    apply (intro iffI impI, auto)
    apply (drule spec[of _ \<open>Max_dom x1c + 1\<close>])
    by (auto simp: ge_Max_dom_notin_dom_m)
  have [iff]: \<open>\<exists>b>0. b \<notin># dom_m x1c \<and> (b \<in># dom_m x1c \<longrightarrow> irred x1c b)\<close> for x1c x1
    by (rule exI[of _ \<open>Max_dom x1c + 1\<close>])
      (auto simp: ge_Max_dom_notin_dom_m)

  have \<open>42 + Max_mset (add_mset 0 (x1c)) \<notin># x1c\<close> and \<open>42 + Max_mset (add_mset (0 :: nat) (x1c)) \<noteq> 0\<close> for x1c
    apply  (cases \<open>x1c\<close>) apply (auto simp: max_def)
    apply (metis Max_ge add.commute add.right_neutral add_le_cancel_left finite_set_mset le_zero_eq set_mset_add_mset_insert union_single_eq_member zero_neq_numeral)
    by (smt Max_ge Set.set_insert add.commute add.right_neutral add_mset_commute antisym diff_add_inverse diff_le_self finite_insert finite_set_mset insert_DiffM insert_commute set_mset_add_mset_insert union_single_eq_member zero_neq_numeral)
  then have [iff]: \<open>(\<forall>b. b = (0::nat) \<or> b \<in># x1c) \<longleftrightarrow> False\<close> \<open>\<exists>b>0. b \<notin># x1c\<close>for x1c
    by blast+
  have add_to_clauses_init_wl_alt_def:
   \<open>add_to_clauses_init_wl = (\<lambda>i ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC). do {
     let b = (length i = 2);
    (N', ia) \<leftarrow> SPEC (\<lambda>(N', ia). ia > 0 \<and> ia \<notin># dom_m N \<and> N' = fmupd ia (i, True) N);
    RETURN ((M, N', D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC)
  })\<close>
    by (auto simp: add_to_clauses_init_wl_def get_fresh_index_def Let_def
     RES_RES2_RETURN_RES RES_RES_RETURN_RES2 RES_RETURN_RES uncurry_def image_iff
    intro!: ext)
  show ?thesis
    unfolding add_init_cls_heur_def add_to_clauses_init_wl_alt_def uncurry_def Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg init_fm_add_new)
    subgoal
      by (rule add_init_pre1)
    subgoal
      by (rule add_init_pre2)
    apply (rule lhs_step_If)
    apply (refine_rcg)
    subgoal unfolding twl_st_heur_parsing_no_WL_def
      by (force dest!: valid_arena_vdom_le(2) simp: distinct_card)
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
    apply (rule init_fm_add_new)
    apply assumption+
    subgoal by auto
    subgoal by (rule add_init_cls_final_rel)
    subgoal for x y x1 x2 x1a x1b x2a x1c x2b x1d x2c x1e x2d x1f x2e x1g x2f x1h x2g
       x2h x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m
      unfolding RES_RES2_RETURN_RES RETURN_def
      apply simp
       unfolding RETURN_def apply (rule RES_refine)
      apply (auto simp: twl_st_heur_parsing_no_WL_def clss_size_new_irredI RETURN_def intro!: RES_refine)
      apply (meson \<open>\<And>x1c. (\<forall>b. b = 0 \<or> b \<in># x1c) = False\<close> clss_size_corr_simp(4))
      apply (metis (no_types, opaque_lifting) \<open>\<And>x1c. \<exists>b>0. b \<notin># x1c\<close> clss_size_corr_simp(4))
      apply (meson \<open>\<And>x1c. (\<forall>b. b = 0 \<or> b \<in># x1c) = False\<close> clss_size_corr_simp(4))
      apply (metis (no_types, opaque_lifting) \<open>\<And>x1c. \<exists>b>0. b \<notin># x1c\<close> clss_size_corr_simp(4))
      done
    done
qed

definition already_propagated_unit_cls_conflict
  :: \<open>nat literal \<Rightarrow> nat twl_st_wl_init \<Rightarrow> nat twl_st_wl_init\<close>
where
  \<open>already_propagated_unit_cls_conflict = (\<lambda>L ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC).
     ((M, N, D, add_mset {#L#} NE, UE, NEk, UEk, NS, US, N0, U0, {#}), OC))\<close>

definition already_propagated_unit_cls_conflict_heur
  :: \<open>bool \<Rightarrow> nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
  \<open>already_propagated_unit_cls_conflict_heur = (\<lambda>unbdd L S. do {
     ASSERT (isa_length_trail_pre (get_trail_init_wl_heur S));
     RETURN (set_literals_to_update_wl_init (isa_length_trail (get_trail_init_wl_heur S)) S)
  })\<close>

lemma already_propagated_unit_cls_conflict_heur_already_propagated_unit_cls_conflict:
  \<open>(uncurry (already_propagated_unit_cls_conflict_heur unbdd),
     uncurry (RETURN oo already_propagated_unit_cls_conflict)) \<in>
   [\<lambda>(L, S). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f Id \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow>
     \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: twl_st_heur_parsing_no_WL_def already_propagated_unit_cls_conflict_heur_def
      already_propagated_unit_cls_conflict_def all_lits_of_mm_add_mset
      all_lits_of_m_add_mset uminus_\<A>\<^sub>i\<^sub>n_iff isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
      intro: vmtf_consD
      intro!: ASSERT_leI isa_length_trail_pre)

definition (in -) set_conflict_empty :: \<open>nat clause option \<Rightarrow> nat clause option\<close> where
\<open>set_conflict_empty _ = Some {#}\<close>

definition (in -) lookup_set_conflict_empty :: \<open>conflict_option_rel \<Rightarrow> conflict_option_rel\<close> where
\<open>lookup_set_conflict_empty  = (\<lambda>(b, s) . (False, s))\<close>

lemma lookup_set_conflict_empty_set_conflict_empty:
  \<open>(RETURN o lookup_set_conflict_empty, RETURN o set_conflict_empty) \<in>
     [\<lambda>D. D = None]\<^sub>f option_lookup_clause_rel \<A> \<rightarrow> \<langle>option_lookup_clause_rel \<A>\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: set_conflict_empty_def
      lookup_set_conflict_empty_def option_lookup_clause_rel_def
      lookup_clause_rel_def)

definition set_empty_clause_as_conflict_heur
   :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>set_empty_clause_as_conflict_heur = (\<lambda>S. do {
     let M = get_trail_init_wl_heur S;
     let (_, (n, xs)) = get_conflict_wl_heur_init S;
     ASSERT(isa_length_trail_pre M);
     let j = isa_length_trail M;
     RETURN (set_conflict_wl_heur_init ((False, (n, xs))) (set_literals_to_update_wl_init j S))
  })\<close>

lemma set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict:
  \<open>(set_empty_clause_as_conflict_heur, RETURN o add_empty_conflict_init_wl) \<in>
  [\<lambda>S. get_conflict_init_wl S = None]\<^sub>f
  twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow> \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  unfolding set_empty_clause_as_conflict_heur_def add_empty_conflict_init_wl_def
      twl_st_heur_parsing_no_WL_def Let_def
  by (intro frefI nres_relI)
   (auto simp: set_empty_clause_as_conflict_heur_def add_empty_conflict_init_wl_def
      twl_st_heur_parsing_no_WL_def set_conflict_empty_def option_lookup_clause_rel_def
    lookup_clause_rel_def isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
    all_lits_of_mm_add_mset all_atms_st_def clss_size_def
       intro!: isa_length_trail_pre ASSERT_leI)


definition (in -) add_clause_to_others_heur
   :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_clause_to_others_heur = (\<lambda> _ S. RETURN S)\<close>

lemma add_clause_to_others_heur_add_clause_to_others:
  \<open>(uncurry add_clause_to_others_heur, uncurry (RETURN oo add_to_other_init)) \<in>
   \<langle>Id\<rangle>list_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: add_clause_to_others_heur_def add_to_other_init.simps
      twl_st_heur_parsing_no_WL_def)

definition (in -) add_tautology_to_clauses
  :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>add_tautology_to_clauses = (\<lambda> _ S. RETURN S)\<close>

lemma add_tautology_to_clauses_add_tautology_init_wl:
  \<open>(uncurry add_tautology_to_clauses, uncurry (RETURN oo add_to_tautology_init_wl)) \<in>
  [\<lambda>(C, _). literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C) ]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>r twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow>
    \<langle>twl_st_heur_parsing_no_WL \<A> unbdd\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: add_to_other_init.simps all_lits_of_m_remdups_mset
    add_to_tautology_init_wl.simps add_tautology_to_clauses_def
    twl_st_heur_parsing_no_WL_def all_lits_of_mm_add_mset
    literals_are_in_\<L>\<^sub>i\<^sub>n_def)


definition (in -)list_length_1 where
  [simp]: \<open>list_length_1 C \<longleftrightarrow> length C = 1\<close>

definition (in -)list_length_1_code where
  \<open>list_length_1_code C \<longleftrightarrow> (case C of [_] \<Rightarrow> True | _ \<Rightarrow> False)\<close>


definition (in -) get_conflict_wl_is_None_heur_init :: \<open>twl_st_wl_heur_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_heur_init = (\<lambda>S. fst (get_conflict_wl_heur_init S))\<close>

definition pre_simplify_clause_lookup_st
  :: \<open>nat clause_l \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> (bool \<times> _ \<times> twl_st_wl_heur_init) nres\<close>
  where
  \<open>pre_simplify_clause_lookup_st = (\<lambda>C E S. do {
  (tauto, C, mark) \<leftarrow> pre_simplify_clause_lookup C E (get_mark_wl_heur_init S); 
  RETURN (tauto, C, (set_mark_wl_heur_init mark S))
  })\<close>

definition init_dt_step_wl_heur
  :: \<open>bool \<Rightarrow> nat clause_l \<Rightarrow> twl_st_wl_heur_init \<times> nat clause_l \<Rightarrow>
   (twl_st_wl_heur_init \<times> nat clause_l) nres\<close>
where
  \<open>init_dt_step_wl_heur unbdd C\<^sub>0 = (\<lambda>(S, C). do {
     if get_conflict_wl_is_None_heur_init S
     then do {
       (tauto, C, S) \<leftarrow> pre_simplify_clause_lookup_st C\<^sub>0 C S;
        if tauto
        then do {T \<leftarrow>  add_tautology_to_clauses C\<^sub>0 S; RETURN (T, take 0 C)}
        else if is_Nil C
        then do {T \<leftarrow> set_empty_clause_as_conflict_heur S; RETURN (T, take 0 C)}
        else if list_length_1 C
        then do {
          ASSERT (C \<noteq> []);
          let L = C ! 0;
          ASSERT(polarity_pol_pre (get_trail_init_wl_heur S) L);
          let val_L = polarity_pol (get_trail_init_wl_heur S) L;
          if val_L = None
        then do {T \<leftarrow> propagate_unit_cls_heur unbdd L S; RETURN (T, take 0 C)}
          else
            if val_L = Some True
          then do {T \<leftarrow> already_propagated_unit_cls_heur unbdd C S; RETURN (T, take 0 C)}
            else do {T \<leftarrow> conflict_propagated_unit_cls_heur unbdd L S; RETURN (T, take 0 C)}
        }
        else do {
          ASSERT(length C \<ge> 2);
           T \<leftarrow> add_init_cls_heur unbdd C S;
           RETURN (T, take 0 C)
       }
     }
     else do {T \<leftarrow> add_clause_to_others_heur C\<^sub>0 S; RETURN (T, take 0 C)}
  })\<close>

lemma init_dt_step_wl_heur_alt_def:
\<open>init_dt_step_wl_heur unbdd C\<^sub>0  = (\<lambda>(S,D). do {
  if get_conflict_wl_is_None_heur_init S
  then do {
     (tauto, C, S) \<leftarrow> pre_simplify_clause_lookup_st C\<^sub>0 D S;
     if tauto
   then do {T \<leftarrow> add_tautology_to_clauses C\<^sub>0 S; RETURN (T, take 0 C)}
     else do {
       C \<leftarrow> RETURN C;
       if is_Nil C
     then do {T \<leftarrow> set_empty_clause_as_conflict_heur S; RETURN (T, take 0 C)}
       else if list_length_1 C
     then do {
       ASSERT (C \<noteq> []);
       let L = C ! 0;
       ASSERT(polarity_pol_pre (get_trail_init_wl_heur S) L);
       let val_L = polarity_pol (get_trail_init_wl_heur S) L;
       if val_L = None
     then do {T \<leftarrow> propagate_unit_cls_heur unbdd L S; RETURN (T, take 0 C)}
       else
         if val_L = Some True
       then do {T \<leftarrow> already_propagated_unit_cls_heur unbdd C S; RETURN (T, take 0 C)}
         else do {T \<leftarrow> conflict_propagated_unit_cls_heur unbdd L S; RETURN (T, take 0 C)}
       }
    else do {
      ASSERT(length C \<ge> 2);
         T \<leftarrow> add_init_cls_heur unbdd C S;
         RETURN (T, take 0 C)
      }
    } }
         else do {T \<leftarrow> add_clause_to_others_heur C\<^sub>0 S; RETURN (T, take 0 C)}
  })\<close>
  unfolding nres_monad1 init_dt_step_wl_heur_def by auto

named_theorems twl_st_heur_parsing_no_WL
lemma [twl_st_heur_parsing_no_WL]:
  assumes \<open>(S, T) \<in>  twl_st_heur_parsing_no_WL \<A> unbdd\<close>
  shows \<open>(get_trail_init_wl_heur S, get_trail_init_wl T) \<in> trail_pol \<A>\<close>
  using assms
  by (cases S; auto simp: twl_st_heur_parsing_no_WL_def; fail)+


definition get_conflict_wl_is_None_init :: \<open>nat twl_st_wl_init \<Rightarrow> bool\<close> where
  \<open>get_conflict_wl_is_None_init = (\<lambda>((M, N, D, NE, UE, Q), OC). is_None D)\<close>

lemma get_conflict_wl_is_None_init_alt_def:
  \<open>get_conflict_wl_is_None_init S \<longleftrightarrow> get_conflict_init_wl S = None\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_init_def split: option.splits)

lemma get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init:
    \<open>(RETURN o get_conflict_wl_is_None_heur_init,  RETURN o get_conflict_wl_is_None_init) \<in>
    twl_st_heur_parsing_no_WL \<A> unbdd \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  apply (rename_tac x y, case_tac x, case_tac y)
  by (auto simp: twl_st_heur_parsing_no_WL_def get_conflict_wl_is_None_heur_init_def option_lookup_clause_rel_def
      get_conflict_wl_is_None_init_def split: option.splits)


definition (in -) get_conflict_wl_is_None_init' where
  \<open>get_conflict_wl_is_None_init' = get_conflict_wl_is_None\<close>

definition pre_simplify_clause_lookup_st_rel where
  \<open>pre_simplify_clause_lookup_st_rel \<A> unbdd C T =  {((tauto, C', S'), tauto').
  tauto' = tauto \<and>
  (tauto \<longleftrightarrow> tautology (mset C)) \<and>
  (\<not>tauto \<longrightarrow> remdups_mset (mset C) = mset C') \<and>
  (S', T) \<in> twl_st_heur_parsing_no_WL \<A> unbdd}\<close>

lemma pre_simplify_clause_lookup_st_rel_alt_def:
  \<open>pre_simplify_clause_lookup_st_rel \<A> unbdd C T =  {((tauto, C', S'), tauto').
  tauto' = tauto \<and>
  (tauto \<longleftrightarrow> tautology (mset C)) \<and>
  (\<not>tauto \<longrightarrow> remdups_mset (mset C) = mset C' \<and> distinct C') \<and>
  (S', T) \<in> twl_st_heur_parsing_no_WL \<A> unbdd}\<close>
  by (auto simp: pre_simplify_clause_lookup_st_rel_def eq_commute[of _ \<open>mset _\<close>]
    simp del: distinct_mset_mset_distinct
    simp flip: distinct_mset_mset_distinct)

lemma pre_simplify_clause_lookup_st_remdups_clause:
  fixes D :: \<open>nat clause_l\<close>
  assumes \<open>(C, C') \<in> Id\<close> \<open>(S, T) \<in> twl_st_heur_parsing_no_WL \<A> unbdd\<close>
    \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)\<close> \<open>isasat_input_bounded \<A>\<close> and [simp]: \<open>D = []\<close>
  shows
    \<open>pre_simplify_clause_lookup_st C D S \<le> \<Down> (pre_simplify_clause_lookup_st_rel \<A> unbdd C T)
      (RETURN (tautology (mset C')))\<close>
proof -
  have \<open>mset (remdups C') = remdups_mset (mset C')\<close>
    by auto
  then have [iff]: \<open>(\<forall>x. mset x \<noteq> remdups_mset (mset C')) \<longleftrightarrow> False\<close>
    by blast
  show ?thesis
    using assms
    unfolding pre_simplify_clause_lookup_st_def remdups_clause_def conc_fun_RES
      RETURN_def
      apply (cases S)
    apply clarify
    apply (subst bind_rule_complete_RES)
    apply (refine_vcg bind_rule_complete_RES
      pre_simplify_clause_lookup_pre_simplify_clause[of _ \<A>, THEN order_trans])
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
    subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_def)
    subgoal
      by (rule order_trans, rule ref_two_step', rule pre_simplify_clause_spec)
       (auto simp: pre_simplify_clause_spec_def conc_fun_RES
        twl_st_heur_parsing_no_WL_def pre_simplify_clause_lookup_st_rel_def)
    done
qed

definition RETURN2 where \<open>RETURN2 = RETURN\<close>

lemma init_dt_step_wl_alt_def:
  \<open>init_dt_step_wl C S =
  (case get_conflict_init_wl S of
  None \<Rightarrow>
  let B = tautology (mset C) in
  if B
then do {T \<leftarrow> RETURN (add_to_tautology_init_wl C S); RETURN T}
  else
  do {
  C \<leftarrow> remdups_clause C;
  if length C = 0
  then do {T \<leftarrow> RETURN (add_empty_conflict_init_wl S); RETURN T}
  else if length C = 1
then
let L = hd C in
  if undefined_lit (get_trail_init_wl S) L
then do {T \<leftarrow> propagate_unit_init_wl L S; RETURN T}
  else if L \<in> lits_of_l (get_trail_init_wl S)
then do {T \<leftarrow> RETURN (already_propagated_unit_init_wl (mset C) S); RETURN T}
  else do {T \<leftarrow> RETURN (set_conflict_init_wl L S); RETURN T}
  else do {T \<leftarrow> add_to_clauses_init_wl C S; RETURN T}
  }
  | Some D \<Rightarrow>
  do {T \<leftarrow> RETURN (add_to_other_init C S); RETURN T})\<close>
  unfolding init_dt_step_wl_def Let_def nres_monad1 while.imonad2 RETURN2_def by auto


lemma init_dt_step_wl_heur_init_dt_step_wl:
  \<open>(uncurry (init_dt_step_wl_heur unbdd), uncurry init_dt_step_wl) \<in>
  [\<lambda>(C, S). literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)]\<^sub>f
      Id \<times>\<^sub>f {((S, C), T). C = [] \<and> (S,T)\<in> twl_st_heur_parsing_no_WL \<A> unbdd} \<rightarrow>
      \<langle>{((S, C), T). C = [] \<and> (S,T)\<in>twl_st_heur_parsing_no_WL \<A> unbdd}\<rangle> nres_rel\<close>
proof -
  have remdups: \<open>
    (x', tautology (mset x1))
    \<in> pre_simplify_clause_lookup_st_rel \<A> unbdd x1a T \<Longrightarrow>
    x2b = (x1c, x2c) \<Longrightarrow>
    x' = (x1b, x2b) \<Longrightarrow>
    \<not> x1b \<Longrightarrow>
    \<not> tautology (mset x1) \<Longrightarrow> (x1a, x1) \<in> Id \<Longrightarrow>
    RETURN x1c \<le> \<Down> {(a,b). a = b \<and> set b \<subseteq> set x1 \<and> x1c = b} (remdups_clause x1)\<close>
    for x1 x1a x1c x2 x2b x2c x' x1b T
    apply (auto simp: remdups_clause_def pre_simplify_clause_lookup_st_rel_def
      intro!: RETURN_RES_refine)
    by (metis set_mset_mset set_mset_remdups_mset)
  show ?thesis
    supply [[goals_limit=1]]
    unfolding init_dt_step_wl_alt_def uncurry_def
      option.case_eq_if get_conflict_wl_is_None_init_alt_def[symmetric]
    apply (subst init_dt_step_wl_heur_alt_def)
    supply RETURN_as_SPEC_refine[refine2 del]
    apply (intro frefI nres_relI)
    apply (refine_vcg
      set_empty_clause_as_conflict_heur_set_empty_clause_as_conflict[where \<A> = \<A> and unbdd = unbdd,
         THEN fref_to_Down, unfolded comp_def]
      propagate_unit_cls_heur_propagate_unit_cls[where \<A> = \<A> and unbdd = unbdd,THEN fref_to_Down_curry, unfolded comp_def]
      already_propagated_unit_cls_heur_already_propagated_unit_cls[where \<A> = \<A> and unbdd = unbdd,THEN fref_to_Down_curry,
          unfolded comp_def]
      conflict_propagated_unit_cls_heur_conflict_propagated_unit_cls[where \<A> = \<A> and unbdd = unbdd,THEN fref_to_Down_curry,
          unfolded comp_def]
           add_init_cls_heur_add_init_cls[where \<A> = \<A> and unbdd = unbdd, THEN fref_to_Down_curry,
          unfolded comp_def]
      add_clause_to_others_heur_add_clause_to_others[where \<A> = \<A> and unbdd = unbdd,THEN fref_to_Down_curry,
          unfolded comp_def]
        pre_simplify_clause_lookup_st_remdups_clause[where \<A> = \<A> and unbdd = unbdd]
      add_tautology_to_clauses_add_tautology_init_wl[where \<A> = \<A> and unbdd = unbdd,
           THEN fref_to_Down_curry, unfolded comp_def]
       remdups)
    subgoal by (auto simp: get_conflict_wl_is_None_heur_get_conflict_wl_is_None_init[THEN fref_to_Down_unRET_Id])
    subgoal by (auto simp: twl_st_heur_parsing_no_WL_def is_Nil_def split: list.splits)
    apply auto[]
    subgoal by simp
    subgoal by (clarsimp simp add: twl_st_heur_parsing_no_WL_def)
    subgoal by simp
    subgoal by (simp only: prod.case in_pair_collect_simp pre_simplify_clause_lookup_st_rel_def)
    subgoal by simp
    subgoal by (auto simp: pre_simplify_clause_lookup_st_rel_def)
    subgoal by auto 
      apply assumption
      apply assumption
      apply assumption
      apply assumption
    subgoal by auto
    subgoal by (auto split: list.splits)
    subgoal by (simp add: get_conflict_wl_is_None_init_alt_def)
    subgoal by (auto simp: pre_simplify_clause_lookup_st_rel_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x y x1 T x1a x2a x1b x2b x' x1c x1d x2d S'' D Ca
      by (rule polarity_pol_pre[of \<open>get_trail_init_wl_heur S''\<close> \<open>get_trail_init_wl T\<close> \<A> \<open>D!0\<close>])
       (auto simp: pre_simplify_clause_lookup_st_rel_def twl_st_heur_parsing_no_WL
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset dest!: split_list
        split: list.splits)
    subgoal for x y x1 T x1a x2a x1b x2b x' x1c x1d x2d S'' D Ca
      by (subst polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp,
         THEN fref_to_Down_unRET_uncurry_Id, of \<open>get_trail_init_wl T\<close> \<open>hd D\<close>])
       (auto simp: pre_simplify_clause_lookup_st_rel_def twl_st_heur_parsing_no_WL
          polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id]
          polarity_def
          literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset dest: split_list split: list.splits)
    subgoal by auto
    subgoal by (auto simp: pre_simplify_clause_lookup_st_rel_def twl_st_heur_parsing_no_WL
      polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id]
      polarity_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset dest: split_list split: list.splits)
    subgoal by (auto split: list.splits simp: pre_simplify_clause_lookup_st_rel_def)
    subgoal by auto
    subgoal for x y x1 T x1a x2a x1b x2b x' x1c x1d x2d S'' D Ca
      by (subst polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp,
         THEN fref_to_Down_unRET_uncurry_Id, of \<open>get_trail_init_wl T\<close> \<open>hd D\<close>])
      (auto simp: pre_simplify_clause_lookup_st_rel_def twl_st_heur_parsing_no_WL
         polarity_pol_polarity[of \<A>, unfolded option_rel_id_simp, THEN fref_to_Down_unRET_uncurry_Id]
         polarity_def
         literals_are_in_\<L>\<^sub>i\<^sub>n_add_mset dest: split_list split: list.splits)
     subgoal by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def)
     subgoal by (auto simp: pre_simplify_clause_lookup_st_rel_def list_mset_rel_def br_def)
     subgoal by auto
     subgoal by (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def
       in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
       split: list.splits)
     subgoal by (simp add: get_conflict_wl_is_None_init_alt_def)
     subgoal by (simp add: hd_conv_nth pre_simplify_clause_lookup_st_rel_def)
     subgoal
       by (auto split: list.splits)
     subgoal
       by (auto split: list.splits)
     subgoal by auto
     subgoal by (fastforce simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def)
     subgoal by (auto simp: pre_simplify_clause_lookup_st_rel_alt_def)
     subgoal by (simp add: pre_simplify_clause_lookup_st_rel_def)
     subgoal by (simp add: pre_simplify_clause_lookup_st_rel_def)
     subgoal by fast
     subgoal by (simp add: pre_simplify_clause_lookup_st_rel_def)
     subgoal by auto
     done
qed

definition polarity_st_init :: \<open>'v twl_st_wl_init \<Rightarrow> 'v literal \<Rightarrow> bool option\<close> where
  \<open>polarity_st_init S = polarity (get_trail_init_wl S)\<close>

lemma get_conflict_wl_is_None_init:
   \<open>get_conflict_init_wl S = None \<longleftrightarrow> get_conflict_wl_is_None_init S\<close>
  by (cases S) (auto simp: get_conflict_wl_is_None_init_def split: option.splits)

definition init_dt_wl_heur
 :: \<open>bool \<Rightarrow> nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<times> _ \<Rightarrow> (twl_st_wl_heur_init \<times> _) nres\<close>
where
  \<open>init_dt_wl_heur unbdd CS S = nfoldli CS (\<lambda>_. True)
     (\<lambda>C S. do {
        init_dt_step_wl_heur unbdd C S}) S\<close>

definition init_dt_step_wl_heur_unb :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<times> nat clause_l \<Rightarrow> (twl_st_wl_heur_init \<times> nat clause_l) nres\<close> where
  \<open>init_dt_step_wl_heur_unb = init_dt_step_wl_heur True\<close>

definition init_dt_wl_heur_unb :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
\<open>init_dt_wl_heur_unb CS S = do { (S, _) \<leftarrow> init_dt_wl_heur True CS (S, []); RETURN S}\<close>

definition propagate_unit_cls_heur_b :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>propagate_unit_cls_heur_b = propagate_unit_cls_heur False\<close>

definition already_propagated_unit_cls_conflict_heur_b :: \<open>nat literal \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>already_propagated_unit_cls_conflict_heur_b = already_propagated_unit_cls_conflict_heur False\<close>

definition init_dt_step_wl_heur_b :: \<open>nat clause_l \<Rightarrow> twl_st_wl_heur_init \<times> nat clause_l \<Rightarrow>
  (twl_st_wl_heur_init \<times> nat clause_l) nres\<close> where
\<open>init_dt_step_wl_heur_b = init_dt_step_wl_heur False\<close>

definition init_dt_wl_heur_b :: \<open>nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow>
  (twl_st_wl_heur_init) nres\<close>
where
  \<open>init_dt_wl_heur_b CS S = do { (S, _) \<leftarrow> init_dt_wl_heur False CS (S, []); RETURN S}\<close>


subsection \<open>Extractions of the atoms in the state\<close>

definition init_valid_rep :: \<open>nat list \<Rightarrow> nat set \<Rightarrow> bool\<close> where
  \<open>init_valid_rep xs l \<longleftrightarrow>
      (\<forall>L\<in>l. L < length xs) \<and>
      (\<forall>L \<in> l.  (xs ! L) mod 2 = 1) \<and>
      (\<forall>L. L < length xs \<longrightarrow> (xs ! L) mod 2 = 1 \<longrightarrow> L \<in> l)\<close>

definition isasat_atms_ext_rel :: \<open>((nat list \<times> nat \<times> nat list) \<times> nat set) set\<close> where
  \<open>isasat_atms_ext_rel = {((xs, n, atms), l).
      init_valid_rep xs l \<and>
      n = Max (insert 0 l) \<and>
      length xs < unat32_max \<and>
      (\<forall>s\<in>set xs. s \<le> unat64_max) \<and>
      finite l \<and>
      distinct atms \<and>
      set atms = l \<and>
      length xs \<noteq> 0
   }\<close>


lemma distinct_length_le_Suc_Max:
   assumes \<open>distinct (b :: nat list)\<close>
  shows \<open>length b \<le> Suc (Max (insert 0 (set b)))\<close>
proof -
  have \<open>set b \<subseteq> {0 ..< Suc (Max (insert 0 (set b)))}\<close>
    by (cases \<open>set b = {}\<close>)
     (auto simp add: le_imp_less_Suc)
  from card_mono[OF _ this] show ?thesis
     using distinct_card[OF assms(1)] by auto
qed

lemma isasat_atms_ext_rel_alt_def:
  \<open>isasat_atms_ext_rel = {((xs, n, atms), l).
      init_valid_rep xs l \<and>
      n = Max (insert 0 l) \<and>
      length xs < unat32_max \<and>
      (\<forall>s\<in>set xs. s \<le> unat64_max) \<and>
      finite l \<and>
      distinct atms \<and>
      set atms = l \<and>
      length xs \<noteq> 0 \<and>
      length atms \<le> Suc n
   }\<close>
  by (auto simp: isasat_atms_ext_rel_def distinct_length_le_Suc_Max)


definition in_map_atm_of :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>in_map_atm_of L N \<longleftrightarrow> L \<in> set N\<close>

definition (in -) init_next_size where
  \<open>init_next_size L = 2 * L\<close>

lemma init_next_size: \<open>L \<noteq> 0 \<Longrightarrow> L + 1 \<le> unat32_max \<Longrightarrow> L < init_next_size L\<close>
  by (auto simp: init_next_size_def unat32_max_def)

definition add_to_atms_ext where
  \<open>add_to_atms_ext = (\<lambda>i (xs, n, atms). do {
    ASSERT(i \<le> unat32_max div 2);
    ASSERT(length xs \<le> unat32_max);
    ASSERT(length atms \<le> Suc n);
    let n = max i n;
    (if i < length_uint32_nat xs then do {
       ASSERT(xs!i \<le> unat64_max);
       let atms = (if xs!i AND 1 = 1 then atms else atms @ [i]);
       RETURN (xs[i := 1], n, atms)
     }
     else do {
        ASSERT(i + 1 \<le> unat32_max);
        ASSERT(length_uint32_nat xs \<noteq> 0);
        ASSERT(i < init_next_size i);
        RETURN ((list_grow xs (init_next_size i) 0)[i := 1], n,
            atms @ [i])
     })
    })\<close>
(*((*sum_mod_unat64_max (xs ! i) 2) OR*)*)
lemma init_valid_rep_upd_OR:
  \<open>init_valid_rep (x1b[x1a := a OR 1]) x2 \<longleftrightarrow>
    init_valid_rep (x1b[x1a := 1]) x2 \<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume ?A
  then have
    1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := a OR 1])\<close> and
    2: \<open>\<forall>L\<in>x2. x1b[x1a := a OR 1] ! L mod 2 = 1\<close> and
    3: \<open>\<forall>L<length (x1b[x1a := a OR 1]).
        x1b[x1a := a OR 1] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := 1])\<close>
    using 1 by simp
  then have 2: \<open>\<forall>L\<in>x2. x1b[x1a := 1] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length (x1b[x1a := 1]).
        x1b[x1a := 1] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?B
    using 1 2 3
    unfolding init_valid_rep_def by fast+
next
  assume ?B
  then have
    1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a := 1])\<close> and
    2: \<open>\<forall>L\<in>x2. x1b[x1a := 1] ! L mod 2 = 1\<close> and
    3: \<open>\<forall>L<length (x1b[x1a := 1]).
        x1b[x1a := 1] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>x2. L < length (x1b[x1a :=  a OR 1])\<close>
    using 1 by simp
  then have 2: \<open>\<forall>L\<in>x2. x1b[x1a := a OR 1] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update' bitOR_1_if_mod_2_nat)
  then have 3: \<open>\<forall>L<length (x1b[x1a :=  a OR 1]).
        x1b[x1a :=  a OR 1] ! L mod 2 = 1 \<longrightarrow>
        L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?A
    using 1 2 3
    unfolding init_valid_rep_def by fast+
qed

lemma init_valid_rep_insert:
  assumes val: \<open>init_valid_rep x1b x2\<close> and le: \<open>x1a < length x1b\<close>
  shows \<open>init_valid_rep (x1b[x1a := Suc 0]) (insert x1a x2)\<close>
proof -
  have
    1: \<open>\<forall>L\<in>x2. L < length x1b\<close> and
    2: \<open>\<forall>L\<in>x2. x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length x1b \<Longrightarrow> x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    using val unfolding init_valid_rep_def by fast+
  have 1: \<open>\<forall>L\<in>insert x1a x2. L < length (x1b[x1a := 1])\<close>
    using 1 le by simp
  then have 2: \<open>\<forall>L\<in>insert x1a x2. x1b[x1a := 1] ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length (x1b[x1a := 1]).
        x1b[x1a := 1] ! L mod 2 = 1 \<longrightarrow>
        L \<in> insert x1a x2\<close>
    using 3 le by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?thesis
    using 1 2 3
    unfolding init_valid_rep_def by auto
qed

lemma init_valid_rep_extend:
  \<open>init_valid_rep (x1b @ replicate n 0) x2 \<longleftrightarrow> init_valid_rep (x1b) x2\<close>
   (is \<open>?A \<longleftrightarrow> ?B\<close> is \<open>init_valid_rep ?x1b _ \<longleftrightarrow> _\<close>)
proof
  assume ?A
  then have
    1: \<open>\<And>L. L\<in>x2 \<Longrightarrow> L < length ?x1b\<close> and
    2: \<open>\<And>L. L\<in>x2 \<Longrightarrow> ?x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length ?x1b \<Longrightarrow> ?x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 1: \<open>L\<in>x2 \<Longrightarrow> L < length x1b\<close> for L
    using 3[of L] 2[of L] 1[of L]
    by (auto simp: nth_append split: if_splits)
  then have 2: \<open>\<forall>L\<in>x2. x1b ! L mod 2 = 1\<close>
    using 2 by (auto simp: nth_list_update')
  then have 3: \<open>\<forall>L<length x1b. x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    using 3 by (auto split: if_splits simp: bitOR_1_if_mod_2_nat)
  show ?B
    using 1 2 3
    unfolding init_valid_rep_def by fast
next
  assume ?B
  then have
    1: \<open>\<And>L. L\<in>x2 \<Longrightarrow> L < length x1b\<close> and
    2: \<open>\<And>L. L\<in>x2 \<Longrightarrow> x1b ! L mod 2 = 1\<close> and
    3: \<open>\<And>L. L<length x1b \<longrightarrow> x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>
    unfolding init_valid_rep_def by fast+
  have 10: \<open>\<forall>L\<in>x2. L < length ?x1b\<close>
    using 1 by fastforce
  then have 20: \<open>L\<in>x2 \<Longrightarrow> ?x1b ! L mod 2 = 1\<close> for L
    using 1[of L] 2[of L] 3[of L] by (auto simp: nth_list_update' bitOR_1_if_mod_2_nat nth_append)
  then have 30: \<open>L<length ?x1b \<Longrightarrow> ?x1b ! L mod 2 = 1 \<longrightarrow> L \<in> x2\<close>for L
    using 1[of L] 2[of L] 3[of L]
    by (auto split: if_splits simp: bitOR_1_if_mod_2_nat nth_append)
  show ?A
    using 10 20 30
    unfolding init_valid_rep_def by fast+
qed

lemma init_valid_rep_in_set_iff:
  \<open>init_valid_rep x1b x2  \<Longrightarrow> x \<in> x2 \<longleftrightarrow> (x < length x1b \<and> (x1b!x) mod 2 = 1)\<close>
  unfolding init_valid_rep_def
  by auto

lemma add_to_atms_ext_op_set_insert:
  \<open>(uncurry add_to_atms_ext, uncurry (RETURN oo Set.insert))
   \<in> [\<lambda>(n, l). n \<le> unat32_max div 2]\<^sub>f nat_rel \<times>\<^sub>f isasat_atms_ext_rel \<rightarrow> \<langle>isasat_atms_ext_rel\<rangle>nres_rel\<close>
proof -
  have H: \<open>finite x2 \<Longrightarrow> Max (insert x1 (insert 0 x2)) = Max (insert x1 x2)\<close>
    \<open>finite x2 \<Longrightarrow> Max (insert 0 (insert x1 x2)) = Max (insert x1 x2)\<close>
    for x1 and x2 :: \<open>nat set\<close>
    by (subst insert_commute) auto
  have [simp]: \<open>(a OR Suc 0) mod 2 = Suc 0\<close> for a
    by (auto simp add: bitOR_1_if_mod_2_nat)
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding isasat_atms_ext_rel_def add_to_atms_ext_def uncurry_def
    apply (refine_vcg lhs_step_If)
    subgoal by auto
    subgoal by auto
    subgoal unfolding isasat_atms_ext_rel_def[symmetric] isasat_atms_ext_rel_alt_def by auto
    subgoal by auto
    subgoal for x y x1 x2 x1a x2a x1b x2b
      unfolding comp_def
      apply (rule RETURN_refine)
      apply (subst in_pair_collect_simp)
      apply (subst prod.case)+
      apply (intro conjI impI allI)
      subgoal by (simp add: init_valid_rep_upd_OR init_valid_rep_insert
            del: )
      subgoal by (auto simp: H Max_insert[symmetric] simp del: Max_insert)
      subgoal by auto
      subgoal
        unfolding bitOR_1_if_mod_2_nat
        by (auto simp del: simp: unat64_max_def
            elim!: in_set_upd_cases)
      subgoal
        unfolding bitAND_1_mod_2
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        unfolding bitAND_1_mod_2
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        unfolding bitAND_1_mod_2
        by (auto simp add: init_valid_rep_in_set_iff)
      subgoal
        by (auto simp add: init_valid_rep_in_set_iff)
      done
    subgoal by (auto simp: unat32_max_def)
    subgoal by (auto simp: unat32_max_def)
    subgoal by (auto simp: unat32_max_def init_next_size_def elim: neq_NilE)
    subgoal
      unfolding comp_def list_grow_def
      apply (rule RETURN_refine)
      apply (subst in_pair_collect_simp)
      apply (subst prod.case)+
      apply (intro conjI impI allI)
      subgoal
        unfolding init_next_size_def
        apply (simp del: )
        apply (subst init_valid_rep_insert)
        apply (auto elim: neq_NilE)
        apply (subst init_valid_rep_extend)
        apply (auto elim: neq_NilE)
        done
      subgoal by (auto simp: H Max_insert[symmetric] simp del: Max_insert)
      subgoal by (auto simp: init_next_size_def unat32_max_def)
      subgoal
        unfolding bitOR_1_if_mod_2_nat
        by (auto simp: unat64_max_def
            elim!: in_set_upd_cases)
      subgoal by (auto simp: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      subgoal by (auto simp add: init_valid_rep_in_set_iff)
      done
    done
qed

definition extract_atms_cls :: \<open>'a clause_l \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = fold (\<lambda>L \<A>\<^sub>i\<^sub>n. insert (atm_of L) \<A>\<^sub>i\<^sub>n) C \<A>\<^sub>i\<^sub>n\<close>

definition extract_atms_cls_i :: \<open>nat clause_l \<Rightarrow> nat set \<Rightarrow> nat set nres\<close> where
  \<open>extract_atms_cls_i C \<A>\<^sub>i\<^sub>n = nfoldli C (\<lambda>_. True)
       (\<lambda>L \<A>\<^sub>i\<^sub>n. do {
         ASSERT(atm_of L \<le> unat32_max div 2);
         RETURN(insert (atm_of L) \<A>\<^sub>i\<^sub>n)})
    \<A>\<^sub>i\<^sub>n\<close>

lemma fild_insert_insert_swap:
  \<open>fold (\<lambda>L. insert (f L)) C (insert a \<A>\<^sub>i\<^sub>n) = insert a (fold (\<lambda>L. insert (f L)) C \<A>\<^sub>i\<^sub>n)\<close>
  by (induction C arbitrary: a \<A>\<^sub>i\<^sub>n)  (auto simp: extract_atms_cls_def)

lemma extract_atms_cls_alt_def: \<open>extract_atms_cls C \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n \<union> atm_of ` set C\<close>
  by (induction C) (auto simp: extract_atms_cls_def fild_insert_insert_swap)

lemma extract_atms_cls_i_extract_atms_cls:
  \<open>(uncurry extract_atms_cls_i, uncurry (RETURN oo extract_atms_cls))
   \<in> [\<lambda>(C, \<A>\<^sub>i\<^sub>n). \<forall>L\<in>set C. nat_of_lit L \<le> unat32_max]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H1: \<open>(x1a, x1) \<in> \<langle>{(L, L'). L = L' \<and> nat_of_lit L \<le> unat32_max}\<rangle>list_rel\<close>
    if
      \<open>case y of (C, \<A>\<^sub>i\<^sub>n) \<Rightarrow>  \<forall>L\<in>set C. nat_of_lit L \<le> unat32_max\<close> and
      \<open>(x, y) \<in> \<langle>nat_lit_lit_rel\<rangle>list_rel \<times>\<^sub>f Id\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x :: \<open>nat literal list \<times>  nat set\<close> and y :: \<open>nat literal list \<times>  nat set\<close> and
      x1 :: \<open>nat literal list\<close> and x2 :: \<open>nat set\<close> and x1a :: \<open>nat literal list\<close> and x2a :: \<open>nat set\<close>
    using that by (auto simp: list_rel_def list_all2_conj list.rel_eq list_all2_conv_all_nth)

  have atm_le: \<open>nat_of_lit xa \<le> unat32_max \<Longrightarrow> atm_of xa \<le> unat32_max div 2\<close> for xa
    by (cases xa) (auto simp: unat32_max_def)

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding extract_atms_cls_i_def extract_atms_cls_def uncurry_def comp_def
      fold_eq_nfoldli
    apply (intro frefI nres_relI)
    apply (refine_rcg H1)
           apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: atm_le)
    subgoal by auto
    done
qed


definition extract_atms_clss:: \<open>'a clause_l list \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>  where
  \<open>extract_atms_clss N \<A>\<^sub>i\<^sub>n = fold extract_atms_cls N \<A>\<^sub>i\<^sub>n\<close>

definition extract_atms_clss_i :: \<open>nat clause_l list \<Rightarrow> nat set \<Rightarrow> nat set nres\<close>  where
  \<open>extract_atms_clss_i N \<A>\<^sub>i\<^sub>n = nfoldli N (\<lambda>_. True) extract_atms_cls_i \<A>\<^sub>i\<^sub>n\<close>


lemma extract_atms_clss_i_extract_atms_clss:
  \<open>(uncurry extract_atms_clss_i, uncurry (RETURN oo extract_atms_clss))
   \<in> [\<lambda>(N, \<A>\<^sub>i\<^sub>n). \<forall>C\<in>set N. \<forall>L\<in>set C. nat_of_lit L \<le> unat32_max]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have H1: \<open>(x1a, x1) \<in> \<langle>{(C, C'). C = C' \<and> (\<forall>L\<in>set C. nat_of_lit L \<le> unat32_max)}\<rangle>list_rel\<close>
    if
      \<open>case y of (N, \<A>\<^sub>i\<^sub>n) \<Rightarrow> \<forall>C\<in>set N. \<forall>L\<in>set C. nat_of_lit L \<le> unat32_max\<close> and
      \<open>(x, y) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f Id\<close> and
      \<open>y = (x1, x2)\<close> and
      \<open>x = (x1a, x2a)\<close>
    for x :: \<open>nat literal list list \<times> nat set\<close> and y :: \<open>nat literal list list \<times> nat set\<close> and
      x1 :: \<open>nat literal list list\<close> and x2 :: \<open>nat set\<close> and x1a :: \<open>nat literal list list\<close>
      and x2a :: \<open>nat set\<close>
    using that by (auto simp: list_rel_def list_all2_conj list.rel_eq list_all2_conv_all_nth)

  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
    unfolding extract_atms_clss_i_def extract_atms_clss_def comp_def fold_eq_nfoldli uncurry_def
    apply (intro frefI nres_relI)
    apply (refine_vcg H1 extract_atms_cls_i_extract_atms_cls[THEN fref_to_Down_curry,
          unfolded comp_def])
          apply assumption+
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma fold_extract_atms_cls_union_swap:
  \<open>fold extract_atms_cls N (\<A>\<^sub>i\<^sub>n \<union> a) = fold extract_atms_cls N \<A>\<^sub>i\<^sub>n \<union> a\<close>
  by (induction N arbitrary: a \<A>\<^sub>i\<^sub>n)  (auto simp: extract_atms_cls_alt_def)

lemma extract_atms_clss_alt_def:
  \<open>extract_atms_clss N \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n \<union> ((\<Union>C\<in>set N. atm_of ` set C))\<close>
  by (induction N)
    (auto simp: extract_atms_clss_def extract_atms_cls_alt_def
      fold_extract_atms_cls_union_swap)

lemma finite_extract_atms_clss[simp]: \<open>finite (extract_atms_clss CS' {})\<close> for CS'
  by (auto simp: extract_atms_clss_alt_def)

definition op_extract_list_empty where
  \<open>op_extract_list_empty = {}\<close>

(* TODO 1024 should be replace by a proper parameter given by the parser *)
definition extract_atms_clss_imp_empty_rel where
  \<open>extract_atms_clss_imp_empty_rel = (RETURN (replicate 1024 0, 0, []))\<close>

lemma extract_atms_clss_imp_empty_rel:
  \<open>(\<lambda>_. extract_atms_clss_imp_empty_rel, \<lambda>_. (RETURN op_extract_list_empty)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>isasat_atms_ext_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI)
    (simp add:  op_extract_list_empty_def unat32_max_def
      isasat_atms_ext_rel_def init_valid_rep_def extract_atms_clss_imp_empty_rel_def
       del: replicate_numeral)


lemma extract_atms_cls_Nil[simp]:
  \<open>extract_atms_cls [] \<A>\<^sub>i\<^sub>n = \<A>\<^sub>i\<^sub>n\<close>
  unfolding extract_atms_cls_def fold.simps by simp

lemma extract_atms_clss_Cons[simp]:
  \<open>extract_atms_clss (C # Cs) N = extract_atms_clss Cs (extract_atms_cls C N)\<close>
  by (simp add: extract_atms_clss_def)

definition (in -) all_lits_of_atms_m :: \<open>'a multiset \<Rightarrow> 'a clause\<close> where
 \<open>all_lits_of_atms_m N = poss N + negs N\<close>

lemma (in -) all_lits_of_atms_m_nil[simp]: \<open>all_lits_of_atms_m {#} = {#}\<close>
  unfolding all_lits_of_atms_m_def by auto

definition (in -) all_lits_of_atms_mm :: \<open>'a multiset multiset \<Rightarrow> 'a clause\<close> where
 \<open>all_lits_of_atms_mm N = poss (\<Sum>\<^sub># N) + negs (\<Sum>\<^sub># N)\<close>

lemma all_lits_of_atms_m_all_lits_of_m:
  \<open>all_lits_of_atms_m N = all_lits_of_m (poss N)\<close>
  unfolding all_lits_of_atms_m_def all_lits_of_m_def
  by (induction N) auto


subsubsection \<open>Creation of an initial state\<close>

definition init_dt_wl_heur_spec
  :: \<open>bool \<Rightarrow> nat multiset \<Rightarrow> nat clause_l list \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> bool\<close>
where
  \<open>init_dt_wl_heur_spec unbdd \<A> CS T TOC \<longleftrightarrow>
    (\<exists>T' TOC'. (TOC, TOC') \<in> twl_st_heur_parsing_no_WL \<A> unbdd  \<and> (T, T') \<in> twl_st_heur_parsing_no_WL \<A> unbdd \<and>
        init_dt_wl_spec CS T' TOC')\<close>

definition init_state_wl :: \<open>nat twl_st_wl_init'\<close> where
  \<open>init_state_wl = ([], fmempty, None, {#}, {#}, {#}, {#}, {#}, {#}, {#}, {#}, {#})\<close>

definition init_state_wl_heur :: \<open>nat multiset \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>init_state_wl_heur \<A> = do {
    M \<leftarrow> SPEC(\<lambda>M. (M, []) \<in>  trail_pol \<A>);
    D \<leftarrow> SPEC(\<lambda>D. (D, None) \<in> option_lookup_clause_rel \<A>);
    mark \<leftarrow> SPEC(\<lambda>D. (D, {#}) \<in> lookup_clause_rel \<A>);
    W \<leftarrow> SPEC (\<lambda>W. (W, empty_watched \<A>) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>));
    vm \<leftarrow> RES (bump_heur_init \<A> []);
    \<phi> \<leftarrow> SPEC (phase_saving \<A>);
    cach \<leftarrow> SPEC (cach_refinement_empty \<A>);
    let lbd = empty_lbd;
    let vdom = [];
    let ivdom = [];
    let lcount = (0,0,0,0,0);
    RETURN (Tuple15 M [] D 0 W vm \<phi> 0 cach lbd vdom ivdom False lcount mark)}\<close>

definition init_state_wl_heur_fast where
  \<open>init_state_wl_heur_fast = init_state_wl_heur\<close>

(* TODO Move *)
lemma clss_size_empty [simp]: \<open>clss_size fmempty {#} {#} {#} {#} {#} {#} {#} {#} = (0, 0 ,0, 0, 0)\<close>
  by (auto simp: clss_size_def)
lemma clss_size_corr_empty [simp]: \<open>clss_size_corr fmempty {#} {#} {#} {#} {#} {#} {#} {#} (0, 0 ,0, 0, 0)\<close>
  by (auto simp: clss_size_corr_def)

lemma init_state_wl_heur_init_state_wl:
  \<open>(\<lambda>_. (init_state_wl_heur \<A>), \<lambda>_. (RETURN init_state_wl)) \<in>
   [\<lambda>_. isasat_input_bounded \<A>]\<^sub>f  unit_rel \<rightarrow> \<langle>twl_st_heur_parsing_no_WL_wl \<A> unbdd\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: init_state_wl_heur_def init_state_wl_def
        RES_RETURN_RES bind_RES_RETURN_eq RES_RES_RETURN_RES RETURN_def
        twl_st_heur_parsing_no_WL_wl_def vdom_m_def empty_watched_def valid_arena_empty
        intro!: RES_refine)

definition (in -)to_init_state :: \<open>nat twl_st_wl_init' \<Rightarrow> nat twl_st_wl_init\<close> where
  \<open>to_init_state S = (S, {#})\<close>

definition (in -) from_init_state :: \<open>nat twl_st_wl_init_full \<Rightarrow> nat twl_st_wl\<close> where
  \<open>from_init_state = fst\<close>

(*
lemma id_to_init_state:
  \<open>(RETURN o id, RETURN o to_init_state) \<in> twl_st_heur_parsing_no_WL_wl \<rightarrow>\<^sub>f \<langle>twl_st_heur_parsing_no_WL_wl_no_watched_full\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto simp: to_init_state_def twl_st_heur_parsing_no_WL_wl_def twl_st_heur_parsing_no_WL_wl_no_watched_full_def
      twl_st_heur_parsing_no_WL_def)
*)

definition (in -) to_init_state_code where
  \<open>to_init_state_code = id\<close>


definition from_init_state_code where
  \<open>from_init_state_code = id\<close>

definition (in -) conflict_is_None_heur_wl where
  \<open>conflict_is_None_heur_wl = (\<lambda>(M, N, U, D, _). is_None D)\<close>

definition (in -) finalise_init where
  \<open>finalise_init = id\<close>


subsection \<open>Parsing\<close>

lemma init_dt_wl_heur_init_dt_wl:
  \<open>(uncurry (init_dt_wl_heur unbdd), uncurry init_dt_wl) \<in>
    [\<lambda>(CS, S). (\<forall>C \<in> set CS. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C))]\<^sub>f
     \<langle>Id\<rangle>list_rel \<times>\<^sub>f {((S, C), T). C = [] \<and>  (S,T) \<in> twl_st_heur_parsing_no_WL \<A> unbdd} \<rightarrow>
  \<langle>{((S, C), T). C = [] \<and>  (S,T) \<in> twl_st_heur_parsing_no_WL \<A> unbdd}\<rangle> nres_rel\<close>
proof -
  have H: \<open>\<And>x y x1 x2 x1a x2a.
       (\<forall>C\<in>set x1. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)) \<Longrightarrow>
       (x1a, x1) \<in> \<langle>Id\<rangle>list_rel \<Longrightarrow>
       (x1a, x1) \<in> \<langle>{(C, C'). C = C' \<and> literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)}\<rangle>list_rel\<close>
    apply (auto simp: list_rel_def list_all2_conj)
    apply (auto simp: list_all2_conv_all_nth distinct_mset_set_def)
    done

  show ?thesis
    unfolding init_dt_wl_heur_def init_dt_wl_def uncurry_def
    apply (intro frefI nres_relI)
    apply (case_tac y rule: prod.exhaust)
    apply (case_tac x rule: prod.exhaust)
    apply (simp only: prod.case prod_rel_iff)
    apply (refine_vcg init_dt_step_wl_heur_init_dt_step_wl[THEN fref_to_Down_curry] H)
         apply normalize_goal+
    subgoal by fast
    subgoal by fast
    subgoal by simp
    subgoal by auto
    subgoal by auto
    done
qed



subsubsection \<open>Full Initialisation\<close>


definition rewatch_heur_st_fast where
  \<open>rewatch_heur_st_fast = rewatch_heur_st\<close>

definition rewatch_heur_st_fast_pre where
  \<open>rewatch_heur_st_fast_pre S =
     ((\<forall>x \<in> set (get_vdom_heur_init S). x \<le> snat64_max) \<and> length (get_clauses_wl_heur_init S) \<le> snat64_max)\<close>

definition rewatch_heur_st_init
 :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
\<open>rewatch_heur_st_init = (\<lambda>S. do {
  ASSERT(length ((get_vdom_heur_init S)) \<le> length (get_clauses_wl_heur_init S));
  W \<leftarrow> rewatch_heur ((get_vdom_heur_init S)) (get_clauses_wl_heur_init S) (get_watchlist_wl_heur_init S);
  RETURN (set_watchlist_wl_heur_init W S)
  })\<close>

definition init_dt_wl_heur_full
  :: \<open>bool \<Rightarrow> _ \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
\<open>init_dt_wl_heur_full unb CS S = do {
    (S, C) \<leftarrow> init_dt_wl_heur unb CS (S, []);
    ASSERT(\<not>is_failed_heur_init S);
    rewatch_heur_st_init S
  }\<close>

definition init_dt_wl_heur_full_unb
  :: \<open>_ \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close>
where
\<open>init_dt_wl_heur_full_unb = init_dt_wl_heur_full True\<close>

lemma init_dt_wl_heur_full_init_dt_wl_full:
  assumes
    \<open>init_dt_wl_pre CS T\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)\<close>
    \<open>(S, T) \<in> twl_st_heur_parsing_no_WL \<A> True\<close>
  shows \<open>init_dt_wl_heur_full True CS S
         \<le> \<Down> (twl_st_heur_parsing \<A> True) (init_dt_wl_full CS T)\<close>
proof -
  have H: \<open>valid_arena (get_clauses_wl_heur_init x) x1b (set (get_vdom_heur_init x))\<close>
    \<open>set (get_vdom_heur_init x) \<subseteq> set (get_vdom_heur_init x)\<close> \<open>set_mset (dom_m x1b) \<subseteq> set (get_vdom_heur_init x)\<close>
    \<open>distinct (get_vdom_heur_init x)\<close> \<open>(get_watchlist_wl_heur_init x, \<lambda>_. []) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close>
    if
      xx': \<open>(xa, x') \<in> {((S, C), T). C = [] \<and>  (S,T) \<in> twl_st_heur_parsing_no_WL \<A> True}\<close> and
      st: \<open>xa = (x, a)\<close>
        \<open>x2c = (x1e, x2d)\<close>
        \<open>x2b = (x1d, x2c)\<close>
        \<open>x2a = (x1c, x2b)\<close>
        \<open>x2 = (x1b, x2a)\<close>
        \<open>x1 = (x1a, x2)\<close>
        \<open>x' = (x1, x2e)\<close>
    for x x' x1 x1a x2 x1b x2a x1c x2b x1d x2c x1e x2d x2e x1f x2f x1g x2g x1h x2h
       x1i x2i x1j x2j x1k x2k x1l x2l x1m x2m x1n x2n x1o x2o x1p x2p xa a
  proof -
    show \<open>valid_arena (get_clauses_wl_heur_init x) x1b (set (get_vdom_heur_init x))\<close>
    \<open>set (get_vdom_heur_init x) \<subseteq> set (get_vdom_heur_init x)\<close> \<open>set_mset (dom_m x1b) \<subseteq> set (get_vdom_heur_init x)\<close>
    \<open>distinct (get_vdom_heur_init x)\<close> \<open>(get_watchlist_wl_heur_init x, \<lambda>_. []) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close>
    using xx' distinct_mset_dom[of x1b] unfolding st
      by (auto simp: twl_st_heur_parsing_no_WL_def empty_watched_def
        simp flip: set_mset_mset distinct_mset_mset_distinct)
  qed

  show ?thesis
    unfolding init_dt_wl_heur_full_def init_dt_wl_full_def rewatch_heur_st_init_def
    apply (refine_rcg rewatch_heur_rewatch[of _ _ _ _ _ _ \<A>]
      init_dt_wl_heur_init_dt_wl[of True \<A>, THEN fref_to_Down_curry])
    subgoal using assms by fast
    subgoal using assms by auto
    subgoal by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def)
    subgoal by (auto dest: valid_arena_vdom_subset simp: twl_st_heur_parsing_no_WL_def)
    apply ((rule H; assumption)+)[5]
    subgoal
      by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      literals_are_in_\<L>\<^sub>i\<^sub>n_mm_def all_lits_of_mm_union)
    subgoal by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      empty_watched_def[symmetric] map_fun_rel_def vdom_m_def)
    subgoal by (auto simp: twl_st_heur_parsing_def twl_st_heur_parsing_no_WL_def
      empty_watched_def[symmetric] ac_simps)
    done
qed


lemma init_dt_wl_heur_full_init_dt_wl_spec_full:
  assumes
    \<open>init_dt_wl_pre CS T\<close> and
    \<open>\<forall>C\<in>set CS. literals_are_in_\<L>\<^sub>i\<^sub>n \<A> (mset C)\<close> and
    \<open>(S, T) \<in> twl_st_heur_parsing_no_WL \<A> True\<close>
  shows \<open>init_dt_wl_heur_full True CS S
      \<le>  \<Down> (twl_st_heur_parsing \<A> True) (SPEC (init_dt_wl_spec_full CS T))\<close>
  apply (rule order.trans)
  apply (rule init_dt_wl_heur_full_init_dt_wl_full[OF assms])
  apply (rule ref_two_step')
  apply (rule init_dt_wl_full_init_dt_wl_spec_full[OF assms(1)])
  done


subsection \<open>Conversion to normal state\<close>

  (*
definition (in -)insert_sort_inner_nth2 :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insert_sort_inner_nth2 ns = insert_sort_inner (>) (\<lambda>remove n. ns ! (remove ! n))\<close>

definition (in -)insert_sort_nth2 :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  [code del]: \<open>insert_sort_nth2 = (\<lambda>ns. insert_sort (>) (\<lambda>remove n. ns ! (remove ! n)))\<close>

sepref_definition (in -) insert_sort_inner_nth_code
   is \<open>uncurry2 insert_sort_inner_nth2\<close>
   :: \<open>[\<lambda>((xs, vars), n). (\<forall>x\<in>#mset vars. x < length xs) \<and> n < length vars]\<^sub>a
  (array_assn uint64_nat_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>
  arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_inner_nth2_def insert_sort_inner_def fast_minus_def[symmetric]
    short_circuit_conv
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
    if_splits[split]
  by sepref


declare insert_sort_inner_nth_code.refine[sepref_fr_rules]

sepref_definition (in -) insert_sort_nth_code
   is \<open>uncurry insert_sort_nth2\<close>
   :: \<open>[\<lambda>(xs, vars). (\<forall>x\<in>#mset vars. x < length xs)]\<^sub>a
      (array_assn uint64_nat_assn)\<^sup>k *\<^sub>a (arl_assn uint32_nat_assn)\<^sup>d  \<rightarrow>
       arl_assn uint32_nat_assn\<close>
  unfolding insert_sort_nth2_def insert_sort_def insert_sort_inner_nth2_def[symmetric]
  supply [[goals_limit = 1]]
  supply mset_eq_setD[dest] mset_eq_length[dest]
  by sepref

declare insert_sort_nth_code.refine[sepref_fr_rules]

declare insert_sort_nth2_def[unfolded insert_sort_def insert_sort_inner_def, code]
*)
definition extract_lits_sorted where
  \<open>extract_lits_sorted = (\<lambda>(xs, n, vars). do {
    vars \<leftarrow> \<comment>\<open>insert\_sort\_nth2 xs vars\<close>RETURN vars;
    RETURN (vars, n)
  })\<close>


definition lits_with_max_rel where
  \<open>lits_with_max_rel = {((xs, n), \<A>\<^sub>i\<^sub>n). mset xs = \<A>\<^sub>i\<^sub>n \<and> n = Max (insert 0 (set xs)) \<and>
    length xs < unat32_max}\<close>

lemma extract_lits_sorted_mset_set:
  \<open>(extract_lits_sorted, RETURN o mset_set)
   \<in> isasat_atms_ext_rel \<rightarrow>\<^sub>f \<langle>lits_with_max_rel\<rangle>nres_rel\<close>
proof -
  have K: \<open>RETURN o mset_set = (\<lambda>v. do {v' \<leftarrow> SPEC(\<lambda>v'. v' = mset_set v); RETURN v'})\<close>
    by auto
  have K': \<open>length x2a < unat32_max\<close> if \<open>distinct b\<close> \<open>init_valid_rep x1 (set b)\<close>
    \<open>length x1 < unat32_max\<close> \<open>mset x2a = mset b\<close>for x1 x2a b
  proof -
    have \<open>distinct x2a\<close>
      by (simp add: same_mset_distinct_iff that(1) that(4))
    have \<open>length x2a = length b\<close> \<open>set x2a = set b\<close>
      using \<open>mset x2a = mset b\<close> apply (metis size_mset)
       using \<open>mset x2a = mset b\<close> by (rule mset_eq_setD)
    then have \<open>set x2a \<subseteq> {0..<unat32_max - 1}\<close>
      using that by (auto simp: init_valid_rep_def)
    from card_mono[OF _ this] show ?thesis
      using \<open>distinct x2a\<close> by (auto simp: unat32_max_def distinct_card)
  qed
  have H_simple: \<open>RETURN x2a
      \<le> \<Down> (list_mset_rel \<inter> {(v, v'). length v < unat32_max})
          (SPEC (\<lambda>v'. v' = mset_set y))\<close>
    if
      \<open>(x, y) \<in> isasat_atms_ext_rel\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x = (x1, x2)\<close>
    for x :: \<open>nat list \<times> nat \<times> nat list\<close> and y :: \<open>nat set\<close> and x1 :: \<open>nat list\<close> and
      x2 :: \<open>nat \<times> nat list\<close> and x1a :: \<open>nat\<close> and x2a :: \<open>nat list\<close>
    using that mset_eq_length by (auto simp: isasat_atms_ext_rel_def list_mset_rel_def br_def
          mset_set_set RETURN_def intro: K' intro!: RES_refine dest: mset_eq_length)

  show ?thesis
    unfolding extract_lits_sorted_def reorder_list_def K
    apply (intro frefI nres_relI)
    apply (refine_vcg H_simple)
       apply assumption+
    by (auto simp: lits_with_max_rel_def isasat_atms_ext_rel_def mset_set_set list_mset_rel_def
        br_def dest!: mset_eq_setD)
qed

text \<open>TODO Move\<close>

definition reduce_interval_init :: \<open>64 word\<close> where \<open>reduce_interval_init = 300\<close>

text \<open>This value is taken from CaDiCaL.\<close>
definition inprocessing_interval_init :: \<open>64 word\<close> where \<open>inprocessing_interval_init = 100000\<close>

definition rephasing_initial_phase :: \<open>64 word\<close> where \<open>rephasing_initial_phase = 10\<close>
definition rephasing_end_of_initial_phase :: \<open>64 word\<close> where \<open>rephasing_end_of_initial_phase = 10000\<close>

definition subsuming_length_initial_phase :: \<open>64 word\<close> where \<open>subsuming_length_initial_phase = 10000\<close>

definition finalize_vmtf_init where \<open>
  finalize_vmtf_init = (\<lambda>(ns, m, fst_As, lst_As, next_search). do {
  ASSERT (fst_As \<noteq> None);
  ASSERT (lst_As \<noteq> None);
  RETURN (ns, m, the fst_As, the lst_As, next_search)})\<close>

definition finalize_bump_init :: \<open>bump_heuristics_init \<Rightarrow> bump_heuristics nres\<close> where
  \<open>finalize_bump_init = (\<lambda>x. case x of Tuple4 hstable focused foc to_remove \<Rightarrow> do {
    focused \<leftarrow> finalize_vmtf_init focused;
    RETURN (Tuple4 hstable focused foc to_remove)
  })\<close>

text \<open>The value 160 is random (but larger than the default 16 for array lists).\<close>
definition finalise_init_code :: \<open>opts \<Rightarrow> twl_st_wl_heur_init \<Rightarrow> isasat nres\<close> where
  \<open>finalise_init_code opts =
    (\<lambda>S. case S of Tuple15 M' N' D' Q' W' bmp \<phi> clvls cach
       lbd vdom ivdom _ lcount mark \<Rightarrow> do {
     let init_stats = empty_stats_clss (of_nat (length ivdom));
     let fema = ema_init (opts_fema opts);
     let sema = ema_init (opts_sema opts);
     let other_fema = ema_init (opts_fema opts);
     let other_sema = ema_init (opts_sema opts);
     let ccount = restart_info_init;
     let heur = Restart_Heuristics (fema, sema, ccount, 0,
       (\<phi>, 0, replicate (length \<phi>) False, 0, replicate (length \<phi>) False,
           rephasing_end_of_initial_phase, 0, rephasing_initial_phase), reluctant_init, False, replicate (length \<phi>) False,
          (inprocessing_interval_init, reduce_interval_init, subsuming_length_initial_phase), other_fema, other_sema);
     let vdoms = AIvdom_init vdom [] ivdom;
     let occs =  replicate (length W') [];
    bmp \<leftarrow> finalize_bump_init bmp;
    RETURN (IsaSAT M' N' D' Q' W' bmp
       clvls cach lbd (take 1 (replicate 160 (Pos 0))) init_stats
       heur vdoms lcount opts [] occs)
     })\<close>

lemma isa_vmtf_init_nemptyD:
     \<open>((ak, al, am, an, bc)) \<in> isa_vmtf_init \<A> au \<Longrightarrow> \<A> \<noteq> {#} \<Longrightarrow>  \<exists>y. an = Some y\<close>
     \<open>((ak, al, am, an, bc)) \<in> isa_vmtf_init \<A> au \<Longrightarrow> \<A> \<noteq> {#} \<Longrightarrow>  \<exists>y. am = Some y\<close>
   by (auto simp: isa_vmtf_init_def bump_heur_init_def)

lemma isa_vmtf_init_isa_vmtf: \<open>\<A> \<noteq> {#} \<Longrightarrow> ((ak, al, Some am, Some an, bc))
       \<in> isa_vmtf_init \<A> au \<Longrightarrow> ((ak, al, am, an, bc))
       \<in> vmtf \<A> au\<close>
  by (auto simp: isa_vmtf_init_def Image_iff)

lemma bump_heur_init_isa_vmtf: \<open>\<A> \<noteq> {#} \<Longrightarrow> x \<in> bump_heur_init \<A> M \<Longrightarrow> finalize_bump_init x \<le> \<Down>Id (SPEC (\<lambda>x. x \<in> bump_heur \<A> M))\<close>
  unfolding finalize_bump_init_def bump_heur_init_def bump_heur_def finalize_vmtf_init_def
    nres_monad3
  apply (cases x, hypsubst, simp)
  apply refine_vcg
  by (auto dest: isa_vmtf_init_nemptyD intro!: isa_vmtf_init_isa_vmtf)

lemma heuristic_rel_initI:
  \<open>phase_saving \<A> \<phi> \<Longrightarrow> length \<phi>' = length \<phi> \<Longrightarrow> length \<phi>'' = length \<phi> \<Longrightarrow> phase_saving \<A> g \<Longrightarrow>
  heuristic_rel \<A> (Restart_Heuristics ((fema, sema, ccount, 0, (\<phi>,a, \<phi>',b,\<phi>'',c,d), e, f, g, h)))\<close>
  by (auto simp: heuristic_rel_def phase_save_heur_rel_def phase_saving_def heuristic_rel_stats_def)

lemma init_empty_occ_list_from_WL_length: \<open>(x5, m) \<in> \<langle>Id\<rangle>map_fun_rel  (D\<^sub>0 A) \<Longrightarrow>
    (replicate (length x5) [],  empty_occs_list A)  \<in> occurrence_list_ref\<close>
  by (auto simp: occurrence_list_ref_def map_fun_rel_def empty_occs_list_def \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset
    dest!: multi_member_split)

lemma finalise_init_finalise_init_full:
  \<open>get_conflict_wl S = None \<Longrightarrow>
  all_atms_st S \<noteq> {#} \<Longrightarrow> size (learned_clss_l (get_clauses_wl S)) = 0 \<Longrightarrow>
  ((ops', T), ops, S) \<in> Id \<times>\<^sub>f twl_st_heur_post_parsing_wl True \<Longrightarrow>
  finalise_init_code ops' T \<le> \<Down> {(S', T'). (S', T') \<in> twl_st_heur \<and>
  get_clauses_wl_heur_init T = get_clauses_wl_heur S' \<and>
  aivdom_inv_strong_dec (get_aivdom S') (dom_m (get_clauses_wl T')) \<and>
     get_learned_count_init T = get_learned_count S'} (RETURN (finalise_init S))\<close>
  apply (cases S; cases T)
  apply (simp add: finalise_init_code_def aivdom_inv_strong_dec_def2 split:prod.splits)
  apply (auto simp: finalise_init_def twl_st_heur_def twl_st_heur_parsing_no_WL_def
    twl_st_heur_parsing_no_WL_wl_def distinct_mset_dom AIvdom_init_def
      finalise_init_code_def out_learned_def all_lits_st_alt_def[symmetric]
      twl_st_heur_post_parsing_wl_def all_atms_st_def aivdom_inv_dec_def
    intro!: ASSERT_leI intro!: heuristic_rel_initI
    specify_left_RES[OF bump_heur_init_isa_vmtf[where \<A>= \<open>all_atms_st S\<close> and M=\<open>get_trail_wl S\<close>, unfolded conc_fun_RES]]
    intro: )
  apply (auto simp: finalise_init_def twl_st_heur_def twl_st_heur_parsing_no_WL_def
    twl_st_heur_parsing_no_WL_wl_def distinct_mset_dom AIvdom_init_def init_empty_occ_list_from_WL_length
      finalise_init_code_def out_learned_def all_lits_st_alt_def[symmetric] phase_saving_def
      twl_st_heur_post_parsing_wl_def all_atms_st_def aivdom_inv_dec_def ac_simps
    intro!: ASSERT_leI intro!:  heuristic_rel_initI
    intro: )
  done

lemma finalise_init_finalise_init:
  \<open>(uncurry finalise_init_code, uncurry (RETURN oo (\<lambda>_. finalise_init))) \<in>
   [\<lambda>(_, S::nat twl_st_wl). get_conflict_wl S = None \<and> all_atms_st S \<noteq> {#} \<and>
      size (learned_clss_l (get_clauses_wl S)) = 0]\<^sub>f Id \<times>\<^sub>r
      twl_st_heur_post_parsing_wl True \<rightarrow> \<langle>twl_st_heur\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  subgoal for x y
    using finalise_init_finalise_init_full[of \<open>snd y\<close> \<open>fst x\<close> \<open>snd x\<close> \<open>fst y\<close>]
    by (cases x; cases y)
      (auto intro: "weaken_\<Down>'")
  done

definition (in -) init_rll :: \<open>nat \<Rightarrow> (nat, 'v clause_l \<times> bool) fmap\<close> where
  \<open>init_rll n = fmempty\<close>

definition (in -) init_aa :: \<open>nat \<Rightarrow> 'v list\<close> where
  \<open>init_aa n = []\<close>


definition (in -) init_aa' :: \<open>nat \<Rightarrow> (clause_status \<times> nat \<times> nat) list\<close> where
  \<open>init_aa' n = []\<close>


definition init_trail_D :: \<open>nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> trail_pol nres\<close> where
  \<open>init_trail_D \<A>\<^sub>i\<^sub>n n m = do {
     let M0 = [];
     let cs = [];
     let M = replicate m UNSET;
     let M' = replicate n 0;
     let M'' = replicate n 1;
     RETURN ((M0, M, M', M'', 0, cs, 0))
  }\<close>

definition init_trail_D_fast where
  \<open>init_trail_D_fast = init_trail_D\<close>


definition init_state_wl_D' :: \<open>nat list \<times> nat \<Rightarrow>  (twl_st_wl_heur_init) nres\<close> where
  \<open>init_state_wl_D' = (\<lambda>(\<A>\<^sub>i\<^sub>n, n). do {
     ASSERT(Suc (2 * (n)) \<le> unat32_max);
     let n = Suc (n);
     let m = 2 * n;
     M \<leftarrow> init_trail_D \<A>\<^sub>i\<^sub>n n m;
     let N = [];
     let D = (True, 0, replicate n NOTIN);
     let mark = (0, replicate n None);
     let WS = replicate m [];
     vm \<leftarrow> initialize_Bump_Init \<A>\<^sub>i\<^sub>n n;
     let \<phi> = replicate n False;
     let cach = (replicate n SEEN_UNKNOWN, []);
     let lbd = empty_lbd;
     let vdom = [];
     let ivdom = [];
     let lcount = (0, 0, 0, 0, 0);
     RETURN (Tuple15 M N D 0 WS vm \<phi> 0 cach lbd vdom ivdom False lcount mark)
  })\<close>

lemma init_trail_D_ref:
  \<open>(uncurry2 init_trail_D, uncurry2 (RETURN ooo (\<lambda> _ _ _. []))) \<in> [\<lambda>((N, n), m). mset N = \<A>\<^sub>i\<^sub>n \<and>
    distinct N \<and> (\<forall>L\<in>set N. L < n) \<and> m = 2 * n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f
    \<langle>Id\<rangle>list_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f nat_rel \<rightarrow>
   \<langle>trail_pol \<A>\<^sub>i\<^sub>n\<rangle> nres_rel\<close>
proof -
  have K: \<open>(\<forall>L\<in>set N. L < n) \<longleftrightarrow>
     (\<forall>L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l (mset N)). atm_of L < n)\<close> for N n
    apply (rule iffI)
    subgoal by (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by (metis (full_types) image_eqI in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n literal.sel(1)
          set_image_mset set_mset_mset)
    done
  have K': \<open>(\<forall>L\<in>set N. L < n) \<Longrightarrow>
     (\<forall>L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l (mset N)). nat_of_lit L < 2 * n)\<close>
     (is \<open>?A \<Longrightarrow> ?B\<close>) for N n
     (*TODO proof*)
  proof -
    assume ?A
    then show ?B
      apply (auto simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
      apply (case_tac L)
      apply auto
      done
  qed
  show ?thesis
    unfolding init_trail_D_def
    apply (intro frefI nres_relI)
    unfolding uncurry_def Let_def comp_def trail_pol_def
    apply clarify
    unfolding RETURN_refine_iff
    apply clarify
    apply (intro conjI)
    subgoal
      by (auto simp: ann_lits_split_reasons_def
          list_mset_rel_def Collect_eq_comp list_rel_def
          list_all2_op_eq_map_right_iff' Id_def
          br_def in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        dest: multi_member_split)
    subgoal
      by auto
    subgoal using K' by (auto simp: polarity_def)
    subgoal
      by (auto simp:
        nat_shiftr_div2 in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff
        polarity_atm_def trail_pol_def K
        phase_saving_def list_rel_mset_rel_def  atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        list_rel_def Id_def br_def list_all2_op_eq_map_right_iff'
        ann_lits_split_reasons_def
      list_mset_rel_def Collect_eq_comp)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: control_stack.empty)
    subgoal by (auto simp: zeroed_trail_def)
    subgoal by auto
    done
qed

fun to_tuple where
  \<open>to_tuple (Tuple15 a b c d e f g h i j k l m n ko) = (a, b, c, d, e, f, g, h, i, j, k, l, m, n, ko)\<close>

definition tuple15_rel where tuple15_rel_internal_def:
  \<open>tuple15_rel A B C D E F G H I J K L M N KO = {(S,T).
  (case (S, T) of
  (Tuple15 a b c d e f g h i j k l m n ko,
  Tuple15 a' b' c' d' e' f' g' h' i' j' k' l' m' n' ko') \<Rightarrow>
  (a, a') \<in> A \<and> (b,b') \<in> B \<and> (c,c') \<in> C \<and> (d,d')\<in>D \<and> (e,e')\<in>E \<and>
  (f,f')\<in>F \<and> (g,g') \<in> G \<and> (h,h')\<in>H \<and> (i,i')\<in>I \<and> (j,j') \<in> J \<and> (k,k')\<in>K \<and> 
  (l,l')\<in>L \<and> (m,m')\<in>M \<and> (n,n')\<in>N \<and> (ko,ko')\<in>KO)}\<close>

lemma tuple15_rel_def:
  \<open>\<langle>A,B,C,D,E,F,G,H,I,J,K,L,M,N,KO\<rangle>tuple15_rel \<equiv> {(a,b). case (a,b) of
  (Tuple15 a b c d e f g h i j k l m n ko,
  Tuple15 a' b' c' d' e' f' g' h' i' j' k' l' m' n' ko') \<Rightarrow>
  (a, a') \<in> A \<and> (b,b') \<in> B \<and> (c,c') \<in> C \<and> (d,d')\<in>D \<and> (e,e')\<in>E \<and>
  (f,f')\<in>F \<and> (g,g') \<in> G \<and> (h,h')\<in>H \<and> (i,i')\<in>I \<and> (j,j') \<in> J \<and> (k,k')\<in>K \<and> 
  (l,l')\<in>L \<and> (m,m')\<in>M \<and> (n,n')\<in>N \<and> (ko,ko')\<in>KO}\<close>
  by (simp add: tuple15_rel_internal_def relAPP_def)

lemma to_tuple_eq_iff[iff]: \<open>to_tuple S = to_tuple T \<longleftrightarrow> S = T\<close>
  by (cases S; cases T) auto
 
lemma init_state_wl_D0:
  \<open>(init_state_wl_D', init_state_wl_heur) \<in>
    [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f
      lits_with_max_rel O \<langle>Id\<rangle>mset_rel \<rightarrow>
      \<langle>\<langle>Id, Id, Id, nat_rel, \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel,
           Id, \<langle>bool_rel\<rangle>list_rel, Id, Id, Id, Id, Id, Id, Id, Id\<rangle>tuple15_rel\<rangle>nres_rel\<close>
  (is \<open>?C \<in> [?Pre]\<^sub>f ?arg \<rightarrow> \<langle>?im\<rangle>nres_rel\<close>)
proof -
  have init_state_wl_heur_alt_def: \<open>init_state_wl_heur \<A>\<^sub>i\<^sub>n = do {
    M \<leftarrow> SPEC (\<lambda>M. (M, []) \<in> trail_pol \<A>\<^sub>i\<^sub>n);
    N \<leftarrow> RETURN [];
    D \<leftarrow> SPEC (\<lambda>D. (D, None) \<in> option_lookup_clause_rel \<A>\<^sub>i\<^sub>n);
    mark \<leftarrow> SPEC (\<lambda>D. (D, {#}) \<in> lookup_clause_rel \<A>\<^sub>i\<^sub>n);
    W \<leftarrow> SPEC (\<lambda>W. (W, empty_watched \<A>\<^sub>i\<^sub>n ) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>\<^sub>i\<^sub>n));
    vm \<leftarrow> RES (bump_heur_init \<A>\<^sub>i\<^sub>n []);
    \<phi> \<leftarrow> SPEC (phase_saving \<A>\<^sub>i\<^sub>n);
    cach \<leftarrow> SPEC (cach_refinement_empty \<A>\<^sub>i\<^sub>n);
    let lbd = empty_lbd;
    let vdom = [];
    let ivdom = [];
    let lcount = (0, 0, 0, 0, 0);
    RETURN (Tuple15 M N D 0 W vm \<phi> 0 cach lbd vdom ivdom False lcount mark)}\<close> for \<A>\<^sub>i\<^sub>n
    unfolding init_state_wl_heur_def Let_def by auto

  have tr: \<open>distinct_mset \<A>\<^sub>i\<^sub>n \<and> (\<forall>L\<in>#\<A>\<^sub>i\<^sub>n. L < b) \<Longrightarrow>
        (\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> \<langle>Id\<rangle>list_rel_mset_rel \<Longrightarrow> isasat_input_bounded \<A>\<^sub>i\<^sub>n \<Longrightarrow>
     b' = 2 * b \<Longrightarrow>
      init_trail_D \<A>\<^sub>i\<^sub>n' b (2 * b) \<le> \<Down> (trail_pol \<A>\<^sub>i\<^sub>n) (RETURN [])\<close> for b' b \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n' x
    by (rule init_trail_D_ref[unfolded fref_def nres_rel_def, simplified, rule_format])
      (auto simp: list_rel_mset_rel_def list_mset_rel_def br_def)

  have [simp]: \<open>comp_fun_idem (max :: 'b :: {zero,linorder} \<Rightarrow> _)\<close>
    unfolding comp_fun_idem_def comp_fun_commute_def comp_fun_idem_axioms_def
    by (auto simp: max_def[abs_def] intro!: ext)
  have [simp]: \<open>fold max x a = Max (insert a (set x))\<close> for x and a :: \<open>'b :: {zero,linorder}\<close>
    by (auto simp flip: Max.eq_fold Max.set_eq_fold)
  have in_N0: \<open>L \<in> set \<A>\<^sub>i\<^sub>n \<Longrightarrow> L  < Suc ((Max (insert 0 (set \<A>\<^sub>i\<^sub>n))))\<close>
    for L \<A>\<^sub>i\<^sub>n
    using Max_ge[of \<open>insert 0 (set \<A>\<^sub>i\<^sub>n)\<close> L]
    by (auto simp del: Max_ge simp: nat_shiftr_div2)
  define P where \<open>P x = {(a, b). b = [] \<and> (a, b) \<in> trail_pol x}\<close> for x
  have P: \<open>(c, []) \<in> P x \<longleftrightarrow> (c, []) \<in> trail_pol x\<close> for c x
    unfolding P_def by auto
  have [simp]: \<open>{p. \<exists>x. p = (x, x)} = {(y, x). x = y}\<close>
     by auto
  have [simp]: \<open>\<And>a \<A>\<^sub>i\<^sub>n. (a, \<A>\<^sub>i\<^sub>n) \<in> \<langle>nat_rel\<rangle>mset_rel \<longleftrightarrow> \<A>\<^sub>i\<^sub>n = a\<close>
    by (auto simp: Id_def br_def in_mset_rel_eq_f_iff list_rel_mset_rel_def
         in_mset_rel_eq_f_iff)

  have [simp]: \<open>(a, mset a) \<in> \<langle>Id\<rangle>list_rel_mset_rel\<close> for a
    unfolding list_rel_mset_rel_def
    by (rule relcompI [of _ \<open>a\<close>])
       (auto simp: list_rel_def Id_def br_def list_all2_op_eq_map_right_iff'
        list_mset_rel_def)
  have init: \<open>init_trail_D x1 (Suc (x2))
          (2 * Suc (x2)) \<le>
     SPEC (\<lambda>c. (c, []) \<in> trail_pol \<A>\<^sub>i\<^sub>n)\<close>
    if \<open>distinct_mset \<A>\<^sub>i\<^sub>n\<close> and x: \<open>(\<A>\<^sub>i\<^sub>n', \<A>\<^sub>i\<^sub>n) \<in> ?arg\<close> and
      \<open>\<A>\<^sub>i\<^sub>n' = (x1, x2)\<close> and \<open>isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close>
    for \<A>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n' x1 x2
    unfolding x P
    by (rule tr[unfolded conc_fun_RETURN])
      (use that in \<open>auto simp: lits_with_max_rel_def dest: in_N0\<close>)

  have H:
  \<open>(replicate (2 * Suc (b)) [], empty_watched \<A>\<^sub>i\<^sub>n)
      \<in> \<langle>Id\<rangle>map_fun_rel ((\<lambda>L. (nat_of_lit L, L)) ` set_mset (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n))\<close>
   if \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> ?arg\<close> and
     \<open>x = (a, b)\<close>
    for \<A>\<^sub>i\<^sub>n x a b
    using that unfolding map_fun_rel_def
    by (auto simp: empty_watched_def \<L>\<^sub>a\<^sub>l\<^sub>l_def
        lits_with_max_rel_def
        intro!: nth_replicate dest!: in_N0
        simp del: replicate.simps)
  have [simp]: \<open>(x, y) \<in> \<langle>Id\<rangle>list_rel_mset_rel \<Longrightarrow> L \<in># y \<Longrightarrow>
     L < Suc ((Max (insert 0 (set x))))\<close>
    for x y L
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def Id_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def dest: in_N0)

  have cach: \<open>RETURN (replicate (Suc (b)) SEEN_UNKNOWN, [])
      \<le> \<Down> Id
          (SPEC (cach_refinement_empty y))\<close>
    if
      \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n\<close> and
      \<open>(x, y) \<in> ?arg\<close> and
      \<open>x = (a, b)\<close>
    for M W vm vma \<phi> x y a b
  proof -
    show ?thesis
      unfolding cach_refinement_empty_def RETURN_RES_refine_iff
        cach_refinement_alt_def Bex_def
      by (rule exI[of _ \<open>(replicate (Suc (b)) SEEN_UNKNOWN, [])\<close>]) (use that in
          \<open>auto simp: map_fun_rel_def empty_watched_def \<L>\<^sub>a\<^sub>l\<^sub>l_def
             list_mset_rel_def lits_with_max_rel_def
            simp del: replicate_Suc
            dest!: in_N0 intro: \<close>)
  qed
  have conflict: \<open>RETURN (True, 0, replicate (Suc (b)) NOTIN)
      \<le> SPEC (\<lambda>D. (D, None) \<in> option_lookup_clause_rel \<A>\<^sub>i\<^sub>n)\<close>
  if
    \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n  \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close> and
    \<open>((a, b), \<A>\<^sub>i\<^sub>n) \<in> lits_with_max_rel O \<langle>Id\<rangle>mset_rel\<close> and
    \<open>x = (a, b)\<close>
  for a b x y
  proof -
    have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow>
        L < Suc (b)\<close> for L
      using that in_N0 by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
          lits_with_max_rel_def)
    then show ?thesis
      by (auto simp: option_lookup_clause_rel_def
      lookup_clause_rel_def simp del: replicate_Suc
      intro: mset_as_position.intros)
  qed
  have mark: \<open>RETURN (0, replicate (Suc (b)) None)
    \<le> SPEC (\<lambda>D. (D, {#}) \<in> lookup_clause_rel \<A>\<^sub>i\<^sub>n)\<close>
    if
      \<open>y = \<A>\<^sub>i\<^sub>n \<and> distinct_mset \<A>\<^sub>i\<^sub>n  \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close> and
      \<open>((a, b), \<A>\<^sub>i\<^sub>n) \<in> lits_with_max_rel O \<langle>Id\<rangle>mset_rel\<close> and
      \<open>x = (a, b)\<close>
    for a b x y
  proof -
    have \<open>L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow>
      L < Suc (b)\<close> for L
      using that in_N0 by (auto simp: atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
        lits_with_max_rel_def)
    then show ?thesis
      by (auto simp: option_lookup_clause_rel_def
        lookup_clause_rel_def simp del: replicate_Suc
        intro: mset_as_position.intros)
  qed
  have [simp]:
     \<open>NO_MATCH 0 a1 \<Longrightarrow> max 0 (Max (insert a1 (set a2))) = max a1 (Max (insert 0 (set a2)))\<close>
    for a1 :: nat and a2
    by (metis (mono_tags, lifting) List.finite_set Max_insert all_not_in_conv finite_insert insertI1 insert_commute)
  have le_uint32: \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l (mset a). nat_of_lit L \<le> unat32_max \<Longrightarrow>
    Suc (2 * (Max (insert 0 (set a)))) \<le> unat32_max\<close> for a
    apply (induction a)
    apply (auto simp: unat32_max_def)
    apply (auto simp: max_def  \<L>\<^sub>a\<^sub>l\<^sub>l_add_mset)
    done
  have K[simp]: \<open>(x, \<A>\<^sub>i\<^sub>n) \<in> \<langle>Id\<rangle>list_rel_mset_rel \<Longrightarrow>
         L \<in> atms_of (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n) \<Longrightarrow> L < Suc ((Max (insert 0 (set x))))\<close>
    for x L \<A>\<^sub>i\<^sub>n
    unfolding atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n
    by (auto simp: list_rel_mset_rel_def br_def list_rel_def Id_def
        list_all2_op_eq_map_right_iff' list_mset_rel_def)

  show ?thesis
    apply (intro frefI nres_relI)
    subgoal for x y
    unfolding init_state_wl_heur_alt_def init_state_wl_D'_def
    apply (rewrite in \<open>let _ = Suc _in _\<close> Let_def)
    apply (rewrite in \<open>let _ = 2 * _in _\<close> Let_def)
    apply (cases x; simp only: prod.case)
    apply (refine_rcg init[of y x] initialize_Bump_Init[where \<A>=\<A>\<^sub>i\<^sub>n, THEN fref_to_Down_curry, of _ \<open>Suc (snd x)\<close>] cach)
    subgoal for a b by (auto simp: lits_with_max_rel_def intro: le_uint32)
    subgoal by (auto intro!: simp: in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n
     lits_with_max_rel_def atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule conflict)
    subgoal by (rule mark)
    subgoal by (rule RETURN_rule) (rule H; simp only:)
    subgoal using in_N0 by (auto simp: lits_with_max_rel_def P_def)
    subgoal by simp
    subgoal by (auto simp: lits_with_max_rel_def)
    subgoal by (auto simp: lits_with_max_rel_def)
    subgoal by (auto simp: lits_with_max_rel_def)
    subgoal unfolding phase_saving_def lits_with_max_rel_def by (auto intro!: K)
    subgoal by fast
    subgoal by (auto simp: lits_with_max_rel_def)
      apply assumption
    apply (rule refl)
    subgoal by (auto simp: P_def init_rll_def option_lookup_clause_rel_def
          lookup_clause_rel_def lits_with_max_rel_def tuple15_rel_def
          simp del: replicate.simps
          intro!: mset_as_position.intros K)
    done
  done
qed

lemma init_state_wl_D':
  \<open>(init_state_wl_D', init_state_wl_heur) \<in>
    [\<lambda>\<A>\<^sub>i\<^sub>n. distinct_mset \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f
      lits_with_max_rel O \<langle>Id\<rangle>mset_rel \<rightarrow>
      \<langle>\<langle>Id, Id, Id, nat_rel, \<langle>\<langle>Id\<rangle>list_rel\<rangle>list_rel,
           Id, \<langle>bool_rel\<rangle>list_rel, Id, Id, Id, Id, Id, Id, Id, Id\<rangle>tuple15_rel\<rangle>nres_rel\<close>
  apply -
  apply (intro frefI nres_relI)
  by (rule init_state_wl_D0[THEN fref_to_Down, THEN order_trans])  auto

lemma init_state_wl_heur_init_state_wl':
  \<open>(init_state_wl_heur, RETURN o (\<lambda>_. init_state_wl))
  \<in> [\<lambda>N. N = \<A>\<^sub>i\<^sub>n \<and> isasat_input_bounded \<A>\<^sub>i\<^sub>n]\<^sub>f Id \<rightarrow> \<langle>twl_st_heur_parsing_no_WL_wl \<A>\<^sub>i\<^sub>n True\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  unfolding comp_def
  using init_state_wl_heur_init_state_wl[THEN fref_to_Down, of \<A>\<^sub>i\<^sub>n \<open>()\<close> \<open>()\<close>]
  by auto


lemma all_blits_are_in_problem_init_blits_in: \<open>all_blits_are_in_problem_init S \<Longrightarrow> blits_in_\<L>\<^sub>i\<^sub>n S\<close>
  unfolding blits_in_\<L>\<^sub>i\<^sub>n_def
  by (cases S)
   (auto simp: all_blits_are_in_problem_init.simps ac_simps
    \<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_all_lits_of_mm all_lits_def all_lits_st_def)

lemma correct_watching_init_blits_in_\<L>\<^sub>i\<^sub>n:
  assumes \<open>correct_watching_init S\<close>
  shows \<open>blits_in_\<L>\<^sub>i\<^sub>n S\<close>
proof -
  show ?thesis
    using assms
    by (cases S)
      (auto simp: all_blits_are_in_problem_init_blits_in
      correct_watching_init.simps)
 qed

fun append_empty_watched where
  \<open>append_empty_watched ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q), OC) = ((M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, (\<lambda>_. [])), OC)\<close>

fun remove_watched :: \<open>'v twl_st_wl_init_full \<Rightarrow> 'v twl_st_wl_init\<close> where
  \<open>remove_watched ((M, N, D, NE, UE, NEk, UEk, NNS, US, N0, U0, Q, _), OC) = ((M, N, D, NE, UE, NEk, UEk, NNS, US, N0, U0, Q), OC)\<close>


definition init_dt_wl' :: \<open>'v clause_l list \<Rightarrow> 'v twl_st_wl_init \<Rightarrow> 'v twl_st_wl_init_full nres\<close> where
  \<open>init_dt_wl' CS S = do{
     S \<leftarrow> init_dt_wl CS S;
     RETURN (append_empty_watched S)
  }\<close>

lemma init_dt_wl'_spec: \<open>init_dt_wl_pre CS S \<Longrightarrow> init_dt_wl' CS S \<le> \<Down>
   ({(S :: 'v twl_st_wl_init_full, S' :: 'v twl_st_wl_init).
      remove_watched S =  S'}) (SPEC (init_dt_wl_spec CS S))\<close>
  unfolding init_dt_wl'_def
  by (refine_vcg  bind_refine_spec[OF _ init_dt_wl_init_dt_wl_spec])
   (auto intro!: RETURN_RES_refine)

lemma init_dt_wl'_init_dt:
  \<open>init_dt_wl_pre CS S \<Longrightarrow> (S, S') \<in> state_wl_l_init \<Longrightarrow>
  init_dt_wl' CS S \<le> \<Down>
   ({(S :: 'v twl_st_wl_init_full, S' :: 'v twl_st_wl_init).
      remove_watched S =  S'} O state_wl_l_init) (init_dt CS S')\<close>
  unfolding init_dt_wl'_def
  apply (refine_vcg bind_refine[of _ _ _ _ _  \<open>RETURN\<close>, OF init_dt_wl_init_dt, simplified])
  subgoal for S T
    by (cases S; cases T)
      auto
  done

definition isasat_init_fast_slow :: \<open>twl_st_wl_heur_init \<Rightarrow> twl_st_wl_heur_init nres\<close> where
  \<open>isasat_init_fast_slow =
    (\<lambda>S::twl_st_wl_heur_init. case S of Tuple15 M' N' D' j W' vm \<phi> clvls cach lbd vdom failed x y z \<Rightarrow>
      RETURN (Tuple15 (trail_pol_slow_of_fast M') N' D' j (convert_wlists_to_nat_conv W') vm \<phi>
        clvls cach lbd vdom failed x y z))\<close>

lemma isasat_init_fast_slow_alt_def:
  \<open>isasat_init_fast_slow S = RETURN S\<close>
  unfolding isasat_init_fast_slow_def trail_pol_slow_of_fast_alt_def
    convert_wlists_to_nat_conv_def
  by (cases S) auto

end
