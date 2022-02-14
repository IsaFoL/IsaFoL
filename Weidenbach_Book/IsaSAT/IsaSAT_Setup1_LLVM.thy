theory IsaSAT_Setup1_LLVM
  imports
    IsaSAT_Setup0_LLVM
begin


context
  fixes C :: \<open>64 word\<close> and C' :: nat
begin

definition not_deleted_code where
  \<open>not_deleted_code xi = do\<^sub>M {
  x \<leftarrow> arena_status_impl xi C;
  status_neq_impl x 3
  }\<close>


context
  assumes [sepref_import_param]: \<open>(C, C') \<in> snat_rel' TYPE(64)\<close>
  notes [[sepref_register_adhoc C']]
begin

sepref_register arena_status DELETED
qualified sepref_definition not_deleted_code_tmp
  is \<open>(\<lambda>N. do {status \<leftarrow> RETURN (arena_status N C'); RETURN (status \<noteq> DELETED)})\<close>
  :: \<open>[\<lambda>N. arena_is_valid_clause_vdom N C']\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  by sepref

lemmas not_deleted_code_refine =
  not_deleted_code_tmp.refine[unfolded not_deleted_code_tmp_def
    not_deleted_code_def[symmetric]]
end
end

lemma clause_not_marked_to_delete_heur_alt_def:
  \<open>RETURN oo clause_not_marked_to_delete_heur = (\<lambda> S C'. read_arena_wl_heur (\<lambda>N. do {status \<leftarrow> RETURN (arena_status N C'); RETURN (status \<noteq> DELETED)}) S)\<close>
  by (auto intro!: ext simp: clause_not_marked_to_delete_heur_def read_arena_wl_heur_def
    split: isasat_int.splits)

definition clause_not_marked_to_delete_heur_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>clause_not_marked_to_delete_heur_code S C' = read_arena_wl_heur_code (not_deleted_code C') S\<close>

global_interpretation arena_is_valid: read_arena_param_adder where
  R = \<open>snat_rel' TYPE(64)\<close> and
  f = \<open>\<lambda>C N. (not_deleted_code C) N\<close> and
  f' = \<open>(\<lambda>C' N. do {status \<leftarrow> RETURN (arena_status N C'); RETURN (status \<noteq> DELETED)})\<close> and
  x_assn = bool1_assn and
  P = \<open>(\<lambda>C S. arena_is_valid_clause_vdom S C)\<close>
  rewrites \<open>(\<lambda>S C'. read_arena_wl_heur (\<lambda>N. do {status \<leftarrow> RETURN (arena_status N C'); RETURN (status \<noteq> DELETED)}) S) = RETURN oo clause_not_marked_to_delete_heur\<close> and
  \<open>(\<lambda>S C'. read_arena_wl_heur_code (not_deleted_code C') S) = clause_not_marked_to_delete_heur_code\<close>
  apply unfold_locales
  apply (rule not_deleted_code_refine; assumption)
  unfolding clause_not_marked_to_delete_heur_alt_def clause_not_marked_to_delete_heur_code_def
  by (solves \<open>rule refl\<close>)+

sepref_register clause_not_marked_to_delete_heur
lemmas [sepref_fr_rules] = arena_is_valid.refine
lemmas [llvm_code] = clause_not_marked_to_delete_heur_code_def[unfolded read_arena_wl_heur_code_def not_deleted_code_def]

definition conflict_is_None  :: \<open>conflict_option_rel \<Rightarrow> bool nres\<close> where
  \<open>conflict_is_None =(\<lambda>N. do {let (b, _) = N;  RETURN b})\<close>
definition \<open>conflict_is_None_code :: option_lookup_clause_assn \<Rightarrow> 1 word llM \<equiv>
\<lambda>(a, _). do\<^sub>M {
  return\<^sub>M (a)
  }\<close>
lemma conflict_is_None_code_refine[sepref_fr_rules] :
  \<open>(conflict_is_None_code, conflict_is_None) \<in> conflict_option_rel_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn\<close>
  unfolding conflict_is_None_code_def conflict_is_None_def Let_def conflict_option_rel_assn_def
  apply sepref_to_hoare
  apply vcg
  done

lemma get_conflict_wl_is_None_heur_alt_def: \<open>read_conflict_wl_heur conflict_is_None = RETURN \<circ> get_conflict_wl_is_None_heur\<close>
  by (auto simp: read_conflict_wl_heur_def get_conflict_wl_is_None_heur_def conflict_is_None_def
    intro!: ext split: isasat_int.splits)

definition get_conflict_wl_is_None_heur2 where
  \<open>get_conflict_wl_is_None_heur2 = RETURN o get_conflict_wl_is_None_heur\<close>


definition get_conflict_wl_is_None_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>get_conflict_wl_is_None_fast_code = read_conflict_wl_heur_code conflict_is_None_code\<close>

global_interpretation conflict_is_None: read_conflict_param_adder0 where
  f = \<open>conflict_is_None_code\<close> and
  f' = \<open>conflict_is_None\<close> and
  x_assn = bool1_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>(\<lambda>S. read_conflict_wl_heur (conflict_is_None) S) = get_conflict_wl_is_None_heur2\<close> and
  \<open>(\<lambda>S. read_conflict_wl_heur_code (conflict_is_None_code) S) = get_conflict_wl_is_None_fast_code\<close>
  apply unfold_locales
  apply (rule conflict_is_None_code_refine; assumption)
  unfolding get_conflict_wl_is_None_heur2_def get_conflict_wl_is_None_fast_code_def
  by (solves \<open>rule get_conflict_wl_is_None_heur_alt_def refl\<close>)+
thm inline_return_node_case

lemmas [sepref_fr_rules] = conflict_is_None.refine[unfolded get_conflict_wl_is_None_heur2_def]
lemmas [llvm_code] = conflict_is_None_code_def
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  get_conflict_wl_is_None_fast_code_def[unfolded read_conflict_wl_heur_code_def]

llvm_deps get_conflict_wl_is_None_fast_code
export_llvm get_conflict_wl_is_None_fast_code


lemma count_decided_st_heur_alt_def:
  \<open>RETURN o count_decided_st_heur = read_trail_wl_heur (RETURN \<circ> count_decided_pol)\<close>
  by (auto intro!: ext simp: count_decided_st_heur_def count_decided_pol_def
    read_trail_wl_heur_def split: isasat_int.splits)

definition count_decided_st_heur_impl where
  \<open>count_decided_st_heur_impl = read_trail_wl_heur_code count_decided_pol_impl\<close>

sepref_register extract_trail_wl_heur count_decided_pol update_trail_wl_heur count_decided_st_heur

lemma lambda_comp_true: \<open>(\<lambda>S. True) \<circ> f = (\<lambda>_. True)\<close> \<open>uncurry (\<lambda>a b. True) = (\<lambda>_. True)\<close>
  by auto

lemmas [llvm_code] =
  read_trail_wl_heur_code_def

definition isa_count_decided_st_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>isa_count_decided_st_fast_code = read_trail_wl_heur_code count_decided_pol_impl\<close>

lemmas [sepref_fr_rules] =
  read_trail_wl_heur_code_refine[OF count_decided_pol_impl.refine, unfolded count_decided_st_heur_alt_def[symmetric]
  lambda_comp_true isa_count_decided_st_fast_code_def[symmetric]]


global_interpretation count_decided: read_trail_param_adder0 where
  f = \<open>count_decided_pol_impl\<close> and
  f' = \<open>RETURN o count_decided_pol\<close> and
  x_assn = uint32_nat_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_trail_wl_heur (RETURN o count_decided_pol) = RETURN o isa_count_decided_st\<close> and
  \<open>read_trail_wl_heur_code count_decided_pol_impl = isa_count_decided_st_fast_code\<close>
  apply unfold_locales
  apply (rule count_decided_pol_impl.refine)
  subgoal
    by (auto simp: read_trail_wl_heur_def isa_count_decided_st_def intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: isa_count_decided_st_fast_code_def)
  done

lemmas [sepref_fr_rules] = count_decided.refine[unfolded lambda_comp_true]
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  isa_count_decided_st_fast_code_def[unfolded read_trail_wl_heur_code_def]

definition polarity_st_heur_pol_fast ::  \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close>  where
  \<open>polarity_st_heur_pol_fast = (\<lambda>S C. read_trail_wl_heur_code (\<lambda>L. polarity_pol_fast L C) S)\<close>

global_interpretation mop_count_decided: read_trail_param_adder where
  f = \<open>\<lambda>S L. polarity_pol_fast L S\<close> and
  f' = \<open>\<lambda>S L. mop_polarity_pol L S\<close> and
  x_assn = tri_bool_assn and
  P = \<open>\<lambda>S _. True\<close> and
  R = \<open>unat_lit_rel\<close>
  rewrites \<open>(\<lambda>S C. read_trail_wl_heur_code (\<lambda>L. polarity_pol_fast L C) S) = polarity_st_heur_pol_fast\<close> and
  \<open>(\<lambda>S C'. read_trail_wl_heur (\<lambda>L. mop_polarity_pol L C') S) = mop_polarity_st_heur\<close>
  apply unfold_locales
  apply (rule remove_pure_parameter2[where f = polarity_pol_fast and f' = mop_polarity_pol])
  apply (subst lambda_comp_true)
  apply (rule polarity_pol_fast.refine)
  apply assumption
  subgoal
    by (auto simp: polarity_st_heur_pol_fast_def)
  subgoal
    by (auto simp: mop_polarity_st_heur_def read_trail_wl_heur_def
      split: isasat_int.splits intro!: ext)
  done

lemmas [sepref_fr_rules] = mop_count_decided.refine[unfolded lambda_comp_true]
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  polarity_st_heur_pol_fast_def[unfolded read_trail_wl_heur_code_def]

definition arena_lit2 where \<open>arena_lit2 N i j = arena_lit N (i+j)\<close>

sepref_def arena_lit2_impl
  is \<open>uncurry2 (RETURN ooo arena_lit2)\<close>
    :: \<open>[uncurry2 (\<lambda>N i j. arena_lit_pre N (i+j) \<and> length N \<le> sint64_max)]\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_lit_assn\<close>
  supply [dest] = arena_lit_implI
  unfolding arena_lit_def arena_lit2_def
  by sepref

lemma arena_lit2_impl_arena_lit:
  assumes \<open>(C, C') \<in> snat_rel\<close> and
    \<open>(D, D') \<in> snat_rel\<close>
  shows \<open>(\<lambda>S. arena_lit2_impl S C D, \<lambda>S. RETURN (arena_lit S (C' + D')))
    \<in> [\<lambda>S. arena_lit_pre S (C' + D') \<and> length S \<le> sint64_max]\<^sub>a (al_assn arena_el_impl_assn)\<^sup>k \<rightarrow> unat_lit_assn\<close>
proof -
  have arena_lit2: \<open>RETURN ooo arena_lit2 = (\<lambda>S C' D'. RETURN (arena_lit2 S C' D'))\<close> for f
    by (auto intro!: ext)
  show ?thesis
  apply (rule remove_pure_parameter2_twoargs[where R = \<open>snat_rel' TYPE(64)\<close> and f = \<open>\<lambda>a C D. arena_lit2_impl a C D\<close> and f' =
     \<open>\<lambda>S C' D'. RETURN (arena_lit S (C' + D'))\<close>, OF _ assms])
  unfolding arena_lit2_def[symmetric] arena_lit2[symmetric]
  by (rule arena_lit2_impl.refine)
qed

lemma access_lit_in_clauses_heur_alt_def:
  \<open>RETURN ooo access_lit_in_clauses_heur = (\<lambda>N C' D. read_arena_wl_heur (\<lambda>N. RETURN (arena_lit N (C' + D))) N)\<close>
  by (auto intro!: ext simp: read_arena_wl_heur_def access_lit_in_clauses_heur_def split: isasat_int.splits)

lemma access_lit_in_clauses_heur_pre:
  \<open>uncurry2
   (\<lambda>S C D.
    arena_lit_pre (get_clauses_wl_heur S) (C + D) \<and>
    length (get_clauses_wl_heur S) \<le> sint64_max) = uncurry2 (\<lambda>S i j. access_lit_in_clauses_heur_pre ((S, i), j) \<and>
           length (get_clauses_wl_heur S) \<le> sint64_max)\<close>
  by (auto simp: access_lit_in_clauses_heur_pre_def)

definition access_lit_in_clauses_heur_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>access_lit_in_clauses_heur_fast_code = (\<lambda>N C D. read_arena_wl_heur_code (\<lambda>N. arena_lit2_impl N C D) N)\<close>

global_interpretation access_arena: read_arena_param_adder2_twoargs' where
  R = \<open>(snat_rel' TYPE(64))\<close> and
  R' = \<open>snat_rel' TYPE(64)\<close> and
  f' = \<open>\<lambda>N i j. RETURN (arena_lit N (i+j))\<close> and
  f = \<open>arena_lit2_impl\<close> and
  x_assn = unat_lit_assn and
  P = \<open>(\<lambda>i j S. arena_lit_pre (S) (i+j) \<and> length S \<le> sint64_max)\<close>
  rewrites
     \<open>(\<lambda>N C' D. read_arena_wl_heur (\<lambda>N. RETURN (arena_lit N (C' + D))) N) = RETURN ooo access_lit_in_clauses_heur\<close> and
    \<open>(\<lambda>N C D. read_arena_wl_heur_code (\<lambda>N. arena_lit2_impl N C D) N) = access_lit_in_clauses_heur_fast_code\<close> and
  \<open>uncurry2 (\<lambda>S C D. arena_lit_pre (get_clauses_wl_heur S) (C + D) \<and> length (get_clauses_wl_heur S) \<le> sint64_max) =
    uncurry2 (\<lambda>S i j. access_lit_in_clauses_heur_pre ((S, i), j) \<and> length (get_clauses_wl_heur S) \<le> sint64_max)\<close>
  apply unfold_locales
  apply (rule arena_lit2_impl_arena_lit; assumption)
  apply (subst access_lit_in_clauses_heur_alt_def; rule refl)
  apply (subst access_lit_in_clauses_heur_fast_code_def; rule refl)
  apply (rule access_lit_in_clauses_heur_pre)
  done

lemmas [sepref_fr_rules] = access_arena.refine

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  access_lit_in_clauses_heur_fast_code_def[unfolded read_arena_wl_heur_code_def]



sepref_register mop_arena_lit2 mop_arena_length mop_append_ll
sepref_def rewatch_heur_vdom_fast_code
  is \<open>uncurry2 (rewatch_heur_vdom)\<close>
  :: \<open>[\<lambda>((vdom, arena), W). (\<forall>x \<in> set (get_tvdom_aivdom vdom). x \<le> sint64_max) \<and> length arena \<le> sint64_max \<and>
        length (get_tvdom_aivdom vdom) \<le> sint64_max]\<^sub>a
        aivdom_assn\<^sup>k *\<^sub>a arena_fast_assn\<^sup>k *\<^sub>a watchlist_fast_assn\<^sup>d \<rightarrow> watchlist_fast_assn\<close>
  supply [[goals_limit=1]]
     arena_lit_pre_le_sint64_max[dest] arena_is_valid_clause_idx_le_uint64_max[dest]
  supply [simp] = append_ll_def length_tvdom_aivdom_def
  supply [dest] = arena_lit_implI(1)
  unfolding rewatch_heur_alt_def Let_def PR_CONST_def rewatch_heur_vdom_def
    tvdom_aivdom_at_def[symmetric] length_tvdom_aivdom_def[symmetric]
  unfolding while_eq_nfoldli[symmetric]
  apply (subst while_upt_while_direct, simp)
  unfolding if_not_swap
    FOREACH_cond_def FOREACH_body_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

lemma rewatch_heur_st_fast_alt_def:
  \<open>rewatch_heur_st_fast = (\<lambda>S\<^sub>0. do {
  let (N, S) = extract_arena_wl_heur S\<^sub>0;
  let (W, S) = extract_watchlist_wl_heur S;
  let (vdom, S) = extract_vdom_wl_heur S;
  ASSERT(length (get_tvdom_aivdom vdom) \<le> length N);
  ASSERT (vdom = get_aivdom S\<^sub>0);
  ASSERT (N = get_clauses_wl_heur S\<^sub>0);
  ASSERT (W = get_watched_wl_heur S\<^sub>0);
  W \<leftarrow> rewatch_heur (get_tvdom_aivdom vdom) N W;
  let S = update_arena_wl_heur N S;
  let S = update_watchlist_wl_heur W S;
  let S = update_vdom_wl_heur vdom S;
  RETURN S
  })\<close>
  by (auto simp: rewatch_heur_st_fast_def rewatch_heur_st_def
    extract_arena_wl_heur_def extract_watchlist_wl_heur_def extract_vdom_wl_heur_def
    isasat_state_ops.remove_arena_wl_heur_def  isasat_state_ops.remove_watchlist_wl_heur_def  isasat_state_ops.remove_vdom_wl_heur_def
    update_arena_wl_heur_def update_watchlist_wl_heur_def update_vdom_wl_heur_def
    split: isasat_int.splits
    intro!: ext)

lemmas [sepref_fr_rules] =
  remove_watchlist_wl_heur_code.refine
  remove_vdom_wl_heur_code.refine
  remove_arena_wl_heur_code.refine

sepref_def rewatch_heur_st_fast_code
  is \<open>(rewatch_heur_st_fast)\<close>
  :: \<open>[rewatch_heur_st_fast_pre]\<^sub>a
       isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding rewatch_heur_st_fast_alt_def rewatch_heur_st_def rewatch_heur_vdom_def[symmetric] rewatch_heur_st_fast_pre_def
  by sepref

definition length_ivdom_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>length_ivdom_fast_code = read_vdom_wl_heur_code length_ivdom_aivdom_impl\<close>
global_interpretation length_ivdom_aivdom: read_vdom_param_adder0 where
  f = \<open>length_ivdom_aivdom_impl\<close> and
  f' = \<open>RETURN o length_ivdom_aivdom\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_vdom_wl_heur (RETURN o length_ivdom_aivdom) = RETURN o length_ivdom\<close> and
  \<open>read_vdom_wl_heur_code length_ivdom_aivdom_impl = length_ivdom_fast_code\<close>
  apply unfold_locales
  apply (rule vdom_ref)
  subgoal
    by (auto simp: read_vdom_wl_heur_def length_ivdom_aivdom_def length_ivdom_def intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: length_ivdom_fast_code_def)
  done

definition length_avdom_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>length_avdom_fast_code = read_vdom_wl_heur_code length_avdom_aivdom_impl\<close>

global_interpretation length_avdom_aivdom: read_vdom_param_adder0 where
  f = \<open>length_avdom_aivdom_impl\<close> and
  f' = \<open>RETURN o length_avdom_aivdom\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_vdom_wl_heur (RETURN o length_avdom_aivdom) = RETURN o length_avdom\<close> and
  \<open>read_vdom_wl_heur_code length_avdom_aivdom_impl = length_avdom_fast_code\<close>
  apply unfold_locales
  apply (rule vdom_ref)
  subgoal
    by (auto simp: read_vdom_wl_heur_def length_avdom_aivdom_def length_avdom_def intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: length_avdom_fast_code_def)
  done


definition length_tvdom_fast_code :: \<open>twl_st_wll_trail_fast2 \<Rightarrow> _\<close> where
  \<open>length_tvdom_fast_code = read_vdom_wl_heur_code length_tvdom_aivdom_impl\<close>

global_interpretation length_tvdom_aivdom: read_vdom_param_adder0 where
  f = \<open>length_tvdom_aivdom_impl\<close> and
  f' = \<open>RETURN o length_tvdom_aivdom\<close> and
  x_assn = sint64_nat_assn and
  P = \<open>(\<lambda>S. True)\<close>
  rewrites \<open>read_vdom_wl_heur (RETURN o length_tvdom_aivdom) = RETURN o length_tvdom\<close> and
  \<open>read_vdom_wl_heur_code length_tvdom_aivdom_impl = length_tvdom_fast_code\<close>
  apply unfold_locales
  apply (rule vdom_ref)
  subgoal
    by (auto simp: read_vdom_wl_heur_def length_tvdom_aivdom_def length_tvdom_def intro!: ext
      split: isasat_int.splits)
  subgoal
    by (auto simp: length_tvdom_fast_code_def)
  done


lemmas [sepref_fr_rules] = length_ivdom_aivdom.refine[unfolded lambda_comp_true]
  length_avdom_aivdom.refine[unfolded lambda_comp_true]
  length_tvdom_aivdom.refine[unfolded lambda_comp_true]

lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  length_ivdom_fast_code_def[unfolded read_vdom_wl_heur_code_def]
  length_avdom_fast_code_def[unfolded read_vdom_wl_heur_code_def]
  length_tvdom_fast_code_def[unfolded read_vdom_wl_heur_code_def]

sepref_register length_avdom length_ivdom length_tvdom

export_llvm polarity_st_heur_pol_fast isa_count_decided_st_fast_code get_conflict_wl_is_None_fast_code
  clause_not_marked_to_delete_heur_code access_lit_in_clauses_heur_fast_code length_ivdom_fast_code
  length_avdom_fast_code length_tvdom_fast_code

subsection \<open>More theorems\<close>

 
sepref_register get_the_propagation_reason_heur

sepref_def get_the_propagation_reason_heur_fast_code
  is \<open>uncurry get_the_propagation_reason_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a unat_lit_assn\<^sup>k \<rightarrow>\<^sub>a snat_option_assn' TYPE(64)\<close>
  unfolding get_the_propagation_reason_heur_alt_def
     isasat_bounded_assn_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref


sepref_def clause_is_learned_heur_code2
  is \<open>uncurry (RETURN oo clause_is_learned_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_vdom (get_clauses_wl_heur S) C]\<^sub>a
      isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> bool1_assn\<close>
  supply [[goals_limit = 1]]
  unfolding clause_is_learned_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clause_lbd_heur

sepref_def clause_lbd_heur_code2
  is \<open>uncurry (RETURN oo clause_lbd_heur)\<close>
  :: \<open>[\<lambda>(S, C). get_clause_LBD_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> uint32_nat_assn\<close>
  unfolding isasat_bounded_assn_def clause_lbd_heur_alt_def fold_tuple_optimizations
  supply [[goals_limit = 1]]
  by sepref



sepref_register mark_garbage_heur

sepref_def mop_mark_garbage_heur_impl
  is \<open>uncurry2 mop_mark_garbage_heur\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur_alt_def
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def
    get_clauses_wl_heur.simps
  apply (rewrite in \<open>RETURN \<hole>\<close> fold_tuple_optimizations)
  by sepref

sepref_def mark_garbage_heur_code2
  is \<open>uncurry2 (RETURN ooo mark_garbage_heur)\<close>
  :: \<open>[\<lambda>((C, i), S). mark_garbage_pre (get_clauses_wl_heur S, C) \<and> i < length_avdom S \<and>
         clss_size_lcount (get_learned_count S) \<ge> 1]\<^sub>a
       sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mark_garbage_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations clss_size_decr_lcount_def clss_size_lcount_def
    lcount_assn_def
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

sepref_def mop_mark_garbage_heur3_impl
  is \<open>uncurry2 mop_mark_garbage_heur3\<close>
  :: \<open>[\<lambda>((C, i), S). length (get_clauses_wl_heur S) \<le> sint64_max]\<^sub>a
      sint64_nat_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding mop_mark_garbage_heur3_def fold_tuple_optimizations
    clause_not_marked_to_delete_heur_pre_def prod.case isasat_bounded_assn_def mark_garbage_heur3_def
  by sepref

sepref_register delete_index_vdom_heur


sepref_def delete_index_vdom_heur_fast_code2
  is \<open>uncurry (RETURN oo delete_index_vdom_heur)\<close>
  :: \<open>[\<lambda>(i, S). i < length_tvdom S]\<^sub>a
        sint64_nat_assn\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>d \<rightarrow> isasat_bounded_assn\<close>
  supply [[goals_limit = 1]]
  supply [simp] = length_tvdom_def
  unfolding delete_index_vdom_heur_def isasat_bounded_assn_def delete_index_and_swap_alt_def
    length_avdom_def fold_tuple_optimizations
  by sepref

sepref_register access_length_heur

sepref_def access_length_heur_fast_code2
  is \<open>uncurry (RETURN oo access_length_heur)\<close>
  :: \<open>[\<lambda>(S, C). arena_is_valid_clause_idx (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> sint64_nat_assn\<close>
  supply [[goals_limit = 1]]
  unfolding access_length_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register marked_as_used_st

sepref_def marked_as_used_st_fast_code
  is \<open>uncurry (RETURN oo marked_as_used_st)\<close>
  :: \<open>[\<lambda>(S, C). marked_as_used_pre (get_clauses_wl_heur S) C]\<^sub>a
       isasat_bounded_assn\<^sup>k *\<^sub>a sint64_nat_assn\<^sup>k \<rightarrow> unat_assn' TYPE(2)\<close>
  supply [[goals_limit = 1]]
  unfolding marked_as_used_st_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref



sepref_def get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a word64_assn\<close>
  unfolding get_conflict_count_since_last_restart_heur_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_def get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def fold_tuple_optimizations
  by sepref

sepref_register clss_size_lcount get_learned_count_number

sepref_def get_learned_count_number_fast_code
  is \<open>RETURN o get_learned_count_number\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_nat_assn\<close>
  unfolding isasat_bounded_assn_def get_learned_count_number_alt_def fold_tuple_optimizations
  by sepref

sepref_def learned_clss_count_fast_code
  is \<open>RETURN o learned_clss_count\<close>
  :: \<open>[\<lambda>S. learned_clss_count S \<le> uint64_max]\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> uint64_nat_assn\<close>
  unfolding clss_size_allcount_alt_def learned_clss_count_def fold_tuple_optimizations
  by sepref

end
