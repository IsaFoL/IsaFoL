theory CDCL_Two_Watched_Literals_List_Watched_Init_Code
imports CDCL_Two_Watched_Literals_List_Watched_Code
begin

type_synonym 'v twl_st_wl' =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl"

type_synonym twl_st_wll' =
  "nat_trail \<times> clauses_wl \<times> nat \<times> nat array_list option \<times>  unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l"
 
definition init_dt_step_wl :: \<open>nat clause_l \<Rightarrow> nat twl_st_wl' \<Rightarrow> (nat twl_st_wl') nres\<close> where
  \<open>init_dt_step_wl C S = do {
   (let (M, N, U, D, NP, UP, Q) = S in
   (case D of
    None \<Rightarrow>
    if length C = 1
    then do {
      ASSERT (no_dup M);
      ASSERT (C \<noteq> []);
      let L = hd C;
      let val_L = valued M L;
      if val_L = None
      then do {RETURN (Propagated L 0 # M, N, U, None, add_mset {#L#} NP, UP, add_mset (-L) Q)}
      else
        if val_L = Some True
        then do {RETURN (M, N, U, None, add_mset {#L#} NP, UP, Q)}
        else do {RETURN (M, N, U, Some (mset C), add_mset {#L#} NP, UP, {#})}
      }
    else do {
      ASSERT(C \<noteq> []);
      ASSERT(tl C \<noteq> []);
      let U = length N;
      RETURN (M, N @ [op_array_of_list C], U, None, NP, UP, Q)}
  | Some D \<Rightarrow>
    if length C = 1
    then do {
      ASSERT (C \<noteq> []);
      let L = hd C;
      RETURN (M, N, U, Some D, add_mset {#L#} NP, UP, {#})}
    else do {
      ASSERT(C \<noteq> []);
      ASSERT(tl C \<noteq> []);
      let U = length N;
      RETURN (M, N @ [op_array_of_list C], U, Some D, NP, UP, {#})}))
  }\<close>

definition twl_st_l_assn' :: \<open>nat twl_st_wl' \<Rightarrow> twl_st_wll' \<Rightarrow> assn\<close> where
\<open>twl_st_l_assn' \<equiv>
  (pair_nat_ann_lits_assn *assn clauses_ll_assn *assn nat_assn *assn
  conflict_option_assn *assn
  unit_lits_assn *assn
  unit_lits_assn *assn
  clause_l_assn
  )\<close>
definition array_of_list :: "'a::heap list \<Rightarrow> 'a array_list Heap" where
  \<open>array_of_list l = do {
     e \<leftarrow> Array.of_list l;
     arl_of_array_raa e}\<close>

definition [simp]: "op_arl_of_list \<equiv> op_list_copy"

lemma array_of_list_op_arl_list:
  assumes p: \<open>CONSTRAINT is_pure R\<close> 
  shows \<open>(array_of_list, RETURN \<circ> op_arl_of_list) \<in> 
    [\<lambda>xs. xs \<noteq> []]\<^sub>a (list_assn R)\<^sup>d \<rightarrow> arl_assn R\<close>
proof -
  obtain R' where R: \<open>R = pure R'\<close> and \<open>R' = the_pure R\<close>
    using p by auto
  have \<open>x \<noteq> [] \<Longrightarrow>
       <xa \<mapsto>\<^sub>a xi * list_assn R x xi> arl_of_array_raa xa
       <\<lambda>r. arl_assn R x r * true>\<close> for x xi xa
    by (sep_auto simp: arl_of_array_raa_def arl_assn_def hr_comp_def is_array_list_def R
        list_assn_pure_conv mod_star_conv)
  moreover have \<open>(\<exists>\<^sub>Axa. arl_assn R xa r * true * \<up> (xa = x)) = (arl_assn R x r * true)\<close> for x r
    using ex_assn_up_eq by force
  ultimately show ?thesis
    by (sepref_to_hoare) (sep_auto simp: array_of_list_def array_assn_def[symmetric])
qed

lemma array_of_list_mset[sepref_fr_rules]:
  shows \<open>(array_of_list, RETURN \<circ> mset) \<in> 
    [\<lambda>xs. xs \<noteq> []]\<^sub>a (list_assn nat_lit_assn)\<^sup>d \<rightarrow> conflict_assn\<close>
proof -
  have 1: \<open>(RETURN \<circ> op_arl_of_list, RETURN o mset) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>list_mset_rel\<rangle>nres_rel\<close>
    by (auto intro!: frefI nres_relI simp: list_mset_rel_def br_def)
  show ?thesis
    by (rule array_of_list_op_arl_list[of nat_lit_assn, FCOMP 1]) simp
qed

sepref_thm init_dt_step_l
  is \<open>uncurry init_dt_step_wl\<close>
  :: \<open>(list_assn nat_lit_assn)\<^sup>d *\<^sub>a twl_st_l_assn'\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn'\<close>
  unfolding init_dt_step_wl_def twl_st_l_assn'_def
  unfolding  length_rll_def[symmetric] PR_CONST_def
  unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding swap_ll_def[symmetric]
  apply (rewrite at \<open>(add_mset _ \<hole>)\<close> lms_fold_custom_empty)+
  apply (rewrite at \<open>(_, \<hole>)\<close> lms_fold_custom_empty)+
  supply [[goals_limit = 1]]
  by sepref

end