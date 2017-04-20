theory CDCL_Two_Watched_Literals_List_Simple_Code
  imports CDCL_Two_Watched_Literals_List DPLL_CDCL_W_Implementation
    CDCL_Two_Watched_Literals_Initialisation CDCL_Two_Watched_Literals_Code_Common
begin

section \<open>CDCL Code (without caching clause watched by a literal)\<close>

text \<open>Some functions and types:\<close>


abbreviation nat_lits_trail_assn :: "ann_lits_l \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> assn" where
  \<open>nat_lits_trail_assn \<equiv> list_assn (nat_ann_lit_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> list_assn nat_lit_assn_id\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> list_assn clause_ll_assn\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn_id\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation clauses_to_update_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation clauses_to_update_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>clauses_to_update_ll_assn \<equiv> list_assn nat_assn\<close>

type_synonym clauses_to_update_ll = "nat list"
type_synonym lit_queue_l = "nat literal list"

type_synonym twl_st_ll =
  "(nat, nat) ann_lits \<times> nat clauses_l \<times> nat \<times>
    nat cconflict_l \<times> nat clauses_l \<times> nat clauses_l \<times> clauses_to_update_ll \<times> lit_queue_l"

fun twl_st_of_ll :: \<open>twl_st_ll \<Rightarrow> nat twl_st_l\<close> where
  \<open>twl_st_of_ll (M, N, U, D, NP, UP, WS, Q) = (M, N, U, map_option mset D, mset `# mset NP, mset `# mset UP, mset WS, mset Q)\<close>

abbreviation cconflict_assn :: \<open>nat cconflict \<Rightarrow> nat cconflict_l \<Rightarrow> assn\<close> where
  \<open>cconflict_assn \<equiv> option_assn (list_mset_assn nat_lit_assn_id)\<close>

notation prod_assn (infixr "*assn" 90)

abbreviation twl_st_l_assn :: \<open>nat twl_st_l \<Rightarrow> twl_st_ll \<Rightarrow> assn\<close> where
\<open>twl_st_l_assn \<equiv>
 nat_lits_trail_assn *assn clauses_ll_assn *assn nat_assn *assn
 cconflict_assn *assn
 clauses_l_assn *assn
 clauses_l_assn *assn
 clauses_to_update_l_assn *assn
 clause_l_assn
\<close>
abbreviation nat_ann_lits_assn :: "ann_lits_l \<Rightarrow> ann_lits_l \<Rightarrow> assn" where
  \<open>nat_ann_lits_assn \<equiv> list_assn nat_ann_lit_assn\<close>

sepref_definition defined_lit_map_impl' is
  \<open>uncurry (defined_lit_map_impl :: (nat, nat) ann_lit list \<Rightarrow> _)\<close> ::
  \<open>(nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding defined_lit_map_impl_def
  by sepref

lemma defined_lit_map_impl_denifend_lit: \<open>defined_lit_map_impl M L \<le> SPEC (op = (defined_lit M L))\<close>
  unfolding defined_lit_map_impl_def
  apply (induction M)
   apply (auto simp: defined_lit_cons)
  by (smt RES_sng_eq_RETURN eq_iff nfoldli_no_ctd)

lemma defined_lit_map_impl_spec: \<open>(uncurry defined_lit_map_impl, uncurry (RETURN oo op_defined_lit_imp)) \<in>
    (Id :: ((nat, nat) ann_lit list \<times> _) set) \<times>\<^sub>r (Id ::  (nat literal \<times>_) set) \<rightarrow> \<langle>bool_rel\<rangle> nres_rel\<close>
  apply clarify
  apply refine_rcg
  using defined_lit_map_impl_denifend_lit
  by (auto simp add: RES_sng_eq_RETURN)

lemma defined_lit_map_impl'_refine:
  \<open>(uncurry (defined_lit_map_impl'), uncurry (RETURN oo op_defined_lit_imp)) \<in>
    (nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using defined_lit_map_impl'.refine[FCOMP defined_lit_map_impl_spec]
  unfolding op_defined_lit_imp_def .

sepref_decl_impl defined_lit_impl: defined_lit_map_impl'_refine .

definition valued_impl :: "(nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option nres" where
  \<open>valued_impl M L =
    nfoldli M
     (\<lambda>brk. brk = None)
     (\<lambda>L' _. do {
       let L\<^sub>1 = atm_of L;
       let L\<^sub>2 = (lit_of L');
       let L\<^sub>2' = atm_of (lit_of L');
       if L = L\<^sub>2 then RETURN (Some True)
       else
         if L\<^sub>1 = L\<^sub>2' then RETURN (Some False) else RETURN None
    })
    None\<close>

sepref_definition valued_impl' is \<open>uncurry valued_impl\<close> ::
  \<open>(nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
  unfolding valued_impl_def
  by sepref

lemma valued_impl_valued:
  assumes \<open>no_dup M\<close>
  shows \<open>valued_impl M L = RETURN (valued M L)\<close>
    using assms
  apply (induction M)
   apply (simp add: valued_def valued_impl_def Decided_Propagated_in_iff_in_lits_of_l atm_of_eq_atm_of)[]
  by (auto simp add: valued_def valued_impl_def defined_lit_map dest: in_lits_of_l_defined_litD)

lemma hrp_comp_Id2[simp]: \<open>hrp_comp A Id = A\<close>
  unfolding hrp_comp_def
  by auto

lemma valued_impl_spec:
  shows \<open>(uncurry valued_impl, uncurry (RETURN oo valued)) \<in> [\<lambda>(M, L). no_dup M]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  unfolding fref_def nres_rel_def
  by (auto simp: valued_impl_valued IS_ID_def)


definition valued'  :: "(nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option" where
  \<open>valued' = valued\<close>


context
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI] frefI
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

sepref_decl_op valued: \<open>valued :: ((nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option)\<close>
  :: "(Id :: ((nat, nat) ann_lits \<times>_)set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (bool option\<times> _) set)"
  .

lemma [def_pat_rules]:
  "valued $ a $ b \<equiv> op_valued $ a $ b"
  by auto

term case_bool
lemma case_bool_if: "case_bool a b v = (if v then a else b)"
  by (cases v) auto

lemma valued_impl'_refine:
  shows \<open>(uncurry valued_impl', uncurry (RETURN oo op_valued)) \<in>
    [\<lambda>(M, _). no_dup M]\<^sub>a (nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  using valued_impl'.refine[FCOMP valued_impl_spec]
  unfolding hrp_comp_Id2 valued'_def op_valued_def .

sepref_decl_impl valued: valued_impl'_refine
  by simp

end

sepref_definition find_unwatched_impl is
   "uncurry (find_unwatched :: (nat, nat) ann_lits
      \<Rightarrow> nat literal list \<Rightarrow> nat option nres)"
  :: \<open>[\<lambda>(M, L). no_dup M]\<^sub>anat_ann_lits_assn\<^sup>k *\<^sub>a (list_assn nat_lit_assn_id)\<^sup>k \<rightarrow> option_assn nat_assn\<close>
  unfolding find_unwatched_def
  supply [[goals_limit=1]]
  by sepref

sepref_register "find_unwatched :: (nat, nat) ann_lits
      \<Rightarrow> nat literal list \<Rightarrow> nat option nres"
declare find_unwatched_impl.refine[sepref_fr_rules]
thm HOL_list_prepend_hnr_mop
term op_list_empty


sepref_decl_op Propagated : "Propagated :: nat literal \<Rightarrow> nat \<Rightarrow> (nat, nat) ann_lit"
  :: "((Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat \<times> _) set) \<rightarrow> (Id :: ((nat, nat) ann_lit \<times> _) set))"
  .

lemma [def_pat_rules]:
  "Propagated $ a $ b \<equiv> op_Propagated $ a $ b"
  by auto

lemma op_Propagated_refine[sepref_fr_rules]:
  \<open>(uncurry (return oo op_Propagated), uncurry (RETURN oo op_Propagated)) \<in>
     nat_lit_assn_id\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_ann_lit_assn\<close>
  apply (
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      intro: Assertions.mod_emp_simp)
  done

sepref_decl_op Decided : "Decided :: nat literal \<Rightarrow> (nat, nat) ann_lit"
  :: "((Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: ((nat, nat) ann_lit \<times> _) set))"
  .

lemma [def_pat_rules]:
  "Decided $ a \<equiv> op_Decided $ a"
  by auto

sepref_decl_op uminus_lit: \<open>uminus :: nat literal \<Rightarrow> nat literal\<close>
  :: \<open>(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set)\<close>
  .

lemma [def_pat_rules]:
  "uminus $ a \<equiv> op_uminus_lit $ a"
  by auto

lemma op_uminus_lit_refine[sepref_fr_rules]:
  \<open>(return o op_uminus_lit, RETURN o op_uminus_lit) \<in>
     nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn_id\<close>
  apply (
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      intro: Assertions.mod_emp_simp)
  done

lemma [sepref_fr_rules]:
  \<open>((return o op_Decided), (RETURN o op_Decided)) \<in>
     nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a nat_ann_lit_assn\<close>
  apply (
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      intro: Assertions.mod_emp_simp)
  done


subsection \<open>Code Generation\<close>

subsubsection \<open>The Body of the Inner Propagation\<close>
lemma Collect_eq_comp: \<open>{(c, a). a = f c} O {(x, y). P x y} = {(c, y). P (f c) y}\<close>
  by auto

lemma id_mset_hnr[sepref_fr_rules]:
 \<open>((return o id), (RETURN o mset)) \<in> (list_assn (pure R))\<^sup>d \<rightarrow>\<^sub>a list_mset_assn (pure R)\<close>
  unfolding list_assn_pure_conv list_mset_assn_def the_pure_pure
  by sepref_to_hoare (sep_auto simp: list_mset_assn_def mset_rel_def rel_mset_def
      rel2p_def[abs_def] p2rel_def list_mset_rel_def br_def Collect_eq_comp pure_def list_rel_def)

sepref_definition unit_propagation_inner_loop_body_l_impl is \<open>uncurry2 (unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close> ::
  \<open>nat_lit_assn_id\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_body_l_def unfolding lms_fold_custom_empty
  supply [[goals_limit=1]]
  by sepref

concrete_definition unit_propagation_inner_loop_body_l_impl' uses
  unit_propagation_inner_loop_body_l_impl.refine

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (SML) CDCL_W_Level

prepare_code_thms unit_propagation_inner_loop_body_l_impl'_def
export_code unit_propagation_inner_loop_body_l_impl' in SML

sepref_register \<open>unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_inner_loop_body_l_impl.refine_raw[sepref_fr_rules]

sepref_register \<open>select_from_clauses_to_update :: nat twl_st_l \<Rightarrow> (nat twl_st_l \<times> nat) nres\<close>


subsubsection \<open>The Inner Propagation Loop\<close>

lemma list_mst_assn_add_mset_empty_false:
  \<open>\<not>(as, bk) \<Turnstile> list_mset_assn (\<lambda>a c::nat. \<up> (c = a)) (add_mset x N) []\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [iff]: \<open>([], y) \<in> list_mset_rel \<longleftrightarrow> y = {#}\<close> for y
    by (auto simp: list_mset_rel_def br_def)
  show ?thesis
    by (auto simp: list_mset_assn_def)
qed

lemma list_mset_assn_add_mset_cons_in:
  assumes
    assn: \<open>A \<Turnstile> list_mset_assn (\<lambda>a c. \<up> (c = a)) (add_mset x N) (ab # list)\<close>
  shows \<open>ab \<in># add_mset x N\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [iff]: \<open>(ab # list, y) \<in> list_mset_rel \<longleftrightarrow> y = add_mset ab (mset list)\<close> for y ab list
    by (auto simp: list_mset_rel_def br_def)
  then have \<open>add_mset x N = mset (ab # list)\<close>
    using assn
    apply (cases A)
    by (auto simp: list_mset_assn_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] add_mset_eq_add_mset list.rel_eq)
  show ?thesis
    using assn
    apply (cases A)
    apply (auto simp: list_mset_assn_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] add_mset_eq_add_mset list.rel_eq)
    done
qed

definition select_from_clauses_to_update2 :: \<open>'v twl_st_l \<Rightarrow> (nat) nres\<close> where
  \<open>select_from_clauses_to_update2 S = SPEC (\<lambda>C. C \<in># clauses_to_update_l S)\<close>

lemma hd_select_from_clauses_to_update2_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd WS),
      select_from_clauses_to_update2) \<in>
    [\<lambda>S. clauses_to_update_l S \<noteq> {#}]\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow> nat_assn\<close>
  unfolding select_from_clauses_to_update2_def
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac \<open>af\<close>; case_tac am)
    apply sep_auto
  apply (sep_auto)
     apply (auto simp: mod_pure_star_dist list_mst_assn_add_mset_empty_false
    dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
      dest!: mod_starD; fail)+
  done

definition hd_of_clauses_to_update_l :: \<open>twl_st_ll \<Rightarrow> nat\<close> where
  \<open>hd_of_clauses_to_update_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd WS)\<close>

definition tl_of_clauses_to_update_l :: \<open>twl_st_ll \<Rightarrow> twl_st_ll\<close> where
  \<open>tl_of_clauses_to_update_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). (M, N, U, D, NP, UP, tl WS, Q))\<close>

lemma entails_list_mset_assn_eq_mset:
  assumes \<open>(ay, bm) \<Turnstile> list_mset_assn (\<lambda>a c. \<up> (c = a)) af am\<close>
  shows \<open>af = mset am\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  show ?thesis
    using assms
    by (auto simp: list_mset_assn_def mset_rel_def p2rel_def rel_mset_def (* the_pure_def *)
      list_mset_rel_def br_def rel2p_dflt list.rel_eq)
qed

lemma entails_list_mset_assn_list_mset_assn_eq_mset:
  assumes \<open>(ay, bm) \<Turnstile> list_mset_assn (list_mset_assn (\<lambda>a c. \<up> (c = a))) af am\<close>
  shows \<open>af = mset `# mset am\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [simp]: \<open>{(c, a). a = mset c} O
           {(x, y). \<exists>xs. mset xs = x \<and> mset xs = y} = {(c, a). a = mset c}\<close>
    by auto
  have [simp]: \<open>list_all2 (\<lambda>x y. y = mset x) xs ys \<Longrightarrow> mset ys = mset `# mset xs\<close> for xs ys
    apply (subgoal_tac \<open>length xs = length ys\<close>)
    apply (rotate_tac)
    subgoal by (induction xs ys rule: list_induct2) auto
    subgoal by (simp add: list_all2_iff)
    done
  show ?thesis
    using assms
    by (auto simp: list_mset_assn_def mset_rel_def p2rel_def
      list_mset_rel_def br_def rel2p_dflt list.rel_eq rel2p_def[abs_def] rel_mset_def)
qed

lemma entails_list_assn_eqD:
  assumes \<open>A \<Turnstile> list_assn (\<lambda>a c. \<up> (c = a)) a ag\<close>
  shows \<open>a = ag\<close>
  using assms
  apply (induction a arbitrary: ag)
  subgoal by simp
  subgoal for a1 a2 ag by (cases ag) auto
  done

lemma entails_list_assn_list_assn_eqD:
  assumes \<open>A \<Turnstile> list_assn (list_assn (\<lambda>a c. \<up> (c = a))) a ag\<close>
  shows \<open>a = ag\<close>
  using assms
  apply (induction a arbitrary: ag A)
  subgoal by simp
  subgoal for a1 a2 ag by (cases ag) (auto dest!: mod_starD entails_list_assn_eqD)
  done

lemma entails_option_assn_assn_eqD:
  assumes \<open>A \<Turnstile> option_assn (list_assn (\<lambda>a c. \<up> (c = a))) a ag\<close>
  shows \<open>a = ag\<close>
  using assms
  apply (induction a arbitrary: ag A)
  subgoal by simp
  subgoal for a ag A by (cases ag) (auto dest!: mod_starD entails_list_assn_eqD)
  done

lemma mset_tl_remove1_mset_hd:
  \<open>am \<noteq> [] \<Longrightarrow> mset (tl am) = remove1_mset (hd am) (mset am)\<close>
  by (cases am) auto


lemma list_assn_same_emp: \<open>(\<And>a. R a a = emp) \<Longrightarrow> list_assn R ag ag = emp\<close>
  by (induction ag) auto

lemma option_assn_same_emp: \<open>(\<And>a. R a a = emp) \<Longrightarrow> option_assn R ag ag = emp\<close>
  by (induction ag) auto

lemma list_assn_same_emp_id: \<open>list_assn (\<lambda>a c. \<up> (c = a)) ag ag = emp\<close>
  by (auto simp: list_assn_same_emp)

lemma list_assn_list_assn_same_emp_id: \<open>list_assn (list_assn (\<lambda>a c. \<up> (c = a))) ag ag = emp\<close>
  by (auto simp: list_assn_same_emp)

lemma list_mset_assn_id_mset_emp: \<open>list_mset_assn (\<lambda>a c. \<up> (c = a)) (mset am) am = emp\<close>
proof -
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [simp]: \<open>{(c, a). a = mset c} O
           {(x, y). \<exists>xs. mset xs = x \<and> mset xs = y} = {(c, a). a = mset c}\<close>
    by auto
  show ?thesis
    by (auto simp: list_mset_assn_def mset_rel_def p2rel_def pure_def
      list_mset_rel_def br_def rel2p_dflt list.rel_eq rel2p_def[abs_def] rel_mset_def)
qed
lemma recomp_set_eq_simp: \<open>{(c, a). a = f c} O {(x, y). P x y} = {(c, y). P (f c) y}\<close>
  by auto

lemma list_all2_eq_mset_iff:
  \<open>list_all2 (\<lambda>x y. y = mset x) xs ys \<longleftrightarrow> map mset xs = ys\<close> (is \<open>?A \<longleftrightarrow> ?B\<close>)
proof
  assume A: ?A
  then have \<open>length xs = length ys\<close>
    by (simp add: list_all2_iff)
  then show ?B
    using A by (induction xs ys rule: list_induct2) auto
next
  assume B: ?B
  then have \<open>length xs = length ys\<close>
    by auto
  then show ?A
    using B by (induction xs ys rule: list_induct2) auto
qed

lemma list_mset_assn_list_mset_assn_id_mset_mset_emp:
  \<open>list_mset_assn (list_mset_assn (\<lambda>a c. \<up> (c = a))) (mset `# mset al) al = emp\<close>
proof -
  have H: \<open>(\<forall>x x'. (x = mset x') = ((x', x) \<in> P')) \<longleftrightarrow> P' = {(c, a). a = mset c}\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (a = mset c)) =  {(c, a). a = mset c}\<close>
    by (auto simp: the_pure_def H)
  have H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close> for P'
    by (auto simp: the_pure_def)
  have [simp]: \<open>the_pure (\<lambda>a c. \<up> (c = a)) = Id\<close>
    by (auto simp: the_pure_def H)
  have [simp]: \<open>{(c, a). a = mset c} O
           {(x, y). \<exists>xs. mset xs = x \<and> mset xs = y} = {(c, a). a = mset c}\<close>
    by auto
  have [simp]: \<open>{(c, a). a = mset c} O {(x, y). \<exists>xs. mset xs = x \<and> (\<exists>ys. mset ys = y \<and> list_all2 (\<lambda>x y. y = mset x) xs ys)} =
    {(c, a). a = mset `# mset c}\<close>
    by (auto simp add: recomp_set_eq_simp list_all2_eq_mset_iff)
  show ?thesis
    by (auto simp: list_mset_assn_def mset_rel_def p2rel_def pure_def
      list_mset_rel_def br_def rel2p_dflt list.rel_eq rel2p_def[abs_def] rel_mset_def)
qed

lemma hd_select_from_clauses_to_update_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>S. (tl_of_clauses_to_update_l S, hd_of_clauses_to_update_l S)),
      select_from_clauses_to_update) \<in>
    [\<lambda>S. clauses_to_update_l S \<noteq> {#}]\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow> prod_assn twl_st_l_assn nat_assn\<close>
proof -
  have H: \<open>RETURN x
         \<le> SPEC (\<lambda>(S', C).
                     C \<in># clauses_to_update_l S \<and>
                     S' = set_clauses_to_update_l (remove1_mset C (clauses_to_update_l S)) S)\<close>
   if \<open>snd x \<in># clauses_to_update_l S\<close> and
   \<open>fst x = set_clauses_to_update_l (remove1_mset (snd x) (clauses_to_update_l S)) S\<close>
   for x :: \<open>nat twl_st_l \<times> nat\<close> and S :: \<open>nat twl_st_l\<close> and xi xi' :: twl_st_ll
     using that by auto
  show ?thesis
    unfolding select_from_clauses_to_update_def tl_of_clauses_to_update_l_def hd_of_clauses_to_update_l_def
    apply sepref_to_hoare
    apply (sep_auto (plain))
     apply (rule_tac psi = \<open>RETURN ((\<lambda>_ _ (S, C). (twl_st_of_ll S, C)) x xi xa) \<le> _\<close> in asm_rl)
     apply (rule order_trans[OF _ H])
       apply (rule order_refl)
      apply (auto simp: list_mst_assn_add_mset_empty_false
        dest!: list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset; fail)[]
     apply (auto simp: mod_pure_star_dist mset_tl_remove1_mset_hd option_assn_alt_def
        dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset
        entails_list_assn_eqD entails_list_assn_list_assn_eqD entails_option_assn_assn_eqD
        entails_list_mset_assn_list_mset_assn_eq_mset
        split: option.splits; fail)[]
    by (sep_auto intro!: ent_star_mono simp: list_assn_same_emp option_assn_same_emp
        list_mset_assn_id_mset_emp list_mset_assn_list_mset_assn_id_mset_mset_emp
        option_assn_alt_def
        split: option.splits)
qed

lemma clauses_to_update_l_abs_def:\<open>clauses_to_update_l = (fst o snd o snd o snd o snd o snd o snd)\<close>
  by auto

lemma clauses_to_update_l_refine[sepref_fr_rules]:
  \<open>(return o ((fst o snd o snd o snd o snd o snd o snd) ::  twl_st_ll \<Rightarrow> _),
     RETURN o (clauses_to_update_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a list_mset_assn nat_assn\<close>
  unfolding clauses_to_update_l_abs_def
  by sepref_to_hoare sep_auto

sepref_definition unit_propagation_inner_loop_l_impl is
  \<open>uncurry (unit_propagation_inner_loop_l :: nat literal \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>nat_lit_assn_id\<^sup>k *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding unit_propagation_inner_loop_l_def
  by sepref


sepref_register \<open>unit_propagation_inner_loop_l :: nat literal \<Rightarrow>  nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_inner_loop_l_impl.refine[sepref_fr_rules]


subsubsection \<open>The Outer Propagation Loop\<close>

sepref_register \<open>select_and_remove_from_literals_to_update :: nat twl_st_l \<Rightarrow> (nat twl_st_l \<times> nat literal) nres\<close>

definition hd_of_literals_to_update_l :: \<open>twl_st_ll \<Rightarrow> nat literal\<close> where
  \<open>hd_of_literals_to_update_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd Q)\<close>

(* TODO Move to top *)
fun get_clauses_ll :: "twl_st_ll \<Rightarrow> nat clauses_l" where
  \<open>get_clauses_ll (M, N, U, D, NP, UP, WS, Q) = N\<close>
(* End move *)

definition clause_to_update_l :: \<open>nat literal \<Rightarrow> twl_st_ll \<Rightarrow> clauses_to_update_ll\<close> where
  \<open>clause_to_update_l L S =
    filter
      (\<lambda>C::nat. get_clauses_ll S ! C ! 0 = L \<or> get_clauses_ll S ! C ! 1 = L)
      ([1..<length (get_clauses_ll S)])\<close>

definition tl_of_literals_to_update_l :: \<open>twl_st_ll \<Rightarrow> twl_st_ll\<close> where
  \<open>tl_of_literals_to_update_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). (M, N, U, D, NP, UP,
     clause_to_update_l (hd Q) (M, N, U, D, NP, UP, WS, Q),
     tl Q))\<close>


lemma nth_mem_tl: \<open>0 < x \<Longrightarrow> x < length N \<Longrightarrow> N!x \<in> set (tl N)\<close>
  using nth_mem[of \<open>x - 1\<close> \<open>tl N\<close>] by (cases N) (auto simp del: nth_mem)

lemma clause_to_update_l_clause_to_update:
  fixes M N av D NP UP WS Q
  assumes \<open>twl_struct_invs (twl_st_of None (M, N, U, map_option mset D, mset `# mset NP, mset `# mset UP, mset WS, mset Q))\<close>
  shows \<open>mset (clause_to_update_l (hd Q) (M, N, U, D, NP, UP, WS, Q)) =
   clause_to_update (hd Q) (M, N, U, map_option mset D, mset `# mset NP, mset `# mset UP, mset WS, mset Q)\<close>
proof -
  have \<open>Multiset.Ball (twl_clause_of `# mset (tl N)) struct_wf_twl_cls\<close>
    using assms
    unfolding twl_struct_invs_def
    apply (simp only: twl_st_inv.simps twl_st_of.simps mset_append[symmetric]
         image_mset_union[symmetric] drop_Suc append_take_drop_id)
    by fast
  then have length_ge_2: \<open>length (N ! x) \<ge> 2\<close> if \<open>x > 0\<close> and \<open>x < length N\<close> for x
    using that by (auto dest: nth_mem_tl)
  have H: \<open>length (N ! x) \<noteq> Suc 0\<close> \<open>N!x \<noteq> []\<close>if \<open>Suc 0 \<le> x\<close>\<open> x < length N\<close> for x
    using that length_ge_2[of x] by auto
  have [simp]: \<open>(\<lambda>x. Suc 0 \<le> x \<and> x < length N \<and> (N ! x ! 0 = hd Q \<or> N ! x ! Suc 0 = hd Q)) =
      (\<lambda>x. Suc 0 \<le> x \<and> x < length N \<and> hd Q \<in> set (take 2 (N ! x)))\<close>
    by (intro ext) (auto simp: take_2_if simp: H)
  show ?thesis
    using assms by (auto simp: clause_to_update_l_def clause_to_update_def mset_filter)
qed

text \<open>More assumption needed here. Probably relies on full invariant.\<close>
lemma hd_select_and_remove_from_literals_to_update_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>S. (tl_of_literals_to_update_l S, hd_of_literals_to_update_l S)),
      select_and_remove_from_literals_to_update) \<in>
    [\<lambda>S. literals_to_update_l S \<noteq> {#} \<and> twl_struct_invs (twl_st_of None S)]\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow> prod_assn twl_st_l_assn nat_lit_assn_id\<close>
proof -
  have H: \<open>RETURN x \<le> select_and_remove_from_literals_to_update S\<close>
   if \<open>snd x \<in># literals_to_update_l S\<close> and
   \<open>fst x = set_clauses_to_update_l (clause_to_update (snd x) S) (set_literals_to_update_l (literals_to_update_l S - {#snd x#}) S)\<close>
   for x :: \<open>nat twl_st_l \<times> nat literal\<close> and S :: \<open>nat twl_st_l\<close> and xi xi' :: twl_st_ll
     using that by (auto simp: select_and_remove_from_literals_to_update_def)
  show ?thesis
    unfolding tl_of_literals_to_update_l_def hd_of_literals_to_update_l_def
    apply sepref_to_hoare
    apply (sep_auto (plain))
     apply (rule_tac psi = \<open>RETURN ((\<lambda>_ _ (S, C). (twl_st_of_ll S, C)) x xi xa) \<le> _\<close> in asm_rl)
     apply (rule order_trans[OF _ H])
       apply (rule order_refl)
      apply (auto simp: list_mst_assn_add_mset_empty_false simp del: twl_st_of_ll.simps
        dest!: list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset; fail)[]
     apply (auto simp: mod_pure_star_dist mset_tl_remove1_mset_hd option_assn_alt_def
        clause_to_update_l_clause_to_update
        dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset
        entails_list_assn_eqD entails_list_assn_list_assn_eqD entails_option_assn_assn_eqD
        entails_list_mset_assn_list_mset_assn_eq_mset
        intro!: clause_to_update_l_clause_to_update split: option.splits)[]
    apply (sep_auto intro!: ent_star_mono simp: list_assn_same_emp option_assn_same_emp
        list_mset_assn_id_mset_emp list_mset_assn_list_mset_assn_id_mset_mset_emp option_assn_alt_def
        split: option.splits)
   done
qed

lemma literals_to_update_l_refine[sepref_fr_rules]:
  \<open>(return o ((snd o snd o snd o snd o snd o snd o snd) ::  twl_st_ll \<Rightarrow> _),
     RETURN o (literals_to_update_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a list_mset_assn nat_lit_assn_id\<close>
  by sepref_to_hoare sep_auto

lemma get_trail_l_refine[sepref_fr_rules]:
  \<open>(return o (fst ::  twl_st_ll \<Rightarrow> _),
     RETURN o (get_trail_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a nat_ann_lits_assn\<close>
  by sepref_to_hoare sep_auto

sepref_definition unit_propagation_outer_loop_l_impl is
  \<open>(unit_propagation_outer_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding unit_propagation_outer_loop_l_def
  by sepref

sepref_register \<open>unit_propagation_outer_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_outer_loop_l_impl.refine[sepref_fr_rules]


subsubsection \<open>Skip and Resolve\<close>

lemma is_decided_hnr[sepref_fr_rules]:
  \<open>(return o (is_decided :: (nat, nat) ann_lit \<Rightarrow> _),
      RETURN o (is_decided :: (nat, nat) ann_lit \<Rightarrow> _)) \<in>
      nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare sep_auto


fun get_conflict_ll :: "twl_st_ll \<Rightarrow> nat clause_l option" where
  \<open>get_conflict_ll (_, _, _, D, _, _, _, _) = D\<close>

lemma get_conflict_l_hnr[sepref_fr_rules]:
  \<open>(return o (get_conflict_ll :: twl_st_ll\<Rightarrow> _),
      RETURN o (get_conflict_l :: nat twl_st_l \<Rightarrow> _)) \<in>
      twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a cconflict_assn\<close>
  by sepref_to_hoare sep_auto

lemma option_is_empty:
   \<open>a = Some {#} \<longleftrightarrow> \<not>is_None a \<and> Multiset.is_empty (the a)\<close>
  by (cases a) (auto simp: Multiset.is_empty_def)

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o lit_and_ann_of_propagated, RETURN o lit_and_ann_of_propagated) \<in>
     [\<lambda>L. is_proped L]\<^sub>a nat_ann_lit_assn\<^sup>k \<rightarrow> prod_assn nat_lit_assn_id nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x)
   apply sep_auto+
  done

(* TODO change order of the arguments of maximum_level_code *)
lemma get_maximum_level_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (\<lambda>M D. maximum_level_code D M)),
      uncurry (RETURN oo (get_maximum_level :: (nat, nat) ann_lit list \<Rightarrow> _))) \<in>
    nat_ann_lits_assn\<^sup>d *\<^sub>a (list_mset_assn nat_lit_assn_id)\<^sup>d \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_code_eq_get_maximum_level
  apply sepref_to_hoare
  by (sep_auto dest: entails_list_assn_eqD entails_list_mset_assn_eq_mset
      simp: mod_star_conv)

lemma maximum_level_code_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo maximum_level_code),
      uncurry (RETURN oo (maximum_level_code :: _ \<Rightarrow> (nat, nat) ann_lit list \<Rightarrow> _))) \<in>
    (list_assn nat_lit_assn_id)\<^sup>d *\<^sub>a nat_ann_lits_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_code_eq_get_maximum_level
  apply sepref_to_hoare
  by (sep_auto dest: entails_list_assn_eqD entails_list_mset_assn_eq_mset
      simp: mod_star_conv)

lemma is_Nil_hnr[sepref_fr_rules]:
  \<open>(return \<circ> is_Nil, RETURN o is_Nil) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply sep_auto
   apply (case_tac x; case_tac xi; auto)+
  done

lemma count_decided_hnr[sepref_fr_rules]:
  \<open>(return \<circ> count_decided, RETURN o count_decided) \<in> nat_ann_lits_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by sepref_to_hoare (sep_auto dest: entails_list_assn_eqD)

lemma list_assn_union_mset_list:
  assumes \<open>(aa, ba) \<Turnstile>
       list_assn (\<lambda>a c. \<up> (c = a)) b bi * list_assn (\<lambda>a c. \<up> (c = a)) a ai\<close>
  shows \<open> (aa, ba) \<Turnstile>
       list_assn (\<lambda>a c. \<up> (c = a)) b bi * list_assn (\<lambda>a c. \<up> (c = a)) a ai *
       list_assn (\<lambda>a c. \<up> (c = a)) (union_mset_list a b)
        (union_mset_list ai bi) *
       true\<close>
  using assms models_in_range[OF assms]
  by (sep_auto dest!: entails_list_assn_eqD simp: entails_def list_assn_same_emp
      elim!: mod_starE)


lemma union_mset_list_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo union_mset_list), uncurry (RETURN oo union_mset_list)) \<in>
     clause_ll_assn\<^sup>k *\<^sub>a clause_ll_assn\<^sup>k \<rightarrow>\<^sub>a clause_ll_assn\<close>
  by sepref_to_hoare (sep_auto simp: entails_def intro: list_assn_union_mset_list)

lemma list_assn_remove1:
  assumes \<open>(aa, ba) \<Turnstile> list_assn (\<lambda>a c. \<up> (c = a)) b bi * (\<lambda>a c. \<up> (c = a)) a ai\<close>
  shows \<open>(aa, ba) \<Turnstile> list_assn (\<lambda>a c. \<up> (c = a)) (remove1 a b) (remove1 ai bi) * true\<close>
proof -
  have [simp]: \<open>b = bi\<close> and [simp]: \<open>a = ai\<close>
    using assms
    by (auto dest!: entails_list_assn_eqD simp: entails_def list_assn_same_emp
      elim!: mod_starE)
  show ?thesis
    using models_in_range[OF assms] by (auto simp: list_assn_same_emp_id)
qed

lemma remove1_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo remove1), uncurry (RETURN oo remove1)) \<in>
     id_assn\<^sup>d *\<^sub>a (list_assn id_assn)\<^sup>d \<rightarrow>\<^sub>a list_assn id_assn\<close>
  by sepref_to_hoare (sep_auto simp: entails_def intro: list_assn_remove1)

(* TODO Move WB_More_Refinement *)
lemma is_Nil_is_empty[sepref_fr_rules]:
  \<open>(return o is_Nil, RETURN o Multiset.is_empty) \<in> (list_mset_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (rename_tac x xi)
    apply (case_tac x)
   by (sep_auto simp: Multiset.is_empty_def list_mset_assn_empty_Cons list_mset_assn_add_mset_Nil
      split: list.splits)+

lemma union_mset_list_Nil[simp]: \<open>union_mset_list [] bi = bi\<close>
  by (auto simp: union_mset_list_def)
term list_mset_rel term mset_rel

lemma union_mset_list_nat_lit_assn_hnr[sepref_fr_rules]:
  \<open>(uncurry (return \<circ>\<circ> union_mset_list), uncurry (RETURN \<circ>\<circ> op \<union>#))
  \<in> (list_mset_assn nat_lit_assn_id)\<^sup>k *\<^sub>a (list_mset_assn nat_lit_assn_id)\<^sup>k \<rightarrow>\<^sub>a list_mset_assn nat_lit_assn_id\<close>
  using union_mset_list_op_union_hnr .

sepref_definition skip_and_resolve_loop_l_impl is
  \<open>(skip_and_resolve_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding skip_and_resolve_loop_l_def option_is_empty conv_to_is_Nil is_empty_def[symmetric]
  skip_and_resolve_loop_inv_def mset_remove1[symmetric]
  maximum_level_code_eq_get_maximum_level[symmetric]
  apply (rewrite at \<open>If _ \<hole> _\<close> lms_fold_custom_empty)+
  apply (rewrite at \<open>_ = {#}\<close> Multiset.is_empty_def[symmetric])+
  apply (rewrite at \<open>\<not>_ \<and> \<not> is_decided _\<close> short_circuit_conv)
  apply (rewrite at \<open>\<not>_ \<and> Multiset.is_empty _\<close> short_circuit_conv)
  by sepref


sepref_register \<open>skip_and_resolve_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>
declare skip_and_resolve_loop_l_impl.refine[sepref_fr_rules]


subsubsection \<open>Backtrack\<close>

definition find_decomp_l_res :: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres" where
  \<open>find_decomp_l_res = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    do {
     let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
     let M1 = tl (the (bt_cut j M));
     RETURN M1
    })\<close>

lemma bt_cut_not_none2:
  assumes "no_dup M" and "i < count_decided M"
  shows "bt_cut i M \<noteq> None"
proof -
  obtain K M1 M2 where
    \<open>M = M2 @ Decided K # M1\<close> and \<open>get_level M K = Suc i\<close>
      using le_count_decided_decomp[OF assms(1)] assms(2) by auto
    then show ?thesis
      using bt_cut_not_none[OF assms(1), of M2 K M1 i] by auto
  qed

lemma find_decomp_l_res_le_find_decomp:
  fixes S' :: \<open>nat twl_st_l\<close> and M :: \<open>(nat, nat) ann_lits\<close> and N :: \<open>nat clauses_l\<close> and
    U :: nat and D :: \<open>nat cconflict_l\<close> and NP UP :: \<open>nat literal list list\<close> and
    WS :: \<open>nat list\<close> and Q :: \<open>nat literal list\<close> and L
  defines
    L: \<open>L \<equiv> lit_of (hd M)\<close> and
    S'_def: \<open>S' \<equiv> twl_st_of_ll (M, N, U, D, NP, UP, WS, Q)\<close>
  assumes
    T_def: \<open>T = ((M, N, U, D, NP, UP, WS, Q), L)\<close> and
    T'_def: \<open>T' = (S', L)\<close>
  assumes D: \<open>D \<noteq> None\<close> \<open>D \<noteq> Some []\<close> and
    ex_decomp: \<open>ex_decomp_of_max_lvl M (map_option mset D) L\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of None S')\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of None S')\<close> and
    ns_s: \<open>no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None S'))\<close> and
    M_not_empty: \<open>M \<noteq> []\<close>
 shows \<open>uncurry find_decomp_l_res T \<le> \<Down> Id (uncurry find_decomp T')\<close>
proof -
  have S': \<open>S' = (M, N, U, map_option mset D, mset `# mset NP, mset `# mset UP, mset WS, mset Q)\<close>
    using S'_def by auto
  have n_d: \<open>no_dup M\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (simp add: cdcl\<^sub>W_restart_mset_state S')

  obtain D' where D'[simp]: \<open>D = Some D'\<close>
    using D by auto
  obtain M1'' M2'' K'' where
    decomp_K'': \<open>(Decided K'' # M1'', M2'') \<in> set (get_all_ann_decomposition M)\<close>
    \<open>get_level M K'' = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset D')))\<close>
    using ex_decomp unfolding L[symmetric] ex_decomp_of_max_lvl_def by auto
  then have lev_max: \<open>get_maximum_level M (mset (remove1 (-L) D')) < count_decided M\<close>
    using count_decided_ge_get_level[of M K''] L by auto
  have hd_converts_L: \<open>lit_of (hd (convert_lits_l N M)) = L\<close>
    using M_not_empty unfolding L by (cases M) auto
  have lev_L: \<open>get_level M L = count_decided M\<close>
    using M_not_empty L by (cases M) auto

  have \<open>conflicting (state\<^sub>W_of (twl_st_of None S')) = Some (mset D')\<close>
    by (auto simp: twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset_state S')
  then have uhd_D': \<open>- L \<in> set D'\<close>
    using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
        \<open>state\<^sub>W_of (twl_st_of None S')\<close>] D ns_s struct_invs stgy_invs
    by (auto simp: cdcl\<^sub>W_restart_mset_state S' hd_converts_L twl_struct_invs_def
        twl_stgy_invs_def)

  have \<open>-L \<in># mset D'\<close>
    using uhd_D' L M_not_empty by (cases M) simp_all
  with multi_member_split[OF this]
  have False if \<open>find_level_decomp M (the D) [] (count_decided M) = None\<close>
    using find_level_decomp_none[OF that, of \<open>-L\<close> \<open>remove1 (-L) D'\<close>] lev_max
    unfolding S' by (auto dest!: simp: lev_L)
  then obtain K j where
    Kj: \<open>find_level_decomp M (the D) [] (count_decided M) = Some (K, j)\<close>
    by (cases \<open>find_level_decomp M (the D) [] (count_decided M)\<close>) auto
  then have
    \<open>K \<in> set D'\<close> and
    j: \<open>get_maximum_level M (mset (remove1 K D')) = j\<close> and
    \<open>get_level M K = count_decided M\<close>
    using find_level_decomp_some[OF Kj] by simp_all
  have KL: \<open>K = -L\<close>
    by (metis \<open>K \<in> set D'\<close> \<open>\<exists>A. mset D' = add_mset (- L) A\<close> \<open>get_level M K = count_decided M\<close>
        add_mset_remove_trivial get_maximum_level_ge_get_level leD lev_max member_add_mset
        mset_remove1 set_mset_mset)
  have j_le_M: \<open>j < count_decided M\<close>
    unfolding j[symmetric] KL using lev_max by simp
  have bt_cut: \<open>bt_cut j M \<noteq> None\<close>
    apply (rule bt_cut_not_none2)
    using n_d apply (simp; fail)
    using j_le_M by simp
  then obtain M1 where M1: \<open>bt_cut j M = Some M1\<close>
    by auto
  show ?thesis
    using bt_cut_some_decomp[OF n_d M1]
      bt_cut_in_get_all_ann_decomposition[OF n_d M1]
    unfolding Kj find_decomp_l_res_def find_decomp_def split
      Let_def M1 S' option.sel snd_conv KL uncurry_def T_def T'_def
    by (fastforce simp: find_decomp_l_res_def find_decomp_def S' KL j[symmetric])
qed

lemma find_decomp_l_res_find_decomp:
  \<open>(uncurry find_decomp_l_res, uncurry find_decomp) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal). L = lit_of (hd M) \<and> D \<noteq> None \<and> D \<noteq> Some {#} \<and>
       ex_decomp_of_max_lvl M D L \<and>
       twl_stgy_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
       twl_struct_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
       no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None (M, N, U, D, NP, UP, WS, Q))) \<and>
      M \<noteq> []]\<^sub>f
    {((S'::twl_st_ll), (S::nat twl_st_l)). S = twl_st_of_ll S'} \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  (is \<open>_ \<in> [\<lambda>(S, L). ?P S L]\<^sub>f _ \<rightarrow> _\<close>)
proof -
  define P where \<open>P \<equiv> ?P\<close>
  {
    fix S and L L' :: \<open>nat literal\<close> and T T' S'
    assume P: \<open>?P S L\<close> and S: \<open>S = twl_st_of_ll T\<close> and T': \<open>T' = (T, L)\<close> and S' : \<open>S' = (S, L)\<close>

    obtain M N U D NP UP WS Q where
      T: \<open>T = (M, N, U, D, NP, UP, WS, Q)\<close>
      by (cases T)

    have D: \<open>D \<noteq> None\<close> \<open>the D \<noteq> []\<close>
      using P unfolding S T
      by auto
    have \<open>uncurry find_decomp_l_res T' \<le> \<Down> Id (uncurry find_decomp S')\<close>
      apply (rule find_decomp_l_res_le_find_decomp[of T' M N U D NP UP WS Q S'])
      using P S D by (auto simp: T T' S')
  } note H = this[unfolded P_def[symmetric]]
  show ?thesis
    unfolding P_def[symmetric]
    unfolding fref_def nres_rel_def ex_decomp_of_max_lvl_def
      in_pair_collect_simp
    apply (intro allI impI)
    subgoal for T' S'
      apply (cases T')
      apply (rule H[of \<open>fst S'\<close> \<open>snd S'\<close> \<open>fst T'\<close> T' S'])
      by (auto intro!: H)
    done
qed

definition find_decomp_l :: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits Heap" where
  \<open>find_decomp_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    do {
     let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
     let M1 = tl (the (bt_cut j M));
     return M1
    })\<close>

abbreviation twl_st_ll_assn :: \<open>twl_st_ll \<Rightarrow> twl_st_ll \<Rightarrow> assn\<close> where
\<open>twl_st_ll_assn \<equiv>
 nat_lits_trail_assn *assn clauses_ll_assn *assn nat_assn *assn
 option_assn clause_ll_assn *assn
 clauses_ll_assn *assn
 clauses_ll_assn *assn
 clauses_to_update_ll_assn *assn
 clause_ll_assn
\<close>

lemma find_decomp_l_find_decomp_l_res: \<open>(uncurry find_decomp_l, uncurry find_decomp_l_res) \<in>
   twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a nat_ann_lits_assn\<close>
proof -
  {
    fix M :: "(nat, nat) ann_lits" and N :: "nat clauses_l" and D :: "nat clause_l option" and
      NP UP :: "nat clauses_l" and U :: "nat list" and WS :: "nat set" and P :: "nat clause_l" and
      M'' :: "(nat, nat) ann_lits" and N'' :: "nat clauses_l" and D'' :: "nat clause_l option" and
      NP'' UP'' :: "nat clauses_l" and WS'' :: "nat list" and P'' :: "nat clause_l" and
      ab :: Heap.heap
    assume a1: "(ab, WS) \<Turnstile> list_assn (\<lambda>a c. \<up> (c = a)) M M'' * list_assn (list_assn (\<lambda>a c. \<up> (c = a))) N N'' * option_assn (list_assn (\<lambda>a c. \<up> (c = a))) D D'' * list_assn (list_assn (\<lambda>a c. \<up> (c = a))) NP NP'' * list_assn (list_assn (\<lambda>a c. \<up> (c = a))) UP UP'' * list_assn (\<lambda>a c. \<up> (c = a)) U WS'' * list_assn (\<lambda>a c. \<up> (c = a)) P P''"
    obtain pp :: "assn \<Rightarrow> assn \<Rightarrow> Heap.heap \<times> nat set" and ppa :: "assn \<Rightarrow> assn \<Rightarrow> Heap.heap \<times> nat set" where
      pp: "\<forall>x1 x2. (\<exists>v3 v4. v3 \<Turnstile> x2 \<and> v4 \<Turnstile> x1) = (pp x1 x2 \<Turnstile> x2 \<and> ppa x1 x2 \<Turnstile> x1)"
      by moura
    then have f3: "P = P''"
      using a1 entails_list_assn_eqD by (blast dest: mod_starD)
    have f4: "U = WS''"
      using a1 entails_list_assn_eqD by (blast dest: mod_starD)
    have f5: "\<forall>lss lssa p. \<not> p \<Turnstile> list_assn (list_assn (\<lambda>l la. \<up> ((la::nat literal) = l))) lss lssa \<or> lss = lssa"
      using entails_list_assn_list_assn_eqD by blast
    then have f6: "UP = UP''"
      using a1 by (blast dest: mod_starD)
    have f7: "NP = NP''"
      using f5 a1 by (blast dest: mod_starD)
    have f8: "pp (option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D'') (list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'') \<Turnstile> list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'' \<and> ppa (option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D'') (list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'') \<Turnstile> option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D''"
      using pp a1 by (fast dest: mod_starD)
    then have f9: "M = M''"
      by (blast dest: mod_starD entails_list_assn_eqD)
    have f10: "N = N''"
      using f8 f5 by (blast dest: mod_starD)
    have "pp (option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D'') (list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'') \<Turnstile> list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'' \<and> ppa (option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D'') (list_assn (\<lambda>a aa. \<up> (aa = a)) M M'' * list_assn (list_assn (\<lambda>l la. \<up> (la = l))) N N'') \<Turnstile> option_assn (list_assn (\<lambda>l la. \<up> (la = l))) D D''"
      using pp a1 by (fast dest: mod_starD)
    then have "(ab, WS) \<Turnstile> list_assn (\<lambda>a aa. \<up> (aa = a)) (tl (the (bt_cut (snd (the (find_level_decomp M (the D) [] (count_decided M)))) M))) (tl (the (bt_cut (snd (the (find_level_decomp M'' (the D'') [] (count_decided M'')))) M''))) * true"
      using f10 f9 f7 f6 f4 f3 a1 by (metis (no_types) entails_option_assn_assn_eqD
          list_assn_list_assn_same_emp_id list_assn_same_emp_id mod_star_trueI
          mult.right_neutral option_assn_same_emp)
  }
  then show ?thesis
    unfolding find_decomp_l_def find_decomp_l_res_def
    by sepref_to_hoare (sep_auto simp: entails_def)
qed

lemma set_eq_twl_st_of_ll:
  \<open>{(S', S). S = twl_st_of_ll S'} = Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r\<langle>list_mset_rel\<rangle>option_rel \<times>\<^sub>r
     {(NP', NP). NP = mset `# mset NP'} \<times>\<^sub>r {(NP', NP). NP = mset `# mset NP'} \<times>\<^sub>r list_mset_rel \<times>\<^sub>r list_mset_rel\<close>
  by (auto simp: list_mset_rel_def br_def option_rel_def) (case_tac ac, auto)

lemma list_assn_id_id_assn: \<open>list_assn (\<lambda>a c. \<up> (c = a)) b c = id_assn b c\<close>
  by (induction b arbitrary: c) (case_tac c; auto simp: pure_def; fail)+

lemma hr_comp_list_mst_rel_clause_l_assn: \<open>hr_comp clause_ll_assn list_mset_rel = clause_l_assn\<close>
proof -
  have [abs_def, simp]: \<open>pure_assn_raw a h = (snd h = {} \<and> a)\<close> for a h
    by (cases h) auto
  have H: \<open>(\<exists>\<^sub>Ab. \<up> (c = b \<and> a = mset b)) = \<up> (a = mset c)\<close> for a c
    unfolding ex_assn_def
    by (subst (2) pure_assn_def) (auto simp: )
  have H': \<open>(\<exists>xs. mset xs = mset c \<and> mset xs = a) \<longleftrightarrow> (a = mset c)\<close> for a c
    by auto
  have \<open>(\<exists>\<^sub>Ab. \<up> (c = b \<and> a = mset b)) = \<up> (\<exists>xs. mset xs = mset c \<and> mset xs = a)\<close> for a c
    unfolding H H' ..
  then show ?thesis
    apply (auto simp: hr_comp_def[abs_def] list_mset_assn_def)
    apply (auto simp: pure_def list_mset_rel_def mset_rel_def rel2p_def[abs_def]
        p2rel_def[abs_def] rel_mset_def[abs_def] list_mset_rel_def mset_rel_def rel_mset_def[abs_def]
        rel2p_def[abs_def] list.rel_eq p2rel_def refine_rel_defs recomp_set_eq_simp
        list_assn_id_id_assn
        intro!: ext)
    done
qed

thm br_comp_alt[of _ _ Id, simplified]
lemma hr_comp_clauses_ll_assn_clauses_l_ass:
  \<open>hr_comp clauses_ll_assn {(NP', NP). NP = mset `# mset NP'} = clauses_l_assn\<close>
proof -
  have Id: \<open>Id = the_pure id_assn\<close>
    by auto
  have [simp]: \<open>list_mset_rel O \<langle>Id\<rangle>mset_rel = list_mset_rel\<close>
    by (auto simp: list_mset_rel_def mset_rel_def rel_mset_def[abs_def]
        rel2p_def[abs_def] list.rel_eq p2rel_def refine_rel_defs)
  have [abs_def, simp]: \<open>pure_assn_raw a h = (snd h = {} \<and> a)\<close> for a h
    by (cases h) auto
  have H: \<open>(\<exists>\<^sub>Ab. \<up> (c = b \<and> a = mset `# mset b)) = \<up> (a = mset `# mset c)\<close> for a c
    unfolding ex_assn_def
    by (subst (2) pure_assn_def) auto
  have in_br_mset: \<open>(a, aa) \<in> br mset (\<lambda>_. True) \<longleftrightarrow> mset a = aa\<close> for a aa
    unfolding br_comp_alt[of _ _ Id, simplified] by auto

  have [iff]: \<open>list_all2 (\<lambda>x y. (x, y) \<in> br mset (\<lambda>_. True)) xs ys \<longleftrightarrow> map mset xs = ys\<close> for xs ys
    by (induction xs arbitrary: ys) (case_tac ys; auto simp: in_br_mset; fail)+
  show ?thesis
    apply (auto simp: hr_comp_def[abs_def] list_mset_assn_def)
    apply (auto simp: pure_def list_mset_rel_def mset_rel_def rel2p_def[abs_def]
        p2rel_def[abs_def] rel_mset_def[abs_def] H
        br_comp_alt list_assn_id_id_assn[abs_def]
        intro!: ext)
    done
qed

lemma hr_comp_clauses_to_update_ll_assn_clauses_to_update_l_assn:
  \<open>hr_comp clauses_to_update_ll_assn list_mset_rel = clauses_to_update_l_assn\<close>
proof -
  have [abs_def, simp]: \<open>pure_assn_raw a h = (snd h = {} \<and> a)\<close> for a h
    by (cases h) auto
  have H: \<open>(\<exists>\<^sub>Ab. \<up> (c = b \<and> mset b = a)) = \<up> (mset c = a)\<close> for a c
    unfolding ex_assn_def
    by (subst (2) pure_assn_def) auto
  have in_br_mset: \<open>(a, aa) \<in> br mset (\<lambda>_. True) \<longleftrightarrow> mset a = aa\<close> for a aa
    unfolding br_comp_alt[of _ _ Id, simplified] by auto

  show ?thesis
    apply (auto simp: hr_comp_def[abs_def] list_mset_assn_def)
    apply (auto simp: pure_def list_mset_rel_def mset_rel_def rel2p_def[abs_def]
        p2rel_def[abs_def] rel_mset_def[abs_def] H list.rel_eq
        br_comp_alt list_assn_id_id_assn[abs_def] in_br_mset
        intro!: ext)
    done
qed

lemma hrp_comp_twl_st_ll_assn_twl_st_of_ll: \<open>hrp_comp (twl_st_ll_assn\<^sup>d)
     {(S', S). S = twl_st_of_ll S'} =
    (twl_st_l_assn, invalid_assn twl_st_l_assn)\<close>
  unfolding set_eq_twl_st_of_ll
  by (auto simp: hrp_comp_def hr_comp_def hr_comp_list_mst_rel_clause_l_assn hr_comp_invalid
      hr_comp_clauses_ll_assn_clauses_l_ass hr_comp_clauses_to_update_ll_assn_clauses_to_update_l_assn)

lemma find_decomp_l_hnr[sepref_fr_rules]:
  \<open>(uncurry find_decomp_l, uncurry find_decomp) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal). L = lit_of (hd M) \<and> D \<noteq> None \<and> D \<noteq> Some {#} \<and>
      ex_decomp_of_max_lvl M D L \<and>
      twl_stgy_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
      twl_struct_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
      no_step cdcl\<^sub>W_restart_mset.skip (state\<^sub>W_of (twl_st_of None (M, N, U, D, NP, UP, WS, Q))) \<and>
      M \<noteq> []]\<^sub>a
      twl_st_l_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow> nat_ann_lits_assn\<close>
  apply (rule subst[of \<open>comp_PRE ({(S', S). S = twl_st_of_ll S'} \<times>\<^sub>r Id)
       (\<lambda>((M, N, U, D, NP, UP, WS, Q), L).
           L = lit_of (hd M) \<and>
           D \<noteq> None \<and>
           D \<noteq> Some {#} \<and>
           ex_decomp_of_max_lvl M D L \<and>
           twl_stgy_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
           twl_struct_invs (twl_st_of None (M, N, U, D, NP, UP, WS, Q)) \<and>
           (\<forall>S'. \<not> cdcl\<^sub>W_restart_mset.skip
                     (state\<^sub>W_of
                       (twl_st_of None (M, N, U, D, NP, UP, WS, Q)))
                     S') \<and>
           M \<noteq> [])
       (\<lambda>_ _. True)
       (\<lambda>_. True)\<close> _ \<open>\<lambda>c. (uncurry find_decomp_l, uncurry find_decomp) \<in> [c]\<^sub>a _ \<rightarrow> _\<close>])
  subgoal by (auto simp: comp_PRE_def; fail)[]
  apply (rule subst[of \<open>hr_comp nat_lits_trail_assn Id\<close> _
        \<open>\<lambda>c. (uncurry find_decomp_l, uncurry find_decomp) \<in> [_]\<^sub>a _ \<rightarrow> c\<close>])
  subgoal by (auto simp: ; fail)[]
  apply (rule subst[of \<open>hrp_comp (twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k)
                       ({(S', S). S = twl_st_of_ll S'} \<times>\<^sub>r
                        Id)\<close> _
        \<open>\<lambda>c. (uncurry find_decomp_l, uncurry find_decomp) \<in> [_]\<^sub>a c \<rightarrow> _\<close>])
  subgoal
    unfolding prod_hrp_comp hrp_comp_twl_st_ll_assn_twl_st_of_ll
    by (auto simp: hrp_comp_twl_st_ll_assn_twl_st_of_ll; fail)[]

  supply [[unify_trace_failure]]
  apply (rule hfref_compI_PRE_aux[OF find_decomp_l_find_decomp_l_res find_decomp_l_res_find_decomp])
  done

definition find_lit_of_max_level_l :: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> nat literal Heap" where
  \<open>find_lit_of_max_level_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    return (the (find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (-L) (mset (the D)))) (the D))))\<close>

definition find_lit_of_max_level_l_res :: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> nat literal nres" where
  \<open>find_lit_of_max_level_l_res = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    RETURN (the (find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (-L) (mset (the D)))) (the D))))\<close>

sepref_register "find_lit_of_max_level :: nat twl_st_l \<Rightarrow> nat literal \<Rightarrow> nat literal nres"
sepref_register "find_decomp :: nat twl_st_l \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres"

lemma in_remove1_msetI: \<open>x \<noteq> a \<Longrightarrow> x \<in># M \<Longrightarrow> x \<in># remove1_mset a M\<close>
  by (simp add: in_remove1_mset_neq)

lemma find_lit_of_max_level_l_res_find_lit_of_max_level:
  \<open>(uncurry find_lit_of_max_level_l_res, uncurry find_lit_of_max_level) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L). D \<noteq> None \<and> D \<noteq> Some {#} \<and> size (the D) > 1 \<and>
      get_level M L > get_maximum_level M (remove1_mset (-L) (the D))]\<^sub>f
    {(S', S). S = twl_st_of_ll S'} \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
proof -
  { fix C and M :: \<open>(nat, nat) ann_lits\<close> and L :: \<open>nat literal\<close> and D' :: \<open>nat literal list\<close>
    assume \<open>length D' > Suc 0\<close>
    then have \<open>remove1_mset (- L) (mset D') \<noteq> {#}\<close>
      by (cases D'; cases \<open>tl D'\<close>) (auto simp: remove1_mset_add_mset_If)
    then have \<open>\<exists>L' \<in> set D'. get_level M L' = get_maximum_level M (remove1_mset (- L) (mset D'))\<close>
      using get_maximum_level_exists_lit_of_max_level[of \<open>remove1_mset (- L) (mset D')\<close> M]
      by (auto dest!: in_diffD)
    then have L: \<open>find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (- L) (mset D'))) D' \<noteq> None\<close>
      by (meson find_None_iff)
    let ?L = \<open>(find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (- L) (mset D'))) D')\<close>

    have \<open>the ?L \<in> set D'\<close> and
      \<open>get_level M (the ?L) = get_maximum_level M (remove1_mset (- L) (mset D'))\<close>
      using L by (auto dest: find_SomeD)
  }
  note H_D = this

  show ?thesis
    unfolding find_lit_of_max_level_l_res_def find_lit_of_max_level_def
    apply (auto simp: fref_def nres_rel_def simp: H_D intro!: in_remove1_msetI)
    by (metis H_D(2) get_level_uminus less_irrefl)
qed

lemma find_lit_of_max_level_l_find_lit_of_max_level:
  \<open>(uncurry find_lit_of_max_level_l, uncurry find_lit_of_max_level_l_res) \<in>
    twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn_id\<close>
  unfolding find_lit_of_max_level_l_def find_lit_of_max_level_l_res_def
  by sepref_to_hoare
   (sep_auto elim!: mod_starE dest!: entails_list_assn_eqD entails_option_assn_assn_eqD)


lemma find_lit_of_max_level_l_hnr[sepref_fr_rules]:
  \<open>(uncurry find_lit_of_max_level_l, uncurry find_lit_of_max_level) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal).
     D \<noteq> None \<and> D \<noteq> Some {#} \<and> 1 < size (the D) \<and>
     get_level M L > get_maximum_level M (remove1_mset (-L) (the D))]\<^sub>a
    twl_st_l_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k \<rightarrow> nat_lit_assn_id\<close>
proof -
  have pre: \<open>comp_PRE ({(S', S). S = twl_st_of_ll S'} \<times>\<^sub>r Id)
     (\<lambda>((M, N, U, D, NP, UP, WS, Q), L).
         D \<noteq> None \<and> D \<noteq> Some {#} \<and> 1 < size (the D) \<and>
        get_level M L > get_maximum_level M (remove1_mset (-L) (the D)))
     (\<lambda>_ _. True)
     (\<lambda>_. True) = (\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal).
     D \<noteq> None \<and> D \<noteq> Some {#} \<and> 1 < size (the D) \<and>
     get_level M L > get_maximum_level M (remove1_mset (-L) (the D)))\<close>
    by (auto simp: comp_PRE_def)

  have args: \<open>hrp_comp (twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k)
                     ({(S', S). S = twl_st_of_ll S'} \<times>\<^sub>r
                      Id) = twl_st_l_assn\<^sup>d *\<^sub>a nat_lit_assn_id\<^sup>k\<close>
    unfolding prod_hrp_comp hrp_comp_twl_st_ll_assn_twl_st_of_ll
    by simp
  have out: \<open>hr_comp nat_lit_assn_id Id = nat_lit_assn_id\<close>
    by simp
  show ?thesis
    using hfref_compI_PRE_aux [OF find_lit_of_max_level_l_find_lit_of_max_level
      find_lit_of_max_level_l_res_find_lit_of_max_level]
    unfolding pre args out by assumption
qed

sepref_register \<open>add_mset_list :: nat literal list \<Rightarrow> nat clauses \<Rightarrow> nat clauses\<close>

lemma add_mset_list_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo Cons), uncurry (RETURN oo add_mset_list)) \<in>
    clause_ll_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>d \<rightarrow>\<^sub>a clauses_l_assn\<close>
proof -
  {
    fix aa :: Heap.heap and ba :: \<open>nat set\<close> and a :: \<open>nat clause_l\<close> and b :: \<open>nat clauses\<close> and
      bi :: \<open>nat clauses_l\<close> and ai
    assume \<open>(aa, ba) \<Turnstile>
       list_mset_assn (list_mset_assn (\<lambda>a c. \<up> (c = a))) b bi *
       list_assn (\<lambda>a c. \<up> (c = a)) a ai\<close>
    then have \<open>
       Assertions.models (aa, ba)
       (list_mset_assn (list_mset_assn (\<lambda>a c. \<up> (c = a))) (add_mset (mset a) b)
        (ai # bi) * true)\<close>
      by (metis (no_types) entails_list_assn_eqD entails_list_mset_assn_list_mset_assn_eq_mset
          image_mset_add_mset list_assn_same_emp_id list_mset_assn_list_mset_assn_id_mset_mset_emp
          mod_star_conv mod_star_trueI mset.simps(2) mult.right_neutral)
  }
  then show ?thesis
  unfolding add_mset_list.simps
  by sepref_to_hoare (sep_auto simp: entails_def)
qed

lemma list_of_mset_hnr[sepref_fr_rules]:
  \<open>(return o id, list_of_mset) \<in> (clause_l_assn)\<^sup>k \<rightarrow>\<^sub>a clause_ll_assn\<close>
proof -
  have I: \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
    by (auto simp: pure_def)
  have [simp]: \<open> (\<lambda>x y. (x, y) \<in> the_pure (\<lambda>a c. \<up> (c = a))) = op =\<close>
    apply (intro ext)
    unfolding I the_pure_pure by simp
  have [simp]: \<open>list_assn (\<lambda>a c. \<up> (c = a)) xi xi = emp\<close> for xi
    by (induction xi) auto
  show ?thesis
    apply sepref_to_hoare
    apply sep_auto
     apply (subgoal_tac \<open>RETURN xi \<le> list_of_mset x\<close>)
      apply simp
    by (sep_auto simp: list_of_mset_def list_mset_assn_def mset_rel_def p2rel_def
        list_mset_rel_def rel2p_def[abs_def] br_def rel_mset_def list.rel_eq Collect_eq_comp)+
qed

lemma length_size[sepref_fr_rules]:
  \<open>(return o length, RETURN o size) \<in> (list_mset_assn R)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  by (sepref_to_hoare)
    (sep_auto simp: list_of_mset_def list_mset_assn_def mset_rel_def p2rel_def
        list_mset_rel_def rel2p_def[abs_def] br_def rel_mset_def list.rel_eq Collect_eq_comp
        size_mset[symmetric]
        simp del: size_mset
        dest!: list_all2_lengthD)

sepref_definition backtrack_l_impl
  is \<open>(backtrack_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding backtrack_l_def
  apply (rewrite at \<open>add_mset _ \<hole>\<close> lms_fold_custom_empty)+
  unfolding skip_and_resolve_loop_inv_def mset_remove1[symmetric]
    HOL_list.fold_custom_empty
  supply [[goals_limit=1]]
  by sepref (* slow *)

sepref_register \<open>(backtrack_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
declare backtrack_l_impl.refine[sepref_fr_rules]


subsubsection \<open>Decide\<close>

definition find_unassigned_lit_cls_l ::
  "'a literal list \<Rightarrow> ('a, 'b) ann_lits \<Rightarrow> (nat \<times> 'a literal option) nres" where
  \<open>find_unassigned_lit_cls_l C M =
    WHILE\<^sub>T\<^bsup>\<lambda>(i, v). (\<forall>j<i. defined_lit M (C!j)) \<and> i \<le> length C \<and>
      (v \<noteq> None \<longrightarrow> (undefined_lit M (the v) \<and> (\<forall>j<i. defined_lit M (C!j)) \<and>
        atm_of (the v) \<in> atms_of (mset C)) \<and> the v = C!i)\<^esup>
      (\<lambda>(i, v). v = None \<and> i < length C)
      (\<lambda>(i, _). do {
        ASSERT(no_dup M);
        ASSERT(i < length C);
        val_L' \<leftarrow> RETURN (valued M (C!i));
        if val_L' = None then do {RETURN (i, Some (C!i))}
        else do {RETURN (i+1, None)}
      })
     (0, None)\<close>

lemma find_unassigned_lit_cls_l_spec:
  assumes \<open>no_dup M\<close>
  shows
    \<open>find_unassigned_lit_cls_l C M \<le> SPEC(\<lambda>(i, v). (v = None \<longrightarrow> (\<forall>j < length C. defined_lit M (C!j))) \<and>
      (v \<noteq> None \<longrightarrow> undefined_lit M (the v) \<and> the v = C!i \<and> atm_of (the v) \<in> atms_of (mset C)))\<close>
  using assms unfolding find_unassigned_lit_cls_l_def
  by (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, v). Suc (length C) - i - If (v \<noteq> None) 1 0)\<close>])
     ((auto simp: valued_def Decided_Propagated_in_iff_in_lits_of_l split: if_splits
        simp: less_Suc_eq; fail))+

definition find_unassigned_lit_clss_l :: \<open>'v twl_st_l \<Rightarrow> (nat \<times> 'v literal option) nres\<close>  where
  \<open>find_unassigned_lit_clss_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q).
    WHILE\<^sub>T\<^bsup>\<lambda>(i, v). ((\<forall>j<i. j > 0 \<longrightarrow> (\<forall>k<length (N!j). defined_lit M (N!j!k)))) \<and>
        (v \<noteq> None \<longrightarrow> undefined_lit M (the v) \<and> atm_of (the v) \<in> atms_of_mm (mset `# mset (tl N))) \<and> i \<le> length N \<and> i \<ge> 1\<^esup>
      (\<lambda>(i, v). v = None \<and> i < length N)
      (\<lambda>(i::nat, v::'v literal option). do {
        ASSERT(i < length N);
        ASSERT(i > 0);
        ASSERT(no_dup M);
        (k, v) \<leftarrow> find_unassigned_lit_cls_l (N!i) M;
        if v = None then do {RETURN (i+1, None)}
        else do {RETURN (i, v)}
      })
     (1, None))\<close>
declare find_unassigned_lit_cls_l_spec[THEN order_trans, refine_vcg]

lemma find_unassigned_lit_clss_l_spec:
  assumes \<open>no_dup M\<close> and \<open>length N > 0\<close>
  shows
    \<open>find_unassigned_lit_clss_l (M, N, U, D, NP, UP, WS, Q) \<le>
        SPEC(\<lambda>(i, v). (v = None \<longrightarrow> (\<forall>j<length N. j > 0 \<longrightarrow> (\<forall>k<length (N!j). defined_lit M (N!j!k)))) \<and>
           (v \<noteq> None \<longrightarrow> undefined_lit M (the v) \<and>
               atm_of (the v) \<in> atms_of_mm (mset `# mset (tl N))) \<and> i > 0)\<close>
proof -
  have [intro]: \<open>x1 < length N \<Longrightarrow> 0 < x1 \<Longrightarrow>
     atm_of (N ! x1 ! aha) = atm_of x \<Longrightarrow> x \<in> set (N ! x1) \<Longrightarrow>
     atm_of x \<in> atms_of_ms (mset ` set (tl N))\<close>
    for x1 aha x
    unfolding tl_drop_def One_nat_def atms_of_ms_def
    by simp (meson Suc_leI atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_set_drop_conv_nth)
  show ?thesis
    using assms unfolding find_unassigned_lit_clss_l_def
  by (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, v). Suc (length N) - i - If (v \<noteq> None) 1 0)\<close>])
    (auto simp: less_Suc_eq)
qed

definition find_unassigned_lit_l :: \<open>'v twl_st_l \<Rightarrow> 'v literal option nres\<close>  where
  \<open>find_unassigned_lit_l S =  do {
    (i, v) \<leftarrow> find_unassigned_lit_clss_l S;
    RETURN v
  }\<close>
declare find_unassigned_lit_cls_l_spec[THEN order_trans, refine_vcg]

declare find_unassigned_lit_clss_l_spec[THEN order_trans, refine_vcg]

lemma find_unassigned_lit_l_spec:
  assumes
    struct_inv: \<open>twl_struct_invs (twl_st_of None S)\<close>and
    stgy_inv: \<open>twl_stgy_invs (twl_st_of None S)\<close> and
    add_invs: \<open>additional_WS_invs S\<close> and
    D: \<open>get_conflict_l S = None\<close>
  shows \<open>find_unassigned_lit_l S \<le> find_unassigned_lit S\<close>
proof -
  obtain M N U D NP UP WS Q where
    S: \<open>S = (M, N, U, None, NP, UP, WS, Q)\<close>
    using D by (cases S) auto
  have [simp]: \<open>(\<lambda>x. mset (take 2 x) + mset (drop 2 x)) = mset\<close>
    unfolding mset_append[symmetric] append_take_drop_id ..
  have learned_in_init: \<open>atms_of_mm
     (learned_clss (state\<^sub>W_of (twl_st_of None S)))
    \<subseteq> atms_of_mm
        (init_clss (state\<^sub>W_of (twl_st_of None S)))\<close> and
    unit_inv: \<open>unit_clss_inv (twl_st_of None S)\<close>
    using struct_inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.no_strange_atm_def by fast+
  have n_d: \<open>no_dup M\<close>
    using struct_inv unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: S cdcl\<^sub>W_restart_mset_state)
  have length_N_ge_0: \<open>length N > 0\<close>
    using add_invs by (auto simp: additional_WS_invs_def S)
  have \<open>atm_of y \<in> atms_of_ms (mset ` set (take U (tl N)))\<close>
    if undef: \<open>undefined_lit M y\<close> and \<open>atm_of y \<in> atms_of_ms (mset ` set (tl N))\<close> for y
  proof -
    have \<open>atm_of y \<notin> atms_of_mm NP\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain C where \<open>C \<in># NP\<close> and y_in_C: \<open>atm_of y \<in> atms_of C\<close>
        by (auto simp: S atms_of_ms_def)
      then obtain L where \<open>C = {#L#}\<close> and \<open>L \<in> lits_of_l M\<close>
        using unit_inv undef by (auto simp: S atms_of_ms_def)
      then show False
        using y_in_C undef by (auto simp: atm_of_eq_atm_of Decided_Propagated_in_iff_in_lits_of_l)
    qed
    moreover have \<open>atms_of_ms (mset ` set (drop (Suc U) N)) \<subseteq> atms_of_ms
        (mset ` set (take U (tl N))) \<union>
       atms_of_mm NP\<close>
      using that learned_in_init
      apply (subst (asm) append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
      apply (subst (asm) set_append)
      by (auto simp: cdcl\<^sub>W_restart_mset_state S image_Un)
    ultimately have \<open>atm_of y \<in> atms_of_ms (mset ` set (drop U (tl N))) \<Longrightarrow>
      atm_of y \<in> atms_of_ms (mset ` set (take U (tl N)))\<close>
      by (metis (no_types, lifting) UnE drop_Suc subsetCE)
    then show ?thesis
      using that learned_in_init
      apply (subst (asm)(2) append_take_drop_id[of \<open>U\<close> \<open>tl N\<close>, symmetric])
      apply (subst (asm) set_append)
      by (auto simp: cdcl\<^sub>W_restart_mset_state S image_Un)
  qed
  moreover have \<open>\<not>(\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))\<close>
    if \<open>\<forall>j<length N. 0 < j \<longrightarrow> (\<forall>k<length (N ! j). defined_lit M (N ! j ! k))\<close>
  proof (rule ccontr)
    assume \<open>\<not> ?thesis\<close>
    then obtain L where
      \<open>undefined_lit M L\<close> and
      \<open>atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N)))\<close>
      by blast
    moreover have \<open>\<forall>C \<in> set (take U (tl N)). (\<forall>L \<in> set C. defined_lit M L)\<close>
      using that unfolding tl_drop_def all_set_conv_nth
      by auto
    ultimately show False
        by (auto simp: atms_of_ms_def atm_of_eq_atm_of)
  qed
  ultimately show ?thesis
    using n_d length_N_ge_0 unfolding find_unassigned_lit_l_def find_unassigned_lit_def S
    by refine_vcg auto
qed

sepref_definition find_unassigned_lit_l_impl is find_unassigned_lit_l
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a option_assn nat_lit_assn_id\<close>
  unfolding find_unassigned_lit_l_def find_unassigned_lit_clss_l_def
    find_unassigned_lit_cls_l_def
  by sepref

sepref_register \<open>find_unassigned_lit_l :: nat twl_st_l \<Rightarrow> nat literal option nres\<close>

lemma find_unassigned_lit_l_find_unassigned_lit:
  \<open>(find_unassigned_lit_l, find_unassigned_lit) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
       additional_WS_invs S \<and> get_conflict_l S = None]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle> nres_rel\<close>
  using find_unassigned_lit_l_spec by (fastforce simp: fref_def nres_rel_def simp del: twl_st_of.simps)

lemma find_unassigned_lit_l_impl_find_unassigned_lit_l[sepref_fr_rules]:
  \<open>(find_unassigned_lit_l_impl, find_unassigned_lit) \<in>
    [\<lambda>S.
       twl_struct_invs (twl_st_of None S) \<and>
       twl_stgy_invs (twl_st_of None S) \<and>
       additional_WS_invs S \<and> get_conflict_l S = None]\<^sub>a
    twl_st_l_assn\<^sup>d \<rightarrow> option_assn nat_lit_assn_id\<close>
proof -
  have pre: \<open>comp_PRE (Id \<times>\<^sub>r
        Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)
       (\<lambda>S. twl_struct_invs (twl_st_of None S) \<and>
             twl_stgy_invs (twl_st_of None S) \<and>
             additional_WS_invs S \<and> get_conflict_l S = None)
       (\<lambda>_ _. True)
       (\<lambda>_. True) = (\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
          additional_WS_invs S \<and> get_conflict_l S = None)\<close>
    by (auto simp: comp_PRE_def)

  have args: \<open>hrp_comp (twl_st_l_assn\<^sup>d) (Id \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)
      = twl_st_l_assn\<^sup>d\<close>
    unfolding prod_hrp_comp hrp_comp_twl_st_ll_assn_twl_st_of_ll
    by simp
  have out: \<open>hr_comp (option_assn nat_lit_assn_id) (\<langle>Id\<rangle>option_rel) = option_assn nat_lit_assn_id\<close>
    by simp
  show ?thesis
    using hfref_compI_PRE_aux [OF find_unassigned_lit_l_impl.refine
      find_unassigned_lit_l_find_unassigned_lit]
    unfolding pre args out by assumption
qed

sepref_definition decide_l_or_skip_impl is
  \<open>decide_l_or_skip :: nat twl_st_l \<Rightarrow> (bool \<times> nat twl_st_l) nres\<close>
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_l_assn\<close>
  unfolding decide_l_or_skip_def
  unfolding lms_fold_custom_empty
  by sepref

sepref_register \<open>decide_l_or_skip :: nat twl_st_l \<Rightarrow> (bool \<times> nat twl_st_l) nres\<close>
declare decide_l_or_skip_impl.refine[sepref_fr_rules]


subsubsection \<open>Combining Decide, Skip, Resolve and Backtrack\<close>

sepref_definition cdcl_twl_o_prog_l_impl is cdcl_twl_o_prog_l
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a bool_assn *assn twl_st_l_assn\<close>
  unfolding cdcl_twl_o_prog_l_def unfolding option_is_empty
  unfolding HOL_list.fold_custom_empty
  apply (rewrite at \<open>\<not>_ \<and> Multiset.is_empty _\<close> short_circuit_conv)
  by sepref

sepref_register \<open>(cdcl_twl_o_prog_l :: nat twl_st_l \<Rightarrow> (bool \<times> nat twl_st_l) nres)\<close>
declare cdcl_twl_o_prog_l_impl.refine[sepref_fr_rules]


subsubsection \<open>Combining All Together\<close>

sepref_definition cdcl_twl_stgy_prog_l_impl is cdcl_twl_stgy_prog_l
  :: \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding cdcl_twl_stgy_prog_l_def
  by sepref

definition full_cdcl_twl_stgy where
  \<open>full_cdcl_twl_stgy S = SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of None S) (twl_st_of None T))\<close>

lemma cdcl_twl_stgy_prog_l_spec_final:
  shows
    \<open>(cdcl_twl_stgy_prog_l, full_cdcl_twl_stgy) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
      clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> additional_WS_invs S]\<^sub>f
    Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  unfolding full_cdcl_twl_stgy_def
  using cdcl_twl_stgy_prog_l_spec_final
  by (fastforce simp: fref_def nres_rel_def simp del: twl_st_of.simps)

lemma cdcl_twl_stgy_prog_l_impl_spec_final:
  shows
    \<open>(cdcl_twl_stgy_prog_l_impl, full_cdcl_twl_stgy) \<in>
    [\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
      clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> additional_WS_invs S]\<^sub>a
   twl_st_l_assn\<^sup>d \<rightarrow> twl_st_l_assn\<close>
proof -
  have pre: \<open>comp_PRE (Id \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id)
       (\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> additional_WS_invs S) (\<lambda>_ _. True)
       (\<lambda>_. True)
        = (\<lambda>S. twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and>
          clauses_to_update_l S = {#} \<and> get_conflict_l S = None \<and> additional_WS_invs S)\<close>
    by (auto simp: comp_PRE_def)

  have args: \<open> hrp_comp (twl_st_l_assn\<^sup>d) (Id \<times>\<^sub>r Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r Id) =
      twl_st_l_assn\<^sup>d\<close>
    unfolding prod_hrp_comp hrp_comp_twl_st_ll_assn_twl_st_of_ll
    by simp
  have out: \<open>hr_comp twl_st_l_assn Id = twl_st_l_assn\<close>
    by simp
  show ?thesis
    using hfref_compI_PRE_aux [OF cdcl_twl_stgy_prog_l_impl.refine cdcl_twl_stgy_prog_l_spec_final]
    unfolding pre args out by assumption
qed

text \<open>This is the least worst version:\<close>
thm cdcl_twl_stgy_prog_l_impl_spec_final[unfolded full_cdcl_twl_stgy_def]

export_code cdcl_twl_stgy_prog_l_impl in SML_imp module_name CDCL_Non_Cached_List
  file "code/CDCL_Non_Cached_List.ML"


section \<open>Code for the initialisation of the Data Structure\<close>

sepref_register \<open>init_dt_step_l :: nat clause_l \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>
sepref_definition init_dt_step_impl is
  \<open>uncurry (init_dt_step_l :: nat clause_l \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>clause_ll_assn\<^sup>d *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  supply [[goals_limit=1]]
  unfolding init_dt_step_l_def
  unfolding HOL_list.fold_custom_empty lms_fold_custom_empty
  by sepref (* slow *)

declare init_dt_step_impl.refine[sepref_fr_rules]

sepref_definition init_dt_l_impl is
  \<open>uncurry ((init_dt_l :: nat clauses_l \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres))\<close>
  :: \<open>clauses_ll_assn\<^sup>d *\<^sub>a twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding init_dt_l_def
  by sepref

export_code init_dt_l_impl in SML_imp

end