theory CDCL_Two_Watched_Literals_List_Simple_Code
  imports CDCL_Two_Watched_Literals_List DPLL_CDCL_W_Implementation
begin

text \<open>
  First we instantiate our types with sort heap, to show compatibility with code generation. The
  idea is simplify to create injections into the components of our datatypes. This wirks since we
  are not recursing through steps.
\<close>
instance literal :: (heap) heap
proof standard
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where f: \<open>inj f\<close>
    by blast
  then have Hf: \<open>f x = f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  let ?f = \<open>\<lambda>L. (is_pos L, f (atm_of L))\<close>
  have \<open>OFCLASS(bool \<times> nat, heap_class)\<close>
   by standard
  then obtain g :: \<open>bool \<times> nat \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: 'a literal \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

instance ann_lit :: (heap, heap) heap
proof standard
  let ?f = \<open>\<lambda>L:: ('a, 'b) ann_lit. (lit_of L, if is_decided L then None else Some (mark_of L))\<close>
  have f: \<open>inj ?f\<close>
    unfolding inj_on_def Ball_def
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then have Hf: \<open>?f x = ?f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>OFCLASS('a literal \<times> 'b option, heap_class)\<close>
   by standard
  then obtain g :: \<open>'a literal \<times> 'b option \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: ('a, 'b) ann_lit \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed

definition unit_propagation_inner_loop_body_l' :: "nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres" where
  \<open>unit_propagation_inner_loop_body_l' L C S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let i = (if (N!C) ! 0 = L then 0 else 1);
    ASSERT(i < length (N!C));
    let L = (N!C) ! i;
    ASSERT(1-i < length (N!C));
    let L' = (N!C) ! (1 - i);
    ASSERT(no_dup M);
    val_L' \<leftarrow> RETURN (valued M L');
    if val_L' = Some True
    then RETURN S
    else do {
      f \<leftarrow> find_unwatched M (N!C);
      if fst f = None
      then
        if val_L' = Some False
        then do {RETURN (M, N, U, Some (N!C), NP, UP, {#}, {#})}
        else do {RETURN (Propagated L' C # M, N, U, D, NP, UP, WS, add_mset (-L') Q)}
      else do {
        ASSERT(snd f < length (N!C));
        let K = (N!C) ! (snd f);
        let N' = list_update N C (swap (N!C) i (snd f));
        RETURN (M, N', U, D, NP, UP, WS, Q)
      }
    }
   }
\<close>

text \<open>Some functions and types:\<close>
abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat literal \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> (id_assn :: nat literal \<Rightarrow> _)\<close>

abbreviation nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> (nat, nat) ann_lit \<Rightarrow> assn" where
  \<open>nat_ann_lit_assn \<equiv> (id_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

abbreviation nat_ann_lits_assn :: "(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> assn" where
  \<open>nat_ann_lits_assn \<equiv> list_assn nat_ann_lit_assn\<close>

abbreviation nat_lits_trail_assn :: "(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> assn" where
  \<open>nat_lits_trail_assn \<equiv> list_assn (nat_ann_lit_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> list_assn nat_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> list_assn clause_ll_assn\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

(* abbreviation pending_l_assn :: "nat clause \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>pending_l_assn \<equiv> clause_l_assn\<close>

abbreviation pending_ll_assn :: "nat clause_l \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>pending_ll_assn \<equiv> clause_ll_assn\<close> *)

abbreviation working_queue_ll_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_ll_assn \<equiv> list_mset_assn nat_assn\<close>

(* concrete_definition backtrack_l'_impl uses backtrack_l'_impl

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (SML) CDCL_W_Level

prepare_code_thms backtrack_l'_impl_def
export_code backtrack_l'_impl in SML *)


type_synonym working_queue_ll = "nat list"
type_synonym lit_queue_l = "nat literal list"

type_synonym twl_st_ll =
  "(nat, nat) ann_lits \<times> nat clauses_l \<times> nat \<times>
    nat clause_l option \<times> nat clauses_l \<times> nat clauses_l \<times> working_queue_ll \<times> lit_queue_l"

fun twl_st_of_ll :: \<open>twl_st_ll \<Rightarrow> nat twl_st_l\<close> where
  \<open>twl_st_of_ll (M, N, U, D, NP, UP, WS, Q) = (M, N, U, D, mset `# mset NP, mset `# mset UP, mset WS, mset Q)\<close>

notation prod_assn (infixr "*assn" 90)
abbreviation twl_st_ll_assn :: \<open>nat twl_st_l \<Rightarrow> twl_st_ll \<Rightarrow> assn\<close> where
\<open>twl_st_ll_assn \<equiv>
 nat_lits_trail_assn *assn clauses_ll_assn *assn nat_assn *assn
 option_assn clause_ll_assn *assn
 clauses_l_assn *assn
 clauses_l_assn *assn
 working_queue_ll_assn *assn
 clause_l_assn
\<close>

section \<open>Declaration of the operators.\<close>
sepref_decl_op nat_lit_eq: "op = :: nat literal \<Rightarrow> nat literal \<Rightarrow> bool" ::
  "(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (bool \<times> _) set)" .

lemma [def_pat_rules]:
  "op = $ a $ b \<equiv> op_nat_lit_eq $ a $ b"
  by auto

term id_assn

definition nat_ann_lit_eq_cases :: "(nat, nat) ann_lit \<Rightarrow> (nat, nat) ann_lit \<Rightarrow> bool" where
  \<open>nat_ann_lit_eq_cases K L =
    (case (K, L) of
      (Decided K, Decided L) \<Rightarrow> K = L
    | (Propagated K C, Propagated L C') \<Rightarrow> K = L \<and> C = C'
    | (_, _) \<Rightarrow> False)\<close>

definition nat_lit_eq_cases :: "nat literal \<Rightarrow> nat literal \<Rightarrow> bool" where
  \<open>nat_lit_eq_cases K L =
    (case (K, L) of
      (Pos K, Pos L) \<Rightarrow> K = L
    | (Neg K, Neg L) \<Rightarrow> K = L
    | (_, _) \<Rightarrow> False)\<close>


sepref_decl_op atm_of: "atm_of :: nat literal \<Rightarrow> nat" ::
  "(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat \<times> _) set)" .

lemma [def_pat_rules]:
  "atm_of \<equiv> op_atm_of"
  by auto

definition atm_of_impl  :: "nat literal \<Rightarrow> nat" where
  \<open>atm_of_impl L = do {
    case L of
      Pos K \<Rightarrow> K
    | Neg K \<Rightarrow> K}\<close>


sepref_decl_op lit_of: "lit_of :: (nat, nat) ann_lit \<Rightarrow> nat literal" ::
  "(Id :: ((nat, nat) ann_lit \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set)" .

lemma [def_pat_rules]:
  "lit_of \<equiv> op_lit_of"
  by auto

sepref_decl_op option_bool_eq: "op = :: bool option \<Rightarrow> bool option \<Rightarrow> bool" ::
  "(Id :: ((bool option \<times> _) set)) \<rightarrow> (Id :: (bool option \<times> _) set) \<rightarrow> (Id :: (bool \<times> _) set)" .

lemma [def_pat_rules]:
  "op = $ a $ b \<equiv> op_option_bool_eq $ a $ b"
  by auto

sepref_decl_op case_bool: "case_bool :: 'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a" ::
  "(Id :: (('a \<times> 'a) set)) \<rightarrow> (Id :: ('a \<times> 'a) set) \<rightarrow> (Id :: (bool \<times> _) set) \<rightarrow> (Id :: ('a \<times> 'a) set)" .


lemma [def_pat_rules]:
  "case_bool $ a $ b $ v \<equiv> op_case_bool $ a $ b $ v"
  by auto

definition option_bool_eq_impl :: \<open>bool option \<Rightarrow> bool option \<Rightarrow> bool\<close> where
  \<open>option_bool_eq_impl L L' =
   (if is_None L
   then
     if is_None L' then True else False
   else
    (if is_None L' then False else the L = the L'))\<close>

definition lit_of_impl :: "(nat, nat) ann_lit \<Rightarrow> nat literal" where
  \<open>lit_of_impl L = do {
    case L of
      Propagated K _ \<Rightarrow> K
    | Decided K \<Rightarrow> K}\<close>


definition case_bool_impl :: \<open>bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>case_bool_impl L L' v = do {if v then L else L'}\<close>

context
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI] frefI
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

lemma nat_lit_eq_cases_refine[sepref_fr_rules]:
  \<open>(uncurry (return oo nat_lit_eq_cases), uncurry (RETURN oo op_nat_lit_eq)) \<in>
    nat_lit_assn\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding nat_lit_eq_cases_def
  apply (sep_auto split: literal.split)
  apply (rename_tac aa ba a b)
  apply (case_tac aa; case_tac ba; sep_auto)
  done

sepref_decl_impl nat_lit_eq_cases: nat_lit_eq_cases_refine .


lemma atom_of_impl_refine[sepref_fr_rules]:
  \<open>(return o atm_of_impl, RETURN o op_atm_of) \<in> nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding op_atm_of_def atm_of_impl_def
  by (sep_auto split: literal.split)

sepref_decl_impl atom_of_impl: atom_of_impl_refine .


lemma lit_of_impl_refine[sepref_fr_rules]:
  \<open>(return o lit_of_impl, RETURN o op_lit_of) \<in> nat_ann_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn\<close>
  unfolding op_lit_of_def lit_of_impl_def
  by (sep_auto split: ann_lit.split)

sepref_decl_impl lit_of_impl: atom_of_impl_refine .

lemma option_bool_eq_impl_option_op_bool_eq_impl: \<open>option_bool_eq_impl = op_option_bool_eq\<close>
  unfolding option_bool_eq_impl_def op_option_bool_eq_def by (auto split: option.splits intro!: ext)

lemma option_bool_eq_refine[sepref_fr_rules]:
  \<open>(uncurry (return oo option_bool_eq_impl), uncurry (RETURN oo op_option_bool_eq)) \<in>
    (option_assn bool_assn)\<^sup>k *\<^sub>a (option_assn bool_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding option_bool_eq_impl_option_op_bool_eq_impl
  unfolding op_option_bool_eq_def
  apply sep_auto
  subgoal for b aa ba ab bb ac bc by (cases b; cases ba; cases aa; auto)
  subgoal for b aa ba ab bb ac bc by (cases b; cases ba; cases aa; auto)
  done

sepref_decl_impl option_bool_eq: option_bool_eq_refine .

lemma case_bool_impl_refine[sepref_fr_rules]:
  \<open>(uncurry2 (return ooo (case_bool_impl :: bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool)),
       uncurry2 (RETURN ooo op_case_bool)) \<in>
    (id_assn :: bool \<Rightarrow> _)\<^sup>k *\<^sub>a (id_assn :: bool \<Rightarrow> _)\<^sup>k *\<^sub>a (bool_assn)\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding case_bool_impl_def
  unfolding op_option_bool_eq_def
  apply (sep_auto split!: if_splits option.splits)
  apply (case_tac bc)
  apply auto
  done

sepref_decl_impl case_bool: case_bool_impl_refine .

end

sepref_decl_op defined_lit_imp: "defined_lit:: (nat, nat) ann_lit list \<Rightarrow> nat literal \<Rightarrow> bool" ::
  "(Id :: ((nat, nat) ann_lit list \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> bool_rel" .

lemma [def_pat_rules]:
  "defined_lit $ a $ b \<equiv> op_defined_lit_imp $ a $ b"
  by auto

definition defined_lit_set :: \<open>('a, 'm) ann_lit set \<Rightarrow> 'a literal \<Rightarrow> bool\<close>
  where
\<open>defined_lit_set I L \<longleftrightarrow> (Decided L \<in> I) \<or> (\<exists>P. Propagated L P \<in>  I)
  \<or> (Decided (-L) \<in> I) \<or> (\<exists>P. Propagated (-L) P \<in>  I)\<close>

lemma defined_lit_defined_lit_set: \<open>defined_lit M L \<longleftrightarrow> defined_lit_set (set M) L\<close>
  unfolding defined_lit_set_def defined_lit_def
  by auto

lemma defined_lit_set_insert: \<open>defined_lit_set (insert L' M) L \<longleftrightarrow> atm_of (lit_of L') = atm_of L \<or> defined_lit_set M L\<close>
  unfolding defined_lit_set_def
  by (metis (no_types, lifting) ann_lit.sel(1) ann_lit.sel(2) atm_of_eq_atm_of insertE insertI1
      insertI2 literal_is_lit_of_decided)

lemma defined_lit_set_nil[simp]: \<open>\<not>defined_lit_set {} L\<close>
   unfolding defined_lit_set_def by auto

lemma defined_lit_set_mono: \<open>M \<subseteq> M' \<Longrightarrow> defined_lit_set M L \<Longrightarrow> defined_lit_set M' L\<close>
   unfolding defined_lit_set_def by auto

definition defined_lit_map_impl :: "(nat, nat) ann_lit list \<Rightarrow> nat literal \<Rightarrow> bool nres" where
  \<open>defined_lit_map_impl M L =
  nfoldli M
     (\<lambda>brk. brk = False)
     (\<lambda>L' _. do {
       let L\<^sub>1 = atm_of L;
       let L\<^sub>1'' = atm_of (lit_of L');
       RETURN (L\<^sub>1 = L\<^sub>1'')})
    False\<close>

sepref_definition defined_lit_map_impl' is
  \<open>uncurry (defined_lit_map_impl :: (nat, nat) ann_lit list \<Rightarrow> _)\<close> ::
  \<open>(nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
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
    (nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using defined_lit_map_impl'.refine_raw[unfolded defined_lit_map_impl'_def[symmetric],
      FCOMP defined_lit_map_impl_spec] unfolding op_defined_lit_imp_def
  .

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
  \<open>(nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a option_assn bool_assn\<close>
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


(* lemma [sepref_import_param]:
  \<open>(uncurry (RETURN oo valued), uncurry (RETURN oo valued)) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: nres_rel_def) *)

(* sepref_register \<open>valued' :: ((nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option)\<close>

lemma valued_impl'_refine[sepref_fr_rules]:
  shows \<open>(uncurry valued_impl', uncurry (RETURN oo valued)) \<in>
    [\<lambda>(M, _). no_dup M]\<^sub>a (nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  using valued_impl'.refine_raw[unfolded valued_impl'_def[symmetric], FCOMP valued_impl_spec]
  unfolding hrp_comp_Id2 valued'_def .

concrete_definition valued'_impl_impl uses valued_impl'_refine
 *)
context
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI] frefI
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

(*

lemma [sepref_import_param]:
  \<open>(uncurry (RETURN oo valued), uncurry (RETURN oo valued)) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
  by (auto simp: nres_rel_def)
 *)
(* sepref_register \<open>valued' :: ((nat, nat) ann_lits \<Rightarrow> nat literal \<Rightarrow> bool option)\<close> *)
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
    [\<lambda>(M, _). no_dup M]\<^sub>a (nat_ann_lits_assn)\<^sup>k *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> option_assn bool_assn\<close>
  using valued_impl'.refine_raw[unfolded valued_impl'_def[symmetric], FCOMP valued_impl_spec]
  unfolding hrp_comp_Id2 valued'_def op_valued_def .

sepref_decl_impl valued: valued_impl'_refine
  by simp

end
term find_unwatched_impl
(* concrete_definition valued'_impl_impl uses valued_impl'_refine *)

(*
lemma [safe_constraint_rules]: \<open>is_pure R \<Longrightarrow> is_pure (nat_ann_lits_assn R)\<close>
  by (simp add: list_assn_pure_conv) *)
(* definition find_unwatched :: "('a, 'b) ann_lits \<Rightarrow> 'a clause_l \<Rightarrow> (bool option \<times> nat) nres" where
\<open>find_unwatched M C = do {
  WHILE\<^sub>T\<^bsup>\<lambda>(found, i). i \<ge> 2 \<and> i \<le> length C \<and> (\<forall>j\<in>{2..<i}. -(C!j) \<in> lits_of_l M) \<and>
    (found = Some False \<longrightarrow> (undefined_lit M (C!i) \<and> i < length C)) \<and>
    (found = Some True \<longrightarrow> (C!i \<in> lits_of_l M \<and> i < length C)) \<^esup>
    (\<lambda>(found, i). found = None \<and> i < length C)
    (\<lambda>(_, i). do {
      ASSERT(i < length C);
      case valued M (C!i) of
        None \<Rightarrow> do { RETURN (Some False, i)}
      | Some v \<Rightarrow>
         (if v then do { RETURN (Some True, i)} else do { RETURN (None, i+1)})
      }
    )
    (None, 2::nat)
  }
\<close> *)

term find_unwatched
sepref_definition find_unwatched_impl is
   "uncurry (find_unwatched :: (nat, nat) ann_lits
      \<Rightarrow> nat literal list \<Rightarrow> (bool option \<times> nat) nres)"
  :: \<open>[\<lambda>(M, L). no_dup M]\<^sub>anat_ann_lits_assn\<^sup>k *\<^sub>a (list_assn nat_lit_assn)\<^sup>k \<rightarrow> prod_assn (option_assn bool_assn) nat_assn\<close>
  unfolding find_unwatched_def (* valued'_def[symmetric] *)
  supply [[goals_limit=1]]
  by sepref

sepref_register "find_unwatched :: (nat, nat) ann_lits
      \<Rightarrow> nat literal list \<Rightarrow> (bool option \<times> nat) nres"
declare find_unwatched_impl.refine_raw[sepref_fr_rules]
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
     nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_ann_lit_assn\<close>
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
     nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_assn\<close>
  apply (
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      intro: Assertions.mod_emp_simp)
  done

lemma [sepref_fr_rules]:
  \<open>((return o op_Decided), (RETURN o op_Decided)) \<in>
     nat_lit_assn\<^sup>k \<rightarrow>\<^sub>a nat_ann_lit_assn\<close>
  apply (
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      intro: Assertions.mod_emp_simp)
  done

sepref_definition unit_propagation_inner_loop_body_l_impl is \<open>uncurry2 (unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close> ::
  \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding unit_propagation_inner_loop_body_l_def unfolding lms_fold_custom_empty
  supply [[goals_limit=1]]
  by sepref

concrete_definition unit_propagation_inner_loop_body_l_impl' uses unit_propagation_inner_loop_body_l_impl.refine_raw

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (SML) CDCL_W_Level

prepare_code_thms unit_propagation_inner_loop_body_l_impl'_def
export_code unit_propagation_inner_loop_body_l_impl' in SML

sepref_register \<open>unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_inner_loop_body_l_impl.refine_raw[sepref_fr_rules]

sepref_register \<open>select_from_working_queue :: nat twl_st_l \<Rightarrow> (nat twl_st_l \<times> nat) nres\<close>

lemma H: \<open>(\<forall>x x'. (x' = x) = ((x', x) \<in> P')) \<longleftrightarrow> P' = Id\<close>
  by (auto simp: the_pure_def)

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

definition select_from_working_queue2 :: \<open>'v twl_st_l \<Rightarrow> (nat) nres\<close> where
  \<open>select_from_working_queue2 S = SPEC (\<lambda>C. C \<in># working_queue_l S)\<close>

lemma hd_select_from_working_queue2_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd WS),
      select_from_working_queue2) \<in>
    [\<lambda>S. working_queue_l S \<noteq> {#}]\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow> nat_assn\<close>
  unfolding select_from_working_queue2_def
  apply sepref_to_hoare
  apply sep_auto
  apply (case_tac \<open>af\<close>; case_tac am)
    apply sep_auto
  apply (sep_auto)
     apply (auto simp: mod_pure_star_dist list_mst_assn_add_mset_empty_false
    dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
      dest!: mod_starD; fail)+
  done

definition hd_of_working_queue_l :: \<open>twl_st_ll \<Rightarrow> nat\<close> where
  \<open>hd_of_working_queue_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd WS)\<close>

definition tl_of_working_queue_l :: \<open>twl_st_ll \<Rightarrow> twl_st_ll\<close> where
  \<open>tl_of_working_queue_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). (M, N, U, D, NP, UP, tl WS, Q))\<close>

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

lemma hd_select_from_working_queue_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>S. (tl_of_working_queue_l S, hd_of_working_queue_l S)),
      select_from_working_queue) \<in>
    [\<lambda>S. working_queue_l S \<noteq> {#}]\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow> prod_assn twl_st_ll_assn nat_assn\<close>
proof -
  have H: \<open>RETURN x
         \<le> SPEC (\<lambda>(S', C).
                     C \<in># working_queue_l S \<and>
                     S' = set_working_queue_l (remove1_mset C (working_queue_l S)) S)\<close>
   if \<open>snd x \<in># working_queue_l S\<close> and
   \<open>fst x = set_working_queue_l (remove1_mset (snd x) (working_queue_l S)) S\<close>
   for x :: \<open>nat twl_st_l \<times> nat\<close> and S :: \<open>nat twl_st_l\<close> and xi xi' :: twl_st_ll
     using that by auto
  show ?thesis
    unfolding select_from_working_queue_def tl_of_working_queue_l_def hd_of_working_queue_l_def
    apply sepref_to_hoare
    apply (sep_auto (plain))
     apply (rule_tac psi = \<open>RETURN ((\<lambda>_ _ (S, C). (twl_st_of_ll S, C)) x xi xa) \<le> _\<close> in asm_rl)
     apply (rule order_trans[OF _ H])
       apply (rule order_refl)
      apply (auto simp: list_mst_assn_add_mset_empty_false
        dest!: list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset; fail)[]
     apply (auto simp: mod_pure_star_dist mset_tl_remove1_mset_hd
        dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset
        entails_list_assn_eqD entails_list_assn_list_assn_eqD entails_option_assn_assn_eqD
        entails_list_mset_assn_list_mset_assn_eq_mset; fail)[]
    by (sep_auto intro!: ent_star_mono simp: list_assn_same_emp option_assn_same_emp
        list_mset_assn_id_mset_emp list_mset_assn_list_mset_assn_id_mset_mset_emp)
qed

lemma working_queue_l_abs_def:\<open>working_queue_l = (fst o snd o snd o snd o snd o snd o snd)\<close>
  by auto

lemma working_queue_l_refine[sepref_fr_rules]:
  \<open>(return o ((fst o snd o snd o snd o snd o snd o snd) ::  twl_st_ll \<Rightarrow> _),
     RETURN o (working_queue_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a list_mset_assn nat_assn\<close>
  unfolding working_queue_l_abs_def
  by sepref_to_hoare sep_auto

sepref_definition unit_propagation_inner_loop_l_impl is
  \<open>uncurry (unit_propagation_inner_loop_l :: nat literal \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding unit_propagation_inner_loop_l_def
  by sepref


sepref_register \<open>unit_propagation_inner_loop_l :: nat literal \<Rightarrow>  nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_inner_loop_l_impl.refine_raw[sepref_fr_rules]

sepref_register \<open>select_and_remove_from_pending :: nat twl_st_l \<Rightarrow> (nat twl_st_l \<times> nat literal) nres\<close>

definition hd_of_pending_l :: \<open>twl_st_ll \<Rightarrow> nat literal\<close> where
  \<open>hd_of_pending_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). hd Q)\<close>

(* TODO Move to top *)
fun get_clauses_ll :: "twl_st_ll \<Rightarrow> nat clauses_l" where
  \<open>get_clauses_ll (M, N, U, D, NP, UP, WS, Q) = N\<close>
(* End move *)

definition clause_to_update_l :: \<open>nat literal \<Rightarrow> twl_st_ll \<Rightarrow> working_queue_ll\<close> where
  \<open>clause_to_update_l L S =
    filter
      (\<lambda>C::nat. get_clauses_ll S ! C ! 0 = L \<or> get_clauses_ll S ! C ! 1 = L)
      ([1..<length (get_clauses_ll S)])\<close>

definition tl_of_pending_l :: \<open>twl_st_ll \<Rightarrow> twl_st_ll\<close> where
  \<open>tl_of_pending_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q). (M, N, U, D, NP, UP,
     clause_to_update_l (hd Q) (M, N, U, D, NP, UP, WS, Q),
     tl Q))\<close>


lemma nth_mem_tl: \<open>0 < x \<Longrightarrow> x < length N \<Longrightarrow> N!x \<in> set (tl N)\<close>
  using nth_mem[of \<open>x - 1\<close> \<open>tl N\<close>] by (cases N) (auto simp del: nth_mem)

lemma clause_to_update_l_clause_to_update:
  fixes M N av D NP UP WS Q
  assumes \<open>twl_struct_invs (twl_st_of None (M, N, U, D, mset `# mset NP, mset `# mset UP, mset WS, mset Q))\<close>
  shows \<open>mset (clause_to_update_l (hd Q) (M, N, U, D, NP, UP, WS, Q)) =
   clause_to_update (hd Q) (M, N, U, D, mset `# mset NP, mset `# mset UP, mset WS, mset Q)\<close>
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
lemma hd_select_and_remove_from_pending_refine[sepref_fr_rules]: (* TODO tune proof *)
  \<open>(return o (\<lambda>S. (tl_of_pending_l S, hd_of_pending_l S)),
      select_and_remove_from_pending) \<in>
    [\<lambda>S. pending_l S \<noteq> {#} \<and> twl_struct_invs (twl_st_of None S)]\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow> prod_assn twl_st_ll_assn nat_lit_assn\<close>
proof -
  have H: \<open>RETURN x \<le> select_and_remove_from_pending S\<close>
   if \<open>snd x \<in># pending_l S\<close> and
   \<open>fst x = set_working_queue_l (clause_to_update (snd x) S) (set_pending_l (pending_l S - {#snd x#}) S)\<close>
   for x :: \<open>nat twl_st_l \<times> nat literal\<close> and S :: \<open>nat twl_st_l\<close> and xi xi' :: twl_st_ll
     using that by (auto simp: select_and_remove_from_pending_def)
  show ?thesis
    unfolding tl_of_pending_l_def hd_of_pending_l_def
    apply sepref_to_hoare
    apply (sep_auto (plain))
     apply (rule_tac psi = \<open>RETURN ((\<lambda>_ _ (S, C). (twl_st_of_ll S, C)) x xi xa) \<le> _\<close> in asm_rl)
     apply (rule order_trans[OF _ H])
       apply (rule order_refl)
      apply (auto simp: list_mst_assn_add_mset_empty_false simp del: twl_st_of_ll.simps
        dest!: list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset; fail)[]
     apply (auto simp: mod_pure_star_dist mset_tl_remove1_mset_hd
        dest!: list_mset_assn_add_mset_cons_in list_mset_assn_add_mset_cons_in
        dest!: mod_starD entails_list_mset_assn_eq_mset
        entails_list_assn_eqD entails_list_assn_list_assn_eqD entails_option_assn_assn_eqD
        entails_list_mset_assn_list_mset_assn_eq_mset
        intro!: clause_to_update_l_clause_to_update; fail)[]
    apply (sep_auto intro!: ent_star_mono simp: list_assn_same_emp option_assn_same_emp
        list_mset_assn_id_mset_emp list_mset_assn_list_mset_assn_id_mset_mset_emp)
   done
qed

lemma pending_l_refine[sepref_fr_rules]:
  \<open>(return o ((snd o snd o snd o snd o snd o snd o snd) ::  twl_st_ll \<Rightarrow> _),
     RETURN o (pending_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a list_mset_assn nat_lit_assn\<close>
  by sepref_to_hoare sep_auto

lemma get_trail_l_refine[sepref_fr_rules]:
  \<open>(return o (fst ::  twl_st_ll \<Rightarrow> _),
     RETURN o (get_trail_l :: nat twl_st_l \<Rightarrow> _)) \<in>
   twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a nat_ann_lits_assn\<close>
  by sepref_to_hoare sep_auto

sepref_definition unit_propagation_outer_loop_l_impl is
  \<open>(unit_propagation_outer_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding unit_propagation_outer_loop_l_def
  by sepref

sepref_register \<open>unit_propagation_outer_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres\<close>

declare unit_propagation_outer_loop_l_impl.refine_raw[sepref_fr_rules]


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
      twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a option_assn clause_ll_assn\<close>
  by sepref_to_hoare sep_auto

lemma option_is_Nil:
   \<open>a = Some [] \<longleftrightarrow> \<not>is_None a \<and> is_Nil (the a)\<close>
  by (cases a) (auto split: list.splits)

lemma lit_and_ann_of_propagated_hnr[sepref_fr_rules]:
  \<open>(return o lit_and_ann_of_propagated, RETURN o lit_and_ann_of_propagated) \<in>
     [\<lambda>L. is_proped L]\<^sub>a nat_ann_lit_assn\<^sup>k \<rightarrow> prod_assn nat_lit_assn nat_assn\<close>
  apply sepref_to_hoare
  apply (case_tac x)
   apply sep_auto+
  done

(* TODO change order of the arguments of maximum_level_code *)
lemma get_maximum_level_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo (\<lambda>M D. maximum_level_code D M)),
      uncurry (RETURN oo (get_maximum_level :: (nat, nat) ann_lit list \<Rightarrow> _))) \<in>
    nat_ann_lits_assn\<^sup>d *\<^sub>a (list_mset_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding maximum_level_code_eq_get_maximum_level
  apply sepref_to_hoare
  by (sep_auto dest: entails_list_assn_eqD entails_list_mset_assn_eq_mset
      simp: mod_star_conv)

lemma maximum_level_code_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo maximum_level_code),
      uncurry (RETURN oo (maximum_level_code :: _ \<Rightarrow> (nat, nat) ann_lit list \<Rightarrow> _))) \<in>
    (list_assn nat_lit_assn)\<^sup>d *\<^sub>a nat_ann_lits_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn\<close>
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

sepref_definition skip_and_resolve_loop_l_impl is
  \<open>(skip_and_resolve_loop_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding skip_and_resolve_loop_l_def option_is_Nil conv_to_is_Nil
  unfolding HOL_list.fold_custom_empty
  skip_and_resolve_loop_inv_def mset_remove1[symmetric]
  maximum_level_code_eq_get_maximum_level[symmetric]
  apply (rewrite at \<open>\<not>_ \<and> \<not> is_decided _\<close> short_circuit_conv)
  apply (rewrite at \<open>\<not>_ \<and> is_Nil _\<close> short_circuit_conv)
  supply [[goals_limit=1]]
  by sepref


definition find_decomp_l :: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits Heap" where
  \<open>find_decomp_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    do {
     let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
     let M1 = tl (the (bt_cut j M));
     return M1
    })\<close>

lemma find_decomp_l_hnr[sepref_fr_rules]:
  \<open>(uncurry find_decomp_l, uncurry find_decomp) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal). True(*
     (* D \<noteq> None \<and> D \<noteq> Some [] \<and> *)
      (\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = maximum_level_code ((remove1 (-L) (the D))) M + 1) *)]\<^sub>a
      twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> nat_ann_lits_assn\<close>
  unfolding find_decomp_l_def find_decomp_def
  apply sepref_to_hoare
  apply (sep_auto)
sorry

definition find_lit_of_max_level_l:: "twl_st_ll \<Rightarrow> nat literal \<Rightarrow> nat literal Heap" where
  \<open>find_lit_of_max_level_l = (\<lambda>(M, N, U, D, NP, UP, WS, Q) L.
    return (the (find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (-L) (mset (the D)))) (the D))))\<close>

sepref_register "find_lit_of_max_level :: nat twl_st_l \<Rightarrow> nat literal \<Rightarrow> nat literal nres"
sepref_register "find_decomp :: nat twl_st_l \<Rightarrow> nat literal \<Rightarrow> (nat, nat) ann_lits nres"

lemma find_lit_of_max_level_l_hnr[sepref_fr_rules]:
  \<open>(uncurry find_lit_of_max_level_l, uncurry find_lit_of_max_level) \<in>
    [\<lambda>((M, N, U, D, NP, UP, WS, Q), L::nat literal).
     (* D \<noteq> None \<and> D \<noteq> Some [] \<and> *)
      (\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (mset (the D) - {#-L#}) + 1)]\<^sub>a
      twl_st_ll_assn\<^sup>d *\<^sub>a nat_lit_assn\<^sup>k \<rightarrow> nat_lit_assn\<close>
  sorry

fun add_mset_list :: "'a list \<Rightarrow> 'a multiset multiset \<Rightarrow> 'a multiset multiset"  where
  \<open>add_mset_list L UP = add_mset (mset L) UP\<close>

sepref_register \<open>add_mset_list :: nat literal list \<Rightarrow> nat clauses \<Rightarrow> nat clauses\<close>
term clauses_ll_assn
lemma add_mset_list_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo Cons), uncurry (RETURN oo add_mset_list)) \<in>
    clause_ll_assn\<^sup>d *\<^sub>a clauses_l_assn\<^sup>d \<rightarrow>\<^sub>a clauses_l_assn\<close>
  unfolding add_mset_list.simps
  apply sepref_to_hoare
  apply sep_auto
  sorry

definition backtrack_l :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>backtrack_l S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        ASSERT(get_level M L = count_decided M);
        ASSERT(D \<noteq> None);
        ASSERT(\<exists>K M1 M2. (Decided K # M1, M2) \<in> set (get_all_ann_decomposition M) \<and>
          get_level M K = get_maximum_level M (remove1_mset (-L) (mset (the D))) + 1);
        M1 \<leftarrow> find_decomp (M, N, U, D, NP, UP, WS, Q) L;

        if length (the D) > 1
        then do {
          L' \<leftarrow> find_lit_of_max_level (M, N, U, D, NP, UP, WS, Q) L;
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, add_mset L {#})
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset_list (the D) UP, WS, add_mset L {#})
        }
      }
    }
  \<close>

sepref_definition backtrack_l_impl is
  \<open>(backtrack_l :: nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
  :: \<open>twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding backtrack_l_def
  unfolding HOL_list.fold_custom_empty lms_fold_custom_empty
  skip_and_resolve_loop_inv_def mset_remove1[symmetric]
  maximum_level_code_eq_get_maximum_level[symmetric]
  supply [[goals_limit=2]]
  by sepref


definition backtrack_l' :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>backtrack_l' S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        ASSERT(D \<noteq> None);
        let L = lit_of (hd M);
        let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
        ASSERT(bt_cut j M \<noteq> None);
        let M1 = tl (the (bt_cut j M));

        if length (the D) > 1
        then do {
          let SL' = (find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (-L) (mset (the D)))) (the D));
          ASSERT(SL' \<noteq> None);
          let L' = the SL';
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, mset [L])
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, mset [L])
        }
      }
    }
  \<close>

lemma Let_assignI: \<open>\<Phi> = {L'} \<Longrightarrow> P L' = Q L' \<Longrightarrow>  (do {let L = L'; P L}) = (do {L \<leftarrow> RES \<Phi>; Q L})\<close>
  by (simp add: RES_sng_eq_RETURN)

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

lemma backtrack_l'_spec:
  assumes
    confl1: \<open>get_conflict_l S \<noteq> None\<close> and
    confl2: \<open>get_conflict_l S \<noteq> Some []\<close> and
    \<open>working_queue_l S = {#}\<close> and
    \<open>pending_l S = {#}\<close> and
    \<open>additional_WS_invs S\<close> and
    ns: \<open>no_step cdcl\<^sub>W_restart_mset.skip (convert_to_state (twl_st_of None S))\<close> and
    \<open>no_step cdcl\<^sub>W_restart_mset.resolve (convert_to_state (twl_st_of None S))\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of None S)\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of None S)\<close> (* and
    SS: \<open>S' = S\<close> *)
  shows \<open>backtrack_l' S \<le> \<Down> Id (backtrack_l S)\<close>
proof-
  show ?thesis
    unfolding backtrack_l_def backtrack_l'_def (* SS *)
    apply (rewrite at \<open>let _ = snd _ in _\<close> Let_def)
    apply (refine_rcg; remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal premises p for M N U C NP UP WS Q L
    proof -
      note S = p(1) and L = p(4) and M_not_empty = p(2) and L_hd = p(4) and ex_decomp = p(6)
      have n_d: \<open>no_dup M\<close>
        using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        by (simp add: cdcl\<^sub>W_restart_mset_state S)
      obtain C' where [simp]: \<open>C = Some C'\<close>
        using confl1 S by auto
      have lev_L: \<open>get_level M L = count_decided M\<close>
        using M_not_empty L by (cases M) auto
      have uhd_C: \<open>- lit_of (hd (convert_lits_l N M)) \<in> set C'\<close>
        using cdcl\<^sub>W_restart_mset.no_step_skip_hd_in_conflicting[of
            \<open>convert_to_state (twl_st_of None (M, N, U, C, NP, UP, WS, Q))\<close>]
        confl2 ns struct_invs stgy_invs unfolding S
        by (auto simp: twl_struct_invs_def twl_stgy_invs_def cdcl\<^sub>W_restart_mset_state)
      obtain M1'' M2'' K'' where
        decomp_K'': \<open>(Decided K'' # M1'', M2'') \<in> set (get_all_ann_decomposition M)\<close>
        \<open>get_level M K'' = Suc (get_maximum_level M (remove1_mset (- lit_of (hd M)) (mset C')))\<close>
        using ex_decomp L_hd by auto
      then have lev_max: \<open>get_maximum_level M (mset (remove1 (-L) C')) < count_decided M\<close>
        using count_decided_ge_get_level[of M K''] L by auto
      have \<open>-L \<in># mset C'\<close>
        using uhd_C L M_not_empty by (cases M) simp_all
      with multi_member_split[OF this]
      have False if \<open>find_level_decomp M (the C) [] (count_decided M) = None\<close>
        using find_level_decomp_none[OF that, of \<open>-L\<close> \<open>remove1 (-L) C'\<close>] lev_max
        unfolding S by (auto dest!: simp: lev_L)
      then obtain K j where
        Kj: \<open>find_level_decomp M C' [] (count_decided M) = Some (K, j)\<close>
        by (cases \<open>find_level_decomp M (the C) [] (count_decided M)\<close>) auto
      then have
        \<open>K \<in> set C'\<close> and
        j: \<open>get_maximum_level M (mset (remove1 K C')) = j\<close> and
        \<open>get_level M K = count_decided M\<close>
        using find_level_decomp_some[OF Kj] by simp_all
      have KL: \<open>K = -L\<close>
        by (metis \<open>K \<in> set C'\<close> \<open>\<exists>A. mset C' = add_mset (- L) A\<close> \<open>get_level M K = count_decided M\<close>
            add_mset_remove_trivial get_maximum_level_ge_get_level leD lev_max member_add_mset
            mset_remove1 set_mset_mset)
      have j_le_M: \<open>j < count_decided M\<close>
          unfolding j[symmetric] KL using lev_max by simp
      have \<open>bt_cut j M \<noteq> None\<close>
        apply (rule bt_cut_not_none2[of ])
        using n_d apply (simp; fail)
        using j_le_M by simp
      then obtain M2 M1 K''' M' where
        \<open>M = M2 @ M'\<close> and M': \<open>M' = Decided K''' # M1\<close> and lev_K: \<open>get_level M K''' = j + 1\<close> and
        bt_cut: \<open>bt_cut j M = Some M'\<close>
        using bt_cut_some_decomp[of M j \<open>the (bt_cut j M)\<close>] n_d by auto
      show ?thesis
        using lev_K j bt_cut_in_get_all_ann_decomposition[OF n_d bt_cut] by (auto simp: Kj bt_cut M' KL)
    qed
    subgoal premises p for M N U C NP UP WS Q L M1
    proof -
      note S = p(1) and L_hd = p(4) and len_C = p(9)
      obtain C' where [simp]: \<open>C = Some C'\<close>
        using confl1 S by auto

      have \<open>find (\<lambda>L'. get_level M L' = get_maximum_level M (remove1_mset (- L) (mset (the C)))) (the C) \<noteq> None\<close>
      proof (rule ccontr)
        assume H: \<open>\<not>?thesis\<close>
        have \<open>remove1_mset (- lit_of (hd M)) (mset (the C)) \<noteq> {#}\<close>
          using len_C by (cases C'; cases \<open>tl C'\<close>) (auto simp: Diff_eq_empty_iff_mset)
        then show False
          using get_maximum_level_exists_lit_of_max_level[of
              \<open>remove1_mset (- lit_of (hd M)) (mset (the C))\<close> M]
          using L_hd H by (auto simp: find_None_iff dest: in_diffD)
      qed
      then show ?thesis
        using p by (auto dest: find_SomeD)
    qed
    subgoal by simp
    subgoal by simp
    done
qed

definition cdcl_twl_o_prog_l' :: "'v twl_st_l \<Rightarrow> (bool \<times> 'v twl_st_l) nres" where
  \<open>cdcl_twl_o_prog_l' S =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S in
      do {
        if D = None
        then
          if (\<exists>L. undefined_lit M L \<and> atm_of L \<in> atms_of_mm (clause `# twl_clause_of `# mset (take U (tl N))))
          then do {S \<leftarrow> decide_l S; RETURN (False, S)}
          else do {RETURN (True, S)}
        else do {
          T \<leftarrow> skip_and_resolve_loop_l S;
          if get_conflict_l T \<noteq> Some []
          then do {U \<leftarrow> backtrack_l' T; RETURN (False, U)}
          else do {RETURN (True, T)}
        }
      }
    }
  \<close>

lemma TT:
  assumes \<open>(f, g) \<in> {(S, S'). S' = h S \<and> P S} \<rightarrow> \<langle>{(T, T'). T' = h' T \<and> Q T}\<rangle>nres_rel\<close> and
    \<open>P S\<close> and \<open>\<And>S. P S \<Longrightarrow> nofail (g (h S))\<close>
  shows \<open>f S \<le> \<Down> {(T', T). T = T' \<and> Q T} (f S)\<close>
  using assms unfolding fun_rel_def nres_rel_def
  by (auto simp add: pw_conc_inres pw_conc_nofail pw_ords_iff(1))

lemma TT':
  assumes \<open>f \<le> \<Down> R g\<close> and \<open>g \<le> \<Down> R' h\<close>
  shows \<open>f \<le> \<Down> (R O R') h\<close>
  by (metis (full_types) assms(1) assms(2) conc_fun_chain ref_two_step)

thm TT'[OF backtrack_l'_spec backtrack_l_spec[THEN refine_pair_to_SPEC]]

lemma cdcl_twl_o_prog_l_spec:
  \<open>(cdcl_twl_o_prog_l', cdcl_twl_o_prog) \<in>
    {(S, S'). S' = twl_st_of None S \<and>
       working_queue_l S = {#} \<and> pending_l S = {#} \<and> no_step cdcl_twl_cp (twl_st_of None S) \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S) \<and> additional_WS_invs S} \<rightarrow>
    \<langle>{((brk, T), (brk', T')). T' = twl_st_of None T \<and> brk = brk' \<and> additional_WS_invs T \<and>
    (get_conflict_l T \<noteq> None \<longrightarrow> get_conflict_l T = Some [])\<and>
       twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
       working_queue_l T = {#} (* \<and>
       (\<not>brk \<longrightarrow> pending_l T \<noteq> {#}) *)}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have twl_prog:
    \<open>(cdcl_twl_o_prog_l', cdcl_twl_o_prog) \<in> ?R \<rightarrow>
      \<langle>{(S, S').
         (fst S' = (fst S) \<and> snd S' = twl_st_of None (snd S)) \<and> additional_WS_invs (snd S) \<and>
           working_queue_l (snd S) = {#}}\<rangle> nres_rel\<close>
    apply clarify
    unfolding cdcl_twl_o_prog_l'_def cdcl_twl_o_prog_def
    apply (refine_vcg decide_l_spec[THEN refine_pair_to_SPEC]
        skip_and_resolve_loop_l_spec[THEN refine_pair_to_SPEC]
        TT'[OF backtrack_l'_spec backtrack_l_spec[THEN refine_pair_to_SPEC]];
        remove_dummy_vars)
    subgoal by simp
    subgoal by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by simp
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by auto
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (auto simp add: get_conflict_l_Some_nil_iff)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      by (cases T) (auto)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T T'
      by fast
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q'
      by (simp add: get_conflict_l_get_conflict)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: additional_WS_invs_def)
    subgoal for M N U NP UP WS Q M' N' U' NP' UP' WS' Q' _ _ T
      apply (cases M; cases T)
      by (auto simp add: (* additional_WS_invs_def *))
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by fast
    subgoal by simp
    subgoal by simp
    done
  have KK:
    \<open>get_conflict_l T = None \<longleftrightarrow> get_conflict (twl_st_of None T) = None\<close>
    \<open>pending_l T = {#} \<longleftrightarrow> pending (twl_st_of None T) = {#}\<close>
    for T
    by (cases T; auto)+
  text \<open>Stupid placeholder to help the application of \<open>rule\<close> later:\<close>
  define TT where [simp]: \<open>TT = (\<lambda>_::bool \<times> 'a twl_st_l. True)\<close>
  let ?J' = \<open>{(U, U').
       (fst U' = id (fst U) \<and> snd U' = twl_st_of None (snd U)) \<and> (additional_WS_invs (snd U) \<and>
         working_queue_l (snd U) = {#}) \<and>
        (get_conflict (twl_st_of None (snd U)) \<noteq> None \<longrightarrow> get_conflict (twl_st_of None (snd U)) = Some {#}) \<and>
         twl_struct_invs (twl_st_of None (snd U)) \<and>
         twl_stgy_invs (twl_st_of None (snd U)) (* \<and>
         (\<not>fst U \<longrightarrow> pending (twl_st_of (snd U)) \<noteq> {#}) *)}\<close>

  have J: \<open>?J = ?J'\<close>
    by auto
  show bt': ?thesis
    unfolding J
    apply (rule refine_add_inv_pair)
    subgoal
      using twl_prog by auto
    subgoal for S
      apply (rule weaken_SPEC[OF cdcl_twl_o_prog_spec[of \<open>twl_st_of None S\<close>]])
      apply (auto simp: KK(2))[5]
      apply auto
      done
    done
qed


definition cdcl_twl_stgy_prog_l' :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>cdcl_twl_stgy_prog_l' S\<^sub>0 =
  do {
    do {
      (brk, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(brk, T). twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
        (brk \<longrightarrow> no_step cdcl_twl_stgy (twl_st_of None T)) \<and> cdcl_twl_stgy\<^sup>*\<^sup>* (twl_st_of None S\<^sub>0) (twl_st_of None T) \<and>
        working_queue_l T = {#} \<and>
        (\<not>brk \<longrightarrow> get_conflict_l T = None)\<^esup>
        (\<lambda>(brk, _). \<not>brk)
        (\<lambda>(brk, S).
        do {
          T \<leftarrow> unit_propagation_outer_loop_l S;
          cdcl_twl_o_prog_l' T
        })
        (False, S\<^sub>0);
      RETURN T
    }
  }
  \<close>


lemma cdcl_twl_stgy_prog_l'_spec:
  \<open>(cdcl_twl_stgy_prog_l', cdcl_twl_stgy_prog) \<in>
    {(S, S'). S' = twl_st_of None S \<and> additional_WS_invs S \<and>
       working_queue_l S = {#} \<and>
       twl_struct_invs (twl_st_of None S) \<and> twl_stgy_invs (twl_st_of None S)} \<rightarrow>
    \<langle>{(T, T'). T' = twl_st_of None T \<and> True}\<rangle> nres_rel\<close>
  (is \<open> _ \<in> ?R \<rightarrow> ?I\<close> is \<open> _ \<in> ?R \<rightarrow> \<langle>?J\<rangle>nres_rel\<close>)
proof -
  have R: \<open>(a, b) \<in> ?R \<Longrightarrow> ((False, a), (False, b)) \<in> {((brk, S), (brk', S')). brk = brk' \<and> (S, S') \<in> ?R}\<close>
    for a b by auto
  have KK:
    \<open>get_conflict_l T = None \<longleftrightarrow> get_conflict (twl_st_of None T) = None\<close>
    \<open>pending_l T = {#} \<longleftrightarrow> pending (twl_st_of None T) = {#}\<close>
    for T
    by (cases T; auto)+
  show ?thesis
    unfolding cdcl_twl_stgy_prog_l'_def cdcl_twl_stgy_prog_def
    apply (refine_rcg R cdcl_twl_o_prog_l_spec[THEN refine_pair_to_SPEC_fst_pair2]
        unit_propagation_outer_loop_l_spec[THEN refine_pair_to_SPEC]; remove_dummy_vars)
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by fastforce
    subgoal unfolding KK by fastforce
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal unfolding KK by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: additional_WS_invs_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal unfolding KK by auto
    subgoal by (auto simp: pending_l_pending)
    subgoal by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


lemma cdcl_twl_stgy_prog_l'_spec_final:
  assumes \<open>twl_struct_invs (twl_st_of None S)\<close> and \<open>twl_stgy_invs (twl_st_of None S)\<close> and
    \<open>working_queue_l S = {#}\<close> and
    \<open>get_conflict_l S = None\<close> and \<open>additional_WS_invs S\<close>
  shows
    \<open>cdcl_twl_stgy_prog_l' S \<le> SPEC(\<lambda>T. full cdcl_twl_stgy (twl_st_of None S) (twl_st_of None T))\<close>
  apply (rule order_trans[OF cdcl_twl_stgy_prog_l'_spec[THEN refine_pair_to_SPEC,
          of S \<open>twl_st_of None S\<close>]])
  using assms apply auto[2]
  apply (rule order_trans)
   apply (rule ref_two_step[OF _ cdcl_twl_stgy_prog_spec[of \<open>twl_st_of None S\<close>],
        of _ \<open>{(S, S'). S' = twl_st_of None S \<and> True}\<close>])
  using assms by (auto simp: full_def pending_l_pending get_conflict_l_get_conflict
      pw_conc_inres pw_conc_nofail pw_ords_iff(1))

schematic_goal backtrack_l'_impl: "RETURN ?c \<le> backtrack_l' S"
  unfolding backtrack_l'_def _def Let_def
  apply (refine_transfer find_unwatched_impl)
  done


schematic_goal unit_propagation_inner_loop_body_l_impl:
  "RETURN ?c \<le> unit_propagation_inner_loop_body_l L C S"
  unfolding unit_propagation_inner_loop_body_l_def _def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

schematic_goal unit_propagation_inner_loop_l_impl: "RETURN ?c \<le> unit_propagation_inner_loop_l L S"
  unfolding unit_propagation_inner_loop_l_def _def Let_def
  apply (refine_transfer unit_propagation_inner_loop_body_l_impl)
  done

schematic_goal unit_propagation_outer_loop_l_impl: "RETURN ?c \<le> unit_propagation_outer_loop_l S"
  unfolding unit_propagation_outer_loop_l_def _def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

schematic_goal cdcl_twl_stgy_prog_l'_impl: "RETURN ?c \<le> cdcl_twl_stgy_prog_l' S"
  unfolding cdcl_twl_stgy_prog_l'_def _def Let_def
  apply (refine_transfer find_unwatched_impl)
  done

concrete_definition backtrack_l'_impl uses cdcl_twl_stgy_prog_l'

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (SML) CDCL_W_Level

prepare_code_thms backtrack_l'_impl_def
export_code backtrack_l'_impl in SML
end