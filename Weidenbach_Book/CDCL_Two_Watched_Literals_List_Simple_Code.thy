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

abbreviation nat_lits_trail_assn :: "(nat, nat) ann_lits \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> assn" where
  \<open>nat_lits_trail_assn \<equiv> (id_assn :: (nat, nat) ann_lits \<Rightarrow> _)\<close>

abbreviation clause_l_assn :: "nat clause_l \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses_l \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_assn clause_l_assn\<close>


notation prod_assn (infixr "*assn" 90)
abbreviation twl_st_ll_assn :: \<open>nat twl_st_l \<Rightarrow> twl_st_ll \<Rightarrow> assn\<close> where
\<open>twl_st_ll_assn \<equiv>
 nat_lits_trail_assn *assn clauses_l_assn *assn nat_assn *assn
 option_assn clause_l_assn *assn
 list_mset_assn (list_mset_assn nat_lit_assn) *assn
 list_mset_assn (list_mset_assn nat_lit_assn) *assn
 list_mset_assn nat_assn *assn
 list_mset_assn nat_lit_assn
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

definition test42 :: "nat literal \<Rightarrow> nat \<Rightarrow> nat twl_st_l \<Rightarrow> nat twl_st_l nres" where
  \<open>test42 L C S = do {
    let (M, N, U, D, NP, UP, WS, Q) = S;
    ASSERT(C < length N);
    ASSERT(0 < length (N!C));
    let (i::nat) = (if (N!C) ! 0 = L then 0 else 1);
    ASSERT(i < length (N!C));
    let L = (N!C) ! i;
    ASSERT(1-i < length (N!C));
    let L' = (N!C) ! (1 - i);
     ASSERT(no_dup M);
   let val_L' = valued M L';
 (*    if valued M L' = Some True then RETURN (M, N, U, D, NP, UP, WS, Q)
    else RETURN (M, N, U, D, NP, UP, WS, Q) *)
     if val_L' = Some True
    then RETURN (M, N, U, D, NP, UP, WS, Q)
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

lemma unification_is_stupid_in_isabelle: \<open>valued_impl' a (aa ! bia ! Suc 0) \<bind>
       (\<lambda>x'g. return (a, aa, ab, ac, ad, ae, af, b)) =
       (\<lambda>ai bia (a, aa, ab, ac, ad, ae, af, b). valued_impl' a (aa ! bia ! Suc 0) \<bind>
       (\<lambda>x'g. return (a, aa, ab, ac, ad, ae, af, b))) ai bia (a, aa, ab, ac, ad, ae, af, b)\<close>
  by auto


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

lemmas rel_id_simps =
  fun_rel_id_simp
  prod_rel_id_simp
  option_rel_id_simp
  sum_rel_id_simp
  list_rel_id_simp
  set_rel_id_simp

lemmas [sepref_frame_normrel_eqs] = rel_id_simps[symmetric]

sepref_definition test_42' is \<open>uncurry2 (unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close> ::
  \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding unit_propagation_inner_loop_body_l_def unfolding lms_fold_custom_empty
  supply [[goals_limit=1]]
  by sepref

concrete_definition unit_propagation_inner_loop_body_l_impl uses test_42'.refine_raw

code_identifier
  code_module DPLL_CDCL_W_Implementation \<rightharpoonup> (SML) CDCL_W_Level

prepare_code_thms unit_propagation_inner_loop_body_l_impl_def
export_code unit_propagation_inner_loop_body_l_impl in SML

(* sepref_dbg_trans_step_keep
apply (simp add: list_assn_pure_conv; fail)*)

thm Sepref_Id_Op.def_pat_rules
term \<open>uncurry2 (unit_propagation_inner_loop_body_l :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close>
term unit_propagation_inner_loop_body_l

sepref_definition unit_propagation_inner_loop_body_l_impl is \<open>uncurry2 (unit_propagation_inner_loop_body_l' :: nat literal \<Rightarrow> nat \<Rightarrow>
  nat twl_st_l \<Rightarrow> nat twl_st_l nres)\<close> ::
  \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a twl_st_ll_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_ll_assn\<close>
  unfolding unit_propagation_inner_loop_body_l'_def(* 
  apply (sepref ) *)
  apply sepref_dbg_keep
  -- \<open>This prints a trace of the different phases of sepref, and stops when the first phase fails.
    It then returns the internal proof state of the tool, which can be inspected further.

    Here, the translation phase fails. The translation phase translates the control structures and operations of
    the abstract program to their concrete counterparts. To inspect the actual problem, we let translation run
    until the operation where it fails: \<close>
  supply [[goals_limit=5]] -- \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
  apply sepref_dbg_trans_keep
  -- \<open>Things get stuck at a goal with predicate @{const hn_refine}. This is the internal refinement predicate,
    @{term "hn_refine \<Gamma> c \<Gamma>' R a"} means, that, for operands whose refinement is described by @{term \<Gamma>},
    the concrete program @{term c} refines the abstract program @{term a}, such that, afterwards, the operands
    are described by @{term \<Gamma>'}, and the results are refined by @{term R}.

    Inspecting the first subgoal reveals that we got stuck on refining the abstract operation
    @{term "RETURN $ (op_list_get $ b $ xf)"}. Note that the @{term "op $"} is just a constant for function
    application, which is used to tame Isabelle's higher-order unification algorithms. You may use
    \<open>unfolding APP_def\<close>, or even \<open>simp\<close> to get a clearer picture of the failed goal.

    If a translation step fails, it may be helpful to execute as much of the translation step as possible:
    \<close>
  -- \<open>The translation step gets stuck at proving @{term "pre_list_get (b, xf)"}, which is the
    precondition for list indexing.\<close>
  apply sepref_dbg_trans_step_keep
                      apply sepref_dbg_trans_step_keep

  apply (simp add: list_assn_pure_conv)
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
(*   
  apply (sepref_dbg_side_keep) *)
oops

lemma \<open>hn_val Id a1' a1 \<Longrightarrow>\<^sub>t hn_ctxt nat_ann_lits_assn a1' a1\<close>
  by (simp add: list_assn_pure_conv)
definition backtrack_l' :: "'v twl_st_l \<Rightarrow> 'v twl_st_l nres" where
  \<open>backtrack_l' S\<^sub>0 =
    do {
      let (M, N, U, D, NP, UP, WS, Q) = S\<^sub>0 in
      do {
        ASSERT(M \<noteq> []);
        let L = lit_of (hd M);
        let j = snd (the (find_level_decomp M (the D) [] (count_decided M)));
        let M1 = tl (the (bt_cut j M));

        if length (the D) > 1
        then do {
          let L' = the (find (\<lambda>L'.  get_level M L' = get_maximum_level M (mset (the D) - {#-L#})) (the D));
          RETURN (Propagated (-L) (length N) # M1,
            N @ [[-L, L'] @ (remove1 (-L) (remove1 L' (the D)))], U,
            None, NP, UP, WS, {#L#})
        }
        else do {
          RETURN (Propagated (-L) 0 # M1, N, U, None, NP, add_mset (mset (the D)) UP, WS, {#L#})
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