theory CDCL_Two_Watched_Literals_Code_Common
  imports "Partial_Annotated_Clausal_Logic" IICF
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

instance annotated_lit :: (heap, heap, heap) heap
proof standard
  let ?f = \<open>\<lambda>L:: ('a, 'b, 'c) annotated_lit.
      (if is_decided L then Some (lit_dec L) else None,
       if is_decided L then None else Some (lit_prop L), if is_decided L then None else Some (mark_of L))\<close>
    term ?f
  have f: \<open>inj ?f\<close>
    unfolding inj_on_def Ball_def
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then have Hf: \<open>?f x = ?f s \<longleftrightarrow> x = s\<close> for s x
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>OFCLASS('a option \<times> 'b option \<times> 'c option, heap_class)\<close>
   by standard
  then obtain g :: \<open>'a option \<times> 'b option \<times> 'c option \<Rightarrow> nat\<close> where g: \<open>inj g\<close>
    by blast
  then have H: \<open>g (x, y) = g (s, t) \<longleftrightarrow> x = s \<and> y = t\<close> for s t x y
    unfolding inj_on_def Ball_def comp_def by blast
  have \<open>inj (g o ?f)\<close>
    using f g unfolding inj_on_def Ball_def comp_def H Hf
    apply (intro allI impI)
    apply (rename_tac x y, case_tac x; case_tac y)
    by auto
  then show \<open>\<exists>to_nat:: ('a, 'b, 'c) annotated_lit \<Rightarrow> nat. inj to_nat\<close>
    by blast
qed


subsection \<open>Declaration of some Operators and Implementation\<close>

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


text \<open>Some functions and types:\<close>
abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat literal \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> (id_assn :: nat literal \<Rightarrow> _)\<close>

abbreviation nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> (nat, nat) ann_lit \<Rightarrow> assn" where
  \<open>nat_ann_lit_assn \<equiv> (id_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>

abbreviation nat_ann_lits_assn :: "ann_lits_l \<Rightarrow> ann_lits_l \<Rightarrow> assn" where
  \<open>nat_ann_lits_assn \<equiv> list_assn nat_ann_lit_assn\<close>

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
  by (sep_auto split: annotated_lit.splits)

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
  by (cases L') (auto dest!: literal_is_lit_of_decided simp: atm_of_eq_atm_of)

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

end