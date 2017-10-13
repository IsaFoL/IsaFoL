theory CDCL_Two_Watched_Literals_Code_Common
  imports CDCL_Two_Watched_Literals_Initialisation
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

instantiation literal :: (default) default
begin
definition default_literal where
\<open>default_literal = Pos default\<close>
instance by standard
end


subsection \<open>Declaration of some Operators and Implementation\<close>

sepref_decl_op nat_lit_eq: "op = :: nat literal \<Rightarrow> nat literal \<Rightarrow> bool" ::
  "(Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> (Id :: (bool \<times> _) set)" .

lemma [def_pat_rules]:
  "op = $ a $ b \<equiv> op_nat_lit_eq $ a $ b"
  by auto

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


type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>

context
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI] frefI
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def
begin

lemma option_bool_eq_impl_option_op_bool_eq_impl: \<open>option_bool_eq_impl = op_option_bool_eq\<close>
  unfolding option_bool_eq_impl_def op_option_bool_eq_def by (auto split: option.splits intro!: ext)

lemma option_bool_eq_refine[sepref_fr_rules]:
  \<open>(uncurry (return oo (op =)), uncurry (RETURN oo op_option_bool_eq)) \<in>
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

section \<open>Code for the initialisation of the Data Structure\<close>

definition init_dt_step_l :: \<open>'v clause_l \<Rightarrow> 'v twl_st_l \<Rightarrow> ('v twl_st_l) nres\<close> where
  \<open>init_dt_step_l C S = do {
   (let (M, N, U, D, NP, UP, WS, Q) = S in
   (case D of
    None \<Rightarrow>
    if length C = 1
    then do {
      ASSERT (no_dup M);
      ASSERT (C \<noteq> []);
      let L = hd C;
      let val_L = polarity M L;
      if val_L = None
      then do {RETURN (Propagated L 0 # M, N, U, None, add_mset {#L#} NP, UP, WS, add_mset (-L) Q)}
      else
        if val_L = Some True
        then do {RETURN (M, N, U, None, add_mset {#L#} NP, UP, WS, Q)}
        else do {RETURN (M, N, U, Some (mset C), add_mset {#L#} NP, UP, {#}, {#})}
      }
    else do {
      ASSERT(C \<noteq> []);
      ASSERT(tl C \<noteq> []);
      RETURN (M, N @ [C], length N, None, NP, UP, WS, Q)}
  | Some D \<Rightarrow>
    if length C = 1
    then do {
      ASSERT (C \<noteq> []);
      let L = hd C;
      RETURN (M, N, U, Some D, add_mset {#L#} NP, UP, {#}, {#})}
    else do {
      ASSERT(C \<noteq> []);
      ASSERT(tl C \<noteq> []);
      RETURN (M, N @ [C], length N, Some D, NP, UP, {#}, {#})}))
  }\<close>

lemma length_ge_Suc_0_tl_not_nil: \<open>length C > Suc 0 \<Longrightarrow> tl C \<noteq> []\<close>
  by (cases C) auto

lemma init_dt_step_init_dt_step_l:
  assumes
    le_C: \<open>length C \<ge> 1\<close> and
    struct_invs: \<open>twl_struct_invs (twl_st_of None S)\<close>
  shows \<open>RETURN (init_dt_step C S) = init_dt_step_l C S\<close>
proof -
  have \<open>no_dup (trail (state\<^sub>W_of (twl_st_of None S)))\<close>
    using struct_invs unfolding twl_struct_invs_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by fast
  then have n_d: \<open>no_dup (get_trail_l S)\<close>
    by (cases S) (auto simp add: cdcl\<^sub>W_restart_mset_state)

  have tl_C_nempty: \<open>tl C \<noteq> []\<close> if \<open>length C \<noteq> Suc 0\<close>
    using le_C that by (cases C) auto
  show ?thesis
    using n_d le_C unfolding init_dt_step_def init_dt_step_l_def Let_def
    by (cases S) (auto simp: polarity_def length_ge_Suc_0_tl_not_nil split: option.splits cong: bind_cong
        dest!: tl_C_nempty)
qed

definition init_dt_l where
  \<open>init_dt_l CS S = nfoldli CS (\<lambda>_. True) init_dt_step_l S\<close>

lemma init_dt_init_dt_l:
  assumes
    \<open>\<forall>C \<in> set CS. distinct C\<close> and
    \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    \<open>twl_struct_invs (twl_st_of None S)\<close> and
    \<open>clauses_to_update_l S = {#}\<close> and
    \<open>\<forall>s\<in>set (get_trail_l S). \<not>is_decided s\<close> and
    \<open>get_conflict_l S = None \<longrightarrow> literals_to_update_l S = uminus `# lit_of `# mset (get_trail_l S)\<close> and
    \<open>additional_WS_invs S\<close> and
    \<open>get_learned_l S = length (get_clauses_l S) - 1\<close> and
    \<open>twl_stgy_invs (twl_st_of None S)\<close>
  shows \<open>RETURN (init_dt CS S) = init_dt_l (rev CS) S\<close>
  using assms unfolding init_dt_l_def
proof (induction CS)
  case Nil
  then show ?case by simp
next
  case (Cons a CS)
  then have IH: \<open>RETURN (init_dt CS S) = nfoldli (rev CS) (\<lambda>_. True) init_dt_step_l S\<close>
    by auto
  have [simp]: \<open>nfoldli [] (\<lambda>_. True) init_dt_step_l = (\<lambda>S. RETURN S)\<close>
    by (auto intro!: ext)
  have step:
    \<open>RETURN (init_dt_step a (init_dt CS S)) = init_dt_step_l a (init_dt CS S)\<close>
    apply (rule init_dt_step_init_dt_step_l)
    subgoal using Cons(3) by auto
    subgoal by (rule init_dt_full[of CS S]) (use Cons(2-) in \<open>solves simp\<close>)+
    done
  show ?case
    by (auto simp: IH[symmetric] step)
qed

end