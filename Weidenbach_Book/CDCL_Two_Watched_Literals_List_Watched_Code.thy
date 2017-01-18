theory CDCL_Two_Watched_Literals_List_Watched_Code
  imports CDCL_Two_Watched_Literals_List_Watched Array_Array_List
begin

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


section \<open>Code Generation\<close>

subsection \<open>Literals as Natural Numbers\<close>

text \<open>
  Modeling \<^typ>\<open>nat literal\<close> via the transformation associating \<^term>\<open>2*n\<close> or \<^term>\<open>2*n+1\<close>
  has some advantages over the transformation to positive or negative integers: 0 is not an issue.\<close>

fun nat_of_lit :: \<open>nat literal \<Rightarrow> nat\<close> where
  \<open>nat_of_lit (Pos L) = 2*L\<close>
| \<open>nat_of_lit (Neg L) = 2*L + 1\<close>

lemma nat_of_lit_def: \<open>nat_of_lit L = (if is_pos L then 2*atm_of L else 2*atm_of L + 1)\<close>
  by (cases L) auto

fun literal_of_nat :: \<open>nat \<Rightarrow> nat literal\<close> where
  \<open>literal_of_nat n = (if even n then Pos (n div 2) else Neg (n div 2))\<close>

lemma lit_of_nat_nat_of_lit[simp]: \<open>literal_of_nat (nat_of_lit L) = L\<close>
  by (cases L) auto

lemma nat_of_lit_lit_of_nat[simp]: \<open>nat_of_lit (literal_of_nat n) = n\<close>
  by auto

lemma atm_of_lit_of_nat: \<open>atm_of (literal_of_nat n) = n div 2\<close>
  by auto

text \<open>There is probably a more-``closed'' form from the following theorem, but it is unclear if
  that is useful or not.\<close>
lemma uminus_lit_of_nat:
  \<open>- (literal_of_nat n) = (if even n then literal_of_nat (n+1) else literal_of_nat (n-1))\<close>
  by (auto elim!: oddE)

definition lit_of_natP where
  \<open>lit_of_natP L L' \<longleftrightarrow> literal_of_nat L = L'\<close>

abbreviation lit_of_nat_rel where
  \<open>lit_of_nat_rel \<equiv> p2rel lit_of_natP\<close>

definition nat_nat_lit_assn :: "nat literal \<Rightarrow> nat \<Rightarrow> assn" where
  \<open>nat_nat_lit_assn = pure (p2rel lit_of_natP)\<close>

fun pair_of_ann_lit :: "('a, 'b) ann_lit \<Rightarrow> 'a literal \<times> 'b option" where
  \<open>pair_of_ann_lit (Propagated L D) = (L, Some D)\<close>
| \<open>pair_of_ann_lit (Decided L) = (L, None)\<close>

fun ann_lit_of_pair :: "'a literal \<times> 'b option \<Rightarrow> ('a, 'b) ann_lit" where
  \<open>ann_lit_of_pair (L, Some D) = Propagated L D\<close>
| \<open>ann_lit_of_pair (L, None) = Decided L\<close>

lemma ann_lit_of_pair_pair_of_ann_lit: \<open>ann_lit_of_pair (pair_of_ann_lit L) = L\<close>
  by (cases L) auto

lemma pair_of_ann_lit_ann_lit_of_pair: \<open>pair_of_ann_lit (ann_lit_of_pair L) = L\<close>
  by (cases L; cases \<open>snd L\<close>) auto

definition pair_nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> (nat \<times> nat option) \<Rightarrow> assn" where
  \<open>pair_nat_ann_lit_assn = pure ({(a, b). b = ann_lit_of_pair ((\<lambda>(a,b). (literal_of_nat a, b)) a)})\<close>


subsection \<open>State Conversion\<close>

subsubsection \<open>Refinement of the Watched Function\<close>

definition watched_rel :: "('a \<Rightarrow> 'b) \<Rightarrow> nat clauses_l \<Rightarrow> ('a list \<times> (nat literal \<Rightarrow> 'b)) set" where
  \<open>watched_rel R N =
    (br (\<lambda>W. (\<lambda>L. R (W!(nat_of_lit L))))
        (\<lambda>W. \<forall>L \<in># lits_of_atms_of_mm (mset `# mset N). nat_of_lit L < length W))\<close>

term \<open>br (\<lambda>W. (\<lambda>L. R (W!(nat_of_lit L))))\<close>

text \<open>Some functions and types:\<close>

abbreviation nat_lit_assn :: "nat literal \<Rightarrow> nat literal \<Rightarrow> assn" where
  \<open>nat_lit_assn \<equiv> (id_assn :: nat literal \<Rightarrow> _)\<close>

abbreviation nat_ann_lit_assn :: "(nat, nat) ann_lit \<Rightarrow> (nat, nat) ann_lit \<Rightarrow> assn" where
  \<open>nat_ann_lit_assn \<equiv> (id_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

type_synonym ann_lits_l = \<open>(nat, nat) ann_lits\<close>
type_synonym working_queue_ll = "nat list"
type_synonym lit_queue_l = "nat literal list"
type_synonym nat_trail = \<open>(nat \<times> nat option) array_list\<close>
type_synonym clause_wl = \<open>nat array_list\<close>
type_synonym clauses_wl = \<open>nat array_list array_list\<close>
type_synonym watched_wl = \<open>nat array_list array\<close>

abbreviation nat_ann_lits_assn :: "ann_lits_l \<Rightarrow> ann_lits_l \<Rightarrow> assn" where
  \<open>nat_ann_lits_assn \<equiv> list_assn nat_ann_lit_assn\<close>

abbreviation nat_lits_trail_assn :: "ann_lits_l \<Rightarrow> (nat \<times> nat option) array_list \<Rightarrow> assn" where
  \<open>nat_lits_trail_assn \<equiv> arl_assn (pair_nat_ann_lit_assn :: (nat, nat) ann_lit \<Rightarrow> _)\<close>

abbreviation clause_ll_assn :: "nat clause_l \<Rightarrow> clause_wl \<Rightarrow> assn" where
  \<open>clause_ll_assn \<equiv> arl_assn nat_nat_lit_assn\<close>

abbreviation clauses_ll_assn :: "nat clauses_l \<Rightarrow> clauses_wl \<Rightarrow> assn" where
  \<open>clauses_ll_assn \<equiv> arl_assn clause_ll_assn\<close>

abbreviation clause_l_assn :: "nat clause \<Rightarrow> nat clause_l \<Rightarrow> assn" where
  \<open>clause_l_assn \<equiv> list_mset_assn nat_lit_assn\<close>

abbreviation clauses_l_assn :: "nat clauses \<Rightarrow> nat clauses_l \<Rightarrow> assn" where
  \<open>clauses_l_assn \<equiv> list_mset_assn clause_l_assn\<close>

abbreviation working_queue_l_assn :: "nat multiset \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_l_assn \<equiv> list_mset_assn nat_assn\<close>

abbreviation working_queue_ll_assn :: "nat list \<Rightarrow> nat list \<Rightarrow> assn" where
  \<open>working_queue_ll_assn \<equiv> list_assn nat_assn\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

type_synonym twl_st_wll =
  "nat_trail \<times> clauses_wl \<times> nat \<times>
      clause_wl option \<times> nat clauses_l \<times> nat clauses_l \<times> lit_queue_l \<times> watched_wl"

notation prod_assn (infixr "*assn" 90)
term \<open>array_watched_assn N\<close>

locale test =
  fixes N :: \<open>nat literal list list\<close>
begin

definition map_fun_rel :: "(nat \<times> nat literal) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> (nat literal \<Rightarrow> 'a)) set" where
  \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

definition map_fun_rel_assn :: "(nat \<times> nat literal) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> (nat literal \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> assn" where
  \<open>map_fun_rel_assn D R = pure (\<langle>the_pure R\<rangle>map_fun_rel D)\<close>

lemma [safe_constraint_rules]: \<open>is_pure (map_fun_rel_assn D R)\<close>
  unfolding map_fun_rel_assn_def by auto

term array_assn
term \<open>hr_comp is_array_list (\<langle>the_pure A\<rangle>list_rel)\<close>
term \<open>\<lambda>Q. hr_comp Q (the_pure (map_fun_rel_assn D (arl_assn R)))\<close>
term \<open>\<lambda>Q. hr_comp (map_fun_rel_assn D (arl_assn R)) Q\<close>

term \<open>hr_comp (array_assn (arl_assn id_assn)) (\<langle>Id\<rangle>map_fun_rel D)\<close>
  term \<open>array_assn\<close>
term \<open>the_pure (list_assn (arl_assn R))\<close>
term \<open>hr_comp (list_assn (hr_comp is_array_list (\<langle>the_pure A\<rangle>list_rel)))\<close>
term \<open>\<lambda>Q. hr_comp ((hr_comp is_array (\<langle>the_pure (hr_comp is_array_list (\<langle>the_pure A\<rangle>list_rel))\<rangle>list_rel)))
  (the_pure Q) a b\<close>
term \<open>map_fun_rel D (the_pure (arl_assn R))\<close>
term \<open>the_pure (array_assn G)\<close>
definition max_index where
\<open>max_index = MMax (nat_of_lit `# lits_of_atms_of_mm (mset `# mset N))\<close>

(* abbreviation array_watched_assn :: "(nat literal \<Rightarrow> nat list) \<Rightarrow>
    nat array_list array \<Rightarrow> assn" where
  \<open>array_watched_assn W \<equiv>
      array_assn (arl_assn nat_assn) (map (W o lit_of_nat) [0..<max_index])\<close> *)
abbreviation D where
  \<open>D \<equiv> (\<lambda>L. (nat_of_lit L, L)) ` set_mset (lits_of_atms_of_mm (mset `# mset N))\<close>

abbreviation array_watched_assn :: "(nat literal \<Rightarrow> nat list) \<Rightarrow> (nat array \<times> nat) array  \<Rightarrow> assn" where
  \<open>array_watched_assn \<equiv> hr_comp (arrayO (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D)\<close>
term hr_comp
  term \<open>Array.nth\<close>
term \<open>(hrp_comp (is_array_list, list_assn id_assn) (\<langle>Id\<rangle>map_fun_rel D))\<close>
term \<open>hr_comp (array_assn (list_assn id_assn)) (\<langle>Id\<rangle>map_fun_rel D)\<close>
term \<open>(\<langle>\<langle>R\<rangle>list_rel\<rangle>map_fun_rel D)\<close>
term \<open>(hr_comp (array_assn (list_assn (arl_assn (list_assn id_assn)))) (\<langle>R\<rangle>map_fun_rel D))\<close>
term \<open>hr_comp (array_assn (arl_assn nat_assn)) (\<langle>Id\<rangle>map_fun_rel D)\<close>
term \<open>hrp_comp (is_array, list_assn (fst (hrp_comp (is_array_list, list_assn
nat_assn) S))) T\<close>
term list_assn
term \<open>array_assn\<close>
definition twl_st_l_assn :: \<open>nat twl_st_wl \<Rightarrow> twl_st_wll \<Rightarrow> assn\<close> where
\<open>twl_st_l_assn \<equiv>
  (nat_lits_trail_assn *assn clauses_ll_assn *assn nat_assn *assn
  option_assn clause_ll_assn *assn
  clauses_l_assn *assn
  clauses_l_assn *assn
  clause_l_assn *assn
  array_watched_assn
  )\<close>


definition truc_muche :: \<open>nat twl_st_wl \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>truc_muche S = do {RETURN S}\<close>

sepref_register \<open>watched_by :: nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>
   :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> watched\<close>

definition watched_by_nth :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_by_nth = (\<lambda>(M, N, U, D, NP, UP, Q, W) L i. W L ! i)\<close>

term p2rel
sepref_decl_intf i_my_watched is "nat literal \<Rightarrow> nat list"
thm map_type_eqI[of "TYPE(nat literal literal \<Rightarrow> nat list)" "TYPE(i_my_watched)"]

definition watched_app :: \<open>(nat literal \<Rightarrow> nat list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>watched_app M L i \<equiv> M L ! i\<close>

sepref_decl_op watched_app: \<open>watched_app ::(nat literal \<Rightarrow> nat list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat\<close> ::
  \<open>(Id :: ((nat literal \<Rightarrow> nat list) \<times> _) set) \<rightarrow> (Id :: (nat literal \<times> _) set) \<rightarrow> nat_rel \<rightarrow>
     nat_rel\<close>
  .

thm nth_aa_hnr[unfolded hoare_triple_def, simplified]
lemma [def_pat_rules]:
  \<open>watched_app $ M $ L $ i \<equiv> op_watched_app $ M $ L $ i\<close>
  by (auto simp: watched_app_def)

lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_ll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in> snd ` D]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D) \<times>\<^sub>r p2rel lit_of_natP) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_ll_def
  by (fastforce simp: fref_def map_fun_rel_def[abs_def] relAPP_def prod_rel_def_internal
      nres_rel_def_internal p2rel_def lit_of_natP_def
      simp del: (* literal_of_nat.simps *))

lemma literal_of_neq_eq_nat_of_lit_eq_iff: \<open>literal_of_nat b = L \<longleftrightarrow> b = nat_of_lit L\<close>
  by (auto simp del: literal_of_nat.simps)

lemma nat_of_lit_eq_iff[iff]: \<open>nat_of_lit xa = nat_of_lit x \<longleftrightarrow> x = xa\<close>
  apply (cases x; cases xa) by auto presburger+


lemma \<open>(uncurry2 nth_aa, uncurry2 (RETURN ooo watched_app)) \<in>
   [\<lambda>((W, L), i). L \<in> snd ` D \<and> i < length (W L)]\<^sub>a array_watched_assn\<^sup>k *\<^sub>a nat_nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  (is \<open>?c \<in> [?pre]\<^sub>a ?im \<rightarrow> ?f\<close>)
proof -
  have P: \<open>is_pure nat_assn\<close>
    by auto
  have \<open>(uncurry2 nth_aa, uncurry2 (RETURN \<circ>\<circ>\<circ> watched_app))
  \<in> [comp_PRE ((\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r nat_rel)
       (\<lambda>((W, L), i). L \<in> snd ` D)
       (\<lambda>_ ((l, i), j). i < length l \<and> j < length (l ! i))
       (\<lambda>_. True)]\<^sub>a hrp_comp
                       ((arrayO (arl_assn nat_assn))\<^sup>k *\<^sub>a
                        nat_assn\<^sup>k *\<^sub>a
                        nat_assn\<^sup>k)
                       ((\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel) \<times>\<^sub>r
                        nat_rel) \<rightarrow> hr_comp nat_assn nat_rel\<close>
    (is \<open>_ \<in> [?pre']\<^sub>a ?im' \<rightarrow> ?f'\<close>)
    using hfref_compI_PRE_aux[OF nth_aa_hnr nth_ll_watched_app, OF P] .
  note H = hfref_compI_PRE_aux[OF nth_aa_hnr nth_ll_watched_app, OF P]
  have \<open>(\<forall>aa. \<exists>x\<in>#lits_of_atms_of_mm (mset `# mset N).
               nat_of_lit x < length aa \<longrightarrow>
               aa ! nat_of_lit x \<noteq> W x) = False\<close>
    (is \<open>(\<forall>aa. ?P aa) = False\<close>)
    for W :: \<open>nat literal \<Rightarrow> nat list\<close>
  proof -
    define D' where \<open>D' = D\<close>
    define D'' where \<open>D'' = mset_set (snd ` D')\<close>
    let ?f = \<open>(\<lambda>L a. a[nat_of_lit L:= W L])\<close>
    interpret comp_fun_commute ?f
      apply standard
      apply (case_tac \<open>y = x\<close>)
       apply (solves simp)
      apply (intro ext)
        apply (subst (asm) lit_of_nat_nat_of_lit[symmetric])
        apply (subst (asm)(3) lit_of_nat_nat_of_lit[symmetric])
      apply (clarsimp simp only: comp_def intro!: list_update_swap)
      done
    define aa where \<open>aa \<equiv> fold_mset ?f (replicate (1+Max (nat_of_lit ` snd ` D')) [])
     (mset_set (snd ` D'))\<close>
    have length_fold:  \<open>length (fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l M) = length l\<close>
      for l M
      by (induction M) auto
    have length_aa: \<open>length aa = Suc (Max (nat_of_lit ` snd ` D'))\<close>
      unfolding aa_def D''_def[symmetric] by (simp add: length_fold)
    define Ls where \<open>Ls = lits_of_atms_of_mm (mset `# mset N)\<close>
    have H: \<open>x \<in># Ls \<Longrightarrow>
      length l \<ge> Suc  (Max (nat_of_lit ` set_mset Ls)) \<Longrightarrow>
      fold_mset (\<lambda>L a. a[nat_of_lit L := W L]) l (remdups_mset Ls) ! nat_of_lit x = W x\<close>
      for x l
      apply (induction Ls arbitrary: l)
      subgoal by simp
      subgoal for xa Ls l
         apply (case_tac \<open>(nat_of_lit ` set_mset Ls) = {}\<close>)
         apply (solves simp)
        apply (auto simp: nth_list_update_neq less_Suc_eq_le length_fold)
       apply (subst nth_list_update_neq)
        apply (auto simp: less_Suc_eq_le Max.insert)[]
        apply (auto simp: less_Suc_eq_le)[]
        done
      done
    have H': \<open>x \<in># lits_of_atms_of_mm (mset `# mset N) \<Longrightarrow> aa ! nat_of_lit x = W x\<close> for x
      unfolding aa_def D'_def
      by (auto simp: D'_def image_image remdups_mset_def[symmetric]
          less_Suc_eq_le Ls_def[symmetric] intro!: H)
    have \<open>\<not>?P aa\<close>
      by (auto simp: D'_def image_image remdups_mset_def[symmetric]
          less_Suc_eq_le length_aa H')
    then show ?thesis
      by blast
  qed

  then have 1: \<open>?pre' = ?pre\<close>
    apply (auto simp: comp_PRE_def intro!: ext simp: prod_rel_def_internal
        relAPP_def map_fun_rel_def[abs_def] p2rel_def lit_of_natP_def
        literal_of_neq_eq_nat_of_lit_eq_iff
        simp del: literal_of_nat.simps)
      done

  have 2: \<open>?im' = ?im\<close>
    unfolding prod_hrp_comp
    by (auto simp: hrp_comp_def hr_comp_def nat_nat_lit_assn_def)
  have 3: \<open>?f' = ?f\<close>
    by (auto simp: hrp_comp_def hr_comp_def nat_nat_lit_assn_def)

  show ?thesis
    using H unfolding 1 2 3 .
qed

sepref_thm set_of_arrays_ex is "uncurry0 (RETURN (op_list_append [] op_array_empty))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (array_assn nat_assn)"
  unfolding "HOL_list.fold_custom_empty"
  by sepref

lemma list_nth_watched_app:
  \<open>(uncurry (RETURN oo op_list_get), uncurry (RETURN oo watched_app)) \<in>
     [\<lambda>(W, L). L \<in> snd ` D]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel D)) \<times>\<^sub>r lit_of_nat_rel \<rightarrow> \<langle>Id\<rangle> nres_rel\<close>
  by (fastforce simp: fref_def p2rel_def watched_app_def map_fun_rel_def[abs_def] relAPP_def
      prod_rel_def_internal lit_of_natP_def nres_rel_def_internal)
term \<open>\<langle>the_pure (is_array_list)\<rangle>map_fun_rel D\<close>
term \<open>\<langle>Id\<rangle>map_fun_rel D\<close>
term \<open>\<langle>the_pure (is_array_list)\<rangle>map_fun_rel D\<close>
term \<open>\<langle>Id\<rangle>map_fun_rel D\<close>
term "\<langle>the_pure (is_array)\<rangle> U"
term \<open>R O \<langle>Id\<rangle>map_fun_rel D\<close>
lemma list_nth_watched_app':
  \<open>(uncurry (RETURN oo op_list_get), uncurry (RETURN oo watched_app)) \<in>
     [\<lambda>(W, L). L \<in> snd ` D]\<^sub>f (\<langle>R\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel) \<rightarrow> \<langle>R\<rangle> nres_rel\<close>
  by (force simp: fref_def p2rel_def watched_app_def map_fun_rel_def[abs_def] relAPP_def
      prod_rel_def_internal lit_of_natP_def nres_rel_def_internal lit_of_natP_def[abs_def])
(* (((nat array \<times> nat) list \<times> nat) \<times>
    (nat literal \<Rightarrow> nat list) \<times> nat literal) set *)
thm arl_get_hnr_aux hfref_compI_PRE_aux[OF arl_get_hnr_aux list_nth_watched_app]
term is_array_list
lemma \<open>(uncurry (Array.nth) , uncurry (RETURN oo watched_app)) \<in>
   [\<lambda>(W, L). L \<in> snd ` D]\<^sub>a array_watched_assn\<^sup>k *\<^sub>a nat_nat_lit_assn\<^sup>k \<rightarrow> arl_assn id_assn\<close>
  (is \<open>?u \<in> ?B\<close> is \<open>_ \<in> [?PRE]\<^sub>a ?init \<rightarrow> ?post\<close>)
proof -
  term \<open>addr_of_array\<close>
  term \<open>p\<mapsto>\<^sub>al\<close>
  term is_array

  thm hfref_compI_PRE_aux[of \<open>fst ?u\<close> _ _ _ _ \<open>snd ?u\<close>, unfolded fst_conv snd_conv ,
      OF array_get_hnr_aux list_nth_watched_app']
    term \<open> \<langle>Id\<rangle>map_fun_rel D\<close>
    thm array_get_hnr_aux list_nth_watched_app
  thm hfref_compI_PRE_aux[of \<open>fst ?u\<close> _ _ _ _ \<open>snd ?u\<close>, unfolded fst_conv snd_conv ,
      OF (* array_get_hnr_aux *)_ list_nth_watched_app
      (* list_nth_watched_app *)(* , of \<open>arl_assn id_assn\<close> *)]
  have 0: \<open>?u \<in> [comp_PRE (\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r lit_of_nat_rel)
       (\<lambda>(W, L). L \<in> snd ` D) (\<lambda>_ (l, i). i < length l)
       (\<lambda>_. True)]\<^sub>a hrp_comp (is_array\<^sup>k *\<^sub>a nat_assn\<^sup>k)
                       (\<langle>Id\<rangle>map_fun_rel D \<times>\<^sub>r
                        lit_of_nat_rel) \<rightarrow> hr_comp id_assn Id\<close>
    (is " _ \<in> [?PRE']\<^sub>a ?init' \<rightarrow> ?post'")
    using hfref_compI_PRE_aux[OF array_get_hnr_aux list_nth_watched_app'] .
  have 1: \<open>?PRE' = ?PRE\<close>
    by (force simp: comp_PRE_def map_fun_rel_def[abs_def] relAPP_def lit_of_natP_def p2rel_def
        prod_rel_def_internal
        intro!: ext)
  have eq_mem_trans2:
    \<open>a \<in> A \<Longrightarrow> A = B \<Longrightarrow> a \<in> B\<close> for a A B
    by auto
  thm eq_mem_trans2[OF 0, of ?B]
  show ?thesis(*
    supply [[show_types]]
    using 0 unfolding 1 2 prod_hrp_comp apply -
    supply [[unify_trace_failure]] *)
    apply (rule eq_mem_trans2[OF 0])
      unfolding 1 prod_hrp_comp
      prefer 2 apply assumption

      (*hrp_comp (is_array\<^sup>k)
                   (\<langle>the_pure is_array_list\<rangle>map_fun_rel D) =
   (hr_comp (array_assn (arl_assn nat_assn))
                    (\<langle>Id\<rangle>map_fun_rel D))\<^sup>k *)
      (*)






  apply sepref_to_hoare
  apply (sep_auto simp: map_fun_rel_def[abs_def] nat_nat_lit_assn_def lit_of_natP_def relAPP_def)
=======
lemma arl_get_hnr_aux: "(uncurry arl_get,uncurry (RETURN oo op_list_get)) \<in> [\<lambda>(l,i). i<length l]\<^sub>a (is_array_list\<^sup>k *\<^sub>a nat_assn\<^sup>k) \<rightarrow> id_assn"
<<<<<<< HEAD

  by sep_auto
inductive_cases runE: \<open>run a b c d\<close>
=======

  by sep_auto
inductive_cases runE: \<open>run a b c d\<close>
>>>>>>> generalise_trail_for_CDCL_T
lemma \<open>(uncurry Array.nth, uncurry (RETURN oo watched_app)) \<in>
   [\<lambda>(W, L). L \<in> snd ` D]\<^sub>a array_watched_assn\<^sup>k *\<^sub>a nat_nat_lit_assn\<^sup>k \<rightarrow> arl_assn id_assn\<close>
  apply sep_auto
  apply (sep_auto simp: lit_of_natP_def nat_nat_lit_assn_def lit_of_natP_def[abs_def] p2rel_def
      hoare_triple_def Let_def Array.nth_def Heap_Monad.guard_def
      elim!: runE
      split: if_splits)
    apply auto[]
  apply (sep_auto simp: map_fun_rel_def[abs_def] (* nat_nat_lit_assn_def *) lit_of_natP_def
      relAPP_def nat_nat_lit_assn_def)
  apply (rule cons_rule[OF _ _ nth_rule])
    apply (auto simp: hr_comp_def entails_def (* snga_assndef *) array_assn_def relAPP_def
      arl_assn_def)
    apply (auto simp: hr_comp_def[abs_def])
    apply (subgoal_tac \<open>(aa, b) \<Turnstile> ai \<mapsto>\<^sub>a (Array.get aa ai)\<close>)
     defer
     apply sep_auto
  oops
















lemma
  \<open>(uncurry2 watched_by_nth_wll, uncurry2 (RETURN ooo watched_by_nth)) \<in>
     [\<lambda>(((M, N, U, D, NP, UP, Q, W), L), i). i < length (W L)]\<^sub>a
      twl_st_l_assn\<^sup>d *\<^sub>a nat_nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding watched_by_nth_wll_def watched_by_nth_def
  unfolding watched_by_nth_def twl_st_l_assn_def
  apply (subst watched_app_def[symmetric])
  apply sepref_dbg_keep
  supply [[goals_limit=1]] -- \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
   apply sepref_dbg_trans_keep
               apply sepref_dbg_trans_step_keep
    oops
    apply (simp only: prod.case)
   apply sepref_dbg_trans_step_keep
      apply (sepref_dbg_side_keep)
    apply  ( ( elim CONSTRAINT_is_pureE;  (simp only: list_assn_pure_conv the_pure_pure)?)?;
    sep_auto
      simp: pure_def hn_ctxt_def invalid_assn_def list_assn_aux_eqlen_simp
      intro!: hn_refineI[THEN hn_refine_preI] hfrefI
      elim!: mod_starE
      intro: (* list_set_entails_aux list_set_hd_tl_aux list_set_last_butlast_aux
             list_swap_aux list_rotate1_aux list_rev_aux *)
    ;
    ((rule entails_preI; sep_auto simp: list_assn_aux_eqlen_simp | (parametricity; simp; fail))?)
  )
  apply sepref_dbg_keep
  supply [[goals_limit=1]] -- \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
   apply sepref_dbg_trans_keep
               apply sepref_dbg_trans_step_keep
    apply (simp only: prod.case)
   apply sepref_dbg_trans_step_keep
      apply (sepref_dbg_side_keep)


  thm HOL_list_prepend_hnr




 *)

















sepref_definition watched_by_nth_impl is \<open>uncurry2 (RETURN ooo watched_by_nth)\<close>
  :: \<open>[\<lambda>(((M, N, U, D, NP, UP, Q, W), L), i). i < length (W L)]\<^sub>a
      twl_st_l_assn\<^sup>k *\<^sub>a nat_nat_lit_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> nat_assn\<close>
  unfolding watched_by_nth_def twl_st_l_assn_def
  apply sepref_dbg_keep
  supply [[goals_limit=1]] -- \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
   apply sepref_dbg_trans_keep
    apply auto[]
   apply sepref_dbg_trans_step_keep
      apply (sepref_dbg_side_keep)

definition watched_by_impl :: \<open>twl_st_wll \<Rightarrow> nat \<Rightarrow> _\<close> where
  \<open>watched_by_impl S L =
     do {
        let (M, N, U, D, NP, UP, Q, W) = S;
        RETURN (Array.nth W L)
     }\<close>

sepref_definition truc_muche is truc_muche ::
    \<open>twl_st_l_assn\<^sup>d \<rightarrow>\<^sub>a twl_st_l_assn\<close>
  unfolding truc_muche_def
  apply sepref_dbg_keep
  supply [[goals_limit=1]] -- \<open>There will be many subgoals during translation, and printing them takes very long with Isabelle :(\<close>
   apply sepref_dbg_trans_keep
    apply auto
   apply sepref_dbg_trans_step_keep
      apply (sepref_dbg_side_keep)

end