theory CDCL_Two_Watched_Literals_List_Watched_Init_Trail_Code
imports CDCL_Two_Watched_Literals_List_Watched_Trail_Code
begin

type_synonym 'v twl_st_wl' =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl"

type_synonym twl_st_wll' =
  "trail_assn \<times> clauses_wl \<times> nat \<times> nat array_list option \<times> unit_lits_wl \<times> unit_lits_wl \<times>
    lit_queue_l"

definition init_dt_step_wl :: \<open>nat list \<Rightarrow> nat clause_l \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close> where
  \<open>init_dt_step_wl N\<^sub>1 C S = do {
     let (M, N, U, D, NP, UP, Q, WS) = S in
     case D of
      None \<Rightarrow>
      if length C = 1
      then do {
        ASSERT (no_dup M);
        ASSERT (C \<noteq> []);
        let L = hd C;
        ASSERT(L \<in> snd ` twl_array_code.D\<^sub>0 N\<^sub>1);
        let val_L = valued M L;
        if val_L = None
        then do {RETURN (Propagated L 0 # M, N, U, None, add_mset {#L#} NP, UP, add_mset (-L) Q, WS)}
        else
          if val_L = Some True
          then do {RETURN (M, N, U, None, add_mset {#L#} NP, UP, Q, WS)}
          else do {RETURN (M, N, U, Some (mset C), add_mset {#L#} NP, UP, {#}, WS)}
        }
      else do {
        ASSERT(C \<noteq> []);
        ASSERT(tl C \<noteq> []);
        ASSERT(hd C \<in> snd ` twl_array_code.D\<^sub>0 N\<^sub>1);
        ASSERT(hd (tl C) \<in> snd ` twl_array_code.D\<^sub>0 N\<^sub>1);
        let U = length N;
        let WS = WS((hd C) := WS (hd C) @ [U]);
        let WS = WS((hd (tl C)) := WS (hd (tl C)) @ [U]);
        RETURN (M, N @ [op_array_of_list C], U, None, NP, UP, Q, WS)}
    | Some D \<Rightarrow>
      if length C = 1
      then do {
        ASSERT (C \<noteq> []);
        let L = hd C;
        RETURN (M, N, U, Some D, add_mset {#L#} NP, UP, {#}, WS)}
      else do {
        ASSERT(C \<noteq> []);
        ASSERT(tl C \<noteq> []);
        ASSERT(hd C \<in> snd ` twl_array_code.D\<^sub>0 N\<^sub>1);
        ASSERT(hd (tl C) \<in> snd ` twl_array_code.D\<^sub>0 N\<^sub>1);
        let U = length N;
        let WS = WS(hd C := WS (hd C) @ [U]);
        let WS = WS((hd (tl C)) := WS (hd (tl C)) @ [U]);
        RETURN (M, N @ [op_array_of_list C], U, Some D, NP, UP, {#}, WS)}
  }\<close>

definition arl_of_list_raa :: "'a::heap list \<Rightarrow> ('a array_list) Heap" where
  \<open>arl_of_list_raa xs = do {
    ys \<leftarrow> Array.of_list xs;
    arl_of_array_raa ys }\<close>

lemma arl_of_list_raa_mset[sepref_fr_rules]:
  \<open>(arl_of_list_raa, RETURN o mset) \<in> [\<lambda>C. C \<noteq> []]\<^sub>a(list_assn nat_lit_assn)\<^sup>d \<rightarrow> conflict_assn\<close>
proof -
  define R where \<open>R = nat_lit_rel\<close>
  have [simp]: \<open>x \<noteq> [] \<Longrightarrow> pure (\<langle>R\<rangle>list_rel) x [] = false\<close> for x
    by (auto simp: list_rel_def pure_def)
  show ?thesis
    unfolding R_def[symmetric]
    apply sepref_to_hoare
    unfolding pure_def[symmetric]
    apply (sep_auto simp: arl_of_list_raa_def arl_of_array_raa_def hr_comp_def
        list_mset_rel_def br_def list_assn_pure_conv arl_assn_def is_array_list_def)
    apply (sep_auto simp: pure_def)
    done
qed


thm twl_array_code.cons_trail_Propagated_tr_code_cons_trail_Propagated_tr
lemma valued_None_undefined_lit: \<open>is_None (valued M L) \<Longrightarrow> undefined_lit M L\<close>
  by (auto simp: valued_def split: if_splits)

declare twl_array_code.append_el_aa_hnr[sepref_fr_rules]
declare twl_array_code.valued_trail_code_valued_refine_code[sepref_fr_rules]
  twl_array_code.cons_trail_Propagated_tr_code_cons_trail_Propagated_tr[sepref_fr_rules]
sepref_definition init_dt_step_wl_code
  is \<open>uncurry2 (init_dt_step_wl)\<close>
  :: \<open>[\<lambda>((N, _), _). N = N\<^sub>1]\<^sub>a
       (list_assn nat_assn)\<^sup>k *\<^sub>a (list_assn nat_lit_assn)\<^sup>d *\<^sub>a (twl_array_code.twl_st_l_trail_assn N\<^sub>1)\<^sup>d \<rightarrow>
       (twl_array_code.twl_st_l_trail_assn N\<^sub>1)\<close>
  supply valued_None_undefined_lit[simp]
  unfolding init_dt_step_wl_def twl_array_code.twl_st_l_trail_assn_def lms_fold_custom_empty
      unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding twl_array_code.append_update_def[of, symmetric] fold_is_None
    twl_array_code.cons_trail_Propagated_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref


lemmas init_dt_step_wl_code_refine = init_dt_step_wl_code.refine[sepref_fr_rules]


definition init_dt_wl where
  \<open>init_dt_wl N CS S = nfoldli CS (\<lambda>_. True) (init_dt_step_wl N) S\<close>

sepref_definition init_dt_wl_code
  is \<open>uncurry2 init_dt_wl\<close>
  :: \<open>[\<lambda>((N, _), _). N = N\<^sub>1]\<^sub>a
       (list_assn nat_assn)\<^sup>k *\<^sub>a (list_assn (list_assn nat_lit_assn))\<^sup>d *\<^sub>a (twl_array_code.twl_st_l_trail_assn N\<^sub>1)\<^sup>d \<rightarrow>
       (twl_array_code.twl_st_l_trail_assn N\<^sub>1)\<close>
  unfolding init_dt_wl_def
  supply [[goals_limit = 1]]
  by sepref

term nat_lit_assn
term nat_lit_rel
  term \<open>hs.assn\<close>
definition nat_lit_list_hm_ref_rel :: "(('a set \<times> 'a literal list) \<times> 'a literal list) set" where
  \<open>nat_lit_list_hm_ref_rel = {((s, xs), l). l = xs \<and> s = atm_of ` set l}\<close>

abbreviation nat_lit_lits_init_ref_assn where
  \<open>nat_lit_lits_init_ref_assn \<equiv> hs.assn nat_assn *assn list_assn nat_lit_assn\<close>

abbreviation nat_lit_list_hm_assn where
  \<open>nat_lit_list_hm_assn \<equiv> hr_comp nat_lit_lits_init_ref_assn nat_lit_list_hm_ref_rel\<close>

definition in_map_atm_of :: "'a \<Rightarrow> 'a literal list \<Rightarrow> bool" where
  \<open>in_map_atm_of L N \<longleftrightarrow> L \<in> set (map atm_of N)\<close>

sepref_definition nat_lit_lits_init_assn_assn_in
  is \<open>uncurry (RETURN oo (\<lambda>L (s, xs). L \<in> s))\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_lit_lits_init_ref_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref

lemma nat_lit_lits_init_assn_ref_in:
  \<open>(uncurry (RETURN oo (\<lambda>L (s, xs). L \<in> s)), uncurry (RETURN oo in_map_atm_of)) \<in>
    nat_rel \<times>\<^sub>r nat_lit_list_hm_ref_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def in_map_atm_of_def)

sepref_definition nat_lit_lits_init_assn_assn_prepend
  is \<open>uncurry (RETURN oo (\<lambda>L (s, xs). (insert (atm_of L) s, L # xs)))\<close>
  :: \<open>nat_lit_assn\<^sup>k *\<^sub>a nat_lit_lits_init_ref_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_lits_init_ref_assn\<close>
  by sepref

lemma nat_lit_lits_init_assn_ref_list_prepend:
  \<open>(uncurry (RETURN oo (\<lambda>L (s, xs). (insert (atm_of L) s, L # xs))), uncurry (RETURN oo op_list_prepend)) \<in>
    Id \<times>\<^sub>r nat_lit_list_hm_ref_rel \<rightarrow>\<^sub>f \<langle>nat_lit_list_hm_ref_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def in_map_atm_of_def)

lemma nat_lit_lits_init_assn_assn_prepend[sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_prepend, uncurry (RETURN \<circ>\<circ> op_list_prepend))
      \<in> nat_lit_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using nat_lit_lits_init_assn_assn_prepend.refine[FCOMP nat_lit_lits_init_assn_ref_list_prepend] .

lemma nat_lit_lits_init_assn_assn_id[sepref_fr_rules]:
  \<open>(return o snd, RETURN o id) \<in> nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a list_assn nat_lit_assn\<close>
  by sepref_to_hoare (sep_auto simp: nat_lit_list_hm_ref_rel_def hr_comp_def)

lemma in_map_atm_of_hnr[sepref_fr_rules]:
  \<open>(uncurry nat_lit_lits_init_assn_assn_in, uncurry (RETURN \<circ>\<circ> in_map_atm_of))
     \<in> nat_assn\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using nat_lit_lits_init_assn_assn_in.refine[FCOMP nat_lit_lits_init_assn_ref_in] .


definition extract_lits_cls :: \<open>'a clause_l \<Rightarrow> 'a literal list \<Rightarrow> 'a literal list\<close> where
  \<open>extract_lits_cls C N\<^sub>0 = fold (\<lambda>L N\<^sub>0. if atm_of L \<in> set (map atm_of N\<^sub>0) then N\<^sub>0 else L # N\<^sub>0) C N\<^sub>0\<close>

sepref_definition extract_lits_cls_imp
  is \<open>uncurry (RETURN oo extract_lits_cls)\<close>
  :: \<open>(list_assn nat_lit_assn)\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_lits_cls_def in_map_atm_of_def[symmetric] 
  apply (subst fold_idx_conv)
  by sepref

declare extract_lits_cls_imp.refine[sepref_fr_rules]

definition extract_lits_clss:: \<open>'a clauses_l \<Rightarrow> 'a literal list \<Rightarrow> 'a literal list\<close>  where
  \<open>extract_lits_clss N N\<^sub>0 = fold extract_lits_cls N N\<^sub>0\<close>

sepref_definition extract_lits_clss_imp
  is \<open>uncurry (RETURN oo extract_lits_clss)\<close>
  :: \<open>(list_assn (list_assn nat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  unfolding extract_lits_clss_def in_map_atm_of_def[symmetric]
  apply (subst fold_idx_conv)
  by sepref

lemma id_extract_lits_clss: \<open>extract_lits_clss = (\<lambda>a b. id (extract_lits_clss a b))\<close>
  by auto

sepref_definition extract_lits_clss_imp_list_assn
  is \<open>uncurry (RETURN oo extract_lits_clss)\<close>
  :: \<open>(list_assn (list_assn nat_lit_assn))\<^sup>k *\<^sub>a nat_lit_list_hm_assn\<^sup>d \<rightarrow>\<^sub>a list_assn nat_lit_assn\<close>
  supply extract_lits_clss_imp.refine[sepref_fr_rules]
  apply (rewrite at \<open>extract_lits_clss\<close> id_extract_lits_clss)
  by sepref

lemma extract_lits_clss_imp_empty_rel:
  \<open>(uncurry0 (RETURN ({}, [])), uncurry0 (RETURN op_HOL_list_empty)) \<in>
     unit_rel \<rightarrow>\<^sub>f \<langle>nat_lit_list_hm_ref_rel\<rangle> nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: nat_lit_list_hm_ref_rel_def)

sepref_definition extract_lits_clss_imp_empty_assn
  is \<open>uncurry0 (RETURN ({}, []))\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_lits_init_ref_assn\<close>
  unfolding hs.fold_custom_empty HOL_list.fold_custom_empty
  by sepref

lemma extract_lits_clss_imp_empty_assn[sepref_fr_rules]:
  \<open>(uncurry0 extract_lits_clss_imp_empty_assn, uncurry0 (RETURN op_HOL_list_empty))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_lit_list_hm_assn\<close>
  using extract_lits_clss_imp_empty_assn.refine[FCOMP extract_lits_clss_imp_empty_rel] .

declare extract_lits_clss_imp_list_assn.refine[sepref_fr_rules]
declare atm_of_hnr[sepref_fr_rules]

sepref_definition find_first_eq_map_atm_of_code
  is \<open>uncurry (find_first_eq_map atm_of)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a (list_assn nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding find_first_eq_map_def short_circuit_conv
  by sepref

definition index_atm_of where
  \<open>index_atm_of L N\<^sub>0 = index (map atm_of N\<^sub>0) L\<close>

lemma find_first_eq_map_atm_of_code_index_atm_of[sepref_fr_rules]:
  \<open>(uncurry find_first_eq_map_atm_of_code, uncurry (RETURN oo index_atm_of)) \<in>
     nat_assn\<^sup>k *\<^sub>a (list_assn nat_lit_assn)\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
proof -
  have 1: \<open>(uncurry (find_first_eq_map atm_of), uncurry (RETURN oo index_atm_of)) \<in>
    Id \<times>\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>nat_rel\<rangle>nres_rel\<close>
    unfolding uncurry_def index_atm_of_def using find_first_eq_map_index
    by (intro nres_relI frefI, rename_tac x y) (case_tac x, case_tac y, fastforce)
  show ?thesis
    using find_first_eq_map_atm_of_code.refine[FCOMP 1] .
qed

definition extract_lits_cls' :: \<open>'a clause_l \<Rightarrow> 'a literal list \<Rightarrow> 'a literal list\<close> where
  \<open>extract_lits_cls' C N\<^sub>0 =
     fold (\<lambda>L N\<^sub>0. let i = index (map atm_of N\<^sub>0) (atm_of L) in if i < length N\<^sub>0 then N\<^sub>0 else L # N\<^sub>0) C N\<^sub>0\<close>

sepref_definition extract_lits_cls_code
  is \<open>uncurry (RETURN oo extract_lits_cls')\<close>
  :: \<open>(list_assn nat_lit_assn)\<^sup>d *\<^sub>a (list_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a (list_assn nat_lit_assn)\<close>
  unfolding extract_lits_cls'_def twl_array_code.twl_st_l_trail_assn_def lms_fold_custom_empty
      unfolding watched_app_def[symmetric]
  unfolding nth_rll_def[symmetric] find_unwatched'_find_unwatched[symmetric]
  unfolding lms_fold_custom_empty swap_ll_def[symmetric]
  unfolding twl_array_code.append_update_def[symmetric] index_atm_of_def[symmetric]
  supply [[goals_limit = 1]]
  by sepref

declare extract_lits_cls_code.refine[sepref_fr_rules]

lemma extract_lits_cls'_extract_lits_cls: \<open>extract_lits_cls' = extract_lits_cls\<close>
proof -
  have [simp]: \<open>(\<lambda>L N\<^sub>0. if index (map atm_of N\<^sub>0) (atm_of L) < length N\<^sub>0 then N\<^sub>0 else L # N\<^sub>0) =
      (\<lambda>L N\<^sub>0. if atm_of L \<in> atm_of ` set N\<^sub>0 then N\<^sub>0 else L # N\<^sub>0)\<close>
    by (intro ext) (auto simp: extract_lits_cls'_def extract_lits_cls_def)
  then show ?thesis
    by (intro ext) (auto simp: extract_lits_cls'_def extract_lits_cls_def)
qed

sepref_definition extract_lits_clss_code
  is \<open>uncurry (RETURN oo extract_lits_clss)\<close>
  :: \<open>(list_assn (list_assn nat_lit_assn))\<^sup>d *\<^sub>a (list_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a (list_assn nat_lit_assn)\<close>
  unfolding extract_lits_clss_def extract_lits_cls'_extract_lits_cls[symmetric]
  by sepref

declare extract_lits_clss_code.refine[sepref_fr_rules]

lemma lits_of_atms_of_mm_empty[simp]: \<open>lits_of_atms_of_mm {#} = {#}\<close>
  by (auto simp: lits_of_atms_of_mm_def)

lemma lits_of_atms_of_m_empty[simp]: \<open>lits_of_atms_of_m {#} = {#}\<close>
  by (auto simp: lits_of_atms_of_m_def)

lemma extract_lits_cls_Cons:
  \<open>extract_lits_cls (L # C) N\<^sub>0 = extract_lits_cls C (if atm_of L \<in> atms_of (mset N\<^sub>0) then N\<^sub>0 else L # N\<^sub>0)\<close>
  unfolding extract_lits_cls_def fold.simps by simp

lemma extract_lits_cls_Nil[simp]:
  \<open>extract_lits_cls [] N\<^sub>0 = N\<^sub>0\<close>
  unfolding extract_lits_cls_def fold.simps by simp

lemma extract_lits_clss_Cons[simp]:
  \<open>extract_lits_clss (C # Cs) N = extract_lits_clss Cs (extract_lits_cls C N)\<close>
  by (simp add: extract_lits_clss_def)

lemma lits_of_atms_of_m_extract_lits_cls: \<open>set_mset (lits_of_atms_of_m (mset (extract_lits_cls C N\<^sub>0))) =
   set_mset (lits_of_atms_of_m (mset C) + lits_of_atms_of_m (mset N\<^sub>0))\<close>
  apply (induction C arbitrary: N\<^sub>0)
  subgoal by simp
  subgoal by (simp add: extract_lits_cls_Cons lits_of_atms_of_m_add_mset
        in_lits_of_atms_of_m_ain_atms_of_iff insert_absorb)
  done

lemma is_N\<^sub>1_extract_lits_clss: \<open>twl_array_code.is_N\<^sub>1 (map nat_of_lit (extract_lits_clss N N\<^sub>0))
  (lits_of_atms_of_mm (mset `# mset N) + lits_of_atms_of_m (mset N\<^sub>0))\<close>
proof -
  have is_N\<^sub>1_add: \<open>twl_array_code.is_N\<^sub>1 N\<^sub>0 (A + B) \<longleftrightarrow> set_mset A \<subseteq> set_mset (twl_array_code.N\<^sub>1 N\<^sub>0)\<close>
    if \<open>twl_array_code.is_N\<^sub>1 N\<^sub>0 B\<close> for A B N\<^sub>0
    using that unfolding twl_array_code.is_N\<^sub>1_def by auto
  show ?thesis
    apply (induction N arbitrary: N\<^sub>0)
    subgoal by (auto simp: extract_lits_cls_def extract_lits_clss_def twl_array_code.is_N\<^sub>1_def
          twl_array_code.N\<^sub>1_def in_lits_of_atms_of_m_ain_atms_of_iff twl_array_code.N\<^sub>0''_def
          twl_array_code.N\<^sub>0'_def atm_of_eq_atm_of
          simp del: nat_of_lit.simps literal_of_nat.simps)
    subgoal premises H for C Cs N\<^sub>0
      using H[of \<open>extract_lits_cls C N\<^sub>0\<close>, unfolded twl_array_code.is_N\<^sub>1_def, symmetric]
      by (simp add: lits_of_atms_of_mm_add_mset twl_array_code.is_N\<^sub>1_def
          lits_of_atms_of_m_extract_lits_cls ac_simps)
    done
qed

fun correct_watching_init :: \<open>nat literal multiset \<Rightarrow> nat twl_st_wl \<Rightarrow> bool\<close> where
  \<open>correct_watching_init N\<^sub>1 (M, N, U, D, NP, UP, Q, W) \<longleftrightarrow>
    (\<forall>L \<in># lits_of_atms_of_m N\<^sub>1. mset (W L) = clause_to_update L (M, N, U, D, NP, UP, {#}, {#}))\<close>


lemma clause_to_update_append: \<open>N \<noteq> [] \<Longrightarrow> clause_to_update La (M, N @ [C], U, D, NP, UP, WS, Q) =
     clause_to_update La (M, N, U, D, NP, UP, WS, Q) +
    (if La \<in> set (watched_l C) then {#length N#} else {#})\<close>
  unfolding clause_to_update_def get_clauses_l.simps
  apply (auto simp: clause_to_update_def nth_append)
  by meson

definition HH :: \<open>nat literal multiset \<Rightarrow> (nat twl_st_wl \<times> nat twl_st_l) set\<close> where
  \<open>HH N\<^sub>1 = {((M', N', U', D', NP', UP', Q', WS'), (M, N, U, D, NP, UP, WS, Q)).
               M = M' \<and> N = N' \<and> U = U' \<and> D = D' \<and> NP = NP' \<and> UP = UP' \<and> Q = Q' \<and> WS = {#} \<and>
               (* U = length N - 1 \<and> *) UP = {#} \<and> N \<noteq> [] \<and>
               correct_watching_init N\<^sub>1 (M', N', U', D', NP', UP', Q', WS') \<and>
               set_mset (lits_of_atms_of_mm (mset `# mset (tl N) + NP)) \<subseteq> set_mset N\<^sub>1 \<and>
               (\<forall>L \<in> lits_of_l M. {#L#} \<in># NP) \<and>
               (\<forall>L \<in> set M. \<exists>K. L = Propagated K 0)}\<close>

lemma literals_are_in_N\<^sub>0_add_mset:
  \<open>twl_array_code.literals_are_in_N\<^sub>0 N\<^sub>0 (add_mset L M) \<longleftrightarrow>
   twl_array_code.literals_are_in_N\<^sub>0 N\<^sub>0 M \<and> (L \<in> literal_of_nat ` set N\<^sub>0 \<or> -L \<in> literal_of_nat ` set N\<^sub>0)\<close>
  by (auto simp: twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
      twl_array_code.literals_are_in_N\<^sub>0_def image_image lits_of_atms_of_m_add_mset uminus_lit_swap
        simp del: literal_of_nat.simps)

lemma init_dt_step_wl_init_dt_step_l:
  fixes N\<^sub>0 :: \<open>nat list\<close>
  defines \<open>N\<^sub>1 \<equiv> mset (map literal_of_nat N\<^sub>0) + mset (map (uminus o literal_of_nat) N\<^sub>0)\<close>
  assumes
    \<open>(S', S) \<in> HH N\<^sub>1\<close> and
    \<open>twl_array_code.literals_are_in_N\<^sub>0 N\<^sub>0 (mset C)\<close> and
    \<open>distinct C\<close>
  shows \<open>init_dt_step_wl N\<^sub>0 C S' \<le> \<Down> (HH N\<^sub>1) (init_dt_step_l C S)\<close>
proof -
  have [simp]: \<open>N\<^sub>1 = twl_array_code.N\<^sub>1 N\<^sub>0\<close>
    by (auto simp: twl_array_code.N\<^sub>1_def N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
        simp del: literal_of_nat.simps)
  have [iff]: \<open>- L \<in># twl_array_code.N\<^sub>1 N\<^sub>0 \<longleftrightarrow> L \<in># twl_array_code.N\<^sub>1 N\<^sub>0\<close> for L
    by (auto simp: twl_array_code.N\<^sub>1_def N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
        uminus_lit_swap simp del: literal_of_nat.simps)
  have [simp]: \<open>clause_to_update L (M, N, U, D, NP, UP, WS, Q) =
       clause_to_update L (M', N', U', D', NP', UP', WS', Q')\<close>
    if \<open>N = N'\<close>
    for M N U D NP UP WS Q M' N' U' D' NP' UP' WS' Q' and L :: \<open>nat literal\<close>
    by (auto simp: clause_to_update_def that)
  show ?thesis
    supply literal_of_nat.simps[simp del]
    using assms(2-)
    unfolding init_dt_step_wl_def init_dt_step_l_def
    apply refine_rcg
    subgoal by (auto simp: HH_def)
    subgoal by fast
    subgoal by (auto simp: HH_def)
    subgoal by (cases C) (auto simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (auto simp: HH_def)
    subgoal by (cases C)
        (clarsimp_all simp: HH_def lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset)
    subgoal by (auto simp only: HH_def)
    subgoal by (cases C)
        (clarsimp_all simp: HH_def lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset)
    subgoal by (cases C; cases \<open>tl C\<close>)
        (clarsimp_all simp: HH_def lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset)
    subgoal by (cases C) (clarsimp_all simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' image_image lits_of_atms_of_m_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' lits_of_atms_of_m_add_mset
          lits_of_atms_of_mm_add_mset literals_are_in_N\<^sub>0_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' lits_of_atms_of_m_add_mset
          lits_of_atms_of_mm_add_mset literals_are_in_N\<^sub>0_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    subgoal by (cases C; cases \<open>tl C\<close>) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' lits_of_atms_of_m_add_mset
          lits_of_atms_of_mm_add_mset literals_are_in_N\<^sub>0_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    done
qed

lemma init_dt_wl_init_dt_l:
  fixes N\<^sub>0 :: \<open>nat list\<close>
  defines \<open>N\<^sub>1 \<equiv> mset (map literal_of_nat N\<^sub>0) + mset (map (uminus o literal_of_nat) N\<^sub>0)\<close>
  assumes
    S'S: \<open>(S', S) \<in> HH N\<^sub>1\<close> and
    \<open>\<forall>C\<in>set CS. twl_array_code.literals_are_in_N\<^sub>0 N\<^sub>0 (mset C)\<close> and
    \<open>\<forall>C\<in>set CS. distinct C\<close>
  shows \<open>init_dt_wl N\<^sub>0 CS S' \<le> \<Down> (HH N\<^sub>1) (init_dt_l CS S)\<close>
  using assms(2-)
  supply literal_of_nat.simps[simp del]
  apply (induction CS arbitrary: S S')
  subgoal using S'S by (simp add: init_dt_wl_def init_dt_l_def)
  subgoal premises p for a CS S S'
    using p(2-)
    unfolding init_dt_wl_def init_dt_l_def nfoldli_simps(2) if_True apply -
    apply (rule bind_refine)
     apply (rule init_dt_step_wl_init_dt_step_l[of _ _ N\<^sub>0, unfolded N\<^sub>1_def[symmetric]]; solves \<open>simp\<close>)
    apply (rule p(1)[unfolded init_dt_wl_def init_dt_l_def]; solves \<open>simp\<close>)
    done
  done

abbreviation twl_code_array_literals_are_N\<^sub>0 where
  \<open>twl_code_array_literals_are_N\<^sub>0 N\<^sub>0 S \<equiv>
     twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S))))\<close>

fun get_clauses_wl :: "'v twl_st_wl \<Rightarrow> 'v clauses_l" where
  \<open>get_clauses_wl (M, N, U, D, NP, UP, WS, Q) = N\<close>

fun get_learned_wl :: "'v twl_st_wl \<Rightarrow> nat" where
  \<open>get_learned_wl (M, N, U, D, NP, UP, WS, Q) = U\<close>

lemma lits_of_atms_of_mm_in_lits_of_atms_of_m_in_iff:
  \<open>set_mset (lits_of_atms_of_mm (mset `# mset CS)) \<subseteq> A \<longleftrightarrow>
    (\<forall>C\<in>set CS. set_mset (lits_of_atms_of_m (mset C)) \<subseteq> A)\<close>
  by (auto simp: lits_of_atms_of_mm_def lits_of_atms_of_m_def)

definition get_unit_learned :: "'v twl_st_wl \<Rightarrow> 'v clauses" where
  \<open>get_unit_learned = (\<lambda>(M, N, U, D, NP, UP, Q, W). UP)\<close>

definition get_unit_init_clss :: "'v twl_st_wl \<Rightarrow> 'v clauses" where
  \<open>get_unit_init_clss = (\<lambda>(M, N, U, D, NP, UP, Q, W). NP)\<close>


lemma init_dt_init_dt_l_full:
  fixes S :: \<open>nat twl_st_wl\<close> and CS
  defines \<open>N\<^sub>0 \<equiv> map nat_of_lit (extract_lits_clss CS [])\<close>
  defines \<open>N\<^sub>1 \<equiv> mset (map literal_of_nat N\<^sub>0) + mset (map (uminus \<circ> literal_of_nat) N\<^sub>0)\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    length: \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    taut: \<open>\<forall>C \<in> set CS. \<not>tautology (mset C)\<close> and
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    dec:\<open>\<forall>s\<in>set (get_trail_wl S). \<not>is_decided s\<close> and
    confl: \<open>get_conflict_wl S = None \<longrightarrow> literals_to_update_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init N\<^sub>1 S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset N\<^sub>1\<close> and
    no_learned: \<open>get_unit_learned S = {#}\<close> and
    confl_in_clss: \<open>get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS\<close> and
    trail_in_NP: \<open>\<forall>L \<in> lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S\<close> and
    prop_NP: \<open>\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0\<close>
  shows
    \<open>init_dt_wl N\<^sub>0 CS S \<le> SPEC(\<lambda>T.
       twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (mset `# mset CS +
          cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<and>
       twl_struct_invs (twl_st_of_wl None T) \<and> twl_stgy_invs (twl_st_of_wl None T) \<and>
       additional_WS_invs (st_l_of_wl None T) \<and>
       correct_watching_init N\<^sub>1 T \<and>
       cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None T))) =
         mset `# mset CS +
         cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) \<and>
      get_unit_learned T = {#} \<and>
      get_learned_wl T = length (get_clauses_wl T) - 1 \<and>
      count_decided (get_trail_wl T) = 0 \<and>
      (get_conflict_wl T \<noteq> None \<longrightarrow> the (get_conflict_wl T) \<in># mset `# mset CS) \<and>
      (\<forall>L \<in> lits_of_l (get_trail_wl T). {#L#} \<in># get_unit_init_clss T) \<and>
      (\<forall>L \<in> set (get_trail_wl T). \<exists>K. L = Propagated K 0))\<close>
proof -
  define T where \<open>T = st_l_of_wl None S\<close>
  have N\<^sub>0_N\<^sub>1: \<open>twl_array_code.N\<^sub>1 N\<^sub>0 = N\<^sub>1\<close>
    by (auto simp: twl_array_code.N\<^sub>1_def N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
        simp del: nat_of_lit.simps literal_of_nat.simps)
  have w_q: \<open>clauses_to_update_l T = {#}\<close>
    by (cases S) (simp add: T_def)
  have tr_T_S: \<open>get_trail_l T = get_trail_wl S\<close> and p_T_S: \<open>literals_to_update_l T = literals_to_update_wl S\<close> and
    c_T_S: \<open>get_conflict_l T = get_conflict_wl S\<close> and
    l_T_S: \<open>get_learned_l T = get_learned_wl S\<close>and
    cl_T_S: \<open>get_clauses_l T = get_clauses_wl S\<close>
    by (cases S; simp add: T_def)+
  have
    dist_T: \<open>\<forall>C \<in> set (rev CS). distinct C\<close> and
    length_T: \<open>\<forall>C \<in> set (rev CS). length C \<ge> 1\<close> and
    taut_T: \<open>\<forall>C \<in> set (rev CS). \<not>tautology (mset C)\<close> and
    struct_T: \<open>twl_struct_invs (twl_st_of None T)\<close> and
    stgy_T: \<open>twl_stgy_invs (twl_st_of None T)\<close> and
    w_q_T: \<open>clauses_to_update_l T = {#}\<close> and
    tr_T: \<open>\<forall>s\<in>set (get_trail_l T). \<not> is_decided s\<close> and
    c_T: \<open>get_conflict_l T = None \<longrightarrow> literals_to_update_l T = uminus `# lit_of `# mset (get_trail_l T)\<close> and
    add_invs_T: \<open>additional_WS_invs T\<close> and
    le_T: \<open>get_learned_l T = length (get_clauses_l T) - 1\<close> and
    confl_in_clss_T: \<open>get_conflict_l T \<noteq> None \<longrightarrow> the (get_conflict_l T) \<in># mset `# mset (rev CS)\<close>
    by (use assms(3-) in \<open>simp add: T_def[symmetric]  w_q tr_T_S p_T_S c_T_S l_T_S cl_T_S\<close>)+
  note init = init_dt_full[of \<open>rev CS\<close> T, OF dist_T length_T taut_T struct_T w_q_T tr_T c_T
      add_invs_T le_T stgy_T ] init_dt_confl_in_clauses[OF confl_in_clss_T]
  have i: \<open>init_dt_l CS T \<le> \<Down> Id (SPEC(\<lambda>T. twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
      cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None T)) =
        mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of_wl None S)) \<and>
      get_learned_l T = length (get_clauses_l T) - 1 \<and> additional_WS_invs T \<and>
      count_decided (get_trail_l T) = 0 \<and>
      (get_conflict_l T \<noteq> None \<longrightarrow> the (get_conflict_l T) \<in># mset `# mset CS)))
      \<close>
    apply (subst init_dt_init_dt_l[of \<open>rev CS\<close>, unfolded rev_rev_ident, symmetric];
        use assms(3-) in \<open>simp add: T_def[symmetric]  w_q tr_T_S p_T_S c_T_S l_T_S cl_T_S\<close>)
    apply (intro conjI)
    using init apply (simp_all add: count_decided_def)
    done
   have CS_N\<^sub>1: \<open>\<forall>C\<in>set CS. twl_array_code.literals_are_in_N\<^sub>0 N\<^sub>0 (mset C)\<close>
    using is_N\<^sub>1_extract_lits_clss[of CS \<open>[]\<close>] unfolding N\<^sub>1_def N\<^sub>0_def
      twl_array_code.is_N\<^sub>1_def twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0''_def
      twl_array_code.N\<^sub>0'_def twl_array_code.literals_are_in_N\<^sub>0_def
    by (simp del: literal_of_nat.simps add: lits_of_atms_of_mm_in_lits_of_atms_of_m_in_iff[symmetric])
  have is_N\<^sub>1: \<open>twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (mset `# mset CS))\<close>
    using is_N\<^sub>1_extract_lits_clss[of CS \<open>[]\<close>] unfolding N\<^sub>1_def N\<^sub>0_def
      twl_array_code.is_N\<^sub>1_def twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0''_def
      twl_array_code.N\<^sub>0'_def twl_array_code.literals_are_in_N\<^sub>0_def
    by (simp del: literal_of_nat.simps add: lits_of_atms_of_mm_in_lits_of_atms_of_m_in_iff[symmetric])
  have Un_eq_iff_subset: \<open>A \<union> B = A \<longleftrightarrow> B \<subseteq> A\<close> for A B
    by blast
  have [simp]: \<open>twl_array_code.is_N\<^sub>1 N\<^sub>0 (A + lits_of_atms_of_mm B) \<longleftrightarrow>
       set_mset (lits_of_atms_of_mm B) \<subseteq> set_mset N\<^sub>1\<close>
    if \<open>twl_array_code.is_N\<^sub>1 N\<^sub>0 A\<close> for A B
    using that by (simp add: twl_array_code.is_N\<^sub>1_def twl_array_code.literals_are_in_N\<^sub>0_def
        Un_eq_iff_subset N\<^sub>0_N\<^sub>1)
  have CS_N\<^sub>1': \<open>set_mset (lits_of_atms_of_mm (mset `# mset CS)) \<subseteq> set_mset N\<^sub>1\<close>
    using is_N\<^sub>1 unfolding twl_array_code.is_N\<^sub>1_def by (clarsimp simp: HH_def lits_of_atms_of_mm_union N\<^sub>0_N\<^sub>1)
  have \<open>set_mset (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq>
   set_mset N\<^sub>1\<close>
    using S_N\<^sub>1 unfolding twl_array_code.is_N\<^sub>1_def
    by (cases S)(clarsimp simp: mset_take_mset_drop_mset' clauses_def HH_def N\<^sub>0_N\<^sub>1 cl_T_S)
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  show ?thesis
    apply (rule order.trans)
     apply (rule conc_trans[OF init_dt_wl_init_dt_l i, of S N\<^sub>0, unfolded N\<^sub>1_def[symmetric]])
    subgoal using clss watch S_N\<^sub>1 no_learned trail_in_NP prop_NP
      by (auto simp: HH_def T_def clauses_def mset_take_mset_drop_mset' get_unit_learned_def
            get_unit_init_clss_def
          simp del: correct_watching_init.simps)
    subgoal using CS_N\<^sub>1 by auto
    subgoal using dist .
    subgoal using is_N\<^sub>1 CS_N\<^sub>1' S_N\<^sub>1 unfolding conc_fun_RES
      by (clarsimp simp: HH_def lits_of_atms_of_mm_union mset_take_mset_drop_mset'
          clauses_def get_unit_learned_def get_unit_init_clss_def)
    done
qed

lemma init_dt_init_dt_l:
  fixes CS
  defines \<open>S \<equiv> ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])\<close>
  defines \<open>N\<^sub>0 \<equiv> map nat_of_lit (extract_lits_clss CS [])\<close>
  defines \<open>N\<^sub>1 \<equiv> mset (map literal_of_nat N\<^sub>0) + mset (map (uminus \<circ> literal_of_nat) N\<^sub>0)\<close>
  assumes
    dist: \<open>\<forall>C \<in> set CS. distinct C\<close> and
    length: \<open>\<forall>C \<in> set CS. length C \<ge> 1\<close> and
    taut: \<open>\<forall>C \<in> set CS. \<not>tautology (mset C)\<close>
   shows
    \<open>init_dt_wl N\<^sub>0 CS S \<le> SPEC(\<lambda>S.
       twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (mset `# mset CS)) \<and>
       twl_struct_invs (twl_st_of_wl None S) \<and> twl_stgy_invs (twl_st_of_wl None S) \<and>
       correct_watching S \<and>
       additional_WS_invs (st_l_of_wl None S) \<and>
       get_unit_learned S = {#} \<and>
       count_decided (get_trail_wl S) = 0 \<and>
       get_learned_wl S = length (get_clauses_wl S) - 1 \<and>
       cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) =
         mset `# mset CS \<and>
       (get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS) \<and>
       (\<forall>L\<in>lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S) \<and>
       (\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0))\<close>
proof -
  have clss_empty: \<open>cdcl\<^sub>W_restart_mset.clauses (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))) = {#}\<close>
    by (auto simp: S_def cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state)
  have
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    dec:\<open>\<forall>s\<in>set (get_trail_wl S). \<not>is_decided s\<close> and
    confl: \<open>get_conflict_wl S = None \<longrightarrow> literals_to_update_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init N\<^sub>1 S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset N\<^sub>1\<close> and
    no_learned: \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). UP) S = {#}\<close> and
    learned_nil: \<open>get_unit_learned S = {#}\<close> and
    confl_nil: \<open>get_conflict_wl S = None\<close> and
    trail_in_NP: \<open>\<forall>L\<in>lits_of_l (get_trail_wl S). {#L#} \<in># get_unit_init_clss S\<close> and
    prop_NP: \<open>\<forall>L \<in> set (get_trail_wl S). \<exists>K. L = Propagated K 0\<close>
    unfolding S_def by (auto simp:
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def additional_WS_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def get_unit_learned_def)
  note HH = init_dt_init_dt_l_full[of CS S, unfolded N\<^sub>0_def[symmetric] N\<^sub>1_def[symmetric] clss_empty,
        OF dist length taut struct dec confl aff_invs learned stgy_invs watch clss _ learned_nil,
        unfolded empty_neutral trail_in_NP]
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  have [simp]: \<open>twl_array_code.N\<^sub>1 N\<^sub>0 = N\<^sub>1\<close>
    by (auto simp: N\<^sub>1_def twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def)
      have [simp]: \<open>L \<notin> (\<lambda>x. - literal_of_nat x) ` set N\<^sub>0 \<longleftrightarrow> -L \<notin> literal_of_nat ` set N\<^sub>0\<close> for L
        by (cases L) (auto simp: split: if_splits)
  have H: \<open>xa \<in> set N\<^sub>0 \<Longrightarrow>
          Pos (atm_of (literal_of_nat xa)) \<in> literal_of_nat ` set N\<^sub>0 \<or>
          Neg (atm_of (literal_of_nat xa)) \<in> literal_of_nat ` set N\<^sub>0\<close> for xa
    by (cases \<open>literal_of_nat xa\<close>) (auto split: if_splits)
  have \<open>set_mset N\<^sub>1 \<subseteq> set_mset (lits_of_atms_of_m N\<^sub>1)\<close>
    by (fastforce simp: lits_of_atms_of_m_def N\<^sub>1_def image_image uminus_lit_swap)
  then have [simp]: \<open>set_mset (lits_of_atms_of_m N\<^sub>1) = set_mset N\<^sub>1\<close>
    by (fastforce simp: lits_of_atms_of_m_def N\<^sub>1_def image_image uminus_lit_swap
        simp del: literal_of_nat.simps dest: H)
  show ?thesis
    apply (rule order.trans)
     apply (rule HH)
    by (clarsimp_all simp: correct_watching.simps twl_array_code.is_N\<^sub>1_def clauses_def
        mset_take_mset_drop_mset' get_unit_learned_def confl_nil trail_in_NP prop_NP)
qed

definition init_state :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset\<close> where
  \<open>init_state N = (([]:: (nat, nat clause) ann_lits), (N :: nat clauses), ({#}::nat clauses),
      (None :: nat clause option))\<close>

definition empty_watched :: \<open>nat list \<Rightarrow> nat literal \<Rightarrow> nat list\<close> where
  \<open>empty_watched _ = (\<lambda>_. [])\<close>

locale locale_nat_list =
  fixes N :: \<open>nat list\<close>

definition (in locale_nat_list) init_state_wl :: \<open>nat \<Rightarrow> nat twl_st_wl\<close> where
  \<open>init_state_wl _ = ([], [[]], 0, None, {#}, {#}, {#}, empty_watched N)\<close>

text \<open>to get a full SAT:
  \<^item> either we fully apply \<^term>\<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<close>
  \<^item> or we can stop early.
\<close>
definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (\<lambda>U. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T U \<or>
         (cdcl\<^sub>W_restart_mset.clauses U = CS \<and> learned_clss U = {#} \<and>
            conflicting U \<noteq> None \<and> count_decided (trail U) = 0 \<and>
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv U))
  }\<close>

definition SAT_wl :: \<open>nat clauses_l \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let n = length CS;
    let N\<^sub>0 = map nat_of_lit (extract_lits_clss CS []);
    let S = locale_nat_list.init_state_wl N\<^sub>0 n;
    T \<leftarrow> init_dt_wl N\<^sub>0 CS S;
    if get_conflict_wl T = None
    then twl_array_code.cdcl_twl_stgy_prog_wl_D N\<^sub>0 T
    else RETURN T
  }\<close>

definition map_nat_of_lit where
  \<open>map_nat_of_lit = map nat_of_lit\<close>

definition SAT_wl' :: \<open>nat clauses_l \<Rightarrow> bool nres\<close> where
  \<open>SAT_wl' CS = do{
    let n = length CS;
    let N\<^sub>0 = map_nat_of_lit (extract_lits_clss CS []);
    let S = locale_nat_list.init_state_wl N\<^sub>0 n;
    T \<leftarrow> init_dt_wl N\<^sub>0 CS S;
    if get_conflict_wl T = None
    then do {
       U \<leftarrow> twl_array_code.cdcl_twl_stgy_prog_wl_D N\<^sub>0 T;
       RETURN (get_conflict_wl U = None)}
    else RETURN False
  }\<close>
text \<open>TODO Move\<close>
lemma list_assn_map_list_assn: \<open>list_assn g (map f x) xi = list_assn (\<lambda>a c. g (f a) c) x xi\<close>
  apply (induction x arbitrary: xi)
  subgoal by auto
  subgoal for a x xi
    by (cases xi) auto
  done

lemma id_map_nat_of_lit[sepref_fr_rules]:
  \<open>(return o id, RETURN o map_nat_of_lit) \<in> (list_assn nat_lit_assn)\<^sup>d \<rightarrow>\<^sub>a (list_assn nat_assn)\<close>
  by sepref_to_hoare (sep_auto simp: map_nat_of_lit_def list_assn_map_list_assn p2rel_def lit_of_natP_nat_of_lit_iff)

definition (in locale_nat_list) init_state_wl_D :: \<open>nat \<Rightarrow> twl_st_wll_trail Heap\<close> where
  \<open>init_state_wl_D l_Ns = do {
     let n = Suc (Suc (fold max N 0));
     N \<leftarrow> arrayO_raa_empty_sz l_Ns;
     e \<leftarrow> Array.new 0 0;
     N \<leftarrow> arrayO_raa_append N e;
     (WS) \<leftarrow> arrayO_ara_empty_sz_code n;
     M \<leftarrow> Array.new (shiftr1 n) (None, 0::nat);
     return (([], M, 0), N, 0, None, [], [], [], WS)
  }\<close>

lemma fold_cons_replicate: \<open>fold (\<lambda>_ xs. a # xs) [0..<n] xs = replicate n a @ xs\<close>
  by (induction n) auto

lemma arrayO_ara_empty_sz_code_rule:
   \<open><emp> arrayO_ara_empty_sz_code m <\<lambda>r. arrayO_assn (arl_assn R) (replicate m []) r * true>\<close>
proof -
  have H: \<open>(\<exists>\<^sub>Ara. hn_val nat_rel n m * true * arrayO_assn (arl_assn R) ra r * \<up> (ra = replicate n [])) =
     (hn_val nat_rel n m * true * arrayO_assn (arl_assn R) (replicate n []) r)\<close> for r n m
    by (simp add: ex_assn_up_eq2)
  have \<open><hn_val nat_rel n m> arrayO_ara_empty_sz_code m
     <\<lambda>r. \<exists>\<^sub>Ara. hn_val nat_rel n m * arrayO_assn (arl_assn R) ra r * true * \<up> (ra = replicate n [])>\<close>
    for n m :: nat
    by (rule imp_correctI[OF arrayO_ara_empty_sz_code.refine[to_hnr], simplified])
    (auto simp: arrayO_ara_empty_sz_def fold_cons_replicate)
  then show ?thesis
    by (simp add: ex_assn_up_eq2 hn_ctxt_def pure_def)
qed

lemma arrayO_ara_empty_sz_code_empty_watched:
  \<open>(uncurry0 (arrayO_ara_empty_sz_code (Suc (Suc (fold max N (0::nat))))),
     uncurry0 (RETURN (empty_watched N))) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a twl_array_code.array_watched_assn N\<close>
proof -
  define n where \<open>n = Suc (Suc (fold max N 0))\<close>
  have n_def_alt: \<open>n = Max (set N) + 2\<close> if \<open>xa \<in> set N\<close> for xa
    unfolding n_def
    using that by (cases N, auto simp: Max.set_eq_fold list.set(2)[symmetric] simp del: list.set(2))

  have [simp]:
    \<open>xa \<in> set N \<Longrightarrow> xa < n\<close>
    \<open>xa \<in> set N \<Longrightarrow> Suc xa < n\<close>
    \<open>xa \<in> set N \<Longrightarrow> xa - Suc 0 < n\<close>
    for xa
    unfolding n_def_alt using Max_ge[of \<open>set N\<close> xa]
    by (simp_all del: Max_ge)

  have 1: \<open>(uncurry0 (RETURN (arrayO_ara_empty_sz n)),
     uncurry0  (RETURN (empty_watched N)))\<in>
   unit_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>map_fun_rel (twl_array_code.D\<^sub>0 N)\<rangle> nres_rel\<close>
    by (intro nres_relI frefI)
       (auto simp: map_fun_rel_def arrayO_ara_empty_sz_def fold_cons_replicate
        twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0'_def twl_array_code.N\<^sub>0''_def empty_watched_def
        simp del: replicate.simps)
  have 0: \<open>(uncurry0 (arrayO_ara_empty_sz_code n), uncurry0 (RETURN (arrayO_ara_empty_sz n))) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a arrayO_assn (arl_assn R)\<close> for R
    supply arrayO_ara_empty_sz_code_rule[sep_heap_rules]
    by sepref_to_hoare (sep_auto simp: arrayO_ara_empty_sz_def fold_cons_replicate)

  show ?thesis
    using 0[FCOMP 1] unfolding n_def[symmetric] PR_CONST_def .
qed


context locale_nat_list
begin
lemma atm_of_uminus_lit_of_nat: \<open> atm_of (- literal_of_nat x) = x div 2\<close>
  by (cases x) auto
lemma in_atms_of_N\<^sub>1_iff:
   \<open>atm_of L \<in> atms_of (twl_array_code.N\<^sub>1 N) \<longleftrightarrow> nat_of_lit L \<in> set N \<or> nat_of_lit (-L) \<in> set N\<close>
proof -
  have [dest]: \<open>x \<in> set N \<Longrightarrow> Suc (2 * (x div 2)) \<in> set N \<or> 2 * (x div 2) \<in> set N\<close> for x
    by (metis Suc_eq_plus1 dvd_mult_div_cancel odd_two_times_div_two_succ)
  show ?thesis
    unfolding twl_array_code.N\<^sub>1_def atms_of_plus twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
      atms_of_def set_mset_union set_mset_mset set_map image_image image_Un atm_of_lit_of_nat
      set_image_mset atm_of_uminus_lit_of_nat
    by (cases L) (auto simp: atms_of_def atm_of_eq_atm_of twl_array_code.N\<^sub>1_def twl_array_code.N\<^sub>0'_def
        twl_array_code.N\<^sub>0''_def image_Un rev_image_eqI)
qed

sepref_register init_state_wl
lemma init_state_wl_D_init_state_wl:
  \<open>(init_state_wl_D, RETURN o (PR_CONST init_state_wl)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a twl_array_code.twl_st_l_trail_assn N\<close>
proof -
  have [simp]: \<open>clauses_l_assn {#} [] = emp\<close>
    by (rule list_mset_assn_empty_nil)
  have [simp]: \<open>clause_l_assn {#} [] = emp\<close>
    by (rule list_mset_assn_empty_nil)
  have [simp]: \<open>nat_assn n n = emp\<close> for n
    by (simp add: pure_app_eq)
  have e: \<open>RETURN $ empty_watched N \<le> SPEC (op = (empty_watched N))\<close>
    by auto
  note imp_correctI[OF arrayO_ara_empty_sz_code_empty_watched[to_hnr] e, sep_heap_rules]

  have [sep_heap_rules]:
      \<open><arlO_assn clause_ll_assn l a * x \<mapsto>\<^sub>a []> arrayO_raa_append a x <arlO_assn clause_ll_assn (l @ [[]])>\<^sub>t\<close>
    for l a x
    using arrayO_raa_append_rule[of clause_ll_assn l a \<open>[]\<close> x, unfolded]
      apply (subst (asm)(2) array_assn_def)
    by (auto simp: hr_comp_def ex_assn_def is_array_def)
  define n where \<open>n = Suc ((fold max N 0) div 2)\<close>

  have n_def_alt: \<open>n = Max (set N) div 2 + 1\<close> if \<open>xa \<in> set N\<close> for xa
    unfolding n_def
    using that by (cases N, auto simp: Max.set_eq_fold list.set(2)[symmetric] simp del: list.set(2))

  have [dest!]:
    \<open>xa \<in> set N \<Longrightarrow> xa div 2 < n\<close>
    for xa
    unfolding n_def_alt using Max_ge[of \<open>set N\<close> xa]
    by (simp_all del: Max_ge)
  have nat_of_lit_div2_atm_of[simp]: \<open>nat_of_lit L div 2  = atm_of L\<close> for L
    by (cases L) auto
  have [simp]: \<open>L \<in># twl_array_code.N\<^sub>1 N \<Longrightarrow> atm_of L < n\<close> for L
    by (auto simp add: in_atms_of_N\<^sub>1_iff twl_array_code.in_N\<^sub>1_iff)
  have [intro!]: \<open>(([], replicate n (None, 0), 0), []) \<in> twl_array_code.trail_ref N\<close>
    by (auto simp: twl_array_code.trail_ref_def twl_array_code.valued_atm_on_trail_def)
  have [simp]: \<open>the_pure (option_assn bool_assn *assn nat_assn) = Id\<close>
    unfolding prod_assn_pure_conv option_assn_pure_conv by auto
  show ?thesis
    supply arl_empty_sz_array_rule[sep_heap_rules del]
    supply arl_empty_sz_array_rule[of _ clause_ll_assn, sep_heap_rules]
    apply sepref_to_hoare
    apply (sep_auto simp: init_state_wl_D_def init_state_wl_def twl_array_code.twl_st_l_trail_assn_def
        twl_array_code.trail_assn_def hr_comp_def n_def shiftr1_def nat_shiftr_div2)
    apply (auto simp: array_assn_def is_array_def hr_comp_def ac_simps)
    done
qed

concrete_definition (in -) init_state_wl_D_code
  uses "locale_nat_list.init_state_wl_D_init_state_wl"
  is "(?f,_)\<in>_"

prepare_code_thms (in -) init_state_wl_D_code_def

lemmas init_state_wl_D_code_refine[sepref_fr_rules] = init_state_wl_D_code.refine[of N]
end

sepref_register locale_nat_list.init_state_wl

text \<open>We declare the rule as \<open>sepref_fr_rules\<close>, once we have discharged the assumption:\<close>
lemma init_state_wl_D_code[unfolded twl_array_code.twl_st_l_trail_assn_def]:
  \<open>(uncurry init_state_wl_D_code, uncurry (RETURN oo locale_nat_list.init_state_wl))
  \<in> [\<lambda>(N', _). N = N']\<^sub>a(list_assn nat_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> twl_array_code.twl_st_l_trail_assn N\<close>
proof -
  have e: \<open>RETURN $ (locale_nat_list.init_state_wl N $ x) \<le> SPEC (op = (locale_nat_list.init_state_wl N x))\<close>
    for x
    by auto
  have [simp]: \<open>hn_val nat_rel x1 x1 = emp\<close> for x1
    by (simp add: hn_ctxt_def pure_def)
  have 1: \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
    by (auto simp: pure_def)
  have [simp]: \<open>list_assn (\<lambda>a c. \<up> (c = a)) a ai = \<up> (a = ai)\<close> for a ai
    unfolding list_assn_pure_conv 1 by (auto simp: pure_def)
  have [sep_heap_rules]: \<open><emp> init_state_wl_D_code N x1
  <\<lambda>r. \<exists>\<^sub>Ara. twl_array_code.twl_st_l_trail_assn N ra r *
               true *
               \<up> (locale_nat_list.init_state_wl N x1 = ra)>\<close> for x1 :: nat
    using imp_correctI[OF init_state_wl_D_code.refine[to_hnr, of x1 x1 N, unfolded PR_CONST_def] e,
        sep_heap_rules, simplified]
    by simp
  show ?thesis
    by sepref_to_hoare sep_auto
qed

text \<open>It is not possible to discharge assumption of the rule directly, but here, it works. This avoids
  guessing form the \<open>sepref\<close> tools:\<close>
declare init_state_wl_D_code[to_hnr, OF refl, sepref_fr_rules]

lemmas init_dt_wl_code_refine[sepref_fr_rules] =
  init_dt_wl_code.refine[unfolded twl_array_code.twl_st_l_trail_assn_def]

lemma XX[unfolded twl_array_code.twl_st_l_trail_assn_def, sepref_fr_rules]:
  \<open>(uncurry cdcl_twl_stgy_prog_wl_D_code, uncurry twl_array_code.cdcl_twl_stgy_prog_wl_D) \<in>
   [\<lambda>(N', _). N' = N]\<^sub>a (list_assn nat_assn)\<^sup>k *\<^sub>a (twl_array_code.twl_st_l_trail_assn N)\<^sup>d \<rightarrow>
   twl_array_code.twl_st_l_trail_assn N\<close>
proof -
  have H: \<open> <R x1 xi1> f xi1
    <\<lambda>r. \<exists>\<^sub>Ara. invalid_assn R x1 xi1 *
                          twl_array_code.twl_st_l_trail_assn N ra r *
                          \<up> (\<Phi> ra)> \<Longrightarrow>
    <R x1 xi1> f xi1 <\<lambda>r. \<exists>\<^sub>Ara.
                          twl_array_code.twl_st_l_trail_assn N ra r * true *
                          \<up> (\<Phi> ra)>\<close>
    for R x1 xi1 f \<Phi>
    apply (sep_auto simp: hoare_triple_def Let_def invalid_assn_def)
    by fast
  have e: \<open>RETURN $ (locale_nat_list.init_state_wl N $ x) \<le> SPEC (op = (locale_nat_list.init_state_wl N x))\<close>
    for x
    by auto
  have [simp]: \<open>hn_val nat_rel x1 x1 = emp\<close> for x1
    by (simp add: hn_ctxt_def pure_def)
  have 1: \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
    by (auto simp: pure_def)
  have [simp]: \<open>list_assn (\<lambda>a c. \<up> (c = a)) a ai = \<up> (a = ai)\<close> for a ai
    unfolding list_assn_pure_conv 1 by (auto simp: pure_def)
  have XX: \<open>twl_array_code.cdcl_twl_stgy_prog_wl_D N x1 \<le> SPEC \<Phi> \<Longrightarrow>
    <twl_array_code.twl_st_l_trail_assn N x1 xi1>
      cdcl_twl_stgy_prog_wl_D_code N xi1
    <\<lambda>r. \<exists>\<^sub>Ara. twl_array_code.twl_st_l_trail_assn N ra r * true * \<up> (\<Phi> ra)>\<close> for x1 xi1 \<Phi>
    apply (rule H)
    using imp_correctI[OF cdcl_twl_stgy_prog_wl_D_code.refine[to_hnr, of N],
        sep_heap_rules, unfolded hn_ctxt_def, of x1 \<Phi> xi1]
    apply (sep_auto simp: hoare_triple_def invalid_assn_def Let_def)
    done
  show ?thesis
    by sepref_to_hoare (sep_auto intro!: XX simp: no_fail_spec_le_RETURN_itself)
qed


(* Taken from Lammich's GRAT:
  TODO: Move, patch Imperative/HOL!
  This patch makes Imperative/HOL array translation also work for index types other than IntInf.
  Note that the toInt-operations are required to raise an Overflow exception on overflow, such that
  creating an array of too big size is safe, and also indexing an array out of bounds will be
  correctly caught.
*)
code_printing constant Array.new' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ (IntInf.toInt _,/ (_)))"
code_printing constant Array.make' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ (IntInf.toInt _,/ _ o IntInf.fromInt))"
code_printing constant Array.len' \<rightharpoonup> (SML) "(fn/ ()/ =>/ IntInf.fromInt (Array.length/ _))"
code_printing constant Array.nth' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ IntInf.toInt _))"
code_printing constant Array.upd' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ IntInf.toInt _,/ (_)))"


(*
  TODO: Patch that belongs to array_blit.thy.
  Already in Lammich's local AFP copy!
*)
code_printing code_module "array_blit" \<rightharpoonup> (SML)
  {*
  (* Locally patched version  *)
  fun array_blit src si dst di len = (
    src=dst andalso raise Fail ("array_blit: Same arrays");
    ArraySlice.copy {
      di = IntInf.toInt di,
      src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
      dst = dst})

  fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
  fun array_upd_oo f i x a () =
    (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

  *}

  (* TODO: Export to other languages: OCaml, Haskell, Scala *)
code_printing constant blit' \<rightharpoonup>
  (SML) "(fn/ ()/ => /array'_blit _ _ _ _ _)"
  and (Scala) "{ ('_: Unit)/=>/
    def safecopy(src: Array['_], srci: Int, dst: Array['_], dsti: Int, len: Int) = {
      if (src eq dst)
        sys.error(\"array'_blit: Same arrays\")
      else
        System.arraycopy(src, srci, dst, dsti, len)
    }
    safecopy(_.array,_.toInt,_.array,_.toInt,_.toInt)
  }"


sepref_definition SAT_wl_code
  is \<open>SAT_wl'\<close>
  :: \<open>(list_assn (list_assn nat_lit_assn))\<^sup>d \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding SAT_wl'_def HOL_list.fold_custom_empty extract_lits_cls'_extract_lits_cls[symmetric]
    PR_CONST_def twl_array_code.get_conflict_wl_is_None
  supply twl_array_code.get_conflict_wl_is_None_code_refine[sepref_fr_rules]
  supply [[goals_limit = 1]]
  by sepref


declare locale_nat_list.init_state_wl_D_def[code]

code_printing constant "shiftl :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup>
  (SML) "(nat'_of'_integer(IntInf.<</ (integer'_of'_nat((_)),/ Word.fromInt (integer'_of'_nat((_))))))"

code_printing constant "shiftr :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup>
  (SML) "(nat'_of'_integer(IntInf.~>>/ (integer'_of'_nat((_)),/ Word.fromInt (integer'_of'_nat((_))))))"

export_code SAT_wl_code checking SML_imp
export_code SAT_wl_code
    int_of_integer
    integer_of_int
    integer_of_nat
    nat_of_integer
  in Scala_imp module_name SAT_Solver file "code/full_SAT_Cached_Trail.scala"

definition TWL_to_clauses_state_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset) set\<close> where
  \<open>TWL_to_clauses_state_conv = {(S', S). S = state\<^sub>W_of (twl_st_of_wl None S')}\<close>

lemma list_all2_eq_map_iff: \<open>list_all2 (\<lambda>x y. y = f x) xs ys \<longleftrightarrow> ys = map f xs\<close>
  apply (induction xs arbitrary: ys)
  subgoal by auto
  subgoal for a xs ys
    by (cases ys) auto
  done

lemma SPEC_add_information: \<open>P \<Longrightarrow> A \<le> SPEC Q \<Longrightarrow> A \<le> SPEC(\<lambda>x. Q x \<and> P)\<close>
  by auto

lemma cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and> (\<forall>C \<in># CS. size C \<ge> 1) \<and>
        (\<forall>C \<in># CS. \<not>tautology C)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>TWL_to_clauses_state_conv\<rangle>nres_rel\<close>
proof -
  have in_list_mset_rel: \<open>(CS', y) \<in> list_mset_rel \<longleftrightarrow> y = mset CS'\<close> for CS' y
    by (auto simp: list_mset_rel_def br_def)
  have in_list_mset_rel_mset_rel:
    \<open>(mset CS', CS) \<in> \<langle>list_mset_rel\<rangle>mset_rel \<longleftrightarrow> CS = mset `# mset CS'\<close> for CS CS'
    by (auto simp: list_mset_rel_def br_def mset_rel_def p2rel_def rel_mset_def
        rel2p_def[abs_def] list_all2_eq_map_iff)
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  show ?thesis
    unfolding SAT_wl_def SAT_def locale_nat_list.init_state_wl_def empty_watched_def
  apply (intro frefI nres_relI)
    apply (refine_vcg bind_refine_spec init_dt_init_dt_l)
       defer
    subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    subgoal by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
    subgoal premises p for CS' CS S\<^sub>0
    proof (cases \<open>get_conflict_wl S\<^sub>0 = None\<close>)
      case False
      then have confl: \<open>get_conflict_wl S\<^sub>0 = None \<longleftrightarrow> False\<close>
        by auto
      have CS: \<open>CS = mset `# mset CS'\<close>
        using p by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      show ?thesis
        unfolding confl if_False
        apply (rule RETURN_SPEC_refine)
        apply (rule exI[of _ \<open>state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0))\<close>])
        apply (intro conjI)
       subgoal using p confl by (cases S\<^sub>0, clarsimp_all simp: TWL_to_clauses_state_conv_def mset_take_mset_drop_mset'
            clauses_def get_unit_learned_def in_list_mset_rel in_list_mset_rel_mset_rel)
       subgoal
         apply (rule disjI2)
         using p False by (cases S\<^sub>0) (clarsimp simp: twl_struct_invs_def CS init_state_def full_def
             cdcl\<^sub>W_restart_mset_state get_unit_learned_def)
        done
    next
      case True
      then have confl: \<open>get_conflict_wl S\<^sub>0 = None \<longleftrightarrow> True\<close>
        by auto
      obtain M N NP Q W where
        S\<^sub>0: \<open>S\<^sub>0 = (M, N, length N - 1, None, NP, {#}, Q, W)\<close>
        using p True by (cases S\<^sub>0) (auto simp: clauses_def mset_take_mset_drop_mset' get_unit_learned_def)
      have N_NP: \<open>mset `# mset (tl N) + NP = mset `# mset CS'\<close>
        using p by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0)
      have trail_in_NP: \<open>\<forall>L\<in>lits_of_l M. {#L#} \<in># NP\<close> and
        struct: \<open>twl_struct_invs (twl_st_of_wl None S\<^sub>0)\<close>
        using p unfolding S\<^sub>0 by (auto simp: get_unit_init_clss_def)
      have n_d: \<open>no_dup M\<close>
        using struct by (auto simp: twl_struct_invs_def S\<^sub>0
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
            cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def)
      have prop_M: \<open>\<forall>L\<in> set M. \<exists>K. L = Propagated K 0\<close>
        using p by (auto simp: S\<^sub>0)
      have CS: \<open>CS = mset `# mset CS'\<close>
        using p by (auto simp: in_list_mset_rel in_list_mset_rel_mset_rel)
      have 0: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], CS, {#}, None)
         (convert_lits_l N M, mset `# mset CS', {#}, None)\<close>
        using trail_in_NP prop_M n_d
        apply (induction M)
        subgoal by (auto simp: CS)
        subgoal for L M
          apply simp
          apply (rule rtranclp.rtrancl_into_rtrancl)
           apply assumption
          apply (rule cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.propagate')
            apply (cases L)
           apply (auto simp: cdcl\<^sub>W_restart_mset.propagate.simps cdcl\<^sub>W_restart_mset_state clauses_def CS
              N_NP[symmetric])
          done
        done
      then have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (init_state CS)
         (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0)))\<close>
        using 0 by (auto simp: S\<^sub>0 CS mset_take_mset_drop_mset' N_NP init_state_def)
      have 2: \<open>twl_array_code.cdcl_twl_stgy_prog_wl_D (map nat_of_lit (extract_lits_clss CS' [])) S\<^sub>0
         \<le> SPEC (\<lambda>T. full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy
                       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None S\<^sub>0)))
                       (state\<^sub>W_of (twl_st_of None (st_l_of_wl None T))))\<close>
        using twl_array_code.cdcl_twl_stgy_prog_wl_spec_final2[of S\<^sub>0 \<open>(map nat_of_lit (extract_lits_clss CS' []))\<close>]
        using p 1 True by auto

      have \<open>twl_array_code.cdcl_twl_stgy_prog_wl_D (map nat_of_lit (extract_lits_clss CS' [])) S\<^sub>0
        \<le> \<Down> TWL_to_clauses_state_conv
        (SPEC (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy (init_state CS)))\<close>
        by (auto simp: TWL_to_clauses_state_conv_def conc_fun_RES rtranclp_fullI
            intro!: weaken_SPEC[OF SPEC_add_information[OF 1 2]])
      then show ?thesis
        unfolding confl if_True by (rule ref_two_step) auto
    qed
    done
qed

definition is_SAT :: \<open>'a clauses \<Rightarrow> bool nres\<close> where
  \<open>is_SAT CS = RETURN (satisfiable (set_mset CS))\<close>

definition SAT' :: \<open>nat clauses \<Rightarrow> bool nres\<close> where
  \<open>SAT' CS = do {
     T \<leftarrow> SAT CS;
     RETURN(conflicting T = None)
  }
\<close>

lemma SPEC_RETURN_RES: \<open>SPEC \<Phi> \<bind> (\<lambda>T. RETURN (f T)) = RES (f ` {T. \<Phi> T})\<close>
  by (simp add: bind_RES_RETURN_eq setcompr_eq_image)

lemma true_clss_clss_true_clss_cls_true_clss_clss:
  assumes
    \<open>A \<Turnstile>ps unmark_l M\<close> and \<open>M \<Turnstile>as D\<close>
  shows \<open>A \<Turnstile>ps D\<close>
  by (meson assms total_over_m_union true_annots_true_cls true_annots_true_clss_clss
      true_clss_clss_def true_clss_clss_left_right true_clss_clss_union_and
      true_clss_clss_union_l_r)

lemma true_clss_clss_CNot_true_clss_cls_unsatisfiable:
  assumes \<open>A \<Turnstile>ps CNot D\<close> and \<open>A \<Turnstile>p D\<close>
  shows \<open>unsatisfiable A\<close>
  using assms(2) unfolding true_clss_clss_def true_clss_cls_def satisfiable_def
  by (metis (full_types) Un_absorb Un_empty_right assms(1) atms_of_empty
      atms_of_ms_emtpy_set total_over_m_def total_over_m_insert total_over_m_union
      true_cls_empty true_clss_cls_def true_clss_clss_generalise_true_clss_clss
      true_clss_clss_true_clss_cls true_clss_clss_union_false_true_clss_clss_cnot)

context conflict_driven_clause_learning\<^sub>W
begin

lemma rtranclp_cdcl\<^sub>W_restart_learned_clauses_entailed:
  assumes
    \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
  using assms(1)
proof (induction)
  case base
  then show ?case using assms by fast
next
  case (step T U) note ST = this(1) and TU = this(2) and learned = this(3)
  have \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using assms(2) rtranclp_cdcl\<^sub>W_all_struct_inv_inv step.hyps(1) by blast
  then have l: \<open>cdcl\<^sub>W_learned_clause T\<close>
    by (auto simp: cdcl\<^sub>W_all_struct_inv_def)
  from TU l learned show ?case
    by (rule cdcl\<^sub>W_learned_clauses_entailed)
qed

lemma rtranclp_cdcl\<^sub>W_stgy_learned_clauses_entailed:
  assumes
    \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T\<close> and
    \<open>cdcl\<^sub>W_all_struct_inv S\<close> and
    \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init T\<close>
  using assms rtranclp_cdcl\<^sub>W_restart_learned_clauses_entailed rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
  by blast
end

lemma conflict_of_level_unsatisfiable:
  assumes
    struct: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S\<close> and
    dec: \<open>count_decided (trail S) = 0\<close> and
    confl: \<open>conflicting S \<noteq> None\<close> and
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init S\<close>
  shows \<open>unsatisfiable (set_mset (cdcl\<^sub>W_restart_mset.clauses S))\<close>
proof -

  obtain M N U D where S: \<open>S = (M, N, U, Some D)\<close>
    by (cases S) (use confl in \<open>auto simp: cdcl\<^sub>W_restart_mset_state\<close>)

  have [simp]: \<open>get_all_ann_decomposition M = [([], M)]\<close>
    by (rule no_decision_get_all_ann_decomposition)
      (use dec in \<open>auto simp: count_decided_def filter_empty_conv S cdcl\<^sub>W_restart_mset_state\<close>)
  have
    N_U: \<open>N \<Turnstile>psm U\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close> and
    N_U_M: \<open>set_mset N \<union> set_mset U \<Turnstile>ps unmark_l M\<close> and
    n_d: \<open>no_dup M\<close> and
    N_U_D: \<open>set_mset N \<union> set_mset U \<Turnstile>p D\<close>
    using assms
    by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def all_decomposition_implies_def
        cdcl\<^sub>W_restart_mset_state S clauses_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def)
  have \<open>set_mset N \<union> set_mset U \<Turnstile>ps CNot D\<close>
    by (rule true_clss_clss_true_clss_cls_true_clss_clss[OF N_U_M M_D])
  then have \<open>set_mset N \<Turnstile>ps CNot D\<close> \<open>set_mset N \<Turnstile>p D\<close>
    using N_U N_U_D true_clss_clss_left_right by blast+
  then have \<open>unsatisfiable (set_mset N)\<close>
    by (rule true_clss_clss_CNot_true_clss_cls_unsatisfiable)

  then show ?thesis
    by (auto simp: cdcl\<^sub>W_restart_mset_state S clauses_def dest: satisfiable_decreasing)
qed

lemma SAT_is_SAT:
  \<open>(SAT', is_SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and> (\<forall>C \<in># CS. size C \<ge> 1) \<and>
      (\<forall>C \<in># CS. \<not>tautology C)]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
    (is \<open>_ \<in>[\<lambda>CS. ?P CS]\<^sub>f Id \<rightarrow> _\<close>)
proof -
  have H: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant (init_state CS)\<close>
    \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (init_state CS)\<close>
    if \<open>?P CS\<close> for CS
    using that by (auto simp: init_state_def
        twl_struct_invs_def twl_st_inv.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.no_strange_atm_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
        cdcl\<^sub>W_restart_mset.distinct_cdcl\<^sub>W_state_def cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def cdcl\<^sub>W_restart_mset.no_smaller_propa_def
        past_invs.simps clauses_def additional_WS_invs_def twl_stgy_invs_def clause_to_update_def
        cdcl\<^sub>W_restart_mset_state cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy_invariant_def
        cdcl\<^sub>W_restart_mset.no_smaller_confl_def get_unit_learned_def
        distinct_mset_set_def)
  show ?thesis
    unfolding SAT'_def is_SAT_def SAT_def
    apply (intro frefI nres_relI)
    subgoal for CS' CS
      using H[of CS]
        cdcl\<^sub>W_restart_mset.full_cdcl\<^sub>W_stgy_inv_normal_form[of \<open>init_state CS\<close>]
      by (auto intro!: le_SPEC_bindI simp: SPEC_RETURN_RES clauses_def
          cdcl\<^sub>W_restart_mset_state init_state_def
          cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clauses_entailed_by_init_def
          dest: conflict_of_level_unsatisfiable) blast
    done
qed

lemma list_assn_list_mset_rel_clauses_l_assn:
  \<open>(hr_comp (list_assn (list_assn nat_lit_assn)) (list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel)) xs xs'
     = clauses_l_assn xs xs'\<close>
proof -
  have H: \<open>(\<lambda>a c. \<up> ((c, a) \<in> nat_lit_rel)) = pure nat_lit_rel\<close>
    by (auto simp: pure_def)

  have [simp]: \<open>the_pure (\<lambda>a c. \<up> ((c, a) \<in> nat_lit_rel)) = nat_lit_rel\<close>
    unfolding H by simp

  have l_swap:  \<open>(\<lambda>x y. y = mset x) = (\<lambda>x. op = (mset x))\<close>
    by auto
  have [simp]: \<open>list_all2 (list_all2 lit_of_natP) xs' x \<longleftrightarrow> x = map (map literal_of_nat) xs'\<close> for x
    unfolding list_all2_op_eq_map_map_right_iff lit_of_natP_def ..
  have [iff]: \<open>rel_mset (rel2p {(c, a). a = mset c}) X Y \<longleftrightarrow> mset `# X = Y\<close> for X Y
    using ex_mset[of X]
    by (auto simp: rel_mset_def rel2p_def[abs_def] list_all2_op_eq_map_left_iff
        list_all2_op_eq_map_right_iff l_swap)
  have rel_mset_eq: \<open>rel_mset (\<lambda>x. op = (f x)) X Y \<longleftrightarrow> Y = f `# X\<close> for X Y f
    using ex_mset[of X]
    by (auto simp: rel_mset_def[abs_def] p2rel_def list_all2_op_eq_map_right_iff)
  have [simp]: \<open>(x, y) \<in> p2rel (\<lambda>c. rel_mset (\<lambda>x. op = (f x)) (mset c)) \<longleftrightarrow>
     y = f `# mset x\<close> for f x y
    unfolding rel_mset_eq by (auto simp: p2rel_def)
  have H: \<open>(\<lambda>a c. \<up> (rel_mset (rel2p {(x, y). literal_of_nat x = y}) (mset c) a)) =
          pure (p2rel (\<lambda>c a. rel_mset (rel2p {(x, y). literal_of_nat x = y}) (mset c) a))\<close>
    by (auto simp: pure_def rel2p_def rel_mset_def p2rel_def simp del: literal_of_nat.simps intro!: ext )
  have [simp]: \<open>rel2p (the_pure (\<lambda>a c. \<up> (rel_mset (rel2p {(x, y). literal_of_nat x = y}) (mset c) a))) =
      (\<lambda>c a. (rel_mset (rel2p {(x, y). literal_of_nat x = y}) (mset c) a))\<close>
    unfolding H
    by (auto simp: rel2p_def[abs_def] rel_mset_def list_all2_op_eq_map_map_left_iff
        list_all2_op_eq_map_map_right_iff list_all2_op_eq_map_right_iff
        simp del: literal_of_nat.simps intro!: ext)
  have H: \<open>(\<lambda>c Y. Y = f `# mset c) = (% c. op= (f `# mset c))\<close> for f
    by auto
  have [simp]: \<open>rel_mset (\<lambda>c. rel_mset (rel2p {(x, y). f x = y}) (mset c)) (mset xs')
     xs \<longleftrightarrow> xs = (mset `# mset (map (map f) xs'))\<close> for f
    by (auto simp: rel_mset_def rel2p_def[abs_def]  list_all2_op_eq_map_map_left_iff
        list_all2_op_eq_map_map_right_iff list_all2_op_eq_map_right_iff
        rel_mset_eq[abs_def] list_all2_op_eq_map_left_iff H)

  show ?thesis
    apply (auto simp: hr_comp_def list_assn_pure_conv)
    apply (auto simp: ent_ex_up_swap list_mset_assn_def pure_def list_rel_def)
    by (clarsimp_all simp add: list_mset_rel_def br_def mset_rel_def
        p2rel_def Collect_eq_comp rel2p_def lit_of_natP_def[abs_def] list_all2_op_eq_map_map_left_iff
        list_all2_op_eq_map_map_right_iff simp del: literal_of_nat.simps)
qed

lemma \<open>(SAT_wl_code, SAT')
    \<in> [\<lambda>x. Multiset.Ball x distinct_mset \<and> (\<forall>C\<in>#x. Suc 0 \<le> size C) \<and> (\<forall>C\<in>#x. \<not> tautology C)]\<^sub>a
      clauses_l_assn\<^sup>d \<rightarrow> bool_assn\<close>
proof -
  have 1: \<open>(H \<bind>
    (\<lambda>T. if get_conflict_wl T = None
          then twl_array_code.cdcl_twl_stgy_prog_wl_D
                (map nat_of_lit (extract_lits_clss CS [])) T \<bind>
               (\<lambda>U. RETURN (get_conflict_wl U = None))
          else RETURN False)) =
    (H \<bind>
     (\<lambda>T. if get_conflict_wl T = None
           then twl_array_code.cdcl_twl_stgy_prog_wl_D
                 (map nat_of_lit (extract_lits_clss CS [])) T
           else RETURN T)) \<bind>
    (\<lambda>T. RETURN (get_conflict_wl T = None))\<close> for H CS
    by (smt bind_cong nres_monad1 nres_monad3)

  have SAT_wl': \<open>SAT_wl' CS = do {T \<leftarrow> SAT_wl CS; RETURN (get_conflict_wl T = None)}\<close> for CS
    unfolding SAT_wl'_def SAT_wl_def Let_def map_nat_of_lit_def
    by (auto cong: bind_cong simp: 1)
  have 2: \<open>Multiset.Ball y distinct_mset \<and>
       (\<forall>C\<in>#y. 1 \<le> size C) \<and> (\<forall>C\<in>#y. \<not> tautology C) \<Longrightarrow>
       (x, y) \<in> list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<Longrightarrow>
       SAT_wl x \<le> \<Down> TWL_to_clauses_state_conv (SAT y)\<close> for x y
    using cdcl_twl_stgy_prog_wl_spec_final2[unfolded fref_def nres_rel_def] by simp

  have SAT_wl'_SAT: \<open>(SAT_wl', SAT')\<in>
     [\<lambda>CS. Multiset.Ball CS distinct_mset \<and> (\<forall>C\<in>#CS. 1 \<le> size C) \<and> (\<forall>C\<in>#CS. \<not> tautology C)]\<^sub>f
     list_mset_rel O \<langle>list_mset_rel\<rangle>mset_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding SAT'_def SAT_wl'
    apply (intro frefI nres_relI bind_refine)
     apply (rule 2; simp)
    by (auto simp: TWL_to_clauses_state_conv_def cdcl\<^sub>W_restart_mset_state)
  show ?thesis
    using SAT_wl_code.refine[FCOMP SAT_wl'_SAT] unfolding list_assn_list_mset_rel_clauses_l_assn .
qed

end