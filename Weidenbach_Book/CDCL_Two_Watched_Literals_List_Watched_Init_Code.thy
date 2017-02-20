theory CDCL_Two_Watched_Literals_List_Watched_Init_Code
imports CDCL_Two_Watched_Literals_List_Watched_Code
begin

type_synonym 'v twl_st_wl' =
  "('v, nat) ann_lits \<times> 'v clause_l list \<times> nat \<times>
    'v cconflict \<times> 'v clauses \<times> 'v clauses \<times> 'v lit_queue_wl"

type_synonym twl_st_wll' =
  "nat_trail \<times> clauses_wl \<times> nat \<times> nat array_list option \<times> unit_lits_wl \<times> unit_lits_wl \<times>
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
    by sepref_to_hoare (sep_auto simp: array_of_list_def array_assn_def[symmetric])
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

definition extract_lits_cls :: \<open>'a clause_l \<Rightarrow> 'a literal list \<Rightarrow> 'a literal list\<close> where
  \<open>extract_lits_cls C N\<^sub>0 = fold (\<lambda>L N\<^sub>0. if atm_of L \<in> atms_of (mset N\<^sub>0) then N\<^sub>0 else L # N\<^sub>0) C N\<^sub>0\<close>

definition extract_lits_clss:: \<open>'a clauses_l \<Rightarrow> 'a literal list \<Rightarrow> 'a literal list\<close>  where
  \<open>extract_lits_clss N N\<^sub>0 = fold extract_lits_cls N N\<^sub>0\<close>

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
    subgoal by (auto simp: extract_lits_cls_def extract_lits_clss_def  twl_array_code.is_N\<^sub>1_def
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

definition HH :: \<open>nat literal multiset \<Rightarrow> (nat twl_st_wl \<times> nat twl_st_l) set\<close> where
  \<open>HH N\<^sub>1 = {((M', N', U', D', NP', UP', Q', WS'), (M, N, U, D, NP, UP, WS, Q)).
               M = M' \<and> N = N' \<and> U = U' \<and> D = D' \<and> NP = NP' \<and> UP = UP' \<and> Q = Q' \<and> WS = {#} \<and>
               U = length N - 1 \<and> UP = {#} \<and> N \<noteq> [] \<and>
               correct_watching_init N\<^sub>1 (M', N', U', D', NP', UP', Q', WS') \<and>
               set_mset (lits_of_atms_of_mm (mset `# mset N)) \<subseteq> set_mset N\<^sub>1}\<close>

lemma clause_to_update_append: \<open>N \<noteq> [] \<Longrightarrow> clause_to_update La (M, N @ [C], U, D, NP, UP, WS, Q) =
     clause_to_update La (M, N, U, D, NP, UP, WS, Q) +
    (if La \<in> set (watched_l C) then {#length N#} else {#})\<close>
  unfolding clause_to_update_def get_clauses_l.simps
  apply (auto simp: clause_to_update_def nth_append)
  by meson

lemma literal_of_nat_literal_of_nat_eq[iff]: \<open>literal_of_nat x = literal_of_nat xa \<longleftrightarrow> x = xa\<close>
  by auto presburger+
thm twl_array_code.literals_are_in_N\<^sub>0_def

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
    subgoal by (auto simp: HH_def)
    subgoal by (cases C) (auto simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (auto simp: HH_def)
    subgoal by (cases C) (clarsimp_all simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (clarsimp simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' lits_of_atms_of_m_add_mset
          lits_of_atms_of_mm_add_mset literals_are_in_N\<^sub>0_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    subgoal by fast
    subgoal by (auto simp: HH_def)
    subgoal by (cases C; cases \<open>tl C\<close>) (clarsimp_all simp: HH_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset image_image
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' image_image lits_of_atms_of_m_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    subgoal by (cases C; cases \<open>tl C\<close>) (auto simp: HH_def Let_def clause_to_update_append
          clauses_def mset_take_mset_drop_mset' lits_of_atms_of_m_add_mset
          lits_of_atms_of_mm_add_mset literals_are_in_N\<^sub>0_add_mset
          twl_array_code.literals_are_in_N\<^sub>0_def)
    done
qed

definition init_dt_wl where
  \<open>init_dt_wl N\<^sub>1 CS S = nfoldli CS (\<lambda>_. True) (init_dt_step_wl N\<^sub>1) S\<close>

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
     apply (rule init_dt_step_wl_init_dt_step_l)
    unfolding N\<^sub>1_def[symmetric]
       apply (solves \<open>simp add: N\<^sub>1_def\<close>)
      apply (solves \<open>simp\<close>)
     apply (solves \<open>simp\<close>)
    apply (rule p(1)[unfolded init_dt_wl_def init_dt_l_def])
      apply (solves \<open>simp\<close>)
     apply (solves \<open>simp\<close>)
    apply (solves \<open>simp\<close>)
    done
  done


end