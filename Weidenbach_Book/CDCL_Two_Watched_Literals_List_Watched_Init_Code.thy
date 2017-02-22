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
               (* U = length N - 1 \<and> *) UP = {#} \<and> N \<noteq> [] \<and>
               correct_watching_init N\<^sub>1 (M', N', U', D', NP', UP', Q', WS') \<and>
               set_mset (lits_of_atms_of_mm (mset `# mset (tl N) + NP)) \<subseteq> set_mset N\<^sub>1}\<close>

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
    subgoal by (cases C) (clarsimp_all simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
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
    subgoal by (cases C) (clarsimp_all simp: HH_def correct_watching.simps clause_to_update_def
          lits_of_atms_of_mm_add_mset lits_of_atms_of_m_add_mset twl_array_code.N\<^sub>1_def
          twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
          twl_array_code.literals_are_in_N\<^sub>0_def clauses_def mset_take_mset_drop_mset')
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

definition init_dt_wl :: \<open>nat list \<Rightarrow> nat clauses_l \<Rightarrow> nat twl_st_wl \<Rightarrow> (nat twl_st_wl) nres\<close> where
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
     apply (rule init_dt_step_wl_init_dt_step_l[of _ _ N\<^sub>0, unfolded N\<^sub>1_def[symmetric]]; solves \<open>simp\<close>)
    apply (rule p(1)[unfolded init_dt_wl_def init_dt_l_def]; solves \<open>simp\<close>)
    done
  done

abbreviation twl_code_array_literals_are_N\<^sub>0 where
  \<open>twl_code_array_literals_are_N\<^sub>0 N\<^sub>0 S \<equiv>
     twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of_wl None S))))\<close>

fun get_clauses_wl :: "'v twl_st_wl \<Rightarrow> 'v clauses_l" where
  \<open>get_clauses_wl (M, N, U, D, NP, UP, WS, Q) = N\<close>

fun get_learned_wl :: "'v twl_st_wl \<Rightarrow> nat" where
  \<open>get_learned_wl (M, N, U, D, NP, UP, WS, Q) = U\<close>
term get_learned_l
thm init_dt_init_dt_l
thm init_dt_full
lemma lits_of_atms_of_mm_in_lits_of_atms_of_m_in_iff:
  \<open>set_mset (lits_of_atms_of_mm (mset `# mset CS)) \<subseteq> A \<longleftrightarrow>
    (\<forall>C\<in>set CS. set_mset (lits_of_atms_of_m (mset C)) \<subseteq> A)\<close>
  by (auto simp: lits_of_atms_of_mm_def lits_of_atms_of_m_def)

definition get_unit_learned :: "'v twl_st_wl \<Rightarrow> 'v clauses" where
  \<open>get_unit_learned = (\<lambda>(M, N, U, D, NP, UP, Q, W). UP)\<close>

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
    confl: \<open>get_conflict_wl S = None \<longrightarrow> pending_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init N\<^sub>1 S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (convert_to_state (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset N\<^sub>1\<close> and
    no_learned: \<open>get_unit_learned S = {#}\<close> and
    confl_in_clss: \<open>get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS\<close>
  shows
    \<open>init_dt_wl N\<^sub>0 CS S \<le> SPEC(\<lambda>T.
       twl_array_code.is_N\<^sub>1 N\<^sub>0 (lits_of_atms_of_mm (mset `# mset CS +
          cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (st_l_of_wl None S))))) \<and>
       twl_struct_invs (twl_st_of_wl None T) \<and> twl_stgy_invs (twl_st_of_wl None T) \<and>
       additional_WS_invs (st_l_of_wl None T) \<and>
       correct_watching_init N\<^sub>1 T \<and>
       cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (st_l_of_wl None T))) =
         mset `# mset CS +
         cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (st_l_of_wl None S))) \<and>
      get_unit_learned T = {#} \<and>
      get_learned_wl T = length (get_clauses_wl T) - 1 \<and>
      count_decided (get_trail_wl T) = 0 \<and>
      (get_conflict_wl T \<noteq> None \<longrightarrow> the (get_conflict_wl T) \<in># mset `# mset CS))\<close>
proof -
  define T where \<open>T = st_l_of_wl None S\<close>
  have N\<^sub>0_N\<^sub>1: \<open>twl_array_code.N\<^sub>1 N\<^sub>0 = N\<^sub>1\<close>
    by (auto simp: twl_array_code.N\<^sub>1_def N\<^sub>1_def twl_array_code.N\<^sub>0''_def twl_array_code.N\<^sub>0'_def
        simp del: nat_of_lit.simps literal_of_nat.simps)
  have w_q: \<open>working_queue_l T = {#}\<close>
    by (cases S) (simp add: T_def)
  have tr_T_S: \<open>get_trail_l T = get_trail_wl S\<close> and p_T_S: \<open>pending_l T = pending_wl S\<close> and
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
    w_q_T: \<open>working_queue_l T = {#}\<close> and
    tr_T: \<open>\<forall>s\<in>set (get_trail_l T). \<not> is_decided s\<close> and
    c_T: \<open>get_conflict_l T = None \<longrightarrow> pending_l T = uminus `# lit_of `# mset (get_trail_l T)\<close> and
    add_invs_T: \<open>additional_WS_invs T\<close> and
    le_T: \<open>get_learned_l T = length (get_clauses_l T) - 1\<close> and
    confl_in_clss_T: \<open>get_conflict_l T \<noteq> None \<longrightarrow> the (get_conflict_l T) \<in># mset `# mset (rev CS)\<close>
    by (use assms(3-) in \<open>simp add: T_def[symmetric]  w_q tr_T_S p_T_S c_T_S l_T_S cl_T_S\<close>)+
  note init = init_dt_full[of \<open>rev CS\<close> T, OF dist_T length_T taut_T struct_T w_q_T tr_T c_T
      add_invs_T le_T stgy_T ] init_dt_confl_in_clauses[OF confl_in_clss_T]
  have i: \<open>init_dt_l CS T \<le> \<Down> Id (SPEC(\<lambda>T. twl_struct_invs (twl_st_of None T) \<and> twl_stgy_invs (twl_st_of None T) \<and>
      cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None T)) =
        mset `# mset CS + cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of_wl None S)) \<and>
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
      (convert_to_state (twl_st_of None (st_l_of_wl None S))))) \<subseteq>
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
    subgoal using clss watch S_N\<^sub>1 no_learned
      by (auto simp: HH_def T_def clauses_def mset_take_mset_drop_mset' get_unit_learned_def
          simp del: correct_watching_init.simps)
    subgoal using CS_N\<^sub>1 by auto
    subgoal using dist .
    subgoal using is_N\<^sub>1 CS_N\<^sub>1' S_N\<^sub>1 unfolding conc_fun_RES
      by (clarsimp simp: HH_def lits_of_atms_of_mm_union mset_take_mset_drop_mset'
          clauses_def get_unit_learned_def)
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
       cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (st_l_of_wl None S))) =
         mset `# mset CS \<and>
       (get_conflict_wl S \<noteq> None \<longrightarrow> the (get_conflict_wl S) \<in># mset `# mset CS))\<close>
proof -
  have clss_empty: \<open>cdcl\<^sub>W_restart_mset.clauses (convert_to_state (twl_st_of None (st_l_of_wl None S))) = {#}\<close>
    by (auto simp: S_def  cdcl\<^sub>W_restart_mset.clauses_def cdcl\<^sub>W_restart_mset_state)
  have
    struct: \<open>twl_struct_invs (twl_st_of_wl None S)\<close> and
    dec:\<open>\<forall>s\<in>set (get_trail_wl S). \<not>is_decided s\<close> and
    confl: \<open>get_conflict_wl S = None \<longrightarrow> pending_wl S = uminus `# lit_of `# mset (get_trail_wl S)\<close> and
    aff_invs: \<open>additional_WS_invs (st_l_of_wl None S)\<close> and
    learned: \<open>get_learned_wl S = length (get_clauses_wl S) - 1\<close> and
    stgy_invs: \<open>twl_stgy_invs (twl_st_of_wl None S)\<close> and
    watch: \<open>correct_watching_init N\<^sub>1 S\<close> and
    clss: \<open>get_clauses_wl S \<noteq> []\<close> and
    S_N\<^sub>1: \<open>set_mset (lits_of_atms_of_mm (cdcl\<^sub>W_restart_mset.clauses
      (convert_to_state (twl_st_of None (st_l_of_wl None S))))) \<subseteq> set_mset N\<^sub>1\<close> and
    no_learned: \<open>(\<lambda>(M, N, U, D, NP, UP, Q, W). UP) S = {#}\<close> and
    learned_nil: \<open>get_unit_learned S = {#}\<close> and
    confl_nil: \<open>get_conflict_wl S = None\<close>
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
        unfolded empty_neutral]
  have [simp]: \<open>mset `# mset (take ag (tl af)) + ai + (mset `# mset (drop (Suc ag) af)) =
     mset `# mset (tl af) + ai\<close> for ag af aj ai
    by (subst (2) append_take_drop_id[symmetric, of \<open>tl af\<close> ag], subst mset_append)
      (auto simp: drop_Suc)
  have [simp]: \<open>twl_array_code.N\<^sub>1 N\<^sub>0 = N\<^sub>1\<close>
    by (auto simp: N\<^sub>1_def twl_array_code.N\<^sub>1_def  twl_array_code.N\<^sub>0''_def  twl_array_code.N\<^sub>0'_def)
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
        mset_take_mset_drop_mset' get_unit_learned_def confl_nil)
qed
term cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy

definition init_state :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset\<close> where
  \<open>init_state N = (([]:: (nat, nat clause) ann_lits), (N :: nat clauses), ({#}::nat clauses),
      (None :: nat clause option))\<close>

definition init_state_wl :: \<open>nat twl_st_wl\<close> where
  \<open>init_state_wl = ([], [[]], 0, None, {#}, {#}, {#}, \<lambda>_. [])\<close>

definition SAT :: \<open>nat clauses \<Rightarrow> nat cdcl\<^sub>W_restart_mset nres\<close> where
  \<open>SAT CS = do{
    let T = init_state CS;
    SPEC (full cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy T)
  }\<close>

definition trivial_skip_and_resolve :: \<open> nat twl_st_wl \<Rightarrow> nat twl_st_wl\<close> where
  \<open>trivial_skip_and_resolve = (\<lambda>(M, N, U, D', NP, UP, Q, W). ([], N, U, Some {#}, NP, UP, Q, W))\<close>

definition SAT_wl :: \<open>nat clauses_l \<Rightarrow> nat twl_st_wl nres\<close> where
  \<open>SAT_wl CS = do{
    let N\<^sub>0 = map nat_of_lit (extract_lits_clss CS []);
    let S = init_state_wl;
    T \<leftarrow> init_dt_wl N\<^sub>0 CS S;
    if get_conflict_wl T = None
    then twl_array_code.cdcl_twl_stgy_prog_wl_D N\<^sub>0 T
    else RETURN (trivial_skip_and_resolve T)
  }\<close>

definition f_conv :: \<open>(nat twl_st_wl \<times> nat cdcl\<^sub>W_restart_mset)set\<close> where
  \<open>f_conv = {(S', S). S = convert_to_state (twl_st_of_wl None S')}\<close>

lemma list_all2_eq_map_iff: \<open>list_all2 (\<lambda>x y. y = f x) xs ys \<longleftrightarrow> ys = map f xs\<close>
  apply (induction xs arbitrary: ys)
  subgoal by auto
  subgoal for a xs ys
    by (cases ys) auto
  done

theorem cdcl_twl_stgy_prog_wl_spec_final2:
  shows
    \<open>(SAT_wl, SAT) \<in> [\<lambda>CS. (\<forall>C \<in># CS. distinct_mset C) \<and> (\<forall>C \<in># CS. size C \<ge> 1) \<and>
        (\<forall>C \<in># CS. \<not>tautology C)]\<^sub>f
     (list_mset_rel O \<langle>list_mset_rel\<rangle> mset_rel) \<rightarrow> \<langle>f_conv\<rangle>nres_rel\<close>
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
    unfolding SAT_wl_def SAT_def init_state_wl_def
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
      obtain M N D NP Q W where
        S\<^sub>0: \<open>S\<^sub>0 = (M, N, length N - 1, Some D, NP, {#}, Q, W)\<close>
        using p False by (cases S\<^sub>0) (auto simp: clauses_def mset_take_mset_drop_mset' get_unit_learned_def)
      have N_NP: \<open>mset `# mset (tl N) + NP = mset `# mset CS'\<close>
        using p by (auto simp: clauses_def mset_take_mset_drop_mset' S\<^sub>0)
      have 1: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ([], CS, {#}, None)
         (convert_to_state (twl_st_of None (st_l_of_wl None S\<^sub>0)))\<close>
        apply (simp add: mset_take_mset_drop_mset' S\<^sub>0 N_NP CS)
          -- \<open>induction on the (growing) trail + conflict\<close>
        sorry
      have 2: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (convert_to_state (twl_st_of None (st_l_of_wl None S\<^sub>0)))
        ([], CS, {#}, Some {#})\<close>
          -- \<open>induction on the (shrinking) trail\<close>
        sorry


      have 3: \<open>no_step cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy ([], CS, {#}, Some {#})\<close>
        by (auto simp: cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_restart_mset_state
            cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_o.simps cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_bj.simps
            elim!: cdcl\<^sub>W_restart_mset.rulesE)
      show ?thesis
        unfolding confl if_False
        apply (rule RETURN_SPEC_refine)
        apply (rule exI[of _ \<open>([]::(nat, nat clause) ann_lits, CS, {#}::nat clauses, Some {#}::nat clause option)\<close>])
        apply (intro conjI)
        subgoal using p confl by (cases S\<^sub>0, clarsimp_all simp: f_conv_def trivial_skip_and_resolve_def mset_take_mset_drop_mset'
            clauses_def get_unit_learned_def in_list_mset_rel in_list_mset_rel_mset_rel)
        subgoal
          using rtranclp_trans[OF 1 2] 3 by (auto simp: init_state_def full_def)
        done
    next
      case True
      then show ?thesis sorry
    next
    qed
    oops
end