theory IsaSAT_Watch_List
  imports IsaSAT_Literals IsaSAT_Clauses Watched_Literals.Watched_Literals_Watch_List_Initialisation
begin

chapter \<open>Refinement of the Watched Function\<close>

text \<open>There is not much to say about watch lists since they are arrays of resizeable arrays,
  which are defined in a separate theory.

  However, when replacing the elements in our watch lists from \<open>(nat \<times> uint32)\<close>
  to \<open>(nat \<times> uint32 \<times> bool)\<close> to enable special handling of binary clauses, we got a huge and
  unexpected slowdown, due to a much higher
  number of cache misses (roughly 3.5 times as many on a eq.atree.braun.8.unsat.cnf which also took
  66s instead of 50s). While toying with the generated ML code, we found out that our version of
  the tuples with booleans were using 40 bytes instead of 24 previously. Just merging the
  \<open>uint32\<close> and the \<^typ>\<open>bool\<close> to a single \<open>uint64\<close> was sufficient to get the
  performance back.

  Remark that however, the evaluation of terms like \<open>(2::uint64) ^ 32\<close> was not done automatically
  and even worse, was redone each time, leading to a complete performance blow-up (75s on my macbook
  for eq.atree.braun.7.unsat.cnf instead of 7s).

  None of the problems appears in the LLVM code.
\<close>

section \<open>Definition\<close>

definition map_fun_rel :: \<open>(nat \<times> 'key) set \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> ('b list \<times> ('key \<Rightarrow> 'a)) set\<close> where
  map_fun_rel_def_internal:
    \<open>map_fun_rel D R = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>

lemma map_fun_rel_def:
  \<open>\<langle>R\<rangle>map_fun_rel D = {(m, f). \<forall>(i, j)\<in>D. i < length m \<and> (m ! i, f j) \<in> R}\<close>
  unfolding relAPP_def map_fun_rel_def_internal by auto

definition mop_append_ll :: \<open>'a list list \<Rightarrow> nat literal \<Rightarrow> 'a \<Rightarrow> 'a list list nres\<close> where
  \<open>mop_append_ll xs i x = do {
     ASSERT(nat_of_lit i < length xs);
     RETURN (append_ll xs (nat_of_lit i) x)
  }\<close>

section \<open>Operations\<close>
lemma length_ll_length_ll_f:
  \<open>(uncurry (RETURN oo length_ll), uncurry (RETURN oo length_ll_f)) \<in>
     [\<lambda>(W, L). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<^sub>i\<^sub>n]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>\<^sub>i\<^sub>n)) \<times>\<^sub>r nat_lit_rel) \<rightarrow>
       \<langle>nat_rel\<rangle> nres_rel\<close>
  unfolding length_ll_def length_ll_f_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def br_def
      nat_lit_rel_def)

lemma mop_append_ll:
   \<open>(uncurry2 mop_append_ll, uncurry2 (RETURN ooo (\<lambda>W i x. W(i := W i @ [x])))) \<in>
    [\<lambda>((W, i), x). i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  unfolding uncurry_def mop_append_ll_def
  by (intro frefI nres_relI)
    (auto intro!: ASSERT_leI simp: map_fun_rel_def append_ll_def)


definition delete_index_and_swap_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>delete_index_and_swap_update W K w = W(K := delete_index_and_swap (W K) w)\<close>

text \<open>The precondition is not necessary.\<close>
lemma delete_index_and_swap_ll_delete_index_and_swap_update:
  \<open>(uncurry2 (RETURN ooo delete_index_and_swap_ll), uncurry2 (RETURN ooo delete_index_and_swap_update))
  \<in>[\<lambda>((W, L), i). L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f (\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
      \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  by (auto simp: delete_index_and_swap_ll_def uncurry_def fref_def nres_rel_def
      delete_index_and_swap_update_def map_fun_rel_def p2rel_def nat_lit_rel_def br_def
      nth_list_update' nat_lit_rel_def
      simp del: literal_of_nat.simps)

definition append_update :: \<open>('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b list\<close> where
  \<open>append_update W L a = W(L:= W (L) @ [a])\<close>

type_synonym nat_clauses_l = \<open>nat list list\<close>

subsubsection \<open>Refinement of the Watched Function\<close>

definition watched_by_nth :: \<open>nat twl_st_wl \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_by_nth = (\<lambda>(M, N, D, NE, UE, NEk, UEk, NS, US, N0, U0, Q, W) L i. W L ! i)\<close>

definition watched_app
  :: \<open>(nat literal \<Rightarrow> (nat watcher) list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_app M L i \<equiv> M L ! i\<close>

lemma watched_by_nth_watched_app:
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd o snd o snd o snd o snd o snd o snd) S) K w\<close>
  by (cases S) (auto simp: watched_app_def)


lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_rll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)) \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_rll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def br_def
      nat_lit_rel_def)




section \<open>Rewatch\<close>

definition rewatch_heur where
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      ASSERT(i < length vdom);
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        L1 \<leftarrow> mop_arena_lit2 arena C 0;
        L2 \<leftarrow> mop_arena_lit2 arena C 1;
        n \<leftarrow> mop_arena_length arena C;
        let b = (n = 2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        W \<leftarrow> mop_append_ll W L1 (C, L2, b);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
        W \<leftarrow> mop_append_ll W L2 (C, L1, b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>

lemma rewatch_heur_rewatch:
  assumes
    valid: \<open>valid_arena arena N vdom\<close> and \<open>set xs \<subseteq> vdom\<close> and \<open>distinct xs\<close> and \<open>set_mset (dom_m N) \<subseteq> set xs\<close> and
    \<open>(W, W') \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<close> and lall: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm \<A> (mset `# ran_mf N)\<close> and
    \<open>vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)\<close>
  shows
    \<open>rewatch_heur xs arena W \<le> \<Down> ({(W, W'). (W, W') \<in>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<and> vdom_m \<A> W' N \<subseteq> set_mset (dom_m N)}) (rewatch N W')\<close>
proof -
  have [refine0]: \<open>(xs, xsa) \<in> Id \<Longrightarrow>
     ([0..<length xs], [0..<length xsa]) \<in> \<langle>{(x, x'). x = x' \<and> x < length xsa \<and> xs!x \<in> vdom}\<rangle>list_rel\<close>
    for xsa
    using assms unfolding list_rel_def
    by (auto simp: list_all2_same)
  show ?thesis
    unfolding rewatch_heur_def rewatch_def
    apply (subst (2) nfoldli_nfoldli_list_nth)
    apply (refine_vcg mop_arena_lit[OF valid] mop_append_ll[of \<A>, THEN fref_to_Down_curry2, unfolded comp_def]
       mop_arena_length[of vdom, THEN fref_to_Down_curry, unfolded comp_def])
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal
      using assms by fast
    subgoal by fast
    subgoal by auto
    subgoal
      using assms
      unfolding arena_is_valid_clause_vdom_def
      by blast
    subgoal
      using assms
      by (auto simp: arena_dom_status_iff)
    subgoal for xsa xi x si s
      using assms
      by auto
    subgoal by simp
    subgoal by linarith
    subgoal for xsa xi x si s
      using assms
      unfolding arena_lit_pre_def
      by (auto)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal for xsa xi x si s
      using assms
      unfolding arena_is_valid_clause_idx_and_access_def
        arena_is_valid_clause_idx_def
      by (auto simp: arena_is_valid_clause_idx_and_access_def
          intro!: exI[of _ N] exI[of _ vdom])
    subgoal for xsa xi x si s
      using valid_arena_size_dom_m_le_arena[OF assms(1)] assms
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 0]
      by (auto simp: map_fun_rel_def arena_lifting)
    subgoal for xsa xi x si s
      using valid_arena_size_dom_m_le_arena[OF assms(1)] assms
         literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 0]
      by (auto simp: map_fun_rel_def arena_lifting)
    subgoal using assms by (simp add: arena_lifting)
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1]
      assms valid_arena_size_dom_m_le_arena[OF assms(1)]
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[OF lall, of  \<open>xs ! xi\<close> 1]
        assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    subgoal for xsa xi x si s
      using assms
      by (auto simp: arena_lifting append_ll_def map_fun_rel_def)
    done
qed

lemma rewatch_heur_alt_def:
\<open>rewatch_heur vdom arena W = do {
  let _ = vdom;
  nfoldli [0..<length vdom] (\<lambda>_. True)
   (\<lambda>i W. do {
      ASSERT(i < length vdom);
      let C = vdom ! i;
      ASSERT(arena_is_valid_clause_vdom arena C);
      if arena_status arena C \<noteq> DELETED
      then do {
        L1 \<leftarrow> mop_arena_lit2 arena C 0;
        L2 \<leftarrow> mop_arena_lit2 arena C 1;
        n \<leftarrow> mop_arena_length arena C;
        let b = (n = 2);
        ASSERT(length (W ! (nat_of_lit L1)) < length arena);
        W \<leftarrow> mop_append_ll W L1 (C, L2, b);
        ASSERT(length (W ! (nat_of_lit L2)) < length arena);
        W \<leftarrow> mop_append_ll W L2 (C, L1, b);
        RETURN W
      }
      else RETURN W
    })
   W
  }\<close>
  unfolding Let_def rewatch_heur_def
  by auto

end