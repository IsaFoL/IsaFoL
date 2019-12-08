theory IsaSAT_Watch_List
  imports IsaSAT_Literals
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

definition mop_append_ll :: "'a list list \<Rightarrow> nat literal \<Rightarrow> 'a \<Rightarrow> 'a list list nres" where
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
  \<open>watched_by_nth = (\<lambda>(M, N, D, NE, UE, NS, US, Q, W) L i. W L ! i)\<close>

definition watched_app
  :: \<open>(nat literal \<Rightarrow> (nat watcher) list) \<Rightarrow> nat literal \<Rightarrow> nat \<Rightarrow> nat watcher\<close> where
  \<open>watched_app M L i \<equiv> M L ! i\<close>

lemma watched_by_nth_watched_app:
  \<open>watched_by S K ! w = watched_app ((snd o snd o snd o snd o snd o snd o snd o snd) S) K w\<close>
  by (cases S) (auto simp: watched_app_def)


lemma nth_ll_watched_app:
  \<open>(uncurry2 (RETURN ooo nth_rll), uncurry2 (RETURN ooo watched_app)) \<in>
     [\<lambda>((W, L), i). L \<in># (\<L>\<^sub>a\<^sub>l\<^sub>l \<A>)]\<^sub>f ((\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)) \<times>\<^sub>r nat_lit_rel) \<times>\<^sub>r nat_rel \<rightarrow>
       \<langle>nat_rel \<times>\<^sub>r Id\<rangle> nres_rel\<close>
  unfolding watched_app_def nth_rll_def
  by (fastforce simp: fref_def map_fun_rel_def prod_rel_def nres_rel_def p2rel_def br_def
      nat_lit_rel_def)


end