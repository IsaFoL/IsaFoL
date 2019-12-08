theory IsaSAT_Watch_List
  imports IsaSAT_Literals
begin

text \<open>There is not much to say about watch lists since they are arrays of resizeable arrays,
  which are defined in a separate theory.

  However, when replacing the elements in our watch lists from \<open>(nat \<times> uint32)\<close>
  to \<open>(nat \<times> uint32 \<times> bool)\<close>, we got a huge and unexpected slowdown, due to a much higher
  number of cache misses (roughly 3.5 times as many on a eq.atree.braun.8.unsat.cnf which also took
  66s instead of 50s). While toying with the generated ML code, we found out that our version of
  the tuples with booleans were using 40 bytes instead of 24 previously. Just merging the
  \<open>uint32\<close> and the \<^typ>\<open>bool\<close> to a single \<open>uint64\<close> was sufficient to get the
  performance back.

  Remark that however, the evaluation of terms like \<open>(2::uint64) ^ 32\<close> was not done automatically
  and even worse, was redone each time, leading to a complete performance blow-up (75s on my macbook
  for eq.atree.braun.7.unsat.cnf instead of 7s).
\<close>

definition mop_append_ll :: "'a list list \<Rightarrow> nat literal \<Rightarrow> 'a \<Rightarrow> 'a list list nres" where
  \<open>mop_append_ll xs i x = do {
     ASSERT(nat_of_lit i < length xs);
     RETURN (append_ll xs (nat_of_lit i) x)
  }\<close>

lemma mop_append_ll:
   \<open>(uncurry2 mop_append_ll, uncurry2 (RETURN ooo (\<lambda>W i x. W(i := W i @ [x])))) \<in>
    [\<lambda>((W, i), x). i \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>]\<^sub>f \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>) \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>\<langle>Id\<rangle>map_fun_rel (D\<^sub>0 \<A>)\<rangle>nres_rel\<close>
  unfolding uncurry_def mop_append_ll_def
  by (intro frefI nres_relI)
    (auto intro!: ASSERT_leI simp: map_fun_rel_def append_ll_def)

end