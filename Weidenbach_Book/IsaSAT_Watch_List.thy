theory IsaSAT_Watch_List
  imports IsaSAT_Literals
    Watched_Literals.WB_Word
begin

text \<open>There is not much to say about watch lists since they are arrays of resizeable arrays,
  which are defined in a separate theory.

  However, when replacing the elements in our watch lists from \<^typ>\<open>(nat \<times> uint32)\<close>
  to \<^typ>\<open>(nat \<times> uint32 \<times> bool)\<close>, we got a huge and unexpected slowdown, due to a much higher
  number of cache misses (roughly 3.5 times as many on a eq.atree.braun.8.unsat.cnf which also took
  66s instead of 50s). While toying with the generated ML code, we found out that our version of
  the tuples with booleans were using 40 bytes instead of 24 previously. Just merging the
  \<^typ>\<open>uint32\<close> and the \<^typ>\<open>bool\<close> to a single \<^typ>\<open>uint64\<close> was sufficient to get the
  performance back.

  Remark that however, the evaluation of terms like \<^term>\<open>(2::uint64) ^ 32\<close> was not done automatically
  and even worse, was redone each time, leading to a complete performance blow-up (75s on my macbook
  for eq.atree.braun.7.unsat.cnf instead of 7s).
\<close>

end