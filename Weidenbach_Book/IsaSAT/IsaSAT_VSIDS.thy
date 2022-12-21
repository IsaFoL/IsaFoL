theory IsaSAT_VSIDS
  imports Watched_Literals.WB_Sort IsaSAT_Setup Ordered_Pairing_Heap_List2
  (*  IsaSAT_Literals_LLVM
    IsaSAT_Literals_LLVM
    Isabelle_LLVM.IICF
    Isabelle_LLVM.LLVM_DS_Open_List
    Isabelle_LLVM.LLVM_DS_Array_List_Pure*)
    Weidenbach_Book_Base.Explorer
    Pairing_Heaps
begin

definition mop_get_min where
  \<open>mop_get_min xs = do {
    ASSERT (xs \<noteq> None);
    RETURN (get_min2 xs)
  }\<close>

definition mop_pop_min where
  \<open>mop_pop_min xs = do {
    ASSERT (xs \<noteq> None);
    a \<leftarrow> mop_get_min xs;
    RETURN (a, VSIDS.del_min xs)
  }\<close>

definition mop_push where
  \<open>mop_push a w xs = do {
    ASSERT (xs \<noteq> None \<and> a \<notin># mset_nodes (the xs));
    RETURN (VSIDS.insert a w xs)
  }\<close>

definition mop_rescore where
  \<open>mop_rescore x w xs = do {
    ASSERT (xs \<noteq> None);
    let a = VSIDS.find_key x (the xs);
    let b = VSIDS.remove_key x (the xs);
    if a = None
    then RETURN b
    else do {
      let a = the a;
      ASSERT (score a < w);
      let a = Hp (node a) w (hps a);
      RETURN (VSIDS.merge (Some a) b)
    }
  }\<close>

text \<open>This is a bit stricter than required, but...\<close>
definition pairing_heap_rel where
  \<open>pairing_heap_rel xs \<longleftrightarrow> VSIDS.invar xs \<and> (xs \<noteq> None \<longrightarrow> distinct_mset (mset_nodes (the xs)))\<close>

lemma mset_nodes_link[simp]: \<open>mset_nodes (VSIDS.link a b) = mset_nodes a + mset_nodes b\<close>
  by (cases a; cases b)
   auto

lemma mop_push_rule:
  assumes \<open>pairing_heap_rel xs\<close> \<open>xs \<noteq> None\<close> \<open>a \<notin># mset_nodes (the xs)\<close>
  shows \<open>mop_push a w xs \<le> SPEC (\<lambda>xs'. xs' = VSIDS.insert a w xs \<and> pairing_heap_rel xs')\<close>
  using assms unfolding mop_push_def
  apply (refine_vcg)
  subgoal by auto
  subgoal by (auto simp: pairing_heap_rel_def intro!: VSIDS.invar_insert)
  done

end
