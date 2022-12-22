theory Pairing_Heaps
  imports Ordered_Pairing_Heap_List2
    Isabelle_LLVM.IICF
    More_Sepref.WB_More_Refinement
    Watched_Literals_VMTF
    Heaps_Abs
begin

section \<open>Genealogy Over Pairing Heaps\<close>

text \<open>We first tried to use the heapmap, but this attempt was a terrible failure, because as useful
the heapmap is parametrized by the size. This might be useful in some contexts, but I consider this
to be the most terrible idea ever, based on past experience. So instead I went for a modification
of the pairing heaps.

To increase fun, we reuse the trick from VSIDS to represent the pairing heap inside an array in
order to avoid allocation yet another array. As a side effect, it also avoids including the label
inside the node (because per definition, the label is exactly the index).
But maybe pointers are actually better, because by definition in Isabelle no graph is shared.
\<close>

fun mset_nodes :: "('b, 'a) hp \<Rightarrow>'b multiset" where
"mset_nodes (Hp x _ hs) = {#x#} + \<Sum>\<^sub># (mset_nodes `# mset hs)"

context pairing_heap_assms
begin

lemma mset_nodes_link[simp]: \<open>mset_nodes (link a b) = mset_nodes a + mset_nodes b\<close>
  by (cases a; cases b)
   auto

lemma mset_nodes_merge_pairs: \<open>merge_pairs a \<noteq> None \<Longrightarrow> mset_nodes (the (merge_pairs a)) = sum_list (map mset_nodes a)\<close>
  apply (induction a rule: merge_pairs.induct)
  subgoal by auto
  subgoal by auto
  subgoal for h1 h2 hs
    by (cases hs)
     (auto simp: Let_def split: option.splits)
  done

lemma mset_nodes_pass\<^sub>1[simp]: \<open>sum_list (map mset_nodes (pass\<^sub>1 a)) = sum_list (map mset_nodes a)\<close>
  apply (induction a rule: pass\<^sub>1.induct)
  subgoal by auto
  subgoal by auto
  subgoal for h1 h2 hs
    by (cases hs)
     (auto simp: Let_def split: option.splits)
  done


lemma mset_nodes_pass\<^sub>2[simp]: \<open>pass\<^sub>2 a \<noteq> None \<Longrightarrow> mset_nodes (the (pass\<^sub>2 a)) = sum_list (map mset_nodes a)\<close>
  apply (induction a rule: pass\<^sub>1.induct)
  subgoal by auto
  subgoal by auto
  subgoal for h1 h2 hs
    by (cases hs)
     (auto simp: Let_def split: option.splits)
  done

end

lemma mset_nodes_simps[simp]: \<open>mset_nodes (Hp x n hs) = {#x#} + (sum_list (map mset_nodes hs))\<close>
  by auto

lemmas [simp del] = mset_nodes.simps

fun hp_next where
  \<open>hp_next a (Hp m s (x # y # children)) = (if a = node x then Some y else (case hp_next a x of Some a \<Rightarrow> Some a | None \<Rightarrow> hp_next a (Hp m s (y # children))))\<close> |
  \<open>hp_next a (Hp m s [b]) = hp_next a b\<close> |
  \<open>hp_next a (Hp m s []) = None\<close>

lemma [simp]: \<open>size_list size (hps x) < Suc (size x + a)\<close>
  by (cases x) auto

fun hp_prev where
  \<open>hp_prev a (Hp m s (x # y # children)) = (if a = node y then Some x else (case hp_prev a x of Some a \<Rightarrow> Some a | None \<Rightarrow> hp_prev a (Hp m s (y # children))))\<close> |
  \<open>hp_prev a (Hp m s [b]) = hp_prev a b\<close> |
  \<open>hp_prev a (Hp m s []) = None\<close>

fun hp_child where
  \<open>hp_child a (Hp m s (x # children)) = (if a = m then Some x else (case hp_child a x of None \<Rightarrow> hp_child a (Hp m s children) | Some a \<Rightarrow> Some a))\<close> |
  \<open>hp_child a (Hp m s _) = None\<close>

fun hp_node where
  \<open>hp_node a (Hp m s (x#children)) = (if a = m then Some (Hp m s (x#children)) else (case hp_node a x of None \<Rightarrow> hp_node a (Hp m s children) | Some a \<Rightarrow> Some a))\<close> |
  \<open>hp_node a (Hp m s []) = (if a = m then Some (Hp m s []) else None)\<close>

lemma node_in_mset_nodes[simp]: \<open>node x \<in># mset_nodes x\<close>
  by (cases x; auto)

lemma hp_next_None_notin[simp]: \<open>m \<notin># mset_nodes a \<Longrightarrow> hp_next m a = None\<close>
  by (induction m a rule: hp_next.induct) auto

lemma hp_prev_None_notin[simp]: \<open>m \<notin># mset_nodes a \<Longrightarrow> hp_prev m a = None\<close>
  by (induction m a rule: hp_prev.induct) auto

lemma hp_child_None_notin[simp]: \<open>m \<notin># mset_nodes a \<Longrightarrow> hp_child m a = None\<close>
  by (induction m a rule: hp_child.induct) auto

lemma hp_node_None_notin2[iff]: \<open>hp_node m a = None \<longleftrightarrow> m \<notin># mset_nodes a\<close>
  by (induction m a rule: hp_node.induct) auto

lemma hp_node_None_notin[simp]: \<open>m \<notin># mset_nodes a \<Longrightarrow> hp_node m a = None\<close>
  by auto

lemma hp_node_simps[simp]: \<open>hp_node m (Hp m w\<^sub>m ch\<^sub>m) = Some (Hp m w\<^sub>m ch\<^sub>m)\<close>
  by (cases ch\<^sub>m) auto

lemma hp_next_None_notin_children[simp]: \<open>a \<notin># sum_list (map mset_nodes children) \<Longrightarrow>
  hp_next a (Hp m w\<^sub>m (children)) = None\<close>
  by (induction a \<open>Hp m w\<^sub>m children\<close> arbitrary:children rule: hp_next.induct) auto

lemma hp_prev_None_notin_children[simp]: \<open>a \<notin># sum_list (map mset_nodes children) \<Longrightarrow>
  hp_prev a (Hp m w\<^sub>m (children)) = None\<close>
  by (induction a \<open>Hp m w\<^sub>m children\<close> arbitrary:children rule: hp_prev.induct) auto

lemma hp_child_None_notin_children[simp]: \<open>a \<notin># sum_list (map mset_nodes children) \<Longrightarrow> a \<noteq> m \<Longrightarrow>
  hp_child a (Hp m w\<^sub>m (children)) = None\<close>
  by (induction a \<open>Hp m w\<^sub>m children\<close> arbitrary:children rule: hp_next.induct) auto

text \<open>The function above are nicer for definition than for usage. Instead we define the list version
and change the simplification lemmas. We initially tried to use a recursive function, but the
proofs did not go through (and it seemed that the induction principle were to weak).\<close>
fun hp_next_children where
  \<open>hp_next_children a (x # y # children) = (if a = node x then Some y else (case hp_next a x of Some a \<Rightarrow> Some a | None \<Rightarrow> hp_next_children a (y # children)))\<close> |
  \<open>hp_next_children a [b] = hp_next a b\<close> |
  \<open>hp_next_children a [] = None\<close>

lemma hp_next_simps[simp]:
  \<open>hp_next a (Hp m s children) = hp_next_children a children\<close>
  by (induction a children rule: hp_next_children.induct) (auto split: option.splits)

lemma hp_next_children_None_notin[simp]: \<open>m \<notin># \<Sum>\<^sub># (mset_nodes `# mset children) \<Longrightarrow> hp_next_children m children = None\<close>
  by (induction m children rule: hp_next_children.induct) auto

lemma [simp]: \<open>distinct_mset (mset_nodes a) \<Longrightarrow> hp_next (node a) a = None\<close>
  by (induction a) auto

lemma [simp]:
  \<open>ch\<^sub>m \<noteq> [] \<Longrightarrow> hp_next_children (node a) (a # ch\<^sub>m) = Some (hd ch\<^sub>m)\<close>
  by (cases ch\<^sub>m) auto

fun hp_prev_children where
  \<open>hp_prev_children a (x # y # children) = (if a = node y then Some x else (case hp_prev a x of Some a \<Rightarrow> Some a | None \<Rightarrow> hp_prev_children a (y # children)))\<close> |
  \<open>hp_prev_children a [b] = hp_prev a b\<close> |
  \<open>hp_prev_children a [] = None\<close>

lemma hp_prev_simps[simp]:
  \<open>hp_prev a (Hp m s children) = hp_prev_children a children\<close>
  by (induction a children rule: hp_prev_children.induct) (auto split: option.splits)

lemma hp_prev_children_None_notin[simp]: \<open>m \<notin># \<Sum>\<^sub># (mset_nodes `# mset children) \<Longrightarrow> hp_prev_children m children = None\<close>
  by (induction m children rule: hp_prev_children.induct) auto

lemma [simp]: \<open>distinct_mset (mset_nodes a) \<Longrightarrow> hp_prev (node a) a = None\<close>
  by (induction a) auto

lemma hp_next_in_first_child [simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a)) \<Longrightarrow>
  xa \<in># mset_nodes a \<Longrightarrow> xa \<noteq> node a \<Longrightarrow>
  hp_next_children xa (a # ch\<^sub>m) = (hp_next xa a)\<close>
  by (cases ch\<^sub>m) (auto split: option.splits dest!: multi_member_split)

lemma hp_next_skip_hd_children:
  \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a)) \<Longrightarrow> xa \<in># \<Sum>\<^sub># (mset_nodes `# mset ch\<^sub>m) \<Longrightarrow>
  xa \<noteq> node a \<Longrightarrow> hp_next_children xa (a # ch\<^sub>m) = hp_next_children xa (ch\<^sub>m)\<close>
  apply (cases ch\<^sub>m)
  apply (auto split: option.splits dest!: multi_member_split)
  done

lemma hp_prev_in_first_child [simp]: \<open>distinct_mset
  (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a)) \<Longrightarrow> xa \<in># mset_nodes a \<Longrightarrow> hp_prev_children xa (a # ch\<^sub>m) = hp_prev xa a\<close>
  by (cases ch\<^sub>m) (auto split: option.splits dest!: multi_member_split)

lemma hp_prev_skip_hd_children:
  \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a)) \<Longrightarrow> xa \<in># \<Sum>\<^sub># (mset_nodes `# mset ch\<^sub>m) \<Longrightarrow>
  xa \<noteq> node (hd ch\<^sub>m) \<Longrightarrow> hp_prev_children xa (a # ch\<^sub>m) = hp_prev_children xa ch\<^sub>m\<close>
  apply (cases ch\<^sub>m)
  apply (auto split: option.splits dest!: multi_member_split)
  done

lemma node_hd_in_sum[simp]: \<open>ch\<^sub>m \<noteq> [] \<Longrightarrow> node (hd ch\<^sub>m) \<in># sum_list (map mset_nodes ch\<^sub>m)\<close>
  by (cases ch\<^sub>m) auto

lemma hp_prev_cadr_node[simp]: \<open>ch\<^sub>m \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd ch\<^sub>m)) (a # ch\<^sub>m) = Some a\<close>
  by (cases ch\<^sub>m) auto

lemma hp_next_children_simps[simp]:
   \<open>a = node x \<Longrightarrow> hp_next_children a (x # y # children) = Some y\<close>
   \<open>a \<noteq> node x \<Longrightarrow> hp_next a x \<noteq> None \<Longrightarrow> hp_next_children a (x # children) = hp_next a x\<close>
   \<open>a \<noteq> node x \<Longrightarrow> hp_next a x = None \<Longrightarrow> hp_next_children a (x # children) = hp_next_children a (children)\<close>
  apply (solves auto)
  apply (solves \<open>cases children; auto\<close>)+
  done

lemma hp_prev_children_simps[simp]:
   \<open>a = node y \<Longrightarrow> hp_prev_children a (x # y # children) = Some x\<close>
   \<open>a \<noteq> node y \<Longrightarrow> hp_prev a x \<noteq> None \<Longrightarrow> hp_prev_children a (x # y # children) = hp_prev a x\<close>
   \<open>a \<noteq> node y \<Longrightarrow> hp_prev a x = None \<Longrightarrow> hp_prev_children a (x # y # children) = hp_prev_children a (y # children)\<close>
  by auto

lemmas [simp del] =  hp_next_children.simps(1) hp_next.simps(1) hp_prev.simps(1) hp_prev_children.simps(1)

lemma hp_next_children_skip_first_append[simp]:
  \<open>xa \<notin># \<Sum>\<^sub># (mset_nodes `# mset ch) \<Longrightarrow> hp_next_children xa (ch @ ch') = hp_next_children xa ch'\<close>
  apply (induction xa ch rule: hp_next_children.induct)
  subgoal
    by (auto simp: hp_next_children.simps(1))
  subgoal
    by (cases ch')
      (auto simp: hp_next_children.simps(1))
  subgoal by auto
  done

lemma hp_prev_children_skip_first_append[simp]:
  \<open>xa \<notin># \<Sum>\<^sub># (mset_nodes `# mset ch) \<Longrightarrow> xa \<noteq> node m \<Longrightarrow> hp_prev_children xa (ch @ m # ch') = hp_prev_children xa (m#ch')\<close>
  apply (induction xa ch rule: hp_prev_children.induct)
  subgoal
    by (auto simp: hp_prev_children.simps(1))
  subgoal
    by (auto simp: hp_prev_children.simps(1))
  subgoal by auto
  done

lemma hp_prev_children_skip_Cons[simp]:
  \<open>xa \<notin># \<Sum>\<^sub># (mset_nodes `# mset ch') \<Longrightarrow> xa \<in># mset_nodes m \<Longrightarrow> hp_prev_children xa (m # ch') = hp_prev xa m\<close>
  apply (induction ch')
  subgoal
    by (auto simp: hp_prev_children.simps(1) split: option.splits)
  subgoal
    by (auto simp: hp_prev_children.simps(1) split: option.splits)
  done

definition hp_child_children where
  \<open>hp_child_children a = option_hd o (List.map_filter (hp_child a))\<close>

lemma hp_child_children_Cons_if:
  \<open>hp_child_children a (x # y) = (if hp_child a x = None then hp_child_children a y else hp_child a x)\<close>
  by (auto simp: hp_child_children_def List.map_filter_def split: list.splits)

lemma hp_child_children_simps[simp]:
  \<open>hp_child_children a [] = None\<close>
  \<open>hp_child a x =None \<Longrightarrow> hp_child_children a (x # y) = hp_child_children a y\<close>
  \<open>hp_child a x \<noteq> None \<Longrightarrow> hp_child_children a (x # y) = hp_child a x\<close>
  by (auto simp: hp_child_children_def List.map_filter_def split: list.splits)

lemma hp_child_hp_children_simps2[simp]:
  \<open>x \<noteq> a \<Longrightarrow> hp_child x (Hp a b child) = hp_child_children x child\<close>
  by (induction child) (auto split: option.splits)

lemma hp_child_children_None_notin[simp]: \<open>m \<notin># \<Sum>\<^sub># (mset_nodes `# mset children) \<Longrightarrow> hp_child_children m children = None\<close>
  by (induction children) auto

definition hp_node_children where
  \<open>hp_node_children a = option_hd o (List.map_filter (hp_node a))\<close>

lemma hp_node_children_Cons_if:
  \<open>hp_node_children a (x # y) = (if hp_node a x = None then hp_node_children a y else hp_node a x)\<close>
  by (auto simp: hp_node_children_def List.map_filter_def split: list.splits)

lemma hp_node_children_simps[simp]:
  \<open>hp_node_children a [] = None\<close>
  \<open>hp_node a x =None \<Longrightarrow> hp_node_children a (x # y) = hp_node_children a y\<close>
  \<open>hp_node a x \<noteq> None \<Longrightarrow> hp_node_children a (x # y) = hp_node a x\<close>
  by (auto simp: hp_node_children_def List.map_filter_def split: list.splits)

lemma hp_node_children_simps2[simp]:
  \<open>x \<noteq> a \<Longrightarrow> hp_node x (Hp a b child) = hp_node_children x child\<close>
  by (induction child) (auto split: option.splits)

lemma hp_node_children_None_notin2: \<open>hp_node_children m children = None \<longleftrightarrow> m \<notin># \<Sum>\<^sub># (mset_nodes `# mset children)\<close>
  apply (induction children)
  apply auto
  by (metis hp_node_children_simps(2) hp_node_children_simps(3) option_last_Nil option_last_Some_iff(2))

lemma hp_node_children_None_notin[simp]: \<open>m \<notin># \<Sum>\<^sub># (mset_nodes `# mset children) \<Longrightarrow> hp_node_children m children = None\<close>
  by (induction children) auto


lemma hp_next_children_hd_simps[simp]:
  \<open>a = node x \<Longrightarrow> distinct_mset (sum_list (map mset_nodes (x # children))) \<Longrightarrow>
  hp_next_children a (x # children) = option_hd children\<close>
  by (cases children) auto

lemma hp_next_children_simps_if:
  \<open> distinct_mset (sum_list (map mset_nodes (x # children))) \<Longrightarrow>
  hp_next_children a (x # children) = (if a = node x then option_hd children else case hp_next a x of None \<Rightarrow> hp_next_children a children | a \<Rightarrow> a)\<close>
  by (cases children) (auto split: if_splits option.splits)


lemma hp_next_children_skip_end[simp]:
  \<open>n \<in># mset_nodes a \<Longrightarrow> n \<noteq> node a \<Longrightarrow> n \<notin># sum_list (map mset_nodes b) \<Longrightarrow> 
  distinct_mset (mset_nodes a) \<Longrightarrow>
  hp_next_children n (a # b) = hp_next n a\<close>
  by (induction b) (auto simp add: hp_next_children.simps(1) split: option.splits)

lemma hp_next_children_append2[simp]:
  \<open>x \<noteq> n \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> hp_next_children x (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m) = hp_next_children x ch\<^sub>n\<close>
  by (cases ch\<^sub>m) (auto simp: hp_next_children.simps(1) split: option.splits)

lemma hp_next_children_skip_Cons_append[simp]:
  \<open>NO_MATCH [] b \<Longrightarrow> x \<in># sum_list (map mset_nodes a) \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes (a @ m # b))) \<Longrightarrow>
  hp_next_children x (a @ m # b) = hp_next_children x (a @ m # [])\<close>
  apply (induction x a rule: hp_next_children.induct)
  apply (auto simp: hp_next_children.simps(1) distinct_mset_add split: option.splits)
  apply (metis (no_types, lifting) add_mset_disjoint(1) hp_next_children.simps(2)
    hp_next_children_None_notin hp_next_children_simps(2) hp_next_children_simps(3)
    hp_next_children_skip_first_append mset_add node_in_mset_nodes sum_image_mset_sum_map union_iff)
  by (metis add_mset_disjoint(1) hp_next_None_notin hp_next_children_None_notin
    hp_next_children_simps(3) insert_DiffM node_in_mset_nodes sum_image_mset_sum_map union_iff)

lemma hp_next_children_append_single_remove_children:
  \<open>NO_MATCH [] ch\<^sub>m \<Longrightarrow> x \<in># sum_list (map mset_nodes a) \<Longrightarrow>
     distinct_mset (sum_list (map mset_nodes (a @ [Hp m w\<^sub>m ch\<^sub>m]))) \<Longrightarrow>
     map_option node (hp_next_children x (a @ [Hp m w\<^sub>m ch\<^sub>m])) =
     map_option node (hp_next_children x (a @ [Hp m w\<^sub>m []]))\<close>
  apply (induction x a rule: hp_next_children.induct)
  apply (auto simp: hp_next_children.simps(1) distinct_mset_add split: option.splits)
  apply (smt (verit, ccfv_threshold) distinct_mset_add hp_next_None_notin hp_next_children.simps(2)
    hp_next_children_simps(3) hp_next_children_skip_first_append hp_next_in_first_child hp_next_simps
    node_in_mset_nodes sum_image_mset_sum_map union_assoc union_commute)
  apply (simp add: disjunct_not_in)
  done

lemma hp_prev_children_first_child[simp]:
  \<open>m \<noteq> n \<Longrightarrow> n \<notin># sum_list (map mset_nodes b) \<Longrightarrow>  n \<notin># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow>
   n \<in># sum_list (map mset_nodes child) \<Longrightarrow>
  hp_prev_children n (Hp m w\<^sub>m child # b) = hp_prev_children n child\<close>
  by (cases b) (auto simp: hp_prev_children.simps(1) split: option.splits)

lemma hp_prev_children_skip_last_append[simp]:
  \<open>NO_MATCH [] ch' ⟹
     distinct_mset (sum_list (map mset_nodes (ch @ch'))) \<Longrightarrow>
  xa \<notin># \<Sum>\<^sub># (mset_nodes `# mset ch') \<Longrightarrow> xa \<in># \<Sum>\<^sub># (mset_nodes `# mset (ch )) \<Longrightarrow> hp_prev_children xa (ch @ ch') = hp_prev_children xa (ch)\<close>
  apply (induction xa ch rule: hp_prev_children.induct)
  subgoal for a x y children
    by (subgoal_tac \<open>distinct_mset (sum_list (map mset_nodes ((y # children) @ ch')))\<close>)
     (auto simp: hp_prev_children.simps(1) dest!: multi_member_split split: option.splits
      dest: WB_List_More.distinct_mset_union2)
  subgoal
    by (auto simp: hp_prev_children.simps(1) split: option.splits dest: multi_member_split)
  subgoal by auto
  done

lemma hp_prev_children_Cons_append_found[simp]:
  \<open>m \<notin># sum_list (map mset_nodes a) \<Longrightarrow> m \<notin># sum_list (map mset_nodes ch) \<Longrightarrow>  m \<notin># sum_list (map mset_nodes b) \<Longrightarrow> hp_prev_children m (a @ Hp m w\<^sub>m ch # b) = option_last a\<close>
  by (induction m a rule: hp_prev_children.induct)
   (auto simp: hp_prev_children.simps(1))


lemma hp_prev_children_append_single_remove_children:
  \<open>NO_MATCH [] ch\<^sub>m \<Longrightarrow> x \<in># sum_list (map mset_nodes a) \<Longrightarrow>
     distinct_mset (sum_list (map mset_nodes (Hp m w\<^sub>m ch\<^sub>m # a))) \<Longrightarrow>
     map_option node (hp_prev_children x (Hp m w\<^sub>m ch\<^sub>m # a)) =
     map_option node (hp_prev_children x (Hp m w\<^sub>m [] # a))\<close>
  by (induction a) (auto simp: hp_prev_children.simps(1) distinct_mset_add split: option.splits
    dest!: multi_member_split)

lemma map_option_skip_in_child:
  \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes a))) \<Longrightarrow> m \<notin># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow>
  ch\<^sub>m \<noteq> [] \<Longrightarrow>
  hp_prev_children (node (hd ch\<^sub>m)) (a @ [Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m)]) = Some (Hp n w\<^sub>n ch\<^sub>n)\<close>
  apply (induction \<open>node (hd ch\<^sub>m)\<close> a rule: hp_prev_children.induct)
  subgoal for x y children
    by (cases x; cases y)
     (auto simp add: hp_prev_children.simps(1) disjunct_not_in distinct_mset_add
      split: option.splits)
  subgoal for b
    by (cases b)
     (auto simp: hp_prev_children.simps(1) disjunct_not_in distinct_mset_add
      split: option.splits)
  subgoal by auto
  done



lemma hp_child_children_skip_first[simp]:
  \<open>x \<in># sum_list (map mset_nodes ch') \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes ch) + sum_list (map mset_nodes ch')) \<Longrightarrow>
  hp_child_children x (ch @ ch') = hp_child_children x ch'\<close>
  apply (induction ch)
  apply (auto simp: hp_child_children_Cons_if dest!: multi_member_split)
  by (metis WB_List_More.distinct_mset_union2 union_ac(1))

lemma hp_child_children_skip_last[simp]:
  \<open>x \<in># sum_list (map mset_nodes ch) \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes ch) + sum_list (map mset_nodes ch')) \<Longrightarrow>
  hp_child_children x (ch @ ch') = hp_child_children x ch\<close>
  apply (induction ch)
  apply (auto simp: hp_child_children_Cons_if dest!: multi_member_split)
  by (metis WB_List_More.distinct_mset_union2 union_ac(1))

lemma hp_child_children_skip_last_in_first:
  \<open> distinct_mset (sum_list (map mset_nodes (Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m) # b))) ⟹
  hp_child_children n (Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m) # b) = hp_child n (Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m))\<close>
  by (auto simp: hp_child_children_Cons_if split: option.splits)

lemma hp_child_children_hp_child[simp]: \<open>hp_child_children x [a] = hp_child x a\<close>
  by (auto simp: hp_child_children_def List.map_filter_def)

lemma hp_next_children_last[simp]:
  \<open>distinct_mset (sum_list (map mset_nodes a)) \<Longrightarrow> a \<noteq> [] \<Longrightarrow>
  hp_next_children (node (last a)) (a @ b) = option_hd b\<close>
  apply (induction \<open>node (last a)\<close> a rule: hp_next_children.induct)
  apply (auto simp: hp_next_children.simps(1) dest: multi_member_split)
  apply (metis add_diff_cancel_right' distinct_mset_in_diff node_in_mset_nodes)
  apply (metis add_diff_cancel_right' distinct_mset_in_diff node_in_mset_nodes)
  apply (metis Duplicate_Free_Multiset.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff empty_append_eq_id hp_next_None_notin node_in_mset_nodes option.simps(4))
  apply (metis Misc.last_in_set add_diff_cancel_left' distinct_mem_diff_mset node_in_mset_nodes sum_list_map_remove1 union_iff)
  apply (metis (no_types, lifting) add_diff_cancel_left' append_butlast_last_id distinct_mem_diff_mset distinct_mset_add inter_mset_empty_distrib_right list.distinct(2) list.sel(1) map_append node_hd_in_sum node_in_mset_nodes sum_list.append)
  apply (metis add_diff_cancel_right' append_butlast_last_id distinct_mset_add distinct_mset_in_diff hp_next_None_notin list.sel(1) map_append node_hd_in_sum not_Cons_self2 option.case(1) sum_list.append union_iff)
  by (metis (no_types, lifting) arith_simps(50) hp_next_children_hd_simps hp_next_children_simps(1) list.exhaust list.sel(1) list.simps(8) list.simps(9) option_hd_Some_iff(1) sum_list.Cons sum_list.Nil)



lemma hp_next_children_skip_last_not_last:
  \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes b))  \<Longrightarrow>
  a \<noteq> [] \<Longrightarrow>
     x \<noteq> node (last a) \<Longrightarrow> x \<in># sum_list (map mset_nodes a) \<Longrightarrow>
  hp_next_children x (a @ b) = hp_next_children x a\<close>
  apply (cases a rule: rev_cases)
  subgoal by auto
  subgoal for ys y
    apply (cases \<open>x \<notin># mset_nodes (last a)\<close>)
    subgoal by (auto simp: ac_simps)
    subgoal
      apply auto
      apply (subst hp_next_children_skip_first_append)
      apply (auto simp: ac_simps)
      using distinct_mset_in_diff apply fastforce
      using distinct_mset_in_diff distinct_mset_union by fastforce
      done
  done

lemma hp_node_children_append_case:
  \<open>hp_node_children x (a @ b) = (case hp_node_children x a of None \<Rightarrow> hp_node_children x b | x \<Rightarrow> x)\<close>
   by (auto simp: hp_node_children_def List.map_filter_def split: option.splits)

lemma hp_node_children_append[simp]:
  \<open>hp_node_children x a = None \<Longrightarrow> hp_node_children x (a @ b) = hp_node_children x b\<close>
  \<open>hp_node_children x a \<noteq> None \<Longrightarrow> hp_node_children x (a @ b) = hp_node_children x a\<close>
   by (auto simp: hp_node_children_append_case)

lemma ex_hp_node_children_Some_in_mset_nodes:
  \<open>(\<exists>y. hp_node_children xa a = Some y) \<longleftrightarrow> xa \<in># sum_list (map mset_nodes a)\<close>
  using hp_node_children_None_notin2[of xa a] by auto

hide_const (open) NEMonad.ASSERT NEMonad.RETURN NEMonad.SPEC

lemma hp_node_node_itself[simp]: \<open>hp_node (node x2) x2 = Some x2\<close>
  by (cases x2; cases \<open>hps x2\<close>) auto

lemma hp_child_hd[simp]: \<open>hp_child x1 (Hp x1 x2 x3) = option_hd x3\<close>
  by (cases x3) auto

(*TODO Move*)
lemma drop_is_single_iff: \<open>drop e xs = [a] \<longleftrightarrow> last xs = a \<and> e = length xs - 1 \<and> xs \<noteq> []\<close>
  apply auto
  apply (metis append_take_drop_id last_snoc)
  by (metis diff_diff_cancel diff_is_0_eq' length_drop length_list_Suc_0 n_not_Suc_n nat_le_linear)

(*TODO this is the right ordering for the theorems*)
lemma distinct_mset_mono': \<open>distinct_mset D \<Longrightarrow> D' \<subseteq># D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

context pairing_heap_assms
begin

lemma pass\<^sub>1_append_even: \<open>even (length xs) \<Longrightarrow> pass\<^sub>1 (xs @ ys) = pass\<^sub>1 xs @ pass\<^sub>1 ys\<close>
  by (induction xs rule: pass\<^sub>1.induct) auto

lemma pass\<^sub>2_None_iff[simp]: \<open>pass\<^sub>2 list = None \<longleftrightarrow> list = []\<close>
  by (cases list)
   auto

lemma last_pass\<^sub>1[simp]: "odd (length xs) \<Longrightarrow> last (pass\<^sub>1 xs) = last xs"
  by (metis pass\<^sub>1.simps(2) append_butlast_last_id even_Suc last_snoc length_append_singleton
    length_greater_0_conv odd_pos pass\<^sub>1_append_even)

lemma get_min2_alt_def: \<open>get_min2 (Some h) = node h\<close>
  by (cases h) auto


fun hp_parent :: \<open>'a \<Rightarrow> ('a, 'b) hp \<Rightarrow> ('a, 'b)hp option\<close> where
  \<open>hp_parent n (Hp a sc (x # children)) = (if n = node x then Some (Hp a sc (x # children)) else map_option the (option_hd (filter ((\<noteq>) None) (map (hp_parent n) (x#children)))))\<close> |
  \<open>hp_parent n _ = None\<close>

definition hp_parent_children :: \<open>'a \<Rightarrow> ('a, 'b) hp list \<Rightarrow> ('a, 'b)hp option\<close> where
  \<open>hp_parent_children n xs =  map_option the (option_hd (filter ((\<noteq>) None) (map (hp_parent n) xs)))\<close>


lemma hp_parent_None_notin[simp]: \<open>m \<notin># mset_nodes a \<Longrightarrow> hp_parent m a = None\<close>
  apply (induction m a rule: hp_parent.induct)
  apply (auto simp: filter_empty_conv)
  by (metis node_in_mset_nodes sum_list_map_remove1 union_iff)

lemma hp_parent_children_None_notin[simp]: \<open>(m) \<notin># sum_list (map mset_nodes a) \<Longrightarrow> hp_parent_children m a = None\<close>
  by (induction a)
   (auto simp: filter_empty_conv hp_parent_children_def)

lemma hp_parent_children_cons: \<open>hp_parent_children a (x # children) = (case hp_parent a x of None \<Rightarrow> hp_parent_children a children | Some a \<Rightarrow> Some a)\<close>
  by (auto simp: hp_parent_children_def)

lemma hp_parent_simps_if:
  \<open>hp_parent n (Hp a sc (x # children)) = (if n = node x then Some (Hp a sc (x # children)) else hp_parent_children n (x#children))\<close>
  by (auto simp: hp_parent_children_def)

lemmas [simp del] = hp_parent.simps(1)

lemma hp_parent_simps:
  \<open>n = node x \<Longrightarrow> hp_parent n (Hp a sc (x # children)) = Some (Hp a sc (x # children))\<close>
  \<open>n \<noteq> node x \<Longrightarrow> hp_parent n (Hp a sc (x # children)) = hp_parent_children n (x # children)\<close>
  by (auto simp: hp_parent_simps_if)

lemma hp_parent_itself[simp]: \<open>distinct_mset (mset_nodes x) \<Longrightarrow> hp_parent (node x) x = None\<close>
  by (cases \<open>(node x, x)\<close> rule: hp_parent.cases)
   (auto simp: hp_parent.simps hp_parent_children_def filter_empty_conv sum_list_map_remove1)

lemma hp_parent_children_itself[simp]:
  \<open>distinct_mset (mset_nodes x + sum_list (map mset_nodes children)) \<Longrightarrow> hp_parent_children (node x) (x # children) = None\<close>
  by (auto simp: hp_parent_children_def filter_empty_conv disjunct_not_in distinct_mset_add sum_list_map_remove1 dest: distinct_mset_union)

lemma hp_parent_in_nodes: \<open>hp_parent n x \<noteq> None \<Longrightarrow> node (the (hp_parent n x)) \<in># mset_nodes x\<close>
  apply (induction n x rule: hp_parent.induct)
  subgoal premises p for n a sc x children
    using p p(1)[of xa]
    apply (auto simp: hp_parent.simps)
    apply (cases \<open>filter (\<lambda>y. \<exists>ya. y = Some ya) (map (hp_parent n) children)\<close>)
    apply (fastforce simp: filter_empty_conv filter_eq_Cons_iff map_eq_append_conv)+
    done
  subgoal for n v va
    by (auto simp: hp_parent.simps filter_empty_conv)
  done

lemma hp_parent_children_Some_iff:
  \<open>hp_parent_children a xs = Some y \<longleftrightarrow> (\<exists>u b as. xs = u @ b # as \<and> (\<forall>x\<in>set u. hp_parent a x = None) \<and> hp_parent a b = Some y)\<close>
  by (cases \<open>(filter (\<lambda>y. \<exists>ya. y = Some ya) (map (hp_parent a) xs))\<close>)
   (fastforce simp: hp_parent_children_def filter_empty_conv filter_eq_Cons_iff map_eq_append_conv)+

lemma hp_parent_children_in_nodes:
  \<open>hp_parent_children b xs \<noteq> None \<Longrightarrow> node (the (hp_parent_children b xs)) \<in># \<Sum>\<^sub># (mset_nodes `# mset xs)\<close>
  by (metis hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_append(1)
    hp_node_children_append(2) hp_node_children_simps(3) hp_parent_children_Some_iff
    hp_parent_in_nodes option.collapse)

lemma hp_parent_hp_child:
  \<open>distinct_mset ((mset_nodes (a::('a,nat)hp))) \<Longrightarrow> hp_child n a \<noteq> None \<Longrightarrow> map_option node (hp_parent (node (the (hp_child n a))) a) = Some n\<close>
  apply (induction n a rule: hp_child.induct)
  subgoal for  n a sc x children
    apply (simp add: hp_parent_simps_if)
    apply auto
    subgoal for y
      apply (auto simp add: hp_parent_simps_if hp_parent_children_Some_iff 
        split: option.splits dest: distinct_mset_union)
      apply (metis (no_types, lifting) diff_single_trivial disjunct_not_in distinct_mem_diff_mset
        distinct_mset_add hp_parent_None_notin mset_cancel_union(2) mset_nodes_simps node_in_mset_nodes
        option_last_Nil option_last_Some_iff(2) sum_mset_sum_list)
      done
    subgoal for y
      using distinct_mset_union[of \<open>mset_nodes x\<close> \<open>sum_list (map mset_nodes children)\<close>]
        distinct_mset_union[of \<open>sum_list (map mset_nodes children)\<close> \<open>mset_nodes x\<close> ]
      apply (auto simp add: hp_parent_simps_if ac_simps hp_parent_children_cons
        split: option.splits dest: distinct_mset_union)
      apply (metis Groups.add_ac(2) add_mset_add_single disjunct_not_in distinct_mset_add hp_parent_None_notin member_add_mset mset_nodes_simps option_last_Nil option_last_Some_iff(2) sum_mset_sum_list)
      by (smt (verit, best) get_min2.simps get_min2_alt_def hp.inject hp_parent.elims hp_parent_simps(2) option_last_Nil option_last_Some_iff(2))
    done
  subgoal by auto
  done


lemma hp_child_hp_parent:
  \<open>distinct_mset ((mset_nodes (a::('a,nat)hp))) \<Longrightarrow> hp_parent n a \<noteq> None \<Longrightarrow> map_option node (hp_child (node (the (hp_parent n a))) a) = Some n\<close>
  apply (induction n a rule: hp_parent.induct)
  subgoal for  n a sc x children
    apply (simp add: hp_parent_simps_if)
    apply auto
    subgoal for y
      using distinct_mset_union[of \<open>mset_nodes x\<close> \<open>sum_list (map mset_nodes children)\<close>]
        distinct_mset_union[of \<open>sum_list (map mset_nodes children)\<close> \<open>mset_nodes x\<close> ]
      apply (auto simp add: hp_parent_simps_if hp_parent_children_cons ac_simps
        split: option.splits)
      apply (smt (verit, del_insts) hp_parent_children_Some_iff hp_parent_in_nodes list.map(2) map_append option.sel option_last_Nil option_last_Some_iff(2) sum_list.append sum_list_simps(2) union_iff)
      by fastforce
    subgoal premises p for yy
      using p(2-) p(1)[of x]
      using distinct_mset_union[of \<open>mset_nodes x\<close> \<open>sum_list (map mset_nodes children)\<close>]
        distinct_mset_union[of \<open>sum_list (map mset_nodes children)\<close> \<open>mset_nodes x\<close> ]
      apply (auto simp add: hp_parent_simps_if hp_parent_children_cons ac_simps
        split: option.splits)
      apply (smt (verit, del_insts) disjunct_not_in distinct_mset_add hp_child_None_notin
        hp_parent_children_Some_iff hp_parent_in_nodes list.map(2) map_append option.sel
        option_last_Nil option_last_Some_iff(2) sum_list.Cons sum_list.append union_iff)

      using p(1)
      apply (auto simp: hp_parent_children_Some_iff)
      by (metis WB_List_More.distinct_mset_union2 distinct_mset_union hp_child_children_simps(3)
        hp_child_children_skip_first hp_child_hp_children_simps2 hp_parent_in_nodes list.map(2)
        option.sel option_last_Nil option_last_Some_iff(2) sum_list.Cons union_iff)
    done
  subgoal by auto
  done

lemma hp_parent_children_append_case:
  \<open>hp_parent_children a (xs @ ys) = (case hp_parent_children a xs of None \<Rightarrow> hp_parent_children a ys | Some a \<Rightarrow> Some a)\<close>
  by (auto simp: hp_parent_children_def comp_def option_hd_def)

lemma hp_parent_children_append_skip_first[simp]:
  \<open>a \<notin># \<Sum>\<^sub># (mset_nodes `# mset xs) \<Longrightarrow> hp_parent_children a (xs @ ys) = hp_parent_children a ys\<close>
  by (auto simp: hp_parent_children_append_case split: option.splits)

lemma hp_parent_children_append_skip_second[simp]:
  \<open>a \<notin># \<Sum>\<^sub># (mset_nodes `# mset ys) \<Longrightarrow> hp_parent_children a (xs @ ys) = hp_parent_children a xs\<close>
  by (auto simp: hp_parent_children_append_case split: option.splits)

lemma hp_parent_simps_single_if:
 \<open>hp_parent n (Hp a sc (children)) =
  (if children = [] then None else if n = node (hd children) then Some (Hp a sc (children))
  else hp_parent_children n children)\<close>
 by (cases children)
   (auto simp: hp_parent_simps)

lemma hp_parent_children_remove_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> hp_parent_children a (remove_key_children a xs) = None\<close>
  apply (induction a xs rule: remove_key_children.induct)
  subgoal by auto
  subgoal for k x n c xs
    apply (auto simp: hp_parent_simps_if hp_parent_children_cons
      split: option.split
      dest: WB_List_More.distinct_mset_union2)
    apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in
      distinct_mset_add hp.sel(1) hp_parent_simps_single_if list.map(2) list.sel(1) list.simps(3)
      node_hd_in_sum node_in_mset_nodes option_last_Nil option_last_Some_iff(2) sum_list_simps(2)) 
    apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in
      distinct_mset_add hp.sel(1) hp_parent_simps_single_if list.map(2) list.sel(1) list.simps(3)
      node_hd_in_sum node_in_mset_nodes option_last_Nil option_last_Some_iff(2) sum_list_simps(2))
   done
  done

lemma remove_key_children_notin_unchanged[simp]: \<open>x \<notin># sum_list (map mset_nodes c) \<Longrightarrow> remove_key_children x c = c\<close>
  by (induction x c rule: remove_key_children.induct)
     auto

lemma remove_key_notin_unchanged[simp]: \<open>x \<notin># mset_nodes c \<Longrightarrow> remove_key x c = Some c\<close>
  by (induction x c rule: remove_key.induct)
     auto

lemma remove_key_remove_all: \<open>k \<notin># \<Sum>\<^sub># (mset_nodes `# mset (remove_key_children k c))\<close>
  by (induction k c rule: remove_key_children.induct) auto

lemma hd_remove_key_node_same: \<open>c \<noteq> [] \<Longrightarrow> remove_key_children k c \<noteq> [] \<Longrightarrow>
  node (hd (remove_key_children k c)) = node (hd c) \<longleftrightarrow> node (hd c) \<noteq> k\<close>
  using remove_key_remove_all[of k]
  apply (induction k c rule: remove_key_children.induct)
  apply (auto)[]
  by fastforce

lemma hd_remove_key_node_same': \<open>c \<noteq> [] \<Longrightarrow> remove_key_children k c \<noteq> [] \<Longrightarrow>
  node (hd c) = node (hd (remove_key_children k c)) \<longleftrightarrow> node (hd c) \<noteq> k\<close>
  using hd_remove_key_node_same[of c k] by auto

lemma remove_key_children_node_hd[simp]: \<open>c \<noteq> [] \<Longrightarrow> remove_key_children (node (hd c)) c= remove_key_children (node (hd c)) (tl c)\<close>
  by (cases c; cases \<open>tl c›; cases \<open>hd c\<close>)
     (auto simp: )

lemma VSIDS_remove_key_children_alt_def:
  \<open>remove_key_children k xs = map (\<lambda>x. case x of Hp a b c \<Rightarrow> Hp a b (remove_key_children k c)) (filter (\<lambda>n. node n \<noteq> k) xs)\<close>
  by (induction k xs rule: remove_key_children.induct) auto

lemma not_orig_notin_remove_key: \<open>b \<notin># sum_list (map mset_nodes xs) \<Longrightarrow>
  b \<notin># sum_list (map mset_nodes (remove_key_children a xs))\<close>
  by (induction a xs rule: remove_key_children.induct) auto

lemma hp_parent_None_notin_same_hd[simp]: \<open>b \<notin># sum_list (map mset_nodes x3) \<Longrightarrow> hp_parent b (Hp b x2 x3) = None\<close>
  by (induction x3 rule: induct_list012)
   (auto simp: hp_parent_children_cons hp_parent.simps(1) filter_empty_conv split: if_splits)

(*does not hold for the children of a*)
lemma hp_parent_children_remove_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> a \<noteq> b \<Longrightarrow>  hp_parent_children b (remove_key_children a xs) = hp_parent_children b xs\<close>
  oops


lemma hp_parent_remove_key:
  \<open>distinct_mset ((mset_nodes xs)) \<Longrightarrow> a \<noteq> node xs \<Longrightarrow> hp_parent a (the (remove_key a xs)) = None\<close>
  apply (induction a xs rule: remove_key.induct)
  subgoal for a b sc children
    apply (cases \<open>remove_key_children a children\<close>)
    apply (auto simp: hp_parent_simps_if)
    apply (smt (verit, ccfv_threshold) remove_key_children.elims distinct_mset_add empty_iff
        hp.sel(1) inter_iff list.map(2) list.sel(1) list.simps(3) node_hd_in_sum node_in_mset_nodes set_mset_empty sum_list_simps(2))
    by (metis hp_parent_children_remove_key_children mset_map sum_mset_sum_list)
  done

lemma (in pairing_heap_assms) find_key_children_None_or_itself[simp]:
  \<open>find_key_children a h \<noteq> None \<Longrightarrow> node (the (find_key_children a h)) = a\<close>
  by (induction a h rule: find_key_children.induct)
   (auto split: option.splits)

lemma (in pairing_heap_assms) find_key_None_or_itself[simp]:
  \<open>find_key a h \<noteq> None \<Longrightarrow> node (the (find_key a h)) = a\<close>
  apply (induction a h rule: find_key.induct)
  apply auto
  using find_key_children_None_or_itself by fastforce

lemma (in pairing_heap_assms) find_key_children_notin[simp]:
  \<open>a \<notin>#  \<Sum>\<^sub># (mset_nodes `# mset xs) \<Longrightarrow> find_key_children a xs = None\<close>
  by (induction a xs rule: find_key_children.induct) auto


lemma (in pairing_heap_assms) find_key_notin[simp]:
  \<open>a \<notin># mset_nodes h \<Longrightarrow> find_key a h = None\<close>
  by (induction a h rule: find_key.induct) auto

lemma (in pairing_heap_assms) mset_nodes_find_key_children_subset:
  \<open>find_key_children a h \<noteq> None \<Longrightarrow> mset_nodes (the (find_key_children a h)) \<subseteq># \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  apply (induction a h rule: find_key_children.induct)
  apply (auto split: option.splits simp: ac_simps intro: mset_le_incr_right)
  apply (metis mset_le_incr_right union_commute union_mset_add_mset_right)+
  done

lemma hp_parent_None_iff_children_None:
  \<open>hp_parent z (Hp x n c) = None \<longleftrightarrow> (c \<noteq> [] \<longrightarrow> z \<noteq> node (hd c)) \<and> hp_parent_children (z) c = None\<close>
  by (cases c; cases \<open>tl c\<close>)
  (auto simp: hp_parent_children_cons hp_parent_simps_if hp_parent.simps(1) filter_empty_conv split: option.splits)


lemma mset_nodes_find_key_subset:
  \<open>find_key a h \<noteq> None \<Longrightarrow> mset_nodes (the (find_key a h)) \<subseteq># mset_nodes h\<close>
  apply (induction a h rule: find_key.induct)
  apply (auto intro: mset_nodes_find_key_children_subset)
  by (metis mset_nodes_find_key_children_subset option.distinct(2) option.sel subset_mset_imp_subset_add_mset sum_image_mset_sum_map)

lemma find_key_none_iff[simp]:
  \<open>find_key_children a h = None \<longleftrightarrow> a \<notin># \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  by (induction a h rule: find_key_children.induct) auto

lemma find_key_noneD:
  \<open>find_key_children a h = Some x \<Longrightarrow>  a \<in># \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  using find_key_none_iff by (metis option.simps(2))

lemma hp_parent_children_hd_None[simp]:
  \<open>xs \<noteq> [] \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> hp_parent_children (node (hd xs)) xs = None\<close>
  by (cases xs; cases \<open>hd xs\<close>)
    (auto simp: hp_parent_children_def filter_empty_conv sum_list_map_remove1)

lemma hp_parent_hd_None[simp]:
  \<open>x \<notin># (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow>x \<notin># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children x (Hp x n c # xs) = None\<close>
  by (cases xs; cases \<open>hd xs\<close>; cases c)
    (auto simp: hp_parent_children_def filter_empty_conv sum_list_map_remove1 hp_parent.simps(1))

lemma hp_parent_none_children: \<open>hp_parent_children z c = None \<Longrightarrow>
    hp_parent z (Hp x n c) = Some x2a \<longleftrightarrow> (c \<noteq> [] \<and> z = node (hd c) \<and> x2a = Hp x n c)\<close>
  by (cases c)
   (auto simp:  filter_empty_conv sum_list_map_remove1 hp_parent_simps_if)

(* does not hold for Hp x _ (a # b # ...)  *)
lemma hp_parent_children_remove_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> a \<noteq> b \<Longrightarrow>  hp_parent_children b (remove_key_children a xs) =
  (if find_key_children b xs \<noteq> None then None else hp_parent_children b xs)\<close>
  oops

lemma in_the_default_empty_iff: \<open>b \<in># the_default {#} M \<longleftrightarrow> M \<noteq> None \<and> b \<in># the M\<close>
  by (cases M) auto

lemma remove_key_children_hd_tl: \<open>distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow> c \<noteq> [] \<Longrightarrow> remove_key_children (node (hd c)) (tl c) = tl c\<close>
  by (cases c) (auto simp add: disjunct_not_in distinct_mset_add)

lemma in_find_key_children_notin_remove_key:
  \<open>find_key_children k c = Some x2 \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow>
      b \<in># mset_nodes x2 \<Longrightarrow>
      b \<notin># \<Sum>\<^sub>#(mset_nodes `# mset (remove_key_children k c))\<close>
  apply (induction k c rule: remove_key_children.induct)
  subgoal by auto
  subgoal for k x n c xs
    using find_key_children_None_or_itself[of b c] find_key_children_None_or_itself[of b xs]
    using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
      distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
     apply (auto dest: multi_member_split[of b] split: option.splits)
     apply (auto dest!: multi_member_split[of b])[]
     apply (metis mset_nodes_find_key_children_subset option.distinct(1) option.sel subset_mset.le_iff_add sum_image_mset_sum_map union_iff)
     apply (metis add_diff_cancel_right' distinct_mset_in_diff mset_nodes_find_key_children_subset option.distinct(1) option.sel subset_mset.le_iff_add
           sum_image_mset_sum_map)
     apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(2) option.sel sum_image_mset_sum_map)
     by (metis add_diff_cancel_right' distinct_mset_in_diff mset_nodes_find_key_children_subset not_orig_notin_remove_key option.distinct(1)
  option.sel subset_mset.le_iff_add sum_image_mset_sum_map)
   done

lemma hp_parent_children_None_hp_parent_iff: \<open>hp_parent_children b list = None \<Longrightarrow> hp_parent b (Hp x n list) = Some x2a \<longleftrightarrow> list \<noteq> [] \<and> node (hd list) = b \<and> x2a = Hp x n list\<close>
  by (cases list; cases \<open>tl list\<close>) (auto simp: hp_parent_simps_if)

lemma (in pairing_heap_assms) hp_parent_children_not_hd_node:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> node (hd c) = node x2a \<Longrightarrow> c \<noteq> [] \<Longrightarrow>  remove_key_children (node x2a) c \<noteq> [] \<Longrightarrow>
    hp_parent_children (node (hd (remove_key_children (node x2a) c))) c = Some x2a \<Longrightarrow> False\<close>
  apply (cases c; cases \<open>tl c\<close>; cases \<open>hd c\<close>)
  apply (auto simp: hp_parent_children_cons
    split: option.splits)
  apply (simp add:  disjunct_not_in distinct_mset_add)
  apply (metis hp_parent_in_nodes option.distinct(1) option.sel)
  by (smt (verit, ccfv_threshold) WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp.sel(1) hp_parent_children_in_nodes hp_parent_simps_single_if list.sel(1) node_hd_in_sum node_in_mset_nodes option.sel option_last_Nil option_last_Some_iff(2) remove_key_children.elims sum_image_mset_sum_map)

lemma hp_parent_children_hd_tl_None[simp]: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> c \<noteq> [] \<Longrightarrow> a \<in> set (tl c)\<Longrightarrow>  hp_parent_children (node a) c = None\<close>
  apply (cases c)
    apply (auto simp: hp_parent_children_def filter_empty_conv dest!: split_list[of a])
    apply (metis add_diff_cancel_left' add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff hp_parent_None_notin node_in_mset_nodes)
  apply (simp add: distinct_mset_add)
  apply (simp add: distinct_mset_add)
  apply (metis (no_types, opaque_lifting) disjunct_not_in hp_parent_None_notin mset_subset_eqD mset_subset_eq_add_right node_in_mset_nodes sum_list_map_remove1 union_commute)
  by (metis WB_List_More.distinct_mset_union2 add_diff_cancel_left' distinct_mem_diff_mset hp_parent_None_notin node_in_mset_nodes sum_list_map_remove1 union_iff)


lemma hp_parent_hp_parent_remove_key_not_None_same:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c))\<close> and
    \<open>x \<notin># \<Sum>\<^sub># (mset_nodes `# mset c)\<close> and
    \<open>hp_parent b (Hp x n c) = Some x2a\<close> \<open>b \<notin># mset_nodes x2a\<close>
    \<open>hp_parent b (Hp x n (remove_key_children k c)) = Some x2b›
  shows \<open>remove_key k x2a \<noteq> None \<and> (case remove_key k x2a of Some a \<Rightarrow> (x2b) = a | None \<Rightarrow> node x2a = k)\<close>
proof -
  show ?thesis
    using assms
  proof (induction k c rule: remove_key_children.induct)
    case (1 k)
    then show ?case by (auto simp: hp_parent_children_cons split: if_splits)
  next
    case (2 k x n c xs)
    moreover have \<open>c \<noteq> [] \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> node (hd xs) \<noteq> node (hd c)\<close>
      using 2(4) by  (cases c; cases \<open>hd c\<close>; cases xs; auto)
    moreover have \<open>xs \<noteq> [] \<Longrightarrow> hp_parent_children (node (hd xs)) c = None\<close>
      by (metis (no_types, lifting) add_diff_cancel_left' calculation(4) distinct_mset_in_diff
        distinct_mset_union hp_parent_children_None_notin list.map(2) mset_nodes.simps
        node_hd_in_sum sum_image_mset_sum_map sum_list.Cons)
    moreover have \<open>c \<noteq> [] \<Longrightarrow> hp_parent_children (node (hd c)) xs = None\<close>
      by (metis calculation(4) disjunct_not_in distinct_mset_add hp_parent_None_iff_children_None
        hp_parent_None_notin hp_parent_children_None_notin list.simps(9) sum_image_mset_sum_map
        sum_list.Cons)
    moreover have [simp]: \<open>remove_key (node x2a) x2a = None\<close>
      by (cases x2a) auto
    moreover have
      \<open>hp_parent_children b xs \<noteq> None \<Longrightarrow> hp_parent_children b c = None\<close>
      \<open>hp_parent_children b c \<noteq> None \<Longrightarrow> hp_parent_children b xs = None\<close>
      \<open>node x2a \<in># sum_list (map mset_nodes c) \<Longrightarrow> node x2a \<notin># sum_list (map mset_nodes xs)\<close>
      using hp_parent_children_in_nodes[of b xs] hp_parent_children_in_nodes[of b c] 2(4)
      apply auto
      apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.distinct(1))
      apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.distinct(1))
      apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.distinct(1))
      done
    ultimately show ?case
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
        hp_parent_children_in_nodes[of b c]  hp_parent_children_in_nodes[of b xs]
      apply (auto simp: hp_parent_children_cons remove_key_None_iff split: if_splits option.splits)
      apply (auto simp: hp_parent_simps_single_if hp_parent_children_cons split: option.splits if_splits)[]
      apply (auto simp: hp_parent_simps_single_if hp_parent_children_cons split: option.splits if_splits)[]
      apply (auto simp: hp_parent_children_cons hp_parent_simps_single_if  handy_if_lemma split: if_splits option.splits )[]
      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
      apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
        list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
      apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
        list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
      apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
        list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
      apply (smt (verit, ccfv_threshold) remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
        list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        cases \<open>node x2a \<in># sum_list (map mset_nodes c)\<close>; auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits)

      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same[of c \<open>node x2a\<close>]
        intro: hp_parent_children_not_hd_node
        split: if_splits option.splits)

      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same
        dest: hp_parent_children_not_hd_node split: if_splits option.splits
        intro: hp_parent_children_not_hd_node)

      apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>remove_key_children (node x2a) xs = []\<close>;
        cases \<open>b = node (hd (remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (remove_key_children (node x2a) xs) = x2b\<close>;
        cases \<open>node x2a \<in># sum_list (map mset_nodes c)\<close>;
        auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits)

      apply (cases \<open>xs = []\<close>)
      apply (auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same remove_key_children_hd_tl
        dest: hp_parent_children_not_hd_node split: if_splits option.splits)[2]
      apply (smt (verit, best) hd_remove_key_node_same' hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_children_hd_tl_None hp_parent_simps_single_if in_hd_or_tl_conv mset_map option_hd_Nil option_hd_Some_iff(1) remove_key_children_hd_tl remove_key_children_node_hd sum_mset_sum_list)
      apply (smt (verit, best) hd_remove_key_node_same' hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_children_hd_tl_None hp_parent_simps_single_if in_hd_or_tl_conv mset_map option_hd_Nil option_hd_Some_iff(1) remove_key_children_hd_tl remove_key_children_node_hd sum_mset_sum_list)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_parent_children_None_notin not_orig_notin_remove_key option_hd_Nil option_hd_Some_iff(2))
      apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin node_hd_in_sum not_orig_notin_remove_key option_last_Nil option_last_Some_iff(1) remove_key_children_hd_tl remove_key_children_node_hd)
      apply (smt (verit, del_insts) remove_key_children.simps(1) hd_remove_key_node_same' hp_parent_children_None_notin hp_parent_children_hd_None hp_parent_children_hd_tl_None in_hd_or_tl_conv option.distinct(1) remove_key_children_hd_tl remove_key_children_node_hd remove_key_remove_all sum_image_mset_sum_map)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_parent_children_None_notin not_orig_notin_remove_key option_hd_Nil option_hd_Some_iff(2))
      by (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin not_orig_notin_remove_key option_hd_Nil option_hd_Some_iff(2))
  qed
qed

lemma (in pairing_heap_assms) in_remove_key_children_changed: \<open>k \<in># sum_list (map mset_nodes c) \<Longrightarrow> remove_key_children k c \<noteq> c\<close>
  apply (induction k c rule: remove_key_children.induct)
  apply auto
  apply (metis hp.sel(1) list.sel(1) mset_map neq_Nil_conv node_hd_in_sum remove_key_remove_all sum_mset_sum_list)+
  done

lemma hp_parent_in_nodes2: \<open>hp_parent (z) xs = Some a \<Longrightarrow> node a \<in># mset_nodes xs\<close>
  apply (induction z xs rule: hp_parent.induct)
  apply (auto simp: hp_parent_children_def filter_empty_conv)
  by (metis empty_iff hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_simps(2) hp_parent_in_nodes
    member_add_mset mset_nodes_simps option.discI option.sel set_mset_empty sum_image_mset_sum_map sum_mset_sum_list union_iff)

lemma hp_parent_children_in_nodes2: \<open>hp_parent_children (z) xs = Some a \<Longrightarrow> node a \<in># \<Sum>\<^sub># (mset_nodes `# mset xs)\<close>
    apply (induction xs)
    apply (auto simp: hp_parent_children_cons filter_empty_conv split: option.splits)
    using hp_parent_in_nodes by fastforce

lemma hp_next_in_nodes2: \<open>hp_next (z) xs = Some a \<Longrightarrow> node a \<in># mset_nodes xs\<close>
  apply (induction z xs rule: hp_next.induct)
  apply (auto simp: )
  by (metis hp_next_children.simps(1) hp_next_children_simps(2) hp_next_children_simps(3) node_in_mset_nodes option.sel)

lemma hp_next_children_in_nodes2: \<open>hp_next_children (z) xs = Some a \<Longrightarrow> node a \<in># \<Sum>\<^sub># (mset_nodes `# mset xs)\<close>
  apply (induction z xs rule: hp_next_children.induct)
  apply (auto simp:  hp_next_in_nodes2 split: option.splits)
  by (metis hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_in_nodes2 node_in_mset_nodes option.inject)

lemma in_remove_key_changed: \<open>remove_key k a \<noteq> None \<Longrightarrow> a = the (remove_key k a) \<longleftrightarrow> k \<notin># mset_nodes a\<close>
  apply (induction k a rule: remove_key.induct)
  apply (auto simp: in_remove_key_children_changed)
  by (metis in_remove_key_children_changed)

lemma node_remove_key_children_in_mset_nodes: \<open>\<Sum>\<^sub># (mset_nodes `# mset (remove_key_children k c)) \<subseteq># (\<Sum>\<^sub># (mset_nodes `# mset c))\<close>
  apply (induction k c rule: remove_key_children.induct)
  apply auto
  apply (metis mset_le_incr_right(2) union_commute union_mset_add_mset_right)
  using subset_mset.add_mono by blast

lemma remove_key_children_hp_parent_children_hd_None: \<open>remove_key_children k c = a # list \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow>
  hp_parent_children (node a) (a # list) = None\<close>
  using node_remove_key_children_in_mset_nodes[of k c]
  apply (auto simp: hp_parent_children_def filter_empty_conv)
  apply (meson WB_List_More.distinct_mset_mono distinct_mset_union hp_parent_itself)
  by (metis WB_List_More.distinct_mset_mono add_diff_cancel_left' distinct_mem_diff_mset hp_parent_None_notin node_in_mset_nodes sum_list_map_remove1 union_iff)


lemma hp_next_not_same_node: \<open>distinct_mset (mset_nodes b) \<Longrightarrow> hp_next x b = Some y \<Longrightarrow> x \<noteq> node y\<close>
  apply (induction x b rule: hp_next.induct)
  apply auto
    by (metis disjunct_not_in distinct_mset_add hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) inter_mset_empty_distrib_right node_in_mset_nodes option.sel)

lemma hp_next_children_not_same_node: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> hp_next_children x c = Some y \<Longrightarrow> x \<noteq> node y\<close>
  apply (induction x c rule: hp_next_children.induct)
  subgoal
    apply (auto simp: hp_next_children.simps(1) split: if_splits option.splits dest: hp_next_not_same_node)
    apply (metis (no_types, opaque_lifting) distinct_mset_iff hp.exhaust_sel mset_nodes_simps union_mset_add_mset_left union_mset_add_mset_right)
    apply (metis Duplicate_Free_Multiset.distinct_mset_mono mset_subset_eq_add_left union_commute)
      by (meson distinct_mset_union hp_next_not_same_node)
  subgoal apply auto
    by (meson hp_next_not_same_node)
  subgoal by auto
  done

lemma hp_next_children_hd_is_hd_tl: \<open>c \<noteq> [] \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> hp_next_children (node (hd c)) c = option_hd (tl c)\<close>
  by (cases c; cases \<open>tl c\<close>) auto

lemma hp_parent_children_remove_key_children_other:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_parent_children b (remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key_children a xs))) then None
    else if map_option node (hp_next_children a xs) = Some b then map_option (the o remove_key a) (hp_parent_children a xs)
    else map_option (the o remove_key a) (hp_parent_children b xs))\<close>
  using assms
proof (induction a xs rule: remove_key_children.induct)
  case (1 k)
  then show ?case by auto
next
  case (2 k x n c xs)
  have [intro]: \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close>
    using 2(4) by (auto simp: in_the_default_empty_iff dest!: multi_member_split split: if_splits)
  consider
    (kx) \<open>k=x\<close> |
    (inc) \<open>k \<noteq> x› \<open>find_key_children k c \<noteq> None\<close> |
    (inxs) \<open>k \<noteq> x› \<open>find_key_children k c = None\<close>
    by blast
  then show ?case
  proof (cases)
    case kx
    then show ?thesis 
      apply (auto simp: in_the_default_empty_iff)
      using find_key_children_None_or_itself[of b c] find_key_children_None_or_itself[of b xs] 2
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
      by (auto simp: not_orig_notin_remove_key in_the_default_empty_iff hp_parent_children_cons
        split: option.split if_splits)
  next
    case inc
    moreover have \<open>b \<in># mset_nodes (the (find_key_children k c)) \<Longrightarrow> b \<in># \<Sum>\<^sub># (mset_nodes `# mset c)\<close>
      using inc by (meson mset_nodes_find_key_children_subset mset_subset_eqD)
    moreover have c: \<open>c \<noteq> []\<close>
      using inc by auto
    moreover have [simp]: \<open>remove_key_children (node (hd c)) (tl c) = tl c\<close>
      using c 2(4) by (cases c; cases \<open>hd c\<close>) auto
    moreover have [simp]: \<open>find_key_children (node (hd c)) c = Some (hd c)\<close>
      using c 2(4) by (cases c; cases \<open>hd c\<close>) auto
    moreover have [simp]: \<open>k \<in># sum_list (map mset_nodes c) \<Longrightarrow> k \<notin># sum_list (map mset_nodes xs)\<close> for k
      using 2(4) by (auto dest!: multi_member_split)
    moreover have KK[iff]: \<open>remove_key_children k c = [] \<longleftrightarrow> c = [] \<or> (c \<noteq> [] \<and>  tl c = [] \<and> node (hd c) = k)\<close>
      using 2(4)
      by (induction k c rule: remove_key_children.induct) (auto simp: dest: multi_member_split)
    ultimately show ?thesis
      using find_key_children_None_or_itself[of b c] find_key_children_None_or_itself[of b xs] 2
        find_key_children_None_or_itself[of k c] find_key_children_None_or_itself[of k xs]
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
      apply (auto simp: not_orig_notin_remove_key in_the_default_empty_iff split: option.split if_splits)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis hp_parent_None_iff_children_None in_find_key_children_notin_remove_key mset_map node_hd_in_sum sum_mset_sum_list)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis hp_parent_None_iff_children_None in_find_key_children_notin_remove_key mset_map node_hd_in_sum sum_mset_sum_list)
        defer

      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None
        hp_parent_children_None_hp_parent_iff split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis KK \<open>remove_key_children (node (hd c)) (tl c) = tl c\<close>
        hd_remove_key_node_same' hp_next_children_hd_simps list.exhaust_sel option_hd_def remove_key_children_node_hd)
      apply (metis KK hd_remove_key_node_same')
      apply (metis KK find_key_children_None_or_itself hd_remove_key_node_same inc(2) node_in_mset_nodes option.sel)
      apply (smt (verit) remove_key.simps \<open>remove_key_children (node (hd c)) (tl c) = tl c\<close> \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close>
        hd_remove_key_node_same hp_next_children.elims hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_none_children
        hp_parent_simps_single_if list.sel(1) list.sel(3) o_apply option.map_sel option.sel remove_key_children_node_hd sum_image_mset_sum_map)


      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None
        hp_parent_children_None_hp_parent_iff in_remove_key_changed split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close> hp_next_children_in_nodes2 sum_image_mset_sum_map)

      apply (smt (verit, ccfv_threshold) remove_key_children.elims WB_List_More.distinct_mset_mono \<open>find_key_children (node (hd c)) c = Some (hd c)\<close> \<open>remove_key_children (node (hd c)) (tl c) = tl c\<close> add_diff_cancel_left' distinct_mset_in_diff hp.exhaust_sel hp.inject hp_next_children_in_nodes2
        hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps in_remove_key_children_changed list.exhaust_sel list.sel(1) mset_nodes_simps
        mset_nodes_find_key_children_subset option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map sum_mset_sum_list union_single_eq_member)
      apply (smt (verit, ccfv_threshold) remove_key_children.elims WB_List_More.distinct_mset_mono \<open>find_key_children (node (hd c)) c = Some (hd c)\<close>
        \<open>remove_key_children (node (hd c)) (tl c) = tl c\<close> add_diff_cancel_left' distinct_mset_in_diff hp.exhaust_sel hp.inject hp_next_children_in_nodes2
        hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps in_remove_key_children_changed list.exhaust_sel list.sel(1) mset_nodes_simps
        mset_nodes_find_key_children_subset option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map sum_mset_sum_list union_single_eq_member)
      apply (metis handy_if_lemma hp_next_children_hd_simps list.exhaust_sel option_hd_def)
      apply (metis hp_next_children_hd_is_hd_tl mset_map option_hd_Some_iff(1) sum_mset_sum_list)
      by (smt (verit, best) None_eq_map_option_iff remove_key.simps hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_none_children hp_parent_simps_single_if list.exhaust_sel o_apply option.map_sel option.sel remove_key_children_hp_parent_children_hd_None sum_image_mset_sum_map)
  next
    case inxs
    moreover have True
      by auto
    ultimately show ?thesis
      using find_key_children_None_or_itself[of b c] find_key_children_None_or_itself[of b xs] 2
        find_key_children_None_or_itself[of k c] find_key_children_None_or_itself[of k xs]
        hp_next_children_in_nodes2[of k xs]
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
      apply (auto simp: not_orig_notin_remove_key in_the_default_empty_iff split: option.split if_splits)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff ex_hp_node_children_Some_in_mset_nodes
        split: option.split intro!: hp_parent_None_notin
        dest: in_find_key_children_notin_remove_key multi_member_split
        mset_nodes_find_key_children_subset)[2]
      apply (cases \<open>hp_next_children k xs\<close>)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff ex_hp_node_children_Some_in_mset_nodes
        split: option.split intro!: hp_parent_None_notin
        dest: in_find_key_children_notin_remove_key multi_member_split
        mset_nodes_find_key_children_subset)[2]
      apply (metis (no_types, lifting)  find_key_none_iff mset_map
        mset_nodes_find_key_children_subset mset_subset_eqD  option.map_sel sum_mset_sum_list)
      apply (metis (no_types, lifting)  find_key_none_iff mset_map
        mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel sum_mset_sum_list)
      apply (metis (no_types, lifting) distinct_mset_add find_key_none_iff in_the_default_empty_iff inter_iff mset_map
        mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel sum_mset_sum_list the_default.simps(2))
      apply (smt (verit) add_diff_cancel_left' distinct_mem_diff_mset hp_next_children_in_nodes2 hp_parent_None_iff_children_None hp_parent_children_None_notin hp_parent_children_append_case hp_parent_children_append_skip_first hp_parent_children_cons mset_map node_hd_in_sum sum_mset_sum_list)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis (mono_tags, opaque_lifting) remove_key.simps comp_def hp_parent_None_iff_children_None hp_parent_children_None_hp_parent_iff hp_parent_simps_single_if option.map_sel option.sel remove_key_children_notin_unchanged)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      by (metis (no_types, opaque_lifting) remove_key.simps hp_parent_simps_single_if option.distinct(1) option.map(2) option.map_comp option.sel remove_key_children_notin_unchanged)
  qed
qed


lemma hp_parent_remove_key_other:
  assumes \<open>distinct_mset ((mset_nodes  xs))\<close> \<open>(remove_key a xs) \<noteq> None\<close>
  shows \<open>hp_parent b (the (remove_key a xs)) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key a xs))) then None
    else if map_option node (hp_next a xs) = Some b then map_option (the o remove_key a) (hp_parent a xs)
    else map_option (the o remove_key a) (hp_parent b xs))\<close>
  using assms hp_parent_children_remove_key_children_other[of \<open>hps xs\<close> b a]
  apply (cases xs)
  apply (auto simp: in_the_default_empty_iff hp_parent_None_iff_children_None
    dest: in_find_key_children_notin_remove_key split: if_splits)
  apply (metis (no_types, lifting) in_find_key_children_notin_remove_key  node_hd_in_sum sum_image_mset_sum_map)
  apply (metis hp_parent_None_notin_same_hd hp_parent_simps_single_if in_find_key_children_notin_remove_key option.simps(2) sum_image_mset_sum_map)
  apply (smt (verit, ccfv_threshold) None_eq_map_option_iff remove_key.simps remove_key_children.elims distinct_mset_add distinct_mset_add_mset
    hd_remove_key_node_same hp.sel(1) hp_child.simps(1) hp_child_hd hp_next_children_hd_is_hd_tl hp_next_children_in_nodes2 hp_next_children_simps(2)
    hp_next_children_simps(3) hp_next_simps hp_parent_None_iff_children_None hp_parent_simps_single_if inter_iff list.simps(9) mset_nodes_simps
    node_in_mset_nodes o_apply option.collapse option.map_sel option.sel option_hd_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd
    sum_image_mset_sum_map sum_list_simps(2) sum_mset_sum_list union_single_eq_member)
  apply (simp add: hp_parent_simps_single_if; fail)
  apply (simp add: hp_parent_simps_single_if; fail)
  apply (smt (verit) find_key_children.elims remove_key.simps remove_key_children.elims find_key_none_iff hp.sel(1) hp_next_children_hd_is_hd_tl
    hp_parent_children_None_notin hp_parent_simps_single_if list.sel(1) list.sel(3) list.simps(3) map_option_eq_Some node_in_mset_nodes o_apply option.map_sel
    option.sel option_hd_def remove_key_children_hd_tl sum_image_mset_sum_map)
  apply (simp add: hp_parent_simps_single_if)
  apply (simp add: hp_parent_simps_single_if)
  done

lemma hp_prev_in_nodes: \<open>hp_prev k c\<noteq> None \<Longrightarrow> node (the (hp_prev k c)) \<in># ((mset_nodes c))\<close>
  by (induction k c rule: hp_prev.induct) (auto simp: hp_prev_children.simps(1) split: option.splits)

lemma hp_prev_children_in_nodes: \<open>hp_prev_children k c\<noteq> None \<Longrightarrow> node (the (hp_prev_children k c)) \<in># (\<Sum>\<^sub># (mset_nodes `# mset c))\<close>
  apply (induction k c rule: hp_prev_children.induct)
  subgoal for a x y children
    using hp_prev_in_nodes[of a x]
    by (auto simp: hp_prev_children.simps(1) split: option.splits)
  subgoal for a x
    using hp_prev_in_nodes[of a x]
    by (auto simp: hp_prev_children.simps(1) split: option.splits)
  subgoal by auto
  done

lemma hp_next_children_notin_end:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset (x#xs))) \<Longrightarrow> hp_next_children a xs = None \<Longrightarrow> hp_next_children a (x # xs) = (if a = node x then option_hd xs else hp_next a x)\<close>
  by (cases xs)
   (auto simp: hp_next_children.simps(1) split: option.splits)

lemma hp_next_children_remove_key_children_other:
  fixes xs :: "('b, 'a) hp list"
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_next_children b (remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key_children a xs))) then None
    else if map_option node (hp_prev_children a xs) = Some b then (hp_next_children a xs)
    else map_option (the o remove_key a) (hp_next_children b xs))\<close>
  using assms
proof (induction a xs rule: remove_key_children.induct)
    case (1 k)
    then show ?case by auto
  next
    case (2 k x n c xs)
    have dist_c_rem_y_xs: \<open>distinct_mset
     (sum_list (map mset_nodes c) +
          sum_list (map mset_nodes (remove_key_children y xs)))\<close> for y
      by (smt (verit, del_insts) "2"(4) distinct_mset_add inter_mset_empty_distrib_right mset.simps(2)
        mset_nodes.simps node_remove_key_children_in_mset_nodes subset_mset.add_diff_inverse
        sum_image_mset_sum_map sum_mset.insert union_ac(2))
    have \<open>distinct_mset
      (sum_list (map mset_nodes c) + sum_list (map mset_nodes (remove_key_children k xs)))\<close>
      \<open>x \<notin># sum_list (map mset_nodes (remove_key_children k xs))\<close>
      using 2(4) apply auto
      apply (metis distinct_mset_mono' mset_map mset_subset_eq_mono_add_left_cancel node_remove_key_children_in_mset_nodes sum_mset_sum_list)
      by (simp add: not_orig_notin_remove_key)
    moreover have \<open>distinct_mset (sum_list
      (map mset_nodes (Hp x n (remove_key_children k c) # remove_key_children k xs)))\<close>
      using 2(4) apply (auto simp: not_orig_notin_remove_key)
      by (metis calculation(1) distinct_mset_mono' mset_map node_remove_key_children_in_mset_nodes subset_mset.add_right_mono sum_mset_sum_list)
    moreover have \<open>hp_prev_children k xs \<noteq> None \<Longrightarrow> remove_key_children k xs \<noteq> []\<close>
      using 2(4) by (cases xs; cases \<open>hd xs\<close>; cases \<open>tl xs\<close>) (auto)
    moreover have \<open>x = node z \<Longrightarrow> hp_prev_children k (Hp (node z) n c # xs) = Some z \<longleftrightarrow>
      z = Hp x n c \<and> xs \<noteq> [] \<and> k = node (hd (xs))\<close> for z
      using 2(4) hp_prev_children_in_nodes[of _ c] apply -
      apply (cases \<open>xs\<close>; cases z; cases \<open>hd xs\<close>)
      using hp_prev_children_in_nodes[of _ c] apply fastforce
      apply (auto simp:  )
      apply (metis "2"(4) hp.inject hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(1) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps list.distinct(1) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl remove_key_remove_all sum_image_mset_sum_map)
      apply (metis "2"(4) hp.inject hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(1) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps in_remove_key_children_changed list.distinct(2) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl sum_image_mset_sum_map)
      by (metis "2"(4) hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps in_remove_key_children_changed list.distinct(2) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl sum_image_mset_sum_map)
    moreover have \<open>xs \<noteq> [] \<Longrightarrow> find_key_children (node (hd xs)) xs = Some (hd xs)\<close>
      by (metis find_key_children.simps(2) hp.exhaust_sel list.exhaust_sel)
    moreover have \<open>find_key_children k c = Some y \<Longrightarrow>
      option_hd (remove_key_children k xs) =
      map_option (\<lambda>a. the (remove_key k a)) (option_hd xs)\<close> for y
      using 2(4) by (cases xs; cases \<open>hd xs\<close>) auto
    moreover have \<open>find_key_children k c = Some x2 \<Longrightarrow> k \<notin># \<Sum>\<^sub># (mset_nodes `# mset xs)\<close> for x2
      by (metis (no_types, lifting) "2"(4) Un_iff add_diff_cancel_left' distinct_mset_in_diff
        find_key_noneD list.simps(9) mset_nodes.simps set_mset_union sum_image_mset_sum_map sum_list_simps(2))
    moreover have \<open>k \<notin># sum_list (map mset_nodes xs) \<Longrightarrow> k \<noteq> x \<Longrightarrow>
      \<forall>za. hp_prev_children k (Hp x n c # xs) = Some za \<longrightarrow> node za \<noteq> node z \<Longrightarrow>
      hp_prev_children k c = Some z \<Longrightarrow> hp_next_children (node z) (Hp x n (remove_key_children k c) # xs) =
      map_option (\<lambda>a. the (remove_key k a)) (hp_next_children (node z) (Hp x n c # xs))\<close> for z
      by (metis hp_prev_children_None_notin hp_prev_children_first_child option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    moreover have \<open>find_key_children k c = Some x2 \<Longrightarrow>
      b \<in># mset_nodes x2 \<Longrightarrow>
      b\<notin># \<Sum>\<^sub># (mset_nodes `# mset (Hp x n (remove_key_children k c) # xs))\<close> for x2
      by (smt (verit, ccfv_threshold) "2"(4) add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff
        find_key_noneD find_key_none_iff in_find_key_children_notin_remove_key mset.simps(2)
        mset_left_cancel_union mset_nodes.simps mset_nodes_find_key_children_subset mset_subset_eqD
        mset_subset_eq_add_right option.sel sum_mset.insert)
    moreover have \<open> find_key_children k c = Some x2 \<Longrightarrow> k \<noteq> x \<Longrightarrow> k \<in># sum_list (map mset_nodes c)\<close> for x2
      by (metis find_key_none_iff option.distinct(1) sum_image_mset_sum_map)
    moreover have [simp]: \<open>z \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_next_children (z) xs = None\<close> for z
      using "2.prems" distinct_mset_in_diff by fastforce
    moreover have \<open>\<forall>z. hp_prev_children k (Hp x n c # xs) = Some z \<longrightarrow> node z \<noteq> x \<Longrightarrow>
      xs = [] \<or> (xs \<noteq> [] \<and> node (hd xs) \<noteq> k)\<close>
      by (smt (verit, ccfv_SIG) remove_key.simps remove_key_children.elims hp.sel(1)
        hp_prev_children_simps(1) list.sel(1) list.simps(3) option.map(1) option.map(2) option.sel
        option_hd_Nil option_hd_Some_hd)
    moreover have \<open>xs \<noteq> [] \<Longrightarrow> node (hd xs) \<noteq> k \<Longrightarrow> remove_key_children k xs \<noteq> []\<close> and
      [simp]: \<open>xs \<noteq> [] \<Longrightarrow> node (hd xs) \<noteq> k \<Longrightarrow> hd (remove_key_children k xs) = the (remove_key k (hd xs))\<close>
      \<open>xs \<noteq> [] \<Longrightarrow> node (hd xs) \<noteq> k \<Longrightarrow> k \<notin># sum_list (map mset_nodes c) \<Longrightarrow> hp_prev_children k (Hp x n c # xs) = Some z \<longleftrightarrow> hp_prev_children k (xs) =Some z\<close>
      \<open>k \<notin># sum_list (map mset_nodes xs) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> the (remove_key k (hd xs)) = hd xs\<close>
      for z
      by (cases xs; cases \<open>hd xs\<close>; auto; fail)+
    moreover have\<open>mset_nodes y \<subseteq># sum_list (map mset_nodes xs)⟹
      distinct_mset (sum_list (map mset_nodes c) + sum_list (map mset_nodes xs)) \<Longrightarrow> b \<in># mset_nodes y \<Longrightarrow>
      b \<notin># (sum_list (map mset_nodes c))\<close> for y :: "('b, 'a) hp"
      by (metis (no_types, lifting) add_diff_cancel_right' distinct_mset_in_diff mset_subset_eqD)
    moreover have \<open>hp_prev_children k xs = Some z \<Longrightarrow> hp_next_children (node z) c = None\<close> for z
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
      by (metis "2.prems" disjunct_not_in dist_c_rem_y_xs distinct_mset_add hp_next_children_None_notin
        hp_prev_children_in_nodes list.sel(3) list.simps(3) option.sel option.simps(2) remove_key_children_hd_tl sum_image_mset_sum_map)
    ultimately show ?case
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>] 2
        find_key_children_None_or_itself[of k c] find_key_children_None_or_itself[of k xs] hp_prev_children_in_nodes[of b c]
        hp_prev_children_in_nodes[of k c] mset_nodes_find_key_children_subset[of k xs]
      supply [simp del] = find_key_children_None_or_itself
      apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl comp_def
        in_the_default_empty_iff)
      apply (simp add: disjunct_not_in distinct_mset_add)
      apply (auto simp: hp_next_children_simps_if remove_key_children_hd_tl
        dist_c_rem_y_xs hp_next_children_notin_end
        hp_next_children_hd_is_hd_tl
        split: option.splits)
      by (metis (no_types, lifting) "2.prems" remove_key_children.simps(1)
        hp_prev_children_None_notin hp_prev_children_skip_Cons hp_prev_in_nodes hp_prev_skip_hd_children
        list.exhaust_sel mset.simps(2) node_in_mset_nodes option.map_sel option.sel option_last_Nil
        option_last_Some_iff(2) remove_key_children_hd_tl remove_key_remove_all sum_image_mset_sum_map sum_mset.insert union_commute)
qed

lemma hp_next_remove_key_other:
  assumes \<open>distinct_mset (mset_nodes xs)\<close> \<open>remove_key a xs \<noteq> None\<close>
  shows \<open>hp_next b (the (remove_key a xs)) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key a xs))) then None
    else if map_option node (hp_prev a xs) = Some b then (hp_next a xs)
    else map_option (the o remove_key a) (hp_next b xs))\<close>
  using hp_next_children_remove_key_children_other[of \<open>hps xs\<close> b a] assms
  by (cases xs) (auto)


lemma hp_prev_children_cons_if:
  \<open>hp_prev_children b (a # xs) = (if map_option node (option_hd xs) = Some b then Some a
    else (case hp_prev_children b (hps a) of None \<Rightarrow> hp_prev_children b xs | Some a \<Rightarrow> Some a))\<close>
  apply (cases xs)
  apply (auto split: option.splits simp: hp_prev_children.simps(1))
  apply (metis hp.collapse hp_prev_simps)
  apply (metis hp.exhaust_sel hp_prev_simps)
  apply (metis hp.exhaust_sel hp_prev_simps option.simps(2))
  apply (metis hp.exhaust_sel hp_prev_simps option.simps(2))
  by (metis hp.exhaust_sel hp_prev_simps the_default.simps(1))


lemma hp_prev_children_remove_key_children_other:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_prev_children b (remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key_children a xs))) then None
    else if map_option node (hp_next_children a xs) = Some b then (hp_prev_children a xs)
    else map_option (the o remove_key a) (hp_prev_children b xs))\<close>
  using assms
proof (induction a xs rule: remove_key_children.induct)
    case (1 k)
    then show ?case by auto
  next
    case (2 k x n c xs)
    have find_None_not_other: \<open>find_key_children k c \<noteq> None \<Longrightarrow> find_key_children k xs = None\<close>
       \<open>find_key_children k xs \<noteq> None \<Longrightarrow> find_key_children k c = None\<close>
      using "2"(4) distinct_mset_in_diff apply fastforce
      using "2"(4) distinct_mset_in_diff by fastforce

    have [simp]: \<open>remove_key_children k xs \<noteq> [] \<Longrightarrow> xs \<noteq> []\<close>
      by auto

    have [simp]: \<open>hp_prev_children (node (hd xs)) xs = None\<close>
      using 2(4)
      by (cases xs; cases "hd xs"; cases "tl xs")
        auto
    have remove_key_children_empty_iff: \<open>(remove_key_children k xs = []) = (\<forall>x. x \<in> set xs \<longrightarrow> node x = k)\<close>
      by (auto simp: VSIDS_remove_key_children_alt_def filter_empty_conv)
    have [simp]: \<open>find_key_children k c = Some x2 \<Longrightarrow> remove_key_children k xs = xs\<close> for x2
      by (metis \<open>find_key_children k c \<noteq> None \<Longrightarrow> find_key_children k xs = None\<close> find_key_none_iff option.distinct(1) remove_key_children_notin_unchanged sum_image_mset_sum_map)

    have dist: \<open>distinct_mset
      (sum_list (map mset_nodes c) + sum_list (map mset_nodes (remove_key_children k xs)))\<close>
      \<open>x \<notin># sum_list (map mset_nodes (remove_key_children k xs))\<close>
      using 2(4) apply auto
      apply (metis distinct_mset_mono' mset_map mset_subset_eq_mono_add_left_cancel node_remove_key_children_in_mset_nodes sum_mset_sum_list)
      by (simp add: not_orig_notin_remove_key)
    moreover have \<open>distinct_mset
    (sum_list
      (map mset_nodes (Hp x n (remove_key_children k c) # remove_key_children k xs)))\<close>
      \<open>distinct_mset (sum_list (map mset_nodes (remove_key_children k xs)))\<close>
      using 2(4) apply (auto simp: not_orig_notin_remove_key)
      apply (metis dist(1) distinct_mset_mono' mset_map node_remove_key_children_in_mset_nodes subset_mset.add_right_mono sum_mset_sum_list)
      using WB_List_More.distinct_mset_union2 calculation by blast
    moreover have \<open>hp_next_children k xs \<noteq> None \<Longrightarrow> remove_key_children k xs \<noteq> []\<close>
      using 2(4) by (cases xs; cases \<open>hd xs\<close>; cases \<open>tl xs\<close>) (auto)
    moreover have \<open>xs \<noteq> [] \<Longrightarrow> find_key_children (node (hd xs)) xs = Some (hd xs)\<close>
      by (metis find_key_children.simps(2) hp.exhaust_sel list.exhaust_sel)
    moreover have [simp]: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset a)) \<Longrightarrow> hp_prev_children (node (hd a)) a = None\<close> for a
      by (cases \<open>(node (hd a), a)\<close> rule: hp_prev_children.cases; cases \<open>hd a\<close>)
       (auto simp: hp_prev_children.simps(1) split: option.splits)
    moreover have
      \<open>remove_key_children k xs \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd (remove_key_children k xs))) (remove_key_children k c) = None\<close>
      \<open>xs \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd xs)) (remove_key_children k c) = None\<close>
      apply (metis dist(1) disjunct_not_in distinct_mset_add hp_prev_children_None_notin node_hd_in_sum not_orig_notin_remove_key sum_image_mset_sum_map)
      by (smt (verit, ccfv_threshold) remove_key_children.elims add_diff_cancel_right' dist(1) distinct_mem_diff_mset hp.sel(1)
        hp_prev_children_None_notin list.distinct(2) list.sel(1) mset_subset_eqD node_hd_in_sum node_remove_key_children_in_mset_nodes remove_key_remove_all sum_image_mset_sum_map)
    have \<open>hp_next_children k c = Some z \<Longrightarrow>
    hp_prev_children (node z) (Hp x n (remove_key_children k c) # remove_key_children k xs) =
      hp_prev_children (node z) (remove_key_children k c)\<close> for z
      apply (auto simp: hp_prev_children_cons_if split: option.splits simp del: )
      apply (metis add_diff_cancel_right' calculation(1) distinct_mset_in_diff hp_next_children_in_nodes2 node_hd_in_sum sum_image_mset_sum_map)
      apply (metis add_diff_cancel_right' calculation(1) distinct_mset_in_diff hp_next_children_in_nodes2 hp_prev_children_None_notin sum_image_mset_sum_map)
      by (metis \<open>remove_key_children k xs \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd (remove_key_children k xs))) (remove_key_children k c) = None\<close> option.simps(2))
    moreover have \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_prev_children b xs = None\<close> for b
      by (metis (no_types, lifting) "2"(4) add_diff_cancel_left' distinct_mset_add distinct_mset_in_diff hp_prev_children_None_notin list.map(2) mset_nodes_simps sum_image_mset_sum_map sum_list.Cons)

    moreover have \<open>find_key_children k c \<noteq> None \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> node (hd xs) \<notin># mset_nodes (the (find_key_children k c))\<close>
      by (metis (no_types, opaque_lifting) \<open>\<And>x2. find_key_children k c = Some x2 \<Longrightarrow> remove_key_children k xs = xs\<close>
        add_diff_cancel_right' calculation(1) calculation(6) distinct_mset_in_diff mset_nodes_find_key_children_subset
        mset_subset_eqD node_in_mset_nodes option.distinct(1) option.exhaust_sel option.sel sum_image_mset_sum_map)
    ultimately show ?case
      supply [[goals_limit=1]]
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>] 2
      apply (simp_all add: remove_key_children_hd_tl split: option.splits if_splits)
      apply (intro conjI impI allI)
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
        done
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
          by (metis (mono_tags, lifting) fun_comp_eq_conv hp_prev_children.simps(2) hp_prev_children.simps(3) hp_prev_children_None_notin hp_prev_children_simps(3) hp_prev_simps list.collapse sum_image_mset_sum_map)
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
     	  apply (smt (z3) pass\<^sub>2.cases add_diff_cancel_left' distinct_mset_in_diff find_key_none_iff hp_next_children_None_notin hp_prev_None_notin_children hp_prev_children_simps(3) in_find_key_children_notin_remove_key in_the_default_empty_iff list.sel(1) mset_nodes_find_key_children_subset mset_subset_eqD node_hd_in_sum option.exhaust_sel option.map_sel option_last_Some_iff(2) sum_image_mset_sum_map)
        done
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
          apply (simp add: hp_prev_children_cons_if)
          apply (intro conjI impI)
        apply (metis (no_types, lifting) remove_key_children.simps(1) WB_List_More.distinct_mset_mono add_diff_cancel_left' distinct_mset_in_diff hd_remove_key_node_same
          hp.exhaust_sel hp_next_children_in_nodes2 hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps list.exhaust_sel mset_nodes_simps
          mset_nodes_find_key_children_subset option.sel option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_remove_all sum_image_mset_sum_map
          union_single_eq_member)
          apply (simp add: hp_prev_children_cons_if split: option.splits if_splits)
          apply (metis \<open>remove_key_children k xs \<noteq> [] \<Longrightarrow> xs \<noteq> []\<close> hp_next_children_hd_is_hd_tl option_hd_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
          by (metis add_diff_cancel_right' distinct_mset_in_diff hp_next_children_in_nodes2 hp_prev_children_None_notin option.case_eq_if sum_image_mset_sum_map)
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
        apply (auto simp: hp_prev_children_cons_if split: option.splits if_splits)[]
        apply (metis (no_types, lifting) None_eq_map_option_iff in_find_key_children_notin_remove_key in_the_default_empty_iff node_hd_in_sum option.exhaust_sel option.map_sel sum_image_mset_sum_map)
        apply (metis (no_types, lifting) distinct_mset_add hp_prev_children_None_notin in_the_default_empty_iff inter_iff map_option_is_None mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel option_last_Nil option_last_Some_iff(1) sum_mset_sum_list the_default.simps(2))
        by (metis (no_types, lifting) None_eq_map_option_iff add_diff_cancel_right' distinct_mset_in_diff hp_prev_children_None_notin in_the_default_empty_iff mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)+
      subgoal
        apply (auto split: option.splits if_splits simp: remove_key_children_empty_iff remove_key_children_hd_tl)
        apply (auto simp: hp_prev_children_cons_if hd_remove_key_node_same' remove_key_children_empty_iff comp_def split: option.splits if_splits)[]
        apply (metis list.set_sel(1) node_in_mset_nodes)
        apply (smt (verit, best) Nil_is_map_conv VSIDS_remove_key_children_alt_def filter_empty_conv hd_in_set hd_remove_key_node_same' node_in_mset_nodes option.map(2) the_default.simps(1))
        apply (metis hd_remove_key_node_same hp_next_children_hd_is_hd_tl option_hd_Some_iff(2) remove_key_children_empty_iff remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
        apply (metis \<open>xs \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd xs)) (remove_key_children k c) = None\<close> option.distinct(1) remove_key_children_notin_unchanged)
        by (metis \<open>remove_key_children k xs \<noteq> [] \<Longrightarrow> hp_prev_children (node (hd (remove_key_children k xs))) (remove_key_children k c) = None\<close> option.distinct(1) remove_key_children_empty_iff remove_key_children_notin_unchanged)
      subgoal
        by (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
      subgoal
        by (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
      subgoal
        using find_None_not_other
        by (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
      subgoal
        using find_None_not_other find_key_noneD[of k c]
        by (auto split: option.splits if_splits simp: remove_key_children_hd_tl)
      subgoal
        using find_None_not_other
        apply (cases \<open>k \<in># sum_list (map mset_nodes c)\<close>)
        apply (auto split: option.splits if_split simp: comp_def remove_key_children_hd_tl)
        apply (auto simp: hp_prev_children_cons_if dest: mset_nodes_find_key_children_subset split: option.splits if_splits)[]
        apply (metis mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(1) sum_mset_sum_list)
        done
      subgoal
        using find_None_not_other
        apply (auto split: option.splits if_splits
          simp: hp_prev_children_cons_if comp_def remove_key_children_hd_tl)
        done
      done
qed

lemma hp_prev_remove_key_other:
  assumes \<open>distinct_mset (mset_nodes xs)\<close> \<open>remove_key a xs \<noteq> None\<close>
  shows \<open>hp_prev b (the (remove_key a xs)) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key a xs))) then None
    else if map_option node (hp_next a xs) = Some b then (hp_prev a xs)
    else map_option (the o remove_key a) (hp_prev b xs))\<close>
  using assms hp_prev_children_remove_key_children_other[of \<open>hps xs\<close> b a]
  by (cases xs) auto

lemma hp_next_find_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset h)) \<Longrightarrow> find_key_children a h \<noteq> None ⟹
  x \<in># mset_nodes (the (find_key_children a h)) \<Longrightarrow> x \<noteq>a \<Longrightarrow>
  hp_next x (the (find_key_children a h)) = hp_next_children x h\<close>
  apply (induction a h arbitrary: x rule: find_key_children.induct)
  subgoal
    by auto
  subgoal for k xa n c xs y
    apply (auto simp: split: option.splits)
    apply (metis add_diff_cancel_left' distinct_mem_diff_mset hp_next_children_append2)
    apply (metis disjunct_not_in distinct_mset_add find_key_noneD find_key_none_iff hp.sel(1)
      hp_next_None_notin_children hp_next_children_simps(3) mset_map mset_nodes_find_key_children_subset
      mset_subset_eqD option.sel sum_mset_sum_list)
    by (metis (no_types, lifting) add_diff_cancel_left' distinct_mset_add distinct_mset_in_diff
      find_key_noneD find_key_none_iff hp_next_children_append2 mset_nodes_find_key_children_subset
      mset_subset_eqD option.sel sum_image_mset_sum_map)
  done

lemma hp_next_find_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  find_key a h \<noteq> None ⟹ x \<in># mset_nodes (the (find_key a h)) \<Longrightarrow> x \<noteq>a \<Longrightarrow>
  hp_next x (the (find_key a h)) = hp_next x h\<close>
  using hp_next_find_key_children[of \<open>hps h\<close> a x]
  by (cases \<open>(a,h)\<close> rule: find_key.cases;
    cases \<open>a \<in># sum_list (map mset_nodes (hps h))\<close>)
   clarsimp_all

lemma hp_next_find_key_itself:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow> (find_key a h) \<noteq> None \<Longrightarrow> hp_next a (the (find_key a h)) = None\<close>
  using find_key_None_or_itself[of a h]
  apply (cases \<open>find_key a h\<close>)
  apply auto
  by (metis add_diff_cancel_left' distinct_mset_add_mset distinct_mset_in_diff distinct_mset_mono'
    hp.exhaust_sel hp_next_None_notin_children mset_nodes_simps mset_nodes_find_key_subset option.sel
    option.simps(2) sum_mset_sum_list union_mset_add_mset_left)


lemma hp_prev_find_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset h)) \<Longrightarrow> find_key_children a h \<noteq> None ⟹
  x \<in># mset_nodes (the (find_key_children a h)) \<Longrightarrow> x \<noteq>a \<Longrightarrow>
  hp_prev x (the (find_key_children a h)) = hp_prev_children x h\<close>
  apply (induction a h arbitrary: x rule: find_key_children.induct)
  subgoal
    by auto
  subgoal for k xa n c xs y
    apply (auto simp: split: option.splits)
    apply (simp add: disjunct_not_in distinct_mset_add)
    apply (smt (verit, ccfv_SIG) find_key_children.elims remove_key_children.simps(2) WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mem_diff_mset find_key_noneD hp.sel(1) hp_prev_None_notin_children hp_prev_children_simps(3) in_find_key_children_notin_remove_key list.distinct(2) list.sel(1) mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    by (metis (no_types, lifting) disjunct_not_in distinct_mset_add find_key_noneD find_key_none_iff hp_prev_children_first_child mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_image_mset_sum_map)
  done

lemma hp_prev_find_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  find_key a h \<noteq> None ⟹ x \<in># mset_nodes (the (find_key a h)) \<Longrightarrow> x \<noteq>a \<Longrightarrow>
  hp_prev x (the (find_key a h)) = hp_prev x h\<close>
  using hp_prev_find_key_children[of \<open>hps h\<close> a x]
  by (cases \<open>(a,h)\<close> rule: find_key.cases;
    cases \<open>a \<in># sum_list (map mset_nodes (hps h))\<close>)
   clarsimp_all

lemma hp_prev_find_key_itself:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow> (find_key a h) \<noteq> None \<Longrightarrow> hp_prev a (the (find_key a h)) = None\<close>
  using find_key_None_or_itself[of a h]
  apply (cases \<open>find_key a h\<close>)
  apply auto
  by (metis add_diff_cancel_left' distinct_mset_add_mset distinct_mset_in_diff distinct_mset_mono'
    hp.exhaust_sel hp_prev_None_notin_children mset_nodes_simps mset_nodes_find_key_subset option.sel
    option.simps(2) sum_mset_sum_list union_mset_add_mset_left)

lemma (in pairing_heap_assms) hp_child_find_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset h)) \<Longrightarrow> find_key_children a h \<noteq> None ⟹
  x \<in># mset_nodes (the (find_key_children a h)) \<Longrightarrow>
  hp_child x (the (find_key_children a h)) = hp_child_children x h\<close>
  apply (induction a h arbitrary: x rule: find_key_children.induct)
  subgoal
    by auto
  subgoal for k xa n c xs y
    apply (auto simp: hp_child_children_Cons_if split: option.splits)
    using distinct_mem_diff_mset apply fastforce
    apply (metis Groups.add_ac(2) distinct_mset_union find_key_none_iff option.simps(2) sum_image_mset_sum_map)
    apply (metis disjunct_not_in distinct_mset_add hp_child_None_notin_children if_Some_None_eq_None mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_mset_sum_list)
      apply (metis distinct_mset_union find_key_noneD hp_child_children_None_notin hp_child_children_skip_first hp_child_children_skip_last
        hp_child_hp_children_simps2 mset_map mset_subset_eqD option.sel find_key_none_iff mset_nodes_find_key_children_subset
        sum_mset_sum_list)
     by (metis (no_types, lifting) distinct_mset_add find_key_noneD find_key_none_iff hp_child_hp_children_simps2
      mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_image_mset_sum_map)
  done

lemma (in pairing_heap_assms) hp_child_find_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  find_key a h \<noteq> None ⟹ x \<in># mset_nodes (the (find_key a h)) \<Longrightarrow>
  hp_child x (the (find_key a h)) = hp_child x h\<close>
  using hp_child_find_key_children[of \<open>hps h\<close> a x]
  apply (cases \<open>(a,h)\<close> rule: find_key.cases;
    cases \<open>a \<in># sum_list (map mset_nodes (hps h))\<close>)
  apply clarsimp_all
  by (metis find_key_none_iff hp_child_hp_children_simps2 mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_image_mset_sum_map)+

lemma (in pairing_heap_assms) find_remove_children_mset_nodes_full:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset h)) \<Longrightarrow>  find_key_children a h = Some x \<Longrightarrow>
  (\<Sum>\<^sub># (mset_nodes `# mset (remove_key_children a h))) + mset_nodes x = \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  apply (induction a h rule: find_key_children.induct)
  apply (auto split: if_splits option.splits)
  using distinct_mset_add apply blast
    by (metis (no_types, lifting) disjunct_not_in distinct_mset_add find_key_noneD remove_key_children_notin_unchanged sum_image_mset_sum_map union_assoc union_commute)

lemma (in pairing_heap_assms) find_remove_mset_nodes_full:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  remove_key a h = Some y \<Longrightarrow>
  find_key a h = Some ya \<Longrightarrow>  (mset_nodes y + mset_nodes ya) = mset_nodes h\<close>
  apply (induction a h rule: remove_key.induct)
  subgoal for k x n c
    using find_remove_children_mset_nodes_full[of c k ya]
    by (auto split: if_splits)
  done

lemma in_remove_key_in_nodes: \<open>remove_key a h \<noteq> None \<Longrightarrow> x' \<in># mset_nodes (the (remove_key a h)) \<Longrightarrow> x' \<in># mset_nodes h\<close>
  by (metis remove_key.simps hp.exhaust_sel mset_nodes.simps not_orig_notin_remove_key option.sel sum_image_mset_sum_map union_iff)

lemma in_find_key_in_nodes: \<open>find_key a h \<noteq> None \<Longrightarrow> x' \<in># mset_nodes (the (find_key a h)) \<Longrightarrow> x' \<in># mset_nodes h\<close>
  by (meson mset_nodes_find_key_subset mset_subset_eqD)

lemma in_find_key_notin_remove_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset h)) \<Longrightarrow> find_key_children a h \<noteq> None \<Longrightarrow> x \<in># mset_nodes (the (find_key_children a h))\<Longrightarrow> x \<notin># \<Sum>\<^sub># (mset_nodes `# mset (remove_key_children a h))\<close>
  apply (induction a h rule: find_key_children.induct)
  subgoal
    by (auto split: if_splits)
  subgoal for k xa n c xs
          using distinct_mset_union[of \<open>sum_list (map mset_nodes c)\<close> \<open>sum_list (map mset_nodes xs)\<close>]
        distinct_mset_union[of \<open>sum_list (map mset_nodes c)\<close> \<open>sum_list (map mset_nodes xs)\<close> ]

    apply (auto 4 3 simp: remove_key_remove_all[simplified] ac_simps dest: find_key_noneD multi_member_split split: option.splits)
    apply (metis find_key_noneD find_key_none_iff mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_image_mset_sum_map)
    apply (metis add_diff_cancel_left' distinct_mset_in_diff mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(1) option.sel sum_image_mset_sum_map)
    apply (metis distinct_mset_union find_key_none_iff option.distinct(1) sum_image_mset_sum_map union_commute)
    apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(2) sum_image_mset_sum_map)
    apply (metis find_key_none_iff option.simps(2) sum_image_mset_sum_map)
    by (metis add_diff_cancel_right' distinct_mset_in_diff mset_nodes_find_key_children_subset mset_subset_eqD not_orig_notin_remove_key option.sel option.simps(2) sum_image_mset_sum_map)
  done

lemma in_find_key_notin_remove_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow> find_key a h \<noteq> None \<Longrightarrow> remove_key a h \<noteq> None \<Longrightarrow> x \<in># mset_nodes (the (find_key a h))\<Longrightarrow> x \<notin># mset_nodes (the (remove_key a h))\<close>
  using in_find_key_notin_remove_key_children[of \<open>hps h\<close> a x]
  apply (cases h)
  apply auto
  apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
  by fastforce

lemma map_option_node_hp_next_remove_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  map_option node (hp_prev a h) \<noteq> Some x' \<Longrightarrow> map_option node (hp_next x' h) =
  map_option (\<lambda>x. node (the (remove_key a x))) (hp_next x' h)\<close>
  apply (induction x' h rule:hp_next.induct)
  subgoal for aa m s x y children
    apply (auto simp: split: option.splits)
    by (smt (z3) remove_key.simps add_mset_add_single distinct_mset_add_mset distinct_mset_union hp.exhaust_sel hp.sel(1) hp_next_children_simps(1-3)
      hp_prev_None_notin_children hp_prev_children_None_notin hp_prev_children_simps(1) hp_prev_in_first_child hp_prev_skip_hd_children list.map(2) list.sel(1)
      map_option_cong member_add_mset mset_nodes.simps option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map sum_list_simps(2) union_ac(2))
  subgoal by auto
  subgoal by auto
  done

lemma has_prev_still_in_remove_key: \<open>distinct_mset (mset_nodes h) \<Longrightarrow> hp_prev a h \<noteq> None \<Longrightarrow> 
  remove_key a h \<noteq> None \<Longrightarrow> node (the (hp_prev a h)) \<in># mset_nodes (the (remove_key a h))\<close>
  apply (induction a h rule: hp_prev.induct)
  subgoal for a m s x y children
    apply (cases x)
    apply (auto simp: hp_prev_children.simps(1) split: option.splits)
    using Duplicate_Free_Multiset.distinct_mset_union2 apply blast
    using distinct_mset_add by blast
  subgoal apply auto
    by (smt (verit, del_insts) remove_key.simps remove_key_children.elims
      add_diff_cancel_left' distinct_mset_add_mset hp_prev_children_None_notin hp_prev_simps
      insert_DiffM list.distinct(2) list.sel(1) list.simps(9) mset_nodes.simps option.sel
      option_last_Nil option_last_Some_iff(2) sum_list_simps(2) union_iff)
  subgoal by auto
  done
lemma find_key_head_node_iff: \<open>node h = node m' \<Longrightarrow> find_key (node m') h = Some m' \<longleftrightarrow> h = m'\<close>
  by (cases h) auto

lemma map_option_node_hp_prev_remove_key:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  map_option node (hp_next a h) \<noteq> Some x' \<Longrightarrow> map_option node (hp_prev x' h) =
  map_option (\<lambda>x. node (the (remove_key a x))) (hp_prev x' h)\<close>
  apply (induction x' h rule:hp_prev.induct)
  subgoal for aa m s x y children
    apply (auto simp: hp_prev_children.simps(1) split: option.splits)
    apply (metis remove_key.simps hp.exhaust_sel hp.sel(1) hp_next_children_simps(1) option.sel)
    apply (metis add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff hp_next_None_notin hp_next_children_None_notin hp_next_children_simps(3) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map union_ac(2))
    apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp_prev_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
    by (metis distinct_mset_add find_key_head_node_iff hp_next_children_simps(2) hp_next_find_key_itself option.distinct(1) option.sel)
  subgoal by auto
  subgoal by auto
  done

lemma \<open>distinct_mset (mset_nodes h) \<Longrightarrow> node y \<in># mset_nodes h \<Longrightarrow> find_key (node y) h = Some y\<Longrightarrow>
  mset_nodes (the (find_key (node y) h)) = mset_nodes y\<close>
  apply (induction \<open>node y\<close> h rule: find_key.induct)
  apply auto
  oops

lemma distinct_mset_find_node_next:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow> find_key n h = Some y \<Longrightarrow>
  distinct_mset (mset_nodes y + (if hp_next n h = None then {#} else (mset_nodes (the (hp_next n h)))))\<close>
  apply (induction n h rule: hp_next.induct)
  subgoal for a m s x ya children
    apply (cases x)
    apply (auto simp: hp_next_children.simps(1)
      split: if_splits option.splits)
    apply (metis distinct_mset_union union_ac(1))
    using distinct_mset_add apply blast
    using distinct_mset_add apply blast
    using distinct_mset_add apply blast
    apply (metis (no_types, opaque_lifting) add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff find_key_noneD hp_next_None_notin hp_next_children_None_notin hp_next_children_simps(3) node_in_mset_nodes option.simps(2) sum_image_mset_sum_map union_lcomm)
    using distinct_mset_add by blast
  subgoal apply (auto simp: hp_next_children.simps(1)
      split: if_splits option.splits)
    apply (metis (no_types, opaque_lifting) remove_key_children.simps(1) WB_List_More.distinct_mset_mono arith_extra_simps(5) ex_Melem_conv list.simps(9) mset_nodes_find_key_children_subset option.distinct(2) option.sel remove_key_remove_all sum_image_mset_sum_map sum_list_simps(2) union_ac(2))
    by (smt (verit, del_insts) find_key.simps find_key_children.elims find_key_children.simps(1) list_tail_coinc option.case_eq_if option.collapse option.discI)
  subgoal
    by (auto simp: split: if_splits)
  done

lemma hp_child_node_itself[simp]: \<open>hp_child (node a) a = option_hd (hps a)\<close>
  by (cases a; auto)

lemma VSIDS_find_key_children_itself_hd[simp]:
  \<open>find_key_children (node a) [a]  = Some a\<close>
  by (cases a; auto)

lemma hp_prev_and_next_same_node:
  fixes y  h :: \<open>('b, 'a) hp\<close>
  assumes \<open>distinct_mset (mset_nodes h)\<close> \<open>hp_prev x' y \<noteq> None\<close>
    \<open>node yb = x'\<close>
    \<open>hp_next (node y) h = Some yb\<close>
    \<open>find_key (node y) h = Some y\<close>
  shows \<open>False\<close>
proof -
  have x'y: \<open>x' \<in># mset_nodes y\<close>
    by (metis assms(2) hp_prev_None_notin)
  have \<open>x' \<noteq> node y\<close>
    using assms(1,2) by (metis assms(3) assms(4) hp_next_not_same_node)
  have \<open>remove_key (node y) h \<noteq> None\<close>
    by (metis remove_key_None_iff find_key_head_node_iff handy_if_lemma hp_next_find_key_itself option.sel assms(1,4))
  moreover have neq: \<open>find_key (node y) h \<noteq> None\<close>
    by (metis find_key.elims find_key_none_iff hp_next_children_None_notin hp_next_simps option.discI assms(4))
  ultimately have \<open>node (the (hp_next (node y) h)) \<noteq> x'\<close>
    using hp_next_remove_key_other[of h \<open>node y\<close> x']
      distinct_mset_find_node_next[of h \<open>node y\<close>] assms
    by (cases yb) auto
  then show False
    using assms by (auto split: if_splits simp: )
qed

lemma hp_child_children_remove_is_remove_hp_child_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow>
   hp_child_children b (c) \<noteq> None \<Longrightarrow>
   hp_parent_children k (c) = None \<Longrightarrow>
    hp_child_children b ((remove_key_children k c)) \<noteq> None \<Longrightarrow>
    (hp_child_children b (remove_key_children k c)) = (remove_key k (the (hp_child_children b (c))))\<close>
  apply (induction k c rule: remove_key_children.induct)
  subgoal by auto
  subgoal for k x n c xs
    using distinct_mset_union[of \<open>sum_list (map mset_nodes c)\<close> \<open>sum_list (map mset_nodes xs)\<close>]
    apply auto
    apply (metis disjunct_not_in distinct_mset_add hp_child_None_notin_children hp_child_children_None_notin hp_child_children_simps(2) option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (auto simp: hp_parent_children_cons split: option.splits)
    by (smt (verit) remove_key.simps remove_key_children.elims disjunct_set_mset_diff distinct_mset_add
        distinct_mset_in_diff hp.sel(1) hp_child_children_Cons_if hp_child_children_None_notin hp_child_hd hp_child_hp_children_simps2
        hp_parent_None_iff_children_None list.sel(1) mset_subset_eqD node_remove_key_children_in_mset_nodes option.sel option_hd_Some_iff(2) sum_image_mset_sum_map)
  done

lemma hp_child_remove_is_remove_hp_child:
  \<open>distinct_mset (mset_nodes (Hp x n c)) \<Longrightarrow>
   hp_child b (Hp x n c) \<noteq> None \<Longrightarrow>
   hp_parent k (Hp x n c) = None \<Longrightarrow>
  remove_key k (Hp x n c) \<noteq> None \<Longrightarrow>
    hp_child b (the (remove_key k (Hp x n c))) \<noteq> None \<Longrightarrow>
    hp_child b (the (remove_key k (Hp x n c))) = remove_key k (the (hp_child b (Hp x n c)))\<close>
  using hp_child_children_remove_is_remove_hp_child_children[of c b k]
  apply auto
  by (smt (z3) remove_key.elims remove_key_children.elims hp.exhaust_sel hp.inject hp_child_hd
    hp_child_hp_children_simps2 hp_parent_None_iff_children_None list.sel(1) option.sel option_hd_Some_iff(2))


lemma VSIDS_remove_key_children_itself_hd[simp]: \<open>distinct_mset (mset_nodes a + sum_list (map mset_nodes list)) \<Longrightarrow>
    remove_key_children (node a) (a # list) = list\<close>
  by (cases a; auto)

lemma hp_child_children_remove_key_children_other_helper:
  assumes
    K: ‹hp_child_children b (remove_key_children k c) = map_option ((the \<circ>\<circ> remove_key) k) (hp_child_children b c)\<close> and
    H: \<open>node x2a \<noteq> b\<close>
    \<open>hp_parent k (Hp x n c) = Some x2a\<close>
    \<open>hp_child b (Hp x n c) = Some y\<close>
    \<open>hp_child b (Hp x n (remove_key_children k c)) = Some ya\<close>
  shows
    \<open>ya = the (remove_key k y)\<close>
  using  K H
  apply (cases c; cases y)
  apply (auto split: option.splits if_splits)
  apply (metis get_min2.simps get_min2_alt_def hp_parent_simps(1))
  by (metis get_min2.simps get_min2_alt_def hp_parent_simps(1))

lemma hp_child_children_remove_key_children_other:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_child_children b (remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key_children a xs))) then None
    else if map_option node (hp_parent_children a xs) = Some b then (hp_next_children a xs)
    else map_option (the o remove_key a) (hp_child_children b xs))\<close>
  using assms
proof (induction a xs rule: remove_key_children.induct)
    case (1 k)
    then show ?case by auto
  next
    case (2 k x n c xs)
    moreover have \<open>distinct_mset
      (sum_list (map mset_nodes c) + sum_list (map mset_nodes (remove_key_children k xs)))\<close>
      \<open>x \<notin># sum_list (map mset_nodes (remove_key_children k xs))\<close>
      using 2(4) apply auto
      apply (metis distinct_mset_mono' mset_map mset_subset_eq_mono_add_left_cancel node_remove_key_children_in_mset_nodes sum_mset_sum_list)
      by (simp add: not_orig_notin_remove_key)
    moreover have \<open>distinct_mset
    (sum_list
      (map mset_nodes (Hp x n (remove_key_children k c) # remove_key_children k xs)))\<close>
      using 2(4) apply (auto simp: not_orig_notin_remove_key)
      by (metis calculation(5) distinct_mset_mono' mset_map node_remove_key_children_in_mset_nodes subset_mset.add_right_mono sum_mset_sum_list)
    moreover have \<open>hp_prev_children k xs \<noteq> None \<Longrightarrow> remove_key_children k xs \<noteq> []\<close>
      using 2(4) by (cases xs; cases \<open>hd xs\<close>; cases \<open>tl xs\<close>) (auto)
    moreover have \<open>x = node z \<Longrightarrow> hp_prev_children k (Hp (node z) n c # xs) = Some z \<longleftrightarrow>
      z = Hp x n c \<and> xs \<noteq> [] \<and> k = node (hd (xs))\<close> for z
      using 2(4) hp_prev_children_in_nodes[of _ c] apply -
      apply (cases \<open>xs\<close>; cases z; cases \<open>hd xs\<close>)
      using hp_prev_children_in_nodes[of _ c] apply fastforce
      apply (auto simp:  )
      apply (metis "2"(4) hp.inject hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(1) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps list.distinct(1) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl remove_key_remove_all sum_image_mset_sum_map)
      apply (metis "2"(4) hp.inject hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(1) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps in_remove_key_children_changed list.distinct(2) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl sum_image_mset_sum_map)
      by (metis "2"(4) hp.sel(1) hp_prev_children_in_nodes hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps in_remove_key_children_changed list.distinct(2) list.sel(1) list.sel(3) option.sel remove_key_children_hd_tl sum_image_mset_sum_map)
    moreover have \<open>xs \<noteq> [] \<Longrightarrow> find_key_children (node (hd xs)) xs = Some (hd xs)\<close>
      by (metis find_key_children.simps(2) hp.exhaust_sel list.exhaust_sel)
    ultimately show ?case
      using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
        distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
      apply (auto split: option.splits if_splits simp: remove_key_children_hd_tl in_the_default_empty_iff)
      apply (simp add: disjunct_not_in distinct_mset_add)
      apply (auto simp add: hp_parent_children_cons hp_child_children_Cons_if)[]
      apply (metis disjunct_not_in distinct_mset_add hp_child_children_None_notin hp_child_hp_children_simps2 hp_parent_children_in_nodes2 option.distinct(1) sum_image_mset_sum_map)
      apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_child_None_notin_children hp_child_children_simps(2) hp_parent_children_in_nodes2 sum_image_mset_sum_map)
      apply (simp add: hp_parent_children_cons)
      apply (simp add: hp_child_children_Cons_if)
      apply (metis disjunct_not_in distinct_mset_add find_key_none_iff hp_child_None_notin_children mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_mset_sum_list)
      apply (smt (verit, del_insts) hp_child.simps(2) hp_child_children_Cons_if hp_child_hd hp_child_hp_children_simps2 list.exhaust_sel list.simps(9) o_apply option.map(2) option.sel option_hd_Some_hd remove_key_notin_unchanged sum_list_simps(2) union_iff)
      apply (metis hp_parent_None_iff_children_None hp_parent_children_None_notin hp_parent_children_append_case hp_parent_children_append_skip_first hp_parent_children_cons mset_map node_hd_in_sum sum_mset_sum_list)


      apply (auto simp add: hp_child_children_Cons_if)[]
      apply (smt (verit, best) ex_hp_node_children_Some_in_mset_nodes hp.sel(1) hp_child_children_remove_is_remove_hp_child_children hp_child_hd hp_child_hp_children_simps2 hp_node_children_None_notin2 hp_parent_children_remove_key_children list.sel(1) option.sel option_hd_Some_iff(2) pairing_heap_assms.hd_remove_key_node_same pairing_heap_assms.remove_key.simps remove_key_children.elims remove_key_children_notin_unchanged sum_image_mset_sum_map)
      apply (metis add_diff_cancel_left' distinct_mset_in_diff)
      apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_parent_children_None_notin option_last_Nil option_last_Some_iff(2))
      apply (metis (mono_tags, lifting) add_diff_cancel_right' distinct_mset_in_diff hp_child_None_notin_children hp_child_children_None_notin hp_child_children_simps(2) in_find_key_children_notin_remove_key mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (smt (verit, del_insts) arith_simps(49) disjunct_not_in distinct_mset_add hp_child_None_notin hp_child_children_None_notin hp_child_children_simps(2) in_find_key_notin_remove_key_children member_add_mset mset_nodes_find_key_children_subset mset_nodes_simps option.distinct(1) option.sel subset_mset.le_iff_add sum_image_mset_sum_map union_iff)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_noneD sum_image_mset_sum_map)
      apply (metis disjunct_not_in distinct_mset_add hp_parent_children_in_nodes2 sum_image_mset_sum_map)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_child_children_Cons_if hp_child_children_None_notin hp_child_hp_children_simps2 hp_parent_children_in_nodes2 sum_image_mset_sum_map)
      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2)[]
      apply (metis disjunct_not_in distinct_mset_add find_key_noneD hp_child_children_None_notin hp_child_hp_children_simps2 hp_next_children_append2 hp_parent_children_in_nodes2 mset_map sum_mset_sum_list)
      apply (metis hp.sel(1) hp_child_hp_children_simps2 hp_next_children_simps(2) hp_next_simps hp_parent_children_in_nodes option.distinct(1) option.sel sum_image_mset_sum_map)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_noneD sum_image_mset_sum_map)
      apply (metis disjunct_not_in distinct_mset_add find_key_noneD hp_parent_children_None_notin option.distinct(1) sum_image_mset_sum_map)
      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis get_min2.simps get_min2_alt_def hp_child_children_None_notin hp_child_hd hp_next_children_hd_is_hd_tl hp_parent_simps_single_if option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
      apply (metis get_min2.simps get_min2_alt_def hp_child_hd hp_next_children_hd_is_hd_tl hp_parent_simps_single_if option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (smt (z3) add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin get_min2.simps get_min2_alt_def hp.sel(3) hp_child.elims hp_child_children_None_notin hp_next_children_append2 hp_next_children_hd_is_hd_tl hp_parent_simps_single_if option_hd_Nil option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
      apply (metis get_min2.simps get_min2_alt_def hp_child_hd hp_next_children_hd_is_hd_tl hp_next_children_simps(2) hp_next_simps hp_parent_simps_single_if option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (smt (z3) add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin get_min2.simps get_min2_alt_def hp.sel(3) hp_child.elims hp_child_children_None_notin hp_next_children_append2 hp_next_children_hd_is_hd_tl hp_parent_simps_single_if option_hd_Nil option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
      apply (meson disjunct_not_in distinct_mset_add)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin sum_image_mset_sum_map)
      apply (metis hp_child_hp_children_simps2 hp_parent_children_in_nodes option.distinct(1) option.sel sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis (no_types, lifting) add_diff_cancel_left' distinct_mset_in_diff hp_child_children_None_notin mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (metis hp_child_hp_children_simps2 mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(1) option.sel sum_image_mset_sum_map)
      apply (metis (no_types, lifting) add_diff_cancel_left' distinct_mset_in_diff hp_child_children_None_notin mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (metis hp_child_hp_children_simps2 mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(1) option.sel sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis disjunct_not_in distinct_mset_add hp_child_children_None_notin mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (metis hp_child_hp_children_simps2 mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(1) option.sel sum_image_mset_sum_map)
      apply (metis disjunct_not_in distinct_mset_add hp_child_children_None_notin mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (metis hp_child_hp_children_simps2 mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(1) option.sel sum_image_mset_sum_map)


      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)

      apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_parent_children_None_notin option_last_Nil option_last_Some_iff(2))


      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis hp_parent_None_iff_children_None option.distinct(1))
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)
      apply (metis get_min2_alt_def hp_parent_children_hd_None hp_parent_simps_single_if option.distinct(1) sum_image_mset_sum_map)

      apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_noneD sum_image_mset_sum_map)

      apply (metis disjunct_not_in distinct_mset_add find_key_noneD hp_parent_children_None_notin option.distinct(1) sum_image_mset_sum_map)

      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis find_key_children.simps(1) hp_child_hd hp_child_hp_children_simps2 option.distinct(1) option.simps(8) option_hd_None_iff(2))
      apply (smt (verit, best) find_key_children.elims find_key_children_None_or_itself find_key_noneD
        find_key_none_iff hp.inject hp_child_hd hp_child_hp_children_simps2 hp_parent_None_iff_children_None list.discI list.sel(1)
        map_option_is_None mset_map option.sel option_hd_None_iff(1) remove_key_children.elims sum_mset_sum_list)
      apply (metis (no_types, lifting) remove_key.simps ex_hp_node_children_Some_in_mset_nodes hp_child_remove_is_remove_hp_child
        hp_node_children_None_notin2 is_mset_set_add mset_nodes.simps option.sel sum_image_mset_sum_map union_ac(2))
      apply (metis remove_key_children.simps(1) hp_child.simps(1) hp_child_hp_children_simps2 neq_NilE option.distinct(1) option.simps(8))
      apply (smt (verit, ccfv_SIG) remove_key_children.elims find_key_children_None_or_itself find_key_noneD find_key_none_iff get_min2.simps
        get_min2_alt_def hp.inject hp_child_hd hp_child_hp_children_simps2 hp_parent_simps_single_if list.discI option.map_disc_iff option_hd_None_iff(2)
        option_last_Nil option_last_Some_iff(1) remove_key_children_hp_parent_children_hd_None remove_key_children_notin_unchanged)
      apply (meson hp_child_children_remove_key_children_other_helper)


      apply (auto simp add: hp_child_children_Cons_if hp_parent_children_in_nodes2 hp_parent_children_cons split: option.splits if_splits)[]
      apply (metis find_key_children.simps(1) hp_child_hd hp_child_hp_children_simps2 option.distinct(1) option.simps(8) option_hd_None_iff(2))
        apply (smt (verit) find_key_children_None_or_itself hp.inject hp_child_hd hp_child_hp_children_simps2 hp_parent_simps(1) list_tail_coinc map_option_is_None neq_Nil_conv not_Some_eq option.sel option_hd_None_iff(1) find_key_children.elims remove_key_children.elims)

      apply (metis (no_types, lifting) remove_key.simps ex_hp_node_children_Some_in_mset_nodes hp_child_remove_is_remove_hp_child hp_node_children_None_notin2 is_mset_set_add mset_nodes.simps option.sel sum_image_mset_sum_map union_ac(2))
      apply (metis find_key_children.simps(1) hp_child_hd hp_child_hp_children_simps2 option.distinct(1) option.simps(8) option_hd_None_iff(2))
      apply (smt (verit) find_key_children.elims find_key_children_None_or_itself find_key_noneD find_key_none_iff get_min2.simps get_min2_alt_def hp.inject hp_child_hd hp_child_hp_children_simps2 hp_parent_simps_single_if if_Some_None_eq_None list_tail_coinc map_option_is_None neq_Nil_conv option.sel option_hd_None_iff(1) find_key_children.elims remove_key_children.elims remove_key_children_hp_parent_children_hd_None remove_key_children_notin_unchanged)
      by (meson hp_child_children_remove_key_children_other_helper)
qed

lemma hp_child_remove_key_other:
  assumes \<open>distinct_mset (mset_nodes xs)\<close> \<open>remove_key a xs \<noteq> None\<close>
  shows \<open>hp_child b (the (remove_key a xs)) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key a xs))) then None
    else if map_option node (hp_parent a xs) = Some b then (hp_next a xs)
    else map_option (the o remove_key a) (hp_child b xs))\<close>
  using assms hp_child_children_remove_key_children_other[of \<open>hps xs\<close> b a]
  apply (cases xs)
  apply auto
  apply (metis hp_child_hp_children_simps2 in_the_default_empty_iff mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.map_disc_iff option.map_sel sum_mset_sum_list)
  apply (metis get_min2.simps get_min2_alt_def hp.sel(3) hp_child_hd hp_child_hp_children_simps2 hp_next_children_hd_is_hd_tl hp_parent_children_in_nodes2 hp_parent_simps_single_if option_last_Nil option_last_Some_iff(2) remove_key_children_hd_tl remove_key_children_node_hd sum_image_mset_sum_map)
  apply (metis hp_child_hp_children_simps2 in_the_default_empty_iff map_option_is_None mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel sum_mset_sum_list)
  apply (case_tac x3; case_tac \<open>hd x3\<close>)
  apply (auto simp add: hp_parent_simps_single_if split: option.splits if_splits)
  done

abbreviation hp_score_children where
  \<open>hp_score_children a xs \<equiv> map_option score (hp_node_children a xs)\<close>

lemma hp_score_children_remove_key_children_other:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_score_children b (remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key_children a xs))) then None
    else (hp_score_children b xs))\<close>
  using assms apply (induction a xs rule: remove_key_children.induct)
  apply (auto split: option.splits if_splits simp: hp_node_children_Cons_if in_the_default_empty_iff)
  apply (metis find_key_none_iff mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel sum_image_mset_sum_map)
  apply (simp add: disjunct_not_in distinct_mset_add)
  apply (metis disjunct_not_in distinct_mset_add find_key_none_iff mset_nodes_find_key_children_subset mset_subset_eqD option.map_sel sum_image_mset_sum_map)
  apply (metis None_eq_map_option_iff distinct_mset_add find_key_noneD sum_image_mset_sum_map)
  using distinct_mset_add apply blast
  apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(2) option.sel sum_image_mset_sum_map)
  apply (meson not_orig_notin_remove_key)
  apply (metis disjunct_not_in distinct_mset_add hp_node_children_None_notin2 not_orig_notin_remove_key sum_image_mset_sum_map)
  apply (metis distinct_mset_add hp_node_children_None_notin2 sum_image_mset_sum_map)
  apply (metis Duplicate_Free_Multiset.distinct_mset_union2 None_eq_map_option_iff find_key_noneD hp_node_children_None_notin2 sum_image_mset_sum_map union_commute)
  apply (metis None_eq_map_option_iff distinct_mset_add hp_node_children_None_notin2 sum_image_mset_sum_map)
  apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.distinct(2) option.sel sum_image_mset_sum_map)
  apply (metis add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff find_key_noneD sum_image_mset_sum_map)
  apply (meson not_orig_notin_remove_key)
  by (meson not_orig_notin_remove_key)

abbreviation hp_score where
  \<open>hp_score a xs \<equiv> map_option score (hp_node a xs)\<close>

lemma hp_score_remove_key_other:
  assumes \<open>distinct_mset (mset_nodes xs)\<close> \<open>remove_key a xs \<noteq> None\<close>
  shows \<open>hp_score b (the (remove_key a xs)) =
    (if b \<in># (the_default {#} (map_option mset_nodes (find_key a xs))) then None
    else (hp_score b xs))\<close>
  using hp_score_children_remove_key_children_other[of \<open>hps xs\<close> b a] assms
  apply (cases xs)
  apply (auto split: if_splits simp: in_the_default_empty_iff)
  apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
  apply (simp add: hp_node_children_None_notin2)
  by (metis hp.sel(2) hp_node_children_simps2 hp_node_simps option.simps(9))

lemma map_option_node_remove_key_iff:
  \<open>(h \<noteq> None \<Longrightarrow> distinct_mset (mset_nodes (the h))) \<Longrightarrow> (h \<noteq> None \<Longrightarrow> remove_key a (the h) \<noteq> None) \<Longrightarrow>
  map_option node h = map_option node (map_option (\<lambda>x. the (remove_key a x)) h) \<longleftrightarrow> h = None \<or> (h \<noteq> None \<and> a \<noteq> node (the h))\<close>
  apply (cases h; cases \<open>the h\<close>)
  apply simp
  apply (rule iffI)
  apply simp
  apply auto
  done

lemma sum_next_prev_child_subset:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>
   ((if hp_next n h = None then {#} else (mset_nodes (the (hp_next n h)))) +
  (if hp_prev n h = None then {#} else (mset_nodes (the (hp_prev n h)))) +
  (if hp_child n h = None then {#} else (mset_nodes (the (hp_child n h))))) \<subseteq># mset_nodes h\<close>
  apply (induction n h rule: hp_next.induct)
  apply (auto split: option.splits if_splits)
  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) split: if_splits option.splits intro: distinct_mset_mono')[]
  apply (metis distinct_mset_add mset_le_incr_right(2) union_mset_add_mset_right)
  apply (smt (verit, ccfv_threshold) distinct_mset_add hp_next_children_simps(1) hp_next_children_simps(2) hp_prev_children_simps(1) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps mset_subset_eq_add_right option.sel option_last_Nil option_last_Some_iff(2) subset_mset.dual_order.trans union_commute union_mset_add_mset_right)
  apply (smt (verit, ccfv_threshold) Duplicate_Free_Multiset.distinct_mset_union2 Groups.add_ac(2) ab_semigroup_add_class.add_ac(1) add_diff_cancel_left' distinct_mem_diff_mset hp_child_children_None_notin hp_next_children_simps(2) hp_prev_children_simps(2) hp_prev_children_simps(3) hp_prev_simps mset_le_subtract_right mset_map mset_subset_eq_mono_add node_in_mset_nodes option.sel option_last_Nil option_last_Some_iff(1) sum_mset_sum_list union_mset_add_mset_right)
  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) split: if_splits option.splits intro: distinct_mset_mono')[]
  apply (metis distinct_mset_add mset_le_incr_right(2) union_mset_add_mset_right)
  apply (metis distinct_mset_add mset_le_incr_right(1) union_mset_add_mset_right)
    
  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right)[]
  apply (metis mset_le_incr_right(2) union_mset_add_mset_right)
  apply (metis hp_child_children_None_notin hp_next_None_notin option.simps(2) sum_image_mset_sum_map)
  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right)[]
  apply (metis hp_next_None_notin node_in_mset_nodes option.simps(2))
  apply (metis mset_le_incr_right(2) union_mset_add_mset_right)
  subgoal
    by (metis hp_next_None_notin hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_simps(2) hp_prev_None_notin_children hp_prev_simps mset_map option.simps(2) sum_mset_sum_list)
  subgoal
    by (metis hp_prev_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis subset_mset.add_mono union_ac(2) union_mset_add_mset_right)
  subgoal
    by (metis hp_next_None_notin hp_next_children_simps(3) hp_next_children_skip_end hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2))
  subgoal
    by (metis mset_le_incr_right(1) union_mset_add_mset_right)

  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right)[]
  subgoal
    by (metis mset_le_incr_right(2) union_mset_add_mset_right)
  subgoal
    by (metis hp_child_children_None_notin hp_next_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_children_None_notin hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_children_None_notin hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_children_None_notin hp_next_None_notin mset_map option.simps(2) sum_mset_sum_list)

  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]


  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis hp_child_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis subset_mset.add_mono union_ac(2) union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_child_children_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))



  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  subgoal
    by (smt (verit, del_insts) hp.collapse list.exhaust_sel list.simps(9) mset_le_decr_left(1) mset_map mset_nodes.simps subset_mset.dual_order.refl subset_mset_trans_add_mset sum_list_simps(2) sum_mset_sum_list union_ac(2))
  subgoal
    by (metis subset_mset.add_mono union_ac(2) union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_child_children_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)



  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis node_in_mset_nodes)
  subgoal
    by (metis hp_child_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis hp_child_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis subset_mset.add_mono union_commute union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_child_children_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_None_notin hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_simps(2) hp_prev_children_None_notin mset_map option.distinct(1) sum_mset_sum_list)
  subgoal
    by (metis hp_prev_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis hp_prev_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis hp_child_None_notin hp_next_None_notin hp_next_children_None_notin hp_next_children_simps(3) option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_next_None_notin hp_next_children_None_notin hp_next_children_simps(3) hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_children_None_notin hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)
  subgoal
    by (metis hp_child_None_notin hp_child_children_None_notin option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map)


  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  apply (metis mset_le_incr_right2 union_mset_add_mset_right)
  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis mset_le_incr_right2 union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_prev_None_notin option.distinct(1))
  subgoal
    by (metis hp_child_None_notin hp_prev_None_notin option.distinct(1))
   

  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono'
    intro: mset_le_incr_right mset_le_incr_right subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis mset_le_incr_right2 union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_next_None_notin option.distinct(1))
  

  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono' union_mset_add_mset_right
    intro: mset_le_incr_right mset_le_incr_right2 subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis hp_next_None_notin node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
  subgoal
    by (metis mset_le_incr_right2 union_mset_add_mset_right)
  subgoal
    by (metis hp_child_None_notin hp_next_None_notin option_hd_Nil option_hd_Some_iff(2))
  subgoal
    by (metis hp_next_None_notin node_in_mset_nodes option.simps(2))
  subgoal
    by (metis hp_child_None_notin hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2))
  subgoal
    by (metis hp_child_None_notin hp_prev_None_notin option_hd_Nil option_hd_Some_iff(2))
  subgoal
    by (metis hp_child_None_notin hp_next_None_notin option.simps(2))

  apply (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono' union_mset_add_mset_right
    intro: mset_le_incr_right mset_le_incr_right2 subset_mset_imp_subset_add_mset)[]
  subgoal
    by (metis add_diff_cancel_left' distinct_mset_in_diff hp_child_None_notin option.distinct(1) union_iff)
  subgoal
    by (metis add_diff_cancel_left' distinct_mset_in_diff hp_child_None_notin option.distinct(1) union_iff)
  subgoal
    by (metis add_diff_cancel_left' distinct_mset_in_diff hp_child_None_notin option.distinct(1) union_iff)

  by (auto simp add: hp_next_children.simps(1) hp_prev_children.simps(1) distinct_mset_add disjunct_not_in ac_simps
    split: if_splits option.splits intro: distinct_mset_mono' union_mset_add_mset_right
    intro: mset_le_incr_right mset_le_incr_right2 subset_mset_imp_subset_add_mset)


lemma distinct_sum_next_prev_child:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow>
   distinct_mset ((if hp_next n h = None then {#} else (mset_nodes (the (hp_next n h)))) +
  (if hp_prev n h = None then {#} else (mset_nodes (the (hp_prev n h)))) +
  (if hp_child n h = None then {#} else (mset_nodes (the (hp_child n h)))))\<close>
  using sum_next_prev_child_subset[of h n] by (auto intro: distinct_mset_mono)


lemma node_remove_key_in_mset_nodes:
  \<open>remove_key a h \<noteq> None \<Longrightarrow> mset_nodes (the (remove_key a h)) \<subseteq># mset_nodes h\<close>
  apply (induction a h rule: remove_key.induct)
  apply (auto intro: )
  by (metis node_remove_key_children_in_mset_nodes sum_image_mset_sum_map)


lemma no_relative_ancestor_or_notin: \<open>hp_parent ( m') h = None \<Longrightarrow>
      hp_prev ( m') h = None \<Longrightarrow>
  hp_next ( m') h = None \<Longrightarrow>  m' = node h \<or> m' \<notin># mset_nodes h\<close>
  apply (induction m' h rule: hp_next.induct)
  apply (auto simp: hp_prev_children_cons_if
    split:option.splits )
  apply (metis hp.exhaust_sel hp_next_children_simps(1) hp_next_children_simps(2) hp_parent_children_cons hp_parent_simps(2) hp_prev_simps option.collapse option.simps(5) option_last_Some_iff(2))
  apply (metis hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_parent_children_cons hp_parent_simps(2) hp_prev_cadr_node hp_prev_children_cons_if option.collapse option.simps(2) option.simps(4) option.simps(5))
  apply (metis hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_parent_children_cons hp_parent_simps(2) hp_prev_cadr_node hp_prev_children_cons_if option.case(1) option.collapse option.simps(2) option.simps(5))
  apply (metis option.simps(2))
  apply (metis option.simps(2))
  apply (metis option.simps(2))
  by (metis hp.exhaust_sel hp_parent_None_iff_children_None hp_parent_children_cons hp_prev_simps list.sel(1) list.simps(3) option.case_eq_if option.simps(2))

lemma hp_node_in_find_key_children:
  "distinct_mset (sum_list (map mset_nodes h)) \<Longrightarrow> find_key_children x h = Some m' \<Longrightarrow> a \<in># mset_nodes m' \<Longrightarrow>
  hp_node a m' = hp_node_children a h"
  apply (induction x h arbitrary: m' rule: find_key_children.induct)
  apply (auto split: if_splits option.splits simp: hp_node_children_Cons_if
    disjunct_not_in distinct_mset_add)
  by (metis hp_node_children_simps2)

lemma hp_node_in_find_key0:
  "distinct_mset (mset_nodes h) \<Longrightarrow> find_key x h = Some m' \<Longrightarrow> a \<in># mset_nodes m' \<Longrightarrow>
  hp_node a m' = hp_node a h"
  using hp_node_in_find_key_children[of \<open>hps h\<close> x m' a]
  apply (cases h)
  apply (auto split: if_splits simp: hp_node_children_Cons_if)
  by (metis hp_node_None_notin2 hp_node_children_None_notin hp_node_children_simps2 sum_image_mset_sum_map)

lemma hp_node_in_find_key:
  "distinct_mset (mset_nodes h) \<Longrightarrow> find_key x h \<noteq> None \<Longrightarrow> a \<in># mset_nodes (the (find_key x h)) \<Longrightarrow>
  hp_node a (the (find_key x h)) = hp_node a h"
  using hp_node_in_find_key0[of h x _ a]
  by auto

end


context hmstruct_with_prio
begin

definition hmrel :: \<open>(('a, 'v) hp option \<times> ('a multiset \<times> ('a \<Rightarrow> 'v))) set\<close> where
  \<open>hmrel = {(xs, (b, w)). invar xs \<and> distinct_mset b \<and>
     ((xs = None \<and> b = {#}) \<or>
       (xs \<noteq> None \<and> b = mset_nodes (the xs) \<and>
       (\<forall>v\<in>#b. hp_node v (the xs) \<noteq> None) \<and>
       (\<forall>v\<in>#b. score (the (hp_node v (the xs))) = w v)))}\<close>

lemma hp_score_children_iff_hp_score: \<open>xa \<in># sum_list (map mset_nodes list) \<Longrightarrow> distinct_mset (sum_list (map mset_nodes list)) \<Longrightarrow>
  hp_score_children xa list \<noteq> None \<longleftrightarrow> (\<exists>x\<in>set list. hp_score xa x \<noteq> None \<and> hp_score_children xa list = hp_score xa x \<and> (\<forall>x\<in>set list - {x}. hp_score xa x = None))\<close>
  apply (induction list)
  apply (auto simp: hp_node_children_Cons_if)
  apply (metis disjunct_not_in distinct_mset_add mset_subset_eqD mset_subset_eq_add_left sum_list_map_remove1)
  apply (metis disjunct_not_in distinct_mset_add mset_subset_eqD mset_subset_eq_add_left sum_list_map_remove1)
  using WB_List_More.distinct_mset_union2 apply blast
  done

lemma hp_score_children_in_iff: \<open>xa \<in># sum_list (map mset_nodes list) \<Longrightarrow> distinct_mset (sum_list (map mset_nodes list)) \<Longrightarrow>
  the (hp_score_children xa list) \<in> A \<longleftrightarrow> (\<exists>x\<in>set list. hp_score xa x \<noteq> None \<and> the (hp_score xa x) \<in> A)\<close>
  using hp_score_children_iff_hp_score[of xa list]
  by (auto simp: hp_node_children_Cons_if hp_node_children_None_notin2)

lemma set_hp_is_hp_score_mset_nodes:
  assumes \<open>distinct_mset (mset_nodes a)\<close>
  shows \<open>set_hp a =  (\<lambda>v'. the (hp_score v' a)) ` set_mset (mset_nodes a)\<close>
    using assms
  proof (induction a rule: mset_nodes.induct)
    case (1 x1a x2a x3a) note p = this(1) and dist = this(2)
    show ?case (is "?A = ?B")
    proof (standard; standard)
      fix x
      assume xA: \<open>x \<in> ?A\<close>
      moreover have \<open>\<Union> (set_hp ` set x3a) = (\<lambda>v'. the (hp_score_children v' x3a)) ` set_mset (\<Sum>\<^sub># (mset_nodes `# mset x3a))\<close> (is \<open>?X = ?Y\<close>)
      proof -
        have [simp]: \<open>x \<in> set x3a \<Longrightarrow> distinct_mset (mset_nodes x)\<close> for x
          using dist by (simp add: distinct_mset_add sum_list_map_remove1)
        have \<open>?X =  (\<Union>x\<in>set x3a. (\<lambda>v'. the (hp_score v' x)) ` set_mset (mset_nodes x))\<close>
          using p dist by (simp add: distinct_mset_add sum_list_map_remove1)
        also have \<open>... = (\<Union>x\<in>set x3a. (\<lambda>v'. the (hp_score_children v' x3a)) ` set_mset (mset_nodes x))\<close>
          apply (rule SUP_cong)
          apply simp
          apply (auto intro!: imageI dest!: split_list_first simp: image_Un cong: image_cong)
          apply (subst image_cong)
          apply (rule refl)
          apply (subst hp_node_children_append(1))
          using dist apply auto[]
          apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp_node_children_None_notin2 sum_image_mset_sum_map)
          apply (rule refl)
          apply auto[]
          apply (subst hp_node_children_append(1))
          using dist apply auto[]
          apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp_node_children_None_notin2 sum_image_mset_sum_map)
          apply auto
          done
        also have \<open>... = ?Y\<close>
          apply (auto simp add: sum_list_map_remove1)
          by (metis (no_types, lifting) dist distinct_mset_add hp_node_None_notin2 hp_node_children_None_notin2
            hp_score_children_iff_hp_score image_iff mset_nodes.simps option.map_disc_iff sum_image_mset_sum_map)
        finally show ?thesis .
      qed
      ultimately have \<open>x=x2a \<or> x \<in> ?Y\<close>
        by simp
      then show \<open>x \<in> ?B\<close>
        apply auto
        by (metis (no_types, lifting) "1"(2) add_mset_disjoint(1) distinct_mset_add hp_node_children_simps2 mset_nodes_simps rev_image_eqI)
    next
      fix x
      assume xA: \<open>x \<in> ?B\<close>
      moreover have \<open>\<Union> (set_hp ` set x3a) = (\<lambda>v'. the (hp_score_children v' x3a)) ` set_mset (\<Sum>\<^sub># (mset_nodes `# mset x3a))\<close> (is \<open>?X = ?Y\<close>)
      proof -
        have [simp]: \<open>x \<in> set x3a \<Longrightarrow> distinct_mset (mset_nodes x)\<close> for x
          using dist by (simp add: distinct_mset_add sum_list_map_remove1)
        have \<open>?X =  (\<Union>x\<in>set x3a. (\<lambda>v'. the (hp_score v' x)) ` set_mset (mset_nodes x))\<close>
          using p dist by (simp add: distinct_mset_add sum_list_map_remove1)
        also have \<open>... = (\<Union>x\<in>set x3a. (\<lambda>v'. the (hp_score_children v' x3a)) ` set_mset (mset_nodes x))\<close>
          apply (rule SUP_cong)
          apply simp
          apply (auto intro!: imageI dest!: split_list_first simp: image_Un cong: image_cong)
          apply (subst image_cong)
          apply (rule refl)
          apply (subst hp_node_children_append(1))
          using dist apply auto[]
          apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp_node_children_None_notin2 sum_image_mset_sum_map)
          apply (rule refl)
          apply auto[]
          apply (subst hp_node_children_append(1))
          using dist apply auto[]
          apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mset_in_diff hp_node_children_None_notin2 sum_image_mset_sum_map)
          apply auto
          done
        also have \<open>... = ?Y\<close>
          apply (auto simp add: sum_list_map_remove1)
          by (metis (no_types, lifting) dist distinct_mset_add hp_node_None_notin2 hp_node_children_None_notin2
            hp_score_children_iff_hp_score image_iff mset_nodes.simps option.map_disc_iff sum_image_mset_sum_map)
        finally show ?thesis .
      qed
      ultimately have \<open>x=x2a \<or> x \<in> ?X\<close>
        apply auto
        by (metis (no_types, lifting) "1"(2) add_mset_disjoint(1) distinct_mset_add hp_node_children_simps2 image_iff mset_nodes.simps sum_image_mset_sum_map)
      then show \<open>x \<in> ?A\<close>
        by auto
    qed
qed

lemma get_min2_mop_prio_peek_min:
  \<open>(xs, ys) \<in> hmrel \<Longrightarrow> fst ys \<noteq> {#} \<Longrightarrow>
  RETURN (get_min2 xs) \<le> \<Down>(Id) (mop_prio_peek_min ys)\<close>
  unfolding mop_prio_peek_min_def hmrel_def
  apply refine_vcg
  subgoal
    by (cases xs; cases \<open>the xs\<close>) auto
  subgoal
    using set_hp_is_hp_score_mset_nodes[of \<open>hd (hps (the xs))\<close>]
    apply (cases xs; cases \<open>the xs\<close>)
    apply (auto simp: invar_def)
    using le apply blast
    apply (cases \<open>hps (the xs)\<close>)
    apply simp
    apply (auto split: if_splits option.splits simp: distinct_mset_union in_mset_sum_list_iff
      dest!: split_list)
    apply (metis (no_types, lifting) hp_node_None_notin2 mem_simps(3) option.exhaust_sel option.map_sel)
    by (smt (z3) diff_union_cancelR distinct_mset_add distinct_mset_in_diff hp_node_None_notin2
      hp_node_children_None_notin2 hp_node_children_append(1) hp_node_children_simps(3)
      hp_node_children_simps2 mset_map option.map_sel rev_image_eqI set_hp_is_hp_score_mset_nodes set_mset_union sum_mset_sum_list union_iff)
  done

lemma del_min_None_iff: \<open>del_min a = None \<longleftrightarrow> a = None \<or> hps (the a) = []\<close>
  by (cases a; cases \<open>the a\<close>) (auto simp: pass12_merge_pairs)

lemma score_hp_node_pass\<^sub>1: \<open>distinct_mset (sum_list (map mset_nodes x3)) \<Longrightarrow> score (the (hp_node_children v (pass\<^sub>1 x3))) = score (the (hp_node_children v x3))\<close>
  apply (induction x3 rule: pass\<^sub>1.induct)
  subgoal by auto
  subgoal by auto
  subgoal for h1 h2 hs
    apply (cases h1; cases h2)
    apply (auto simp: hp_node_children_Cons_if split: option.splits)
    using WB_List_More.distinct_mset_union2 apply blast
    apply (metis hp_node_children_None_notin2 sum_image_mset_sum_map)
    by (metis diff_union_cancelL distinct_mset_in_diff union_iff)
  done

lemma node_pass\<^sub>2_in_nodes: \<open>pass\<^sub>2 hs \<noteq> None \<Longrightarrow> mset_nodes (the (pass\<^sub>2 hs)) \<subseteq># sum_list (map mset_nodes hs)\<close>
  by (induction hs rule: pass\<^sub>2.induct) (fastforce split: option.splits simp del: mset_nodes_pass\<^sub>2)+

lemma score_pass2_same:
  \<open>distinct_mset (sum_list (map mset_nodes x3)) \<Longrightarrow> pass\<^sub>2 x3 \<noteq> None \<Longrightarrow>v \<in># sum_list (map mset_nodes x3) \<Longrightarrow>
  score (the (hp_node v (the (pass\<^sub>2 x3)))) = score (the (hp_node_children v x3))\<close>
  apply (induction x3 rule: pass\<^sub>2.induct)
  subgoal by auto
  subgoal for h hs
    using node_pass\<^sub>2_in_nodes[of hs]
    apply (cases h; cases \<open>the (pass\<^sub>2 hs)\<close>)
    apply (auto split: option.splits simp: hp_node_children_None_notin2 hp_node_children_Cons_if distinct_mset_add)
    apply (metis mset_subset_eq_insertD option_last_Nil option_last_Some_iff(1) pass\<^sub>2.simps(1))
    apply (metis disjunct_not_in mset_subset_eq_insertD not_Some_eq pass\<^sub>2.simps(1))
    apply (metis mset_subset_eq_insertD option_last_Nil option_last_Some_iff(1) pass\<^sub>2.simps(1))
    apply (metis disjunct_not_in mset_subset_eq_insertD not_Some_eq pass\<^sub>2.simps(1))
    apply (metis disjunct_not_in hp_node_None_notin2 hp_node_children_simps2 mset_nodes_pass\<^sub>2 not_Some_eq option.sel)
    apply (metis option.distinct(2) pass\<^sub>2.simps(1))
    apply (metis option.distinct(2) pass\<^sub>2.simps(1))
    apply (metis option.distinct(2) pass\<^sub>2.simps(1))
    apply (metis option.distinct(2) pass\<^sub>2.simps(1))
    apply (meson disjunct_not_in insert_subset_eq_iff)
    apply (meson disjunct_not_in insert_subset_eq_iff)
    apply (meson disjunct_not_in insert_subset_eq_iff)
    apply (meson disjunct_not_in ex_hp_node_children_Some_in_mset_nodes mset_le_add_mset mset_subset_eqD)
    done
  done

lemma score_hp_node_merge_pairs_same: \<open>distinct_mset (sum_list (map mset_nodes x3)) \<Longrightarrow> v \<in># sum_list (map mset_nodes x3) \<Longrightarrow>
  score (the (hp_node v (the (merge_pairs x3)))) = score (the (hp_node_children v x3))\<close>
  unfolding pass12_merge_pairs[symmetric]
  apply (subst score_pass2_same score_hp_node_pass\<^sub>1)
  apply simp_all
  apply (metis in_multiset_nempty list.map(1) pairing_heap_assms.mset_nodes_pass\<^sub>1 sum_list.Nil)
  by (meson score_hp_node_pass\<^sub>1)

lemma get_min2_del_min2_mop_prio_pop_min:
  \<open>(xs, ys) \<in> hmrel \<Longrightarrow>fst ys \<noteq> {#} \<Longrightarrow>
  RETURN (get_min2 xs, del_min xs) \<le> \<Down>(Id \<times>\<^sub>r hmrel) (mop_prio_pop_min ys)\<close>
  using get_min2_mop_prio_peek_min[of xs ys]
  unfolding mop_prio_pop_min_def
  apply refine_vcg
  unfolding conc_fun_RES
  apply (auto simp: local.mop_prio_peek_min_def Image_iff
    intro!: exI[of _ \<open>get_min2 xs\<close>] exI[of _ \<open>(snd ys)\<close>])
  apply (cases \<open>the xs\<close>; cases xs)
  apply (simp add: hmrel_def invar_del_min pass12_merge_pairs)
  apply (simp add: hmrel_def invar_del_min pass12_merge_pairs)
  apply (cases \<open>del_min xs = None\<close>)
  apply (auto simp: hmrel_def invar_del_min del_min_None_iff pass12_merge_pairs
      mset_nodes_merge_pairs intro!: invar_merge_pairs)[]
  apply (auto simp: hmrel_def invar_del_min del_min_None_iff pass12_merge_pairs score_hp_node_merge_pairs_same
      mset_nodes_merge_pairs intro!: invar_merge_pairs)[]
  apply (meson invar_Some php.simps)
  apply (meson merge_pairs_None_iff not_None_eq)
  by (metis hp_node_children_simps2)


lemma mop_prio_insert:
  \<open>(xs, ys) \<in> hmrel \<Longrightarrow>
  RETURN (insert w v xs) \<le> \<Down>(hmrel) (mop_prio_insert w v ys)\<close>
  unfolding mop_prio_insert_def
  apply refine_vcg
  subgoal for a b
    apply (auto simp: hmrel_def invar_Some php_link le)
    apply (smt (verit, del_insts) hp.exhaust_sel hp.inject hp_node_children_simps(3) hp_node_children_simps2
      hp_node_simps link.simps node_in_mset_nodes option.sel option_last_Nil option_last_Some_iff(2))
    by (smt (verit, ccfv_threshold) add.right_neutral diff_single_trivial distinct_mset_in_diff hp.sel(1,2) hp_node_None_notin2
      hp_node_children_simps(2) hp_node_children_simps(3) hp_node_children_simps2 hp_node_node_itself
      list.simps(8) mset_nodes_simps option.sel link.simps php.elims(2) sum_list_simps(1))
  done

lemma find_key_node_itself[simp]: \<open>find_key (node y) y = Some y\<close>
  by (cases y) auto

lemma invar_decrease_key: \<open>le v x \<Longrightarrow>
      invar (Some (Hp w x x3)) \<Longrightarrow> invar (Some (Hp w v x3))\<close>
  by (auto simp: invar_def intro!: transpD[OF trans, of v x])

lemma find_key_children_single[simp]: \<open>find_key_children k [x] = find_key k x\<close>
  by (cases x; auto split: option.splits)

lemma hp_node_find_key_children:
  \<open>distinct_mset (sum_list (map mset_nodes a)) \<Longrightarrow> find_key_children x a \<noteq> None \<Longrightarrow>
  hp_node x (the (find_key_children x a)) \<noteq> None \<Longrightarrow>
  hp_node x (the (find_key_children x a)) = hp_node_children x a\<close>
  apply (induction x a rule: find_key_children.induct)
  apply (auto split: option.splits)
  apply (metis WB_List_More.distinct_mset_union2 find_key_noneD sum_image_mset_sum_map)
  by (metis distinct_mset_add find_key_noneD hp_node_None_notin2 hp_node_children_Cons_if hp_node_children_simps2 sum_image_mset_sum_map)

lemma hp_node_find_key:
  \<open>distinct_mset (mset_nodes a) \<Longrightarrow> find_key x a \<noteq> None \<Longrightarrow> hp_score x (the (find_key x a)) \<noteq> None \<Longrightarrow>
  hp_score x (the (find_key x a)) = hp_score x a\<close>
  using hp_node_find_key_children[of \<open>hps a\<close> x]
  apply (cases a)
  apply auto
  by (metis find_key_noneD sum_image_mset_sum_map)

lemma score_hp_node_link:
  \<open>distinct_mset (mset_nodes a + mset_nodes b) \<Longrightarrow>
  map_option score (hp_node w (link a b)) = (case hp_node w a of Some a \<Rightarrow> Some (score a)
  | _ \<Rightarrow> map_option score (hp_node w b))\<close>
  apply (cases a; cases b)
  apply (auto split: option.splits)
  by (metis (no_types, opaque_lifting) distinct_mset_iff ex_hp_node_children_Some_in_mset_nodes mset_add union_mset_add_mset_left union_mset_add_mset_right)

lemma hp_node_link_none_iff_parents: \<open>hp_node va (link a b) = None \<longleftrightarrow> hp_node va a = None \<and> hp_node va b = None\<close>
  by auto

lemma score_hp_node_link2:
  \<open>distinct_mset (mset_nodes a + mset_nodes b) \<Longrightarrow> (hp_node w (link a b)) \<noteq> None \<Longrightarrow>
  score (the (hp_node w (link a b))) = (case hp_node w a of Some a \<Rightarrow> (score a)
  | _ \<Rightarrow> score (the (hp_node w b)))\<close>
  using score_hp_node_link[of a b w] by (cases \<open>hp_node w (link a b)\<close>; cases \<open>hp_node w b\<close>)
   (auto split: option.splits)

lemma decrease_key_mop_prio_change_weight:
  assumes \<open>(xs, ys) \<in> hmrel\<close> \<open>w \<in># fst ys\<close> \<open>le v (snd ys w)\<close>
  shows \<open>RETURN (decrease_key w v (the xs)) \<le> \<Down>(hmrel) (mop_prio_change_weight w v ys)\<close>
proof -
  have K: \<open>xs' = xs \<Longrightarrow> node (the xs') \<noteq> w \<longleftrightarrow> remove_key w (the xs)\<noteq> None\<close> for xs'
    using assms by (cases xs; cases \<open>the xs\<close>) (auto simp: hmrel_def)
  have \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close>
    using assms invar_find_key[of \<open>the xs\<close> w] find_key_None_or_itself[of w \<open>the xs\<close>]
       find_key_none_iff[of w \<open>[the xs]\<close>]
       hp_node_find_key[of \<open>the xs\<close> w]
    apply (cases \<open>the (find_key w (the xs))\<close>; cases \<open>find_key w (the xs)\<close>)
    apply simp_all
    apply (auto simp: hmrel_def invar_Some)
    by (metis hp_node_None_notin2 option.map_sel option.sel)

  then have \<open>invar (Some (Hp w (snd ys w) (hps (the (find_key w (the xs))))))\<close>
    using assms invar_find_key[of \<open>the xs\<close> w] by (auto simp: hmrel_def invar_Some)
  moreover have \<open>find_key w (the xs) \<noteq> None ⟹ remove_key w (the xs) \<noteq> None \<Longrightarrow>
    distinct_mset (mset_nodes (Hp w v (hps (the (find_key w (the xs))))) + mset_nodes (the (remove_key w (the xs))))\<close>
    using assms distinct_mset_find_node_next[of \<open>the xs\<close> w \<open>the (find_key w (the xs))\<close>]
    apply (subst \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close>) apply (auto simp: hmrel_def)
    apply (metis Some_to_the \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close> add_mset_disjoint(1) distinct_mset_add mset_nodes_simps)
    apply (metis \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close> hp.sel(1) in_find_key_notin_remove_key node_in_mset_nodes not_Some_eq option.sel)
    by (metis (no_types, lifting) \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close> add_diff_cancel_left' disjunct_not_in distinct_mset_add distinct_mset_mono' in_diffD in_find_key_notin_remove_key mset_nodes.simps option.distinct(1) option.sel pairing_heap_assms.node_remove_key_in_mset_nodes sum_image_mset_sum_map)
 
  ultimately show ?thesis
    using assms
    unfolding mop_prio_change_weight_def
    apply refine_vcg
    subgoal
      using invar_decrease_key[of v \<open>snd ys w\<close> w \<open>hps (the (find_key w (the xs)))\<close>]
        find_key_none_iff[of w \<open>[the xs]\<close>] find_key_None_or_itself[of w \<open>the xs\<close>]
        invar_find_key[of \<open>the xs\<close> w] hp_node_find_key[of \<open>the xs\<close> w]
        find_remove_mset_nodes_full[of \<open>the xs\<close> w \<open>the (remove_key w (the xs))\<close> \<open>the(find_key w (the xs))\<close>]
      apply (auto simp: hmrel_def decrease_key_def remove_key_None_iff invar_def score_hp_node_link2
        simp del: find_key_none_iff php.simps
        intro:
        split: option.splits hp.splits)
      apply (metis invar_Some php_link php_remove_key)
      apply (metis (no_types, lifting) \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close>
        add_mset_add_single find_remove_mset_nodes_full hp.inject mset_nodes.simps option.sel sum_image_mset_sum_map union_ac(2)
        union_mset_add_mset_right)
      apply (metis Some_to_the \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close>
        hp.sel(1) mset_cancel_elem(2) mset_nodes.simps mset_right_cancel_union
        find_remove_mset_nodes_full sum_image_mset_sum_map)
      using K
      apply (simp add: score_hp_node_link2 del: php.simps)
      apply auto

      using K
      apply (simp add: score_hp_node_link2 del: php.simps)
      apply (subst score_hp_node_link2)
      apply simp
      apply (simp add: hp_node_link_none_iff_parents)
      apply (auto split: option.splits)
      apply (metis member_add_mset mset_cancel_union(2))
      apply (metis hp_node_None_notin2 hp_node_children_None_notin2 hp_score_remove_key_other map_option_is_None member_add_mset option.map_sel option.sel option_hd_Nil option_hd_Some_iff(2) sum_image_mset_sum_map union_iff)
      by (metis \<open>find_key w (the xs) = Some (Hp w (snd ys w) (hps (the (find_key w (the xs)))))\<close> hp.simps(1) hp_node_children_None_notin2 hp_node_children_simps2 hp_node_in_find_key mset_nodes.simps option.sel option.simps(2) union_iff)
    done
qed

end

interpretation VSIDS: hmstruct_with_prio where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done

end
