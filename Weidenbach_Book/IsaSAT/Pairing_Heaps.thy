theory Pairing_Heaps
  imports Ordered_Pairing_Heap_List2
    Isabelle_LLVM.IICF
    More_Sepref.WB_More_Refinement
    Watched_Literals_VMTF
begin

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
"mset_nodes (Hp x _ hs) = {#x#} + sum_mset(mset(map mset_nodes hs))"

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

definition encoded_hp_prop :: \<open>('e,'f) hp multiset \<Rightarrow> _\<close> where
  \<open>encoded_hp_prop m = (\<lambda>(prevs,nxts,children, scores). distinct_mset (\<Sum>\<^sub># (mset_nodes `# m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. prevs x = map_option node (hp_prev x m)) \<and>
     (\<forall>m'\<in>#m. \<forall>x \<in># mset_nodes m'. nxts x = map_option node (hp_next x m')) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. children x = map_option node (hp_child x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. scores x = map_option score (hp_node x m)))\<close>

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

lemma encoded_hp_prop_irrelevant:
  assumes \<open>a \<notin># \<Sum>\<^sub># (mset_nodes `# m)\<close> and
    \<open>encoded_hp_prop m (nxts, prevs, children, scores)\<close>
  shows
    \<open>encoded_hp_prop (add_mset (Hp a sc []) m) (nxts(a:= None), prevs(a:=None), children(a:=None), scores(a:=Some sc))\<close>
  using assms by (auto simp: encoded_hp_prop_def)

lemma hp_node_simps[simp]: \<open>hp_node m (Hp m w\<^sub>m ch\<^sub>m) = Some (Hp m w\<^sub>m ch\<^sub>m)\<close>
  by (cases ch\<^sub>m) auto

lemma encoded_hp_prop_link:
  fixes ch\<^sub>m a prevs
  defines \<open>prevs' \<equiv> (if ch\<^sub>m = [] then prevs else prevs (node (hd ch\<^sub>m) := Some (node a)))\<close>
  assumes \<open>encoded_hp_prop (add_mset (Hp m w\<^sub>m ch\<^sub>m) (add_mset a x)) (prevs, nxts, children, scores)\<close>
  shows
    \<open>encoded_hp_prop (add_mset (Hp m w\<^sub>m (a # ch\<^sub>m)) x) (prevs', nxts(node a:= if ch\<^sub>m = [] then None else Some (node (hd ch\<^sub>m))), children(m := Some (node a)), scores(m:=Some w\<^sub>m))\<close>
proof -
  have H[simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a))\<close> \<open>distinct_mset (mset_nodes a)\<close>
    using assms unfolding encoded_hp_prop_def prod.simps
    by (metis distinct_mset_add mset_nodes.simps sum_mset.insert sum_mset_sum_list union_assoc)+
  have K: \<open>xa \<in># mset_nodes a \<Longrightarrow> xa \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>xa \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> xa \<notin># mset_nodes a\<close> for xa
    using H by (auto simp del: H dest!: multi_member_split)
  show ?thesis
    using assms unfolding encoded_hp_prop_def prod.simps
    apply (intro conjI impI ballI)
    subgoal by (auto simp: ac_simps)
    subgoal
      apply (auto simp: prevs'_def hp_prev_skip_hd_children dest: multi_member_split)
      by (metis add_mset_disjoint(1) distinct_mset_add image_msetI in_Union_mset_iff mset_add node_hd_in_sum union_iff)
    subgoal apply simp
      apply (intro conjI impI allI)
      subgoal by (auto dest!: multi_member_split simp: add_mset_eq_add_mset)
      subgoal by (auto dest: multi_member_split)[]
      subgoal by (auto dest!: multi_member_split)[]
      subgoal
        by (auto dest: multi_member_split distinct_mset_union simp: hp_next_skip_hd_children)
      done
    subgoal
      by (auto split: option.splits simp: K)
    subgoal
      by (auto split: option.splits simp: K(2))
    done
qed


definition encoded_hp_prop_list :: \<open>('e,'f) hp multiset \<Rightarrow> ('e,'f) hp list \<Rightarrow> _\<close> where
  \<open>encoded_hp_prop_list m xs  = (\<lambda>(prevs,nxts,children, scores). distinct_mset (\<Sum>\<^sub># (mset_nodes `# m + mset_nodes `# (mset xs))) \<and>
     (\<forall>m'\<in>#m. \<forall>x \<in># mset_nodes m'. nxts x = map_option node (hp_next x m')) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. prevs x = map_option node (hp_prev x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. children x = map_option node (hp_child x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. scores x = map_option score (hp_node x m)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). nxts x = map_option node (hp_next_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). prevs x = map_option node (hp_prev_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). children x = map_option node (hp_child_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). scores x = map_option score (hp_node_children x xs))
  )\<close>


lemma encoded_hp_prop_list_remove_min:
  assumes \<open>encoded_hp_prop_list (add_mset (Hp a b child) xs) [] (prevs, nxts, children, scores)\<close>
  shows \<open>encoded_hp_prop_list xs child (prevs, nxts, children(a:=None), scores(a:=None))\<close>
  using assms
  unfolding encoded_hp_prop_list_def
  by (auto simp: ac_simps)


lemma hp_next_children_hd_simps[simp]:
  \<open>a = node x \<Longrightarrow> distinct_mset (sum_list (map mset_nodes (x # children))) \<Longrightarrow>
  hp_next_children a (x # children) = option_hd children\<close>
  by (cases children) auto

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

  
lemma encoded_hp_prop_list_link:
  fixes m ch\<^sub>m prevs b hp\<^sub>m n nxts children
  defines \<open>prevs\<^sub>0 \<equiv> (if ch\<^sub>m = [] then prevs else prevs (node (hd ch\<^sub>m) := Some n))\<close>
  defines \<open>prevs' \<equiv> (if b = [] then prevs\<^sub>0 else prevs\<^sub>0 (node (hd b) := Some m)) (n:= None)\<close>
  defines \<open>nxts' \<equiv> nxts (m := map_option node (option_hd b), n := map_option node (option_hd ch\<^sub>m))\<close>
  defines \<open>children' \<equiv> children (m := Some n)\<close>
  assumes \<open>encoded_hp_prop_list (xs) (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b) (prevs, nxts, children, scores)\<close>
  shows \<open>encoded_hp_prop_list xs (a @ [Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m)] @ b)
       (prevs', nxts', children', scores)\<close>
proof -
  have dist: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) +
    (\<Sum>\<^sub># (mset_nodes `# xs) + (sum_list (map mset_nodes a) + sum_list (map mset_nodes b)))))\<close>
    and notin:
    \<open>n \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>n \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
    \<open>n \<notin># sum_list (map mset_nodes a)\<close>
    \<open>n \<notin># sum_list (map mset_nodes b)\<close>
    \<open>m \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>m \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
    \<open>m \<notin># sum_list (map mset_nodes a)\<close>
    \<open>m \<notin># sum_list (map mset_nodes b)\<close>
    \<open>n \<noteq> m\<close> and
    nxts1: \<open>(\<forall>m'\<in>#xs. \<forall>x\<in>#mset_nodes m'. nxts x = map_option node (hp_next x m'))\<close> and
    prevs1: ‹(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. prevs x = map_option node (hp_prev x m))\<close> and
    child1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. children x = map_option node (hp_child x m))\<close> and
    scores1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. scores x = map_option score (hp_node x m))\<close> and
    nxts2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     nxts x = map_option node (hp_next_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    prevs2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     prevs x = map_option node (hp_prev_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    child2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    children x = map_option node (hp_child_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    scores x = map_option score (hp_node_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    dist2: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close>
    using assms unfolding encoded_hp_prop_list_def by auto
  have [simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes a)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis distinct_mset_add union_ac(3))
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 group_cancel.add1 group_cancel.add2)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 group_cancel.add1 group_cancel.add2)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    done
  have [simp]: \<open>m \<noteq> node (hd ch\<^sub>m)\<close> \<open>n \<noteq> node (hd ch\<^sub>m)\<close> \<open>(node (hd ch\<^sub>m)) \<notin># sum_list (map mset_nodes b)\<close>
    \<open>node (hd ch\<^sub>m) \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>if \<open>ch\<^sub>m \<noteq> []›
    using dist that notin by (cases ch\<^sub>m; auto dest: multi_member_split; fail)+
  have [simp]: \<open>m \<noteq> node (hd b)\<close> \<open>n \<noteq> node (hd b)\<close> if \<open>b \<noteq> []›
    using dist that notin unfolding encoded_hp_prop_list_def by (cases b; auto; fail)+
  
  define NOTIN where
    \<open>NOTIN x ch\<^sub>n \<equiv> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close> for x and  ch\<^sub>n :: \<open>('a, 'b) hp list\<close>
  have K[unfolded NOTIN_def[symmetric]]: \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes a)\<close>
      \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes b)\<close>
      \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
      \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> \<not>x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<noteq> m\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<noteq> n\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> NOTIN x a\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> NOTIN x b\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<noteq> m\<close> 
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<noteq> n\<close> 
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close> and
    K'[unfolded NOTIN_def[symmetric]]:
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes b)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<noteq> m\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<noteq> n\<close> and
   K''[unfolded NOTIN_def[symmetric]]:
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> (x \<notin># sum_list (map mset_nodes a))\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<noteq> m\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<noteq> n\<close>
    for x
    using dist notin by (auto dest!: multi_member_split simp: NOTIN_def)
  note [simp] = NOTIN_def[symmetric]
  show ?thesis
    using dist2 unfolding encoded_hp_prop_list_def prod.simps assms(1,2,3,4)
    apply (intro conjI impI allI)
    subgoal using assms unfolding encoded_hp_prop_list_def
      by (auto simp: ac_simps simp del: NOTIN_def[symmetric])
    subgoal using nxts1
      by auto
    subgoal using prevs1
      apply (cases ch\<^sub>m; cases b)
      apply (auto)
      apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' distinct_mem_diff_mset mset_add node_in_mset_nodes sum_mset.insert union_iff)
      apply (metis (no_types, lifting) add_mset_disjoint(1) distinct_mset_add mset_add node_in_mset_nodes sum_mset.insert union_iff)+
      done
    subgoal
      using child1
      by auto
    subgoal
      using scores1
      by auto
    subgoal
      using nxts2
      by (auto dest: multi_member_split simp: K hp_next_children_append_single_remove_children)
    subgoal
      using prevs2 supply [cong del] = image_mset_cong
      by (auto simp add:  K K' K'' hp_prev_children_append_single_remove_children hp_prev_skip_hd_children map_option_skip_in_child)
    subgoal
      using child2
      by (auto simp add: K K' K'' hp_child_children_skip_first[of _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_first[of _ \<open>_ # _\<close>, simplified]
        hp_child_children_skip_last[of _ _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_last[of _ \<open>[_]\<close>, simplified] notin
        hp_child_children_skip_last[of _ \<open>[_, _]\<close>, simplified]
        hp_child_children_skip_first[of _ _ \<open>[_]\<close>, simplified]
        split: option.splits)
    subgoal
      using scores2
      by (auto split: option.splits simp: K K' K'' hp_node_children_Cons_if
        ex_hp_node_children_Some_in_mset_nodes
        dest: multi_member_split)
    done
qed


lemma encoded_hp_prop_list_link2:
  fixes m ch\<^sub>m prevs b hp\<^sub>m n nxts children ch\<^sub>n a
  defines \<open>prevs' \<equiv> (if ch\<^sub>n = [] then prevs else prevs (node (hd ch\<^sub>n) := Some m))(m := None, n := map_option node (option_last a))\<close>
  defines \<open>nxts\<^sub>0 \<equiv> (if a = [] then nxts else nxts(node (last a) := Some n))\<close>
  defines \<open>nxts' \<equiv> nxts\<^sub>0 (n := map_option node (option_hd b), m := map_option node (option_hd ch\<^sub>n))\<close>
  defines \<open>children' \<equiv> children (n := Some m)\<close>
  assumes \<open>encoded_hp_prop_list (xs) (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b) (prevs, nxts, children, scores)\<close>
  shows \<open>encoded_hp_prop_list xs (a @ [Hp n w\<^sub>n (Hp m w\<^sub>m ch\<^sub>m # ch\<^sub>n)] @ b)
       (prevs', nxts', children', scores)\<close>
proof -
  have dist: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) +
    (\<Sum>\<^sub># (mset_nodes `# xs) + (sum_list (map mset_nodes a) + sum_list (map mset_nodes b)))))\<close>
    and notin:
    \<open>n \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>n \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
    \<open>n \<notin># sum_list (map mset_nodes a)\<close>
    \<open>n \<notin># sum_list (map mset_nodes b)\<close>
    \<open>m \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>m \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
    \<open>m \<notin># sum_list (map mset_nodes a)\<close>
    \<open>m \<notin># sum_list (map mset_nodes b)\<close>
    \<open>n \<noteq> m\<close> \<open>m \<noteq> n\<close> and
    nxts1: \<open>(\<forall>m'\<in>#xs. \<forall>x\<in>#mset_nodes m'. nxts x = map_option node (hp_next x m'))\<close> and
    prevs1: ‹(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. prevs x = map_option node (hp_prev x m))\<close> and
    child1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. children x = map_option node (hp_child x m))\<close> and
    nxts2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     nxts x = map_option node (hp_next_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    prevs2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     prevs x = map_option node (hp_prev_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    child2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    children x = map_option node (hp_child_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
      scores x = map_option score (hp_node_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. scores x = map_option score (hp_node x m))\<close> and
    dist2: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close>
    using assms unfolding encoded_hp_prop_list_def by auto
  have [simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes a)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes b) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n))))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b))\<close>
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis distinct_mset_add union_ac(3))
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 group_cancel.add1 group_cancel.add2)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 group_cancel.add1 group_cancel.add2)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 union_commute union_lcomm)
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 union_commute union_lcomm)
    using dist apply (smt (verit, del_insts) WB_List_More.distinct_mset_union2 union_commute union_lcomm)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    using dist apply (metis (no_types, lifting) distinct_mset_add union_assoc union_commute)
    done
  have [simp]: \<open>m \<noteq> node (hd ch\<^sub>m)\<close> \<open>n \<noteq> node (hd ch\<^sub>m)\<close> \<open>(node (hd ch\<^sub>m)) \<notin># sum_list (map mset_nodes b)\<close>
    \<open>node (hd ch\<^sub>m) \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>if \<open>ch\<^sub>m \<noteq> []›
    using dist that notin by (cases ch\<^sub>m; auto dest: multi_member_split; fail)+
  have [simp]: \<open>m \<noteq> node (hd b)\<close> \<open>n \<noteq> node (hd b)\<close> if \<open>b \<noteq> []›
    using dist that notin unfolding encoded_hp_prop_list_def by (cases b; auto; fail)+

  define NOTIN where
    \<open>NOTIN x ch\<^sub>n \<equiv> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close> for x and  ch\<^sub>n :: \<open>('a, 'b) hp list\<close>
  have K[unfolded NOTIN_def[symmetric]]: \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes a)\<close>
      \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes b)\<close>
      \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<noteq> m\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>n) \<Longrightarrow> x \<noteq> n\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> NOTIN x a\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> NOTIN x b\<close>
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<noteq> m\<close> 
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<noteq> n\<close> 
    \<open>x \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close> and
    K'[unfolded NOTIN_def[symmetric]]:
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<notin># sum_list (map mset_nodes b)\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<noteq> m\<close>
      \<open>x \<in># sum_list (map mset_nodes a) \<Longrightarrow> x \<noteq> n\<close> and
   K''[unfolded NOTIN_def[symmetric]]:
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> (x \<notin># sum_list (map mset_nodes a))\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<noteq> m\<close>
      \<open>x \<in># sum_list (map mset_nodes b) \<Longrightarrow> x \<noteq> n\<close>
    for x
    using dist notin by (auto dest!: multi_member_split simp: NOTIN_def)
  have [simp]: \<open>node (last a) \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>node (last a) \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close> if \<open>a \<noteq> []\<close>
    using that dist by (cases a rule: rev_cases; cases \<open>last a\<close>; auto; fail)+
  note [simp] = NOTIN_def[symmetric]
  have [iff]: \<open> ch\<^sub>n \<noteq> [] \<Longrightarrow> ma \<in># xs \<Longrightarrow> node (hd ch\<^sub>n) \<in># mset_nodes ma \<longleftrightarrow> False\<close> for ma
    using dist2 apply auto
    by (metis (no_types, lifting) add_mset_disjoint(1) distinct_mset_add insert_DiffM inter_mset_empty_distrib_right node_hd_in_sum sum_mset.insert)
  show ?thesis
    using dist2 unfolding encoded_hp_prop_list_def prod.simps assms(1,2,3,4)
    apply (intro conjI impI allI)
    subgoal using assms unfolding encoded_hp_prop_list_def
      by (auto simp: ac_simps simp del: NOTIN_def[symmetric])
    subgoal using nxts1
      apply (cases a rule: rev_cases)
      apply auto
      by (metis (no_types, lifting) add_diff_cancel_right' distinct_mset_in_diff mset_add node_in_mset_nodes sum_mset.insert union_iff)
    subgoal using prevs1
      by auto
    subgoal
      using child1
      by auto
    subgoal
      using scores1
      by auto
    subgoal
      using nxts2
      by (auto dest: multi_member_split simp: K hp_next_children_append_single_remove_children
        hp_next_children_skip_last_not_last
        notin)
    subgoal
      using prevs2 supply [cong del] = image_mset_cong
      by (auto simp add:  K K' K'' hp_prev_children_append_single_remove_children hp_prev_skip_hd_children map_option_skip_in_child hp_prev_children_skip_first_append[of _ \<open>[_]\<close>, simplified])
    subgoal
      using child2
      by (auto simp add: K K' K'' hp_child_children_skip_first[of _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_first[of _ \<open>_ # _\<close>, simplified]
        hp_child_children_skip_last[of _ _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_last[of _ \<open>[_]\<close>, simplified] notin
        hp_child_children_skip_last[of _ \<open>[_, _]\<close>, simplified]
        hp_child_children_skip_first[of _ _ \<open>[_,_]\<close>, simplified]
        hp_child_children_skip_first[of _ _ \<open>[_]\<close>, simplified]
        split: option.splits)
    subgoal
      using scores2
      by (auto split: option.splits simp: K K' K'' hp_node_children_Cons_if
        ex_hp_node_children_Some_in_mset_nodes
        dest: multi_member_split)
    done
qed

type_synonym ('a, 'b) hp_fun = \<open>(('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'b option))\<close>

definition encoded_hp_prop_list_conc
  :: "'a::linorder set \<times> ('a, 'b) hp_fun \<times> 'a option \<Rightarrow>
     ('a, 'b) hp option \<Rightarrow> bool"
  where
  \<open>encoded_hp_prop_list_conc = (\<lambda>(\<V>, arr, h) x.
  (case x of None \<Rightarrow> encoded_hp_prop_list {#} ([]:: ('a, 'b) hp list) arr \<and> h = None
  | Some x \<Rightarrow> encoded_hp_prop_list {#x#} [] arr \<and> set_mset (mset_nodes x) \<subseteq> \<V> \<and> h = Some (node x)))\<close>

definition encoded_hp_prop_list2_conc
  :: "'a::linorder set \<times> ('a, 'b) hp_fun \<times> 'a option \<Rightarrow>
     ('a, 'b) hp list \<Rightarrow> bool"
  where
  \<open>encoded_hp_prop_list2_conc = (\<lambda>(\<V>, arr, h) x.
  (encoded_hp_prop_list {#} x arr \<and> set_mset (sum_list (map mset_nodes x)) \<subseteq> \<V> \<and> h = None))\<close>


interpretation VSIDS: pairing_heap where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done
hide_const (open) NEMonad.ASSERT NEMonad.RETURN NEMonad.SPEC


definition hp_set_all where
  \<open>hp_set_all i prev nxt child sc = (\<lambda>(prevs, nxts, childs, scores). (prevs(i:=prev), nxts(i:=nxt), childs(i:=child), scores(i:=sc)))\<close>


definition hp_update_prev where
  \<open>hp_update_prev i prev = (\<lambda>(prevs, nxts, childs, scores). (prevs(i:=prev), nxts, childs, scores))\<close>

definition hp_update_nxt where
  \<open>hp_update_nxt i nxt = (\<lambda>(prevs, nxts, childs, scores). (prevs, nxts(i:=nxt), childs, scores))\<close>

definition hp_update_score where
  \<open>hp_update_score i nxt = (\<lambda>(prevs, nxts, childs, scores). (prevs, nxts, childs, scores(i:=nxt)))\<close>


fun hp_read_nxt :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_nxt i (prevs, nxts, childs) = nxts i\<close>
fun hp_read_prev :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_prev i (prevs, nxts, childs) = prevs i\<close>
fun hp_read_child :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_child i (prevs, nxts, childs, scores) = childs i\<close>
fun hp_read_score :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_score i (prevs, nxts, childs, scores) = scores i\<close>

definition hp_insert :: \<open>'a \<Rightarrow> 'b::linorder \<Rightarrow> 'a set \<times> ('a,'b) hp_fun \<times> 'a option \<Rightarrow> ('a set \<times> ('a,'b) hp_fun \<times> 'a option) nres\<close> where
  \<open>hp_insert = (\<lambda>(i::'a) (w::'b) (\<V>::'a set, arr :: ('a, 'b) hp_fun, h :: 'a option). do {
  if h = None then do {
    ASSERT (i \<in> \<V>);
    RETURN (\<V>, hp_set_all i None None None (Some w) arr, Some i)
   } else do {
    ASSERT (i \<in> \<V>);
    let (j::'a) = ((the h) :: 'a);
    ASSERT (j \<in> (\<V>::'a set) \<and> j \<noteq> i);
    ASSERT (hp_read_score j (arr :: ('a, 'b) hp_fun) \<noteq> None);
    ASSERT (hp_read_prev j arr = None \<and> hp_read_nxt j arr = None);
    let y = (the (hp_read_score j arr)::'b);
    if y < w
    then do {
      let arr = hp_set_all i None None (Some j) (Some (w::'b)) (arr::('a, 'b) hp_fun);
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, Some i)
    }
    else do {
      let child = hp_read_child j arr;
      let arr = hp_set_all j None None (Some i) (Some y) arr;
      let arr = hp_set_all i None child None (Some (w::'b)) arr;
      let arr = (if child = None then arr else hp_update_prev (the child) (Some i) arr);
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, h)
    }
   }
  })\<close>

lemma hp_node_node_itself[simp]: \<open>hp_node (node x2) x2 = Some x2\<close>
  by (cases x2) auto

lemma hp_child_hd[simp]: \<open>hp_child x1 (Hp x1 x2 x3) = option_hd x3\<close>
  by (cases x3) auto

lemma encoded_hp_prop_list_encoded_hp_prop[simp]: \<open>encoded_hp_prop_list arr [] h = encoded_hp_prop arr h\<close>
  unfolding encoded_hp_prop_list_def encoded_hp_prop_def by auto

lemma encoded_hp_prop_list_encoded_hp_prop_single[simp]: \<open>encoded_hp_prop_list {#} [arr] h = encoded_hp_prop {#arr#} h\<close>
  unfolding encoded_hp_prop_list_def encoded_hp_prop_def by auto

lemma hp_insert_spec:
  assumes \<open>encoded_hp_prop_list_conc arr h\<close> and
    \<open>h \<noteq> None \<Longrightarrow> i \<notin># mset_nodes (the h)\<close> and
    \<open>i \<in> fst arr\<close>
  shows \<open>hp_insert i w arr \<le> SPEC (\<lambda>arr. encoded_hp_prop_list_conc arr (VSIDS.insert i w h))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), map_option node h)\<close>
    by (cases arr; cases h) (use assms in \<open>auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)

  have enc: \<open>encoded_hp_prop {#Hp i w [the h]#}
    (prevs(i := None), nxts(i := None, node (the h) := None), childs(i \<mapsto> node (the h)), scores(i \<mapsto> w))\<close> and
    enc2: \<open>encoded_hp_prop {#Hp (node (the h)) (score (the h)) (Hp i w [] # hps (the h))#}
   (if hps (the h) = [] then prevs(i := None) else prevs(i := None)(node (hd (hps (the h))) \<mapsto> node (Hp i w [])),
    nxts  (i := None,  node (Hp i w []) := if hps (the h) = [] then None else Some (node (hd (hps (the h))))),
    childs(i := None)(node (the h) \<mapsto> node (Hp i w [])), scores(i \<mapsto> w, node (the h) \<mapsto> score (the h)))\<close> (is ?G)if \<open>h \<noteq> None\<close>
  proof -
    have \<open>encoded_hp_prop {#the h#} (prevs, nxts, childs, scores)\<close>
      using that assms by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def arr)
    then have 0: \<open>encoded_hp_prop {#Hp i w [], the h#}
      (prevs(i := None), nxts(i := None), childs(i := None), scores(i \<mapsto> w))\<close>
      using encoded_hp_prop_irrelevant[of i \<open>{#the h#}\<close> prevs nxts childs scores w] that assms
      by auto
    from encoded_hp_prop_link[OF this]
    show \<open>encoded_hp_prop {#Hp i w [the h]#}
      (prevs(i := None), nxts(i := None, node (the h) := None), childs(i \<mapsto> node (the h)), scores(i \<mapsto> w))\<close>
      by auto
    from 0 have \<open>encoded_hp_prop {#Hp (node (the h)) (score (the h)) (hps (the h)), Hp i w []#}
      (prevs(i := None), nxts(i := None), childs(i := None), scores(i \<mapsto> w))\<close>
      by (cases \<open>the h\<close>) (auto simp: add_mset_commute)
    from encoded_hp_prop_link[OF this]
    show ?G .
  qed

  have [simp]: \<open>encoded_hp_prop {#Hp x1a x2 x3#} (prevs, nxts, childs, scores) \<Longrightarrow> scores x1a = Some x2\<close>
    \<open>encoded_hp_prop {#Hp x1a x2 x3#} (prevs, nxts, childs, scores) \<Longrightarrow> childs x1a = map_option node (option_hd x3)\<close> for x1a x2 x3
    by (auto simp: encoded_hp_prop_def)
  show ?thesis
    using assms
    unfolding hp_insert_def arr prod.simps
    apply refine_vcg
    subgoal
      by auto
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by auto
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      using enc
      by (cases h, simp; cases \<open>the h\<close>)
        (auto simp: hp_set_all_def encoded_hp_prop_list_conc_def fun_upd_idem)
    subgoal
      using enc2
      by (cases h, simp; cases \<open>the h\<close>)
       (auto simp: hp_set_all_def encoded_hp_prop_list_conc_def fun_upd_idem hp_update_prev_def
        fun_upd_twist)
     done
qed

thm hp_insert_def
definition hp_link :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a set \<times> ('a,'b::order) hp_fun \<times> 'a option \<Rightarrow> (('a set \<times> ('a,'b) hp_fun \<times> 'a option) \<times> 'a) nres\<close> where
  \<open>hp_link = (\<lambda>(i::'a) j (\<V>::'a set, arr :: ('a, 'b) hp_fun, h :: 'a option). do {
    ASSERT (i \<noteq> j);
    ASSERT (i \<in> \<V>);
    ASSERT (j \<in> \<V>);
    let x = (the (hp_read_score i arr)::'b);
    let y = (the (hp_read_score j arr)::'b);
    let prev = hp_read_prev i arr;
    let nxt = hp_read_nxt j arr;
    ASSERT (nxt \<noteq> Some i \<and> nxt \<noteq> Some j);
    ASSERT (prev \<noteq> Some i \<and> prev \<noteq> Some j);
    let (parent,ch,w\<^sub>p, w\<^sub>c\<^sub>h) = (if y < x then (i, j, x, y) else (j, i, y, x));
    let child = hp_read_child parent arr;
    ASSERT (child \<noteq> Some i \<and> child \<noteq> Some j);
    let child\<^sub>c\<^sub>h = hp_read_child ch arr;
    ASSERT (child\<^sub>c\<^sub>h \<noteq> Some i \<and> child\<^sub>c\<^sub>h \<noteq> Some j \<and> (child\<^sub>c\<^sub>h \<noteq> None \<longrightarrow> child\<^sub>c\<^sub>h \<noteq> child));
    ASSERT (distinct ([i, j] @ (if child\<^sub>c\<^sub>h \<noteq> None then [the child\<^sub>c\<^sub>h] else [])
      @ (if child \<noteq> None then [the child] else [])
      @ (if prev \<noteq> None then [the prev] else [])
      @ (if nxt \<noteq> None then [the nxt] else []))
      );
    let arr = hp_set_all parent prev nxt (Some ch) (Some (w\<^sub>p::'b)) (arr::('a, 'b) hp_fun);
    let arr = hp_set_all ch None child child\<^sub>c\<^sub>h (Some (w\<^sub>c\<^sub>h::'b)) (arr::('a, 'b) hp_fun);
    let arr = (if child = None then arr else hp_update_prev (the child) (Some ch) arr);
    let arr = (if nxt = None then arr else hp_update_prev (the nxt) (Some parent) arr);
    let arr = (if prev = None then arr else hp_update_nxt (the prev) (Some parent) arr);
    RETURN ((\<V>, arr :: ('a, 'b) hp_fun, h), parent)
 })\<close>


lemma fun_upd_twist2: "a \<noteq> c \<Longrightarrow> a \<noteq> e \<Longrightarrow> c \<noteq> e \<Longrightarrow> m(a := b, c := d, e := f) = (m(e := f, c := d))(a := b)"
  by auto

lemma hp_link:
  assumes enc: \<open>encoded_hp_prop_list2_conc arr (xs @ x # y # ys)\<close> and
    \<open>i = node x\<close> and
    \<open>j = node y\<close>
  shows \<open>hp_link i j arr \<le> SPEC (\<lambda>(arr, n). encoded_hp_prop_list2_conc arr (xs @ VSIDS.link x y # ys) \<and>
    n = node (VSIDS.link x y))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs @ x # y # ys))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes (xs @ x # y # ys))) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)

  have ij: \<open>i \<noteq> j\<close>
    using dist assms(2,3) by (cases x; cases y) auto
  have xy: \<open>Hp (node x) (score x) (hps x) = x\<close>  \<open>Hp (node y) (score y) (hps y) = y\<close> and
    sc: \<open>score x = the (scores i)\<close> \<open>score y = the (scores j)\<close> and
    link_x_y: \<open>VSIDS.link x y = VSIDS.link (Hp i (the (scores i)) (hps x))
     (Hp j (the (scores j)) (hps y))\<close>
    by (cases x; cases y; use assms in \<open>auto simp: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def arr
      simp del: VSIDS.link.simps\<close>; fail)+
  obtain ch\<^sub>x w\<^sub>x ch\<^sub>y w\<^sub>y where
    x: \<open>x = Hp i w\<^sub>x ch\<^sub>x\<close> and
    y: \<open>y = Hp j w\<^sub>y ch\<^sub>y\<close>
    using assms(2-3)
    by (cases y; cases x) auto
  have sc':
    \<open>scores i = Some w\<^sub>x\<close>
    \<open>scores j = Some w\<^sub>y\<close>
    \<open>prevs i = map_option node (option_last xs)\<close>
    \<open>nxts i = Some j\<close>
    \<open>prevs j = Some i\<close>
    \<open>nxts j = map_option node (option_hd ys)\<close>
    \<open>childs i = map_option node (option_hd ch\<^sub>x)\<close>
    \<open>childs j = map_option node (option_hd ch\<^sub>y)\<close>
    \<open>xs \<noteq> [] \<Longrightarrow> nxts (node (last xs)) = Some i\<close>
    \<open>ys \<noteq> [] \<Longrightarrow> prevs (node (hd ys)) = Some j\<close>
    using assms(1) x y apply (auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def arr hp_child_children_Cons_if)
    apply (smt (verit) assms(3) hp_next_None_notin_children hp_next_children.elims list.discI list.inject list.sel(1) option_hd_Nil option_hd_Some_hd)
    using assms(1) x y apply (cases xs rule: rev_cases; auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def arr)
    apply (metis WB_List_More.distinct_mset_union2 add_diff_cancel_right' assms(2) distinct_mset_in_diff
      hp_next_children_simps(1) hp_next_children_skip_first_append node_in_mset_nodes option.map(2)
      sum_image_mset_sum_map)
    using assms(1) x y apply (cases ys;auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
      encoded_hp_prop_def arr)
      apply (cases \<open>hd ys\<close>)
      apply (auto simp:)
      done

  have diff:
    \<open>nxts j \<noteq> Some j\<close>  \<open>nxts j \<noteq> Some i\<close>  \<open>nxts i \<noteq> Some i\<close>
    \<open>prevs i \<noteq> Some i\<close> \<open>prevs i \<noteq> Some j\<close>
    \<open>childs i \<noteq> Some i\<close> \<open>childs i \<noteq> Some j\<close>
    \<open>childs j \<noteq> Some i\<close> \<open>childs j \<noteq> Some j\<close> \<open>childs i \<noteq> None \<Longrightarrow> childs i \<noteq> childs j\<close>
    \<open>childs j \<noteq> None \<Longrightarrow> childs i \<noteq> childs j\<close>
    \<open>prevs i \<noteq> None \<Longrightarrow> prevs i \<noteq> nxts j\<close>
    using dist sc' unfolding x y apply (cases ys; cases xs rule: rev_cases; auto split: if_splits; fail)+
    using dist sc' unfolding x y apply (cases ys; cases xs rule: rev_cases; cases \<open>last xs\<close>; cases \<open>hd ys\<close>;
      cases ch\<^sub>x; cases ch\<^sub>y; cases \<open>hd ch\<^sub>x\<close>; cases \<open>hd ch\<^sub>y\<close>; auto split: if_splits; fail)+
    done
  have dist2:
    \<open>distinct([i, j]
      @ (if childs i \<noteq> None then [the (childs i)] else [])
      @ (if childs j \<noteq> None then [the (childs j)] else [])
      @ (if prevs i \<noteq> None then [the (prevs i)] else [])
      @ (if nxts j \<noteq> None then [the (nxts j)] else []))\<close>
    using dist sc' unfolding x y by (cases ys; cases xs rule: rev_cases; cases \<open>last xs\<close>; cases \<open>hd ys\<close>;
      cases ch\<^sub>x; cases ch\<^sub>y; cases \<open>hd ch\<^sub>x\<close>; cases \<open>hd ch\<^sub>y\<close>)
       (auto split: if_splits)
  have if_pair: \<open>(if a then (b, c) else (d,f)) = (if a then b else d, if a then c else f)\<close> for a b c d f
    by auto
  have enc0: \<open>encoded_hp_prop_list {#} (xs @ [Hp (node x) (score x) (hps x), Hp (node y) (score y) (hps y)] @ ys) (prevs, nxts, childs, scores)\<close>
    using enc unfolding x y by (auto simp: encoded_hp_prop_list2_conc_def arr)
  then have H: \<open>fst x1= \<V> \<Longrightarrow> snd (snd x1) = None\<Longrightarrow> encoded_hp_prop_list2_conc x1 (xs @ VSIDS.link x y # ys) \<longleftrightarrow>
    encoded_hp_prop_list {#} (xs @ VSIDS.link x y # ys) (fst (snd x1))\<close> for x1
    using dist \<V> unfolding x y
    by (cases x1)
     (simp add: encoded_hp_prop_list2_conc_def)
  show ?thesis
    unfolding hp_link_def arr prod.simps
    apply refine_vcg
    subgoal using ij by auto
    subgoal using dist \<V> by (auto simp: x)
    subgoal using dist \<V> by (auto simp: y)
    subgoal using diff by auto
    subgoal using diff by auto
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using diff by (auto split: if_splits)
    subgoal using dist2 by (clarsimp split: if_splits)
    subgoal premises p for parent b ch ba w\<^sub>p w\<^sub>c x1 x2
      apply (cases \<open>the (scores j) < the (scores i)\<close>)
      subgoal
        apply (subst H)
        using p(1-10) p(12)[symmetric] dist2 \<V>
        apply simp
        using p(1-10) p(12)[symmetric] dist2 \<V>
        apply simp
        apply (subst arg_cong2[THEN iffD1, of _ _ _ _ \<open>encoded_hp_prop_list {#}\<close>, OF _ _ encoded_hp_prop_list_link[of \<open>{#}\<close> xs \<open>node x\<close> \<open>score x\<close> \<open>hps x\<close> \<open>node y\<close> \<open>score y\<close> \<open>hps y\<close> ys
          prevs nxts childs scores, OF enc0]])
        subgoal
          using sc' p(1-10) p(12)[symmetric] dist2 \<V>
          by (simp add: x y)
        subgoal
          using sc' p(1-10) p(12)[symmetric] dist2 \<V>
          apply (simp add: x y)
          apply (intro conjI impI)
          subgoal apply (simp add: fun_upd_idem fun_upd_twist  fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>] hp_set_all_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply auto
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_idem[of \<open>nxts(parent := None)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist[of _ _ prevs])
              apply force
              apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist[of _ _ prevs])
              apply force
              apply (subst fun_upd_idem[of \<open>nxts(ch := None)(parent \<mapsto> node (hd ys))\<close>])
              apply (simp (no_asm_simp))
              apply argo
              apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist[of _ _ prevs])
              apply force
              apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist[of _ _ prevs])
              apply force
              apply (subst fun_upd_idem[of \<open>nxts(parent := None)(ch \<mapsto> node (hd ch\<^sub>x))\<close>])
              apply (simp (no_asm_simp))
              apply argo
              apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist2)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (subst fun_upd_twist[of _ _ \<open>prevs(ch := None)\<close>])
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (simp (no_asm))
              done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
              apply (simp (no_asm_simp))
              apply force
              apply (subst fun_upd_twist2)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (subst fun_upd_twist[of _ _ \<open>prevs(ch := None)\<close>])
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (subst fun_upd_idem[of \<open>nxts(ch \<mapsto> node (hd ch\<^sub>x), parent \<mapsto> node (hd ys))\<close>])
              apply (simp (no_asm_simp))
              apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
              apply (simp (no_asm_simp))
            done
          done
          apply (rule TrueI)
          done
        subgoal
          supply [[goals_limit=1]]
        apply (subst H)
        using p(1-10) p(12)[symmetric] dist2 \<V>
        apply simp
        using p(1-10) p(12)[symmetric] dist2 \<V>
        apply simp
        apply (subst arg_cong2[THEN iffD1, of _ _ _ _ \<open>encoded_hp_prop_list {#}\<close>, OF _ _ encoded_hp_prop_list_link2[of \<open>{#}\<close> xs \<open>node x\<close> \<open>score x\<close> \<open>hps x\<close> \<open>node y\<close> \<open>score y\<close> \<open>hps y\<close> ys
          prevs nxts childs scores, OF enc0]])
        subgoal
          using sc' p(1-10) p(12)[symmetric] dist2 \<V>
          by (simp add: x y)
        subgoal
          using sc' p(1-10) p(12)[symmetric] dist2 \<V>
          apply (simp add: x y)
          apply (intro conjI impI)
          subgoal by (simp add: fun_upd_idem fun_upd_twist  fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>] hp_set_all_def)
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist)
            apply (subst fun_upd_idem[of \<open>(nxts(node (last xs) \<mapsto> parent))\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist[of _ _ nxts])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>prevs(parent := None)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply force
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>(prevs(parent \<mapsto> node (last xs)))(ch := None)\<close>])
            apply (metis fun_upd_apply)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_idem[of \<open>nxts(ch := None)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>prevs(node (hd ch\<^sub>y) \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_idem[of \<open>nxts(_ := _)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ nxts])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>prevs(node (hd ch\<^sub>y) \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_idem[of \<open>prevs(parent := None)(node (hd ch\<^sub>y) \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_idem[of \<open>(prevs(parent \<mapsto> node (last xs)))(ch := None)(node (hd ch\<^sub>y) \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_idem[of \<open>nxts(node (last xs) \<mapsto> parent)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ nxts])
            apply force
            apply (simp (no_asm))
            done
          done
          apply (rule TrueI)
          done
        done
      subgoal premises p
        using p(1-10) p(12)[symmetric] dist2 \<V>
        using sc'
        by (cases \<open>the (scores j) < the (scores i)\<close>)
         (simp_all add: x y split: if_split)
      done
qed


thm VSIDS.pass\<^sub>1.simps VSIDS.pass\<^sub>2.simps
text \<open>In an imperative setting use the two pass approaches is better than the alternative.

The \<^term>\<open>e::nat\<close> of the loop is a dummy counter.\<close>
definition vsids_pass\<^sub>1 where
  \<open>vsids_pass\<^sub>1 = (\<lambda>(\<V>::'a set, arr :: ('a, 'b::order) hp_fun, h :: 'a option) (j::'a). do {
  ((\<V>, arr, h), j, _, n) \<leftarrow> WHILE\<^sub>T(\<lambda>((\<V>, arr, h), j, e, n). j \<noteq> None)
  (\<lambda>((\<V>, arr, h), j, e::nat, n). do {
    if j = None then RETURN ((\<V>, arr, h), None, e, n)
    else do {
    let j = the j;
    let nxt = hp_read_nxt j arr;
    if nxt = None then RETURN ((\<V>, arr, h), nxt, e+1, j)
    else do {
      ASSERT (nxt \<noteq> None);
      let nnxt = hp_read_nxt (the nxt) arr;
      ((\<V>, arr, h), n) \<leftarrow> hp_link j (the nxt) (\<V>, arr, h);
      RETURN ((\<V>, arr, h), nnxt, e+2, n)
   }}
  })
  ((\<V>, arr, h), Some j, 0::nat, j);
  RETURN ((\<V>, arr, h), n)
  })\<close>

lemma sum_list_mset_nodes_pass\<^sub>1 [simp]: \<open>sum_list (map mset_nodes (VSIDS.pass\<^sub>1 (xs))) = sum_list (map mset_nodes xs)\<close>
  apply (induction xs rule: VSIDS.pass\<^sub>1.induct)
  apply auto
  apply (case_tac h1, case_tac h2)
  apply auto
  done

(*TODO Move*)
lemma drop_is_single_iff: \<open>drop e xs = [a] \<longleftrightarrow> last xs = a \<and> e = length xs - 1 \<and> xs \<noteq> []\<close>
  apply auto
  apply (metis append_take_drop_id last_snoc)
  by (metis diff_diff_cancel diff_is_0_eq' length_drop length_list_Suc_0 n_not_Suc_n nat_le_linear)

(*TODO this is the right ordering for the theorems*)
lemma distinct_mset_mono': \<open>distinct_mset D \<Longrightarrow> D' \<subseteq># D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

lemma pass\<^sub>1_append_even: \<open>even (length xs) \<Longrightarrow> VSIDS.pass\<^sub>1 (xs @ ys) = VSIDS.pass\<^sub>1 xs @ VSIDS.pass\<^sub>1 ys\<close>
  by (induction xs rule: VSIDS.pass\<^sub>1.induct) auto

lemma last_pass\<^sub>1[simp]: "odd (length xs) \<Longrightarrow> last (VSIDS.pass\<^sub>1 xs) = last xs"
  by (metis VSIDS.pass\<^sub>1.simps(2) append_butlast_last_id even_Suc last_snoc length_append_singleton
    length_greater_0_conv odd_pos pass\<^sub>1_append_even)

lemma vsids_pass\<^sub>1:
  fixes arr :: \<open>'a::linorder set \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr xs\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (hd xs)\<close>
  shows \<open>vsids_pass\<^sub>1 arr j \<le> SPEC(\<lambda>(arr, j). encoded_hp_prop_list2_conc arr (VSIDS.pass\<^sub>1 xs) \<and> j = node (last (VSIDS.pass\<^sub>1 xs)))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  define I where \<open>I \<equiv> (\<lambda>(arr, nnxt::'a option, e, k).
    encoded_hp_prop_list2_conc arr (VSIDS.pass\<^sub>1(take e xs) @ drop e xs) \<and> nnxt = map_option node (option_hd (drop (e) xs)) \<and>
    e \<le> (length xs) \<and> (nnxt = None \<longleftrightarrow> e = length xs) \<and> (nnxt \<noteq> None \<longrightarrow> even e) \<and>
    k = (if e=0 then j else node (last (VSIDS.pass\<^sub>1(take e xs)))))\<close>
  have I0: \<open>I ((\<V>, (prevs, nxts, childs, scores), None), Some j, 0, j)\<close>
    using assms unfolding I_def prod.simps
    by (cases xs, auto simp: arr; fail)+
  have I_no_next: \<open>I ((\<V>, arr, ch'), None, Suc e, y)\<close>
    if \<open>I ((\<V>, arr, ch'), Some y, e, n)\<close> and
      \<open>hp_read_nxt y arr = None\<close>
    for s a b prevs x2 nxts children x1b x2b x1c x2c x1d x2d arr e y ch' \<V> n
  proof -
    have \<open>e = length xs - 1\<close> \<open>xs \<noteq> []\<close>
      using that
      apply (cases \<open>drop e xs\<close>; cases \<open>hd (drop e xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def)
      apply (subst (asm) hp_next_children_hd_simps)
      apply simp
      apply simp
      apply (rule distinct_mset_mono)
        prefer 2
      apply assumption
      apply (auto simp: drop_is_single_iff)
      using that
      apply (auto simp: I_def)
      done
    then show ?thesis
      using that pass\<^sub>1_append_even[of \<open>butlast xs\<close> \<open>[last xs]\<close>]
      by (auto simp: I_def)
  qed

  have link_pre1: \<open>encoded_hp_prop_list2_conc (x1, x1a, x2a)
    (VSIDS.pass\<^sub>1 (take x2b xs) @
    xs!x2b # xs!(Suc x2b) # drop (x2b+2) xs)\<close> (is ?H1) and
    link_pre2: \<open>the x1b = node (xs ! x2b)\<close>  (is ?H2) and
    link_pre3: \<open>the (hp_read_nxt (the x1b) x1a) = node (xs ! Suc x2b)\<close> (is ?H3) 
    if \<open>I s\<close> and
      s: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, e, n). j \<noteq> None) xa\<close>
      \<open>s = (a, b)\<close>
      "x2b' = (x2b, j)"
      \<open>b = (x1b, x2b')\<close>
      ‹x2 = (x1a, x2a)\<close>
      \<open>a = (x1, x2)\<close>
      ‹x1b \<noteq> None\<close> and
      nxt: ‹hp_read_nxt (the x1b) x1a \<noteq> None\<close>
    for s a b x1 x2 x1a x2a x1b x2b j x2b'
  proof -
    have \<open>encoded_hp_prop_list {#} (VSIDS.pass\<^sub>1 (take x2b xs) @ drop x2b xs) x1a\<close>
      \<open>x2b < length xs\<close>
      \<open>x1b = Some (node (hd (drop x2b xs)))\<close>
      using that
      by (auto simp: I_def encoded_hp_prop_list2_conc_def)
    then have \<open>drop x2b xs \<noteq> []\<close> \<open>tl (drop x2b xs) \<noteq> []\<close> \<open>Suc x2b < length xs\<close> \<open>the x1b = node (xs ! x2b)\<close>
      \<open>the (hp_read_nxt (the x1b) x1a) = node (xs ! Suc x2b)\<close>
      using nxt unfolding s apply -
      apply (cases \<open>drop x2b xs\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (cases \<open>drop x2b xs\<close>; cases \<open>hd (drop x2b xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (cases \<open>drop x2b xs\<close>; cases \<open>hd (drop x2b xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (smt (verit) Suc_le_eq append_eq_conv_conj hp_next_None_notin_children
        hp_next_children.elims length_Suc_conv_rev list.discI list.inject nat_less_le
        option_last_Nil option_last_Some_iff(2))
      apply (cases \<open>drop x2b xs\<close>; cases \<open>hd (drop x2b xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (subst (asm) hp_next_children_hd_simps)
      apply simp
      apply simp
      apply (rule distinct_mset_mono')
      apply assumption
      apply (auto simp: drop_is_single_iff)
      apply (metis hd_drop_conv_nth hp.sel(1) list.sel(1))
      apply (cases \<open>drop x2b xs\<close>; cases \<open>tl (drop x2b xs)\<close>; cases \<open>hd (drop x2b xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      by (metis Cons_nth_drop_Suc list.inject nth_via_drop)
    then show ?H1
      using that \<open>x2b < length xs\<close>
      by (cases \<open>drop x2b xs\<close>; cases \<open>tl (drop x2b xs)\<close>)
        (auto simp: I_def encoded_hp_prop_list2_conc_def Cons_nth_drop_Suc)
    show ?H2 ?H3 using \<open>the x1b = node (xs ! x2b)\<close>
      \<open>the (hp_read_nxt (the x1b) x1a) = node (xs ! Suc x2b)\<close> by fast+
  qed
  have I_Suc_Suc: \<open>I ((x2c, x2d, xe), hp_read_nxt (the (hp_read_nxt (the nxt) x2a)) x2a, k + 2, n)\<close>
    if 
      inv: \<open>I s\<close> and
      brk: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, e, n). j \<noteq> None) xa\<close> and
      st: \<open>s = (arr2, b)\<close>
        \<open>b = (nxt, k')\<close>
        \<open>k' = (k, j)\<close>
        \<open>x1a = (x2a, x1b)\<close>
        \<open>arr2 = (\<V>', x1a)\<close> 
        \<open>linkedn = (linked, n)\<close>
        \<open>x1d = (x2d, xe)\<close>
        \<open>linked = (x2c, x1d)\<close> and
      nxt: \<open>nxt \<noteq> None\<close> and
      nxts: \<open>hp_read_nxt (the nxt) x2a \<noteq> None\<close>
        \<open>hp_read_nxt (the nxt) x2a \<noteq> None\<close> and
      linkedn: \<open>case linkedn of
      (arr, n) \<Rightarrow>
      encoded_hp_prop_list2_conc arr
      (VSIDS.pass\<^sub>1 (take k xs) @ VSIDS.link (xs ! k) (xs ! Suc k) # drop (k + 2) xs) \<and>
      n = node (VSIDS.link (xs ! k) (xs ! Suc k))\<close>
    for s arr2 b \<V>' x1a x2a x1b nxt k linkedn linked n x2c x1d x2d xe j k'
  proof -
    have enc: \<open>encoded_hp_prop_list {#} (VSIDS.pass\<^sub>1 (take k xs) @ drop k xs) x2a\<close>
      \<open>k < length xs\<close>
      \<open>nxt = Some (node (hd (drop k xs)))\<close> and
      dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (VSIDS.pass\<^sub>1 (take k xs) @ drop k xs))))\<close>
      using that
      by (auto simp: I_def encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def)

    then have \<open>drop k xs \<noteq> []\<close> \<open>tl (drop k xs) \<noteq> []\<close> \<open>Suc k < length xs\<close> \<open>the nxt = node (xs ! k)\<close>
      using nxt unfolding st apply -
      apply (cases \<open>drop k xs\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (cases \<open>drop k xs\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (cases \<open>drop k xs\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (metis hp_read_nxt.simps option.sel that(12))
      apply (cases \<open>drop k xs\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (subst (asm) hp_next_children_hd_simps)
      apply simp
      apply simp
      apply (rule distinct_mset_mono')
      apply assumption
      apply (auto simp: drop_is_single_iff)
      apply (metis Some_to_the Suc_lessI drop_eq_ConsD drop_eq_Nil2 hp_read_nxt.simps nat_in_between_eq(1) option.map(1) option_hd_Nil that(12))
      apply (cases \<open>drop k xs\<close>; cases \<open>tl (drop k xs)\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      apply (metis hp.sel(1) nth_via_drop)
      by (metis hp.sel(1) nth_via_drop)
    then have le: \<open>Suc (Suc k) \<le> length xs\<close>
      using enc nxts unfolding st nxt apply -
      apply (cases \<open>drop k xs\<close>; cases \<open>tl (drop k xs)\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def)
      done
    have take_nth: \<open>take (Suc (Suc k)) xs = take k xs @ [xs!k, xs!Suc k]\<close>
      using le by (auto simp: take_Suc_conv_app_nth)
    have nnxts: \<open>hp_read_nxt (the (hp_read_nxt (node (hd (drop k xs))) x2a)) x2a =
      map_option node (option_hd (drop (Suc (Suc k)) xs))\<close>
      using enc nxts le  \<open>tl (drop k xs) \<noteq> []\<close> unfolding st nxt apply -
      apply (cases \<open>drop k xs\<close>; cases \<open>tl (drop k xs)\<close>; cases \<open>hd (tl (drop k xs))\<close>; cases \<open>hd (drop k xs)\<close>)
      apply (auto simp: I_def encoded_hp_prop_list_def arr)
      apply (subst hp_next_children_hd_simps)
      apply (solves simp)
      apply (rule distinct_mset_mono'[OF dist])
      by (auto simp: drop_is_single_iff drop_Suc_nth)
    show ?thesis
      using inv nxt le linkedn nnxts
      unfolding st
      by (auto simp: I_def take_Suc take_nth pass\<^sub>1_append_even)
  qed

  show ?thesis
    unfolding vsids_pass\<^sub>1_def arr prod.simps
    apply (refine_vcg WHILET_rule[where I=I and R = \<open>measure (\<lambda>(arr, nnxt::'a option, e, _). length xs -e)\<close>]
      hp_link)
    subgoal by auto
    subgoal by (rule I0)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal for s a b x1 x2 x1a x2a x1b x2b
      by (auto simp: I_no_next)
    subgoal by (auto simp: I_def)
    apply (rule link_pre1; assumption?)
    apply (rule link_pre2; assumption)
    subgoal premises p for s a b x1 x2 x1a x2a x1b x2b
      using link_pre3[OF p(1-8)] p(9-)
      by auto
    subgoal for s arr2 b \<V>' x1a x2a x1b nxt k linkedn linked n x2c x1d x2d xe
      by (rule I_Suc_Suc)
    subgoal
      by (auto simp: I_def)
    subgoal
      by (auto simp: I_def)
    subgoal
      using assms
      by (auto simp: I_def)
    done
qed

definition vsids_pass\<^sub>2 where
  \<open>vsids_pass\<^sub>2 = (\<lambda>(\<V>::'a set, arr :: ('a, 'b::order) hp_fun, h :: 'a option) (j::'a). do {
  let nxt = hp_read_prev j arr;
  ((\<V>, arr, h), j, leader, _) \<leftarrow> WHILE\<^sub>T(\<lambda>((\<V>, arr, h), j, leader, e). j \<noteq> None)
  (\<lambda>((\<V>, arr, h), j, leader, e::nat). do {
    if j = None then RETURN ((\<V>, arr, h), None, leader, e)
    else do {
    let j = the j;
      let nnxt = hp_read_prev j arr;
      ((\<V>, arr, h), n) \<leftarrow> hp_link j leader (\<V>, arr, h);
      RETURN ((\<V>, arr, h), nnxt, n, e+1)
   }
  })
  ((\<V>, arr, h), nxt, j, 1::nat);
  RETURN (\<V>, arr, Some leader)
  })\<close>

lemma pass\<^sub>2_None_iff[simp]: \<open>VSIDS.pass\<^sub>2 list = None \<longleftrightarrow> list = []\<close>
  by (cases list)
   auto

lemma vsids_pass\<^sub>2:
  fixes arr :: \<open>'a::linorder set \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr xs\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (last xs)\<close>
  shows \<open>vsids_pass\<^sub>2 arr j \<le> SPEC(\<lambda>(arr). encoded_hp_prop_list_conc arr (VSIDS.pass\<^sub>2 xs))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  have prevs_lastxs: \<open>prevs (node (last xs)) = map_option node (option_last (butlast xs))\<close>
    using assms
    by (cases xs rule: rev_cases; cases \<open>last xs\<close>)
     (auto simp: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def arr)

  define I where \<open>I \<equiv> (\<lambda>(arr, nnxt::'a option, leader, e'). let e = length xs - e' in
    encoded_hp_prop_list2_conc arr (take e xs @ [the (VSIDS.pass\<^sub>2 (drop e xs))]) \<and> nnxt = map_option node (option_last (take e xs)) \<and>
    leader = node (the (VSIDS.pass\<^sub>2 (drop e xs))) \<and>
    e \<le> (length xs) \<and> (nnxt = None \<longleftrightarrow> e = 0) \<and> e' > 0)\<close>
  have I0: \<open>I ((\<V>, (prevs, nxts, childs, scores), None), hp_read_prev j (prevs, nxts, childs, scores), j, 1)\<close>
    using assms prevs_lastxs unfolding I_def prod.simps Let_def
    by (auto simp: arr butlast_Nil_iff)
  have links_pre1: \<open>encoded_hp_prop_list2_conc (\<V>', arr', h')
    (take (length xs - Suc e) xs @
    xs ! (length xs - Suc e) #
    the (VSIDS.pass\<^sub>2 (drop (length xs - e) xs)) # [])\<close> (is ?H1) and
    links_pre2: \<open>the x1b = node (xs ! (length xs - Suc e))\<close> (is ?H2) and
    links_pre3: \<open>leader = node (the (VSIDS.pass\<^sub>2 (drop (length xs - e) xs)))\<close> (is ?H3)
    if 
      I: \<open>I s\<close> and
      brk: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, leader, e). j \<noteq> None) xa\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>x2b = (leader, e)\<close>
        \<open>b = (x1b, x2b)\<close>
        \<open>xy = (arr', h')\<close>
        \<open>a = (\<V>', xy)\<close> and
      no_None: \<open>x1b \<noteq> None\<close>
    for s a b \<V>' xy arr' h' x1b x2b x1c x2c e leader
  proof -
    have \<open>e < length xs\<close> \<open>length xs - e < length xs\<close>
      using I brk no_None
      unfolding st I_def
      by (auto simp: I_def Let_def)
    then have take_Suc: \<open>take (length xs - e) xs = take (length xs - Suc e) xs @ [xs ! (length xs - Suc e)]\<close>
      using I brk take_Suc_conv_app_nth[of "length xs - Suc e" xs]
      unfolding st
      apply (cases \<open>take (length xs - e) xs\<close> rule: rev_cases)
      apply (auto simp: I_def Let_def)
      done

    then show ?H1
      using I brk unfolding st
      apply (cases \<open>take (length xs - e) xs\<close> rule: rev_cases)
      apply (auto simp: I_def Let_def)
      done
    show ?H2
      using I brk unfolding st I_def Let_def
      by (auto simp: take_Suc)
    show ?H3
      using I brk unfolding st I_def Let_def
      by (auto simp: take_Suc)
  qed
  have I_Suc: \<open>I ((x1d, x1e, x2e), hp_read_prev (the x1b) x1a, new_leader, e + 1)\<close>
    if 
      I: \<open>I s\<close> and
      brk: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, leader, e). j \<noteq> None) xa\<close> and
      st: \<open>s = (a, b)\<close>
        \<open>x2b = (x1c, e)\<close>
        \<open>b = (x1b, x2b)\<close>
        \<open>x2 = (x1a, x2a)\<close>
        \<open>a = (\<V>', x2)\<close>
        \<open>linkedn = (linked, new_leader)\<close>
        \<open>x2d = (x1e, x2e)\<close>
        \<open>linked = (x1d, x2d)\<close> and
      no_None: \<open>x1b \<noteq> None\<close> and
      \<open>case linkedn of
      (arr, n) \<Rightarrow>
      encoded_hp_prop_list2_conc arr
      (take (length xs - Suc e) xs @
      [VSIDS.link (xs ! (length xs - Suc e)) (the (VSIDS.pass\<^sub>2 (drop (length xs - e) xs)))]) \<and>
      n =
      node
      (VSIDS.link (xs ! (length xs - Suc e)) (the (VSIDS.pass\<^sub>2 (drop (length xs - e) xs))))\<close>
    for s a b \<V>' x2 x1a x2a x1b x2b x1c e linkedn linked new_leader x1d x2d x1e x2e
  proof -
    have e: \<open>e < length xs\<close> \<open>length xs - e < length xs\<close>
      using I brk no_None
      unfolding st I_def
      by (auto simp: I_def Let_def)
    then have [simp]: \<open>VSIDS.link (xs ! (length xs - Suc e)) (the (VSIDS.pass\<^sub>2 (drop (length xs - e) xs)))  =
      the (VSIDS.pass\<^sub>2 (drop (length xs - Suc e) xs))\<close>
      using that
      by (auto simp: I_def Let_def simp flip: Cons_nth_drop_Suc split: option.split)
    have [simp]: \<open>hp_read_prev (node (last (take (length xs - e) xs))) x1a = map_option node (option_last (take (length xs - Suc e) xs))\<close>
      using e I  take_Suc_conv_app_nth[of "length xs - Suc e" xs] unfolding I_def st Let_def
      by (cases \<open>(take (length xs - e) xs)\<close> rule: rev_cases; cases \<open>last (take (length xs - e) xs)\<close>)
       (auto simp: encoded_hp_prop_list2_conc_def
        encoded_hp_prop_list_def)
    show ?thesis
      using that e by (auto simp: I_def Let_def)
  qed

  show ?thesis
    unfolding vsids_pass\<^sub>2_def arr prod.simps
    apply (refine_vcg WHILET_rule[where I=I and R = \<open>measure (\<lambda>(arr, nnxt::'a option, _, e). length xs -e)\<close>]
      hp_link)
    subgoal by auto
    subgoal by (rule I0)
    subgoal by auto
    subgoal by auto
    apply (rule links_pre1; assumption)
    subgoal
      by (rule links_pre2)
    subgoal
      by (rule links_pre3)
    subgoal
      by (rule I_Suc)
    subgoal for s a b \<V>' x2 x1a x2a x1b x2b x1c e linkedn linked new_leader x1d x2d x1e x2e
      by (auto simp: I_def Let_def)
    subgoal using assms by (auto simp: I_def Let_def
      encoded_hp_prop_list_conc_def encoded_hp_prop_list2_conc_def
      split: option.split)
    done
qed

definition merge_pairs where
  "merge_pairs arr j = do {
    (arr, j) \<leftarrow> vsids_pass\<^sub>1 arr j;
    vsids_pass\<^sub>2 arr j
  }"


lemma vsids_merge_pairs:
  fixes arr :: \<open>'a::linorder set \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr xs\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (hd xs)\<close>
  shows \<open>merge_pairs arr j \<le> SPEC(\<lambda>(arr). encoded_hp_prop_list_conc arr (VSIDS.merge_pairs xs))\<close>
proof -
  show ?thesis
    unfolding merge_pairs_def
    apply (refine_vcg vsids_pass\<^sub>1 vsids_pass\<^sub>2[of _ "VSIDS.pass\<^sub>1 xs"])
    apply (rule assms)+
    subgoal by auto
    subgoal using assms by (cases xs rule: VSIDS.pass\<^sub>1.cases) auto
    subgoal using assms by auto
    subgoal by (auto simp: VSIDS.pass12_merge_pairs)
    done
qed


definition hp_update_child where
  \<open>hp_update_child i nxt = (\<lambda>(prevs, nxts, childs, scores). (prevs, nxts, childs(i:=nxt), scores))\<close>

definition vsids_pop_min :: \<open>_\<close> where
  \<open>vsids_pop_min = (\<lambda>(\<V>::'a set, arr :: ('a, 'b::order) hp_fun, h :: 'a option). do {
  if h = None then RETURN (None, (\<V>, arr, h))
  else do {
      let j = hp_read_child (the h) arr;
      if j = None then RETURN (h, (\<V>, arr, None))
      else do {
        let arr = hp_update_child (the h) None arr;
        let arr = hp_update_score (the h) None arr;
        arr \<leftarrow> merge_pairs (\<V>, arr, None) (the j);
        RETURN (h, arr)
      }
    }
  })\<close>


lemma get_min2_alt_def: \<open>get_min2 (Some h) = node h\<close>
  by (cases h) auto

lemma vsids_pop_min:
  fixes arr :: \<open>'a::linorder set \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list_conc arr h\<close>
  shows \<open>vsids_pop_min arr \<le> SPEC(\<lambda>(j, arr). j = (if h = None then None else Some (get_min2 h)) \<and> encoded_hp_prop_list_conc arr (VSIDS.del_min h))\<close>
proof -
  show ?thesis
    unfolding vsids_pop_min_def
    apply (refine_vcg vsids_merge_pairs[of _ \<open>case the h of Hp _ _ child \<Rightarrow> child\<close>])
    subgoal using assms by (cases h) (auto simp: encoded_hp_prop_list_conc_def)
    subgoal using assms by (auto simp: encoded_hp_prop_list_conc_def split: option.splits)
    subgoal using assms by (auto simp: encoded_hp_prop_list_conc_def get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms encoded_hp_prop_list_remove_min[of \<open>node (the h)\<close> \<open>score (the h)\<close> \<open>hps (the h)\<close> \<open>{#}\<close>
      \<open>fst (fst (snd arr))\<close> \<open>(fst o snd) (fst (snd arr))\<close> \<open>(fst o snd o snd) (fst (snd arr))\<close>
      \<open>(snd o snd o snd) (fst (snd arr))\<close>]
      by (cases \<open>the h\<close>; cases \<open>fst (snd arr)\<close>)
       (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list2_conc_def
        hp_update_nxt_def hp_update_score_def hp_update_child_def
        get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>h\<close>; cases \<open>the h\<close>)
      (auto simp: get_min2_alt_def VSIDS.pass12_merge_pairs encoded_hp_prop_list_conc_def split: option.splits)
    done
qed

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

lemma hp_parent_hp_child:
  \<open>distinct_mset ((mset_nodes (a::(nat,nat)hp))) \<Longrightarrow> hp_child n a \<noteq> None \<Longrightarrow> map_option node (hp_parent (node (the (hp_child n a))) a) = Some n\<close>
  apply (induction n a rule: hp_child.induct)
  subgoal for  n a sc x children
    apply (simp add: hp_parent_simps_if)
    apply auto
    subgoal for y
      apply (auto simp add: hp_parent_simps_if hp_parent_children_Some_iff 
        split: option.splits dest: distinct_mset_union)
      apply (metis (no_types, lifting) diff_single_trivial disjunct_not_in distinct_mem_diff_mset
        distinct_mset_add hp_parent_None_notin mset_cancel_union(2) mset_nodes.simps node_in_mset_nodes
        option_last_Nil option_last_Some_iff(2) sum_mset_sum_list)
      done
    subgoal for y
      using distinct_mset_union[of \<open>mset_nodes x\<close> \<open>sum_list (map mset_nodes children)\<close>]
        distinct_mset_union[of \<open>sum_list (map mset_nodes children)\<close> \<open>mset_nodes x\<close> ]
      apply (auto simp add: hp_parent_simps_if ac_simps hp_parent_children_cons
        split: option.splits dest: distinct_mset_union)
      apply (metis Groups.add_ac(2) add_mset_add_single disjunct_not_in distinct_mset_add hp_parent_None_notin member_add_mset mset_nodes.simps option_last_Nil option_last_Some_iff(2) sum_mset_sum_list)
      by (smt (verit, best) get_min2.simps get_min2_alt_def hp.inject hp_parent.elims hp_parent_simps(2) option_last_Nil option_last_Some_iff(2))
    done
  subgoal by auto
  done


lemma hp_child_hp_parent:
  \<open>distinct_mset ((mset_nodes (a::(nat,nat)hp))) \<Longrightarrow> hp_parent n a \<noteq> None \<Longrightarrow> map_option node (hp_child (node (the (hp_parent n a))) a) = Some n\<close>
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
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> hp_parent_children a (VSIDS.remove_key_children a xs) = None\<close>
  apply (induction a xs rule: VSIDS.remove_key_children.induct)
  subgoal by auto
  subgoal for k x n c xs
    apply (auto simp: hp_parent_simps_if hp_parent_children_cons
      split: option.split
      dest: WB_List_More.distinct_mset_union2)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in
      distinct_mset_add hp.sel(1) hp_parent_simps_single_if list.map(2) list.sel(1) list.simps(3)
      node_hd_in_sum node_in_mset_nodes option_last_Nil option_last_Some_iff(2) sum_list_simps(2)) 
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in
      distinct_mset_add hp.sel(1) hp_parent_simps_single_if list.map(2) list.sel(1) list.simps(3)
      node_hd_in_sum node_in_mset_nodes option_last_Nil option_last_Some_iff(2) sum_list_simps(2))
   done
  done

lemma remove_key_children_notin_unchanged[simp]: \<open>x \<notin># sum_list (map mset_nodes c) \<Longrightarrow> VSIDS.remove_key_children x c = c\<close>
  by (induction x c rule: VSIDS.remove_key_children.induct)
     auto

lemma remove_key_notin_unchanged[simp]: \<open>x \<notin># mset_nodes c \<Longrightarrow> VSIDS.remove_key x c = Some c\<close>
  by (induction x c rule: VSIDS.remove_key.induct)
     auto

lemma remove_key_remove_all: \<open>k \<notin># \<Sum>\<^sub># (mset_nodes `# mset (VSIDS.remove_key_children k c))\<close>
  by (induction k c rule: VSIDS.remove_key_children.induct) auto

lemma hd_remove_key_node_same: \<open>c \<noteq> [] \<Longrightarrow> VSIDS.remove_key_children k c \<noteq> [] \<Longrightarrow>
  node (hd (VSIDS.remove_key_children k c)) = node (hd c) \<longleftrightarrow> node (hd c) \<noteq> k\<close>
  using remove_key_remove_all[of k]
  apply (induction k c rule: VSIDS.remove_key_children.induct)
  apply (auto)[]
  by fastforce

lemma hd_remove_key_node_same': \<open>c \<noteq> [] \<Longrightarrow> VSIDS.remove_key_children k c \<noteq> [] \<Longrightarrow>
  node (hd c) = node (hd (VSIDS.remove_key_children k c)) \<longleftrightarrow> node (hd c) \<noteq> k\<close>
  using hd_remove_key_node_same[of c k] by auto

lemma remove_key_children_node_hd[simp]: \<open>c \<noteq> [] \<Longrightarrow> VSIDS.remove_key_children (node (hd c)) c= VSIDS.remove_key_children (node (hd c)) (tl c)\<close>
  by (cases c; cases \<open>tl c›; cases \<open>hd c\<close>)
     (auto simp: )

lemma VSIDS_remove_key_children_alt_def:
  \<open>VSIDS.remove_key_children k xs = map (\<lambda>x. case x of Hp a b c \<Rightarrow> Hp a b (VSIDS.remove_key_children k c)) (filter (\<lambda>n. node n \<noteq> k) xs)\<close>
  by (induction k xs rule: VSIDS.remove_key_children.induct) auto

lemma not_orig_notin_remove_key: \<open>b \<notin># sum_list (map mset_nodes xs) \<Longrightarrow>
  b \<notin># sum_list (map mset_nodes (VSIDS.remove_key_children a xs))\<close>
  by (induction a xs rule: VSIDS.remove_key_children.induct) auto

lemma hp_parent_None_notin_same_hd[simp]: \<open>b \<notin># sum_list (map mset_nodes x3) \<Longrightarrow> hp_parent b (Hp b x2 x3) = None\<close>
  by (induction x3 rule: induct_list012)
   (auto simp: hp_parent_children_cons hp_parent.simps(1) filter_empty_conv split: if_splits)

(*does not hold for the children of a*)
lemma hp_parent_children_remove_key_children:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> a \<noteq> b \<Longrightarrow>  hp_parent_children b (VSIDS.remove_key_children a xs) = hp_parent_children b xs\<close>
  oops


lemma hp_parent_remove_key:
  \<open>distinct_mset ((mset_nodes xs)) \<Longrightarrow> a \<noteq> node xs \<Longrightarrow> hp_parent a (the (VSIDS.remove_key a xs)) = None\<close>
  apply (induction a xs rule: VSIDS.remove_key.induct)
  subgoal for a b sc children
    apply (cases \<open>VSIDS.remove_key_children a children\<close>)
    apply (auto simp: hp_parent_simps_if)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims distinct_mset_add empty_iff
        hp.sel(1) inter_iff list.map(2) list.sel(1) list.simps(3) node_hd_in_sum node_in_mset_nodes set_mset_empty sum_list_simps(2))
    by (metis hp_parent_children_remove_key_children mset_map sum_mset_sum_list)
  done

lemma find_key_children_None_or_itself[simp]:
  \<open>VSIDS.find_key_children a h \<noteq> None \<Longrightarrow> node (the (VSIDS.find_key_children a h)) = a\<close>
  by (induction a h rule: VSIDS.find_key_children.induct)
   (auto split: option.splits)

lemma find_key_None_or_itself[simp]:
  \<open>VSIDS.find_key a h \<noteq> None \<Longrightarrow> node (the (VSIDS.find_key a h)) = a\<close>
  apply (induction a h rule: VSIDS.find_key.induct)
  apply auto
  using find_key_children_None_or_itself by fastforce

lemma find_key_children_notin[simp]:
  \<open>a \<notin>#  \<Sum>\<^sub># (mset_nodes `# mset xs) \<Longrightarrow> VSIDS.find_key_children a xs = None\<close>
  by (induction a xs rule: VSIDS.find_key_children.induct) auto


lemma find_key_notin[simp]:
  \<open>a \<notin># mset_nodes h \<Longrightarrow> VSIDS.find_key a h = None\<close>
  by (induction a h rule: VSIDS.find_key.induct) auto

lemma mset_nodes_find_key_children_subset:
  \<open>VSIDS.find_key_children a h \<noteq> None \<Longrightarrow> mset_nodes (the (VSIDS.find_key_children a h)) \<subseteq># \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  apply (induction a h rule: VSIDS.find_key_children.induct)
  apply (auto split: option.splits simp: ac_simps intro: mset_le_incr_right)
  apply (metis mset_le_incr_right union_commute union_mset_add_mset_right)+
  done

lemma hp_parent_None_iff_children_None:
  \<open>hp_parent z (Hp x n c) = None \<longleftrightarrow> (c \<noteq> [] \<longrightarrow> z \<noteq> node (hd c)) \<and> hp_parent_children (z) c = None\<close>
  by (cases c; cases \<open>tl c\<close>)
  (auto simp: hp_parent_children_cons hp_parent_simps_if hp_parent.simps(1) filter_empty_conv split: option.splits)


lemma mset_nodes_find_key_subset:
  \<open>VSIDS.find_key a h \<noteq> None \<Longrightarrow> mset_nodes (the (VSIDS.find_key a h)) \<subseteq># mset_nodes h\<close>
  apply (induction a h rule: VSIDS.find_key.induct)
  apply (auto intro: mset_nodes_find_key_children_subset)
  by (metis mset_nodes_find_key_children_subset option.distinct(2) option.sel subset_mset_imp_subset_add_mset sum_image_mset_sum_map)

lemma find_key_none_iff[simp]:
  \<open>VSIDS.find_key_children a h = None \<longleftrightarrow> a \<notin># \<Sum>\<^sub># (mset_nodes `# mset h)\<close>
  by (induction a h rule: VSIDS.find_key_children.induct) auto

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
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs)) \<Longrightarrow> a \<noteq> b \<Longrightarrow>  hp_parent_children b (VSIDS.remove_key_children a xs) =
  (if VSIDS.find_key_children b xs \<noteq> None then None else hp_parent_children b xs)\<close>
  oops

lemma in_the_default_empty_iff: \<open>b \<in># the_default {#} M \<longleftrightarrow> M \<noteq> None \<and> b \<in># the M\<close>
  by (cases M) auto

lemma remove_key_children_hd_tl: \<open>distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow> c \<noteq> [] \<Longrightarrow> VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close>
  by (cases c) (auto simp add: disjunct_not_in distinct_mset_add)

lemma in_find_key_children_notin_remove_key:
  \<open>VSIDS.find_key_children k c = Some x2 \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow>
      b \<in># mset_nodes x2 \<Longrightarrow>
      b \<notin># \<Sum>\<^sub>#(mset_nodes `# mset (VSIDS.remove_key_children k c))\<close>
  apply (induction k c rule: VSIDS.remove_key_children.induct)
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

find_theorems hp_parent hp_parent_children None
lemma hp_parent_children_None_hp_parent_iff: \<open>hp_parent_children b list = None \<Longrightarrow> hp_parent b (Hp x n list) = Some x2a \<longleftrightarrow> list \<noteq> [] \<and> node (hd list) = b \<and> x2a = Hp x n list\<close>
  by (cases list; cases \<open>tl list\<close>) (auto simp: hp_parent_simps_if)

lemma hp_parent_children_not_hd_node:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> node (hd c) = node x2a \<Longrightarrow> c \<noteq> [] \<Longrightarrow>  VSIDS.remove_key_children (node x2a) c \<noteq> [] \<Longrightarrow>
    hp_parent_children (node (hd (VSIDS.remove_key_children (node x2a) c))) c = Some x2a \<Longrightarrow> False\<close>
  apply (cases c; cases \<open>tl c\<close>; cases \<open>hd c\<close>)
  apply (auto simp: hp_parent_children_cons
    split: option.splits)
  apply (simp add:  disjunct_not_in distinct_mset_add)
  apply (simp add:  disjunct_not_in distinct_mset_add)
  apply (auto simp add:  disjunct_not_in distinct_mset_add)
    by (metis hp_parent_None_iff_children_None hp_parent_children_None_notin node_hd_in_sum node_in_mset_nodes option_last_Nil option_last_Some_iff(2))
lemma hp_parent_children_hd_tl_None[simp]: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> c \<noteq> [] \<Longrightarrow> a \<in> set (tl c)\<Longrightarrow>  hp_parent_children (node a) c = None\<close>
  apply (cases c)
    apply (auto simp: hp_parent_children_def filter_empty_conv dest!: split_list[of a])
apply (metis add_diff_cancel_left' add_diff_cancel_right' distinct_mset_add distinct_mset_in_diff hp_parent_None_notin node_in_mset_nodes)
  apply (simp add: distinct_mset_add)
  apply (simp add: distinct_mset_add)
  apply (metis (no_types, opaque_lifting) disjunct_not_in hp_parent_None_notin mset_subset_eqD mset_subset_eq_add_right node_in_mset_nodes sum_list_map_remove1 union_commute)
  by (metis WB_List_More.distinct_mset_union2 add_diff_cancel_left' distinct_mem_diff_mset hp_parent_None_notin node_in_mset_nodes sum_list_map_remove1 union_iff)


lemma hp_parent_hp_parent_remove_key_not_None_same:
  \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> x \<notin># \<Sum>\<^sub># (mset_nodes `# mset c) \<Longrightarrow>
  hp_parent b (Hp x n c) = Some x2a \<Longrightarrow> b \<notin># mset_nodes x2a \<Longrightarrow>
    hp_parent b (Hp x n (VSIDS.remove_key_children k c)) = Some x2b \<Longrightarrow>
  VSIDS.remove_key k x2a \<noteq> None \<and> (case VSIDS.remove_key k x2a of Some a \<Rightarrow> (x2b) = a | None \<Rightarrow> node x2a = k)\<close>
  apply (induction k c rule: VSIDS.remove_key_children.induct)
  subgoal by (auto simp: hp_parent_children_cons split: if_splits)
  subgoal for k x n c xs
    using distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>, unfolded add.commute[of  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]]
      distinct_mset_union[of \<open>\<Sum>\<^sub># (mset_nodes `# mset c)\<close>  \<open>\<Sum>\<^sub># (mset_nodes `# mset xs)\<close>]
    apply (auto simp: hp_parent_children_cons VSIDS.remove_key_None_iff split: if_splits option.splits)
    apply (smt (z3) disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_None_notin hp_parent_children_append_case hp_parent_children_append_skip_first hp_parent_children_cons hp_parent_children_hd_None hp_parent_simps_single_if list.sel(1) node_hd_in_sum option.case(2) option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (smt (z3) disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_None_notin hp_parent_children_append_case hp_parent_children_append_skip_first hp_parent_children_cons hp_parent_children_hd_None hp_parent_simps_single_if list.sel(1) node_hd_in_sum option.case(2) option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (smt (z3) disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_None_notin hp_parent_children_append_case hp_parent_children_append_skip_first hp_parent_children_cons hp_parent_children_hd_None hp_parent_simps_single_if list.sel(1) node_hd_in_sum option.case(2) option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (auto simp: hp_parent_children_cons hp_parent_simps_single_if  handy_if_lemma split: if_splits option.splits )[]
    apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>VSIDS.remove_key_children (node x2a) xs = []\<close>;
      cases \<open>b = node (hd (VSIDS.remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (VSIDS.remove_key_children (node x2a) xs) = x2b\<close>;
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>VSIDS.remove_key_children (node x2a) xs = []\<close>;
      cases \<open>b = node (hd (VSIDS.remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (VSIDS.remove_key_children (node x2a) xs) = x2b\<close>;
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>VSIDS.remove_key_children (node x2a) xs = []\<close>;
      cases \<open>b = node (hd (VSIDS.remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (VSIDS.remove_key_children (node x2a) xs) = x2b\<close>;
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.distinct(1) remove_key_children_notin_unchanged)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.distinct(1) remove_key_children_notin_unchanged)
    apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>VSIDS.remove_key_children (node x2a) xs = []\<close>;
      cases \<open>b = node (hd (VSIDS.remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (VSIDS.remove_key_children (node x2a) xs) = x2b\<close>;
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma split: if_splits option.splits )
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_children_hd_None list.sel(1)
      list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (metis disjunct_not_in distinct_mset_add  remove_key_children_notin_unchanged)
    apply (metis disjunct_not_in distinct_mset_add  remove_key_children_notin_unchanged)
    apply (metis disjunct_not_in distinct_mset_add  remove_key_children_notin_unchanged)
    apply (metis add_diff_cancel_right' distinct_mem_diff_mset hp_parent_children_None_notin node_hd_in_sum not_orig_notin_remove_key option_last_Nil
      option_last_Some_iff(2))

    apply (cases \<open>xs = []\<close>; cases \<open>b = node (hd xs)\<close>; cases \<open>VSIDS.remove_key_children (node x2a) xs = []\<close>;
      cases \<open>b = node (hd (VSIDS.remove_key_children (node x2a) xs))\<close>; cases \<open>Hp x n (VSIDS.remove_key_children (node x2a) xs) = x2b\<close>;
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same
      dest: hp_parent_children_not_hd_node split: if_splits option.splits )
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (metis hp_parent_children_not_hd_node sum_image_mset_sum_map)
    apply (smt (z3) hd_remove_key_node_same' hp_parent.simps(2) hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_children_not_hd_node mset_map option_hd_Nil option_hd_Some_iff(1) sum_mset_sum_list)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin option.simps(2) remove_key_children_notin_unchanged)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin not_orig_notin_remove_key option.simps(2))
    apply (metis VSIDS.remove_key_None_iff option.simps(2))

    apply (
      auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same
      dest: hp_parent_children_not_hd_node split: if_splits option.splits )

    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_simps_single_if list.sel(1) list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims disjunct_not_in distinct_mset_add hp.sel(1) hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_simps_single_if list.sel(1) list.simps(9) node_in_mset_nodes option_last_Nil option_last_Some_iff(2) remove_key_children_notin_unchanged sum_image_mset_sum_map sum_list.Cons)
    apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_parent_children_None_notin not_orig_notin_remove_key option_last_Nil option_last_Some_iff(2))
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin node_hd_in_sum not_orig_notin_remove_key option.simps(2) remove_key_children_node_hd)
    apply (cases \<open>xs = []\<close>)
    apply (auto simp: hp_parent_children_cons hp_parent_simps_single_if handy_if_lemma hd_remove_key_node_same remove_key_children_hd_tl
      dest: hp_parent_children_not_hd_node split: if_splits option.splits)[2]
    apply (smt (verit, best) VSIDS.remove_key_children.simps(1) hd_in_set hd_remove_key_node_same' hp_parent_children_None_notin hp_parent_children_hd_None hp_parent_children_hd_tl_None option.simps(2) remove_key_children_hd_tl remove_key_children_node_hd remove_key_remove_all sum_image_mset_sum_map)
    apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_parent_children_None_notin not_orig_notin_remove_key option_hd_Nil option_hd_Some_iff(2))
    by (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin not_orig_notin_remove_key option_hd_Nil option_hd_Some_iff(2))
  done

lemma in_remove_key_children_changed: \<open>k \<in># sum_list (map mset_nodes c) \<Longrightarrow> VSIDS.remove_key_children k c \<noteq> c\<close>
  apply (induction k c rule: VSIDS.remove_key_children.induct)
  apply auto
  apply (metis hp.sel(1) list.sel(1) mset_map neq_Nil_conv node_hd_in_sum remove_key_remove_all sum_mset_sum_list)+
  done

lemma hp_parent_in_nodes2: \<open>hp_parent (z) xs = Some a \<Longrightarrow> node a \<in># mset_nodes xs\<close>
  apply (induction z xs rule: hp_parent.induct)
  apply (auto simp: hp_parent_children_def filter_empty_conv)
  by (metis empty_iff hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_simps(2) hp_parent_in_nodes
    member_add_mset mset_nodes.simps option.discI option.sel set_mset_empty sum_image_mset_sum_map sum_mset_sum_list union_iff)

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

lemma in_remove_key_changed: \<open>VSIDS.remove_key k a \<noteq> None \<Longrightarrow> a = the (VSIDS.remove_key k a) \<longleftrightarrow> k \<notin># mset_nodes a\<close>
  apply (induction k a rule: VSIDS.remove_key.induct)
  apply (auto simp: in_remove_key_children_changed)
  by (metis in_remove_key_children_changed)

lemma node_remove_key_in_mset_nodes: \<open>\<Sum>\<^sub># (mset_nodes `# mset (VSIDS.remove_key_children k c)) \<subseteq># (\<Sum>\<^sub># (mset_nodes `# mset c))\<close>
  apply (induction k c rule: VSIDS.remove_key_children.induct)
  apply auto
  apply (metis mset_le_incr_right(2) union_commute union_mset_add_mset_right)
  using subset_mset.add_mono by blast

lemma remove_key_children_hp_parent_children_hd_None: \<open>VSIDS.remove_key_children k c = a # list \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow>
  hp_parent_children (node a) (a # list) = None\<close>
  using node_remove_key_in_mset_nodes[of k c]
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
    apply (metis (no_types, opaque_lifting) distinct_mset_iff hp.exhaust_sel mset_nodes.simps union_mset_add_mset_left union_mset_add_mset_right)
    apply (metis Duplicate_Free_Multiset.distinct_mset_mono mset_subset_eq_add_left union_commute)
      by (meson distinct_mset_union hp_next_not_same_node)
  subgoal apply auto
    by (meson hp_next_not_same_node)
  subgoal by auto
  done

lemma hp_parent_children_remove_key_children:
  assumes \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset xs))\<close>
  shows \<open>hp_parent_children b (VSIDS.remove_key_children a xs) =
    (if b \<in># (the_default {#} (map_option mset_nodes (VSIDS.find_key_children a xs))) then None
    else if map_option node (hp_next_children a xs) = Some b then hp_parent_children a xs
    else map_option (the o VSIDS.remove_key a) (hp_parent_children b xs))\<close>
  using assms
proof (induction a xs rule: VSIDS.remove_key_children.induct)
  case (1 k)
  then show ?case by auto
next
  case (2 k x n c xs)
  have [intro]: \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close>
    using 2(4) by (auto simp: in_the_default_empty_iff dest!: multi_member_split split: if_splits)
  consider
    (kx) \<open>k=x\<close> |
    (inc) \<open>k \<noteq> x› \<open>VSIDS.find_key_children k c \<noteq> None\<close> |
    (inxs) \<open>k \<noteq> x› \<open>VSIDS.find_key_children k c = None\<close>
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
    moreover have \<open>b \<in># mset_nodes (the (VSIDS.find_key_children k c)) \<Longrightarrow> b \<in># \<Sum>\<^sub># (mset_nodes `# mset c)\<close>
      using inc by (meson mset_nodes_find_key_children_subset mset_subset_eqD)
    moreover have c: \<open>c \<noteq> []\<close>
      using inc by auto
    moreover have [simp]: \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close>
      using c 2(4) by (cases c; cases \<open>hd c\<close>) auto
    moreover have [simp]: \<open>VSIDS.find_key_children (node (hd c)) c = Some (hd c)\<close>
      using c 2(4) by (cases c; cases \<open>hd c\<close>) auto
    moreover have [simp]: \<open>k \<in># sum_list (map mset_nodes c) \<Longrightarrow> k \<notin># sum_list (map mset_nodes xs)\<close> for k
      using 2(4) by (auto dest!: multi_member_split)
    moreover have [iff]: \<open>VSIDS.remove_key_children k c = [] \<longleftrightarrow> c = [] \<or> (c \<noteq> [] \<and>  tl c = [] \<and> node (hd c) = k)\<close>
      using 2(4)
      by (induction k c rule: VSIDS.remove_key_children.induct) (auto simp: dest: multi_member_split)
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
apply (metis \<open>(VSIDS.remove_key_children k c = []) = (c = [] \<or> c \<noteq> [] \<and> tl c = [] \<and> node (hd c) = k)\<close> \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close> hd_remove_key_node_same' hp_next_children_hd_simps list.exhaust_sel option_hd_def remove_key_children_node_hd)
apply (metis \<open>(VSIDS.remove_key_children k c = []) = (c = [] \<or> c \<noteq> [] \<and> tl c = [] \<and> node (hd c) = k)\<close> hd_remove_key_node_same')
apply (metis \<open>(VSIDS.remove_key_children k c = []) = (c = [] \<or> c \<noteq> [] \<and> tl c = [] \<and> node (hd c) = k)\<close> find_key_children_None_or_itself hd_remove_key_node_same inc(2) node_in_mset_nodes option.sel)
apply (smt (verit) VSIDS.remove_key.simps \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close> \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close>
  hd_remove_key_node_same hp_next_children.elims hp_parent_None_iff_children_None hp_parent_children_hd_None hp_parent_none_children
  hp_parent_simps_single_if list.sel(1) list.sel(3) o_apply option.map_sel option.sel remove_key_children_node_hd sum_image_mset_sum_map)


        apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None
          hp_parent_children_None_hp_parent_iff in_remove_key_changed split: option.split
        dest: in_find_key_children_notin_remove_key)[]
apply (metis handy_if_lemma hd_Cons_tl hp_next_children_hd_simps option_hd_def)
prefer 2
apply (metis handy_if_lemma hp_next_children_hd_simps list.collapse option_hd_def)
 apply (case_tac \<open>hp_parent_children (node z) xs\<close>)
   apply simp
   apply simp
   apply (subst (asm) remove_key_notin_unchanged)

   apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None
     hp_parent_children_None_hp_parent_iff in_remove_key_changed split: option.split
     dest: in_find_key_children_notin_remove_key hp_parent_children_in_nodes2)[2]
   apply (metis (no_types, lifting) "2"(3) VSIDS.remove_key_None_iff \<open>\<And>k. k \<in># sum_list (map mset_nodes c) \<Longrightarrow> k \<notin># sum_list (map mset_nodes xs)\<close>
     comp_def hp_next_children_None_notin hp_parent_children_in_nodes2 in_remove_key_changed mset_map option.map_sel
     option.sel option.simps(8) option_last_Nil option_last_Some_iff(1) remove_key_children_notin_unchanged sum_mset_sum_list)
   using hp_next_children_in_nodes2 apply force
   apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims WB_List_More.distinct_mset_mono \<open>VSIDS.find_key_children (node (hd c)) c = Some (hd c)\<close>
     \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close> add_diff_cancel_left' distinct_mset_in_diff hp.exhaust_sel hp.inject hp_next_children_in_nodes2
     hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps in_remove_key_children_changed list.exhaust_sel list.sel(1) mset_nodes.simps
     mset_nodes_find_key_children_subset option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map sum_mset_sum_list union_single_eq_member)
   apply (smt (verit, ccfv_threshold) VSIDS.remove_key_children.elims WB_List_More.distinct_mset_mono \<open>VSIDS.find_key_children (node (hd c)) c = Some (hd c)\<close>
     \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close> add_diff_cancel_left' distinct_mset_in_diff hp.exhaust_sel hp.inject hp_next_children_in_nodes2
     hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps in_remove_key_children_changed list.exhaust_sel list.sel(1) mset_nodes.simps
     mset_nodes_find_key_children_subset option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map sum_mset_sum_list union_single_eq_member)
   apply (cases \<open>VSIDS.remove_key_children k c\<close>)

   apply (auto simp: hp_parent_simps_if remove_key_children_hp_parent_children_hd_None split: if_splits)
     defer
    apply (frule remove_key_children_hp_parent_children_hd_None)
      using find_key_children_None_or_itself[of k c]
   apply (auto simp: hp_parent_simps_if remove_key_children_hp_parent_children_hd_None split: if_splits)
   apply (metis \<open>VSIDS.remove_key_children (node (hd c)) (tl c) = tl c\<close> hp_next_children_hd_simps hp_parent_simps_single_if list.exhaust_sel list.sel(1) option_hd_Some_iff(1) remove_key_children_node_hd)
subgoal for z x2 x2b a list
  using hp_next_children_not_same_node[of c \<open>node x2\<close> z]
    apply auto
      sledgehammer

apply (frule hp_next_children_not_same_node)
  apply simp
  apply simp
find_theorems node VSIDS.find_key_children

oops
lemma hp_next_not_same_node: \<open>distinct_mset (mset_nodes b) \<Longrightarrow> hp_next x b = Some y \<Longrightarrow> x \<noteq> node y\<close>
  apply (induction x b rule: hp_next.induct)
  apply auto
    by (metis disjunct_not_in distinct_mset_add hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) inter_mset_empty_distrib_right node_in_mset_nodes option.sel)

lemma hp_next_children_not_same_node: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow> hp_next_children x c = Some y \<Longrightarrow> x \<noteq> node y\<close>
  apply (induction x c rule: hp_next_children.induct)
  subgoal
    apply (auto simp: hp_next_children.simps(1) split: if_splits option.splits dest: hp_next_not_same_node)
    apply (metis (no_types, opaque_lifting) distinct_mset_iff hp.exhaust_sel mset_nodes.simps union_mset_add_mset_left union_mset_add_mset_right)
    apply (metis Duplicate_Free_Multiset.distinct_mset_mono mset_subset_eq_add_left union_commute)
      by (meson distinct_mset_union hp_next_not_same_node)
  subgoal apply auto
    by (meson hp_next_not_same_node)
  subgoal by auto
  done

  find_theorems hp_next_children hp_next If
lemma node_remove_key_in_mset_nodes: \<open>\<Sum>\<^sub># (mset_nodes `# mset (VSIDS.remove_key_children k c)) \<subseteq># (\<Sum>\<^sub># (mset_nodes `# mset c))\<close>
  apply (induction k c rule: VSIDS.remove_key_children.induct)
  apply auto
  apply (metis mset_le_incr_right(2) union_commute union_mset_add_mset_right)
  using subset_mset.add_mono by blast

  lemma remove_key_children_hp_parent_children_hd_None: \<open>VSIDS.remove_key_children k c = a # list \<Longrightarrow>
    distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow>
    hp_parent_children (node a) (a # list) = None\<close>
    using node_remove_key_in_mset_nodes[of k c]
    apply (auto simp: hp_parent_children_def filter_empty_conv)
    apply (meson WB_List_More.distinct_mset_mono distinct_mset_union hp_parent_itself)
    by (metis WB_List_More.distinct_mset_mono add_diff_cancel_left' distinct_mem_diff_mset hp_parent_None_notin node_in_mset_nodes sum_list_map_remove1 union_iff)


      oops

      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis handy_if_lemma hp_next_children_hd_simps list.exhaust_sel option_hd_def)
        
find_theorems VSIDS.remove_key "_ \<notin># mset_nodes _"
oops
      apply (metis (mono_tags, lifting) add_diff_cancel_left' distinct_mem_diff_mset hp_parent_None_iff_children_None hp_parent_children_None_notin
        mset_nodes_find_key_children_subset mset_subset_eqD node_hd_in_sum option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_None_iff_children_None split: option.split
        dest: in_find_key_children_notin_remove_key)[]
      apply (metis hp_parent_None_iff_children_None in_find_key_children_notin_remove_key node_hd_in_sum sum_image_mset_sum_map)
      apply (metis \<open>b \<in># sum_list (map mset_nodes c) \<Longrightarrow> hp_parent_children b xs = None\<close> hp_parent_None_iff_children_None
        hp_parent_None_notin_same_hd hp_parent_children_cons hp_parent_hd_None in_find_key_children_notin_remove_key sum_image_mset_sum_map)
      apply (metis add_diff_cancel_right' distinct_mset_in_diff)
      apply (auto simp: hp_parent_children_cons in_the_default_empty_iff hp_parent_children_None_hp_parent_iff hp_parent_None_iff_children_None
        hd_remove_key_node_same' hd_remove_key_node_same split: option.split)[]
      apply (smt (verit, best) VSIDS.find_key_children.simps(2) VSIDS.remove_key_children.elims handy_if_lemma list.sel(1) neq_Nil_conv node_in_mset_nodes)
      apply (smt (verit, best) VSIDS.remove_key_children.elims find_key_children_None_or_itself hp.sel(1) inc(2) list.sel(1) node_in_mset_nodes option.sel)
      sledgehammer
      apply (subst (asm) hd_remove_key_node_same)
      apply simp

oops
find_theorems hd VSIDS.remove_key_children
    apply (metis hp_parent_children_cons)
    apply (meson disjunct_not_in distinct_mset_add)
    apply (auto simp: hp_parent_children_cons split: option.split)[]
      defer
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin mset_map mset_nodes_find_key_children_subset
      mset_subset_eqD option.sel option_hd_Nil option_hd_Some_iff(2) sum_mset_sum_list)
    apply (auto simp: hp_parent_children_cons split: option.split)[]
    apply (metis hp_parent_None_iff_children_None in_find_key_children_notin_remove_key node_hd_in_sum sum_image_mset_sum_map)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_hd_Nil option_hd_Some_iff(1) sum_mset_sum_list)
    apply (metis disjunct_not_in distinct_mset_add find_key_children_notin option.distinct(1) sum_image_mset_sum_map)
defer
    apply (auto simp: hp_parent_children_cons hp_parent_None_iff_children_None
      split: option.split)[]

apply (smt (verit, best) VSIDS.remove_key_children.elims find_key_children_None_or_itself hp.sel(1) hp_parent_None_iff_children_None list.distinct(2) list.sel(1) node_in_mset_nodes option.sel option_last_Nil option_last_Some_iff(2))
apply (metis VSIDS.remove_key_children.simps(2) find_key_children_None_or_itself hd_remove_key_node_same hp.exhaust_sel hp_parent_simps_single_if list.distinct(1) list.exhaust_sel node_in_mset_nodes option.distinct(1) option.sel)
apply (cases \<open>c\<close>; cases \<open>hd c\<close>)
    apply (auto simp: hp_parent_children_cons hp_parent_None_iff_children_None hp_parent_children_None_hp_parent_iff
      split: option.splits if_splits)[]
apply (simp split: if_splits)
    apply (simp add: hp_parent_children_cons hp_parent_None_iff_children_None hp_parent_children_None_hp_parent_iff
      split: option.splits if_splits)[]

oops
    apply (auto simp: hp_parent_children_cons)[]
    apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_next_children_None_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (auto simp: hp_parent_children_cons split: option.split)[]
    apply (smt (verit, del_insts) VSIDS.remove_key_children.elims ex_hp_node_children_Some_in_mset_nodes hp_next_children_hd_simps hp_next_children_simps(1)
      hp_node_children_None_notin2 hp_parent_simps_single_if list.map(2) list.sel(1) node_hd_in_sum option.sel option_hd_Nil sum_image_mset_sum_map sum_list.Cons union_iff)
apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin hp_parent_children_None_notin mset_map option_last_Nil option_last_Some_iff(1) sum_mset_sum_list)
    apply (auto simp: hp_parent_children_cons split: option.split)[]
      apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin hp_parent_children_None_notin hp_parent_simps_single_if mset_map node_hd_in_sum option.simps(2) sum_mset_sum_list)

    apply (auto simp: hp_parent_children_cons split: option.split)[]
      apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)
      apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)

    apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_next_children_None_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)

    apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
apply (metis get_min2_alt_def hp_next_children_hd_simps hp_next_children_simps(1) hp_parent_simps_single_if hp_prev_cadr_node
  hp_prev_children_None_notin list.exhaust_sel mset_map option.simps(3) option_hd_Nil sum_mset_sum_list)
  apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin hp_parent_children_None_notin mset_map option_hd_Nil option_hd_Some_iff(1) sum_mset_sum_list)

    apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_next_children_None_notin hp_parent_children_None_notin hp_parent_simps_single_if node_hd_in_sum option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)

 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
  apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)
  apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)


    apply (metis add_diff_cancel_left' distinct_mset_in_diff hp.sel(1) hp_next_None_notin_children hp_next_children_None_notin hp_next_children_simps(3) option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
apply (simp add: hp_parent_children_cons not_orig_notin_remove_key)

apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_next_children_None_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)


 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
apply (smt (verit, del_insts) VSIDS.remove_key_children.elims ex_hp_node_children_Some_in_mset_nodes hp_next_children_hd_simps hp_next_children_simps(1) hp_node_children_None_notin2 hp_parent_simps_single_if list.map(2) list.sel(1) node_hd_in_sum option.sel option_hd_Nil sum_image_mset_sum_map sum_list.Cons union_iff)
apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_next_children_None_notin hp_parent_children_None_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)


 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
apply (metis add_diff_cancel_left' distinct_mset_in_diff hp_next_children_None_notin hp_parent_children_None_notin hp_parent_simps_single_if node_hd_in_sum option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)


 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
  apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)
  apply (metis hp.sel(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps)


 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
  apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin mset_map option.simps(2) sum_mset_sum_list)
  apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin mset_map option.simps(2) sum_mset_sum_list)
  apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin mset_map option.simps(2) sum_mset_sum_list)

  
 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key split: option.split)[]
   apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
   apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
   apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
   apply (metis add_diff_cancel_right' distinct_mset_in_diff find_key_children_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)

 apply (auto simp: hp_parent_children_cons not_orig_notin_remove_key hp_parent_None_iff_children_None hp_parent_none_children
   split: option.split)[]
    apply (metis disjunct_not_in distinct_mset_add hp_next_children_None_notin hp_parent_children_None_notin option.simps(3) sum_image_mset_sum_map)
    apply (metis (mono_tags, lifting) Misc.last_in_set VSIDS_remove_key_children_alt_def append.right_neutral filter_empty_conv
  hp_next_children_last list.map_disc_iff option_hd_Some_iff(2))
    apply (metis add_diff_cancel_right' distinct_mset_in_diff hp_next_children_None_notin hp_parent_children_None_notin option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (metis (no_types, opaque_lifting) add_diff_cancel_right' distinct_mset_in_diff get_min2_alt_def hp_next_children_hd_simps hp_next_children_simps(1) list.exhaust_sel list.simps(9) node_in_mset_nodes option.distinct(1) option_hd_Nil remove_key_children_node_hd remove_key_children_notin_unchanged sum_list.Cons)

sledgehammer

  oops
find_theorems   VSIDS.find_key_children node
lemma \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# mset c)) \<Longrightarrow>
    VSIDS.find_key_children k c = Some y \<Longrightarrow>
    x \<in># sum_list (map mset_nodes c) \<Longrightarrow> k \<noteq> x \<Longrightarrow>
    map_option node (hp_next_children x c) = map_option node (hp_next x y)\<close>
  apply (induction x c arbitrary: y k rule: VSIDS.find_key_children.induct)
  subgoal by auto
  subgoal for ka x n c xsa y
    apply (auto split: if_splits option.splits)
    apply (cases xsa)
    apply (auto split: if_splits option.splits)[2]
    apply (metis disjunct_not_in distinct_mset_add hp_next_children_append2 list.map(2) sum_list_simps(2))


    oops
      find_theorems hp_next_children If

lemma \<open>x \<in># mset_nodes h \<Longrightarrow>
     VSIDS.find_key a h = Some y \<Longrightarrow> map_option node (hp_next x h) = map_option node (hp_next x y)\<close>
  apply (induction a h arbitrary: y rule: VSIDS.find_key.induct)
  apply (auto split: if_splits)
    oops
lemma
  fixes h :: \<open>('a, nat) hp\<close> and a arr and hs :: \<open>('a, nat) hp multiset\<close>
  defines \<open>arr\<^sub>1 \<equiv> (if hp_parent a h = None then arr else hp_update_child (node (the (hp_parent a h))) (map_option node (hp_next a h)) arr)\<close>
  defines \<open>arr\<^sub>2 \<equiv> (if hp_prev a h = None then arr\<^sub>1 else hp_update_nxt (node (the (hp_prev a h))) (map_option node (hp_next a h)) arr\<^sub>1)\<close>
  defines \<open>arr\<^sub>3 \<equiv> (if hp_next a h = None then arr\<^sub>2 else hp_update_prev (node (the (hp_next a h))) (map_option node (hp_prev a h)) arr\<^sub>2)\<close>
  defines \<open>arr' \<equiv> hp_update_child a None arr\<^sub>3\<close>
  assumes enc: \<open>encoded_hp_prop_list (add_mset h {#}) [] arr\<close>
  shows \<open>encoded_hp_prop_list ({#} + (if VSIDS.remove_key a h = None then {#} else {#the (VSIDS.remove_key a h)#}) +
        (if VSIDS.find_key a h = None then {#} else {#the (VSIDS.find_key a h)#})) []
        arr'\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = ((prevs, nxts, childs, scores))\<close> and
    dist: \<open>distinct_mset (mset_nodes h)\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  have find_key_in_nodes: \<open>VSIDS.find_key a h \<noteq> None \<Longrightarrow> node (the (VSIDS.find_key a h)) \<in># mset_nodes h\<close>
    by (cases \<open>a \<in># mset_nodes h\<close>)
   	 (use find_key_None_or_itself[of a h] in \<open>auto simp del: find_key_None_or_itself\<close>)
  have in_find_key_in_nodes: \<open>x \<in># mset_nodes y \<Longrightarrow> VSIDS.find_key a h = Some y \<Longrightarrow> x \<in># mset_nodes h\<close> for x y
    using mset_nodes_find_key_subset[of a h]
    by auto
  show ?thesis
    supply [[goals_limit=1]]
    using enc
    unfolding assms(1-4) arr  hp_update_child_def hp_update_nxt_def hp_update_prev_def
    apply (clarsimp simp add: encoded_hp_prop_list_def)
    apply (intro conjI impI allI ballI)
    subgoal
      using dist by (metis VSIDS.find_key.simps VSIDS.remove_key_None_iff hp.exhaust_sel option.sel)
    subgoal for x
      using find_key_in_nodes in_find_key_in_nodes[of x \<open>the (VSIDS.find_key a h)\<close>]
      apply (auto dest: multi_member_split)



end
