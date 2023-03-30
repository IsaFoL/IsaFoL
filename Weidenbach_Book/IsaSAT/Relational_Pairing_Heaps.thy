theory Relational_Pairing_Heaps
  imports Pairing_Heaps
begin

subsection \<open>Flat Version of Pairing Heaps\<close>

subsubsection \<open>Splitting genealogy to Relations\<close>

text \<open>In this subsection, we replace the tree version by several arrays that represent
  the relations (parent, child, next, previous) of the same trees.\<close>

(*TODO: this is missing the parents*)
type_synonym ('a, 'b) hp_fun = \<open>(('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'a option) \<times> ('a \<Rightarrow> 'b option))\<close>

definition hp_set_all :: \<open>'a \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'b option  \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> ('a, 'b) hp_fun \<close> where
  \<open>hp_set_all i prev nxt child par sc = (\<lambda>(prevs, nxts, childs, parents, scores). (prevs(i:=prev), nxts(i:=nxt), childs(i:=child), parents(i:=par), scores(i:=sc)))\<close>


definition hp_update_prev :: \<open>'a \<Rightarrow> 'a option \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> ('a, 'b) hp_fun\<close> where
  \<open>hp_update_prev i prev = (\<lambda>(prevs, nxts, childs, parents, score). (prevs(i:=prev), nxts, childs, parents, score))\<close>

definition hp_update_nxt :: \<open>'a \<Rightarrow> 'a option \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> ('a, 'b) hp_fun\<close> where
  \<open>hp_update_nxt i nxt = (\<lambda>(prevs, nxts, childs, parents, score). (prevs, nxts(i:=nxt), childs, parents, score))\<close>

definition hp_update_parents :: \<open>'a \<Rightarrow> 'a option \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> ('a, 'b) hp_fun\<close> where
  \<open>hp_update_parents i nxt = (\<lambda>(prevs, nxts, childs, parents, score). (prevs, nxts, childs, parents(i:=nxt), score))\<close>

definition hp_update_score :: \<open>'a \<Rightarrow> 'b option \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> ('a, 'b) hp_fun\<close> where
  \<open>hp_update_score i nxt = (\<lambda>(prevs, nxts, childs, parents, score). (prevs, nxts, childs, parents, score(i:=nxt)))\<close>

fun hp_read_nxt :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> _\<close> where \<open>hp_read_nxt i (prevs, nxts, childs) = nxts i\<close>
fun hp_read_prev :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> _\<close> where \<open>hp_read_prev i (prevs, nxts, childs) = prevs i\<close>
fun hp_read_child :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> _\<close> where \<open>hp_read_child i (prevs, nxts, childs, parents, scores) = childs i\<close>
fun hp_read_parent :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> _\<close> where \<open>hp_read_parent i (prevs, nxts, childs, parents, scores) = parents i\<close>
fun hp_read_score :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun \<Rightarrow> _\<close> where \<open>hp_read_score i (prevs, nxts, childs, parents, scores) = scores i\<close>

text \<open>

It was not entirely clear from the ground up whether we would actually need to have the conditions
of emptyness of the previous or the parent.  However, these are the only conditions to know whether
a node is in the treen or not, so we decided to include them. It is critical to not add that the scores
are empty, because this is the only way to track the scores after removing a node.

We initially inlined the definition of \<^term>\<open>empty_outside\<close>, but the simplifier immediatly hung himself.
\<close>
definition empty_outside :: \<open>_\<close> where
  \<open>empty_outside \<V> prevs = (\<forall>x. x \<notin># \<V> \<longrightarrow> prevs x = None)\<close>

definition encoded_hp_prop :: \<open>'e multiset \<Rightarrow> ('e,'f) hp multiset \<Rightarrow>  ('e, 'f) hp_fun \<Rightarrow> _\<close> where
  \<open>encoded_hp_prop \<V> m = (\<lambda>(prevs,nxts,children, parents, scores). distinct_mset (\<Sum>\<^sub># (mset_nodes `# m)) \<and>
     set_mset (\<Sum>\<^sub># (mset_nodes `# m)) \<subseteq> set_mset \<V> \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. prevs x = map_option node (hp_prev x m)) \<and>
     (\<forall>m'\<in>#m. \<forall>x \<in># mset_nodes m'. nxts x = map_option node (hp_next x m')) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. children x = map_option node (hp_child x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. parents x = map_option node (hp_parent x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. scores x = map_option score (hp_node x m)) \<and>
     empty_outside (\<Sum>\<^sub># (mset_nodes `# m)) prevs \<and>
     empty_outside (\<Sum>\<^sub># (mset_nodes `# m)) parents)\<close>

lemma empty_outside_alt_def: \<open>empty_outside \<V> f = (dom f \<inter> UNIV - set_mset \<V> = {})\<close>
  unfolding empty_outside_def
  by auto

lemma empty_outside_add_mset[simp]:
  \<open>f v = None \<Longrightarrow> empty_outside (add_mset v \<V>) f \<longleftrightarrow> empty_outside \<V> f\<close>
  unfolding empty_outside_alt_def
  by auto

lemma empty_outside_notin_None: \<open>empty_outside \<V> prevs \<Longrightarrow> a \<notin># \<V> \<Longrightarrow> prevs a = None\<close>
  unfolding empty_outside_alt_def
  by auto

lemma empty_outside_update_already_in[simp]: \<open>x \<in># \<V> \<Longrightarrow> empty_outside \<V> (prevs(x := a)) = empty_outside \<V> prevs\<close>
  unfolding empty_outside_alt_def
  by auto

lemma encoded_hp_prop_irrelevant:
  assumes \<open>a \<notin># \<Sum>\<^sub># (mset_nodes `# m)\<close> and \<open>a\<in>#\<V>\<close> and
    \<open>encoded_hp_prop \<V> m (prevs, nxts, children, parents, scores)\<close>
  shows
    \<open>encoded_hp_prop \<V> (add_mset (Hp a sc []) m) (prevs, nxts(a:=None), children(a:=None), parents, scores(a:=Some sc))\<close>
  using assms by (auto simp: encoded_hp_prop_def empty_outside_notin_None)

lemma hp_parent_single_child[simp]: \<open>hp_parent (node a) (Hp m w\<^sub>m [a]) = Some (Hp m w\<^sub>m [a])\<close>
  by (cases a) (auto simp: hp_parent.simps(1))

lemma hp_parent_children_single_hp_parent[simp]: \<open>hp_parent_children b [a] = hp_parent b a\<close>
  by (auto simp: hp_parent_children_def)


lemma hp_parent_single_child_If:
  \<open>b \<noteq> m \<Longrightarrow> hp_parent b (Hp m w\<^sub>m (a # [])) = (if b = node a then Some (Hp m w\<^sub>m [a]) else hp_parent b a)\<close>
  by (auto simp: hp_parent_simps)

lemma hp_parent_single_child_If2:
  \<open>distinct_mset (add_mset m (mset_nodes a)) \<Longrightarrow>
  hp_parent b (Hp m w\<^sub>m (a # [])) = (if b = m then None else if b = node a then Some (Hp m w\<^sub>m [a]) else hp_parent b a)\<close>
  by (auto simp: hp_parent_simps)


lemma hp_parent_single_child_If3:
  \<open>distinct_mset (add_mset m (mset_nodes a + sum_list (map mset_nodes xs))) \<Longrightarrow>
  hp_parent b (Hp m w\<^sub>m (a # xs)) = (if b = m then None else if b = node a then Some (Hp m w\<^sub>m (a # xs)) else hp_parent_children b (a # xs))\<close>
  by (auto simp: hp_parent_simps)

lemma hp_parent_is_first_child[simp]: \<open>hp_parent (node a) (Hp m w\<^sub>m (a # ch\<^sub>m)) = Some (Hp m w\<^sub>m (a # ch\<^sub>m))\<close>
  by (auto simp: hp_parent.simps(1))

lemma hp_parent_children_in_first_child[simp]: \<open>distinct_mset (mset_nodes a + sum_list (map mset_nodes ch\<^sub>m)) \<Longrightarrow>
  xa \<in># mset_nodes a \<Longrightarrow> hp_parent_children xa (a # ch\<^sub>m) = hp_parent xa a\<close>
  by (auto simp: hp_parent_children_cons split: option.splits dest: multi_member_split)

lemma encoded_hp_prop_link:
  fixes ch\<^sub>m a prevs parents m
  defines \<open>prevs' \<equiv> (if ch\<^sub>m = [] then prevs else prevs (node (hd ch\<^sub>m) := Some (node a)))\<close>
  defines \<open>parents' \<equiv> (if ch\<^sub>m = [] then parents else parents (node (hd ch\<^sub>m) := None))\<close>
  assumes \<open>encoded_hp_prop \<V> (add_mset (Hp m w\<^sub>m ch\<^sub>m) (add_mset a x)) (prevs, nxts, children, parents, scores)\<close>
  shows
    \<open>encoded_hp_prop \<V> (add_mset (Hp m w\<^sub>m (a # ch\<^sub>m)) x) (prevs', nxts(node a:= if ch\<^sub>m = [] then None else Some (node (hd ch\<^sub>m))),
      children(m := Some (node a)), parents'(node a:= Some m), scores(m:=Some w\<^sub>m))\<close>
proof -
  have H[simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a))\<close> \<open>distinct_mset (mset_nodes a)\<close>
     \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m))\<close> and
    dist: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a) + \<Sum>\<^sub># (mset_nodes `# x))\<close>
    \<open>m \<notin># sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a) + \<Sum>\<^sub># (mset_nodes `# x)\<close> and
    incl: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# add_mset (Hp m w\<^sub>m ch\<^sub>m) (add_mset a x))) \<subseteq> set_mset \<V>\<close>
    using assms unfolding encoded_hp_prop_def prod.simps apply auto
    by (metis distinct_mset_add mset_nodes_simps sum_mset.insert union_assoc)+
  have [simp]: \<open>distinct_mset (mset_nodes a + sum_list (map mset_nodes ch\<^sub>m))\<close>
    by (metis H(1) union_ac(2))
  have 1: \<open>ch\<^sub>m \<noteq> [] \<Longrightarrow> node a \<noteq> node (hd ch\<^sub>m)\<close>
    if \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (mset_nodes a + \<Sum>\<^sub># (mset_nodes `# x)))\<close>
    using that by (cases ch\<^sub>m; cases a; auto)
  have K: \<open>xa \<in># mset_nodes a \<Longrightarrow> xa \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>
    \<open>xa \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> xa \<notin># mset_nodes a\<close>for xa
    using H by (auto simp del: H dest!: multi_member_split)

  have [simp]: \<open>ch\<^sub>m \<noteq> [] \<Longrightarrow> ma \<in># x \<Longrightarrow> hp_parent (node (hd ch\<^sub>m)) ma = None\<close>
    \<open>ma \<in># x \<Longrightarrow> hp_parent (node a) ma = None\<close>
    \<open>ma \<in># x \<Longrightarrow> node a \<notin># mset_nodes ma\<close> for ma
    by (cases ch\<^sub>m; cases \<open>hd ch\<^sub>m\<close>; cases a; use dist in \<open>auto simp del: H dest!: multi_member_split\<close>; fail)+
  have [simp]: \<open>xa \<in># sum_list (map mset_nodes ch\<^sub>m) \<Longrightarrow> xa \<noteq> node (hd ch\<^sub>m) \<Longrightarrow> 
    (hp_parent xa (Hp m w\<^sub>m ch\<^sub>m)) = (hp_parent_children xa (a # ch\<^sub>m))\<close> for xa
    using dist H
    by (cases ch\<^sub>m; cases x)
     (auto simp: hp_parent_single_child_If3 hp_parent_children_cons
      simp del: H
      dest!: multi_member_split split: option.splits)

  show ?thesis
    using assms 1 unfolding encoded_hp_prop_def prod.simps
    apply (intro conjI impI ballI)
    subgoal by (auto simp: ac_simps)
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
      by (auto simp: hp_parent_single_child_If2 hp_parent_single_child_If3)
    subgoal
      by (auto split: option.splits simp: K(2))
    subgoal
      by (auto simp: ac_simps)
    subgoal
      by (auto simp: ac_simps)
    done
qed


fun find_first_not_none where
  \<open>find_first_not_none (None # xs) = find_first_not_none xs\<close> |
  \<open>find_first_not_none (Some a # _) = Some a\<close>|
  \<open>find_first_not_none [] = None\<close>

lemma find_first_not_none_alt_def:
  \<open>find_first_not_none xs = map_option the (option_hd (filter ((\<noteq>) None) xs))\<close>
  by (induction xs rule: find_first_not_none.induct) auto

text \<open>In the following we distinguish between the tree part and the tree part without parent (aka the list part).
The latter corresponds to a tree where we have removed the source, but the leafs remains in the correct form.
They are different for first level nexts and first level children.\<close>
definition encoded_hp_prop_list :: \<open>'e multiset \<Rightarrow> ('e,'f) hp multiset \<Rightarrow> ('e,'f) hp list \<Rightarrow> _\<close> where
  \<open>encoded_hp_prop_list \<V> m xs  = (\<lambda>(prevs,nxts,children, parents, scores). distinct_mset (\<Sum>\<^sub># (mset_nodes `# m + mset_nodes `# (mset xs))) \<and>
     set_mset (\<Sum>\<^sub># (mset_nodes `# m + mset_nodes `# (mset xs))) \<subseteq> set_mset \<V> \<and>
     (\<forall>m'\<in>#m. \<forall>x \<in># mset_nodes m'. nxts x = map_option node (hp_next x m')) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. prevs x = map_option node (hp_prev x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. children x = map_option node (hp_child x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. parents x = map_option node (hp_parent x m)) \<and>
     (\<forall>m\<in># m. \<forall>x \<in># mset_nodes m. scores x = map_option score (hp_node x m)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). nxts x = map_option node (hp_next_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). prevs x = map_option node (hp_prev_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). children x = map_option node (hp_child_children x xs)) \<and>
     (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). parents x = map_option node (hp_parent_children x xs)) \<and>
    (\<forall>x \<in># \<Sum>\<^sub># (mset_nodes `# mset xs). scores x = map_option score (hp_node_children x xs)) \<and>
    empty_outside (\<Sum>\<^sub># (mset_nodes `# m + mset_nodes `# (mset xs))) prevs \<and>
    empty_outside (\<Sum>\<^sub># (mset_nodes `# m + mset_nodes `# (mset xs))) parents)
  \<close>

lemma encoded_hp_prop_list_encoded_hp_prop[simp]: \<open>encoded_hp_prop_list \<V> arr [] h = encoded_hp_prop \<V> arr h\<close>
  unfolding encoded_hp_prop_list_def encoded_hp_prop_def by auto

lemma encoded_hp_prop_list_encoded_hp_prop_single[simp]: \<open>encoded_hp_prop_list \<V> {#} [arr] h = encoded_hp_prop \<V> {#arr#} h\<close>
  unfolding encoded_hp_prop_list_def encoded_hp_prop_def by auto

lemma empty_outside_set_none_outside[simp]: \<open>empty_outside \<V> prevs \<Longrightarrow> a \<notin># \<V> \<Longrightarrow>  empty_outside \<V> (prevs(a := None))\<close>
  unfolding empty_outside_alt_def by auto

lemma encoded_hp_prop_list_remove_min:
  fixes parents a child children
  defines \<open>parents' \<equiv> (if children a = None then parents else parents(the (children a) := None))\<close>
  assumes \<open>encoded_hp_prop_list \<V> (add_mset (Hp a b child) xs) [] (prevs, nxts, children, parents, scores)\<close>
  shows \<open>encoded_hp_prop_list \<V> xs child (prevs(a:=None), nxts, children(a:=None), parents', scores)\<close>
proof -
  have a: \<open>children a = None \<longleftrightarrow> child = []\<close> and
    b: \<open>children a \<noteq> None \<Longrightarrow> the (children a) = node (hd child)\<close>
    using assms
    unfolding encoded_hp_prop_list_def
    by (cases child; auto simp: ac_simps hp_parent_single_child_If3 dest: multi_member_split; fail)+
  have dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# add_mset (Hp a b child) xs))\<close>
    using assms unfolding encoded_hp_prop_list_def prod.simps
    by (metis empty_neutral(2) image_mset_empty mset_zero_iff)
  then have \<open>child \<noteq> [] \<Longrightarrow> distinct_mset (mset_nodes ((hd child)) + sum_list (map mset_nodes (tl child)))\<close>
     \<open>child \<noteq> [] \<Longrightarrow> distinct_mset (mset_nodes ((hd child)))\<close>
    using distinct_mset_union by (cases child; auto; fail)+
  moreover have \<open>parents a = None\<close>
    using assms
    unfolding encoded_hp_prop_list_def a
    by (cases child)
     (auto simp: ac_simps hp_parent_single_child_If3 hp_parent_simps_if
      dest: multi_member_split)
  ultimately show ?thesis
    using assms b
    unfolding encoded_hp_prop_list_def a
    apply (cases child)
    apply (auto simp: ac_simps hp_parent_single_child_If3 hp_parent_simps_if
      dest: multi_member_split)
    apply (metis (no_types, lifting) disjunct_not_in distinct_mset_add insert_DiffM node_in_mset_nodes sum_mset.insert union_iff)
    apply (metis hp_node_None_notin2 option.case_eq_if option.exhaust_sel)
    apply (metis hp_node.simps(1) hp_node_children_simps2)
    apply (metis hp_child.simps(1) hp_child_hp_children_simps2)
    done
qed

lemma hp_parent_children_skip_first[simp]:
  \<open>x \<in># sum_list (map mset_nodes ch') \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes ch) + sum_list (map mset_nodes ch')) \<Longrightarrow>
  hp_parent_children x (ch @ ch') = hp_parent_children x ch'\<close>
  by (induction ch) (auto simp: hp_parent_children_cons dest!: multi_member_split)

lemma hp_parent_children_skip_last[simp]:
  \<open>x \<in># sum_list (map mset_nodes ch) \<Longrightarrow>
  distinct_mset (sum_list (map mset_nodes ch) + sum_list (map mset_nodes ch')) \<Longrightarrow>
  hp_parent_children x (ch @ ch') = hp_parent_children x ch\<close>
  by (induction ch) (auto simp: hp_parent_children_cons dest!: multi_member_split split: option.splits)

lemma hp_parent_first_child[simp]:
  \<open>n \<noteq> m \<Longrightarrow> hp_parent n (Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m)) = Some (Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m))\<close>
  by (auto simp: hp_parent.simps(1))

lemma encoded_hp_prop_list_link:
  fixes m ch\<^sub>m prevs b hp\<^sub>m n nxts children parents
  defines \<open>prevs\<^sub>0 \<equiv> (if ch\<^sub>m = [] then prevs else prevs (node (hd ch\<^sub>m) := Some n))\<close>
  defines \<open>prevs' \<equiv> (if b = [] then prevs\<^sub>0 else prevs\<^sub>0 (node (hd b) := Some m)) (n:= None)\<close>
  defines \<open>nxts' \<equiv> nxts (m := map_option node (option_hd b), n := map_option node (option_hd ch\<^sub>m))\<close>
  defines \<open>children' \<equiv> children (m := Some n)\<close>
  defines \<open>parents' \<equiv> (if ch\<^sub>m = [] then parents else parents(node (hd ch\<^sub>m) := None))(n := Some m)\<close>
  assumes \<open>encoded_hp_prop_list \<V> (xs) (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b) (prevs, nxts, children, parents, scores)\<close>
  shows \<open>encoded_hp_prop_list \<V> xs (a @ [Hp m w\<^sub>m (Hp n w\<^sub>n ch\<^sub>n # ch\<^sub>m)] @ b)
       (prevs', nxts', children', parents', scores)\<close>
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
    prevs1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. prevs x = map_option node (hp_prev x m))\<close> and
    parents1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. parents x = map_option node (hp_parent x m))\<close> and
    child1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. children x = map_option node (hp_child x m))\<close> and
    scores1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. scores x = map_option score (hp_node x m))\<close> and
    nxts2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     nxts x = map_option node (hp_next_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    prevs2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     prevs x = map_option node (hp_prev_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    parents2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     parents x = map_option node (hp_parent_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    child2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    children x = map_option node (hp_child_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    scores x = map_option score (hp_node_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    dist2: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    others_empty: \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) prevs\<close>
    \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) parents\<close> and
    incl: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) \<subseteq> set_mset \<V>\<close>
    using assms unfolding encoded_hp_prop_list_def by auto
  have [simp]: \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    "distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))"
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes ch\<^sub>m)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>m))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes a)))\<close>
    "distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes b))"
    \<open>distinct_mset (sum_list (map mset_nodes a) + (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n)))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b))\<close>
    \<open>distinct_mset (sum_list (map mset_nodes ch\<^sub>m) + (sum_list (map mset_nodes ch\<^sub>n) + sum_list (map mset_nodes b)))\<close>
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
    done
  have [simp]: \<open>m \<noteq> node (hd ch\<^sub>m)\<close> \<open>n \<noteq> node (hd ch\<^sub>m)\<close> \<open>(node (hd ch\<^sub>m)) \<notin># sum_list (map mset_nodes b)\<close>
    \<open>node (hd ch\<^sub>m) \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>if \<open>ch\<^sub>m \<noteq> []\<close>
    using dist that notin by (cases ch\<^sub>m; auto dest: multi_member_split; fail)+
  have [simp]: \<open>m \<noteq> node (hd b)\<close> \<open>n \<noteq> node (hd b)\<close> if \<open>b \<noteq> []\<close>
    using dist that notin unfolding encoded_hp_prop_list_def by (cases b; auto; fail)+
  have [simp]: \<open>ma \<in># xs \<Longrightarrow> node (hd ch\<^sub>m) \<notin># mset_nodes ma\<close> if \<open>ch\<^sub>m \<noteq> []\<close> for ma
    using dist that notin by (cases ch\<^sub>m; auto dest!: multi_member_split; fail)+
  have [simp]: \<open>hp_parent_children (node (hd ch\<^sub>m)) ch\<^sub>m = None\<close>
    by (metis \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>m))\<close> distinct_mset_add
      hp_parent.simps(2) hp_parent_None_iff_children_None hp_parent_children_hd_None sum_image_mset_sum_map)
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
    using dist2 unfolding encoded_hp_prop_list_def prod.simps assms(1-5)
    apply (intro conjI impI allI)
    subgoal using assms unfolding encoded_hp_prop_list_def
      by (auto simp: ac_simps simp del: NOTIN_def[symmetric])
    subgoal using incl by auto
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
      using parents1
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
      using child2 notin(9)
      by (auto simp add: K K' K'' hp_child_children_skip_first[of _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_first[of _ \<open>_ # _\<close>, simplified]
        hp_child_children_skip_last[of _ _ \<open>[_]\<close>, simplified]
        hp_child_children_skip_last[of _ \<open>[_]\<close>, simplified] notin
        hp_child_children_skip_last[of _ \<open>[_, _]\<close>, simplified]
        hp_child_children_skip_first[of _ _ \<open>[_]\<close>, simplified]
        split: option.splits)
    subgoal
      using parents2 notin(9)
      by (auto simp add: K K' K'' hp_parent_children_skip_first[of _ \<open>[_]\<close>, simplified]
        hp_parent_children_skip_first[of _ \<open>_ # _\<close>, simplified] hp_parent_simps_single_if
        hp_parent_children_skip_last[of _ _ \<open>[_]\<close>, simplified]
        hp_parent_children_skip_last[of _ \<open>[_]\<close>, simplified] notin
        hp_parent_children_skip_last[of _ \<open>[_, _]\<close>, simplified]
        hp_parent_children_skip_first[of _ _ \<open>[_]\<close>, simplified]
        split: option.splits)
    subgoal
      using scores2
      by (auto split: option.splits simp: K K' K'' hp_node_children_Cons_if
        ex_hp_node_children_Some_in_mset_nodes
        dest: multi_member_split)
    subgoal
      using others_empty
      by (auto simp add: K K' K'' ac_simps)
    subgoal
      using others_empty
      by (auto simp add: K K' K'' ac_simps)
    done
qed

lemma encoded_hp_prop_list_link2:
  fixes m ch\<^sub>m prevs b hp\<^sub>m n nxts children ch\<^sub>n a parents
  defines \<open>prevs' \<equiv> (if ch\<^sub>n = [] then prevs else prevs (node (hd ch\<^sub>n) := Some m))(m := None, n := map_option node (option_last a))\<close>
  defines \<open>nxts\<^sub>0 \<equiv> (if a = [] then nxts else nxts(node (last a) := Some n))\<close>
  defines \<open>nxts' \<equiv> nxts\<^sub>0 (n := map_option node (option_hd b), m := map_option node (option_hd ch\<^sub>n))\<close>
  defines \<open>children' \<equiv> children (n := Some m)\<close>
  defines \<open>parents' \<equiv> (if ch\<^sub>n = [] then parents else parents(node (hd ch\<^sub>n) := None))(m := Some n)\<close>
  assumes \<open>encoded_hp_prop_list \<V> (xs) (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b) (prevs, nxts, children, parents, scores)\<close>
  shows \<open>encoded_hp_prop_list \<V> xs (a @ [Hp n w\<^sub>n (Hp m w\<^sub>m ch\<^sub>m # ch\<^sub>n)] @ b)
       (prevs', nxts', children', parents', scores)\<close>
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
    prevs1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. prevs x = map_option node (hp_prev x m))\<close> and
    child1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. children x = map_option node (hp_child x m))\<close> and
    parent1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. parents x = map_option node (hp_parent x m))\<close> and
    nxts2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     nxts x = map_option node (hp_next_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    prevs2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     prevs x = map_option node (hp_prev_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    child2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
    children x = map_option node (hp_child_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    parent2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
     parents x = map_option node (hp_parent_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores2: \<open>(\<forall>x\<in>#\<Sum>\<^sub># (mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)).
      scores x = map_option score (hp_node_children x (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    scores1: \<open>(\<forall>m\<in>#xs. \<forall>x\<in>#mset_nodes m. scores x = map_option score (hp_node x m))\<close> and
    dist2: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b)))\<close> and
    others_empty: \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) prevs\<close>
      \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) parents\<close> and
    incl: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# xs + mset_nodes `# mset (a @ [Hp m w\<^sub>m ch\<^sub>m, Hp n w\<^sub>n ch\<^sub>n] @ b))) \<subseteq> set_mset \<V>\<close>
    using assms unfolding encoded_hp_prop_list_def prod.simps by clarsimp_all
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
    \<open>node (hd ch\<^sub>m) \<notin># sum_list (map mset_nodes ch\<^sub>n)\<close>if \<open>ch\<^sub>m \<noteq> []\<close>
    using dist that notin by (cases ch\<^sub>m; auto dest: multi_member_split; fail)+
  have [simp]: \<open>m \<noteq> node (hd ch\<^sub>n)\<close> \<open>n \<noteq> node (hd ch\<^sub>n)\<close> \<open>(node (hd ch\<^sub>n)) \<notin># sum_list (map mset_nodes b)\<close>
    \<open>node (hd ch\<^sub>n) \<notin># sum_list (map mset_nodes ch\<^sub>m)\<close>if \<open>ch\<^sub>n \<noteq> []\<close>
    using dist that notin by (cases ch\<^sub>n; auto dest: multi_member_split; fail)+
  have [simp]: \<open>m \<noteq> node (hd b)\<close> \<open>n \<noteq> node (hd b)\<close> if \<open>b \<noteq> []\<close>
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

  have [simp]: \<open>hp_parent_children (node (hd ch\<^sub>m)) ch\<^sub>m = None\<close>
    by (metis \<open>distinct_mset (sum_list (map mset_nodes a) + sum_list (map mset_nodes ch\<^sub>m))\<close> distinct_mset_add
      hp_parent.simps(2) hp_parent_None_iff_children_None hp_parent_children_hd_None sum_image_mset_sum_map)
  have [simp]: \<open>ch\<^sub>n \<noteq> [] \<Longrightarrow> hp_parent_children (node (hd ch\<^sub>n)) ch\<^sub>n = None\<close>
    using dist
    by (cases ch\<^sub>n; cases \<open>hd ch\<^sub>n\<close>) (auto simp: hp_parent_children_cons distinct_mset_add split: option.splits)
  have [iff]: \<open>ch\<^sub>n \<noteq> [] \<Longrightarrow> ma \<in># xs \<Longrightarrow> node (hd ch\<^sub>n) \<in># mset_nodes ma \<longleftrightarrow> False\<close> for ma
    using dist2 apply auto
    by (metis (no_types, lifting) add_mset_disjoint(1) distinct_mset_add insert_DiffM inter_mset_empty_distrib_right node_hd_in_sum sum_mset.insert)
  show ?thesis
    using dist2 unfolding encoded_hp_prop_list_def prod.simps assms(1-5)
    apply (intro conjI impI allI)
    subgoal using assms unfolding encoded_hp_prop_list_def
      by (auto simp: ac_simps simp del: NOTIN_def[symmetric])
    subgoal using incl by auto
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
      using parent1
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
      using parent2 notin(9)
      by (auto simp add: K K' K'' hp_parent_children_skip_first[of _ \<open>[_]\<close>, simplified]
        hp_parent_children_skip_first[of _ \<open>_ # _\<close>, simplified] hp_parent_simps_single_if
        hp_parent_children_skip_last[of _ _ \<open>[_]\<close>, simplified]
        hp_parent_children_skip_last[of _ \<open>[_]\<close>, simplified] notin
        hp_parent_children_skip_last[of _ \<open>[_, _]\<close>, simplified]
        hp_parent_children_skip_first[of _ _ \<open>[_]\<close>, simplified]
        hp_parent_children_skip_first[of _ _ \<open>[_,_]\<close>, simplified]
        eq_commute[of n \<open>node (hd [])\<close>]
        split: option.splits)
    subgoal
      using scores2
      by (auto split: option.splits simp: K K' K'' hp_node_children_Cons_if
        ex_hp_node_children_Some_in_mset_nodes
        dest: multi_member_split)
    subgoal
      using others_empty
      by (auto simp add: K K' K'' ac_simps add_mset_commute[of m n])
    subgoal
      using others_empty
      by (auto simp add: K K' K'' ac_simps add_mset_commute[of m n])
    done
qed

definition encoded_hp_prop_list_conc
  :: "'a::linorder multiset \<times> ('a, 'b) hp_fun \<times> 'a option \<Rightarrow>
     'a multiset \<times> ('a, 'b) hp option \<Rightarrow> bool"
  where
  \<open>encoded_hp_prop_list_conc = (\<lambda>(\<V>, arr, h) (\<V>', x). \<V> = \<V>' \<and>
  (case x of None \<Rightarrow> encoded_hp_prop_list \<V>' {#} ([]:: ('a, 'b) hp list) arr \<and> h = None
  | Some x \<Rightarrow> encoded_hp_prop_list \<V>' {#x#} [] arr \<and> set_mset (mset_nodes x) \<subseteq> set_mset \<V> \<and> h = Some (node x)))\<close>

lemma encoded_hp_prop_list_conc_alt_def:
  \<open>encoded_hp_prop_list_conc = (\<lambda>(\<V>, arr, h) (\<V>', x). \<V> = \<V>' \<and>
  (case x of None \<Rightarrow> encoded_hp_prop_list \<V>' {#} ([]:: ('a::linorder, 'b) hp list) arr \<and> h = None
  | Some x \<Rightarrow> encoded_hp_prop_list \<V>' {#x#} [] arr \<and> h = Some (node x)))\<close>
  unfolding encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
  by (auto split: option.splits intro!: ext)

definition encoded_hp_prop_list2_conc
  :: "'a::linorder multiset \<times> ('a, 'b) hp_fun \<times> 'a option \<Rightarrow>
     'a multiset \<times> ('a, 'b) hp list \<Rightarrow> bool"
  where
  \<open>encoded_hp_prop_list2_conc = (\<lambda>(\<V>, arr, h) (\<V>', x). \<V>' = \<V> \<and>
  (encoded_hp_prop_list \<V> {#} x arr \<and> set_mset (sum_list (map mset_nodes x)) \<subseteq> set_mset \<V> \<and> h = None))\<close>

lemma encoded_hp_prop_list2_conc_alt_def:
  \<open>encoded_hp_prop_list2_conc = (\<lambda>(\<V>, arr, h) (\<V>', x). \<V> = \<V>' \<and>
  (encoded_hp_prop_list \<V> {#} x arr \<and>  h = None))\<close>
  unfolding encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
  by (auto split: option.splits intro!: ext)

lemma encoded_hp_prop_list_update_score:
  fixes h :: \<open>('a, nat) hp\<close> and a arr and hs :: \<open>('a, nat) hp multiset\<close> and x
  defines arr': \<open>arr' \<equiv> hp_update_score a (Some x) arr\<close>
  assumes enc: \<open>encoded_hp_prop_list \<V> (add_mset (Hp a b c) hs) [] arr\<close>
  shows \<open>encoded_hp_prop_list \<V> (add_mset (Hp a x c) hs) []
        arr'\<close>
proof -
  obtain prevs nxts childs parents scores \<V> where
    arr: \<open>arr = ((prevs, nxts, childs, parents, scores))\<close> and
    dist: \<open>distinct_mset (sum_list (map mset_nodes c) + \<Sum>\<^sub># (mset_nodes `# hs))\<close>
      \<open>a \<notin># sum_list (map mset_nodes c)\<close>
      \<open>a \<notin># \<Sum>\<^sub># (mset_nodes `# hs)\<close>
    and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  have find_key_in_nodes: \<open>find_key a h \<noteq> None \<Longrightarrow> node (the (find_key a h)) \<in># mset_nodes h\<close>
    by (cases \<open>a \<in># mset_nodes h\<close>)
   	 (use find_key_None_or_itself[of a h] in \<open>auto simp del: find_key_None_or_itself\<close>)
  have in_find_key_in_nodes1: \<open>x \<in># mset_nodes y \<Longrightarrow> find_key a h = Some y \<Longrightarrow> x \<in># mset_nodes h\<close> for x y
    using mset_nodes_find_key_subset[of a h]
    by auto
  have [simp]: \<open>find_key a h = None \<Longrightarrow> remove_key a h = Some h\<close>
    by (metis find_key.simps find_key_none_iff hp.exhaust_sel hp_node_None_notin2
      hp_node_children_None_notin2 hp_node_children_simps2 option_last_Nil option_last_Some_iff(2)
      remove_key_notin_unchanged)
  have [simp]: \<open>map_option node (hp_parent xa (Hp a b c)) = map_option node (hp_parent xa (Hp a x c))\<close> for xa
    by (cases c; auto simp: hp_parent.simps(1))
  have \<open>remove_key a h \<noteq> None \<Longrightarrow> node (the (remove_key a h)) \<in># mset_nodes h\<close>
    by (metis remove_key.simps get_min2.simps hp.exhaust_sel option.collapse option.distinct(2) remove_key_notin_unchanged)
  then show ?thesis
    supply [[goals_limit=1]]
    using enc
    unfolding arr hp_update_nxt_def hp_update_prev_def case_prod_beta
      encoded_hp_prop_list_def prod.simps arr' apply -
    apply (intro conjI impI ballI)
    subgoal
      by (auto simp: find_remove_mset_nodes_full)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      apply (auto simp: find_remove_mset_nodes_full hp_update_score_def)
      by (metis hp_child_hp_children_simps2)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    subgoal
      by (auto simp: find_remove_mset_nodes_full hp_update_score_def)
    done
qed


subsubsection \<open>Refinement to Imperative version\<close>

definition hp_insert :: \<open>'a \<Rightarrow> 'b::linorder \<Rightarrow> 'a multiset \<times> ('a,'b) hp_fun \<times> 'a option \<Rightarrow> ('a multiset \<times> ('a,'b) hp_fun \<times> 'a option) nres\<close> where
  \<open>hp_insert = (\<lambda>(i::'a) (w::'b) (\<V>::'a multiset, arr :: ('a, 'b) hp_fun, h :: 'a option). do {
  if h = None then do {
    ASSERT (i \<in># \<V>);
    RETURN (\<V>, hp_set_all i None None None None (Some w) arr, Some i)
   } else do {
    ASSERT (i \<in># \<V>);
    ASSERT (hp_read_prev i arr = None);
    ASSERT (hp_read_parent i arr = None);
    let (j::'a) = ((the h) :: 'a);
    ASSERT (j \<in># \<V> \<and> j \<noteq> i);
    ASSERT (hp_read_score j (arr :: ('a, 'b) hp_fun) \<noteq> None);
    ASSERT (hp_read_prev j arr = None \<and> hp_read_nxt j arr = None \<and> hp_read_parent j arr = None);
    let y = (the (hp_read_score j arr)::'b);
    if y < w
    then do {
      let arr = hp_set_all i None None (Some j) None (Some (w::'b)) (arr::('a, 'b) hp_fun);
      let arr = hp_update_parents j (Some i) arr;
      let nxt = hp_read_nxt j arr;
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, Some i)
    }
    else do {
      let child = hp_read_child j arr;
      ASSERT (child \<noteq> None \<longrightarrow> the child \<in># \<V>);
      let arr = hp_set_all j None None (Some i) None (Some y) arr;
      let arr = hp_set_all i None child None (Some j) (Some (w::'b)) arr;
      let arr = (if child = None then arr else hp_update_prev (the child) (Some i) arr);
      let arr = (if child = None then arr else hp_update_parents (the child) None arr);
      RETURN (\<V>, arr :: ('a, 'b) hp_fun, h)
    }
   }
  })\<close>


lemma hp_insert_spec:
  assumes \<open>encoded_hp_prop_list_conc arr h\<close> and
    \<open>snd h \<noteq> None \<Longrightarrow> i \<notin># mset_nodes (the (snd h))\<close> and
    \<open>i \<in># fst arr\<close>
  shows \<open>hp_insert i w arr \<le> \<Down> {(arr, h). encoded_hp_prop_list_conc arr h}  (ACIDS.mop_hm_insert i w h)\<close>
proof -
  let ?h = \<open>snd h\<close>
  obtain prevs nxts childs scores parents \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, parents, scores), map_option node ?h)\<close> 
    by (cases arr; cases ?h) (use assms in \<open>auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)

  have enc: \<open>encoded_hp_prop \<V> {#Hp i w [the ?h]#}
    (prevs, nxts(i := None, node (the ?h) := None), childs(i \<mapsto> node (the ?h)), parents(node (the ?h) \<mapsto> i), scores(i \<mapsto> w))\<close> and
    enc2: \<open>encoded_hp_prop \<V> {#Hp (node (the ?h)) (score (the ?h)) (Hp i w [] # hps (the ?h))#}
   (if hps (the ?h) = [] then prevs else prevs(node (hd (hps (the ?h))) \<mapsto> node (Hp i w [])),
    nxts  (i := None,  node (Hp i w []) := if hps (the ?h) = [] then None else Some (node (hd (hps (the ?h))))),
    childs(i := None)(node (the ?h) \<mapsto> node (Hp i w [])),
    (if hps (the ?h) = [] then parents else parents(node (hd (hps (the ?h))) := None))(node (Hp i w []) \<mapsto> node (the ?h)),
    scores(i \<mapsto> w, node (the ?h) \<mapsto> score (the ?h)))\<close> (is ?G)
    if \<open>?h \<noteq> None\<close>
  proof -
    have \<open>encoded_hp_prop \<V> {#the ?h#} (prevs, nxts, childs, parents, scores)\<close>
      using that assms by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def arr)
    then have 0: \<open>encoded_hp_prop \<V> {#Hp i w [], the ?h#}
      (prevs, nxts(i := None), childs(i := None), parents, scores(i \<mapsto> w))\<close>
      using encoded_hp_prop_irrelevant[of i \<open>{#the ?h#}\<close> \<V> prevs nxts childs parents scores w] that assms
      by (auto simp: arr)
    from encoded_hp_prop_link[OF this]
    show \<open>encoded_hp_prop \<V> {#Hp i w [the ?h]#}
      (prevs, nxts(i := None, node (the ?h) := None), childs(i \<mapsto> node (the ?h)), parents(node (the ?h) \<mapsto> i), scores(i \<mapsto> w))\<close>
      by auto
    from 0 have \<open>encoded_hp_prop \<V> {#Hp (node (the ?h)) (score (the ?h)) (hps (the ?h)), Hp i w []#}
      (prevs, nxts(i := None), childs(i := None), parents, scores(i \<mapsto> w))\<close>
      by (cases \<open>the ?h\<close>) (auto simp: add_mset_commute)
    from encoded_hp_prop_link[OF this]
    show ?G .
  qed
  have prev_parent_i:
    \<open>?h \<noteq> None \<Longrightarrow> hp_read_prev i (prevs, nxts, childs, parents, scores) = None\<close>
    \<open>?h \<noteq> None \<Longrightarrow> hp_read_parent i (prevs, nxts, childs, parents, scores) = None\<close>
    using assms unfolding encoded_hp_prop_list_conc_def
    by (force simp: arr encoded_hp_prop_def empty_outside_alt_def dest!: multi_member_split[of i])+
  have 1: \<open>?h \<noteq> None \<Longrightarrow> hps (the ?h) \<noteq> [] \<Longrightarrow> i \<noteq> node (hd (hps (the ?h)))\<close>
    using assms by (cases \<open>the ?h\<close>; cases \<open>hps (the ?h)\<close>; cases h) auto
  have [simp]: \<open>encoded_hp_prop \<V> {#Hp x1a x2 x3#} (prevs, nxts, childs, parents, scores) \<Longrightarrow> scores x1a = Some x2\<close>
    \<open>encoded_hp_prop \<V> {#Hp x1a x2 x3#} (prevs, nxts, childs, parents, scores) \<Longrightarrow> parents x1a = None\<close>
    \<open>encoded_hp_prop \<V> {#Hp x1a x2 x3#} (prevs, nxts, childs, parents, scores) \<Longrightarrow> childs x1a = map_option node (option_hd x3)\<close> for x1a x2 x3
    by (auto simp: encoded_hp_prop_def)
  show ?thesis
    using assms
    unfolding hp_insert_def arr prod.simps ACIDS.mop_hm_insert_def
    apply refine_vcg
    subgoal
      by auto
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
          empty_outside_alt_def
        split: option.splits prod.splits)
    subgoal
      by auto
    subgoal using prev_parent_i by auto
    subgoal using prev_parent_i by auto
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (cases \<open>the ?h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (cases \<open>the ?h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def hp_set_all_def
        split: option.splits prod.splits)
    subgoal
      using enc
      by (cases h, simp; cases \<open>the ?h\<close>)
        (auto simp: hp_set_all_def encoded_hp_prop_list_conc_def fun_upd_idem hp_update_parents_def)
    subgoal
      using enc
      by (cases h, simp; cases \<open>the ?h\<close>; cases \<open>hps (the ?h)\<close>; cases \<open>hd (hps (the ?h))\<close>)
        (auto simp: hp_set_all_def encoded_hp_prop_list_conc_def fun_upd_idem hp_update_parents_def
        arr)
    subgoal
      using enc2 1
      by (cases h, simp; cases \<open>the ?h\<close>)
        (auto simp: hp_set_all_def encoded_hp_prop_list_conc_def fun_upd_idem hp_update_prev_def
          fun_upd_twist hp_update_parents_def)
     done
qed

definition hp_link :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a multiset \<times> ('a,'b::order) hp_fun \<times> 'a option \<Rightarrow> (('a multiset \<times> ('a,'b) hp_fun \<times> 'a option) \<times> 'a) nres\<close> where
  \<open>hp_link = (\<lambda>(i::'a) j (\<V>::'a multiset, arr :: ('a, 'b) hp_fun, h :: 'a option). do {
    ASSERT (i \<noteq> j);
    ASSERT (i \<in># \<V>);
    ASSERT (j \<in># \<V>);
    ASSERT (hp_read_score i arr \<noteq> None);
    ASSERT (hp_read_score j arr \<noteq> None);
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
    ASSERT (ch \<in># \<V>);
    ASSERT (parent \<in># \<V>);
    ASSERT (child \<noteq> None \<longrightarrow> the child \<in># \<V>);
    ASSERT (nxt \<noteq> None \<longrightarrow> the nxt \<in># \<V>);
    ASSERT (prev \<noteq> None \<longrightarrow> the prev \<in># \<V>);
    let arr = hp_set_all parent prev nxt (Some ch) None (Some (w\<^sub>p::'b)) (arr::('a, 'b) hp_fun);
    let arr = hp_set_all ch None child child\<^sub>c\<^sub>h (Some parent) (Some (w\<^sub>c\<^sub>h::'b)) (arr::('a, 'b) hp_fun);
    let arr = (if child = None then arr else hp_update_prev (the child) (Some ch) arr);
    let arr = (if nxt = None then arr else hp_update_prev (the nxt) (Some parent) arr);
    let arr = (if prev = None then arr else hp_update_nxt (the prev) (Some parent) arr);
    let arr = (if child = None then arr else hp_update_parents (the child) None arr);
    RETURN ((\<V>, arr :: ('a, 'b) hp_fun, h), parent)
 })\<close>


lemma fun_upd_twist2: "a \<noteq> c \<Longrightarrow> a \<noteq> e \<Longrightarrow> c \<noteq> e \<Longrightarrow> m(a := b, c := d, e := f) = (m(e := f, c := d))(a := b)"
  by auto

lemma hp_link:
  assumes enc: \<open>encoded_hp_prop_list2_conc arr (\<V>', xs @ x # y # ys)\<close> and
    \<open>i = node x\<close> and
    \<open>j = node y\<close>
  shows \<open>hp_link i j arr \<le> SPEC (\<lambda>(arr, n). encoded_hp_prop_list2_conc arr (\<V>', xs @ ACIDS.link x y # ys) \<and>
    n = node (ACIDS.link x y))\<close>
proof -
  obtain prevs nxts childs parents scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, parents, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs @ x # y # ys))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes (xs @ x # y # ys))) \<subseteq> set_mset \<V>\<close> and
    \<V>'[simp]: \<open>\<V>' = \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)

  have ij: \<open>i \<noteq> j\<close>
    using dist assms(2,3) by (cases x; cases y) auto
  have xy: \<open>Hp (node x) (score x) (hps x) = x\<close>  \<open>Hp (node y) (score y) (hps y) = y\<close> and
    sc: \<open>score x = the (scores i)\<close> \<open>score y = the (scores j)\<close> and
    link_x_y: \<open>ACIDS.link x y = ACIDS.link (Hp i (the (scores i)) (hps x))
     (Hp j (the (scores j)) (hps y))\<close>
    by (cases x; cases y; use assms in \<open>auto simp: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def arr
      simp del: ACIDS.link.simps\<close>; fail)+
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
    \<open>parents i = None\<close>
    \<open>parents j = None\<close>
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
    by (simp add: hp_parent_None_notin_same_hd hp_parent_children_cons)

  have par: \<open>parents j = None\<close> \<open>parents i = None\<close>
    \<open>ch\<^sub>x \<noteq> [] \<Longrightarrow> parents (node (hd ch\<^sub>x)) = Some i\<close>
    \<open>ch\<^sub>y \<noteq> [] \<Longrightarrow> parents (node (hd ch\<^sub>y)) = Some j\<close>
    using assms(1) x y apply (auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
      encoded_hp_prop_def arr hp_child_children_Cons_if)
    apply (metis hp_parent_None_iff_children_None hp_parent_None_notin_same_hd hp_parent_children_cons hp_parent_hd_None sum_image_mset_sum_map)
    apply (metis assms(2) hp_parent_children_cons hp_parent_simps_single_if option.simps(5))
    apply (cases ch\<^sub>y)
    apply (simp_all add: hp_parent_children_skip_first[of _ _ \<open>[_]\<close>, simplified] distinct_mset_add)
    apply (subst hp_parent_children_skip_first[of _ _ \<open>[_]\<close>, simplified])
    apply simp
    apply simp
    apply (metis distinct_mset_add inter_mset_empty_distrib_right)
    apply (subst hp_parent_children_skip_last[of _ \<open>[_]\<close>, simplified])
    apply simp
    apply simp
    apply (metis distinct_mset_add inter_mset_empty_distrib_right)
    apply simp
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
  have enc0: \<open>encoded_hp_prop_list \<V> {#} (xs @ [Hp (node x) (score x) (hps x), Hp (node y) (score y) (hps y)] @ ys) (prevs, nxts, childs, parents, scores)\<close>
    using enc unfolding x y by (auto simp: encoded_hp_prop_list2_conc_def arr)
  then have H: \<open>fst x1= \<V> \<Longrightarrow> snd (snd x1) = None\<Longrightarrow> encoded_hp_prop_list2_conc x1 (\<V>', xs @ ACIDS.link x y # ys) \<longleftrightarrow>
    encoded_hp_prop_list \<V> {#} (xs @ ACIDS.link x y # ys) (fst (snd x1))\<close> for x1
    using dist \<V> unfolding x y
    by (cases x1)
      (simp add: encoded_hp_prop_list2_conc_def)
  have KK [intro!]: \<open>ch\<^sub>x \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> node (hd ch\<^sub>x) \<noteq> node (hd ys)\<close>
    using dist2 sc' by simp

  have subs: \<open>set_mset (sum_list (map mset_nodes (xs @ Hp i w\<^sub>x ch\<^sub>x # Hp j w\<^sub>y ch\<^sub>y # ys))) \<subseteq> set_mset \<V>\<close>
    using assms(1) sc'(7,3) unfolding encoded_hp_prop_list2_conc_def x y arr prod.simps
      encoded_hp_prop_list_def
    by (clarsimp_all simp: encoded_hp_prop_list_def)
  then have childs_i: \<open>childs i \<noteq> None \<Longrightarrow> the (childs i) \<in># \<V>\<close>
    \<open>prevs i \<noteq> None \<Longrightarrow> the (prevs i) \<in># \<V>\<close>
    using sc'(7,3) unfolding encoded_hp_prop_list2_conc_def x y arr prod.simps
      encoded_hp_prop_list_def
    apply (clarsimp_all simp: encoded_hp_prop_list_def)
    apply (metis node_hd_in_sum option.sel subsetD)
    by (metis \<V> dist distinct_mset_add hp_next_children_None_notin hp_next_children_last
      list.discI map_append option_hd_Some_hd option_last_Nil option_last_Some_iff(2)
      subset_eq sum_image_mset_sum_map sum_list_append)
  have childs_j: \<open>childs j \<noteq> None \<Longrightarrow> the (childs j) \<in># \<V>\<close>
    \<open>nxts j \<noteq> None \<Longrightarrow> the (nxts j) \<in># \<V>\<close>
    using subs sc'(6,8) unfolding encoded_hp_prop_list2_conc_def x y arr prod.simps
    apply (clarsimp_all simp: encoded_hp_prop_list_def)
    apply (metis node_hd_in_sum option.sel subsetD)
    by (metis basic_trans_rules(31) node_hd_in_sum option.sel)
  show ?thesis
    unfolding hp_link_def arr prod.simps
    apply refine_vcg
    subgoal using ij by auto
    subgoal using dist \<V> by (auto simp: x)
    subgoal using dist \<V> by (auto simp: y)
    subgoal using sc' by auto
    subgoal using sc' by auto
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
    subgoal by (clarsimp split: if_splits)
    subgoal by (clarsimp split: if_splits)
    subgoal using childs_i childs_j by (clarsimp simp: split: if_splits)
    subgoal using childs_i childs_j by (clarsimp simp: split: if_splits)
    subgoal using childs_i childs_j by (clarsimp simp: split: if_splits)
    subgoal premises p for parent b ch ba w\<^sub>p w\<^sub>c x1 x2
      apply (cases \<open>the (scores j) < the (scores i)\<close>)
      subgoal
        apply (subst H)
        using p(1-12) p(19)[symmetric] dist2 \<V>
        apply (solves simp)
        using p(1-12) p(19)[symmetric] dist2 \<V>
        apply (solves simp)
        apply (subst arg_cong2[THEN iffD1, of _ _ _ _ \<open>encoded_hp_prop_list \<V> {#}\<close>, OF _ _ encoded_hp_prop_list_link[of \<V> \<open>{#}\<close> xs \<open>node x\<close> \<open>score x\<close> \<open>hps x\<close> \<open>node y\<close> \<open>score y\<close> \<open>hps y\<close> ys
          prevs nxts childs parents scores, OF enc0]])
        subgoal
          using sc' p(1-12) p(19)[symmetric] dist2 \<V>
          by (simp add: x y)
        subgoal
          using sc' p(1-12) p(19)[symmetric] dist2 \<V> par
          apply (simp add: x y)
          apply (intro conjI impI)
          subgoal apply (simp add: fun_upd_idem fun_upd_twist  fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>] hp_set_all_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply auto[2]
            done
          subgoal
            supply [[goals_limit=1]]
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def
              hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ parents])
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
            apply (subst fun_upd_idem[of \<open>nxts(parent := None)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist[of _ _ parents])
            apply force
            apply (simp (no_asm_simp))
            apply (subst fun_upd_idem[of \<open>nxts(parent := None)(ch \<mapsto> node (hd ch\<^sub>x))\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply force
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist2[of _ _ _ prevs])
            apply (rule KK)
            apply assumption
            apply assumption
            apply force
            apply force
            apply (subst fun_upd_twist[of _ _ \<open>prevs(ch := None)\<close>])
            apply (rule KK[symmetric])
            apply assumption
            apply assumption
            apply (subst fun_upd_twist[of _ _ \<open>parents\<close>])
            apply argo
            apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_idem[of \<open>nxts\<close> \<open>node (last xs)\<close>])
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (simp (no_asm))
            apply (subst fun_upd_twist[of _ _ \<open>nxts\<close>])
            apply argo
            apply blast
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
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
            apply (subst fun_upd_twist[of _ _ \<open>parents\<close>])
            apply argo
            apply blast
            done
          done
          apply (rule TrueI)
          done
        subgoal
          supply [[goals_limit=1]]
        apply (subst H)
        using p(1-12) p(19)[symmetric] dist2 \<V>
        apply simp
        using p(1-12) p(19)[symmetric] dist2 \<V>
        apply simp
        apply (subst arg_cong2[THEN iffD1, of _ _ _ _ \<open>encoded_hp_prop_list \<V> {#}\<close>, OF _ _ encoded_hp_prop_list_link2[of \<V> \<open>{#}\<close> xs \<open>node x\<close> \<open>score x\<close> \<open>hps x\<close> \<open>node y\<close> \<open>score y\<close> \<open>hps y\<close> ys
          prevs nxts childs parents scores, OF enc0]])
        subgoal
          using sc' p(1-12) p(19)[symmetric] dist2 \<V>
          by (simp add: x y)
        subgoal
          using sc' p(1-12) p(19)[symmetric] dist2 \<V>
          apply (simp add: x y)
          apply (intro conjI impI)
          subgoal
            by (simp add: fun_upd_idem fun_upd_twist  fun_upd_idem[of \<open>childs(parent \<mapsto> ch)\<close>] hp_set_all_def)
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_idem[of prevs _ ])
            apply (simp (no_asm_simp))
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist[of _ _ parents])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist2[of _ _ _ nxts])
            apply force
            apply force
            apply force
            apply (subst fun_upd_idem[of \<open>nxts(ch := None)\<close>])
            apply (simp (no_asm_simp))
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>(nxts(node (last xs) \<mapsto> parent))\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ parents])
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ nxts])
            apply force
            apply (subst fun_upd_twist[of _ _ \<open>(prevs(parent \<mapsto> node (last xs)))\<close>])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_idem[of \<open>prevs(parent := None)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_twist2)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_twist[of _ _ parents])
            apply force
            apply (simp (no_asm_simp))
            apply (subst fun_upd_idem[of \<open>prevs(parent := None)\<close>])
            apply (simp (no_asm_simp))
            apply (subst fun_upd_idem[of \<open>(prevs(parent := None))(_ \<mapsto> _)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply force
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
            apply (subst fun_upd_twist[of _ _ prevs])
            apply force
            apply (subst fun_upd_idem[of \<open>(prevs(parent \<mapsto> node (last xs)))(ch := None)\<close>])
            apply (simp (no_asm_simp))
            apply (smt (z3) IntI Un_iff empty_iff mem_Collect_eq option.simps(9) option_hd_Some_hd)
            apply (subst fun_upd_idem[of \<open>nxts(node (last xs) \<mapsto> parent)\<close>])
            apply (simp (no_asm_simp))
            apply force
            apply (subst fun_upd_twist[of _ _ nxts])
            apply force
            apply (simp (no_asm_simp))
            done
          subgoal
            apply (simp (no_asm_simp) add: hp_set_all_def hp_update_nxt_def fun_upd_idem fun_upd_twist
              hp_update_prev_def hp_update_parents_def)
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
            apply (subst fun_upd_twist[of _ _ parents])
            apply force
            apply (simp (no_asm))
            done
          done
          apply (rule TrueI)
          done
        done
      subgoal premises p
        using p(1-12) p(19)[symmetric] dist2 \<V>
        using sc'
        by (cases \<open>the (scores j) < the (scores i)\<close>)
         (simp_all add: x y split: if_split)
      done
qed


text \<open>In an imperative setting use the two pass approaches is better than the alternative.

The \<^term>\<open>e::nat\<close> of the loop is a dummy counter.\<close>
definition vsids_pass\<^sub>1 where
  \<open>vsids_pass\<^sub>1 = (\<lambda>(\<V>::'a multiset, arr :: ('a, 'b::order) hp_fun, h :: 'a option) (j::'a). do {
  ((\<V>, arr, h), j, _, n) \<leftarrow> WHILE\<^sub>T(\<lambda>((\<V>, arr, h), j, e, n). j \<noteq> None)
  (\<lambda>((\<V>, arr, h), j, e::nat, n). do {
    if j = None then RETURN ((\<V>, arr, h), None, e, n)
    else do {
    let j = the j;
    ASSERT (j \<in># \<V>);
    let nxt = hp_read_nxt j arr;
    if nxt = None then RETURN ((\<V>, arr, h), nxt, e+1, j)
    else do {
      ASSERT (nxt \<noteq> None);
      ASSERT (the nxt \<in># \<V>);
      let nnxt = hp_read_nxt (the nxt) arr;
      ((\<V>, arr, h), n) \<leftarrow> hp_link j (the nxt) (\<V>, arr, h);
      RETURN ((\<V>, arr, h), nnxt, e+2, n)
   }}
  })
  ((\<V>, arr, h), Some j, 0::nat, j);
  RETURN ((\<V>, arr, h), n)
  })\<close>


lemma vsids_pass\<^sub>1:
  fixes arr :: \<open>'a::linorder multiset \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr (\<V>', xs)\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (hd xs)\<close>
  shows \<open>vsids_pass\<^sub>1 arr j \<le> SPEC(\<lambda>(arr, j). encoded_hp_prop_list2_conc arr (\<V>', ACIDS.pass\<^sub>1 xs) \<and> j = node (last (ACIDS.pass\<^sub>1 xs)))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> set_mset \<V>\<close> and
    [simp]: \<open>\<V>' = \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  define I where \<open>I \<equiv> (\<lambda>(arr, nnxt::'a option, e, k).
    encoded_hp_prop_list2_conc arr (\<V>, ACIDS.pass\<^sub>1(take e xs) @ drop e xs) \<and> nnxt = map_option node (option_hd (drop (e) xs)) \<and>
    e \<le> (length xs) \<and> (nnxt = None \<longleftrightarrow> e = length xs) \<and> (nnxt \<noteq> None \<longrightarrow> even e) \<and>
    k = (if e=0 then j else node (last (ACIDS.pass\<^sub>1(take e xs)))))\<close>
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
      using that ACIDS.pass\<^sub>1_append_even[of \<open>butlast xs\<close> \<open>[last xs]\<close>]
      by (auto simp: I_def)
  qed

  have link_pre1: \<open>encoded_hp_prop_list2_conc (x1, x1a, x2a)
    (\<V>', ACIDS.pass\<^sub>1 (take x2b xs) @
    xs!x2b # xs!(Suc x2b) # drop (x2b+2) xs)\<close> (is ?H1) and
    link_pre2: \<open>the x1b = node (xs ! x2b)\<close>  (is ?H2) and
    link_pre3: \<open>the (hp_read_nxt (the x1b) x1a) = node (xs ! Suc x2b)\<close> (is ?H3)
    if \<open>I s\<close> and
      s: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, e, n). j \<noteq> None) xa\<close>
      \<open>s = (a, b)\<close>
      "x2b' = (x2b, j)"
      \<open>b = (x1b, x2b')\<close>
      \<open>x2 = (x1a, x2a)\<close>
      \<open>a = (x1, x2)\<close>
      \<open>x1b \<noteq> None\<close> and
      nxt: \<open>hp_read_nxt (the x1b) x1a \<noteq> None\<close>
    for s a b x1 x2 x1a x2a x1b x2b j x2b'
  proof -
    have \<open>encoded_hp_prop_list x1 {#} (ACIDS.pass\<^sub>1 (take x2b xs) @ drop x2b xs) x1a\<close>
      \<open>x2b < length xs\<close>
      \<open>x1b = Some (node (hd (drop x2b xs)))\<close>
      using that
      by (auto simp: I_def encoded_hp_prop_list2_conc_def arr)
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
        \<open>arr2 = (\<V>'', x1a)\<close>
        \<open>linkedn = (linked, n)\<close>
        \<open>x1d = (x2d, xe)\<close>
        \<open>linked = (x2c, x1d)\<close> and
      nxt: \<open>nxt \<noteq> None\<close> and
      nxts: \<open>hp_read_nxt (the nxt) x2a \<noteq> None\<close>
        \<open>hp_read_nxt (the nxt) x2a \<noteq> None\<close> and
      linkedn: \<open>case linkedn of
      (arr, n) \<Rightarrow>
      encoded_hp_prop_list2_conc arr
      (\<V>', ACIDS.pass\<^sub>1 (take k xs) @ ACIDS.link (xs ! k) (xs ! Suc k) # drop (k + 2) xs) \<and>
      n = node (ACIDS.link (xs ! k) (xs ! Suc k))\<close>
    for s arr2 b x1a x2a x1b nxt k linkedn linked n x2c x1d x2d xe j k' \<V>''
  proof -
    have enc: \<open>encoded_hp_prop_list \<V>' {#} (ACIDS.pass\<^sub>1 (take k xs) @ drop k xs) x2a\<close>
      \<open>k < length xs\<close>
      \<open>nxt = Some (node (hd (drop k xs)))\<close> and
      dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (ACIDS.pass\<^sub>1 (take k xs) @ drop k xs))))\<close>
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
      by (auto simp: I_def take_Suc take_nth ACIDS.pass\<^sub>1_append_even)
  qed

  show ?thesis
    unfolding vsids_pass\<^sub>1_def arr prod.simps
    apply (refine_vcg WHILET_rule[where I=I and R = \<open>measure (\<lambda>(arr, nnxt::'a option, e, _). length xs -e)\<close>]
      hp_link)
    subgoal by auto
    subgoal by (rule I0)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def encoded_hp_prop_list2_conc_def)
    subgoal for s a b x1 x2 x1a x2a x1b x2b
      by (auto simp: I_no_next)
    subgoal by (auto simp: I_def)
    subgoal for s a b x1 x2 x1a x2a x1b x2b x1c x2c
      using hp_next_children_in_nodes2[of \<open>(node (hd (drop x1c xs)))\<close> \<open>(ACIDS.pass\<^sub>1 (take x1c xs) @ drop x1c xs)\<close>]
      by (auto 5 3 simp: I_def encoded_hp_prop_list_def encoded_hp_prop_list2_conc_def)
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
  \<open>vsids_pass\<^sub>2 = (\<lambda>(\<V>::'a multiset, arr :: ('a, 'b::order) hp_fun, h :: 'a option) (j::'a). do {
  ASSERT (j \<in># \<V>);
  let nxt = hp_read_prev j arr;
  ((\<V>, arr, h), j, leader, _) \<leftarrow> WHILE\<^sub>T(\<lambda>((\<V>, arr, h), j, leader, e). j \<noteq> None)
  (\<lambda>((\<V>, arr, h), j, leader, e::nat). do {
    if j = None then RETURN ((\<V>, arr, h), None, leader, e)
    else do {
      let j = the j;
      ASSERT (j \<in># \<V>);
      let nnxt = hp_read_prev j arr;
      ((\<V>, arr, h), n) \<leftarrow> hp_link j leader (\<V>, arr, h);
      RETURN ((\<V>, arr, h), nnxt, n, e+1)
   }
  })
  ((\<V>, arr, h), nxt, j, 1::nat);
  RETURN (\<V>, arr, Some leader)
  })\<close>


lemma vsids_pass\<^sub>2:
  fixes arr :: \<open>'a::linorder multiset \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr (\<V>', xs)\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (last xs)\<close>
  shows \<open>vsids_pass\<^sub>2 arr j \<le> SPEC(\<lambda>(arr). encoded_hp_prop_list_conc arr (\<V>', ACIDS.pass\<^sub>2 xs))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> set_mset \<V>\<close> and
    [simp]: \<open>\<V>' = \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  have prevs_lastxs: \<open>prevs (node (last xs)) = map_option node (option_last (butlast xs))\<close>
    using assms
    by (cases xs rule: rev_cases; cases \<open>last xs\<close>)
     (auto simp: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def arr)

  define I where \<open>I \<equiv> (\<lambda>(arr, nnxt::'a option, leader, e'). let e = length xs - e' in
    encoded_hp_prop_list2_conc arr (\<V>, take e xs @ [the (ACIDS.pass\<^sub>2 (drop e xs))]) \<and> nnxt = map_option node (option_last (take e xs)) \<and>
    leader = node (the (ACIDS.pass\<^sub>2 (drop e xs))) \<and>
    e \<le> (length xs) \<and> (nnxt = None \<longleftrightarrow> e = 0) \<and> e' > 0)\<close>
  have I0: \<open>I ((\<V>, (prevs, nxts, childs, scores), None), hp_read_prev j (prevs, nxts, childs, scores), j, 1)\<close>
    using assms prevs_lastxs unfolding I_def prod.simps Let_def
    by (auto simp: arr butlast_Nil_iff)
  have j\<V>: \<open>j \<in># \<V>\<close>
    using assms by (cases xs rule: rev_cases) (auto simp: encoded_hp_prop_list2_conc_def arr)
  have links_pre1: \<open>encoded_hp_prop_list2_conc (\<V>', arr', h')
    (\<V>, take (length xs - Suc e) xs @
    xs ! (length xs - Suc e) #
    the (ACIDS.pass\<^sub>2 (drop (length xs - e) xs)) # [])\<close> (is ?H1) and
    links_pre2: \<open>the x1b = node (xs ! (length xs - Suc e))\<close> (is ?H2) and
    links_pre3: \<open>leader = node (the (ACIDS.pass\<^sub>2 (drop (length xs - e) xs)))\<close> (is ?H3)
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
      (\<V>, take (length xs - Suc e) xs @
      [ACIDS.link (xs ! (length xs - Suc e)) (the (ACIDS.pass\<^sub>2 (drop (length xs - e) xs)))]) \<and>
      n =
      node
      (ACIDS.link (xs ! (length xs - Suc e)) (the (ACIDS.pass\<^sub>2 (drop (length xs - e) xs))))\<close>
    for s a b \<V>' x2 x1a x2a x1b x2b x1c e linkedn linked new_leader x1d x2d x1e x2e
  proof -
    have e: \<open>e < length xs\<close> \<open>length xs - e < length xs\<close>
      using I brk no_None
      unfolding st I_def
      by (auto simp: I_def Let_def)
    then have [simp]: \<open>ACIDS.link (xs ! (length xs - Suc e)) (the (ACIDS.pass\<^sub>2 (drop (length xs - e) xs)))  =
      the (ACIDS.pass\<^sub>2 (drop (length xs - Suc e) xs))\<close>
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
    subgoal using j\<V> by auto
    subgoal by auto
    subgoal by (rule I0)
    subgoal by auto
    subgoal by auto
    subgoal for s a b x1 x2 x1a x2a x1b x2b x1c x2c
      by (cases \<open>take (length xs - x2c) xs\<close> rule: rev_cases)
       (auto simp: I_def Let_def encoded_hp_prop_list2_conc_def)
    apply (rule links_pre1; assumption)
    subgoal
      by (rule links_pre2)
    subgoal
      by (rule links_pre3)
    subgoal
      by (rule I_Suc)
    subgoal for s a b \<V>' x2 x1a x2a x1b x2b x1c e linkedn linked new_leader x1d x2d x1e x2e
      by (auto simp: I_def Let_def)
    subgoal using assms ACIDS.mset_nodes_pass\<^sub>2[of xs] by (auto simp: I_def Let_def
      encoded_hp_prop_list_conc_def encoded_hp_prop_list2_conc_def
      split: option.split simp del: ACIDS.mset_nodes_pass\<^sub>2)
    done
qed

definition merge_pairs where
  \<open>merge_pairs arr j = do {
    (arr, j) \<leftarrow> vsids_pass\<^sub>1 arr j;
    vsids_pass\<^sub>2 arr j
  }\<close>


lemma vsids_merge_pairs:
  fixes arr :: \<open>'a::linorder multiset \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr (\<V>', xs)\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (hd xs)\<close>
  shows \<open>merge_pairs arr j \<le> SPEC(\<lambda>(arr). encoded_hp_prop_list_conc arr (\<V>', ACIDS.merge_pairs xs))\<close>
proof -
  show ?thesis
    unfolding merge_pairs_def
    apply (refine_vcg vsids_pass\<^sub>1 vsids_pass\<^sub>2[of _ \<V>' "ACIDS.pass\<^sub>1 xs"])
    apply (rule assms)+
    subgoal by auto
    subgoal using assms by (cases xs rule: ACIDS.pass\<^sub>1.cases) auto
    subgoal using assms by auto
    subgoal by (auto simp: ACIDS.pass12_merge_pairs)
    done
qed


definition hp_update_child where
  \<open>hp_update_child i nxt = (\<lambda>(prevs, nxts, childs, scores). (prevs, nxts, childs(i:=nxt), scores))\<close>

definition vsids_pop_min :: \<open>_\<close> where
  \<open>vsids_pop_min = (\<lambda>(\<V>::'a multiset, arr :: ('a, 'b::order) hp_fun, h :: 'a option). do {
  if h = None then RETURN (None, (\<V>, arr, h))
  else do {
      ASSERT (the h \<in># \<V>);
      let j = hp_read_child (the h) arr;
      if j = None then RETURN (h, (\<V>, arr, None))
      else do {
        ASSERT (the j \<in># \<V>);
        let arr = hp_update_prev (the h) None arr;
        let arr = hp_update_child (the h) None arr;
        let arr = hp_update_parents (the j) None arr;
        arr \<leftarrow> merge_pairs (\<V>, arr, None) (the j);
        RETURN (h, arr)
      }
    }
  })\<close>

lemma node_remove_key_itself_iff[simp]: \<open>remove_key (y) z \<noteq> None \<Longrightarrow> node z = node (the (remove_key (y) z)) \<longleftrightarrow> y \<noteq> node z\<close>
  by (cases z) auto

lemma vsids_pop_min:
  fixes arr :: \<open>'a::linorder multiset \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list_conc arr (\<V>, h)\<close>
  shows \<open>vsids_pop_min arr \<le> SPEC(\<lambda>(j, arr). j = (if h = None then None else Some (get_min2 h)) \<and> encoded_hp_prop_list_conc arr (\<V>, ACIDS.del_min h))\<close>
proof -
  show ?thesis
    unfolding vsids_pop_min_def
    apply (refine_vcg vsids_merge_pairs[of _ \<V> \<open>case the h of Hp _ _ child \<Rightarrow> child\<close>])
    subgoal using assms by (cases h) (auto simp: encoded_hp_prop_list_conc_def)
    subgoal using assms by (auto simp: encoded_hp_prop_list_conc_def split: option.splits)
    subgoal using assms by (auto simp: encoded_hp_prop_list_conc_def split: option.splits)
    subgoal using assms by (auto simp: encoded_hp_prop_list_conc_def get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms encoded_hp_prop_list_remove_min[of \<V> \<open>node (the h)\<close> \<open>score (the h)\<close> \<open>hps (the h)\<close> \<open>{#}\<close>
      \<open>fst (fst (snd arr))\<close> \<open>(fst o snd) (fst (snd arr))\<close> \<open>(fst o snd o snd) (fst (snd arr))\<close>
      \<open>(fst o snd o snd o snd) (fst (snd arr))\<close>
      \<open>(snd o snd o snd o snd) (fst (snd arr))\<close>]
      by (cases \<open>the h\<close>; cases \<open>fst (snd arr)\<close>)
       (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list2_conc_def hp_update_parents_def
        hp_update_nxt_def hp_update_score_def hp_update_child_def hp_update_prev_def
        get_min2_alt_def split: option.splits if_splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>the h\<close>) (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def
      get_min2_alt_def split: option.splits)
    subgoal using assms by (cases \<open>h\<close>; cases \<open>the h\<close>)
      (auto simp: get_min2_alt_def ACIDS.pass12_merge_pairs encoded_hp_prop_list_conc_def split: option.splits)
    done
qed

lemma in_remove_key_in_find_keyD:
  \<open>m' \<in># (if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
    (if find_key a h = None then {#} else {#the (find_key a h)#}) \<Longrightarrow>
  distinct_mset (mset_nodes h) \<Longrightarrow>
    x' \<in># mset_nodes m' \<Longrightarrow> x' \<in># mset_nodes h\<close>
  using find_remove_mset_nodes_full[of h a \<open>the (remove_key a h)\<close> \<open>the (find_key a h)\<close>]
    in_remove_key_in_nodes[of a h x']
  apply (auto split: if_splits simp: find_key_None_remove_key_ident)
  apply (metis hp_node_None_notin2 hp_node_in_find_key0)
  by (metis union_iff)

lemma map_option_node_map_option_node_iff:
  \<open>(x \<noteq> None \<Longrightarrow> distinct_mset (mset_nodes (the x))) \<Longrightarrow> (x \<noteq> None \<Longrightarrow>  y \<noteq> node (the x)) \<Longrightarrow>
  map_option node x = map_option node (map_option (\<lambda>x. the (remove_key y x)) x)\<close>
  by (cases x; cases \<open>the x\<close>) auto

lemma distinct_mset_hp_parent: \<open>distinct_mset (mset_nodes h) \<Longrightarrow>  hp_parent a h = Some ya \<Longrightarrow> distinct_mset (mset_nodes ya)\<close>
  apply (induction a h arbitrary: ya rule: hp_parent.induct)
  apply (auto simp: hp_parent_simps_if hp_parent_children_cons split: if_splits option.splits)
  apply (metis (no_types, lifting) WB_List_More.distinct_mset_union2 distinct_mset_union hp_parent_children_Some_iff in_list_in_setD list.map(2) map_append sum_list.Cons sum_list_append)
  by (metis distinct_mset_union)

lemma in_find_key_children_same_hp_parent:
  \<open>hp_parent k (Hp x n c) = None \<Longrightarrow>
    x' \<in># mset_nodes m' \<Longrightarrow>
    x \<notin># sum_list (map mset_nodes c) \<Longrightarrow>
    distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow>
    find_key_children k c = Some m' \<Longrightarrow> hp_parent x' (Hp x n c) = hp_parent x' m'\<close>
  apply (induction k c rule: find_key_children.induct)
  subgoal
    by (auto split: if_splits option.splits simp: hp_parent_simps_single_if hp_parent_children_cons)
  subgoal for k xa na c xs
    apply (auto split: if_splits option.splits simp: hp_parent_simps_single_if hp_parent_children_cons)
    apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(3) sum_image_mset_sum_map)
    apply (metis (no_types, lifting) ACIDS.hp_node_find_key_children find_key_children.simps(1) find_key_children_None_or_itself
      hp.sel(1) hp_node_None_notin2 hp_node_children_simps(3) hp_node_node_itself hp_parent_children_in_first_child hp_parent_in_nodes list.exhaust_sel
      list.simps(9) mset_nodes_find_key_children_subset mset_subset_eqD node_in_mset_nodes option.sel sum_image_mset_sum_map sum_list_simps(2))
    apply (metis hp_node_None_notin2 hp_node_children_None_notin2 hp_node_in_find_key_children sum_image_mset_sum_map)
    apply (smt (verit, ccfv_threshold) basic_trans_rules(31) find_key_children.elims find_key_children.simps(2) hp.exhaust_sel hp.sel(1)
      hp_parent_children_in_first_child hp_parent_in_nodes list.distinct(1) list.exhaust_sel list.simps(9) mset_nodes_find_key_children_subset
      option.sel option.simps(2) set_mset_mono sum_image_mset_sum_map sum_list_simps(2))
    apply (metis disjunct_not_in distinct_mset_add find_key_noneD find_key_none_iff mset_map mset_nodes_find_key_children_subset
      mset_subset_eqD node_hd_in_sum option.sel sum_mset_sum_list)
    apply (smt (verit, ccfv_threshold) basic_trans_rules(31) find_key_children.elims find_key_children.simps(2) hp.exhaust_sel hp.sel(1)
      hp_parent_children_in_first_child hp_parent_in_nodes list.distinct(1) list.exhaust_sel list.simps(9) mset_nodes_find_key_children_subset
      option.sel option.simps(2) set_mset_mono sum_image_mset_sum_map sum_list_simps(2))
    apply (smt (verit) ACIDS.hp_node_find_key_children distinct_mset_add ex_hp_node_children_Some_in_mset_nodes find_key_children.simps(1) find_key_children_None_or_itself
      find_key_none_iff hp.sel(1) hp_node_None_notin2 hp_node_children_None_notin2 hp_node_children_simps(3) hp_node_in_find_key_children hp_node_node_itself
      hp_parent_children_in_first_child hp_parent_in_nodes list.exhaust_sel list.simps(9) option.sel option_last_Nil option_last_Some_iff(2) sum_list_simps(2))
    apply (metis Duplicate_Free_Multiset.distinct_mset_union2 hp_parent_children_hd_None option.simps(2) sum_image_mset_sum_map union_commute)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin if_Some_None_eq_None mset_map mset_nodes_find_key_children_subset mset_subset_eqD
      option.sel sum_mset_sum_list)
    apply (metis Duplicate_Free_Multiset.distinct_mset_union2 hp.sel(1) hp_parent_in_nodes mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(2) sum_image_mset_sum_map union_commute)
    apply (metis basic_trans_rules(31) mset_nodes_find_key_children_subset option.distinct(1) option.sel set_mset_mono sum_image_mset_sum_map)
    apply (metis distinct_mset_add find_key_noneD find_key_none_iff hp_parent_children_None_notin hp_parent_children_skip_first hp_parent_children_skip_last
      mset_map mset_nodes_find_key_children_subset mset_subset_eqD option.sel sum_mset_sum_list)
    apply (simp add: distinct_mset_add)
    using distinct_mset_union by blast
  done

lemma in_find_key_same_hp_parent:
  \<open>x' \<in># mset_nodes m' \<Longrightarrow>
    distinct_mset (mset_nodes h) \<Longrightarrow>
    find_key a h = Some m' \<Longrightarrow>
    hp_parent a h = None \<Longrightarrow>
    \<exists>y. hp_prev a h = Some y \<Longrightarrow>
    hp_parent x' h = hp_parent x' m'\<close>
  by (induction a h rule: find_key.induct)
   (auto split: if_splits intro: in_find_key_children_same_hp_parent)


lemma in_find_key_children_same_hp_parent2:
  \<open>x' \<noteq> k \<Longrightarrow>
    x' \<in># mset_nodes m' \<Longrightarrow>
    x \<notin># sum_list (map mset_nodes c) \<Longrightarrow>
    distinct_mset (sum_list (map mset_nodes c)) \<Longrightarrow>
    find_key_children k c = Some m' \<Longrightarrow> hp_parent x' (Hp x n c) = hp_parent x' m'\<close>
  apply (induction k c rule: find_key_children.induct)
  subgoal
    by (auto split: if_splits option.splits simp: hp_parent_simps_single_if hp_parent_children_cons)
  subgoal for k xa na c xs
    apply (auto split: if_splits option.splits simp: hp_parent_simps_single_if hp_parent_children_cons)
    apply (metis add_diff_cancel_left' distinct_mem_diff_mset hp_parent_children_None_notin)
    apply (metis hp_node_None_notin2 hp_node_children_None_notin2 hp_node_in_find_key_children sum_image_mset_sum_map)
    apply (metis hp.sel(1) hp_parent_in_nodes2 mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(2) sum_image_mset_sum_map)
    apply (metis disjunct_not_in distinct_mset_add find_key_noneD find_key_none_iff mset_map mset_nodes_find_key_children_subset mset_subset_eqD node_hd_in_sum option.sel sum_mset_sum_list)
    apply (metis hp_node_None_notin2 hp_node_children_None_notin2 hp_node_in_find_key_children sum_image_mset_sum_map)
    apply (metis hp.sel(1) hp_parent_in_nodes2 mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(2) sum_image_mset_sum_map)
    apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (metis basic_trans_rules(31) distinct_mset_union ex_hp_node_children_Some_in_mset_nodes hp.sel(1) hp_node_children_simps(1) hp_parent_in_nodes mset_nodes_find_key_children_subset option.sel option.simps(2) set_mset_mono sum_image_mset_sum_map union_commute)
    apply (metis distinct_mset_union hp_parent_children_hd_None option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (metis disjunct_not_in distinct_mset_add hp_parent_children_None_notin mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (metis distinct_mset_union hp.sel(1) hp_parent_in_nodes mset_nodes_find_key_children_subset mset_subset_eqD option.sel option.simps(2) sum_image_mset_sum_map)
    apply (metis mset_nodes_find_key_children_subset mset_subset_eqD option.sel option_last_Nil option_last_Some_iff(2) sum_image_mset_sum_map)
    apply (metis disjunct_not_in distinct_mset_add hp_node_None_notin2 hp_node_children_None_notin2 hp_node_in_find_key_children hp_parent_children_None_notin sum_image_mset_sum_map)
    apply (metis distinct_mset_union hp_parent_children_hd_None option.simps(2) sum_image_mset_sum_map)
    using distinct_mset_union by blast
  done

lemma in_find_key_same_hp_parent2:
  \<open>x' \<in># mset_nodes m' \<Longrightarrow>
    distinct_mset (mset_nodes h) \<Longrightarrow>
    find_key a h = Some m' \<Longrightarrow>
    x' \<noteq> a \<Longrightarrow>
    hp_parent x' h = hp_parent x' m'\<close>
  by (induction a h rule: find_key.induct)
   (auto split: if_splits intro: in_find_key_children_same_hp_parent2)

lemma encoded_hp_prop_list_remove_find:
  fixes h :: \<open>('a, nat) hp\<close> and a arr and hs :: \<open>('a, nat) hp multiset\<close>
  defines \<open>arr\<^sub>1 \<equiv> (if hp_parent a h = None then arr else hp_update_child (node (the (hp_parent a h))) (map_option node (hp_next a h)) arr)\<close>
  defines \<open>arr\<^sub>2 \<equiv> (if hp_prev a h = None then arr\<^sub>1 else hp_update_nxt (node (the (hp_prev a h))) (map_option node (hp_next a h)) arr\<^sub>1)\<close>
  defines \<open>arr\<^sub>3 \<equiv> (if hp_next a h = None then arr\<^sub>2 else hp_update_prev (node (the (hp_next a h))) (map_option node (hp_prev a h)) arr\<^sub>2)\<close>
  defines \<open>arr\<^sub>4 \<equiv> (if hp_next a h = None then arr\<^sub>3 else hp_update_parents (node (the (hp_next a h))) (map_option node (hp_parent a h)) arr\<^sub>3)\<close>
  defines \<open>arr' \<equiv> hp_update_parents a None (hp_update_prev a None (hp_update_nxt a None arr\<^sub>4))\<close>
  assumes enc: \<open>encoded_hp_prop_list \<V> (add_mset h {#}) [] arr\<close>
  shows \<open>encoded_hp_prop_list \<V> ((if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
        (if find_key a h = None then {#} else {#the (find_key a h)#})) []
        arr'\<close>
proof -
  obtain prevs nxts childs parents scores where
    arr: \<open>arr = ((prevs, nxts, childs, parents, scores))\<close> and
    dist: \<open>distinct_mset (mset_nodes h)\<close> and
    \<V>: \<open>set_mset (mset_nodes h) \<subseteq> set_mset \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  have find_key_in_nodes: \<open>find_key a h \<noteq> None \<Longrightarrow> node (the (find_key a h)) \<in># mset_nodes h\<close>
    by (cases \<open>a \<in># mset_nodes h\<close>)
   	 (use find_key_None_or_itself[of a h] in \<open>auto simp del: find_key_None_or_itself\<close>)
  have in_find_key_in_nodes1: \<open>x \<in># mset_nodes y \<Longrightarrow> find_key a h = Some y \<Longrightarrow> x \<in># mset_nodes h\<close> for x y
    using mset_nodes_find_key_subset[of a h]
    by auto
  have [simp]: \<open>find_key a h = None \<Longrightarrow> remove_key a h = Some h\<close>
    by (metis find_key.simps find_key_none_iff hp.exhaust_sel hp_node_None_notin2
      hp_node_children_None_notin2 hp_node_children_simps2 option_last_Nil option_last_Some_iff(2)
      remove_key_notin_unchanged)
  have HX1: \<open>
    (find_key (node m') h \<noteq> None \<Longrightarrow>
  distinct_mset
   (mset_nodes (the (find_key (node m') h)) +
    (if hp_next (node m') h = None then {#}
     else mset_nodes (the (hp_next (node m') h))))) \<Longrightarrow>
    x' \<in># mset_nodes m' \<Longrightarrow>
    x' \<notin># mset_nodes y' \<Longrightarrow>
    find_key (node y) h = Some y \<Longrightarrow>
    m' = y' \<or> m' = y \<Longrightarrow>
    hp_next (node y) h \<noteq> None \<Longrightarrow>
    x' = node (the (hp_next (node y) h)) \<Longrightarrow>
    map_option node (hp_prev (node y) h) = map_option node (hp_prev (node (the (hp_next (node y) h))) m')\<close>
    for y y' m' x'
    by (smt (z3) distinct_mset_iff mset_add node_in_mset_nodes option.distinct(1) option.sel union_mset_add_mset_left union_mset_add_mset_right)
  have
    dist: \<open>distinct_mset (mset_nodes h)\<close> and
    nxts: \<open>(\<forall>m'\<in>#{#h#}. \<forall>x\<in>#mset_nodes m'. nxts x = map_option node (hp_next x m'))\<close> and
    prevs: \<open>(\<forall>m\<in>#{#h#}. \<forall>x\<in>#mset_nodes m. prevs x = map_option node (hp_prev x m))\<close> and
    childs: \<open>(\<forall>m\<in>#{#h#}. \<forall>x\<in>#mset_nodes m. childs x = map_option node (hp_child x m))\<close> and
    parents: \<open>(\<forall>m\<in>#{#h#}. \<forall>x\<in>#mset_nodes m. parents x = map_option node (hp_parent x m))\<close> and
    scores: \<open>(\<forall>m\<in>#{#h#}. \<forall>x\<in>#mset_nodes m. scores x = hp_score x m)\<close> and
    empty_outside: \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# {#h#} + mset_nodes `# mset [])) prevs\<close>
      \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# {#h#} + mset_nodes `# mset [])) parents\<close>
    using enc unfolding encoded_hp_prop_list_def prod.simps arr by auto
  let ?a = \<open>(if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
      (if find_key a h = None then {#} else {#the (find_key a h)#})\<close>
  have H: \<open>remove_key a h \<noteq> None \<Longrightarrow> node (the (remove_key a h)) \<in># mset_nodes h\<close>
    by (metis remove_key.simps get_min2.simps hp.exhaust_sel option.collapse option.distinct(2) remove_key_notin_unchanged)
  show ?thesis
    supply [[goals_limit=1]]
    using dist
    unfolding arr hp_update_child_def hp_update_nxt_def hp_update_prev_def case_prod_beta hp_update_parents_def
      encoded_hp_prop_list_def prod.simps apply -

  proof (intro conjI impI ballI)
    show \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# ?a +
      mset_nodes `# mset []))\<close>
      using dist
      apply (auto simp: find_remove_mset_nodes_full)
      apply (metis distinct_mset_mono' mset_nodes_find_key_subset option.distinct(2) option.sel)
      done
  next
    show \<open>set_mset (\<Sum>\<^sub># (mset_nodes `#
     ((if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
      (if find_key a h = None then {#} else {#the (find_key a h)#})) +
     mset_nodes `# mset []))
      \<subseteq> set_mset \<V>\<close>
      using \<V> apply (auto dest: in_find_key_in_nodes1)
      apply (metis Set.basic_monos(7) in_remove_key_in_nodes option.distinct(2) option.sel)
      done
  next
    fix m' and x'
    assume \<open>m'\<in>#?a\<close> and \<open>x' \<in># mset_nodes m'\<close>
    then show \<open>fst (snd arr') x' = map_option node (hp_next x' m')\<close>
      using nxts dist H
        hp_next_find_key[of h a x'] hp_next_find_key_itself[of h a]
        in_remove_key_in_nodes[of a h x'] in_find_key_notin_remove_key[of h a x']
        in_find_key_in_nodes[of a h x']
      unfolding assms(1-5) arr
      using hp_next_remove_key_other[of h a x'] find_key_None_or_itself[of a h]
        hp_next_find_key_itself[of h a] has_prev_still_in_remove_key[of h a]
        in_remove_key_changed[of a h]
        hp_parent_itself[of h] remove_key_None_iff[of a h] find_key_head_node_iff[of h m']
      by (auto simp add: hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
        map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
  next
    fix m' and x'
    assume M': \<open>m'\<in>#?a\<close> \<open>x' \<in># mset_nodes m'\<close>
    then show \<open>fst arr' x' = map_option node (hp_prev x' m')\<close>
      using prevs H dist
        hp_prev_find_key[of h a x']
        in_remove_key_in_nodes[of a h x'] in_find_key_notin_remove_key[of h a x']
        in_find_key_in_nodes[of a h x']
      unfolding assms(1-5) arr
      using hp_prev_remove_key_other[of h a x'] find_key_None_or_itself[of a h]
        hp_prev_find_key_itself[of h a] has_prev_still_in_remove_key[of h a]
        in_remove_key_changed[of a h]
        hp_parent_itself[of h] remove_key_None_iff[of a h]
        find_key_head_node_iff[of h m']
      using hp_prev_and_next_same_node[of h x' m' \<open>the (hp_next (node m') h)\<close>]
        distinct_mset_find_node_next[of h \<open>node m'\<close> \<open>the (find_key (node m') h)\<close>]
      apply (simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
        map_option.compositionality comp_def map_option_node_hp_prev_remove_key
        split: if_splits  del: find_key_None_or_itself hp_parent_itself)
      apply (intro conjI impI allI)
      subgoal
        by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
          map_option.compositionality comp_def map_option_node_hp_prev_remove_key
          split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
          map_option.compositionality comp_def map_option_node_hp_prev_remove_key
          split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
        apply (intro conjI impI allI)
        subgoal
          by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key
            split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
        subgoal
          unfolding eq_commute[of _ x']
          by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key
            split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
        subgoal
          using node_in_mset_nodes[of \<open>the (hp_next (node m') h)\<close>]
          unfolding eq_commute[of _ x']
          by auto
        subgoal
          using node_in_mset_nodes[of \<open>the (hp_next (node m') h)\<close>]
          unfolding eq_commute[of _ x']
          by auto
        subgoal for y y'
          apply (clarsimp simp add: atomize_not hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key hp_update_parents_def
            split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
          apply (intro conjI impI)
          using HX1[of y x' y' m']
          apply (auto simp add: atomize_not hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key hp_update_parents_def
            split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
          done
        subgoal
          by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key
            split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
        subgoal
          by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_prev_remove_key
            split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
        done
  next
    fix m' and x'
    assume M': \<open>m'\<in>#?a\<close> \<open>x' \<in># mset_nodes m'\<close>
    have helper1: \<open>hp_parent (node yb) yyy = None\<close>
      if
        \<open>distinct_mset (mset_nodes yyy)\<close> and
        \<open>node y \<in># mset_nodes h\<close> and
        \<open>hp_parent (node yyy) h = Some y\<close> and
        \<open>hp_child (node y) h = Some yb\<close>
      for y :: \<open>('a, nat) hp\<close> and ya :: \<open>('a, nat) hp\<close> and yb :: \<open>('a, nat) hp\<close> and z :: \<open>('a, nat) hp\<close> and yyy
      using childs[simplified]
      by (metis dist hp_child_hp_parent hp_parent_itself option.map_sel option.sel option_last_Nil option_last_Some_iff(1)
        that)
    have helper2: \<open>hp_child (node ya) yyy \<noteq> hp_child (node ya) h\<close>
      if
        \<open>distinct_mset (mset_nodes yyy)\<close> and
        \<open>hp_parent (node yyy) h = Some ya\<close>
        \<open>node ya \<in># mset_nodes h\<close>
      for y :: \<open>('a, nat) hp\<close> and ya :: \<open>('a, nat) hp\<close> and yyy yya
      using childs[simplified]
      by (metis dist that hp_child_hp_parent hp_parent_hp_child hp_parent_itself map_option_is_None option.map_sel option.sel option_last_Nil option_last_Some_iff(1))
    have helper4: \<open>map_option node (map_option (\<lambda>x. the (remove_key (node yy) x)) (hp_child (x') h)) = map_option node (hp_child (x') h)\<close>
      if
        \<open>\<exists>y. hp_child (x') h = Some y \<Longrightarrow> \<exists>z. hp_parent (node (the (hp_child (x') h))) h = Some z \<and> node z = x'\<close> and
        \<open>node h = node yya \<Longrightarrow> find_key (node yya) h \<noteq> Some yya\<close> and
        \<open>hp_parent (node yy) h = None\<close>
      for yya yy x'
      using that childs[simplified] dist apply -
      using distinct_sum_next_prev_child[of h x']
      apply (auto simp: map_option_node_remove_key_iff)
      apply (subst eq_commute)
      apply (rule ccontr)
      apply (subst (asm) map_option_node_remove_key_iff)
      apply simp
      apply (meson distinct_mset_add)
      by (auto simp: remove_key_None_iff)

    have \<open>find_key a h \<noteq> None \<Longrightarrow> distinct_mset (mset_nodes (the (find_key a h)))\<close>
      by (meson dist distinct_mset_mono' mset_nodes_find_key_subset)

    then show \<open>fst (snd (snd arr')) x' = map_option node (hp_child x' m')\<close>
      using childs dist H M'
        hp_child_find_key[of h a x']
        in_remove_key_in_nodes[of a h x'] in_find_key_notin_remove_key[of h a x']
        in_find_key_in_nodes[of a h x']
        hp_parent_hp_child[of h x'] hp_child_hp_parent[of h x']
         hp_child_hp_parent[of h x'] (*hp_parent_hp_child[of \<open>the (find_key a h)\<close> x']*)
          hp_parent_hp_child[of \<open>the (find_key a h)\<close> x']
      unfolding assms(1-5) arr
      using hp_child_remove_key_other[of h a x'] find_key_None_or_itself[of a h]
        hp_next_find_key_itself[of h a] has_prev_still_in_remove_key[of h a]
        in_remove_key_changed[of a h]
        hp_parent_itself[of h] remove_key_None_iff[of a h] find_key_head_node_iff[of h m']

      apply (simp split: if_splits(2)  del: find_key_None_or_itself hp_parent_itself)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
        map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
        map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
      apply (solves \<open>auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def helper2
        map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself\<close>)[]
      apply (solves \<open>auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def helper2
        map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself\<close>)[]

      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def
        split: if_splits simp del: find_key_None_or_itself hp_parent_itself)
      apply (intro conjI impI)

      subgoal for yy yya
        apply auto
        apply (subst (asm) helper4)
        apply assumption+
        apply simp
        done
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      subgoal by auto
      subgoal for y y'
        using hp_child_remove_key_other[of h a x', symmetric]
        apply (auto simp: map_option.compositionality comp_def)
        apply (subst (asm) map_option_node_map_option_node_iff)
        apply auto[]
        apply (smt (verit, del_insts) None_eq_map_option_iff node_remove_key_itself_iff option.distinct(2) option.exhaust_sel option.map_sel remove_key_None_iff)
        apply (smt (verit) None_eq_map_option_iff node_remove_key_itself_iff option.exhaust_sel option.simps(9) remove_key_None_iff)
        by (metis (no_types, lifting) map_option_cong node_remove_key_itself_iff option.sel option.simps(3) remove_key_None_iff)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal
        apply auto
        by (metis no_relative_ancestor_or_notin)
      subgoal
        apply auto
        by (smt (verit, del_insts) None_eq_map_option_iff hp.exhaust_sel hp_child_remove_is_remove_hp_child node_remove_key_itself_iff option.exhaust_sel option.map(2) option.simps(1))
      subgoal
        by (smt (verit, ccfv_SIG) None_eq_map_option_iff node_remove_key_itself_iff option.exhaust_sel option.map_sel remove_key_None_iff)
      subgoal
        by (smt (verit, ccfv_SIG) None_eq_map_option_iff node_remove_key_itself_iff option.exhaust_sel option.map_sel remove_key_None_iff)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      apply (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def hp_update_parents_def
          map_option.compositionality comp_def map_option_node_hp_next_remove_key
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
      subgoal
        using distinct_sum_next_prev_child[of h x']
        apply (auto simp: remove_key_None_iff map_option_node_remove_key_iff)
        apply (subst (asm) map_option_node_remove_key_iff)
        apply simp
        apply (meson distinct_mset_add)
        by (auto simp: remove_key_None_iff)
      done

    have helper1: False
      if
        \<open>distinct_mset (mset_nodes h)\<close> and
        \<open>node y \<in># mset_nodes m'\<close> and
        \<open>node y \<in># mset_nodes ya\<close> and
        \<open>remove_key a h = Some m'\<close> and
        \<open>find_key a h = Some ya\<close> and
        \<open>x' = node y\<close>
      for ya :: \<open>('a, nat) hp\<close> and y :: \<open>('a, nat) hp\<close> and yb :: \<open>('a, nat) hp\<close>
      by (metis that Some_to_the in_find_key_notin_remove_key option_last_Nil option_last_Some_iff(2))
    have helper3: \<open>False\<close>
      if
        \<open>distinct_mset (mset_nodes h)\<close> and
        \<open>x' \<in># mset_nodes m'\<close> and
        \<open>x' \<in># mset_nodes ya\<close> and
        \<open>remove_key a h = Some m'\<close> and
        \<open>find_key a h = Some ya\<close>
      for ya :: \<open>('a, nat) hp\<close>
      by (metis that Some_to_the in_find_key_notin_remove_key option_last_Nil option_last_Some_iff(1))
    have helperb4: \<open>False\<close>
      if
        \<open>h = m'\<close> and
        \<open>hp_next a m' = Some z\<close> and
        \<open>find_key a m' = None\<close>
      for z :: \<open>('a, nat) hp\<close> and y :: \<open>('a, nat) hp\<close>
      by (metis that find_key_None_remove_key_ident hp_next_None_notin in_remove_key_changed option.sel option.simps(2))
    have [simp]: \<open>map_option (\<lambda>x. node (the (remove_key a x))) (hp_parent a h) = map_option node (hp_parent a h)\<close>
      for z :: \<open>('a, nat) hp\<close>
      by (smt (verit, ccfv_SIG) None_eq_map_option_iff distinct_mset_find_node_next distinct_mset_union find_key_None_or_itself
            find_key_None_remove_key_ident find_key_notin hp_child_find_key hp_child_hp_parent hp_parent_hp_child hp_parent_in_nodes
            hp_parent_itself in_remove_key_changed node_remove_key_itself_iff option.exhaust_sel option.map_sel option.sel
            option.sel remove_key_None_iff
            dist)

    have helperc1: \<open>a \<in># mset_nodes m' \<Longrightarrow> h = m' \<Longrightarrow> find_key a m' = None \<Longrightarrow> False\<close>
      by (metis find_key_None_remove_key_ident in_remove_key_changed option.sel option_hd_Nil option_hd_Some_iff(1))

    have helperc2: \<open>
      \<forall>x\<in>#mset_nodes m'. parents x = map_option node (hp_parent x m') \<Longrightarrow>
      hp_parent x' m' = map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' m') \<Longrightarrow>
      map_option node (hp_parent x' m') = map_option (\<lambda>x. node (the (remove_key a x))) (hp_parent x' m')\<close>
      by (metis (mono_tags, lifting) None_eq_map_option_iff map_option_cong option.map_sel option.sel)
    have helperc3: False
      if
        \<open>remove_key a h = Some m'\<close> and
        \<open>hp_parent a m' = Some (the (remove_key a y))\<close> and
        \<open>hp_parent a h = Some y\<close>
      for y :: \<open>('a, nat) hp\<close>
      by (metis dist that hp_parent_itself hp_parent_remove_key option.sel option.simps(2))

    have helperc4: \<open>map_option node (hp_parent x' h) =
      map_option node (map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' h))\<close>
      if
        \<open>remove_key a h = Some m'\<close> and
        \<open>hp_parent x' m' = map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' h)\<close> and
        \<open>hp_next a h = None\<close> and
        \<open>hp_parent a h = None\<close> and
        \<open>hp_prev a h = None\<close>
      by (metis that find_key_None_remove_key_ident find_key_notin no_relative_ancestor_or_notin option.sel option.simps(2) remove_key_None_iff)

    have helperc5: \<open>map_option node (hp_parent x' h) = map_option node (map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' h))\<close>
      if
        \<open>\<forall>x\<in>#mset_nodes h. parents x = map_option node (hp_parent x h)\<close> and
        \<open>distinct_mset (mset_nodes h)\<close> and
        \<open>node m' \<in># mset_nodes h\<close> and
        \<open>remove_key a h = Some m'\<close> and
        \<open>hp_parent x' m' = map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' h)\<close> and
        \<open>x' \<notin># the (map_option mset_nodes (find_key a h))\<close>
        \<open>node (the (None :: ('a, nat) hp option)) = x'\<close>
      using that apply -
      apply (rule map_option_node_map_option_node_iff)
      apply (meson distinct_mset_hp_parent option.exhaust_sel)
      apply auto[]
      apply (smt (verit, ccfv_threshold) Duplicate_Free_Multiset.distinct_mset_mono None_eq_map_option_iff find_key_None_or_itself
        find_key_None_remove_key_ident hp_child_find_key hp_child_hp_parent hp_parent_hp_child hp_parent_remove_key in_remove_key_changed
        mset_nodes_find_key_subset node_in_mset_nodes option.map_sel option.sel option_last_Nil option_last_Some_iff(2) remove_key_notin_unchanged)
      done
    have helperc6: \<open>map_option node (hp_parent x' h) = map_option (\<lambda>x. node (the (remove_key a x))) (hp_parent x' h)\<close>
      if
        \<open>\<forall>x\<in>#mset_nodes h. parents x = map_option node (hp_parent x h)\<close> and
        \<open>remove_key a h = Some m'\<close> and
        \<open>hp_parent x' m' = map_option (\<lambda>x. the (remove_key a x)) (hp_parent x' h)\<close> and
        \<open>x' \<notin># the (map_option mset_nodes (find_key a h))\<close>
      using that dist
      by ((smt (verit, ccfv_SIG) Duplicate_Free_Multiset.distinct_mset_mono None_eq_map_option_iff find_key_None_or_itself find_key_None_remove_key_ident
        hp_child_find_key hp_child_hp_parent hp_parent_None_notin hp_parent_hp_child map_option_cong mset_nodes_find_key_subset node_in_mset_nodes node_remove_key_itself_iff
            option.map_sel option.sel option_last_Nil option_last_Some_iff(2) remove_key_None_iff)+)[]
    have helperd1: \<open>hp_parent a m' = None\<close>
      if
        \<open>a \<in># mset_nodes h\<close> and
        \<open>find_key a h = Some m'\<close> and
        \<open>hp_next a h = None\<close> and
        \<open>hp_parent a h = None\<close> and
        \<open>hp_prev a h = None\<close>
      by (metis that ACIDS.find_key_node_itself no_relative_ancestor_or_notin option.sel)
    have helperd2: \<open>hp_parent a m' = None\<close>
      if
        \<open>find_key a h = Some m'\<close>
      by (metis dist that Duplicate_Free_Multiset.distinct_mset_mono find_key_None_or_itself hp_parent_itself mset_nodes_find_key_subset option.sel option.simps(3))
    have helperd3:  \<open>node ya \<notin># mset_nodes m'\<close>
      if
        \<open>distinct_mset (mset_nodes m' + mset_nodes ya)\<close>
      for ya :: \<open>('a, nat) hp\<close>
      by (smt (verit, best) that disjunct_not_in distinct_mset_add node_in_mset_nodes option.sel option.simps(3))

   show \<open>fst (snd (snd (snd arr'))) x' = map_option node (hp_parent x' m')\<close>
      using parents dist H M' apply -
      apply (frule in_remove_key_in_find_keyD)
      apply (solves auto)[]
      apply (solves auto)[]
      unfolding union_iff
      apply (rule disjE, assumption)
      subgoal
          unfolding assms(1-5) arr
          using find_key_None_remove_key_ident[of a h]
            hp_parent_remove_key_other[of h a x']
            distinct_mset_hp_parent[of h a \<open>the (hp_parent a h)\<close>]
          by (clarsimp simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
            map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def in_the_default_empty_iff
            intro: helper1
            split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
           (intro conjI impI allI; auto dest: helper1 helper3
            dest: helperb4 hp_next_not_same_node
            intro: helperc1 helperc2 helperc3
             dest: helperc4 helperc5 intro: helperc6)+
      subgoal
          unfolding assms(1-5) arr
          using in_find_key_same_hp_parent[of x' m' h a]
            in_find_key_same_hp_parent2[of x' m' h a]
            distinct_mset_find_node_next[of h a \<open>the (find_key a h)\<close>]
          by (cases \<open>x' = a\<close>) (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def helperd3
            map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def in_the_default_empty_iff
            split: if_splits  simp del: find_key_None_or_itself hp_parent_itself
            intro: helperd1 simp: helperd2)
      done

    show \<open>snd (snd (snd (snd arr'))) x' = map_option score (hp_node x' m')\<close>
      using scores M' dist H
        hp_child_find_key[of h a x']
        in_remove_key_in_nodes[of a h x'] in_find_key_notin_remove_key[of h a x']
        in_find_key_in_nodes[of a h x']
        hp_parent_hp_child[of h x'] hp_child_hp_parent[of h x']
        hp_node_in_find_key[of h a x']
      unfolding assms(1-5) arr
      using hp_score_remove_key_other[of h a x'] find_key_None_or_itself[of a h]
        hp_next_find_key_itself[of h a] has_prev_still_in_remove_key[of h a]
        in_remove_key_changed[of a h]
        hp_parent_itself[of h] remove_key_None_iff[of a h] find_key_head_node_iff[of h m']
        node_remove_key_in_mset_nodes[of a h]
      by (auto simp add:  hp_update_child_def hp_update_prev_def hp_update_nxt_def
        map_option.compositionality comp_def map_option_node_hp_next_remove_key hp_update_parents_def in_the_default_empty_iff
        split: if_splits  simp del: find_key_None_or_itself hp_parent_itself)
  next
    fix x :: 'a
    assume \<open>x \<in># \<Sum>\<^sub># (mset_nodes `# mset [])\<close>
    then show
      \<open>fst (snd arr') x = map_option node (hp_next_children x [])\<close>
      \<open>fst arr' x = map_option node (hp_prev_children x [])\<close>
      \<open>fst (snd (snd arr')) x = map_option node (hp_child_children x [])\<close> and
      \<open>fst (snd (snd (snd arr'))) x = map_option node (hp_parent_children x [])\<close>
      \<open>snd (snd (snd (snd arr'))) x = map_option score (hp_node_children x [])\<close>
      by auto
  next
    have H: \<open>(\<Sum>\<^sub># (mset_nodes `#
     ((if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
      (if find_key a h = None then {#} else {#the (find_key a h)#})) +
     mset_nodes `# mset [])) = (\<Sum>\<^sub>#(mset_nodes `# {#h#}))\<close>
      using find_remove_mset_nodes_full[of h a \<open>the (remove_key a h)\<close> \<open>the (find_key a h)\<close>] find_key_None_remove_key_ident[of a h]
        dist
      apply (cases \<open>find_key a h\<close>; cases \<open>remove_key a h\<close>; auto simp: ac_simps)
      apply (metis find_key_head_node_iff option.sel remove_key_None_iff)
      done
    show \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# ?a + mset_nodes `# mset []))
      (fst arr')\<close>
      using empty_outside hp_next_in_nodes2[of a h] unfolding H
      unfolding assms(1-5) arr by (auto simp: hp_update_parents_def hp_update_prev_def hp_update_child_def
        hp_update_nxt_def empty_outside_alt_def)
    show \<open>empty_outside (\<Sum>\<^sub># (mset_nodes `# ?a + mset_nodes `# mset []))
      (fst (snd (snd (snd arr'))))\<close>
      using empty_outside hp_next_in_nodes2[of a h] unfolding H
      unfolding assms(1-5) arr by (auto simp: hp_update_parents_def hp_update_prev_def hp_update_child_def
        hp_update_nxt_def empty_outside_alt_def)
  qed
qed


text \<open>In the kissat implementation prev and parent are merged.\<close>
lemma in_node_iff_prev_parent_or_root:
  assumes \<open>distinct_mset (mset_nodes h)\<close>
  shows \<open>i \<in># mset_nodes h \<longleftrightarrow> hp_prev i h \<noteq> None \<or> hp_parent i h \<noteq> None \<or> i = node h\<close>
  using assms
proof (induction h arbitrary: i)
  case (Hp x1a x2a x3a) note IH = this(1) and dist = this(2)
  have ?case if pre:\<open>i \<noteq> x1a\<close> \<open>i \<in># sum_list (map mset_nodes x3a)\<close>
  proof -
    obtain c where
      c: \<open>c \<in> set x3a\<close> and
      i_c: \<open>i \<in>#mset_nodes c\<close>
      using pre
      unfolding in_mset_sum_list_iff
      by auto
    have dist_c: \<open>distinct_mset (mset_nodes c)\<close>
      using c dist by (simp add: distinct_mset_add sum_list_map_remove1)

    obtain ys zs where x3a_def: \<open>x3a = ys @ c # zs\<close>
      using split_list[OF c] by auto
    have i_ys: \<open>i \<notin># \<Sum>\<^sub># (mset_nodes `# mset ys)\<close> \<open>i \<notin># sum_list (map mset_nodes zs)\<close>
      using dist i_c
      by (auto simp: x3a_def disjunct_not_in distinct_mset_add)
    have dist_c_zs: \<open>distinct_mset (mset_nodes c + sum_list (map mset_nodes zs))\<close>
      using WB_List_More.distinct_mset_union2 dist x3a_def by auto
    consider
      \<open>i = node c\<close> |
      \<open>i \<noteq> node c\<close>
      by blast
    then show ?case
    proof cases
      case 2
      then have \<open>hp_prev i c \<noteq> None \<Longrightarrow> hp_prev_children i x3a \<noteq> None\<close>
        using c dist i_c i_ys dist_c_zs by (auto simp: x3a_def hp_prev_children_skip_last_append[of _ \<open>[_]\<close>, simplified])
      moreover have \<open>hp_parent i c \<noteq> None \<Longrightarrow> hp_parent_children i x3a \<noteq> None\<close>
        using c dist i_c by (auto dest!: split_list simp: hp_parent_children_append_case hp_parent_children_cons
          split: option.splits)
      ultimately show ?thesis
        using i_c 2 IH[of c i, OF c dist_c]
        by (cases \<open>hp_prev i c\<close>)
         (auto simp del: hp_prev_None_notin hp_parent_None_notin simp: hp_parent_simps_single_if)
    next
      case 1
       have \<open>hp_prev_children (node c) (ys @ c # zs) = (option_last ys)\<close>
        using i_ys hp_prev_children_Cons_append_found[of i ys \<open>hps c\<close> zs \<open>score c\<close>] 1 dist_c
        by (cases c) (auto simp del: hp_prev_children_Cons_append_found)
      then show ?thesis
        using c dist i_c i_ys dist_c_zs by (auto dest!: simp: x3a_def 1)
    qed
  qed
  then show ?case
    using dist IH
    by (auto simp add: hp_parent_none_children)
qed

lemma encoded_hp_prop_list_in_node_iff_prev_parent_or_root:
  assumes \<open>encoded_hp_prop_list_conc arr h\<close> and \<open>snd h \<noteq> None\<close>
  shows \<open>i \<in># mset_nodes (the (snd h)) \<longleftrightarrow> hp_read_prev i (fst (snd arr)) \<noteq> None \<or> hp_read_parent i (fst (snd arr)) \<noteq> None \<or> Some i = snd (snd arr)\<close>
  using assms in_node_iff_prev_parent_or_root[of \<open>the (snd h)\<close> i]
  by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def
    simp del: hp_prev_None_notin hp_parent_None_notin)

(*TODO Move*)
fun update_source_node where
  \<open>update_source_node i (\<V>,arr,_) = (\<V>, arr, i)\<close>
fun source_node :: \<open>(nat multiset \<times> (nat,'c) hp_fun \<times> nat option) \<Rightarrow> _\<close> where
  \<open>source_node (\<V>,arr,h) = h\<close>
fun hp_read_nxt' :: \<open>_\<close> where
  \<open>hp_read_nxt' i (\<V>, arr, h) = hp_read_nxt i arr\<close>
fun hp_read_parent' :: \<open>_\<close> where
  \<open>hp_read_parent' i (\<V>, arr, h) = hp_read_parent i arr\<close>

fun hp_read_score' :: \<open>_\<close> where
  \<open>hp_read_score' i (\<V>, arr, h) = (hp_read_score i arr)\<close>
fun hp_read_child' :: \<open>_\<close> where
  \<open>hp_read_child' i (\<V>, arr, h) = hp_read_child i arr\<close>

fun hp_read_prev' :: \<open>_\<close> where
  \<open>hp_read_prev' i (\<V>, arr, h) = hp_read_prev i arr\<close>

fun hp_update_child' where
  \<open>hp_update_child' i p(\<V>, u, h) = (\<V>, hp_update_child i p u, h)\<close>

fun hp_update_parents' where
  \<open>hp_update_parents' i p(\<V>, u, h) = (\<V>, hp_update_parents i p u, h)\<close>

fun hp_update_prev' where
  \<open>hp_update_prev' i p (\<V>, u, h) = (\<V>, hp_update_prev i p u, h)\<close>

fun hp_update_nxt' where
  \<open>hp_update_nxt' i p(\<V>, u, h) = (\<V>, hp_update_nxt i p u, h)\<close>

fun hp_update_score' where
  \<open>hp_update_score' i p(\<V>, u, h) = (\<V>, hp_update_score i p u, h)\<close>


definition maybe_hp_update_prev' where
  \<open>maybe_hp_update_prev' child ch arr =
     (if child = None then arr else hp_update_prev' (the child) ch arr)\<close>

definition maybe_hp_update_nxt' where
  \<open>maybe_hp_update_nxt' child ch arr =
     (if child = None then arr else hp_update_nxt' (the child) ch arr)\<close>

definition maybe_hp_update_parents' where
  \<open>maybe_hp_update_parents' child ch arr =
     (if child = None then arr else hp_update_parents' (the child) ch arr)\<close>

definition maybe_hp_update_child' where
  \<open>maybe_hp_update_child' child ch arr =
     (if child = None then arr else hp_update_child' (the child) ch arr)\<close>

definition unroot_hp_tree where
  \<open>unroot_hp_tree arr h = do {
    ASSERT (h \<in># fst arr);
    let a = source_node arr;
    ASSERT (a \<noteq> None \<longrightarrow> the a \<in># fst arr);
    let nnext = hp_read_nxt' h arr;
    let parent = hp_read_parent' h arr;
    let prev = hp_read_prev' h arr;
    if prev = None \<and> parent = None \<and> Some h \<noteq> a then RETURN (update_source_node None arr)
    else if Some h = a then RETURN (update_source_node None arr)
    else do {
      ASSERT (a \<noteq> None);
      ASSERT (nnext \<noteq> None \<longrightarrow> the nnext \<in># fst arr);
      ASSERT (parent \<noteq> None \<longrightarrow> the parent \<in># fst arr);
      ASSERT (prev \<noteq> None \<longrightarrow> the prev \<in># fst arr);
      let a' = the a;
      let arr = maybe_hp_update_child' parent nnext arr;
      let arr = maybe_hp_update_nxt' prev nnext arr;
      let arr = maybe_hp_update_prev' nnext prev arr;
      let arr = maybe_hp_update_parents' nnext parent arr;

      let arr = hp_update_nxt' h None arr;
      let arr = hp_update_prev' h None arr;
      let arr = hp_update_parents' h None arr;

      let arr = hp_update_nxt' h (Some a') arr;
      let arr = hp_update_prev' a' (Some h) arr;
      RETURN (update_source_node None arr)
    }
}\<close>

lemma unroot_hp_tree_alt_def:
  \<open>unroot_hp_tree arr h = do {
    ASSERT (h \<in># fst arr);
    let a = source_node arr;
    ASSERT (a \<noteq> None \<longrightarrow> the a \<in># fst arr);
    let nnext = hp_read_nxt' h arr;
    let parent = hp_read_parent' h arr;
    let prev = hp_read_prev' h arr;
    if prev = None \<and> parent = None \<and> Some h \<noteq> a then RETURN (update_source_node None arr)
    else if Some h = a then RETURN (update_source_node None arr)
    else do {
      ASSERT (a \<noteq> None);
      ASSERT (nnext \<noteq> None \<longrightarrow> the nnext \<in># fst arr);
      ASSERT (parent \<noteq> None \<longrightarrow> the parent \<in># fst arr);
      ASSERT (prev \<noteq> None \<longrightarrow> the prev \<in># fst arr);
      let a' = the a;
       arr \<leftarrow> do {
         let arr = maybe_hp_update_child' parent nnext arr;
         let arr = maybe_hp_update_nxt' prev nnext arr;
         let arr = maybe_hp_update_prev' nnext prev arr;
         let arr = maybe_hp_update_parents' nnext parent arr;

         let arr = hp_update_nxt' h None arr;
         let arr = hp_update_prev' h None arr;
         let arr = hp_update_parents' h None arr;

        RETURN (update_source_node None arr)
      };

      let arr = hp_update_nxt' h (Some a') arr;
      let arr = hp_update_prev' a' (Some h) arr;
      RETURN (arr)
      }
}\<close>
  unfolding unroot_hp_tree_def nres_monad3 Let_def
  apply (cases arr)
  by (auto intro!: bind_cong[OF refl] simp: maybe_hp_update_child'_def
    maybe_hp_update_nxt'_def maybe_hp_update_prev'_def maybe_hp_update_parents'_def)

lemma hp_update_fst_snd:
  \<open>hp_update_prev i j (fst (snd arr)) = fst (snd (hp_update_prev' i j arr))\<close>
  \<open>hp_update_nxt i j (fst (snd arr)) = fst (snd (hp_update_nxt' i j arr))\<close>
  \<open>hp_update_parents i j (fst (snd arr)) = fst (snd (hp_update_parents' i j arr))\<close>
  \<open>hp_update_child i j (fst (snd arr)) = fst (snd (hp_update_child' i j arr))\<close>
  by (solves \<open>cases arr; auto\<close>)+

lemma find_remove_mset_nodes_full2:
  \<open>distinct_mset (mset_nodes h) \<Longrightarrow> sum_mset (mset_nodes `# ((if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
        (if find_key a h = None then {#} else {#the (find_key a h)#}))) = mset_nodes h\<close>
  using find_remove_mset_nodes_full[of h a]
  apply (auto)
  apply (auto simp add: find_key_None_remove_key_ident)
  apply (metis find_key_head_node_iff option.sel remove_key_None_iff)
  done

definition encoded_hp_prop_mset2_conc
  :: "'a::linorder multiset \<times> ('a, 'b) hp_fun \<times> 'a option \<Rightarrow>
     'a::linorder multiset \<times> ('a, 'b) hp multiset \<Rightarrow> bool"
  where
  \<open>encoded_hp_prop_mset2_conc = (\<lambda>(\<V>, arr, h) (\<V>', x). \<V> = \<V>' \<and> 
  (encoded_hp_prop_list \<V> x  [] arr))\<close>

lemma fst_update[simp]:
  \<open> fst (hp_update_prev' a b x) = fst x\<close>
  \<open>fst (hp_update_nxt' a b x) = fst x\<close>
  \<open>fst (update_source_node y x) = fst x\<close>
  by (cases x;auto; fail)+

lemma encoded_hp_prop_mset2_conc_combine_list2_conc:
  \<open>encoded_hp_prop_mset2_conc arr (\<V>, {#a,b#}) \<Longrightarrow>
  encoded_hp_prop_list2_conc (hp_update_prev' (node b) (Some (node a)) (hp_update_nxt' (node a) (Some (node b)) (update_source_node None arr))) (\<V>, [a,b])\<close>
  unfolding encoded_hp_prop_mset2_conc_def encoded_hp_prop_list2_conc_alt_def
    encoded_hp_prop_list_def case_prod_beta
  apply (intro conjI)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply (cases arr)
    apply (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
    apply (metis hp_next_None_notin hp_next_children.simps(2) hp_next_children_simps(2) hp_next_children_simps(3))
    by (metis hp_next_None_notin hp_next_children.simps(2) hp_next_children_simps(2) hp_next_children_simps(3))
  subgoal
    apply (cases arr)
    apply (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
    apply (metis hp_prev_None_notin hp_prev_children.simps(2) hp_prev_children_simps(2) hp_prev_children_simps(3))
    by (metis hp_prev_None_notin hp_prev_children.simps(2) hp_prev_children_simps(2) hp_prev_children_simps(3))
  subgoal
    apply (cases arr)
    apply (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
    by (metis hp_child_None_notin hp_child_children_hp_child hp_child_children_simps(2) hp_child_children_simps(3))+
  subgoal
    apply (cases arr)
    apply (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
    by (metis hp_parent_None_notin hp_parent_children_cons hp_parent_children_single_hp_parent option.case_eq_if)
  subgoal
    apply (cases arr)
    apply (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
    by (metis hp_node_None_notin2 hp_node_children_Cons_if)
  subgoal
    by (cases arr)
     (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
  subgoal
    by (cases arr)
     (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
  subgoal
    by (cases arr)
     (auto simp: encoded_hp_prop_list_def hp_update_prev_def hp_update_nxt_def)
  done

lemma update_source_node_fst_simps[simp]:
  \<open>fst (snd (update_source_node None arr)) = fst (snd arr)\<close>
  \<open>fst (update_source_node None arr) = fst arr\<close>
  \<open>snd (snd (update_source_node None arr)) = None\<close>
  by (solves \<open>cases arr; auto\<close>)+

lemma maybe_hp_update_fst_snd: \<open>fst (snd (maybe_hp_update_child' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_child' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_prev' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_prev' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_nxt' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_nxt' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_parents' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_parents' (node (the b)) x arr)))\<close> and
  maybe_hp_update_fst_snd2:
    \<open>( (maybe_hp_update_child' (map_option node b) x arr')) =
    (if b = None then ( arr') else ( (hp_update_child' (node (the b)) x arr')))\<close>
    \<open>( (maybe_hp_update_prev' (map_option node b) x arr')) =
    (if b = None then ( arr') else ( (hp_update_prev' (node (the b)) x arr')))\<close>
    \<open>( (maybe_hp_update_nxt' (map_option node b) x arr')) =
    (if b = None then ( arr') else ( (hp_update_nxt' (node (the b)) x arr')))\<close>
    \<open>( (maybe_hp_update_parents' (map_option node b) x arr')) =
    (if b = None then ( arr') else ( (hp_update_parents' (node (the b)) x arr')))\<close>
    for x b arr
    apply (solves \<open>cases arr; auto simp: maybe_hp_update_child'_def maybe_hp_update_parents'_def
      maybe_hp_update_prev'_def maybe_hp_update_nxt'_def maybe_hp_update_prev'_def
      maybe_hp_update_nxt'_def\<close>)+
    done

lemma fst_hp_update_simp[simp]:
  \<open>fst (hp_update_prev' i x arr) = fst arr\<close>
  \<open>fst (hp_update_nxt' i x arr) = fst arr\<close>
  \<open>fst (hp_update_child' i x arr) = fst arr\<close>
  \<open>fst (hp_update_parents' i x arr) = fst arr\<close>
  by (solves \<open>cases arr; auto\<close>)+

lemma fst_maybe_hp_update_simp[simp]:
  \<open>fst (maybe_hp_update_prev' i y arr) = fst arr\<close>
  \<open>fst (maybe_hp_update_nxt' i y arr) = fst arr\<close>
  \<open>fst (maybe_hp_update_child' i y arr) = fst arr\<close>
  \<open>fst (maybe_hp_update_parents' i y arr) = fst arr\<close>
  by (solves \<open>cases arr; cases i; auto simp: maybe_hp_update_prev'_def maybe_hp_update_nxt'_def
    maybe_hp_update_child'_def maybe_hp_update_parents'_def\<close>)+

lemma encoded_hp_prop_list_remove_find2:
  fixes h :: \<open>('a::linorder, nat) hp\<close> and a arr and hs :: \<open>('a, nat) hp multiset\<close>
  defines \<open>arr\<^sub>1 \<equiv> (if hp_parent a h = None then arr else hp_update_child' (node (the (hp_parent a h))) (map_option node (hp_next a h)) arr)\<close>
  defines \<open>arr\<^sub>2 \<equiv> (if hp_prev a h = None then arr\<^sub>1 else hp_update_nxt' (node (the (hp_prev a h))) (map_option node (hp_next a h)) arr\<^sub>1)\<close>
  defines \<open>arr\<^sub>3 \<equiv> (if hp_next a h = None then arr\<^sub>2 else hp_update_prev' (node (the (hp_next a h))) (map_option node (hp_prev a h)) arr\<^sub>2)\<close>
  defines \<open>arr\<^sub>4 \<equiv> (if hp_next a h = None then arr\<^sub>3 else hp_update_parents' (node (the (hp_next a h))) (map_option node (hp_parent a h)) arr\<^sub>3)\<close>
  defines \<open>arr' \<equiv> hp_update_parents' a None (hp_update_prev' a None (hp_update_nxt' a None arr\<^sub>4))\<close>
  assumes enc: \<open>encoded_hp_prop_mset2_conc arr (\<V>, add_mset h {#})\<close>
  shows \<open>encoded_hp_prop_mset2_conc arr' (\<V>, (if remove_key a h = None then {#} else {#the (remove_key a h)#}) +
        (if find_key a h = None then {#} else {#the (find_key a h)#}))\<close>
    using encoded_hp_prop_list_remove_find[of \<V> h \<open>fst (snd arr)\<close> a] enc
    unfolding assms(1-5) apply -
    unfolding encoded_hp_prop_mset2_conc_def case_prod_beta hp_update_fst_snd
    apply (subst hp_update_fst_snd[symmetric])
    apply (subst hp_update_fst_snd[symmetric])
    apply (subst hp_update_fst_snd[symmetric])
    unfolding maybe_hp_update_fst_snd[symmetric] maybe_hp_update_parents'_def[symmetric]
      maybe_hp_update_nxt'_def[symmetric] maybe_hp_update_prev'_def[symmetric] maybe_hp_update_child'_def[symmetric]
      encoded_hp_prop_mset2_conc_def case_prod_beta hp_update_fst_snd maybe_hp_update_fst_snd2[symmetric]
      maybe_hp_update_fst_snd[symmetric]
    by auto

lemma hp_read_fst_snd_simps[simp]:
  \<open>hp_read_nxt j (fst (snd arr)) = hp_read_nxt' j arr\<close>
  \<open>hp_read_prev j (fst (snd arr)) = hp_read_prev' j arr\<close>
  \<open>hp_read_child j (fst (snd arr)) = hp_read_child' j arr\<close>
  \<open>hp_read_parent j (fst (snd arr)) = hp_read_parent' j arr\<close>
  \<open>hp_read_score j (fst (snd arr)) = hp_read_score' j arr\<close>
  by (solves \<open>cases arr; auto\<close>)+


lemma unroot_hp_tree:
  fixes h :: \<open>(nat, nat)hp option\<close>
  assumes enc: \<open>encoded_hp_prop_list_conc arr (\<V>, h)\<close> \<open>a \<in># fst arr\<close> \<open>h \<noteq> None\<close>
  shows \<open>unroot_hp_tree arr a \<le> SPEC (\<lambda>arr'. fst arr' = fst arr \<and> encoded_hp_prop_list2_conc arr'
    (\<V>, (if find_key a (the h) = None then [] else [the (find_key a (the h))]) @
    (if remove_key a (the h) = None then [] else [the (remove_key a (the h))])))\<close>
proof -
  obtain prevs nxts childs parents scores k where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, parents, scores), k)\<close> and
    dist: \<open>distinct_mset (mset_nodes (the h))\<close> and
    k: \<open>k = Some (node (the h))\<close>\<open>the k \<in># \<V>\<close> and
    \<V>: \<open>set_mset ((mset_nodes (the h))) \<subseteq> set_mset \<V>\<close>
    by (cases arr; cases \<open>the h\<close>) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
      encoded_hp_prop_list_conc_def encoded_hp_prop_def\<close>)
  have K1: \<open>fst (snd (maybe_hp_update_child' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_child' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_prev' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_prev' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_nxt' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_nxt' (node (the b)) x arr)))\<close>
    \<open>fst (snd (maybe_hp_update_parents' (map_option node b) x arr)) =
    (if b = None then fst (snd arr) else fst (snd (hp_update_parents' (node (the b)) x arr)))\<close>
    for x b arr
    apply (solves \<open>cases arr; auto simp: maybe_hp_update_child'_def maybe_hp_update_parents'_def
      maybe_hp_update_prev'_def maybe_hp_update_nxt'_def maybe_hp_update_prev'_def
      maybe_hp_update_nxt'_def\<close>)+
    done
  have source_node_alt: \<open>snd (snd arr) = source_node arr\<close>
    by (cases arr) auto
  have KK: \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> nxts a = map_option node (hp_next a (the h))\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> prevs a = map_option node (hp_prev a (the h))\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> parents a = map_option node (hp_parent a (the h))\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> childs a = map_option node (hp_child a (the h))\<close>
   using enc 
   unfolding arr encoded_hp_prop_list_conc_def
   by (auto simp: encoded_hp_prop_def)
  have KK': \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> nxts a \<noteq> None \<Longrightarrow> the (nxts a) \<in># \<V>\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> prevs a \<noteq> None \<Longrightarrow> the (prevs a) \<in># \<V>\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> parents a \<noteq> None \<Longrightarrow> the (parents a) \<in># \<V>\<close>
    \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> childs a \<noteq> None \<Longrightarrow> the (childs a) \<in># \<V>\<close>
   using enc \<V> KK hp_next_in_nodes2[of a \<open>the h\<close> \<open>the (hp_next a (the h))\<close>] dist
     hp_parent_None_notin[of a \<open>the h\<close>]
     hp_prev_in_nodes[of a \<open>the h\<close>]
     hp_parent_in_nodes[of a \<open>the h\<close>]
     hp_parent_hp_child[of \<open>the h\<close> a]
   unfolding arr encoded_hp_prop_list_conc_def
   apply (auto simp: encoded_hp_prop_def)
   by (metis hp_parent_None_notin mset_set_set_mset_msubset mset_subset_eqD option.simps(3))
  have KK2: \<open>fst (hp_update_parents' a None
     (hp_update_prev' a None
    (hp_update_nxt' a None
      (maybe_hp_update_parents' (nxts a) (parents a)
        (maybe_hp_update_prev' (nxts a) (Some (node z))
       (maybe_hp_update_nxt' (Some (node z)) (nxts a)
         (maybe_hp_update_child' (parents a) (nxts a)
    (\<V>, (prevs, nxts, childs, parents, scores), Some (node y))))))))) = \<V>\<close>
   by auto
  have HH: \<open>encoded_hp_prop_list \<V> {#the h#} [] (fst (snd (arr)))\<close> \<open>encoded_hp_prop_mset2_conc arr (\<V>, {#the h#})\<close>
    using assms unfolding encoded_hp_prop_list_def encoded_hp_prop_list_conc_def
      encoded_hp_prop_mset2_conc_def
    by auto
  have  KK3: \<open>a\<in>#mset_nodes (the h) \<Longrightarrow> remove_key a (the h) = None \<or> node (the (remove_key a (the h))) = node (the h)\<close>
    by (cases \<open>the h\<close>; auto simp: )
  let ?arr = \<open>hp_update_parents' a None
    (hp_update_prev' a None
    (hp_update_nxt' a None
    (maybe_hp_update_parents' (map_option node (hp_next a (the h)))
    (map_option node (hp_parent a (the h)))
    (maybe_hp_update_prev' (map_option node (hp_next a (the h))) (map_option node (hp_prev a (the h)))
    (maybe_hp_update_nxt' (map_option node (hp_prev a (the h)))
    (map_option node (hp_next a (the h)))
    (maybe_hp_update_child' (map_option node (hp_parent a (the h)))
    (map_option node (hp_next a (the h))) arr))))))\<close>
  have update_source_node_None_alt: \<open>update_source_node None x = (fst x, fst (snd x), None)\<close> for x
    by (cases x) auto
  show ?thesis
    using assms
    unfolding unroot_hp_tree_alt_def
    apply refine_vcg
    subgoal using k unfolding arr by auto
    subgoal using k unfolding arr by auto
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr \<open>(\<V>, h)\<close> a]
      unfolding source_node_alt
      by (auto simp add: find_key_None_remove_key_ident encoded_hp_prop_mset2_conc_def arr)
        (solves \<open>auto simp: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_conc_def\<close>)+
    subgoal using k unfolding arr by auto
    subgoal
      unfolding
        hp_update_fst_snd K1[symmetric] arr encoded_hp_prop_list_conc_def encoded_hp_prop_mset2_conc_def
      by (auto simp: remove_key_None_iff encoded_hp_prop_list2_conc_def)
    subgoal
      unfolding
        hp_update_fst_snd K1[symmetric] arr encoded_hp_prop_list_conc_def encoded_hp_prop_mset2_conc_def
      by clarsimp
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr \<open>(\<V>, h)\<close> a] KK' unfolding arr by auto
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr \<open>(\<V>, h)\<close> a] KK' unfolding arr by auto
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr \<open>(\<V>, h)\<close> a] KK' unfolding arr by auto
    subgoal using k unfolding arr by auto
    subgoal
      apply ((split if_splits)+; intro impI conjI)
      subgoal by (simp add: find_key_None_remove_key_ident)
      subgoal 
        using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr \<open>(\<V>, h)\<close> a] KK' unfolding arr 
        apply  (simp add: find_key_None_remove_key_ident arr)
        by (metis find_key_None_remove_key_ident in_remove_key_changed option.sel option.simps(3))
      subgoal
        by (auto simp: remove_key_None_iff encoded_hp_prop_list2_conc_def encoded_hp_prop_list_conc_def)
      subgoal
        unfolding append.append_Cons append.append_Nil
        apply (insert encoded_hp_prop_list_remove_find2[of \<open>arr\<close> \<V> \<open>the h\<close> a, OF HH(2)])
        unfolding K1[symmetric]
          maybe_hp_update_child'_def[symmetric] maybe_hp_update_parents'_def[symmetric]
          maybe_hp_update_prev'_def[symmetric] maybe_hp_update_nxt'_def[symmetric]
          hp_update_fst_snd
        unfolding maybe_hp_update_fst_snd[symmetric] maybe_hp_update_parents'_def[symmetric]
          maybe_hp_update_nxt'_def[symmetric] maybe_hp_update_prev'_def[symmetric] maybe_hp_update_child'_def[symmetric]
          hp_update_fst_snd maybe_hp_update_fst_snd2[symmetric]
          maybe_hp_update_fst_snd[symmetric]
        apply (subst arg_cong[of _ _ \<open>\<lambda>arr. encoded_hp_prop_list2_conc arr _\<close>])
          defer
        apply (rule encoded_hp_prop_mset2_conc_combine_list2_conc[of ?arr \<V> \<open>the (find_key a (the h))\<close> \<open>the (remove_key a (the h))\<close>])
        subgoal using HH(2) by (auto simp: add_mset_commute)
        subgoal using KK[symmetric] KK3
          encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of \<open>arr\<close> \<open>(\<V>, h)\<close> a] arr k
          by auto
        done
      done
    done
qed

definition rescale_and_reroot where
  \<open>rescale_and_reroot h w' arr = do {
    ASSERT (h \<in># fst arr);
    let nnext = hp_read_nxt' h arr;
    let parent = hp_read_parent' h arr;
    let prev = hp_read_prev' h arr;
    if source_node arr = None then RETURN (hp_update_score' h (Some w') arr)
    else if prev = None \<and> parent = None \<and> Some h \<noteq> source_node arr then RETURN (hp_update_score' h (Some w') arr)
    else if Some h = source_node arr then RETURN (hp_update_score' h (Some w') arr)
    else do {
       arr \<leftarrow> unroot_hp_tree arr h;
       ASSERT (h \<in># fst arr);
       let arr = (hp_update_score' h (Some w') arr);
       merge_pairs arr h
   }
}\<close>

lemma fst_update2[simp]:
  \<open>fst (hp_update_score' a b h) = fst h\<close>
  by (cases h; auto; fail)+

lemma encoded_hp_prop_list2_conc_update_score:
  \<open>encoded_hp_prop_list2_conc h (\<V>, [x,y]) \<Longrightarrow> node x = a \<Longrightarrow> encoded_hp_prop_list2_conc (hp_update_score' a (Some w') h) (\<V>, [Hp (node x) w' (hps x), y])\<close>
  unfolding encoded_hp_prop_list2_conc_alt_def case_prod_beta encoded_hp_prop_list_def
  apply (intro conjI  conjI allI impI ballI)
  subgoal by auto
  subgoal by (cases x) auto
  subgoal by (cases x) auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal
    apply (cases x; cases h)
    apply (clarsimp simp add: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def hp_update_score_def)
      by (smt (verit, ccfv_threshold) add_diff_cancel_left' add_diff_cancel_right' distinct_mset_in_diff hp.sel(1) hp_next_children.simps(2)
        hp_next_children_simps(1) hp_next_children_simps(2) hp_next_children_simps(3) hp_next_simps option.map(2) set_mset_union)
   subgoal
    apply (cases x; cases h)
    apply (clarsimp simp add: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def hp_update_score_def)
    by (metis (no_types, lifting) None_eq_map_option_iff Un_iff hp.sel(1) hp_prev_None_notin
      hp_prev_None_notin_children hp_prev_children.simps(2) hp_prev_children_simps
      hp_prev_simps node_in_mset_nodes option.map(2))
  subgoal
    apply (cases x; cases h)
    apply (clarsimp simp add: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def hp_update_score_def)
      by (metis (no_types, opaque_lifting) hp_child_None_notin hp_child_children_hp_child hp_child_children_simps(2)
        hp_child_children_simps(3) hp_child_hd hp_child_hp_children_simps2 set_mset_union union_iff)
   subgoal
    by (cases x; cases h)
     (auto simp add: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def hp_update_score_def
      hp_parent_children_cons hp_parent_simps_single_if)
    subgoal
    apply (cases x; cases h)
    apply (clarsimp simp add: encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def hp_update_score_def)
    by (metis hp_node_children_Cons_if hp_node_children_simps2)
  subgoal
    by (cases h; cases x)
     (auto simp: hp_update_score_def)
  subgoal
    by (cases h; cases x)
     (auto simp: hp_update_score_def)
  subgoal
    by (cases h; cases x)
     (auto simp: hp_update_score_def)
  done


lemma encoded_hp_prop_list_conc_update_score: \<open>encoded_hp_prop_list_conc arr (\<V>, Some (Hp a x2 x3)) \<Longrightarrow>
    encoded_hp_prop_list_conc (hp_update_score' a (Some w') arr) (\<V>, Some (Hp a w' x3))\<close>
  supply [simp] = hp_update_score_def
  unfolding encoded_hp_prop_list_conc_alt_def case_prod_beta encoded_hp_prop_list_def option.case
    snd_conv
  apply (intro conjI  conjI allI impI ballI)
  subgoal by auto
  subgoal by (cases arr) auto
  subgoal by (cases arr) auto
  subgoal by (cases arr) auto
  subgoal by (cases arr) auto
  subgoal apply (cases arr) apply auto
    by (metis hp_child_hp_children_simps2)
  subgoal by (cases arr) (auto simp add: hp_parent_simps_single_if)
  subgoal by (cases arr) auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (cases arr) auto
  subgoal by (cases arr) auto
  subgoal by (cases arr) auto
  done

lemma encoded_hp_prop_list_conc_update_outside:
  \<open>(snd h \<noteq> None \<Longrightarrow> a \<notin># mset_nodes (the (snd h))) \<Longrightarrow> encoded_hp_prop_list_conc arr h \<Longrightarrow>
  encoded_hp_prop_list_conc (hp_update_score' a w' arr) h\<close>
  by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_list_def
    hp_update_score_def
    split: option.splits)

definition ACIDS_decrease_key' where
  \<open>ACIDS_decrease_key' = (\<lambda>a w (\<V>, h). (\<V>, ACIDS.decrease_key a w (the h)))\<close>

lemma rescale_and_reroot:
  fixes h :: \<open>nat multiset \<times> (nat, nat)hp option\<close>
  assumes enc: \<open>encoded_hp_prop_list_conc arr h\<close> \<open>a \<in># fst arr\<close> (*\<open>snd h \<noteq> None\<close>*)
  shows \<open>rescale_and_reroot a w' arr \<le> \<Down> {(arr, h). encoded_hp_prop_list_conc arr h} (ACIDS.mop_hm_decrease_key a w' h)\<close>
proof -
  let ?h = \<open>snd h\<close>
  have 1: \<open>encoded_hp_prop_list_conc arr h \<Longrightarrow> encoded_hp_prop_list_conc arr (fst h, snd h)\<close>
    by (cases h) auto
  have src: \<open>source_node arr = map_option node ?h\<close>
    using enc by (auto simp: encoded_hp_prop_list_conc_def split: option.splits)
  show ?thesis
    using assms
    unfolding rescale_and_reroot_def ACIDS.decrease_key_def ACIDS_decrease_key'_def
      ACIDS.mop_hm_decrease_key_def
    apply (refine_vcg unroot_hp_tree vsids_merge_pairs)
    subgoal by (auto simp: encoded_hp_prop_list_conc_def split: option.splits)
    subgoal by (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def hp_update_score_def split: option.splits)
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
      apply (auto split: option.splits hp.splits intro!: encoded_hp_prop_list_conc_update_outside)
      apply (metis prod.collapse source_node.simps)+
      done
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>] src
        encoded_hp_prop_list_conc_update_score[of arr \<open>fst h\<close> a \<open>score (the ?h)\<close> \<open>hps (the ?h)\<close> w']
      by (auto split: option.splits hp.splits simp: find_key_None_remove_key_ident)
    apply (rule 1; assumption)
    subgoal by auto
    subgoal by auto
    apply (rule encoded_hp_prop_list2_conc_update_score[of _ \<open>fst h\<close> \<open>the (find_key a (the ?h))\<close> \<open>the (remove_key a (the ?h))\<close>])
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>]
      by (auto split: if_splits simp add: find_key_None_remove_key_ident
        encoded_hp_prop_list_conc_def)
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>]
        find_key_None_or_itself[of a \<open>the ?h\<close>] find_key_None_remove_key_ident[of a \<open>the ?h\<close>]
      by (cases \<open>find_key a (the ?h)\<close>)
       (auto simp del: find_key_None_or_itself)
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>]
      by (auto split: if_splits simp add: find_key_None_remove_key_ident
        encoded_hp_prop_list_conc_def)
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>]
        node_remove_key_itself_iff[of a \<open>the ?h\<close>]
      by (auto split: if_splits simp add: find_key_None_remove_key_ident
        encoded_hp_prop_list_conc_def)
    subgoal
      using encoded_hp_prop_list_in_node_iff_prev_parent_or_root[of arr h a]
        in_remove_key_changed[of a \<open>the ?h\<close>] remove_key_None_iff[of a \<open>the ?h\<close>] src
        find_key_None_or_itself[of a \<open>the ?h\<close>]
      by (cases \<open>the (find_key a (the ?h))\<close>)
        (clarsimp split: if_splits simp add: find_key_None_remove_key_ident
        simp del: ACIDS.merge_pairs.simps find_key_None_or_itself)
    done
qed

definition acids_encoded_hmrel where
  \<open>acids_encoded_hmrel = {(arr, h). encoded_hp_prop_list_conc arr h} O ACIDS.hmrel\<close>

lemma hp_insert_spec_mop_prio_insert:
  assumes \<open>(arr, h) \<in> acids_encoded_hmrel\<close>
  shows \<open>hp_insert i w arr \<le> \<Down>acids_encoded_hmrel (ACIDS.mop_prio_insert i w h)\<close>
proof -
  obtain j where
    i: \<open> encoded_hp_prop_list_conc arr j\<close>
    \<open>(j, h) \<in> ACIDS.hmrel\<close>
    using assms unfolding acids_encoded_hmrel_def by auto
  show ?thesis
    unfolding ACIDS.mop_prio_insert_def case_prod_beta acids_encoded_hmrel_def
    apply (refine_vcg hp_insert_spec[THEN order_trans] i)
    subgoal using i by (auto simp: encoded_hp_prop_list_conc_def ACIDS.hmrel_def)
    subgoal using i by (auto simp: encoded_hp_prop_list_conc_def ACIDS.hmrel_def)
     apply (rule order_trans, rule ref_two_step')
     apply (rule ACIDS.mop_prio_insert)
     apply (rule i)
     apply (auto simp: conc_fun_chain conc_fun_RES ACIDS.mop_prio_insert_def case_prod_beta RETURN_def)
     done
qed

lemma rescale_and_reroot_mop_prio_change_weight:
  assumes \<open>(arr, h) \<in> acids_encoded_hmrel\<close> and nempty: \<open>fst (snd h) \<noteq> {#}\<close>
  shows \<open>rescale_and_reroot a w arr \<le> \<Down>acids_encoded_hmrel (ACIDS.mop_prio_change_weight a w h)\<close>
proof -
  obtain j where
    i: \<open> encoded_hp_prop_list_conc arr j\<close>
    \<open>(j, h) \<in> ACIDS.hmrel\<close>
    using assms unfolding acids_encoded_hmrel_def by auto
  show ?thesis
    unfolding ACIDS.mop_prio_change_weight_def case_prod_beta
      ACIDS.mop_hm_decrease_key_def
    apply (refine_vcg rescale_and_reroot[THEN order_trans] i)
    subgoal using i by (auto simp: encoded_hp_prop_list_conc_def ACIDS.hmrel_def)
    apply (rule order_trans, rule ref_two_step')
    apply (rule ACIDS.decrease_key_mop_prio_change_weight i)+
    apply (auto simp: conc_fun_chain conc_fun_RES ACIDS.mop_prio_insert_def case_prod_beta RETURN_def
      ACIDS.mop_prio_change_weight_def acids_encoded_hmrel_def)
    done
qed

end
