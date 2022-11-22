theory IsaSAT_VSIDS
  imports Watched_Literals.WB_Sort IsaSAT_Setup Ordered_Pairing_Heap_List2
    Isabelle_LLVM.IICF
  (*  IsaSAT_Literals_LLVM
    IsaSAT_Literals_LLVM
    Isabelle_LLVM.IICF
    Isabelle_LLVM.LLVM_DS_Open_List
    Isabelle_LLVM.LLVM_DS_Array_List_Pure*)
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
(*
global_interpretation VSIDS: heap_impl where
  prio = id and
  prio_assn = \<open>snat_assn\<close> and
  elem_assn = atom_assn and
  prio_impl = Mreturn and
  le_prio_impl = ll_icmp_sle and
  lt_prio_impl = ll_icmp_slt and
  ltype = "TYPE(64)" and
  N = "LENGTH(64)"
    defines h_update_impl = update_impl
        and h_val_of_impl = val_of_impl
        and h_exch_impl = exch_impl
        and h_valid_impl = valid_impl
        and h_prio_of_impl = prio_of_impl
        and h_append_impl = append_impl
        and h_swim_impl = swim_impl
  and h_sink_impl = sink_impl
        and h_empty_impl = empty_impl
        and h_is_empty_impl = is_empty_impl
        and h_insert_impl = insert_impl
        and h_pop_min_impl = pop_min_impl
        and h_peek_min_impl = peek_min_impl
  apply unfold_locales
  sorry

interpretation hm_impl
  oops
find_theorems update_impl
find_theorems HM.h.update_op
  thm HM.h.update_op_def
thm h_val_of_impl_def
thm IICF_Impl_Heap.h_val_of_impl_def heap_impl.val_of_impl_def
thm val_of_def
definition vsids where
  \<open>vsids M h \<longleftrightarrow> HM.h.heap_invar h\<close>
find_theorems update_impl
  thm IICF_Impl_Heap.h_update_impl_def heap_impl.update_impl_def
  thm sink_impl.refine HM.h.valid_def
  term HM.h.sink_op
find_theorems append_impl
find_theorems HM.h.swim_invar
  thm HM.h.heap_invar_def
    *)
fun mset_nodes :: "('b, 'a) hp \<Rightarrow>'b multiset" where
"mset_nodes (Hp x _ hs) = {#x#} + sum_mset(mset(map mset_nodes hs))"

fun hp_next where
  \<open>hp_next a (Hp m s (x # y # children)) = (if a = node x then Some y else (case hp_next a x of Some a \<Rightarrow> Some a | None \<Rightarrow> hp_next a (Hp m s (y # children))))\<close> |
  \<open>hp_next a (Hp m s [b]) = hp_next a b\<close> |
  \<open>hp_next a (Hp m s []) = None\<close>

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


abbreviation hp_read_nxt :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_nxt i \<equiv> (\<lambda>(prevs, nxts, childs). nxts i)\<close>
abbreviation hp_read_prev :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_prev i \<equiv> (\<lambda>(prevs, nxts, childs). prevs i)\<close>
abbreviation hp_read_child :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_child i \<equiv> (\<lambda>(prevs, nxts, childs, scores). childs i)\<close>
abbreviation hp_read_score :: \<open>_ \<Rightarrow> ('a, 'b) hp_fun  \<Rightarrow> _\<close> where \<open>hp_read_score i \<equiv> (\<lambda>(prevs, nxts, childs, scores). scores i)\<close>

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

definition vsids_merge_pairs where
  \<open>vsids_merge_pairs = (\<lambda>(\<V>::'a set, arr :: ('a, 'b::order) hp_fun, h :: 'a option) j. do {
  REC\<^sub>T (\<lambda>f (arr, j). do {
    ASSERT (hp_read_nxt j arr \<noteq> None);
    ASSERT (j \<in> \<V>);
    let curr = the (hp_read_nxt j arr);
    let maybe_next = hp_read_nxt curr arr;
    if maybe_next = None then RETURN ((\<V>, arr, h), curr)
    else do {
      ASSERT (maybe_next \<noteq> None);
      let next = the (maybe_next);
      if hp_read_nxt next arr = None then hp_link curr next (\<V>, arr, h)
      else do {
       ASSERT (hp_read_nxt next arr \<noteq> None);
       ((\<V>, arr, h), m) \<leftarrow> f (arr, the (hp_read_nxt next arr));
       ((\<V>, arr, h), n) \<leftarrow> hp_link curr next (\<V>, arr, h);
       ((\<V>, arr, h), p) \<leftarrow> hp_link m n (\<V>, arr, h);
       RETURN ((\<V>, arr, h), p)
    }
   }
  }) (arr, j)
  })\<close>

thm VSIDS.pass\<^sub>1.simps VSIDS.pass\<^sub>2.simps
text \<open>In an imperative setting use the two pass approaches is better than the alternative.

The \<^term>\<open>e::nat\<close> of the loop is a dummy counter.\<close>
definition vsids_pass\<^sub>1 where
  \<open>vsids_pass\<^sub>1 = (\<lambda>(\<V>::'a set, arr :: ('a, 'b::order) hp_fun, h :: 'a option) (j::'a). do {

  ((\<V>, arr, h), j, _) \<leftarrow> WHILE\<^sub>T(\<lambda>((\<V>, arr, h), j, e). j \<noteq> None)
  (\<lambda>((\<V>, arr, h), j, e::nat). do {
    if j = None then RETURN ((\<V>, arr, h), None, e)
    else do {
    let j = the j;
    let nxt = hp_read_nxt j arr;
    if nxt = None then RETURN ((\<V>, arr, h), nxt, e+1)
    else do {
      ASSERT (nxt \<noteq> None);
      let nnxt = hp_read_nxt (the nxt) arr;
      ((\<V>, arr, h), n) \<leftarrow> hp_link j (the nxt) (\<V>, arr, h);
      RETURN ((\<V>, arr, h), nnxt, e+2)
   }}
  })
  ((\<V>, arr, h), Some j, 0::nat);
  RETURN (\<V>, arr, h)
  })\<close>

lemma sum_list_mset_nodes_pass\<^sub>1 [simp]: \<open>sum_list (map mset_nodes (VSIDS.pass\<^sub>1 (xs))) = sum_list (map mset_nodes xs)\<close>
  apply (induction xs rule: VSIDS.pass\<^sub>1.induct)
  apply auto
  apply (case_tac h1, case_tac h2)
  apply auto
  done

lemma drop_is_single_iff: \<open>drop e xs = [a] \<longleftrightarrow> last xs = a \<and> e = length xs - 1 \<and> xs \<noteq> []\<close>
  apply auto
  apply (metis append_take_drop_id last_snoc)
  by (metis diff_diff_cancel diff_is_0_eq' length_drop length_list_Suc_0 n_not_Suc_n nat_le_linear)


lemma distinct_mset_mono': \<open>distinct_mset D \<Longrightarrow> D' \<subseteq># D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

lemma pass\<^sub>1_append_even: \<open>even (length xs) \<Longrightarrow> VSIDS.pass\<^sub>1 (xs @ ys) = VSIDS.pass\<^sub>1 xs @ VSIDS.pass\<^sub>1 ys\<close>
  by (induction xs rule: VSIDS.pass\<^sub>1.induct) auto

lemma
  fixes arr :: \<open>'a::linorder set \<times> ('a, nat) hp_fun \<times> 'a option\<close>
  assumes \<open>encoded_hp_prop_list2_conc arr xs\<close> and \<open>xs \<noteq> []\<close> and \<open>j = node (hd xs)\<close>
  shows \<open>vsids_pass\<^sub>1 arr j \<le> SPEC(\<lambda>(arr). encoded_hp_prop_list2_conc arr (VSIDS.pass\<^sub>1 xs))\<close>
proof -
  obtain prevs nxts childs scores \<V> where
    arr: \<open>arr = (\<V>, (prevs, nxts, childs, scores), None)\<close> and
    dist: \<open>distinct_mset (\<Sum>\<^sub># (mset_nodes `# (mset (xs))))\<close> and
    \<V>: \<open>set_mset (sum_list (map mset_nodes xs)) \<subseteq> \<V>\<close>
    by (cases arr) (use assms in \<open>auto simp: ac_simps encoded_hp_prop_list2_conc_def encoded_hp_prop_list_def
        encoded_hp_prop_def\<close>)
  define I where \<open>I \<equiv> (\<lambda>(arr, nnxt::'a option, e).
    encoded_hp_prop_list2_conc arr (VSIDS.pass\<^sub>1(take e xs) @ drop e xs) \<and> nnxt = map_option node (option_hd (drop e xs)) \<and>
    e \<le> (length xs) \<and> (nnxt = None \<longleftrightarrow> e = length xs) \<and> (nnxt \<noteq> None \<longrightarrow> even e))\<close>
  have I0: \<open>I ((\<V>, (prevs, nxts, childs, scores), None), Some j, 0)\<close>
    using assms unfolding I_def by (auto simp: arr)
  have I_no_next: \<open>I ((\<V>, arr, ch'), None, Suc e)\<close>
    if \<open>I ((\<V>, arr, ch'), Some y, e)\<close> and
      \<open>hp_read_nxt y arr = None\<close>
    for s a b prevs x2 nxts children x1b x2b x1c x2c x1d x2d arr e y ch' \<V>
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
      s: \<open>case s of (x, xa) \<Rightarrow> (case x of (\<V>, arr, h) \<Rightarrow> \<lambda>(j, e). j \<noteq> None) xa\<close>
      \<open>s = (a, b)\<close>
      \<open>b = (x1b, x2b)\<close>
      ‹x2 = (x1a, x2a)\<close>
      \<open>a = (x1, x2)\<close>
      ‹x1b \<noteq> None\<close> and
      nxt: ‹hp_read_nxt (the x1b) x1a \<noteq> None\<close>
    for s a b x1 x2 x1a x2a x1b x2b
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
      apply (rule distinct_mset_mono)
        prefer 2
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

  show ?thesis
    unfolding vsids_pass\<^sub>1_def arr prod.simps
    apply (refine_vcg WHILET_rule[where I=I and R = \<open>measure (\<lambda>(arr, nnxt::'a option, e). length xs -e)\<close>]
      hp_link)
    subgoal by auto
    subgoal by (rule I0)
    subgoal by (auto simp: I_def)
    subgoal by (auto simp: I_def)
    subgoal for s a b prevs' x2 nxts' children' x1b x2b x1c x2c x1d
      by (auto simp: I_no_next)
    subgoal by (auto simp: I_def)
    apply (rule link_pre1; assumption)
    apply (rule link_pre2; assumption)
    subgoal premises p for s a b x1 x2 x1a x2a x1b x2b
      using link_pre3[OF p(1-8)] p(9-)
      by auto
    subgoal for s a b x1 x2 x1a x2a x1b x2b x aa ba x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g x1h x2h
      apply (auto simp: I_def)
      sorry
    subgoal
      by (auto simp: I_def)
    subgoal
      by (auto simp: I_def)
      oops
      
apply (rule WHILET_rule)
    subgoal
      unfolding case_prod_beta
      by (rule refine_mono) (auto intro!: refine_mono dest: le_funD)
supply [[unify_trace_failure]]
    apply (rule wf)
    apply (rule pre)
      subgoal
        using pre
        apply (rule pre)
      

oops
thm RECT_rule

  term VSIDS.insert
thm VSIDS.insert.simps[unfolded VSIDS.link.simps]
  VSIDS.link.simps[unfolded VSIDS.insert.simps]

text \<open>
The choice of the current rule sets took a very long time and I am still unsure that this is the
best set of rules. In essence, the rules are doing two things:
  \<^item> flattening the representation to make it fit into a list;
  \<^item> representing everything into an array.

Those could be split but I did not find a nice way to do that.


We had several attempts over time:
  \<^item> in the first we could not prove that lists are also well-formed, because we did no keep enough
  information about the order of the construction.
  \<^item> in the second version, we kept enough information but could not save trees in order to work 
  on other parts of the tree. We also could not construct only one list of children at a time.

TODO: unclear if reusing prev for parent and previous is the best idea.
\<close>
inductive encoded_pairheap :: \<open>'a pairing_heap list \<Rightarrow> (nat, 'a) hp multiset \<Rightarrow> (nat, 'a) hp list multiset \<Rightarrow> bool\<close> where
  empty: \<open>encoded_pairheap arr {#} {#}\<close> |
  leaf: \<open>encoded_pairheap (arr[n := PHeap x None None None]) (add_mset (Hp n x []) {#}) treeLists\<close>
  if  \<open>encoded_pairheap arr {#} treeLists\<close> \<open>n < length arr\<close> \<open>n \<notin># \<Sum>\<^sub># (mset_nodes `# \<Sum>\<^sub># (mset `# treeLists))\<close>|
  comb: \<open>encoded_pairheap (arr[m := hp_set_next p (arr!m), p := hp_set_prev m (arr!p)])
              trees  (add_mset ((Hp m w\<^sub>m child\<^sub>m # Hp p w\<^sub>p child\<^sub>p # child\<^sub>n)) treeLists)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp m w\<^sub>m child\<^sub>m) trees) (add_mset (Hp p w\<^sub>p child\<^sub>p # child\<^sub>n) treeLists)\<close>|

  comb_single: \<open>encoded_pairheap (arr) trees (add_mset (Hp m w\<^sub>m child\<^sub>m # []) treeLists)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp m w\<^sub>m child\<^sub>m) trees) treeLists\<close>|

  add_child: \<open>encoded_pairheap (arr[n := hp_set_child m (arr!n), m := hp_set_prev n (arr!m)]) (add_mset (Hp n w\<^sub>n ((Hp m w\<^sub>m child\<^sub>m # oth))) trees) treeLists\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n []) trees) (add_mset (Hp m w\<^sub>m child\<^sub>m # oth) treeLists)\<close>

lemma encoded_pairheap_distinct_nodes:
  \<open>encoded_pairheap arr trees treeLists \<Longrightarrow>
  distinct_mset (\<Sum>\<^sub># (mset_nodes `# trees + mset_nodes `# \<Sum>\<^sub># (mset `# treeLists)))\<close>
  by (induction rule: encoded_pairheap.induct)
   (auto simp: ac_simps)

lemma encoded_pairheap_change_irrelevant:
  \<open>encoded_pairheap arr trees treeLists \<Longrightarrow> n < length arr \<Longrightarrow>
  n \<notin># \<Sum>\<^sub># (mset_nodes `# trees + mset_nodes `# \<Sum>\<^sub># (mset `# treeLists)) \<Longrightarrow> encoded_pairheap (arr [n := a]) trees treeLists\<close>
  apply (induction rule: encoded_pairheap.induct)
  subgoal
    by (rule encoded_pairheap.empty)
  subgoal for arr treeLists na x
    using encoded_pairheap.leaf[of \<open>arr[n := a]\<close> treeLists na x]
    by (auto simp add: list_update_swap encoded_pairheap.intros(1))
  subgoal for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
    using encoded_pairheap.comb[of \<open>arr[n := a]\<close> m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists]
    by (auto simp: list_update_swap)
  subgoal for arr m w\<^sub>m child\<^sub>m trees
    using encoded_pairheap.comb_single[of \<open>arr[n := a]\<close> m w\<^sub>m child\<^sub>m trees]
    by (auto simp: list_update_swap split: if_splits)
  subgoal for arr na w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists
    using encoded_pairheap.add_child[of \<open>arr[n := a]\<close> na w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists]
    by (auto simp: list_update_swap split: if_splits)
  done

lemma encoded_pairheap_atmost_one:
  \<open>encoded_pairheap arr trees treeLists \<Longrightarrow> size trees \<le> 1›
  by (solves \<open>induction rule: encoded_pairheap.induct; auto\<close>)+


interpretation VSIDS: pairing_heap where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done

fun nodes where
  \<open>nodes (Hp m w children) = add_mset (Hp m w children) (\<Sum>\<^sub># (nodes `# mset children))\<close>

lemma  encoded_pairheap_le_lengthI: \<open>encoded_pairheap arr trees treeLists \<Longrightarrow> m \<in># \<Sum>\<^sub># (mset_nodes `# trees + mset_nodes `# \<Sum>\<^sub># (mset `# treeLists)) \<Longrightarrow> m < length arr\<close>
  by (induction arr trees treeLists arbitrary:  rule: encoded_pairheap.induct) auto

lemma mset_nodes_nodes: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# nodes x)) = set_mset (mset_nodes x)\<close>
  by (induction x)  (force simp: in_mset_sum_list_iff)

lemma mset_nodes_nodes_indirect: \<open>nodes x = A \<Longrightarrow> set_mset (mset_nodes x) = set_mset ( \<Sum>\<^sub>#(mset_nodes  `# A))\<close>
  unfolding mset_nodes_nodes[symmetric]
  by simp

lemma in_mset_nodes_iff: \<open>n \<in># mset_nodes x \<Longrightarrow> \<exists>m a. Hp n m a \<in># nodes x\<close>
  by (induction x)
   (fastforce simp: mset_nodes_nodes in_mset_sum_list_iff)

lemma ph_child_prev_next_simp[simp]:
  \<open>ph_child (hp_set_child c a) = Some c\<close>
  \<open>ph_prev (hp_set_child c a) = ph_prev a\<close>
  \<open>ph_next (hp_set_child c a) = ph_next a\<close>
  \<open>ph_score (hp_set_child c a) = ph_score a\<close>

  \<open>ph_child (hp_set_next c a) = ph_child a\<close>
  \<open>ph_prev (hp_set_next c a) = ph_prev a\<close>
  \<open>ph_next (hp_set_next c a) = Some c\<close>
  \<open>ph_score (hp_set_next c a) = ph_score a\<close>

  \<open>ph_child (hp_set_child' c' a) = c'\<close>
  \<open>ph_prev (hp_set_child' c' a) = ph_prev a\<close>
  \<open>ph_next (hp_set_child' c' a) = ph_next a\<close>
  \<open>ph_score (hp_set_child' c' a) = ph_score a\<close>

  \<open>ph_child (hp_set_next' c' a) = ph_child a\<close>
  \<open>ph_prev (hp_set_next' c' a) = ph_prev a\<close>
  \<open>ph_next (hp_set_next' c' a) = c'\<close>
  \<open>ph_score (hp_set_next' c' a) = ph_score a\<close>

  \<open>ph_child (hp_set_prev c a) = ph_child a\<close>
  \<open>ph_prev (hp_set_prev c a) = Some c\<close>
  \<open>ph_next (hp_set_prev c a) = ph_next a\<close>
  \<open>ph_score (hp_set_prev c a) = ph_score a\<close>

  \<open>ph_child (hp_set_prev' c' a) = ph_child a\<close>
  \<open>ph_prev (hp_set_prev' c' a) = c'\<close>
  \<open>ph_next (hp_set_prev' c' a) = ph_next a\<close>
  \<open>ph_score (hp_set_prev' c' a) = ph_score a\<close>
  by (cases a; auto; fail)+



lemma encoded_pairheap_no_next_at_toplevel:
  assumes \<open>encoded_pairheap arr trees treeLists\<close>
    \<open>Hp m w\<^sub>m child\<^sub>m \<in># trees\<close>
  shows \<open>ph_next (arr!m) = None\<close>\<open>ph_prev (arr!m) = None\<close>
    \<open>ph_child (arr!m) = (if child\<^sub>m = [] then None else Some (node (hd child\<^sub>m)))\<close>
proof -
  have trees: \<open>trees = {#Hp m w\<^sub>m child\<^sub>m#}\<close>
    by (metis One_nat_def assms(1) assms(2) encoded_pairheap_atmost_one in_multiset_nempty member_add_mset mset_size_le1_cases)
  show \<open>ph_next (arr!m) = None\<close>\<open>ph_prev (arr!m) = None\<close>
    \<open>ph_child (arr!m) = (if child\<^sub>m = [] then None else Some (node (hd child\<^sub>m)))\<close>
    using assms(1) encoded_pairheap_le_lengthI[OF assms(1), of m] unfolding trees
    apply (induction arr \<open>{#Hp m w\<^sub>m child\<^sub>m#}\<close> treeLists arbitrary: m w\<^sub>m child\<^sub>m rule: encoded_pairheap.induct)
    subgoal
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m trees treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m treeLists
      by (auto dest: encoded_pairheap_atmost_one)

    subgoal for arr m w\<^sub>m child\<^sub>m treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists
      by (auto dest: encoded_pairheap_atmost_one)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists ma w\<^sub>m' child\<^sub>m'
      by (auto dest: encoded_pairheap_atmost_one encoded_pairheap_distinct_nodes)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists ma w\<^sub>m' child\<^sub>m'
      by (auto dest: encoded_pairheap_atmost_one encoded_pairheap_distinct_nodes)
    done
qed

text \<open>The simplifier is too stupid to use the previous version...\<close>
lemma encoded_pairheap_no_next_at_toplevel2:
  assumes \<open>encoded_pairheap arr (add_mset (Hp m w\<^sub>m child\<^sub>m) trees) treeLists\<close>
  shows \<open>ph_next (arr!m) = None\<close>\<open>ph_prev (arr!m) = None\<close>
    \<open>ph_child (arr!m) = (if child\<^sub>m = [] then None else Some (node (hd child\<^sub>m)))\<close>
  using encoded_pairheap_no_next_at_toplevel[of arr \<open>add_mset (Hp m w\<^sub>m child\<^sub>m) trees\<close> treeLists m w\<^sub>m child\<^sub>m] assms
  by auto

lemma encoded_pairheap_no_next_at_head_list:
  assumes \<open>encoded_pairheap arr trees treeLists\<close>
    \<open>Hp m w\<^sub>m child\<^sub>m # stuff \<in># treeLists\<close>
  shows \<open>ph_next (arr!m) = (if stuff = [] then None else Some (node (hd stuff)))\<close>
    \<open>ph_prev (arr!m) = None\<close>
    \<open>ph_child (arr!m) = (if child\<^sub>m = [] then None else Some (node (hd child\<^sub>m)))\<close>
proof -
  have \<open>m < length arr\<close>
    using encoded_pairheap_le_lengthI[OF assms(1), of m] assms by (auto dest!: multi_member_split)
  show \<open>ph_next (arr!m) = (if stuff = [] then None else Some (node (hd stuff)))\<close>
    \<open>ph_prev (arr!m) = None\<close>
    \<open>ph_child (arr!m) = (if child\<^sub>m = [] then None else Some (node (hd child\<^sub>m)))\<close>
    using assms
      encoded_pairheap_atmost_one[OF assms(1)] \<open>m < length arr\<close>
    apply (induction arr trees \<open>treeLists\<close> rule: encoded_pairheap.induct)
    subgoal
      by auto
    subgoal
      by auto
    subgoal for arr
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr trees na x
      by auto
    subgoal for arr ma w\<^sub>m' child\<^sub>m' trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (frule encoded_pairheap_distinct_nodes)
        (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one
        split: if_splits)
    subgoal for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (frule encoded_pairheap_distinct_nodes)
        (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal  for arr m w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists
      by (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m trees treeLists
      by (auto intro: encoded_pairheap_no_next_at_toplevel dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m trees treeLists
      by (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal for arr m w\<^sub>m child\<^sub>m treeLists
      by (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth treeLists
      by (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth
      by (frule encoded_pairheap_distinct_nodes)
        (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    subgoal for arr n w\<^sub>n trees m w\<^sub>m child\<^sub>m oth
      by (frule encoded_pairheap_distinct_nodes)
        (auto simp: encoded_pairheap_no_next_at_toplevel2 dest: encoded_pairheap_atmost_one)
    done
qed

lemma ph_next_update_self:
  \<open>ph_next a = n \<Longrightarrow> hp_set_next' n a = a\<close>
  by (cases a; auto)

(*
lemma encoded_pairheap_comb_general:
   \<open>encoded_pairheap (arr[n := hp_set_child m (arr!n), m := hp_set_next' (if child\<^sub>n = [] then None else Some (node (hd child\<^sub>n))) (arr!m)])
              (add_mset (Hp n w\<^sub>n (Hp m w\<^sub>m child\<^sub>m # child\<^sub>n)) trees)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n (child\<^sub>n)) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>
  for child\<^sub>n :: \<open>(nat, 'a) hp list\<close>
  using encoded_pairheap.comb[of arr n w\<^sub>n \<open>(node (hd child\<^sub>n))\<close> \<open>score (hd child\<^sub>n)\<close> \<open>hps (hd child\<^sub>n)\<close> \<open>tl child\<^sub>n\<close>
    m w\<^sub>m child\<^sub>m trees] encoded_pairheap_distinct_nodes[OF that(1)] that
    encoded_pairheap.comb_single[of arr n w\<^sub>n m w\<^sub>m child\<^sub>m trees]
    encoded_pairheap_no_next_at_toplevel[OF that, of n w\<^sub>n child\<^sub>n]
    encoded_pairheap_no_next_at_toplevel[OF that, of m w\<^sub>m child\<^sub>m]
    apply (cases child\<^sub>n)
    apply (auto simp: ph_next_update_self list_update_swap)
    by (metis hp_set_next'.simps hp_set_next.elims)
*)
lemma in_sum_mset_nodes_iff: \<open>(\<exists>m a. Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees + nodes `# \<Sum>\<^sub># (mset `# treeLists))) \<longleftrightarrow> n \<in># \<Sum>\<^sub># (mset_nodes `# trees + mset_nodes `# \<Sum>\<^sub># (mset `# treeLists))\<close>
  apply (rule iffI)
  subgoal
    apply (induction trees)
    apply (auto simp: mset_nodes_nodes)
    using mset_nodes_nodes apply fastforce+
    done
  subgoal
    by (induction trees)
     (fastforce simp: mset_nodes_nodes dest!: in_mset_nodes_iff)+
  done


lemma encoded_pairheap_correct_annot:
  assumes 1: \<open>encoded_pairheap arr trees treeLists\<close> and
    \<open>Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees + nodes `# \<Sum>\<^sub># (mset `# treeLists))\<close>
  shows \<open>ph_score (arr!n) = m\<close>
    \<open>ph_child (arr!n) = (if a = [] then None else Some (node (hd a)))\<close>
proof -
  have 2: \<open>n \<in># \<Sum>\<^sub># (mset_nodes `# trees + mset_nodes `# \<Sum>\<^sub># (mset `# treeLists))\<close>
    by (rule in_sum_mset_nodes_iff[THEN iffD1]) (use assms(2) in fast)
  show \<open>ph_score (arr!n) = m\<close>
    using 1 assms(2) encoded_pairheap_le_lengthI[OF 1 2]
    apply (induction arr trees treeLists arbitrary:  a rule: encoded_pairheap.induct)
    subgoal by auto
    subgoal for arr trees m' w
      apply auto
      by (metis (full_types) mset_nodes.simps mset_nodes_nodes multi_member_split multi_member_this sum_mset.insert union_iff)
    subgoal for arr ma w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists a
      by auto
    subgoal for arr ma w\<^sub>m child\<^sub>m treeLists a
      apply auto
      done
    subgoal for arr na w\<^sub>n trees ma w\<^sub>m child\<^sub>m oth treeLists a
      by auto
    done
  show \<open>ph_child (arr!n) = (if a = [] then None else Some (node (hd a)))\<close>
    using 1 assms(2) encoded_pairheap_le_lengthI[OF 1 2]
    apply (induction arr trees treeLists arbitrary:  a rule: encoded_pairheap.induct)
    subgoal by auto
    subgoal for arr trees m' w
      by auto (use mset_nodes_nodes in force)+
    subgoal for arr ma w\<^sub>m child\<^sub>m trees p w\<^sub>p child\<^sub>p child\<^sub>n treeLists a
      apply auto apply metis+ done
    subgoal for arr ma w\<^sub>m child\<^sub>m treeLists a
      by auto
    subgoal for arr na w\<^sub>n trees ma w\<^sub>m child\<^sub>m oth treeLists a
      apply (frule encoded_pairheap_distinct_nodes)
      apply auto
      apply force
      apply force
      apply (smt (verit, ccfv_threshold) add_0 member_add_mset mset_add mset_map mset_nodes.simps
        mset_nodes_nodes nodes.simps sum_image_mset_sum_map sum_mset.insert union_mset_add_mset_left)
      apply (metis (no_types, opaque_lifting) add.right_neutral image_mset_empty
        in_sum_mset_nodes_iff list.simps(8) mset_map sum_list_simps(1) sum_mset_sum_list)
      apply (metis union_assoc union_lcomm)
      apply (metis union_assoc union_lcomm)
      apply (metis (no_types, opaque_lifting) add.right_neutral image_mset_empty
        in_sum_mset_nodes_iff list.simps(8) mset_map sum_list_simps(1) sum_mset_sum_list)
      apply (metis (no_types, opaque_lifting) add.right_neutral image_mset_empty
        in_sum_mset_nodes_iff list.simps(8) mset_map sum_list_simps(1) sum_mset_sum_list)
      apply (metis union_assoc union_lcomm)
      apply (metis union_assoc union_lcomm)
      apply (smt (verit, ccfv_threshold) add_0 member_add_mset mset_add mset_map mset_nodes.simps
        mset_nodes_nodes nodes.simps sum_image_mset_sum_map sum_mset.insert union_mset_add_mset_left)
      apply (smt (verit, ccfv_threshold) add_0 member_add_mset mset_add mset_map mset_nodes.simps
        mset_nodes_nodes nodes.simps sum_image_mset_sum_map sum_mset.insert union_mset_add_mset_left)
      apply (metis union_assoc union_lcomm)
      apply (metis union_assoc union_lcomm)
      apply (smt (verit, ccfv_threshold) add_0 member_add_mset mset_add mset_map mset_nodes.simps
        mset_nodes_nodes nodes.simps sum_image_mset_sum_map sum_mset.insert union_mset_add_mset_left)
      apply (smt (verit, ccfv_threshold) add_0 member_add_mset mset_add mset_map mset_nodes.simps
        mset_nodes_nodes nodes.simps sum_image_mset_sum_map sum_mset.insert union_mset_add_mset_left)
      apply (metis union_assoc union_lcomm)
      by (metis (no_types, lifting) union_assoc union_lcomm)
    done
qed
hide_const (open) NEMonad.ASSERT NEMonad.RETURN NEMonad.SPEC

definition vsids_push_to_child where
  \<open>vsids_push_to_child arr m n = do {
    let c = ph_child (arr!m);
    if ph_child (arr!m) = None then RETURN (arr[m := hp_set_child n (arr ! m), n := hp_set_prev m (arr!n)])
    else do {
      ASSERT (c \<noteq> None);
      RETURN (arr[m := hp_set_child n (arr ! m), n := hp_set_next' c (arr!n), the c := hp_set_prev n (arr!the c)])}
  }\<close>
definition vsids_link where
  \<open>vsids_link arr m n = do {
     ASSERT (m < length arr);
     ASSERT (n < length arr);
     if ph_score (arr ! n) \<le> ph_score (arr ! m)
     then vsids_push_to_child arr m n
     else do{
        vsids_push_to_child arr n m
    }
}\<close>

inductive_cases  encoded_ph_add_msetE: \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) trees) treeLists\<close>
inductive_cases  encoded_ph_add_msetE2: \<open>encoded_pairheap arr trees (add_mset (Hp n w\<^sub>n child\<^sub>n#eth) treeLists)\<close>

lemma hp_set_prev_next_children_commute[simp]:
  \<open>hp_set_prev' a (hp_set_child b x) = hp_set_child b (hp_set_prev' a x)\<close>
  \<open>hp_set_next' a (hp_set_child b x) = hp_set_child b (hp_set_next' a x)\<close>
  \<open>hp_set_child' a (hp_set_child b x) = hp_set_child' a x\<close> 
  \<open>hp_set_prev' a (hp_set_prev b x) = hp_set_prev' a x\<close> and
  hp_prev_next_children_update_self:
  \<open>ph_child x =a \<Longrightarrow> hp_set_child' a x = x\<close>
  \<open>ph_prev x =a \<Longrightarrow> hp_set_prev' a x = x\<close>
  \<open>ph_next x =a \<Longrightarrow> hp_set_next' a x = x\<close>
  by (solves \<open>cases x;auto\<close>)+

lemma encoded_pairheap_move_children_to_treeLists:
  assumes \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) trees) treeLists\<close> \<open>child\<^sub>n \<noteq> []\<close>
  shows \<open>encoded_pairheap (arr[node (hd child\<^sub>n) := hp_set_prev' None (arr!node (hd child\<^sub>n)),
        n := hp_set_child' None (hp_set_prev' None (arr!n))])
    (add_mset (Hp n w\<^sub>n []) trees) (add_mset child\<^sub>n treeLists)\<close>
  using assms  encoded_pairheap_atmost_one[OF assms(1)] encoded_pairheap_le_lengthI[OF assms(1), of n]
    encoded_pairheap_le_lengthI[OF assms(1), of \<open>node (hd child\<^sub>n)\<close>]
    encoded_pairheap_no_next_at_toplevel[OF assms(1), of \<open>node (hd child\<^sub>n)\<close> \<open>score (hd child\<^sub>n)\<close> \<open>hps (hd child\<^sub>n)\<close>]
    encoded_pairheap_no_next_at_toplevel[OF assms(1), of \<open>n\<close> \<open>w\<^sub>n\<close> \<open>child\<^sub>n\<close>]
    encoded_pairheap_distinct_nodes[OF assms(1)] encoded_pairheap_no_next_at_toplevel[of _ \<open>{#Hp n w\<^sub>n []#}\<close> \<open>add_mset child\<^sub>n treeLists\<close> n w\<^sub>n child\<^sub>n]
  apply -
  apply (rule encoded_ph_add_msetE, assumption)
  apply (auto dest: encoded_pairheap_atmost_one
    simp: list_update_swap hp_prev_next_children_update_self
    encoded_pairheap_no_next_at_toplevel split: if_splits
    dest: encoded_pairheap_no_next_at_head_list(2)[of _ \<open>{#Hp n w\<^sub>n []#}\<close> \<open>add_mset (_ # _) treeLists\<close> \<open>node (hd child\<^sub>n)\<close> \<open>score (hd child\<^sub>n)\<close> \<open>hps (hd child\<^sub>n)\<close>])
  apply (frule encoded_pairheap_no_next_at_head_list(2)[of _ \<open>{#Hp n w\<^sub>n []#}\<close> \<open>add_mset (_ # _) treeLists\<close> \<open>node (hd child\<^sub>n)\<close> \<open>score (hd child\<^sub>n)\<close> \<open>hps (hd child\<^sub>n)\<close>])
  apply (auto split: if_splits simp: hp_prev_next_children_update_self)
  done

lemma encoded_pairheap_move_children_to_treeLists:
  assumes \<open>encoded_pairheap arr {#} treeLists\<close> and
    \<open>(Hp n w\<^sub>n child\<^sub>n # other)  \<in># treeLists\<close>
  shows \<open>encoded_pairheap (arr[n := hp_set_next' None (arr ! n)]) {#Hp n w\<^sub>n child\<^sub>n#} (add_mset other treeLists)\<close>
  using assms  encoded_pairheap_atmost_one[OF assms(1)] encoded_pairheap_le_lengthI[OF assms(1), of n]
  apply -
  apply (induction arr \<open>{#} :: (nat, 'a) hp multiset\<close> \<open>treeLists\<close> rule: encoded_pairheap.induct)
  subgoal
    by (auto dest: encoded_pairheap_atmost_one
      simp: list_update_swap hp_prev_next_children_update_self
      encoded_pairheap_no_next_at_toplevel split: if_splits)
  subgoal
    by (auto dest: encoded_pairheap_atmost_one
      simp: list_update_swap hp_prev_next_children_update_self
      encoded_pairheap_no_next_at_toplevel split: if_splits)
  subgoal
    apply (auto dest: encoded_pairheap_atmost_one
      simp: list_update_swap hp_prev_next_children_update_self add_mset_eq_add_mset
      encoded_pairheap_no_next_at_toplevel split: if_splits)
    apply (metis encoded_pairheap.intros(3) encoded_pairheap_no_next_at_head_list(2) length_list_update nth_list_update_eq option.simps(3) ph_child_prev_next_simp(18) union_single_eq_member)
      oops


lemma vsids_link:
  assumes vsids: \<open>encoded_pairheap arr trees (add_mset (Hp n w\<^sub>n child\<^sub>n # Hp m w\<^sub>m child\<^sub>m # []) treeLists)\<close>
  shows \<open>vsids_link arr m n \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' (add_mset (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m)) trees) treeLists)\<close>
proof -
  show ?thesis
    using assms
    unfolding vsids_link_def vsids_push_to_child_def
    apply (refine_vcg if_refine)
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of m] by auto
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of n] by auto
    subgoal
      using encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
      by (auto intro!: encoded_pairheap.comb_single encoded_pairheap.add_child split: if_splits)
    subgoal
      using encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap.comb_single[of arr m w\<^sub>m child\<^sub>m \<open>add_mset (Hp n w\<^sub>n child\<^sub>n) trees\<close> treeLists,
        unfolded add_mset_commute[of _ \<open>Hp n _ _\<close>]]
        encoded_pairheap.add_child[of arr n w\<^sub>n ]
        
      apply (auto intro!: encoded_pairheap.comb encoded_pairheap.add_child split: if_splits)

    subgoal
      using encoded_pairheap_comb_general[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    done
qed

definition vsids_insert where
  \<open>vsids_insert m n arr = do {
    ASSERT (n < length arr);
    vsids_link (arr[n:= PHeap (ph_score (arr!n)) None None]) m n
  }\<close>

lemma vsids_insert:
  assumes \<open>encoded_pairheap arr {#Hp m w\<^sub>m children#}\<close> \<open>n \<notin># mset_nodes (Hp m w\<^sub>m children)\<close> \<open>n < length arr\<close>
  shows \<open>vsids_insert m n arr \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' {#the (VSIDS.insert n (ph_score (arr!n)) (Some (Hp m w\<^sub>m children)))#}) \<close>
proof -
  have 1: \<open>encoded_pairheap (arr[n:= PHeap (ph_score (arr!n)) None None]) {#Hp n (ph_score (arr!n)) [], Hp m w\<^sub>m children#}\<close>
    using assms encoded_pairheap.leaf[OF assms(1), of n True \<open>ph_score (arr!n)\<close>]
    by (auto intro!: )
  show ?thesis
    unfolding vsids_insert_def
    apply (refine_vcg vsids_link[OF 1, THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    done
qed


definition vsids_link2 where
  \<open>vsids_link2 arr m n = do {
     ASSERT (m < length arr);
     ASSERT (n < length arr);
     if ph_score (arr ! n) \<le> ph_score (arr ! m)
     then do{
        let c = ph_child (arr!m);
        RETURN (arr[m := hp_set_child n (arr ! m), n := hp_set_next' c (arr!n)], m)
     }
     else do{
        let c = ph_child (arr!n);
        RETURN (arr [n :=  hp_set_child m (arr ! n), m := hp_set_next' c (arr!m)], n)
    }
}\<close>

lemma vsids_link2:
  assumes vsids: \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>
  shows \<open>vsids_link2 arr m n \<le> SPEC (\<lambda>(arr', k). k = node (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m))  \<and>
    encoded_pairheap arr' (add_mset (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m)) trees))\<close>
proof -
  show ?thesis
    unfolding vsids_link2_def
    unfolding vsids_link_def
    apply (refine_vcg if_refine)
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of m] by auto
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of n] by auto
    subgoal
      using encoded_pairheap_comb_general[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap_comb_general[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap_comb_general[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap_comb_general[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    done
qed

inductive_cases encoded_pairheapE: \<open>encoded_pairheap arr trees\<close>
(*
lemma encoded_pairheap_array_cong:
  assumes \<open>encoded_pairheap arr trees\<close>
    \<open>length arr = length arr'\<close>
    \<open>\<forall>m\<in>#\<Sum>\<^sub># (mset_nodes`#trees). arr!m = arr'!m\<close>
    \<open>\<forall>m< length arr . m\<notin>#\<Sum>\<^sub># (mset_nodes`#trees) \<longrightarrow> \<not>ph_contained (arr'!m)\<close>
  shows \<open>encoded_pairheap arr' trees\<close>
  using assms 
proof (induction arbitrary: arr' rule: encoded_pairheap.induct)
  case (empty arr)
  then show ?case apply -
    apply (rule  encoded_pairheap.empty)
    by (auto intro!: simp: )
next
  case (leaf arr trees n intree x arr')
  let ?arr' = \<open>arr' [n := PHeap (ph_score (arr'!n)) False (ph_children (arr'!n))]\<close>
  have \<open>\<forall>y\<in>#trees. \<forall>m\<in>#mset_nodes y. arr ! m = ?arr' ! m\<close> and
    \<open>\<forall>m<length arr. m \<notin># \<Sum>\<^sub># (mset_nodes `# trees) \<longrightarrow> \<not> ph_contained (?arr' ! m)\<close>
    using leaf apply (auto; metis; fail)
    by (use leaf in \<open>auto split: if_splits\<close>)
  then show ?case
    using encoded_pairheap.leaf[of ?arr' trees n intree x] leaf
    by (auto split: if_splits)
next
  case (comb arr n w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees)
  let ?arr' = \<open>arr'[n := PHeap (ph_score (arr ! n)) (ph_contained (arr ! n)) (ph_children (arr ! n))]\<close>
  have 1: \<open>\<forall>m\<in>#\<Sum>\<^sub># (mset_nodes `# add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees)).
    arr ! m = ?arr' ! m\<close>
    using comb(1,3-) encoded_pairheap_distinct_nodes[OF comb(1)]
      encoded_pairheap_le_lengthI[OF comb(1), of m]
      encoded_pairheap_le_lengthI[OF comb(1), of n]
    apply auto
    apply (meson Un_iff)
    apply (meson Un_iff)
    by (meson Un_iff UnionI image_eqI)
  have 2: \<open>\<forall>ma<length arr.
    ma \<notin># \<Sum>\<^sub># (mset_nodes `# add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees)) \<longrightarrow>
    \<not> ph_contained (?arr' ! ma)\<close>
    using comb(1,3-) encoded_pairheap_distinct_nodes[OF comb(1)]
      encoded_pairheap_le_lengthI[OF comb(1), of m]
      encoded_pairheap_le_lengthI[OF comb(1), of n]
    by auto
  have [simp]: \<open>(arr'
   [n := PHeap (ph_score (arr'[n := arr ! n] ! n)) (ph_contained (arr'[n := arr ! n] ! n))
       (ph_children (arr'[n := arr ! n] ! n) @ [m])]) = arr'\<close>
    using comb(1,3-) encoded_pairheap_distinct_nodes[OF comb(1)]
      encoded_pairheap_le_lengthI[OF comb(1), of m]
      encoded_pairheap_le_lengthI[OF comb(1), of n]
    by auto

  show ?case
    using comb.IH[of ?arr', OF _ 1 2] comb(3-5)
    using encoded_pairheap.comb[of ?arr' n w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees]
    by (auto split: if_splits)
qed
*)

definition vsids_merge_pairs where
  \<open>vsids_merge_pairs arr j = do {
  REC\<^sub>T (\<lambda>f (arr, j). do {
    ASSERT (ph_next (arr !j) \<noteq> None);
    let curr = the (ph_next (arr !j));
    let maybe_next = ph_next (arr ! curr);
    if maybe_next = None then RETURN (arr, curr)
    else do {
      ASSERT (maybe_next \<noteq> None);
      let next = the (maybe_next);
      if ph_next (arr ! next) = None then vsids_link2 arr curr next
      else do {
       ASSERT (ph_next (arr!next) \<noteq> None);
       (arr, m) \<leftarrow> f (arr, the (ph_next (arr!next)));
       (arr, n) \<leftarrow> vsids_link2 arr curr next;
      (arr, p) \<leftarrow> vsids_link2 arr m n;
       RETURN (arr, p)
    }
   }
  }) (arr, j)
  }\<close>

lemma merge_pairs_empty_iff[simp, iff]: \<open>VSIDS.merge_pairs xs = None \<longleftrightarrow> xs = []\<close>
  by (cases xs rule: VSIDS.merge_pairs.cases) auto

(*TODO: we have to link the order of the nodes and hp\<^sub>s *)
lemma
  assumes \<open>encoded_pairheap arr (mset hp\<^sub>s + trees)\<close>
    \<open>j < length xs\<close>
  shows \<open>vsids_merge_pairs arr j \<le> \<Down> Id (SPEC (\<lambda>(arr', n). n = node (the (VSIDS.merge_pairs (rev hp\<^sub>s))) \<and>
    encoded_pairheap arr' (add_mset (the (VSIDS.merge_pairs (rev hp\<^sub>s))) trees)))\<close>
proof -
  have take2: \<open>i \<le> length xs \<Longrightarrow> i > 0 \<Longrightarrow> take i xs = xs ! 0 # take (i-1) (tl xs)\<close> for i xs
    apply (cases xs; cases i)
    apply (auto)
    done
  define pre  :: \<open>nat pairing_heap list \<times> nat \<Rightarrow> bool\<close> where
    \<open>pre = (\<lambda>(arr, j\<^sub>0). j\<^sub>0 \<le> j \<and> encoded_pairheap arr (mset hp\<^sub>s + trees))\<close>
  define spec :: \<open>nat pairing_heap list \<times> nat \<Rightarrow> nat pairing_heap list \<times> nat \<Rightarrow> _\<close> where
    \<open>spec = (\<lambda>(old_arr, j\<^sub>0) (arr, n). (case (VSIDS.merge_pairs (rev (take (Suc j\<^sub>0) hp\<^sub>s))) of Some a \<Rightarrow> n = node a |_ \<Rightarrow>True) \<and>
    encoded_pairheap arr ((case (VSIDS.merge_pairs (rev (take (Suc j\<^sub>0) hp\<^sub>s))) of Some a \<Rightarrow> {#a#} | _ \<Rightarrow> {#}) + mset (drop (Suc j\<^sub>0) hp\<^sub>s) + trees))\<close> for x
(*  have [simp]: \<open>j > 0 \<Longrightarrow> (Hp (node (hp\<^sub>s ! 0)) (score (hp\<^sub>s ! 0)) (hps (hp\<^sub>s ! 0))) = hd hp\<^sub>s\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases j; auto)
  have [simp]: \<open>hd hp\<^sub>s = hp\<^sub>s ! 0\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases xs; cases \<open>tl xs\<close>; cases j; cases \<open>j-1\<close>; auto)
  have [simp]: \<open>j \<ge> Suc 0 \<Longrightarrow> (add_mset (hp\<^sub>s ! 0) (add_mset (hp\<^sub>s ! Suc 0) (mset (drop (Suc (Suc 0)) hp\<^sub>s) + trees))) = mset hp\<^sub>s + trees\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>j \<ge> Suc 0 \<Longrightarrow> VSIDS.merge_pairs (take (Suc 0) hp\<^sub>s) = Some (hd hp\<^sub>s)\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>j > 0 \<Longrightarrow> add_mset (hd hp\<^sub>s) (mset (drop (Suc 0) hp\<^sub>s)) = mset hp\<^sub>s\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>VSIDS.merge_pairs (rev (take (Suc 0) hp\<^sub>s)) = Some (hd hp\<^sub>s)\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>node (hp\<^sub>s ! 0) = xs ! 0\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>(add_mset (hp\<^sub>s!0) (mset (drop (Suc 0) hp\<^sub>s) + trees)) = (mset hp\<^sub>s + trees)\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have [simp]: \<open>j > 0 \<Longrightarrow> VSIDS.merge_pairs (rev (take (Suc (Suc 0)) hp\<^sub>s)) = Some (VSIDS.link (hp\<^sub>s ! 1) (hd hp\<^sub>s))\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases \<open>tl hp\<^sub>s\<close>; cases xs; cases \<open>tl xs\<close>; cases j; auto)
  have Hp_hps [simp]: \<open>j \<ge> y \<Longrightarrow> (Hp (xs ! y) (score (hp\<^sub>s ! y)) (hps (hp\<^sub>s ! y))) = hp\<^sub>s!y\<close> for y
    using assms(3)  arg_cong[OF assms(2), of \<open>\<lambda>xs. xs ! y\<close>] arg_cong[OF assms(2), of length]
    by (cases \<open>hp\<^sub>s ! y\<close>) (auto simp: nth_map)
  have VSIDS_merge_pairs_simps2: \<open>j\<^sub>0 > 1 \<Longrightarrow> j\<^sub>0 < length hp\<^sub>s \<Longrightarrow> VSIDS.merge_pairs (rev (take (Suc j\<^sub>0) hp\<^sub>s)) =
    Some (VSIDS.link (VSIDS.link (hp\<^sub>s ! j\<^sub>0) (hp\<^sub>s ! (j\<^sub>0 - 1)))
    (the (VSIDS.merge_pairs (rev (take (j\<^sub>0 - Suc 0) (hp\<^sub>s))))))\<close> for j\<^sub>0
    by (cases j\<^sub>0)
     (auto simp: take_Suc_conv_app_nth Let_def split: option.splits)
*)


  have pre0: \<open>pre (arr, j)\<close>
    using assms unfolding pre_def by (auto split: option.splits)
  show ?thesis
    using assms
    unfolding vsids_merge_pairs_def Let_def
    apply refine_vcg
    apply (rule order_trans)
    apply (rule RECT_rule[of _ \<open>measure (\<lambda>(arr, j). j)\<close> pre _ \<open> \<lambda>x. SPEC (spec x)\<close>])
    subgoal
      unfolding case_prod_beta
      by (rule refine_mono) (auto intro!: refine_mono dest: le_funD)
    subgoal
      by auto
    subgoal
      by (rule pre0)
    subgoal for f x
      unfolding case_prod_beta
      apply (refine_vcg)
      subgoal sorry
      subgoal premises p
        using p(1-4,6-)
        apply (auto simp: pre_def spec_def split: option.splits)
oops
      subgoal premises p
        using p by (auto simp: pre_def)
      subgoal premises p
        using p by (auto simp: pre_def)
      subgoal premises p
        apply (rule vsids_link2[THEN order_trans, of _ _ \<open>score (hp\<^sub>s ! 1)\<close> \<open>hps (hp\<^sub>s ! 1)\<close>
          _ \<open>score (hp\<^sub>s ! 0)\<close> \<open>hps (hp\<^sub>s ! 0)\<close> \<open>mset (drop (Suc (Suc 0)) hp\<^sub>s) + trees\<close>])
        using p(1,2,3-4,6,8-) assms(2)
        by (auto simp: pre_def spec_def H1 add_mset_commute[of \<open>hp\<^sub>s ! Suc 0\<close>]
          simp del: VSIDS.link.simps hd_conv_nth simp flip: Cons_nth_drop_Suc)
      subgoal
        by (auto simp: pre_def)
      subgoal
        by (auto simp: pre_def)
      subgoal premises p
        using p(1-4,6,8-) apply -
        apply (rule order_trans)
        apply (rule p)
        subgoal
          by (auto simp: pre_def)
        subgoal
          by (auto)
        apply (refine_vcg)
        apply (rule vsids_link2[THEN order_trans, of _ 
          _ \<open>score (hp\<^sub>s ! (snd x))\<close> \<open>hps (hp\<^sub>s ! (snd x))\<close>
          _ \<open>score (hp\<^sub>s ! (snd x -1))\<close> \<open>hps (hp\<^sub>s ! (snd x -1))\<close>
          \<open>(case VSIDS.merge_pairs (rev (take (snd x - Suc 0) hp\<^sub>s)) of None \<Rightarrow> {#}
          | Some a \<Rightarrow> {#a#}) + mset (drop (Suc (snd x)) hp\<^sub>s) + trees\<close>])
        subgoal
          by (auto simp: spec_def pre_def add_mset_commute[of _ "hp\<^sub>s ! (_ - Suc 0)"] simp del: VSIDS.link.simps VSIDS.merge_pairs.simps)
        apply (refine_vcg)
        subgoal for arrm arrn
          apply (rule vsids_link2[THEN order_trans, of _ 
            _
            \<open>score ((VSIDS.link 
            (Hp (xs ! snd x) (score (hp\<^sub>s ! snd x)) (hps (hp\<^sub>s ! snd x)))
            (Hp (xs ! (snd x - 1)) (score (hp\<^sub>s ! (snd x - 1))) (hps (hp\<^sub>s ! (snd x - 1))))))\<close>
            \<open>hps (VSIDS.link 
              (Hp (xs ! snd x) (score (hp\<^sub>s ! snd x)) (hps (hp\<^sub>s ! snd x)))
              (Hp (xs ! (snd x - 1)) (score (hp\<^sub>s ! (snd x - 1))) (hps (hp\<^sub>s ! (snd x - 1)))))\<close>
            _
            \<open>score (the (VSIDS.merge_pairs (rev (take (snd x - Suc 0) hp\<^sub>s))))\<close>
            \<open>hps (the (VSIDS.merge_pairs (rev (take (snd x - Suc 0) hp\<^sub>s))))\<close>
              \<open>mset (drop (Suc (snd x)) hp\<^sub>s) + trees\<close>])
          subgoal
            unfolding case_prod_beta
            by (cases \<open>VSIDS.merge_pairs (rev (take (snd x - Suc 0) hp\<^sub>s))\<close>)
              (auto simp add: spec_def pre_def add_mset_commute add_mset_commute[of _ "hp\<^sub>s ! (_ - Suc 0)"]
              simp del: VSIDS.link.simps VSIDS.merge_pairs.simps)
          subgoal
            by (auto simp add: spec_def VSIDS_merge_pairs_simps2 pre_def
              simp del: VSIDS.link.simps VSIDS.merge_pairs.simps
              split: option.splits)
          done
       done
    done
    subgoal by (auto simp: spec_def split: option.splits)
    done
qed

definition vsids_del_min where
  \<open>vsids_del_min arr m = undefined
    \<close>
thm VSIDS.merge_pairs.simps
hide_const (open) NEMonad.ASSERT NEMonad.RETURN


term Node
interpretation VSIDS: pairing_heap where
  le = \<open>(\<ge>) :: nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: transp_def)
  subgoal by (auto simp: totalp_on_def)
  done
term lseg
term pure_list_assn
find_theorems lseg 
  term os_list_assn
  thm os_list_assn_def
  term "mk_assn"
term \<open>\<upharpoonleft>arl_assn\<close>
lemma [termination_simp]: \<open>size_list size (hps a) < size a\<close>
  by (cases a) auto

term al_assn
fun lseg :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 'b) hp \<Rightarrow> _ \<Rightarrow> ll_assn\<close> and
  lseg_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 'b) hp list \<Rightarrow> _ \<Rightarrow> ll_assn\<close>
  where
  "lseg containt_assn score_assn a p = (EXS xn' p'. prod_assn containt_assn score_assn (node a, score a) xn' \<and>* lseg_l containt_assn score_assn (hps a) p')" |
  \<open>lseg_l containt_assn score_assn [] p = \<up>True\<close> |
  \<open>lseg_l containt_assn score_assn (a # as) p = (if p=null then sep_false else (EXS r. lseg containt_assn score_assn a p \<and>* lseg_l containt_assn score_assn as r))\<close>

term "\<upharpoonleft>(mk_assn (λl p. lseg atom_assn word64_assn l p))"
term node.next



partial_function (M) vsids_delete :: "'a::llvm_rep ptr \<Rightarrow> unit llM" where
  "vsids_delete p = doM { 
    if p=null then Mreturn () 
    else doM {
      n \<leftarrow> ll_load p;
      ll_free p;
      vsids_delete (hd(hps n))    }
  }"

lemma os_delete_rule[vcg_rules]: 
  "llvm_htriple (\<upharpoonleft>os_list_assn xs p) (os_delete p) (\<lambda>_. \<box>)"  
proof (induction xs arbitrary: p)
  case Nil
  note [simp] = os_list_assn_simps
  show ?case 
    apply (subst os_delete.simps)
    by vcg
next
  case (Cons a xs)
  
  note [vcg_rules] = Cons.IH
  note [simp] = os_list_assn_simps
  
  interpret llvm_prim_ctrl_setup .
  
  show ?case 
    apply (subst os_delete.simps)
    apply vcg
    done
    
  
qed


fun mset_nodes :: "('b, 'a) hp \<Rightarrow>'b multiset" where
"mset_nodes (Hp x _ hs) = {#x#} + sum_mset(mset(map mset_nodes hs))"

(*TODO: do we need to ensure that there are no cycle already here?*)
inductive encoded_pairheap where
  empty: \<open>encoded_pairheap [] {#}\<close> |
  leaf: \<open>encoded_pairheap (arr[n := (x, [])]) (add_mset (Hp n x []) trees)\<close>
  if  \<open>encoded_pairheap arr trees\<close> \<open>n \<notin># \<Sum>\<^sub># (mset_nodes `# trees)\<close>|
  comb: \<open>encoded_pairheap (arr[n := (x, snd (arr!n)@[m])]) (add_mset (Hp n w\<^sub>n (Hp m w\<^sub>m child\<^sub>m # child\<^sub>n)) trees)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n (child\<^sub>n)) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close> and
    \<open>n < length arr\<close>

lemma encoded_pairheap_distinct_nodes: \<open>encoded_pairheap arr trees \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# trees))\<close>
  by (induction rule: encoded_pairheap.induct)
   (auto simp: ac_simps)

lemma \<open>encoded_pairheap arr trees \<Longrightarrow> n \<notin># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> encoded_pairheap (arr [n := a]) trees\<close>
  apply (induction rule: encoded_pairheap.induct)
  apply (auto intro: encoded_pairheap.intros)

(*
From here we need:
  - how to distinguish empty from no children? \<rightarrow> probably easy: by default only a single tree.
  - the node names are not already present
  - congruence on array
*)
lemma drop_tree:
  assumes \<open>encoded_pairheap arr (add_mset (Hp m w child) trees)\<close>
  shows \<open>encoded_pairheap arr (trees)\<close>
  using assms apply (induction arr "add_mset (Hp m w child) trees" rule: encoded_pairheap.induct)
  apply (auto simp: add_mset_eq_add_mset dest!: multi_member_split
    intro: encoded_pairheap.intros)

term VSIDS.link

type_synonym vsids = \<open>(nat \<Rightarrow> nat option) \<times> nat list\<close>

definition vsids :: \<open>nat multiset \<Rightarrow> (nat, 'a) ann_lits \<Rightarrow> vsids \<Rightarrow> bool\<close> where
  \<open>vsids \<A> M \<equiv> (\<lambda>(x, scores). (\<forall>L\<in>#\<A>. undefined_lit M (Pos L) \<longrightarrow> x L \<noteq> None) \<and> (\<forall>L\<in>#\<A>. L < length scores))\<close>

lemma vsids_push_lit:
  \<open>vsids \<A> M x \<Longrightarrow> vsids \<A> (L # M) x\<close>
  by (auto simp: vsids_def)


definition vsids_push_back_if_needed where
  \<open>vsids_push_back_if_needed L = (\<lambda>(heap, scores). do {
      ASSERT (L < length scores);
     ASSERT (pre_map_contains_key (L, heap));
     if (L \<in> dom heap) then RETURN (heap, scores)
     else RETURN (heap(L\<mapsto>scores!L), scores)
  })\<close>
term VSIDS.hm2_assn
definition vsids_assn where
  \<open>vsids_assn N = VSIDS.hm_assn N \<times>\<^sub>a array_assn (unat_assn' TYPE(32))\<close>

lemma op_map_contains_key[pat_rules]: 
  "op_set_member $ k $ (dom$m) \<equiv> op_map_contains_key$'k$'m"
  by (auto intro!: eq_reflection)

sepref_register op_map_contains_key

find_theorems op_map_contains_key
sepref_def vsids_push_back_if_needed_impl
  is \<open>uncurry vsids_push_back_if_needed\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a (vsids_assn N)\<^sup>k \<rightarrow>\<^sub>a vsids_assn N\<close>
  unfolding vsids_assn_def vsids_push_back_if_needed_def
    op_map_contains_key is_None_def
  supply [sepref_fr_rules] = snatb_hnr
  apply annot_all_atm_idxs
  apply (rewrite at \<open>\<hole> \<in> _\<close> value_of_atm_def[symmetric])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id_keep
  unfolding op_map_contains_key
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve_cp
  apply sepref_dbg_constraints

  apply apply sepref_dbg_keep
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_side_unfold
term op_map_contains_key

thm VSIDS.hm12_assn_def
  term VSIDS.hm_assn
term op_map_empty
    term VSIDS.hm_assn
  term mop_map_update
  term VSIDS.hm_pop_min_op
thm VSIDS.hm_pm_peek_min_def
  term mop_pm_peek_min
end
