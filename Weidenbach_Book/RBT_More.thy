theory RBT_More
imports Main "~~/src/HOL/Library/RBT" "$AFP/Nested_Multisets_Ordinals/Multiset_More"
begin

section \<open>More red-black trees\<close>

text \<open>The file @{file "~~/src/HOL/Library/RBT.thy"} contains the lifting from a red-black tree to
  the version with invariants (sorted keys for example). However, some properties are missing\<close>

subsection \<open>Keys and Entries\<close>

subsubsection \<open>Additional Properties\<close>

lemma RBT_keys_RBT_delete: "RBT.keys (RBT.delete k C) = remove1 k (RBT.keys C)"
  by (rule sorted_distinct_set_unique) (auto simp: sorted_remove1 lookup_keys[symmetric])

lemma RBT_entries_empty[simp]: "RBT.entries RBT.empty = []"
  by (simp add: empty.rep_eq entries.rep_eq)

lemma keys_empty[simp]: "RBT.keys RBT.empty = []"
  by (simp add: keys_def_alt)

lemma image_mset_fst_RBT_entries_keys:
  "image_mset fst (mset (RBT.entries C)) = mset (RBT.keys C)"
  by (simp add: keys_def_alt)

lemma distinct_rbt_entries:
  "distinct (RBT.entries t)"
  using RBT.distinct_entries by (metis distinct_zipI1 zip_map_fst_snd)


subsubsection \<open>Multiset version\<close>

abbreviation RBT_entries_mset :: "('a::linorder, 'b) RBT.rbt \<Rightarrow> ('a \<times> 'b) multiset" where
"RBT_entries_mset C \<equiv> mset (RBT.entries C)"

abbreviation RBT_keys_mset :: "('a::linorder, 'b) RBT.rbt \<Rightarrow> 'a multiset" where
"RBT_keys_mset C \<equiv> mset (RBT.keys C)"

lemma rbt_insert_swap:
  "i \<noteq> j \<Longrightarrow>
  RBT.entries (RBT.insert j b (RBT.insert i a C)) = RBT.entries (RBT.insert i a (RBT.insert j b C))"
  "RBT.entries (RBT.insert i a (RBT.insert i a C)) = RBT.entries (RBT.insert i a (RBT.insert i b C))"
  unfolding entries_lookup by (rule ext) auto



lemma mset_entries_insert:
  assumes lookup: "RBT.lookup C j = Some j'"
  shows "mset (RBT.entries (RBT.insert j i' C)) = add_mset (j, i')
    (remove1_mset (j, j') (mset (RBT.entries C))) " (is "?l = ?r")
proof (rule distinct_set_mset_eq)
  show \<open>distinct_mset ?l\<close>
    by (simp add: distinct_rbt_entries; fail)

  have \<open>(j, i') \<notin># remove1_mset (j, j') (RBT_entries_mset C)\<close>
    by (metis add_mset_remove_trivial_If distinct_count_atmost_1 lookup
        distinct_mset_add_mset distinct_mset_def distinct_rbt_entries lookup_in_tree
        mset_remove1 notin_set_remove1 option.simps(1) set_mset_mset)
  then show "distinct_mset ?r"
    by (auto simp: distinct_rbt_entries)[]

  show "set_mset ?l = set_mset ?r"
    using lookup by (auto simp add: distinct_rbt_entries lookup_in_tree[symmetric]
      distinct_mset_remove1_All split: if_splits)
qed


lemma mset_RBT_entries_insert:
  "mset (RBT.entries (RBT.insert a a' C)) =
    add_mset (a, a') (remove1_mset (a, the (RBT.lookup C a)) (mset (RBT.entries C)))"
  apply (rule distinct_set_mset_eq)
     apply (simp add: distinct_mset_filter distinct_rbt_entries; fail)
    apply (metis distinct_mem_diff_mset distinct_mset_add_mset distinct_mset_minus
      distinct_mset_mset_distinct distinct_mset_singleton distinct_mset_size_2
      distinct_rbt_entries in_diffD in_multiset_in_set lookup_in_tree option.sel)
  by (auto simp add: distinct_mset_filter distinct_rbt_entries
      distinct_remove1_removeAll Multiset.mset_remove1[symmetric]
      lookup_in_tree[symmetric]
      simp del: Multiset.mset_remove1 split: if_splits)

lemma mset_RBT_keys_insert:
  "mset (RBT.keys (RBT.insert k v rbt)) =
    (if k \<in># mset (RBT.keys rbt) then mset (RBT.keys rbt) else {#k#} + mset (RBT.keys rbt))"
  by (auto simp: image_mset_fst_RBT_entries_keys[symmetric] mset_RBT_entries_insert
    image_mset_remove1_mset_if lookup_in_tree[symmetric] single_remove1_mset_eq)

lemma length_RBT_keys_insert:
  "length (RBT.keys (RBT.insert k v rbt)) =
    (if k \<in># mset (RBT.keys rbt) then length (RBT.keys rbt) else 1 + length (RBT.keys rbt))"
  unfolding size_mset[symmetric] mset_RBT_keys_insert by auto

lemma RBT_entries_insert_empty[simp]:
  fixes L :: 'v and a :: "'a :: {linorder}"
  shows "RBT.entries (RBT.insert a L RBT.empty) = [(a, L)]"
proof -
  have M: "mset (RBT.entries (RBT.insert a L RBT.empty)) = mset [(a, L)]"
    by (auto simp: mset_RBT_entries_insert)
  have l: "list = []" "aa = a" "b = L" if "add_mset (aa, b) (mset list) = {#(a, L)#}"
    for list :: "('a \<times> 'v) list" and aa :: 'a and b :: 'v
    using that by auto
  show ?thesis
    using M by (cases "RBT.entries (RBT.insert a L RBT.empty)") auto
qed

lemma snd_entries_the_lookup:
  "image_mset snd (mset (RBT.entries C)) =
    {#the (RBT.lookup C (fst x)). x \<in># mset (RBT.entries C)#}"
  unfolding multiset_eq_iff by (metis (mono_tags, lifting) image_mset_cong2 lookup_in_tree
    option.sel prod.collapse set_mset_mset)

lemma count_RBT_entries:
  "count (mset (RBT.entries C)) (a, b) = (if RBT.lookup C a = Some b then 1 else 0)"
  by (meson distinct_count_atmost_1 distinct_rbt_entries lookup_in_tree)

lemma count_RBT_keys:
  "count (mset (RBT.keys C)) a = (if RBT.lookup C a \<noteq> None then 1 else 0)"
  by (metis RBT.distinct_keys RBT.keys_entries distinct_count_atmost_1 lookup_in_tree not_Some_eq)

lemma in_RBT_keys_lookup: "j \<in> set (RBT.keys C) \<longleftrightarrow> RBT.lookup C j \<noteq> None"
  unfolding lookup_keys[symmetric] by fastforce

lemma RBT_keys_insert_insort:
  "RBT.keys (RBT.insert k v C) = insort k (remove1 k (RBT.keys C))"
proof -
  show ?thesis
  proof (cases \<open>k \<in># RBT_keys_mset C\<close>)
    case True
    have "\<And>f a. dom f = insert (a::'a) (dom f) \<or> (None::'b option) = f a"
      by (metis (no_types) dom_fun_upd fun_upd_triv)
    then have H: "RBT.keys (RBT.insert k v C) = insort k (remove1 k (RBT.keys C))"
      if "k \<in># RBT_keys_mset C" using that
      by (metis (no_types) RBT.distinct_keys domIff dom_fun_upd insort_remove1 lookup_insert
          lookup_keys option.simps(3) set_mset_mset sorted_distinct_set_unique sorted_keys)
    then show ?thesis using True by auto
  next
    case False
    assume a1: "k \<notin># RBT_keys_mset C"
    then have "\<And>b. insort k (sorted_list_of_multiset (RBT_keys_mset C)) =
        RBT.keys (RBT.insert k b C)"
      by (metis (no_types) add.commute add_mset_add_single mset_RBT_keys_insert properties_for_sort
          sorted_keys sorted_list_of_multiset_insert sorted_list_of_multiset_mset)
    then show ?thesis
      using a1 by (simp add: remove1_idem sorted_sort_id)
  qed
qed

lemma length_RBT_entries_keys:
  "length (RBT.entries C) = length (RBT.keys C)"
  by (simp add: keys_def_alt)

lemma RBT_lookup_Some_in_keysD:
  "RBT.lookup C k = Some a \<Longrightarrow> k \<in> set (RBT.keys C)"
  by (simp add: in_RBT_keys_lookup)


subsection \<open>Elements\<close>

definition RBT_elements :: "('a :: linorder, 'b) RBT.rbt \<Rightarrow> 'b list" where
"RBT_elements C = map snd (RBT.entries C)"

lemma RBT_entries_zip_keys_elements:
  "RBT.entries C = zip (RBT.keys C) (RBT_elements C)"
  by (simp add: keys_def_alt zip_map_fst_snd RBT_elements_def)

abbreviation RBT_elements_mset :: "('a::linorder, 'b) RBT.rbt \<Rightarrow> 'b multiset" where
"RBT_elements_mset C \<equiv> mset (RBT_elements C)"

lemma RBT_elements_mset_image_mset_lookup_keys_mset:
  "RBT_elements_mset C = {#the (RBT.lookup C x). x \<in># RBT_keys_mset C#}"
  by (metis (no_types, lifting) RBT.distinct_keys RBT.map_of_entries RBT_elements_def
    image_mset_cong2 image_mset_map_of keys_def_alt)


subsection \<open>Induction Principle\<close>

text \<open>The first assumptions is needed. Otherwise the predicate @{term P} could rely on the internal
  data-structure.\<close>
lemma rbt_induct[case_names independancy empty insert]:
  assumes
    indep_of_imp: "\<And>S T. RBT.lookup S = RBT.lookup T \<Longrightarrow> P S \<Longrightarrow> P T" and
    empty: "P RBT.empty" and
    insert: "\<And>k v C. (\<forall>k' \<in> set (RBT.keys C). k < k') \<Longrightarrow> P C \<Longrightarrow> P (RBT.insert k v C)"
  shows "P C"
proof (induction "RBT.keys C" arbitrary: C)
  case Nil
  then show ?case by (metis empty non_empty_keys)
next
  case (Cons k ks C) note IH = this(1) and keys = this(2)
  let ?C = "RBT.delete k C"
  have "RBT.lookup C k \<noteq> None"
    by (metis append_Nil domIff in_set_conv_decomp keys lookup_keys)
  have keys_C: "RBT.keys ?C = ks"
    by (simp add: RBT_keys_RBT_delete keys[symmetric])
  then have "P ?C" using IH[of ?C] by blast
  moreover have "\<forall>k' \<in> set (RBT.keys ?C). k < k'"
    using sorted_keys[of C] distinct_keys[of C] le_imp_less_or_eq unfolding keys[symmetric] keys_C
    by (auto simp: sorted_Cons)
  ultimately have [simp]: "P (RBT.insert k (the (RBT.lookup C k)) ?C)"
    using insert[of ?C] by blast
  show ?case
    apply (rule indep_of_imp[of "RBT.insert k (the (RBT.lookup C k)) ?C"])
    using \<open>RBT.lookup C k \<noteq> None\<close> by auto
qed

end
