theory RBT_More
imports Main "~~/src/HOL/Library/RBT" "../lib/Multiset_More" 
begin

section \<open>More red-black trees\<close>

text \<open>The file @{file "~~/src/HOL/Library/RBT.thy"} contains the lifting from a red-black tree to
  the version with invariants (sorted keys for example). However, some properties are missing\<close>

lemma RBT_entries_empty[simp]: "RBT.entries RBT.empty = []"
  by (simp add: empty.rep_eq entries.rep_eq)


lemma keys_empty[simp]: "RBT.keys RBT.empty = []"
  by (simp add: keys_def_alt)

lemma image_mset_fst_RBT_entries_keys:
  "image_mset fst (mset (RBT.entries C)) = mset (RBT.keys C)"
  by (simp add: image_mset_mset_mset_map keys_def_alt)

lemma rbt_insert_swap:
  "i \<noteq> j \<Longrightarrow>
  RBT.entries (RBT.insert j b (RBT.insert i a C)) = RBT.entries (RBT.insert i a (RBT.insert j b C))"
  "RBT.entries (RBT.insert i a (RBT.insert i a C)) = RBT.entries (RBT.insert i a (RBT.insert i b C))"
  unfolding entries_lookup by (rule ext) auto

lemma distinct_rbt_entries:
  "distinct (RBT.entries t)"
  using RBT.distinct_entries by (metis distinct_zipI1 zip_map_fst_snd)

lemma mset_entries_insert:
  "RBT.lookup C j = Some j' \<Longrightarrow>
    mset (RBT.entries (RBT.insert j i' C)) = {#(j, i')#} +
    remove1_mset (j, j') (mset (RBT.entries C))"
  apply (rule distinct_set_mset_eq)
     apply (simp add: distinct_rbt_entries; fail)
    apply (metis distinct_mem_diff_mset distinct_mset_add_single distinct_mset_distinct
      distinct_mset_minus distinct_rbt_entries in_diffD in_multiset_in_set lookup_in_tree
      multi_member_last option.sel)
  by (auto simp add: distinct_rbt_entries lookup_in_tree[symmetric] split: if_splits)
  
text \<open>As there is no property about the ordering of the result of @{term RBT.entries}, multiset are 
  the natural representation of the output.\<close>
lemma mset_RBT_entries_insert:
  "mset (RBT.entries (RBT.insert a a' C)) = 
    {#(a, a')#} + remove1_mset (a, the (RBT.lookup C a)) (mset (RBT.entries C))"
  apply (rule distinct_set_mset_eq)
    apply (simp add: distinct_mset_filter distinct_rbt_entries; fail)
   apply (auto simp: distinct_mset_add_single distinct_rbt_entries lookup_in_tree[symmetric]; 
     fail)[]
  by (auto simp add: distinct_mset_filter distinct_rbt_entries lookup_in_tree[symmetric] split: if_splits )

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
  have l: "list = []" "aa = a" "b = L" if "mset list + {#(aa, b)#} = {#(a, L)#}" 
    for list :: "('a \<times> 'v) list" and aa :: 'a and b :: 'v
    proof -
      show [simp]: "list = []"
        using that by (metis add.left_neutral add_right_imp_eq empty_iff insert_iff list.set(1)
          list.set(2) mset.simps(2) mset_zero_iff set_mset_mset)
      show "aa = a" and "b = L" using that by auto
    qed
  show ?thesis
    using M by (cases "RBT.entries (RBT.insert a L RBT.empty)") (auto simp: l)
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

end