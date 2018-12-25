theory WB_More_Refinement_List
  imports Refine_Imperative_HOL.IICF Weidenbach_Book_Base.WB_List_More
begin

section \<open>More theorems about list\<close>

text \<open>This should theorem and functions that defined in the Refinement Framework, but not in
\<^theory>\<open>HOL.List\<close>. There might be moved somewhere eventually in the AFP or so.
\<close>
lemma swap_nth_irrelevant:
  \<open>k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> swap xs i j ! k = xs ! k\<close>
  by (auto simp: swap_def)

lemma swap_nth_relevant:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i j ! i = xs ! j\<close>
  by (cases \<open>i = j\<close>) (auto simp: swap_def)

lemma swap_nth_relevant2:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs j i ! i = xs ! j\<close>
  by (auto simp: swap_def)

lemma swap_nth_if:
  \<open>i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> swap xs i j ! k =
    (if k = i then xs ! j else if k = j then xs ! i else xs ! k)\<close>
  by (auto simp: swap_def)

lemma drop_swap_irrelevant:
  \<open>k > i \<Longrightarrow> k > j \<Longrightarrow> drop k (swap outl' j i) = drop k outl'\<close>
  by (subst list_eq_iff_nth_eq) auto

lemma take_swap_relevant:
  \<open>k > i \<Longrightarrow> k > j \<Longrightarrow>  take k (swap outl' j i) = swap (take k outl') i j\<close>
  by (subst list_eq_iff_nth_eq) (auto simp: swap_def)

lemma tl_swap_relevant:
  \<open>i > 0 \<Longrightarrow> j > 0 \<Longrightarrow> tl (swap outl' j i) = swap (tl outl') (i - 1) (j - 1)\<close>
  by (subst list_eq_iff_nth_eq)
    (cases \<open>outl' = []\<close>; cases i; cases j; auto simp: swap_def tl_update_swap nth_tl)

lemma swap_only_first_relevant:
  \<open>b \<ge> i \<Longrightarrow> a < length xs  \<Longrightarrow>take i (swap xs a b) = take i (xs[a := xs ! b])\<close>
  by (auto simp: swap_def)

text \<open>TODO this should go to a different place from the previous lemmas, since it concerns
\<^term>\<open>Misc.slice\<close>, which is not part of \<^theory>\<open>HOL.List\<close> but only part of the Refinement Framework.
\<close>
lemma slice_nth:
  \<open>\<lbrakk>from \<le> length xs; i < to - from\<rbrakk> \<Longrightarrow> Misc.slice from to xs ! i = xs ! (from + i)\<close>
  unfolding slice_def Misc.slice_def
  apply (subst nth_take, assumption)
  apply (subst nth_drop, assumption)
  ..

lemma slice_irrelevant[simp]:
  \<open>i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i \<ge> to \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  \<open>i \<ge> to \<or> i < from \<Longrightarrow> Misc.slice from to (xs[i := C]) = Misc.slice from to xs\<close>
  unfolding Misc.slice_def apply auto
  by (metis drop_take take_update_cancel)+

lemma slice_update_swap[simp]:
  \<open>i < to \<Longrightarrow> i \<ge> from \<Longrightarrow> i < length xs \<Longrightarrow>
     Misc.slice from to (xs[i := C]) = (Misc.slice from to xs)[(i - from) := C]\<close>
  unfolding Misc.slice_def by (auto simp: drop_update_swap)

lemma drop_slice[simp]:
  \<open>drop n (Misc.slice from to xs) = Misc.slice (from + n) to xs\<close> for "from" n to xs
    by (auto simp: Misc.slice_def drop_take ac_simps)

lemma take_slice[simp]:
  \<open>take n (Misc.slice from to xs) = Misc.slice from (min to (from + n)) xs\<close> for "from" n to xs
  using antisym_conv by (fastforce simp: Misc.slice_def drop_take ac_simps min_def)

lemma slice_append[simp]:
  \<open>to \<le> length xs \<Longrightarrow> Misc.slice from to (xs @ ys) = Misc.slice from to xs\<close>
  by (auto simp: Misc.slice_def)

lemma slice_prepend[simp]:
  \<open>from \<ge> length xs \<Longrightarrow>
     Misc.slice from to (xs @ ys) = Misc.slice (from - length xs) (to - length xs) ys\<close>
  by (auto simp: Misc.slice_def)

lemma slice_len_min_If:
  \<open>length (Misc.slice from to xs) =
     (if from < length xs then min (length xs - from) (to - from) else 0)\<close>
  unfolding min_def by (auto simp: Misc.slice_def)

lemma slice_start0: \<open>Misc.slice 0 to xs = take to xs\<close>
  unfolding Misc.slice_def
  by auto

lemma slice_end_length: \<open>n \<ge> length xs \<Longrightarrow> Misc.slice to n xs = drop to xs\<close>
  unfolding Misc.slice_def
  by auto

lemma slice_swap[simp]:
   \<open>l \<ge> from \<Longrightarrow> l < to \<Longrightarrow> k \<ge> from \<Longrightarrow> k < to \<Longrightarrow> from < length arena \<Longrightarrow>
     Misc.slice from to (swap arena l k) = swap (Misc.slice from to arena) (k - from) (l - from)\<close>
  by (cases \<open>k = l\<close>) (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)

lemma drop_swap_relevant[simp]:
  \<open>i \<ge> k \<Longrightarrow> j \<ge> k \<Longrightarrow> j < length outl' \<Longrightarrow>drop k (swap outl' j i) = swap (drop k outl') (j - k) (i - k)\<close>
  by (cases \<open>j = i\<close>)
    (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)


lemma swap_swap: \<open>k < length xs \<Longrightarrow> l < length xs \<Longrightarrow> swap xs k l = swap xs l k\<close>
  by (cases \<open>k = l\<close>)
    (auto simp: Misc.slice_def swap_def drop_update_swap list_update_swap)

lemma in_mset_rel_eq_f_iff:
  \<open>(a, b) \<in> \<langle>{(c, a). a = f c}\<rangle>mset_rel \<longleftrightarrow> b = f `# a\<close>
  using ex_mset[of a]
  by (auto simp: mset_rel_def br_def rel2p_def[abs_def] p2rel_def rel_mset_def
      list_all2_op_eq_map_right_iff' cong: ex_cong)


lemma in_mset_rel_eq_f_iff_set:
  \<open>\<langle>{(c, a). a = f c}\<rangle>mset_rel = {(b, a). a = f `# b}\<close>
  using in_mset_rel_eq_f_iff[of _ _ f] by blast

lemma list_rel_append_single_iff:
  \<open>(xs @ [x], ys @ [y]) \<in> \<langle>R\<rangle>list_rel \<longleftrightarrow>
    (xs, ys) \<in> \<langle>R\<rangle>list_rel \<and> (x, y) \<in> R\<close>
  using list_all2_lengthD[of \<open>(\<lambda>x x'. (x, x') \<in> R)\<close> \<open>xs @ [x]\<close> \<open>ys @ [y]\<close>]
  using list_all2_lengthD[of \<open>(\<lambda>x x'. (x, x') \<in> R)\<close> \<open>xs\<close> \<open>ys\<close>]
  by (auto simp: list_rel_def list_all2_append)

end