theory WB_Sort
  imports
    Watched_Literals.WB_More_Refinement
begin

definition choose_pivot :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>choose_pivot _ _ _ i j = SPEC(\<lambda>k. k \<ge> i \<and> k \<le> j)\<close>

definition isPartition :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition R xs i j k \<equiv> (\<forall> k. k \<le> j \<and> k \<ge> i \<longrightarrow> R (xs!k) (xs!j)) \<and> (\<forall> k. k \<ge> j \<and> k \<le> j \<longrightarrow> R (xs!j) (xs!k))\<close>

definition isPartition_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_map R h xs i j k \<equiv> isPartition R (map h xs) i j k\<close>

term FOREACHi
value \<open>[0..<42]\<close> \<comment> \<open>This does not include \<open>42\<close>.\<close>

definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h i0 j0 xs0 = do {
    ASSERT(i0 < length xs0 \<and> j0 < length xs0 \<and> j0 > i0);
    k \<leftarrow> choose_pivot R h xs0 i0 j0; \<comment> \<open>choice of pivot\<close>
    xs \<leftarrow> RETURN (swap xs0 k j0);
    ASSERT(length xs = length xs0);
    pivot \<leftarrow> RETURN (h (xs ! j0));
    (i, xs) \<leftarrow> FOREACHi
      (\<lambda>js (i, xs). i < length xs \<and> mset xs = mset xs0 \<and> i \<ge> i0 \<and>
	     i \<le> (j0 - 1) - card js)
      (set [i0..<j0])
      (\<lambda>j (i, xs). do {
	      ASSERT(j < length xs \<and> i < length xs \<and> mset xs = mset xs0); \<comment> \<open>@maxi Add stronger invariant here\<close>
       	if R (h (xs!j)) pivot
      	then RETURN (i+1, swap xs i j)
      	else RETURN (i, xs)
      })
      (i0, xs);
    ASSERT(i < length xs \<and> j0 < length xs);
    RETURN (swap xs i j0, i)
  }\<close>

lemma Min_atLeastLessThan[simp]: \<open>b > a \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by auto

lemma Min_atLeastLessThan2[simp]: \<open>{a..<b} \<noteq> {} \<Longrightarrow> Min {a..<b} = a\<close> for a b :: nat
  using linorder_class.eq_Min_iff[of \<open>{a..<b}\<close> a]
  by auto


lemma partition_between_mset_eq:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>j > i\<close>
  shows \<open>partition_between R h i j xs \<le>
    SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and>
                    p < length xs \<and> isPartition_map R h xs' i j p)\<close>
proof -
  have H: \<open>Suc b \<le> j - card \<sigma>\<close>
    if
      a4: \<open>\<sigma> \<subseteq> {i..<j - Suc 0}\<close> and
      a2: \<open>x2 = Suc b\<close> and
      a3: \<open>i \<le> b\<close> and
      a1: \<open>b \<le> j - Suc (card \<sigma>)\<close>
      for \<sigma> b it ix xi2' a x x1 x2 x2'
  proof -
    have f6: "\<forall>n na. 0 < card {na::nat..<n} \<or> \<not> na < n"
      using card_atLeastLessThan by presburger
    have f7: "\<forall>n na. card {n::nat..<na} = 0 \<or> \<not> na \<le> n"
      using card_atLeastLessThan by presburger
    then have f8: "\<forall>n na. card {n..<Suc na} = 0 \<or> \<not> na < n"
      by (meson Suc_leI)
    have f9: "\<not> (0::nat) < 0"
      by fastforce
    have f10: "\<forall>n na. (n::nat) \<le> na \<or> card {na..<n} \<noteq> 0"
      by simp
    have f11: "\<forall>n na. \<not> n < Suc na \<or> \<not> na < n"
      using f9 f8 f6 by metis
    have f12: "\<forall>n na. card {na::nat..<n} = 0 \<or> na < n"
      by (metis (no_types) card_atLeastLessThan neq0_conv zero_less_diff)
    have f13: "\<forall>n. Suc (card {Suc 0..<n}) = n \<or> \<not> 0 < n"
      by (metis (full_types) Suc_pred card_atLeastLessThan)
    have f14: "\<not> b < i"
      using f7 f6 a3 neq0_conv by blast
    have "\<not> card {i..<card {Suc 0..<j}} < card \<sigma>"
      using f11 a4 by (metis card_atLeastLessThan card_mono finite_atLeastLessThan le_imp_less_Suc)
    then show ?thesis
      using f14 f13 f12 f10 f8 assms(3) a2 a1
      by (metis (no_types) Suc_diff_Suc card_atLeastLessThan le_imp_less_Suc nat_diff_split neq0_conv)
  qed

  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure (\<lambda>(i, j, _). j - i)\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (force dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal using assms by (auto dest: mset_eq_length)
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal for x it \<sigma> a b x1 x2
      apply (subst card_Diff_singleton)
      apply (auto dest: finite_subset simp: Suc_pred card_gt_0_iff)
      apply (subst Suc_pred)
      by (auto dest: finite_subset simp: card_gt_0_iff intro!: H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x it \<sigma> a b x1 x2
      by (subst card_Diff_singleton)
        (auto dest: finite_subset simp: card_gt_0_iff)
    subgoal by auto
    subgoal by (force dest: mset_eq_length)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    \<comment> \<open>I think we need a stronger invariant to prove this.\<close>
    subgoal sorry
    subgoal sorry
    done
qed

definition sublist :: \<open>'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
\<open>sublist xs i j \<equiv> take (1+j-i) (drop i xs)\<close>

value \<open>sublist [0,1,2,3::nat] 1 3\<close>
value \<open>sublist [0::nat] 0 0\<close>

lemma sublist_single: \<open>i < length xs \<Longrightarrow> sublist xs i i = [xs!i]\<close>
  by (simp add: sublist_def Hash_Map.take_Suc0(2))

lemma insert_eq: \<open>insert a b = b \<union> {a}\<close>
  by auto

lemma sublist_nth: \<open>\<lbrakk>i1 \<le> i2; i2 < length xs; k \<le> (i2-i1)\<rbrakk> \<Longrightarrow> (sublist xs i1 i2)!k = xs!(i1+k)\<close>
  by (simp add: sublist_def)

lemma sublist_length: \<open>\<lbrakk>i \<le> j; j < length xs\<rbrakk> \<Longrightarrow> length (sublist xs i j) = 1 + j - i\<close>
  by (simp add: sublist_def)

lemma sublist_not_empty: \<open>\<lbrakk>i \<le> j; j < length xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> sublist xs i j \<noteq> []\<close>
  apply simp
  apply (rewrite List.length_greater_0_conv[symmetric])
  apply (rewrite sublist_length)
  by auto

lemma sublist_app: \<open>\<lbrakk>i1 \<le> i2; i2 \<le> i3\<rbrakk> \<Longrightarrow> sublist xs i1 i2 @ sublist xs (Suc i2) i3 = sublist xs i1 i3\<close>
  unfolding sublist_def
  by (smt Suc_eq_plus1_left Suc_le_mono append.assoc le_SucI le_add_diff_inverse le_trans same_append_eq take_add)

definition sorted_sublist :: \<open>'a::linorder list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
\<open>sorted_sublist xs i j = sorted (sublist xs i j)\<close>

lemma sorted_sublist_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist xs i i\<close>
  apply (simp add: sorted_sublist_def)
  apply (rewrite sublist_single)
  by auto

lemma sorted_sublist_partition:
  assumes \<open>i1 \<le> i2\<close> and \<open>i2 + 1 \<le> i3\<close> and
    \<open>sorted_sublist xs i1 i2\<close> and
    \<open>sorted_sublist xs (i2+2) i3\<close> and
    \<open>\<And> k. k \<ge> i1 \<and> k \<le> i2     \<longrightarrow> xs!k \<le> xs!(i2+1)\<close> and
    \<open>\<And> k. k \<ge> i2 + 1 \<and> k \<le> i3 \<longrightarrow> xs!k \<ge> xs!(i2+1)\<close>
  shows \<open>sorted_sublist xs i1 i3\<close>
  apply (simp add: sorted_sublist_def)
  oops


\<comment> \<open>The left part is already sorted. The elements are always the same. \<open>i\<close> and \<open>j\<close> are pointers on
    the list, and \<open>i\<le>j\<close>.\<close>
definition quicksort_inv :: \<open>'a::linorder list \<Rightarrow> nat \<Rightarrow> ('a list * nat * nat) \<Rightarrow> bool\<close> where
\<open>quicksort_inv xs0 i0 p \<equiv>
  case p of
    (xs,i,j) \<Rightarrow>
      i < length xs \<and> j < length xs \<and> i \<le> j \<and>
      mset xs = mset xs0 \<and>
      sorted_sublist xs i0 i\<close>

definition quicksort :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h i0 j0 xs0 = do {
  RECT (\<lambda>f (i, j, xs). do {
      ASSERT(quicksort_inv xs0 i0 (xs, i, j));
      if j\<le>i then RETURN xs
      else do {
	      (xs, p) \<leftarrow> partition_between R h i j xs;
      	xs \<leftarrow> f (i, p-1, xs);
      	f (p+1, j, xs)
      }
    })
    (i0, j0, xs0)
  }\<close>

lemma quicksort_between_mset_eq:
  assumes \<open>i < length xs\<close> and \<open>j < length xs\<close> and \<open>j \<ge> i\<close>
  shows \<open>quicksort R h i j xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs' \<and> sorted_sublist xs' i j))\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(i, j, xs). Suc j - i))\<close>
    by auto
  have pre: \<open>quicksort_inv xs i (xs, i,j)\<close>
    using assms by (auto simp add: quicksort_inv_def sorted_sublist_refl)
  show ?thesis
    unfolding quicksort_def
    apply (rule RECT_rule)
       apply (refine_mono)
      apply (rule wf)
     apply (rule pre)
    subgoal premises IH for f x
      using IH
      apply (refine_vcg)
      apply auto
      subgoal
        \<comment> \<open>apply rule for \<open>partition_between\<close> somehow\<close>
        sorry
      subgoal
        sorry
      subgoal sorry
      apply (rule spec) sorry
    done
qed

text \<open>We use the median of the first, the middle, and the last element.\<close>
definition choose_pivot3 where
  \<open>choose_pivot3 R h xs i (j::nat) = do {
    ASSERT(i < length xs);
    ASSERT(j < length xs);
    let k = (i + j) div 2;
    let start = h (xs ! i);
    let mid = h (xs ! k);
    let end = h (xs ! j);
    if (R start mid \<and> R mid end) \<or> (R end mid \<and> R mid start) then RETURN k
    else if (R start end \<and> R end mid) \<or> (R mid end \<and> R end start) then RETURN j
    else RETURN i
}\<close>

lemma choose_pivot3_choose_pivot:
  assumes \<open>i < length xs\<close> \<open>j < length xs\<close> \<open>j \<ge> i\<close>
  shows \<open>choose_pivot3 R h xs i j \<le> \<Down> Id (choose_pivot R h xs i j)\<close>
  unfolding choose_pivot3_def choose_pivot_def
  using assms by (auto intro!: ASSERT_leI simp: Let_def)

definition partition_between_ref
  :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close>
where
  \<open>partition_between_ref R h i0 j0 xs0 = do {
    ASSERT(i0 < length xs0 \<and> j0 < length xs0 \<and> j0 > i0);
    k \<leftarrow> choose_pivot3 R h xs0 i0 j0; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k j0);
    ASSERT(length xs = length xs0);
    pivot \<leftarrow> RETURN (h (xs ! j0));
    (i, xs) \<leftarrow> nfoldli
      ([i0..<j0])
      (\<lambda>_. True)
      (\<lambda>j (i, xs). do {
	      ASSERT(j < length xs \<and> i < length xs \<and> mset xs = mset xs0);
      	if R (h (xs!j)) pivot
      	then RETURN (i+1, swap xs i j)
      	else RETURN (i, xs)
      })
      (i0, xs);
    ASSERT(i < length xs \<and> j0 < length xs);
    RETURN (swap xs i j0, i)
  }\<close>

lemma partition_between_ref_partition_between:
  \<open>partition_between_ref R h i j xs \<le> (partition_between R h i j xs)\<close>
proof -
  have swap: \<open>(swap xs k j, swap xs ka j) \<in> Id\<close> if \<open>k = ka\<close>
    for k ka
    using that by auto
  have [refine0]: \<open>(h (xsa ! j), h (xsaa ! j)) \<in> Id\<close>
    if \<open>(xsa, xsaa) \<in> Id\<close>
    for xsa xsaa
    using that by auto
  have [refine0]: \<open>(RETURN ([i..<j]), it_to_sorted_list (\<lambda>_ _. True) (set [i..<j]))
       \<in> {(c, a).
          c \<le> \<Down> {(x, y).
                 list_all2 (\<lambda>x x'. (x, x') \<in> Id) x
                  y}
               a}\<close>
    by (auto simp: it_to_sorted_list_def list.rel_eq
      intro!: RETURN_RES_refine exI[of _ \<open>([i..<j])\<close>])
  have [refine0]: \<open>(\<lambda>j (i, xs). do {
             _ \<leftarrow> ASSERT (j < length xs \<and> i < length xs \<and> mset xs = mset xsa);
             if R (h (xs ! j)) pivot then RETURN (i + 1, swap xs i j)
             else RETURN (i, xs)
           },
        \<lambda>j (i, xs). do {
             _ \<leftarrow> ASSERT (j < length xs \<and> i < length xs \<and> mset xs = mset xsa);
             if R (h (xs ! j)) pivota then RETURN (i + 1, swap xs i j)
             else RETURN (i, xs)
           })
       \<in> {(f, f').
          \<forall>x y. (x, y) \<in> nat_rel \<longrightarrow>
                (\<forall>xa ya.
                    (xa, ya) \<in> Id \<longrightarrow>
                    f x xa \<le> \<Down> Id (f' y ya))}\<close>
    if \<open>(pivot, pivota) \<in> Id\<close>
    for pivot pivota xsa
    using that
    by (auto intro!: ext ASSERT_leI)

  show ?thesis
    apply (subst (2) Down_id_eq[symmetric])
    unfolding partition_between_ref_def
      partition_between_def FOREACH_patterns
      LIST_FOREACH'_def[of \<open>RETURN _\<close>, unfolded nres_monad1, symmetric]
      OP_def
    apply (refine_vcg choose_pivot3_choose_pivot swap
      LIST_FOREACH_autoref["to_\<Down>"] \<comment> \<open>@Peter: what is the proper way to do that?\<close>
      )
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma partition_between_ref_partition_between':
  \<open>(uncurry2 (partition_between_ref R h), uncurry2 (partition_between R h)) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  (* by (intro frefI nres_relI)
    (auto intro: partition_between_ref_partition_between) *)
  oops


definition choose_pivot3_impl where
  \<open>choose_pivot3_impl = choose_pivot3 (<) id\<close>

sepref_definition choose_pivot3_impl_code
  is \<open>uncurry2 (choose_pivot3_impl)\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>k  *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k\<rightarrow>\<^sub>a nat_assn\<close>
  unfolding choose_pivot3_impl_def choose_pivot3_def id_def
  by sepref

declare choose_pivot3_impl_code.refine[sepref_fr_rules]


definition partition_between_impl where
  \<open>partition_between_impl = partition_between_ref (<) id\<close>

sepref_register choose_pivot3 partition_between_ref

sepref_definition partition_between_code
  is \<open>uncurry2 (partition_between_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_ref_def partition_between_impl_def
    choose_pivot3_impl_def[symmetric]
  unfolding id_def
  by sepref

declare partition_between_code.refine[sepref_fr_rules]

term partition_between_ref_code


definition quicksort_ref :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort_ref R h i0 j0 xs0 = do {
  RECT (\<lambda>f (i,j,xs). do {
      ASSERT(quicksort_inv xs0 i0 (xs, i, j));
      if j\<le>i then RETURN xs
      else do{
      	(xs, p) \<leftarrow> partition_between_ref R h i j xs;
      	xs \<leftarrow> f (i, p-1, xs);
      	f (p+1, j, xs)
      }
    })
    (i0, j0, xs0)
  }\<close>

lemma quicksort_ref_quicksort:
  \<open>quicksort_ref R f i j xs \<le> \<Down> Id (quicksort R f i j xs)\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(i, j, xs). Suc j - i))\<close>
    by auto
  have pre: \<open> ((i, j, xs), i, j, xs) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close>
    by auto
  have f: \<open>f (x1b, x2e - 1, x1e)
	\<le> \<Down> Id
	   (fa (x1, x2d - 1, x1d))\<close>
    if
      H: \<open>\<And>x x'.
	  (x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel) \<Longrightarrow>
	  f x \<le> \<Down> Id (fa x')\<close> and
      \<open>(x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>(xa, x'a) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f nat_rel\<close> and
      \<open>x'a = (x1d, x2d)\<close> and
      \<open>xa = (x1e, x2e)\<close>
    for f fa x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e
  proof -
    show ?thesis
      by (rule H) (use that in auto)
  qed
  have f': \<open>f (x2e, x1c, xsa) \<le> \<Down> Id (fa (x2d, x1a, xsaa))\<close>
    if
      H: \<open>\<And>x x'.
	  (x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel) \<Longrightarrow>
	  f x \<le> \<Down> Id (fa x')\<close> and
      \<open>(x, x') \<in> nat_rel \<times>\<^sub>f (nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel)\<close> and
      \<open>x2 = (x1a, x2a)\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x2b = (x1c, x2c)\<close> and
      \<open>x = (x1b, x2b)\<close> and
      \<open>(xa, x'a) \<in> \<langle>Id\<rangle>list_rel \<times>\<^sub>f nat_rel\<close> and
      \<open>x'a = (x1d, x2d)\<close> and
      \<open>xa = (x1e, x2e)\<close> and
      \<open>(xsa, xsaa) \<in> Id\<close>
    for f fa x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e xsa xsaa
  proof -
    show ?thesis
      by (rule H) (use that in auto)
  qed
  show ?thesis
    unfolding quicksort_def quicksort_ref_def
    apply (refine_vcg pre
      partition_between_ref_partition_between'[THEN fref_to_Down_curry2])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule f; assumption)
    apply (rule f'; assumption)
    done
qed


definition quicksort_impl :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>quicksort_impl = quicksort_ref (<) id\<close>

term quicksort_impl
(*
value quicksort_impl
value \<open>quicksort_impl (0::nat) (3::nat) [0,1,2,3::nat]\<close>
*)

sepref_register quicksort quicksort_impl

sepref_definition quicksort_code
  is \<open>uncurry2 (quicksort_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding quicksort_impl_def quicksort_ref_def
  unfolding partition_between_impl_def[symmetric]
  by sepref

declare quicksort_code.refine[sepref_fr_rules]


definition full_quicksort where
  \<open>full_quicksort R h xs = (if List.null xs then RETURN xs else quicksort R h 0 (length xs - 1) xs)\<close>

definition full_quicksort_ref where
  \<open>full_quicksort_ref R h xs =
    (if List.null xs then RETURN xs else quicksort_ref R h 0 (length xs - 1) xs)\<close>


definition full_quicksort_impl :: \<open>nat list \<Rightarrow> nat list nres\<close> where
  \<open>full_quicksort_impl xs = full_quicksort_ref (<) id xs\<close>


lemma full_quicksort_ref_full_quicksort:
  \<open>(full_quicksort_ref R h, full_quicksort R h) \<in>
    \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding full_quicksort_ref_def full_quicksort_def
  by (intro frefI nres_relI)
     (auto intro!: quicksort_ref_quicksort[unfolded Down_id_eq]
       simp: List.null_def)

sepref_definition full_quicksort_code
  is \<open>full_quicksort_impl\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding full_quicksort_impl_def full_quicksort_ref_def quicksort_impl_def[symmetric] List.null_def
  by sepref

lemma sublist_length_eq: \<open>xs \<noteq> [] \<Longrightarrow> sublist xs 0 (length xs - Suc 0) = xs\<close>
  unfolding sublist_def
  by simp

lemma sorted_sublist_sorted: \<open>xs \<noteq> [] \<Longrightarrow> sorted_sublist xs 0 (length xs - 1) \<Longrightarrow> sorted xs\<close>
  apply (simp add: sorted_sublist_def)
  by (simp add: sublist_length_eq)

lemma sorted_sublist_sorted': \<open>xs \<noteq> [] \<Longrightarrow> mset xs = mset xs' \<Longrightarrow> sorted_sublist xs' 0 (length xs - Suc 0) \<Longrightarrow> sorted xs'\<close>
  apply (rule sorted_sublist_sorted)
   apply auto
  apply (rewrite Multiset.mset_eq_length)
   apply auto
  done

export_code \<open>nat_of_integer\<close> \<open>integer_of_nat\<close> \<open>partition_between_code\<close> \<open>full_quicksort_code\<close> in SML_imp module_name IsaQuicksort file "code/quicksort.sml"

lemma full_quicksort:
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs' \<and> sorted xs'))\<close>
  unfolding full_quicksort_def List.null_def
  apply (auto split: if_splits)
  apply (rule order_trans)
   apply (rule quicksort_between_mset_eq)
     apply (auto simp add: sorted_sublist_sorted')
  done

end
