theory WB_Sort
  imports
    Watched_Literals.WB_More_Refinement
begin

sledgehammer_params [provers= cvc4 spass z3 e]


text \<open>Every element between \<^term>\<open>lo\<close> and \<^term>\<open>hi\<close> can be chosen as pivot element.\<close>
definition choose_pivot :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>choose_pivot _ _ _ lo hi = SPEC(\<lambda>k. k \<ge> lo \<and> k \<le> hi)\<close>

text \<open>The element at index \<open>p\<close> partitions the subarray \<open>lo..hi\<close>. This means that every element \<close>
definition isPartition_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_wrt R xs lo hi p \<equiv> (\<forall> i. i \<ge> lo \<and> i < p \<longrightarrow> R (xs!i) (xs!p)) \<and> (\<forall> j. j > p \<and> j \<le> hi \<longrightarrow> R (xs!p) (xs!j))\<close>

definition isPartition :: \<open>'a :: order list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition xs lo hi p \<equiv> isPartition_wrt (\<le>) xs lo hi p\<close>

abbreviation isPartition_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_map R h xs i j k \<equiv> isPartition_wrt (\<lambda>a b. R (h a) (h b)) xs i j k\<close>

lemma isPartition_map_def':
  \<open>lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> isPartition_map R h xs lo hi p = isPartition_wrt R (map h xs) lo hi p\<close>
  by (auto simp add: isPartition_wrt_def conjI)


text \<open>Example: 6 is the pivot element (with index 4); \<open>7\<close> is equal to the length - 1.\<close>
lemma \<open>isPartition [0,5,3,4,6,9,8,10::nat] 0 7 4\<close>
  by (auto simp add: isPartition_def isPartition_wrt_def nth_Cons')



definition sublist :: \<open>'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
\<open>sublist xs i j \<equiv> take (Suc j - i) (drop i xs)\<close>

value \<open>sublist [0,1,2,3::nat] 1 3\<close>
value \<open>sublist [0::nat] 0 0\<close>

lemma sublist_single: \<open>i < length xs \<Longrightarrow> sublist xs i i = [xs!i]\<close>
  by (simp add: sublist_def Hash_Map.take_Suc0(2))

lemma insert_eq: \<open>insert a b = b \<union> {a}\<close>
  by auto

lemma sublist_nth: \<open>\<lbrakk>lo \<le> hi; hi < length xs; k+lo \<le> hi\<rbrakk> \<Longrightarrow> (sublist xs lo hi)!k = xs!(lo+k)\<close>
  by (simp add: sublist_def)

lemma sublist_length: \<open>\<lbrakk>i \<le> j; j < length xs\<rbrakk> \<Longrightarrow> length (sublist xs i j) = 1 + j - i\<close>
  by (simp add: sublist_def)

lemma sublist_not_empty: \<open>\<lbrakk>i \<le> j; j < length xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> sublist xs i j \<noteq> []\<close>
  apply simp
  apply (rewrite List.length_greater_0_conv[symmetric])
  apply (rewrite sublist_length)
  by auto


lemma sublist_swap: \<open>lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> i+lo \<le> hi \<Longrightarrow> j+lo \<le> hi \<Longrightarrow> sublist (swap xs i j) lo hi = swap (sublist xs lo hi)  (lo+i) (lo+j)\<close>
  apply (simp add: sublist_def swap_def)
  nitpick sledgehammer
  oops


lemma sublist_app: \<open>\<lbrakk>i1 \<le> i2; i2 \<le> i3\<rbrakk> \<Longrightarrow> sublist xs i1 i2 @ sublist xs (Suc i2) i3 = sublist xs i1 i3\<close>
  unfolding sublist_def
  by (smt Suc_eq_plus1_left Suc_le_mono append.assoc le_SucI le_add_diff_inverse le_trans same_append_eq take_add)

definition sorted_sublist_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_wrt R xs lo hi = sorted_wrt R (sublist xs lo hi)\<close>

definition sorted_sublist :: \<open>'a :: linorder list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist xs lo hi = sorted_sublist_wrt (\<le>) xs lo hi\<close>

abbreviation sorted_sublist_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_map R h xs lo hi \<equiv> sorted_sublist_wrt (\<lambda>a b. R (h a) (h b)) xs lo hi\<close>

lemma sorted_sublist_map_def':
  \<open>lo < length xs \<Longrightarrow> sorted_sublist_map R h xs lo hi \<equiv> sorted_sublist_wrt R (map h xs) lo hi\<close>
  apply (simp add: sorted_sublist_wrt_def)
  by (simp add: drop_map sorted_wrt_map sublist_def take_map)

lemma sorted_sublist_wrt_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_wrt R xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_def sublist_single)

lemma sorted_sublist_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist xs i i\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_refl)

lemma sorted_sublist_map_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_map R h xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_refl)




lemma sublist_map: \<open>sublist (map f xs) i j = map f (sublist xs i j)\<close>
  apply (auto simp add: sublist_def)
  by (simp add: drop_map take_map)


lemma take_set: \<open>j \<le> length xs \<Longrightarrow> x \<in> set (take j xs) \<equiv> (\<exists> k. k < j \<and> xs!k = x)\<close>
  apply (induction xs)
   apply simp
  by (meson in_set_conv_iff less_le_trans)

lemma drop_set: \<open>j \<le> length xs \<Longrightarrow> x \<in> set (drop j xs) \<equiv> (\<exists>k. j\<le>k\<and>k<length xs \<and> xs!k=x)\<close>
  by (smt Misc.in_set_drop_conv_nth) (* lemma found by sledgehammer *)

lemma sublist_el: \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. k < Suc j-i \<and> xs!(i+k)=x)\<close>
  apply (simp add: sublist_def)
  by (auto simp add: take_set)

lemma sublist_el': \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. i\<le>k\<and>k\<le>j \<and> xs!k=x)\<close>
  apply (simp add: sublist_el)
  by (smt Groups.add_ac(2) le_add1 le_add_diff_inverse less_Suc_eq less_diff_conv nat_less_le order_refl)


lemma sublist_lt: \<open>hi < lo \<Longrightarrow> sublist xs lo hi = []\<close>
  by (auto simp add: sublist_def)

lemma nat_le_eq_or_lt: \<open>(a :: nat) \<le> b = (a = b \<or> a < b)\<close>
  by linarith


lemma sorted_sublist_wrt_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (auto simp add: nat_le_eq_or_lt)
  unfolding sorted_sublist_wrt_def
  subgoal apply (rewrite sublist_single) by auto
  subgoal by (auto simp add: sublist_lt)
  done




text \<open>Elements in a sorted sublists are actually sorted\<close>
lemma sorted_sublist_wrt_nth_le:
  assumes \<open>sorted_sublist_wrt R xs lo hi\<close> and \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
    \<open>lo \<le> i\<close> and \<open>i < j\<close> and \<open>j \<le> hi\<close>
  shows \<open>R (xs!i) (xs!j)\<close>
proof -
  have A: \<open>lo < length xs\<close> using assms(2) assms(3) by linarith
  obtain i' where I: \<open>i = lo + i'\<close> using assms(4) le_Suc_ex by auto
  obtain j' where J: \<open>j = lo + j'\<close> by (meson assms(4) assms(5) dual_order.trans le_iff_add less_imp_le_nat)
  show ?thesis
    using assms(1) apply (simp add: sorted_sublist_wrt_def I J)
    apply (rewrite sublist_nth[symmetric, where k=i', where lo=lo, where hi=hi])
    using assms apply auto subgoal using I by linarith
    apply (rewrite sublist_nth[symmetric, where k=j', where lo=lo, where hi=hi])
    using assms apply auto subgoal using J by linarith
    apply (rule sorted_wrt_nth_less)
    apply auto
    subgoal using I J nat_add_left_cancel_less by blast
    subgoal apply (simp add: sublist_length) using J by linarith
    done
qed

lemma sorted_sublist_map_nth_le:
  assumes \<open>sorted_sublist_map R h xs lo hi\<close> and \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
    \<open>lo \<le> i\<close> and \<open>i < j\<close> and \<open>j \<le> hi\<close>
  shows \<open>R (h (xs!i)) (h (xs!j))\<close>
proof -
  show ?thesis
    using assms by (rule sorted_sublist_wrt_nth_le)
qed



lemma sorted_sublist_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist xs lo hi\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_le)

lemma sorted_sublist_map_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist_map R h xs lo hi\<close>
  by (auto simp add: sorted_sublist_wrt_le)

lemma sublist_cons: \<open>lo < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo hi = xs!lo # sublist xs (Suc lo) hi\<close>
  apply (simp add: sublist_def)
  by (metis Cons_nth_drop_Suc Suc_diff_le le_trans less_imp_le_nat not_le take_Suc_Cons)

lemma sorted_sublist_wrt_cons':
  \<open>sorted_sublist_wrt R xs (lo+1) hi \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> (\<forall>j. lo<j\<and>j\<le>hi \<longrightarrow> R (xs!lo) (xs!j)) \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (simp add: sorted_sublist_wrt_def)
  apply (auto simp add: nat_le_eq_or_lt)
  subgoal by (simp add: sublist_single)
  apply (auto simp add: sublist_cons sublist_el)
  by (metis Suc_lessI ab_semigroup_add_class.add.commute less_add_Suc1 less_diff_conv)

lemma sorted_sublist_wrt_cons:
  assumes trans: \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z)\<close> and
    \<open>sorted_sublist_wrt R xs (lo+1) hi\<close> and
    \<open>lo \<le> hi\<close> and \<open>hi < length xs \<close> and \<open>R (xs!lo) (xs!(lo+1))\<close>
  shows \<open>sorted_sublist_wrt R xs lo hi\<close>
proof -
  show ?thesis
    apply (rule sorted_sublist_wrt_cons') using assms apply auto
    subgoal premises assms' for j
    proof -
      have A: \<open>j=lo+1 \<or> j>lo+1\<close> using assms'(5) by linarith
      show ?thesis
        using A proof
        assume A: \<open>j=lo+1\<close> show ?thesis
          by (simp add: A assms')
      next
        assume A: \<open>j>lo+1\<close> show ?thesis
          apply (rule trans)
          apply (rule assms(5))
          apply (rule sorted_sublist_wrt_nth_le[OF assms(2), where i=\<open>lo+1\<close>, where j=j])
          subgoal using A assms'(6) by linarith
          subgoal using assms'(3) less_imp_diff_less by blast
          subgoal using assms'(5) by auto
          subgoal using A by linarith
          subgoal by (simp add: assms'(6))
          done
      qed
    qed
    done
qed

lemma sorted_sublist_map_cons:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    sorted_sublist_map R h xs (lo+1) hi \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> R (h (xs!lo)) (h (xs!(lo+1))) \<Longrightarrow> sorted_sublist_map R h xs lo hi\<close>
  by (blast intro: sorted_sublist_wrt_cons)


lemma sublist_snoc: \<open>lo < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo hi = sublist xs lo (hi-1) @ [xs!hi]\<close>
  apply (simp add: sublist_def)
proof -
  assume a1: "lo < hi"
  assume "hi < length xs"
  then have "take lo xs @ take (Suc hi - lo) (drop lo xs) = (take lo xs @ take (hi - lo) (drop lo xs)) @ [xs ! hi]"
    using a1 by (metis (no_types) Suc_diff_le add_Suc_right hd_drop_conv_nth le_add_diff_inverse less_imp_le_nat take_add take_hd_drop)
  then show "take (Suc hi - lo) (drop lo xs) = take (hi - lo) (drop lo xs) @ [xs ! hi]"
    by simp
qed

lemma sorted_sublist_wrt_snoc':
  \<open>sorted_sublist_wrt R xs lo (hi-1) \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> (\<forall>j. lo\<le>j\<and>j<hi \<longrightarrow> R (xs!j) (xs!hi)) \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (simp add: sorted_sublist_wrt_def)
  apply (auto simp add: nat_le_eq_or_lt)
  subgoal by (simp add: sublist_single)
  apply (auto simp add: sublist_snoc sublist_el sorted_wrt_append)
  by (metis less_diff_conv linorder_neqE_nat linordered_field_class.sign_simps(2) not_add_less1)


lemma sorted_sublist_wrt_snoc:
  assumes trans: \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z)\<close> and
    \<open>sorted_sublist_wrt R xs lo (hi-1)\<close> and
    \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and \<open>(R (xs!(hi-1)) (xs!hi))\<close>
  shows \<open>sorted_sublist_wrt R xs lo hi\<close>
proof -
  show ?thesis
    apply (rule sorted_sublist_wrt_snoc') using assms apply auto
    subgoal premises assms' for j
    proof -
      have A: \<open>j=hi-1 \<or> j<hi-1\<close> using assms'(6) by linarith
      show ?thesis
        using A proof
        assume A: \<open>j=hi-1\<close> show ?thesis
          by (simp add: A assms')
      next
        assume A: \<open>j<hi-1\<close> show ?thesis
          apply (rule trans)
           apply (rule sorted_sublist_wrt_nth_le[OF assms(2), where i=j, where j=\<open>hi-1\<close>])
               prefer 6
               apply (rule assms(5))
              apply auto
          subgoal using A assms'(5) by linarith
          subgoal using assms'(3) less_imp_diff_less by blast
          subgoal using assms'(5) by auto
          subgoal using A by linarith
          done
      qed
    qed
    done
qed

lemma sorted_sublist_map_snoc:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    sorted_sublist_map R h xs lo (hi-1) \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> (R (h (xs!(hi-1))) (h (xs!hi))) \<Longrightarrow> sorted_sublist_map R h xs lo hi\<close>
  by (blast intro: sorted_sublist_wrt_snoc)



lemma sublist_split: \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo p @ sublist xs (p+1) hi = sublist xs lo hi\<close>
  apply (auto simp add: sublist_def)
  by (smt Suc_leI append_assoc append_eq_append_conv diff_Suc_Suc drop_take_drop_drop le_SucI le_trans nat_less_le) (* Proof by sledgehammer!!! *)

lemma sublist_split_part: \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo (p-1) @ xs!p # sublist xs (p+1) hi = sublist xs lo hi\<close>
  apply (auto simp add: sublist_split[symmetric])
  apply (rewrite sublist_snoc[where xs=xs,where lo=lo,where hi=p])
  by auto


text \<open>A property for partitions (we always assume that \<^term>\<open>R\<close> is transitive.\<close>
lemma isPartition_wrt_trans:
\<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow>
  isPartition_wrt R xs lo hi p \<Longrightarrow>
  (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j))\<close>
  by (auto simp add: isPartition_wrt_def)

lemma isPartition_map_trans:
\<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  isPartition_map R h xs lo hi p \<Longrightarrow>
  (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (h (xs!i)) (h (xs!j)))\<close>
  by (auto simp add: isPartition_wrt_def)


lemma merge_sorted_wrt_partitions_between':
  \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow>
    (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j)) \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  apply (auto simp add: isPartition_def isPartition_wrt_def sorted_sublist_def sorted_sublist_wrt_def sublist_map)
  apply (simp add: sublist_split_part[symmetric])
  apply (auto simp add: List.sorted_wrt_append)
  subgoal by (auto simp add: sublist_el)
  subgoal by (auto simp add: sublist_el)
  subgoal by (auto simp add: sublist_el')
  done

lemma merge_sorted_wrt_partitions_between:
  \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  by (simp add: merge_sorted_wrt_partitions_between' isPartition_wrt_trans)



lemma merge_sorted_map_partitions_between:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_map R h xs lo hi p \<Longrightarrow>
    sorted_sublist_map R h xs lo (p-1) \<Longrightarrow> sorted_sublist_map R h xs (p+1) hi \<Longrightarrow>
    sorted_sublist_map R h xs lo hi\<close>
  by (simp add: merge_sorted_wrt_partitions_between' isPartition_map_trans)

  


text \<open>The main theorem to merge sorted lists\<close>
lemma merge_sorted_wrt_partitions:
  \<open>lo \<le> hi \<Longrightarrow> lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow>
    (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j)) \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  subgoal premises assms
  proof -
    have C: \<open>lo=p\<and>p=hi \<or> lo=p\<and>p<hi \<or> lo<p\<and>p=hi \<or> lo<p\<and>p<hi\<close>
      using assms by linarith
    show ?thesis
      using C apply auto
      subgoal \<comment> \<open>lo=p=hi\<close>
        apply (rule sorted_sublist_wrt_refl)
        using assms by auto
      subgoal \<comment> \<open>lo=p<hi\<close>
        using assms by (simp add: isPartition_def isPartition_wrt_def sorted_sublist_wrt_cons')
      subgoal \<comment> \<open>lo<p=hi\<close>
        using assms by (simp add: isPartition_def isPartition_wrt_def sorted_sublist_wrt_snoc')
      subgoal \<comment> \<open>lo<p<hi\<close>
        using assms
        apply (rewrite merge_sorted_wrt_partitions_between'[where p=p])
        by auto
      done
  qed
  done

theorem merge_sorted_map_partitions:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_map R h xs lo hi p \<Longrightarrow>
    sorted_sublist_map R h xs lo (p-1) \<Longrightarrow> sorted_sublist_map R h xs (p+1) hi \<Longrightarrow>
    sorted_sublist_map R h xs lo hi\<close>
  apply (rule merge_sorted_wrt_partitions) apply auto
  by (simp add: merge_sorted_wrt_partitions isPartition_map_trans)


lemma partition_wrt_extend:
  \<open>isPartition_wrt R xs lo' hi' p \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  lo \<le> lo' \<Longrightarrow> lo' \<le> hi \<Longrightarrow> hi' \<le> hi \<Longrightarrow>
  lo' \<le> p \<Longrightarrow> p \<le> hi' \<Longrightarrow>
  (\<And> i. lo\<le>i \<Longrightarrow> i <lo' \<Longrightarrow> R (xs!i) (xs!p)) \<Longrightarrow>
  (\<And> j. hi'<j \<Longrightarrow> j\<le>hi \<Longrightarrow> R (xs!p) (xs!j)) \<Longrightarrow>
  isPartition_wrt R xs lo hi p\<close>
  unfolding isPartition_wrt_def
  apply auto
  subgoal by (meson not_le)
  subgoal by (metis nat_le_eq_or_lt nat_le_linear)
  done

lemma partition_map_extend:
  \<open>isPartition_map R h xs lo' hi' p \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  lo \<le> lo' \<Longrightarrow> lo' \<le> hi \<Longrightarrow> hi' \<le> hi \<Longrightarrow>
  lo' \<le> p \<Longrightarrow> p \<le> hi' \<Longrightarrow>
  (\<And> i. lo\<le>i \<Longrightarrow> i <lo' \<Longrightarrow> R (h (xs!i)) (h (xs!p))) \<Longrightarrow>
  (\<And> j. hi'<j \<Longrightarrow> j\<le>hi \<Longrightarrow> R (h (xs!p)) (h (xs!j))) \<Longrightarrow>
  isPartition_map R h xs lo hi p\<close>
  by (auto simp add: partition_wrt_extend)


lemma isPartition_empty:
  \<open>(\<forall>j. lo < j \<and> j \<le> hi \<longrightarrow> R (xs ! lo) (xs ! j)) \<Longrightarrow>
  isPartition_wrt R xs lo hi lo\<close>
  by (auto simp add: isPartition_wrt_def)



lemma take_ext:
  \<open>(\<forall>i<k. xs'!i=xs!i) \<Longrightarrow>
  k < length xs \<Longrightarrow> k < length xs' \<Longrightarrow>
  take k xs' = take k xs\<close>
  by (simp add: nth_take_lemma)

lemma drop_ext':
  \<open>(\<forall>i. i\<ge>k \<and> i<length xs \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   0<k \<Longrightarrow> xs\<noteq>[] \<Longrightarrow> \<comment> \<open>These corner cases will be dealt with in the next lemma\<close>
   length xs'=length xs \<Longrightarrow>
   drop k xs' = drop k xs\<close>
  apply (rewrite in \<open>drop _ \<hole> = _\<close> List.rev_rev_ident[symmetric])
  apply (rewrite in \<open>_ = drop _ \<hole>\<close> List.rev_rev_ident[symmetric])
  apply (rewrite in \<open>\<hole> = _\<close> List.drop_rev)
  apply (rewrite in \<open>_ = \<hole>\<close> List.drop_rev)
  apply simp
  apply (rule take_ext)
  by (auto simp add: nth_rev)

lemma drop_ext:
\<open>(\<forall>i. i\<ge>k \<and> i<length xs \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs'=length xs \<Longrightarrow>
   drop k xs' = drop k xs\<close>
  apply (cases xs)
   apply auto
  apply (cases k)
  subgoal  by (simp add: nth_equalityI)
  subgoal apply (rule drop_ext') by auto
  done


lemma sublist_ext':
  \<open>(\<forall>i. lo\<le>i\<and>i\<le>hi \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs' = length xs \<Longrightarrow>
   lo \<le> hi \<Longrightarrow> Suc hi < length xs \<Longrightarrow>
   sublist xs' lo hi = sublist xs lo hi\<close>
  apply (simp add: sublist_def)
  apply (rule take_ext)
  by auto


lemma lt_Suc: \<open>(a < b) = (Suc a = b \<or> Suc a < b)\<close>
  by auto

lemma sublist_until_end_eq_drop: \<open>Suc hi = length xs \<Longrightarrow> sublist xs lo hi = drop lo xs\<close>
  by (simp add: sublist_def)

lemma sublist_ext:
  \<open>(\<forall>i. lo\<le>i\<and>i\<le>hi \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs' = length xs \<Longrightarrow>
   lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
   sublist xs' lo hi = sublist xs lo hi\<close>
  apply (auto simp add: lt_Suc[where a=hi])
  subgoal by (auto simp add: sublist_until_end_eq_drop drop_ext)
  subgoal by (auto simp add: sublist_ext')
  done

lemma sorted_wrt_lower_sublist_still_sorted:
  assumes \<open>sorted_sublist_wrt R xs lo (lo'-1)\<close> and
    \<open>lo \<le> lo'\<close> and \<open>lo' < length xs\<close> and
    \<open>(\<forall> i. lo\<le>i\<and>i<lo' \<longrightarrow> xs'!i=xs!i)\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_wrt R xs' lo (lo'-1)\<close>
proof -
  have l: \<open>lo < lo' - 1 \<or> lo \<ge> lo'-1\<close>
    by linarith
  show ?thesis
    using l apply auto
    subgoal \<comment> \<open>lo < lo' - 1\<close>
      apply (auto simp add: sorted_sublist_wrt_def)
      apply (rewrite sublist_ext[where xs=xs])
      using assms by (auto simp add: sorted_sublist_wrt_def)
    subgoal \<comment> \<open>lo >= lo' - 1\<close>
      using assms by (auto simp add: sorted_sublist_wrt_le)
    done
qed

lemma sorted_map_lower_sublist_still_sorted:
  assumes \<open>sorted_sublist_map R h xs lo (lo'-1)\<close> and
    \<open>lo \<le> lo'\<close> and \<open>lo' < length xs\<close> and
    \<open>(\<forall> i. lo\<le>i\<and>i<lo' \<longrightarrow> xs'!i=xs!i)\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_map R h xs' lo (lo'-1)\<close>
  using assms by (rule sorted_wrt_lower_sublist_still_sorted)

lemma sorted_wrt_upper_sublist_still_sorted:
  assumes \<open>sorted_sublist_wrt R xs (hi'+1) hi\<close> and
    \<open>lo \<le> lo'\<close> and \<open>hi < length xs\<close> and
    \<open>\<forall> j. hi'<j\<and>j\<le>hi \<longrightarrow> xs'!j=xs!j\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_wrt R xs' (hi'+1) hi\<close>
proof -
  have l: \<open>hi' + 1 < hi \<or> hi' + 1 \<ge> hi\<close>
    by linarith
  show ?thesis
    using l apply auto
    subgoal \<comment> \<open>hi' + 1 < h\<close>
      apply (auto simp add: sorted_sublist_wrt_def)
      apply (rewrite sublist_ext[where xs=xs])
      using assms by (auto simp add: sorted_sublist_wrt_def)
    subgoal \<comment> \<open>hi' + 1 \<ge> hi\<close>
      using assms by (auto simp add: sorted_sublist_wrt_le)
    done
qed

lemma sorted_map_upper_sublist_still_sorted:
  assumes \<open>sorted_sublist_map R h xs (hi'+1) hi\<close> and
    \<open>lo \<le> lo'\<close> and \<open>hi < length xs\<close> and
    \<open>\<forall> j. hi'<j\<and>j\<le>hi \<longrightarrow> xs'!j=xs!j\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_map R h xs' (hi'+1) hi\<close>
  using assms by (rule sorted_wrt_upper_sublist_still_sorted)



text \<open>The specification of the partition function\<close>
definition partition_spec :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>partition_spec R h xs lo hi xs' p \<equiv>
    mset xs' = mset xs \<and> \<comment> \<open>The list is a permutation\<close>
    mset (sublist xs' lo hi) = mset (sublist xs lo hi) \<and> \<comment> \<open>The sublist is a permutation\<close>
    isPartition_map R h xs' lo hi p \<and> \<comment> \<open>We have a valid partition on the resulting list\<close>
    lo \<le> p \<and> p \<le> hi \<and> \<comment> \<open>The partition index is in bounds\<close>
    (\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i) \<and> (\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i)\<close> \<comment> \<open>Everything else is unchanged.\<close>


text \<open>Maybe this part is redundant\<close>
lemma
    \<open>mset xs' = mset xs \<and>
    (\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i) \<and> (\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
    mset (sublist xs' lo hi) = mset (sublist xs lo hi)\<close>
  apply (auto simp add: sublist_def)
  oops


value \<open>take 1 [a,b,c]\<close>

lemma take_eq_set':
  assumes \<open>k < length xs\<close> and
    \<open>set xs' = set xs\<close> and
    \<open>\<forall> j. j < k \<longrightarrow> xs'!j = xs!j\<close>
    \<open>x \<in> set (take k xs')\<close>
  shows \<open>x \<in> set (take k xs)\<close>
  by (metis WB_Sort.take_set assms(1) assms(3) assms(4) in_set_conv_iff less_imp_le_nat)

lemma take_eq_set: 
  assumes
    \<open>set xs' = set xs\<close> and \<open>length xs' = length xs\<close> and
    \<open>\<forall> j. j < k \<longrightarrow> xs'!j = xs!j\<close> and
    \<open>x \<in> set (take k xs')\<close>
  shows \<open>x \<in> set (take k xs)\<close>
proof -
  consider
    (a) \<open>k < length xs\<close> |
    (b) \<open>length xs \<le> k\<close> by linarith
  then show ?thesis
  proof cases
    case a
    then show ?thesis
      using assms(1,3,4) by (rule take_eq_set')
  next
    case b
    then show ?thesis
      using assms by simp
  qed
qed

value \<open>drop 4 [a,b,c,d,e,f]\<close>

(* Actually, I only need that \<open>set (sublist xs' lo hi) = set (sublist xs lo hi)\<close> *)
lemma
  assumes \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
    \<open>mset xs' = mset xs\<close> and
    E1: \<open>\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i\<close> and E2: \<open>\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i\<close> and
    A: \<open>x \<in> set (sublist xs' lo hi)\<close>
  shows \<open>x \<in> set (sublist xs lo hi)\<close>
proof -
  have L0: \<open>set xs' = set xs\<close> by (metis assms(3) set_mset_mset)
  have L1: \<open>length xs' = length xs\<close> by (metis assms(3) size_mset)
  have L2: \<open>lo < length xs\<close> using assms(1,2) by linarith
  have L3: \<open>lo < length xs'\<close> using L1 L2 by simp

(*
  have \<open>\<exists>k. lo\<le>k\<and>k\<le>hi \<and> xs'!k=x\<close>
    by (metis assms(1) assms(2) assms(3) assms(6) mset_eq_length sublist_el')
  then obtain k where X: \<open>lo\<le>k\<close> \<open>k\<le>hi\<close> \<open>xs'!k=x\<close> by blast
  have \<open>\<exists>k'. xs!k'=x\<close>
    by (metis X(2) X(3) assms(2) assms(3) in_set_conv_nth less_le_trans mset_eq_setD nat_less_le size_mset)
  then obtain k' where Y: \<open>xs!k'=x\<close> by blast
*)

  have Z: \<open>set (drop lo xs') = set (drop lo xs)\<close>
    nitpick
    sorry
  
  then show ?thesis
    apply (simp add: sublist_def)
    using Z apply (rule take_eq_set[where xs'=\<open>drop lo xs'\<close>]) apply auto
    subgoal using L1 by auto
    subgoal nitpick done
    subgoal using A by (auto simp add: sublist_def[symmetric])
    done
oops
    



(*
  have \<open>\<exists>k''. lo\<le>k''\<and>k''\<le>hi \<and> xs!k''=x\<close>
  proof
    assume \<open>\<not> (\<exists>k''. lo\<le>k''\<and>k''\<le>hi \<and> xs!k''=x)\<close>
    then have \<open>\<forall>k''. lo\<le>k''\<and>k''\<le>hi \<longrightarrow> xs!k''\<noteq>x\<close> by blast
    then have \<open>\<forall>k''. xs!k''=x \<longrightarrow> \<not>(lo\<le>k''\<and>k''\<le>hi)\<close> by blast
    then have \<open>\<not> (lo\<le>k'\<and>k'\<le>hi)\<close> using Y by blast
    


  then show ?thesis
    sorry
qed
*)


text \<open>Our abstract recursive quicksort procedure. We abstract over a partition procedure.\<close>
definition quicksort :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h lo hi xs0 = do {
  RECT (\<lambda>f (lo,hi,xs). do {
      (xs, p) \<leftarrow> SPEC(uncurry (partition_spec R h xs lo hi)); \<comment> \<open>Abstract partition function\<close>
      xs \<leftarrow> (if p-1\<le>lo then RETURN xs else f (lo, p-1, xs));
      if hi\<le>p+1 then RETURN xs else f (p+1, hi, xs)
    })
    (lo, hi, xs0)
  }\<close>


text \<open>The invariant/precondition of the recursive calls of quicksort.\<close>

definition quicksort_inv :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>quicksort_inv R h xs lo hi lo' hi' xs' \<equiv>
    lo \<le> lo' \<and> lo' \<le> hi' \<and> hi' \<le> hi \<and>
    mset xs = mset xs' \<and>
    sorted_sublist_map R h xs' lo (lo'-1) \<and> sorted_sublist_map R h xs' (hi'+1) hi \<and>
    (\<forall> i j. lo \<le> i \<and> i < lo' \<and> lo' \<le> j \<and> j \<le> hi \<longrightarrow> R (h (xs'!i)) (h (xs'!j))) \<and> \<comment> \<open>All elements below lo' are smaller than the rest to the right\<close>
    (\<forall> i j. i > hi' \<and> i \<le> hi \<and> j  \<ge> lo' \<and> j \<le> hi \<longrightarrow> R (h (xs'!j)) (h (xs'!i)))\<close> \<comment> \<open>All elements over hi' are bigger than the rest to the right\<close>


text \<open>The first case for the correctness proof of quicksort: \<^term>\<open>p-1 \<le> lo'\<close> and \<^term>\<open>hi'\<le>p+1\<close>.\<close>
lemma quicksort_correct_case1:
  assumes
    trans: \<open>\<And>x y z. R (h x) (h y) \<Longrightarrow> R (h y) (h z) \<Longrightarrow> R (h x) (h z)\<close> and
    pre0: \<open>hi < length xs\<close> and
    inv: \<open>quicksort_inv R h xs lo hi lo' hi' xs'\<close> and
    if1: \<open>p-1 \<le> lo'\<close> and if2: \<open>hi'\<le>p+1\<close> and \<comment> \<open>From the "if"s\<close>
    part: \<open>partition_spec R h xs' lo' hi' xs'' p\<close>
  shows \<open>sorted_sublist_map R h xs'' lo hi\<close>
proof -
  text \<open>First, we need to "unfold" the assumptions\<close>
  have inv1: \<open>lo \<le> lo'\<close> and inv2: \<open>lo' \<le> hi'\<close> and inv3: \<open>hi' \<le> hi\<close> and
    inv4: \<open>mset xs = mset xs'\<close> and
    inv5: \<open>sorted_sublist_map R h xs' lo (lo'-1)\<close> and inv5': \<open>sorted_sublist_map R h xs' (hi'+1) hi\<close> and
    inv6: \<open>(\<forall> i j. lo \<le> i \<and> i < lo' \<and> lo' \<le> j \<and> j \<le> hi \<longrightarrow> R (h (xs'!i)) (h (xs'!j)))\<close> and
    inv7: \<open>(\<forall> i j. i > hi' \<and> i \<le> hi \<and> j  \<ge> lo' \<and> j \<le> hi \<longrightarrow> R (h (xs'!j)) (h (xs'!i)))\<close>
    using inv unfolding quicksort_inv_def by auto
  have part1: \<open>mset xs'' = mset xs'\<close> and
    part1': \<open>mset (sublist xs'' lo' hi') = mset (sublist xs' lo' hi')\<close> and
    part2: \<open>isPartition_map R h xs'' lo' hi' p\<close> and
    part3: \<open>lo' \<le> p\<close> and part4: \<open>p \<le> hi'\<close> and
    part5: \<open>(\<forall> i. i<lo' \<longrightarrow> xs''!i=xs'!i)\<close> and part6: \<open>(\<forall> i. hi'<i\<and>i<length xs'' \<longrightarrow> xs''!i=xs'!i)\<close>
    using part unfolding partition_spec_def by auto

  text \<open>A bit arithmetic with sledgehammer\<dots>\<close>
  have A: \<open>lo \<le> hi\<close> using inv1 inv2 inv3 by linarith
  have B: \<open>lo < length xs\<close> using A pre0 by linarith
  have C: \<open>lo \<le> p\<close> using inv1 part3 by linarith
  have D: \<open>p \<le> hi\<close> using inv1 part3 part4 inv3 by linarith
  have E: \<open>hi < length xs''\<close> using pre0 inv4 part1 by (metis size_mset)
  have F: \<open>lo < length xs''\<close> using A E by linarith
  have G: \<open>lo' < length xs'\<close> using mset_eq_length pre0 inv2 inv3 inv4 by fastforce
  have H: \<open>length xs'' = length xs'\<close> using mset_eq_length part1 by auto
  have I: \<open>lo' < length xs''\<close> by (simp add: G H)
  have J: \<open>hi' < length xs''\<close> using inv3 E H by linarith
  have K: \<open>hi < length xs'\<close> using E H by auto

  have \<open>xs''!p \<in> set (sublist xs'' lo' hi')\<close>
    by (metis E less_le_trans nat_le_eq_or_lt part3 part4 inv3 sublist_el')
  then have \<open>xs''!p \<in> set (sublist xs' lo' hi')\<close>
    by (metis part1' set_mset_mset)
  then have \<open>\<exists> p'. lo'\<le>p' \<and> p'\<le>hi' \<and> xs''!p = xs'!p'\<close>
    text \<open>This holds because the partition function permutes the sublist xs'[lo'..hi'].\<close>
    by (metis E le_less_trans part1 inv2 inv3 size_mset sublist_el')
  then obtain p' where L: \<open>lo'\<le>p'\<close> \<open>p'\<le>hi'\<close> \<open>xs''!p = xs'!p'\<close> by blast

  then have L': \<open>lo \<le> p'\<close> \<open>p' \<le> hi\<close>
    using le_trans inv1 apply blast
    using L(2) le_trans inv3 by blast

  from part6 have part6': \<open>(\<forall> i. hi'<i\<and>i\<le>hi \<longrightarrow> xs''!i=xs'!i)\<close> using E le_less_trans by blast

  show ?thesis
    apply (rule merge_sorted_map_partitions [where p=p])
    subgoal by (rule trans)
    subgoal by (rule A)
    subgoal by (rule C)
    subgoal by (rule D)
    subgoal by (rule E)

    text \<open>We have to show that \<^term>\<open>p\<close> is a partition on xs''[lo..hi].\<close>
    subgoal
      apply (rule partition_map_extend [where lo'=lo', where hi'=hi'])
      subgoal by (rule part2)
      subgoal by (rule E)
      subgoal by (rule inv1)
      subgoal using inv2 inv3 by linarith
      subgoal by (rule inv3)
      subgoal by (rule part3)
      subgoal by (rule part4)
      subgoal
        apply (rewrite in \<open>R (h \<hole>) _\<close> part5) subgoal by blast
        apply (rewrite in \<open>R _ (h \<hole>)\<close> L(3))
        by (simp add: inv6 L L')
      subgoal
        apply (rewrite in \<open>R _ (h \<hole>)\<close> part6') subgoal by blast
        apply (rewrite in \<open>R (h \<hole>) _\<close> L(3))
        by (simp add: inv7 L L')
      done

    text \<open>We have to show that \<^term>\<open>xs''\<close> is sorted from \<^term>\<open>lo\<close> to \<^term>\<open>p-1\<close>. Note that by the
          precondition, \<^term>\<open>xs'\<close> is sorted from \<^term>\<open>lo\<close> to \<^term>\<open>lo'-1\<close>.\<close>
    subgoal
    proof -
      have S: \<open>sorted_sublist_map R h xs'' lo (lo'-1)\<close>
        apply (rule sorted_wrt_lower_sublist_still_sorted [OF inv5 inv1])
          apply auto
        subgoal by (rule G)
        subgoal using part5 by blast
        subgoal by (rule H)
        done

      text \<open>We obtain the position where element \<^term>\<open>xs''!lo'\<close> was stored in \<^term>\<open>xs'\<close>.\<close>
      have \<open>xs''!lo' \<in> set (sublist xs'' lo' hi')\<close>
        by (meson J order_mono_setup.refl inv2 sublist_el')
      then have \<open>xs''!lo' \<in> set (sublist xs' lo' hi')\<close>
        by (metis part1' set_mset_mset)
      then have \<open>\<exists> lo''. lo' \<le> lo'' \<and> lo'' \<le> hi' \<and> xs''!lo' = xs'!lo''\<close>
        using H J inv2 sublist_el' by fastforce
      then obtain lo'' where M: \<open>lo' \<le> lo''\<close> \<open>lo'' \<le> hi'\<close> \<open>xs''!lo' = xs'!lo''\<close> by blast

      have Bp1: \<open>p = lo' \<or> (p = Suc lo' \<and> lo=lo') \<or> (p = Suc lo' \<and> lo < lo')\<close>
        using if1 part3 inv1 by linarith
      show ?thesis
      using Bp1 proof (elim disjE)
        assume A:\<open>p = lo'\<close> show ?thesis
          using S by (simp add: A)
      next
        assume A:\<open>p = Suc lo' \<and> lo=lo'\<close> show ?thesis
          by (simp add: A sorted_sublist_map_refl I)
      next
        assume A:\<open>p = Suc lo' \<and> lo < lo'\<close> show ?thesis
          apply (simp add: A)
          apply (rule sorted_sublist_map_snoc)
          subgoal by (rule trans)
          subgoal by (rule S)
          subgoal by (rule inv1)
          subgoal by (rule I)
          subgoal
            using inv6 apply (auto simp add:)
            using A M(1) M(2) M(3) part5 inv3 by auto
          done
      qed
    qed

    text \<open>The dual case for the right sublist from \<^term>\<open>p+1\<close> to \<^term>\<open>hi\<close>.\<close>
    subgoal
    proof -
      have S: \<open>sorted_sublist_map R h xs'' (hi'+1) hi\<close>
        apply (rule sorted_wrt_upper_sublist_still_sorted [OF inv5' inv1])
          apply auto
        subgoal by (rule K)
        subgoal using part6' by blast
        subgoal by (rule H)
        done

      text \<open>We obtain the position where element \<^term>\<open>xs''!hi'\<close> was stored in \<^term>\<open>xs'\<close>.\<close>
      have \<open>xs''!hi' \<in> set (sublist xs'' lo' hi')\<close>
        by (meson J order_mono_setup.refl inv2 sublist_el')
      then have \<open>xs''!hi' \<in> set (sublist xs' lo' hi')\<close>
        by (metis part1' set_mset_mset)
      then have \<open>\<exists> hi''. lo' \<le> hi'' \<and> hi'' \<le> hi' \<and> xs''!hi' = xs'!hi''\<close>
        using H J inv2 sublist_el' by fastforce
      then obtain hi'' where M: \<open>lo' \<le> hi''\<close> \<open>hi'' \<le> hi'\<close> \<open>xs''!hi' = xs'!hi''\<close> by blast

      have Bp2: \<open>p = hi' \<or> (p = hi'-1 \<and> hi=hi') \<or> (p = hi'-1 \<and> hi'=0) \<or> (p = hi'-1 \<and> hi > hi' \<and> hi'>0)\<close>
        using if2 part4 inv3 by linarith

      show ?thesis
      using Bp2 proof (elim disjE)
        assume A:\<open>p = hi'\<close> show ?thesis
          using S by (simp add: A)
      next
        assume A:\<open>p = hi'-1 \<and> hi=hi'\<close> show ?thesis
          using A J if2 sorted_sublist_wrt_le by blast
      next
        assume A:\<open>p = hi'-1 \<and> hi'=0\<close> show ?thesis
          using A S by auto
      next
        assume A:\<open>p = hi'-1 \<and> hi > hi' \<and> hi' > 0\<close> show ?thesis
          apply (simp add: A)
          apply (rule sorted_sublist_map_cons)
          subgoal by (rule trans)
          subgoal by (rule S)
          subgoal by (rule inv3)
          subgoal by (rule E)
          subgoal
            using inv7 apply (auto simp add:)
            using A \<open>\<exists>hi''\<ge>lo'. hi'' \<le> hi' \<and> xs'' ! hi' = xs' ! hi''\<close> part6' by auto
          done
      qed
    qed

    text \<open>All done! :-)\<close>
    done
qed


text \<open>Second part of correctness: We assume that we only called the second recursive call.\<close>
lemma quicksort_correct_case2:
  assumes
    trans: \<open>\<And>x y z. R (h x) (h y) \<Longrightarrow> R (h y) (h z) \<Longrightarrow> R (h x) (h z)\<close> and
    pre0: \<open>hi < length xs\<close> and
    inv: \<open>quicksort_inv R h xs lo hi lo' hi' xs'\<close> and
    (* if1: \<open>p-1 \<le> lo'\<close> and *) if2: \<open>hi'>p+1\<close> and \<comment> \<open>From the "if"s\<close>
    part: \<open>partition_spec R h xs' lo' hi' xs'' p\<close>
  shows \<open>quicksort_inv R h xs lo hi (Suc p) hi' xs''\<close>
proof -
  text \<open>First, we need to "unfold" the assumptions\<close>
  have inv1: \<open>lo \<le> lo'\<close> and inv2: \<open>lo' \<le> hi'\<close> and inv3: \<open>hi' \<le> hi\<close> and
    inv4: \<open>mset xs = mset xs'\<close> and
    inv5: \<open>sorted_sublist_map R h xs' lo (lo'-1)\<close> and inv5': \<open>sorted_sublist_map R h xs' (hi'+1) hi\<close> and
    inv6: \<open>(\<forall> i j. lo \<le> i \<and> i < lo' \<and> lo' \<le> j \<and> j \<le> hi \<longrightarrow> R (h (xs'!i)) (h (xs'!j)))\<close> and
    inv7: \<open>(\<forall> i j. i > hi' \<and> i \<le> hi \<and> j  \<ge> lo' \<and> j \<le> hi \<longrightarrow> R (h (xs'!j)) (h (xs'!i)))\<close>
    using inv unfolding quicksort_inv_def by auto
  have part1: \<open>mset xs'' = mset xs'\<close> and
    part1': \<open>mset (sublist xs'' lo' hi') = mset (sublist xs' lo' hi')\<close> and
    part2: \<open>isPartition_map R h xs'' lo' hi' p\<close> and
    part3: \<open>lo' \<le> p\<close> and part4: \<open>p \<le> hi'\<close> and
    part5: \<open>(\<forall> i. i<lo' \<longrightarrow> xs''!i=xs'!i)\<close> and part6: \<open>(\<forall> i. hi'<i\<and>i<length xs'' \<longrightarrow> xs''!i=xs'!i)\<close>
    using part unfolding partition_spec_def by auto

  text \<open>A bit arithmetic with sledgehammer\<dots>\<close>
  have A: \<open>lo \<le> hi\<close> using inv1 inv2 inv3 by linarith
  have B: \<open>lo < length xs\<close> using A pre0 by linarith
  have C: \<open>lo \<le> p\<close> using inv1 part3 by linarith
  have D: \<open>p \<le> hi\<close> using inv1 part3 part4 inv3 by linarith
  have E: \<open>hi < length xs''\<close> using pre0 inv4 part1 by (metis size_mset)
  have F: \<open>lo < length xs''\<close> using A E by linarith
  have G: \<open>lo' < length xs'\<close> using mset_eq_length pre0 inv2 inv3 inv4 by fastforce
  have H: \<open>length xs'' = length xs'\<close> using mset_eq_length part1 by auto
  have I: \<open>lo' < length xs''\<close> by (simp add: G H)
  have J: \<open>hi' < length xs''\<close> using inv3 E H by linarith
  have K: \<open>hi < length xs'\<close> using E H by auto

  show ?thesis
    unfolding quicksort_inv_def
    apply (intro conjI)
    subgoal
      by (simp add: C le_SucI)
    subgoal
      using if2 part3 by linarith
    subgoal
      using inv3 by linarith
    subgoal
      by (simp add: inv4 part1)
    subgoal
      sorry (* TODO *)
    subgoal
      sorry (* TODO *)
    subgoal
      sorry (* TODO *)
    subgoal
      sorry (* TODO *)
    done
qed
    



(* TODO:
- lemmas that show that the preconditions still hold after a recursive call of quicksort
- apply lemmas in correctness lemma
- use \<open>transp\<close> (But what about linearity/conexity?)
*)
term transp

lemma quicksort_correct:
  assumes \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
  trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> (* and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> *)
  shows \<open>quicksort R h lo hi xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs' \<and> sorted_sublist_map R h xs' lo hi))\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
 
  have pre: \<open>(\<lambda>(lo',hi',xs'). quicksort_inv R h xs lo hi lo' hi' xs')(lo,hi,xs)\<close>
    unfolding quicksort_inv_def apply simp
    by (meson assms(1) assms(2) diff_le_self dual_order.strict_trans2 lessI less_imp_le_nat not_less sorted_sublist_wrt_le)

  show ?thesis
    unfolding quicksort_def
    apply (rule RECT_rule)
       apply (refine_mono)
      apply (rule wf)
     apply (rule pre)
    subgoal premises IH for f x
      apply (refine_vcg)

      text \<open>Termination case: (p-1 \<le> lo') and (hi' \<le> p+1)\<close>
      subgoal
        using IH(2) by (simp add: quicksort_inv_def partition_spec_def)
      subgoal apply simp
        apply (rule quicksort_correct_case1 [where xs=xs and lo'=\<open>fst(x)\<close> and hi'=\<open>fst(snd x)\<close> and xs'=\<open>snd(snd x)\<close>])
        apply simp_all
        subgoal by (rule trans)
        subgoal by (rule assms(2))
        subgoal using IH(2) by simp
        done

      text \<open>Case (p-1 \<le> lo') and (hi' < p+1) (Only second recursive call)\<close>
      subgoal using IH(2) apply (auto dest: mset_eq_length)
        (* apply (subst (2) Down_id_eq[symmetric]) *)
        apply (rule IH(1)[THEN order_trans])
        text \<open>Show that the invariant holds for the recursive call\<close>
        subgoal apply simp
          apply (rule quicksort_correct_case2 [where xs=xs and xs'=\<open>snd(snd x)\<close>])
          apply simp_all
          subgoal by (rule trans)
          subgoal by (rule assms(2))
          done
        text \<open>Wellfoundness (easy)\<close>
        subgoal by (auto simp add: quicksort_inv_def partition_spec_def)
        text \<open>Show that the postcondition holds (easy)\<close>
        subgoal by auto
        done

      text \<open>Case (p-1 < lo') and (hi' < p+1) (Both recursive calls)\<close>
      subgoal using IH(2) apply (auto dest: mset_eq_length)
        apply (rule IH(1)[THEN order_trans])
        text \<open>Show that the premise holds for the first recursive call\<close>
        subgoal
          sorry (* TODO: Case 3 *)
        text \<open>Wellfoundness (easy)\<close>
        subgoal by (auto simp add: quicksort_inv_def partition_spec_def)
        apply auto
        apply (rule IH(1)[THEN order_trans])
        text \<open>Show that the premise holds for the second recursive call\<close>
        subgoal apply simp
          apply (rule quicksort_correct_case2)
          apply simp_all
          subgoal by (rule trans)
          subgoal by (rule assms(2))
          subgoal sorry (* TODO: We have to show that p is still a partition after the first function call (case 4) *)
          done
        text \<open>Wellfoundness (easy)\<close>
        subgoal by auto
        text \<open>Show that the postcondition holds (easy)\<close>
        subgoal by auto
        done

      done
    done
qed


(* TODO: Show that our (abstract) partition satisifies the specification *)


definition partition_main_inv :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat\<times>nat\<times>'a list) \<Rightarrow> bool\<close> where
  \<open>partition_main_inv R h lo hi xs0 p \<equiv>
    case p of (i,j,xs) \<Rightarrow>
    j < length xs \<and> j \<le> hi \<and> i < length xs \<and> lo \<le> i \<and> i \<le> j \<and> mset xs = mset xs0 \<and>
    (\<forall>k. k \<ge> lo \<and> k < i \<longrightarrow> R (h (xs!k)) (h (xs!hi))) \<and> \<comment> \<open>All elements from \<open>lo\<close> to \<open>i-1\<close> are smaller than the pivot\<close>
    (\<forall>k. k \<ge> i \<and> k < j \<longrightarrow>  R (h (xs!hi)) (h (xs!k))) \<and> \<comment> \<open>All elements from \<open>i\<close> to \<open>j-1\<close> are greater than the pivot\<close>
    (\<forall>k. k \<ge> j \<and> k \<le> hi \<longrightarrow> xs!k = xs0!k) \<comment> \<open>All elements from \<open>j\<close> to \<open>hi\<close> are unchanged\<close>
  \<close>

text \<open>The main part of the partition function. The pivot is assumed to be the last element. This is
exactly the "Lomuto partition scheme" partition function from Wikipedia.\<close>
definition partition_main :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_main R h lo hi xs0 = do {
    ASSERT(hi < length xs0);
    pivot \<leftarrow> RETURN (h (xs0 ! hi));
    (i,j,xs) \<leftarrow> WHILE\<^sub>T\<^bsup>partition_main_inv R h lo hi xs0\<^esup> \<comment> \<open>We loop from \<^term>\<open>j=lo\<close> to \<^term>\<open>j=hi-1\<close>.\<close>
      (\<lambda>(i,j,xs). j < hi)
      (\<lambda>(i,j,xs). do {
        ASSERT(i < length xs \<and> j < length xs);
      	if R (h (xs!j)) pivot
      	then RETURN (i+1, j+1, swap xs i j)
      	else RETURN (i,   j+1, xs)
      })
      (lo, lo, xs0); \<comment> \<open>i and j are both initialized to lo\<close>
    ASSERT(i < length xs \<and> j = hi \<and> lo \<le> i \<and> hi < length xs \<and> mset xs = mset xs0);
    RETURN (swap xs i hi, i)
  }\<close>

lemma partition_main_correct:
  assumes \<open>lo < length xs\<close> and \<open>hi < length xs\<close> and \<open>hi > lo\<close> and
    \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>partition_main R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and>
     lo \<le> p \<and> p \<le> hi \<and> isPartition_map R h xs' lo hi p)\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  have L: \<open>~ R (h x) (h y) \<Longrightarrow> R (h y) (h x)\<close> for x y \<comment> \<open>Corollary of linearity\<close>
    using assms by blast
  have M: \<open>a < Suc b \<equiv> a = b \<or> a < b\<close> for a b
    by linarith
  have N: \<open>(a::nat) \<le> b \<equiv> a = b \<or> a < b\<close> for a b
    by arith

  show ?thesis
    unfolding partition_main_def choose_pivot_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure(\<lambda>(i,j,xs). hi-j)\<close>])
    subgoal using assms by blast \<comment> \<open>We feed our assumption to the assertion\<close>
    subgoal by auto \<comment> \<open>WF\<close>
    subgoal \<comment> \<open>Invariant holds before the first iteration\<close>
      unfolding partition_main_inv_def
      using assms apply simp by linarith
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp
    subgoal
      unfolding partition_main_inv_def
      apply (auto dest: mset_eq_length)
      done
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal
      unfolding partition_main_inv_def apply (auto dest: mset_eq_length)
      apply (auto simp add: M) using assms(5) by blast

    subgoal unfolding partition_main_inv_def by simp \<comment> \<open>assertions, etc\<close>
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp

    subgoal \<comment> \<open>After the last iteration, we have a partitioning! :-)\<close>
      unfolding partition_main_inv_def by (auto simp add: isPartition_wrt_def)
    done
qed


definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h lo hi xs0 = do {
    ASSERT(lo < length xs0 \<and> hi < length xs0 \<and> hi > lo);
    k \<leftarrow> choose_pivot R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    partition_main R h lo hi xs
  }\<close>


lemma partition_between_correct:
  assumes \<open>lo < length xs\<close> and \<open>hi < length xs\<close> and \<open>hi > lo\<close> and
  \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>partition_between R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and>
     lo \<le> p \<and> p \<le> hi \<and> isPartition_map R h xs' lo hi p)\<close> \<comment> \<open>TODO: Maxi: Show that \<open>p\<close> is a valid partiton.\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg partition_main_correct)
    using assms by (auto dest: mset_eq_length)
qed



text \<open>We use the median of the first, the middle, and the last element.\<close>
definition choose_pivot3 where
  \<open>choose_pivot3 R h xs lo (hi::nat) = do {
    ASSERT(lo < length xs);
    ASSERT(hi < length xs);
    let k' = (hi - lo) div 2;
    let k = lo + k';
    ASSERT(k < length xs);
    let start = h (xs ! lo);
    let mid = h (xs ! k);
    let end = h (xs ! hi);
    if (R start mid \<and> R mid end) \<or> (R end mid \<and> R mid start) then RETURN k
    else if (R start end \<and> R end mid) \<or> (R mid end \<and> R end start) then RETURN hi
    else RETURN lo
}\<close>

\<comment> \<open>We only have to show that this procedure yields a valid index between \<open>lo\<close> and \<open>hi\<close>.\<close>
lemma choose_pivot3_choose_pivot:
  assumes \<open>lo < length xs\<close> \<open>hi < length xs\<close> \<open>hi \<ge> lo\<close>
  shows \<open>choose_pivot3 R h xs lo hi \<le> \<Down> Id (choose_pivot R h xs lo hi)\<close>
  unfolding choose_pivot3_def choose_pivot_def
  using assms by (auto intro!: ASSERT_leI simp: Let_def)

\<comment> \<open>The refined partion function: We use the above pivot function and fold instead of non-deterministic iteration.\<close>
definition partition_between_ref
  :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close>
where
  \<open>partition_between_ref R h lo hi xs0 = do {
    ASSERT(lo < length xs0 \<and> hi < length xs0 \<and> hi > lo);
    k \<leftarrow> choose_pivot3 R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    partition_main R h lo hi xs
  }\<close>


lemma partition_main_ref':
  \<open>partition_main R h lo hi xs
    \<le> \<Down> ((\<lambda> a b c d. Id) a b c d) (partition_main R h lo hi xs)\<close>
  by auto

lemma partition_between_ref_partition_between:
  \<open>partition_between_ref R h lo hi xs \<le> (partition_between R h lo hi xs)\<close>
proof -
  have swap: \<open>(swap xs k hi, swap xs ka hi) \<in> Id\<close> if \<open>k = ka\<close>
    for k ka
    using that by auto
  have [refine0]: \<open>(h (xsa ! hi), h (xsaa ! hi)) \<in> Id\<close>
    if \<open>(xsa, xsaa) \<in> Id\<close>
    for xsa xsaa
    using that by auto

  show ?thesis
    apply (subst (2) Down_id_eq[symmetric])
    unfolding partition_between_ref_def
      partition_between_def FOREACH_patterns
      LIST_FOREACH'_def[of \<open>RETURN _\<close>, unfolded nres_monad1, symmetric]
      OP_def
    apply (refine_vcg choose_pivot3_choose_pivot swap partition_main_correct)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    by (auto intro: Refine_Basic.Id_refine dest: mset_eq_length)
qed

text \<open>Technical lemma for sepref\<close>
lemma partition_between_ref_partition_between':
  \<open>(uncurry2 (partition_between_ref R h), uncurry2 (partition_between R h)) \<in>
    nat_rel \<times>\<^sub>f nat_rel \<times>\<^sub>f \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: partition_between_ref_partition_between)

text \<open>Example instantiation for pivot\<close>
definition choose_pivot3_impl where
  \<open>choose_pivot3_impl = choose_pivot3 (\<le>) id\<close>

sepref_register choose_pivot3

text \<open>Example instantiation code for pivot\<close>
sepref_definition choose_pivot3_impl_code
  is \<open>uncurry2 (choose_pivot3_impl)\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>k  *\<^sub>a  nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k\<rightarrow>\<^sub>a nat_assn\<close>
  unfolding choose_pivot3_impl_def choose_pivot3_def id_def
  by sepref

declare choose_pivot3_impl_code.refine[sepref_fr_rules]



text \<open>Example instantiation for partition_main\<close>
definition partition_main_impl where
  \<open>partition_main_impl = partition_main (\<le>) id\<close>

sepref_register partition_main_impl

text \<open>Example instantiation code for partition_main\<close>
sepref_definition partition_main_code
  is \<open>uncurry2 (partition_main_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_main_impl_def partition_main_def
  unfolding id_def
  by sepref

declare partition_main_code.refine[sepref_fr_rules]


text \<open>Example instantiation for partition\<close>
definition partition_between_impl where
  \<open>partition_between_impl = partition_between_ref (\<le>) id\<close>

sepref_register partition_between_ref

text \<open>Example instantiation code for partition\<close>
sepref_definition partition_between_code
  is \<open>uncurry2 (partition_between_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn *a nat_assn\<close>
  unfolding partition_between_ref_def partition_between_impl_def
    choose_pivot3_impl_def[symmetric] partition_main_impl_def[symmetric]
  unfolding id_def
  by sepref

declare partition_between_code.refine[sepref_fr_rules]



(* TODO *)

text \<open>Refined quicksort algorithm: We use the refined partition function.\<close>
definition quicksort_ref :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::ord list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort_ref R h i j xs0 = do {
  RECT (\<lambda>f (i,j,xs). do {
      ASSERT(mset xs = mset xs0);
      if j \<le> i then RETURN xs
      else do{
      	(xs, k) \<leftarrow> partition_between_ref R h i j xs;
      	xs \<leftarrow> f (i, k-1, xs);
      	f (k+1, j, xs)
      }
    })
    (i, j, xs0)
  }\<close>

lemma quicksort_ref_quicksort:
  \<open>quicksort_ref R f lo hi xs \<le> \<Down> Id (quicksort R f lo hi xs)\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
  have pre: \<open> ((lo, hi, xs), lo, hi, xs) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close>
    by auto
  have f: \<open>f (x1b, x2e - 1, x1e) \<comment> \<open>Boilerplate code for first recursive call\<close>
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
  have f': \<open>f (x2e + 1, x1c, xsa) \<le> \<Down> Id (fa (x2d + 1, x1a, xsaa))\<close>  \<comment> \<open>Boilerplate code for second recursive call\<close>
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
    subgoal
      by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule f; assumption)
    apply (rule f'; assumption)
    done
 qed

\<comment> \<open>Example implementation\<close>
definition quicksort_impl where
  \<open>quicksort_impl = quicksort_ref (\<le>) id\<close>

sepref_register quicksort_impl

\<comment> \<open>Example implementation code\<close>
sepref_definition quicksort_code
  is \<open>uncurry2 (quicksort_impl)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding partition_between_impl_def[symmetric]
    quicksort_impl_def quicksort_ref_def
  by sepref

declare quicksort_code.refine[sepref_fr_rules]

\<comment> \<open>Sort the entire list\<close>
definition full_quicksort where
  \<open>full_quicksort R h xs = quicksort R h 0 (length xs - 1) xs\<close>

definition full_quicksort_ref where
  \<open>full_quicksort_ref R h xs =
    quicksort_ref R h 0 (length xs - 1) xs\<close>

definition full_quicksort_impl :: \<open>nat list \<Rightarrow> nat list nres\<close> where
  \<open>full_quicksort_impl xs = full_quicksort_ref (\<le>) id xs\<close>

lemma full_quicksort_ref_full_quicksort:
  \<open>(full_quicksort_ref R h, full_quicksort R h) \<in>
    \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle> \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding full_quicksort_ref_def full_quicksort_def
  by (intro frefI nres_relI)
     (auto intro!: quicksort_ref_quicksort[unfolded Down_id_eq]
       simp: List.null_def)

text \<open>Executable code for the example instance\<close>
sepref_definition full_quicksort_code
  is \<open>full_quicksort_impl\<close>
  :: \<open>(arl_assn nat_assn)\<^sup>d \<rightarrow>\<^sub>a
      arl_assn nat_assn\<close>
  unfolding full_quicksort_impl_def full_quicksort_ref_def quicksort_impl_def[symmetric] List.null_def
  by sepref

text \<open>Export the code\<close>
export_code \<open>nat_of_integer\<close> \<open>integer_of_nat\<close> \<open>partition_between_code\<close> \<open>full_quicksort_code\<close> in SML_imp module_name IsaQuicksort file "code/quicksort.sml"


text \<open>Final correctness lemma\<close>
lemma full_quicksort_correct:
  assumes
    \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close> and \<open>\<And>x. R (h x) (h x)\<close>
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs = mset xs'))\<close>
  unfolding full_quicksort_def
  apply (rule order_trans)
   prefer 1
   apply (rule quicksort_correct[where R=R])
       apply auto
  using assms apply auto
  sledgehammer
  (* subgoal by (meson diff_Suc_less length_greater_0_conv)
  subgoal by force *)
  done



end
