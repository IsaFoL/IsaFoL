theory IsaSAT_VSIDS
  imports Watched_Literals.WB_Sort IsaSAT_Setup Ordered_Pairing_Heap_List2
  (*  IsaSAT_Literals_LLVM
    Isabelle_LLVM.IICF
    Isabelle_LLVM.LLVM_DS_Open_List
    Isabelle_LLVM.LLVM_DS_Array_List_Pure*)
begin

typ \<open>'v clauses\<close>

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

datatype 'a pairing_heap = PHeap (ph_score: 'a) (ph_contained: bool) (ph_children: \<open>nat list\<close>)

(*TODO we need a field to say contained or not*)
inductive encoded_pairheap where
  empty: \<open>encoded_pairheap arr {#}\<close> if \<open>ph_contained ` set arr \<subseteq> {False}\<close> |
  leaf: \<open>encoded_pairheap (arr[n := PHeap x intree []]) (add_mset (Hp n x []) trees)\<close>
  if  \<open>encoded_pairheap arr trees\<close> \<open>n \<notin># \<Sum>\<^sub># (mset_nodes `# trees)\<close> and
    \<open>n < length arr\<close>
    \<open>intree\<close> |
  comb: \<open>encoded_pairheap (arr[n := PHeap (ph_score (arr!n)) (ph_contained (arr!n)) (ph_children (arr!n)@[m])]) (add_mset (Hp n w\<^sub>n (Hp m w\<^sub>m child\<^sub>m # child\<^sub>n)) trees)\<close>
  if  \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n (child\<^sub>n)) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>

lemma encoded_pairheap_distinct_nodes: \<open>encoded_pairheap arr trees \<Longrightarrow> distinct_mset (\<Sum>\<^sub># (mset_nodes `# trees))\<close>
  by (induction rule: encoded_pairheap.induct)
   (auto simp: ac_simps)

lemma encoded_pairheap_change_irrelevant:
  \<open>encoded_pairheap arr trees \<Longrightarrow> \<not>ph_contained a \<Longrightarrow> n < length arr \<Longrightarrow>
  n \<notin># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> encoded_pairheap (arr [n := a]) trees\<close>
  apply (induction rule: encoded_pairheap.induct)
  subgoal
    by (rule encoded_pairheap.empty) (auto elim: in_set_upd_cases)
  subgoal for arr trees na x
    using encoded_pairheap.leaf[of \<open>arr[n := a]\<close> trees na x]
    by (auto simp add: list_update_swap)
  subgoal for arr na w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees
    using encoded_pairheap.comb[of \<open>arr[n := a]\<close> na w\<^sub>n child\<^sub>n m w\<^sub>m child\<^sub>m trees]
    by (auto simp: list_update_swap)
  done


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

lemma  encoded_pairheap_le_lengthI: \<open>encoded_pairheap arr trees \<Longrightarrow> m \<in># \<Sum>\<^sub># (mset_nodes `# trees) \<Longrightarrow> m < length arr\<close>
  by (induction arr trees arbitrary:  rule: encoded_pairheap.induct) auto

lemma mset_nodes_nodes: \<open>set_mset (\<Sum>\<^sub># (mset_nodes `# nodes x)) = set_mset (mset_nodes x)\<close>
  by (induction x)  (force simp: in_mset_sum_list_iff)

lemma mset_nodes_nodes_indirect: \<open>nodes x = A \<Longrightarrow> set_mset (mset_nodes x) = set_mset ( \<Sum>\<^sub>#(mset_nodes  `# A))\<close>
  unfolding mset_nodes_nodes[symmetric]
  by simp

lemma in_mset_nodes_iff: \<open>n \<in># mset_nodes x \<Longrightarrow> \<exists>m a. Hp n m a \<in># nodes x\<close>
  by (induction x)
   (fastforce simp: mset_nodes_nodes in_mset_sum_list_iff)


lemma in_sum_mset_nodes_iff: \<open>(\<exists>m a. Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees)) \<longleftrightarrow> n \<in># \<Sum>\<^sub># (mset_nodes `# trees)\<close>
  apply (rule iffI)
  subgoal
    apply (induction trees)
    apply (auto simp: mset_nodes_nodes)
    using mset_nodes_nodes apply fastforce
    done
  subgoal
    by (induction trees)
     (auto simp: mset_nodes_nodes dest!: in_mset_nodes_iff)
  done

lemma encoded_pairheap_correct_annot:
  assumes 1: \<open>encoded_pairheap arr trees\<close> and
    \<open>Hp n m a \<in>#  \<Sum>\<^sub># (nodes `# trees)\<close>
  shows \<open>(arr ! n) = PHeap m True (rev (map node a))\<close>
proof -
  have 2: \<open>n \<in># \<Sum>\<^sub># (mset_nodes `# trees)\<close>
    by (rule in_sum_mset_nodes_iff[THEN iffD1])
     (use assms(2) in auto)
  show ?thesis
    using 1 assms(2) encoded_pairheap_le_lengthI[OF 1 2] encoded_pairheap_distinct_nodes[OF 1]
    apply (induction arr trees arbitrary:  a rule: encoded_pairheap.induct)
    subgoal by auto
    subgoal for arr trees m' w
      by auto (use in_sum_mset_nodes_iff mset_nodes_nodes in fastforce)+
    subgoal for arr na w\<^sub>n child\<^sub>n ma w\<^sub>m child\<^sub>m trees a
      apply (auto)
      apply fastforce
      apply fastforce
      apply fastforce
      apply (metis (mono_tags, opaque_lifting) add.assoc add.left_commute fst_conv)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (simp add: union_assoc union_lcomm)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (simp add: union_assoc union_lcomm)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (metis in_sum_mset_nodes_iff sum_image_mset_sum_map)
      apply (metis (no_types, lifting) fst_conv union_assoc union_lcomm)
      apply (metis (no_types, lifting) pairing_heap.sel(1) union_assoc union_lcomm)
      apply (metis pairing_heap.collapse pairing_heap.inject union_commute union_lcomm)
      apply (metis image_mset_single in_sum_mset_nodes_iff sum_mset.singleton)
      by (metis (no_types, lifting) union_assoc union_lcomm)
   done
qed

definition vsids_link where
  \<open>vsids_link arr m n = do {
     ASSERT (m < length arr);
     ASSERT (n < length arr);
     if ph_score (arr ! n) \<le> ph_score (arr ! m) then RETURN (arr[m := PHeap (ph_score (arr ! m)) True (ph_children (arr ! m) @ [n])])
     else RETURN (arr [n := PHeap (ph_score (arr ! n)) True (ph_children (arr ! n) @ [m])])
}\<close>


lemma vsids_link:
  assumes vsids: \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>
  shows \<open>vsids_link arr m n \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' (add_mset (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m)) trees))\<close>
proof -
  show ?thesis
    unfolding vsids_link_def
    apply (refine_vcg if_refine)
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of m] by auto
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of n] by auto
    subgoal
      using encoded_pairheap.comb[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap.comb[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    done
qed

definition vsids_insert where
  \<open>vsids_insert m n arr = do {
    ASSERT (n < length arr);
    vsids_link (arr[n:= PHeap (ph_score (arr!n)) True []]) m n
  }\<close>

lemma vsids_insert:
  assumes \<open>encoded_pairheap arr {#Hp m w\<^sub>m children#}\<close> \<open>n \<notin># mset_nodes (Hp m w\<^sub>m children)\<close> \<open>n < length arr\<close>
  shows \<open>vsids_insert m n arr \<le> SPEC (\<lambda>arr'. encoded_pairheap arr' {#the (VSIDS.insert n (ph_score (arr!n)) (Some (Hp m w\<^sub>m children)))#}) \<close>
proof -
  have 1: \<open>encoded_pairheap (arr[n:= PHeap (ph_score (arr!n)) True []]) {#Hp n (ph_score (arr!n)) [], Hp m w\<^sub>m children#}\<close>
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
     if ph_score (arr ! n) \<le> ph_score (arr ! m) then RETURN (arr[m := PHeap (ph_score (arr ! m)) True (ph_children (arr ! m) @ [n])], m)
     else RETURN (arr [n := PHeap (ph_score (arr ! n)) True (ph_children (arr ! n) @ [m])], n)
}\<close>

lemma vsids_link2:
  assumes vsids: \<open>encoded_pairheap arr (add_mset (Hp n w\<^sub>n child\<^sub>n) (add_mset (Hp m w\<^sub>m child\<^sub>m) trees))\<close>
  shows \<open>vsids_link2 arr m n \<le> SPEC (\<lambda>(arr', k). k = node (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m))  \<and>
    encoded_pairheap arr' (add_mset (VSIDS.link (Hp n w\<^sub>n child\<^sub>n) (Hp m w\<^sub>m child\<^sub>m)) trees))\<close>
proof -
  show ?thesis
    unfolding vsids_link2_def
    apply (refine_vcg if_refine)
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of m] by auto
    subgoal using encoded_pairheap_le_lengthI[OF vsids, of n] by auto
    subgoal
      using encoded_pairheap.comb[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap.comb[OF vsids[unfolded add_mset_commute[of \<open>Hp n _ _\<close>]]]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap.comb[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    subgoal
      using encoded_pairheap.comb[OF vsids]
        encoded_pairheap_correct_annot[OF vsids, of n w\<^sub>n child\<^sub>n]
        encoded_pairheap_correct_annot[OF vsids, of m w\<^sub>m child\<^sub>m]
      by (auto intro: encoded_pairheap.intros)
    done
qed

inductive_cases encoded_pairheapE: \<open>encoded_pairheap arr trees\<close>

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
    apply (auto intro!: simp: )
    by (metis image_eqI in_set_image_conv_nth)
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


definition vsids_merge_pairs where
  \<open>vsids_merge_pairs arr (xs :: nat list) j = do {
  ASSERT (j < length xs);
  REC\<^sub>T (\<lambda>f (arr, j). do {
  if 0 = j then RETURN (arr, xs!j)
  else if j = 1 then do {
    ASSERT (j < length xs);
    ASSERT (j > 0);
    vsids_link2 arr (xs!(j-1)) (xs!j)
  }
  else do {
    ASSERT (j < length xs);
    ASSERT (j > 0);
    (arr, m) \<leftarrow> f (arr, j-2);
    (arr, n) \<leftarrow> vsids_link2 arr (xs!(j-1)) (xs!j);
    (arr, p) \<leftarrow> vsids_link2 arr m n;
    RETURN (arr, p)}
  }) (arr, j)
  }\<close>


lemma merge_pairs_empty_iff[simp, iff]: \<open>VSIDS.merge_pairs xs = None \<longleftrightarrow> xs = []\<close>
  by (cases xs rule: VSIDS.merge_pairs.cases) auto

(*TODO: we are going over hp in the wrong order *)
lemma
  assumes \<open>encoded_pairheap arr (mset hp\<^sub>s + trees)\<close>
    \<open>(map node hp\<^sub>s) = take (Suc j) xs\<close>
    \<open>j < length xs\<close>
  shows \<open>vsids_merge_pairs arr xs j \<le> \<Down> Id (SPEC (\<lambda>(arr', n). n = node (the (VSIDS.merge_pairs (rev hp\<^sub>s))) \<and>
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
  have [simp]: \<open>j > 0 \<Longrightarrow> (Hp (xs ! 0) (score (hp\<^sub>s ! 0)) (hps (hp\<^sub>s ! 0))) = hd hp\<^sub>s\<close>
    using assms(2,3) by (cases hp\<^sub>s; cases xs; cases j; auto)
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

  have [simp]: \<open>length hp\<^sub>s = Suc j\<close>
    using arg_cong[OF assms(2), of length] assms(3) by auto
  have H1: \<open>[a] = take n xs \<longleftrightarrow> (n = 1 \<or> (length xs = 1 \<and> n \<ge> 1)) \<and> length xs>0 \<and> hd xs = a\<close> for a n xs
    by (cases xs; cases n) auto
  have [simp]: \<open>y \<noteq> Suc 0 \<Longrightarrow> 0 < y \<Longrightarrow> y \<le> j \<Longrightarrow> add_mset (hp\<^sub>s ! (y - Suc 0)) (add_mset (hp\<^sub>s ! y) (A + mset (drop (Suc y) hp\<^sub>s) + trees)) =
    A + mset (drop (y - Suc 0) hp\<^sub>s) + trees\<close> for y A
    using assms(3) arg_cong[OF assms(2), of length]
    by (cases y; cases \<open>y - Suc 0\<close>) (auto simp flip: Cons_nth_drop_Suc)

  have pre0: \<open>pre (arr, j)\<close>
    using assms arg_cong[OF assms(2), of length, simplified, symmetric] unfolding pre_def by (auto split: option.splits)
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
      subgoal premises p
        using p(1,3-) p(2)
        by (auto simp: pre_def spec_def split: option.splits)
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