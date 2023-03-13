theory IsaSAT_VSIDS
  imports Watched_Literals.WB_Sort Ordered_Pairing_Heap_List2
    Weidenbach_Book_Base.Explorer
    Pairing_Heaps
begin

definition mop_get_min where
  \<open>mop_get_min xs = do {
    ASSERT (xs \<noteq> None);
    RETURN (get_min2 xs)
  }\<close>

context pairing_heap
begin

definition mop_pop_min where
  \<open>mop_pop_min xs = do {
    ASSERT (xs \<noteq> None);
    a \<leftarrow> mop_get_min xs;
    RETURN (a, del_min xs)
  }\<close>

definition mop_push where
  \<open>mop_push a w xs = do {
    ASSERT (xs \<noteq> None \<and> a \<notin># mset_nodes (the xs));
    RETURN (insert a w xs)
  }\<close>

definition mop_rescore where
  \<open>mop_rescore x w xs = do {
    ASSERT (xs \<noteq> None);
    let a = find_key x (the xs);
    let b = remove_key x (the xs);
    if a = None
    then RETURN b
    else do {
      let a = the a;
      ASSERT (le (score a) w);
      let a = Hp (node a) w (hps a);
      RETURN (merge (Some a) b)
    }
  }\<close>


definition mop_score where
  \<open>mop_score x xs = do {
    if xs \<noteq> None \<and> x \<in># mset_nodes (the xs)
    then RETURN (node (the (hp_node x (the xs))))
    else
      SPEC (\<lambda>_. True)
  }\<close>


text \<open>This is a bit stricter than required, but we decided to put distinctiveness already here, instead of adding it later.\<close>
definition pairing_heap_rel where
  \<open>pairing_heap_rel xs \<longleftrightarrow> invar xs \<and> (xs \<noteq> None \<longrightarrow> distinct_mset (mset_nodes (the xs)))\<close>

lemma mop_push_rule:
  assumes \<open>pairing_heap_rel xs\<close> \<open>xs \<noteq> None\<close> \<open>a \<notin># mset_nodes (the xs)\<close>
  shows \<open>mop_push a w xs \<le> SPEC (\<lambda>xs'. xs' = insert a w xs \<and> pairing_heap_rel xs')\<close>
  using assms unfolding mop_push_def
  apply (refine_vcg)
  subgoal by auto
  subgoal by (auto simp: pairing_heap_rel_def intro!: invar_insert)
  done

lemma mop_pop_min:
  assumes \<open>pairing_heap_rel xs\<close> \<open>xs \<noteq> None\<close>
  shows \<open>mop_pop_min xs \<le> SPEC (\<lambda>(a, xs'). a = get_min2 xs \<and> xs' = del_min xs \<and> pairing_heap_rel xs')\<close>
  using assms unfolding mop_pop_min_def mop_get_min_def
  apply (refine_vcg)
  subgoal by auto
  subgoal by auto
  subgoal
    using invar_del_min[of xs] mset_nodes_merge_pairs[of \<open>hps (the xs)\<close>]
    by (cases xs; cases \<open>the xs\<close>; cases \<open>hps (the xs)\<close>) (auto simp: pairing_heap_rel_def pass12_merge_pairs)
  done

end


text \<open>
  We first tried to follow the setup from Isabelle LLVM, but it is not
  clear how useful this really is. Hence we adapted the definition from
  the abstract operations.
\<close>
locale hmstruct_with_prio =
    fixes lt :: \<open>'v \<Rightarrow> 'v \<Rightarrow> bool\<close> and
    le :: \<open>'v \<Rightarrow> 'v \<Rightarrow> bool\<close>
  assumes le: \<open>\<And>a b. le a b \<longleftrightarrow> a = b \<or> lt a b\<close> and
    trans: \<open>transp le\<close> and
    transt: \<open>transp lt\<close> and
    totalt: \<open>totalp lt\<close>
begin

    definition mop_prio_pop_min where
      "mop_prio_pop_min = (\<lambda>(b, w). doN {ASSERT (b\<noteq>{#}); SPEC (\<lambda>(v, (b', w)).
        v \<in># b
      \<and> b'=b - {#v#}
      \<and> (\<forall>v'\<in>set_mset b. le (w v) (w v')))})"

    definition mop_prio_peek_min where
      "mop_prio_peek_min \<equiv>  (\<lambda>(b, w). doN {ASSERT (b\<noteq>{#}); SPEC (\<lambda>v.
          v \<in># b
        \<and> (\<forall>v'\<in>set_mset b. le (w v) (w v')))})"

    definition mop_prio_change_weight where
      "mop_prio_change_weight \<equiv>  (\<lambda>v \<omega> (b, w). doN {
        if v \<in># b then RETURN (b,w)
        else RETURN (b, w(v := \<omega>))
     })"

    definition mop_prio_insert where
      "mop_prio_insert \<equiv>  (\<lambda>v \<omega> (b, w). doN {
        ASSERT (v \<notin># b);
        RETURN (add_mset v b, w(v := \<omega>))
     })"

    definition mop_prio_insert_maybe where
      "mop_prio_insert_maybe \<equiv>  (\<lambda>v \<omega> (bw). doN {
        if v \<notin># fst bw then mop_prio_insert v \<omega> (bw)
        else mop_prio_change_weight v \<omega> (bw)
     })"

sublocale pairing_heap
  by unfold_locales (rule le trans transt totalt)+

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
  by (auto)

thm mset_nodes_pass\<^sub>2
lemma score_pass2_same:
  \<open>distinct_mset (sum_list (map mset_nodes x3)) \<Longrightarrow> pass\<^sub>2 x3 \<noteq> None \<Longrightarrow>v \<in># sum_list (map mset_nodes x3) \<Longrightarrow>
  score (the (hp_node v (the (pass\<^sub>2 x3)))) = score (the (hp_node_children v x3))\<close>
  apply (induction x3 rule: pass\<^sub>2.induct)
  subgoal by auto
  subgoal for h hs
    using node_pass\<^sub>2_in_nodes[of hs]
    apply (cases h; cases \<open>the (pass\<^sub>2 hs)\<close>)
    apply (auto split: option.splits simp: hp_node_children_None_notin2 hp_node_children_Cons_if distinct_mset_add)
                apply (metis if_Some_None_eq_None mset_subset_eq_insertD pass\<^sub>2.simps(1))
               apply (metis disjunct_not_in insert_subset_eq_iff option.simps(2) pass\<^sub>2.simps(1))
              apply (metis insert_subset_eq_iff option.simps(2) pass\<^sub>2.simps(1))
             apply (metis disjunct_not_in mset_subset_eq_insertD not_None_eq2 pass\<^sub>2.simps(1))
            apply (metis add_mset_disjoint(1) hp_node_children_None_notin2 insert_DiffM mset_le_add_mset_decr_left1 mset_map mset_subset_eqD option.simps(2) pass\<^sub>2.simps(1) sum_mset_sum_list)
           apply (metis option.simps(2) pass\<^sub>2.simps(1))
          apply (metis option.distinct(1) pass\<^sub>2.simps(1))
         apply (metis option.simps(2) pass\<^sub>2.simps(1))
        apply (metis option.distinct(1) pass\<^sub>2.simps(1))
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
  apply (metis empty_iff list.map(1) pairing_heap_assms.mset_nodes_pass\<^sub>1 set_mset_empty sum_list_simps(1))
  apply (subst score_pass2_same score_hp_node_pass\<^sub>1)
  apply simp_all
  done

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

end

end
