theory EPAC_Efficient_Checker_Synthesis
  imports EPAC_Efficient_Checker
    EPAC_Perfectly_Shared_Vars
    PAC_Checker.PAC_Checker_Synthesis
    EPAC_Steps_Refine
    PAC_Checker.PAC_Checker_Synthesis
begin

lemma in_set_rel_inD: \<open>(x,y) \<in>\<langle>R\<rangle>list_rel \<Longrightarrow> a \<in> set x \<Longrightarrow> \<exists>b \<in> set y. (a,b)\<in> R\<close>
  by (metis (no_types, lifting) Un_iff list.set_intros(1) list_relE3 list_rel_append1 set_append split_list_first)

lemma perfectly_shared_monom_eqD: \<open>(a, ab) \<in> perfectly_shared_monom \<V> \<Longrightarrow> ab = map ((the \<circ>\<circ> fmlookup) (fst (snd \<V>))) a\<close>
  by (induction a arbitrary: ab)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
    list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def)

lemma perfectly_shared_monom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_monom \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_eqD by blast

lemma perfectly_shared_monom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_monom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
    list_rel_split_left_iff perfectly_shared_vars_rel_def perfectly_shared_vars_def
    list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
    add_mset_eq_add_mset
    dest!: multi_member_split[of _ \<open>dom_m _\<close>])

lemma perfectly_shared_polynom_unique_left:
  \<open>(x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_polynom \<V> \<Longrightarrow> y = y'\<close>
  by (induction x arbitrary: y y')
    (auto dest: perfectly_shared_monom_unique_left simp: list_rel_split_right_iff)
lemma perfectly_shared_polynom_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel  \<Longrightarrow>
  (x, y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_polynom \<V> \<Longrightarrow> x = x'\<close>
  by (induction x arbitrary: x' y)
   (auto dest: perfectly_shared_monom_unique_right simp: list_rel_split_left_iff
    list_rel_split_right_iff)

definition (in -)perfect_shared_var_order_s :: \<open>(nat, string)shared_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ordered nres\<close> where
  \<open>perfect_shared_var_order_s \<D> x y = do {
    eq \<leftarrow> perfectly_shared_strings_equal_l \<D> x y;
    if eq then RETURN EQUAL
    else do {
      x \<leftarrow> get_var_nameS \<D> x;
      y \<leftarrow> get_var_nameS \<D> y;
      if (x, y) \<in> var_order_rel then RETURN (LESS)
      else RETURN (GREATER)
        }}\<close>

lemma perfect_shared_var_order_s_perfect_shared_var_order:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(i, i') \<in> perfectly_shared_var_rel \<V>\<close>and
    \<open>(j, j') \<in> perfectly_shared_var_rel \<V>\<close>
  shows \<open>perfect_shared_var_order_s \<V> i j \<le>\<Down>Id (perfect_shared_var_order \<V>\<D> i' j')\<close>
proof -
  show ?thesis
    unfolding perfect_shared_var_order_s_def perfect_shared_var_order_def
    apply (refine_rcg perfectly_shared_strings_equal_l_perfectly_shared_strings_equal
      get_var_nameS_spec)
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal using assms by metis
    subgoal by auto
    done
qed

definition (in -) perfect_shared_term_order_rel_s
  :: \<open>(nat, string) shared_vars \<Rightarrow> nat list\<Rightarrow> nat list \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel_s \<V> xs ys  = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
         eq \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
         if eq = EQUAL then RETURN (b, tl xs, tl ys)
         else RETURN (eq, xs, ys)
      }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>

lemma perfect_shared_term_order_rel_s_perfect_shared_term_order_rel:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>perfect_shared_term_order_rel_s \<V> xs ys \<le> \<Down>Id (perfect_shared_term_order_rel \<V>\<D> xs' ys')\<close>
  using assms
  unfolding perfect_shared_term_order_rel_s_def perfect_shared_term_order_rel_def
  apply (refine_rcg WHILET_refine[where R = \<open>Id \<times>\<^sub>r perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>]
    perfect_shared_var_order_s_perfect_shared_var_order)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  done

fun mergeR :: "_ \<Rightarrow> _ \<Rightarrow>  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "mergeR  \<Phi> f (x#xs) (y#ys) = do {
         ASSERT(\<Phi> x y);
         b \<leftarrow> f x y;
         if b then do {zs \<leftarrow> mergeR \<Phi> f xs (y#ys); RETURN (x # zs)}
         else do {zs \<leftarrow> mergeR \<Phi> f (x#xs) ys; RETURN (y # zs)}
       }"
| "mergeR  \<Phi> f xs [] = RETURN xs"
| "mergeR \<Phi> f [] ys = RETURN ys"

lemma mergeR_merge:
  assumes \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<union> set ys \<Longrightarrow> y\<in>set xs \<union> set ys \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close> and
    \<open>(xs,xs')\<in>Id\<close>and
    \<open>(ys,ys')\<in>Id\<close>
  shows
    \<open>mergeR \<Phi> f xs ys \<le> \<Down>Id (RETURN (merge f' xs' ys'))\<close>
proof -
  have xs: \<open>xs' = xs\<close> \<open>ys' = ys\<close>
    using assms
    by auto
  show ?thesis
    using assms(1,2) unfolding xs
    apply (induction f' xs ys arbitrary: xs' ys' rule: merge.induct)
    subgoal for f' x xs y ys
      unfolding mergeR.simps merge.simps
      apply (refine_rcg)
      subgoal by simp
      subgoal premises p
        using p(1,2,3,4,5) p(4)[of x y, simplified]
        apply auto
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        apply (smt RES_sng_eq_RETURN insert_compr ireturn_rule nres_order_simps(20) specify_left)
        done
      done
    subgoal by auto
    subgoal by auto
    done
qed

lemma merge_alt:
  "RETURN (merge f xs ys) = SPEC(\<lambda>zs. zs = merge f xs ys \<and> set zs = set xs \<union> set ys)"
  by (induction f xs ys rule: merge.induct)
   (clarsimp_all simp: Collect_conv_if insert_commute)

fun msortR :: "_ \<Rightarrow> _ \<Rightarrow> 'a list \<Rightarrow> 'a list nres"
where
  "msortR \<Phi> f [] = RETURN []"
| "msortR \<Phi> f [x] = RETURN [x]"
| "msortR \<Phi> f xs = do {
    as \<leftarrow> msortR \<Phi> f (take (size xs div 2) xs);
    bs \<leftarrow> msortR \<Phi> f (drop (size xs div 2) xs);
   mergeR \<Phi> f as bs
  }"

lemma set_msort[simp]: \<open>set (msort f xs) = set xs\<close>
   by (meson mset_eq_setD mset_msort)

lemma msortR_msort:
  assumes \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow>\<Phi> x y\<close> and
    \<open>\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> f x y \<le> \<Down>Id (RETURN (f' x y))\<close>
  shows
    \<open>msortR \<Phi> f xs \<le> \<Down>Id (RETURN (msort f' xs))\<close>
proof -
  have a: \<open>set (take (length xs div 2) (y # xs)) \<subseteq> insert x (insert y (set xs))\<close>
    \<open>set (drop (length xs div 2) (y # xs)) \<subseteq> insert x (insert y (set xs))\<close>
    for x y xs
    by (auto dest: in_set_takeD in_set_dropD)
  have H: \<open>RETURN (msort f' (x#y#xs)) = do {
    let as = msort f' (take (size (x#y#xs) div 2) (x#y#xs));
    let bs = msort f' (drop (size (x#y#xs) div 2) (x#y#xs));
    ASSERT(set (as) \<subseteq> set (x#y#xs));
    ASSERT(set (bs) \<subseteq> set (x#y#xs));
    RETURN (merge f' as bs)}\<close> for x y xs f'
    unfolding Let_def
    by (auto simp: a)
  show ?thesis
    supply RETURN_as_SPEC_refine[refine2 del]
  using assms
  apply (induction f' xs rule: msort.induct)
  subgoal by auto
  subgoal by auto
  subgoal premises p for f' x y xs
    using p
    unfolding msortR.simps H
    apply (refine_vcg mergeR_merge p)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_takeD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by (auto dest!: in_set_dropD)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  done
qed

lemma merge_list_rel:
  assumes \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set ys \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set ys' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close> and
    \<open>(ys,ys') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(merge f xs ys, merge f' xs' ys') \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  show ?thesis
    using assms
  proof (induction f' xs' ys' arbitrary: f xs ys rule: merge.induct)
    case (1 f' x' xs' y' y's)
    have \<open>f' x' y' \<Longrightarrow>
      (PAC_Checker_Init.merge f (tl xs) ys, PAC_Checker_Init.merge f' xs' (y' # y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    moreover have \<open>\<not>f' x' y' \<Longrightarrow>
      (PAC_Checker_Init.merge f ( xs) (tl ys), PAC_Checker_Init.merge f' (x' # xs') (y's)) \<in> \<langle>R\<rangle>list_rel\<close>
      apply (rule 1)
      apply assumption
      apply (rule 1(3); auto dest: in_set_tlD)
      using 1(4-5) apply (auto simp: list_rel_split_left_iff)
      done
    ultimately show ?case
      using 1(1,4-5) 1(3)[of \<open>hd xs\<close> \<open>hd ys\<close> x' y']
      by (auto simp: list_rel_split_left_iff)
  qed  (auto simp: list_rel_split_left_iff)

qed

lemma msort_list_rel:
  assumes  \<open>\<And>x y x' y'. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> x'\<in>set xs' \<Longrightarrow> y'\<in>set xs' \<Longrightarrow> (x,x')\<in>R \<Longrightarrow> (y,y')\<in>R \<Longrightarrow> f x y = f' x' y'\<close> and
    \<open>(xs,xs') \<in> \<langle>R\<rangle>list_rel\<close>
  shows \<open>(msort f xs, msort f' xs') \<in> \<langle>R\<rangle>list_rel\<close>
proof -
  show ?thesis
    using assms
  proof (induction f' xs' arbitrary: xs f rule: msort.induct)
    case (3 f'' v vb vc)
    have xs: \<open>
      (msort f (take (length xs div 2) xs), msort f'' (take (length (v # vb # vc) div 2) (v # vb # vc))) \<in> \<langle>R\<rangle>list_rel\<close>
      \<open>(msort f (drop (length xs div 2) xs), msort f'' (drop (length (v # vb # vc) div 2) (v # vb # vc))) \<in> \<langle>R\<rangle>list_rel\<close>
      subgoal
        apply (rule 3)
        using 3(3-) apply (force dest!:  in_set_dropD in_set_takeD list_rel_imp_same_length)
        using 3(4) apply (auto simp: list_rel_imp_same_length dest: list_rel_takeD)
        done
      subgoal
        apply (rule 3)
        using 3(3-) apply (force dest!:  in_set_dropD in_set_takeD list_rel_imp_same_length
          dest: )
        using 3(4) apply (auto simp: list_rel_imp_same_length dest: list_rel_dropD)
        done
      done
    have H: \<open>(PAC_Checker_Init.merge f (msort f (x # take (length xsaa div 2) (xa # xsaa)))
      (msort f (drop (length xsaa div 2) (xa # xsaa))),
      PAC_Checker_Init.merge f''  (msort f'' (v # take (length vc div 2) (vb # vc)))
      (msort f'' (drop (length vc div 2) (vb # vc))))
      \<in> \<langle>R\<rangle>list_rel\<close>
      if \<open>xs = x # xa # xsaa\<close> and
        \<open> (x, v) \<in> R\<close> and
        \<open>(xa, vb) \<in> R\<close> and
        \<open> (xa, vb) \<in> R\<close>
      for x xa xsaa
      apply (rule merge_list_rel)
      subgoal for xb y x' y'
        by (rule 3(3))
          (use that in \<open>auto dest: in_set_takeD in_set_dropD\<close>)
      subgoal
        by (use xs(1) 3(4) that in auto)
      subgoal
        by (use xs(2) 3(4) that in auto)
      done
    show ?case
      using 3(3-) H by (auto simp: list_rel_split_left_iff)
  qed (auto simp: list_rel_split_left_iff intro!: )
qed


lemma msortR_alt_def:
  \<open>(msortR \<Phi> f xs) = REC\<^sub>T(\<lambda>msortR' xs.
  if length xs \<le> 1 then RETURN xs else do {
    let xs1 = (take ((size xs) div 2) xs);
    let xs2 = (drop ((size xs) div 2) xs);
    as \<leftarrow> msortR' xs1;
    bs \<leftarrow> msortR' xs2;
    (mergeR \<Phi> f as bs)
  }) xs
      \<close>
 apply (induction \<Phi> f xs rule: msortR.induct)
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 done

definition sort_poly_spec_s where
  \<open>sort_poly_spec_s \<V> xs = msortR (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)}) xs\<close>

lemma sort_poly_spec_s_sort_poly_spec:
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<V>\<D>\<close>
 shows
  \<open>sort_poly_spec_s \<V> xs
  \<le>\<Down>(perfectly_shared_polynom \<V>)
  (sort_poly_spec xs')
   \<close>
proof -
  have [iff]: \<open>sorted_wrt (rel2p (Id \<union> term_order_rel)) (map fst (msort (\<lambda>xs ys. rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) xs'))\<close>
    unfolding sorted_wrt_map
    apply (rule sorted_msort)
    apply (smt Un_iff pair_in_Id_conv rel2p_def term_order_rel_trans transp_def)
    apply (auto simp: rel2p_def)
    using total_on_lexord_less_than_char_linear var_order_rel_def by auto
  have [iff]:
    \<open>(a,b)\<in> \<langle>\<langle>(perfectly_shared_var_rel \<V>)\<inverse>\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<longleftrightarrow> (b,a)\<in>perfectly_shared_polynom \<V>\<close> for a b
    by (metis converse_Id converse_iff inv_list_rel_eq inv_prod_rel_eq)

  show ?thesis
    unfolding sort_poly_spec_s_def
    apply (rule order_trans[OF msortR_msort[where
      f'=\<open> \<lambda>xs ys. (map (the o fmlookup (fst (snd \<V>))) (fst xs), map (the o fmlookup (fst (snd \<V>))) (fst ys)) \<in> Id \<union> term_order_rel\<close>]])
    subgoal for x y
      apply (cases x, cases y)
      using assms by (auto simp: list_rel_append1 list_rel_split_right_iff perfectly_shared_var_rel_def br_def
        perfectly_shared_vars_rel_def append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
        dest!: split_list split: prod.splits)
      subgoal for x y
        using assms(2,3) apply -
        apply (frule in_set_rel_inD)
        apply assumption
        apply (frule in_set_rel_inD[of _ _ _ y])
        apply assumption
        apply (elim bexE)+
        subgoal for x' y'
          apply (refine_vcg perfect_shared_term_order_rel_s_perfect_shared_term_order_rel[OF assms(1), THEN order_trans,
            of _ \<open>fst x'\<close> _ \<open>fst y'\<close>])
          subgoal
            by (cases x', cases x) auto
          subgoal
            by (cases y', cases y) auto
          subgoal
            using assms
            apply (clarsimp dest!: split_list intro!: perfect_shared_term_order_rel_spec[THEN order_trans]
              simp: append_eq_append_conv2 append_eq_Cons_conv Cons_eq_append_conv
              vars_llist_def)
            apply (rule perfect_shared_term_order_rel_spec[THEN order_trans])
            apply auto[]
            apply auto[]
            apply simp
            apply (clarsimp_all simp: perfectly_shared_monom_eqD)
            apply (cases x, cases y, cases x', cases y')
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD)
            apply (case_tac xa)
            apply (clarsimp_all simp flip: perfectly_shared_monom_eqD simp: lexord_irreflexive)
            by (meson lexord_irreflexive term_order_rel_trans var_order_rel_antisym)
          done
        done
      unfolding sort_poly_spec_def conc_fun_RES
      apply auto
      apply (subst Image_iff)
      apply (rule_tac x= \<open>msort (\<lambda>xs ys.  rel2p (Id \<union> term_order_rel) (fst xs) (fst ys)) (xs')\<close> in bexI)
      apply (auto intro!: msort_list_rel simp flip: perfectly_shared_monom_eqD
          simp: assms)
      apply (auto simp: rel2p_def)
      done
qed

definition msort_coeff_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>msort_coeff_s \<V> xs = msortR (\<lambda>a b. a \<in> set xs \<and> b \<in> set xs)
  (\<lambda>a b. do {
    x \<leftarrow> get_var_nameS \<V> a;
  y \<leftarrow> get_var_nameS \<V> b;
    RETURN(a = b \<or> var_order x y)
  }) xs\<close>


lemma perfectly_shared_var_rel_unique_left:
  \<open>(x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x, y') \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> y = y'\<close>
  using perfectly_shared_monom_unique_left[of \<open>[x]\<close>  \<open>[y]\<close> \<V> \<open>[y']\<close>] by auto

lemma perfectly_shared_var_rel_unique_right:
  \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel \<Longrightarrow> (x, y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> (x', y) \<in> perfectly_shared_var_rel \<V> \<Longrightarrow> x = x'\<close>
  using perfectly_shared_monom_unique_right[of \<V> \<D>\<V> \<open>[x]\<close>  \<open>[y]\<close>  \<open>[x']\<close>]
  by auto

lemma msort_coeff_s_sort_coeff:
  fixes xs' :: \<open>string list\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close> and
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>set xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>msort_coeff_s \<V> xs \<le> \<Down>(perfectly_shared_monom \<V>) (sort_coeff xs')\<close>
proof -
  have H: \<open>x \<in> set xs \<Longrightarrow> \<exists>x' \<in> set xs'. (x,x') \<in> perfectly_shared_var_rel \<V> \<and> x' \<in># \<D>\<V>\<close> for x
    using assms(1,3) by (auto dest: in_set_rel_inD)
  define f where
    \<open>f x y \<longleftrightarrow> x = y \<or> var_order (fst (snd \<V>) \<propto> x) (fst (snd \<V>) \<propto> y)\<close> for x y
  have [simp]: \<open>x \<in> set xs \<Longrightarrow> x' \<in> set xs' \<Longrightarrow> (x, x') \<in> perfectly_shared_var_rel \<V> \<Longrightarrow>
    fst (snd \<V>) \<propto> x = x'\<close> for x x'
    using assms(2)
    by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_var_rel_def br_def)
  have [intro]: \<open>transp (\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel)\<close>
    by (smt transE trans_var_order_rel transp_def)
  have [intro]: \<open>sorted_wrt (rel2p (Id \<union> var_order_rel))  (msort (\<lambda>a b. a = b \<or> var_order a b) xs')\<close>
    using var_roder_rel_total by (auto intro!: sorted_msort simp: rel2p_def[abs_def])
  show ?thesis
    unfolding msort_coeff_s_def
    apply (rule msortR_msort[of _ _ _ f, THEN order_trans])
    subgoal by auto
    subgoal for x y
      unfolding f_def
      apply (frule H[of x])
      apply (frule H[of y])
      apply (elim bexE)
      apply (refine_vcg get_var_nameS_spec2[THEN order_trans] assms)
      apply (solves auto)
      apply (solves auto)
      apply (subst Down_id_eq)
      apply (refine_vcg get_var_nameS_spec2[THEN order_trans] assms)
      apply (solves auto)
      apply (solves auto)
      apply (auto simp: perfectly_shared_var_rel_def br_def)
      done
    subgoal
      apply (subst Down_id_eq)
      apply (auto simp: sort_coeff_def intro!: RETURN_RES_refine)
      apply (rule_tac x = \<open>msort (\<lambda>a b. a = b \<or> var_order a b) xs'\<close> in exI)
      apply (force intro!: msort_list_rel assms simp: f_def
        dest: perfectly_shared_var_rel_unique_left
        perfectly_shared_var_rel_unique_right[OF assms(2)])
      done
    done
qed

type_synonym sllist_polynomial = \<open>(nat list \<times> int) list\<close>

definition sort_all_coeffs_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
\<open>sort_all_coeffs_s \<V> xs = monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>(a, n) b. do {ASSERT((a,n)\<in>set xs);a \<leftarrow> msort_coeff_s \<V> a; RETURN ((a, n) # b)}) []\<close>

 fun merge_coeffs0_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>merge_coeffs0_s[] = []\<close> |
  \<open>merge_coeffs0_s [(xs, n)] = (if n = 0 then [] else [(xs, n)])\<close> |
  \<open>merge_coeffs0_s ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs0_s ((xs, n + m) # p) else merge_coeffs0_s p
    else if n = 0 then merge_coeffs0_s ((ys, m) # p)
      else(xs, n) # merge_coeffs0_s ((ys, m) # p))\<close>

lemma merge_coeffs0_s_merge_coeffs0:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
  shows \<open>(merge_coeffs0_s xs, merge_coeffs0 xs') \<in> perfectly_shared_polynom \<V>\<close>
  using assms
  apply (induction xs' arbitrary: xs rule: merge_coeffs0.induct)
  subgoal by auto
  subgoal by (auto simp: list_rel_split_left_iff)
  subgoal premises p for xs n ys m p xsa
    using p(1)[of \<open>(_, _ + _) # tl (tl xsa)\<close>] p(2)[of \<open>tl (tl xsa)\<close>] p(3)[of \<open>tl xsa\<close>] p(4)[of \<open>tl xsa\<close>] p(5-)
    using perfectly_shared_monom_unique_right[OF \<V>, of _ xs]
      perfectly_shared_monom_unique_left[of \<open>fst (hd xsa)\<close> _ \<V>]
    apply (auto 4 1 simp: list_rel_split_left_iff
      dest: )
    apply smt
    done
 done

lemma list_rel_mono_strong: \<open>A \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>xs. fst xs \<in> set (fst A) \<Longrightarrow> snd xs \<in> set (snd A) \<Longrightarrow> xs \<in> R \<Longrightarrow> xs \<in> R') \<Longrightarrow> A \<in> \<langle>R'\<rangle>list_rel\<close>
  unfolding list_rel_def
  apply (cases A)
  apply (simp add: list.rel_mono_strong)
  done

definition full_normalize_poly_s where
  \<open>full_normalize_poly_s \<V> p = do {
     p \<leftarrow> sort_all_coeffs_s \<V> p;
     p \<leftarrow> sort_poly_spec_s \<V> p;
    RETURN (merge_coeffs0_s p)
  }\<close>

lemma sort_all_coeffs_s_sort_all_coeffs:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>sort_all_coeffs_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (sort_all_coeffs xs')\<close>
proof -
  have [refine]: \<open>(xs, xs') \<in> \<langle>{(a,b). a\<in>set xs \<and> (a,b)\<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel}\<rangle>list_rel\<close>
    by (rule list_rel_mono_strong[OF assms(1)])
     (use assms(3) in auto)

  show ?thesis
    unfolding sort_all_coeffs_s_def sort_all_coeffs_def
    apply (refine_vcg \<V> msort_coeff_s_sort_coeff)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto dest!: split_list)
    subgoal by auto
    done
qed


definition vars_llist_in_s :: \<open>(nat, string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow> bool\<close> where
  \<open>vars_llist_in_s = (\<lambda>(\<V>,\<D>,\<D>') p. vars_llist p \<subseteq> set_mset (dom_m \<D>'))\<close>

lemma vars_llist_in_s_vars_llist[simp]:
  assumes \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
  shows \<open>vars_llist_in_s \<V> p \<longleftrightarrow> vars_llist p \<subseteq> set_mset \<D>\<V>\<close>
  using assms unfolding perfectly_shared_vars_rel_def perfectly_shared_vars_def vars_llist_in_s_def
  by auto

definition (in -)add_poly_l_s :: \<open>(nat,string)shared_vars \<Rightarrow> sllist_polynomial \<times> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>add_poly_l_s \<D> = REC\<^sub>T
  (\<lambda>add_poly_l (p, q).
  case (p,q) of
    (p, []) \<Rightarrow> RETURN p
    | ([], q) \<Rightarrow> RETURN q
    | ((xs, n) # p, (ys, m) # q) \<Rightarrow> do {
    comp \<leftarrow> perfect_shared_term_order_rel_s \<D> xs ys;
    if comp = EQUAL then if n + m = 0 then add_poly_l (p, q)
    else do {
      pq \<leftarrow> add_poly_l (p, q);
      RETURN ((xs, n + m) # pq)
    }
    else if comp = LESS
    then do {
      pq \<leftarrow> add_poly_l (p, (ys, m) # q);
      RETURN ((xs, n) # pq)
    }
    else do {
      pq \<leftarrow> add_poly_l ((xs, n) # p, q);
      RETURN ((ys, m) # pq)
    }
  })\<close>


lemma add_poly_l_s_add_poly_l:
  fixes xs :: \<open>sllist_polynomial \<times> sllist_polynomial\<close>
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V> \<times>\<^sub>r perfectly_shared_polynom \<V>\<close>
  shows \<open>add_poly_l_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (add_poly_l_prep \<V>\<D> xs')\<close>
proof -
  have x: \<open>x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow> x \<in> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel\<close> for x
    by auto
  show ?thesis
    unfolding add_poly_l_s_def add_poly_l_prep_def
    apply (refine_rcg assms perfect_shared_term_order_rel_s_perfect_shared_term_order_rel)
    apply (rule x)
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule x)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
      (*many boring goals, some require unification*)
    by (auto)
qed

definition (in -) mult_monoms_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>mult_monoms_s \<D> xs ys = REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<D> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> f (tl xs, tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> f (tl xs, ys);
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> f (xs, tl ys);
        RETURN (hd ys # pq)
      }
   }
 }) (xs, ys)\<close>

lemma mult_monoms_s_simps:
  \<open>mult_monoms_s \<V> xs ys =
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order_s \<V> (hd xs) (hd ys);
      if comp = EQUAL then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) (tl ys);
        RETURN (hd xs # pq)
      }
      else if comp = LESS then do {
        pq \<leftarrow> mult_monoms_s \<V> (tl xs) ys;
        RETURN (hd xs # pq)
      }
      else do {
        pq \<leftarrow> mult_monoms_s \<V> xs (tl ys);
        RETURN (hd ys # pq)
      }
   }
 }\<close>
  apply (subst mult_monoms_s_def)
  apply (subst RECT_unfold, refine_mono)
  unfolding prod.case[of _ \<open>(xs,ys)\<close>]
  apply (subst mult_monoms_s_def[symmetric])+
  apply (auto intro!: bind_cong[OF refl])
  done

lemma mult_monoms_s_mult_monoms_prep:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_monom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V>\<close>
  shows \<open>mult_monoms_s \<V> xs ys \<le> \<Down>(perfectly_shared_monom \<V>) ((mult_monoms_prep \<V>\<D> xs' ys'))\<close>
proof -
  have [refine]: \<open>((xs, ys), xs', ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r perfectly_shared_monom \<V>\<close>
    using assms by auto
  have x: \<open>a \<le> \<Down> (perfectly_shared_monom \<V>) b \<Longrightarrow> a \<le> \<Down> (perfectly_shared_monom \<V>) b\<close> for a b
    by auto
  show ?thesis
    using assms unfolding mult_monoms_s_def mult_monoms_prep_def
    apply (refine_vcg perfect_shared_var_order_s_perfect_shared_var_order)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    apply (rule x)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    done
qed


definition (in -) mult_term_s
  :: \<open>(nat,string)shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow>  _ \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close>
where
  \<open>mult_term_s = (\<lambda>\<V> qs (p, m) b. nfoldli qs (\<lambda>_. True) (\<lambda>(q, n) b. do {pq \<leftarrow> mult_monoms_s \<V> p q; RETURN ((pq, m * n) # b)}) b)\<close>

definition mult_poly_s :: \<open>(nat,string) shared_vars\<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mult_poly_s \<V> p q = nfoldli p (\<lambda>_. True) (mult_term_s \<V> q) []\<close>

lemma mult_term_s_mult_monoms_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<close>
    \<open>(zs, zs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_term_s \<V> xs ys zs \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_monoms_prop \<V>\<D> xs' ys' zs')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_term_s_def mult_monoms_prop_def
    by (refine_rcg mult_monoms_s_mult_monoms_prep)
     auto
qed

lemma mult_poly_s_mult_poly_raw_prop:
  fixes xs
  assumes \<open>(\<V>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>mult_poly_s \<V> xs ys \<le> \<Down>(perfectly_shared_polynom \<V>) (mult_poly_raw_prop \<V>\<D> xs' ys')\<close>
proof -
  show ?thesis
    using assms
    unfolding mult_poly_s_def mult_poly_raw_prop_def
    by (refine_rcg mult_term_s_mult_monoms_prop)
     auto
qed


lemma op_eq_uint64_nat[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: uint64 \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)

abbreviation ordered_assn :: \<open>ordered \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>ordered_assn \<equiv> id_assn\<close>

lemma op_eq_ordered_assn[sepref_fr_rules]:
  \<open>(uncurry (return oo ((=) :: ordered \<Rightarrow> _)), uncurry (RETURN oo (=))) \<in>
    ordered_assn\<^sup>k *\<^sub>a ordered_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: uint64_nat_rel_def br_def)


abbreviation monom_s_rel where
  \<open>monom_s_rel \<equiv> \<langle>uint64_nat_rel\<rangle>list_rel\<close>

abbreviation monom_s_assn where
  \<open>monom_s_assn \<equiv> list_assn uint64_nat_assn\<close>

abbreviation poly_s_assn where
  \<open>poly_s_assn \<equiv> list_assn (monom_s_assn \<times>\<^sub>a int_assn)\<close>

sepref_decl_intf wordered is ordered

sepref_register EQUAL LESS GREATER UNKNOWN get_var_nameS perfect_shared_var_order_s perfect_shared_term_order_rel_s
lemma [sepref_fr_rules]:
  \<open>(uncurry0 (return EQUAL), uncurry0 (RETURN EQUAL)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return LESS), uncurry0 (RETURN LESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return GREATER), uncurry0 (RETURN GREATER)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  \<open>(uncurry0 (return UNKNOWN), uncurry0 (RETURN UNKNOWN)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by (sepref_to_hoare; sep_auto)+

sepref_definition perfect_shared_var_order_s_impl
  is \<open>uncurry2 perfect_shared_var_order_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding perfect_shared_var_order_s_def perfectly_shared_strings_equal_l_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    var_order_rel''
  by sepref

lemmas [sepref_fr_rules] = perfect_shared_var_order_s_impl.refine

sepref_definition perfect_shared_term_order_rel_s_impl
  is \<open>uncurry2 perfect_shared_term_order_rel_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  unfolding perfect_shared_term_order_rel_s_def
   by sepref

lemmas [sepref_fr_rules] = perfect_shared_term_order_rel_s_impl.refine

sepref_definition add_poly_l_prep_impl
  is \<open>uncurry add_poly_l_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (poly_s_assn \<times>\<^sub>a poly_s_assn)\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding add_poly_l_s_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemma [sepref_fr_rules]:
  \<open>(return o is_Nil, RETURN o is_Nil)\<in> (list_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by (sepref_to_hoare)
    (sep_auto split: list.splits)

sepref_definition mult_monoms_s_impl
  is \<open>uncurry2 mult_monoms_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k *\<^sub>a monom_s_assn\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  unfolding mult_monoms_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_monoms_s_impl.refine

sepref_definition mult_term_s_impl
  is \<open>uncurry3 mult_term_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a (monom_s_assn \<times>\<^sub>a int_assn)\<^sup>k *\<^sub>a poly_s_assn\<^sup>k\<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_term_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mult_term_s_impl.refine


sepref_definition mult_poly_s_impl
  is \<open>uncurry2 mult_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k\<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_s_def conv_to_is_Nil
  unfolding
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] =
  mult_poly_s_impl.refine

sepref_register take drop
lemma [sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry (return oo take), uncurry (RETURN oo take)) \<in> nat_assn\<^sup>k *\<^sub>a (list_assn R)\<^sup>k \<rightarrow>\<^sub>a list_assn R\<close>
  apply sepref_to_hoare
  using assms unfolding is_pure_conv CONSTRAINT_def
  apply (sep_auto simp add: list_assn_pure_conv)
  apply (sep_auto simp: pure_def list_rel_takeD)
  done

lemma [sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure R\<close>
  shows \<open>(uncurry (return oo drop), uncurry (RETURN oo drop)) \<in> nat_assn\<^sup>k *\<^sub>a (list_assn R)\<^sup>k \<rightarrow>\<^sub>a list_assn R\<close>
  apply sepref_to_hoare
  using assms unfolding is_pure_conv CONSTRAINT_def
  apply (sep_auto simp add: list_assn_pure_conv)
  apply (sep_auto simp: pure_def list_rel_dropD)
  done

definition mergeR_vars :: \<open>(nat, string) shared_vars \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial nres\<close> where
  \<open>mergeR_vars \<V> = mergeR
   (\<lambda>xs ys. (\<forall>a\<in>set (fst xs). a \<in># dom_m (fst (snd \<V>))) \<and>  (\<forall>a\<in>set(fst ys). a \<in># dom_m (fst (snd \<V>))))
     (\<lambda>xs ys. do {a \<leftarrow> perfect_shared_term_order_rel_s \<V> (fst xs) (fst ys); RETURN (a \<noteq> GREATER)})\<close>
lemma mergeR_alt_def:
  \<open>(mergeR \<Phi> f xs ys) = REC\<^sub>T(\<lambda>mergeR xs.
  case xs of
    ([], ys) \<Rightarrow> RETURN ys
  | (xs, []) \<Rightarrow> RETURN xs
  | (x # xs, y # ys) \<Rightarrow> do {
    ASSERT(\<Phi> x y);
     b \<leftarrow> f x y;
    if b then do {
       zs \<leftarrow> mergeR (xs, y # ys);
       RETURN (x # zs)
    }
    else do {
     zs \<leftarrow> mergeR (x # xs, ys);
     RETURN (y # zs)
    }
  })
  (xs, ys)\<close>
 apply (induction \<Phi> f xs ys rule: mergeR.induct)
 subgoal
   apply (subst RECT_unfold, refine_mono)
   apply (simp add:)
   apply (rule bind_cong[OF refl])+
   apply auto
   done
 subgoal
   by (subst RECT_unfold, refine_mono)
    (simp split: list.splits)
 subgoal
   by (subst RECT_unfold, refine_mono) auto
 done

sepref_definition mergeR_vars_impl
  is \<open>uncurry2 mergeR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding mergeR_vars_def mergeR_alt_def
  by sepref

lemmas [sepref_fr_rules] =
  mergeR_vars_impl.refine

abbreviation msortR_vars where
  \<open>msortR_vars \<equiv> sort_poly_spec_s\<close>
lemmas msortR_vars_def = sort_poly_spec_s_def

sepref_register mergeR_vars msortR_vars

sepref_definition msortR_vars_impl
  is \<open>uncurry msortR_vars\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit = 1]]
  unfolding msortR_vars_def msortR_alt_def  mergeR_vars_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] =
  msortR_vars_impl.refine

fun merge_coeffs_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial\<close> where
  \<open>merge_coeffs_s [] = []\<close> |
  \<open>merge_coeffs_s [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs_s ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs_s ((xs, n + m) # p) else merge_coeffs_s p
      else (xs, n) # merge_coeffs_s ((ys, m) # p))\<close>

lemma perfectly_shared_merge_coeffs_merge_coeffs:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>(merge_coeffs_s xs, merge_coeffs xs') \<in> (perfectly_shared_polynom \<V>)\<close>
  using assms
  apply (induction xs arbitrary: xs' rule: merge_coeffs_s.induct)
  subgoal
    by auto
  subgoal
    by (auto simp: list_rel_split_right_iff)
  subgoal
    by(auto simp: list_rel_split_right_iff dest: perfectly_shared_monom_unique_left
      perfectly_shared_monom_unique_right)
  done

definition normalize_poly_s :: \<open>_\<close> where
  \<open>normalize_poly_s \<V> p =  do {
  p \<leftarrow> msortR_vars \<V> p;
  RETURN (merge_coeffs_s p)
  }\<close>

lemma normalize_poly_s_normalize_poly_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>normalize_poly_s \<V> xs \<le> \<Down> (perfectly_shared_polynom \<V>) (normalize_poly xs')\<close>
  unfolding normalize_poly_s_def normalize_poly_def
  by (refine_rcg sort_poly_spec_s_sort_poly_spec[unfolded msortR_vars_def[symmetric]] assms
    perfectly_shared_merge_coeffs_merge_coeffs)

definition check_linear_combi_l_s_dom_err :: \<open>sllist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_dom_err p r = SPEC (\<lambda>_. True)\<close>

definition mult_poly_full_s :: \<open>_\<close> where
  \<open>mult_poly_full_s \<V> p q = do {
    pq \<leftarrow> mult_poly_s \<V> p q;
   normalize_poly_s \<V> pq
  }\<close>

lemma mult_poly_full_s_mult_poly_full_prop:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(ys, ys') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close> and
    \<open>vars_llist ys' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>mult_poly_full_s \<V> xs ys \<le> \<Down> (perfectly_shared_polynom \<V>) (mult_poly_full_prop \<D>\<V> xs' ys')\<close>
  unfolding mult_poly_full_s_def mult_poly_full_prop_def
  by (refine_rcg mult_poly_s_mult_poly_raw_prop assms normalize_poly_s_normalize_poly_s)
   (use assms in auto)
definition (in -)linear_combi_l_prep_s
  :: \<open>nat \<Rightarrow> _ \<Rightarrow> (nat, string) shared_vars \<Rightarrow> _ \<Rightarrow> (sllist_polynomial \<times> (llist_polynomial \<times> nat) list \<times> string code_status) nres\<close>
where
  \<open>linear_combi_l_prep_s i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      let (q :: llist_polynomial, i) = hd xs;
      if (i \<notin># dom_m A \<or> \<not>(vars_llist_in_s \<V> q))
      then do {
        err \<leftarrow> check_linear_combi_l_s_dom_err p i;
        RETURN (p, xs, error_msg i err)
      } else do {
        ASSERT(fmlookup A i \<noteq> None);
        let r = the (fmlookup A i);
        if q = [([], 1)]
        then do {
          pq \<leftarrow> add_poly_l_s \<V> (p, r);
          RETURN (pq, tl xs, CSUCCESS)}
        else do {
          (no_new, q) \<leftarrow> normalize_poly_sharedS \<V> (q);
          q \<leftarrow> mult_poly_full_s \<V> q r;
          pq \<leftarrow> add_poly_l_s \<V> (p, q);
          RETURN (pq, tl xs, CSUCCESS)
        }
        }
        })
        ([], xs, CSUCCESS)
          }\<close>

lemma normalize_poly_sharedS_normalize_poly_shared:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(xs, xs') \<in> Id\<close>
  shows \<open>normalize_poly_sharedS \<V> xs
    \<le> \<Down>(bool_rel \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (normalize_poly_shared \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>full_normalize_poly xs \<le> \<Down> Id (full_normalize_poly xs')\<close>
    using assms by auto
  show ?thesis
    unfolding normalize_poly_sharedS_def normalize_poly_shared_def
    by (refine_rcg assms import_poly_no_newS_import_poly_no_new)
qed


lemma linear_combi_l_prep_s_linear_combi_l_prep:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close>
    \<open>(xs,xs') \<in> Id\<close>
  shows \<open>linear_combi_l_prep_s i A \<V> xs
    \<le> \<Down>(perfectly_shared_polynom \<V> \<times>\<^sub>r Id \<times>\<^sub>r Id)
    (linear_combi_l_prep2 j B \<D>\<V> xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_s_dom_err a b
    \<le> \<Down> Id
    (check_linear_combi_l_dom_err c d)\<close> for a b c d
    unfolding check_linear_combi_l_dom_err_def check_linear_combi_l_s_dom_err_def
    by auto
  show ?thesis
    unfolding linear_combi_l_prep_s_def linear_combi_l_prep2_def
    apply (refine_rcg normalize_poly_sharedS_normalize_poly_shared
      mult_poly_full_s_mult_poly_full_prop add_poly_l_s_add_poly_l)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using fmap_rel_nat_rel_dom_m[OF assms(2)] unfolding in_dom_m_lookup_iff by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition check_linear_combi_l_s_mult_err :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_s_mult_err pq r = SPEC (\<lambda>_. True)\<close>

definition weak_equality_l_s :: \<open>sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> bool nres\<close> where
  \<open>weak_equality_l_s p q = RETURN (p = q)\<close>

definition check_linear_combi_l_s where
  \<open>check_linear_combi_l_s spec A \<V> i xs r = do {
  (mem_err, r) \<leftarrow> import_poly_no_newS \<V> r;
  if mem_err \<or> i \<in># dom_m A \<or> xs = []
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i (i \<in># dom_m A) (xs = []) (mem_err);
    RETURN (error_msg i err, r)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l_prep_s i A \<V> xs;
    if (is_cfailed err)
    then do {
      RETURN (err, r)
    }
    else do {
      b \<leftarrow> weak_equality_l_s p r;
      b' \<leftarrow> weak_equality_l_s r spec;
      if b then (if b' then RETURN (CFOUND, r) else RETURN (CSUCCESS, r)) else do {
        c \<leftarrow> check_linear_combi_l_s_mult_err p r;
        RETURN (error_msg i c, r)
      }
    }
        }}\<close>
definition weak_equality_l_s' :: \<open>_\<close> where
  \<open>weak_equality_l_s' _ =  weak_equality_l_s\<close>

definition weak_equality_l' :: \<open>_\<close> where
  \<open>weak_equality_l' _ =  weak_equality_l\<close>

lemma weak_equality_l_s_weak_equality_l:
  fixes a :: sllist_polynomial and b :: llist_polynomial and \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(a,b) \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(c,d) \<in> perfectly_shared_polynom \<V>\<close>
  shows
    \<open>weak_equality_l_s' \<V> a c \<le>\<Down>bool_rel (weak_equality_l' \<D>\<V> b d)\<close>
  using assms perfectly_shared_polynom_unique_left[OF assms(2), of d]
    perfectly_shared_polynom_unique_right[OF assms(1,2), of c]
  unfolding weak_equality_l_s_def weak_equality_l_def weak_equality_l'_def
    weak_equality_l_s'_def
  by auto

lemma check_linear_combi_l_s_check_linear_combi_l:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(xs,xs')\<in> Id\<close>
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close>
  shows \<open>check_linear_combi_l_s spec A \<V> i r xs
    \<le> \<Down>(Id \<times>\<^sub>r perfectly_shared_polynom \<V>)
    (check_linear_combi_l_prop spec' B \<D>\<V> j r' xs')\<close>
proof -
  have [refine]: \<open>check_linear_combi_l_pre_err a b c d \<le> \<Down>Id (check_linear_combi_l_pre_err u x y z)\<close>
    for a b c d u x y z
    by  (auto simp: check_linear_combi_l_pre_err_def)
  have [refine]: \<open>check_linear_combi_l_s_mult_err a b \<le> \<Down>Id (check_linear_combi_l_mult_err u x)\<close>
    for a b u x
    by  (auto simp: check_linear_combi_l_s_mult_err_def check_linear_combi_l_mult_err_def)

  show ?thesis
    unfolding check_linear_combi_l_s_def check_linear_combi_l_prop_def
    apply (refine_rcg import_poly_no_newS_import_poly_no_new assms
      linear_combi_l_prep_s_linear_combi_l_prep weak_equality_l_s_weak_equality_l[unfolded weak_equality_l'_def
      weak_equality_l_s'_def])
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

definition check_extension_l_s_new_var_multiple_err :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_s_new_var_multiple_err v p = SPEC (\<lambda>_. True)\<close>

definition check_extension_l_s_side_cond_err
  :: \<open>string \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> sllist_polynomial \<Rightarrow> string nres\<close>
where
  \<open>check_extension_l_s_side_cond_err v p p' q = SPEC (\<lambda>_. True)\<close>
term is_new_variable
definition (in -)check_extension_l2_s
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> (nat,string)shared_vars \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial \<Rightarrow>
     (string code_status \<times> sllist_polynomial \<times> (nat,string)shared_vars \<times> nat) nres\<close>
where
  \<open>check_extension_l2_s spec A \<V> i v p = do {
  n \<leftarrow> is_new_variableS v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist_in_s \<V> p;
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, 0)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, 0)
      }
      else do {
        (mem', \<V>, v') \<leftarrow> import_variableS v \<V>;
        if alloc_failed mem'
        then do {
          c \<leftarrow> check_extension_l_dom_err i;
          RETURN (error_msg i c, [], \<V>, 0)
        } else
        do {
         p2 \<leftarrow> mult_poly_full_s \<V> p p;
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         q \<leftarrow> add_poly_l_s \<V> (p2, p'');
         eq \<leftarrow> weak_equality_l_s q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v')
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>, v')
        }
      }
     }
  }
 }\<close>
lemma list_rel_tlD: \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (tl a, tl b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (metis list.sel(2) list.sel(3) list_rel_simp(1) list_rel_simp(2) list_rel_simp(4) neq_NilE)

lemma check_extension_l2_prop_alt_def:
  \<open>check_extension_l2_prop spec A \<V> i v p = do {
  n \<leftarrow> is_new_variable v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist p \<subseteq> set_mset \<V>;
  (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
  (mem', \<V>, va) \<leftarrow> if pre \<and> nonew \<and> \<not> alloc_failed mem then import_variable v \<V> else RETURN (mem, \<V>, v);
  let pre = ((pre \<and> \<not>alloc_failed mem) \<and> \<not>alloc_failed mem');

  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, va)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, va)
      }
      else do {
         ASSERT(vars_llist p \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p p;
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, va)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p q;
          RETURN (error_msg i c, [], \<V>, va)
        }
      }
    }
  }\<close>
  unfolding check_extension_l2_prop_def Let_def check_extension_l_side_cond_err_def
     is_new_variable_def
  by (auto intro!: bind_cong[OF refl])

lemma check_extension_l2_prop_alt_def2:
  \<open>check_extension_l2_prop spec A \<V> i v p = do {
  n \<leftarrow> is_new_variable v \<V>;
  let pre = i \<notin># dom_m A \<and> n;
  let nonew = vars_llist p \<subseteq> set_mset \<V>;
  (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, v)
   } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, v)
      }
      else do {
      (mem', \<V>, va) \<leftarrow> import_variable v \<V>;
      if (alloc_failed mem')
      then do {
       c \<leftarrow> check_extension_l_dom_err i;
       RETURN (error_msg i c, [], \<V>, va)
      }
      else do {
         ASSERT(vars_llist p \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p p;
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, va)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p q;
          RETURN (error_msg i c, [], \<V>, va)
        }
      }
     }
    }
  }\<close>
  unfolding check_extension_l2_prop_alt_def
  unfolding Let_def check_extension_l_side_cond_err_def de_Morgan_conj
    not_not
  by (subst if_conn(2))
    (auto intro!: bind_cong[OF refl])

lemma list_rel_mapI: \<open>(xs,ys) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (f x, g y) \<in> S) \<Longrightarrow> (map f xs, map g ys) \<in> \<langle>S\<rangle>list_rel\<close>
  by (induction xs arbitrary: ys)
    (auto simp: list_rel_split_right_iff)

lemma perfectly_shared_var_rel_perfectly_shared_monom_mono:
  \<open>(\<forall>xs. xs \<in> perfectly_shared_var_rel \<A> \<longrightarrow> xs \<in> perfectly_shared_var_rel \<A>') \<longleftrightarrow>
  (\<forall>xs. xs \<in> perfectly_shared_monom \<A> \<longrightarrow> xs \<in> perfectly_shared_monom \<A>')\<close>
  by (metis list_rel_mono old.prod.exhaust list_rel_simp(2) list_rel_simp(4))

lemma perfectly_shared_var_rel_perfectly_shared_polynom_mono:
  \<open>(\<forall>xs. xs \<in> perfectly_shared_var_rel \<A> \<longrightarrow> xs \<in> perfectly_shared_var_rel \<A>') \<longleftrightarrow>
  (\<forall>xs. xs \<in> perfectly_shared_polynom \<A> \<longrightarrow> xs \<in> perfectly_shared_polynom \<A>')\<close>
  unfolding perfectly_shared_var_rel_perfectly_shared_monom_mono
  apply (auto intro: list_rel_mono)
    apply (drule_tac x =  \<open>[(a,1)]\<close> in spec)
    apply (drule_tac x =  \<open>[(b,1)]\<close> in spec)
    apply auto
    done


lemma check_extension_l2_s_check_extension_l2:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(r,r')\<in>Id\<close>
    \<open>(i,j)\<in>nat_rel\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close>
    \<open>(v,v')\<in>Id\<close>
  shows \<open>check_extension_l2_s spec A \<V> i v r
    \<le> \<Down>{((err, p, A, v), (err', p', A', v')).
    (err, err') \<in> Id \<and>
    (\<not>is_cfailed err \<longrightarrow>
    (p, p') \<in> perfectly_shared_polynom A \<and> (v, v') \<in> perfectly_shared_var_rel A \<and>
      (A, A') \<in> {(a,b). (a,b) \<in> perfectly_shared_vars_rel \<and> perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom a})}
    (check_extension_l2_prop spec' B \<D>\<V> j v' r')\<close>
proof -
  have [refine]: \<open>check_extension_l_s_new_var_multiple_err a b \<le>\<Down>Id (check_extension_l_new_var_multiple_err a' b')\<close> for a a' b b'
    by (auto simp: check_extension_l_s_new_var_multiple_err_def check_extension_l_new_var_multiple_err_def)

  have [refine]: \<open>check_extension_l_dom_err i \<le> \<Down> (Id) (check_extension_l_dom_err j)\<close>
    by (auto simp: check_extension_l_dom_err_def)
  have [refine]: \<open>check_extension_l_s_side_cond_err a b c d \<le> \<Down>Id (check_extension_l_side_cond_err a' b' c')\<close> for a b c d a' b' c' d'
    by (auto simp: check_extension_l_s_side_cond_err_def check_extension_l_side_cond_err_def)
  have G: \<open>(a, b) \<in> import_poly_rel \<V> x \<Longrightarrow> \<not>alloc_failed (fst a) \<Longrightarrow>
    (snd (snd a), snd (snd b)) \<in> perfectly_shared_vars_rel\<close> for a b x
    by auto

  show ?thesis
    unfolding check_extension_l2_s_def check_extension_l2_prop_alt_def2 nres_monad3
    apply (refine_rcg import_polyS_import_poly assms mult_poly_full_s_mult_poly_full_prop
      import_variableS_import_variable[unfolded perfectly_shared_var_rel_perfectly_shared_polynom_mono]
      is_new_variable_spec)
    subgoal using assms by auto
    subgoal using assms by (auto simp add: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
    subgoal using assms by (auto)
    subgoal using assms by (auto)
    subgoal using assms by (auto)
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
      apply (rule add_poly_l_s_add_poly_l)
    subgoal by auto
    subgoal for _ _ x x' x1 x2 x1a x2a x1b x2b x1c x2c xa x'a x1d x2d x1e x2e x1f x2f x1g x2g p2 p2a
      using assms
      by ( auto intro!: list_rel_mapI[of _ _ \<open>perfectly_shared_monom x1g \<times>\<^sub>r int_rel\<close>])
    apply (rule weak_equality_l_s_weak_equality_l[unfolded weak_equality_l'_def
      weak_equality_l_s'_def])
    defer apply assumption
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    apply (solves auto) (*one goal with unifucation*)
    done
qed

definition PAC_checker_l_step_s
  :: \<open>sllist_polynomial \<Rightarrow> string code_status \<times> (nat,string)shared_vars \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close>
where
  \<open>PAC_checker_l_step_s = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT (\<not>is_cfailed st');
    case st of
     CL _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> full_normalize_poly (pac_res st);
        (eq, r) \<leftarrow> check_linear_combi_l_s spec A \<V> (new_id st) (pac_srcs st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmupd (new_id st) r A)
       else RETURN (eq, \<V>, A)
     }
    | Del _ \<Rightarrow>
       do {
        eq \<leftarrow> check_del_l spec A (pac_src1 st);
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmdrop (pac_src1 st) A)
        else RETURN (eq, \<V>, A)
     }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (pac_res st);
        (eq, r, \<V>, v) \<leftarrow> check_extension_l2_s spec A (\<V>) (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then do {
           r \<leftarrow> add_poly_l_s \<V> ([([v], -1)], r);
          RETURN (st', \<V>, fmupd (new_id st) r A)
        }
        else RETURN (eq, \<V>, A)
     }}
          )\<close>
lemma is_cfailed_merge_cstatus:
  "is_cfailed (merge_cstatus c d) \<longleftrightarrow> is_cfailed c \<or> is_cfailed d"
  by (cases c; cases d) auto
lemma (in -) fmap_rel_mono2:
  \<open>x \<in> \<langle>A,B\<rangle>fmap_rel \<Longrightarrow>  B \<subseteq>B' \<Longrightarrow> x \<in> \<langle>A,B'\<rangle>fmap_rel\<close>
  by (auto simp: fmap_rel_alt_def)

lemma PAC_checker_l_step_s_PAC_checker_l_step_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(err, err') \<in> Id\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>PAC_checker_l_step_s spec (err, \<V>, A) st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
     (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>'))}
    (PAC_checker_l_step_prep spec' (err', \<D>\<V>, B) st')\<close>
proof -
  have [refine]: \<open>check_del_l spec A (EPAC_Checker_Specification.pac_step.pac_src1 st)
    \<le> \<Down> Id
    (check_del_l spec' B
    (EPAC_Checker_Specification.pac_step.pac_src1 st'))\<close>
    by (auto simp: check_del_l_def)
  have HID: \<open>f = f' \<Longrightarrow> f \<le> \<Down>Id f'\<close> for f f'
    by auto
  show ?thesis
    unfolding PAC_checker_l_step_s_def PAC_checker_l_step_prep_def pac_step.case_eq_if
      prod.simps
    apply (refine_rcg check_linear_combi_l_s_check_linear_combi_l
      check_extension_l2_s_check_extension_l2 add_poly_l_s_add_poly_l)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by (auto simp: is_cfailed_merge_cstatus intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by auto
    subgoal using assms by auto
    apply (rule HID)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto intro!: fmap_rel_fmupd_fmap_rel  intro: fmap_rel_mono2)
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto intro!: fmap_rel_fmdrop_fmap_rel)
    subgoal by auto
    done
qed

lemma PAC_checker_l_step_s_PAC_checker_l_step_s2:
  assumes
    \<open>(st,st')\<in>Id\<close>
    \<open>(spec, spec') \<in> perfectly_shared_polynom (fst (snd err\<V>A))\<close> and
    \<open>((err\<V>A), (err'\<D>\<V>B)) \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r  \<langle>nat_rel, perfectly_shared_polynom (fst (snd err\<V>A))\<rangle>fmap_rel\<close>
  shows \<open>PAC_checker_l_step_s spec (err\<V>A) st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
     (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom (fst (snd err\<V>A)) \<subseteq> perfectly_shared_polynom \<V>'))}
    (PAC_checker_l_step_prep spec' (err'\<D>\<V>B) st')\<close>
  using PAC_checker_l_step_s_PAC_checker_l_step_s[of \<open>fst (snd err\<V>A)\<close> \<open>fst (snd err'\<D>\<V>B)\<close>
    \<open>snd (snd err\<V>A)\<close> \<open>snd (snd err'\<D>\<V>B)\<close> spec spec' \<open>fst (err\<V>A)\<close> \<open>fst (err'\<D>\<V>B)\<close> st st' ] assms
  by (cases err\<V>A; cases err'\<D>\<V>B)
   auto

definition fully_normalize_and_import where
  \<open>fully_normalize_and_import \<V> p = do {
    p \<leftarrow> sort_all_coeffs p;
   (err, p, \<V>) \<leftarrow> import_polyS \<V> p;
   if alloc_failed err
   then RETURN (err, p, \<V>)
   else do {
     p \<leftarrow> normalize_poly_s \<V> p;
     RETURN (err, p, \<V>)
  }}\<close>

fun vars_llist_l where
  \<open>vars_llist_l [] = []\<close> |
  \<open>vars_llist_l (x#xs) = fst x @ vars_llist_l xs\<close>

lemma set_vars_llist_l[simp]: \<open>set(vars_llist_l xs) = vars_llist xs\<close>
  by (induction xs)
    (auto)

lemma vars_llist_l_append[simp]: \<open>vars_llist_l (a @ b) = vars_llist_l a @ vars_llist_l b\<close>
  by (induction a) auto

definition (in -) remap_polys_s_with_err :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, string) shared_vars \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow>
   (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close> where
  \<open>remap_polys_s_with_err spec spec0 = (\<lambda>(\<V>:: (nat, string) shared_vars) A. do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (mem, \<V>) \<leftarrow> import_variablesS (vars_llist_l spec0) \<V>;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> SPEC(\<lambda>b::bool. alloc_failed mem \<or> alloc_failed mem' \<longrightarrow> b);
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      RETURN (error_msg (0 :: nat) c, \<V>, fmempty, [])
   }
   else do {
     (err, \<V>, A) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(err, \<V>,  A'). \<not>is_cfailed err)
       (\<lambda>i (err, \<V>,  A').
          if i \<in># dom_m A
        then  do {
           (err', p, \<V>) \<leftarrow> import_polyS \<V> (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'', \<V>, A'))
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq  \<leftarrow> weak_equality_l_s' \<V> p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
                }})\<close>

lemma full_normalize_poly_alt_def:
  \<open>full_normalize_poly p0 = do {
     p \<leftarrow> sort_all_coeffs p0;
     ASSERT(vars_llist p \<subseteq> vars_llist p0);
     p \<leftarrow> sort_poly_spec p;
     ASSERT(vars_llist p \<subseteq> vars_llist p0);
     RETURN (merge_coeffs0 p)
  }\<close> (is \<open>?A = ?B\<close>)
proof -
  have sort_poly_spec1: \<open>(p,p')\<in> Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close> for p p'
    by auto

  have sort_all_coeffs2: \<open>sort_all_coeffs xs \<le>\<Down>{(ys,ys'). (ys,ys') \<in> Id \<and> vars_llist ys \<subseteq> vars_llist xs} (sort_all_coeffs xs)\<close> for xs
  proof -
    term xs
    have [refine]: \<open>(xs, xs) \<in> \<langle>{(ys,ys'). (ys,ys') \<in> Id \<and> ys \<in> set xs}\<rangle>list_rel\<close>
      by (rule list_rel_mono_strong[of _ Id])
        (auto)
    have [refine]: \<open>(x1a,x1)\<in> Id \<Longrightarrow> sort_coeff x1a  \<le> \<Down> {(ys,ys'). (ys,ys') \<in> Id \<and> set ys \<subseteq> set x1a} (sort_coeff x1)\<close> for x1a x1
      unfolding sort_coeff_def
      by (auto intro!: RES_refine dest: mset_eq_setD)

    show ?thesis
      unfolding sort_all_coeffs_def
      apply refine_vcg
      subgoal by auto
      subgoal by auto
      subgoal by (auto dest!: split_list)
      done
  qed

  have sort_poly_spec1: \<open>(p,p')\<in> Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close> for p p'
    by auto
  have sort_poly_spec2: \<open>(p,p')\<in>Id \<Longrightarrow> sort_poly_spec p \<le> \<Down> {(ys,ys'). (ys,ys') \<in> Id \<and> vars_llist ys \<subseteq> vars_llist p} (sort_poly_spec p')\<close>
    for p p'
    by (auto simp: sort_poly_spec_def intro!: RES_refine dest: vars_llist_mset_eq)
  have \<open>?A \<le> \<Down>Id ?B\<close>
    unfolding full_normalize_poly_def
    by (refine_rcg sort_poly_spec1) auto
  moreover have \<open>?B \<le> \<Down>Id ?A\<close>
    unfolding full_normalize_poly_def
    apply (rule bind_refine[OF sort_all_coeffs2])
    apply (refine_vcg sort_poly_spec2)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
  ultimately show ?thesis
    by auto
qed

definition full_normalize_poly' :: \<open>_\<close> where
  \<open>full_normalize_poly' _ = full_normalize_poly\<close>

lemma full_normalize_poly_s_full_normalize_poly:
  fixes xs :: \<open>sllist_polynomial\<close> and
    \<V> :: \<open>(nat,string)shared_vars\<close>
  assumes
    \<open>(xs, xs') \<in> perfectly_shared_polynom \<V>\<close> and
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>vars_llist xs' \<subseteq> set_mset \<D>\<V>\<close>
  shows \<open>full_normalize_poly_s \<V> xs \<le> \<Down>(perfectly_shared_polynom \<V>) (full_normalize_poly' \<D>\<V> xs')\<close>
proof -
  show ?thesis
    unfolding full_normalize_poly_s_def full_normalize_poly_alt_def full_normalize_poly'_def
    apply (refine_rcg sort_all_coeffs_s_sort_all_coeffs assms
      sort_poly_spec_s_sort_poly_spec merge_coeffs0_s_merge_coeffs0)
    subgoal using assms by auto
    done
qed

lemma remap_polys_l2_with_err_prep_alt_def:
  \<open>remap_polys_l2_with_err_prep spec spec0 = (\<lambda>(\<V>:: (nat, string) vars) A. do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (mem, \<V>) \<leftarrow> SPEC(\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow> set_mset \<V>' = set_mset \<V> \<union> vars_llist spec0);
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_poly \<V> spec else SPEC(\<lambda>_. True);
   failed \<leftarrow> SPEC(\<lambda>b::bool. alloc_failed mem \<or> alloc_failed mem' \<longrightarrow> b);
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      SPEC (\<lambda>(mem, _, _, _). mem = error_msg (0::nat) c)
   }
   else do {
     (err, \<V>, A) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(err, \<V>,  A'). \<not>is_cfailed err)
       (\<lambda>i (err, \<V>,  A').
          if i \<in># dom_m A
          then  do {
           (err', p, \<V>) \<leftarrow> import_poly \<V> (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'', \<V>, A'))
            else do {
              ASSERT(vars_llist p \<subseteq> set_mset \<V>);
              p \<leftarrow> full_normalize_poly' \<V> p;
              eq  \<leftarrow> weak_equality_l' \<V> p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
  }})\<close>
  unfolding full_normalize_poly'_def weak_equality_l'_def
  by(auto simp: remap_polys_l2_with_err_prep_def 
       intro!: ext bind_cong[OF refl])

lemma remap_polys_s_with_err_remap_polys_l2_with_err_prep:
  fixes \<V> :: \<open>(nat, string) shared_vars\<close>
  assumes
    \<V>: \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    AB: \<open>(A,B) \<in> \<langle>nat_rel, Id\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    spec0: \<open>(spec0, spec0') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
  shows
    \<open>remap_polys_s_with_err spec spec0 \<V> A \<le>
    \<Down>{((err, \<V>, A, fspec), (err', \<V>', A', fspec')).
    (err, err') \<in> Id \<and>
   ( \<not>is_cfailed err \<longrightarrow> (fspec, fspec') \<in> perfectly_shared_polynom \<V> \<and>
     ((err, \<V>, A), (err', \<V>', A')) \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r\<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel)}
  (remap_polys_l2_with_err_prep spec' spec0' \<D>\<V> B)\<close>
proof -
  have vars_spec: \<open>(vars_llist_l spec0, vars_llist_l spec0) \<in> Id\<close>
    by auto
  have [refine]: \<open>import_variablesS (vars_llist_l spec0) \<V>
    \<le> \<Down> {((mem, \<V>\<V>), (mem', \<V>\<V>')). mem=mem' \<and> (\<not>alloc_failed mem \<longrightarrow>  (\<V>\<V>, \<V>\<V>') \<in> perfectly_shared_vars_rel \<and>
       perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>\<V>)}
      (SPEC (\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow>  set_mset \<V>' = set_mset \<D>\<V> \<union> vars_llist spec0'))\<close>
    apply (rule import_variablesS_import_variables[OF \<V> vars_spec, THEN order_trans])
    apply (rule ref_two_step'[THEN order_trans])
    apply (rule import_variables_spec)
    apply (use spec0 in \<open>auto simp: conc_fun_RES
      dest!: spec[of _  \<open>\<D>\<V> + mset (vars_llist_l spec0)\<close>]\<close>)
    by (meson perfectly_shared_var_rel_perfectly_shared_polynom_mono subset_eq)

  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by (auto simp: inj_on_def)
  have [refine]: \<open>(x2e, x2c) \<in> perfectly_shared_vars_rel \<Longrightarrow>
    ((CSUCCESS, x2e, fmempty), CSUCCESS, x2c, fmempty)
    \<in>  {((mem,\<A>, A), (mem',\<A>', A')). (mem,mem') \<in> Id \<and>
    (\<not>is_cfailed mem \<longrightarrow> ((\<A>, A), (\<A>', A'))\<in> perfectly_shared_vars_rel \<times>\<^sub>r\<langle>nat_rel, perfectly_shared_polynom \<A>\<rangle>fmap_rel \<and>
      perfectly_shared_polynom x2e \<subseteq> perfectly_shared_polynom \<A>)}\<close>
    for x2e x2c
    by auto
  have [simp]: \<open>A \<propto> xb = B \<propto> xb\<close> for xb
    using AB unfolding fmap_rel_alt_def apply auto by (metis in_dom_m_lookup_iff)
  show ?thesis
    unfolding remap_polys_s_with_err_def remap_polys_l2_with_err_prep_alt_def Let_def
    apply (refine_rcg import_polyS_import_poly 1 full_normalize_poly_s_full_normalize_poly
      weak_equality_l_s_weak_equality_l)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by (auto intro!: RETURN_RES_refine)
    subgoal by auto
    subgoal by auto
    subgoal by (clarsimp intro!: RETURN_RES_refine)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by simp
    subgoal by auto
    subgoal
      by (auto intro!: fmap_rel_fmupd_fmap_rel
        intro: fmap_rel_mono2)
    subgoal by auto
    subgoal
      by (auto intro!: fmap_rel_fmupd_fmap_rel
        intro: fmap_rel_mono2)
    done
qed

definition PAC_checker_l_s where
  \<open>PAC_checker_l_s spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
  (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
  (\<lambda>((bA), n). do {
  ASSERT(n \<noteq> []);
  S \<leftarrow> PAC_checker_l_step_s spec bA (hd n);
  RETURN (S, tl n)
  })
  ((b, A), st);
  RETURN S
  }\<close>


lemma PAC_checker_l_s_PAC_checker_l_prep_s:
  assumes
    \<open>(\<V>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close>
    \<open>(A,B) \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> perfectly_shared_polynom \<V>\<close> and
    \<open>(err, err') \<in> Id\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>PAC_checker_l_s spec (\<V>, A)  err st
    \<le> \<Down>{((err, \<V>', A'), (err', \<D>\<V>', B')).
    (err, err') \<in> Id \<and>
    (\<not>is_cfailed err \<longrightarrow> ((\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>(A',B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel))}
    (PAC_checker_l2 spec' (\<D>\<V>, B) err' st')\<close>
proof -
  show ?thesis
    unfolding PAC_checker_l_s_def PAC_checker_l2_def
    apply (refine_rcg PAC_checker_l_step_s_PAC_checker_l_step_s2
      WHILET_refine[where R = \<open>{((err, \<V>', A'), err', \<D>\<V>', B').
  (err, err') \<in> Id \<and> (\<not> is_cfailed err \<longrightarrow>
  (\<V>', \<D>\<V>') \<in> perfectly_shared_vars_rel \<and>
      (A', B') \<in> \<langle>nat_rel, perfectly_shared_polynom \<V>'\<rangle>fmap_rel \<and>
    perfectly_shared_polynom \<V> \<subseteq> perfectly_shared_polynom \<V>')}\<times>\<^sub>rId\<close>])
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by force
    subgoal by auto
    done
qed

definition full_checker_l_s
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A, spec') \<leftarrow> remap_polys_s_with_err spec' spec ({#}, fmempty, fmempty) A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec' (\<V>, A) b st
     }
  }\<close>
lemma full_checker_l_s_full_checker_l_prep:
  assumes
    \<open>(A,B) \<in> \<langle>nat_rel, Id\<rangle>fmap_rel\<close> and
    \<open>(spec, spec') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    \<open>(st,st')\<in>Id\<close>
  shows \<open>full_checker_l_s spec A st
    \<le> \<Down>{((err, _), (err', _)). (err, err') \<in> Id}
    (full_checker_l_prep spec' B st')\<close>
proof -
  have [refine]: \<open>full_normalize_poly spec \<le> \<Down> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel) (full_normalize_poly spec')\<close>
    using assms by auto
  have [refine]: \<open>(({#}, fmempty, fmempty), {#}) \<in> perfectly_shared_vars_rel\<close>
     by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
   have H: \<open>(x1d, x1a) \<in> perfectly_shared_vars_rel\<close>
     \<open>(x1e, x1b) \<in> \<langle>nat_rel, perfectly_shared_polynom x1d\<rangle>fmap_rel\<close>
     \<open>(x2e, x2b) \<in> perfectly_shared_polynom x1d\<close>
     \<open>(x1c, x1) \<in> Id\<close>
     if \<open>(x, x')
       \<in> {((err, \<V>, A, fspec), err', \<V>', A', fspec').
       (err, err') \<in> Id \<and>
       (\<not> is_cfailed err \<longrightarrow>
       (fspec, fspec') \<in> perfectly_shared_polynom \<V> \<and>
       ((err, \<V>, A), err', \<V>', A')
       \<in> Id \<times>\<^sub>r perfectly_shared_vars_rel \<times>\<^sub>r \<langle>nat_rel, perfectly_shared_polynom \<V>\<rangle>fmap_rel)}\<close>
       \<open>x2a = (x1b, x2b)\<close>
       \<open>x2 = (x1a, x2a)\<close>
       \<open>x' = (x1, x2)\<close>
       \<open>x2d = (x1e, x2e)\<close>
       \<open>x2c = (x1d, x2d)\<close>
       \<open>x = (x1c, x2c)\<close>
       \<open>\<not> is_cfailed x1c\<close>
     for spec' spec'a x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e
     using that by auto
  term PAC_checker_l2
  thm PAC_checker_l_s_PAC_checker_l_prep_s
  show ?thesis
    unfolding full_checker_l_s_def full_checker_l_prep_def
    apply (refine_rcg PAC_checker_l_s_PAC_checker_l_prep_s[THEN order_trans]
      remap_polys_s_with_err_remap_polys_l2_with_err_prep assms)
    subgoal by (auto simp: perfectly_shared_vars_rel_def perfectly_shared_vars_def)
    subgoal using assms by auto
    apply (rule H(1); assumption)
    apply (rule H(2); assumption)
    apply (rule H(3); assumption)
    apply (rule H(4); assumption)
    subgoal by (auto intro!: conc_fun_R_mono)
    done
qed

lemma full_checker_l_s_full_checker_l_prep':
  \<open>(uncurry2 full_checker_l_s, uncurry2 full_checker_l_prep)\<in>
  (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<times>\<^sub>r \<langle>nat_rel, Id\<rangle>fmap_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f
  \<langle>{((err, _), (err', _)). (err, err') \<in> Id}\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI full_checker_l_s_full_checker_l_prep[THEN order_trans])

definition merge_coeff_s :: \<open>(nat,string)shared_vars \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>merge_coeff_s \<V> xs = mergeR (\<lambda>a b. a \<in> set xs \<and> b \<in> set xs)
  (\<lambda>a b. do {
    x \<leftarrow> get_var_nameS \<V> a;
  y \<leftarrow> get_var_nameS \<V> b;
    RETURN(a = b \<or> var_order x y)
  })\<close>

term get_var_nameS
sepref_definition merge_coeff_s_impl
  is \<open>uncurry3 merge_coeff_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeff_s_def mergeR_alt_def var_order'_def[symmetric]
  by sepref

sepref_register merge_coeff_s msort_coeff_s sort_all_coeffs_s
lemmas [sepref_fr_rules] = merge_coeff_s_impl.refine

lemma msort_coeff_s_alt_def:
  \<open>msort_coeff_s \<V> xs = do {
    let zs = COPY xs;
    REC\<^sub>T
     (\<lambda>msortR' xsa. if length xsa \<le> 1 then RETURN (ASSN_ANNOT monom_s_assn xsa) else do {
      let xs1 = ASSN_ANNOT monom_s_assn (take (length xsa div 2) xsa);
      let xs2 = ASSN_ANNOT monom_s_assn (drop (length xsa div 2) xsa);
      as \<leftarrow> msortR' xs1;
      let as = ASSN_ANNOT monom_s_assn as;
      bs \<leftarrow> msortR' xs2;
      let bs = ASSN_ANNOT monom_s_assn bs;
      merge_coeff_s \<V> zs as bs
    })
        xs}\<close>
  unfolding msort_coeff_s_def merge_coeff_s_def[symmetric]
  msortR_alt_def ASSN_ANNOT_def Let_def COPY_def
  by auto

sepref_definition msort_coeff_s_impl
  is \<open>uncurry msort_coeff_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (monom_s_assn)\<^sup>k \<rightarrow>\<^sub>a monom_s_assn\<close>
  supply [[goals_limit=1]]
  unfolding msort_coeff_s_alt_def
  unfolding var_order'_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = msort_coeff_s_impl.refine

sepref_definition sort_all_coeffs_s'_impl
  is \<open>uncurry sort_all_coeffs_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>d \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding sort_all_coeffs_s_def HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] = sort_all_coeffs_s'_impl.refine

(*let's pray that the most stupid compiler on earth, MLton, recognizes that the copy is useless*)
lemma merge_coeffs0_s_alt_def:
  \<open>(RETURN o merge_coeffs0_s) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [p] => if snd (COPY p)= 0 then RETURN [] else RETURN [p]
     | (a # b # p) \<Rightarrow>
  (let (xs, n) = COPY a; (ys, m) = COPY b in
  if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # (COPY p)) else f p
       else if n = 0 then
          do {p \<leftarrow> f (b # (COPY p));
            RETURN p}
       else do {p \<leftarrow> f (b # (COPY p));
            RETURN (a # p)})))
         p\<close>
  unfolding COPY_def Let_def
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs0_s.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: let_to_bind_conv)
  done

lemma [sepref_import_param]: \<open>(((=)), ((=))) \<in> \<langle>uint64_nat_rel\<rangle> list_rel \<rightarrow> \<langle>uint64_nat_rel\<rangle> list_rel \<rightarrow> bool_rel\<close>
proof -
  have \<open>IS_LEFT_UNIQUE (\<langle>uint64_nat_rel\<rangle> list_rel)\<close>
    by (intro safe_constraint_rules)
  moreover have \<open>IS_RIGHT_UNIQUE (\<langle>uint64_nat_rel\<rangle> list_rel)\<close>
    by (intro safe_constraint_rules)
  ultimately show ?thesis
    by (sep_auto simp: IS_LEFT_UNIQUE_def single_valued_def
      simp flip: inv_list_rel_eq)
qed

lemma is_pure_monom_s_assn: \<open>is_pure monom_s_assn\<close>
  \<open>is_pure (monom_s_assn \<times>\<^sub>a int_assn)\<close>
  by (auto simp add: list_assn_pure_conv)

sepref_definition merge_coeffs0_s_impl
  is \<open>RETURN o merge_coeffs0_s\<close>
  :: \<open>poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs0_s_alt_def HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] = merge_coeffs0_s_impl.refine


sepref_definition full_normalize_poly'_impl
  is \<open>uncurry full_normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding full_normalize_poly_s_def
  by sepref

lemma weak_equality_l_s_alt_def:
  \<open>weak_equality_l_s = RETURN oo (\<lambda>p q. p = q)\<close>
  unfolding weak_equality_l_s_def weak_equality_l_s_def by (auto intro!: ext)


lemma [sepref_import_param]
  : \<open>(((=)), ((=))) \<in> \<langle>\<langle>uint64_nat_rel\<rangle> list_rel \<times>\<^sub>r int_rel\<rangle> list_rel \<rightarrow> \<langle>\<langle>uint64_nat_rel\<rangle> list_rel \<times>\<^sub>r int_rel\<rangle> list_rel \<rightarrow> bool_rel\<close>
proof -
  let ?A = \<open>\<langle>\<langle>uint64_nat_rel\<rangle> list_rel \<times>\<^sub>r int_rel\<rangle> list_rel\<close>
  have \<open>IS_LEFT_UNIQUE (\<langle>uint64_nat_rel\<rangle> list_rel)\<close>
    by (intro safe_constraint_rules)
  then have \<open>IS_LEFT_UNIQUE (?A)\<close>
    by (intro safe_constraint_rules)
  moreover have \<open>IS_RIGHT_UNIQUE (\<langle>uint64_nat_rel\<rangle> list_rel)\<close>
    by (intro safe_constraint_rules)
  then have \<open>IS_RIGHT_UNIQUE (?A)\<close>
    by (intro safe_constraint_rules)
  ultimately show ?thesis
    by (sep_auto simp: IS_LEFT_UNIQUE_def single_valued_def
      simp flip: inv_list_rel_eq)
qed

sepref_definition weak_equality_l_s_impl
  is \<open>uncurry weak_equality_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding weak_equality_l_s_alt_def
  by sepref

code_printing constant arl_get_u' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn/ (a,b)/ =>/ a) ((_)),/ Word32.toInt ((_))))"

abbreviation polys_s_assn where
  \<open>polys_s_assn \<equiv> hm_fmap_assn uint64_nat_assn poly_s_assn\<close>


sepref_definition import_monom_no_newS_impl
  is \<open>uncurry (import_monom_no_newS :: (nat,string)shared_vars \<Rightarrow> _ \<Rightarrow>( bool \<times> _) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a (list_assn string_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a list_assn uint64_nat_assn\<close>
  unfolding import_monom_no_newS_def HOL_list.fold_custom_empty
  by sepref
sepref_register import_monom_no_newS import_poly_no_newS check_linear_combi_l_pre_err
lemmas [sepref_fr_rules] =
  import_monom_no_newS_impl.refine weak_equality_l_s_impl.refine

sepref_definition import_poly_no_newS_impl
  is \<open>uncurry (import_poly_no_newS :: (nat,string)shared_vars \<Rightarrow> llist_polynomial \<Rightarrow>( bool \<times> sllist_polynomial) nres)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding import_poly_no_newS_def HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] =
  import_poly_no_newS_impl.refine

definition check_linear_combi_l_pre_err_impl  where
  \<open>check_linear_combi_l_pre_err_impl i pd p mem =
    (if pd then ''The polynomial with id '' @ show (nat_of_uint64 i) @ '' was not found'' else '''') @
    (if p then ''The co-factor from '' @ show (nat_of_uint64 i) @ '' was empty'' else '''')@
    (if mem then ''Memory out'' else '''')\<close>

definition check_mult_l_mult_err_impl where
  \<open>check_mult_l_mult_err_impl p q pq r =
    ''Multiplying '' @ show p @ '' by '' @ show q @ '' gives '' @ show pq @ '' and not '' @ show r\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_linear_combi_l_pre_err_impl x y))),
   uncurry3 (check_linear_combi_l_pre_err)) \<in> uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding check_linear_combi_l_pre_err_impl_def check_linear_combi_l_pre_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

lemma vars_llist_in_s_single: \<open>RETURN (vars_llist_in_s \<V> [(xs, a)]) =
  REC\<^sub>T (\<lambda>f xs. case xs of
    [] \<Rightarrow> RETURN True
  | x # xs \<Rightarrow> do {
  b \<leftarrow> is_new_variableS x \<V>;
  if b then RETURN False
  else f xs
    }) (xs)\<close>
  apply (subst eq_commute)
  apply (cases \<V>)
  apply (induction xs)
  subgoal
    by (subst RECT_unfold, refine_mono)
     (auto simp: vars_llist_in_s_def)
  subgoal
    by (subst RECT_unfold, refine_mono)
     (auto simp: vars_llist_in_s_def is_new_variableS_def)
  done

lemma vars_llist_in_s_alt_def: \<open>(RETURN oo vars_llist_in_s) \<V> xs =
  REC\<^sub>T (\<lambda>f xs. case xs of
    [] \<Rightarrow> RETURN True
  | (x, a) # xs \<Rightarrow> do {
  b \<leftarrow> RETURN (vars_llist_in_s \<V> [(x, a)]);
  if \<not>b then RETURN False
  else f xs
    }) xs\<close>
  apply (subst eq_commute)
  apply (cases \<V>)
  apply (induction xs)
  subgoal
    by (subst RECT_unfold, refine_mono)
     (auto simp: vars_llist_in_s_def)
  subgoal
    by (subst RECT_unfold, refine_mono)
     (auto simp: vars_llist_in_s_def is_new_variableS_def split: prod.splits)
  done

sepref_definition vars_llist_in_s_impl
  is \<open>uncurry (RETURN oo vars_llist_in_s)\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding vars_llist_in_s_alt_def
    vars_llist_in_s_single
  by sepref
lemmas [sepref_fr_rules] = vars_llist_in_s_impl.refine

definition check_linear_combi_l_s_dom_err_impl :: \<open>_ \<Rightarrow> uint64 \<Rightarrow> _\<close>  where
  \<open>check_linear_combi_l_s_dom_err_impl x p =
    ''Poly not found in CL from x '' @ show (nat_of_uint64 p)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_linear_combi_l_s_dom_err_impl)),
    uncurry (check_linear_combi_l_s_dom_err)) \<in> poly_s_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_linear_combi_l_s_dom_err_def check_linear_combi_l_s_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done
sepref_register check_linear_combi_l_s_dom_err_impl mult_poly_s normalize_poly_s

sepref_definition normalize_poly_sharedS_impl
  is \<open>uncurry normalize_poly_sharedS\<close>
  :: \<open> shared_vars_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_sharedS_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_sharedS_impl.refine
  mult_poly_s_impl.refine
lemma merge_coeffs_s_alt_def:
  \<open>(RETURN o merge_coeffs_s) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [_] => RETURN p
     | ((xs, n) # (ys, m) # p) \<Rightarrow>
      (if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # COPY p) else f p
       else do {p \<leftarrow> f ((ys, m) # p); RETURN ((xs, n) # p)})))
         p\<close>
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs_s.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal for x p y q
    by (subst RECT_unfold, refine_mono) auto
  done

sepref_definition merge_coeffs_s_impl
  is \<open>(RETURN o merge_coeffs_s)\<close>
  :: \<open>poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding merge_coeffs_s_alt_def
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] = merge_coeffs_s_impl.refine

sepref_definition normalize_poly_s_impl
  is \<open>uncurry normalize_poly_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding normalize_poly_s_def
  by sepref

lemmas [sepref_fr_rules] = normalize_poly_s_impl.refine

sepref_definition mult_poly_full_s_impl
  is \<open>uncurry2 mult_poly_full_s\<close>
  :: \<open>shared_vars_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a poly_s_assn\<close>
  unfolding mult_poly_full_s_def
  by sepref

lemmas [sepref_fr_rules] = mult_poly_full_s_impl.refine
  add_poly_l_prep_impl.refine

sepref_register add_poly_l_s

sepref_definition linear_combi_l_prep_s_impl
  is \<open>uncurry3 linear_combi_l_prep_s\<close>
  :: \<open>uint64_nat_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a
  (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn))\<^sup>d  \<rightarrow>\<^sub>a  poly_s_assn \<times>\<^sub>a (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn)) \<times>\<^sub>a status_assn raw_string_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding linear_combi_l_prep_s_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric] conv_to_is_Nil
  unfolding is_Nil_def
    HOL_list.fold_custom_empty
  apply (rewrite in \<open>op_HOL_list_empty\<close> annotate_assn[where A=\<open>poly_s_assn\<close>])
  by sepref

lemmas [sepref_fr_rules] = linear_combi_l_prep_s_impl.refine

definition check_linear_combi_l_s_mult_err_impl :: \<open>_ \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_linear_combi_l_s_mult_err_impl x p =
  ''Unequal polynom found in CL '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p) @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) x)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_linear_combi_l_s_mult_err_impl)),
    uncurry (check_linear_combi_l_s_mult_err)) \<in> poly_s_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_linear_combi_l_s_mult_err_impl_def check_linear_combi_l_s_mult_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_linear_combi_l_s_impl
  is \<open>uncurry5 check_linear_combi_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
  (list_assn (poly_assn \<times>\<^sub>a uint64_nat_assn))\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a poly_s_assn
  \<close>
  unfolding check_linear_combi_l_s_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

sepref_register fmlookup'
lemma check_extension_l2_s_alt_def:
  \<open>check_extension_l2_s spec A \<V> i v p = do {
  n \<leftarrow> is_new_variableS v \<V>;
  let t = fmlookup' i A;
  pre \<leftarrow> RETURN (t = None);
  let pre = pre \<and> n;
  let nonew = vars_llist_in_s \<V> p;
  (mem, p, \<V>) \<leftarrow> import_polyS \<V> p;
  let pre = (pre \<and> \<not>alloc_failed mem);
  if \<not>pre
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c, [], \<V>, 0)
  } else do {
      if \<not>nonew
      then do {
        c \<leftarrow> check_extension_l_s_new_var_multiple_err v p;
        RETURN (error_msg i c, [], \<V>, 0)
      }
      else do {
        (mem', \<V>, v') \<leftarrow> import_variableS v \<V>;
        if alloc_failed mem'
        then do {
          c \<leftarrow> check_extension_l_dom_err i;
          RETURN (error_msg i c, [], \<V>, 0)
        } else
        do {
         p2 \<leftarrow> mult_poly_full_s \<V> p p;
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         q \<leftarrow> add_poly_l_s \<V> (p2, p'');
         eq \<leftarrow> weak_equality_l_s q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v')
         } else do {
          c \<leftarrow> check_extension_l_s_side_cond_err v p p'' q;
          RETURN (error_msg i c, [], \<V>, v')
        }
      }
     }
  }
  }\<close>
  unfolding check_extension_l2_s_def fmlookup'_def[symmetric] Let_def
     in_dom_m_lookup_iff
   by (auto intro!: bind_cong[OF refl])

definition uminus_poly :: \<open>_ \<Rightarrow> _\<close> where
  \<open>uminus_poly p' = map (\<lambda>(a, b). (a, - b)) p'\<close>

lemma [sepref_import_param]: \<open>(uminus_poly, uminus_poly) \<in> \<langle>monom_s_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<rightarrow> \<langle>monom_s_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
proof -
  have \<open>(a, a') \<in> \<langle>monom_s_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
    (EPAC_Efficient_Checker_Synthesis.uminus_poly a,
     EPAC_Efficient_Checker_Synthesis.uminus_poly a')
    \<in> \<langle>monom_s_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> for a a'
    apply (induction a arbitrary: a')
    subgoal by (auto simp: uminus_poly_def)
    subgoal for a as a'
      by (cases a'; cases a)
        (auto simp: uminus_poly_def)
    done
  then show ?thesis
    by (auto intro!: frefI)
qed

sepref_register import_monomS import_polyS

sepref_definition import_monomS_impl
  is \<open>uncurry import_monomS\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a monom_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_monomS_def
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] =
  import_monomS_impl.refine

sepref_definition import_polyS_impl
  is \<open>uncurry import_polyS\<close>
  :: \<open>shared_vars_assn\<^sup>d *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn\<close>
  supply [[goals_limit=1]]
  unfolding import_polyS_def
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] =
  import_polyS_impl.refine

definition check_extension_l_s_new_var_multiple_err_impl :: \<open>String.literal \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_s_new_var_multiple_err_impl x p =
  ''Variable already defined '' @ show x @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p)\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry (return oo (check_extension_l_s_new_var_multiple_err_impl)),
    uncurry (check_extension_l_s_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_s_new_var_multiple_err_impl_def check_extension_l_s_new_var_multiple_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_s_side_cond_err_impl :: \<open>String.literal \<Rightarrow> _ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_s_side_cond_err_impl x p p' q' =
  ''p^2- p != 0 '' @ show x @
  '' but '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p) @
  '' and '' @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) p') @
   '' and ''  @ show (map (\<lambda>(a,b). (map nat_of_uint64 a, b)) q')\<close>

abbreviation comp4 (infixl "oooo" 55) where "f oooo g \<equiv> \<lambda>x. f ooo (g x)"
abbreviation comp5 (infixl "ooooo" 55) where "f ooooo g \<equiv> \<lambda>x. f oooo (g x)"

lemma [sepref_fr_rules]:
  \<open>(uncurry3 (return oooo (check_extension_l_s_side_cond_err_impl)),
    uncurry3 (check_extension_l_s_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k*\<^sub>a poly_s_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_s_side_cond_err_impl_def check_extension_l_s_side_cond_err_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_register mult_poly_full_s weak_equality_l_s check_extension_l_s_side_cond_err check_extension_l2_s
     check_linear_combi_l_s is_cfailed check_del_l

sepref_definition check_extension_l_impl
  is \<open>uncurry5 check_extension_l2_s\<close>
    :: \<open>poly_s_assn\<^sup>k *\<^sub>a polys_s_assn\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
    string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a poly_s_assn \<times>\<^sub>a shared_vars_assn  \<times>\<^sub>a uint64_nat_assn
  \<close>
  supply [[goals_limit=1]]
  unfolding check_extension_l2_s_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    not_not is_None_def
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
    zero_uint64_nat_def[symmetric]
  by sepref


lemma [sepref_fr_rules]:
  \<open>(return o is_cfailed, RETURN o is_cfailed) \<in> (status_assn raw_string_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply sepref_to_hoare
  apply (sep_auto)
  apply (case_tac x; case_tac xi; sep_auto)+
  done

sepref_definition check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>apolys_s_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding check_del_l_def
  by sepref

lemmas [sepref_fr_rules] =
  check_extension_l_impl.refine
  check_linear_combi_l_s_impl.refine
  check_del_l_impl.refine

sepref_definition PAC_checker_l_step_s_impl
  is \<open>uncurry2 PAC_checker_l_step_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn)\<^sup>d *\<^sub>a
         (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn)\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn
  \<close>
  supply [[goals_limit = 1]]
  supply [intro] = is_Mult_lastI
  unfolding PAC_checker_l_step_s_def Let_def
    pac_step.case_eq_if
    HOL_list.fold_custom_empty
  by sepref

lemmas [sepref_fr_rules] = PAC_checker_l_step_s_impl.refine

fun vars_llist_s2 :: \<open>_ \<Rightarrow> _ list\<close> where
  \<open>vars_llist_s2 [] = []\<close> |
  \<open>vars_llist_s2 ((a,_) # xs) = a @ vars_llist_s2 xs\<close>

lemma [sepref_import_param]:
  \<open>(vars_llist_s2, vars_llist_s2) \<in> \<langle>\<langle>string_rel\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<rightarrow> \<langle>string_rel\<rangle>list_rel\<close>
  apply (intro fun_relI)
  subgoal for a b
    apply (induction a arbitrary: b)
    subgoal by auto
    subgoal for a as b
      by (cases a, cases b)
       (force simp: list_rel_append1)+
    done
  done
sepref_register PAC_checker_l_step_s
lemma step_rewrite_pure:
  fixes K :: \<open>('olbl \<times> 'lbl) set\<close>
  shows
    \<open>pure (p2rel (\<langle>K, V, R\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V) (pure R)\<close>
  apply (intro ext)
  apply (case_tac x; case_tac xa)
  apply simp_all
  apply (simp_all add: relAPP_def p2rel_def pure_def)
  unfolding pure_def[symmetric] list_assn_pure_conv
  apply (auto simp: pure_def relAPP_def)
  done

lemma safe_epac_step_rel_assn[safe_constraint_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow> CONSTRAINT is_pure V \<Longrightarrow> CONSTRAINT is_pure R \<Longrightarrow>
  CONSTRAINT is_pure (EPAC_Checker.pac_step_rel_assn K V R)\<close>
  by (auto simp: step_rewrite_pure(1)[symmetric] is_pure_conv)

sepref_definition PAC_checker_l_s_impl
  is \<open>uncurry3 PAC_checker_l_s\<close>
  :: \<open>poly_s_assn\<^sup>k *\<^sub>a (shared_vars_assn \<times>\<^sub>a polys_s_assn)\<^sup>d *\<^sub>a(status_assn raw_string_assn)\<^sup>d *\<^sub>a
  (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>d \<rightarrow>\<^sub>a
  status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn
  \<close>
  supply [[goals_limit = 1]]
  supply [intro] = is_Mult_lastI
  unfolding PAC_checker_l_s_def Let_def
    pac_step.case_eq_if
    neq_Nil_conv
    conv_to_is_Nil is_Nil_def
  by sepref

lemmas [sepref_fr_rules] = PAC_checker_l_s_impl.refine

definition memory_out_msg :: \<open>string\<close> where
  \<open>memory_out_msg = ''memory out''\<close>

lemma [sepref_fr_rules]: \<open>(uncurry0 (return memory_out_msg), uncurry0 (RETURN memory_out_msg)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding memory_out_msg_def
  by sepref_to_hoare sep_auto

definition (in -) remap_polys_l2_with_err_s :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (nat, string) shared_vars \<Rightarrow>
   (string code_status \<times> (nat, string) shared_vars \<times> (nat, sllist_polynomial) fmap \<times> sllist_polynomial) nres\<close> where
  \<open>remap_polys_l2_with_err_s spec spec0 A (\<V> :: (nat, string) shared_vars) =  do{
   ASSERT(vars_llist spec \<subseteq> vars_llist spec0);
    n \<leftarrow> upper_bound_on_dom A;
   (mem, \<V>) \<leftarrow> import_variablesS (vars_llist_s2 spec0) \<V>;
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_polyS \<V> spec else RETURN (mem, [], \<V>);
   failed \<leftarrow> RETURN (alloc_failed mem \<or> alloc_failed mem' \<or> n \<ge> 2^64);
   if failed
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     RETURN (error_msg (0::nat) c, \<V>, fmempty, [])
   }
   else do {
     (err, A, \<V>) \<leftarrow>  nfoldli ([0..<n]) (\<lambda>(err, A', \<V>). \<not>is_cfailed err)
       (\<lambda>i (err, A'  :: (nat, sllist_polynomial) fmap, \<V> :: (nat,string) shared_vars).
          if i \<in># dom_m A
          then  do {
           (err', p, \<V>  :: (nat,string) shared_vars) \<leftarrow> import_polyS (\<V> :: (nat,string) shared_vars) (the (fmlookup A i));
            if alloc_failed err' then RETURN((CFAILED ''memory out'',  A', \<V>  :: (nat,string) shared_vars))
            else do {
              p \<leftarrow> full_normalize_poly_s \<V> p;
              eq  \<leftarrow> weak_equality_l_s p spec;
              RETURN((if eq then CFOUND else CSUCCESS),  fmupd i p A', \<V>  :: (nat,string) shared_vars)
            }
          } else RETURN (err, A', \<V>  :: (nat,string) shared_vars))
       (CSUCCESS, fmempty :: (nat, sllist_polynomial) fmap,  \<V> :: (nat,string) shared_vars);
     RETURN (err, \<V>, A, spec)
  }}\<close>

lemma set_vars_llist_s2 [simp]: \<open>set (vars_llist_s2 b) = vars_llist b\<close>
  by (induction b)
    (auto simp: vars_llist_def)

sepref_register upper_bound_on_dom import_variablesS vars_llist_s2 memory_out_msg

sepref_definition import_variablesS_impl
  is \<open>uncurry import_variablesS\<close>
  :: \<open>(list_assn string_assn)\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a memory_allocation_assn \<times>\<^sub>a shared_vars_assn\<close>
  unfolding import_variablesS_def
  by sepref

lemmas [sepref_fr_rules] =
  import_variablesS_impl.refine full_normalize_poly'_impl.refine
lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow> ((return o CFAILED), RETURN o CFAILED) \<in> R\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  apply sepref_to_hoare
  apply sep_auto
  by (smt ent_refl_true is_pure_conv merge_pure_star pure_def)

sepref_definition remap_polys_l2_with_err_s_impl
  is \<open>uncurry3 remap_polys_l2_with_err_s\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a shared_vars_assn\<^sup>d \<rightarrow>\<^sub>a
  status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn \<times>\<^sub>a poly_s_assn\<close>
  supply [[goals_limit=1]]
  supply [split] = option.splits
  unfolding remap_polys_l2_with_err_s_def pow_2_64
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    memory_out_msg_def[symmetric]
    op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
  unfolding
    HOL_list.fold_custom_empty
  apply (subst while_upt_while_direct)
  apply simp
  apply (rewrite in \<open>(_, \<hole>, _)\<close> annotate_assn[where A=\<open>polys_s_assn\<close>])
  apply (rewrite at \<open>fmupd \<hole>\<close> uint64_of_nat_conv_def[symmetric])
  by sepref

lemmas [sepref_fr_rules] =
  remap_polys_l2_with_err_s_impl.refine

definition full_checker_l_s2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_s2 spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A, spec') \<leftarrow> remap_polys_l2_with_err_s spec' spec A ({#}, fmempty, fmempty);
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l_s spec' (\<V>, A) b st
     }
   }\<close>

sepref_register remap_polys_l2_with_err_s full_checker_l_s2 PAC_checker_l_s

sepref_definition full_checker_l_s2_impl
  is \<open>uncurry2 full_checker_l_s2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>k *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
  status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn\<close>
  unfolding full_checker_l_s2_def
     empty_shared_vars_def[symmetric]
  by sepref
local_setup \<open>
  let
    val version =
      trim_line (#1 (Isabelle_System.bash_output ("cd $ISAFOL/ && git rev-parse --short HEAD || echo unknown")))
  in
    Local_Theory.define
      ((\<^binding>\<open>version\<close>, NoSyn),
        ((\<^binding>\<open>version_def\<close>, []), HOLogic.mk_literal version)) #> #2
  end
\<close>

declare version_def [code]

definition uint32_of_uint64 :: \<open>uint64 \<Rightarrow> uint32\<close> where
  \<open>uint32_of_uint64 n = uint32_of_nat (nat_of_uint64 n)\<close>

lemma [code]: \<open>hashcode n = uint32_of_uint64 (n AND 4294967295)\<close> for n :: uint64
  unfolding hashcode_uint64_def uint32_of_uint64_def by auto

(*TODO this is a copy paste because of the order of the merge *)
code_printing code_module Uint64 \<rightharpoonup> (SML) \<open>(* Test that words can handle numbers between 0 and 63 *)
val _ = if 6 <= Word.wordSize then () else raise (Fail ("wordSize less than 6"));

structure Uint64 : sig
  eqtype uint64;
  val zero : uint64;
  val one : uint64;
  val fromInt : IntInf.int -> uint64;
  val toInt : uint64 -> IntInf.int;
  val toFixedInt : uint64 -> Int.int;
  val toLarge : uint64 -> LargeWord.word;
  val fromLarge : LargeWord.word -> uint64
  val fromFixedInt : Int.int -> uint64
  val toWord32: uint64 -> Word32.word
  val plus : uint64 -> uint64 -> uint64;
  val minus : uint64 -> uint64 -> uint64;
  val times : uint64 -> uint64 -> uint64;
  val divide : uint64 -> uint64 -> uint64;
  val modulus : uint64 -> uint64 -> uint64;
  val negate : uint64 -> uint64;
  val less_eq : uint64 -> uint64 -> bool;
  val less : uint64 -> uint64 -> bool;
  val notb : uint64 -> uint64;
  val andb : uint64 -> uint64 -> uint64;
  val orb : uint64 -> uint64 -> uint64;
  val xorb : uint64 -> uint64 -> uint64;
  val shiftl : uint64 -> IntInf.int -> uint64;
  val shiftr : uint64 -> IntInf.int -> uint64;
  val shiftr_signed : uint64 -> IntInf.int -> uint64;
  val set_bit : uint64 -> IntInf.int -> bool -> uint64;
  val test_bit : uint64 -> IntInf.int -> bool;
end = struct

type uint64 = Word64.word;

val zero = (0wx0 : uint64);

val one = (0wx1 : uint64);

fun fromInt x = Word64.fromLargeInt (IntInf.toLarge x);

fun toInt x = IntInf.fromLarge (Word64.toLargeInt x);

fun toFixedInt x = Word64.toInt x;

fun fromLarge x = Word64.fromLarge x;

fun fromFixedInt x = Word64.fromInt x;

fun toLarge x = Word64.toLarge x;

fun toWord32 x = Word32.fromLarge x

fun plus x y = Word64.+(x, y);

fun minus x y = Word64.-(x, y);

fun negate x = Word64.~(x);

fun times x y = Word64.*(x, y);

fun divide x y = Word64.div(x, y);

fun modulus x y = Word64.mod(x, y);

fun less_eq x y = Word64.<=(x, y);

fun less x y = Word64.<(x, y);

fun set_bit x n b =
  let val mask = Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word64.orb (x, mask)
     else Word64.andb (x, Word64.notb mask)
  end

fun shiftl x n =
  Word64.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word64.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word64.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word64.andb (x, Word64.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word64.fromInt 0

val notb = Word64.notb

fun andb x y = Word64.andb(x, y);

fun orb x y = Word64.orb(x, y);

fun xorb x y = Word64.xorb(x, y);

end (*struct Uint64*)
\<close>

code_printing constant arl_get_u' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((fn/ (a,b)/ =>/ a) ((_)),/ Word64.toInt (Uint64.toLarge ((_)))))"

definition uint32_of_uint64' where
  [symmetric, code]: "uint32_of_uint64' = uint32_of_uint64"
code_printing constant uint32_of_uint64' \<rightharpoonup> (SML) "Uint64.toWord32 ((_))"
thm hashcode_literal_def[unfolded hashcode_list_def]

definition string_nth where
  \<open>string_nth s x = literal.explode s ! x\<close>

definition string_nth' where
  \<open>string_nth' s x = literal.explode s ! nat x\<close>

lemma [code]: \<open>string_nth s x = string_nth' s (int x)\<close>
  unfolding string_nth_def string_nth'_def
  by auto

definition string_size :: \<open>String.literal\<Rightarrow>nat\<close> where
  \<open>string_size s = size s\<close>

definition string_size' where
  [symmetric,code]: \<open>string_size' = string_size\<close>

lemma [code]: \<open>size = string_size\<close>
  unfolding string_size_def ..

code_printing constant string_nth' \<rightharpoonup> (SML) "(String.sub/ ((_),/ IntInf.toInt ((integer'_of'_int ((_))))))"
code_printing constant string_size' \<rightharpoonup> (SML) "nat'_of'_integer ((IntInf.fromInt ((String.size ((_))))))"

function hashcode_eff where 
  [simp del]: \<open>hashcode_eff s h i = (if i \<ge> size s then h else hashcode_eff s (h * 33 + hashcode (s ! i)) (i+1))\<close>
  by auto
termination
  by (relation \<open>measure (\<lambda>(s,h,i). size s -i)\<close>)
    auto

definition hashcode_eff' where
  \<open>hashcode_eff' s h i = hashcode_eff (String.explode s) h i\<close>

lemma hashcode_eff'_code[code]:
   \<open>hashcode_eff' s h i = (if i \<ge> size s then h else hashcode_eff' s (h * 33 + hashcode (string_nth s i)) (i+1))\<close>
  unfolding hashcode_eff'_def string_nth_def  hashcode_eff.simps[symmetric] size_literal.rep_eq
  ..

lemma [simp]: \<open>length s \<le> i \<Longrightarrow> hashcode_eff s h i = h\<close>
  by (subst hashcode_eff.simps)
   auto
lemma [simp]: \<open>hashcode_eff (a # s) h (Suc i) = hashcode_eff (s) h (i)\<close>
  apply (induction "s" h "i" rule: hashcode_eff.induct)
  subgoal
    apply (subst (2) hashcode_eff.simps)
    apply (subst (1) hashcode_eff.simps)
    apply auto
    done
  done


lemma hashcode_eff_def[unfolded hashcode_eff'_def[symmetric], code]:
  \<open>hashcode s = hashcode_eff (String.explode s)5381 0\<close> for s::String.literal
proof -
  have H: \<open>length (literal.explode s) = size s\<close>
    by (simp add: size_literal.rep_eq)
  have [simp]: \<open>foldl (\<lambda>h xa. h * 33 + hashcode ((xs @ [x]) ! xa)) 5381 [0..<length xs] =
    foldl (\<lambda>h x. h * 33 + hashcode (xs ! x)) 5381 [0..<length xs]\<close> for xs x
    by (rule foldl_cong) auto
  have \<open>foldl (\<lambda>h x. h * 33 + hashcode x) 5381 (s) =
    foldl (\<lambda>h x. h * 33 + hashcode (s ! x)) 5381
     [0..<length (s)]\<close> for s
    by (induction s rule: rev_induct) auto
  then have 0: \<open>hashcode s = foldl (\<lambda>h x. h * 33 + hashcode (string_nth s x)) 5381 [0..<size s]\<close>
    unfolding string_nth_def
    unfolding hashcode_literal_def[unfolded hashcode_list_def] size_literal.rep_eq
    by blast

  have upt: \<open>\<not> Suc (length s) \<le> i \<Longrightarrow> [i..<Suc (length s)] = i # [Suc i..<Suc (length s)]\<close> for i s
    by (meson leI upt_rec)

  have [simp]: \<open>foldl (\<lambda>h x. h * 33 + hashcode ((a # s) ! x)) h [Suc i..<Suc (length s)] =
    foldl (\<lambda>h x. h * 33 + hashcode (s ! x)) h [i..<(length s)]\<close> for a s i h
  proof -
    have \<open>foldl (\<lambda>h x. h * 33 + hashcode ((a # s) ! x)) h [Suc i..<Suc (length s)] = 
      foldl (\<lambda>h x. h * 33 + hashcode ((a # s) ! x)) h (map Suc [i..<(length s)])\<close>
      using map_Suc_upt by presburger
    also have \<open>\<dots> = foldl (\<lambda>aa x. aa * 33 + hashcode (s ! x)) h [i..<length s]\<close>
      unfolding foldl_map by (rule foldl_cong) auto
    finally show ?thesis .
  qed
   
  have H': \<open>foldl (\<lambda>h x. h * 33 + hashcode (s ! x)) h [i..<length s] =
    hashcode_eff s h i\<close> for i h s
    unfolding string_nth_def H[symmetric]
    supply [simp del] = upt.simps
    apply (induction \<open>s\<close> arbitrary: h)
    subgoal
      by (subst hashcode_eff.simps)
       auto
    subgoal
      by (subst hashcode_eff.simps)
       (auto simp: upt)
    done
  show ?thesis
    unfolding 0 H[symmetric] string_nth_def H'
    ..
qed

export_code "hashcode :: String.literal \<Rightarrow> _" 
  in SML_imp module_name PAC_Checker
(*make array_blit compatible with unsafe*)
code_printing code_module "array_blit" \<rightharpoonup> (SML)
    \<open>
   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = if IntInf.toInt i >= Array.length a then v 
       else Array.sub(a,IntInf.toInt i) handle Overflow => v
    fun array_upd_oo f i x a () = 
      if IntInf.toInt i >= Array.length a then f ()
      else
        (Array.update(a,IntInf.toInt i,x); a) handle Overflow => f ()

\<close>

export_code
    full_checker_l_s2_impl int_of_integer Del CL nat_of_integer String.implode remap_polys_l2_with_err_s_impl
    PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
    fully_normalize_poly_impl empty_shared_vars_int_impl
    PAC_checker_l_s_impl PAC_checker_l_step_s_impl version
  in SML_imp module_name PAC_Checker
  file_prefix "checker"


compile_generated_files _
  external_files
    \<open>code/parser.sml\<close>
    \<open>code/pasteque.sml\<close>
    \<open>code/pasteque.mlb\<close>
  where \<open>fn dir =>
  let

    val exec = Generated_Files.execute (Path.append dir (Path.basic "code"));
    val _ = exec \<open>Copy files\<close>
      ("cp checker.ML " ^ ((File.bash_path \<^path>\<open>$ISAFOL\<close>) ^ "/PAC_Checker2/code/checker.ML"));
(*       val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^ " " ^
            "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
            "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb"); *)
    in () end\<close>


section \<open>Correctness theorem\<close>

context poly_embed
begin

definition fully_epac_assn where
  \<open>fully_epac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel, 
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>


text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

  \<close>

lemma remap_polys_l2_with_err_s_remap_polys_s_with_err:
  assumes \<open>((spec, a, b, c), (spec', a', c', b')) \<in> Id\<close>
  shows \<open>remap_polys_l2_with_err_s spec a b c
    \<le> \<Down> Id
  (remap_polys_s_with_err spec' a' b' c')\<close>
proof -
  have [refine]: \<open>(A, A') \<in> Id \<Longrightarrow> upper_bound_on_dom A
    \<le> \<Down> {(n, dom). dom = set [0..<n]} (SPEC (\<lambda>dom. set_mset (dom_m A') \<subseteq> dom \<and> finite dom))\<close> for A A'
    unfolding upper_bound_on_dom_def
    apply (rule RES_refine)
    apply (auto simp: upper_bound_on_dom_def)
    done
  have 3: \<open>(n, dom) \<in> {(n, dom). dom = set [0..<n]} \<Longrightarrow>
    ([0..<n], dom) \<in> \<langle>nat_rel\<rangle>list_set_rel\<close> for n dom
    by (auto simp: list_set_rel_def br_def)
  have 4: \<open>(p,q) \<in> Id \<Longrightarrow>
    weak_equality_l p spec \<le> \<Down>Id (weak_equality_l q spec)\<close> for p q spec
    by auto

  have 6: \<open>a = b \<Longrightarrow> (a, b) \<in> Id\<close> for a b
    by auto

  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  have [simp]: \<open>vars_llist_s2 x = vars_llist_l x\<close> for x
    by (induction x rule: vars_llist_s2.induct) auto
  show ?thesis
    supply [[goals_limit=1]]
    unfolding remap_polys_l2_with_err_s_def remap_polys_s_with_err_def
    apply (refine_rcg
      LFOc_refine[where R= \<open>{((a,b,c), (a',b',c')). ((a,b,c), (a',c',b'))\<in>Id}\<close>])
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule 3)
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    apply (rule id)
    subgoal unfolding weak_equality_l_s'_def by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma full_checker_l_s2_full_checker_l_s:
  \<open>(uncurry2 full_checker_l_s2, uncurry2 full_checker_l_s) \<in> (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
proof -
  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding uncurry_def
    apply clarify
    unfolding full_checker_l_s2_def
      full_checker_l_s_def
    apply (refine_rcg remap_polys_l2_with_err_s_remap_polys_s_with_err)
    apply (rule id)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule id)
    subgoal by auto
    done
qed

lemma full_poly_input_assn_alt_def:
  \<open>full_poly_input_assn = (hr_comp
  (hr_comp (hr_comp polys_assn_input (\<langle>nat_rel, Id\<rangle>fmap_rel))
  (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
  polys_rel)\<close>
proof -
  have [simp]: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def)
    by (metis (no_types, hide_lams) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
  show ?thesis
    unfolding full_poly_input_assn_def
    by auto
qed

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_s2_impl,
 uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
\<in> full_poly_assn\<^sup>k *\<^sub>a full_poly_input_assn\<^sup>k *\<^sub>a
  fully_epac_assn\<^sup>k \<rightarrow>\<^sub>a hr_comp (status_assn raw_string_assn \<times>\<^sub>a shared_vars_assn \<times>\<^sub>a polys_s_assn)
            {((err, _), err', _). (err, err') \<in> code_status_status_rel}\<close>
proof -
  have 1: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
    (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
    polys_rel) \<times>\<^sub>r
    \<langle>p2rel
    (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
    var_rel\<rangle>EPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>(({((err, _), err', _).
    (err, err') \<in> Id} O
    {((b, A, st), b', A', st').
    (\<not> is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st') \<in> Id) \<and>
    (b, b') \<in> Id}) O
    {((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A')
    \<in> code_status_status_rel \<times>\<^sub>r
    vars_rel2 err \<times>\<^sub>r
    {(xs, ys).
    \<not> is_cfailed err \<longrightarrow>
    (xs, ys) \<in> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel \<and>
    (\<forall>i\<in>#dom_m xs. vars_llist (xs \<propto> i) \<subseteq> \<V>)}}) O
    {((st, G), st', G').
    (st, st') \<in> status_rel \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<rangle>nres_rel\<close>
    using full_checker_l_s2_full_checker_l_s[
      FCOMP full_checker_l_s_full_checker_l_prep',
      FCOMP full_checker_l_prep_full_checker_l2',
      FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
      full_poly_input_assn_def[symmetric]
      fully_epac_assn_def[symmetric]
      code_status_assn_def[symmetric]
      full_vars_assn_def[symmetric]
      polys_rel_full_polys_rel
      hr_comp_prod_conv
      full_polys_assn_def[symmetric]
      full_poly_input_assn_alt_def[symmetric]] by auto
  have 2: \<open>A \<subseteq> B \<Longrightarrow> \<langle>A\<rangle>nres_rel \<subseteq> \<langle>B\<rangle>nres_rel\<close> for A B
    by (auto simp: nres_rel_def conc_fun_R_mono conc_trans_additional(6))

  have 3: \<open>(uncurry2 full_checker_l_s2, uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel \<times>\<^sub>r
    (\<langle>nat_rel, Id\<rangle>fmap_rel O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O
    polys_rel) \<times>\<^sub>r
    \<langle>p2rel
    (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel,
    var_rel\<rangle>EPAC_Checker.pac_step_rel_raw)\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>{((err, _), err', _). (err, err') \<in> code_status_status_rel}\<rangle>nres_rel\<close>
    apply (rule set_mp[OF _ 1])
    unfolding fref_param1[symmetric]
    apply (rule fun_rel_mono)
    apply auto[]
    apply (rule 2)
    apply auto
    done

  have 4: \<open>\<langle>nat_rel, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def)
    by (metis (no_types, hide_lams) fmap_ext_fmdom fmlookup_dom_iff fset_eqI option.sel)
  have H: \<open>full_poly_assn = (hr_comp poly_assn
    (\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O fully_unsorted_poly_rel O mset_poly_rel))\<close>
    \<open>full_poly_input_assn = hr_comp polys_assn_input
   ((Id O \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel) O polys_rel)\<close>
    unfolding full_poly_assn_def fully_epac_assn_def full_poly_input_assn_def
      hr_comp_assoc O_assoc
    by auto
  show ?thesis
    using full_checker_l_s2_impl.refine[FCOMP 3]
    unfolding full_poly_assn_def[symmetric]
      full_poly_input_assn_def[symmetric]
      fully_epac_assn_def[symmetric]
      code_status_assn_def[symmetric]
      full_vars_assn_def[symmetric]
      polys_rel_full_polys_rel
      hr_comp_prod_conv
      full_polys_assn_def[symmetric]
      full_poly_input_assn_alt_def[symmetric]
      4 H[symmetric]
    by auto
qed

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

end
end
