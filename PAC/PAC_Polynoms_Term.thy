theory PAC_Polynoms_Term
  imports PAC_Polynoms_List
    Refine_Imperative_HOL.IICF
begin

type_synonym term_poly_list = \<open>string list\<close>
type_synonym llist_polynom = \<open>(term_poly_list \<times> int) list\<close>


text \<open>We instantiate the characters with typeclass linorder to be able to talk abourt sorted and
  so on.\<close>

definition less_than_char :: \<open>(char \<times> char) set\<close> where
  \<open>less_than_char = {(a, b). of_char a < (of_char b :: nat) } \<close>

lemma trans_less_than_char[simp]:
    \<open>trans less_than_char\<close> and
  irrefl_less_than_char:
    \<open>irrefl less_than_char\<close> and
  antisym_less_than_char:
    \<open>antisym less_than_char\<close>
  by (auto simp: less_than_char_def trans_def irrefl_def antisym_def)

abbreviation var_order_rel :: \<open>(string \<times> string) set\<close> where
  \<open>var_order_rel \<equiv> lexord less_than_char\<close>

abbreviation var_order :: \<open>string \<Rightarrow> string \<Rightarrow> bool\<close> where
  \<open>var_order \<equiv> rel2p var_order_rel\<close>

abbreviation term_order_rel :: \<open>(term_poly_list \<times> term_poly_list) set\<close> where
  \<open>term_order_rel \<equiv> lexord (lexord less_than_char)\<close>

abbreviation term_order :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> bool\<close> where
  \<open>term_order \<equiv> rel2p term_order_rel\<close>

definition term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and>
     distinct xs \<and>
     sorted_wrt (rel2p (lexord less_than_char)) xs}\<close>

definition poly_list_rel :: \<open>_ \<Rightarrow> (('a \<times> int) list \<times> mset_polynom) set\<close> where
  \<open>poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel}\<close>

definition sorted_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynom) set\<close> where
  \<open>sorted_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs)}\<close>

abbreviation sorted_poly_list_rel where
  \<open>sorted_poly_list_rel R \<equiv> sorted_poly_list_rel_wrt R term_poly_list_rel\<close>

abbreviation sorted_poly_rel where
  \<open>sorted_poly_rel \<equiv> sorted_poly_list_rel (rel2p (lexord (lexord less_than_char)))\<close>

abbreviation unsorted_poly_rel where
  \<open>unsorted_poly_rel \<equiv> poly_list_rel term_poly_list_rel\<close>

lemma sorted_poly_list_rel_empty_l[simp]:
  \<open>([], s') \<in> sorted_poly_list_rel_wrt S T \<longleftrightarrow> s' = {#}\<close>
  by (cases s')
    (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def)

fun add_poly_l' :: \<open>llist_polynom \<times> llist_polynom \<Rightarrow> llist_polynom\<close> where
  \<open>add_poly_l' (p, []) = p\<close> |
  \<open>add_poly_l' ([], q) = q\<close> |
  \<open>add_poly_l' ((xs, n) # p, (ys, m) # q) =
            (if xs = ys then if n + m = 0 then add_poly_l' (p, q) else
                 let pq = add_poly_l' (p, q) in
                 ((xs, n + m) # pq)
            else if (xs, ys) \<in> lexord (lexord less_than_char)
              then
                 let pq = add_poly_l' (p, (ys, m) # q) in
                 ((xs, n) # pq)
            else
                 let pq = add_poly_l' ((xs, n) # p, q) in
                 ((ys, m) # pq)
            )\<close>

definition add_poly_l :: \<open>llist_polynom \<times> llist_polynom \<Rightarrow> llist_polynom nres\<close> where
  \<open>add_poly_l = REC\<^sub>T
      (\<lambda>add_poly_l (p, q).
        case (p,q) of
          (p, []) \<Rightarrow> RETURN p
        | ([], q) \<Rightarrow> RETURN q
        | ((xs, n) # p, (ys, m) # q) \<Rightarrow>
            (if xs = ys then if n + m = 0 then add_poly_l (p, q) else
               do {
                 pq \<leftarrow> add_poly_l (p, q);
                 RETURN ((xs, n + m) # pq)
             }
            else if (xs, ys) \<in> lexord (lexord less_than_char)
              then do {
                 pq \<leftarrow> add_poly_l (p, (ys, m) # q);
                 RETURN ((xs, n) # pq)
            }
            else do {
                 pq \<leftarrow> add_poly_l ((xs, n) # p, q);
                 RETURN ((ys, m) # pq)
            }))\<close>

lemma sorted_poly_list_rel_ConsD:
  \<open>((ys, n) # p, a) \<in> sorted_poly_list_rel S \<Longrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p (lexord less_than_char)) ys \<and>
    distinct ys\<close>
  unfolding sorted_poly_list_rel_wrt_def prod.case mem_Collect_eq
    list_rel_def
  apply (clarsimp)
  apply (subst (asm) list.rel_sel)
  apply (intro conjI)
  apply (rule_tac b = \<open>tl y\<close> in relcompI)
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  done

lemma sorted_poly_list_rel_Cons_iff:
  \<open>((ys, n) # p, a) \<in> sorted_poly_list_rel S \<longleftrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p (lexord less_than_char)) ys \<and>
    distinct ys\<close>
  apply (rule iffI)
  subgoal
    by (auto dest: sorted_poly_list_rel_ConsD)
  subgoal
    unfolding sorted_poly_list_rel_wrt_def prod.case mem_Collect_eq
      list_rel_def
    apply (clarsimp)
    apply (rule_tac b = \<open>(mset ys, n) # y\<close> in relcompI)
    by (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
        term_poly_list_rel_def
      dest!: multi_member_split)
    done

lemma add_poly_p_add_mset_sum_0:
   \<open>n + m = 0 \<Longrightarrow>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
           add_poly_p\<^sup>*\<^sup>*
            (add_mset (mset ys, n) A, add_mset (mset ys, m) Aa, {#})
            ({#}, {#}, r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_same_coeff_l)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (auto intro: add_poly_p.rem_0_coeff)
  done

lemma monoms_add_poly_l'D:
  \<open>(aa, ba) \<in> set (add_poly_l' x) \<Longrightarrow> aa \<in> fst ` set (fst x) \<or> aa \<in> fst ` set (snd x)\<close>
  by (induction x rule: add_poly_l'.induct)
    (auto split: if_splits)

lemma add_poly_p_add_to_result:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, B, r) (A', B', r') \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (A, B, p + r) (A', B', p + r')\<close>
  apply (induction rule: rtranclp_induct[of add_poly_p \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  apply auto
  apply (cases rule: add_poly_p.cases)
  apply assumption
  apply (auto simp: )
  apply (meson add_poly_p.intros rtranclp.simps)+
  done

lemma add_poly_p_add_mset_comb:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (add_mset (xs, n) A, Aa, {#})
        ({#}, {#}, add_mset (xs, n) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_l)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(xs, n)#}\<close>]
  by auto

lemma add_poly_p_add_mset_comb2:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (add_mset (ys, n) A, add_mset (ys, m) Aa, {#})
        ({#}, {#}, add_mset (ys, n + m) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_same_coeff_l)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(ys, n+m)#}\<close>]
  by auto


lemma add_poly_p_add_mset_comb3:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (A, add_mset (ys, m) Aa, {#})
        ({#}, {#}, add_mset (ys, m) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(ys, m)#}\<close>]
  by auto

lemma total_on_lexord:
  \<open>Relation.total_on R UNIV \<Longrightarrow> Relation.total_on (lexord R) UNIV\<close>
  by (auto simp: Relation.total_on_def)

lemma antisym_lexord:
  \<open>antisym R \<Longrightarrow> irrefl R \<Longrightarrow> antisym (lexord R)\<close>
  by (auto simp: antisym_def lexord_def irrefl_def
    elim!: list_match_lel_lel)

lemma less_than_char_linear:
  \<open>(a, b) \<in> less_than_char \<or>
           a = b \<or> (b, a) \<in> less_than_char\<close>
  by (auto simp: less_than_char_def)

lemma total_on_lexord_less_than_char_linear:
  \<open>xs \<noteq> ys \<Longrightarrow> (xs, ys) \<notin> lexord (lexord less_than_char) \<longleftrightarrow>
       (ys, xs) \<in> lexord (lexord less_than_char)\<close>
   using lexord_linear[of \<open>lexord less_than_char\<close> xs ys]
   using lexord_linear[of \<open>less_than_char\<close>] less_than_char_linear
   apply (auto simp: Relation.total_on_def)
   using lexord_irrefl[OF irrefl_less_than_char]
     antisym_lexord[OF antisym_lexord[OF antisym_less_than_char irrefl_less_than_char]]
   apply (auto simp: antisym_def)
   done

lemma add_poly_l'_add_poly_p:
  assumes \<open>(pq, pq') \<in> sorted_poly_rel \<times>\<^sub>r sorted_poly_rel\<close>
  shows \<open>\<exists>r. (add_poly_l' pq, r) \<in> sorted_poly_rel \<and>
                        add_poly_p\<^sup>*\<^sup>* (fst pq', snd pq', {#}) ({#}, {#}, r)\<close>
  supply [[goals_limit=1]]
  using assms
  apply (induction \<open>pq\<close> arbitrary: pq' rule: add_poly_l'.induct)
  subgoal for p pq'
    using add_poly_p_empty_l[of \<open>fst pq'\<close> \<open>{#}\<close> \<open>{#}\<close>]
    by (cases pq') (auto intro!: exI[of _ \<open>fst pq'\<close>])
  subgoal for x p pq'
    using add_poly_p_empty_r[of  \<open>{#}\<close> \<open>snd pq'\<close> \<open>{#}\<close>]
    by (cases pq')  (auto intro!: exI[of _ \<open>snd pq'\<close>])
  subgoal premises p for xs n p ys m q pq'
    apply (cases pq') \<comment> \<open>Isabelle does a completely stupid case distinction here\<close>
    apply (cases \<open>xs = ys\<close>)
    subgoal
      apply (cases \<open>n + m = 0\<close>)
      subgoal
        using p(1)[of \<open>(remove1_mset (mset xs, n) (fst pq'), remove1_mset (mset ys, m)  (snd pq'))\<close>] p(5-)
        apply (auto dest!: sorted_poly_list_rel_ConsD multi_member_split
           )
      using add_poly_p_add_mset_sum_0 by blast
    subgoal
        using p(2)[of \<open>(remove1_mset (mset xs, n) (fst pq'), remove1_mset (mset ys, m)  (snd pq'))\<close>] p(5-)
        apply (auto dest!: sorted_poly_list_rel_ConsD multi_member_split)
        apply (rule_tac x = \<open>add_mset (mset ys, n + m) r\<close> in exI)
        apply (fastforce dest!: monoms_add_poly_l'D simp: sorted_poly_list_rel_Cons_iff rel2p_def
          intro: add_poly_p_add_mset_comb2)
        done
     done
    subgoal
      apply (cases \<open>(xs, ys) \<in> lexord (lexord less_than_char)\<close>)
      subgoal
        using p(3)[of \<open>(remove1_mset (mset xs, n) (fst pq'), (snd pq'))\<close>] p(5-)
        apply (auto dest!: multi_member_split simp: sorted_poly_list_rel_Cons_iff rel2p_def)
        apply (rule_tac x = \<open>add_mset (mset xs, n) r\<close> in exI)
        apply (auto dest!: monoms_add_poly_l'D)
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb  simp: lexord_transI)
        apply (rule lexord_trans)
        apply assumption
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb simp: lexord_transI)
        done
      subgoal
        using p(4)[of \<open>(fst pq', remove1_mset (mset ys, m) (snd pq'))\<close>] p(5-)
        apply (auto dest!: multi_member_split simp: sorted_poly_list_rel_Cons_iff rel2p_def)
        apply (rule_tac x = \<open>add_mset (mset ys, m) r\<close> in exI)
        apply (auto dest!: monoms_add_poly_l'D
          simp: total_on_lexord_less_than_char_linear)
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb  simp: lexord_transI
          total_on_lexord_less_than_char_linear)
        apply (rule lexord_trans)
        apply assumption
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb3 simp: lexord_transI)
        done
      done
   done
  done


lemma add_poly_l_add_poly:
  \<open>add_poly_l x = RETURN (add_poly_l' x)\<close>
  unfolding add_poly_l_def
  by (induction x rule: add_poly_l'.induct)
    (solves \<open>subst RECT_unfold, refine_mono, simp split: list.split\<close>)+

lemma add_poly_l_spec:
  \<open>(add_poly_l, uncurry (\<lambda>p q. SPEC(\<lambda>r. add_poly_p\<^sup>*\<^sup>* (p, q, {#}) ({#}, {#}, r)))) \<in>
    sorted_poly_rel \<times>\<^sub>r sorted_poly_rel \<rightarrow>\<^sub>f \<langle>sorted_poly_rel\<rangle>nres_rel\<close>
  unfolding add_poly_l_add_poly
  apply (intro nres_relI frefI)
  apply (drule add_poly_l'_add_poly_p)
  apply (auto simp: conc_fun_RES)
  done

definition sort_poly_spec :: \<open>llist_polynom \<Rightarrow> llist_polynom nres\<close> where
\<open>sort_poly_spec p =
  SPEC(\<lambda>p'. mset p = mset p' \<and> sorted_wrt (rel2p (lexord (lexord less_than_char))) (map fst p'))\<close>

lemma sort_poly_spec_id:
  assumes \<open>(p, p') \<in> unsorted_poly_rel\<close>
  shows \<open>sort_poly_spec p \<le> \<Down> (sorted_poly_rel) (RETURN p')\<close>
proof -
  obtain y where
    py: \<open>(p, y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    p'_y: \<open>p' = mset y\<close>
    using assms
    unfolding sort_poly_spec_def poly_list_rel_def sorted_poly_list_rel_wrt_def
    by (auto simp: list_mset_rel_def br_def Collect_eq_comp')
  then have [simp]: \<open>length y = length p\<close>
    by (auto simp: list_rel_def list_all2_conv_all_nth)
  have H: \<open>(x, p')
        \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel\<close>
     if px: \<open>mset p = mset x\<close> and \<open>sorted_wrt (rel2p (lexord (lexord less_than_char))) (map fst x)\<close>
     for x :: \<open>llist_polynom\<close>
  proof -
    obtain f where
      f: \<open>bij_betw f {..<length x} {..<length p}\<close> and
      [simp]: \<open>\<And>i. i<length x \<Longrightarrow> x ! i = p ! (f i)\<close>
      using px apply - apply (subst (asm)(2) eq_commute)  unfolding mset_eq_perm
      by (auto dest!: permutation_Ex_bij)
    let ?y = \<open>map (\<lambda>i. y ! f i) [0 ..< length x]\<close>
    have \<open>i < length y \<Longrightarrow> (p ! f i, y ! f i) \<in> term_poly_list_rel \<times>\<^sub>r int_rel\<close> for i
      using list_all2_nthD[of _ p y
         \<open>f i\<close>, OF py[unfolded list_rel_def mem_Collect_eq prod.case]]
         mset_eq_length[OF px] f
      by (auto simp: list_rel_def list_all2_conv_all_nth bij_betw_def)
    then have \<open>(x, ?y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
      xy: \<open>length x = length y\<close>
      using py list_all2_nthD[of \<open>rel2p (term_poly_list_rel \<times>\<^sub>r int_rel)\<close> p y
         \<open>f i\<close> for i, simplified] mset_eq_length[OF px]
      by (auto simp: list_rel_def list_all2_conv_all_nth)
    moreover {
      have f: \<open>mset_set {0..<length x} = f `# mset_set {0..<length x}\<close>
        using f mset_eq_length[OF px]
        by (auto simp: bij_betw_def lessThan_atLeast0 image_mset_mset_set)
      have \<open>mset y = {#y ! f x. x \<in># mset_set {0..<length x}#}\<close>
        by (subst drop_0[symmetric], subst mset_drop_upto, subst xy[symmetric], subst f)
          auto
      then have \<open>(?y, p') \<in> list_mset_rel\<close>
        by (auto simp: list_mset_rel_def br_def p'_y)
       }
    ultimately show ?thesis
      by (auto intro!: relcompI[of _ ?y])
  qed
  show ?thesis
    unfolding sort_poly_spec_def poly_list_rel_def sorted_poly_list_rel_wrt_def
    by refine_rcg (auto intro: H)
qed


definition mult_poly_raw_l_spec where
  \<open>mult_poly_raw_l_spec p q = map (apfst remdups_mset) (mult_poly_raw_l p q)\<close>

fun mult_monoms :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list\<close> where
  \<open>mult_monoms p [] = p\<close> |
  \<open>mult_monoms [] p = p\<close> |
  \<open>mult_monoms (x # p) (y # q) =
    (if x = y then x # mult_monoms p q
     else if (x, y) \<in> var_order_rel then x # mult_monoms p (y # q)
      else y # mult_monoms (x # p) q)\<close>

lemma term_poly_list_rel_empty_iff[simp]:
  \<open>([], q') \<in> term_poly_list_rel \<longleftrightarrow> q' = {#}\<close>
  by (auto simp: term_poly_list_rel_def)

lemma term_poly_list_rel_Cons_iff:
  \<open>(y # p, p') \<in> term_poly_list_rel \<longleftrightarrow>
    (p, remove1_mset y p') \<in> term_poly_list_rel \<and>
    y \<in># p' \<and> y \<notin> set p \<and> y \<notin># remove1_mset y p' \<and>
    (\<forall>x\<in>#mset p. (y, x) \<in> var_order_rel)\<close>
  apply (auto simp: term_poly_list_rel_def rel2p_def dest!: multi_member_split)
  by (metis list.set_intros(1) list_of_mset_exi mset.simps(2) mset_eq_setD)

lemma var_order_rel_antisym[simp]:
  \<open>(y, y) \<notin> var_order_rel\<close>
  by (simp add: less_than_char_def lexord_irreflexive)

lemma term_poly_list_rel_remdups_mset:
  \<open>(p, p') \<in> term_poly_list_rel \<Longrightarrow>
    (p, remdups_mset p') \<in> term_poly_list_rel\<close>
  by (auto simp: term_poly_list_rel_def distinct_mset_remdups_mset_id simp flip: distinct_mset_mset_distinct)

lemma var_notin_notin_mult_monomsD:
  \<open>y \<in> set (mult_monoms p q) \<Longrightarrow> y \<in> set p \<or> y \<in> set q\<close>
  by (induction p q arbitrary: p' q' rule: mult_monoms.induct) (auto split: if_splits)

lemma term_poly_list_rel_set_mset:
  \<open>(p, q) \<in> term_poly_list_rel \<Longrightarrow> set p = set_mset q\<close>
  by (auto simp: term_poly_list_rel_def)

lemma mult_monoms_spec:
  \<open>(mult_monoms, (\<lambda>a b. remdups_mset (a + b))) \<in> term_poly_list_rel \<rightarrow> term_poly_list_rel \<rightarrow> term_poly_list_rel\<close>
  apply (intro fun_relI)
  apply (rename_tac p p' q q')
  subgoal for p p' q q'
    apply (induction p q arbitrary: p' q' rule: mult_monoms.induct)
    subgoal by (auto simp: term_poly_list_rel_Cons_iff rel2p_def term_poly_list_rel_remdups_mset)
    subgoal for x p p' q'
      by (auto simp: term_poly_list_rel_Cons_iff rel2p_def term_poly_list_rel_remdups_mset
      dest!: multi_member_split[of _ q'])
    subgoal premises p for x p y q p' q'
      apply (cases \<open>x = y\<close>)
      subgoal
        using p(1)[of \<open>remove1_mset y p'\<close> \<open>remove1_mset y q'\<close>] p(4-)
        apply (auto simp: term_poly_list_rel_Cons_iff rel2p_def
          dest!: var_notin_notin_mult_monomsD
          dest!: multi_member_split)
       by (metis set_mset_remdups_mset union_iff union_single_eq_member)
     apply (cases \<open>(x, y) \<in> var_order_rel\<close>)
     subgoal
        using p(2)[of \<open>remove1_mset x p'\<close> \<open>q'\<close>] p(4-)
        apply (auto simp: term_poly_list_rel_Cons_iff rel2p_def
            term_poly_list_rel_set_mset rel2p_def
          dest!: multi_member_split[of _ p'] multi_member_split[of _ q']
            var_notin_notin_mult_monomsD
          split: if_splits)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       done
     subgoal
        using p(3)[of \<open>p'\<close> \<open>remove1_mset y q'\<close>] p(4-)
        apply (auto simp: term_poly_list_rel_Cons_iff rel2p_def
            term_poly_list_rel_set_mset rel2p_def
          dest!: multi_member_split[of _ p'] multi_member_split[of _ q']
            var_notin_notin_mult_monomsD
          split: if_splits)
       using lexord_trans trans_less_than_char var_order_rel_antisym apply blast
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       by (meson less_than_char_linear lexord_linear lexord_trans trans_less_than_char)
       done
    done
  done

definition mult_monomials :: \<open>_\<close> where
  \<open>mult_monomials = (\<lambda>(x, a) (y, b). (mult_monoms x y, a * b))\<close>

definition mult_poly_raw :: \<open>llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom\<close> where
  \<open>mult_poly_raw p q = foldl (\<lambda>b x. map (mult_monomials x) q @ b) [] p\<close>

inductive mult_poly_p :: \<open>mset_polynom \<Rightarrow> mset_polynom \<times> mset_polynom \<Rightarrow> mset_polynom \<times> mset_polynom \<Rightarrow> bool\<close>
  for q :: mset_polynom where
mult_step:
    \<open>mult_poly_p q (add_mset (xs, n) p, r) (p, (\<lambda>(ys, m). (remdups_mset (xs + ys), n * m)) `# q + r)\<close>


lemmas mult_poly_p_induct = mult_poly_p.induct[split_format(complete)]


context poly_embed
begin

lemma polynom_of_mset_mult_map:
  \<open>polynom_of_mset
     {#case x of (ys, n) \<Rightarrow> (remdups_mset (ys + xs), n * m). x \<in># q#} -
    Const n * (poly_of_vars xs * polynom_of_mset q)
    \<in> More_Modules.ideal polynom_bool\<close>
proof (induction q)
  case empty
  then show ?case by (auto simp: algebra_simps ideal.span_zero)
next
  case (add x q)
  show ?case
    by (metis (no_types) add.IH add.left_neutral fold_mset_empty image_mset_add_mset mult_zero_left mult_zero_right
      poly_embed.poly_of_vars_def poly_embed.poly_of_vars_simps(2) poly_embed.polynom_of_mset_Cons)
qed

lemma mult_poly_p_mult_ideal:
  \<open>mult_poly_p q (p, r) (p', r') \<Longrightarrow>
     (polynom_of_mset p' * polynom_of_mset q + polynom_of_mset r') - (polynom_of_mset p * polynom_of_mset q + polynom_of_mset r)
       \<in> ideal polynom_bool\<close>
proof (induction rule: mult_poly_p_induct)
  case (mult_step xs n p r)
  show ?case
    by (auto simp: algebra_simps polynom_of_mset_mult_map)
qed

lemma rtranclp_mult_poly_p_mult_ideal:
  \<open>(mult_poly_p q)\<^sup>*\<^sup>* (p, r) (p', r') \<Longrightarrow>
     (polynom_of_mset p' * polynom_of_mset q + polynom_of_mset r') - (polynom_of_mset p * polynom_of_mset q + polynom_of_mset r)
       \<in> ideal polynom_bool\<close>
  apply (induction p' r' rule: rtranclp_induct[of \<open>mult_poly_p q\<close> \<open>(p, r)\<close> \<open>(p', q')\<close> for p' q', split_format(complete)])
  subgoal
    by (auto simp: ideal.span_zero)
  subgoal for a b aa ba
    apply (drule mult_poly_p_mult_ideal)
    apply (drule ideal.span_add)
    apply assumption
    apply (auto simp: group_add_class.diff_add_eq_diff_diff_swap
      add.assoc add.inverse_distrib_swap ac_simps
      simp flip: ab_group_add_class.ab_diff_conv_add_uminus)
    by (metis (no_types, hide_lams) ab_group_add_class.ab_diff_conv_add_uminus
      ab_semigroup_add_class.add.commute add.assoc add.inverse_distrib_swap)
  done

lemma rtranclp_mult_poly_p_mult_ideal_final:
  \<open>(mult_poly_p q)\<^sup>*\<^sup>* (p, {#}) ({#}, r) \<Longrightarrow>
    (polynom_of_mset r) - (polynom_of_mset p * polynom_of_mset q)
       \<in> ideal polynom_bool\<close>
  by (drule rtranclp_mult_poly_p_mult_ideal) auto
end

lemma foldl_append_empty:
  \<open>NO_MATCH [] xs \<Longrightarrow> foldl (\<lambda>b x. f x @ b) xs p = foldl (\<lambda>b x. f x @ b) [] p @ xs\<close>
  apply (induction p arbitrary: xs)
  apply simp
  by (metis (mono_tags, lifting) NO_MATCH_def append.assoc append_self_conv foldl_Cons)


lemma poly_list_rel_empty_iff[simp]:
  \<open>([], r) \<in> poly_list_rel R \<longleftrightarrow> r = {#}\<close>
  by (auto simp: poly_list_rel_def list_mset_rel_def br_def)

lemma mult_poly_raw_simp[simp]:
  \<open>mult_poly_raw [] q = []\<close>
  \<open>mult_poly_raw (x # p) q = mult_poly_raw p q @ map (mult_monomials x) q\<close>
  subgoal by (auto simp: mult_poly_raw_def)
  subgoal
    by (induction p)
      (auto simp: mult_poly_raw_def foldl_append_empty)
  done

lemma sorted_poly_list_relD:
  \<open>(q, q') \<in> sorted_poly_list_rel R \<Longrightarrow> q' = (\<lambda>(a, b). (mset a, b)) `# mset q\<close>
  apply (induction q arbitrary: q')
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    list_rel_split_right_iff)
  apply (subst (asm)(2) term_poly_list_rel_def)
  apply auto
  done

lemma list_all2_in_set_ExD:
  \<open>list_all2 R p q \<Longrightarrow> x \<in> set p \<Longrightarrow> \<exists>y \<in> set q. R x y\<close>
  by (induction p q rule: list_all2_induct)
    auto

inductive_cases mult_poly_p_elim: \<open>mult_poly_p q (A, r) (B, r')\<close>

lemma mult_poly_p_add_mset_same:
  \<open>(mult_poly_p q')\<^sup>*\<^sup>* (A, r) (B, r') \<Longrightarrow> (mult_poly_p q')\<^sup>*\<^sup>* (add_mset x A, r) (add_mset x B, r')\<close>
  apply (induction rule: rtranclp_induct[of \<open>mult_poly_p q'\<close> \<open>(p, r)\<close> \<open>(p', q'')\<close> for p' q'', split_format(complete)])
  apply (auto elim!: mult_poly_p_elim intro: mult_poly_p.intros)
  by (smt add_mset_commute mult_step rtranclp.rtrancl_into_rtrancl)

lemma mult_poly_raw_mult_poly_p:
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> and \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>\<exists>r. (mult_poly_raw p q, r) \<in> unsorted_poly_rel \<and> (mult_poly_p q')\<^sup>*\<^sup>* (p', {#}) ({#}, r)\<close>
proof -
  have H: \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow> n < length q \<Longrightarrow>
    distinct aa \<Longrightarrow> sorted_wrt var_order aa \<Longrightarrow>
    (mult_monoms aa (fst (q ! n)),
           mset (mult_monoms aa (fst (q ! n))))
          \<in> term_poly_list_rel\<close> for aa n
    using mult_monoms_spec[unfolded fun_rel_def, simplified] apply -
    apply (drule bspec[of _ _ \<open>(aa, (mset aa))\<close>])
    apply (auto simp: term_poly_list_rel_def)[]
    unfolding prod.case sorted_poly_list_rel_wrt_def
    apply clarsimp
    subgoal for y
      apply (drule bspec[of _ _ \<open>(fst (q ! n), mset (fst (q ! n)))\<close>])
      apply (cases \<open>q ! n\<close>; cases \<open>y ! n\<close>)
      using param_nth[of n y n q \<open>term_poly_list_rel \<times>\<^sub>r int_rel\<close>]
      by (auto simp: list_rel_imp_same_length term_poly_list_rel_def)
    done

  have H': \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow>
    distinct aa \<Longrightarrow> sorted_wrt var_order aa \<Longrightarrow>
     (ab, ba) \<in> set q \<Longrightarrow>
       remdups_mset (mset aa + mset ab) = mset (mult_monoms aa ab)\<close> for aa n ab ba
    using mult_monoms_spec[unfolded fun_rel_def, simplified] apply -
    apply (drule bspec[of _ _ \<open>(aa, (mset aa))\<close>])
    apply (auto simp: term_poly_list_rel_def)[]
    unfolding prod.case sorted_poly_list_rel_wrt_def
    apply clarsimp
    subgoal for y
      apply (drule bspec[of _ _ \<open>(ab, mset ab)\<close>])
      apply (auto simp: list_rel_imp_same_length term_poly_list_rel_def list_rel_def
        dest: list_all2_in_set_ExD)
    done
    done

  have  H: \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow>
       a = (aa, b) \<Longrightarrow>
       (pq, r) \<in> unsorted_poly_rel \<Longrightarrow>
       p' = add_mset (mset aa, b) A \<Longrightarrow>
       \<forall>x\<in>set p. term_order aa (fst x) \<Longrightarrow>
       sorted_wrt var_order aa \<Longrightarrow>
       distinct aa \<Longrightarrow>
       (pq @
        map (mult_monomials (aa, b)) q,
        {#case x of (ys, n) \<Rightarrow> (remdups_mset (mset aa + ys), n * b)
        . x \<in># q'#} +
        r)
       \<in> unsorted_poly_rel\<close> for a p p' pq aa b r
   apply (auto simp: poly_list_rel_def)
   apply (rule_tac b = \<open>y @ map (\<lambda>(a,b). (mset a, b)) (map (mult_monomials (aa, b)) q)\<close> in relcompI)
   apply (auto simp: list_rel_def list_all2_append list_all2_lengthD H
     list_mset_rel_def br_def mult_monomials_def case_prod_beta intro!: list_all2_all_nthI
     simp: sorted_poly_list_relD)
     apply (subst sorted_poly_list_relD[of q q' term_order])
     apply (auto simp: case_prod_beta H' intro!: image_mset_cong)
   done

  show ?thesis
    using assms
    apply (induction p arbitrary: p')
    subgoal
      by auto
    subgoal premises p for a p p'
      using p(1)[of \<open>remove1_mset (mset (fst a), snd a) p'\<close>] p(2-)
      apply (cases a)
      apply (auto simp: sorted_poly_list_rel_Cons_iff
        dest!: multi_member_split)
      apply (rule_tac x = \<open>(\<lambda>(ys, n). (remdups_mset (mset (fst a) + ys), n * snd a)) `# q' + r\<close> in exI)
      apply (auto intro: mult_poly_p.intros intro!: H)
      apply (rule rtranclp_trans)
      apply (rule mult_poly_p_add_mset_same)
      apply assumption
      apply (rule converse_rtranclp_into_rtranclp)
      apply (auto intro!: mult_poly_p.intros simp: ac_simps)
      done
    done
qed

instantiation char :: linorder
begin
  definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
    \<open>less_eq_char c d = (((of_char c) :: nat) \<le> of_char d)\<close>

  definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
    \<open>less_char c d = (((of_char c) :: nat) < of_char d)\<close>

instance
  using linorder_char
  unfolding linorder_class_def class.linorder_def
    less_eq_char_def[symmetric] less_char_def[symmetric]
    class.order_def order_class_def
    class.preorder_def preorder_class_def
    ord_class_def
  apply auto
  apply standard
  done
end

end