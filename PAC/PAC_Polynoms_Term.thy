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

definition term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and>
     sorted_wrt (rel2p (lexord less_than_char)) xs}\<close>

definition poly_list_rel :: \<open>_ \<Rightarrow> (_ \<times> mset_polynom) set\<close> where
  \<open>poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R\<rangle>list_rel O list_mset_rel}\<close>

definition sorted_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynom) set\<close> where
  \<open>sorted_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs)}\<close>

abbreviation sorted_poly_list_rel where
  \<open>sorted_poly_list_rel R \<equiv> sorted_poly_list_rel_wrt R term_poly_list_rel\<close>

lemma sorted_poly_list_rel_empty_l[simp]:
  \<open>([], s') \<in> sorted_poly_list_rel S \<longleftrightarrow> s' = {#}\<close>
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
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p (lexord less_than_char)) ys\<close>
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
  done

lemma sorted_poly_list_rel_Cons_iff:
  \<open>((ys, n) # p, a) \<in> sorted_poly_list_rel S \<longleftrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p (lexord less_than_char)) ys\<close>
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
  assumes \<open>(pq, pq') \<in> sorted_poly_list_rel (rel2p (lexord (lexord less_than_char))) \<times>\<^sub>r sorted_poly_list_rel (rel2p (lexord (lexord less_than_char)))\<close>
  shows \<open>\<exists>r. (add_poly_l' pq, r) \<in> sorted_poly_list_rel (rel2p (lexord (lexord less_than_char))) \<and>
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
proof -
  show ?thesis
    unfolding add_poly_l_def
    apply (induction x rule: add_poly_l'.induct)
    subgoal
      apply (subst RECT_unfold)
      apply refine_mono
      apply (simp split: list.split)
      done
    subgoal
      apply (subst RECT_unfold)
      apply refine_mono
      apply (simp split: list.split)
      done
    subgoal
      apply (subst RECT_unfold)
      apply refine_mono
      apply (simp split: list.split)
      done
    done
qed


lemma add_poly_l_spec:
  \<open>(add_poly_l, uncurry (\<lambda>p q. SPEC(\<lambda>r. add_poly_p\<^sup>*\<^sup>* (p, q, {#}) ({#}, {#}, r)))) \<in>
    sorted_poly_list_rel (rel2p (lexord (lexord less_than_char))) \<times>\<^sub>r
       sorted_poly_list_rel (rel2p (lexord (lexord less_than_char))) \<rightarrow>\<^sub>f
    \<langle>sorted_poly_list_rel (rel2p (lexord (lexord less_than_char)))\<rangle>nres_rel\<close>
  unfolding add_poly_l_add_poly
  apply (intro nres_relI frefI)
  apply (drule add_poly_l'_add_poly_p)
  apply (auto simp: conc_fun_RES)
  done

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