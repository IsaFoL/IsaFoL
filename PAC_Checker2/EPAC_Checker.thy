(*
  File:         PAC_Checker.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory EPAC_Checker
  imports
    EPAC_Checker_Specification
    PAC_Checker.PAC_Map_Rel
    PAC_Checker.PAC_Polynomials_Operations
    PAC_Checker.PAC_Checker
    Show.Show
    Show.Show_Instances
begin

hide_const (open) PAC_Checker_Specification.PAC_checker_step
    PAC_Checker.PAC_checker_l PAC_Checker_Specification.PAC_checker
hide_fact (open) PAC_Checker_Specification.PAC_checker_step_def
  PAC_Checker.PAC_checker_l_def PAC_Checker_Specification.PAC_checker_def

lemma vars_llist[simp]:
  \<open>vars_llist [] = {}\<close>
  \<open>vars_llist (xs @ ys) = vars_llist xs \<union> vars_llist ys\<close>
  \<open>vars_llist (x # ys) = set (fst x) \<union> vars_llist ys\<close>
  by (auto simp: vars_llist_def)

section \<open>Executable Checker\<close>

text \<open>In this layer we finally refine the checker to executable code.\<close>

subsection \<open>Definitions\<close>

text \<open>Compared to the previous layer, we add an error message when an error is discovered. We do not
  attempt to prove anything on the error message (neither that there really is an error, nor that the
  error message is correct).
\<close>

paragraph \<open>Refinement relation\<close>

fun pac_step_rel_raw :: \<open>('olbl \<times> 'lbl) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('c \<times> 'd) set \<Rightarrow> ('a, 'c, 'olbl) pac_step \<Rightarrow> ('b, 'd, 'lbl) pac_step \<Rightarrow> bool\<close> where
\<open>pac_step_rel_raw R1 R2 R3 (CL p i r) (CL p' i' r') \<longleftrightarrow>
   (p, p') \<in> \<langle>R2 \<times>\<^sub>r R1\<rangle>list_rel \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 R3 (Del p1) (Del p1') \<longleftrightarrow>
   (p1, p1') \<in> R1\<close> |
\<open>pac_step_rel_raw R1 R2 R3 (Extension i x p1) (Extension j x' p1') \<longleftrightarrow>
   (i, j) \<in> R1 \<and> (x, x') \<in> R3 \<and> (p1, p1') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 R3 _ _ \<longleftrightarrow> False\<close>

fun pac_step_rel_assn :: \<open>('olbl \<Rightarrow> 'lbl \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> assn) \<Rightarrow> ('a, 'c, 'olbl) pac_step \<Rightarrow> ('b, 'd, 'lbl) pac_step \<Rightarrow> assn\<close> where
\<open>pac_step_rel_assn R1 R2 R3 (CL p i r) (CL p' i' r') =
   list_assn (R2 \<times>\<^sub>a R1) p p' * R1 i i' * R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 R3 (Del p1) (Del p1') =
   R1 p1 p1'\<close> |
\<open>pac_step_rel_assn R1 R2 R3 (Extension i x p1) (Extension i' x' p1') =
   R1 i i' * R3 x x' * R2 p1 p1'\<close> |
\<open>pac_step_rel_assn R1 R2 _ _ _ = false\<close>

lemma pac_step_rel_assn_alt_def:
  \<open>pac_step_rel_assn R1 R2 R3 x y = (
  case (x, y) of
      (CL p i r, CL p' i' r') \<Rightarrow>
        list_assn (R2 \<times>\<^sub>a R1) p p' * R1 i i' * R2 r r'
    | (Del p1, Del p1') \<Rightarrow> R1 p1 p1'
    | (Extension i x p1, Extension i' x' p1') \<Rightarrow> R1 i i' * R3 x x' * R2 p1 p1'
    | _ \<Rightarrow> false)\<close>
    by (auto split: pac_step.splits)


paragraph \<open>Addition checking\<close>


paragraph \<open>Linear Combination\<close>

definition check_linear_combi_l_pre_err :: \<open>nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_pre_err r _ _ _ = SPEC (\<lambda>_. True)\<close>

definition check_linear_combi_l_dom_err :: \<open>llist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_dom_err p r = SPEC (\<lambda>_. True)\<close>

definition check_linear_combi_l_mult_err :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_mult_err pq r = SPEC (\<lambda>_. True)\<close>
definition linear_combi_l_pre where
  \<open>linear_combi_l_pre i A \<V> xs \<longleftrightarrow>
  (\<forall>i\<in>#dom_m A. vars_llist (the (fmlookup A i)) \<subseteq> \<V>)\<close>

definition linear_combi_l where
\<open>linear_combi_l i A \<V> xs = do {
    ASSERT(linear_combi_l_pre i A \<V> xs);
    WHILE\<^sub>T
      (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         ASSERT(vars_llist p \<subseteq> \<V>);
         let (q\<^sub>0 :: llist_polynomial, i) = hd xs;
         if (i \<notin># dom_m A \<or> \<not>(vars_llist q\<^sub>0 \<subseteq> \<V>))
         then do {
           err \<leftarrow> check_linear_combi_l_dom_err q\<^sub>0 i;
           RETURN (p, xs, error_msg i err)
         } else do {
           ASSERT(fmlookup A i \<noteq> None);  
           let r = the (fmlookup A i);
           ASSERT(vars_llist r \<subseteq> \<V>);
           q \<leftarrow> full_normalize_poly (q\<^sub>0);
           ASSERT(vars_llist q \<subseteq> \<V>);
           pq \<leftarrow> mult_poly_full q r;
           ASSERT(vars_llist pq \<subseteq> \<V>);
           pq \<leftarrow> add_poly_l (p, pq);
           RETURN (pq, tl xs, CSUCCESS)
         }
      })
     ([], xs, CSUCCESS)
  }\<close>

definition check_linear_combi_l where
  \<open>check_linear_combi_l spec A \<V> i xs r = do{
  b\<leftarrow> RES(UNIV::bool set);
  if b \<or> i \<in># dom_m A \<or> xs = [] \<or> \<not>(vars_llist r \<subseteq> \<V>)
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i (i \<in># dom_m A) (xs = []) (\<not>(vars_llist r \<subseteq> \<V>));
    RETURN (error_msg i err)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l i A \<V> xs;
    if (is_cfailed err) 
    then do {
      RETURN err
    }
    else do {
      b \<leftarrow> weak_equality_l p r;
      b' \<leftarrow> weak_equality_l r spec;
      if b then (if b' then RETURN CFOUND else RETURN CSUCCESS) else do {
        c \<leftarrow> check_linear_combi_l_mult_err p r;
        RETURN (error_msg i c)
      }
    }
  }}\<close>


paragraph \<open>Deletion checking\<close>

definition check_extension_l_side_cond_err
  :: \<open>string \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string nres\<close>
where
  \<open>check_extension_l_side_cond_err v p' q = SPEC (\<lambda>_. True)\<close>

definition (in -)check_extension_l2
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial \<Rightarrow> (string code_status) nres\<close>
where
\<open>check_extension_l2 spec A \<V> i v p' = do {
  b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> i \<notin># dom_m A \<and> v \<notin> \<V>);
  if \<not>b
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c)
  } else do {
      let p' = p';
      let b = vars_llist p' \<subseteq> \<V>;
      if \<not>b
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p';
        RETURN (error_msg i c)
      }
      else do {
         ASSERT(vars_llist p' \<subseteq> \<V>);
         p2 \<leftarrow> mult_poly_full p' p';
         ASSERT(vars_llist p2 \<subseteq> \<V>);
         let p' = map (\<lambda>(a,b). (a, -b)) p';
         ASSERT(vars_llist p' \<subseteq> \<V>);
         q \<leftarrow> add_poly_l (p2, p');
         ASSERT(vars_llist q \<subseteq> \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p' q;
          RETURN (error_msg i c)
        }
      }
    }
           }\<close>




paragraph \<open>Extension checking\<close>

paragraph \<open>Step checking\<close>
definition PAC_checker_l_step_inv where
  \<open>PAC_checker_l_step_inv spec st' \<V> A \<longleftrightarrow>
  (\<forall>i\<in>#dom_m A. vars_llist (the (fmlookup A i)) \<subseteq> \<V>)\<close>

definition PAC_checker_l_step ::  \<open>_ \<Rightarrow> string code_status \<times> string set \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close> where
  \<open>PAC_checker_l_step = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT(\<not>is_cfailed st');
    ASSERT(PAC_checker_l_step_inv spec st' \<V> A);
    case st of
     CL _ _ _ \<Rightarrow>
       do {
        ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
         r \<leftarrow> full_normalize_poly (pac_res st);
        eq \<leftarrow> check_linear_combi_l spec A \<V> (new_id st) (pac_srcs st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          \<V>, fmupd (new_id st) r A)
        else RETURN (eq, \<V>, A)
   }
   | Del _ \<Rightarrow>
       do {
        ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
        eq \<leftarrow> check_del_l spec A (pac_src1 st);
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmdrop (pac_src1 st) A)
        else RETURN (eq, \<V>, A)
   }
   | Extension _ _ _ \<Rightarrow>
       do {
        ASSERT (PAC_checker_l_step_inv spec st' \<V> A);
         r \<leftarrow> full_normalize_poly (pac_res st);
        eq \<leftarrow> check_extension_l2 spec A \<V> (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then do {
          ASSERT(new_var st \<notin> vars_llist r \<and> vars_llist r \<subseteq> \<V>);
          r' \<leftarrow> add_poly_l ([([new_var st], -1)], r);
          RETURN (st',
            insert (new_var st) \<V>, fmupd (new_id st) r' A)}
        else RETURN (eq, \<V>, A)
   }}
 )\<close>

lemma pac_step_rel_raw_def:
  \<open>\<langle>K, V, R\<rangle> pac_step_rel_raw = pac_step_rel_raw K V R\<close>
  by (auto intro!: ext simp: relAPP_def)


subsection \<open>Correctness\<close>

text \<open>We now enter the locale to reason about polynomials directly.\<close>

context poly_embed
begin

lemma (in -) vars_llist_merge_coeffsD:
  \<open>x \<in> vars_llist (merge_coeffs pa)   \<Longrightarrow> x \<in> vars_llist pa\<close>
  apply (induction pa rule:merge_coeffs.induct)
  apply (auto split: if_splits)
  done
lemma (in -) add_nset_list_rel_add_mset_iff:
  \<open>(pa, add_mset (aa) (ys)) \<in> \<langle>R\<rangle>list_rel O {(c, a). a = mset c}  \<longleftrightarrow>
  (\<exists>pa\<^sub>1 pa\<^sub>2 x. pa = pa\<^sub>1 @ x # pa\<^sub>2 \<and> (pa\<^sub>1 @ pa\<^sub>2, ys) \<in> \<langle>R\<rangle>list_rel O {(c, a). a = mset c} \<and>
  (x, aa) \<in> R)\<close>
  apply (rule iffI)
  subgoal
    apply clarify
    apply (subgoal_tac \<open>aa \<in> set y\<close>)
  apply (auto dest!: split_list simp: list_rel_split_right_iff list_rel_append1 list_rel_split_left_iff
    list_rel_append2)
    apply (rule_tac x=cs in exI)
    apply (rule_tac x=xs in exI)
    apply (rule_tac x=x in exI)
    apply simp
      apply (rule_tac b = \<open>ysa@zs\<close> in relcompI)
    apply (auto dest!: split_list simp: list_rel_split_right_iff list_rel_append1 list_rel_split_left_iff
      list_rel_append2)
    by (metis add_mset_remove_trivial mset_remove1 multi_self_add_other_not_self remove1_idem)
  subgoal
    apply (auto dest!: split_list simp: list_rel_split_right_iff list_rel_append1 list_rel_split_left_iff
      list_rel_append2)
    apply (rule_tac b = \<open>cs@aa#ds\<close> in relcompI)
    apply (auto dest!: split_list simp: list_rel_split_right_iff list_rel_append1 list_rel_split_left_iff
      list_rel_append2)
    done
  done

lemma (in -) sorted_poly_rel_vars_llist2:
  \<open>(pa, r) \<in> sorted_poly_rel \<Longrightarrow> (vars_llist pa) = \<Union> (set_mset ` fst ` set_mset r)\<close>
    apply (auto split: if_splits simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def list_rel_append1
      list_rel_append2 list_rel_split_right_iff term_poly_list_rel_set_mset vars_llist_def image_Un
      term_poly_list_rel_def
      add_nset_list_rel_add_mset_iff dest!: split_list)
    apply (auto simp: list_rel_split_left_iff)
    done
lemma (in -)normalize_poly_p_vars: \<open>normalize_poly_p p q \<Longrightarrow> \<Union> (set_mset ` fst ` set_mset q) \<subseteq> \<Union> (set_mset ` fst ` set_mset p)\<close>
  by (induction rule: normalize_poly_p.induct)
    auto

lemma (in -)rtranclp_normalize_poly_p_vars: \<open>normalize_poly_p\<^sup>*\<^sup>* p q \<Longrightarrow> \<Union> (set_mset ` fst ` set_mset q) \<subseteq> \<Union> (set_mset ` fst ` set_mset p)\<close>
  by (induction rule: rtranclp_induct)
   (force dest!: normalize_poly_p_vars)+

lemma normalize_poly_normalize_poly_p2:
  assumes \<open>(p, p') \<in> unsorted_poly_rel\<close>
  shows \<open>normalize_poly p \<le> \<Down>{(xs,ys). (xs,ys)\<in>sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p} (SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r))\<close>
proof -
  have 1: \<open>sort_poly_spec p \<le> SPEC (\<lambda>p'. vars_llist p' = vars_llist p)\<close>
    unfolding sort_poly_spec_def vars_llist_def
    by (auto dest: mset_eq_setD)
  have [refine]: \<open>sort_poly_spec p \<le> \<Down>{(xs,ys). (xs,ys)\<in>sorted_repeat_poly_list_rel (rel2p (Id \<union> term_order_rel)) \<and>
      vars_llist xs \<subseteq> vars_llist p} (RETURN p')\<close>
    using sort_poly_spec_id[OF assms] apply -
    apply (rule order_trans)
    apply (rule SPEC_rule_conjI[OF 1])
    unfolding RETURN_def
    apply (subst (asm) conc_fun_RES)
    apply (subst (asm) RES_SPEC_eq)
    apply assumption
    apply (auto simp: conc_fun_RES)
      done
  have 1: \<open>SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r) = do {
       p'' \<leftarrow> RETURN p';
      ASSERT(p'' = p');
      SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p'' r)
   }\<close>
   by auto
  show ?thesis
    unfolding normalize_poly_def
    apply (subst 1)
    apply (refine_rcg)
    subgoal for pa p'
      by (force intro!: RES_refine simp: RETURN_def dest: vars_llist_merge_coeffsD sorted_poly_rel_vars_llist2
        merge_coeffs_is_normalize_poly_p
        subsetD vars_llist_merge_coeffsD)
    done
qed

lemma (in -)vars_llist_mult_poly_raw: \<open>vars_llist (mult_poly_raw p q) \<subseteq> vars_llist p \<union> vars_llist q\<close>
proof -
  have [simp]: \<open>foldl (\<lambda>b x. map (mult_monomials x) qs @ b) b ps = foldl (\<lambda>b x. map (mult_monomials x) qs @ b) [] ps @ b\<close>
    if \<open>NO_MATCH [] b\<close> for qs ps b
    by (induction ps arbitrary: b)
      (simp, metis (no_types, lifting) append_assoc foldl_Cons self_append_conv)
  have [simp]: \<open>x \<in> set (mult_monoms a aa) \<longleftrightarrow> x \<in> set a \<or> x \<in> set aa\<close> for x a aa
    by (induction a aa rule: mult_monoms.induct)
     (auto split: if_splits)
  have 0: \<open>vars_llist (map (mult_monomials (a, ba)) q) \<subseteq> vars_llist q \<union> set a\<close> for a ba q
    unfolding mult_monomials_def
    by (induction q) auto

  have \<open>vars_llist (foldl (\<lambda>b x. map (mult_monomials x) q @ b) [] p) \<subseteq> vars_llist p \<union> vars_llist q \<union> vars_llist b\<close> for b
    by (induction p) (use 0 in force)+
  then show ?thesis
    unfolding mult_poly_raw_def
    by auto
qed

lemma mult_poly_full_mult_poly_p'2:
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>mult_poly_full p q \<le> \<Down> {(xs,ys). (xs,ys)\<in>sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} (mult_poly_p' p' q')\<close>
  unfolding mult_poly_full_def mult_poly_p'_def
  apply (refine_rcg full_normalize_poly_normalize_poly_p
    normalize_poly_normalize_poly_p2[THEN order_trans])
  apply (subst RETURN_RES_refine_iff)
  apply (subst Bex_def)
  apply (subst mem_Collect_eq)
  apply (subst conj_commute)
  apply (rule mult_poly_raw_mult_poly_p[OF assms(1,2)])
  apply assumption
  subgoal
    using vars_llist_mult_poly_raw[of p q]
    unfolding conc_fun_RES
    by auto
  done

lemma mult_poly_full_spec2:
  assumes
    \<open>(p, p'') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q'') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>mult_poly_full p q \<le> \<Down>{(xs,ys). (xs,ys)\<in>sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q}
    (SPEC (\<lambda>s.  s - p'' * q'' \<in> ideal polynomial_bool))\<close>
proof -
  have 1: \<open>{(xs, ys). (xs, ys) \<in> sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} =
    {(xs, ys). (xs, ys) \<in> sorted_poly_rel  \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} O{(xs, ys). (xs, ys) \<in>  mset_poly_rel}\<close>
    by blast
  obtain p' q' where
    pq: \<open>(p, p') \<in> sorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel\<close>
    \<open>(q', q'') \<in> mset_poly_rel\<close>
    using assms by auto
  show ?thesis
    apply (rule mult_poly_full_mult_poly_p'2[THEN order_trans, OF pq(1,3)])
    apply (subst 1)
    apply (subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    unfolding mult_poly_p'_def
    apply refine_vcg
    by (use pq assms in \<open>auto simp: mult_poly_p'_def mset_poly_rel_def
      dest!: rtranclp_normalize_poly_p_poly_of_mset rtranclp_mult_poly_p_mult_ideal_final
      intro!: RES_refine\<close>)
qed

lemma mult_poly_full_mult_poly_spec:
  assumes \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close> \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows \<open>mult_poly_full p q \<le> \<Down> {(xs,ys). (xs,ys)\<in>sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} (mult_poly_spec p' q')\<close>
  apply (rule mult_poly_full_spec2[OF assms, THEN order_trans])
  apply (rule ref_two_step')
  by (auto simp: mult_poly_spec_def dest: ideal.span_neg)


lemma vars_llist_merge_coeff0: \<open>vars_llist (merge_coeffs0 paa) \<subseteq> vars_llist paa\<close>
  by (induction paa rule: merge_coeffs0.induct)
    auto

lemma sort_poly_spec_id'2:
  assumes \<open>(p, p') \<in> unsorted_poly_rel_with0\<close>
  shows \<open>sort_poly_spec p \<le> \<Down> {(xs, ys). (xs, ys) \<in> sorted_repeat_poly_rel_with0 \<and>
     vars_llist xs \<subseteq> vars_llist p} (RETURN p')\<close>
proof -
  obtain y where
    py: \<open>(p, y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    p'_y: \<open>p' = mset y\<close>
    using assms
    unfolding fully_unsorted_poly_list_rel_def poly_list_rel_def sorted_poly_list_rel_wrt_def
    by (auto simp: list_mset_rel_def br_def)
  then have [simp]: \<open>length y = length p\<close>
    by (auto simp: list_rel_def list_all2_conv_all_nth)
  have H: \<open>(x, p')
        \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel\<close>
     if px: \<open>mset p = mset x\<close> and \<open>sorted_wrt (rel2p (Id \<union> lexord var_order_rel)) (map fst x)\<close>
     for x :: \<open>llist_polynomial\<close>
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
    unfolding sort_poly_spec_def poly_list_rel_def sorted_repeat_poly_list_rel_with0_wrt_def
    by refine_rcg (auto intro: H simp: vars_llist_def dest: mset_eq_setD)
qed

lemma sort_all_coeffs_unsorted_poly_rel_with02:
  assumes \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
  shows \<open>sort_all_coeffs p \<le> \<Down> {(xs, ys). (xs, ys) \<in> unsorted_poly_rel_with0 \<and> vars_llist xs \<subseteq> vars_llist p} (RETURN p')\<close>
proof -
  have H: \<open>(map (\<lambda>(a, y). (mset a, y)) (rev p)) =
          map (\<lambda>(a, y). (mset a, y)) s \<longleftrightarrow>
          (map (\<lambda>(a, y). (mset a, y)) p) =
          map (\<lambda>(a, y). (mset a, y)) (rev s)\<close> for s
    by (auto simp flip: rev_map simp: eq_commute[of \<open>rev (map _ _)\<close> \<open>map _ _\<close>])
  have 1: \<open>\<And>s y. (p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
           p' = mset y \<Longrightarrow>
           map (\<lambda>(a, y). (mset a, y)) (rev p) = map (\<lambda>(a, y). (mset a, y)) s \<Longrightarrow>
           \<forall>x\<in>set s. sorted_wrt var_order (fst x) \<Longrightarrow>
           (s, map (\<lambda>(a, y). (mset a, y)) s)
           \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
    by (auto 4 4 simp: rel2p_def
        dest!: list_rel_unsorted_term_poly_list_relD
        dest: shuffle_terms_distinct_iff["THEN" iffD1]
        intro!: map_mset_unsorted_term_poly_list_rel
        sorted_wrt_mono_rel[of _ \<open>rel2p (var_order_rel)\<close> \<open>rel2p (Id \<union> var_order_rel)\<close>])
  have 2: \<open>\<And>s y. (p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
           p' = mset y \<Longrightarrow>
           map (\<lambda>(a, y). (mset a, y)) (rev p) = map (\<lambda>(a, y). (mset a, y)) s \<Longrightarrow>
           \<forall>x\<in>set s. sorted_wrt var_order (fst x) \<Longrightarrow>
           mset y = {#case x of (a, x) \<Rightarrow> (mset a, x). x \<in># mset s#}\<close>
    by (metis (no_types, lifting) list_rel_unsorted_term_poly_list_relD mset_map mset_rev)
  have vars_llits_alt_def:
    \<open>x \<in> vars_llist p \<longleftrightarrow> x \<in> \<Union>(set_mset ` fst ` set (map (\<lambda>(a, y). (mset a, y)) (rev p)))\<close> for p x
    by (force simp: vars_llist_def)
 
  have [intro]: \<open>map (\<lambda>(a, y). (mset a, y)) (rev p) = map (\<lambda>(a, y). (mset a, y)) s \<Longrightarrow>
    x \<in> vars_llist s \<Longrightarrow> x \<in> vars_llist p\<close> for s x
    unfolding vars_llits_alt_def
    by (auto simp: vars_llist_def image_image dest!: split_list)
  show ?thesis
    by (rule sort_all_coeffs[THEN order_trans])
     (use assms in \<open>auto simp: shuffle_coefficients_def poly_list_rel_def
      RETURN_def fully_unsorted_poly_list_rel_def list_mset_rel_def
      br_def dest: list_rel_unsorted_term_poly_list_relD
      intro!: RES_refine 1 2
      intro!: relcompI[of _  \<open>map (\<lambda>(a, y). (mset a, y)) (rev p)\<close>]\<close>)
qed

lemma full_normalize_poly_normalize_poly_p2:
  assumes \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
  shows \<open>full_normalize_poly p \<le> \<Down> {(xs, ys). (xs, ys) \<in> sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p}
      (SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r))\<close>
  (is \<open>?A \<le> \<Down> ?R ?B\<close>)
proof -
  have 1: \<open>?B = do {
     p' \<leftarrow> RETURN p';
     p' \<leftarrow> RETURN p';
     SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r)
    }\<close>
    by auto
  have [refine0]: \<open>sort_all_coeffs p \<le> SPEC(\<lambda>q. (q, p') \<in> {(xs, ys). (xs, ys) \<in> unsorted_poly_rel_with0\<and> vars_llist xs \<subseteq> vars_llist p})\<close>
    by (rule sort_all_coeffs_unsorted_poly_rel_with02[OF assms, THEN order_trans])
     (auto simp: conc_fun_RES RETURN_def)
  have [refine0]: \<open>sort_poly_spec p \<le> SPEC (\<lambda>c. (c, p') \<in> 
      {(xs, ys). (xs, ys) \<in> sorted_repeat_poly_rel_with0 \<and> vars_llist xs \<subseteq> vars_llist p})\<close>
    if \<open>(p, p') \<in> unsorted_poly_rel_with0\<close>
    for p p'
    by (rule sort_poly_spec_id'2[THEN order_trans, OF that])
      (auto simp: conc_fun_RES RETURN_def)
  show ?thesis
    apply (subst 1)
    unfolding full_normalize_poly_def
    apply (refine_rcg)
    by (use in \<open>auto intro!: RES_refine
      dest!: merge_coeffs0_is_normalize_poly_p
      dest!:  set_mp[OF vars_llist_merge_coeff0]
      simp: RETURN_def\<close>)
qed

lemma add_poly_full_spec:
  assumes
    \<open>(p, p'') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q'') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>add_poly_l (p, q) \<le> \<Down>(sorted_poly_rel O mset_poly_rel)
    (SPEC (\<lambda>s.  s - (p'' + q'' )\<in> ideal polynomial_bool))\<close>
proof -
  obtain p' q' where
    pq: \<open>(p, p') \<in> sorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel\<close>
    \<open>(q', q'') \<in> mset_poly_rel\<close>
    using assms by auto
  show ?thesis
    apply (rule add_poly_l_add_poly_p'[THEN order_trans, OF pq(1,3)])
    apply (subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    by (use pq assms in \<open>clarsimp simp: add_poly_p'_def mset_poly_rel_def ideal.span_zero
      dest!: rtranclp_add_poly_p_polynomial_of_mset_full
      intro!: RES_refine\<close>)
qed
lemma (in -)add_poly_l_simps:
   \<open>add_poly_l  (p, q) =
        (case (p,q) of
          (p, []) \<Rightarrow> RETURN p
        | ([], q) \<Rightarrow> RETURN q
        | ((xs, n) # p, (ys, m) # q) \<Rightarrow>
            (if xs = ys then if n + m = 0 then add_poly_l (p, q) else
               do {
                 pq \<leftarrow> add_poly_l (p, q);
                 RETURN ((xs, n + m) # pq)
             }
            else if (xs, ys) \<in> term_order_rel
              then do {
                 pq \<leftarrow> add_poly_l (p, (ys, m) # q);
                 RETURN ((xs, n) # pq)
            }
            else do {
                 pq \<leftarrow> add_poly_l ((xs, n) # p, q);
                 RETURN ((ys, m) # pq)
            }))\<close>
    apply (subst add_poly_l_def)
    apply (subst RECT_unfold, refine_mono)
    apply (subst add_poly_l_def[symmetric, abs_def])+
    apply auto
    done
lemma nat_less_induct_useful:
  assumes \<open>P 0\<close>\<open>(\<And>m. (\<forall>n < Suc m. P n) \<Longrightarrow> P (Suc m))\<close>
  shows \<open>P m\<close>
    using assms
    apply(induction m rule: nat_less_induct)
  apply (case_tac n)
  apply auto
  done
lemma add_poly_l_vars: \<open>add_poly_l (p, q) \<le> SPEC(\<lambda>xa. vars_llist xa \<subseteq> vars_llist p \<union> vars_llist q)\<close>
  apply (induction "length p + length q" arbitrary: p q rule: nat_less_induct_useful)
  subgoal
    apply (subst add_poly_l_simps)
    apply (auto split: list.splits)
    done
  subgoal premises p for n p q
    using p(1)[rule_format, of n \<open>tl p\<close> q]
    using p(1) [rule_format, of n p \<open>tl q\<close>]  p(1)[rule_format, of \<open>n-1\<close> \<open>tl p\<close> \<open>tl q\<close>]
    using p(2-)
    apply (subst add_poly_l_simps)
    apply (case_tac p)
    subgoal by (auto split: list.splits)
    subgoal
      apply (simp split: prod.splits list.splits if_splits)
      apply (intro conjI impI allI)
      apply (auto intro: order_trans intro!: Refine_Basic.bind_rule)
      apply (rule order_trans, assumption, auto)+
      done
    done
  done
lemma pw_le_SPEC_merge: \<open>f \<le> \<Down>R g \<Longrightarrow> f \<le> RES \<Phi> \<Longrightarrow> f \<le>\<Down>{(x,y). (x,y)\<in>R \<and> x \<in> \<Phi>} g\<close>
   by (simp add: pw_conc_inres pw_conc_nofail pw_le_iff)
lemma add_poly_l_add_poly_p'2:
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>add_poly_l (p, q) \<le> \<Down> {(xs,ys). (xs,ys) \<in> sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} (add_poly_p' p' q')\<close>
  unfolding add_poly_p'_def
  apply (rule pw_le_SPEC_merge[THEN order_trans])
  apply (rule add_poly_l_spec[THEN fref_to_Down_curry_right, of _ p' q'])
  using assms apply auto[2]
  apply (rule add_poly_l_vars)
  apply (auto simp: conc_fun_RES)
  done

lemma add_poly_full_spec2:
  assumes
    \<open>(p, p'') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q'') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>add_poly_l (p, q) \<le> \<Down> {(xs,ys). (xs,ys) \<in> sorted_poly_rel  O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q}
    (SPEC (\<lambda>s.  s - (p'' + q'' )\<in> ideal polynomial_bool))\<close>
proof -
  obtain p' q' where
    pq: \<open>(p, p') \<in> sorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel\<close>
    \<open>(q', q'') \<in> mset_poly_rel\<close>
    using assms by auto
  have 1: \<open>{(xs, ys). (xs, ys) \<in> sorted_poly_rel O mset_poly_rel  \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q} =
    {(xs, ys). (xs, ys) \<in> sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q}  O mset_poly_rel\<close>
    by blast
  show ?thesis
    apply (rule add_poly_l_add_poly_p'2[THEN order_trans, OF pq(1,3)])
    apply (subst 1, subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    by (use pq assms in \<open>clarsimp simp: add_poly_p'_def mset_poly_rel_def ideal.span_zero
      dest!: rtranclp_add_poly_p_polynomial_of_mset_full
      intro!: RES_refine\<close>)
qed

lemma add_poly_full_spec3:
  assumes
    \<open>(p, p'') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q'') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>add_poly_l (p, q) \<le> \<Down> {(xs,ys). (xs,ys) \<in> sorted_poly_rel  O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p \<union> vars_llist q}
    (add_poly_spec p'' q'')\<close>
  apply (rule add_poly_full_spec2[OF assms, THEN order_trans])
  apply (rule ref_two_step')
  apply (auto simp: add_poly_spec_def dest: ideal.span_neg)
  done

lemma full_normalize_poly_full_spec2:
  assumes
    \<open>(p, p'') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>full_normalize_poly p \<le> \<Down>{(xs, ys). (xs, ys) \<in> sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p}
    (SPEC (\<lambda>s.  s - (p'')\<in> ideal polynomial_bool \<and> vars s \<subseteq> vars p''))\<close>
proof -
  obtain p' q' where
    pq: \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    using assms by auto
  have 1: \<open>\<Down> {(xs, ys). (xs, ys) \<in> sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p} =
    \<Down> ({(xs, ys). (xs, ys) \<in> sorted_poly_rel \<and> vars_llist xs \<subseteq> vars_llist p} O mset_poly_rel)\<close>
    by (rule cong[of \<open>\<lambda>u. \<Down>u\<close>]) auto
  show ?thesis
    apply (rule full_normalize_poly_normalize_poly_p2[THEN order_trans, OF pq(1)])
    apply (subst 1)
    apply (subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    by (use pq assms in \<open>clarsimp simp: add_poly_p'_def mset_poly_rel_def ideal.span_zero
          ideal.span_zero rtranclp_normalize_poly_p_poly_of_mset
      dest!: rtranclp_add_poly_p_polynomial_of_mset_full
      intro!: RES_refine\<close>)
qed
lemma (in -) add_poly_l_simps_empty[simp]: \<open>add_poly_l ([], a) = RETURN a\<close>
  by (subst add_poly_l_simps, cases a) auto

definition term_rel :: \<open>_\<close> where
  \<open>term_rel = sorted_poly_rel O mset_poly_rel\<close>
definition raw_term_rel where
  \<open>raw_term_rel = fully_unsorted_poly_rel O mset_poly_rel\<close>
  term sorted_wrt
term insort
fun (in -)insort_wrt :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>insort_wrt _ _ a [] = [a]\<close> |
  \<open>insort_wrt f P a (x # xs) =
     (if P (f a) (f x) then a # x # xs else x # insort_wrt f P a xs)\<close>

lemma (in -)set_insort_wrt [simp]: \<open>set (insort_wrt P f a xs) = insert a (set xs)\<close>
  by (induction P f a xs rule: insort_wrt.induct) auto


lemma (in -)sorted_insort_wrt:
  \<open>transp P \<Longrightarrow> total (p2rel P) \<Longrightarrow> sorted_wrt (\<lambda>a b. P (f a) (f b)) xs \<Longrightarrow> reflp_on P (f ` set (a # xs)) \<Longrightarrow>
  sorted_wrt (\<lambda>a b. P (f a) (f b)) (insort_wrt f P a xs)\<close>
  apply (induction f P a xs rule: insort_wrt.induct)
  subgoal by auto
  subgoal for f P a x xs
    apply (cases \<open>x=a\<close>)
    apply (auto simp: Relation.total_on_def p2rel_def reflp_on_def dest: transpD sympD reflpD elim: reflpE)+
    apply (force simp: Relation.total_on_def p2rel_def reflp_on_def dest: transpD sympD reflpD elim: reflpE)+
    done
  done

lemma (in -)sorted_insort_wrt3: (*(* reflp_on P (f ` set (a # xs)) \<Longrightarrow>  *)*)
  \<open>transp P \<Longrightarrow> total (p2rel P) \<Longrightarrow> sorted_wrt (\<lambda>a b. P (f a) (f b)) xs \<Longrightarrow> f a\<notin>f ` set xs \<Longrightarrow>
  sorted_wrt (\<lambda>a b. P (f a) (f b)) (insort_wrt f P a xs)\<close>
  apply (induction f P a xs rule: insort_wrt.induct)
  subgoal by auto
  subgoal for f P a x xs
    apply (cases \<open>x=a\<close>)
    apply (auto simp: Relation.total_on_def p2rel_def reflp_on_def dest: transpD sympD reflpD elim: reflpE)
    done
  done
lemma (in -)sorted_insort_wrt4:
  \<open>transp P \<Longrightarrow> total (p2rel P) \<Longrightarrow> f a\<notin>f ` set xs  \<Longrightarrow> sorted_wrt (\<lambda>a b. P (f a) (f b)) xs \<Longrightarrow> f'=(\<lambda>a b. P (f a) (f b)) \<Longrightarrow>
  sorted_wrt f' (insort_wrt f P a xs)\<close>
  using sorted_insort_wrt3[of P f xs a] by auto

text \<open>When \<^term>\<open>a\<close> is empty, constants are added up.\<close>
lemma add_poly_p_insort:
  \<open>fst a \<noteq> [] \<Longrightarrow> vars_llist [a] \<inter> vars_llist b = {} \<Longrightarrow> add_poly_l ([a],b) = RETURN (insort_wrt fst term_order a b)\<close>
  apply (induction b)
  subgoal
    by (subst add_poly_l_simps) auto
  subgoal for y ys
    apply (cases a, cases y)
    apply (subst add_poly_l_simps)
    apply (auto simp: rel2p_def Int_Un_distrib)
    done
  done

lemma (in -) map_insort_wrt: \<open>map f (insort_wrt f P x xs) = insort_wrt id P (f x) (map f xs)\<close>
  by (induction xs)
   auto

lemma (in-) distinct_insort_wrt[simp]: \<open>distinct (insort_wrt f P x xs) \<longleftrightarrow> distinct (x # xs)\<close>
  by (induction xs) auto
lemma (in -) mset_insort_wrt[simp]: \<open>mset (insort_wrt f P x xs) = add_mset x (mset xs)\<close>
  by (induction xs)
    auto
lemma (in -) transp_term_order_rel: \<open>transp (\<lambda>x y. (fst x, fst y) \<in> term_order_rel)\<close>
  apply (auto simp: transp_def)
  by (smt lexord_partial_trans lexord_trans trans_less_than_char var_order_rel_def)

lemma (in -) transp_term_order: \<open>transp term_order\<close>
  using transp_term_order_rel
  by (auto simp: transp_def rel2p_def)

lemma total_term_order_rel: \<open>total (term_order_rel)\<close>
  apply standard
  using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def[symmetric]] by (auto simp: p2rel_def intro!: )

lemma monomom_rel_mapI: \<open>sorted_wrt (\<lambda>x y. (fst x, fst y) \<in> term_order_rel) r \<Longrightarrow>
  distinct (map fst r) \<Longrightarrow>
  (\<forall>x\<in>set r. distinct (fst x) \<and> sorted_wrt var_order (fst x)) \<Longrightarrow>
  (r, map (\<lambda>(a, y). (mset a, y)) r) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
  apply (induction r)
  subgoal
    by auto
  subgoal for x xs
    apply (cases x)
    apply (auto simp: term_poly_list_rel_def rel2p_def)
    done
  done

lemma add_poly_l_single_new_var:
  assumes \<open>(r, ra) \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>v \<notin> vars_llist r\<close> and
   v: \<open>(v, v') \<in> var_rel\<close>
  shows
    \<open>add_poly_l ([([v], -1)], r)
    \<le> \<Down> {(a,b). (a,b)\<in>sorted_poly_rel O mset_poly_rel \<and> vars_llist a \<subseteq> insert v (vars_llist r)}
    (SPEC
      (\<lambda>r0. r0 = ra - Var v' \<and>
    vars r0 = vars ra \<union> {v'}))\<close>
proof -
  have [simp]: \<open>([], ra) \<in> term_rel \<Longrightarrow> ([([v], - 1)], ra - Var v') \<in> term_rel\<close> for ra
    using v
    apply (auto intro!: RETURN_RES_refine relcompI[of _ \<open>mset [(mset [v], -1)]\<close>]
      simp: mset_poly_rel_def var_rel_def br_def Const_1_eq_1 term_rel_def)
    apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
      term_poly_list_rel_def
      intro!: relcompI[of _ \<open>[(mset [v], -1)]\<close>])
    done
  have [iff]: \<open>v' \<notin> vars ra\<close>
  proof (rule ccontr)
    assume H: \<open>\<not>?thesis\<close>
    then have \<open>\<phi> v \<in> \<phi> ` vars_llist r\<close>
      using assms sorted_poly_rel_vars_llist[OF assms(1)]
      by (auto simp: var_rel_def br_def)
    then have \<open>v \<in> vars_llist r\<close>
      using  \<phi>_inj by (auto simp: image_iff inj_def)
    then show \<open>False\<close>
      using assms(2) by fast
  qed
  have [simp]: \<open>([], ra) \<in> term_rel \<Longrightarrow> vars (ra - Var v') = vars (ra) \<union> {v'}\<close> for ra
    by (auto simp: term_rel_def mset_poly_rel_def)
  have [simp]: \<open>v' \<notin> vars ra \<Longrightarrow> vars (ra - Var v') = vars ra \<union> {v'}\<close>
    by (auto simp add: vars_subst_in_left_only_diff_iff)
  have [iff]: \<open>([v], b) \<notin> set r \<close> for b
    using assms
    by (auto simp: vars_llist_def)
  have
    \<open>add_poly_l ([([v], -1)], r)
    \<le> \<Down> (sorted_poly_rel O mset_poly_rel)
    (SPEC
      (\<lambda>r0. r0 = ra - Var v' \<and>
    vars r0 = vars ra \<union> {v'}))\<close>
    using v sorted_poly_rel_vars_llist[OF assms(1)]
    apply -
    apply (subst add_poly_p_insort)
    apply (use assms in auto)
    apply (rule RETURN_RES_refine)
    apply auto
    apply (rule_tac b=\<open>add_mset ({#v#}, -1) (y)\<close> in relcompI)
    apply (auto simp: rel2p_def mset_poly_rel_def Const_1_eq_1 var_rel_def br_def)
    apply (auto simp: sorted_poly_list_rel_wrt_def sorted_wrt_map)
    apply (rule_tac b = \<open>map (\<lambda>(a,b). (mset a, b)) ((insort_wrt fst term_order ([v], - 1) r))\<close> in relcompI)
    apply (auto simp: list_mset_rel_def br_def map_insort_wrt)
      prefer 2
    apply (auto dest!: term_poly_list_rel_list_relD)[]
      prefer 2
    apply (auto intro!: sorted_insort_wrt4 monomom_rel_mapI simp: rel2p_def transp_term_order total_term_order_rel
      transp_term_order_rel map_insort_wrt)
    apply (auto dest!: split_list simp: list_rel_append1 list_rel_split_right_iff
      term_poly_list_rel_def)
    done
  then show ?thesis
    using add_poly_l_vars[of \<open>[([v], - 1)]\<close> r]
    unfolding conc_fun_RES
    apply (subst (asm) RES_SPEC_eq)
    apply (rule order_trans)
    apply (rule SPEC_rule_conjI)
    apply assumption
    apply auto
    done
qed

  
lemma empty_sorted_poly_rel[simp,intro]: \<open> ([], 0) \<in> sorted_poly_rel O mset_poly_rel\<close>
  by (auto intro!: relcompI[of \<open>[]\<close>] simp: mset_poly_rel_def)

abbreviation epac_step_rel where
  \<open>epac_step_rel \<equiv> p2rel (\<langle>Id, fully_unsorted_poly_rel O mset_poly_rel, var_rel\<rangle> pac_step_rel_raw)\<close>

lemma single_valued_monomials: \<open>single_valued (\<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel)\<close>
  by (intro single_valued_relcomp list_rel_sv)
  (auto simp: mset_poly_rel_def sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    single_valued_def term_poly_list_rel_def)
lemma single_valued_term: \<open>single_valued (sorted_poly_rel O mset_poly_rel) \<close>
  using single_valued_monomials apply -
  by (rule single_valued_relcomp)
   (auto simp: mset_poly_rel_def sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    single_valued_def )


lemma single_valued_poly:
  \<open>(ysa, cs) \<in> \<langle>sorted_poly_rel O mset_poly_rel \<times>\<^sub>r nat_rel\<rangle>list_rel \<Longrightarrow>
  (ysa, csa) \<in> \<langle>sorted_poly_rel O mset_poly_rel \<times>\<^sub>r nat_rel\<rangle>list_rel \<Longrightarrow>
  cs = csa\<close>
  using list_rel_sv[of \<open>sorted_poly_rel O mset_poly_rel \<times>\<^sub>r nat_rel\<close>, OF prod_rel_sv[OF single_valued_term]]
  by (auto simp: single_valued_def)

lemma check_linear_combi_l_check_linear_comb:
  assumes \<open>(A, B) \<in> fmap_polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(i, i') \<in> nat_rel\<close>
    \<open>(\<V>', \<V>) \<in> \<langle>var_rel\<rangle>set_rel\<close> and
    xs: \<open>(xs, xs') \<in> \<langle>(fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r nat_rel\<rangle>list_rel\<close> and
    A: \<open>\<And>i. i \<in># dom_m A \<Longrightarrow> vars_llist (the (fmlookup A i)) \<subseteq> \<V>'\<close>
  shows
    \<open>check_linear_combi_l spec A \<V>' i xs r \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
    (is_cfound st \<longrightarrow> spec = r) \<and> (b \<longrightarrow> vars_llist r \<subseteq> \<V>' \<and> i \<notin># dom_m A)} (check_linear_comb B \<V> xs' i' r')\<close>
proof -
  have \<V>: \<open>\<V> = \<phi>`\<V>'\<close>
    using assms(4) unfolding set_rel_def var_rel_def
    by (auto simp: br_def)

  define f where
    \<open>f = (\<lambda>ys::((char list list \<times> int) list \<times> nat) list.
        (\<forall>x \<in> set (take (length ys) xs'). snd x \<in># dom_m B \<and> vars (fst x) \<subseteq> \<V>))\<close>
  let ?I = \<open>\<lambda>(p, xs'', err). \<not>is_cfailed err \<longrightarrow> 
    (\<exists>r ys. (p, r) \<in> sorted_poly_rel O mset_poly_rel \<and> f ys \<and> vars_llist p \<subseteq> \<V>' \<and>
    (\<Sum>(p,n) \<in># mset (take (length ys) xs'). the (fmlookup B n) * p) - r \<in> ideal polynomial_bool \<and> xs = ys @ xs'' \<and>
    (xs'', drop (length ys) xs') \<in> \<langle>(fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r nat_rel\<rangle>list_rel)\<close>

  have [simp]: \<open>length xs = length xs'\<close>
    using xs by (auto simp: list_rel_imp_same_length)

  have [simp]: \<open>drop (length ysa) xs' = cs @ (b) # ysb \<Longrightarrow> length ysa < length xs'\<close> for ysa cs b ysb
    by (rule ccontr) auto

  have Hf2: \<open>(\<Sum>(p, n)\<leftarrow>cs. the (fmlookup B n) * p) + the (fmlookup B bb) * ad - xf \<in> More_Modules.ideal polynomial_bool\<close>
    if 1: \<open>(\<Sum>(p, n)\<leftarrow>cs. the (fmlookup B n) * p) - r \<in> More_Modules.ideal polynomial_bool\<close> and
      2: \<open>xd - xb * the (fmlookup B bb) \<in> More_Modules.ideal polynomial_bool\<close> and
      3: \<open>xb - ad \<in> More_Modules.ideal polynomial_bool\<close> and
      4: \<open>xf - (r + xd)  \<in> More_Modules.ideal polynomial_bool\<close>
    for a ba bb r ys cs ysa ad ysc x y xa xb xc xd xe xf
  proof -
    have 2: \<open>xd - ad * the (fmlookup B bb) \<in> More_Modules.ideal polynomial_bool\<close> 
      using 2 3
      by (smt diff_add_eq group_eq_aux ideal.scale_left_diff_distrib ideal.span_add_eq
          ideal_mult_right_in)
    note two = ideal.span_neg[OF 2]
    note 4 = ideal.span_neg[OF 4]
    note 5 = ideal.span_add[OF 1 two, simplified]
    note 6 = ideal.span_add[OF 4 5]
    show ?thesis
      using 6 by (auto simp: algebra_simps)
  qed


  have H[simp]: \<open>length ys < length xs \<Longrightarrow>
    i < length xs' - length ys \<longleftrightarrow> (i < length xs' - Suc (length ys) \<or> i = length xs' - length ys - 1)\<close> for ys i
    by auto
  have lin: \<open>linear_combi_l  i' A \<V>' xs \<le> \<Down> {((p, xs, err), (b, p')). (\<not>b \<longrightarrow> is_cfailed err) \<and>
        (b \<longrightarrow>(p, p') \<in> sorted_poly_rel O mset_poly_rel)}
    (SPEC(\<lambda>(b, r). b \<longrightarrow> ((\<forall>i \<in> set xs'. snd i \<in># dom_m B \<and> vars (fst i) \<subseteq> \<V>) \<and>
       (\<Sum>(p,n) \<in># mset xs'. the (fmlookup B n) * p) - r \<in> ideal polynomial_bool)))\<close>
    using assms(1) xs
    unfolding linear_combi_l_def conc_fun_RES check_linear_combi_l_dom_err_def term_rel_def[symmetric]
      raw_term_rel_def[symmetric] error_msg_def in_dom_m_lookup_iff[symmetric] apply -
    apply (rule ASSERT_leI)
    subgoal using assms unfolding linear_combi_l_pre_def by blast
    apply (subst (2) RES_SPEC_eq)
    apply (rule WHILET_rule[where R = \<open>measure (\<lambda>(_, xs, p). if is_cfailed p then 0 else Suc (length xs))\<close>
      and I = \<open>?I\<close>])
    subgoal by auto
    subgoal using xs by (auto 5 5 intro!: exI[of _ 0] intro: exI[of _xs] exI[of _ \<open>[]\<close>] ideal.span_zero simp: f_def)
    subgoal for s
      unfolding term_rel_def[symmetric]
      apply (refine_vcg full_normalize_poly_full_spec2[THEN order_trans, unfolded term_rel_def[symmetric]
        raw_term_rel_def[symmetric]])
      subgoal
        by clarsimp
      subgoal using xs by auto
      subgoal
        by (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
      subgoal
        by (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply (use assms(6) in auto)
        apply (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply (rule_tac P = \<open>(x, fst (hd (drop (length xs' - length (fst (snd s))) xs'))) \<in> raw_term_rel\<close> in TrueE)
        apply (auto simp: list_rel_imp_same_length)[2]
        apply (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply (auto simp: conc_fun_RES)
        apply refine_vcg
        subgoal for a ba bb r ys cs ysa ad ysc x y xa xb
           by auto
      apply (rule mult_poly_full_spec2[THEN order_trans, unfolded term_rel_def[symmetric]])
      apply assumption
      apply auto
      unfolding conc_fun_RES
      apply auto
      apply refine_vcg
      subgoal using A by simp blast
      apply (rule add_poly_full_spec2[THEN order_trans, unfolded term_rel_def[symmetric]])
      apply assumption
      apply (auto simp: )
      apply (subst conc_fun_RES)
      apply clarsimp_all
      apply (auto simp: f_def take_Suc_conv_app_nth list_rel_imp_same_length single_valued_poly)
      apply (rule_tac x=yse in exI)
      apply (auto simp: f_def take_Suc_conv_app_nth list_rel_imp_same_length[symmetric] single_valued_poly)
        apply (auto dest!: sorted_poly_rel_vars_llist[unfolded term_rel_def[symmetric]]
          fully_unsorted_poly_rel_vars_subset_vars_llist[unfolded raw_term_rel_def[symmetric]]
          simp: \<V> intro: Hf2)[]
        apply (auto intro: Hf2)
          apply force
      done 
    subgoal for s
      unfolding term_rel_def[symmetric] f_def
      apply simp
      apply (case_tac \<open>is_cfailed (snd (snd s))\<close>; cases s)
      apply simp_all
      apply (rule_tac x=False in exI)
      apply clarsimp_all
      apply (rule_tac x=True in exI)
      apply clarsimp_all
      apply auto
      done
    done
  have [iff]: \<open> xs = [] \<longleftrightarrow> xs' = []\<close>
    using  list_rel_imp_same_length[OF assms(5)]
    by (metis length_0_conv)
  show ?thesis
    using sorted_poly_rel_vars_llist[OF assms(2)] list_rel_imp_same_length[OF assms(5)]
      fmap_rel_nat_rel_dom_m[OF assms(1)] assms(3) assms(2)
    unfolding check_linear_combi_l_def check_linear_comb_def check_linear_combi_l_mult_err_def
      weak_equality_l_def conc_fun_RES term_rel_def[symmetric] check_linear_combi_l_pre_err_def
      error_msg_def apply -
      apply simp
    apply (refine_vcg lin[THEN order_trans, unfolded term_rel_def[symmetric]])
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (auto split: if_splits simp: bind_RES_RETURN_eq)
      apply (rule lin[THEN order_trans, unfolded term_rel_def[symmetric]])
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (auto 5 3 split: if_splits simp: bind_RES_RETURN_eq \<V>)
    apply (frule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES)
    apply (drule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES)
    apply (rule lin[THEN order_trans, unfolded term_rel_def[symmetric]])
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (auto 5 3 split: if_splits simp: bind_RES_RETURN_eq \<V>)
    apply (drule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES bind_RES_RETURN_eq)
    done
qed
thm remap_polys_l_remap_polys

definition remap_polys_with_err :: \<open>int mpoly \<Rightarrow> int mpoly \<Rightarrow> nat set \<Rightarrow> (nat, int_poly) fmap \<Rightarrow> (status \<times> fpac_step) nres\<close> where
  \<open>remap_polys_with_err spec spec0 = (\<lambda>\<V> A. do{
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars spec0 \<subseteq> \<V>');
   failed \<leftarrow> SPEC(\<lambda>_::bool. True);
   if failed
   then do {
      RETURN (FAILED, \<V>, fmempty)
   }
   else do {
     (b, N) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(b, \<V>, A'). \<not>is_failed b)
       (\<lambda>i (b, \<V>, A').
          if i \<in># dom_m A
          then do {
            ASSERT(\<not>is_failed b);
            err \<leftarrow> RES {FAILED,SUCCESS};
            if is_failed err then SPEC(\<lambda>(err', \<V>, A'). err = err')
            else do {
              p \<leftarrow> SPEC(\<lambda>p. the (fmlookup A i) - p \<in> ideal polynomial_bool \<and> vars p \<subseteq> vars (the (fmlookup A i)));
              eq \<leftarrow> SPEC(\<lambda>eq. eq \<noteq> FAILED \<and> (eq = FOUND \<longrightarrow> p = spec));
              \<V> \<leftarrow> SPEC(\<lambda>\<V>'. \<V> \<union> vars (the (fmlookup A i)) \<subseteq> \<V>');
              RETURN(merge_status eq err, \<V>, fmupd i p A')
              }
            }
          else RETURN (b, \<V>, A'))
       (SUCCESS, \<V>, fmempty);
       RETURN (b, N)
     }
   })\<close>

lemma remap_polys_with_err_spec:
  \<open>remap_polys_with_err spec spec0 \<V> A \<le> \<Down>{(a,(err, \<V>', A)). a = (err, \<V>', A) \<and> (\<not>is_failed err \<longrightarrow> vars spec0 \<subseteq> \<V>')} (remap_polys_polynomial_bool spec \<V> A)\<close>
proof -
  have [dest]: \<open>set_mset (dom_m x2a) = set_mset (dom_m A) \<Longrightarrow> dom_m A = dom_m x2a\<close> for x2a
    by (simp add: distinct_mset_dom distinct_set_mset_eq_iff)
  define I where
    [simp]: \<open>I = (\<lambda>dom (b, \<V>', A'). \<not>is_failed b \<longrightarrow>
      (set_mset (dom_m A') =  set_mset (dom_m A) - dom \<and>
       (\<forall>i \<in> set_mset (dom_m A) - dom. the (fmlookup A i) - the (fmlookup A' i) \<in> ideal polynomial_bool) \<and>
       \<Union>(vars ` set_mset (ran_m (fmrestrict_set (set_mset (dom_m A')) A))) \<subseteq> \<V>' \<and>
       \<Union>(vars ` set_mset (ran_m A')) \<subseteq> \<V>') \<and>
       \<V> \<union> vars spec0 \<subseteq> \<V>' \<and>
    (b = FOUND \<longrightarrow> spec \<in># ran_m A'))\<close>
  show ?thesis
    unfolding remap_polys_with_err_def remap_polys_polynomial_bool_def conc_fun_RES
    apply (rewrite at \<open>_ \<le> \<hole>\<close> RES_SPEC_eq)
    apply (refine_vcg FOREACHc_rule[where I = I])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal for x xa xb it \<sigma> a b aa ba xc xd xe xf
      supply[[goals_limit=1]]
      by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
    subgoal
      supply[[goals_limit=1]]
      by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq)
    subgoal
      by (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq
        fmlookup_restrict_set_id')
    subgoal for x xa xb it \<sigma> a b
      by (cases a)
        (auto simp add: ran_m_mapsto_upd_notin dom_m_fmrestrict_set' subset_eq
        fmlookup_restrict_set_id')
    done
qed

definition (in -) remap_polys_l_with_err_pre
  :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> bool\<close>
where
  \<open>remap_polys_l_with_err_pre spec spec0 \<V> A \<longleftrightarrow> vars_llist spec \<subseteq> vars_llist spec0\<close>

definition (in -) remap_polys_l_with_err :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow>
   (_ code_status \<times> string set \<times> (nat, llist_polynomial) fmap) nres\<close> where
  \<open>remap_polys_l_with_err spec spec0 = (\<lambda>\<V> A. do{
   ASSERT(remap_polys_l_with_err_pre spec spec0 \<V> A);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   \<V> \<leftarrow> RETURN(\<V> \<union> vars_llist spec0);
   failed \<leftarrow> SPEC(\<lambda>_::bool. True);
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      RETURN (error_msg (0 :: nat) c, \<V>, fmempty)
   }
   else do {
     (err, \<V>, A) \<leftarrow> FOREACH\<^sub>C dom (\<lambda>(err, \<V>,  A'). \<not>is_cfailed err)
       (\<lambda>i (err, \<V>,  A').
          if i \<in># dom_m A
          then  do {
            err' \<leftarrow> SPEC(\<lambda>err. err \<noteq> CFOUND);
            if is_cfailed err' then RETURN((err', \<V>, A'))
            else do {
              p \<leftarrow> full_normalize_poly (the (fmlookup A i));
              eq  \<leftarrow> weak_equality_l p spec;
              \<V> \<leftarrow> RETURN(\<V> \<union> vars_llist (the (fmlookup A i)));
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A)
  }})\<close>

lemma sorted_poly_rel_extend_vars:
  \<open>(A, B) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
  (x1c, x1a) \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
   RETURN (x1c \<union> vars_llist A)
    \<le> \<Down> (\<langle>var_rel\<rangle>set_rel)
       (SPEC ((\<subseteq>) (x1a \<union> vars (B))))\<close>
  using sorted_poly_rel_vars_llist[of A B]
  apply (subst RETURN_RES_refine_iff)
  apply clarsimp
  apply (rule exI[of _ \<open>x1a \<union> \<phi> ` vars_llist A\<close>])
  apply (auto simp: set_rel_def var_rel_def br_def
    dest: fully_unsorted_poly_rel_vars_subset_vars_llist)
  done

lemma remap_polys_l_remap_polys:
  assumes
    AB: \<open>(A, B) \<in> \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close> and
    spec: \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    V: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close> and
    \<open>(spec0, spec0') \<in>  fully_unsorted_poly_rel O mset_poly_rel\<close>
    \<open>remap_polys_l_with_err_pre spec spec0 \<V> A\<close>
  shows \<open>remap_polys_l_with_err spec spec0 \<V> A \<le>
     \<Down>(code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (remap_polys_with_err spec' spec0' \<V>' B)\<close>
  (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by auto
  have H: \<open>x \<in># dom_m A \<Longrightarrow>
     (\<And>p. (the (fmlookup A x), p) \<in> fully_unsorted_poly_rel \<Longrightarrow>
       (p, the (fmlookup B x)) \<in> mset_poly_rel \<Longrightarrow> thesis) \<Longrightarrow>
     thesis\<close> for x thesis
     using fmap_rel_nat_the_fmlookup[OF AB, of x x] fmap_rel_nat_rel_dom_m[OF AB] by auto
  have full_normalize_poly: \<open>full_normalize_poly (the (fmlookup A x))
       \<le> \<Down> (sorted_poly_rel O mset_poly_rel)
          (SPEC
            (\<lambda>p. the (fmlookup B x') - p \<in> More_Modules.ideal polynomial_bool \<and>
                 vars p \<subseteq> vars (the (fmlookup B x'))))\<close>
      if x_dom: \<open>x \<in># dom_m A\<close> and \<open>(x, x') \<in> Id\<close> for x x'
      apply (rule H[OF x_dom])
      subgoal for p
      apply (rule full_normalize_poly_normalize_poly_p[THEN order_trans])
      apply assumption
      subgoal
        using that(2) apply -
        unfolding conc_fun_chain[symmetric]
        by (rule ref_two_step', rule RES_refine)
         (auto simp: rtranclp_normalize_poly_p_poly_of_mset
          mset_poly_rel_def ideal.span_zero)
      done
      done

  have H': \<open>(p, pa) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
    weak_equality_l p spec \<le> \<Down>{(b,enn). b = (enn=FOUND)}
    (SPEC (\<lambda>eqa. eqa \<noteq> FAILED \<and> (eqa = FOUND \<longrightarrow> pa = spec')))\<close> for p pa
    using spec by (auto simp: weak_equality_l_def weak_equality_spec_def RETURN_def
        list_mset_rel_def br_def mset_poly_rel_def intro!: RES_refine
      dest: list_rel_term_poly_list_rel_same_rightD sorted_poly_list_relD)
  have [refine]: \<open>SPEC (\<lambda>err. err \<noteq> CFOUND) \<le> \<Down>code_status_status_rel (RES {FAILED, SUCCESS})\<close>
    by (auto simp: code_status_status_rel_def intro!: RES_refine)
       (case_tac s, auto)
  have [intro!]: \<open>\<exists>a. (aa, a) \<in> \<langle>var_rel\<rangle>set_rel\<close> for aa
    by (auto simp: set_rel_def var_rel_def br_def)

  have emp: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
    ((CSUCCESS, \<V>, fmempty), SUCCESS, \<V>', fmempty) \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> for \<V> \<V>'
    by auto
  show ?thesis
    using assms
    unfolding remap_polys_l_with_err_def remap_polys_l_dom_err_def
      remap_polys_with_err_def prod.case
    apply (refine_rcg full_normalize_poly fmap_rel_fmupd_fmap_rel)
    subgoal
      by auto
    apply (rule fully_unsorted_poly_rel_extend_vars)
    subgoal
      using assms by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: error_msg_def)
    apply (rule 1)
    subgoal by auto
    apply (rule emp)
    subgoal
      using V by auto
    subgoal by (auto simp: code_status_status_rel_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: code_status_status_rel_def RETURN_def intro!: RES_refine)
    subgoal by auto
    apply (rule H')
    subgoal by auto
    apply (rule fully_unsorted_poly_rel_extend_vars)
    subgoal by (auto intro!: fmap_rel_nat_the_fmlookup)
    subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel)
    subgoal for dom doma failed faileda x it \<sigma> x' it' \<sigma>' x1 x2 x1a x2a x1b x2b x1c x2c p pa err' err _ _ eqa eqaa \<V>'' \<V>'''
      by (cases eqaa)
       (auto intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by (auto simp: code_status_status_rel_def is_cfailed_def)
    subgoal by (auto simp: code_status_status_rel_def)
    done
qed

end



export_code add_poly_l' in SML module_name test

definition PAC_checker_l where
  \<open>PAC_checker_l spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
  (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
  (\<lambda>((bA), n). do {
  ASSERT(n \<noteq> []);
  S \<leftarrow> PAC_checker_l_step spec bA (hd n);
  RETURN (S, tl n)
  })
  ((b, A), st);
  RETURN S
  }\<close>




definition full_checker_l2
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l2 spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    err \<leftarrow> SPEC(\<lambda>xs. xs \<noteq> CFOUND);
    (b, \<V>, A) \<leftarrow> remap_polys_l_with_err spec' spec {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>

lemma (in -) keys_mult_monomial2:
  \<open>keys (monomial (n::int) (k::'a \<Rightarrow>\<^sub>0 nat) * a) = (if n = 0 then {} else ((+) k) ` keys (a))\<close>
proof -
  have [simp]: \<open>(\<Sum>aa. (if k = aa then n else 0) *
               (\<Sum>q. lookup (a) q when k + xa = aa + q)) =
        (\<Sum>aa. (if k = aa then n * (\<Sum>q. lookup (a) q when k + xa = aa + q) else 0))\<close>
      for xa
      by (smt Sum_any.cong mult_not_zero)

  show ?thesis
    apply (auto simp: vars_def times_mpoly.rep_eq Const.rep_eq times_poly_mapping.rep_eq
      Const\<^sub>0_def elim!: in_keys_timesE split: if_splits)
    apply (auto simp: lookup_monomial_If prod_fun_def
      keys_def times_poly_mapping.rep_eq)
    done
qed

lemma keys_Const\<^sub>0_mult_left:
  \<open>keys (Const\<^sub>0 (b::int) * aa) = (if b = 0 then {} else keys aa)\<close> for aa :: \<open>('a :: {cancel_semigroup_add,monoid_add} \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _\<close>
  by (auto elim!: in_keys_timesE simp: keys_mult_monomial keys_single Const\<^sub>0_def keys_mult_monomial2)

hide_fact (open) poly_embed.PAC_checker_l_PAC_checker
context poly_embed
begin

definition fmap_polys_rel2 where
  \<open>fmap_polys_rel2 err \<V> \<equiv> {(xs, ys). (xs, ys) \<in> fmap_polys_rel \<and> (\<not> is_cfailed err \<longrightarrow> (\<forall>i\<in>#dom_m xs. vars_llist (the (fmlookup xs i)) \<subseteq> \<V>))}\<close>

lemma check_del_l_check_del:
  \<open>(A, B) \<in> fmap_polys_rel \<Longrightarrow> (x3, x3a) \<in> Id \<Longrightarrow> check_del_l spec A (pac_src1 (Del x3))
  \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and> (b \<longrightarrow> st = CSUCCESS)} (check_del B (pac_src1 (Del x3a)))\<close>
  unfolding check_del_l_def check_del_def
  by (refine_vcg lhs_step_If RETURN_SPEC_refine)
    (auto simp: fmap_rel_nat_rel_dom_m bind_RES_RETURN_eq)


lemma check_extension_alt_def:
  \<open>check_extension_precalc A \<V> i v p \<ge> do {
    b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> i \<notin># dom_m A \<and> v \<notin> \<V>);
    if \<not>b
    then RETURN (False)
    else do {
         p' \<leftarrow> RETURN (p);
         b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> vars p' \<subseteq> \<V>);
         if \<not>b
         then RETURN (False)
         else do {
           pq \<leftarrow> mult_poly_spec p' p';
           let p' = - p';
           p \<leftarrow> add_poly_spec pq p';
           eq \<leftarrow> weak_equality p 0;
           if eq then RETURN(True)
           else RETURN (False)
       }
     }
   }\<close>
proof -
  have [intro]: \<open>ab \<notin> \<V> \<Longrightarrow>
       vars ba \<subseteq> \<V> \<Longrightarrow>
       MPoly_Type.coeff (ba + Var ab) (monomial (Suc 0) ab) = 1\<close> for ab ba
    by (subst coeff_add[symmetric], subst not_in_vars_coeff0)
      (auto simp flip: coeff_add monom.abs_eq
        simp: not_in_vars_coeff0 MPoly_Type.coeff_def
          Var.abs_eq Var\<^sub>0_def lookup_single_eq monom.rep_eq)
  have [simp]: \<open>MPoly_Type.coeff p (monomial (Suc 0) ab) = -1\<close>
     if \<open>vars (p + Var ab) \<subseteq> \<V>\<close>
       \<open>ab \<notin> \<V>\<close>
     for ab
   proof -
     define q where \<open>q \<equiv> p + Var ab\<close>
     then have p: \<open>p = q - Var ab\<close>
       by auto
     show ?thesis
       unfolding p
       apply (subst coeff_minus[symmetric], subst not_in_vars_coeff0)
       using that unfolding q_def[symmetric]
       by (auto simp flip: coeff_minus simp: not_in_vars_coeff0
           Var.abs_eq Var\<^sub>0_def simp flip: monom.abs_eq
           simp: not_in_vars_coeff0 MPoly_Type.coeff_def
           Var.abs_eq Var\<^sub>0_def lookup_single_eq monom.rep_eq)
  qed
  have [simp]: \<open>vars (p - Var ab) = vars (Var ab - p)\<close> for ab
    using vars_uminus[of \<open>p - Var ab\<close>]
    by simp
  show ?thesis
    unfolding check_extension_def
    apply (auto 5 5 simp: check_extension_precalc_def weak_equality_def
      mult_poly_spec_def field_simps
      add_poly_spec_def power2_eq_square cong: if_cong
      intro!: intro_spec_refine[where R=Id, simplified]
      split: option.splits dest: ideal.span_add)
   done
qed

lemma check_extension_l2_check_extension:
  assumes \<open>(A, B) \<in> fmap_polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(i, i') \<in> nat_rel\<close> \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close> \<open>(x, x') \<in> var_rel\<close>
  shows
    \<open>check_extension_l2 spec A \<V> i x r \<le>
      \<Down>{((st), (b)).
        (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
    (is_cfound st \<longrightarrow> spec = r) \<and>
    (b \<longrightarrow> vars_llist r \<subseteq> \<V> \<and> x \<notin> \<V>)} (check_extension_precalc B \<V>' i' x' r')\<close>
proof -
  have \<open>x' = \<phi> x\<close>
    using assms(5) by (auto simp: var_rel_def br_def)


  have [simp]: \<open>(l, l') \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
       (map (\<lambda>(a, b). (a, - b)) l, map (\<lambda>(a, b). (a, - b)) l')
       \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> for l l'
     by (induction l l'  rule: list_rel_induct)
        (auto simp: list_mset_rel_def br_def)

  have [intro!]:
    \<open>(x2c, za) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<Longrightarrow>
     (map (\<lambda>(a, b). (a, - b)) x2c,
        {#case x of (a, b) \<Rightarrow> (a, - b). x \<in># za#})
       \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel\<close> for x2c za
     apply (auto)
     subgoal for y
       apply (induction x2c y  rule: list_rel_induct)
       apply (auto simp: list_mset_rel_def br_def)
       apply (rule_tac b = \<open>(aa, - ba) # map (\<lambda>(a, b). (a, - b)) l'\<close> in relcompI)
       by auto
     done
  have [simp]: \<open>(\<lambda>x. fst (case x of (a, b) \<Rightarrow> (a, - b))) = fst\<close>
    by (auto intro: ext)

  have uminus: \<open>(x2c, x2a) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
       (map (\<lambda>(a, b). (a, - b)) x2c,
        - x2a)
       \<in> sorted_poly_rel O mset_poly_rel\<close> for x2c x2a x1c x1a
     apply (clarsimp simp: sorted_poly_list_rel_wrt_def
      mset_poly_rel_def)
    apply (rule_tac b = \<open>(\<lambda>(a, b). (a, - b)) `# za\<close> in relcompI)
    by (auto simp: sorted_poly_list_rel_wrt_def
      mset_poly_rel_def comp_def polynomial_of_mset_uminus)
   have [simp]: \<open>([], 0) \<in> sorted_poly_rel O mset_poly_rel\<close>
     by (auto simp: sorted_poly_list_rel_wrt_def
      mset_poly_rel_def list_mset_rel_def br_def
       intro!: relcompI[of _ \<open>{#}\<close>])
   have [simp]: \<open>vars_llist (map (\<lambda>(a, b). (a, - b)) xs) = vars_llist xs\<close> for xs
     by (auto simp: vars_llist_def)

   show ?thesis
     unfolding check_extension_l2_def
       check_extension_l_dom_err_def
       check_extension_l_no_new_var_err_def
       check_extension_l_new_var_multiple_err_def
       check_extension_l_side_cond_err_def
      apply (rule order_trans)
      defer
      apply (rule ref_two_step')
      apply (rule check_extension_alt_def)
      apply (refine_vcg add_poly_full_spec3 mult_poly_full_mult_poly_spec)
      subgoal using assms(1,3,4,5)
        by (auto simp: var_rel_set_rel_iff)
      subgoal using assms(1,3,4,5)
        by (auto simp: var_rel_set_rel_iff)
      subgoal by auto
      subgoal by auto
      apply (rule assms)
      subgoal using sorted_poly_rel_vars_llist[of \<open>r\<close> \<open>r'\<close>] assms
        by (force simp: set_rel_def var_rel_def br_def
          dest!: sorted_poly_rel_vars_llist)
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply (rule uminus)
      subgoal using assms by auto
      subgoal by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by (auto simp: in_set_conv_decomp_first[of _ r] remove1_append)
      subgoal using assms by auto
      done
qed

lemma PAC_checker_l_step_PAC_checker_step:
  assumes
    \<open>(Ast, Bst) \<in>{((err, \<V>, A), (err', \<V>', A')). ((err, \<V>, A), (err', \<V>', A')) \<in> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)}\<close> and
    \<open>(st, st') \<in> epac_step_rel\<close> and
    spec: \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    fail: \<open>\<not>is_cfailed (fst Ast)\<close>
  shows
    \<open>PAC_checker_l_step spec Ast st \<le>
    \<Down>{((err, \<V>, A), (err', \<V>', A')). ((err, \<V>, A), (err', \<V>', A')) \<in> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)}
      (PAC_checker_step spec' Bst st')\<close>
proof -
  obtain A \<V> cst B \<V>' cst' where
   Ast: \<open>Ast = (cst, \<V>, A)\<close> and
   Bst: \<open>Bst = (cst', \<V>', B)\<close> and
   \<V>[intro]: \<open>(\<V>, \<V>') \<in>  \<langle>var_rel\<rangle>set_rel\<close>  and
   AB: \<open>(A, B) \<in> fmap_polys_rel\<close>
     \<open>(cst, cst') \<in> code_status_status_rel\<close>
    using assms(1) unfolding fmap_polys_rel2_def
    by (cases Ast; cases Bst; auto)
  have [intro]: \<open>xc \<in> \<V> \<Longrightarrow> \<phi> xc \<in> \<V>'\<close> for xc
    using  \<V> by (auto simp: set_rel_def var_rel_def br_def)
  have \<V>': \<open>\<V>' = \<phi> ` \<V>\<close>
    using \<V>
      by (auto simp: set_rel_def var_rel_def br_def)
  have [refine]: \<open>(r, ra) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
       (eqa, eqaa)
       \<in> {(st, b). (\<not> is_cfailed st \<longleftrightarrow> b) \<and> (is_cfound st \<longrightarrow> spec = r) \<and> (b \<longrightarrow> vars_llist r \<subseteq> \<V> \<and> new_id step \<notin># dom_m A)} \<Longrightarrow>
       RETURN eqa
       \<le> \<Down> code_status_status_rel
          (SPEC
            (\<lambda>st'. (\<not> is_failed st' \<and>
                   is_found st' \<longrightarrow>
                    ra - spec' \<in> More_Modules.ideal polynomial_bool)))\<close>
     for r ra eqa eqaa step
     using spec
     by (cases eqa)
       (auto intro!: RETURN_RES_refine dest!: sorted_poly_list_relD
         simp: mset_poly_rel_def ideal.span_zero)
  have [simp]: \<open>(eqa, st'a) \<in> code_status_status_rel \<Longrightarrow>
       (merge_cstatus cst eqa, merge_status cst' st'a)
       \<in> code_status_status_rel\<close> for eqa st'a
     using AB
     by (cases eqa; cases st'a)
       (auto simp: code_status_status_rel_def)
  have [simp]: \<open>(merge_cstatus cst CSUCCESS, cst') \<in> code_status_status_rel\<close>
    using AB
    by (cases st)
      (auto simp: code_status_status_rel_def)
  have [simp]: \<open>(x32, x32a) \<in> var_rel \<Longrightarrow>
        ([([x32], -1::int)], -Var x32a) \<in> fully_unsorted_poly_rel O mset_poly_rel\<close> for x32 x32a
   by (auto simp: mset_poly_rel_def fully_unsorted_poly_list_rel_def list_mset_rel_def br_def
         unsorted_term_poly_list_rel_def var_rel_def Const_1_eq_1
       intro!: relcompI[of _ \<open>{#({#x32#}, -1 :: int)#}\<close>]
         relcompI[of _ \<open>[({#x32#}, -1)]\<close>])
  have H3: \<open>p - Var a = (-Var a) + p\<close> for p :: \<open>int mpoly\<close> and a
    by auto
  have [iff]: \<open>x3a \<in># remove1_mset x3a (dom_m B) \<longleftrightarrow> False\<close> for x3a B
    using distinct_mset_dom[of B]
    by (cases \<open>x3a \<in># dom_m B\<close>) (auto dest!: multi_member_split)
  show ?thesis
    using assms(2)
    unfolding PAC_checker_l_step_def PAC_checker_step_def Ast Bst prod.case
    apply (cases st; cases st'; simp only: p2rel_def pac_step.case
      pac_step_rel_raw_def mem_Collect_eq prod.case pac_step_rel_raw.simps)
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec check_linear_combi_l_check_linear_comb
        full_normalize_poly_diff_ideal)
      subgoal using fail unfolding Ast by auto
      subgoal using assms(1) fail \<V>'
        unfolding PAC_checker_l_step_inv_def by (auto simp: fmap_polys_rel2_def Ast Bst
          dest!: multi_member_split)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal using AB unfolding PAC_checker_step_inv_def fmap_rel_alt_def PAC_checker_l_step_inv_def
        by (auto simp: all_conj_distrib dest!: multi_member_split sorted_poly_rel_vars_llist2)
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        using AB
        by (auto intro!: fmap_rel_fmupd_fmap_rel fmap_rel_fmdrop_fmap_rel AB simp: fmap_polys_rel2_def PAC_checker_l_step_inv_def subset_iff)
      subgoal using AB
        by (auto intro!: fmap_rel_fmupd_fmap_rel fmap_rel_fmdrop_fmap_rel AB simp: fmap_polys_rel2_def PAC_checker_l_step_inv_def subset_iff)
      done
    subgoal
      apply (refine_rcg full_normalize_poly_diff_ideal add_poly_l_single_new_var
        check_extension_l2_check_extension)
      subgoal using fail unfolding Ast by auto
      subgoal using assms(1) fail \<V>'
        unfolding PAC_checker_l_step_inv_def by (auto simp: fmap_polys_rel2_def Ast Bst
        dest!: multi_member_split)
      subgoal using AB by (auto intro!: fully_unsorted_poly_rel_diff[of _ \<open>-Var _ :: int mpoly\<close>, unfolded H3[symmetric]] simp: comp_def case_prod_beta)
      subgoal using AB by (auto intro!: fully_unsorted_poly_rel_diff[of _ \<open>-Var _ :: int mpoly\<close>, unfolded H3[symmetric]] simp: comp_def case_prod_beta)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by simp
      subgoal by simp
      subgoal by simp
      subgoal using AB \<V>
        by (auto simp: fmap_polys_rel2_def PAC_checker_l_step_inv_def
          intro!: fmap_rel_fmupd_fmap_rel insert_var_rel_set_rel dest!: in_diffD)
      subgoal
        by (auto simp: code_status_status_rel_def AB fmap_polys_rel2_def
          code_status.is_cfailed_def)
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_del_l_check_del check_addition_l_check_add
        full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]])
      subgoal using fail unfolding Ast by auto
      subgoal using assms(1) fail \<V>'
        unfolding PAC_checker_l_step_inv_def by (auto simp: fmap_polys_rel2_def Ast Bst
        dest!: multi_member_split)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal using AB
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel code_status_status_rel_def
          simp: fmap_polys_rel2_def PAC_checker_l_step_inv_def
          dest: in_diffD)
      subgoal
        using AB
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel simp: fmap_polys_rel2_def)
      done
    done
qed


lemma PAC_checker_l_PAC_checker:
  assumes
    \<open>(A, B) \<in>{((\<V>, A), (\<V>', A')). ((\<V>, A), (\<V>', A')) \<in> (\<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 b \<V>)}\<close>
    (is \<open>_ \<in> ?A\<close>) and
    \<open>(st, st') \<in> \<langle>epac_step_rel\<rangle>list_rel\<close> and
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(b, b') \<in> code_status_status_rel\<close>
  shows
    \<open>PAC_checker_l spec A b st \<le>
      \<Down> {((err, \<V>, A), (err', \<V>', A')). ((err, \<V>, A), (err', \<V>', A')) \<in> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)} (PAC_checker spec' B b' st')\<close>
proof -
  have [refine0]: \<open>(((b, A), st), (b', B), st') \<in>
    ({((err, \<V>, A), (err', \<V>', A')). ((err, \<V>, A), (err', \<V>', A')) \<in> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)} \<times>\<^sub>r
     \<langle>epac_step_rel\<rangle>list_rel)\<close>
    using assms by (auto simp: code_status_status_rel_def)
  show ?thesis
    using assms
    unfolding PAC_checker_l_def PAC_checker_def
    apply (refine_rcg PAC_checker_l_step_PAC_checker_step)
    subgoal by (auto simp: code_status_status_rel_discrim_iff
       WHILEIT_refine[where R = \<open>(?A \<times>\<^sub>r \<langle>pac_step_rel\<rangle>list_rel)\<close>])
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv intro!: param_nth)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv fmap_polys_rel2_def)
    subgoal by (auto simp: neq_Nil_conv fmap_polys_rel2_def)
    done
qed

lemma sorted_poly_rel_extend_vars2:
  \<open>(A, B) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
  (x1c, x1a) \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
   RETURN (x1c \<union> vars_llist A)
    \<le> \<Down> {(a,b). (a,b) \<in> \<langle>var_rel\<rangle>set_rel \<and> a = x1c \<union> vars_llist A}
       (SPEC ((\<subseteq>) (x1a \<union> vars (B))))\<close>
  using sorted_poly_rel_vars_llist[of A B]
  apply (subst RETURN_RES_refine_iff)
  apply clarsimp
  apply (rule exI[of _ \<open>x1a \<union> \<phi> ` vars_llist A\<close>])
  apply (auto simp: set_rel_def var_rel_def br_def
    dest: fully_unsorted_poly_rel_vars_subset_vars_llist)
  done

lemma fully_unsorted_poly_rel_extend_vars2:
  \<open>(A, B) \<in> fully_unsorted_poly_rel O mset_poly_rel \<Longrightarrow>
  (x1c, x1a) \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
   RETURN (x1c \<union> vars_llist A)
    \<le> \<Down> {(a,b). (a,b) \<in> \<langle>var_rel\<rangle>set_rel \<and> a = x1c \<union> vars_llist A}
       (SPEC ((\<subseteq>) (x1a \<union> vars (B))))\<close>
  using fully_unsorted_poly_rel_vars_subset_vars_llist[of A B]
  apply (subst RETURN_RES_refine_iff)
  apply clarsimp
  apply (rule exI[of _ \<open>x1a \<union> \<phi> ` vars_llist A\<close>])
  apply (auto simp: set_rel_def var_rel_def br_def
    dest: fully_unsorted_poly_rel_vars_subset_vars_llist)
  done


lemma remap_polys_l_with_err_remap_polys_with_err:
  assumes
    AB: \<open>(A, B) \<in> \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close> and
    spec: \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    V: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close> and
    spec0: \<open>(spec0, spec0') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close> and
    pre: \<open>remap_polys_l_with_err_pre spec spec0 \<V> A\<close>
  shows \<open>remap_polys_l_with_err spec spec0 \<V> A \<le>
    \<Down>{((err, \<V>, A), (err', \<V>', A')). ((err, \<V>, A), (err', \<V>', A')) \<in> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)}
      (remap_polys_with_err spec' spec0' \<V>' B)\<close>
  (is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by auto
  have H: \<open>x \<in># dom_m A \<Longrightarrow>
     (\<And>p. (the (fmlookup A x), p) \<in> fully_unsorted_poly_rel \<Longrightarrow>
       (p, the (fmlookup B x)) \<in> mset_poly_rel \<Longrightarrow> thesis) \<Longrightarrow>
     thesis\<close> for x thesis
     using fmap_rel_nat_the_fmlookup[OF AB, of x x] fmap_rel_nat_rel_dom_m[OF AB] by auto

  have full_normalize_poly: \<open>full_normalize_poly (the (fmlookup A x))
       \<le> \<Down>  {(xs, ys). (xs, ys) \<in> sorted_poly_rel O mset_poly_rel \<and> vars_llist xs \<subseteq> vars_llist (the (fmlookup A x))}
          (SPEC
            (\<lambda>p. the (fmlookup B x') - p \<in> More_Modules.ideal polynomial_bool \<and>
                 vars p \<subseteq> vars (the (fmlookup B x'))))\<close> (is \<open>_ \<le> \<Down>?A _\<close>)
      if x_dom: \<open>x \<in># dom_m A\<close> and \<open>(x, x') \<in> Id\<close> for x x'
      apply (rule H[OF x_dom])
      subgoal for p
      apply (rule full_normalize_poly_normalize_poly_p2[THEN order_trans])
      apply assumption
      subgoal
        using that(2) apply -
        unfolding conc_fun_chain[symmetric]
        by
         (auto simp: rtranclp_normalize_poly_p_poly_of_mset conc_fun_RES
            mset_poly_rel_def ideal.span_zero
            intro!: exI[of _ \<open>polynomial_of_mset _\<close>])
      done
      done

  have H': \<open>(p, pa) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
    weak_equality_l p spec \<le> \<Down>{(b,enn). b = (enn=FOUND)}
    (SPEC (\<lambda>eqa. eqa \<noteq> FAILED \<and> (eqa = FOUND \<longrightarrow> pa = spec')))\<close> for p pa
    using spec by (auto simp: weak_equality_l_def weak_equality_spec_def RETURN_def
        list_mset_rel_def br_def mset_poly_rel_def intro!: RES_refine
      dest: list_rel_term_poly_list_rel_same_rightD sorted_poly_list_relD)
  have [refine]: \<open>SPEC (\<lambda>err. err \<noteq> CFOUND) \<le> \<Down>code_status_status_rel (RES {FAILED, SUCCESS})\<close>
    by (auto simp: code_status_status_rel_def intro!: RES_refine)
       (case_tac s, auto)
  have [intro!]: \<open>\<exists>a. (aa, a) \<in> \<langle>var_rel\<rangle>set_rel\<close> for aa
    by (auto simp: set_rel_def var_rel_def br_def)

  have emp: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
    ((CSUCCESS, \<V>, fmempty), SUCCESS, \<V>', fmempty) \<in>
    {((err, \<V>, A), (f', \<V>', A')). ((err, \<V>, A), (f',  \<V>', A')) \<in>
      (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>)}\<close>
    for \<V> \<V>'
    by (auto simp: fmap_polys_rel2_def)
  have XXX: \<open>(\<V>'', \<V>''') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow> x \<in> \<V>'' \<Longrightarrow> \<phi> x \<in> \<V>'''\<close> for x \<V>'' \<V>'''
    by (auto simp: br_def set_rel_def var_rel_def)

  show ?thesis
    using assms
    unfolding remap_polys_l_with_err_def remap_polys_l_dom_err_def
      remap_polys_with_err_def prod.case term_rel_def[symmetric]
    apply (refine_rcg full_normalize_poly fmap_rel_fmupd_fmap_rel)

    subgoal
      by auto
    apply (rule fully_unsorted_poly_rel_extend_vars2[unfolded term_rel_def[symmetric]])
    subgoal using spec0 by auto
    subgoal by auto
    subgoal by auto
    subgoal
      by (auto simp: error_msg_def fmap_polys_rel2_def)
    apply (rule 1)
    subgoal by auto
    apply (rule emp)
    subgoal
      using V by auto
    subgoal by (auto simp: code_status_status_rel_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: code_status_status_rel_def RETURN_def fmap_polys_rel2_def intro!: RES_refine)
    subgoal by auto
    apply (rule H')
    subgoal by auto
    apply (rule fully_unsorted_poly_rel_extend_vars2[unfolded term_rel_def[symmetric]])
    subgoal by (auto intro!: fmap_rel_nat_the_fmlookup)
    subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel)
    subgoal for dom doma failed faileda x it \<sigma> x' it' \<sigma>' x1 x2 x1a x2a x1b x2b x1c x2c p pa err' err _ _ eqa eqaa \<V>'' \<V>'''
      unfolding term_rel_def[symmetric]
      by (cases eqaa)
       (auto simp: fmap_rel_fmupd_fmap_rel[where R = \<open>sorted_poly_rel O mset_poly_rel\<close>, unfolded term_rel_def[symmetric]]
        simp: fmap_polys_rel2_def code_status_status_rel_def term_rel_def[symmetric]
        dest: in_diffD) (*very slow*)
    subgoal by (auto simp: code_status_status_rel_def is_cfailed_def)
    subgoal by (auto simp: code_status_status_rel_def)
    done
qed


definition full_checker_l
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A) \<leftarrow> remap_polys_l_with_err spec' spec {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      let \<V> = \<V>;
      PAC_checker_l spec' (\<V>, A) b st
     }
   }\<close>

lemma (in -)RES_RES_RETURN_RES3: \<open>RES A \<bind> (\<lambda>(a,b,c). RES (f a b c)) = RES (\<Union>((\<lambda>(a,b,c). f a b c) ` A))\<close> for A f
  by (auto simp: pw_eq_iff refine_pw_simps)

definition vars_rel2 :: \<open>_\<close> where
  \<open>vars_rel2 err = {(A,B). \<not>is_cfailed err \<longrightarrow> (A,B)\<in> \<langle>var_rel\<rangle>set_rel} \<close>

lemma full_checker_l_full_checker:
 assumes
    \<open>(A, B) \<in> unsorted_fmap_polys_rel\<close> and
    st: \<open>(st, st') \<in> \<langle>epac_step_rel\<rangle>list_rel\<close> and
    spec: \<open>(spec, spec') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>full_checker_l spec A st \<le> \<Down> {((err, \<V>, A), err', \<V>', A').
          ((err, \<V>, A), err', \<V>', A') \<in> code_status_status_rel \<times>\<^sub>r vars_rel2 err \<times>\<^sub>r fmap_polys_rel2 err \<V>} (full_checker spec' B st')\<close>
proof -
  (* have 0[simp]: \<open>\<Phi> \<noteq> {} \<Longrightarrow> do {(a,b) \<leftarrow> RES \<Phi>; RETURN P} = RETURN P\<close> for \<Phi> P
   *   by (auto simp: pw_eq_iff refine_pw_simps)
   * have H:  \<open>do {spec \<leftarrow> RES A; (a,b,c) \<leftarrow> RES (B spec); f a b c spec} =
   *   do { (spec, a,b,c) \<leftarrow> SPEC(\<lambda>(spec,a,b,c). spec \<in> A \<and> (a,b,c) \<in> B spec); f a b c spec}\<close> for A f g spec B
   *   by (auto simp: pw_eq_iff refine_pw_simps)
   * have 1: \<open>(if is_failed st then RETURN (st, \<V>, A) else do {
   *   \<V> \<leftarrow> SPEC ((\<subseteq>) (\<V> \<union> vars spec0));
   *   PAC_checker spec (\<V>, A) st pac
   *   }) = ( do {
   *   \<V>' \<leftarrow> SPEC ((\<subseteq>) (\<V> \<union> vars spec0));
   *   if is_failed st then RETURN (st, \<V>, A) else PAC_checker spec (\<V>', A) st pac
   *     })\<close>
   *   for \<V> A st pac spec spec0
   *   by (auto simp: bind_RES_RETURN_eq)
   * have 2: \<open>(if is_failed st then RETURN (st, \<V>, A)
   *   else do {
   *   (err, \<V>') \<leftarrow>  SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> \<V> \<union> vars spec0 \<subseteq> \<V>'));
   *   if \<not> is_failed err then PAC_checker spec (\<V>', A) st pac else RETURN (err, \<V>, A)
   *     }) = (do {
   *     (err, \<V>') \<leftarrow>  SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> \<V> \<union> vars spec0 \<subseteq> \<V>'));
   *   if is_failed st then RETURN (st, \<V>, A)
   *     else
   *   if \<not> is_failed err then PAC_checker spec (\<V>', A) st pac else RETURN (err, \<V>, A)
   *     })\<close>
   *
   *   for st \<V> A spec pac spec0
   *   by (auto simp: bind_RES_RETURN_eq bind_RES_RETURN2_eq)
   *
   *
   * have full_checker_alt_def:
   *  \<open>full_checker spec0 A pac = do {
   *    spec \<leftarrow> normalize_poly_spec spec0;
   *    (st, \<V>, A) \<leftarrow> remap_polys_change_all spec {} A;
   *    if is_failed st then
   *    RETURN (st, \<V>, A)
   *    else do {
   *      (err, \<V>') \<leftarrow> SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> \<V> \<union> vars spec0 \<subseteq> \<V>'));
   *    if \<not>is_failed err then PAC_checker spec (\<V>', A) st pac
   *      else RETURN (err, \<V>, A)
   *   }
   *      }\<close>  (is \<open>?A = ?B\<close>) for spec0 A pac
   *  proof -
   *    have [refine]: \<open>(spec, speca) \<in> Id \<Longrightarrow> remap_polys_change_all spec {} A \<le> \<Down> Id (remap_polys_change_all speca {} A)\<close> for spec speca A
   *      by auto
   *    have  1:\<open>(x1c, x1a) \<in> Id \<Longrightarrow> SPEC ((\<subseteq>) (x1c \<union> vars spec0))
   *      \<le> \<Down> {(\<V>, (err, \<V>')). err = SUCCESS \<and> (\<V>,\<V>')\<in>Id}
   *      (SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> x1a \<union> vars spec0 \<subseteq> \<V>')))\<close> for x1c x1a spec0
   *      by (auto simp: conc_fun_RES)
   *
   *    have AB: \<open>?A \<le> \<Down>Id ?B\<close>
   *      unfolding full_checker_def normalize_poly_spec_def
   *      apply (refine_rcg 1)
   *      subgoal by auto
   *      subgoal by auto
   *      subgoal by auto
   *      subgoal by auto
   *      done
   *    define f where
   *      \<open>f spec A (spec0::int mpoly) \<equiv> do {  (st, \<V>, A) \<leftarrow> remap_polys_change_all spec {} A;
   *      (err, \<V>') \<leftarrow> SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> \<V> \<union> vars spec0 \<subseteq> \<V>'));
   *      RETURN (st, \<V>, A, err, \<V>')
   *      }\<close> for spec A \<V> spec0
   *    have B: \<open>?B = do {
   *      spec \<leftarrow> SPEC (\<lambda>r. spec0 - r \<in> More_Modules.ideal polynomial_bool \<and> vars r \<subseteq> vars spec0);
   *      (st, \<V>, A, err, \<V>') \<leftarrow> f spec A spec0;
   *      if is_failed st \<or> is_failed err then RETURN (merge_status err st, \<V>, A)
   *       else do {let \<V>' = \<V>'; PAC_checker spec (\<V>', A) st pac}
   *        } \<close>
   *      unfolding full_checker_def normalize_poly_spec_def 2 f_def
   *      by (auto intro!: bind_cong[OF refl] simp: is_failed_def)
   *
   *    have [simp]: \<open>merge_status SUCCESS a = a\<close> for a
   *      by (cases a) auto
   *    have [simp]: \<open>merge_status a SUCCESS = a\<close> for a
   *      by (cases a) auto
   *    have [refine]: \<open>(spec, speca) \<in> Id \<Longrightarrow>
   *      f spec A spec0 \<le> \<Down>{((st, \<V>, A, err, \<V>''),  (st', \<V>', A')).
   *         ((merge_status st err, \<V>, A), (st', \<V>', A')) \<in> Id \<and>
   *           (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> \<V> \<union> vars spec0 \<subseteq> \<V>'') } (remap_polys_change_all speca {} A)\<close>
   *      for spec A speca spec0
   *      unfolding f_def remap_polys_change_all_def
   *      by (auto simp: bind_RES_RETURN_eq bind_RES_RETURN2_eq RES_RES_RETURN_RES3
   *        intro!:RES_refine lhs_step_If)
   *    have BA: \<open>?B \<le> \<Down>Id ?A\<close>
   *      unfolding B unfolding full_checker_def normalize_poly_spec_def
   *      apply (refine_rcg)
   *      subgoal by auto
   *      subgoal by (auto simp: is_failed_def)
   *      subgoal by auto
   *      subgoal by auto
   *      done
   *    show ?thesis
   *      using AB BA by auto
   *  qed *)
  have aa: \<open>{((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A') \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V> \<and>
    (\<not>is_failed err' \<longrightarrow> vars spec' \<subseteq> \<V>')} =
    {((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A') \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V>} O
    {((err, \<V>, A), err', \<V>', A').  ((err, \<V>, A), err', \<V>', A') \<in> Id \<and> (\<not>is_failed err' \<longrightarrow> vars spec' \<subseteq> \<V>')}\<close> for spec'
    by auto
  have [refine]:
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
    (spec0, spec0') \<in> fully_unsorted_poly_rel O mset_poly_rel \<Longrightarrow>
    (\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>  remap_polys_l_with_err_pre spec spec0 \<V> A \<Longrightarrow>
    remap_polys_l_with_err spec spec0 \<V> A \<le> \<Down> {((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A') \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V> \<and>
     (\<not>is_failed err' \<longrightarrow> vars spec0' \<subseteq> \<V>')}
    (remap_polys_change_all spec' \<V>' B)\<close> for spec spec' \<V> \<V>' spec0 spec0'
    apply (rule remap_polys_l_with_err_remap_polys_with_err[THEN order_trans, OF assms(1)])
    apply assumption+
    apply (subst aa, subst conc_fun_chain[symmetric])
    apply (rule ref_two_step[OF order.refl])
    apply (rule remap_polys_with_err_spec[THEN order_trans])
    apply (rule conc_fun_R_mono[THEN order_trans, of _ \<open>{((err, \<V>, A), err', \<V>', A').
      ((err, \<V>, A), err', \<V>', A') \<in> Id \<and> (\<not> is_failed err' \<longrightarrow> vars spec0' \<subseteq> \<V>')}\<close>])
    apply (solves auto)
    apply (subst ref_two_step')
    apply (rule remap_polys_polynomial_bool_remap_polys_change_all)
    apply (solves \<open>rule TrueI\<close>)
    done

   have unfold_code_status: \<open>(\<exists>(a). P a) \<longleftrightarrow> (\<exists>a. P (CFAILED a)) \<or> P CFOUND \<or> P CSUCCESS\<close> for P
     by (auto, case_tac a, auto)
   have unfold_status: \<open>(\<exists>(a). P a) \<longleftrightarrow> ( P (FAILED)) \<or> P FOUND \<or> P SUCCESS\<close> for P
     by (auto, case_tac a, auto)
   have var_rel_set_rel_alt_def: \<open>(A, B) \<in> \<langle>var_rel\<rangle>set_rel \<longleftrightarrow> B = \<phi> ` A\<close> for A B
     by (auto simp: var_rel_def set_rel_def br_def)
   have [refine]: \<open>(x1c, x1a) \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
      SPEC (\<lambda>(err, \<V>'). (err = CSUCCESS \<or> is_cfailed err) \<and> (err = CSUCCESS \<longrightarrow> \<V>' = x1c \<union> vars_llist spec))
    \<le> \<Down> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel)
     (SPEC (\<lambda>(err, \<V>'). (err = SUCCESS \<or> is_failed err) \<and> (err = SUCCESS \<longrightarrow> x1a \<union> vars spec' \<subseteq> \<V>')))\<close> for x1c x1a
     using fully_unsorted_poly_rel_vars_subset_vars_llist[OF spec]
     by (force simp: code_status_status_rel_def is_failed_def unfold_code_status unfold_status is_cfailed_def
         var_rel_set_rel_alt_def
       intro!: RES_refine
       intro: )
   have [refine]: \<open>(b,b') \<in> {((\<V>, A), \<V>', A'). ((\<V>, A), \<V>', A') \<in> \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 c \<V>} \<Longrightarrow>
     (spec, spec') \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
     (c, c') \<in> code_status_status_rel \<Longrightarrow>
     PAC_checker_l spec b c  st
    \<le> \<Down> {((err, \<V>, A), err', \<V>', A').
      ((err, \<V>, A), err', \<V>', A') \<in> code_status_status_rel \<times>\<^sub>r vars_rel2 err \<times>\<^sub>r fmap_polys_rel2 err \<V>}
     (PAC_checker spec' b' c' st')\<close> for spec b c spec' b' c'
     using assms apply -
     apply (rule order_trans)
     apply (rule ref_two_step[OF PAC_checker_l_PAC_checker])
     apply assumption+
     apply (rule order_refl)
     apply (rule conc_fun_R_mono)
     apply (auto simp: vars_rel2_def)
     done
   have still_in: \<open>(spec'a, spec) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
     (x, x')
     \<in> {((err, \<V>, A), err', \<V>', A').
     ((err, \<V>, A), err', \<V>', A')
     \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel2 err \<V> \<and>
     (\<not> is_failed err' \<longrightarrow> vars spec' \<subseteq> \<V>')} \<Longrightarrow>
     x2 = (x1a, x2a) \<Longrightarrow>
     x' = (x1, x2) \<Longrightarrow>
     x2b = (x1c, x2c) \<Longrightarrow>
     x = (x1b, x2b) \<Longrightarrow>
     \<not> is_cfailed x1b \<Longrightarrow>
     \<not> is_failed x1 \<Longrightarrow>
     RETURN x1c
     \<le> \<Down> (\<langle>var_rel\<rangle>set_rel) (SPEC ((\<subseteq>) (x1a \<union> vars spec')))\<close>
     for spec'a spec x x' x1 x2 x1a x2a x1b x2b x1c x2c
     by (auto intro!: RETURN_RES_refine exI[of _ x1a])

  show ?thesis
    unfolding full_checker_def full_checker_l_def
    apply (refine_rcg remap_polys_l_remap_polys
       full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]] assms)
    subgoal by auto
    subgoal unfolding remap_polys_l_with_err_pre_def by auto
    subgoal by (auto simp: is_cfailed_def is_failed_def)
    subgoal by (auto simp: vars_rel2_def)
    apply (rule still_in; assumption)
    subgoal by auto
    subgoal by (auto simp: fmap_polys_rel2_def vars_rel2_def)
    done
qed

lemma full_checker_l_full_checker':
  \<open>(uncurry2 full_checker_l, uncurry2 full_checker) \<in>
  ((fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r unsorted_fmap_polys_rel) \<times>\<^sub>r \<langle>epac_step_rel\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>{((err, \<V>, A), err', \<V>', A').
    ((err, \<V>, A), err', \<V>', A')
    \<in> code_status_status_rel \<times>\<^sub>r  vars_rel2 err \<times>\<^sub>r {(xs, ys). (xs, ys) \<in> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel \<and>
     (\<not> is_cfailed err \<longrightarrow> (\<forall>i\<in>#dom_m xs. vars_llist (the (fmlookup xs i)) \<subseteq> \<V>))}}\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using full_checker_l_full_checker unfolding fmap_polys_rel2_def by force

end

end
