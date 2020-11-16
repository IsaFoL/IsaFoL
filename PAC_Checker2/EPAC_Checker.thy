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

definition check_linear_combi_l_pre_err :: \<open>nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_pre_err r = SPEC (\<lambda>_. True)\<close>

definition check_linear_combi_l_dom_err :: \<open>llist_polynomial \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_dom_err p r = SPEC (\<lambda>_. True)\<close>

definition check_linear_combi_l_mult_err :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> string nres\<close> where
  \<open>check_linear_combi_l_mult_err pq r = SPEC (\<lambda>_. True)\<close>

definition linear_combi_l where
\<open>linear_combi_l A \<V> xs = do {
    WHILE\<^sub>T
      (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         let (q :: llist_polynomial, i) = hd xs;
         if (i \<notin># dom_m A \<or> \<not>(vars_llist q \<subseteq> \<V>))
         then do {
           err \<leftarrow> check_linear_combi_l_dom_err q i;
           RETURN (p, xs, CFAILED err)
         } else do {
           let r = the (fmlookup A i);
           q \<leftarrow> full_normalize_poly (q);
           pq \<leftarrow> mult_poly_full q r;
           pq \<leftarrow> add_poly_l (p, pq);
           RETURN (pq, tl xs, CSUCCESS)
         }
      })
     ([], xs, CSUCCESS)
  }\<close>

definition check_linear_combi_l where
  \<open>check_linear_combi_l spec A \<V> i xs r =
  (if i \<in># dom_m A \<or> xs = [] \<or> \<not>(vars_llist r \<subseteq> \<V>)
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i;
    RETURN (CFAILED err)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l A \<V> xs;
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
  })\<close>


paragraph \<open>Deletion checking\<close>


paragraph \<open>Extension checking\<close>

paragraph \<open>Step checking\<close>

definition PAC_checker_l_step ::  \<open>_ \<Rightarrow> string code_status \<times> string set \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close> where
  \<open>PAC_checker_l_step = (\<lambda>spec (st', \<V>, A) st. case st of
     CL _ _ _ \<Rightarrow>
       do {
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
        eq \<leftarrow> check_del_l spec A (pac_src1 st);
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq, \<V>, fmdrop (pac_src1 st) A)
        else RETURN (eq, \<V>, A)
   }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (([new_var st], -1) # (pac_res st));
        (eq) \<leftarrow> check_extension_l spec A \<V> (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then do {
          RETURN (st',
            insert (new_var st) \<V>, fmupd (new_id st) r A)}
        else RETURN (eq, \<V>, A)
   }
 )\<close>

lemma pac_step_rel_raw_def:
  \<open>\<langle>K, V, R\<rangle> pac_step_rel_raw = pac_step_rel_raw K V R\<close>
  by (auto intro!: ext simp: relAPP_def)


subsection \<open>Correctness\<close>

text \<open>We now enter the locale to reason about polynomials directly.\<close>

context poly_embed
begin

lemma mult_poly_full_spec:
  assumes
    \<open>(p, p'') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q'') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>mult_poly_full p q \<le> \<Down>(sorted_poly_rel O mset_poly_rel)
    (SPEC (\<lambda>s.  s - p'' * q'' \<in> ideal polynomial_bool))\<close>
proof -
  obtain p' q' where
    pq: \<open>(p, p') \<in> sorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel\<close>
    \<open>(q', q'') \<in> mset_poly_rel\<close>
    using assms by auto
  show ?thesis
    find_theorems mult_poly_full 
    apply (rule mult_poly_full_mult_poly_p'[THEN order_trans, OF pq(1,3)])
    apply (subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    unfolding mult_poly_p'_def
    apply refine_vcg
    by (use pq assms in \<open>auto simp: mult_poly_p'_def mset_poly_rel_def
      dest!: rtranclp_normalize_poly_p_poly_of_mset rtranclp_mult_poly_p_mult_ideal_final
      intro!: RES_refine\<close>)
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

lemma full_normalize_poly_full_spec:
  assumes
    \<open>(p, p'') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>full_normalize_poly p \<le> \<Down>(sorted_poly_rel O mset_poly_rel)
    (SPEC (\<lambda>s.  s - (p'')\<in> ideal polynomial_bool \<and> vars s \<subseteq> vars p''))\<close>
proof -
  obtain p' q' where
    pq: \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
    \<open>(p', p'') \<in> mset_poly_rel\<close>
    using assms by auto
  show ?thesis
    apply (rule full_normalize_poly_normalize_poly_p[THEN order_trans, OF pq(1)])
    apply (subst conc_fun_chain[symmetric])
    apply (rule ref_two_step')
    by (use pq assms in \<open>clarsimp simp: add_poly_p'_def mset_poly_rel_def ideal.span_zero
          ideal.span_zero rtranclp_normalize_poly_p_poly_of_mset
      dest!: rtranclp_add_poly_p_polynomial_of_mset_full
      intro!: RES_refine\<close>)
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

definition term_rel :: \<open>_\<close> where
  \<open>term_rel = sorted_poly_rel O mset_poly_rel\<close>
definition raw_term_rel where
  \<open>raw_term_rel = fully_unsorted_poly_rel O mset_poly_rel\<close>

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
    xs: \<open>(xs, xs') \<in> \<langle>(fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r nat_rel\<rangle>list_rel\<close>
  shows
    \<open>check_linear_combi_l spec A \<V>' i xs r \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
    (is_cfound st \<longrightarrow> spec = r)} (check_linear_comb B \<V> xs' i' r')\<close>
proof -
  have \<V>: \<open>\<V> = \<phi>`\<V>'\<close>
    using assms(4) unfolding set_rel_def var_rel_def
    by (auto simp: br_def)

  define f where
    \<open>f = (\<lambda>ys::((char list list \<times> int) list \<times> nat) list.
        (\<forall>x \<in> set (take (length ys) xs'). snd x \<in># dom_m B \<and> vars (fst x) \<subseteq> \<V>))\<close>
  let ?I = \<open>\<lambda>(p, xs'', err). \<not>is_cfailed err \<longrightarrow> 
    (\<exists>r ys. (p, r) \<in> sorted_poly_rel O mset_poly_rel \<and> f ys \<and>
    (\<Sum>(p,n) \<in># mset (take (length ys) xs'). the (fmlookup B n) * p) - r \<in> ideal polynomial_bool \<and> xs = ys @ xs'' \<and>
    (xs'', drop (length ys) xs') \<in> \<langle>(fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r nat_rel\<rangle>list_rel)\<close>

  have [simp]: \<open>length xs = length xs'\<close>
    using xs by (auto simp: list_rel_imp_same_length)
  (* have f: \<open>f ((xa, bb) # ys) \<Longrightarrow>  (length ys) < length xs' \<Longrightarrow> snd (xs'!(length xs' - Suc (length ys))) \<in># dom_m B \<Longrightarrow>
   *    vars (fst (xs'!(length xs' - Suc (length ys)))) \<subseteq> \<V> \<Longrightarrow> f ys\<close> for xa bb ys
   *   unfolding f_def apply simp_all
   *   apply (intro allI impI)
   *   apply (subgoal_tac \<open>i < length xs' - Suc (length ys) \<or> i = (length xs' - Suc (length ys))\<close>)
   *   apply auto
   *   done *)
  have [simp]: \<open>drop (length ysa) xs' = cs @ (b) # ysb \<Longrightarrow> length ysa < length xs'\<close> for ysa cs b ysb
    by (rule ccontr) auto

have Hf2:
  \<open>(\<Sum>(p, n)\<leftarrow>cs. the (fmlookup B n) * p) - r \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
  xa - ac * the (fmlookup B b) \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
  xc - (r + xa) \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
  (\<Sum>(p, n)\<leftarrow>cs. the (fmlookup B n) * p) + the (fmlookup B b) * ac - xc \<in> More_Modules.ideal polynomial_bool
  \<close>
  for xa ad bb r xc B ac cs b
  sorry
  have H[simp]: \<open>length ys < length xs \<Longrightarrow>
    i < length xs' - length ys \<longleftrightarrow> (i < length xs' - Suc (length ys) \<or> i = length xs' - length ys - 1)\<close> for ys i
    by auto
      find_theorems full_normalize_poly
  have lin: \<open>linear_combi_l A \<V>' xs \<le> \<Down> {((p, xs, err), (b, p')). (\<not>b \<longrightarrow> is_cfailed err) \<and>
        (b \<longrightarrow>(p, p') \<in> sorted_poly_rel O mset_poly_rel)}
    (SPEC(\<lambda>(b, r). b \<longrightarrow> ((\<forall>i \<in> set xs'. snd i \<in># dom_m B \<and> vars (fst i) \<subseteq> \<V>) \<and>
       (\<Sum>(p,n) \<in># mset xs'. the (fmlookup B n) * p) - r \<in> ideal polynomial_bool)))\<close>
    using assms(1) xs
    unfolding linear_combi_l_def conc_fun_RES check_linear_combi_l_dom_err_def term_rel_def[symmetric]
      raw_term_rel_def[symmetric]
    apply (subst (2) RES_SPEC_eq)
    apply (rule WHILET_rule[where R = \<open>measure (\<lambda>(_, xs, p). if is_cfailed p then 0 else Suc (length xs))\<close>
      and I = \<open>?I\<close>])
    subgoal by auto
    subgoal using xs by (auto 5 5 intro!: exI[of _ 0] intro: exI[of _xs] exI[of _ \<open>[]\<close>] ideal.span_zero simp: f_def)
    subgoal for s
      unfolding term_rel_def[symmetric]
      apply (refine_vcg full_normalize_poly_full_spec[THEN order_trans, unfolded term_rel_def[symmetric]
        raw_term_rel_def[symmetric]])
      subgoal
        by clarsimp
      subgoal
        by (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
      subgoal
        by (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply auto
          find_theorems \<open>?P \<Longrightarrow> ?P\<close>
        apply (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply (rule_tac P = \<open>(x, fst (hd (drop (length xs' - length (fst (snd s))) xs'))) \<in> raw_term_rel\<close> in TrueE)
        apply (auto simp: list_rel_imp_same_length)[2]
        apply (clarsimp simp: list_rel_split_right_iff list_rel_append1 neq_Nil_conv list_rel_imp_same_length)
        apply (auto simp: conc_fun_RES)
        apply refine_vcg
      apply (rule mult_poly_full_spec[THEN order_trans, unfolded term_rel_def[symmetric]])
      apply assumption
      apply auto
      unfolding conc_fun_RES
      apply auto
      apply refine_vcg
      apply (rule add_poly_full_spec[THEN order_trans, unfolded term_rel_def[symmetric]])
      apply assumption
      apply (auto simp: )
      apply (subst conc_fun_RES)
      apply clarsimp_all
      apply (auto simp: f_def take_Suc_conv_app_nth list_rel_imp_same_length single_valued_poly)
      apply (rule_tac x=xf in exI)
      apply (auto simp: f_def take_Suc_conv_app_nth list_rel_imp_same_length[symmetric] single_valued_poly)
        apply (auto dest!: sorted_poly_rel_vars_llist[unfolded term_rel_def[symmetric]]
          fully_unsorted_poly_rel_vars_subset_vars_llist[unfolded raw_term_rel_def[symmetric]]
          simp: \<V>)[]
        apply blast
     sorry 
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
    apply simp
    apply (refine_vcg lin[THEN order_trans, unfolded term_rel_def[symmetric]])
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (auto split: if_splits simp: bind_RES_RETURN_eq)
    apply (clarsimp simp add: conc_fun_RES bind_RES_RETURN_eq split: if_splits)
    apply (auto 5 3 split: if_splits simp: bind_RES_RETURN_eq \<V>)
    apply (frule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES)
    apply (drule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES)
    apply (drule single_valuedD[OF single_valued_term[unfolded term_rel_def[symmetric]]])
    apply assumption
    apply (auto simp: conc_fun_RES bind_RES_RETURN_eq)
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


definition full_checker_l
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A) \<leftarrow> remap_polys_l spec' {} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      let \<V> = \<V> \<union> vars_llist spec;
      PAC_checker_l spec' (\<V>, A) b st
    }
  }\<close>


hide_fact (open) poly_embed.PAC_checker_l_PAC_checker
context poly_embed
begin


lemma check_del_l_check_del:
  \<open>(A, B) \<in> fmap_polys_rel \<Longrightarrow> (x3, x3a) \<in> Id \<Longrightarrow> check_del_l spec A (pac_src1 (Del x3))
  \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and> (b \<longrightarrow> st = CSUCCESS)} (check_del B (pac_src1 (Del x3a)))\<close>
  unfolding check_del_l_def check_del_def
  by (refine_vcg lhs_step_If RETURN_SPEC_refine)
    (auto simp: fmap_rel_nat_rel_dom_m bind_RES_RETURN_eq)

lemma PAC_checker_l_step_PAC_checker_step:
  assumes
    \<open>(Ast, Bst) \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> and
    \<open>(st, st') \<in> epac_step_rel\<close> and
    spec: \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>PAC_checker_l_step spec Ast st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (PAC_checker_step spec' Bst st')\<close>
proof -
  obtain A \<V> cst B \<V>' cst' where
   Ast: \<open>Ast = (cst, \<V>, A)\<close> and
   Bst: \<open>Bst = (cst', \<V>', B)\<close> and
   \<V>[intro]: \<open>(\<V>, \<V>') \<in>  \<langle>var_rel\<rangle>set_rel\<close>  and
   AB: \<open>(A, B) \<in> fmap_polys_rel\<close>
     \<open>(cst, cst') \<in> code_status_status_rel\<close>
    using assms(1)
    by (cases Ast; cases Bst; auto)
  have [refine]: \<open>(r, ra) \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
       (eqa, eqaa)
       \<in> {(st, b). (\<not> is_cfailed st \<longleftrightarrow> b) \<and> (is_cfound st \<longrightarrow> spec = r)} \<Longrightarrow>
       RETURN eqa
       \<le> \<Down> code_status_status_rel
          (SPEC
            (\<lambda>st'. (\<not> is_failed st' \<and>
                   is_found st' \<longrightarrow>
                    ra - spec' \<in> More_Modules.ideal polynomial_bool)))\<close>
     for r ra eqa eqaa
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
  show ?thesis
    using assms(2)
    unfolding PAC_checker_l_step_def PAC_checker_step_def Ast Bst prod.case
    apply (cases st; cases st'; simp only: p2rel_def pac_step.case
      pac_step_rel_raw_def mem_Collect_eq prod.case pac_step_rel_raw.simps)
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec check_linear_combi_l_check_linear_comb
        full_normalize_poly_diff_ideal)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      subgoal using AB by auto
      done
    subgoal
      apply (refine_rcg full_normalize_poly_diff_ideal
        check_extension_l_check_extension)
      subgoal using AB by (auto intro!: fully_unsorted_poly_rel_diff[of _ \<open>-Var _ :: int mpoly\<close>, unfolded H3[symmetric]] simp: comp_def case_prod_beta)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal by auto
      subgoal by auto
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto simp: AB
          intro!: fmap_rel_fmupd_fmap_rel insert_var_rel_set_rel)
      subgoal
        by (auto simp: code_status_status_rel_def AB
          code_status.is_cfailed_def)
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_del_l_check_del check_addition_l_check_add
        full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]])
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel code_status_status_rel_def AB)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      done
    done
qed

lemma PAC_checker_l_PAC_checker:
  assumes
    \<open>(A, B) \<in> \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>epac_step_rel\<rangle>list_rel\<close> and
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(b, b') \<in> code_status_status_rel\<close>
  shows
    \<open>PAC_checker_l spec A b st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (PAC_checker spec' B b' st')\<close>
proof -
  have [refine0]: \<open>(((b, A), st), (b', B), st') \<in> ((code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) \<times>\<^sub>r  \<langle>epac_step_rel\<rangle>list_rel)\<close>
    using assms by (auto simp: code_status_status_rel_def)
  show ?thesis
    using assms
    unfolding PAC_checker_l_def PAC_checker_def
    apply (refine_rcg PAC_checker_l_step_PAC_checker_step
      WHILEIT_refine[where R = \<open>((bool_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) \<times>\<^sub>r \<langle>pac_step_rel\<rangle>list_rel)\<close>])
    subgoal by (auto simp: code_status_status_rel_discrim_iff)
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv intro!: param_nth)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    done
qed

lemma full_checker_l_full_checker:
 assumes
    \<open>(A, B) \<in> unsorted_fmap_polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>epac_step_rel\<rangle>list_rel\<close> and
    \<open>(spec, spec') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>full_checker_l spec A st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (full_checker spec' B st')\<close>
proof -
  have [refine]:
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
    (\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
    remap_polys_l spec \<V> A \<le> \<Down>(code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel)
        (remap_polys_change_all spec' \<V>' B)\<close> for spec spec' \<V> \<V>'
    apply (rule remap_polys_l_remap_polys[THEN order_trans, OF assms(1)])
    apply assumption+
    apply (rule ref_two_step[OF order.refl])
    apply(rule remap_polys_spec[THEN order_trans])
    by (rule remap_polys_polynomial_bool_remap_polys_change_all)

  show ?thesis
    unfolding full_checker_l_def full_checker_def
    apply (refine_rcg remap_polys_l_remap_polys
       full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]]
       PAC_checker_l_PAC_checker)
    subgoal
      using assms(3) .
    subgoal by auto
    subgoal by (auto simp: is_cfailed_def is_failed_def)
    subgoal by auto
    apply (rule fully_unsorted_poly_rel_extend_vars)
    subgoal using assms(3) .
    subgoal by auto
    subgoal by auto
    subgoal
      using assms(2) by (auto simp: p2rel_def)
    subgoal by auto
    done
qed


lemma full_checker_l_full_checker':
  \<open>(uncurry2 full_checker_l, uncurry2 full_checker) \<in>
  ((fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r unsorted_fmap_polys_rel) \<times>\<^sub>r \<langle>epac_step_rel\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>(code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel)\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using full_checker_l_full_checker by force

end

definition remap_polys_l2 :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> _ nres\<close> where
  \<open>remap_polys_l2 spec = (\<lambda>\<V> A. do{
   n \<leftarrow> upper_bound_on_dom A;
   b \<leftarrow> RETURN (n \<ge> 2^64);
   if b
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     RETURN (error_msg (0 ::nat) c, \<V>, fmempty)
   }
   else do {
       (b, \<V>, A) \<leftarrow> nfoldli ([0..<n]) (\<lambda>_. True)
       (\<lambda>i (b, \<V>, A').
          if i \<in># dom_m A
          then do {
            ASSERT(fmlookup A i \<noteq> None);
            p \<leftarrow> full_normalize_poly (the (fmlookup A i));
            eq \<leftarrow> weak_equality_l p spec;
            \<V> \<leftarrow> RETURN (\<V> \<union> vars_llist (the (fmlookup A i)));
            RETURN(b \<or> eq, \<V>, fmupd i p A')
          } else RETURN (b, \<V>, A')
        )
       (False, \<V>, fmempty);
     RETURN (if b then CFOUND else CSUCCESS, \<V>, A)
    }
 })\<close>

lemma remap_polys_l2_remap_polys_l:
  \<open>remap_polys_l2 spec \<V> A \<le> \<Down> Id (remap_polys_l spec \<V> A)\<close>
proof -
  have [refine]: \<open>(A, A') \<in> Id \<Longrightarrow> upper_bound_on_dom A
    \<le> \<Down> {(n, dom). dom = set [0..<n]} (SPEC (\<lambda>dom. set_mset (dom_m A') \<subseteq> dom \<and> finite dom))\<close> for A A'
    unfolding upper_bound_on_dom_def
    apply (rule RES_refine)
    apply (auto simp: upper_bound_on_dom_def)
    done
  have 1: \<open>inj_on id dom\<close> for dom
    by auto
  have 2: \<open>x \<in># dom_m A \<Longrightarrow>
       x' \<in># dom_m A' \<Longrightarrow>
       (x, x') \<in> nat_rel \<Longrightarrow>
       (A, A') \<in> Id \<Longrightarrow>
       full_normalize_poly (the (fmlookup A x))
       \<le> \<Down> Id
          (full_normalize_poly (the (fmlookup A' x')))\<close>
       for A A' x x'
       by (auto)
  have 3: \<open>(n, dom) \<in> {(n, dom). dom = set [0..<n]} \<Longrightarrow>
       ([0..<n], dom) \<in> \<langle>nat_rel\<rangle>list_set_rel\<close> for n dom
  by (auto simp: list_set_rel_def br_def)
  have 4: \<open>(p,q) \<in> Id \<Longrightarrow>
    weak_equality_l p spec \<le> \<Down>Id (weak_equality_l q spec)\<close> for p q spec
    by auto

  have 6: \<open>a = b \<Longrightarrow> (a, b) \<in> Id\<close> for a b
    by auto
  show ?thesis
    unfolding remap_polys_l2_def remap_polys_l_def
    apply (refine_rcg LFO_refine[where R= \<open>Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel \<times>\<^sub>r Id\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule 3)
    subgoal by auto
    subgoal by (simp add: in_dom_m_lookup_iff)
    subgoal by (simp add: in_dom_m_lookup_iff)
    apply (rule 2)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule 4; assumption)
    apply (rule 6)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

end
