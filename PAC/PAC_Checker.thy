theory PAC_Checker
  imports PAC_Polynoms_Operations
    PAC_Checker_Specification
    PAC_Map_Rel
    Show.Show
    Show.Show_Instances
begin



fun pac_step_rel_raw :: \<open>(nat \<times> nat) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'a pac_step \<Rightarrow> 'b pac_step \<Rightarrow> bool\<close> where
\<open>pac_step_rel_raw R1 R2 (AddD p1 p2 i r) (AddD p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R1 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 (Add p1 p2 i r) (Add p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R1 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 (MultD p1 p2 i r) (MultD p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R2 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 (Mult p1 p2 i r) (Mult p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R2 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 _ _ \<longleftrightarrow> False\<close>

fun pac_step_rel_assn :: \<open>(nat \<Rightarrow> nat \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a pac_step \<Rightarrow> 'b pac_step \<Rightarrow> assn\<close> where
\<open>pac_step_rel_assn R1 R2 (AddD p1 p2 i r) (AddD p1' p2' i' r') =
   R1 p1 p1' * R1 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 (Add p1 p2 i r) (Add p1' p2' i' r') =
   R1 p1 p1' * R1 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 (MultD p1 p2 i r) (MultD p1' p2' i' r') =
   R1 p1 p1' * R2 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 (Mult p1 p2 i r) (Mult p1' p2' i' r') =
   R1 p1 p1' * R2 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 _ _ = false\<close>

datatype 'a status =
  FAILED (status_error: 'a) |
  is_success: SUCCESS

lemma is_success_alt_def:
  \<open>is_success a \<longleftrightarrow> a = SUCCESS\<close>
  by (cases a) auto

definition error_msg where
  \<open>error_msg i msg = FAILED (''s CHECKING failed at line '' @ show i @ '' with error '' @ msg)\<close>

definition bool_with_error_msg where
  \<open>bool_with_error_msg = {(st, b). b \<longleftrightarrow> st = SUCCESS}\<close>

definition error_msg_notin_dom_err where
  \<open>error_msg_notin_dom_err = '' notin domain''\<close>

definition error_msg_notin_dom :: \<open>nat \<Rightarrow> string\<close> where
  \<open>error_msg_notin_dom i = show i @ error_msg_notin_dom_err\<close>

definition error_msg_reused_dom where
  \<open>error_msg_reused_dom i = show i @ '' already in domain''\<close>


definition error_msg_not_equal_dom where
  \<open>error_msg_not_equal_dom p q = show p @ '' and '' @ show q @ '' not equal''\<close>


definition check_addition_l :: \<open>_ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> string status nres\<close> where
\<open>check_addition_l A p q i r = do {
   if p \<notin># dom_m A \<or> q \<notin># dom_m A \<or> i \<in># dom_m A
   then RETURN (error_msg i ((if p \<notin># dom_m A then error_msg_notin_dom p else []) @ (if q \<notin># dom_m A then error_msg_notin_dom p else []) @
      (if i \<in># dom_m A then error_msg_reused_dom p else [])))
   else do {
     ASSERT (p \<in># dom_m A);
     let p = the (fmlookup A p);
     ASSERT (q \<in># dom_m A);
     let q = the (fmlookup A q);
     pq \<leftarrow> add_poly_l (p, q);
     b \<leftarrow> weak_equality_p pq r;
     if b then RETURN SUCCESS else RETURN (error_msg i (error_msg_not_equal_dom pq r))
   }
}\<close>

definition check_mult_l_dom_err :: \<open>bool \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_mult_l_dom_err p_notin p i_already i = SPEC (\<lambda>_. True)\<close>


definition check_mult_l_mult_err :: \<open>llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> string nres\<close> where
  \<open>check_mult_l_mult_err p q pq r = SPEC (\<lambda>_. True)\<close>


definition check_mult_l :: \<open>_ \<Rightarrow> nat \<Rightarrow>llist_polynom \<Rightarrow>  nat \<Rightarrow> llist_polynom \<Rightarrow> string status  nres\<close> where
\<open>check_mult_l A p q i r = do {
    if p \<notin># dom_m A \<or> i \<in># dom_m A
    then do {
      c \<leftarrow> check_mult_l_dom_err (p \<notin># dom_m A) p (i \<in># dom_m A) i;
      RETURN (error_msg i c)}
    else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       pq \<leftarrow> mult_poly_full p q;
       b \<leftarrow> weak_equality_p pq r;
       if b then RETURN SUCCESS else do {
         c \<leftarrow> check_mult_l_mult_err p q pq r;
         RETURN (error_msg i c)
       }
     }
  }\<close>

(* Copy of WB_More_Refinement *)
lemma RES_RES_RETURN_RES: \<open>RES A \<bind> (\<lambda>T. RES (f T)) = RES (\<Union>(f ` A))\<close>
  by (auto simp:  pw_eq_iff refine_pw_simps)


lemma check_add_alt_def:
  \<open>check_add A p q i r =
    do {
     if p \<notin># dom_m A \<or> q \<notin># dom_m A \<or> i \<in># dom_m A
     then RETURN False
     else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       ASSERT (q \<in># dom_m A);
       let q = the (fmlookup A q);
       pq \<leftarrow> add_poly_spec p q;
       eq \<leftarrow> weak_equality pq r;
       RETURN eq
     }
  }\<close>
  by (auto simp: check_add_def weak_equality_def
      add_poly_spec_def RES_RES_RETURN_RES
    intro!:  ideal.span_zero
      exI[of _ \<open>the (fmlookup A p) + the (fmlookup A q)\<close>])



lemma check_mult_alt_def:
  \<open>check_mult A p q i r =
    do {
     if p \<notin># dom_m A \<or> i \<in># dom_m A
     then RETURN False
     else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       pq \<leftarrow> mult_poly_spec p q;
       p \<leftarrow> weak_equality pq r;
       RETURN p
     }
  }\<close>
  by (auto simp: check_mult_def weak_equality_def
      mult_poly_spec_def RES_RES_RETURN_RES
    intro!:  ideal.span_zero
      exI[of _ \<open>the (fmlookup A p) * q\<close>])


lemma fmap_rel_nat_rel_dom_m[simp]:
  \<open>(A, B) \<in> \<langle>nat_rel, R\<rangle>fmap_rel \<Longrightarrow> dom_m A = dom_m B\<close>
  by (subst distinct_set_mset_eq_iff[symmetric])
    (auto simp: fmap_rel_alt_def distinct_mset_dom)

lemma fmap_rel_nat_the_fmlookup[simp]:
  \<open>(A, B) \<in> \<langle>S, R\<rangle>fmap_rel \<Longrightarrow> (p, p') \<in> S \<Longrightarrow> p' \<in># dom_m B \<Longrightarrow>
   (the (fmlookup A p), the (fmlookup B p')) \<in> R\<close>
  by (auto simp: fmap_rel_alt_def distinct_mset_dom)

lemma ref_two_step':
  \<open>A \<le> B \<Longrightarrow>  \<Down> R A \<le> \<Down> R B\<close>
  using ref_two_step by auto



definition PAC_checker_l_step ::  _ where
  \<open>PAC_checker_l_step A st = (case st of
     AddD _ _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> normalize_poly (pac_res st);
        eq \<leftarrow> check_addition_l A (pac_src1 st) (pac_src2 st) (new_id st) r;
        if eq = SUCCESS
        then RETURN (eq,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) (fmdrop (pac_src2 st) A)))
        else RETURN (eq, A)
   }
   | Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
        eq \<leftarrow> check_addition_l A (pac_src1 st) (pac_src2 st) (new_id st) r;
        if eq = SUCCESS
        then RETURN (eq,
          fmupd (new_id st) r A)
        else RETURN (eq, A)
   }
   | MultD _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
         q \<leftarrow> normalize_poly (pac_mult st);
        eq \<leftarrow> check_mult_l A (pac_src1 st) q (new_id st) r;
        if eq = SUCCESS
        then RETURN (eq,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) A))
        else RETURN (eq, A)
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
         q \<leftarrow> normalize_poly (pac_mult st);
        eq \<leftarrow> check_mult_l A (pac_src1 st) q (new_id st) r;
        if eq = SUCCESS
        then RETURN (eq,
          fmupd (new_id st) r A)
        else RETURN (eq, A)
   }
 )\<close>


lemma pac_step_rel_raw_def:
  \<open>\<langle>K, V\<rangle> pac_step_rel_raw = pac_step_rel_raw K V\<close>
  by (auto intro!: ext simp: relAPP_def)

definition PAC_checker_l where
  \<open>PAC_checker_l A st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b, A), n::nat). b = SUCCESS \<and> n < length st)
       (\<lambda>((b, A), n). do {
          ASSERT(n < length st);
          S \<leftarrow> PAC_checker_l_step A (st ! n);
          RETURN (S, (n+1))
        })
      ((SUCCESS, A), 0);
    RETURN S
  }\<close>


context poly_embed
begin

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, unsorted_poly_rel O mset_poly_rel\<rangle> pac_step_rel_raw)\<close>

abbreviation polys_rel where
  \<open>polys_rel \<equiv> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close>


lemma fref_to_Down_curry:
  \<open>(uncurry f, uncurry g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y'. P (x', y') \<Longrightarrow> ((x, y), (x', y')) \<in> A \<Longrightarrow> f x y \<le> \<Down> B (g x' y'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma weak_equality_spec_weak_equality:
  \<open>(p, p') \<in> mset_poly_rel \<Longrightarrow>
    (r, r') \<in> mset_poly_rel \<Longrightarrow>
    weak_equality_spec p r \<le> weak_equality p' r'\<close>
  unfolding weak_equality_spec_def weak_equality_def
  by (auto simp: mset_poly_rel_def)


lemma weak_equality_p_weak_equality_p'[refine]:
  \<open>weak_equality_p p q \<le> \<Down> bool_rel (weak_equality p' q')\<close>
  if \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
  for p p' q q'
  using that
  by (auto intro!: weak_equality_p_weak_equality_spec[THEN fref_to_Down_curry, THEN order_trans]
         ref_two_step'
         weak_equality_spec_weak_equality
      simp flip: conc_fun_chain)

lemma error_msg_ne_SUCCES[simp, iff]: \<open>error_msg i m \<noteq> SUCCESS\<close>
  by (auto simp: error_msg_def)

lemma check_addition_l_check_add:
  assumes \<open>(A, B) \<in> polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>check_addition_l A p q i r \<le> \<Down> bool_with_error_msg (check_add B p q i r')\<close>
proof -
  have [refine]:
    \<open>add_poly_l (p, q) \<le> \<Down> (sorted_poly_rel O mset_poly_rel) (add_poly_spec p' q')\<close>
    if \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close>
      \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
    for p p' q q'
    using that
    by (auto intro!: add_poly_l_add_poly_p'[THEN order_trans] ref_two_step'
         add_poly_p'_add_poly_spec
      simp flip: conc_fun_chain)

  show ?thesis
    using assms
    unfolding check_addition_l_def check_add_alt_def
    apply refine_rcg
    subgoal
      by auto
    subgoal
      by (auto simp: bool_with_error_msg_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: bool_with_error_msg_def)
    done
qed

lemma check_mult_l_check_mult:
  assumes \<open>(A, B) \<in> polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>check_mult_l A p q i r \<le> \<Down>bool_with_error_msg (check_mult B p q' i r')\<close>
proof -
  have [refine]:
    \<open>mult_poly_full p q \<le> \<Down> (sorted_poly_rel O mset_poly_rel) (mult_poly_spec p' q')\<close>
    if \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close>
      \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
    for p p' q q'
    using that
    by (auto intro!: mult_poly_full_mult_poly_p'[THEN order_trans] ref_two_step'
         mult_poly_p'_mult_poly_spec
      simp flip: conc_fun_chain)

  show ?thesis
    using assms
    unfolding check_mult_l_def check_mult_alt_def
      check_mult_l_mult_err_def check_mult_l_dom_err_def
    apply refine_rcg
    subgoal
      by auto
    subgoal
      by (auto simp: bool_with_error_msg_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: bool_with_error_msg_def bind_RES_RETURN_eq)
    done
qed


lemma normalize_poly_normalize_poly_spec:
  assumes \<open>(r, t) \<in> unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>normalize_poly r \<le> \<Down>(sorted_poly_rel O mset_poly_rel) (normalize_poly_spec t)\<close>
proof -
  obtain s where
    rs: \<open>(r, s) \<in> unsorted_poly_rel\<close> and
    st: \<open>(s, t) \<in> mset_poly_rel\<close>
    using assms by auto
  show ?thesis
    by (rule normalize_poly_normalize_poly_p[THEN order_trans, OF rs])
     (use st in \<open>auto dest!: rtranclp_normalize_poly_p_poly_of_mset
      intro!: ref_two_step' RES_refine exI[of _ t]
      simp: normalize_poly_spec_def ideal.span_zero mset_poly_rel_def
      simp flip: conc_fun_chain\<close>)
qed


lemma PAC_checker_l_step_PAC_checker_step:
  assumes
    \<open>(A, B) \<in> polys_rel\<close> and
    \<open>(st, st') \<in> pac_step_rel\<close>
  shows
    \<open>PAC_checker_l_step A st \<le> \<Down> (bool_with_error_msg \<times>\<^sub>r polys_rel) (PAC_checker_step B st')\<close>
proof -
  show ?thesis
    using assms(2)
    unfolding PAC_checker_l_step_def PAC_checker_step_def
    apply (cases st; cases st') apply (clarsimp_all simp: p2rel_def
      pac_step_rel_raw_def)
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using assms by auto
      subgoal by (auto simp: bool_with_error_msg_def)
      subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel assms)
      subgoal using assms by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using assms by auto
      subgoal by (auto simp: bool_with_error_msg_def)
      subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel assms)
      subgoal using assms by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal by (auto simp: bool_with_error_msg_def)
      subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel assms)
      subgoal using assms by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal by (auto simp: bool_with_error_msg_def)
      subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel assms)
      subgoal using assms by auto
      done
    done
qed

lemma PAC_checker_l_PAC_checker:
  assumes
    \<open>(A, B) \<in> polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>pac_step_rel\<rangle>list_rel\<close>
  shows
    \<open>PAC_checker_l A st \<le> \<Down> (bool_with_error_msg \<times>\<^sub>r polys_rel) (PAC_checker B st')\<close>
proof -
  have [refine0]: \<open>(((SUCCESS, A), 0), (True, B), 0) \<in> ((bool_with_error_msg \<times>\<^sub>r polys_rel) \<times>\<^sub>r nat_rel)\<close>
    using assms by (auto simp: bool_with_error_msg_def)
  show ?thesis
    using assms
    unfolding PAC_checker_l_def PAC_checker_def
    apply (refine_rcg PAC_checker_l_step_PAC_checker_step
      WHILEIT_refine[where R = \<open>((bool_rel \<times>\<^sub>r polys_rel) \<times>\<^sub>r nat_rel)\<close>])
    subgoal by (auto simp: list_rel_imp_same_length bool_with_error_msg_def)
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by (auto simp: list_rel_imp_same_length intro!: param_nth)
    subgoal by (auto simp: list_rel_imp_same_length)
    subgoal by (auto simp: list_rel_imp_same_length)
    done
qed

end

lemma less_than_char_of_char[code_unfold]:
  \<open>(x, y) \<in> less_than_char \<longleftrightarrow> (of_char x :: nat) < of_char y\<close>
  by (auto simp: less_than_char_def less_char_def)


lemmas [code] = 
  add_poly_l'.simps[unfolded var_order_rel_def]

export_code add_poly_l' in SML module_name test


end
