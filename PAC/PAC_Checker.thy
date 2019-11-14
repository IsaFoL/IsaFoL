theory PAC_Checker
  imports PAC_Polynoms_Operations
    PAC_Checker_Specification
    PAC_Map_Rel
    Show.Show
    Show.Show_Instances
begin


datatype 'a code_status =
  is_cfailed: CFAILED (the_error: 'a) |
  CSUCCESS |
  is_cfound: CFOUND

fun merge_cstatus where
  \<open>merge_cstatus (CFAILED a) _ = CFAILED a\<close> |
  \<open>merge_cstatus _ (CFAILED a) = CFAILED a\<close> |
  \<open>merge_cstatus CFOUND _ = CFOUND\<close> |
  \<open>merge_cstatus _ CFOUND = CFOUND\<close> |
  \<open>merge_cstatus _ _ = CSUCCESS\<close>

definition code_status_status_rel :: \<open>('a code_status \<times> status) set\<close> where
\<open>code_status_status_rel =
  {(CFOUND, FOUND), (CSUCCESS, SUCCESS)} \<union>
  {(CFAILED a, FAILED)| a. True}\<close>

lemma in_code_status_status_rel_iff[simp]:
  \<open>(CFOUND, b) \<in> code_status_status_rel \<longleftrightarrow> b = FOUND\<close>
  \<open>(a, FOUND) \<in> code_status_status_rel \<longleftrightarrow> a = CFOUND\<close>
  \<open>(CSUCCESS, b) \<in> code_status_status_rel \<longleftrightarrow> b = SUCCESS\<close>
  \<open>(a, SUCCESS) \<in> code_status_status_rel \<longleftrightarrow> a = CSUCCESS\<close>
  \<open>(a, FAILED) \<in> code_status_status_rel \<longleftrightarrow> is_cfailed a\<close>
  \<open>(CFAILED C, b) \<in> code_status_status_rel \<longleftrightarrow> b = FAILED\<close>
  by (cases a; cases b; auto simp: code_status_status_rel_def; fail)+
  
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

definition error_msg where
  \<open>error_msg i msg = CFAILED (''s CHECKING failed at line '' @ show i @ '' with error '' @ msg)\<close>

definition error_msg_notin_dom_err where
  \<open>error_msg_notin_dom_err = '' notin domain''\<close>

definition error_msg_notin_dom :: \<open>nat \<Rightarrow> string\<close> where
  \<open>error_msg_notin_dom i = show i @ error_msg_notin_dom_err\<close>

definition error_msg_reused_dom where
  \<open>error_msg_reused_dom i = show i @ '' already in domain''\<close>


definition error_msg_not_equal_dom where
  \<open>error_msg_not_equal_dom p q pq r = show p @ '' + '' @ show q @ '' = '' @ show pq @ '' not equal'' @ show r\<close>


definition check_not_equal_dom_err :: \<open>llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> string nres\<close> where
  \<open>check_not_equal_dom_err p q pq r = SPEC (\<lambda>_. True)\<close>

definition check_addition_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> string code_status nres\<close> where
\<open>check_addition_l spec A p q i r = do {
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
     b' \<leftarrow> weak_equality_p r spec;
     if b then (if b' then RETURN CFOUND else RETURN CSUCCESS)
     else do {
       c \<leftarrow> check_not_equal_dom_err p q pq r;
       RETURN (error_msg i c)}
   }
}\<close>

definition check_mult_l_dom_err :: \<open>bool \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> string nres\<close> where
  \<open>check_mult_l_dom_err p_notin p i_already i = SPEC (\<lambda>_. True)\<close>


definition check_mult_l_mult_err :: \<open>llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> string nres\<close> where
  \<open>check_mult_l_mult_err p q pq r = SPEC (\<lambda>_. True)\<close>


definition check_mult_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow>llist_polynom \<Rightarrow>  nat \<Rightarrow> llist_polynom \<Rightarrow> string code_status nres\<close> where
\<open>check_mult_l spec A p q i r = do {
    if p \<notin># dom_m A \<or> i \<in># dom_m A
    then do {
      c \<leftarrow> check_mult_l_dom_err (p \<notin># dom_m A) p (i \<in># dom_m A) i;
      RETURN (error_msg i c)}
    else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       pq \<leftarrow> mult_poly_full p q;
       b \<leftarrow> weak_equality_p pq r;
       b' \<leftarrow> weak_equality_p r spec;
       if b then (if b' then RETURN CFOUND else RETURN CSUCCESS) else do {
         c \<leftarrow> check_mult_l_mult_err p q pq r;
         RETURN (error_msg i c)
       }
     }
  }\<close>

(* Copy of WB_More_Refinement *)
lemma RES_RES_RETURN_RES: \<open>RES A \<bind> (\<lambda>T. RES (f T)) = RES (\<Union>(f ` A))\<close>
  by (auto simp: pw_eq_iff refine_pw_simps)


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
  \<open>PAC_checker_l_step = (\<lambda>spec (st', A) st. case st of
     AddD _ _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> normalize_poly (pac_res st);
        eq \<leftarrow> check_addition_l spec A (pac_src1 st) (pac_src2 st) (new_id st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) (fmdrop (pac_src2 st) A)))
        else RETURN (eq, A)
   }
   | Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
        eq \<leftarrow> check_addition_l spec A (pac_src1 st) (pac_src2 st) (new_id st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          fmupd (new_id st) r A)
        else RETURN (eq, A)
   }
   | MultD _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
         q \<leftarrow> normalize_poly (pac_mult st);
        eq \<leftarrow> check_mult_l spec A (pac_src1 st) q (new_id st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          fmupd (new_id st) r
            (fmdrop (pac_src1 st) A))
        else RETURN (eq, A)
   }
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> normalize_poly (pac_res st);
         q \<leftarrow> normalize_poly (pac_mult st);
        eq \<leftarrow> check_mult_l spec A (pac_src1 st) q (new_id st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          fmupd (new_id st) r A)
        else RETURN (eq, A)
   }
 )\<close>


lemma pac_step_rel_raw_def:
  \<open>\<langle>K, V\<rangle> pac_step_rel_raw = pac_step_rel_raw K V\<close>
  by (auto intro!: ext simp: relAPP_def)

definition mononoms_equal_up_to_reorder where
  \<open>mononoms_equal_up_to_reorder xs ys \<longleftrightarrow>
     map (\<lambda>(a, b).  (mset a, b)) xs = map (\<lambda>(a, b). (mset a, b)) ys\<close>


 definition normalize_poly_l where
  \<open>normalize_poly_l p = SPEC (\<lambda>p'.
     normalize_poly_p\<^sup>*\<^sup>* ((\<lambda>(a, b). (mset a, b)) `# mset p) ((\<lambda>(a, b). (mset a, b)) `# mset p') \<and>
     0 \<notin># snd `# mset p' \<and>
     sorted_wrt (rel2p (term_order_rel \<times>\<^sub>r int_rel)) p' \<and>
     (\<forall> x \<in> mononoms p'. sorted_wrt (rel2p var_order_rel) x))\<close>

definition remap_polys_l :: \<open>(nat, llist_polynom) fmap \<Rightarrow> _ nres\<close> where
  \<open>remap_polys_l A = do{
    dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   FOREACH dom
     (\<lambda>i A'.
        if i \<in># dom_m A
        then  do {
          p \<leftarrow> full_normalize_poly (the (fmlookup A i));
          RETURN(fmupd i p A')
        } else RETURN A')
     fmempty
 }\<close>

definition PAC_checker_l where
  \<open>PAC_checker_l spec A st = do {
    (S, _) \<leftarrow> WHILE\<^sub>T
       (\<lambda>((b, A), n::nat). \<not>is_cfailed b \<and> n < length st)
       (\<lambda>((bA), n). do {
          ASSERT(n < length st);
          S \<leftarrow> PAC_checker_l_step spec bA (st ! n);
          RETURN (S, (n+1))
        })
      ((CSUCCESS, A), 0);
    RETURN S
  }\<close>


context poly_embed
begin

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, unsorted_poly_rel O mset_poly_rel\<rangle> pac_step_rel_raw)\<close>

abbreviation polys_rel where
  \<open>polys_rel \<equiv> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close>

lemma
  \<open>normalize_poly_p s0 s \<Longrightarrow>
        (s0, p) \<in> mset_poly_rel \<Longrightarrow>
        (s, p) \<in> mset_poly_rel\<close>
  by (auto simp: mset_poly_rel_def normalize_poly_p_poly_of_mset)

lemma
  assumes \<open>(A, B) \<in> \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close>
  shows \<open>remap_polys_l A \<le> \<Down> (polys_rel) (remap_polys B)\<close>
proof -
  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by auto
  have remap_polys_alt_def:
    \<open>remap_polys A = do{
       dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
       A' \<leftarrow> FOREACH dom
         (\<lambda>i A'.
            if i \<in># dom_m A
            then do {
              p \<leftarrow> SPEC(\<lambda>p. the (fmlookup A i) - p \<in> ideal polynom_bool);
              RETURN(fmupd i p A')
            } else RETURN A')
         fmempty;
       RETURN A'
     }\<close> for A
    unfolding remap_polys_def by auto
  have remap_polys_l_alt_def:
    \<open>remap_polys_l A = do{
       dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
       A' \<leftarrow> FOREACH dom
         (\<lambda>i A'.
            if i \<in># dom_m A
            then  do {
              p \<leftarrow> full_normalize_poly (the (fmlookup A i));
              RETURN(fmupd i p A')
            } else RETURN A')
         fmempty;
       RETURN A'
     }\<close> for A
     unfolding remap_polys_l_def
     by auto
  have H: \<open>x \<in># dom_m A \<Longrightarrow>
     (\<And>p. (the (fmlookup A x), p) \<in> fully_unsorted_poly_rel \<Longrightarrow>
       (p, the (fmlookup B x)) \<in> mset_poly_rel \<Longrightarrow> thesis) \<Longrightarrow>
     thesis\<close> for x thesis
     using fmap_rel_nat_the_fmlookup[OF assms, of x x] fmap_rel_nat_rel_dom_m[OF assms] by auto
  have full_normalize_poly: \<open>full_normalize_poly (the (fmlookup A x))
       \<le> \<Down> (sorted_poly_rel O mset_poly_rel)
          (SPEC
            (\<lambda>p. the (fmlookup B x') - p \<in> More_Modules.ideal polynom_bool))\<close>
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

  have emp: \<open>(fmempty, fmempty) \<in> polys_rel\<close>
    by auto
  show ?thesis
    using assms
    unfolding remap_polys_l_alt_def
      remap_polys_alt_def
    apply (refine_rcg full_normalize_poly fmap_rel_fmupd_fmap_rel)
    subgoal
      by auto
    apply (rule 1)
    subgoal by auto
    apply (rule emp)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed


definition remap_polys_in_place_l:: \<open>(nat, llist_polynom) fmap \<Rightarrow> _ nres\<close> where
  \<open>remap_polys_in_place_l A = do{
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   FOREACH dom
     (\<lambda>i A.
        if i \<in># dom_m A
        then  do {
          p \<leftarrow> full_normalize_poly (the (fmlookup A i));
          RETURN(fmupd i p A)
        } else RETURN A)
     A
 }\<close>

lemma
  \<open>remap_polys_in_place_l A \<le> \<Down>Id (remap_polys_l A)\<close>

proof -
  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by auto
  have remap_polys_in_place_l_alt_def:
    \<open>remap_polys_in_place_l A = do{
       dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
       A' \<leftarrow>  FOREACH dom
     (\<lambda>i A.
        if i \<in># dom_m A
        then  do {
          p \<leftarrow> full_normalize_poly (the (fmlookup A i));
          RETURN(fmupd i p A)
        } else RETURN A)
     A;
       RETURN A'
     }\<close> for A
    unfolding remap_polys_in_place_l_def by auto
  have remap_polys_l_alt_def:
    \<open>remap_polys_l A = do{
       dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
       A' \<leftarrow> FOREACH dom
         (\<lambda>i A'.
            if i \<in># dom_m A
            then  do {
              p \<leftarrow> full_normalize_poly (the (fmlookup A i));
              RETURN(fmupd i p A')
            } else RETURN A')
         fmempty;
       RETURN A'
     }\<close> for A
     unfolding remap_polys_l_def
     by auto
  let ?I = \<open>\<lambda>dom A' dom' fmempty. (A', fmempty) \<in> {(D, C).
        dom_m D = mset_set (dom \<inter> set_mset (dom_m A))+ dom_m C \<and>
          (\<forall>i\<in>dom. i \<notin># dom_m C) \<and>
        (\<forall>i. i\<in>dom \<longrightarrow> fmlookup D i = fmlookup A i) \<and>
        (\<forall>i \<in> set_mset (dom_m A) - dom. fmlookup D i = fmlookup C i) \<and>
        dom_m C \<subseteq># dom_m A}\<close>

  have 2: \<open>((dom, A), id ` dom, fmempty) \<in> {((dom, A'), dom', fmempty). ?I dom A' dom' fmempty}\<close>
    if \<open>dom \<in> {dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom}\<close>
    for dom
    using that in_dom_m_lookup_iff apply auto
    apply (metis dom_m_fmrestrict_set' fmlookup_restrict_set_id')
    done
  have 3: \<open>(dom, doma) \<in> Id \<Longrightarrow>
    dom \<in> {dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom} \<Longrightarrow>
    doma \<in> {dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom} \<Longrightarrow>
    x' = id x \<Longrightarrow>
    x \<in> it \<Longrightarrow>
    x' \<in> it' \<Longrightarrow>
    (( it, \<sigma>), it', \<sigma>') \<in> {((dom, A'), dom', fmempty). ?I dom A' dom' fmempty} \<Longrightarrow>
    x \<in># dom_m \<sigma> \<Longrightarrow>
    x' \<in># dom_m A \<Longrightarrow>
    full_normalize_poly (the (fmlookup \<sigma> x))
    \<le> \<Down> Id
       (full_normalize_poly (the (fmlookup A x')))\<close>
    for dom doma x it \<sigma> x' it' \<sigma>'
    by (auto dest!: multi_member_split)

  show ?thesis
  supply FOREACH_refine_rcg[refine del]
    unfolding remap_polys_l_alt_def remap_polys_in_place_l_alt_def
    apply (refine_vcg FOREACH_refine_genR[where \<alpha> = id and R = \<open>{((dom, A'), dom', fmempty). ?I dom A' dom' fmempty}\<close> and
       R' = \<open>{(C, D). ?I {} C {} D}\<close>])
    apply (rule 1)
    subgoal by auto
    apply (rule 2, assumption)
    subgoal
      by (auto simp add: in_dom_m_lookup_iff intro: in_mono)
    apply (rule 3; assumption)
    subgoal for dom doma x it \<sigma> x' it' \<sigma>'
      apply (auto dest: multi_member_split simp: ac_simps mset_set.insert_remove
        intro: subset_add_mset_notin_subset)
      using multi_member_split subset_add_mset_notin_subset by fastforce+
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      apply auto
      by (metis (mono_tags) Collect_mem_eq Collect_mono_iff finite_set_mset fmap_ext
        in_dom_m_lookup_iff mset_set_subset_iff subset_mset.dual_order.trans)
    done
qed


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

lemma error_msg_ne_SUCCES[iff]:
  \<open>error_msg i m \<noteq> CSUCCESS\<close>
  \<open>error_msg i m \<noteq> CFOUND\<close>
  \<open>is_cfailed (error_msg i m)\<close>
  \<open>\<not>is_cfound (error_msg i m)\<close>
  by (auto simp: error_msg_def)

lemma check_addition_l_check_add:
  assumes \<open>(A, B) \<in> polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(p, p') \<in> Id\<close> \<open>(q, q') \<in> Id\<close> \<open>(i, i') \<in> nat_rel\<close>
  shows
    \<open>check_addition_l spec A p q i r \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
       (is_cfound st \<longrightarrow> spec = r)} (check_add B p' q' i' r')\<close>
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
      check_not_equal_dom_err_def
    apply refine_rcg
    subgoal
      by auto
    subgoal
      by (auto simp: )
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: weak_equality_p_def bind_RES_RETURN_eq)
    done
qed

lemma check_mult_l_check_mult:
  assumes \<open>(A, B) \<in> polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(p, p') \<in> Id\<close> \<open>(i, i') \<in> nat_rel\<close>
  shows
    \<open>check_mult_l spec A p q i r \<le> \<Down>  {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
       (is_cfound st \<longrightarrow> spec = r)} (check_mult B p' q' i' r')\<close>
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
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: weak_equality_p_def bind_RES_RETURN_eq)
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
    \<open>(Ast, Bst) \<in> code_status_status_rel \<times>\<^sub>r polys_rel\<close> and
    \<open>(st, st') \<in> pac_step_rel\<close> and
    spec: \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>PAC_checker_l_step spec Ast st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r polys_rel) (PAC_checker_step spec' Bst st')\<close>
proof -
  obtain A cst B cst' where
   Ast: \<open>Ast = (cst, A)\<close> and
   Bst: \<open>Bst = (cst', B)\<close> and
   AB: \<open>(A, B) \<in> polys_rel\<close>
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
                    ra - spec' \<in> More_Modules.ideal polynom_bool)))\<close>
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
  show ?thesis
    using assms(2)
    unfolding PAC_checker_l_step_def PAC_checker_step_def Ast Bst prod.case
    apply (cases st; cases st'; simp only: p2rel_def pac_step.case
      pac_step_rel_raw_def mem_Collect_eq prod.case pac_step_rel_raw.simps)
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using AB by auto
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      subgoal using AB by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using AB by auto
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      subgoal using AB by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using AB by auto
      subgoal using AB by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      subgoal using AB by auto
      done
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add)
      subgoal by auto
      subgoal using AB by auto
      subgoal using AB by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      apply assumption+
      subgoal
        by (auto simp: code_status_status_rel_def)
      subgoal
        by (auto intro!: fmap_rel_fmupd_fmap_rel
          fmap_rel_fmdrop_fmap_rel AB)
      subgoal using AB by auto
      done
    done
qed

lemma code_status_status_rel_discrim_iff:
  \<open>(x1a, x1c) \<in> code_status_status_rel \<Longrightarrow> is_cfailed x1a \<longleftrightarrow> is_failed x1c\<close>
  \<open>(x1a, x1c) \<in> code_status_status_rel \<Longrightarrow> is_cfound x1a \<longleftrightarrow> is_found x1c\<close>
  by (cases x1a; cases x1c; auto; fail)+

lemma PAC_checker_l_PAC_checker:
  assumes
    \<open>(A, B) \<in> polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>pac_step_rel\<rangle>list_rel\<close> and
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>PAC_checker_l spec A st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r polys_rel) (PAC_checker spec' B st')\<close>
proof -
  have [refine0]: \<open>(((CSUCCESS, A), 0), (SUCCESS, B), 0) \<in> ((code_status_status_rel \<times>\<^sub>r polys_rel) \<times>\<^sub>r nat_rel)\<close>
    using assms by (auto simp: code_status_status_rel_def)
  show ?thesis
    using assms
    unfolding PAC_checker_l_def PAC_checker_def
    apply (refine_rcg PAC_checker_l_step_PAC_checker_step
      WHILEIT_refine[where R = \<open>((bool_rel \<times>\<^sub>r polys_rel) \<times>\<^sub>r nat_rel)\<close>])
    subgoal by (auto simp: list_rel_imp_same_length code_status_status_rel_discrim_iff)
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

