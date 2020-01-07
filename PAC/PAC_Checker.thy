theory PAC_Checker
  imports PAC_Polynoms_Operations
    PAC_Checker_Specification
    PAC_Map_Rel
    Show.Show
    Show.Show_Instances
begin

section \<open>Executable Checker\<close>


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

fun pac_step_rel_raw :: \<open>(nat \<times> nat) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('c \<times> 'd) set \<Rightarrow> ('a, 'c) pac_step \<Rightarrow> ('b, 'd) pac_step \<Rightarrow> bool\<close> where
\<open>pac_step_rel_raw R1 R2 R3 (Add p1 p2 i r) (Add p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R1 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 R3 (Mult p1 p2 i r) (Mult p1' p2' i' r') \<longleftrightarrow>
   (p1, p1') \<in> R1 \<and> (p2, p2') \<in> R2 \<and> (i, i') \<in> R1 \<and>
   (r, r') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 R3 (Del p1) (Del p1') \<longleftrightarrow>
   (p1, p1') \<in> R1\<close> |
\<open>pac_step_rel_raw R1 R2 R3 (Extension i x p1) (Extension j x' p1') \<longleftrightarrow>
   (i, j) \<in> R1 \<and> (x, x') \<in> R3 \<and> (p1, p1') \<in> R2\<close> |
\<open>pac_step_rel_raw R1 R2 R3 _ _ \<longleftrightarrow> False\<close>

fun pac_step_rel_assn :: \<open>(nat \<Rightarrow> nat \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> assn) \<Rightarrow> ('a, 'c) pac_step \<Rightarrow> ('b, 'd) pac_step \<Rightarrow> assn\<close> where
\<open>pac_step_rel_assn R1 R2 R3 (Add p1 p2 i r) (Add p1' p2' i' r') =
   R1 p1 p1' * R1 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 R3 (Mult p1 p2 i r) (Mult p1' p2' i' r') =
   R1 p1 p1' * R2 p2 p2' * R1 i i' *
   R2 r r'\<close> |
\<open>pac_step_rel_assn R1 R2 R3 (Del p1) (Del p1') =
   R1 p1 p1'\<close> |
\<open>pac_step_rel_assn R1 R2 R3 (Extension i x p1) (Extension i' x' p1') =
   R1 i i' * R3 x x' * R2 p1 p1'\<close> |
\<open>pac_step_rel_assn R1 R2 _ _ _ = false\<close>

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


definition vars_llist :: \<open>llist_polynom \<Rightarrow> string set\<close> where
\<open>vars_llist  xs = \<Union>(set ` fst ` set xs)\<close>


definition check_addition_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> llist_polynom \<Rightarrow> string code_status nres\<close> where
\<open>check_addition_l spec A \<V> p q i r = do {
   let b = p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars_llist r \<subseteq> \<V>;
   if \<not>b
   then RETURN (error_msg i ((if p \<notin># dom_m A then error_msg_notin_dom p else []) @ (if q \<notin># dom_m A then error_msg_notin_dom p else []) @
      (if i \<in># dom_m A then error_msg_reused_dom p else [])))
   else do {
     ASSERT (p \<in># dom_m A);
     let p = the (fmlookup A p);
     ASSERT (q \<in># dom_m A);
     let q = the (fmlookup A q);
     pq \<leftarrow> add_poly_l (p, q);
     b \<leftarrow> weak_equality_l pq r;
     b' \<leftarrow> weak_equality_l r spec;
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


definition check_mult_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow>llist_polynom \<Rightarrow>  nat \<Rightarrow> llist_polynom \<Rightarrow> string code_status nres\<close> where
\<open>check_mult_l spec A \<V> p q i r = do {
    let b = p \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars_llist q \<subseteq> \<V>\<and> vars_llist r \<subseteq> \<V>;
    if \<not>b
    then do {
      c \<leftarrow> check_mult_l_dom_err (p \<notin># dom_m A) p (i \<in># dom_m A) i;
      RETURN (error_msg i c)}
    else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       pq \<leftarrow> mult_poly_full p q;
       b \<leftarrow> weak_equality_l pq r;
       b' \<leftarrow> weak_equality_l r spec;
       if b then (if b' then RETURN CFOUND else RETURN CSUCCESS) else do {
         c \<leftarrow> check_mult_l_mult_err p q pq r;
         RETURN (error_msg i c)
       }
     }
  }\<close>


definition check_del_l_dom_err :: \<open>nat \<Rightarrow> string nres\<close> where
  \<open>check_del_l_dom_err p = SPEC (\<lambda>_. True)\<close>



definition check_del_l :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> string code_status nres\<close> where
\<open>check_del_l spec A p = do {
    if p \<notin># dom_m A
    then do {
      c \<leftarrow> check_del_l_dom_err p;
      RETURN (error_msg p c)
      }
    else do {
         RETURN CSUCCESS
       }
  }\<close>


definition check_extension_l_dom_err :: \<open>nat \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_dom_err p = SPEC (\<lambda>_. True)\<close>


definition check_extension_l_no_new_var_err :: \<open>llist_polynom \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_no_new_var_err p = SPEC (\<lambda>_. True)\<close>

definition check_extension_l_new_var_multiple_err :: \<open>string \<Rightarrow> llist_polynom \<Rightarrow> string nres\<close> where
  \<open>check_extension_l_new_var_multiple_err v p = SPEC (\<lambda>_. True)\<close>

definition check_extension_l_side_cond_err
  :: \<open>string \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> llist_polynom \<Rightarrow> string nres\<close>
where
  \<open>check_extension_l_side_cond_err v p p' q = SPEC (\<lambda>_. True)\<close>

definition check_extension_l
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> string set \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynom \<Rightarrow> (string code_status) nres\<close>
where
\<open>check_extension_l spec A \<V> i v p = do {
  if i \<in># dom_m A \<or> v \<in> \<V>
  then do {
    c \<leftarrow> check_extension_l_dom_err i;
    RETURN (error_msg i c)
  } else do {
      let b = vars_llist p \<subseteq> \<V>;
      if \<not>b
      then do {
        c \<leftarrow> check_extension_l_new_var_multiple_err v p;
        RETURN (error_msg i c)
      }
      else do {
         p2 \<leftarrow> mult_poly_full p p;
         let up = map (\<lambda>(a, b). (a, -b)) p;
         q \<leftarrow> add_poly_l (p2, up);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p p q;
          RETURN (error_msg i c)
        }
      }
    }
  }\<close>


lemma check_extension_alt_def:
  \<open>check_extension A \<V> i v p \<ge> do {
    if i \<in># dom_m A \<or> v \<in> \<V>
    then RETURN (False)
    else do {
         b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> vars p \<subseteq> \<V>);
         if \<not>b
         then RETURN (False)
         else do {
           pq \<leftarrow> mult_poly_spec p p;
           up \<leftarrow> RETURN (-p);
           p \<leftarrow> add_poly_spec pq up;
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
      apply (auto simp flip: coeff_add simp: not_in_vars_coeff0
        Var.abs_eq Var\<^sub>0_def)
      apply (subst not_in_vars_coeff0)
      apply auto
      by (metis MPoly_Type.coeff_def lookup_single_eq monom.abs_eq monom.rep_eq)
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
      apply (auto simp flip: coeff_minus simp: not_in_vars_coeff0
        Var.abs_eq Var\<^sub>0_def)
      apply (subst not_in_vars_coeff0)
      using that unfolding q_def[symmetric] apply auto
      by (metis MPoly_Type.coeff_def lookup_single_eq monom.abs_eq monom.rep_eq)
  qed
  have [simp]: \<open>vars (p - Var ab) = vars (Var ab - p)\<close> for ab
    using vars_uminus[of \<open>p - Var ab\<close>]
    by simp
  show ?thesis
    by (auto 5 3 simp: check_extension_def weak_equality_def
      mult_poly_spec_def field_simps
      add_poly_spec_def power2_eq_square cong: if_cong
      intro!: intro_spec_refine[where R=Id, simplified]
      split: option.splits dest: ideal.span_add)
qed

(* Copy of WB_More_Refinement *)
lemma RES_RES_RETURN_RES: \<open>RES A \<bind> (\<lambda>T. RES (f T)) = RES (\<Union>(f ` A))\<close>
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma check_add_alt_def:
  \<open>check_add A \<V> p q i r \<ge>
    do {
     b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars r \<subseteq> \<V>);
     if \<not>b
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
  }\<close> (is \<open>_ \<ge> ?A\<close>)
proof -
  have check_add_alt_def: \<open>check_add A \<V> p q i r = do {
     b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars r \<subseteq> \<V>);
     if \<not>b then SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars r \<subseteq> \<V> \<and>
            the (fmlookup A p) + the (fmlookup A q) - r \<in>  ideal polynom_bool)
     else
       SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> q \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars r \<subseteq> \<V> \<and>
            the (fmlookup A p) + the (fmlookup A q) - r \<in>  ideal polynom_bool)}\<close>
   (is \<open>_ = ?B\<close>)
    by (auto simp: check_add_def RES_RES_RETURN_RES)
   have \<open>?A \<le> \<Down> Id (check_add A \<V> p q i r)\<close>
     apply refine_vcg
     apply ((auto simp: check_add_alt_def weak_equality_def
        add_poly_spec_def RES_RES_RETURN_RES summarize_ASSERT_conv
      cong: if_cong
      intro!:  ideal.span_zero;fail)+)
      done
   then show ?thesis
     unfolding check_add_alt_def[symmetric]
     by simp
qed

lemma check_mult_alt_def:
  \<open>check_mult A \<V> p q i r \<ge>
    do {
     b \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow> p \<in># dom_m A \<and> i \<notin># dom_m A \<and> vars q \<subseteq> \<V>  \<and> vars r \<subseteq> \<V>);
     if \<not>b
     then RETURN False
     else do {
       ASSERT (p \<in># dom_m A);
       let p = the (fmlookup A p);
       pq \<leftarrow> mult_poly_spec p q;
       p \<leftarrow> weak_equality pq r;
       RETURN p
     }
  }\<close>
  unfolding check_mult_def
  apply (rule refine_IdD)
  by refine_vcg
   (auto simp: check_mult_def weak_equality_def
      mult_poly_spec_def RES_RES_RETURN_RES
    intro!:  ideal.span_zero
      exI[of _ \<open>the (fmlookup A p) * q\<close>])

primrec insort_key_rel :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list" where
"insort_key_rel f x [] = [x]" |
"insort_key_rel f x (y#ys) =
  (if f x y then (x#y#ys) else y#(insort_key_rel f x ys))"


definition PAC_checker_l_step ::  \<open>_ \<Rightarrow> string code_status \<times> string set \<times> _ \<Rightarrow> (llist_polynom, string) pac_step \<Rightarrow> _\<close> where
  \<open>PAC_checker_l_step = (\<lambda>spec (st', \<V>, A) st. case st of
     Add _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (pac_res st);
        eq \<leftarrow> check_addition_l spec A \<V> (pac_src1 st) (pac_src2 st) (new_id st) r;
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
   | Mult _ _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (pac_res st);
         q \<leftarrow> full_normalize_poly (pac_mult st);
        eq \<leftarrow> check_mult_l spec A \<V> (pac_src1 st) q (new_id st) r;
        let _ = eq;
        if \<not>is_cfailed eq
        then RETURN (merge_cstatus st' eq,
          \<V>, fmupd (new_id st) r A)
        else RETURN (eq, \<V>, A)
   }
   | Extension _ _ _ \<Rightarrow>
       do {
         r \<leftarrow> full_normalize_poly (pac_res st);
        (eq) \<leftarrow> check_extension_l spec A \<V> (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
        then do {
          RETURN (st',
            insert (new_var st) \<V>, fmupd (new_id st) (insort_key_rel (\<lambda>(a, _) (c, _). term_order a c) ([new_var st], 1) (map (\<lambda>(a,b). (a, -b)) r)) A)}
        else RETURN (eq, \<V>, A)
   }
 )\<close>

lemma pac_step_rel_raw_def:
  \<open>\<langle>K, V, R\<rangle> pac_step_rel_raw = pac_step_rel_raw K V R\<close>
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


definition remap_polys_l :: \<open>llist_polynom \<Rightarrow> string set \<Rightarrow> (nat, llist_polynom) fmap \<Rightarrow>
   (_ code_status \<times> string set \<times> (nat, llist_polynom) fmap) nres\<close> where
  \<open>remap_polys_l spec = (\<lambda>\<V> A. do{
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (b, \<V>, A) \<leftarrow> FOREACH dom
     (\<lambda>i (b, \<V>,  A').
        if i \<in># dom_m A
        then  do {
          p \<leftarrow> full_normalize_poly (the (fmlookup A i));
          eq \<leftarrow> weak_equality_l p spec;
          \<V> \<leftarrow> RETURN(\<V> \<union> vars_llist (the (fmlookup A i)));
          RETURN(b \<or> eq, \<V>, fmupd i p A')
        } else RETURN (b, \<V>, A'))
     (False, \<V>, fmempty);
   RETURN (if b then CFOUND else CSUCCESS, \<V>, A)
 })\<close>

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


context poly_embed
begin

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, fully_unsorted_poly_rel O mset_poly_rel, var_rel\<rangle> pac_step_rel_raw)\<close>

abbreviation fmap_polys_rel where
  \<open>fmap_polys_rel \<equiv> \<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close>

lemma
  \<open>normalize_poly_p s0 s \<Longrightarrow>
        (s0, p) \<in> mset_poly_rel \<Longrightarrow>
        (s, p) \<in> mset_poly_rel\<close>
  by (auto simp: mset_poly_rel_def normalize_poly_p_poly_of_mset)

lemma vars_poly_of_vars:
  \<open>vars (poly_of_vars a :: int mpoly) \<subseteq> (\<phi> ` set_mset a)\<close>
  by (induction a)
   (auto simp: vars_mult_Var)

lemma vars_polynom_of_mset:
  \<open>vars (polynom_of_mset za) \<subseteq> \<Union>(image \<phi> ` (set_mset o fst) ` set_mset za)\<close>
  apply (induction za)
  using vars_poly_of_vars
  by (fastforce elim!: in_vars_addE simp: vars_mult_Const split: if_splits)+

lemma fully_unsorted_poly_rel_vars_subset_vars_llist:
  \<open>(A, B) \<in> fully_unsorted_poly_rel O mset_poly_rel \<Longrightarrow> vars B \<subseteq> \<phi> ` vars_llist A\<close>
  apply (auto simp: fully_unsorted_poly_list_rel_def mset_poly_rel_def
      set_rel_def var_rel_def br_def vars_llist_def list_rel_append2 list_rel_append1
      list_rel_split_right_iff list_mset_rel_def image_iff
    dest!: set_rev_mp[OF _ vars_polynom_of_mset]
    dest!: split_list)
    apply (auto dest!: multi_member_split simp: list_rel_append1
      unsorted_term_poly_list_rel_def eq_commute[of _ \<open>mset _\<close>]
      list_rel_split_right_iff list_rel_append2 list_rel_split_left_iff
      dest: arg_cong[of \<open>mset _\<close> \<open>add_mset _ _\<close> set_mset])
    done

lemma fully_unsorted_poly_rel_extend_vars:
  \<open>(A, B) \<in> fully_unsorted_poly_rel O mset_poly_rel \<Longrightarrow>
  (x1c, x1a) \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
   RETURN (x1c \<union> vars_llist A)
    \<le> \<Down> (\<langle>var_rel\<rangle>set_rel)
       (SPEC ((\<subseteq>) (x1a \<union> vars (B))))\<close>
  using fully_unsorted_poly_rel_vars_subset_vars_llist[of A B]
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
    V: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close>
  shows \<open>remap_polys_l spec \<V> A \<le>
     \<Down>(code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (remap_polys spec' \<V>' B)\<close>
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
            (\<lambda>p. the (fmlookup B x') - p \<in> More_Modules.ideal polynom_bool \<and>
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
     weak_equality_l p spec \<le> SPEC (\<lambda>eqa. eqa \<longrightarrow> pa = spec')\<close> for p pa
    using spec apply (auto simp: weak_equality_l_def weak_equality_spec_def
       list_mset_rel_def br_def
    dest: list_rel_term_poly_list_rel_same_rightD sorted_poly_list_relD)
    by (metis (mono_tags) mem_Collect_eq mset_poly_rel_def prod.simps(2)
      sorted_poly_list_relD)

  have emp: \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
    ((False, \<V>, fmempty), False, \<V>', fmempty) \<in> bool_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> for \<V> \<V>'
    by auto
  show ?thesis
    using assms
    unfolding remap_polys_l_def
      remap_polys_def prod.case
    apply (refine_rcg full_normalize_poly fmap_rel_fmupd_fmap_rel)
    subgoal
      by auto
    apply (rule 1)
    subgoal by auto
    apply (rule emp)
    subgoal
      using V by auto
    subgoal by auto
    subgoal by auto
    subgoal by (rule H')
    apply (rule fully_unsorted_poly_rel_extend_vars)
    subgoal by (auto intro!: fmap_rel_nat_the_fmlookup)
    subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by (auto intro!: fmap_rel_fmupd_fmap_rel)
    subgoal by auto
    subgoal by auto
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


lemma weak_equality_l_weak_equality_l'[refine]:
  \<open>weak_equality_l p q \<le> \<Down> bool_rel (weak_equality p' q')\<close>
  if \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
  for p p' q q'
  using that
  by (auto intro!: weak_equality_l_weak_equality_spec[THEN fref_to_Down_curry, THEN order_trans]
         ref_two_step'
         weak_equality_spec_weak_equality
      simp flip: conc_fun_chain)

lemma error_msg_ne_SUCCES[iff]:
  \<open>error_msg i m \<noteq> CSUCCESS\<close>
  \<open>error_msg i m \<noteq> CFOUND\<close>
  \<open>is_cfailed (error_msg i m)\<close>
  \<open>\<not>is_cfound (error_msg i m)\<close>
  by (auto simp: error_msg_def)

lemma sorted_poly_rel_vars_llist:
  \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel \<Longrightarrow>
   vars r' \<subseteq> \<phi> ` vars_llist r\<close>
  apply (auto simp: mset_poly_rel_def
      set_rel_def var_rel_def br_def vars_llist_def list_rel_append2 list_rel_append1
      list_rel_split_right_iff list_mset_rel_def image_iff sorted_poly_list_rel_wrt_def
    dest!: set_rev_mp[OF _ vars_polynom_of_mset]
    dest!: split_list)
    apply (auto dest!: multi_member_split simp: list_rel_append1
      term_poly_list_rel_def eq_commute[of _ \<open>mset _\<close>]
      list_rel_split_right_iff list_rel_append2 list_rel_split_left_iff
      dest: arg_cong[of \<open>mset _\<close> \<open>add_mset _ _\<close> set_mset])
    done


lemma check_addition_l_check_add:
  assumes \<open>(A, B) \<in> fmap_polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(p, p') \<in> Id\<close> \<open>(q, q') \<in> Id\<close> \<open>(i, i') \<in> nat_rel\<close>
    \<open>(\<V>', \<V>) \<in> \<langle>var_rel\<rangle>set_rel\<close>
  shows
    \<open>check_addition_l spec A \<V>' p q i r \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
       (is_cfound st \<longrightarrow> spec = r)} (check_add B \<V> p' q' i' r')\<close>
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
    unfolding check_addition_l_def
      check_not_equal_dom_err_def apply -
    apply (rule order_trans)
    defer
    apply (rule ref_two_step')
    apply (rule check_add_alt_def)
    apply refine_rcg
    subgoal
      by (drule sorted_poly_rel_vars_llist)
       (auto simp: set_rel_def var_rel_def br_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: weak_equality_l_def bind_RES_RETURN_eq)
    done
qed

lemma check_del_l_check_del:
  \<open>(A, B) \<in> fmap_polys_rel \<Longrightarrow> (x3, x3a) \<in> Id \<Longrightarrow> check_del_l spec A (pac_src1 (Del x3))
    \<le> \<Down> {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and> (b \<longrightarrow> st = CSUCCESS)} (check_del B (pac_src1 (Del x3a)))\<close>
  unfolding check_del_l_def check_del_def check_del_l_dom_err_def
  by (refine_vcg lhs_step_If RETURN_SPEC_refine)
    (auto simp: fmap_rel_nat_rel_dom_m bind_RES_RETURN_eq)

lemma check_mult_l_check_mult:
  assumes \<open>(A, B) \<in> fmap_polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
    \<open>(p, p') \<in> Id\<close> \<open>(i, i') \<in> nat_rel\<close> \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close>
  shows
    \<open>check_mult_l spec A \<V> p q i r \<le> \<Down>  {(st, b). (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
       (is_cfound st \<longrightarrow> spec = r)} (check_mult B \<V>' p' q' i' r')\<close>
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
    unfolding check_mult_l_def
      check_mult_l_mult_err_def check_mult_l_dom_err_def apply -
    apply (rule order_trans)
    defer
    apply (rule ref_two_step')
    apply (rule check_mult_alt_def)
    apply refine_rcg
    subgoal
      by (drule sorted_poly_rel_vars_llist)+
        (fastforce simp: set_rel_def var_rel_def br_def)
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by auto
    subgoal
      by (auto simp: weak_equality_l_def bind_RES_RETURN_eq)
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

lemma remove1_list_rel:
  \<open>(xs, ys) \<in> \<langle>R\<rangle> list_rel \<Longrightarrow>
  (a, b) \<in> R \<Longrightarrow>
  IS_RIGHT_UNIQUE R \<Longrightarrow>
  IS_LEFT_UNIQUE R \<Longrightarrow>
  (remove1 a xs, remove1 b ys) \<in> \<langle>R\<rangle>list_rel\<close>
  by (induction xs ys rule: list_rel_induct)
   (auto simp: single_valued_def IS_LEFT_UNIQUE_def)

lemma remove1_list_rel2:
  \<open>(xs, ys) \<in> \<langle>R\<rangle> list_rel \<Longrightarrow>
  (a, b) \<in> R \<Longrightarrow>
  (\<And>c. (a, c) \<in> R \<Longrightarrow> c = b) \<Longrightarrow>
  (\<And>c. (c, b) \<in> R \<Longrightarrow> c = a) \<Longrightarrow>
  (remove1 a xs, remove1 b ys) \<in> \<langle>R\<rangle>list_rel\<close>
  apply (induction xs ys rule: list_rel_induct)
  apply (simp (no_asm))
  by (smt list_rel_simp(4) remove1.simps(2))

lemma remove1_sorted_poly_rel_mset_poly_rel:
  assumes
    \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>([a], 1) \<in> set r\<close>
  shows
    \<open>(remove1 ([a], 1) r, r' - Var (\<phi> a))
          \<in> sorted_poly_rel O mset_poly_rel\<close>
proof -
   have [simp]: \<open>([a], {#a#}) \<in> term_poly_list_rel\<close>
     \<open>\<And>aa. ([a], aa) \<in> term_poly_list_rel \<longleftrightarrow> aa = {#a#}\<close>
     by (auto simp: term_poly_list_rel_def)
  have H:
    \<open>\<And>aa. ([a], aa) \<in> term_poly_list_rel \<Longrightarrow> aa = {#a#}\<close>
     \<open>\<And>aa. (aa, {#a#}) \<in> term_poly_list_rel \<Longrightarrow> aa = [a]\<close>
     by (auto simp: single_valued_def IS_LEFT_UNIQUE_def
       term_poly_list_rel_def)

  have [simp]: \<open>Const (1 :: int) = (1 :: int mpoly)\<close>
    by (simp add: Const.abs_eq Const\<^sub>0_one one_mpoly.abs_eq)
  have [simp]: \<open>sorted_wrt term_order (map fst r) \<Longrightarrow>
         sorted_wrt term_order (map fst (remove1 ([a], 1) r))\<close>
    by (induction r) auto
  have [intro]: \<open>distinct (map fst r) \<Longrightarrow> distinct (map fst (remove1 x r))\<close> for x
    apply (induction r) apply auto
    by (meson img_fst in_set_remove1D)
  have [simp]: \<open>(r, ya) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
         polynom_of_mset (mset ya) -  Var (\<phi> a) =
         polynom_of_mset (remove1_mset ({#a#}, 1) (mset ya))\<close> for ya
    using assms
     by (auto simp: list_rel_append1 list_rel_split_right_iff
       dest!: split_list)

  show ?thesis
    using assms
    apply (auto simp: mset_poly_rel_def sorted_poly_list_rel_wrt_def
      Collect_eq_comp' dest!: )
    apply (rule_tac b = \<open>remove1_mset ({#a#}, 1) za\<close> in relcompI)
    apply (auto)
    apply (rule_tac b = \<open>remove1 ({#a#}, 1) ya\<close> in relcompI)
    apply (auto intro!: remove1_list_rel2 intro: H
      simp: list_mset_rel_def br_def)
    done
qed

lemma remove1_sorted_poly_rel_mset_poly_rel_minus:
  assumes
    \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>([a], -1) \<in> set r\<close>
  shows
    \<open>(remove1 ([a], -1) r, r' + Var (\<phi> a))
          \<in> sorted_poly_rel O mset_poly_rel\<close>
proof -
   have [simp]: \<open>([a], {#a#}) \<in> term_poly_list_rel\<close>
     \<open>\<And>aa. ([a], aa) \<in> term_poly_list_rel \<longleftrightarrow> aa = {#a#}\<close>
     by (auto simp: term_poly_list_rel_def)
  have H:
    \<open>\<And>aa. ([a], aa) \<in> term_poly_list_rel \<Longrightarrow> aa = {#a#}\<close>
     \<open>\<And>aa. (aa, {#a#}) \<in> term_poly_list_rel \<Longrightarrow> aa = [a]\<close>
     by (auto simp: single_valued_def IS_LEFT_UNIQUE_def
       term_poly_list_rel_def)

  have [simp]: \<open>Const (1 :: int) = (1 :: int mpoly)\<close>
    by (simp add: Const.abs_eq Const\<^sub>0_one one_mpoly.abs_eq)
  have [simp]: \<open>sorted_wrt term_order (map fst r) \<Longrightarrow>
         sorted_wrt term_order (map fst (remove1 ([a], -1) r))\<close>
    by (induction r) auto
  have [intro]: \<open>distinct (map fst r) \<Longrightarrow> distinct (map fst (remove1 x r))\<close> for x
    apply (induction r) apply auto
    by (meson img_fst in_set_remove1D)
  have [simp]: \<open>(r, ya) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
         polynom_of_mset (mset ya) +  Var (\<phi> a) =
         polynom_of_mset (remove1_mset ({#a#}, -1) (mset ya))\<close> for ya
    using assms
     by (auto simp: list_rel_append1 list_rel_split_right_iff
       dest!: split_list)

  show ?thesis
    using assms
    apply (auto simp: mset_poly_rel_def sorted_poly_list_rel_wrt_def
      Collect_eq_comp' dest!: )
    apply (rule_tac b = \<open>remove1_mset ({#a#}, -1) za\<close> in relcompI)
    apply (auto)
    apply (rule_tac b = \<open>remove1 ({#a#}, -1) ya\<close> in relcompI)
    apply (auto intro!: remove1_list_rel2 intro: H
      simp: list_mset_rel_def br_def)
    done
qed


lemma insert_var_rel_set_rel:
  \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
  (yb, x2) \<in> var_rel \<Longrightarrow>
  (insert yb \<V>, insert x2 \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close>
  by (auto simp: var_rel_def set_rel_def)
  
lemma var_rel_set_rel_iff:
  \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel \<Longrightarrow>
  (yb, x2) \<in> var_rel \<Longrightarrow>
  yb \<in> \<V> \<longleftrightarrow> x2 \<in>  \<V>'\<close>
  using \<phi>_inj inj_eq by (fastforce simp: var_rel_def set_rel_def br_def)


lemma check_extension_l_check_extension:
  assumes \<open>(A, B) \<in> fmap_polys_rel\<close> and \<open>(r, r') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(i, i') \<in> nat_rel\<close> \<open>(\<V>, \<V>') \<in> \<langle>var_rel\<rangle>set_rel\<close> \<open>(x, x') \<in> var_rel\<close>
  shows
    \<open>check_extension_l spec A \<V> i x r \<le>
      \<Down>{((st), (b)).
        (\<not>is_cfailed st \<longleftrightarrow> b) \<and>
       (is_cfound st \<longrightarrow> spec = r)} (check_extension B \<V>' i' x' r')\<close>
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
  have [refine]:
    \<open>add_poly_l (p, q) \<le> \<Down> (sorted_poly_rel O mset_poly_rel) (add_poly_spec p' q')\<close>
    if \<open>(p, p') \<in> sorted_poly_rel O mset_poly_rel\<close>
      \<open>(q, q') \<in> sorted_poly_rel O mset_poly_rel\<close>
    for p p' q q'
    using that
    by (auto intro!: add_poly_l_add_poly_p'[THEN order_trans] ref_two_step'
         add_poly_p'_add_poly_spec
      simp flip: conc_fun_chain)

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
      mset_poly_rel_def comp_def polynom_of_mset_uminus)
   have [simp]: \<open>([], 0) \<in> sorted_poly_rel O mset_poly_rel\<close>
     by (auto simp: sorted_poly_list_rel_wrt_def
      mset_poly_rel_def list_mset_rel_def br_def
      intro!: relcompI[of _ \<open>{#}\<close>])
   show ?thesis
     unfolding check_extension_l_def
       check_extension_l_dom_err_def
       check_extension_l_no_new_var_err_def
       check_extension_l_new_var_multiple_err_def
       check_extension_l_side_cond_err_def
      apply (rule order_trans)
      defer
      apply (rule ref_two_step')
      apply (rule check_extension_alt_def)
      apply (refine_vcg )
      subgoal using assms(1,3,4,5)
        by (auto simp: var_rel_set_rel_iff)
      subgoal by auto
      subgoal using sorted_poly_rel_vars_llist[of \<open>r\<close> \<open>r'\<close>]
          assms
        by (force simp: set_rel_def var_rel_def br_def
          dest!: sorted_poly_rel_vars_llist)
      subgoal by auto
      subgoal by auto
      subgoal using assms by auto
      subgoal using assms by auto
      apply (rule uminus)
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      subgoal using assms by auto
      done
qed


lemma full_normalize_poly_diff_ideal:
  fixes dom
  assumes \<open>(p, p') \<in> fully_unsorted_poly_rel O mset_poly_rel\<close>
  shows
    \<open>full_normalize_poly p
    \<le> \<Down> (sorted_poly_rel O mset_poly_rel)
       (normalize_poly_spec p')\<close>
proof -
  obtain q where
    pq: \<open>(p, q) \<in> fully_unsorted_poly_rel\<close>  and qp':\<open>(q, p') \<in> mset_poly_rel\<close>
    using assms by auto
   show ?thesis
     unfolding normalize_poly_spec_def
     apply (rule full_normalize_poly_normalize_poly_p[THEN order_trans])
     apply (rule pq)
     unfolding conc_fun_chain[symmetric]
     by (rule ref_two_step', rule RES_refine)
       (use qp' in \<open>auto dest!: rtranclp_normalize_poly_p_poly_of_mset
            simp: mset_poly_rel_def ideal.span_zero\<close>)
qed

lemma PAC_checker_l_step_PAC_checker_step:
  assumes
    \<open>(Ast, Bst) \<in> code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> and
    \<open>(st, st') \<in> pac_step_rel\<close> and
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
  have [simp]: \<open>(merge_cstatus cst CSUCCESS, cst') \<in> code_status_status_rel\<close>
    using AB
    by (cases st)
      (auto simp: code_status_status_rel_def)

  show ?thesis
    using assms(2)
    unfolding PAC_checker_l_step_def PAC_checker_step_def Ast Bst prod.case
    apply (cases st; cases st'; simp only: p2rel_def pac_step.case
      pac_step_rel_raw_def mem_Collect_eq prod.case pac_step_rel_raw.simps)
    subgoal
      apply (refine_rcg normalize_poly_normalize_poly_spec
        check_mult_l_check_mult check_addition_l_check_add
        full_normalize_poly_diff_ideal)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto intro: \<V>)
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
        check_mult_l_check_mult check_addition_l_check_add
        full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]])
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal using AB by (auto simp: )
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
      apply (refine_rcg full_normalize_poly_diff_ideal
        check_extension_l_check_extension)
      subgoal using AB by auto
      subgoal using AB by auto
      subgoal using AB by (auto simp: )
      subgoal by (auto simp: )
      subgoal by (auto simp: )
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

lemma code_status_status_rel_discrim_iff:
  \<open>(x1a, x1c) \<in> code_status_status_rel \<Longrightarrow> is_cfailed x1a \<longleftrightarrow> is_failed x1c\<close>
  \<open>(x1a, x1c) \<in> code_status_status_rel \<Longrightarrow> is_cfound x1a \<longleftrightarrow> is_found x1c\<close>
  by (cases x1a; cases x1c; auto; fail)+

lemma PAC_checker_l_PAC_checker:
  assumes
    \<open>(A, B) \<in> \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>pac_step_rel\<rangle>list_rel\<close> and
    \<open>(spec, spec') \<in> sorted_poly_rel O mset_poly_rel\<close> and
    \<open>(b, b') \<in> code_status_status_rel\<close>
  shows
    \<open>PAC_checker_l spec A b st \<le> \<Down> (code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) (PAC_checker spec' B b' st')\<close>
proof -
  have [refine0]: \<open>(((b, A), st), (b', B), st') \<in> ((code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel) \<times>\<^sub>r  \<langle>pac_step_rel\<rangle>list_rel)\<close>
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

end

lemma less_than_char_of_char[code_unfold]:
  \<open>(x, y) \<in> less_than_char \<longleftrightarrow> (of_char x :: nat) < of_char y\<close>
  by (auto simp: less_than_char_def less_char_def)


lemmas [code] =
  add_poly_l'.simps[unfolded var_order_rel_def]

export_code add_poly_l' in SML module_name test

definition full_checker_l
  :: \<open>llist_polynom \<Rightarrow> (nat, llist_polynom) fmap \<Rightarrow> _ pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A) \<leftarrow> remap_polys_l spec' {} A;
    let \<V> = \<V> \<union> vars_llist spec;
    PAC_checker_l spec' (\<V>, A) b st
  }\<close>


context poly_embed
begin


term normalize_poly_spec
thm full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]]
abbreviation unsorted_fmap_polys_rel where
  \<open>unsorted_fmap_polys_rel \<equiv> \<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel\<close>

lemma full_checker_l_full_checker:
 assumes
    \<open>(A, B) \<in> unsorted_fmap_polys_rel\<close> and
    \<open>(st, st') \<in> \<langle>pac_step_rel\<rangle>list_rel\<close> and
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
    by (rule remap_polys_polynom_bool_remap_polys_change_all)

  show ?thesis
    unfolding full_checker_l_def full_checker_def
    apply (refine_rcg remap_polys_l_remap_polys
       full_normalize_poly_diff_ideal[unfolded normalize_poly_spec_def[symmetric]]
       PAC_checker_l_PAC_checker)
    subgoal
      using assms(3) .
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
  ((fully_unsorted_poly_rel O mset_poly_rel) \<times>\<^sub>r unsorted_fmap_polys_rel) \<times>\<^sub>r \<langle>pac_step_rel\<rangle>list_rel \<rightarrow>\<^sub>f
    \<langle>(code_status_status_rel \<times>\<^sub>r \<langle>var_rel\<rangle>set_rel \<times>\<^sub>r fmap_polys_rel)\<rangle>nres_rel\<close>
  apply (intro frefI nres_relI)
  using full_checker_l_full_checker by force

end

definition remap_polys_l2 :: \<open>llist_polynom \<Rightarrow> string set \<Rightarrow> (nat, llist_polynom) fmap \<Rightarrow> _ nres\<close> where
  \<open>remap_polys_l2 spec = (\<lambda>\<V> A. do{
   n \<leftarrow> upper_bound_on_dom A;
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

term find_undefined_var_l

fun find_undefined_var_l_only :: \<open>string set \<Rightarrow> llist_polynom \<Rightarrow> (string \<times> int) option\<close> where
  \<open>find_undefined_var_l_only \<V> [] = None\<close> |
  \<open>find_undefined_var_l_only \<V> (([x], n) # xs) =
    (if x \<notin> \<V> \<and> (n = 1 \<or> n = -1)
     then Some (x, n)
     else find_undefined_var_l_only \<V> xs)\<close> |
  \<open>find_undefined_var_l_only \<V> (_ # xs) =
    (find_undefined_var_l_only \<V> xs)\<close>

lemma find_undefined_var_l_only_spec:
  \<open>case find_undefined_var_l_only \<V> xs of
          None \<Rightarrow> True
       | Some (a, c) \<Rightarrow> (a \<notin> \<V> \<and>
         ((([a], 1) \<in> set xs \<and> c = 1) \<or>
          (([a], -1) \<in> set xs \<and> c = -1)))\<close>
   apply (induction \<V> xs rule: find_undefined_var_l_only.induct)
   apply (auto split: option.splits)
   done

definition find_undefined_var_l_fun where
  \<open>find_undefined_var_l_fun \<V> xs = do {
    c \<leftarrow> RETURN (find_undefined_var_l_only \<V> xs);
    case c of
      None \<Rightarrow> RETURN None
    | Some (a, i) \<Rightarrow> RETURN (Some (a, i, remove1 ([a], i) xs))
  }\<close>

lemma find_undefined_var_l_alt_def:
  \<open>find_undefined_var_l \<V> xs \<ge> find_undefined_var_l_fun \<V> xs\<close>
  unfolding find_undefined_var_l_def find_undefined_var_l_fun_def
  apply refine_vcg
  using find_undefined_var_l_only_spec[of \<V> xs]
  apply (auto)
  done

lemma find_undefined_var_l_only_RECT:
  \<open>RETURN (find_undefined_var_l_only \<V> xs) =
  REC\<^sub>T (\<lambda>f xs.
    case xs of
      [] \<Rightarrow> RETURN None
    | ([x], n) # xs \<Rightarrow>
        (if x \<notin> \<V> \<and> (n = 1 \<or> n = -1)
         then RETURN (Some (x, n))
         else f xs)
    | _ # xs \<Rightarrow> f xs)
    xs\<close>
  apply (subst eq_commute)
  apply (induction xs)
  subgoal
    apply (subst RECT_unfold)
    apply (refine_mono)
    apply auto
    done
  subgoal for a xs
    apply (subst RECT_unfold)
    apply (refine_mono)
    apply (cases a)
    apply (auto split: list.splits)
    done
 done

lemma find_undefined_var_l_only_alt_def:
  \<open>(RETURN oo find_undefined_var_l_only) =
  (\<lambda>\<V> xs. REC\<^sub>T (\<lambda>f xs.
    case xs of
      [] \<Rightarrow> RETURN None
    | ([x], n) # xs \<Rightarrow>
        (if x \<notin> \<V> \<and> (n = 1 \<or> n = -1)
         then RETURN (Some (x, n))
         else f xs)
    | _ # xs \<Rightarrow> f xs)
    xs)\<close>
  using find_undefined_var_l_only_RECT by fastforce

end
