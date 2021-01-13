theory EPAC_Efficient_Checker
  imports EPAC_Checker EPAC_Perfectly_Shared
begin
hide_const (open) PAC_Checker.full_checker_l
hide_fact (open) PAC_Checker.full_checker_l_def

type_synonym shared_poly = \<open>(nat list \<times> int) list\<close>

definition (in -) add_poly_l' where
  \<open>add_poly_l' _ = add_poly_l\<close>

definition (in -)add_poly_l_prep :: \<open>(nat,string)vars \<Rightarrow> llist_polynomial \<times> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>add_poly_l_prep \<D> = REC\<^sub>T
  (\<lambda>add_poly_l (p, q).
  case (p,q) of
    (p, []) \<Rightarrow> RETURN p
    | ([], q) \<Rightarrow> RETURN q
    | ((xs, n) # p, (ys, m) # q) \<Rightarrow> do {
    comp \<leftarrow> perfect_shared_term_order_rel \<D> xs ys;
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

lemma add_poly_alt_def[unfolded conc_Id id_apply]:
  fixes xs ys :: llist_polynomial
  assumes \<open>\<Union>(set ` (fst`set xs)) \<subseteq> set_mset \<D>\<close>  \<open>\<Union>(set ` fst ` set ys) \<subseteq> set_mset \<D>\<close>
  shows \<open>add_poly_l_prep \<D> (xs, ys) \<le> \<Down> Id (add_poly_l' \<D> (xs, ys))\<close>
proof -
  let ?Rx = \<open>{(xs', ys'). (xs', ys') \<in> \<langle>Id\<rangle> list_rel \<and> (\<exists>xs\<^sub>0. xs = xs\<^sub>0 @ xs')}\<close>
  let ?Ry = \<open>{(xs', ys'). (xs', ys') \<in> \<langle>Id\<rangle> list_rel \<and> (\<exists>xs\<^sub>0. ys = xs\<^sub>0 @ xs')}\<close>
   have [refine0]: \<open>((xs, ys), xs, ys) \<in> ?Rx \<times>\<^sub>r ?Ry\<close>
     by auto
   have H: \<open>(x1c, x1a) \<in> \<langle>Id\<rangle>list_rel  \<Longrightarrow> (x1c, x1a) \<in> \<langle>Id\<rangle>list_rel\<close> for x1c x1a
     by auto
   have [intro!]: \<open>f \<le> f' \<Longrightarrow> do {a \<leftarrow> f; P a} \<le> do {a \<leftarrow> f'; P a}\<close> for f f' :: \<open>_ nres\<close> and P
     unfolding pw_bind_inres pw_bind_nofail pw_le_iff
     by blast
   show ?thesis
     using assms
     unfolding add_poly_l'_def add_poly_l_def add_poly_l_prep_def
    apply (refine_vcg perfect_shared_term_order_rel_spec[THEN order_trans])
    apply (rule H)
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal
      apply (rule specify_left)
      apply (rule perfect_shared_term_order_rel_spec[unfolded conc_Id id_apply])
      subgoal by auto
      subgoal by auto
      subgoal premises p for comp
        supply [intro!] = p(3)[unfolded conc_Id id_apply]
        using p(1,2,4-)
        using ordered.exhaust[of comp False]
        by (auto simp: lexord_irreflexive dest: term_order_rel_irreflexive; fail)+         
      done
    done
qed

definition (in -)normalize_poly_shared
  :: \<open>(nat,string) vars \<Rightarrow> llist_polynomial \<Rightarrow>
  (bool \<times> llist_polynomial) nres\<close>
  where
  \<open>normalize_poly_shared \<A> xs = do {
  xs \<leftarrow> full_normalize_poly xs;
  import_poly_no_new \<A> xs
  }\<close>

definition normalize_poly_sharedS
  :: \<open>(nat,string) shared_vars \<Rightarrow> llist_polynomial \<Rightarrow>
        (bool \<times> shared_poly) nres\<close>
where
  \<open>normalize_poly_sharedS \<A> xs = do {
    xs \<leftarrow> full_normalize_poly xs;
    import_poly_no_newS \<A> xs
  }\<close>

definition (in -) mult_monoms_prep :: \<open>(nat,string)vars \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list nres\<close> where
  \<open>mult_monoms_prep \<D> xs ys = REC\<^sub>T (\<lambda>f (xs, ys).
 do {
    if xs = [] then RETURN ys
    else if ys = [] then RETURN xs
    else do {
      ASSERT(xs \<noteq> [] \<and> ys \<noteq> []);
      comp \<leftarrow> perfect_shared_var_order \<D> (hd xs) (hd ys);
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

lemma (in -) mult_monoms_prep_mult_monoms:
  assumes \<open>set xs \<subseteq> set_mset \<V>\<close> \<open>set ys \<subseteq> set_mset \<V>\<close>
  shows \<open>mult_monoms_prep \<V> xs ys \<le> \<Down>Id (SPEC ((=) (mult_monoms xs ys)))\<close>
proof -
  have H: \<open>f \<le> RES p \<Longrightarrow> (\<And>x. x \<in> p \<Longrightarrow> (g x) \<in> Q) \<Longrightarrow> do {x \<leftarrow> f; RETURN (g x)} \<le> RES Q\<close> for f p g Q
    by (meson bind_le_nofailI le_RES_nofailI nres_order_simps(21) order.trans)
  have [dest]: \<open> (x, y) \<in> var_order_rel \<Longrightarrow>
    (y, x) \<in> var_order_rel \<Longrightarrow> x = y\<close> for x y
     by (meson transE trans_var_order_rel var_order_rel_antisym)

  have [dest]: \<open> xa \<noteq> UNKNOWN \<Longrightarrow> xa \<noteq> GREATER \<Longrightarrow> xa \<noteq> LESS \<Longrightarrow> xa = EQUAL \<close> for xa
    by (cases xa) auto
  show ?thesis
   using assms
    apply (induction xs ys rule:mult_monoms.induct)
    subgoal
      unfolding mult_monoms_prep_def
      by (subst RECT_unfold, refine_mono) auto
    subgoal
      unfolding mult_monoms_prep_def
      by (subst RECT_unfold, refine_mono) auto
    subgoal
      apply (subst mult_monoms_prep_def)
      apply (subst RECT_unfold, refine_mono)
      apply (subst mult_monoms_prep_def[symmetric])+
        apply (simp only: prod.simps)
        apply (refine_vcg perfect_shared_term_order_rel_spec[THEN order_trans]
          perfect_shared_var_order_spec[THEN order_trans])
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by auto
       subgoal by (auto intro!: H)
       done
    done
qed
definition mult_monoms_prop :: \<open>(nat,string)vars\<Rightarrow> llist_polynomial \<Rightarrow>  _ \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>mult_monoms_prop = (\<lambda>\<V> qs (p, m) b. nfoldli qs (\<lambda>_. True) (\<lambda>(q, n) b. do {pq \<leftarrow> mult_monoms_prep \<V> p q; RETURN ((pq, m * n) # b)}) b)\<close>

definition mult_poly_raw_prop :: \<open>(nat,string) vars\<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>mult_poly_raw_prop \<V> p q = nfoldli p (\<lambda>_. True) (mult_monoms_prop \<V> q) []\<close>

lemma mult_monoms_prop_mult_monomials:
  assumes \<open>vars_llist qs \<subseteq> set_mset \<V>\<close> \<open>set (fst m) \<subseteq> set_mset \<V>\<close>
  shows \<open>mult_monoms_prop \<V> qs m b \<le> \<Down>{(xs, ys). mset xs = mset ys} (RES{map (mult_monomials m) qs @ b})\<close>
    using assms
  unfolding mult_monoms_prop_def
  apply (cases m)
  apply (induction qs arbitrary: b)
  subgoal by (auto intro!: RETURN_RES_refine)
  subgoal for a qs aa b ba
    apply (cases a)
    apply (simp only: prod.simps nfoldli_simps(2) if_True nres_monad3 nres_monad1)
    apply (refine_vcg mult_monoms_prep_mult_monoms[THEN order_trans])
    subgoal by auto
    subgoal by auto
    subgoal premises p
      supply [intro!] = p(1)[THEN order_trans]
      using p(2-)
      by (auto simp: conc_fun_RES mult_monomials_def)
    done
  done


lemma mult_poly_raw_prop_mult_poly_raw:
  assumes \<open>vars_llist qs \<subseteq> set_mset \<V>\<close> \<open>vars_llist ps \<subseteq> set_mset \<V>\<close>
  shows \<open>mult_poly_raw_prop \<V> ps qs \<le>
       (SPEC (\<lambda>c. (c, PAC_Polynomials_Operations.mult_poly_raw ps qs) \<in> {(xs, ys). mset xs = mset ys}))\<close>
proof -
  have [simp]: \<open>foldl (\<lambda>b x. map (mult_monomials x) qs @ b) b ps = foldl (\<lambda>b x. map (mult_monomials x) qs @ b) [] ps @ b\<close>
    if \<open>NO_MATCH [] b\<close> for qs ps b
    apply (induction ps arbitrary: b)
      apply simp
    by (metis (no_types, lifting) append_assoc foldl_Cons self_append_conv)

  have H: \<open>nfoldli ps (\<lambda>_. True) (mult_monoms_prop \<V> qs) b0
    \<le> \<Down> {(xs, ys). mset xs = mset ys} (RES {foldl (\<lambda>b x. map (mult_monomials x) qs @ b) b0 ps})\<close> for b0
    using assms
    apply (induction ps arbitrary: b0)
    subgoal by (auto intro!: RETURN_RES_refine)
    subgoal premises p
      supply [intro!] = p(1)[THEN order_trans]
      using p(2-)
      apply (simp only: prod.simps nfoldli_simps(2) if_True nres_monad3 nres_monad1)
      apply (refine_rcg mult_monoms_prop_mult_monomials)
      apply auto
      apply (rule specify_left)
      apply (subst RES_SPEC_eq[symmetric])
      apply (rule mult_monoms_prop_mult_monomials[unfolded conc_fun_RES])
      apply (auto simp: conc_fun_RES)
      done
    done

  show ?thesis
    unfolding mult_poly_raw_def mult_poly_raw_prop_def
    by (rule H[THEN order_trans]) (auto simp: conc_fun_RES)
qed

definition (in -) mult_poly_full_prop :: \<open>_\<close> where
\<open>mult_poly_full_prop \<V> p q = do {
  pq \<leftarrow> mult_poly_raw_prop \<V> p q;
  ASSERT(vars_llist pq \<subseteq> vars_llist p \<union> vars_llist q);
  normalize_poly pq
  }\<close>

lemma vars_llist_mset_eq: \<open>mset p = mset q \<Longrightarrow> vars_llist p = vars_llist q\<close>
  by (auto simp: vars_llist_def dest!: mset_eq_setD)
lemma mult_poly_full_prop_mult_poly_full:
  assumes \<open>vars_llist qs \<subseteq> set_mset \<V>\<close> \<open>vars_llist ps \<subseteq> set_mset \<V>\<close>
    \<open>(ps, ps') \<in> Id\<close> \<open>(qs, qs') \<in> Id\<close>
  shows \<open>mult_poly_full_prop \<V> ps qs \<le> \<Down>Id (mult_poly_full ps' qs')\<close>
proof -
  have [refine0]: \<open>sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close>
    if \<open>mset p= mset p'\<close> for p p'
    using that
    unfolding sort_poly_spec_def
    by auto
  have  H: \<open>x \<in> A \<Longrightarrow> x= x' \<Longrightarrow> x' \<in> A\<close> for x x' A
    by auto
  show ?thesis
    using assms
    unfolding mult_poly_full_prop_def mult_poly_full_def normalize_poly_def
    apply (refine_vcg mult_poly_raw_prop_mult_poly_raw)
    apply (rule H[of _ \<open>{(xs, ys). mset xs = mset ys}\<close>], assumption)
    subgoal by auto
    subgoal by (force dest: vars_llist_mset_eq vars_llist_mult_poly_raw[THEN set_mp])
    subgoal by auto
    subgoal by auto
    done
qed

definition (in -) linear_combi_l_prep2 where
  \<open>linear_combi_l_prep2 i A \<V> xs = do {
    ASSERT(linear_combi_l_pre i A (set_mset \<V>) xs);
    WHILE\<^sub>T
      (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
      (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         let (q\<^sub>0 :: llist_polynomial, i) = hd xs;
         if (i \<notin># dom_m A \<or> \<not>(vars_llist q\<^sub>0 \<subseteq> set_mset \<V>))
         then do {
           err \<leftarrow> check_linear_combi_l_dom_err q\<^sub>0 i;
           RETURN (p, xs, error_msg i err)
         } else do {
           ASSERT(fmlookup A i \<noteq> None);
           let r = the (fmlookup A i);
           ASSERT(vars_llist r \<subseteq> set_mset \<V>);
           if q\<^sub>0 = [([],1)] then do {
             pq \<leftarrow> add_poly_l_prep \<V> (p, r);
             RETURN (pq, tl xs, CSUCCESS)
          } else do {
             (_, q) \<leftarrow> normalize_poly_shared \<V> (q\<^sub>0);
             ASSERT(vars_llist q \<subseteq> set_mset \<V>);
             pq \<leftarrow> mult_poly_full_prop \<V> q r;
             ASSERT(vars_llist pq \<subseteq> set_mset \<V>);
             pq \<leftarrow> add_poly_l_prep \<V> (p, pq);
             RETURN (pq, tl xs, CSUCCESS)
          }
         }
      })
     ([], xs, CSUCCESS)
    }\<close>
lemma (in -) import_poly_no_new_spec:
    \<open>import_poly_no_new \<V> xs \<le> \<Down>Id (SPEC(\<lambda>(b, xs'). (\<not>b \<longrightarrow> xs = xs') \<and> (\<not>b \<longleftrightarrow> vars_llist xs \<subseteq> set_mset \<V>)))\<close>
  unfolding import_poly_no_new_def
  apply (refine_vcg WHILET_rule[where I = \<open> \<lambda>(b, xs', ys'). (\<not>b \<longrightarrow> xs = ys' @ xs')  \<and>
    (\<not>b \<longrightarrow> vars_llist ys' \<subseteq> set_mset \<V>) \<and>
    (b \<longrightarrow> \<not>vars_llist xs \<subseteq> set_mset \<V>)\<close>  and R = \<open>measure (\<lambda>(b, xs, _). (if b then 0 else 1) + length xs)\<close>]
    import_monom_no_new_spec[THEN order_trans])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (clarsimp simp add: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  done

lemma linear_combi_l_prep2_linear_combi_l:
  assumes \<V>: \<open>(\<V>,\<V>') \<in> {(x, y). y = set_mset x}\<close>\<open>(i,i')\<in>nat_rel\<close>\<open>(A,A')\<in>Id\<close>\<open>(xs,xs')\<in>Id\<close>
  shows \<open>linear_combi_l_prep2 i A \<V> xs \<le> \<Down>Id (linear_combi_l i' A' \<V>' xs')\<close>
proof -
  have H1: \<open>(if p \<or> q then P else Q) = (if p then P else if q then P else Q)\<close> for p q P Q
    by auto
  have [intro!]: \<open>check_linear_combi_l_dom_err x1e x2e \<le> \<Down> Id (check_linear_combi_l_dom_err x1e x2e)\<close>
    for x1e x2e
    by auto
  have linear_combi_l_alt_def:
    \<open>linear_combi_l i A \<V> xs = do {
      ASSERT(linear_combi_l_pre i A \<V> xs);
      WHILE\<^sub>T
        (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
        (\<lambda>(p, xs, _). do {
         ASSERT(xs \<noteq> []);
         ASSERT (vars_llist p \<subseteq> \<V>);
         let (q :: llist_polynomial, i) = hd xs;
          if (i \<notin># dom_m A \<or> \<not>(vars_llist q \<subseteq> \<V>))
          then do {
            err \<leftarrow> check_linear_combi_l_dom_err q i;
            RETURN (p, xs, error_msg i err)
            }
          else do {
          ASSERT(fmlookup A i \<noteq> None);
          let r = the (fmlookup A i);
          ASSERT (vars_llist r \<subseteq> \<V>);
          if q = [([], 1)]
          then do {
            pq \<leftarrow> add_poly_l' \<V>' (p, r);
            RETURN (pq, tl xs, CSUCCESS)
          }
          else  do {
            q \<leftarrow> full_normalize_poly q;
            ASSERT (vars_llist q \<subseteq> \<V>);
            let q = q;
            pq \<leftarrow> mult_poly_full q r;
            ASSERT (vars_llist pq \<subseteq> \<V>);
            pq \<leftarrow> add_poly_l' \<V>' (p, pq);
            RETURN (pq, tl xs, CSUCCESS)
          }
        }
       })
    ([], xs, CSUCCESS)
    }\<close> for i A \<V> xs
    unfolding Let_def linear_combi_l_def add_poly_l'_def by auto
  have H: \<open>P = Q \<Longrightarrow> P \<le>\<Down>Id Q\<close> for P Q
    by auto
  have [refine0]: \<open>\<Down> Id (SPEC (\<lambda>(b, xs'). (\<not> b \<longrightarrow> xa = xs') \<and> (\<not> b) = (vars_llist xa \<subseteq> set_mset \<V>)))
    \<le> SPEC (\<lambda>c. (c, q) \<in> {((b, c), d). \<not>b \<and> c = d \<and> d = q})\<close>
    if \<open>vars_llist xa \<subseteq> set_mset \<V>\<close> \<open>xa = q\<close>
    for xa \<V> q
    using that by auto
  show ?thesis
    using assms
    unfolding linear_combi_l_prep2_def linear_combi_l_alt_def normalize_poly_shared_def nres_monad3
    apply (refine_rcg import_poly_no_new_spec[THEN order_trans]
      mult_poly_full_prop_mult_poly_full[THEN order_trans]
      add_poly_alt_def[THEN order_trans])
    subgoal using \<V> by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using \<V> by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: vars_llist_def)
    subgoal by auto
    subgoal by (auto simp: vars_llist_def)
    subgoal by (auto simp: vars_llist_def)
    apply (rule H)
    subgoal by (auto simp: add_poly_l'_def)
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal using \<V> by auto
    subgoal by auto
    apply (solves auto)[]
    apply (solves auto)[]
    apply (rule H)
    subgoal by auto
    subgoal using \<V> by (auto dest!: split_list)
    subgoal using \<V> by (auto dest!: split_list)
    subgoal by (auto simp: vars_llist_def)
    apply (rule H)
    subgoal by (auto simp: add_poly_l'_def)
    subgoal by auto
    done
qed

definition check_linear_combi_l_prop where
  \<open>check_linear_combi_l_prop spec A \<V> i xs r = do {
  (mem_err, r) \<leftarrow> import_poly_no_new \<V> r;
  if mem_err \<or> i \<in># dom_m A \<or> xs = []
  then do {
    err \<leftarrow> check_linear_combi_l_pre_err i (i \<in># dom_m A) (xs = []) (mem_err);
    RETURN (error_msg i err, r)
  }
  else do {
    (p, _, err) \<leftarrow> linear_combi_l_prep2 i A \<V> xs;
    if (is_cfailed err)
    then do {
      RETURN (err, r)
    }
    else do {
      b \<leftarrow> weak_equality_l p r;
      b' \<leftarrow> weak_equality_l r spec;
      if b then (if b' then RETURN (CFOUND, r) else RETURN (CSUCCESS, r)) else do {
        c \<leftarrow> check_linear_combi_l_mult_err p r;
        RETURN (error_msg i c, r)
      }
    }
  }}\<close>

lemma check_linear_combi_l_prop_check_linear_combi_l:
  assumes \<open>(\<V>,\<V>') \<in> {(x, y). y = set_mset x}\<close> \<open>(A, A') \<in> Id\<close> \<open>(i,i')\<in>nat_rel\<close> \<open>(xs,xs')\<in>Id\<close>\<open>(r,r')\<in>Id\<close>
       \<open>(spec,spec')\<in>Id\<close>
  shows \<open>check_linear_combi_l_prop spec A \<V> i xs r \<le>
    \<Down>{((b,r'), b'). b=b' \<and> (\<not>is_cfailed b \<longrightarrow> r=r')} (check_linear_combi_l spec' A' \<V>' i' xs' r')\<close>
proof -
  have [refine]: \<open>import_poly_no_new \<V> r \<le> \<Down> {((mem, r'), b). (b=mem) \<and> (\<not>b \<longrightarrow> r'=r \<and> vars_llist r \<subseteq> set_mset \<V>)} (RES UNIV)\<close>
    apply (rule order_trans)
    apply (rule import_poly_no_new_spec)
    apply (auto simp: conc_fun_RES)
    done
  have H: \<open>f=g \<Longrightarrow> f \<le> \<Down>Id g\<close> for f g
    by auto

  show ?thesis
    using assms
    unfolding check_linear_combi_l_prop_def check_linear_combi_l_def
    apply (refine_vcg linear_combi_l_prep2_linear_combi_l)
    subgoal using assms by auto
    apply (rule H)
    subgoal by (auto simp: check_linear_combi_l_pre_err_def)
    subgoal by (auto simp:error_msg_def)
    subgoal using assms by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    done
qed

definition (in -)check_extension_l2_prop
  :: \<open>_ \<Rightarrow> _ \<Rightarrow> string multiset \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> llist_polynomial \<Rightarrow> (string code_status \<times> llist_polynomial \<times> string multiset \<times> string) nres\<close>
where
\<open>check_extension_l2_prop spec A \<V> i v p = do {
  (pre, nonew, mem, mem', p, \<V>, v) \<leftarrow> do {
      let pre = i \<notin># dom_m A \<and> v \<notin> set_mset \<V>;
      let b = vars_llist p \<subseteq> set_mset \<V>;
      (mem, p, \<V>) \<leftarrow> import_poly \<V> p;
      (mem', \<V>, v) \<leftarrow> if b \<and> pre \<and> \<not> alloc_failed mem then import_variable v \<V> else RETURN (mem, \<V>, v);
      RETURN (pre \<and> \<not>alloc_failed mem \<and> \<not> alloc_failed mem', b, mem, mem', p, \<V>, v)
   };
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
         ASSERT(vars_llist p \<subseteq> set_mset \<V>);
         p2 \<leftarrow>  mult_poly_full_prop \<V> p p;
         ASSERT(vars_llist p2 \<subseteq> set_mset \<V>);
         let p'' = map (\<lambda>(a,b). (a, -b)) p;
         ASSERT(vars_llist p'' \<subseteq> set_mset \<V>);
         q \<leftarrow> add_poly_l_prep \<V> (p2, p'');
         ASSERT(vars_llist q \<subseteq> set_mset \<V>);
         eq \<leftarrow> weak_equality_l q [];
         if eq then do {
           RETURN (CSUCCESS, p, \<V>, v)
         } else do {
          c \<leftarrow> check_extension_l_side_cond_err v p q;
          RETURN (error_msg i c, [], \<V>, v)
        }
      }
    }
  }\<close>

lemma check_extension_l2_prop_check_extension_l2:
  assumes \<open>(\<V>,\<V>') \<in> {(x, y). y = set_mset x}\<close> \<open>(spec, spec') \<in> Id\<close>  \<open>(A, A') \<in> Id\<close> \<open>(i,i') \<in> nat_rel\<close> \<open>(v, v') \<in> Id\<close> \<open>(p, p') \<in> Id\<close>
  shows \<open>check_extension_l2_prop spec A \<V> i v p \<le>\<Down>{((err, q, \<A>, va), b). (b = err) \<and> (\<not>is_cfailed err \<longrightarrow> q=p \<and> v=va \<and> set_mset \<A> = insert v \<V>')}
    (check_extension_l2 spec' A' \<V>' i' v' p')\<close>
proof -

  have G[refine]: \<open>do {
   (mem, pa, \<V>') \<leftarrow> import_poly \<V> p;
   (mem', \<V>', va) \<leftarrow> if vars_llist p \<subseteq> set_mset \<V> \<and> (i \<notin># dom_m A \<and> v \<notin># \<V>) \<and> \<not> alloc_failed mem
     then import_variable v \<V>' else RETURN (mem, \<V>', v);
   RETURN
    ((i \<notin># dom_m A \<and> v \<notin># \<V>) \<and> \<not> alloc_failed mem \<and> \<not> alloc_failed mem',
     vars_llist p \<subseteq> set_mset \<V>, mem, mem', pa, \<V>', va)
    } \<le> \<Down> {((pre, nonew, mem, mem', p', \<A>, va), b). (b=pre)\<and>  (b \<longrightarrow> \<not>alloc_failed mem \<and> \<not>alloc_failed mem') \<and>
    (b \<and> nonew \<longrightarrow> (p'=p \<and> set_mset \<A> = set_mset \<V> \<union> vars_llist p \<union> {v} \<and> va = v))  \<and>
       ((nonew \<longleftrightarrow> vars_llist p \<subseteq> set_mset \<V>))}
    (SPEC (\<lambda>b. b \<longrightarrow> i' \<notin># dom_m A' \<and> v' \<notin> \<V>'))\<close>
    using assms unfolding conc_fun_RES import_variable_def nres_monad3
    apply (subst (2) RES_SPEC_eq)
    apply (refine_vcg import_poly_spec[THEN order_trans])
    apply (clarsimp simp: )
    apply (rule conjI impI)
    apply (refine_vcg import_poly_spec[THEN order_trans])
    apply (auto simp: vars_llist_def)[]
    apply (auto simp: vars_llist_def)[]
    apply (auto simp: vars_llist_def)[]
    done

  have H: \<open>f=g \<Longrightarrow> f \<le> \<Down>Id g\<close> for f g
    by auto
  show ?thesis
    using assms
    unfolding check_extension_l2_prop_def check_extension_l2_def
    apply (refine_vcg mult_poly_full_prop_mult_poly_full add_poly_alt_def[unfolded add_poly_l'_def, THEN order_trans]
      )
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by (simp add: error_msg_def)
    subgoal by auto
    apply (rule H)
    subgoal by (auto simp: check_extension_l_new_var_multiple_err_def)
    subgoal by (simp add: error_msg_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto dest: split_list_first simp: vars_llist_def)
    subgoal by (auto simp: vars_llist_def)
    apply (rule H)
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest!: split_list_first simp: remove1_append)
    apply (rule H)
    subgoal by (auto simp: check_extension_l_new_var_multiple_err_def check_extension_l_side_cond_err_def)
    subgoal by (auto simp: error_msg_def)
    done
qed


definition PAC_checker_l_step_prep ::  \<open>_ \<Rightarrow> string code_status \<times> string multiset \<times> _ \<Rightarrow> (llist_polynomial, string, nat) pac_step \<Rightarrow> _\<close> where
  \<open>PAC_checker_l_step_prep = (\<lambda>spec (st', \<V>, A) st. do {
    ASSERT (PAC_checker_l_step_inv spec st' (set_mset \<V>) A);
    ASSERT (\<not>is_cfailed st');
    case st of
     CL _ _ _ \<Rightarrow>
       do {
        r \<leftarrow> full_normalize_poly (pac_res st);
        (eq, r) \<leftarrow> check_linear_combi_l_prop spec A \<V> (new_id st) (pac_srcs st) r;
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
        (eq, r, \<V>, v) \<leftarrow> check_extension_l2_prop spec A (\<V>) (new_id st) (new_var st) r;
        if \<not>is_cfailed eq
      then do {
        r \<leftarrow> add_poly_l_prep \<V> ([([v], -1)], r);
        RETURN (st', \<V>, fmupd (new_id st) r A)
        }
        else RETURN (eq, \<V>, A)
     }}
          )\<close>

lemma PAC_checker_l_step_prep_PAC_checker_l_step:
  assumes \<open>(state, state') \<in> {((st, \<V>, A), (st', \<V>', A')). (st,st')\<in>Id \<and> (A,A')\<in>Id \<and> (\<not>is_cfailed st \<longrightarrow> (\<V>,\<V>')\<in> {(x, y). y = set_mset x})}\<close>
    \<open>(spec,spec')\<in>Id\<close>
    \<open>(step,step')\<in>Id\<close>
  shows \<open>PAC_checker_l_step_prep spec state step \<le>
    \<Down>{((st, \<V>, A), (st', \<V>', A')). (st,st')\<in>Id \<and> (A,A')\<in>Id \<and> (\<not>is_cfailed st \<longrightarrow> (\<V>,\<V>')\<in> {(x, y). y = set_mset x})}
    (PAC_checker_l_step spec' state' step')\<close>
proof -
  have H: \<open>f=g \<Longrightarrow> f \<le> \<Down>Id g\<close> for f g
    by auto
  show ?thesis
    using assms apply -
    unfolding PAC_checker_l_step_prep_def PAC_checker_l_step_def
    apply (simp only: split: prod.splits)
    apply (simp only: split:prod.splits pac_step.splits)
    apply (intro conjI impI allI)
    subgoal
      apply (refine_rcg check_linear_combi_l_prop_check_linear_combi_l)
      subgoal using assms by auto
      subgoal by auto
      apply (rule H)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      apply (refine_rcg check_extension_l2_prop_check_extension_l2 add_poly_alt_def[unfolded add_poly_l'_def, THEN order_trans])
      subgoal by auto
      subgoal by auto
      apply (rule H)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by (auto simp add: vars_llist_def)
      apply (rule H)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal
      apply (refine_rcg)
      subgoal by auto
      subgoal by auto
      apply (rule H)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal by auto
      done
    done
qed

definition (in -) remap_polys_l2_with_err
  :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, string) vars \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow>
   (string code_status \<times> (nat, string) vars \<times> (nat, llist_polynomial) fmap) nres\<close> where
  \<open>remap_polys_l2_with_err spec' spec0 = (\<lambda>(\<V>:: (nat, string) vars) A. do{
   ASSERT(vars_llist spec' \<subseteq> vars_llist spec0);
   dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   (mem, \<V>) \<leftarrow> SPEC(\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow> set_mset \<V>' = set_mset \<V> \<union> vars_llist spec0);
   (mem', spec, \<V>) \<leftarrow> if \<not>alloc_failed mem then import_poly \<V> spec' else SPEC(\<lambda>_. True);
   failed \<leftarrow> SPEC(\<lambda>b::bool. alloc_failed mem \<or> alloc_failed mem' \<longrightarrow> b);
   ASSERT(\<not>failed \<longrightarrow> spec = spec');
   if failed
   then do {
      c \<leftarrow> remap_polys_l_dom_err;
      SPEC (\<lambda>(mem, _, _). mem = error_msg (0::nat) c)
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
              p \<leftarrow> full_normalize_poly p;
              eq  \<leftarrow> weak_equality_l p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A)
  }})\<close>

lemma remap_polys_l_with_err_alt_def:
  \<open>remap_polys_l_with_err spec spec0 = (\<lambda>\<V> A. do{
  ASSERT (remap_polys_l_with_err_pre spec spec0 \<V> A);
  dom \<leftarrow> SPEC(\<lambda>dom. set_mset (dom_m A) \<subseteq> dom \<and> finite dom);
   \<V> \<leftarrow> RETURN (\<V> \<union> vars_llist spec0);
   spec \<leftarrow> RETURN spec;
   failed \<leftarrow> SPEC(\<lambda>_::bool. True);
   if failed
   then do {
     c \<leftarrow> remap_polys_l_dom_err;
     SPEC (\<lambda>(mem, _, _). mem = error_msg (0::nat) c)
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
   unfolding remap_polys_l_with_err_def by (auto intro!: ext bind_cong[OF refl])

lemma remap_polys_l2_with_err_polys_l2_with_err:
  assumes \<open>(\<V>, \<V>') \<in> {(x, y). y = set_mset x}\<close> \<open>(A,A') \<in> Id\<close> \<open>(spec, spec')\<in>Id\<close> \<open>(spec0, spec0')\<in>Id\<close>
  shows \<open>remap_polys_l2_with_err spec spec0 \<V> A \<le> \<Down>{((st, \<V>, A), st', \<V>', A').
   (st, st') \<in> Id \<and>
   (A, A') \<in> Id \<and>
    (\<not> is_cfailed st \<longrightarrow> (\<V>, \<V>') \<in> {(x, y). y = set_mset x})}
    (remap_polys_l_with_err spec' spec0' \<V>' A')\<close>
proof -
  have [refine]: \<open>inj_on id dom\<close> for dom
    by (auto simp: inj_on_def)
  have [refine]: \<open>((CSUCCESS, \<V>, fmempty), CSUCCESS, \<V>', fmempty) \<in> {((st, \<V>, A), st', \<V>', A').
    (st, st') \<in> Id \<and>  (A, A') \<in> Id \<and> (\<not> is_cfailed st \<longrightarrow> (\<V>, \<V>') \<in> {(x, y). y = set_mset x})}\<close>
    if \<open>(\<V>, \<V>') \<in> {(x, y). y = set_mset x}\<close>
    for \<V> \<V>'
    using assms that
    by auto
  have [refine]: \<open>import_poly x1c p \<le>\<Down>{((mem, ys, \<A>'), (err :: string code_status)). (alloc_failed mem \<longleftrightarrow> err = CFAILED ''memory out'') \<and>
    (\<not>alloc_failed mem \<longleftrightarrow> err = CSUCCESS) \<and>
    (\<not> alloc_failed mem \<longrightarrow> ys = p \<and> set_mset \<A>' = set_mset x1c \<union> \<Union> (set ` fst ` set p))}
    (SPEC (\<lambda>err. err \<noteq> CFOUND))\<close> for x1c p
    apply (rule order_trans[OF import_poly_spec])
    apply (auto simp: conc_fun_RES)
    done

  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  have id2: \<open>(f,g)\<in>{(x, y). y = set_mset x} \<Longrightarrow> (f,g)\<in>{(x, y). y = set_mset x}\<close> for f g
    by auto
  have [refine]: \<open> SPEC (\<lambda>(mem, \<V>'). \<not> alloc_failed mem \<longrightarrow> set_mset \<V>' = set_mset \<V> \<union> vars_llist spec0)
    \<le> SPEC (\<lambda>c. (c, \<V>' \<union> vars_llist spec0') \<in> {((mem, x), y). \<not> alloc_failed mem \<longrightarrow> y = set_mset x})\<close>
    using assms by auto
  have [refine]: \<open>(x, \<V>''') \<in> {((mem, x), y). \<not> alloc_failed mem \<longrightarrow> y = set_mset x} \<Longrightarrow>
    x = (x1, \<V>'') \<Longrightarrow>
    (if \<not> alloc_failed x1 then import_poly \<V>'' spec else SPEC(\<lambda>_. True)) \<le> SPEC (\<lambda>c. (c, spec') \<in>
    {((new, ys, \<A>'), spec').
     (\<not> alloc_failed new \<and> \<not> alloc_failed x1 \<longrightarrow>
     ys = spec \<and>  spec' = spec \<and> set_mset \<A>' = set_mset \<V>'' \<union> \<Union> (set ` mononoms spec))})\<close>
    for \<V>'' \<V>''' x x1
    using assms
    by (auto split: if_splits intro!: import_poly_spec[THEN order_trans])
  have [simp]: \<open>(\<Union>a\<in>set spec'. set (fst a)) \<subseteq> (\<Union>a\<in>set spec0'. set (fst a)) \<Longrightarrow>
    set_mset \<V> \<union> (\<Union>x\<in>set spec0'. set (fst x)) \<union> (\<Union>x\<in>set spec'. set (fst x)) =
    set_mset \<V> \<union> (\<Union>x\<in>set spec0'. set (fst x))\<close>
    by (auto)
  show ?thesis
    unfolding remap_polys_l2_with_err_def remap_polys_l_with_err_alt_def
    apply (refine_rcg)
    subgoal using assms unfolding remap_polys_l_with_err_pre_def by auto
    subgoal using assms by auto
    apply assumption
    subgoal by auto
    subgoal using assms by auto
    subgoal by (auto simp: error_msg_def)

    subgoal using assms by (simp add: )
    subgoal by (auto intro!: RES_refine)
    subgoal using assms by (simp add: )
    subgoal using assms by (simp add: remap_polys_l_with_err_pre_def vars_llist_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by (auto simp: vars_llist_def)
    apply (rule id)
    subgoal using assms by auto
    apply (rule id)
    subgoal using assms by auto
    apply (rule id2)
    subgoal using assms by (clarsimp simp add: vars_llist_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    done
qed

definition PAC_checker_l2 where
  \<open>PAC_checker_l2 spec A b st = do {
  (S, _) \<leftarrow> WHILE\<^sub>T
  (\<lambda>((b, A), n). \<not>is_cfailed b \<and> n \<noteq> [])
  (\<lambda>((bA), n). do {
  ASSERT(n \<noteq> []);
  S \<leftarrow> PAC_checker_l_step_prep spec bA (hd n);
  RETURN (S, tl n)
  })
  ((b, A), st);
  RETURN S
  }\<close>

lemma PAC_checker_l2_PAC_checker_l:
  assumes \<open>(A, A') \<in> {(x, y). y = set_mset x} \<times>\<^sub>r Id\<close> \<open>(spec, spec')\<in>Id\<close> \<open>(st, st')\<in>Id\<close> \<open>(b,b')\<in>Id\<close>
  shows \<open>PAC_checker_l2 spec A b st \<le> \<Down>{((b, A, st), (b', A', st')).
      (\<not>is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st')\<in>Id) \<and> (b,b')\<in>Id} (PAC_checker_l spec' A' b' st')\<close>
proof -
  show ?thesis
    unfolding PAC_checker_l2_def PAC_checker_l_def
    apply (refine_rcg
      PAC_checker_l_step_prep_PAC_checker_l_step
      WHILET_refine[where R = \<open>{(((b, A), st:: (llist_polynomial, string, nat) pac_step list), (b', A'), st').
      (\<not>is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<times>\<^sub>r Id) \<and> (b,b')\<in>Id \<and> (st,st')\<in>Id}\<close>])
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

definition (in -) remap_polys_l2_with_err_prep :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> (nat, string) vars \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow>
   (string code_status \<times> (nat, string) vars \<times> (nat, llist_polynomial) fmap \<times> llist_polynomial) nres\<close> where
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
              p \<leftarrow> full_normalize_poly p;
              eq  \<leftarrow> weak_equality_l p spec;
              let \<V> = \<V>;
              RETURN((if eq then CFOUND else CSUCCESS), \<V>, fmupd i p A')
            }
          } else RETURN (err, \<V>, A'))
       (CSUCCESS, \<V>, fmempty);
     RETURN (err, \<V>, A, spec)
  }})\<close>

lemma remap_polys_l2_with_err_prep_remap_polys_l2_with_err:
  assumes \<open>(p, p') \<in> Id\<close>  \<open>(q, q') \<in> Id\<close> \<open>(A,A') \<in> \<langle>Id, Id\<rangle>fmap_rel\<close> and \<open>(V,V') \<in> Id\<close>
  shows \<open>remap_polys_l2_with_err_prep p q V A \<le> \<Down>{((b, A, st, spec'), (b', A', st')).
    ((b, A, st), (b', A', st')) \<in> Id \<and>
    (\<not>is_cfailed b \<longrightarrow> spec' = p')} (remap_polys_l2_with_err p' q' V' A')\<close>
proof -
  have [simp]: \<open>\<langle>Id, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def fmlookup_dom_iff intro!: fmap_ext dest: fmdom_notD)
    by (metis fmdom_notD fmlookup_dom_iff option.sel)

  have 1: \<open>inj_on id (dom :: nat set)\<close> for dom
    by auto
  have [refine]:
    \<open>(x2e, x2c)\<in>Id \<Longrightarrow> ((CSUCCESS, x2e, fmempty), CSUCCESS, x2c, fmempty) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>Id, Id\<rangle>fmap_rel\<close> for x2e x2c
    by auto
  have [refine]: \<open>import_poly x y \<le> \<Down> Id (import_poly x' y')\<close>
    if \<open>(x,x') \<in> Id\<close>\<open>(y,y') \<in> Id\<close> for x x' y y'
    using that by auto
  have [refine]: \<open>full_normalize_poly x \<le> \<Down> Id (full_normalize_poly x')\<close>
    if \<open>(x,x')\<in>Id\<close> for x x'
    using that by auto
  have [refine]: \<open>weak_equality_l x y \<le> \<Down> bool_rel (weak_equality_l x' y')\<close>
    if \<open>(x,x')\<in>Id\<close> \<open>(y,y')\<in>Id\<close> for x x' y y'
    using that by auto

  show ?thesis
    unfolding remap_polys_l2_with_err_prep_def remap_polys_l2_with_err_def
    apply (refine_vcg 1)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by (auto intro!: RES_refine simp: error_msg_def)
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

definition full_checker_l_prep
  :: \<open>llist_polynomial \<Rightarrow> (nat, llist_polynomial) fmap \<Rightarrow> (_, string, nat) pac_step list \<Rightarrow>
    (string code_status \<times> _) nres\<close>
where
  \<open>full_checker_l_prep spec A st = do {
    spec' \<leftarrow> full_normalize_poly spec;
    (b, \<V>, A, spec) \<leftarrow> remap_polys_l2_with_err_prep spec' spec {#} A;
    if is_cfailed b
    then RETURN (b, \<V>, A)
    else do {
      let \<V> = \<V>;
      PAC_checker_l2 spec (\<V>, A) b st
     }
        }\<close>

lemma remap_polys_l2_with_err_polys_l_with_err:
  assumes \<open>(\<V>, \<V>') \<in> {(x, y). y = set_mset x}\<close> \<open>(A,A') \<in> Id\<close> \<open>(spec, spec')\<in>Id\<close> \<open>(spec0, spec0')\<in>Id\<close>
  shows \<open>remap_polys_l2_with_err_prep spec spec0 \<V> A \<le> \<Down>{((st, \<V>, A, spec''), st', \<V>', A').
   (st, st') \<in> Id \<and>
   (A, A') \<in> Id \<and>
    (\<not> is_cfailed st \<longrightarrow> (\<V>, \<V>') \<in> {(x, y). y = set_mset x} \<and> spec'' = spec)}
    (remap_polys_l_with_err spec' spec0' \<V>' A')\<close>
proof -
  have [simp]: \<open>\<langle>Id, Id\<rangle>fmap_rel = Id\<close>
    apply (auto simp: fmap_rel_def fmlookup_dom_iff intro!: fmap_ext dest: fmdom_notD)
    by (metis fmdom_notD fmlookup_dom_iff option.sel)

  have A: \<open>(A, A') \<in> \<langle>nat_rel, Id\<rangle>fmap_rel\<close> \<open>(\<V>, \<V>) \<in> Id\<close> \<open>(A',A') \<in> Id\<close>
    \<open>(spec',spec')\<in> Id\<close> \<open>(spec0', spec0') \<in> Id\<close>
    using assms(2) by auto
  show ?thesis
    apply (rule remap_polys_l2_with_err_prep_remap_polys_l2_with_err[THEN order_trans])
    apply (rule assms A)+
    apply (rule order_trans)
    apply (rule ref_two_step')
    apply (rule remap_polys_l2_with_err_polys_l2_with_err)
    apply (rule assms A)+
    apply (subst conc_fun_chain)
    apply (rule conc_fun_R_mono)
    apply (use assms in auto)
    done
qed


lemma full_checker_l_prep_full_checker_l:
  assumes \<open>(spec, spec')\<in>Id\<close> \<open>(st, st')\<in>Id\<close> \<open>(A,A')\<in>Id\<close>
  shows \<open>full_checker_l_prep spec A st \<le>\<Down>{((b, A, st), (b', A', st')).
    (\<not>is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st')\<in>Id) \<and> (b,b')\<in>Id}
    (full_checker_l spec' A' st')\<close>
proof -
  have id: \<open>f=g \<Longrightarrow> f \<le>\<Down>Id g\<close> for f g
    by auto
  show ?thesis
    unfolding full_checker_l_prep_def full_checker_l_def
    apply (refine_rcg remap_polys_l2_with_err_polys_l_with_err
      PAC_checker_l2_PAC_checker_l remap_polys_l2_with_err_polys_l_with_err)
    apply (rule id)
    subgoal using assms by auto
    subgoal by auto
    apply (rule assms)
    subgoal by auto
    apply (rule assms)
    subgoal by auto
    subgoal using assms by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    subgoal by auto
    done
qed


lemma full_checker_l_prep_full_checker_l2':
  shows \<open>(uncurry2 full_checker_l_prep, uncurry2 full_checker_l) \<in> (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow>\<^sub>f
    \<langle>{((b, A, st), (b', A', st')). (\<not>is_cfailed b \<longrightarrow> (A, A') \<in> {(x, y). y = set_mset x} \<and> (st, st')\<in>Id) \<and> (b,b')\<in>Id}\<rangle>nres_rel\<close>
  by (auto intro!: frefI nres_relI full_checker_l_prep_full_checker_l[THEN order_trans])

end

