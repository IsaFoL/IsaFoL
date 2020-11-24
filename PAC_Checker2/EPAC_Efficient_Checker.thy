theory EPAC_Efficient_Checker
  imports EPAC_Checker EPAC_Perfectly_Shared_Vars
begin
type_synonym shared_poly = \<open>(nat list \<times> int) list\<close>

context poly_embed
begin

definition add_poly_l' where
  \<open>add_poly_l' _ = add_poly_l\<close>

datatype ordered = LESS | EQUAL | GREATER | UNKNOWN

definition perfect_shared_var_order :: \<open>(nat, string)vars \<Rightarrow> string \<Rightarrow> string \<Rightarrow> ordered nres\<close> where
  \<open>perfect_shared_var_order \<D> x y = do {
    ASSERT(x \<in># \<D> \<and> y \<in># \<D>);
    eq \<leftarrow> perfectly_shared_strings_equal \<D> x y;
    if eq then RETURN EQUAL
    else do {
      x \<leftarrow> get_var_name \<D> x;
      y \<leftarrow> get_var_name \<D> y;
      if (x, y) \<in> var_order_rel then RETURN (LESS)
      else RETURN (GREATER)
    }
  }\<close>

lemma var_roder_rel_total:
  \<open>y \<noteq> ya \<Longrightarrow> (y, ya) \<notin> var_order_rel \<Longrightarrow> (ya, y) \<in> var_order_rel\<close>
  unfolding var_order_rel_def
  using less_than_char_linear lexord_linear by blast

lemma perfect_shared_var_order_spec:
  assumes \<open>xs \<in># \<V>\<close>  \<open>ys \<in># \<V>\<close>
  shows
    \<open>perfect_shared_var_order \<V> xs ys \<le> \<Down> Id (SPEC(\<lambda>b. ((b=LESS \<longrightarrow> (xs, ys) \<in> var_order_rel) \<and>
    (b=GREATER \<longrightarrow> (ys, xs) \<in> var_order_rel \<and> \<not>(xs, ys) \<in> var_order_rel) \<and>
    (b=EQUAL \<longrightarrow> xs = ys)) \<and> b \<noteq> UNKNOWN))\<close>
  using assms unfolding perfect_shared_var_order_def perfectly_shared_strings_equal_def nres_monad3 get_var_name_def
  by refine_vcg
   (auto dest: var_roder_rel_total)


definition perfect_shared_term_order_rel_pre
  :: \<open>(nat, string) vars \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> bool\<close>
where
  \<open>perfect_shared_term_order_rel_pre \<V> xs ys \<longleftrightarrow>
    set xs \<subseteq> set_mset \<V> \<and> set ys \<subseteq> set_mset \<V>\<close>

definition perfect_shared_term_order_rel
  :: \<open>(nat, string) vars \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel \<V> xs ys  = do {
    ASSERT (perfect_shared_term_order_rel_pre \<V> xs ys);
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []); 
         eq \<leftarrow> perfect_shared_var_order \<V> (hd xs) (hd ys);
         if eq = EQUAL then RETURN (b, tl xs, tl ys)
         else RETURN (eq, xs, ys)
      }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>


lemma perfect_shared_term_order_rel_spec:
  assumes \<open>set xs \<subseteq> set_mset \<V>\<close>  \<open>set ys \<subseteq> set_mset \<V>\<close>
  shows
    \<open>perfect_shared_term_order_rel \<V> xs ys \<le> \<Down> Id (SPEC(\<lambda>b. ((b=LESS \<longrightarrow> (xs, ys) \<in> term_order_rel) \<and>
    (b=GREATER \<longrightarrow> (ys, xs) \<in> term_order_rel) \<and>
    (b=EQUAL \<longrightarrow> xs = ys)) \<and> b \<noteq> UNKNOWN))\<close> (is \<open>_ \<le> \<Down> _ (SPEC (\<lambda>b. ?f b \<and> b \<noteq> UNKNOWN))\<close>)
proof -
  define I where
  [simp]:  \<open>I=  (\<lambda>(b, xs0, ys0). ?f b \<and> (\<exists>xs'. xs = xs' @ xs0 \<and> ys = xs' @ ys0))\<close>
  show ?thesis
    using assms
    unfolding perfect_shared_term_order_rel_def get_var_name_def perfectly_shared_strings_equal_def
      perfectly_shared_strings_equal_def
    apply (refine_vcg WHILET_rule[where I= \<open>I\<close> and
      R = \<open>measure (\<lambda>(b, xs, ys). length xs + (if b = UNKNOWN then 1 else 0))\<close>]
      perfect_shared_var_order_spec[THEN order_trans])
    subgoal by (auto simp: perfect_shared_term_order_rel_pre_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv lexord_append_leftI lexord_append_rightI)
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv lexord_append_leftI lexord_append_rightI)
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv lexord_append_leftI)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal
      by ((subst conc_Id id_apply)+, rule SPEC_rule, rename_tac x, case_tac x)
       (auto simp: neq_Nil_conv intro: var_roder_rel_total
        intro!: lexord_append_leftI lexord_append_rightI)
    subgoal by (auto simp: neq_Nil_conv lexord_append_leftI)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    done
qed

lemma trans_var_order_rel[simp]: \<open>trans var_order_rel\<close>
  unfolding trans_def var_order_rel_def
  apply (intro conjI impI allI)
  by (meson lexord_partial_trans trans_def trans_less_than_char)
 
lemma term_order_rel_irreflexive:
  \<open>(x1f, x1d) \<in> term_order_rel \<Longrightarrow> (x1d, x1f) \<in> term_order_rel \<Longrightarrow> x1f = x1d\<close>
  using lexord_trans[of x1f x1d var_order_rel x1f] lexord_irreflexive[of var_order_rel x1f]
  by simp

definition add_poly_l_prep :: \<open>(nat,string)vars \<Rightarrow> llist_polynomial \<times> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
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

definition normalize_poly_shared
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


definition linear_combi_l_prep where
  \<open>linear_combi_l_prep i A \<V> xs = do {
  WHILE\<^sub>T
    (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
    (\<lambda>(p, xs, _). do {
      ASSERT(xs \<noteq> []);
      let (q :: llist_polynomial, i) = hd xs;
      if (i \<notin># dom_m A \<or> \<not>(vars_llist q \<subseteq> set_mset \<V>))
      then do {
        err \<leftarrow> check_linear_combi_l_dom_err q i;
        RETURN (p, xs, error_msg i err)
      } else do {
        ASSERT(fmlookup A i \<noteq> None);  
        let r = the (fmlookup A i);
        (no_new, q) \<leftarrow> normalize_poly_shared \<V> (q);
        q \<leftarrow> mult_poly_full q r;
        pq \<leftarrow> add_poly_l (p, q);
        RETURN (pq, tl xs, CSUCCESS)
        }
        })
        ([], xs, CSUCCESS)
        }\<close>


lemma import_poly_no_new_spec:
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

lemma linear_combi_l_prep_linear_combi_l:
  \<open>linear_combi_l_prep i A \<V> xs  \<le> \<Down>Id (linear_combi_l i A (set_mset \<V>) xs) \<close>
proof -
  have H1: \<open>(if p \<or> q then P else Q) = (if p then P else if q then P else Q)\<close> for p q P Q
    by auto
  have [intro!]: \<open>check_linear_combi_l_dom_err x1e x2e \<le> \<Down> Id (check_linear_combi_l_dom_err x1e x2e)\<close>
    for x1e x2e
    by auto
  have linear_combi_l_alt_def:
      \<open>linear_combi_l i A \<V> xs = do {
      WHILE\<^sub>T
        (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
        (\<lambda>(p, xs, _). do {
          ASSERT(xs \<noteq> []);
          let (q :: llist_polynomial, i) = hd xs;
          if (i \<notin># dom_m A \<or> \<not>(vars_llist q \<subseteq> \<V>))
          then do {
            err \<leftarrow> check_linear_combi_l_dom_err q i;
            RETURN (p, xs, error_msg i err)
            }
          else do {
          ASSERT(fmlookup A i \<noteq> None);  
          let r = the (fmlookup A i);
          q \<leftarrow> full_normalize_poly q;
          ASSERT (vars_llist q \<subseteq> \<V>);
          let q = q;
          pq \<leftarrow> mult_poly_full q r;
          pq \<leftarrow> add_poly_l (p, pq);
          RETURN (pq, tl xs, CSUCCESS)
          }
       })
    ([], xs, CSUCCESS)
    }\<close> for i A \<V> xs
    unfolding Let_def linear_combi_l_def by auto
  have H: \<open>P = Q \<Longrightarrow> P \<le>\<Down>Id Q\<close> for P Q
    by auto
  have [refine0]: \<open>\<Down> Id (SPEC (\<lambda>(b, xs'). (\<not> b \<longrightarrow> xa = xs') \<and> (\<not> b) = (vars_llist xa \<subseteq> set_mset \<V>)))
    \<le> SPEC (\<lambda>c. (c, q) \<in> {((b, c), d). \<not>b \<and> c = d \<and> d = q})\<close>
    if \<open>vars_llist xa \<subseteq> set_mset \<V>\<close> \<open>xa = q\<close>
    for xa \<V> q
    using that by auto
  show ?thesis
    unfolding linear_combi_l_prep_def linear_combi_l_alt_def normalize_poly_shared_def nres_monad3
    apply (refine_rcg import_poly_no_new_spec[THEN order_trans])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    done 
qed

thm mult_poly_full_def
thm mult_poly_raw_def
thm mult_monomials_def
thm mult_monoms.simps
term REC\<^sub>T

definition mult_monoms_prep :: \<open>(nat,string)vars \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list nres\<close> where
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


lemma mult_monoms_prep_mult_monoms:
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

definition mult_poly_full_prop :: \<open>_\<close> where
\<open>mult_poly_full_prop \<V> p q = do {
  pq \<leftarrow> mult_poly_raw_prop \<V> p q;
  normalize_poly pq
}\<close>

lemma mult_poly_full_prop_mult_poly_full:
  assumes \<open>vars_llist qs \<subseteq> set_mset \<V>\<close> \<open>vars_llist ps \<subseteq> set_mset \<V>\<close>
  shows \<open>mult_poly_full_prop \<V> ps qs \<le> \<Down>Id (mult_poly_full ps qs)\<close>
proof -
  have [refine0]: \<open>sort_poly_spec p \<le> \<Down> Id (sort_poly_spec p')\<close>
    if \<open>mset p= mset p'\<close> for p p'
    using that
    unfolding sort_poly_spec_def
    by auto
  show ?thesis
    using assms
    unfolding mult_poly_full_prop_def mult_poly_full_def normalize_poly_def
    by (refine_vcg mult_poly_raw_prop_mult_poly_raw) auto
qed
  term linear_combi_l_prep
thm linear_combi_l_prep_def
definition linear_combi_l_prep2 where
\<open>linear_combi_l_prep2 i A \<V> xs = do {
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
           (_, q) \<leftarrow> normalize_poly_shared \<V> (q\<^sub>0);
           ASSERT(vars_llist q \<subseteq> set_mset \<V>);
           pq \<leftarrow> mult_poly_full_prop \<V> q r;
           pq \<leftarrow> add_poly_l_prep \<V> (p, pq);
           RETURN (pq, tl xs, CSUCCESS)
         }
      })
     ([], xs, CSUCCESS)
    }\<close>

lemma
  assumes \<V>: \<open>(\<V>,\<V>') \<in> {(x, y). y = set_mset x}\<close> and
    A: \<open>\<And>xs. xs \<in># dom_m A \<Longrightarrow> vars_llist (A \<propto> xs) \<subseteq> set_mset \<V>\<close>
  shows \<open>linear_combi_l_prep2 i A \<V> xs \<le> \<Down>Id (linear_combi_l i A \<V>' xs)\<close>
proof -
  have H1: \<open>(if p \<or> q then P else Q) = (if p then P else if q then P else Q)\<close> for p q P Q
    by auto
  have [intro!]: \<open>check_linear_combi_l_dom_err x1e x2e \<le> \<Down> Id (check_linear_combi_l_dom_err x1e x2e)\<close>
    for x1e x2e
    by auto
  have linear_combi_l_alt_def:
      \<open>linear_combi_l i A \<V> xs = do {
      WHILE\<^sub>T
        (\<lambda>(p, xs, err). xs \<noteq> [] \<and> \<not>is_cfailed err)
        (\<lambda>(p, xs, _). do {
          ASSERT(xs \<noteq> []);
          let (q :: llist_polynomial, i) = hd xs;
          if (i \<notin># dom_m A \<or> \<not>(vars_llist q \<subseteq> \<V>))
          then do {
            err \<leftarrow> check_linear_combi_l_dom_err q i;
            RETURN (p, xs, error_msg i err)
            }
          else do {
          ASSERT(fmlookup A i \<noteq> None);
          let r = the (fmlookup A i);
          q \<leftarrow> full_normalize_poly q;
          ASSERT (vars_llist q \<subseteq> \<V>);
          let q = q;
          pq \<leftarrow> mult_poly_full q r;
          pq \<leftarrow> add_poly_l' \<V>' (p, pq);
          RETURN (pq, tl xs, CSUCCESS)
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
    unfolding linear_combi_l_prep2_def linear_combi_l_alt_def normalize_poly_shared_def nres_monad3
    apply (refine_rcg import_poly_no_new_spec[THEN order_trans]
      mult_poly_full_prop_mult_poly_full[THEN order_trans]
      add_poly_alt_def[THEN order_trans])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using \<V> by auto
    apply (rule H)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule H)
    subgoal by auto
    subgoal using \<V> by auto
    subgoal by auto
    subgoal using \<V> by auto
    subgoal using \<V> A by auto
    apply (rule H)
    subgoal by auto
    subgoal using \<V> A apply auto
      sorry
    subgoal using \<V> A apply auto
      sorry
    apply (rule H)
    subgoal by (auto simp: add_poly_l'_def)
    subgoal by auto
    done
qed
    find_theorems linear_combi_l_prep
oops
end

end
