theory EPAC_Efficient_Checker
  imports EPAC_Checker EPAC_Perfectly_Shared_Vars
begin
type_synonym shared_poly = \<open>(nat list \<times> int) list\<close>

context poly_embed
begin

definition add_poly_l' where
  \<open>add_poly_l' _ = add_poly_l\<close>

datatype ordered = LESS | EQUAL | GREATER | UNKNOWN

definition perfect_shared_term_order_rel
  :: \<open>(nat, string) vars \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> ordered nres\<close>
where
  \<open>perfect_shared_term_order_rel \<V> xs ys  = do {
    (b, _, _) \<leftarrow> WHILE\<^sub>T (\<lambda>(b, xs, ys). b = UNKNOWN)
    (\<lambda>(b, xs, ys). do {
       if xs = [] \<and> ys = [] then RETURN (EQUAL, xs, ys)
       else if xs = [] then RETURN (LESS, xs, ys)
       else if ys = [] then RETURN (GREATER, xs, ys)
       else do {
         ASSERT(xs \<noteq> [] \<and> ys \<noteq> []); 
         eq \<leftarrow> perfectly_shared_strings_equal \<V> (hd xs) (hd ys);
         if eq then RETURN (b, tl xs, tl ys)
         else do {
           x \<leftarrow> get_var_name \<V> (hd xs);
           y \<leftarrow> get_var_name \<V> (hd ys);
           if (x, y) \<in> var_order_rel then RETURN (LESS, xs, ys)
           else RETURN (GREATER, xs, ys)}
       }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>

lemma var_roder_rel_total:
  \<open>y \<noteq> ya \<Longrightarrow> (y, ya) \<notin> var_order_rel \<Longrightarrow> (ya, y) \<in> var_order_rel\<close>
  unfolding var_order_rel_def
  using less_than_char_linear lexord_linear by blast

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
      R = \<open>measure (\<lambda>(b, xs, ys). length xs + (if b = UNKNOWN then 1 else 0))\<close>])
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
    subgoal by (auto simp: neq_Nil_conv lexord_append_leftI)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv intro: var_roder_rel_total
      intro!: lexord_append_leftI lexord_append_rightI)
    subgoal by (auto simp: neq_Nil_conv intro: var_roder_rel_total
      intro!: lexord_append_leftI lexord_append_rightI)
    subgoal by (auto simp: neq_Nil_conv intro: var_roder_rel_total
      intro!: lexord_append_leftI lexord_append_rightI)
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by (auto simp: neq_Nil_conv)
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

definition add_poly_l_prep :: \<open>(nat,string)vars \<Rightarrow> llist_polynomial \<times> llist_polynomial \<Rightarrow>  llist_polynomial nres\<close> where
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
        find_theorems import_poly_no_new
          term import_poly_no_new


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

end

end