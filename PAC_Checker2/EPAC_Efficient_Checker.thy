theory EPAC_Efficient_Checker
  imports EPAC_Checker EPAC_Perfectly_Shared_Vars
begin

context poly_embed
begin
  term term_order_rel
thm add_poly_l_def
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
         x \<leftarrow> get_var_name \<V> (hd xs);
         y \<leftarrow> get_var_name \<V> (hd ys);
         if x = y then RETURN (b, tl xs, tl ys)
         else if (x, y) \<in> var_order_rel then RETURN (LESS, xs, ys)
         else RETURN (GREATER, xs, ys)
       }
    }) (UNKNOWN, xs, ys);
    RETURN b
  }\<close>

lemma var_roder_rel_total:
  \<open>y \<noteq> ya \<Longrightarrow> (y, ya) \<notin> var_order_rel \<Longrightarrow> (ya, y) \<in> var_order_rel\<close>
  unfolding var_order_rel_def
  using less_than_char_linear lexord_linear by blast

lemma perfect_shared_term_order_rel_spec:
  assumes \<open>set xs \<subseteq> snd \<V>\<close>  \<open>set ys \<subseteq> snd \<V>\<close>
  shows
    \<open>perfect_shared_term_order_rel \<V> xs ys \<le> \<Down> Id (SPEC(\<lambda>b. ((b=LESS \<longrightarrow> (xs, ys) \<in> term_order_rel) \<and>
    (b=GREATER \<longrightarrow> (ys, xs) \<in> term_order_rel) \<and>
    (b=EQUAL \<longrightarrow> xs = ys)) \<and> b \<noteq> UNKNOWN))\<close> (is \<open>_ \<le> \<Down> _ (SPEC (\<lambda>b. ?f b \<and> b \<noteq> UNKNOWN))\<close>)
proof -
  define I where
  [simp]:  \<open>I=  (\<lambda>(b, xs0, ys0). ?f b \<and> (\<exists>xs'. xs = xs' @ xs0 \<and> ys = xs' @ ys0))\<close>
  show ?thesis
    using assms
    unfolding perfect_shared_term_order_rel_def get_var_name_def
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

lemma add_poly_alt_def[unfolded conc_Id id_apply]:
  fixes xs ys :: llist_polynomial
  assumes \<open>\<Union>(set ` (fst`set xs)) \<subseteq> snd \<D>\<close>  \<open>\<Union>(set ` fst ` set ys) \<subseteq> snd \<D>\<close>
  shows \<open>\<Down> Id (add_poly_l' \<D> (xs, ys)) \<ge> REC\<^sub>T
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
       }) (xs, ys)\<close>
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
    unfolding add_poly_l'_def add_poly_l_def
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

end
end