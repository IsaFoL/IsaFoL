theory EPAC_Perfectly_Shared
  imports EPAC_Checker_Specification
    PAC_Checker.PAC_Checker (*for vars_llist*)
    EPAC_Checker (*for vars_llist*)
begin

text \<open>We now introduce sharing of variables to make a more efficient representation possible.\<close>

section \<open>Perfectly sharing of elements\<close>

subsection \<open>Definition\<close>
  
type_synonym ('nat, 'string) shared_vars = \<open>'string multiset \<times> ('nat, 'string) fmap \<times> ('string, 'nat) fmap\<close>

definition perfectly_shared_vars
  :: \<open>'string multiset \<Rightarrow>  ('nat, 'string) shared_vars \<Rightarrow> bool\<close>
where
  \<open>perfectly_shared_vars \<V> = (\<lambda>(\<D>, V, V').
  set_mset (dom_m V') = set_mset \<V> \<and> \<D> = \<V> \<and> 
  (\<forall>i \<in>#dom_m V. fmlookup V' (the (fmlookup V i)) = Some i) \<and>
  (\<forall>str \<in>#dom_m V'. fmlookup V (the (fmlookup V' str)) = Some str) \<and>
  (\<forall>i j. i\<in>#dom_m V \<longrightarrow> j\<in>#dom_m V \<longrightarrow> (fmlookup V i = fmlookup V j \<longleftrightarrow> i = j)))\<close>

abbreviation fmlookup_direct :: \<open>('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b\<close> (infix "\<propto>" 70) where
  \<open>fmlookup_direct A b \<equiv> the (fmlookup A b)\<close>

lemma perfectly_shared_vars_simps:
  assumes \<open>perfectly_shared_vars \<V> (VV')\<close>
  shows \<open>str \<in># \<V> \<longleftrightarrow> str \<in># dom_m (snd (snd VV'))\<close>
  using assms
  unfolding perfectly_shared_vars_def
  apply auto
  done

lemma perfectly_shared_add_new_var:
  fixes V :: \<open>('nat, 'string) fmap\<close> and
    v :: \<open>'string\<close>
  assumes \<open>perfectly_shared_vars \<V> (D, V, V')\<close> and
    \<open>v \<notin># \<V>\<close> and
    k_notin[simp]: \<open>k \<notin># dom_m V\<close>
  shows \<open>perfectly_shared_vars (add_mset v \<V>) (add_mset v D, fmupd k v V, fmupd v k V')\<close>
proof -
  have
    DV[simp]: \<open>D = \<V>\<close> and
    V'\<V>: \<open>set_mset (dom_m V') = set_mset \<V>\<close> and
    map: \<open>\<And>i. i \<in>#dom_m V \<Longrightarrow> fmlookup V' (the (fmlookup V i)) = Some i\<close> and
    map_str: \<open>\<And>str. str \<in>#dom_m V' \<Longrightarrow> fmlookup V (the (fmlookup V' str)) = Some str\<close> and
    perfect: \<open>\<And>i j.  i\<in>#dom_m V \<Longrightarrow> j\<in>#dom_m V \<Longrightarrow> fmlookup V i = fmlookup V j \<longleftrightarrow> i = j\<close>
    using assms unfolding perfectly_shared_vars_def
    by auto
  have v_notin[simp]: \<open>v \<notin># dom_m V'\<close>
    using V'\<V> assms(2) by blast
  show ?thesis
    unfolding perfectly_shared_vars_def prod.simps
  proof (intro conjI allI ballI impI)
    show \<open>add_mset v D = add_mset v \<V>\<close>
      using DV by auto
    show \<open>set_mset (dom_m (fmupd v k V')) = set_mset (add_mset v \<V>)\<close>
      using V'\<V> in_remove1_mset_neq by fastforce
 
    show \<open>fmlookup (fmupd v k V') (fmupd k v V \<propto> i) = Some i\<close>
      if \<open>i \<in># dom_m (fmupd k v V)\<close>
      for i
      using map[of i] that v_notin
      by (auto dest!: indom_mI simp del: v_notin)

    show \<open>fmlookup (fmupd k v V) (fmupd v k V' \<propto> str) = Some str\<close>
      if \<open>str \<in># dom_m (fmupd v k V')\<close>
      for str
      using map_str[of str] that k_notin
      by (auto dest!: indom_mI simp del: k_notin)
    show \<open>(fmlookup (fmupd k v V) i = fmlookup (fmupd k v V) j) = (i = j)\<close>
      if \<open>i \<in># dom_m (fmupd k v V)\<close> and
        \<open>j \<in># dom_m (fmupd k v V)\<close>
      for i j
      using perfect[of i j] that
      using indom_mI[of V i] map[of i] indom_mI[of V j] map[of j] indom_mI[of V' v]
      apply (auto simp: eq_commute[of \<open>Some _\<close> \<open>fmlookup V _\<close>])
      apply auto
      done
  qed
qed

lemma perfectly_shared_vars_remove_update:
  assumes \<open>perfectly_shared_vars (add_mset v \<V>) (D, V, V')\<close> and
    \<open>v \<notin># \<V>\<close>
  shows \<open>perfectly_shared_vars  \<V> (remove1_mset v D, fmdrop (V' \<propto> v) V, fmdrop v V')\<close>
  using assms
  unfolding perfectly_shared_vars_def
  by (fastforce simp: distinct_mset_dom distinct_mset_remove1_All)


section \<open>Refinement\<close>

datatype memory_allocation =
  Allocated | alloc_failed: Mem_Out

type_synonym ('nat, 'string) vars = \<open>'string multiset\<close>

definition perfectly_shared_var_rel :: \<open>('nat,'string) shared_vars \<Rightarrow> ('nat \<times> 'string) set\<close> where
  \<open>perfectly_shared_var_rel = (\<lambda>(\<D>, \<V>, \<V>'). br (\<lambda>i. \<V> \<propto> i) (\<lambda>i. i \<in># dom_m \<V>))\<close>

definition perfectly_shared_vars_rel :: \<open>(('nat,'string) shared_vars \<times> ('nat, 'string) vars) set\<close>
where
  \<open>perfectly_shared_vars_rel = {(\<A>, \<V>). perfectly_shared_vars \<V> \<A>}\<close>

definition find_new_idx :: \<open>('nat,'string) shared_vars \<Rightarrow> _\<close> where
  \<open>find_new_idx = (\<lambda>(_, \<V>, _). SPEC (\<lambda>(mem, k). \<not> alloc_failed mem \<longrightarrow> k \<notin># dom_m \<V>))\<close>

definition import_variableS
  :: \<open>'string \<Rightarrow> ('nat, 'string) shared_vars \<Rightarrow>
  (memory_allocation \<times> ('nat, 'string) shared_vars \<times> 'nat) nres\<close>
where
  \<open>import_variableS v = (\<lambda>(\<D>, \<V>, \<V>'). do {
    (mem, k) \<leftarrow> find_new_idx (\<D>, \<V>, \<V>');
    if alloc_failed mem then do {k \<leftarrow> RES (UNIV :: 'nat set); RETURN (mem, (\<D>, \<V>, \<V>'), k)}
    else RETURN (Allocated, (add_mset v \<D>, fmupd k v \<V>, fmupd v k \<V>'), k)
  })\<close>

definition import_variable
  :: \<open>'string \<Rightarrow> ('nat, 'string) vars \<Rightarrow> (memory_allocation \<times> ('nat, 'string) vars \<times> 'string) nres\<close>
  where
  \<open>import_variable v = (\<lambda>\<V>. do {
     ASSERT(v \<notin># \<V>);
     SPEC(\<lambda>(mem, \<V>', k::'string). \<not>alloc_failed mem \<longrightarrow> \<V>' = add_mset k \<V> \<and> k = v)
  })\<close>

definition is_new_variableS :: \<open>'string \<Rightarrow> ('nat, 'string) shared_vars \<Rightarrow> bool nres\<close> where
  \<open>is_new_variableS v = (\<lambda>(\<D>, \<V>, \<V>').
  RETURN (v \<notin># dom_m \<V>')
  )\<close>

definition is_new_variable :: \<open>'string \<Rightarrow> ('nat, 'string) vars \<Rightarrow> bool nres\<close> where
  \<open>is_new_variable v = (\<lambda>\<V>'.
    RETURN (v \<notin># \<V>')
  )\<close>

lemma import_variableS_import_variable:
  fixes \<V> :: \<open>('nat, 'string) vars\<close>
  assumes \<open>(\<A>, \<V>) \<in> perfectly_shared_vars_rel\<close> and \<open>(v, v') \<in> Id\<close>
  shows \<open>import_variableS v \<A> \<le> \<Down>({((mem, \<A>', i), (mem', \<V>', j)). mem = mem' \<and>
      (\<A>', \<V>') \<in> perfectly_shared_vars_rel \<and>
      (\<not>alloc_failed mem' \<longrightarrow> (i, j) \<in> perfectly_shared_var_rel \<A>') \<and>
      (\<forall>xs. xs \<in> perfectly_shared_var_rel \<A> \<longrightarrow> xs \<in> perfectly_shared_var_rel \<A>')})
    (import_variable v' \<V>)\<close>
  using assms
  unfolding import_variableS_def import_variable_def find_new_idx_def
  by (refine_vcg lhs_step_If)
   (auto intro!: RETURN_RES_refine simp:  perfectly_shared_add_new_var perfectly_shared_vars_rel_def
    perfectly_shared_var_rel_def br_def)

lemma is_new_variable_spec:
  assumes \<open>(\<A>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> \<open>(v,v') \<in> Id\<close>
  shows \<open>is_new_variableS v \<A> \<le> \<Down>bool_rel (is_new_variable v' \<D>\<V>)\<close>
  using assms
  unfolding is_new_variable_def is_new_variableS_def
  by (auto simp: perfectly_shared_vars_rel_def
    perfectly_shared_vars_simps split: prod.splits)

definition import_variables
  :: \<open>'string list \<Rightarrow> ('nat, 'string) vars \<Rightarrow> (memory_allocation \<times> ('nat, 'string) vars) nres\<close>
where
  \<open>import_variables vs \<V> = do {
  (mem, \<V>, _, _) \<leftarrow> WHILE\<^sub>T(\<lambda>(mem, \<V>, vs, _). \<not>alloc_failed mem \<and> vs \<noteq> [])
  (\<lambda>(_, \<V>, vs, vs'). do {
    ASSERT(vs \<noteq> []);
    let v = hd vs;
    a \<leftarrow> is_new_variable v \<V>;
    if \<not>a then RETURN (Allocated ,\<V>, tl vs, vs' @ [v])
    else do {
      (mem, \<V>, _) \<leftarrow> import_variable v \<V>;
      RETURN(mem, \<V>, tl vs, vs' @ [v])
    }
    })
      (Allocated, \<V>, vs, []);
    RETURN (mem, \<V>)
      }\<close>

definition import_variablesS
  :: \<open>'string list \<Rightarrow> ('nat, 'string) shared_vars \<Rightarrow> (memory_allocation \<times> ('nat, 'string) shared_vars) nres\<close>
where
  \<open>import_variablesS vs \<V> = do {
  (mem, \<V>, _) \<leftarrow> WHILE\<^sub>T(\<lambda>(mem, \<V>, vs). \<not>alloc_failed mem \<and> vs \<noteq> [])
  (\<lambda>(_, \<V>, vs). do {
    ASSERT(vs \<noteq> []);
    let v = hd vs;
    a \<leftarrow> is_new_variableS v \<V>;
    if \<not>a then RETURN (Allocated ,\<V>, tl vs)
    else do {
      (mem, \<V>, _) \<leftarrow> import_variableS v \<V>;
      RETURN(mem, \<V>, tl vs)
    }
    })
      (Allocated, \<V>, vs);
    RETURN (mem, \<V>)
  }\<close>

lemma import_variables_spec:
  \<open>import_variables vs \<V> \<le> \<Down>Id (SPEC(\<lambda>(mem, \<V>'). \<not>alloc_failed mem \<longrightarrow> set_mset \<V>' = set_mset \<V> \<union> set vs))\<close>
proof -
  define I where
    \<open>I \<equiv> (\<lambda>(mem, \<V>', vs', vs'').
      (\<not>alloc_failed mem \<longrightarrow>  (vs = vs'' @ vs') \<and> set_mset \<V>' = set_mset \<V> \<union> set vs''))\<close>
  show ?thesis
  unfolding import_variables_def is_new_variable_def
  apply (refine_vcg WHILET_rule[where I = \<open>I\<close> and
    R = \<open>measure (\<lambda>(mem, \<V>', vs', _). (if \<not>alloc_failed mem then 1 else 0) + length vs')\<close>]
    is_new_variable_spec)
  subgoal by auto
  subgoal unfolding I_def by auto
  subgoal by auto
  subgoal for s a b aa ba ab bb
    unfolding I_def by auto
  subgoal for s a b aa ba ab bb
    by auto
  subgoal
    by (clarsimp simp: neq_Nil_conv import_variable_def I_def)
  subgoal
    by (auto simp: I_def)
  done
qed

lemma import_variablesS_import_variables:
  assumes \<open>(\<V>, \<V>') \<in> perfectly_shared_vars_rel\<close> and
    \<open>(vs, vs') \<in> Id\<close>
  shows \<open>import_variablesS vs \<V> \<le> \<Down>(Id \<times>\<^sub>r perfectly_shared_vars_rel) (import_variables vs' \<V>')\<close>
proof -
  show ?thesis
    unfolding import_variablesS_def import_variables_def
    apply (refine_rcg WHILET_refine[where R = \<open>{((mem, \<V>, vs), (mem', \<V>', vs', _)).
      (mem, mem') \<in> Id \<and> (\<V>, \<V>') \<in> perfectly_shared_vars_rel \<and> (vs, vs') \<in> Id}\<close>]
      is_new_variable_spec import_variableS_import_variable)
    subgoal using assms by auto
    subgoal by auto
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
qed

definition get_var_name :: \<open>('nat, 'string) vars \<Rightarrow> 'string \<Rightarrow>  'string nres\<close> where
  \<open>get_var_name \<V> x = do {
    ASSERT(x \<in># \<V>);
    RETURN x
  }\<close>

definition get_var_posS  :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'string \<Rightarrow> 'nat nres\<close> where
  \<open>get_var_posS \<V> x = do {
    ASSERT(x \<in># dom_m (snd (snd \<V>)));
    RETURN (snd (snd \<V>) \<propto> x)
  }\<close>

definition get_var_nameS :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'nat \<Rightarrow> 'string nres\<close> where
  \<open>get_var_nameS \<V> x = do {
    ASSERT(x \<in># dom_m (fst (snd \<V>)));
    RETURN (fst (snd \<V>) \<propto> x)
  }\<close>

lemma get_var_posS_spec:
  fixes \<D>\<V> :: \<open>('nat, 'string) vars\<close> and
    \<A> :: \<open>('nat, 'string) shared_vars\<close> and
    x :: 'string
  assumes \<open>(\<A>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(x,x') \<in> Id\<close>
  shows \<open>get_var_posS \<A> x \<le> \<Down>(perfectly_shared_var_rel \<A>) (get_var_name \<D>\<V> x')\<close>
  using assms unfolding get_var_posS_def get_var_name_def
  apply refine_vcg
  apply (auto simp: perfectly_shared_var_rel_def
    perfectly_shared_vars_rel_def perfectly_shared_vars_simps br_def
    intro!: ASSERT_leI)
  apply (simp_all add: perfectly_shared_vars_def in_dom_m_lookup_iff)
  done

abbreviation perfectly_shared_monom
  :: \<open>('nat,'string) shared_vars \<Rightarrow> ('nat list \<times> 'string list) set\<close>
where
  \<open>perfectly_shared_monom \<V> \<equiv> \<langle>perfectly_shared_var_rel \<V>\<rangle>list_rel \<close>

definition import_monom_no_newS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'string list \<Rightarrow> (bool \<times> 'nat list) nres\<close>
where
  \<open>import_monom_no_newS \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let x = hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (False, tl xs, ys @ [x])
       }
    })
    (False, xs, []);
  RETURN (new, xs)
 }\<close>

definition import_monom_no_new
  :: \<open>('nat, 'string) vars \<Rightarrow> 'string list \<Rightarrow> (bool \<times> 'string list) nres\<close>
where
  \<open>import_monom_no_new \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
  (\<lambda>(_, xs, ys). do {
    ASSERT(xs \<noteq> []);
    let x = hd xs;
    b \<leftarrow> is_new_variable x \<A>;
    if b
    then RETURN (True, tl xs, ys)
      else do {
      x \<leftarrow> get_var_name \<A> x;
      RETURN (False, tl xs, ys @ [x])
    }
    })
    (False, xs, []);
  RETURN (new, xs)
}\<close>

lemma import_monom_no_new_spec:
  shows \<open>import_monom_no_new \<A> xs \<le> \<Down> Id
    (SPEC(\<lambda>(new, ys). (new \<longleftrightarrow> \<not>set xs \<subseteq> set_mset \<A>) \<and>
      (\<not>new \<longrightarrow> ys = xs)))\<close>
  unfolding import_monom_no_new_def is_new_variable_def get_var_name_def
  apply (refine_vcg
    WHILET_rule[where I = \<open>(\<lambda>(new, ys, zs). (\<not>new \<longrightarrow> xs = zs @ ys) \<and> (\<not>new \<longrightarrow> set zs \<subseteq> set_mset \<A>) \<and>
     (new \<longrightarrow> \<not>set xs \<subseteq> set_mset \<A>))\<close> and
    R = \<open>measure (\<lambda>(_, ys, _). length ys)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

lemma import_monom_no_newS_import_monom_no_new:
  assumes \<open>(\<A>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in> Id\<close>
  shows \<open>import_monom_no_newS \<A> xs \<le> \<Down>(bool_rel \<times>\<^sub>r perfectly_shared_monom \<A>)
    (import_monom_no_new \<V>\<D> xs')\<close>
  using assms
  unfolding import_monom_no_new_def import_monom_no_newS_def
  apply (refine_rcg WHILET_refine[where R = \<open>bool_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r perfectly_shared_monom \<A>\<close>]
    is_new_variable_spec get_var_posS_spec)
  subgoal by auto
  subgoal
    by auto
  subgoal
    by auto 
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (force simp: list_rel_append1)
  subgoal by auto
  done

 definition import_poly_no_newS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow> (bool \<times> ('nat list \<times> 'a)list) nres\<close>
where
  \<open>import_poly_no_newS \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (b, x) \<leftarrow> import_monom_no_newS \<A> x;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        RETURN (False, tl xs, ys @ [(x, n)])
       }
    })
    (False, xs, []);
  RETURN (new, xs)
 }\<close>

definition import_poly_no_new
  :: \<open>('nat, 'string) vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow> (bool \<times> ('string list \<times> 'a) list) nres\<close>
where
  \<open>import_poly_no_new \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
  (\<lambda>(_, xs, ys). do {
    ASSERT(xs \<noteq> []);
    let (x, n) = hd xs;
    (b, x) \<leftarrow> import_monom_no_new \<A> x;
    if b
    then RETURN (True, tl xs, ys)
      else do {
      RETURN (False, tl xs, ys @ [(x, n)])
    }
    })
    (False, xs, []);
  RETURN (new, xs)
}\<close>


lemma import_poly_no_newS_import_poly_no_new:
  assumes \<open>(\<A>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in> Id\<close>
  shows \<open>import_poly_no_newS \<A> xs \<le> \<Down>(bool_rel \<times>\<^sub>r \<langle>perfectly_shared_monom \<A> \<times>\<^sub>r Id\<rangle>list_rel)
    (import_poly_no_new \<V>\<D> xs')\<close>
  using assms
  unfolding import_poly_no_new_def import_poly_no_newS_def
  apply (refine_rcg WHILET_refine[where
    R = \<open>bool_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>perfectly_shared_monom \<A> \<times>\<^sub>r Id\<rangle>list_rel\<close>]
    import_monom_no_newS_import_monom_no_new)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (force simp: list_rel_append1)
  subgoal by auto
  done

lemma import_poly_no_new_spec:
  shows \<open>import_poly_no_new \<A> xs \<le> \<Down> Id
    (SPEC(\<lambda>(new, ys). \<not>new \<longrightarrow> ys = xs \<and> vars_llist xs \<subseteq> set_mset \<A>))\<close>
proof -
  define I where
    [simp]: \<open>I = (\<lambda>(new, ys, zs). \<not>new \<longrightarrow> (xs = zs @ ys \<and> vars_llist zs \<subseteq> set_mset \<A>))\<close>
  show ?thesis
  unfolding import_poly_no_new_def is_new_variable_def get_var_name_def import_variable_def
  apply (refine_vcg import_monom_no_new_spec[THEN order_trans]
    WHILET_rule[where I = \<open>I\<close> and
    R = \<open>measure (\<lambda>(mem, ys, _). (if mem then 0 else 1) + length ys)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  done
qed

definition import_monomS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'string list \<Rightarrow> (_ \<times> 'nat list \<times> ('nat, 'string) shared_vars) nres\<close>
where
  \<open>import_monomS \<A> xs = do {
  (new, _, xs, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys, \<A>). do {
      ASSERT(xs \<noteq> []);
      let x = hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then do {
        (mem, \<A>, x) \<leftarrow> import_variableS x \<A>;
        if alloc_failed mem
        then RETURN (mem, xs, ys, \<A>)
        else RETURN (mem, tl xs, ys @ [x], \<A>)
      }
      else do {
        x \<leftarrow> get_var_posS \<A> x;
        RETURN (Allocated, tl xs, ys @ [x], \<A>)
       }
    })
    (Allocated, xs, [], \<A>);
  RETURN (new, xs, \<A>)
 }\<close>

definition import_monom
  :: \<open>('nat, 'string) vars \<Rightarrow> 'string list \<Rightarrow> (memory_allocation \<times> 'string list \<times> ('nat, 'string) vars) nres\<close>
where
  \<open>import_monom \<A> xs = do {
  (new, _, xs, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _, _). \<not>alloc_failed new \<and> xs \<noteq> [])
  (\<lambda>(mem, xs, ys, \<A>). do {
  ASSERT(xs \<noteq> []);
  let x = hd xs;
    b \<leftarrow> is_new_variable x \<A>;
    if b
  then do {
    (mem, \<A>, x) \<leftarrow> import_variable x \<A>;
    if alloc_failed mem
    then RETURN (mem, xs, ys, \<A>)
    else RETURN (mem, tl xs, ys @ [x], \<A>)
    }
    else do {
    x \<leftarrow> get_var_name \<A> x;
    RETURN (mem, tl xs, ys @ [x], \<A>)
    }
    })
    (Allocated, xs, [], \<A>);
    RETURN (new, xs, \<A>)
    }\<close>

lemma import_monom_spec:
  shows \<open>import_monom \<A> xs \<le> \<Down> Id
    (SPEC(\<lambda>(new, ys, \<A>'). \<not>alloc_failed new \<longrightarrow> ys = xs \<and> set_mset \<A>' = set_mset \<A> \<union> set xs))\<close>
proof -
  define I where
    [simp]: \<open>I = (\<lambda>(new, ys, zs, \<A>'). \<not>alloc_failed new \<longrightarrow> (xs = zs @ ys \<and> set_mset \<A>' = set_mset \<A> \<union> set zs))\<close>
  show ?thesis
  unfolding import_monom_def is_new_variable_def get_var_name_def import_variable_def
  apply (refine_vcg
    WHILET_rule[where I = \<open>I\<close> and
    R = \<open>measure (\<lambda>(mem, ys, _). (if alloc_failed mem then 0 else 1) + length ys)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: neq_Nil_conv)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done
qed

definition import_polyS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow> 
    (memory_allocation \<times> ('nat list \<times> 'a)list \<times> ('nat, 'string) shared_vars) nres\<close>
  where
  \<open>import_polyS \<A> xs = do {
  (mem,_, xs, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(mem, xs, _, _). \<not>alloc_failed mem \<and> xs \<noteq> [])
    (\<lambda>(mem, xs, ys, \<A>). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (mem, x, \<A>) \<leftarrow> import_monomS \<A> x;
      if alloc_failed mem
      then RETURN (mem, xs, ys, \<A>)
      else do {
       RETURN (mem, tl xs, ys @ [(x, n)], \<A>)
      }
    }) 
    (Allocated, xs, [], \<A>);
   RETURN (mem, xs, \<A>)
 }\<close>

definition import_poly
  :: \<open>('nat, 'string) vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow>
        (memory_allocation \<times> ('string list \<times> 'a) list \<times> ('nat, 'string)vars) nres\<close>
  where
  \<open>import_poly \<A> xs0 = do {
  (new, _, xs, \<A>) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>alloc_failed new \<and> xs \<noteq> [])
  (\<lambda>(_, xs, ys, \<A>). do {
    ASSERT(xs \<noteq> []);
    let (x, n) = hd xs;
    (b, x, \<A>) \<leftarrow> import_monom \<A> x;
    if alloc_failed b
    then RETURN (b, xs, ys, \<A>)
    else do {
      RETURN (Allocated, tl xs, ys @ [(x, n)], \<A>)
    }
  })
      (Allocated, xs0, [], \<A>);
  ASSERT(\<not>alloc_failed new \<longrightarrow> xs0 = xs);
  RETURN (new, xs, \<A>)
}\<close>

lemma import_poly_spec:
  fixes \<A> :: \<open>('nat, 'string) vars\<close>
  shows \<open>import_poly \<A> xs \<le> \<Down> Id
    (SPEC(\<lambda>(new, ys, \<A>'). \<not>alloc_failed new \<longrightarrow> ys = xs \<and> set_mset \<A>' = set_mset \<A> \<union> \<Union>(set `fst ` set xs)))\<close>
proof -
  define I where
    [simp]: \<open>I = (\<lambda>(new, ys, zs, \<A>'). \<not>alloc_failed new \<longrightarrow> (xs = zs @ ys \<and>
       set_mset \<A>' = set_mset \<A> \<union> \<Union>(set ` fst ` set zs)))\<close>
  show ?thesis
    unfolding import_poly_def is_new_variable_def get_var_name_def import_variable_def
    apply (refine_vcg import_monom_spec[THEN order_trans]
      WHILET_rule[where I = \<open>I\<close> and
      R = \<open>measure (\<lambda>(mem, ys, _). (if alloc_failed mem then 0 else 1) + length ys)\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: neq_Nil_conv)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

lemma list_rel_append_single: \<open>(xs, ys) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (xs @ [x], ys @ [y]) \<in> \<langle>R\<rangle>list_rel\<close>
  by (meson list_rel_append1 list_rel_simp(4) refine_list(1))

lemma list_rel_mono: \<open>A \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (\<And>xs. xs \<in> R \<Longrightarrow> xs \<in> R') \<Longrightarrow> A \<in> \<langle>R'\<rangle>list_rel\<close>
  unfolding list_rel_def
  apply (cases A)
  by (simp add: list_all2_mono)

lemma import_monomS_import_monom:
  fixes \<V>\<D> :: \<open>('nat, 'string) vars\<close> and \<A>\<^sub>0 :: \<open>('nat, 'string)shared_vars\<close> and xs xs' :: \<open>'string list\<close>
  assumes \<open>(\<A>\<^sub>0, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in> \<langle>Id\<rangle>list_rel\<close>
  shows \<open>import_monomS \<A>\<^sub>0 xs \<le> \<Down> {((mem, xs\<^sub>0, \<A>), (mem', ys\<^sub>0, \<A>')). mem = mem' \<and> 
    (\<A>, \<A>') \<in> perfectly_shared_vars_rel \<and>  (\<not>alloc_failed mem \<longrightarrow> (xs\<^sub>0, ys\<^sub>0) \<in> perfectly_shared_monom \<A>)\<and>
    (\<not>alloc_failed mem \<longrightarrow> (\<forall>xs. xs \<in> perfectly_shared_monom \<A>\<^sub>0 \<longrightarrow> xs \<in> perfectly_shared_monom \<A>))}
    (import_monom \<V>\<D> xs')\<close>
  using assms
  unfolding import_monom_def import_monomS_def
  apply (refine_rcg WHILET_refine[where
    R = \<open>{((mem::memory_allocation, xs\<^sub>0::'string list, zs\<^sub>0::'nat list,  \<A> :: ('nat, 'string)shared_vars),
    (mem', ys\<^sub>0::'string list, zs\<^sub>0'::'string list, \<A>' :: ('nat, 'string)vars)). mem = mem' \<and>
    (\<A>, \<A>') \<in> perfectly_shared_vars_rel \<and> (\<not>alloc_failed mem \<longrightarrow> (zs\<^sub>0, zs\<^sub>0') \<in> perfectly_shared_monom \<A>) \<and>
    (xs\<^sub>0, ys\<^sub>0) \<in> \<langle>Id\<rangle>list_rel \<and>
    (\<not>alloc_failed mem \<longrightarrow> (\<forall>xs. xs \<in> perfectly_shared_monom \<A>\<^sub>0 \<longrightarrow> xs \<in> perfectly_shared_monom \<A>))}\<close>]
    import_variableS_import_variable
    is_new_variable_spec get_var_posS_spec)
  subgoal by auto
  subgoal
    by auto
  subgoal
    by auto 
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply (auto intro!: list_rel_append_single intro: list_rel_mono)
    by (metis (full_types) list_rel_mono surj_pair)
  subgoal by auto
  subgoal by auto
  subgoal using memory_allocation.exhaust_disc  by (auto intro!: list_rel_append_single intro: list_rel_mono)
  subgoal by auto
  done

abbreviation perfectly_shared_polynom
  :: \<open>('nat,'string) shared_vars \<Rightarrow> (('nat list \<times> int) list \<times> ('string list \<times> int) list) set\<close>
where
  \<open>perfectly_shared_polynom \<V> \<equiv> \<langle>perfectly_shared_monom \<V> \<times>\<^sub>r int_rel\<rangle>list_rel\<close>

abbreviation import_poly_rel :: \<open>_\<close> where
  \<open>import_poly_rel \<A>\<^sub>0 xs' \<equiv>
  {((mem, xs\<^sub>0, \<A>), (mem', ys\<^sub>0, \<A>')). mem = mem' \<and>
    (\<A>, \<A>') \<in> perfectly_shared_vars_rel \<and>  (\<not>alloc_failed mem \<longrightarrow> ys\<^sub>0 = xs' \<and> (xs\<^sub>0, ys\<^sub>0) \<in> perfectly_shared_polynom \<A>) \<and>
    (\<not>alloc_failed mem \<longrightarrow> perfectly_shared_polynom \<A>\<^sub>0 \<subseteq> perfectly_shared_polynom \<A>)}\<close>

lemma import_polyS_import_poly:
  assumes \<open>(\<A>\<^sub>0, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in>  \<langle>\<langle>Id\<rangle>list_rel\<times>\<^sub>rId\<rangle>list_rel\<close>
  shows \<open>import_polyS \<A>\<^sub>0 xs \<le> \<Down>(import_poly_rel \<A>\<^sub>0 xs)
    (import_poly \<V>\<D> xs')\<close>
  using assms
  unfolding import_poly_def import_polyS_def
  apply (refine_rcg WHILET_refine[where
    R = \<open>{((mem, zs, xs\<^sub>0, \<A>), (mem', zs', ys\<^sub>0, \<A>')). mem = mem' \<and> 
    (\<A>, \<A>') \<in> perfectly_shared_vars_rel \<and> (zs, zs') \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_rel
    \<and> (\<not>alloc_failed mem \<longrightarrow> (xs\<^sub>0, ys\<^sub>0) \<in> perfectly_shared_polynom \<A>) \<and>
    (\<not>alloc_failed mem \<longrightarrow> perfectly_shared_polynom \<A>\<^sub>0 \<subseteq> perfectly_shared_polynom \<A>)}\<close>]
    import_monomS_import_monom)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: list_rel_append1)
  subgoal for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f x1g x2g xa x'a x1h x2h x1i x2i
    x1j x2j x1k x2k
    using memory_allocation.exhaust_disc[of x1h \<open>x1h = Allocated\<close>]
    by (auto intro!: list_rel_append_single intro: list_rel_mono)
  subgoal by auto
  done



definition drop_content :: \<open>'string \<Rightarrow> ('nat, 'string) vars \<Rightarrow> ('nat, 'string) vars nres\<close>
  where
  \<open>drop_content = (\<lambda>v \<V>'. do {
    ASSERT(v \<in># \<V>');
    RETURN (remove1_mset v \<V>')
  })\<close>


definition drop_contentS :: \<open>'string \<Rightarrow> ('nat, 'string) shared_vars \<Rightarrow> ('nat, 'string) shared_vars nres\<close>
  where
  \<open>drop_contentS = (\<lambda>v (\<D>, \<V>, \<V>'). do {
    ASSERT(v \<in># dom_m \<V>');
    if count \<D> v = 1
    then do {
      let i = \<V>' \<propto> v;
      RETURN (remove1_mset v \<D>, fmdrop i \<V>, fmdrop v \<V>')
    }
    else
    RETURN (remove1_mset v \<D>, \<V>, \<V>')
  })\<close>

lemma drop_contentS_drop_content:
  assumes \<open>(\<A>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(v, v') \<in> Id\<close> 
  shows \<open>drop_contentS v \<A> \<le> \<Down>perfectly_shared_vars_rel (drop_content v' \<V>\<D>)\<close>
proof -
  have [simp]: \<open>count xs x = 1 \<Longrightarrow> y \<in># remove1_mset x xs \<longleftrightarrow> y \<in># xs \<and> x \<noteq>y\<close> for x xs y
    by (auto simp add: in_diff_count)
  have [simp]: \<open>count xs x \<noteq> 1 \<Longrightarrow> x \<in># xs \<Longrightarrow> y \<in># remove1_mset x xs \<longleftrightarrow> y \<in># xs\<close> for x xs y
    by (metis One_nat_def add_mset_remove_trivial_eq count_add_mset count_inI in_remove1_mset_neq)
  show ?thesis
    using assms
    unfolding drop_content_def drop_contentS_def
    apply refine_vcg
    apply (auto simp: perfectly_shared_vars_rel_def perfectly_shared_vars_def
      distinct_mset_dom distinct_mset_remove1_All)
    by (metis option.inject)
qed

definition perfectly_shared_strings_equal
  :: \<open>('nat, 'string) vars \<Rightarrow> 'string \<Rightarrow> 'string \<Rightarrow> bool nres\<close>
where
  \<open>perfectly_shared_strings_equal \<V> x y = do {
    ASSERT(x \<in># \<V> \<and> y \<in># \<V>);
    RETURN (x = y)
  }\<close>

definition perfectly_shared_strings_equal_l
  :: \<open>('nat,'string)shared_vars \<Rightarrow> 'nat \<Rightarrow> 'nat \<Rightarrow> bool nres\<close>
where
  \<open>perfectly_shared_strings_equal_l \<V> x y = do {
    RETURN (x = y)
  }\<close>

lemma perfectly_shared_strings_equal_l_perfectly_shared_strings_equal:
  assumes \<open>(\<A>, \<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(x, x') \<in> perfectly_shared_var_rel \<A>\<close> and
    \<open>(y, y') \<in> perfectly_shared_var_rel \<A>\<close>
  shows \<open>perfectly_shared_strings_equal_l \<A> x y \<le> \<Down>bool_rel (perfectly_shared_strings_equal \<V> x' y')\<close>
  using assms unfolding perfectly_shared_strings_equal_l_def perfectly_shared_strings_equal_def
    perfectly_shared_vars_rel_def perfectly_shared_var_rel_def br_def
  by refine_rcg
    (auto simp: perfectly_shared_vars_def simp: add_mset_eq_add_mset dest!: multi_member_split)

datatype(in -) ordered = LESS | EQUAL | GREATER | UNKNOWN

definition (in -)perfect_shared_var_order :: \<open>(nat, string)vars \<Rightarrow> string \<Rightarrow> string \<Rightarrow> ordered nres\<close> where
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


definition (in -) perfect_shared_term_order_rel_pre
  :: \<open>(nat, string) vars \<Rightarrow> string list \<Rightarrow> string list \<Rightarrow> bool\<close>
where
  \<open>perfect_shared_term_order_rel_pre \<V> xs ys \<longleftrightarrow>
    set xs \<subseteq> set_mset \<V> \<and> set ys \<subseteq> set_mset \<V>\<close>

definition (in -) perfect_shared_term_order_rel
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


lemma (in -)perfect_shared_term_order_rel_spec:
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

lemma (in-) trans_var_order_rel[simp]: \<open>trans var_order_rel\<close>
  unfolding trans_def var_order_rel_def
  apply (intro conjI impI allI)
  by (meson lexord_partial_trans trans_def trans_less_than_char)

lemma (in-) term_order_rel_irreflexive:
  \<open>(x1f, x1d) \<in> term_order_rel \<Longrightarrow> (x1d, x1f) \<in> term_order_rel \<Longrightarrow> x1f = x1d\<close>
  using lexord_trans[of x1f x1d var_order_rel x1f] lexord_irreflexive[of var_order_rel x1f]
  by simp


lemma get_var_nameS_spec:
  fixes \<D>\<V> :: \<open>('nat, 'string) vars\<close> and
    \<A> :: \<open>('nat, 'string) shared_vars\<close> and
    x' :: 'string
  assumes \<open>(\<A>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(x,x') \<in> perfectly_shared_var_rel \<A>\<close>
  shows \<open>get_var_nameS \<A> x \<le> \<Down>(Id) (get_var_name \<D>\<V> x')\<close>
  using assms unfolding get_var_nameS_def get_var_name_def
  apply refine_vcg
  apply (auto simp: perfectly_shared_var_rel_def
    perfectly_shared_vars_rel_def perfectly_shared_vars_simps br_def
    intro!: ASSERT_leI)
  done

end
