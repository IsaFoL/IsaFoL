theory EPAC_Perfectly_Shared_Vars
  imports EPAC_Checker_Specification
begin


text \<open>We now introduce sharing of variables to make a more efficient representation possible.\<close>

section \<open>Definition\<close>

definition perfectly_shared_vars
  :: \<open>'nat set \<Rightarrow> 'string set \<Rightarrow> ('nat, 'string) fmap \<times> ('string, 'nat) fmap  \<Rightarrow> bool\<close>
where
  \<open>perfectly_shared_vars D \<V> = (\<lambda>(V, V').
  D \<subseteq> set_mset (dom_m V) \<and> set_mset (dom_m V') = \<V> \<and>
  (\<forall>i \<in>#dom_m V. fmlookup V' (the (fmlookup V i)) = Some i) \<and>
  (\<forall>str \<in>#dom_m V'. fmlookup V (the (fmlookup V' str)) = Some str) \<and>
  (\<forall>i j. i\<in>#dom_m V \<longrightarrow> j\<in>#dom_m V \<longrightarrow> (fmlookup V i = fmlookup V j \<longleftrightarrow> i = j)))\<close>

abbreviation fmlookup_direct :: \<open>('a, 'b) fmap \<Rightarrow> 'a \<Rightarrow> 'b\<close> (infix "\<propto>" 70) where
  \<open>fmlookup_direct A b \<equiv> the (fmlookup A b)\<close>

lemma perfectly_shared_vars_simps:
  assumes \<open>perfectly_shared_vars D \<V> (VV')\<close>
  shows \<open>str \<in> \<V> \<longleftrightarrow> str \<in># dom_m (snd VV')\<close> and
    \<open>i \<in> D \<Longrightarrow> i \<in># dom_m (fst VV')\<close>
  using assms
  unfolding perfectly_shared_vars_def
  apply auto
  done

lemma perfectly_shared_add_new_var:
  fixes V :: \<open>('nat, 'string) fmap\<close> and
    v :: \<open>'string\<close>
  assumes \<open>perfectly_shared_vars D \<V> (V, V')\<close> and
    \<open>v \<notin> \<V>\<close> and
    k_notin[simp]: \<open>k \<notin># dom_m V\<close>
  shows \<open>perfectly_shared_vars D (insert v \<V>) (fmupd k v V, fmupd v k V')\<close>
proof -
  have
    DV: \<open>D \<subseteq> set_mset (dom_m V)\<close> and
    V'\<V>: \<open>set_mset (dom_m V') = \<V>\<close> and
    map: \<open>\<And>i. i \<in>#dom_m V \<Longrightarrow> fmlookup V' (the (fmlookup V i)) = Some i\<close> and
    map_str: \<open>\<And>str. str \<in>#dom_m V' \<Longrightarrow> fmlookup V (the (fmlookup V' str)) = Some str\<close> and
    perfect: \<open>\<And>i j. i\<in>#dom_m V \<Longrightarrow> j\<in>#dom_m V \<Longrightarrow> fmlookup V i = fmlookup V j \<longleftrightarrow> i = j\<close>
    using assms unfolding perfectly_shared_vars_def
    by auto
  have v_notin[simp]: \<open>v \<notin># dom_m V'\<close>
    using V'\<V> assms(2) by blast
  show ?thesis
    unfolding perfectly_shared_vars_def prod.simps
  proof (intro conjI allI ballI impI)
    show \<open>D \<subseteq> set_mset (dom_m (fmupd k v V))\<close>
      using DV by auto
    show \<open>set_mset (dom_m (fmupd v k V')) = insert v \<V>\<close>
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

lemma perfectly_shared_add_del_vars:
  fixes V :: \<open>('nat, 'string) fmap\<close> and
    v :: \<open>'string\<close>
  assumes \<open>perfectly_shared_vars D \<V> (V, V')\<close> and
    \<open>D' \<subseteq> D\<close>
  shows \<open>perfectly_shared_vars D' (\<V>) (V, V')\<close>
  using assms
  unfolding perfectly_shared_vars_def
  by blast


section \<open>Refinement\<close>

datatype memory_allocation =
  Allocated | alloc_failed: Mem_Out

type_synonym ('nat, 'string) shared_vars = \<open>('nat, 'string) fmap \<times> ('string, 'nat) fmap\<close>
type_synonym ('nat, 'string) vars = \<open>'nat set \<times> 'string set\<close>

definition perfectly_shared_var_rel :: \<open>('nat,'string) shared_vars \<Rightarrow> ('nat \<times> 'string) set\<close> where
  \<open>perfectly_shared_var_rel = (\<lambda>(\<V>, \<V>'). br (\<lambda>i. \<V> \<propto> i) (\<lambda>i. i \<in># dom_m \<V>))\<close>

definition perfectly_shared_vars_rel :: \<open>(('nat,'string) shared_vars \<times> ('nat, 'string) vars) set\<close>
where
  \<open>perfectly_shared_vars_rel = {(\<A>, (\<D>, \<V>)). perfectly_shared_vars \<D> \<V> \<A>}\<close>

definition import_variable
  :: \<open>'string \<Rightarrow> ('nat, 'string) fmap \<times> ('string, 'nat) fmap \<Rightarrow>
  (memory_allocation \<times> ('nat, 'string) fmap \<times> ('string, 'nat) fmap) nres\<close>
where
  \<open>import_variable v = (\<lambda>(\<V>, \<V>'). do {
    (mem, k) \<leftarrow> SPEC(\<lambda>(mem, k::'nat). \<not>alloc_failed mem \<longrightarrow> k \<notin># dom_m \<V>);
    if alloc_failed mem then RETURN (mem, (\<V>, \<V>'))
    else RETURN (Allocated, (fmupd k v \<V>, fmupd v k \<V>'))
  })\<close>

definition is_new_variableS :: \<open>'string \<Rightarrow> ('nat, 'string) shared_vars \<Rightarrow> bool nres\<close> where
  \<open>is_new_variableS v = (\<lambda>(\<V>, \<V>').
  RETURN (v \<notin># dom_m \<V>')
  )\<close>

definition is_new_variable :: \<open>'string \<Rightarrow> ('nat, 'string) vars \<Rightarrow> bool nres\<close> where
  \<open>is_new_variable v = (\<lambda>(\<V>, \<V>').
    RETURN (v \<notin> \<V>')
  )\<close>

lemma is_new_variable_spec:
  assumes \<open>(\<A>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> \<open>(v,v') \<in> Id\<close>
  shows \<open>is_new_variableS v \<A> \<le> \<Down>bool_rel (is_new_variable v' \<D>\<V>)\<close>
  using assms
  unfolding is_new_variable_def is_new_variableS_def
  by (auto simp: perfectly_shared_vars_rel_def
    perfectly_shared_vars_simps split: prod.splits)


definition get_var_name :: \<open>('nat, 'string) vars \<Rightarrow> 'string \<Rightarrow>  'string nres\<close> where
  \<open>get_var_name \<V> x = do {
    ASSERT(x \<in> snd \<V>);
    RETURN x
  }\<close>
definition get_var_nameS :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'string \<Rightarrow> 'nat nres\<close> where
  \<open>get_var_nameS \<V> x = do {
    ASSERT(x \<in># dom_m (snd \<V>));
    RETURN (snd \<V> \<propto> x)
  }\<close>

lemma get_var_nameS_spec:
  fixes \<D>\<V> :: \<open>('nat, 'string) vars\<close> and
    \<A> :: \<open>('nat, 'string) shared_vars\<close> and
    x :: 'string
  assumes \<open>(\<A>, \<D>\<V>) \<in> perfectly_shared_vars_rel\<close> and
    \<open>(x,x') \<in> Id\<close>
  shows \<open>get_var_nameS \<A> x \<le> \<Down>(perfectly_shared_var_rel \<A>) (get_var_name \<D>\<V> x')\<close>
  using assms unfolding get_var_nameS_def get_var_name_def
  apply refine_vcg
  apply (auto simp: perfectly_shared_var_rel_def
    perfectly_shared_vars_rel_def perfectly_shared_vars_simps br_def
    intro!: ASSERT_leI)
  apply (simp_all add: perfectly_shared_vars_def in_dom_m_lookup_iff)
  using indom_mI apply force
  by (meson indom_mI)

abbreviation perfectly_shared_monom
  :: \<open>('nat,'string) shared_vars \<Rightarrow> ('nat list \<times> 'string list) set\<close>
where
  \<open>perfectly_shared_monom \<V> \<equiv> \<langle>perfectly_shared_var_rel \<V>\<rangle>list_rel \<close>

definition import_monomS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> 'string list \<Rightarrow> (bool \<times> 'nat list) nres\<close>
where
  \<open>import_monomS \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let x = hd xs;
      b \<leftarrow> is_new_variableS x \<A>;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        x \<leftarrow> get_var_nameS \<A> x;
        RETURN (False, tl xs, ys @ [x])
       }
    })
    (False, xs, []);
  RETURN (new, xs)
 }\<close>

definition import_monom
  :: \<open>('nat, 'string) vars \<Rightarrow> 'string list \<Rightarrow> (bool \<times> 'string list) nres\<close>
where
  \<open>import_monom \<A> xs = do {
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

lemma import_monom_spec:
  shows \<open>import_monom \<A> xs \<le> \<Down> Id
    (SPEC(\<lambda>(new, ys). (new \<longrightarrow> \<not>set xs \<subseteq> snd \<A>) \<and>
      \<not>new \<longrightarrow> ys = xs))\<close>
  unfolding import_monom_def is_new_variable_def get_var_name_def
  apply (refine_vcg
    WHILET_rule[where I = \<open>(\<lambda>(new, ys, zs). (\<not>new \<longrightarrow> xs = zs @ ys) \<and> (\<not>new \<longrightarrow> set zs \<subseteq> snd \<A>) \<and>
     (new \<longrightarrow> \<not>set xs \<subseteq> snd \<A>))\<close> and
    R = \<open>measure (\<lambda>(_, ys, _). length ys)\<close>])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
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
  done

lemma import_monomS_import_monom:
  assumes \<open>(\<A>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in> Id\<close>
  shows \<open>import_monomS \<A> xs \<le> \<Down>(bool_rel \<times>\<^sub>r perfectly_shared_monom \<A>)
    (import_monom \<V>\<D> xs')\<close>
  using assms
  unfolding import_monom_def import_monomS_def
  apply (refine_rcg WHILET_refine[where R = \<open>bool_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r perfectly_shared_monom \<A>\<close>]
    is_new_variable_spec get_var_nameS_spec)
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

 definition import_polyS
  :: \<open>('nat, 'string) shared_vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow> (bool \<times> ('nat list \<times> 'a)list) nres\<close>
where
  \<open>import_polyS \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
    (\<lambda>(_, xs, ys). do {
      ASSERT(xs \<noteq> []);
      let (x, n) = hd xs;
      (b, x) \<leftarrow> import_monomS \<A> x;
      if b
      then RETURN (True, tl xs, ys)
      else do {
        RETURN (False, tl xs, ys @ [(x, n)])
       }
    })
    (False, xs, []);
  RETURN (new, xs)
 }\<close>

definition import_poly
  :: \<open>('nat, 'string) vars \<Rightarrow> ('string list \<times> 'a) list \<Rightarrow> (bool \<times> ('string list \<times> 'a) list) nres\<close>
where
  \<open>import_poly \<A> xs = do {
  (new, _, xs) \<leftarrow> WHILE\<^sub>T (\<lambda>(new, xs, _). \<not>new \<and> xs \<noteq> [])
  (\<lambda>(_, xs, ys). do {
    ASSERT(xs \<noteq> []);
    let (x, n) = hd xs;
    (b, x) \<leftarrow> import_monom \<A> x;
    if b
    then RETURN (True, tl xs, ys)
      else do {
      RETURN (False, tl xs, ys @ [(x, n)])
    }
    })
    (False, xs, []);
  RETURN (new, xs)
}\<close>


lemma import_polyS_import_poly:
  assumes \<open>(\<A>, \<V>\<D>) \<in> perfectly_shared_vars_rel\<close> \<open>(xs, xs') \<in> Id\<close>
  shows \<open>import_polyS \<A> xs \<le> \<Down>(bool_rel \<times>\<^sub>r \<langle>perfectly_shared_monom \<A> \<times>\<^sub>r Id\<rangle>list_rel)
    (import_poly \<V>\<D> xs')\<close>
  using assms
  unfolding import_poly_def import_polyS_def
  apply (refine_rcg WHILET_refine[where
    R = \<open>bool_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>perfectly_shared_monom \<A> \<times>\<^sub>r Id\<rangle>list_rel\<close>]
    import_monomS_import_monom)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (force simp: list_rel_append1)
  subgoal by auto
  done

end