theory IsaSAT_Restart_Heuristics
  imports Watched_Literals_Watch_List_Domain_Restart IsaSAT_Setup IsaSAT_VMTF
    IsaSAT_Inner_Propagation (* TODO remove dependency *)
    "../lib/Explorer"
begin

text \<open>
  This is a list of comments (how does it work for glucose and cadical) to prepare the future
  refinement:
  \<^enum> Reduction
     \<^item> every 2000+300*n (rougly since inprocessing changes the real number, cadical)
           (split over initialisation file); don't restart if level < 2 or if the level is less
       than the fast average
     \<^item> curRestart * nbclausesbeforereduce;
          curRestart = (conflicts / nbclausesbeforereduce) + 1 (glucose)
  \<^enum> Killed
     \<^item> half of the clauses that \<^bold>\<open>can\<close> be deleted (i.e., not used since last restart), not strictly
       LBD, but a probability of being useful.
     \<^item> half of the clauses
  \<^enum> Restarts:
     \<^item> EMA-14, aka restart if enough clauses and slow\_glue\_avg * opts.restartmargin > fast\_glue (file ema.cpp)
     \<^item> (lbdQueue.getavg() * K) > (sumLBD / conflictsRestarts),
       \<^text>\<open>conflictsRestarts > LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid() && trail.size() > R * trailQueue.getavg()\<close>
\<close>

definition GC_clauses :: \<open>nat clauses_l \<Rightarrow> nat clauses_l \<Rightarrow> (nat clauses_l \<times> (nat \<Rightarrow> nat option)) nres\<close> where
\<open>GC_clauses N N' = do {
  xs \<leftarrow> SPEC(\<lambda>xs. set_mset (dom_m N) \<subseteq> set xs);
  (N, N', m) \<leftarrow> nfoldli
    xs
    (\<lambda>(N, N', m). True)
    (\<lambda>C (N, N', m).
       if C \<in># dom_m N
       then do {
         C' \<leftarrow> SPEC(\<lambda>i. i \<notin># dom_m N');
	 RETURN (fmdrop C N, fmupd C' (N \<propto> C, irred N C) N', m(C \<mapsto> C'))
       }
       else
         RETURN (N, N', m))
    (N, N', (\<lambda>_. None));
  RETURN (N', m)
}\<close>


inductive GC_remap
  :: \<open>('a, 'b) fmap \<times> ('a \<Rightarrow> 'c option) \<times> ('c, 'b) fmap \<Rightarrow>  ('a, 'b) fmap \<times> ('a \<Rightarrow> 'c option) \<times> ('c, 'b) fmap \<Rightarrow> bool\<close>
where
remap_cons:
  \<open>GC_remap (N, m, new) (fmdrop C N, m(C \<mapsto> C'), fmupd C' (the (fmlookup N C)) new)\<close>
   if \<open>C' \<notin># dom_m new\<close> and
      \<open>C \<in># dom_m N\<close> and
      \<open>C \<notin> dom m\<close> and
      \<open>C' \<notin> ran m\<close>

lemma GC_remap_ran_m_old_new:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> ran_m old + ran_m new = ran_m old' + ran_m new'\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)

lemma GC_remap_ran_m_remap:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m old \<Longrightarrow> C \<notin># dom_m old' \<Longrightarrow>
         m' C \<noteq>	 None \<and>
         fmlookup new' (the (m' C)) = fmlookup old C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)

lemma GC_remap_ran_m_no_rewrite_map:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> C \<notin># dom_m old \<Longrightarrow> m' C = m C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin split: if_splits)


lemma GC_remap_ran_m_no_rewrite_fmap:
  \<open>GC_remap (old, m, new) (old', m', new')  \<Longrightarrow> C \<in># dom_m new \<Longrightarrow> C \<in># dom_m new' \<and> fmlookup new C = fmlookup new' C\<close>
  by (induction "(old, m, new)" "(old', m', new')" rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin)


lemma rtranclp_GC_remap_ran_m_no_rewrite_fmap:
  \<open>GC_remap\<^sup>*\<^sup>* S S'  \<Longrightarrow> C \<in># dom_m (snd (snd S)) \<Longrightarrow> C \<in># dom_m (snd (snd S')) \<and> fmlookup (snd (snd S)) C = fmlookup (snd (snd S')) C\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_no_rewrite_fmap)

lemma GC_remap_ran_m_no_rewrite:
  \<open>GC_remap S S'  \<Longrightarrow> C \<in># dom_m (fst S) \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow>
         fmlookup (fst S) C = fmlookup (fst S') C\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma GC_remap_ran_m_lookup_kept:
  assumes
    \<open>GC_remap\<^sup>*\<^sup>* S y\<close> and
    \<open>GC_remap y z\<close> and
    \<open>C \<in># dom_m (fst S)\<close> and
    \<open>C \<in># dom_m (fst z)\<close> and
    \<open>C \<notin># dom_m (fst y)\<close>
  shows \<open>fmlookup (fst S) C = fmlookup (fst z) C\<close>
  using assms by (smt GC_remap.cases fmlookup_drop fst_conv in_dom_m_lookup_iff)

lemma rtranclp_GC_remap_ran_m_no_rewrite:
  \<open>GC_remap\<^sup>*\<^sup>*  S S'  \<Longrightarrow> C \<in># dom_m (fst S) \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow>
         fmlookup (fst S) C = fmlookup (fst S') C\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept)
  done

lemma GC_remap_ran_m_no_lost:
  \<open>GC_remap S S'  \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma rtranclp_GC_remap_ran_m_no_lost:
  \<open>GC_remap\<^sup>*\<^sup>* S S'  \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
  done


lemma GC_remap_ran_m_no_new_lost:
  \<open>GC_remap S S'  \<Longrightarrow> dom (fst (snd S)) \<subseteq> set_mset (dom_m (fst S)) \<Longrightarrow> dom (fst (snd S')) \<subseteq> set_mset (dom_m (fst S))\<close>
  by (induction rule: GC_remap.induct)
    (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin distinct_mset_dom distinct_mset_set_mset_remove1_mset
      dest: GC_remap_ran_m_remap)

lemma rtranclp_GC_remap_ran_m_no_new_lost:
  \<open>GC_remap\<^sup>*\<^sup>* S S'  \<Longrightarrow> dom (fst (snd S)) \<subseteq> set_mset (dom_m (fst S)) \<Longrightarrow> dom (fst (snd S')) \<subseteq> set_mset (dom_m (fst S))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    apply (cases \<open>C \<in># dom_m (fst y)\<close>)
    apply (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
	apply (smt GC_remap_ran_m_no_rewrite_map contra_subsetD domI prod.collapse rtranclp_GC_remap_ran_m_no_lost)
	apply (smt GC_remap_ran_m_no_rewrite_map contra_subsetD domI prod.collapse rtranclp_GC_remap_ran_m_no_lost)
	done
  done


lemma rtranclp_GC_remap_map_ran:
  assumes
    \<open>GC_remap\<^sup>*\<^sup>* S S'\<close> and
    \<open>(the \<circ>\<circ> fst) (snd S) `# mset_set (dom (fst (snd S))) = dom_m (snd (snd S))\<close> and
    \<open>finite (dom (fst (snd S)))\<close>
  shows \<open>finite (dom (fst (snd S'))) \<and>
         (the \<circ>\<circ> fst) (snd S') `# mset_set (dom (fst (snd S'))) = dom_m (snd (snd S'))\<close>
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z) note star = this(1) and st = this(2) and IH = this(3) and H = this(4-)
  from st
  show ?case
  proof cases
    case (remap_cons C' new C N m)
    have \<open>C \<notin> dom m\<close>
      using step remap_cons by auto
   then have [simp]: \<open>{#the (if x = C then Some C' else m x). x \<in># mset_set (dom m)#} =
     {#the (m x). x \<in># mset_set (dom m)#}\<close>
    apply (auto intro!: image_mset_cong split: if_splits)
    by (metis empty_iff finite_set_mset_mset_set local.remap_cons(5) mset_set.infinite set_mset_empty)

    show ?thesis
      using step remap_cons
      by (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin
        dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost dest: )
  qed
qed


lemma rtranclp_GC_remap_ran_m_no_new_map:
  \<open>GC_remap\<^sup>*\<^sup>*  S S'  \<Longrightarrow> C \<in># dom_m (fst S') \<Longrightarrow> C \<in># dom_m (fst S)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (cases \<open>C \<in># dom_m (fst y)\<close>)
      (auto simp: ran_m_lf_fmdrop ran_m_mapsto_upd_notin dest: GC_remap_ran_m_remap GC_remap_ran_m_no_rewrite
        intro: GC_remap_ran_m_lookup_kept GC_remap_ran_m_no_lost)
  done

lemma remap_cons2:
  assumes
      \<open>C' \<notin># dom_m new\<close> and
      \<open>C \<in># dom_m N\<close> and
      \<open>(the \<circ>\<circ> fst) (snd (N, m, new)) `# mset_set (dom (fst (snd (N, m, new)))) = dom_m (snd (snd (N, m, new)))\<close> and
      \<open>\<And>x. x \<in># dom_m (fst (N, m, new)) \<Longrightarrow> x \<notin> dom (fst (snd (N, m, new)))\<close> and
      \<open>finite (dom m)\<close>
  shows
    \<open>GC_remap (N, m, new) (fmdrop C N, m(C \<mapsto> C'), fmupd C' (the (fmlookup N C)) new)\<close>
proof -
  have 3: \<open>C \<in> dom m \<Longrightarrow> False\<close>
    apply (drule mk_disjoint_insert)
    using assms
    apply (auto 5 5 simp: ran_def)
    done

  have 4: \<open>False\<close> if C': \<open>C' \<in> ran m\<close>
  proof -
    obtain a where a: \<open>a \<in> dom m\<close> and [simp]: \<open>m a = Some C'\<close>
      using that C' unfolding ran_def
      by auto
    show False
      using mk_disjoint_insert[OF a] assms by (auto simp: union_single_eq_member)
  qed

  show ?thesis
    apply (rule remap_cons)
    apply (rule assms(1))
    apply (rule assms(2))
    apply (use 3 in fast)
    apply (use 4 in fast)
    done
qed


inductive_cases GC_remapE: \<open>GC_remap S T\<close>

lemma rtranclp_GC_remap_finite_map:
  \<open>GC_remap\<^sup>*\<^sup>*  S S'  \<Longrightarrow> finite (dom (fst (snd S))) \<Longrightarrow> finite (dom (fst (snd S')))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z
    by (auto elim: GC_remapE)
  done


lemma rtranclp_GC_remap_old_dom_map:
  \<open>GC_remap\<^sup>*\<^sup>*  R S  \<Longrightarrow> (\<And>x. x \<in># dom_m (fst R) \<Longrightarrow> x \<notin> dom (fst (snd R))) \<Longrightarrow>
       (\<And>x. x \<in># dom_m (fst S) \<Longrightarrow> x \<notin> dom (fst (snd S)))\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for y z x
    by (fastforce elim!: GC_remapE simp: distinct_mset_dom distinct_mset_set_mset_remove1_mset)
  done

lemma remap_cons2_rtranclp:
  assumes
      \<open>(the \<circ>\<circ> fst) (snd R) `# mset_set (dom (fst (snd R))) = dom_m (snd (snd R))\<close> and
      \<open>\<And>x. x \<in># dom_m (fst R) \<Longrightarrow> x \<notin> dom (fst (snd R))\<close> and
      \<open>finite (dom (fst (snd R)))\<close> and
      st: \<open>GC_remap\<^sup>*\<^sup>* R S\<close> and
      C': \<open>C' \<notin># dom_m (snd (snd S))\<close> and
      C: \<open>C \<in># dom_m (fst S)\<close>
  shows
    \<open>GC_remap\<^sup>*\<^sup>* R (fmdrop C (fst S), (fst (snd S))(C \<mapsto> C'), fmupd C' (the (fmlookup (fst S) C)) (snd (snd S)))\<close>
proof -
  have
    1: \<open>(the \<circ>\<circ> fst) (snd S) `# mset_set (dom (fst (snd S))) = dom_m (snd (snd S))\<close> and
    2: \<open>\<And>x. x \<in># dom_m (fst S) \<Longrightarrow> x \<notin> dom (fst (snd S))\<close> and
    3: \<open>finite (dom (fst (snd S)))\<close>
      using assms(1) assms(3) assms(4) rtranclp_GC_remap_map_ran apply blast
     apply (meson assms(2) assms(4) rtranclp_GC_remap_old_dom_map)
    using assms(3) assms(4) rtranclp_GC_remap_finite_map by blast
  have 5: \<open>GC_remap S
     (fmdrop C (fst S), (fst (snd S))(C \<mapsto> C'), fmupd C' (the (fmlookup (fst S) C)) (snd (snd S)))\<close>
    using remap_cons2[OF C' C, of \<open>(fst (snd S))\<close>] 1 2 3 by (cases S) auto
  show ?thesis
    using 5 st by simp
qed

lemma (in -) fmdom_fmrestrict_set: \<open>fmdrop xa (fmrestrict_set s N) = fmrestrict_set (s - {xa}) N\<close>
  by (rule fmap_ext_fmdom)
   (auto simp: fset_fmdom_fmrestrict_set fmember.rep_eq notin_fset)

lemma (in -) GC_clauses_GC_remap:
  \<open>GC_clauses N fmempty \<le> SPEC(\<lambda>(N'', m). GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, m, N''))\<close>
proof -
  let ?remap = \<open>(GC_remap)\<^sup>*\<^sup>*  (N, \<lambda>_. None, fmempty)\<close>
  note remap = remap_cons2_rtranclp[of \<open>(N, \<lambda>_. None, fmempty)\<close>, of \<open>(a, b, c)\<close> for a b c, simplified]
  define I where
    \<open>I a b \<equiv> (\<lambda>(old :: nat clauses_l, new :: nat clauses_l, m :: nat \<Rightarrow> nat option).
      ?remap (old, m, new) \<and>
      set_mset (dom_m old) \<subseteq> set b)\<close>
      for a b :: \<open>nat list\<close>
  have I0: \<open>set_mset (dom_m N) \<subseteq> set x \<Longrightarrow> I [] x (N, fmempty, \<lambda>_. None)\<close> for x
    unfolding I_def
    by (auto intro!: fmap_ext_fmdom simp: fset_fmdom_fmrestrict_set fmember.rep_eq notin_fset dom_m_def)

  have I_drop: \<open>I (l1 @ [xa]) l2
       (fmdrop xa a, fmupd xb (a \<propto> xa, irred a xa) aa, ba(xa \<mapsto> xb))\<close>
  if
    \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
    \<open>x = l1 @ xa # l2\<close> and
    \<open>I l1 (xa # l2) \<sigma>\<close> and
    \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
    \<open>\<sigma> = (a, b)\<close> and
    \<open>b = (aa, ba)\<close> and
    \<open>xa \<in># dom_m a\<close> and
    \<open>xb \<notin># dom_m aa\<close>
    for x xa l1 l2 \<sigma> a b aa ba xb
  proof -
    have \<open>insert xa (set l2) - set l1 - {xa} = set l2 - insert xa (set l1)\<close>
      by auto
    have \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmdrop xa a, ba(xa \<mapsto> xb), fmupd xb (the (fmlookup a xa)) aa)\<close>
      by (rule remap)
        (use that in \<open>auto simp: I_def\<close>)
    then show ?thesis
      using that distinct_mset_dom[of a] distinct_mset_dom[of aa] unfolding I_def prod.simps
      apply (auto dest!: mset_le_subtract[of \<open>dom_m _\<close> _ \<open>{#xa#}\<close>] simp: mset_set.insert_remove
         )
      by (metis Diff_empty Diff_insert0 add_mset_remove_trivial finite_set_mset finite_set_mset_mset_set insert_subset_eq_iff mset_set.remove set_mset_mset subseteq_remove1)
  qed


  have I_notin: \<open>I (l1 @ [xa]) l2 (a, aa, ba)\<close>
    if
      \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
      \<open>x = l1 @ xa # l2\<close> and
      \<open>I l1 (xa # l2) \<sigma>\<close> and
      \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
      \<open>\<sigma> = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>xa \<notin># dom_m a\<close>
      for x xa l1 l2 \<sigma> a b aa ba
  proof -
    show ?thesis
      using that unfolding I_def
      by (auto dest!: multi_member_split)
  qed

  have early_break: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
     if
       \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
       \<open>x = l1 @ l2\<close> and
       \<open>I l1 l2 \<sigma>\<close> and
       \<open>\<not> (case \<sigma> of (N, N', m) \<Rightarrow> True)\<close> and
       \<open>\<sigma> = (a, b)\<close> and
       \<open>b = (aa, ba)\<close> and
       \<open>(aa, ba) = (x1, x2)\<close>
      for x l1 l2 \<sigma> a b aa ba x1 x2
   proof -
     show ?thesis using that by auto
   qed

  have final_rel: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
  if
    \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
    \<open>I x [] \<sigma>\<close> and
    \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
    \<open>\<sigma> = (a, b)\<close> and
    \<open>b = (aa, ba)\<close> and
    \<open>(aa, ba) = (x1, x2)\<close>
  proof -
    show \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
      using that
      by (auto simp: I_def)
  qed
  have final_rel: \<open>GC_remap\<^sup>*\<^sup>* (N, Map.empty, fmempty) (fmempty, x2, x1)\<close>
    if
      \<open>set_mset (dom_m N) \<subseteq> set x\<close> and
      \<open>I x [] \<sigma>\<close> and
      \<open>case \<sigma> of (N, N', m) \<Rightarrow> True\<close> and
      \<open>\<sigma> = (a, b)\<close> and
      \<open>b = (aa, ba)\<close> and
      \<open>(aa, ba) = (x1, x2)\<close>
    for x \<sigma> a b aa ba x1 x2
    using that
    by (auto simp: I_def)
  show ?thesis
    unfolding GC_clauses_def
    apply (refine_vcg nfoldli_rule[where I = I])
    subgoal by (rule I0)
    subgoal by (rule I_drop)
    subgoal by (rule I_notin)
    \<comment> \<open>Final properties:\<close>
    subgoal for x l1 l2 \<sigma> a b aa ba x1 x2
      by (rule early_break)
    subgoal
      by (rule final_rel) assumption+
    done
qed

definition twl_st_heur_restart :: \<open>(twl_st_wl_heur \<times> nat twl_st_wl) set\<close> where
\<open>twl_st_heur_restart =
  {((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts),
     (M, N, D, NE, UE, Q, W)).
    (M', M) \<in> trail_pol (all_init_atms N NE) \<and>
    valid_arena N' N (set vdom) \<and>
    (D', D) \<in> option_lookup_clause_rel (all_init_atms N NE) \<and>
    (D = None \<longrightarrow> j \<le> length M) \<and>
    Q = uminus `# lit_of `# mset (drop j (rev M)) \<and>
    (W', W) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_init_atms N NE)) \<and>
    vm \<in> isa_vmtf (all_init_atms N NE) M \<and>
    phase_saving (all_init_atms N NE) \<phi> \<and>
    no_dup M \<and>
    clvls \<in> counts_maximum_level M D \<and>
    cach_refinement_empty (all_init_atms N NE) cach \<and>
    out_learned M D outl \<and>
    lcount = size (learned_clss_lf N) \<and>
    vdom_m (all_init_atms N NE)  W N \<subseteq> set vdom \<and>
    set avdom \<subseteq> set vdom \<and>
    isasat_input_bounded (all_init_atms N NE) \<and>
    isasat_input_nempty (all_init_atms N NE)
  }\<close>


definition clause_score_ordering where
  \<open>clause_score_ordering = (\<lambda>(lbd, act) (lbd', act'). lbd < lbd' \<or> (lbd = lbd' \<and> act = act'))\<close>

lemma clause_score_ordering_hnr[sepref_fr_rules]:
  \<open>(uncurry (return oo clause_score_ordering), uncurry (RETURN oo clause_score_ordering)) \<in>
    (uint32_nat_assn *a uint32_nat_assn)\<^sup>k *\<^sub>a (uint32_nat_assn *a uint32_nat_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  by sepref_to_hoare (sep_auto simp: clause_score_ordering_def uint32_nat_rel_def br_def
      nat_of_uint32_less_iff)


lemma unbounded_id: \<open>unbounded (id :: nat \<Rightarrow> nat)\<close>
  by (auto simp: bounded_def) presburger

global_interpretation twl_restart_ops id
  by unfold_locales

global_interpretation twl_restart id
  by standard (rule unbounded_id)

text \<open>
  We first fix the function that proves termination. We don't take the ``smallest'' function
  possible (other possibilites that are growing slower include \<^term>\<open>\<lambda>(n::nat). n >> 50\<close>).
  Remark that this scheme is not compatible with Luby (TODO: use Luby restart scheme every once
  in a while like CryptoMinisat?)
\<close>

lemma get_slow_ema_heur_alt_def:
   \<open>RETURN o get_slow_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN sema)\<close>
  by auto

sepref_definition get_slow_ema_heur_fast_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_slow_ema_heur_slow_code
  is \<open>RETURN o get_slow_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_slow_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_slow_ema_heur_fast_code.refine[sepref_fr_rules]
  get_slow_ema_heur_slow_code.refine[sepref_fr_rules]


lemma get_fast_ema_heur_alt_def:
   \<open>RETURN o get_fast_ema_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, lcount). RETURN fema)\<close>
  by auto

sepref_definition get_fast_ema_heur_fast_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_fast_ema_heur_slow_code
  is \<open>RETURN o get_fast_ema_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a ema_assn\<close>
  unfolding get_fast_ema_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_fast_ema_heur_slow_code.refine[sepref_fr_rules]
  get_fast_ema_heur_fast_code.refine[sepref_fr_rules]


fun (in -) get_conflict_count_since_last_restart_heur :: \<open>twl_st_wl_heur \<Rightarrow> uint64\<close> where
  \<open>get_conflict_count_since_last_restart_heur (_, _, _, _, _, _, _, _, _, _, _, _, _, _, (ccount, _), _)
      = ccount\<close>

lemma (in -) get_counflict_count_heur_alt_def:
   \<open>RETURN o get_conflict_count_since_last_restart_heur = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, (ccount, _), lcount). RETURN ccount)\<close>
  by auto

sepref_definition get_conflict_count_since_last_restart_heur_fast_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_conflict_count_since_last_restart_heur_slow_code
  is \<open>RETURN o get_conflict_count_since_last_restart_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  unfolding get_counflict_count_heur_alt_def isasat_unbounded_assn_def
  by sepref

declare get_conflict_count_since_last_restart_heur_fast_code.refine[sepref_fr_rules]
  get_conflict_count_since_last_restart_heur_slow_code.refine[sepref_fr_rules]

lemma get_learned_count_alt_def:
   \<open>RETURN o get_learned_count = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). RETURN lcount)\<close>
  by auto

sepref_definition get_learned_count_fast_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_bounded_assn_def
  by sepref

sepref_definition get_learned_count_slow_code
  is \<open>RETURN o get_learned_count\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn\<close>
  unfolding get_learned_count_alt_def isasat_unbounded_assn_def
  by sepref

declare get_learned_count_fast_code.refine[sepref_fr_rules]
  get_learned_count_slow_code.refine[sepref_fr_rules]

definition (in -) find_local_restart_target_level_int_inv where
  \<open>find_local_restart_target_level_int_inv ns cs =
     (\<lambda>(brk, i). i \<le> length cs \<and> length cs < uint32_max)\<close>

definition find_local_restart_target_level_int
   :: \<open>trail_pol \<Rightarrow> isa_vmtf_remove_int \<Rightarrow> nat nres\<close>
where
  \<open>find_local_restart_target_level_int =
     (\<lambda>(M, xs, lvls, reasons, k, cs) ((ns :: nat_vmtf_node list, m :: nat, fst_As::nat, lst_As::nat,
        next_search::nat option), _). do {
     (brk, i) \<leftarrow> WHILE\<^sub>T\<^bsup>find_local_restart_target_level_int_inv ns cs\<^esup>
        (\<lambda>(brk, i). \<not>brk \<and> i < length_u cs)
        (\<lambda>(brk, i). do {
           ASSERT(i < length cs);
           let t = (cs  ! i);
	   ASSERT(t < length M);
	   let L = atm_of (M ! t);
           ASSERT(L < length ns);
           let brk = stamp (ns ! L) < m;
           RETURN (brk, if brk then i else i+one_uint32_nat)
         })
        (False, zero_uint32_nat);
    RETURN i
   })\<close>

sepref_definition find_local_restart_target_level_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

sepref_definition find_local_restart_target_level_fast_code
  is \<open>uncurry find_local_restart_target_level_int\<close>
  :: \<open>trail_pol_fast_assn\<^sup>k *\<^sub>a vmtf_remove_conc\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_int_inv_def
  by sepref

declare find_local_restart_target_level_code.refine[sepref_fr_rules]
  find_local_restart_target_level_fast_code.refine[sepref_fr_rules]

definition find_local_restart_target_level where
  \<open>find_local_restart_target_level M _ = SPEC(\<lambda>i. i \<le> count_decided M)\<close>

lemma find_local_restart_target_level_alt_def:
  \<open>find_local_restart_target_level M vm = do {
      (b, i) \<leftarrow> SPEC(\<lambda>(b::bool, i). i \<le> count_decided M);
       RETURN i
    }\<close>
  unfolding find_local_restart_target_level_def by (auto simp: RES_RETURN_RES2 uncurry_def)


lemma find_local_restart_target_level_int_find_local_restart_target_level:
   \<open>(uncurry find_local_restart_target_level_int, uncurry find_local_restart_target_level) \<in>
     [\<lambda>(M, vm). vm \<in> isa_vmtf \<A> M]\<^sub>f trail_pol \<A> \<times>\<^sub>r Id \<rightarrow> \<langle>nat_rel\<rangle>nres_rel\<close>
  unfolding find_local_restart_target_level_int_def find_local_restart_target_level_alt_def
    uncurry_def Let_def
  apply (intro frefI nres_relI)
  apply clarify
  subgoal for a aa ab ac ad b ae af ag ah ba bb ai aj ak al am bc bd
    apply (refine_rcg WHILEIT_rule[where R = \<open>measure (\<lambda>(brk, i). (If brk 0 1) + length b - i)\<close>]
        assert.ASSERT_leI)
    subgoal by auto
    subgoal
      unfolding find_local_restart_target_level_int_inv_def
      by (auto simp: trail_pol_alt_def control_stack_length_count_dec)
    subgoal by auto
    subgoal by (auto simp: trail_pol_alt_def intro: control_stack_le_length_M)
    subgoal for s x1 x2
      by (subgoal_tac \<open>a ! (b ! x2) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A>\<close>)
        (auto simp: trail_pol_alt_def rev_map lits_of_def rev_nth
            vmtf_def atms_of_def isa_vmtf_def
          intro!: literals_are_in_\<L>\<^sub>i\<^sub>n_trail_in_lits_of_l)
    subgoal by (auto simp: find_local_restart_target_level_int_inv_def)
    subgoal by (auto simp: trail_pol_alt_def control_stack_length_count_dec
          find_local_restart_target_level_int_inv_def)
    subgoal by auto
    done
  done

definition empty_Q :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>empty_Q = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema, ccount, vdom, lcount). do{
    ASSERT(isa_length_trail_pre M);
    let j = isa_length_trail M;
    RETURN (M, N, D, j, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
       restart_info_restart_done ccount, vdom, lcount)
  })\<close>

definition incr_restart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_restart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_restart stats,
       ema_reinit fast_ema, ema_reinit slow_ema,
       restart_info_restart_done res_info, vdom, avdom, lcount)
  })\<close>

sepref_definition incr_restart_stat_slow_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_restart_stat

sepref_definition incr_restart_stat_fast_code
  is \<open>incr_restart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_restart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_restart_stat_slow_code.refine[sepref_fr_rules]
  incr_restart_stat_fast_code.refine[sepref_fr_rules]

definition incr_lrestart_stat :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>incr_lrestart_stat = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     res_info, vdom, avdom, lcount). do{
     RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, incr_lrestart stats,
       ema_reinit fast_ema, ema_reinit slow_ema,
       restart_info_restart_done res_info,
       vdom, avdom, lcount)
  })\<close>

sepref_definition incr_lrestart_stat_slow_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_register incr_lrestart_stat

sepref_definition incr_lrestart_stat_fast_code
  is \<open>incr_lrestart_stat\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding incr_lrestart_stat_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare incr_lrestart_stat_slow_code.refine[sepref_fr_rules]
  incr_lrestart_stat_fast_code.refine[sepref_fr_rules]

definition restart_abs_wl_heur_pre  :: \<open>twl_st_wl_heur \<Rightarrow> bool \<Rightarrow> bool\<close> where
  \<open>restart_abs_wl_heur_pre S brk  \<longleftrightarrow> (\<exists>T. (S, T) \<in> twl_st_heur \<and> restart_abs_wl_D_pre T brk)\<close>

text \<open>\<^term>\<open>find_decomp_wl_st_int\<close> is the wrong function here, because unlike in the backtrack case,
  we also have to update the queue of literals to update. This is done in the function \<^term>\<open>empty_Q\<close>.
\<close>

definition find_local_restart_target_level_st :: \<open>twl_st_wl_heur \<Rightarrow> nat nres\<close> where
  \<open>find_local_restart_target_level_st S = do {
    find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S)
  }\<close>

lemma find_local_restart_target_level_st_alt_def:
  \<open>find_local_restart_target_level_st = (\<lambda>(M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, stats). do {
      find_local_restart_target_level_int M vm})\<close>
 apply (intro ext)
  apply (case_tac x)
  by (auto simp: find_local_restart_target_level_st_def)

sepref_definition find_local_restart_target_level_st_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_unbounded_assn_def PR_CONST_def
  by sepref

sepref_definition find_local_restart_target_level_st_fast_code
  is \<open>find_local_restart_target_level_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  supply [[goals_limit=1]] length_rev[simp del]
  unfolding find_local_restart_target_level_st_alt_def isasat_bounded_assn_def PR_CONST_def
  by sepref

declare find_local_restart_target_level_st_code.refine[sepref_fr_rules]
  find_local_restart_target_level_st_fast_code.refine[sepref_fr_rules]

definition cdcl_twl_local_restart_wl_D_heur
   :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
  \<open>cdcl_twl_local_restart_wl_D_heur = (\<lambda>S. do {
      ASSERT(restart_abs_wl_heur_pre S False);
      lvl \<leftarrow> find_local_restart_target_level_st S;
      if lvl = count_decided_st_heur S
      then RETURN S
      else do {
        S \<leftarrow> find_decomp_wl_st_int lvl S;
        S \<leftarrow> empty_Q S;
        incr_lrestart_stat S
      }
   })\<close>


sepref_definition empty_Q_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_unbounded_assn_def
  by sepref

sepref_definition empty_Q_fast_code
  is \<open>empty_Q\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding empty_Q_def isasat_bounded_assn_def
  by sepref

declare empty_Q_code.refine[sepref_fr_rules]
  empty_Q_fast_code.refine[sepref_fr_rules]

sepref_register cdcl_twl_local_restart_wl_D_heur
  empty_Q find_decomp_wl_st_int

sepref_definition cdcl_twl_local_restart_wl_D_heur_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition cdcl_twl_local_restart_wl_D_heur_fast_code
  is \<open>cdcl_twl_local_restart_wl_D_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_bounded_assn\<close>
  unfolding cdcl_twl_local_restart_wl_D_heur_def PR_CONST_def
  supply [[goals_limit = 1]]
  by sepref

declare cdcl_twl_local_restart_wl_D_heur_code.refine[sepref_fr_rules]
  cdcl_twl_local_restart_wl_D_heur_fast_code.refine[sepref_fr_rules]
  

named_theorems twl_st_heur_restart

lemma [twl_st_heur_restart]:
  assumes \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>(get_trail_wl_heur S, get_trail_wl T) \<in> trail_pol (all_init_atms_st T)\<close>
  using assms by (cases S; cases T; auto simp: twl_st_heur_restart_def)


(*
lemma restart_abs_wl_D_pre_find_decomp_w_ns_pre:
  assumes
    pre: \<open>restart_abs_wl_D_pre T False\<close> and
    ST: \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>lvl < count_decided_st_heur S\<close>
  shows \<open>find_decomp_w_ns_pre (all_atms_st T) ((get_trail_wl T, lvl), get_vmtf_heur S)\<close>
proof -
  obtain x xa where
    lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n' (all_init_atms_st T) T\<close> and
    Tx: \<open>(T, x) \<in> state_wl_l None\<close> and
    \<open>correct_watching T\<close> and
    xxa: \<open>(x, xa) \<in> twl_st_l None\<close> and
    struct: \<open>twl_struct_invs xa\<close> and
    \<open>twl_list_invs x\<close> and
    \<open>clauses_to_update_l x = {#}\<close> and
    \<open>twl_stgy_invs xa\<close> and
    \<open>get_conflict xa = None\<close>
    using pre unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by blast
  have lits: \<open>literals_are_\<L>\<^sub>i\<^sub>n (all_atms_st T) T\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff[OF Tx xxa struct] lits by blast
  have \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_trail (all_atms_st T) (get_trail_wl_heur S)\<close>
    using literals_are_\<L>\<^sub>i\<^sub>n_literals_are_\<L>\<^sub>i\<^sub>n_trail[OF Tx struct xxa lits] ST
    by (auto simp add: twl_st_heur_restart)
  moreover have \<open> get_vmtf_heur S \<in> isa_vmtf (all_atms_st S) (get_trail_wl_heur S)\<close>
    using ST by (auto simp add: twl_st_heur_restart_def)
  moreover have \<open>no_dup (get_trail_wl_heur S)\<close>
    using struct ST Tx xxa unfolding twl_struct_invs_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def by (auto simp: twl_st twl_st_l twl_st_heur_restart)
  ultimately show ?thesis
    using assms unfolding find_decomp_w_ns_pre_def prod.case
    by blast
qed
*)
lemma trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail:
  \<open>(M', M) \<in> trail_pol \<A> \<Longrightarrow>  literals_are_in_\<L>\<^sub>i\<^sub>n_trail \<A> M\<close>
  unfolding literals_are_in_\<L>\<^sub>i\<^sub>n_trail_def trail_pol_def
  by auto

lemma refine_generalise1: "A \<le> B \<Longrightarrow> do {x \<leftarrow> B; C x} \<le> D \<Longrightarrow> do {x \<leftarrow> A; C x} \<le> (D:: 'a nres)"
  using Refine_Basic.bind_mono(1) dual_order.trans by blast
 
lemma refine_generalise2: "A \<le> B \<Longrightarrow> do {x \<leftarrow> do {x \<leftarrow> B; A' x}; C x} \<le> D \<Longrightarrow> do {x \<leftarrow> do {x \<leftarrow> A; A' x}; C x} \<le> (D:: 'a nres)"
  by (simp add: refine_generalise1)
  
lemma cdcl_twl_local_restart_wl_D_spec_int:
  \<open>cdcl_twl_local_restart_wl_D_spec (M, N, D, NE, UE, Q, W) \<ge> ( do {
      ASSERT(restart_abs_wl_D_pre (M, N, D, NE, UE, Q, W) False);
      i \<leftarrow> SPEC(\<lambda>_. True);
      if i
      then RETURN (M, N, D, NE, UE, Q, W)
      else do {
        (M, Q') \<leftarrow> SPEC(\<lambda>(M', Q'). (\<exists>K M2. (Decided K # M', M2) \<in> set (get_all_ann_decomposition M) \<and>
              Q' = {#}) \<or> (M' = M \<and> Q' = Q));
        RETURN (M, N, D, NE, UE, Q', W)
     }
   })\<close>
proof -
  have If_Res: \<open>(if i then (RETURN f) else (RES g)) = (RES (if i then {f} else g))\<close> for i f g
    by auto
  have H: \<open>g = g' \<Longrightarrow> (f \<bind> g) = (f \<bind> g')\<close> for f :: \<open>_ nres\<close> and g g' by auto
  show ?thesis
    unfolding cdcl_twl_local_restart_wl_D_spec_def prod.case RES_RETURN_RES2 If_Res
    by refine_vcg
      (auto simp: If_Res RES_RETURN_RES2 RES_RES_RETURN_RES uncurry_def
        image_iff split:if_splits)
qed

lemma trail_pol_no_dup: \<open>(M, M') \<in> trail_pol \<A> \<Longrightarrow> no_dup M'\<close>
  by (auto simp: trail_pol_def)

lemma cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec:
  \<open>(cdcl_twl_local_restart_wl_D_heur, cdcl_twl_local_restart_wl_D_spec) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
proof -
  have K: \<open>( (case S of
               (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow>
                 ASSERT (isa_length_trail_pre M) \<bind>
                 (\<lambda>_. RES {(M, N, D, isa_length_trail M, W, vm, \<phi>, clvls, cach,
                            lbd, outl, stats, fema, sema,
                            restart_info_restart_done ccount, vdom, lcount)}))) =
        ((ASSERT (case S of (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow> isa_length_trail_pre M)) \<bind>
         (\<lambda> _. (case S of
               (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats, fema, sema,
                ccount, vdom, lcount) \<Rightarrow> RES {(M, N, D, isa_length_trail M, W, vm, \<phi>, clvls, cach,
                            lbd, outl, stats, fema, sema,
                            restart_info_restart_done ccount, vdom, lcount)})))\<close> for S
  by (cases S) auto
  
  have K2: \<open>(case S of
               (a, b) \<Rightarrow> RES (\<Phi> a b)) =
        (RES (case S of (a, b) \<Rightarrow> \<Phi> a b))\<close> for S
  by (cases S) auto
			
  have [dest]: \<open>av = None\<close> \<open>out_learned a av am \<Longrightarrow> out_learned x1 av am\<close>
    if \<open>restart_abs_wl_D_pre (a, au, av, aw, ax, ay, bd) False\<close>
    for a au av aw ax ay bd x1 am
    using that
    unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
      restart_prog_pre_def
    by (auto simp: twl_st_l_def state_wl_l_def out_learned_def)
(*  have [dest]: \<open>find_decomp_w_ns_pre ((a, lvl), (ae, af, ag, ah, b), ba) \<Longrightarrow>
       (Decided K # x1, M2) \<in> set (get_all_ann_decomposition a) \<Longrightarrow>
        no_dup x1\<close>
    for a lvl ae ab ag ah b ba x1 M2 af K
    unfolding find_decomp_w_ns_pre_def prod.case
    by (auto dest!: distinct_get_all_ann_decomposition_no_dup no_dup_appendD1)*)
  have [refine0]:
    \<open>find_local_restart_target_level_int (get_trail_wl_heur S) (get_vmtf_heur S) \<le> \<Down> {(i, b). b = (i = count_decided (get_trail_wl T)) \<and>
          i \<le> count_decided (get_trail_wl T)} (SPEC (\<lambda>_. True))\<close>
    if \<open>(S, T) \<in> twl_st_heur\<close> for S T
    apply (rule find_local_restart_target_level_int_find_local_restart_target_level[THEN fref_to_Down_curry,
       THEN order_trans, of \<open>all_atms_st T\<close> \<open>get_trail_wl T\<close> \<open>get_vmtf_heur S\<close>])
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal using that unfolding twl_st_heur_def by auto
    subgoal by (auto simp: find_local_restart_target_level_def conc_fun_RES)
    done
  have P: \<open>P\<close>
    if 
      ST: \<open>(((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs),
	bt, bu, bv, bw, bx, by, bz)
       \<in> twl_st_heur\<close> and
      \<open>restart_abs_wl_D_pre (bt, bu, bv, bw, bx, by, bz) False\<close> and
      \<open>restart_abs_wl_heur_pre
	((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs)
	False\<close> and
      lvl: \<open>(lvl, i)
       \<in> {(i, b).
	  b = (i = count_decided (get_trail_wl (bt, bu, bv, bw, bx, by, bz))) \<and>
	  i \<le> count_decided (get_trail_wl (bt, bu, bv, bw, bx, by, bz))}\<close> and
      \<open>i \<in> {_. True}\<close> and
      \<open>lvl \<noteq>
       count_decided_st_heur
	((a, aa, ab, ac, ad, b), ae, (af, ag, ba), ah, ai,
	 ((aj, ak, al, am, bb), an, bc), ao, ap, (aq, bd), ar, as,
	 (at, au, av, aw, be), (ax, ay, az, bf, bg), (bh, bi, bj, bk, bl),
	 (bm, bn), bo, bp, bq, br, bs)\<close> and
      i: \<open>\<not> i\<close> and
    H: \<open>(\<And>vm0. ((an, bc), vm0) \<in> distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz)) \<Longrightarrow>
           ((aj, ak, al, am, bb), vm0) \<in> vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt \<Longrightarrow>
      isa_find_decomp_wl_imp (a, aa, ab, ac, ad, b) lvl
        ((aj, ak, al, am, bb), an, bc)
	\<le> \<Down> {(a, b). (a,b) \<in> trail_pol (all_atms_st (bt, bu, bv, bw, bx, by, bz)) \<times>\<^sub>f
               (Id \<times>\<^sub>f distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz)))}
	    (find_decomp_w_ns (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt lvl vm0) \<Longrightarrow> P)\<close>
    for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz lvl i x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e x1f x2f
       x1g x2g x1h x2h x1i x2i P
  proof -
    have 
      tr: \<open>((a, aa, ab, ac, ad, b), bt) \<in> trail_pol (all_atms bu (bw + bx))\<close> and
      \<open>valid_arena ae bu (set bo)\<close> and
      \<open>((af, ag, ba), bv)
       \<in> option_lookup_clause_rel (all_atms bu (bw + bx))\<close> and
      \<open>by = {#- lit_of x. x \<in># mset (drop ah (rev bt))#}\<close> and
      \<open>(ai, bz) \<in> \<langle>Id\<rangle>map_fun_rel (D\<^sub>0 (all_atms bu (bw + bx)))\<close> and
      vm: \<open>((aj, ak, al, am, bb), an, bc) \<in> isa_vmtf (all_atms bu (bw + bx)) bt\<close> and
      \<open>phase_saving (all_atms bu (bw + bx)) ao\<close> and
      \<open>no_dup bt\<close> and
      \<open>ap \<in> counts_maximum_level bt bv\<close> and
      \<open>cach_refinement_empty (all_atms bu (bw + bx)) (aq, bd)\<close> and
      \<open>out_learned bt bv as\<close> and
      \<open>bq = size (learned_clss_l bu)\<close> and
      \<open>vdom_m (all_atms bu (bw + bx)) bz bu \<subseteq> set bo\<close> and
      \<open>set bp \<subseteq> set bo\<close> and
      \<open>\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l (all_atms bu (bw + bx)). nat_of_lit L \<le> uint_max\<close> and
      \<open>all_atms bu (bw + bx) \<noteq> {#}\<close> and
      bounded: \<open>isasat_input_bounded (all_atms bu (bw + bx))\<close>
      using ST unfolding twl_st_heur_def all_atms_def[symmetric]
      by (auto)
      
    obtain vm0 where
      vm: \<open>((aj, ak, al, am, bb), vm0) \<in> vmtf (all_atms_st (bt, bu, bv, bw, bx, by, bz)) bt\<close> and
      vm0: \<open>((an, bc), vm0) \<in> distinct_atoms_rel (all_atms_st (bt, bu, bv, bw, bx, by, bz))\<close>
      using vm
      by (auto simp: isa_vmtf_def)
 (*   have \<A>: \<open>set_mset (all_atms_st (bt, bu, bv, bw, bx, by, bz)) =
       set_mset (all_atms_st (bt, bu, bv, bw, bx, by, bz))\<close>
      using that(2) unfolding restart_abs_wl_D_pre_def restart_abs_wl_pre_def restart_abs_l_pre_def
        restart_prog_pre_def
      apply - apply normalize_goal+
      subgoal for x xa
      apply (rule literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of \<open>(bt, bu, bv, bw, bx, by, bz)\<close> x xa])
        by auto
      done
    have [simp]: \<open>vmtf (all_atms bu (bw + bx)) bt =
        vmtf (all_atms bu bw) bt\<close> for bt
      using vmtf_cong[OF \<A>] vmtf_cong[OF \<A>[symmetric]]
      by auto
*)
    have n_d: \<open>no_dup bt\<close>
      using tr by (auto simp: trail_pol_def)
    show ?thesis
      apply (rule H)
      apply (rule vm0)
      apply (rule vm)
      apply (rule isa_find_decomp_wl_imp_find_decomp_wl_imp[THEN fref_to_Down_curry2, THEN order_trans,
        of bt lvl \<open>((aj, ak, al, am, bb), vm0)\<close> _ _ _ \<open>all_atms_st (bt, bu, bv, bw, bx, by, bz)\<close>])
      subgoal using lvl i by auto
      subgoal using vm0 tr by auto
      apply (subst (3) Down_id_eq[symmetric])
      apply (rule order_trans)
      apply (rule ref_two_step')
      apply (rule find_decomp_wl_imp_find_decomp_wl'[THEN fref_to_Down_curry2, of _ bt lvl
        \<open>((aj, ak, al, am, bb), vm0)\<close>])
      subgoal
        using that(1-8) vm vm0 bounded n_d tr
	by (auto simp: find_decomp_w_ns_pre_def dest: trail_pol_literals_are_in_\<L>\<^sub>i\<^sub>n_trail)
      subgoal by auto
        using ST
        by (auto simp: find_decomp_w_ns_def conc_fun_RES twl_st_heur_def)
  qed

  show ?thesis
    supply [[goals_limit=1]]
    unfolding cdcl_twl_local_restart_wl_D_heur_def
    unfolding
      find_decomp_wl_st_int_def find_local_restart_target_level_def incr_lrestart_stat_def
       empty_Q_def find_local_restart_target_level_st_def nres_monad_laws
    apply (intro frefI nres_relI)
    apply clarify
    apply (rule ref_two_step)
     prefer 2
     apply (rule cdcl_twl_local_restart_wl_D_spec_int)
    unfolding bind_to_let_conv Let_def RES_RETURN_RES2 nres_monad_laws
    apply (refine_vcg)
    subgoal unfolding restart_abs_wl_heur_pre_def by blast
    apply assumption
    subgoal by (auto simp: twl_st_heur_def count_decided_st_heur_def trail_pol_def)
    apply (rule P)
    apply assumption+
      apply (rule refine_generalise1)
      apply assumption
    subgoal for a aa ab ac ad b ae af ag ba ah ai aj ak al am bb an bc ao ap aq bd ar as at
       au av aw be ax ay az bf bg bh bi bj bk bl bm bn bo bp bq br bs bt bu bv
       bw bx "by" bz lvl i vm0
      unfolding RETURN_def RES_RES2_RETURN_RES RES_RES13_RETURN_RES find_decomp_w_ns_def conc_fun_RES
        RES_RES13_RETURN_RES K K2
	apply (auto simp: intro_spec_iff intro!: ASSERT_leI isa_length_trail_pre)
	apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
	  intro: isa_vmtfI trail_pol_no_dup)
	apply (clarsimp simp: twl_st_heur_def)
	apply (rule_tac x=aja in exI)
	apply (auto simp: isa_length_trail_length_u[THEN fref_to_Down_unRET_Id]
	  intro: isa_vmtfI trail_pol_no_dup)
	done
    done
qed

(*
definition remove_all_annot_true_clause_imp_wl_D_heur_inv
  :: \<open>twl_st_wl_heur \<Rightarrow> nat watcher list \<Rightarrow> nat \<times> twl_st_wl_heur \<Rightarrow> bool\<close>
where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_inv S xs = (\<lambda>(i, T).
       \<exists>S' T'. (S, S') \<in> twl_st_heur_restart \<and> (T, T') \<in> twl_st_heur_restart \<and>
         remove_all_annot_true_clause_imp_wl_D_inv S' (map fst xs) (i, T'))
     \<close>

definition (in isasat_input_ops) remove_all_annot_true_clause_one_imp_heur
  :: \<open>nat \<times> arena \<Rightarrow> arena nres\<close>
where
\<open>remove_all_annot_true_clause_one_imp_heur = (\<lambda>(C, N). do {
      if arena_status N C = DELETED
         then RETURN (extra_information_mark_to_delete N C)
      else do {
        RETURN N
      }
  })\<close>

definition(in isasat_input_ops) remove_all_annot_true_clause_imp_wl_D_heur_pre where
  \<open>remove_all_annot_true_clause_imp_wl_D_heur_pre L S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur_restart \<and> remove_all_annot_true_clause_imp_wl_D_pre L S')\<close>


(* TODO: unfold Let when generating code! *)
definition(in isasat_input_ops) remove_all_annot_true_clause_imp_wl_D_heur
  :: \<open>nat literal \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>remove_all_annot_true_clause_imp_wl_D_heur = (\<lambda>L (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats). do {
    ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_pre L (M, N0, D, Q, W, vm, \<phi>, clvls,
       cach, lbd, outl, stats));
    let xs = W!(nat_of_lit L);
    (_, N) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, N).
        remove_all_annot_true_clause_imp_wl_D_heur_inv
           (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
           (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)\<^esup>
      (\<lambda>(i, N). i < length xs)
      (\<lambda>(i, N). do {
        ASSERT(i < length xs);
        if clause_not_marked_to_delete_heur (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) i
        then do {
          N \<leftarrow> remove_all_annot_true_clause_one_imp_heur (fst (xs!i), N);
          ASSERT(remove_all_annot_true_clause_imp_wl_D_heur_inv
             (M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats) xs
             (i, M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats));
          RETURN (i+1, N)
        }
        else
          RETURN (i+1, N)
      })
      (0, N0);
    RETURN (M, N, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl, stats)
  })\<close>
*)

definition minimum_number_between_restarts :: \<open>uint64\<close> where
  \<open>minimum_number_between_restarts = 50\<close>

lemma minimum_number_between_restarts[sepref_fr_rules]:
 \<open>(uncurry0 (return minimum_number_between_restarts), uncurry0 (RETURN minimum_number_between_restarts))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition five_uint64 :: \<open>uint64\<close> where
  \<open>five_uint64 = 5\<close>

lemma five_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return five_uint64), uncurry0 (RETURN five_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto

definition two_uint64 :: \<open>uint64\<close> where
  \<open>two_uint64 = 2\<close>

lemma two_uint64[sepref_fr_rules]:
 \<open>(uncurry0 (return two_uint64), uncurry0 (RETURN two_uint64))
  \<in>  unit_assn\<^sup>k \<rightarrow>\<^sub>a uint64_assn\<close>
  by sepref_to_hoare sep_auto


definition upper_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>upper_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    lcount < 3000 + 500 * nat_of_uint64 restarts)\<close>

sepref_register upper_restart_bound_not_reached
sepref_definition upper_restart_bound_not_reached_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition upper_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o upper_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding upper_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref
  
declare upper_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  upper_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]


definition (in -) lower_restart_bound_not_reached :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>lower_restart_bound_not_reached = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
        (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
     (\<not>opts_reduce opts \<or> (opts_restart opts \<and> (lcount < 2000 + 300 * nat_of_uint64 restarts))))\<close>

sepref_register lower_restart_bound_not_reached
sepref_definition lower_restart_bound_not_reached_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_unbounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

sepref_definition lower_restart_bound_not_reached_fast_impl
  is \<open>(RETURN o lower_restart_bound_not_reached)\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding lower_restart_bound_not_reached_def PR_CONST_def isasat_bounded_assn_def
  supply [[goals_limit = 1]]
  by sepref

declare lower_restart_bound_not_reached_impl.refine[sepref_fr_rules]
  lower_restart_bound_not_reached_fast_impl.refine[sepref_fr_rules]
  

definition (in -) clause_score_extract :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close> where
  \<open>clause_score_extract arena xs C = (
     let C = (xs ! C) in
     if arena_status arena C = DELETED then (uint32_max, zero_uint32_nat) \<comment> \<open>deleted elements are the
        largest possible\<close>
     else
       let lbd = get_clause_LBD arena C in
       let act = arena_act arena C in
       (lbd, act)
  )\<close>
sepref_register clause_score_extract

(* TODO Move *)
lemma uint32_max_uint32_nat_assn:
  \<open>(uncurry0 (return 4294967295), uncurry0 (RETURN uint32_max)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare
    (sep_auto simp: uint32_max_def uint32_nat_rel_def br_def)
(* End Move *)

definition (in -)valid_sort_clause_score_pre_at where
  \<open>valid_sort_clause_score_pre_at arena vdom i \<longleftrightarrow>
    arena_is_valid_clause_vdom arena (vdom!i) \<and>
          (arena_status arena (vdom!i) \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena (vdom!i) \<and> arena_act_pre arena (vdom!i)))
          \<and> i < length vdom\<close>

sepref_definition (in -) clause_score_extract_code
  is \<open>uncurry2 (RETURN ooo clause_score_extract)\<close>
  :: \<open>[uncurry2 valid_sort_clause_score_pre_at]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> uint32_nat_assn *a uint32_nat_assn\<close>
  supply uint32_max_uint32_nat_assn[sepref_fr_rules]
  unfolding clause_score_extract_def insert_sort_inner_def valid_sort_clause_score_pre_at_def
  by sepref

declare clause_score_extract_code.refine[sepref_fr_rules]

definition (in -)valid_sort_clause_score_pre where
  \<open>valid_sort_clause_score_pre arena vdom \<longleftrightarrow>
    (\<forall>C \<in> set vdom. arena_is_valid_clause_vdom arena C \<and>
        (arena_status arena C \<noteq> DELETED \<longrightarrow>
             (get_clause_LBD_pre arena C \<and> arena_act_pre arena C)))\<close>

definition (in -)insort_inner_clauses_by_score :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list nres\<close> where
  \<open>insort_inner_clauses_by_score arena =
     insert_sort_inner clause_score_ordering (clause_score_extract arena)\<close>

definition (in -) sort_clauses_by_score :: \<open>arena \<Rightarrow> nat list \<Rightarrow> nat list nres\<close> where
  \<open>sort_clauses_by_score arena = insert_sort clause_score_ordering (clause_score_extract arena)\<close>

definition reorder_vdom_wl :: \<open>'v twl_st_wl \<Rightarrow> 'v twl_st_wl nres\<close> where
  \<open>reorder_vdom_wl S = RETURN S\<close>

definition (in -) sort_vdom_heur :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close> where
  \<open>sort_vdom_heur = (\<lambda>(M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount). do {
    ASSERT(valid_sort_clause_score_pre arena avdom);
    avdom \<leftarrow> sort_clauses_by_score arena avdom;
    RETURN (M', arena, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount)
    })\<close>

lemma sort_clauses_by_score_reorder:
  \<open>sort_clauses_by_score arena vdom \<le> SPEC(\<lambda>vdom'. mset vdom = mset vdom')\<close>
  unfolding sort_clauses_by_score_def
  by (rule order.trans, rule insert_sort_reorder_remove[THEN fref_to_Down, of _ vdom])
     (auto simp add: reorder_remove_def)

lemma sort_vdom_heur_reorder_vdom_wl:
  \<open>(sort_vdom_heur, reorder_vdom_wl) \<in> twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding  reorder_vdom_wl_def sort_vdom_heur_def
    apply (intro frefI nres_relI)
    apply refine_rcg
    apply (subst assert_bind_spec_conv, intro conjI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
        intro!: exI[of _ \<open>get_clauses_wl y\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def dest: mset_eq_setD)
    done
qed

lemma (in -) insort_inner_clauses_by_score_invI:
   \<open>valid_sort_clause_score_pre a ba \<Longrightarrow>
       mset ba = mset a2' \<Longrightarrow>
       a1' < length a2' \<Longrightarrow>
       valid_sort_clause_score_pre_at a a2' a1'\<close>
  unfolding valid_sort_clause_score_pre_def all_set_conv_nth valid_sort_clause_score_pre_at_def
  by (metis in_mset_conv_nth)+

sepref_definition (in -) insort_inner_clauses_by_score_code
  is \<open>uncurry2 insort_inner_clauses_by_score\<close>
  :: \<open>[\<lambda>((arena, vdom), _). valid_sort_clause_score_pre arena vdom]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> vdom_assn\<close>
  supply insort_inner_clauses_by_score_invI[intro]
  unfolding insort_inner_clauses_by_score_def insert_sort_inner_def
  by sepref

declare insort_inner_clauses_by_score_code.refine[sepref_fr_rules]

lemma sort_clauses_by_score_invI:
  \<open>valid_sort_clause_score_pre a b \<Longrightarrow>
       mset b = mset a2' \<Longrightarrow> valid_sort_clause_score_pre a a2'\<close>
  using mset_eq_setD unfolding valid_sort_clause_score_pre_def by blast

sepref_definition (in -) sort_clauses_by_score_code
  is \<open>uncurry sort_clauses_by_score\<close>
  :: \<open>[uncurry valid_sort_clause_score_pre]\<^sub>a
      arena_assn\<^sup>k *\<^sub>a vdom_assn\<^sup>d \<rightarrow> vdom_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding insert_sort_def insort_inner_clauses_by_score_def[symmetric]
    sort_clauses_by_score_def
  by sepref

declare sort_clauses_by_score_code.refine[sepref_fr_rules]


sepref_definition sort_vdom_heur_code
  is \<open>sort_vdom_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>d \<rightarrow>\<^sub>a isasat_unbounded_assn\<close>
  supply sort_clauses_by_score_invI[intro]
  unfolding sort_vdom_heur_def isasat_unbounded_assn_def
  by sepref

declare sort_vdom_heur_code.refine[sepref_fr_rules]

definition opts_restart_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_restart_st = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts). (opts_restart opts))\<close>

sepref_definition opts_restart_st_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_restart_st_fast_code
  is \<open>RETURN o opts_restart_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_restart_st_def isasat_bounded_assn_def
  by sepref

declare opts_restart_st_code.refine[sepref_fr_rules]
  opts_restart_st_fast_code.refine[sepref_fr_rules]

definition opts_reduction_st :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>opts_reduction_st = (\<lambda>(M, N0, D, Q, W, vm, \<phi>, clvls, cach, lbd, outl,
       stats, fema, sema, ccount, vdom, avdom, lcount, opts). (opts_reduce opts))\<close>

sepref_definition opts_reduction_st_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_unbounded_assn_def
  by sepref

sepref_definition opts_reduction_st_fast_code
  is \<open>RETURN o opts_reduction_st\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding opts_reduction_st_def isasat_bounded_assn_def
  by sepref

declare opts_reduction_st_code.refine[sepref_fr_rules]
  opts_reduction_st_fast_code.refine[sepref_fr_rules]

sepref_register opts_reduction_st opts_restart_st

definition restart_required_heur :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool nres" where
  \<open>restart_required_heur S n = do {
    let opt_red = opts_reduction_st S;
    let opt_res = opts_restart_st S;
    let sema = ema_get_value (get_slow_ema_heur S);
    let limit = (18 * sema) >> 4;
       \<comment>\<open>roughly speaking 125/100 with hopefully no overflow (there is currently no division
         on \<^typ>\<open>uint64\<close>\<close>
    let fema = ema_get_value (get_fast_ema_heur S);
    let ccount = get_conflict_count_since_last_restart_heur S;
    let lcount = get_learned_count S;
    let can_res = (lcount > n);
    let min_reached = (ccount > minimum_number_between_restarts);
    let level = count_decided_st_heur S;
    let should_not_reduce = (\<not>opt_red \<or> upper_restart_bound_not_reached S);
    RETURN ((opt_res \<or> opt_red) \<and>
       (should_not_reduce \<longrightarrow> limit > fema) \<and> min_reached \<and> can_res \<and>
      level > two_uint32_nat \<and> nat_of_uint32_conv level > nat_of_uint64 (fema >> 48))}
  \<close>

lemma uint64_max_ge_48: \<open>48 \<le> uint64_max\<close>
  by (auto simp: uint64_max_def)


sepref_definition restart_required_heur_fast_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_bounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]] uint64_max_ge_48[simp]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

sepref_definition restart_required_heur_slow_code
  is \<open>uncurry restart_required_heur\<close>
  :: \<open>isasat_unbounded_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]] uint64_max_ge_48[simp]
  bit_lshift_uint64_assn[sepref_fr_rules]
  unfolding restart_required_heur_def
  by sepref

declare restart_required_heur_fast_code.refine[sepref_fr_rules]
  restart_required_heur_slow_code.refine[sepref_fr_rules]

definition mark_to_delete_clauses_wl_D_heur_pre :: \<open>twl_st_wl_heur \<Rightarrow> bool\<close> where
  \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
    (\<exists>S'. (S, S') \<in> twl_st_heur_restart \<and> mark_to_delete_clauses_wl_D_pre S')\<close>

lemma mark_to_delete_clauses_wl_post_alt_def:
  \<open>mark_to_delete_clauses_wl_post S0 S \<longleftrightarrow>
    (\<exists>T0 T.
        (S0, T0) \<in> state_wl_l None \<and>
        (S, T) \<in> state_wl_l None \<and>
        (\<exists>U0 U. (T0, U0) \<in> twl_st_l None \<and>
               (T, U) \<in> twl_st_l None \<and>
               remove_one_annot_true_clause\<^sup>*\<^sup>* T0 T \<and>
               twl_list_invs T0 \<and>
               twl_struct_invs U0 \<and>
               twl_list_invs T \<and>
               twl_struct_invs U \<and>
               get_conflict_l T0 = None \<and>
	       clauses_to_update_l T0 = {#}) \<and>
        correct_watching S0 \<and> correct_watching S)\<close>
  unfolding mark_to_delete_clauses_wl_post_def mark_to_delete_clauses_l_post_def
    mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
  apply (rule iffI; normalize_goal+)
  subgoal for T0 T U0
    apply (rule exI[of _ T0])
    apply (rule exI[of _ T])
    apply (intro conjI)
    apply auto[2]
    apply (rule exI[of _ U0])
    apply auto
    using rtranclp_remove_one_annot_true_clause_cdcl_twl_restart_l2[of T0 T U0]
      rtranclp_cdcl_twl_restart_l_list_invs[of T0]
    apply (auto dest: )
     using rtranclp_cdcl_twl_restart_l_list_invs by blast
  subgoal for T0 T U0 U
    apply (rule exI[of _ T0])
    apply (rule exI[of _ T])
    apply (intro conjI)
    apply auto[2]
    apply (rule exI[of _ U0])
    apply auto
    done
  done

lemma mark_to_delete_clauses_wl_D_heur_pre_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur_pre S \<longleftrightarrow>
      (\<exists>S'. (S, S') \<in> twl_st_heur \<and> mark_to_delete_clauses_wl_D_pre S')\<close> (is ?A) and
    mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_D_pre T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ ?B\<close>) and
    mark_to_delete_clauses_wl_post_twl_st_heur:
      \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow>
        (S, T) \<in> twl_st_heur \<longleftrightarrow> (S, T) \<in> twl_st_heur_restart\<close> (is \<open>_ \<Longrightarrow> _ ?C\<close>)
proof -
  note cong =  trail_pol_cong
      option_lookup_clause_rel_cong D\<^sub>0_cong isa_vmtf_cong phase_saving_cong
      cach_refinement_empty_cong vdom_m_cong isasat_input_nempty_cong
      isasat_input_bounded_cong

  show ?A
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
    apply (rule iffI)
    apply normalize_goal+
    subgoal for T U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (rule exI[of _ T])
      apply (intro conjI) defer
      apply (rule exI[of _ U])
      apply (intro conjI) defer
      apply (rule exI[of _ V])
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    apply normalize_goal+
    subgoal for T U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (rule exI[of _ T])
      apply (intro conjI) defer
      apply (rule exI[of _ U])
      apply (intro conjI) defer
      apply (rule exI[of _ V])
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  show \<open>mark_to_delete_clauses_wl_D_pre T \<Longrightarrow> ?B\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def mark_to_delete_clauses_wl_pre_def
      mark_to_delete_clauses_l_pre_def mark_to_delete_clauses_wl_D_pre_def
    apply normalize_goal+
    apply (rule iffI)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    subgoal for U V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  show  \<open>mark_to_delete_clauses_wl_post T0 T \<Longrightarrow> ?C\<close>
    supply [[goals_limit=1]]
    unfolding mark_to_delete_clauses_wl_post_alt_def
    apply normalize_goal+
    apply (rule iffI)
    subgoal for U0 U V0 V     
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close>]
	vdom_m_cong[of \<open>all_atms_st T\<close> \<open>all_init_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (simp_all del: isasat_input_nempty_def isasat_input_bounded_def)
      apply (cases S; cases T)
      apply (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
      done
    subgoal for U0 U V0 V
      using literals_are_\<L>\<^sub>i\<^sub>n'_literals_are_\<L>\<^sub>i\<^sub>n_iff(3)[of T U V]
        cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close>]
	vdom_m_cong[of \<open>all_init_atms_st T\<close> \<open>all_atms_st T\<close> \<open>get_watched_wl T\<close> \<open>get_clauses_wl T\<close>]
      apply -
      apply (cases S; cases T)
      by (simp add: twl_st_heur_def twl_st_heur_restart_def del: isasat_input_nempty_def)
    done
  
qed

definition mark_garbage_heur :: \<open>nat \<Rightarrow> nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close> where
  \<open>mark_garbage_heur C i = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, avdom, lcount, opts).
    (M', extra_information_mark_to_delete N' C, D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema, ccount,
       vdom, delete_index_and_swap avdom i, lcount - 1, opts))\<close>

lemma get_vdom_mark_garbage[simp]:
  \<open>get_vdom (mark_garbage_heur C i S) = get_vdom S\<close>
  \<open>get_avdom (mark_garbage_heur C i S) = delete_index_and_swap (get_avdom S) i\<close>
  by (cases S; auto simp: mark_garbage_heur_def; fail)+


lemma mark_garbage_heur_wl:
  assumes 
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T)\<close> and
    \<open>\<not> irred (get_clauses_wl T) C\<close>
  shows \<open>(mark_garbage_heur C i S, mark_garbage_wl C T) \<in> twl_st_heur_restart\<close>
  using assms
  apply (cases S; cases T)
   apply (simp add: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
	all_init_atms_def[symmetric])
  apply (auto simp: twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
         learned_clss_l_l_fmdrop size_remove1_mset_If
     simp: all_init_atms_def all_init_lits_def
     simp del: all_init_atms_def[symmetric]
     intro: valid_arena_extra_information_mark_to_delete'
      dest!: in_set_butlastD in_vdom_m_fmdropD
      elim!: in_set_upd_cases)
  done

lemma twl_st_heur_restart_valid_arena[twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close>
  shows \<open>valid_arena (get_clauses_wl_heur S) (get_clauses_wl T) (set (get_vdom S))\<close>
  using assms by (auto simp: twl_st_heur_restart_def)

lemma twl_st_heur_restart_get_avdom_nth_get_vdom[twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> \<open>i < length (get_avdom S)\<close>
  shows \<open>get_avdom S ! i \<in> set (get_vdom S)\<close>
  using assms by (fastforce simp: twl_st_heur_restart_def)

lemma [twl_st_heur_restart]:
  assumes
    \<open>(S, T) \<in> twl_st_heur_restart\<close> and
    \<open>C \<in> set (get_avdom S)\<close>
  shows \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow>
         (C \<in># dom_m (get_clauses_wl T))\<close> and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>and
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    \<open>C \<in># dom_m (get_clauses_wl T) \<Longrightarrow> arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
proof -
  show \<open>clause_not_marked_to_delete_heur S C \<longleftrightarrow> (C \<in># dom_m (get_clauses_wl T))\<close>
    using assms
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_dom_status_iff(1)
        split: prod.splits)
  assume C: \<open>C \<in># dom_m (get_clauses_wl T)\<close>
  show \<open>arena_lit (get_clauses_wl_heur S) C = get_clauses_wl T \<propto> C ! 0\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_status (get_clauses_wl_heur S) C = LEARNED \<longleftrightarrow> \<not>irred (get_clauses_wl T) C\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
  show \<open>arena_length (get_clauses_wl_heur S) C = length (get_clauses_wl T \<propto> C)\<close>
    using assms C
    by (cases S; cases T)
      (auto simp add: twl_st_heur_restart_def clause_not_marked_to_delete_heur_def
          arena_lifting
        split: prod.splits)
qed

definition number_clss_to_keep :: \<open>twl_st_wl_heur \<Rightarrow> nat\<close> where
  \<open>number_clss_to_keep = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl,
      (props, decs, confl, restarts, _), fast_ema, slow_ema, ccount,
       vdom, avdom, lcount).
    1000 + 150 * nat_of_uint64 restarts)\<close>


definition access_vdom_at :: \<open>twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>access_vdom_at S i = get_avdom S ! i\<close>

lemma access_vdom_at_alt_def:
  \<open>access_vdom_at = (\<lambda>(M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount) i. avdom ! i)\<close>
  by (intro ext) (auto simp: access_vdom_at_def)

definition access_vdom_at_pre where
  \<open>access_vdom_at_pre S i \<longleftrightarrow> i < length (get_avdom S)\<close>

(* TODO Missing : The sorting function + definition of l should depend on the number of initial
  clauses *)
definition (in -) MINIMUM_DELETION_LBD :: nat where
  \<open>MINIMUM_DELETION_LBD = 3\<close>

lemma (in -) MINIMUM_DELETION_LBD_hnr[sepref_fr_rules]:
 \<open>(uncurry0 (return 3), uncurry0 (RETURN MINIMUM_DELETION_LBD)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  by sepref_to_hoare (sep_auto simp: MINIMUM_DELETION_LBD_def uint32_nat_rel_def br_def)

definition delete_index_vdom_heur :: \<open>nat \<Rightarrow> twl_st_wl_heur \<Rightarrow> twl_st_wl_heur\<close>where
  \<open>delete_index_vdom_heur = (\<lambda>i (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
     ccount, vdom, avdom, lcount).
     (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema, slow_ema,
       ccount, vdom, delete_index_and_swap avdom i, lcount))\<close>

definition mark_to_delete_clauses_wl_D_heur
  :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wl_heur nres\<close>
where
\<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
    ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
    S \<leftarrow> sort_vdom_heur S;
    let l = number_clss_to_keep S;
    (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
      (\<lambda>(i, S). i < length (get_avdom S))
      (\<lambda>(i, T). do {
        ASSERT(i < length (get_avdom T));
        ASSERT(access_vdom_at_pre T i);
        let C = get_avdom T ! i;
        ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
        if \<not>clause_not_marked_to_delete_heur T C then RETURN (i, delete_index_vdom_heur i T)
        else do {
          ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
          let L = access_lit_in_clauses_heur T C 0;
          D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
          ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
          ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
          ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
            arena_is_valid_clause_idx (get_clauses_wl_heur T) C);
          let can_del = (D \<noteq> Some C) \<and> arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
             arena_status (get_clauses_wl_heur T) C = LEARNED \<and>
             arena_length (get_clauses_wl_heur T) C \<noteq> two_uint64_nat;
          if can_del
          then
            do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
          else
            RETURN (i+1, T)
        }
      })
      (l, S);
    incr_restart_stat T
  })\<close>

lemma twl_st_heur_restart_same_annotD:
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> Propagated L C \<in> set (get_trail_wl T) \<Longrightarrow>
     Propagated L C' \<in> set (get_trail_wl T) \<Longrightarrow> C = C'\<close>
  \<open>(S, T) \<in> twl_st_heur_restart \<Longrightarrow> Propagated L C \<in> set (get_trail_wl T) \<Longrightarrow>
     Decided L \<in> set (get_trail_wl T) \<Longrightarrow> False\<close>
  by (auto simp: twl_st_heur_restart_def dest: no_dup_no_propa_and_dec
    no_dup_same_annotD)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_mono:
  \<open>set_mset \<A> \<subseteq> set_mset \<B> \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<B>\<close>
  by (auto simp: \<L>\<^sub>a\<^sub>l\<^sub>l_def)

lemma \<L>\<^sub>a\<^sub>l\<^sub>l_init_all:
  \<open>L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a) \<Longrightarrow> L  \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_atms_st x1a)\<close>
  apply (rule \<L>\<^sub>a\<^sub>l\<^sub>l_mono)
  defer
  apply assumption
  apply (cases x1a)
  apply (auto simp: all_init_atms_def all_lits_def all_init_lits_def
      all_lits_of_mm_union
    simp del: all_init_atms_def[symmetric])
  by (metis all_clss_l_ran_m all_lits_of_mm_union imageI image_mset_union union_iff)


lemma mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D:
  \<open>(mark_to_delete_clauses_wl_D_heur, mark_to_delete_clauses_wl_D) \<in>
     twl_st_heur_restart \<rightarrow>\<^sub>f \<langle>twl_st_heur_restart\<rangle>nres_rel\<close>
proof -
  have mark_to_delete_clauses_wl_D_alt_def:
    \<open>mark_to_delete_clauses_wl_D  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_pre S);
      S \<leftarrow> reorder_vdom_wl S;
      xs \<leftarrow> collect_valid_indices_wl S;
      l \<leftarrow> SPEC(\<lambda>_::nat. True);
      (_, S, _) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_to_delete_clauses_wl_D_inv S xs\<^esup>
        (\<lambda>(i, T, xs). i < length xs)
        (\<lambda>(i, T, xs). do {
          if(xs!i \<notin># dom_m (get_clauses_wl T)) then RETURN (i, T, delete_index_and_swap xs i)
          else do {
            ASSERT(0 < length (get_clauses_wl T\<propto>(xs!i)));
	    ASSERT (get_clauses_wl T \<propto> (xs ! i) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st T));
            can_del \<leftarrow> SPEC(\<lambda>b. b \<longrightarrow>
              (Propagated (get_clauses_wl T\<propto>(xs!i)!0) (xs!i) \<notin> set (get_trail_wl T)) \<and>
               \<not>irred (get_clauses_wl T) (xs!i) \<and> length (get_clauses_wl T \<propto> (xs!i)) \<noteq> 2 );
            ASSERT(i < length xs);
            if can_del
            then
              RETURN (i, mark_garbage_wl (xs!i) T, delete_index_and_swap xs i)
            else
              RETURN (i+1, T, xs)
          }
        })
        (l, S, xs);
      RETURN S
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_def reorder_vdom_wl_def
    by (auto intro!: ext)

  have mark_to_delete_clauses_wl_D_heur_alt_def:
    \<open>mark_to_delete_clauses_wl_D_heur  = (\<lambda>S. do {
      ASSERT(mark_to_delete_clauses_wl_D_heur_pre S);
      S \<leftarrow> sort_vdom_heur S;
      _ \<leftarrow> RETURN (get_avdom S);
      l \<leftarrow> RETURN (number_clss_to_keep S);
      (_, T) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>_. True\<^esup>
        (\<lambda>(i, S). i < length (get_avdom S))
        (\<lambda>(i, T). do {
          ASSERT(i < length (get_avdom T));
          ASSERT(access_vdom_at_pre T i);
          let C = get_avdom T ! i;
          ASSERT(clause_not_marked_to_delete_heur_pre (T, C));
          if(\<not>clause_not_marked_to_delete_heur T C) then RETURN (i, delete_index_vdom_heur i T)
          else do {
            ASSERT(access_lit_in_clauses_heur_pre ((T, C), 0));
            let L = access_lit_in_clauses_heur T C 0;
            D \<leftarrow> get_the_propagation_reason_pol (get_trail_wl_heur T) L;
            ASSERT(get_clause_LBD_pre (get_clauses_wl_heur T) C);
            ASSERT(arena_is_valid_clause_vdom (get_clauses_wl_heur T) C);
            ASSERT(arena_status (get_clauses_wl_heur T) C = LEARNED \<longrightarrow>
                arena_is_valid_clause_idx (get_clauses_wl_heur T) C);
            let can_del = (D \<noteq> Some C) \<and> arena_lbd (get_clauses_wl_heur T) C > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur T) C = LEARNED \<and>
               arena_length (get_clauses_wl_heur T) C \<noteq> two_uint64_nat;
            if can_del
            then do {
              ASSERT(mark_garbage_pre (get_clauses_wl_heur T, C));
              RETURN (i, mark_garbage_heur C i T)
            }
            else
              RETURN (i+1, T)
          }
        })
        (l, S);
      incr_restart_stat T
    })\<close>
    unfolding mark_to_delete_clauses_wl_D_heur_def
    by (auto intro!: ext)

  have [refine0]: \<open>RETURN (get_avdom x) \<le> \<Down> {(xs, xs'). xs = xs' \<and> xs = get_avdom x} (collect_valid_indices_wl y)\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close>
    for x y
  proof -
    show ?thesis by (auto simp: collect_valid_indices_wl_def simp: RETURN_RES_refine_iff)
  qed
  have init_rel[refine0]: \<open>(x, y) \<in> twl_st_heur_restart \<Longrightarrow>
       (l, la) \<in> nat_rel \<Longrightarrow>
       ((l, x), la, y) \<in> nat_rel \<times>\<^sub>f {(S, T). (S, T) \<in> twl_st_heur_restart \<and> get_avdom S = get_avdom x}\<close>
    for x y l la
    by auto

  have get_the_propagation_reason:
    \<open>get_the_propagation_reason_pol (get_trail_wl_heur x2b)
       (arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0))
        \<le> \<Down> {(D, b). b \<longleftrightarrow> ((D \<noteq> Some (get_avdom x2b ! x1b)) \<and>
               arena_lbd (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) > MINIMUM_DELETION_LBD \<and>
               arena_status (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) = LEARNED) \<and>
                arena_length (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b) \<noteq> two_uint32_nat}
       (SPEC
           (\<lambda>b. b \<longrightarrow>
                Propagated (get_clauses_wl x1a \<propto> (x2a ! x1) ! 0) (x2a ! x1)
                \<notin> set (get_trail_wl x1a) \<and>
                \<not> irred (get_clauses_wl x1a) (x2a ! x1) \<and>
                length (get_clauses_wl x1a \<propto> (x2a ! x1)) \<noteq> 2 ))\<close>
  if
    \<open>(x, y) \<in> twl_st_heur_restart\<close> and
    \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
    \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
    \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
    \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
    \<open>(l, la) \<in> nat_rel\<close> and
    \<open>la \<in> {_. True}\<close> and
    xa_x': \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
    \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
    \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
    \<open>x1b < length (get_avdom x2b)\<close> and
    \<open>access_vdom_at_pre x2b x1b\<close> and
    \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
    \<open>\<not> \<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
    \<open>\<not> x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close> and
    \<open>0 < length (get_clauses_wl x1a \<propto> (x2a ! x1))\<close> and
    \<open>access_lit_in_clauses_heur_pre ((x2b, get_avdom x2b ! x1b), 0)\<close> and
    st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
    L: \<open>get_clauses_wl x1a \<propto> (x2a ! x1) ! 0 \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
    for x y S Sa xs' xs l la xa x' x1 x2 x1a x2a x1' x2' x3 x1b ys x2b
  proof -
    have L: \<open>arena_lit (get_clauses_wl_heur x2b) (x2a ! x1) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l (all_init_atms_st x1a)\<close>
      using L that by (auto simp: twl_st_heur_restart st arena_lifting dest: \<L>\<^sub>a\<^sub>l\<^sub>l_init_all)

    show ?thesis
      apply (rule order.trans)
      apply (rule get_the_propagation_reason_pol[THEN fref_to_Down_curry,
        of \<open>all_init_atms_st x1a\<close> \<open>get_trail_wl x1a\<close>
	  \<open>arena_lit (get_clauses_wl_heur x2b) (get_avdom x2b ! x1b + 0)\<close>])
      subgoal
        using xa_x' L by (auto simp add: twl_st_heur_restart_def st)
      subgoal
        using xa_x' by (auto simp add: twl_st_heur_restart_def st)
      using that unfolding get_the_propagation_reason_def apply -
      by (auto simp: twl_st_heur_restart lits_of_def get_the_propagation_reason_def
          conc_fun_RES
        dest: twl_st_heur_restart_same_annotD imageI[of _ _ lit_of])
  qed
  have \<open>((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom, lcount),
           S')
          \<in> twl_st_heur_restart \<longleftrightarrow>
    ((M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats, fast_ema,
            slow_ema, ccount, vdom, avdom', lcount),
           S')
          \<in> twl_st_heur_restart\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema
      ccount vdom lcount S' avdom' avdom
    using that unfolding twl_st_heur_restart_def
    by auto
  then have mark_to_delete_clauses_wl_D_heur_pre_vdom':
    \<open>mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
       fast_ema, slow_ema, ccount, vdom, avdom, lcount) \<longleftrightarrow>
      mark_to_delete_clauses_wl_D_heur_pre (M', N', D', j, W', vm, \<phi>, clvls, cach, lbd, outl, stats,
        fast_ema, slow_ema, ccount, vdom, avdom', lcount)\<close>
    if \<open>set avdom = set avdom'\<close>
    for M' N' D' j W' vm \<phi> clvls cach lbd outl stats fast_ema slow_ema avdom avdom'
      ccount vdom lcount
    using that
    unfolding mark_to_delete_clauses_wl_D_heur_pre_def
    by metis
  have [refine0]:
    \<open>sort_vdom_heur S \<le> \<Down> {(U, V). (U, V) \<in> twl_st_heur_restart \<and> V = T \<and>
         (mark_to_delete_clauses_wl_D_pre T \<longrightarrow> mark_to_delete_clauses_wl_D_pre V) \<and>
         (mark_to_delete_clauses_wl_D_heur_pre S \<longrightarrow> mark_to_delete_clauses_wl_D_heur_pre U)}
         (reorder_vdom_wl T)\<close>
    if \<open>(S, T) \<in> twl_st_heur_restart\<close> for S T
    using that unfolding reorder_vdom_wl_def sort_vdom_heur_def
    apply (refine_rcg ASSERT_leI)
    subgoal for x y
      unfolding valid_sort_clause_score_pre_def arena_is_valid_clause_vdom_def
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def arena_act_pre_def
      by (auto simp: valid_sort_clause_score_pre_def twl_st_heur_restart_def arena_dom_status_iff
        arena_act_pre_def get_clause_LBD_pre_def arena_is_valid_clause_idx_def
         intro!: exI[of _ \<open>get_clauses_wl T\<close>])
    subgoal
      apply (rewrite at \<open>_ \<le> \<hole>\<close> Down_id_eq[symmetric])
      apply (rule bind_refine_spec)
      prefer 2
      apply (rule sort_clauses_by_score_reorder)
      by (auto simp: twl_st_heur_restart_def
         intro: mark_to_delete_clauses_wl_D_heur_pre_vdom'[THEN iffD1]
         dest: mset_eq_setD)
    done
  have already_deleted:
    \<open>((x1b, delete_index_vdom_heur x1b x2b), x1, x1a,
       delete_index_and_swap x2a x1)
      \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
    if
      \<open>(x, y) \<in> twl_st_heur_restart\<close> and
      \<open>mark_to_delete_clauses_wl_D_pre y\<close> and
      \<open>mark_to_delete_clauses_wl_D_heur_pre x\<close> and
      \<open>(S, Sa)
     \<in> {(U, V).
        (U, V) \<in> twl_st_heur_restart \<and>
        V = y \<and>
        (mark_to_delete_clauses_wl_D_pre y \<longrightarrow>
         mark_to_delete_clauses_wl_D_pre V) \<and>
        (mark_to_delete_clauses_wl_D_heur_pre x \<longrightarrow>
         mark_to_delete_clauses_wl_D_heur_pre U)}\<close> and
      \<open>(ys, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S}\<close> and
      \<open>(l, la) \<in> nat_rel\<close> and
      \<open>la \<in> {_. True}\<close> and
      xx: \<open>(xa, x')
     \<in> nat_rel \<times>\<^sub>f {(Sa, T, xs). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close> and
      \<open>case xa of (i, S) \<Rightarrow> i < length (get_avdom S)\<close> and
      \<open>case x' of (i, T, xs) \<Rightarrow> i < length xs\<close> and
      \<open>mark_to_delete_clauses_wl_D_inv Sa xs x'\<close> and
      st:
      \<open>x2 = (x1a, x2a)\<close>
      \<open>x' = (x1, x2)\<close>
      \<open>xa = (x1b, x2b)\<close> and
      \<open>x1b < length (get_avdom x2b)\<close> and
      \<open>access_vdom_at_pre x2b x1b\<close> and
      \<open>clause_not_marked_to_delete_heur_pre (x2b, get_avdom x2b ! x1b)\<close> and
      \<open>\<not> clause_not_marked_to_delete_heur x2b (get_avdom x2b ! x1b)\<close> and
      \<open>x2a ! x1 \<notin># dom_m (get_clauses_wl x1a)\<close>
    for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d ys x1b Sa
  proof -
    show ?thesis
      using xx unfolding st
      by (auto simp: twl_st_heur_restart_def delete_index_vdom_heur_def
          twl_st_heur_restart_def mark_garbage_heur_def mark_garbage_wl_def
          learned_clss_l_l_fmdrop size_remove1_mset_If
          intro: valid_arena_extra_information_mark_to_delete'
          dest!: in_set_butlastD in_vdom_m_fmdropD
          elim!: in_set_upd_cases)
  qed

  have init:
    \<open>(u, xs) \<in> {(xs, xs'). xs = xs' \<and> xs = get_avdom S} \<Longrightarrow>
    (l, la) \<in> nat_rel \<Longrightarrow>
    (S, Sa) \<in> twl_st_heur_restart \<Longrightarrow>
    mark_to_delete_clauses_wl_D_inv Sa xs (la, Sa, xs) \<Longrightarrow>
    ((l, S), la, Sa, xs) \<in>  nat_rel \<times>\<^sub>f
       {(Sa, (T, xs)). (Sa, T) \<in> twl_st_heur_restart \<and> xs = get_avdom Sa}\<close>
       for x y S Sa xs l la u
    by auto

  show ?thesis
    supply sort_vdom_heur_def[simp]
    unfolding mark_to_delete_clauses_wl_D_heur_alt_def mark_to_delete_clauses_wl_D_alt_def
      access_lit_in_clauses_heur_def Let_def
    apply (intro frefI nres_relI)
    apply (refine_vcg sort_vdom_heur_reorder_vdom_wl[THEN fref_to_Down])
    subgoal
      unfolding mark_to_delete_clauses_wl_D_heur_pre_def by fast
    subgoal by auto
    subgoal by auto
    subgoal by auto
    apply (rule init; solves auto)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: access_vdom_at_pre_def)
    subgoal for x y S xs l la xa x' xz x1 x2 x1a x2a x2b x2c x2d
      unfolding clause_not_marked_to_delete_heur_pre_def arena_is_valid_clause_vdom_def
        prod.simps
      by (rule exI[of _ \<open>get_clauses_wl x2a\<close>], rule exI[of _ \<open>set (get_vdom x2d)\<close>])
         (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal
      by (rule already_deleted)
    subgoal for x y _ _ _ _ _ xs l la xa x' x1 x2 x1a x2a
      unfolding access_lit_in_clauses_heur_pre_def prod.simps arena_lit_pre_def
        arena_is_valid_clause_idx_and_access_def
      by (rule bex_leI[of _ \<open>get_avdom x2a ! x1a\<close>], simp, rule exI[of _ \<open>get_clauses_wl x1\<close>])
        (auto simp: twl_st_heur_restart_def)
    apply (rule get_the_propagation_reason; assumption)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        get_clause_LBD_pre_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart arena_dom_status_iff
          dest: twl_st_heur_restart_valid_arena twl_st_heur_restart_get_avdom_nth_get_vdom)
    subgoal
      by (auto simp: twl_st_heur_restart)
    subgoal for x y S Sa _ xs l la xa x' x1 x2 x1a x2a x1b x2b
      unfolding prod.simps mark_garbage_pre_def
        arena_is_valid_clause_vdom_def arena_is_valid_clause_idx_def
      by (rule exI[of _ \<open>get_clauses_wl x1a\<close>], rule exI[of _ \<open>set (get_vdom x2b)\<close>])
        (auto simp: twl_st_heur_restart dest: twl_st_heur_restart_valid_arena)
    subgoal
      by (auto intro!: mark_garbage_heur_wl)
    subgoal
      by auto
    subgoal
      by (auto simp: incr_restart_stat_def twl_st_heur_restart_def)
    done
qed

definition cdcl_twl_full_restart_wl_prog_heur where
\<open>cdcl_twl_full_restart_wl_prog_heur S = do {
  _ \<leftarrow> ASSERT (mark_to_delete_clauses_wl_D_heur_pre S);
  T \<leftarrow> mark_to_delete_clauses_wl_D_heur S;
  RETURN T
}\<close>

lemma cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D:
  \<open>(cdcl_twl_full_restart_wl_prog_heur, cdcl_twl_full_restart_wl_prog_D) \<in>
     twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_full_restart_wl_prog_heur_def cdcl_twl_full_restart_wl_prog_D_def
  apply (intro frefI nres_relI)
  apply (refine_vcg
    mark_to_delete_clauses_wl_D_heur_mark_to_delete_clauses_wl_D[THEN fref_to_Down])
  subgoal
    unfolding mark_to_delete_clauses_wl_D_heur_pre_alt_def
    by fast
  subgoal
    by (subst mark_to_delete_clauses_wl_D_heur_pre_twl_st_heur[symmetric])
  subgoal
    by (subst mark_to_delete_clauses_wl_post_twl_st_heur)
  done

definition cdcl_twl_restart_wl_heur where
\<open>cdcl_twl_restart_wl_heur S = do {
    let b = lower_restart_bound_not_reached S;
    if b then cdcl_twl_local_restart_wl_D_heur S
    else cdcl_twl_full_restart_wl_prog_heur S
  }\<close>


lemma cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog:
  \<open>(cdcl_twl_restart_wl_heur, cdcl_twl_restart_wl_D_prog) \<in>
    twl_st_heur \<rightarrow>\<^sub>f \<langle>twl_st_heur\<rangle>nres_rel\<close>
  unfolding cdcl_twl_restart_wl_D_prog_def cdcl_twl_restart_wl_heur_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
    cdcl_twl_local_restart_wl_D_heur_cdcl_twl_local_restart_wl_D_spec[THEN fref_to_Down]
    cdcl_twl_full_restart_wl_prog_heur_cdcl_twl_full_restart_wl_prog_D[THEN fref_to_Down])
  subgoal by auto
  subgoal by auto
  done


definition restart_prog_wl_D_heur
  :: "twl_st_wl_heur \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (twl_st_wl_heur \<times> nat) nres"
where
  \<open>restart_prog_wl_D_heur S n brk = do {
    b \<leftarrow> restart_required_heur S n;
    if \<not>brk \<and> b
    then do {
       T \<leftarrow> cdcl_twl_restart_wl_heur S;
       RETURN (T, n+1)
    }
    else RETURN (S, n)
  }\<close>

lemma restart_required_heur_restart_required_wl:
  \<open>(uncurry restart_required_heur, uncurry restart_required_wl) \<in>
    twl_st_heur \<times>\<^sub>f nat_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
    unfolding restart_required_heur_def restart_required_wl_def uncurry_def Let_def
    by (intro frefI nres_relI)
     (auto simp: twl_st_heur_def get_learned_clss_wl_def)

lemma restart_prog_wl_D_heur_restart_prog_wl_D:
  \<open>(uncurry2 restart_prog_wl_D_heur, uncurry2 restart_prog_wl_D) \<in>
    twl_st_heur \<times>\<^sub>f nat_rel \<times>\<^sub>f bool_rel  \<rightarrow>\<^sub>f \<langle>twl_st_heur \<times>\<^sub>f nat_rel\<rangle>nres_rel\<close>
  unfolding restart_prog_wl_D_heur_def restart_prog_wl_D_def uncurry_def
  apply (intro frefI nres_relI)
  apply (refine_rcg
      restart_required_heur_restart_required_wl[THEN fref_to_Down_curry]
      cdcl_twl_restart_wl_heur_cdcl_twl_restart_wl_D_prog[THEN fref_to_Down])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

end