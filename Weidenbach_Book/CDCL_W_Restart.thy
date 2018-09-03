theory CDCL_W_Restart
imports CDCL_W_Full
begin

chapter \<open>Extensions on Weidenbach's CDCL\<close>

text \<open>We here extend our calculus.\<close>

section \<open>Restarts\<close>

context conflict_driven_clause_learning\<^sub>W
begin
text \<open>This is an unrestricted version.\<close>
inductive cdcl\<^sub>W_restart_stgy for S T :: \<open>'st \<times> nat\<close> where
  \<open>cdcl\<^sub>W_stgy (fst S) (fst T) \<Longrightarrow> snd S = snd T \<Longrightarrow> cdcl\<^sub>W_restart_stgy S T\<close> |
  \<open>restart (fst S) (fst T) \<Longrightarrow> snd T = Suc (snd S) \<Longrightarrow> cdcl\<^sub>W_restart_stgy S T\<close>

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart: \<open>cdcl\<^sub>W_stgy S S' \<Longrightarrow> cdcl\<^sub>W_restart S S'\<close>
  by (induction rule: cdcl\<^sub>W_stgy.induct) auto

lemma cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W_restart_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart (fst S) (fst T)\<close>
  by (induction rule: cdcl\<^sub>W_restart_stgy.induct)
    (auto dest: cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart simp: cdcl\<^sub>W_restart.simps cdcl\<^sub>W_rf.restart)

lemma rtranclp_cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* (fst S) (fst T)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_stgy (S, n) (T, n)\<close>
  using cdcl\<^sub>W_restart_stgy.intros [of \<open>(S, n)\<close> \<open>(T, n)\<close>]
  by auto

lemma rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy:
  \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* (S, n) (T, n)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    by (auto dest!: cdcl\<^sub>W_stgy_cdcl\<^sub>W_restart_stgy[of _ _ n])
  done

lemma cdcl\<^sub>W_restart_dcl\<^sub>W_all_struct_inv:
  \<open>cdcl\<^sub>W_restart_stgy S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv (fst S) \<Longrightarrow>  cdcl\<^sub>W_all_struct_inv (fst T)\<close>
  using cdcl\<^sub>W_all_struct_inv_inv[OF cdcl\<^sub>W_restart_stgy_cdcl\<^sub>W_restart] .

lemma rtranclp_cdcl\<^sub>W_restart_dcl\<^sub>W_all_struct_inv:
  \<open>cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv (fst S) \<Longrightarrow>  cdcl\<^sub>W_all_struct_inv (fst T)\<close>
  by (induction rule: rtranclp_induct)
     (auto intro: cdcl\<^sub>W_restart_dcl\<^sub>W_all_struct_inv)

lemma restart_cdcl\<^sub>W_stgy_invariant:
  \<open>restart S T \<Longrightarrow> cdcl\<^sub>W_stgy_invariant T\<close>
  by (auto simp: restart.simps cdcl\<^sub>W_stgy_invariant_def state_prop no_smaller_confl_def)

lemma cdcl\<^sub>W_restart_dcl\<^sub>W_stgy_invariant:
  \<open>cdcl\<^sub>W_restart_stgy S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv (fst S) \<Longrightarrow> cdcl\<^sub>W_stgy_invariant (fst S) \<Longrightarrow>
      cdcl\<^sub>W_stgy_invariant (fst T)\<close>
  apply (induction rule: cdcl\<^sub>W_restart_stgy.induct)
  subgoal using cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant .
  subgoal by (auto dest!: cdcl\<^sub>W_rf.intros cdcl\<^sub>W_restart.intros simp: restart_cdcl\<^sub>W_stgy_invariant)
  done

lemma rtranclp_cdcl\<^sub>W_restart_dcl\<^sub>W_stgy_invariant:
  \<open>cdcl\<^sub>W_restart_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_all_struct_inv (fst S) \<Longrightarrow> cdcl\<^sub>W_stgy_invariant (fst S) \<Longrightarrow>
      cdcl\<^sub>W_stgy_invariant (fst T)\<close>
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal by (auto simp: rtranclp_cdcl\<^sub>W_restart_dcl\<^sub>W_all_struct_inv cdcl\<^sub>W_restart_dcl\<^sub>W_stgy_invariant)
  done

end

locale cdcl\<^sub>W_restart_restart_ops =
  conflict_driven_clause_learning\<^sub>W
    state_eq
    state
    \<comment> \<open>functions for the state:\<close>
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b\<close> and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and

    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close> +
  fixes
    f :: \<open>nat \<Rightarrow> nat\<close>

locale cdcl\<^sub>W_restart_restart =
  cdcl\<^sub>W_restart_restart_ops +
  assumes
    f: \<open>unbounded f\<close>


text \<open>The condition of the differences of cardinality has to be strict.
  Otherwise, you could be in a strange state, where nothing remains to do, but a restart is done.
  See the proof of well-foundedness. The same applies for the \<^term>\<open>full1 cdcl\<^sub>W_stgy S T\<close>:
  With a \<^term>\<open>full cdcl\<^sub>W_stgy S T\<close>, this rules could be applied one after the other, doing
  nothing each time.
\<close>
context cdcl\<^sub>W_restart_restart_ops
begin
inductive cdcl\<^sub>W_merge_with_restart where
restart_step:
  \<open>(cdcl\<^sub>W_stgy^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T
  \<Longrightarrow> card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n
  \<Longrightarrow> restart T U \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (U, Suc n)\<close> |
restart_full: \<open>full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)\<close>

lemma cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* (fst S) (fst T)\<close>
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
  (auto dest!: relpowp_imp_rtranclp rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart cdcl\<^sub>W_restart.rf
    cdcl\<^sub>W_rf.restart tranclp_into_rtranclp simp: full1_def)

lemma cdcl\<^sub>W_merge_with_restart_increasing_number:
  \<open>cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> snd T = 1 + snd S\<close>
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct) auto

lemma \<open>full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)\<close>
  using restart_full by blast

lemma cdcl\<^sub>W_all_struct_inv_learned_clss_bound:
  assumes inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (init_clss S))\<close>
proof
  fix C
  assume C: \<open>C \<in> set_mset (learned_clss S)\<close>
  have \<open>distinct_mset C\<close>
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by auto
  moreover have \<open>\<not>tautology C\<close>
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def by auto
  moreover
    have \<open>atms_of C \<subseteq> atms_of_mm (learned_clss S)\<close>
      using C by auto
    then have \<open>atms_of C \<subseteq> atms_of_mm (init_clss S)\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def by force
  moreover have \<open>finite (atms_of_mm (init_clss S))\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  ultimately show \<open>C \<in> simple_clss (atms_of_mm (init_clss S))\<close>
    using distinct_mset_not_tautology_implies_in_simple_clss simple_clss_mono
    by blast
qed

lemma cdcl\<^sub>W_merge_with_restart_init_clss:
  \<open>cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow>
  init_clss (fst S) = init_clss (fst T)\<close>
  using cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss by blast

lemma (in cdcl\<^sub>W_restart_restart)
  \<open>wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_merge_with_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
    then obtain g where
    g: \<open>\<And>i. cdcl\<^sub>W_merge_with_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have \<open>init_clss (fst (g i)) = init_clss (fst (g 0))\<close>
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_merge_with_restart_init_clss)
    } note init_g = this
  let ?S = \<open>g 0\<close>
  have \<open>finite (atms_of_mm (init_clss (fst ?S)))\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: \<open>\<And>i. snd (g i) = i + snd (g 0)\<close>
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_merge_with_restart_increasing_number g)
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: \<open>f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close> and
    \<open>k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume \<open>no_step cdcl\<^sub>W_stgy (fst (g i))\<close>
    with g[of i]
    have False
      proof (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where \<open>cdcl\<^sub>W_stgy S S'\<close>
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: \<open>m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))\<close> and
    \<open>m > f (snd (g k))\<close> and
    \<open>restart T (fst (g (k+1)))\<close> and
    cdcl\<^sub>W_stgy: \<open>(cdcl\<^sub>W_stgy ^^ m) (fst (g k)) T\<close>
    using g[of k] H[of \<open>Suc k\<close>] by (force simp: cdcl\<^sub>W_merge_with_restart.simps full1_def)
  have \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close>
    using cdcl\<^sub>W_stgy relpowp_imp_rtranclp by metis
  then have \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using inv[of k] rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
    by blast
  moreover have \<open>card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have \<open>card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
      by linarith
  moreover
    have \<open>init_clss (fst (g k)) = init_clss T\<close>
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
      rtranclp_cdcl\<^sub>W_restart_init_clss inv unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have \<open>init_clss (fst ?S) = init_clss T\<close>
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_merge_with_restart_distinct_mset_clauses:
  assumes invR: \<open>cdcl\<^sub>W_all_struct_inv (fst R)\<close> and
  st: \<open>cdcl\<^sub>W_merge_with_restart R S\<close> and
  dist: \<open>distinct_mset (clauses (fst R))\<close> and
  R: \<open>no_smaller_propa (fst R)\<close>
  shows \<open>distinct_mset (clauses (fst S))\<close>
  using assms(2,1,3,4)
proof induction
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have \<open>distinct_mset (clauses T)\<close>
    using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close>  unfolding clauses_def
    by (metis distinct_mset_union fstI restartE subset_mset.le_iff_add union_assoc)
qed

inductive cdcl\<^sub>W_restart_with_restart where
restart_step:
  \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T \<Longrightarrow>
     card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n \<Longrightarrow>
     restart T U \<Longrightarrow>
   cdcl\<^sub>W_restart_with_restart (S, n) (U, Suc n)\<close> |
restart_full: \<open>full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_with_restart (S, n) (T, Suc n)\<close>

lemma cdcl\<^sub>W_restart_with_restart_rtranclp_cdcl\<^sub>W_restart:
  \<open>cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* (fst S) (fst T)\<close>
  apply (induction rule: cdcl\<^sub>W_restart_with_restart.induct)
  by (auto dest!: relpowp_imp_rtranclp tranclp_into_rtranclp cdcl\<^sub>W_restart.rf
     cdcl\<^sub>W_rf.restart rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
    simp: full1_def)

lemma cdcl\<^sub>W_restart_with_restart_increasing_number:
  \<open>cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow> snd T = 1 + snd S\<close>
  by (induction rule: cdcl\<^sub>W_restart_with_restart.induct) auto

lemma \<open>full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_restart_with_restart (S, n) (T, Suc n)\<close>
  using restart_full by blast

lemma cdcl\<^sub>W_restart_with_restart_init_clss:
  \<open>cdcl\<^sub>W_restart_with_restart S T \<Longrightarrow>  cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow>
     init_clss (fst S) = init_clss (fst T)\<close>
  using cdcl\<^sub>W_restart_with_restart_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss by blast

theorem (in cdcl\<^sub>W_restart_restart)
  \<open>wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_restart_with_restart S T}\<close>
proof (rule ccontr)
  assume \<open>\<not> ?thesis\<close>
    then obtain g where
    g: \<open>\<And>i. cdcl\<^sub>W_restart_with_restart (g i) (g (Suc i))\<close> and
    inv: \<open>\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))\<close>
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have \<open>init_clss (fst (g i)) = init_clss (fst (g 0))\<close>
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_restart_with_restart_init_clss)
    } note init_g = this
  let ?S = \<open>g 0\<close>
  have \<open>finite (atms_of_mm (init_clss (fst ?S)))\<close>
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: \<open>\<And>i. snd (g i) = i + snd (g 0)\<close>
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_restart_with_restart_increasing_number g)
  then have snd_g_0: \<open>\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)\<close>
    by blast
  have unbounded_f_g: \<open>unbounded (\<lambda>i. f (snd (g i)))\<close>
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: \<open>f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close> and
    \<open>k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
   have H: False if \<open>no_step cdcl\<^sub>W_stgy (fst (g i))\<close> for i
     using g[of i] that
   proof (induction rule: cdcl\<^sub>W_restart_with_restart.induct)
     case (restart_step S T n) note H = this(1) and c = this(2) and n_s = this(4)
    obtain S' where \<open>cdcl\<^sub>W_stgy S S'\<close>
      using H c by (subst (asm) rtranclp_unfold) (auto dest!: tranclpD)
     then show False using n_s by auto
   next
     case (restart_full S T)
     then show False unfolding full1_def by (auto dest: tranclpD)
   qed
  obtain m T where
    m: \<open>m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))\<close> and
    \<open>m > f (snd (g k))\<close> and
    \<open>restart T (fst (g (k+1)))\<close> and
    cdcl\<^sub>W_stgy: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close>
    using g[of k] H[of \<open>Suc k\<close>] by (force simp: cdcl\<^sub>W_restart_with_restart.simps full1_def)
  have \<open>cdcl\<^sub>W_all_struct_inv T\<close>
    using inv[of k] rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart
      cdcl\<^sub>W_stgy by blast
  moreover {
    have \<open>card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have \<open>card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))\<close>
      by linarith
  }
  moreover {
    have \<open>init_clss (fst (g k)) = init_clss T\<close>
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart rtranclp_cdcl\<^sub>W_restart_init_clss
      inv unfolding cdcl\<^sub>W_all_struct_inv_def
      by blast
    then have \<open>init_clss (fst ?S) = init_clss T\<close>
      using init_g[of k] by auto
  }
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_restart_with_restart_distinct_mset_clauses:
  assumes invR: \<open>cdcl\<^sub>W_all_struct_inv (fst R)\<close> and
  st: \<open>cdcl\<^sub>W_restart_with_restart R S\<close> and
  dist: \<open>distinct_mset (clauses (fst R))\<close> and
  R: \<open>no_smaller_propa (fst R)\<close>
  shows \<open>distinct_mset (clauses (fst S))\<close>
  using assms(2,1,3,4)
proof (induction)
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step S T n U)
  then have \<open>distinct_mset (clauses T)\<close> using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T]
    unfolding full1_def by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close> unfolding clauses_def
    by (metis distinct_mset_union fstI restartE subset_mset.le_iff_add union_assoc)
qed

end

locale luby_sequence =
  fixes ur :: nat (*unit run*)
  assumes \<open>ur > 0\<close>
begin

lemma exists_luby_decomp:
  fixes i ::nat
  shows \<open>\<exists>k::nat. (2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1) \<or> i = 2 ^ k - 1\<close>
proof (induction i)
  case 0
  then show ?case
    by (rule exI[of _ 0], simp)
next
  case (Suc n)
  then obtain k where \<open>2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1\<close>
    by blast
  then consider
      (st_interv) \<open>2 ^ (k - 1) \<le> n\<close> and \<open>n \<le> 2 ^ k - 2\<close>
    | (end_interv) \<open>2 ^ (k - 1) \<le> n\<close> and \<open>n = 2 ^ k - 2\<close>
    | (pow2) \<open>n = 2 ^ k - 1\<close>
    by linarith
  then show ?case
    proof cases
      case st_interv
      then show ?thesis apply - apply (rule exI[of _ k])
        by (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_lessI
          \<open>2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1\<close> diff_self_eq_0
          dual_order.trans le_SucI le_imp_less_Suc numeral_2_eq_2 one_le_numeral
          one_le_power zero_less_numeral zero_less_power)
    next
      case end_interv
      then show ?thesis apply - apply (rule exI[of _ k]) by auto
    next
      case pow2
      then show ?thesis apply - apply (rule exI[of _ \<open>k+1\<close>]) by auto
    qed
qed

text \<open>
  Luby sequences are defined by:
   \<^item> @{term \<open>(2::nat)^(k::nat)- 1\<close>}, if @{term \<open>i = 2^k - 1\<close>}
   \<^item> @{term \<open>luby_sequence_core (i - (2::nat)^(k - 1) + 1)\<close>}, if @{term \<open>2^(k - 1) \<le> i\<close>} and
   @{term \<open>i \<le> 2^k - 1\<close>}

Then the sequence is then scaled by a constant unit run (called @{term ur} here), strictly positive.
\<close>
function luby_sequence_core :: \<open>nat \<Rightarrow> nat\<close> where
\<open>luby_sequence_core i =
  (if \<exists>k. i = 2^k - 1
  then 2^((SOME k. i = 2^k - 1) - 1)
  else luby_sequence_core (i - 2^((SOME k. 2^(k-1)\<le> i \<and> i < 2^k - 1) - 1) + 1))\<close>
by auto
termination
proof (relation \<open>less_than\<close>, goal_cases)
  case 1
  then show ?case by auto
next
  case (2 i)
  let ?k = \<open>SOME k. 2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1\<close>
  have \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close>
    by (rule someI_ex) (use 2 exists_luby_decomp in blast)
  then show ?case
    (* sledgehammer *)
  proof -
    have \<open>\<forall>n na. \<not> (1::nat) \<le> n \<or> 1 \<le> n ^ na\<close>
      by (meson one_le_power)
    then have f1: \<open>(1::nat) \<le> 2 ^ (?k - 1)\<close>
      using one_le_numeral by blast
    have f2: \<open>i - 2 ^ (?k - 1) + 2 ^ (?k - 1) = i\<close>
      using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> le_add_diff_inverse2 by blast
    have f3: \<open>2 ^ ?k - 1 \<noteq> Suc 0\<close>
      using f1 \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> by linarith
    have \<open>2 ^ ?k - (1::nat) \<noteq> 0\<close>
      using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> gr_implies_not0 by blast
    then have f4: \<open>2 ^ ?k \<noteq> (1::nat)\<close>
      by linarith
    have f5: \<open>\<forall>n na. if na = 0 then (n::nat) ^ na = 1 else n ^ na = n * n ^ (na - 1)\<close>
      by (simp add: power_eq_if)
    then have \<open>?k \<noteq> 0\<close>
      using f4 by meson
    then have \<open>2 ^ (?k - 1) \<noteq> Suc 0\<close>
      using f5 f3 by presburger
    then have \<open>Suc 0 < 2 ^ (?k - 1)\<close>
      using f1 by linarith
    then show ?thesis
      using f2 less_than_iff by presburger
  qed
qed

declare luby_sequence_core.simps[simp del]

lemma two_pover_n_eq_two_power_n'_eq:
  assumes H: \<open>(2::nat) ^ (k::nat) - 1 = 2 ^ k' - 1\<close>
  shows \<open>k' = k\<close>
proof -
  have \<open>(2::nat) ^ (k::nat) = 2 ^ k'\<close>
    using H by (metis One_nat_def Suc_pred zero_less_numeral zero_less_power)
  then show ?thesis by simp
qed

lemma luby_sequence_core_two_power_minus_one:
  \<open>luby_sequence_core (2^k - 1) = 2^(k-1)\<close> (is \<open>?L = ?K\<close>)
proof -
  have decomp: \<open>\<exists>ka. 2 ^ k - 1 = 2 ^ ka - 1\<close>
    by auto
  have \<open>?L = 2^((SOME k'. (2::nat)^k - 1 = 2^k' - 1) - 1)\<close>
    apply (subst luby_sequence_core.simps, subst decomp)
    by simp
  moreover have \<open>(SOME k'. (2::nat)^k - 1 = 2^k' - 1) = k\<close>
    apply (rule some_equality)
      apply simp
      using two_pover_n_eq_two_power_n'_eq by blast
  ultimately show ?thesis by presburger
qed

lemma different_luby_decomposition_false:
  assumes
    H: \<open>2 ^ (k - Suc 0) \<le> i\<close> and
    k': \<open>i < 2 ^ k' - Suc 0\<close> and
    k_k': \<open>k > k'\<close>
  shows \<open>False\<close>
proof -
  have \<open>2 ^ k' - Suc 0 < 2 ^ (k - Suc 0)\<close>
    using k_k' less_eq_Suc_le by auto
  then show ?thesis
    using H k' by linarith
qed

lemma luby_sequence_core_not_two_power_minus_one:
  assumes
    k_i: \<open>2 ^ (k - 1) \<le> i\<close> and
    i_k: \<open>i < 2^ k - 1\<close>
  shows \<open>luby_sequence_core i = luby_sequence_core (i - 2 ^ (k - 1) + 1)\<close>
proof -
  have H: \<open>\<not> (\<exists>ka. i = 2 ^ ka - 1)\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain k'::nat where k': \<open>i = 2 ^ k' - 1\<close> by blast
      have \<open>(2::nat) ^ k' - 1 < 2 ^ k - 1\<close>
        using i_k unfolding k' .
      then have \<open>(2::nat) ^ k' < 2 ^ k\<close>
        by linarith
      then have \<open>k' < k\<close>
        by simp
      have \<open>2 ^ (k - 1) \<le> 2 ^ k' - (1::nat)\<close>
        using k_i unfolding k' .
      then have \<open>(2::nat) ^ (k-1) < 2 ^ k'\<close>
        by (metis Suc_diff_1 not_le not_less_eq zero_less_numeral zero_less_power)
      then have \<open>k-1 < k'\<close>
        by simp

      show False using \<open>k' < k\<close> \<open>k-1 < k'\<close> by linarith
    qed
  have \<open>\<And>k k'. 2 ^ (k - Suc 0) \<le> i \<Longrightarrow> i < 2 ^ k - Suc 0 \<Longrightarrow> 2 ^ (k' - Suc 0) \<le> i \<Longrightarrow>
    i < 2 ^ k' - Suc 0 \<Longrightarrow> k = k'\<close>
    by (meson different_luby_decomposition_false linorder_neqE_nat)
  then have k: \<open>(SOME k. 2 ^ (k - Suc 0) \<le> i \<and> i < 2 ^ k - Suc 0) = k\<close>
    using k_i i_k by auto
  show ?thesis
    apply (subst luby_sequence_core.simps[of i], subst H)
    by (simp add: k)
qed

lemma unbounded_luby_sequence_core: \<open>unbounded luby_sequence_core\<close>
  unfolding bounded_def
proof
  assume \<open>\<exists>b. \<forall>n. luby_sequence_core n \<le> b\<close>
  then obtain b where b: \<open>\<And>n. luby_sequence_core n \<le> b\<close>
    by metis
  have \<open>luby_sequence_core (2^(b+1) - 1) = 2^b\<close>
    using luby_sequence_core_two_power_minus_one[of \<open>b+1\<close>] by simp
  moreover have \<open>(2::nat)^b > b\<close>
    by (induction b) auto
  ultimately show False using b[of \<open>2^(b+1) - 1\<close>] by linarith
qed

abbreviation luby_sequence :: \<open>nat \<Rightarrow> nat\<close> where
\<open>luby_sequence n \<equiv>  ur * luby_sequence_core n\<close>

lemma bounded_luby_sequence: \<open>unbounded luby_sequence\<close>
  using bounded_const_product[of ur] luby_sequence_axioms
  luby_sequence_def unbounded_luby_sequence_core by blast

lemma luby_sequence_core_0: \<open>luby_sequence_core 0 = 1\<close>
proof -
  have 0: \<open>(0::nat) = 2^0-1\<close>
    by auto
  show ?thesis
    by (subst 0, subst luby_sequence_core_two_power_minus_one) simp
qed

lemma \<open>luby_sequence_core n \<ge> 1\<close>
proof (induction n rule: nat_less_induct_case)
  case 0
  then show ?case by (simp add: luby_sequence_core_0)
next
  case (Suc n) note IH = this

  consider
    (interv) k where \<open>2 ^ (k - 1) \<le> Suc n\<close> and \<open>Suc n < 2 ^ k - 1\<close> |
    (pow2)  k where \<open>Suc n = 2 ^ k - Suc 0\<close>
    using exists_luby_decomp[of \<open>Suc n\<close>] by auto

  then show ?case
     proof cases
       case pow2
       show ?thesis
         using luby_sequence_core_two_power_minus_one pow2 by auto
     next
       case interv
       have n: \<open>Suc n - 2 ^ (k - 1) + 1 < Suc n\<close>
         by (metis Suc_1 Suc_eq_plus1 add.commute add_diff_cancel_left' add_less_mono1 gr0I
           interv(1) interv(2) le_add_diff_inverse2 less_Suc_eq not_le power_0 power_one_right
           power_strict_increasing_iff)
       show ?thesis
         apply (subst luby_sequence_core_not_two_power_minus_one[OF interv])
         using IH n by auto
     qed
qed
end

locale luby_sequence_restart =
  luby_sequence ur +
  conflict_driven_clause_learning\<^sub>W
    \<comment> \<open>functions for the state:\<close>
    state_eq state
      \<comment> \<open>access functions:\<close>
    trail init_clss learned_clss conflicting
      \<comment> \<open>changing state:\<close>
    cons_trail tl_trail add_learned_cls remove_cls
    update_conflicting

      \<comment> \<open>get state:\<close>
    init_state
  for
    ur :: nat and
    state_eq :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits \<times> 'v clauses \<times> 'v clauses \<times> 'v clause option \<times>
      'b\<close> and
    trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lits\<close> and
    hd_trail :: \<open>'st \<Rightarrow> ('v, 'v clause) ann_lit\<close> and
    init_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    learned_clss :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    conflicting :: \<open>'st \<Rightarrow> 'v clause option\<close> and

    cons_trail :: \<open>('v, 'v clause) ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    add_learned_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    remove_cls :: \<open>'v clause \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    update_conflicting :: \<open>'v clause option \<Rightarrow> 'st \<Rightarrow> 'st\<close> and

    init_state :: \<open>'v clauses \<Rightarrow> 'st\<close>
begin

sublocale cdcl\<^sub>W_restart_restart where
  f = luby_sequence
  by unfold_locales (use bounded_luby_sequence in blast)

end

end
