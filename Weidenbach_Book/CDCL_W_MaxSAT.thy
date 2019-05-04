theory CDCL_W_MaxSAT
  imports CDCL_W_Optimal_Model
begin


subsection \<open>Partial MAX-SAT\<close>

definition weight_on_clauses where
  \<open>weight_on_clauses N\<^sub>S \<rho> I = (\<Sum>C \<in># (filter_mset (\<lambda>C. I \<Turnstile> C) N\<^sub>S). \<rho> C)\<close>

definition atms_exactly_m :: \<open>'v partial_interp \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
  \<open>atms_exactly_m I N \<longleftrightarrow>
  total_over_m I (set_mset N) \<and>
  atms_of_s I \<subseteq> atms_of_mm N\<close>

text \<open>Partial in the name refers to the fact that not all clauses are soft clauses, not to the fact
  that we consider partial models.\<close>
inductive partial_max_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
  partial_max_sat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
if
  \<open>I \<Turnstile>sm N\<^sub>H\<close> and
  \<open>atms_exactly_m I ((N\<^sub>H + N\<^sub>S))\<close> and
  \<open>consistent_interp I\<close> and
  \<open>\<And>I'. consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> |
  partial_max_unsat:
  \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

inductive partial_min_sat :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> ('v clause \<Rightarrow> nat) \<Rightarrow>
  'v partial_interp option \<Rightarrow> bool\<close> where
  partial_min_sat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
if
  \<open>I \<Turnstile>sm N\<^sub>H\<close> and
  \<open>atms_exactly_m I (N\<^sub>H + N\<^sub>S)\<close> and
  \<open>consistent_interp I\<close> and
  \<open>\<And>I'. consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> |
  partial_min_unsat:
  \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N\<^sub>H)\<close>

lemma atms_exactly_m_finite:
  assumes \<open>atms_exactly_m I N\<close>
  shows \<open>finite I\<close>
proof -
  have \<open>I \<subseteq> Pos ` (atms_of_mm N) \<union> Neg ` atms_of_mm N\<close>
    using assms by (force simp: total_over_m_def  atms_exactly_m_def lit_in_set_iff_atm
        atms_of_s_def)
  from finite_subset[OF this] show ?thesis by auto
qed


lemma
  fixes N\<^sub>H :: \<open>'v clauses\<close>
  assumes \<open>satisfiable (set_mset N\<^sub>H)\<close>
  shows sat_partial_max_sat: \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close> and
    sat_partial_min_sat: \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
proof -
  let ?Is = \<open>{I. atms_exactly_m I ((N\<^sub>H + N\<^sub>S)) \<and>  consistent_interp I \<and>
     I \<Turnstile>sm N\<^sub>H}\<close>
  let ?Is'= \<open>{I. atms_exactly_m I ((N\<^sub>H + N\<^sub>S)) \<and> consistent_interp I \<and>
    I \<Turnstile>sm N\<^sub>H \<and> finite I}\<close>
  have Is: \<open>?Is = ?Is'\<close>
    by (auto simp: atms_of_s_def atms_exactly_m_finite)
  have \<open>?Is' \<subseteq> set_mset ` simple_clss (atms_of_mm (N\<^sub>H + N\<^sub>S))\<close>
    apply rule
    unfolding image_iff
    by (rule_tac x= \<open>mset_set x\<close> in bexI)
      (auto simp: simple_clss_def atms_exactly_m_def image_iff
        atms_of_s_def atms_of_def distinct_mset_mset_set consistent_interp_tuatology_mset_set)
  from finite_subset[OF this] have fin: \<open>finite ?Is\<close> unfolding Is
    by (auto simp: simple_clss_finite)
  then have fin': \<open>finite (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
    by auto
  define \<rho>I where
    \<open>\<rho>I = Min (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have nempty: \<open>?Is \<noteq> {}\<close>
  proof -
    obtain I where I:
      \<open>total_over_m I (set_mset N\<^sub>H)\<close>
      \<open>I \<Turnstile>sm N\<^sub>H\<close>
      \<open>consistent_interp I\<close>
      \<open>atms_of_s I \<subseteq> atms_of_mm N\<^sub>H\<close>
      using assms unfolding satisfiable_def_min atms_exactly_m_def
      by (auto simp: atms_of_s_def atm_of_def total_over_m_def)
    let ?I = \<open>I \<union> Pos ` {x \<in> atms_of_mm N\<^sub>S. x \<notin> atm_of ` I}\<close>
    have \<open>?I \<in> ?Is\<close>
      using I
      by (auto simp: atms_exactly_m_def total_over_m_alt_def image_iff
          lit_in_set_iff_atm)
        (auto simp: consistent_interp_def uminus_lit_swap)
    then show ?thesis
      by blast
  qed
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Min_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>sm N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<ge> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Min_le[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_min_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: atms_exactly_m_finite\<close>)
  then show \<open>\<exists>I. partial_min_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast

  define \<rho>I where
    \<open>\<rho>I = Max (weight_on_clauses N\<^sub>S \<rho> ` ?Is)\<close>
  have \<open>\<rho>I \<in> weight_on_clauses N\<^sub>S \<rho> ` ?Is\<close>
    unfolding \<rho>I_def
    by (rule Max_in[OF fin']) (use nempty in auto)
  then obtain I :: \<open>'v partial_interp\<close> where
    \<open>weight_on_clauses N\<^sub>S \<rho> I = \<rho>I\<close> and
    \<open>I \<in> ?Is\<close>
    by blast
  then have H: \<open>consistent_interp I' \<Longrightarrow> atms_exactly_m I' (N\<^sub>H + N\<^sub>S) \<Longrightarrow> I' \<Turnstile>m N\<^sub>H \<Longrightarrow>
      weight_on_clauses N\<^sub>S \<rho> I' \<le> weight_on_clauses N\<^sub>S \<rho> I\<close> for I'
    using Max_ge[OF fin', of \<open>weight_on_clauses N\<^sub>S \<rho> I'\<close>]
    unfolding \<rho>I_def[symmetric]
    by auto
  then have \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    apply -
    by (rule partial_max_sat)
      (use fin \<open>I \<in> ?Is\<close> in \<open>auto simp: atms_exactly_m_finite
        consistent_interp_tuatology_mset_set\<close>)
  then show \<open>\<exists>I. partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some I)\<close>
    by fast
qed

inductive weight_sat
  :: \<open>'v clauses \<Rightarrow> ('v literal multiset \<Rightarrow> 'a :: linorder) \<Rightarrow>
    'v literal multiset option \<Rightarrow> bool\<close>
where
  weight_sat:
  \<open>weight_sat N \<rho> (Some I)\<close>
if
  \<open>set_mset I \<Turnstile>sm N\<close> and
  \<open>atms_exactly_m (set_mset I) N\<close> and
  \<open>consistent_interp (set_mset I)\<close> and
  \<open>distinct_mset I\<close>
  \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> atms_exactly_m (set_mset I') N \<Longrightarrow> distinct_mset I' \<Longrightarrow>
      set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho> I' \<ge> \<rho> I\<close> |
  partial_max_unsat:
  \<open>weight_sat N \<rho> None\<close>
if
  \<open>unsatisfiable (set_mset N)\<close>

lemma partial_max_sat_is_weight_sat: (* \htmllink{ocdcl-maxsat}*)
  fixes additional_atm :: \<open>'v clause \<Rightarrow> 'v\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    N\<^sub>S :: \<open>'v clauses\<close>
  defines
    \<open>\<rho>' \<equiv> (\<lambda>C. sum_mset
       ((\<lambda>L. if L \<in> Pos ` additional_atm ` set_mset N\<^sub>S
         then count N\<^sub>S (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
           * \<rho> (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
         else 0) `# C))\<close>
  assumes
    add: \<open>\<And>C. C \<in># N\<^sub>S \<Longrightarrow> additional_atm C \<notin> atms_of_mm (N\<^sub>H + N\<^sub>S)\<close>
    \<open>\<And>C D. C \<in># N\<^sub>S \<Longrightarrow> D \<in># N\<^sub>S \<Longrightarrow> additional_atm C = additional_atm D \<longleftrightarrow> C = D\<close> and
    w: \<open>weight_sat (N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S) \<rho>' (Some I)\<close>
  shows
    \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some {L \<in> set_mset I. atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})\<close>
proof -
  define N where \<open>N \<equiv> N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S\<close>
  define cl_of where \<open>cl_of L = (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)\<close> for L
  from w
  have
    ent: \<open>set_mset I \<Turnstile>sm N\<close> and
    bi: \<open>atms_exactly_m (set_mset I) N\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    dist: \<open>distinct_mset I\<close> and
    weight: \<open>\<And>I'. consistent_interp (set_mset I') \<Longrightarrow> atms_exactly_m (set_mset I') N \<Longrightarrow>
      distinct_mset I' \<Longrightarrow> set_mset I' \<Turnstile>sm N \<Longrightarrow> \<rho>' I' \<ge> \<rho>' I\<close>
    unfolding N_def[symmetric]
    by (auto simp: weight_sat.simps)
  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
  have ent': \<open>set_mset I \<Turnstile>sm N\<^sub>H\<close>
    using ent unfolding true_clss_restrict
    by (auto simp: N_def)
  then have ent': \<open>?I \<Turnstile>sm N\<^sub>H\<close>
    apply (subst (asm) true_clss_restrict[symmetric])
    apply (rule true_clss_mono_left, assumption)
    apply auto
    done
  have [simp]: \<open>atms_of_ms ((\<lambda>C. add_mset (Pos (additional_atm C)) C) ` set_mset N\<^sub>S) =
    additional_atm ` set_mset N\<^sub>S \<union> atms_of_ms (set_mset N\<^sub>S)\<close>
    by (auto simp: atms_of_ms_def)
  have bi': \<open>atms_exactly_m ?I (N\<^sub>H + N\<^sub>S)\<close>
    using bi
    by (auto simp: atms_exactly_m_def total_over_m_def total_over_set_def
        atms_of_s_def N_def)
  have cons': \<open>consistent_interp ?I\<close>
    using cons by (auto simp: consistent_interp_def)
  have [simp]: \<open>cl_of (Pos (additional_atm xb)) = xb\<close>
    if \<open>xb \<in># N\<^sub>S\<close> for xb
    using someI[of \<open>\<lambda>C. additional_atm xb = additional_atm C\<close> xb] add that
    unfolding cl_of_def
    by auto

  let ?I = \<open>{L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)} \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>set_mset I \<Turnstile> C}
    \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. set_mset I \<Turnstile> C}\<close>
  have \<open>consistent_interp ?I\<close>
    using cons add by (auto simp: consistent_interp_def
        atms_exactly_m_def uminus_lit_swap
        dest: add)
  moreover have \<open>atms_exactly_m ?I N\<close>
    using bi
    by (auto simp: N_def atms_exactly_m_def total_over_m_def
        total_over_set_def image_image)
  moreover have \<open>?I \<Turnstile>sm N\<close>
    using ent by (auto simp: N_def true_clss_def image_image
          atm_of_lit_in_atms_of true_cls_def
        dest!: multi_member_split)
  moreover have \<open>set_mset (mset_set ?I) = ?I\<close> and fin: \<open>finite ?I\<close>
    by (auto simp: atms_exactly_m_finite)
  moreover have \<open>distinct_mset (mset_set ?I)\<close>
    by (auto simp: distinct_mset_mset_set)
  ultimately have \<open>\<rho>' (mset_set ?I) \<ge> \<rho>' I\<close>
    using weight[of \<open>mset_set ?I\<close>]
    by argo
  moreover have \<open>\<rho>' (mset_set ?I) \<le> \<rho>' I\<close>
    using ent
    by (auto simp: \<rho>'_def sum_mset_inter_restrict[symmetric] mset_set_subset_iff N_def
        intro!: sum_image_mset_mono
        dest!: multi_member_split)
  ultimately have I_I: \<open>\<rho>' (mset_set ?I) = \<rho>' I\<close>
    by linarith

  have min: \<open>weight_on_clauses N\<^sub>S \<rho> I'
      \<le> weight_on_clauses N\<^sub>S \<rho> {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)}\<close>
    if
      cons: \<open>consistent_interp I'\<close> and
      bit: \<open>atms_exactly_m I' (N\<^sub>H + N\<^sub>S)\<close> and
      I': \<open>I' \<Turnstile>sm N\<^sub>H\<close>
    for I'
  proof -
    let ?I' = \<open>I' \<union> Pos ` additional_atm ` {C \<in> set_mset N\<^sub>S. \<not>I' \<Turnstile> C}
      \<union> Neg ` additional_atm ` {C \<in> set_mset N\<^sub>S. I' \<Turnstile> C}\<close>
    have \<open>consistent_interp ?I'\<close>
      using cons bit add by (auto simp: consistent_interp_def
          atms_exactly_m_def uminus_lit_swap
          dest: add)
    moreover have \<open>atms_exactly_m ?I' N\<close>
      using bit
      by (auto simp: N_def atms_exactly_m_def total_over_m_def
          total_over_set_def image_image)
    moreover have \<open>?I' \<Turnstile>sm N\<close>
      using I' by (auto simp: N_def true_clss_def image_image
          dest!: multi_member_split)
    moreover have \<open>set_mset (mset_set ?I') = ?I'\<close> and fin: \<open>finite ?I'\<close>
      using bit by (auto simp: atms_exactly_m_finite)
    moreover have \<open>distinct_mset (mset_set ?I')\<close>
      by (auto simp: distinct_mset_mset_set)
    ultimately have I'_I: \<open>\<rho>' (mset_set ?I') \<ge> \<rho>' I\<close>
      using weight[of \<open>mset_set ?I'\<close>]
      by argo
    have inj: \<open>inj_on cl_of (I' \<inter> (\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S)\<close> for I'
      using add by (auto simp: inj_on_def)

    have we: \<open>weight_on_clauses N\<^sub>S \<rho> I' = sum_mset (\<rho> `# N\<^sub>S) -
      sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close> for I'
      unfolding weight_on_clauses_def
      apply (subst (3) multiset_partition[of _ \<open>(\<Turnstile>) I'\<close>])
      unfolding image_mset_union sum_mset.union
      by (auto simp: comp_def)
    have H: \<open>sum_mset
       (\<rho> `#
        filter_mset (Not \<circ> (\<Turnstile>) {L. L \<in># I \<and> atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})
         N\<^sub>S) = \<rho>' I\<close>
            unfolding I_I[symmetric] unfolding \<rho>'_def cl_of_def[symmetric]
              sum_mset_sum_count if_distrib
            apply (auto simp: sum_mset_sum_count image_image simp flip: sum.inter_restrict
                cong: if_cong)
            apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
            apply ((use inj in auto; fail)+)[2]
            apply (rule sum.cong)
            apply auto[]
            using inj[of \<open>set_mset I\<close>] \<open>set_mset I \<Turnstile>sm N\<close> assms(2)
            apply (auto dest!: multi_member_split simp: N_def image_Int
                atm_of_lit_in_atms_of true_cls_def)[]
            using add apply (auto simp: true_cls_def)
            done
    have \<open>(\<Sum>x\<in>(I' \<union> (\<lambda>x. Pos (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> C} \<union>
         (\<lambda>x. Neg (additional_atm x)) ` {C. C \<in># N\<^sub>S \<and> I' \<Turnstile> C}) \<inter>
        (\<lambda>x. Pos (additional_atm x)) ` set_mset N\<^sub>S.
       count N\<^sub>S (cl_of x) * \<rho> (cl_of x))
    \<le> (\<Sum>A\<in>{a. a \<in># N\<^sub>S \<and> \<not> I' \<Turnstile> a}. count N\<^sub>S A * \<rho> A)\<close>
      apply (subst comm_monoid_add_class.sum.reindex_cong[symmetric, of cl_of, OF _ refl])
      apply ((use inj in auto; fail)+)[2]
      apply (rule ordered_comm_monoid_add_class.sum_mono2)
      using that add by (auto dest:  simp: N_def
          atms_exactly_m_def)
    then have \<open>sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S) \<ge> \<rho>' (mset_set ?I')\<close>
      using fin unfolding cl_of_def[symmetric] \<rho>'_def
      by (auto simp: \<rho>'_def
          simp add: sum_mset_sum_count image_image simp flip: sum.inter_restrict)
    then have \<open>\<rho>' I \<le> sum_mset (\<rho> `# filter_mset (Not \<circ> (\<Turnstile>) I') N\<^sub>S)\<close>
      using I'_I by auto
    then show ?thesis
      unfolding we H I_I apply -
      by auto
  qed

  show ?thesis
    apply (rule partial_max_sat.intros)
    subgoal using ent' by auto
    subgoal using bi' by fast
    subgoal using cons' by fast
    subgoal for I'
      by (rule min)
    done
qed

lemma sum_mset_cong:
  \<open>(\<And>a. a \<in># A \<Longrightarrow> f a = g a) \<Longrightarrow> (\<Sum>a\<in>#A. f a) = (\<Sum>a\<in>#A. g a)\<close>
  by (induction A) auto

lemma partial_max_sat_is_weight_sat_distinct: (* \htmllink{ocdcl-maxsat}*)
  fixes additional_atm :: \<open>'v clause \<Rightarrow> 'v\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> nat\<close> and
    N\<^sub>S :: \<open>'v clauses\<close>
  defines
    \<open>\<rho>' \<equiv> (\<lambda>C. sum_mset
       ((\<lambda>L. if L \<in> Pos ` additional_atm ` set_mset N\<^sub>S
         then \<rho> (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
         else 0) `# C))\<close>
  assumes
    \<open>distinct_mset N\<^sub>S\<close> and \<comment>\<open>This is implicit on paper\<close>
    add: \<open>\<And>C. C \<in># N\<^sub>S \<Longrightarrow> additional_atm C \<notin> atms_of_mm (N\<^sub>H + N\<^sub>S)\<close>
    \<open>\<And>C D. C \<in># N\<^sub>S \<Longrightarrow> D \<in># N\<^sub>S \<Longrightarrow> additional_atm C = additional_atm D \<longleftrightarrow> C = D\<close> and
    w: \<open>weight_sat (N\<^sub>H + (\<lambda>C. add_mset (Pos (additional_atm C)) C) `# N\<^sub>S) \<rho>' (Some I)\<close>
  shows
    \<open>partial_max_sat N\<^sub>H N\<^sub>S \<rho> (Some {L \<in> set_mset I. atm_of L \<in> atms_of_mm (N\<^sub>H + N\<^sub>S)})\<close>
proof -
  define cl_of where \<open>cl_of L = (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)\<close> for L
  have [simp]: \<open>cl_of (Pos (additional_atm xb)) = xb\<close>
    if \<open>xb \<in># N\<^sub>S\<close> for xb
    using someI[of \<open>\<lambda>C. additional_atm xb = additional_atm C\<close> xb] add that
    unfolding cl_of_def
    by auto
  have \<rho>': \<open>\<rho>' = (\<lambda>C. \<Sum>L\<in>#C. if L \<in> Pos ` additional_atm ` set_mset N\<^sub>S
                 then count N\<^sub>S
                       (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S) *
                      \<rho> (SOME C. L = Pos (additional_atm C) \<and> C \<in># N\<^sub>S)
                 else 0)\<close>
    unfolding cl_of_def[symmetric] \<rho>'_def
    using assms(2,4) by (auto intro!: ext sum_mset_cong simp: \<rho>'_def not_in_iff dest!: multi_member_split)
  show ?thesis
    apply (rule partial_max_sat_is_weight_sat[where additional_atm=additional_atm])
    subgoal by (rule assms(3))
    subgoal by (rule assms(4))
    subgoal unfolding \<rho>'[symmetric] by (rule assms(5))
    done
qed

lemma atms_exactly_m_alt_def:
  \<open>atms_exactly_m (set_mset y) N \<longleftrightarrow> atms_of y \<subseteq> atms_of_mm N \<and>
        total_over_m (set_mset y) (set_mset N)\<close>
  by (auto simp: atms_exactly_m_def atms_of_s_def atms_of_def
      atms_of_ms_def dest!: multi_member_split)

lemma atms_exactly_m_alt_def2:
  \<open>atms_exactly_m (set_mset y) N \<longleftrightarrow> atms_of y = atms_of_mm N\<close>
  by (metis atms_of_def atms_of_s_def atms_exactly_m_alt_def equalityI order_refl total_over_m_def
      total_over_set_alt_def)

lemma (in conflict_driven_clause_learning\<^sub>W_optimal_weight) full_cdcl_bnb_stgy_weight_sat:
  \<open>full cdcl_bnb_stgy (init_state N) T \<Longrightarrow> distinct_mset_mset N \<Longrightarrow> weight_sat N \<rho> (weight T)\<close>
  using full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state[of N T]
  apply (cases \<open>weight T = None\<close>)
  subgoal
    by (auto intro!: weight_sat.intros(2))
  subgoal premises p
    using p(1-4,6)
    apply (clarsimp simp only:)
    apply (rule weight_sat.intros(1))
    subgoal by auto
    subgoal by (auto simp: atms_exactly_m_alt_def)
    subgoal by auto
    subgoal by auto
    subgoal for J I'
      using p(5)[of I'] by (auto simp: atms_exactly_m_alt_def2)
    done
  done

end