theory Model_Enumeration
  imports Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    Weidenbach_Book_Base.Wellfounded_More
begin

lemma Ex_sat_model:
  assumes \<open>satisfiable (set_mset N)\<close>
  shows \<open>\<exists>M. set M \<Turnstile>sm N \<and>
           distinct M \<and>
           consistent_interp (set M) \<and>
           atm_of ` set M \<subseteq> atms_of_mm N\<close>
proof -
  from assms obtain I where
    I_N: \<open>I \<Turnstile>sm N\<close> and
    consistent: \<open>consistent_interp I\<close> and
    \<open>total_over_m I (set_mset N)\<close> and
    atms_I_N: \<open>atm_of ` I = atms_of_mm N\<close>
    unfolding satisfiable_def_min by blast
  have \<open>I \<subseteq> Pos ` (atms_of_mm N) \<union> Neg ` (atms_of_mm N)\<close>
    using atms_I_N
    by (smt in_set_image_subsetD literal.exhaust_sel subsetI sup_ge1 sup_ge2)
  then have \<open>finite I\<close>
    using infinite_super by fastforce
  then obtain I' where I': \<open>I = set I'\<close> and dist: \<open>distinct I'\<close>
    using finite_distinct_list by force
  show ?thesis
    apply (rule exI[of _ I'])
    using I_N dist consistent atms_I_N by (auto simp: I')
qed


definition all_models where
  \<open>all_models N = {M. set M \<Turnstile>sm N \<and> consistent_interp (set M) \<and>
    distinct M \<and> atm_of ` set M \<subseteq> atms_of_mm N}\<close>

lemma finite_all_models:
  \<open>finite (all_models N)\<close>
proof -
  let ?n = \<open>Pos ` (atms_of_mm N) \<union> Neg ` (atms_of_mm N)\<close>
  have H: \<open>all_models N \<subseteq> {M. set M \<subseteq> ?n \<and> length M \<le> card ?n}\<close>
    unfolding all_models_def
    apply (auto dest: imageI[of _ _ atm_of])
     apply (metis contra_subsetD image_eqI literal.exhaust_sel)
    by (smt atms_of_ms_finite card_mono distinct_card finite_Un finite_imageI
        finite_set_mset image_subset_iff literal.exhaust_sel subsetI sup_ge1 sup_ge2)
  show ?thesis
    apply (rule finite_subset)
     apply (rule H)
    apply (rule finite_lists_length_le)
    apply auto
    done
qed


inductive next_model where
  \<open>set M \<Turnstile>sm N \<Longrightarrow> distinct M \<Longrightarrow> consistent_interp (set M) \<Longrightarrow>
           atm_of ` set M \<subseteq> atms_of_mm N \<Longrightarrow> next_model M N\<close>

lemma image_mset_uminus_eq_image_mset_uminus_literals[simp]:
  \<open>image_mset uminus M' = image_mset uminus M \<longleftrightarrow> M = M'\<close> for M :: \<open>'v clause\<close>
  by (auto simp:inj_image_mset_eq_iff inj_def)

context
  fixes P :: \<open>'v literal set \<Rightarrow> bool\<close>
begin

inductive next_model_filtered  :: \<open>'v literal list option \<times> 'v literal multiset multiset
         \<Rightarrow> 'v literal list option \<times> 'v literal multiset multiset
            \<Rightarrow> bool\<close> where
  \<open>next_model M N \<Longrightarrow> P (set M) \<Longrightarrow> next_model_filtered (None, N) (Some M, N)\<close> |
  \<open>next_model M N \<Longrightarrow> \<not>P (set M) \<Longrightarrow> next_model_filtered (None, N) (None, add_mset (image_mset uminus (mset M)) N)\<close>

lemma next_model_filtered_mono:
  \<open>next_model_filtered a b \<Longrightarrow> snd a \<subseteq># snd b\<close>
  by (induction rule: next_model_filtered.induct) auto

lemma rtranclp_next_model_filtered_mono:
  \<open>next_model_filtered\<^sup>*\<^sup>* a b \<Longrightarrow> snd a \<subseteq># snd b\<close>
  by (induction rule: rtranclp_induct) (auto dest: next_model_filtered_mono)

lemma next_filtered_same_atoms:
  \<open>next_model_filtered a b \<Longrightarrow> atms_of_mm (snd b) = atms_of_mm (snd a)\<close>
  by (induction rule: next_model_filtered.induct) (auto simp: next_model.simps atms_of_def)

lemma rtranclp_next_filtered_same_atoms:
  \<open>next_model_filtered\<^sup>*\<^sup>* a b \<Longrightarrow> atms_of_mm (snd b) = atms_of_mm (snd a)\<close>
  by (induction rule: rtranclp_induct) (auto simp: next_filtered_same_atoms)

lemma next_model_filtered_next_modelD:
  \<open>next_model_filtered a b \<Longrightarrow> M \<in># snd b - snd a \<Longrightarrow> M = image_mset uminus (mset M') \<Longrightarrow>
   next_model M' (snd a)\<close>
  by (induction arbitrary: M M' rule: next_model_filtered.induct)
    (auto simp: next_model.simps distinct_mset_mset_distinct[symmetric]
      dest: mset_eq_setD
      simp del: distinct_mset_mset_distinct)

lemma rtranclp_next_model_filtered_next_modelD:
  \<open>next_model_filtered\<^sup>*\<^sup>* a b \<Longrightarrow> M \<in># snd b - snd a \<Longrightarrow> M = image_mset uminus (mset M') \<Longrightarrow>
   next_model M' (snd a)\<close>
proof (induction arbitrary: M M' rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z) note star = this(1) and step = this(2) and IH = this(3) and M_in = this(4) and
    M = this(5)
  consider
    \<open>M \<in># snd y - snd a\<close> |
    \<open>M \<in># snd z - snd y\<close>
    using step star M_in
    by (smt rtranclp_next_model_filtered_mono add_diff_cancel_right
        in_multiset_minus_notin_snd rtranclp.rtrancl_into_rtrancl subset_mset.diff_add)
  then show ?case
  proof cases
    case 1
    show ?thesis
      by (rule IH[OF 1 M])
  next
    case 2
    then show ?thesis
      using step rtranclp_next_model_filtered_mono[OF star] rtranclp_next_filtered_same_atoms[OF star]
      unfolding subset_mset.le_iff_add
      by (force simp: next_model_filtered.simps M next_model.simps
          distinct_mset_mset_distinct[symmetric]
          dest: mset_eq_setD
          simp del: distinct_mset_mset_distinct)
  qed
qed


lemma rtranclp_next_model_filtered_next_false:
  \<open>next_model_filtered\<^sup>*\<^sup>* a b \<Longrightarrow> M \<in># snd b - snd a \<Longrightarrow> M = image_mset uminus (mset M') \<Longrightarrow>
   \<not>P (uminus ` set_mset M)\<close>
proof (induction arbitrary: M M' rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z) note star = this(1) and step = this(2) and IH = this(3) and M_in = this(4) and
    M = this(5)
  consider
    \<open>M \<in># snd y - snd a\<close> |
    \<open>M \<in># snd z - snd y\<close>
    using step star M_in
    by (smt rtranclp_next_model_filtered_mono add_diff_cancel_right
        in_multiset_minus_notin_snd rtranclp.rtrancl_into_rtrancl subset_mset.diff_add)
  then show ?case
  proof cases
    case 1
    show ?thesis
      by (rule IH[OF 1 M])
  next
    case 2
    then show ?thesis
      using step rtranclp_next_model_filtered_mono[OF star] rtranclp_next_filtered_same_atoms[OF star]
      unfolding subset_mset.le_iff_add
      by (force simp: next_model_filtered.simps M next_model.simps
          distinct_mset_mset_distinct[symmetric] image_image
          dest: mset_eq_setD
          simp del: distinct_mset_mset_distinct)
  qed
qed

lemma next_model_decreasing:
  assumes
    \<open>next_model M N\<close>
  shows \<open>(add_mset (image_mset uminus (mset M)) N, N)
         \<in> measure (\<lambda>N. card (all_models N))\<close>
proof -
  have \<open>M \<in> all_models N\<close>
    using assms unfolding all_models_def
    by (auto simp: true_clss_def true_cls_mset_def next_model.simps)
  moreover {
    have \<open>\<not> set M \<Turnstile> image_mset uminus (mset M)\<close>
      using assms unfolding true_cls_def all_models_def
      by (auto simp: true_clss_def consistent_interp_def next_model.simps)
    then have \<open>M \<notin> all_models (add_mset (image_mset uminus (mset M)) N)\<close>
      unfolding all_models_def by (auto elim!: simp: true_clss_def)
  }
  moreover {
    have \<open>atm_of ` uminus ` set M \<union> atms_of_ms (set_mset N) = atms_of_ms (set_mset N)\<close>
      using assms unfolding true_cls_def all_models_def
      by (auto simp: true_clss_def consistent_interp_def atms_of_def next_model.simps)
    then have \<open>all_models (add_mset (image_mset uminus (mset M)) N) \<subseteq> all_models N\<close>
      using assms unfolding all_models_def
      by (auto simp: atms_of_def)
  }
  ultimately have \<open>all_models (add_mset (image_mset uminus (mset M)) N) \<subset> all_models N\<close>
    by auto
  then show ?thesis
    by (auto simp: finite_all_models psubset_card_mono)
qed

lemma next_model_decreasing':
  assumes
    \<open>next_model M N\<close>
  shows \<open>((P, add_mset (image_mset uminus (mset M)) N), P, N)
         \<in> measure (\<lambda>(P, N). card (all_models N))\<close>
  using next_model_decreasing[OF assms] by auto

lemma wf_next_model_filtered:
  \<open>wf {(y, x). next_model_filtered x y}\<close>
proof -
  have \<open>wf {(y, x). True \<and> next_model_filtered x y}\<close>
    by (rule wfP_if_measure[of \<open>\<lambda>_. True\<close> next_model_filtered
          \<open>\<lambda>N. (if fst N = None then 1 else 0) + card (all_models (snd N))\<close>])
      (auto dest: next_model_decreasing simp: next_model_filtered.simps)
  then show ?thesis
    unfolding wfP_def
    by simp
qed

lemma no_step_next_model_filtered_unsat:
  assumes \<open>no_step next_model_filtered (None, N)\<close>
  shows \<open>unsatisfiable (set_mset N)\<close>
  by (metis Ex_sat_model Model_Enumeration.next_model_filtered.simps
      assms next_model.intros)

lemma unsat_no_step_next_model_filtered:
  assumes \<open>unsatisfiable (set_mset N)\<close>
  shows \<open>no_step next_model_filtered (None, N)\<close>
  by (metis (no_types, lifting) next_model_filtered.simps assms
      next_model.cases satisfiable_carac' snd_conv)

lemma full_next_model_filtered_no_distinct_model:
  assumes
    no_model:  \<open>full next_model_filtered (None, N) (None, N')\<close> and
    filter_mono: \<open>\<And>M M'. set M \<Turnstile>sm N \<Longrightarrow> consistent_interp (set M) \<Longrightarrow> set M' \<Turnstile>sm N \<Longrightarrow>
      distinct M \<Longrightarrow> distinct M' \<Longrightarrow> set M \<subseteq> set M' \<Longrightarrow> P (set M) \<longleftrightarrow> P (set M')\<close>
  shows
    \<open>\<nexists>M. set M \<Turnstile>sm N \<and> P (set M) \<and> consistent_interp (set M) \<and> distinct M\<close>
proof clarify
  fix M
  assume
    M_N: \<open>set M \<Turnstile>m N\<close> and
    P_M: \<open>P (set M)\<close> and
    consistent: \<open>consistent_interp (set M)\<close> and
    dist_M: \<open>distinct M\<close>
  have st: \<open>next_model_filtered\<^sup>*\<^sup>* (None, N) (None, N')\<close> and
    ns: \<open>no_step next_model_filtered (None, N')\<close>
    using no_model unfolding full_def by blast+
  define Ms where \<open>Ms = N' - N\<close>
  then have N'[simp]: \<open>N' = N + Ms\<close>
    using rtranclp_next_model_filtered_mono[OF st] by auto
  have \<open>unsatisfiable (set_mset N')\<close>
    using ns by (rule no_step_next_model_filtered_unsat)
  then have \<open>\<not>set M \<Turnstile>m Ms\<close>
    using consistent M_N by (auto simp: satisfiable_carac[symmetric])
  then obtain M' where
    M'_MS: \<open>M' \<in># Ms\<close> and
    M_M': \<open>\<not>set M \<Turnstile> M'\<close>
    by (auto simp: true_cls_mset_def)
  obtain M'' where
    [simp]: \<open>M' = mset M''\<close>
    using ex_mset[of M'] by auto
  let ?M'' = \<open>map uminus M''\<close>
  have \<open>next_model ?M'' (snd (None :: 'v literal list option, N))\<close>
    apply (rule rtranclp_next_model_filtered_next_modelD[OF st, of M'])
    using M'_MS by auto
  then have
    cons': \<open>consistent_interp (set ?M'')\<close> and
    M''_N: \<open>set ?M'' \<Turnstile>sm N\<close> and
    dist_M'': \<open>distinct ?M''\<close>
    unfolding next_model.simps by auto

  let ?I = \<open>remdups (M @ ?M'')\<close>
  have cons_I: \<open>consistent_interp (set ?I)\<close>
    using M_M' consistent cons' by (auto simp: consistent_interp_def true_cls_def)

  have \<open>P (set ?I)\<close>
    using filter_mono[of M \<open>?I\<close>] cons' M''_N M_N consistent dist_M'' dist_M P_M
    by auto
  then have \<open>P (uminus ` (set M''))\<close>
    using filter_mono[of \<open>?M''\<close> ?I] cons' M''_N M_N consistent dist_M'' dist_M P_M cons_I
    by auto
  then show False
    using rtranclp_next_model_filtered_next_false[OF st, of M' ?M''] M'_MS by auto
qed


lemma full_next_model_filtered_no_model:
  assumes
    no_model:  \<open>full next_model_filtered (None, N) (None, N')\<close> and
    filter_mono: \<open>\<And>M M'. set M \<Turnstile>sm N \<Longrightarrow> consistent_interp (set M) \<Longrightarrow> set M' \<Turnstile>sm N \<Longrightarrow>
      distinct M \<Longrightarrow> distinct M' \<Longrightarrow> set M \<subseteq> set M' \<Longrightarrow> P (set M) \<longleftrightarrow> P (set M')\<close>
  shows
    \<open>\<nexists>M. set M \<Turnstile>sm N \<and> P (set M) \<and> consistent_interp (set M)\<close>
    (is \<open>\<nexists>M. ?P M\<close>)
proof -
  have H: \<open>(\<exists>M. ?P M) \<longleftrightarrow> (\<exists>M. set M \<Turnstile>sm N \<and> P (set M) \<and> consistent_interp (set M) \<and> distinct M)\<close>
    by (auto intro: exI[of _ \<open>remdups _\<close>])
  show ?thesis
    apply (subst H)
    apply (rule full_next_model_filtered_no_distinct_model)
     apply (rule no_model)
    apply (rule filter_mono; assumption)
    done
qed

end

lemma no_step_next_model_filtered_next_model_iff:
  \<open>fst S = None \<Longrightarrow> no_step (next_model_filtered P) S \<longleftrightarrow> (\<nexists>M. next_model M (snd S))\<close>
  apply (cases S; auto simp: next_model_filtered.simps)
  by metis

lemma Ex_next_model_iff_statisfiable:
  \<open>(\<exists>M. next_model M N) \<longleftrightarrow> satisfiable (set_mset N)\<close>
  by (metis no_step_next_model_filtered_next_model_iff
      next_model.cases no_step_next_model_filtered_unsat prod.sel(1) prod.sel(2) satisfiable_carac')

lemma unsat_no_step_next_model_filtered':
  assumes \<open>unsatisfiable (set_mset (snd S)) \<or> fst S \<noteq> None\<close>
  shows \<open>no_step (next_model_filtered P) S\<close>
  using assms
  apply cases
  apply (auto dest: unsat_no_step_next_model_filtered)
   apply (metis Ex_next_model_iff_statisfiable fst_conv next_model_filtered.simps
      no_step_next_model_filtered_next_model_iff)
  by (metis Pair_inject next_model_filtered.cases option.simps(3) prod.collapse)

end
