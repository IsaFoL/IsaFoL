theory CDCL_Model_Enumeration
imports Entailment_Definition.Partial_Annotated_Herbrand_Interpretation Weidenbach_Book_Base.Explorer
begin


definition option_model where
  \<open>option_model N M \<longleftrightarrow>
         (M \<noteq> None \<longrightarrow>
           set (the M) \<Turnstile>sm N \<and>
           distinct (the M) \<and>
           consistent_interp (set (the M)) \<and>
           atm_of ` set (the M) \<subseteq> atms_of_mm N) \<and>
         (M = None \<longrightarrow> unsatisfiable (set_mset N))\<close>

abbreviation get_option_model where
  \<open>get_option_model N \<equiv> Eps (option_model N)\<close>


lemma Ex_option_model:
   \<open>\<exists>M. option_model N M\<close>
proof (cases \<open>satisfiable (set_mset N)\<close>)
  case False
  then show ?thesis by (auto simp: option_model_def)
next
  case True
  then obtain I where
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
    apply (rule exI[of _ \<open>Some I'\<close>])
    using I_N dist consistent atms_I_N by (auto simp: option_model_def I')
qed


lemma get_model_SomeE:
  assumes
    mod: \<open>Some M = get_option_model N\<close> and
    H: \<open>set M \<Turnstile>sm N  \<Longrightarrow> consistent_interp (set M) \<Longrightarrow>  distinct M \<Longrightarrow>
           consistent_interp (set M)  \<Longrightarrow> atm_of ` set M \<subseteq> atms_of_mm N \<Longrightarrow> P M\<close>
  shows \<open>P M\<close>
  apply (rule H)
  using mod by (metis Ex_option_model mod option.distinct(1) option.sel option_model_def someI)+

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

lemma enumerate_model_while_decreasing:
  assumes
    \<open>SM = get_option_model (image_mset mset (mset N))\<close> and
    [simp]: \<open>SM = Some M\<close>
  shows \<open>((P, N @ [map uminus M]), P, N)
         \<in> measure (\<lambda>(P, N). card (all_models (image_mset mset (mset N))))\<close>
proof -
  have \<open>M \<in> all_models (image_mset mset (mset N))\<close>
    using assms unfolding all_models_def by (auto elim!: get_model_SomeE simp: true_clss_def)
  moreover {
    have \<open>\<not> set M \<Turnstile> image_mset uminus (mset M)\<close>
      using assms unfolding true_cls_def all_models_def
      by (auto elim!: get_model_SomeE simp: true_clss_def consistent_interp_def)
    then have \<open>M \<notin> all_models (add_mset (image_mset uminus (mset M)) (image_mset mset (mset N)))\<close>
      unfolding all_models_def by (auto elim!: simp: true_clss_def)
  }
  moreover {
    have \<open>atm_of ` uminus ` set M \<union> atms_of_ms (mset ` set N) = atms_of_ms (mset ` set N)\<close>
      using assms unfolding true_cls_def all_models_def
      by (auto elim!: get_model_SomeE simp: true_clss_def consistent_interp_def atms_of_def)
    then have \<open>all_models (add_mset (image_mset uminus (mset M)) (image_mset mset (mset N)))
       \<subseteq> all_models (image_mset mset (mset N))\<close>
      using assms unfolding all_models_def
      by (auto elim!: get_model_SomeE simp: atms_of_def)
  }
  ultimately have \<open>all_models (add_mset (image_mset uminus (mset M)) (image_mset mset (mset N)))
       \<subset> all_models (image_mset mset (mset N))\<close>
    by auto
  then show ?thesis
    by (auto simp: finite_all_models psubset_card_mono)
qed


function enumerate_model_while where
  \<open>enumerate_model_while P N =
     (let M = get_option_model (image_mset mset (mset N)) in
      case M of
        None \<Rightarrow> None
      | Some M \<Rightarrow>
        if P M
        then enumerate_model_while P (N @ [map uminus M])
        else Some M)\<close>
  by pat_completeness auto

termination enumerate_model_while
  apply (relation \<open>measure (\<lambda>(P, N). card (all_models (image_mset mset (mset N))))\<close>)
  subgoal by auto
  subgoal by (rule enumerate_model_while_decreasing)
  done

end
