theory Autarky
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    Model_Reconstruction
    Inprocessing_Rules
    Simulation
begin

definition autarky :: "'a literal set \<Rightarrow>'a clauses \<Rightarrow> 'a clauses \<Rightarrow> bool " where
  "autarky I F Fa = (consistent_interp I \<longrightarrow> ((I \<Turnstile>m Fa) \<and> (\<forall>C \<in># F.  \<not>I \<Turnstile> C \<and> \<not>I \<Turnstile> mset_set(uminus ` set_mset C))))"

lemma autarky_cons:
  assumes "autarky I F Fa" and "consistent_interp I"
  shows "(I \<Turnstile>m Fa) \<and> (\<forall>C \<in># F.  \<not>I \<Turnstile> C \<and> \<not>I \<Turnstile> mset_set(uminus ` set_mset C))"
  using assms unfolding autarky_def by auto

lemma compose_model_after_autarky:
  assumes "I \<Turnstile>m N" "consistent_interp I" "autarky J N Na" "consistent_interp J"
  shows "interpr_composition I J  \<Turnstile>m (N+Na)"
  using assms 
proof-
  have 1: "(J \<Turnstile>m Na) \<and> (\<forall>C \<in># N.  \<not>J \<Turnstile> C \<and> \<not>J \<Turnstile> mset_set(uminus ` set_mset C))"
    using autarky_cons assms(3, 4) by auto
  hence "\<forall>C \<in># N.  \<not>J \<Turnstile> C \<and> \<not>J \<Turnstile> mset_set(uminus ` set_mset C)"
    by auto
  hence 2:"\<forall>C \<in># N. (set_mset C \<inter> J = {})" and 3:"\<forall>C \<in># N. (uminus `(set_mset C) \<inter> J = {})"
    apply auto
    apply (metis insert_DiffM true_cls_add_mset)
    by (metis elem_mset_set finite_imageI finite_set_mset imageI multi_member_split true_cls_add_mset)
  have "interpr_composition I J \<Turnstile> C" if C: "C \<in># N" for C
  proof-
    have C1:"(set_mset C \<inter> J = {})" and C2:"(uminus `(set_mset C) \<inter> J = {})" 
      using  C 2 3 by auto
    have "I \<Turnstile> C"
      using C assms(1)
      using true_cls_mset_def by blast
    hence "\<exists>L. L \<in> I \<and> L \<in># C"
      using true_cls_def by auto
    then obtain L where L1:"L \<in> I" and L2:" L \<in># C" 
      by blast
    have "L \<notin> J \<and> -L \<notin> J" 
      using C1 C2 L2
      by blast
    hence "L \<in> interpr_composition I J" 
      using L1 unfolding interpr_composition_def by auto
    then show ?thesis using L2  unfolding interpr_composition_def
      by (meson true_cls_def true_lit_def) 
  qed
  hence N:"interpr_composition I J  \<Turnstile>m N" 
    unfolding interpr_composition_def
    using true_cls_mset_def by blast
  have "interpr_composition I J  \<Turnstile>m Na" 
    using 1 unfolding interpr_composition_def apply auto
    by (simp add: Un_commute)
  then show ?thesis 
    using N by auto
qed

definition unit_clauses_of_model :: \<open>'a partial_interp \<Rightarrow> 'a clauses\<close> where
  \<open>unit_clauses_of_model I = (\<lambda>L. {#L#}) `# mset_set I\<close>

lemma in_unit_clauses_of_model_iff[iff]:
  assumes \<open>finite I\<close>
  shows \<open>{#L#} \<in># unit_clauses_of_model I \<longleftrightarrow> L \<in> I\<close>
  using assms by (auto simp: unit_clauses_of_model_def)


lemma in_unit_clauses_of_modelE:
  assumes \<open>finite I\<close> and \<open>C \<in># unit_clauses_of_model I\<close>
  shows \<open>(\<And>L. C = {#L#} \<and> L \<in> I \<Longrightarrow> P) \<Longrightarrow> P\<close>
  using assms by (auto simp: unit_clauses_of_model_def)



lemma autarky_redundancy:  
  assumes "autarky \<omega> N (Na + {#x#})" and "consistent_interp \<omega>"
  shows "redundancy (N + Na) x \<omega> (N + Na)"
  using assms 
proof-
  have 1: "( \<omega> \<Turnstile>m Na + {#x#}) \<and> (\<forall>C \<in># N.  \<not> \<omega> \<Turnstile> C \<and> \<not> \<omega> \<Turnstile> mset_set(uminus ` set_mset C))"
    using autarky_cons assms(1, 2) by auto
  hence 2:"\<forall>C \<in># N. (set_mset C \<inter>  \<omega> = {})" and 3:"\<forall>C \<in># N. (uminus `(set_mset C) \<inter>  \<omega> = {})" apply auto
    apply (metis insert_DiffM true_cls_add_mset)
    by (metis elem_mset_set finite_imageI finite_set_mset imageI multi_member_split true_cls_add_mset)
  have "interpr_composition I (interpr_composition (uminus ` set_mset x) \<omega> ) \<Turnstile>m (N + Na)" if A:"consistent_interp I " 
    and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m (N + Na)" for I
  proof-
    have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega>)) \<Turnstile> C" if C: "C \<in># N" for C
    proof-
      have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
        using C B apply auto
        using true_cls_mset_def by blast
      hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
        by (meson disjoint_iff true_cls_def true_lit_def)
      have "(set_mset C \<inter>  \<omega> = {}) " and  "(uminus `(set_mset C) \<inter>  \<omega> = {})" 
        using C 2 apply auto using C 3 apply auto
        by (metis IntI empty_iff image_eqI)
      hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega>))\<inter> (set_mset C) \<noteq> {}"
        using notempty  unfolding interpr_composition_def by auto
      then show ?thesis
        by (meson disjoint_iff true_cls_def true_lit_def)
    qed note N_sat = this
    have "interpr_composition I (interpr_composition (uminus ` set_mset x) \<omega>) \<Turnstile> C" if C: "C \<in># Na" for C
    proof-
      have C1: "\<omega> \<Turnstile> C" using 1 C apply auto
        using true_cls_mset_def by blast
      hence "\<exists>L. L \<in> \<omega> \<and> L \<in># C"
        using true_cls_def by auto
      then obtain L where L1: "L \<in> \<omega> " and L2: "L \<in># C" 
        by blast
      hence "L \<in> interpr_composition I (interpr_composition (uminus ` set_mset x) \<omega>)" 
        unfolding interpr_composition_def by auto
      then show ?thesis unfolding interpr_composition_def
        by (simp add: C1)
    qed note Na_sat = this
    then show ?thesis using N_sat unfolding interpr_composition_def apply auto
      using true_cls_mset_def apply blast
      using true_cls_mset_def by blast
  qed 
  then show ?thesis
    using redundancy_def by blast
qed



lemma autarky_simulation2: 
  assumes "autarky I N Na" and "consistent_interp I" and " atm_of ` I \<subseteq>  atms_of_mm (Na)"
  shows "\<exists>S'. rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
          (N, R, S@S', V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) \<and>
           wit_clause `# mset S' = Na \<and> (\<forall>I'\<in># (wit_interp `# mset S'). I' = I)"
  using assms
proof - 
  obtain LNa where [simp]: \<open>mset LNa = Na\<close> 
    by (metis list_of_mset_exi)
  have "I \<Turnstile>m Na" 
    using assms(1, 2) unfolding autarky_def by auto
  hence LNa_sat:"I \<Turnstile>m mset LNa"
    by simp
  have "rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
(N + mset(drop i LNa), R, S@map (\<lambda>C. Witness I C) (take i LNa), V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
    for i
  proof (induction i)
    case 0
    then show ?case by auto
  next
    case (Suc i) note rul1 = this
    consider 
      (1) \<open>Suc i \<le> length LNa\<close> |
      (boring) \<open>Suc i>length LNa\<close>
      by linarith
    then show ?case
    proof cases
      case boring
      then have \<open>take ( i)LNa = LNa\<close> \<open>mset (drop (Suc i) LNa) = {#}\<close>
        by simp_all
      then show ?thesis
        using Suc by (auto simp:  ac_simps)
    next
      case 1
      have [simp]: \<open>mset (drop i LNa) = add_mset (LNa!i) (mset (drop (Suc i) LNa))\<close>
        by (metis "1" Cons_nth_drop_Suc Suc_le_lessD mset.simps(2))
      have h1:"mset (drop (Suc i) LNa) =  (remove1_mset (LNa ! i)  (mset (drop i LNa))) "
        by simp
      have Ii_sat:"I \<Turnstile> LNa ! i" using LNa_sat
        by (meson "1" Suc_le_eq nth_mem_mset true_cls_mset_def)
      have aut:"autarky I N (mset (drop (Suc i) LNa) + {#LNa ! i#})"
        using assms(1, 2)Ii_sat unfolding autarky_def apply auto
        by (metis \<open>mset LNa = Na\<close> set_drop_subset set_mset_mset true_cls_mset_mono)
      have red: "redundancy (mset (drop (Suc i) LNa) + N) (LNa ! i) I (mset (drop (Suc i) LNa) + N)" 
        using autarky_redundancy[of I N "(mset (drop (Suc i) LNa))" "LNa ! i"] using aut assms(2) apply auto
        by (simp add: add.commute)
      have Na1:"({#LNa ! i#} + (mset (drop (Suc i) LNa)) + (mset((take i LNa)))) = Na"
        by (metis \<open>mset (drop i LNa) = add_mset (LNa ! i) (mset (drop (Suc i) LNa))\<close> \<open>mset LNa = Na\<close> add_mset atd_lem union_code union_commute)
      hence sub: "atm_of ` I \<subseteq> V \<union> atms_of (LNa ! i) \<union> atms_of_mm (mset (drop (Suc i) LNa) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness I) (take i LNa)))"
        using assms(3) by auto
      have rul2: "rules (mset (drop (Suc i) LNa) + N + {#LNa ! i#}, R, S @ map (Witness I) (take i LNa),
 V \<union> atms_of (LNa ! i) \<union> atms_of_mm (mset (drop (Suc i) LNa) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness I) (take i LNa))))
   (mset (drop (Suc i) LNa) + N, R, (S @ map (Witness I) (take i LNa)) @ [Witness I (LNa ! i)], 
V \<union> atms_of (LNa ! i) \<union> atms_of_mm (mset (drop (Suc i) LNa) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness I) (take i LNa))))"
        using weakenp[of I "(LNa ! i)" " (mset (drop (Suc i) LNa))+ N" V R "S @ map (Witness I) (take i LNa)"]  using Ii_sat red sub assms(2) by auto
      have h2: "(V \<union> atms_of (LNa ! i) \<union> atms_of_mm (mset (drop (Suc i) LNa) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness I) (take i LNa))) 
               = (V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)))" using Na1 by auto
      have h3: "map (Witness I) (take i LNa) @ [Witness I (LNa ! i)] = map (Witness I) (take (Suc i) LNa)"
        by (simp add: "1" Suc_le_lessD take_Suc_conv_app_nth)
      have rul3:"rules (N + mset (drop i LNa), R, S @ map (Witness I) (take i LNa), V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
                  (N + mset (drop (Suc i) LNa), R, S @ map (Witness I) (take (Suc i) LNa), V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
        using h1 h2 h3 rul2 apply auto
        by (simp add: add.commute)
      then show ?thesis 
        using rul1 by auto
    qed
  qed note ag = this
  have "mset (drop (length LNa) LNa) = {#}" and "(take (length LNa) LNa) = LNa"
    by auto
  then have 2: "rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
                       (N, R, S@map (\<lambda>C. Witness I C) LNa, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    using ag[of "length LNa" ] by auto
  have wit_Na:"wit_clause `# mset (map (\<lambda>C. Witness I C) LNa) = Na" 
    by simp
  have int_Na:"(\<forall>I'\<in># (wit_interp `# mset (map (\<lambda>C. Witness I C) LNa)). I' = I)" 
    by auto
  then show ?thesis 
    using 2 wit_Na by blast
qed

end
