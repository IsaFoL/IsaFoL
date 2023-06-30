theory autarky
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    modelReconstruction
    inprocessingRulesNeu2
    simulation2
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

(*Das Lemma geht wenn unit_clauses_of_model \<omega> dabei ist. Aber wenn es weggellassen wird, dann geht es glaube ich nicht.*)
lemma autarky_redundancy3:  
  assumes "autarky \<omega> N (Na + {#x#} + unit_clauses_of_model \<omega>)" and "consistent_interp \<omega>" and  "finite \<omega> "
  shows "redundancy (N + Na + unit_clauses_of_model \<omega> ) x (\<omega> \<inter> set_mset x) (N + Na + unit_clauses_of_model \<omega>)"
  using assms 
proof-
  have 1: "( \<omega> \<Turnstile>m Na + {#x#} + unit_clauses_of_model \<omega>) \<and> (\<forall>C \<in># N.  \<not> \<omega> \<Turnstile> C \<and> \<not> \<omega> \<Turnstile> mset_set(uminus ` set_mset C))"
    using autarky_cons assms(1, 2) by auto
  hence 2:"\<forall>C \<in># N. (set_mset C \<inter>  \<omega> = {})" and 3:"\<forall>C \<in># N. (uminus `(set_mset C) \<inter>  \<omega> = {})" apply auto
    apply (metis insert_DiffM true_cls_add_mset)
    by (metis elem_mset_set finite_imageI finite_set_mset imageI multi_member_split true_cls_add_mset)
  have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile>m (N + Na + unit_clauses_of_model \<omega>)" if A:"consistent_interp I " 
and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m (N + Na + unit_clauses_of_model \<omega>)" for I
  proof-
   have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile> C" if C: "C \<in># N" for C
   proof-
     have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
       using C B apply auto
       using true_cls_mset_def by blast
     hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
       by (meson disjoint_iff true_cls_def true_lit_def)
     have "(set_mset C \<inter>  \<omega> = {}) " and  "(uminus `(set_mset C) \<inter>  \<omega> = {})" 
       using C 2 apply auto using C 3 apply auto
       by (metis IntI empty_iff image_eqI)
     hence "(set_mset C \<inter> (\<omega> \<inter> set_mset x) = {}) " and  "(uminus `(set_mset C) \<inter> (\<omega> \<inter> set_mset x) = {})" 
       by auto
     hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}"
       using notempty  unfolding interpr_composition_def by auto
     then show ?thesis
       by (meson disjoint_iff true_cls_def true_lit_def)
   qed note N_sat = this
   have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile> C" if C: "C \<in>#  unit_clauses_of_model \<omega>" for C
   proof-
     have 1:"interpr_composition I (uminus ` set_mset x) \<Turnstile> C" using B C apply auto
       using true_cls_mset_def by blast
     hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
       by (meson disjoint_iff true_cls_def true_lit_def)
     show ?thesis
     proof(cases "(\<omega> \<inter> set_mset x) \<inter> (set_mset C) \<noteq> {}")
       case True
       hence "\<exists>L. L \<in> (\<omega> \<inter> set_mset x) \<and> L \<in># C" 
         by auto
       then obtain L where L1:"L \<in> (\<omega> \<inter> set_mset x)" and L2: "L \<in># C" by blast
       hence "L \<in> interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))"
         unfolding interpr_composition_def by auto
       then show ?thesis using L2 unfolding interpr_composition_def
         by (meson true_cls_def true_lit_def)
     next
       case False
       have "(uminus `(set_mset C) \<inter> (\<omega> \<inter> set_mset x) = {})" using C unfolding unit_clauses_of_model_def apply auto
         by (metis assms(2) consistent_interp_def empty_iff in_unit_clauses_of_model_iff mset_set.infinite set_mset_empty that)
       hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}"
       using notempty False unfolding interpr_composition_def by auto
     then show ?thesis
       by (meson disjoint_iff true_cls_def true_lit_def)
     qed
   qed note omega_sat = this
   hence "I \<^bold>\<circ> (uminus ` set_mset x \<^bold>\<circ> (\<omega> \<inter> set_mset x)) \<Turnstile>m unit_clauses_of_model \<omega> " 
     unfolding interpr_composition_def unit_clauses_of_model_def by auto
   hence "\<forall>D \<in># unit_clauses_of_model \<omega>. set_mset D \<subseteq> I \<^bold>\<circ> (uminus ` set_mset x \<^bold>\<circ> (\<omega> \<inter> set_mset x)) "
     unfolding interpr_composition_def unit_clauses_of_model_def by auto
   hence "\<omega> \<subseteq> I \<^bold>\<circ> (uminus ` set_mset x \<^bold>\<circ> (\<omega> \<inter> set_mset x))" 
     using assms(3) unfolding interpr_composition_def unit_clauses_of_model_def by auto
   hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile>m Na" using 1  unfolding interpr_composition_def apply auto
     by (meson true_clss_mono_left true_clss_set_mset)
   then show ?thesis
     using N_sat omega_sat unfolding interpr_composition_def 
     apply auto using true_cls_mset_def apply blast
      using true_cls_mset_def by blast
  qed 
  then show ?thesis
    using redundancy_def by blast
qed


(*So wie das Lemma jetzt ist gibt es glaube ich ein Gegenbeispiel: 
C\<in> Na, \<omega> \<Turnstile>m Na, \<omega> \<Turnstile> x, C = (L \<or> A)  (\<omega> \<inter> set_mset x) = {-L}, interpr_composition I (uminus ` set_mset x) = {L}, x = (-L), \<omega> = {-L, A}
Geht das wenn ich die unit clauses von omega hinzufüge? *)
lemma autarky_redundancy:  
  assumes "autarky \<omega> N (Na + {#x#})" and "consistent_interp \<omega>"
  shows "redundancy (N + Na) x (\<omega> \<inter> set_mset x) (N + Na)"
  using assms 
proof-
  have 1: "( \<omega> \<Turnstile>m Na + {#x#}) \<and> (\<forall>C \<in># N.  \<not> \<omega> \<Turnstile> C \<and> \<not> \<omega> \<Turnstile> mset_set(uminus ` set_mset C))"
    using autarky_cons assms(1, 2) by auto
  hence 2:"\<forall>C \<in># N. (set_mset C \<inter>  \<omega> = {})" and 3:"\<forall>C \<in># N. (uminus `(set_mset C) \<inter>  \<omega> = {})" apply auto
    apply (metis insert_DiffM true_cls_add_mset)
    by (metis elem_mset_set finite_imageI finite_set_mset imageI multi_member_split true_cls_add_mset)
  have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile>m (N + Na)" if A:"consistent_interp I " 
and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m (N + Na)" for I
  proof-
   have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile> C" if C: "C \<in># N" for C
   proof-
     have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
       using C B apply auto
       using true_cls_mset_def by blast
     hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
       by (meson disjoint_iff true_cls_def true_lit_def)
     have "(set_mset C \<inter>  \<omega> = {}) " and  "(uminus `(set_mset C) \<inter>  \<omega> = {})" 
       using C 2 apply auto using C 3 apply auto
       by (metis IntI empty_iff image_eqI)
     hence "(set_mset C \<inter> (\<omega> \<inter> set_mset x) = {}) " and  "(uminus `(set_mset C) \<inter> (\<omega> \<inter> set_mset x) = {})" 
       by auto
     hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}"
       using notempty  unfolding interpr_composition_def by auto
     then show ?thesis
       by (meson disjoint_iff true_cls_def true_lit_def)
   qed note N_sat = this
  have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile> C" if C: "C \<in># Na" for C
  proof-
    have C1: "\<omega> \<Turnstile> C" using 1 C apply auto
      using true_cls_mset_def by blast
    have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
       using C B apply auto
       using true_cls_mset_def by blast
    hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
      by (meson disjoint_iff true_cls_def true_lit_def)
    have notem1:"(set_mset C \<inter>  \<omega> \<noteq> {}) " using C 1 apply auto
      by (metis disjoint_iff true_cls_def true_cls_mset_def true_lit_def)
    show ?thesis
      proof(cases "(set_mset C \<inter> (\<omega> \<inter> set_mset x) = {})")
        case True note empty = this
        show ?thesis 
        proof(cases "(uminus `(set_mset C) \<inter> (\<omega> \<inter> set_mset x) = {})")
          case True
          hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}" 
            using empty notempty unfolding interpr_composition_def by auto
          then show ?thesis 
            by (meson disjoint_iff true_cls_def true_lit_def)
        next
          case False note f = this
          hence "(\<omega> \<inter> set_mset x) \<noteq> (uminus `(set_mset C))" using C1
            by (metis Int_emptyI Int_iff assms(2) consistent_interp_def imageI notem1)
          hence "\<exists>L. L \<in> (uminus `(set_mset C)) \<and> L \<notin> (\<omega> \<inter> set_mset x)" apply auto
            by (meson C1 assms(2) consistent_CNot_not true_clss_def_iff_negation_in_model)
          then obtain L where L1: "L \<in> (uminus `(set_mset C))" and L2: "L \<notin> (\<omega> \<inter> set_mset x)"
            by blast
          hence "-L \<in># C \<and> -L \<notin> (\<omega> \<inter> set_mset x)" using empty
            by (simp add: disjoint_iff in_image_uminus_uminus)
          hence "-L \<in> interpr_composition I (uminus ` set_mset x)" using L2 unfolding interpr_composition_def apply auto sorry
          then show ?thesis sorry
        qed
      next
        case False
        hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}"
          unfolding interpr_composition_def by auto
        then show ?thesis
          by (meson disjoint_iff true_cls_def true_lit_def)
      qed
  qed note Na_sat = this
    then show ?thesis using N_sat unfolding interpr_composition_def apply auto
      using true_cls_mset_def apply blast
      using true_cls_mset_def by blast
  qed 
  then show ?thesis
    using redundancy_def by blast
qed

(*Das Lemma geht aber wenn bei redundancy das Na weggelassen wird.*)
lemma autarky_redundancy2:  
  assumes "autarky \<omega> N (Na + {#x#})" and "consistent_interp \<omega>"
  shows "redundancy (N ) x (\<omega> \<inter> set_mset x) (N )"
  using assms 
proof-
  have 1: "( \<omega> \<Turnstile>m Na + {#x#}) \<and> (\<forall>C \<in># N.  \<not> \<omega> \<Turnstile> C \<and> \<not> \<omega> \<Turnstile> mset_set(uminus ` set_mset C))"
    using autarky_cons assms(1, 2) by auto
  hence 2:"\<forall>C \<in># N. (set_mset C \<inter>  \<omega> = {})" and 3:"\<forall>C \<in># N. (uminus `(set_mset C) \<inter>  \<omega> = {})" apply auto
    apply (metis insert_DiffM true_cls_add_mset)
    by (metis elem_mset_set finite_imageI finite_set_mset imageI multi_member_split true_cls_add_mset)
  have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile>m (N )" if A:"consistent_interp I " 
and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m (N )" for I
  proof-
   have "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x)) \<Turnstile> C" if C: "C \<in># N" for C
   proof-
     have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
       using C B apply auto
       using true_cls_mset_def by blast
     hence notempty:"interpr_composition I (uminus ` set_mset x) \<inter> (set_mset C) \<noteq> {}" apply auto
       by (meson disjoint_iff true_cls_def true_lit_def)
     have "(set_mset C \<inter>  \<omega> = {}) " and  "(uminus `(set_mset C) \<inter>  \<omega> = {})" 
       using C 2 apply auto using C 3 apply auto
       by (metis IntI empty_iff image_eqI)
     hence "(set_mset C \<inter> (\<omega> \<inter> set_mset x) = {}) " and  "(uminus `(set_mset C) \<inter> (\<omega> \<inter> set_mset x) = {})" 
       by auto
     hence "interpr_composition I (interpr_composition (uminus ` set_mset x) (\<omega> \<inter> set_mset x))\<inter> (set_mset C) \<noteq> {}"
       using notempty  unfolding interpr_composition_def by auto
     then show ?thesis
       by (meson disjoint_iff true_cls_def true_lit_def)
   qed note N_sat = this
   then show ?thesis 
     using N_sat unfolding interpr_composition_def apply auto
      using true_cls_mset_def by blast
  qed 
  then show ?thesis
    using redundancy_def by blast
qed


(*Geht das hier überhaupt? Oder muss man ein I' \<subseteq> I nehmen, wo alle L \<in> I' auch in Na vorkommen? Aber dann müsste man das Lemma mit Redundancy auch ändern.*)
lemma learn_autarky:
  assumes "autarky I N Na" and "consistent_interp I" and "C \<in># unit_clauses_of_model I" and "finite I"
  shows "rules (N+Na, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (N+Na, ({#C#}+R), S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
  using assms
proof -
  have "((I \<Turnstile>m Na) \<and> (\<forall>C \<in># N.  \<not>I \<Turnstile> C \<and> \<not>I \<Turnstile> mset_set(uminus ` set_mset C)))" 
    using autarky_cons assms(1, 2) by auto
  hence "(I \<Turnstile>m Na)" by auto
  hence "(set_mset (Na)) \<Turnstile>p C" using assms(3) unfolding true_clss_cls_def unit_clauses_of_model_def apply auto  sorry
  show ?thesis sorry
qed

lemma autarky_simulation: 
  assumes "autarky I N Na" and "consistent_interp I"
  obtains  S' where "rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N, R, S@S', V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
and "wit_clause `# mset S' = Na" and "\<forall>I'\<in># (wit_interp `# mset S'). I' \<subseteq> I"
  using assms
proof(induction Na)
  case empty
  then show ?case by auto
next
(*Muss hier zuerst Na auf den Stack gemacht werden oder zuerst x? Weil bei beiden kann ich nicht zeigen dass rules\<^sup>*\<^sup>*((N + Na) + {#x#}...(N+ {#x#} )... bzw. rules\<^sup>*\<^sup>*((N + Na)...(N)*)
  case (add x Na) note A1 = this(1) and A2 = this(2) and aut = this(3) and cons = this(4)
  have "autarky I N Na" 
    using aut unfolding autarky_def by auto
 (*then obtain S' where ruls:"rules\<^sup>*\<^sup>*(N + Na, R, S, V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N, R, S@S',  V \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" and "wit_clause `# mset S' = Na" and "\<forall>I'\<in># (wit_interp `# mset S'). I' \<subseteq> I"
    using A1 cons apply auto sorry *)
  obtain  S'  where "rules\<^sup>*\<^sup>*((N + Na) + {#x#}, R, S, V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
(N + {#x#}, R, S@S',V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
 and "wit_clause `# mset S' = Na" and "\<forall>I'\<in># (wit_interp `# mset S'). I' \<subseteq> I" using A1 apply auto sorry
  have  "I \<Turnstile> x"
    using aut cons unfolding autarky_def by auto
  hence 1:" (I \<inter> set_mset x) \<Turnstile> x"
    by (simp add: true_cls_def) 
  hence 2: "atm_of ` (I \<inter> set_mset x) \<subseteq> atms_of x" apply auto
    using atm_of_lit_in_atms_of by blast
  have cons2:"consistent_interp (I \<inter> set_mset x)" using cons
    using consistent_interp_subset inf_le1 by blast 
  have red1: "redundancy (N) x (I \<inter> set_mset x) (N)" using autarky_redundancy2[of I N Na x] cons aut by auto
have "rules((N + {#x#}, R, S@S', V \<union> atms_of x \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set (S@S'))))
(N, R,S@S'@ [Witness (I \<inter> set_mset x) x], V \<union> atms_of x \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set (S@S')) )" using weakenp[of "(I \<inter> set_mset x)" x N R "S@S'" V] using 1 2 cons2 red1 apply auto
  by (simp add: image_Un)


(*Hier geht das mit der Redundancy nicht, vielleicht wenn es N + Na + I ist? aber ich weiß auch nicht wie man die einzelnen Literale von I als Klauses hinzufügen kann, weil dann braucht man die Regel learn_minus und es muss 
sein dass N + R \<Turnstile>p I. Also wäre es besser wenn man erst Na auf den Stack hinzufügen könnte...*)
  have red:"redundancy (N + Na) x (I \<inter> set_mset x) (N + Na)" unfolding redundancy_def sorry
  have "rules((N + Na) + {#x#}, R, S, V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
(N + Na, R, S @ [Witness (I \<inter> set_mset x) x], V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    using weakenp[of "(I \<inter> set_mset x)" x "N + Na" R S V] using red 1 2 cons2 by auto
  have "rules\<^sup>*\<^sup>*(N + Na, R, S @ [Witness (I \<inter> set_mset x) x], V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N, R, S@ [Witness (I \<inter> set_mset x) x]@S',
 V \<union> atms_of x \<union> atms_of_mm (N + Na) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set (S@ [Witness (I \<inter> set_mset x) x]@S')))"  apply auto sorry
  then show ?case sorry
qed


end
