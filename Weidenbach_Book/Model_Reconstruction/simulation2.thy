theory simulation2
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    modelReconstruction
    inprocessingRulesNeu2
begin

lemma sat_N_then_sat_res: 
  assumes "res_stack (N, Z) (N', Z')" and "I \<Turnstile>m N" and "consistent_interp I" and "total_over_m I (set_mset N)" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "I \<Turnstile>m N'"
  using assms apply(induction rule: res_stack_induct) by auto

lemma atm_sub_N:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "atms_of_mm N' \<subseteq> atms_of_mm N"
  using assms
proof(induction rule: res_stack_induct)
  case (1 L N T S)note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have "res_stack (N, Z) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, Z @ [Elimination L {#C\<in># N.  (L\<in>#C)#} {#C\<in>#N. (-L\<in>#C)#}] @ T)"
    using L T A3 by auto
  hence "atms_of_mm {# C\<in>#resolve_all_on L N. \<not>tautology C#} \<subseteq> atms_of_mm N" 
    apply (auto simp: atms_of_ms_def resolve_all_on_def resolve_on_def atms_of_def
        dest: multi_member_split)
     apply (meson imageI in_diffD)
    by (meson imageI in_diffD)
  then show ?case
    by auto
qed 

lemma N_entail_resolvents:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})"
  using assms
proof(induction rule: res_stack_induct)
  case (1 L N T S) note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  (L\<in>#C)#} {#C\<in>#N. (-L\<in>#C)#} # T)"
    using L T A3 by auto
  have tot:"\<forall>I. total_over_m I (set_mset(N)) \<longrightarrow> total_over_m I (set_mset(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}))" 
    using atm_sub_N rul dist taut apply auto
    by (smt (verit) Collect_cong atm_sub_N in_mono set_mset_filter total_over_m_def total_over_set_def)
  have "(\<forall>I. total_over_m I (set_mset(N)) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s (set_mset N) \<longrightarrow> I \<Turnstile>s set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#}))"
    using atm_sub_N dist taut sat_N_then_sat_res rul apply auto
    by (smt (verit, best) Collect_cong sat_N_then_sat_res set_mset_filter true_cls_mset_def true_clss_def)
  hence "(\<forall>I. total_over_m I (set_mset(N + {#C \<in># resolve_all_on L N. \<not> tautology C#})) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s (set_mset N) \<longrightarrow> I \<Turnstile>s set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#}))"
    using tot by auto 
  then show ?case 
    using true_clss_clss_def
    by (metis (mono_tags, lifting) dist entails_resolve_all_on taut total_over_m_union true_clss_set_mset)
qed

lemma learn_resolvents: 
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" "C \<in># N'"
  shows "rules(N,  R, S,  V \<union> atms_of_mm N \<union> atms_of C\<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
      (N, add_mset C R, S, V \<union> atms_of_mm N \<union> atms_of C\<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z) note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and C = this(6)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  (L\<in>#C)#} {#C\<in>#N. (-L\<in>#C)#} # T)"
    using L T A3 by auto
  hence learn1: "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using N_entail_resolvents dist taut by blast 
  hence learn3: "(set_mset N) \<Turnstile>p C" 
    using true_clss_clss_in_imp_true_clss_cls C by blast
  have learn2: "distinct_mset C"
    using res_stack_distinct rul dist C by blast
  show ?case
    using learn3 learn2 rules.learn_minus[of N "R" C S "V \<union> atms_of_mm N"]
    by (auto simp: ac_simps)
qed

lemma learn_resolvents2: 
  assumes "res_stack (N, Z) (N', Z')" and "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and
    \<open>N'' \<subseteq># N'\<close>
  shows "rules\<^sup>*\<^sup>* (N,  R, S,  V \<union> atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
      (N, R+N'', S, V \<union> atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and N' = this(6)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  (L\<in>#C)#} {#C\<in>#N. (-L\<in>#C)#} # T)"
    using L T A3 by auto
  hence learn1: "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using N_entail_resolvents dist taut by blast 
  have learn2: "\<forall>C. C\<in># {#C \<in># resolve_all_on L N. \<not> tautology C#}  \<longrightarrow> distinct_mset C"
    using res_stack_distinct rul dist by blast
  have "rules\<^sup>*\<^sup>* (N,  R, S,  V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
     (N, R+Relim, S, V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    if \<open>Relim \<subseteq># {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> for Relim
    using that
  proof (induction Relim)
    case empty
    then show ?case by auto
  next
    case (add C Relim) note IH =this(1) and incl = this(2)
    have R: \<open>Relim \<subseteq># {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> and
      C: "C \<in># resolve_all_on L N" "\<not> tautology C"
      using incl
        apply (meson subset_mset.dual_order.refl subset_mset.order_trans subset_mset_imp_subset_add_mset)
      using incl by auto
    have \<open>rules (N, R+Relim, S, V \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm N \<union> atms_of C \<union> atms_of_mm (R+Relim) \<union> atms_of_ms (wit_clause ` set S))
       (N, add_mset C (R+Relim), S,  V \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm N \<union> atms_of C \<union> atms_of_mm (R+Relim)\<union> atms_of_ms (wit_clause ` set S))\<close>
      by (rule learn_resolvents[OF rul dist taut]) (use C in auto)
    moreover have \<open>atms_of_mm Relim \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N} =  atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}\<close>
      \<open>atms_of C \<union> (atms_of_mm N \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}) = 
        atms_of_mm N \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}\<close>
      using atms_of_ms_mono[OF set_mset_mono[OF incl]]
      by (auto simp: ac_simps)
    ultimately have \<open>rules (N, R + Relim, S, V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm R\<union> atms_of_ms (wit_clause ` set S))
       (N, add_mset C (R+ Relim), S, V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm R\<union> atms_of_ms (wit_clause ` set S))\<close>
      by (auto simp: ac_simps)
    with IH[OF R] show ?case
      by auto
  qed
  from this[OF N'] show ?case
    by auto
qed

lemma interpr_composition_neg_itself_iff:
  "interpr_composition I (uminus ` set_mset D)  \<Turnstile> D \<longleftrightarrow> D \<noteq> {#} \<and> tautology D"
  by (auto simp:interpr_composition_def true_cls_def tautology_decomp')

lemma L_not_in_resolve_on:
  assumes "L \<in>#D" and "-L \<in># C" and "\<not>tautology C" and  "\<not>tautology D" and "distinct_mset C" and "distinct_mset D"
  shows "L \<notin># (resolve_on L D C)" 
  unfolding resolve_on_def using assms apply auto
  by (smt (verit, del_insts) Multiset.diff_add add_mset_remove_trivial distinct_mset_add_mset insert_DiffM2 member_add_mset tautology_minus union_iff union_mset_add_mset_left)

lemma minus_L_not_in_resolve_on:
  assumes "L \<in>#D" and "-L \<in># C" and "\<not>tautology C" and  "\<not>tautology D" and "distinct_mset C" and "distinct_mset D"
  shows "-L \<notin># (resolve_on L D C)" 
  unfolding resolve_on_def using assms apply auto
  by (smt (verit, del_insts) Multiset.diff_add add_diff_cancel_left' cancel_ab_semigroup_add_class.diff_right_commute distinct_mset_add_mset distinct_mset_size_2 in_multiset_minus_notin_snd insert_DiffM tautology_minus)

lemma filter_mset_disj_eq: \<open>(\<And>x. P x \<Longrightarrow> \<not>Q x) \<Longrightarrow> 
  filter_mset (\<lambda>x. P x \<or> Q x) C = filter_mset P C + filter_mset Q C\<close>
  by (subst filter_union_or_split)
   (auto intro: filter_mset_cong)

(*TODO Move*)
lemma filter_mset_id_conv: \<open>filter_mset P N = N \<longleftrightarrow> (\<forall>L\<in>#N. P L)\<close>
  by (simp add: filter_mset_eq_conv)

lemma redundancy_of_resolvents: 
  assumes D: \<open>D\<in># {#D \<in># N'. (L \<in># D \<and> -L \<notin># D)#}\<close> and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and \<open>N' \<subseteq># N\<close> and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C"
  shows "redundancy ((N' - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#}) D {L}
      ((N' - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#})"
proof -
  have "{L} \<Turnstile> D"
    using D true_cls_def by fastforce
  have \<open>L \<in># D\<close> 
    using D by auto
  have "interpr_composition I (interpr_composition (uminus ` set_mset D) {L})  \<Turnstile>m ((N' - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#})" if A:"consistent_interp I " 
and B: "interpr_composition I (uminus ` set_mset D) \<Turnstile>m ((N' - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#})" for I
  proof-
    have "interpr_composition I (interpr_composition (uminus ` set_mset D) {L}) \<Turnstile> C" if C: "C \<in># {#D \<in># N'. (-L \<in># D \<and> L \<notin># D)#}" for C
    proof-
      have "-L \<in># C" 
        using C by auto
      then show ?thesis
        proof(cases "tautology (resolve_on L D C)")
          case True note taut = this
          have T1:"L \<notin># (resolve_on L D C)"
            using L_not_in_resolve_on[of L D C]
              using \<open>-L \<in># C\<close> \<open>L \<in># D\<close> assms(2, 4) C D apply auto
              using assms(3) by blast
          have T11:"-L \<notin># (resolve_on L D C)" 
              using minus_L_not_in_resolve_on[of "L" D C]
              using \<open>-L \<in># C\<close> \<open>L \<in># D\<close> assms(2, 4) C D apply auto
              using assms(3) by blast
            have "\<exists>K. K \<in># (resolve_on L D C) \<and> -K \<in># (resolve_on L D C)" 
              using True
              by (simp add: tautology_decomp') 
            hence T2: "\<exists>K. -K \<in># (remove1_mset (-L) C) \<and> K \<in># (remove1_mset L D) \<and> K \<noteq> L" 
            using T1 T11 assms(2) unfolding resolve_on_def apply auto
            apply (metis D assms(3) in_diffD mem_Collect_eq mset_subset_eq_add_left set_mset_filter subset_mset.le_imp_diff_is_add tautology_decomp' union_commute)
            apply (metis uminus_of_uminus_id)
            by (metis (no_types, lifting) assms(3) in_diffD mem_Collect_eq mset_subset_eqD set_mset_filter tautology_minus that)
          then obtain K where K1:"-K \<in># (remove1_mset (-L) C)" and K2:"K \<in># (remove1_mset L D)" and K3:"K \<noteq> L" 
            by blast 
          have K5:"-K \<in>#C" 
            using K1 K3 by auto
          have "K \<in>#D"
            using K2 K3 by auto
          hence "K \<in># (resolve_on L D C)" 
            using K1 K2 K3  unfolding resolve_on_def by auto
          hence K4: "K \<noteq> -L" 
            using T11 by auto 
          have T3:"-K \<in> (uminus ` set_mset D)"
            using K2 K3 by auto
          have T4: "-K \<in> (interpr_composition (uminus ` set_mset D) {L})" 
            using T3 K3 K4 unfolding interpr_composition_def by auto
          have "(uminus ` set_mset D) \<Turnstile> C" 
            using K1 K3 T3 apply auto
            using true_cls_def by auto
          have "(interpr_composition (uminus ` set_mset D) {L}) \<Turnstile> C"
            using T4 K1 K5 unfolding interpr_composition_def
            by (meson true_cls_def true_lit_def)
          then show ?thesis 
            unfolding interpr_composition_def apply auto
            using true_cls_union_increase' by fastforce
        next
          case False note taut = this
          have \<open>C\<in>#N\<close> and \<open>D\<in>#N\<close>
            using C D assms(3) by auto
          moreover have \<open>L \<notin># C\<close> \<open>-L \<notin># D\<close>
            using taut C D by (auto dest!: multi_member_split 
                simp: add_mset_eq_add_mset resolve_on_def)
          ultimately have F1: "remdups_mset (resolve_on L D C) \<in># {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
            using taut assms(3) \<open>-L \<in># C\<close> \<open>L \<in># D\<close>
            unfolding resolve_all_on_def 
            by (auto simp: add_mset_eq_add_mset image_Un Times_insert_right
                conj_disj_distribR Times_insert_left Collect_disj_eq Collect_conv_if
                dest!: multi_member_split[of C]  multi_member_split[of D]) 
          have F2:"L \<notin># (resolve_on L D C)" 
              using L_not_in_resolve_on[of L D C]
              using \<open>-L \<in># C\<close> \<open>L \<in># D\<close> assms(2, 4) C D apply auto
              using assms(3) by blast
         have F22:"-L \<notin># (resolve_on L D C)" 
              using minus_L_not_in_resolve_on[of "L" D C]
              using \<open>-L \<in># C\<close> \<open>L \<in># D\<close> assms(2, 4) C D apply auto
              using assms(3) by blast
          have F3: "interpr_composition I (uminus ` set_mset D) \<Turnstile> (resolve_on L D C)" 
            using B F1 apply auto unfolding interpr_composition_def apply auto
            using F1 true_cls_mset_def by blast
          hence "\<exists>J. J \<in> interpr_composition I (uminus ` set_mset D) \<and> J \<in># (resolve_on L D C)"
            apply auto
            by (meson true_cls_def true_lit_def)
          then obtain J where J1:"J \<in> interpr_composition I (uminus ` set_mset D)" and J2:"J \<in># (resolve_on L D C)"
            by blast
          have J3:"J \<noteq> L "
            using F2 J2 by  auto
          have J33:"J \<noteq> -L "
            using F22 J2 by  auto
          have J4:"J \<in> interpr_composition I (interpr_composition (uminus ` set_mset D) {L})" 
            using J1 J3 J33 unfolding interpr_composition_def by auto
          have F4:" interpr_composition I (interpr_composition (uminus ` set_mset D) {L})  \<Turnstile> (resolve_on L D C)" 
            using J4 J2  apply auto
            using true_cls_def by auto
          have "\<not>((interpr_composition I (uminus ` set_mset D)) \<Turnstile> D)"
            unfolding interpr_composition_def using assms(2, 3) apply auto
            by (metis D interpr_composition_def interpr_composition_neg_itself_iff mem_Collect_eq mset_subset_eqD set_mset_filter)
          hence F5: "\<not>((interpr_composition I (uminus ` set_mset D)) \<Turnstile> (remove1_mset L D))" 
            unfolding interpr_composition_def using assms(2, 3) apply auto
            using diff_subset_eq_self by blast
          have F7:"-L \<notin># (remove1_mset (-L) C)"
            by (metis F22 resolve_on_def union_iff) 
          have F8:"L \<notin># (remove1_mset (-L) C)" 
            using assms(2, 3) C by  auto
          have F6: "interpr_composition I (uminus ` set_mset D) \<Turnstile> (remove1_mset (-L) C)" 
            using F3 F5 unfolding interpr_composition_def apply auto
            by (simp add: resolve_on_def)
          hence "\<exists>H. H \<in> interpr_composition I (uminus ` set_mset D) \<and> H \<in># (remove1_mset (-L) C)" 
            apply auto
            by (meson true_cls_def true_lit_def)
          then obtain H where H1: "H \<in> interpr_composition I (uminus ` set_mset D)" and H2: "H \<in># (remove1_mset (-L) C)" 
            by blast
          have H3:"H \<noteq> L" 
            using F8 H2 by auto
          have H4:"H \<noteq> -L" 
            using F7 H2 by auto
          have "H \<in>  interpr_composition I (interpr_composition (uminus ` set_mset D) {L})" 
            using H1 H3 H4 unfolding interpr_composition_def by auto
          hence " interpr_composition I (interpr_composition (uminus ` set_mset D) {L})  \<Turnstile> (remove1_mset (-L) C)" 
            using H2 unfolding interpr_composition_def using true_cls_def by auto
          then show ?thesis
            unfolding interpr_composition_def apply auto
            using diff_subset_eq_self by blast
              qed
            qed note part1 = this
        have part2: "interpr_composition I (interpr_composition (uminus ` set_mset D) {L}) \<Turnstile> C" if C2: "C \<in># {#D \<in># N'. (L \<in># D \<and> -L \<notin># D)#}" for C
            unfolding interpr_composition_def apply auto
            by (smt (verit, del_insts) filter_mset_eq_conv insertI1 that true_cls_def true_lit_def)
          have "interpr_composition I (interpr_composition (uminus ` set_mset D) {L}) \<Turnstile> C" if C3: "C \<in># {#D \<in># N'. (L \<notin># D \<and> -L \<notin># D)#}" for C
          proof-
            have p1:"L \<notin># C \<and> -L \<notin># C" 
              using C3 by auto
            have "interpr_composition I (uminus ` set_mset D) \<Turnstile> C" 
              using B unfolding interpr_composition_def apply auto
              by (metis (no_types, lifting) p1 \<open>{L} \<Turnstile> D\<close> atm_of_notin_atms_of_iff in_remove1_msetI mset_subset_eqD multiset_filter_subset sup_bot.right_neutral
                  that true_cls_mset_def true_cls_remove_hd_if_notin_vars true_cls_union_increase')
            hence "\<exists>G. G \<in> interpr_composition I (uminus ` set_mset D) \<and> G \<in># C"
              apply auto
              by (meson true_cls_def true_lit_def)
            then obtain G where G1: "G \<in> interpr_composition I (uminus ` set_mset D)" and G2: "G \<in># C" 
              by blast
            have G3: "G \<noteq> L"
              using G2 p1 by auto
            have G4: "G \<noteq> -L"
              using G2 p1 by auto
            have "G \<in>  interpr_composition I (interpr_composition (uminus ` set_mset D) {L})"
              using G1 G3 G4 unfolding interpr_composition_def by auto
            then show ?thesis 
              using G2 unfolding interpr_composition_def using true_cls_def by auto
          qed note part3 = this
          have "interpr_composition I (interpr_composition (uminus ` set_mset D) {L}) \<Turnstile> C" if C4: "C \<in># {#C \<in># resolve_all_on L N. \<not> tautology C#}" for C 
          proof-
            have " atm_of L \<notin> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
              using assms(2, 4) resolved_atm_notin_resolved_clauses by blast
            hence q1:"L \<notin># C \<and> -L \<notin># C" 
              using C4  apply auto
              apply (simp add: in_implies_atm_of_on_atms_of_ms)
              using in_implies_atm_of_on_atms_of_ms by fastforce
            have "interpr_composition I (uminus ` set_mset D) \<Turnstile> C" 
              using B unfolding interpr_composition_def apply auto
              using that true_cls_mset_def by blast
            hence "\<exists>G. G \<in> interpr_composition I (uminus ` set_mset D) \<and> G \<in># C" 
              apply auto
              by (meson true_cls_def true_lit_def)
            then obtain G where G1: "G \<in> interpr_composition I (uminus ` set_mset D)" and G2: "G \<in># C" 
              by blast
            have G3: "G \<noteq> L"
              using G2 q1 by auto
            have G4: "G \<noteq> -L"
              using G2 q1 by auto
            have "G \<in>  interpr_composition I (interpr_composition (uminus ` set_mset D) {L})"
              using G1 G3 G4 unfolding interpr_composition_def by auto
            then show ?thesis 
              using G2 unfolding interpr_composition_def using true_cls_def by auto
          qed note part4 = this
          have N':"N' =  {#D \<in># N'. (L \<in># D \<and> -L \<notin># D)#} + {#D \<in># N'. (L \<notin># D \<and> -L \<notin># D)#} + 
                         {#D \<in># N'. (-L \<in># D \<and> L \<notin># D)#} + {#D \<in># N'. (-L \<in># D \<and> L \<in># D)#}" 
            by (subst filter_mset_disj_eq[symmetric], auto)+
             (auto intro!: filter_mset_id_conv[THEN iffD2, symmetric])
          hence "interpr_composition I (interpr_composition (uminus ` set_mset D) {L}) \<Turnstile>m (N' - {#D#})" 
            using part1 part2 part3 unfolding interpr_composition_def apply auto
            by (smt (verit, best) D Un_iff insertI1 insert_DiffM2 set_mset_union true_cls_def true_cls_mset_def true_lit_def) 
          then show ?thesis 
            using part4 unfolding interpr_composition_def apply auto
      by (simp add: true_cls_mset_def)
  qed
  then show ?thesis
    unfolding redundancy_def by auto
qed

lemma add_mset: "{#a#} + M = add_mset a M"
  by auto

lemma strenghten_with_resolvents:
  "rules\<^sup>*\<^sup>*(N,D+R, S,  H \<union> atms_of_mm N \<union> atms_of_mm D \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
        (N + D, R ,S, H \<union> atms_of_mm N \<union> atms_of_mm D \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
proof (induction D arbitrary: N H)
  case empty
  then show ?case by auto
next
  case (add x D) note A1 = this(1)
  have 1: \<open>rtranclp rules (N, add_mset x D+R, S, H \<union> atms_of_mm N \<union> atms_of_mm (add_mset x D) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
     ({#x#} + N, R + D, S, H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm (R + D) \<union> atms_of_mm (wit_clause `# mset S))\<close>
    using rules.strenghten[of N x "R+D" S H] by (auto simp: ac_simps)
  show ?case
    apply -
    apply (rule rtranclp_trans[OF 1])
    using add[of \<open>{#x#} + N\<close> \<open>H \<union> atms_of x\<close>] by (auto simp: ac_simps)
qed

lemma redundancy_add:
  assumes "redundancy (F-{#C#}) C \<omega> (F-{#C#})" and "redundancy (F'-{#C#}) C \<omega> (F'-{#C#})"
  shows "redundancy ((F'-{#C#}) + (F-{#C#})) C \<omega> ((F'-{#C#}) + (F-{#C#}))" 
  using assms unfolding redundancy_def by auto

lemma simulation_res_stack_rules:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists> S' V' R'. rules\<^sup>*\<^sup>*(N, R, S, V \<union> atms_of_mm N \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N', R', S', V')"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z) note L =this(1) and T = this(2,3) and N=this(4,5)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  (L\<in>#C)#} {#C\<in>#N. (-L\<in>#C)#} # T)"
    using L T by auto
  define N1 where \<open>N1 = {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#}\<close>
  define NL where \<open>NL = {#C \<in>#N. (L \<in>#C \<or> -L \<in># C)#}\<close>
  define NpL where \<open>NpL = {#C \<in>#N. (L \<in>#C)#}\<close>
  define NuL where \<open>NuL = {#C \<in>#N. (-L \<in># C)#}\<close>
  have NN: \<open>N = N1 + NL\<close>
    unfolding N1_def NL_def by auto
  obtain UpL UuL where
    [simp]: \<open>mset UpL = NpL\<close>
    \<open>mset UuL = NuL\<close>
    by (metis list_of_mset_exi)
  have LN: \<open>atm_of L \<notin> atms_of_mm N1\<close>
    using NN by (auto simp: N1_def atms_of_ms_def resolve_all_on_distrib_no_lit atm_of_notin_atms_of_iff
        dest: multi_member_split)
  have \<open>NuL = {#C \<in># N. (L \<notin># C \<and> - L \<in># C)#}\<close>
    using N
    unfolding NuL_def NpL_def NL_def
    by (metis (mono_tags, lifting) filter_mset_cong0 tautology_minus) 
  then have NNL: \<open>NuL + NpL = NL\<close>
    using N
    unfolding NuL_def NpL_def NL_def 
    by (auto simp: filter_union_or_split)
  moreover have \<open>resolve_all_on L (N1 + (NuL + NpL)) = N1 + resolve_all_on L(NuL + NpL)\<close>
    by (subst resolve_all_on_distrib_no_lit[OF LN])
      (use N in \<open>auto simp: atms_of_ms_def resolve_all_on_distrib_no_lit NN
        Duplicate_Free_Multiset.distinct_mset_remdups_mset_id
        dest: multi_member_split\<close>)
  ultimately have N_res:"{#C \<in># resolve_all_on L N. \<not> tautology C#} = {#C \<in># resolve_all_on L NL. \<not> tautology C#} + N1" 
    using NN NNL N apply auto
    by (metis add_0 filter_mset_empty_conv multiset_partition)
  have atms_N_NL: \<open>V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} = V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<close>
    using NN N_res by force
  have 0:  "rules\<^sup>*\<^sup>* (N,  R, S,  V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
        (N,R + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, S, V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
    (is \<open>rules\<^sup>*\<^sup>* ?start ?add_added_to_R\<close>)
    using learn_resolvents2[of N _ "{#C \<in># resolve_all_on L N. \<not> tautology C#}" _ "{#C \<in># resolve_all_on L NL. \<not> tautology C#}" R S V, OF rul] N 
    unfolding atms_N_NL
    by (auto simp: N_res)
  have "rules\<^sup>*\<^sup>* ?add_added_to_R
       (N + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S,
       V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    (is \<open>rules\<^sup>*\<^sup>* _ ?resolvents_in_N\<close>)
    using strenghten_with_resolvents[of N "{#C \<in># resolve_all_on L NL. \<not> tautology C#}" R S "V"]
    by (auto simp: ac_simps)
  hence R: "rules\<^sup>*\<^sup>* ?start ?resolvents_in_N" using 0
    by (meson rtranclp_trans)
  have [simp]: \<open>V \<union> atms_of_mm N \<union> (X \<union> atms_of_mm N1) \<union> V' =  V \<union> atms_of_mm N \<union> X \<union> V'\<close> for X V'
    by (auto simp: N_res NN)
  have 1: "rules\<^sup>*\<^sup>* (N,  R, S,  V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
     (N + ({#C \<in># resolve_all_on L NL. \<not> tautology C#}), R, S,
       V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"  (is \<open>rules\<^sup>*\<^sup>* _ ?st1\<close>)
    using R by (auto simp: N_res)
  have 2: \<open>rules\<^sup>*\<^sup>* ?st1
     (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) (take i UpL), 
      V \<union> atms_of_mm N \<union> atms_of_mm (mset (take i UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S)))\<close> (is \<open>rules\<^sup>*\<^sup>* _ ?st2\<close>)
    for i
  proof (induction i)
    case 0
    then show ?case 
      using NNL[symmetric] by (auto simp: NN ac_simps)
  next
    case (Suc i)
    consider 
      (1) \<open>Suc i \<le> length UpL\<close> |
      (boring) \<open>Suc i>length UpL\<close>
      by linarith
    then show ?case
    proof cases
      case boring
      then have \<open>take ( i) UpL = UpL\<close> \<open>mset (drop (Suc i) UpL) = {#}\<close>
        by simp_all
      then show ?thesis
        using Suc NNL[symmetric] by (auto simp: NN ac_simps)
    next
      case 1
      have \<open>L \<in># (UpL ! i)\<close>
        by (metis (mono_tags, lifting) "1" NpL_def Suc_le_lessD \<open>mset UpL = NpL\<close> mem_Collect_eq nth_mem_mset set_mset_filter)
      then have \<open>{L} \<Turnstile> UpL ! i\<close>
        by (auto simp: true_cls_def)
      have \<open>atm_of L \<in> atms_of (UpL ! i)\<close>
        by (simp add: \<open>L \<in># UpL ! i\<close> atm_of_lit_in_atms_of)
      have [simp]: \<open>- L \<notin># UpL ! i\<close>
        by (metis "1" N(2) NpL_def \<open>L \<in># UpL ! i\<close> \<open>mset UpL = NpL\<close> less_eq_Suc_le multiset_partition
            nth_mem_mset tautology_minus union_iff)
      have [simp]: \<open>mset (drop i UpL) = add_mset (UpL!i) (mset (drop (Suc i) UpL))\<close>
        by (metis "1" Cons_nth_drop_Suc Suc_le_lessD mset.simps(2))
      have taut:\<open>\<not> tautology (UpL ! i)\<close>
        by (metis "1" N(2) NpL_def Suc_le_lessD \<open>mset UpL = NpL\<close> mset_subset_eqD multiset_filter_subset
            nth_mem_mset)
      have NL_dist: "\<forall>C. C\<in># NL  \<longrightarrow> distinct_mset C" 
        using N(1) NN
        by simp
      have NL_taut: "\<forall>C. C\<in># NL  \<longrightarrow>  \<not>tautology C" 
        using N(2) NN
        by simp
      have "UpL ! i \<in># {#D \<in># NL. (L \<in># D \<and> - L \<notin># D)#}"
        apply (auto simp: \<open>L \<in># (UpL ! i)\<close> \<open>\<not> tautology (UpL ! i)\<close>) using NNL  \<open>mset UpL = NpL\<close>
        by (meson "1" Suc_le_lessD nth_mem_mset union_iff) 
      hence red:"redundancy (remove1_mset (UpL ! i) (NL + {#C \<in># resolve_all_on L NL. \<not> tautology C#}))  (UpL ! i) {L} (remove1_mset (UpL ! i) NL + {#C \<in># resolve_all_on L NL. \<not> tautology C#})"
        using redundancy_of_resolvents[of "UpL ! i" L NL NL ] NL_dist NL_taut by auto
      have in1:" UpL ! i \<in># {#D \<in># (N1 + NuL + mset (drop i UpL)). (L \<in># D \<and> - L \<notin># D)#}"
        by (simp add: \<open>L \<in># UpL ! i\<close>)
      have UpLi: \<open>UpL ! i \<in># (if L \<in># UpL ! i
          then add_mset (UpL ! i) {#D \<in># NuL + mset (drop (Suc i) UpL). (L \<in># D \<and> - L \<notin># D)#}
          else {#D \<in># NuL + mset (drop (Suc i) UpL). (L \<in># D \<and> - L \<notin># D)#})\<close>
        using 1 by (auto simp: \<open>L \<in># (UpL ! i)\<close> \<open>\<not> tautology (UpL ! i)\<close> simp flip: Cons_nth_drop_Suc)
      have incl: \<open>add_mset (UpL ! i) (NuL + mset (drop (Suc i) UpL)) \<subseteq># NL\<close>
        apply (auto simp flip: NNL)
        by (metis \<open>mset (drop i UpL) = add_mset (UpL ! i) (mset (drop (Suc i) UpL))\<close> \<open>mset UpL = NpL\<close> 
            append_take_drop_id mset_subset_eq_add_right union_code)
      then have incl: \<open>add_mset (UpL ! i) (NuL + mset (drop (Suc i) UpL)) \<subseteq># N1+NL\<close>
        by (simp add: subset_mset.add_increasing)
      have red:"redundancy (N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})  (UpL ! i) {L}
       (N1 + NuL + mset (drop (Suc i) UpL) +  ({#C \<in># resolve_all_on L NL. \<not> tautology C#}))"
        using redundancy_of_resolvents[of "UpL ! i" L "NuL + mset (drop (i) UpL)" "N1+NL"] using N NN incl taut in1 N_res UpLi
        by (auto simp: NN ac_simps)
      have cons: "consistent_interp {L}"
        by simp
      have h1:"mset (drop (Suc i) UpL) =  (remove1_mset (UpL ! i)  (mset (drop i UpL))) "
        by simp
      have h2:"remove1_mset (UpL !  i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) = N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}"  
        by auto
      have h3:"map (Witness {L}) (take i UpL) @ [Witness {L} (UpL !i)] = map (Witness {L}) (take (Suc i) UpL)"
        by (simp add: "1" Suc_le_lessD take_Suc_conv_app_nth)
      have h4:"remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) + {#UpL ! i#} = N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}" 
        by auto
      have at_in1:"atms_of_mm (wit_clause `# mset ( map (Witness {L}) (take i UpL))) \<subseteq> atms_of_mm N"
        using NNL NN \<open>mset UpL = NpL\<close> apply auto
        by (metis \<open>mset UpL = NpL\<close> atms_of_ms_mono in_mono set_mset_mset set_take_subset) 
      have at_in3: "atms_of_mm (mset (take (Suc i) UpL)) \<subseteq> atms_of_mm N"
        using NNL NN \<open>mset UpL = NpL\<close> apply auto
        by (metis \<open>mset UpL = NpL\<close> atms_of_ms_mono set_mset_mset set_take_subset subsetD)
      have at_in2:"atms_of (UpL ! i) \<union> atms_of_mm (remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL))) \<subseteq> atms_of_mm N" 
        unfolding NN using NNL NN \<open>mset UpL = NpL\<close> apply auto
         apply (metis "1" Suc_le_lessD UN_I \<open>mset UpL = NpL\<close> atms_of_ms_def nth_mem_mset)
        by (metis \<open>mset UpL = NpL\<close> atms_of_ms_mono set_drop_subset set_mset_mset subsetD)
      hence h5: "V \<union> atms_of_mm N \<union> atms_of (UpL ! i) \<union> atms_of_mm (remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}))
 \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) (take i UpL))) = 
V \<union> atms_of_mm N \<union> atms_of_mm (mset (take i UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)"
        using at_in1 by auto
      have h6: "V \<union> atms_of_mm N \<union> atms_of (UpL ! i) \<union> atms_of_mm (remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) 
\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) (take i UpL))) =
 V \<union> atms_of_mm N \<union> atms_of_mm (mset (take (Suc i) UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S) "
        using at_in1 at_in2 at_in3 by auto
      have "rules
     (remove1_mset (UpL !  i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) + {#UpL ! i#}, R, S @ map (Witness {L}) (take i UpL),
      V \<union> atms_of_mm N \<union> atms_of (UpL ! i) \<union> atms_of_mm (remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) (take i UpL))))
     (remove1_mset (UpL !  i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}), R, (S @ map (Witness {L}) (take i UpL)) @ [Witness {L} (UpL !i)],
     V \<union> atms_of_mm N \<union> atms_of (UpL ! i) \<union> atms_of_mm (remove1_mset (UpL ! i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) (take i UpL))))"
        using weakenp[of "{L}" "(UpL ! i)" "remove1_mset (UpL !  i) (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})" R "S @ map (Witness {L}) (take i UpL)"
            "V \<union> atms_of_mm N", OF ]
          \<open>atm_of L \<in> atms_of (UpL ! i)\<close> \<open>{L} \<Turnstile> (UpL ! i)\<close> cons red by fastforce
      hence "rules (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (Witness {L}) (take i UpL),
      V \<union> atms_of_mm N \<union> atms_of_mm (mset (take i UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
    (N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (Witness {L}) (take (Suc i) UpL),
      V \<union> atms_of_mm N \<union> atms_of_mm (mset (take (Suc i) UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
        using h1 h2 h3 h4 h5 h6
        by (metis append.assoc)
      then show ?thesis
        using Suc by auto
    qed
  qed note ag = this
  have "mset (drop (length UpL) UpL) = {#}" and "(take (length UpL) UpL) = UpL"
     apply simp by auto
  then have 2: \<open>rules\<^sup>*\<^sup>* ?st1
     (N1 + NuL + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL, 
      V  \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))\<close> (is \<open>rules\<^sup>*\<^sup>* _ ?st2\<close>)
    using ag[of "length UpL"]
    by auto
  have A3: "rules\<^sup>*\<^sup>* ?st2
 (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL  @ map (\<lambda>C. Witness {-L} C) (take i UuL), 
V  \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
    for i 
  proof (induction i)
    case 0
    then show ?case 
      using NNL[symmetric] by (auto simp: NN ac_simps)
  next
    case (Suc i)
    consider 
      (1) \<open>Suc i \<le> length UuL\<close> |
      (boring) \<open>Suc i>length UuL\<close>
      by linarith
    then show ?case
    proof cases
      case boring
      then have \<open>take ( i) UuL = UuL\<close> \<open>mset (drop (Suc i) UuL) = {#}\<close>
        by simp_all
      then show ?thesis 
        using Suc NNL[symmetric] by (auto simp: NN ac_simps)
    next
      case 1
      have \<open>-L \<in># (UuL ! i)\<close>
        by (metis (mono_tags, lifting) "1" NuL_def Suc_le_lessD \<open>mset UuL = NuL\<close> mem_Collect_eq nth_mem_mset set_mset_filter)
      then have \<open>{-L} \<Turnstile> UuL ! i\<close>
        by (auto simp: true_cls_def)
      have \<open>atm_of L \<in> atms_of (UuL ! i)\<close>
        using \<open>-L \<in># UuL ! i\<close>
        using atm_of_notin_atms_of_iff by blast
      have [simp]: \<open> L \<notin># UuL ! i\<close>
        by (metis "1" N(2) NuL_def \<open>-L \<in># UuL ! i\<close> \<open>mset UuL = NuL\<close> less_eq_Suc_le multiset_partition
            nth_mem_mset tautology_minus union_iff)
      have [simp]: \<open>mset (drop i UuL) = add_mset (UuL!i) (mset (drop (Suc i) UuL))\<close>
        by (metis "1" Cons_nth_drop_Suc Suc_le_lessD mset.simps(2))
      have taut:\<open>\<not> tautology (UuL ! i)\<close>
        by (metis "1" N(2) NuL_def Suc_le_lessD \<open>mset UuL = NuL\<close> mset_subset_eqD multiset_filter_subset
            nth_mem_mset)
      have "UuL ! i \<in># {#D \<in># NL. (-L \<in># D \<and> L \<notin># D)#}"
        apply (auto simp: \<open>-L \<in># (UuL ! i)\<close> \<open>\<not> tautology (UuL ! i)\<close>) using NNL  \<open>mset UuL = NuL\<close>
        by (meson "1" Suc_le_lessD nth_mem_mset union_iff) 
      have cons2: "consistent_interp {-L}"
        by simp
      have incl: \<open>add_mset (UuL ! i) (mset (drop (Suc i) UuL)) \<subseteq># N1 + NL\<close>
        by (metis NNL \<open>mset (drop i UuL) = add_mset (UuL ! i) (mset (drop (Suc i) UuL))\<close> \<open>mset UuL = NuL\<close> append_take_drop_id mset_subset_eq_add_left subset_mset.add_increasing subset_mset.le_add_same_cancel1 union_code union_commute)
      have red:"redundancy (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) (UuL ! i) {- L} (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}))"
        using redundancy_of_resolvents[of "UuL ! i" "-L" "mset (drop (i) UuL)" "N1+NL"]
        apply (auto simp: \<open>-L \<in># UuL ! i\<close> resolve_all_on_neg)
        using incl N NN
        apply (auto simp: NN ac_simps N_res)
        by (smt (verit, best) NN N_res add.commute add.left_commute)
      have g1:"mset (drop (Suc i) UuL) =  (remove1_mset (UuL ! i)  (mset (drop i UuL))) "
        by simp
      have g2: "map (Witness {- L}) (take i UuL) @ [Witness {- L} (UuL ! i)] = map (Witness {- L}) (take (Suc i) UuL)" 
        by (simp add: "1" Suc_le_lessD take_Suc_conv_app_nth)
      have g3: "remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) + {#UuL ! i#} = N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}"
        by auto
      have in_atm1: "atms_of (UuL ! i) \<union> atms_of_mm (remove1_mset (UuL ! i) (N1 + mset (drop i UuL))) \<subseteq> atms_of_mm N" 
        using NNL NN  \<open>mset UuL = NuL\<close> apply auto
         apply (metis "1" Suc_le_lessD UN_I \<open>mset UuL = NuL\<close> atms_of_ms_def nth_mem_mset)
        by (metis \<open>mset UuL = NuL\<close> atms_of_ms_mono set_drop_subset set_mset_mset subsetD)
      have in_atm2: "atms_of_mm (wit_clause `# mset ( map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL))) \<subseteq> atms_of_mm N" 
        using NNL NN  \<open>mset UuL = NuL\<close> apply auto
        by (metis \<open>mset UuL = NuL\<close> atms_of_ms_mono in_mono set_mset_mset set_take_subset)
      have in_atm3: "atms_of_mm NpL \<subseteq> atms_of_mm N" 
        using NNL NN  \<open>mset UuL = NuL\<close> by auto
      have g4: " V \<union> atms_of_mm N \<union> atms_of (UuL ! i) \<union> atms_of_mm (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union>
    atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL))) = 
V \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)"
        using in_atm1 in_atm2 in_atm3 by auto
      have g5: "V \<union> atms_of_mm N \<union> atms_of (UuL ! i) \<union> atms_of_mm (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union>
    atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL))) =
 V \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S) "
        using in_atm1 in_atm2 in_atm3 by auto 
      have g6: "remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) =  (N1 + mset (drop (Suc i) UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})" 
        by auto
      have"rules(remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}) + {#UuL ! i#}, R, S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL),
      V \<union> atms_of_mm N \<union> atms_of (UuL ! i) \<union> atms_of_mm (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union>
    atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL))))
 (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}), R, (S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL)) @ [Witness {- L} (UuL ! i)],
      V \<union> atms_of_mm N \<union> atms_of (UuL ! i) \<union> atms_of_mm (remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})) \<union> atms_of_mm R \<union>
    atms_of_mm (wit_clause `# mset (S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL))))"
        using weakenp[of "{-L}" "(UuL ! i)" "remove1_mset (UuL ! i) (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})" R "S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL)" "V \<union> atms_of_mm N"]
          cons2 \<open>atm_of L \<in> atms_of (UuL ! i)\<close> \<open>{-L} \<Turnstile> UuL ! i\<close> red by fastforce
      hence "rules (N1 + mset (drop i UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (Witness {L}) UpL @ map (Witness {- L}) (take i UuL),
      V \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
(N1 + mset (drop (Suc i) UuL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (Witness {L}) UpL @ map (Witness {- L}) (take (Suc i) UuL),
      V \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))" 
        using g1 g2 g3 g4 g5 g6 by (metis append.assoc) 
      then show ?thesis
        using Suc by auto
    qed
  qed note last_rul = this
  have " mset (drop (length UuL) UuL) = {#}" and "(take (length UuL) UuL) = UuL"
     apply simp by auto
  hence 3: \<open>rules\<^sup>*\<^sup>* ?st2
     (N1 + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL@ map (\<lambda>C. Witness {-L} C) UuL, 
      V  \<union> atms_of_mm N \<union>atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))\<close> 
    using last_rul[of "length UuL" ] by simp
  have "{#C \<in># resolve_all_on L N. \<not> tautology C#} = N1 + {#C \<in># resolve_all_on L NL. \<not> tautology C#}"
    using N_res by auto
  then have "rules\<^sup>*\<^sup>* ?st2
     ({#C \<in># resolve_all_on L N. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL@ map (\<lambda>C. Witness {-L} C) UuL, 
      V  \<union> atms_of_mm N \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))" 
    using 3 by auto
  then have "rules\<^sup>*\<^sup>* (N, R, S, V \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#} \<union> atms_of_mm R \<union>
      atms_of_ms (wit_clause ` set S))
     ({#C \<in># resolve_all_on L N. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL@ map (\<lambda>C. Witness {-L} C) UuL, 
      V  \<union> atms_of_mm N \<union>atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#}\<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
  (is \<open>rules\<^sup>*\<^sup>* (N, R, S, ?V) _\<close>)
    using 2 1
    by (meson rtranclp_trans) 
  moreover have \<open>?V = V \<union> atms_of_mm N \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)\<close>
    by (force simp: NN atms_of_ms_def resolve_all_on_def resolve_on_def
        dest!: multi_member_split[of L] multi_member_split[of "-L"])
  ultimately show ?case
    by auto
qed

lemma rules_mono_set: 
   \<open>rules (N, R, S, V) (N', R', S', V') \<Longrightarrow> rules (N, R, S, V \<union> X) (N', R', S', V' \<union> X)\<close>
   proof(induction rule: rules_induct)
     case (drop N C R S V)
     then show ?case 
       using rules.drop[of N C R S "V \<union> X"] apply auto
       by (simp add: Un_left_commute sup_commute)
   next
     case (strenghten N C R S V)
     then show ?case 
       using rules.strenghten[of N C R S "V \<union> X"] apply auto
       by (simp add: Un_left_commute sup_commute)
   next
     case (weakenp I C N R S V)
     then show ?case 
       using rules.weakenp[of I C N R S  "V \<union> X"] apply auto 
       by (simp add: Un_left_commute sup_commute)
   next
     case (forget N C R S V)
     then show ?case 
       using rules.forget[of N C R S "V \<union> X"] apply auto
       by (simp add: Un_left_commute sup_commute)
   next
     case (learn_minus N R C S V)
     then show ?case 
       using rules.learn_minus[of N R C S "V \<union> X"] apply auto 
       by (simp add: Un_left_commute sup_commute)
   qed

lemma rtranclp_rules_mono_set: 
  \<open>rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V') \<Longrightarrow> rules\<^sup>*\<^sup>* (N, R, S, V \<union> X) (N', R', S', V' \<union> X)\<close>
  by (induction rule: rtranclp_induct4)
   (auto dest: rules_mono_set[of _ _ _ _ _ _ _ _ X])

lemma rtranclp_simulation_res_stack_rules:
  assumes "res_stack\<^sup>*\<^sup>* (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists>  S'  V'  R' V. rules\<^sup>*\<^sup>*(N, R, S, V \<union> atms_of_mm N \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N', R', S', V')"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case 
    using simulation_res_stack_rules
    by blast
next
  case (step N' Z' N'' Z'') note  A1 = this(1) and A2 = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have rul:"res_stack\<^sup>*\<^sup>* (N, Z) (N', Z')" using assms(1)
    by (simp add: A1) 
  have rul1:"\<exists> S'  V'  R' V. rules\<^sup>*\<^sup>* (N, R, S, V \<union> atms_of_mm N \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N', R', S', V')"
    using dist taut A3 by auto
  then obtain  S'  V'  R' V where rul2:"rules\<^sup>*\<^sup>* (N, R, S, V \<union> atms_of_mm N \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) (N', R', S', V')"
    by blast
  have dist2: "\<forall>C \<in># N'. distinct_mset C"
    using rtranclp_res_stack_distinct rul dist by blast
  have taut2: "\<forall>C. C\<in># N'  \<longrightarrow>  \<not>tautology C"
    using rtranclp_res_stack_tauto rul taut by blast
  have rul4:"\<exists>  S''  V''  R''. rules\<^sup>*\<^sup>* (N', R', S', V' \<union> atms_of_mm N' \<union> atms_of_mm R' \<union> atms_of_ms (wit_clause ` set S')) (N'', R'', S'', V'')" 
    using simulation_res_stack_rules[of N' Z' N'' Z'' R' S' V'] A2 dist2 taut2 by auto
  then obtain S'' V'' R'' where rul5:"rules\<^sup>*\<^sup>* (N', R', S', V' \<union> atms_of_mm N' \<union> atms_of_mm R' \<union> atms_of_ms (wit_clause ` set S')) (N'', R'', S'', V'')" 
    by blast
  have "rules\<^sup>*\<^sup>* (N', R', S', V' \<union> atms_of_mm N' \<union> atms_of_mm R' \<union> atms_of_ms (wit_clause ` set S')) (N'', R'', S'', V'')" 
    using rul5 by auto
  then show ?case 
    using rul2
    by (meson rtranclp_rules_mono_set transitive_closurep_trans'(2))
qed

end
