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
  using assms proof(induction rule: res_stack_induct)
  case (1 L N T S)note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have "res_stack (N, Z) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, Z @ [Elimination L {#C\<in># N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#}] @ T)"
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
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
  have tot:"\<forall>I. total_over_m I (set_mset(N)) \<longrightarrow> total_over_m I (set_mset(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}))" using atm_sub_N rul dist taut apply auto
    by (smt (verit) Collect_cong atm_sub_N in_mono set_mset_filter total_over_m_def total_over_set_def)
  have "(\<forall>I. total_over_m I (set_mset(N)) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s (set_mset N) \<longrightarrow> I \<Turnstile>s set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#}))" using atm_sub_N dist taut sat_N_then_sat_res rul apply auto
    by (smt (verit, best) Collect_cong sat_N_then_sat_res set_mset_filter true_cls_mset_def true_clss_def)
  hence "(\<forall>I. total_over_m I (set_mset(N + {#C \<in># resolve_all_on L N. \<not> tautology C#})) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s (set_mset N) \<longrightarrow> I \<Turnstile>s set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#}))"
    using tot by auto 
  then show ?case using true_clss_clss_def
    by (metis (mono_tags, lifting) dist entails_resolve_all_on taut total_over_m_union true_clss_set_mset)
qed

lemma learn_resolvents: 
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" "C \<in># N'"
  shows "rules(N,  R, [],  V \<union> atms_of_mm N \<union> atms_of C\<union> atms_of_mm R) (N, add_mset C R, [], V \<union> atms_of_mm N \<union> atms_of C\<union> atms_of_mm R)"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and C = this(6)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
  hence learn1: "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using N_entail_resolvents dist taut by blast 
  hence learn3: "(set_mset N) \<Turnstile>p C" 
    using true_clss_clss_in_imp_true_clss_cls C by blast
  have learn2: "distinct_mset C"
    using res_stack_distinct rul dist C by blast
  show ?case
    using learn3 learn2 rules.learn_minus[of N "R" C "[]" "V \<union> atms_of_mm N"]
    by (auto simp: ac_simps)
qed

lemma learn_resolvents2: 
  assumes "res_stack (N, Z) (N', Z')" and "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "rules\<^sup>*\<^sup>* (N,  {#}, [],  atms_of_mm N \<union> atms_of_mm N') (N, N', [], atms_of_mm N \<union> atms_of_mm N')"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
  hence learn1: "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using N_entail_resolvents dist taut by blast 
  have learn2: "\<forall>C. C\<in># {#C \<in># resolve_all_on L N. \<not> tautology C#}  \<longrightarrow> distinct_mset C"
    using res_stack_distinct rul dist by blast
  have "rules\<^sup>*\<^sup>* (N,  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}) 
     (N, R, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    if \<open>R \<subseteq># {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> for R
    using that
  proof (induction R)
    case empty
    then show ?case by auto
  next
    case (add C R) note IH =this(1) and incl = this(2)
    have R: \<open>R \<subseteq># {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> and
     C: "C \<in># resolve_all_on L N" "\<not> tautology C"
      using incl
       apply (meson subset_mset.dual_order.refl subset_mset.order_trans subset_mset_imp_subset_add_mset)
      using incl by auto
    have \<open>rules (N, R, [], atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm N \<union> atms_of C \<union> atms_of_mm R)
       (N, add_mset C R, [],  atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm N \<union> atms_of C \<union> atms_of_mm R)\<close>
      by (rule learn_resolvents[OF rul dist taut]) (use C in auto)
    moreover have \<open>atms_of_mm R \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N} =  atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}\<close>
      \<open>atms_of C \<union> (atms_of_mm N \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}) = 
        atms_of_mm N \<union> atms_of_ms {a. \<not> tautology a \<and> a \<in># resolve_all_on L N}\<close>
      using atms_of_ms_mono[OF set_mset_mono[OF incl]]
      by (auto simp: ac_simps)
    ultimately have \<open>rules (N, R, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#})
       (N, add_mset C R, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#})\<close>
      by (auto simp: ac_simps)
    with IH[OF R] show ?case
      by auto
  qed
  then show ?case
    by auto
qed

lemma interpr_composition_neg_itself_iff:
  "interpr_composition I (uminus ` set_mset D)  \<Turnstile> D \<longleftrightarrow> D \<noteq> {#} \<and> tautology D"
  by (auto simp:interpr_composition_def true_cls_def tautology_decomp')

(*verdoppelt die klauseln ohne L*)
lemma redundancy_of_resolvents: 
  assumes D: \<open>D\<in># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}\<close> \<open>\<not>tautology D\<close>
  shows "redundancy ((N - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#}) D {L}
      ((N - {#D#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#})"
proof -
  have "{L} \<Turnstile> D"
    using D true_cls_def by fastforce
  have \<open>\<not>interpr_composition I (uminus ` set_mset D) \<Turnstile>m (N + {#C \<in># resolve_all_on L N. \<not> tautology C#})\<close> for I
    using D by (auto dest!: multi_member_split[of D]
        simp: interpr_composition_neg_itself_iff)
  then show ?thesis
    unfolding redundancy_def apply auto
    sorry
qed

lemma redundancy_of_resolvents2:
  assumes  D: \<open>D\<in># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}\<close> \<open>\<not>tautology D\<close>
  shows "redundancy (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) D {-L} (N + {#C \<in># resolve_all_on L N. \<not> tautology C#})"
proof-
  have "{-L} \<Turnstile> D"
    using D true_cls_def by fastforce
  have \<open>\<not>interpr_composition I (uminus ` set_mset D) \<Turnstile>m (N + {#C \<in># resolve_all_on L N. \<not> tautology C#})\<close> for I
    using D by (auto dest!: multi_member_split[of D]
        simp: interpr_composition_neg_itself_iff)
  then show ?thesis 
    unfolding redundancy_def by auto
qed

lemma add_mset: "{#a#} + M = add_mset a M"
  by auto



lemma simulation_res_stack_rules:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists> S' V' R'. rules\<^sup>*\<^sup>*(N, R, S, V) (N', R', S', V')"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z) note L =this(1) and T = this(2,3) and N=this(4,5)
  define N1 where \<open>N1 = {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#}\<close>
  define NL where \<open>NL = {#C \<in>#N. L \<in>#C \<or> -L \<in># C#}\<close>
  define NpL where \<open>NpL = {#C \<in>#N. (L \<in>#C)#}\<close>
  define NuL where \<open>NuL = {#C \<in>#N. -L \<in># C#}\<close>
  have NN: \<open>N = N1 + NL\<close>
    unfolding N1_def NL_def by auto

  obtain UpL UuL where
    [simp]: \<open>mset UpL = NpL\<close>
      \<open>mset UuL = NuL\<close>
    by (metis list_of_mset_exi)
  let ?SU = \<open>S @ map (\<lambda>C. Witness {L} C) U\<close>
  have \<open>NuL = {#C \<in># N. L \<notin># C \<and> - L \<in># C#}\<close>
    using N
    unfolding NuL_def NpL_def NL_def
    by (metis (mono_tags, lifting) filter_mset_cong0 tautology_minus) 
  then have NNL: \<open>NuL + NpL = NL\<close>
    using N
    unfolding NuL_def NpL_def NL_def 
    by (auto simp: filter_union_or_split)

  have 1: \<open>rules\<^sup>*\<^sup>* (N, R, S, V)
    (N + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S, 
      V \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close> (is \<open>rules\<^sup>*\<^sup>* (N, R, S, V) ?st1\<close>)
    (*schon gezeigt*)
    sorry


  have 2: \<open>rules\<^sup>*\<^sup>* ?st1
     (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) (take i UpL), 
      V  \<union> atms_of_mm (mset (take i UpL)) \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close> (is \<open>rules\<^sup>*\<^sup>* _ ?st2\<close>)
    for i
  proof (induction i)
    case 0
    then show ?case using NNL[symmetric] by (auto simp: NN ac_simps)
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
      then show ?thesis using Suc NNL[symmetric] by (auto simp: NN ac_simps)

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
      have \<open>\<not> tautology (UpL ! i)\<close>
        by (metis "1" N(2) NpL_def Suc_le_lessD \<open>mset UpL = NpL\<close> mset_subset_eqD multiset_filter_subset
            nth_mem_mset)

      have \<open>UpL ! i
       \<in>#  {#D \<in># N1 + NuL + mset (drop (i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}. L \<in># D \<and> - L \<notin># D#}\<close>
        using 1 by (auto simp: \<open>L \<in># (UpL ! i)\<close> \<open>\<not> tautology (UpL ! i)\<close> simp flip: Cons_nth_drop_Suc)

      then have \<open>redundancy (N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL.  \<not> tautology C#})
           (UpL ! i) {L}
          (N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close>
        using redundancy_of_resolvents[of \<open>UpL ! i\<close> L "(N1 + NuL + mset (drop (i) UpL) + {#C \<in># resolve_all_on L NL.  \<not> tautology C#})"]
        \<open>\<not> tautology (UpL ! i)\<close>
        apply (auto simp: )
        sorry
      then have \<open>rules (N1 + NuL + mset (drop i UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R,
        S @ map (Witness {L}) (take i UpL),
        V \<union> atms_of_ms (set (take i UpL)) \<union>
        atms_of_ms {a. a \<in># resolve_all_on L NL \<and> \<not> tautology a})
       (N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R,
        S @ map (Witness {L}) (take (Suc i) UpL),
        V \<union> atms_of_ms (set (take (Suc i) UpL)) \<union>
        atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close>
        (is \<open>rules (?N, ?R, ?V, ?S) _\<close>)
        using weakenp[of "{L}" "UpL ! i" "(N1 + NuL + mset (drop (Suc i) UpL) + {#C \<in># resolve_all_on L NL. \<not> tautology C#})"
          ?R ?V ?S] 1 \<open>{L} \<Turnstile> UpL ! i\<close>\<open>atm_of L \<in> atms_of (UpL ! i)\<close>
        apply auto
          (*\S should be equal in both expression*)
        sorry
      then show ?thesis
        using Suc by auto
    qed
  qed

  have 2: \<open>rules\<^sup>*\<^sup>* ?st1
     (N1 + NuL + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL, 
      V  \<union> atms_of_mm NpL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close> (is \<open>rules\<^sup>*\<^sup>* _ ?st2\<close>)
    sorry

  have 3: \<open>rules\<^sup>*\<^sup>* ?st2
     (N1 + {#C \<in># resolve_all_on L NL. \<not> tautology C#}, R, S @ map (\<lambda>C. Witness {L} C) UpL@ map (\<lambda>C. Witness {L} C) UuL, 
      V  \<union> atms_of_mm NL \<union> atms_of_mm {#C \<in># resolve_all_on L NL. \<not> tautology C#})\<close> 
    sorry



  obtain U where
    \<open>mset U = N\<close>
    by (metis list_of_mset_exi)
  let ?SU = \<open>S @ map (\<lambda>C. Witness {L} C) U\<close>
  let ?VU = \<open>V \<union> atms_of_mm (mset U) \<union> atms_of_mm (wit_clause `# mset (S @ map (\<lambda>C. Witness {L} C) U))\<close>
  have \<open>rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, V)
    (N - mset U + {#C \<in># resolve_all_on L N. \<not> tautology C#},{#}, S @ map (\<lambda>C. Witness {L} C) U, 
      V \<union> atms_of_mm (mset U) \<union> atms_of_mm (wit_clause `# mset (S @ map (\<lambda>C. Witness {L} C) U)))\<close>
    if \<open>mset U \<subseteq># N\<close>
    for U
    sorry
  then have \<open>rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, V)
    ({#C \<in># resolve_all_on L N. \<not> tautology C#},{#}, ?SU, ?VU)\<close>
    sorry
  show ?case sorry
qed




(*L hat verschiedene Farben, wie kann es eine Farbe haben?*)
lemma weaken_resolvents_L:
  assumes "res_stack (N, Z) (N', Z')" and
    "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and
    "C \<in># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}"
  shows "rules(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S,
      atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {L} C])))
  (N - {#C#} + {#C \<in># resolve_all_on L N. \<not> tautology C#},{#}, S @[Witness {L} C], 
      atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {L} C])))"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L' N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and set = this(6)
  
  have C:"C \<in># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}" using set  sorry
  hence ent:  "{L} \<Turnstile> C " using assms(4)
    by (metis (no_types, lifting) insert_DiffM mem_Collect_eq set_mset_filter singletonI true_cls_add_mset) 
  have cons: "consistent_interp {L}" 
    by simp 
  have sub: "atm_of ` {L} \<subseteq> atms_of C"
    using ent true_cls_remove_hd_if_notin_vars by fastforce
  have red: "redundancy (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) C {L} (N + {#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using redundancy_of_resolvents taut C by auto
  have atm:"{} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset [Witness {L} C]) =  atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
    apply simp by auto
  have A:"(N - {#C#}) + {#C#} = N" using C by simp
  have "rules ((N - {#C#}) + {#C#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, {} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {L} C])))
     ((N - {#C#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S @[Witness {L} C],{} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {L} C])))"
    using sub cons ent rules.weakenp A sorry
  then show ?case using atm apply simp sorry
qed

(*L hat verschiedene Farben, wie kann es die gleiche Farbe haben?*)
lemma weaken_resolvents_minL:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and  "C \<in># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}"
  shows  "rules(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {-L} C])))
(N - {#C#} + {#C \<in># resolve_all_on L N. \<not> tautology C#},{#}, [Witness {-L} C]@S,  atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {-L} C])))"
using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and set = this(6) 
  have C:"C \<in># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}" using set sorry
  hence ent:  "{-L} \<Turnstile> C " using assms(4)
    by (metis (no_types, lifting) insert_DiffM mem_Collect_eq set_mset_filter singletonI true_cls_add_mset) 
  have cons: "consistent_interp {-L}" 
    by simp 
  have sub: "atm_of ` {-L} \<subseteq> atms_of C"
    using ent true_cls_remove_hd_if_notin_vars by fastforce
  have red: "redundancy (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) C {-L} (N + {#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using redundancy_of_resolvents2 taut C by auto
  have atm:"{} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset [Witness {-L} C]) =  atms_of C \<union> atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
    apply simp by auto
  have A:"(N - {#C#}) + {#C#} = N" using C by simp
  have "rules ((N - {#C#}) + {#C#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, {} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {-L} C])))
     ((N - {#C#}) + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, [Witness {-L} C]@S,{} \<union> atms_of C \<union> atms_of_mm (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset (S @[Witness {-L} C])))"
    using sub cons ent rules.weakenp A sorry
  then show ?case using atm apply simp sorry
qed


(*Wieso geht das hier nicht?*)
lemma N_equal:
  assumes "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "N + {#C \<in># resolve_all_on L N. \<not> tautology C#} =  {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}+ {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}"
  using assms
proof-
  have N: "N = {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}+ {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#D \<in># N. (-L \<notin># D \<and> L \<notin># D)#}" using assms(2)  sorry
  hence N2:"N + {#C \<in># resolve_all_on L N. \<not> tautology C#} =  {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}+ {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#D \<in># N. (-L \<notin># D \<and> L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
    by auto
  have sub: "{#D \<in># N. (-L \<notin># D \<and> L \<notin># D)#} \<subseteq># {#C \<in># resolve_all_on L N. \<not> tautology C#}" unfolding resolve_all_on_def using assms(2) apply auto sorry
  then show ?thesis using N2 sorry
qed

(*L hat verschiedene Farben, wie kann es die gleiche Farbe haben?*)
lemma weaken_resolvents_1: 
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and "wit_clause `# mset S =  {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}" and "wit_interp `# mset S = {#{-L}#}"
  shows "rules\<^sup>*\<^sup>* (N + N',  {#}, [],  atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm (wit_clause `# mset (S ))) ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + N', {#}, S , atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm (wit_clause `# mset (S )))"
using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and set = this(6) and inter = this(7)
   have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
  have  "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#},  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (P ))) 
((N - (wit_clause `# mset (P ))) + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, P , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (P )))"
    if "wit_clause `# mset P \<subseteq># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}\<and>wit_interp `# mset P = {#{-L}#}" for P 
    using that
  proof (induction P)
    case Nil
    then show ?case by auto
  next
    case (Cons a P) note A1 = this(1) and A2 = this(2)
    have "wit_clause `# mset (a # P) \<subseteq># {#D \<in># N. (- L \<in># D \<and> L \<notin># D)#} \<and> wit_interp `# mset (a # P) = {#{- L}#}" using A2 by auto
    hence "wit_interp `# mset (a # P) = {#{- L}#}" by auto
    hence inter2:"wit_interp `# mset P = {#{- L}#}"  sorry
    have sub:"wit_clause `# mset P \<subset># wit_clause `# mset (a # P)"
      by simp
    hence sub2:"wit_clause `# mset P \<subseteq># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}" using A2
      by (meson subset_mset.dual_order.strict_implies_order subset_mset.dual_order.trans)
    hence rul2:"rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset P))
     (N - wit_clause `# mset P + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset P))"
      using A1 inter2 by auto
    have " atms_of_mm N \<union> atms_of_mm (wit_clause `# mset P) =  atms_of_mm N \<union> atms_of_mm (wit_clause `# mset (a # P))" using A2
      by (metis (no_types, lifting) Un_absorb2 atms_of_ms_mono multiset_filter_subset set_mset_mono sub subset_mset.dual_order.trans subset_msetE)
    hence "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (a # P)))
     (N - wit_clause `# mset P + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (a # P)))"
      using rul2
      by (smt (verit, best) sup.commute sup_assoc)
    have a_in:"wit_clause a \<in># {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}"
      using A2 by auto
    hence a_in2:"wit_clause a \<in># {#D \<in># N - wit_clause `# mset P. (-L \<in># D \<and> L \<notin># D)#}" using sub sorry
    have dist2: "\<forall>C. C \<in># N - wit_clause `# mset P \<longrightarrow> distinct_mset C" using dist sub2
      by (meson in_diffD) 
  have taut2: "\<forall>C. C \<in># N - wit_clause `# mset P \<longrightarrow> \<not> tautology C " using taut sub2
    by (meson in_diffD)
  have A:"{#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} \<subseteq># (N - wit_clause `# mset P)" sorry
  have B: "atm_of L \<in> atms_of_mm{#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}"  sorry
  hence L2: "atm_of L \<in> atms_of_mm (N - wit_clause `# mset P)" using A
    using atms_of_ms_mono set_mset_mono by blast
  have rul3:"res_stack ((N - wit_clause `# mset P), Z) ({#C \<in># resolve_all_on L (N - wit_clause `# mset P). \<not> tautology C#},  Z @ Elimination L {#C\<in>#(N - wit_clause `# mset P).  L\<in>#C#} {#C\<in>#(N - wit_clause `# mset P). -L\<in>#C#} # T)" 
    using rul sub2 L2 T A3 sorry
(*ist der nächste Schritt überhaupt sinnvoll?*)
  have "rules((N - wit_clause `# mset P) + {#C \<in># resolve_all_on L (N - wit_clause `# mset P). \<not> tautology C#}, {#}, P,  atms_of(wit_clause a)\<union> atms_of_mm (N - wit_clause `# mset P) \<union>
 atms_of_mm {#C \<in># resolve_all_on L (N - wit_clause `# mset P). \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (P@[Witness {-L} (wit_clause a)])))
((N - wit_clause `# mset P) - {#wit_clause a#}  + {#C \<in># resolve_all_on L (N - wit_clause `# mset P). \<not> tautology C#}, {#},  [Witness {-L} (wit_clause a)]@ P,atms_of(wit_clause a)\<union> atms_of_mm (N - wit_clause `# mset P)
 \<union> atms_of_mm {#C \<in># resolve_all_on L (N - wit_clause `# mset P). \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (P@[Witness {-L} (wit_clause a)])))"
    using weaken_resolvents_minL[of "(N - wit_clause `# mset P)"  _ _ _ "wit_clause a"] rul3 dist2 taut2 a_in2 by auto
    then show ?case  sorry
  qed note res = this(1)
  have "N  +  {#C \<in># resolve_all_on L N. \<not> tautology C#} = {#D \<in># N. (- L \<in># D \<and> L \<notin># D)#} + {#D \<in># N. (L \<in># D \<and> - L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
    using N_equal dist taut by auto
  hence  "N  +  {#C \<in># resolve_all_on L N. \<not> tautology C#}- {#D \<in># N. (- L \<in># D \<and> L \<notin># D)#} = {#D \<in># N. (L \<in># D \<and> - L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}"
    by (metis (no_types, lifting) add_diff_cancel_left' add_right_imp_eq multiset_filter_subset subset_mset.add_diff_assoc2) 
  then show ?case using res set 
    sorry
qed

(*L hat verschiedene Farben, wie kann es die gleiche Farbe haben?*)
lemma weaken_resolvents_2: 
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and "wit_clause `# mset S =  {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}"  and "wit_clause `# mset S' =  {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}"
and "wit_interp `# mset S = {#{-L}#}" and "wit_interp `# mset S' = {#{L}#}"
  shows "rules\<^sup>*\<^sup>* ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + N', {#}, S , atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm  (wit_clause `# mset (S @S'))) (N', {#}, S@S' , atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm  (wit_clause `# mset (S @S')))"
using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z) note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and set = this(6) and set2 = this(7) and inter =this(8) and inter2 = this(9)
have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
 have  "rules\<^sup>*\<^sup>* ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#},  {#}, S,  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (S )) \<union> atms_of_mm (wit_clause `# mset (P ))) 
({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S@P , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S ))\<union> atms_of_mm (wit_clause `# mset (P )))"
    if "wit_clause `# mset P \<subseteq># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}\<and>wit_interp `# mset P = {#{L}#}" for P 
    using that
  proof (induction P)
    case Nil
    then show ?case by auto
  next
    case (Cons a P) note A1 = this(1) and A2 = this(2)
have "wit_clause `# mset (a # P) \<subseteq># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} \<and> wit_interp `# mset (a # P) = {#{L}#}" using A2 by auto
    hence "wit_interp `# mset (a # P) = {#{L}#}" by auto
    hence inter2:"wit_interp `# mset P = {#{L}#}"  sorry
    have sub:"wit_clause `# mset P \<subset># wit_clause `# mset (a # P)"
      by simp
    hence sub2:"wit_clause `# mset P \<subseteq># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}" using A2
      by (meson subset_mset.dual_order.strict_implies_order subset_mset.dual_order.trans)
    hence rul2:"rules\<^sup>*\<^sup>* ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset S)\<union> atms_of_mm (wit_clause `# mset (P )))
     ( {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S@P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset S)\<union> atms_of_mm (wit_clause `# mset (P )))"
      using A1 inter2 by auto
    have " atms_of_mm N \<union> atms_of_mm (wit_clause `# mset P) =  atms_of_mm N \<union> atms_of_mm (wit_clause `# mset (a # P))" using A2
      by (metis (no_types, lifting) Un_absorb2 atms_of_ms_mono multiset_filter_subset set_mset_mono sub subset_mset.dual_order.trans subset_msetE)
    hence "rules\<^sup>*\<^sup>* ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset S) \<union> atms_of_mm (wit_clause `# mset (a # P)))
     ({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S@P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset S) \<union> atms_of_mm (wit_clause `# mset (a # P)))"
      using rul2
      by (smt (verit, best) sup.commute sup_assoc)
    have a_in:"wit_clause a \<in># {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}"
      using A2 by auto
    hence a_in2:"wit_clause a \<in># {#D \<in># {#wit_clause a#}. (L \<in># D \<and> -L \<notin># D)#}"  by auto
    have a_in3: "wit_clause a \<in># N" using a_in by auto
    have dist2: "\<forall>C. C \<in># {#wit_clause a#} \<longrightarrow> distinct_mset C" using dist a_in3
      by simp
  have taut2: "\<forall>C. C \<in># {#wit_clause a#} \<longrightarrow> \<not> tautology C " using taut a_in3
    by simp
  have B: "atm_of L \<in> atms_of_mm{#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}"
    using a_in in_implies_atm_of_on_atms_of_ms by fastforce  
  hence L2: "atm_of L \<in> atms_of_mm {#wit_clause a#}" using a_in
    by (smt (verit, del_insts) filter_mset_eq_conv in_m_in_literals member_add_mset mset_add)
  have rul3:"res_stack ( {#wit_clause a#} , Z) ({#C \<in># resolve_all_on L  {#wit_clause a#} . \<not> tautology C#},  Z @ Elimination L {#C\<in># {#wit_clause a#} .  L\<in>#C#} {#C\<in># {#wit_clause a#} . -L\<in>#C#} # T)" 
    using rul sub2 L2 T A3 sorry
(*ist der nächste Schritt überhaupt sinnvoll?*)
  have rul4: " rules({#wit_clause a#} + {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#}, {#}, S,
      atms_of (wit_clause a) \<union> atms_of_mm {#wit_clause a#} \<union> atms_of_mm {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ [Witness {L} (wit_clause a)])))
     (remove1_mset (wit_clause a) {#wit_clause a#} + {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#}, {#}, S @ [Witness {L} (wit_clause a)],
      atms_of (wit_clause a) \<union> atms_of_mm {#wit_clause a#} \<union> atms_of_mm {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ [Witness {L} (wit_clause a)])))"
    using weaken_resolvents_L[of " {#wit_clause a#} "  _ _ _ "wit_clause a"] rul3 dist2 taut2 a_in2 by auto
  have atm:"atms_of (wit_clause a) \<union> atms_of_mm {#wit_clause a#} \<union> atms_of_mm {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ [Witness {L} (wit_clause a)]))
 = atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ S'))" sorry
  have " rules({#wit_clause a#} + {#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#}, {#}, S,  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ S')))
({#C \<in># resolve_all_on L {#wit_clause a#}. \<not> tautology C#}, {#}, S @ [Witness {L} (wit_clause a)], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @ S')))"
    using rul4 atm by auto
    then show ?case sorry
  qed note res = this(1)
  then show ?case using set2 inter2 res   sorry 
qed

(*L hat verschiedene Farben, wie kann es die gleiche Farbe haben?*)
lemma weaken_resolvents:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and
    "wit_clause `# mset S =  {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#}" and "wit_clause `# mset S' =  {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#}" and
    "wit_interp `# mset S = {#{-L}#}" and "wit_interp `# mset S' = {#{L}#}"
  shows "rules\<^sup>*\<^sup>* (N + N',  {#}, [],  atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm (wit_clause `# mset (S @S'))) (N', {#}, S@S' , atms_of_mm N \<union> atms_of_mm N' \<union> atms_of_mm (wit_clause `# mset (S @S')))"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z)  note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5) and set = this(6) and set2 = this(7) and inter = this(8) and inter2 = this(9)
  have rul:  "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#}, Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)" 
    using L T A3 by auto
  have "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#},  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S ))) 
({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S )))" 
    using rul set inter  weaken_resolvents_1 dist taut  sorry
  hence ruls: "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#},  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union>atms_of_mm  (wit_clause `# mset (S @S'))) 
({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm  (wit_clause `# mset (S @S')))" sorry
  have "rules\<^sup>*\<^sup>* ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm  (wit_clause `# mset (S @S'))) 
({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S@S' , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm  (wit_clause `# mset (S @S')))" 
    using rul set set2 inter inter2 weaken_resolvents_2 dist taut sorry 
  hence "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#},  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @S')))
 ({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, S@S' , atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (S @S')))" using ruls by auto
  then show ?case by auto
qed

lemma strenghten_with_resolvents:
"rules\<^sup>*\<^sup>*(N, D, [],  H \<union> atms_of_mm N \<union> atms_of_mm D) (N + D, {#} ,[], H \<union> atms_of_mm N \<union> atms_of_mm D)"
proof (induction D arbitrary: N H)
  case empty
  then show ?case by auto
next
  case (add x D) note A1 = this(1)
  have A:"rules\<^sup>*\<^sup>* (N, D, [], H  \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D \<union> atms_of_mm (wit_clause `# mset [])) (N + D, {#}, [], H  \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D \<union> atms_of_mm (wit_clause `# mset []))" using A1
    by simp
(*Warum geht der nächste Schritt nicht?*)
  have ruls: "rules\<^sup>*\<^sup>* (N, {#x#} +D, [], H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D  \<union> atms_of_mm (wit_clause `# mset [])) (N + D, {#x#}, [], H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D \<union> atms_of_mm (wit_clause `# mset []))"
    using A apply auto sorry 
  have "rules (N + D, {#x#} + {#}, [],  H  \<union> atms_of x \<union> atms_of_mm (N+D) \<union> atms_of_mm {#} \<union> atms_of_mm (wit_clause `# mset []))
({#x#} + N + D, {#}, [],  H  \<union> atms_of x \<union> atms_of_mm  (N+D) \<union> atms_of_mm {#}  \<union> atms_of_mm (wit_clause `# mset []))" using rules.strenghten
    by (metis union_assoc)
  hence "rules (N + D, {#x#} + {#}, [],  H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D  \<union> atms_of_mm (wit_clause `# mset []))
({#x#} + N + D, {#}, [],  H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D  \<union> atms_of_mm (wit_clause `# mset []))"
    by (simp add: sup_assoc)
  hence "rules\<^sup>*\<^sup>*(N, D + {#x#}, [],  H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D  \<union> atms_of_mm (wit_clause `# mset []))
({#x#} + N + D, {#}, [], H \<union> atms_of x \<union> atms_of_mm N \<union> atms_of_mm D  \<union> atms_of_mm (wit_clause `# mset []))" using ruls by auto
  then show ?case using add_mset
    by (smt (verit, ccfv_SIG) atms_of_ms_insert atms_of_ms_union boolean_algebra_cancel.sup1 image_mset_is_empty_iff mset.simps(1) set_mset_add_mset_insert set_mset_union union_commute union_mset_add_mset_right)
qed

lemma simulation_res_stack_rules:
  assumes "res_stack (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists> S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) (N', R', S', V')"
  using assms
proof (induction rule: res_stack_induct)
  case (1 L N T Z) note L = this(1) and T = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have rul: "res_stack (N, Z) ({#C \<in># resolve_all_on L N. \<not> tautology C#},  Z @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
    using L T A3 by auto
  hence learn1: "(set_mset N) \<Turnstile>ps set_mset({#C \<in># resolve_all_on L N. \<not> tautology C#})" 
    using N_entail_resolvents dist taut by blast 
  have learn2: "\<forall>C \<in># {#C \<in># resolve_all_on L N. \<not> tautology C#}. distinct_mset C"
    using res_stack_distinct rul dist by blast
  have learn:"rules\<^sup>*\<^sup>*(N,  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}) (N, {#C \<in># resolve_all_on L N. \<not> tautology C#}, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#})"
    using learn_resolvents2  dist taut rul by blast
  have streng:"rules\<^sup>*\<^sup>*(N, {#C \<in># resolve_all_on L N. \<not> tautology C#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}) 
(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#} ,[], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#})"  using strenghten_with_resolvents
    by (metis sup.idem)
(*Wie kann ich sagen, dass diese Stacks existieren?*)
  have "\<exists>Q. wit_clause `# mset Q = {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#} \<and>  wit_interp `# mset Q = {#{-L}#}" sorry
  then obtain Q where Q:" wit_clause `# mset Q = {#D \<in># N. (-L \<in># D \<and> L \<notin># D)#} " and Q2:" wit_interp `# mset Q = {#{-L}#}" by auto
  have "\<exists>P. wit_clause `# mset P = {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} \<and>  wit_interp `# mset P = {#{L}#}" sorry
  then obtain P where P:"wit_clause `# mset P = {#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} " and P2:"wit_interp `# mset P = {#{L}#}" by auto
  have sub:"{#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} +{#D \<in># N. (-L \<in># D \<and> L \<notin># D)#} \<subseteq># N"
    by (metis (no_types, lifting) multiset_filter_mono2 multiset_partition subset_mset.add_le_cancel_left)
  hence "atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} = atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm ({#D \<in># N. (L \<in># D \<and> -L \<notin># D)#} +{#D \<in># N. (-L \<in># D \<and> L \<notin># D)#} )"
    by (meson atms_of_ms_mono le_supI1 set_mset_mono sup.orderE)
  hence atm: "atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} = atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (Q @P))" using P Q
    by (simp add: union_commute)
  have learn_fin:"rules\<^sup>*\<^sup>*(N,  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (Q @P))) 
(N, {#C \<in># resolve_all_on L N. \<not> tautology C#}, [], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (Q @P)))" using learn atm
    by presburger 
have streng_fin: "rules\<^sup>*\<^sup>*(N, {#C \<in># resolve_all_on L N. \<not> tautology C#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (Q @P))) 
(N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#} ,[], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (Q @P)))" using streng atm
  by presburger
  have weak: "rules\<^sup>*\<^sup>* (N + {#C \<in># resolve_all_on L N. \<not> tautology C#}, {#} ,[], atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#} \<union> atms_of_mm (wit_clause `# mset (Q @P))) 
({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, Q@P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}  \<union> atms_of_mm (wit_clause `# mset (Q @P)))"
    using weaken_resolvents rul dist taut Q Q2 P P2 by blast
  have fin: "rules\<^sup>*\<^sup>*(N,  {#}, [],  atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}\<union> atms_of_mm (wit_clause `# mset (Q @P))) 
({#C \<in># resolve_all_on L N. \<not> tautology C#}, {#}, Q@P, atms_of_mm N \<union> atms_of_mm {#C \<in># resolve_all_on L N. \<not> tautology C#}  \<union> atms_of_mm (wit_clause `# mset (Q @P)))" using learn_fin streng_fin weak
    by (meson rtranclp_trans)
  hence "\<exists> S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) (({#C \<in># resolve_all_on L N. \<not> tautology C#}), R', S', V')"
    by blast
  then show ?case by auto
qed

lemma rtranclp_simulation_res_stack_rules:
  assumes "res_stack\<^sup>*\<^sup>* (N, Z) (N', Z')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists> S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) (N', R', S', V')"
 using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case using  simulation_res_stack_rules
    by blast
next
  case (step N' Z' N'' Z'') note  A1 = this(1) and A2 = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have rul:"res_stack\<^sup>*\<^sup>* (N, Z) (N', Z')" using assms(1)
    by (simp add: A1) 
  have rul1:"\<exists>S S' V V' R R'. rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')"
    using dist taut A3 by auto
  then obtain S S' V V' R R' where rul2:"rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" by blast
  have dist2: "\<forall>C \<in># N'. distinct_mset C"
    using rtranclp_res_stack_distinct rul dist by blast
  have taut2: "\<forall>C. C\<in># N'  \<longrightarrow>  \<not>tautology C"
    using rtranclp_res_stack_tauto rul taut by blast
(*Warm geht das hier nicht?*)
  have rul4:"\<exists>  S''  V''  R''. rules\<^sup>*\<^sup>* (N', R', S', V') (N'', R'', S'', V'')" 
    using simulation_res_stack_rules A2 dist2 taut2 sorry
  then obtain  S''   V''  R'' where rul3: "rules\<^sup>*\<^sup>* (N', R', S', V') (N'', R'', S'', V'')" by blast
  then show ?case using rul2
    by (meson rtranclp_trans)
qed


lemma equivalence_reconstruction_1:
  assumes  "res_stack\<^sup>*\<^sup>*  (N, []) ({#}, Z')"  and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"
  shows "\<exists> S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) ({#}, R', S', V') \<and> inter_from_stack Z' I = reconstruction_stack S' I"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  have rul:"\<exists>S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) (N, R', [], V')" 
    using rtranclp_simulation_res_stack_rules[of _ "[]" "{#}"] assms by blast
  have A:"inter_from_stack [] I = I "
    by simp 
  have "reconstruction_stack [] I = I" 
    by simp
  hence equal:"inter_from_stack [] I = reconstruction_stack [] I"
    using A by simp
  hence "\<exists>S S' V V' R R'. rules\<^sup>*\<^sup>*(N, R, S, V) (N, R', S', V') \<and> inter_from_stack [] I = reconstruction_stack S' I" using rul
    by meson
  then show ?case 
    by auto
next
  case (step N' Z' N'' Z'') note  A1 = this(1) and A2 = this(2) and A3 = this(3) and dist = this(4) and taut = this(5)
  have "\<exists>S S' V V' R R'. rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V') \<and> inter_from_stack Z' I = reconstruction_stack S' I"
    using dist taut A3 by auto
  have "res_stack\<^sup>*\<^sup>* (N, [])(N'', Z'')"
    using A1 A2 by auto
  hence rul1:"\<exists> S S'' V V'' R R''. rules\<^sup>*\<^sup>*(N, R, S, V) (N'', R'', S'', V'')" 
    using rtranclp_simulation_res_stack_rules dist taut by blast
  show " \<exists>S S'' V V'' R R''. rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'') \<and> inter_from_stack Z'' I = reconstruction_stack S'' I"
  proof (rule ccontr)
    assume ass: "\<not>(\<exists>S S'' V V'' R R''. rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'') \<and> inter_from_stack Z'' I = reconstruction_stack S'' I)"
    then obtain S S'' V V'' R R'' where "\<not>( rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'') \<and> inter_from_stack Z'' I = reconstruction_stack S'' I)" by blast
    hence "\<not>(inter_from_stack Z'' I = reconstruction_stack S'' I) \<or> \<not>( rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V''))" by auto
    show "False"
(*Geht das in die richtige Richtung oder eher nicht so?*)
      proof(cases "\<not>(inter_from_stack Z'' I = reconstruction_stack S'' I)")
        case True note A1 = this(1)
        then show ?thesis sorry
      next
        case False
        then show ?thesis  sorry
      qed
    qed
qed


end