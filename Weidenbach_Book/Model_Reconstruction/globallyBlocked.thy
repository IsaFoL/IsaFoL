theory globallyBlocked
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    modelReconstruction
    inprocessingRulesNeu2
    simulation2
begin

definition globallyBlocked2 :: "'a literal set \<Rightarrow>'a clause \<Rightarrow> 'a clauses \<Rightarrow> bool " where 
"globallyBlocked2 I C F = (consistent_interp I \<longrightarrow>((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># F. (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. tautology ((D-(mset_set(uminus `I))) + C))))"
(*Es sind die gleichen Definitionen, aber die zweite hat besser funktioniert*)
definition globallyBlocked :: "'a literal set \<Rightarrow>'a clause \<Rightarrow> 'a clauses \<Rightarrow> bool " where 
"globallyBlocked I C F = (consistent_interp I \<longrightarrow>((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># F. (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C)))"

lemma globallyBlocked_cons2:
  assumes "globallyBlocked2 I C F" and "consistent_interp I"
  shows "((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># F. (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. tautology ((D-(mset_set(uminus `I))) + C)))"
  using assms unfolding globallyBlocked2_def by auto

lemma globallyBlocked_cons:
  assumes "globallyBlocked I C F" and "consistent_interp I"
  shows "((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># F. (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C))"
  using assms  unfolding globallyBlocked_def by auto

(*Wenn das "\<not>I \<Turnstile> C" weggelassen wird, dann gibt glaube ich ein Gegenbeispiel: I = {l, -k}, N = (l \<or> k), C = (-l \<or> a \<or> -k), J = {-l}*)
lemma compose_model_after_globallyBlocked:
  assumes "I \<Turnstile>m (N-{#C#})" "consistent_interp I" "globallyBlocked J C (N-{#C#})" "consistent_interp J" "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" " atms_of_mm (N-{#C#}) \<subseteq> atm_of ` I" "\<not>I \<Turnstile> C"
  shows "interpr_composition I J  \<Turnstile>m N + {#C#}"
  using assms 
proof-
have 1: "((J \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J)\<noteq> {}) \<and> (set_mset D \<inter> J = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `J))) \<and> -K \<in># C))"
    using globallyBlocked_cons[of J C "(N-{#C#})"] assms(3, 4) by auto
  hence 2:"J \<Turnstile> C" apply auto
    by (metis insert_DiffM true_cls_add_mset)
(*Warum geht der nächste Schritt nicht? *)
   have parts: "(N-{#C#}) = ({#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#} + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I \<noteq> {})#}
 + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I = {})#} + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I \<noteq> {})#})"   sorry
   have "interpr_composition I J \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) = {}) \<and> (set_mset D \<inter> J \<noteq> {})#}" for D
   proof-
     have "J \<Turnstile> D"
       using D apply auto
       by (smt (verit, best) Int_emptyI filter_mset_eq_conv that true_cls_def true_lit_def)
   then show ?thesis unfolding interpr_composition_def by auto 
 qed
  hence part1:"interpr_composition I J \<Turnstile>m {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) = {}) \<and> (set_mset D \<inter> J \<noteq> {})#}"
    using true_cls_mset_def by blast
  have "interpr_composition I J \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) \<noteq> {}) \<and> (set_mset D \<inter> J \<noteq> {})#}" for D
  proof-
     have "J \<Turnstile> D" 
       using D apply auto
       by (smt (verit, best) Int_emptyI filter_mset_eq_conv that true_cls_def true_lit_def)
   then show ?thesis unfolding interpr_composition_def by auto 
 qed
  hence part2:"interpr_composition I J \<Turnstile>m {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) \<noteq> {}) \<and> (set_mset D \<inter> J \<noteq> {})#}"
    using true_cls_mset_def by blast
   have "interpr_composition I J \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) = {}) \<and> (set_mset D \<inter> J = {})#}" for D
   proof-
     have D1:"(set_mset D \<inter> (uminus `J) = {})" and D2:"(set_mset D \<inter> J = {})" 
       using D apply auto
       apply (smt (verit, del_insts) "1" diff_empty disjoint_iff filter_empty_mset filter_mset_eq_conv imageI)
       by (smt (verit, ccfv_SIG) disjoint_iff filter_mset_eq_add_msetD in_diffD insert_DiffM) 
     have "D \<in># (N-{#C#})"
       using D apply auto
       by (meson filter_mset_eq_add_msetD' insert_DiffM that)
     hence "I \<Turnstile>D" 
       using assms(1)  using true_cls_mset_def by blast
     hence "\<exists>k. k \<in> I \<and> k \<in># D" 
       by (smt (verit, ccfv_threshold) Diff_iff UnE mem_Collect_eq true_cls_def true_lit_def) 
     then obtain k where k1: " k \<in> I" and k2:" k \<in># D" 
       by blast
     have "k \<notin> J \<and> k \<notin> (uminus `J)" 
       using D1 D2  k2 by auto
     hence "k \<in> interpr_composition I J" 
       using k1 unfolding interpr_composition_def apply auto
       by (simp add: in_image_uminus_uminus)
     then show ?thesis 
       using k2 unfolding interpr_composition_def
     by (meson true_cls_def true_lit_def) 
 qed
  hence part3:"interpr_composition I J \<Turnstile>m {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J) = {}) \<and> (set_mset D \<inter> J = {})#}"
    using true_cls_mset_def by blast
  have "interpr_composition I J \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J)\<noteq> {}) \<and> (set_mset D \<inter> J = {})#}" for D
  proof-
    have D1:"(set_mset D \<inter> (uminus `J) \<noteq> {})" and D2:"(set_mset D \<inter> J = {})" 
       using D apply auto
       apply (smt (verit, del_insts) "1" diff_empty disjoint_iff filter_empty_mset filter_mset_eq_conv imageI)
       by (smt (verit, ccfv_SIG) disjoint_iff filter_mset_eq_add_msetD in_diffD insert_DiffM) 
    have D3:"D \<in># (N-{#C#})"
       using D apply auto
       by (meson filter_mset_eq_add_msetD' insert_DiffM that)
     hence "I \<Turnstile>D" 
       using assms(1) using true_cls_mset_def by blast
     have "\<exists>K. K \<in># (D-(mset_set(uminus `J))) \<and> -K \<in># C" 
       using 1 D by auto
     then obtain K where K1: "K \<in># (D-(mset_set(uminus `J)))" and K2:" -K \<in># C" 
       by blast
     have dist:"distinct_mset D" using assms(5) D3
       by (meson in_diffD)
     have K3:"K \<in># D" using K1 apply auto
       by (meson in_diffD)
     hence "K \<notin>#  mset_set (uminus ` J)" 
       using K1 dist using distinct_mem_diff_mset[of D K " mset_set (uminus ` J)"] by auto
(*Warum geht der nächste Schritt nicht? *)
     hence "K \<notin> (uminus ` J)"  sorry
     hence notK:"-K \<notin> J" apply auto
       using in_image_uminus_uminus by blast
     have "-K \<notin> I" using K2 assms(7) apply auto
       by (simp add: true_cls_def)
     hence "K \<in> I" using assms(6) D3  apply auto
       by (meson K3 atm_of_in_atm_of_set_in_uminus in_implies_atm_of_on_atms_of_ms in_mono)
     hence "K \<in> interpr_composition I J" 
       using notK unfolding interpr_composition_def by auto
     then show ?thesis 
       using K3 unfolding interpr_composition_def 
       by (meson true_cls_def true_lit_def)
   qed
  hence part4:"interpr_composition I J \<Turnstile>m{#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `J)\<noteq> {}) \<and> (set_mset D \<inter> J = {})#}"
    using true_cls_mset_def by blast
  hence satN:"interpr_composition I J \<Turnstile>m(N-{#C#})" 
    using parts part1 part2 part3
    by (smt (verit, del_insts) filter_mset_add_mset insert_DiffM true_cls_mset_add_mset true_cls_mset_def)
  have "interpr_composition I J \<Turnstile> C" 
    using 2  unfolding interpr_composition_def by auto 
  then show ?thesis 
    using satN  unfolding interpr_composition_def
    by (metis (no_types, lifting) add_mset_add_single add_mset_remove_trivial_If true_cls_mset_add_mset) 
qed

(*Hier gibt es auch zwei sorries, aber es sind die genau gleichen Schritte wie oben, die noch fehlen*)
lemma globallyBlocked_redundancy:  
  assumes "globallyBlocked I C (N-{#C#})" and "consistent_interp I" and  "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C"
  shows "redundancy (N-{#C#}) C I (N-{#C#})"
  using assms 
proof-
  have 1: "((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C))"
    using globallyBlocked_cons[of I C "(N-{#C#})"] assms(1, 2) by auto
  hence 2:"I \<Turnstile> C" apply auto
    by (metis insert_DiffM true_cls_add_mset) 
  have parts: "(N-{#C#}) = ({#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#} + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I \<noteq> {})#}
 + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I = {})#} + {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I \<noteq> {})#})"   sorry
   have "interpr_composition J (interpr_composition (uminus ` set_mset C) I ) \<Turnstile>m (N-{#C#})" if A:"consistent_interp J " 
    and B: "interpr_composition J (uminus ` set_mset C) \<Turnstile>m (N-{#C#})" for J
  proof-
   have "interpr_composition J (interpr_composition (uminus ` set_mset C) (I)) \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I \<noteq> {})#}" for D
   proof-
     have "I \<Turnstile> D"
       using D apply auto
       by (smt (verit, best) Int_emptyI filter_mset_eq_conv that true_cls_def true_lit_def)
   then show ?thesis unfolding interpr_composition_def by auto 
 qed note part1 = this
  have "interpr_composition J (interpr_composition (uminus ` set_mset C) (I)) \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) \<noteq> {}) \<and> (set_mset D \<inter> I \<noteq> {})#}" for D
   proof-
     have "I \<Turnstile> D" 
       using D apply auto
       by (smt (verit, best) Int_emptyI filter_mset_eq_conv that true_cls_def true_lit_def)
   then show ?thesis unfolding interpr_composition_def by auto 
 qed note part2 = this
   have "interpr_composition J (interpr_composition (uminus ` set_mset C) (I)) \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I) = {}) \<and> (set_mset D \<inter> I = {})#}" for D
   proof-
     have D1:"(set_mset D \<inter> (uminus `I) = {})" and D2:"(set_mset D \<inter> I = {})" 
       using D apply auto
       apply (smt (verit, del_insts) "1" diff_empty disjoint_iff filter_empty_mset filter_mset_eq_conv imageI)
       by (smt (verit, ccfv_SIG) disjoint_iff filter_mset_eq_add_msetD in_diffD insert_DiffM) 
     have "D \<in># (N-{#C#})"
       using D apply auto
       by (meson filter_mset_eq_add_msetD' insert_DiffM that)
     hence "interpr_composition J (uminus ` set_mset C) \<Turnstile>D" 
       using B apply auto using true_cls_mset_def by blast
     hence "\<exists>k. k \<in> interpr_composition J (uminus ` set_mset C) \<and> k \<in># D" 
       unfolding interpr_composition_def apply auto
       by (smt (verit, ccfv_threshold) Diff_iff UnE mem_Collect_eq true_cls_def true_lit_def) 
     then obtain k where k1: " k \<in> interpr_composition J (uminus ` set_mset C)" and k2:" k \<in># D" 
       by blast
     have "k \<notin> I \<and> k \<notin> (uminus `I)" 
       using D1 D2  k2 by auto
     hence "k \<in> interpr_composition J (interpr_composition (uminus ` set_mset C) (I))" 
       using k1 unfolding interpr_composition_def apply auto
       by (simp add: in_image_uminus_uminus)
     then show ?thesis 
       using k2 unfolding interpr_composition_def
     by (meson true_cls_def true_lit_def) 
 qed note part3 = this
  have "interpr_composition J (interpr_composition (uminus ` set_mset C) (I)) \<Turnstile> D" if D: "D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}" for D
  proof-
    have D1:"(set_mset D \<inter> (uminus `I) \<noteq> {})" and D2:"(set_mset D \<inter> I = {})" 
       using D apply auto
       apply (smt (verit, del_insts) "1" diff_empty disjoint_iff filter_empty_mset filter_mset_eq_conv imageI)
       by (smt (verit, ccfv_SIG) disjoint_iff filter_mset_eq_add_msetD in_diffD insert_DiffM) 
    have D3:"D \<in># (N-{#C#})"
       using D apply auto
       by (meson filter_mset_eq_add_msetD' insert_DiffM that)
     hence "interpr_composition J (uminus ` set_mset C) \<Turnstile>D" 
       using B apply auto using true_cls_mset_def by blast
     have "\<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C" 
       using 1 D by auto
     then obtain K where K1: "K \<in># (D-(mset_set(uminus `I)))" and K2:" -K \<in># C" 
       by blast
    have dist:"distinct_mset D" using assms(3) D3
       by (meson in_diffD)
     have K3:"K \<in># D" using K1 apply auto
       by (meson in_diffD)
     hence "K \<notin>#  mset_set (uminus ` I)" 
       using K1 dist using distinct_mem_diff_mset[of D K " mset_set (uminus ` I)"] by auto
     hence "K \<notin> (uminus `I)" using K1 D1 apply auto  sorry
     hence notK:"-K \<notin> I" apply auto
       using in_image_uminus_uminus by blast
     have "K \<in> (uminus ` set_mset C)"
       using K2 apply auto
       by (simp add: in_image_uminus_uminus)
     hence "K \<in> interpr_composition J (uminus ` set_mset C)" 
       unfolding interpr_composition_def by auto
     hence "K \<in> interpr_composition J (interpr_composition (uminus ` set_mset C) (I))" 
       using notK unfolding interpr_composition_def by auto
    then show ?thesis using K3 unfolding interpr_composition_def
     by (meson true_cls_def true_lit_def)
 qed note part4 = this
 then show ?thesis using parts part1 part2 part3
   by (smt (verit, ccfv_SIG) true_cls_mset_def union_iff)
qed
  then show ?thesis 
    unfolding redundancy_def by auto
qed

(*Das ist das gleiche Lemma wie weiter unten, aber mit \<forall> und ich wusste nicht wie ich das richtig formulieren kann, bzw. welche Beweismethode dann am besten ist*)
lemma globallyBlocked_simulation2: 
  assumes "globallyBlocked I C (N-{#C#})" and "consistent_interp I" and "atm_of ` I \<subseteq> V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)"  and C1:"C \<in># N" and  "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C"
  shows "\<forall>S'. rules\<^sup>*\<^sup>*(N, R, S, V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
          ((N-{#C#}), R, S@S', V \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) \<and>
          List.member S' (Witness I C)" (*{#C#} \<subseteq># wit_clause `# mset S' \<and> (I \<in># (wit_interp `# mset S'))*)
  using assms
proof -
  have 1: "((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C))"
    using globallyBlocked_cons[of I C "(N-{#C#})"] assms(1, 2) by auto
  hence 2:"I \<Turnstile> C" apply auto
    by (metis insert_DiffM true_cls_add_mset) 
  have red: "redundancy (N-{#C#}) C I (N-{#C#})" 
    using globallyBlocked_redundancy[of I C N] assms(1, 2, 5) by auto
  have eq1: "atms_of C \<union> atms_of_mm (remove1_mset C N) = atms_of_mm (N)" sorry
  have sub: "atm_of ` I \<subseteq> V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)" 
    using eq1 assms(3) by auto
  have eq2: "remove1_mset C N + {#C#} = N" apply auto sorry
  have "\<forall>S'. rules\<^sup>*\<^sup>*(N, R, S, V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
          ((N-{#C#}), R, S@S', V \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) \<and>
          List.member S' (Witness I C)" for S'
  proof-
  have "rules (remove1_mset C N + {#C#}, R, S, V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
     (remove1_mset C N, R, S @ [Witness I C], V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
   using weakenp[of I C "(N-{#C#})" V R S] 2 red assms(2) sub by auto
  hence rul:"rules(N, R, S, V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))((N-{#C#}), R, S@[Witness I C], V \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    using eq1 eq2 apply auto
    by (simp add: sup.assoc)
  (*have wit1:"{#C#} \<subseteq># wit_clause `# mset (S@[Witness I C])"
    by auto
  have wit2: "(I \<in># (wit_interp `# mset  (S@[Witness I C])))" 
    by auto*)
  then show ?thesis   sorry
qed
  then show ?thesis
    by blast
qed


lemma globallyBlocked_simulation: 
  assumes "globallyBlocked I C (N-{#C#})" and "consistent_interp I" and "atm_of ` I \<subseteq> V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)" and C1:"C \<in># N"  and  "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C"
  shows "\<exists>S'. rules\<^sup>*\<^sup>*(N, R, S, V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
          ((N-{#C#}), R, S@S', V \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) \<and>
           wit_clause `# mset S' = {#C#} \<and> (\<forall>I'\<in># (wit_interp `# mset S'). I' = I)"
  using assms
proof -
  have 1: "((I \<inter> set_mset C \<noteq> {}) \<and> (\<forall>D \<in># {#D \<in># (N-{#C#}). (set_mset D \<inter> (uminus `I)\<noteq> {}) \<and> (set_mset D \<inter> I = {})#}. \<exists>K. K \<in># (D-(mset_set(uminus `I))) \<and> -K \<in># C))"
    using globallyBlocked_cons[of I C "(N-{#C#})"] assms(1, 2) by auto
  hence 2:"I \<Turnstile> C" apply auto
    by (metis insert_DiffM true_cls_add_mset) 
  have red: "redundancy (N-{#C#}) C I (N-{#C#})" 
    using globallyBlocked_redundancy[of I C N] assms(1, 2, 5) by auto
  have eq1: "atms_of C \<union> atms_of_mm (remove1_mset C N) = atms_of_mm (N)" using C1
    by (metis atms_of_ms_insert insert_DiffM set_mset_add_mset_insert)
  have sub: "atm_of ` I \<subseteq> V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)" 
    using eq1 assms(3) by auto
  have eq2: "(remove1_mset C N) + {#C#} = N" 
    using C1 by auto
  have "rules (remove1_mset C N + {#C#}, R, S, V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
     (remove1_mset C N, R, S @ [Witness I C], V \<union> atms_of C \<union> atms_of_mm (remove1_mset C N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
   using weakenp[of I C "(N-{#C#})" V R S] 2 red assms(2) sub by auto
  hence rul:"rules(N, R, S, V \<union> atms_of_mm (N) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))((N-{#C#}), R, S@[Witness I C], V \<union> atms_of_mm (N ) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    using eq1 eq2 apply auto
    by (simp add: sup.assoc)
  have wit1:" wit_clause `# mset[Witness I C] = {#C#}"
    by auto
  have wit2: "(\<forall>I'\<in># (wit_interp `# mset [Witness I C]). I' = I)" 
    by auto
  then show ?thesis
    using rul wit1 by auto
qed
end 