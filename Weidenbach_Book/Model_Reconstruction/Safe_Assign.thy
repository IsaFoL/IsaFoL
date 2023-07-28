theory Safe_Assign
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    Model_Reconstruction
    Inprocessing_Rules
    Simulation
    Autarky
begin

definition safe_assign :: "'a literal \<Rightarrow>'a clauses \<Rightarrow>'a clauses \<Rightarrow> bool" where
  "safe_assign v F Fv =
    (\<forall>I. consistent_interp I \<and>
       (\<forall>C \<in># Fv. -v \<in># C) \<and> (\<forall>C \<in># F. -v \<notin># C) \<and>
       interpr_composition I {v} \<Turnstile>m  (F + Fv) \<longrightarrow> interpr_composition I {-v} \<Turnstile>m (F + Fv))"


lemma safe_assign_notv:
  assumes "safe_assign v F Fv" and "consistent_interp I" and "\<forall>C \<in># Fv. -v \<in># C" and "(\<forall>C \<in># F. -v \<notin># C)" and "interpr_composition I {v} \<Turnstile>m  (F + Fv)"
  shows "interpr_composition I {-v} \<Turnstile>m (F + Fv)"
  using assms unfolding safe_assign_def by auto


lemma compose_model_after_safe_assign:
  assumes "I \<Turnstile>m N" "consistent_interp I" "safe_assign v N Nv" "\<forall>C \<in># Nv. -v \<in># C" "\<forall>C \<in># N. -v \<notin># C"
  shows "interpr_composition I {-v} \<Turnstile>m (N + Nv)"
  using assms
proof -
  have 1:"interpr_composition I {-v} \<Turnstile>m (N + Nv)" if A:"interpr_composition I {v} \<Turnstile>m  (N + Nv)"
    using safe_assign_notv[of v N Nv I] assms(2, 3, 4, 5) A by auto
  hence 3:"interpr_composition I {-v} \<Turnstile> C" if A:"interpr_composition I {v} \<Turnstile>m  (N + Nv)" and B: "C \<in># (N + Nv)" for C using A B
    using true_cls_mset_def by blast
      (*Der nächste Schritt gilt eher nicht? *)
  hence 2:"interpr_composition I {-v} \<Turnstile> C" if A:"interpr_composition I {v} \<Turnstile>  C" and B: "C \<in># (N + Nv)" for C using A B apply auto sorry
  have "{-v} \<Turnstile>m Nv" using assms(4)
    by (metis insert_DiffM singletonI true_cls_add_mset true_cls_mset_def)
  hence Nv: "interpr_composition I {-v} \<Turnstile>m  Nv"
    unfolding interpr_composition_def  apply auto
    using true_cls_mset_increasing_r by fastforce
  have "interpr_composition I {-v} \<Turnstile> C" if C: "C \<in># N" for C
  proof(cases "v \<in># C")
    case True
    show ?thesis
    proof (rule ccontr)
      assume ass:"\<not>I \<^bold>\<circ> {- v} \<Turnstile> C"
      have nSat:"\<not> interpr_composition I {-v} \<Turnstile>m (N + Nv)" 
        using ass C  unfolding interpr_composition_def apply auto
        using true_cls_mset_def by blast
      have T1:"I \<Turnstile> C" using assms(1) C
        using true_cls_mset_def by blast
      hence "v \<in> I" using ass True unfolding interpr_composition_def apply auto
        by (metis (mono_tags, lifting) Collect_empty_eq Diff_empty true_cls_insert_l)
      hence "I = interpr_composition I {v}" 
        using assms(2) unfolding interpr_composition_def apply auto
        using consistent_interp_def by blast
      hence "interpr_composition I {v} \<Turnstile> C" 
        using T1 by auto
      then show "False"
        using 2[of C] C nSat unfolding interpr_composition_def
        by (metis ass interpr_composition_def union_iff) 
    qed
  next
    case False 
    have F1:"I \<Turnstile> C" using assms(1) C
      using true_cls_mset_def by blast
    have "-v \<notin># C"
      using C assms(5) by auto
    then show ?thesis using False F1 unfolding interpr_composition_def apply auto
      by (smt (verit) Diff_iff insert_iff mem_Collect_eq true_cls_def true_lit_def) 
  qed
  then show ?thesis using Nv
    using true_cls_mset_def by auto
qed

(*Bei dem lemma fehlen ein paar sorries, aber ich weiß sonst nicht so richtig wie man das zeigen könnte?*)
lemma safe_assign_redundancy2:
  assumes "safe_assign v N Nv" and "\<forall>C \<in># Nv. -v \<in># C" and  "\<forall>C \<in># N. -v \<notin># C" and "N' \<subseteq># Nv" and "x \<in># N'"
  shows "redundancy ((N' - {#x#}) + N) x {-v} ((N' - {#x#}) + N)"
  using assms
proof-  
  have 1:"interpr_composition I {-v} \<Turnstile>m (N + Nv)" if  A:"consistent_interp I "  and B:"interpr_composition I {v} \<Turnstile>m  (N + Nv)" for I
    using safe_assign_notv[of v N Nv I] assms(1, 2, 3) A B by auto
  have "({-v} \<Turnstile>m Nv)"
    using  assms( 2)
    by (metis insert_DiffM singletonI true_cls_add_mset true_cls_mset_def)
  hence 2:"{-v} \<Turnstile>m (N' - {#x#})" using assms(4)
    by (meson set_mset_mono subseteq_remove1 true_cls_mset_mono)
  have "(interpr_composition I (interpr_composition (uminus ` set_mset x) {-v})) \<Turnstile>m ((N' - {#x#}) + N)" if A:"consistent_interp I " 
    and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m ((N' - {#x#}) + N)"  for I 
  proof-
    have "(interpr_composition I (interpr_composition (uminus ` set_mset x) {-v})) \<Turnstile> C" if C: "C \<in># N" for C
    proof-
      have "interpr_composition I (uminus ` set_mset x) \<Turnstile> C" 
        using B C unfolding interpr_composition_def apply auto
        using true_cls_mset_def by blast
          (*Die nächsten zwei Schritte gehen auch nur wenn es keine Tautologien sind*)
      have cons: "consistent_interp (I \<^bold>\<circ> uminus ` set_mset x)" sorry
      have eq:"uminus ` set_mset x \<^bold>\<circ> {v} = uminus ` set_mset x" sorry
          (*Das geht eigentlich glaube ich nicht*)
      hence Ixv:  "I \<^bold>\<circ> uminus ` set_mset x \<^bold>\<circ> {v} \<Turnstile>m (Nv + N)"
        sorry
      have "(interpr_composition I (interpr_composition (uminus ` set_mset x) {-v})) \<Turnstile> C" 
        using 1[of  "interpr_composition I (uminus ` set_mset x)"] C cons Ixv apply auto
        by (simp add: interpr_composition_assoc true_cls_mset_def)
      then show ?thesis
        by auto
    qed
    then show ?thesis
      using 2 unfolding interpr_composition_def  apply auto
      using true_cls_mset_increasing_r apply fastforce
      using true_cls_mset_def by blast
  qed
  then show ?thesis
    unfolding redundancy_def by auto
qed


(*Die Variante von dem Lemma davor ist vermutlich die bessere*)
lemma safe_assign_redundancy:  
  assumes "safe_assign v N (Nv + {#x#})" and "\<forall>C \<in># (Nv + {#x#}). -v \<in># C" and "\<forall>C \<in># N. -v \<notin># C"
  shows "redundancy (N + Nv) x {-v} (N + Nv)"
  using assms 
proof-
  have 1: "({-v} \<Turnstile>m Nv + {#x#})"
    using  assms( 2) apply auto
    apply (metis insert_DiffM singletonI true_cls_add_mset)
    by (metis insert_DiffM singletonI true_cls_add_mset true_cls_mset_def)
  have "(\<forall>C \<in># N.  \<not>{-v} \<Turnstile> C)" using assms(3) apply auto
    by (simp add: true_cls_def)
  have "v  \<in> uminus ` set_mset x" using assms(2) apply auto
    using in_image_uminus_uminus by blast
      (*Gilt eigentlich nur wenn x keine Tautologie ist*)
  hence eq:"uminus ` set_mset x \<^bold>\<circ> {v} = uminus ` set_mset x" unfolding interpr_composition_def  apply auto sorry
  have "(interpr_composition I (interpr_composition (uminus ` set_mset x) {-v})) \<Turnstile>m  (N+Nv)" if A:"consistent_interp I " 
    and B: "interpr_composition I (uminus ` set_mset x) \<Turnstile>m (N + Nv)"  for I
  proof-
    (*Gilt auch nur wenn x keine Tautologie ist*)
    have cons:" consistent_interp (I \<^bold>\<circ> uminus ` set_mset x)"
      using A unfolding interpr_composition_def  apply auto sorry
        (*Ich weiß nicht ob das so stimmt?*)
    have safe1: "safe_assign v N Nv" 
      using assms(1)  unfolding safe_assign_def interpr_composition_def  apply auto  sorry
    have in1: "\<forall>C\<in>#Nv. - v \<in># C" using assms(2) by auto
    have " I \<^bold>\<circ> uminus ` set_mset x \<^bold>\<circ> {v} \<Turnstile>m N + Nv"
      using eq B unfolding interpr_composition_def  apply auto
      apply (smt (z3) Collect_empty_eq Diff_empty Un_commute Un_insert_left cons consistent_interp_insert_iff insertI1 insert_absorb interpr_composition_def)
      by (smt (z3) Diff_empty Un_insert_right cons consistent_interp_insert_iff empty_Collect_eq insertI1 insert_absorb interpr_composition_def)
    then show ?thesis 
      using safe_assign_notv[of v N Nv "interpr_composition I (uminus ` set_mset x)"] cons safe1 in1 assms(3) apply auto
      apply (simp add: interpr_composition_assoc)
      by (simp add: interpr_composition_assoc)
  qed
  then show ?thesis
    unfolding redundancy_def by auto
qed

lemma safe_assign_simulation: 
  assumes "safe_assign v N Nv" and "\<forall>C \<in># Nv. -v \<in># C" and  "\<forall>C \<in># N. -v \<notin># C"
  shows "\<exists>S'. rules\<^sup>*\<^sup>*(N + Nv, R, S, V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
          (N, R, S@S', V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) \<and>
           wit_clause `# mset S' = Nv \<and> (\<forall>I'\<in># (wit_interp `# mset S'). I' = {-v})"
  using assms
proof - 
  obtain LNv where [simp]: \<open>mset LNv = Nv\<close> 
    by (metis list_of_mset_exi)
  have "{-v} \<Turnstile>m Nv" 
    using assms(2)
    by (metis insert_DiffM singletonI true_cls_add_mset true_cls_mset_def)
  hence LNv_sat:"{-v} \<Turnstile>m mset LNv"
    by simp
  have "rules\<^sup>*\<^sup>*(N + Nv, R, S, V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)) 
(N + mset(drop i LNv), R, S@map (\<lambda>C. Witness {-v} C) (take i LNv), V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))"
    for i
  proof (induction i)
    case 0
    then show ?case by auto
  next
    case (Suc i) note rul1 = this
    consider 
      (1) \<open>Suc i \<le> length LNv\<close> |
      (boring) \<open>Suc i>length LNv\<close>
      by linarith
    then show ?case
    proof cases
      case boring
      then have \<open>take ( i)LNv = LNv\<close> \<open>mset (drop (Suc i) LNv) = {#}\<close>
        by simp_all
      then show ?thesis
        using Suc by (auto simp:  ac_simps)
    next
      case 1
      have [simp]: \<open>mset (drop i LNv) = add_mset (LNv!i) (mset (drop (Suc i) LNv))\<close>
        by (metis "1" Cons_nth_drop_Suc Suc_le_lessD mset.simps(2))
      have h1:"mset (drop (Suc i) LNv) =  (remove1_mset (LNv ! i)  (mset (drop i LNv))) "
        by simp
      have Ii_sat:"{-v} \<Turnstile> LNv ! i" using LNv_sat
        by (meson "1" Suc_le_eq nth_mem_mset true_cls_mset_def)
          (*Der nächste Schritt fehlt, ich weiß aber gar nicht ob der so stimmt*)
      have safe1: "safe_assign v N (mset (drop (Suc i) LNv) + {#LNv ! i#})" using assms(1) unfolding safe_assign_def apply auto
        apply (metis (no_types, lifting) Ii_sat interpr_composition_def true_cls_union_increase') sorry
      have red: "redundancy (mset (drop (Suc i) LNv) + N) (LNv ! i) {-v} (mset (drop (Suc i) LNv) + N)" 
        using safe_assign_redundancy[of v N "mset (drop (Suc i) LNv)" "LNv ! i"] safe1 assms(2, 3) apply auto
        by (metis "1" Suc_le_lessD \<open>mset LNv = Nv\<close> add.commute in_set_conv_nth in_set_dropD set_mset_mset)
      have Na1:"({#LNv ! i#} + (mset (drop (Suc i) LNv)) + (mset((take i LNv)))) = Nv"
        by (metis \<open>mset (drop i LNv) = add_mset (LNv ! i) (mset (drop (Suc i) LNv))\<close> \<open>mset LNv = Nv\<close> add_mset atd_lem union_code union_commute)
      have sub: "atm_of ` {-v} \<subseteq> V \<union> atms_of (LNv ! i) \<union> atms_of_mm (mset (drop (Suc i) LNv) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {-v}) (take i LNv)))"
        using assms(2) apply auto
        by (metis "1" Suc_le_lessD \<open>mset LNv = Nv\<close> atm_of_notin_atms_of_iff nth_mem_mset)
      have rul2: "rules (mset (drop (Suc i) LNv) + N + {#LNv ! i#}, R, S @ map (Witness {-v}) (take i LNv),
 V \<union> atms_of (LNv ! i) \<union> atms_of_mm (mset (drop (Suc i) LNv) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {-v}) (take i LNv))))
   (mset (drop (Suc i) LNv) + N, R, (S @ map (Witness {-v}) (take i LNv)) @ [Witness {-v} (LNv ! i)], 
V \<union> atms_of (LNv ! i) \<union> atms_of_mm (mset (drop (Suc i) LNv) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {-v}) (take i LNv))))"
        using weakenp[of "{-v}" "(LNv ! i)" " (mset (drop (Suc i) LNv))+ N" V R "S @ map (Witness {-v}) (take i LNv)"]  using Ii_sat red sub assms(2) by auto
      have h2: "(V \<union> atms_of (LNv ! i) \<union> atms_of_mm (mset (drop (Suc i) LNv) + N) \<union> atms_of_mm R \<union> atms_of_mm (wit_clause `# mset (S @ map (Witness {-v}) (take i LNv))) 
               = (V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S)))" using Na1 by auto
      have h3: "map (Witness {-v}) (take i LNv) @ [Witness {-v} (LNv ! i)] = map (Witness {-v}) (take (Suc i) LNv)"
        by (simp add: "1" Suc_le_lessD take_Suc_conv_app_nth)
      have rul3:"rules (N + mset (drop i LNv), R, S @ map (Witness {-v}) (take i LNv), V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
                  (N + mset (drop (Suc i) LNv), R, S @ map (Witness {-v}) (take (Suc i) LNv), V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
        using h1 h2 h3 rul2 apply auto
        by (simp add: add.commute)
      then show ?thesis 
        using rul1 by auto
    qed
  qed note ag = this
  have "mset (drop (length LNv) LNv) = {#}" and "(take (length LNv) LNv) = LNv"
    by auto
  then have 2: "rules\<^sup>*\<^sup>*(N + Nv, R, S, V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))
                       (N, R, S@map (\<lambda>C. Witness {-v} C) LNv, V \<union> atms_of_mm (N + Nv) \<union> atms_of_mm R \<union> atms_of_ms (wit_clause ` set S))" 
    using ag[of "length LNv" ] by auto
  have wit_Na:"wit_clause `# mset (map (\<lambda>C. Witness {-v} C) LNv) = Nv" 
    by simp
  have int_Na:"(\<forall>I'\<in># (wit_interp `# mset (map (\<lambda>C. Witness {-v} C) LNv)). I' = {-v})" 
    by auto
  then show ?thesis 
    using 2 wit_Na by blast
qed



end