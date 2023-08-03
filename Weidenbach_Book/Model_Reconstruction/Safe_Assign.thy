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


lemma safe_assign_rules:
  assumes safe: \<open>safe_assign v F Fv\<close> and eq: \<open>F+Fv = N + R\<close> and nempty: \<open>Fv \<noteq> {#}\<close>
    "consistent_interp I" and Fv: "\<forall>C \<in># Fv. -v \<in># C" and "(\<forall>C \<in># F. -v \<notin># C)"
  shows \<open>rules (N, R, S, V \<union> atms_of {#-v#} \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) 
       (add_mset {#-v#} N, (R), S, V \<union> atms_of {#-v#} \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))\<close>
proof (rule rules.intros(6))
  show \<open>distinct_mset {#-v#}\<close>
    by auto
  show \<open>satisfiable (set_mset (N + R)) \<longrightarrow>  satisfiable (set_mset (add_mset {#-v#} (N + R)))\<close>
  proof
    assume \<open>satisfiable (set_mset (N + R))\<close>
    then obtain I where
      cons: \<open>consistent_interp I\<close> and
      I: \<open>I \<Turnstile>sm N+R\<close> and
      tot: \<open>total_over_m I (set_mset (N+R))\<close>
      unfolding satisfiable_def by auto
    consider
      \<open>v \<in> I\<close> | 
      \<open>-v \<in> I\<close>
      using tot Fv nempty unfolding eq[symmetric] by (cases Fv; cases v) (auto dest!: multi_member_split)
    then show \<open>satisfiable (set_mset (add_mset {#-v#} (N + R)))\<close>
    proof cases
      case 2
      then have \<open>I \<Turnstile>sm add_mset {#-v#} N+R\<close>
        using I by auto
      then show ?thesis using cons by simp
    next
      case 1
      then have \<open>interpr_composition I {v} = I\<close>
        using cons by (auto simp: interpr_composition_def consistent_interp_def)
      then have \<open>interpr_composition I {-v} \<Turnstile>sm add_mset {#-v#} N+R\<close>
        using assms I unfolding safe_assign_def unfolding eq
        by (simp add: cons interpr_composition_def true_cls_mset_def true_clss_def)
      moreover have \<open>consistent_interp (interpr_composition I {-v})\<close>
        using cons by (auto simp: interpr_composition_def consistent_interp_def)
      ultimately show ?thesis using cons by simp
    qed
  qed
qed

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


end