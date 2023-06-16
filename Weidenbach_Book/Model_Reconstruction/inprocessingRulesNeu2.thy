(* Title: Inprocessing Rules
   Author: Katharina Wagner
*)
theory inprocessingRulesNeu2
  imports Entailment_Definition.Partial_Herbrand_Interpretation
          Entailment_Definition.Partial_Annotated_Herbrand_Interpretation

begin

datatype 'a witness = 
is_wit: Witness (wit_interp: "'a partial_interp") (wit_clause: "'a clause")

type_synonym 'a stackWit = "'a witness list"

text \<open>
In the following defintion interpr_composition, I is from a [Witness I C], while I' is the 
existing, given interpretation.
\<close>
definition interpr_composition :: "'a literal set \<Rightarrow> 'a literal set \<Rightarrow>'a literal set " where
"interpr_composition I' I = ((I' - {L \<in> I'. -L \<in> I}) \<union> I) "

notation interpr_composition (infixl "\<^bold>\<circ>" 80)

definition redundancy :: "'a clauses \<Rightarrow> 'a clause \<Rightarrow> 'a literal set \<Rightarrow> 'a clauses \<Rightarrow> bool" where
"redundancy F C \<omega> F' = (\<forall>I. consistent_interp I \<longrightarrow>interpr_composition I (uminus ` set_mset C) \<Turnstile>m F \<longrightarrow>
     (interpr_composition I (interpr_composition (uminus ` set_mset C) \<omega>)) \<Turnstile>m F' )"

lemma redundancyD:
  assumes "redundancy F C \<omega> F'" and  "consistent_interp I" and "interpr_composition I (uminus ` set_mset C) \<Turnstile>m F"
  shows "(interpr_composition I (interpr_composition (uminus ` set_mset C) \<omega>)) \<Turnstile>m F'"
  using assms unfolding redundancy_def by blast

notation (output) redundancy ("_ \<^bold>\<and> _ \<equiv>\<^sub>s\<^sub>a\<^sub>t\<^bsub>_\<^esub> _")

(*This is the original definition of the paper.*)
definition redundancy_old :: "'a clauses \<Rightarrow> 'a clause \<Rightarrow> 'a literal set \<Rightarrow> 'a clauses \<Rightarrow> bool" where
"redundancy_old F C \<omega> F' = (\<forall>I. consistent_interp I \<longrightarrow>interpr_composition I (uminus ` set_mset C) \<Turnstile>m F \<longrightarrow>
     (interpr_composition I \<omega>) \<Turnstile>m F')"

lemma redundancyD_old:
  assumes "redundancy_old F C \<omega> F'" and  "consistent_interp I" and "interpr_composition I (uminus ` set_mset C) \<Turnstile>m F"
  shows "(interpr_composition I  \<omega>) \<Turnstile>m F'"
  using assms unfolding redundancy_old_def by blast


inductive rules :: "'v clauses \<times> 'v clauses \<times>  'v stackWit \<times> 'v set \<Rightarrow> 'v clauses \<times> 'v clauses \<times> 'v stackWit \<times> 'v set \<Rightarrow> bool" where
drop: 
  "rules (({#C#}+N), R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (N, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
if "set_mset N \<Turnstile>p C"|
strenghten:
  "rules (N, ({#C#}+R), S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (({#C#}+N), R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))" |
weakenp:
  "rules (N+{#C#}, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (N, R, (S @ [Witness I C]), V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
if "I \<Turnstile> C" and "atm_of ` I \<subseteq> atms_of C" and "redundancy N C I N" and "consistent_interp I " |
forget:
   "rules (N, ({#C#}+R), S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (N, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))" |
learn_minus:
  "rules (N, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S)) (N, ({#C#}+R), S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
if "(set_mset (N) \<union> set_mset(R)) \<Turnstile>p C" and "distinct_mset C"

fun reconstruction_step :: "'v witness \<Rightarrow> 'v partial_interp \<Rightarrow> 'v partial_interp " where
"reconstruction_step (Witness I C) I' = (if I' \<Turnstile> C then I' else  interpr_composition I' I)"

abbreviation reconstruction_stack :: "'v witness list \<Rightarrow> 'v partial_interp \<Rightarrow> 'v partial_interp" where
"reconstruction_stack xs I \<equiv> foldr reconstruction_step xs I"

lemmas rules_induct = rules.induct[split_format(complete)]

lemma irredundant_entail_redundant:
 assumes"rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
 shows "N' + wit_clause `# mset S' \<Turnstile>psm R'"
  using assms apply (induction rule: rules_induct)
  apply auto
  apply (smt (verit, ccfv_SIG) Un_insert_right sup.left_idem sup_bot_right sup_commute true_clss_clss_generalise_true_clss_clss true_clss_clss_true_clss_cls)
  using true_clss_clss_generalise_true_clss_clss true_clss_clss_true_clss_cls by force 

lemma irredundant_entail_redundant_before:
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "N' + wit_clause `# mset S' \<Turnstile>psm R"
  using assms apply (induction rule: rules_induct)
  apply auto
  by (smt (verit) insert_def singleton_conv sup.idem sup_commute sup_left_commute true_clss_clss_generalise_true_clss_clss true_clss_clss_true_clss_cls) 

lemma irredundant_entail_redundant_before2:
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "N + wit_clause `# mset S' \<Turnstile>psm R'"
  using assms apply (induction rule: rules_induct)
  apply auto
  by (smt (verit, best) sup.idem sup_commute sup_left_commute true_clss_clss_generalise_true_clss_clss true_clss_clss_true_clss_cls)

lemmas rtranclp_induct4 = rtranclp_induct[of r \<open>(_, _, _, _)\<close> \<open>(_, _, _, _)\<close>, split_format(complete),
  case_names refl step]

lemma rtranclp_irredundant_entail_redundant:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "N' + wit_clause `# mset S' \<Turnstile>psm R'"
  using assms 
proof (induction rule: rtranclp_induct4)
  case refl
  then show ?case using assms(2) by auto
next
  case (step N' R' S' V' N'' R'' S'' V'') note  A1 = this(1) and A2 = this(2) and A3 = this(3) and A4 = this(4)
  have "N' + wit_clause `# mset S' \<Turnstile>psm R'" 
    using A3 A4 by auto
  hence "N'' + wit_clause `# mset S'' \<Turnstile>psm R''" 
    using A2 irredundant_entail_redundant by auto
  then show ?case by auto
qed

text \<open>
The proof assumes that C is not a tautology, due to the existence
of a countermodel.
Moreover, the proof is not correct for partial models (due to tautologies).
\<close>


experiment begin
lemma proposition1: 
  fixes A L
  defines
    \<open>L \<equiv> Pos (1::nat)\<close> and
    \<open>A \<equiv> Pos (2::nat)\<close> and
    \<open>N \<equiv> {#{#L,A#}#}\<close> and
    \<open>C \<equiv> {#-L,-A#}\<close> and
    \<open>\<tau> \<equiv> {L}\<close>and
    \<open>\<omega> \<equiv> {-L}\<close>
  shows 
   red: "redundancy N C \<omega> N" and \<tau>: "\<tau> \<Turnstile>m N" and "\<not>\<tau> \<Turnstile> C" and cons3:"consistent_interp \<tau>"
    and "consistent_interp \<omega>" and \<omega>: "\<omega> \<Turnstile> C" and "atm_of ` \<omega> \<subseteq> atms_of C"  and
    "\<not>interpr_composition \<tau> \<omega> \<Turnstile>m N+{#C#}" 
  unfolding assms
  by (auto simp: interpr_composition_def redundancy_def)
end


lemma interpr_composition_assoc: \<open>a \<^bold>\<circ> (b \<^bold>\<circ> c) = a \<^bold>\<circ> b \<^bold>\<circ> c\<close>
  by (auto simp: interpr_composition_def)

lemma proposition1: 
  assumes red: "redundancy N C \<omega> N" and \<tau>: "\<tau> \<Turnstile>m N" and "\<not>\<tau> \<Turnstile> C" and cons3:"consistent_interp \<tau>"
  and "consistent_interp \<omega>" and \<omega>: "\<omega> \<Turnstile> C" and "atm_of ` \<omega> \<subseteq> atms_of C" and
    "total_over_set \<tau> (atms_of_mm (add_mset C N))"
  shows "interpr_composition \<tau> \<omega> \<Turnstile>m N+{#C#}" 
  using assms
proof-
  let ?\<alpha> = \<open>image uminus (set_mset C)\<close>  
  have C:"interpr_composition \<tau> \<omega> \<Turnstile> C" using assms(6)
    by (simp add: interpr_composition_def) 
  have notC:"?\<alpha>  \<Turnstile> (uminus `# C)"
    by (metis \<omega> atm_of_in_atm_of_set_in_uminus atm_of_lit_in_atms_of atms_of_def atms_of_uminus multi_member_split multiset.set_map true_cls_add_mset true_cls_def) 
  hence "interpr_composition \<tau> ?\<alpha> = interpr_composition ?\<alpha> \<tau>" 
    using cons3 assms(3) apply auto apply(simp add: interpr_composition_def)
    apply (metis in_image_uminus_uminus insert_DiffM true_cls_add_mset)
    apply(simp add: interpr_composition_def)
    by (metis in_image_uminus_uminus insert_DiffM true_cls_add_mset uminus_of_uminus_id)
  hence sat:"interpr_composition \<tau> ?\<alpha> \<Turnstile>m N + {#uminus `# C#}"
    using notC \<tau> apply auto
    apply (metis (no_types, lifting) interpr_composition_def true_cls_union_increase')
    by (simp add: interpr_composition_def true_cls_mset_def)
  then have min:"interpr_composition \<tau> ?\<alpha> \<Turnstile>m N" 
    by auto
  have sat:"interpr_composition \<tau> (interpr_composition ?\<alpha> \<omega>) \<Turnstile>m N"
    using cons3 min redundancyD redundancyD[OF red cons3 min] by blast 
  have \<open>\<tau> \<^bold>\<circ> ?\<alpha> = \<tau>\<close>
    using \<open>\<not>\<tau> \<Turnstile> C\<close> \<open>total_over_set \<tau> (atms_of_mm (add_mset C N))\<close>
    apply (auto simp: interpr_composition_def dest!: multi_member_split)
    apply (metis atm_of_eq_atm_of literal.sel(1))
    apply (metis atm_of_eq_atm_of literal.sel(2))
    done
  have sat2:"interpr_composition \<tau> \<omega> \<Turnstile>m N"
    using sat unfolding interpr_composition_assoc \<open>\<tau> \<^bold>\<circ> ?\<alpha> = \<tau>\<close> .
  then show ?thesis
    using C by auto
qed

lemma atoms_sub_interpretation: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" 
  and "V' \<subseteq> atm_of ` I"
  shows "V \<subseteq> atm_of ` I"
  using assms apply (induction rule: rules_induct) by auto

lemma rtranclp_atoms_sub_interpretation:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')"  and "N + wit_clause `# mset S \<Turnstile>psm R"
  and "V' \<subseteq> atm_of ` I"
  shows  "V \<subseteq> atm_of ` I"
  using assms 
proof (induction arbitrary: I rule: rtranclp_induct4)
  case refl
  then show ?case  by auto
next
  case (step N' R' S' V' N'' R'' S'' V'' I) note A2 = this(2) and A4 = this(4) and A5 = this(5) and A3 = this(3)
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'" 
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) step.hyps(1) by blast
  have " V' \<subseteq> atm_of ` I"
    using atoms_sub_interpretation A2 add A5 apply auto by blast
  then show ?case
    using A3 A4 by auto 
qed

lemma proposition3: 
  assumes  "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and 
   "I \<Turnstile>m N + wit_clause `# mset S" and "consistent_interp I"  and "V' \<subseteq> atm_of ` I"
  shows "I \<Turnstile>m N' + wit_clause `# mset S'"
  using assms
proof (induction rule: rules_induct)
  case (drop N C R S V)
  then show ?case by auto
next
  case (strenghten N C R S V) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4 = this(4)
  have tot:"total_over_m I (set_mset(N + R + {#C#} + (wit_clause `# mset S)))" 
    using A4
    by (simp add: atms_of_s_def total_over_m_alt_def)
  have "I \<Turnstile> C"
    using true_clss_cls_def A3 A2 tot A1
     by (metis set_mset_add_mset_insert set_mset_empty set_mset_union total_over_m_union true_cls_mset_true_clss_iff(2) true_clss_clss_insert union_mset_add_mset_left)
  then show ?case using A2
    by fastforce
next
  case (weakenp I C N R S V)
  then show ?case by auto
next
  case (forget N C R S V)
  then show ?case by auto
next
  case (learn_minus N R C S V)
  then show ?case by auto
qed

lemma proposition3_back: 
  assumes  "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and 
   "I \<Turnstile>m N' + wit_clause `# mset S'" and "consistent_interp I" 
  and "V' \<subseteq> atm_of ` I"
  shows "I \<Turnstile>m N + wit_clause `# mset S"
  using assms
proof (induction rule: rules_induct)
  case (drop N C R S V) note all = this(1,2, 4, 5) and sub = this(5) and cons = this(4) and A1 = this(1) and A3 = this(3)
  have sat:"I \<Turnstile>m N" 
    using A3 by auto
  have "total_over_m I (set_mset(N + R + {#C#}))"
    using sub
    by (simp add: atms_of_s_def total_over_m_alt_def)
  hence "I \<Turnstile> C" 
    using true_clss_cls_def cons sat
    using A1 by auto
  then show ?case using A3 by auto
next
  case (strenghten C N R S V)
  then show ?case by auto
next
  case (weakenp I C N R S V)
  then show ?case by auto 
next
  case (forget N C R S V)
  then show ?case by auto 
next
  case (learn_minus N R C S V)
  then show ?case by auto
qed

lemma rtranclp_proposition3:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')"  and "N + wit_clause `# mset S \<Turnstile>psm R" and 
   "I \<Turnstile>m N + wit_clause `# mset S" and "consistent_interp I" and "V' \<subseteq> atm_of ` I"
  shows "I \<Turnstile>m N' + wit_clause `# mset S'"
  using assms 
proof (induction arbitrary: I rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
  case (step N' R' S' V' N'' R'' S'' V'' I) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4 = this(4) and A5 = this(5) and A6 = this(6) and A7 = this(7)
  have ruls:  "rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'')" 
    using A1 A2 by auto
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'" 
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) step.hyps(1) by blast
  have sub:"V' \<subseteq> atm_of ` I"
    using atoms_sub_interpretation A7 A2 add by blast
  have "I \<Turnstile>m N'  + wit_clause `# mset S'"
    using A3 A4 A5 A6 sub by auto
  hence "I \<Turnstile>m N'' + wit_clause `# mset S''" 
    using A2 add A6 proposition3 A7 by blast
  then show ?case by auto
qed

lemma rtranclp_proposition3_back:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')"  and "N + wit_clause `# mset S \<Turnstile>psm R" and 
   "I \<Turnstile>m N' + wit_clause `# mset S'" and "consistent_interp I" 
  and "V' \<subseteq> atm_of ` I"
  shows "I \<Turnstile>m N + wit_clause `# mset S"
  using assms 
proof (induction arbitrary: I rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
  case (step N' R' S' V' N'' R'' S'' V'' I) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4 = this(4) and A5 = this(5) and A6 = this(6) and A7 = this(7)
  have ruls:  "rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'')" 
    using A1 A2 by auto
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'"
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) step.hyps(1) by blast
  have sub:" V' \<subseteq> atm_of ` I"
    using atoms_sub_interpretation A2 add A7 apply auto by blast
  have "I \<Turnstile>m N' + wit_clause `# mset S'" 
    using A2 add A6 A5 A7 proposition3_back by blast 
  hence "I \<Turnstile>m N + wit_clause `# mset S"
    using A6 step.IH step.prems(1) step.prems(2) sub by blast 
  then show ?case 
    by auto
qed

lemma wit_clause_sub:
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "wit_clause `# mset S \<subseteq>#  wit_clause `# mset S'"
  using assms
  apply(induction rule: rules_induct) by auto

lemma rtranclp_wit_clause_sub:
  assumes"rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "wit_clause `# mset S \<subseteq>#  wit_clause `# mset S'"
  using assms
proof (induction rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
  case (step N' R' S' V' N'' R'inter_from_stack' S'' V'') note A3 = this(3) and A4 = this(4) and A2 = this(2) and A1 = this(1)
  have A:" wit_clause `# mset S \<subseteq># wit_clause `# mset S'"
    using A3 A4 by auto
  have "N' + wit_clause `# mset S' \<Turnstile>psm R'" 
    using rtranclp_irredundant_entail_redundant A1 A4 by auto
  hence  " wit_clause `# mset S' \<subseteq># wit_clause `# mset S''" 
    using wit_clause_sub A2 by auto
  then show ?case using A by auto
qed

lemma interp_is_cons: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and
    "I  \<Turnstile>m N'" and "consistent_interp I" and  "V' \<subseteq> atm_of ` I"
  shows "consistent_interp (reconstruction_stack (drop (length S) S') I)"
  using assms
proof(induction rule: rules_induct)
  case (drop N C R S)
  then show ?case by auto
next
  case (strenghten N C R S)
  then show ?case by auto
next
  case (weakenp I' C N R S) note consI' = this(4) and red = this(1, 2) and sat = this(6) and cons = this(7)
  have "consistent_interp (interpr_composition I I')" 
    using cons consI' apply (simp add: interpr_composition_def)
    by (smt (verit, ccfv_threshold) Diff_iff Un_iff consistent_interp_def mem_Collect_eq uminus_of_uminus_id)
  then show ?case 
    using red consI' sat apply auto using weakenp.prems(3) by blast
next
  case (forget N C R S)
  then show ?case by auto
next
  case (learn_minus N R C S)
  then show ?case by auto
qed

lemma interpr_sat: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and "I \<Turnstile>m N'" 
  and "consistent_interp I" and "V' \<subseteq> atm_of ` I"
  shows "(reconstruction_stack (drop (length S) S') I) \<Turnstile>m N"
  using assms
proof(induction rule: rules_induct)
  case (drop N C R S V) note N = this(3) and cons = this(4) and all = this(3, 4) and sub = this(5)
  have rul:"rules (({#C#}+N), R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
            (N, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
    using drop.hyps rules.drop by blast
  have cons:"consistent_interp I" 
    using interp_is_cons rul all assms(4) sub by blast
  have "total_over_m I (set_mset(N + R + {#C#}))" 
    using sub by (simp add: atms_of_s_def total_over_m_alt_def)
  hence "I \<Turnstile> C" 
    using true_clss_cls_def cons N drop.hyps by auto
  then show ?case 
    using N by auto
next
  case (strenghten N C R S V)
  then show ?case by auto
next
  case (weakenp I' C N R S V) note all = this(1-7) and A8 = this(8)
  have "total_over_set I (atms_of_mm (add_mset C N))" 
    using A8 apply auto
    apply (meson subset_iff total_over_set_atm_of)
    by (meson subset_iff total_over_set_atm_of)
  then show ?case 
    using proposition1[of N C I' I] all by auto
next
  case (forget N C R S V)
  then show ?case by auto
next
  case (learn_minus N R C S V)
  then show ?case by auto
qed

lemma stack: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows " S' = S @ (drop (length S) S')"
  using assms apply(induction rule: rules_induct) by auto

lemma atms_equal:  
  assumes  "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and "V' \<subseteq> atm_of ` I"
  shows  "atm_of ` reconstruction_stack (drop (length S) S') I = atm_of ` I" 
  using assms
proof(induction rule: rules_induct)
  case (drop N C R S V)
  then show ?case by auto
next
  case (strenghten C N R S V)
  then show ?case by auto
next
  case (weakenp I' C N R S V) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4= this(4) and A5 = this(5) and A6 = this(6)
  have "atm_of `interpr_composition I I' = atm_of `I" 
    apply (simp add: interpr_composition_def) 
    apply auto using A6 A2
    apply blast
    by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set)
  then show ?case by auto
next
  case (forget N C R S V)
  then show ?case by auto
next
  case (learn_minus N R C S V)
  then show ?case by auto
qed

lemma atoms_sub_interpretation2: 
  assumes  "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and "V' \<subseteq> atm_of ` I"
  shows  "V \<subseteq> atm_of ` reconstruction_stack (drop (length S) S') I"
  using assms
proof(induction rule: rules_induct)
  case (drop N C R S V)
  then show ?case by auto
next
  case (strenghten C N R S V)
  then show ?case by auto
next
  case (weakenp I' C N R S V) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4= this(4) and A5 = this(5) and A6 = this(6)
  have "rules (N+{#C#}, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
        (N, R, (S @ [Witness I' C]), V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
    using A1 A2 A3 A4 rules.weakenp apply auto by blast
  hence "atm_of ` reconstruction_stack (drop (length S) (S @ [Witness I' C])) I = atm_of ` I"
    using atms_equal A5 A6 by blast
  then show ?case using A6 by auto
next
  case (forget N C R S V)
  then show ?case by auto
next
  case (learn_minus N R C S V)
  then show ?case by auto
qed

lemma interp_is_cons_mult: 
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and
   "I  \<Turnstile>m N'" and "consistent_interp I" and "V' \<subseteq> atm_of ` I"
  shows "consistent_interp (reconstruction_stack (drop (length S) S') I)"
  using assms 
proof (induction arbitrary: I rule: rtranclp_induct4)
  case refl
  then show ?case 
    by auto
next
  case (step N' R' S' V' N'' R'' S'' V'' I)  note at = this(7) and A1 = this(1) and cons = this(6) and A5 = this(5)  and A2 = this(2) and A3 = this(3) and A4 = this(4) 
  have ruls2:  "rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'')"
    using A1 A2 by auto
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'"
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) using  step.hyps(1) by blast
  have add2: "N'' + wit_clause `# mset S'' \<Turnstile>psm R''"
    using irredundant_entail_redundant add A2 by blast
  have relS:"wit_clause `# mset S' \<subseteq>#  wit_clause `# mset S''"
    using A2 apply(induction rule: rules_induct) by auto
  have sub:" V' \<subseteq> atm_of ` I" 
    using atoms_sub_interpretation A2 add at apply auto by blast
  have  sat:"(reconstruction_stack (drop (length S') S'') I) \<Turnstile>m N'" 
    using interpr_sat A2 cons add A5 at by blast
  have cons1:"consistent_interp (reconstruction_stack (drop (length S') S'') I)" 
    using interp_is_cons A2 add at A5 cons by blast
  have relS2:"wit_clause `# mset S \<subseteq>#  wit_clause `# mset S'"
    using A1 rtranclp_wit_clause_sub A4 by auto 
  hence len: "length S \<le> length S'"
    using size_mset_mono by fastforce
  have len1: "length S' \<le> length S''" 
    using relS size_mset_mono by fastforce
  have sep: "drop (length S) S'' = (drop (length S) S')@ (drop (length S') S'')"
    using A2 stack add apply auto
    by (smt (verit) add append_self_conv2 cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq drop_all drop_append len stack) 
  have sub2: "V' \<subseteq> atm_of `reconstruction_stack (drop (length S') S'') I" 
    using atoms_sub_interpretation2 A2 add at apply auto by blast
  then show ?case 
    using cons1 len A2 step(3, 4, 5, 6, 7) by (metis foldr_append sat sep)
qed

lemma interpr_sat_all:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" and
    "I  \<Turnstile>m N'"  and "consistent_interp I" 
  and "V' \<subseteq> atm_of ` I"
  shows "(reconstruction_stack (drop (length S) S') I) \<Turnstile>m N"
  using assms
proof (induction arbitrary: I rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
 case (step N' R' S' V' N'' R'' S'' V'' I)  note  at = this(7) and A1 = this(1) and cons = this(6) and A5 = this(5) and A2 = this(2) and A3 = this(3) and A4 = this(4)
  have ruls2:  "rules\<^sup>*\<^sup>* (N, R, S, V) (N'', R'', S'', V'')" 
    using A1 A2 by auto
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'"
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) using  step.hyps(1) by blast 
  have add2: "N'' + wit_clause `# mset S'' \<Turnstile>psm R''" 
    using irredundant_entail_redundant add A2 by blast
  have relS:"wit_clause `# mset S' \<subseteq>#  wit_clause `# mset S''"
    using A2 apply(induction rule: rules_induct) by auto
   have sub:" V' \<subseteq> atm_of ` I" 
    using atoms_sub_interpretation A2 add at apply auto by blast
  have  sat:"(reconstruction_stack (drop (length S') S'') I) \<Turnstile>m N'" 
    using interpr_sat A2 cons add A5 at by blast
  have cons1:"consistent_interp (reconstruction_stack (drop (length S') S'') I)" 
    using interp_is_cons A2 add at A5 cons by blast
  have relS2:"wit_clause `# mset S \<subseteq>#  wit_clause `# mset S'"
    using A1 rtranclp_wit_clause_sub A4 by auto 
  hence len: "length S \<le> length S'"
    using size_mset_mono by fastforce
  have len1: "length S' \<le> length S''"
    using relS size_mset_mono by fastforce
  have sep: "drop (length S) S'' = (drop (length S) S')@ (drop (length S') S'')"   
    using A2 stack add apply auto
    by (smt (verit) add append_self_conv2 cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq drop_all drop_append len stack) 
  have sub2: "V' \<subseteq> atm_of `reconstruction_stack (drop (length S') S'') I" 
    using atoms_sub_interpretation2 A2 add at apply auto by blast
  have "(reconstruction_stack (drop (length S) S') (reconstruction_stack (drop (length S') S'') I)) \<Turnstile>m N" 
    using A3 sat A4  cons1 sub2 by auto
  hence "(reconstruction_stack (drop (length S) S'') I) \<Turnstile>m N" 
    using sep by simp
  then show ?case by auto
qed

lemma interpr_sat_all_final:
  assumes "rules\<^sup>*\<^sup>* (N, {#}, [], V) (N', R', S', V')" and
    "I \<Turnstile>m N'" and "consistent_interp I" and "V' \<subseteq> image atm_of I" 
  shows "(reconstruction_stack S' I) \<Turnstile>m N"
  using interpr_sat_all[OF assms(1) _ assms(2-4)] by auto

lemma sat: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" 
  shows "satisfiable (set_mset( N+R)) \<Longrightarrow> satisfiable(set_mset( N'+R'))"
  using assms 
proof(induction rule: rules_induct)
  case (drop N C R S V) note A2 = this(2)
  then show ?case
    by (metis mset_subset_eq_add_right set_mset_mono subset_mset.add_right_mono unsatisfiable_mono)
next
  case (strenghten N C R S V)
  then show ?case by auto
next
  case (weakenp I C N R S V) note A5 = this(5)
  then show ?case
    by (metis mset_subset_eq_add_left set_mset_mono subset_mset.add_right_mono unsatisfiable_mono)
next
  case (forget N C R S V)
  then show ?case using satisfiable_decreasing
    by (smt (verit) set_mset_union union_commute union_lcomm) 
next
  case (learn_minus N R C S V) note A1 = this(1) and A3 = this(3)
  have ent: "(\<forall>I. total_over_m I (set_mset N \<union> set_mset R \<union> {C}) \<longrightarrow> consistent_interp I \<longrightarrow> I \<Turnstile>s set_mset(N+R) \<longrightarrow> I \<Turnstile> C)" 
    using true_clss_cls_def A1 by auto
  have "(\<exists>I. consistent_interp I \<and> I \<Turnstile>s set_mset(N+R))"
    using satisfiable_carac A3 by blast
  then obtain I where I:"consistent_interp I \<and> I \<Turnstile>s set_mset(N+R)"
    by auto
  have "\<exists>I'. total_over_m (I \<union> I') (set_mset N \<union> set_mset R \<union> {C}) \<and> consistent_interp (I \<union> I')"
    by (meson I total_over_m_consistent_extension total_over_m_empty total_over_m_union)
  then obtain I' where I':"total_over_m (I \<union> I') (set_mset N \<union> set_mset R \<union> {C}) \<and> consistent_interp (I \<union> I')"
    by auto
  hence A:"(I \<union> I') \<Turnstile>s set_mset(N+R)" 
    using I by auto
  hence "(I \<union> I') \<Turnstile> C" 
    using I' ent by blast
  hence "(\<exists>J. consistent_interp J \<and> J \<Turnstile>s (set_mset(N+R)\<union> {C}))"
    using I' A by auto
  hence "satisfiable (set_mset(N+R)\<union> {C})"
    using satisfiable_carac by auto
  then show ?case by auto
qed

lemma rtranclp_sat:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "satisfiable (set_mset( N+R)) \<Longrightarrow> satisfiable(set_mset( N'+R'))"
  using assms
proof(induction rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
  case (step N' R' S' V' N'' R'' S'' V'') note A3 = this(3) and A5 = this(5) and A2 = this(2) and A4 = this(4)
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'"
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) using  step.hyps(1) by blast
  have "satisfiable (set_mset (N' + R'))" 
    using A3 A4 A5 by auto
  then show ?case using sat add A2 by auto
qed

lemma unsat: 
  assumes "rules (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R" 
  shows "unsatisfiable (set_mset (N'+R')) \<Longrightarrow> unsatisfiable (set_mset (N+R))"
  using assms
proof(induction rule: rules_induct)
  case (drop N C R S V) note A2 = this(2)
  have "R + N \<subseteq># {#C#} + R + N" 
    by auto
  then show ?case
    using unsatisfiable_mono A2 by (metis set_mset_mono union_assoc union_commute) 
next
  case (strenghten C N R S V)
  then show ?case by auto
next
  case (weakenp I' C N R S V) note A5 = this(5)
  have "R + N \<subseteq># {#C#} + R + N" 
    by auto
  then show ?case 
    using unsatisfiable_mono A5 by (metis set_mset_mono union_assoc union_commute)
next
  case (forget N C R S V) note A1 = this(1)
  have "R + N \<subseteq># {#C#} + R + N"
    by auto
  then show ?case
    using unsatisfiable_mono A1 by (metis set_mset_mono union_commute)
next
  case (learn_minus N R C S V) note A1 = this(1) and A2 = this(2) and A3 = this(3) and A4 = this(4)
  have rul: "rules (N, R, S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))
            (N, ({#C#}+R), S, V \<union> atms_of C \<union> atms_of_mm N \<union>  atms_of_mm R \<union> atms_of_mm (wit_clause `# mset S))"
    using A1 A2 rules.learn_minus by blast 
  show "unsatisfiable (set_mset (N + R))"
  proof (rule ccontr)
    assume ass: "\<not>unsatisfiable (set_mset (N + R))"
    have "satisfiable (set_mset (N + R))"
      using ass by auto 
    hence "satisfiable (set_mset (N + R)\<union> {C})"
      using sat rul A4 A3 by blast
    then show "False"
      using A3 A4 ass rul sat by blast
 qed
qed

lemma rtranclp_unsat:
  assumes "rules\<^sup>*\<^sup>* (N, R, S, V) (N', R', S', V')" and "N + wit_clause `# mset S \<Turnstile>psm R"
  shows "unsatisfiable (set_mset( N'+R')) \<Longrightarrow>  unsatisfiable (set_mset( N+R))"
  using assms 
proof(induction rule: rtranclp_induct4)
  case refl
  then show ?case by auto
next
  case (step N' R' S' V' N'' R'' S'' V'') note A3 = this(3) and A5 = this(5) and A2 = this(2) and A4 = this(4)
  have add:"N' + wit_clause `# mset S' \<Turnstile>psm R'"
    using rtranclp_irredundant_entail_redundant assms(1) assms(2) step.hyps(1) by blast
  have "unsatisfiable (set_mset (N'+R'))"
    using unsat add A2 A4 by blast 
  hence "unsatisfiable (set_mset (N+R))"
    using A3 A5 by auto
  then show ?case by auto
qed

end