theory Partial_And_Total_Herbrand_Interpretation
  imports Partial_Herbrand_Interpretation
    Ordered_Resolution_Prover.Herbrand_Interpretation
begin

section \<open>Bridging of total and partial Herbrand interpretation\<close>

text \<open>This theory has mostly be written as a sanity check between the two entailment notion.\<close>
definition partial_model_of :: \<open>'a interp \<Rightarrow> 'a partial_interp\<close> where
\<open>partial_model_of I = Pos ` I \<union> Neg ` {x. x \<notin> I}\<close>

definition total_model_of :: \<open>'a partial_interp \<Rightarrow> 'a interp\<close> where
\<open>total_model_of I = {x. Pos x \<in> I}\<close>

lemma total_over_set_partial_model_of:
  \<open>total_over_set (partial_model_of I) UNIV\<close>
  unfolding total_over_set_def
  by (auto simp: partial_model_of_def)

lemma consistent_interp_partial_model_of:
  \<open>consistent_interp (partial_model_of I)\<close>
  unfolding consistent_interp_def
  by (auto simp: partial_model_of_def)

lemma consistent_interp_alt_def:
  \<open>consistent_interp I \<longleftrightarrow> (\<forall>L. \<not>(Pos L \<in> I \<and> Neg L \<in> I))\<close>
  unfolding consistent_interp_def
  by (metis literal.exhaust uminus_Neg uminus_of_uminus_id)

context
  fixes I :: \<open>'a partial_interp\<close>
  assumes cons: \<open>consistent_interp I\<close>
begin

lemma partial_implies_total_true_cls_total_model_of:
  assumes \<open>Partial_Herbrand_Interpretation.true_cls I C\<close>
  shows \<open>Herbrand_Interpretation.true_cls (total_model_of I) C\<close>
  using assms cons apply -
  unfolding total_model_of_def Partial_Herbrand_Interpretation.true_cls_def
    Herbrand_Interpretation.true_cls_def consistent_interp_alt_def
  by (rule bexE, assumption)
    (case_tac x; auto)


lemma total_implies_partial_true_cls_total_model_of:
  assumes \<open>Herbrand_Interpretation.true_cls (total_model_of I) C\<close> and
   \<open>total_over_set I (atms_of C)\<close>
  shows \<open>Partial_Herbrand_Interpretation.true_cls I C\<close>
  using assms cons
  unfolding total_model_of_def Partial_Herbrand_Interpretation.true_cls_def
    Herbrand_Interpretation.true_cls_def consistent_interp_alt_def
    total_over_m_def total_over_set_def
  by (auto simp: atms_of_def dest: multi_member_split)


lemma partial_implies_total_true_clss_total_model_of:
  assumes \<open>Partial_Herbrand_Interpretation.true_clss I C\<close>
  shows \<open>Herbrand_Interpretation.true_clss (total_model_of I) C\<close>
  using assms cons
  unfolding Partial_Herbrand_Interpretation.true_clss_def
    Herbrand_Interpretation.true_clss_def
  by (auto simp: partial_implies_total_true_cls_total_model_of)

lemma total_implies_partial_true_clss_total_model_of:
  assumes \<open>Herbrand_Interpretation.true_clss (total_model_of I) C\<close> and
    \<open>total_over_m I C\<close>
  shows \<open>Partial_Herbrand_Interpretation.true_clss I C\<close>
  using assms cons mk_disjoint_insert
  unfolding Partial_Herbrand_Interpretation.true_clss_def
    Herbrand_Interpretation.true_clss_def
    total_over_set_def
  by (fastforce simp: total_implies_partial_true_cls_total_model_of
      dest: multi_member_split)

end

lemma total_implies_partial_true_cls_partial_model_of:
  assumes \<open>Herbrand_Interpretation.true_cls I C\<close>
  shows \<open>Partial_Herbrand_Interpretation.true_cls (partial_model_of I) C\<close>
  using assms apply -
  unfolding partial_model_of_def Partial_Herbrand_Interpretation.true_cls_def
    Herbrand_Interpretation.true_cls_def consistent_interp_alt_def
  by (rule bexE, assumption)
    (case_tac x; auto)


lemma total_implies_partial_true_clss_partial_model_of:
  assumes \<open>Herbrand_Interpretation.true_clss I C\<close>
  shows \<open>Partial_Herbrand_Interpretation.true_clss (partial_model_of I) C\<close>
  using assms
  unfolding Partial_Herbrand_Interpretation.true_clss_def
    Herbrand_Interpretation.true_clss_def
  by (auto simp: total_implies_partial_true_cls_partial_model_of)

lemma partial_total_satisfiable_iff:
  \<open>Partial_Herbrand_Interpretation.satisfiable N \<longleftrightarrow> Herbrand_Interpretation.satisfiable N\<close>
  by (meson consistent_interp_partial_model_of partial_implies_total_true_clss_total_model_of
    satisfiable_carac total_implies_partial_true_clss_partial_model_of)

end