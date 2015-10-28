theory Propo_Superposition
imports Partial_Clausal_Logic "../lib/Herbrand_Interpretation"
begin

no_notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>" 50)
notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>h" 50)

no_notation Herbrand_Interpretation.true_cls (infix "\<Turnstile>s" 50)
notation Herbrand_Interpretation.true_clss (infix "\<Turnstile>hs" 50)

lemma herbrand_interp_iff_partial_interp_cls:
  "S \<Turnstile>h C \<longleftrightarrow> {Pos P|P. P\<in>S} \<union> {Neg P|P. P\<notin>S} \<Turnstile> C"
  unfolding Herbrand_Interpretation.true_cls_def Partial_Clausal_Logic.true_cls_def
  by auto

lemma herbrand_consistent_interp:
  "consistent_interp ({Pos P|P. P\<in>S} \<union> {Neg P|P. P\<notin>S})"
  unfolding consistent_interp_def by auto

lemma herbrand_total_over_set:
  "total_over_set ({Pos P|P. P\<in>S} \<union> {Neg P|P. P\<notin>S}) T"
  unfolding total_over_set_def by auto

lemma herbrand_total_over_m:
  "total_over_m ({Pos P|P. P\<in>S} \<union> {Neg P|P. P\<notin>S}) T"
  unfolding total_over_m_def by (auto simp add: herbrand_total_over_set)

lemma herbrand_interp_iff_partial_interp_clss:
  "S \<Turnstile>hs C \<longleftrightarrow> {Pos P|P. P\<in>S} \<union> {Neg P|P. P\<notin>S} \<Turnstile>s C"
  unfolding true_clss_def Ball_def herbrand_interp_iff_partial_interp_cls
  Partial_Clausal_Logic.true_clss_def by auto

definition clss_lt :: "'a::wellorder clauses \<Rightarrow> 'a clause \<Rightarrow> 'a clauses"  where
"clss_lt N C = {D \<in> N. D #\<subset># C}"

notation (latex output)
 clss_lt ("_<^bsup>_<^esup>")

locale selection =
  fixes S :: "'a clause \<Rightarrow> 'a clause"
  assumes
    S_selects_subseteq: "\<And>C. S C \<le># C" and
    S_selects_neg_lits: "\<And>C L. L \<in># S C \<Longrightarrow> is_neg L"

locale ground_resolution_with_selection =
  selection S for S :: "('a :: wellorder) clause \<Rightarrow> 'a clause"
begin

context
  fixes N :: "'a clause set"
begin

text \<open>We do not create an equivalent of @{term \<delta>}, but we directly defined @{term N\<^sub>C} by inlining the definition.\<close>
function
  production :: "'a clause \<Rightarrow> 'a interp"
where
  "production C =
   {A. C \<in> N \<and> C \<noteq> {#} \<and> Max (set_mset C) = Pos A \<and> count C (Pos A) \<le> 1
     \<and> \<not> (\<Union>D \<in> {D. D #\<subset># C}. production D) \<Turnstile>h C \<and> S C = {#}}"
  by auto
termination by (relation "{(D, C). D #\<subset># C}") (auto simp: wf_less_multiset)

declare production.simps[simp del]

definition interp :: "'a clause \<Rightarrow> 'a interp" where
  "interp C = (\<Union>D \<in> {D. D #\<subset># C}. production D)"

lemma production_unfold:
  "production C = {A. C \<in> N \<and> C \<noteq> {#} \<and> Max (set_mset C) = Pos A\<and> count C (Pos A) \<le> 1 \<and> \<not> interp C \<Turnstile>h C \<and> S C = {#}}"
  unfolding interp_def by (rule production.simps)

abbreviation "productive A \<equiv> (production A \<noteq> {})"

abbreviation produces :: "'a clause \<Rightarrow> 'a \<Rightarrow> bool" where
  "produces C A \<equiv> production C = {A}"

lemma producesD:
  "produces C A \<Longrightarrow> C \<in> N \<and> C \<noteq> {#} \<and> Pos A = Max (set_mset C) \<and> count C (Pos A) \<le> 1\<and> \<not> interp C \<Turnstile>h C \<and> S C = {#}"
  unfolding production_unfold by auto

lemma "produces C A \<Longrightarrow> Pos A \<in># C"
  by (simp add: Max_in_lits producesD)

lemma interp'_def_in_set:
  "interp C = (\<Union>D \<in> {D \<in> N. D #\<subset># C}. production D)"
  unfolding interp_def apply auto
  unfolding production_unfold apply auto
  done

lemma production_iff_produces:
  "produces D A \<longleftrightarrow> A \<in> production D"
  unfolding production_unfold by auto

definition Interp :: "'a clause \<Rightarrow> 'a interp" where
  "Interp C = interp C \<union> production C"

lemma
  assumes "produces C P"
  shows "Interp C \<Turnstile>h C"
  unfolding Interp_def assms using producesD[OF assms] 
  by (metis Max_in_lits Un_insert_right insertI1 pos_literal_in_imp_true_cls)

definition INTERP :: "'a interp" where
"INTERP = (\<Union>D \<in>N. production D)"


lemma interp_subseteq_Interp[simp]: "interp C \<subseteq> Interp C"
  unfolding Interp_def by simp

lemma Interp_as_UNION: "Interp C = (\<Union>D \<in> {D. D #\<subseteq># C}. production D)"
  unfolding Interp_def interp_def le_multiset_def by fast

lemma productive_not_empty: "productive C \<Longrightarrow> C \<noteq> {#}"
  unfolding production_unfold by auto

lemma productive_imp_produces_Max_literal: "productive C \<Longrightarrow> produces C (atm_of (Max (set_mset C)))"
  unfolding production_unfold by (auto simp del: atm_of_Max_lit)

lemma productive_imp_produces_Max_atom: "productive C \<Longrightarrow> produces C (Max (atms_of C))"
  unfolding atms_of_def Max_atm_of_set_mset_commute[OF productive_not_empty]
  by (rule productive_imp_produces_Max_literal)

lemma produces_imp_Max_literal: "produces C A \<Longrightarrow> A = atm_of (Max (set_mset C))"
  by (metis Max_singleton insert_not_empty productive_imp_produces_Max_literal)

lemma produces_imp_Max_atom: "produces C A \<Longrightarrow> A = Max (atms_of C)"
  by (metis Max_singleton insert_not_empty productive_imp_produces_Max_atom)

lemma produces_imp_Pos_in_lits: "produces C A \<Longrightarrow> Pos A \<in># C"
  by (auto intro: Max_in_lits dest!: producesD)

lemma productive_in_N: "productive C \<Longrightarrow> C \<in> N"
  unfolding production_unfold by auto

lemma produces_imp_atms_leq: "produces C A \<Longrightarrow> B \<in> atms_of C \<Longrightarrow> B \<le> A"
  by (metis Max_ge finite_atms_of insert_not_empty productive_imp_produces_Max_atom
    singleton_inject)

lemma produces_imp_neg_notin_lits: "produces C A \<Longrightarrow> \<not> Neg A \<in># C"
  by (auto intro!: pos_Max_imp_neg_notin dest: producesD simp del: not_gr0)

lemma less_eq_imp_interp_subseteq_interp: "C #\<subseteq># D \<Longrightarrow> interp C \<subseteq> interp D"
  unfolding interp_def by auto (metis multiset_order.order.strict_trans2)

lemma less_eq_imp_interp_subseteq_Interp: "C #\<subseteq># D \<Longrightarrow> interp C \<subseteq> Interp D"
  unfolding Interp_def using less_eq_imp_interp_subseteq_interp by blast

lemma less_imp_production_subseteq_interp: "C #\<subset># D \<Longrightarrow> production C \<subseteq> interp D"
  unfolding interp_def by fast

lemma less_eq_imp_production_subseteq_Interp: "C #\<subseteq># D \<Longrightarrow> production C \<subseteq> Interp D"
  unfolding Interp_def using less_imp_production_subseteq_interp
  by (metis multiset_order.le_imp_less_or_eq le_supI1 sup_ge2)

lemma less_imp_Interp_subseteq_interp: "C #\<subset># D \<Longrightarrow> Interp C \<subseteq> interp D"
  unfolding Interp_def
  by (auto simp: less_eq_imp_interp_subseteq_interp less_imp_production_subseteq_interp)

lemma less_eq_imp_Interp_subseteq_Interp: "C #\<subseteq># D \<Longrightarrow> Interp C \<subseteq> Interp D"
  using less_imp_Interp_subseteq_interp
  unfolding Interp_def by (metis multiset_order.le_imp_less_or_eq le_supI2 subset_refl sup_commute)

lemma false_Interp_to_true_interp_imp_less_multiset: "A \<notin> Interp C \<Longrightarrow> A \<in> interp D \<Longrightarrow> C #\<subset># D"
  using less_eq_imp_interp_subseteq_Interp multiset_linorder.not_less by blast

lemma false_interp_to_true_interp_imp_less_multiset: "A \<notin> interp C \<Longrightarrow> A \<in> interp D \<Longrightarrow> C #\<subset># D"
  using less_eq_imp_interp_subseteq_interp multiset_linorder.not_less by blast

lemma false_Interp_to_true_Interp_imp_less_multiset: "A \<notin> Interp C \<Longrightarrow> A \<in> Interp D \<Longrightarrow> C #\<subset># D"
  using less_eq_imp_Interp_subseteq_Interp multiset_linorder.not_less by blast

lemma false_interp_to_true_Interp_imp_le_multiset: "A \<notin> interp C \<Longrightarrow> A \<in> Interp D \<Longrightarrow> C #\<subseteq># D"
  using less_imp_Interp_subseteq_interp multiset_linorder.not_less by blast

lemma interp_subseteq_INTERP: "interp C \<subseteq> INTERP"
  unfolding interp_def INTERP_def by (auto simp: production_unfold)

lemma production_subseteq_INTERP: "production C \<subseteq> INTERP"
  unfolding INTERP_def using production_unfold by blast

lemma Interp_subseteq_INTERP: "Interp C \<subseteq> INTERP"
  unfolding Interp_def by (auto intro!: interp_subseteq_INTERP production_subseteq_INTERP)

text \<open>This lemma corresponds to \cwref{prop:prop:suppmcprop}{theorem 2.7.6 page 66}.\<close>
lemma produces_imp_in_interp:
  assumes a_in_c: "Neg A \<in># C" and d: "produces D A"
  shows "A \<in> interp C"
proof -
  from d have "Max (set_mset D) = Pos A"
    using production_unfold by blast
  hence "D #\<subset># {#Neg A#}"
    by (auto intro: Max_pos_neg_less_multiset)
  moreover have "{#Neg A#} #\<subseteq># C"
    by (rule less_eq_imp_le_multiset) (rule mset_le_single[OF a_in_c[unfolded mem_set_mset_iff]])
  ultimately show ?thesis
    using d by (blast dest: less_eq_imp_interp_subseteq_interp less_imp_production_subseteq_interp)
qed

lemma neg_notin_Interp_not_produce: "Neg A \<in># C \<Longrightarrow> A \<notin> Interp D \<Longrightarrow> C #\<subseteq># D \<Longrightarrow> \<not> produces D'' A"
  by (auto dest: produces_imp_in_interp less_eq_imp_interp_subseteq_Interp)

lemma in_production_imp_produces: "A \<in> production C \<Longrightarrow> produces C A"
  by (metis insert_absorb productive_imp_produces_Max_atom singleton_insert_inj_eq')

lemma not_produces_imp_notin_production: "\<not> produces C A \<Longrightarrow> A \<notin> production C"
  by (metis in_production_imp_produces)

lemma not_produces_imp_notin_interp: "(\<And>D. \<not> produces D A) \<Longrightarrow> A \<notin> interp C"
  unfolding interp_def by (fast intro!: in_production_imp_produces)

text \<open>
The results below corresponds to Lemma 3.4.

\begin{nit}
If $D = D'$ and $D$ is productive, $I^D \subseteq I_{D'}$ does not hold. 
\end{nit}
\<close>

lemma true_Interp_imp_general:
  assumes
    c_le_d: "C #\<subseteq># D" and
    d_lt_d': "D #\<subset># D'" and
    c_at_d: "Interp D \<Turnstile>h C" and
    subs: "interp D' \<subseteq> (\<Union>C \<in> CC. production C)"
  shows "(\<Union>C \<in> CC. production C) \<Turnstile>h C"
proof (cases "\<exists>A. Pos A \<in># C \<and> A \<in> Interp D")
  case True
  then obtain A where a_in_c: "Pos A \<in># C" and a_at_d: "A \<in> Interp D"
    by blast
  from a_at_d have "A \<in> interp D'"
    using d_lt_d' less_imp_Interp_subseteq_interp by blast
  thus ?thesis
    using subs a_in_c by (blast dest: contra_subsetD)
next
  case False
  then obtain A where a_in_c: "Neg A \<in># C" and "A \<notin> Interp D"
    using c_at_d unfolding true_cls_def by blast
  hence "\<And>D''. \<not> produces D'' A"
    using c_le_d neg_notin_Interp_not_produce by simp
  thus ?thesis
    using a_in_c subs not_produces_imp_notin_production by auto
qed

lemma true_Interp_imp_interp: "C #\<subseteq># D \<Longrightarrow> D #\<subset># D' \<Longrightarrow> Interp D \<Turnstile>h C \<Longrightarrow> interp D' \<Turnstile>h C"
  using interp_def true_Interp_imp_general by simp

lemma true_Interp_imp_Interp: "C #\<subseteq># D \<Longrightarrow> D #\<subset># D' \<Longrightarrow> Interp D \<Turnstile>h C \<Longrightarrow> Interp D' \<Turnstile>h C"
  using Interp_as_UNION interp_subseteq_Interp true_Interp_imp_general by simp

lemma true_Interp_imp_INTERP: "C #\<subseteq># D \<Longrightarrow> Interp D \<Turnstile>h C \<Longrightarrow> INTERP \<Turnstile>h C"
  using INTERP_def interp_subseteq_INTERP
    true_Interp_imp_general[OF _ less_multiset_right_total]
  by simp

lemma true_interp_imp_general:
  assumes
    c_le_d: "C #\<subseteq># D" and
    d_lt_d': "D #\<subset># D'" and
    c_at_d: "interp D \<Turnstile>h C" and
    subs: "interp D' \<subseteq> (\<Union>C \<in> CC. production C)"
  shows "(\<Union>C \<in> CC. production C) \<Turnstile>h C"
proof (cases "\<exists>A. Pos A \<in># C \<and> A \<in> interp D")
  case True
  then obtain A where a_in_c: "Pos A \<in># C" and a_at_d: "A \<in> interp D"
    by blast
  from a_at_d have "A \<in> interp D'"
    using d_lt_d' less_eq_imp_interp_subseteq_interp[OF multiset_order.less_imp_le] by blast
  thus ?thesis
    using subs a_in_c by (blast dest: contra_subsetD)
next
  case False
  then obtain A where a_in_c: "Neg A \<in># C" and "A \<notin> interp D"
    using c_at_d unfolding true_cls_def by blast
  hence "\<And>D''. \<not> produces D'' A"
    using c_le_d by (auto dest: produces_imp_in_interp less_eq_imp_interp_subseteq_interp)
  thus ?thesis
    using a_in_c subs not_produces_imp_notin_production by auto
qed

text \<open>This lemma corresponds to \cwref{prop:prop:suppmcprop}{theorem 2.7.6 page 66}. Here the strict maximality is important\<close>
lemma true_interp_imp_interp: "C #\<subseteq># D \<Longrightarrow> D #\<subset># D' \<Longrightarrow> interp D \<Turnstile>h C \<Longrightarrow> interp D' \<Turnstile>h C"
  using interp_def true_interp_imp_general by simp

lemma true_interp_imp_Interp: "C #\<subseteq># D \<Longrightarrow> D #\<subset># D' \<Longrightarrow> interp D \<Turnstile>h C \<Longrightarrow> Interp D' \<Turnstile>h C"
  using Interp_as_UNION interp_subseteq_Interp[of D'] true_interp_imp_general by simp

lemma true_interp_imp_INTERP: "C #\<subseteq># D \<Longrightarrow> interp D \<Turnstile>h C \<Longrightarrow> INTERP \<Turnstile>h C"
  using INTERP_def interp_subseteq_INTERP
    true_interp_imp_general[OF _ less_multiset_right_total]
  by simp

lemma productive_imp_false_interp: "productive C \<Longrightarrow> \<not> interp C \<Turnstile>h C"
  unfolding production_unfold by auto

text \<open>This lemma corresponds to \cwref{prop:prop:suppmcprop}{theorem 2.7.6 page 66}. Here the strict maximality is important\<close>
lemma cls_gt_double_pos_no_production:
  assumes D: "{#Pos P, Pos P#} #\<subset># C"
  shows "\<not>produces C P"
proof -
  let ?D = "{#Pos P, Pos P#}"
  note D' = D[unfolded less_multiset\<^sub>H\<^sub>O]
  consider
    (P) "count C (Pos P) \<ge> 2"
  | (Q) Q where "Q > Pos P" and "Q \<in># C "
    using HOL.spec[OF HOL.conjunct2[OF D'], of "Pos P"] by auto 
  thus ?thesis
    proof cases
      case Q
      have "Q \<in> set_mset C" 
        using Q(2) by (auto split: split_if_asm)
      then have "Max (set_mset C) > Pos P"
        using Q(1) Max_gr_iff by blast
      thus ?thesis
        unfolding production_unfold by auto
    next
      case P
      thus ?thesis
        unfolding production_unfold by auto
    qed
qed


text \<open>This lemma corresponds to \cwref{prop:prop:suppmcprop}{theorem 2.7.6 page 66}.\<close>
lemma
  assumes D: "C+{#Neg P#} #\<subset># D" 
  shows "production D \<noteq> {P}"
proof -
  note D' = D[unfolded less_multiset\<^sub>H\<^sub>O]
  consider
    (P) "Neg P \<in># D"
  | (Q) Q where "Q > Neg P" and "count D Q > count (C + {#Neg P#}) Q"
    using HOL.spec[OF HOL.conjunct2[OF D'], of "Neg P"] by fastforce 
  thus ?thesis
    proof cases
      case Q
      have "Q \<in> set_mset D" 
        using Q(2) by (auto split: split_if_asm)
      then have "Max (set_mset D) > Neg P"
        using Q(1) Max_gr_iff by blast
      hence "Max (set_mset D) > Pos P"
        using less_trans[of "Pos P" "Neg P" "Max (set_mset D)"] by auto
      thus ?thesis
        unfolding production_unfold by auto
    next
      case P
      hence "Max (set_mset D) > Pos P"
        by (meson Max_ge finite_set_mset le_less_trans linorder_not_le mem_set_mset_iff
          pos_less_neg)
      thus ?thesis
        unfolding production_unfold by auto
    qed
qed

lemma in_interp_is_produced:
  assumes "P \<in> INTERP"
  shows "\<exists>D. D +{#Pos P#} \<in> N \<and> produces (D +{#Pos P#}) P"
  using assms unfolding INTERP_def UN_iff production_iff_produces Ball_def 
  by (metis ground_resolution_with_selection.produces_imp_Pos_in_lits ground_resolution_with_selection_axioms insert_DiffM2 not_produces_imp_notin_production)


end
end
(*TODO sharing with Propo_CDCL*)
abbreviation "MMax M \<equiv> Max (set_mset M)"

subsection \<open>We can now define the rules of the calculus\<close>
inductive superposition_rules :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
factoring: "superposition_rules (C + {#Pos P#} + {#Pos P#}) B (C + {#Pos P#})" |
superposition_l: "superposition_rules (C\<^sub>1 + {#Pos P#}) (C\<^sub>2 + {#Neg P#}) (C\<^sub>1+ C\<^sub>2)"
  
inductive superposition :: "'a clauses \<Rightarrow> 'a clauses \<Rightarrow> bool" where
superposition: "A \<in> N \<Longrightarrow> B \<in> N \<Longrightarrow> superposition_rules A B C
  \<Longrightarrow> superposition N (N \<union> {C})"

definition abstract_red :: "'a::wellorder clause \<Rightarrow> 'a clauses \<Rightarrow> bool" where
"abstract_red C N = (clss_lt N C \<Turnstile>p C)"

(*TODO: remove when multiset is of sort ord again*)
instantiation multiset :: (linorder) linorder
begin

definition less_multiset :: "'a::linorder multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "M' < M \<longleftrightarrow> M' #\<subset># M"

definition less_eq_multiset :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow>bool" where
   "(M'::'a multiset) \<le> M \<longleftrightarrow> M' #\<subseteq># M"

instance
  by standard (auto simp add: less_eq_multiset_def less_multiset_def multiset_order.less_le_not_le add.commute multiset_order.add_right_mono)
end

lemma less_multiset[iff]: "M < N \<longleftrightarrow> M #\<subset># N"
  unfolding less_multiset_def by auto

lemma less_eq_multiset[iff]: "M \<le> N \<longleftrightarrow> M #\<subseteq># N"
  unfolding less_eq_multiset_def by auto

lemma herbrand_true_clss_true_clss_cls_herbrand_true_clss:
  assumes 
    AB: "A \<Turnstile>hs B" and
    BC: "B \<Turnstile>p C"
  shows "A \<Turnstile>h C"
proof -
  let ?I = "{Pos P |P. P \<in> A} \<union> {Neg P |P. P \<notin> A}"
  have B: "?I \<Turnstile>s B" using AB
    by (auto simp add: herbrand_interp_iff_partial_interp_clss)
  
  have IH: "\<And>I. total_over_set I (atms_of C) \<Longrightarrow> total_over_m I B \<Longrightarrow> consistent_interp I \<Longrightarrow> I \<Turnstile>s B \<Longrightarrow> I \<Turnstile> C" using BC
    by (auto simp add: true_clss_cls_def)
  show ?thesis
    unfolding herbrand_interp_iff_partial_interp_cls
    by (auto intro: IH[of ?I] simp add: herbrand_total_over_set herbrand_total_over_m herbrand_consistent_interp B)
qed
  
lemma abstract_red_subset_mset_abstract_red:
  assumes 
    abstr: "abstract_red C N" and 
    c_lt_d: "C \<subseteq># D"
  shows "abstract_red D N"
proof -
  have "{D \<in> N. D #\<subset># C} \<subseteq> {D' \<in> N. D' #\<subset># D}"
    using c_lt_d less_eq_imp_le_multiset by fastforce
  thus ?thesis
    using abstr unfolding abstract_red_def clss_lt_def 
    by (metis (no_types, lifting) c_lt_d subset_mset.diff_add true_clss_cls_mono_r' true_clss_cls_subset)
qed
  
locale ground_ordered_resolution_with_redundancy = 
  ground_resolution_with_selection +
  fixes redundant :: "'a::wellorder clause \<Rightarrow> 'a clauses \<Rightarrow> bool" 
  assumes 
    redundant_is_abstract: "redundant A N \<Longrightarrow> abstract_red A N" and
    redundant_mono: "redundant A N \<Longrightarrow> A \<subseteq># B \<Longrightarrow> redundant B N"
begin
definition saturated :: "'a clauses \<Rightarrow> bool" where
"saturated N \<longleftrightarrow> (\<forall>A B C. A \<in> N \<longrightarrow> B \<in> N \<longrightarrow> \<not>redundant A N \<longrightarrow> \<not>redundant B N \<longrightarrow> superposition_rules A B C \<longrightarrow> redundant C N)"
  
lemma
  assumes 
    saturated: "saturated N" and
    finite: "finite N" and
    empty: "{#} \<notin> N"
  shows "INTERP N \<Turnstile>hs N"
proof (rule ccontr)
  let ?I = "INTERP N"
  assume "\<not> ?thesis"
  hence not_empty: "{E\<in>N. \<not>?I \<Turnstile>h E} \<noteq> {}"
    unfolding true_clss_def Ball_def by auto
  def D \<equiv> "Min {E\<in>N. \<not>?I \<Turnstile>h E}"
  have [simp]: "D \<in> N" 
    unfolding D_def
    by (metis (mono_tags, lifting) Min_in not_empty finite mem_Collect_eq rev_finite_subset subsetI)
  have not_d_interp: "\<not>?I \<Turnstile>h D"
    unfolding D_def
    by (metis (mono_tags, lifting) Min_in finite mem_Collect_eq not_empty rev_finite_subset subsetI)
  have cls_not_D: "\<And>E. E \<in> N \<Longrightarrow> E \<noteq> D \<Longrightarrow> \<not>?I \<Turnstile>h E \<Longrightarrow> D \<le> E"
    using finite D_def by (auto simp del: less_eq_multiset)
  obtain C L where D: "D = C + {#L#}"  and LSD: "L \<in># S D \<or> (S D = {#} \<and> Max (set_mset D) = L)"
    proof (cases "S D = {#}")
      case False
      then obtain L where "L \<in># S D"
        using Max_in_lits by blast
      moreover 
        hence "L \<in># D"
          using S_selects_subseteq[of D] by auto
        hence "D = (D - {#L#}) + {#L#}"
          by auto
      ultimately show ?thesis using that by blast
    next
      let ?L = "MMax D"
      case True
      moreover
        have "?L \<in># D"
          by (metis (no_types, lifting) Max_in_lits \<open>D \<in> N\<close> empty)
        hence "D = (D - {#?L#}) + {#?L#}"
          by auto
      ultimately show ?thesis using that by blast
    qed
  have red: "\<not>redundant D N"
    proof (rule ccontr)
      assume red[simplified]: "~~redundant D N"  
      have "\<forall>E < D. E \<in> N \<longrightarrow> ?I \<Turnstile>h E"
        using cls_not_D not_le by fastforce
      hence "?I \<Turnstile>hs clss_lt N D"
        unfolding clss_lt_def true_clss_def Ball_def by blast
      thus False
        using redundant_is_abstract[simplified, OF red] not_d_interp unfolding abstract_red_def 
        using herbrand_true_clss_true_clss_cls_herbrand_true_clss by fast
    qed
    
  consider
    (L) P where "L = Pos P" and "S D = {#}" and "Max (set_mset D) = Pos P"
  | (Lneg) P where "L = Neg P"
    using LSD S_selects_neg_lits[of D L] by (cases L) auto
  thus False
    proof cases
      case L note P = this(1) and S = this(2) and max = this(3)
      have "count D L > 1"
        proof (rule ccontr)
          assume "~ ?thesis"
          hence count: "count D L = 1"
            unfolding D by auto
          have "\<not>?I\<Turnstile>h D"  
            using not_d_interp true_interp_imp_INTERP ground_resolution_with_selection_axioms 
              by blast
          hence "produces N D P"
            using not_empty empty finite \<open>D \<in> N\<close> count L 
              true_interp_imp_INTERP unfolding production_iff_produces unfolding production_unfold 
            by (auto simp add: max not_empty)
          hence "INTERP N \<Turnstile>h D"
            unfolding D
            by (metis pos_literal_in_imp_true_cls produces_imp_Pos_in_lits production_subseteq_INTERP singletonI subsetCE)
          thus False
            using not_d_interp by blast
        qed
      then obtain C' where C':"D = C' + {#Pos P#} + {#Pos P#}"
        unfolding D by (metis P add.left_neutral add_less_cancel_right count_single count_union multi_member_split)
      have sup: "superposition_rules D D (D - {#L#})"
        unfolding C' L by (auto simp add: superposition_rules.simps)
      have "C' + {#Pos P#}  #\<subset># C' + {#Pos P#} + {#Pos P#}"
        by auto
      moreover have "\<not>?I \<Turnstile>h (D - {#L#})"
        using not_d_interp unfolding C' L by auto
      ultimately have "C' + {#Pos P#} \<notin> N"
        by (metis (no_types, lifting) C' P add_diff_cancel_right' cls_not_D less_multiset
          multi_self_add_other_not_self not_le)
      have "D - {#L#} #\<subset># D"
        unfolding C' L by auto
      have c'_p_p: "C' + {#Pos P#} + {#Pos P#} - {#Pos P#} = C' + {#Pos P#}"
        by auto
      have "redundant (C' + {#Pos P#}) N"
        using saturated red sup \<open>D \<in> N\<close> unfolding saturated_def C' L c'_p_p by blast
      moreover have "C' + {#Pos P#}  \<subseteq># C' + {#Pos P#} + {#Pos P#}"
        by auto
      ultimately show False
        using red unfolding C' by (blast dest: redundant_mono)
    next
      case Lneg note L = this(1)
      have "P \<in> ?I"
        using not_d_interp unfolding D true_cls_def L by (auto split: split_if_asm)
      then obtain E where 
        DPN: "E + {#Pos P#} \<in> N" and 
        prod: "production N (E + {#Pos P#}) = {P}"
        using in_interp_is_produced by blast
      have "superposition_rules (E + {#Pos P#}) (C + {#Neg P#}) (E + C)"
        using superposition_l by fast
      hence "superposition N (N \<union> {E+C})"
        using DPN \<open>D \<in> N\<close> unfolding D L by (auto simp add: superposition.simps)
      have 
        PMax: "Pos P = MMax (E + {#Pos P#})" and 
        "count (E + {#Pos P#}) (Pos P) \<le> 1" and 
        "S (E + {#Pos P#}) = {#}" and
        " \<not>interp N (E + {#Pos P#}) \<Turnstile>h E + {#Pos P#}"
        using prod unfolding production_unfold by auto
      have "Neg P \<notin># E"
        using prod produces_imp_neg_notin_lits by force    
      hence "\<And>y. y \<in># (E + {#Pos P#}) \<Longrightarrow> count (E + {#Pos P#}) (Neg P) < count (C + {#Neg P#}) (Neg P)"
        by (auto split: split_if_asm)
      moreover have "\<And>y. y \<in># (E + {#Pos P#}) \<Longrightarrow> y < Neg P"
        using PMax by (metis DPN Max_less_iff empty finite_set_mset mem_set_mset_iff pos_less_neg set_mset_eq_empty_iff)
      moreover have "E + {#Pos P#} \<noteq> C + {#Neg P#}" 
        using prod produces_imp_neg_notin_lits by force
      ultimately have "E + {#Pos P#} #\<subset># C + {#Neg P#}"
        unfolding less_multiset\<^sub>H\<^sub>O by (metis add.left_neutral add_lessD1)
      have ce_lt_d: "C + E #\<subset># D"
        unfolding D L
        by (metis (mono_tags, lifting) Max_pos_neg_less_multiset One_nat_def PMax count_single less_multiset_plus_right_nonempty mult_less_trans single_not_empty union_less_mono2 zero_less_Suc)
      have "\<not>redundant (C + E) N"
        proof (rule ccontr)
          assume red'[simplified]: "\<not> ?thesis"
          have "clss_lt N (C + E) \<Turnstile>p C + E"
            using redundant_is_abstract[OF red'] unfolding abstract_red_def .
          hence "clss_lt N (C + E) \<Turnstile>p E + {#Pos P#} \<or> clss_lt N (C + E) \<Turnstile>p C + {#Neg P#}"
            using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or
            sorry
          show False sorry
        qed
      hence CEN: "C + E \<in> N"
        sorry
      have CED: "C + E \<noteq> D"
        using D ce_lt_d by auto
      have interp: "\<not> INTERP N \<Turnstile>h C + E"
      sorry
      show False using cls_not_D[OF CEN CED interp] ce_lt_d unfolding INTERP_def less_eq_multiset_def by auto
  qed
qed
    
end

lemma tautology_is_redundant:
  assumes "tautology C"
  shows "abstract_red C N"
  using assms unfolding abstract_red_def true_clss_cls_def tautology_def by auto
  
lemma subsumed_is_redundant:
  assumes AB: "A \<subset># B"
  and AN: "A \<in> N"
  shows "abstract_red B N"
proof -
  have "A \<in> clss_lt N B" using AN AB unfolding clss_lt_def 
    by (auto dest: less_eq_imp_le_multiset simp add: multiset_order.dual_order.order_iff_strict)
  thus ?thesis
    using AB unfolding abstract_red_def true_clss_cls_def Partial_Clausal_Logic.true_clss_def by blast
qed

inductive redundant :: "'a clause \<Rightarrow> 'a clauses \<Rightarrow> bool" where
subsumption: "A \<in> N \<Longrightarrow> A \<subset># B \<Longrightarrow> redundant B N"

lemma redundant_is_redundancy_criterion:
  fixes A :: "'a :: wellorder clause" and N :: "'a :: wellorder clauses"
  assumes "redundant A N"
  shows  "abstract_red A N"
  using assms 
proof (induction rule: redundant.induct)
  case (subsumption A B N)
  thus ?case
    using subsumed_is_redundant[of A N B] unfolding abstract_red_def clss_lt_def by auto
qed

lemma redundant_mono:
  "redundant A N \<Longrightarrow> A \<subseteq># B \<Longrightarrow>  redundant B N"
  apply (induction rule: redundant.induct)
  by (meson subset_mset.less_le_trans subsumption)

locale truc=
    selection S for S :: "nat clause \<Rightarrow> nat clause"
begin

interpretation truc: ground_ordered_resolution_with_redundancy S redundant
  using redundant_is_redundancy_criterion redundant_mono by unfold_locales auto

end

end