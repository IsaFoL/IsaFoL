theory Propo_CDCL2
imports Partial_Annotated_Clausal_Logic List_More "../Bachmair_Ganzinger/Lazy_List_Limit"

begin

type_synonym ('v, 'lvl, 'mark) cdcl_state = "('v, 'lvl, 'mark) annoted_lits \<times> 'v clauses"


inductive propagate :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
propagate[intro]: "C + {#L#} \<in> N \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L M \<Longrightarrow> propagate (M, N) ((Propagated L mark) # M, N)"

inductive_cases propagateE[elim]: "propagate S T"
thm propagateE

inductive decide ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
decide[intro]: "undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N \<Longrightarrow> decide (M, N) (Marked L d # M, N)"

inductive_cases decideE[elim]: "decide S S'"

inductive backjump  ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
backjump: "C \<in> N \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C 
  \<Longrightarrow> undefined_lit L (F' @ Marked K d # F) \<Longrightarrow> atm_of L \<in> atms_of_m N
  \<Longrightarrow> N \<Turnstile>p {#L#} + C'
  \<Longrightarrow> backjump (F' @ Marked K d # F, N) (Propagated L l #  F, N)"
inductive_cases backjumpE[elim]: "backjump S S'"

inductive dpll :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
bj_decide:  "decide S S' \<Longrightarrow> dpll S S'" |
bj_propagate: "propagate S S' \<Longrightarrow> dpll S S'" |
bj_backjump:  "backjump S S' \<Longrightarrow> dpll S S'"

lemmas dpll_induct = dpll.induct[split_format(complete)]
lemma dpll_all_induct[consumes 1, case_names decide propagate backjump]:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits" and N ::" 'v clauses"
  assumes "dpll (M, N) (M', N')" and
  "\<And>L M N d. undefined_lit L M \<Longrightarrow> atm_of L \<in> atms_of_m N \<Longrightarrow> P M N (Marked L d # M) N" and
  "\<And>C L N M mark. C + {#L#} \<in> N \<Longrightarrow> M \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L M \<Longrightarrow> P M N ((Propagated L mark) # M) N" and
  "\<And>C N F' K d F L C' l. C \<in> N \<Longrightarrow> F' @ Marked K d # F \<Turnstile>as CNot C \<Longrightarrow> undefined_lit L (F' @ Marked K d # F) 
  \<Longrightarrow> atm_of L \<in> atms_of_m N
  \<Longrightarrow> N \<Turnstile>p {#L#} + C'
  \<Longrightarrow> P (F' @ Marked K d # F) N (Propagated L l #  F) N"
  shows "P M N M' N'"
  using assms(1) by (induction rule: dpll_induct) (auto dest!: assms(2,3,4))

 
inductive learn  ::  "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
learn: "N \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m N \<Longrightarrow> learn (M, N) (M, insert C N)"
inductive_cases learnE[elim]: "learn S S'"

inductive forget :: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
forget: "N - {C} \<Turnstile>p C \<Longrightarrow> C \<in> N \<Longrightarrow> forget (M, N) (M, N - {C})"
inductive_cases forgetE[elim]: "forget S S'"


    
inductive cdcl:: "('v, 'lvl, 'mark) cdcl_state \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> bool" where
c_dpll:  "dpll S S' \<Longrightarrow> cdcl S S'" |
c_learn:  "learn S S' \<Longrightarrow> cdcl S S'" |
c_forget:  "forget S S' \<Longrightarrow> cdcl S S'"
  
lemmas cdcl_induct = cdcl.induct[split_format(complete)]
lemma cdcl_all_induct[consumes 1, case_names dpll learn forget]:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits" and N ::" 'v clauses"
  assumes "cdcl (M, N) (M', N')" and
  "\<And>M N M' N'. dpll (M, N) (M', N') \<Longrightarrow> P M N M' N'" and
  learn: "\<And>M N C. N \<Turnstile>p C \<Longrightarrow> atms_of C \<subseteq> atms_of_m N \<Longrightarrow>  P M N M (insert C N)" and
  "\<And>M N C. N - {C} \<Turnstile>p C \<Longrightarrow> C \<in> N \<Longrightarrow>  P M N M (N - {C})"
  shows "P M N M' N'"
  using assms(1) by (induction rule: cdcl_induct)
    (auto intro!: learn dest!: assms(2,3,4))



lemma dpll_no_dup:
  assumes "dpll (M, N) (M', N')"
  and "no_dup M"
  shows "no_dup M'" 
  using assms by (induction rule: dpll_all_induct) (auto simp add: defined_lit_map)

lemma cdcl_no_dup:
  assumes "cdcl (M, N) (M', N')"
  and "no_dup M"
  shows "no_dup M'" 
  using assms by (induction rule: cdcl_all_induct) (auto intro: dpll_no_dup)

lemma cdcl_consistent:
  assumes "cdcl (M, N) (M', N')"
  and "no_dup M"
  shows "consistent_interp (lits_of M')" 
  using cdcl_no_dup[OF assms] distinctconsistent_interp by fast

lemma dpll_sat_iff:
  assumes "dpll (M, N) (M', N')"
  shows "I \<Turnstile>s N \<longleftrightarrow> I \<Turnstile>s N'"
  using assms by (induction rule: dpll_all_induct) auto

(*TODO Move*)
lemma total_over_set_in_total:
  "total_over_set I (atms_of_m N) \<Longrightarrow> C : N \<Longrightarrow> total_over_set I (atms_of C)"
  unfolding total_over_set_def atms_of_m_def by fastforce
  
lemma cdcl_sat_iff:
  assumes "cdcl (M, N) (M', N')"
  and "consistent_interp I" and "total_over_m I N"
  shows "I \<Turnstile>s N \<longleftrightarrow> I \<Turnstile>s N'"
  using assms apply (induction rule: cdcl_all_induct) 
     using dpll_sat_iff apply blast
    unfolding true_clss_cls_def total_over_m_def apply (metis atms_of_m_singleton atms_of_m_union sup.orderE true_clss_insert)
  unfolding true_clss_insert atms_of_m_singleton atms_of_m_union by (metis atms_of_m_insert insert_Diff total_over_set_union true_clss_insert)


lemma dpll_atms_of_m_clauses_inv:
  assumes "dpll (M, N) (M', N')"
  shows "atms_of_m N = atms_of_m N'"
  using assms by (induction rule: dpll_all_induct) auto

lemma dpll_atms_of_m_clauses_decreasing:
  assumes "cdcl (M, N) (M', N')"
  shows "atms_of_m N' \<subseteq> atms_of_m N"
  using assms by (induction rule: cdcl_all_induct) (auto dest!: dpll_atms_of_m_clauses_inv simp add: atms_of_m_def)
  
lemma dpll_atms_in_trail:
  assumes "dpll (M, N) (M', N')"
  and "atm_of ` (lits_of M) \<subseteq> atms_of_m N"
  shows "atm_of ` (lits_of M') \<subseteq> atms_of_m N'"
  using assms by (induction rule: dpll_all_induct) auto
  
lemma dpll_atms_in_trail_in_set:
  assumes "dpll (M, N) (M', N')" and
  "atms_of_m N \<subseteq> A" and 
  "atm_of ` (lits_of M) \<subseteq> A"
  shows "atm_of ` (lits_of M') \<subseteq> A"
  using assms by (induction rule: dpll_all_induct) auto

lemma cdcl_atms_in_trail:
  assumes "cdcl (M, N) (M', N')"
  and "atm_of ` (lits_of M) \<subseteq> atms_of_m N"
  shows "atm_of ` (lits_of M') \<subseteq> atms_of_m N"
  using assms 
  by (induction rule: cdcl_all_induct) 
    (simp_all add: dpll_atms_in_trail dpll_atms_of_m_clauses_inv)


lemma cdcl_atms_in_trail_in_set:
  assumes "cdcl (M, N) (M', N')" and 
  "atms_of_m N \<subseteq> A" and 
  "atm_of ` (lits_of M) \<subseteq> A"
  shows "atm_of ` (lits_of M') \<subseteq> A"
  using assms 
  by (induction rule: cdcl_all_induct) 
    (simp_all add: dpll_atms_in_trail_in_set dpll_atms_of_m_clauses_inv)

subsection \<open>Measure\<close>


subsection\<open>Adding the measure based on Nieuwenhuis et al.\<close>
abbreviation latm where
  "latm M N \<equiv> card (atms_of_m N) - length M"

abbreviation synchronise :: "'a \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'a list \<times> 'b list" where
"synchronise a l a' l' \<equiv> 
  (take (min (length l) (length l')) l @[a], 
    take (min (length l) (length l')) l' @ [a'])"

fun skip_first_if_empty where
"skip_first_if_empty ((a, []) # l) = l" |
"skip_first_if_empty l = l"

fun trail_mes ::  "'v literal multiset set \<Rightarrow> ('v, 'lvl, 'mark) cdcl_state \<Rightarrow> nat list" where
"trail_mes A (M, N) = 
  (map (\<lambda>(_, propa). latm propa A) (rev (get_all_marked_decomposition M)))"
  
abbreviation trail_mes_build where
"trail_mes_build \<equiv> \<lambda>A (M, N) (M', N').
  synchronise (latm M A) (trail_mes A (M, N)) 
              (latm M' A) (trail_mes A (M', N))"

lemma length_get_all_marked_decomposition_append_Marked:
  "length (get_all_marked_decomposition (F' @ Marked K d # F)) =
    length (get_all_marked_decomposition F') 
    + length (get_all_marked_decomposition (Marked K d # F))
    - 1"
    by (induction F' rule: marked_lit_list_induct)
      auto
lemma take_length_get_all_marked_decomposition_marked_sandwich:
  "take (length (get_all_marked_decomposition F)) 
      (map (\<lambda>(_, propa). latm propa A) (rev (get_all_marked_decomposition (F' @ Marked K d # F))))
      =
     map (\<lambda>(_, propa). latm propa A) (rev (get_all_marked_decomposition F)) 
    "
proof (induction F' rule: marked_lit_list_induct)
  case nil
  thus ?case by auto
next
  case (marked K)
  thus ?case by (simp add: length_get_all_marked_decomposition_append_Marked)
next
  case (proped L m F') note IH = this(1)
  obtain a b l where F': "get_all_marked_decomposition (F' @ Marked K d # F) = (a, b) # l"
    by (cases "get_all_marked_decomposition (F' @ Marked K d # F)") auto
  have "length (get_all_marked_decomposition F) - length l = 0"
    using length_get_all_marked_decomposition_append_Marked[of F' K d F]
    unfolding F' by (cases "get_all_marked_decomposition F'") auto
  thus ?case
    using IH by (simp add: F')
qed

lemma dpll_trail_mes_decreasing:
  fixes M :: "('v, 'lvl, 'mark) annoted_lits " and N :: "'v clauses"
  assumes "dpll (M, N) (M', N')" and 
  "atms_of_m N \<subseteq> atms_of_m A" and
  "atm_of ` lits_of M \<subseteq> atms_of_m A" and
  "no_dup M" and
  finite: "finite A"
  shows "trail_mes_build A (M', N') (M, N) \<in> lenlex less_than"
  using assms
proof (induction rule: dpll_all_induct)
  case (propagate C L N M d) note CLN = this(1) and MC =this(2) and undef_L = this(3) and A = this(4) and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L d # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_propagate propagate.propagate[OF propagate.hyps] A MA by blast

  have no_dup: "no_dup (Propagated L d # M)"  
    using defined_lit_map propagate.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp
  
  hence "length (Propagated L d # M) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup] 
    by (simp add: card_mono)
  hence latm: "latm b A = Suc (latm (Propagated L d # b) A)"
    using b_le_M by force 
  thus ?case 
    by (auto simp: lenlex_conv lex_conv latm M)
next  
  case (decide L M N lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4) and MA = this(5)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Marked L lv # M) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set bj_decide decide.decide[OF decide.hyps] A MA  NA by blast 

  have no_dup: "no_dup (Marked L lv # M)"  
    using defined_lit_map decide.prems(3) undef_L by auto
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp
  
  hence "length (Marked L lv # M) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup] 
    by (simp add: card_mono)
  hence latm: "latm M A = Suc (latm (Marked L lv # M) A)"
    using b_le_M by force 
  have " (map (\<lambda>(_, propa). latm propa A) (rev (get_all_marked_decomposition M)) @ [card (atms_of_m A) - Suc (length M)], map (\<lambda>(_, propa). latm propa A) (rev (get_all_marked_decomposition M)) @ [latm M A]) \<in> lenlex less_than"
    unfolding M 
    unfolding lenlex_conv lex_conv latm M
    by (auto intro: exI[of _ "map (\<lambda>(_, propa). latm propa A) (rev l) @ [latm b A]"])
  thus ?case by auto
next
  case (backjump C N F' K d F L _ lv) note undef_L = this(1) and MC =this(2) and NA = this(3) and A = this(4) and MA = this(5) and nd = this(8)
  have "atms_of_m N' \<subseteq> atms_of_m A"
    using assms(1) assms(2) dpll_atms_of_m_clauses_inv by blast
  have incl: "atm_of ` lits_of (Propagated L lv # F) \<subseteq> atms_of_m A"
    using dpll_atms_in_trail_in_set backjump.hyps(4) backjump.prems(1) backjump.prems(2) by auto

  have no_dup: "no_dup (Propagated L lv # F)"  
    using bj_backjump backjump.backjump[OF backjump.hyps] dpll_no_dup nd by blast
  obtain a b l where M: "get_all_marked_decomposition M = (a, b) # l"
    by (case_tac "get_all_marked_decomposition M") auto
  have b_le_M: "length b \<le> length M"
    using get_all_marked_decomposition_decomp[of M] by (simp add: M)
  have "finite (atms_of_m A)" using finite by simp
  
  hence F_le_A: "length (Propagated L lv # F) \<le>  card (atms_of_m A)"
    using incl finite unfolding distinctlength_eq_card_atm_of_lits_of[OF no_dup] 
    by (simp add: card_mono)
 
  have min: "min ((length (get_all_marked_decomposition F))) (length (get_all_marked_decomposition (F' @ Marked K d # F))) = length (get_all_marked_decomposition F)"
    unfolding length_get_all_marked_decomposition_append_Marked by (simp add: min_def)

  obtain a b l where F: "get_all_marked_decomposition F = (a, b) # l"
   by (cases "get_all_marked_decomposition F") auto
  
  hence "F = b @ a"
    using get_all_marked_decomposition_decomp[of "Propagated L lv # F" a "Propagated L lv # b"] by simp
  hence latm: "latm b A = Suc (latm (Propagated L lv # b) A)"
     using F_le_A by simp
  show ?case  
    apply (simp add: min)
    using take_length_get_all_marked_decomposition_marked_sandwich[of F A F' K d] 
    by (auto simp add: F latm lenlex_conv lex_conv)
qed

lemma
  assumes "trail_mes_build A (M, N) (M', N') \<in> lenlex less_than"
  and "length M' \<le> n"
  and "length N' \<le> n"
  shows False
  
  
  
coinductive derivation :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> bool" where
  singleton: "derivation R (LCons N LNil)"
| cons: "derivation R Ns \<Longrightarrow> R M (lhd Ns) \<Longrightarrow> derivation R (LCons M Ns)"

lemma
  derivation_LNil[simp]: "\<not> derivation R LNil" and
  lnull_derivation: "lnull Ns \<Longrightarrow> \<not> derivation R Ns"
  by (auto elim: derivation.cases)

lemma derivation_ldropn:
  assumes "derivation R Ns" and "enat n < llength Ns"
  shows "derivation R (ldropn n Ns)"
using assms
proof (induct n arbitrary: Ns)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  from Suc.prems(2) have len: "enat n < llength Ns"
    using Suc_ile_eq less_imp_le by blast
  hence "derivation R (ldropn n Ns)"
    using Suc.hyps Suc.prems(1) by blast
  hence "derivation R (LCons (lnth Ns n) (ldropn (Suc n) Ns))"
    using len by (simp add: ldropn_Suc_conv_ldropn)
  thus ?case
    using Suc.prems(2) by (auto elim: derivation.cases simp: ldropn_eq_LNil)
qed

lemma derivation_lnth_rel:
  assumes
    deriv: "derivation R Ns" and
    len: "enat (Suc j) < llength Ns"
  shows "R (lnth Ns j) (lnth Ns (Suc j))"
proof -
  def Ms \<equiv> "ldropn j Ns"
  have "llength Ms > 1"
    unfolding Ms_def using len
    by (metis eSuc_enat funpow_swap1 ldropn_0 ldropn_def ldropn_ltl lnull_ldropn not_less one_eSuc
      zero_enat_def)
  obtain M0 M1 Ms' where ms: "Ms = LCons M0 (LCons M1 Ms')"
    unfolding Ms_def by (metis Suc_ile_eq ldropn_Suc_conv_ldropn len less_imp_not_less not_less)
  have "derivation R Ms"
  unfolding Ms_def
  proof -
    have "Ms \<noteq> LNil" and "lhd Ms = M0"
      unfolding ms by simp_all
    thus "derivation R (ldropn j Ns)"
      unfolding Ms_def using deriv derivation_ldropn ldropn_all not_less by blast
  qed
  hence "R M0 M1"
    unfolding ms by (auto elim: derivation.cases)
  thus ?thesis
    using Ms_def unfolding ms by (metis ldropn_Suc_conv_ldropn ldropn_eq_LConsD llist.inject)
qed


lemma
  assumes "derivation dpll Ns"
  shows "llength Ns < \<infinity>"
  using assms
apply (induction Ns)  
  apply auto
  oops
lemma  
  assumes fin:  "finite A"
  shows "wf ({(S', S). (atm_of ` lits_of (fst S) \<subseteq> atms_of_m A \<and> atms_of_m (snd S) \<subseteq> atms_of_m A \<and> no_dup (fst S)) \<and> dpll S S'})"
  unfolding wf_def apply auto
sorry



lemma dpll_forget_disjoint:
  "dpll S S' \<Longrightarrow> \<not>forget S' S"
  by (induction rule: dpll.induct) auto

lemma dpll_learn_disjoint:
  "dpll S S' \<Longrightarrow> \<not>learn S' S"
  by (induction rule: dpll.induct) (auto elim!: decideE propagateE backjumpE)

lemma "wf ({(S', S). dpll S' S} \<union> {(S', S). forget S' S \<or> learn S S'})"
oops  
  
  
  
  
  
  
  
  
  
  
  
text \<open>Needs that N is not a tautology\<close>
lemma
  assumes "I \<Turnstile>s M" and
  MN: "M \<Turnstile>p N" and
  cons: "consistent_interp I"
  shows "I \<Turnstile> N"
proof -
  let ?I1 = "I \<union> {Pos P| P. P \<in> atms_of_m (M \<union> {N}) \<and> P \<notin> atm_of ` I}"
  have "consistent_interp ?I1"
    using cons unfolding consistent_interp_def
    apply (auto simp add: atms_of_def atms_of_s_def rev_image_eqI )
     apply (metis atm_of_uminus image_iff literal.sel(1))+
    done
  moreover have "total_over_set ?I1 (atms_of_m (M \<union> {N}))"
    unfolding total_over_set_def
      apply auto
      by (case_tac x, auto)+
    
  moreover have "?I1 \<Turnstile>s M" by (simp add: assms(1))
  ultimately have 1: "?I1 \<Turnstile> N"
    using MN unfolding true_clss_cls_def total_over_m_def by auto

  let ?I2 = "I \<union> {Neg P| P. P \<in> atms_of_m (M \<union> {N}) \<and> P \<notin> atm_of ` I}"
  have "consistent_interp ?I2"
    using cons unfolding consistent_interp_def
    apply (auto simp add: atms_of_def atms_of_s_def rev_image_eqI)
    apply (metis atm_of_uminus image_iff literal.sel(2))+
    done
  moreover have "total_over_set ?I2 (atms_of_m (M \<union> {N}))"
    unfolding total_over_set_def
      apply auto
      by (case_tac x, auto)+
    
  moreover have "?I2 \<Turnstile>s M" by (simp add: assms(1))
  ultimately have 2: "?I2 \<Turnstile> N"
    using MN unfolding true_clss_cls_def total_over_m_def by auto

  show "I \<Turnstile> N"
    using 1 2 unfolding true_cls_def apply auto sorry
    (*does not work for tautologies*)
oops    


end
