(*  Title:       Saturation Framework (originating from Ordered_Resolution_Prover.Inference_System)
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018
*)

section \<open>Saturation Framework\<close>

theory Saturation_Framework
  imports Ordered_Resolution_Prover.Herbrand_Interpretation
    Ordered_Resolution_Prover.Lazy_List_Liminf
    Ordered_Resolution_Prover.Lazy_List_Chain
begin

text \<open>
TODO
\<close>


subsection \<open>Preliminaries\<close>

text \<open>
Inferences have one distinguished main premise, any number of side premises, and a conclusion.
\<close>

type_synonym 'f formulas = "'f set"

locale consequence_relation =
  fixes
    Bot_F :: 'f and
    entails :: "'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool" (infix "|=" 50)
  assumes
    bot_implies_all: "{Bot_F} |= N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 |= N2" and
    all_formulas_entailed: "(\<forall>C \<in> N2. N1 |= {C}) \<Longrightarrow> N1 |= N2" and
    transitive_entails: "(N1 |= N2 \<and> N2 |= N3) \<Longrightarrow> N1 |= N3"
begin

lemma easy1: "(N1 |= N2) \<longleftrightarrow> (\<forall>C \<in> N2. N1 |= {C})"
by (meson all_formulas_entailed empty_subsetI insert_subset subset_entailed transitive_entails)

lemma easy2: "(N |= N1 \<and> N |= N2) \<longleftrightarrow> N |= (N1 \<union> N2)"
  apply (subst easy1)
  apply (subst (2) easy1)
  apply (subst (3) easy1)
  by auto

end

datatype 'f inference =
  Infer (prems_of: "'f list") (concl_of: "'f ")
  (* Infer (side_prems_of: "'a clause multiset") (main_prem_of: "'a clause") (concl_of: "'a clause") *)

(* abbreviation prems_of :: "'a inference \<Rightarrow> 'a clause multiset" where
  "prems_of \<gamma> \<equiv> side_prems_of \<gamma> + {#main_prem_of \<gamma>#}" *)


abbreviation concls_of :: "'f inference set \<Rightarrow> 'f set" where
  "concls_of \<iota> \<equiv> concl_of ` \<iota>"

(* FIXME: make an abbreviation *)
(* definition infer_from :: "'a clause set \<Rightarrow> 'a inference \<Rightarrow> bool" where
  "infer_from CC \<gamma> \<longleftrightarrow> set_mset (prems_of \<gamma>) \<subseteq> CC" *)

locale inference_system = consequence_relation +
  fixes 
    I :: "'f inference set" and
    Red_I :: "'f formulas \<Rightarrow> 'f inference set" and
    Red_F :: "'f formulas \<Rightarrow> 'f formulas"
  assumes
    Red_I_to_I: "Red_I N \<in> Pow I" and
    Red_F_Bot_F: "N |= {Bot_F} \<Longrightarrow> N - Red_F N |= {Bot_F}" and
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
    Red_I_of_I_to_N: "\<iota> \<in> I \<and> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N" and
    same_with_other_syntax: "{\<iota> \<in> I. (concl_of \<iota> \<in> N)} \<subseteq> Red_I N"
begin

definition Inf :: "'f formulas  \<Rightarrow> 'f inference set" where
  "Inf N = {\<iota> \<in> I. set (prems_of \<iota>) \<subseteq> N}"


lemma red_concl_to_red_inf: 
  assumes 
    i: "\<iota> \<in> I" and
    concl: "concl_of \<iota> \<in> Red_F N"
  shows "\<iota> \<in> Red_I N"
proof -
  have i2: "\<iota> \<in> Red_I (Red_F N)" by (simp add: Red_I_of_I_to_N i concl)
  then have i3: "\<iota> \<in> Red_I (N \<union> Red_F N)" by (simp add: Red_I_of_I_to_N concl i)
  also have red_n_subs: "Red_F N \<subseteq> Red_F (N \<union> Red_F N)" by (simp add: Red_F_of_subset)
  then have "\<iota> \<in> Red_I ((N \<union> Red_F N) - (Red_F N - N))" using Red_I_of_Red_F_subset i3
    by (meson Diff_subset subsetCE subset_trans)
  then show ?thesis by (metis Diff_cancel Diff_subset Un_Diff Un_Diff_cancel contra_subsetD 
    inference_system.Red_I_of_subset inference_system_axioms sup_bot.right_neutral)
qed

inductive "derive" :: "'f formulas \<Rightarrow> 'f formulas \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  unsat_preserving_derive: "(N |= {Bot_F} \<Longrightarrow> M |= {Bot_F}) \<Longrightarrow> M - N \<subseteq> Red_F N \<Longrightarrow> M \<turnstile> N"

definition saturated :: "'f formulas \<Rightarrow> bool" where 
  "saturated N \<equiv> Inf N \<subseteq> Red_I N"

definition Sup_Red_I_llist :: "'f formulas llist \<Rightarrow> 'f inference set" where
    "Sup_Red_I_llist D = (\<Union>i \<in> {i. enat i < llength D}. (Red_I (lnth D i)))"

lemma Sup_Red_I_unit: "Sup_Red_I_llist (LCons X LNil) = Red_I X" 
  using Sup_Red_I_llist_def enat_0_iff(1) by simp

definition fair :: "'f formulas llist \<Rightarrow> bool" where
  "fair D \<equiv> Inf (Liminf_llist D) \<subseteq> Sup_Red_I_llist D"

(* derivation are finite or infinite sequences - are lists the best datastructures to represent such them*)
(* inductive derivation :: "'f formulas list \<Rightarrow> bool" where
  empty: "derivation []"
  | one: "derivation [N]"
  | more: "derivation (N2 # T) \<Longrightarrow> (N2 |= {# Bot_F #} \<Longrightarrow> N1 |= {# Bot_F #}) 
            \<Longrightarrow> (N1 - N2) \<subseteq># Red_F N2 \<Longrightarrow> derivation (N1 # (N2 # T))"
*)
text \<open>TODO: replace in Lazy_List_Liminf\<close>
lemma (in-) elem_Sup_llist_imp_Sup_upto_llist': "x \<in> Sup_llist Xs \<Longrightarrow> \<exists>j < llength Xs. x \<in> Sup_upto_llist Xs j"
  unfolding Sup_llist_def Sup_upto_llist_def by blast 

lemma gt_Max_notin: \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x > Max A \<Longrightarrow> x \<notin> A\<close> by auto

lemma equiv_Sup_Liminf:
  assumes 
    in_Sup: "C \<in> Sup_llist D" and
    not_in_Liminf: "C \<notin> Liminf_llist D"
  shows
    "\<exists> i \<in> {i. enat (Suc i) < llength D}. C \<in> (lnth D i) - (lnth D (Suc i))"
proof -
  obtain i where C_D_i: "C \<in> Sup_upto_llist D i" and "i < llength D" 
    using elem_Sup_llist_imp_Sup_upto_llist' in_Sup by fast
  then obtain j where j: "j \<ge> i \<and> enat j < llength D \<and> C \<notin> lnth D j" using not_in_Liminf   
    unfolding Sup_llist_def chain_def Liminf_llist_def by auto
  obtain k where k: "C \<in> (lnth D k)" "enat k < llength D" "k \<le> i" using C_D_i 
    unfolding Sup_upto_llist_def by auto
  let ?S = "{i. i < j \<and> i \<ge> k \<and> C \<in> (lnth D i)}"
  define l where "l \<equiv> Max ?S"
  have \<open>k \<in> {i. i < j \<and> k \<le> i \<and> C \<in> lnth D i}\<close> using k j by (auto simp: order.order_iff_strict)
  then have nempty: "{i. i < j \<and> k \<le> i \<and> C \<in> lnth D i} \<noteq> {}" by auto 
  then have l_prop: "l < j \<and> l \<ge> k \<and> C \<in> (lnth D l)" using Max_in[of ?S, OF _ nempty] unfolding l_def by auto 
  then have "C \<in> (lnth D l) - (lnth D (Suc l))" using j gt_Max_notin[OF _ nempty, of "Suc l"] 
    unfolding l_def[symmetric] by (auto intro: Suc_lessI)
  then show ?thesis apply (rule bexI[of _ l]) using l_prop j 
    apply auto 
    by (metis Suc_leI dual_order.order_iff_strict enat_ord_simps(2) less_trans)
qed

text \<open>lemma 2 in Uwe's notes\<close>
lemma Red_in_Sup: 
  assumes deriv: "chain (\<turnstile>) D"
  shows "Sup_llist D - Liminf_llist D \<subseteq> Red_F (Sup_llist D)"
proof
  fix C
  assume C_in_subset: "C \<in> Sup_llist D - Liminf_llist D"
  {
    fix C i
    assume 
      in_ith_elem: "C \<in> (lnth D i) - (lnth D (Suc i))" and
      i: "enat (Suc i) < llength D"
    have "(lnth D i) \<turnstile> (lnth D (Suc i))" using i deriv in_ith_elem chain_lnth_rel by auto
    then have "C \<in> Red_F (lnth D (Suc i))" using in_ith_elem derive.cases by blast
    then have "C \<in> Red_F (Sup_llist D)" using Red_F_of_subset 
      by (meson contra_subsetD i lnth_subset_Sup_llist)
  }
  then show "C \<in> Red_F (Sup_llist D)" using equiv_Sup_Liminf[of C] C_in_subset by fast
qed

text \<open>lemma 3 in Uwe's notes part 1/2\<close>
lemma Red_I_subset_Liminf: 
  assumes deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_I (lnth D i) \<subseteq> Red_I (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_I (Sup_llist D) \<subseteq> Red_I ((Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)))\<close> 
    using Red_I_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>(Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_I_Sup_in_Liminf: \<open>Red_I (Sup_llist D) \<subseteq> Red_I (Liminf_llist D)\<close> using Sup_in_diff by auto
  have \<open>(lnth D i) \<subseteq> (Sup_llist D)\<close> unfolding Sup_llist_def using i by blast
  then have "Red_I (lnth D i) \<subseteq> Red_I (Sup_llist D)" using Red_I_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_I_Sup_in_Liminf by auto
qed

text \<open>lemma 3 in Uwe's notes part 2/2\<close>
lemma Red_F_subset_Liminf:
 assumes deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>Red_F (lnth D i) \<subseteq> Red_F (Liminf_llist D)\<close>
proof -
  have Sup_in_diff: \<open>Red_F (Sup_llist D) \<subseteq> Red_F ((Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)))\<close> 
    using Red_F_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>(Sup_llist D) - ((Sup_llist D) - (Liminf_llist D)) = Liminf_llist D\<close> 
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_F_Sup_in_Liminf: \<open>Red_F (Sup_llist D) \<subseteq> Red_F (Liminf_llist D)\<close>
    using Sup_in_diff by auto
  have \<open>(lnth D i) \<subseteq> (Sup_llist D)\<close> unfolding Sup_llist_def using i by blast
  then have "Red_F (lnth D i) \<subseteq> Red_F (Sup_llist D)" using Red_F_of_subset 
    unfolding Sup_llist_def by auto 
  then show ?thesis using Red_F_Sup_in_Liminf by auto
qed

text \<open>lemma 4 in Uwe's notes\<close>
lemma i_in_Liminf_or_Red_F:
  assumes deriv: \<open>chain (\<turnstile>) D\<close> and
    i: \<open>enat i < llength D\<close>
  shows \<open>(lnth D i) \<subseteq> (Liminf_llist D) \<union> (Red_F (Liminf_llist D))\<close>
proof
  fix C
  assume C: \<open>C \<in> (lnth D i)\<close>
  and C_not_Liminf: \<open>C \<notin> (Liminf_llist D)\<close>
  have \<open>C \<in> Sup_llist D\<close> unfolding Sup_llist_def using C i by auto
  then obtain j where j: \<open>C \<in> (lnth D j) - (lnth D (Suc j))\<close> \<open>enat (Suc j) < llength D\<close> 
    using equiv_Sup_Liminf[of C D] C_not_Liminf by auto
  then have \<open>C \<in> Red_F (lnth D (Suc j))\<close> 
    using deriv by (meson chain_lnth_rel contra_subsetD derive.cases)
  then have \<open>C \<in> Red_F (Liminf_llist D)\<close> using Red_F_subset_Liminf[of D "Suc j"] deriv j(2) by blast

end

locale static_refutational_complete_inference_system = inference_system +
  assumes
    static_refutational_complete: "saturated N \<and> N |= {Bot_F} \<Longrightarrow> Bot_F \<in> N"
begin

end

locale dynamic_refutational_complete_inference_system = inference_system +
  assumes
    dynamic_refutational_complete: "fair D \<and> (lnth D 0) |= {Bot_F}
      \<Longrightarrow> \<exists>i \<in> {i. enat i < llength D}. Bot_F \<in> (lnth D i)"
begin



sublocale static_refutational_complete_inference_system
proof standard
  fix N
  assume 
    saturated_N: "saturated N \<and> N |= {Bot_F}"
  define D where "D = LCons N LNil"
  have liminf_is_N: "Liminf_llist D = N" by (simp add: D_def Liminf_llist_LCons)
  also have head_D: "N = lnth D 0" by (simp add: D_def)
  also have "Sup_Red_I_llist D = Red_I N" by (simp add: D_def Sup_Red_I_unit)
  then have fair_D: "fair D" using saturated_N by (simp add: fair_def saturated_def liminf_is_N)  
  obtain i where "Bot_F \<in> (lnth D i)" and \<open>i < llength D\<close>
    using dynamic_refutational_complete fair_D head_D saturated_N 
    by auto
  then have "i = 0"
    by (auto simp: D_def enat_0_iff)
  show \<open>Bot_F \<in> N\<close>
    using \<open>Bot_F \<in> (lnth D i)\<close> unfolding \<open>i = 0\<close> head_D[symmetric] .
qed


end












(* 
text \<open>
Satisfiability preservation is a weaker requirement than soundness.
\<close>

locale sat_preserving_inference_system = inference_system +
  assumes \<Gamma>_sat_preserving: "satisfiable N \<Longrightarrow> satisfiable (N \<union> concls_of (inferences_from N))"
*)

locale sound_inference_system = inference_system +
  assumes I_sound: "Infer CC C \<in> I \<Longrightarrow> mset CC |= {# C #}"
begin

(* lemma \<Gamma>_sat_preserving:
  assumes sat_n: "satisfiable N"
  shows "satisfiable (N \<union> concls_of (inferences_from N))"
proof -
  obtain I where i: "I \<Turnstile>s N"
    using sat_n by blast
  then have "\<And>CC D E. Infer CC D E \<in> \<Gamma> \<Longrightarrow> set_mset CC \<subseteq> N \<Longrightarrow> D \<in> N \<Longrightarrow> I \<Turnstile> E"
    using \<Gamma>_sound unfolding true_clss_def true_cls_mset_def by (simp add: subset_eq)
  then have "\<And>\<gamma>. \<gamma> \<in> \<Gamma> \<Longrightarrow> infer_from N \<gamma> \<Longrightarrow> I \<Turnstile> concl_of \<gamma>"
    unfolding infer_from_def by (case_tac \<gamma>) clarsimp
  then have "I \<Turnstile>s concls_of (inferences_from N)"
    unfolding inferences_from_def image_def true_clss_def infer_from_def by blast
  then have "I \<Turnstile>s N \<union> concls_of (inferences_from N)"
    using i by simp
  then show ?thesis
    by blast
qed

sublocale sat_preserving_inference_system
  by unfold_locales (erule \<Gamma>_sat_preserving) *)

end

locale reductive_inference_system = inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  assumes \<Gamma>_reductive: "\<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> < main_prem_of \<gamma>"


subsection \<open>Refutational Completeness\<close>

text \<open>
Refutational completeness can be established once and for all for counterexample-reducing inference
systems. The material formalized here draws from both the general framework of Section 4.2 and the
concrete instances of Section 3.
\<close>

locale counterex_reducing_inference_system =
  inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  fixes I_of :: "'a clause set \<Rightarrow> 'a interp"
  assumes \<Gamma>_counterex_reducing:
    "{#} \<notin> N \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> D \<Longrightarrow> (\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> C \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>CC E. set_mset CC \<subseteq> N \<and> I_of N \<Turnstile>m CC \<and> Infer CC D E \<in> \<Gamma> \<and> \<not> I_of N \<Turnstile> E \<and> E < D"
begin

lemma ex_min_counterex:
  fixes N :: "('a :: wellorder) clause set"
  assumes "\<not> I \<Turnstile>s N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> C \<and> (\<forall>D \<in> N. D < C \<longrightarrow> I \<Turnstile> D)"
proof -
  obtain C where "C \<in> N" and "\<not> I \<Turnstile> C"
    using assms unfolding true_clss_def by auto
  then have c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> C}"
    by blast
  show ?thesis
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset c_in] by blast
qed

(* Theorem 4.4 (generalizes Theorems 3.9 and 3.16) *)

theorem saturated_model:
  assumes
    satur: "saturated N" and
    ec_ni_n: "{#} \<notin> N"
  shows "I_of N \<Turnstile>s N"
proof -
  have ec_ni_n: "{#} \<notin> N"
    using ec_ni_n by auto

  {
    assume "\<not> I_of N \<Turnstile>s N"
    then obtain D where
      d_in_n: "D \<in> N" and
      d_cex: "\<not> I_of N \<Turnstile> D" and
      d_min: "\<And>C. C \<in> N \<Longrightarrow> C < D \<Longrightarrow> I_of N \<Turnstile> C"
      by (meson ex_min_counterex)
    then obtain CC E where
      cc_subs_n: "set_mset CC \<subseteq> N" and
      inf_e: "Infer CC D E \<in> \<Gamma>" and
      e_cex: "\<not> I_of N \<Turnstile> E" and
      e_lt_d: "E < D"
      using \<Gamma>_counterex_reducing[OF ec_ni_n] not_less by metis
    from cc_subs_n inf_e have "E \<in> N"
      using d_in_n satur by (blast dest: saturatedD)
    then have False
      using e_cex e_lt_d d_min not_less by blast
  }
  then show ?thesis
    by satx
qed

text \<open>
Cf. Corollary 3.10:
\<close>

corollary saturated_complete: "saturated N \<Longrightarrow> \<not> satisfiable N \<Longrightarrow> {#} \<in> N"
  using saturated_model by blast

end


subsection \<open>Compactness\<close>

text \<open>
Bachmair and Ganzinger claim that compactness follows from refutational completeness but leave the
proof to the readers' imagination. Our proof relies on an inductive definition of saturation in
terms of a base set of clauses.
\<close>

context inference_system
begin

inductive_set saturate :: "'a clause set \<Rightarrow> 'a clause set" for CC :: "'a clause set" where
  base: "C \<in> CC \<Longrightarrow> C \<in> saturate CC"
| step: "Infer CC' D E \<in> \<Gamma> \<Longrightarrow> (\<And>C'. C' \<in># CC' \<Longrightarrow> C' \<in> saturate CC) \<Longrightarrow> D \<in> saturate CC \<Longrightarrow>
    E \<in> saturate CC"

lemma saturate_mono: "C \<in> saturate CC \<Longrightarrow> CC \<subseteq> DD \<Longrightarrow> C \<in> saturate DD"
  by (induct rule: saturate.induct) (auto intro: saturate.intros)

lemma saturated_saturate[simp, intro]: "saturated (saturate N)"
  unfolding saturated_def inferences_from_def infer_from_def image_def
  by clarify (rename_tac x, case_tac x, auto elim!: saturate.step)

lemma saturate_finite: "C \<in> saturate CC \<Longrightarrow> \<exists>DD. DD \<subseteq> CC \<and> finite DD \<and> C \<in> saturate DD"
proof (induct rule: saturate.induct)
  case (base C)
  then have "{C} \<subseteq> CC" and "finite {C}" and "C \<in> saturate {C}"
    by (auto intro: saturate.intros)
  then show ?case
    by blast
next
  case (step CC' D E)
  obtain DD_of where
    "\<And>C. C \<in># CC' \<Longrightarrow> DD_of C \<subseteq> CC \<and> finite (DD_of C) \<and> C \<in> saturate (DD_of C)"
    using step(3) by metis
  then have
    "(\<Union>C \<in> set_mset CC'. DD_of C) \<subseteq> CC"
    "finite (\<Union>C \<in> set_mset CC'. DD_of C) \<and> set_mset CC' \<subseteq> saturate (\<Union>C \<in> set_mset CC'. DD_of C)"
    by (auto intro: saturate_mono)
  then obtain DD where
    d_sub: "DD \<subseteq> CC" and d_fin: "finite DD" and in_sat_d: "set_mset CC' \<subseteq> saturate DD"
    by blast
  obtain EE where
    e_sub: "EE \<subseteq> CC" and e_fin: "finite EE" and in_sat_ee: "D \<in> saturate EE"
    using step(5) by blast
  have "DD \<union> EE \<subseteq> CC"
    using d_sub e_sub step(1) by fast
  moreover have "finite (DD \<union> EE)"
    using d_fin e_fin by fast
  moreover have "E \<in> saturate (DD \<union> EE)"
    using in_sat_d in_sat_ee step.hyps(1)
    by (blast intro: inference_system.saturate.step saturate_mono)
  ultimately show ?case
    by blast
qed

end

context sound_inference_system
begin

theorem saturate_sound: "C \<in> saturate CC \<Longrightarrow> I \<Turnstile>s CC \<Longrightarrow> I \<Turnstile> C"
  by (induct rule: saturate.induct) (auto simp: true_cls_mset_def true_clss_def \<Gamma>_sound)

end

context sat_preserving_inference_system
begin

text \<open>
This result surely holds, but we have yet to prove it. The challenge is: Every time a new clause is
introduced, we also get a new interpretation (by the definition of
@{text sat_preserving_inference_system}). But the interpretation we want here is then the one that
exists "at the limit". Maybe we can use compactness to prove it.
\<close>

theorem saturate_sat_preserving: "satisfiable CC \<Longrightarrow> satisfiable (saturate CC)"
  oops

end

locale sound_counterex_reducing_inference_system =
  counterex_reducing_inference_system + sound_inference_system
begin

text \<open>
Compactness of clausal logic is stated as Theorem 3.12 for the case of unordered ground resolution.
The proof below is a generalization to any sound counterexample-reducing inference system. The
actual theorem will become available once the locale has been instantiated with a concrete inference
system.
\<close>

theorem clausal_logic_compact:
  fixes N :: "('a :: wellorder) clause set"
  shows "\<not> satisfiable N \<longleftrightarrow> (\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD)"
proof
  assume "\<not> satisfiable N"
  then have "{#} \<in> saturate N"
    using saturated_complete saturated_saturate saturate.base unfolding true_clss_def by meson
  then have "\<exists>DD \<subseteq> N. finite DD \<and> {#} \<in> saturate DD"
    using saturate_finite by fastforce
  then show "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
    using saturate_sound by auto
next
  assume "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
  then show "\<not> satisfiable N"
    by (blast intro: true_clss_mono)
qed

end

end
