theory Background
  imports
    Simple_Clause_Learning.SCL_FOL
    Simple_Clause_Learning.Correct_Termination
    Simple_Clause_Learning.Initial_Literals_Generalize_Learned_Literals
    Simple_Clause_Learning.Termination
    Ground_Ordered_Resolution
    Min_Max_Least_Greatest.Min_Max_Least_Greatest_FSet
    Superposition_Calculus.Multiset_Extra
    VeriComp.Compiler
    "HOL-ex.Sketch_and_Explore"
    "HOL-Library.FuncSet"
    Lower_Set
    HOL_Extra_Extra
    The_Optional
    Full_Run
begin

lemma "I \<TTurnstile>l L \<longleftrightarrow> (is_pos L \<longleftrightarrow> atm_of L \<in> I)"
  by (cases L) simp_all

section \<open>Move to \<^theory>\<open>HOL-Library.Multiset\<close>\<close>

lemmas strict_subset_implies_multp = subset_implies_multp
hide_fact subset_implies_multp

lemma subset_implies_reflclp_multp: "A \<subseteq># B \<Longrightarrow> (multp R)\<^sup>=\<^sup>= A B"
  by (metis reflclp_iff strict_subset_implies_multp subset_mset.le_imp_less_or_eq)

lemma member_mset_repeat_msetD: "L \<in># repeat_mset n M \<Longrightarrow> L \<in># M"
  by (induction n) auto

lemma member_mset_repeat_mset_Suc[simp]: "L \<in># repeat_mset (Suc n) M \<longleftrightarrow> L \<in># M"
  by (metis member_mset_repeat_msetD repeat_mset_Suc union_iff)

lemma image_msetI: "x \<in># M \<Longrightarrow> f x \<in># image_mset f M"
  by (metis imageI in_image_mset)

lemma inj_image_mset_mem_iff: "inj f \<Longrightarrow> f x \<in># image_mset f M \<longleftrightarrow> x \<in># M"
  by (simp add: inj_image_mem_iff)


section \<open>Move to \<^theory>\<open>HOL-Library.FSet\<close>\<close>

declare wfP_pfsubset[intro]

syntax
  "_FFilter" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> 'a fset" ("(1{|_ |\<in>| _./ _|})")

translations
  "{|x |\<in>| X. P|}" == "CONST ffilter (\<lambda>x. P) X"

lemma fimage_ffUnion: "f |`| ffUnion SS = ffUnion ((|`|) f |`| SS)"
proof (intro fsubset_antisym fsubsetI)
  fix x assume "x |\<in>| f |`| ffUnion SS"
  then obtain y where "y |\<in>| ffUnion SS" and "x = f y"
    by auto
  thus "x |\<in>| ffUnion ((|`|) f |`| SS)"
    unfolding fmember_ffUnion_iff
    by (metis UN_E ffUnion.rep_eq fimage_eqI)
next
  fix x assume "x |\<in>| ffUnion ((|`|) f |`| SS)"
  then obtain S where "S |\<in>| SS" and "x |\<in>| f |`| S"
    unfolding fmember_ffUnion_iff by auto
  then show "x |\<in>| f |`| ffUnion SS"
    by (metis ffUnion_fsubset_iff fimage_mono fin_mono fsubsetI)
qed

lemma ffilter_eq_ffilter_minus_singleton:
  assumes "\<not> P y"
  shows "{|x |\<in>| X. P x|} = {|x |\<in>| X - {|y|}. P x|}"
  using assms by (induction X) auto

lemma fun_upd_fimage: "f(x := y) |`| A = (if x |\<in>| A then finsert y (f |`| (A - {|x|})) else f |`| A)"
  using fun_upd_image
  by (smt (verit) bot_fset.rep_eq finsert.rep_eq fset.set_map fset_cong minus_fset.rep_eq)

lemma ffilter_fempty[simp]: "ffilter P {||} = {||}"
  by (metis ex_fin_conv ffmember_filter)

lemma fstrict_subset_iff_fset_strict_subset_fset:
  fixes \<X> \<Y> :: "_ fset"
  shows "\<X> |\<subset>| \<Y> \<longleftrightarrow> fset \<X> \<subset> fset \<Y>"
    by blast

lemma (in linorder) ex1_sorted_list_for_fset:
  "\<exists>!xs. sorted_wrt (<) xs \<and> fset_of_list xs = X"
  using ex1_sorted_list_for_set_if_finite
  by (metis finite_fset fset_cong fset_of_list.rep_eq)

lemma (in linorder) is_least_in_fset_ffilterD:
  assumes "is_least_in_fset_wrt (<) (ffilter P X) x"
  shows "x |\<in>| X" "P x"
  using assms
  by (simp_all add: is_least_in_fset_wrt_iff)


section \<open>Move to \<^theory>\<open>VeriComp.Simulation\<close>\<close>

locale forward_simulation_with_measuring_function =
  L1: semantics step1 final1 +
  L2: semantics step2 final2
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" +
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state1 \<Rightarrow> 'index" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70)
  assumes
    wfp_order:
      "wfp (\<sqsubset>)" and
    match_final:
      "match s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2" and
    simulation:
      "match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
        (\<exists>s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> match s1' s2') \<or> (match s1' s2 \<and> measure s1' \<sqsubset> measure s1)"
begin

sublocale forward_simulation where
  step1 = step1 and step2 = step2 and final1 = final1 and final2 = final2 and order = order and
  match = "\<lambda>i x y. i = measure x \<and> match x y"
proof unfold_locales
  show "\<And>i s1 s2. i = measure s1 \<and> match s1 s2 \<Longrightarrow> final1 s1 \<Longrightarrow> final2 s2"
    using match_final by metis
next
  show "\<And>i s1 s2 s1'. i = measure s1 \<and> match s1 s2 \<Longrightarrow> step1 s1 s1' \<Longrightarrow>
    (\<exists>i' s2'. step2\<^sup>+\<^sup>+ s2 s2' \<and> i' = measure s1' \<and> match s1' s2') \<or>
    (\<exists>i'. (i' = measure s1' \<and> match s1' s2) \<and> i' \<sqsubset> i)"
    using simulation by metis
next
  show "wfp (\<sqsubset>)"
    using wfp_order .
qed

end

locale backward_simulation_with_measuring_function =
  L1: semantics step1 final1 +
  L2: semantics step2 final2
  for
    step1 :: "'state1 \<Rightarrow> 'state1 \<Rightarrow> bool" and
    step2 :: "'state2 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    final1 :: "'state1 \<Rightarrow> bool" and
    final2 :: "'state2 \<Rightarrow> bool" +
  fixes
    match :: "'state1 \<Rightarrow> 'state2 \<Rightarrow> bool" and
    measure :: "'state2 \<Rightarrow> 'index" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" (infix "\<sqsubset>" 70)
  assumes
    wfp_order:
      "wfp (\<sqsubset>)" and
    match_final:
      "match s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1" and
    simulation:
      "match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
        (\<exists>s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> match s1' s2') \<or> (match s1 s2' \<and> measure s2' \<sqsubset> measure s2)"
begin

sublocale backward_simulation where
  step1 = step1 and step2 = step2 and final1 = final1 and final2 = final2 and order = order and
  match = "\<lambda>i x y. i = measure y \<and> match x y"
proof unfold_locales
  show "\<And>i s1 s2. i = measure s2 \<and> match s1 s2 \<Longrightarrow> final2 s2 \<Longrightarrow> final1 s1"
    using match_final by metis
next
  show "\<And>i1 s1 s2 s2'. i1 = measure s2 \<and> match s1 s2 \<Longrightarrow> step2 s2 s2' \<Longrightarrow>
    (\<exists>i2 s1'. step1\<^sup>+\<^sup>+ s1 s1' \<and> i2 = measure s2' \<and> match s1' s2') \<or>
    (\<exists>i2. (i2 = measure s2' \<and> match s1 s2') \<and> i2 \<sqsubset> i1)"
    using simulation by metis
next
  show "wfp (\<sqsubset>)"
    using wfp_order .
qed

end


section \<open>Move to \<^theory>\<open>Simple_Clause_Learning.SCL_FOL\<close>\<close>

definition trail_true_lit :: "(_ literal \<times> _ option) list \<Rightarrow> _ literal \<Rightarrow> bool" where
  "trail_true_lit \<Gamma> L \<longleftrightarrow> L \<in> fst ` set \<Gamma>"

definition trail_false_lit :: "(_ literal \<times> _ option) list \<Rightarrow> _ literal \<Rightarrow> bool" where
  "trail_false_lit \<Gamma> L \<longleftrightarrow> - L \<in> fst ` set \<Gamma>"

definition trail_true_cls :: "(_ literal \<times> _ option) list \<Rightarrow> _ clause \<Rightarrow> bool" where
  "trail_true_cls \<Gamma> C \<longleftrightarrow> (\<exists>L \<in># C. trail_true_lit \<Gamma> L)"

definition trail_false_cls :: "(_ literal \<times> _ option) list \<Rightarrow> _ clause \<Rightarrow> bool" where
  "trail_false_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_false_lit \<Gamma> L)"

lemma trail_false_cls_mempty[simp]: "trail_false_cls \<Gamma> {#}"
  by (simp add: trail_false_cls_def)

definition trail_defined_lit :: "(_ literal \<times> _ option) list \<Rightarrow> _ literal \<Rightarrow> bool" where
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> (L \<in> fst ` set \<Gamma> \<or> - L \<in> fst ` set \<Gamma>)"

lemma trail_defined_lit_iff: "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L \<in> atm_of ` fst ` set \<Gamma>"
  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_defined_lit_def)

definition trail_defined_cls :: "(_ literal \<times> _ option) list \<Rightarrow> _ clause \<Rightarrow> bool" where
  "trail_defined_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_defined_lit \<Gamma> L)"

lemma trail_defined_lit_iff_true_or_false:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L"
  unfolding trail_defined_lit_def trail_false_lit_def trail_true_lit_def by (rule refl)

lemma trail_true_or_false_cls_if_defined:
  "trail_defined_cls \<Gamma> C \<Longrightarrow> trail_true_cls \<Gamma> C \<or> trail_false_cls \<Gamma> C"
  unfolding trail_defined_cls_def trail_false_cls_def trail_true_cls_def
  unfolding trail_defined_lit_iff_true_or_false
  by blast

lemma subtrail_falseI:
  assumes tr_false: "trail_false_cls ((L, Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Cl) # \<Gamma>) M"
    unfolding trail_false_cls_def by simp
  thus "trail_false_lit \<Gamma> M"
    unfolding trail_false_lit_def
    using M_neq_L
    by (cases L; cases M) (simp_all add: trail_interp_def trail_false_lit_def)
qed

inductive trail_consistent :: "('a literal \<times> 'b option) list \<Rightarrow> bool" where
  Nil[simp]: "trail_consistent []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> trail_consistent \<Gamma> \<Longrightarrow> trail_consistent ((L, u) # \<Gamma>)"

lemma distinct_lits_if_trail_consistent:
  "trail_consistent \<Gamma> \<Longrightarrow> distinct (map fst \<Gamma>)"
  by (induction \<Gamma> rule: trail_consistent.induct)
    (simp_all add: image_comp trail_defined_lit_def)

lemma trail_true_lit_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma>' K \<Longrightarrow> trail_true_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_true_lit_def)

lemma trail_true_cls_if_trail_true_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_true_cls \<Gamma>' C \<Longrightarrow> trail_true_cls \<Gamma> C"
  using trail_true_cls_def trail_true_lit_if_trail_true_suffix by metis

lemma trail_false_lit_if_trail_false_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_false_lit \<Gamma>' K \<Longrightarrow> trail_false_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_false_lit_def)

lemma trail_false_cls_if_trail_false_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_false_cls \<Gamma>' C \<Longrightarrow> trail_false_cls \<Gamma> C"
  using trail_false_cls_def trail_false_lit_if_trail_false_suffix by metis

lemma trail_defined_lit_if_trail_defined_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_defined_lit \<Gamma>' K \<Longrightarrow> trail_defined_lit \<Gamma> K"
  unfolding trail_defined_lit_def
  by (metis (no_types) Un_iff image_Un set_append suffix_def)

lemma trail_defined_cls_if_trail_defined_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_defined_cls \<Gamma>' C \<Longrightarrow> trail_defined_cls \<Gamma> C"
  unfolding trail_defined_cls_def by (metis trail_defined_lit_if_trail_defined_suffix)

lemma not_trail_true_lit_and_trail_false_lit:
  fixes \<Gamma> :: "('a literal \<times> 'b option) list" and L :: "'a literal"
  shows "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
proof (induction \<Gamma> rule: trail_consistent.induct)
  case Nil
  show ?case
    by (simp add: trail_true_cls_def trail_false_cls_def trail_true_lit_def trail_false_lit_def)
next
  case (Cons \<Gamma> K annot)
  then show ?case
    unfolding trail_defined_lit_def trail_false_lit_def trail_true_lit_def
    by (metis (no_types, opaque_lifting) fst_conv image_insert insertE list.simps(15) uminus_not_id'
        uminus_of_uminus_id)
qed

lemma not_trail_true_cls_and_trail_false_cls:
  fixes \<Gamma> :: "('a literal \<times> 'b option) list" and C :: "'a clause"
  shows "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
proof (induction \<Gamma> rule: trail_consistent.induct)
  case Nil
  show ?case
    by (simp add: trail_true_cls_def trail_false_cls_def trail_true_lit_def trail_false_lit_def)
next
  case (Cons \<Gamma> L u)
  thus ?case
    using not_trail_true_lit_and_trail_false_lit
    by (metis trail_consistent.Cons trail_false_cls_def trail_true_cls_def)
qed

lemma not_lit_and_comp_lit_false_if_trail_consistent:
 assumes "trail_consistent \<Gamma>"
  shows "\<not> (trail_false_lit \<Gamma> L \<and> trail_false_lit \<Gamma> (- L))"
  using assms
proof (induction \<Gamma>)
  case Nil
  show ?case
    by (simp add: trail_false_lit_def)
next
 case (Cons \<Gamma> K u)
  show ?case
  proof (cases "K = L \<or> K = - L")
    case True
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      unfolding de_Morgan_conj list.set image_insert prod.sel
      by (metis Cons.hyps(1) insertE trail_defined_lit_def uminus_not_id' uminus_of_uminus_id)
 next
    case False
    thus ?thesis
      unfolding trail_false_lit_def uminus_of_uminus_id
      by (metis (no_types, lifting) Cons.IH fst_conv image_iff set_ConsD trail_false_lit_def
          uminus_of_uminus_id)
  qed
qed

lemma not_both_lit_and_comp_lit_in_false_clause_if_trail_consistent:
  assumes \<Gamma>_consistent: "trail_consistent \<Gamma>" and C_false: "trail_false_cls \<Gamma> C"
  shows "\<not> (L \<in># C \<and> - L \<in># C)"
proof (rule notI)
  assume "L \<in># C \<and> - L \<in># C"

  hence "trail_false_lit \<Gamma> L \<and> trail_false_lit \<Gamma> (- L)"
    using C_false unfolding trail_false_cls_def by metis

  thus False
    using \<Gamma>_consistent not_lit_and_comp_lit_false_if_trail_consistent by metis
qed


section \<open>Move to ground ordered resolution\<close>

lemma (in ground_ordered_resolution_calculus) unique_ground_resolution:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_resolution P1 P2 C"
proof (intro Uniq_I)
  fix C C'
  assume "ground_resolution P1 P2 C" and "ground_resolution P1 P2 C'"
  thus "C = C'"
    unfolding ground_resolution.simps
    apply (elim exE conjE)
    apply simp
    by (metis asymp_on_less_lit is_maximal_in_mset_wrt_if_is_greatest_in_mset_wrt
        is_maximal_in_mset_wrt_iff literal.inject(1) totalpD totalp_on_less_lit transp_on_less_lit
        union_single_eq_diff)
qed

lemma (in ground_ordered_resolution_calculus) unique_ground_factoring:
  shows "\<exists>\<^sub>\<le>\<^sub>1C. ground_factoring P C"
proof (intro Uniq_I)
  fix P C C'
  assume "ground_factoring P C" and "ground_factoring P C'"
  thus "C = C'"
    unfolding ground_factoring.simps
    by (metis asymp_on_less_lit is_maximal_in_mset_wrt_iff totalpD totalp_less_lit
        transp_on_less_lit union_single_eq_diff)
qed

lemma (in ground_ordered_resolution_calculus) termination_ground_factoring:
  shows "wfP ground_factoring\<inverse>\<inverse>"
proof (rule wfp_if_convertible_to_wfp)
  show "\<And>x y. ground_factoring\<inverse>\<inverse> x y \<Longrightarrow> x \<prec>\<^sub>c y"
    using ground_factoring_smaller_conclusion by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by simp
qed

lemma (in ground_ordered_resolution_calculus) atms_of_concl_subset_if_ground_resolution:
  assumes "ground_resolution P\<^sub>1 P\<^sub>2 C"
  shows "atms_of C \<subseteq> atms_of P\<^sub>1 \<union> atms_of P\<^sub>2"
  using assms by (cases P\<^sub>1 P\<^sub>2 C rule: ground_resolution.cases) (auto simp add: atms_of_def)

lemma (in ground_ordered_resolution_calculus) strict_subset_mset_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "C \<subset># P"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) set_mset_eq_set_mset_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "set_mset P = set_mset C"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) atms_of_concl_eq_if_ground_factoring:
  assumes "ground_factoring P C"
  shows "atms_of C = atms_of P"
  using assms by (cases P C rule: ground_factoring.cases) simp

lemma (in ground_ordered_resolution_calculus) ground_factoring_preserves_maximal_literal:
  assumes "ground_factoring P C"
  shows "is_maximal_lit L P = is_maximal_lit L C"
  using assms by (cases P C rule: ground_factoring.cases) (simp add: is_maximal_in_mset_wrt_iff)

lemma (in ground_ordered_resolution_calculus) ground_factorings_preserves_maximal_literal:
  assumes "ground_factoring\<^sup>*\<^sup>* P C"
  shows "is_maximal_lit L P = is_maximal_lit L C"
  using assms
  by (induction P rule: converse_rtranclp_induct)
    (simp_all add: ground_factoring_preserves_maximal_literal)

lemma (in ground_ordered_resolution_calculus) ground_factoring_reduces_maximal_pos_lit:
  assumes "ground_factoring P C" and "is_pos L" and
    "is_maximal_lit L P" and "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc n"
  unfolding atomize_conj
  using \<open>ground_factoring P C\<close>
proof (cases P C rule: ground_factoring.cases)
  case (ground_factoringI t P')
  then show "is_maximal_lit L C \<and> count C L = Suc n"
    by (metis assms(1) assms(3) assms(4) asymp_on_less_lit count_add_mset
        ground_factoring_preserves_maximal_literal is_maximal_in_mset_wrt_iff nat.inject totalpD
        totalp_less_lit transp_on_less_lit)
qed

lemma (in ground_ordered_resolution_calculus) ground_factorings_reduces_maximal_pos_lit:
  assumes "(ground_factoring ^^ m) P C" and "m \<le> Suc n" and "is_pos L" and
    "is_maximal_lit L P" and "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc (Suc n - m)"
  unfolding atomize_conj
  using \<open>(ground_factoring ^^ m) P C\<close> \<open>m \<le> Suc n\<close>
proof (induction m arbitrary: C)
  case 0
  hence "P = C"
    by simp
  then show ?case
    using assms(4,5) by simp
next
  case (Suc m')
  then show ?case
    by (metis Suc_diff_le Suc_leD assms(3) diff_Suc_Suc ground_factoring_reduces_maximal_pos_lit(2)
        ground_factorings_preserves_maximal_literal relpowp_Suc_E relpowp_imp_rtranclp)
qed

lemma (in ground_ordered_resolution_calculus) full_ground_factorings_reduces_maximal_pos_lit:
  assumes steps: "(ground_factoring ^^ Suc n) P C" and L_pos: "is_pos L" and
    L_max: "is_maximal_lit L P" and L_count: "count P L = Suc (Suc n)"
  shows "is_maximal_lit L C" and "count C L = Suc 0"
  unfolding atomize_conj
  using steps L_max L_count
proof (induction n arbitrary: P)
  case 0
  then show ?case
    using L_pos ground_factorings_reduces_maximal_pos_lit[of "Suc 0" P C 0] by simp
next
  case (Suc n)
  from Suc.prems obtain P' where
    "ground_factoring P P'" and "(ground_factoring ^^ Suc n) P' C"
    by (metis relpowp_Suc_D2)

  from Suc.prems have "is_maximal_lit L P'" and "count P' L = Suc (Suc n)"
    using ground_factoring_reduces_maximal_pos_lit[OF \<open>ground_factoring P P'\<close> L_pos] by simp_all

  thus ?case
    using Suc.IH[OF \<open>(ground_factoring ^^ Suc n) P' C\<close>] by metis
qed


section \<open>Move somewhere?\<close>

lemma true_cls_imp_neq_mempty: "\<I> \<TTurnstile> C \<Longrightarrow> C \<noteq> {#}"
  by blast

lemma lift_tranclp_to_pairs_with_constant_fst:
  "(R x)\<^sup>+\<^sup>+ y z \<Longrightarrow> (\<lambda>(x, y) (x', z). x = x' \<and> R x y z)\<^sup>+\<^sup>+ (x, y) (x, z)"
  by (induction z arbitrary: rule: tranclp_induct) (auto simp: tranclp.trancl_into_trancl)

abbreviation (in preorder) is_lower_fset where
  "is_lower_fset X Y \<equiv> is_lower_set_wrt (<) (fset X) (fset Y)"

lemma lower_set_wrt_prefixI:
  assumes
    trans: "transp_on (set zs) R" and
    asym: "asymp_on (set zs) R" and
    sorted: "sorted_wrt R zs" and
    prefix: "prefix xs zs"
  shows "is_lower_set_wrt R (set xs) (set zs)"
proof -
  obtain ys where "zs = xs @ ys"
    using prefix by (auto elim: prefixE)

  show ?thesis
    using trans asym sorted
    unfolding \<open>zs = xs @ ys\<close>
    by (metis lower_set_wrt_appendI)
qed

lemmas (in preorder) lower_set_prefixI =
  lower_set_wrt_prefixI[OF transp_on_less asymp_on_less]

lemma lower_set_wrt_suffixI:
  assumes
    trans: "transp_on (set zs) R" and
    asym: "asymp_on (set zs) R" and
    sorted: "sorted_wrt R\<inverse>\<inverse> zs" and
    suffix: "suffix ys zs"
  shows "is_lower_set_wrt R (set ys) (set zs)"
proof -
  obtain xs where "zs = xs @ ys"
    using suffix by (auto elim: suffixE)

  show ?thesis
    using trans asym sorted
    unfolding \<open>zs = xs @ ys\<close>
    by (smt (verit, del_insts) Un_iff \<open>zs = xs @ ys\<close> asymp_onD asymp_on_conversep conversepI
        is_lower_set_wrt_def set_append set_mono_suffix sorted_wrt_append suffix)
qed

lemmas (in preorder) lower_set_suffixI =
  lower_set_wrt_suffixI[OF transp_on_less asymp_on_less]


lemma true_cls_repeat_mset_Suc[simp]: "I \<TTurnstile> repeat_mset (Suc n) C \<longleftrightarrow> I \<TTurnstile> C"
  by (induction n) simp_all

lemma (in backward_simulation)
  assumes "match i S1 S2" and "\<not> L1.inf_step S1"
  shows "\<not> L2.inf_step S2"
  using assms match_inf by metis

lemma (in scl_fol_calculus) grounding_of_clss_ground:
  assumes "is_ground_clss N"
  shows "grounding_of_clss N = N"
proof -
  have "grounding_of_clss N = (\<Union> C \<in> N. grounding_of_cls C)"
    unfolding grounding_of_clss_def by simp
  also have "\<dots> = (\<Union> C \<in> N. {C})"
    using \<open>is_ground_clss N\<close>
    by (simp add: is_ground_clss_def grounding_of_cls_ground)
  also have "\<dots> = N"
    by simp
  finally show ?thesis .
qed

lemma (in scl_fol_calculus) propagateI':
  "C |\<in>| N |\<union>| U \<Longrightarrow> C = add_mset L C' \<Longrightarrow> is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow>
    \<forall>K \<in># C \<cdot> \<gamma>. atm_of K \<preceq>\<^sub>B \<beta> \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow> C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    SCL_FOL.trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow> \<not> SCL_FOL.trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    \<Gamma>' = trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma> \<Longrightarrow>
    propagate N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)"
  using propagateI by metis

lemma (in scl_fol_calculus) decideI':
  "is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow> \<not> SCL_FOL.trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow> atm_of L \<cdot>a \<gamma> \<preceq>\<^sub>B \<beta> \<Longrightarrow>
    \<Gamma>' = trail_decide \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    decide N \<beta> (\<Gamma>, U, None) (\<Gamma>', U, None)"
  by (auto intro!: decideI)

lemma ground_iff_vars_term_empty: "ground t \<longleftrightarrow> vars_term t = {}"
proof (rule iffI)
  show "ground t \<Longrightarrow> vars_term t = {}"
    by (rule ground_vars_term_empty)
next
  show "vars_term t = {} \<Longrightarrow> ground t"
    by (induction t) simp_all
qed

lemma is_ground_atm_eq_ground[iff]: "is_ground_atm = ground"
proof (rule ext)
  fix t :: "('v, 'f) Term.term"
  show "is_ground_atm t = ground t"
    by (simp only: is_ground_atm_iff_vars_empty ground_iff_vars_term_empty)
qed

definition lit_of_glit :: "'f gterm literal \<Rightarrow> ('f, 'v) term literal" where
  "lit_of_glit = map_literal term_of_gterm"

definition glit_of_lit where
  "glit_of_lit = map_literal gterm_of_term"

definition cls_of_gcls where
  "cls_of_gcls = image_mset lit_of_glit"

definition gcls_of_cls where
  "gcls_of_cls = image_mset glit_of_lit"

lemma inj_lit_of_glit: "inj lit_of_glit"
proof (rule injI)
  fix L K
  show "lit_of_glit L = lit_of_glit K \<Longrightarrow> L = K"
    by (metis lit_of_glit_def literal.expand literal.map_disc_iff literal.map_sel term_of_gterm_inv)
qed

lemma atm_of_lit_of_glit_conv: "atm_of (lit_of_glit L) = term_of_gterm (atm_of L)"
  by (cases L) (simp_all add: lit_of_glit_def)

lemma ground_atm_of_lit_of_glit[simp]: "Term_Context.ground (atm_of (lit_of_glit L))"
  by (simp add: atm_of_lit_of_glit_conv)

lemma is_ground_lit_lit_of_glit[simp]: "is_ground_lit (lit_of_glit L)"
  by (simp add: is_ground_lit_def atm_of_lit_of_glit_conv)

lemma is_ground_cls_cls_of_gcls[simp]: "is_ground_cls (cls_of_gcls C)"
  by (auto simp add: is_ground_cls_def cls_of_gcls_def)

lemma glit_of_lit_lit_of_glit[simp]: "glit_of_lit (lit_of_glit L) = L"
  by (simp add: glit_of_lit_def lit_of_glit_def literal.map_comp comp_def literal.map_ident)

lemma gcls_of_cls_cls_of_gcls[simp]: "gcls_of_cls (cls_of_gcls L) = L"
  by (simp add: gcls_of_cls_def cls_of_gcls_def multiset.map_comp comp_def multiset.map_ident)

lemma lit_of_glit_glit_of_lit_ident[simp]: "is_ground_lit L \<Longrightarrow> lit_of_glit (glit_of_lit L) = L"
  by (simp add: is_ground_lit_def lit_of_glit_def glit_of_lit_def literal.map_comp literal.expand
      literal.map_sel)

lemma cls_of_gcls_gcls_of_cls_ident[simp]: "is_ground_cls D \<Longrightarrow> cls_of_gcls (gcls_of_cls D) = D"
  by (simp add: is_ground_cls_def cls_of_gcls_def gcls_of_cls_def)

lemma vars_lit_lit_of_glit[simp]: "vars_lit (lit_of_glit L) = {}"
  by simp

lemma vars_cls_cls_of_gcls[simp]: "vars_cls (cls_of_gcls C) = {}"
  by (metis is_ground_cls_cls_of_gcls is_ground_cls_iff_vars_empty)

definition atms_of_cls :: "'a clause \<Rightarrow> 'a fset" where
  "atms_of_cls C = atm_of |`| fset_mset C"

definition atms_of_clss :: "'a clause fset \<Rightarrow> 'a fset" where
  "atms_of_clss N = ffUnion (atms_of_cls |`| N)"

lemma atms_of_clss_fempty[simp]: "atms_of_clss {||} = {||}"
  unfolding atms_of_clss_def by simp

lemma atms_of_clss_finsert[simp]:
  "atms_of_clss (finsert C N) = atms_of_cls C |\<union>| atms_of_clss N"
  unfolding atms_of_clss_def by simp

definition lits_of_clss :: "'a clause fset \<Rightarrow> 'a literal fset" where
  "lits_of_clss N = ffUnion (fset_mset |`| N)"

definition lit_occures_in_clss where
  "lit_occures_in_clss L N \<longleftrightarrow> fBex N (\<lambda>C. L \<in># C)"

inductive constant_context for R where
  "R \<C> \<D> \<D>' \<Longrightarrow> constant_context R (\<C>, \<D>) (\<C>, \<D>')"

lemma rtranclp_constant_context: "(R \<C>)\<^sup>*\<^sup>* \<D> \<D>' \<Longrightarrow> (constant_context R)\<^sup>*\<^sup>* (\<C>, \<D>) (\<C>, \<D>')"
  by (induction \<D>' rule: rtranclp_induct) (auto intro: constant_context.intros rtranclp.intros)

lemma tranclp_constant_context: "(R \<C>)\<^sup>+\<^sup>+ \<D> \<D>' \<Longrightarrow> (constant_context R)\<^sup>+\<^sup>+ (\<C>, \<D>) (\<C>, \<D>')"
  by (induction \<D>' rule: tranclp_induct) (auto intro: constant_context.intros tranclp.intros)

lemma right_unique_constant_context:
  assumes R_ru: "\<And>\<C>. right_unique (R \<C>)"
  shows "right_unique (constant_context R)"
proof (rule right_uniqueI)
  fix x y z
  show "constant_context R x y \<Longrightarrow> constant_context R x z \<Longrightarrow> y = z"
    using R_ru[THEN right_uniqueD]
    by (elim constant_context.cases) (metis prod.inject)
qed

lemma safe_state_constant_context_if_invars:
  fixes N s
  assumes
    \<R>_preserves_\<I>:
      "\<And>N s s'. \<R> N s s' \<Longrightarrow> \<I> N s \<Longrightarrow> \<I> N s'" and
    ex_\<R>_if_not_final:
      "\<And>N s. \<not> \<F> (N, s) \<Longrightarrow> \<I> N s \<Longrightarrow> \<exists>s'. \<R> N s s'"
  assumes invars: "\<I> N s"
  shows "safe_state (constant_context \<R>) \<F> (N, s)"
proof -
  {
    fix S'
    assume "(constant_context \<R>)\<^sup>*\<^sup>* (N, s) S'" and "stuck_state (constant_context \<R>) S'"
    then obtain s' where "S' = (N, s')" and "(\<R> N)\<^sup>*\<^sup>* s s'" and "\<I> N s'"
      using invars
    proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
      case base
      thus ?case by simp
    next
      case (step z)
      thus ?case
        by (metis (no_types, opaque_lifting) Pair_inject \<R>_preserves_\<I> constant_context.cases
            converse_rtranclp_into_rtranclp)
    qed
    hence "\<not> \<F> (N, s') \<Longrightarrow> \<exists>s''. \<R> N s' s''"
      using ex_\<R>_if_not_final[of N s'] by argo
    hence "\<not> \<F> S' \<Longrightarrow> \<exists>S''. constant_context \<R> S' S''"
      unfolding \<open>S' = (N, s')\<close> using constant_context.intros by metis
    hence "\<F> S'"
      by (metis \<open>stuck_state (constant_context \<R>) S'\<close> stuck_state_def)
  }
  thus ?thesis
    by (metis (no_types) safe_state_def stuck_state_def)
qed

primrec trail_atms :: "(_ literal \<times> _) list \<Rightarrow> _ fset" where
  "trail_atms [] = {||}" |
  "trail_atms (Ln # \<Gamma>) = finsert (atm_of (fst Ln)) (trail_atms \<Gamma>)"

lemma fset_trail_atms: "fset (trail_atms \<Gamma>) = atm_of ` fst ` set \<Gamma>"
  by (induction \<Gamma>) simp_all

lemma trail_defined_lit_iff_trail_defined_atm:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L |\<in>| trail_atms \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  show ?case
    by (simp add: trail_defined_lit_def)
next
  case (Cons Ln \<Gamma>)

  have "trail_defined_lit (Ln # \<Gamma>) L \<longleftrightarrow> L = fst Ln \<or> - L = fst Ln \<or> trail_defined_lit \<Gamma> L"
    unfolding trail_defined_lit_def by auto

  also have "\<dots> \<longleftrightarrow> atm_of L = atm_of (fst Ln) \<or> trail_defined_lit \<Gamma> L"
    by (cases L; cases "fst Ln") simp_all

  also have "\<dots> \<longleftrightarrow> atm_of L = atm_of (fst Ln) \<or> atm_of L |\<in>| trail_atms \<Gamma>"
    unfolding Cons.IH ..

  also have "\<dots> \<longleftrightarrow> atm_of L |\<in>| trail_atms (Ln # \<Gamma>)"
    by simp

  finally show ?case .
qed

lemma trail_atms_subset_if_suffix:
  assumes "suffix \<Gamma>' \<Gamma>"
  shows "trail_atms \<Gamma>' |\<subseteq>| trail_atms \<Gamma>"
proof -
  obtain \<Gamma>\<^sub>0 where "\<Gamma> = \<Gamma>\<^sub>0 @ \<Gamma>'"
    using assms unfolding suffix_def by metis

  show ?thesis
    unfolding \<open>\<Gamma> = \<Gamma>\<^sub>0 @ \<Gamma>'\<close>
    by (induction \<Gamma>\<^sub>0) auto
qed

lemma dom_model_eq_trail_interp:
  assumes
    "\<forall>A C. \<M> A = Some C \<longleftrightarrow> map_of \<Gamma> (Pos A) = Some (Some C)" and
    "\<forall>Ln \<in> set \<Gamma>. \<forall>L. Ln = (L, None) \<longrightarrow> is_neg L"
  shows "dom \<M> = trail_interp \<Gamma>"
proof -
  have "dom \<M> = {A. \<exists>C. \<M> A = Some C}"
    unfolding dom_def by simp
  also have "\<dots> = {A. \<exists>C. map_of \<Gamma> (Pos A) = Some (Some C)}"
    using assms(1) by metis
  also have "\<dots> = {A. \<exists>opt. map_of \<Gamma> (Pos A) = Some opt}"
  proof (rule Collect_cong)
    show "\<And>A. (\<exists>C. map_of \<Gamma> (Pos A) = Some (Some C)) \<longleftrightarrow> (\<exists>opt. map_of \<Gamma> (Pos A) = Some opt)"
      using assms(2)
      by (metis literal.disc(1) map_of_SomeD option.exhaust)
  qed
  also have "\<dots> = trail_interp \<Gamma>"
  proof (induction \<Gamma>)
    case Nil
    thus ?case
      by (simp add: trail_interp_def)
  next
    case (Cons Ln \<Gamma>)

    have "{A. \<exists>opt. map_of (Ln # \<Gamma>) (Pos A) = Some opt} =
      {A. \<exists>opt. map_of [Ln] (Pos A) = Some opt} \<union> {A. \<exists>opt. map_of \<Gamma> (Pos A) = Some opt}"
      by auto

    also have "\<dots> = {A. Pos A = fst Ln} \<union> trail_interp \<Gamma>"
      unfolding Cons.IH by simp

    also have "\<dots> = trail_interp [Ln] \<union> trail_interp \<Gamma>"
      by (cases "fst Ln") (simp_all add: trail_interp_def)

    also have "\<dots> = trail_interp (Ln # \<Gamma>)"
      unfolding trail_interp_Cons[of Ln \<Gamma>] ..

    finally show ?case .
  qed
  finally show ?thesis .
qed



type_synonym 'f gliteral = "'f gterm literal"
type_synonym 'f gclause = "'f gterm clause"



locale simulation_SCLFOL_ground_ordered_resolution =
  renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50)
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    finite_less_trm: "\<And>\<beta>. finite {x. x \<prec>\<^sub>t \<beta>}" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"



section \<open>Ground ordered resolution for ground terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

sublocale ord_res: ground_ordered_resolution_calculus "(\<prec>\<^sub>t)" "\<lambda>_. {#}"
  by unfold_locales auto

sublocale linorder_trm: linorder "(\<preceq>\<^sub>t)" "(\<prec>\<^sub>t)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>t y) = (x \<preceq>\<^sub>t y \<and> \<not> y \<preceq>\<^sub>t x)"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>t x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t z \<Longrightarrow> x \<preceq>\<^sub>t z"
    by (meson transpE transp_less_trm transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<Longrightarrow> y \<preceq>\<^sub>t x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_trm reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>t y \<or> y \<preceq>\<^sub>t x"
    by (metis reflclp_iff totalpD totalp_less_trm)
qed

sublocale linorder_lit: linorder "(\<preceq>\<^sub>l)" "(\<prec>\<^sub>l)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE ord_res.transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_lit)
qed

sublocale linorder_cls: linorder "(\<preceq>\<^sub>c)" "(\<prec>\<^sub>c)"
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE ord_res.transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD ord_res.asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD ord_res.totalp_less_cls)
qed

declare linorder_trm.is_least_in_fset_ffilterD[no_atp]
declare linorder_lit.is_least_in_fset_ffilterD[no_atp]
declare linorder_cls.is_least_in_fset_ffilterD[no_atp]

end


section \<open>Common definitions and lemmas\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

abbreviation ord_res_Interp where
  "ord_res_Interp N C \<equiv> ord_res.interp N C \<union> ord_res.production N C"

definition is_least_false_clause where
  "is_least_false_clause N C \<longleftrightarrow>
    linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C"

lemma is_least_false_clause_finsert_smaller_false_clause:
  assumes
    D_least: "is_least_false_clause N D" and
    "C \<prec>\<^sub>c D" and
    C_false: "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
  shows "is_least_false_clause (finsert C N) C"
  unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
proof (intro conjI ballI impI)
  show "C |\<in>| finsert C N"
    by simp
next
  show "\<not> ord_res_Interp (fset (finsert C N)) C \<TTurnstile> C"
    using assms by metis
next
  fix y
  assume "y |\<in>| finsert C N" and "y \<noteq> C" and y_false: "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
  hence "y |\<in>| N"
    by simp

  have "\<not> (y \<prec>\<^sub>c C)"
  proof (rule notI)
    assume "y \<prec>\<^sub>c C"
    hence "ord_res_Interp (fset (finsert C N)) y = ord_res_Interp (fset N) y"
      using ord_res.Interp_insert_greater_clause by simp

    hence "\<not> ord_res_Interp (fset N) y \<TTurnstile> y"
      using y_false by argo

    moreover have "y \<prec>\<^sub>c D"
      using \<open>y \<prec>\<^sub>c C\<close> \<open>C \<prec>\<^sub>c D\<close> by order

    ultimately show False
      using D_least
      by (metis (mono_tags, lifting) \<open>y |\<in>| N\<close> linorder_cls.is_least_in_ffilter_iff
          linorder_cls.less_asym' is_least_false_clause_def)
  qed
  thus "C \<prec>\<^sub>c y"
    using \<open>y \<noteq> C\<close> by order
qed

lemma is_least_false_clause_swap_swap_compatible_fsets:
  assumes "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}"
  shows "is_least_false_clause N1 C \<longleftrightarrow> is_least_false_clause N2 C"
proof -
  have "is_least_false_clause N2 C" if
    subsets_agree: "{|x |\<in>| N1. x \<preceq>\<^sub>c C|} = {|x |\<in>| N2. x \<preceq>\<^sub>c C|}" and
    C_least: "is_least_false_clause N1 C" for N1 N2 C
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    have "C |\<in>| N1"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    thus "C |\<in>| N2"
      using subsets_agree by auto
  next
    have "\<not> ord_res_Interp (fset N1) C \<TTurnstile> C"
      using C_least
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      by argo
    moreover have "ord_res_Interp (fset N1) C = ord_res_Interp (fset N2) C"
      using subsets_agree by (auto intro!: ord_res.Interp_swap_clause_set) 
    ultimately show "\<not> ord_res_Interp (fset N2) C \<TTurnstile> C"
      by argo
  next
    fix y assume "y |\<in>| N2" and "y \<noteq> C"
    show "\<not> ord_res_Interp (fset N2) y \<TTurnstile> y \<Longrightarrow> C \<prec>\<^sub>c y"
    proof (erule contrapos_np)
      assume "\<not> C \<prec>\<^sub>c y"
      hence "y \<preceq>\<^sub>c C"
        by order
      hence "y |\<in>| N1"
        using \<open>y |\<in>| N2\<close> using subsets_agree by auto
      hence "\<not> ord_res_Interp (fset N1) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
        using \<open>is_least_false_clause N1 C\<close> \<open>y \<noteq> C\<close>
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
        by metis
      moreover have "ord_res_Interp (fset N1) y = ord_res_Interp (fset N2) y"
      proof (rule ord_res.Interp_swap_clause_set)
        show "{D. D |\<in>| N1 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y} = {D. D |\<in>| N2 \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= D y}"
          using subsets_agree \<open>y \<preceq>\<^sub>c C\<close> by fastforce
      qed
      ultimately show "ord_res_Interp (fset N2) y \<TTurnstile> y"
        using \<open>y \<preceq>\<^sub>c C\<close> by auto
    qed
  qed
  thus ?thesis
    using assms by metis
qed

lemma Uniq_is_least_false_clause: "\<exists>\<^sub>\<le>\<^sub>1 C. is_least_false_clause N C"
proof (rule Uniq_I)
  show "\<And>x y z. is_least_false_clause x y \<Longrightarrow> is_least_false_clause x z \<Longrightarrow> y = z"
    unfolding is_least_false_clause_def
    by (meson Uniq_D linorder_cls.Uniq_is_least_in_fset)
qed

lemma mempty_lesseq_cls[simp]: "{#} \<preceq>\<^sub>c C" for C
  by (cases C) (simp_all add: strict_subset_implies_multp)

lemma is_least_false_clause_mempty: "{#} |\<in>| N \<Longrightarrow> is_least_false_clause N {#}"
  using is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff mempty_lesseq_cls
  by fastforce

lemma production_union_unproductive_strong:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2 - N1. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using ord_res.wfP_less_cls C_in
proof (induction C rule: wfp_induct_rule)
  case (less C)
  hence C_in_iff: "C \<in> N1 \<union> N2 \<longleftrightarrow> C \<in> N1"
    by simp

  have interp_eq: "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C"
  proof -
    have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
      unfolding ord_res.interp_def ..
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2 - N1. D \<prec>\<^sub>c C})"
      by auto
    also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using N2_unproductive by simp
    also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
      using less.IH by simp
    also have "\<dots> = ord_res.interp N1 C"
      unfolding ord_res.interp_def ..
    finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
  qed

  show ?case
    unfolding ord_res.production_unfold C_in_iff interp_eq by argo
qed

lemma production_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}" and
    C_in: "C \<in> N1"
  shows "ord_res.production (N1 \<union> N2) C = ord_res.production N1 C"
  using production_union_unproductive_strong assms by simp

lemma interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res.interp (N1 \<union> N2) = ord_res.interp N1"
proof (rule ext)
  fix C
  have "ord_res.interp (N1 \<union> N2) C = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1 \<union> N2. D \<prec>\<^sub>c C})"
    unfolding ord_res.interp_def ..
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C} \<union>
    ord_res.production (N1 \<union> N2) ` {D \<in> N2. D \<prec>\<^sub>c C})"
    by auto
  also have "\<dots> = \<Union> (ord_res.production (N1 \<union> N2) ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using N2_unproductive by simp
  also have "\<dots> = \<Union> (ord_res.production N1 ` {D \<in> N1. D \<prec>\<^sub>c C})"
    using production_union_unproductive[OF fin N2_unproductive] by simp
  also have "\<dots> = ord_res.interp N1 C"
    unfolding ord_res.interp_def ..
  finally show "ord_res.interp (N1 \<union> N2) C = ord_res.interp N1 C" .
qed

lemma Interp_union_unproductive:
  assumes
    fin: "finite N1" "finite N2" and
    N2_unproductive: "\<forall>x \<in> N2. ord_res.production (N1 \<union> N2) x = {}"
  shows "ord_res_Interp (N1 \<union> N2) C = ord_res_Interp N1 C"
  unfolding interp_union_unproductive[OF assms]
  using production_union_unproductive[OF assms]
  using N2_unproductive[rule_format]
  by (metis (no_types, lifting) Un_iff empty_Collect_eq ord_res.production_unfold)

lemma Interp_insert_unproductive:
  assumes
    fin: "finite N1" and
    x_unproductive: "ord_res.production (insert x N1) x = {}"
  shows "ord_res_Interp (insert x N1) C = ord_res_Interp N1 C"
  using assms Interp_union_unproductive
  by (metis Un_commute finite.emptyI finite.insertI insert_is_Un singletonD)

lemma extended_partial_model_entails_iff_partial_model_entails:
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N"
  shows "ord_res_Interp (N \<union> N') C \<TTurnstile> C \<longleftrightarrow> ord_res_Interp N C \<TTurnstile> C"
  using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
  by metis

lemma nex_strictly_maximal_pos_lit_if_factorizable:
  assumes "ord_res.ground_factoring C C'"
  shows "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  by (metis Uniq_D add_mset_remove_trivial assms linorder_lit.Uniq_is_maximal_in_mset
      linorder_lit.dual_order.order_iff_strict linorder_lit.is_greatest_in_mset_iff
      linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset linorder_lit.not_less
      ord_res.ground_factoring.cases union_single_eq_member)

lemma unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "ord_res.production N C = {}"
  using assms by (simp add: ord_res.production_unfold)

lemma ball_unproductive_if_nex_strictly_maximal_pos_lit:
  assumes "\<forall>C \<in> N'. \<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
  shows "\<forall>C \<in> N'. ord_res.production (N \<union> N') C = {}"
  using assms unproductive_if_nex_strictly_maximal_pos_lit by metis

lemma is_least_false_clause_finsert_cancel:
  assumes
    C_unproductive: "ord_res.production (fset (finsert C N)) C = {}" and
    C_entailed_by_smaller: "\<exists>D |\<in>| N. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (finsert C N) = is_least_false_clause N"
proof (intro ext iffI)
  fix E
  assume E_least: "is_least_false_clause (finsert C N) E"
  hence
    E_in: "E |\<in>| finsert C N" and
    E_false: "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| finsert C N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  obtain D where
    "D |\<in>| N" and "D \<prec>\<^sub>c C" and "{D} \<TTurnstile>e {C}"
    using C_entailed_by_smaller by metis

  show "is_least_false_clause N E"
  proof (cases "C = E")
    case True

    have "E \<prec>\<^sub>c D"
    proof (rule E_least[rule_format])
      show "D |\<in>| finsert C N"
        using \<open>D |\<in>| N\<close> by simp
    next
      show "D \<noteq> E"
        using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    next
      show "\<not> ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        using E_false
      proof (rule contrapos_nn)
        assume "ord_res_Interp (fset (finsert C N)) D \<TTurnstile> D"
        thus "ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
          using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> \<open>{D} \<TTurnstile>e {C}\<close> ord_res.entailed_clause_stays_entailed by auto
      qed
    qed
    hence False
      using \<open>D \<prec>\<^sub>c C\<close> \<open>C = E\<close> by order
    thus ?thesis ..
  next
    case False
    show ?thesis
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "E |\<in>| N"
        using E_in \<open>C \<noteq> E\<close> by simp
    next
      have "ord_res_Interp (fset (finsert C N)) E = ord_res_Interp (fset N) E"
        using C_unproductive Interp_insert_unproductive by simp
      thus "\<not> ord_res_Interp (fset N) E \<TTurnstile> E"
        using E_false by argo
    next
      show "\<And>y. y |\<in>| N \<Longrightarrow> y \<noteq> E \<Longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<Longrightarrow> E \<prec>\<^sub>c y"
        using E_least C_unproductive Interp_insert_unproductive by auto
    qed
  qed
next
  fix E
  assume "is_least_false_clause N E"
  hence
    E_in: "E |\<in>| N" and
    E_false: "\<not> ord_res_Interp (fset N) E \<TTurnstile> E" and
    E_least: "(\<forall>y |\<in>| N. y \<noteq> E \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> E \<prec>\<^sub>c y)"
    unfolding atomize_conj is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by metis

  show "is_least_false_clause (finsert C N) E"
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
  proof (intro conjI ballI impI)
    show "E |\<in>| finsert C N"
      using E_in by simp
  next
    show "\<not> ord_res_Interp (fset (finsert C N)) E \<TTurnstile> E"
      using E_least E_false C_unproductive Interp_insert_unproductive by simp
  next
    fix y
    assume "y |\<in>| finsert C N" and "y \<noteq> E" and "\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y"
    show "E \<prec>\<^sub>c y"
    proof (cases "y = C")
      case True
      thus ?thesis
      using E_least \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
      by (metis (no_types, lifting) C_entailed_by_smaller C_unproductive Interp_insert_unproductive
          finite_fset fset_simps(2) linorder_cls.dual_order.strict_trans
          ord_res.entailed_clause_stays_entailed true_clss_singleton)
    next
      case False
      thus ?thesis
        using E_least \<open>y |\<in>| finsert C N\<close> \<open>y \<noteq> E\<close> \<open>\<not> ord_res_Interp (fset (finsert C N)) y \<TTurnstile> y\<close>
        using C_unproductive Interp_insert_unproductive by auto
    qed
  qed
qed

lemma is_least_false_clause_funion_cancel_right_strong:
  assumes
    "\<forall>C |\<in>| N2 - N1. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2 - N1. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms
proof (induction N2)
  case empty
  thus ?case
    by simp
next
  case (insert C N2)

  have IH: "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  proof (rule insert.IH)
    show "\<forall>C|\<in>|N2 |-| N1. \<forall>U. ord_res.production U C = {}"
      using insert.prems(1) by auto
  next
    show "\<forall>C|\<in>|N2 |-| N1. \<exists>D|\<in>|N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
      using insert.prems(2) by auto
  qed

  show ?case
  proof (cases "C |\<in>| N1")
    case True
    hence "is_least_false_clause (N1 |\<union>| finsert C N2) = is_least_false_clause (N1 |\<union>| N2)"
      by (simp add: finsert_absorb)
    also have "\<dots> = is_least_false_clause N1"
      using IH .
    finally show ?thesis .
  next
    case False
    then show ?thesis
      using is_least_false_clause_finsert_cancel IH
      by (metis finsertCI fminusI funionI1 funion_finsert_right insert.prems(1) insert.prems(2))
  qed
qed

lemma is_least_false_clause_funion_cancel_right:
  assumes
    "\<forall>C |\<in>| N2. \<forall>U. ord_res.production U C = {}" and
    "\<forall>C |\<in>| N2. \<exists>D |\<in>| N1. D \<prec>\<^sub>c C \<and> {D} \<TTurnstile>e {C}"
  shows "is_least_false_clause (N1 |\<union>| N2) = is_least_false_clause N1"
  using assms is_least_false_clause_funion_cancel_right_strong by simp

definition ex_false_clause where
  "ex_false_clause N = (\<exists>C \<in> N. \<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C)"

lemma obtains_least_false_clause_if_ex_false_clause:
  assumes "ex_false_clause (fset N)"
  obtains C where "is_least_false_clause N C"
  using assms
  by (metis (mono_tags, lifting) bot_fset.rep_eq emptyE ex_false_clause_def ffmember_filter
      linorder_cls.ex_least_in_fset is_least_false_clause_def)

lemma ex_false_clause_if_least_false_clause:
  assumes "is_least_false_clause N C"
  shows "ex_false_clause (fset N)"
  using assms
  by (metis (no_types, lifting) ex_false_clause_def is_least_false_clause_def
      linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2))

lemma ex_false_clause_iff: "ex_false_clause (fset N) \<longleftrightarrow> (\<exists>C. is_least_false_clause N C)"
  using obtains_least_false_clause_if_ex_false_clause ex_false_clause_if_least_false_clause by metis

definition ord_res_model where
  "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"

lemma ord_res_model_eq_interp_union_production_of_greatest_clause:
  assumes C_greatest: "linorder_cls.is_greatest_in_set N C"
  shows "ord_res_model N = ord_res.interp N C \<union> ord_res.production N C"
proof -
  have "ord_res_model N = (\<Union>D \<in> N. ord_res.production N D)"
    unfolding ord_res_model_def ..
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<preceq>\<^sub>c C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<union> {C}. ord_res.production N D)"
    using C_greatest linorder_cls.is_greatest_in_set_iff by auto
  also have "\<dots> = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. ord_res.production N D) \<union> ord_res.production N C"
    by auto
  also have "\<dots> = ord_res.interp N C \<union> ord_res.production N C"
    unfolding ord_res.interp_def ..
  finally show ?thesis .
qed

lemma ord_res_model_entails_clauses_if_nex_false_clause:
  assumes "finite N" and "N \<noteq> {}" and "\<not> ex_false_clause N"
  shows "ord_res_model N \<TTurnstile>s N"
  unfolding true_clss_def
proof (intro ballI)
  from \<open>\<not> ex_false_clause N\<close> have ball_true:
    "\<forall>C \<in> N. ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    by (simp add: ex_false_clause_def)

  from \<open>finite N\<close> \<open>N \<noteq> {}\<close> obtain D where
    D_greatest: "linorder_cls.is_greatest_in_set N D"
    using linorder_cls.ex_greatest_in_set by metis

  fix C assume "C \<in> N"
  hence "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ball_true by metis

  moreover have "C \<preceq>\<^sub>c D"
    using \<open>C \<in> N\<close> D_greatest[unfolded linorder_cls.is_greatest_in_set_iff] by auto

  ultimately have "ord_res.interp N D \<union> ord_res.production N D \<TTurnstile> C"
    using ord_res.entailed_clause_stays_entailed by auto

  thus "ord_res_model N \<TTurnstile> C"
    using ord_res_model_eq_interp_union_production_of_greatest_clause[OF D_greatest] by argo
qed

lemma pos_lit_not_greatest_if_maximal_in_least_false_clause:
  assumes
    C_least: "linorder_cls.is_least_in_fset {|C |\<in>| N. \<not> ord_res_Interp (fset N) C \<TTurnstile> C|} C" and
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C"
  shows "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Pos A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from C_least have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_lt: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding linorder_cls.is_least_in_ffilter_iff by auto

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  have "{D \<in> fset N. D \<preceq>\<^sub>c C} = {D \<in> fset N. D \<prec>\<^sub>c C} \<union> {D \<in> fset N. D = C}"
    by fastforce
  with C_unproductive have
    "ord_res_Interp (fset N) C = ord_res.interp (fset N) C"
    by simp
  with C_false have C_false': "\<not> ord_res.interp (fset N) C \<TTurnstile> C"
    by simp

  from C_unproductive have "A \<notin> ord_res.production (fset N) C"
    by simp
  thus ?thesis
  proof (rule contrapos_nn)
    assume "ord_res.is_strictly_maximal_lit (Pos A) C"
    then show "A \<in> ord_res.production (fset N) C"
      unfolding ord_res.production_unfold[of "fset N" C] mem_Collect_eq
      using C_in C_def C_false'
      by metis
  qed
qed

lemma ex_ground_factoringI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Pos A) C" and
    C_not_max_lit: "\<not> ord_res.is_strictly_maximal_lit (Pos A) C"
  shows "\<exists>C'. ord_res.ground_factoring C C'"
proof -
  from C_max_lit C_not_max_lit have "count C (Pos A) \<ge> 2"
    using linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset by metis
  then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
    by (metis two_le_countE)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_factoring C (add_mset (Pos A) C')"
      using ord_res.ground_factoringI[of C A C']
      using C_def C_max_lit by metis
  qed
qed

lemma true_cls_if_true_lit_in: "L \<in># C \<Longrightarrow> I \<TTurnstile>l L \<Longrightarrow> I \<TTurnstile> C"
  by auto

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit:
  assumes
    C_least_false: "is_least_false_clause N C" and
    Neg_A_max: "ord_res.is_maximal_lit (Neg A) C"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (Pos A) D \<and>
    ord_res.production (fset N) D = {A})"
proof -
  from C_least_false have
    C_in: "C |\<in>| N" and
    C_false: "\<not> ord_res_Interp (fset N) C \<TTurnstile> C" and
    C_min: "\<forall>y |\<in>| N. y \<noteq> C \<longrightarrow> \<not> ord_res_Interp (fset N) y \<TTurnstile> y \<longrightarrow> C \<prec>\<^sub>c y"
    unfolding atomize_conj is_least_false_clause_def
    unfolding linorder_cls.is_least_in_ffilter_iff
    by argo

  have "\<nexists>A. A \<in> ord_res.production (fset N) C"
  proof (rule notI, elim exE)
    fix A assume A_in: "A \<in> ord_res.production (fset N) C"
    have "Pos A \<in># C"
      using A_in by (auto elim: ord_res.mem_productionE)
    moreover have "A \<in> ord_res_Interp (fset N) C"
      using A_in C_in by blast
    ultimately show False
      using C_false by auto
  qed
  hence C_unproductive: "ord_res.production (fset N) C = {}"
    using ord_res.production_eq_empty_or_singleton[of "fset N" C] by simp

  from Neg_A_max have "Neg A \<in># C"
    by (simp add: linorder_lit.is_maximal_in_mset_iff)

  from C_false have "\<not> ord_res_Interp (fset N) C \<TTurnstile>l Neg A"
    using true_cls_if_true_lit_in[OF \<open>Neg A \<in># C\<close>]
    by meson
  hence "A \<in> ord_res_Interp (fset N) C"
    by simp
  with C_unproductive have "A \<in> ord_res.interp (fset N) C"
    by blast
  then obtain D where
    D_in: "D |\<in>| N" and D_lt_C: "D \<prec>\<^sub>c C" and D_productive: "A \<in> ord_res.production (fset N) D"
    unfolding ord_res.interp_def by auto

  from D_productive have "ord_res.is_strictly_maximal_lit (Pos A) D"
    using ord_res.mem_productionE by metis

  moreover have "ord_res.production (fset N) D = {A}"
    using D_productive ord_res.production_eq_empty_or_singleton by fastforce

  ultimately show ?thesis
    using D_in D_lt_C by metis
qed

lemma bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit':
  assumes
    C_least_false: "is_least_false_clause N C" and
    L_max: "ord_res.is_maximal_lit L C" and
    L_neg: "is_neg L"
  shows "fBex N (\<lambda>D. D \<prec>\<^sub>c C \<and> ord_res.is_strictly_maximal_lit (- L) D \<and>
    ord_res.production (fset N) D = {atm_of L})"
  using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit[OF C_least_false]
  by (simp add: L_max L_neg uminus_literal_def)

lemma ex_ground_resolutionI:
  assumes
    C_max_lit: "ord_res.is_maximal_lit (Neg A) C" and
    D_lt: "D \<prec>\<^sub>c C" and
    D_max_lit: "ord_res.is_strictly_maximal_lit (Pos A) D"
  shows "\<exists>CD. ord_res.ground_resolution C D CD"
proof -
  from C_max_lit obtain C' where C_def: "C = add_mset (Neg A) C'"
    by (meson linorder_lit.is_maximal_in_mset_iff mset_add)

  from D_max_lit obtain D' where D_def: "D = add_mset (Pos A) D'"
    by (meson linorder_lit.is_greatest_in_mset_iff mset_add)

  show ?thesis
  proof (rule exI)
    show "ord_res.ground_resolution C D (C' + D')"
      using ord_res.ground_resolutionI[of C A C' D D']
      using C_def D_def D_lt C_max_lit D_max_lit by metis
  qed
qed

lemma
  fixes N N'
  assumes
    fin: "finite N" "finite N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    C_in: "C \<in> N" and
    C_not_entailed: "\<not> ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
  shows "\<not> ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  using C_not_entailed
proof (rule contrapos_nn)
  assume "ord_res.interp (N \<union> N') C \<union> ord_res.production (N \<union> N') C \<TTurnstile> C"
  then show "ord_res.interp N C \<union> ord_res.production N C \<TTurnstile> C"
    using ord_res.interp_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    using ord_res.production_add_irrelevant_clauses_to_set[OF fin C_in irrelevant]
    by metis
qed

lemma trail_consistent_if_sorted_wrt_atoms:
  assumes "sorted_wrt (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) \<Gamma>"
  shows "trail_consistent \<Gamma>"
  using assms
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons Ln \<Gamma>)

  obtain L opt where
    "Ln = (L, opt)"
    by fastforce

  show ?case
    unfolding \<open>Ln = (L, opt)\<close>
  proof (rule trail_consistent.Cons)
    have "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<prec>\<^sub>t atm_of (fst Ln)"
      using Cons.prems by simp

    hence "\<forall>x\<in>set \<Gamma>. atm_of (fst x) \<noteq> atm_of L"
      unfolding \<open>Ln = (L, opt)\<close> by fastforce

    thus "\<not> trail_defined_lit \<Gamma> L"
      unfolding trail_defined_lit_def by fastforce
  next
    show "trail_consistent \<Gamma>"
      using Cons by simp
  qed
qed


lemma mono_atms_lt: "monotone_on (set \<Gamma>) (\<lambda>x y. atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)) (\<lambda>x y. y \<le> x)
  (\<lambda>x. atm_of K \<preceq>\<^sub>t atm_of (fst x))" for K
proof (intro monotone_onI, unfold le_bool_def, intro impI)
  fix x y
  assume "atm_of (fst y) \<prec>\<^sub>t atm_of (fst x)" and "atm_of K \<preceq>\<^sub>t atm_of (fst y)"
  thus "atm_of K \<preceq>\<^sub>t atm_of (fst x)"
    by order
qed

lemma in_trail_atms_dropWhileI:
  assumes
    "sorted_wrt R \<Gamma>" and
    "monotone_on (set \<Gamma>) R (\<ge>) (\<lambda>x. P (atm_of (fst x)))" and
    "\<not> P A" and
    "A |\<in>| trail_atms \<Gamma>"
  shows "A |\<in>| trail_atms (dropWhile (\<lambda>Ln. P (atm_of (fst Ln))) \<Gamma>)"
  using assms(1,2,4)
proof (induction \<Gamma>)
  case Nil
  thus ?case
    by simp
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "P (atm_of (fst Ln))")
    case True

    have "A |\<in>| trail_atms (dropWhile (\<lambda>Ln. P (atm_of (fst Ln))) \<Gamma>)"
    proof (rule Cons.IH)
      show "sorted_wrt R \<Gamma>"
        using Cons.prems(1) by simp
    next
      show "monotone_on (set \<Gamma>) R (\<lambda>x y. y \<le> x) (\<lambda>x. P (atm_of (fst x)))"
        using Cons.prems(2) by (meson monotone_on_subset set_subset_Cons)
    next
      have "\<not> P A"
        using assms by metis
      hence "A \<noteq> atm_of (fst Ln)"
        using True by metis
      moreover have "A |\<in>| trail_atms (Ln # \<Gamma>)"
        using Cons.prems(3) by metis
      ultimately show "A |\<in>| trail_atms \<Gamma>"
        by (simp add: trail_defined_lit_def)
    qed

    thus ?thesis
      using True by simp
  next
    case False
    thus ?thesis
      using Cons.prems(3) by simp
  qed
qed

lemma trail_defined_lit_dropWhileI:
  assumes
    "sorted_wrt R \<Gamma>" and
    "monotone_on (set \<Gamma>) R (\<ge>) (\<lambda>x. P (fst x))" and
    "\<not> P L \<and> \<not> P (- L)" and
    "trail_defined_lit \<Gamma> L"
  shows "trail_defined_lit (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) L"
  using assms in_trail_atms_dropWhileI
  by (smt (verit) imageE image_eqI mem_set_dropWhile_conv_if_list_sorted_and_pred_monotone
      trail_defined_lit_def trail_defined_lit_iff_trail_defined_atm)

lemma trail_defined_cls_dropWhileI:
  assumes
    "sorted_wrt R \<Gamma>" and
    "monotone_on (set \<Gamma>) R (\<ge>) (\<lambda>x. P (fst x))" and
    "\<forall>L \<in># C. \<not> P L \<and> \<not> P (- L)" and
    "trail_defined_cls \<Gamma> C"
  shows "trail_defined_cls (dropWhile (\<lambda>Ln. P (fst Ln)) \<Gamma>) C"
  using assms trail_defined_lit_dropWhileI
  by (metis trail_defined_cls_def)

lemma nbex_less_than_least_in_fset: "\<not> (\<exists>w |\<in>| X. w \<prec>\<^sub>c x)"
  if "linorder_cls.is_least_in_fset X x" for X x
  using that unfolding linorder_cls.is_least_in_fset_iff by auto

lemma clause_le_if_lt_least_greater:
  fixes N U\<^sub>e\<^sub>r \<F> C D
  defines
    "\<C> \<equiv> The_optional (linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N))"
  assumes
    C_lt: "\<And>E. \<C> = Some E \<Longrightarrow> C \<prec>\<^sub>c E" and
    C_in: "C |\<in>| N"
  shows "C \<preceq>\<^sub>c D"
proof (cases \<C>)
  case None

  hence "\<not> (\<exists>E. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N) E)"
    using \<C>_def
    by (metis None_eq_The_optionalD Uniq_D linorder_cls.Uniq_is_least_in_fset)

  hence "\<not> (\<exists>E |\<in>| N. D \<prec>\<^sub>c E)"
    by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)

  thus ?thesis
    using C_in linorder_cls.less_linear by blast
next
  case (Some E)

  hence "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) N) E"
    using \<C>_def by (metis Some_eq_The_optionalD)

  hence "C \<prec>\<^sub>c D \<or> C = D"
    by (metis C_in C_lt Some ffmember_filter linorder_cls.neqE nbex_less_than_least_in_fset)

  thus ?thesis
    by simp
qed

end


section \<open>Lemmas about going between ground and first-order terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

lemma ex1_gterm_of_term:
  fixes t :: "'f gterm"
  shows "\<exists>!(t' :: ('f, 'v) term). ground t' \<and> t = gterm_of_term t'"
proof (rule ex1I)
  show "ground (term_of_gterm t) \<and> t = gterm_of_term (term_of_gterm t)"
    by simp
next
  fix t' :: "('f, 'v) term"
  show "ground t' \<and> t = gterm_of_term t' \<Longrightarrow> t' = term_of_gterm t"
    by (induction t') (simp_all add: map_idI)
qed

lemma binj_betw_gterm_of_term: "bij_betw gterm_of_term {t. ground t} UNIV"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on gterm_of_term {t. ground t}"
    by (metis gterm_of_term_inj mem_Collect_eq)
next
  show "gterm_of_term ` {t. ground t} = UNIV"
  proof (rule Set.subset_antisym)
    show "gterm_of_term ` {t. Term_Context.ground t} \<subseteq> UNIV"
      by simp
  next
    show "UNIV \<subseteq> gterm_of_term ` {t. Term_Context.ground t}"
      by (metis (mono_tags, opaque_lifting) ground_term_of_gterm image_iff mem_Collect_eq subsetI
          term_of_gterm_inv)
  qed
qed

end


section \<open>SCL(FOL) for first-order terms\<close>

context simulation_SCLFOL_ground_ordered_resolution begin

definition less_B where
  "less_B x y \<longleftrightarrow> ground x \<and> ground y \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term y"

sublocale order_less_B: order "less_B\<^sup>=\<^sup>=" less_B
  by unfold_locales (auto simp add: less_B_def)

sublocale scl_fol: scl_fol_calculus renaming_vars less_B
proof unfold_locales
  fix \<beta> :: "('f, 'v) term"

  have Collect_gterms_eq: "\<And>P. {y. P y} = gterm_of_term ` {t. ground t \<and> P (gterm_of_term t)}"
    using Collect_eq_image_filter_Collect_if_bij_betw[OF binj_betw_gterm_of_term subset_UNIV]
    by auto

  have "{t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>} = gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using Collect_gterms_eq[of "\<lambda>t\<^sub>G. t\<^sub>G \<prec>\<^sub>t gterm_of_term \<beta>"] .
  hence "finite (gterm_of_term ` {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>})"
    using finite_less_trm[of "gterm_of_term \<beta>"] by metis
  moreover have "inj_on gterm_of_term {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    by (rule gterm_of_term_inj) simp
  ultimately have "finite {x. ground x \<and> gterm_of_term x \<prec>\<^sub>t gterm_of_term \<beta>}"
    using finite_imageD by blast
  thus "finite {x. less_B x \<beta>}"
    unfolding less_B_def
    using not_finite_existsD by force
qed

end


lemma trail_atms_eq_trail_atms_if_same_lits:
  assumes "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0"
  shows "trail_atms \<Gamma>\<^sub>9 = trail_atms \<Gamma>\<^sub>1\<^sub>0"
  using assms
proof (induction \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 rule: list.rel_induct)
  case Nil
  show ?case
    by (simp add: trail_atms_def)
next
  case (Cons Ln\<^sub>9 \<Gamma>\<^sub>9' Ln\<^sub>1\<^sub>0 \<Gamma>\<^sub>1\<^sub>0')
  thus ?case
    by (simp add: trail_atms_def)
qed

lemma trail_false_lit_eq_trail_false_lit_if_same_lits:
  assumes "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0"
  shows "trail_false_lit \<Gamma>\<^sub>9 = trail_false_lit \<Gamma>\<^sub>1\<^sub>0"
  using assms
proof (induction \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 rule: list.rel_induct)
  case Nil
  show ?case
    by (simp add: trail_false_lit_def)
next
  case (Cons Ln\<^sub>9 \<Gamma>\<^sub>9' Ln\<^sub>1\<^sub>0 \<Gamma>\<^sub>1\<^sub>0')
  thus ?case
    unfolding trail_false_lit_def
    unfolding list.set image_insert
    by (metis insert_iff)
qed

lemma trail_false_cls_eq_trail_false_cls_if_same_lits:
  assumes "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0"
  shows "trail_false_cls \<Gamma>\<^sub>9 = trail_false_cls \<Gamma>\<^sub>1\<^sub>0"
  unfolding trail_false_cls_def 
  unfolding trail_false_lit_eq_trail_false_lit_if_same_lits[OF assms] ..

lemma trail_defined_lit_eq_trail_defined_lit_if_same_lits:
  assumes "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0"
  shows "trail_defined_lit \<Gamma>\<^sub>9 = trail_defined_lit \<Gamma>\<^sub>1\<^sub>0"
  using assms
proof (induction \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0 rule: list.rel_induct)
  case Nil
  show ?case
    by (simp add: trail_defined_lit_def)
next
  case (Cons Ln\<^sub>9 \<Gamma>\<^sub>9' Ln\<^sub>1\<^sub>0 \<Gamma>\<^sub>1\<^sub>0')
  thus ?case
    unfolding trail_defined_lit_def
    unfolding list.set image_insert
    by (metis (no_types, opaque_lifting) insert_iff)
qed

lemma trail_defined_cls_eq_trail_defined_cls_if_same_lits:
  assumes "list_all2 (\<lambda>x y. fst x = fst y) \<Gamma>\<^sub>9 \<Gamma>\<^sub>1\<^sub>0"
  shows "trail_defined_cls \<Gamma>\<^sub>9 = trail_defined_cls \<Gamma>\<^sub>1\<^sub>0"
  unfolding trail_defined_cls_def
  unfolding trail_defined_lit_eq_trail_defined_lit_if_same_lits[OF assms] ..

end