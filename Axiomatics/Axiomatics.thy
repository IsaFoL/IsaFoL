theory Axiomatics imports Main begin unbundle cardinal_syntax

chapter \<open>Library - Alternatively import "HOL-Cardinals.Cardinal_Order_Relation" instead of Main\<close>

declare
  card_order_on_well_order_on[simp]
  card_of_card_order_on[simp]
  card_of_well_order_on[simp]
  Field_card_of[simp]
  card_of_Card_order[simp]
  card_of_Well_order[simp]
  card_of_least[simp]
  card_of_unique[simp]
  card_of_mono1[simp]
  card_of_mono2[simp]
  card_of_cong[simp]
  card_of_Field_ordIso[simp]
  card_of_underS[simp]
  ordLess_Field[simp]
  card_of_empty[simp]
  card_of_empty1[simp]
  card_of_image[simp]
  card_of_singl_ordLeq[simp]
  Card_order_singl_ordLeq[simp]
  card_of_Pow[simp]
  Card_order_Pow[simp]
  card_of_Plus1[simp]
  Card_order_Plus1[simp]
  card_of_Plus2[simp]
  Card_order_Plus2[simp]
  card_of_Plus_mono1[simp]
  card_of_Plus_mono2[simp]
  card_of_Plus_mono[simp]
  card_of_Plus_cong2[simp]
  card_of_Plus_cong[simp]
  card_of_Un_Plus_ordLeq[simp]
  card_of_Times1[simp]
  card_of_Times2[simp]
  card_of_Times3[simp]
  card_of_Times_mono1[simp]
  card_of_Times_mono2[simp]
  card_of_ordIso_finite[simp]
  card_of_Times_same_infinite[simp]
  card_of_Times_infinite_simps[simp]
  card_of_Plus_infinite1[simp]
  card_of_Plus_infinite2[simp]
  card_of_Plus_ordLess_infinite[simp]
  card_of_Plus_ordLess_infinite_Field[simp]
  infinite_cartesian_product[simp]
  cardSuc_Card_order[simp]
  cardSuc_greater[simp]
  cardSuc_ordLeq[simp]
  cardSuc_ordLeq_ordLess[simp]
  cardSuc_mono_ordLeq[simp]
  cardSuc_invar_ordIso[simp]
  card_of_cardSuc_finite[simp]
  cardSuc_finite[simp]
  card_of_Plus_ordLeq_infinite_Field[simp]
  curr_in[intro, simp]

context wo_rel begin

lemma suc_least:
  "\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r)\<rbrakk> \<Longrightarrow> (suc B, a) \<in> r"
  by (simp add: suc_least_AboveS AboveS_def)

definition "succ i \<equiv> suc {i}"

definition "isSucc i \<equiv> \<exists>j. aboveS j \<noteq> {} \<and> i = succ j"

definition "zero = minim (Field r)"

definition "isLim i \<equiv> \<not> isSucc i"

definition "pred i \<equiv> SOME j. j \<in> Field r \<and> aboveS j \<noteq> {} \<and> succ j = i"

lemma zero_smallest[simp]: assumes "j \<in> Field r" shows "(zero, j) \<in> r"
  by (simp add: assms minim_least zero_def)

lemma zero_in_Field: assumes "Field r \<noteq> {}" shows "zero \<in> Field r"
  using assms unfolding zero_def by (metis Field_ofilter minim_in ofilter_def)

lemma succ_in_diff: assumes "aboveS i \<noteq> {}" shows "(i,succ i) \<in> r \<and> succ i \<noteq> i"
  using assms suc_greater[of "{i}"] unfolding succ_def AboveS_def aboveS_def Field_def by auto

lemma succ_in_Field[simp]: assumes "aboveS i \<noteq> {}" shows "succ i \<in> Field r"
  by (meson FieldI2 assms succ_in_diff)

lemma succ_not_in: assumes "aboveS i \<noteq> {}" shows "(succ i, i) \<notin> r"
  by (metis FieldI2 assms max2_def max2_equals1 succ_in_diff)

lemma succ_smallest: assumes "(i,j) \<in> r" and "i \<noteq> j" shows "(succ i, j) \<in> r"
  by (metis Field_iff assms empty_subsetI insert_subset singletonD suc_least succ_def)

lemma pred_Field_succ:
  assumes "isSucc i" shows "pred i \<in> Field r \<and> aboveS (pred i) \<noteq> {} \<and> succ (pred i) = i"
proof -
  obtain j where j: "aboveS j \<noteq> {}" "i = succ j"
    using assms unfolding isSucc_def by auto
  then obtain "j \<in> Field r" "j \<noteq> i"
    by (metis FieldI1 succ_in_diff)
  then show ?thesis
    unfolding pred_def by (metis (mono_tags, lifting) j someI_ex)
qed

lemma succ_inj[simp]: assumes "aboveS i \<noteq> {}" and "aboveS j \<noteq> {}" shows "succ i = succ j \<longleftrightarrow> i = j"
  using Field_iff assms in_notinI succ_in_diff succ_not_in succ_smallest wo_rel_axioms by metis

lemma pred_succ[simp]: assumes "aboveS j \<noteq> {}" shows "pred (succ j) = j"
  using assms isSucc_def pred_Field_succ succ_inj by blast

lemma less_succ[simp]: assumes "aboveS i \<noteq> {}" shows "(j, succ i) \<in> r \<longleftrightarrow> (j,i) \<in> r \<or> j = succ i"
  using FieldI1 TRANS assms in_notinI max2_equals1 max2_equals2 succ_in_diff succ_smallest transD
  by (metis (no_types, lifting))

lemma underS_succ[simp]: assumes "aboveS i \<noteq> {}" shows "underS (succ i) = under i"
  unfolding underS_def under_def by (auto simp: assms succ_not_in)

definition mergeSL :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "mergeSL S L f i \<equiv> if isSucc i then S (pred i) (f (pred i)) else L f i"

definition worecSL :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "worecSL S L \<equiv> worec (mergeSL S L)"

definition "adm_woL L \<equiv> \<forall>f g i. isLim i \<and> (\<forall>j\<in>underS i. f j = g j) \<longrightarrow> L f i = L g i"

lemma mergeSL: assumes "adm_woL L" shows "adm_wo (mergeSL S L)"
  using assms pred_Field_succ succ_in_diff underS_I
  unfolding adm_wo_def adm_woL_def isLim_def mergeSL_def by metis

lemma worecSL_isSucc:
  assumes "adm_woL L" and "isSucc i" shows "worecSL S L i = S (pred i) (worecSL S L (pred i))"
  by (metis assms mergeSL mergeSL_def worecSL_def worec_fixpoint)

lemma worecSL_succ:
  assumes "adm_woL L" and "aboveS j \<noteq> {}" shows "worecSL S L (succ j) = S j (worecSL S L j)"
  by (metis assms isSucc_def pred_succ worecSL_isSucc)

lemma worecSL_isLim:
  assumes "adm_woL L" and "isLim i" shows "worecSL S L i = L (worecSL S L) i"
  using assms isLim_def mergeSL mergeSL_def worecSL_def worec_fixpoint by metis

definition worecZSL :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "worecZSL Z S L \<equiv> worecSL S (\<lambda>f a. if a = zero then Z else L f a)"

lemma worecZSL_zero: assumes "adm_woL L" shows "worecZSL Z S L zero = Z"
  using assms pred_Field_succ succ_not_in worecSL_isLim zero_smallest
  unfolding adm_woL_def isLim_def worecZSL_def by (smt (verit))

lemma worecZSL_succ:
  assumes "adm_woL L" and "aboveS j \<noteq> {}" shows "worecZSL Z S L (succ j) = S j (worecZSL Z S L j)"
  using assms worecSL_succ unfolding adm_woL_def worecZSL_def by (smt (verit))

lemma worecZSL_isLim:
  assumes "adm_woL L" and "isLim i" and "i \<noteq> zero" shows "worecZSL Z S L i = L (worecZSL Z S L) i"
proof -
  let ?L = "\<lambda>f a. if a = zero then Z else L f a"
  have "worecZSL Z S L i = ?L (worecZSL Z S L) i"
    using assms(1,2) worecSL_isLim unfolding adm_woL_def worecZSL_def by (smt (verit))
  also have "\<dots> = L (worecZSL Z S L) i"
    using assms(3) by simp
  finally show ?thesis .
qed

lemma well_order_inductZSL[case_names Zero Suc Lim]:
  assumes "P zero"
    and "\<And>i. \<lbrakk>aboveS i \<noteq> {}; P i\<rbrakk> \<Longrightarrow> P (succ i)"
    and "\<And>i. \<lbrakk>isLim i; i \<noteq> zero; \<And>j. j \<in> underS i \<Longrightarrow> P j\<rbrakk> \<Longrightarrow> P i"
  shows "P i"
  using assms succ_in_diff underS_E well_order_induct unfolding isLim_def isSucc_def by metis

definition "isSuccOrd \<equiv> \<exists>j \<in> Field r. \<forall>i \<in> Field r. (i,j) \<in> r"

definition "isLimOrd \<equiv> \<not> isSuccOrd"

end

lemma Linear_order_under_aboveS_Field:
  assumes LIN: "Linear_order r" and IN: "a \<in> Field r" shows "Field r = under r a \<union> aboveS r a"
proof (unfold under_def aboveS_def, auto)
  assume "a \<in> Field r" "(a, a) \<notin> r"
  with LIN IN order_on_defs[of _ r] refl_on_def[of _ r]
  show False by auto
next
  fix b assume "b \<in> Field r" "(b, a) \<notin> r"
  with LIN IN order_on_defs[of "Field r" r] total_on_def[of "Field r" r]
  have "(a,b) \<in> r \<or> a = b" by blast
  thus "(a,b) \<in> r"
    using LIN IN order_on_defs[of _ r] refl_on_def[of _ r] by auto
next
  fix b assume "(b, a) \<in> r"
  thus "b \<in> Field r"
    using LIN order_on_defs[of _ r] refl_on_def[of _ r] by blast
next
  fix b assume "b \<noteq> a" "(a, b) \<in> r"
  thus "b \<in> Field r"
    using LIN order_on_defs[of "Field r" r] refl_on_def[of "Field r" r] by blast
qed

definition nlists :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
  where "nlists A n \<equiv> {l. set l \<le> A \<and> length l = n}"

lemma lists_UNION_nlists: "lists A = (\<Union>n. nlists A n)"
  unfolding lists_eq_set nlists_def by blast

lemma nlists_not_empty: assumes "A \<noteq> {}" shows "nlists A n \<noteq> {}"
proof (induct n)
  case (Suc n)
  then obtain a and l where "a \<in> A \<and> l \<in> nlists A n" using assms by blast
  then have "a # l \<in> nlists A (Suc n)" by (simp add: nlists_def)
  then show ?case by blast
qed (simp add: nlists_def)

lemma card_of_lists: "|A| \<le>o |lists A|"
proof -
  let ?h = "\<lambda>a. [a]"
  have "inj_on ?h A \<and> ?h ` A \<le> lists A"
    unfolding inj_on_def lists_eq_set by auto
  thus ?thesis by (metis card_of_ordLeq)
qed

lemma card_of_nlists_Succ: "|nlists A (Suc n)| =o |A \<times> (nlists A n)|"
proof -
  let ?B = "A \<times> (nlists A n)" let ?h = "\<lambda>(a,l). a # l"
  have "inj_on ?h ?B \<and> ?h ` ?B \<le> nlists A (Suc n)"
    unfolding inj_on_def nlists_def by auto
  moreover have "nlists A (Suc n) \<le> ?h ` ?B"
  proof clarify
    fix l assume "l \<in> nlists A (Suc n)"
    hence 1: "length l = Suc n \<and> set l \<le> A" unfolding nlists_def by auto
    then obtain a and l' where 2: "l = a # l'" by (auto simp: length_Suc_conv)
    hence "a \<in> A \<and> set l' \<le> A \<and> length l' = n" using 1 by auto
    thus "l \<in> ?h ` ?B" using 2 unfolding nlists_def by auto
  qed
  ultimately have "bij_betw ?h ?B (nlists A (Suc n))"
    unfolding bij_betw_def by auto
  thus ?thesis using card_of_ordIso ordIso_symmetric by blast
qed

lemma card_of_nlists_infinite: assumes "infinite A" shows "|nlists A n| \<le>o |A|"
proof (induct n)
  case 0
  have "A \<noteq> {}" and "nlists A 0 = {[]}"
    using assms unfolding nlists_def by auto
  then show ?case
    by simp
next
  case (Suc n)
  have "|nlists A (Suc n)| =o |A \<times> (nlists A n)|"
    using card_of_nlists_Succ by blast
  moreover
  have "nlists A n \<noteq> {}" using assms nlists_not_empty[of A] by blast
  hence "|A \<times> (nlists A n)| =o |A|"
    using Suc assms by auto
  ultimately show ?case
    using ordIso_transitive ordIso_iff_ordLeq by blast
qed

lemma card_of_lists_infinite: assumes "infinite A" shows "|lists A| =o |A|"
proof -
  have "|lists A| \<le>o |A|" unfolding lists_UNION_nlists
    by (rule card_of_UNION_ordLeq_infinite[OF assms _ ballI[OF card_of_nlists_infinite[OF assms]]])
      (metis infinite_iff_card_of_nat assms)
  thus ?thesis using card_of_lists ordIso_iff_ordLeq by blast
qed

lemma card_of_Un_infinite:
  assumes "infinite A" and "|B| \<le>o |A|" shows "|A \<union> B| =o |A| \<and> |B \<union> A| =o |A|"
  by (simp add: assms card_of_Un_ordLeq_infinite_Field ordIso_iff_ordLeq)

lemma card_of_Un_diff_infinite: assumes "infinite A" and "|B| <o |A|" shows "|A - B| =o |A|"
proof -
  obtain C where C_def: "C = A - B" by blast
  have "|A \<union> B| =o |A|"
    using assms ordLeq_iff_ordLess_or_ordIso card_of_Un_infinite by blast
  moreover have "C \<union> B = A \<union> B" unfolding C_def by auto
  ultimately have 1: "|C \<union> B| =o |A|" by auto
  {assume *: "|C| \<le>o |B|"
    moreover
    {assume **: "finite B"
      hence "finite C"
        using card_of_ordLeq_finite * by blast
      hence False using ** assms card_of_ordIso_finite 1 by blast
    }
    hence "infinite B" by auto
    ultimately have False
      using card_of_Un_infinite 1 ordIso_equivalence(1,3) assms not_ordLess_ordIso by metis
  }
  hence 2: "|B| \<le>o |C|" using card_of_Well_order ordLeq_total by blast
  {assume *: "finite C"
    hence "finite B" using card_of_ordLeq_finite 2 by blast
    hence False using * assms card_of_ordIso_finite 1 by blast
  }
  hence "infinite C" by auto
  hence "|C| =o |A|"
    using card_of_Un_infinite 1 2 ordIso_equivalence(1,3) by metis
  thus ?thesis unfolding C_def .
qed

chapter \<open>Locales\<close>

section \<open>Utility\<close>

lemma Set_Diff_Un: \<open>X - (Y \<union> Z) = X - Y - Z\<close>
  by blast

lemma infinite_Diff_fin_Un: \<open>infinite (X - Y) \<Longrightarrow> finite Z \<Longrightarrow> infinite (X - (Z \<union> Y))\<close>
  by (simp add: Set_Diff_Un Un_commute)

lemma infinite_Diff_subset: \<open>infinite (X - A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> infinite (X - B)\<close>
  by (meson Diff_cancel Diff_eq_empty_iff Diff_mono infinite_super)

lemma finite_bound:
  fixes X :: \<open>('a :: size) set\<close>
  assumes \<open>finite X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>x \<in> X. \<forall>y \<in> X. size y \<le> size x\<close>
  using assms by (induct X rule: finite_induct) force+

lemma infinite_UNIV_size:
  fixes f :: \<open>('a :: size) \<Rightarrow> 'a\<close>
  assumes \<open>\<And>x. size x < size (f x)\<close>
  shows \<open>infinite (UNIV :: 'a set)\<close>
proof
  assume \<open>finite (UNIV :: 'a set)\<close>
  then obtain x :: 'a where \<open>\<forall>y :: 'a. size y \<le> size x\<close>
    using finite_bound by fastforce
  moreover have \<open>size x < size (f x)\<close>
    using assms .
  ultimately show False
    using leD by blast
qed

lemma split_finite_sets:
  assumes \<open>finite A\<close> \<open>finite B\<close>
  assumes \<open>A \<subseteq> B \<union> S\<close>
  shows \<open>\<exists>B' C. finite C \<and> (B' \<union> C = A) \<and> B' \<subseteq> B \<and> C \<subseteq> S\<close>
  using assms subset_UnE by fastforce

lemma split_list:
  assumes \<open>set A \<subseteq> set B \<union> S\<close>
  shows \<open>\<exists>B' C. set (B' @ C) = set A \<and> set B' \<subseteq> set B \<and> set C \<subseteq> S\<close>
  using assms split_finite_sets[where A=\<open>set A\<close> and B=\<open>set B\<close> and S=S]
  by (metis List.finite_set finite_Un finite_list set_append)

lemma struct_split:
  assumes \<open>\<And>A B. P A \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> P B\<close> \<open>P A\<close> \<open>set A \<subseteq> set B \<union> X\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> P (B @ C)\<close>
proof -
  obtain B' C where C: \<open>set (B' @ C) = set A\<close> \<open>set B' \<subseteq> set B\<close> \<open>set C \<subseteq> X\<close>
    using assms(3) split_list by meson
  then have \<open>P (B @ C)\<close>
    using assms(1)[where B=\<open>B @ C\<close>] assms(2) by fastforce
  then show ?thesis
    using C by blast
qed

context wo_rel begin

lemma underS_bound: \<open>a \<in> underS n \<Longrightarrow> b \<in> underS n \<Longrightarrow> a \<in> under b \<or> b \<in> under a\<close>
  by (meson BNF_Least_Fixpoint.underS_Field REFL Refl_under_in in_mono under_ofilter ofilter_linord)

lemma finite_underS_bound:
  assumes \<open>finite X\<close> \<open>X \<subseteq> underS n\<close> \<open>X \<noteq> {}\<close>
  shows \<open>\<exists>a \<in> X. \<forall>b \<in> X. b \<in> under a\<close>
  using assms
proof (induct X rule: finite_induct)
  case (insert x F)
  then show ?case
  proof (cases \<open>F = {}\<close>)
    case True
    then show ?thesis
      using insert underS_bound by fast
  next
    case False
    then show ?thesis
      using insert underS_bound insert_absorb insert_iff insert_subset under_ofilter wo_rel_axioms
      unfolding ofilter_def by metis
  qed
qed simp

lemma finite_bound_under:
  assumes \<open>finite p\<close> \<open>p \<subseteq> (\<Union>n \<in> Field r. f n)\<close>
  shows \<open>\<exists>m. p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
  using assms
proof (induct rule: finite_induct)
  case (insert x p)
  then obtain m where \<open>p \<subseteq> (\<Union>n \<in> under m. f n)\<close>
    by fast
  moreover obtain m' where \<open>x \<in> f m'\<close> \<open>m' \<in> Field r\<close>
    using insert(4) by blast
  then have \<open>x \<in> (\<Union>n \<in> under m'. f n)\<close>
    using REFL Refl_under_in by fast
  ultimately have \<open>{x} \<union> p \<subseteq> (\<Union>n \<in> under m. f n) \<union> (\<Union>n \<in> under m'. f n)\<close>
    by fast
  then show ?case
    by (metis SUP_union Un_commute insert_is_Un sup.absorb_iff2 ofilter_linord under_ofilter)
qed simp

lemma underS_trans: \<open>a \<in> underS b \<Longrightarrow> b \<in> underS c \<Longrightarrow> a \<in> underS c\<close>
  using DiffI Diff_eq_empty_iff ofilter_def empty_iff underS_subset_under underS_ofilter
    wo_rel_axioms by metis

end

lemma card_of_infinite_smaller_Union:
  assumes \<open>\<forall>x. |f x| <o |X|\<close> \<open>infinite X\<close>
  shows \<open>|\<Union>x \<in> X. f x| \<le>o |X|\<close>
  using assms by (metis (full_types) Field_card_of card_of_UNION_ordLeq_infinite
      card_of_well_order_on ordLeq_iff_ordLess_or_ordIso ordLess_or_ordLeq)

lemma card_of_params_marker_lists:
  assumes \<open>infinite (UNIV :: 'i set)\<close> \<open>|UNIV :: 'm set| \<le>o |UNIV :: nat set|\<close>
  shows \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
proof -
  have \<open>(UNIV :: 'm set) \<noteq> {}\<close>
    by simp
  then have \<open>|UNIV :: 'm set| *c |UNIV :: nat set| \<le>o |UNIV :: nat set|\<close>
    using assms(2) by (simp add: cinfinite_def cprod_cinfinite_bound ordLess_imp_ordLeq)
  then have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: nat set|\<close>
    unfolding cprod_def by simp
  moreover have \<open>|UNIV :: nat set| \<le>o |UNIV :: 'i set|\<close>
    using assms infinite_iff_card_of_nat by blast
  ultimately have \<open>|UNIV :: ('m \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordLeq_transitive by blast
  moreover have \<open>Cinfinite |UNIV :: 'i set|\<close>
    using assms by (simp add: cinfinite_def)
  ultimately have \<open>|UNIV :: 'i set| +c |UNIV :: ('m \<times> nat) set| =o |UNIV :: 'i set|\<close>
    using csum_absorb1 by blast
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| =o |UNIV :: 'i set|\<close>
    unfolding csum_def by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_iff_ordLeq by blast
  moreover have \<open>infinite (UNIV :: ('i + 'm \<times> nat) set)\<close>
    using assms by simp
  then have \<open>|UNIV :: ('i + 'm \<times> nat) list set| =o |UNIV :: ('i + 'm \<times> nat) set|\<close>
    by (metis card_of_lists_infinite lists_UNIV)
  ultimately have \<open>|UNIV :: ('i + 'm \<times> nat) list set| \<le>o |UNIV :: 'i set|\<close>
    using ordIso_ordLeq_trans by blast
  then show ?thesis
    using ordLeq_transitive by blast
qed

section \<open>Base Locale\<close>

locale MCS_Base =
  fixes consistent :: \<open>'a set \<Rightarrow> bool\<close>
  assumes consistent_hereditary: \<open>\<And>S S'. consistent S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> consistent S'\<close>
    and inconsistent_finite: \<open>\<And>S. \<not> consistent S \<Longrightarrow> \<exists>S' \<subseteq> S. finite S' \<and> \<not> consistent S'\<close>
begin

definition maximal :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> \<forall>p. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

end

section \<open>Ordinal Locale\<close>

locale MCS_Lim_Ord = MCS_Base +
  fixes r :: \<open>'a rel\<close>
  assumes WELL: \<open>Well_order r\<close>
    and Cinfinite_r: \<open>Cinfinite r\<close>
  fixes params :: \<open>'a \<Rightarrow> 'i set\<close>
    and witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
  assumes finite_params: \<open>\<And>p. finite (params p)\<close>
    and finite_witness_params: \<open>\<And>p S. finite (\<Union>q \<in> witness p S. params q)\<close>
    and consistent_witness: \<open>\<And>p S. consistent ({p} \<union> S)
      \<Longrightarrow> infinite (UNIV - (\<Union>q \<in> S. params q))
      \<Longrightarrow> consistent (witness p S \<union> {p} \<union> S)\<close>
begin

lemma wo_rel_r: \<open>wo_rel r\<close>
  by (simp add: WELL wo_rel.intro)

lemma isLimOrd_r: \<open>wo_rel.isLimOrd r\<close>
  using Cinfinite_r cinfinite_def Card_order_trans Cinfinite_r cinfinite_def
    infinite_Card_order_limit wo_rel.isLimOrd_def wo_rel.isSuccOrd_def wo_rel_r by metis

subsection \<open>Lindenbaum Extension\<close>

abbreviation paramss :: \<open>'a set \<Rightarrow> 'i set\<close> where
  \<open>paramss S \<equiv> \<Union>p \<in> S. params p\<close>

definition extendS :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>extendS n prev \<equiv> if consistent ({n} \<union> prev) then witness n prev \<union> {n} \<union> prev else prev\<close>

definition extendL :: \<open>('a \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extendL rec n \<equiv> \<Union>m \<in> underS r n. rec m\<close>

definition extend :: \<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> where
  \<open>extend S n \<equiv> wo_rel.worecZSL r S extendS extendL n\<close>

lemma adm_woL_extendL: \<open>wo_rel.adm_woL r extendL\<close>
  unfolding extendL_def wo_rel.adm_woL_def[OF wo_rel_r] by blast

definition Extend :: \<open>'a set \<Rightarrow> 'a set\<close> where
  \<open>Extend S \<equiv> \<Union>n \<in> Field r. extend S n\<close>

lemma extend_subset: \<open>n \<in> Field r \<Longrightarrow> S \<subseteq> extend S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by simp
next
  case (2 i)
  moreover from this have \<open>i \<in> Field r\<close>
    by (meson FieldI1 wo_rel.succ_in_diff wo_rel_r)
  ultimately show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    using wo_rel.zero_in_Field[OF wo_rel_r] wo_rel.zero_smallest[OF wo_rel_r]
    by (metis SUP_upper2 emptyE underS_I)
qed

lemma Extend_subset': \<open>Field r \<noteq> {} \<Longrightarrow> S \<subseteq> Extend S\<close>
  unfolding Extend_def using extend_subset by fast

lemma extend_underS: \<open>m \<in> underS r n \<Longrightarrow> extend S m \<subseteq> extend S n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def using BNF_Least_Fixpoint.underS_Field underS_I underS_notIn wo_rel_r
      wo_rel.underS_trans wo_rel.zero_smallest by metis
next
  case (2 i)
  moreover from this have \<open>m = i \<or> m \<in> underS r i\<close>
    by (metis wo_rel.less_succ[OF wo_rel_r] underS_E underS_I)
  ultimately show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)] by auto
next
  case (3 i)
  then show ?case
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
qed

lemma extend_under: \<open>m \<in> under r n \<Longrightarrow> extend S m \<subseteq> extend S n\<close>
  using extend_underS wo_rel_r order_eq_iff extend_underS mem_Collect_eq underS_I under_def by metis

subsection \<open>Consistency\<close>

lemma params_origin:
  assumes \<open>a \<in> paramss (extend S n)\<close>
  shows \<open>a \<in> paramss S \<or> (\<exists>m \<in> underS r n. a \<in> paramss (witness m (extend S m) \<union> {m}))\<close>
  using assms
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by blast
next
  case (2 i)
  then consider (here) \<open>a \<in> paramss (witness i (extend S i) \<union> {i})\<close> |
    (there) \<open>a \<in> paramss (extend S i)\<close>
    using wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)] extendS_def extend_def
    by (metis (no_types, lifting) UN_Un UnE)
  then show ?case
  proof cases
    case here
    moreover have \<open>i \<in> Field r\<close>
      by (meson WELL 2(1) well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
    ultimately show ?thesis
      using 2(1) by (metis Refl_under_in wo_rel.underS_succ[OF wo_rel_r] wo_rel.REFL[OF wo_rel_r])
  next
    case there
    then show ?thesis
      using 2 by (metis in_mono underS_subset_under wo_rel.underS_succ[OF wo_rel_r])
  next
  qed
next
  case (3 i)
  then obtain j where \<open>j \<in> underS r i\<close> \<open>a \<in> paramss (extend S j)\<close>
    unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
    by blast
  then show ?case
    using 3 wo_rel.underS_trans[OF wo_rel_r, of _ j i] by meson
qed

lemma consistent_extend:
  assumes \<open>consistent S\<close> \<open>r \<le>o |UNIV - paramss S|\<close>
  shows \<open>consistent (extend S n)\<close>
  using assms(1)
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case
    unfolding extend_def wo_rel.worecZSL_zero[OF wo_rel_r adm_woL_extendL]
    by blast
next
  case (2 i)
  then have \<open>i \<in> Field r\<close>
    by (meson WELL well_order_on_domain wo_rel.succ_in_diff[OF wo_rel_r])
  then have *: \<open>|underS r i| <o r\<close>
    using card_of_underS by (simp add: Cinfinite_r)
  let ?paramss = \<open>\<lambda>k. paramss (witness k (extend S k) \<union> {k})\<close>
  let ?X = \<open>\<Union>k \<in> underS r i. ?paramss k\<close>
  have \<open>|?X| <o r\<close>
  proof (cases \<open>finite (underS r i)\<close>)
    case True
    then have \<open>finite ?X\<close>
      by (simp add: finite_params finite_witness_params)
    then show ?thesis
      using Cinfinite_r assms(2) unfolding cinfinite_def by (simp add: finite_ordLess_infinite)
  next
    case False
    moreover have \<open>\<forall>k. finite (?paramss k)\<close>
      by (simp add: finite_params finite_witness_params)
    then have \<open>\<forall>k. |?paramss k| <o |underS r i|\<close>
      by (metis calculation card_of_ordLess2 finite.simps finite_imageI)
    ultimately have \<open>|?X| \<le>o |underS r i|\<close>
      using card_of_infinite_smaller_Union by fast
    then show ?thesis
      using * ordLeq_ordLess_trans by blast
  qed
  then have \<open>|?X| <o |UNIV - paramss S|\<close>
    using assms(2) ordLess_ordLeq_trans by blast
  moreover have \<open>infinite (UNIV - paramss S)\<close>
    using assms(2) Cinfinite_r unfolding cinfinite_def
    by (metis Field_card_of cinfinite_def cinfinite_mono)
  ultimately have \<open>|UNIV - paramss S - ?X| =o |UNIV - paramss S|\<close>
    using card_of_Un_diff_infinite by blast
  moreover from this have \<open>infinite (UNIV - paramss S - ?X)\<close>
    using \<open>infinite (UNIV - paramss S)\<close> card_of_ordIso_finite by blast
  moreover have \<open>\<And>a. a \<in> paramss (extend S i) \<Longrightarrow> a \<in> paramss S \<or> a \<in> ?X\<close>
    using params_origin by simp
  then have \<open>paramss (extend S i) \<subseteq> paramss S \<union> ?X\<close>
    by fast
  ultimately have \<open>infinite (UNIV - paramss (extend S i))\<close>
    using infinite_Diff_subset by (metis (no_types, lifting) Set_Diff_Un)
  with 2 show ?case
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL 2(1)]
    using consistent_witness by simp
next
  case (3 i)
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> consistent (extend S i)\<close>
    then obtain S' where S': \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n \<in> underS r i. extend S n)\<close> \<open>\<not> consistent S'\<close>
      unfolding extend_def extendL_def wo_rel.worecZSL_isLim[OF wo_rel_r adm_woL_extendL 3(1-2)]
      using inconsistent_finite by auto
    then obtain ns where ns: \<open>S' \<subseteq> (\<Union>n \<in> ns. extend S n)\<close> \<open>ns \<subseteq> underS r i\<close> \<open>finite ns\<close>
      by (metis finite_subset_Union finite_subset_image)
    moreover have \<open>ns \<noteq> {}\<close>
      using S'(3) assms calculation(1) consistent_hereditary by auto
    ultimately obtain j where \<open>\<forall>n \<in> ns. n \<in> under r j\<close> \<open>j \<in> underS r i\<close>
      using wo_rel.finite_underS_bound wo_rel_r ns subset_iff by meson
    then have \<open>\<forall>n \<in> ns. extend S n \<subseteq> extend S j\<close>
      using extend_under by fast
    then have \<open>S' \<subseteq> extend S j\<close>
      using S' ns(1) by blast
    then show False
      using 3(3-) \<open>\<not> consistent S'\<close> consistent_hereditary \<open>j \<in> underS r i\<close>
      by (meson BNF_Least_Fixpoint.underS_Field)
  qed
qed

lemma consistent_Extend:
  assumes \<open>consistent S\<close> \<open>r \<le>o |UNIV - paramss S|\<close>
  shows \<open>consistent (Extend S)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union>n \<in> Field r. extend S n)\<close>
  then obtain S' where \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n \<in> Field r. extend S n)\<close> \<open>\<not> consistent S'\<close>
    using inconsistent_finite by metis
  then obtain m where \<open>S' \<subseteq> (\<Union>n \<in> under r m. extend S n)\<close> \<open>m \<in> Field r\<close>
    using wo_rel.finite_bound_under[OF wo_rel_r] assms consistent_hereditary SUP_le_iff
      consistent_extend extend_under by metis
  then have \<open>S' \<subseteq> extend S m\<close>
    using extend_under by fast
  moreover have \<open>consistent (extend S m)\<close>
    using assms consistent_extend \<open>m \<in> Field r\<close> by blast
  ultimately show False
    using \<open>\<not> consistent S'\<close> consistent_hereditary by blast
qed

lemma Extend_bound: \<open>n \<in> Field r \<Longrightarrow> extend S n \<subseteq> Extend S\<close>
  unfolding Extend_def by blast

subsection \<open>Maximality\<close>

definition maximal' :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>maximal' S \<equiv> \<forall>p \<in> Field r. consistent ({p} \<union> S) \<longrightarrow> p \<in> S\<close>

lemma maximal'_Extend: \<open>maximal' (Extend S)\<close>
  unfolding maximal'_def
proof safe
  fix p
  assume *: \<open>p \<in> Field r\<close> \<open>consistent ({p} \<union> Extend S)\<close>
  then have \<open>{p} \<union> extend S p \<subseteq> {p} \<union> Extend S\<close>
    unfolding Extend_def by blast
  then have **: \<open>consistent ({p} \<union> extend S p)\<close>
    using * consistent_hereditary by blast
  moreover have succ: \<open>aboveS r p \<noteq> {}\<close>
    using *(1)
      Card_order_infinite_not_under Cinfinite_r Linear_order_under_aboveS_Field
      Un_empty_right card_order_on_def cinfinite_def well_order_on_def by metis
  then have \<open>wo_rel.succ r p \<in> Field r\<close>
    using wo_rel.succ_in_Field[OF wo_rel_r] by blast
  moreover have \<open>p \<in> extend S (wo_rel.succ r p)\<close>
    using ** unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL succ]
    by simp
  ultimately show \<open>p \<in> Extend S\<close>
    using Extend_bound by fast
qed

subsection \<open>Saturation\<close>

definition saturated' :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>saturated' S \<equiv> \<forall>p \<in> S. p \<in> Field r \<longrightarrow> (\<exists>S'. witness p S' \<subseteq> S)\<close>

lemma saturated'_Extend:
  assumes \<open>consistent (Extend S)\<close>
  shows \<open>saturated' (Extend S)\<close>
  unfolding saturated'_def
proof safe
  fix p
  assume *: \<open>p \<in> Extend S\<close> \<open>p \<in> Field r\<close>
  then have \<open>extend S p \<subseteq> Extend S\<close>
    unfolding Extend_def by blast
  then have \<open>consistent ({p} \<union> extend S p)\<close>
    using assms(1) * consistent_hereditary by auto
  moreover have succ: \<open>aboveS r p \<noteq> {}\<close>
    using *(2)
      Card_order_infinite_not_under Cinfinite_r Linear_order_under_aboveS_Field
      Un_empty_right card_order_on_def cinfinite_def well_order_on_def by metis
  then have \<open>wo_rel.succ r p \<in> Field r\<close>
    using wo_rel_r by (simp add: wo_rel.succ_in_Field)
  ultimately have \<open>extend S (wo_rel.succ r p) = witness p (extend S p) \<union> {p} \<union> extend S p\<close>
    unfolding extend_def extendS_def wo_rel.worecZSL_succ[OF wo_rel_r adm_woL_extendL succ]
    by simp
  moreover have \<open>extend S (wo_rel.succ r p) \<subseteq> Extend S\<close>
    unfolding Extend_def using \<open>wo_rel.succ r p \<in> Field r\<close> by blast
  ultimately show \<open>\<exists>a. witness p a \<subseteq> Extend S\<close>
    by fast
qed

end

section \<open>Locale with Saturation\<close>

locale MCS_Saturation = MCS_Base +
  assumes infinite_UNIV: \<open>infinite (UNIV :: 'a set)\<close>
  fixes params :: \<open>'a \<Rightarrow> 'i set\<close>
    and witness :: \<open>'a \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
  assumes \<open>\<And>p. finite (params p)\<close>
    and \<open>\<And>p S. finite (\<Union>q \<in> witness p S. params q)\<close>
    and \<open>\<And>p S. consistent ({p} \<union> S) \<Longrightarrow> infinite (UNIV - (\<Union>q \<in> S. params q))
      \<Longrightarrow> consistent (witness p S \<union> {p} \<union> S)\<close>

sublocale MCS_Saturation \<subseteq> MCS_Lim_Ord _ \<open>|UNIV|\<close>
proof
  show \<open>Well_order |UNIV|\<close>
    by simp
next
  show \<open>Cinfinite |UNIV :: 'a set|\<close>
    unfolding cinfinite_def using infinite_UNIV by simp
next
  fix p
  show \<open>finite (params p)\<close>
    by (metis MCS_Saturation_axioms MCS_Saturation_axioms_def MCS_Saturation_def)
next
  fix p S
  show \<open>finite (\<Union>q \<in> witness p S. params q)\<close>
    using MCS_Saturation_axioms unfolding MCS_Saturation_axioms_def MCS_Saturation_def by metis
next
  fix p S
  show \<open>consistent ({p} \<union> S) \<Longrightarrow>
           infinite (UNIV - (\<Union>q \<in> S. params q)) \<Longrightarrow>
           consistent (witness p S \<union> {p} \<union> S)\<close>
    by (metis MCS_Saturation_axioms MCS_Saturation_axioms_def MCS_Saturation_def)
qed

context MCS_Saturation begin

theorem Extend_subset: \<open>S \<subseteq> Extend S\<close>
  by (simp add: Extend_subset')

lemma maximal_maximal': \<open>maximal S \<longleftrightarrow> maximal' S\<close>
  unfolding maximal_def maximal'_def by simp

lemma maximal_Extend: \<open>maximal (Extend S)\<close>
  using maximal'_Extend maximal_maximal' by fast

definition saturated :: \<open>'a set \<Rightarrow> bool\<close> where
  \<open>saturated S \<equiv> \<forall>p \<in> S. \<exists>S'. witness p S' \<subseteq> S\<close>

lemma saturated_saturated': \<open>saturated S \<longleftrightarrow> saturated' S\<close>
  unfolding saturated_def saturated'_def by simp

lemma saturated_Extend:
  assumes \<open>consistent (Extend S)\<close>
  shows \<open>saturated (Extend S)\<close>
  using assms saturated'_Extend saturated_saturated' by blast

theorem MCS_Extend:
  assumes \<open>consistent S\<close> \<open>|UNIV :: 'a set| \<le>o |UNIV - paramss S|\<close>
  shows \<open>consistent (Extend S)\<close> \<open>maximal (Extend S)\<close> \<open>saturated (Extend S)\<close>
  using assms consistent_Extend maximal_Extend saturated_Extend by blast+

end

section \<open>Locale without Saturation\<close>

locale MCS_No_Saturation = MCS_Base +
  assumes \<open>infinite (UNIV :: 'a set)\<close>

sublocale MCS_No_Saturation \<subseteq> MCS_Saturation consistent \<open>\<lambda>_. {} :: 'a set\<close> \<open>\<lambda>_ _. {}\<close>
proof
  show \<open>infinite (UNIV :: 'a set)\<close>
    using MCS_No_Saturation_axioms MCS_No_Saturation_axioms_def MCS_No_Saturation_def by blast
next
  show \<open>finite {}\<close> ..
next
  show \<open>finite (\<Union>_\<in>{}. {})\<close>
    by fast
next
  fix p S
  show \<open>consistent ({p} \<union> S) \<Longrightarrow> consistent ({} \<union> {p} \<union> S)\<close>
    by simp
qed

context MCS_No_Saturation begin

lemma always_saturated [simp]: \<open>saturated H\<close>
  unfolding saturated_def by simp

theorem MCS_Extend':
  assumes \<open>consistent S\<close>
  shows \<open>consistent (Extend S)\<close> \<open>maximal (Extend S)\<close>
  using assms consistent_Extend maximal_Extend by simp_all

end

section \<open>Truth Lemma\<close>

locale Truth_Base =
  fixes semics :: \<open>'model \<Rightarrow> ('model \<Rightarrow> 'fm \<Rightarrow> bool) \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and semantics :: \<open>'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
    and models_from :: \<open>'a set \<Rightarrow> 'model set\<close>
    and rel :: \<open>'a set \<Rightarrow> 'model \<Rightarrow> 'fm \<Rightarrow> bool\<close>
  assumes semics_semantics: \<open>semantics M p \<longleftrightarrow> semics M semantics p\<close>
    and Hintikka_model: \<open>\<And>H M p. \<forall>M \<in> models_from H. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p \<Longrightarrow>
      M \<in> models_from H \<Longrightarrow> semantics M p \<longleftrightarrow> rel H M p\<close>

locale Truth_No_Saturation = MCS_No_Saturation + Truth_Base +
  assumes MCS_Hintikka: \<open>\<And>H. consistent H \<Longrightarrow> maximal H \<Longrightarrow>
      \<forall>M \<in> models_from H. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close>
begin

theorem truth_lemma_no_saturation:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>M \<in> models_from H\<close>
  shows \<open>semantics M p \<longleftrightarrow> rel H M p\<close>
  using Hintikka_model MCS_Hintikka assms .

end

locale Truth_Saturation = MCS_Saturation + Truth_Base +
  assumes MCS_Hintikka: \<open>\<And>H. consistent H \<Longrightarrow> maximal H \<Longrightarrow> saturated H \<Longrightarrow>
      \<forall>M \<in> models_from H. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close>
begin

theorem truth_lemma_saturation:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close> \<open>M \<in> models_from H\<close>
  shows \<open>semantics M p \<longleftrightarrow> rel H M p\<close>
  using Hintikka_model MCS_Hintikka assms .

end

section \<open>Rearranging Assumptions\<close>

locale Derivations =
  fixes derive :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes derive_struct: \<open>\<And>A B p. derive A p \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> derive B p\<close>
begin

theorem derive_split:
  assumes \<open>set A \<subseteq> set B \<union> X\<close> \<open>derive A p\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> derive (B @ C) p\<close>
  using struct_split[where P=\<open>\<lambda>A. derive A p\<close>] derive_struct assms by blast

corollary derive_split1:
  assumes \<open>set A \<subseteq> {q} \<union> X\<close> \<open>derive A p\<close>
  shows \<open>\<exists>C. set C \<subseteq> X \<and> derive (q # C) p\<close>
  using assms derive_split[where B=\<open>[q]\<close>] by simp

end

section \<open>MCSs and Deriving Falsity\<close>

locale Derivations_MCS = Derivations + MCS_Base +
  fixes fls
  assumes consistent_derive_fls: \<open>\<And>S. consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> derive S' fls)\<close>
begin

theorem MCS_derive_fls:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<notin> S \<longleftrightarrow> (\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls)\<close>
proof
  assume \<open>p \<notin> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls\<close>
    using assms derive_split1 consistent_derive_fls unfolding maximal_def by metis
next
  assume \<open>\<exists>S'. set S' \<subseteq> S \<and> derive (p # S') fls\<close>
  then show \<open>p \<notin> S\<close>
    using assms consistent_derive_fls by fastforce
qed

end

section \<open>MCSs and Derivability\<close>

locale Derivations_MCS_Cut = Derivations_MCS +
  assumes derive_assm: \<open>\<And>A p. p \<in> set A \<Longrightarrow> derive A p\<close>
    and derive_cut: \<open>\<And>A B p q. derive A p \<Longrightarrow> derive (p # B) q \<Longrightarrow> derive (A @ B) q\<close>
begin

theorem MCS_derive:
  assumes \<open>consistent S\<close> \<open>maximal S\<close>
  shows \<open>p \<in> S \<longleftrightarrow> (\<exists>S'. set S' \<subseteq> S \<and> derive S' p)\<close>
proof
  assume \<open>p \<in> S\<close>
  then show \<open>\<exists>S'. set S' \<subseteq> S \<and> derive S' p\<close>
    using derive_assm by (metis List.set_insert empty_set empty_subsetI insert_subset singletonI)
next
  assume \<open>\<exists>A. set A \<subseteq> S \<and> derive A p\<close>
  then obtain A where A: \<open>set A \<subseteq> S\<close> \<open>derive A p\<close>
    by blast
  have \<open>consistent ({p} \<union> S)\<close>
    unfolding consistent_derive_fls
  proof safe
    fix B
    assume B: \<open>set B \<subseteq> {p} \<union> S\<close> \<open>derive B fls\<close>
    then obtain C where C: \<open>derive (p # C) fls\<close> \<open>set C \<subseteq> S\<close>
      using derive_split1 by blast
    then have \<open>derive (A @ C) fls\<close>
      using A derive_cut by blast
    then show False
      using A(1) B(1) C assms(1) consistent_derive_fls by simp
  qed
  then show \<open>p \<in> S\<close>
    using assms unfolding maximal_def by auto
qed

end

chapter \<open>First-Order Logic\<close>

section \<open>Syntax\<close>

datatype (params_tm: 'f) tm =
  Var nat (\<open>\<cdot>\<close>) |
  Fun 'f \<open>'f tm list\<close> (\<open>\<ddagger>\<close>)

abbreviation Con :: \<open>'f \<Rightarrow> 'f tm\<close> (\<open>\<star>\<close>) where \<open>\<star>a \<equiv> \<ddagger>a []\<close>

datatype (params_fm: 'f, 'p) fm =
  Pre 'p \<open>'f tm list\<close> (\<open>\<dagger>\<close>) |
  Neg \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<not> _\<close> [100] 100) |
  Imp \<open>('f, 'p) fm\<close> \<open>('f, 'p) fm\<close> (\<open>_ \<^bold>\<longrightarrow> _\<close> [56, 55] 55) |
  Uni \<open>('f, 'p) fm\<close> (\<open>\<^bold>\<forall>\<close>)

abbreviation Pro :: \<open>'p \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<section>\<close>) where \<open>\<section>n \<equiv> \<dagger>n []\<close>

section \<open>Freshness\<close>

primrec new_term :: \<open>'f \<Rightarrow> 'f tm \<Rightarrow> bool\<close> and new_list :: \<open>'f \<Rightarrow> 'f tm list \<Rightarrow> bool\<close> where
  \<open>new_term c (Var n) = True\<close> |
  \<open>new_term c (Fun i l) = (if i = c then False else new_list c l)\<close> |
  \<open>new_list c [] = True\<close> |
  \<open>new_list c (t # l) = (if new_term c t then new_list c l else False)\<close>

primrec new :: \<open>'f \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>new c (Pre i l) = new_list c l\<close> |
  \<open>new c (Neg p) = new c p\<close> |
  \<open>new c (Imp p q) = (if new c p then new c q else False)\<close> |
  \<open>new c (Uni p) = new c p\<close>

section \<open>Substitution\<close>

primrec add_env :: \<open>'a \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a\<close> (\<open>_ \<then> _\<close> 0) where
  \<open>(t \<then> s) 0 = t\<close> |
  \<open>(t \<then> s) (Suc n) = s n\<close>

primrec lift_tm :: \<open>'f tm \<Rightarrow> 'f tm\<close> where
  \<open>lift_tm (\<cdot>n) = \<cdot>(n+1)\<close> |
  \<open>lift_tm (\<ddagger>f ts) = \<ddagger>f (map lift_tm ts)\<close>

primrec sub_tm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_tm s (\<cdot>n) = s n\<close> |
  \<open>sub_tm s (\<ddagger>f ts) = \<ddagger>f (map (sub_tm s) ts)\<close>

primrec sub_fm :: \<open>(nat \<Rightarrow> 'f tm) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fm s (\<dagger>P ts) = \<dagger>P (map (sub_tm s) ts)\<close> |
  \<open>sub_fm s (\<^bold>\<not> p) = \<^bold>\<not> sub_fm s p\<close> |
  \<open>sub_fm s (p \<^bold>\<longrightarrow> q) = sub_fm s p \<^bold>\<longrightarrow> sub_fm s q\<close> |
  \<open>sub_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fm (\<cdot>0 \<then> \<lambda>n. lift_tm (s n)) p)\<close>

abbreviation inst_single :: \<open>'f tm \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> (\<open>\<langle>_\<rangle>\<close>) where
  \<open>\<langle>t\<rangle> \<equiv> sub_fm (t \<then> \<cdot>)\<close>

section \<open>Axiomatics\<close>

inductive Calculus (\<open>\<turnstile> _\<close> [50] 50) where
  01: \<open>\<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p\<close> |
  02: \<open>\<turnstile> (\<^bold>\<not> p \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close> |
  03: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<not> q \<^bold>\<longrightarrow> p\<close> |
  MP: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<Longrightarrow> \<turnstile> q \<Longrightarrow> \<turnstile> p\<close> |
  SR: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<langle>t\<rangle>p\<close> |
  GR: \<open>\<turnstile> q \<^bold>\<longrightarrow> \<langle>\<star>a\<rangle>p \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close> if \<open>new a p\<close> and \<open>new a q\<close>

lemma 04: \<open>\<turnstile> (((q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> s\<close>
  using MP 01 01 .

lemma 05: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (s \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> s \<^bold>\<longrightarrow> r\<close>
  using MP 04 04 .

lemma 06: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ((p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s\<close>
  using MP 04 01 .

lemma 07: \<open>\<turnstile> (t \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> t \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s\<close>
  using MP 05 06 .

lemma 09: \<open>\<turnstile> ((\<^bold>\<not> p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 01 03 .

lemma 10: \<open>\<turnstile> p \<^bold>\<longrightarrow> ((\<^bold>\<not> p \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 09 06 .

lemma 11: \<open>\<turnstile> (q \<^bold>\<longrightarrow> (\<^bold>\<not> p \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> (\<^bold>\<not> p \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP MP 10 02 02 .

lemma 12: \<open>\<turnstile> t \<^bold>\<longrightarrow> (\<^bold>\<not> p \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 09 11 .

lemma 13: \<open>\<turnstile> (\<^bold>\<not> p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> t \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 07 12 .

lemma 14: \<open>\<turnstile> ((t \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (\<^bold>\<not> p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r\<close>
  using MP 01 13 .

lemma 15: \<open>\<turnstile> (\<^bold>\<not> p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 14 02 .

lemma 16: \<open>\<turnstile> p \<^bold>\<longrightarrow> p\<close>
  using MP 09 02 .

lemma 17: \<open>\<turnstile> p \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 09 15 .

lemma 18: \<open>\<turnstile> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  using MP MP 05 17 03 .

lemma 19: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r\<close>
  using MP 01 18 .

lemma 20: \<open>\<turnstile> p \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> q\<close>
  using MP 19 15 .

lemma 21: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 05 20 .

lemma 22: \<open>\<turnstile> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 21 01 .

lemma 23: \<open>\<turnstile> ((q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s\<close>
  using MP 01 21 .

lemma 24: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP MP 23 15 03 .

lemma 25: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s\<close>
  using MP 21 06 .

lemma 26: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
  using MP 25 24 .

lemma 28: \<open>\<turnstile> (((r \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> s\<close>
  using MP 01 26 .

lemma 29: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> r\<close>
  using MP 28 26 .

lemma 31: \<open>\<turnstile> (p \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (s \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> r\<close>
  using MP 07 29 .

lemma 32: \<open>\<turnstile> ((p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (s \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> r\<close>
  using MP 21 31 .

lemma 33: \<open>\<turnstile> (p \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> (s \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 32 18 .

lemma 34: \<open>\<turnstile> (s \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> s) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 21 33 .

lemma 35: \<open>\<turnstile> (p \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> r) \<^bold>\<longrightarrow> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> r\<close>
  using MP 34 22 .

lemma 36: \<open>\<turnstile> \<^bold>\<not> p \<^bold>\<longrightarrow> p \<^bold>\<longrightarrow> q\<close>
  using MP 21 03 .

lemmas
  Tran = 01 and
  Clavius = 02 and
  Expl = 03 and
  Frege' = 05 and
  Clavius' = 15 and
  Id = 16 and
  Simp = 18 and
  Swap = 21 and
  Tran' = 22 and
  Peirce = 24 and
  Frege = 35 and
  Expl' = 36

theorem 00: \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t\<rangle>p\<close>
  using SR Id .

corollary \<open>\<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p \<Longrightarrow> \<turnstile> q \<^bold>\<longrightarrow> \<langle>t\<rangle>p\<close>
proof -
  assume \<open>\<turnstile> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
  with MP MP 01 show ?thesis
    using 00 .
qed

section \<open>Semantics\<close>

type_synonym ('a, 'f, 'p) model = \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<times> ('p \<Rightarrow> 'a list \<Rightarrow> bool)\<close>

fun semantics_tm :: \<open>(nat \<Rightarrow> 'a) \<times> ('f \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'f tm \<Rightarrow> 'a\<close> (\<open>\<lparr>_\<rparr>\<close>) where
  \<open>\<lparr>(E, _)\<rparr> (\<cdot>n) = E n\<close> |
  \<open>\<lparr>(E, F)\<rparr> (\<ddagger>f ts) = F f (map \<lparr>(E, F)\<rparr> ts)\<close>

fun semantics_fm :: \<open>('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> (\<open>\<lbrakk>_\<rbrakk>\<close>) where
  \<open>\<lbrakk>(E, F, G)\<rbrakk> (\<dagger>P ts) \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close> |
  \<open>\<lbrakk>(E, F, G)\<rbrakk> (\<^bold>\<not> p) \<longleftrightarrow> \<not> \<lbrakk>(E, F, G)\<rbrakk> p\<close> |
  \<open>\<lbrakk>(E, F, G)\<rbrakk> (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> \<lbrakk>(E, F, G)\<rbrakk> p \<longrightarrow> \<lbrakk>(E, F, G)\<rbrakk> q\<close> |
  \<open>\<lbrakk>(E, F, G)\<rbrakk> (\<^bold>\<forall>p) \<longleftrightarrow> (\<forall>x. \<lbrakk>(x \<then> E, F, G)\<rbrakk> p)\<close>

abbreviation valid :: \<open>('f, 'p) fm \<Rightarrow> bool\<close> (\<open>\<tturnstile> _\<close> [50] 50) where
  \<open>\<tturnstile> p \<equiv> \<forall>M :: ('f tm, _, _) model. \<lbrakk>M\<rbrakk> p\<close>

section \<open>Soundness\<close>

fun params_tm' where
  \<open>params_tm' (Var n) = {}\<close> |
  \<open>params_tm' (Fun a ts) = {a} \<union> (\<Union>t \<in> set ts. params_tm' t)\<close>

lemma params_tm [simp]: \<open>params_tm' t = params_tm t\<close>
  by (induct t) simp_all

primrec params_fm' where
  \<open>params_fm' (Pre b ts) = (\<Union>t \<in> set ts. params_tm' t)\<close> |
  \<open>params_fm' (Neg p) = params_fm' p\<close> |
  \<open>params_fm' (Imp p q) = params_fm' p \<union> params_fm' q\<close> |
  \<open>params_fm' (Uni p) = params_fm' p\<close>

lemma params_fm [simp]: \<open>params_fm' p = params_fm p\<close>
  by (induct p) simp_all

lemma new_params' [simp]:
  \<open>new_term c t = (c \<notin> params_tm' t)\<close>
  \<open>new_list c l = (c \<notin> (\<Union>t \<in> set l. params_tm' t))\<close>
  by (induct t and l rule: new_term.induct new_list.induct) simp_all

lemma new_params [simp]: \<open>new c p = (c \<notin> params_fm' p)\<close>
  by (induct p) simp_all

lemma upd_params_tm [simp]: \<open>f \<notin> params_tm t \<Longrightarrow> \<lparr>(E, F(f := x))\<rparr> t = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma upd_params_fm [simp]: \<open>f \<notin> params_fm p \<Longrightarrow> \<lbrakk>(E, F(f := x), G)\<rbrakk> p = \<lbrakk>(E, F, G)\<rbrakk> p\<close>
  by (induct p arbitrary: E) (auto cong: map_cong)

lemma env [simp]: \<open>P ((x \<then> E) n) = (P x \<then> \<lambda>n. P (E n)) n\<close>
  by (induct n) simp_all

lemma lift_lemma [simp]: \<open>\<lparr>(x \<then> E, F)\<rparr> (lift_tm t) = \<lparr>(E, F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_tm_semantics [simp]: \<open>\<lparr>(E, F)\<rparr> (sub_tm s t) = \<lparr>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F)\<rparr> t\<close>
  by (induct t) (auto cong: map_cong)

lemma sub_fm_semantics [simp]: \<open>\<lbrakk>(E, F, G)\<rbrakk> (sub_fm s p) = \<lbrakk>(\<lambda>n. \<lparr>(E, F)\<rparr> (s n), F, G)\<rbrakk> p\<close>
  by (induct p arbitrary: E s) (auto cong: map_cong)

theorem soundness: fixes M :: \<open>(_ , _, _) model\<close> assumes \<open>\<turnstile> p\<close> shows \<open>\<lbrakk>M\<rbrakk> p\<close>
proof -
  have \<open>\<lbrakk>(E, F, G)\<rbrakk> p\<close> if \<open>\<turnstile> p\<close> for E :: \<open>_ \<Rightarrow> 'a\<close> and F G
    using that
  proof (induct arbitrary: F)
    case (GR a p q)
    moreover from this have \<open>\<lbrakk>(E, F(a := x), G)\<rbrakk> (q \<^bold>\<longrightarrow> \<langle>\<star>a\<rangle>p)\<close> for x
      by blast
    ultimately show ?case
      by fastforce
  qed simp_all
  then show ?thesis
    using assms surj_pair by metis
qed

proposition \<open>\<turnstile> p \<longrightarrow> \<tturnstile> p\<close>
  using soundness by blast

section \<open>Completeness\<close>

primrec imply (\<open>_ \<leadsto> _\<close> [57, 56] 56) where
  \<open>([] \<leadsto> q) = q\<close> |
  \<open>(p # ps \<leadsto> q) = p \<^bold>\<longrightarrow> ps \<leadsto> q\<close>

abbreviation Calculus_assms (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  \<open>ps \<turnstile> q \<equiv> \<turnstile> ps \<leadsto> q\<close>

lemma imply_MP: \<open>\<turnstile> ps \<leadsto> (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> ps \<leadsto> p \<^bold>\<longrightarrow> ps \<leadsto> q\<close>
proof (induct ps)
  case Nil
  then show ?case
    using Frege Simp MP imply.simps(1) by metis
next
  case (Cons r ps)
  then have \<open>\<turnstile> (r \<^bold>\<longrightarrow> ps \<leadsto> (p \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> (r \<^bold>\<longrightarrow> ps \<leadsto> p) \<^bold>\<longrightarrow> r \<^bold>\<longrightarrow> ps \<leadsto> q\<close>
    using Frege Simp MP by meson
  then show ?case
    by simp
qed

lemma MP': \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> ps \<turnstile> p \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_MP MP by metis

lemma imply_Cons [intro]: \<open>ps \<turnstile> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (auto intro: MP Simp)

lemma imply_head [intro]: \<open>p # ps \<turnstile> p\<close>
  by (induct ps) (simp add: Id, metis MP Simp Swap imply.simps(2))

lemma add_imply [simp]: \<open>\<turnstile> q \<Longrightarrow> ps \<turnstile> q\<close>
  using imply_head by (metis MP imply.simps(2))

lemma imply_mem [simp]: \<open>p \<in> set ps \<Longrightarrow> ps \<turnstile> p\<close>
  by (induct ps) (use imply_Cons imply_head in auto)

lemma deduct1: \<open>ps \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # ps \<turnstile> q\<close>
  by (meson MP' imply_Cons imply_head)

lemma imply_append [iff]: \<open>(ps @ qs \<leadsto> r) = (ps \<leadsto> qs \<leadsto> r)\<close>
  by (induct ps) simp_all

lemma imply_swap_append: \<open>ps @ qs \<turnstile> r \<Longrightarrow> qs @ ps \<turnstile> r\<close>
proof (induct qs arbitrary: ps)
  case Cons
  then show ?case
    by (metis deduct1 imply.simps(2) imply_append)
qed simp

lemma deduct2: \<open>p # ps \<turnstile> q \<Longrightarrow> ps \<turnstile> p \<^bold>\<longrightarrow> q\<close>
  by (metis imply.simps imply_append imply_swap_append)

lemmas deduct [iff] = deduct1 deduct2

lemma cut: \<open>p # ps \<turnstile> r \<Longrightarrow> q # ps \<turnstile> p \<Longrightarrow> q # ps \<turnstile> r\<close>
  by (meson MP' deduct2 imply_Cons)

lemma imply_weaken: \<open>ps \<turnstile> q \<Longrightarrow> set ps \<subseteq> set ps' \<Longrightarrow> ps' \<turnstile> q\<close>
  by (induct ps arbitrary: q) (simp, metis MP' deduct2 imply_mem insert_subset list.set(2))

interpretation Derivations Calculus_assms
  unfolding Derivations_def using imply_weaken by blast

abbreviation Truth (\<open>\<^bold>\<top>\<close>) where \<open>\<^bold>\<top> \<equiv> (\<lambda>p. p \<^bold>\<longrightarrow> p) (\<section>undefined)\<close>

abbreviation Falsity (\<open>\<^bold>\<bottom>\<close>) where \<open>\<^bold>\<bottom> \<equiv> \<^bold>\<not> \<^bold>\<top>\<close>

lemma Falsity_negation: \<open>p # A \<turnstile> \<^bold>\<bottom> \<longleftrightarrow> A \<turnstile> \<^bold>\<not> p\<close>
proof -
  have \<open>\<forall>A p q. A \<turnstile> (q \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> p \<longrightarrow> A \<turnstile> p\<close>
    using MP' by blast
  moreover have \<open>\<forall>A p q. A \<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> p\<close>
    using add_imply Expl' by blast
  moreover have \<open>\<forall>A p q. A \<turnstile> (\<^bold>\<not> p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> (q \<^bold>\<longrightarrow> p) \<^bold>\<longrightarrow> p\<close>
    using add_imply Clavius' by blast
  ultimately show ?thesis
    using MP' deduct by (metis (no_types))
qed

definition consistent :: \<open>('f, 'p) fm set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>

lemma imply_params_fm: \<open>params_fm (ps \<leadsto> q) = params_fm q \<union> (\<Union>p \<in> set ps. params_fm p)\<close>
  by (induct ps) auto

lemma inconsistent_fm:
  assumes \<open>consistent S\<close> \<open>\<not> consistent ({p} \<union> S)\<close>
  obtains S' where \<open>set S' \<subseteq> S\<close> and \<open>p # S' \<turnstile> \<^bold>\<bottom>\<close>
proof -
  obtain S' where S': \<open>set S' \<subseteq> {p} \<union> S\<close> \<open>p \<in> set S'\<close> \<open>S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms unfolding consistent_def by blast
  then obtain S'' where S'': \<open>set (p # S'') = set S'\<close> \<open>p \<notin> set S''\<close>
    using Diff_insert_absorb list.set(2) mk_disjoint_insert set_removeAll by (metis (no_types))
  then have \<open>p # S'' \<turnstile> \<^bold>\<bottom>\<close>
    using \<open>S' \<turnstile> \<^bold>\<bottom>\<close> imply_weaken by blast
  then show ?thesis
    using that S'' S'(1) Diff_insert_absorb Diff_subset_conv list.set(2) by metis
qed

lemma consistent_add_instance:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>consistent S\<close> \<open>\<^bold>\<forall>p \<in> S\<close>
  shows \<open>consistent ({\<langle>t\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<langle>t\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>\<langle>t\<rangle>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  moreover have \<open>\<turnstile> \<^bold>\<forall>p \<^bold>\<longrightarrow> \<langle>t\<rangle>p\<close>
    using SR Id .
  ultimately have \<open>\<^bold>\<forall>p # S' \<turnstile> \<^bold>\<bottom>\<close>
    by (meson add_imply cut deduct(1))
  moreover have \<open>set ((\<^bold>\<forall>p) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

lemma GR': \<open>\<turnstile> \<^bold>\<not> \<langle>\<star>a\<rangle>p \<^bold>\<longrightarrow> q \<Longrightarrow> \<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> q\<close> if \<open>new a p\<close> and \<open>new a q\<close>
proof -
  assume \<open>\<turnstile> \<^bold>\<not> \<langle>\<star>a\<rangle>p \<^bold>\<longrightarrow> q\<close>
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> \<langle>\<star>a\<rangle>p\<close>
    using MP Clavius Expl' Tran by (metis (no_types, opaque_lifting))
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<langle>\<star>a\<rangle>p\<close>
    using MP Clavius Expl' Tran by (metis (no_types, opaque_lifting))
  then have \<open>\<turnstile> \<^bold>\<not> q \<^bold>\<longrightarrow> \<^bold>\<forall>p\<close>
    using that by (auto intro: GR)
  then have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> q\<close>
    using MP Clavius Expl' Tran by (metis (no_types, opaque_lifting))
  then show ?thesis
    using MP Clavius Expl' Tran by (metis (no_types, opaque_lifting))
qed

primrec sub_fn_tm :: \<open>('f \<Rightarrow> 'f) \<Rightarrow> 'f tm \<Rightarrow> 'f tm\<close> where
  \<open>sub_fn_tm s (\<cdot>n) = \<cdot>n\<close> |
  \<open>sub_fn_tm s (\<ddagger>f ts) = \<ddagger>(s f) (map (sub_fn_tm s) ts)\<close>

primrec sub_fn_fm :: \<open>('f \<Rightarrow> 'f) \<Rightarrow> ('f, 'p) fm \<Rightarrow> ('f, 'p) fm\<close> where
  \<open>sub_fn_fm s (\<dagger>P ts) = \<dagger>P (map (sub_fn_tm s) ts)\<close> |
  \<open>sub_fn_fm s (\<^bold>\<not> p) = \<^bold>\<not> sub_fn_fm s p\<close> |
  \<open>sub_fn_fm s (p \<^bold>\<longrightarrow> q) = sub_fn_fm s p \<^bold>\<longrightarrow> sub_fn_fm s q\<close> |
  \<open>sub_fn_fm s (\<^bold>\<forall>p) = \<^bold>\<forall>(sub_fn_fm s p)\<close>

abbreviation \<open>params S \<equiv> \<Union>p \<in> S. params_fm p\<close>

lemma sub_fn_fm_lift [simp]:
  \<open>sub_fn_tm f (lift_tm t) = lift_tm (sub_fn_tm f t)\<close>
  by (induct t) simp_all

lemma sub_fn_tm_fresh_away [simp]: \<open>fresh \<notin> params_tm t \<Longrightarrow>
    sub_fn_tm (id(fresh := a)) (sub_fn_tm (id(a := fresh)) t) = t\<close>
  by (induct t, simp_all, metis (no_types, lifting) comp_apply map_idI)

lemma sub_fn_fm_fresh_away [simp]: \<open>fresh \<notin> params_fm p \<Longrightarrow>
    sub_fn_fm (id(fresh := a)) (sub_fn_fm (id(a := fresh)) p) = p\<close>
  by (induct p, simp_all, simp add: map_idI)

lemma sub_fn_tm_one_fresh [simp]: \<open>fresh \<notin> params_tm t \<Longrightarrow>
    sub_fn_tm (id(fresh := a)) t = t\<close>
  by (induct t, auto simp: map_idI)

lemma sub_fn_fm_one_fresh [simp]: \<open>fresh \<notin> params_fm p \<Longrightarrow>
    sub_fn_fm (id(fresh := a)) p = p\<close>
  by (induct p, simp_all, simp add: map_idI)

lemma sub_fn_tm_fresh [simp]: \<open>x \<notin> params_tm t \<Longrightarrow>
    sub_fn_tm (f(x := y)) t = sub_fn_tm f t\<close>
  by (induct t, simp_all, meson)

lemma sub_fn_fm_fresh [simp]: \<open>x \<notin> params_fm p \<Longrightarrow>
    sub_fn_fm (f(x := y)) p = sub_fn_fm f p\<close>
  by (induct p, simp_all)

lemma fresh_after_sub_fn_tm: \<open>c \<noteq> n \<Longrightarrow>
    n \<notin> params_tm (sub_fn_tm (id(n := c)) t)\<close>
  by (induct t, simp_all)

lemma fresh_sub_fn_tm_image: \<open>c \<notin> params_tm t \<Longrightarrow> d \<notin> f ` (params_tm t) \<Longrightarrow>
    d \<notin> params_tm (sub_fn_tm (f(c := d)) t)\<close>
  by (induct t, auto)

lemma fresh_sub_fn_fm_image: \<open>c \<notin> params_fm p \<Longrightarrow> d \<notin> f ` (params_fm p) \<Longrightarrow>
    d \<notin> params_fm (sub_fn_fm (f(c := d)) p)\<close>
  by (induct p, simp_all, use fresh_sub_fn_tm_image in fastforce, blast)

lemma finite_params_tm [simp]: \<open>finite (params_tm t)\<close>
  by (induct t) simp_all

lemma finite_params_fm [simp]: \<open>finite (params_fm p)\<close>
  by (induct p) simp_all

lemma sub_tm_Var [simp]: \<open>sub_tm \<cdot> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma reduce_Var [simp]: \<open>(\<cdot> 0 \<then> \<lambda>n. \<cdot> (Suc n)) = \<cdot>\<close>
proof (rule ext)
  show \<open>(\<cdot> 0 \<then> \<lambda>n. \<cdot> (Suc n)) n = \<cdot>n\<close> for n
    by (induct n) simp_all
qed

lemma sub_fm_Var [simp]: \<open>sub_fm \<cdot> p = p\<close>
  by (induct p) (auto cong: map_cong)

lemma semantics_tm_id [simp]: \<open>\<lparr>(\<cdot>, \<ddagger>)\<rparr> t = t\<close>
  by (induct t) (auto cong: map_cong)

lemma semantics_tm_id_map [simp]: \<open>map \<lparr>(\<cdot>, \<ddagger>)\<rparr> ts = ts\<close>
  by (auto cong: map_cong)

lemma sub_fn_tm_sub_tm [simp]:
  \<open>sub_fn_tm f (sub_tm s t) = sub_tm (\<lambda>x \<Rightarrow> sub_fn_tm f (s x)) (sub_fn_tm f t)\<close>
  by (induct t) simp_all

lemma sub_fn_fm_sub_fm [simp]:
  \<open>sub_fn_fm f (sub_fm s p) = sub_fm (\<lambda>x \<Rightarrow> sub_fn_tm f (s x)) (sub_fn_fm f p)\<close>
  by (induct p arbitrary: s f, simp_all)

lemma sub_fn_fm_inst [simp]:
  \<open>sub_fn_fm f (\<langle>t\<rangle> p) = \<langle>sub_fn_tm f t\<rangle> (sub_fn_fm f p)\<close>
  by (induct p, simp_all)

text \<open>The built-in \<open>size\<close> is not invariant under substitution.\<close>

primrec size_fm :: \<open>('f, 'p) fm \<Rightarrow> nat\<close> where
  \<open>size_fm (\<dagger>_ _) = 1\<close> |
  \<open>size_fm (\<^bold>\<not> p) = 1 + size_fm p\<close> |
  \<open>size_fm (p \<^bold>\<longrightarrow> q) = 1 + size_fm p + size_fm q\<close> |
  \<open>size_fm (\<^bold>\<forall>p) = 1 + size_fm p\<close>

lemma size_sub_fm [simp]: \<open>size_fm (sub_fm s p) = size_fm p\<close>
  by (induct p arbitrary: s) simp_all

lemma consistent_add_witness:
  assumes \<open>consistent S\<close> \<open>\<^bold>\<not> (\<^bold>\<forall>p) \<in> S\<close> \<open>a \<notin> params S\<close>
  shows \<open>consistent ({\<^bold>\<not> \<langle>\<star>a\<rangle>p} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {\<^bold>\<not> \<langle>\<star>a\<rangle>p} \<union> S \<and> S' \<turnstile> \<^bold>\<bottom>\<close>
  then obtain S' where \<open>set S' \<subseteq> S\<close> and \<open>(\<^bold>\<not> \<langle>\<star>a\<rangle>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    using assms inconsistent_fm unfolding consistent_def by blast
  then have \<open>\<turnstile> \<^bold>\<not> \<langle>\<star>a\<rangle>p \<^bold>\<longrightarrow> S' \<leadsto> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>a \<notin> params_fm p\<close>
    using assms(2,3) by auto
  moreover have \<open>\<forall>p \<in> set S'. a \<notin> params_fm p\<close>
    using \<open>set S' \<subseteq> S\<close> assms(3) by auto
  then have \<open>a \<notin> params_fm (S' \<leadsto> \<^bold>\<bottom>)\<close>
    by (simp add: imply_params_fm)
  ultimately have \<open>\<turnstile> \<^bold>\<not> (\<^bold>\<forall>p) \<^bold>\<longrightarrow> S' \<leadsto> \<^bold>\<bottom>\<close>
    using GR' by fastforce
  then have \<open>\<^bold>\<not> (\<^bold>\<forall>p) # S' \<turnstile> \<^bold>\<bottom>\<close>
    by simp
  moreover have \<open>set ((\<^bold>\<not> (\<^bold>\<forall>p)) # S') \<subseteq> S\<close>
    using \<open>set S' \<subseteq> S\<close> assms(2) by simp
  ultimately show False
    using assms(1) unfolding consistent_def by blast
qed

fun witness :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) fm set \<Rightarrow> ('f, 'p) fm set\<close> where
  \<open>witness (\<^bold>\<not> \<^bold>\<forall>p) S = {\<^bold>\<not> \<langle>\<star>(SOME a. a \<notin> params ({p} \<union> S))\<rangle>p}\<close> |
  \<open>witness _ _ = {}\<close>

lemma consistent_witness':
  assumes \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params S)\<close>
  shows \<open>consistent (witness p S \<union> {p} \<union> S)\<close>
  using assms
proof (induct p S rule: witness.induct)
  case (1 p S)
  have \<open>infinite (UNIV - params ({p} \<union> S))\<close>
    using 1(2) by (simp add: infinite_Diff_fin_Un)
  then have \<open>\<exists>a. a \<notin> params ({p} \<union> S)\<close>
    by (simp add: not_finite_existsD set_diff_eq)
  then have \<open>(SOME a. a \<notin> params ({p} \<union> S)) \<notin> params ({p} \<union> S)\<close>
    by (rule someI_ex)
  then obtain a where a: \<open>witness (\<^bold>\<not> \<^bold>\<forall>p) S = {\<^bold>\<not> \<langle>\<star>a\<rangle>p}\<close> \<open>a \<notin> params ({\<^bold>\<not> \<^bold>\<forall>p} \<union> S)\<close>
    by simp
  then show ?case
    using 1(1-2) a(1) consistent_add_witness[where S=\<open>{\<^bold>\<not> \<^bold>\<forall>p} \<union> S\<close>] by fastforce
qed (auto simp: assms)

interpretation MCS_Saturation consistent params_fm witness
proof
  fix S S' :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent S\<close> \<open>S' \<subseteq> S\<close>
  then show \<open>consistent S'\<close>
    unfolding consistent_def by blast
next
  fix S :: \<open>('f, 'p) fm set\<close>
  assume \<open>\<not> consistent S\<close>
  then show \<open>\<exists>S'\<subseteq>S. finite S' \<and> \<not> consistent S'\<close>
    unfolding consistent_def by blast
next
  fix p :: \<open>('f, 'p) fm\<close>
  show \<open>finite (params_fm p)\<close>
    by simp
next
  fix p and S :: \<open>('f, 'p) fm set\<close>
  show \<open>finite (params (witness p S))\<close>
    by (induct p S rule: witness.induct) simp_all
next
  fix p and S :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent ({p} \<union> S)\<close> \<open>infinite (UNIV - params S)\<close>
  then show \<open>consistent (witness p S \<union> {p} \<union> S)\<close>
    using consistent_witness' by fast
next
  show \<open>infinite (UNIV :: ('f, 'p) fm set)\<close>
    using infinite_UNIV_size[of \<open>\<lambda>p. p \<^bold>\<longrightarrow> p\<close>] by simp
qed

interpretation Derivations_MCS_Cut Calculus_assms consistent \<open>\<^bold>\<bottom>\<close>
proof
  fix S :: \<open>('f, 'p) fm set\<close>
  show \<open>consistent S = (\<nexists>S'. set S' \<subseteq> S \<and> S' \<turnstile> \<^bold>\<bottom>)\<close>
    unfolding consistent_def ..
next
  fix A and p :: \<open>('f, 'p) fm\<close>
  assume \<open>p \<in> set A\<close>
  then show \<open>A \<turnstile> p\<close>
    by simp
next
  fix A B and p q :: \<open>('f, 'p) fm\<close>
  assume \<open>A \<turnstile> p\<close> \<open>p # B \<turnstile> q\<close>
  then show \<open>A @ B \<turnstile> q\<close>
    using MP' add_imply imply_append by (metis imply.simps(2))
qed

abbreviation hmodel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model\<close> where
  \<open>hmodel H \<equiv> (\<cdot>, \<ddagger>, \<lambda>P ts. \<dagger>P ts \<in> H)\<close>

fun semics ::
  \<open>('a, 'f, 'p) model \<Rightarrow> (('a, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool) \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>semics (E, F, G) _ (\<dagger>P ts) \<longleftrightarrow> G P (map \<lparr>(E, F)\<rparr> ts)\<close> |
  \<open>semics (E, F, G) r (\<^bold>\<not> p) \<longleftrightarrow> \<not> r (E, F, G) p\<close> |
  \<open>semics (E, F, G) r (p \<^bold>\<longrightarrow> q) \<longleftrightarrow> r (E, F, G) p \<longrightarrow> r (E, F, G) q\<close> |
  \<open>semics (E, F, G) r (\<^bold>\<forall>p) \<longleftrightarrow> (\<forall>x. r (x \<then> E, F, G) p)\<close>

fun rel :: \<open>('f, 'p) fm set \<Rightarrow> ('f tm, 'f, 'p) model \<Rightarrow> ('f, 'p) fm \<Rightarrow> bool\<close> where
  \<open>rel H (E, _, _) p = (sub_fm E p \<in> H)\<close>

theorem Hintikka_model':
  assumes \<open>\<And>p. semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
  shows \<open>p \<in> H \<longleftrightarrow> \<lbrakk>hmodel H\<rbrakk> p\<close>
proof (induct p rule: wf_induct[where r=\<open>measure size_fm\<close>])
  case 1
  then show ?case ..
next
  case (2 x)
  then show ?case
    using assms[of x] by (cases x) simp_all
qed

lemma Hintikka_Extend:
  assumes \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  shows \<open>semics (hmodel H) (rel H) p \<longleftrightarrow> p \<in> H\<close>
proof (cases p)
  case (Neg p)
  have \<open>\<not> p \<in> H \<longleftrightarrow> \<^bold>\<not> p \<in> H\<close> for p
    using Falsity_negation assms MCS_derive MCS_derive_fls by metis
  then show ?thesis
    using Neg by simp
next
  case (Imp p q)
  have \<open>p # A \<turnstile> \<^bold>\<bottom> \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> q\<close> \<open>A \<turnstile> q \<Longrightarrow> A \<turnstile> p \<^bold>\<longrightarrow> q\<close> \<open>A \<turnstile> p \<^bold>\<longrightarrow> q \<Longrightarrow> p # A \<turnstile> q\<close> for A
    by (metis MP' add_imply deduct2 MP 01 02 03) blast+
  then have \<open>(p \<in> H \<longrightarrow> q \<in> H) \<longleftrightarrow> p \<^bold>\<longrightarrow> q \<in> H\<close>
    using assms(1-3) MCS_derive MCS_derive_fls by (metis insert_subset list.set(2))
  then show ?thesis
    using Imp by simp
next
  case (Uni p)
  have \<open>(\<forall>x. \<langle>x\<rangle>p \<in> H) \<longleftrightarrow> (\<^bold>\<forall>p \<in> H)\<close>
  proof
    assume \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close>
    show \<open>\<^bold>\<forall>p \<in> H\<close>
    proof (rule ccontr)
      have \<open>\<not> p \<in> H \<longleftrightarrow> \<^bold>\<not> p \<in> H\<close> for p
        using Falsity_negation assms MCS_derive MCS_derive_fls by metis
      moreover assume \<open>\<^bold>\<forall>p \<notin> H\<close>
      then have \<open>consistent ({\<^bold>\<not> \<^bold>\<forall>p} \<union> H)\<close>
        using assms(1) calculation by (simp add: insert_absorb)
      then have \<open>\<^bold>\<not> \<^bold>\<forall>p \<in> H\<close>
        using assms(2) unfolding maximal_def by blast
      then obtain a where \<open>\<^bold>\<not> \<langle>\<star>a\<rangle>p \<in> H\<close>
        using assms(3) unfolding saturated_def by fastforce
      moreover have \<open>\<langle>\<star>a\<rangle>p \<in> H\<close>
        using \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close> by blast
      ultimately show False
        by blast
    qed
  next
    assume \<open>\<^bold>\<forall>p \<in> H\<close>
    then show \<open>\<forall>x. \<langle>x\<rangle>p \<in> H\<close>
      using assms(1-3) consistent_add_instance maximal_def by blast
  qed
  then show ?thesis
    using Uni by simp
qed simp

interpretation Truth_Saturation
  consistent params_fm witness semics semantics_fm \<open>\<lambda>H. {hmodel H}\<close> rel
proof unfold_locales
  fix p and M :: \<open>('a tm, 'f, 'p) model\<close>
  show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> semics M semantics_fm p\<close>
    by (cases M, induct p) auto
next
  fix p and H :: \<open>('f, 'p) fm set\<close> and M :: \<open>('f tm, 'f, 'p) model\<close>
  assume \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close> \<open>M \<in> {hmodel H}\<close>
  then show \<open>\<lbrakk>M\<rbrakk> p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_model' by auto
next
  fix H :: \<open>('f, 'p) fm set\<close>
  assume \<open>consistent H\<close> \<open>maximal H\<close> \<open>saturated H\<close>
  then show \<open>\<forall>M \<in> {hmodel H}. \<forall>p. semics M (rel H) p \<longleftrightarrow> rel H M p\<close>
    using Hintikka_Extend by auto
qed

datatype marker = VarM | FunM | TmM | PreM | NegM | ImpM | UniM

type_synonym ('f, 'p) enc = \<open>('f + 'p) + marker \<times> nat\<close>

abbreviation \<open>FUNS f \<equiv> Inl (Inl f)\<close>
abbreviation \<open>PRES p \<equiv> Inl (Inr p)\<close>

abbreviation \<open>VAR n \<equiv> Inr (VarM, n)\<close>
abbreviation \<open>FUN n \<equiv> Inr (FunM, n)\<close>
abbreviation \<open>TM n \<equiv> Inr (TmM, n)\<close>

abbreviation \<open>PRE n \<equiv> Inr (PreM, n)\<close>
abbreviation \<open>NEG \<equiv> Inr (NegM, 0)\<close>
abbreviation \<open>IMP n \<equiv> Inr (NegM, n)\<close>
abbreviation \<open>UNI \<equiv> Inr (UniM, 0)\<close>

primrec
  encode_tm :: \<open>'f tm \<Rightarrow> ('f, 'p) enc list\<close> and
  encode_tms :: \<open>'f tm list \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_tm (\<cdot>n) = [VAR n]\<close> |
  \<open>encode_tm (\<ddagger>f ts) = FUN (length ts) # FUNS f # encode_tms ts\<close> |
  \<open>encode_tms [] = []\<close> |
  \<open>encode_tms (t # ts) = TM (length (encode_tm t)) # encode_tm t @ encode_tms ts\<close>

lemma encode_tm_ne [simp]: \<open>encode_tm t \<noteq> []\<close>
  by (induct t) auto

lemma inj_encode_tm':
  \<open>(encode_tm t :: ('f, 'p) enc list) = encode_tm s \<Longrightarrow> t = s\<close>
  \<open>(encode_tms ts :: ('f, 'p) enc list) = encode_tms ss \<Longrightarrow> ts = ss\<close>
proof (induct t and ts arbitrary: s and ss rule: encode_tm.induct encode_tms.induct)
  case (Var n)
  then show ?case
    by (cases s) auto
next
  case (Fun f fts)
  then show ?case
    by (cases s) auto
next
  case Nil_tm
  then show ?case
    by (cases ss) auto
next
  case (Cons_tm t ts)
  then show ?case
    by (cases ss) auto
qed

lemma inj_encode_tm: \<open>inj encode_tm\<close>
  unfolding inj_def using inj_encode_tm' by blast

primrec encode_fm :: \<open>('f, 'p) fm \<Rightarrow> ('f, 'p) enc list\<close> where
  \<open>encode_fm (\<dagger>P ts) = PRE (length ts) # PRES P # encode_tms ts\<close> |
  \<open>encode_fm (\<^bold>\<not> p) = NEG # encode_fm p\<close> |
  \<open>encode_fm (p \<^bold>\<longrightarrow> q) = IMP (length (encode_fm p)) # encode_fm p @ encode_fm q\<close> |
  \<open>encode_fm (\<^bold>\<forall>p) = UNI # encode_fm p\<close>

lemma encode_fm_ne [simp]: \<open>encode_fm p \<noteq> []\<close>
  by (induct p) auto

lemma inj_encode_fm': \<open>encode_fm p = encode_fm q \<Longrightarrow> p = q\<close>
proof (induct p arbitrary: q)
  case Pre
  then show ?case
    by (cases q) (auto simp: inj_encode_tm')
next
  case Neg
  then show ?case
    by (cases q) auto
next
  case Imp
  then show ?case
    by (cases q) auto
next
  case Uni
  then show ?case
    by (cases q) auto
qed

lemma inj_encode_fm: \<open>inj encode_fm\<close>
  unfolding inj_def using inj_encode_fm' by blast

lemma finite_marker: \<open>finite (UNIV :: marker set)\<close>
proof -
  have \<open>p \<in> {VarM, FunM, TmM, NegM, PreM, ImpM, UniM}\<close> for p
    by (cases p) auto
  then show ?thesis
    by (meson ex_new_if_finite finite.emptyI finite_insert)
qed

lemma card_of_fm:
  assumes \<open>infinite (UNIV :: 'f set)\<close>
  shows \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: 'f set| +c |UNIV :: 'p set|\<close>
proof -
  have \<open>|UNIV :: marker set| \<le>o |UNIV :: nat set|\<close>
    using finite_marker finite_iff_ordLess_natLeq infinite_UNIV_nat
      infinite_iff_natLeq_ordLeq ordLess_imp_ordLeq ordLess_ordLeq_trans by meson
  moreover have \<open>infinite (UNIV :: ('f + 'p) set)\<close>
    using assms by simp
  ultimately have \<open>|UNIV :: ('f, 'p) enc list set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using card_of_params_marker_lists by blast
  moreover have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f, 'p) enc list set|\<close>
    using card_of_ordLeq inj_encode_fm by blast
  ultimately have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV :: ('f + 'p) set|\<close>
    using ordLeq_transitive by blast
  then show ?thesis
    unfolding csum_def by simp
qed

theorem strong_completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>infinite (UNIV :: 'f set)\<close>
    and \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params S|\<close>
    and \<open>\<forall>M :: ('f tm, _, _) model. (\<forall>q \<in> S. \<lbrakk>M\<rbrakk> q) \<longrightarrow> \<lbrakk>M\<rbrakk> p\<close>
  shows \<open>\<exists>A. set A \<subseteq> S \<and> A \<turnstile> p\<close>
proof (rule ccontr)
  assume \<open>\<nexists>A. set A \<subseteq> S \<and> A \<turnstile> p\<close>
  then have *: \<open>\<nexists>A. set A \<subseteq> S \<and> \<^bold>\<not> p # A \<turnstile> \<^bold>\<bottom>\<close>
    using MP' add_imply deduct2 Clavius MP Expl Simp Tran by metis
  let ?S = \<open>{\<^bold>\<not> p} \<union> S\<close>
  let ?H = \<open>Extend ?S\<close>
  have \<open>consistent ?S\<close>
    using * by (meson consistent_def derive_split1 assms(2))
  moreover have \<open>infinite (UNIV - params S)\<close>
    using assms(1,2)
    by (metis Cinfinite_csum Cnotzero_UNIV Field_card_of cinfinite_def cinfinite_mono)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params S - params_fm (\<^bold>\<not> p)|\<close>
    using assms(2) fm.set_finite(1) card_of_Un_diff_infinite ordIso_iff_ordLeq ordLeq_transitive
      finite_marker finite_iff_ordLess_natLeq infinite_UNIV_nat infinite_iff_natLeq_ordLeq
      ordLess_ordLeq_trans by meson
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - (params S \<union> params_fm (\<^bold>\<not> p))|\<close>
    by (metis Set_Diff_Un)
  then have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV - params ?S|\<close>
    by (metis UN_insert insert_is_Un sup_commute)
  then have \<open>|UNIV :: ('f, 'p) fm set| \<le>o |UNIV - params ?S|\<close>
    using assms card_of_fm ordLeq_transitive by blast
  ultimately have \<open>consistent ?H\<close> \<open>maximal ?H\<close> \<open>saturated ?H\<close>
    using MCS_Extend by fast+
  then have \<open>p \<in> ?H \<longleftrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using truth_lemma_saturation by fastforce
  then have \<open>p \<in> ?S \<longrightarrow> \<lbrakk>hmodel ?H\<rbrakk> p\<close> for p
    using Extend_subset by blast
  then have \<open>\<lbrakk>hmodel ?H\<rbrakk> (\<^bold>\<not> p)\<close> \<open>\<forall>q \<in> S. \<lbrakk>hmodel ?H\<rbrakk> q\<close>
    by blast+
  moreover from this have \<open>\<lbrakk>hmodel ?H\<rbrakk> p\<close>
    using assms(3) by blast
  ultimately show False
    by simp
qed

theorem completeness:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>infinite (UNIV :: 'f set)\<close>
    and \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
    and \<open>\<tturnstile> p\<close>
  shows \<open>\<turnstile> p\<close>
proof -
  have \<open>|UNIV :: 'f set| +c |UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
    using assms(1,2) Field_card_of card_of_Plus_infinite csum_def ordIso_iff_ordLeq by metis
  then show ?thesis
    using assms(1,3) strong_completeness[where S=\<open>{}\<close>] by auto
qed

section \<open>Main Result\<close>

theorem main [iff]:
  fixes p :: \<open>('f, 'p) fm\<close>
  assumes \<open>infinite (UNIV :: 'f set)\<close>
    and \<open>|UNIV :: 'p set| \<le>o |UNIV :: 'f set|\<close>
  shows \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close>
  using assms completeness soundness by fast

proposition \<open>\<turnstile> p \<longleftrightarrow> \<tturnstile> p\<close> for p :: \<open>(nat, nat) fm\<close>
  using infinite_iff_card_of_nat by blast

end
