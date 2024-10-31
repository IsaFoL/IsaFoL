theory Ground_Ordered_Resolution
  imports
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus
    Isabelle_2024_Compatibility
    Superposition_Calculus.Ground_Ctxt_Extra
    Superposition_Calculus.HOL_Extra
    Superposition_Calculus.Transitive_Closure_Extra
    Min_Max_Least_Greatest.Min_Max_Least_Greatest_FSet
    Min_Max_Least_Greatest.Min_Max_Least_Greatest_Multiset
    Superposition_Calculus.Multiset_Extra
    Superposition_Calculus.Relation_Extra
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

primrec mset_lit :: "'a literal \<Rightarrow> 'a multiset" where
  "mset_lit (Pos A) = {#A#}" |
  "mset_lit (Neg A) = {#A, A#}"

type_synonym 't atom = "'t"


section \<open>Ground Resolution Calculus\<close>

locale ground_ordered_resolution_calculus =
  fixes
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    select :: "'f gterm atom clause \<Rightarrow> 'f gterm atom clause"
  assumes
    transp_less_trm[simp]: "transp (\<prec>\<^sub>t)" and
    asymp_less_trm[intro]: "asymp (\<prec>\<^sub>t)" and
    wfP_less_trm[intro]: "wfP (\<prec>\<^sub>t)" and
    totalp_less_trm[intro]: "totalp (\<prec>\<^sub>t)" and
    less_trm_compatible_with_gctxt[simp]: "\<And>ctxt t t'. t \<prec>\<^sub>t t' \<Longrightarrow> ctxt\<langle>t\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t'\<rangle>\<^sub>G" and
    less_trm_if_subterm[simp]: "\<And>t ctxt. ctxt \<noteq> \<box>\<^sub>G \<Longrightarrow> t \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G" and
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_lits: "\<And>C L. L \<in># select C \<Longrightarrow> is_neg L"
begin

lemma irreflp_on_less_trm[simp]: "irreflp_on A (\<prec>\<^sub>t)"
  by (metis asympD asymp_less_trm irreflp_onI)

abbreviation lesseq_trm (infix "\<preceq>\<^sub>t" 50) where
  "lesseq_trm \<equiv> (\<prec>\<^sub>t)\<^sup>=\<^sup>="

lemma lesseq_trm_if_subtermeq: "t \<preceq>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
  using less_trm_if_subterm
  by (metis gctxt_ident_iff_eq_GHole reflclp_iff)

definition less_lit ::
  "'f gterm atom literal \<Rightarrow> 'f gterm atom literal \<Rightarrow> bool" (infix "\<prec>\<^sub>l" 50) where
  "less_lit L1 L2 \<equiv> multp (\<prec>\<^sub>t) (mset_lit L1) (mset_lit L2)"

abbreviation lesseq_lit (infix "\<preceq>\<^sub>l" 50) where
  "lesseq_lit \<equiv> (\<prec>\<^sub>l)\<^sup>=\<^sup>="

abbreviation less_cls ::
  "'f gterm atom clause \<Rightarrow> 'f gterm atom clause \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
  "less_cls \<equiv> multp (\<prec>\<^sub>l)"

abbreviation lesseq_cls (infix "\<preceq>\<^sub>c" 50) where
  "lesseq_cls \<equiv> (\<prec>\<^sub>c)\<^sup>=\<^sup>="

lemma transp_on_less_lit[simp]: "transp_on A (\<prec>\<^sub>l)"
  by (smt (verit, best) less_lit_def transpE transp_less_trm transp_multp transp_onI)

corollary transp_less_lit: "transp (\<prec>\<^sub>l)"
  by simp

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: transp_multp)

lemma asymp_on_less_lit[simp]: "asymp_on A (\<prec>\<^sub>l)"
  by (metis asympD asymp_less_trm asymp_multp\<^sub>H\<^sub>O asymp_onI less_lit_def multp_eq_multp\<^sub>H\<^sub>O
      transp_less_trm)

corollary asymp_less_lit[simp]: "asymp (\<prec>\<^sub>l)"
  by simp

lemma asymp_less_cls[simp]: "asymp (\<prec>\<^sub>c)"
  by (simp add: asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)

lemma irreflp_on_less_lit[simp]: "irreflp_on A (\<prec>\<^sub>l)"
  by (simp only: asymp_on_less_lit irreflp_on_if_asymp_on)

lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfp_multp wfp_if_convertible_to_wfp by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfp_multp by blast

lemma totalp_on_less_lit[simp]: "totalp_on A (\<prec>\<^sub>l)"
proof (rule totalp_onI)
  fix L1 L2 :: "'f gterm atom literal"
  assume "L1 \<noteq> L2"

  show "L1 \<prec>\<^sub>l L2 \<or> L2 \<prec>\<^sub>l L1"
    unfolding less_lit_def
  proof (rule totalp_multp[THEN totalpD])
    show "totalp (\<prec>\<^sub>t)"
      using totalp_less_trm .
  next
    show "transp (\<prec>\<^sub>t)"
      using transp_less_trm .
  next
    show "mset_lit L1 \<noteq> mset_lit L2"
      using \<open>L1 \<noteq> L2\<close>
      by (cases L1; cases L2) (auto simp add: add_eq_conv_ex)
  qed
qed

corollary totalp_less_lit: "totalp (\<prec>\<^sub>l)"
  by simp

lemma totalp_less_cls[simp]: "totalp (\<prec>\<^sub>c)"
proof (rule totalp_multp)
  show "totalp (\<prec>\<^sub>l)"
    by simp
next
  show "transp (\<prec>\<^sub>l)"
    by simp
qed

interpretation term_order: linorder lesseq_trm less_trm
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

interpretation literal_order: linorder lesseq_lit less_lit
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>l y) = (x \<preceq>\<^sub>l y \<and> \<not> y \<preceq>\<^sub>l x)"
    by (metis asympD asymp_less_lit reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>l x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l z \<Longrightarrow> x \<preceq>\<^sub>l z"
    by (meson transpE transp_less_lit transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<Longrightarrow> y \<preceq>\<^sub>l x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_lit reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>l y \<or> y \<preceq>\<^sub>l x"
    by (metis reflclp_iff totalpD totalp_less_lit)
qed

interpretation clause_order: linorder lesseq_cls less_cls
proof unfold_locales
  show "\<And>x y. (x \<prec>\<^sub>c y) = (x \<preceq>\<^sub>c y \<and> \<not> y \<preceq>\<^sub>c x)"
    by (metis asympD asymp_less_cls reflclp_iff)
next
  show "\<And>x. x \<preceq>\<^sub>c x"
    by simp
next
  show "\<And>x y z. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c z \<Longrightarrow> x \<preceq>\<^sub>c z"
    by (meson transpE transp_less_cls transp_on_reflclp)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<Longrightarrow> y \<preceq>\<^sub>c x \<Longrightarrow> x = y"
    by (metis asympD asymp_less_cls reflclp_iff)
next
  show "\<And>x y. x \<preceq>\<^sub>c y \<or> y \<preceq>\<^sub>c x"
    by (metis reflclp_iff totalpD totalp_less_cls)
qed

lemma less_lit_simps[simp]:
  "Pos A\<^sub>1 \<prec>\<^sub>l Pos A\<^sub>2 \<longleftrightarrow> A\<^sub>1 \<prec>\<^sub>t A\<^sub>2"
  "Pos A\<^sub>1 \<prec>\<^sub>l Neg A\<^sub>2 \<longleftrightarrow> A\<^sub>1 \<preceq>\<^sub>t A\<^sub>2"
  "Neg A\<^sub>1 \<prec>\<^sub>l Neg A\<^sub>2 \<longleftrightarrow> A\<^sub>1 \<prec>\<^sub>t A\<^sub>2"
  "Neg A\<^sub>1 \<prec>\<^sub>l Pos A\<^sub>2 \<longleftrightarrow> A\<^sub>1 \<prec>\<^sub>t A\<^sub>2"
  by (auto simp add: less_lit_def)


subsection \<open>Ground Rules\<close>

abbreviation is_maximal_lit :: "'f gterm literal \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_maximal_lit L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal_lit :: "'f gterm literal \<Rightarrow> 'f gterm clause \<Rightarrow> bool" where
  "is_strictly_maximal_lit L M \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) M L"

inductive ground_resolution ::
  "'f gterm atom clause \<Rightarrow> 'f gterm atom clause \<Rightarrow> 'f gterm atom clause \<Rightarrow> bool"
where
  ground_resolutionI: "
    P\<^sub>1 = add_mset (Neg t) P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset (Pos t) P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal_lit (Neg t) P\<^sub>1 \<or> Neg t \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit (Pos t) P\<^sub>2 \<Longrightarrow>
    C = P\<^sub>1' + P\<^sub>2' \<Longrightarrow>
    ground_resolution P\<^sub>1 P\<^sub>2 C"

inductive ground_factoring :: "'f gterm atom clause \<Rightarrow> 'f gterm atom clause \<Rightarrow> bool" where
  ground_factoringI: "
    P = add_mset (Pos t) (add_mset (Pos t) P') \<Longrightarrow>
    select P = {#} \<Longrightarrow>
    is_maximal_lit (Pos t) P \<Longrightarrow>
    C = add_mset (Pos t) P' \<Longrightarrow>
    ground_factoring P C"


subsection \<open>Ground Layer\<close>

definition G_Inf :: "'f gterm atom clause inference set" where
  "G_Inf =
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. ground_resolution P\<^sub>1 P\<^sub>2 C} \<union>
    {Infer [P] C | P C. ground_factoring P C}"

abbreviation G_Bot :: "'f gterm atom clause set" where
  "G_Bot \<equiv> {{#}}"

definition G_entails :: "'f gterm atom clause set \<Rightarrow> 'f gterm atom clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm set). I \<TTurnstile>s N\<^sub>1 \<longrightarrow> I \<TTurnstile>s N\<^sub>2)"


subsection \<open>Correctness\<close>

lemma soundness_ground_resolution:
  assumes
    step: "ground_resolution P1 P2 C"
  shows "G_entails {P1, P2} {C}"
  using step
proof (cases P1 P2 C rule: ground_resolution.cases)
  case (ground_resolutionI t P\<^sub>1' P\<^sub>2')

  show ?thesis
    unfolding G_entails_def true_clss_singleton
    unfolding true_clss_insert
  proof (intro allI impI, elim conjE)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile> P1" and "I \<TTurnstile> P2"
    then obtain K1 K2 :: "'f gterm atom literal" where
      "K1 \<in># P1" and "I \<TTurnstile>l K1" and "K2 \<in># P2" and "I \<TTurnstile>l K2"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> C"
    proof (cases "K1 = Neg t")
      case K1_def: True
      hence "I \<TTurnstile>l Neg t"
        using \<open>I \<TTurnstile>l K1\<close> by simp

      show ?thesis
      proof (cases "K2 = Pos t")
        case K2_def: True
        hence "I \<TTurnstile>l Pos t"
          using \<open>I \<TTurnstile>l K2\<close> by simp
        hence False
          using \<open>I \<TTurnstile>l Neg t\<close> by simp
        thus ?thesis ..
      next
        case False
        hence "K2 \<in># P\<^sub>2'"
          using \<open>K2 \<in># P2\<close>
          unfolding ground_resolutionI by simp
        hence "I \<TTurnstile> P\<^sub>2'"
          using \<open>I \<TTurnstile>l K2\<close> by blast
        thus ?thesis
          unfolding ground_resolutionI by simp
      qed
    next
      case False
      hence "K1 \<in># P\<^sub>1'"
        using \<open>K1 \<in># P1\<close>
        unfolding ground_resolutionI by simp
      hence "I \<TTurnstile> P\<^sub>1'"
        using \<open>I \<TTurnstile>l K1\<close> by blast
      thus ?thesis
        unfolding ground_resolutionI by simp
    qed
  qed
qed

lemma soundness_ground_factoring:
  assumes step: "ground_factoring P C"
  shows "G_entails {P} {C}"
  using step
proof (cases P C rule: ground_factoring.cases)
  case (ground_factoringI t P')
  show ?thesis
    unfolding G_entails_def true_clss_singleton
  proof (intro allI impI)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile> P"
    then obtain K :: "'f gterm atom literal" where
      "K \<in># P" and "I \<TTurnstile>l K"
      by (auto simp: true_cls_def)

    show "I \<TTurnstile> C"
    proof (cases "K = Pos t")
      case True
      hence "I \<TTurnstile>l Pos t"
        using \<open>I \<TTurnstile>l K\<close> by metis
      thus ?thesis
        unfolding ground_factoringI
        by (metis true_cls_add_mset)
    next
      case False
      hence "K \<in># P'"
        using \<open>K \<in># P\<close>
        unfolding ground_factoringI
        by auto
      hence "K \<in># C"
        unfolding ground_factoringI
        by simp
      thus ?thesis
        using \<open>I \<TTurnstile>l K\<close> by blast
    qed
  qed
qed

interpretation G: sound_inference_system G_Inf G_Bot G_entails
proof unfold_locales
  show "G_Bot \<noteq> {}"
    by simp
next
  show "\<And>B N. B \<in> G_Bot \<Longrightarrow> G_entails {B} N"
    by (simp add: G_entails_def)
next
  show "\<And>N2 N1. N2 \<subseteq> N1 \<Longrightarrow> G_entails N1 N2"
    by (auto simp: G_entails_def elim!: true_clss_mono[rotated])
next
  fix N1 N2 assume ball_G_entails: "\<forall>C \<in> N2. G_entails N1 {C}"
  show "G_entails N1 N2"
    unfolding G_entails_def
  proof (intro allI impI)
    fix I :: "'f gterm set"
    assume "I \<TTurnstile>s N1"
    hence "\<forall>C \<in> N2. I \<TTurnstile>s {C}"
      using ball_G_entails by (simp add: G_entails_def)
    then show "I \<TTurnstile>s N2"
      by (simp add: true_clss_def)
  qed
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def by simp
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> G_entails (set (prems_of \<iota>)) {concl_of \<iota>}"
    unfolding G_Inf_def
    using soundness_ground_resolution
    using soundness_ground_factoring
    by (auto simp: G_entails_def)
qed


subsection \<open>Redundancy Criterion\<close>

lemma ground_resolution_smaller_conclusion:
  assumes
    step: "ground_resolution P1 P2 C"
  shows "C \<prec>\<^sub>c P1"
  using step
proof (cases P1 P2 C rule: ground_resolution.cases)
  case (ground_resolutionI t P\<^sub>1' P\<^sub>2')
  have "\<forall>k\<in>#P\<^sub>2'. k \<prec>\<^sub>l Pos t"
    using \<open>is_strictly_maximal_lit (Pos t) P2\<close> \<open>P2 = add_mset (Pos t) P\<^sub>2'\<close>
    by (simp add: literal_order.is_greatest_in_mset_iff)
  moreover have "\<And>A. Pos A \<prec>\<^sub>l Neg A"
    by (simp add: less_lit_def)
  ultimately have "\<forall>k\<in>#P\<^sub>2'. k \<prec>\<^sub>l Neg t"
    by (metis transp_def transp_less_lit)
  hence "P\<^sub>2' \<prec>\<^sub>c {#Neg t#}"
    using one_step_implies_multp[of "{#Neg t#}" P\<^sub>2' "(\<prec>\<^sub>l)" "{#}"] by simp
  hence "P\<^sub>2' + P\<^sub>1' \<prec>\<^sub>c add_mset (Neg t) P\<^sub>1'"
    using multp_cancel[of "(\<prec>\<^sub>l)" P\<^sub>1' P\<^sub>2' "{#Neg t#}"] by simp
  thus ?thesis
    unfolding ground_resolutionI
    by (simp only: add.commute)
qed

lemma ground_factoring_smaller_conclusion:
  assumes step: "ground_factoring P C"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: ground_factoring.cases)
  case (ground_factoringI t P')
  then show ?thesis
    by (metis add_mset_add_single mset_subset_eq_exists_conv multi_self_add_other_not_self
        multp_subset_supersetI totalpD totalp_less_cls transp_less_lit)
qed

interpretation G: calculus_with_finitary_standard_redundancy G_Inf G_Bot G_entails "(\<prec>\<^sub>c)"
proof unfold_locales
  show "transp (\<prec>\<^sub>c)"
    using transp_less_cls .
next
  show "wfP (\<prec>\<^sub>c)"
    using wfP_less_cls .
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  fix \<iota>
  have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P\<^sub>2, P\<^sub>1] C" and
      infer: "ground_resolution P\<^sub>1 P\<^sub>2 C"
    for P\<^sub>2 P\<^sub>1 C
    unfolding \<iota>_def
    using infer
    using ground_resolution_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "ground_factoring P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_factoring_smaller_conclusion
    by simp

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    unfolding G_Inf_def
    by fast
qed


subsection \<open>Refutational Completeness\<close>

context
  fixes N :: "'f gterm atom clause set"
begin

function production :: "'f gterm atom clause \<Rightarrow> 'f gterm set" where
  "production C = {A | A C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production D) \<TTurnstile> C}"
  by simp_all

termination production
proof (relation "{(x, y). x \<prec>\<^sub>c y}")
  show "wf {(x, y). x \<prec>\<^sub>c y}"
    using wfP_less_cls
    by (simp add: wfp_def)
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed

declare production.simps[simp del]

end

lemma Uniq_striclty_maximal_lit_in_ground_cls:
  "\<exists>\<^sub>\<le>\<^sub>1L. is_strictly_maximal_lit L C"
proof (rule Uniq_is_greatest_in_mset_wrt)
  show "transp_on (set_mset C) (\<prec>\<^sub>l)"
    by (auto intro: transp_on_subset transp_less_lit)
next
  show "asymp_on (set_mset C) (\<prec>\<^sub>l)"
    by (auto intro: asymp_on_subset asymp_less_lit)
next
  show "totalp_on (set_mset C) (\<prec>\<^sub>l)"
    by (auto intro: totalp_on_subset totalp_less_lit)
qed

lemma production_eq_empty_or_singleton:
  "production N C = {} \<or> (\<exists>A. production N C = {A})"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1A. is_strictly_maximal_lit (Pos A) C"
    using Uniq_striclty_maximal_lit_in_ground_cls
    by (metis (mono_tags, lifting) Uniq_def literal.inject(1))
  hence "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'. C = add_mset (Pos A) C' \<and> is_strictly_maximal_lit (Pos A) C"
    by (simp add: Uniq_def)
  hence Uniq_production: "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production N D) \<TTurnstile> C"
    using Uniq_antimono'
    by (smt (verit) Uniq_def Uniq_prodI case_prod_conv)
  show ?thesis
    unfolding production.simps[of N C]
    using Collect_eq_if_Uniq[OF Uniq_production]
    by (smt (verit, best) Collect_cong Collect_empty_eq Uniq_def Uniq_production case_prod_conv
        insertCI mem_Collect_eq)
qed

lemma production_eq_singleton_if_atom_in_production:
  assumes "A \<in> production N C"
  shows "production N C = {A}"
  using assms production_eq_empty_or_singleton
  by force

definition interp where
  "interp N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production N D)"

lemma interp_mempty[simp]: "interp N {#} = {}"
proof -
  have "\<nexists>C. C \<prec>\<^sub>c {#}"
    by (metis clause_order.order.asym subset_implies_multp subset_mset.gr_zeroI)
  hence "{D \<in> N. D \<prec>\<^sub>c {#}} = {}"
    by simp
  thus ?thesis
    unfolding interp_def by auto
qed

lemma production_unfold: "production N C = {A | A C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> interp N C \<TTurnstile> C}"
  by (simp add: production.simps[of N C] interp_def)

lemma production_unfold': "production N C = {A | A.
    C \<in> N \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> interp N C \<TTurnstile> C}"
  unfolding production_unfold
  by (metis (mono_tags, lifting) literal_order.explode_greatest_in_mset)

lemma mem_productionE:
  assumes C_prod: "A \<in> production N C"
  obtains C' where
    "C \<in> N" and
    "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    "is_strictly_maximal_lit (Pos A) C" and
    "\<not> interp N C \<TTurnstile> C"
  using C_prod
  unfolding production.simps[of N C] mem_Collect_eq Let_def interp_def
  by (metis (no_types, lifting))

lemma production_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> production N C \<subseteq> interp N D"
  unfolding interp_def
  using production_unfold by blast

lemma Uniq_production_eq_singleton: "\<exists>\<^sub>\<le>\<^sub>1 C. production N C = {A}"
proof (rule Uniq_I)
  fix C D
  assume "production N C = {A}"
  hence "A \<in> production N C"
    by simp
  then obtain C' where
    "C \<in> N"
    "C = add_mset (Pos A) C'"
    "is_strictly_maximal_lit (Pos A) C"
    "\<not> interp N C \<TTurnstile> C"
    by (auto elim!: mem_productionE)

  assume "production N D = {A}"
  hence "A \<in> production N D"
    by simp
  then obtain D' where
    "D \<in> N"
    "D = add_mset (Pos A) D'"
    "is_strictly_maximal_lit (Pos A) D"
    "\<not> interp N D \<TTurnstile> D"
    by (auto elim!: mem_productionE)

  have "\<not> (C \<prec>\<^sub>c D)"
  proof (rule notI)
    assume "C \<prec>\<^sub>c D"
    hence "production N C \<subseteq> interp N D"
      using production_subset_if_less_cls by metis
    hence "A \<in> interp N D"
      unfolding \<open>production N C = {A}\<close> by simp
    hence "interp N D \<TTurnstile> D"
      unfolding \<open>D = add_mset (Pos A) D'\<close> by simp
    with \<open>\<not> interp N D \<TTurnstile> D\<close> show False
      by metis
  qed

  moreover have "\<not> (D \<prec>\<^sub>c C)"
  proof (rule notI)
    assume "D \<prec>\<^sub>c C"
    hence "production N D \<subseteq> interp N C"
      using production_subset_if_less_cls by metis
    hence "A \<in> interp N C"
      unfolding \<open>production N D = {A}\<close> by simp
    hence "interp N C \<TTurnstile> C"
      unfolding \<open>C = add_mset (Pos A) C'\<close> by simp
    with \<open>\<not> interp N C \<TTurnstile> C\<close> show False
      by metis
  qed

  ultimately show "C = D"
    by order
qed

lemma singleton_eq_CollectD: "{x} = {y. P y} \<Longrightarrow> P x"
  by blast

lemma subset_Union_mem_CollectI: "P x \<Longrightarrow> f x \<subseteq> (\<Union>y \<in> {z. P z}. f y)"
  by blast

lemma interp_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> interp N C \<subseteq> interp N D"
  by (smt (verit, best) UN_iff mem_Collect_eq interp_def subsetI transpD transp_less_cls)

lemma interp_subset_if_less_cls': "C \<prec>\<^sub>c D \<Longrightarrow> interp N C \<subseteq> interp N D \<union> production N D"
  using interp_subset_if_less_cls by blast

lemma split_Union_production:
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. production N C) =
    interp N D \<union> production N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. production N C)"
proof -
  have "N = {C \<in> N. C \<prec>\<^sub>c D} \<union> {D} \<union> {C \<in> N. D \<prec>\<^sub>c C}"
  proof (rule partition_set_around_element)
    show "totalp_on N (\<prec>\<^sub>c)"
      using totalp_less_cls totalp_on_subset by blast
  next
    show "D \<in> N"
      using D_in by simp
  qed
  hence "(\<Union>C \<in> N. production N C) =
      (\<Union>C \<in> {C \<in> N. C \<prec>\<^sub>c D}. production N C) \<union> production N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. production N C)"
    by auto
  thus "(\<Union>C \<in> N. production N C) =
    interp N D \<union> production N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. production N C)"
    by (simp add: interp_def)
qed

lemma split_Union_production':
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. production N C) = interp N D \<union> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. production N C)"
  using split_Union_production[OF D_in] D_in by auto

lemma split_interp:
  assumes "C \<in> N" and D_in: "D \<in> N" and "D \<prec>\<^sub>c C"
  shows "interp N C = interp N D \<union> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. production N C')"
proof -
  have "{D \<in> N. D \<prec>\<^sub>c C} =
        {y \<in> {D \<in> N. D \<prec>\<^sub>c C}. y \<prec>\<^sub>c D} \<union> {D} \<union> {y \<in> {D \<in> N. D \<prec>\<^sub>c C}. D \<prec>\<^sub>c y}"
  proof (rule partition_set_around_element)
    show "totalp_on {D \<in> N. D \<prec>\<^sub>c C} (\<prec>\<^sub>c)"
      using totalp_less_cls totalp_on_subset by blast
  next
    from D_in \<open>D \<prec>\<^sub>c C\<close> show "D \<in> {D \<in> N. D \<prec>\<^sub>c C}"
      by simp
  qed
  also have "\<dots> = {x \<in> N. x \<prec>\<^sub>c C \<and> x \<prec>\<^sub>c D} \<union> {D} \<union> {x \<in> N. D \<prec>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    by auto
  also have "\<dots> = {x \<in> N. x \<prec>\<^sub>c D} \<union> {D} \<union> {x \<in> N. D \<prec>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    using \<open>D \<prec>\<^sub>c C\<close> transp_less_cls
    by (metis (no_types, opaque_lifting) transpD)
  finally have Collect_N_lt_C: "{x \<in> N. x \<prec>\<^sub>c C} = {x \<in> N. x \<prec>\<^sub>c D} \<union> {x \<in> N. D \<preceq>\<^sub>c x \<and> x \<prec>\<^sub>c C}"
    by auto

  have "interp N C = (\<Union>C' \<in> {D \<in> N. D \<prec>\<^sub>c C}. production N C')"
    by (simp add: interp_def)
  also have "\<dots> = (\<Union>C' \<in> {x \<in> N. x \<prec>\<^sub>c D}. production N C') \<union> (\<Union>C' \<in> {x \<in> N. D \<preceq>\<^sub>c x \<and> x \<prec>\<^sub>c C}. production N C')"
    unfolding Collect_N_lt_C by simp
  finally show "interp N C = interp N D \<union> \<Union> (production N ` {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C})"
    unfolding interp_def by simp
qed

lemma less_imp_Interp_subseteq_interp: "C \<prec>\<^sub>c D \<Longrightarrow> interp N C \<union> production N C \<subseteq> interp N D"
  using interp_subset_if_less_cls production_subset_if_less_cls
  by (simp add: interp_def)

lemma not_interp_to_Interp_imp_le: "A \<notin> interp N C \<Longrightarrow> A \<in> interp N D \<union> production N D \<Longrightarrow> C \<preceq>\<^sub>c D"
  using less_imp_Interp_subseteq_interp
  by (metis (mono_tags, opaque_lifting) subsetD sup2CI totalpD totalp_less_cls)

lemma produces_imp_in_interp:
  assumes "Neg A \<in># C" and D_prod: "A \<in> production N D"
  shows "A \<in> interp N C"
proof -
  from D_prod have "Pos A \<in># D" and "is_strictly_maximal_lit (Pos A) D"
    by (auto elim: mem_productionE)

  have "D \<prec>\<^sub>c C"
  proof (rule multp_if_maximal_of_lhs_is_less)
    show "Pos A \<in># D"
      using \<open>Pos A \<in># D\<close> .
  next
    show "Neg A \<in># C"
      using \<open>Neg A \<in># C\<close> .
  next
    show "Pos A \<prec>\<^sub>l Neg A"
      by (simp add: less_lit_def subset_implies_multp)
  next
    show "is_maximal_lit (Pos A) D"
      using \<open>is_strictly_maximal_lit (Pos A) D\<close> by auto
  qed simp_all
  hence "\<not> (\<prec>\<^sub>c)\<^sup>=\<^sup>= C D"
    by (metis asympD asymp_less_cls reflclp_iff)
  thus ?thesis
  proof (rule contrapos_np)
    from D_prod show  "A \<notin> interp N C \<Longrightarrow> (\<prec>\<^sub>c)\<^sup>=\<^sup>= C D"
      using not_interp_to_Interp_imp_le by simp
  qed
qed

lemma neg_notin_Interp_not_produce:
  "Neg A \<in># C \<Longrightarrow> A \<notin> interp N D \<union> production N D \<Longrightarrow> C \<preceq>\<^sub>c D \<Longrightarrow> A \<notin> production N D''"
  using interp_subset_if_less_cls'
  by (metis Un_iff produces_imp_in_interp reflclp_iff sup.orderE)

lemma lift_interp_entails:
  assumes
    D_in: "D \<in> N" and
    D_entailed: "interp N D \<TTurnstile> D" and
    C_in: "C \<in> N" and
    D_lt_C: "D \<prec>\<^sub>c C"
  shows "interp N C \<TTurnstile> D"
proof -
  from D_entailed obtain L A where
    L_in: "L \<in># D" and
    L_eq_disj_L_eq: "L = Pos A \<and> A \<in> interp N D \<or> L = Neg A \<and> A \<notin> interp N D"
    unfolding true_cls_def true_lit_iff by metis

  have "interp N D \<subseteq> interp N C"
    using interp_subset_if_less_cls[OF D_lt_C] .

  from L_eq_disj_L_eq show "interp N C \<TTurnstile> D"
  proof (elim disjE conjE)
    assume "L = Pos A" and "A \<in> interp N D"
    thus "interp N C \<TTurnstile> D"
      using L_in \<open>interp N D \<subseteq> interp N C\<close> by auto
  next
    assume "L = Neg A" and "A \<notin> interp N D"
    hence "A \<notin> interp N C"
      using neg_notin_Interp_not_produce
      by (smt (verit, ccfv_threshold) L_in UN_E interp_def produces_imp_in_interp)
    thus "interp N C \<TTurnstile> D"
      using L_in \<open>L = Neg A\<close> by blast
  qed
qed

lemma lift_interp_entails_to_interp_production_entails:
  assumes
    C_in: "C \<in> N" and
    D_in: "D \<in> N" and
    C_lt_D: "D \<prec>\<^sub>c C" and
    D_entailed: "interp N C \<TTurnstile> D"
  shows "interp N C \<union> production N C \<TTurnstile> D"
proof -
  from D_entailed obtain L A where
    L_in: "L \<in># D" and
    L_eq_disj_L_eq: "L = Pos A \<and> A \<in> interp N C \<or> L = Neg A \<and> A \<notin> interp N C"
    unfolding true_cls_def true_lit_iff by metis

  from L_eq_disj_L_eq show "interp N C \<union> production N C \<TTurnstile> D"
  proof (elim disjE conjE)
    assume "L = Pos A" and "A \<in> interp N C"
    thus "interp N C \<union> production N C \<TTurnstile> D"
      using L_in by blast
  next
    assume "L = Neg A" and "A \<notin> interp N C"
    hence "A \<notin> interp N C \<union> production N C"
      using neg_notin_Interp_not_produce
      by (metis (no_types, opaque_lifting) C_lt_D L_in Un_iff interp_subset_if_less_cls
          produces_imp_in_interp subsetD)
    thus "interp N C \<union> production N C \<TTurnstile> D"
      using L_in \<open>L = Neg A\<close> by blast
  qed
qed

lemma lift_entailment_to_Union:
  fixes N D
  assumes
    D_in: "D \<in> N" and
    R\<^sub>D_entails_D: "interp N D \<TTurnstile> D"
  shows
    "(\<Union>C \<in> N. production N C) \<TTurnstile> D"
  using lift_interp_entails
  by (smt (verit, best) D_in R\<^sub>D_entails_D UN_iff produces_imp_in_interp split_Union_production'
      subsetD sup_ge1 true_cls_def true_lit_iff)


lemma
  assumes
    "D \<preceq>\<^sub>c C" and
    C_prod: "A \<in> production N C" and
    L_in: "L \<in># D"
  shows
    lesseq_trm_if_pos: "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and
    less_trm_if_neg: "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
proof -
  from C_prod obtain C' where
    C_def: "C = add_mset (Pos A) C'" and
    C_max_lit: "is_strictly_maximal_lit (Pos A) C"
    by (auto elim: mem_productionE)

  have "Pos A \<prec>\<^sub>l L" if "is_pos L" and "\<not> atm_of L \<preceq>\<^sub>t A"
  proof -
    from that(2) have "A \<prec>\<^sub>t atm_of L"
      using totalp_less_trm[THEN totalpD] by auto
    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L#}"
      by (smt (verit, del_insts) add.right_neutral empty_iff insert_iff one_step_implies_multp
          set_mset_add_mset_insert set_mset_empty transpD transp_less_trm union_mset_add_mset_right)
    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (cases L) (simp_all add: less_lit_def)
  qed

  moreover have "Pos A \<prec>\<^sub>l L" if "is_neg L" and "\<not> atm_of L \<prec>\<^sub>t A"
  proof -
    from that(2) have "A \<preceq>\<^sub>t atm_of L"
      using totalp_less_trm[THEN totalpD] by auto
    hence "multp (\<prec>\<^sub>t) {#A#} {#atm_of L, atm_of L#}"
      by (smt (z3) add_mset_add_single add_mset_remove_trivial add_mset_remove_trivial_iff
          empty_not_add_mset insert_DiffM insert_noteq_member one_step_implies_multp reflclp_iff
          transp_def transp_less_trm union_mset_add_mset_left union_mset_add_mset_right)
    with that(1) show "Pos A \<prec>\<^sub>l L"
      by (cases L) (simp_all add: less_lit_def)
  qed

  moreover have False if "Pos A \<prec>\<^sub>l L"
  proof -
    have "C \<prec>\<^sub>c D"
    proof (rule multp_if_maximal_of_lhs_is_less)
      show "Pos A \<in># C"
        by (simp add: C_def)
    next
      show "L \<in># D"
        using L_in by simp
    next
      show "is_maximal_lit (Pos A) C"
        using C_max_lit by auto
    next
      show "Pos A \<prec>\<^sub>l L"
        using that by simp
    qed simp_all
    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by (metis asympD reflclp_iff wfp_imp_asymp wfP_less_cls)
  qed

  ultimately show "is_pos L \<Longrightarrow> atm_of L \<preceq>\<^sub>t A" and "is_neg L \<Longrightarrow> atm_of L \<prec>\<^sub>t A"
    by metis+
qed

lemma less_trm_iff_less_cls_if_mem_production:
  assumes C_prod: "A\<^sub>C \<in> production N C" and D_prod: "A\<^sub>D \<in> production N D"
  shows "A\<^sub>C \<prec>\<^sub>t A\<^sub>D \<longleftrightarrow> C \<prec>\<^sub>c D"
proof -
  from C_prod obtain C' where
    "C \<in> N" and
    C_def: "C = add_mset (Pos A\<^sub>C) C'" and
    "is_strictly_maximal_lit (Pos A\<^sub>C) C"
    by (elim mem_productionE) simp
  hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>C"
    by (simp add: literal_order.is_greatest_in_mset_iff)

  from D_prod obtain D' where
    "D \<in> N" and
    D_def: "D = add_mset (Pos A\<^sub>D) D'" and
    "is_strictly_maximal_lit (Pos A\<^sub>D) D"
    by (elim mem_productionE) simp
  hence "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos A\<^sub>D"
    by (simp add: literal_order.is_greatest_in_mset_iff)

  show ?thesis
  proof (rule iffI)
    assume "A\<^sub>C \<prec>\<^sub>t A\<^sub>D"
    hence "Pos A\<^sub>C \<prec>\<^sub>l Pos A\<^sub>D"
      by (simp add: less_lit_def)
    moreover hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>D"
      using \<open>\<forall>L \<in># C'. L \<prec>\<^sub>l Pos A\<^sub>C\<close>
      by (meson transp_less_lit transpD)
    ultimately show "C \<prec>\<^sub>c D"
      using one_step_implies_multp[of D C _ "{#}"]
      by (simp add: D_def C_def)
  next
    assume "C \<prec>\<^sub>c D"
    hence "production N C \<subseteq> (\<Union> (production N ` {x \<in> N. x \<prec>\<^sub>c D}))"
      using \<open>C \<in> N\<close> by auto
    hence "A\<^sub>C \<in> (\<Union> (production N ` {x \<in> N. x \<prec>\<^sub>c D}))"
      using C_prod by auto
    hence "A\<^sub>C \<noteq> A\<^sub>D"
      by (metis D_prod interp_def mem_productionE true_cls_add_mset true_lit_iff)
    moreover have "\<not> (A\<^sub>D \<prec>\<^sub>t A\<^sub>C)"
      by (metis C_def D_prod \<open>C \<prec>\<^sub>c D\<close> asympD asymp_less_trm lesseq_trm_if_pos literal.disc(1)
          literal.sel(1) reflclp_iff union_single_eq_member)
    ultimately show "A\<^sub>C \<prec>\<^sub>t A\<^sub>D"
      using totalp_less_trm[THEN totalpD]
      using C_def D_def by auto
  qed
qed

lemma false_cls_if_productive_production:
  assumes C_prod: "A \<in> production N C" and "D \<in> N" and "C \<prec>\<^sub>c D"
  shows "\<not> interp N D \<TTurnstile> C - {#Pos A#}"
proof -
  from C_prod obtain C' where
    C_in: "C \<in> N" and
    C_def: "C = add_mset (Pos A) C'" and
    "select C = {#}" and
    Pox_A_max: "is_strictly_maximal_lit (Pos A) C" and
    "\<not> interp N C \<TTurnstile> C"
    by (rule mem_productionE) blast

  from \<open>D \<in> N\<close> \<open>C \<prec>\<^sub>c D\<close> have "A \<in> interp N D"
    using C_prod production_subset_if_less_cls by auto

  from \<open>D \<in> N\<close> have "interp N D \<subseteq> (\<Union>D \<in> N. production N D)"
    by (auto simp: interp_def)

  have "\<not> interp N D \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    have "C' \<prec>\<^sub>c C"
      by (simp add: C_def subset_implies_multp)
    hence "C' \<preceq>\<^sub>c C"
      by order

    show "\<not> interp N D \<TTurnstile>l L"
    proof (cases L)
      case (Pos A\<^sub>L)
      moreover have "A\<^sub>L \<notin> interp N D"
      proof -
        have "\<forall>y\<in>#C'. y \<prec>\<^sub>l Pos A"
          using Pox_A_max
          by (simp add: C_def literal_order.is_greatest_in_mset_iff)
        with Pos have "A\<^sub>L \<notin> insert A (interp N C)"
          using L_in \<open>\<not> interp N C \<TTurnstile> C\<close> C_def
          by blast

        moreover have "A\<^sub>L \<notin> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. production N D')"
        proof -
          have "A\<^sub>L \<preceq>\<^sub>t A"
            using Pos lesseq_trm_if_pos[OF \<open>C' \<preceq>\<^sub>c C\<close> C_prod \<open>L \<in># C'\<close>]
            by simp
          thus ?thesis
            using less_trm_iff_less_cls_if_mem_production
            using C_prod calculation interp_def by fastforce
        qed

        moreover have "interp N D =
          insert A (interp N C) \<union> (\<Union>D' \<in> {D' \<in> N. C \<prec>\<^sub>c D' \<and> D' \<prec>\<^sub>c D}. production N D')"
        proof -
          have "interp N D = (\<Union>D' \<in> {D' \<in> N. D' \<prec>\<^sub>c D}. production N D')"
            by (simp only: interp_def)
          also have "\<dots> = (\<Union>D' \<in> {D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y}. D' \<prec>\<^sub>c D}. production N D')"
            using partition_set_around_element[of N "(\<prec>\<^sub>c)", OF _ \<open>C \<in> N\<close>]
              totalp_on_subset[OF totalp_less_cls, simplified]
            by simp
          also have "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C \<and> y \<prec>\<^sub>c D} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            using \<open>C \<prec>\<^sub>c D\<close> by auto
          also have "\<dots> = (\<Union>D' \<in> {y \<in> N. y \<prec>\<^sub>c C} \<union> {C} \<union> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            by (metis (no_types, opaque_lifting) assms(3) transpD transp_less_cls)
          also have "\<dots> = interp N C \<union> production N C \<union> (\<Union>D' \<in> {y \<in> N. C \<prec>\<^sub>c y \<and> y \<prec>\<^sub>c D}. production N D')"
            by (auto simp: interp_def)
          finally show ?thesis
            using C_prod
            by (metis (no_types, lifting) empty_iff insertE insert_is_Un
                production_eq_empty_or_singleton sup_commute)
        qed

        ultimately show ?thesis
          by simp
      qed
      ultimately show ?thesis
        by simp
    next
      case (Neg A\<^sub>L)
      moreover have "A\<^sub>L \<in> interp N D"
        using Neg \<open>L \<in># C\<close> \<open>C \<prec>\<^sub>c D\<close> \<open>\<not> interp N C \<TTurnstile> C\<close> interp_subset_if_less_cls
        by blast
      ultimately show ?thesis
        by simp
    qed
  qed
  thus "\<not> interp N D \<TTurnstile> C - {#Pos A#}"
    by (simp add: C_def)
qed

lemma production_subset_Union_production:
  "\<And>C N. C \<in> N \<Longrightarrow> production N C \<subseteq> (\<Union>D \<in> N. production N D)"
  by auto

lemma interp_subset_Union_production:
  "\<And>C N. C \<in> N \<Longrightarrow> interp N C \<subseteq> (\<Union>D \<in> N. production N D)"
  by (simp add: split_Union_production')

lemma model_construction:
  fixes
    N :: "'f gterm atom clause set" and
    C :: "'f gterm atom clause"
  assumes "G.saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "production N C = {} \<longleftrightarrow> interp N C \<TTurnstile> C"
    "(\<Union>D \<in> N. production N D) \<TTurnstile> C"
    "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> interp N D \<TTurnstile> C"
  unfolding atomize_conj atomize_imp
  using wfP_less_cls C_in
proof (induction C arbitrary: D rule: wfp_induct_rule)
  case (less C)
  note IH = less.IH

  from \<open>{#} \<notin> N\<close> \<open>C \<in> N\<close> have "C \<noteq> {#}"
    by metis

  define I :: "'f gterm set" where
    "I = interp N C"

  have i: "interp N C \<TTurnstile> C \<longleftrightarrow> (production N C = {})"
  proof (rule iffI)
    show "interp N C \<TTurnstile> C \<Longrightarrow> production N C = {}"
      by (smt (z3) Collect_empty_eq interp_def production.elims)
  next
    assume "production N C = {}"
    show "interp N C \<TTurnstile> C"
    proof (cases "\<exists>A. Neg A \<in># C \<and> (Neg A \<in># select C \<or> select C = {#} \<and> is_maximal_lit (Neg A) C)")
      case ex_neg_lit_sel_or_max: True
      then obtain A where
        "Neg A \<in># C" and
        sel_or_max: "Neg A \<in># select C \<or> select C = {#} \<and> is_maximal_lit (Neg A) C"
        by metis
      then obtain C' where
        C_def: "C = add_mset (Neg A) C'"
        by (metis mset_add)

      show ?thesis
      proof (cases "A \<in> interp N C")
        case True
        then obtain D where
          "A \<in> production N D" and "D \<in> N" and "D \<prec>\<^sub>c C"
          unfolding interp_def by auto
        then obtain D' where
          D_def: "D = add_mset (Pos A) D'" and
          sel_D: "select D = {#}" and
          max_t_t': "is_strictly_maximal_lit (Pos A) D" and
          "\<not> interp N D \<TTurnstile> D"
          by (elim mem_productionE) fast

        have reso: "ground_resolution C D (C' + D')"
        proof (rule ground_resolutionI)
          show "C = add_mset (Neg A) C'"
            by (simp add: C_def)
        next
          show "D = add_mset (Pos A) D'"
            by (simp add: D_def)
        next
          show "D \<prec>\<^sub>c C"
            using \<open>D \<prec>\<^sub>c C\<close> .
        next
          show "select C = {#} \<and> is_maximal_lit (Neg A) C \<or> Neg A \<in># select C"
            using sel_or_max by auto
        next
          show "select D = {#}"
            using sel_D by blast
        next
          show "is_strictly_maximal_lit (Pos A) D"
            using max_t_t' .
        qed simp_all

        define \<iota> :: "'f gterm clause inference" where
          "\<iota> = Infer [D, C] (C' + D')"

        have "\<iota> \<in> G_Inf"
          using reso
          by (auto simp only: \<iota>_def G_Inf_def)

        moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close>
          by (auto simp add: \<iota>_def)

        ultimately have "\<iota> \<in> G.Inf_from N"
          by (auto simp: G.Inf_from_def)
        hence "\<iota> \<in> G.Red_I N"
          using \<open>G.saturated N\<close>
          by (auto simp: G.saturated_def)
        then obtain DD where
          DD_subset: "DD \<subseteq> N" and
          "finite DD" and
          DD_entails_CD: "G_entails (insert D DD) {C' + D'}" and
          ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
          unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq
          by (auto simp: \<iota>_def)

        moreover have "\<forall>D\<in> insert D DD. interp N C \<TTurnstile> D"
          using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
          using \<open>C \<in> N\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close> DD_subset ball_DD_lt_C
          by (metis in_mono insert_iff)

        ultimately have "interp N C \<TTurnstile> C' + D'"
          using DD_entails_CD
          unfolding G_entails_def
          by (simp add: I_def true_clss_def)

        moreover have "\<not> interp N D \<TTurnstile> D'"
          using \<open>\<not> interp N D \<TTurnstile> D\<close>
          using D_def by force

        moreover have "D' \<prec>\<^sub>c D"
          unfolding D_def
          by (simp add: subset_implies_multp)

        moreover have "\<not> interp N C \<TTurnstile> D'"
          using false_cls_if_productive_production[OF _ \<open>C \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close>]
          by (metis D_def \<open>A \<in> production N D\<close> remove1_mset_add_mset_If)

        ultimately show "interp N C \<TTurnstile> C"
          unfolding C_def by fast
      next
        case False
        thus ?thesis
          using \<open>Neg A \<in># C\<close>
          by (auto simp add: true_cls_def)
      qed
    next
      case False
      hence "select C = {#}"
        using select_subset select_negative_lits
        by (metis (no_types, opaque_lifting) Neg_atm_of_iff mset_subset_eqD multiset_nonemptyE)
        
      from False obtain A where Pos_A_in: "Pos A \<in># C" and max_Pos_A: "is_maximal_lit (Pos A) C"
        using ex_maximal_in_mset_wrt[OF transp_on_less_lit asymp_on_less_lit \<open>C \<noteq> {#}\<close>]
        using is_maximal_in_mset_wrt_iff[OF transp_on_less_lit asymp_on_less_lit]
        by (metis Neg_atm_of_iff \<open>select C = {#}\<close> is_pos_def)
      then obtain C' where C_def: "C = add_mset (Pos A) C'"
        by (meson mset_add)

      show ?thesis
      proof (cases "interp N C \<TTurnstile> C'")
        case True
        then show ?thesis
          using C_def by force
      next
        case False
        show ?thesis
        proof (cases "is_strictly_maximal_lit (Pos A) C")
          case strictly_maximal: True
          then show ?thesis
            using \<open>production N C = {}\<close> \<open>select C = {#}\<close> less.prems
            unfolding production_unfold[of N C] Collect_empty_eq
            using C_def by blast
        next
          case False
          hence "count C (Pos A) \<ge> 2"
            using max_Pos_A
            by (simp add: literal_order.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset)
          then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
            by (metis two_le_countE)

          define \<iota> :: "'f gterm clause inference" where
            "\<iota> = Infer [C] (add_mset (Pos A) C')"

          have eq_fact: "ground_factoring C (add_mset (Pos A) C')"
          proof (rule ground_factoringI)
            show "C = add_mset (Pos A) (add_mset (Pos A) C')"
              by (simp add: C_def)
          next
            show "select C = {#}"
              using \<open>select C = {#}\<close> .
          next
            show "is_maximal_lit (Pos A) C"
              using max_Pos_A .
          qed simp_all
          hence "\<iota> \<in> G_Inf"
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C \<in> N\<close>
            by (auto simp add: \<iota>_def)

          ultimately have "\<iota> \<in> G.Inf_from N"
            by (auto simp: G.Inf_from_def)
          hence "\<iota> \<in> G.Red_I N"
            using \<open>G.saturated N\<close>
            by (auto simp: G.saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_concl: "G_entails DD {add_mset (Pos A) C'}" and
            ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
            unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in>DD. interp N C \<TTurnstile> D"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
            using \<open>C \<in> N\<close> DD_subset ball_DD_lt_C
            by blast

          ultimately have "interp N C \<TTurnstile> add_mset (Pos A) C'"
            using DD_entails_concl
            unfolding G_entails_def
            by (simp add: I_def true_clss_def)
          then show ?thesis
            by (simp add: C_def joinI_right pair_imageI)
        qed
      qed
    qed
  qed

  moreover have iia: "(\<Union> (production N ` N)) \<TTurnstile> C"
    using production_eq_empty_or_singleton[of N C]
  proof (elim disjE exE)
    assume "production N C = {}"
    hence "interp N C \<TTurnstile> C"
      by (simp only: i)
    thus ?thesis
      using lift_entailment_to_Union[OF \<open>C \<in> N\<close>] by argo
  next
    fix A
    assume "production N C = {A}"
    hence prod: "A \<in> production N C"
      by simp

    from prod have "Pos A \<in># C"
      unfolding production.simps[of N C] mem_Collect_eq
      by force

    moreover from prod have "A \<in> \<Union> (production N ` N)"
      using \<open>C \<in> N\<close> production_subset_Union_production
      by fast
    
    ultimately show ?thesis
      by blast
  qed

  moreover have iib: "interp N D \<TTurnstile> C" if "D \<in> N" and "C \<prec>\<^sub>c D"
    using production_eq_empty_or_singleton[of N C, folded ]
  proof (elim disjE exE)
    assume "production N C = {}"
    hence "interp N C \<TTurnstile> C"
      unfolding i by simp
    thus ?thesis
      using lift_interp_entails[OF \<open>C \<in> N\<close> _ that] by argo
  next
    fix A assume "production N C = {A}"
    thus ?thesis
      by (metis Un_insert_right insertCI insert_subset less_imp_Interp_subseteq_interp
          mem_productionE pos_literal_in_imp_true_cls that(2) union_single_eq_member)
  qed

  ultimately show ?case
    by argo
qed

lemma
  assumes "clause_order.is_least_in_fset N C" and "A \<in> production (fset N) C"
  shows "\<And>A'. A' \<prec>\<^sub>t A \<Longrightarrow> A' \<notin> (\<Union>D \<in> fset N. production (fset N) D)"
  using assms less_trm_iff_less_cls_if_mem_production clause_order.is_least_in_fset_iff by auto

lemma lesser_atoms_not_in_previous_interp_are_not_in_final_interp_if_productive:
  assumes "A \<in> production (fset N) C"
  shows "\<And>A'. A' \<prec>\<^sub>t A \<Longrightarrow> A' \<notin> interp (fset N) C \<Longrightarrow> A' \<notin> (\<Union>D \<in> fset N. production (fset N) D)"
  using assms production_subset_if_less_cls less_trm_iff_less_cls_if_mem_production by fastforce

lemma lesser_atoms_not_in_previous_interp_are_not_in_final_interp_if_not_productive:
  assumes "literal_order.is_maximal_in_mset C L" and "production (fset N) C = {}"
  shows "\<And>A'. A' \<prec>\<^sub>t atm_of L \<Longrightarrow> A' \<notin> interp (fset N) C \<Longrightarrow> A' \<notin> (\<Union>D \<in> fset N. production (fset N) D)"
  using assms
  by (metis (no_types, lifting) UN_E UnCI less_trm_if_neg lesseq_trm_if_pos
      literal_order.is_maximal_in_mset_iff term_order.less_imp_not_less term_order.not_le
      not_interp_to_Interp_imp_le)

lemma lesser_atoms_not_in_previous_interp_are_not_in_final_interp:
  fixes A
  assumes
    L_max: "literal_order.is_maximal_in_mset C L" and
    A_less: "A \<prec>\<^sub>t atm_of L" and
    A_no_in: "A \<notin> interp (fset N) C"
  shows "A \<notin> (\<Union>D \<in> fset N. production (fset N) D)"
proof (cases "production (fset N) C = {}")
  case True
  thus ?thesis
    using L_max A_less A_no_in
    using lesser_atoms_not_in_previous_interp_are_not_in_final_interp_if_not_productive
    by metis
next
  case False
  then obtain A' where C_produces_A': "A' \<in> production (fset N) C"
    by auto
  hence "is_strictly_maximal_lit (Pos A') C"
    unfolding production_unfold mem_Collect_eq by metis
  hence "literal_order.is_maximal_in_mset C (Pos A')"
    using literal_order.is_maximal_in_mset_if_is_greatest_in_mset by metis
  hence "L = Pos A'"
    using L_max
    by (metis Uniq_D literal_order.Uniq_is_maximal_in_mset)
  hence "atm_of L \<in> production (fset N) C"
    using C_produces_A' by simp
  thus ?thesis
    using L_max A_less A_no_in
    using lesser_atoms_not_in_previous_interp_are_not_in_final_interp_if_productive
    by metis
qed

lemma lesser_atoms_in_previous_interp_are_in_final_interp:
  fixes A
  assumes
    L_max: "literal_order.is_maximal_in_mset C L" and
    A_less: "A \<prec>\<^sub>t atm_of L" and
    A_in: "A \<in> interp N C"
  shows "A \<in> (\<Union>D \<in> N. production N D)"
  using A_in interp_def by fastforce

lemma interp_fixed_for_smaller_literals:
  fixes A
  assumes
    L_max: "literal_order.is_maximal_in_mset C L" and
    A_less: "A \<prec>\<^sub>t atm_of L" and
    "C \<prec>\<^sub>c D"
  shows "A \<in> interp N C \<longleftrightarrow> A \<in> interp N D"
proof (rule iffI)
  show "A \<in> interp N C \<Longrightarrow> A \<in> interp N D"
    using assms(3) interp_subset_if_less_cls by auto
next
  assume "A \<in> interp N D"

  then obtain E where "A \<in> production N E" and "E \<in> N" and "E \<prec>\<^sub>c D"
    unfolding interp_def by auto

  hence "literal_order.is_greatest_in_mset E (Pos A)"
    by (auto elim: mem_productionE)

  moreover have "Pos A \<prec>\<^sub>l L"
    by (metis A_less Neg_atm_of_iff less_lit_simps(1) less_lit_simps(2)
        literal_order.dual_order.strict_trans term_order.order_eq_iff literal.collapse(1))

  ultimately have "E \<prec>\<^sub>c C"
    using L_max
    using literal_order.multp\<^sub>H\<^sub>O_if_maximal_less_that_maximal multp\<^sub>D\<^sub>M_imp_multp multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M
    by blast

  hence "production N E \<subseteq> interp N C"
    by (simp add: production_subset_if_less_cls)

  thus "A \<in> interp N C"
    using \<open>A \<in> production N E\<close> by auto
qed

lemma neg_lits_not_in_model_stay_out_of_model:
  assumes
    L_in: "L \<in># C" and
    L_neg: "is_neg L" and
    atm_L_not_in: "atm_of L \<notin> interp N C"
  shows "atm_of L \<notin> (\<Union>D \<in> N. production N D)"
  using assms produces_imp_in_interp by force

lemma neg_lits_already_in_model_stay_in_model:
  assumes
    L_in: "L \<in># C" and
    L_neg: "is_neg L" and
    atm_L_not_in: "atm_of L \<in> interp N C"
  shows "atm_of L \<in> (\<Union>D \<in> N. production N D)"
  using atm_L_not_in interp_def by auto

lemma image_eq_imageI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
  shows "f ` X = g ` X"
  using assms by auto

lemma production_swap_clause_set:
  assumes
    agree: "{D \<in> N1. D \<preceq>\<^sub>c C} = {D \<in> N2. D \<preceq>\<^sub>c C}"
  shows "production N1 C = production N2 C"
  using agree
proof (induction C rule: wfp_induct_rule[OF wfP_less_cls])
  case hyps: (1 C)
  from hyps have AAA: "C \<in> N1 \<longleftrightarrow> C \<in> N2"
    by auto

  from hyps have "{D \<in> N1. D \<prec>\<^sub>c C} = {D \<in> N2. D \<prec>\<^sub>c C}"
    by blast

  have "production N1 ` {D \<in> N2. D \<prec>\<^sub>c C} = production N2 ` {D \<in> N2. D \<prec>\<^sub>c C}"
  proof (rule image_eq_imageI)
    fix x assume "x \<in> {D \<in> N2. D \<prec>\<^sub>c C}"
    hence "x \<in> N2" and "x \<prec>\<^sub>c C"
      by simp_all
    moreover have "{D \<in> N1. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x} = {D \<in> N2. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x}"
      using hyps.prems \<open>x \<prec>\<^sub>c C\<close> clause_order.order.strict_trans1 by blast
    ultimately show "production N1 x = production N2 x"
      using hyps.IH[rule_format, of x] by metis
  qed
  hence BBB: "interp N1 C = interp N2 C"
    unfolding interp_def \<open>{D \<in> N1. D \<prec>\<^sub>c C} = {D \<in> N2. D \<prec>\<^sub>c C}\<close>
    by argo

  show ?case
    unfolding production_unfold
    unfolding AAA BBB
    by simp
qed

lemma interp_swap_clause_set:
  assumes agree: "{D \<in> N1. D \<prec>\<^sub>c C} = {D \<in> N2. D \<prec>\<^sub>c C}"
  shows "interp N1 C = interp N2 C"
proof -
  have BBB: "production N1 ` {D \<in> N2. D \<prec>\<^sub>c C} = production N2 ` {D \<in> N2. D \<prec>\<^sub>c C}"
  proof (intro image_eq_imageI production_swap_clause_set)
    fix x
    assume "x \<in> {D \<in> N2. D \<prec>\<^sub>c C}"
    thus "{D \<in> N1. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x} = {D \<in> N2. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D x}"
      using agree clause_order.le_less_trans by blast
  qed

  show ?thesis
    unfolding interp_def
    unfolding agree BBB
    by argo
qed

definition interp' where
  "interp' N \<equiv> (\<Union>C \<in> N. production N C)"

lemma interp_eq_interp': "interp N D = interp' {C \<in> N. C \<prec>\<^sub>c D}"
proof -
  have "interp N D = interp {C \<in> N. C \<prec>\<^sub>c D} D"
  proof (rule interp_swap_clause_set)
    show "{Da \<in> N. Da \<prec>\<^sub>c D} = {Da \<in> {C \<in> N. C \<prec>\<^sub>c D}. Da \<prec>\<^sub>c D}"
      by blast
  qed

  also have "\<dots> = interp' {C \<in> N. C \<prec>\<^sub>c D}"
    unfolding interp_def interp'_def by blast

  finally show ?thesis .
qed

lemma production_unfold'': "production N C = {A | A.
    C \<in> N \<and> select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> interp' {B \<in> N. B \<prec>\<^sub>c C} \<TTurnstile> C}"
  unfolding production_unfold interp_eq_interp'
  using literal_order.explode_greatest_in_mset
  by metis

lemma Interp_swap_clause_set:
  assumes agree: "{D \<in> N1. D \<preceq>\<^sub>c C} = {D \<in> N2. D \<preceq>\<^sub>c C}"
  shows "interp N1 C \<union> production N1 C = interp N2 C \<union> production N2 C"
  using production_swap_clause_set[OF agree]
  using interp_swap_clause_set
  using agree
  by blast

lemma production_insert_greater_clause:
  assumes "C \<prec>\<^sub>c D"
  shows "production (insert D N) C = production N C"
proof (rule production_swap_clause_set)
  show "{Da \<in> insert D N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C} = {D \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C}"
    using \<open>C \<prec>\<^sub>c D\<close> by auto
qed

lemma interp_insert_greater_clause_strong:
  assumes "C \<preceq>\<^sub>c D"
  shows "interp (insert D N) C = interp N C"
proof (rule interp_swap_clause_set)
  show "{x \<in> insert D N. x \<prec>\<^sub>c C} = {x \<in> N. x \<prec>\<^sub>c C}"
    using \<open>C \<preceq>\<^sub>c D\<close> by auto
qed

lemma interp_insert_greater_clause:
  assumes "C \<prec>\<^sub>c D"
  shows "interp (insert D N) C = interp N C"
proof (rule interp_swap_clause_set)
  show "{x \<in> insert D N. x \<prec>\<^sub>c C} = {x \<in> N. x \<prec>\<^sub>c C}"
    using \<open>C \<prec>\<^sub>c D\<close> by auto
qed

lemma Interp_insert_greater_clause:
  assumes "C \<prec>\<^sub>c D"
  shows "interp (insert D N) C \<union> production (insert D N) C = interp N C \<union> production N C"
proof (rule Interp_swap_clause_set)
  show "{Da \<in> insert D N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C} = {D \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C}"
    using \<open>C \<prec>\<^sub>c D\<close> by auto
qed

lemma production_add_irrelevant_clause_to_set0:
  assumes
    fin: "finite N" and
    D_irrelevant: "E \<in> N" "E \<subset># D" "set_mset D = set_mset E" and
    no_select: "select E = {#}"
  shows "production (insert D N) D = {}"
proof -
  from D_irrelevant have "E \<prec>\<^sub>c D"
    using subset_implies_multp by metis
  hence prod_E_subset: "production (insert D N) E \<subseteq> interp (insert D N) D"
    using production_subset_if_less_cls by metis

  show ?thesis
  proof (cases "production (insert D N) E = {}")
    case True
    hence "(\<nexists>A. is_strictly_maximal_lit (Pos A) E) \<or> interp (insert D N) E \<TTurnstile> E"
      unfolding production_unfold
      using no_select
      by (smt (verit, del_insts) Collect_empty_eq \<open>E \<in> N\<close> diff_single_eq_union insertI2
          literal_order.is_greatest_in_mset_iff)
    hence "(\<nexists>A. is_strictly_maximal_lit (Pos A) D) \<or> interp (insert D N) D \<TTurnstile> D"
    proof (elim disjE)
      assume "\<nexists>A. is_strictly_maximal_lit (Pos A) E"
      hence "\<nexists>A. is_strictly_maximal_lit (Pos A) D"
      proof (rule contrapos_nn)
        show "\<exists>A. is_strictly_maximal_lit (Pos A) D \<Longrightarrow> \<exists>A. is_strictly_maximal_lit (Pos A) E"
          using \<open>E \<subset># D\<close> \<open>set_mset D = set_mset E\<close>
          unfolding literal_order.is_greatest_in_mset_iff
          by (metis (no_types, opaque_lifting) add_mset_remove_trivial_eq
              insert_union_subset_iff)
      qed
      thus ?thesis ..
    next
      assume "interp (insert D N) E \<TTurnstile> E"
      hence "interp (insert D N) D \<TTurnstile> D"
        using lift_interp_entails \<open>E \<in> N\<close> \<open>E \<prec>\<^sub>c D\<close>
        by (metis \<open>set_mset D = set_mset E\<close> insert_iff true_cls_def)
      thus ?thesis ..
    qed
    thus ?thesis
      unfolding production_unfold by auto
  next
    case False
    hence "interp (insert D N) D \<TTurnstile> D"
      using prod_E_subset
      by (metis \<open>set_mset D = set_mset E\<close> mem_productionE production_eq_empty_or_singleton
          insertCI insert_subset literal_order.is_greatest_in_mset_iff
          pos_literal_in_imp_true_cls)
    thus ?thesis
      unfolding production_unfold by simp
  qed
qed

lemma production_add_irrelevant_clause_to_set:
  assumes
    fin: "finite N" and
    C_in: "C \<in> N" and
    D_irrelevant: "\<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    no_select: "\<And>C. select C = {#}"
  shows "production (insert D N) C = production N C"
    using wfP_less_cls C_in
proof (induction C rule: wfp_induct_rule)
  case (less C)
  hence C_in_iff: "C \<in> insert D N \<longleftrightarrow> C \<in> N"
    by simp
  
  have interp_insert_eq: "interp (insert D N) C = interp N C"
  proof (cases "D \<prec>\<^sub>c C")
    case True
    hence "{x \<in> insert D N. x \<prec>\<^sub>c C} = insert D {x \<in> N. x \<prec>\<^sub>c C}"
      by auto
    hence "\<Union> (production (insert D N) ` {x \<in> insert D N. x \<prec>\<^sub>c C}) =
      production (insert D N) D \<union> \<Union> (production (insert D N) ` {D \<in> N. D \<prec>\<^sub>c C})"
      by simp
    also have "\<dots> = \<Union> (production (insert D N) ` {D \<in> N. D \<prec>\<^sub>c C})"
      using production_add_irrelevant_clause_to_set0
      using D_irrelevant fin no_select by force
    also have "\<dots> = \<Union> (production N ` {D \<in> N. D \<prec>\<^sub>c C})"
      using less.IH by simp
    finally show ?thesis
      unfolding interp_def .
  next
    case False
    then show ?thesis
      unfolding interp_def
      by (smt (verit, best) Collect_cong image_eq_imageI insert_iff less.IH mem_Collect_eq)
  qed

  show ?case
    unfolding production_unfold C_in_iff interp_insert_eq by argo
qed

lemma production_add_irrelevant_clauses_to_set0:
  assumes
    fin: "finite N" "finite N'" and
    D_in: "D \<in> N'" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    no_select: "\<And>C. select C = {#}"
  shows "production (N \<union> N') D = {}"
  using \<open>finite N'\<close> D_in irrelevant
proof (induction N' rule: finite_induct)
  case empty
  hence False
    by simp
  thus ?case ..
next
  case (insert x F)
  then show ?case
    using production_add_irrelevant_clause_to_set0
    by (metis UnCI fin(1) finite_Un finite_insert production_add_irrelevant_clause_to_set no_select)
qed

lemma production_add_irrelevant_clauses_to_set:
  assumes
    fin: "finite N" "finite N'" and
    C_in: "C \<in> N" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    no_select: "\<And>C. select C = {#}"
  shows "production (N \<union> N') C = production N C"
  using \<open>finite N'\<close> irrelevant
proof (induction N' rule: finite_induct)
  case empty
  show ?case
    by simp
next
  case (insert x F)
  then show ?case
    using production_add_irrelevant_clause_to_set
    by (metis C_in UnI1 Un_insert_right fin(1) finite_Un insertCI no_select)
qed

lemma interp_add_irrelevant_clauses_to_set:
  assumes
    fin: "finite N" "finite N'" and
    C_in: "C \<in> N" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subset># D \<and> set_mset D = set_mset E" and
    no_select: "\<And>C. select C = {#}"
  shows "interp (N \<union> N') C = interp N C"
proof -
  have "interp (N \<union> N') C = \<Union> (production (N \<union> N') ` {D \<in> N \<union> N'. D \<prec>\<^sub>c C})"
    unfolding interp_def ..
  also have "\<dots> = \<Union> (production (N \<union> N') ` {D \<in> N. D \<prec>\<^sub>c C} \<union>
    production (N \<union> N') ` {D \<in> N'. D \<prec>\<^sub>c C})"
    by auto
  also have "\<dots> = \<Union> (production (N \<union> N') ` {D \<in> N. D \<prec>\<^sub>c C})"
    using production_add_irrelevant_clauses_to_set0[OF fin _ irrelevant no_select] by simp
  also have "\<dots> = \<Union> (production N ` {D \<in> N. D \<prec>\<^sub>c C})"
    using production_add_irrelevant_clauses_to_set[OF fin _ _ no_select] irrelevant
    using subset_mset.less_le by fastforce
  also have "\<dots> = interp N C"
    unfolding interp_def ..
  finally show ?thesis .
qed

lemma interp_add_irrelevant_clauses_to_set':
  assumes
    fin: "finite N" "finite N'" and
    C_in: "C \<in> N" and
    irrelevant: "\<forall>D \<in> N'. \<exists>E \<in> N. E \<subseteq># D \<and> set_mset D = set_mset E" and
    no_select: "\<And>C. select C = {#}"
  shows "interp (N \<union> N') C = interp N C"
proof -
  define N'' where
    "N'' = N' - N"

  from fin(2) have "finite N''"
    unfolding N''_def by simp

  moreover from irrelevant have "\<forall>D \<in> N''. \<exists>E \<in> N. E \<subset># D \<and> set_mset E = set_mset D"
    unfolding N''_def
    by (metis Diff_iff subset_mset.le_less)

  moreover have "N \<union> N' = N \<union> N''"
    unfolding N''_def by simp

  ultimately show ?thesis
    using assms interp_add_irrelevant_clauses_to_set by metis
qed

lemma lesser_entailed_clause_stays_entailed':
  assumes "C \<preceq>\<^sub>c D" and D_lt: "D \<prec>\<^sub>c E" and C_entailed: "interp N D \<union> production N D \<TTurnstile> C"
  shows "interp N E \<TTurnstile> C"
proof -
  from C_entailed obtain L where "L \<in># C" and "interp N D \<union> production N D \<TTurnstile>l L"
    by (auto simp: true_cls_def)

  show ?thesis
  proof (cases L)
    case (Pos A)
    hence "A \<in> interp N D \<union> production N D"
      using \<open>interp N D \<union> production N D \<TTurnstile>l L\<close> by simp
    moreover from D_lt have "interp N D \<union> production N D \<subseteq> interp N E"
      using less_imp_Interp_subseteq_interp by blast
    ultimately have "A \<in> interp N E"
      by auto
    thus ?thesis
      using Pos \<open>L \<in># C\<close> by auto
  next
    case (Neg A)
    then show ?thesis
      using neg_lits_not_in_model_stay_out_of_model
      by (smt (verit, best) UN_E Un_iff \<open>L \<in># C\<close> \<open>interp N D \<union> production N D \<TTurnstile>l L\<close> assms(1)
          interp_def clause_order.antisym_conv neg_literal_notin_imp_true_cls
          not_interp_to_Interp_imp_le produces_imp_in_interp true_lit_simps(2))
  qed
qed

lemma lesser_entailed_clause_stays_entailed:
  assumes C_le: "C \<preceq>\<^sub>c D" and D_lt: "D \<prec>\<^sub>c E" and C_entailed: "interp N D \<union> production N D \<TTurnstile> C"
  shows "interp N E \<union> production N E \<TTurnstile> C"
proof -
  from C_entailed obtain L where "L \<in># C" and "interp N D \<union> production N D \<TTurnstile>l L"
    by (auto simp: true_cls_def)

  show ?thesis
  proof (cases L)
    case (Pos A)
    hence "A \<in> interp N D \<union> production N D"
      using \<open>interp N D \<union> production N D \<TTurnstile>l L\<close> by simp
    moreover from D_lt have "interp N D \<union> production N D \<subseteq> interp N E \<union> production N E"
      using less_imp_Interp_subseteq_interp by blast
    ultimately have "A \<in> interp N E \<union> production N E"
      by auto
    thus ?thesis
      using Pos \<open>L \<in># C\<close> by auto
  next
    case (Neg A)
    then show ?thesis
      using neg_lits_not_in_model_stay_out_of_model
      by (smt (verit, best) UN_E Un_iff \<open>L \<in># C\<close> \<open>interp N D \<union> production N D \<TTurnstile>l L\<close> assms(1)
          interp_def clause_order.antisym_conv neg_literal_notin_imp_true_cls
          not_interp_to_Interp_imp_le produces_imp_in_interp true_lit_simps(2))
  qed
qed

lemma entailed_clause_stays_entailed':
  assumes C_lt: "C \<prec>\<^sub>c D" and C_entailed: "interp N C \<union> production N C \<TTurnstile> C"
  shows "interp N D \<TTurnstile> C"
  using lesser_entailed_clause_stays_entailed'[OF clause_order.order_refl assms] .

lemma entailed_clause_stays_entailed:
  assumes C_lt: "C \<prec>\<^sub>c D" and C_entailed: "interp N C \<union> production N C \<TTurnstile> C"
  shows "interp N D \<union> production N D \<TTurnstile> C"
  using lesser_entailed_clause_stays_entailed[OF clause_order.order_refl assms] .

lemma multp_if_all_left_smaller: "M2 \<noteq> {#} \<Longrightarrow> \<forall>k\<in>#M1. \<exists>j\<in>#M2. R k j \<Longrightarrow> multp R M1 M2"
  using one_step_implies_multp
  by (metis add_0)

lemma
  fixes
    P1 :: "'f gterm" and
    C1 :: "'f gterm clause" and
    N :: "'f gterm clause set"
  defines
    "C1 \<equiv> {#Neg P1#}" and
    "N \<equiv> {C1}"
  assumes
    no_select: "\<And>C. select C = {#}"
  shows
    False
proof -
  have "interp N C1 = {}"
    unfolding interp_def N_def by simp
  have "production N C1 = {}"
    unfolding production_unfold \<open>interp N C1 = {}\<close> C1_def by simp
  hence "interp N C1 \<union> production N C1 \<TTurnstile> C1"
    unfolding \<open>interp N C1 = {}\<close> \<open>production N C1 = {}\<close>
    by (simp add: C1_def)
  oops

lemma
  fixes
    P1 P2 :: "'f gterm" and
    C1 :: "'f gterm clause" and
    N :: "'f gterm clause set"
  defines
    "C1 \<equiv> {#Pos P1, Neg P2#}" and
    "N \<equiv> {C1}"
  assumes
    term_order: "P1 \<prec>\<^sub>t P2" and
    no_select: "\<And>C. select C = {#}"
  shows False
proof -
  have lit_order: "Pos P1 \<prec>\<^sub>l Neg P1" "Neg P1 \<prec>\<^sub>l Pos P2" "Pos P2 \<prec>\<^sub>l Neg P2"
    using term_order by simp_all
  have "interp N C1 = {}"
    unfolding interp_def N_def by simp
  have "production N C1 = {}"
    unfolding production_unfold
    using C1_def \<open>interp N C1 = {}\<close> by simp
  hence "interp N C1 \<union> production N C1 \<TTurnstile> C1"
    unfolding \<open>interp N C1 = {}\<close> \<open>production N C1 = {}\<close>
    by (simp add: C1_def)
  oops

  


lemma
  fixes
    P1 P2 P3 P4 :: "'f gterm" and
    C1 C2 C3 C4 C5 :: "'f gterm clause" and
    N :: "'f gterm clause set"
  defines
    "C1 \<equiv> {#Neg P1, Neg P2#}" and
    "C2 \<equiv> {#Pos P2, Neg P3#}" and
    "C3 \<equiv> {#Pos P1, Pos P2, Pos P4#}" and
    "C4 \<equiv> {#Pos P2, Pos P3, Pos P4#}" and
    "C5 \<equiv> {#Pos P2, Neg P4#}" and
    "N \<equiv> {C1, C2, C3, C4, C5}"
  assumes
    term_order: "P1 \<prec>\<^sub>t P2" "P2 \<prec>\<^sub>t P3" "P3 \<prec>\<^sub>t P4" and
    no_select: "\<And>C. select C = {#}"
  shows
    "C1 \<prec>\<^sub>c C2" "C2 \<prec>\<^sub>c C3" "C3 \<prec>\<^sub>c C4" "C4 \<prec>\<^sub>c C5"
proof -
  have lit_order: "Pos P1 \<prec>\<^sub>l Neg P1" "Neg P1 \<prec>\<^sub>l Pos P2" "Pos P2 \<prec>\<^sub>l Neg P2" "Neg P2 \<prec>\<^sub>l Pos P3"
    "Pos P3 \<prec>\<^sub>l Neg P3" "Neg P3 \<prec>\<^sub>l Pos P4" "Pos P4 \<prec>\<^sub>l Neg P4"
    using term_order by simp_all

  show "C1 \<prec>\<^sub>c C2"
    unfolding C1_def C2_def
  proof (rule multp_if_all_left_smaller)
    show "{#Pos P2, Neg P3#} \<noteq> {#}"
      by simp
  next
    show "\<forall>k\<in>#{#Neg P1, Neg P2#}. \<exists>j\<in>#{#Pos P2, Neg P3#}. k \<prec>\<^sub>l j"
      using lit_order by simp
  qed

  moreover show "C2 \<prec>\<^sub>c C3"
    unfolding C2_def C3_def
  proof (rule multp_if_all_left_smaller)
    show "{#Pos P1, Pos P2, Pos P4#} \<noteq> {#}"
      by simp
  next
    show "\<forall>k\<in>#{#Pos P2, Neg P3#}. \<exists>j\<in>#{#Pos P1, Pos P2, Pos P4#}. k \<prec>\<^sub>l j"
      using lit_order by auto
  qed

  moreover show "C3 \<prec>\<^sub>c C4"
  proof -
    have "{#Pos P1, Pos P2#} \<prec>\<^sub>c {#Pos P2, Pos P3#}"
    proof (rule multp_if_all_left_smaller)
      show "{#Pos P2, Pos P3#} \<noteq> {#}"
        by simp
    next
      show "\<forall>k\<in>#{#Pos P1, Pos P2#}. \<exists>j\<in>#{#Pos P2, Pos P3#}. k \<prec>\<^sub>l j"
        using lit_order by simp
    qed
    thus ?thesis
      unfolding C3_def C4_def
      by (smt (verit, ccfv_SIG) add_mset_commute irreflp_on_less_lit multp_cancel_add_mset
          transp_less_lit)
  qed

  moreover show "C4 \<prec>\<^sub>c C5"
    unfolding C4_def C5_def
  proof (rule multp_if_all_left_smaller)
    show "{#Pos P2, Neg P4#} \<noteq> {#}"
      by simp
  next
    show "\<forall>k\<in>#{#Pos P2, Pos P3, Pos P4#}. \<exists>j\<in>#{#Pos P2, Neg P4#}. k \<prec>\<^sub>l j"
      using lit_order by auto
  qed

  note cls_order = calculation this

  have "interp N C1 = {}"
    unfolding interp_def N_def
    using cls_order
    by (smt (verit, best) Collect_empty_eq bot_fset.rep_eq ccSUP_empty finsertCI fset_simps(2)
        clause_order.dual_order.strict_implies_not_eq clause_order.is_minimal_in_fset_finsertI
        clause_order.is_minimal_in_fset_iff singletonD)
  hence "production N C1 = {}"
    unfolding production_unfold C1_def by simp
  hence "interp N C1 \<union> production N C1 \<TTurnstile> C1"
    unfolding \<open>interp N C1 = {}\<close> \<open>production N C1 = {}\<close>
    unfolding C1_def
    unfolding true_cls_def true_lit_def
    by (simp add: C1_def)

  have "{D \<in> N. D \<prec>\<^sub>c C2} = {C1}"
    unfolding N_def
    using cls_order by auto
  hence "interp N C2 = interp N C1 \<union> production N C1"
    unfolding \<open>interp N C1 = {}\<close>
    unfolding interp_def
    by simp
  hence "interp N C2 = {}"
    unfolding \<open>interp N C1 = {}\<close> \<open>production N C1 = {}\<close> by simp
  hence "production N C2 = {}"
    unfolding production_unfold
    by (simp add: C2_def)
  hence "interp N C2 \<union> production N C2 \<TTurnstile> C2"
    using \<open>interp N C2 = {}\<close>
    by (simp add: C2_def)

  have "{D \<in> N. D \<prec>\<^sub>c C3} = {C1, C2}"
    unfolding N_def
    using cls_order by auto
  hence "interp N C3 = interp N C2 \<union> production N C2"
    unfolding \<open>interp N C2 = {}\<close>
    unfolding interp_def
    by (simp add: \<open>production N C1 = {}\<close>)
  hence "interp N C3 = {}"
    unfolding \<open>interp N C2 = {}\<close> \<open>production N C2 = {}\<close> by simp
  have "production N C3 = {P4}"
  proof -
    have "C3 \<in> N"
      by (simp add: N_def)
    moreover have "\<exists>C3'. C3 = add_mset (Pos P4) C3'"
      by (auto simp: C3_def)
    moreover have "is_strictly_maximal_lit (Pos P4) C3"
      unfolding C3_def literal_order.is_greatest_in_mset_iff
      using lit_order by auto
    moreover have "\<not> interp N C3 \<TTurnstile> C3"
      unfolding \<open>interp N C3 = {}\<close>
      unfolding C3_def
      by simp
    ultimately have "P4 \<in> production N C3"
      unfolding production_unfold
      using no_select
      by simp
    thus ?thesis
      using production_eq_empty_or_singleton by fastforce
  qed
  hence "interp N C3 \<union> production N C3 \<TTurnstile> C3"
    using \<open>interp N C3 = {}\<close>
    by (simp add: C3_def)

  have "{D \<in> N. D \<prec>\<^sub>c C4} = {C1, C2, C3}"
    unfolding N_def
    using cls_order by auto
  hence "interp N C4 = interp N C3 \<union> production N C3"
    unfolding \<open>interp N C3 = interp N C2 \<union> production N C2\<close>
    unfolding \<open>interp N C2 = interp N C1 \<union> production N C1\<close>
    unfolding \<open>interp N C1 = {}\<close>
    unfolding interp_def
    by auto
  hence "interp N C4 = {P4}"
    using \<open>interp N C3 = {}\<close> \<open>production N C3 = {P4}\<close> by simp
  hence "interp N C4 \<TTurnstile> C4"
    using C4_def by simp
  hence "production N C4 = {}"
    unfolding production_unfold by simp
  hence "interp N C4 \<union> production N C4 \<TTurnstile> C4"
    using \<open>interp N C4 = {P4}\<close>
    by (simp add: C4_def)

  have "{D \<in> N. D \<prec>\<^sub>c C5} = {C1, C2, C3, C4}"
    unfolding N_def
    using cls_order by auto
  hence "interp N C5 = interp N C4 \<union> production N C4"
    unfolding \<open>interp N C4 = interp N C3 \<union> production N C3\<close>
    unfolding \<open>interp N C3 = interp N C2 \<union> production N C2\<close>
    unfolding \<open>interp N C2 = interp N C1 \<union> production N C1\<close>
    unfolding \<open>interp N C1 = {}\<close>
    unfolding interp_def
    by auto
  hence "interp N C5 = {P4}"
    using \<open>interp N C4 = {P4}\<close> \<open>production N C4 = {}\<close> by simp
  have "production N C5 = {}"
  proof -
    have "is_strictly_maximal_lit (Neg P4) C5"
      unfolding C5_def literal_order.is_greatest_in_mset_iff
      using lit_order by auto
    hence "\<And>A. \<not> is_strictly_maximal_lit (Pos A) C5"
      by (meson Uniq_D literal_order.Uniq_is_greatest_in_mset literal.distinct(1))
    thus ?thesis
      unfolding production_unfold by simp
  qed
  hence "\<not> interp N C5 \<union> production N C5 \<TTurnstile> C5"
    unfolding \<open>interp N C5 = {P4}\<close> \<open>production N C5 = {}\<close>
    unfolding C5_def
    using term_order
    by simp
qed 
  

interpretation G: statically_complete_calculus G_Bot G_Inf G_entails G.Red_I G.Red_F
proof unfold_locales
  fix B :: "'f gterm atom clause" and N :: "'f gterm atom clause set"
  assume "B \<in> G_Bot" and "G.saturated N"
  hence "B = {#}"
    by simp

  assume "G_entails N {B}"
  hence "{#} \<in> N"
    unfolding \<open>B = {#}\<close>
  proof (rule contrapos_pp)
    assume "{#} \<notin> N"

    define I :: "'f gterm set" where
      "I = (\<Union>D \<in> N. production N D)"

    show "\<not> G_entails N G_Bot"
      unfolding G_entails_def not_all not_imp
    proof (intro exI conjI)
      show "I \<TTurnstile>s N"
        unfolding I_def
        using model_construction(2)[OF \<open>G.saturated N\<close> \<open>{#} \<notin> N\<close>]
        by (simp add: true_clss_def)
    next
      show "\<not> I \<TTurnstile>s G_Bot"
        by simp
    qed
  qed
  thus "\<exists>B'\<in>G_Bot. B' \<in> N"
    by auto
qed

end

end