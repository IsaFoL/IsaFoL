theory Ground_Ordered_Resolution
  imports
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus

    Ground_Ctxt_Extra
    HOL_Extra
    Transitive_Closure_Extra
    Multiset_Extra
    Relation_Extra
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

lemma transp_less_lit[simp]: "transp (\<prec>\<^sub>l)"
  by (metis (no_types, lifting) less_lit_def transpD transpI transp_less_trm transp_multp)

lemma transp_less_cls[simp]: "transp (\<prec>\<^sub>c)"
  by (simp add: transp_multp)

lemma asymp_on_less_lit[simp]: "asymp_on A (\<prec>\<^sub>l)"
  by (metis asympD asymp_less_trm asymp_multp\<^sub>H\<^sub>O asymp_onI less_lit_def multp_eq_multp\<^sub>H\<^sub>O
      transp_less_trm)

lemma irreflp_on_less_lit[simp]: "irreflp_on A (\<prec>\<^sub>l)"
  by (simp only: asymp_on_less_lit irreflp_on_if_asymp_on)

lemma asymp_less_lit[simp]: "asymp (\<prec>\<^sub>l)"
  by (metis asympD asympI asymp_less_trm asymp_multp\<^sub>H\<^sub>O less_lit_def multp_eq_multp\<^sub>H\<^sub>O transp_less_trm)

lemma asymp_less_cls[simp]: "asymp (\<prec>\<^sub>c)"
  by (simp add: asymp_multp\<^sub>H\<^sub>O multp_eq_multp\<^sub>H\<^sub>O)

lemma wfP_less_lit[simp]: "wfP (\<prec>\<^sub>l)"
  unfolding less_lit_def
  using wfP_less_trm wfP_multp wfP_if_convertible_to_wfP by meson

lemma wfP_less_cls[simp]: "wfP (\<prec>\<^sub>c)"
  using wfP_less_lit wfP_multp by blast

lemma totalp_less_lit: "totalp (\<prec>\<^sub>l)"
proof (rule totalpI)
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

lemma totalp_on_less_lit[simp]: "totalp_on A (\<prec>\<^sub>l)"
  using totalp_less_lit totalp_on_subset by auto

lemma totalp_less_cls[simp]: "totalp (\<prec>\<^sub>c)"
proof (rule totalp_multp)
  show "totalp (\<prec>\<^sub>l)"
    by simp
next
  show "transp (\<prec>\<^sub>l)"
    by simp
qed

interpretation linorder_trm: linorder lesseq_trm less_trm
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

interpretation linorder_lit: linorder lesseq_lit less_lit
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

interpretation linorder_cls: linorder lesseq_cls less_cls
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



subsection \<open>Ground Rules\<close>

abbreviation is_maximal_lit where
  "is_maximal_lit \<equiv> is_maximal_wrt (\<prec>\<^sub>l)"

abbreviation is_strictly_maximal_lit where
  "is_strictly_maximal_lit \<equiv> is_maximal_wrt (\<preceq>\<^sub>l)"

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

lemma correctness_ground_resolution:
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

lemma correctness_ground_factoring:
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
    using correctness_ground_resolution
    using correctness_ground_factoring
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
  hence "\<forall>k\<in>#P\<^sub>2'. k \<prec>\<^sub>l Pos t"
    by (metis (no_types, opaque_lifting) add_mset_remove_trivial is_maximal_wrt_def
        lift_is_maximal_wrt_to_is_maximal_wrt_reflclp sup2I1 totalpD totalp_less_lit)
  moreover have "\<And>A. Pos A \<prec>\<^sub>l Neg A"
    apply (simp add: less_lit_def)
    by (metis add.right_neutral empty_not_add_mset mset_add one_step_implies_multp
        union_mset_add_mset_right)
  ultimately have "\<forall>k\<in>#P\<^sub>2'. k \<prec>\<^sub>l Neg t"
    by (metis transp_def transp_less_lit)
  hence "P\<^sub>2' \<prec>\<^sub>c {#Neg t#}"
    using one_step_implies_multp[of "{#Neg t#}" P\<^sub>2' "(\<prec>\<^sub>l)" "{#}", simplified] by argo
  hence "P\<^sub>2' + P\<^sub>1' \<prec>\<^sub>c add_mset (Neg t) P\<^sub>1'"
    by (simp only: multp_cancel[of "(\<prec>\<^sub>l)" P\<^sub>1' P\<^sub>2' "{#Neg t#}", simplified])
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
    by (simp add: wfP_def)
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed

declare production.simps[simp del]

end

lemma Uniq_striclty_maximal_lit_in_ground_cls:
  "\<exists>\<^sub>\<le>\<^sub>1L. is_strictly_maximal_lit L C"
proof (rule Uniq_is_maximal_wrt_reflclp)
  show "totalp_on (set_mset C) (\<prec>\<^sub>l)"
    by (auto intro: totalp_on_subset totalp_less_lit)
qed

lemma production_eq_empty_or_singleton:
  "production N C = {} \<or> (\<exists>A. production N C = {A})"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1A. \<exists>C'. C = add_mset (Pos A) C' \<and> is_strictly_maximal_lit (Pos A) C"
    apply (rule UniqI)
    apply (elim exE conjE)
    using Uniq_striclty_maximal_lit_in_ground_cls[THEN Uniq_D,
        of "Pos _" _ "Pos _", unfolded literal.inject]
    using totalp_less_trm
    by (metis union_single_eq_member)
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

definition interp where
  "interp N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. production N D)"

lemma production_unfold: "production N C = {A | A C'.
    C \<in> N \<and>
    C = add_mset (Pos A) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos A) C \<and>
    \<not> interp N C \<TTurnstile> C}"
  by (simp add: production.simps[of N C] interp_def)

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

lemma production_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> production N C \<subseteq> interp N D"
  unfolding interp_def
  using production_unfold by blast

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
  proof (rule multp_if_maximal_less)
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
      using \<open>is_strictly_maximal_lit (Pos A) D\<close>
      by (meson is_maximal_wrt_if_is_maximal_wrt_reflclp)
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
    proof (rule multp_if_maximal_less)
      show "Pos A \<in># C"
        by (simp add: C_def)
    next
      show "L \<in># D"
        using L_in by simp
    next
      show "is_maximal_lit (Pos A) C"
        using C_max_lit by simp
    next
      show "Pos A \<prec>\<^sub>l L"
        using that by simp
    qed simp_all
    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by (metis asympD reflclp_iff wfP_imp_asymp wfP_less_cls)
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
    unfolding is_maximal_wrt_def
    using totalp_less_lit[THEN totalpD]
    by (metis (no_types, opaque_lifting) add_mset_remove_trivial reflclp_iff)

  from D_prod obtain D' where
    "D \<in> N" and
    D_def: "D = add_mset (Pos A\<^sub>D) D'" and
    "is_strictly_maximal_lit (Pos A\<^sub>D) D"
    by (elim mem_productionE) simp
  hence "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos A\<^sub>D"
    unfolding is_maximal_wrt_def
    using totalp_less_lit[THEN totalpD]
    by (metis (no_types, opaque_lifting) add_mset_remove_trivial reflclp_iff)

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
    "is_strictly_maximal_lit (Pos A) C" and
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
      by simp

    thm lesseq_trm_if_pos[OF \<open>C' \<preceq>\<^sub>c C\<close> C_prod \<open>L \<in># C'\<close>]

    show "\<not> interp N D \<TTurnstile>l L"
    proof (cases L)
      case (Pos A\<^sub>L)
      moreover have "A\<^sub>L \<notin> interp N D"
      proof -
        from Pos have "A\<^sub>L \<notin> insert A (interp N C)"
          by (metis C_def L_in \<open>L \<in># C\<close> \<open>\<not> interp N C \<TTurnstile> C\<close> \<open>is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) C\<close>
              add_mset_remove_trivial insertE lift_is_maximal_wrt_to_is_maximal_wrt_reflclp
              pos_literal_in_imp_true_cls sup.right_idem)

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
proof (induction C arbitrary: D rule: wfP_induct_rule)
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
          show "is_maximal_wrt (\<prec>\<^sub>l)\<^sup>=\<^sup>= (Pos A) D"
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
        using ex_is_maximal_wrt_if_not_empty[OF
            transp_less_lit[THEN transp_on_subset, OF subset_UNIV]
            asymp_less_lit[THEN asymp_on_subset, OF subset_UNIV]
            \<open>C \<noteq> {#}\<close>]
        using select_subset select_negative_lits
        by (metis (no_types, opaque_lifting) literal.disc(1) literal.exhaust mset_subset_eqD
            multiset_nonemptyE)
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
          then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
            using Pos_A_in max_Pos_A lift_is_maximal_wrt_to_is_maximal_wrt_reflclp
            by (metis insert_DiffM)

          thm ground_factoringI

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