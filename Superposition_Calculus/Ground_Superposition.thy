theory Ground_Superposition
  imports
    (* Theories from the Isabelle distribution *)
    Main

    (* Theories from the AFP *)
    "Saturation_Framework.Calculus"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Abstract-Rewriting.Abstract_Rewriting"
    "Regular_Tree_Relations.Ground_Terms"
    "Regular_Tree_Relations.Ground_Ctxt"

    (* Theories from this formalization *)
    "Abstract_Rewriting_Extra"
    "Ground_Critical_Pairs"
    Min_Max_Least_Greatest_Multiset
    "Multiset_Extra"
    "Term_Rewrite_System"
    "Transitive_Closure_Extra"
    "Uprod_Extra"
    "HOL_Extra"
    "Ground_Ctxt_Extra"
    Relation_Extra
    Clausal_Calculus_Extra
    Ground_Select
    Ground_Ordering
begin

hide_type Inference_System.inference
hide_const
  Inference_System.Infer
  Inference_System.prems_of
  Inference_System.concl_of
  Inference_System.main_prem_of

(* TODO: Move these out*)
lemma uprod_mem_image_iff_prod_mem[simp]:
  assumes "sym I"
  shows "(Upair t t') \<in> (\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<longleftrightarrow> (t, t') \<in> I"
  using \<open>sym I\<close>[THEN symD] by auto

lemma true_lit_uprod_iff_true_lit_prod[simp]:
  assumes "sym I"
  shows
    "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l Pos (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Pos (t, t')"
    "(\<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2) ` I \<TTurnstile>l Neg (Upair t t') \<longleftrightarrow> I \<TTurnstile>l Neg (t, t')"
  unfolding true_lit_simps uprod_mem_image_iff_prod_mem[OF \<open>sym I\<close>]
  by simp_all


section \<open>Superposition Calculus\<close>

locale ground_superposition_calculus = ground_ordering less_trm + ground_select select
  for
    less_trm :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" (infix "\<prec>\<^sub>t" 50) and
    select :: "'f atom clause \<Rightarrow> 'f atom clause" +
  assumes
    ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

subsection \<open>Ground Rules\<close>

abbreviation is_maximal_lit :: "'f atom literal \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  "is_maximal_lit L M \<equiv> is_maximal_in_mset_wrt (\<prec>\<^sub>l) M L"

abbreviation is_strictly_maximal_lit :: "'f atom literal \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  "is_strictly_maximal_lit L M \<equiv> is_greatest_in_mset_wrt (\<prec>\<^sub>l) M L"

inductive ground_superposition ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool"
where
  ground_superpositionI: "
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>1 = \<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    (\<P> = Pos \<and> select P\<^sub>1 = {#} \<and> is_strictly_maximal_lit L\<^sub>1 P\<^sub>1) \<or>
    (\<P> = Neg \<and> (select P\<^sub>1 = {#} \<and> is_maximal_lit L\<^sub>1 P\<^sub>1 \<or> L\<^sub>1 \<in># select P\<^sub>1)) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    ground_superposition P\<^sub>1 P\<^sub>2 C"

inductive ground_eq_resolution ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  ground_eq_resolutionI: "
    P = add_mset L P' \<Longrightarrow>
    L = Neg (Upair t t) \<Longrightarrow>
    select P = {#} \<and> is_maximal_lit L P \<or> L \<in># select P \<Longrightarrow>
    ground_eq_resolution P P'"

inductive ground_eq_factoring ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool" where
  ground_eq_factoringI: "
    P = add_mset L\<^sub>1 (add_mset L\<^sub>2 P') \<Longrightarrow>
    L\<^sub>1 = t \<approx> t' \<Longrightarrow>
    L\<^sub>2 = t \<approx> t'' \<Longrightarrow>
    select P = {#} \<Longrightarrow>
    is_maximal_lit L\<^sub>1 P \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    C = add_mset (Neg (Upair t' t'')) (add_mset (t \<approx> t'') P') \<Longrightarrow>
    ground_eq_factoring P C"


subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive ground_pos_superposition ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool"
where
  ground_pos_superpositionI: "
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    L\<^sub>1 = s\<langle>t\<rangle>\<^sub>G \<approx> s' \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal_lit L\<^sub>1 P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (s\<langle>t'\<rangle>\<^sub>G \<approx> s') (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    ground_pos_superposition P\<^sub>1 P\<^sub>2 C"

lemma ground_superposition_if_ground_pos_superposition:
  assumes step: "ground_pos_superposition P\<^sub>1 P\<^sub>2 C"
  shows "ground_superposition P\<^sub>1 P\<^sub>2 C"
  using step
proof (cases P\<^sub>1 P\<^sub>2 C rule: ground_pos_superposition.cases)
  case (ground_pos_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s t s' t')
  thus ?thesis
    using ground_superpositionI
    by (metis insert_iff)
qed

inductive ground_neg_superposition ::
  "'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> 'f atom clause \<Rightarrow> bool"
where
  ground_neg_superpositionI: "
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    L\<^sub>1 = Neg (Upair s\<langle>t\<rangle>\<^sub>G s') \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal_lit L\<^sub>1 P\<^sub>1 \<or> L\<^sub>1 \<in># select P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal_lit L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (Neg (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    ground_neg_superposition P\<^sub>1 P\<^sub>2 C"

lemma ground_superposition_if_ground_neg_superposition:
  assumes "ground_neg_superposition P\<^sub>1 P\<^sub>2 C"
  shows "ground_superposition P\<^sub>1 P\<^sub>2 C"
  using assms
proof (cases P\<^sub>1 P\<^sub>2 C rule: ground_neg_superposition.cases)
  case (ground_neg_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s t s' t')
  then show ?thesis
    using ground_superpositionI
    by (metis insert_iff)
qed

lemma ground_superposition_iff_pos_or_neg:
  "ground_superposition P\<^sub>1 P\<^sub>2 C \<longleftrightarrow>
    ground_pos_superposition P\<^sub>1 P\<^sub>2 C \<or> ground_neg_superposition P\<^sub>1 P\<^sub>2 C"
proof (rule iffI)
  assume "ground_superposition P\<^sub>1 P\<^sub>2 C"
  thus "ground_pos_superposition P\<^sub>1 P\<^sub>2 C \<or> ground_neg_superposition P\<^sub>1 P\<^sub>2 C"
  proof (cases P\<^sub>1 P\<^sub>2 C rule: ground_superposition.cases)
    case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
    then show ?thesis
      using ground_pos_superpositionI[of P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2' s t s' t']
      using ground_neg_superpositionI[of P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2' s t s' t']
      by metis
  qed
next
  assume "ground_pos_superposition P\<^sub>1 P\<^sub>2 C \<or> ground_neg_superposition P\<^sub>1 P\<^sub>2 C"
  thus "ground_superposition P\<^sub>1 P\<^sub>2 C"
    using ground_superposition_if_ground_neg_superposition
      ground_superposition_if_ground_pos_superposition
    by metis
qed


subsection \<open>Ground Layer\<close>

(*
Considérer de changer l'ordre des prémisses des règles afin qu'elles soient cohérentes avec le
framework et l'état de l'art. 
*)

definition G_Inf :: "'f atom clause inference set" where
  "G_Inf =
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. ground_superposition P\<^sub>1 P\<^sub>2 C} \<union>
    {Infer [P] C | P C. ground_eq_resolution P C} \<union>
    {Infer [P] C | P C. ground_eq_factoring P C}"

abbreviation G_Bot :: "'f atom clause set" where
  "G_Bot \<equiv> {{#}}"

abbreviation upair where
  "upair \<equiv> \<lambda>(t\<^sub>1, t\<^sub>2). Upair t\<^sub>1 t\<^sub>2"

definition G_entails :: "'f atom clause set \<Rightarrow> 'f atom clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm rel). refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow>
    compatible_with_gctxt I \<longrightarrow> upair ` I \<TTurnstile>s N\<^sub>1 \<longrightarrow> upair ` I \<TTurnstile>s N\<^sub>2)"


subsection \<open>Redundancy Criterion\<close>

lemma ground_superposition_smaller_conclusion:
  assumes
    step: "ground_superposition P1 P2 C"
  shows "C \<prec>\<^sub>c P1"
  using step
proof (cases P1 P2 C rule: ground_superposition.cases)
  case (ground_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')

  have "P\<^sub>1' + add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) P\<^sub>2' \<prec>\<^sub>c P\<^sub>1' + {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}"
  proof (intro one_step_implies_multp ballI)
    fix K assume "K \<in># add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) P\<^sub>2'"

    moreover have "\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
    proof -
      have  "s\<langle>t'\<rangle>\<^sub>G \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
        using \<open>t' \<prec>\<^sub>t t\<close> less_trm_compatible_with_gctxt by simp
      hence "multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
        using transp_less_trm
        by (simp add: add_mset_commute multp_cancel_add_mset)

      have ?thesis if "\<P> = Pos"
        unfolding that less_lit_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}\<close> by simp

      moreover have ?thesis if "\<P> = Neg"
        unfolding that less_lit_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}\<close>
        using multp_double_doubleI by force

      ultimately show ?thesis
        using \<open>\<P> \<in> {Pos, Neg}\<close> by auto
    qed

    moreover have "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
    proof -
      have "is_strictly_maximal_lit L\<^sub>2 P2"
        using ground_superpositionI by argo
      hence "\<forall>K \<in># P\<^sub>2'. \<not> Pos (Upair t t') \<prec>\<^sub>l K \<and> Pos (Upair t t') \<noteq> K"
        unfolding linorder_lit.is_greatest_in_mset_iff
        unfolding \<open>P2 = add_mset L\<^sub>2 P\<^sub>2'\<close> \<open>L\<^sub>2 = t \<approx> t'\<close>
        by auto
      hence "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l Pos (Upair t t')"
        using totalp_less_lit[THEN totalpD] by metis

      have thesis_if_Neg: "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        if "\<P> = Neg"
      proof -
        have "t \<preceq>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using lesseq_trm_if_subtermeq .
        hence " multp (\<prec>\<^sub>t) {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s', s\<langle>t\<rangle>\<^sub>G, s'#}"
          unfolding reflclp_iff
        proof (elim disjE)
          assume "t \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          moreover hence "t' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
            by (meson \<open>t' \<prec>\<^sub>t t\<close> transpD transp_less_trm)
          ultimately show ?thesis
            by (auto intro: one_step_implies_multp[of _ _ _ "{#}", simplified])
        next
          assume "t = s\<langle>t\<rangle>\<^sub>G"
          thus ?thesis
            using \<open>t' \<prec>\<^sub>t t\<close>
            by (smt (verit, ccfv_SIG) add.commute add_mset_add_single add_mset_commute bex_empty
                one_step_implies_multp set_mset_add_mset_insert set_mset_empty singletonD
                union_single_eq_member)
        qed
        thus "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using \<open>\<P> = Neg\<close>
          by (simp add: less_lit_def)
      qed

      have thesis_if_Pos: "Pos (Upair t t') \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        if "\<P> = Pos" and "is_maximal_lit L\<^sub>1 P1"
      proof (cases "s")
        case GHole
        show ?thesis
        proof (cases "t' \<preceq>\<^sub>t s'")
          case True
          hence "(multp (\<prec>\<^sub>t))\<^sup>=\<^sup>= {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
            unfolding GHole
            using transp_less_trm
            by (simp add: multp_cancel_add_mset)
          thus ?thesis
            unfolding GHole \<open>\<P> = Pos\<close>
            by (auto simp: less_lit_def)
        next
          case False
          hence "s' \<prec>\<^sub>t t'"
            using totalp_less_trm
            by (metis reflclp_iff totalpD)
          hence "multp (\<prec>\<^sub>t) {#s\<langle>t\<rangle>\<^sub>G, s'#} {#t, t'#}"
            using transp_less_trm
            by (simp add: GHole multp_cancel_add_mset)
          hence "\<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<prec>\<^sub>l Pos (Upair t t')"
            using \<open>\<P> = Pos\<close>
            by (simp add: less_lit_def)
          moreover have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
            using that
            unfolding ground_superpositionI
            unfolding linorder_lit.is_maximal_in_mset_iff
            by auto
          ultimately have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l Pos (Upair t t')"
            using transp_less_lit
            by (metis (no_types, lifting) reflclp_iff transpD)
          hence "P1 \<prec>\<^sub>c P2"
            using \<open>\<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<prec>\<^sub>l Pos (Upair t t')\<close>
              one_step_implies_multp[of P2 P1 "(\<prec>\<^sub>l)" "{#}", simplified]
            unfolding ground_superpositionI
            by (metis \<open>\<forall>K\<in>#P\<^sub>1'. K \<preceq>\<^sub>l (\<P> (Upair s\<langle>t\<rangle>\<^sub>G s'))\<close> empty_not_add_mset insert_iff reflclp_iff
                set_mset_add_mset_insert transpD transp_less_lit)
          hence False
            using \<open>P2 \<prec>\<^sub>c P1\<close>
            by (meson asympD asymp_less_cls)
          thus ?thesis ..
        qed
      next
        case (GMore f ts1 ctxt ts2)
        hence "t \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using less_trm_if_subterm[of s t] by simp
        moreover hence "t' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using \<open>t' \<prec>\<^sub>t t\<close> transp_less_trm
          by (metis transpD)
        ultimately have "multp (\<prec>\<^sub>t) {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
          using one_step_implies_multp[of "{#s\<langle>t\<rangle>\<^sub>G, s'#}" "{#t, t'#}" "(\<prec>\<^sub>t)" "{#}"] by simp
        hence "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using \<open>\<P> = Pos\<close>
          by (simp add: less_lit_def)
        thus ?thesis
          by simp
      qed

      have "\<P> = Pos \<or> \<P> = Neg"
        using \<open>\<P> \<in> {Pos, Neg}\<close> by simp
      thus ?thesis
      proof (elim disjE; intro ballI)
        fix K assume "\<P> = Pos" "K \<in># P\<^sub>2'"
        have "K \<prec>\<^sub>l t \<approx> t'"
          using \<open>\<forall>K\<in>#P\<^sub>2'. K \<prec>\<^sub>l t \<approx> t'\<close> \<open>K \<in># P\<^sub>2'\<close> by metis
        also have "t \<approx> t' \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        proof (rule thesis_if_Pos[OF \<open>\<P> = Pos\<close>])
          have "is_strictly_maximal_lit L\<^sub>1 P1"
            using \<open>\<P> = Pos\<close> ground_superpositionI literal.simps(4)
            by (metis literal.simps(4))
          thus "is_maximal_lit L\<^sub>1 P1"
            using linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset by metis
        qed
        finally show "K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')" .
      next
        fix K assume "\<P> = Neg" "K \<in># P\<^sub>2'"
        have "K \<prec>\<^sub>l t \<approx> t'"
          using \<open>\<forall>K\<in>#P\<^sub>2'. K \<prec>\<^sub>l t \<approx> t'\<close> \<open>K \<in># P\<^sub>2'\<close> by metis
        also have "t \<approx> t' \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using thesis_if_Neg[OF \<open>\<P> = Neg\<close>] .
        finally show "K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')" .
      qed
    qed

    ultimately show "\<exists>j \<in># {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}. K \<prec>\<^sub>l j"
      by auto
  qed simp

  moreover have "C = add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2')"
    unfolding ground_superpositionI ..

  moreover have "P1 = P\<^sub>1' + {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}"
    unfolding ground_superpositionI by simp

  ultimately show ?thesis
    by simp
qed

lemma ground_eq_resolution_smaller_conclusion:
  assumes step: "ground_eq_resolution P C"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: ground_eq_resolution.cases)
  case (ground_eq_resolutionI L t)
  then show ?thesis
    using totalp_less_cls
    by (metis add.right_neutral add_mset_add_single empty_iff empty_not_add_mset
        one_step_implies_multp set_mset_empty)
qed

lemma ground_eq_factoring_smaller_conclusion:
  assumes step: "ground_eq_factoring P C"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: ground_eq_factoring.cases)
  case (ground_eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
  have "is_maximal_lit L\<^sub>1 P"
    using ground_eq_factoringI by simp
  hence "\<forall>K \<in># add_mset (Pos (Upair t t'')) P'. \<not> Pos (Upair t t') \<prec>\<^sub>l K"
    unfolding ground_eq_factoringI
    by (simp add: linorder_lit.is_maximal_in_mset_iff linorder_lit.neq_iff)
  hence "\<not> Pos (Upair t t') \<prec>\<^sub>l Pos (Upair t t'')"
    by simp
  hence "Pos (Upair t t'') \<preceq>\<^sub>l Pos (Upair t t')"
    using totalp_less_lit
    by (metis reflclp_iff totalpD)
  hence "t'' \<preceq>\<^sub>t t'"
    unfolding reflclp_iff
    using transp_less_trm
    by (auto simp: less_lit_def multp_cancel_add_mset)

  have "C = add_mset (Neg (Upair t' t'')) (add_mset (Pos (Upair t t'')) P')"
    using ground_eq_factoringI by fastforce

  moreover have "add_mset (Neg (Upair t' t'')) (add_mset (Pos (Upair t t'')) P') \<prec>\<^sub>c P"
    unfolding ground_eq_factoringI
  proof (intro one_step_implies_multp[of "{#_#}" "{#_#}", simplified])
    have "t'' \<prec>\<^sub>t t"
      using \<open>t' \<prec>\<^sub>t t\<close> \<open>t'' \<preceq>\<^sub>t t'\<close> by order
    hence "multp (\<prec>\<^sub>t) {#t', t'', t', t''#} {#t, t'#}"
      using one_step_implies_multp[of _ _ _ "{#}", simplified]
      by (metis \<open>t' \<prec>\<^sub>t t\<close> diff_empty id_remove_1_mset_iff_notin insert_iff
          set_mset_add_mset_insert)
    thus "Neg (Upair t' t'') \<prec>\<^sub>l Pos (Upair t t')"
      by (simp add: less_lit_def)
  qed

  ultimately show ?thesis
    by simp
qed

sublocale consequence_relation where
  Bot = G_Bot and
  entails = G_entails
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
    fix I :: "'f gterm rel"
    assume "refl I" and "trans I" and "sym I" and "compatible_with_gctxt I" and
      "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s N1"
    hence "\<forall>C \<in> N2. (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {C}"
      using ball_G_entails by (simp add: G_entails_def)
    then show "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s N2"
      by (simp add: true_clss_def)
  qed
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def by simp
qed

sublocale calculus_with_finitary_standard_redundancy where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails and
  less = "(\<prec>\<^sub>c)"
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
      infer: "ground_superposition P\<^sub>1 P\<^sub>2 C"
    for P\<^sub>2 P\<^sub>1 C
    unfolding \<iota>_def
    using infer
    using ground_superposition_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "ground_eq_resolution P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_eq_resolution_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "ground_eq_factoring P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_eq_factoring_smaller_conclusion
    by simp

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    unfolding G_Inf_def
    by fast
qed


subsection \<open>Refutational Completeness\<close>

context
  fixes N :: "'f atom clause set"
begin

function equation :: "'f atom clause \<Rightarrow> 'f gterm rel" where
  "equation C = {(s, t)| s t C'.
    C \<in> N \<and>
    C = add_mset (Pos (Upair s t)) C' \<and>
    select C = {#} \<and>
    is_strictly_maximal_lit (Pos (Upair s t)) C \<and>
    t \<prec>\<^sub>t s \<and>
    (let R\<^sub>C = (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. equation D) in
    \<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt R\<^sub>C)\<^sup>\<down> \<TTurnstile> C \<and>
    \<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (s, t) R\<^sub>C))\<^sup>\<down> \<TTurnstile> C' \<and>
    s \<in> NF (rewrite_inside_gctxt R\<^sub>C))}"
  by simp_all

termination equation
proof (relation "{(x, y). x \<prec>\<^sub>c y}")
  show "wf {(x, y). x \<prec>\<^sub>c y}"
    using wfP_less_cls
    by (simp add: wfP_def)
next
  show "\<And>C D. D \<in> {D \<in> N. D \<prec>\<^sub>c C} \<Longrightarrow> (D, C) \<in> {(x, y). x \<prec>\<^sub>c y}"
    by simp
qed

declare equation.simps[simp del]

end

lemma Uniq_striclty_maximal_lit_in_ground_cls:
  "\<exists>\<^sub>\<le>\<^sub>1L. is_strictly_maximal_lit L C"
  using linorder_lit.Uniq_is_greatest_in_mset .

lemma equation_eq_empty_or_singleton:
  "equation N C = {} \<or> (\<exists>s t. equation N C = {(s, t)})"
proof -
  have "\<exists>\<^sub>\<le>\<^sub>1 (x, y). \<exists>C'.
    C = add_mset (Pos (Upair x y)) C' \<and> is_strictly_maximal_lit (Pos (Upair x y)) C \<and> y \<prec>\<^sub>t x"
    by (rule Uniq_prodI)
      (metis Uniq_D Upair_inject linorder_lit.Uniq_is_greatest_in_mset linorder_trm.min.absorb3
        linorder_trm.min.absorb4 literal.inject(1))
  hence Uniq_equation: "\<exists>\<^sub>\<le>\<^sub>1 (x, y). \<exists>C'.
    C \<in> N \<and>
    C = add_mset (Pos (Upair x y)) C' \<and> select C = {#} \<and>
    is_strictly_maximal_lit (Pos (Upair x y)) C \<and> y \<prec>\<^sub>t x \<and>
    (let R\<^sub>C = \<Union> (equation N ` {D \<in> N. D \<prec>\<^sub>c C}) in
      \<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt R\<^sub>C)\<^sup>\<down> \<TTurnstile> C \<and>
      \<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (x, y) R\<^sub>C))\<^sup>\<down> \<TTurnstile> C' \<and>
      x \<in> NF (rewrite_inside_gctxt R\<^sub>C))"
    using Uniq_antimono'
    by (smt (verit) Uniq_def Uniq_prodI case_prod_conv)
  show ?thesis
    unfolding equation.simps[of N C]
    using Collect_eq_if_Uniq_prod[OF Uniq_equation]
    by (smt (verit, best) Collect_cong Collect_empty_eq Uniq_def Uniq_equation case_prod_conv
        insertCI mem_Collect_eq)
qed

definition rewrite_sys where
  "rewrite_sys N C \<equiv> (\<Union>D \<in> {D \<in> N. D \<prec>\<^sub>c C}. equation N D)"

lemma mem_equationE:
  assumes rule_in: "rule \<in> equation N C"
  obtains l r C' where
    "C \<in> N" and
    "rule = (l, r)" and
    "C = add_mset (Pos (Upair l r)) C'" and
    "select C = {#}" and
    "is_strictly_maximal_lit (Pos (Upair l r)) C" and
    "r \<prec>\<^sub>t l" and
    "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C" and
    "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'" and
    "l \<in> NF (rewrite_inside_gctxt (rewrite_sys N C))"
  using rule_in
  unfolding equation.simps[of N C] mem_Collect_eq Let_def rewrite_sys_def
  by (metis (no_types, lifting))

lemma rhs_lt_lhs_if_mem_rewrite_sys:
  assumes "(t1, t2) \<in> rewrite_sys N C"
  shows "t2 \<prec>\<^sub>t t1"
  using assms
  unfolding rewrite_sys_def
  by (smt (verit, best) UN_iff mem_equationE prod.inject)

lemma rhs_less_trm_lhs_if_mem_rewrite_inside_gctxt_rewrite_sys:
  assumes rule_in: "(t1, t2) \<in> rewrite_inside_gctxt (rewrite_sys N C)"
  shows "t2 \<prec>\<^sub>t t1"
proof -
  from rule_in obtain ctxt t1' t2' where
    "(t1, t2) = (ctxt\<langle>t1'\<rangle>\<^sub>G, ctxt\<langle>t2'\<rangle>\<^sub>G) \<and> (t1', t2') \<in> rewrite_sys N C"
    unfolding rewrite_inside_gctxt_def mem_Collect_eq
    by auto
  thus ?thesis
  using rhs_lt_lhs_if_mem_rewrite_sys[of t1' t2']
  by (metis Pair_inject less_trm_compatible_with_gctxt)
qed

lemma rhs_lesseq_trm_lhs_if_mem_rtrancl_rewrite_inside_gctxt_rewrite_sys:
  assumes rule_in: "(t1, t2) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*"
  shows "t2 \<preceq>\<^sub>t t1"
  using rule_in
proof (induction t2 rule: rtrancl_induct)
  case base
  show ?case
    by simp
next
  case (step t2 t3)
  from step.hyps have "t3 \<prec>\<^sub>t t2"
    using rhs_less_trm_lhs_if_mem_rewrite_inside_gctxt_rewrite_sys by metis
  with step.IH show ?case
    by order
qed

lemma singleton_eq_CollectD: "{x} = {y. P y} \<Longrightarrow> P x"
  by blast

lemma subset_Union_mem_CollectI: "P x \<Longrightarrow> f x \<subseteq> (\<Union>y \<in> {z. P z}. f y)"
  by blast

lemma rewrite_sys_subset_if_less_cls: "C \<prec>\<^sub>c D \<Longrightarrow> rewrite_sys N C \<subseteq> rewrite_sys N D"
  by (smt (verit, best) UN_iff mem_Collect_eq rewrite_sys_def subsetI transpD transp_less_cls)

lemma less_trm_iff_less_cls_if_lhs_equation:
  assumes E\<^sub>C: "equation N C = {(s, t)}" and E\<^sub>D: "equation N D = {(u, v)}"
  shows "u \<prec>\<^sub>t s \<longleftrightarrow> D \<prec>\<^sub>c C"
proof -
  from E\<^sub>C obtain C' where
    "C \<in> N" and
    C_def: "C = add_mset (Pos (Upair s t)) C'" and
    "is_strictly_maximal_lit (Pos (Upair s t)) C" and
    "t \<prec>\<^sub>t s" and
    s_irreducible: "s \<in> NF (rewrite_inside_gctxt (\<Union>C' \<in> {C' \<in> N. C' \<prec>\<^sub>c C}. equation N C'))"
    by (auto simp:  elim!: equation.elims dest: singleton_eq_CollectD)
  hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (Upair s t)"
    by (simp add: linorder_lit.is_greatest_in_mset_iff)

  from E\<^sub>D obtain D' where
    "D \<in> N" and
    D_def: "D = add_mset (Pos (Upair u v)) D'" and
    "is_strictly_maximal_lit (Pos (Upair u v)) D" and
    "v \<prec>\<^sub>t u"
    by (auto simp:  elim: equation.elims dest: singleton_eq_CollectD)
  hence "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (Upair u v)"
    by (simp add: linorder_lit.is_greatest_in_mset_iff)

  show ?thesis
  proof (rule iffI)
    assume "u \<prec>\<^sub>t s"
    moreover hence "v \<prec>\<^sub>t s"
      using \<open>v \<prec>\<^sub>t u\<close>
      by (meson transpD transp_less_trm)
    ultimately have "multp (\<prec>\<^sub>t) {#u, v#} {#s, t#}"
      using one_step_implies_multp[of "{#s, t#}" "{#u, v#}" _ "{#}"] by simp
    hence "Pos (Upair u v) \<prec>\<^sub>l Pos (Upair s t)"
      by (simp add: less_lit_def)
    moreover hence "\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (Upair s t)"
      using \<open>\<forall>L \<in># D'. L \<prec>\<^sub>l Pos (Upair u v)\<close>
      by (meson transp_less_lit transpD)
    ultimately show "D \<prec>\<^sub>c C"
      using one_step_implies_multp[of C D _ "{#}"]
      by (simp add: D_def C_def)
  next
    assume "D \<prec>\<^sub>c C"
    hence "equation N D \<subseteq> (\<Union> (equation N ` {C' \<in> N. C' \<prec>\<^sub>c C}))"
      using \<open>D \<in> N\<close>
      by (auto simp: )
    hence "(u, v) \<in> (\<Union> (equation N ` {C' \<in> N. C' \<prec>\<^sub>c C}))"
      unfolding E\<^sub>D by simp
    hence "(u, v) \<in> rewrite_inside_gctxt (\<Union> (equation N ` {C' \<in> N. C' \<prec>\<^sub>c C}))"
      by auto
    hence "s \<noteq> u"
      using s_irreducible
      by auto
    moreover have "\<not> (s \<prec>\<^sub>t u)"
    proof (rule notI)
      assume "s \<prec>\<^sub>t u"
      moreover hence "t \<prec>\<^sub>t u"
        using \<open>t \<prec>\<^sub>t s\<close>
        by (meson transpD transp_less_trm)
      ultimately have "multp (\<prec>\<^sub>t) {#s, t#} {#u, v#}"
        using one_step_implies_multp[of "{#u, v#}" "{#s, t#}" _ "{#}"] by simp
      hence "Pos (Upair s t) \<prec>\<^sub>l Pos (Upair u v)"
        by (simp add: less_lit_def)
      moreover hence "\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (Upair u v)"
        using \<open>\<forall>L \<in># C'. L \<prec>\<^sub>l Pos (Upair s t)\<close>
        by (meson transp_less_lit transpD)
      ultimately have "C \<prec>\<^sub>c D"
        using one_step_implies_multp[of D C _ "{#}"]
        by (simp add: D_def C_def)
      thus False
        using \<open>D \<prec>\<^sub>c C\<close> by order
    qed
    ultimately show "u \<prec>\<^sub>t s"
      by order
  qed
qed

lemma termination_rewrite_sys: "wf ((rewrite_sys N C)\<inverse>)"
proof (rule wf_if_convertible_to_wf)
  show "wf {(x, y). x \<prec>\<^sub>t y}"
    using wfP_less_trm
    by (simp add: wfP_def)
next
  fix t s
  assume "(t, s) \<in> (rewrite_sys N C)\<inverse>"
  hence "(s, t) \<in> rewrite_sys N C"
    by simp
  then obtain D where "D \<prec>\<^sub>c C" and "(s, t) \<in> equation N D"
    unfolding rewrite_sys_def by blast
  hence "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)
  thus "(t, s) \<in> {(x, y). x \<prec>\<^sub>t y}"
    by (simp add: ) 
qed

lemma termination_Union_rewrite_sys: "wf ((\<Union>D \<in> N. rewrite_sys N D)\<inverse>)"
proof (rule wf_if_convertible_to_wf)
  show "wf {(x, y). x \<prec>\<^sub>t y}"
    using wfP_less_trm
    by (simp add: wfP_def)
next
  fix t s
  assume "(t, s) \<in> (\<Union>D \<in> N. rewrite_sys N D)\<inverse>"
  hence "(s, t) \<in> (\<Union>D \<in> N. rewrite_sys N D)"
    by simp
  then obtain C where "C \<in> N" "(s, t) \<in> rewrite_sys N C"
    by auto
  then obtain D where "D \<prec>\<^sub>c C" and "(s, t) \<in> equation N D"
    unfolding rewrite_sys_def by blast
  hence "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)
  thus "(t, s) \<in> {(x, y). x \<prec>\<^sub>t y}"
    by simp 
qed

lemma no_crit_pairs:
  "{(t1, t2) \<in> ground_critical_pairs (\<Union> (equation N2 ` N)). t1 \<noteq> t2} = {}"
proof (rule ccontr)
  assume "{(t1, t2).
    (t1, t2) \<in> ground_critical_pairs (\<Union> (equation N2 ` N)) \<and> t1 \<noteq> t2} \<noteq> {}"
  then obtain ctxt l r1 r2 where
    "(ctxt\<langle>r2\<rangle>\<^sub>G, r1) \<in> ground_critical_pairs (\<Union> (equation N2 ` N))" and
    "ctxt\<langle>r2\<rangle>\<^sub>G \<noteq> r1" and
    rule1_in: "(ctxt\<langle>l\<rangle>\<^sub>G, r1) \<in> \<Union> (equation N2 ` N)" and
    rule2_in: "(l, r2) \<in> \<Union> (equation N2 ` N)"
    unfolding ground_critical_pairs_def mem_Collect_eq by blast

  from rule1_in rule2_in obtain C1 C2 where
    "C1 \<in> N" and rule1_in': "(ctxt\<langle>l\<rangle>\<^sub>G, r1) \<in> equation N2 C1" and
    "C2 \<in> N" and rule2_in': "(l, r2) \<in> equation N2 C2"
    by auto

  from rule1_in' obtain C1' where
    C1_def: "C1 = add_mset (Pos (Upair ctxt\<langle>l\<rangle>\<^sub>G r1)) C1'" and
    C1_max: "is_strictly_maximal_lit (Pos (Upair ctxt\<langle>l\<rangle>\<^sub>G r1)) C1" and
    "r1 \<prec>\<^sub>t ctxt\<langle>l\<rangle>\<^sub>G" and
    l1_irreducible: "ctxt\<langle>l\<rangle>\<^sub>G \<in> NF (rewrite_inside_gctxt (rewrite_sys N2 C1))"
    by (auto elim: mem_equationE)

  from rule2_in' obtain C2' where
    C2_def: "C2 = add_mset (Pos (Upair l r2)) C2'" and
    C2_max: "is_strictly_maximal_lit (Pos (Upair l r2)) C2" and
    "r2 \<prec>\<^sub>t l"
    by (auto elim: mem_equationE)

  have "equation N2 C1 = {(ctxt\<langle>l\<rangle>\<^sub>G, r1)}"
    using rule1_in' equation_eq_empty_or_singleton by fastforce

  have "equation N2 C2 = {(l, r2)}"
    using rule2_in' equation_eq_empty_or_singleton by fastforce

  show False
  proof (cases "ctxt = \<box>\<^sub>G")
    case True
    hence "\<not> (ctxt\<langle>l\<rangle>\<^sub>G \<prec>\<^sub>t l)" and "\<not> (l \<prec>\<^sub>t ctxt\<langle>l\<rangle>\<^sub>G)"
      by (simp_all add: irreflpD)
    hence "\<not> (C1 \<prec>\<^sub>c C2)" and "\<not> (C2 \<prec>\<^sub>c C1)"
      using \<open>equation N2 C1 = {(ctxt\<langle>l\<rangle>\<^sub>G, r1)}\<close> \<open>equation N2 C2 = {(l, r2)}\<close>
        less_trm_iff_less_cls_if_lhs_equation
      by simp_all
    hence "C1 = C2"
      by order
    hence "r1 = r2"
      using \<open>equation N2 C1 = {(ctxt\<langle>l\<rangle>\<^sub>G, r1)}\<close> \<open>equation N2 C2 = {(l, r2)}\<close> by simp
    moreover have "r1 \<noteq> r2"
      using \<open>ctxt\<langle>r2\<rangle>\<^sub>G \<noteq> r1\<close>
      unfolding \<open>ctxt = \<box>\<^sub>G\<close>
      by simp
    ultimately show ?thesis
      by contradiction
  next
    case False
    hence "l \<prec>\<^sub>t ctxt\<langle>l\<rangle>\<^sub>G"
      by (metis less_trm_if_subterm)
    hence "C2 \<prec>\<^sub>c C1"
      using \<open>equation N2 C1 = {(ctxt\<langle>l\<rangle>\<^sub>G, r1)}\<close> \<open>equation N2 C2 = {(l, r2)}\<close>
        less_trm_iff_less_cls_if_lhs_equation
      by simp
    hence "equation N2 C2 \<subseteq> rewrite_sys N2 C1"
      unfolding rewrite_sys_def
      using \<open>C2 \<in> N\<close>
      using mem_equationE by blast
    hence "(l, r2) \<in> rewrite_sys N2 C1"
      unfolding \<open>equation N2 C2 = {(l, r2)}\<close> by simp
    hence "(ctxt\<langle>l\<rangle>\<^sub>G, ctxt\<langle>r2\<rangle>\<^sub>G) \<in> rewrite_inside_gctxt (rewrite_sys N2 C1)"
      by auto
    thus False
      using l1_irreducible by auto
  qed
qed

lemma WCR_Union_rewrite_sys:
  "WCR (rewrite_inside_gctxt (\<Union>D \<in> N. equation N2 D))"
  unfolding ground_critical_pair_theorem
proof (intro subsetI ballI)
  fix tuple
  assume tuple_in: "tuple \<in> ground_critical_pairs (\<Union> (equation N2 ` N))"
  then obtain t1 t2 where tuple_def: "tuple = (t1, t2)"
    by fastforce

  moreover have "(t1, t2) \<in> (rewrite_inside_gctxt (\<Union> (equation N2 ` N)))\<^sup>\<down>" if "t1 = t2"
    using that by auto

  moreover have False if "t1 \<noteq> t2"
    using that tuple_def tuple_in no_crit_pairs by simp

  ultimately show "tuple \<in> (rewrite_inside_gctxt (\<Union> (equation N2 ` N)))\<^sup>\<down>"
    by (cases "t1 = t2") simp_all
qed

lemma
  assumes
    "D \<preceq>\<^sub>c C" and
    E\<^sub>C_eq: "equation N C = {(s, t)}" and
    L_in: "L \<in># D" and
    topmost_trms_of_L: "mset_uprod (atm_of L) = {#u, v#}"
  shows
    lesseq_trm_if_pos: "is_pos L \<Longrightarrow> u \<preceq>\<^sub>t s" and
    less_trm_if_neg: "is_neg L \<Longrightarrow> u \<prec>\<^sub>t s"
proof -
  from E\<^sub>C_eq have "(s, t) \<in> equation N C"
    by simp
  then obtain C' where
    C_def: "C = add_mset (Pos (Upair s t)) C'" and
    C_max_lit: "is_strictly_maximal_lit (Pos (Upair s t)) C" and
    "t \<prec>\<^sub>t s"
    by (auto elim: mem_equationE)

  hence less_lit_tot_on_C_D[simp]: "totalp_on (set_mset C \<union> set_mset D) (\<prec>\<^sub>l)"
    using totalp_less_lit totalp_on_subset by blast

  have "Pos (Upair s t) \<prec>\<^sub>l L" if "is_pos L" and "\<not> u \<preceq>\<^sub>t s"
  proof -
    from that(2) have "s \<prec>\<^sub>t u"
      using totalp_less_trm[THEN totalpD] by auto
    hence "multp (\<prec>\<^sub>t) {#s, t#} {#u, v#}"
      using \<open>t \<prec>\<^sub>t s\<close>
      by (smt (verit, del_insts) add.right_neutral empty_iff insert_iff one_step_implies_multp
          set_mset_add_mset_insert set_mset_empty transpD transp_less_trm union_mset_add_mset_right)
    with that(1) show "Pos (Upair s t) \<prec>\<^sub>l L"
      using topmost_trms_of_L
      by (cases L) (simp_all add: less_lit_def)
  qed

  moreover have "Pos (Upair s t) \<prec>\<^sub>l L" if "is_neg L" and "\<not> u \<prec>\<^sub>t s"
  proof -
    from that(2) have "s \<preceq>\<^sub>t u"
      using totalp_less_trm[THEN totalpD] by auto
    hence "multp (\<prec>\<^sub>t) {#s, t#} {#u, v, u, v#}"
      using \<open>t \<prec>\<^sub>t s\<close>
      by (smt (z3) add_mset_add_single add_mset_remove_trivial add_mset_remove_trivial_iff
          empty_not_add_mset insert_DiffM insert_noteq_member one_step_implies_multp reflclp_iff
          transp_def transp_less_trm union_mset_add_mset_left union_mset_add_mset_right)
    with that(1) show "Pos (Upair s t) \<prec>\<^sub>l L"
      using topmost_trms_of_L
      by (cases L) (simp_all add: less_lit_def)
  qed

  moreover have False if "Pos (Upair s t) \<prec>\<^sub>l L"
  proof -
    have "C \<prec>\<^sub>c D"
    proof (rule multp_if_maximal_of_lhs_is_less)
      show "Pos (Upair s t) \<in># C"
        by (simp add: C_def)
    next
      show "L \<in># D"
        using L_in by simp
    next
      show "is_maximal_lit (Pos (Upair s t)) C"
        using C_max_lit by auto
    next
      show "Pos (Upair s t) \<prec>\<^sub>l L"
        using that by simp
    qed simp_all
    with \<open>D \<preceq>\<^sub>c C\<close> show False
      by order
  qed

  ultimately show "is_pos L \<Longrightarrow> u \<preceq>\<^sub>t s" and "is_neg L \<Longrightarrow> u \<prec>\<^sub>t s"
    by argo+
qed

lemma less_trm_const_lhs_if_mem_rewrite_inside_gctxt:
  fixes t t1 t2 r
  assumes
    rule_in: "(t1, t2) \<in> rewrite_inside_gctxt r" and
    ball_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> r \<Longrightarrow> t \<prec>\<^sub>t t1"
  shows "t \<prec>\<^sub>t t1"
proof -
  from rule_in obtain ctxt t1' t2' where
    rule_in': "(t1', t2') \<in> r" and
    l_def: "t1 = ctxt\<langle>t1'\<rangle>\<^sub>G" and
    r_def: "t2 = ctxt\<langle>t2'\<rangle>\<^sub>G"
    unfolding rewrite_inside_gctxt_def by fast

  show ?thesis
    using ball_lt_lhs[OF rule_in'] lesseq_trm_if_subtermeq[of t1' ctxt] l_def by order
qed

lemma split_Union_equation:
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. equation N C) =
    rewrite_sys N D \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
proof -
  have "N = {C \<in> N. C \<prec>\<^sub>c D} \<union> {D} \<union> {C \<in> N. D \<prec>\<^sub>c C}"
  proof (rule partition_set_around_element)
    show "totalp_on N (\<prec>\<^sub>c)"
      using totalp_less_cls totalp_on_subset by blast
  next
    show "D \<in> N"
      using D_in by simp
  qed
  hence "(\<Union>C \<in> N. equation N C) =
      (\<Union>C \<in> {C \<in> N. C \<prec>\<^sub>c D}. equation N C) \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
    by auto
  thus "(\<Union>C \<in> N. equation N C) =
    rewrite_sys N D \<union> equation N D \<union> (\<Union>C \<in> {C \<in> N. D \<prec>\<^sub>c C}. equation N C)"
    by (simp add: rewrite_sys_def)
qed

lemma split_Union_equation':
  assumes D_in: "D \<in> N"
  shows "(\<Union>C \<in> N. equation N C) = rewrite_sys N D \<union> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C)"
  using split_Union_equation[OF D_in] D_in by auto

lemma split_rewrite_sys:
  assumes "C \<in> N" and D_in: "D \<in> N" and "D \<prec>\<^sub>c C"
  shows "rewrite_sys N C = rewrite_sys N D \<union> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C')"
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

  have "rewrite_sys N C = (\<Union>C' \<in> {D \<in> N. D \<prec>\<^sub>c C}. equation N C')"
    by (simp add: rewrite_sys_def)
  also have "\<dots> = (\<Union>C' \<in> {x \<in> N. x \<prec>\<^sub>c D}. equation N C') \<union> (\<Union>C' \<in> {x \<in> N. D \<preceq>\<^sub>c x \<and> x \<prec>\<^sub>c C}. equation N C')"
    unfolding Collect_N_lt_C by simp
  finally show "rewrite_sys N C = rewrite_sys N D \<union> \<Union> (equation N ` {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C})"
    unfolding rewrite_sys_def by simp
qed

lemma mem_join_union_iff_mem_join_lhs':
  assumes
    ball_R\<^sub>1_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>1 \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    ball_R\<^sub>2_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>2 \<Longrightarrow> s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
  shows "(s, t) \<in> (R\<^sub>1 \<union> R\<^sub>2)\<^sup>\<down> \<longleftrightarrow> (s, t) \<in> R\<^sub>1\<^sup>\<down>"
proof -
  have ball_R\<^sub>1_rhs_lt_lhs': "(t1, t2) \<in> R\<^sub>1\<^sup>* \<Longrightarrow> t2 \<preceq>\<^sub>t t1" for t1 t2
  proof (induction t2 rule: rtrancl_induct)
    case base
    show ?case
      by simp
  next
    case (step y z)
    thus ?case
      using ball_R\<^sub>1_rhs_lt_lhs
      by (metis reflclp_iff transpD transp_less_trm)
  qed

  show ?thesis
  proof (rule mem_join_union_iff_mem_join_lhs)
    fix u assume "(s, u) \<in> R\<^sub>1\<^sup>*"
    hence "u \<preceq>\<^sub>t s"
      using ball_R\<^sub>1_rhs_lt_lhs' by metis

    show "u \<notin> Domain R\<^sub>2"
    proof (rule notI)
      assume "u \<in> Domain R\<^sub>2"
      then obtain u' where "(u, u') \<in> R\<^sub>2"
        by auto
      hence "s \<prec>\<^sub>t u"
        using ball_R\<^sub>2_lt_lhs by simp
      with \<open>u \<preceq>\<^sub>t s\<close> show False
        by order
    qed
  next
    fix u assume "(t, u) \<in> R\<^sub>1\<^sup>*"
    hence "u \<preceq>\<^sub>t t"
      using ball_R\<^sub>1_rhs_lt_lhs' by simp

    show "u \<notin> Domain R\<^sub>2"
    proof (rule notI)
      assume "u \<in> Domain R\<^sub>2"
      then obtain u' where "(u, u') \<in> R\<^sub>2"
        by auto
      hence "t \<prec>\<^sub>t u"
        using ball_R\<^sub>2_lt_lhs by simp
      with \<open>u \<preceq>\<^sub>t t\<close> show False
        by order
    qed
  qed
qed

lemma mem_join_union_iff_mem_join_rhs':
  assumes
    ball_R\<^sub>1_rhs_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>2 \<Longrightarrow> t2 \<prec>\<^sub>t t1" and
    ball_R\<^sub>2_lt_lhs: "\<And>t1 t2. (t1, t2) \<in> R\<^sub>1 \<Longrightarrow> s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
  shows "(s, t) \<in> (R\<^sub>1 \<union> R\<^sub>2)\<^sup>\<down> \<longleftrightarrow> (s, t) \<in> R\<^sub>2\<^sup>\<down>"
  using assms mem_join_union_iff_mem_join_lhs'
  by (metis (no_types, opaque_lifting) sup_commute)

lemma mem_join_union_iff_mem_join_lhs'':
  assumes
    Range_R\<^sub>1_lt_Domain_R\<^sub>2: "\<And>t1 t2. t1 \<in> Range R\<^sub>1 \<Longrightarrow> t2 \<in> Domain R\<^sub>2 \<Longrightarrow> t1 \<prec>\<^sub>t t2" and
    s_lt_Domain_R\<^sub>2: "\<And>t2. t2 \<in> Domain R\<^sub>2 \<Longrightarrow> s \<prec>\<^sub>t t2" and
    t_lt_Domain_R\<^sub>2: "\<And>t2. t2 \<in> Domain R\<^sub>2 \<Longrightarrow> t \<prec>\<^sub>t t2"
  shows "(s, t) \<in> (R\<^sub>1 \<union> R\<^sub>2)\<^sup>\<down> \<longleftrightarrow> (s, t) \<in> R\<^sub>1\<^sup>\<down>"
proof (rule mem_join_union_iff_mem_join_lhs)
  fix u assume "(s, u) \<in> R\<^sub>1\<^sup>*"
  hence "u = s \<or> u \<in> Range R\<^sub>1"
    by (meson Range.intros rtrancl.cases)
  thus "u \<notin> Domain R\<^sub>2"
    using Range_R\<^sub>1_lt_Domain_R\<^sub>2 s_lt_Domain_R\<^sub>2
    by (metis irreflpD irreflp_on_less_trm)
next
  fix u assume "(t, u) \<in> R\<^sub>1\<^sup>*"
  hence "u = t \<or> u \<in> Range R\<^sub>1"
    by (meson Range.intros rtrancl.cases)
  thus "u \<notin> Domain R\<^sub>2"
    using Range_R\<^sub>1_lt_Domain_R\<^sub>2 t_lt_Domain_R\<^sub>2
    by (metis irreflpD irreflp_on_less_trm)
qed

lemma lift_entailment_to_Union:
  fixes N D
  defines "R\<^sub>D \<equiv> rewrite_sys N D"
  assumes
    D_in: "D \<in> N" and
    R\<^sub>D_entails_D: "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down> \<TTurnstile> D"
  shows
    "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> D" and
    "C \<in> N \<Longrightarrow> D \<prec>\<^sub>c C \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D"
proof -
  from R\<^sub>D_entails_D obtain L s t where
    L_in: "L \<in># D" and
    L_eq_disj_L_eq: "L = Pos (Upair s t) \<and> (s, t) \<in> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down> \<or>
     L = Neg (Upair s t) \<and> (s, t) \<notin> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>"
    unfolding true_cls_def true_lit_iff
    by (metis (no_types, opaque_lifting) image_iff prod.case surj_pair uprod_exhaust)

  from L_eq_disj_L_eq show
    "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> D" and
    "C \<in> N \<Longrightarrow> D \<prec>\<^sub>c C \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D"
    unfolding atomize_conj atomize_imp
  proof (elim disjE conjE)
    assume L_def: "L = Pos (Upair s t)" and "(s, t) \<in> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>"
    have "R\<^sub>D \<subseteq> (\<Union>D \<in> N. equation N D)" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> R\<^sub>D \<subseteq> rewrite_sys N C"
      unfolding R\<^sub>D_def rewrite_sys_def
      using D_in transp_less_cls[THEN transpD]
      by (auto intro: Collect_mono)
    hence "rewrite_inside_gctxt R\<^sub>D \<subseteq> rewrite_inside_gctxt (\<Union>D \<in> N. equation N D)" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> rewrite_inside_gctxt R\<^sub>D \<subseteq> rewrite_inside_gctxt (rewrite_sys N C)"
      by (auto intro!: rewrite_inside_gctxt_mono)
    hence "(s, t) \<in> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (s, t) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
      by (auto intro!: join_mono intro: set_mp[OF _ \<open>(s, t) \<in> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>\<close>])
    thus "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile> D \<and>
      (C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D)"
      unfolding true_cls_def true_lit_iff
      using L_in L_def by blast
  next
    have "(t1, t2) \<in> R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1" for t1 t2
      by (auto simp: R\<^sub>D_def rewrite_sys_def elim: mem_equationE)
    hence ball_R\<^sub>D_rhs_lt_lhs: "(t1, t2) \<in> rewrite_inside_gctxt R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1" for t1 t2
      by (smt (verit, ccfv_SIG) Pair_inject less_trm_compatible_with_gctxt mem_Collect_eq
          rewrite_inside_gctxt_def)

    assume L_def: "L = Neg (Upair s t)" and "(s, t) \<notin> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>"

    have "(s, t) \<in> (rewrite_inside_gctxt R\<^sub>D \<union> rewrite_inside_gctxt (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C))\<^sup>\<down> \<longleftrightarrow>
      (s, t) \<in> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>"
    proof (rule mem_join_union_iff_mem_join_lhs')
      show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1"
        using ball_R\<^sub>D_rhs_lt_lhs by simp
    next
      have ball_Rinf_minus_lt_lhs: "s \<prec>\<^sub>t fst rule \<and> t \<prec>\<^sub>t fst rule"
        if rule_in: "rule \<in> (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C)"
        for rule
      proof -
        from rule_in obtain C where
          "C \<in> N" and "D \<preceq>\<^sub>c C" and "rule \<in> equation N C"
          by auto

        have equation_C_eq: "equation N C = {(fst rule, snd rule)}"
          using \<open>rule \<in> equation N C\<close> equation_eq_empty_or_singleton by force

        show ?thesis
          using less_trm_if_neg[OF \<open>D \<preceq>\<^sub>c C\<close> equation_C_eq L_in]
          by (simp add: L_def)
      qed

      show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt (\<Union> (equation N ` {C \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C})) \<Longrightarrow>
        s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        using less_trm_const_lhs_if_mem_rewrite_inside_gctxt
        using ball_Rinf_minus_lt_lhs
        by force
    qed

    moreover have
      "(s, t) \<in> (rewrite_inside_gctxt R\<^sub>D \<union> rewrite_inside_gctxt (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C'))\<^sup>\<down> \<longleftrightarrow>
       (s, t) \<in> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>"
      if "C \<in> N" and "D \<prec>\<^sub>c C"
      for C
    proof (rule mem_join_union_iff_mem_join_lhs')
      show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt R\<^sub>D \<Longrightarrow> t2 \<prec>\<^sub>t t1"
        using ball_R\<^sub>D_rhs_lt_lhs by simp
    next
      have ball_lt_lhs: "s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        if "C \<in> N" and "D \<prec>\<^sub>c C" and
          rule_in: "(t1, t2) \<in> (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C')"
        for C t1 t2
      proof -
        from rule_in obtain C' where
          "C' \<in> N" and "D \<preceq>\<^sub>c C'" and "C' \<prec>\<^sub>c C" and "(t1, t2) \<in> equation N C'"
          by (auto simp: rewrite_sys_def)

        have equation_C'_eq: "equation N C' = {(t1, t2)}"
          using \<open>(t1, t2) \<in> equation N C'\<close> equation_eq_empty_or_singleton by force

        show ?thesis
          using less_trm_if_neg[OF \<open>D \<preceq>\<^sub>c C'\<close> equation_C'_eq L_in]
          by (simp add: L_def)
      qed

      show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt (\<Union> (equation N ` {C' \<in> N. (\<prec>\<^sub>c)\<^sup>=\<^sup>= D C' \<and> C' \<prec>\<^sub>c C})) \<Longrightarrow>
        s \<prec>\<^sub>t t1 \<and> t \<prec>\<^sub>t t1"
        using less_trm_const_lhs_if_mem_rewrite_inside_gctxt
        using ball_lt_lhs[OF that(1,2)]
        by (metis (no_types, lifting))
    qed

    ultimately have "(s, t) \<notin> (rewrite_inside_gctxt R\<^sub>D \<union> rewrite_inside_gctxt (\<Union>C \<in> {C \<in> N. D \<preceq>\<^sub>c C}. equation N C))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow>
        (s, t) \<notin> (rewrite_inside_gctxt R\<^sub>D \<union> rewrite_inside_gctxt (\<Union>C' \<in> {C' \<in> N. D \<preceq>\<^sub>c C' \<and> C' \<prec>\<^sub>c C}. equation N C'))\<^sup>\<down>"
      using \<open>(s, t) \<notin> (rewrite_inside_gctxt R\<^sub>D)\<^sup>\<down>\<close> by simp_all
    hence "(s, t) \<notin> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (s, t) \<notin> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
      using split_Union_equation'[OF D_in, folded R\<^sub>D_def]
      using split_rewrite_sys[OF _ D_in, folded R\<^sub>D_def]
      by (simp_all add: rewrite_inside_gctxt_union)
    hence "(Upair s t) \<notin> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>" and
      "\<forall>C. C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (Upair s t) \<notin> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
      unfolding atomize_conj
      by (meson sym_join true_lit_simps(2) true_lit_uprod_iff_true_lit_prod(2))
    thus "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile> D \<and>
    (C \<in> N \<longrightarrow> D \<prec>\<^sub>c C \<longrightarrow> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> D)"
      unfolding true_cls_def true_lit_iff
      using L_in L_def by metis
  qed
qed

lemma
  assumes productive: "equation N C = {(l, r)}"
  shows
    true_cls_if_productive_equation:
      "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C"
      "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C" and
    false_cls_if_productive_equation:
      "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (Upair l r)#}"
      "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> \<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (Upair l r)#}"
proof -
  from productive have "(l, r) \<in> equation N C"
    by simp
  then obtain C' where
    C_in: "C \<in> N" and
    C_def: "C = add_mset (Pos (Upair l r)) C'" and
    "select C = {#}" and
    "is_strictly_maximal_lit (Pos (Upair l r)) C" and
    "r \<prec>\<^sub>t l" and
    e: "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C" and
    f: "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'" and
    "l \<in> NF (rewrite_inside_gctxt (rewrite_sys N C))"
    by (rule mem_equationE) blast

  have "(l, r) \<in> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>"
    using C_in \<open>(l, r) \<in> equation N C\<close> mem_rewrite_inside_gctxt_if_mem_rewrite_rules by blast
  thus "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C"
    using C_def by blast

  have "rewrite_inside_gctxt (\<Union>D \<in> N. equation N D) =
        rewrite_inside_gctxt (rewrite_sys N C \<union> equation N C \<union> (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D))"
    using split_Union_equation[OF C_in] by simp
  also have "\<dots> =
    rewrite_inside_gctxt (rewrite_sys N C \<union> equation N C) \<union>
    rewrite_inside_gctxt (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
    by (simp add: rewrite_inside_gctxt_union)
  finally have rewrite_inside_gctxt_Union_equation_eq:
    "rewrite_inside_gctxt (\<Union>D \<in> N. equation N D) =
      rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)) \<union>
      rewrite_inside_gctxt (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
    unfolding productive by simp

  have mem_join_union_iff_mem_lhs:"(t1, t2) \<in> (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)) \<union>
    rewrite_inside_gctxt (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D))\<^sup>\<down> \<longleftrightarrow>
    (t1, t2) \<in> (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
    if "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
    for t1 t2
  proof (rule mem_join_union_iff_mem_join_lhs')
    fix s1 s2 assume "(s1, s2) \<in> rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C))"

    moreover have "s2 \<prec>\<^sub>t s1" if "(s1, s2) \<in> rewrite_inside_gctxt {(l, r)}"
    proof (rule rhs_lt_lhs_if_rule_in_rewrite_inside_gctxt[OF that])
      show "\<And>s1 s2. (s1, s2) \<in> {(l, r)} \<Longrightarrow> s2 \<prec>\<^sub>t s1"
        using \<open>r \<prec>\<^sub>t l\<close> by simp
    qed simp_all

    moreover have "s2 \<prec>\<^sub>t s1" if "(s1, s2) \<in> rewrite_inside_gctxt (rewrite_sys N C)"
    proof (rule rhs_lt_lhs_if_rule_in_rewrite_inside_gctxt[OF that])
      show "\<And>s1 s2. (s1, s2) \<in> rewrite_sys N C \<Longrightarrow> s2 \<prec>\<^sub>t s1"
        by (simp add: rhs_lt_lhs_if_mem_rewrite_sys)
    qed simp

    ultimately show "s2 \<prec>\<^sub>t s1"
      using rewrite_inside_gctxt_union[of "{(l, r)}", simplified] by blast
  next
    have ball_lt_lhs: "t1 \<prec>\<^sub>t s1 \<and> t2 \<prec>\<^sub>t s1"
      if rule_in: "(s1, s2) \<in> (\<Union>D \<in> {D \<in> N. C \<prec>\<^sub>c D}. equation N D)"
      for s1 s2
    proof -
      from rule_in obtain D where
        "D \<in> N" and "C \<prec>\<^sub>c D" and "(s1, s2) \<in> equation N D"
        by (auto simp: rewrite_sys_def)

      have E\<^sub>D_eq: "equation N D = {(s1, s2)}"
        using \<open>(s1, s2) \<in> equation N D\<close> equation_eq_empty_or_singleton by force

      have "l \<prec>\<^sub>t s1"
        using \<open>C \<prec>\<^sub>c D\<close>
        using less_trm_iff_less_cls_if_lhs_equation[OF E\<^sub>D_eq productive]
        by metis

      with \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close> show ?thesis
        by (metis reflclp_iff transpD transp_less_trm)
    qed
    thus "\<And>l r. (l, r) \<in> rewrite_inside_gctxt (\<Union> (equation N ` {D \<in> N. C \<prec>\<^sub>c D})) \<Longrightarrow> t1 \<prec>\<^sub>t l \<and> t2 \<prec>\<^sub>t l"
      using rewrite_inside_gctxt_Union_equation_eq
      using less_trm_const_lhs_if_mem_rewrite_inside_gctxt
      by presburger
  qed

  have neg_concl1: "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    obtain t1 t2 where
      atm_L_eq: "atm_of L = Upair t1 t2"
      by (metis uprod_exhaust)
    hence trms_of_L: "mset_uprod (atm_of L) = {#t1, t2#}"
      by simp
    hence "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
      unfolding atomize_conj
      using less_trm_if_neg[OF reflclp_refl productive \<open>L \<in># C\<close>]
      using lesseq_trm_if_pos[OF reflclp_refl productive \<open>L \<in># C\<close>]
      by (metis (no_types, opaque_lifting) add_mset_commute sup2CI)

    have "(t1, t2) \<notin> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>" if L_def: "L = Pos (Upair t1 t2)"
    proof -
      from that have "(t1, t2) \<notin> (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close> by blast
      thus ?thesis
        using rewrite_inside_gctxt_Union_equation_eq mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>]
        by simp
    qed

    moreover have "(t1, t2) \<in> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>"
      if L_def: "L = Neg (Upair t1 t2)"
    proof -
      from that have "(t1, t2) \<in> (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close>
        by (meson true_lit_uprod_iff_true_lit_prod(2) sym_join true_cls_def true_lit_simps(2))
      thus ?thesis
        using rewrite_inside_gctxt_Union_equation_eq
          mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>]
        by simp
    qed

    ultimately show "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union> (equation N ` N)))\<^sup>\<down> \<TTurnstile>l L"
      using atm_L_eq true_lit_uprod_iff_true_lit_prod[OF sym_join] true_lit_simps
      by (smt (verit, ccfv_SIG) literal.exhaust_sel)
  qed
  then show "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (Upair l r)#}"
    by (simp add: C_def)

  assume "D \<in> N" and "C \<prec>\<^sub>c D"
  then have "(l, r) \<in> (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down>"
    by (smt (verit, ccfv_threshold) C_in UN_iff \<open>(l, r) \<in> equation N C\<close> joinI_left mem_Collect_eq
        r_into_rtrancl mem_rewrite_inside_gctxt_if_mem_rewrite_rules rewrite_sys_def)
  thus "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C"
    using C_def by blast

  from \<open>D \<in> N\<close> have "rewrite_sys N D \<subseteq> (\<Union>D \<in> N. equation N D)"
    by (auto simp: rewrite_sys_def)
  hence "rewrite_inside_gctxt (rewrite_sys N D) \<subseteq> rewrite_inside_gctxt (\<Union>D \<in> N. equation N D)"
    using rewrite_inside_gctxt_mono by metis
  hence "(rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<subseteq> (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>"
    using join_mono by metis

  have "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C'"
    unfolding true_cls_def Set.bex_simps
  proof (intro ballI)
    fix L assume L_in: "L \<in># C'"
    hence "L \<in># C"
      by (simp add: C_def)

    obtain t1 t2 where
      atm_L_eq: "atm_of L = Upair t1 t2"
      by (metis uprod_exhaust)
    hence trms_of_L: "mset_uprod (atm_of L) = {#t1, t2#}"
      by simp
    hence "t1 \<preceq>\<^sub>t l" and "t2 \<preceq>\<^sub>t l"
      unfolding atomize_conj
      using less_trm_if_neg[OF reflclp_refl productive \<open>L \<in># C\<close>]
      using lesseq_trm_if_pos[OF reflclp_refl productive \<open>L \<in># C\<close>]
      by (metis (no_types, opaque_lifting) add_mset_commute sup2CI)

    have "(t1, t2) \<notin> (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down>" if L_def: "L = Pos (Upair t1 t2)"
    proof -
      from that have "(t1, t2) \<notin> (rewrite_inside_gctxt (insert (l, r) (rewrite_sys N C)))\<^sup>\<down>"
        using f \<open>L \<in># C'\<close> by blast
      thus ?thesis
        using rewrite_inside_gctxt_Union_equation_eq
        using mem_join_union_iff_mem_lhs[OF \<open>t1 \<preceq>\<^sub>t l\<close> \<open>t2 \<preceq>\<^sub>t l\<close>]
        using \<open>(rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<subseteq> (rewrite_inside_gctxt (\<Union> (equation N ` N)))\<^sup>\<down>\<close> by auto
    qed

    moreover have "(t1, t2) \<in> (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down>" if L_def: "L = Neg (Upair t1 t2)"
      using e
    proof (rule contrapos_np)
      assume "(t1, t2) \<notin> (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down>"
      hence "(t1, t2) \<notin> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
        using rewrite_sys_subset_if_less_cls[OF \<open>C \<prec>\<^sub>c D\<close>]
        by (meson join_mono rewrite_inside_gctxt_mono subsetD)
      thus "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C"
        using neg_literal_notin_imp_true_cls[of "Upair t1 t2" C "(\<lambda>(x, y). Upair x y) ` _\<^sup>\<down>"]
        unfolding uprod_mem_image_iff_prod_mem[OF sym_join]
        using L_def L_in C_def
        by simp
    qed

    ultimately show "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile>l L"
      using atm_L_eq true_lit_uprod_iff_true_lit_prod[OF sym_join] true_lit_simps
      by (smt (verit, ccfv_SIG) literal.exhaust_sel)
  qed
  thus "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N D))\<^sup>\<down> \<TTurnstile> C - {#Pos (Upair l r)#}"
    by (simp add: C_def)
qed

lemma from_neq_double_rtrancl_to_eqE:
  assumes "x \<noteq> y" and "(x, z) \<in> r\<^sup>*" and "(y, z) \<in> r\<^sup>*"
  obtains
    w where "(x, w) \<in> r" and "(w, z) \<in> r\<^sup>*" |
    w where "(y, w) \<in> r" and "(w, z) \<in> r\<^sup>*"
  using assms
  by (metis converse_rtranclE)


lemma ex_step_if_joinable:
  assumes "asymp R" "(x, z) \<in> r\<^sup>*" and "(y, z) \<in> r\<^sup>*"
  shows
    "R\<^sup>=\<^sup>= z y \<Longrightarrow> R y x \<Longrightarrow> \<exists>w. (x, w) \<in> r \<and> (w, z) \<in> r\<^sup>*"
    "R\<^sup>=\<^sup>= z x \<Longrightarrow> R x y \<Longrightarrow> \<exists>w. (y, w) \<in> r \<and> (w, z) \<in> r\<^sup>*"
  using assms
  by (metis asympD converse_rtranclE reflclp_iff)+

lemma trans_join_rewrite_inside_gctxt_rewrite_sys:
  "trans ((rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>)"
proof (rule trans_join)
  have "wf ((rewrite_inside_gctxt (rewrite_sys N C))\<inverse>)"
  proof (rule wf_converse_rewrite_inside_gctxt)
    fix s t
    assume "(s, t) \<in> rewrite_sys N C"
    then obtain D where "(s, t) \<in> equation N D"
      unfolding rewrite_sys_def by auto
    thus "t \<prec>\<^sub>t s"
      by (auto elim: mem_equationE)
  qed auto
  thus "SN (rewrite_inside_gctxt (rewrite_sys N C))"
    by (simp only: SN_iff_wf)
next
  show "WCR (rewrite_inside_gctxt (rewrite_sys N C))"
    unfolding rewrite_sys_def
    using WCR_Union_rewrite_sys
    by (metis (mono_tags, lifting))
qed

lemma true_cls_insert_and_not_true_clsE:
  assumes
    "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert r R))\<^sup>\<down> \<TTurnstile> C" and
    "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt R)\<^sup>\<down> \<TTurnstile> C"
  obtains t t' where
    "Pos (Upair t t') \<in># C" and
    "t \<prec>\<^sub>t t'" and
    "(t, t') \<in> (rewrite_inside_gctxt (insert r R))\<^sup>\<down>" and
    "(t, t') \<notin> (rewrite_inside_gctxt R)\<^sup>\<down>"
proof -
  assume hyp: "\<And>t t'. Pos (Upair t t') \<in># C \<Longrightarrow> t \<prec>\<^sub>t t' \<Longrightarrow> (t, t') \<in> (rewrite_inside_gctxt (insert r R))\<^sup>\<down> \<Longrightarrow>
    (t, t') \<notin> (rewrite_inside_gctxt R)\<^sup>\<down> \<Longrightarrow> thesis"

  from assms obtain L where
    "L \<in># C" and
    entails_L: "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert r R))\<^sup>\<down> \<TTurnstile>l L" and
    doesnt_entail_L: "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt R)\<^sup>\<down> \<TTurnstile>l L"
    by (meson true_cls_def)

  have "totalp_on (set_uprod (atm_of L)) (\<prec>\<^sub>t)"
    using totalp_less_trm totalp_on_subset by blast
  then obtain t t' where "atm_of L = Upair t t'" and "t \<preceq>\<^sub>t t'"
    using ex_ordered_Upair by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    hence L_def: "L = Pos (Upair t t')"
      using \<open>atm_of L = Upair t t'\<close> by simp

    moreover have "(t, t') \<in> (rewrite_inside_gctxt (insert r R))\<^sup>\<down>"
      using entails_L
      unfolding L_def
      unfolding true_lit_uprod_iff_true_lit_prod[OF sym_join]
      by (simp add: true_lit_def)

    moreover have "(t, t') \<notin> (rewrite_inside_gctxt R)\<^sup>\<down>"
      using doesnt_entail_L
      unfolding L_def
      unfolding true_lit_uprod_iff_true_lit_prod[OF sym_join]
      by (simp add: true_lit_def)

    ultimately show ?thesis
      using hyp \<open>L \<in># C\<close> \<open>t \<preceq>\<^sub>t t'\<close> by auto
  next
    case (Neg A)
    hence L_def: "L = Neg (Upair t t')"
      using \<open>atm_of L = Upair t t'\<close> by simp

    have "(t, t') \<notin> (rewrite_inside_gctxt (insert r R))\<^sup>\<down>"
      using entails_L
      unfolding L_def
      unfolding true_lit_uprod_iff_true_lit_prod[OF sym_join]
      by (simp add: true_lit_def)

    moreover have "(t, t') \<in> (rewrite_inside_gctxt R)\<^sup>\<down>"
      using doesnt_entail_L
      unfolding L_def
      unfolding true_lit_uprod_iff_true_lit_prod[OF sym_join]
      by (simp add: true_lit_def)

    moreover have "(rewrite_inside_gctxt R)\<^sup>\<down> \<subseteq> (rewrite_inside_gctxt (insert r R))\<^sup>\<down>"
      using join_mono rewrite_inside_gctxt_mono
      by (metis subset_insertI)

    ultimately have False
      by auto
    thus ?thesis ..
  qed
qed

lemma model_construction:
  fixes
    N :: "'f atom clause set" and
    C :: "'f atom clause"
  defines
    "entails \<equiv> \<lambda>E C. (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt E)\<^sup>\<down> \<TTurnstile> C"
  assumes "saturated N" and "{#} \<notin> N" and C_in: "C \<in> N"
  shows
    "equation N C = {} \<longleftrightarrow> entails (rewrite_sys N C) C"
    "entails (\<Union>D \<in> N. equation N D) C"
    "D \<in> N \<Longrightarrow> C \<prec>\<^sub>c D \<Longrightarrow> entails (rewrite_sys N D) C"
  unfolding atomize_conj atomize_imp
  using wfP_less_cls C_in
proof (induction C arbitrary: D rule: wfP_induct_rule)
  case (less C)
  note IH = less.IH

  from \<open>{#} \<notin> N\<close> \<open>C \<in> N\<close> have "C \<noteq> {#}"
    by metis

  define I where
    "I = (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"

  have "refl I"
    by (simp only: I_def refl_join)

  have "trans I"
    unfolding I_def
    using trans_join_rewrite_inside_gctxt_rewrite_sys .

  have "sym I"
    by (simp only: I_def sym_join)

  have "compatible_with_gctxt I"
    by (simp only: I_def compatible_with_gctxt_join compatible_with_gctxt_rewrite_inside_gctxt)

  note I_interp = \<open>refl I\<close> \<open>trans I\<close> \<open>sym I\<close> \<open>compatible_with_gctxt I\<close>

  have i: "entails (rewrite_sys N C) C \<longleftrightarrow> (equation N C = {})"
  proof (rule iffI)
    show "entails (rewrite_sys N C) C \<Longrightarrow> equation N C = {}"
      unfolding entails_def rewrite_sys_def
      by (metis (no_types) empty_iff equalityI mem_equationE rewrite_sys_def subsetI)
  next
    assume "equation N C = {}"
    show "entails (rewrite_sys N C) C"
    proof (cases "\<exists>A. Neg A \<in># C \<and> (Neg A \<in># select C \<or> select C = {#} \<and> is_maximal_lit (Neg A) C)")
      case ex_neg_lit_sel_or_max: True
      then obtain s s' where
        "Neg (Upair s s') \<in># C" and
        sel_or_max: "Neg (Upair s s') \<in># select C \<or> select C = {#} \<and> is_maximal_lit (Neg (Upair s s')) C"
        by (metis uprod_exhaust)
      then obtain C' where
        C_def: "C = add_mset (Neg (Upair s s')) C'"
        by (metis mset_add)

      show ?thesis
      proof (cases "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile>l Pos (Upair s s')")
        case True
        hence "(s, s') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
          by (meson sym_join true_lit_simps(1) true_lit_uprod_iff_true_lit_prod(1))

        have "s = s' \<or> s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s"
          using totalp_less_trm
          by (metis totalpD)
        thus ?thesis
        proof (rule disjE)
          assume "s = s'"
          define \<iota> :: "'f atom clause inference" where
            "\<iota> = Infer [C] C'"

          have "ground_eq_resolution C C'"
          proof (rule ground_eq_resolutionI)
            show "C = add_mset (Neg (Upair s s')) C'"
              by (simp only: C_def)
          next
            show "Neg (Upair s s') = Neg (Upair s s)"
              by (simp only: \<open>s = s'\<close>)
          next
            show "select C = {#} \<and> is_maximal_lit (Neg (Upair s s')) C \<or> Neg (Upair s s') \<in># select C"
              using sel_or_max by argo
          qed
          hence "\<iota> \<in> G_Inf"
            by (auto simp only: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C \<in> N\<close>
            by (simp add: \<iota>_def)

          ultimately have "\<iota> \<in> Inf_from N"
            by (auto simp: Inf_from_def)
          hence "\<iota> \<in> Red_I N"
            using \<open>saturated N\<close>
            by (auto simp: saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_C': "G_entails DD {C'}" and
            ball_DD_lt_C: "\<forall>D \<in> DD. D \<prec>\<^sub>c C"
            unfolding Red_I_def redundant_infer_def
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in>DD. entails (rewrite_sys N C) D"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
            using \<open>C \<in> N\<close> DD_subset ball_DD_lt_C
            by blast

          ultimately have "entails (rewrite_sys N C) C'"
            using I_interp DD_entails_C'
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)
          then show "entails (rewrite_sys N C) C"
            using C_def entails_def by simp
        next
          from \<open>(s, s') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>\<close> obtain u where
            s_u: "(s, u) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*" and
            s'_u: "(s', u) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*"
            by auto
          moreover hence "u \<preceq>\<^sub>t s" and "u \<preceq>\<^sub>t s'"
            using rhs_lesseq_trm_lhs_if_mem_rtrancl_rewrite_inside_gctxt_rewrite_sys by simp_all

          moreover assume "s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s"

          ultimately obtain u\<^sub>0 where
            "s' \<prec>\<^sub>t s \<Longrightarrow> (s, u\<^sub>0) : rewrite_inside_gctxt (rewrite_sys N C)"
            "s \<prec>\<^sub>t s' \<Longrightarrow> (s', u\<^sub>0) : rewrite_inside_gctxt (rewrite_sys N C)" and
            "(u\<^sub>0, u) : (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*"
            using ex_step_if_joinable[OF _ s_u s'_u]
            by (metis asympD asymp_less_trm)
          then obtain ctxt t t' where
            s_eq_if: "s' \<prec>\<^sub>t s \<Longrightarrow> s = ctxt\<langle>t\<rangle>\<^sub>G" and
            s'_eq_if: "s \<prec>\<^sub>t s' \<Longrightarrow> s' = ctxt\<langle>t\<rangle>\<^sub>G" and
            "u\<^sub>0 = ctxt\<langle>t'\<rangle>\<^sub>G" and
            "(t, t') \<in> rewrite_sys N C"
            by (smt (verit) Pair_inject \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> asympD asymp_less_trm mem_Collect_eq
                rewrite_inside_gctxt_def)
          then obtain D where
            "(t, t') \<in> equation N D" and "D \<in> N" and "D \<prec>\<^sub>c C"
            unfolding rewrite_sys_def by auto
          then obtain D' where
            D_def: "D = add_mset (Pos (Upair t t')) D'" and
            sel_D: "select D = {#}" and
            max_t_t': "is_strictly_maximal_lit (Pos (Upair t t')) D" and
            "t' \<prec>\<^sub>t t"
            by (elim mem_equationE) fast

          have superI: "ground_neg_superposition C D (add_mset (Neg (Upair s\<^sub>1\<langle>t'\<rangle>\<^sub>G s\<^sub>1')) (C' + D'))"
            if "{s, s'} = {s\<^sub>1\<langle>t\<rangle>\<^sub>G, s\<^sub>1'}" and "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>t\<rangle>\<^sub>G"
            for s\<^sub>1 s\<^sub>1'
          proof (rule ground_neg_superpositionI)
            show "C = add_mset (Neg (Upair s s')) C'"
              by (simp only: C_def)
          next
            show "D = add_mset (Pos (Upair t t')) D'"
              by (simp only: D_def)
          next
            show "D \<prec>\<^sub>c C"
              using \<open>D \<prec>\<^sub>c C\<close> .
          next
            show "select C = {#} \<and> is_maximal_lit (Neg (Upair s s')) C \<or> Neg (Upair s s') \<in># select C"
              using sel_or_max by argo
          next
            show "select D = {#}"
              using sel_D by blast
          next
            show "is_strictly_maximal_lit (Pos (Upair t t')) D"
              using max_t_t' .
          next
            show "t' \<prec>\<^sub>t t"
              using \<open>t' \<prec>\<^sub>t t\<close> .
          next
            from that(1) show "Neg (Upair s s') = Neg (Upair s\<^sub>1\<langle>t\<rangle>\<^sub>G s\<^sub>1')"
              by fastforce
          next
            from that(2) show "s\<^sub>1' \<prec>\<^sub>t s\<^sub>1\<langle>t\<rangle>\<^sub>G" .
          qed simp_all

          have "ground_neg_superposition C D (add_mset (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s')) (C' + D'))"
            if \<open>s' \<prec>\<^sub>t s\<close>
          proof (rule superI)
            from that show "{s, s'} = {ctxt\<langle>t\<rangle>\<^sub>G, s'}"
              using s_eq_if by simp
          next
            from that show "s' \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
              using s_eq_if by simp
          qed

          moreover have "ground_neg_superposition C  D (add_mset (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s)) (C' + D'))"
            if \<open>s \<prec>\<^sub>t s'\<close>
          proof (rule superI)
            from that show "{s, s'} = {ctxt\<langle>t\<rangle>\<^sub>G, s}"
              using s'_eq_if by auto
          next
            from that show "s \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
              using s'_eq_if by simp
          qed

          ultimately obtain CD where
            super: "ground_neg_superposition C  D CD" and
            CD_eq1: "s' \<prec>\<^sub>t s \<Longrightarrow> CD = add_mset (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s')) (C' + D')" and
            CD_eq2: "s \<prec>\<^sub>t s' \<Longrightarrow> CD = add_mset (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s)) (C' + D')"
            using \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> s'_eq_if s_eq_if by metis

          define \<iota> :: "'f atom clause inference" where
            "\<iota> = Infer [D, C] CD"

          have "\<iota> \<in> G_Inf"
            using ground_superposition_if_ground_neg_superposition[OF super]
            by (auto simp only: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C \<in> N\<close> \<open>D \<in> N\<close>
            by (auto simp add: \<iota>_def)

          ultimately have "\<iota> \<in> Inf_from N"
            by (auto simp: Inf_from_def)
          hence "\<iota> \<in> Red_I N"
            using \<open>saturated N\<close>
            by (auto simp: saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_CD: "G_entails (insert D DD) {CD}" and
            ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
            unfolding Red_I_def redundant_infer_def mem_Collect_eq
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in> insert D DD. entails (rewrite_sys N C) D"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
            using \<open>C \<in> N\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close> DD_subset ball_DD_lt_C
            by (metis in_mono insert_iff)

          ultimately have "entails (rewrite_sys N C) CD"
            using I_interp DD_entails_CD
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)

          moreover have "\<not> entails (rewrite_sys N C) D'"
            unfolding entails_def
            using false_cls_if_productive_equation(2)[OF _ \<open>C \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close>]
            by (metis D_def \<open>(t, t') \<in> equation N D\<close> add_mset_remove_trivial empty_iff
                 equation_eq_empty_or_singleton singletonD)

          moreover have "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile>l
            (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s'))"
            if "s' \<prec>\<^sub>t s"
            using \<open>(u\<^sub>0, u) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*\<close> \<open>u\<^sub>0 = ctxt\<langle>t'\<rangle>\<^sub>G\<close> s'_u by blast

          moreover have "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile>l
            (Neg (Upair ctxt\<langle>t'\<rangle>\<^sub>G s))"
            if "s \<prec>\<^sub>t s'"
            using \<open>(u\<^sub>0, u) \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>*\<close> \<open>u\<^sub>0 = ctxt\<langle>t'\<rangle>\<^sub>G\<close> s_u by blast

          ultimately show "entails (rewrite_sys N C) C"
            unfolding entails_def C_def
            using \<open>s \<prec>\<^sub>t s' \<or> s' \<prec>\<^sub>t s\<close> CD_eq1 CD_eq2 by fast
        qed
      next
        case False
        thus ?thesis
          using \<open>Neg (Upair s s') \<in># C\<close>
          by (auto simp add: entails_def true_cls_def)
      qed
    next
      case False
      hence "select C = {#}"
        using select_subset select_negative_lits
        by (metis (no_types, opaque_lifting) Neg_atm_of_iff mset_subset_eqD multiset_nonemptyE)
        
      from False obtain A where Pos_A_in: "Pos A \<in># C" and max_Pos_A: "is_maximal_lit (Pos A) C"
        using \<open>select C = {#}\<close> linorder_lit.ex_maximal_in_mset[OF \<open>C \<noteq> {#}\<close>]
        by (metis linorder_lit.is_maximal_in_mset_iff literal.exhaust)
      then obtain C' where C_def: "C = add_mset (Pos A) C'"
        by (meson mset_add)

      have "totalp_on (set_uprod A) (\<prec>\<^sub>t)"
        using totalp_less_trm totalp_on_subset by blast
      then obtain s s' where A_def: "A = Upair s s'" and "s' \<preceq>\<^sub>t s"
        using ex_ordered_Upair[of A "(\<prec>\<^sub>t)"] by fastforce

      show ?thesis
      proof (cases "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C' \<or> s = s'")
        case True
        then show ?thesis
          using \<open>equation N C = {}\<close>
          using A_def C_def entails_def by blast
      next
        case False

        from False have "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C'"
          by simp

        from False have "s' \<prec>\<^sub>t s"
          using \<open>s' \<preceq>\<^sub>t s\<close> asymp_less_trm[THEN asympD] by auto

        then show ?thesis
        proof (cases "is_strictly_maximal_lit (Pos A) C")
          case strictly_maximal: True
          show ?thesis
          proof (cases "s \<in> NF (rewrite_inside_gctxt (rewrite_sys N C))")
            case s_irreducible: True
            hence e_or_f_doesnt_hold: "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C \<or>
              (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'"
              using \<open>equation N C = {}\<close>[unfolded  equation.simps[of N C]]
              using \<open>C \<in> N\<close> C_def \<open>select C = {#}\<close> strictly_maximal \<open>s' \<prec>\<^sub>t s\<close>
              unfolding A_def rewrite_sys_def 
              by (smt (verit, best) Collect_empty_eq)
            show ?thesis
            proof (cases "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C")
              case e_doesnt_hold: True
              thus ?thesis
                by (simp add: entails_def)
            next
              case e_holds: False
              hence R_C_doesnt_entail_C': "\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C'"
                unfolding C_def by simp
              show ?thesis
              proof (cases "(\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down> \<TTurnstile> C'")
                case f_doesnt_hold: True
                then obtain C'' t t' where C'_def: "C' = add_mset (Pos (Upair t t')) C''" and
                  "t' \<prec>\<^sub>t t" and
                  "(t, t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down>" and
                  "(t, t') \<notin> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
                  using f_doesnt_hold R_C_doesnt_entail_C'
                  using true_cls_insert_and_not_true_clsE
                  by (metis insert_DiffM join_sym Upair_sym)

                have "Pos (Upair t t') \<prec>\<^sub>l Pos (Upair s s')"
                  using strictly_maximal
                  by (simp add: A_def C'_def C_def linorder_lit.is_greatest_in_mset_iff)

                have "\<not> (t \<prec>\<^sub>t s)"
                proof (rule notI)
                  assume "t \<prec>\<^sub>t s"

                  have "(t, t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down> \<longleftrightarrow>
                    (t, t') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
                    unfolding rewrite_inside_gctxt_union[of "{(s, s')}" "rewrite_sys N C", simplified]
                  proof (rule mem_join_union_iff_mem_join_rhs')
                    show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt {(s, s')} \<Longrightarrow> t \<prec>\<^sub>t t1 \<and> t' \<prec>\<^sub>t t1"
                      using \<open>t \<prec>\<^sub>t s\<close> \<open>t' \<prec>\<^sub>t t\<close>
                      by (smt (verit, ccfv_threshold) fst_conv singletonD
                          less_trm_const_lhs_if_mem_rewrite_inside_gctxt transpD transp_less_trm)
                  next
                    show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt (rewrite_sys N C) \<Longrightarrow> t2 \<prec>\<^sub>t t1"
                      using rhs_less_trm_lhs_if_mem_rewrite_inside_gctxt_rewrite_sys by force
                  qed
                  thus False
                    using \<open>(t, t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down>\<close>
                    using \<open>(t, t') \<notin> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>\<close>
                    by metis
                qed

                moreover have "\<not> (s \<prec>\<^sub>t t)"
                proof (rule notI)
                  assume "s \<prec>\<^sub>t t"
                  hence "multp (\<prec>\<^sub>t) {#s, s'#} {#t, t'#}"
                    using \<open>s' \<prec>\<^sub>t s\<close> \<open>t' \<prec>\<^sub>t t\<close>
                    using one_step_implies_multp[of _ _ _ "{#}", simplified]
                    by (metis (mono_tags, opaque_lifting) empty_not_add_mset insert_iff
                        set_mset_add_mset_insert set_mset_empty singletonD transpD transp_less_trm)
                  hence "Pos (Upair s s') \<prec>\<^sub>l Pos (Upair t t')"
                    by (simp add: less_lit_def)
                  thus False
                    using strictly_maximal \<open>t \<approx> t' \<prec>\<^sub>l s \<approx> s'\<close> by force
                qed

                ultimately have "t = s"
                  by order
                hence "t' \<prec>\<^sub>t s'"
                  using \<open>t' \<prec>\<^sub>t t\<close> \<open>s' \<prec>\<^sub>t s\<close>
                  using \<open>Pos (Upair t t') \<prec>\<^sub>l Pos (Upair s s')\<close>
                  unfolding less_lit_def
                  by (simp add: multp_cancel_add_mset transp_less_trm)

                obtain t'' where
                  "(t, t'') \<in> rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C))" and
                  "(t'', t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down>"
                  using \<open>(t, t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down>\<close>[THEN joinD]
                  using ex_step_if_joinable[OF asymp_less_trm _ _ _ \<open>t' \<prec>\<^sub>t t\<close>]
                  by (smt (verit, ccfv_threshold) \<open>t = s\<close> converse_rtranclE insertCI joinI_right
                      join_sym r_into_rtrancl mem_rewrite_inside_gctxt_if_mem_rewrite_rules rtrancl_join_join)

                have "t'' \<prec>\<^sub>t t"
                proof (rule predicate_holds_of_mem_rewrite_inside_gctxt[of _ _ _ "\<lambda>x y. y \<prec>\<^sub>t x"])
                  show "(t, t'') \<in> rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C))"
                    using \<open>(t, t'') \<in> rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C))\<close> .
                next
                  show "\<And>t1 t2. (t1, t2) \<in> insert (s, s') (rewrite_sys N C) \<Longrightarrow> t2 \<prec>\<^sub>t t1"
                    by (metis \<open>s' \<prec>\<^sub>t s\<close> insert_iff old.prod.inject rhs_lt_lhs_if_mem_rewrite_sys)
                next
                  show "\<And>t1 t2 ctxt \<sigma>. (t1, t2) \<in> insert (s, s') (rewrite_sys N C) \<Longrightarrow>
                    t2 \<prec>\<^sub>t t1 \<Longrightarrow> ctxt\<langle>t2\<rangle>\<^sub>G \<prec>\<^sub>t ctxt\<langle>t1\<rangle>\<^sub>G"
                    by (simp only: less_trm_compatible_with_gctxt)
                qed

                have "(t, t'') \<in> rewrite_inside_gctxt {(s, s')}"
                  using \<open>(t, t'') \<in> rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C))\<close>
                  using \<open>t = s\<close> s_irreducible mem_rewrite_step_union_NF
                  using rewrite_inside_gctxt_insert by blast
                hence "\<exists>ctxt. s = ctxt\<langle>s\<rangle>\<^sub>G \<and> t'' = ctxt\<langle>s'\<rangle>\<^sub>G"
                  by (simp add: \<open>t = s\<close> rewrite_inside_gctxt_def)
                hence "t'' = s'"
                  by (metis gctxt_ident_iff_eq_GHole)

                moreover have "(t'', t') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
                proof (rule mem_join_union_iff_mem_join_rhs'[THEN iffD1])
                  show "(t'', t') \<in> (rewrite_inside_gctxt {(s, s')} \<union>
                    rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
                    using \<open>(t'', t') \<in> (rewrite_inside_gctxt (insert (s, s') (rewrite_sys N C)))\<^sup>\<down>\<close>
                    using rewrite_inside_gctxt_union[of "{_}", simplified] by metis
                next
                  show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt (rewrite_sys N C) \<Longrightarrow> t2 \<prec>\<^sub>t t1"
                    using rhs_less_trm_lhs_if_mem_rewrite_inside_gctxt_rewrite_sys .
                next
                  show "\<And>t1 t2. (t1, t2) \<in> rewrite_inside_gctxt {(s, s')} \<Longrightarrow> t'' \<prec>\<^sub>t t1 \<and> t' \<prec>\<^sub>t t1"
                    using \<open>t' \<prec>\<^sub>t t\<close> \<open>t'' \<prec>\<^sub>t t\<close>
                    unfolding \<open>t = s\<close>
                    using less_trm_const_lhs_if_mem_rewrite_inside_gctxt by fastforce
                qed

                ultimately have "(s', t') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
                  by simp

                let ?concl = "add_mset (Neg (Upair s' t')) (add_mset (Pos (Upair t t')) C'')"

                define \<iota> :: "'f atom clause inference" where
                  "\<iota> = Infer [C] ?concl"

                have eq_fact: "ground_eq_factoring C ?concl"
                proof (rule ground_eq_factoringI)
                  show "C = add_mset (Pos (Upair s s')) (add_mset (Pos (Upair t t')) C'')"
                    by (simp add: C_def C'_def A_def)
                next
                  show "select C = {#}"
                    using \<open>select C = {#}\<close> .
                next
                  show "is_maximal_lit (Pos (Upair s s')) C"
                    by (metis A_def max_Pos_A)
                next
                  show "s' \<prec>\<^sub>t s"
                    using \<open>s' \<prec>\<^sub>t s\<close> .
                next
                  show "Pos (Upair t t') = Pos (Upair s t')"
                    unfolding \<open>t = s\<close> ..
                next
                  show "add_mset (Neg (Upair s' t')) (add_mset (Pos (Upair t t')) C'') =
                    add_mset (Neg (Upair s' t')) (add_mset (Pos (Upair s t')) C'')"
                    by (auto simp add: \<open>t = s\<close>)
                qed simp_all
                hence "\<iota> \<in> G_Inf"
                  by (auto simp: \<iota>_def G_Inf_def)

                moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
                  using \<open>C \<in> N\<close>
                  by (auto simp add: \<iota>_def)

                ultimately have "\<iota> \<in> Inf_from N"
                  by (auto simp: Inf_from_def)
                hence "\<iota> \<in> Red_I N"
                  using \<open>saturated N\<close>
                  by (auto simp: saturated_def)
                then obtain DD where
                  DD_subset: "DD \<subseteq> N" and
                  "finite DD" and
                  DD_entails_C': "G_entails DD {?concl}" and
                  ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
                  unfolding Red_I_def redundant_infer_def
                  by (auto simp: \<iota>_def)

                have "\<forall>D\<in>DD. entails (rewrite_sys N C) D"
                  using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
                  using \<open>C \<in> N\<close> DD_subset ball_DD_lt_C
                  by blast
                hence "entails (rewrite_sys N C) ?concl"
                  unfolding entails_def I_def[symmetric]
                  using DD_entails_C'[unfolded G_entails_def]
                  using I_interp
                  by (simp add: true_clss_def)
                thus "entails (rewrite_sys N C) C"
                  unfolding entails_def I_def[symmetric]
                  unfolding C_def C'_def A_def
                  using I_def \<open>(s', t') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>\<close> by blast
              next
                case f_holds: False
                hence False
                  using e_or_f_doesnt_hold e_holds by metis
                thus ?thesis ..
              qed
            qed
          next
            case s_reducible: False
            hence "\<exists>ss. (s, ss) \<in> rewrite_inside_gctxt (rewrite_sys N C)"
              unfolding NF_def by auto
            then obtain ctxt t t' D where
              "D \<in> N" and
              "D \<prec>\<^sub>c C" and
              "(t, t') \<in> equation N D" and
              "s = ctxt\<langle>t\<rangle>\<^sub>G"
              by (auto simp: rewrite_inside_gctxt_def rewrite_sys_def)

            obtain D' where
              D_def: "D = add_mset (Pos (Upair t t')) D'" and
              "select D = {#}" and
              max_t_t': "is_strictly_maximal_lit (t \<approx> t') D" and
              "t' \<prec>\<^sub>t t"
              using \<open>(t, t') \<in> equation N D\<close>
              by (elim mem_equationE) simp

            let ?concl = "add_mset (Pos (Upair ctxt\<langle>t'\<rangle>\<^sub>G s')) (C' + D')"

            define \<iota> :: "'f atom clause inference" where
              "\<iota> = Infer [D, C] ?concl"

            have super: "ground_pos_superposition C D ?concl"
            proof (rule ground_pos_superpositionI)
              show "C = add_mset (Pos (Upair s s')) C'"
                by (simp only: C_def A_def)
            next
              show "D = add_mset (Pos (Upair t t')) D'"
                by (simp only: D_def)
            next
              show "D \<prec>\<^sub>c C"
                using \<open>D \<prec>\<^sub>c C\<close> .
            next
              show "select D = {#}"
                using \<open>select D = {#}\<close> .
            next
              show "select C = {#}"
                using \<open>select C = {#}\<close> .
            next
              show "is_strictly_maximal_lit (s \<approx> s') C"
                using A_def strictly_maximal by simp
            next
              show "is_strictly_maximal_lit (t \<approx> t') D"
                using max_t_t' .
            next
              show "t' \<prec>\<^sub>t t"
                using \<open>t' \<prec>\<^sub>t t\<close> .
            next
              show "Pos (Upair s s') = Pos (Upair ctxt\<langle>t\<rangle>\<^sub>G s')"
                by (simp only: \<open>s = ctxt\<langle>t\<rangle>\<^sub>G\<close>)
            next
              show "s' \<prec>\<^sub>t ctxt\<langle>t\<rangle>\<^sub>G"
                using \<open>s' \<prec>\<^sub>t s\<close>
                unfolding \<open>s = ctxt\<langle>t\<rangle>\<^sub>G\<close> .
            qed simp_all
            hence "\<iota> \<in> G_Inf"
              using ground_superposition_if_ground_pos_superposition
              by (auto simp: \<iota>_def G_Inf_def)

            moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
              using \<open>C \<in> N\<close> \<open>D \<in> N\<close>
              by (auto simp add: \<iota>_def)

            ultimately have "\<iota> \<in> Inf_from N"
              by (auto simp only: Inf_from_def)
            hence "\<iota> \<in> Red_I N"
              using \<open>saturated N\<close>
              by (auto simp only: saturated_def)
            then obtain DD where
              DD_subset: "DD \<subseteq> N" and
              "finite DD" and
              DD_entails_concl: "G_entails (insert D DD) {?concl}" and
              ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
              unfolding Red_I_def redundant_infer_def mem_Collect_eq
              by (auto simp: \<iota>_def)

            moreover have "\<forall>D\<in> insert D DD. entails (rewrite_sys N C) D"
              using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
              using \<open>C \<in> N\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close> DD_subset ball_DD_lt_C
              by (metis in_mono insert_iff)

            ultimately have "entails (rewrite_sys N C) ?concl"
              using I_interp DD_entails_concl
              unfolding entails_def G_entails_def
              by (simp add: I_def true_clss_def)

            moreover have "\<not> entails (rewrite_sys N C) D'"
              unfolding entails_def
              using false_cls_if_productive_equation(2)[OF _ \<open>C \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close>]
              by (metis D_def \<open>(t, t') \<in> equation N D\<close> add_mset_remove_trivial empty_iff
                   equation_eq_empty_or_singleton singletonD)

            ultimately have "entails (rewrite_sys N C) {#Pos (Upair ctxt\<langle>t'\<rangle>\<^sub>G s')#}"
              unfolding entails_def
              using \<open>\<not> (\<lambda>(x, y). Upair x y) ` (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down> \<TTurnstile> C'\<close>
              by fastforce

            hence "(ctxt\<langle>t'\<rangle>\<^sub>G, s') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
              by (simp add: entails_def true_cls_def uprod_mem_image_iff_prod_mem[OF sym_join])

            moreover have "(ctxt\<langle>t\<rangle>\<^sub>G, ctxt\<langle>t'\<rangle>\<^sub>G) \<in> rewrite_inside_gctxt (rewrite_sys N C)"
              using \<open>(t, t') \<in> equation N D\<close> \<open>D \<in> N\<close> \<open>D \<prec>\<^sub>c C\<close> rewrite_sys_def
              by (auto simp: rewrite_inside_gctxt_def)

            ultimately have "(ctxt\<langle>t\<rangle>\<^sub>G, s') \<in> (rewrite_inside_gctxt (rewrite_sys N C))\<^sup>\<down>"
              using r_into_rtrancl rtrancl_join_join by metis

            hence "entails (rewrite_sys N C) {#Pos (Upair ctxt\<langle>t\<rangle>\<^sub>G s')#}"
              unfolding entails_def true_cls_def by auto

            thus ?thesis
              using A_def C_def \<open>s = ctxt\<langle>t\<rangle>\<^sub>G\<close> entails_def by fastforce
          qed
        next
          case False
          hence "2 \<le> count C (Pos A)"
            using max_Pos_A
            by (metis linorder_lit.count_ge_2_if_maximal_in_mset_and_not_greatest_in_mset)
          then obtain C' where C_def: "C = add_mset (Pos A) (add_mset (Pos A) C')"
            using two_le_countE by metis

          define \<iota> :: "'f atom clause inference" where
            "\<iota> = Infer [C] (add_mset (Pos (Upair s s')) (add_mset (Neg (Upair s' s')) C'))"

          let ?concl = "add_mset (Pos (Upair s s')) (add_mset (Neg (Upair s' s')) C')"

          have eq_fact: "ground_eq_factoring C ?concl"
          proof (rule ground_eq_factoringI)
            show "C = add_mset (Pos A) (add_mset (Pos A) C')"
              by (simp add: C_def)
          next
            show "Pos A = Pos (Upair s s')"
              by (simp add: A_def)
          next
            show "Pos A = Pos (Upair s s')"
              by (simp add: A_def)
          next
            show "select C = {#}"
              using \<open>select C = {#}\<close> .
          next
            show "is_maximal_lit (Pos A) C"
              using max_Pos_A .
          next
            show "s' \<prec>\<^sub>t s"
              using \<open>s' \<prec>\<^sub>t s\<close> .
          qed simp_all
          hence "\<iota> \<in> G_Inf"
            by (auto simp: \<iota>_def G_Inf_def)

          moreover have "\<And>t. t \<in> set (prems_of \<iota>) \<Longrightarrow> t \<in> N"
            using \<open>C \<in> N\<close>
            by (auto simp add: \<iota>_def)

          ultimately have "\<iota> \<in> Inf_from N"
            by (auto simp: Inf_from_def)
          hence "\<iota> \<in> Red_I N"
            using \<open>saturated N\<close>
            by (auto simp: saturated_def)
          then obtain DD where
            DD_subset: "DD \<subseteq> N" and
            "finite DD" and
            DD_entails_concl: "G_entails DD {?concl}" and
            ball_DD_lt_C: "\<forall>D\<in>DD. D \<prec>\<^sub>c C"
            unfolding Red_I_def redundant_infer_def mem_Collect_eq
            by (auto simp: \<iota>_def)

          moreover have "\<forall>D\<in>DD. entails (rewrite_sys N C) D"
            using IH[THEN conjunct2, THEN conjunct2, rule_format, of _ C]
            using \<open>C \<in> N\<close> DD_subset ball_DD_lt_C
            by blast

          ultimately have "entails (rewrite_sys N C) ?concl"
            using I_interp DD_entails_concl
            unfolding entails_def G_entails_def
            by (simp add: I_def true_clss_def)
          then show ?thesis
            by (simp add: entails_def A_def C_def joinI_right pair_imageI)
        qed
      qed
    qed
  qed

  moreover have iia: "entails (\<Union> (equation N ` N)) C"
    using equation_eq_empty_or_singleton[of N C, folded ]
  proof (elim disjE exE)
    assume "equation N C = {}"
    hence "entails (rewrite_sys N C) C"
      unfolding i by simp
    thus ?thesis
      using lift_entailment_to_Union(1)[OF \<open>C \<in> N\<close>]
      by (simp only: entails_def)
  next
    fix l r assume "equation N C = {(l, r)}"
    thus ?thesis
      using true_cls_if_productive_equation(1)[OF \<open>equation N C = {(l, r)}\<close>]
      by (simp only: entails_def)
  qed

  moreover have iib: "entails (rewrite_sys N D) C" if "D \<in> N" and "C \<prec>\<^sub>c D"
    using equation_eq_empty_or_singleton[of N C, folded ]
  proof (elim disjE exE)
    assume "equation N C = {}"
    hence "entails (rewrite_sys N C) C"
      unfolding i by simp
    thus ?thesis
      using lift_entailment_to_Union(2)[OF \<open>C \<in> N\<close> _ that]
      by (simp only: entails_def)
  next
    fix l r assume "equation N C = {(l, r)}"
    thus ?thesis
      using true_cls_if_productive_equation(2)[OF \<open>equation N C = {(l, r)}\<close> that]
      by (simp only: entails_def)
  qed

  ultimately show ?case
    by argo
qed

sublocale statically_complete_calculus where
  Bot = G_Bot and
  Inf = G_Inf and
  entails = G_entails and
  Red_I = Red_I and
  Red_F = Red_F
proof unfold_locales
  fix B :: "'f atom clause" and N :: "'f atom clause set"
  assume "B \<in> G_Bot" and "saturated N"
  hence "B = {#}"
    by simp

  assume "G_entails N {B}"
  hence "{#} \<in> N"
    unfolding \<open>B = {#}\<close>
  proof (rule contrapos_pp)
    assume "{#} \<notin> N"

    define I :: "'f gterm rel" where
      "I = (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<^sup>\<down>"

    show "\<not> G_entails N G_Bot"
      unfolding G_entails_def not_all not_imp
    proof (intro exI conjI)
      show "refl I"
        by (simp only: I_def refl_join)
    next
      show "trans I"
        unfolding I_def
      proof (rule trans_join)
        have "wf ((rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))\<inverse>)"
        proof (rule wf_converse_rewrite_inside_gctxt)
          fix s t
          assume "(s, t) \<in> (\<Union>D \<in> N. equation N D)"
          then obtain C where "C \<in> N" "(s, t) \<in> equation N C"
            by auto
          thus "t \<prec>\<^sub>t s"
            by (auto elim: mem_equationE)
        qed auto
        thus "SN (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))"
          unfolding SN_iff_wf .
      next
        show "WCR (rewrite_inside_gctxt (\<Union>D \<in> N. equation N D))"
          using WCR_Union_rewrite_sys .
      qed
    next
      show "sym I"
        by (simp only: I_def sym_join)
    next
      show "compatible_with_gctxt I"
        unfolding I_def
        by (simp only: I_def compatible_with_gctxt_join compatible_with_gctxt_rewrite_inside_gctxt)
    next
      show "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s N"
        unfolding I_def
        using model_construction(2)[OF \<open>saturated N\<close> \<open>{#} \<notin> N\<close>]
        by (simp add: true_clss_def)
    next
      show "\<not> (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s G_Bot"
        by simp
    qed
  qed
  thus "\<exists>B'\<in>G_Bot. B' \<in> N"
    by auto
qed


(* TODO: How to access this stuff differently? *)
abbreviation Red_I' where "Red_I' \<equiv> Red_I"
abbreviation Red_F' where "Red_F' \<equiv> Red_F"
lemmas Red_I_def = Red_I_def
lemmas Red_F_def = Red_F_def 

end

end