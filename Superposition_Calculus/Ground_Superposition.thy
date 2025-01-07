theory Ground_Superposition
  imports
    (* Theories from the Isabelle distribution *)
    Main

    (* Theories from the AFP *)
    "Saturation_Framework.Calculus"
    "Saturation_Framework_Extensions.Clausal_Calculus"
    "Abstract-Rewriting.Abstract_Rewriting"

    (* Theories from this formalization *)
    Abstract_Rewriting_Extra
    Ground_Critical_Pairs
    Multiset_Extra
    Term_Rewrite_System
    Transitive_Closure_Extra
    Uprod_Extra
    HOL_Extra
    Clausal_Calculus_Extra
    Selection_Function
    Ground_Order 
begin

no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)
no_notation subst_apply_term (infixl "\<cdot>" 67) (* TODO: Just have these once *)

section \<open>Superposition Calculus\<close>


locale ground_superposition_calculus = 
  ground_order_with_equality where less\<^sub>t = less\<^sub>t +
  selection_function select
for
  less\<^sub>t :: "'f gterm \<Rightarrow> 'f gterm \<Rightarrow> bool" and
  select :: "'f gatom clause \<Rightarrow> 'f gatom clause"  +
assumes
  ground_critical_pair_theorem: "\<And>(R :: 'f gterm rel). ground_critical_pair_theorem R"
begin

subsection \<open>Ground Rules\<close>

inductive superposition ::
  "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool"
where
  superpositionI: "
    E = add_mset L\<^sub>E E' \<Longrightarrow>
    D = add_mset L\<^sub>D D' \<Longrightarrow>
    D \<prec>\<^sub>c E \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>E = \<P> (Upair \<kappa>\<langle>t\<rangle>\<^sub>G u) \<Longrightarrow>
    L\<^sub>D = t \<approx> t' \<Longrightarrow>
    u \<prec>\<^sub>t \<kappa>\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    (\<P> = Pos \<and> select E = {#} \<and> is_strictly_maximal L\<^sub>E E) \<or>
    (\<P> = Neg \<and> (select E = {#} \<and> is_maximal L\<^sub>E E \<or> is_maximal L\<^sub>E (select E))) \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_strictly_maximal L\<^sub>D D \<Longrightarrow>
    C = add_mset (\<P> (Upair \<kappa>\<langle>t'\<rangle>\<^sub>G u)) (E' + D') \<Longrightarrow>
    superposition D E C"

inductive eq_resolution :: "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool" where
  eq_resolutionI: "
    D = add_mset L D' \<Longrightarrow>
    L = Neg (Upair t t) \<Longrightarrow>
    select D = {#} \<and> is_maximal L D \<or> is_maximal L (select D) \<Longrightarrow>
    C = D' \<Longrightarrow>
    eq_resolution D C"

inductive eq_factoring :: "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool" where
  eq_factoringI: "
    D = add_mset L\<^sub>1 (add_mset L\<^sub>2 D') \<Longrightarrow>
    L\<^sub>1 = t \<approx> t' \<Longrightarrow>
    L\<^sub>2 = t \<approx> t'' \<Longrightarrow>
    select D = {#} \<Longrightarrow>
    is_maximal L\<^sub>1 D \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    C = add_mset (Neg (Upair t' t'')) (add_mset (t \<approx> t'') D') \<Longrightarrow>
    eq_factoring D C"

abbreviation eq_resolution_inferences where
  "eq_resolution_inferences \<equiv> {Infer [D] C | D C. eq_resolution D C}"

abbreviation eq_factoring_inferences where
  "eq_factoring_inferences \<equiv> {Infer [D] C | D C.  eq_factoring D C}"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv> {Infer [D, E] C | D E C. superposition D E C}"

subsubsection \<open>Alternative Specification of the Superposition Rule\<close>

inductive superposition' :: 
  "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool"
where
  superposition'I: "
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    \<P> \<in> {Pos, Neg} \<Longrightarrow>
    L\<^sub>1 = \<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    (\<P> = Pos \<longrightarrow> select P\<^sub>1 = {#} \<and> is_strictly_maximal L\<^sub>1 P\<^sub>1) \<Longrightarrow>
    (\<P> = Neg \<longrightarrow> (select P\<^sub>1 = {#} \<and> is_maximal L\<^sub>1 P\<^sub>1 \<or> is_maximal L\<^sub>1 (select P\<^sub>1))) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    superposition' P\<^sub>2 P\<^sub>1 C"

lemma "superposition' = superposition"
proof (intro ext iffI)
  fix P1 P2 C
  assume "superposition' P2 P1 C"
  thus "superposition P2 P1 C"
  proof (cases P2 P1 C rule: superposition'.cases)
    case (superposition'I L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
    thus ?thesis
      using superpositionI 
      by force
  qed
next
  fix P1 P2 C
  assume "superposition P1 P2 C"
  thus "superposition' P1 P2 C"
  proof (cases P1 P2 C rule: superposition.cases)
    case (superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
    thus ?thesis
      using superposition'I
      by (metis literals_distinct)
  qed
qed

inductive pos_superposition ::
  "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool"
where
 pos_superpositionI: "
    P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    L\<^sub>1 = s\<langle>t\<rangle>\<^sub>G \<approx> s' \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    select P\<^sub>1 = {#} \<Longrightarrow>
    is_strictly_maximal L\<^sub>1 P\<^sub>1 \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (s\<langle>t'\<rangle>\<^sub>G \<approx> s') (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    pos_superposition P\<^sub>2 P\<^sub>1 C"

lemma superposition_if_pos_superposition:
  assumes step: "pos_superposition P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
  using step
proof (cases P\<^sub>2 P\<^sub>1 C rule: pos_superposition.cases)
  case (pos_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s t s' t')
  thus ?thesis
    using superpositionI
    by (metis insert_iff)
qed

inductive neg_superposition ::
  "'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> 'f gatom clause \<Rightarrow> bool"
where
 neg_superpositionI: 
   "P\<^sub>1 = add_mset L\<^sub>1 P\<^sub>1' \<Longrightarrow>
    P\<^sub>2 = add_mset L\<^sub>2 P\<^sub>2' \<Longrightarrow>
    P\<^sub>2 \<prec>\<^sub>c P\<^sub>1 \<Longrightarrow>
    L\<^sub>1 = Neg (Upair s\<langle>t\<rangle>\<^sub>G s') \<Longrightarrow>
    L\<^sub>2 = t \<approx> t' \<Longrightarrow>
    s' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G \<Longrightarrow>
    t' \<prec>\<^sub>t t \<Longrightarrow>
    select P\<^sub>1 = {#} \<and> is_maximal L\<^sub>1 P\<^sub>1 \<or> is_maximal L\<^sub>1 (select P\<^sub>1) \<Longrightarrow>
    select P\<^sub>2 = {#} \<Longrightarrow>
    is_strictly_maximal L\<^sub>2 P\<^sub>2 \<Longrightarrow>
    C = add_mset (Neg (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2') \<Longrightarrow>
    neg_superposition P\<^sub>2 P\<^sub>1 C"

lemma superposition_if_neg_superposition:
  assumes "neg_superposition P\<^sub>2 P\<^sub>1 C"
  shows "superposition P\<^sub>2 P\<^sub>1 C"
  using assms
proof (cases P\<^sub>2 P\<^sub>1 C rule: neg_superposition.cases)
  case (neg_superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' s t s' t')
  then show ?thesis
    using superpositionI
    by (metis insert_iff)
qed

lemma superposition_iff_pos_or_neg:
  "superposition P\<^sub>2 P\<^sub>1 C \<longleftrightarrow>
    pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
proof (rule iffI)
  assume "superposition P\<^sub>2 P\<^sub>1 C"
  thus "pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  proof (cases P\<^sub>2 P\<^sub>1 C rule: superposition.cases)
    case (superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')
    then show ?thesis
      using pos_superpositionI[of P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2' s t s' t']
      using neg_superpositionI[of P\<^sub>1 L\<^sub>1 P\<^sub>1' P\<^sub>2 L\<^sub>2 P\<^sub>2' s t s' t']
      by metis
  qed
next
  assume "pos_superposition P\<^sub>2 P\<^sub>1 C \<or> neg_superposition P\<^sub>2 P\<^sub>1 C"
  thus "superposition P\<^sub>2 P\<^sub>1 C"
    using 
      superposition_if_neg_superposition
      superposition_if_pos_superposition
    by metis
qed


subsection \<open>Ground Layer\<close>

definition G_Inf :: "'f gatom clause inference set" where
  "G_Inf =
    {Infer [P\<^sub>2, P\<^sub>1] C | P\<^sub>2 P\<^sub>1 C. superposition P\<^sub>2 P\<^sub>1 C} \<union>
    {Infer [P] C | P C. eq_resolution P C} \<union>
    {Infer [P] C | P C. eq_factoring P C}"

abbreviation G_Bot :: "'f gatom clause set" where
  "G_Bot \<equiv> {{#}}"

definition G_entails :: "'f gatom clause set \<Rightarrow> 'f gatom clause set \<Rightarrow> bool" where
  "G_entails N\<^sub>1 N\<^sub>2 \<longleftrightarrow> (\<forall>(I :: 'f gterm rel). refl I \<longrightarrow> trans I \<longrightarrow> sym I \<longrightarrow>
    compatible_with_gctxt I \<longrightarrow> upair ` I \<TTurnstile>s N\<^sub>1 \<longrightarrow> upair ` I \<TTurnstile>s N\<^sub>2)"

lemma superposition_smaller_conclusion:
  assumes
    step: "superposition P1 P2 C"
  shows "C \<prec>\<^sub>c P2"
  using step
proof (cases P1 P2 C rule: superposition.cases)
  case (superpositionI L\<^sub>1 P\<^sub>1' L\<^sub>2 P\<^sub>2' \<P> s t s' t')

  have "P\<^sub>1' + add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) P\<^sub>2' \<prec>\<^sub>c P\<^sub>1' + {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}"
    unfolding less\<^sub>c_def
  proof (intro one_step_implies_multp ballI)
    fix K assume "K \<in># add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) P\<^sub>2'"

    moreover have "\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
    proof -
      have  "s\<langle>t'\<rangle>\<^sub>G \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
        using \<open>t' \<prec>\<^sub>t t\<close> 
        by simp

      hence "multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
        by (simp add: add_mset_commute multp_cancel_add_mset)

      have ?thesis if "\<P> = Pos"
        unfolding that less\<^sub>l_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}\<close> 
        by simp

      moreover have ?thesis if "\<P> = Neg"
        unfolding that less\<^sub>l_def
        using \<open>multp (\<prec>\<^sub>t) {#s\<langle>t'\<rangle>\<^sub>G, s'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}\<close> multp_double_doubleI
        by force

      ultimately show ?thesis
        using \<open>\<P> \<in> {Pos, Neg}\<close> 
        by auto
    qed

    moreover have "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
    proof -
      have "is_strictly_maximal L\<^sub>2 P1"
        using superpositionI
        by argo

      hence "\<forall>K \<in># P\<^sub>2'. \<not> Pos (Upair t t') \<prec>\<^sub>l K \<and> Pos (Upair t t') \<noteq> K"
        unfolding 
          is_strictly_maximal_def
          \<open>P1 = add_mset L\<^sub>2 P\<^sub>2'\<close> \<open>L\<^sub>2 = t \<approx> t'\<close>
        by simp

      hence "\<forall>K \<in># P\<^sub>2'. K \<prec>\<^sub>l Pos (Upair t t')"
        by auto

      have thesis_if_Neg: "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        if "\<P> = Neg"
      proof -
        have "t \<preceq>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using term.order.less_eq_subterm_property .

        hence "multp (\<prec>\<^sub>t) {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s', s\<langle>t\<rangle>\<^sub>G, s'#}"
          unfolding reflclp_iff
        proof (elim disjE)
          assume "t \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"

          moreover hence "t' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
            using superpositionI(8) 
            by order

          ultimately show ?thesis
            by (auto intro: one_step_implies_multp[of _ _ _ "{#}", simplified])
        next
          assume "t = s\<langle>t\<rangle>\<^sub>G"
          thus ?thesis
            using \<open>t' \<prec>\<^sub>t t\<close>
            by simp
        qed
        thus "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using \<open>\<P> = Neg\<close>
          by (simp add: less\<^sub>l_def)
      qed

      have thesis_if_Pos: "Pos (Upair t t') \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        if "\<P> = Pos" and "is_maximal L\<^sub>1 P2"
      proof (cases "s")
        case Hole
        show ?thesis
        proof (cases "t' \<preceq>\<^sub>t s'")
          case True

          hence "(multp (\<prec>\<^sub>t))\<^sup>=\<^sup>= {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
            unfolding Hole
            by (simp add: multp_cancel_add_mset)

          thus ?thesis
            unfolding Hole \<open>\<P> = Pos\<close>
            by (auto simp: less\<^sub>l_def)
        next
          case False
          hence "s' \<prec>\<^sub>t t'"
            by order

          hence "multp (\<prec>\<^sub>t) {#s\<langle>t\<rangle>\<^sub>G, s'#} {#t, t'#}"
            by (simp add: Hole multp_cancel_add_mset)

          hence "\<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<prec>\<^sub>l Pos (Upair t t')"
            using \<open>\<P> = Pos\<close>
            by (simp add: less\<^sub>l_def)

          moreover have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
            using that
            unfolding superpositionI is_maximal_def
            by auto

          ultimately have "\<forall>K \<in># P\<^sub>1'. K \<preceq>\<^sub>l Pos (Upair t t')"
            by auto
            
          hence "P2 \<prec>\<^sub>c P1"
            using 
              \<open>\<P> (Upair s\<langle>t\<rangle>\<^sub>G s') \<prec>\<^sub>l Pos (Upair t t')\<close>
              one_step_implies_multp[of P1 P2 "(\<prec>\<^sub>l)" "{#}", simplified] 
              literal.order.multp_if_maximal_less_that_maximal 
              superpositionI
              that 
            unfolding less\<^sub>c_def
            by blast

          hence False
            using \<open>P1 \<prec>\<^sub>c P2\<close> by order

          thus ?thesis ..
        qed
      next
        case (More f ts1 ctxt ts2)
        hence "t \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using term.order.subterm_property[of s t]
          by simp

        moreover hence "t' \<prec>\<^sub>t s\<langle>t\<rangle>\<^sub>G"
          using \<open>t' \<prec>\<^sub>t t\<close> 
          by order

        ultimately have "multp (\<prec>\<^sub>t) {#t, t'#} {#s\<langle>t\<rangle>\<^sub>G, s'#}"
          using one_step_implies_multp[of "{#s\<langle>t\<rangle>\<^sub>G, s'#}" "{#t, t'#}" "(\<prec>\<^sub>t)" "{#}"] 
          by simp

        hence "Pos (Upair t t') \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using \<open>\<P> = Pos\<close>
          by (simp add: less\<^sub>l_def)

        thus ?thesis
          by order
      qed

      have "\<P> = Pos \<or> \<P> = Neg"
        using \<open>\<P> \<in> {Pos, Neg}\<close> 
        by simp

      thus ?thesis
      proof (elim disjE; intro ballI)
        fix K assume "\<P> = Pos" "K \<in># P\<^sub>2'"
        have "K \<prec>\<^sub>l t \<approx> t'"
          using \<open>\<forall>K\<in>#P\<^sub>2'. K \<prec>\<^sub>l t \<approx> t'\<close> \<open>K \<in># P\<^sub>2'\<close> 
          by metis

        also have "t \<approx> t' \<preceq>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
        proof (rule thesis_if_Pos[OF \<open>\<P> = Pos\<close>])

          have "is_strictly_maximal L\<^sub>1 P2"
            using \<open>\<P> = Pos\<close> superpositionI 
            by simp

          thus "is_maximal L\<^sub>1 P2"
            by blast
        qed

        finally show "K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')" .
      next
        fix K assume "\<P> = Neg" "K \<in># P\<^sub>2'"

        have "K \<prec>\<^sub>l t \<approx> t'"
          using \<open>\<forall>K\<in>#P\<^sub>2'. K \<prec>\<^sub>l t \<approx> t'\<close> \<open>K \<in># P\<^sub>2'\<close> 
          by metis

        also have "t \<approx> t' \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')"
          using thesis_if_Neg[OF \<open>\<P> = Neg\<close>] .

        finally show "K \<prec>\<^sub>l \<P> (Upair s\<langle>t\<rangle>\<^sub>G s')" .
      qed
    qed

    ultimately show "\<exists>j \<in># {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}. K \<prec>\<^sub>l j"
      by auto
  qed simp

  moreover have "C = add_mset (\<P> (Upair s\<langle>t'\<rangle>\<^sub>G s')) (P\<^sub>1' + P\<^sub>2')"
    unfolding superpositionI ..

  moreover have "P2 = P\<^sub>1' + {#\<P> (Upair s\<langle>t\<rangle>\<^sub>G s')#}"
    unfolding superpositionI by simp

  ultimately show ?thesis
    by simp
qed

lemma ground_eq_resolution_smaller_conclusion:
  assumes step: "eq_resolution P C"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: eq_resolution.cases)
  case (eq_resolutionI L t)
  then show ?thesis
    unfolding less\<^sub>c_def
    by (metis add.left_neutral add_mset_add_single empty_not_add_mset multi_member_split 
        one_step_implies_multp union_commute)
qed

lemma ground_eq_factoring_smaller_conclusion:
  assumes step: "eq_factoring P C"
  shows "C \<prec>\<^sub>c P"
  using step
proof (cases P C rule: eq_factoring.cases)
  case (eq_factoringI L\<^sub>1 L\<^sub>2 P' t t' t'')
  have "is_maximal L\<^sub>1 P"
    using eq_factoringI 
    by simp

  hence "\<forall>K \<in># add_mset (Pos (Upair t t'')) P'. \<not> Pos (Upair t t') \<prec>\<^sub>l K"
    unfolding eq_factoringI is_maximal_def
    by auto
   
  hence "\<not> Pos (Upair t t') \<prec>\<^sub>l Pos (Upair t t'')"
    by simp

  hence "Pos (Upair t t'') \<preceq>\<^sub>l Pos (Upair t t')"
    by order

  hence "t'' \<preceq>\<^sub>t t'"
    unfolding reflclp_iff
    by (auto simp: less\<^sub>l_def multp_cancel_add_mset)

  have "C = add_mset (Neg (Upair t' t'')) (add_mset (Pos (Upair t t'')) P')"
    using eq_factoringI 
    by argo

  moreover have "add_mset (Neg (Upair t' t'')) (add_mset (Pos (Upair t t'')) P') \<prec>\<^sub>c P"
    unfolding eq_factoringI less\<^sub>c_def
  proof (intro one_step_implies_multp[of "{#_#}" "{#_#}", simplified])
    have "t'' \<prec>\<^sub>t t"
      using \<open>t' \<prec>\<^sub>t t\<close> \<open>t'' \<preceq>\<^sub>t t'\<close> 
      by order

    hence "multp (\<prec>\<^sub>t) {#t', t'', t', t''#} {#t, t'#}"
      using one_step_implies_multp[of _ _ _ "{#}", simplified]
      by (metis \<open>t' \<prec>\<^sub>t t\<close> diff_empty id_remove_1_mset_iff_notin insert_iff
          set_mset_add_mset_insert)

    thus "Neg (Upair t' t'') \<prec>\<^sub>l Pos (Upair t t')"
      by (simp add: less\<^sub>l_def)
  qed

  ultimately show ?thesis
    by argo
qed

end

sublocale ground_superposition_calculus \<subseteq> consequence_relation where
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
      using ball_G_entails
      by (simp add: G_entails_def)

    then show "(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s N2"
      by (simp add: true_clss_def)
  qed
next
  show "\<And>N1 N2 N3. G_entails N1 N2 \<Longrightarrow> G_entails N2 N3 \<Longrightarrow> G_entails N1 N3"
    using G_entails_def
    by simp
qed

subsection \<open>Redundancy Criterion\<close>

sublocale ground_superposition_calculus \<subseteq> calculus_with_finitary_standard_redundancy where
  Inf = G_Inf and
  Bot = G_Bot and
  entails = G_entails and
  less = "(\<prec>\<^sub>c)"
  defines GRed_I = Red_I and GRed_F = Red_F
proof unfold_locales
  show "transp (\<prec>\<^sub>c)"
    by simp
next
  show "wfP (\<prec>\<^sub>c)"
    by auto
next
  show "\<And>\<iota>. \<iota> \<in> G_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
    by (auto simp: G_Inf_def)
next
  fix \<iota>
  have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P\<^sub>2, P\<^sub>1] C" and
      infer: "superposition P\<^sub>2 P\<^sub>1 C"
    for P\<^sub>2 P\<^sub>1 C
    unfolding \<iota>_def
    using infer
    using superposition_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "eq_resolution P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_eq_resolution_smaller_conclusion
    by simp

  moreover have "concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    if \<iota>_def: "\<iota> = Infer [P] C" and
      infer: "eq_factoring P C"
    for P C
    unfolding \<iota>_def
    using infer
    using ground_eq_factoring_smaller_conclusion
    by simp

  ultimately show "\<iota> \<in> G_Inf \<Longrightarrow> concl_of \<iota> \<prec>\<^sub>c main_prem_of \<iota>"
    unfolding G_Inf_def
    by fast
qed

end
