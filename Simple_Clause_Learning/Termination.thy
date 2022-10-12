theory Termination
  imports
    Simple_Clause_Learning
begin


section \<open>Extra Lemmas\<close>


subsection \<open>Wellfounded_Extra\<close>

lemma wf_if_measurable:
  fixes f :: "'a \<Rightarrow> 'b" and s :: "('b \<times> 'b) set"
  assumes
    "wf s"
    "\<And>x y. (x, y) \<in> r \<Longrightarrow> (f x, f y) \<in> s"
  shows "wf r"
  by (metis assms in_inv_image wfE_min wfI_min wf_inv_image)

lemma wfP_if_measurable:
  fixes f :: "'a \<Rightarrow> 'b" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes
    "wfP S"
    "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  shows "wfP R"
  using assms wf_if_measurable[to_pred, of S R f] by simp

lemma wfP_if_measurable_as_nat:
  fixes f :: "_ \<Rightarrow> nat"
  shows "(\<And>x y. R x y \<Longrightarrow> f x < f y) \<Longrightarrow> wfP R"
  by (rule wfP_if_measurable[of "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool", simplified])

lemma wf_union_if_measurable:
  fixes
    f :: "'a \<Rightarrow> 'b" and g :: "'a \<Rightarrow> 'c" and
    R S :: "('a \<times> 'a) set" and Q :: "('b \<times> 'b) set" and T :: "('c \<times> 'c) set"
  assumes
    "wf T"
    "\<And>x y. (x, y) \<in> R \<Longrightarrow> (g x, g y) \<in> T"
    "wf Q"
    "\<And>x y. (x, y) \<in> S \<Longrightarrow> (f x, f y) \<in> Q"
    "\<And>x y. (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> Q \<or> f x = f y"
  shows "wf (R \<union> S)"
proof (rule wf_if_measurable)
  show "wf (Q <*lex*> T)"
    by (rule wf_lex_prod[OF \<open>wf Q\<close> \<open>wf T\<close>])
next
  define h where
    "h \<equiv> \<lambda>z. (f z, g z)"
  
  fix x y assume "(x, y) \<in> R \<union> S"
  with assms(2,4,5) show "(h x, h y) \<in> Q <*lex*> T"
    unfolding h_def by fastforce
qed


lemma wfP_union_if_measurable:
  fixes
    f :: "'a \<Rightarrow> 'b" and g :: "'a \<Rightarrow> 'c" and
    R S :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and T :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  assumes
    "wfP T"
    "\<And>x y. R x y \<Longrightarrow> T (g x) (g y)"
    "wfP Q"
    "\<And>x y. S x y \<Longrightarrow> Q (f x) (f y)"
    "\<And>x y. R x y \<Longrightarrow> Q (f x) (f y) \<or> f x = f y"
  shows "wfP (R \<squnion> S)"
proof -
  have "wf ({(xa, x). R xa x} \<union> {(xa, x). S xa x})"
    using wf_union_if_measurable[to_pred, OF \<open>wfP T\<close> _ \<open>wfP Q\<close>,
        of R g "{(xa, x). S xa x}" f, simplified] assms(2,4,5)
    by simp
  thus ?thesis
    by (smt (verit, ccfv_threshold) CollectD CollectI UnCI case_prod_conv sup2E wfE_min wfI_min
        wfP_def)
qed


section \<open>Termination\<close>

context scl begin

definition ground_lits_of_lit where
  "ground_lits_of_lit L = {L \<cdot>l \<gamma> | \<gamma> . is_ground_lit (L \<cdot>l \<gamma>)}"

fun \<M> :: "_ \<Rightarrow> _ \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) Term.term literal set" where
  "\<M> N \<beta> (\<Gamma>, U, D) =
    {L \<in> \<Union>(ground_lits_of_lit ` \<Union>(set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>} - fst ` set \<Gamma>"

lemma minus_psubset_minusI:
  assumes "C \<subset> B" and "B \<subseteq> A"
  shows "(A - B \<subset> A - C)"
proof (rule Set.psubsetI)
  show "A - B \<subseteq> A - C"
    using assms(1) by blast
next
  show "A - B \<noteq> A - C"
    using assms by blast
qed

lemma
  fixes N \<beta>
  defines
    "scl_without_backtrack \<equiv> propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion>
      factorize N \<beta> \<squnion> resolve N \<beta>" and
    "invars \<equiv> \<lambda>S _. trail_atoms_lt \<beta> S \<and> trail_lits_ground S \<and> trail_lits_from_clauses N S \<and>
      initial_lits_generalize_learned_trail_conflict N S"
  shows "wfP (scl_without_backtrack \<sqinter> invars)\<inverse>\<inverse>"
proof (rule wfP_if_measurable)
  fix S S' :: "('f, 'v) state"
  assume "(scl_without_backtrack \<sqinter> invars)\<inverse>\<inverse> S S'"
  hence step: "scl_without_backtrack S' S" and invars: "invars S' S"
    by simp_all

  from invars have
    "trail_atoms_lt \<beta> S'" and
    "trail_lits_ground S'" and
    "trail_lits_from_clauses N S'" and
    "initial_lits_generalize_learned_trail_conflict N S'"
    by (simp_all add: invars_def)
  with step have
    "trail_lits_from_clauses N S" and
    "initial_lits_generalize_learned_trail_conflict N S"
    unfolding scl_without_backtrack_def
    by (auto simp add: scl_def intro: scl_preserves_trail_lits_from_clauses
        scl_preserves_initial_lits_generalize_learned_trail_conflict)

  have "trail_lits_from_init_clauses N S'"
    using \<open>trail_lits_from_clauses N S'\<close> \<open>initial_lits_generalize_learned_trail_conflict N S'\<close>
    by (simp add: trail_lits_from_init_clausesI)

  have "trail_lits_from_init_clauses N S"
    using \<open>trail_lits_from_clauses N S\<close> \<open>initial_lits_generalize_learned_trail_conflict N S\<close>
    by (simp add: trail_lits_from_init_clausesI)

  from step show "(\<M> N \<beta> S) < (\<M> N \<beta> S')"
    unfolding scl_without_backtrack_def sup_apply sup_bool_def
  proof (elim disjE)
    assume "decide N \<beta> S' S"
    thus "(\<M> N \<beta> S) < (\<M> N \<beta> S')"
    proof (cases N \<beta> S' S rule: decide.cases)
      case (decideI L \<gamma> \<Gamma> U)
      show ?thesis
        unfolding decideI(1,2) trail_decide_def \<M>.simps
      proof (rule minus_psubset_minusI)
        show "fst ` set \<Gamma> \<subset> fst ` set ((L \<cdot>l \<gamma>, None) # \<Gamma>)"
          using decideI
          by (auto simp add: trail_decide_def trail_defined_lit_def)
      next
        have "L \<cdot>l \<gamma> \<in> {L \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>}"
          unfolding mem_Collect_eq
          using decideI
          by (auto simp add: ground_lits_of_lit_def)
        moreover have "fst ` set \<Gamma> \<subseteq>
          {L \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>}"
        proof (rule Set.subsetI, unfold mem_Collect_eq, rule conjI)
          show "\<And>x. x \<in> fst ` set \<Gamma> \<Longrightarrow> atm_of x \<prec>\<^sub>B \<beta>"
            using \<open>trail_atoms_lt \<beta> S'\<close>
            by (auto simp add: trail_atoms_lt_def decideI(1))
        next
          fix K
          show "K \<in> fst ` set \<Gamma> \<Longrightarrow> K \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N))"
            using \<open>trail_lits_from_init_clauses N S'\<close>[unfolded trail_lits_from_init_clauses_def, rule_format, of K]
            using \<open>trail_lits_ground S'\<close>[unfolded trail_lits_ground_def, rule_format, of K]
            unfolding decideI(1,2) state_proj_simp
            by (smt (verit, best) UN_absorb UnI1 generalizes_lit_def ground_lits_of_lit_def
                mem_Collect_eq)
        qed
        ultimately show "fst ` set ((L \<cdot>l \<gamma>, None) # \<Gamma>) \<subseteq>
          {L \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>}"
          by simp
      qed
    qed
  next
    assume "propagate N \<beta> S' S"
    thus "\<M> N \<beta> S \<subset> \<M> N \<beta> S'"
    proof (cases N \<beta> S' S rule: propagate.cases)
      case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu> \<gamma>' \<rho> \<gamma>\<^sub>\<rho>')

      have "L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<mu> \<cdot>l \<gamma>'"
        unfolding \<open>\<gamma>\<^sub>\<rho>' = adapt_subst_to_renaming \<rho> \<gamma>'\<close>
      proof (rule subst_lit_renaming_subst_adapted)
        show "is_renaming \<rho>"
          using propagateI(3-) by simp
      next
        have "add_mset L C\<^sub>0 \<subseteq># C"
          using propagateI(3-) by simp
        hence "add_mset L C\<^sub>0 \<cdot> \<mu> \<subseteq># C \<cdot> \<mu>"
          by (rule subst_cls_mono_mset) thm subst_cls_mono_mset[no_vars]
        hence "vars_cls (add_mset L C\<^sub>0 \<cdot> \<mu>) \<subseteq> vars_cls (C \<cdot> \<mu>)"
          by (metis mset_subset_eq_exists_conv sup_ge1 vars_cls_plus_iff)
        also have "\<dots> \<subseteq> vars_cls C"
        proof (rule subset_trans[OF vars_subst_cls_subset_weak])
          have "range_vars \<mu> \<subseteq> vars_cls (add_mset L C\<^sub>1)"
            using \<open>is_mimgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>[unfolded is_mimgu_def,
                THEN conjunct2]
            by (auto simp add: vars_cls_def)
          also have "\<dots> \<subseteq> vars_cls C"
            apply (rule vars_cls_subset_vars_cls_if_subset_mset)
            unfolding \<open>C = add_mset L C'\<close> \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
            by simp
          finally show "vars_cls C \<union> range_vars \<mu> \<subseteq> vars_cls C"
            by simp
        qed
        also have "\<dots> \<subseteq> subst_domain \<gamma>"
          by (rule vars_cls_subset_subst_domain_if_grounding[OF \<open>is_ground_cls (C \<cdot> \<gamma>)\<close>])

        finally show "vars_lit (L \<cdot>l \<mu>) \<subseteq> subst_domain \<gamma>'"
          unfolding \<open>\<gamma>' = restrict_subst (vars_cls (add_mset L C\<^sub>0 \<cdot> \<mu>)) \<gamma>\<close>
          unfolding subst_domain_restrict_subst
          by simp
      qed
      also have "\<dots> = L \<cdot>l \<mu> \<cdot>l \<gamma>"
        using propagateI(3-) by (simp add: subst_lit_restrict_subst_idem)
      also have "\<dots> = L \<cdot>l \<gamma>"
      proof -
        have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
          unfolding \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
          by (auto simp: is_unifiers_def is_unifier_alt intro: subst_atm_of_eqI)
        hence "\<mu> \<odot> \<gamma> = \<gamma>"
          using \<open>is_mimgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>[unfolded is_mimgu_def,
              THEN conjunct1, unfolded is_imgu_def, THEN conjunct2]
          by simp
        thus ?thesis
          by (metis subst_lit_comp_subst)
      qed
      finally have "L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<gamma>"
        by assumption

      show ?thesis
        unfolding propagateI(1,2) trail_propagate_def \<M>.simps list.set image_insert prod.sel
      proof (rule minus_psubset_minusI)
        show "fst ` set \<Gamma> \<subset> insert (L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>') (fst ` set \<Gamma>)"
          unfolding \<open>L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<gamma>\<close>
          using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>
          by (metis insertCI psubsetI subset_insertI trail_defined_lit_def)
      next
        show "insert (L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>') (fst ` set \<Gamma>) \<subseteq>
          {L \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>}"
          unfolding \<open>L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<gamma>\<close>
        proof (intro Set.subsetI Set.CollectI conjI)
          fix K assume "K \<in> insert (L \<cdot>l \<gamma>) (fst ` set \<Gamma>)"
          thus "atm_of K \<prec>\<^sub>B \<beta>"
            using \<open>trail_atoms_lt \<beta> S'\<close>
            by (metis image_eqI insert_iff propagateI(1,4,6) state_trail_simp subst_cls_add_mset
                trail_atoms_lt_def union_single_eq_member)
        next
          fix K assume K_in: "K \<in> insert (L \<cdot>l \<gamma>) (fst ` set \<Gamma>)"

          from K_in have "is_ground_lit K"
            using \<open>trail_lits_ground S'\<close>
            by (metis insert_iff is_ground_cls_def propagateI(1,4,5) state_trail_simp
                subst_cls_add_mset trail_lits_ground_def union_single_eq_member)

          moreover from K_in have "\<exists>K'\<in>\<Union> (set_mset ` (fset N)). generalizes_lit K' K"
            using \<open>trail_lits_from_init_clauses N S\<close>
            unfolding trail_lits_from_init_clauses_def propagateI(1,2) trail_propagate_def \<open>L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<gamma>\<close>
            unfolding state_proj_simp list.set image_insert prod.sel
            by fast

          ultimately show "K \<in> \<Union> (ground_lits_of_lit ` \<Union> (set_mset ` fset N))"
            unfolding UN_iff
            using \<open>trail_lits_from_init_clauses N S'\<close>[unfolded trail_lits_from_init_clauses_def propagateI(1,2) state_proj_simp]
            by (smt (verit, best) ground_lits_of_lit_def mem_Collect_eq generalizes_lit_def)
        qed
      qed
    qed
  next
    show "conflict N \<beta> S' S \<Longrightarrow> \<M> N \<beta> S \<subset> \<M> N \<beta> S'" sorry
  next
    show "skip N \<beta> S' S \<Longrightarrow> \<M> N \<beta> S \<subset> \<M> N \<beta> S'" sorry
  next
    show "factorize N \<beta> S' S \<Longrightarrow> \<M> N \<beta> S \<subset> \<M> N \<beta> S'" sorry
  next
    show "resolve N \<beta> S' S \<Longrightarrow> \<M> N \<beta> S \<subset> \<M> N \<beta> S'" sorry
  qed
next
  show "wfP (\<subset>)"
    oops












thm scl_def reasonable_scl_def regular_scl_def

definition regular_state ::
  "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "regular_state N \<beta> S \<longleftrightarrow> True"

definition regular ::
  "_ \<Rightarrow> ('f, 'v) term clause set \<Rightarrow> ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool"  where
  "regular step N \<beta> S S' \<longleftrightarrow> regular_state N \<beta> S \<and> step N \<beta> S S'"

definition reg_backtrack where
  "reg_backtrack N \<beta> S S' \<longleftrightarrow> backtrack N \<beta> S S' \<and> (\<nexists>S''. conflict N \<beta> S S'')"

thm wf_bounded_measure[of r ub f]

term "conversep"

lemma
  assumes
    "wfP R" and
    "\<And>x y. (propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion>
      factorize N \<beta> \<squnion> resolve N \<beta>)\<inverse>\<inverse> x y \<Longrightarrow> R (m\<^sub>R x) (m\<^sub>R y)"
  shows "wfP (propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta> \<squnion>
    backtrack N \<beta>)\<inverse>\<inverse>"
proof -
  define gnd_\<beta> where
    "gnd_\<beta> \<equiv> {}"
  define count_remaining :: "('f, 'v) state \<Rightarrow> nat" where
    "count_remaining \<equiv> \<lambda>S. card gnd_\<beta> - card (state_learned S)"

  show ?thesis
    unfolding converse_join
  proof (rule wfP_union_if_measurable)
    show "wfP R"
      by (rule assms(1))
  next
    fix S S' :: "('f, 'v) state"
    show "((propagate N \<beta>)\<inverse>\<inverse> \<squnion> (decide N \<beta>)\<inverse>\<inverse> \<squnion> (conflict N \<beta>)\<inverse>\<inverse> \<squnion> (skip N \<beta>)\<inverse>\<inverse> \<squnion>
      (factorize N \<beta>)\<inverse>\<inverse> \<squnion> (resolve N \<beta>)\<inverse>\<inverse>) S S' \<Longrightarrow> R (m\<^sub>R S) (m\<^sub>R S')"
      by (rule assms(2)[unfolded converse_join])
  next
    show "wfP ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
      by simp
  next
    fix S' S :: "('f, 'v) state" assume "(backtrack N \<beta>)\<inverse>\<inverse> S' S"
    hence "backtrack N \<beta> S S'"
      by simp
    thus "count_remaining S' < count_remaining S"
    proof (cases N \<beta> S S' rule: backtrack.cases)
      case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
      then have "card (state_learned S') = Suc (card (state_learned S))"
        sorry
      moreover have "card gnd_\<beta> > card (state_learned S)"
        sorry
      ultimately show ?thesis
        unfolding count_remaining_def by simp
    qed
  next
    fix S' S :: "('f, 'v) state"
    assume "((propagate N \<beta>)\<inverse>\<inverse> \<squnion> (decide N \<beta>)\<inverse>\<inverse> \<squnion> (conflict N \<beta>)\<inverse>\<inverse> \<squnion> (skip N \<beta>)\<inverse>\<inverse> \<squnion>
      (factorize N \<beta>)\<inverse>\<inverse> \<squnion> (resolve N \<beta>)\<inverse>\<inverse>) S' S"
    moreover have "propagate N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule propagate.cases) simp
    moreover have "decide N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule decide.cases) simp
    moreover have "conflict N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule conflict.cases) simp
    moreover have "skip N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule skip.cases) simp
    moreover have "factorize N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule factorize.cases) simp
    moreover have "resolve N \<beta> S S' \<Longrightarrow> state_learned S' = state_learned S"
      by (erule resolve.cases) simp
    ultimately have "state_learned S' = state_learned S"
      unfolding sup_apply sup_bool_def by (elim disjE) simp_all
    thus "count_remaining S' < count_remaining S \<or> count_remaining S' = count_remaining S"
      by (simp add: count_remaining_def)
  qed
qed

lemma "wfP (scl N \<beta>)"
proof -
  show ?thesis
  unfolding scl_def

thm wfP_union_if_measurable


end