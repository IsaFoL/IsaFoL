theory Termination
  imports
    Simple_Clause_Learning
    "HOL-Library.Monad_Syntax"
    (* "HOL-Library.State_Monad" *)
begin


section \<open>Extra Lemmas\<close>


subsection \<open>Set_Extra\<close>

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


subsection \<open>Prod_Extra\<close>

definition lex_prodp where
  "lex_prodp RA RB x y \<longleftrightarrow> RA (fst x) (fst y) \<or> fst x = fst y \<and> RB (snd x) (snd y)"

lemma lex_prod_lex_prodp_eq:
  "lex_prod {(x, y). RA x y} {(x, y). RB x y} = {(x, y). lex_prodp RA RB x y}"
  unfolding lex_prodp_def lex_prod_def
  by auto

lemma reflp_on_lex_prodp:
  assumes "reflp_on A RA"
  shows "reflp_on (A \<times> B) (lex_prodp RA RB)"
proof (rule reflp_onI)
  fix x assume "x \<in> A \<times> B"
  hence "fst x \<in> A"
    by auto
  thus "lex_prodp RA RB x x"
    by (simp add: lex_prodp_def \<open>reflp_on A RA\<close>[THEN reflp_onD])
qed

lemma transp_lex_prodp:
  assumes "transp RA" and "transp RB"
  shows "transp (lex_prodp RA RB)"
proof (rule transpI)
  fix x y z assume "lex_prodp RA RB x y" and "lex_prodp RA RB y z"
  thus "lex_prodp RA RB x z"
    by (auto simp add: lex_prodp_def \<open>transp RA\<close>[THEN transpD, of "fst x" "fst y" "fst z"]
        \<open>transp RB\<close>[THEN transpD, of "snd x" "snd y" "snd z"])
qed

lemma asymp_lex_prodp:
  assumes "asymp RA" and "asymp RB"
  shows "asymp (lex_prodp RA RB)"
proof (rule asympI)
  fix x y assume "lex_prodp RA RB x y"
  thus "\<not> lex_prodp RA RB y x"
    using assms by (metis (full_types, opaque_lifting) asymp.cases lex_prodp_def)
qed

lemma totalp_on_lex_prodp:
  assumes "totalp_on A RA" and "totalp_on B RB"
  shows "totalp_on (A \<times> B) (lex_prodp RA RB)"
proof (rule totalp_onI)
  fix x y assume "x \<in> A \<times> B" and "y \<in> A \<times> B" and "x \<noteq> y"
  then show "lex_prodp RA RB x y \<or> lex_prodp RA RB y x"
    using assms
    by (metis (full_types) lex_prodp_def mem_Times_iff prod_eq_iff totalp_on_def)
qed

lemma wfP_lex_prodp:
  assumes "wfP RA" and "wfP RB"
  shows "wfP (lex_prodp RA RB)"
  using assms
  by (rule wf_lex_prod[of "{(x, y). RA x y}" "{(x, y). RB x y}", unfolded lex_prod_lex_prodp_eq, to_pred])
  

instantiation prod :: (preorder, preorder) order begin

definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "x < y \<longleftrightarrow> lex_prodp less less x y"

definition less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod x y \<longleftrightarrow> x < y \<or> x = y"

instance
proof intro_classes
  fix x y :: "'a \<times> 'b"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_eq_prod_def less_prod_def
    using order_less_imp_not_less
    by (metis (full_types, opaque_lifting) lex_prodp_def order_less_imp_not_less)
next
  fix x :: "'a \<times> 'b"
  show "x \<le> x"
    unfolding less_eq_prod_def
    by simp
next
  fix x y z :: "'a \<times> 'b"
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_prod_def less_prod_def
    using transp_lex_prodp[OF transp_less transp_less, THEN transpD]
    by metis
next
  fix x y :: "'a \<times> 'b"
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_prod_def less_prod_def
    using asymp_lex_prodp[OF asymp_less asymp_less, THEN asympD]
    by metis
qed

end

instance prod :: (linorder, linorder) linorder
proof intro_classes
  fix x y :: "'a \<times> 'b"
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_prod_def less_prod_def
    using totalp_on_lex_prodp[OF totalp_less totalp_less, of UNIV UNIV, simplified, THEN totalpD]
    by metis
qed

instance prod :: (wellorder, wellorder) wellorder
proof intro_classes
  fix P :: "'a \<times> 'b \<Rightarrow> bool" and x :: "'a \<times> 'b"
  assume "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  then show "P x"
    unfolding less_prod_def
    using wfP_lex_prodp[OF wfP_less wfP_less, THEN wfP_induct]
    by metis
qed


subsection \<open>Wellfounded_Extra\<close>

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
proof (rule wf_if_convertible_to_wf)
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


subsection \<open>FSet_Extra\<close>

lemma finsert_Abs_fset: "finite A \<Longrightarrow> finsert a (Abs_fset A) = Abs_fset (insert a A)"
  by (simp add: eq_onp_same_args finsert.abs_eq)

lemma minus_pfsubset_minusI:
  assumes "C |\<subset>| B" and "B |\<subseteq>| A"
  shows "(A |-| B |\<subset>| A |-| C)"
proof (rule FSet.pfsubsetI)
  show "A |-| B |\<subseteq>| A |-| C"
    using assms(1) by blast
next
  show "A |-| B \<noteq> A |-| C"
    using assms by blast
qed

lemma Abs_fset_minus: "finite A \<Longrightarrow> finite B \<Longrightarrow> Abs_fset (A - B) = Abs_fset A |-| Abs_fset B"
  by (metis Abs_fset_inverse fset_inverse mem_Collect_eq minus_fset)


section \<open>Termination\<close>

context scl begin

definition \<M>_prop_deci :: "_ \<Rightarrow> _ \<Rightarrow> (_, _) Term.term literal fset" where
  "\<M>_prop_deci \<beta> \<Gamma> = Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>} |-| (fst |`| fset_of_list \<Gamma>)"

primrec \<M>_skip_fact_reso where
  "\<M>_skip_fact_reso [] C = []" |
  "\<M>_skip_fact_reso (Ln # \<Gamma>) C =
    (let n = count C (- (fst Ln)) in
    (case snd Ln of None \<Rightarrow> 0 | Some _ \<Rightarrow> n) #
      \<M>_skip_fact_reso \<Gamma> (C + (case snd Ln of None \<Rightarrow> {#} | Some (D, _, \<gamma>) \<Rightarrow> repeat_mset n (D \<cdot> \<gamma>))))"

lemma length_\<M>_skip_fact_reso[simp]: "length (\<M>_skip_fact_reso \<Gamma> C) = length \<Gamma>"
  by (induction \<Gamma> arbitrary: C) (simp_all add: Let_def)

lemma \<M>_skip_fact_reso_add_mset:
  "(\<M>_skip_fact_reso \<Gamma> C, \<M>_skip_fact_reso \<Gamma> (add_mset L C)) \<in> (List.lenlex {(x, y). x < y})\<^sup>="
proof (induction \<Gamma> arbitrary: C)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "snd Ln")
    case None
    then show ?thesis
      using Cons.IH[of C]
      by (simp add: Cons_lenlex_iff)
  next
    case (Some cl)
    show ?thesis
    proof (cases "L = - fst Ln")
      case True
      then show ?thesis
        by (simp add: Let_def Some Cons_lenlex_iff)
    next
      case False
      then show ?thesis
        using Cons.IH
        by (auto simp add: Let_def Some Cons_lenlex_iff)
    qed
  qed
qed

definition \<M> :: "_ \<Rightarrow> _ \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) Term.term literal fset \<times> nat list \<times> nat" where
  "\<M> N \<beta> S =
    (case state_conflict S of
      None \<Rightarrow> (\<M>_prop_deci \<beta> (state_trail S), [], 0)
    | Some (C, \<gamma>) \<Rightarrow> ({||}, \<M>_skip_fact_reso (state_trail S) (C \<cdot> \<gamma>), size C))"

theorem scl_without_backtrack_terminates:
  fixes N \<beta>
  defines
    "scl_without_backtrack \<equiv> propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion>
      factorize N \<beta> \<squnion> resolve N \<beta>" and
    "invars \<equiv> trail_atoms_lt \<beta> \<sqinter> trail_resolved_lits_pol \<sqinter> trail_lits_ground \<sqinter>
      trail_lits_from_clauses N \<sqinter> initial_lits_generalize_learned_trail_conflict N \<sqinter>
      conflict_disjoint_vars N \<sqinter> minimal_ground_closures"
  shows
    "wfP (\<lambda>S' S. scl_without_backtrack S S' \<and> invars S)" and
    "invars initial_state" and
    "\<And>S S'. scl_without_backtrack S S' \<Longrightarrow> invars S \<Longrightarrow> invars S'"
proof -
  show "invars initial_state"
    by (simp add: invars_def)
next
  fix S S'
  assume "scl_without_backtrack S S'"
  hence "scl N \<beta> S S'"
    unfolding scl_without_backtrack_def sup_apply sup_bool_def
    by (auto simp add: scl_def)
  thus "invars S \<Longrightarrow> invars S'"
    unfolding invars_def
    by (auto intro: scl_preserves_trail_atoms_lt
        scl_preserves_trail_resolved_lits_pol
        scl_preserves_trail_lits_ground
        scl_preserves_trail_lits_from_clauses
        scl_preserves_initial_lits_generalize_learned_trail_conflict
        scl_preserves_conflict_disjoint_vars
        scl_preserves_minimal_ground_closures)
next
  show "wfP (\<lambda>S' S. scl_without_backtrack S S' \<and> invars S)"
  proof (rule wfP_if_convertible_to_wfP)
    fix S' S :: "('f, 'v) state"
    assume "scl_without_backtrack S S' \<and> invars S"
    hence step: "scl_without_backtrack S S'" and invars: "invars S"
      by simp_all

    from invars have
      "trail_atoms_lt \<beta> S" and
      "trail_resolved_lits_pol S" and
      "trail_lits_ground S" and
      "trail_lits_from_clauses N S" and
      "initial_lits_generalize_learned_trail_conflict N S" and
      "conflict_disjoint_vars N S" and
      "minimal_ground_closures S"
      by (simp_all add: invars_def)
    with step have
      "trail_lits_from_clauses N S'" and
      "initial_lits_generalize_learned_trail_conflict N S'"
      unfolding scl_without_backtrack_def
      by (auto simp add: scl_def intro: scl_preserves_trail_lits_from_clauses
          scl_preserves_initial_lits_generalize_learned_trail_conflict)

    have "trail_lits_from_init_clauses N S"
      using \<open>trail_lits_from_clauses N S\<close> \<open>initial_lits_generalize_learned_trail_conflict N S\<close>
      by (simp add: trail_lits_from_init_clausesI)

    have "trail_lits_from_init_clauses N S'"
      using \<open>trail_lits_from_clauses N S'\<close> \<open>initial_lits_generalize_learned_trail_conflict N S'\<close>
      by (simp add: trail_lits_from_init_clausesI)

    let ?less = "lex_prodp (|\<subset>|) (lex_prodp (\<lambda>x y. (x, y) \<in> List.lenlex {(x, y). x < y}) (<))"

    from step show "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      unfolding scl_without_backtrack_def sup_apply sup_bool_def
    proof (elim disjE)
      assume "decide N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: decide.cases)
        case (decideI L \<gamma> \<Gamma> U)
        have "\<M>_prop_deci \<beta> ((L \<cdot>l \<gamma>, None) # \<Gamma>) |\<subset>| \<M>_prop_deci \<beta> \<Gamma>"
          unfolding \<M>_prop_deci_def fset_of_list_simps fimage_finsert prod.sel
        proof (rule minus_pfsubset_minusI)
          show "fst |`| fset_of_list \<Gamma> |\<subset>| finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>)"
            using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>[unfolded trail_defined_lit_def]
            by (metis (no_types, lifting) finsertCI fset_of_list_elem fset_of_list_map
                fsubset_finsertI list.set_map nless_le)
        next
          have "L \<cdot>l \<gamma> \<in> {L. atm_of L \<prec>\<^sub>B \<beta>}"
            using \<open>atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>\<close>
            by simp
          moreover have "fst ` set \<Gamma> \<subseteq> {L. atm_of L \<prec>\<^sub>B \<beta>}"
            using \<open>trail_atoms_lt \<beta> S\<close>
            by (auto simp: trail_atoms_lt_def decideI(1))
          ultimately have "insert (L \<cdot>l \<gamma>) (fst ` set \<Gamma>) \<subseteq> {L. atm_of L \<prec>\<^sub>B \<beta>}"
            by simp
          also have "\<dots> \<subseteq> {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>}"
            by blast
          finally show "finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>) |\<subseteq>|
          Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>}"
            using finite_lits_less_eq_B
            by (simp add: less_eq_fset.rep_eq fimage.rep_eq fset_of_list.rep_eq Abs_fset_inverse)
        qed
        then show ?thesis
          unfolding decideI(1,2) trail_decide_def \<M>_def state_proj_simp option.case
          unfolding lex_prodp_def prod.sel by simp
      qed
    next
      assume "propagate N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: propagate.cases)
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

        have "\<M>_prop_deci \<beta> ((L \<cdot>l \<gamma>, Some (C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>, L \<cdot>l \<mu> \<cdot>l \<rho>, \<gamma>\<^sub>\<rho>')) # \<Gamma>) |\<subset>| \<M>_prop_deci \<beta> \<Gamma>"
          unfolding \<M>_prop_deci_def fset_of_list_simps fimage_finsert prod.sel
        proof (rule minus_pfsubset_minusI)
          show "fst |`| fset_of_list \<Gamma> |\<subset>| finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>)"
            using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>[unfolded trail_defined_lit_def]
            by (metis (no_types, lifting) finsertCI fset_of_list_elem fset_of_list_map
                fsubset_finsertI list.set_map nless_le)
        next
          have "insert (L \<cdot>l \<gamma>) (fst ` set \<Gamma>) \<subseteq> {L. atm_of L \<prec>\<^sub>B \<beta>}"
          proof (intro Set.subsetI Set.CollectI)
            fix K assume "K \<in> insert (L \<cdot>l \<gamma>) (fst ` set \<Gamma>)"
            thus "atm_of K \<prec>\<^sub>B \<beta>"
              using \<open>trail_atoms_lt \<beta> S\<close>
              by (metis image_eqI insert_iff propagateI(1,4,6) state_trail_simp subst_cls_add_mset
                  trail_atoms_lt_def union_single_eq_member)
          qed
          also have "\<dots> \<subseteq> {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>}"
            by blast
          finally show "finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>) |\<subseteq>|
          Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>}"
            using finite_lits_less_eq_B
            by (simp add: less_eq_fset.rep_eq fimage.rep_eq fset_of_list.rep_eq Abs_fset_inverse)
        qed
        thus ?thesis
          unfolding propagateI(1,2) trail_propagate_def \<M>_def state_proj_simp option.case
          unfolding \<open>L \<cdot>l \<mu> \<cdot>l \<rho> \<cdot>l \<gamma>\<^sub>\<rho>' = L \<cdot>l \<gamma>\<close>
          unfolding lex_prodp_def prod.sel by simp
      qed
    next
      assume "conflict N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: conflict.cases)
        case (conflictI D U \<gamma> \<Gamma> \<rho> \<gamma>\<^sub>\<rho>)
        have "\<And>L. L |\<in>| fst |`| fset_of_list \<Gamma> \<Longrightarrow> atm_of L \<prec>\<^sub>B \<beta>"
          using \<open>trail_atoms_lt \<beta> S\<close>[unfolded conflictI(1,2) trail_atoms_lt_def, simplified]
          by (metis (no_types, opaque_lifting) fimageE fset_of_list_elem)
        hence "Pos \<beta> |\<notin>| fst |`| fset_of_list \<Gamma> \<and> Neg \<beta> |\<notin>| fst |`| fset_of_list \<Gamma>"
          by (metis irreflpD irreflp_less_B literal.sel(1) literal.sel(2))
        hence "finsert (Pos \<beta>) (finsert (Neg \<beta>) (Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>})) |-|
        fst |`| fset_of_list \<Gamma> =
        finsert (Pos \<beta>) (finsert (Neg \<beta>) (Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>} - fst |`| fset_of_list \<Gamma>))"
          by (simp add: finsert_fminus_if)
        hence "{||} |\<subset>| finsert (Pos \<beta>) (finsert (Neg \<beta>) (Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>})) |-| fst |`| fset_of_list \<Gamma>"
          by auto
        also have "\<dots> = \<M>_prop_deci \<beta> \<Gamma>"
          unfolding \<M>_prop_deci_def
          unfolding lits_less_eq_B_conv
          using finite_lits_less_B
          by (simp add: finsert_Abs_fset)
        finally show ?thesis
          unfolding lex_prodp_def conflictI(1,2)
          unfolding \<M>_def state_proj_simp option.case prod.case prod.sel
          by simp
      qed
    next
      assume "skip N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: skip.cases)
        case (skipI L D \<sigma> n \<Gamma> U)
        have "(\<M>_skip_fact_reso \<Gamma> (D \<cdot> \<sigma>), \<M>_skip_fact_reso ((L, n) # \<Gamma>) (D \<cdot> \<sigma>)) \<in>
          lenlex {(x, y). x < y}"
          by (simp add: lenlex_conv Let_def)
        thus ?thesis
          unfolding lex_prodp_def skipI(1,2)
          unfolding \<M>_def state_proj_simp option.case prod.case prod.sel
          by simp
      qed
    next
      assume "factorize N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: factorize.cases)
        case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)

        have "is_unifier \<sigma> {atm_of L, atm_of L'}"
          using \<open>L \<cdot>l \<sigma> = L' \<cdot>l \<sigma>\<close>[THEN subst_atm_of_eqI]
          by (simp add: is_unifier_alt)
        hence "\<mu> \<odot> \<sigma> = \<sigma>"
          using \<open>is_mimgu \<mu> {{atm_of L, atm_of L'}}\<close>
          by (simp add: is_mimgu_def is_imgu_def is_unifiers_def)

        have "add_mset L D \<cdot> \<mu> \<cdot> \<sigma>' = add_mset L D \<cdot> \<mu> \<cdot> \<sigma>"
          unfolding factorizeI
          by (rule subst_cls_restrict_subst_idem) simp
        also have "\<dots> = add_mset L D \<cdot> \<sigma>"
          using \<open>\<mu> \<odot> \<sigma> = \<sigma>\<close>
          by (metis subst_cls_comp_subst)
        finally have "(\<M>_skip_fact_reso \<Gamma> (add_mset L D \<cdot> \<mu> \<cdot> \<sigma>'),
          \<M>_skip_fact_reso \<Gamma> (add_mset L' (add_mset L D) \<cdot> \<sigma>)) \<in> (lenlex {(x, y). x < y})\<^sup>="
          using \<M>_skip_fact_reso_add_mset
          by (metis subst_cls_add_mset)
        thus ?thesis
          unfolding lex_prodp_def factorizeI(1,2)
          unfolding \<M>_def state_proj_simp option.case prod.case prod.sel
          unfolding add_mset_commute[of L' L]
          by simp
      qed
    next
      assume "resolve N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
        hence ren_\<rho>: "is_renaming \<rho>"
          using finite_fset is_renaming_renaming_wrt by blast

        from \<open>minimal_ground_closures S\<close> have
          ground_conflict: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)" and
          ground_resolvant: "is_ground_cls (add_mset L C \<cdot> \<delta>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)" and
          dom_\<delta>: "subst_domain \<delta> \<subseteq> vars_cls (add_mset L C)"
          unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close>
          by (simp_all add: minimal_ground_closures_def trail_propagate_def)

        have vars_conflict_disj_vars_resolvant:
          "vars_cls (add_mset L' D) \<inter> vars_cls (add_mset L C) = {}"
          using \<open>conflict_disjoint_vars N S\<close>
          unfolding resolveI(1,2)
          by (auto simp add: \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close> trail_propagate_def conflict_disjoint_vars_def)

        from \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)\<close> have "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
          by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
        hence "atm_of L \<cdot>a \<sigma> \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma> \<cdot>a \<delta>"
        proof (rule subst_subst_eq_subst_subst_if_subst_eq_substI)
          show "vars_lit L \<inter> subst_domain \<sigma> = {}"
            using dom_\<sigma> vars_conflict_disj_vars_resolvant by auto
        next
          show "vars_lit L' \<inter> subst_domain \<delta> = {}"
            using dom_\<delta> vars_conflict_disj_vars_resolvant by auto
        next
          have "range_vars \<sigma> = {}"
            unfolding range_vars_def UNION_empty_conv subst_range.simps
            using dom_\<sigma> ground_conflict is_ground_cls_is_ground_on_var is_ground_atm_iff_vars_empty
            by fast
          thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
            by simp
        qed
        hence is_unifs_\<sigma>_\<delta>: "is_unifiers (\<sigma> \<odot> \<delta>) {{atm_of L, atm_of L'}}"
          by (simp add: is_unifiers_def is_unifier_def subst_atms_def)
        hence "\<mu> \<odot> \<sigma> \<odot> \<delta> = \<sigma> \<odot> \<delta>"
          using \<open>is_mimgu \<mu> {{atm_of L, atm_of L'}}\<close>
          by (auto simp: is_mimgu_def is_imgu_def)
        hence "(D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta> = (D + C) \<cdot> \<sigma> \<cdot> \<delta>"
          by (metis subst_cls_comp_subst)

        have "D \<cdot> \<sigma> \<cdot> \<delta> = D \<cdot> \<sigma>"
          using ground_conflict by (simp add: is_ground_cls_add_mset)

        hence "subst_domain \<sigma> \<inter> vars_cls C = {}"
          using dom_\<sigma> vars_conflict_disj_vars_resolvant by auto
        hence "C \<cdot> \<sigma> \<cdot> \<delta> = C \<cdot> \<delta>"
          by (simp add: subst_cls_idem_if_disj_vars)

        have "- (L \<cdot>l \<delta>) \<notin># C \<cdot> \<delta>"
          using \<open>trail_resolved_lits_pol S\<close>
          unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close>
          by (simp add: trail_resolved_lits_pol_def trail_propagate_def)

        have "(\<M>_skip_fact_reso \<Gamma> (D \<cdot> \<sigma> + C \<cdot> \<delta>), \<M>_skip_fact_reso \<Gamma> (D \<cdot> \<sigma> + {#L'#} \<cdot> \<sigma>)) \<in>
          lex {(x, y). x < y}"
          unfolding \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close> trail_propagate_def
          unfolding \<M>_skip_fact_reso.simps Let_def prod.sel option.case prod.case
          unfolding lex_conv mem_Collect_eq prod.case
          apply (rule conjI)
           apply simp
          apply (rule exI[of _ "[]"])
          apply simp
          using \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)\<close>[unfolded uminus_lit_swap, symmetric]
          apply simp
          unfolding count_eq_zero_iff
          by (rule \<open>- (L \<cdot>l \<delta>) \<notin># C \<cdot> \<delta>\<close>)
        hence "(\<M>_skip_fact_reso \<Gamma> (D \<cdot> \<sigma> + C \<cdot> \<delta>), \<M>_skip_fact_reso \<Gamma> (D \<cdot> \<sigma> + {#L'#} \<cdot> \<sigma>)) \<in>
          lenlex {(x, y). x < y}"
          unfolding lenlex_conv by simp
        thus ?thesis
          unfolding lex_prodp_def resolveI(1,2)
          unfolding \<M>_def state_proj_simp option.case prod.case prod.sel
          unfolding subst_cls_restrict_subst_idem[OF subset_refl] subst_cls_comp_subst
            subst_cls_renaming_inv_renaming_idem[OF ren_\<rho>]
          unfolding \<open>(D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta> = (D + C) \<cdot> \<sigma> \<cdot> \<delta>\<close>
          unfolding subst_cls_union \<open>D \<cdot> \<sigma> \<cdot> \<delta> = D \<cdot> \<sigma>\<close> \<open>C \<cdot> \<sigma> \<cdot> \<delta> = C \<cdot> \<delta>\<close>
          by simp
      qed
    qed
  next
    show "wfP (lex_prodp (|\<subset>|)
      (lex_prodp (\<lambda>x y. (x, y) \<in> List.lenlex {(x :: nat, y :: nat). x < y})
        ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)))"
    proof (intro wfP_lex_prodp)
      show "wfP (|\<subset>|)"
        by (rule wfP_pfsubset)
    next
      show "wfP (\<lambda>x y. (x, y) \<in> lenlex {(x :: _ :: wellorder, y). x < y})"
        unfolding wfP_wf_eq
        using wf_lenlex
        using wf by blast
    next
      show "wfP ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)"
        by simp
    qed
  qed
qed

term generalizes_atm
thm generalizes_atm_def

lemma generalizes_atm_refl[simp]: "generalizes_atm t t"
  unfolding generalizes_atm_def
proof (rule exI)
  show "t \<cdot>a Var = t"
    by simp
qed

lemma
  assumes "\<And>w. generalizes_atm w u \<longleftrightarrow> (\<exists>t \<in> T. generalizes_atm t w)"
  shows "\<forall>t \<in> T. generalizes_atm t u"
proof (rule ballI)
  fix t assume "t \<in> T"
  show "generalizes_atm t u"
    unfolding assms
  proof (rule bexI)
    show "generalizes_atm t t"
      by simp
  next
    show "t \<in> T"
      by (rule \<open>t \<in> T\<close>)
  qed
qed

lemma size_le_size_if_generalizes_atm:
  assumes "generalizes_atm t u"
  shows "size t \<le> size u"
proof -
  from assms obtain \<sigma> where "t \<cdot>a \<sigma> = u"
    by (auto simp: generalizes_atm_def)
  thus ?thesis
  proof (induction t arbitrary: u)
    case (Var x)
    then show ?case
      by (cases u) simp_all
  next
    case (Fun f args)
    from Fun.prems show ?case
      by (auto elim: Fun.IH intro!: size_list_pointwise)
  qed
qed

lemma size_term_le_size_term_if_generalizes_atm:
  assumes "generalizes_atm t u" and "m \<le> n"
  shows "size_term (\<lambda>_. n) (\<lambda>_. m) t \<le> size_term (\<lambda>_. n) (\<lambda>_. m) u"
proof -
  from assms(1) obtain \<sigma> where "t \<cdot>a \<sigma> = u"
    by (auto simp: generalizes_atm_def)
  thus ?thesis
  proof (induction t arbitrary: u)
    case (Var x)
    with assms(2) show ?case
      by (cases u) simp_all
  next
    case (Fun f args)
    from Fun.prems show ?case
      by (auto elim: Fun.IH intro!: size_list_pointwise)
  qed
qed

lemma size_term_lt_size_term_if_generalizes_atm:
  assumes
    generalizes: "t \<cdot>a \<sigma> = u" and
    not_renaming: "\<exists>x \<in> vars_term t. \<not> is_Var (\<sigma> x)" and
    "m < n"
  defines "size_term' \<equiv> size_term (\<lambda>_. n) (\<lambda>_. m)"
  shows "size_term' t < size_term' u"
  using generalizes not_renaming
proof (induction t arbitrary: u)
  case (Var x)
  with assms(3) show ?case
    by (cases u) (simp_all add: size_term'_def)
next
  case (Fun f args)
  from Fun.prems have u_def: "u = Fun f (map (\<lambda>t. t \<cdot>a \<sigma>) args)"
    by simp

  from Fun.prems obtain arg where
    arg_in: "arg \<in> set args" and bex_arg_is_Fun: "\<exists>x\<in>vars_term arg. is_Fun (\<sigma> x)"
    by auto

  from arg_in obtain args0 args1 where args_def: "args = args0 @ arg # args1"
    by (auto simp: in_set_conv_decomp)

  have "size_term' (Fun f args) = 1 + n + size_list size_term' args"
    by (simp add: size_term'_def)
  also have "\<dots> = 2 + n + size_list size_term' args0 + size_term' arg + size_list size_term' args1"
    by (simp add: args_def)
  also have "\<dots> \<le> 2 + n + size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) args0 + size_term' arg +
      size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) args1"
  proof -
    have "size_list size_term' xs \<le> size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) xs" for xs
    proof (rule size_list_pointwise)
      fix x
      from \<open>m < n\<close> show "size_term' x \<le> (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) x"
        unfolding size_term'_def comp_def
        by (auto simp: generalizes_atm_def intro!: size_term_le_size_term_if_generalizes_atm)
    qed
    thus ?thesis
      by (simp add: add_le_mono)
  qed
  also have "\<dots> < 2 + n + size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) args0 + size_term' (arg \<cdot>a \<sigma>) +
      size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) args1"
    using Fun.IH[OF arg_in refl bex_arg_is_Fun] by simp
  also have "\<dots> = 1 + n + size_list (size_term' \<circ> (\<lambda>t. t \<cdot>a \<sigma>)) args"
    by (simp add: args_def comp_def)
  also have "\<dots> = size_term' u"
    by (simp add: u_def size_term'_def)
  finally show ?case
    by assumption
qed


adhoc_overloading
  bind FSet.fbind

term set_Cons
term Set.bind

definition fset_Cons where
  "fset_Cons A AS = do {
    a \<leftarrow> A;
    as \<leftarrow> AS;
    {| a # as |}
  }"

lemma mem_fset_fset_ConsD:
  assumes xs_in: "xs \<in> fset (fset_Cons A AS)"
  shows "\<exists>a \<in> fset A. \<exists>as \<in> fset AS. xs = a # as"
proof -
  from xs_in have "xs \<in> fset A \<bind> (\<lambda>x. fset AS \<bind> (\<lambda>xs'. {x # xs'}))"
    unfolding fset_Cons_def fbind.rep_eq comp_def id_apply finsert.rep_eq bot_fset.rep_eq
    by simp

  then show ?thesis
    unfolding member_bind UN_iff
    by simp
qed

term listset

primrec listfset :: "'a fset list \<Rightarrow> 'a list fset" where
  "listfset [] = {|[]|}" |
  "listfset (A # As) = fset_Cons A (listfset As)"

(* lemma
  fixes xs
  assumes "xs \<in> fset (listfset (A # As))"
  shows "\<exists>x \<in> fset A. \<exists>xs' \<in> fset (listfset As). xs = x # xs'"
  using assms
proof (induction  *)


lemma ball_fset_listfset_length_conv: "\<forall>xs \<in> fset (listfset As). length xs = length As"
proof (induction As)
  case Nil
  show ?case
    by simp
next
  case (Cons A As)
  show ?case
  proof (rule ballI)
    fix xs assume "xs \<in> fset (listfset (A # As))"
    then obtain x xs' where "xs = x # xs' \<and> x \<in> fset A \<and> xs' \<in> fset (listfset As)"
      unfolding listfset.simps
      by (auto dest: mem_fset_fset_ConsD)
    thus "length xs = length (A # As)"
      using Cons.IH
      by simp
  qed
qed

term ffUnion
find_consts "'a fset set \<Rightarrow> _"

term "foldr"

primrec generalizations :: "('a, 'b) Term.term \<Rightarrow> ('a, 'b) Term.term fset" where
  "generalizations (Var _) = {||}" |
  "generalizations (Fun f xs) =
    (let T = (Fun f) |`| listfset (map generalizations xs) in
     finsert (Var (SOME x. x \<notin> (\<Union>t \<in> fset T. vars_term t))) T)"

lemma bex_not_member_if_infinite: "infinite A \<Longrightarrow> finite B \<Longrightarrow> \<exists>x\<in>A. x \<notin> B"
  by (meson rev_finite_subset subsetI)

lemma
  fixes w :: "('f, 'v) term"
  assumes inf_vars: "infinite (UNIV :: 'v set)"
  shows "pairwise (\<lambda>t u. vars_term t \<inter> vars_term u = {}) (fset (generalizations w))"
  unfolding pairwise_def
proof (intro ballI impI)
  fix t u assume "t \<in> fset (generalizations w)" and "u \<in> fset (generalizations w)" and "t \<noteq> u"
  then show "vars_term t \<inter> vars_term u = {}"
  proof (induction w arbitrary: t u)
    case (Var x)
    thus ?case
      by simp
  next
    case (Fun f xs)
    let ?T = "fset (Fun f |`| listfset (map generalizations xs))"
    let ?var = "Var (SOME x. x \<notin> \<Union> (vars_term ` ?T))"

    have fin_UN_vars_image_T:"finite (\<Union> (vars_term ` ?T))"
      by simp
    
    from Fun.prems show ?case
      unfolding generalizations.simps Let_def finsert.rep_eq insert_iff
    proof (elim disjE)
      assume t_eq: "t = ?var" and u_eq: "u = ?var"
      thus ?thesis
        using \<open>t \<noteq> u\<close> by simp
    next
      assume "t = ?var" and u_in: "u \<in> ?T"
      then obtain y where "t = Var y \<and> y \<notin> \<Union> (vars_term ` ?T)"
        using bex_not_member_if_infinite[OF inf_vars fin_UN_vars_image_T]
        by (metis (no_types, lifting) someI_ex)
      with u_in show ?thesis
        by auto
    next
      assume t_in: "t \<in> ?T" and "u = ?var"
      then obtain y where "u = Var y \<and> y \<notin> \<Union> (vars_term ` ?T)"
        using bex_not_member_if_infinite[OF inf_vars fin_UN_vars_image_T]
        by (metis (no_types, lifting) someI_ex)
      with t_in show ?thesis
        by auto
    next
      assume t_in: "t \<in> ?T" and u_in: "u \<in> ?T"
      
      from t_in obtain xs\<^sub>t where
        t_def: "t = Fun f xs\<^sub>t" and "xs\<^sub>t |\<in>| listfset (map generalizations xs)"
        by (meson fimageE notin_fset)

      from u_in obtain xs\<^sub>u where
        u_def: "u = Fun f xs\<^sub>u" and "xs\<^sub>u |\<in>| listfset (map generalizations xs)"
        by (meson fimageE notin_fset)

      show ?thesis
        unfolding t_def u_def
        unfolding term.set
        unfolding Int_UN_distrib2 Union_empty_conv Set.ball_simps
      proof (intro ballI)
        fix x y assume "x \<in> set xs\<^sub>t" and "y \<in> set xs\<^sub>u"
        then show "vars_term x \<inter> vars_term y = {}"
          using Fun.IH
          sorry
      qed
    qed
  qed
  oops

lemma
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. P x y"
  shows "\<exists>ys. list_all2 P xs ys"
  using assms by (induction xs) auto

find_consts name: "com" "('a \<Rightarrow> 'a \<Rightarrow> _) \<Rightarrow> bool"
print_locale monoid
print_locale monoid_mult

find_consts "(_, _) subst list"

term prod_list
term monoid_list
term "fold (\<odot>) xs Var"
term "(\<cdot>)"
term foldl

lemma subst_atm_foldl_comp: "t \<cdot>a foldl (\<odot>) \<sigma>_def \<sigma>s = t \<cdot>a \<sigma>_def \<cdot>a foldl (\<odot>) Var \<sigma>s"
proof (induction \<sigma>s arbitrary: t \<sigma>_def)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  show ?case
    unfolding foldl.simps comp_def
    unfolding Cons.IH[of t]
    unfolding Cons.IH[of "t \<cdot>a \<sigma>_def"]
    by simp
qed

lemma subst_atm_fold_comp_Var_ident:
  assumes "\<forall>\<sigma> \<in> set \<sigma>s. t \<cdot>a \<sigma> = t"
  shows "t \<cdot>a foldl (\<odot>) Var \<sigma>s = t"
  using assms
proof (induction \<sigma>s arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  from Cons.prems have "t \<cdot>a \<sigma> = t"
    by simp

  have "t \<cdot>a foldl (\<odot>) Var (\<sigma> # \<sigma>s) = t \<cdot>a foldl (\<odot>) \<sigma> \<sigma>s"
    by simp
  also have "\<dots> = t \<cdot>a \<sigma> \<cdot>a foldl (\<odot>) Var \<sigma>s"
    unfolding subst_atm_foldl_comp[of t] by simp
  also have "\<dots> = t \<cdot>a foldl (\<odot>) Var \<sigma>s"
    using Cons.prems by simp
  also have "\<dots> = t"
    using Cons.prems by (simp add: Cons.IH)
  finally show ?case
    by assumption
qed

lemma foldl_comp_Var_is_merged_subst:
  fixes ts :: "('f, 'v) term list" and \<sigma>s :: "('f, 'v) subst list"
  assumes
    same_length: "length ts = length \<sigma>s" and
    range_vars_subset: "\<forall>\<sigma> \<in> set \<sigma>s. range_vars \<sigma> \<subseteq> A" and
    min_domains: "list_all2 (\<lambda>t \<sigma>. subst_domain \<sigma> \<subseteq> vars_term t) ts \<sigma>s" and
    disj_vars_wrt_A: "\<forall>t \<in> set ts. vars_term t \<inter> A = {}" and
    disj_vars: "pairwise (\<lambda>t1 t2. vars_term t1 \<inter> vars_term t2 = {}) (set ts)" and
    dist_terms: "distinct ts"
  shows "list_all2 (\<lambda>x \<sigma>\<^sub>x. x \<cdot>a \<sigma>\<^sub>x = x \<cdot>a foldl (\<odot>) Var \<sigma>s) ts \<sigma>s"
  using assms
proof (induction ts \<sigma>s rule: list_induct2)
  case Nil
  show ?case
    by simp
next
  case (Cons t ts \<sigma>\<^sub>t \<sigma>s)
  show ?case
    unfolding foldl.simps id_subst_comp_subst
  proof (rule list.rel_intros)
    have vars_t_\<sigma>\<^sub>t_disj: "vars_term (t \<cdot>a \<sigma>\<^sub>t) \<inter> subst_domain \<sigma>' = {}"
      if \<sigma>'_in: "\<sigma>' \<in> set \<sigma>s"
      for \<sigma>'
    proof -
      from \<sigma>'_in obtain n where "n < length \<sigma>s" and \<sigma>'_def: "\<sigma>' = \<sigma>s ! n"
        by (auto simp: in_set_conv_nth)

      define u where
        "u = ts ! n"
      hence "u \<in> set ts"
        by (simp add: Cons.hyps \<open>n < length \<sigma>s\<close>)
      hence "t \<noteq> u"
        using Cons.prems(5) by fastforce
      hence vars_disj_t_u: "vars_term t \<inter> vars_term u = {}"
        using Cons.prems(4)
        by (meson \<open>u \<in> set ts\<close> list.set_intros(1) pairwiseD set_subset_Cons subsetD)
      
      have dom_\<sigma>': "subst_domain \<sigma>' \<subseteq> vars_term u"
        using \<sigma>'_def u_def \<open>length ts = length \<sigma>s\<close> \<open>n < length \<sigma>s\<close>
        using Cons.prems(2) list_all2_nthD2 by fastforce

      have "vars_term (t \<cdot>a \<sigma>\<^sub>t) \<subseteq> vars_term t \<union> A"
        by (meson Cons.prems(1) Diff_subset_conv list.set_intros(1) subset_trans
            vars_subst_term_subset_weak)
      moreover have "vars_term t \<inter> subst_domain \<sigma>' = {}"
        using dom_\<sigma>' vars_disj_t_u by auto
      moreover have "A \<inter> subst_domain \<sigma>' = {}"
        using Cons.prems(3) \<open>u \<in> set ts\<close> dom_\<sigma>' by fastforce
      ultimately show ?thesis
        by auto
    qed

    show "t \<cdot>a \<sigma>\<^sub>t = t \<cdot>a foldl (\<odot>) \<sigma>\<^sub>t \<sigma>s"
      unfolding subst_atm_foldl_comp[of t]
      using subst_atm_fold_comp_Var_ident[of \<sigma>s "t \<cdot>a \<sigma>\<^sub>t", symmetric]
      by (simp add: subst_apply_term_ident vars_t_\<sigma>\<^sub>t_disj)
  next
    have "u \<cdot>a \<sigma>\<^sub>u = u \<cdot>a foldl (\<odot>) \<sigma>\<^sub>t \<sigma>s"
      if u_\<sigma>\<^sub>u_in: "(u, \<sigma>\<^sub>u) \<in> set (zip ts \<sigma>s)"
      for u \<sigma>\<^sub>u
    proof -
      from u_\<sigma>\<^sub>u_in have "u \<in> set ts"
        by (meson in_set_zipE)
      moreover hence "t \<noteq> u"
        using Cons.prems(5) by fastforce
      ultimately have "vars_term u \<inter> vars_term t = {}"
        using Cons.prems(4) by (simp add: pairwise_def)
      moreover have "subst_domain \<sigma>\<^sub>t \<subseteq> vars_term t"
        using Cons.prems by simp
      ultimately have "vars_term u \<inter> subst_domain \<sigma>\<^sub>t = {}"
        by auto
      hence "u \<cdot>a \<sigma>\<^sub>t = u"
        by (rule subst_apply_term_ident)

      have IH: "list_all2 (\<lambda>x \<sigma>\<^sub>x. x \<cdot>a \<sigma>\<^sub>x = x \<cdot>a foldl (\<odot>) Var \<sigma>s) ts \<sigma>s"
        using Cons.prems by (simp_all add: pairwise_insert Cons.IH)

      show ?thesis
        unfolding subst_atm_foldl_comp[of _ \<sigma>\<^sub>t \<sigma>s] \<open>u \<cdot>a \<sigma>\<^sub>t = u\<close>
        using IH[unfolded list_all2_iff] u_\<sigma>\<^sub>u_in
        by auto
    qed
    thus "list_all2 (\<lambda>x \<sigma>\<^sub>x. x \<cdot>a \<sigma>\<^sub>x = x \<cdot>a foldl (\<odot>) \<sigma>\<^sub>t \<sigma>s) ts \<sigma>s"
      using \<open>length ts = length \<sigma>s\<close>
      by (auto simp add: list_all2_iff)
  qed
qed

lemma subst_domain_foldl_compose:
  "subst_domain (foldl (\<odot>) \<sigma>\<^sub>0 \<sigma>s) \<subseteq> subst_domain \<sigma>\<^sub>0 \<union> \<Union>(subst_domain ` set \<sigma>s)"
proof (induction \<sigma>s arbitrary: \<sigma>\<^sub>0)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  show ?case
    apply simp
    using Cons.IH[of "\<sigma>\<^sub>0 \<odot> \<sigma>"] subst_domain_compose
    by fastforce
qed

lemma range_vars_fold_compose:
  "range_vars (foldl (\<odot>) \<sigma>\<^sub>0 \<sigma>s) \<subseteq> range_vars \<sigma>\<^sub>0 \<union> \<Union>(range_vars ` set \<sigma>s)"
proof (induction \<sigma>s arbitrary: \<sigma>\<^sub>0)
  case Nil
  show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  show ?case
    apply simp
    using Cons.IH[of "\<sigma>\<^sub>0 \<odot> \<sigma>"] range_vars_subst_compose_subset
    by force
qed
  

lemma strong_generalizes_if_fmember_generalizations:
  fixes t u :: "('f, 'v) term"
  assumes "infinite (UNIV :: 'v set)"
  shows "t |\<in>| generalizations u \<Longrightarrow> \<exists>\<sigma>. t \<cdot>a \<sigma> = u \<and> subst_domain \<sigma> \<subseteq> vars_term t \<and>
    range_vars \<sigma> \<subseteq> vars_term u"
proof (induction u arbitrary: t)
  case (Var x)
  hence False by simp
  thus ?case ..
next
  case (Fun f xs)
  let ?XS = "Fun f |`| listfset (map generalizations xs)"
  have "finite (\<Union>t \<in> fset ?XS. vars_term t)"
    by simp
  with Fun.prems obtain y where "t = Var y \<and> y \<notin> (\<Union>t \<in> fset ?XS. vars_term t) \<or> t |\<in>| ?XS"
    unfolding generalizations.simps Let_def finsert_iff
    by (metis (mono_tags, lifting) assms bex_not_member_if_infinite someI_ex)
  then show ?case
  proof (elim disjE exE conjE)
    fix y assume "t = Var y" and "y \<notin> (\<Union>t \<in> fset ?XS. vars_term t)"
    show "\<exists>\<sigma>. t \<cdot>a \<sigma> = Fun f xs \<and> subst_domain \<sigma> \<subseteq> vars_term t \<and>
        range_vars \<sigma> \<subseteq> vars_term (Fun f xs)"
    proof (intro exI[of _ "Var(y := Fun f xs)"] conjI)
      show "t \<cdot>a Var(y := Fun f xs) = Fun f xs"
        by (simp add: \<open>t = Var y\<close>)
    next
      show "subst_domain (Var(y := Fun f xs)) \<subseteq> vars_term t"
        by (simp add: \<open>t = Var y\<close> subst_domain_def)
    next
      show "range_vars (Var(y := Fun f xs)) \<subseteq> vars_term (Fun f xs)"
        by (simp add: range_vars_def subst_domain_def)
    qed
  next
    assume "t |\<in>| Fun f |`| listfset (map generalizations xs)"
    then obtain xs' where
      t_def: "t = Fun f xs'" and xs'_in: "xs' |\<in>| listfset (map generalizations xs)"
      by auto

    have "length xs' = length xs"
      using xs'_in[unfolded fmember_iff_member_fset]
      by (simp add: ball_fset_listfset_length_conv[rule_format])

    have ball_fmember_generalizations:
      "\<forall>n < length xs. xs' ! n |\<in>| generalizations (xs ! n)"
      using xs'_in[unfolded fmember_iff_member_fset]
    proof (induction xs arbitrary: xs')
      case Nil
      show ?case by simp
    next
      case (Cons x xs)
      from Cons.prems have "xs' \<in>
        fset (fset_Cons (generalizations x) (listfset (map generalizations xs)))"
        unfolding list.map listfset.simps
        by simp
      then obtain a as where
        a_in: "a \<in> fset (generalizations x)" and
        as_in: "as \<in> fset (listfset (map generalizations xs))" and
        "xs' = a # as"
        by (auto dest: mem_fset_fset_ConsD)

      show ?case
        unfolding \<open>xs' = a # as\<close>
        using a_in Cons.IH[OF as_in]
        by (metis One_nat_def diff_less length_Cons less_Suc_eq less_imp_diff_less linorder_neqE_nat
            not_less0 notin_fset nth_Cons')
    qed
    with \<open>length xs' = length xs\<close> have "\<exists>\<sigma>s. length \<sigma>s = length xs \<and>
      (\<forall>n < length xs. (xs' ! n) \<cdot>a (\<sigma>s ! n) = xs ! n \<and>
      subst_domain (\<sigma>s ! n) \<subseteq> vars_term (xs' ! n) \<and>
      range_vars (\<sigma>s ! n) \<subseteq> vars_term (Fun f xs))"
      using Fun.IH[unfolded generalizes_atm_def]
    proof (induction xs' xs rule: list_induct2)
      case Nil
      show ?case
        by simp
    next
      case (Cons x xs y ys)

      from Cons.prems(1) have
        "x |\<in>| generalizations y" and
        ball_fmember_gen:"\<forall>n<length ys. xs ! n |\<in>| generalizations (ys ! n)"
        by auto

      with Cons.prems(2)[of y x, simplified] obtain \<sigma> where
        x_\<sigma>: "x \<cdot>a \<sigma> = y" and dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_term x" and
        range_\<sigma>: "range_vars \<sigma> \<subseteq> vars_term y"
        by auto
      
      moreover from Cons.prems(2) obtain \<sigma>s where
        "length \<sigma>s = length ys" and ball_ys: "\<forall>n<length ys. xs ! n \<cdot>a \<sigma>s ! n = ys ! n \<and>
          subst_domain (\<sigma>s ! n) \<subseteq> vars_term (xs ! n) \<and> range_vars (\<sigma>s ! n) \<subseteq> vars_term (Fun f ys)"
        using Cons.IH[OF ball_fmember_gen] by auto
      
      show ?case
      proof (intro exI[of _ "\<sigma> # \<sigma>s"] conjI allI)
        show "length (\<sigma> # \<sigma>s) = length (y # ys)"
          using \<open>length \<sigma>s = length ys\<close> by simp
      next
        fix n show "n < length (y # ys) \<longrightarrow>
          (x # xs) ! n \<cdot>a (\<sigma> # \<sigma>s) ! n = (y # ys) ! n \<and>
          subst_domain ((\<sigma> # \<sigma>s) ! n) \<subseteq> vars_term ((x # xs) ! n) \<and>
          range_vars ((\<sigma> # \<sigma>s) ! n) \<subseteq> vars_term (Fun f (y # ys)) "
          using x_\<sigma> dom_\<sigma> range_\<sigma> ball_ys
          by (cases n) auto
      qed
    qed
    then obtain \<sigma>s where "length \<sigma>s = length xs" and
      ball_subst_eq: "\<forall>n<length xs. xs' ! n \<cdot>a \<sigma>s ! n = xs ! n \<and>
        subst_domain (\<sigma>s ! n) \<subseteq> vars_term (xs' ! n) \<and>
        range_vars (\<sigma>s ! n) \<subseteq> vars_term (Fun f xs)"
      by auto

    have "length xs' = length \<sigma>s"
      using \<open>length \<sigma>s = length xs\<close> \<open>length xs' = length xs\<close> by simp

    have ball_\<sigma>s_range_vars: "\<forall>\<sigma>\<in>set \<sigma>s. range_vars \<sigma> \<subseteq> vars_term (Fun f xs)"
      using ball_subst_eq
      by (metis \<open>length \<sigma>s = length xs\<close> in_set_conv_nth)

    have "list_all2 (\<lambda>x \<sigma>\<^sub>x. x \<cdot>a \<sigma>\<^sub>x = x \<cdot>a foldl (\<odot>) Var \<sigma>s) xs' \<sigma>s"
    proof (rule foldl_comp_Var_is_merged_subst[of xs' \<sigma>s])
      show "length xs' = length \<sigma>s"
        by (rule \<open>length xs' = length \<sigma>s\<close>)
    next
      show "\<forall>\<sigma>\<in>set \<sigma>s. range_vars \<sigma> \<subseteq> vars_term (Fun f xs)"
        by (rule ball_\<sigma>s_range_vars)
    next
      show "list_all2 (\<lambda>t \<sigma>. subst_domain \<sigma> \<subseteq> vars_term t) xs' \<sigma>s"
        using ball_subst_eq
        by (metis \<open>length xs' = length \<sigma>s\<close> \<open>length xs' = length xs\<close> list_all2_all_nthI)
    next
      show "\<forall>t\<in>set xs'. vars_term t \<inter> vars_term (Fun f xs) = {}"
        sorry
    next
      show "pairwise (\<lambda>t1 t2. vars_term t1 \<inter> vars_term t2 = {}) (set xs')"
        sorry
    next
      show "distinct xs'"
        sorry
    qed

    show "\<exists>\<sigma>. t \<cdot>a \<sigma> = Fun f xs \<and> subst_domain \<sigma> \<subseteq> vars_term t \<and>
        range_vars \<sigma> \<subseteq> vars_term (Fun f xs)"
      unfolding t_def generalizes_atm_def subst_apply_term.simps term.inject
    proof (intro exI conjI)
      show "map (\<lambda>t. t \<cdot>a foldl (\<odot>) Var \<sigma>s) xs' = xs"
        using ball_subst_eq \<open>length xs' = length xs\<close>
          \<open>list_all2 (\<lambda>x \<sigma>\<^sub>x. x \<cdot>a \<sigma>\<^sub>x = x \<cdot>a foldl (\<odot>) Var \<sigma>s) xs' \<sigma>s\<close>
        by (smt (verit, del_insts) length_map list_all2_conv_all_nth list_eq_iff_nth_eq nth_map)
    next
      have "subst_domain (foldl (\<odot>) Var \<sigma>s) \<subseteq> \<Union> (subst_domain ` set \<sigma>s)"
        by (rule subst_domain_foldl_compose[of Var, simplified])
      also have "\<dots> \<subseteq> \<Union> (vars_term ` set xs')"
      using ball_subst_eq
      by (smt (verit, best) \<open>length \<sigma>s = length xs\<close> \<open>length xs' = length xs\<close>
          complete_lattice_class.Sup_mono image_iff in_set_conv_nth)
      also have "\<dots> = vars_term (Fun f xs')"
        by simp
      finally show "subst_domain (foldl (\<odot>) Var \<sigma>s) \<subseteq> vars_term (Fun f xs')"
        by assumption
    next
      have "range_vars (foldl (\<odot>) Var \<sigma>s) \<subseteq> \<Union> (range_vars ` set \<sigma>s)"
        by (rule range_vars_fold_compose[of Var, simplified])
      also have "\<dots> \<subseteq> vars_term (Fun f xs)"
        using ball_\<sigma>s_range_vars
        by blast
      finally show "range_vars (foldl (\<odot>) Var \<sigma>s) \<subseteq> vars_term (Fun f xs)"
        by assumption
    qed simp
  qed
qed

lemma generalizes_atm_if_fmember_generalizations:
  fixes t u :: "('f, 'v) term"
  assumes "infinite (UNIV :: 'v set)"
  shows "t |\<in>| generalizations u \<Longrightarrow> generalizes_atm t u"
  by (auto simp: generalizes_atm_def dest: strong_generalizes_if_fmember_generalizations[OF assms])

lemma renamed_fmember_generalizations_if_generalizes_atm:
  fixes t u :: "('f, 'v) term"
  assumes "infinite (UNIV :: 'v set)" and "generalizes_atm t u"
  shows "\<exists>\<rho>. is_renaming \<rho> \<and> t \<cdot>a \<rho> |\<in>| generalizations u"
  unfolding generalizes_atm_def
  sorry

find_theorems name: "Finite_Set" "\<exists>B. _"

find_consts "'a set list \<Rightarrow> 'a list set"

lemma
  fixes u :: "('f, 'v) term"
  assumes "infinite (UNIV :: 'v set)"
  shows "\<exists>T. finite T \<and> (\<forall>w. generalizes_atm w u \<longleftrightarrow> (\<exists>t \<in> T. generalizes_atm t w))"
  thm size_le_size_if_generalizes_atm
proof (intro exI conjI allI)
  show "finite (fset (generalizations u))"
    by simp
next
  fix w
  show "generalizes_atm w u = (\<exists>t\<in>fset (generalizations u). generalizes_atm t w)"
  using renamed_fmember_generalizations_if_generalizes_atm
    generalizes_atm_if_fmember_generalizations
  by (metis assms fempty_iff generalizations.simps(1) generalizes_atm_refl) 
qed

end

end