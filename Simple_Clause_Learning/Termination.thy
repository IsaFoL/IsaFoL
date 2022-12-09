theory Termination
  imports
    Simple_Clause_Learning
    Non_Redundancy
    "HOL-Library.Monad_Syntax"
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
    using totalp_on_lex_prodp[OF totalp_on_less totalp_on_less, of UNIV UNIV, simplified,
        THEN totalpD]
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

lemma wf_union_if_convertible_to_wf:
  fixes
    f :: "'a \<Rightarrow> 'b" and g :: "'a \<Rightarrow> 'c" and
    R S :: "('a \<times> 'a) set" and Q :: "('b \<times> 'b) set" and T :: "('c \<times> 'c) set"
  assumes
    "wf S"
    "wf Q"
    "\<And>x y. (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> Q"
    "\<And>x y. (x, y) \<in> S \<Longrightarrow> (f x, f y) \<in> Q \<or> f x = f y"
  shows "wf (R \<union> S)"
proof (rule wf_if_convertible_to_wf)
  show "wf (Q <*lex*> S)"
    by (rule wf_lex_prod[OF \<open>wf Q\<close> \<open>wf S\<close>])
next
  define h where
    "h \<equiv> \<lambda>z. (f z, z)"
  
  fix x y assume "(x, y) \<in> R \<union> S"
  with assms show "(h x, h y) \<in> Q <*lex*> S"
    unfolding h_def by fastforce
qed

lemma wfP_union_if_convertible_to_wfP:
  assumes
    "wfP S"
    "wfP Q"
    "\<And>x y. R x y \<Longrightarrow> Q (f x) (f y)"
    "\<And>x y. S x y \<Longrightarrow> Q (f x) (f y) \<or> f x = f y"
  shows "wfP (R \<squnion> S)"
  using assms by (rule wf_union_if_convertible_to_wf[to_pred])


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

lemma fminus_conv: "A |\<subset>| B \<longleftrightarrow> fset A \<subset> fset B \<and> finite (fset A) \<and> finite (fset B)"
  by (simp add: less_eq_fset.rep_eq less_le_not_le)


section \<open>Termination\<close>

context scl begin


subsection \<open>SCL without backtracking terminates\<close>

definition \<M>_prop_deci :: "_ \<Rightarrow> _ \<Rightarrow> (_, _) Term.term literal fset" where
  "\<M>_prop_deci \<beta> \<Gamma> = Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>} |-| (fst |`| fset_of_list \<Gamma>)"

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

definition \<M>
  :: "_ \<Rightarrow> _ \<Rightarrow> ('f, 'v) state \<Rightarrow> bool \<times> ('f, 'v) Term.term literal fset \<times> nat list \<times> nat" where
  "\<M> N \<beta> S =
    (case state_conflict S of
      None \<Rightarrow> (True, \<M>_prop_deci \<beta> (state_trail S), [], 0)
    | Some (C, \<gamma>) \<Rightarrow> (False, {||}, \<M>_skip_fact_reso (state_trail S) (C \<cdot> \<gamma>), size C))"

lemma scl_without_backtrack_terminates:
  fixes N \<beta>
  defines
    "scl_without_backtrack \<equiv> propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion>
      factorize N \<beta> \<squnion> resolve N \<beta>" and
    "invars \<equiv> trail_atoms_lt \<beta> \<sqinter> trail_resolved_lits_pol \<sqinter> trail_lits_ground \<sqinter>
      trail_lits_from_clauses N \<sqinter> initial_lits_generalize_learned_trail_conflict N \<sqinter>
      ground_closures"
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
        scl_preserves_ground_closures)
next
  let ?less =
    "lex_prodp ((<) :: bool \<Rightarrow> bool \<Rightarrow> bool)
      (lex_prodp (|\<subset>|)
        (lex_prodp (\<lambda>x y. (x, y) \<in> List.lenlex {(x :: _ :: wellorder, y). x < y})
          ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)))"

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
      "ground_closures S"
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
          then show "finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>) |\<subseteq>| Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>}"
            using finite_lits_less_B
            by (simp add: less_eq_fset.rep_eq Abs_fset_inverse fset_of_list.rep_eq)
        qed
        then show ?thesis
          unfolding decideI(1,2) decide_lit_def \<M>_def state_proj_simp option.case
          unfolding lex_prodp_def prod.sel by simp
      qed
    next
      assume "propagate N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: propagate.cases)
        case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

        have "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>"
        proof -
          have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
            unfolding \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
            by (auto simp: is_unifiers_def is_unifier_alt intro: subst_atm_of_eqI)
          hence "\<mu> \<odot> \<gamma> = \<gamma>"
            using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>[unfolded is_imgu_def, THEN conjunct2]
            by simp
          thus ?thesis
            by (metis subst_lit_comp_subst)
        qed

        have "\<M>_prop_deci \<beta> ((L \<cdot>l \<gamma>, Some (C\<^sub>0 \<cdot> \<mu>, L \<cdot>l \<mu>, \<gamma>)) # \<Gamma>) |\<subset>| \<M>_prop_deci \<beta> \<Gamma>"
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
          then show "finsert (L \<cdot>l \<gamma>) (fst |`| fset_of_list \<Gamma>) |\<subseteq>| Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>}"
            using finite_lits_less_B
            by (simp add: less_eq_fset.rep_eq fset_of_list.rep_eq Abs_fset_inverse)
        qed
        thus ?thesis
          unfolding propagateI(1,2) propagate_lit_def \<M>_def state_proj_simp option.case
          unfolding \<open>L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<close>
          unfolding lex_prodp_def prod.sel by simp
      qed
    next
      assume "conflict N \<beta> S S'"
      thus "?less (\<M> N \<beta> S') (\<M> N \<beta> S)"
      proof (cases N \<beta> S S' rule: conflict.cases)
        case (conflictI D U \<gamma> \<Gamma>)
        show ?thesis
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
        case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)

        have "is_unifier \<gamma> {atm_of L, atm_of L'}"
          using \<open>L \<cdot>l \<gamma> = L' \<cdot>l \<gamma>\<close>[THEN subst_atm_of_eqI]
          by (simp add: is_unifier_alt)
        hence "\<mu> \<odot> \<gamma> = \<gamma>"
          using \<open>is_imgu \<mu> {{atm_of L, atm_of L'}}\<close>
          by (simp add: is_imgu_def is_unifiers_def)

        have "add_mset L D \<cdot> \<mu> \<cdot> \<gamma> = add_mset L D \<cdot> \<gamma>"
          using \<open>\<mu> \<odot> \<gamma> = \<gamma>\<close>
          by (metis subst_cls_comp_subst)
        hence "(\<M>_skip_fact_reso \<Gamma> (add_mset L D \<cdot> \<mu> \<cdot> \<gamma>),
          \<M>_skip_fact_reso \<Gamma> (add_mset L' (add_mset L D) \<cdot> \<gamma>)) \<in> (lenlex {(x, y). x < y})\<^sup>="
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
        case (resolveI \<Gamma> \<Gamma>' K D \<gamma>\<^sub>D L \<gamma>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U)
        from \<open>ground_closures S\<close> have
          ground_conf: "is_ground_cls (add_mset L C \<cdot> \<gamma>\<^sub>C)" and
          ground_prop: "is_ground_cls (add_mset K D \<cdot> \<gamma>\<^sub>D)"
          unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close>
          by (simp_all add: ground_closures_def propagate_lit_def)
        hence
          "\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
          "\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
          using resolveI merge_of_renamed_groundings by metis+

        have "atm_of L \<cdot>a \<rho>\<^sub>C \<cdot>a \<gamma> = atm_of K \<cdot>a \<rho>\<^sub>D \<cdot>a \<gamma>"
          using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
            \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close>[rule_format, of L, simplified]
            \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>[rule_format, of K, simplified]
          by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
        hence "is_unifiers \<gamma> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"
          by (simp add: is_unifiers_def is_unifier_alt)
        hence "\<mu> \<odot> \<gamma> = \<gamma>"
          using \<open>is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}\<close>
          by (auto simp: is_imgu_def)
        hence "C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C" and "D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma> = D \<cdot> \<gamma>\<^sub>D"
          using \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close> \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>
          by (metis insert_iff same_on_lits_clause set_mset_add_mset_insert subst_cls_comp_subst
              subst_lit_comp_subst)+
        hence "(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C + D \<cdot> \<gamma>\<^sub>D"
          by (metis subst_cls_comp_subst subst_cls_union)

        have "L \<cdot>l \<gamma>\<^sub>C \<notin># D \<cdot> \<gamma>\<^sub>D"
          using \<open>trail_resolved_lits_pol S\<close> \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
          unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close>
          by (simp add: trail_resolved_lits_pol_def propagate_lit_def)

        have "(\<M>_skip_fact_reso \<Gamma> (C \<cdot> \<gamma>\<^sub>C + D \<cdot> \<gamma>\<^sub>D), \<M>_skip_fact_reso \<Gamma> (add_mset L C \<cdot> \<gamma>\<^sub>C)) \<in>
          lex {(x, y). x < y}"
          unfolding \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close> propagate_lit_def
          unfolding \<M>_skip_fact_reso.simps Let_def prod.sel option.case prod.case
          unfolding lex_conv mem_Collect_eq prod.case
          apply (rule conjI)
           apply simp
          apply (rule exI[of _ "[]"])
          apply simp
          using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
          apply simp
          unfolding count_eq_zero_iff
          by (rule \<open>L \<cdot>l \<gamma>\<^sub>C \<notin># D \<cdot> \<gamma>\<^sub>D\<close>)
        hence "(\<M>_skip_fact_reso \<Gamma> (C \<cdot> \<gamma>\<^sub>C + D \<cdot> \<gamma>\<^sub>D), \<M>_skip_fact_reso \<Gamma> (add_mset L C \<cdot> \<gamma>\<^sub>C)) \<in>
          lenlex {(x, y). x < y}"
          unfolding lenlex_conv by simp
        thus ?thesis
          unfolding lex_prodp_def resolveI(1,2)
          unfolding \<M>_def state_proj_simp option.case prod.case prod.sel
          unfolding \<open>(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C + D \<cdot> \<gamma>\<^sub>D\<close>
          by simp
      qed
    qed
  next
    show "wfP ?less"
    proof (intro wfP_lex_prodp)
      show "wfP ((<) :: bool \<Rightarrow> bool \<Rightarrow> bool)"
        by (simp add: wfPUNIVI)
    next
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


subsection \<open>Backtracking can only be done finitely often\<close>

thm learned_clauses_in_regular_runs_static_order

lemma ex_new_grounding_if_not_redudant:
  assumes not_redundant: "\<not> redundant R N C"
  shows "\<exists>C' \<in> grounding_of_cls C. C' \<notin> grounding_of_clss N"
proof -
  from not_redundant obtain C' I where
    C'_in: "C' \<in> grounding_of_cls C" and
    I_entails: "I \<TTurnstile>s {D \<in> grounding_of_clss N. R D C' \<or> D = C'}" and
    not_I_entails: "\<not> I \<TTurnstile> C'"
    using not_redundant[unfolded redundant_def ground_redundant_def, rule_format, simplified]
    by (auto simp: is_ground_cls_if_in_grounding_of_cls)

  from I_entails have "C' \<in> grounding_of_clss N \<Longrightarrow> I \<TTurnstile> C'"
    by (simp add: true_clss_def)
  with not_I_entails have "C' \<notin> grounding_of_clss N"
    by argo
  with C'_in show ?thesis
    by metis
qed

lemma
  assumes
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
    (\<exists>C' \<in> grounding_of_cls C. C' \<notin> grounding_of_clss (fset U))) \<and>
    grounding_of_clss (fset U) \<subset> grounding_of_clss (fset (state_learned Sn'))"
proof -
  from  learned_clauses_in_regular_runs_static_order[OF assms(1,2,3,4,5)]
  obtain C \<gamma> where
    conf_Sn: "state_conflict Sn = Some (C, \<gamma>)" and
    not_redundant: "\<not> redundant (\<subset>#) (fset N \<union> fset (state_learned S1)) C"
    by auto

  moreover have bex_grounding_not_in_U: "\<exists>C' \<in> grounding_of_cls C. C' \<notin> grounding_of_clss (fset U)"
    using ex_new_grounding_if_not_redudant[OF not_redundant, folded U_def]
    by (auto simp: grounding_of_clss_union)

  moreover have "grounding_of_clss (fset U) \<subset> grounding_of_clss (fset (state_learned Sn'))"
  proof -
    have "state_learned Sn = state_learned S1"
      using resolution
    proof (induction Sn rule: tranclp_induct)
      case (base y)
      thus ?case
        by (auto elim: skip.cases factorize.cases resolve.cases)
    next
      case (step y z)
      from step.hyps have "state_learned z = state_learned y"
        by (auto elim: skip.cases factorize.cases resolve.cases)
      with step.IH show ?case
        by simp
    qed

    moreover have "state_learned Sn' = finsert C (state_learned Sn)"
      using backtrack conf_Sn
      by (auto elim: backtrack.cases)

    ultimately have "state_learned Sn' = finsert C U"
      by (simp add: U_def)

    show ?thesis
      unfolding \<open>state_learned Sn' = finsert C U\<close>
    proof (rule Set.psubsetI)
      show "grounding_of_clss (fset U) \<subseteq> grounding_of_clss (fset (finsert C U))"
        by (simp add: grounding_of_clss_insert)
    next
      show "grounding_of_clss (fset U) \<noteq> grounding_of_clss (fset (finsert C U))"
        using bex_grounding_not_in_U by (auto simp: grounding_of_clss_insert)
    qed
  qed

  ultimately show ?thesis
    by simp
qed

definition fclss_no_dup :: "('f, 'v) Term.term \<Rightarrow> ('f, 'v) Term.term literal fset fset" where
  "fclss_no_dup \<beta> = fPow (Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>})"

lemma image_fset_fset_fPow_eq: "fset ` fset (fPow A) = Pow (fset A)"
proof (rule Set.equalityI)
  show "fset ` fset (fPow A) \<subseteq> Pow (fset A)"
    by (meson PowI fPowD image_subset_iff less_eq_fset.rep_eq notin_fset)
next
  show "Pow (fset A) \<subseteq> fset ` fset (fPow A)"
  proof (rule Set.subsetI)
    fix x assume "x \<in> Pow (fset A)"
    moreover hence "finite x"
      by (metis PowD finite_fset rev_finite_subset)
    ultimately show "x \<in> fset ` fset (fPow A)"
      unfolding image_iff
      by (metis PowD fPowI fset_cases less_eq_fset.rep_eq mem_Collect_eq notin_fset)
  qed
qed

lemma
  assumes "\<forall>L \<in># C. count C L = 1"
  shows "\<exists>C'. C = mset_set C'"
  using assms
  by (metis count_eq_zero_iff count_mset_set(1) count_mset_set(3) finite_set_mset multiset_eqI)

lemma fmember_fclss_no_dup_if:
  assumes "\<forall>L |\<in>| C. atm_of L \<prec>\<^sub>B \<beta>"
  shows "C |\<in>| fclss_no_dup \<beta>"
proof -
  show ?thesis
    unfolding fclss_no_dup_def fPow_iff
  proof (rule fsubsetI)
    fix K assume "K |\<in>| C"
    with assms show "K |\<in>| Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta>}"
      by (auto simp: fmember_iff_member_fset Abs_fset_inverse[simplified, OF finite_lits_less_B])
  qed
qed

definition \<M>_back :: " _ \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) Term.term literal fset fset" where
  "\<M>_back \<beta> S = Abs_fset (fset (fclss_no_dup \<beta>) -
    Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned S)))"

lemma \<M>_back_pfsubset_\<M>_back_after_regular_backtrack:
  assumes
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt" and

    invars: "ground_closures Sn" "trail_atoms_lt \<beta> Sn" "sound_state N \<beta> Sn"
      "ground_false_closures Sn"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))"
  shows "\<M>_back \<beta> Sn' |\<subset>| \<M>_back \<beta> Sn"
proof -
  obtain C \<gamma> where
    conf: "state_conflict Sn = Some (C, \<gamma>)" and
    set_conf_not_in_set_groundings:
      "set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset (state_learned S1))"
    using learned_clauses_in_regular_runs[OF assms(1,2,3,4,5)]
    by auto

  have 1: "state_learned Sn' = finsert C (state_learned Sn)"
    using backtrack conf by (auto elim: backtrack.cases)

  have 2: "state_learned Sn = state_learned S1"
    using resolution
  proof (induction Sn rule: tranclp_induct)
    case (base y)
    thus ?case
      by (auto elim: skip.cases factorize.cases resolve.cases)
  next
    case (step y z)
    from step.hyps(2) have "state_learned z = state_learned y"
      by (auto elim: skip.cases factorize.cases resolve.cases)
    with step.IH show ?case
      by simp
  qed

  have Diff_strict_subsetI: "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> A - B \<subset> A" for x A B
    by auto

  have "fset (fclss_no_dup \<beta>) - Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned Sn')) =
    fset (fclss_no_dup \<beta>) - Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned Sn)) -
      Abs_fset ` set_mset ` grounding_of_cls C"
    unfolding 1 finsert.rep_eq grounding_of_clss_insert image_Un
    by auto

  also have "\<dots> \<subset>
    fset (fclss_no_dup \<beta>) - Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned Sn))"
  proof (rule Diff_strict_subsetI)
    from invars(1) have "C \<cdot> \<gamma> \<in> grounding_of_cls C"
      unfolding ground_closures_def conf
      using grounding_of_cls_ground grounding_of_subst_cls_subset by blast
    thus "Abs_fset (set_mset (C \<cdot> \<gamma>)) \<in> Abs_fset ` set_mset ` grounding_of_cls C"
      by blast
  next
    have Abs_fset_in_image_Abs_fset_iff: "Abs_fset A \<in> Abs_fset ` AA \<longleftrightarrow> A \<in> AA"
      if "finite A \<and> (\<forall>B \<in> AA. finite B)"
      for A AA
      apply (rule iffI)
      using that
       apply (metis Abs_fset_inverse imageE mem_Collect_eq)
      using that
      by blast

    have "set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset (state_learned S1))"
      using set_conf_not_in_set_groundings
      by (auto simp: grounding_of_clss_union)
    then have "Abs_fset (set_mset (C \<cdot> \<gamma>)) \<notin>
      Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned Sn))"
      unfolding 2
      using Abs_fset_in_image_Abs_fset_iff
      by (metis finite_set_mset image_iff)

    moreover have "Abs_fset (set_mset (C \<cdot> \<gamma>)) \<in> fset (fclss_no_dup \<beta>)"
      unfolding fmember_iff_member_fset[symmetric]
    proof (intro fmember_fclss_no_dup_if fBallI)
      fix L assume "L |\<in>| Abs_fset (set_mset (C \<cdot> \<gamma>))"
      hence "L \<in># C \<cdot> \<gamma>"
        unfolding fmember_iff_member_fset
        by (metis fset_fset_mset fset_inverse)
      moreover have "trail_false_cls (state_trail Sn) (C \<cdot> \<gamma>)"
        using invars(4) conf by (auto simp: ground_false_closures_def)
      ultimately show "atm_of L \<prec>\<^sub>B \<beta>"
        using ball_less_B_if_trail_false_and_trail_atoms_lt[OF _ invars(2)]
        by metis
    qed

    ultimately show "Abs_fset (set_mset (C \<cdot> \<gamma>)) \<in> fset (fclss_no_dup \<beta>) -
      Abs_fset ` set_mset ` grounding_of_clss (fset (state_learned Sn))"
      by simp
  qed

  finally show ?thesis
    unfolding \<M>_back_def
    unfolding fminus_conv
    by (simp add: Abs_fset_inverse[simplified])
qed


subsection \<open>Regular SCL terminates\<close>

theorem regular_scl_terminates:
  fixes
    N :: "('f, 'v) Term.term clause fset" and
    \<beta> :: "('f, 'v) Term.term" and
    lt :: "('f, 'v) Term.term literal \<Rightarrow> ('f, 'v) Term.term literal \<Rightarrow> bool"
  defines
    "invars \<equiv> trail_atoms_lt \<beta> \<sqinter> trail_resolved_lits_pol \<sqinter> trail_lits_ground \<sqinter>
      trail_lits_from_clauses N \<sqinter> initial_lits_generalize_learned_trail_conflict N \<sqinter>
      ground_closures \<sqinter> ground_false_closures \<sqinter> sound_state N \<beta> \<sqinter>
      almost_no_conflict_with_trail N \<beta> \<sqinter>
      regular_conflict_resolution N \<beta>"
  assumes "transp lt"
  shows
    "wfP (\<lambda>S' S. regular_scl N \<beta> S S' \<and> invars S)" and
    "invars initial_state" and
    "\<And>S S'. regular_scl N \<beta> S S' \<Longrightarrow> invars S \<Longrightarrow> invars S'"
proof -
  show "invars initial_state"
    by (simp add: invars_def)
next
  note rea_to_scl = scl_if_reasonable
  note reg_to_rea = reasonable_if_regular
  note reg_to_scl = reg_to_rea[THEN rea_to_scl]
  fix S S'
  assume "regular_scl N \<beta> S S'"
  thus "invars S \<Longrightarrow> invars S'"
    unfolding invars_def
    using
      reg_to_scl[THEN scl_preserves_trail_atoms_lt]
      reg_to_scl[THEN scl_preserves_trail_resolved_lits_pol]
      reg_to_scl[THEN scl_preserves_trail_lits_ground]
      reg_to_scl[THEN scl_preserves_trail_lits_from_clauses]
      reg_to_scl[THEN scl_preserves_initial_lits_generalize_learned_trail_conflict]
      reg_to_scl[THEN scl_preserves_ground_closures]
      reg_to_scl[THEN scl_preserves_ground_false_closures]
      reg_to_scl[THEN scl_preserves_sound_state]
      regular_scl_preserves_almost_no_conflict_with_trail
      regular_scl_preserves_regular_conflict_resolution
    by simp
next
  have "(\<lambda>S' S. regular_scl N \<beta> S S' \<and> invars S) =
    (\<lambda>S' S. (backtrack N \<beta> S S' \<or> \<not> backtrack N \<beta> S S' \<and> regular_scl N \<beta> S S') \<and> invars S)"
    by (auto simp: fun_eq_iff)
  also have "\<dots> = (\<lambda>S' S. backtrack N \<beta> S S' \<and> invars S \<or>
    regular_scl N \<beta> S S' \<and> \<not> backtrack N \<beta> S S' \<and> invars S)"
    by auto
  also have "\<dots> = (\<lambda>S' S. backtrack N \<beta> S S' \<and> invars S) \<squnion>
    (\<lambda>S' S. regular_scl N \<beta> S S' \<and> \<not> backtrack N \<beta> S S' \<and> invars S)"
    by auto
  finally have *: "(\<lambda>S' S. regular_scl N \<beta> S S' \<and> invars S) =
    (\<lambda>S' S. backtrack N \<beta> S S' \<and> invars S) \<squnion>
    (\<lambda>S' S. regular_scl N \<beta> S S' \<and> \<not> backtrack N \<beta> S S' \<and> invars S)"
    by assumption

  show "wfP (\<lambda>S' S. regular_scl N \<beta> S S' \<and> invars S)"
    unfolding *
  proof (rule wfP_union_if_convertible_to_wfP; (elim conjE)?)
    show "wfP (\<lambda>S' S. regular_scl N \<beta> S S' \<and> \<not> backtrack N \<beta> S S' \<and> invars S)"
      using scl_without_backtrack_terminates(1)[of N \<beta>]
    proof (rule wfP_subset, unfold le_fun_def le_bool_def inf_fun_def, intro allI impI conjI; elim conjE)
      fix S' S
      assume "regular_scl N \<beta> S S'" and "\<not> backtrack N \<beta> S S'"
      thus "(propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>) S S'"
        by (auto simp: regular_scl_def reasonable_scl_def scl_def)
    next
      fix S' S assume "invars S"
      then show "trail_atoms_lt \<beta> S \<sqinter> trail_resolved_lits_pol S \<sqinter> trail_lits_ground S \<sqinter>
       trail_lits_from_clauses N S \<sqinter> initial_lits_generalize_learned_trail_conflict N S \<sqinter>
       ground_closures S"
        by (simp add: invars_def)
    qed
  next
    show "wfP (|\<subset>|)"
      by (rule wfP_pfsubset)
  next
    fix S S' assume "regular_scl N \<beta> S S'" and "\<not> backtrack N \<beta> S S'"
    hence "(propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>) S S'"
      by (auto simp add: regular_scl_def reasonable_scl_def scl_def)
    hence "state_learned S' = state_learned S"
      by (auto elim: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases)
    then show "\<M>_back \<beta> S' |\<subset>| \<M>_back \<beta> S \<or> \<M>_back \<beta> S' = \<M>_back \<beta> S"
      by (simp add: \<M>_back_def)
  next
    fix S S' assume backt: "backtrack N \<beta> S S'" and "invars S"
    
    moreover from \<open>invars S\<close> have "sound_state N \<beta> S"
      by (simp add: invars_def)

    moreover from \<open>invars S\<close> have "almost_no_conflict_with_trail N \<beta> S"
      by (simp add: invars_def)

    moreover from \<open>invars S\<close> have "regular_conflict_resolution N \<beta> S"
      by (simp add: invars_def)

    moreover from \<open>invars S\<close> have "ground_false_closures S"
      by (simp add: invars_def)

    ultimately obtain S0 S1 S2 S3 S4 where
      reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
      propa: "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
      confl: "conflict N \<beta> S1 S2" and
      facto: "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" and
      resol: "resolve N \<beta> S3 S4" and
      reg_res: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
      using before_regular_backtrack by blast

    show "\<M>_back \<beta> S' |\<subset>| \<M>_back \<beta> S"
    proof (rule \<M>_back_pfsubset_\<M>_back_after_regular_backtrack)
      show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
        using reg_run propa(2) by simp
    next
      show "conflict N \<beta> S1 S2"
        by (rule confl)
    next
      have "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S2 S3"
        using facto
        by (rule mono_rtranclp[rule_format, rotated]) simp
      also have "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S3 S4"
        using resol by auto
      finally show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S2 S"
        using reg_res by simp
    next
      show "backtrack N \<beta> S S'"
        by (rule backt)
    next
      show "transp lt"
        by (rule \<open>transp lt\<close>)
    next
      from \<open>invars S\<close> show "ground_closures S"
        by (simp add: invars_def)
    next
      from \<open>invars S\<close> show "trail_atoms_lt \<beta> S"
        by (simp add: invars_def)
    next
      show "sound_state N \<beta> S"
        by (rule \<open>sound_state N \<beta> S\<close>)
    next
      show "ground_false_closures S"
        by (rule \<open>ground_false_closures S\<close>)
    qed
  qed
qed

end

end