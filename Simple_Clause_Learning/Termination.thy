theory Termination
  imports
    Simple_Clause_Learning
begin


section \<open>Extra Lemmas\<close>


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


section \<open>Termination\<close>

context scl begin

definition ground_lits_of_lit where
  "ground_lits_of_lit L = {L \<cdot>l \<gamma> | \<gamma> . is_ground_lit (L \<cdot>l \<gamma>)}"

(* fun \<M> :: "_ \<Rightarrow> _ \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) Term.term literal set" where
  "\<M> N \<beta> (\<Gamma>, U, D) =
    {L \<in> \<Union>(ground_lits_of_lit ` \<Union>(set_mset ` fset N)). atm_of L \<prec>\<^sub>B \<beta>} - fst ` set \<Gamma>" *)

definition \<M>_prop_deci :: "_ \<Rightarrow> _ \<Rightarrow> (_, _) Term.term literal fset" where
  "\<M>_prop_deci \<beta> \<Gamma> = Abs_fset {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>} |-| (fst |`| fset_of_list \<Gamma>)"

(* primrec \<M>_skip_fact_reso where
  "\<M>_skip_fact_reso [] C = []" |
  "\<M>_skip_fact_reso (Lc # \<Gamma>) C = count C (fst Lc) # \<M>_skip_fact_reso \<Gamma> C" *)

(*
fun \<M>_skip_fact_reso where
  "\<M>_skip_fact_reso [] C = []" |
  "\<M>_skip_fact_reso ((L, None) # \<Gamma>) C = 0 # \<M>_skip_fact_reso \<Gamma> C" |
  "\<M>_skip_fact_reso ((L\<^sub>\<gamma>, Some (D, L, \<gamma>)) # \<Gamma>) C =
    count C L\<^sub>\<gamma> # \<M>_skip_fact_reso \<Gamma> (C + repeat_mset (count C L\<^sub>\<gamma>) (D \<cdot> \<gamma>))"
*)

primrec \<M>_skip_fact_reso where
  "\<M>_skip_fact_reso [] C = []" |
  "\<M>_skip_fact_reso (Ln # \<Gamma>) C =
    (let n = count C (- (fst Ln)) in
    (case snd Ln of None \<Rightarrow> 0 | Some _ \<Rightarrow> n) #
      \<M>_skip_fact_reso \<Gamma> (C + (case snd Ln of None \<Rightarrow> {#} | Some (D, _, \<gamma>) \<Rightarrow> repeat_mset n (D \<cdot> \<gamma>))))"

lemma length_\<M>_skip_fact_reso[simp]: "length (\<M>_skip_fact_reso \<Gamma> C) = length \<Gamma>"
  by (induction \<Gamma> arbitrary: C) (simp_all add: Let_def)

find_consts "nat \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset"

definition \<M> :: "_ \<Rightarrow> _ \<Rightarrow> ('f, 'v) state \<Rightarrow> ('f, 'v) Term.term literal fset \<times> nat list" where
  "\<M> N \<beta> S =
    (case state_conflict S of
      None \<Rightarrow> (\<M>_prop_deci \<beta> (state_trail S), [])
    | Some (C, \<gamma>) \<Rightarrow> ({||}, \<M>_skip_fact_reso (state_trail S) (C \<cdot> \<gamma>)))"

term "lex_prodp (|\<subset>|) (List.lexordp (<))"
term "List.lexordp (<)"
find_consts "nat \<Rightarrow> nat \<Rightarrow> bool"

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

lemma
  fixes N \<beta>
  defines
    "scl_without_backtrack \<equiv> propagate N \<beta> \<squnion> decide N \<beta> \<squnion> conflict N \<beta> \<squnion> skip N \<beta> \<squnion>
      factorize N \<beta> \<squnion> resolve N \<beta>" and
    "invars \<equiv> \<lambda>S _. trail_atoms_lt \<beta> S \<and> trail_resolved_lits_pol S \<and> trail_lits_ground S \<and>
      trail_lits_from_clauses N S \<and> initial_lits_generalize_learned_trail_conflict N S \<and>
      conflict_disjoint_vars N S \<and> minimal_ground_closures S"
  shows "invars initial_state S'" and "wfP (scl_without_backtrack \<sqinter> invars)\<inverse>\<inverse>"
proof -
  show "invars initial_state S'"
    by (simp add: invars_def)
next
  show "wfP (scl_without_backtrack \<sqinter> invars)\<inverse>\<inverse>"
  proof (rule wfP_if_convertible_to_wfP)
    fix S S' :: "('f, 'v) state"
    assume "(scl_without_backtrack \<sqinter> invars)\<inverse>\<inverse> S S'"
    hence step: "scl_without_backtrack S' S" and invars: "invars S' S"
      by simp_all

    from invars have
      "trail_atoms_lt \<beta> S'" and
      "trail_resolved_lits_pol S'" and
      "trail_lits_ground S'" and
      "trail_lits_from_clauses N S'" and
      "initial_lits_generalize_learned_trail_conflict N S'" and
      "conflict_disjoint_vars N S'" and
      "minimal_ground_closures S'"
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

    let ?less = "lex_prodp (|\<subset>|) (\<lambda>x y. (x, y) \<in> List.lenlex {(x, y). x < y})"

    from step show "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
      unfolding scl_without_backtrack_def sup_apply sup_bool_def
    proof (elim disjE)
      assume "decide N \<beta> S' S"
      thus "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
      proof (cases N \<beta> S' S rule: decide.cases)
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
            using \<open>trail_atoms_lt \<beta> S'\<close>
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
      assume "propagate N \<beta> S' S"
      thus "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
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
              using \<open>trail_atoms_lt \<beta> S'\<close>
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
      assume "conflict N \<beta> S' S"
      thus "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
      proof (cases N \<beta> S' S rule: conflict.cases)
        case (conflictI D U \<gamma> \<Gamma> \<rho> \<gamma>\<^sub>\<rho>)
        have "\<And>L. L |\<in>| fst |`| fset_of_list \<Gamma> \<Longrightarrow> atm_of L \<prec>\<^sub>B \<beta>"
          using \<open>trail_atoms_lt \<beta> S'\<close>[unfolded conflictI(1,2) trail_atoms_lt_def, simplified]
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
      assume "skip N \<beta> S' S"
      thus "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
      proof (cases N \<beta> S' S rule: skip.cases)
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
      show "factorize N \<beta> S' S \<Longrightarrow> ?less (\<M> N \<beta> S) (\<M> N \<beta> S')" sorry
    next
      assume "resolve N \<beta> S' S"
      thus "?less (\<M> N \<beta> S) (\<M> N \<beta> S')"
      proof (cases N \<beta> S' S)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
        hence ren_\<rho>: "is_renaming \<rho>"
          using finite_fset is_renaming_renaming_wrt by blast

        from \<open>minimal_ground_closures S'\<close> have
          ground_conflict: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)" and
          ground_resolvant: "is_ground_cls (add_mset L C \<cdot> \<delta>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)" and
          dom_\<delta>: "subst_domain \<delta> \<subseteq> vars_cls (add_mset L C)"
          unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close>
          by (simp_all add: minimal_ground_closures_def trail_propagate_def)

        have vars_conflict_disj_vars_resolvant:
          "vars_cls (add_mset L' D) \<inter> vars_cls (add_mset L C) = {}"
          using \<open>conflict_disjoint_vars N S'\<close>
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
          using \<open>trail_resolved_lits_pol S'\<close>
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
    show "wfP (lex_prodp (|\<subset>|) (\<lambda>x y. (x, y) \<in> List.lenlex {(x :: nat, y :: nat). x < y}))"
      by (rule wfP_lex_prodp) (simp_all add: wfP_pfsubset wfP_wf_eq wf_less wf_lenlex)
  qed
qed


end