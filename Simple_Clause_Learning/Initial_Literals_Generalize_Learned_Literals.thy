theory Initial_Literals_Generalize_Learned_Literals
  imports Simple_Clause_Learning
begin

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3! (_/|:|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3? (_/|:|_)./ _)" [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBex A (\<lambda>x. P)"

global_interpretation comp_finsert_commute: comp_fun_commute finsert
proof (unfold_locales)
  show "\<And>y x. finsert y \<circ> finsert x = finsert x \<circ> finsert y"
    by auto
qed

definition fset_mset :: "'a multiset \<Rightarrow> 'a fset"
  where "fset_mset = fold_mset finsert {||}"

lemma fset_mset_mempty[simp]: "fset_mset {#} = {||}"
  by (simp add: fset_mset_def)

lemma fset_mset_add_mset[simp]: "fset_mset (add_mset x M) = finsert x (fset_mset M)"
  by (simp add: fset_mset_def)

lemma fset_fset_mset[simp]: "fset (fset_mset M) = set_mset M"
  by (induction M rule: multiset_induct) simp_all

lemma fmember_fset_mset_iff[simp]: "x |\<in>| fset_mset M \<longleftrightarrow> x \<in># M"
  by (induction M rule: multiset_induct) simp_all

lemma fBall_fset_mset_iff[simp]: "(\<forall>x |\<in>| fset_mset M. P x) \<longleftrightarrow> (\<forall>x \<in># M. P x)"
  by (simp add: fBall_def)

lemma fBex_fset_mset_iff[simp]: "(\<exists>x |\<in>| fset_mset M. P x) \<longleftrightarrow> (\<exists>x \<in># M. P x)"
  by (simp add: fBex_def)

lemma fmember_ffUnion_iff: "a |\<in>| ffUnion (f |`| A) \<longleftrightarrow> (\<exists>x |\<in>| A. a |\<in>| f x)"
  unfolding fmember.rep_eq ffUnion.rep_eq fBex.rep_eq by simp

lemma fBex_ffUnion_iff: "(\<exists>z |\<in>| ffUnion (f |`| A). P z) \<longleftrightarrow> (\<exists>x |\<in>| A. \<exists>z |\<in>| f x. P z)"
  unfolding fBex.rep_eq ffUnion.rep_eq fimage.rep_eq by blast

lemma fBall_ffUnion_iff: "(\<forall>z |\<in>| ffUnion (f |`| A). P z) \<longleftrightarrow> (\<forall>x |\<in>| A. \<forall>z |\<in>| f x. P z)"
  unfolding fBall.rep_eq ffUnion.rep_eq fimage.rep_eq by blast


context scl begin

definition clss_lits_generalize_clss_lits where
  "clss_lits_generalize_clss_lits N U \<longleftrightarrow>
    (\<forall>L |\<in>| ffUnion (fset_mset |`| U). \<exists>K |\<in>| ffUnion (fset_mset |`| N). generalizes_lit K L)"

lemma clss_lits_generalize_clss_lits_if_superset[simp]:
  assumes "N2 |\<subseteq>| N1"
  shows "clss_lits_generalize_clss_lits N1 N2"
proof (unfold clss_lits_generalize_clss_lits_def, rule fBallI)
  fix L
  assume L_in: "L |\<in>| ffUnion (fset_mset |`| N2)"
  show "\<exists>K |\<in>| ffUnion (fset_mset |`| N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro fBexI exI conjI)
    show "L |\<in>| ffUnion (fset_mset |`| N1)"
      using L_in \<open>N2 |\<subseteq>| N1\<close> by (meson ffunion_mono fimage_mono fin_mono)
  next
    show "L \<cdot>l Var = L"
      by simp
  qed
qed 

lemma clss_lits_generalize_clss_lits_refl[simp]: "clss_lits_generalize_clss_lits N N"
  using clss_lits_generalize_clss_lits_if_superset by simp

lemma clss_lits_generalize_clss_lits_insert: "clss_lits_generalize_clss_lits N (finsert C U) \<longleftrightarrow>
  clss_lits_generalize_clss_lits N {|C|} \<and> clss_lits_generalize_clss_lits N U"
  unfolding clss_lits_generalize_clss_lits_def
  by (simp add: fBall_funion)

lemma clss_lits_generalize_clss_lits_rename_clause:
  "C |\<in>| N \<Longrightarrow> finite M \<Longrightarrow> clss_lits_generalize_clss_lits N {|rename_clause M C|}"
  unfolding clss_lits_generalize_clss_lits_def
  apply (simp add: fBex_ffUnion_iff)
  by (metis (no_types, lifting) Melem_subst_cls fBexI generalizes_lit_def rename_clause_def)

lemma clss_lits_generalize_clss_lits_trans:
  assumes
    "clss_lits_generalize_clss_lits N1 N2" and
    "clss_lits_generalize_clss_lits N2 N3"
  shows "clss_lits_generalize_clss_lits N1 N3"
proof (unfold clss_lits_generalize_clss_lits_def, rule fBallI)
  fix L3
  assume "L3 |\<in>| ffUnion (fset_mset |`| N3)"
  then obtain L2 \<sigma>2 where "L2 |\<in>| ffUnion (fset_mset |`| N2)" and "L2 \<cdot>l \<sigma>2 = L3"
    using assms(2)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by blast
  then obtain L1 \<sigma>1 where "L1 |\<in>| ffUnion (fset_mset |`| N1)" and "L1 \<cdot>l \<sigma>1 = L2"
    using assms(1)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by blast
  
  thus "\<exists>K |\<in>| ffUnion (fset_mset |`| N1). generalizes_lit K L3"
    unfolding generalizes_lit_def
  proof (intro fBexI exI conjI)
    show "L1 \<cdot>l (\<sigma>1 \<odot> \<sigma>2) = L3"
      by (simp add: \<open>L1 \<cdot>l \<sigma>1 = L2\<close> \<open>L2 \<cdot>l \<sigma>2 = L3\<close>)
  qed simp_all
qed

definition initial_lits_generalized_learned_lits where
  "initial_lits_generalized_learned_lits N S \<longleftrightarrow>
    clss_lits_generalize_clss_lits N (state_learned S |\<union>| clss_of_trail (state_trail S) |\<union>|
      (case state_conflict S of None \<Rightarrow> {||} | Some (C, _) \<Rightarrow> {|C|}))"

lemma initial_lits_generalized_learned_lits_initial_state:
  "initial_lits_generalized_learned_lits N initial_state"
  unfolding initial_lits_generalized_learned_lits_def by simp

lemma propagate_initial_lits_generalized_learned_lits:
  "propagate N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: propagate.induct)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu> \<gamma>' \<rho> \<gamma>\<^sub>\<rho>')

  from propagateI.prems have
    N_superset_lits: "clss_lits_generalize_clss_lits N (U |\<union>| clss_of_trail \<Gamma>)"
    unfolding initial_lits_generalized_learned_lits_def by simp_all

  from propagateI.hyps have C_in: "C |\<in>| N |\<union>| U" by simp
  from propagateI.hyps have C_def: "C = add_mset L C'" by simp

  have "clss_lits_generalize_clss_lits N (finsert (add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>) (U |\<union>| clss_of_trail \<Gamma>))"
  proof -
    from C_in have generalize_N_C: "clss_lits_generalize_clss_lits N {|C|}"
    proof (unfold funion_iff, elim disjE)
      show "C |\<in>| N \<Longrightarrow> ?thesis"
        by force
    next
      show "C |\<in>| U \<Longrightarrow> ?thesis"
        by (metis N_superset_lits clss_lits_generalize_clss_lits_insert finsert_fminus
            funion_commute funion_finsert_right)
    qed

    have "clss_lits_generalize_clss_lits N {|add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>|}"
      unfolding clss_lits_generalize_clss_lits_def
    proof (rule fBallI)
      fix K assume "K |\<in>| ffUnion (fset_mset |`| {|add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<rho>|})"
      hence "K = L \<cdot>l \<mu> \<cdot>l \<rho> \<or> (\<exists>M. M \<in># C\<^sub>0 \<and> K = M \<cdot>l \<mu> \<cdot>l \<rho>)"
        by auto
      then show "\<exists>K'|\<in>|ffUnion (fset_mset |`| N). generalizes_lit K' K"
      proof (elim disjE exE conjE)
        assume K_def: "K = L \<cdot>l \<mu> \<cdot>l \<rho>"
        then obtain D L\<^sub>D where "D |\<in>| N" and "L\<^sub>D \<in># D" and "generalizes_lit L\<^sub>D L"
          using generalize_N_C[unfolded C_def clss_lits_generalize_clss_lits_def]
          by (auto simp add: fBex_ffUnion_iff fBall_ffUnion_iff)
        then show ?thesis
          by (simp add: fBex_ffUnion_iff K_def generalizes_lit_def)
            (metis (mono_tags, lifting) fBexI subst_lit_comp_subst)
      next
        fix K' assume "K' \<in># C\<^sub>0" and K_def: "K = K' \<cdot>l \<mu> \<cdot>l \<rho>"
        then obtain D L\<^sub>D where
          D_in: "D |\<in>| N" and L\<^sub>D_in: "L\<^sub>D \<in># D" and gen_L\<^sub>D_K': "generalizes_lit L\<^sub>D K'"
          using generalize_N_C[unfolded C_def clss_lits_generalize_clss_lits_def fBex_ffUnion_iff,
              simplified]
          using propagateI.hyps(5) by auto
        show ?thesis
          unfolding K_def fBex_ffUnion_iff fBex_fset_mset_iff
        proof (intro fBexI bexI)
          show "D |\<in>| N"
            by (rule D_in)
        next
          show "L\<^sub>D \<in># D"
            by (rule L\<^sub>D_in)
        next
          show "generalizes_lit L\<^sub>D (K' \<cdot>l \<mu> \<cdot>l \<rho>)"
            using gen_L\<^sub>D_K' by (metis subst_lit_comp_subst generalizes_lit_def)
        qed
      qed
    qed
    thus ?thesis
      using N_superset_lits clss_lits_generalize_clss_lits_insert by blast
  qed

  then show ?case
    unfolding initial_lits_generalized_learned_lits_def by simp
qed

lemma decide_initial_lits_generalized_learned_lits:
  "decide N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: decide.induct)
  case (decideI L \<Gamma> U)
  thus ?case
    by (simp add: initial_lits_generalized_learned_lits_def)
qed

lemma conflict_initial_lits_generalized_learned_lits:
  assumes "conflict N \<beta> S S'" and "initial_lits_generalized_learned_lits N S"
  shows "initial_lits_generalized_learned_lits N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma> \<rho> \<gamma>\<^sub>\<rho>)
  from assms(2) have "clss_lits_generalize_clss_lits N (U |\<union>| clss_of_trail \<Gamma>)"
    unfolding conflictI(1) by (simp add: initial_lits_generalized_learned_lits_def)
  hence ball_U_\<Gamma>_generalize:
    "\<And>L. L|\<in>|ffUnion (fset_mset |`| (U |\<union>| clss_of_trail \<Gamma>)) \<Longrightarrow> \<exists>K|\<in>|ffUnion (fset_mset |`| N). generalizes_lit K L"
    unfolding clss_lits_generalize_clss_lits_def by blast

  have "clss_lits_generalize_clss_lits N (finsert (D \<cdot> \<rho>) (U |\<union>| clss_of_trail \<Gamma>))"
    unfolding clss_lits_generalize_clss_lits_def
  proof (rule fBallI)
    fix L assume "L |\<in>| ffUnion (fset_mset |`| finsert (D \<cdot> \<rho>) (U |\<union>| clss_of_trail \<Gamma>))"
    hence "L |\<in>| fset_mset (D \<cdot> \<rho>) \<or> L |\<in>| ffUnion (fset_mset |`| (U |\<union>| clss_of_trail \<Gamma>))"
      by simp
    thus "\<exists>K|\<in>|ffUnion (fset_mset |`| N). generalizes_lit K L"
    proof (elim disjE)
      assume "L |\<in>| fset_mset (D \<cdot> \<rho>)"
      hence L_in: "L \<in># D \<cdot> \<rho>" by simp
      then obtain L' where "L = L' \<cdot>l \<rho>" and "L' \<in># D"
        using Melem_subst_cls by blast
      show "?thesis"
        using \<open>D |\<in>| N |\<union>| U\<close>[unfolded funion_iff]
      proof (elim disjE)
        show "D |\<in>| N \<Longrightarrow> ?thesis"
          using L_in
          using fBex_ffUnion_iff substitution_ops.generalizes_lit_def by fastforce
      next
        assume "D |\<in>| U"
        hence "\<exists>K|\<in>|ffUnion (fset_mset |`| N). generalizes_lit K L'"
          using L_in ball_U_\<Gamma>_generalize[of L'] \<open>L' \<in># D\<close>
          using mk_disjoint_finsert by fastforce
        thus ?thesis
          unfolding fBex_ffUnion_iff \<open>L = L' \<cdot>l \<rho>\<close>
          by (metis (no_types, lifting) fBexI fBexE generalizes_lit_def subst_lit_comp_subst)
      qed
    next
      show "L |\<in>| ffUnion (fset_mset |`| (U |\<union>| clss_of_trail \<Gamma>)) \<Longrightarrow> ?thesis"
        using ball_U_\<Gamma>_generalize by simp
    qed
  qed
  then show ?thesis
    using assms(2)
    unfolding conflictI(1,2)
    by (simp add: initial_lits_generalized_learned_lits_def)
qed

lemma clss_lits_generalize_clss_lits_subset:
  "clss_lits_generalize_clss_lits N U1 \<Longrightarrow> U2 |\<subseteq>| U1 \<Longrightarrow> clss_lits_generalize_clss_lits N U2"
  unfolding clss_lits_generalize_clss_lits_def
  by (metis fBall_funion ffUnion_funion_distrib fimage_funion le_iff_sup)

lemma skip_initial_lits_generalized_learned_lits:
  "skip N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: skip.induct)
  case (skipI L D \<sigma> Cl \<Gamma> U)
  then show ?case
    unfolding initial_lits_generalized_learned_lits_def
    unfolding state_learned_simp state_conflict_simp state_trail_simp option.case prod.case
    by (auto elim: clss_lits_generalize_clss_lits_subset)
qed

lemma clss_lits_generalize_clss_lits_subst_clss:
  assumes
    N_lits_alpha_superset: "clss_lits_generalize_clss_lits N1 N2"
  shows "clss_lits_generalize_clss_lits N1 ((\<lambda>C. C \<cdot> \<sigma>) |`| N2)"
  unfolding clss_lits_generalize_clss_lits_def
proof (rule fBallI)
  fix L assume "L |\<in>| ffUnion (fset_mset |`| (\<lambda>C. C \<cdot> \<sigma>) |`| N2)"
  hence "\<exists>L\<^sub>2. L\<^sub>2 |\<in>| ffUnion (fset_mset |`| N2) \<and> L = L\<^sub>2 \<cdot>l \<sigma>"
    by (auto simp: fmember_ffUnion_iff)
  then obtain L\<^sub>2 where "L\<^sub>2 |\<in>| ffUnion (fset_mset |`| N2)" and L_def: "L = L\<^sub>2 \<cdot>l \<sigma>" by auto
  then obtain L\<^sub>1 \<sigma>\<^sub>1 where L\<^sub>1_in: "L\<^sub>1 |\<in>| ffUnion (fset_mset |`| N1)" and "L\<^sub>1 \<cdot>l \<sigma>\<^sub>1 = L\<^sub>2"
    using N_lits_alpha_superset[unfolded clss_lits_generalize_clss_lits_def]
    by (meson fBallE fBexE generalizes_lit_def)

  show "\<exists>K |\<in>| ffUnion (fset_mset |`| N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro fBexI exI)
    show "L\<^sub>1 |\<in>| ffUnion (fset_mset |`| N1)"
      by (rule L\<^sub>1_in)
  next
    show "L\<^sub>1 \<cdot>l (\<sigma>\<^sub>1 \<odot> \<sigma>) = L"
      unfolding L_def \<open>L\<^sub>1 \<cdot>l \<sigma>\<^sub>1 = L\<^sub>2\<close>[symmetric] by simp
  qed
qed

lemma clss_lits_generalize_clss_lits_singleton_subst_cls:
  shows "clss_lits_generalize_clss_lits N {|C|} \<Longrightarrow> clss_lits_generalize_clss_lits N {|C \<cdot> \<sigma>|}"
  by (rule clss_lits_generalize_clss_lits_subst_clss[of N "{|C|}" \<sigma>, simplified])

lemma clss_lits_generalize_clss_lits_subst_cls:
  assumes
    N_lits_alpha_superset: "clss_lits_generalize_clss_lits N {|add_mset L1 (add_mset L2 C)|}"
  shows "clss_lits_generalize_clss_lits N {|add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)|}"
proof (rule clss_lits_generalize_clss_lits_trans)
  show "clss_lits_generalize_clss_lits N {|add_mset L1 (add_mset L2 C) \<cdot> \<sigma>|}"
    by (rule clss_lits_generalize_clss_lits_singleton_subst_cls[of N _ \<sigma>, OF N_lits_alpha_superset])
next
  show "clss_lits_generalize_clss_lits {|add_mset L1 (add_mset L2 C) \<cdot> \<sigma>|}
    {|add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)|}"
    apply (simp add: clss_lits_generalize_clss_lits_def generalizes_lit_def)
    using subst_lit_id_subst by blast
qed

lemma factorize_initial_lits_generalized_learned_lits:
  "factorize N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: factorize.induct)
  case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
  moreover have "clss_lits_generalize_clss_lits N {|add_mset (L \<cdot>l \<mu>) (D \<cdot> \<mu>)|}"
    using factorizeI
    unfolding initial_lits_generalized_learned_lits_def
    apply simp
    using clss_lits_generalize_clss_lits_subst_cls
    using clss_lits_generalize_clss_lits_insert by blast
  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def
    apply simp
    using clss_lits_generalize_clss_lits_insert by blast
qed

lemma resolve_initial_lits_generalized_learned_lits:
  "resolve N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: resolve.induct)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
  moreover have "clss_lits_generalize_clss_lits N {|(D + C) \<cdot> \<mu> \<cdot> \<rho>|}"
  proof -
    from resolveI.prems have
      N_lits_sup: "clss_lits_generalize_clss_lits N (U |\<union>| clss_of_trail \<Gamma> |\<union>| {|D + {#L'#}|})"
      unfolding initial_lits_generalized_learned_lits_def
      by simp_all

    have "clss_lits_generalize_clss_lits N {|D \<cdot> \<mu> \<cdot> \<rho>|}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits N {|D + {#L'#}|}"
        using clss_lits_generalize_clss_lits_insert by auto
      hence "clss_lits_generalize_clss_lits N {|D|}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    moreover have "clss_lits_generalize_clss_lits N {|C \<cdot> \<mu> \<cdot> \<rho>|}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits N (clss_of_trail \<Gamma>)"
        by (rule clss_lits_generalize_clss_lits_subset) blast
      hence "clss_lits_generalize_clss_lits N {|add_mset L C|}"
        unfolding resolveI.hyps
        using clss_lits_generalize_clss_lits_insert by auto
      hence "clss_lits_generalize_clss_lits N {|C|}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    ultimately show ?thesis
      by (auto simp add: clss_lits_generalize_clss_lits_def)
  qed
  ultimately show ?case
    unfolding initial_lits_generalized_learned_lits_def
    unfolding state_trail_simp state_learned_simp state_conflict_simp
    unfolding option.case prod.case
    by (metis clss_lits_generalize_clss_lits_insert funion_finsert_right)
qed

lemma backtrack_initial_lits_generalized_learned_lits:
  "backtrack N \<beta> S S' \<Longrightarrow> initial_lits_generalized_learned_lits N S \<Longrightarrow>
    initial_lits_generalized_learned_lits N S'"
proof (induction S S' rule: backtrack.induct)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
  then show ?case
    unfolding initial_lits_generalized_learned_lits_def
    apply (simp add: clss_of_trail_append)
    apply (erule clss_lits_generalize_clss_lits_subset)
    by blast
qed

abbreviation lits_of_clss where
  "lits_of_clss N \<equiv> \<Union>(set_mset ` N)"

abbreviation grounding_lits_of_clss where
  "grounding_lits_of_clss N \<equiv> {L \<cdot>l \<gamma> | L \<gamma>. L \<in> lits_of_clss N \<and> is_ground_lit (L \<cdot>l \<gamma>)}"

corollary
  assumes "initial_lits_generalized_learned_lits N S"
  shows "grounding_lits_of_clss (fset (state_learned S)) \<subseteq> grounding_lits_of_clss (fset N)"
  (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  from assms(1) have N_lits_sup: "clss_lits_generalize_clss_lits N (state_learned S)"
    unfolding initial_lits_generalized_learned_lits_def 
    using clss_lits_generalize_clss_lits_subset by blast

  fix L
  assume "L \<in> ?lhs"
  then obtain L' \<gamma> where
    L_def: "L = L' \<cdot>l \<gamma>" and
    "L' \<in> \<Union> (set_mset ` fset (state_learned S))" and
    "is_ground_lit (L' \<cdot>l \<gamma>)"
    by auto

  then obtain L\<^sub>N \<sigma>\<^sub>N where "L\<^sub>N \<in> \<Union>(set_mset ` fset N)" and "L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'"
    using N_lits_sup[unfolded clss_lits_generalize_clss_lits_def]
    unfolding fBex_ffUnion_iff fBall_ffUnion_iff fBex_fset_mset_iff fBall_fset_mset_iff
      generalizes_lit_def
    by (smt (verit, ccfv_SIG) UN_iff fBall.rep_eq fBex.rep_eq)

  then show "L \<in> ?rhs"
    unfolding mem_Collect_eq
    using \<open>is_ground_lit (L' \<cdot>l \<gamma>)\<close>
    unfolding L_def \<open>L\<^sub>N \<cdot>l \<sigma>\<^sub>N = L'\<close>[symmetric]
    by (metis subst_lit_comp_subst)
qed


definition trail_lits_from_init_clauses where
  "trail_lits_from_init_clauses N S \<longleftrightarrow>
    (\<forall>L \<in> fst ` set (state_trail S). \<exists>L' \<in> \<Union>(set_mset ` fset N). generalizes_lit L' L)"

lemma trail_lits_from_init_clausesI:
  assumes "trail_lits_from_clauses N S" and "initial_lits_generalized_learned_lits N S"
  shows "trail_lits_from_init_clauses N S"
  unfolding trail_lits_from_init_clauses_def
proof (rule ballI)
  fix L assume "L \<in> fst ` set (state_trail S)"
  with assms(1) obtain L' where
    "L' \<in> \<Union> (set_mset ` (fset N \<union> fset (state_learned S))) \<and> generalizes_lit L' L"
    unfolding trail_lits_from_clauses_def by metis
  hence "(\<exists>x\<in>fset N. L' \<in># x) \<or> (\<exists>x \<in> fset (state_learned S). L' \<in># x)" and "generalizes_lit L' L"
    by simp_all
  thus "\<exists>L'\<in>\<Union> (set_mset ` fset N). generalizes_lit L' L"
  proof (elim disjE bexE)
    fix C assume "C \<in> fset N"
    thus "L' \<in># C \<Longrightarrow> ?thesis"
      using \<open>generalizes_lit L' L\<close> by auto
  next
    fix C assume "C \<in> fset (state_learned S)" and "L' \<in># C"
    with assms(2) have "\<exists>K\<in>\<Union> (set_mset ` fset N). generalizes_lit K L'"
      unfolding initial_lits_generalized_learned_lits_def clss_lits_generalize_clss_lits_def
        fBex_ffUnion_iff fBall_ffUnion_iff
      unfolding fBex.rep_eq fBall.rep_eq
      by auto
    thus "?thesis"
      using \<open>generalizes_lit L' L\<close> by (metis generalizes_lit_def subst_lit_comp_subst)
  qed
qed

end

end