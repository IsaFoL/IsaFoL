theory Simple_Clause_Learning
  imports
    Main
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus
    Ordered_Resolution_Prover.Clausal_Logic
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    First_Order_Terms.Unification
    Functional_Ordered_Resolution_Prover.IsaFoR_Term
begin


section \<open>List_Extra\<close>

primrec find_map where
  "find_map f [] = None" |
  "find_map f (x # xs) = (case f x of None \<Rightarrow> find_map f xs | Some y \<Rightarrow> Some y)"

lemma find_map_conv: "find_map f xs = Option.bind (find (\<lambda>x. f x \<noteq> None) xs) f"
  by (induction xs) auto


section \<open>Multiset_Extra\<close>

definition msingleton :: "'a \<Rightarrow> 'a multiset" where
  "msingleton x \<equiv> {#x#}"


section \<open>Calculus_Extra\<close>

lemma (in consequence_relation) entails_one_formula: "N \<Turnstile> U \<Longrightarrow> D \<in> U \<Longrightarrow> N \<Turnstile> {D}"
  using entail_set_all_formulas by blast


section \<open>Clausal_Calculus_Extra\<close>

lemma (in substitution) true_cls_thick_substI: "I \<TTurnstile>s N \<cdot>cs \<eta> \<Longrightarrow> D \<in> N \<Longrightarrow> I \<TTurnstile> D \<cdot> \<eta>"
  by (simp add: substitution_ops.subst_clss_def true_clss_def)

lemma (in substitution) grounding_of_clss_empty[simp]: "grounding_of_clss {} = {}"
  by (simp add: grounding_of_clss_def)

lemma (in substitution) grounding_of_clss_singleton[simp]:
  "grounding_of_clss {C} = grounding_of_cls C"
  by (simp add: grounding_of_clss_def)

section \<open>Substitution_Extra\<close>

lemma (in substitution) var_disjoint_ConsD:
  assumes "var_disjoint (C # Cs)"
  shows "var_disjoint Cs"
  unfolding var_disjoint_def
proof (intro allI impI)
  fix \<sigma>s :: "'s list"
  assume "length \<sigma>s = length Cs"
  then obtain \<tau> where
    "\<forall>i<Suc (length Cs). \<forall>S. S \<subseteq># (C # Cs) ! i \<longrightarrow> S \<cdot> (id_subst # \<sigma>s) ! i = S \<cdot> \<tau>"
    using assms[unfolded var_disjoint_def, rule_format, of "id_subst # \<sigma>s"]
    by auto
  then show "\<exists>\<tau>. \<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>"
    apply -
    apply (rule exI[where x = \<tau>])
    by (metis Suc_less_eq nth_Cons_Suc)
qed

lemma (in substitution) is_unifiers_insert[simp]:
  "is_unifiers \<sigma> (insert AA AAA) \<longleftrightarrow> is_unifier \<sigma> AA \<and> is_unifiers \<sigma> AAA"
  unfolding is_unifiers_def by simp

lemma (in substitution) is_unifier_singleton[simp]: "is_unifier \<sigma> {x}"
  unfolding is_unifier_def by simp

lemma (in substitution) is_unifiers_image_singleton[simp]: "is_unifiers \<sigma> ((\<lambda>x. {f x}) ` AA)"
  unfolding is_unifiers_def by simp


section \<open>First_Order_Terms Extra\<close>

no_notation subst_apply_term (infixl "\<cdot>" 67)
no_notation subst_apply_literal  (infixl "\<cdot>lit" 60)
no_notation subst_apply_clause  (infixl "\<cdot>cls" 60)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)

(* notation subst_apply_term (infixl "\<cdot>a" 67) *)
notation subst_atm_abbrev (infixl "\<cdot>a" 67)
notation subst_atm_list (infixl "\<cdot>al" 67)
notation subst_lit (infixl "\<cdot>l" 67)
notation subst_cls (infixl "\<cdot>" 67)
notation subst_clss (infixl "\<cdot>cs" 67)
notation subst_cls_list (infixl "\<cdot>cl" 67)
notation subst_cls_lists (infixl "\<cdot>\<cdot>cl" 67)
notation subst_compose (infixl "\<odot>" 67)


section \<open>Abstract Concept of Variable Renaming\<close>

locale renaming =
  fixes renaming :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes
    renaming_correct: "finite V \<Longrightarrow> renaming V x \<notin> V" and
    renaming_inj: "finite V \<Longrightarrow> inj (renaming V)"

definition renaming_nats where
  "renaming_nats V = (let m = Max V in (\<lambda>x. Suc (x + m)))"

subsubsection \<open>Interpretation to Prove That Assumptions Are Consistent\<close>

global_interpretation renaming_nats: renaming renaming_nats
proof unfold_locales
  show "\<And>V x. finite V \<Longrightarrow> renaming_nats V x \<notin> V"
    unfolding renaming_nats_def Let_def by (meson Max.coboundedI Suc_le_lessD not_add_less2)
next
  show "\<And>V. finite V \<Longrightarrow> inj (renaming_nats V)"
    unfolding renaming_nats_def Let_def by (rule injI) simp
qed


subsubsection \<open>Extras Related to First-order Terms\<close>

context renaming begin

lemma Term_is_renaming_Var_renaming: "finite V \<Longrightarrow> Term.is_renaming (Var \<circ> renaming V)"
  unfolding Term.is_renaming_def
  apply simp
  by (meson comp_inj_on injI inj_on_subset renaming_inj term.inject(1) top_greatest)

lemma is_renaming_Var_renaming: "finite V \<Longrightarrow> is_renaming (Var \<circ> renaming V)"
  unfolding is_renaming_def
  using renaming_inj
  term surj
  term range
  oops

lemma vars_term_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_term (t \<cdot>a (Var \<circ> renaming V)) \<inter> V = {}"
  using Term_is_renaming_Var_renaming[OF fin_V] renaming_correct[OF fin_V]
  by (induction t) auto

lemma vars_lit_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_lit (L \<cdot>l (Var \<circ> renaming V)) \<inter> V = {}"
  using vars_term_subst_renaming_disj[OF fin_V] by auto

lemma vars_cls_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_clause (C \<cdot> (Var \<circ> renaming V)) \<inter> V = {}"
  unfolding vars_clause_def
  apply simp
  using vars_lit_subst_renaming_disj[OF fin_V]
  by (smt (verit, best) UN_iff UN_simps(10) disjoint_iff multiset.set_map subst_cls_def)

definition rename_clause ::
  "('f, 'a) term clause set \<Rightarrow> ('f, 'a) term clause \<Rightarrow> ('f, 'a) term clause" where
  "rename_clause N C = C \<cdot> (Var \<circ> renaming (\<Union> (vars_clause ` N)))"

lemma disjoint_vars_set_insert_rename_clause:
  assumes fin_N: "finite N" and disj_N: "disjoint_vars_set N"
  shows "disjoint_vars_set (insert (rename_clause N C) N)"
  unfolding disjoint_vars_set_def
proof (intro ballI impI)
  fix D E
  assume D_in: "D \<in> insert (rename_clause N C) N" and E_in: "E \<in> insert (rename_clause N C) N" and
    D_neq_E: "D \<noteq> E"
  from fin_N have fin_vars_N: "finite (\<Union> (vars_clause ` N))" by simp
  show "disjoint_vars D E"
    using D_in E_in D_neq_E
    apply simp
    apply safe
    unfolding rename_clause_def disjoint_vars_conv
    using vars_cls_subst_renaming_disj[OF fin_vars_N]
    using disj_N[unfolded disjoint_vars_set_def disjoint_vars_conv, rule_format]
    by auto
qed

definition renamings_apart :: "('f, 'a) term clause list \<Rightarrow> ('f, 'a) subst list" where
  "renamings_apart Cs = replicate (length Cs) (Var \<circ> renaming (\<Union> (vars_clause ` set Cs)))"

lemma renamings_apart_length: "length (renamings_apart Cs) = length Cs"
  unfolding renamings_apart_def by simp

lemma renamings_apart_renaming: "\<rho> \<in> set (renamings_apart Cs) \<Longrightarrow> is_renaming \<rho>"
  unfolding renamings_apart_def
  apply simp
  using Term_is_renaming_Var_renaming Term_is_renaming_if_is_renaming
  find_theorems "is_renaming _ = Term.is_renaming _"
  oops

lemma renamings_apart_disjoint_vars_set:
  fixes Cs :: "('f, 'a) term clause list"
  shows "disjoint_vars_set (set (Cs \<cdot>\<cdot>cl (renamings_apart Cs)))"
proof (induction Cs)
  case Nil
  show ?case
    by (simp add: renamings_apart_def disjoint_vars_set_def)
next
  case (Cons C Cs)

  define \<rho> :: "('f, 'a) subst" where
    "\<rho> = Var \<circ> renaming (vars_clause C \<union> \<Union> (vars_clause ` set Cs))"
  have ren_C_Cs_conv: "renamings_apart (C # Cs) = \<rho> # replicate (length Cs) \<rho>"
    unfolding renamings_apart_def \<rho>_def by simp
  hence FOO: "(C # Cs) \<cdot>\<cdot>cl renamings_apart (C # Cs) = C \<cdot> \<rho> # Cs \<cdot>\<cdot>cl replicate (length Cs) \<rho>"
    by (simp add: subst_cls_lists_def)

  have fin_vars_C_Cs: "finite (vars_clause C \<union> \<Union> (vars_clause ` set Cs))"
    by simp

  show ?case
    unfolding FOO
    unfolding disjoint_vars_set_def
    apply (intro ballI)
    apply simp
    apply safe
    oops

end


section \<open>SCL State\<close>

type_synonym ('f, 'v) closure = "('f, 'v) term clause \<times> ('f, 'v) subst"
type_synonym ('f, 'v) trail = "(('f, 'v) term literal \<times> ('f, 'v) closure option) list"
type_synonym ('f, 'v) state =
  "('f, 'v) trail \<times> ('f, 'v) term clause set \<times> nat \<times> ('f, 'v) closure option"

definition trail_propagate ::
  "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) closure \<Rightarrow> ('f, 'v) trail" where
  "trail_propagate \<Gamma> L Cl = (L, Some Cl) # \<Gamma>"

definition trail_decide :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) trail" where
  "trail_decide \<Gamma> L = (L, None) # \<Gamma>"

definition is_decision_lit :: "('f, 'v) term literal \<times> ('f, 'v) closure option \<Rightarrow> bool" where
  "is_decision_lit Ln \<longleftrightarrow> snd Ln = None"

primrec trail_level :: "('f, 'v) trail \<Rightarrow> nat" where
  "trail_level [] = 0" |
  "trail_level (Ln # \<Gamma>) = (if is_decision_lit Ln then Suc else id) (trail_level \<Gamma>)"

primrec trail_level_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> nat" where
  "trail_level_lit [] _ = 0" |
  "trail_level_lit (Ln # \<Gamma>) L =
    (if fst Ln = L \<or> fst Ln = -L then trail_level (Ln # \<Gamma>) else trail_level_lit \<Gamma> L)"

definition trail_level_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> nat" where
  "trail_level_cls \<Gamma> C = Max_mset {#trail_level_lit \<Gamma> L. L \<in># C#}"

primrec trail_backtrack :: "('f, 'v) trail \<Rightarrow> nat \<Rightarrow> ('f, 'v) trail" where
  "trail_backtrack [] _ = []" |
  "trail_backtrack (Lc # \<Gamma>) level =
    (if is_decision_lit Lc \<and> trail_level (Lc # \<Gamma>) = level then
      Lc # \<Gamma>
    else
      trail_backtrack \<Gamma> level)"

lemma trail_backtrack_inv: "trail_level \<Gamma> < level \<Longrightarrow> trail_backtrack \<Gamma> level = []"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (metis (mono_tags, lifting) trail_backtrack.simps(2) trail_level.simps(2) not_less_eq
        not_less_iff_gr_or_eq of_nat_eq_id of_nat_id)
qed

lemma trail_backtrack_suffix: "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (cases "is_decision_lit Lc") (simp_all add: suffix_ConsI)
qed

lemma trail_backtrack_hd:
  "trail_backtrack \<Gamma> level = [] \<or> is_decision_lit (hd (trail_backtrack \<Gamma> level))"
  by (induction \<Gamma>) simp_all

lemma trail_backtrack_level:
  "trail_level (trail_backtrack \<Gamma> level) = 0 \<or> trail_level (trail_backtrack \<Gamma> level) = level"
  by (induction \<Gamma>) simp_all

definition trail_interp :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term interp" where
  "trail_interp \<Gamma> = \<Union>((\<lambda>L. case L of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) ` fst ` set \<Gamma>)"

definition trail_true_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_true_lit \<Gamma> L \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"

definition trail_false_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_false_lit \<Gamma> L \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile>l -L"

definition trail_true_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_true_cls \<Gamma> C \<longleftrightarrow> (\<exists>L \<in># C. trail_true_lit \<Gamma> L)"

definition trail_false_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_false_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_false_lit \<Gamma> L)"

definition trail_defined_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> (trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L)"



lemma ball_trail_backtrackI:
  assumes "\<forall>x \<in> set \<Gamma>. P (fst x)"
  shows "\<forall>x \<in> set (trail_backtrack \<Gamma> i). P (fst x)"
  using assms trail_backtrack_suffix[THEN set_mono_suffix]
  by blast

lemma trail_interp_Cons: "trail_interp (Lc # \<Gamma>) = trail_interp [Lc] \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def
  by simp

lemma true_lit_thick_unionD: "(I1 \<union> I2) \<TTurnstile>l L \<Longrightarrow> I1 \<TTurnstile>l L \<or> I2 \<TTurnstile>l L"
  by auto

lemma trail_false_cls_ConsD:
  assumes tr_false: "trail_false_cls ((L, Some Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Some Cl) # \<Gamma>) M"
    unfolding trail_false_cls_def by simp
  hence "trail_interp ((L, Some Cl) # \<Gamma>) \<TTurnstile>l - M"
    unfolding trail_false_lit_def by simp
  hence "trail_interp [(L, Some Cl)] \<union> trail_interp \<Gamma> \<TTurnstile>l - M"
    using trail_interp_Cons by fast
  thus "trail_false_lit \<Gamma> M"
    unfolding trail_false_lit_def
    using M_neq_L
    by (cases L; cases M) (simp_all add: trail_interp_def trail_false_lit_def)
qed


section \<open>SCL Calculus\<close>

locale scl = renaming renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v"
  (* \<comment> \<open>Fiori and Weidenbach (CADE 2019) do not specify whether their mgu is idempotent.\<close>
  minimal_imgu subst_atm id_subst comp_subst renamings_apart atm_of_atms imgu
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    imgu :: "'a set set \<Rightarrow> 's option" + *)
  (* fixes rename_clause :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) term clause \<Rightarrow> ('f, 'v) term clause" *)
(*   assumes
    rename_clause_is_renamed: "rename_clause N C = C' \<Longrightarrow> \<exists>\<sigma>. is_renaming \<sigma> \<and> C' \<cdot> \<sigma> = C" and
    rename_clause_disjoint_vars_set:
      "disjoint_vars_set N \<Longrightarrow> disjoint_vars_set (insert (rename_clause N C) N)" and
    mgu_preserves_disjoint_vars:
      "finite AAA \<Longrightarrow> \<forall>AA\<in>AAA. finite AA \<Longrightarrow> disjoint_vars_set N \<Longrightarrow> C \<in> N \<Longrightarrow>
      \<Union> AAA \<subseteq> atms_of C \<Longrightarrow> imgu AAA = Some \<mu> \<Longrightarrow> disjoint_vars_set ((N - {C}) \<union> {C \<cdot> \<mu>})" *)
begin

(* thm mgu_disjoint_vars_set_subst_clss_ident[no_vars] *)

inductive scl :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state => ('f, 'v) state \<Rightarrow> bool" for N where
  propagate: "C + {#L#} \<in> N \<union> U \<Longrightarrow> is_ground_cls ((C + {#L#}) \<cdot> \<sigma>) \<Longrightarrow>
    trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>) \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C + {#L#}, \<sigma>), U, k, None)" |

  decide: "is_ground_lit L \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (trail_decide \<Gamma> L, U, Suc k, None)" |

  conflict: "D \<in> N \<union> U \<Longrightarrow> D' = rename_clause (N \<union> U) D \<Longrightarrow> is_ground_cls (D' \<cdot> \<sigma>) \<Longrightarrow>
    trail_false_cls \<Gamma> (D' \<cdot> \<sigma>) \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (\<Gamma>, U, Suc k, Some (D', \<sigma>))" |

  skip: "-(L \<cdot>l \<delta>) \<notin># D \<cdot> \<sigma> \<Longrightarrow>
    scl N (trail_propagate \<Gamma> (L \<cdot>l \<delta>) (C + {#L#}, \<delta>), U, k, Some (D, \<sigma>)) (\<Gamma>, U, k, Some (D, \<sigma>))" |

  factorize: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> Unification.mgu (atm_of L) (atm_of L') = Some \<eta> \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L,L'#}, \<sigma>)) (\<Gamma>, U, k, Some ((D + {#L#}) \<cdot> \<eta>, \<sigma>))" |

  resolve: "\<Gamma> = trail_propagate \<Gamma>' (L \<cdot>l \<delta>) (C + {#L#}, \<delta>) \<Longrightarrow> trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = k \<Longrightarrow>
    (L \<cdot>l \<delta>) = -(L' \<cdot>l \<sigma>) \<Longrightarrow> Unification.mgu (atm_of L) (atm_of (-L')) = Some \<eta> \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L'#}, \<sigma>)) (\<Gamma>, U, k, Some ((D + C) \<cdot> \<eta>, \<sigma> \<odot> \<delta>))" |

  backtrack: "trail_level_lit \<Gamma> (L \<cdot>l \<sigma>) = k \<Longrightarrow> trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = i \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L#}, \<sigma>)) (trail_backtrack \<Gamma> i, U \<union> {D + {#L#}}, k, None)"

text \<open>Note that, in contrast to Fiori and Weidenbach (CADE 2019), the set of clauses @{term N} is a
parameter of the relation instead of being repeated twice in the state. This is to highlight the
fact that it is a constant.\<close>


section \<open>Soundness\<close>

inductive sound_trail for N U where
  Nil[simp]: "sound_trail N U []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    (case u of
      None \<Rightarrow> True |
      Some (C, \<sigma>) \<Rightarrow> \<exists>C' L'.
        C = C' + {#L'#} \<and> L = L' \<cdot>l \<sigma> \<and> trail_false_cls \<Gamma> (C' \<cdot> \<sigma>) \<and> C \<in> N \<union> U) \<Longrightarrow>
    sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U ((L, u) # \<Gamma>)"

lemma sound_trail_supersetI: "sound_trail N U \<Gamma> \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> U \<subseteq> UU \<Longrightarrow> sound_trail NN UU \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case by simp
next
  case (Cons \<Gamma> L u)
  thus ?case
    apply simp
    apply (rule sound_trail.Cons)
  subgoal
    by assumption
  subgoal
    by (cases u) auto
  subgoal
    by simp
  done
qed

lemma sound_trail_backtrackI:
  "sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U (trail_backtrack \<Gamma> level)"
  by (induction \<Gamma> rule: sound_trail.induct) (auto intro: sound_trail.intros)

lemma sound_trail_propagate:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>) \<Longrightarrow> trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<Longrightarrow>
  C + {#L#} \<in> N \<union> U \<Longrightarrow> sound_trail N U (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C + {#L#}, \<sigma>))"
  unfolding trail_propagate_def
  by (rule sound_trail.Cons) auto

lemma sound_trail_decide:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow> sound_trail N U (trail_decide \<Gamma> L)"
  unfolding trail_decide_def
  by (auto intro: sound_trail.Cons)

text \<open>In contrast to Fiori and Weidenbach (CADE 2019), I lifting the entailments @{term \<open>N \<TTurnstile>e U\<close>}
and @{term \<open>N \<TTurnstile>e {C}\<close>} from ground to non-ground with a ground substitution @{term \<eta>};
the conjunction becomes an implication.\<close>

abbreviation entails_\<G> (infix "\<TTurnstile>\<G>e" 50) where
  "entails_\<G> N U \<equiv> grounding_of_clss N \<TTurnstile>e grounding_of_clss U"

definition sound_state :: "('f, 'v) Term.term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "sound_state N S \<longleftrightarrow> (\<exists>\<Gamma> U k u.
    S = (\<Gamma>, U, k, u) \<and>
    disjoint_vars_set (N \<union> U \<union> (case u of Some (C, _) \<Rightarrow> {C} | None \<Rightarrow> {})) \<and>
    (\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L) \<and>
    sound_trail N U \<Gamma> \<and>
    N \<TTurnstile>\<G>e U \<and>
    (case u of None \<Rightarrow> True
    | Some (C, \<sigma>) \<Rightarrow> trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<and> N \<TTurnstile>\<G>e {C}))"

abbreviation initial_state :: "('f, 'v) state" where
  "initial_state \<equiv> ([], {}, 0, None)"

lemma sound_initial_state[simp]: "disjoint_vars_set N \<Longrightarrow> sound_state N initial_state"
  apply (simp add: sound_state_def)
  apply (intro allI impI)
  unfolding grounding_of_clss_def
  by force

lemma ball_trail_propagate_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit (L \<cdot>l \<sigma>)"
  shows "\<forall>x\<in>set (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C + {#L#}, \<sigma>)). is_ground_lit (fst x)"
  unfolding trail_propagate_def
  using assms
  by simp

lemma ball_trail_decide_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit L"
  shows "\<forall>x\<in>set (trail_decide \<Gamma> L). is_ground_lit (fst x)"
  unfolding trail_decide_def
  using assms
  by simp

lemma entails_clss_insert: "N \<TTurnstile>e insert C U \<longleftrightarrow> N \<TTurnstile>e {C} \<and> N \<TTurnstile>e U"
  by auto

lemma subst_clss_insert[simp]: "insert C U \<cdot>cs \<eta> = insert (C \<cdot> \<eta>) (U \<cdot>cs \<eta>)"
  by (simp add: subst_clss_def)

lemma ball_singleton: "(\<forall>x \<in> {y}. P x) \<longleftrightarrow> P y" by simp

lemma valid_grounding_of_renaming:
  assumes "is_renaming \<rho>"
  shows "I \<TTurnstile>s grounding_of_cls (C \<cdot> \<rho>) \<longleftrightarrow> I \<TTurnstile>s grounding_of_cls C"
proof -
  have "grounding_of_cls (C \<cdot> \<rho>) = grounding_of_cls C" (is "?lhs = ?rhs")
  proof (rule Set.equalityI)
    show "?lhs \<subseteq> ?rhs"
      using subst_cls_eq_grounding_of_cls_subset_eq
    using assms unfolding is_renaming_def
  using subset_antisym subst_cls_comp_subst
      subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst
      sorry
  next
    show "?rhs \<subseteq> ?lhs" sorry
  qed
  thus ?thesis
    by simp
    unfolding true_clss_def
    apply (rule ballI)
    apply (rule \<open>?lhs\<close>[unfolded true_clss_def, rule_format])
    using assms unfolding is_renaming_def
  using subset_antisym subst_cls_comp_subst
      subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst
  sledgehammer
  (* by (metis is_renaming_def subset_antisym subst_cls_comp_subst
      subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst) *)

theorem scl_sound_state: "scl N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: scl.induct)
  case (propagate C L U \<sigma> \<Gamma> k)
  hence "(\<forall>x\<in>set (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C + {#L#}, \<sigma>)). is_ground_lit (fst x))"
    unfolding sound_state_def
    by (intro ball_trail_propagate_is_ground_lit) (simp_all add: is_ground_cls_def)
  with propagate show ?case
    using sound_trail_propagate
    by (auto simp: sound_state_def)
next
  case (decide L \<Gamma> U k)
  thus ?case
    unfolding sound_state_def
    using sound_trail_decide ball_trail_decide_is_ground_lit
    by fastforce
next
  case (conflict D U D' \<sigma> \<Gamma> k)
  from conflict.prems have
    disj_N_U: "disjoint_vars_set (N \<union> U)" and
    ball_\<Gamma>_ground: "\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from conflict.hyps have D_in: "D \<in> N \<union> U" by simp
  from conflict.hyps have D'_def: "D' = rename_clause (N \<union> U) D" by simp
  from conflict.hyps have tr_false_D': "trail_false_cls \<Gamma> (D' \<cdot> \<sigma>)" by simp

  from disj_N_U and D'_def have disj_N_U_D': "disjoint_vars_set (N \<union> U \<union> {D'})"
    using rename_clause_disjoint_vars_set by simp

  from D'_def obtain \<rho> where "is_renaming \<rho>" and "D' \<cdot> \<rho> = D"
      using rename_clause_is_renamed by auto

  have N_entails_D': "N \<TTurnstile>\<G>e {D'}"
  proof (intro allI impI)
    fix I assume valid_N: "I \<TTurnstile>s grounding_of_clss N"
    show "I \<TTurnstile>s grounding_of_clss {D'}"
      using D_in
    proof (rule Set.UnE)
      assume "D \<in> N"
      with valid_N have "I \<TTurnstile>s grounding_of_cls D"
        unfolding grounding_of_clss_def by simp
      then show ?thesis
        using \<open>is_renaming \<rho>\<close> \<open>D' \<cdot> \<rho> = D\<close>[symmetric]
        by (simp add: valid_grounding_of_renaming)
    next
      assume "D \<in> U"
      moreover from N_entails_U valid_N have "I \<TTurnstile>s grounding_of_clss U" by blast
      ultimately have "I \<TTurnstile>s grounding_of_cls D" by (simp add: grounding_of_clss_def)
      then show ?thesis
        using \<open>is_renaming \<rho>\<close> \<open>D' \<cdot> \<rho> = D\<close>[symmetric]
        by (simp add: valid_grounding_of_renaming)
    qed
  qed

  show ?case
    unfolding sound_state_def
    using disj_N_U_D' ball_\<Gamma>_ground sound_\<Gamma> N_entails_U tr_false_D' N_entails_D'
    by simp
next
  case (skip L \<delta> D \<sigma> \<Gamma> C U k)
  from skip show ?case
    unfolding sound_state_def
    by (auto simp: trail_propagate_def elim: sound_trail.cases dest!: trail_false_cls_ConsD)
next
  case (factorize L \<sigma> L' D \<eta> \<Gamma> U k)

  from factorize.prems have
    disj_N_U_D_L_L': "disjoint_vars_set (N \<union> U \<union> {D + {#L, L'#}})" and
    ball_\<Gamma>_ground:"\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    N_entails_D_L_L': "N \<TTurnstile>\<G>e {D + {#L, L'#}}"
    unfolding sound_state_def by simp_all

  from factorize.hyps have
    imgu: "imgu (insert {atm_of L, atm_of L'} ((\<lambda>x. {atm_of x}) ` set_mset D)) = Some \<eta>" by simp

  from factorize.hyps have unifier_\<sigma>: "is_unifier \<sigma> {atm_of L, atm_of L'}"
    apply (simp add: is_unifiers_def is_unifier_def subst_lit_def)
    by (metis atm_of_subst_lit card_1_singleton_iff factorize.hyps(1) image_insert insert_absorb2
        le_Suc_eq subst_atms_single substitution_ops.subst_atms_def)
  hence unifiers_\<sigma>: "is_unifiers \<sigma> (insert {atm_of L, atm_of L'} ((\<lambda>x. {atm_of x}) ` set_mset D))" by simp
  from factorize.hyps have imgu_\<eta>:
    "is_imgu \<eta> (insert {atm_of L, atm_of L'} ((\<lambda>x. {atm_of x}) ` set_mset D))"
    by (auto intro: mgu_is_imgu)
  hence unif_\<mu>: "is_unifier \<eta> {atm_of L, atm_of L'}"
    using is_unifiers_is_unifier is_mgu_is_unifiers by blast
  hence "atm_of L \<cdot>a \<eta> = atm_of L' \<cdot>a \<eta>"
    by (auto intro: is_unifier_subst_atm_eqI[rotated])
  with factorize.hyps have "L \<cdot>l \<eta> = L' \<cdot>l \<eta>"
    by (cases L; cases L'; simp add: subst_lit_def)
  
  obtain \<gamma> where \<sigma>_def: "\<sigma> = \<eta> \<odot> \<gamma>"
    using is_mgu_is_most_general[OF is_imgu_is_mgu[OF imgu_\<eta>] unifiers_\<sigma>]
    by blast

  have "N \<union> U - {add_mset L (add_mset L' D)} = N \<union> U"
    sorry

  have "(\<Union>x\<in>set_mset D. {atm_of x}) \<subseteq> insert (atm_of L) (insert (atm_of L') (atms_of D))"
    using atm_of_lit_in_atms_of by fastforce

  then have disj_N_U_D_L: "disjoint_vars_set (N \<union> U \<union> {(D + {#L#}) \<cdot> \<eta>})"
    using mgu_preserves_disjoint_vars[OF _ _ disj_N_U_D_L_L' _ _ imgu, of "D + {#L, L'#}", simplified]
    apply (simp add: disjoint_vars_set_insert)
    using disj_N_U_D_L_L'
    find_theorems "disjoint_vars_set (insert _ _)"
    sorry

  moreover have N_entails_D': "N \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<eta>}" sorry

  moreover have "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<eta> \<cdot> \<sigma>)"
    using imgu_\<eta> tr_false_cls
    by (simp add: \<sigma>_def trail_false_cls_def \<open>L \<cdot>l \<eta> = L' \<cdot>l \<eta>\<close>)

  ultimately show ?case
    unfolding sound_state_def
    using ball_\<Gamma>_ground sound_\<Gamma> N_entails_U
    by simp
next
  case (resolve \<Gamma> \<Gamma>' L \<delta> C D \<sigma> k L' \<eta> U)
  from resolve.hyps have imgu_\<eta>: "is_imgu \<eta> {{atm_of L, atm_of L'}}"
    by (auto intro: mgu_is_imgu)

  from resolve.prems have
    ball_\<Gamma>_ground_lit: "Ball (fst ` set \<Gamma>) is_ground_lit" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    tr_false_cls_and_entails: "\<And>\<eta>. is_ground_subst \<eta> \<Longrightarrow> N \<cdot>cs \<eta> \<TTurnstile>e U \<cdot>cs \<eta> \<Longrightarrow>
      trail_false_cls \<Gamma> ((D + {#L'#}) \<cdot> \<sigma>) \<and> N \<cdot>cs \<eta> \<TTurnstile>e {(D + {#L'#}) \<cdot> \<eta>}"
    unfolding sound_state_def by auto

  from sound_\<Gamma> obtain C' L'' where
    "\<not> trail_defined_lit \<Gamma>' (L'' \<cdot>l \<delta>)" "sound_trail N U \<Gamma>'" "C + {#L#} = C' + {#L''#}"
    "- (L' \<cdot>l \<sigma>) = L'' \<cdot>l \<delta>" "trail_false_cls \<Gamma>' (C' \<cdot> \<delta>)" "C + {#L#} \<in> N \<union> U"
    unfolding resolve.hyps trail_propagate_def
    apply simp
    apply (erule sound_trail.cases)
    by auto 

  have "trail_false_cls \<Gamma> ((D + C) \<cdot> \<eta> \<cdot> (\<sigma> \<odot> \<delta>)) \<and> N \<cdot>cs \<eta>' \<TTurnstile>e {(D + C) \<cdot> \<eta> \<cdot> \<eta>'}"
    (is "?lhs \<and> ?rhs")
    if ground_\<eta>': "is_ground_subst \<eta>'" and gr_N_entails_U: "N \<cdot>cs \<eta>' \<TTurnstile>e U \<cdot>cs \<eta>'"
    for \<eta>'
  proof -
    have tr_f: "trail_false_cls \<Gamma> ((D + {#L'#}) \<cdot> \<sigma>)" and entails: "N \<cdot>cs \<eta>' \<TTurnstile>e {(D + {#L'#}) \<cdot> \<eta>'}"
      using tr_false_cls_and_entails[OF ground_\<eta>' gr_N_entails_U] by simp_all

    have "\<forall>x\<in>#D \<cdot> \<eta> \<cdot> \<sigma>. trail_false_lit \<Gamma> x"
      apply (rule ballI)
      apply (rule tr_f[unfolded trail_false_cls_def, rule_format, simplified])
      apply (rule disjI2)
      using imgu_\<eta>
    proof (elim disjE)
      sorry
    have "\<forall>x\<in>#D \<cdot> \<eta> \<cdot> \<sigma> \<cdot> \<delta>. trail_false_lit \<Gamma> x"
      
      sorry
    moreover have "\<forall>x\<in>#C \<cdot> \<eta> \<cdot> \<sigma> \<cdot> \<delta>. trail_false_lit \<Gamma> x"
      sorry
    ultimately have "trail_false_cls \<Gamma> ((D + C) \<cdot> \<eta> \<cdot> (\<sigma> \<odot> \<delta>))"
      by (simp add: trail_false_cls_def ball_Un)

    with entails show ?thesis
      apply simp
      using \<open>C + {#L#} \<in> N \<union> U\<close>
      using resolve.hyps 
      sorry
  qed
  with ball_\<Gamma>_ground_lit sound_\<Gamma> show ?case
    unfolding sound_state_def by simp
next
  case (backtrack \<Gamma> L \<sigma> k D i U)
  have "\<forall>x\<in>set (trail_backtrack \<Gamma> i). is_ground_lit (fst x)" and
       N_entails_U: "\<forall>\<eta>. is_ground_subst \<eta> \<longrightarrow> N \<cdot>cs \<eta> \<TTurnstile>e U \<cdot>cs \<eta>" and
       N_entails_D_plus_L: "\<forall>\<eta>. is_ground_subst \<eta> \<longrightarrow> N \<cdot>cs \<eta> \<TTurnstile>e {D + {#L#}} \<cdot>cs \<eta>"
    using backtrack.prems
    by (auto simp: sound_state_def intro!: ball_trail_backtrack_is_ground_litI)
  moreover have "sound_trail N (insert (add_mset L D) U) (trail_backtrack \<Gamma> i)"
    using backtrack
    by (auto simp: sound_state_def intro: sound_trail_backtrackI sound_trail_supersetI)
  moreover have "\<And>\<eta>. is_ground_subst \<eta> \<Longrightarrow> N \<cdot>cs \<eta> \<TTurnstile>e (U \<union> {D + {#L#}}) \<cdot>cs \<eta>"
    using N_entails_U N_entails_D_plus_L
    by simp
  ultimately show ?case
    unfolding sound_state_def
    by (simp add: sound_state_def)
qed

end

end