theory First_Order_Superposition_Completeness
  imports
    Ground_Superposition_Completeness
    Ground_Superposition_Soundness
    Grounded_First_Order_Superposition
begin

lemma test: " (\<forall>x. is_Var (\<rho> x)) \<Longrightarrow> Var ` vars_term (term \<cdot>t \<rho>) = \<rho> ` (vars_term term)" 
  apply(cases "term")
   apply auto
     apply (metis term.disc(2) term.set_cases(2))
    apply (metis image_iff term.collapse(1) term.set_sel(3))
  apply (smt (verit, ccfv_SIG) UN_iff image_the_Var_image_subst_renaming_eq member_image_the_Var_image_subst vars_term_subst_apply_term)
  by (metis (no_types, lifting) UN_iff image_eqI term.collapse(1) term.set_sel(3) vars_term_subst)

lemma  test_atom: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_atom (atom \<cdot>a \<rho>) = \<rho> ` vars_atom atom"
  using test[OF assms]
  unfolding vars_atom_def subst_atom_def
  apply auto
   apply (smt (verit, del_insts) UN_iff image_iff uprod.set_map)
  by (smt (verit, ccfv_threshold) UN_I image_iff uprod.set_map)

lemma  test_literal: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_literal (literal \<cdot>l \<rho>) = \<rho> ` vars_literal literal"
  using test_atom[OF assms]
  unfolding vars_literal_def subst_literal_def
  by (metis literal.map_sel(1) literal.map_sel(2))

lemma  test_clause: 
  assumes "(\<forall>x. is_Var (\<rho> x))"
  shows "Var ` vars_clause (clause \<cdot> \<rho>) = \<rho> ` vars_clause clause"
  using test_literal[OF assms]
  unfolding vars_clause_def subst_clause_def
  apply auto
   apply (smt (verit, ccfv_threshold) UN_iff image_iff)
  using image_iff by fastforce 

lemma finite_vars_atom [simp]:
  "finite (vars_atom atom)"
  unfolding vars_atom_def
  by simp

lemma finite_vars_literal [simp]:
  "finite (vars_literal literal)"
  unfolding vars_literal_def
  by simp

lemma finite_vars_clause [simp]:
  "finite (vars_clause clause)"
  unfolding vars_clause_def
  by auto

context first_order_superposition_calculus
begin

lemmas term_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_term  finite_vars_term]

lemmas atom_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_atom finite_vars_atom]

lemmas literal_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_literal finite_vars_literal]

lemmas clause_renaming_exists = 
  renaming_exists[OF subset_UNIV subset_UNIV finite_vars_clause finite_vars_clause]

end

(* TODO: *)

lemma term_subst_if: "term \<cdot>t (\<lambda>var. if var \<in> vars_term term then x var else y var) = term \<cdot>t (\<lambda>var. x var)"
  by (smt (verit, ccfv_threshold) term_subst_eq)

lemma atom_subst_if: "atom \<cdot>a (\<lambda>var. if var \<in> vars_atom atom then x var else y var) = atom \<cdot>a (\<lambda>var. x var)"
  using term_subst_if
  unfolding subst_atom_def vars_atom_def
  by (smt (verit, ccfv_SIG) UN_I term_subst_eq uprod.map_cong0)

lemma literal_subst_if: "literal \<cdot>l (\<lambda>var. if var \<in> vars_literal literal then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  using atom_subst_if
  unfolding subst_literal_def vars_literal_def
  by(cases "literal") auto

lemma literal_subst_if': "literal \<in># clause
   \<Longrightarrow> literal \<cdot>l (\<lambda>var. if  \<exists>x\<in>#clause. var \<in> vars_literal x then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  unfolding vars_literal_def subst_literal_def
  apply(cases literal)
   apply auto
  by (smt (verit) UN_I literal.sel subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)+
  
(* TODO: generalize? *)
lemma clause_subst_if: "clause \<cdot> (\<lambda>var. if var \<in> vars_clause clause then x var else y var) = clause \<cdot> (\<lambda>var. x var)"
  unfolding subst_clause_def vars_clause_def 
  using literal_subst_if'[of _ clause x y]
  by simp

lemma term_subst_if'': "vars_term term\<^sub>1 \<subseteq> vars_term term\<^sub>2 \<Longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. x var)"
  apply(cases term\<^sub>1; cases term\<^sub>2)
     apply auto
   apply (smt (verit, ccfv_SIG) SUP_le_iff empty_iff singletonD subset_singletonD term_subst_eq)
  by (smt (verit, del_insts) Term.term.simps(18) subsetD term.distinct(1) term.inject(2) term.set_cases(2) term.set_intros(4) term_subst_eq)

lemma atom_subst_if'': "vars_atom atom\<^sub>1 \<subseteq> vars_atom atom\<^sub>2 \<Longrightarrow> atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) = atom\<^sub>1 \<cdot>a (\<lambda>var. x var)"
  using term_subst_if''
  unfolding subst_atom_def vars_atom_def
  by (smt (verit, del_insts) SUP_le_iff eval_same_vars_cong in_mono uprod.map_cong0)

lemma literal_subst_if'': "vars_literal literal\<^sub>1 \<subseteq> vars_literal literal\<^sub>2 \<Longrightarrow> literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) = literal\<^sub>1 \<cdot>l (\<lambda>var. x var)"
  using atom_subst_if''
  unfolding subst_literal_def vars_literal_def
  by(cases literal\<^sub>1) auto

lemma clause_subst_if''': "literal \<in># clause \<Longrightarrow> literal \<cdot>l (\<lambda>var. if var \<in> vars_clause clause then x var else y var) = literal \<cdot>l (\<lambda>var. x var)"
  unfolding vars_literal_def subst_literal_def vars_clause_def
    apply(cases literal)
   apply auto
  apply (smt (verit, ccfv_SIG) UN_I subst_atom_def term_subst_eq upair_in_literal(1) uprod.map_cong0 vars_atom_def)
   by (smt (verit) UN_I subst_atom_def term_subst_eq upair_in_literal(2) uprod.map_cong0 vars_atom_def)

(* TODO: *)
lemma clause_subst_if': "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. x var)"
  unfolding subst_clause_def vars_clause_def 
  using clause_subst_if'''[of _ clause\<^sub>2 x y]
  by (metis (no_types, lifting) ext image_mset_cong2 mset_subsetD subset_mset.antisym_conv2 vars_clause_def)

lemma term_subst_if_2: "vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<Longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. y var)"
  apply(cases term\<^sub>1; cases term\<^sub>2)
     apply auto
   apply (smt (verit, ccfv_SIG) term_subst_eq)
  by (smt (verit, ccfv_SIG) UN_I disjoint_iff term_subst_eq)

lemma atom_subst_if_2: "vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<Longrightarrow> atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) = atom\<^sub>1 \<cdot>a (\<lambda>var. y var)"
  apply(cases atom\<^sub>1; cases atom\<^sub>2)
  using term_subst_if_2
  by (smt (verit, ccfv_SIG) IntI UN_I empty_iff subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)

lemma literal_subst_if_2: "vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<Longrightarrow> literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) = literal\<^sub>1 \<cdot>l (\<lambda>var. y var)"
   unfolding subst_literal_def vars_literal_def
   apply(cases literal\<^sub>1; cases literal\<^sub>2)
   apply auto
   using atom_subst_if_2 by blast+

abbreviation lift_to_atom 
  where "lift_to_atom P \<equiv> \<lambda>atom. \<forall>term \<in> set_uprod atom. P term"

abbreviation lift_to_literal 
  where "lift_to_literal P \<equiv> \<lambda>literal. P (atm_of literal)"

abbreviation lift_to_clause 
  where "lift_to_clause P \<equiv> \<lambda>clause.  \<forall>literal \<in># clause. P literal"

abbreviation lift_term_predicate_to_clause 
  where "lift_term_predicate_to_clause P \<equiv> lift_to_clause (lift_to_literal (lift_to_atom P))"

abbreviation lift_to_atom2 
  where "lift_to_atom2 P \<equiv> \<lambda>atom\<^sub>1 atom\<^sub>2. \<forall>term\<^sub>1 \<in> set_uprod atom\<^sub>1. \<forall>term\<^sub>2 \<in> set_uprod atom\<^sub>2. P term\<^sub>1 term\<^sub>2"

abbreviation lift_to_literal2
  where "lift_to_literal2 P \<equiv> \<lambda>literal\<^sub>1 literal\<^sub>2. P (atm_of literal\<^sub>1) (atm_of literal\<^sub>2)"

abbreviation lift_to_clause2 
  where "lift_to_clause2 P \<equiv> \<lambda>clause\<^sub>1 clause\<^sub>2.  \<forall>literal\<^sub>1 \<in># clause\<^sub>1. \<forall>literal\<^sub>2 \<in># clause\<^sub>2. P literal\<^sub>1 literal\<^sub>2"

abbreviation lift_term_predicate_to_clause2 
  where "lift_term_predicate_to_clause2 P \<equiv> lift_to_clause2 (lift_to_literal2 (lift_to_atom2 P))"


lemma clause_if_term: "\<forall>term. P term \<Longrightarrow> P' = lift_term_predicate_to_clause P \<Longrightarrow> P' clause"
  by auto

lemma clause2_if_term: "\<forall>term\<^sub>1 term\<^sub>2. P term\<^sub>1 term\<^sub>2 \<Longrightarrow> P' = lift_term_predicate_to_clause2 P \<Longrightarrow> P' clause\<^sub>1 clause\<^sub>2"
  by auto

lemma test': "\<forall> term\<^sub>1 term\<^sub>2. vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow> term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) = term\<^sub>1 \<cdot>t (\<lambda>var. y var)"
  using term_subst_if_2 by blast

lemma test_atom': "(lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)) atom\<^sub>1 atom\<^sub>2 =
                        (vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<longrightarrow>
                        atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) =
                        atom\<^sub>1 \<cdot>a y)"
  apply auto
  using atom_subst_if_2 apply blast
  using test' by blast+

lemma test_atom'': "lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y) = (\<lambda>atom\<^sub>1 atom\<^sub>2.
                        vars_atom atom\<^sub>1 \<inter> vars_atom atom\<^sub>2 = {} \<longrightarrow>
                        atom\<^sub>1 \<cdot>a (\<lambda>var. if var \<in> vars_atom atom\<^sub>2 then x var else y var) =
                        atom\<^sub>1 \<cdot>a y)"
  using test_atom' 
  by fast

lemma test_literal': "(lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y))) literal\<^sub>1 literal\<^sub>2 = (
                        vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
                        literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
                        literal\<^sub>1 \<cdot>l y)"
  apply auto
  using literal_subst_if_2 apply blast
  using test' by blast+

lemma test_literal'': "lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)) = (\<lambda>literal\<^sub>1 literal\<^sub>2.
                        vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
                        literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
                        literal\<^sub>1 \<cdot>l y)"
  using test_literal'
  by fast

lemma test_clause': 
  "(lift_to_clause2 (lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y)))) (clause\<^sub>1 :: ('f, 'v) atom clause) (clause\<^sub>2 :: ('f, 'v) atom clause) = (
                        vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow>
                        clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
                        clause\<^sub>1 \<cdot> y)"
  apply(auto simp: test_literal')
  subgoal 
  proof-
    assume a: "lift_to_clause
      (\<lambda>literal\<^sub>1.
          lift_to_clause
           (\<lambda>literal\<^sub>2.
               vars_literal literal\<^sub>1 \<inter> vars_literal literal\<^sub>2 = {} \<longrightarrow>
               literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
               literal\<^sub>1 \<cdot>l y)
           clause\<^sub>2)
      clause\<^sub>1" 
      "vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {}"

    then have "lift_to_clause
      (\<lambda>literal\<^sub>1.
          lift_to_clause
           (\<lambda>literal\<^sub>2.
               literal\<^sub>1 \<cdot>l (\<lambda>var. if var \<in> vars_literal literal\<^sub>2 then x var else y var) =
               literal\<^sub>1 \<cdot>l y)
           clause\<^sub>2)
      clause\<^sub>1"
      apply auto
      by (smt (verit, ccfv_threshold) inf_assoc inf_bot_left inf_commute inf_sup_absorb multi_member_split vars_clause_add_mset)

    then have "lift_to_clause
     (\<lambda>literal.
              literal \<cdot>l (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
              literal \<cdot>l y)
     clause\<^sub>1"
      unfolding vars_clause_def
      apply auto
    proof-
      fix literal
      assume a': "lift_to_clause
         (\<lambda>literal.
             lift_to_clause
              (\<lambda>literala.
                  literal \<cdot>l (\<lambda>var. if var \<in> vars_literal literala then x var else y var) =
                  literal \<cdot>l y)
              clause\<^sub>2)
         clause\<^sub>1"
      "literal \<in># clause\<^sub>1"

      have "\<And>var. var \<in> vars_literal literal \<Longrightarrow> \<not>literal \<in># clause\<^sub>2"
        using a'(2) a(2)
        unfolding vars_clause_def
        by auto

      then have "\<And>var. var \<in> vars_literal literal \<Longrightarrow>  \<not> var \<in> \<Union> (vars_literal ` set_mset clause\<^sub>2)"
        apply auto
        by (metis IntI UN_I a'(2) a(2) emptyE vars_clause_def)

      then have "literal \<cdot>l (\<lambda>var. if var \<in> \<Union> (vars_literal ` set_mset clause\<^sub>2) then x var else y var) =
           literal \<cdot>l y "
        unfolding  subst_literal_def vars_literal_def
        apply auto
        by (smt (verit, ccfv_SIG) UN_I literal.expand literal.map_disc_iff literal.map_sel(1) literal.map_sel(2) subst_atom_def term_subst_eq uprod.map_cong0 vars_atom_def)

      then show "literal \<cdot>l (\<lambda>var. if \<exists>x\<in>#clause\<^sub>2. var \<in> vars_literal x then x var else y var) =
           literal \<cdot>l y " 
        by auto
    qed  
    

    then show ?thesis
      unfolding vars_clause_def subst_clause_def
      by auto
  qed
  using literal_subst_if_2 by blast+

lemma test_clause'': "lift_to_clause2 (lift_to_literal2 (lift_to_atom2
                    (\<lambda>term\<^sub>1 term\<^sub>2.
                        vars_term term\<^sub>1 \<inter> vars_term term\<^sub>2 = {} \<longrightarrow>
                        term\<^sub>1 \<cdot>t (\<lambda>var. if var \<in> vars_term term\<^sub>2 then x var else y var) =
                        term\<^sub>1 \<cdot>t y))) = (\<lambda>(clause\<^sub>1 :: ('f, 'v) atom clause) (clause\<^sub>2 :: ('f, 'v) atom clause).
                        vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow>
                        clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) =
                        clause\<^sub>1 \<cdot> y)"
  using test_clause' 
  by fast
 
lemma clause_subst_if_2: "vars_clause (clause\<^sub>1 :: ('f, 'v) atom clause)  \<inter> vars_clause (clause\<^sub>2 :: ('f, 'v) atom clause) = {} \<longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. y var)"
  apply(rule clause2_if_term[OF test', of "\<lambda>clause\<^sub>1 clause\<^sub>2. vars_clause clause\<^sub>1 \<inter> vars_clause clause\<^sub>2 = {} \<longrightarrow> clause\<^sub>1 \<cdot> (\<lambda>var. if var \<in> vars_clause clause\<^sub>2 then x var else y var) = clause\<^sub>1 \<cdot> (\<lambda>var. y var)", of x y])
  by (simp add: test_clause'')

lemma vars_clause_subset: "clause\<^sub>1 \<subseteq># clause\<^sub>2 \<Longrightarrow> vars_clause clause\<^sub>1 \<subseteq> vars_clause clause\<^sub>2"
  by (metis Un_subset_iff order_refl subset_mset.add_diff_inverse vars_clause_plus)

(* --MISC-- *)

context ground_superposition_calculus
begin

abbreviation equality_resolution_inferences where
  "equality_resolution_inferences \<equiv>  {Infer [P] C | P C. ground_eq_resolution P C}"

abbreviation equality_factoring_inferences where
  "equality_factoring_inferences \<equiv>  {Infer [P] C | P C.  ground_eq_factoring P C}"

abbreviation superposition_inferences where
  "superposition_inferences \<equiv>  {Infer [P2, P1] C | P1 P2 C. ground_superposition P2 P1 C}"

end

context grounded_first_order_superposition_calculus
begin

lemma equality_resolution_ground_instance:
  assumes 
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>" and
    ground_eq_resolution: 
      "ground.ground_eq_resolution
          (to_ground_clause (premise \<cdot> \<theta>)) 
          (to_ground_clause (conclusion \<cdot> \<theta>))"
  (* TODO: *)
  shows "\<exists>conclusion'. equality_resolution premise conclusion'
            \<and> Infer [to_ground_clause (premise \<cdot> \<theta>)]  (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
                inference_groundings (Infer [premise] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
  using ground_eq_resolution
proof(cases "to_ground_clause (premise \<cdot> \<theta>)" "to_ground_clause (conclusion \<cdot> \<theta>)" 
      rule: ground.ground_eq_resolution.cases)
  case (ground_eq_resolutionI literal\<^sub>G term\<^sub>G)

  have premise_not_empty: "premise \<noteq> {#}"
    using 
      ground_eq_resolutionI(1)
      empty_not_add_mset
      clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G (to_ground_clause (conclusion \<cdot> \<theta>)))"
    using 
       ground_eq_resolutionI(1)[THEN arg_cong, of to_clause]
       to_ground_clause_inverse[OF premise_grounding]
    by metis

  also have "... = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)"
    unfolding to_clause_add_mset
    by (simp add: conclusion_grounding)

  finally have premise': "premise \<cdot> \<theta> = add_mset (to_literal literal\<^sub>G) (conclusion \<cdot> \<theta>)".

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>)) \<noteq> {#}"

  obtain max_literal where max_literal: 
      "is_maximal\<^sub>l max_literal premise" 
      "is_maximal\<^sub>l (max_literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast
   
  moreover then have "max_literal \<in># premise"
    using maximal\<^sub>l_in_clause by fastforce

  moreover have max_literal_literal\<^sub>G: 
      "max_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)"
  if ?select\<^sub>G_empty
    using ground_eq_resolutionI(3) max_literal unique_maximal_in_ground_clause
    unfolding ground_eq_resolutionI(2) is_maximal_lit_iff_is_maximal\<^sub>l
    by (metis empty_not_add_mset multi_member_split premise_grounding that to_ground_clause_inverse)

  moreover obtain selected_literal where 
    "selected_literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    "selected_literal \<in># select premise" 
  if ?select\<^sub>G_not_empty
    using ground_eq_resolutionI(3) select
    unfolding ground_eq_resolutionI(2)
    by (smt image_iff multiset.set_map subst_clause_def ground_literal_in_ground_clause(3))
   
  moreover then have "?select\<^sub>G_not_empty \<Longrightarrow> selected_literal \<in># premise"
    by (meson mset_subset_eqD select_subset)

  ultimately obtain literal where
    literal: "literal \<cdot>l \<theta> = to_literal (term\<^sub>G !\<approx> term\<^sub>G)" and
    literal_in_premise: "literal \<in># premise" and
    literal_selected: "?select\<^sub>G_not_empty \<Longrightarrow> literal \<in># select premise" and
    literal_max: "?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal premise"
    by blast    

  have literal_grounding: "is_ground_literal (literal \<cdot>l \<theta>)"
    using literal ground_literal_is_ground
    by simp

  from literal obtain "term" term' where terms: "literal = term !\<approx> term'"
    using subst_polarity_stable to_literal_polarity_stable
    by (metis literal.collapse(2) literal.disc(2) uprod_exhaust)

  have term_term': "term \<cdot>t \<theta> = term' \<cdot>t \<theta>"
    using literal
    unfolding terms subst_literal(2) subst_atom_def to_literal_def to_atom_def
    by simp

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term, term'}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have literal\<^sub>G: 
    "to_literal literal\<^sub>G = (term !\<approx> term') \<cdot>l \<theta>" 
    "literal\<^sub>G = to_ground_literal ((term !\<approx> term') \<cdot>l \<theta>)"
    using literal ground_eq_resolutionI(2)  terms 
    by simp_all

  obtain conclusion' where conclusion': "premise = add_mset literal conclusion'"
    using multi_member_split[OF literal_in_premise]
    by blast

  have conclusion'_\<theta>: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using premise'
    unfolding conclusion' ground_eq_resolutionI(2) literal[symmetric] subst_clause_add_mset
    by simp
    
  have equality_resolution: "equality_resolution premise (conclusion' \<cdot> \<sigma>)"
  proof (rule equality_resolutionI)
     show "premise = add_mset literal conclusion'"
       using conclusion'.
  next 
    show "literal = term !\<approx> term'"
      using terms.    
  next
    show "term_subst.is_imgu \<sigma> {{term, term'}}"
      using \<sigma>(1).
  next
    show "select premise = {#} \<and> is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>) 
       \<or> literal \<in># select premise"
    proof(cases ?select\<^sub>G_empty)
      case select\<^sub>G_empty: True

      then have "max_literal \<cdot>l \<theta> = literal \<cdot>l \<theta>"
        by (simp add: max_literal_literal\<^sub>G literal)
        
      then have literal_\<theta>_is_maximal: "is_maximal\<^sub>l (literal \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
        using max_literal(2) by simp
       
      have literal_\<sigma>_in_premise: "literal \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
        by (simp add: literal_in_clause_subst literal_in_premise)

      have "is_maximal\<^sub>l (literal \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
        using is_maximal\<^sub>l_ground_subst_stability'[OF 
                literal_\<sigma>_in_premise 
                premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
                literal_\<theta>_is_maximal[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
              ].

     then show ?thesis
       using select select\<^sub>G_empty
       by simp
    next
      case False
      then show ?thesis
        using literal_selected by blast
    qed
  next 
    show "conclusion' \<cdot> \<sigma> = conclusion' \<cdot> \<sigma>" ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have conclusion'_\<sigma>_\<theta> : "conclusion' \<cdot> \<sigma> \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using conclusion'_\<theta>  
    unfolding clause_subst_compose[symmetric] \<sigma>_\<theta>.
 
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def conclusion'_\<sigma>_\<theta>
    by (smt (verit, ccfv_threshold) conclusion'_\<sigma>_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO *)
  with equality_resolution show ?thesis
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def
    using premise_grounding
    apply auto
    by (metis conclusion'_\<sigma>_\<theta> conclusion_grounding ground_eq_resolution)
qed

lemma equality_factoring_ground_instance:
  assumes 
    premise_grounding [intro]: "is_ground_clause (premise \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>" and
    ground_eq_factoring: 
      "ground.ground_eq_factoring
          (to_ground_clause (premise \<cdot> \<theta>)) 
          (to_ground_clause (conclusion \<cdot> \<theta>))"
    shows "\<exists>conclusion'. equality_factoring premise (conclusion') 
            \<and> Infer [to_ground_clause (premise \<cdot> \<theta>)]  (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
                inference_groundings (Infer [premise] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_eq_factoring
proof(cases "to_ground_clause (premise \<cdot> \<theta>)" "to_ground_clause (conclusion \<cdot> \<theta>)" 
      rule: ground.ground_eq_factoring.cases)
  case (ground_eq_factoringI literal\<^sub>G\<^sub>1 literal\<^sub>G\<^sub>2 premise'\<^sub>G term\<^sub>G\<^sub>1 term\<^sub>G\<^sub>2 term\<^sub>G\<^sub>3)

  have premise_not_empty: "premise \<noteq> {#}"
    using ground_eq_factoringI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)
  
  have select_empty: "select premise = {#}"
    using ground_eq_factoringI(4) select clause_subst_empty
    by auto
  
  have premise_\<theta>: "premise \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 (add_mset literal\<^sub>G\<^sub>2 premise'\<^sub>G))"
    using ground_eq_factoringI(1)
    by (metis premise_grounding to_ground_clause_inverse)
  
  obtain literal\<^sub>1 where literal\<^sub>1_maximal: 
    "is_maximal\<^sub>l literal\<^sub>1 premise" 
    "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<theta>) (premise \<cdot> \<theta>)"
    using is_maximal\<^sub>l_ground_subst_stability[OF premise_not_empty premise_grounding]
    by blast

  note max_ground_literal = is_maximal_lit_iff_is_maximal\<^sub>l[
      THEN iffD1,
      OF ground_eq_factoringI(5), 
      unfolded ground_eq_factoringI(2) to_ground_clause_inverse[OF premise_grounding]
    ]

  have literal\<^sub>1: "literal\<^sub>1 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>1"
    using 
      unique_maximal_in_ground_clause[OF premise_grounding literal\<^sub>1_maximal(2) max_ground_literal]
      ground_eq_factoringI(2)
    by blast

  then have "\<exists>term\<^sub>1 term\<^sub>1'. literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
    unfolding ground_eq_factoringI(2)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>1 obtain term\<^sub>1 term\<^sub>1' where 
    literal\<^sub>1_terms: "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'" and
    term\<^sub>G\<^sub>1_term\<^sub>1: "to_term term\<^sub>G\<^sub>1 = term\<^sub>1 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(2) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force 

  obtain premise'' where premise'': "premise = add_mset literal\<^sub>1 premise''"
    using maximal\<^sub>l_in_clause[OF literal\<^sub>1_maximal(1)]
    by (meson multi_member_split)

  then have premise''_\<theta>: "premise'' \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>2) (to_clause premise'\<^sub>G)"
    using premise_\<theta> 
    unfolding to_clause_add_mset literal\<^sub>1[symmetric]
    by (simp add: subst_clause_add_mset)

  then obtain literal\<^sub>2 where literal\<^sub>2:
    "literal\<^sub>2 \<cdot>l \<theta> = to_literal literal\<^sub>G\<^sub>2"
    "literal\<^sub>2 \<in># premise''"
    unfolding subst_clause_def
    using msed_map_invR by force

  then have "\<exists>term\<^sub>2 term\<^sub>2'. literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
    unfolding ground_eq_factoringI(3)  
    using to_literal_stable subst_pos_stable is_pos_def[symmetric]
    by (metis uprod_exhaust)
   
  with literal\<^sub>2 obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2_terms: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>G\<^sub>1_term\<^sub>2: "to_term term\<^sub>G\<^sub>1 = term\<^sub>2 \<cdot>t \<theta>"
    unfolding ground_eq_factoringI(3) to_literal_def to_atom_def subst_literal_def subst_atom_def 
    by force
 
  have term\<^sub>1_term\<^sub>2: "term\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<theta>"
    using term\<^sub>G\<^sub>1_term\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>2
    by argo

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  have term\<^sub>G\<^sub>2_term\<^sub>1': "to_term term\<^sub>G\<^sub>2 = term\<^sub>1' \<cdot>t \<theta>"
    using literal\<^sub>1 term\<^sub>G\<^sub>1_term\<^sub>1 
    unfolding 
      literal\<^sub>1_terms 
      ground_eq_factoringI(2) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto
   
  have term\<^sub>G\<^sub>3_term\<^sub>2': "to_term term\<^sub>G\<^sub>3 = term\<^sub>2' \<cdot>t \<theta>"
    using literal\<^sub>2 term\<^sub>G\<^sub>1_term\<^sub>2
    unfolding 
      literal\<^sub>2_terms 
      ground_eq_factoringI(3) 
      to_literal_def 
      to_atom_def 
      subst_literal_def
      subst_atom_def 
    by auto

  obtain premise' where premise: "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')" 
    using literal\<^sub>2(2) maximal\<^sub>l_in_clause[OF  literal\<^sub>1_maximal(1)] premise''
    by (metis multi_member_split)

  then have premise'_\<theta>: "premise' \<cdot> \<theta> = to_clause premise'\<^sub>G"
    using premise''_\<theta>  premise''
    unfolding literal\<^sub>2(1)[symmetric]
    by (simp add: subst_clause_add_mset)
  
  let ?conclusion' = "add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise')"

  have equality_factoring: "equality_factoring premise (?conclusion' \<cdot> \<sigma>)"
  proof (rule equality_factoringI)
    show "premise = add_mset literal\<^sub>1 (add_mset literal\<^sub>2 premise')"
      using premise.
  next
    show "literal\<^sub>1 = term\<^sub>1 \<approx> term\<^sub>1'"
      using literal\<^sub>1_terms.
  next 
    show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
      using literal\<^sub>2_terms.
  next 
    show  "select premise = {#}"
      using select_empty.
  next
    have literal\<^sub>1_\<sigma>_in_premise: "literal\<^sub>1 \<cdot>l \<sigma> \<in># premise \<cdot> \<sigma>"
      using literal\<^sub>1_maximal(1) literal_in_clause_subst maximal\<^sub>l_in_clause by blast

    have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
    using is_maximal\<^sub>l_ground_subst_stability'[OF 
              literal\<^sub>1_\<sigma>_in_premise 
              premise_grounding[unfolded \<sigma>(2) clause_subst_compose]
              literal\<^sub>1_maximal(2)[unfolded \<sigma>(2) clause_subst_compose literal_subst_compose]
            ].

    then show "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<sigma>) (premise \<cdot> \<sigma>)"
      by blast
  next
    have term_groundings: "is_ground_term (term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau>)" "is_ground_term (term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term_subst_compose[symmetric] 
        \<sigma>(2)[symmetric]
        term\<^sub>G\<^sub>1_term\<^sub>1[symmetric] 
        term\<^sub>G\<^sub>2_term\<^sub>1'[symmetric] 
      using ground_term_is_ground
      by simp_all

    have "term\<^sub>1' \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_eq_factoringI(6)[unfolded 
          less\<^sub>t\<^sub>G_def 
          term\<^sub>G\<^sub>1_term\<^sub>1 
          term\<^sub>G\<^sub>2_term\<^sub>1'
          \<sigma>(2) 
          term_subst_compose
      ].

    then show "\<not> term\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
 next 
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1, term\<^sub>2}}"
      using \<sigma>(1).
  next 
    show "?conclusion' \<cdot> \<sigma> = ?conclusion' \<cdot> \<sigma>"
      ..
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have "conclusion \<cdot> \<theta> = 
      add_mset (to_term term\<^sub>G\<^sub>2 !\<approx> to_term term\<^sub>G\<^sub>3) 
        (add_mset (to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3) (to_clause premise'\<^sub>G))"
    using ground_eq_factoringI(7) to_ground_clause_inverse[OF conclusion_grounding]
    unfolding to_term_to_atom to_atom_to_literal to_clause_add_mset[symmetric]
    by simp

  then have conclusion_\<theta>: 
    "conclusion \<cdot> \<theta> = add_mset (term\<^sub>1 \<approx> term\<^sub>2') (add_mset (term\<^sub>1' !\<approx> term\<^sub>2') premise') \<cdot> \<theta>"
    unfolding 
      term\<^sub>G\<^sub>2_term\<^sub>1'
      term\<^sub>G\<^sub>3_term\<^sub>2'
      term\<^sub>G\<^sub>1_term\<^sub>1
      premise'_\<theta>[symmetric]
      subst_clause_add_mset[symmetric]
      subst_literal[symmetric]
      subst_atom[symmetric]
    by (simp add: add_mset_commute)

  then have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings (?conclusion' \<cdot> \<sigma>)"
    unfolding clause_groundings_def 
    using \<sigma>(2) conclusion_\<theta> conclusion_grounding by auto

  (* TODO *)
  with equality_factoring show ?thesis
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def
    using premise_grounding
    apply auto
    by (metis (no_types, lifting) \<sigma>_\<theta> clause_subst_compose conclusion_\<theta> conclusion_grounding ground_eq_factoring)
qed

lemma superposition_ground_instance:
  assumes 
    renaming: 
      "term_subst.is_renaming \<rho>\<^sub>1" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}" and
    premise\<^sub>1_grounding [intro]: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and
    premise\<^sub>2_grounding [intro]: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and
    conclusion_grounding [intro]: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = (select premise\<^sub>1) \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = (select premise\<^sub>2) \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>" and
    ground_superposition: 
      "ground.ground_superposition
          (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))
          (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))
          (to_ground_clause (conclusion \<cdot> \<theta>))" and
    not_redundant:
    "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion \<cdot> \<theta>)) 
      \<notin> ground.Red_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
 (* TODO: (Premise order!)  *)
  shows "\<exists>conclusion'. superposition premise\<^sub>2 premise\<^sub>1 conclusion'
            \<and> Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) 
                \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')
            \<and> conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   using ground_superposition
proof(cases 
      "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)"
      "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      "to_ground_clause (conclusion \<cdot> \<theta>)"
      rule: ground.ground_superposition.cases)
  case (ground_superpositionI 
          literal\<^sub>G\<^sub>1
          premise\<^sub>G\<^sub>1'
          literal\<^sub>G\<^sub>2
          premise\<^sub>G\<^sub>2'
          \<P>\<^sub>G
          context\<^sub>G
          term\<^sub>G\<^sub>1
          term\<^sub>G\<^sub>2
          term\<^sub>G\<^sub>3
        )

  have premise\<^sub>1_not_empty: "premise\<^sub>1 \<noteq> {#}"
    using ground_superpositionI(1) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>2_not_empty: "premise\<^sub>2 \<noteq> {#}"
    using ground_superpositionI(2) empty_not_add_mset clause_subst_empty
    by (metis to_clause_empty_mset to_clause_inverse)

  have premise\<^sub>1_\<theta> : "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1')"
    using ground_superpositionI(1)
    by (metis premise\<^sub>1_grounding to_ground_clause_inverse)

   have premise\<^sub>2_\<theta> : "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(2)
    by (metis premise\<^sub>2_grounding to_ground_clause_inverse)

  let ?select\<^sub>G_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) = {#}"
  let ?select\<^sub>G_not_empty = "select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)) \<noteq> {#}"

  have pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l: 
    "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  have neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l: 
    "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>1) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<odot> \<theta>)"
    using ground_superpositionI(9)
    unfolding is_maximal_lit_iff_is_maximal\<^sub>l
    by(simp add: premise\<^sub>1_grounding)

  obtain pos_literal\<^sub>1 where
    "is_strictly_maximal\<^sub>l pos_literal\<^sub>1 premise\<^sub>1"
    "pos_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Pos"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>1_grounding[folded clause_subst_compose] 
            pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
          ]
    by blast

  moreover then have "\<P>\<^sub>G = Pos \<Longrightarrow> pos_literal\<^sub>1 \<in># premise\<^sub>1" 
    using strictly_maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_max_literal\<^sub>1 where
    "is_maximal\<^sub>l neg_max_literal\<^sub>1 premise\<^sub>1"
    "neg_max_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_empty
    using 
      is_maximal\<^sub>l_ground_subst_stability[OF 
        premise\<^sub>1_not_empty 
        premise\<^sub>1_grounding[folded clause_subst_compose]
      ]
      neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l
    by (metis clause_subst_compose premise\<^sub>1_grounding unique_maximal_in_ground_clause)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> neg_max_literal\<^sub>1 \<in># premise\<^sub>1" 
    using maximal\<^sub>l_in_clause by fastforce

  moreover obtain neg_selected_literal\<^sub>1 where
    "neg_selected_literal\<^sub>1 \<in># select premise\<^sub>1"
    "neg_selected_literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" 
  if "\<P>\<^sub>G = Neg" ?select\<^sub>G_not_empty 
    using ground_superpositionI(9) select(1)
    by (smt (z3) clause_subst_compose ground_literal_in_ground_clause3 image_iff multiset.set_map 
          subst_clause_def)

  moreover then have "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> neg_selected_literal\<^sub>1 \<in># premise\<^sub>1" 
    by (meson mset_subset_eqD select_subset)

  ultimately obtain literal\<^sub>1 where
   literal\<^sub>1_\<theta>: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>1" and
   literal\<^sub>1_in_premise\<^sub>1: "literal\<^sub>1 \<in># premise\<^sub>1" and
   literal\<^sub>1_is_strictly_maximal: "\<P>\<^sub>G = Pos \<Longrightarrow> is_strictly_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_is_maximal: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_empty \<Longrightarrow> is_maximal\<^sub>l literal\<^sub>1 premise\<^sub>1" and
   literal\<^sub>1_selected: "\<P>\<^sub>G = Neg \<Longrightarrow> ?select\<^sub>G_not_empty \<Longrightarrow> literal\<^sub>1 \<in># select premise\<^sub>1"
    by (metis ground_superpositionI(9) literals_distinct(1))

  then have literal\<^sub>1_grounding [intro]: "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<odot> \<theta>)"
    by simp

  have literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l: 
    "is_strictly_maximal\<^sub>l (to_literal literal\<^sub>G\<^sub>2) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<odot> \<theta>)"
    using ground_superpositionI(11)
    unfolding is_strictly_maximal\<^sub>G\<^sub>l_iff_is_strictly_maximal\<^sub>l
    by (simp add: premise\<^sub>2_grounding)

  obtain literal\<^sub>2 where 
    literal\<^sub>2_maximal: "is_strictly_maximal\<^sub>l literal\<^sub>2 premise\<^sub>2" and
    literal\<^sub>2_\<theta>: "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta> = to_literal literal\<^sub>G\<^sub>2"
    using is_strictly_maximal\<^sub>l_ground_subst_stability[OF 
            premise\<^sub>2_grounding[folded clause_subst_compose] 
            literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
          ].

  then have literal\<^sub>2_in_premise\<^sub>2: "literal\<^sub>2 \<in># premise\<^sub>2" 
    using strictly_maximal\<^sub>l_in_clause by blast

  have literal\<^sub>2_grounding [intro]: "is_ground_literal (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<odot> \<theta>)"
    using literal\<^sub>2_\<theta> by simp

  obtain premise\<^sub>1' where premise\<^sub>1: "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
    by (meson literal\<^sub>1_in_premise\<^sub>1 multi_member_split)

  then have premise\<^sub>1'_\<theta>: "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1'"
    using premise\<^sub>1_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>1_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  obtain premise\<^sub>2' where premise\<^sub>2: "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
    by (meson literal\<^sub>2_in_premise\<^sub>2 multi_member_split)

  then have premise\<^sub>2'_\<theta>: "premise\<^sub>2' \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2'"
    using premise\<^sub>2_\<theta>  
    unfolding to_clause_add_mset literal\<^sub>2_\<theta>[symmetric]
    by (simp add: subst_clause_add_mset)

  let ?\<P> = "if \<P>\<^sub>G = Pos then Pos else Neg"

  from literal\<^sub>1_\<theta> have literal\<^sub>1_\<theta>': 
    "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta> = ?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle> (to_term term\<^sub>G\<^sub>2))"
    using ground_superpositionI(4)
    unfolding ground_superpositionI(5)
    by (cases "\<P>\<^sub>G = Pos") 
       (simp_all add: 
          to_atom_to_literal[symmetric] 
          to_term_to_atom[symmetric] 
          ground_term_with_context(3)[symmetric]
        )

  then obtain term\<^sub>1_with_context term\<^sub>1' where 
    literal\<^sub>1: "literal\<^sub>1 = ?\<P> (Upair term\<^sub>1_with_context term\<^sub>1')" and
    term\<^sub>1'_\<theta>: "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>2" and
    term\<^sub>1_with_context_\<theta>: "term\<^sub>1_with_context \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
    by (smt (verit, ccfv_SIG) obtain_from_literal_subst)

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have conclusion_\<theta>\<^sub>G: "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  from literal\<^sub>2_\<theta> have literal\<^sub>2_\<theta>': 
    "literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<theta> = to_term term\<^sub>G\<^sub>1 \<approx> to_term term\<^sub>G\<^sub>3"
    unfolding ground_superpositionI(6) to_term_to_atom to_atom_to_literal(2) literal_subst_compose.

  then obtain term\<^sub>2 term\<^sub>2' where 
    literal\<^sub>2: "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'" and
    term\<^sub>2_\<theta>: "term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and     
    term\<^sub>2'_\<theta>: "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>3"
   using obtain_from_pos_literal_subst
   by metis

  have special_case: "\<nexists>context\<^sub>1 term\<^sub>1. 
    term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
    term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
    context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> 
    is_Fun term\<^sub>1 \<Longrightarrow>
      ground.redundant_infer
         (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'] 
                (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')))"
  proof-
    assume a: "\<nexists>context\<^sub>1 term\<^sub>1. 
      term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> 
      term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> 
      context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> 
      is_Fun term\<^sub>1"

    have term\<^sub>1_with_context_not_ground: "\<not> is_ground_term term\<^sub>1_with_context"
    proof
      assume "is_ground_term term\<^sub>1_with_context"

      then obtain term\<^sub>1 context\<^sub>1 where
        "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
        "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" 
        "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
        "is_Fun term\<^sub>1"
        by (metis ground_context_is_ground ground_term_is_ground subst_ground_context term\<^sub>1_with_context_\<theta> term_subst.subst_ident_if_ground gterm_is_fun)
    
      with a show False
        by blast
    qed

    with a term\<^sub>1_with_context_\<theta> have "\<exists>term\<^sub>x context\<^sub>x context\<^sub>x'. 
      term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle> \<and> 
      is_Var term\<^sub>x \<and> 
      (context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>) \<circ>\<^sub>c context\<^sub>x' = to_context context\<^sub>G"
     proof(induction term\<^sub>1_with_context arbitrary: context\<^sub>G)
       case (Var x)
       show ?case
         apply(rule exI[of _ "Var x"], rule exI[of _ Hole], rule exI[of _ "to_context context\<^sub>G"])
         by simp
      next
       case (Fun f terms)
       then have "context\<^sub>G \<noteq> GHole"
         by (metis ctxt_apply_term.simps(1) ctxt_of_gctxt.simps(1) subst_apply_ctxt.simps(1) term.disc(2))

       then obtain ss1 context\<^sub>G' ss2 where
        context\<^sub>G: "context\<^sub>G = GMore f ss1 context\<^sub>G' ss2"
         using Fun(3)
         by (smt (verit) ctxt_apply_term.simps(2) ctxt_of_gctxt.elims eval_term.simps(2) term.sel(2))

       have xx: "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) terms = map to_term ss1 @ (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle> # map to_term ss2"
         using Fun(3)
         unfolding context\<^sub>G
         by auto

       then obtain ts1 "term" ts2 where 
          terms: "terms = ts1 @ term # ts2" and
          "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1"
          "map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2"
         by (smt (z3) append_eq_map_conv map_eq_Cons_conv)
          
       with xx have yy: "term \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = (to_context context\<^sub>G')\<langle>to_term term\<^sub>G\<^sub>1\<rangle>"
         by simp

       show ?case
       proof(cases "is_ground_term term")
         case True
         with yy obtain term\<^sub>1 context\<^sub>1 where zz: 
            "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
            "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G'" "is_Fun term\<^sub>1"
           by (metis Term.ground_vars_term_empty ground_context_is_ground ground_subst_apply ground_term_is_ground subst_ground_context gterm_is_fun)

         then have zzz: "Fun f terms = (More f ts1 context\<^sub>1 ts2)\<langle>term\<^sub>1\<rangle>"
           unfolding terms
           by auto

         have "\<exists>context\<^sub>1 term\<^sub>1. Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> is_Fun term\<^sub>1"
           apply(rule exI[of _ "(More f ts1 context\<^sub>1 ts2)"])
           apply(rule exI[of _ term\<^sub>1])
           using zz zzz
           by (auto simp add: \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)

         then show ?thesis
           using Fun(2)
           by blast
       next
         case False
         have zz: "term \<in> set terms"
           using terms by auto

         have zzz: "\<nexists>context\<^sub>1 term\<^sub>1. term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G' \<and> is_Fun term\<^sub>1"
         proof
           assume "\<exists>context\<^sub>1 term\<^sub>1. term = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G' \<and> is_Fun term\<^sub>1"
  
           then obtain context\<^sub>1 term\<^sub>1 where
              "term": "term = context\<^sub>1\<langle>term\<^sub>1\<rangle>"
              "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1"
              "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G'"
              "is_Fun term\<^sub>1"
             by blast

          then have zzzz: "Fun f terms = (More f ts1 context\<^sub>1 ts2)\<langle>term\<^sub>1\<rangle>"
           unfolding terms
           by auto

         have "\<exists>context\<^sub>1 term\<^sub>1. Fun f terms = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> is_Fun term\<^sub>1"
           apply(rule exI[of _ "(More f ts1 context\<^sub>1 ts2)"])
           apply(rule exI[of _ term\<^sub>1])
           by(auto simp: "term" terms \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)
           

          then show False
            using Fun(2)
            by blast
        qed

        obtain term\<^sub>x context\<^sub>x context\<^sub>x' where 
          term\<^sub>x: 
          "term = context\<^sub>x\<langle>term\<^sub>x\<rangle>"  
          "is_Var term\<^sub>x" 
          "(context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>) \<circ>\<^sub>c context\<^sub>x' = to_context context\<^sub>G'"
         using Fun(1)[OF zz zzz yy False] by blast

         show ?thesis
           apply(rule exI[of _ term\<^sub>x]) 
           apply(rule exI[of _ "(More f ts1 context\<^sub>x ts2)"])
           apply(rule exI[of _ context\<^sub>x'])
           by(auto simp: term\<^sub>x terms \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts1 = map to_term ss1\<close> \<open>map ((\<lambda>s. s \<cdot>t \<theta>) \<circ> (\<lambda>s. s \<cdot>t \<rho>\<^sub>1)) ts2 = map to_term ss2\<close> context\<^sub>G)
       qed
     qed
  
    then obtain term\<^sub>x context\<^sub>x context\<^sub>x' where
      context\<^sub>x: "term\<^sub>1_with_context = context\<^sub>x\<langle>term\<^sub>x\<rangle>"
      "is_Var term\<^sub>x"
      "(context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G"
      by (metis Subterm_and_Context.ctxt_ctxt_compose ground_context_is_ground ground_term_is_ground ground_term_with_context_is_ground2(2) subst_compose_ctxt_compose_distrib subst_ground_context sup_bot.right_neutral vars_term_ctxt_apply)

    then obtain var\<^sub>x where var\<^sub>x: "Var var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1"
      by (metis eval_term.simps(1) is_Var_def renaming(1) subst_cannot_add_var subst_compose_def term_subst.is_renaming_def)

    obtain \<theta>' where \<theta>':
      "\<theta>' = \<theta>(var\<^sub>x := (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>)"
      by simp

    have update_grounding: "is_ground_term (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      by (metis Subterm_and_Context.ctxt_ctxt_compose context\<^sub>x(3) ground_term_with_context_is_ground1 ground_term_with_context_is_ground2(2) subst_compose_ctxt_compose_distrib)

    have premise\<^sub>1_grounding': "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1 premise\<^sub>1_grounding by blast

    have \<theta>'_grounding: "is_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
      using ground_clause_subst_upd[OF update_grounding premise\<^sub>1_grounding']
      unfolding \<theta>'
      by blast
 
    let ?D = "to_ground_clause ((add_mset literal\<^sub>1 premise\<^sub>1') \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
    let ?DD = "{ ?D }"

    have term\<^sub>x_\<theta>: "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G"
      using term\<^sub>1_with_context_\<theta>
      unfolding context\<^sub>x(1)context\<^sub>x(3)[symmetric]
      apply auto
      by (metis ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) update_grounding to_term_inverse)

    have term\<^sub>x_\<theta>': "to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>') = (to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>))\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
      unfolding \<theta>'
      by (metis eval_term.simps(1) fun_upd_same ground_term_is_ground ground_term_with_context1 ground_term_with_context_is_ground2(1) update_grounding to_term_inverse var\<^sub>x)

    have premise\<^sub>1_\<theta>_x: "add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> =  add_mset (to_literal literal\<^sub>G\<^sub>1) (to_clause premise\<^sub>G\<^sub>1')"
      using premise\<^sub>1 premise\<^sub>1_\<theta> to_clause_add_mset by auto

    have entails: "\<And>I. refl I \<Longrightarrow>
         trans I \<Longrightarrow>
         sym I \<Longrightarrow>
         compatible_with_gctxt I \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D} \<Longrightarrow>
         (\<lambda>(x, y). Upair x y) ` I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
    proof-
      fix I :: "'f gterm rel"
      let ?I = "(\<lambda>(x, y). Upair x y) ` I"
  
      assume 
        refl: "refl I" and 
        trans: "trans I" and 
        sym: "sym I" and
        compatible_with_gctxt: "compatible_with_gctxt I" and
        premise: "?I \<TTurnstile>s {add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', ?D}"

      have var\<^sub>x_\<theta>_ground: "is_ground_term (Var var\<^sub>x \<cdot>t \<theta>)"
        by (metis context\<^sub>x(1) ground_term_is_ground ground_term_with_context3 ground_term_with_context_is_ground2(2) subst_apply_term_ctxt_apply_distrib term\<^sub>1_with_context_\<theta> var\<^sub>x)
        
      show "?I \<TTurnstile>s {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      proof(cases "?I \<TTurnstile> premise\<^sub>G\<^sub>2'")
        case True
        then show ?thesis 
          by auto
      next
        let ?x =  "to_ground_context (context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)"
        case False
        then have literal\<^sub>G\<^sub>2: "?I \<TTurnstile>l literal\<^sub>G\<^sub>2"
          using premise by blast

        then have "?I \<TTurnstile>l ?x\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G \<approx> ?x\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G"
          unfolding ground_superpositionI(6)
          using compatible_with_gctxt compatible_with_gctxt_def sym by auto

        then have "?I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')"
          using term\<^sub>x_\<theta> term\<^sub>x_\<theta>'
          by argo

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>')"
          using premise by fastforce

        then have "?I \<TTurnstile> to_ground_clause (add_mset literal\<^sub>1 premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
          using \<theta>'_grounding
          unfolding \<theta>'
          using interpretation_clause_congruence[OF trans sym compatible_with_gctxt update_grounding var\<^sub>x_\<theta>_ground]
          using \<open>(\<lambda>(x, y). Upair x y) ` I \<TTurnstile>l to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>) \<approx> to_ground_term (term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>')\<close> \<theta>' premise\<^sub>1_grounding' var\<^sub>x by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>1\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using ground_superpositionI(1) ground_superpositionI(5) premise\<^sub>1 by auto

       then have "?I \<TTurnstile> add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) premise\<^sub>G\<^sub>1'"
         using literal\<^sub>G\<^sub>2
         unfolding ground_superpositionI(6)
         (* TODO: Only place where ground soundness is used *)
         by (smt (verit) False compatible_with_gctxt ground.G_entails_def
             ground.soundness_ground_superposition ground_superposition ground_superpositionI(1)
             ground_superpositionI(12) ground_superpositionI(2) ground_superpositionI(5) local.refl
             local.sym local.trans premise true_cls_union true_clss_insert union_commute
             union_mset_add_mset_right)
  
        then show ?thesis 
          by blast
      qed
 
    qed
  
    have var\<^sub>x_\<theta>: "\<theta> var\<^sub>x = term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      using var\<^sub>x
      by simp

    have smaller': "((context\<^sub>x \<circ>\<^sub>c context\<^sub>x') \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t context\<^sub>x\<langle>term\<^sub>x\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"
      unfolding context\<^sub>x(3) context\<^sub>x(1)[symmetric]
      unfolding term\<^sub>1_with_context_\<theta>
      by (simp add: ground_superpositionI(8) less\<^sub>t_less\<^sub>t\<^sub>G)

    then have xx: "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> \<prec>\<^sub>t \<theta> var\<^sub>x"
      unfolding var\<^sub>x_\<theta>
      using less\<^sub>t_ground_context_compatible'[of "context\<^sub>x \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>" "(context\<^sub>x' \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta>)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>" "term\<^sub>x \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta>"]
      by (metis Subterm_and_Context.ctxt_ctxt_compose context\<^sub>x(1) ground_term_with_context_is_ground1 ground_term_with_context_is_ground2(1) ground_term_with_context_is_ground2(2) update_grounding subst_compose_ctxt_compose_distrib term\<^sub>1_with_context_\<theta> subst_apply_term_ctxt_apply_distrib)

    have xy: "var\<^sub>x \<in> vars_literal (literal\<^sub>1  \<cdot>l \<rho>\<^sub>1)"
      unfolding literal\<^sub>1 context\<^sub>x vars_literal_def vars_atom_def 
      using var\<^sub>x
      by(auto simp: subst_literal subst_atom)

    have "is_ground_literal (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>)"
      using literal\<^sub>1_grounding by force
    
    then have smaller: "literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>' \<prec>\<^sub>l literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<theta>"
      unfolding \<theta>'
      using less\<^sub>l_subst_upd[of _ \<theta>, OF update_grounding xx _ xy]
      by blast

    have premise\<^sub>1'_\<theta>_grounding: "is_ground_clause (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1'_\<theta>
      by simp

    have smaller_premise\<^sub>1': "premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>' \<preceq>\<^sub>c premise\<^sub>1' \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      unfolding \<theta>'
      using 
        less\<^sub>c_subst_upd[of _ \<theta>, OF update_grounding xx premise\<^sub>1'_\<theta>_grounding]
      by (metis (no_types, lifting) clause_subst_eq fun_upd_other reflclp_iff)

    from \<theta>'_grounding have "?D \<in> clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1')"
      unfolding clause_groundings_def clause_subst_compose[symmetric]
      by blast

    moreover have "?D \<prec>\<^sub>c\<^sub>G add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1'"
      unfolding less\<^sub>c\<^sub>G_less\<^sub>c to_ground_clause_inverse[OF \<theta>'_grounding] to_clause_add_mset
      unfolding literal\<^sub>1_\<theta>[symmetric]  subst_clause_add_mset premise\<^sub>1'_\<theta>[symmetric]
      using less\<^sub>c_add_mset[OF smaller smaller_premise\<^sub>1']
      by simp

    moreover have "ground.G_entails (insert (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2') ?DD) {add_mset (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G term\<^sub>G\<^sub>2)) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')}"
      unfolding ground.G_entails_def
      using entails
      by blast

    ultimately show ?thesis
      unfolding ground.redundant_infer_def
      by auto
  qed

  have z: "(to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))) = 
             (add_mset  (\<P>\<^sub>G (Upair context\<^sub>G\<langle>term\<^sub>G\<^sub>3\<rangle>\<^sub>G  term\<^sub>G\<^sub>2))) (premise\<^sub>G\<^sub>1' + premise\<^sub>G\<^sub>2')"
    by (smt (verit) ground_superpositionI(9) ground_term_with_context3 to_atom_to_literal(1) to_atom_to_literal(2) to_clause_add_mset to_clause_inverse to_clause_plus to_term_to_atom)  

  have x: "\<lbrakk>
     ground.ground_superposition (add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1') (add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2')
      (to_ground_clause
        (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')));

     \<not> ground.redundant_infer (clause_groundings (add_mset literal\<^sub>1 premise\<^sub>1') \<union> clause_groundings (add_mset literal\<^sub>2 premise\<^sub>2'))
         (Infer [add_mset literal\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>2', add_mset literal\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>1']
           (to_ground_clause
             (add_mset ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2'))))\<rbrakk>
    \<Longrightarrow> \<exists>context\<^sub>1 term\<^sub>1. term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle> \<and> context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G \<and> term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1 \<and> is_Fun term\<^sub>1"
    unfolding z
    using special_case
    by blast

  obtain context\<^sub>1 term\<^sub>1 where 
    term\<^sub>1_with_context: "term\<^sub>1_with_context = context\<^sub>1\<langle>term\<^sub>1\<rangle>" and
    term\<^sub>1_\<theta> : "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = to_term term\<^sub>G\<^sub>1" and
    context\<^sub>1_\<theta> : "context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1 \<cdot>t\<^sub>c \<theta> = to_context context\<^sub>G" and
    term\<^sub>1_not_Var: "\<not> is_Var term\<^sub>1"
    using not_redundant ground_superposition
    unfolding premise\<^sub>1_\<theta>
    unfolding premise\<^sub>2_\<theta>
    unfolding conclusion_\<theta>\<^sub>G
    unfolding premise\<^sub>1 premise\<^sub>2
    apply auto
    unfolding ground.Red_I_def
    apply auto
    unfolding ground.G_Inf_def
     apply blast
    by (metis special_case z)
 
  obtain term\<^sub>2'_with_context where
    term\<^sub>2'_with_context: 
      "term\<^sub>2'_with_context \<cdot>t \<theta> = (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle>"
      "term\<^sub>2'_with_context = (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle>" 
    unfolding term\<^sub>2'_\<theta>[symmetric]  context\<^sub>1_\<theta>[symmetric]
    by force

  have term_term': "term\<^sub>1 \<cdot>t \<rho>\<^sub>1 \<cdot>t \<theta> = term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<theta>"
    unfolding term\<^sub>1_\<theta> term\<^sub>2_\<theta>
    by(rule refl)

  then obtain \<sigma> \<tau> where \<sigma>: "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}" "\<theta> = \<sigma> \<odot> \<tau>"
    using imgu_exists
    by blast

  let ?conclusion' = "add_mset (?\<P> (Upair (term\<^sub>2'_with_context) (term\<^sub>1' \<cdot>t \<rho>\<^sub>1))) 
        (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  from conclusion_\<theta>\<^sub>G have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      subst_atom[symmetric]
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit, del_insts))+

  have superposition: "superposition premise\<^sub>2 premise\<^sub>1 ?conclusion'"
  proof(rule superpositionI)
    show "term_subst.is_renaming \<rho>\<^sub>1"
      using renaming(1).
  next
    show "term_subst.is_renaming \<rho>\<^sub>2"
      using renaming(2).
  next 
    show "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
     using renaming(3).
  next 
    show "premise\<^sub>1 = add_mset literal\<^sub>1 premise\<^sub>1'"
      using premise\<^sub>1.
  next
    show "premise\<^sub>2 = add_mset literal\<^sub>2 premise\<^sub>2'"
      using premise\<^sub>2.
  next
    show  "?\<P> \<in> {Pos, Neg}"
      by simp
  next
    show "literal\<^sub>1 = ?\<P> (Upair context\<^sub>1\<langle>term\<^sub>1\<rangle> term\<^sub>1')"
      unfolding literal\<^sub>1 term\<^sub>1_with_context..
  next
    show "literal\<^sub>2 = term\<^sub>2 \<approx> term\<^sub>2'"
      using literal\<^sub>2.
  next
    show "is_Fun term\<^sub>1"
      using term\<^sub>1_not_Var.
  next
    show "term_subst.is_imgu \<sigma> {{term\<^sub>1 \<cdot>t \<rho>\<^sub>1, term\<^sub>2 \<cdot>t \<rho>\<^sub>2}}"
      using \<sigma>(1).
  next
    note premises_to_ground_clause_inverse = assms(4, 5)[THEN to_ground_clause_inverse]  
    note premise_groundings = assms(5, 4)[unfolded \<sigma>(2) clause_subst_compose]
    
    have "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau> \<prec>\<^sub>c premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>"
      using ground_superpositionI(3)[
        unfolded less\<^sub>c\<^sub>G_less\<^sub>c premises_to_ground_clause_inverse, 
        unfolded \<sigma>(2) clause_subst_compose
        ].

    then show "\<not> premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<preceq>\<^sub>c premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>"
      using less\<^sub>c_less_eq\<^sub>c_ground_subst_stability[OF premise_groundings]
      by blast
  next
    show "?\<P> = Pos 
            \<and> select premise\<^sub>1 = {#} 
            \<and> is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
       \<or> ?\<P> = Neg 
            \<and> (select premise\<^sub>1 = {#} \<and> is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>) 
               \<or> literal\<^sub>1 \<in># select premise\<^sub>1)"
    proof(cases "?\<P> = Pos")
      case True
      moreover then have select_empty: "select premise\<^sub>1 = {#}"
        using clause_subst_empty select(1) ground_superpositionI(9) 
        by(auto simp: subst_clause_def)

      moreover have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
        using True pos_literal\<^sub>G\<^sub>1_is_strictly_maximal\<^sub>l
        unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
        by force

      moreover then have "is_strictly_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
        using 
          is_strictly_maximal\<^sub>l_ground_subst_stability'[OF
            _
            premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
          ]
          literal_in_clause_subst
          literal\<^sub>1_in_premise\<^sub>1
        by blast
        
      ultimately show ?thesis
        by auto
    next
      case \<P>_not_Pos: False
      then have \<P>\<^sub>G_Neg: "\<P>\<^sub>G = Neg"
        using ground_superpositionI(4)
        by fastforce

      show ?thesis
      proof(cases ?select\<^sub>G_empty)
        case select\<^sub>G_empty: True
    
        then have "select premise\<^sub>1 = {#}"
          using clause_subst_empty select(1) ground_superpositionI(9) \<P>\<^sub>G_Neg
          by auto

        moreover have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma> \<cdot> \<tau>)"
          using neg_literal\<^sub>G\<^sub>1_is_maximal\<^sub>l[OF \<P>\<^sub>G_Neg select\<^sub>G_empty]
          unfolding literal\<^sub>1_\<theta>[symmetric] \<sigma>(2)
          by simp
          
        moreover then have "is_maximal\<^sub>l (literal\<^sub>1 \<cdot>l \<rho>\<^sub>1 \<cdot>l \<sigma>) (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<sigma>)"
          using 
            is_maximal\<^sub>l_ground_subst_stability'[OF 
              _  
              premise\<^sub>1_grounding[unfolded \<sigma>(2) clause_subst_compose]
            ]
            literal_in_clause_subst
            literal\<^sub>1_in_premise\<^sub>1
          by blast

        ultimately show ?thesis
          using \<P>\<^sub>G_Neg
          by simp
      next
        case select\<^sub>G_not_empty: False
        have "literal\<^sub>1 \<in># select premise\<^sub>1"
          using literal\<^sub>1_selected[OF \<P>\<^sub>G_Neg select\<^sub>G_not_empty].
  
        with select\<^sub>G_not_empty \<P>\<^sub>G_Neg show ?thesis 
          by simp
      qed
    qed
  next
    show "select premise\<^sub>2 = {#}"
      using clause_subst_empty ground_superpositionI(10) select(2)
      by auto
  next 
    have "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma> \<cdot>l \<tau>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma> \<cdot> \<tau>)"
      using literal\<^sub>G\<^sub>2_is_strictly_maximal\<^sub>l
      unfolding literal\<^sub>2_\<theta>[symmetric]  \<sigma>(2)
      by simp

    then show "is_strictly_maximal\<^sub>l (literal\<^sub>2 \<cdot>l \<rho>\<^sub>2 \<cdot>l \<sigma>) (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<sigma>)"
      using 
        is_strictly_maximal\<^sub>l_ground_subst_stability'[OF 
          _  premise\<^sub>2_grounding[unfolded \<sigma>(2) clause_subst_compose]
        ]
        literal\<^sub>2_in_premise\<^sub>2 
        literal_in_clause_subst 
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>1_with_context[symmetric]  
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      using ground_term_with_context_is_ground(1)
      by simp_all

    have "term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(7) 
      unfolding 
        term\<^sub>1'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>1_with_context[symmetric]
        term\<^sub>1_with_context_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_def
        ground_term_with_context(3).
     
    then show "\<not> context\<^sub>1\<langle>term\<^sub>1\<rangle> \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>1' \<cdot>t \<rho>\<^sub>1 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    have term_groundings: 
      "is_ground_term (term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      "is_ground_term (term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>)" 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
      by simp_all

    have "term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau> \<prec>\<^sub>t term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<cdot>t \<tau>"
      using ground_superpositionI(8) 
      unfolding 
        term\<^sub>2_\<theta>[unfolded \<sigma>(2) term_subst_compose]             
        term\<^sub>2'_\<theta>[unfolded \<sigma>(2) term_subst_compose]
        less\<^sub>t\<^sub>G_def.

    then show "\<not> term\<^sub>2 \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma> \<preceq>\<^sub>t term\<^sub>2' \<cdot>t \<rho>\<^sub>2 \<cdot>t \<sigma>"
      using less\<^sub>t_less_eq\<^sub>t_ground_subst_stability[OF term_groundings]
      by blast
  next
    show "?conclusion' =  add_mset
     ((if \<P>\<^sub>G = Pos then Pos else Neg) (Upair (context\<^sub>1 \<cdot>t\<^sub>c \<rho>\<^sub>1)\<langle>term\<^sub>2' \<cdot>t \<rho>\<^sub>2\<rangle> (term\<^sub>1' \<cdot>t \<rho>\<^sub>1)))
     (premise\<^sub>1' \<cdot> \<rho>\<^sub>1 + premise\<^sub>2' \<cdot> \<rho>\<^sub>2) \<cdot> \<sigma>"
      using term\<^sub>2'_with_context(2) by blast
  qed

  have "term_subst.is_idem \<sigma>"
    using \<sigma>(1)
    by (simp add: term_subst.is_imgu_iff_is_idem_and_is_mgu)  

  then have \<sigma>_\<theta>: "\<sigma> \<odot> \<theta> = \<theta>"
    unfolding \<sigma>(2) term_subst.is_idem_def
    by simp

  have "to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>1"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>1_grounding)

  moreover have "to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>) \<in> clause_groundings premise\<^sub>2"
    unfolding clause_groundings_def
    by (smt (verit, del_insts) clause_subst_compose mem_Collect_eq premise\<^sub>2_grounding)

  moreover have "conclusion \<cdot> \<theta> = 
    add_mset (?\<P> (Upair (to_context context\<^sub>G)\<langle>to_term term\<^sub>G\<^sub>3\<rangle> (to_term term\<^sub>G\<^sub>2))) 
      (to_clause premise\<^sub>G\<^sub>1' + to_clause premise\<^sub>G\<^sub>2')"
    using ground_superpositionI(4, 12) to_ground_clause_inverse[OF conclusion_grounding] 
    unfolding ground_term_with_context(3) to_term_to_atom
    by(cases "\<P>\<^sub>G = Pos")(simp_all add: to_atom_to_literal to_clause_add_mset)

  then have conclusion_\<theta>: "conclusion \<cdot> \<theta> =  ?conclusion' \<cdot> \<theta>"
    unfolding 
      term\<^sub>2'_with_context[symmetric]
      premise\<^sub>1'_\<theta>[symmetric] 
      premise\<^sub>2'_\<theta>[symmetric] 
      term\<^sub>1'_\<theta>[symmetric]
      subst_clause_plus[symmetric] 
      subst_apply_term_ctxt_apply_distrib[symmetric]
      subst_atom[symmetric]
    apply(cases "\<P>\<^sub>G = Pos")
    using subst_clause_add_mset subst_literal \<sigma>_\<theta> clause_subst_compose
    by (smt (verit))+
    
  have "to_ground_clause (conclusion \<cdot> \<theta>) \<in> clause_groundings ?conclusion'"
    unfolding clause_groundings_def
    by (smt (verit, best) conclusion_\<theta> conclusion_grounding mem_Collect_eq)

  (* TODO: *)
  ultimately show ?thesis
    unfolding clause_groundings_def inference_groundings_def ground.G_Inf_def inferences_def
    using superposition
    apply simp
    by (metis conclusion_\<theta> conclusion_grounding ground_superposition premise\<^sub>1_grounding premise\<^sub>2_grounding renaming)
qed

end

context grounded_first_order_superposition_calculus
begin

(* TODO: Probably it is easier to combine these with the above ones or have a generic way for 
    converting the formats
*)
lemma equality_resolution_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_resolution_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))"
    (* TODO: Create definition or abbreviation for this *)
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises"
  shows "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_resolution: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_resolution: "equality_resolution premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_resolution_ground_instance[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_resolution[unfolded premise\<^sub>G conclusion\<^sub>G]
      ]
    by blast

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_resolution
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed 

lemma equality_factoring_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.equality_factoring_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises"
  shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G] conclusion\<^sub>G" and
    ground_eq_factoring: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"
    using assms(1)
    by blast

  have premise\<^sub>G_in_groundings: "premise\<^sub>G \<in>  \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp
  
  obtain premise conclusion \<theta> where
    "to_clause premise\<^sub>G = premise \<cdot> \<theta>" and
    "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>" and
    select: "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>" and
    premise_in_premises: "premise \<in> premises"
    using assms(2, 3) premise\<^sub>G_in_groundings
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by (metis (no_types, opaque_lifting) ground_clause_is_ground subst_ground_clause)
    
  then have 
    premise_grounding: "is_ground_clause (premise \<cdot> \<theta>)" and 
    premise\<^sub>G: "premise\<^sub>G = to_ground_clause (premise \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    by (smt ground_clause_is_ground to_clause_inverse)+
   
  obtain conclusion' where 
    equality_factoring: "equality_factoring premise conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise \<cdot> \<theta>)] (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
    using 
      equality_factoring_ground_instance[OF 
        premise_grounding 
        conclusion_grounding 
        select 
        ground_eq_factoring[unfolded premise\<^sub>G conclusion\<^sub>G]
      ]
    by blast

  let ?\<iota> = "Infer [premise] conclusion'"

  have "?\<iota> \<in> Inf_from premises"
    using premise_in_premises  equality_factoring
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)

  ultimately show ?thesis
    by blast
qed

lemma superposition_ground_instance': 
  assumes 
    "\<iota>\<^sub>G \<in> ground.superposition_inferences"
    "\<iota>\<^sub>G \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota>\<^sub>G \<notin> ground.GRed_I (\<Union> (clause_groundings ` premises))"
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
   shows  "\<exists>\<iota> \<in> Inf_from premises. \<iota>\<^sub>G \<in> inference_groundings \<iota>"
proof-
  obtain premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G where 
    \<iota>\<^sub>G : "\<iota>\<^sub>G = Infer [premise\<^sub>G\<^sub>2, premise\<^sub>G\<^sub>1] conclusion\<^sub>G" and
    ground_superposition: "ground.ground_superposition premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G"
    using assms(1)
    by blast

  have 
    premise\<^sub>G\<^sub>1_in_groundings: "premise\<^sub>G\<^sub>1 \<in> \<Union> (clause_groundings ` premises)" and  
    premise\<^sub>G\<^sub>2_in_groundings: "premise\<^sub>G\<^sub>2 \<in> \<Union> (clause_groundings ` premises)"
    using assms(2)
    unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
    by simp_all

  obtain premise\<^sub>1 premise\<^sub>2 \<theta>\<^sub>1 \<theta>\<^sub>2 where
    premise\<^sub>1_\<theta>\<^sub>1: "premise\<^sub>1 \<cdot> \<theta>\<^sub>1 = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>\<^sub>2: "premise\<^sub>2 \<cdot> \<theta>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2" and
    select': 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<theta>\<^sub>1))) = select premise\<^sub>1 \<cdot> \<theta>\<^sub>1"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<theta>\<^sub>2))) = select premise\<^sub>2 \<cdot> \<theta>\<^sub>2" and
    premise\<^sub>1_in_premises: "premise\<^sub>1 \<in> premises" and
    premise\<^sub>2_in_premises: "premise\<^sub>2 \<in> premises"
     using assms(2, 4) premise\<^sub>G\<^sub>1_in_groundings premise\<^sub>G\<^sub>2_in_groundings
     unfolding \<iota>\<^sub>G ground.Inf_from_q_def ground.Inf_from_def
     by (metis (no_types, lifting))

  obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where
    renaming: 
      "term_subst.is_renaming (\<rho>\<^sub>1 :: ('f, 'v) subst)" 
      "term_subst.is_renaming \<rho>\<^sub>2" 
      "\<rho>\<^sub>1 ` vars_clause premise\<^sub>1 \<inter> \<rho>\<^sub>2 ` vars_clause premise\<^sub>2 = {}"
    using clause_renaming_exists[of premise\<^sub>1 premise\<^sub>2]. 

  (* TODO: *)
  then have vars_distinct: "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
    using test_clause[symmetric] term_subst_is_renaming_iff[of \<rho>\<^sub>1]  term_subst_is_renaming_iff[of \<rho>\<^sub>2]  
    by (smt (verit, del_insts) disjoint_iff imageI)

  from renaming obtain \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv where
     \<rho>\<^sub>1_inv: "\<rho>\<^sub>1 \<odot> \<rho>\<^sub>1_inv = Var" and
     \<rho>\<^sub>2_inv: "\<rho>\<^sub>2 \<odot> \<rho>\<^sub>2_inv = Var"
    unfolding term_subst.is_renaming_def
    by blast

  have select_subset: "select premise\<^sub>1 \<subseteq># premise\<^sub>1" "select premise\<^sub>2 \<subseteq># premise\<^sub>2"
    by (simp_all add: select_subset)

  then have a: "select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<subseteq># premise\<^sub>1 \<cdot> \<rho>\<^sub>1"  "select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<subseteq># premise\<^sub>2 \<cdot> \<rho>\<^sub>2"
    by (simp_all add: image_mset_subseteq_mono subst_clause_def)

  have "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<subseteq> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2)"
    using vars_clause_subset[OF a(2)].

  then have b: "vars_clause (select premise\<^sub>2 \<cdot> \<rho>\<^sub>2) \<inter> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) = {}"
    using vars_distinct
    by blast

  obtain \<theta> where "\<theta> = (\<lambda>var. 
      if var \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) 
      then (\<rho>\<^sub>1_inv \<odot> \<theta>\<^sub>1) var 
      else (\<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2) var
    )"
    by simp

  then have 
    premise\<^sub>1_\<theta>: "premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>1" and
    premise\<^sub>2_\<theta>: "premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta> = to_clause premise\<^sub>G\<^sub>2" and
    select: 
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>"
    using premise\<^sub>1_\<theta>\<^sub>1 premise\<^sub>2_\<theta>\<^sub>2 select' 
       apply auto

    unfolding clause_subst_if clause_subst_if_2[rule_format, OF vars_distinct]  clause_subst_if_2[rule_format, OF vars_distinct]
    using \<rho>\<^sub>1_inv \<rho>\<^sub>2_inv clause_subst_if_2[of "premise\<^sub>2 \<cdot> \<rho>\<^sub>2" "premise\<^sub>1 \<cdot> \<rho>\<^sub>2"]
       apply (metis (mono_tags, lifting) clause_subst_compose subst_clause_Var_ident)
      apply (metis (no_types) \<rho>\<^sub>2_inv clause_subst_compose clause_subst_if_2 inf_commute vars_distinct subst_clause_Var_ident)
    unfolding clause_subst_if'[OF a(1)]  clause_subst_if_2[rule_format, OF b]
    apply (metis (no_types, lifting) \<rho>\<^sub>1_inv clause_subst_compose select'(1) subst_clause_Var_ident)
  proof -
    assume a1: "premise\<^sub>2 \<cdot> \<theta>\<^sub>2 = to_clause premise\<^sub>G\<^sub>2"
    assume a2: "to_clause (select\<^sub>G premise\<^sub>G\<^sub>2) = select premise\<^sub>2 \<cdot> \<theta>\<^sub>2"
    have "\<forall>m f. m \<cdot> f = m \<cdot> \<rho>\<^sub>2 \<odot> (\<rho>\<^sub>2_inv \<odot> f)"
      by (simp add: \<rho>\<^sub>2_inv)
    then show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> (\<lambda>b. if b \<in> vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) then (\<rho>\<^sub>1_inv \<odot> \<theta>\<^sub>1) b else (\<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2) b)))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<rho>\<^sub>2_inv \<odot> \<theta>\<^sub>2"
      using a2 a1 by (simp add: clause_subst_if_2 inf_commute vars_distinct)
  qed

  obtain conclusion where conclusion_\<theta>: "to_clause conclusion\<^sub>G = conclusion \<cdot> \<theta>"
    by (metis ground_clause_is_ground subst_ground_clause)
   
  then have 
    premise\<^sub>1_grounding: "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>2_grounding: "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>1: "premise\<^sub>G\<^sub>1 = to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)" and 
    premise\<^sub>G\<^sub>2: "premise\<^sub>G\<^sub>2 = to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)" and 
    conclusion_grounding: "is_ground_clause (conclusion \<cdot> \<theta>)" and
    conclusion\<^sub>G: "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
    apply (simp_all add: premise\<^sub>1_\<theta> premise\<^sub>2_\<theta>)
    by (smt ground_clause_is_ground to_clause_inverse)+

  have "clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2 \<subseteq> \<Union> (clause_groundings ` premises)"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises by blast

  then have Infer_not_GRed_I:
    "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
      (to_ground_clause (conclusion \<cdot> \<theta>)) \<notin>
      ground.GRed_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
    using assms(3) ground.Red_I_of_subset
    unfolding \<iota>\<^sub>G  premise\<^sub>G\<^sub>1[symmetric] premise\<^sub>G\<^sub>2[symmetric] conclusion\<^sub>G[symmetric]
    by blast

  have "\<exists>conclusion'. superposition premise\<^sub>2 premise\<^sub>1 conclusion' \<and>
    Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
      (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion') \<and>
    conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
  proof (rule superposition_ground_instance)
    show "term_subst.is_renaming \<rho>\<^sub>1"
      using renaming by argo
  next
    show "term_subst.is_renaming \<rho>\<^sub>2"
      using renaming by argo
  next
    show "vars_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1) \<inter> vars_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2) = {}"
      using vars_distinct .
  next
    show "is_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)"
      using premise\<^sub>1_grounding .
  next
    show "is_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>)"
      using premise\<^sub>2_grounding .
  next
    show "is_ground_clause (conclusion \<cdot> \<theta>)"
      using conclusion_grounding .
  next
    show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))) = select premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>"
      using select by argo
  next
    show "to_clause (select\<^sub>G (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))) = select premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>"
      using select by argo
  next
    show "ground.ground_superposition
      (to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>))
      (to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>))
      (to_ground_clause (conclusion \<cdot> \<theta>))"
      using ground_superposition unfolding premise\<^sub>G\<^sub>2 premise\<^sub>G\<^sub>1 conclusion\<^sub>G .
  next
    show "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
     (to_ground_clause (conclusion \<cdot> \<theta>))
    \<notin> ground.GRed_I (clause_groundings premise\<^sub>1 \<union> clause_groundings premise\<^sub>2)"
      using Infer_not_GRed_I .
  qed

 then obtain conclusion' where 
    superposition: "superposition premise\<^sub>2 premise\<^sub>1 conclusion'" and
    inference_groundings: 
      "Infer [to_ground_clause (premise\<^sub>2 \<cdot> \<rho>\<^sub>2 \<cdot> \<theta>), to_ground_clause (premise\<^sub>1 \<cdot> \<rho>\<^sub>1 \<cdot> \<theta>)]
        (to_ground_clause (conclusion' \<cdot> \<theta>)) \<in> 
        inference_groundings (Infer [premise\<^sub>2, premise\<^sub>1] conclusion')" and  
    conclusion'_conclusion: "conclusion' \<cdot> \<theta> = conclusion \<cdot> \<theta>"
   by metis

   let ?\<iota> = "Infer [premise\<^sub>2, premise\<^sub>1] conclusion'"

   have "?\<iota> \<in> Inf_from premises"
    using premise\<^sub>1_in_premises premise\<^sub>2_in_premises superposition
    unfolding Inf_from_def inferences_def inference_system.Inf_from_def
    by simp

  moreover have "\<iota>\<^sub>G \<in> inference_groundings ?\<iota>"
    unfolding \<iota>\<^sub>G premise\<^sub>G\<^sub>1 premise\<^sub>G\<^sub>2 conclusion\<^sub>G conclusion'_conclusion[symmetric]
    by(rule inference_groundings)


  ultimately show ?thesis
    by blast
qed

lemma ground_instances: 
  assumes 
    "\<iota> \<in> ground.Inf_from_q select\<^sub>G (\<Union> (clause_groundings ` premises))" 
    "\<iota> \<notin> ground.Red_I (\<Union> (clause_groundings ` premises))"
    "\<forall>premise\<^sub>G \<in> \<Union> (clause_groundings ` premises). \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
      \<and> premise \<in> premises"
  shows "\<exists>\<iota>'\<in>Inf_from premises. \<iota> \<in> inference_groundings \<iota>'"
proof-
  have "\<iota> \<in> ground.superposition_inferences \<or>
        \<iota> \<in> ground.equality_resolution_inferences \<or>
        \<iota> \<in> ground.equality_factoring_inferences"
    using assms(1)
    unfolding 
      ground.Inf_from_q_def 
      ground.Inf_from_def 
      ground.G_Inf_def 
      inference_system.Inf_from_def
    by auto

  then show ?thesis
    using 
      assms
      equality_resolution_ground_instance'
      equality_factoring_ground_instance'
      superposition_ground_instance'
    by presburger
qed

end

lemma for_all_elements_exists_f_implies_f_exists_for_all_elements: 
  "\<forall>x \<in> X. \<exists>f. P (f x) x \<Longrightarrow> \<exists>f. \<forall>x\<in> X. P (f x) x"
  by meson

lemma (in first_order_superposition_calculus) necessary_select\<^sub>G_exists:
  obtains select\<^sub>G where 
      "\<forall>premise\<^sub>G \<in> \<Union>(clause_groundings ` premises). \<exists>premise \<theta>. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((select premise) \<cdot> \<theta>)
        \<and> premise \<in> premises" 
      "is_grounding select\<^sub>G" 
proof-
  let ?premise_groundings = "\<Union>(clause_groundings ` premises)"
  
  have select\<^sub>G_exists_for_premises: "\<forall>premise\<^sub>G \<in> ?premise_groundings. \<exists>select\<^sub>G premise \<theta>.
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> select\<^sub>G premise\<^sub>G = to_ground_clause ((select premise) \<cdot> \<theta>)
        \<and> premise \<in> premises"
    unfolding clause_groundings_def
    by fastforce

  obtain select\<^sub>G_on_premise_groundings where 
    select\<^sub>G_on_premise_groundings: "\<forall>premise\<^sub>G \<in>?premise_groundings. \<exists>\<theta> premise. 
        premise \<cdot> \<theta> = to_clause premise\<^sub>G 
      \<and> select\<^sub>G_on_premise_groundings (to_ground_clause (premise \<cdot> \<theta>)) = 
          to_ground_clause ((select premise) \<cdot> \<theta>)
      \<and> premise \<in> premises"
    using 
      for_all_elements_exists_f_implies_f_exists_for_all_elements[OF select\<^sub>G_exists_for_premises]
    by (metis (mono_tags, opaque_lifting) to_clause_inverse)
 
  define select\<^sub>G where
    select\<^sub>G_def: "\<And>clause\<^sub>G. select\<^sub>G clause\<^sub>G = (
        if clause\<^sub>G  \<in> ?premise_groundings 
        then select\<^sub>G_on_premise_groundings clause\<^sub>G 
        else select\<^sub>G_simple clause\<^sub>G
    )"

  have "is_grounding select\<^sub>G" 
    unfolding is_select_grounding_def select\<^sub>G_def select\<^sub>G_simple_def
    using select\<^sub>G_on_premise_groundings
    by (metis ground_clause_is_ground subst_clause_Var_ident to_clause_inverse)
  
  then show ?thesis
    using select\<^sub>G_def select\<^sub>G_on_premise_groundings that 
    by (metis to_clause_inverse)
qed

lemma (in first_order_superposition_calculus) ground_instances:
  obtains select\<^sub>G where
    "ground_Inf_overapproximated select\<^sub>G premises"
    "is_grounding select\<^sub>G"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_Inf_overapproximated select\<^sub>G premises \<Longrightarrow> is_grounding select\<^sub>G \<Longrightarrow> thesis"

  obtain select\<^sub>G where   
      select\<^sub>G': "\<forall>premise\<^sub>G \<in> \<Union>(clause_groundings ` premises). \<exists>\<theta> premise. 
          premise \<cdot> \<theta> = to_clause premise\<^sub>G 
        \<and> to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = (select premise) \<cdot> \<theta>
        \<and> premise \<in> premises" and
       "is_grounding select\<^sub>G" 
    using necessary_select\<^sub>G_exists
    by (metis (mono_tags, opaque_lifting) ground_clause_is_ground select_subst1 to_clause_inverse to_ground_clause_inverse)

  then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
    apply unfold_locales.

  from select\<^sub>G'(1) have "ground_Inf_overapproximated select\<^sub>G premises"
    using ground_instances  
    by auto

  with assumption select\<^sub>G show thesis
    by blast
qed

sublocale first_order_superposition_calculus \<subseteq> 
  statically_complete_calculus "\<bottom>\<^sub>F" inferences entails_\<G> Red_I_\<G> Red_F_\<G>
  unfolding static_empty_ord_inter_equiv_static_inter
proof(rule stat_ref_comp_to_non_ground_fam_inter)
  (* TODO *)
  show "\<forall>q\<in>select\<^sub>G\<^sub>s.
    statically_complete_calculus 
      {{#}}                           
      (ground_superposition_calculus.G_Inf (\<prec>\<^sub>t\<^sub>G) q)
      ground_superposition_calculus.G_entails 
      (ground_superposition_calculus.GRed_I (\<prec>\<^sub>t\<^sub>G) q)
      (ground_superposition_calculus.GRed_F (\<prec>\<^sub>t\<^sub>G))"
  proof
    fix select\<^sub>G
    assume "select\<^sub>G \<in> select\<^sub>G\<^sub>s"
    then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
      apply unfold_locales
      unfolding select\<^sub>G\<^sub>s_def
      by simp

    show "statically_complete_calculus 
            ground.G_Bot 
            ground.G_Inf 
            ground.G_entails 
            ground.Red_I 
            ground.Red_F"
      using ground.statically_complete_calculus_axioms by blast
  qed
next
  (* TODO: Why don't we need the saturated precondition? *)
  have "\<And>N. \<exists>q \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated q N" 
    using ground_instances
    by (smt (verit, ccfv_threshold) mem_Collect_eq select\<^sub>G\<^sub>s_def)
    
  then show "\<And>N. empty_ord.saturated N \<Longrightarrow> \<exists>q \<in> select\<^sub>G\<^sub>s. ground_Inf_overapproximated q N".
qed 






(* ---------END----------------------- *)

(* TODO: Can these be useful for something? *)

context lifting_intersection
begin

abbreviation ground_instances ::
  "'q \<Rightarrow> 'f inference set \<Rightarrow> 'g inference set" where
  "ground_instances q inferences \<equiv> { ground_inference. 
    ground_inference \<in> Inf_G_q q \<and> ground_inference \<in>  \<Union> (Option.these (\<G>_I_q q ` inferences))
  }"

end

(* TODO: These are actually not needed *)
context first_order_superposition_calculus
begin

(* TODO: *)
lemma equality_resolution_ground_instance_TODO:
  obtains select\<^sub>G where "ground_superposition_calculus.equality_resolution_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
          \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_superposition_calculus.equality_resolution_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
         \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences \<Longrightarrow> thesis"
  
  obtain select\<^sub>G where "is_grounding select\<^sub>G"
    using select\<^sub>G_simple by blast

  then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
    apply unfold_locales.

  have "\<And>premise\<^sub>G conclusion\<^sub>G. ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G \<Longrightarrow>
           \<exists>premise conclusion. equality_resolution premise conclusion \<and>
               Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion)"
  proof-
    fix premise\<^sub>G conclusion\<^sub>G
    assume a: "ground.ground_eq_resolution premise\<^sub>G conclusion\<^sub>G"

    obtain premise \<theta> conclusion where y:
      "premise\<^sub>G = to_ground_clause ((premise :: ('f, 'v) atom clause) \<cdot> \<theta>)" 
      "is_ground_clause (premise \<cdot> \<theta>)"
      "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
      "is_ground_clause (conclusion \<cdot> \<theta>)"
      "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>"
      using select\<^sub>G
      unfolding is_select_grounding_def
      by (metis select_subst1 subst_ground_clause to_ground_clause_inverse)
      
    show "\<exists>premise conclusion. equality_resolution premise conclusion 
            \<and> Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion)"
      using equality_resolution_ground_instance[OF y(2) y(4) y(5) a[unfolded y(1, 3)]] 
      using y(1) y(3) by fastforce
  qed

  (* TODO *)
  then have "ground.equality_resolution_inferences \<subseteq> ground_instances select\<^sub>G equality_resolution_inferences"
    apply auto
    using inference_groundings_def apply blast
    by (smt (verit, del_insts) image_iff in_these_eq mem_Collect_eq)

  then show ?thesis
    using assumption
    by blast
qed

(* TODO: *)
lemma equality_factoring_ground_instance_TODO:
  obtains select\<^sub>G where "ground_superposition_calculus.equality_factoring_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
          \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences"
      "is_grounding select\<^sub>G"
proof-
  assume assumption: 
    "\<And>select\<^sub>G. ground_superposition_calculus.equality_factoring_inferences (\<prec>\<^sub>t\<^sub>G) select\<^sub>G 
         \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences \<Longrightarrow> is_grounding select\<^sub>G \<Longrightarrow> thesis"
  
  obtain select\<^sub>G where "is_grounding select\<^sub>G"
    using select\<^sub>G_simple by blast

  then interpret grounded_first_order_superposition_calculus _ _ select\<^sub>G
    apply unfold_locales.

  have "\<And>premise\<^sub>G conclusion\<^sub>G. ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G \<Longrightarrow>
           \<exists>premise conclusion. equality_factoring premise conclusion \<and>
               Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion)"
  proof-
    fix premise\<^sub>G conclusion\<^sub>G
    assume a: "ground.ground_eq_factoring premise\<^sub>G conclusion\<^sub>G"

    obtain premise \<theta> conclusion where y:
      "premise\<^sub>G = to_ground_clause ((premise :: ('f, 'v) atom clause) \<cdot> \<theta>)" 
      "is_ground_clause (premise \<cdot> \<theta>)"
      "conclusion\<^sub>G = to_ground_clause (conclusion \<cdot> \<theta>)"
      "is_ground_clause (conclusion \<cdot> \<theta>)"
      "to_clause (select\<^sub>G (to_ground_clause (premise \<cdot> \<theta>))) = select premise \<cdot> \<theta>"
      using select\<^sub>G
      unfolding is_select_grounding_def
      by (metis select_subst1 subst_ground_clause to_ground_clause_inverse)
      
    show "\<exists>premise conclusion. equality_factoring premise conclusion 
            \<and> Infer [premise\<^sub>G] conclusion\<^sub>G \<in> inference_groundings (Infer [premise] conclusion)"
      using equality_factoring_ground_instance[OF y(2) y(4) y(5) a[unfolded y(1, 3)]] 
      using y(1) y(3) by fastforce
  qed

  (* TODO *)
  then have "ground.equality_factoring_inferences \<subseteq> ground_instances select\<^sub>G equality_factoring_inferences"
    apply auto
    using inference_groundings_def select\<^sub>G apply blast
    by (smt (verit, del_insts) image_iff in_these_eq mem_Collect_eq)

  then show ?thesis
    using assumption select\<^sub>G
    by blast
qed

end

end