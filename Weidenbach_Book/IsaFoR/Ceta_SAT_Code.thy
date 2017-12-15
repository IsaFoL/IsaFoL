theory Ceta_SAT_Code
  imports CeTA_SAT_Slow.Ceta_SAT
begin

abbreviation (input)ABS6 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f" (binder "\<lambda>\<^sub>6" 10)
  where "ABS6 f \<equiv> (\<lambda>x y z a b. PROTECT2 (f x y z a b) DUMMY)"

abbreviation (input)ABS7 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g" (binder "\<lambda>\<^sub>7" 10)
  where "ABS7 f \<equiv> (\<lambda>x y z a b c. PROTECT2 (f x y z a b c) DUMMY)"
abbreviation (input)ABS8 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g\<Rightarrow>'h)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g\<Rightarrow>'h" (binder "\<lambda>\<^sub>8" 10)
  where "ABS8 f \<equiv> (\<lambda>x y z a b c d. PROTECT2 (f x y z a b c d) DUMMY)"

declare dp_termination_proof_assn.simps[simp del]

lemma hn_dp_termination_proof_assn:
    "dp_termination_proof_assn x y = z \<Longrightarrow> hn_ctxt (dp_termination_proof_assn) x y = z"
  by (simp add: hn_ctxt_def)

method hn_case_proof_internal uses ccase merge =
  (rule hn_refine_cons[OF _ ccase _ entt_refl],
   solves \<open>simp add: assn_times_comm entt_fr_drop\<close>,
   assumption,
   assumption,
   rule entt_star_mono,
     rule entt_fr_drop,
     subst dp_termination_proof_assn.simps[THEN hn_dp_termination_proof_assn],
     solves \<open>simp add: hn_ctxt_def\<close>,
  rule entt_trans[OF _ merge],
  solves \<open>simp add: entt_disjI1' entt_disjI2'\<close>)

method hn_case_proof uses ccase merge =
  (hn_case_proof_internal ccase:ccase merge:merge; fail)

lemma hn_case_dp_termination_proof_assn[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (dp_termination_proof_assn) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (dp_termination_proof_assn) p p' * F"
  assumes P_is_Empty: "p=P_is_Empty \<Longrightarrow>
      hn_refine (hn_ctxt (dp_termination_proof_assn) p p' * F) f1'
        (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
 assumes Subterm_Criterion_Proc:
    "\<And>projL rseqL trsLL term projL' rseqL' trsLL' term'. \<lbrakk>p=Subterm_Criterion_Proc projL rseqL trsLL term;
       p'= Subterm_Criterion_Proc projL' rseqL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f2' projL' rseqL' trsLL' term')
       (projL_assn (lab_assn id_assn id_assn) projL projL' *
    rseqL_assn id_assn id_assn id_assn  rseqL rseqL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 projL rseqL trsLL term)"
 assumes Gen_Subterm_Criterion_Proc:
    "\<And>projL rseqL trsLL term projL' trsLL' term'. \<lbrakk>p=Gen_Subterm_Criterion_Proc projL trsLL term;
       p'= Gen_Subterm_Criterion_Proc projL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f3' projL' trsLL' term')
       (status_impl_assn (lab_assn id_assn id_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX3 p p' * \<Gamma>3') R (f3 projL trsLL term)"
 assumes Redpair_Proc:
    "\<And> projL trsLL term projL' trsLL' term'. \<lbrakk>p=Redpair_Proc projL trsLL term;
       p'= Redpair_Proc projL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f4' projL' trsLL' term')
       ((root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX4 p p' * \<Gamma>4') R (f4 projL trsLL term)"
 assumes Redpair_UR_Proc:
    "\<And> projL trsLL trsLL2 term  projL' trsLL' trsLL2' term'. \<lbrakk>p=Redpair_UR_Proc projL trsLL trsLL2 term;
       p'= Redpair_UR_Proc  projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f5' projL' trsLL' trsLL2' term')
       ((root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX5 p p' * \<Gamma>5') R (f5 projL trsLL trsLL2 term)"
 assumes Usable_Rules_Proc:
    "\<And>trsLL term trsLL' term'. \<lbrakk>p=Usable_Rules_Proc trsLL term;
       p'= Usable_Rules_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f6' trsLL' term')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX6 p p' * \<Gamma>6') R (f6 trsLL term)"
 assumes Dep_Graph_Proc:
    "\<And>term term'. \<lbrakk>p=Dep_Graph_Proc term;
       p'= Dep_Graph_Proc term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f7' term')
       (list_assn (option_assn dp_termination_proof_assn *a
      trsLL_assn id_assn id_assn id_assn) term term' * hn_ctxt XX7 p p' * \<Gamma>7') R (f7 term)"
 assumes Mono_Redpair_Proc:
    "\<And>projL trsLL trsLL2 term projL' trsLL' trsLL2' term'. \<lbrakk>p=Mono_Redpair_Proc projL trsLL trsLL2 term;
       p'= Mono_Redpair_Proc projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f8' projL' trsLL' trsLL2' term')
       (redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX8 p p' * \<Gamma>8') R (f8 projL trsLL trsLL2 term)"
assumes Mono_URM_Redpair_Proc:
    "\<And>projL trsLL trsLL2 term projL' trsLL' trsLL2' term'. \<lbrakk>p=Mono_URM_Redpair_Proc projL trsLL trsLL2 term;
       p'= Mono_URM_Redpair_Proc projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f9' projL' trsLL' trsLL2' term')
       (redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX9 p p' * \<Gamma>9') R (f9 projL trsLL trsLL2 term)"
assumes Mono_Redpair_UR_Proc:
    "\<And>projL trsLL trsLL2 trsLL3 term projL' trsLL' trsLL2' trsLL3' term'.
     \<lbrakk>p=Mono_Redpair_UR_Proc projL trsLL trsLL2 trsLL3 term;
       p'= Mono_Redpair_UR_Proc projL' trsLL' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f10' projL' trsLL' trsLL2' trsLL3' term')
       (id_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' * hn_ctxt XX10 p p' * \<Gamma>10') R (f10 projL trsLL trsLL2 trsLL3 term)"
  assumes Size_Change_Subterm_Proc:
  "\<And>term term'. \<lbrakk>p=Size_Change_Subterm_Proc term;
       p'= Size_Change_Subterm_Proc term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f11' term')
       ( list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term' * hn_ctxt XX11 p p' * \<Gamma>11') R (f11 term)"
  assumes Size_Change_Redpair_Proc:
  "\<And>red trsLL term  red' trsLL' term'. \<lbrakk>p=Size_Change_Redpair_Proc  red trsLL term;
       p'= Size_Change_Redpair_Proc  red' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f12'  red' trsLL' term')
       (redtriple_impl_assn red red' * option_assn (trsLL_assn id_assn id_assn id_assn) trsLL trsLL' *
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term' *
        hn_ctxt XX12 p p' * \<Gamma>12') R (f12  red trsLL term)"
  assumes Uncurry_Proc:
  "\<And>n unc trsLL2 trsLL3 term n' unc' trsLL2' trsLL3' term'. \<lbrakk>p=Uncurry_Proc n unc trsLL2 trsLL3 term;
       p'= Uncurry_Proc n' unc' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f13' n' unc' trsLL2' trsLL3' term')
       (option_assn nat_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX13 p p' * \<Gamma>13') R (f13 n unc trsLL2 trsLL3 term)"
  assumes Fcc_Proc:
  "\<And>n unc trsLL2 trsLL3 term n' unc' trsLL2' trsLL3' term'. \<lbrakk>p=Fcc_Proc n unc trsLL2 trsLL3 term;
       p'= Fcc_Proc n' unc' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f14' n' unc' trsLL2' trsLL3' term')
       (lab_assn id_assn id_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX14 p p' * \<Gamma>14') R (f14 n unc trsLL2 trsLL3 term)"
  assumes Split_Proc:
  "\<And>trsLL trsLL2 term term2 trsLL' trsLL2' term' term2'. \<lbrakk>p=Split_Proc trsLL trsLL2 term term2;
       p'= Split_Proc trsLL' trsLL2' term' term2'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f15' trsLL' trsLL2' term' term2')
       ( trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
    dp_termination_proof_assn term2 term2' *
        hn_ctxt XX15 p p' * \<Gamma>15') R (f15 trsLL trsLL2 term term2)"
  assumes Semlab_Proc:
  "\<And> sl  trsLL2 unc trsLL3 term  sl' trsLL2' unc' trsLL3' term'. \<lbrakk>p=Semlab_Proc  sl  trsLL2 unc trsLL3 term;
       p'= Semlab_Proc sl' trsLL2' unc' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f16' sl' trsLL2' unc' trsLL3' term')
       (id_assn sl sl' *
    list_assn (term_assn id_assn id_assn) unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX16 p p' * \<Gamma>16') R (f16  sl  trsLL2 unc trsLL3 term)"
  assumes Switch_Innermost_Proc:
  "\<And> sl term sl' term'. \<lbrakk>p=Switch_Innermost_Proc sl term;
       p'= Switch_Innermost_Proc sl' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f17' sl' term')
       (id_assn sl sl' * dp_termination_proof_assn term term' *
        hn_ctxt XX17 p p' * \<Gamma>17') R (f17 sl term)"
  assumes Rewriting_Proc:
  "\<And> n r1 r2 r3 r4 apos term n' r1' r2' r3' r4' apos' term'. \<lbrakk>p=Rewriting_Proc n r1 r2 r3 r4 apos term;
       p'= Rewriting_Proc n' r1' r2' r3' r4' apos' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f18' n' r1' r2' r3' r4' apos' term')
       (option_assn (trsLL_assn id_assn id_assn id_assn) n n' *
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    ruleLL_assn id_assn id_assn id_assn r2 r2' *
    ruleLL_assn id_assn id_assn id_assn r3 r3' *
    ruleLL_assn id_assn id_assn id_assn r4 r4' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX18 p p' * \<Gamma>18') R (f18 n r1 r2 r3 r4 apos term)"
 assumes Instantiation_Proc:
  "\<And> r1 trsLL term r1' trsLL' term'. \<lbrakk>p=Instantiation_Proc r1 trsLL term;
       p'= Instantiation_Proc r1' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f19' r1' trsLL' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX19 p p' * \<Gamma>19') R (f19 r1 trsLL term)"
 assumes Forward_Instantiation_Proc:
  "\<And> r1 trsLL trsLL2 term r1' trsLL' trsLL2' term'. \<lbrakk>p=Forward_Instantiation_Proc r1 trsLL trsLL2 term;
       p'= Forward_Instantiation_Proc r1' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f20' r1' trsLL' trsLL2' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    option_assn (trsLL_assn id_assn id_assn id_assn) trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX20 p p' * \<Gamma>20') R (f20 r1 trsLL trsLL2 term)"
  assumes Narrowing_Proc:
  "\<And> r1 apos trsLL term r1' apos' trsLL' term'. \<lbrakk>p=Narrowing_Proc r1 apos trsLL term;
       p'= Narrowing_Proc r1' apos' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f21' r1' apos' trsLL' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    pos_assn apos apos' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX21 p p' * \<Gamma>21') R (f21 r1 apos trsLL term)"
  assumes Assume_Finite:
  "\<And> r1 term r1' term'. \<lbrakk>p=Assume_Finite r1 term;
       p'= Assume_Finite r1' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f22' r1' term')
       (id_assn r1 r1' * id_assn term term' *
        hn_ctxt XX22 p p' * \<Gamma>22') R (f22 r1 term)"
 assumes Unlab_Proc:
  "\<And> trsLL trsLL2 term trsLL' trsLL2' term'. \<lbrakk>p=Unlab_Proc trsLL trsLL2 term;
       p'= Unlab_Proc trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f23' trsLL' trsLL2' term')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX23 p p' * \<Gamma>23') R (f23 trsLL trsLL2 term)"
 assumes Q_Reduction_Proc:
  "\<And> trsLL term trsLL' term'. \<lbrakk>p=Q_Reduction_Proc trsLL term;
       p'= Q_Reduction_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f24' trsLL' term')
       (termsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX24 p p' * \<Gamma>24') R (f24 trsLL term)"
 assumes Complex_Constant_Removal_Proc:
  "\<And> trsLL term trsLL' term'. \<lbrakk>p=Complex_Constant_Removal_Proc trsLL term;
       p'= Complex_Constant_Removal_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f25' trsLL' term')
       (id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX25 p p' * \<Gamma>25') R (f25 trsLL term)"
  assumes General_Redpair_Proc:
  "\<And> red trsLL trsLL2 pp term red' trsLL' trsLL2' pp' term'. \<lbrakk>p=General_Redpair_Proc red trsLL trsLL2 pp term;
       p'= General_Redpair_Proc red' trsLL' trsLL2' pp' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f26' red' trsLL' trsLL2' pp' term')
       (redtriple_impl_assn red red' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    id_assn pp pp' *
    list_assn dp_termination_proof_assn term term' *
        hn_ctxt XX26 p p' * \<Gamma>26') R (f26 red trsLL trsLL2 pp term)"
  assumes To_Trs_Proc:
  "\<And> red red'. \<lbrakk>p=To_Trs_Proc red;
       p'= To_Trs_Proc red'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f27' red')
       (trs_termination_proof_assn red red' *
        hn_ctxt XX27 p p' * \<Gamma>27') R (f27 red)"
  assumes MERGE1: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<or>\<^sub>A \<Gamma>3' \<or>\<^sub>A \<Gamma>4'  \<or>\<^sub>A \<Gamma>5' \<or>\<^sub>A \<Gamma>6' \<or>\<^sub>A \<Gamma>7' \<or>\<^sub>A \<Gamma>8' \<or>\<^sub>A \<Gamma>9' \<or>\<^sub>A \<Gamma>10' \<or>\<^sub>A
         \<Gamma>11' \<or>\<^sub>A \<Gamma>12' \<or>\<^sub>A \<Gamma>13' \<or>\<^sub>A \<Gamma>14' \<or>\<^sub>A \<Gamma>15' \<or>\<^sub>A \<Gamma>16' \<or>\<^sub>A
         \<Gamma>17' \<or>\<^sub>A \<Gamma>18' \<or>\<^sub>A \<Gamma>19' \<or>\<^sub>A \<Gamma>20' \<or>\<^sub>A \<Gamma>21' \<or>\<^sub>A \<Gamma>22' \<or>\<^sub>A \<Gamma>23' \<or>\<^sub>A \<Gamma>24'  \<or>\<^sub>A \<Gamma>25' \<or>\<^sub>A \<Gamma>26' \<or>\<^sub>A \<Gamma>27' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows
    "hn_refine \<Gamma>
      (case_dp_termination_proof f1' f2' f3' f4' f5' f6' f7' f8' f9' f10' f11' f12' f13' f14' f15'
       f16' f17' f18' f19' f20' f21' f22' f23' f24' f25' f26' f27' p')
      (hn_ctxt (dp_termination_proof_assn) p p' * \<Gamma>') R
      (case_dp_termination_proof$f1$ABS5 f2$ABS4 f3$ABS4 f4$ABS5 f5$ABS3 f6$ABS2 f7
  $ABS2 f8$ABS5 f9$ABS5 f10$ABS2 f11$ABS4 f12$ABS6 f13$ABS6 f14$ABS5 f15$ABS6 f16$ABS3 f17
  $ABS8 f18$ABS4 f19$ABS5 f20$ABS5 f21$ABS3 f22$ABS4 f23$ABS3 f24$ABS3 f25$ABS6 f26$ABS2 f27$p)"
  supply [[goals_limit=1]]
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (subst dp_termination_proof_assn.simps[THEN hn_dp_termination_proof_assn])
  apply (cases p; cases p';
    simp only: PROTECT2_def APP_def dp_termination_proof.case prod.case
     star_false_left hn_refine_false)
  subgoal
    apply (rule hn_refine_cons[OF _ P_is_Empty _ entt_refl]; assumption?)
     applyS (simp add: hn_ctxt_def dp_termination_proof_assn.simps)
    apply (simp add: hn_ctxt_def dp_termination_proof_assn.simps)
    apply1 (rule entt_trans[OF _ MERGE1])
    applyS (simp add: entt_disjI1' entt_disjI2' entt_fr_drop')
    done
  subgoal by (hn_case_proof ccase:Subterm_Criterion_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Gen_Subterm_Criterion_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Redpair_UR_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Usable_Rules_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Dep_Graph_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Mono_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Mono_URM_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase: Mono_Redpair_UR_Proc merge: MERGE1)
  subgoal by (hn_case_proof ccase:Size_Change_Subterm_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Size_Change_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof_internal ccase:Uncurry_Proc merge:MERGE1)
  subgoal by (hn_case_proof_internal ccase:Fcc_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Split_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Semlab_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Switch_Innermost_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Rewriting_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Instantiation_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Forward_Instantiation_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Narrowing_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Assume_Finite merge:MERGE1)
  subgoal by (hn_case_proof ccase:Unlab_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Q_Reduction_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Complex_Constant_Removal_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:General_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:To_Trs_Proc merge:MERGE1)
  done


ML \<open>@{term pre_logic_checker.check_valid_formula}\<close>
term pre_logic_checker.check_valid_formula
thm pre_logic_checker.check_valid_formula_def
 pre_logic_checker.check_valid_formula_def
thm IA.check_valid_formula[unfolded IA.valid_def]
term IA.check_clause

text \<open>Function that should be replaced @{term pre_logic_checker.check_valid_formula}
  @{term pre_logic_checker.check_valid_formula} is called by
  @{term pre_logic_checker.check_valid_formula} called by
  @{term pre_logic_checker.check_formula} called by
  @{term pre_art_checker.check_simulation_cond} and @{term pre_logic_checker.safe_by_assertion_checker}

    for @{term pre_art_checker.check_simulation_cond}
    @{term pre_art_checker.check_art_invariants}  called by
    @{term pre_art_checker.check_art_invariants_impl} called by
    @{term pre_art_checker.invariant_proof_checker}  called by
      @{term pre_art_checker.check_safety} (in the other call too)
      @{term pre_termination_checker.check_cooperation_proof} called by
       @{term pre_termination_checker.check_termination_proof} called by
       @{term pre_termination_checker.check} called by
       @{term IA_locale.check_termination} called by
       @{term check_cert} called by
       @{term certify_cert_problem}
\<close>
term IA_locale.check_clause
term IA_locale.unsat_checker
term IA_locale.unsat_via_simplex
thm IA_locale.unsat_via_simplex_def
term check_valid_formula
thm IA.to_simplex_constraint_def
term simplex
thm simplex_def
lemma \<open>simplex A = None\<close>
  unfolding
    simplex_def
    solve_exec_code_def
    [unfolded SolveExec'.solve_exec_def[OF SolveExec'Default.SolveExec'_axioms]]
    solve_exec_ns_code_def
    Solve_exec_ns'.solve_exec_ns_def[OF Solve_exec_ns'Default.Solve_exec_ns'_axioms]
  unfolding
    (* assert_all_code_def *) AssertAllState.assert_all_def[OF AssertAllStateDefault.AssertAllState_axioms]
  apply simp
  thm 
AssertAllState.assert_all_def[OF AssertAllStateDefault.AssertAllState_axioms]
    Solve_exec_ns'.solve_exec_ns_def
    Solve_exec_ns'.solve_exec_ns_def[OF Solve_exec_ns'Default.Solve_exec_ns'_axioms]

ML \<open>
  BNF_FP_Def_Sugar.fp_sugar_of @{context} @{type_name dp_termination_proof}
  |> the 
  |> #fp_ctr_sugar
  |> #ctr_sugar
  |> #ctrs
\<close>
lemma [code del]: "mset xs - mset ys = mset (fold remove1 ys xs)"
  by (rule sym, induct ys arbitrary: xs) (simp_all add: diff_add diff_right_commute diff_diff_add)

(* export_code certify_proof
(* Certified Unsupported Error Inl Inr sumbot
(* remove, after defining an XML format: *)
  Yes No Terminating Upperbound Nonterminating Confluent Nonconfluent Completed Anything
  nat_of_integer *)
  in SML module_name Ceta file "code/test.sml" *)

lemma list_assn_pure_conv':
  \<open>list_assn (\<lambda>a c. \<up> (c = a)) = pure (\<langle>Id\<rangle>list_rel)\<close>
  unfolding pure_def[symmetric] list_assn_pure_conv
  pair_in_Id_conv[symmetric]
  ..

lemma id_assn_eq_iff: \<open>id_assn a b = (\<up> (a = b))\<close>
  unfolding pure_def by auto


lemma id_assn_alt': \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
  unfolding pure_def[symmetric] pair_in_Id_conv[symmetric]
  by auto

abbreviation char_assn :: \<open>char \<Rightarrow> char \<Rightarrow> assn\<close> where
  \<open>char_assn \<equiv> id_assn\<close>

abbreviation string_assn where
  \<open>string_assn \<equiv> list_assn char_assn\<close>

lemma unfold_to_id_assn:
  \<open>option_assn id_assn = id_assn\<close>
  \<open>string_assn = id_assn\<close>
  \<open>(\<lambda>a c. \<up> (c = a)) = id_assn\<close>
  \<open>(\<lambda>a c. emp) = unit_assn\<close>
     apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv' id_assn_eq_iff
      split: option.splits; fail)
    apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv; fail)
   apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv id_assn_eq_iff; fail)
  apply (intro ext; auto simp: option_assn_alt_def list_assn_pure_conv id_assn_eq_iff; fail)
  done

lemma plain_name_hnr[sepref_fr_rules]:
  \<open>(return o plain_name, RETURN o plain_name) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn +\<^sub>a id_assn\<close>
  supply plain_name.simps[simp del]
  unfolding sum_assn_id
  by (sepref_to_hoare) sep_auto

abbreviation cert_result_assn :: \<open>cert_result \<Rightarrow> cert_result \<Rightarrow> assn\<close> where
  \<open>cert_result_assn \<equiv> id_assn\<close>

definition parse_xtc_plain_name where
  \<open>parse_xtc_plain_name = parse_xtc plain_name\<close>


definition pure_fun_assn :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> assn\<close> where
  \<open>pure_fun_assn = id_assn\<close>

definition fun_comp where
  \<open>fun_comp f x = f x\<close>

lemma fun_comp_hnr:
  \<open>(uncurry (return oo (\<lambda>f x. f x)), uncurry (RETURN oo fun_comp)) \<in>
     pure_fun_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn\<close>
  by sepref_to_hoare (sep_auto simp: pure_fun_assn_def fun_comp_def)

lemma fun_comp_list_hnr:
  \<open>(uncurry (return oo (\<lambda>f x. f x)), uncurry (RETURN oo fun_comp)) \<in>
     pure_fun_assn\<^sup>k *\<^sub>a (list_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn\<close>
  by sepref_to_hoare (sep_auto simp: pure_fun_assn_def fun_comp_def id_assn_eq_iff list_assn_pure_conv')



definition input_assn
  :: \<open>((string, nat list) lab, string) input \<Rightarrow> ((string, nat list) lab, string) input \<Rightarrow> assn\<close>
where
  \<open>input_assn = id_assn\<close>


lemma parse_xtc_plain_name_hnr[sepref_fr_rules]:
  \<open>(return o parse_xtc_plain_name, RETURN o (parse_xtc_plain_name)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn input_assn)\<close>
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims simp: input_assn_def id_assn_eq_iff
      list_assn_pure_conv')


lemma Error_hnr[sepref_fr_rules]:
  \<open>(return o Error, RETURN o Error) \<in> string_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  by (sepref_to_hoare) (sep_auto simp: list_assn_pure_conv')

definition parse_claim_plain_name :: "string \<Rightarrow> string + ('a, 'b) claim" where
  \<open>parse_claim_plain_name = parse_claim plain_name\<close>


lemma parse_claim_plain_name_hnr[sepref_fr_rules]:
  \<open>(return o parse_claim_plain_name, RETURN o (parse_claim_plain_name)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn id_assn)\<close>
  unfolding sum_assn_id unfold_to_id_assn
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims
      simp: input_assn_def id_assn_eq_iff list_assn_pure_conv')

lemma parse_cert_problem_hnr[sepref_fr_rules]:
  \<open>(return o parse_cert_problem, RETURN o (parse_cert_problem)) \<in>
    string_assn\<^sup>k \<rightarrow>\<^sub>a (sum_assn string_assn (option_assn input_assn *a id_assn))\<close>
  by (sepref_to_hoare) (sep_auto elim!: sum_assn.elims simp: input_assn_def id_assn_eq_iff id_assn_alt'
      unfold_to_id_assn)

definition no_input_pb where
  \<open>no_input_pb = ''missing input problem''\<close>

lemma no_input_pb_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return no_input_pb), uncurry0 (RETURN no_input_pb)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition certify_prob where
  \<open>certify_prob = certify_cert_problem tp_impl
               Ceta_Verifier.dpp_impl ac_tp_impl
               Ceta_Verifier.ac_dpp_impl\<close>

definition check_cert_args where
  \<open>check_cert_args = check_cert tp_impl Ceta_Verifier.dpp_impl ac_tp_impl
                      Ceta_Verifier.ac_dpp_impl\<close>

abbreviation claim_assn :: \<open>('f, 'l) claim \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>claim_assn \<equiv> id_assn\<close>

abbreviation proof_assn :: \<open>('f, 'l, 'v) proof \<Rightarrow> _ \<Rightarrow> _\<close> where
  \<open>proof_assn \<equiv> id_assn\<close>

named_theorems isafor_string_names "various strings for code generation"

definition string_eq_of where
  \<open>string_eq_of = '' of ''\<close>

declare string_eq_of_def[symmetric, isafor_string_names]

lemma string_eq_of_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_of), uncurry0 (RETURN string_eq_of)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_by where
  \<open>string_eq_by = '' by ''\<close>

declare string_eq_by_def[symmetric, isafor_string_names]

lemma string_eq_by_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_by), uncurry0 (RETURN string_eq_by)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes3 where
  \<open>string_eq_mes3 = ''Confluence with start term not supported''\<close>

declare string_eq_mes3_def[symmetric, isafor_string_names]

lemma string_eq_mes3_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes3), uncurry0 (RETURN string_eq_mes3)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes4 where
  \<open>string_eq_mes4 = ''Claiming ''\<close>

declare string_eq_mes4_def[symmetric, isafor_string_names]

lemma string_eq_mes4_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes4), uncurry0 (RETURN string_eq_mes4)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes5 where
  \<open>string_eq_mes5 = ''1''\<close>

declare string_eq_mes5_def[symmetric, isafor_string_names]

lemma string_eq_mes5_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes5), uncurry0 (RETURN string_eq_mes5)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes6 where
  \<open>string_eq_mes6 =  ''Confluence under strategy not supported''\<close>

declare string_eq_mes6_def[symmetric, isafor_string_names]

lemma string_eq_mes6_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes6), uncurry0 (RETURN string_eq_mes6)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

definition string_eq_mes7 where
  \<open>string_eq_mes7 =  ''Relative confluence not supported''\<close>

declare string_eq_mes7_def[symmetric, isafor_string_names]

lemma string_eq_mes7_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes7), uncurry0 (RETURN string_eq_mes7)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

thm ac_simps

definition string_eq_mes8 where
  \<open>string_eq_mes8 =  ''complexity class mismatch''\<close>

declare string_eq_mes8_def[symmetric, isafor_string_names]

lemma string_eq_mes8_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes8), uncurry0 (RETURN string_eq_mes8)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_mes9 where
  \<open>string_eq_mes9 =  ''Nonconfluence with start term not supported''\<close>

declare string_eq_mes9_def[symmetric, isafor_string_names]

lemma string_eq_mes9_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes9), uncurry0 (RETURN string_eq_mes9)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)


definition string_eq_mes10 where
  \<open>string_eq_mes10 =  ''Relative nonconfluence not supported''\<close>

declare string_eq_mes10_def[symmetric, isafor_string_names]

lemma string_eq_mes10_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return string_eq_mes10), uncurry0 (RETURN string_eq_mes10)) \<in>
    unit_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  by sepref_to_hoare (sep_auto simp: list_assn_pure_conv' id_assn_eq_iff)

(*
''complexity class mismatch''
''Relative nonconfluence not supported''

 *)
lemma case_input_swap:
  \<open>f (case x of
        DP_input x xa xb xc \<Rightarrow> f10 x xa xb xc
      | Inn_TRS_input x xa xb xc \<Rightarrow> f20 x xa xb xc
      | CPX_input x xa xb xc xd \<Rightarrow> f30 x xa xb xc xd
      | COMP_input x xa \<Rightarrow> f40 x xa
      | OCOMP_input x xa xb xc \<Rightarrow> f50 x xa xb xc
      | EQ_input x xa \<Rightarrow> f60 x xa
      | FP_TRS_input x xa \<Rightarrow> f70 x xa
      | CTRS_input x \<Rightarrow> f80 x
      | TA_input x xa \<Rightarrow> f90 x xa
      | AC_input x xa xb \<Rightarrow> f100 x xa xb
      | LTS_input x \<Rightarrow> f110 x
      | LTS_safety_input x xa \<Rightarrow> f120 x xa
      | Unknown_input x \<Rightarrow> f130 x) =
   (case x of
        DP_input x xa xb xc \<Rightarrow> f (f10 x xa xb xc)
      | Inn_TRS_input x xa xb xc \<Rightarrow> f (f20 x xa xb xc)
      | CPX_input x xa xb xc xd \<Rightarrow> f (f30 x xa xb xc xd)
      | COMP_input x xa \<Rightarrow> f (f40 x xa)
      | OCOMP_input x xa xb xc \<Rightarrow> f (f50 x xa xb xc)
      | EQ_input x xa \<Rightarrow> f (f60 x xa)
      | FP_TRS_input x xa \<Rightarrow> f (f70 x xa)
      | CTRS_input x \<Rightarrow> f (f80 x)
      | TA_input x xa \<Rightarrow> f (f90 x xa )
      | AC_input x xa xb \<Rightarrow> f (f100 x xa xb)
      | LTS_input x \<Rightarrow> f (f110 x)
      | LTS_safety_input x xa \<Rightarrow> f (f120 x xa)
      | Unknown_input x \<Rightarrow> f (f130 x))\<close>
  by (cases x) auto

lemma case_proof_swap:
  \<open>P (case proof of
       TRS_Termination_Proof x \<Rightarrow> f10 x
     | Complexity_Proof x \<Rightarrow> f20 x
     | DP_Termination_Proof x \<Rightarrow> f30 x
     | DP_Nontermination_Proof x \<Rightarrow> f40 x
     | TRS_Nontermination_Proof x \<Rightarrow> f50 x
     | FP_Termination_Proof x \<Rightarrow> f60 x
     | Relative_TRS_Nontermination_Proof x \<Rightarrow> f70 x
     | TRS_Confluence_Proof x \<Rightarrow> f80 x
     | TRS_Non_Confluence_Proof x \<Rightarrow> f90 x
     | Completion_Proof x \<Rightarrow> f100 x
     | Ordered_Completion_Proof x \<Rightarrow> f110 x
     | Equational_Proof x \<Rightarrow> f120 x
     | Equational_Disproof x \<Rightarrow> f130 x
     | Quasi_Reductive_Proof x \<Rightarrow> f140 x
     | Conditional_CR_Proof x \<Rightarrow> f150 x
     | Conditional_Non_CR_Proof x \<Rightarrow> f160 x
     | Tree_Automata_Closed_Proof x \<Rightarrow> f170 x
     | AC_Termination_Proof x \<Rightarrow> f180 x
     | LTS_Termination_Proof x \<Rightarrow> f190 x
     | LTS_Safety_Proof x \<Rightarrow> f200 x
     | Unknown_Proof x \<Rightarrow> f210 x
     | Unknown_Disproof x \<Rightarrow> f220 x) =
  (case proof of
      TRS_Termination_Proof x \<Rightarrow> P (f10 x )
    | Complexity_Proof x \<Rightarrow> P (f20 x )
    | DP_Termination_Proof x \<Rightarrow> P (f30 x)
    | DP_Nontermination_Proof x \<Rightarrow> P (f40 x)
    | TRS_Nontermination_Proof x \<Rightarrow> P (f50 x )
    | FP_Termination_Proof x \<Rightarrow> P (f60 x )
    | Relative_TRS_Nontermination_Proof x \<Rightarrow> P (f70 x)
    | TRS_Confluence_Proof x \<Rightarrow> P (f80 x)
    | TRS_Non_Confluence_Proof x \<Rightarrow> P (f90 x)
    | Completion_Proof x \<Rightarrow> P (f100 x)
    | Ordered_Completion_Proof x \<Rightarrow> P (f110 x)
    | Equational_Proof x \<Rightarrow> P (f120 x)
    | Equational_Disproof x \<Rightarrow> P (f130 x)
    | Quasi_Reductive_Proof x \<Rightarrow> P (f140 x)
    | Conditional_CR_Proof x \<Rightarrow> P (f150 x)
    | Conditional_Non_CR_Proof x \<Rightarrow> P (f160 x)
    | Tree_Automata_Closed_Proof x \<Rightarrow> P (f170 x)
    | AC_Termination_Proof x \<Rightarrow> P (f180 x)
    | LTS_Termination_Proof x \<Rightarrow> P (f190 x )
    | LTS_Safety_Proof x \<Rightarrow> P (f200 x)
    | Unknown_Proof x \<Rightarrow> P (f210 x)
    | Unknown_Disproof x \<Rightarrow> P (f220 x))\<close>
  by (cases "proof") auto

definition check_cert_args_mismatch where
   \<open>check_cert_args_mismatch input claim proof =
      (shows (''Claiming '' @ claim_to_string claim @ '' of '' @ input_to_string input @ '' by '' @ proof_to_string proof))\<close>

lemma [sepref_fr_rules]:
 \<open>(uncurry3 (return oooo check_cert_args_mismatch), uncurry3 (RETURN oooo check_cert_args_mismatch)) \<in>
   input_assn\<^sup>k  *\<^sub>a claim_assn\<^sup>k  *\<^sub>a proof_assn\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a string_assn\<close>
  unfolding unfold_to_id_assn input_assn_def
  by sepref_to_hoare (sep_auto)
(* 
datatype (dead 'f, dead 'v) input =
  DP_input "bool" "('f, 'v) rules" "('f, 'v) strategy" "('f, 'v) rules"
| Inn_TRS_input "('f, 'v) strategy" "('f, 'v) rules" "('f, 'v) rules" "start_term"
| CPX_input  "('f, 'v) strategy" "('f, 'v) rules" "('f, 'v) rules" "('f,'v) complexity_measure" complexity_class (* TODO: improve CPF and remove*)
| COMP_input "('f, 'v) equation list" "('f, 'v) rules"
| OCOMP_input "('f, 'v) equation list" "('f, 'v) equation list" "('f, 'v) rules" "'f reduction_order_input"
| EQ_input "('f, 'v) equation list" "('f, 'v) equation_literal"
| FP_TRS_input "('f, 'v) fp_strategy" "('f, 'v) rules"
| CTRS_input "('f, 'v) crules"
| TA_input "(string,'f)tree_automaton" "('f,'v)rules"
| AC_input "('f,'v) rules" "'f list" "'f list"
| LTS_input "(IA.sig, 'v, IA.ty, string, string) lts_impl"
| LTS_safety_input "(IA.sig, 'v, IA.ty, string, string) lts_impl" "string list"
| Unknown_input unknown_info
 *)
lemma 1:
  \<open>RETURN o (\<lambda>x. f x) = (\<lambda>x. RETURN (f x))\<close>
  by auto
(* sepref_definition  certify_prob_code
  is \<open>uncurry3 (RETURN oooo check_cert_args)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a claim_assn\<^sup>k  *\<^sub>a proof_assn\<^sup>k \<rightarrow>\<^sub>a pure_fun_assn +\<^sub>a unit_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_cert_args_def check_cert_def  pull_out_let_conv check_cert_args_mismatch_def[symmetric]
    case_input_swap 1 case_proof_swap Let_def
  unfolding isafor_string_names
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  oops *)
          (*  apply sepref_dbg_side_unfold apply (auto simp: )[] *)

term sum_assn
lemma certify_prob_hnr[sepref_fr_rules]:
  \<open>(uncurry3 (return oooo check_cert_args), uncurry3 (RETURN oooo check_cert_args)) \<in>
        bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a pure_fun_assn +\<^sub>a unit_assn\<close>
  by sepref_to_hoare (sep_auto simp: input_assn_def unfold_to_id_assn pure_fun_assn_def
      id_assn_eq_iff list_assn_pure_conv')

lemma Certified_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return Certified), uncurry0 (RETURN Certified)) \<in>
   unit_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  by sepref_to_hoare (sep_auto)

sepref_definition  certify_prob_code
  is \<open>uncurry3 (RETURN oooo certify_prob)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a input_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k  *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a cert_result_assn\<close>
  supply fun_comp_list_hnr[sepref_fr_rules]
  unfolding certify_prob_def certify_cert_problem_def check_cert_args_def[symmetric]
    HOL_list.fold_custom_empty
  apply (rewrite at \<open>Error(_  \<hole>)\<close> annotate_assn[where A = \<open>string_assn\<close>])
  apply (rewrite at \<open>Error(\<hole>)\<close> fun_comp_def[symmetric])
  by sepref

declare certify_prob_code.refine[sepref_fr_rules]

(* "bool \<Rightarrow> string option \<Rightarrow> (_,_)claim + string \<Rightarrow> string \<Rightarrow> cert_result" where *)
sepref_definition certify_proof_code
  is \<open>uncurry3 (RETURN oooo certify_proof)\<close>
  :: \<open>bool_assn\<^sup>k *\<^sub>a (option_assn string_assn)\<^sup>k *\<^sub>a (sum_assn id_assn string_assn)\<^sup>k *\<^sub>a string_assn\<^sup>k \<rightarrow>\<^sub>a
      cert_result_assn\<close>
  supply[[goals_limit=1]]
  unfolding certify_proof_def parse_xtc_plain_name_def[symmetric]
    parse_claim_plain_name_def[symmetric] certify_prob_def[symmetric]
    no_input_pb_def[symmetric]
  by sepref

lemma prod_assn_id_assn_id_assn:
  \<open>id_assn *a id_assn = id_assn\<close>
  by auto

theorem certify_proof_code_sound:
  assumes ret: "certify_proof_code False (Some input_str) (Inr claim_str) proof_str = return Certified"
  shows "\<exists>input claim.
    parse_xtc plain_name input_str = Inr input \<and>
    parse_claim plain_name claim_str = Inr claim \<and>
    desired_property input claim"
proof -
  have [simp]: \<open>id_assn a b = \<up>(a =b)\<close> for a b
    by (auto simp: pure_def)
  have H:
    \<open><emp>
       certify_proof_code a b ba bb
       <\<lambda>r. \<exists>\<^sub>Ax. true *
                   \<up> (x = r \<and>
                      x =
                      certify_proof a b ba
                       bb)>\<close>
    for a b ba bb
    using certify_proof_code.refine
    unfolding hfref_def unfold_to_id_assn sum_assn_id hfprod_fst_snd keep_drop_sels
      prod_assn_id_assn_id_assn
    by (auto simp: unfold_to_id_assn hn_refine_def)
  have H:\<open>(h, as) \<Turnstile> emp \<and>
       Run.run (Heap_Monad.return Certified)
        (Some h) \<sigma> r \<longrightarrow>
       \<not> is_exn \<sigma> \<and>
       in_range
        (the_state \<sigma>,
         new_addrs h as (the_state \<sigma>)) \<and>
       r =
       certify_proof False (Some input_str)
        (Inr claim_str) proof_str \<and>
       relH {a. a < heap.lim h \<and> a \<notin> as} h
        (the_state \<sigma>) \<and>
       heap.lim h \<le> heap.lim (the_state \<sigma>)\<close>
    for h as r \<sigma>
    using ret H[of False \<open>Some input_str\<close> \<open>Inr claim_str\<close> \<open>proof_str\<close>]
    by (auto simp: unfold_to_id_assn hn_refine_def hoare_triple_def)


  show ?thesis
    apply (rule certify_proof_sound[where proof_str = \<open>proof_str\<close>])
    using ret H[of \<open>_\<close> \<open>{}\<close>]
    by (auto simp: run.simps return_def Heap_Monad.heap_def)
qed

thm certify_proof_def
thm check_cert_def
thm certify_cert_problem_def
thm certify_proof_def
(*
  apply sepref_dbg_keep
      apply sepref_dbg_trans_keep
           apply sepref_dbg_trans_step_keep
           apply sepref_dbg_side_unfold apply (auto simp: )[]
 *)

(* export_code certify_proof_code in Haskell module_name Ceta file "code/ceta.hs"
export_code certify_proof in Haskell module_name Ceta file "code/ceta_normal.hs" *)
export_code certify_proof_code in SML module_name Ceta file "code/ceta.sml"
text \<open>Function that shoul be replaced @{term pre_logic_checker.check_valid_formula}
  @{term pre_logic_checker.check_valid_formula} is called by
  @{term pre_logic_checker.check_valid_formula} called by
  @{term pre_logic_checker.check_formula} called by
  @{term pre_art_checker.check_simulation_cond} and @{term pre_logic_checker.safe_by_assertion_checker}

    for @{term pre_art_checker.check_simulation_cond}
    @{term pre_art_checker.check_art_invariants}  called by
    @{term pre_art_checker.check_art_invariants_impl} called by
    @{term pre_art_checker.invariant_proof_checker}  called by
      @{term pre_art_checker.check_safety} (in the other call too)
      @{term pre_termination_checker.check_cooperation_proof} called by
       @{term pre_termination_checker.check_termination_proof} called by
       @{term pre_termination_checker.check} called by
       @{term IA_locale.check_termination} called by
       @{term check_cert} called by
       @{term certify_cert_problem}


     for @{term pre_logic_checker.safe_by_assertion_checker}, calls by
     @{term pre_art_checker.check_safety_proof} called by
     @{term pre_art_checker.check_safety} called by
     @{term check_cert} called by
     @{term certify_cert_problem}
  \<close>



end