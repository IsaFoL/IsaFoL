(*  Title:       Integration of IsaFoR Terms
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
*)

section \<open>Integration of IsaFoR Terms\<close>

theory IsaFoR_Term
  imports Deriving.Derive "$ISAFOR/Normalization_Equivalence/Encompassment" Abstract_Substitution
begin

hide_const (open) mgu

derive linorder prod
derive linorder list
derive linorder "term"

abbreviation subst_apply_literal :: "('f, 'v) term literal \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term literal" (infixl "\<cdot>lit" 60) where
  "L \<cdot>lit \<sigma> \<equiv> map_literal (\<lambda>A. A \<cdot> \<sigma>) L"

definition subst_apply_clause :: "('f, 'v) term clause \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term clause" (infixl "\<cdot>cls" 60) where
  "C \<cdot>cls \<sigma> = image_mset (\<lambda>L. L \<cdot>lit \<sigma>) C"

abbreviation var_lit :: "('f, 'v) term literal \<Rightarrow> 'v set" where
  "var_lit L \<equiv> vars_term (atm_of L)"

definition var_clause :: "('f, 'v) term clause \<Rightarrow> 'v set" where
  "var_clause C = Union (set_mset (image_mset var_lit C))"

fun renamings_apart' :: "nat set \<Rightarrow> ('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart' _ [] = []"
| "renamings_apart' X (C#Cs) = 
    (let \<sigma> = (\<lambda>v. Var (v + Max X + 1)) in 
      \<sigma> # renamings_apart' (X \<union> var_clause (C \<cdot>cls \<sigma>)) Cs)
   "

definition subst_of_inverse :: "(('f, nat) term \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f, nat) term" where 
  "subst_of_inverse \<sigma> v = (Var (\<sigma> (Var v)))"

abbreviation renamings_apart :: "('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart Cs \<equiv> renamings_apart' {} Cs"

lemma len_renamings_apart': "length (renamings_apart' X Cs) = length Cs"
  apply (induction rule: renamings_apart'.induct)
   apply simp
  apply (metis length_nth_simps(2) renamings_apart'.simps(2))
  done

interpretation substitution_ops "op \<cdot>" Var "op \<circ>\<^sub>s" .

interpretation substitution "op \<cdot>" "Var :: _ \<Rightarrow> ('f, nat) term" "op \<circ>\<^sub>s" "Fun undefined" renamings_apart
proof
  show "\<And>A. A \<cdot> Var = A"
    by auto
next
  show "\<And>A \<tau> \<sigma>. A \<cdot> \<tau> \<circ>\<^sub>s \<sigma> = A \<cdot> \<tau> \<cdot> \<sigma>"
    by auto
next
  show "\<And>\<sigma> \<tau>. (\<And>A. A \<cdot> \<sigma> = A \<cdot> \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)
next
  fix Cs :: "('f, nat) term clause list"
  fix \<sigma>
  assume "is_ground_cls_list (subst_cls_list Cs \<sigma>)"
  show "\<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> subst_cls S \<sigma> = subst_cls S \<tau>)"
    sorry
next
  fix Cs :: "('f, nat) term clause list"
  {
    have "length (renamings_apart Cs) = length Cs"
      using len_renamings_apart' by auto
  }
  moreover
  {


    find_consts name: var_renaming
    have inj_is_renaming: "\<And>\<sigma> :: ('f, nat) subst. var_renaming \<sigma> \<Longrightarrow> is_renaming \<sigma>"
      subgoal for \<sigma>
      unfolding var_renaming_def is_renaming_def subst_domain_def apply auto
      apply (rule_tac x="subst_of_inverse ((inv \<sigma>))" in exI)
      sorry
    done

    have "\<And>(Cs :: ('f, nat) term clause list) X. Ball (set (renamings_apart' X Cs)) var_renaming"
      subgoal for Cs X
      proof (induction rule: renamings_apart'.induct)
        case (1 uu)
        then show ?case by auto
      next
        case (2 X C Cs)
        note this[of "\<lambda>v. Var (v + Max X + 1)", simplified]
        then show ?case
          unfolding var_renaming_def
          apply auto
          apply (metis is_VarI set_ConsD)
          apply (smt Suc_inject inj_onI nat_add_right_cancel set_ConsD term.inject(1))
          done
      qed
      done
    then have "Ball (set (renamings_apart Cs)) is_renaming"
      using inj_is_renaming by blast
  }
  moreover
  {
    have "var_disjoint (subst_cls_lists Cs (renamings_apart Cs))"
      sorry
  }
  ultimately show "length (renamings_apart Cs) = length Cs \<and>
    Ball (set (renamings_apart Cs)) is_renaming \<and> var_disjoint (subst_cls_lists Cs (renamings_apart Cs))"
    by simp
next
  show "\<And>\<sigma> As Bs. Fun undefined As \<cdot> \<sigma> = Fun undefined Bs \<longleftrightarrow> map (\<lambda>A. A \<cdot> \<sigma>) As = Bs"
    by simp
next
  show "wfP (strictly_generalizes_atm :: ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def
    by (rule wf_subset[OF wf_subsumes])
      (auto simp: strictly_generalizes_atm_def generalizes_atm_def term_subsumable.subsumes_def subsumeseq_term.simps)
qed








  fix CC and \<sigma>::"'b \<Rightarrow> ('a, 'b) term"
  assume "substitution_ops.is_ground_cls_list op \<cdot> (substitution_ops.subst_cls_list op \<cdot> CC \<sigma>) "
  show "\<exists>\<tau>. is_ground_subst (\<tau> :: 'b \<Rightarrow> ('a, 'b) term)  \<and> substitution_ops.subst_cls_list op \<cdot> CC \<sigma> = substitution_ops.subst_cls_list op \<cdot> CC \<tau>"
  proof
    def \<tau> \<equiv> "(\<lambda>x. Fun undefined []) :: ('a, 'b) subst"
    { fix t :: "('a, 'b) term" and \<tau> :: "('a, 'b) subst"
      have "t \<cdot> \<tau> \<cdot> \<tau> = t \<cdot> \<tau>"
        by (induct t) (auto simp add: \<tau>_def)
    }
    then show "substitution_ops.is_ground_subst op \<cdot> \<tau> \<and> substitution_ops.subst_cls_list op \<cdot> CC \<sigma> = substitution_ops.subst_cls_list op \<cdot> CC \<tau>"
      unfolding is_ground_subst_def is_ground_atm_def by simp
  qed
qed (auto intro: subst_term_eqI)

fun pairs where
  "pairs (x # y # xs) = (x, y) # pairs (y # xs)" |
  "pairs _ = []"

definition Pairs where
  "Pairs AAA = concat (sorted_list_of_set ((pairs o sorted_list_of_set) ` AAA))"

lemma unifies_all_pairs_iff:
  "(\<forall>p \<in> set (pairs xs). fst p \<cdot> \<sigma> = snd p \<cdot> \<sigma>) \<longleftrightarrow> (\<forall>a \<in> set xs. \<forall>b \<in> set xs. a \<cdot> \<sigma> = b \<cdot> \<sigma>)"
proof (induct xs rule: pairs.induct)
  case (1 x y xs)
  then show ?case
    unfolding pairs.simps list.set ball_Un ball_simps simp_thms fst_conv snd_conv by metis
qed simp_all

lemma unifiers_Pairs:
  "finite AAA \<Longrightarrow> \<forall>AA\<in>AAA. finite AA \<Longrightarrow> unifiers (set (Pairs AAA)) = {\<sigma>. is_unifier_set \<sigma> AAA}"
  by (auto simp: Pairs_def unifiers_def is_unifier_set_def is_unifier_alt unifies_all_pairs_iff)

definition "mgu AAA = map_option subst_of (unify (Pairs AAA) [])"

interpretation unification "op \<cdot>" Var "op \<circ>\<^sub>s" mgu
proof
  fix AAA :: "('a, 'b) term set set" and \<sigma> :: "('a, 'b) subst"
  assume fin: "finite AAA" "\<forall>AA\<in>AAA. finite AA" and "mgu AAA = Some \<sigma>"
  then have "is_imgu \<sigma> (set (Pairs AAA))"
    using unify_sound unfolding mgu_def by blast
  then show "is_mgu \<sigma> AAA"
    unfolding is_imgu_def is_mgu_def unifiers_Pairs[OF fin] by auto
next
  fix AAA :: "('a, 'b) term set set" and \<sigma> :: "('a, 'b) subst"
  assume fin: "finite AAA" "\<forall>AA\<in>AAA. finite AA" and "is_mgu \<sigma> AAA"
  then have "\<sigma> \<in> unifiers (set (Pairs AAA))"
    unfolding is_mgu_def unifiers_Pairs[OF fin] by auto
  then show "\<exists>\<tau>. mgu AAA = Some \<tau>"
    using unify_complete unfolding mgu_def by blast
qed auto

end
