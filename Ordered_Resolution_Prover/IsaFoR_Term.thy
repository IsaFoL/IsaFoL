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

primrec renamings_apart' :: "nat set \<Rightarrow> ('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart' _ [] = []"
| "renamings_apart' X (C#Cs) = 
    (let \<sigma> = (\<lambda>v. Var (v + Max X + 1)) in 
      \<sigma> # renamings_apart' (X \<union> var_clause (C \<cdot>cls \<sigma>)) Cs)
   "

fun renamings_apart'_inv :: "nat set \<Rightarrow> ('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart'_inv _ [] = []"
| "renamings_apart'_inv X (C#Cs) = 
    (let \<sigma> = (\<lambda>v. Var (v - Max X - 1)) in 
      \<sigma> # renamings_apart'_inv (X \<union> var_clause (C \<cdot>cls \<sigma>)) Cs)
   "

definition var_map_of_subst :: "('f, nat) subst \<Rightarrow> nat \<Rightarrow> nat" where
  "var_map_of_subst \<sigma> v = the_Var (\<sigma> v)"

abbreviation renamings_apart :: "('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart Cs \<equiv> renamings_apart' {} Cs"

lemma len_renamings_apart': "length (renamings_apart' X Cs) = length Cs"
  apply (induction Cs arbitrary: X)
   apply simp
  by (metis length_Cons renamings_apart'.simps(2))

lemma renamings_apart'_is_Var: "\<forall>\<sigma> \<in> set (renamings_apart' X Cs). \<forall>x. is_Var (\<sigma> x)"
proof (induction Cs arbitrary: X)
  case Nil
  then show ?case by auto
next
  case (Cons a Cs)
  then show ?case 
    using is_VarI set_ConsD
    by (metis (no_types, lifting) renamings_apart'.simps(2))
qed

lemma renamings_apart'_inj: "\<forall>\<sigma> \<in> set (renamings_apart' X Cs). inj \<sigma>"
proof (induction Cs arbitrary: X)
  case Nil
  then show ?case by auto
next
  case (Cons a Cs)
  then show ?case 
    by (metis (mono_tags, lifting) renamings_apart'.simps(2) inj_onI
        nat_add_right_cancel set_ConsD term.inject(1))
qed

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
    have inj_is_renaming: 
      "\<And>\<sigma> :: ('f, nat) subst. (\<And>x. is_Var (\<sigma> x)) \<Longrightarrow> inj \<sigma> \<Longrightarrow> is_renaming \<sigma>"
    proof -
      fix \<sigma> :: "('f, nat) subst"
      fix x
      assume is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)"
      assume inj_\<sigma>: "inj \<sigma>"
      define \<sigma>' where "\<sigma>' = var_map_of_subst \<sigma>"

      have \<sigma>: "\<sigma> = Var \<circ> \<sigma>'"
        unfolding \<sigma>'_def var_map_of_subst_def using is_var_\<sigma> by auto

      from is_var_\<sigma> inj_\<sigma> have "inj \<sigma>'"
        unfolding var_renaming_def unfolding subst_domain_def inj_on_def \<sigma>'_def var_map_of_subst_def
        by (metis term.collapse(1))
      then have "inv \<sigma>' \<circ> \<sigma>' = id"
        using inv_o_cancel[of \<sigma>'] by simp
      then have "Var \<circ> (inv \<sigma>' \<circ> \<sigma>') = Var"
        by simp
      then have "\<forall>x. (Var \<circ> (inv \<sigma>' \<circ> \<sigma>')) x = Var x"
        by metis
      then have "\<forall>x. ((Var \<circ> \<sigma>') \<circ>\<^sub>s (Var \<circ> (inv \<sigma>'))) x = Var x"
        unfolding subst_compose_def by auto
      then have "\<sigma> \<circ>\<^sub>s (Var \<circ> (inv \<sigma>')) = Var"
        using \<sigma> by auto
      then show "is_renaming \<sigma>"
        unfolding is_renaming_def by blast
    qed
    then have "\<forall>\<sigma> \<in> (set (renamings_apart Cs)). is_renaming \<sigma>"
      using renamings_apart'_is_Var renamings_apart'_inj by blast
  }
  moreover
  {
    have "\<And>X. var_disjoint (subst_cls_lists Cs (renamings_apart' X Cs))"
      subgoal for X
      proof (induction Cs arbitrary: X)
        case Nil
        then show ?case unfolding var_disjoint_def subst_cls_lists_def by auto
      next
        case (Cons a Cs)
        then show ?case
          unfolding var_disjoint_def
          sorry
      qed
      done
    then have "var_disjoint (subst_cls_lists Cs (renamings_apart Cs))"
      by auto
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
