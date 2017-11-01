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

abbreviation renamings_apart :: "('f, nat) term clause list \<Rightarrow> (('f, nat) subst) list" where
  "renamings_apart Cs \<equiv> renamings_apart' {} Cs"

lemma len_renamings_apart': "length (renamings_apart' X Cs) = length Cs"
  apply (induction rule: renamings_apart'.induct)
   apply simp
  apply (metis length_nth_simps(2) renamings_apart'.simps(2))
  done

interpretation substitution_ops "op \<cdot>" Var "op \<circ>\<^sub>s" .

interpretation substitution "op \<cdot>" "Var :: _ \<Rightarrow> ('f, nat) term" "op \<circ>\<^sub>s" renamings_apart
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
    thm is_renaming_def
    find_theorems is_renaming
    have "\<And>Cs X. Ball (set (renamings_apart' X Cs)) is_renaming"
      subgoal for Cs X
        apply (induction Cs)
         apply simp
        apply auto
        unfolding is_renaming_def
        apply (rule exI)
        sorry
      done
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
  {
    assume "\<exists>C_at :: nat \<Rightarrow> ('f, 'v) term clause.
      \<forall>i. strictly_generalizes_cls (C_at (Suc i)) (C_at i)"
    then obtain C_at :: "nat \<Rightarrow> ('f, 'v) term clause" where
      f: "\<And>i. strictly_generalizes_cls (C_at (Suc i)) (C_at i)"
      by blast

    define n where
      "n = size (C_at 0)"

    have sz_C_n: "size (C_at i) = n" for i
      sorry

    obtain
      Ls_at :: "nat \<Rightarrow> ('f, 'v) term literal list" and
      \<sigma>_at :: "nat \<Rightarrow> 'v \<Rightarrow> ('f, 'v) term"
    where
      Ls_\<sigma>: "\<And>i. map (\<lambda>L. subst_lit L (\<sigma>_at i)) (Ls_at (Suc i)) = Ls_at i" and
      Ls_\<sigma>_strict: "\<And>i. \<exists>j < n. \<not> generalizes_lit (Ls_at (Suc i) ! j) (Ls_at i ! j)"
      sorry

    let ?f = undefined

    define tm_at :: "nat \<Rightarrow> ('f, 'v) term" where
      "\<And>i. tm_at i = Fun ?f (map atm_of (Ls_at i))"

    have "generalizes_atm (tm_at (Suc i)) (tm_at i)" for i
      unfolding tm_at_def generalizes_atm_def using Ls_\<sigma>[THEN arg_cong, of "map atm_of"]
      by (auto simp: comp_def)
    moreover have "\<not> generalizes_atm (tm_at i) (tm_at (Suc i))" for i
      sorry
    ultimately have "strictly_generalizes_atm (tm_at (Suc i)) (tm_at i)" for i
      unfolding strictly_generalizes_atm_def by blast
    then have "tm_at (Suc i) <\<cdot> tm_at i" for i
      unfolding strictly_generalizes_atm_def generalizes_atm_def term_subsumable.subsumes_def
      by (metis subsumeseq_term.simps)
    then have False
      using wf_subsumes[unfolded wf_iff_no_infinite_down_chain mem_Collect_eq prod.case] by blast
  }
  then show "wfP (strictly_generalizes_cls :: ('f, 'v) term clause \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def by (blast intro: wf_iff_no_infinite_down_chain[THEN iffD2])
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
