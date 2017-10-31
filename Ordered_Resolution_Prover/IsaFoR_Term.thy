(*  Title:       Integration of IsaFoR Terms
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
*)

section \<open>Integration of IsaFoR Terms\<close>

theory IsaFoR_Term
  imports Deriving.Derive "$ISAFOR/Rewriting/Unification" Abstract_Substitution
begin

(* TODO: Move to "Multiset_More" *)
lemma sum_image_mset_sum_map[simp]: "sum_mset (image_mset f (mset xs)) = sum_list (map f xs)"
  by (metis mset_map sum_mset_sum_list)

lemma vars_term_is_Var: "is_Var s \<Longrightarrow> vars_term s = {the_Var s}"
  by force

hide_const (open) mgu

derive linorder prod
derive linorder list
derive linorder "term"

definition var_subst :: "('v \<Rightarrow> ('f, 'w) term) \<Rightarrow> bool" where
  "var_subst \<sigma> \<longleftrightarrow> (\<forall>x. is_Var (\<sigma> x))"

definition vars_cls :: "('f, 'v) term clause \<Rightarrow> 'v set" where
  "vars_cls C = \<Union> (set_mset (image_mset (vars_term \<circ> atm_of) C))"

lemma finite_vars_cls[simp]: "finite (vars_cls C)"
  unfolding vars_cls_def by simp

abbreviation same_shape_tm :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "same_shape_tm \<equiv> rel_term (op =) (\<lambda>x y. True)"

abbreviation same_shape_lit :: "('f, 'v) term literal \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "same_shape_lit \<equiv> rel_literal same_shape_tm"

abbreviation same_shape_cls :: "('f, 'v) term clause \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "same_shape_cls \<equiv> rel_mset same_shape_lit"

primrec gsize_tm :: "('f, 'v) term \<Rightarrow> nat" where
  "gsize_tm (Var _) = 1"
| "gsize_tm (Fun _ ss) = 2 + sum_list (map gsize_tm ss)"

definition gsize_cls :: "('f, 'v) term clause \<Rightarrow> nat" where
  "gsize_cls C = sum_mset (image_mset (gsize_tm \<circ> atm_of) C)"

definition gvars_tm :: "('f, 'v) term \<Rightarrow> nat" where
  "gvars_tm s = gsize_tm s - card (vars_term s)"

definition gvars_cls :: "('f, 'v) term clause \<Rightarrow> nat" where
  "gvars_cls C = gsize_cls C - card (vars_cls C)"

definition gpair :: "('f, 'v) term clause rel" where
  "gpair = gsize_cls <*mlex*> measure gvars_cls"

term subst_apply_term
term subst_apply_set

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
  apply (metis length_nth_simps renamings_apart'.simps(2)) 
  done

lemma card_vars_le_gsize_tm: "card (vars_term s) \<le> gsize_tm s"
proof (induct s)
  case (Fun f ss)
  then show ?case
  proof (induct ss)
    case (Cons s ss)
    have "card (vars_term s \<union> (\<Union>x \<in> set ss. vars_term x))
      \<le> card (vars_term s) + card (\<Union>x \<in> set ss. vars_term x)"
      using card_Un_le by blast
    also have "\<dots> \<le> 2 + gsize_tm s + sum_list (map gsize_tm ss)"
      using Cons.hyps Cons.prems by fastforce
    finally show ?case
      by simp
  qed simp
qed simp

lemma card_vars_le_gsize_cls: "card (vars_cls C) \<le> gsize_cls C"
  by (induct C; simp add: vars_cls_def gsize_cls_def)
    (smt add.assoc add.left_commute card_Un_le card_vars_le_gsize_tm le_iff_add)

lemma wf_gpair: "wf gpair"
  by (simp add: gpair_def wf_mlex)

lemma list_elem_le_sum_map_gt_imp_elem_eq:
  fixes f :: "_ \<Rightarrow> 'a::linordered_semiring"
  assumes
    "length xs = length ys" and
    "\<forall>i < length xs. f (xs ! i) \<le> f (ys ! i)" and
    "sum_list (map f xs) \<ge> sum_list (map f ys)"
  shows "\<forall>i < length xs. f (xs ! i) = f (ys ! i)"
  using assms
proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)

  have "\<forall>i < length xs. f (xs ! i) \<le> f (ys ! i)"
    using Cons(3) by fastforce
  moreover have "sum_list (map f xs) \<ge> sum_list (map f ys)"
  proof -
    have "\<forall>bs b f. (f (b::'b)::'a) + sum_list (map f bs) = sum_list (map f (b # bs))"
      by simp
    then have "\<exists>a aa. a + sum_list (map f ys) \<le> aa \<and> aa \<le> sum_list (map f xs) + a"
      using Cons(3)[rule_format, of 0, simplified] Cons(4)
      by (metis (no_types) Groups.add_ac(2) add_le_cancel_left)
    moreover have "\<forall>a aa ab. (a::'a) \<le> aa \<or> \<not> ab + a \<le> aa + ab"
      by (simp add: Groups.add_ac(2))
    ultimately show ?thesis
      by (meson add_mono_thms_linordered_semiring(1))
  qed
  ultimately have fxs_eq_fys: "\<forall>i < length xs. f (xs ! i) = f (ys ! i)"
    by (rule Cons(2))
  then have sum_fxs_eq_fys: "sum_list (map f xs) = sum_list (map f ys)"
    by (metis Cons.hyps(1) map_eq_conv')

  show ?case
  proof (intro allI impI)
    fix i
    assume i_lt: "i < length (x # xs)"
    show "f ((x # xs) ! i) = f ((y # ys) ! i)"
    proof (cases i)
      case 0
      then show ?thesis
        using sum_fxs_eq_fys Cons(3)[rule_format, of 0] Cons(4) by simp
    next
      case (Suc j)
      then show ?thesis
        using i_lt fxs_eq_fys by auto
    qed
  qed
qed simp

interpretation substitution_ops "op \<cdot>" Var "op \<circ>\<^sub>s" .

lemma vars_term_subst: "vars_term (s \<cdot> \<sigma>) = \<Union> ((vars_term \<circ> \<sigma>) ` vars_term s)"
  sorry

lemma vars_term_var_subst: "var_subst \<sigma> \<Longrightarrow> vars_term (t \<cdot> \<sigma>) = (the_Var \<circ> \<sigma>) ` vars_term t"
  unfolding vars_term_subst var_subst_def comp_def image_def by (auto simp: vars_term_is_Var)

lemma vars_cls_var_subst: "var_subst \<sigma> \<Longrightarrow> vars_cls (subst_cls C \<sigma>) = (the_Var \<circ> \<sigma>) ` vars_cls C"
  unfolding vars_cls_def subst_cls_def by (auto simp: vars_term_var_subst)

lemma card_lt_if_noninj_subst:
  assumes fin: "finite V" and x_in: "x \<in> V" and y_in: "y \<in> V" and x_ne_y: "x \<noteq> y" and
    \<sigma>x_eq_\<sigma>y: "\<sigma> x = \<sigma> y"
  shows "card ((the_Var \<circ> \<sigma>) ` V) < card V"
proof -
  have v: "V = (V - {x, y}) \<union> {x, y}"
    using x_in y_in by blast

  have "card ((the_Var \<circ> \<sigma>) ` V) \<le> card ((the_Var \<circ> \<sigma>) ` (V - {x, y})) + 1"
    by (subst v, unfold image_Un, simp add: \<sigma>x_eq_\<sigma>y card_insert_le_m1)
  also have "\<dots> \<le> card (V - {x, y}) + 1"
    by (simp add: card_image_le fin)
  also have "\<dots> < card (V - {x, y}) + 2"
    by arith
  also have "\<dots> = card (V - {x, y}) + card {x, y}"
    by (simp add: x_ne_y)
  also have "\<dots> = card V"
    by (subst (2) v) (auto simp: card_Un_disjoint[symmetric] fin)
  finally show ?thesis
    .
qed

interpretation substitution "op \<cdot>" "Var :: _ \<Rightarrow> ('f, nat) term" "op \<circ>\<^sub>s" "renamings_apart"
proof
  show "\<And>A. subst_atm_abbrev A Var = A"
    by auto
next
  show "\<And>A \<tau> \<sigma>. subst_atm_abbrev A (comp_subst_abbrev \<tau> \<sigma>) = subst_atm_abbrev (subst_atm_abbrev A \<tau>) \<sigma>"
    by auto
next
  show "\<And>\<sigma> \<tau>. (\<And>A. subst_atm_abbrev A \<sigma> = subst_atm_abbrev A \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
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
        apply (rule conjI)
        
        
     
       

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
  have gsize_tm_if_generalizes_atm:
    "generalizes_atm s t \<Longrightarrow> gsize_tm s \<le> gsize_tm t" for s t :: "('f, 'v) term"
  proof (induct s arbitrary: t)
    case (Var x)
    show ?case
      by (cases t) auto
  next
    case (Fun f ss)

    obtain ts where
      t: "t = Fun f ts" and
      len_ts: "length ts = length ss"
      by (metis Fun.prems generalizes_atm_def length_map subst_apply_term.simps(2))

    have "generalizes_atm (Fun f ss) (Fun f ts)"
      using Fun(2) unfolding t .
    hence "\<exists>\<sigma>. map (\<lambda>s. s \<cdot> \<sigma>) ss = ts"
      by (simp add: generalizes_atm_def)
    hence ss_g_ts: "list_all2 generalizes_atm ss ts"
      unfolding generalizes_atm_def using list_all2_conv_all_nth by fastforce

    have gsz_ss_ts: "list_all2 (\<lambda>s t. gsize_tm s \<le> gsize_tm t) ss ts"
      using Fun(1) list.rel_mono_strong ss_g_ts by force

    have "sum_list (map gsize_tm ss) \<le> sum_list (map gsize_tm ts)"
      using len_ts gsz_ss_ts
    proof (induct ss arbitrary: ts)
      case (Cons s ss')
      obtain t ts' where
        ts: "ts = t # ts'"
        by (metis Cons.prems length_Suc_conv)
      have len_ts': "length ts' = length ss'"
        using Cons.prems ts by auto
      have gsz_s_t: "gsize_tm s \<le> gsize_tm t" and
        gsz_ss'_ts': "list_all2 (\<lambda>s t. gsize_tm s \<le> gsize_tm t) ss' ts'"
        using Cons(3) unfolding ts by simp_all
      show ?case
        unfolding ts using gsz_s_t Cons(1)[OF len_ts' gsz_ss'_ts'] by simp
    qed simp
    then show ?case
      unfolding t by simp
  qed

  (* FIXME: move out *)

  have same_shape_if_gen_gsize: "same_shape_cls C D"
    if "generalizes_cls C D" and "gsize_cls C = gsize_cls D"
    for C D :: "('f, 'v) term clause"
    sorry
(* FIXME
    using that
  proof (induct s arbitrary: t)
    case (Var x)
    then show ?case
      by (cases t) auto
  next
    case (Fun f ss)
    note ih = this(1) and gen = this(2) and gsize = this(3)

    show ?case
    proof (cases t)
      case t: (Fun g ts)
      show ?thesis
      proof (simp add: t; intro conjI)
        show "f = g"
          using gen[unfolded t] unfolding generalizes_atm_def by simp
      next
        show "list_all2 same_shape_tm ss ts"
        proof (unfold list_all2_conv_all_nth, intro conjI allI impI)
          show len_eq: "length ss = length ts"
            using gen[unfolded t] unfolding generalizes_atm_def by auto

          have gen_nth: "generalizes_atm (ss ! i) (ts ! i)" if "i < length ss" for i
            using that Fun.prems(1) unfolding generalizes_atm_def
            by (metis (no_types) nth_map subst_apply_term.simps(2) t term.inject(2))
          have gsize_nth: "gsize_tm (ss ! i) = gsize_tm (ts ! i)" if "i < length ss" for i
            using gsize_tm_if_generalizes_atm[OF gen_nth] gsize[unfolded t]
            by simp (metis list_elem_le_sum_map_gt_imp_elem_eq len_eq order_refl that)

          show "same_shape_tm (ss ! i) (ts ! i)" if "i < length ss" for i
            using that by (auto intro!: ih gen_nth gsize_nth)
        qed
      qed
    qed (use Fun(3) in auto)
  qed
*)

  have var_noninj_subst_if_same_shape:
    "\<exists>\<sigma>. \<exists>x \<in> vars_cls C. \<exists>y \<in> vars_cls C. var_subst \<sigma> \<and> x \<noteq> y \<and> \<sigma> x = \<sigma> y \<and> subst_cls C \<sigma> = D"
    if "same_shape_cls C D" and "strictly_generalizes_cls C D"
    for C D :: "('f, 'v) term clause"
    sorry

  have card_vars_cls_lt_if_noninj_subst: "card (vars_cls C) > card (vars_cls D)"
    if x_in: "x \<in> vars_cls C" and y_in: "y \<in> vars_cls C" and vs: "var_subst \<sigma>" and
      x_ne_y: "x \<noteq> y" and \<sigma>x_eq_\<sigma>y: "\<sigma> x = \<sigma> y" and c\<sigma>_eq_d: "subst_cls C \<sigma> = D"
    for C D :: "('f, 'v) term clause" and x y \<sigma>
    unfolding c\<sigma>_eq_d[symmetric] vars_cls_var_subst[OF vs]
    by (rule card_lt_if_noninj_subst[OF finite_vars_cls x_in y_in x_ne_y \<sigma>x_eq_\<sigma>y])

  have in_gpair: "strictly_generalizes_cls C D \<Longrightarrow> (C, D) \<in> gpair" for C D :: "('f, 'v) term clause"
  proof (rule ccontr)
    assume
      sg: "strictly_generalizes_cls C D" and
      ni_gp: "(C, D) \<notin> gpair"

    have g: "generalizes_cls C D" and ng: "\<not> generalizes_cls D C"
      using sg unfolding strictly_generalizes_cls_def by blast+

    {
      have "gsize_cls C \<le> gsize_cls D"
        using g generalizes_cls_size[OF g]
      proof (induct "size C" arbitrary: C D)
        case (Suc k)
        obtain C' L where
          c: "C = C' + {#L#}"
          by (metis Suc.hyps(2) size_mset_SucE union_commute)
        obtain D' M where
          d: "D = D' + {#M#}" and
          c'_g_d': "generalizes_cls C' D'" and
          l_g_m: "generalizes_lit L M"
          by (metis Suc.prems(1) add_mset_add_single c generalizes_cls_def generalizes_lit_def
              subst_cls_add_mset)

        let ?A = "atm_of L"
        let ?B = "atm_of M"

        have "generalizes_atm ?A ?B"
          using l_g_m by (metis (mono_tags) generalizes_atm_def generalizes_lit_def literal.map_sel
              subst_lit_def)
        then have "gsize_tm ?A \<le> gsize_tm ?B"
          by (rule gsize_tm_if_generalizes_atm)
        moreover have "gsize_cls C' \<le> gsize_cls D'"
          using Suc.hyps Suc.prems(2) c'_g_d' d generalizes_cls_size by auto
        ultimately show ?case
          unfolding c d gsize_cls_def by simp
      qed simp
    }
    moreover
    {
      assume gsize: "gsize_cls C = gsize_cls D" and
        "gvars_cls C \<ge> gvars_cls D"
      moreover have "card (vars_cls C) > card (vars_cls D)"
        by (metis card_vars_cls_lt_if_noninj_subst var_noninj_subst_if_same_shape[OF _ sg]
            same_shape_if_gen_gsize[OF g gsize])
      ultimately have False
        using card_vars_le_gsize_cls unfolding gvars_cls_def by (metis leD le_diff_iff')
    }
    ultimately show False
      using ni_gp[unfolded gpair_def] by (simp add: mlex_prod_def not_less)
  qed
  show "wfP (strictly_generalizes_cls :: ('f, 'v) term clause \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def by (auto intro: wf_subset[OF wf_gpair] in_gpair)
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
