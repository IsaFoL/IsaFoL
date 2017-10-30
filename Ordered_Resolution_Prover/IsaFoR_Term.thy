(*  Title:       Integration of IsaFoR Terms
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
*)

section \<open>Integration of IsaFoR Terms\<close>

theory IsaFoR_Term
  imports Deriving.Derive "$ISAFOR/Rewriting/Unification" Abstract_Substitution
begin

(* TODO: Move to Isabelle's "Wellfounded.thy" theory file *)
lemma mlexD: "(x, y) \<in> f <*mlex*> R \<Longrightarrow> f x < f y \<or> f x = f y \<and> (x, y) \<in> R"
  by (simp add: mlex_prod_def)

(* TODO: Move to Isabelle's "Wellfounded.thy" theory file *)
lemma not_mlexD: "(x, y) \<notin> f <*mlex*> R \<Longrightarrow> f x > f y \<or> f x = f y \<and> (x, y) \<notin> R"
  by (meson antisym_conv3 mlex_leq mlex_less not_less)

hide_const (open) mgu

derive linorder prod
derive linorder list
derive linorder "term"

primrec gsize_tm :: "('f, 'v) term \<Rightarrow> nat" where
  "gsize_tm (Var _) = 1"
| "gsize_tm (Fun _ ts) = 2 + sum_list (map gsize_tm ts)"

definition gsize_cls :: "('f, 'v) term clause \<Rightarrow> nat" where
  "gsize_cls C = sum_mset (image_mset (gsize_tm \<circ> atm_of) C)"

definition gvars_tm :: "('f, 'v) Term.term \<Rightarrow> nat" where
  "gvars_tm t = gsize_tm t - card (vars_term t)"

definition gvars_cls :: "('f, 'v) term clause \<Rightarrow> nat" where
  "gvars_cls C = sum_mset (image_mset (gvars_tm \<circ> atm_of) C)"

definition gpair :: "('f, 'v) term clause rel" where
  "gpair = gsize_cls <*mlex*> measure gvars_cls"

lemma wf_gpair: "wf gpair"
  by (simp add: gpair_def wf_mlex)

interpretation substitution_ops "op \<cdot>" Var "op \<circ>\<^sub>s" .

interpretation substitution "op \<cdot>" "Var :: _ \<Rightarrow> ('f, 'v) term" "op \<circ>\<^sub>s"
proof
  show "\<And>A. subst_atm_abbrev A Var = A"
    sorry
next
  show "\<And>A \<tau> \<sigma>. subst_atm_abbrev A (comp_subst_abbrev \<tau> \<sigma>) = subst_atm_abbrev (subst_atm_abbrev A \<tau>) \<sigma>"
    sorry
next
  show "\<And>\<sigma> \<tau>. (\<And>A. subst_atm_abbrev A \<sigma> = subst_atm_abbrev A \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    sorry
next
  show "\<And>Cs \<sigma>. is_ground_cls_list (subst_cls_list Cs \<sigma>) \<Longrightarrow>
            \<exists>\<tau>. is_ground_subst \<tau> \<and> (\<forall>i<length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> subst_cls S \<sigma> = subst_cls S \<tau>)"
    sorry
next
  show "\<And>Cs. length (mk_var_dis Cs) = length Cs \<and>
    Ball (set (mk_var_dis Cs)) is_renaming \<and> var_disjoint (subst_cls_lists Cs (mk_var_dis Cs))"
    sorry
next
  have generalizes_atm_imp_gsize_tm:
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
      sorry

    have "generalizes_atm (Fun f ss) (Fun f ts)"
      sorry
    hence ss_g_ts: "list_all2 generalizes_atm ss ts"
      sorry

    have gsz_ss_ts: "list_all2 (\<lambda>s t. gsize_tm s \<le> gsize_tm t) ss ts"
      using Fun(1)
      sorry

    have "sum_list (map gsize_tm ss) \<le> sum_list (map gsize_tm ts)"
      using len_ts gsz_ss_ts
    proof (induct ss arbitrary: ts)
      case (Cons s ss')

      obtain t ts' where
        ts: "ts = t # ts'"
        by (metis Cons.prems length_Suc_conv)
      have len_ts': "length ts' = length ss'"
        using Cons.prems ts by auto

      have
        gsz_s_t: "gsize_tm s \<le> gsize_tm t" and
        gsz_ss'_ts': "list_all2 (\<lambda>s t. gsize_tm s \<le> gsize_tm t) ss' ts'"
        using Cons(3) unfolding ts by simp_all

      show ?case
        unfolding ts using gsz_s_t Cons(1)[OF len_ts' gsz_ss'_ts'] by simp
    qed simp
    then show ?case
      unfolding t by simp
  qed
  
  have in_gpair: "strictly_generalizes_cls C D \<Longrightarrow> (C, D) \<in> gpair" for C D :: "('f, 'v) term clause"
  proof (rule ccontr)
    assume
      pg: "strictly_generalizes_cls C D" and
      ni_gp: "(C, D) \<notin> gpair"

    have g: "generalizes_cls C D" and ng: "\<not> generalizes_cls D C"
      using pg unfolding strictly_generalizes_cls_def by blast+

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
          sorry

        let ?A = "atm_of L"
        let ?B = "atm_of M"

        have a_g_b: "generalizes_atm ?A ?B"
          using l_g_m by (metis (mono_tags) generalizes_atm_def generalizes_lit_def literal.map_sel
              subst_lit_def)

        have "gsize_cls C' \<le> gsize_cls D'"
          using Suc.hyps Suc.prems(2) c'_g_d' d generalizes_cls_size by auto
        moreover have "gsize_tm ?A \<le> gsize_tm ?B"
          by (rule generalizes_atm_imp_gsize_tm[OF a_g_b])
        ultimately show ?case
          unfolding c d gsize_cls_def by simp
      qed simp
    }
    moreover
    {
      assume gsize: "gsize_cls C = gsize_cls D"

      have "gvars_cls C \<le> gvars_cls D"
        sorry
    }
    moreover
    {
      assume
        gsize: "gsize_cls C = gsize_cls D" and
        gvar: "gvars_cls C = gvars_cls D"

      have False
        sorry
    }
    ultimately show False
      using not_mlexD[OF ni_gp[unfolded gpair_def]] by fastforce
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
