theory DPLL_W_Partial_Encoding
imports
  DPLL_W_Optimal_Model
  CDCL_W_Partial_Encoding
begin

context optimal_encoding_ops
begin

text \<open>

We use the following list to generate an upper bound of the derived
trails by ODPLL: using lists makes it possible to use recursion. Using
\<^text>\<open>inductive_set\<close> does not work, because it is not possible to
recurse on the arguments of a predicate.


The idea is similar to an earlier definition of \<^term>\<open>simple_clss\<close>,
although in that case, we went for recursion over the set of literals
directly, via a choice in the recursive call.

\<close>
definition list_new_vars :: \<open>'v list\<close> where
\<open>list_new_vars = (SOME v. set v = \<Delta>\<Sigma> \<and> distinct v)\<close>

lemma
  set_list_new_vars: \<open>set list_new_vars = \<Delta>\<Sigma>\<close> and
  distinct_list_new_vars: \<open>distinct list_new_vars\<close> and
  length_list_new_vars: \<open>length list_new_vars = card \<Delta>\<Sigma>\<close>
  using someI[of \<open>\<lambda>v. set v = \<Delta>\<Sigma> \<and> distinct v\<close>]
  unfolding list_new_vars_def[symmetric]
  using finite_\<Sigma> finite_distinct_list apply blast
  using someI[of \<open>\<lambda>v. set v = \<Delta>\<Sigma> \<and> distinct v\<close>]
  unfolding list_new_vars_def[symmetric]
  using finite_\<Sigma> finite_distinct_list apply blast
  using someI[of \<open>\<lambda>v. set v = \<Delta>\<Sigma> \<and> distinct v\<close>]
  unfolding list_new_vars_def[symmetric]
  by (metis distinct_card finite_\<Sigma> finite_distinct_list)

fun all_sound_trails where
  \<open>all_sound_trails [] = simple_clss (\<Sigma> - \<Delta>\<Sigma>)\<close> |
  \<open>all_sound_trails (L # M) =
     all_sound_trails M \<union> add_mset (Pos (replacement_pos L)) ` all_sound_trails M
      \<union> add_mset (Pos (replacement_neg L)) ` all_sound_trails M\<close>

lemma all_sound_trails_atms:
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow>
   C \<in> all_sound_trails xs \<Longrightarrow>
     atms_of C \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` set xs \<union> replacement_neg ` set xs\<close>
  apply (induction xs arbitrary: C)
  subgoal by (auto simp: simple_clss_def)
  subgoal for x xs C
    apply (auto simp: tautology_add_mset)
    apply blast+
    done
  done

lemma all_sound_trails_distinct_mset:
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow> distinct xs \<Longrightarrow>
   C \<in> all_sound_trails xs \<Longrightarrow>
     distinct_mset C\<close>
  using all_sound_trails_atms[of xs C]
  apply (induction xs arbitrary: C)
  subgoal by (auto simp: simple_clss_def)
  subgoal for x xs C
    apply clarsimp
    apply (auto simp: tautology_add_mset)
    apply (simp add: all_sound_trails_atms; fail)+
    apply (frule all_sound_trails_atms, assumption)
    apply (auto dest!: multi_member_split simp: subsetD)
    apply (simp add: all_sound_trails_atms; fail)+
    apply (frule all_sound_trails_atms, assumption)
    apply (auto dest!: multi_member_split simp: subsetD)
    apply (simp add: all_sound_trails_atms; fail)+
    done
  done

lemma all_sound_trails_tautology:
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow> distinct xs \<Longrightarrow>
   C \<in> all_sound_trails xs \<Longrightarrow>
     \<not>tautology C\<close>
  using all_sound_trails_atms[of xs C]
  apply (induction xs arbitrary: C)
  subgoal by (auto simp: simple_clss_def)
  subgoal for x xs C
    apply clarsimp
    apply (auto simp: tautology_add_mset)
    apply (simp add: all_sound_trails_atms; fail)+
    apply (frule all_sound_trails_atms, assumption)
    apply (auto dest!: multi_member_split simp: subsetD)
    apply (simp add: all_sound_trails_atms; fail)+
    apply (frule all_sound_trails_atms, assumption)
    apply (auto dest!: multi_member_split simp: subsetD)
    done
  done

lemma all_sound_trails_simple_clss:
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow> distinct xs \<Longrightarrow>
   all_sound_trails xs \<subseteq> simple_clss (\<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` set xs \<union> replacement_neg ` set xs)\<close>
   using all_sound_trails_tautology[of xs]
     all_sound_trails_distinct_mset[of xs]
     all_sound_trails_atms[of xs]
   by (fastforce simp: simple_clss_def)

lemma in_all_sound_trails_inD:
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow> distinct xs \<Longrightarrow> a \<in> \<Delta>\<Sigma> \<Longrightarrow>
   add_mset (Pos (a\<^sup>\<mapsto>\<^sup>0)) xa \<in> all_sound_trails xs \<Longrightarrow> a \<in> set xs\<close>
  using all_sound_trails_simple_clss[of xs]
  apply (auto simp: simple_clss_def)
  apply (rotate_tac 3)
  apply (frule set_mp, assumption)
  apply auto
  done

lemma in_all_sound_trails_inD':
  \<open>set xs \<subseteq> \<Delta>\<Sigma> \<Longrightarrow> distinct xs \<Longrightarrow> a \<in> \<Delta>\<Sigma> \<Longrightarrow>
   add_mset (Pos (a\<^sup>\<mapsto>\<^sup>1)) xa \<in> all_sound_trails xs \<Longrightarrow> a \<in> set xs\<close>
  using all_sound_trails_simple_clss[of xs]
  apply (auto simp: simple_clss_def)
  apply (rotate_tac 3)
  apply (frule set_mp, assumption)
  apply auto
  done

context
  assumes [simp]: \<open>finite \<Sigma>\<close>
begin

lemma all_sound_trails_finite[simp]:
  \<open>finite (all_sound_trails xs)\<close>
  by (induction xs)
    (auto intro!: simple_clss_finite finite_\<Sigma>)

lemma card_all_sound_trails:
  assumes \<open>set xs \<subseteq> \<Delta>\<Sigma>\<close> and \<open>distinct xs\<close>
  shows \<open>card (all_sound_trails xs) = card (simple_clss (\<Sigma> - \<Delta>\<Sigma>)) * 3 ^ (length xs)\<close>
  using assms
  apply (induction xs)
  apply auto
  apply (subst card_Un_disjoint)
  apply (auto simp: add_mset_eq_add_mset dest: in_all_sound_trails_inD)
  apply (subst card_Un_disjoint)
  apply (auto simp: add_mset_eq_add_mset dest: in_all_sound_trails_inD')
  apply (subst card_image)
  apply (auto simp: inj_on_def)
  apply (subst card_image)
  apply (auto simp: inj_on_def)
  done

end

lemma simple_clss_all_sound_trails: \<open>simple_clss (\<Sigma> - \<Delta>\<Sigma>) \<subseteq> all_sound_trails ys\<close>
  apply (induction ys)
  apply auto
  done

lemma all_sound_trails_decomp_in:
  assumes
    \<open>C \<subseteq> \<Delta>\<Sigma>\<close>  \<open>C' \<subseteq> \<Delta>\<Sigma>\<close>  \<open>C \<inter> C' = {}\<close> \<open>C \<union> C' \<subseteq> set xs\<close>
    \<open>D \<in> simple_clss (\<Sigma> - \<Delta>\<Sigma>)\<close>
  shows
    \<open>(Pos o replacement_pos) `# mset_set C + (Pos o replacement_neg) `# mset_set C' + D \<in> all_sound_trails xs\<close>
  using assms
  apply (induction xs arbitrary: C C' D)
  subgoal
    using simple_clss_all_sound_trails[of \<open>[]\<close>]
    by auto
  subgoal premises p for a xs C C' D
    apply (cases \<open>a \<in># mset_set C\<close>)
    subgoal
      using p(1)[of \<open>C - {a}\<close> C' D] p(2-)
      finite_subset[OF p(3)]
      apply -
      apply (subgoal_tac \<open>finite C \<and> C - {a} \<subseteq> \<Delta>\<Sigma> \<and> C' \<subseteq> \<Delta>\<Sigma> \<and> (C - {a}) \<inter> C' = {} \<and> C - {a} \<union> C' \<subseteq> set xs\<close>)
      defer
      apply (auto simp: disjoint_iff_not_equal finite_subset)[]
      apply (auto dest!: multi_member_split)
      by (simp add: mset_set.remove)
    apply (cases \<open>a \<in># mset_set C'\<close>)
    subgoal
      using p(1)[of C \<open>C' - {a}\<close> D] p(2-)
        finite_subset[OF p(3)]
      apply -
      apply (subgoal_tac \<open>finite C \<and> C \<subseteq> \<Delta>\<Sigma> \<and> C'- {a} \<subseteq> \<Delta>\<Sigma> \<and> (C) \<inter> (C'- {a}) = {} \<and> C \<union> C'- {a} \<subseteq> set xs \<and>
         C \<subseteq> set xs \<and> C' - {a} \<subseteq> set xs\<close>)
      defer
      apply (auto simp: disjoint_iff_not_equal finite_subset)[]
      apply (auto dest!: multi_member_split)
      by (simp add: mset_set.remove)
    subgoal
      using p(1)[of C C' D] p(2-)
        finite_subset[OF p(3)]
      apply -
      apply (subgoal_tac \<open>finite C \<and> C \<subseteq> \<Delta>\<Sigma> \<and> C' \<subseteq> \<Delta>\<Sigma> \<and> (C) \<inter> (C') = {} \<and> C \<union> C' \<subseteq> set xs \<and>
         C \<subseteq> set xs \<and> C' \<subseteq> set xs\<close>)
      defer
      apply (auto simp: disjoint_iff_not_equal finite_subset)[]
      by (auto dest!: multi_member_split)
    done
  done

lemma (in -)image_union_subset_decomp:
  \<open>f ` (C) \<subseteq> A \<union> B \<longleftrightarrow> (\<exists>A' B'. f ` A' \<subseteq> A \<and> f ` B' \<subseteq> B \<and> C = A' \<union> B' \<and> A' \<inter> B' = {})\<close>
  apply (rule iffI)
  apply (rule exI[of _ \<open>{x \<in> C. f x \<in> A}\<close>])
  apply (rule exI[of _ \<open>{x \<in> C. f x \<in> B \<and> f x \<notin> A}\<close>])
  apply auto
  done

lemma in_all_sound_trails:
  assumes
    \<open>\<And>L. L \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg (replacement_pos L) \<notin># C\<close>
    \<open>\<And>L. L \<in> \<Delta>\<Sigma> \<Longrightarrow> Neg (replacement_neg L) \<notin># C\<close>
    \<open>\<And>L. L \<in> \<Delta>\<Sigma> \<Longrightarrow> Pos (replacement_pos L) \<in># C \<Longrightarrow> Pos (replacement_neg L) \<notin># C\<close>
    \<open>C \<in> simple_clss (\<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` set xs \<union> replacement_neg ` set xs)\<close> and
    xs: \<open>set xs \<subseteq> \<Delta>\<Sigma>\<close>
  shows
    \<open>C \<in> all_sound_trails xs\<close>
proof -
  have
    atms: \<open>atms_of C \<subseteq> (\<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` set xs \<union> replacement_neg ` set xs)\<close> and
    taut: \<open>\<not>tautology C\<close> and
    dist: \<open>distinct_mset C\<close>
    using assms unfolding simple_clss_def
    by blast+

  obtain A' B' A'a B'' where
    A'a: \<open>atm_of ` A'a \<subseteq> \<Sigma> - \<Delta>\<Sigma>\<close> and
    B'': \<open>atm_of ` B'' \<subseteq> replacement_pos ` set xs\<close> and
    \<open>A' = A'a \<union> B''\<close> and
    B': \<open>atm_of ` B' \<subseteq> replacement_neg ` set xs\<close> and
    C: \<open>set_mset C = A'a \<union> B'' \<union> B'\<close> and
    inter:
      \<open>B'' \<inter> B' = {}\<close>
      \<open>A'a \<inter> B' = {}\<close>
      \<open>A'a \<inter> B'' = {}\<close>
    using atms unfolding atms_of_def
    apply (subst (asm)image_union_subset_decomp)
    apply (subst (asm)image_union_subset_decomp)
    by (auto simp: Int_Un_distrib2)

  have H: \<open>f ` A \<subseteq> B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B\<close> for x A B f
    by auto
  have [simp]: \<open>finite A'a\<close> \<open>finite B''\<close> \<open>finite B'\<close>
    by (metis C finite_Un finite_set_mset)+
  obtain CB'' CB' where
    CB: \<open>CB' \<subseteq> set xs\<close> \<open>CB'' \<subseteq> set xs\<close> and
    decomp:
      \<open>atm_of ` B'' = replacement_pos ` CB''\<close>
      \<open>atm_of ` B' = replacement_neg ` CB'\<close>
    using B' B'' by (auto simp: subset_image_iff)
  have C: \<open>C =mset_set B'' + mset_set B' + mset_set A'a\<close>
    using inter
    apply (subst distinct_set_mset_eq_iff[symmetric, OF dist])
    apply (auto simp: C distinct_mset_mset_set simp flip: mset_set_Union)
    apply (subst mset_set_Union[symmetric])
    using inter
    apply auto
    apply (auto simp: distinct_mset_mset_set)
    done
  have B'': \<open>B'' = (Pos) ` (atm_of ` B'')\<close>
    using assms(1-3) B'' xs A'a B'' unfolding C
    apply (auto simp: )
    apply (frule H, assumption)
    apply (case_tac x)
    apply auto
    apply (rule_tac x = \<open>replacement_pos A\<close> in imageI)
    apply (auto simp add: rev_image_eqI)
    apply (frule H, assumption)
    apply (case_tac xb)
    apply auto
    done
  have B': \<open>B' = (Pos) ` (atm_of ` B')\<close>
    using assms(1-3) B' xs A'a B' unfolding C
    apply (auto simp: )
    apply (frule H, assumption)
    apply (case_tac x)
    apply auto
    apply (rule_tac x = \<open>replacement_neg A\<close> in imageI)
    apply (auto simp add: rev_image_eqI)
    apply (frule H, assumption)
    apply (case_tac xb)
    apply auto
    done

  have simple: \<open>mset_set A'a \<in> simple_clss (\<Sigma> - \<Delta>\<Sigma>)\<close>
    using assms A'a
    by (auto simp: simple_clss_def C atms_of_def image_Un tautology_decomp distinct_mset_mset_set)

  have [simp]: \<open>finite (Pos ` replacement_pos ` CB'')\<close>  \<open>finite (Pos ` replacement_neg ` CB')\<close>
    using B'' \<open>finite B''\<close> decomp \<open>finite B'\<close> B' apply auto
    by (meson CB(1) finite_\<Sigma> finite_imageI finite_subset xs)
  show ?thesis
    unfolding C
    apply (subst B'', subst B')
    unfolding decomp image_image
    apply (subst image_mset_mset_set[symmetric])
    subgoal
      using decomp xs B' B'' inter CB
      by (auto simp: C inj_on_def subset_iff)
    apply (subst image_mset_mset_set[symmetric])
    subgoal
      using decomp xs B' B'' inter CB
      by (auto simp: C inj_on_def subset_iff)
    apply (rule all_sound_trails_decomp_in[unfolded comp_def])
      using decomp xs B' B'' inter CB assms(3) simple
      unfolding C
      apply (auto simp: image_image)
      subgoal for x
        apply (subgoal_tac \<open>x \<in> \<Delta>\<Sigma>\<close>)
        using assms(3)[of x]
        apply auto
        by (metis (mono_tags, lifting) B' \<open>finite (Pos ` replacement_neg ` CB')\<close> \<open>finite B''\<close> decomp(2)
         finite_set_mset_mset_set image_iff)
    done
qed

end


locale dpll_optimal_encoding_opt =
  dpll\<^sub>W_state_optimal_weight trail clauses
    tl_trail cons_trail state_eq state \<rho> update_additional_info +
  optimal_encoding_opt_ops \<Sigma> \<Delta>\<Sigma> new_vars
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin

end


locale dpll_optimal_encoding =
  dpll_optimal_encoding_opt trail clauses
    tl_trail cons_trail state_eq state
    update_additional_info \<Sigma> \<Delta>\<Sigma> \<rho> new_vars  +
  optimal_encoding_ops
    \<Sigma> \<Delta>\<Sigma>
    new_vars \<rho>
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix "\<sim>" 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    \<Sigma> \<Delta>\<Sigma> :: \<open>'v set\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> and
    new_vars :: \<open>'v \<Rightarrow> 'v \<times> 'v\<close>
begin


inductive odecide :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
  odecide_noweight: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) L\<close> and
  \<open>atm_of L \<in> atms_of_mm (clauses S)\<close> and
  \<open>T \<sim> cons_trail (Decided L) S\<close> and
  \<open>atm_of L \<in> \<Sigma> - \<Delta>\<Sigma>\<close> |
  odecide_replacement_pos: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) (Pos (replacement_pos L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_pos L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close> |
  odecide_replacement_neg: \<open>odecide S T\<close>
if
  \<open>undefined_lit (trail S) (Pos (replacement_neg L))\<close> and
  \<open>T \<sim> cons_trail (Decided (Pos (replacement_neg L))) S\<close> and
  \<open>L \<in> \<Delta>\<Sigma>\<close>

inductive_cases odecideE: \<open>odecide S T\<close>

inductive dpll_conflict :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> where
\<open>dpll_conflict S S\<close>
if \<open>C \<in># clauses S\<close> and
  \<open>trail S \<Turnstile>as CNot C\<close>

inductive odpll\<^sub>W_core_stgy :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S T where
propagate: "dpll_propagate S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T" |
decided: "odecide S T \<Longrightarrow> no_step dpll_propagate S  \<Longrightarrow> odpll\<^sub>W_core_stgy S T " |
backtrack: "dpll_backtrack S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T" |
backtrack_opt: \<open>bnb.backtrack_opt S T \<Longrightarrow> odpll\<^sub>W_core_stgy S T\<close>

lemma odpll\<^sub>W_core_stgy_clauses:
  \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: odpll\<^sub>W_core_stgy.induct)
   (auto simp: dpll_propagate.simps odecide.simps dpll_backtrack.simps
      bnb.backtrack_opt.simps)

lemma rtranclp_odpll\<^sub>W_core_stgy_clauses:
  \<open>odpll\<^sub>W_core_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: odpll\<^sub>W_core_stgy_clauses)


inductive odpll\<^sub>W_bnb_stgy :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> for S T :: 'st where
dpll:
  \<open>odpll\<^sub>W_bnb_stgy S T\<close>
  if \<open>odpll\<^sub>W_core_stgy S T\<close> |
bnb:
  \<open>odpll\<^sub>W_bnb_stgy S T\<close>
  if \<open>bnb.dpll\<^sub>W_bound S T\<close>

lemma odpll\<^sub>W_bnb_stgy_clauses:
  \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy.induct)
   (auto simp: bnb.dpll\<^sub>W_bound.simps dest: odpll\<^sub>W_core_stgy_clauses)

lemma rtranclp_odpll\<^sub>W_bnb_stgy_clauses:
  \<open>odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> clauses T = clauses S\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: odpll\<^sub>W_bnb_stgy_clauses)

lemma odecide_dpll_decide_iff:
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows \<open>odecide S T \<Longrightarrow> dpll_decide S T\<close>
    \<open>dpll_decide S T \<Longrightarrow> Ex(odecide S)\<close>
  using assms atms_of_mm_penc_subset2[of N] \<Delta>\<Sigma>_\<Sigma>
  unfolding odecide.simps dpll_decide.simps
  apply (auto simp: odecide.simps dpll_decide.simps)
  apply (metis defined_lit_Pos_atm_iff state_eq_ref)+
  done

lemma
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy: \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> bnb.dpll\<^sub>W_core_stgy S T\<close>
  using odecide_dpll_decide_iff[OF assms]
  by (auto simp: odpll\<^sub>W_core_stgy.simps bnb.dpll\<^sub>W_core_stgy.simps)

lemma
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy: \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> bnb.dpll\<^sub>W_bnb S T\<close>
  using odecide_dpll_decide_iff[OF assms]
  by (auto simp: odpll\<^sub>W_bnb_stgy.simps bnb.dpll\<^sub>W_bnb.simps dest: odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy[OF assms]
    bnb.dpll\<^sub>W_core_stgy_dpll\<^sub>W_core)

lemma
  assumes \<open>clauses S = penc N\<close> and [simp]: \<open>atms_of_mm N = \<Sigma>\<close>
  shows
    rtranclp_odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy: \<open>odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close>
  using assms(1) apply -
  apply (induction rule: rtranclp_induct)
  subgoal by auto
  subgoal for T U
    using odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy[of T N U] rtranclp_odpll\<^sub>W_bnb_stgy_clauses[of S T]
    by auto
  done

lemma no_step_odpll\<^sub>W_core_stgy_no_step_dpll\<^sub>W_core_stgy:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>no_step odpll\<^sub>W_core_stgy S \<longleftrightarrow> no_step bnb.dpll\<^sub>W_core_stgy S\<close>
  using odecide_dpll_decide_iff[of S, OF assms]
  by (auto simp: odpll\<^sub>W_core_stgy.simps bnb.dpll\<^sub>W_core_stgy.simps)

lemma no_step_odpll\<^sub>W_bnb_stgy_no_step_dpll\<^sub>W_bnb:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>no_step odpll\<^sub>W_bnb_stgy S \<longleftrightarrow> no_step bnb.dpll\<^sub>W_bnb S\<close>
  using no_step_odpll\<^sub>W_core_stgy_no_step_dpll\<^sub>W_core_stgy[of S, OF assms] bnb.no_step_stgy_iff
  by (auto simp: odpll\<^sub>W_bnb_stgy.simps bnb.dpll\<^sub>W_bnb.simps dest: odpll\<^sub>W_core_stgy_dpll\<^sub>W_core_stgy[OF assms]
    bnb.dpll\<^sub>W_core_stgy_dpll\<^sub>W_core)

lemma full_odpll\<^sub>W_core_stgy_full_dpll\<^sub>W_core_stgy:
  assumes \<open>clauses S = penc N\<close> and [simp]:\<open>atms_of_mm N = \<Sigma>\<close>
  shows
    \<open>full odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> full bnb.dpll\<^sub>W_bnb S T\<close>
  using no_step_odpll\<^sub>W_bnb_stgy_no_step_dpll\<^sub>W_bnb[of T, OF _ assms(2)]
    rtranclp_odpll\<^sub>W_bnb_stgy_clauses[of S T, symmetric, unfolded assms]
    rtranclp_odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy[of S N T, OF assms]
   by (auto simp: full_def)


lemma decided_cons_eq_append_decide_cons:
  "Decided L # Ms = M' @ Decided K # M \<longleftrightarrow>
    (L = K \<and> Ms = M \<and> M' = []) \<or>
    (hd M' = Decided L \<and> Ms = tl M' @ Decided K # M \<and> M' \<noteq> [])"
  by (cases M')
   auto

lemma no_step_dpll_backtrack_iff:
  \<open>no_step dpll_backtrack S \<longleftrightarrow> (count_decided (trail S) = 0 \<or> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C))\<close>
  using backtrack_snd_empty_not_decided[of \<open>trail S\<close>] backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  apply (cases \<open>backtrack_split (trail S)\<close>; cases \<open>snd(backtrack_split (trail S))\<close>)
  by (auto simp: dpll_backtrack.simps count_decided_0_iff)

lemma no_step_dpll_conflict:
  \<open>no_step dpll_conflict S \<longleftrightarrow> (\<forall>C \<in># clauses S. \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: dpll_conflict.simps)

definition no_smaller_propa :: \<open>'st \<Rightarrow> bool\<close> where
"no_smaller_propa (S ::'st) \<longleftrightarrow>
  (\<forall>M K M' D L. trail S = M' @ Decided K # M \<longrightarrow> add_mset L D \<in># clauses S \<longrightarrow> undefined_lit M L \<longrightarrow> \<not>M \<Turnstile>as CNot D)"

lemma [simp]: \<open>T \<sim> S \<Longrightarrow> no_smaller_propa T = no_smaller_propa S\<close>
  by (auto simp: no_smaller_propa_def)

lemma no_smaller_propa_cons_trail[simp]:
  \<open>no_smaller_propa (cons_trail (Propagated L C) S) \<longleftrightarrow> no_smaller_propa S\<close>
  \<open>no_smaller_propa (update_weight_information M' S) \<longleftrightarrow> no_smaller_propa S\<close>
  by (force simp: no_smaller_propa_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)+

lemma no_smaller_propa_cons_trail_decided[simp]:
  \<open>no_smaller_propa S \<Longrightarrow> no_smaller_propa (cons_trail (Decided L) S) \<longleftrightarrow> (\<forall>L C. add_mset L C \<in># clauses S \<longrightarrow> undefined_lit (trail S)L \<longrightarrow> \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: no_smaller_propa_def cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
    decided_cons_eq_append_decide_cons)

lemma no_step_dpll_propagate_iff:
  \<open>no_step dpll_propagate S \<longleftrightarrow> (\<forall>L C. add_mset L C \<in># clauses S \<longrightarrow> undefined_lit (trail S)L \<longrightarrow> \<not>trail S \<Turnstile>as CNot C)\<close>
  by (auto simp: dpll_propagate.simps)

lemma count_decided_0_no_smaller_propa: \<open>count_decided (trail S) = 0 \<Longrightarrow> no_smaller_propa S\<close>
  by (auto simp: no_smaller_propa_def)

lemma no_smaller_propa_backtrack_split:
  \<open>no_smaller_propa S \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       no_smaller_propa (reduce_trail_to M S)\<close>
  using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  by (auto simp: no_smaller_propa_def)

lemma odpll\<^sub>W_core_stgy_no_smaller_propa:
  \<open>odpll\<^sub>W_core_stgy S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  using no_step_dpll_backtrack_iff[of S] apply -
  by (induction rule: odpll\<^sub>W_core_stgy.induct)
   (auto 5 5 simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_propa
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_propa_backtrack_split)

lemma odpll\<^sub>W_bound_stgy_no_smaller_propa: \<open>bnb.dpll\<^sub>W_bound S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (auto simp: cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons count_decided_0_no_smaller_propa
      dpll_propagate.simps dpll_decide.simps odecide.simps decided_cons_eq_append_decide_cons bnb.dpll\<^sub>W_bound.simps
      bnb.backtrack_opt.simps dpll_backtrack.simps no_step_dpll_conflict no_smaller_propa_backtrack_split)

lemma odpll\<^sub>W_bnb_stgy_no_smaller_propa:
  \<open>odpll\<^sub>W_bnb_stgy S T \<Longrightarrow> no_smaller_propa S \<Longrightarrow> no_smaller_propa T\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy.induct)
    (auto simp: odpll\<^sub>W_core_stgy_no_smaller_propa odpll\<^sub>W_bound_stgy_no_smaller_propa)


lemma filter_disjount_union:
  \<open>(\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> \<not>Q x) \<Longrightarrow>
   length (filter P xs) + length (filter Q xs) =
     length (filter (\<lambda>x. P x \<or> Q x) xs)\<close>
  by (induction xs) auto

lemma Collect_req_remove1:
  \<open>{a \<in> A. a \<noteq> b \<and> P a} = (if P b then Set.remove b {a \<in> A. P a} else {a \<in> A. P a})\<close> and
  Collect_req_remove2:
  \<open>{a \<in> A. b \<noteq> a \<and> P a} = (if P b then Set.remove b {a \<in> A. P a} else {a \<in> A. P a})\<close>
  by auto

lemma card_remove:
  \<open>card (Set.remove a A) = (if a \<in> A then card A - 1 else card A)\<close>
  apply (auto simp: Set.remove_def)
  by (metis Diff_empty One_nat_def card_Diff_insert card_infinite empty_iff
    finite_Diff_insert gr_implies_not0 neq0_conv zero_less_diff)

lemma isabelle_should_do_that_automatically: \<open>Suc (a - Suc 0) = a \<longleftrightarrow> a \<ge> 1\<close>
  by auto
lemma distinct_count_list_if: \<open>distinct xs \<Longrightarrow> count_list xs x = (if x \<in> set xs then 1 else 0)\<close>
  by (induction xs) auto

abbreviation (input) cut_and_complete_trail :: \<open>'st \<Rightarrow> _\<close> where
\<open>cut_and_complete_trail S \<equiv> trail S\<close>


(*TODO prove that favouring conflict over propagate works [this is obvious, but still]...*)
inductive odpll\<^sub>W_core_stgy_count :: "'st \<times> _ \<Rightarrow> 'st \<times> _ \<Rightarrow> bool" where
propagate: "dpll_propagate S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, C)" |
decided: "odecide S T \<Longrightarrow> no_step dpll_propagate S  \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, C) " |
backtrack: "dpll_backtrack S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, add_mset (cut_and_complete_trail S) C)" |
backtrack_opt: \<open>bnb.backtrack_opt S T \<Longrightarrow> odpll\<^sub>W_core_stgy_count (S, C) (T, add_mset (cut_and_complete_trail S) C)\<close>


inductive odpll\<^sub>W_bnb_stgy_count :: \<open>'st \<times> _ \<Rightarrow> 'st \<times> _ \<Rightarrow> bool\<close> where
dpll:
  \<open>odpll\<^sub>W_bnb_stgy_count S T\<close>
  if \<open>odpll\<^sub>W_core_stgy_count S T\<close> |
bnb:
  \<open>odpll\<^sub>W_bnb_stgy_count (S, C) (T, C)\<close>
  if \<open>bnb.dpll\<^sub>W_bound S T\<close>


lemma odpll\<^sub>W_core_stgy_countD:
  \<open>odpll\<^sub>W_core_stgy_count S T \<Longrightarrow> odpll\<^sub>W_core_stgy (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_core_stgy_count S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: odpll\<^sub>W_core_stgy_count.induct; auto intro: odpll\<^sub>W_core_stgy.intros)+

lemma odpll\<^sub>W_bnb_stgy_countD:
  \<open>odpll\<^sub>W_bnb_stgy_count S T \<Longrightarrow> odpll\<^sub>W_bnb_stgy (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_bnb_stgy_count S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: odpll\<^sub>W_bnb_stgy_count.induct; auto dest: odpll\<^sub>W_core_stgy_countD intro: odpll\<^sub>W_bnb_stgy.intros)+

lemma rtranclp_odpll\<^sub>W_bnb_stgy_countD:
  \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* S T \<Longrightarrow> odpll\<^sub>W_bnb_stgy\<^sup>*\<^sup>* (fst S) (fst T)\<close>
  \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* S T \<Longrightarrow> snd S \<subseteq># snd T\<close>
  by (induction rule: rtranclp_induct; auto dest: odpll\<^sub>W_bnb_stgy_countD)+

lemmas odpll\<^sub>W_core_stgy_count_induct = odpll\<^sub>W_core_stgy_count.induct[of \<open>(S, n)\<close> \<open>(T, m)\<close> for S n T m, split_format(complete), OF dpll_optimal_encoding_axioms,
   consumes 1]


definition conflict_clauses_are_entailed :: \<open>'st \<times> _ \<Rightarrow> bool\<close> where
\<open>conflict_clauses_are_entailed =
  (\<lambda>(S, Cs). \<forall>C \<in># Cs. (\<exists>M' K M M''. trail S = M' @ Propagated K () # M \<and> C = M'' @ Decided (-K) # M))\<close>

definition conflict_clauses_are_entailed2 :: \<open>'st \<times> ('v literal, 'v literal, unit) annotated_lits multiset \<Rightarrow> bool\<close> where
\<open>conflict_clauses_are_entailed2 =
  (\<lambda>(S, Cs). \<forall>C \<in># Cs. \<forall>C' \<in># remove1_mset C Cs. (\<exists>L. Decided L \<in> set C \<and> Propagated (-L) () \<in> set C') \<or>
    (\<exists>L.  Propagated (L) () \<in> set C \<and> Decided (-L) \<in> set C'))\<close>

lemma propagated_cons_eq_append_propagated_cons:
 \<open>Propagated L () # M = M' @ Propagated K () # Ma \<longleftrightarrow>
  (M' = [] \<and> K = L \<and> M = Ma) \<or>
  (M' \<noteq> [] \<and> hd M' = Propagated L () \<and> M = tl M' @ Propagated K () # Ma)\<close>
  by (cases M')
    auto


lemma odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close>
  shows
    \<open>conflict_clauses_are_entailed T\<close>
  using assms
  apply (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  subgoal
    apply (auto simp: dpll_propagate.simps conflict_clauses_are_entailed_def
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
    by (metis append_Cons)
  subgoal for S T
    apply (auto simp: odecide.simps conflict_clauses_are_entailed_def
      dest!: multi_member_split intro: exI[of _ \<open>Decided _ # _\<close>])
    by (metis append_Cons)+
  subgoal for S T C
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    apply (auto simp: dpll_backtrack.simps conflict_clauses_are_entailed_def
        propagated_cons_eq_append_propagated_cons is_decided_def append_eq_append_conv2
        eq_commute[of _ \<open>Propagated _ () # _\<close>] conj_disj_distribR ex_disj_distrib
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons dpll\<^sub>W_all_inv_def
      dest!: multi_member_split
      simp del: backtrack_split_list_eq
     )
     apply (case_tac us)
     by force+
  subgoal for S T C
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    apply (auto simp: bnb.backtrack_opt.simps conflict_clauses_are_entailed_def
        propagated_cons_eq_append_propagated_cons is_decided_def append_eq_append_conv2
        eq_commute[of _ \<open>Propagated _ () # _\<close>] conj_disj_distribR ex_disj_distrib
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons
      dpll\<^sub>W_all_inv_def
      dest!: multi_member_split
      simp del: backtrack_split_list_eq
     )
     apply (case_tac us)
     by force+
  done


lemma odpll\<^sub>W_bnb_stgy_count_conflict_clauses_are_entailed:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close>
  shows
    \<open>conflict_clauses_are_entailed T\<close>
  using assms odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed[of S T]
  apply (auto simp: odpll\<^sub>W_bnb_stgy_count.simps)
  apply (auto simp: conflict_clauses_are_entailed_def
    bnb.dpll\<^sub>W_bound.simps)
  done

lemma odpll\<^sub>W_core_stgy_count_no_dup_clss:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>\<forall>C \<in># snd S. no_dup C\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
    \<open>\<forall>C \<in># snd T. no_dup C\<close>
  using assms
  by (induction rule: odpll\<^sub>W_core_stgy_count.induct)
    (auto simp: dpll\<^sub>W_all_inv_def)

lemma odpll\<^sub>W_bnb_stgy_count_no_dup_clss:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>\<forall>C \<in># snd S. no_dup C\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
    \<open>\<forall>C \<in># snd T. no_dup C\<close>
  using assms
  by (induction rule: odpll\<^sub>W_bnb_stgy_count.induct)
    (auto simp: dpll\<^sub>W_all_inv_def 
      bnb.dpll\<^sub>W_bound.simps dest!: odpll\<^sub>W_core_stgy_count_no_dup_clss)

lemma backtrack_split_conflict_clauses_are_entailed_itself:
  assumes
    \<open>backtrack_split (trail S) = (M', L # M)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close>
  shows \<open>\<not> conflict_clauses_are_entailed
            (S, add_mset (trail S) C)\<close> (is \<open>\<not> ?A\<close>)
proof
  assume ?A
  then obtain M' K Ma where
    tr: \<open>trail S = M' @ Propagated K () # Ma\<close> and
    \<open>add_mset (- K) (lit_of `# mset Ma) \<subseteq>#
       add_mset (lit_of L) (lit_of `# mset M)\<close>
    by (clarsimp simp: conflict_clauses_are_entailed_def)

  then have \<open>-K \<in># add_mset (lit_of L) (lit_of `# mset M)\<close>
    by (meson member_add_mset mset_subset_eqD)
  then have \<open>-K \<in># lit_of `# mset (trail S)\<close>
    using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric] assms(1)
    by auto
  moreover have \<open>K \<in># lit_of `# mset (trail S)\<close>
    by (auto simp: tr)
  ultimately show False using invs unfolding dpll\<^sub>W_all_inv_def
    by (auto simp add: no_dup_cannot_not_lit_and_uminus uminus_lit_swap)
qed



lemma odpll\<^sub>W_core_stgy_count_distinct_mset:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
    \<open>distinct_mset (snd T)\<close>
  using assms(1,2,3,4) odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed[OF assms(1,2)]
  apply (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  subgoal
    by (auto simp: dpll_propagate.simps conflict_clauses_are_entailed_def
      cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons)
  subgoal
    by (auto simp:)
  subgoal for S T C
    by (clarsimp simp: dpll_backtrack.simps backtrack_split_conflict_clauses_are_entailed_itself
      dest!: multi_member_split)
  subgoal for S T C
    by (clarsimp simp: bnb.backtrack_opt.simps backtrack_split_conflict_clauses_are_entailed_itself
      dest!: multi_member_split)
  done

lemma odpll\<^sub>W_bnb_stgy_count_distinct_mset:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
    \<open>distinct_mset (snd T)\<close>
  using assms odpll\<^sub>W_core_stgy_count_distinct_mset[OF _ assms(2-), of T]
  by (auto simp: odpll\<^sub>W_bnb_stgy_count.simps)


lemma odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed2:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>conflict_clauses_are_entailed2 S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
      \<open>conflict_clauses_are_entailed2 T\<close>
  using assms
proof (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  case (propagate S T C)
  then show ?case
    by (auto simp: dpll_propagate.simps conflict_clauses_are_entailed2_def)
next
  case (decided S T C)
  then show ?case
    by (auto simp: dpll_decide.simps conflict_clauses_are_entailed2_def)
next
  case (backtrack S T C) note bt = this(1) and ent = this(2) and ent2 = this(3) and dist = this(4)
    and invs = this(5)
  let ?M = \<open>(cut_and_complete_trail S)\<close>
  have \<open>conflict_clauses_are_entailed (T, add_mset ?M C)\<close> and
    dist': \<open>distinct_mset (add_mset ?M C)\<close>
    using odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed[OF _ ent, of \<open>(T, add_mset ?M C)\<close>]
    odpll\<^sub>W_core_stgy_count_distinct_mset[OF _ ent dist invs, of \<open>(T, add_mset ?M C)\<close>]
      bt by (auto dest!: odpll\<^sub>W_core_stgy_count.intros(3)[of S T C])

  obtain M1 K M2 where
    spl: \<open>backtrack_split (trail S) = (M2, Decided K # M1)\<close>
    using bt backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    by (cases \<open>hd (snd (backtrack_split (trail S)))\<close>) (auto simp: dpll_backtrack.simps)
  have has_dec: \<open>\<exists>l\<in>set (trail S). is_decided l\<close>
    using bt apply (auto simp: dpll_backtrack.simps)
    using bt count_decided_0_iff no_step_dpll_backtrack_iff by blast

  let ?P = \<open>\<lambda>Ca C'.
          (\<exists>L. Decided L \<in> set Ca \<and> Propagated (- L) () \<in> set C') \<or>
          (\<exists>L. Propagated L () \<in> set Ca \<and> Decided (- L)  \<in> set C')\<close>
  have \<open>\<forall>C'\<in>#remove1_mset ?M C. ?P ?M C'\<close>
  proof
    fix C'
    assume \<open>C'\<in>#remove1_mset ?M C\<close>
    then have \<open>C' \<in># C\<close> and \<open>C' \<noteq> ?M\<close>
      using dist' by auto
    then obtain M' L M M'' where
      \<open>trail S = M' @ Propagated L () # M\<close> and
      \<open>C' = M'' @ Decided (- L) # M\<close>
      using ent unfolding conflict_clauses_are_entailed_def
      by auto
    then show \<open>?P ?M C'\<close>
      using backtrack_split_some_is_decided_then_snd_has_hd[of \<open>trail S\<close>, OF has_dec]
        spl backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      by (clarsimp simp: conj_disj_distribR ex_disj_distrib  decided_cons_eq_append_decide_cons
        cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons propagated_cons_eq_append_propagated_cons
        append_eq_append_conv2)
  qed
  moreover have H: \<open>?case \<longleftrightarrow> (\<forall>Ca\<in>#add_mset ?M C.
       \<forall>C'\<in>#remove1_mset Ca C. ?P Ca C')\<close>
    unfolding conflict_clauses_are_entailed2_def prod.case
    apply (intro conjI iffI impI ballI)
    subgoal for Ca C'
      by (auto dest: multi_member_split dest: in_diffD)
    subgoal for Ca C'
      using dist'
      by (auto 5 3 dest!: multi_member_split[of Ca] dest: in_diffD)
    done
  moreover have \<open>(\<forall>Ca\<in>#C. \<forall>C'\<in>#remove1_mset Ca C. ?P Ca C')\<close>
    using ent2 unfolding conflict_clauses_are_entailed2_def
    by auto
  ultimately show ?case
    unfolding H
    by auto
next
  case (backtrack_opt S T C) note bt = this(1) and ent = this(2) and ent2 = this(3) and dist = this(4)
    and invs = this(5)
  let ?M = \<open>(cut_and_complete_trail S)\<close>
  have \<open>conflict_clauses_are_entailed (T, add_mset ?M C)\<close> and
    dist': \<open>distinct_mset (add_mset ?M C)\<close>
    using odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed[OF _ ent, of \<open>(T, add_mset ?M C)\<close>]
    odpll\<^sub>W_core_stgy_count_distinct_mset[OF _ ent dist invs, of \<open>(T, add_mset ?M C)\<close>]
      bt by (auto dest!: odpll\<^sub>W_core_stgy_count.intros(4)[of S T C])

  obtain M1 K M2 where
    spl: \<open>backtrack_split (trail S) = (M2, Decided K # M1)\<close>
    using bt backtrack_split_snd_hd_decided[of \<open>trail S\<close>]
    by (cases \<open>hd (snd (backtrack_split (trail S)))\<close>) (auto simp: bnb.backtrack_opt.simps)
  have has_dec: \<open>\<exists>l\<in>set (trail S). is_decided l\<close>
    using bt apply (auto simp: bnb.backtrack_opt.simps)
    by (metis annotated_lit.disc(1) backtrack_split_list_eq in_set_conv_decomp snd_conv spl)

  let ?P = \<open>\<lambda>Ca C'.
          (\<exists>L. Decided L \<in> set Ca \<and> Propagated (- L) () \<in> set C') \<or>
          (\<exists>L. Propagated L () \<in> set Ca \<and> Decided (- L)  \<in> set C')\<close>
  have \<open>\<forall>C'\<in>#remove1_mset ?M C. ?P ?M C'\<close>
  proof
    fix C'
    assume \<open>C'\<in>#remove1_mset ?M C\<close>
    then have \<open>C' \<in># C\<close> and \<open>C' \<noteq> ?M\<close>
      using dist' by auto
    then obtain M' L M M'' where
      \<open>trail S = M' @ Propagated L () # M\<close> and
      \<open>C' = M'' @ Decided (- L) # M\<close>
      using ent unfolding conflict_clauses_are_entailed_def
      by auto
    then show \<open>?P ?M C'\<close>
      using backtrack_split_some_is_decided_then_snd_has_hd[of \<open>trail S\<close>, OF has_dec]
        spl backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
      by (clarsimp simp: conj_disj_distribR ex_disj_distrib  decided_cons_eq_append_decide_cons
        cdcl\<^sub>W_restart_mset.propagated_cons_eq_append_decide_cons propagated_cons_eq_append_propagated_cons
        append_eq_append_conv2)
  qed
  moreover have H: \<open>?case \<longleftrightarrow> (\<forall>Ca\<in>#add_mset ?M C.
       \<forall>C'\<in>#remove1_mset Ca C. ?P Ca C')\<close>
    unfolding conflict_clauses_are_entailed2_def prod.case
    apply (intro conjI iffI impI ballI)
    subgoal for Ca C'
      by (auto dest: multi_member_split dest: in_diffD)
    subgoal for Ca C'
      using dist'
      by (auto 5 3 dest!: multi_member_split[of Ca] dest: in_diffD)
    done
  moreover have \<open>(\<forall>Ca\<in>#C. \<forall>C'\<in>#remove1_mset Ca C. ?P Ca C')\<close>
    using ent2 unfolding conflict_clauses_are_entailed2_def
    by auto
  ultimately show ?case
    unfolding H
    by auto
qed


lemma odpll\<^sub>W_bnb_stgy_count_conflict_clauses_are_entailed2:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>conflict_clauses_are_entailed2 S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close>
  shows
    \<open>conflict_clauses_are_entailed2 T\<close>
  using assms odpll\<^sub>W_core_stgy_count_conflict_clauses_are_entailed2[of S T]
  apply (auto simp: odpll\<^sub>W_bnb_stgy_count.simps)
  apply (auto simp: conflict_clauses_are_entailed2_def
    bnb.dpll\<^sub>W_bound.simps)
  done

definition no_complement_set_lit :: \<open>'v dpll\<^sub>W_ann_lits \<Rightarrow> bool\<close> where
  \<open>no_complement_set_lit M \<longleftrightarrow>
    (\<forall>L \<in> \<Delta>\<Sigma>. Decided (Pos (replacement_pos L)) \<in> set M \<longrightarrow> Decided (Pos (replacement_neg L)) \<notin> set M) \<and>
    (\<forall>L \<in> \<Delta>\<Sigma>. Decided (Neg (replacement_pos L)) \<notin> set M) \<and>
    (\<forall>L \<in> \<Delta>\<Sigma>. Decided (Neg (replacement_neg L)) \<notin> set M) \<and>
    atm_of ` lits_of_l M \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>

definition no_complement_set_lit_st :: \<open>'st \<times> 'v dpll\<^sub>W_ann_lits multiset \<Rightarrow> bool\<close> where
  \<open>no_complement_set_lit_st = (\<lambda>(S, Cs). (\<forall>C\<in>#Cs. no_complement_set_lit C) \<and> no_complement_set_lit (trail S))\<close>

lemma backtrack_no_complement_set_lit: \<open>no_complement_set_lit (trail S) \<Longrightarrow>
       backtrack_split (trail S) = (M', L # M) \<Longrightarrow>
       no_complement_set_lit (Propagated (- lit_of L) () # M)\<close>
  using backtrack_split_list_eq[of \<open>trail S\<close>, symmetric]
  by (auto simp: no_complement_set_lit_def)

lemma odpll\<^sub>W_core_stgy_count_no_complement_set_lit_st:
  assumes
    \<open>odpll\<^sub>W_core_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>conflict_clauses_are_entailed2 S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close> and
    \<open>no_complement_set_lit_st S\<close> and
    atms: \<open>clauses (fst S) = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close> and
    \<open>no_smaller_propa (fst S)\<close>
  shows
      \<open>no_complement_set_lit_st T\<close>
  using assms
proof (induction rule: odpll\<^sub>W_core_stgy_count.induct)
  case (propagate S T C)
  then show ?case
    using atms_of_mm_penc_subset2[of N] \<Delta>\<Sigma>_\<Sigma>
    apply (auto simp: dpll_propagate.simps no_complement_set_lit_st_def no_complement_set_lit_def
      dpll\<^sub>W_all_inv_def dest!: multi_member_split)
    apply blast
    apply blast
    apply auto
    done
next
  case (decided S T C)
  have H1: False if \<open>Decided (Pos (L\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail S)\<close>
    \<open>undefined_lit (trail S) (Pos (L\<^sup>\<mapsto>\<^sup>1))\<close> \<open>L \<in> \<Delta>\<Sigma>\<close> for L
  proof -
    have \<open>{#Neg (L\<^sup>\<mapsto>\<^sup>0), Neg (L\<^sup>\<mapsto>\<^sup>1)#} \<in># clauses S\<close>
      using decided that
      by (fastforce simp: penc_def additional_constraints_def additional_constraint_def)
    then show False
      using decided(2) that
      apply (auto 7 4 simp: dpll_propagate.simps add_mset_eq_add_mset all_conj_distrib
          imp_conjR imp_conjL remove1_mset_empty_iff defined_lit_Neg_Pos_iff lits_of_def
        dest!: multi_member_split dest: in_lits_of_l_defined_litD)
      apply (metis (full_types) image_iff lit_of.simps(1))
      apply auto
      apply (metis (full_types) image_iff lit_of.simps(1))
      done
  qed
  have H2: False if \<open>Decided (Pos (L\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail S)\<close>
    \<open>undefined_lit (trail S) (Pos (L\<^sup>\<mapsto>\<^sup>0))\<close> \<open>L \<in> \<Delta>\<Sigma>\<close> for L
  proof -
    have \<open>{#Neg (L\<^sup>\<mapsto>\<^sup>0), Neg (L\<^sup>\<mapsto>\<^sup>1)#} \<in># clauses S\<close>
      using decided that
      by (fastforce simp: penc_def additional_constraints_def additional_constraint_def)
    then show False
      using decided(2) that
      apply (auto 7 4 simp: dpll_propagate.simps add_mset_eq_add_mset all_conj_distrib
          imp_conjR imp_conjL remove1_mset_empty_iff defined_lit_Neg_Pos_iff lits_of_def
        dest!: multi_member_split dest: in_lits_of_l_defined_litD)
      apply (metis (full_types) image_iff lit_of.simps(1))
      apply auto
      apply (metis (full_types) image_iff lit_of.simps(1))
      done
  qed
  have \<open>?case \<longleftrightarrow> no_complement_set_lit (trail T)\<close>
    using decided(1,7) unfolding no_complement_set_lit_st_def
    by (auto simp: odecide.simps)
  moreover have \<open>no_complement_set_lit (trail T)\<close>
  proof -
    have H: \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow>
        Decided (Pos (L\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail S) \<Longrightarrow>
        Decided (Pos (L\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail S) \<Longrightarrow> False\<close>
      \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> Decided (Neg (L\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail S) \<Longrightarrow> False\<close> 
      \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> Decided (Neg (L\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail S) \<Longrightarrow> False\<close>
      \<open>atm_of ` lits_of_l (trail S) \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
      for L
      using decided(7) unfolding no_complement_set_lit_st_def no_complement_set_lit_def
      by blast+
    have \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow>
        Decided (Pos (L\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail T) \<Longrightarrow>
        Decided (Pos (L\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail T) \<Longrightarrow> False\<close> for L
      using decided(1) H(1)[of L] H1[of L] H2[of L]
      by (auto simp: odecide.simps no_complement_set_lit_def)
    moreover have \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> Decided (Neg (L\<^sup>\<mapsto>\<^sup>1)) \<in> set (trail T) \<Longrightarrow> False\<close> for L
      using decided(1) H(2)[of L]
      by (auto simp: odecide.simps no_complement_set_lit_def)
    moreover have \<open>L \<in> \<Delta>\<Sigma> \<Longrightarrow> Decided (Neg (L\<^sup>\<mapsto>\<^sup>0)) \<in> set (trail T) \<Longrightarrow> False\<close> for L
      using decided(1) H(3)[of L]
      by (auto simp: odecide.simps no_complement_set_lit_def)
    moreover have \<open>atm_of ` lits_of_l (trail T) \<subseteq> \<Sigma> - \<Delta>\<Sigma> \<union> replacement_pos ` \<Delta>\<Sigma> \<union> replacement_neg ` \<Delta>\<Sigma>\<close>
      using decided(1) H(4)
      by (auto 5 3 simp: odecide.simps no_complement_set_lit_def lits_of_def image_image)

    ultimately show ?thesis
      by (auto simp: no_complement_set_lit_def)
  qed
  ultimately show ?case
     by fast

next
  case (backtrack S T C) note bt = this(1) and ent = this(2) and ent2 = this(3) and dist = this(4)
    and invs = this(6)
  show ?case
    using bt invs
    by (auto simp: dpll_backtrack.simps no_complement_set_lit_st_def
      backtrack_no_complement_set_lit)

next
  case (backtrack_opt S T C) note bt = this(1) and ent = this(2) and ent2 = this(3) and dist = this(4)
    and invs = this(6)
  show ?case
    using bt invs
    by (auto simp: bnb.backtrack_opt.simps no_complement_set_lit_st_def
      backtrack_no_complement_set_lit)
qed

lemma odpll\<^sub>W_bnb_stgy_count_no_complement_set_lit_st:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    \<open>conflict_clauses_are_entailed2 S\<close> and
    \<open>distinct_mset (snd S)\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close> and
    \<open>no_complement_set_lit_st S\<close> and
    atms: \<open>clauses (fst S) = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close> and
    \<open>no_smaller_propa (fst S)\<close>
  shows
      \<open>no_complement_set_lit_st T\<close>
  using odpll\<^sub>W_core_stgy_count_no_complement_set_lit_st[of S T, OF _ assms(2-)] assms(1,6)
  by (auto simp: odpll\<^sub>W_bnb_stgy_count.simps no_complement_set_lit_st_def
    bnb.dpll\<^sub>W_bound.simps)

definition stgy_invs :: \<open>'v clauses \<Rightarrow> 'st \<times> _ \<Rightarrow> bool\<close> where
  \<open>stgy_invs N S \<longleftrightarrow>
    no_smaller_propa (fst S) \<and>
    conflict_clauses_are_entailed S \<and>
    conflict_clauses_are_entailed2 S \<and>
    distinct_mset (snd S) \<and>
    (\<forall>C \<in># snd S. no_dup C) \<and>
    dpll\<^sub>W_all_inv (bnb.abs_state (fst S)) \<and>
    no_complement_set_lit_st S \<and>
    clauses (fst S) = penc N \<and>
    atms_of_mm N = \<Sigma>
    \<close>

lemma odpll\<^sub>W_bnb_stgy_count_stgy_invs:
  assumes
    \<open>odpll\<^sub>W_bnb_stgy_count S T\<close> and
    \<open>stgy_invs N S\<close>
  shows \<open>stgy_invs N T\<close>
  using odpll\<^sub>W_bnb_stgy_count_conflict_clauses_are_entailed2[of S T]
    odpll\<^sub>W_bnb_stgy_count_conflict_clauses_are_entailed[of S T]
    odpll\<^sub>W_bnb_stgy_no_smaller_propa[of \<open>fst S\<close> \<open>fst T\<close>]
    odpll\<^sub>W_bnb_stgy_countD[of S T]
    odpll\<^sub>W_bnb_stgy_clauses[of \<open>fst S\<close> \<open>fst T\<close>]
    odpll\<^sub>W_core_stgy_count_distinct_mset[of S T]
    odpll\<^sub>W_bnb_stgy_count_no_dup_clss[of S T]
    odpll\<^sub>W_bnb_stgy_count_distinct_mset[of S T]
    assms
    odpll\<^sub>W_bnb_stgy_dpll\<^sub>W_bnb_stgy[of \<open>fst S\<close> N \<open>fst T\<close>]
    odpll\<^sub>W_bnb_stgy_count_no_complement_set_lit_st[of S T]
  using local.bnb.dpll\<^sub>W_bnb_abs_state_all_inv
  unfolding stgy_invs_def
  by auto

lemma stgy_invs_size_le:
  assumes \<open>stgy_invs N S\<close>
  shows \<open>size (snd S) \<le> 3 ^ (card \<Sigma>)\<close>
proof -
  have \<open>no_smaller_propa (fst S)\<close> and
    \<open>conflict_clauses_are_entailed S\<close> and
    ent2: \<open>conflict_clauses_are_entailed2 S\<close> and
    dist: \<open>distinct_mset (snd S)\<close> and
    n_d: \<open>(\<forall>C \<in># snd S. no_dup C)\<close> and
    \<open>dpll\<^sub>W_all_inv (bnb.abs_state (fst S))\<close> and
    nc: \<open>no_complement_set_lit_st S\<close> and
    \<Sigma>: \<open>atms_of_mm N = \<Sigma>\<close>
    using assms unfolding stgy_invs_def by fast+

  let ?f = \<open>(filter_mset is_decided o mset)\<close>
  have \<open>distinct_mset (?f `# (snd S))\<close>
    apply (subst distinct_image_mset_inj)
    subgoal
      using ent2 n_d
      apply (auto simp: conflict_clauses_are_entailed2_def
        inj_on_def add_mset_eq_add_mset dest!: multi_member_split split_list)
      using n_d apply auto
      apply (metis defined_lit_def multiset_partition set_mset_mset union_iff union_single_eq_member)+
      done
    subgoal
      using dist by auto
    done
  have H: \<open>lit_of `# ?f C \<in> all_sound_trails list_new_vars\<close> if \<open>C \<in># (snd S)\<close> for C
  proof -
    have nc: \<open>no_complement_set_lit C\<close> and n_d: \<open>no_dup C\<close>
      using nc that n_d unfolding no_complement_set_lit_st_def
      by (auto dest!: multi_member_split)
    have taut: \<open>\<not>tautology (lit_of `#  mset C)\<close>
      using n_d no_dup_not_tautology by blast
    have taut: \<open>\<not>tautology (lit_of `# ?f C)\<close>
      apply (rule not_tautology_mono[OF _ taut])
      by (simp add: image_mset_subseteq_mono)
    have dist: \<open>distinct_mset (lit_of `#  mset C)\<close>
      using n_d no_dup_distinct by blast
    have dist: \<open>distinct_mset (lit_of `# ?f C)\<close>
      apply (rule distinct_mset_mono[OF _ dist])
      by (simp add: image_mset_subseteq_mono)

    show ?thesis
      apply (rule in_all_sound_trails)
      subgoal
        using nc unfolding no_complement_set_lit_def
        by (auto dest!: multi_member_split simp: is_decided_def)
      subgoal
        using nc unfolding no_complement_set_lit_def
        by (auto dest!: multi_member_split simp: is_decided_def)
      subgoal
        using nc unfolding no_complement_set_lit_def
        by (auto dest!: multi_member_split simp: is_decided_def)
      subgoal
        using nc n_d taut dist unfolding no_complement_set_lit_def set_list_new_vars
        by (auto dest!: multi_member_split simp: set_list_new_vars
          is_decided_def simple_clss_def atms_of_def lits_of_def
          image_image dest!: split_list)
      subgoal
        by (auto simp: set_list_new_vars)
      done
  qed
  then have incl: \<open>set_mset ((image_mset lit_of o ?f) `# (snd S)) \<subseteq> all_sound_trails list_new_vars\<close>
    by auto
  have K: \<open>xs \<noteq> [] \<Longrightarrow> \<exists>y ys. xs = y # ys\<close> for xs
    by (cases xs) auto
  have K2: \<open>Decided La # zsb = us @ Propagated (L) () # zsa \<longleftrightarrow>
    (us \<noteq> [] \<and> hd us = Decided La \<and> zsb = tl us @ Propagated (L) () # zsa)\<close> for La zsb us L zsa
    apply (cases us)
    apply auto
    done
  have inj: \<open>inj_on ((`#) lit_of \<circ> (filter_mset is_decided \<circ> mset))
     (set_mset (snd S))\<close>
     unfolding inj_on_def
  proof (intro ballI impI, rule ccontr)
    fix x y
    assume x: \<open>x \<in># snd S\<close> and
      y: \<open>y \<in># snd S\<close> and
      eq: \<open>((`#) lit_of \<circ> (filter_mset is_decided \<circ> mset)) x =
         ((`#) lit_of \<circ> (filter_mset is_decided \<circ> mset)) y\<close> and
      neq: \<open>x \<noteq> y\<close>
    consider
      L where \<open>Decided L \<in> set x\<close> \<open>Propagated (- L) () \<in> set y\<close> |
      L where \<open>Decided L \<in> set y\<close> \<open>Propagated (- L) () \<in> set x\<close>
      using ent2 n_d x y unfolding conflict_clauses_are_entailed2_def
      by (auto  dest!: multi_member_split simp: add_mset_eq_add_mset neq)
    then show False
    proof cases
      case 1
      show False
        using eq 1(1) multi_member_split[of \<open>Decided L\<close> \<open>mset x\<close>]
        apply auto
        by (smt "1"(2) lit_of.simps(2) msed_map_invR multiset_partition n_d
          no_dup_cannot_not_lit_and_uminus set_mset_mset union_mset_add_mset_left union_single_eq_member y)
    next
      case 2
      show False
        using eq 2 multi_member_split[of \<open>Decided L\<close> \<open>mset y\<close>]
        apply auto
        by (smt lit_of.simps(2) msed_map_invR multiset_partition n_d
          no_dup_cannot_not_lit_and_uminus set_mset_mset union_mset_add_mset_left union_single_eq_member x)
    qed
  qed

  have [simp]: \<open>finite \<Sigma>\<close>
    unfolding \<Sigma>[symmetric]
    by auto
  have [simp]: \<open>\<Sigma> \<union> \<Delta>\<Sigma> = \<Sigma>\<close>
    using \<Delta>\<Sigma>_\<Sigma> by blast
  have \<open>size (snd S) = size (((image_mset lit_of o ?f) `# (snd S)))\<close>
    by auto
  also have \<open>... = card (set_mset ((image_mset lit_of o ?f) `# (snd S)))\<close>
    supply [[goals_limit=1]]
    apply (subst distinct_mset_size_eq_card)
    apply (subst distinct_image_mset_inj[OF inj])
    using dist by auto
  also have \<open>... \<le> card (all_sound_trails list_new_vars)\<close>
    by (rule card_mono[OF _ incl]) simp
  also have \<open>... \<le> card (simple_clss (\<Sigma> - \<Delta>\<Sigma>)) * 3 ^ card \<Delta>\<Sigma>\<close>
    using card_all_sound_trails[of list_new_vars]
    by (auto simp: set_list_new_vars distinct_list_new_vars
      length_list_new_vars)
  also have \<open>... \<le> 3 ^ card (\<Sigma> - \<Delta>\<Sigma>) * 3 ^ card \<Delta>\<Sigma>\<close>
    using simple_clss_card[of \<open>\<Sigma> - \<Delta>\<Sigma>\<close>]
    unfolding set_list_new_vars distinct_list_new_vars
      length_list_new_vars
    by (auto simp: set_list_new_vars distinct_list_new_vars
      length_list_new_vars)
  also have \<open>... = (3 :: nat) ^ (card \<Sigma>)\<close>
    unfolding comm_semiring_1_class.semiring_normalization_rules(26)
    by (subst card_Un_disjoint[symmetric])
      auto
  finally show \<open>size (snd S) \<le> 3 ^ card \<Sigma>\<close>
    .
qed

lemma rtranclp_odpll\<^sub>W_bnb_stgy_count_stgy_invs: \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* S T \<Longrightarrow> stgy_invs N S \<Longrightarrow> stgy_invs N T\<close>
  apply (induction rule: rtranclp_induct)
  apply (auto dest!: odpll\<^sub>W_bnb_stgy_count_stgy_invs)
  done

theorem (* \htmllink{ODPLL-complexity} *)
  assumes \<open>clauses S = penc N\<close> \<open>atms_of_mm N = \<Sigma>\<close> and
    \<open>odpll\<^sub>W_bnb_stgy_count\<^sup>*\<^sup>* (S, {#}) (T, D)\<close> and
    tr: \<open>trail S = []\<close>
  shows \<open>size D \<le> 3 ^ (card \<Sigma>)\<close>
proof -
  have i: \<open>stgy_invs N (S, {#})\<close>
    using tr unfolding no_smaller_propa_def
      stgy_invs_def conflict_clauses_are_entailed_def
      conflict_clauses_are_entailed2_def assms(1,2)
      no_complement_set_lit_st_def no_complement_set_lit_def
      dpll\<^sub>W_all_inv_def
    by (auto simp: assms(1))
  show ?thesis
    using rtranclp_odpll\<^sub>W_bnb_stgy_count_stgy_invs[OF assms(3) i]
      stgy_invs_size_le[of N \<open>(T, D)\<close>]
    by auto
qed

end

end
