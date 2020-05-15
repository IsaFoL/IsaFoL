(*  Title:       Extensions to the Prover Architectures of the Saturation Framework
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Extensions to the Prover Architectures of the Saturation Framework\<close>

theory Prover_Architectures_Extensions
  imports Saturation_Framework.Prover_Architectures
begin

text \<open>The given clause and lazy given clause procedures satisfy a key saturation invariant. This
provides an alternative way to study them.\<close>


section \<open>Library\<close>

context prover_architecture_basis
begin

lemma in_Inf_FL_imp_to_F_in_Inf_F: "\<iota> \<in> Inf_FL \<Longrightarrow> to_F \<iota> \<in> Inf_F"
  by (simp add: Inf_FL_to_Inf_F to_F_def)

lemma in_Inf_from_imp_to_F_in_Inf_from: "\<iota> \<in> Inf_from N \<Longrightarrow> to_F \<iota> \<in> no_labels.Inf_from (fst ` N)"
  unfolding Inf_from_def no_labels.Inf_from_def to_F_def by (auto intro: Inf_FL_to_Inf_F)

end


section \<open>Given Clause Procedure\<close>

context given_clause
begin

abbreviation invar :: "('f \<times> 'l) set \<Rightarrow> bool" where
  "invar N \<equiv> Inf_from (active_subset N) \<subseteq> Red_Inf_\<G>_Q N"

lemma invar_Liminf_llist:
  assumes
    red: "chain (\<rhd>RedL) Ns" and
    invar: "\<forall>i. enat i < llength Ns \<longrightarrow> invar (lnth Ns i)"
  shows "invar (Liminf_llist Ns)"
proof
  fix \<iota>
  assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (Liminf_llist Ns))"

  define As where
    "As = lmap active_subset Ns"

  have act_ns: "active_subset (Liminf_llist Ns) = Liminf_llist As"
    unfolding As_def active_subset_def by (rule Liminf_set_filter_commute[symmetric])

  note \<iota>_inf = Inf_if_Inf_from[OF \<iota>_inff]
  note \<iota>_inff' = \<iota>_inff[unfolded act_ns]
  note fin = finite_set[of "prems_of \<iota>"]

  have "\<not> lnull As"
    unfolding As_def using chain_not_lnull[OF red] by auto
  moreover have "set (prems_of \<iota>) \<subseteq> Liminf_llist As"
    using \<iota>_inff'[unfolded Inf_from_def] by simp
  ultimately obtain i where
    i_lt: "enat i < llength As" and
    prems_sub_ge_i: "set (prems_of \<iota>) \<subseteq> \<Inter> (lnth As ` {j. i \<le> j \<and> enat j < llength As})"
    using finite_subset_Liminf_llist_imp_exists_index by blast

  have "set (prems_of \<iota>) \<subseteq> lnth As i"
    using prems_sub_ge_i i_lt by auto
  then have "\<iota> \<in> Inf_from (active_subset (lnth Ns i))"
    using i_lt \<iota>_inf unfolding Inf_from_def As_def by auto
  then have "\<iota> \<in> Red_Inf_\<G>_Q (lnth Ns i)"
    using i_lt[unfolded As_def] invar by auto
  then show "\<iota> \<in> Red_Inf_\<G>_Q (Liminf_llist Ns)"
    using red i_in_Liminf_or_Red_F[of Ns i] i_lt[unfolded As_def] Red_Inf_subset_Liminf by auto
qed

lemma gc_invar_init: "active_subset N = {} \<Longrightarrow> invar N"
  unfolding Inf_from_def using labeled_inf_have_prems by auto

lemma gc_invar_step:
  assumes
    invar: "invar N1" and
    step: "N1 \<Longrightarrow>GC N2"
  shows "invar N2"
  using step invar
proof induct
  case (process N1 N M N2 M')
  note n1 = this(1) and n2 = this(2) and m_red = this(3) and m'_pas = this(4) and inv = this(5)

  have "Inf_from (active_subset N2) \<subseteq> Inf_from (active_subset N1)"
    unfolding n1 n2 Inf_from_def using m'_pas by auto
  also have "... \<subseteq> Red_Inf_\<G>_Q N1"
    by (rule inv)
  also have "... \<subseteq> Red_Inf_\<G>_Q (N1 \<union> N2)"
    unfolding n1 n2 using Red_Inf_of_subset by auto
  also have "... \<subseteq> Red_Inf_\<G>_Q N2"
  proof
    fix \<iota>
    assume \<iota>_in: "\<iota> \<in> Red_Inf_\<G>_Q (N1 \<union> N2)"
    have "Red_F_\<G>_Q N2 \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      by (simp add: Red_F_of_subset)
    then have "M \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      using m_red unfolding n1 n2 by blast
    then have "\<iota> \<in> Red_Inf_\<G>_Q (N1 \<union> N2 - M)"
      using \<iota>_in Red_Inf_of_Red_F_subset unfolding n1 n2 by blast
    then show "\<iota> \<in> Red_Inf_\<G>_Q N2"
      using Red_Inf_of_subset[of "N1 \<union> N2 - M" N2] unfolding n1 n2 by auto
  qed
  finally show ?case
    .
next
  case (infer N1 N C L N2 M)
  note n1 = this(1) and n2 = this(2) and l_pas = this(3) and m_pas = this(4) and
    inff_red = this(5) and inv = this(6)
  show ?case
    unfolding n1 n2
  proof
    fix \<iota>
    assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)} \<union> M))"

    have \<iota>_inf: "\<iota> \<in> Inf_FL"
      using \<iota>_inff unfolding Inf_from_def by auto
    then have F\<iota>_inf: "to_F \<iota> \<in> Inf_F"
      using Inf_FL_to_Inf_F[folded to_F_def] by fastforce

    have "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)}))"
      using \<iota>_inff m_pas by simp
    then have F\<iota>_inff:
      "to_F \<iota> \<in> no_labels.Inf_from (fst ` (active_subset (N \<union> {(C, active)})))"
      using F\<iota>_inf unfolding to_F_def Inf_from_def no_labels.Inf_from_def by auto

    show "\<iota> \<in> Red_Inf_\<G>_Q (N \<union> {(C, active)} \<union> M)"
    proof (cases "to_F \<iota> \<in> no_labels.Inf_from2 (fst ` active_subset N) {C}")
      case True
      then have "to_F \<iota> \<in> no_labels.Red_Inf_\<G>_Q (fst ` (N \<union> {(C, active)} \<union> M))"
        using inff_red by auto
      then show ?thesis
        by (subst labeled_red_inf_eq_red_inf[OF \<iota>_inf])
    next
      case False
      then have "to_F \<iota> \<in> no_labels.Inf_from (fst ` active_subset N)"
        using F\<iota>_inff unfolding no_labels.Inf_from_def no_labels.Inf_from2_def by auto
      then have "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, L)}))"
        using \<iota>_inf l_pas unfolding to_F_def Inf_from_def no_labels.Inf_from_def
        by clarsimp (smt \<iota>_inff[unfolded Inf_from_def] active_subset_def imageE image_subset_iff
            in_mono mem_Collect_eq prod.collapse)
      then have "\<iota> \<in> Red_Inf_\<G>_Q (N \<union> {(C, L)})"
        using inv[unfolded n1 n2] by blast
      then show ?thesis
        using labeled_red_inf_eq_red_inf[OF \<iota>_inf]
        by (smt Un_insert_right Un_upper2 image_insert le_sup_iff Red_Inf_of_subset prod.sel(1)
            subsetD subset_Un_eq)
    qed
  qed
qed

lemma gc_invar:
  assumes
    gc: "chain (\<Longrightarrow>GC) Ns" and
    init: "active_subset (lnth Ns 0) = {}" and
    invar: "invar (lnth Ns 0)" and
    i_lt: "enat i < llength Ns"
  shows "invar (lnth Ns i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using gc_invar_init[OF init] by auto
next
  case (Suc i)
  note ih = this(1) and Si_lt = this(2)
  have i_lt: "enat i < llength Ns"
    using Si_lt Suc_ile_eq less_le by blast
  show ?case
    by (rule gc_invar_step[OF ih[OF i_lt]]) (rule chain_lnth_rel[OF gc Si_lt])
qed

lemma gc_Liminf_saturated_new_proof:
  assumes
    gc: "chain (\<Longrightarrow>GC) Ns" and
    init: "active_subset (lnth Ns 0) = {}" and
    lim: "passive_subset (Liminf_llist Ns) = {}"
  shows "saturated (Liminf_llist Ns)"
  unfolding saturated_def
proof -
  note red = gc_to_red[OF gc]

  have inf_init: "Inf_from (active_subset (lnth Ns 0)) = {}"
    unfolding init Inf_from_def by (simp add: labeled_inf_have_prems)

  have "Inf_from (Liminf_llist Ns) = Inf_from (active_subset (Liminf_llist Ns))" (is "?lhs = _")
    using lim unfolding active_subset_def passive_subset_def
    by (smt Collect_empty_eq mem_Collect_eq set_eq_subset subsetI)
  also have "... \<subseteq> Red_Inf_\<G>_Q (Liminf_llist Ns)" (is "_ \<subseteq> ?rhs")
    using invar_Liminf_llist[OF red] gc_invar[OF gc init, unfolded inf_init, OF empty_subsetI]
    by blast
  finally show "?lhs \<subseteq> ?rhs"
    .
qed

end


section \<open>Lazy Given Clause\<close>

context lazy_given_clause
begin

definition from_F :: "'f inference \<Rightarrow> ('f \<times> 'l) inference set" where
  "from_F \<iota> = {\<iota>' \<in> Inf_FL. to_F \<iota>' = \<iota>}"

definition invar :: "'f inference set \<times> ('f \<times> 'l) set \<Rightarrow> bool" where
  "invar TN \<longleftrightarrow> Inf_from (active_subset (snd TN)) \<subseteq> \<Union> (from_F ` (fst TN)) \<union> Red_Inf_\<G>_Q (snd TN)"

definition
  Liminf_state :: "('f inference set \<times> ('f \<times> 'l) set) llist \<Rightarrow> 'f inference set \<times> ('f \<times> 'l) set"
where
  "Liminf_state TNs = (Liminf_llist (lmap fst TNs), Liminf_llist (lmap snd TNs))"

lemma invar_Liminf_llist:
  assumes
    red: "chain (\<rhd>RedL) (lmap snd TNs)" and
    invar: "\<forall>i. enat i < llength TNs \<longrightarrow> invar (lnth TNs i)"
  shows "invar (Liminf_state TNs)"
  unfolding Liminf_state_def invar_def prod.sel
proof
  fix \<iota>
  assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (Liminf_llist (lmap snd TNs)))"

  define As where
    "As = lmap active_subset (lmap snd TNs)"

  have act_ns: "active_subset (Liminf_llist (lmap snd TNs)) = Liminf_llist As"
    unfolding As_def active_subset_def by (rule Liminf_set_filter_commute[symmetric])

  note \<iota>_inf = Inf_if_Inf_from[OF \<iota>_inff]
  note \<iota>_inff' = \<iota>_inff[unfolded act_ns]
  note fin = finite_set[of "prems_of \<iota>"]

  have
    as_nnil: "\<not> lnull As" and
    ts_nnil: "\<not> lnull (lmap fst TNs)"
    unfolding As_def using chain_not_lnull[OF red] by auto

  have "set (prems_of \<iota>) \<subseteq> Liminf_llist As"
    using \<iota>_inff'[unfolded Inf_from_def] by simp
  then obtain i where
    i_lt_as: "enat i < llength As" and
    prems_sub_ge_i: "set (prems_of \<iota>) \<subseteq> \<Inter> (lnth As ` {j. i \<le> j \<and> enat j < llength As})"
    using finite_subset_Liminf_llist_imp_exists_index[OF as_nnil fin] by blast

  show "\<iota> \<in> \<Union> (from_F ` Liminf_llist (lmap fst TNs))
    \<union> Red_Inf_\<G>_Q (Liminf_llist (lmap snd TNs))"
  proof (cases "\<iota> \<in> \<Union> (from_F ` Liminf_llist (lmap fst TNs))")
    case \<iota>_ni_lim: False

    have F\<iota>_ni_lim: "to_F \<iota> \<notin> Liminf_llist (lmap fst TNs)"
      using \<iota>_inf \<iota>_ni_lim unfolding from_F_def by auto
    obtain i' where
      i_le_i': "i \<le> i'" and
      i'_lt_as: "enat i' < llength As" and
      F\<iota>_ni_i': "to_F \<iota> \<notin> lnth (lmap fst TNs) i'"
      using i_lt_as not_Liminf_llist_imp_exists_index[OF ts_nnil F\<iota>_ni_lim, of i] unfolding As_def
      by auto

    have \<iota>_ni_i': "\<iota> \<notin> \<Union> (from_F ` fst (lnth TNs i'))"
      using F\<iota>_ni_i' i'_lt_as[unfolded As_def] unfolding from_F_def by auto

    have "set (prems_of \<iota>) \<subseteq> \<Inter> (lnth As ` {j. i' \<le> j \<and> enat j < llength As})"
      using prems_sub_ge_i i_le_i' by auto
    then have "set (prems_of \<iota>) \<subseteq> lnth As i'"
      using i'_lt_as by auto
    then have "\<iota> \<in> Inf_from (active_subset (snd (lnth TNs i')))"
      using i'_lt_as \<iota>_inf unfolding Inf_from_def As_def by auto
    then have \<iota>_in_i': "\<iota> \<in> \<Union> (from_F ` fst (lnth TNs i')) \<union> Red_Inf_\<G>_Q (snd (lnth TNs i'))"
      using i'_lt_as[unfolded As_def] invar[unfolded invar_def] by auto
    then have "\<iota> \<in> Red_Inf_\<G>_Q (snd (lnth TNs i'))"
      using \<iota>_ni_i' by auto
    then have "\<iota> \<in> Red_Inf_\<G>_Q (Liminf_llist (lmap snd TNs))"
      using \<iota>_in_i' i_in_Liminf_or_Red_F[of _ i', OF red]
        i'_lt_as[unfolded As_def, simplified] Red_Inf_subset_Liminf[OF red]
      by auto
    then show ?thesis
      using red i_in_Liminf_or_Red_F[of "lmap snd TNs" i] i_lt_as[unfolded As_def]
        Red_Inf_subset_Liminf by auto
  qed fast
qed

lemma lgc_invar_init:
  assumes
    n_init: "active_subset (snd TN) = {}" and
    t_init: "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> fst TN"
  shows "invar TN"
  unfolding n_init invar_def prod.sel Inf_from_def from_F_def using t_init
  by (fastforce dest: Inf_FL_to_Inf_F in_Inf_FL_imp_to_F_in_Inf_F simp: to_F_def)

lemma lgc_invar_step:
  assumes
    invar: "invar TN1" and
    step: "TN1 \<Longrightarrow>LGC TN2"
  shows "invar TN2"
  using step invar
proof induction
  case (process N1 N M N2 M' T)
  note n1 = this(1) and n2 = this(2) and m_red = this(3) and m'_pas = this(4) and inv = this(5)

  have "Inf_from (active_subset N2) \<subseteq> Inf_from (active_subset N1)"
    unfolding n1 n2 Inf_from_def using m'_pas by auto
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N1"
    using inv unfolding invar_def by simp
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2)"
    unfolding n1 n2 by (rule Un_mono[OF order.refl Red_Inf_of_subset]) blast
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N2"
  proof
    fix \<iota>
    assume \<iota>_in: "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2)"
    have "Red_F_\<G>_Q N2 \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      by (simp add: Red_F_of_subset)
    then have "M \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      using m_red unfolding n1 n2 by blast
    then have "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2 - M)"
      using \<iota>_in Red_Inf_of_Red_F_subset unfolding n1 n2 by blast
    then show "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N2"
      using Red_Inf_of_subset[of "N1 \<union> N2 - M" N2] unfolding n1 n2 by auto
  qed
  finally show ?case
    unfolding invar_def by simp
next
  case (schedule_infer T2 T1 T' N1 N C L N2)
  note t2 = this(1) and n1 = this(2) and n2 = this(3) and l_pas = this(4) and t' = this(5) and
    inv = this(6)
  show ?case
    unfolding invar_def prod.sel t2 n1 n2
  proof
    fix \<iota>
    assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)}))"

    have \<iota>_inf: "\<iota> \<in> Inf_FL"
      using \<iota>_inff unfolding Inf_from_def by auto
    then have F\<iota>_inf: "to_F \<iota> \<in> Inf_F"
      using Inf_FL_to_Inf_F[folded to_F_def] by fastforce

    have F\<iota>_inff:
      "to_F \<iota> \<in> no_labels.Inf_from (fst ` (active_subset (N \<union> {(C, active)})))"
      using \<iota>_inff F\<iota>_inf unfolding to_F_def Inf_from_def no_labels.Inf_from_def by auto

    show "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T')) \<union> Red_Inf_\<G>_Q (N \<union> {(C, active)})"
    proof (cases "to_F \<iota> \<in> no_labels.Inf_from2 (fst ` active_subset N) {C}")
      case True
      then have "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T'))"
        unfolding t' from_F_def using \<iota>_inf by auto
      then show ?thesis
        by blast
    next
      case False
      then have "to_F \<iota> \<in> no_labels.Inf_from (fst ` active_subset N)"
        using F\<iota>_inff unfolding no_labels.Inf_from_def no_labels.Inf_from2_def by auto
      then have "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, L)}))"
        using \<iota>_inf l_pas unfolding to_F_def Inf_from_def no_labels.Inf_from_def
        by clarsimp (smt \<iota>_inff[unfolded Inf_from_def] active_subset_def imageE image_subset_iff
            in_mono mem_Collect_eq prod.collapse)
      then have "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T')) \<union> Red_Inf_\<G>_Q (N \<union> {(C, L)})"
        using inv[unfolded invar_def n1 n2] by auto
      then show ?thesis
        using labeled_red_inf_eq_red_inf[OF \<iota>_inf] by simp
    qed
  qed
next
  case (compute_infer T1 T2 \<iota> N2 N1 M)
  note t1 = this(1) and n2 = this(2) and m_pas = this(3) and \<iota>_red = this(4) and inv = this(5)
  show ?case
    unfolding invar_def prod.sel n2
  proof
    fix \<iota>'
    assume \<iota>'_inff: "\<iota>' \<in> Inf_from (active_subset (N1 \<union> M))"

    have \<iota>'_bef: "\<iota>' \<in> \<Union> (from_F ` (T2 \<union> {\<iota>})) \<union> Red_Inf_\<G>_Q N1"
      using \<iota>'_inff inv[unfolded invar_def t1] m_pas by auto
    then show "\<iota>' \<in> \<Union> (from_F ` T2) \<union> Red_Inf_\<G>_Q (N1 \<union> M)"
    proof (cases "\<iota>' \<in> \<Union> (from_F ` (T2 \<union> {\<iota>}))")
      case \<iota>'_in_t2_or_\<iota>: True
      then show ?thesis
      proof (cases "\<iota>' \<in> from_F \<iota>")
        case \<iota>'_in_\<iota>: True
        then have "\<iota>' \<in> Red_Inf_\<G>_Q (N1 \<union> M)"
          using \<iota>_red from_F_def labeled_red_inf_eq_red_inf by auto
        then show ?thesis
          by auto
      next
        case False
        then have "\<iota>' \<in> \<Union> (from_F ` T2)"
          using \<iota>'_in_t2_or_\<iota> by auto
        then show ?thesis
          by auto
      qed
    next
      case False
      then have "\<iota>' \<in> Red_Inf_\<G>_Q N1"
        using \<iota>'_bef by simp
      then show ?thesis
        by (metis (no_types, lifting) UnCI local.Red_Inf_of_subset subset_iff)
    qed
  qed
next
  case (delete_orphans T1 T2 T' N)
  note t1 = this(1) and t'_orph = this(2) and inv = this(3)

  show ?case
    unfolding invar_def prod.sel
  proof
    fix \<iota>
    assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset N)"

    have "to_F \<iota> \<notin> T'"
      using t'_orph \<iota>_inff in_Inf_from_imp_to_F_in_Inf_from by blast
    hence "\<iota> \<notin> \<Union> (from_F ` T')"
      unfolding from_F_def by auto
    then show "\<iota> \<in> \<Union> (from_F ` T2) \<union> Red_Inf_\<G>_Q N"
      using \<iota>_inff inv unfolding t1 invar_def by auto
  qed
qed

lemma lgc_invar:
  assumes
    lgc: "chain (\<Longrightarrow>LGC) TNs" and
    n_init: "active_subset (snd (lnth TNs 0)) = {}" and
    t_init: "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> fst (lnth TNs 0)" and
    invar: "invar (lnth TNs 0)" and
    i_lt: "enat i < llength TNs"
  shows "invar (lnth TNs i)"
  using i_lt
proof (induct i)
  case 0
  then show ?case
    using lgc_invar_init[OF n_init t_init] unfolding invar_def by auto
next
  case (Suc i)
  note ih = this(1) and Si_lt = this(2)
  have i_lt: "enat i < llength TNs"
    using Si_lt Suc_ile_eq less_le by blast
  show ?case
    by (rule lgc_invar_step[OF ih[OF i_lt]]) (rule chain_lnth_rel[OF lgc Si_lt])
qed

lemma lgc_Liminf_saturated_new_proof:
  assumes
    lgc: "chain (\<Longrightarrow>LGC) TNs" and
    n_init: "active_subset (snd (lnth TNs 0)) = {}" and
    n_lim: "passive_subset (Liminf_llist (lmap snd TNs)) = {}" and
    t_init: "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> fst (lnth TNs 0)" and
    t_lim: "Liminf_llist (lmap fst TNs) = {}"
  shows "saturated (Liminf_llist (lmap snd TNs))"
  unfolding saturated_def
proof -
  note red = lgc_to_red[OF lgc]

  have "Inf_from (Liminf_llist (lmap snd TNs)) =
    Inf_from (active_subset (Liminf_llist (lmap snd TNs)))" (is "?lhs = _")
    using n_lim unfolding active_subset_def passive_subset_def
    by (smt Collect_empty_eq mem_Collect_eq set_eq_subset subsetI)
  also have "... \<subseteq> \<Union> (from_F ` Liminf_llist (lmap fst TNs))
    \<union> Red_Inf_\<G>_Q (Liminf_llist (lmap snd TNs))" (is "_ \<subseteq> ?rhs")
    using invar_Liminf_llist[OF red]
      lgc_invar[OF lgc n_init t_init lgc_invar_init[OF n_init t_init]]
    unfolding Liminf_state_def invar_def by auto
  also have "... = Red_Inf_\<G>_Q (Liminf_llist (lmap snd TNs))" (is "_ = ?rhs")
    unfolding t_lim by auto
  finally show "?lhs \<subseteq> ?rhs"
    .
qed

end

end
