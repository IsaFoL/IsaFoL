(*  Title:       Extensions to the Prover Architectures of the Saturation Framework
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Extensions to the Prover Architectures of the Saturation Framework\<close>

theory Prover_Architectures_Extensions
  imports Saturation_Framework.Prover_Architectures
begin

text \<open>TODO.\<close>


section \<open>Library\<close>

context prover_architecture_basis
begin

lemma in_Inf_FL_imp_to_F_in_Inf_F: "\<iota> \<in> Inf_FL \<Longrightarrow> to_F \<iota> \<in> Inf_F"
  by (simp add: Inf_FL_to_Inf_F to_F_def)

lemma in_Inf_from_imp_to_F_in_Inf_from: "\<iota> \<in> Inf_from N \<Longrightarrow> to_F \<iota> \<in> no_labels.Inf_from (fst ` N)"
  unfolding Inf_from_def no_labels.Inf_from_def to_F_def by (auto intro:  Inf_FL_to_Inf_F)

end


section \<open>Given Clause Procedure\<close>

context given_clause
begin

abbreviation invar :: "('f \<times> 'l) set \<Rightarrow> bool" where
  "invar N \<equiv> Inf_from (active_subset N) \<subseteq> Red_Inf_Q N"

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
    then have m_red': "M \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      using m_red unfolding n1 n2 by blast
    have "\<iota> \<in> Red_Inf_\<G>_Q (N1 \<union> N2 - M)"
      using \<iota>_in Red_Inf_of_Red_F_subset[OF m_red'] unfolding n1 n2 by blast
    then show "\<iota> \<in> Red_Inf_\<G>_Q N2"
      using Red_Inf_of_subset[of "N1 \<union> N2 - M" N2] unfolding n1 n2 by auto
  qed
  finally show ?case .
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
        using l_pas
        apply auto
        unfolding to_F_def Inf_from_def no_labels.Inf_from_def using \<iota>_inf
        apply auto
        by (smt Inf_from_def \<iota>_inff active_subset_def imageE image_subset_iff in_mono mem_Collect_eq prod.collapse)
      then have "\<iota> \<in> Red_Inf_\<G>_Q (N \<union> {(C, L)})"
        using inv[unfolded n1 n2] by blast
      then show ?thesis
        by (smt Un_insert_right Un_upper2 image_insert labeled_red_inf_eq_red_inf le_sup_iff
            Red_Inf_of_subset Red_Inf_to_Inf prod.sel(1) subsetD subset_Un_eq)
    qed
  qed
qed

end


section \<open>Lazy Given Clause\<close>

context lazy_given_clause
begin

definition from_F :: "'f inference \<Rightarrow> ('f \<times> 'l) inference set" where
  "from_F \<iota> = {\<iota>' \<in> Inf_FL. to_F \<iota>' = \<iota>}"

fun invar :: "'f inference set \<times> ('f \<times> 'l) set \<Rightarrow> bool" where
  "invar (T, N) \<longleftrightarrow> Inf_from (active_subset N) \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_Q N"

lemma lgc_invar_init:
  assumes
    t: "T = {\<iota>. \<iota> \<in> Inf_F \<and> prems_of \<iota> = []}" and
    n_pas: "active_subset N = {}"
  shows "invar (T, N)"
  unfolding invar.simps n_pas Inf_from_def from_F_def t
  by (auto intro: in_Inf_FL_imp_to_F_in_Inf_F simp: to_F_def)

lemma lgc_invar_step:
  assumes
    invar: "invar (T1, N1)" and
    step: "(T1, N1) \<Longrightarrow>LGC (T2, N2)"
  shows "invar (T2, N2)"
  using step invar
proof induction
  case (process N1 N M N2 M' T)
  note n1 = this(1) and n2 = this(2) and m_red = this(3) and m'_pas = this(4) and inv = this(5)

  have "Inf_from (active_subset N2) \<subseteq> Inf_from (active_subset N1)"
    unfolding n1 n2 Inf_from_def using m'_pas by auto
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N1"
    by (rule inv[unfolded invar.simps])
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2)"
    unfolding n1 n2 by (rule Un_mono[OF order.refl Red_Inf_of_subset]) blast
  also have "... \<subseteq> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N2"
  proof
    fix \<iota>
    assume \<iota>_in: "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2)"
    have "Red_F_\<G>_Q N2 \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      by (simp add: Red_F_of_subset)
    then have m_red': "M \<subseteq> Red_F_\<G>_Q (N1 \<union> N2)"
      using m_red unfolding n1 n2 by blast
    have "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q (N1 \<union> N2 - M)"
      using \<iota>_in Red_Inf_of_Red_F_subset[OF m_red'] unfolding n1 n2 by blast
    then show "\<iota> \<in> \<Union> (from_F ` T) \<union> Red_Inf_\<G>_Q N2"
      using Red_Inf_of_subset[of "N1 \<union> N2 - M" N2] unfolding n1 n2 by auto
  qed
  finally show ?case
    unfolding invar.simps .
next
  case (schedule_infer T2 T1 T' N1 N C L N2)
  note t2 = this(1) and n1 = this(2) and n2 = this(3) and l_pas = this(4) and t' = this(5) and
    inv = this(6)

  have act: "active_subset (N \<union> {(C, L)}) = active_subset N"
    using l_pas by auto

  show ?case
    unfolding invar.simps t2 n1 n2
  proof
    fix \<iota>
    assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)}))"

    note \<iota>_inf = Inf_if_Inf_from[OF \<iota>_inff]

    have "to_F \<iota> \<in> no_labels.Inf_from (fst ` active_subset N \<union> {C})"
      using \<iota>_inff in_Inf_from_imp_to_F_in_Inf_from by fastforce
    then have "to_F \<iota> \<in> T' \<union> no_labels.Inf_from (fst ` active_subset N)"
      unfolding t' no_labels.Inf_from_def no_labels.Inf_from2_def by blast
    then have "\<iota> \<in> \<Union> (from_F ` T') \<union> Inf_from (active_subset (N \<union> {(C, L)}))"
      unfolding t' act from_F_def
      using \<iota>_inf
      apply auto
      using Inf_if_Inf_from \<open>\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)}))\<close> apply blast
      sorry
    then have "\<iota> \<in> \<Union> (from_F ` T') \<union> \<Union> (from_F ` T1) \<union> Red_Inf_\<G>_Q (N \<union> {(C, L)})"
      using inv[unfolded invar.simps t2 n1 n2] by blast
    show "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T')) \<union> Red_Inf_\<G>_Q (N \<union> {(C, active)})"
      sorry
  qed
next
  case (compute_infer T1 T2 \<iota> N2 N1 M)
  show ?case sorry
next
  case (delete_orphans T1 T2 T' N)
  note t1 = this(1) and t'_orph = this(2) and inv = this(3)

  show ?case
    unfolding invar.simps
  proof
    fix \<iota>
    assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset N)"

    have "to_F \<iota> \<notin> T'"
      using t'_orph \<iota>_inff in_Inf_from_imp_to_F_in_Inf_from by blast
    hence "\<iota> \<notin> \<Union> (from_F ` T')"
      unfolding from_F_def by auto
    then show "\<iota> \<in> \<Union> (from_F ` T2) \<union> Red_Inf_\<G>_Q N"
      using \<iota>_inff inv unfolding t1 by auto
  qed
qed

end

end
