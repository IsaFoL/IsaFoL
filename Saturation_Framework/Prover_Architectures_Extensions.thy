(*  Title:       Extensions to the Prover Architectures of the Saturation Framework
 *  Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020 *)

section \<open>Extensions to the Prover Architectures of the Saturation Framework\<close>

theory Prover_Architectures_Extensions
  imports Saturation_Framework.Prover_Architectures
begin

text \<open>The given clause and lazy given clause procedures satisfy a key saturation invariant. This
provides an alternative way to study them.\<close>


section \<open>Given Clause Procedure\<close>

context given_clause
begin

definition invar :: "('f \<times> 'l) set llist \<Rightarrow> enat \<Rightarrow> bool" where
  "invar Ns i \<longleftrightarrow>
   Inf_from (active_subset (Liminf_upto_llist Ns i)) \<subseteq> Sup_upto_llist (lmap Red_Inf_\<G>_Q Ns) i"

lemma invar_infinity:
  assumes
    nnil: "\<not> lnull Ns" and
    invar: "\<forall>i. enat i < llength Ns \<longrightarrow> invar Ns (enat i)"
  shows "invar Ns \<infinity>"
  unfolding invar_def
proof (intro subsetI, unfold Liminf_upto_llist_infinity Sup_upto_llist_infinity)
  fix \<iota>
  assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (Liminf_llist Ns))"

  define As where
    "As = lmap active_subset Ns"

  have act_ns: "active_subset (Liminf_llist Ns) = Liminf_llist As"
    unfolding As_def active_subset_def by (rule Liminf_set_filter_commute[symmetric])

  note \<iota>_inf = Inf_if_Inf_from[OF \<iota>_inff]
  note \<iota>_inff' = \<iota>_inff[unfolded act_ns]

  have "\<not> lnull As"
    unfolding As_def using nnil by auto
  moreover have "set (prems_of \<iota>) \<subseteq> Liminf_llist As"
    using \<iota>_inff'[unfolded Inf_from_def] by simp
  ultimately obtain i where
    i_lt_as: "enat i < llength As" and
    prems_sub_ge_i: "set (prems_of \<iota>) \<subseteq> \<Inter> (lnth As ` {j. i \<le> j \<and> enat j < llength As})"
    using finite_subset_Liminf_llist_imp_exists_index by blast

  note i_lt_ns = i_lt_as[unfolded As_def, simplified]

  have "set (prems_of \<iota>) \<subseteq> lnth As i"
    using prems_sub_ge_i i_lt_as by auto
  then have "\<iota> \<in> Inf_from (active_subset (lnth Ns i))"
    using i_lt_as \<iota>_inf unfolding Inf_from_def As_def by auto
  then have "\<iota> \<in> Sup_upto_llist (lmap Red_Inf_\<G>_Q Ns) (enat i)"
    using nnil i_lt_ns invar[unfolded invar_def] by auto
  then show "\<iota> \<in> Sup_llist (lmap Red_Inf_\<G>_Q Ns)"
    using Sup_upto_llist_subset_Sup_llist by fastforce
qed

lemma gc_invar_init:
  assumes
    "\<not> lnull Ns" and
    "active_subset (lnth Ns 0) = {}"
  shows "invar Ns 0"
  using assms labeled_inf_have_prems unfolding invar_def Inf_from_def by auto

lemma gc_invar_step:
  assumes
    Si_lt: "enat (Suc i) < llength Ns" and
    invar: "invar Ns i" and
    step: "lnth Ns i \<Longrightarrow>GC lnth Ns (Suc i)"
  shows "invar Ns (Suc i)"
  using step Si_lt invar
proof cases
  have i_lt: "enat i < llength Ns"
    using Si_lt Suc_ile_eq order.strict_implies_order by blast
  have lim_i: "Liminf_upto_llist Ns (enat i) = lnth Ns i"
    using i_lt by auto
  have lim_Si: "Liminf_upto_llist Ns (enat (Suc i)) = lnth Ns (Suc i)"
    using Si_lt by auto

  {
    case (process N M M')
    note ni = this(1) and nSi = this(2) and m_red = this(3) and m'_pas = this(4)

    have "Inf_from (active_subset (N \<union> M')) \<subseteq> Inf_from (active_subset (N \<union> M))"
      using m'_pas by (metis active_subset_union boolean_algebra_cancel.sup0 Inf_from_mono
          subset_Un_eq sup_left_idem)
    also have "\<dots> \<subseteq> Sup_upto_llist (lmap Red_Inf_\<G>_Q Ns) (enat i)"
      using invar unfolding invar_def lim_i ni by auto
    also have "\<dots> \<subseteq> Sup_upto_llist (lmap Red_Inf_\<G>_Q Ns) (enat (Suc i))"
      by simp
    finally show ?thesis
      unfolding invar_def lim_Si nSi .
  next
    case (infer N C L M)
    note ni = this(1) and nSi = this(2) and l_pas = this(3) and m_pas = this(4) and
      inff_red = this(5)

    {
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

      have "\<iota> \<in> Sup_upto_llist (lmap Red_Inf_\<G>_Q Ns) (enat (Suc i))"
      proof (cases "to_F \<iota> \<in> no_labels.Inf_from2 (fst ` active_subset N) {C}")
        case True
        then have "to_F \<iota> \<in> no_labels.Red_Inf_\<G>_Q (fst ` (N \<union> {(C, active)} \<union> M))"
          using inff_red by auto
        then have "\<iota> \<in> Red_Inf_\<G>_Q (N \<union> {(C, active)} \<union> M)"
          by (subst labeled_red_inf_eq_red_inf[OF \<iota>_inf])
        then show ?thesis
          using Si_lt using nSi by auto
      next
        case False
        then have "to_F \<iota> \<in> no_labels.Inf_from (fst ` active_subset N)"
          using F\<iota>_inff unfolding no_labels.Inf_from_def no_labels.Inf_from2_def by auto
        then have "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, L)}))"
          using \<iota>_inf l_pas unfolding to_F_def Inf_from_def no_labels.Inf_from_def
          by clarsimp (smt \<iota>_inff[unfolded Inf_from_def] active_subset_def imageE image_subset_iff
              in_mono mem_Collect_eq prod.collapse)
        then show ?thesis
          using invar unfolding invar_def lim_i ni by auto
      qed
    }
    then show ?thesis
      unfolding invar_def lim_Si nSi by blast
  }
qed

lemma gc_invar:
  assumes
    gc: "chain (\<Longrightarrow>GC) Ns" and
    init: "active_subset (lnth Ns 0) = {}" and
    i_lt: "i < llength Ns"
  shows "invar Ns i"
  using i_lt
proof (induct i)
  case (enat i)
  note i_lt = this
  show ?case
    using i_lt
  proof (induct i)
    case 0
    then show ?case
      using gc_invar_init[OF chain_not_lnull[OF gc] init] by (simp add: enat_0)
  next
    case (Suc i)
    note ih = this(1) and Si_lt = this(2)
    have i_lt: "enat i < llength Ns"
      using Si_lt Suc_ile_eq less_le by blast
    show ?case
      by (rule gc_invar_step[OF Si_lt ih[OF i_lt] chain_lnth_rel[OF gc Si_lt]])
  qed
qed simp

lemma gc_fair_new_proof:
  assumes
    gc: "chain (\<Longrightarrow>GC) Ns" and
    init: "active_subset (lnth Ns 0) = {}" and
    lim: "passive_subset (Liminf_llist Ns) = {}"
  shows "fair Ns"
  unfolding fair_def
proof -
  have "Inf_from (Liminf_llist Ns) \<subseteq> Inf_from (active_subset (Liminf_llist Ns))" (is "?lhs \<subseteq> _")
    using lim unfolding active_subset_def passive_subset_def
    by (metis (no_types, lifting) Inf_from_mono empty_Collect_eq mem_Collect_eq subsetI)
  also have "... \<subseteq> Sup_llist (lmap Red_Inf_\<G>_Q Ns)" (is "_ \<subseteq> ?rhs")
    using invar_infinity[OF chain_not_lnull[OF gc]] gc_invar[OF gc init]
    unfolding invar_def by fastforce
  finally show "?lhs \<subseteq> ?rhs"
    .
qed

end


section \<open>Lazy Given Clause\<close>

context lazy_given_clause
begin

definition from_F :: "'f inference \<Rightarrow> ('f \<times> 'l) inference set" where
  "from_F \<iota> = {\<iota>' \<in> Inf_FL. to_F \<iota>' = \<iota>}"

definition invar :: "('f inference set \<times> ('f \<times> 'l) set) llist \<Rightarrow> enat \<Rightarrow> bool" where
  "invar TNs i \<equiv>
   Inf_from (active_subset (Liminf_upto_llist (lmap snd TNs) i))
   \<subseteq> \<Union> (from_F ` Liminf_upto_llist (lmap fst TNs) i)
     \<union> Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) i"

lemma invar_infinity:
  assumes
    nnil: "\<not> lnull TNs" and
    invar: "\<forall>i. enat i < llength TNs \<longrightarrow> invar TNs (enat i)"
  shows "invar TNs \<infinity>"
  unfolding invar_def
proof (intro subsetI, unfold Liminf_upto_llist_infinity Sup_upto_llist_infinity)
  fix \<iota>
  assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (Liminf_llist (lmap snd TNs)))"

  define As where
    "As = lmap (active_subset \<circ> snd) TNs"

  have act_ns: "active_subset (Liminf_llist (lmap snd TNs)) = Liminf_llist As"
    unfolding As_def active_subset_def Liminf_set_filter_commute[symmetric] llist.map_comp ..

  note \<iota>_inf = Inf_if_Inf_from[OF \<iota>_inff]
  note \<iota>_inff' = \<iota>_inff[unfolded act_ns]

  have "\<not> lnull As"
    unfolding As_def using nnil by auto
  moreover have "set (prems_of \<iota>) \<subseteq> Liminf_llist As"
    using \<iota>_inff'[unfolded Inf_from_def] by simp
  ultimately obtain i where
    i_lt_as: "enat i < llength As" and
    prems_sub_ge_i: "set (prems_of \<iota>) \<subseteq> \<Inter> (lnth As ` {j. i \<le> j \<and> enat j < llength As})"
    using finite_subset_Liminf_llist_imp_exists_index by blast

  note i_lt_ns = i_lt_as[unfolded As_def, simplified]

  have ts_nnil: "\<not> lnull (lmap fst TNs)"
    using As_def nnil by simp

  have "set (prems_of \<iota>) \<subseteq> lnth As i"
    using prems_sub_ge_i i_lt_as by auto
  then have "\<iota> \<in> Inf_from (active_subset (lnth (lmap snd TNs) i))"
    using i_lt_as \<iota>_inf unfolding Inf_from_def As_def by auto
  then have "\<iota> \<in> \<Union> (from_F ` Liminf_upto_llist (lmap fst TNs) (enat i))
    \<union> Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) (enat i)"
    using nnil i_lt_ns invar[unfolded invar_def] by auto
  then show "\<iota> \<in> \<Union> (from_F ` Liminf_llist (lmap fst TNs))
    \<union> Sup_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs)"
  proof -
    {
      assume \<iota>_ni_lim: "\<iota> \<notin> \<Union> (from_F ` Liminf_llist (lmap fst TNs))"

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
      then have \<iota>_in_i': "\<iota> \<in> \<Union> (from_F ` fst (lnth TNs i'))
        \<union> Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) (enat i')"
        using i'_lt_as[unfolded As_def] invar[unfolded invar_def] by auto
      then have "\<iota> \<in> Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) (enat i')"
        using \<iota>_ni_i' by auto
      then have "\<iota> \<in> Sup_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs)"
        using Sup_upto_llist_subset_Sup_llist by fastforce
    }
    then show ?thesis
      by blast
  qed
qed

lemma lgc_invar_init:
  assumes
    "\<not> lnull TNs" and
    "active_subset (lnth (lmap snd TNs) 0) = {}" and
    "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> lnth (lmap fst TNs) 0"
  shows "invar TNs 0"
  using assms unfolding invar_def Inf_from_def
  by (simp add: from_F_def) (use in_Inf_FL_imp_to_F_in_Inf_F to_F_def in fastforce)

lemma lgc_invar_step:
  assumes
    Si_lt: "enat (Suc i) < llength TNs" and
    invar: "invar TNs i" and
    step: "lnth TNs i \<Longrightarrow>LGC lnth TNs (Suc i)"
  shows "invar TNs (Suc i)"
  using step Si_lt invar
proof cases
  let ?Sup_Red_i = "Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) (enat i)"
  let ?Sup_Red_Si = "Sup_upto_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs) (enat (Suc i))"

  have i_lt: "enat i < llength TNs"
    using Si_lt Suc_ile_eq order.strict_implies_order by blast

  have lim_i:
    "Liminf_upto_llist (lmap fst TNs) (enat i) = lnth (lmap fst TNs) i"
    "Liminf_upto_llist (lmap snd TNs) (enat i) = lnth (lmap snd TNs) i"
    using i_lt by auto
  have lim_Si:
    "Liminf_upto_llist (lmap fst TNs) (enat (Suc i)) = lnth (lmap fst TNs) (Suc i)"
    "Liminf_upto_llist (lmap snd TNs) (enat (Suc i)) = lnth (lmap snd TNs) (Suc i)"
    using Si_lt by auto

  {
    case (process N1 N M N2 M' T)
    note tni = this(1) and tnSi = this(2) and n1 = this(3) and n2 = this(4) and m_red = this(5) and
      m'_pas = this(6)

    have ni: "lnth (lmap snd TNs) i = N \<union> M"
      by (simp add: i_lt n1 tni)
    have nSi: "lnth (lmap snd TNs) (Suc i) = N \<union> M'"
      by (simp add: Si_lt n2 tnSi)
    have ti: "lnth (lmap fst TNs) i = T"
      by (simp add: i_lt tni)
    have tSi: "lnth (lmap fst TNs) (Suc i) = T"
      by (simp add: Si_lt tnSi)

    have "Inf_from (active_subset (N \<union> M')) \<subseteq> Inf_from (active_subset (N \<union> M))"
      using m'_pas by (metis active_subset_union boolean_algebra_cancel.sup0 Inf_from_mono
          subset_Un_eq sup_left_idem)
    also have "\<dots> \<subseteq> \<Union> (from_F ` T) \<union> ?Sup_Red_i"
      using invar unfolding invar_def lim_i ni ti .
    also have "\<dots> \<subseteq> \<Union> (from_F ` T) \<union> ?Sup_Red_Si"
      using Sup_upto_llist_mono by auto
    finally show ?thesis
      unfolding invar_def lim_Si nSi tSi .
  next
    case (schedule_infer T2 T1 T' N1 N C L N2)
    note tni = this(1) and tnSi = this(2) and t2 = this(3) and n1 = this(4) and n2 = this(5) and
      l_pas = this(6) and t' = this(7)

    have ni: "lnth (lmap snd TNs) i = N \<union> {(C, L)}"
      by (simp add: i_lt n1 tni)
    have nSi: "lnth (lmap snd TNs) (Suc i) = N \<union> {(C, active)}"
      by (simp add: Si_lt n2 tnSi)
    have ti: "lnth (lmap fst TNs) i = T1"
      by (simp add: i_lt tni)
    have tSi: "lnth (lmap fst TNs) (Suc i) = T1 \<union> T'"
      by (simp add: Si_lt t2 tnSi)

    {
      fix \<iota>
      assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset (N \<union> {(C, active)}))"

      have \<iota>_inf: "\<iota> \<in> Inf_FL"
        using \<iota>_inff unfolding Inf_from_def by auto
      then have F\<iota>_inf: "to_F \<iota> \<in> Inf_F"
        using Inf_FL_to_Inf_F[folded to_F_def] by fastforce

      have F\<iota>_inff: "to_F \<iota> \<in> no_labels.Inf_from (fst ` active_subset (N \<union> {(C, active)}))"
        using \<iota>_inff F\<iota>_inf unfolding to_F_def Inf_from_def no_labels.Inf_from_def by auto

      have "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T')) \<union> ?Sup_Red_Si"
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
        then have "\<iota> \<in> \<Union> (from_F ` (T1 \<union> T')) \<union> ?Sup_Red_i"
          using invar[unfolded invar_def] unfolding lim_i ni ti by auto
        then show ?thesis
          using Sup_upto_llist_mono by force
      qed
    }
    then show ?thesis
      unfolding invar_def lim_i lim_Si nSi tSi by fast
  next
    case (compute_infer T1 T2 \<iota> N2 N1 M)
    note tni = this(1) and tnSi = this(2) and t1 = this(3) and n2 = this(4) and m_pas = this(5) and
      \<iota>_red = this(6)

    have ni: "lnth (lmap snd TNs) i = N1"
      by (simp add: i_lt tni)
    have nSi: "lnth (lmap snd TNs) (Suc i) = N1 \<union> M"
      by (simp add: Si_lt n2 tnSi)
    have ti: "lnth (lmap fst TNs) i = T2 \<union> {\<iota>}"
      by (simp add: i_lt t1 tni)
    have tSi: "lnth (lmap fst TNs) (Suc i) = T2"
      by (simp add: Si_lt tnSi)

    {
      fix \<iota>'
      assume \<iota>'_inff: "\<iota>' \<in> Inf_from (active_subset (N1 \<union> M))"

      have \<iota>'_bef: "\<iota>' \<in> \<Union> (from_F ` (T2 \<union> {\<iota>})) \<union> ?Sup_Red_i"
        using \<iota>'_inff invar[unfolded invar_def lim_i ti ni] m_pas by auto
      then have "\<iota>' \<in> \<Union> (from_F ` T2) \<union> ?Sup_Red_Si"
      proof (cases "\<iota>' \<in> \<Union> (from_F ` (T2 \<union> {\<iota>}))")
        case \<iota>'_in_t2_or_\<iota>: True
        then show ?thesis
        proof (cases "\<iota>' \<in> from_F \<iota>")
          case \<iota>'_in_\<iota>: True
          then have "\<iota>' \<in> Red_Inf_\<G>_Q (N1 \<union> M)"
            using \<iota>_red from_F_def labeled_red_inf_eq_red_inf by auto
          then have "\<iota>' \<in> ?Sup_Red_Si"
            using Si_lt by (simp add: n2 tnSi)
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
        then have "\<iota>' \<in> ?Sup_Red_i"
          using \<iota>'_bef by simp
        then have "\<iota>' \<in> ?Sup_Red_Si"
          by auto
        then show ?thesis
          by blast
      qed
    }
    then show ?thesis
      unfolding invar_def lim_Si tSi nSi by blast
  next
    case (delete_orphans T1 T2 T' N)
    note tni = this(1) and tnSi = this(2) and t1 = this(3) and t'_orph = this(4)

    have ni: "lnth (lmap snd TNs) i = N"
      by (simp add: i_lt tni)
    have nSi: "lnth (lmap snd TNs) (Suc i) = N"
      by (simp add: Si_lt tnSi)
    have ti: "lnth (lmap fst TNs) i = T2 \<union> T'"
      by (simp add: i_lt t1 tni)
    have tSi: "lnth (lmap fst TNs) (Suc i) = T2"
      by (simp add: Si_lt tnSi)

    {
      fix \<iota>
      assume \<iota>_inff: "\<iota> \<in> Inf_from (active_subset N)"

      have "to_F \<iota> \<notin> T'"
        using t'_orph \<iota>_inff in_Inf_from_imp_to_F_in_Inf_from by blast
      hence "\<iota> \<notin> \<Union> (from_F ` T')"
        unfolding from_F_def by auto
      then have "\<iota> \<in> \<Union> (from_F ` T2) \<union> ?Sup_Red_Si"
        using \<iota>_inff invar unfolding invar_def lim_i ni ti by auto
    }
    then show ?thesis
      unfolding invar_def lim_Si tSi nSi by blast
  }
qed

lemma lgc_invar:
  assumes
    lgc: "chain (\<Longrightarrow>LGC) TNs" and
    n_init: "active_subset (lnth (lmap snd TNs) 0) = {}" and
    t_init: "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> lnth (lmap fst TNs) 0" and
    i_lt: "i < llength TNs"
  shows "invar TNs i"
  using i_lt
proof (induct i)
  case (enat i)
  note i_lt = this
  show ?case
    using i_lt
  proof (induct i)
    case 0
    then show ?case
      using lgc_invar_init[OF chain_not_lnull[OF lgc] n_init t_init] by (simp add: enat_0)
  next
    case (Suc i)
    note ih = this(1) and Si_lt = this(2)
    have i_lt: "enat i < llength TNs"
      using Si_lt Suc_ile_eq less_le by blast
    show ?case
      by (rule lgc_invar_step[OF Si_lt ih[OF i_lt] chain_lnth_rel[OF lgc Si_lt]])
  qed
qed simp

lemma lgc_fair_new_proof:
  assumes
    lgc: "chain (\<Longrightarrow>LGC) TNs" and
    n_init: "active_subset (lnth (lmap snd TNs) 0) = {}" and
    n_lim: "passive_subset (Liminf_llist (lmap snd TNs)) = {}" and
    t_init: "\<forall>\<iota> \<in> Inf_F. length (prems_of \<iota>) = 0 \<longrightarrow> \<iota> \<in> lnth (lmap fst TNs) 0" and
    t_lim: "Liminf_llist (lmap fst TNs) = {}"
  shows "fair (lmap snd TNs)"
  unfolding fair_def llist.map_comp
proof -
  have "Inf_from (Liminf_llist (lmap snd TNs))
    \<subseteq> Inf_from (active_subset (Liminf_llist (lmap snd TNs)))" (is "?lhs \<subseteq> _")
    using t_lim unfolding active_subset_def passive_subset_def
    by (smt Inf_from_mono empty_Collect_eq mem_Collect_eq n_lim passive_subset_def subsetI)
  also have "... \<subseteq> \<Union> (from_F ` Liminf_upto_llist (lmap fst TNs) \<infinity>)
    \<union> Sup_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs)"
    using invar_infinity[OF chain_not_lnull[OF lgc]] lgc_invar[OF lgc n_init t_init]
    unfolding invar_def by fastforce
  also have "... \<subseteq> Sup_llist (lmap (Red_Inf_\<G>_Q \<circ> snd) TNs)" (is "_ \<subseteq> ?rhs")
    using t_lim by auto
  finally show "?lhs \<subseteq> ?rhs"
    .
qed

end

end
