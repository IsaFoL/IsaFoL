theory ORD_RES_5
  imports
    Background
    Implicit_Exhaustive_Factorization
    Exhaustive_Resolution
begin

section \<open>ORD-RES-5 (explicit model construction)\<close>

type_synonym 'f ord_res_5 = "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
  ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

context simulation_SCLFOL_ground_ordered_resolution begin

inductive ord_res_5 where
  skip: "
    (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>')" |

  production: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<M>' = \<M>(atm_of L := Some C) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')" |

  factoring: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_pos L \<Longrightarrow>
    \<not> linorder_lit.is_greatest_in_mset C L \<Longrightarrow>
    \<F>' = finsert C \<F> \<Longrightarrow>
    \<M>' = (\<lambda>_. None) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r, \<F>', \<M>', \<C>')" |

  resolution: "
    \<not> (dom \<M>) \<TTurnstile> C \<Longrightarrow>
    linorder_lit.is_maximal_in_mset C L \<Longrightarrow>
    is_neg L \<Longrightarrow>
    \<M> (atm_of L) = Some D \<Longrightarrow>
    U\<^sub>e\<^sub>r' = finsert (eres D C) U\<^sub>e\<^sub>r \<Longrightarrow>
    \<M>' = (\<lambda>_. None) \<Longrightarrow>
    \<C>' = The_optional (linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) \<Longrightarrow>
    ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) (U\<^sub>e\<^sub>r', \<F>, \<M>', \<C>')"

inductive ord_res_5_step :: "'f ord_res_5 \<Rightarrow> 'f ord_res_5 \<Rightarrow> bool" where
  "ord_res_5 N s s' \<Longrightarrow> ord_res_5_step (N, s) (N, s')"

lemma tranclp_ord_res_5_step_if_tranclp_ord_res_5:
  "(ord_res_5 N)\<^sup>+\<^sup>+ s s' \<Longrightarrow> ord_res_5_step\<^sup>+\<^sup>+ (N, s) (N, s')"
  by (induction s' rule: tranclp_induct)
   (auto intro: ord_res_5_step.intros tranclp.intros)

inductive ord_res_5_final :: "'f ord_res_5 \<Rightarrow> bool" where
  model_found:
    "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, None)" |

  contradiction_found:
    "ord_res_5_final (N, U\<^sub>e\<^sub>r, \<F>, \<M>, Some {#})"

sublocale ord_res_5_semantics: semantics where
  step = ord_res_5_step and
  final = ord_res_5_final
proof unfold_locales
  fix S5 :: "'f gclause fset \<times>'f gclause fset \<times> 'f gclause fset \<times>
    ('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

  obtain
    N U\<^sub>e\<^sub>r \<F> :: "'f gterm clause fset" and
    \<M> :: "'f gterm \<Rightarrow> 'f gclause option" and
    \<C> :: "'f gclause option" where
    S5_def: "S5 = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>))"
    by (metis prod.exhaust)

  assume "ord_res_5_final S5"
  hence "\<C> = None \<or> \<C> = Some {#}"
    by (simp add: S5_def ord_res_5_final.simps)
  hence "\<nexists>x. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) x"
    by (auto simp: linorder_lit.is_maximal_in_mset_iff elim: ord_res_5.cases)
  thus "finished ord_res_5_step S5"
    by (simp add: S5_def finished_def ord_res_5_step.simps)
qed

lemma right_unique_ord_res_5: "right_unique (ord_res_5 N)"
proof (rule right_uniqueI)
  fix s s' s''
  assume step1: "ord_res_5 N s s'" and step2: "ord_res_5 N s s''"
  show "s' = s''"
    using step1
  proof (cases N s s' rule: ord_res_5.cases)
    case hyps1: (skip \<M>1 C1 \<C>1' \<F>1 U1\<^sub>e\<^sub>r)
    with step2 show ?thesis
      by (cases N s s'' rule: ord_res_5.cases) simp_all
  next
    case hyps1: (production \<M>1 C1 L1 \<M>1' \<C>1' \<F>1 U1\<^sub>e\<^sub>r)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    qed
  next
    case hyps1: (factoring \<M>1 C1 L1 \<F>1 \<F>1' \<M>1' \<C>1' U1\<^sub>e\<^sub>r)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    qed
  next
    case hyps1: (resolution \<M>1 C1 L1 D1 U1\<^sub>e\<^sub>r' U1\<^sub>e\<^sub>r \<M>1' \<C>1' \<F>1)
    show ?thesis
      using step2
    proof (cases N s s'' rule: ord_res_5.cases)
      case (skip \<M>2 C2 \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      with hyps1 show ?thesis
        by simp
    next
      case hyps2: (production \<M>2 C2 L2 \<M>2' \<C>2' \<F>2 U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis linorder_lit.Uniq_is_maximal_in_mset Uniq_D)
      thus ?thesis
        using hyps1 hyps2 by simp
    next
      case hyps2: (factoring \<M>2 C2 L2 \<F>2 \<F>2' \<M>2' \<C>2' U2\<^sub>e\<^sub>r)
      have "C1 = C2"
        using hyps1 hyps2 by simp
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      hence False
        using hyps1 hyps2 by argo
      thus ?thesis ..
    next
      case hyps2: (resolution \<M>2 C2 L2 D2 U2\<^sub>e\<^sub>r' U2\<^sub>e\<^sub>r \<M>2' \<C>2' \<F>2)
      have "U1\<^sub>e\<^sub>r = U2\<^sub>e\<^sub>r" "\<F>1 = \<F>2" "\<M>1 = \<M>2" "C1 = C2"
        using hyps1 hyps2 by simp_all
      hence "L1 = L2"
        using hyps1 hyps2
        by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset)
      hence "D1 = D2"
        using \<open>\<M>1 (atm_of L1) = Some D1\<close> \<open>\<M>2 (atm_of L2) = Some D2\<close> \<open>\<M>1 = \<M>2\<close>
        by simp

      have "U1\<^sub>e\<^sub>r' = U2\<^sub>e\<^sub>r'"
        using \<open>U1\<^sub>e\<^sub>r' = finsert (eres D1 C1) U1\<^sub>e\<^sub>r\<close> \<open>U2\<^sub>e\<^sub>r' = finsert (eres D2 C2) U2\<^sub>e\<^sub>r\<close>
          \<open>D1 = D2\<close> \<open>C1 = C2\<close> \<open>U1\<^sub>e\<^sub>r = U2\<^sub>e\<^sub>r\<close>
        by argo

      moreover have "\<M>1' = \<M>2'"
        using \<open>\<M>1' = (\<lambda>_. None)\<close> \<open>\<M>2' = (\<lambda>_. None)\<close>
        by argo

      moreover have "\<C>1' = \<C>2'"
        using hyps1 hyps2 \<open>\<F>1 = \<F>2\<close> \<open>U1\<^sub>e\<^sub>r' = U2\<^sub>e\<^sub>r'\<close> by simp

      ultimately show ?thesis
        using \<open>s' = (U1\<^sub>e\<^sub>r', \<F>1, \<M>1', \<C>1')\<close> \<open>s'' = (U2\<^sub>e\<^sub>r', \<F>2, \<M>2', \<C>2')\<close>
          \<open>\<F>1 = \<F>2\<close>
        by argo
    qed
  qed
qed

lemma right_unique_ord_res_5_step: "right_unique ord_res_5_step"
proof (rule right_uniqueI)
  fix x y z
  show "ord_res_5_step x y \<Longrightarrow> ord_res_5_step x z \<Longrightarrow> y = z"
    using right_unique_ord_res_5[THEN right_uniqueD]
    by (elim ord_res_5_step.cases) (metis prod.inject)
qed

definition next_clause_in_factorized_clause where
  "next_clause_in_factorized_clause N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow> C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))"

lemma next_clause_in_factorized_clause:
  assumes step: "ord_res_5 N s s'"
  shows "next_clause_in_factorized_clause N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
        linorder_cls.is_minimal_in_fset_ffilter_iff)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_minimal_in_fset_eq_is_least_in_fset
        linorder_cls.is_minimal_in_fset_ffilter_iff)
next
  case (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff)
next
  case (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  thus ?thesis
    unfolding next_clause_in_factorized_clause_def
    by (metis Pair_inject The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff)
qed

definition implicitly_factorized_clauses_subset where
  "implicitly_factorized_clauses_subset N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow> \<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r)"

lemma ord_res_5_preserves_implicitly_factorized_clauses_subset:
  assumes
    step: "ord_res_5 N s s'" and
    invars:
      "implicitly_factorized_clauses_subset N s" and
      "next_clause_in_factorized_clause N s"
  shows "implicitly_factorized_clauses_subset N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (simp add: implicitly_factorized_clauses_subset_def)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (simp add: implicitly_factorized_clauses_subset_def)
next
  case (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars
    by (smt (verit) Pair_inject assms(3) fimage_iff finsert_fsubset iefac_def
        implicitly_factorized_clauses_subset_def literal.collapse(1)
        next_clause_in_factorized_clause_def ex1_efac_eq_factoring_chain ex_ground_factoringI)
next
  case (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  thus ?thesis
    using invars
    by (simp add: fsubset_funion_eq implicitly_factorized_clauses_subset_def)
qed

lemma interp_eq_Interp_if_least_greater:
  assumes
    C_in: "C |\<in>| NN" and
    D_least_gt_C: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) NN) D"
  shows "ord_res.interp (fset NN) D = ord_res.interp (fset NN) C \<union> ord_res.production (fset NN) C"
proof -
  have nex_between_C_and_D: "\<not> (\<exists>CD |\<in>| NN. C \<prec>\<^sub>c CD \<and> CD \<prec>\<^sub>c D)"
    using D_least_gt_C
    unfolding linorder_cls.is_least_in_ffilter_iff by auto

  have "ord_res.interp (fset NN) D = ord_res.interp (fset {|B |\<in>| NN. B \<preceq>\<^sub>c C|}) D"
  proof (rule ord_res.interp_swap_clause_set)
    have "NN = {|B |\<in>| NN. B \<preceq>\<^sub>c C|} |\<union>| {|E |\<in>| NN. D \<preceq>\<^sub>c E|}"
      using nex_between_C_and_D by force
    show "{Da. Da |\<in>| NN \<and> Da \<prec>\<^sub>c D} = {Da. Da |\<in>| {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} \<and> Da \<prec>\<^sub>c D}"
      using \<open>NN = {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} |\<union>| ffilter ((\<prec>\<^sub>c)\<^sup>=\<^sup>= D) NN\<close> linorder_cls.leD by auto
  qed

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da. Da |\<in>| {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|} \<and> Da \<prec>\<^sub>c D})"
    unfolding ord_res.interp_def ..

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C \<and> Da \<prec>\<^sub>c D})"
    by auto

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C})"
  proof -
    have "{|Da |\<in>| NN. Da \<preceq>\<^sub>c C \<and> Da \<prec>\<^sub>c D|} = {|Da |\<in>| NN. Da \<preceq>\<^sub>c C|}"
      using nex_between_C_and_D
      by (metis (no_types, opaque_lifting) D_least_gt_C linorder_cls.is_least_in_fset_ffilterD(2)
          linorder_cls.le_less_trans)
    thus ?thesis
      by fastforce
  qed

  also have "\<dots> = \<Union> (ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) `
    {Da \<in> fset NN. Da \<prec>\<^sub>c C}) \<union> ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C"
  proof -
    have "{Da. Da |\<in>| NN \<and> (\<prec>\<^sub>c)\<^sup>=\<^sup>= Da C} = insert C {Da. Da |\<in>| NN \<and> Da \<prec>\<^sub>c C}"
      using C_in by auto
    thus ?thesis
      by blast
  qed

  also have "\<dots> = ord_res_Interp (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C"
    unfolding ord_res.interp_def by auto

  also have "\<dots> = ord_res_Interp (fset NN) C"
  proof -
    have "ord_res.interp (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C = ord_res.interp (fset NN) C"
      using ord_res.interp_swap_clause_set[of "fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}" C "fset NN"]
      by auto

    moreover have "ord_res.production (fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}) C = ord_res.production (fset NN) C"
      using ord_res.production_swap_clause_set[of "fset {|B |\<in>| NN. (\<prec>\<^sub>c)\<^sup>=\<^sup>= B C|}" C "fset NN"]
      by auto

    ultimately show ?thesis
      by simp
  qed

  finally show ?thesis .
qed

lemma interp_eq_empty_if_least_in_set:
  assumes "linorder_cls.is_least_in_set N C"
  shows "ord_res.interp N C = {}"
  using assms
  unfolding ord_res.interp_def
  unfolding linorder_cls.is_least_in_set_iff
  by auto

definition model_eq_interp_upto_next_clause where
  "model_eq_interp_upto_next_clause N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow>
      dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C)"

lemma model_eq_interp_upto_next_clause:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "model_eq_interp_upto_next_clause N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case step_hyps: (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)

  have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
      using invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .

    also have "\<dots> = ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    proof -
      have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
        using \<open>dom \<M> \<TTurnstile> C\<close>
        unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>]
        by (simp add: ord_res.production_unfold)
      thus ?thesis
        by simp
    qed

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_Interp_if_least_greater[symmetric])
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
    next
      show "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that by (metis Some_eq_The_optionalD)
    qed

    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = dom \<M> \<union> {atm_of L}"
      unfolding \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close> by simp

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<union> {atm_of L}"
      unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] ..

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<union>
      ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    proof -
      have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
        unfolding invars(1)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
      hence "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using \<open>is_pos L\<close> \<open>ord_res.is_strictly_maximal_lit L C\<close>
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>]
        unfolding ord_res.production_unfold mem_Collect_eq
        by (metis linorder_lit.is_greatest_in_mset_iff literal.collapse(1) multi_member_split)
      hence "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {atm_of L}"
        by (metis empty_iff insertE ord_res.production_eq_empty_or_singleton)
      thus ?thesis
        by argo
    qed

    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_Interp_if_least_greater[symmetric])
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars(2)[unfolded next_clause_in_factorized_clause_def, rule_format,
            OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
    next
      show "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that by (metis Some_eq_The_optionalD)
    qed

    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = {}"
      using step_hyps(3-) by simp
    also have "\<dots> = ord_res.interp (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    proof (rule interp_eq_empty_if_least_in_set[symmetric])
      show "linorder_cls.is_least_in_set (fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using step_hyps(3-) that
        by (metis Some_eq_The_optionalD linorder_cls.is_least_in_fset_iff
            linorder_cls.is_least_in_set_iff)
    qed
    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)

  have "dom \<M>' = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D" if "\<C>' = Some D" for D
  proof -
    have "dom \<M>' = {}"
      using step_hyps(3-) by simp
    also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
    proof (rule interp_eq_empty_if_least_in_set[symmetric])
      show "linorder_cls.is_least_in_set (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'))) D"
        using step_hyps(3-) that
        by (metis Some_eq_The_optionalD linorder_cls.is_least_in_fset_iff
            linorder_cls.is_least_in_set_iff)
    qed
    finally show ?thesis .
  qed

  thus ?thesis
    using step_hyps by (simp add: model_eq_interp_upto_next_clause_def)
qed

definition all_smaller_clauses_true_wrt_respective_Interp where
  "all_smaller_clauses_true_wrt_respective_Interp N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow>
      (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C))"

lemma all_smaller_clauses_true_wrt_respective_Interp:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "all_smaller_clauses_true_wrt_respective_Interp N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case step_hyps: (skip \<M> D \<C>' \<F> U\<^sub>e\<^sub>r)

  have D_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using invars(2) ord_res.production_unfold step_hyps(1) step_hyps(3)
    by (auto simp: model_eq_interp_upto_next_clause_def)

  have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = Some E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c E" for C E
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)
    hence "C \<preceq>\<^sub>c D"
      using C_in \<open>C \<prec>\<^sub>c E\<close>
      by (metis asympD linorder_cls.is_least_in_ffilter_iff linorder_cls.le_less_linear
          ord_res.asymp_less_cls)
    thus ?thesis
      using D_true
      using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in] by auto
  qed

  moreover have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = None" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis (no_types, opaque_lifting) None_eq_The_optionalD linorder_cls.Uniq_is_least_in_fset
          the1_equality')
    hence "\<not> (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c x)"
      by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      using C_in by force
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      then show ?thesis
        using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in
        by (auto simp: all_smaller_clauses_true_wrt_respective_Interp_def)
    next
      assume "C = D"
      then show ?thesis
        using D_true by argo
    qed
  qed

  ultimately show ?thesis
    using step_hyps
    by (smt (verit, best) all_smaller_clauses_true_wrt_respective_Interp_def old.prod.inject option.exhaust)
next
  case step_hyps: (production \<M> D K \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)

  have "K \<in># D"
    using step_hyps(3-) by (metis linorder_lit.is_greatest_in_mset_iff)

  have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using \<open>\<not> dom \<M> \<TTurnstile> D\<close>
    unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>] .
  hence "atm_of K \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using \<open>is_pos K\<close> \<open>ord_res.is_strictly_maximal_lit K D\<close> \<open>K \<in># D\<close>
    using invars(3)[unfolded next_clause_in_factorized_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>]
    unfolding ord_res.production_unfold mem_Collect_eq
    by (metis literal.collapse(1) multi_member_split)
  hence prod_D_eq: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {atm_of K}"
    by (metis empty_iff insertE ord_res.production_eq_empty_or_singleton)
  hence "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile>l K"
    using \<open>is_pos K\<close> by force
  hence D_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
    using \<open>K \<in># D\<close> by auto

  have "dom \<M>' = dom \<M> \<union> {atm_of K}"
    unfolding \<open>\<M>' = \<M>(atm_of K \<mapsto> D)\<close> by simp

  also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<union> {atm_of K}"
    unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
        OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>] ..

  also have "\<dots> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<union>
      ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using prod_D_eq by argo

  finally have dom_\<M>'_eq: "dom \<M>' = ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D" .

  have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = Some E" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "C \<prec>\<^sub>c E" for C E
  proof -
    have "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E"
      using step_hyps \<open>\<C>' = Some E\<close> by (metis Some_eq_The_optionalD)
    hence "C \<preceq>\<^sub>c D"
      using C_in \<open>C \<prec>\<^sub>c E\<close>
      by (metis asympD linorder_cls.is_least_in_ffilter_iff linorder_cls.le_less_linear
          ord_res.asymp_less_cls)
    thus ?thesis
      using D_true
      using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in] by auto
  qed

  moreover have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    if "\<C>' = None" and C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" for C
  proof -
    have "\<nexists>x. linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) D) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) x"
      using step_hyps \<open>\<C>' = None\<close>
      by (metis (no_types, opaque_lifting) None_eq_The_optionalD linorder_cls.Uniq_is_least_in_fset
          the1_equality')
    hence "\<not> (\<exists>x |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<prec>\<^sub>c x)"
      by (metis femptyE ffmember_filter linorder_cls.ex1_least_in_fset)
    hence "C \<prec>\<^sub>c D \<or> C = D"
      using C_in by force
    thus ?thesis
    proof (elim disjE)
      assume "C \<prec>\<^sub>c D"
      then show ?thesis
        using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close> C_in
        by (auto simp: all_smaller_clauses_true_wrt_respective_Interp_def)
    next
      assume "C = D"
      thus ?thesis
        using D_true by argo
    qed
  qed

  ultimately show ?thesis
    unfolding step_hyps(2) all_smaller_clauses_true_wrt_respective_Interp_def
    by (metis prod.inject option.exhaust)
next
  case step_hyps: (factoring \<M> D K \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  have "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using invars(2-) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)\<close>
    by (metis next_clause_in_factorized_clause_def)
  hence "D |\<in>| N |\<union>| U\<^sub>e\<^sub>r"
    using step_hyps(3-)
    by (smt (verit, ccfv_threshold) fimage_iff iefac_def literal.collapse(1)
        ex1_efac_eq_factoring_chain ex_ground_factoringI)
  hence "iefac \<F>' D |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    unfolding \<open>\<F>' = finsert D \<F>\<close> by simp
  hence "\<C>' \<noteq> None"
    using step_hyps(3-)
    by (metis The_optional_eq_NoneD finsert_not_fempty linorder_cls.ex1_least_in_fset set_finsert)
  then obtain E where
    "\<C>' = Some E"
    by auto

  have "\<not> (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c E)"
    using \<open>\<C>' = Some E\<close> step_hyps(9)
    by (metis The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_not_less)

  thus ?thesis
    unfolding step_hyps(1,2) all_smaller_clauses_true_wrt_respective_Interp_def
    using \<open>\<C>' = Some E\<close> by simp
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  hence "eres D C |\<in>| N |\<union>| U\<^sub>e\<^sub>r'"
    by simp
  hence "iefac \<F> (eres D C) |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')"
    by simp
  hence "\<C>' \<noteq> None"
    using step_hyps(3-)
    by (metis The_optional_eq_NoneD finsert_not_fempty linorder_cls.ex1_least_in_fset set_finsert)
  then obtain E where
    "\<C>' = Some E"
    by auto

  have "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c E)"
    using \<open>\<C>' = Some E\<close> step_hyps(9)
    by (metis The_optional_eq_SomeD linorder_cls.is_least_in_fset_iff
        linorder_cls.less_imp_not_less)

  thus ?thesis
    unfolding step_hyps(1,2) all_smaller_clauses_true_wrt_respective_Interp_def
    using \<open>\<C>' = Some E\<close> by simp
qed

lemma all_smaller_clauses_true_wrt_model:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> D. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow> dom \<M> \<TTurnstile> C)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> D C
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D)" and
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_lt: "C \<prec>\<^sub>c D"

  hence C_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    using invars(1)[unfolded all_smaller_clauses_true_wrt_respective_Interp_def s_def]
    by auto

  moreover have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
    using invars(2) s_def by (metis model_eq_interp_upto_next_clause_def)

  ultimately show "dom \<M> \<TTurnstile> C"
    using ord_res.entailed_clause_stays_entailed' C_lt by metis
qed

definition model_eq_sublocale where
  "model_eq_sublocale N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, None) \<longrightarrow>
      (let NN = fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) in dom \<M> = \<Union> (ord_res.production NN ` NN)))"

lemma all_smaller_clauses_true_wrt_model_strong:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
      "model_eq_sublocale N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow>
    (\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). (\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D) \<longrightarrow> dom \<M> \<TTurnstile> C)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> \<C> C
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and
    C_in: "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
    C_lt: "\<forall>D. \<C> = Some D \<longrightarrow> C \<prec>\<^sub>c D"
  hence C_true: "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
    using invars(1) by (metis all_smaller_clauses_true_wrt_respective_Interp_def)

  show "dom \<M> \<TTurnstile> C"
  proof (cases \<C>)
    case \<C>_def: None
    have "let NN = fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) in dom \<M> = \<Union> (ord_res.production NN ` NN)"
      using invars(3) s_def \<C>_def
      by (metis model_eq_sublocale_def)
    then show ?thesis
      using C_true
      by (smt (verit, ccfv_SIG) C_in UN_I insertCI linorder_lit.is_greatest_in_mset_iff
          ord_res.lift_entailment_to_Union ord_res.mem_productionE
          ord_res.production_eq_empty_or_singleton pos_literal_in_imp_true_cls
          sup_bot.right_neutral)
  next
    case \<C>_def: (Some D)
    have "C \<prec>\<^sub>c D"
      using C_lt \<C>_def by metis
    moreover have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
      using invars(2) s_def \<C>_def by (metis model_eq_interp_upto_next_clause_def)
    ultimately show ?thesis
      using ord_res.entailed_clause_stays_entailed' C_true by metis
  qed
qed

lemma next_clause_lt_least_false_clause:
  assumes
    invars:
      "all_smaller_clauses_true_wrt_respective_Interp N s"
      "model_eq_interp_upto_next_clause N s"
  shows "\<forall>U\<^sub>e\<^sub>r \<F> \<M> C. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) \<longrightarrow>
    (\<forall>D. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D \<longrightarrow> C \<preceq>\<^sub>c D)"
proof (intro allI impI ballI)
  fix U\<^sub>e\<^sub>r \<F> \<M> C D
  assume
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" and
    D_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
  then show "C \<preceq>\<^sub>c D"
    using invars[unfolded model_eq_interp_upto_next_clause_def
        all_smaller_clauses_true_wrt_respective_Interp_def, rule_format, OF s_def, simplified]
    by (metis (no_types, lifting) fimage.rep_eq is_least_false_clause_def
        linorder_cls.is_least_in_fset_ffilterD(1) linorder_cls.is_least_in_fset_ffilterD(2)
        linorder_cls.le_less_linear sup_fset.rep_eq)
qed

definition atoms_in_model_were_produced where
  "atoms_in_model_were_produced N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> \<C>. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) \<longrightarrow> (\<forall>A C. \<M> A = Some C \<longrightarrow>
      A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C))"

lemma atoms_in_model_were_produced:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "atoms_in_model_were_produced N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "atoms_in_model_were_produced N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  thus ?thesis
    using invars(1) by (simp add: atoms_in_model_were_produced_def)
next
  case (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  obtain A where "L = Pos A"
    using \<open>is_pos L\<close> by (cases L) simp_all

  have "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    unfolding ord_res.production_unfold mem_Collect_eq
  proof (intro exI conjI)
    show "atm_of L = A"
      unfolding \<open>L = Pos A\<close> literal.sel ..
  next
    show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars(3)[unfolded next_clause_in_factorized_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
  next
    have "L \<in># C"
      using \<open>linorder_lit.is_maximal_in_mset C L\<close>
      unfolding linorder_lit.is_maximal_in_mset_iff ..
    thus "C = add_mset (Pos A) (C - {#Pos A#})"
      unfolding \<open>L = Pos A\<close> by simp
  next
    show "ord_res.is_strictly_maximal_lit (Pos A) C"
      using \<open>ord_res.is_strictly_maximal_lit L C\<close>
      unfolding \<open>L = Pos A\<close> .
  next
    show "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
      using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
      unfolding invars(2)[unfolded model_eq_interp_upto_next_clause_def, rule_format,
          OF \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>] .
  qed simp_all

  thus ?thesis
    using invars(1)
    by (simp add: atoms_in_model_were_produced_def
        \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close> \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close>)
qed (simp_all add: atoms_in_model_were_produced_def)

definition all_produced_atoms_in_model where
  "all_produced_atoms_in_model N s \<longleftrightarrow>
    (\<forall>U\<^sub>e\<^sub>r \<F> \<M> D. s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some D) \<longrightarrow> (\<forall>C A. C \<prec>\<^sub>c D \<longrightarrow>
      A \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<longrightarrow> \<M> A = Some C))"

lemma all_produced_atoms_in_model:
  assumes step: "ord_res_5 N s s'" and
    invars:
      "all_produced_atoms_in_model N s"
      "model_eq_interp_upto_next_clause N s"
      "next_clause_in_factorized_clause N s"
  shows "all_produced_atoms_in_model N s'"
  using step
proof (cases N s s' rule: ord_res_5.cases)
  case (skip \<M> C \<C>' \<F> U\<^sub>e\<^sub>r)
  have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
    using invars
    by (metis ex_in_conv model_eq_interp_upto_next_clause_def local.skip(1) local.skip(3)
        ord_res.mem_productionE)
  thus ?thesis
    using invars(1) \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>
    unfolding all_produced_atoms_in_model_def
    by (smt (verit, del_insts) Pair_inject The_optional_eq_SomeD empty_iff
        linorder_cls.is_least_in_ffilter_iff linorder_cls.not_less_iff_gr_or_eq local.skip(2)
        local.skip(4) ord_res.mem_productionE)
next
  case step_hyps: (production \<M> C L \<M>' \<C>' \<F> U\<^sub>e\<^sub>r)
  obtain A where "L = Pos A"
    using \<open>is_pos L\<close> by (cases L) simp_all

  have "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
    unfolding ord_res.production_unfold mem_Collect_eq
  proof (intro exI conjI)
    show "atm_of L = A"
      unfolding \<open>L = Pos A\<close> literal.sel ..
  next
    show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
      using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> by (metis next_clause_in_factorized_clause_def)
  next
    have "L \<in># C"
      using \<open>linorder_lit.is_maximal_in_mset C L\<close>
      unfolding linorder_lit.is_maximal_in_mset_iff ..
    thus "C = add_mset (Pos A) (C - {#Pos A#})"
      unfolding \<open>L = Pos A\<close> by simp
  next
    show "ord_res.is_strictly_maximal_lit (Pos A) C"
      using \<open>ord_res.is_strictly_maximal_lit L C\<close>
      unfolding \<open>L = Pos A\<close> .
  next
    show "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
      using \<open>\<not> dom \<M> \<TTurnstile> C\<close>
      using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close> by (metis model_eq_interp_upto_next_clause_def)
  qed simp_all

  thus ?thesis
    using invars \<open>s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)\<close>
    unfolding all_produced_atoms_in_model_def
    using \<open>s' = (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')\<close> \<open>\<M>' = \<M>(atm_of L \<mapsto> C)\<close>
    using prod.inject
    by (smt (verit, del_insts) Some_eq_The_optionalD asympD ord_res.mem_productionE
        linorder_cls.antisym_conv3 linorder_cls.is_least_in_ffilter_iff
        linorder_trm.not_less_iff_gr_or_eq step_hyps(8) map_upd_Some_unfold
        ord_res.asymp_less_cls ord_res.less_trm_iff_less_cls_if_mem_production)
next
  case step_hyps: (factoring \<M> C L \<F>' \<F> \<M>' \<C>' U\<^sub>e\<^sub>r)
  have "\<not> (\<exists>C |\<in>| iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D)" if "\<C>' = Some D" for D
  proof (rule nbex_less_than_least_in_fset)
    show "linorder_cls.is_least_in_fset (iefac \<F>' |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      using step_hyps that by (metis The_optional_eq_SomeD)
  qed
  thus ?thesis
    unfolding all_produced_atoms_in_model_def
    by (metis step_hyps(2) ord_res.mem_productionE prod.inject)
next
  case step_hyps: (resolution \<M> C L D U\<^sub>e\<^sub>r' U\<^sub>e\<^sub>r \<M>' \<C>' \<F>)
  have "\<not> (\<exists>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r'). C \<prec>\<^sub>c D)" if "\<C>' = Some D" for D
  proof (rule nbex_less_than_least_in_fset)
    show "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r')) D"
      using step_hyps that by (metis The_optional_eq_SomeD)
  qed
  thus ?thesis
    unfolding all_produced_atoms_in_model_def
    by (metis step_hyps(2) ord_res.mem_productionE prod.inject)
qed


definition ord_res_5_invars where
  "ord_res_5_invars N s \<longleftrightarrow>
    next_clause_in_factorized_clause N s \<and>
    implicitly_factorized_clauses_subset N s \<and>
    model_eq_interp_upto_next_clause N s \<and>
    all_smaller_clauses_true_wrt_respective_Interp N s \<and>
    atoms_in_model_were_produced N s \<and>
    all_produced_atoms_in_model N s"

lemma ord_res_5_invars_initial_state:
  assumes
    \<F>_subset: "\<F> |\<subseteq>| N |\<union>| U\<^sub>e\<^sub>r" and
    C_least: "linorder_cls.is_least_in_fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
  shows "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, Map.empty, Some C)"
  unfolding ord_res_5_invars_def
proof (intro conjI)
  show "next_clause_in_factorized_clause N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding next_clause_in_factorized_clause_def
    using C_least[unfolded linorder_cls.is_least_in_fset_iff] by simp
next
  show "implicitly_factorized_clauses_subset N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding implicitly_factorized_clauses_subset_def
    using \<F>_subset by simp
next
  have "ord_res.interp (iefac \<F> ` (fset N \<union> fset U\<^sub>e\<^sub>r)) C = {}"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (simp add: interp_eq_empty_if_least_in_set linorder_cls.is_least_in_set_iff)
  thus "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding model_eq_interp_upto_next_clause_def by simp
next
  have "\<not>(\<exists>Ca |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). Ca \<prec>\<^sub>c C)"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (metis linorder_cls.less_asym)
  thus "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding all_smaller_clauses_true_wrt_respective_Interp_def by simp
next
  show "atoms_in_model_were_produced N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding atoms_in_model_were_produced_def by simp
next
  have "\<forall>Ca. Ca \<prec>\<^sub>c C \<longrightarrow> Ca |\<notin>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using C_least[unfolded linorder_cls.is_least_in_fset_iff]
    by (metis linorder_cls.order.asym)
  thus "all_produced_atoms_in_model N (U\<^sub>e\<^sub>r, \<F>, \<lambda>x. None, Some C)"
    unfolding all_produced_atoms_in_model_def
    by (simp add: ord_res.production_unfold)
qed

lemma ord_res_5_preserves_invars:
  assumes step: "ord_res_5 N s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
proof -
  obtain U\<^sub>e\<^sub>r \<F> \<M> \<C> where s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
    by (metis prod.exhaust)

  then show ?thesis
    unfolding ord_res_5_invars_def
    using invars[unfolded ord_res_5_invars_def]
    using next_clause_in_factorized_clause[OF step]
      ord_res_5_preserves_implicitly_factorized_clauses_subset[OF step]
      model_eq_interp_upto_next_clause[OF step]
      all_smaller_clauses_true_wrt_respective_Interp[OF step]
      atoms_in_model_were_produced[OF step]
      all_produced_atoms_in_model[OF step]
    by metis
qed

lemma rtranclp_ord_res_5_preserves_invars:
  assumes steps: "(ord_res_5 N)\<^sup>*\<^sup>* s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using steps invars
  by (induction s rule: converse_rtranclp_induct) (auto intro: ord_res_5_preserves_invars)

lemma tranclp_ord_res_5_preserves_invars:
  assumes steps: "(ord_res_5 N)\<^sup>+\<^sup>+ s s'" and invars: "ord_res_5_invars N s"
  shows "ord_res_5_invars N s'"
  using rtranclp_ord_res_5_preserves_invars
  by (metis invars steps tranclp_into_rtranclp)

lemma le_least_false_clause:
  fixes N s U\<^sub>e\<^sub>r \<F> \<M> C D
  assumes
    invars: "ord_res_5_invars N s" and
    s_def: "s = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" and
    D_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
  shows "C \<preceq>\<^sub>c D"
proof -
  have D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
    using D_least_false
    unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    by argo

  show "C \<preceq>\<^sub>c D"
  proof (rule next_clause_lt_least_false_clause[rule_format])
    show "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      using D_least_false .
  next
    show "(U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) = (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)" ..
  next
    show "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
      using invars by (metis s_def ord_res_5_invars_def)
  next
    show "model_eq_interp_upto_next_clause N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
      using invars by (metis s_def ord_res_5_invars_def)
  qed
qed

lemma ex_ord_res_5_if_not_final:
  assumes
    not_final: "\<not> ord_res_5_final S" and
    invars: "\<forall>N s. S = (N, s) \<longrightarrow> ord_res_5_invars N s"
  shows "\<exists>S'. ord_res_5_step S S'"
proof -
  from not_final obtain N U\<^sub>e\<^sub>r \<F> \<M> C where
    S_def: "S = (N, (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C))" and "C \<noteq> {#}"
    unfolding ord_res_5_final.simps de_Morgan_disj not_ex
    by (metis option.exhaust surj_pair)

  note invars' = invars[unfolded ord_res_5_invars_def, rule_format, OF S_def]

  have "\<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s'"
  proof (cases "dom \<M> \<TTurnstile> C")
    case True
    thus ?thesis
      using ord_res_5.skip by metis
  next
    case C_false: False
    obtain L where L_max: "linorder_lit.is_maximal_in_mset C L"
      using linorder_lit.ex_maximal_in_mset[OF \<open>C \<noteq> {#}\<close>] ..

    show ?thesis
    proof (cases L)
      case (Pos A)
      hence L_pos: "is_pos L"
        by simp
      show ?thesis
      proof (cases "ord_res.is_strictly_maximal_lit L C")
        case True
        then show ?thesis
          using ord_res_5.production[OF C_false L_max L_pos] by metis
      next
        case L_not_striclty_max: False
        thus ?thesis
          using ord_res_5.factoring[OF C_false L_max L_pos L_not_striclty_max _ refl refl] by metis
      qed
    next
      case (Neg A)
      hence L_neg: "is_neg L"
        by simp

      have C_least_false: "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
      proof (intro conjI ballI impI)
        show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          using invars' by (metis next_clause_in_factorized_clause_def)
      next
        have "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
          using invars' C_false by (metis model_eq_interp_upto_next_clause_def)
        moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
        proof -
          have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
            using L_max L_neg
            by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
                linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
          thus ?thesis
            using unproductive_if_nex_strictly_maximal_pos_lit by metis
        qed
        ultimately show "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
          by simp
      next
        fix D
        assume D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and "D \<noteq> C" and
          C_false: "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
        have "\<not> D \<prec>\<^sub>c C"
          using C_false
          using invars' D_in
          unfolding all_smaller_clauses_true_wrt_respective_Interp_def
          by auto
        thus "C \<prec>\<^sub>c D"
          using \<open>D \<noteq> C\<close> by order
      qed
      then obtain D where "D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "D \<prec>\<^sub>c C" and
        "ord_res.is_strictly_maximal_lit (Pos A) D" and
        D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {A}"
        using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
          L_max[unfolded Neg] by metis

      have "\<M> (atm_of L) = Some D"
        using invars'
        by (metis Neg \<open>D \<prec>\<^sub>c C\<close> all_produced_atoms_in_model_def D_prod insertI1 literal.sel(2))

      then show ?thesis
        using ord_res_5.resolution[OF C_false L_max L_neg] by metis
    qed
  qed
  thus ?thesis
    using S_def ord_res_5_step.simps by metis
qed

lemma ord_res_5_safe_state_if_invars:
  fixes N s
  assumes invars: "ord_res_5_invars N s"
  shows "safe_state ord_res_5_step ord_res_5_final (N, s)"
proof -
  {
    fix S'
    assume "ord_res_5_semantics.eval (N, s) S'" and stuck: "stuck_state ord_res_5_step S'"
    then obtain s' where "S' = (N, s')" and "(ord_res_5 N)\<^sup>*\<^sup>* s s'"
    proof (induction "(N, s)" arbitrary: N s rule: converse_rtranclp_induct)
      case base
      thus ?case by simp
    next
      case (step z)
      thus ?case
        by (smt (verit, ccfv_SIG) converse_rtranclp_into_rtranclp ord_res_5_step.cases prod.inject)
    qed
    hence "ord_res_5_invars N s'"
      using invars rtranclp_ord_res_5_preserves_invars by metis
    hence "\<not> ord_res_5_final S' \<Longrightarrow> \<exists>S''. ord_res_5_step S' S''"
      using ex_ord_res_5_if_not_final[of S'] \<open>S' = (N, s')\<close> by blast
    hence "ord_res_5_final S'"
      using stuck[unfolded stuck_state_def] by argo
  }
  thus ?thesis
    unfolding safe_state_def stuck_state_def by metis
qed

lemma MAGIC1:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
  shows "\<exists>\<M>' \<C>'. (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') \<and>
    (\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>''))"
proof -
  define R where
    "R = (\<lambda>(\<M>, \<C>) (\<M>', \<C>'). ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>'))"

  define f :: "('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option \<Rightarrow> 'f gclause fset" where
    "f = (\<lambda>(\<M>, \<C>). case \<C> of None \<Rightarrow> {||} | Some C \<Rightarrow> finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|})"

  have "Wellfounded.wfp_on {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'} R\<inverse>\<inverse>"
  proof (rule wfp_on_if_convertible_to_wfp_on)
    have "wfp (|\<subset>|)"
      by auto
    thus "Wellfounded.wfp_on (f ` {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}) (|\<subset>|)"
      using Wellfounded.wfp_on_subset subset_UNIV by metis
  next
    fix x y :: "('f gterm \<Rightarrow> 'f gclause option) \<times> 'f gclause option"

    obtain \<M>\<^sub>x \<C>\<^sub>x where x_def: "x = (\<M>\<^sub>x, \<C>\<^sub>x)"
      by force

    obtain \<M>\<^sub>y \<C>\<^sub>y where y_def: "y = (\<M>\<^sub>y, \<C>\<^sub>y)"
      by force

    have rtranclp_with_constsD: "(\<lambda>(y, z) (y', z'). R (x, y, z) (x, y', z'))\<^sup>*\<^sup>* (y, z) (y', z') \<Longrightarrow>
      R\<^sup>*\<^sup>* (x, y, z) (x, y', z')" for R x y z y' z'
    proof (induction "(y, z)" arbitrary: y z rule: converse_rtranclp_induct)
      case base
      show ?case
        by simp
    next
      case (step w)
      thus ?case
        by force
    qed 

    assume "x \<in> {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}" and  "y \<in> {x'. R\<^sup>*\<^sup>* (\<M>, \<C>) x'}"
    hence
      "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" and
      "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      unfolding atomize_conj mem_Collect_eq R_def x_def y_def
      by (auto intro: rtranclp_with_constsD)
    hence
      x_invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" and
      y_invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      using invars by (metis rtranclp_ord_res_5_preserves_invars)+

    assume "R\<inverse>\<inverse> y x"
    hence "ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x) (U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)"
      unfolding conversep_iff R_def x_def y_def prod.case .
    thus "f y |\<subset>| f x"
    proof (cases N "(U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>x, \<C>\<^sub>x)" "(U\<^sub>e\<^sub>r, \<F>, \<M>\<^sub>y, \<C>\<^sub>y)")
      case step_hyps: (skip C)

      have "f y |\<subseteq>| {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}"
      proof (cases \<C>\<^sub>y)
        case None
        thus ?thesis
          unfolding f_def y_def prod.case by simp
      next
        case \<C>\<^sub>y_def: (Some D)

        have D_least: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using step_hyps \<C>\<^sub>y_def by (metis The_optional_eq_SomeD)
        hence f_y_eq: "f y = {|E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<preceq>\<^sub>c E|}"
          unfolding f_def y_def prod.case \<C>\<^sub>y_def option.case linorder_cls.is_least_in_ffilter_iff
          by auto

        show ?thesis
          unfolding f_y_eq subset_ffilter
          using D_least
          unfolding linorder_cls.is_least_in_ffilter_iff
          by auto
      qed

      also have "\<dots> |\<subset>| finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|}"
        by auto

      also have "\<dots> = f x"
        unfolding f_def x_def y_def prod.case step_hyps option.case by metis

      finally show ?thesis .
    next
      case step_hyps: (production C L)

      have "f y |\<subseteq>| {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D|}"
      proof (cases \<C>\<^sub>y)
        case None
        thus ?thesis
          unfolding f_def y_def prod.case by simp
      next
        case \<C>\<^sub>y_def: (Some D)

        have D_least: "linorder_cls.is_least_in_fset (ffilter ((\<prec>\<^sub>c) C) (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
          using step_hyps \<C>\<^sub>y_def by (metis The_optional_eq_SomeD)
        hence f_y_eq: "f y = {|E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). D \<preceq>\<^sub>c E|}"
          unfolding f_def y_def prod.case \<C>\<^sub>y_def option.case linorder_cls.is_least_in_ffilter_iff
          by auto

        show ?thesis
          unfolding f_y_eq subset_ffilter
          using D_least
          unfolding linorder_cls.is_least_in_ffilter_iff
          by auto
      qed

      also have "\<dots> |\<subset>| finsert C {|D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<preceq>\<^sub>c D|}"
        by auto

      also have "\<dots> = f x"
        unfolding f_def x_def y_def prod.case step_hyps option.case by metis

      finally show ?thesis .
    next
      case step_hyps: (factoring C L)

      have "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using x_invars unfolding \<open>\<C>\<^sub>x = Some C\<close>
        by (metis next_clause_in_factorized_clause_def ord_res_5_invars_def)
      hence "C |\<notin>| \<F>"
        using step_hyps(3,4,5)
        by (smt (verit, ccfv_SIG) fimage_iff iefac_def literal.collapse(1)
            ex1_efac_eq_factoring_chain ex_ground_factoringI)
      moreover have "C |\<in>| \<F>"
        using \<open>\<F> = finsert C \<F>\<close> by auto
      ultimately have False
        by contradiction
      thus ?thesis ..
    next
      case step_hyps: (resolution C L D)

      have D_productive: "atm_of L \<in> ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D"
        using x_invars step_hyps
        by (metis ord_res_5_invars_def atoms_in_model_were_produced_def)

      hence "\<exists>DC. ground_resolution D C DC"
        unfolding ground_resolution_def
        using step_hyps
        by (metis Neg_atm_of_iff ord_res.mem_productionE linorder_cls.le_less_linear
            linorder_lit.is_maximal_in_mset_iff linorder_trm.dual_order.order_iff_strict
            linorder_trm.not_less ord_res.less_trm_if_neg ex_ground_resolutionI)

      hence "eres D C \<noteq> C"
        unfolding eres_ident_iff by metis

      have "eres D C |\<notin>| U\<^sub>e\<^sub>r"
      proof (rule notI)
        assume "eres D C |\<in>| U\<^sub>e\<^sub>r"
        hence "iefac \<F> (eres D C) |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
          by simp

        moreover have "iefac \<F> (eres D C) \<prec>\<^sub>c C"
        proof -
          have "iefac \<F> C \<prec>\<^sub>c D" if "C \<prec>\<^sub>c D" for \<F> C D
          proof (cases "C |\<in>| \<F>")
            case True
            hence "iefac \<F> C = efac C"
              by (simp add: iefac_def)
            also have "\<dots> \<preceq>\<^sub>c C"
              by (metis efac_subset subset_implies_reflclp_multp)
            also have "\<dots> \<prec>\<^sub>c D"
              using that .
            finally show ?thesis .
          next
            case False
            thus ?thesis
              using that by (simp add: iefac_def)
          qed

          moreover have "eres D C \<prec>\<^sub>c C"
          proof -
            have "eres D C \<preceq>\<^sub>c C"
              using eres_le by metis
            thus "eres D C \<prec>\<^sub>c C"
              using \<open>eres D C \<noteq> C\<close> by order
          qed

          ultimately show ?thesis
            by metis
        qed

        ultimately have "ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) (iefac \<F> (eres D C)) \<TTurnstile> iefac \<F> (eres D C)"
          using x_invars unfolding \<open>\<C>\<^sub>x = Some C\<close>
          unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def by fast
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> iefac \<F> (eres D C)"
          using ord_res.entailed_clause_stays_entailed' \<open>iefac \<F> (eres D C) \<prec>\<^sub>c C\<close> by metis
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> eres D C"
        proof (rule true_cls_iff_set_mset_eq[THEN iffD1, rotated])
          show "set_mset (iefac \<F> (eres D C)) = set_mset (eres D C)"
            using iefac_def by auto
        qed
        hence "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        proof -
          obtain m A D' C' where
            "ord_res.is_strictly_maximal_lit (Pos A) D" and
            D_def: "D = add_mset (Pos A) D'" and
            C_def: "C = replicate_mset (Suc m) (Neg A) + C'" and
            "Neg A \<notin># C'" and
            eres_D_C_eq: "eres D C = repeat_mset (Suc m) D' + C'"
            using \<open>eres D C \<noteq> C\<close>[THEN eres_not_identD] by metis

          hence
            "atm_of L = A" and
            D_in: "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
            D_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
            unfolding atomize_conj
            using D_productive
            unfolding ord_res.production_unfold mem_Collect_eq
            by (metis linorder_lit.Uniq_is_greatest_in_mset literal.inject(1) the1_equality')

          have D'_false: "\<not> ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D'"
            using D_false D_def by fastforce

          have "D \<prec>\<^sub>c C"
            using \<open>\<exists>DC. ground_resolution D C DC\<close> left_premise_lt_right_premise_if_ground_resolution by blast

          let ?I = "ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"

          assume "?I \<TTurnstile> eres D C"
          hence "?I \<TTurnstile> D' \<or> ?I \<TTurnstile> C'"
            unfolding eres_D_C_eq true_cls_union true_cls_repeat_mset_Suc .

          moreover have "\<not> ?I \<TTurnstile> D'"
            using \<open>D \<prec>\<^sub>c C\<close>
            by (smt (verit) D_def D_productive \<open>ord_res.is_strictly_maximal_lit (Pos A) D\<close>
                diff_single_eq_union ord_res.mem_productionE linorder_lit.is_greatest_in_mset_iff
                ord_res.Uniq_striclty_maximal_lit_in_ground_cls
                ord_res.false_cls_if_productive_production ord_res_5_invars_def
                next_clause_in_factorized_clause_def step_hyps(1) the1_equality' x_invars)

          ultimately show "?I \<TTurnstile> C"
            by (simp add: C_def)
        qed
        hence "dom \<M>\<^sub>x \<TTurnstile> C"
          using x_invars \<open>\<C>\<^sub>x = Some C\<close>
          by (metis model_eq_interp_upto_next_clause_def ord_res_5_invars_def)
        thus False
          using \<open>\<not> dom \<M>\<^sub>x \<TTurnstile> C\<close> by contradiction
      qed
      hence False
        using \<open>U\<^sub>e\<^sub>r = finsert (eres D C) U\<^sub>e\<^sub>r\<close> by auto
      thus ?thesis ..
    qed
  qed

  then obtain \<M>' \<C>' where "R\<^sup>*\<^sup>* (\<M>, \<C>) (\<M>', \<C>')" and "\<nexists>z. R (\<M>', \<C>') z"
    using ex_terminating_rtranclp_strong by (metis surj_pair)

  show ?thesis
  proof (intro exI conjI)
    show "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
      using \<open>R\<^sup>*\<^sup>* (\<M>, \<C>) (\<M>', \<C>')\<close>
      by (induction "(\<M>, \<C>)" arbitrary: \<M> \<C> rule: converse_rtranclp_induct) (auto simp: R_def)
  next
    show "\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>'')"
      using \<open>\<nexists>z. R (\<M>', \<C>') z\<close>
      by (simp add: R_def)
  qed
qed

lemma MAGIC2:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C)"
  assumes "C \<noteq> {#}"
  shows "\<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>, Some C) s'"
proof (cases "(dom \<M>) \<TTurnstile> C")
  case C_true: True
  thus ?thesis
    using ord_res_5.skip by metis
next
  case C_false: False
  obtain L where L_max: "linorder_lit.is_maximal_in_mset C L"
    using \<open>C \<noteq> {#}\<close> linorder_lit.ex_maximal_in_mset by metis

  show ?thesis
  proof (cases L)
    case (Pos A)
    hence L_pos: "is_pos L"
      by simp

    show ?thesis
    proof (cases "linorder_lit.is_greatest_in_mset C L")
      case L_greatest: True
      thus ?thesis
        using C_false L_max L_pos ord_res_5.production by metis
    next
      case L_not_greatest: False
      thus ?thesis
        using C_false L_max L_pos ord_res_5.factoring by metis
    qed
  next
    case (Neg A)
    hence L_neg: "is_neg L"
      by simp

    have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars unfolding ord_res_5_invars_def next_clause_in_factorized_clause_def by metis
    next
      have "dom \<M> = ord_res.interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C"
        using invars unfolding ord_res_5_invars_def model_eq_interp_upto_next_clause_def by metis

      moreover have "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C = {}"
      proof -
        have "\<nexists>L. is_pos L \<and> ord_res.is_strictly_maximal_lit L C"
          using L_max L_neg
          by (metis Uniq_D linorder_lit.Uniq_is_maximal_in_mset
              linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset)
        thus ?thesis
          using unproductive_if_nex_strictly_maximal_pos_lit by metis
      qed

      ultimately show "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        using C_false model_eq_interp_upto_next_clause_def by simp
    next
      fix D
      assume
        "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "D \<noteq> C" and
        "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"

      moreover have "\<forall>B |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). B \<prec>\<^sub>c C \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) B \<TTurnstile> B"
        using invars
        unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def
        by simp

      ultimately show "C \<prec>\<^sub>c D"
        by force
    qed
    then obtain D where "D|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
      "D \<prec>\<^sub>c C" and
      "ord_res.is_strictly_maximal_lit (Pos A) D" and
      D_prod: "ord_res.production (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D = {A}"
      using bex_smaller_productive_clause_if_least_false_clause_has_negative_max_lit
        L_max[unfolded Neg] by metis

    have "\<M> (atm_of L) = Some D"
      using invars
      unfolding ord_res_5_invars_def all_produced_atoms_in_model_def
      by (metis Neg \<open>D \<prec>\<^sub>c C\<close> D_prod insertI1 literal.sel(2))

    thus ?thesis
      using ord_res_5.resolution C_false L_max L_neg by metis
  qed
qed

lemma MAGIC3:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)" and
    steps: "(ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')" and
    no_more_steps: "(\<nexists>\<M>'' \<C>''. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') (U\<^sub>e\<^sub>r, \<F>, \<M>'', \<C>''))"
  shows "(\<forall>C. \<C>' = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
proof -
  have invars': "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
    using steps invars rtranclp_ord_res_5_preserves_invars by metis

  show ?thesis
  proof (cases \<C>')
    case None

    moreover have "\<nexists>C. is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"
    proof (rule notI, elim exE)
      fix C

      have "all_smaller_clauses_true_wrt_respective_Interp N (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>')"
        using invars' unfolding ord_res_5_invars_def by metis
      hence "(\<forall>C|\<in>|iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C)"
        by (simp add: \<open>\<C>' = None\<close> all_smaller_clauses_true_wrt_respective_Interp_def)

      moreover assume "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C"

      ultimately show False
        unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff by metis
    qed

    ultimately show ?thesis
      by simp
  next
    case (Some D)

    moreover have "is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) D"
      unfolding is_least_false_clause_def linorder_cls.is_least_in_ffilter_iff
    proof (intro conjI ballI impI)
      show "D |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)"
        using invars' \<open>\<C>' = Some D\<close>
        unfolding ord_res_5_invars_def next_clause_in_factorized_clause_def
        by metis
    next
      have "D \<noteq> {#} \<Longrightarrow> \<exists>s'. ord_res_5 N (U\<^sub>e\<^sub>r, \<F>, \<M>', Some D) s'"
        using MAGIC2 invars' \<open>\<C>' = Some D\<close> by metis

      thus "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) D \<TTurnstile> D"
        by (smt (verit) Pair_inject Un_empty_right Uniq_D calculation empty_iff invars'
            linorder_lit.Uniq_is_maximal_in_mset
            linorder_lit.is_maximal_in_mset_if_is_greatest_in_mset no_more_steps option.inject
            ord_res_5.cases set_mset_empty model_eq_interp_upto_next_clause_def ord_res_5_invars_def
            true_cls_def unproductive_if_nex_strictly_maximal_pos_lit)
    next
      fix E
      assume
        "E |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)" and
        "E \<noteq> D" and
        "\<not> ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) E \<TTurnstile> E"

      moreover have "\<forall>C |\<in>| iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r). C \<prec>\<^sub>c D \<longrightarrow>
        ord_res_Interp (fset (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r))) C \<TTurnstile> C"
        using invars' \<open>\<C>' = Some D\<close>
        unfolding ord_res_5_invars_def all_smaller_clauses_true_wrt_respective_Interp_def
        by simp

      ultimately show "D \<prec>\<^sub>c E"
        by force
    qed

    ultimately show ?thesis
      by (metis Uniq_D Uniq_is_least_false_clause option.inject)
  qed
qed

lemma ord_res_5_construct_model_upto_least_false_clause:
  assumes invars: "ord_res_5_invars N (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>)"
  shows "\<exists>\<M>' \<C>'. (ord_res_5 N)\<^sup>*\<^sup>* (U\<^sub>e\<^sub>r, \<F>, \<M>, \<C>) (U\<^sub>e\<^sub>r, \<F>, \<M>', \<C>') \<and>
    (\<forall>C. \<C>' = Some C \<longleftrightarrow> is_least_false_clause (iefac \<F> |`| (N |\<union>| U\<^sub>e\<^sub>r)) C)"
  using MAGIC1[OF invars] MAGIC3[OF invars] by metis

end

end