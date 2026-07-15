theory First_Order_to_Higher_Order_Terms
  imports
    "First_Order_Terms.Term"
    LN_Lambda_Term
begin

lemma foldl_def_eq_def_iff_list_eq_nil:
  assumes "\<And>x y. f x y \<noteq> e"
  shows "foldl f e xs = e \<longleftrightarrow> xs = []"
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    using assms
    by (metis foldl_Cons foldl_Nil foldl_append rev_exhaust)
qed

text \<open>First-order terms carry no type information, so the free variables produced here are
  annotated according to an externally supplied type environment \<open>\<F>\<close> for first-order variable
  names.\<close>

primrec foterm_to_hoterm :: "('f \<Rightarrow> '\<tau>) \<Rightarrow> ('c, 'f) Term.term \<Rightarrow> ('\<tau>, 'c, 'f) LN_Lambda_Term.preterm"  where
  "foterm_to_hoterm \<F> (Term.Var x) = Free x (\<F> x)" |
  "foterm_to_hoterm \<F> (Term.Fun f ts) = foldl App (Const f [] []) (map (foterm_to_hoterm \<F>) ts)"

lemma
  fixes z :: "('\<tau>, 'c, 'f) LN_Lambda_Term.preterm"
  assumes "\<And>x y. App x y \<noteq> z"
  shows "inj (foldl App z)"
proof (rule injI)
  fix xs ys :: "('\<tau>, 'c, 'f) LN_Lambda_Term.preterm list"
  assume "foldl App z xs = foldl App z ys"
  thus "xs = ys"
    using assms
  proof (induction xs ys arbitrary: z rule: List.rev_induct2)
    case (3 y ys)
    hence False
      by (metis foldl_Cons foldl_Nil foldl_append)
    thus ?case ..
  qed simp_all
qed

lemma foterm_to_hoterm_Fun_eq_Const_or_App:
  fixes \<F> :: "'f \<Rightarrow> '\<tau>" and f :: "'c" and args :: "('c, 'f) Term.term list"
  shows
    "foterm_to_hoterm \<F> (Term.Fun f args) = Const f [] [] \<or>
    (\<exists>t\<^sub>1 t\<^sub>2. foterm_to_hoterm \<F> (Term.Fun f args) = App t\<^sub>1 t\<^sub>2)"
proof (induction args)
  case Nil
  then show ?case
    by simp
next
  case (Cons arg args)
  then show ?case (is "?CONS \<or> ?APP")
  proof (elim disjE exE)
    assume "foterm_to_hoterm \<F> (Term.Fun f args) = Const f [] []"
    then have "args = []"
      by (simp add: foldl_def_eq_def_iff_list_eq_nil)
    then have "?APP"
      by simp
    then show ?thesis ..
  next
    fix t\<^sub>1 t\<^sub>2 :: "('\<tau>, 'c, 'f) LN_Lambda_Term.preterm"
    have "foterm_to_hoterm \<F> (Term.Fun f (arg # args)) =
      foldl App (Const f [] []) (foterm_to_hoterm \<F> arg # map (foterm_to_hoterm \<F>) args)"
      unfolding foterm_to_hoterm.simps
      using foldl_append[of _ _ "[_]", unfolded append_Cons append_Nil]
      by simp
    also have "\<dots> = foldl App (App (Const f [] []) (foterm_to_hoterm \<F> arg)) (map (foterm_to_hoterm \<F>) args)"
      by simp
    finally have "foterm_to_hoterm \<F> (Term.Fun f (arg # args)) =
      foldl App (App (Const f [] []) (foterm_to_hoterm \<F> arg)) (map (foterm_to_hoterm \<F>) args)" .
    moreover assume "foterm_to_hoterm \<F> (Term.Fun f args) = App t\<^sub>1 t\<^sub>2"
    ultimately have "?APP"
      by (metis (no_types, opaque_lifting) foldl_Cons
          foldl_Nil foldl_append list.distinct(1)
          rev_exhaust)
    then show ?thesis ..
  qed
qed

lemma inj_on_foterm_to_hoterm:
  fixes \<F> :: "'f \<Rightarrow> '\<tau>" and A :: "('c, 'f) Term.term set"
  shows "inj_on (foterm_to_hoterm \<F>) A"
proof (rule inj_onI)
  fix s and t :: "('c, 'f) Term.term"
  assume "foterm_to_hoterm \<F> s = (foterm_to_hoterm \<F> t :: ('\<tau>, 'c, 'f) preterm)"
  then show "s = t"
  proof (induction s arbitrary: t rule: Term.term.induct)
    case Var\<^sub>s: (Var x\<^sub>s)
    show ?case
    proof (cases t)
      case (Var x\<^sub>t)
      then show ?thesis
        using Var\<^sub>s by simp
    next
      case (Fun f\<^sub>t args\<^sub>t)
      then have False
        using Var\<^sub>s foterm_to_hoterm_Fun_eq_Const_or_App
        by (metis foterm_to_hoterm.simps(1)
            preterm.distinct(1,11))
      then show ?thesis ..
    qed
  next
    case Fun\<^sub>s: (Fun f\<^sub>s args\<^sub>s)
    show ?case
    proof (cases t)
      case (Var x\<^sub>t)
      then have False
        using Fun\<^sub>s
        by (metis foterm_to_hoterm.simps(1)
            foterm_to_hoterm_Fun_eq_Const_or_App
            preterm.distinct(1,11))
      then show ?thesis ..
    next
      case Fun\<^sub>t: (Fun f\<^sub>t args\<^sub>t)
      have "foterm_to_hoterm \<F> (Term.Fun f\<^sub>s args\<^sub>s) = (foterm_to_hoterm \<F> (Term.Fun f\<^sub>t args\<^sub>t) :: ('\<tau>, 'c, 'f) preterm)"
        unfolding Fun\<^sub>s.prems Fun\<^sub>t ..

      hence "foldl App (Const f\<^sub>s [] []) (map (foterm_to_hoterm \<F>) args\<^sub>s) =
        (foldl App (Const f\<^sub>t [] []) (map (foterm_to_hoterm \<F>) args\<^sub>t) :: ('\<tau>, 'c, 'f) preterm)"
        by simp

      hence "f\<^sub>s = f\<^sub>t" and "map (foterm_to_hoterm \<F>) args\<^sub>s = (map (foterm_to_hoterm \<F>) args\<^sub>t :: ('\<tau>, 'c, 'f) preterm list)"
        by simp_all

      hence "args\<^sub>s = args\<^sub>t"
      proof (elim list.inj_map_strong[rotated])
        show "\<And>z za. z \<in> set args\<^sub>s \<Longrightarrow> za \<in> set args\<^sub>t \<Longrightarrow>
          foterm_to_hoterm \<F> z = (foterm_to_hoterm \<F> za :: ('\<tau>, 'c, 'f) preterm) \<Longrightarrow> z = za"
          using Fun\<^sub>s.IH by metis
      qed

      thus ?thesis
        unfolding Fun\<^sub>t
        using \<open>f\<^sub>s = f\<^sub>t\<close> by metis
    qed
  qed
qed

inductive eff_first_order :: "('f \<Rightarrow> '\<tau>) \<Rightarrow> ('\<tau>, 'c, 'f) preterm \<Rightarrow> bool"
  for \<F> where
  Const: "eff_first_order \<F> (Const f [] [])" |
  Free: "eff_first_order \<F> (Free x (\<F> x))" |
  App: "eff_first_order \<F> (App t\<^sub>1 t\<^sub>2)"
    if "eff_first_order \<F> t\<^sub>1" and "is_Const (head t\<^sub>1)" and "eff_first_order \<F> t\<^sub>2"

lemma eff_first_orderE_foldl_App:
  fixes t :: "('\<tau>, 'c, 'f) preterm"
  assumes "eff_first_order \<F> t"
  shows "is_Const t \<or> is_Free t \<or>
    (\<exists>xs. (\<forall>x \<in> set xs. eff_first_order \<F> x) \<and> t = foldl App (head t) xs)"
    (is "_ \<or> _ \<or> ?IS_APP t")
  using assms
proof (induction t rule: eff_first_order.induct)
  case (Const f)
  then show ?case by simp
next
  case (Free x)
  then show ?case by simp
next
  case (App t\<^sub>1 t\<^sub>2)
  have "?IS_APP (App t\<^sub>1 t\<^sub>2)"
    using App.IH(1)
  proof (elim disjE exE conjE)
    assume "is_Const t\<^sub>1"
    then show ?thesis
      by (metis (no_types, opaque_lifting)
          App.hyps(3) all_not_in_conv empty_set
          foldl_Cons foldl_Nil head.simps(1,4) insertE
          is_Const_def list.simps(15))
  next
    assume "is_Free t\<^sub>1"
    hence False
      using App.hyps
      by (metis head.simps(2) is_Free_def preterm.distinct_disc(1))
    thus ?thesis ..
  next
    fix xs :: "('\<tau>, 'c, 'f) preterm list"
    assume "\<forall>x\<in>set xs. eff_first_order \<F> x" and "t\<^sub>1 = foldl App (head t\<^sub>1) xs"
    show ?thesis
    proof (intro exI conjI ballI)
      show "\<And>x. x \<in> set (xs @ [t\<^sub>2]) \<Longrightarrow> eff_first_order \<F> x"
        using App.hyps(3) \<open>\<forall>x\<in>set xs. eff_first_order \<F> x\<close>
        by auto
    next
      show "App t\<^sub>1 t\<^sub>2 = foldl App (head (App t\<^sub>1 t\<^sub>2)) (xs @ [t\<^sub>2])"
        using \<open>t\<^sub>1 = foldl App (head t\<^sub>1) xs\<close>
        by auto
    qed
  qed
  thus ?case
    by metis
qed

lemma App_eq_foldl_App_ConsD:
  assumes "App t\<^sub>1 t\<^sub>2 = foldl App (Const f [] []) xs"
  shows "\<exists>xs'. xs = xs' @ [t\<^sub>2] \<and> t\<^sub>1 = foldl App (Const f [] []) xs'"
  using assms
  by (induction xs rule: List.rev_induct) simp_all

lemma App_in_range_fo_term_to_ho_termD:
  assumes "App t\<^sub>1 t\<^sub>2 \<in> range (foterm_to_hoterm \<F>)"
  shows "t\<^sub>1 \<in> range (foterm_to_hoterm \<F>) \<and> t\<^sub>2 \<in> range (foterm_to_hoterm \<F>)"
proof -
  obtain t\<^sub>G where "foterm_to_hoterm \<F> t\<^sub>G = App t\<^sub>1 t\<^sub>2"
    using assms by force

  then show ?thesis
  proof (induction t\<^sub>G arbitrary: t\<^sub>1 t\<^sub>2)
    case (Var x)
    then show ?case by simp
  next
    case (Fun g ys)
    obtain y ys' where "ys = ys' @ [y]"
      using Fun.prems[simplified]
      by (metis foldl_Nil list.simps(8) preterm.distinct(5) rev_exhaust)

    show ?case
      using Fun.prems[unfolded \<open>ys = ys' @ [y]\<close>, simplified]
      using Fun.IH
      by (metis foterm_to_hoterm.simps(2) rangeI)
  qed
qed

lemma head_foldl_App[simp]: "head (foldl App x xs) = head x"
  by (induction xs arbitrary: x rule: rev_induct) simp_all

lemma
  "bij_betw (foterm_to_hoterm \<F>) UNIV {t :: ('\<tau>, 'c, 'f) preterm. eff_first_order \<F> t}"
  unfolding bij_betw_def
proof (intro conjI)
  show "inj_on (foterm_to_hoterm \<F>) UNIV"
    using inj_on_foterm_to_hoterm .
next
  show "range (foterm_to_hoterm \<F>) = {t :: ('\<tau>, 'c, 'f) preterm. eff_first_order \<F> t}"
  proof (intro subset_antisym subsetI , unfold mem_Collect_eq)
    fix t :: "('\<tau>, 'c, 'f) preterm"
    assume "t \<in> range (foterm_to_hoterm \<F>)"
    then obtain t\<^sub>G where "t = foterm_to_hoterm \<F> t\<^sub>G"
      by blast
    show "eff_first_order \<F> t"
      unfolding \<open>t = foterm_to_hoterm \<F> t\<^sub>G\<close>
    proof (induction t\<^sub>G)
      case (Var x)
      thus ?case
        by (simp add: eff_first_order.Free)
    next
      case (Fun f xs)
      hence "eff_first_order \<F> (foldl App (Const f [] []) (map (foterm_to_hoterm \<F>) xs :: ('\<tau>, 'c, 'f) preterm list))"
      proof (induction xs rule: List.rev_induct)
        case Nil
        then show ?case
        by (simp add: eff_first_order.Const)
      next
        case (snoc x xs)
        have "eff_first_order \<F> (App (foldl App (Const f [] []) (map (foterm_to_hoterm \<F>) xs :: ('\<tau>, 'c, 'f) preterm list))
          (foterm_to_hoterm \<F> x))"
        proof (rule eff_first_order.App)
          show "eff_first_order \<F> (foldl App (Const f [] []) (map (foterm_to_hoterm \<F>) xs :: ('\<tau>, 'c, 'f) preterm list))"
            using snoc by simp
        next
          show "is_Const (head (foldl App (Const f [] []) (map (foterm_to_hoterm \<F>) xs :: ('\<tau>, 'c, 'f) preterm list)))"
            by simp
        next
          show "eff_first_order \<F> (foterm_to_hoterm \<F> x :: ('\<tau>, 'c, 'f) preterm)"
            by (simp add: snoc.prems)
        qed
        thus ?case
          by simp
      qed
      thus ?case
        by simp
    qed
  next
    fix t :: "('\<tau>, 'c, 'f) preterm"
    assume "eff_first_order \<F> t"
    thus "t \<in> range (foterm_to_hoterm \<F>)"
    proof (induction t rule: eff_first_order.induct)
      case (Const f)
      show ?case
      proof (rule range_eqI)
        show "Const f [] [] = foterm_to_hoterm \<F> (Term.Fun f [])"
          by simp
      qed
    next
      case (Free x)
      show ?case
      proof (rule range_eqI)
        show "Free x (\<F> x) = foterm_to_hoterm \<F> (Term.Var x)"
          by simp
      qed
    next
      case (App t\<^sub>1 t\<^sub>2)
      obtain f :: 'c where "head t\<^sub>1 = Const f [] []"
        by (metis (no_types, opaque_lifting) App.IH(1)
            App.hyps(2) foterm_to_hoterm.simps(1,2)
            head.simps(1,2) head_foldl_App preterm.disc(2)
            rangeE vars_term_ms.cases)
      obtain xs :: "('\<tau>, 'c, 'f) preterm list" where
        "(\<forall>x\<in>set xs. eff_first_order \<F> x)" and "App t\<^sub>1 t\<^sub>2 = foldl App (Const f [] []) xs"
        using eff_first_orderE_foldl_App[of \<F> "App t\<^sub>1 t\<^sub>2"] \<open>head t\<^sub>1 = Const f [] []\<close>
        by (auto simp: App.hyps(1,2,3) eff_first_order.App)
      then obtain ys :: "('\<tau>, 'c, 'f) preterm list" where
        "xs = ys @ [t\<^sub>2]" and "t\<^sub>1 = foldl App (Const f [] []) ys"
        using App_eq_foldl_App_ConsD by metis
      hence "foldl App (Const f [] []) ys \<in> range (foterm_to_hoterm \<F>)"
        using App.IH(1) by simp
      hence "\<exists>ys\<^sub>G. ys = map (foterm_to_hoterm \<F>) ys\<^sub>G"
      proof (induction ys rule: List.rev_induct)
        case Nil
        then show ?case by simp
      next
        case (snoc x xs)
        then have "App (foldl App (Const f [] []) xs) x \<in> range (foterm_to_hoterm \<F>)"
          by simp
        then have
          "foldl App (Const f [] []) xs \<in> range (foterm_to_hoterm \<F>)" and
          "x \<in> range (foterm_to_hoterm \<F>)"
          using App_in_range_fo_term_to_ho_termD by blast+
        then show ?case
          using snoc.IH
          by (metis (no_types) list.simps(8,9) map_append rangeE)
      qed
      then obtain ys\<^sub>G where "ys = map (foterm_to_hoterm \<F>) ys\<^sub>G"
        by metis

      obtain t\<^sub>2\<^sub>G where "t\<^sub>2 = foterm_to_hoterm \<F> t\<^sub>2\<^sub>G"
        using App.IH(2) by blast

      define xs\<^sub>G where
        "xs\<^sub>G = ys\<^sub>G @ [t\<^sub>2\<^sub>G]"

      have "xs = map (foterm_to_hoterm \<F>) xs\<^sub>G"
        by (simp add: \<open>t\<^sub>2 = foterm_to_hoterm \<F> t\<^sub>2\<^sub>G\<close>
            \<open>xs = ys @ [t\<^sub>2]\<close>
            \<open>ys = map (foterm_to_hoterm \<F>) ys\<^sub>G\<close>
            xs\<^sub>G_def)

      show ?case
      proof (rule range_eqI)
        show "App t\<^sub>1 t\<^sub>2 = foterm_to_hoterm \<F> (Term.Fun f xs\<^sub>G)"
          unfolding \<open>App t\<^sub>1 t\<^sub>2 = foldl App (Const f [] []) xs\<close>
          by (simp add: \<open>xs = map (foterm_to_hoterm \<F>) xs\<^sub>G\<close>)
      qed
    qed
  qed
qed

end