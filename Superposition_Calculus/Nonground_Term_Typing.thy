theory Nonground_Term_Typing
  imports 
    Term_Typing 
    Typed_Functional_Substitution 
    Nonground_Term
begin

locale nonground_term_functional_substitution_typing = 
  base_functional_substitution_typing + 
  typed: explicitly_typed_subst_stability + 
  welltyped: explicitly_typed_subst_stability where typed = welltyped +
  typed: explicitly_replaceable_\<V> + 
  welltyped: explicitly_replaceable_\<V> where typed = welltyped +
  typed: explicitly_typed_renaming +
  welltyped: explicitly_typed_renaming where typed = welltyped +
  typed: inhabited_explicitly_typed_functional_substitution +
  welltyped: inhabited_explicitly_typed_functional_substitution where typed = welltyped

locale nonground_term_typing =
  "term": nonground_term +
  fixes \<F> :: "('f, 'ty) fun_types"
  assumes types_inhabited: "\<And>\<tau>. \<exists>f. \<F> f = ([], \<tau>)"
begin

inductive typed :: "('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> typed \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> typed \<V> (Fun f ts) \<tau>"

(* TODO/ Note: Implicitly implies that for every function symbol there is one fixed arity *)
inductive welltyped :: "('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<V>) ts \<tau>s \<Longrightarrow> welltyped \<V> (Fun f ts) \<tau>"

sublocale "term": explicit_typing "typed (\<V> :: 'v \<Rightarrow> 'ty)" "welltyped \<V>"
proof unfold_locales
  show "right_unique (typed \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "typed \<V> t \<tau>\<^sub>1" and "typed \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: typed.cases)
  qed
next
  show welltyped_right_unique: "right_unique (welltyped \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped \<V> t \<tau>\<^sub>1" and "welltyped \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
next
  fix t \<tau> 
  assume "welltyped \<V> t \<tau>"
  then show "typed \<V> t \<tau>"
    by (metis (full_types) typed.simps welltyped.cases)
qed

sublocale "term": term_typing where 
  typed = "typed (\<V> :: 'v \<Rightarrow> 'ty)" and welltyped = "welltyped \<V>" and Fun = Fun
proof unfold_locales
  fix t t' c \<tau> \<tau>'
  assume 
    t_type: "welltyped \<V> t \<tau>'" and 
    t'_type: "welltyped \<V> t' \<tau>'" and
    c_type: "welltyped \<V> c\<langle>t\<rangle> \<tau>"

  from c_type show "welltyped \<V> c\<langle>t'\<rangle> \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using t_type t'_type
      by auto
  next
    case (More f ss1 c ss2)

    have "welltyped \<V> (Fun f (ss1 @ c\<langle>t\<rangle> # ss2)) \<tau>"
      using More.prems 
      by simp

    hence "welltyped \<V> (Fun f (ss1 @ c\<langle>t'\<rangle> # ss2)) \<tau>"
    proof (cases \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: welltyped.cases)
      case (Fun \<tau>s)

      show ?thesis
      proof (rule welltyped.Fun)
        show "\<F> f = (\<tau>s, \<tau>)"
          using \<open>\<F> f = (\<tau>s, \<tau>)\<close> .
      next
        show "list_all2 (welltyped \<V>) (ss1 @ c\<langle>t'\<rangle> # ss2) \<tau>s"
          using \<open>list_all2 (welltyped \<V>) (ss1 @ c\<langle>t\<rangle> # ss2) \<tau>s\<close>
          using More.IH
          by (smt (verit, del_insts) list_all2_Cons1 list_all2_append1 list_all2_lengthD)
      qed
    qed

    thus ?case
      by simp
  qed
next
  fix t t' c \<tau> \<tau>'
  assume
    t_type: "typed \<V> t \<tau>'" and 
    t'_type: "typed \<V> t' \<tau>'" and
    c_type: "typed \<V> c\<langle>t\<rangle> \<tau>"

  from c_type show "typed \<V> c\<langle>t'\<rangle> \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using t'_type t_type 
      by auto
  next
    case (More f ss1 c ss2)

    have "typed \<V> (Fun f (ss1 @ c\<langle>t\<rangle> # ss2)) \<tau>"
      using More.prems 
      by simp

    hence "typed \<V> (Fun f (ss1 @ c\<langle>t'\<rangle> # ss2)) \<tau>"
    proof (cases \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: typed.cases)
      case (Fun \<tau>s)

      then show ?thesis
        by (simp add: typed.simps)
    qed

    thus ?case
      by simp
  qed
next
  fix f ts \<tau>
  assume "welltyped \<V> (Fun f ts) \<tau>"
  then show "\<forall>t\<in>set ts. term.is_welltyped \<V> t"
    by (cases rule: welltyped.cases) (metis in_set_conv_nth list_all2_conv_all_nth)
next
  fix t
  show "term.is_typed \<V> t"
    by (metis term.exhaust prod.exhaust typed.simps)
qed

sublocale nonground_term_functional_substitution_typing where 
  id_subst = "Var :: 'v \<Rightarrow> ('f, 'v) term" and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and 
  vars = term.vars and welltyped = welltyped and typed = typed
proof unfold_locales
  fix \<V> :: "('v, 'ty) var_types" and x
  show "welltyped \<V> (Var x) (\<V> x)"
    by (simp add: welltyped.Var)
next
  fix \<tau> and \<V> and t :: "('f, 'v) term" and \<sigma>
  assume is_typed_on: "\<forall>x \<in> term.vars t. typed \<V> (\<sigma> x) (\<V> x)"

  show "typed \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> typed \<V> t \<tau>"
  proof(rule iffI)
    assume "typed \<V> t \<tau>"
    then show "typed \<V> (t \<cdot>t \<sigma>) \<tau>"
      using is_typed_on
      by(induction rule: typed.induct)(auto simp: typed.Fun)
  next
    assume "typed \<V> (t \<cdot>t \<sigma>) \<tau>"
    then show "typed \<V> t \<tau>"
      using is_typed_on
      by(induction t)(auto simp: typed.simps)
  qed
next
  fix \<tau> and \<V> and t :: "('f, 'v) term" and \<sigma>

  assume is_welltyped_on: "\<forall>x \<in> term.vars t. welltyped \<V> (\<sigma> x) (\<V> x)"

  show "welltyped \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> welltyped \<V> t \<tau>"
  proof(rule iffI)
    assume "welltyped \<V> t \<tau>"
    then show "welltyped \<V> (t \<cdot>t \<sigma>) \<tau>"
      using is_welltyped_on
      by(induction rule: welltyped.induct)
        (auto simp: list.rel_mono_strong list_all2_map1 welltyped.simps)
  next
    assume "welltyped \<V> (t \<cdot>t \<sigma>) \<tau>"
    then show "welltyped \<V> t \<tau>"
      using is_welltyped_on
    proof(induction "t \<cdot>t \<sigma>" \<tau>  arbitrary: t rule: welltyped.induct)
      case (Var x \<tau>)

      then obtain x' where t: "t = Var x'"
        by (metis subst_apply_eq_Var)

      have "welltyped \<V> t (\<V> x')"
        unfolding t 
        by (simp add: welltyped.Var)

      moreover have "welltyped \<V> t (\<V> x)"
        using Var
        unfolding t
        by (simp add: welltyped.simps)

      ultimately have \<V>_x': "\<tau> = \<V> x'"
        using Var.hyps
        by blast

      show ?case 
        unfolding t \<V>_x'
        by (simp add: welltyped.Var)
    next
      case (Fun f \<tau>s \<tau> ts)

      then show ?case 
        by (cases t) (simp_all add: list.rel_mono_strong list_all2_map1 welltyped.simps)
    qed
  qed
next
  fix t :: "('f, 'v) term" and \<V> \<V>' \<tau>
  assume "typed \<V> t \<tau>" "\<forall>x\<in>term.vars t. \<V> x = \<V>' x" 
  then show "typed \<V>' t \<tau>"
    by (cases rule: typed.cases) (simp_all add: typed.simps)
next
  fix t :: "('f, 'v) term" and \<V> \<V>' \<tau>
  assume "welltyped \<V> t \<tau>" "\<forall>x\<in>term.vars t. \<V> x = \<V>' x"
  then show "welltyped \<V>' t \<tau>"
    by (induction rule: welltyped.induct) (simp_all add: welltyped.simps list.rel_mono_strong)
next
  fix \<V> \<V>' :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<rho> \<tau> 
  assume renaming: "term_subst.is_renaming \<rho>" "\<forall>x\<in>term.vars (t \<cdot>t \<rho>). \<V> (inv \<rho> (Var x)) = \<V>' x"

  show "typed \<V>' (t \<cdot>t \<rho>) \<tau> \<longleftrightarrow> typed \<V> t \<tau>"
  proof(intro iffI)
    assume "typed \<V>' (t \<cdot>t \<rho>) \<tau>"
    with renaming  show "typed \<V> t \<tau>"
    proof(induction t arbitrary: \<tau>)
      case (Var x)
      then obtain y where y: "Var x \<cdot>t \<rho> = Var y"
        by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

      then have "\<V> (inv \<rho> (Var y)) = \<V>' y"
        by (simp add: Var)

      moreover have "(inv \<rho> (Var y)) = x"
        using y renaming
        unfolding term_subst_is_renaming_iff
        by (metis eval_term.simps(1) inv_f_f)

      moreover have "\<V>' y = \<tau>"
        using Var
        unfolding y
        using typed.Var by fastforce

      ultimately have "\<V> x = \<tau>"
        by blast

      then show ?case
        by(rule typed.Var)
    next
      case (Fun f ts)
      then show ?case
        by (simp add: typed.simps)
    qed
  next
    assume "typed \<V> t \<tau>"
    then show "typed \<V>' (t \<cdot>t \<rho>) \<tau>"
      using renaming
    proof(induction rule: typed.induct)
      case (Var x \<tau>)

      obtain y where y: "Var x \<cdot>t \<rho> = Var y"
        using renaming
        by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

      then have "\<V> (inv \<rho> (Var y)) = \<V>' y"
        using Var(3)
        by simp     

      moreover have "(inv \<rho> (Var y)) = x"
        using y renaming
        unfolding term_subst_is_renaming_iff
        by (metis eval_term.simps(1) inv_f_f)

      ultimately have "\<V>' y = \<tau>"
        using Var
        by argo

      then show ?case
        unfolding y
        by(rule typed.Var)
    next
      case (Fun f \<tau>s \<tau> ts)

      then show ?case
        by (simp add: typed.simps)
    qed
  qed
next
  (* TODO  ! ! ! !*)
  fix \<V> \<V>' :: "('v, 'ty) var_types" and t :: "('f, 'v) term" and \<rho> \<tau> 
  assume renaming: "term_subst.is_renaming \<rho>" "\<forall>x\<in>term.vars (t \<cdot>t \<rho>). \<V> (inv \<rho> (Var x)) = \<V>' x"

  then show "welltyped \<V>' (t \<cdot>t \<rho>) \<tau> \<longleftrightarrow> welltyped \<V> t \<tau>"
  proof(intro iffI)
    assume "welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"
    with renaming  show "welltyped \<V> t \<tau>"
    proof(induction t arbitrary: \<tau>)
      case (Var x)
      then obtain y where y: "Var x \<cdot>t \<rho> = Var y"
        by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

      then have "\<V> (inv \<rho> (Var y)) = \<V>' y"
        by (simp add: Var)

      moreover have "(inv \<rho> (Var y)) = x"
        using y renaming
        unfolding term_subst_is_renaming_iff
        by (metis eval_term.simps(1) inv_f_f)

      moreover have "\<V>' y = \<tau>"
        using Var
        unfolding y
        using welltyped.Var by fastforce

      ultimately have "\<V> x = \<tau>"
        by blast

      then show ?case
        by(rule welltyped.Var)
    next
      case (Fun f ts)
      have "\<lbrakk>\<And>x2a \<tau>. \<lbrakk>x2a \<in> set ts; welltyped \<V>' (x2a \<cdot>t \<rho>) \<tau>\<rbrakk> \<Longrightarrow> welltyped \<V> x2a \<tau>;
     welltyped \<V>' (Fun f (map (\<lambda>s. s \<cdot>t \<rho>) ts)) \<tau>;
     \<forall>y\<in>set ts. \<forall>x\<in>term.vars (y \<cdot>t \<rho>). \<V> (inv \<rho> (Var x)) = \<V>' x\<rbrakk>
    \<Longrightarrow> welltyped \<V> (Fun f ts) \<tau>"
        by (smt (verit, best) Term.term.simps(2) Term.term.simps(4) list.rel_mono_strong 
            list_all2_map1 welltyped.simps)

      with Fun show ?case
        by auto
    qed
  next
    assume "welltyped \<V> t \<tau>"
    then show "welltyped \<V>' (t \<cdot>t \<rho>) \<tau>"
      using renaming
    proof(induction rule: welltyped.induct)
      case (Var x \<tau>)

      obtain y where y: "Var x \<cdot>t \<rho> = Var y"
        using renaming
        by (metis eval_term.simps(1) term.collapse(1) term_subst_is_renaming_iff)

      then have "\<V> (inv \<rho> (Var y)) = \<V>' y"
        using Var(3)
        by simp     

      moreover have "(inv \<rho> (Var y)) = x"
        using y renaming
        unfolding term_subst_is_renaming_iff
        by (metis eval_term.simps(1) inv_f_f)

      ultimately have "\<V>' y = \<tau>"
        using Var
        by argo

      then show ?case
        unfolding y
        by(rule welltyped.Var)
    next
      case (Fun f \<tau>s \<tau> ts)

      have "list_all2 (welltyped \<V>') (map (\<lambda>s. s \<cdot>t \<rho>) ts) \<tau>s"
        using Fun
        by(auto simp: list.rel_mono_strong list_all2_map1)

      then show ?case
        by (simp add: Fun.hyps welltyped.simps)
    qed
  qed
next
  show "\<And>\<V> x \<tau>. \<V> x = \<tau> \<Longrightarrow> typed \<V> (Var x) \<tau>"
    using typed.Var .
next
  show "\<And>\<V> x \<tau>. \<V> x = \<tau> \<Longrightarrow> welltyped \<V> (Var x) \<tau>"
    using welltyped.Var .
next 
  fix \<V> :: "('v, 'ty) var_types" and \<tau>
 
  obtain f where f: "\<F> f = ([], \<tau>)"
    using types_inhabited
    by blast

  show "\<exists>t. term.is_ground t \<and> welltyped \<V> t \<tau>"
  proof(rule exI[of _ "Fun f []"], intro conjI welltyped.Fun)
    show "term.is_ground (Fun f [])"
      by simp
  next
    show "\<F> f = ([], \<tau>)"
      by(rule f)
  next
    show "list_all2 (welltyped \<V>) [] []"
      by simp
  qed

  then show "\<exists>t. term.is_ground t \<and> typed \<V> t \<tau>"  
    using term.typed_if_welltyped
    by blast
qed

(* TODO: Move further up *)
lemma is_welltyped_subst_compose [intro]:
  assumes "is_welltyped \<V> \<sigma>" "is_welltyped \<V> \<sigma>'"
  shows "is_welltyped \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding subst_compose_def
  by auto

(* TODO! ! *)
lemma is_welltyped_on_subst_compose [intro]:
  assumes "is_welltyped_on X \<V> \<sigma>" "is_welltyped_on (\<Union>(term.vars ` \<sigma> ` X)) \<V> \<sigma>'"
  shows "is_welltyped_on X \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding subst_compose_def
  by auto

(* TODO! ! *)
lemma is_welltyped_on_subst_compose_renaming:
  assumes
    "term_subst.is_renaming \<rho>"
    "is_welltyped_on X \<V> (\<rho> \<odot> \<sigma>)"
    "is_welltyped_on X \<V> \<rho>"
  shows "is_welltyped_on (\<Union> (term.vars ` \<rho> ` X)) \<V> \<sigma>"
  using assms
  unfolding term.is_renaming_iff
  unfolding subst_compose_def
  apply auto
  by (metis assms(1) eval_term.simps(1) is_FunI term.set_cases(2) term.welltyped.right_uniqueD term_subst_is_renaming_iff welltyped.typed_id_subst)

lemma is_typed_subst_compose [intro]:
  assumes "is_typed \<V> \<sigma>" "is_typed \<V> \<sigma>'"
  shows "is_typed \<V> (\<sigma> \<odot> \<sigma>')"
  using assms
  unfolding subst_compose_def
  by auto

lemma is_welltyped_subst: 
  assumes "welltyped \<V> (Var x) \<tau>" "welltyped \<V> t \<tau>"
  shows "is_welltyped \<V> (subst x t)"
  using assms
  unfolding subst_def
  by (simp add: welltyped.simps)

lemma Fun_arg_types:
  assumes 
    "welltyped \<V> (Fun f fs) \<tau>" 
    "welltyped \<V> (Fun f gs) \<tau>" 
  obtains \<tau>s where 
    "\<F> f = (\<tau>s, \<tau>)" 
    "list_all2 (welltyped \<V>) fs \<tau>s"
    "list_all2 (welltyped \<V>) gs \<tau>s"
  using assms
  by (smt (verit, ccfv_SIG) Pair_inject option.inject term.distinct term.inject welltyped.simps)

lemma welltyped_zip_option:
  assumes 
    "welltyped \<V> (Fun f ts) \<tau>" 
    "welltyped \<V> (Fun f ss) \<tau>" 
    "zip_option ts ss = Some es" 
  shows 
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
proof-

  obtain \<tau>s where 
    "list_all2 (welltyped \<V>) ts \<tau>s"
    "list_all2 (welltyped \<V>) ss \<tau>s"
    using Fun_arg_types[OF assms(1, 2)].

  with assms(3) show ?thesis
  proof(induction ts ss arbitrary: \<tau>s es rule: zip_induct)
    case (Cons_Cons t ts s ss)
    then obtain \<tau>' \<tau>s' where \<tau>s: "\<tau>s = \<tau>' # \<tau>s'"
      by (meson list_all2_Cons1)

    from Cons_Cons(2) 
    obtain e es' where es: "es = e # es'"
      by auto

    have "zip_option ts ss = Some es'"
      using Cons_Cons(2) 
      unfolding es
      by fastforce

    moreover have "list_all2 (welltyped \<V>) ts \<tau>s'" 
      using Cons_Cons.prems(2) \<tau>s by blast

    moreover have "list_all2 (welltyped \<V>) ss \<tau>s'"
      using Cons_Cons.prems(3) \<tau>s by blast

    ultimately have "\<forall>(t, s)\<in>set es'. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.IH
      by presburger

    moreover have "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> s \<tau>"
      using Cons_Cons.prems(2) Cons_Cons.prems(3) \<tau>s by blast

    ultimately show ?case
      using Cons_Cons.prems(1) es
      by fastforce
  qed(auto)
qed

lemma welltyped_decompose_Fun:
  assumes
    "welltyped \<V> (Fun f fs) \<tau>" 
    "welltyped \<V> (Fun f gs) \<tau>"
    "decompose (Fun f fs) (Fun g gs) = Some es"
  shows "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  using assms welltyped_zip_option[OF assms(1,2)]
  by (metis (lifting) decompose_Some not_Some_eq zip_option_simps(2,3))
  
lemma welltyped_decompose:
  assumes
    "welltyped \<V> f \<tau>" 
    "welltyped \<V> g \<tau>"
    "decompose f g = Some es"
  shows "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
proof-

  obtain f' fs gs where "f = Fun f' fs" "g = Fun f' gs"
    using assms(3)
    unfolding decompose_def
    by (smt (z3) option.distinct(1) prod.simps(2) rel_option_None1 term.split_sels(2))

  then show ?thesis
    using assms welltyped_decompose_Fun
    by (metis (mono_tags, lifting))
qed

lemma is_welltyped_unify:
  assumes    
    "unify es bs = Some unifier"
    "\<forall>(t, t') \<in> set es. \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    "is_welltyped \<V> (subst_of bs)"
  shows "is_welltyped \<V> (subst_of unifier)"
  using assms
proof(induction es bs arbitrary: unifier rule: unify.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 f ss g ts es bs)
  then obtain \<tau> where \<tau>:
    "welltyped \<V> (Fun f ss) \<tau>" 
    "welltyped \<V> (Fun g ts) \<tau>"
    by auto

  obtain es' where es': "decompose (Fun f ss) (Fun g ts) = Some es'"
    using 2(2)
    by(simp split: option.splits)

  moreover then have "unify (es' @ es) bs = Some unifier"
    using "2.prems"(1) 
    by auto

  moreover have "\<forall>(t, t')\<in>set (es' @ es). \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
    using welltyped_decompose[OF \<tau> es'] 2(3)
    by fastforce

  ultimately show ?case 
    using 2
    by blast
next
  case (3 x t es bs)
  show ?case
  proof(cases "t = Var x")
    case True
    then show ?thesis 
      using 3
      by simp
  next
    case False
    then have "unify (subst_list (subst x t) es) ((x, t) # bs) = Some unifier"
      using 3
      by(auto split: if_splits)

    moreover have 
      "\<forall>(s, s') \<in> set es. \<exists>\<tau>. welltyped \<V> (s \<cdot>t Var(x := t)) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := t)) \<tau>"
      using 3(4)
      by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
          list.set_intros(1) list.set_intros(2) right_uniqueD term.welltyped.right_unique 
           welltyped.explicit_subst_stability)

    moreover then have 
      "\<forall>(s, s') \<in> set (subst_list (subst x t) es). \<exists>\<tau>. welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
      unfolding subst_def subst_list_def
      by fastforce

    moreover have "is_welltyped \<V> (subst x t)"
      using 3(4) is_welltyped_subst
      by fastforce

    moreover then have "is_welltyped \<V> (subst_of ((x, t) # bs))"
      using 3(5)
      by (simp add: calculation(4) subst_compose_def)

    ultimately show ?thesis 
      using 3(2, 3) False by force
  qed
next
  case (4 t ts x es bs)
  then have "unify (subst_list (subst x (Fun t ts)) es) ((x, (Fun t ts)) # bs) = Some unifier"
    by(auto split: if_splits)

  moreover have 
    "\<forall>(s, s') \<in> set es. \<exists>\<tau>. 
        welltyped \<V> (s \<cdot>t Var(x := (Fun t ts))) \<tau> \<and> welltyped \<V> (s' \<cdot>t Var(x := (Fun t ts))) \<tau>"
    using 4(3)
    by (smt (verit, ccfv_threshold) case_prodD case_prodI2 fun_upd_apply welltyped.Var 
        list.set_intros(1) list.set_intros(2) right_uniqueD term.welltyped.right_unique 
        welltyped.explicit_subst_stability)

  moreover then have 
    "\<forall>(s, s') \<in> set (subst_list (subst x (Fun t ts)) es). \<exists>\<tau>. welltyped \<V> s \<tau> \<and> welltyped \<V> s' \<tau>"
    unfolding subst_def subst_list_def
    by fastforce

  moreover have "is_welltyped \<V> (subst x (Fun t ts))"
    using 4(3) is_welltyped_subst
    by fastforce

  moreover then have "is_welltyped \<V> (subst_of ((x, (Fun t ts)) # bs))"
    using 4(4) 
    by (simp add: calculation(4) subst_compose_def)

  ultimately show ?case 
    using 4(1, 2)
    by (metis (no_types, lifting) option.distinct(1) unify.simps(4))
qed

lemma is_welltyped_unify_single:
  assumes 
    unify: "unify [(t, t')] [] = Some unifier" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows "is_welltyped \<V> (subst_of unifier)"
  using assms is_welltyped_unify[OF unify] \<tau>
  by fastforce

lemma welltyped_the_mgu: 
  assumes
    the_mgu: "the_mgu t t' = \<mu>" and
    \<tau>: "\<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau>"
  shows 
    "is_welltyped \<V> \<mu>"
  using assms is_welltyped_unify_single[of t t' _ \<V>]
  unfolding the_mgu_def mgu_def  
  by(auto simp: welltyped.Var split: option.splits)

lemma welltyped_imgu_exists':
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "term \<cdot>t \<upsilon> = term' \<cdot>t \<upsilon>"
  obtains \<mu> :: "('f, 'v) subst"
  where 
    "\<upsilon> = \<mu> \<odot> \<upsilon>" 
    "term_subst.is_imgu \<mu> {{term, term'}}"
    "\<forall>\<tau>. welltyped \<V> term \<tau> \<longrightarrow> welltyped \<V> term' \<tau> \<longrightarrow> is_welltyped \<V> \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu term term' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "\<forall>\<tau>. welltyped \<V> term \<tau> \<longrightarrow> welltyped \<V> term' \<tau> \<longrightarrow> is_welltyped \<V> (the_mgu term term')"
    using welltyped_the_mgu[OF \<mu>, of \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that obtains_imgu_from_unifier_and_the_mgu[OF unified]
    by (metis the_mgu the_mgu_term_subst_is_imgu unified)
qed

abbreviation welltyped_imgu where
  "welltyped_imgu \<V> t t' \<mu> \<equiv>
    \<exists>\<tau>. welltyped \<V> t \<tau> \<and> welltyped \<V> t' \<tau> \<and> is_welltyped \<V> \<mu> \<and> term_subst.is_imgu \<mu> {{t, t'}}"

lemma obtain_welltyped_imgu:
  fixes \<upsilon> :: "('f, 'v) subst"
  assumes unified: "t \<cdot>t \<upsilon> = t' \<cdot>t \<upsilon>" and "welltyped \<V> t \<tau>" "welltyped \<V> t' \<tau>"
  obtains \<mu> :: "('f, 'v) subst"
  where "\<upsilon> = \<mu> \<odot> \<upsilon>" "welltyped_imgu \<V> t t' \<mu>"
proof-
  obtain \<mu> where \<mu>: "the_mgu t t' = \<mu>"
    using assms ex_mgu_if_subst_apply_term_eq_subst_apply_term by blast

  have "\<forall>\<tau>. welltyped \<V> t \<tau> \<longrightarrow> welltyped \<V> t' \<tau> \<longrightarrow> is_welltyped \<V> (the_mgu t t')"
    using welltyped_the_mgu[OF \<mu>, of \<V>] assms
    unfolding \<mu>
    by blast

  then show ?thesis
    using that obtains_imgu_from_unifier_and_the_mgu[OF unified]
    by (metis assms(2) assms(3) the_mgu the_mgu_term_subst_is_imgu unified)
qed

end

end
