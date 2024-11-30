theory Nonground_Term_Typing
  imports 
    Term_Typing 
    Typed_Functional_Substitution 
    Nonground_Term
begin

inductive typed :: "('f, 'ty) fun_types \<Rightarrow> ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<F> \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> typed \<F> \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> typed \<F> \<V> (Fun f ts) \<tau>"

(* TODO/ Note: Implicitly implies that for every function symbol there is one fixed arity *)
inductive welltyped :: "('f, 'ty) fun_types \<Rightarrow>  ('v, 'ty) var_types \<Rightarrow> ('f,'v) term \<Rightarrow> 'ty \<Rightarrow> bool" 
  for \<F> \<V> where
    Var: "\<V> x = \<tau> \<Longrightarrow> welltyped \<F> \<V> (Var x) \<tau>"
  | Fun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F> \<V>) ts \<tau>s \<Longrightarrow> welltyped \<F> \<V> (Fun f ts) \<tau>"

locale nonground_term_functional_substitution_typing = 
  base_functional_substitution_typing + 
  typed: explicitly_typed_subst_stability + 
  welltyped: explicitly_typed_subst_stability where expr_typed = expr_welltyped +
  typed: explicitly_replaceable_\<V> + 
  welltyped: explicitly_replaceable_\<V> where expr_typed = expr_welltyped +
  typed: explicitly_typed_renaming +
  welltyped: explicitly_typed_renaming where expr_typed = expr_welltyped

locale nonground_term_typing =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

abbreviation typed where "typed \<equiv> Nonground_Term_Typing.typed \<F>"
abbreviation welltyped where "welltyped \<equiv> Nonground_Term_Typing.welltyped \<F>"

sublocale "term": explicit_typing "typed \<V>" "welltyped \<V>"
proof unfold_locales
  fix \<V> :: "('var, 'ty) var_types"
  show "right_unique (typed \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "typed \<V> t \<tau>\<^sub>1" and "typed \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: typed.cases)
  qed
next
  fix \<V> :: "('var, 'ty) var_types"
  show welltyped_right_unique: "right_unique (welltyped \<V>)"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped \<V> t \<tau>\<^sub>1" and "welltyped \<V> t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
next
  fix \<V> :: "('var, 'ty) var_types" and t \<tau> 
  assume "welltyped \<V> t \<tau>"
  then show "typed \<V> t \<tau>"
    by (metis typed.intros welltyped.cases)
qed

sublocale term_typing where typed = "typed \<V>" and welltyped = "welltyped \<V>" and Fun = Fun
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
    proof (cases \<F> \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: welltyped.cases)
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
    proof (cases \<F> \<V> "Fun f (ss1 @ c\<langle>t\<rangle> # ss2)" \<tau> rule: typed.cases)
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
  id_subst = Var and comp_subst = "(\<odot>)" and subst = "(\<cdot>t)" and vars = term.vars and 
  expr_welltyped = welltyped and expr_typed = typed
proof unfold_locales
  fix \<V> :: "('var, 'ty) var_types" and x
  show "welltyped \<V> (Var x) (\<V> x)"
    by (simp add: welltyped.Var)
next
  fix \<tau> and \<V> and t :: "('f, 'v) term" and \<sigma>
  assume is_typed_on: "\<forall>x \<in> term.vars t. typed \<V> (\<sigma> x) (\<V> x)"

  show " typed \<V> (t \<cdot>t \<sigma>) \<tau> \<longleftrightarrow> typed \<V> t \<tau>"
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
  show "\<And>\<rho>. term_subst.is_renaming \<rho> \<Longrightarrow> inj \<rho>"
    by (simp add: term_subst_is_renaming_iff)
next
  show "\<And>\<rho> \<gamma> x. (\<rho> \<odot> \<gamma>) x = \<rho> x \<cdot>t \<gamma>"
    unfolding subst_compose..
next
  show "\<And>x. x \<in> term.vars (Var x)"
    by simp
qed

end

end
