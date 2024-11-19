theory Ground_Typing
  imports Ground_Clause Clause_Typing Term_Typing
begin

inductive typed for \<F> where
  GFun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> typed \<F> (GFun f ts) \<tau>"

inductive welltyped for \<F> where
  GFun: "\<F> f = (\<tau>s, \<tau>) \<Longrightarrow> list_all2 (welltyped \<F>) ts \<tau>s \<Longrightarrow> welltyped \<F> (GFun f ts) \<tau>"

locale ground_term_typing =
  fixes \<F> :: "('f, 'ty) fun_types"
begin

sublocale typed_def where typed_def = "typed \<F>" and welltyped_def = "welltyped \<F>" .

sublocale explicit_typing where typed = typed and welltyped = welltyped
proof unfold_locales
  show "right_unique typed"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "typed t \<tau>\<^sub>1" and "typed t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: typed.cases)
  qed
next
  show welltyped_right_unique: "right_unique welltyped"
  proof (rule right_uniqueI)
    fix t \<tau>\<^sub>1 \<tau>\<^sub>2
    assume "welltyped t \<tau>\<^sub>1" and "welltyped t \<tau>\<^sub>2"
    thus "\<tau>\<^sub>1 = \<tau>\<^sub>2"
      by (auto elim!: welltyped.cases)
  qed
next
  fix t \<tau>
  assume "welltyped t \<tau>"
  then show "typed t \<tau>"
    by (metis typed.intros welltyped.cases)
qed

sublocale context_compatible_typing where 
  typed = typed  and welltyped = welltyped and Fun = GFun
proof unfold_locales
  fix t t' c \<tau> \<tau>'
  assume 
    t_type: "welltyped t \<tau>'" and 
    t'_type: "welltyped t' \<tau>'" and
    c_type: "welltyped c\<langle>t\<rangle>\<^sub>G \<tau>"

  from c_type show "welltyped c\<langle>t'\<rangle>\<^sub>G \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using t_type t'_type welltyped_right_unique[THEN right_uniqueD]
      by auto
  next
    case (More f ss1 c ss2)

    have "welltyped (GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)) \<tau>"
      using More.prems 
      by simp

    hence "welltyped (GFun f (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2)) \<tau>"
    proof (cases \<F> "GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)" \<tau> rule: welltyped.cases)
      case (GFun \<tau>s)

      show ?thesis
      proof (rule welltyped.GFun)
        show "\<F> f = (\<tau>s, \<tau>)"
          using \<open>\<F> f = (\<tau>s, \<tau>)\<close> .
      next
        show "list_all2 welltyped (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2) \<tau>s"
          using \<open>list_all2 welltyped (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2) \<tau>s\<close>
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
    t_type: "typed t \<tau>'" and 
    t'_type: "typed t' \<tau>'" and
    c_type: "typed c\<langle>t\<rangle>\<^sub>G \<tau>"
 
  from c_type show "typed c\<langle>t'\<rangle>\<^sub>G \<tau>"
  proof (induction c arbitrary: \<tau>)
    case Hole
    then show ?case
      using t_type t'_type typed_right_unique[THEN right_uniqueD]
      by auto
  next
    case (More f ss1 c ss2)

    have "typed (GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)) \<tau>"
      using More.prems 
      by simp

    hence "typed (GFun f (ss1 @ c\<langle>t'\<rangle>\<^sub>G # ss2)) \<tau>"
    proof (cases \<F> "GFun f (ss1 @ c\<langle>t\<rangle>\<^sub>G # ss2)" \<tau> rule: typed.cases)
      case (GFun \<tau>s)

      then show ?thesis
        by (simp add: typed.simps)
    qed

    thus ?case
      by simp
  qed
qed

end

locale ground_typing = 
  "term": ground_term_typing + 
  clause_typing where term_typed = term.typed and term_welltyped = term.welltyped

end
